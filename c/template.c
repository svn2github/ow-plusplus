/****************************************************************************
*
*                            Open Watcom Project
*
*    Portions Copyright (c) 1983-2002 Sybase, Inc. All Rights Reserved.
*
*  ========================================================================
*
*    This file contains Original Code and/or Modifications of Original
*    Code as defined in and that are subject to the Sybase Open Watcom
*    Public License version 1.0 (the 'License'). You may not use this file
*    except in compliance with the License. BY USING THIS FILE YOU AGREE TO
*    ALL TERMS AND CONDITIONS OF THE LICENSE. A copy of the License is
*    provided with the Original Code and Modifications, and is also
*    available at www.sybase.com/developer/opensource.
*
*    The Original Code and all software distributed under the License are
*    distributed on an 'AS IS' basis, WITHOUT WARRANTY OF ANY KIND, EITHER
*    EXPRESS OR IMPLIED, AND SYBASE AND ALL CONTRIBUTORS HEREBY DISCLAIM
*    ALL SUCH WARRANTIES, INCLUDING WITHOUT LIMITATION, ANY WARRANTIES OF
*    MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE, QUIET ENJOYMENT OR
*    NON-INFRINGEMENT. Please see the License for the specific language
*    governing rights and limitations under the License.
*
*  ========================================================================
*
* Description:  WHEN YOU FIGURE OUT WHAT THIS FILE DOES, PLEASE
*               DESCRIBE IT HERE!
*
****************************************************************************/


#include "plusplus.h"
#include "cgfront.h"
#include "errdefns.h"
#include "rewrite.h"
#include "preproc.h"
#include "ring.h"
#include "stack.h"
#include "memmgr.h"
#include "class.h"
#include "name.h"
#include "yydriver.h"
#include "fnovload.h"
#include "context.h"
#include "template.h"
#include "pcheader.h"
#include "initdefs.h"
#ifndef NDEBUG
#include "pragdefn.h"
#include "dbg.h"
#include "fmttype.h"
#endif

#define BLOCK_TEMPLATE_INFO     16
#define BLOCK_TEMPLATE_SPECIALIZATION 16
#define BLOCK_MEMBER_INST       32
#define BLOCK_CLASS_INST        32
#define BLOCK_TEMPLATE_MEMBER   32
#define BLOCK_FN_TEMPLATE       16
#define BLOCK_FN_TEMPLATE_INST  32
static carve_t carveTEMPLATE_INFO;
static carve_t carveTEMPLATE_SPECIALIZATION;
static carve_t carveMEMBER_INST;
static carve_t carveCLASS_INST;
static carve_t carveTEMPLATE_MEMBER;
static carve_t carveFN_TEMPLATE;
static carve_t carveFN_TEMPLATE_INST;

static TEMPLATE_DATA *currentTemplate;
static TEMPLATE_INFO *allClassTemplates;
static FN_TEMPLATE *allFunctionTemplates;
static struct {
    unsigned            max_depth;
    unsigned            curr_depth;
    tc_fn_control       fn_control;
    SYMBOL              translate_fn;
    TYPE                extra_member_class;
    unsigned            keep_going : 1;
    unsigned            extra_members : 1;
    unsigned            depth_diagnosed : 1;
} templateData;

static CNV_DIAG diagTempParm =  // DIAGNOSIS FOR TEMPLATE ARGUMENT CONVERSION
    { ERR_PARM_IMPOSSIBLE
    , ERR_PARM_AMBIGUOUS
    , ERR_CALL_WATCOM
    , ERR_PARM_PRIVATE
    , ERR_PARM_PROTECTED
    };

enum template_context_type {
    TCTX_CLASS_DEFN     = 1,    // instantiating template class defn
    TCTX_FN_DEFN        = 2,    // instantiating template function defn
    TCTX_MEMBER_DEFN    = 3,    // instantiating template class member defn
    TCTX_FN_BIND        = 4,    // binding a function template to arguments
    TCTX_FN_BIND_AND_GEN= 5,    // binding a function template to a fn sym
    TCTX_NULL           = 0
};

typedef struct template_context TEMPLATE_CONTEXT;
struct template_context {
    TEMPLATE_CONTEXT            *prev;
    TOKEN_LOCN                  *locn;
    union {
        SYMBOL                  sym;    // FN_DEFN, FN_BIND
        SCOPE                   scope;  // CLASS_DEFN
        void                    *any;
    } u;
    enum template_context_type  id;
};

static struct {
    NESTED_POST_CONTEXT         registration;
    TEMPLATE_CONTEXT            *inst_stack;
} activeInstantiations;

static SUICIDE_CALLBACK templateSuicide;

static void injectTemplateParm( SCOPE scope, PTREE parm, char *name );


static void templateSuicideHandler( void )
{
    activeInstantiations.inst_stack = NULL;
    templateData.curr_depth = 0;
}

static SYMBOL firstSymbol( SCOPE scope )
{
    SYMBOL first;

    first = ScopeOrderedFirst( scope );
    DbgAssert( first != NULL );
    return( first );
}

static void verifyOKToProceed( TOKEN_LOCN *locn )
{
    templateData.curr_depth++;
    if( templateData.curr_depth > templateData.max_depth ) {
        if( ! templateData.depth_diagnosed ) {
            templateData.depth_diagnosed = TRUE;
            SetErrLoc( locn );
            CErr2( ERR_TEMPLATE_DEPTH_EXHAUSTED, templateData.max_depth * 2 );
            CSuicide();
        }
    }
}

static void pushInstContext( TEMPLATE_CONTEXT *ctx,
                             enum template_context_type id,
                             TOKEN_LOCN *locn, void *extra_info )
{
    verifyOKToProceed( locn );
    ctx->id = id;
    ctx->locn = locn;
    ctx->u.any = extra_info;
    StackPush( &(activeInstantiations.inst_stack), ctx );
}

static void popInstContext( void )
{
    templateData.curr_depth--;
    StackPop( &(activeInstantiations.inst_stack) );
}

static TYPE extractTemplateClass( TEMPLATE_CONTEXT *ctx )
{
    SYMBOL sym;

    sym = firstSymbol( ctx->u.scope );
    if( sym == NULL ) {
        return( TypeError );
    }
    DbgAssert( sym->id == SC_TYPEDEF );
    return( sym->sym_type );
}

static void displayActiveInstantiations( NESTED_POST_CONTEXT *blk )
{
    TEMPLATE_CONTEXT *ctx;

#ifndef NDEBUG
    if( blk != &(activeInstantiations.registration) ) {
        CFatal( "registered call-back for template locations incorrect" );
    }
#else
    blk = blk;
#endif
    Stack_forall( activeInstantiations.inst_stack, ctx ) {
        if( ctx->locn != NULL ) {
            switch( ctx->id ) {
            case TCTX_CLASS_DEFN:
                AddNoteMessage( INF_TEMPLATE_CLASS_DEFN_TRACEBACK,
                                extractTemplateClass( ctx ), ctx->locn );
                break;
            case TCTX_FN_DEFN:
                AddNoteMessage( INF_TEMPLATE_FN_DEFN_TRACEBACK,
                                ctx->u.sym, ctx->locn );
                break;
            case TCTX_MEMBER_DEFN:
                AddNoteMessage( INF_TEMPLATE_MEMBER_DEFN_TRACEBACK,
                                ctx->locn );
                break;
            case TCTX_FN_BIND:
                AddNoteMessage( INF_TEMPLATE_FN_BIND_TRACEBACK,
                                ctx->u.sym, ctx->locn );
                break;
            case TCTX_FN_BIND_AND_GEN:
                AddNoteMessage( INF_TEMPLATE_FN_BIND_AND_GEN_TRACEBACK,
                                ctx->u.sym, ctx->locn );
                break;
            }
        }
    }
}

void TemplateSetDepth( unsigned depth )
/*************************************/
{
    if( depth < 2 ) {
        /* we need at least 2 in order to bind a function */
        depth = 2;
    }
    templateData.max_depth = depth;
}

static void templateInit( INITFINI* defn )
{
    defn = defn;
    if( CompFlags.dll_subsequent ) {
        currentTemplate = NULL;
        allClassTemplates = NULL;
        allFunctionTemplates = NULL;
        memset( &templateData, 0, sizeof( templateData ) );
    }
    templateData.max_depth = TEMPLATE_MAX_DEPTH;
    activeInstantiations.registration.call_back = displayActiveInstantiations;
    CtxRegisterPostContext( &(activeInstantiations.registration) );
    templateSuicide.call_back = templateSuicideHandler;
    RegisterSuicideCallback( &templateSuicide );
    carveTEMPLATE_INFO = CarveCreate( sizeof( TEMPLATE_INFO ), BLOCK_TEMPLATE_INFO );
    carveTEMPLATE_SPECIALIZATION = CarveCreate( sizeof( TEMPLATE_SPECIALIZATION ), BLOCK_TEMPLATE_SPECIALIZATION );
    carveMEMBER_INST = CarveCreate( sizeof( MEMBER_INST ), BLOCK_MEMBER_INST );
    carveCLASS_INST = CarveCreate( sizeof( CLASS_INST ), BLOCK_CLASS_INST );
    carveTEMPLATE_MEMBER = CarveCreate( sizeof( TEMPLATE_MEMBER ), BLOCK_TEMPLATE_MEMBER );
    carveFN_TEMPLATE = CarveCreate( sizeof( FN_TEMPLATE ), BLOCK_FN_TEMPLATE );
    carveFN_TEMPLATE_INST = CarveCreate( sizeof( FN_TEMPLATE_INST ), BLOCK_FN_TEMPLATE_INST );
}

static void templateFini( INITFINI *defn )
{
    defn = defn;
    CarveDestroy( carveTEMPLATE_INFO );
    CarveDestroy( carveTEMPLATE_SPECIALIZATION );
    CarveDestroy( carveMEMBER_INST );
    CarveDestroy( carveCLASS_INST );
    CarveDestroy( carveTEMPLATE_MEMBER );
    CarveDestroy( carveFN_TEMPLATE );
    CarveDestroy( carveFN_TEMPLATE_INST );
}

INITDEFN( template, templateInit, templateFini )

static TYPE setArgIndex( SYMBOL sym, unsigned index )
{
    TYPE type;

    type = sym->sym_type;
    DbgAssert( type->id == TYP_GENERIC );
    DbgAssert( type->next == NULL );
    type->u.g.index = index;
    type = CheckDupType( type );
    sym->sym_type = type;
    return type;
}

void TemplateDeclInit( TEMPLATE_DATA *data )
/***********************************************************/
{
    StackPush( &currentTemplate, data );
    CErrCheckpoint( &(data->errors) );
    data->all_generic = TRUE;
    data->args = NULL;
    data->nr_args = 0;
    data->spec_args = NULL;
    data->unbound_type = NULL;
    data->decl_scope = ScopeBegin( SCOPE_TEMPLATE_DECL );
    data->defn = NULL;
    data->member_defn = NULL;
    data->template_name = NULL;
    data->template_scope = NULL;
    data->locn.src_file = NULL;
    data->defn_found = FALSE;
    data->member_found = FALSE;
    data->defn_added = FALSE;
}

static void validateNonTypeParameterType( TYPE type )
{
    TYPE trimmed_type;

    trimmed_type = TypedefModifierRemoveOnly( type );
    if( ( trimmed_type->id == TYP_POINTER ) // reference is also ok
     || ( trimmed_type->id == TYP_GENERIC ) ) {
        return;
    }

    if( IntegralType( trimmed_type ) == NULL ) {
        CErr2p( ERR_INVALID_TEMPLATE_ARG_TYPE, trimmed_type );
    }
}

void TemplateDeclAddArgument( DECL_INFO *new_dinfo )
{
    SYMBOL sym;
    char *name;

    currentTemplate->args = AddArgument( currentTemplate->args, new_dinfo );
    currentTemplate->nr_args++;

    name = new_dinfo->name;
    sym = new_dinfo->generic_sym;

    if( sym != NULL ) {
        /* template type parameter */
        new_dinfo->type = setArgIndex( sym, currentTemplate->nr_args );
        DbgAssert( name != NULL );
        sym = ScopeInsert( GetCurrScope(), sym, name );
    } else if( ( new_dinfo->type != NULL ) ) {
        /* template non-type parameter */
        currentTemplate->all_generic = FALSE;
        if( name != NULL ) {
            sym = ScopeInsert( GetCurrScope(),
                               AllocTypedSymbol( new_dinfo->type ), name );
        }
        validateNonTypeParameterType( new_dinfo->type );
    }
}

static unsigned getArgList( DECL_INFO *args, TYPE *type_list, char **names, REWRITE **defarg_list )
{
    DECL_INFO *curr;
    unsigned count;

    count = 0;
    RingIterBeg( args, curr ) {
        if( type_list != NULL ) {
            type_list[count] = curr->type;
        }
        if( names != NULL ) {
            names[count] = curr->name;
        }
        if( defarg_list != NULL ) {
            /*
            //  Ensure that we NULL out curr->defarg_rewrite or else
            //  when we delete the DECL_INFO, the rewrite element gets
            //  freed as well. The rewrite info will be freed when the
            //  the template info is freed.
            */
            defarg_list[count] = curr->defarg_rewrite;
            curr->defarg_rewrite = NULL;
        }
        ++count;
    } RingIterEnd( curr )
    return( count );
}

static TEMPLATE_SPECIALIZATION *newTemplateSpecialization(
    TEMPLATE_DATA *data, TEMPLATE_INFO *tinfo )
{
    DECL_INFO *args;
    TEMPLATE_SPECIALIZATION *tspec;
    TEMPLATE_SPECIALIZATION *tprimary;
    unsigned arg_count;

    tinfo->nr_specs++;

    args = data->args;
    arg_count = getArgList( args, NULL, NULL, NULL );
    tspec = RingCarveAlloc( carveTEMPLATE_SPECIALIZATION,
                            &tinfo->specializations );
    tprimary = RingFirst( tinfo->specializations );

    tspec->tinfo = tinfo;
    tspec->instantiations = NULL;
    tspec->member_defns = NULL;
    tspec->decl_scope = ( arg_count > 0 ) ? data->decl_scope : NULL;
    TokenLocnAssign( tspec->locn, data->locn );
    tspec->num_args = arg_count;
    tspec->type_list = CPermAlloc( arg_count * sizeof( TYPE ) );
    tspec->arg_names = CPermAlloc( arg_count * sizeof( char * ) );
    tspec->spec_args = data->spec_args;
    data->spec_args = NULL;
    tspec->ordering = NULL;
    tspec->defn = NULL;
    tspec->corrupted = FALSE;
    tspec->defn_found = FALSE;
    tspec->free = FALSE;

    getArgList( args, tspec->type_list, tspec->arg_names, NULL );
    return( tspec );
}

static TEMPLATE_INFO *newTemplateInfo( TEMPLATE_DATA *data )
{
    DECL_INFO *args;
    TEMPLATE_INFO *tinfo;
    TEMPLATE_SPECIALIZATION *tprimary;
    unsigned arg_count;

    args = data->args;
    arg_count = getArgList( args, NULL, NULL, NULL );
    if( arg_count == 0 ) {
        CErr1( ERR_TEMPLATE_MUST_HAVE_ARGS );
    }

    tinfo = RingCarveAlloc( carveTEMPLATE_INFO, &allClassTemplates );
    tinfo->specializations = NULL;
    tinfo->nr_specs = 0;
    tprimary = newTemplateSpecialization( data, tinfo );
    /* RingFirst( tinfo->specializations ) is always the primary template */

    tinfo->unbound_type = ClassUnboundTemplate( data->template_name );
    tinfo->sym = NULL;
    tinfo->defarg_list = CPermAlloc( arg_count * sizeof( REWRITE * ) );
    tinfo->free = FALSE;

    tprimary->defn = data->defn;
    tprimary->defn_found = data->defn_found;

    getArgList( args, NULL, NULL, tinfo->defarg_list );
    return( tinfo );
}

static SYMBOL newTemplateSymbol( TEMPLATE_DATA *data )
{
    SYMBOL sym;
    TEMPLATE_INFO *tinfo;

    tinfo = newTemplateInfo( data );
    sym = AllocSymbol();
    sym->id = SC_CLASS_TEMPLATE;
    sym->u.tinfo = tinfo;
    sym->sym_type = TypeGetCache( TYPC_CLASS_TEMPLATE );
    tinfo->sym = sym;
    if( data->locn.src_file != NULL ) {
        SymbolLocnDefine( &(data->locn), sym );
    }
    sym = ScopeInsert( data->template_scope, sym, data->template_name );
    return( sym );
}

void TemplateUsingDecl( SYMBOL sym, TOKEN_LOCN *locn )
/****************************************************/
{
    SYMBOL new_sym;

    DbgAssert( sym->id == SC_CLASS_TEMPLATE );
    new_sym = SymCreateAtLocn( sym->sym_type
                             , SC_CLASS_TEMPLATE
                             , SF_NULL
                             , sym->name->name
                             , GetCurrScope()
                             , locn );
    if( new_sym != NULL ) {
        new_sym->u.tinfo = sym->u.tinfo;
    }
}

SYMBOL ClassTemplateLookup( SCOPE scope, char *name )
/**************************************/
{
    SCOPE file_scope;
    SEARCH_RESULT *result;
    SYMBOL_NAME sym_name;
    SYMBOL sym;

    file_scope = ScopeNearestFileOrClass( scope );

    while( file_scope != NULL ) {
        result = ScopeFindNaked( file_scope, name );
        if( result != NULL ) {
            sym_name = result->sym_name;
            ScopeFreeResult( result );
            sym = sym_name->name_type;
            if( sym != NULL && SymIsClassTemplateModel( sym ) ) {
                return( sym );
            }
        }
        file_scope = ScopeNearestFileOrClass( file_scope->enclosing );
    }

    return( NULL );
}

static boolean templateArgListsSame( DECL_INFO *args, TEMPLATE_INFO *tinfo )
{
    unsigned curr_count;
    unsigned i;
    DECL_INFO *curr;
    TEMPLATE_SPECIALIZATION *tprimary;

    tprimary = RingFirst( tinfo->specializations );
    curr_count = getArgList( args, NULL, NULL, NULL );
    if( curr_count != tprimary->num_args ) {
        return( FALSE );
    }
    i = 0;
    RingIterBeg( args, curr ) {
        if( ! TypesIdentical( curr->type, tprimary->type_list[i] ) ) {
            return( FALSE );
        }
        ++i;
    } RingIterEnd( curr )
    return( TRUE );
}

static boolean sameArgNames( DECL_INFO *args, char **names )
{
    DECL_INFO *curr;

    RingIterBeg( args, curr ) {
        if( *names != curr->name ) {
            return( FALSE );
        }
        ++names;
    } RingIterEnd( curr )
    return( TRUE );
}

static char **getUniqueArgNames( DECL_INFO *args,
                                 TEMPLATE_SPECIALIZATION *tspec )
{
    unsigned arg_count;
    char **arg_names;

    arg_names = tspec->arg_names;
    if( ! sameArgNames( args, arg_names ) ) {
        arg_count = getArgList( args, NULL, NULL, NULL );
        arg_names = CPermAlloc( arg_count * sizeof( char * ) );
        getArgList( args, NULL, arg_names, NULL );
    }
    return( arg_names );
}

static boolean templateArgSame( PTREE left, PTREE right ) {
    if( ( left->op == PT_TYPE ) && ( right->op == PT_TYPE ) ) {
        return TypesIdentical( left->type, right->type );
    } else if( ( left->op == PT_INT_CONSTANT )
            && ( right->op == PT_INT_CONSTANT ) ) {
        // integer constant
        return ! U64Cmp( &left->u.int64_constant, &right->u.int64_constant);
    } else if( ( left->op == PT_SYMBOL ) && ( right->op == PT_SYMBOL ) ) {
        // unbound constant
        return TypesIdentical( left->u.symcg.symbol->sym_type,
                               right->u.symcg.symbol->sym_type );
    } else if( ( left->op == PT_TYPE ) && ( right->op == PT_SYMBOL ) ) {
        // unbound constant
        return TypesIdentical( left->type, right->u.symcg.symbol->sym_type );
    } else if( ( left->op == PT_SYMBOL ) && ( right->op == PT_TYPE ) ) {
        // unbound constant
        return TypesIdentical( left->u.symcg.symbol->sym_type, right->type );
    } else if( ( left->op == PT_SYMBOL )
            && ( right->op == PT_INT_CONSTANT ) ) {
        // left: unbound constant, right: bound constant
        return FALSE;
    } else if( ( left->op == PT_INT_CONSTANT )
            && ( right->op == PT_SYMBOL ) ) {
        // left: unbound constant, right: bound constant
        return FALSE;
    }

    // TODO: add missing cases
#ifndef NDEBUG
    DumpPTree( left );
    DumpPTree( right );
#endif
    CFatal( "not yet implemented: templateArgSame" );

    return FALSE;
}

static TEMPLATE_SPECIALIZATION *findMatchingTemplateSpecialization(
    TEMPLATE_INFO *tinfo, PTREE args )
{
    TEMPLATE_SPECIALIZATION *curr_spec;
    TEMPLATE_SPECIALIZATION *tspec;
    TEMPLATE_SPECIALIZATION *tprimary;
    SCOPE saved_scope;
    PTREE curr_list;
    PTREE spec_list;
    PTREE curr_arg;
    PTREE spec_arg;
    TYPE arg_type;
    SYMBOL curr, stop;
    unsigned i;
    boolean something_went_wrong;
    boolean is_primary;

    /* pre-process args */
    DbgAssert( args != NULL );
    something_went_wrong = FALSE;
    is_primary = TRUE;
    tprimary = RingFirst( tinfo->specializations );

    /* make sure declaration of template parameters are in the current scope */
    saved_scope = GetCurrScope();
    if( currentTemplate->args != NULL ) {
        SetCurrScope( currentTemplate->decl_scope );
        stop = ScopeOrderedStart( currentTemplate->decl_scope );
    } else {
        stop = NULL;
    }
    curr = NULL;

    for( curr_list = args, i = 0;
         curr_list != NULL;
         curr_list = curr_list->u.subtree[0], i++ ) {

        curr_arg = curr_list->u.subtree[1];

        if( ( curr_arg == NULL )
         || ( i >= tprimary->num_args ) ) {
            /* number of parameters don't match */
            /* error message: wrong number of template arguments */
            something_went_wrong = TRUE;
            break;
        }

        arg_type = tprimary->type_list[i];
        if( arg_type->id == TYP_GENERIC || arg_type->id == TYP_CLASS ) {
            arg_type = NULL;
        }

        if( stop != NULL ) {
            curr = ScopeOrderedNext( stop, curr );
            if( curr == NULL ) {
                stop = NULL;
            }
        }

        if( arg_type != NULL ) {
            curr_arg = AnalyseRawExpr( curr_arg );
            if( curr_arg->op == PT_ERROR ) {
                something_went_wrong = TRUE;
                break;
            }

            if( curr_arg->op == PT_SYMBOL ) {
                if( curr_arg->u.symcg.symbol != curr ) {
                    is_primary = FALSE;
                }
            } else {
                is_primary = FALSE;
            }
        } else {
            if( ( curr_arg->op == PT_TYPE )
             && ( curr_arg->type->id == TYP_TYPEDEF ) 
             && ( curr_arg->type->of->id == TYP_GENERIC ) ) {
                if ( curr_arg->type->of->u.g.index != ( i + 1 ) ) {
                    is_primary = FALSE;
                }
            } else {
                is_primary = FALSE;
            }
        }

        curr_list->u.subtree[1] = curr_arg;
    }

    if( currentTemplate->args != NULL ) {
        curr = NULL;
        stop = ScopeOrderedStart( currentTemplate->decl_scope );
        for(;;) {
            curr = ScopeOrderedNext( stop, curr );
            if( curr == NULL ) break;

            if( ( curr->sym_type->id == TYP_TYPEDEF )
             && ( curr->sym_type->of->id == TYP_GENERIC ) ) {
                /* TODO: check for unused symbol */
            } else {
                /* TODO: check for unused symbol */
            }
        }
    }

    SetCurrScope( saved_scope );

    if( something_went_wrong ) {
        if( i >= tprimary->num_args ) {
            CErr2p( ERR_WRONG_NR_TEMPLATE_ARGUMENTS, tinfo->sym );
        } else {
            /* TODO: diagnose error */
            CFatal( "not yet implemented: findMatchingTemplateSpecialization, error message" );
        }
        return NULL;
    }

    if( is_primary ) {
        return tprimary;
    }


    tspec = NULL;
    RingIterBeg( tinfo->specializations, curr_spec ) {
        if( curr_spec->spec_args == NULL ) {
            /* no need to match against the primary template */
            continue;
        }

        for( curr_list = args, spec_list = curr_spec->spec_args;
             ( curr_list != NULL ) && ( spec_list != NULL );
             curr_list = curr_list->u.subtree[0],
                 spec_list = spec_list->u.subtree[0] ) {

            curr_arg = curr_list->u.subtree[1];
            spec_arg = spec_list->u.subtree[1];
            if( ( curr_arg == NULL ) || ( spec_arg == NULL ) ) {
                break;
            }

            if( ! templateArgSame( spec_arg, curr_arg ) ) {
                break;
            }
        }

        if( ( curr_list == NULL ) && ( spec_list == NULL ) ) {
            tspec = curr_spec;
        }
    } RingIterEnd( curr_spec )

    return tspec;
}

static void updateTemplatePartialOrdering( TEMPLATE_INFO *tinfo,
                                           TEMPLATE_SPECIALIZATION *tspec )
{
    TEMPLATE_SPECIALIZATION *curr_spec;
    SYMBOL stop, curr;
    TYPE type;
    unsigned i;
    unsigned nr_specs;

    if( tspec->decl_scope != NULL ) {
        /* It gets a bit tricky here - we need to generate distinct
         * generic types until we have finished with the partial
         * ordering stuff (otherwise BindClassGenericTypes might get
         * confused).
         *
         * The CheckDupType will revert the type back to the original
         * generic type.
         */
        stop = ScopeOrderedStart( tspec->decl_scope );
        curr = NULL;
        i = 0;
        for(;;) {
            curr = ScopeOrderedNext( stop, curr );
            if( curr == NULL ) break;

            i++;
            type = curr->sym_type;

            if( ( type->id == TYP_TYPEDEF )
             && ( type->of->id == TYP_GENERIC ) ) {
                type->of = MakeType( TYP_GENERIC );
                type->of->u.g.index = i;
            }
        }
    }

    nr_specs = tinfo->nr_specs;

    if( tspec->spec_args != NULL ) {
        tspec->ordering = CMemAlloc( 16 * ( ( nr_specs - 2 ) / 128 + 1 ) );
    }

    i = 0;
    RingIterBeg( tinfo->specializations, curr_spec ) {
        if( curr_spec->spec_args == NULL ) {
        } else if( curr_spec == tspec ) {
            tspec->ordering[ i / 8 ] &= ~ ( 1 << ( i & 7 ) );
            i++;
        } else {
            SCOPE parm_scope;
            unsigned char mask;
            void *binding_handle;

            if( ( nr_specs - 2 ) & 128 ) {
                /* grow the bitmap as needed */
                unsigned char *old_mem;

                old_mem = curr_spec->ordering;
                curr_spec->ordering =
                    CMemAlloc( 16 * ( ( nr_specs - 2 ) / 128 + 1 ) );
                memcpy( curr_spec->ordering, old_mem,
                        16 * ( ( nr_specs - 2 ) / 128 ) );
                CMemFree( old_mem );
            }

            parm_scope = ScopeCreate( SCOPE_TEMPLATE_SPEC_PARM );
            ScopeSetEnclosing( parm_scope, tspec->decl_scope );
            BindExplicitTemplateArguments( parm_scope, NULL );

            binding_handle =
                BindGenericTypes( parm_scope, tspec->spec_args,
                                  curr_spec->spec_args, FALSE );
#ifndef NDEBUG
            if( PragDbgToggle.templ_spec && binding_handle ) {
                VBUF vbuf1, vbuf2;

                FormatPTreeList( curr_spec->spec_args, &vbuf1 );
                FormatPTreeList( tspec->spec_args, &vbuf2 );
                printf( "%s<%s> is at least as specialised as %s<%s>\n",
                        tinfo->sym->name->name, vbuf1.buf,
                        tinfo->sym->name->name, vbuf2.buf );
                VbufFree( &vbuf1 );
                VbufFree( &vbuf2 );
            }
#endif

            /* curr_spec is at least as specialized as tspec if (
             * bindings != NULL)
             */
            mask = 1 << ( ( nr_specs - 2 ) & 7 );
            curr_spec->ordering[ ( nr_specs - 2 ) / 8 ] &= ~ mask;
            curr_spec->ordering[ ( nr_specs - 2 ) / 8 ] |=
                binding_handle ? mask : 0;

            if( binding_handle ) {
                ClearGenericBindings( binding_handle );
            }
            ScopeBurn( parm_scope );

            parm_scope = ScopeCreate( SCOPE_TEMPLATE_SPEC_PARM );
            ScopeSetEnclosing( parm_scope, curr_spec->decl_scope );
            BindExplicitTemplateArguments( parm_scope, NULL );

            binding_handle =
                BindGenericTypes( parm_scope, curr_spec->spec_args,
                                  tspec->spec_args, FALSE );
#ifndef NDEBUG
            if( PragDbgToggle.templ_spec && binding_handle ) {
                VBUF vbuf1, vbuf2;

                FormatPTreeList( tspec->spec_args, &vbuf1 );
                FormatPTreeList( curr_spec->spec_args, &vbuf2 );
                printf( "%s<%s> is at least as specialised as %s<%s>\n",
                        tinfo->sym->name->name, vbuf1.buf,
                        tinfo->sym->name->name, vbuf2.buf );
                VbufFree( &vbuf1 );
                VbufFree( &vbuf2 );
            }
#endif

            /* tspec is at least as specialized as curr_spec if (
             * bindings != NULL)
             */
            mask = 1 << ( i & 7 );
            tspec->ordering[ i / 8 ] &= ~ mask;
            tspec->ordering[ i / 8 ] |= binding_handle ? mask : 0;

            if( binding_handle ) {
                ClearGenericBindings( binding_handle );
            }
            ScopeBurn( parm_scope );

            i++;
        }
    } RingIterEnd( curr_spec )

    if( tspec->decl_scope != NULL ) {
        stop = ScopeOrderedStart( tspec->decl_scope );
        curr = NULL;
        i = 0;
        for(;;) {
            curr = ScopeOrderedNext( stop, curr );
            if( curr == NULL ) break;

            i++;
            type = curr->sym_type;

            if( ( type->id == TYP_TYPEDEF )
             && ( type->of->id == TYP_GENERIC ) ) {
                DbgAssert( type->of->next == NULL );
                type->of = CheckDupType( type->of );
            }
        }
    }
}

static TEMPLATE_SPECIALIZATION *mergeClassTemplates( TEMPLATE_DATA *data,
                                                     SYMBOL old_sym )
{
    DECL_INFO *args;
    TEMPLATE_INFO *tinfo;
    TEMPLATE_SPECIALIZATION *tspec;
    REWRITE *defn;
    REWRITE **defarg_list;
    boolean primary_specialization;
 
    tinfo = old_sym->u.tinfo;
    args = data->args;

    if( data->spec_args != NULL ) {
        primary_specialization = FALSE;
        tspec = findMatchingTemplateSpecialization( tinfo, data->spec_args );
        if( tspec == RingFirst( tinfo->specializations ) ) {
            CErr2p( ERR_TEMPLATE_SPECIALIZATION_MATCHES_PRIMARY, tinfo->sym );
            tspec = NULL;
        }
        if( tspec == NULL ) {
            tspec = newTemplateSpecialization( data, tinfo );
            updateTemplatePartialOrdering( tinfo, tspec );
        }
    } else if( data->unbound_type != NULL ) {
        PTREE parm;
        PTREE parms;
        SYMBOL curr;
        SYMBOL stop;
        SCOPE parm_scope;

        parm_scope = data->unbound_type->u.c.scope->enclosing;
        DbgAssert( ScopeType( parm_scope, SCOPE_TEMPLATE_PARM ) );

        /* TODO: factor out, see fakeUpTemplateParms */
        parms = NULL;
        curr = NULL;
        stop = ScopeOrderedStart( parm_scope );
        for(;;) {
            curr = ScopeOrderedNext( stop, curr );
            if( curr == NULL ) break;

            switch( curr->id ) {
              case SC_TYPEDEF:
                parm = PTreeType( curr->sym_type );
                break;

              case SC_STATIC:
                parm = PTreeIntConstant( curr->u.uval, TYP_SINT );
                parm->type = curr->sym_type;
                break;

              case SC_ADDRESS_ALIAS:
                parm = MakeNodeSymbol( curr->u.alias );
                break;

              default:
#ifndef NDEBUG
                DumpSymbol( curr );
#endif
                CFatal( "not yet implemented: mergeClassTemplates" );
            }
            parms = PTreeBinary( CO_LIST, parms, parm );
        }

        if( parms != NULL ) {
            unsigned num_parms;

            parms = NodeReverseArgs( &num_parms, parms );
            tspec = findMatchingTemplateSpecialization( tinfo, parms );

            if( tspec == NULL ) {
                if( ! ( data->member_found && data->args == NULL ) ) {
                    CErr2p( ERR_UNKNOWN_TEMPLATE_SPECIALIZATION, tinfo->sym );
                }
                primary_specialization = TRUE;
                tspec = RingFirst( tinfo->specializations );
            } else {
                if( data->member_found && data->args == NULL ) {
                    CErr2p( ERR_CANNOT_EXPLICITLY_SPECIALIZE_MEMBER, tinfo->sym );
                }
                primary_specialization = FALSE;
            }
        } else {
            primary_specialization = TRUE;
            tspec = RingFirst( tinfo->specializations );
        }

        PTreeFreeSubtrees( parms );
    } else {
        tspec = RingFirst( tinfo->specializations );
        primary_specialization = TRUE;

        if( ( data->nr_args != tspec->num_args )
         || ! templateArgListsSame( args, tinfo ) ) {
            CErr2p( ERR_CANT_OVERLOAD_CLASS_TEMPLATES, tinfo );
            return NULL;
        }
    }
    if( tspec->corrupted ) {
        return tspec;
    }
    defn = data->defn;
    if( data->defn_found ) {
        if( tspec->defn_found ) {
            CErr2p( ERR_CANT_REDEFINE_CLASS_TEMPLATES, tinfo );
            RewriteFree( defn );
            data->defn = NULL;
        } else {
            RewriteFree( tspec->defn );
            tspec->defn = defn;
            tspec->defn_found = TRUE;
            data->defn_added = TRUE;
            tspec->arg_names = getUniqueArgNames( args, tspec );
            if( primary_specialization ) {
                defarg_list = tinfo->defarg_list;
            } else {
                defarg_list = NULL;
            }

            getArgList( args, tspec->type_list, tspec->arg_names,
                        defarg_list );
        }
    } else {
        if( ( tspec->defn == NULL ) ) {
            tspec->defn = defn;
        } else {
            RewriteFree( defn );
        }
        data->defn = NULL;
    }

    return tspec;
}

static void addMemberEntry( TEMPLATE_SPECIALIZATION *tspec, REWRITE *r,
                            char **arg_names )
{
    TEMPLATE_MEMBER *extra_defn;

    extra_defn = RingCarveAlloc( carveTEMPLATE_MEMBER
                               , &(tspec->member_defns) );
    extra_defn->defn = r;
    extra_defn->arg_names = arg_names;
}

static void addClassTemplateMember( TEMPLATE_DATA *data, SYMBOL sym,
                                    TEMPLATE_SPECIALIZATION *tspec )
{
    char **arg_names;

    if( ( NULL == data) || ( NULL == sym) ){
        return;
    }

    if( ! data->member_found ) {
        return;
    }

    arg_names = getUniqueArgNames( data->args, tspec );
    addMemberEntry( tspec, data->member_defn, arg_names );
}

static TYPE doParseClassTemplate( TEMPLATE_SPECIALIZATION *tspec,
                                  REWRITE *defn, TOKEN_LOCN *locn,
                                  tc_instantiate control )
{
    TYPE new_type;
    DECL_SPEC *dspec;
    auto TEMPLATE_CONTEXT context;

    new_type = TypeError;
    if( ! tspec->corrupted ) {
        pushInstContext( &context, TCTX_CLASS_DEFN, locn, GetCurrScope() );
        dspec = ParseClassInstantiation( defn, ( control & TCI_NO_CLASS_DEFN ) != 0 );
        popInstContext();
        if( dspec != NULL ) {
            new_type = dspec->partial;
            PTypeRelease( dspec );
        } else {
            tspec->corrupted = TRUE;
        }
    }
    return( new_type );
}

static SYMBOL dupTemplateParm( SYMBOL old_parm )
{
    SYMBOL sym;

    sym = AllocSymbol();
    sym->id = old_parm->id;
    sym->sym_type = old_parm->sym_type;
    sym->flag = old_parm->flag;
    switch( old_parm->id ) {
    case SC_STATIC:
        if( old_parm->flag & SF_CONSTANT_INT64 ) {
            sym->flag |= SF_CONSTANT_INT64;
            sym->u.pval = old_parm->u.pval;
        } else {
            sym->u.uval = old_parm->u.uval;
        }
        break;
    case SC_ADDRESS_ALIAS:
        sym->u.alias = old_parm->u.alias;
        break;
    }
    return( sym );
}

static void copyWithNewNames( SCOPE old_scope, char **names )
{
    SYMBOL curr;
    SYMBOL stop;
    SYMBOL sym;

    curr = NULL;
    stop = ScopeOrderedStart( old_scope );
    for(;;) {
        curr = ScopeOrderedNext( stop, curr );
        if( curr == NULL ) break;
        sym = dupTemplateParm( curr );
        sym = ScopeInsert( GetCurrScope(), sym, *names );
        ++names;
    }
}

static void defineAllClassDecls( TEMPLATE_SPECIALIZATION *tspec )
{
    /*
        template <class T>
            class F;

        F<int> *p;
        typedef F<double> & REF;
        template <class T>
            class F {
                T x;
            };
             ^ we have to visit F<int> and F<double> to define them with
               this definition
    */
    CLASS_INST *curr;
    SCOPE save_enclosing;
    SCOPE save_scope;
    SCOPE inst_scope;
    SCOPE parm_scope;
    SCOPE old_parm_scope;
    auto TOKEN_LOCN location;

    SrcFileGetTokenLocn( &location );
    save_scope = GetCurrScope();
    RingIterBeg( tspec->instantiations, curr ) {
        if( curr->specific ) {
            /* we shouldn't mess around with specific instantiations */
            continue;
        }
        /* we have to splice in the new parm scope under the old
         * INST scope because the parm names may have changed but
         * the class type must be exactly as before (it may have
         * been used in typedefs) */
        inst_scope = curr->scope;
        old_parm_scope = inst_scope->enclosing;

        SetCurrScope( old_parm_scope->enclosing );
        parm_scope = ScopeBegin( ScopeId( old_parm_scope ) );
        if( ScopeType( old_parm_scope, SCOPE_TEMPLATE_PARM ) ) {
            ScopeSetParmCopy( parm_scope, old_parm_scope );
        }
        copyWithNewNames( old_parm_scope, tspec->arg_names );
        save_enclosing = ScopeEstablishEnclosing( inst_scope, parm_scope );
        SetCurrScope( inst_scope );
        doParseClassTemplate( tspec, tspec->defn, &location, TCI_NULL );
        ScopeSetEnclosing( inst_scope, save_enclosing );
    } RingIterEnd( curr )
    SetCurrScope( save_scope );
}

extern int WalkTemplateInst( SYMBOL sym, AInstSCOPE fscope  )
{
    TEMPLATE_INFO *tinfo;
    TEMPLATE_SPECIALIZATION *tspec;
    CLASS_INST *curr;

    tinfo = sym->u.tinfo;
    RingIterBeg( tinfo->specializations, tspec ) {
        RingIterBeg( tspec->instantiations, curr ) {
            if( !fscope( curr->scope ) ){
                return( FALSE );
            }
        } RingIterEnd( curr )
    } RingIterEnd( tspec )
   return( TRUE );
}

void TemplateDeclFini( void )
/***************************/
{
    TEMPLATE_DATA *data;
    TEMPLATE_SPECIALIZATION *tspec;
    char *name;
    SYMBOL sym;

    ScopeEnd( SCOPE_TEMPLATE_DECL );
    data = currentTemplate;
    name = data->template_name;
    sym = NULL;
    tspec = NULL;
    if( ( name != NULL )
     && ( ScopeType( GetCurrScope(), SCOPE_FILE )
       || ScopeType( GetCurrScope(), SCOPE_CLASS ) ) ) {
        DbgAssert( data->template_scope != NULL );
        sym = ClassTemplateLookup( data->template_scope, name );
        if( ( sym != NULL )
         && ( sym->name->containing == data->template_scope ) ) {
            tspec = mergeClassTemplates( data, sym );
        } else if( data->spec_args == NULL ) {
            sym = newTemplateSymbol( data );
            if( sym != NULL ) {
                tspec = RingFirst( sym->u.tinfo->specializations );
            }
        } else {
            /* TODO: error message */
            CFatal( "not yet implemented: TemplateDeclFini" );
        }

        if( ( sym != NULL ) && ( tspec != NULL ) ) {
            addClassTemplateMember( data, sym, tspec );
        }
    }
    if( CErrOccurred( &(data->errors) ) ) {
        if( sym != NULL ) {
            if( tspec == NULL ) {
                tspec = RingFirst( sym->u.tinfo->specializations );
            }

            tspec->corrupted = TRUE;
        }
    } else {
        if( data->defn_added && ( tspec != NULL ) ) {
            defineAllClassDecls( tspec );
        }
    }

    FreeArgsDefaultsOK( data->args );
    data->args = NULL;
    PTreeFreeSubtrees( data->spec_args );
    data->spec_args = NULL;

    StackPop( &currentTemplate );
}

static FN_TEMPLATE *newTemplateFunction( SYMBOL sym )
{
    FN_TEMPLATE *fn_defn;

    if( CErrOccurred( &(currentTemplate->errors) ) ) {
        return( NULL );
    }
    fn_defn = RingCarveAlloc( carveFN_TEMPLATE, &allFunctionTemplates );
    fn_defn->instantiations = NULL;
    fn_defn->sym = sym;
    fn_defn->decl_scope = GetCurrScope();
    fn_defn->defn = NULL;
    return( fn_defn );
}

void TemplateFunctionCheck( SYMBOL sym, DECL_INFO *dinfo )
/********************************************************/
{
    if( ! SymIsFunction( sym ) ) {
        CErr1( ERR_NO_VARIABLE_TEMPLATES );
        return;
    }
    ForceNoDefaultArgs( dinfo, ERR_FUNCTION_TEMPLATE_NO_DEFARGS );
    if( sym->id != SC_STATIC ) {
        sym->id = SC_FUNCTION_TEMPLATE;
    } else {
        sym->id = SC_STATIC_FUNCTION_TEMPLATE;
    }
    sym->sym_type = MakePlusPlusFunction( sym->sym_type );
}

void TemplateFunctionDeclaration( SYMBOL sym )
/********************************************/
{
    if( sym->u.defn == NULL ) {
        sym->u.defn = newTemplateFunction( sym );
    }
}

void TemplateFunctionAttachDefn( DECL_INFO *dinfo )
/*************************************************/
{
    SYMBOL sym;
    REWRITE *r;
    FN_TEMPLATE *fn_templ;

    sym = dinfo->sym;
    if( sym == NULL ) {
        return;
    }
    r = dinfo->body;
    dinfo->body = NULL;
    fn_templ = sym->u.defn;
    DbgAssert( fn_templ );
    DbgAssert( ScopeType( GetCurrScope(), SCOPE_TEMPLATE_DECL ) );

    if( fn_templ->decl_scope != GetCurrScope() ) {
        // replace the decl_scope of function template declarations
        ScopeBurn( fn_templ->decl_scope );
        fn_templ->decl_scope = GetCurrScope();
    }

    if( fn_templ->defn != NULL ) {
        RewriteFree( r );
        CErr2p( ERR_FUNCTION_TEMPLATE_ALREADY_HAS_DEFN, sym );
    } else {
        fn_templ->defn = r;
    }
    FreeDeclInfo( dinfo );
}

#ifndef NDEBUG
static void verifySyms( SYMBOL syms )
{
    SYMBOL check;

    RingIterBeg( syms, check ) {
        if( SymIsFunctionTemplateModel( check ) ) {
            return;
        }
    } RingIterEnd( check )
    CFatal( "trying to generate a template function without any templates" );
}
#endif

static TYPE attemptGen( arg_list *args, SYMBOL fn_templ, PTREE templ_args,
                        TOKEN_LOCN *locn, SCOPE *templ_parm_scope,
                        bgt_control *pcontrol )
{
    TYPE fn_type;
    TYPE bound_type;
    TEMPLATE_CONTEXT context;
    SCOPE decl_scope;
    SCOPE parm_scope;
    arg_list *parms;
    PTREE pparms, pargs;
    void *binding_handle;
    unsigned i;
    unsigned num_parms, num_args;

    fn_type = FunctionDeclarationType( fn_templ->sym_type );
    if( fn_type == NULL || ! TypeHasNumArgs( fn_type, args->num_args ) ) {
        return( NULL );
    }

    decl_scope = fn_templ->u.defn->decl_scope;
    parms = fn_type->u.f.args;

    pparms = NULL;
    for( i = 0; i < parms->num_args; i++ ) {
        PTREE parm = PTreeType( parms->type_list[i] );
        pparms = PTreeBinary( CO_LIST, pparms, parm );
    }

    pparms = NodeReverseArgs( &num_parms, pparms );

    pargs = NULL;
    for( i = 0; i < args->num_args; i++ ) {
        PTREE arg = PTreeType( args->type_list[i] );
        pargs = PTreeBinary( CO_LIST, pargs, arg );
    }

    pargs = NodeReverseArgs( &num_args, pargs );

    parm_scope = ScopeCreate( SCOPE_TEMPLATE_PARM );
    ScopeSetEnclosing( parm_scope, decl_scope );

    templ_args = NodeReverseArgs( &i, templ_args );

#ifndef NDEBUG
    if( PragDbgToggle.templ_function ) {
        VBUF vbuf1, vbuf2;

        FormatPTreeList( templ_args, &vbuf1 );
        FormatPTreeList( pargs, &vbuf2 );
        printf( "attemptGen for %s<%s>(%s)\n",
                fn_templ->name->name, vbuf1.buf, vbuf2.buf );
        DumpFullType( fn_type );
        VbufFree( &vbuf1 );
        VbufFree( &vbuf2 );
    }
#endif

    BindExplicitTemplateArguments( parm_scope, templ_args );

    pushInstContext( &context, TCTX_FN_BIND, locn, fn_templ );

    binding_handle = BindGenericTypes( parm_scope, pparms, pargs, TRUE );
    if( binding_handle ) {
        bound_type = CreateBoundType( fn_templ->sym_type, locn );
        ClearGenericBindings( binding_handle );
        *templ_parm_scope = parm_scope;
    } else {
        if( PragDbgToggle.templ_function ) {
            printf( "attemptGen: BindGenericTypes failed\n");
        }
        ScopeBurn( parm_scope );
        bound_type = NULL;
    }

    PTreeFreeSubtrees( pparms );
    PTreeFreeSubtrees( pargs );

    popInstContext();
    return( bound_type );
}

static SYMBOL buildTemplateFn( TYPE bound_type, SYMBOL sym,
                               SCOPE parm_scope, TOKEN_LOCN *locn )
{
    SCOPE inst_scope;
    SYMBOL new_sym;
    FN_TEMPLATE *fn_templ;
    FN_TEMPLATE_INST *fn_inst;
    symbol_flag new_flags;

    if( bound_type == NULL ) {
        return( NULL );
    }
    if( ScopeType( SymScope( sym ), SCOPE_CLASS ) ) {
        new_flags = ( sym->flag & SF_ACCESS );
    } else {
        new_flags = ( sym->flag & SF_PLUSPLUS );
    }

    inst_scope = ScopeCreate( SCOPE_TEMPLATE_INST );
    ScopeSetEnclosing( inst_scope, parm_scope );
    new_sym = SymCreateAtLocn( bound_type
                             , SymIsStatic( sym ) ? SC_STATIC : SC_PUBLIC
                             , new_flags | SF_TEMPLATE_FN
                             , sym->name->name
                             , inst_scope
                             , locn );
    new_sym->u.alias = sym;
    fn_templ = sym->u.defn;

    fn_inst = RingCarveAlloc( carveFN_TEMPLATE_INST,
                              &fn_templ->instantiations );
    fn_inst->bound_sym = new_sym;
    fn_inst->parm_scope = parm_scope;
    fn_inst->inst_scope = inst_scope;
    fn_inst->processed = FALSE;

    return new_sym;
}

unsigned TemplateFunctionGenerate( SYMBOL *psym, arg_list *args,
/********************************************************************************/
                                   PTREE templ_args, TOKEN_LOCN *locn,
                                   SYMBOL *ambigs, boolean no_trivials )
{
    SYMBOL generated_fn;
    SYMBOL syms;
    SYMBOL sym;
    SYMBOL fn_templ;
    SCOPE parm_scope;
    bgt_control bind_control;
    bgt_control control;
    unsigned i;
    TYPE check_fn_type;
    TYPE final_fn_type;
    SCOPE final_parm_scope;
    auto TYPE fn_types[BGT_MAX][2];
    auto SYMBOL fn_templs[BGT_MAX][2];
    auto SCOPE fn_scopes[BGT_MAX][2];

#ifndef NDEBUG
    verifySyms( *psym );
    ambigs[0] = (SYMBOL)-1;
    ambigs[1] = (SYMBOL)-1;
#endif
    syms = *psym;
    if( ! ScopeType( SymScope( syms ), SCOPE_FILE )
     && ! ScopeType( SymScope( syms ), SCOPE_CLASS ) ) {
        return( FNOV_NO_MATCH );
    }
    bind_control = BGT_EXACT;
    if( ! no_trivials ) {
        bind_control = BGT_TRIVIAL;
    }
    fn_types[BGT_EXACT][0] = NULL;      /* exact match function types */
    fn_types[BGT_EXACT][1] = NULL;
    fn_types[BGT_TRIVIAL][0] = NULL;    /* trivial conversion function types */
    fn_types[BGT_TRIVIAL][1] = NULL;
    fn_types[BGT_DERIVED][0] = NULL;    /* derived class conversion function types */
    fn_types[BGT_DERIVED][1] = NULL;
    RingIterBeg( syms, sym ) {
        if( SymIsFunctionTemplateModel( sym ) ) {
            control = bind_control;
            check_fn_type = attemptGen( args, sym, templ_args, locn, &parm_scope, &control );
            if( check_fn_type != NULL ) {
                fn_types[control][1] = fn_types[control][0];
                fn_types[control][0] = check_fn_type;
                fn_templs[control][1] = fn_templs[control][0];
                fn_templs[control][0] = sym;
                fn_scopes[control][1] = fn_scopes[control][0];
                fn_scopes[control][0] = parm_scope;
                if( fn_types[BGT_EXACT][1] != NULL ) {
                    /* two exact matches! */
                    ambigs[0] = fn_templs[BGT_EXACT][0];
                    ambigs[1] = fn_templs[BGT_EXACT][1];
                    return( FNOV_AMBIGUOUS );
                }
            }
        }
    } RingIterEnd( sym )
    for( i = BGT_EXACT; i < BGT_MAX; ++i ) {
        fn_templ = fn_templs[ i ][0];
        final_fn_type = fn_types[ i ][0];
        final_parm_scope = fn_scopes[ i ][0];
        if( fn_types[ i ][1] != NULL ) {
            /* two matches for a type of conversion! */
            ambigs[0] = fn_templs[i][0];
            ambigs[1] = fn_templs[i][1];
            return( FNOV_AMBIGUOUS );
        }
        if( final_fn_type != NULL ) break;
    }

#ifndef NDEBUG
    if( PragDbgToggle.templ_function ) {
        printf( "TemplateFunctionGenerate for\n" );
        DumpFullType( final_fn_type );
    }
#endif
    generated_fn = buildTemplateFn( final_fn_type, fn_templ, final_parm_scope,
                                    locn );
    if( generated_fn != NULL ) {
        *psym = generated_fn;
        return( FNOV_NONAMBIGUOUS );
    }
    return( FNOV_NO_MATCH );
}

static void commonTemplateClass( TEMPLATE_DATA *data, PTREE id, SCOPE scope, char *name )
{
    data->template_name = name;
    data->template_scope = ScopeType( scope, SCOPE_TEMPLATE_DECL ) ?
        scope->enclosing : scope;

    if( id->locn.src_file != NULL ) {
        TokenLocnAssign( data->locn, id->locn );
    }
}

void TemplateClassDeclaration( PTREE id, SCOPE scope, char *name )
/***************************************/
{
    TEMPLATE_DATA *data;
    TOKEN_LOCN *locn;
    REWRITE *r;

    data = currentTemplate;
    r = ParseGetRecordingInProgress( &locn );
    data->defn = r;
    commonTemplateClass( data, id, scope, name );
}

boolean TemplateClassDefinition( PTREE id, SCOPE scope, char *name )
/*****************************************/
{
    TEMPLATE_DATA *data;
    TOKEN_LOCN *locn;
    REWRITE *r;
    SCOPE template_scope;

    data = currentTemplate;
    r = ParseGetRecordingInProgress( &locn );
    if( r == NULL ) {
        CErr1( ERR_SYNTAX );
        return( TRUE );
    }
    r = RewritePackageClassTemplate( r, locn );
    data->defn = r;
    data->defn_found = TRUE;
    template_scope = ( id->op == PT_ID ) ? GetCurrScope() : scope;
    commonTemplateClass( data, id, template_scope, name );
    return( r == NULL );
}

static boolean okForTemplateParm( PTREE parm )
{
    SYMBOL sym;
    SCOPE scope;

    sym = parm->u.symcg.symbol;
    sym = SymDeAlias( sym );
    parm->u.symcg.symbol = sym;
    if( SymIsStaticMember( sym ) ) {
        return( TRUE );
    }
    scope = SymScope( sym );
    if( ScopeType( scope, SCOPE_FILE ) ) {
        switch( sym->id ) {
        case SC_PUBLIC:
        case SC_EXTERN:
        case SC_NULL:
            return( TRUE );
        }
    }
    return( FALSE );
}

static PTREE templateParmSimpleEnough( TYPE arg_type, PTREE parm )
{
    PTREE sym_parm;

    switch( parm->op ) {
    case PT_ERROR:
    case PT_INT_CONSTANT:
        return( parm );
    case PT_SYMBOL:
        if( okForTemplateParm( parm ) ) {
            if( PointerType( arg_type ) != NULL ) {
                if( SymIsFunction( parm->u.symcg.symbol ) ) {
                    parm->type = arg_type;
                    return( parm );
                }
            } else if( TypeReference( arg_type ) != NULL ) {
                parm->type = arg_type;
                return( parm );
            }
        }
        break;
    case PT_UNARY:
        if( PointerType( arg_type ) != NULL ) {
            if( parm->cgop == CO_ADDR_OF ) {
                sym_parm = parm->u.subtree[0];
                if( sym_parm->op == PT_SYMBOL ) {
                    PTREE oldparm = parm;
                    parm->u.subtree[0] = NULL;
                    /* reduce parm to a PT_SYMBOL */
                    parm = sym_parm;
                    if( okForTemplateParm( parm ) ) {
                        /* Only delete oldparm if we are returning success */
                        PTreeFreeSubtrees( oldparm );
                        parm->type = arg_type;
                        return( parm );
                    }
                }
            }
        } else if( MemberPtrType( arg_type ) != NULL ) {
            /* TODO: handle member function pointers */
            DbgAssert( 0 );
        }
        break;
    case PT_BINARY:
        if( parm->cgop == CO_CONVERT ) {
            sym_parm = parm->u.subtree[1];
            if( sym_parm->op == PT_SYMBOL ) {
                PTREE oldparm = parm;
                parm->u.subtree[1] = NULL;
                /* reduce parm to a PT_SYMBOL */
                parm = sym_parm;
                if( okForTemplateParm( parm ) ) {
                    /* Only delete oldparm if we are returning success */
                    PTreeFreeSubtrees( oldparm );
                    parm->type = arg_type;
                    return( parm );
                }
            }
        }
        break;
    }
    PTreeErrorExpr( parm, ERR_INVALID_TEMPLATE_PARM );
    return( parm );
}

static boolean suitableForIntegralParm( PTREE parm )
{
    switch( parm->op ) {
    case PT_INT_CONSTANT:
        return( TRUE );
    }
    return( FALSE );
}

static boolean suitableForAddressParm( PTREE parm )
{
    switch( parm->op ) {
    case PT_SYMBOL:
        return( TRUE );
    }
    return( FALSE );
}

static PTREE processIndividualParm( TYPE arg_type, PTREE parm )
{
    parm = AnalyseRawExpr( parm );
    if( parm->op == PT_ERROR ) {
        return( parm );
    }
    parm = CastImplicit( parm, arg_type, CNV_FUNC_ARG, &diagTempParm );
    if( parm->op == PT_ERROR ) {
        return( parm );
    }
    parm = templateParmSimpleEnough( arg_type, parm );
    if( IntegralType( arg_type ) != NULL ) {
        if( ! suitableForIntegralParm( parm ) ) {
            PTreeErrorExpr( parm, ERR_TEMPLATE_ARG_NON_CONSTANT );
        }
    } else {
        if( ! suitableForAddressParm( parm ) ) {
            PTreeErrorExpr( parm, ERR_TEMPLATE_ARG_NOT_SYMBOL );
        }
    }
    return( parm );
}

static PTREE processClassTemplateParms( TEMPLATE_INFO *tinfo, PTREE parms )
{
    SCOPE save_scope;
    SCOPE parm_scope;
    PTREE list;
    PTREE parm;
    TYPE arg_type;
    TEMPLATE_SPECIALIZATION *tprimary;
    unsigned num_parms;
    unsigned i;
    boolean something_went_wrong;
    boolean inside_decl_scope;
    TOKEN_LOCN start_locn;

    inside_decl_scope = ScopeAccessType( SCOPE_TEMPLATE_DECL );
    save_scope = GetCurrScope();
    parms = NodeReverseArgs( &num_parms, parms );
    something_went_wrong = FALSE;
    tprimary = RingFirst( tinfo->specializations );

    if( tprimary->corrupted ) {
        something_went_wrong = TRUE;
    }
    /* Check for argument overflow */
    if( num_parms > tprimary->num_args ) {
        CErr1( ERR_TOO_MANY_TEMPLATE_PARAMETERS );
        something_went_wrong = TRUE;
    } else if( ! something_went_wrong ) {
        if( ! inside_decl_scope ) {
            parm_scope = ScopeCreate( SCOPE_TEMPLATE_PARM );
            ScopeSetEnclosing( parm_scope, SymScope( tinfo->sym ) );
        }
        SrcFileGetTokenLocn( &start_locn );

        list = parms;
        i = 0;

        for( i = 0; ; list = list->u.subtree[0] ) {
            arg_type = TypedefRemove( tprimary->type_list[i] );
            if( arg_type->id == TYP_GENERIC ) {
                if( ! inside_decl_scope ) {
                    /* a generic type might have already been bound - we
                     * should take that into account */
                    SEARCH_RESULT *result;

                    result = ScopeFindMember( parm_scope,
                                              tprimary->arg_names[arg_type->u.g.index - 1] );
                    if( result != NULL ) {
                        arg_type = TypedefRemove( result->sym_name->name_type->sym_type );
                        ScopeFreeResult( result );
                    } else {
                        arg_type = NULL;
                    }
                } else {
                    arg_type = NULL;
                }
            } else if( arg_type->id == TYP_CLASS ) {
                arg_type = NULL;
            }

            parm = list->u.subtree[1];
            if( parm == NULL ) {
                if( ! inside_decl_scope ) {
                    SetCurrScope( parm_scope );
                }

                if( tinfo->defarg_list[i] == NULL ) {
                    /* the rewrite stuff would have killed our location so approximate */
                    SetErrLoc( &start_locn );
                    CErr1( ERR_TOO_FEW_TEMPLATE_PARAMETERS );
                    something_went_wrong = TRUE;
                    break;  /* from for loop */
                } else {
                    void (*last_source)( void );
                    REWRITE *save_token;
                    REWRITE *last_rewrite;
                    REWRITE *defarg_rewrite;

                    ParseFlush();
                    save_token = RewritePackageToken();
                    last_source = SetTokenSource( RewriteToken );
                    defarg_rewrite = tinfo->defarg_list[i];
                    last_rewrite = RewriteRewind( defarg_rewrite );

                    if( arg_type != NULL ) {
                        parm = ParseTemplateIntDefArg();
                    } else {
                        parm = ParseTemplateTypeDefArg();
                    }

                    RewriteClose( last_rewrite );
                    ResetTokenSource( last_source );
                    RewriteRestoreToken( save_token );
                }
            }

            if( parm == NULL ) {
                something_went_wrong = TRUE;
                break;
            }

            if( parm->op != PT_TYPE ) {
                if( arg_type != NULL ) {
                    if( inside_decl_scope && ! currentTemplate->all_generic ) {
                        parm = AnalyseRawExpr( parm );
                        if( parm->op == PT_ERROR ) {
                            something_went_wrong = TRUE;
                        }
                    } else {
                        parm = processIndividualParm( arg_type, parm );

                        if( parm->op == PT_ERROR ) {
                            something_went_wrong = TRUE;
                        }
                    }
                } else {
                    /* non-type parameter supplied for type argument */
                    PTreeErrorExpr( parm, ERR_NON_TYPE_PROVIDED_FOR_TYPE );
                    something_went_wrong = TRUE;
                }
            } else {
                if( arg_type != NULL ) {
                    /* type parameter supplied for non-type argument */
                    PTreeErrorExpr( parm, ERR_TYPE_PROVIDED_FOR_NON_TYPE );
                    something_went_wrong = TRUE;
                }
            }
            list->u.subtree[1] = parm;

            SetCurrScope( save_scope );
            if( something_went_wrong )
                break;

            if( ! inside_decl_scope ) {
                injectTemplateParm( parm_scope, parm, tprimary->arg_names[i] );
                arg_type = TypedefRemove( tprimary->type_list[i] );
            }

            ++i;
            if( i >= tprimary->num_args )
                break;

            if( list->u.subtree[0] == NULL ) {
                list->u.subtree[0] = PTreeBinary( CO_LIST, NULL, NULL );
            }
        }

        SetCurrScope( save_scope );

        if( ! inside_decl_scope ) {
            /* we don't need the parm_scope any more */
            ScopeSetEnclosing( parm_scope, NULL );
            ScopeBurn( parm_scope );
        }
    }

    if( something_went_wrong ) {
        NodeFreeDupedExpr( parms );
        parms = NULL;
    }
    return( parms );
}


static boolean sameConstantInt( SYMBOL s1, SYMBOL s2 )
{
    INT_CONSTANT con1;
    INT_CONSTANT con2;

    SymConstantValue( s1, &con1 );
    SymConstantValue( s2, &con2 );
    return 0 == U64Cmp( &con1.value, &con2.value );
}

boolean TemplateParmEqual( SYMBOL parm1, SYMBOL parm2 )
/*****************************************************/
{
    SYMBOL sym1;
    SYMBOL sym2;

    if( SymIsConstantInt( parm1 ) && SymIsConstantInt( parm2 ) ) {
        return sameConstantInt( parm1, parm2 );
    }
    if( SymIsTypedef( parm1 ) && SymIsTypedef( parm2 ) ) {
        return( TypesIdentical( parm1->sym_type, parm2->sym_type ) );
    }
    sym1 = SymAddressOf( parm1 );
    sym2 = SymAddressOf( parm2 );
    if( sym1 != NULL && sym2 != NULL ) {
        return( sym1 == sym2 );
    }
    return( FALSE );
}

static boolean parmsDifferent( SYMBOL temp_arg, PTREE temp_parm )
{
    SYMBOL sym;

    if( SymIsConstantInt( temp_arg ) ) {
        INT_CONSTANT con;
        switch( temp_parm->op ) {
        case PT_INT_CONSTANT:
            SymConstantValue( temp_arg, &con );
            if( 0 == U64Cmp( &con.value, &temp_parm->u.int64_constant ) ) {
                return( FALSE );
            }
            break;
        }
    } else if( SymIsTypedef( temp_arg ) ) {
        if( temp_parm->op == PT_TYPE ) {
            if( TypesIdentical( temp_arg->sym_type, temp_parm->type ) ) {
                return( FALSE );
            }
        }
    } else {
        sym = SymAddressOf( temp_arg );
        if( sym != NULL ) {
            if( temp_parm->op == PT_SYMBOL ) {
                if( sym == temp_parm->u.symcg.symbol ) {
                    return( FALSE );
                }
            }
        }
    }
    return( TRUE );
}

static SCOPE sameParms( CLASS_INST *inst, PTREE parms )
{
    SCOPE parm_scope;
    SCOPE inst_scope;
    SYMBOL curr;
    SYMBOL stop;
    PTREE list;
    PTREE parm;

    list = parms;
    inst_scope = inst->scope;
    parm_scope = inst_scope->enclosing;
    if( ScopeType( parm_scope, SCOPE_TEMPLATE_SPEC_PARM ) ) {
        parm_scope = parm_scope->enclosing;
    }
    curr = NULL;
    stop = ScopeOrderedStart( parm_scope );
    for(;;) {
        if( list == NULL ) {
            DbgAssert( ScopeOrderedNext( stop, curr ) == NULL );
            return( inst_scope );
        }
        curr = ScopeOrderedNext( stop, curr );
        if( curr == NULL ) break;
        parm = list->u.subtree[1];
        if( parmsDifferent( curr, parm ) ) break;
        list = list->u.subtree[0];
    }
    return( NULL );
}

static SCOPE findInstScope( TEMPLATE_SPECIALIZATION *tspec, PTREE parms,
                            CLASS_INST **inst )
{
    CLASS_INST *curr;
    SCOPE inst_scope;

    RingIterBeg( tspec->instantiations, curr ) {
        inst_scope = sameParms( curr, parms );
        if( inst_scope != NULL ) {
            *inst = curr;
            return( inst_scope );
        }
    } RingIterEnd( curr )
    return( NULL );
}

static TYPE checkAlreadyDone( TEMPLATE_SPECIALIZATION *tspec, PTREE parms,
                              CLASS_INST **inst )
{
    SCOPE inst_scope;

    inst_scope = findInstScope( tspec, parms, inst );
    if( inst_scope != NULL ) {
        /* return previously instantiated class type */
        return( firstSymbol( inst_scope )->sym_type );
    }
    return( NULL );
}

static void setDirectiveFlags( CLASS_INST *inst, tc_instantiate control )
{
    if( control & TCI_NO_MEMBERS ) {
        inst->dont_process = TRUE;
    } else if( control & TCI_EXPLICIT_FULL ) {
        inst->dont_process = FALSE;
        inst->must_process = TRUE;
    }
}

static CLASS_INST *newClassInstantiation( TEMPLATE_SPECIALIZATION *tspec,
                                          SCOPE scope, tc_instantiate control )
{
    CLASS_INST *new_inst;

    new_inst = RingCarveAlloc( carveCLASS_INST, &(tspec->instantiations) );
    scope->owner.inst = new_inst;
    new_inst->scope = scope;
    new_inst->inlines_scope = NULL;
    new_inst->inlines_enclosing = NULL;
    new_inst->inlines = NULL;
    new_inst->members = NULL;
    new_inst->locn.src_file = NULL;
    new_inst->must_process = FALSE;
    new_inst->dont_process = FALSE;
    new_inst->processed = FALSE;
    new_inst->specific = FALSE;
    new_inst->locn_set = FALSE;
    new_inst->free = FALSE;
    if( control & TCI_SPECIFIC ) {
        new_inst->specific = TRUE;
    }
    setDirectiveFlags( new_inst, control );
    templateData.keep_going = TRUE;
    return( new_inst );
}

static SYMBOL templateArgSym( symbol_class sc, TYPE type )
{
    SYMBOL sym;

    sym = AllocSymbol();
    sym->id = sc;
    sym->sym_type = type;
    return( sym );
}

static SYMBOL templateArgTypedef( TYPE type )
{
    SYMBOL tsym;

    tsym = templateArgSym( SC_TYPEDEF, type );
    return tsym;
}

static void injectTemplateParm( SCOPE scope, PTREE parm, char *name )
{
    SYMBOL addr_sym;
    SYMBOL sym;
    TYPE parm_type;

    parm_type = parm->type;
    switch( parm->op ) {
    case PT_INT_CONSTANT:
        sym = templateArgSym( SC_STATIC, parm_type );
        DgStoreConstScalar( parm, parm_type, sym );
        break;
    case PT_TYPE:
        sym = templateArgTypedef( parm_type );
        break;
    case PT_SYMBOL:
        addr_sym = parm->u.symcg.symbol;
        if( PointerType( parm_type ) != NULL ) {
            parm_type = MakePointerTo( addr_sym->sym_type );
        } else {
            parm_type = addr_sym->sym_type;
        }
        sym = templateArgSym( SC_ADDRESS_ALIAS, parm_type );
        sym->u.alias = addr_sym;
        break;
    DbgDefault( "template parms are corrupted" );
    }
    if( sym != NULL ) {
        if( name == NULL ) {
            name = NameDummy();
        }
        sym = ScopeInsert( scope, sym, name );
    }
}

static void injectTemplateParms( TEMPLATE_SPECIALIZATION *tspec, SCOPE scope,
                                 PTREE parms, boolean unnamed )
{
    PTREE list;
    char **pname;
    char *name;

    pname = NULL;
    if( tspec != NULL ) {
        pname = tspec->arg_names;
    }
    for( list = parms; list != NULL; list = list->u.subtree[0] ) {
        if( ! unnamed && ( pname != NULL ) ) {
            name = *pname;
            ++pname;
        } else {
            name = NameDummy();
        }
        if( list->u.subtree[1] ) {
            injectTemplateParm( scope, list->u.subtree[1], name );
        }
    }
}

static TYPE instantiateClass( TEMPLATE_INFO *tinfo, PTREE parms,
                              TEMPLATE_SPECIALIZATION *tspec,
                              SCOPE spec_parm_scope,
                              TOKEN_LOCN *locn, tc_instantiate control )
{
    boolean nothing_to_do;
    TYPE already_instantiated;
    TYPE new_type;
    SCOPE file_scope;
    SCOPE save_scope;
    SCOPE inst_scope;
    SCOPE parm_scope;
    CLASS_INST *curr_instantiation;

    curr_instantiation = NULL;
    already_instantiated = checkAlreadyDone( tspec, parms,
                                             &curr_instantiation );
    if( already_instantiated != NULL ) {
        setDirectiveFlags( curr_instantiation, control );
        nothing_to_do = FALSE;
        if( TypeDefined( already_instantiated ) ) {
            nothing_to_do = TRUE;
        } else if( control & TCI_NO_CLASS_DEFN ) {
            nothing_to_do = TRUE;
        } else {
            already_instantiated = StructType( already_instantiated );
            if( StructOpened( already_instantiated ) != NULL ) {
                /* we're already in the middle of defining this type */
                nothing_to_do = TRUE;
            }
        }
        if( nothing_to_do ) {
            if( spec_parm_scope != NULL ) {
                ScopeBurn( spec_parm_scope );
            }
            return( already_instantiated );
        }
    }
    save_scope = GetCurrScope();
    file_scope = SymScope( tinfo->sym );
    if( already_instantiated != NULL ) {
        inst_scope = curr_instantiation->scope;
        parm_scope = inst_scope->enclosing;

        DbgAssert( ( ScopeType( parm_scope, SCOPE_TEMPLATE_PARM )
                  && ( spec_parm_scope == NULL ) )
                || ( ScopeType( parm_scope, SCOPE_TEMPLATE_SPEC_PARM )
                  && ( spec_parm_scope != NULL ) ) );
        if( ScopeType( parm_scope, SCOPE_TEMPLATE_SPEC_PARM ) ) {
            parm_scope = parm_scope->enclosing;
        }
        ScopeClear( parm_scope );
        ScopeSetParmClass( parm_scope, tinfo );
        SetCurrScope( inst_scope );
    } else {
        SetCurrScope( file_scope );
        parm_scope = ScopeBegin( SCOPE_TEMPLATE_PARM );
        ScopeSetParmClass( parm_scope, tinfo );
        if( spec_parm_scope != NULL ) {
            /*
             * In the case of a template specialization we have to use
             * two different parameter scopes:
             *
             * SCOPE_TEMPLATE_PARM is only used for mangling symbols
             * names (see fnname.c, appendScopeMangling)
             *
             * SCOPE_TEMPLATE_SPEC_PARM is used for the template parms
             * for the template specialization
             */
            ScopeSetEnclosing( spec_parm_scope, parm_scope );
            SetCurrScope( spec_parm_scope );
        }
        inst_scope = ScopeBegin( SCOPE_TEMPLATE_INST );
        curr_instantiation = newClassInstantiation( tspec, inst_scope,
                                                    control );
        curr_instantiation->locn = *locn;
        curr_instantiation->locn_set = TRUE;
    }

    injectTemplateParms( tspec, parm_scope, parms, spec_parm_scope != NULL );
    new_type = doParseClassTemplate( tspec, tspec->defn, locn, control );

    SetCurrScope( save_scope );
    return( new_type );
}

static TYPE instantiateUnboundClass( TEMPLATE_INFO *tinfo,
                                     TEMPLATE_SPECIALIZATION *tspec,
                                     PTREE parms, char *name )
{
    TYPE new_type;
    SCOPE file_scope;
    SCOPE save_scope;
    SCOPE parm_scope;

    save_scope = GetCurrScope();
    file_scope = SymScope( tinfo->sym );
    SetCurrScope( file_scope );
    parm_scope = ScopeBegin( SCOPE_TEMPLATE_PARM );
    ScopeSetParmClass( parm_scope, tinfo );
    injectTemplateParms( tspec, parm_scope, parms, FALSE );
    new_type = ClassUnboundTemplate( name );
    ScopeOpen( new_type->u.c.scope );
    SetCurrScope( save_scope );
    return( new_type );
}

static TEMPLATE_SPECIALIZATION *
findTemplateClassSpecialization( TEMPLATE_INFO *tinfo, PTREE parms,
                                 SCOPE *parm_scope )
{
    struct candidate_ring {
        struct candidate_ring *next;
        TEMPLATE_SPECIALIZATION *tspec;
        SCOPE parm_scope;
        unsigned idx;
    } *candidate_list;
    struct candidate_ring *candidate_iter;

    TEMPLATE_SPECIALIZATION *curr_spec;
    TEMPLATE_SPECIALIZATION *tspec;
    TEMPLATE_SPECIALIZATION *tprimary;
    PTREE spec_list;
    unsigned num_args;
    unsigned i;
    boolean ambiguous;

    candidate_list = NULL;
    tprimary = RingFirst( tinfo->specializations );
    num_args = tprimary->num_args;
    ambiguous = FALSE;

#ifndef NDEBUG
    if( PragDbgToggle.templ_spec && ( tinfo->nr_specs > 1 )) {
        VBUF vbuf;

        FormatPTreeList( parms, &vbuf );
        printf( "try to find template class specialisation for %s<%s>\n",
                tinfo->sym->name->name, vbuf.buf );
        VbufFree( &vbuf );
    }
#endif

    i = 0;
    RingIterBeg( tinfo->specializations, curr_spec ) {
        spec_list = curr_spec->spec_args;
        if( spec_list != NULL ) {
            SCOPE parm_scope;
            void *binding_handle;

            parm_scope = ScopeCreate( SCOPE_TEMPLATE_SPEC_PARM );
            ScopeSetEnclosing( parm_scope, curr_spec->decl_scope );

            BindExplicitTemplateArguments( parm_scope, NULL );

            binding_handle = BindGenericTypes( parm_scope, spec_list,
                                               parms, FALSE );
            if( binding_handle ) {
                ClearGenericBindings( binding_handle );

#ifndef NDEBUG
                if( PragDbgToggle.templ_spec && ( tinfo->nr_specs > 1 )) {
                    VBUF vbuf;

                    FormatPTreeList( spec_list, &vbuf );
                    printf( "found specialisation candidate %s<%s>\n",
                            tinfo->sym->name->name, vbuf.buf );
                    VbufFree( &vbuf );
                }
#endif

                /* we have found a matching specialization, use partial
                 * ordering rules to determine which one to use. */
                if( candidate_list != NULL ) {
                    RingIterBegSafe( candidate_list, candidate_iter ) {
                        boolean curr_at_least_as_specialized;
                        boolean candidate_at_least_as_specialized;

                        curr_at_least_as_specialized =
                            curr_spec->ordering[ candidate_iter->idx / 8 ] & ( 1 << ( candidate_iter->idx & 7 ) );
                        candidate_at_least_as_specialized =
                            candidate_iter->tspec->ordering[ i / 8 ] & ( 1 << ( i & 7 ) );

                        if( curr_at_least_as_specialized
                         && ! candidate_at_least_as_specialized ) {
                            ScopeBurn( candidate_iter->parm_scope );
                            RingPrune( &candidate_list, candidate_iter );
                        } else if( candidate_at_least_as_specialized
                                && ! curr_at_least_as_specialized ) {
                            ScopeBurn( parm_scope );
                            parm_scope = NULL;
                            break;
                        }
                    } RingIterEndSafe( candidate_iter )
                }

                if( parm_scope != NULL ) {
                    candidate_iter =
                        RingAlloc( &candidate_list,
                                   sizeof( struct candidate_ring ) );
                    candidate_iter->tspec = curr_spec;
                    candidate_iter->parm_scope = parm_scope;
                    candidate_iter->idx = i;
                }
            }
            else
            {
                ScopeBurn( parm_scope );
                parm_scope = NULL;
            }

            i++;
        }
    } RingIterEnd( curr_spec );

    if( candidate_list == NULL ) {
        /* no matching specialization found, use primary template */
        tspec = RingFirst( tinfo->specializations );

#ifndef NDEBUG
        if( PragDbgToggle.templ_spec && ( tinfo->nr_specs > 1 )) {
            printf( "chose primary template\n" );
            DumpTemplateInfo( tinfo );
        }
#endif
    } else if( RingFirst( candidate_list ) == RingLast( candidate_list ) ) {
        /* exactly one matching specialization found, use it */

        candidate_iter = RingFirst( candidate_list );
        tspec = candidate_iter->tspec;
        *parm_scope = candidate_iter->parm_scope;

        RingFree( &candidate_list );

#ifndef NDEBUG
        if( PragDbgToggle.templ_spec && ( tinfo->nr_specs > 1 )) {
            printf( "chose template specialisation\n" );
            DumpTemplateSpecialization( tspec );
        }
#endif

    } else {
        CErr2p( ERR_TEMPLATE_SPECIALIZATION_AMBIGUOUS, tinfo->sym );

        /* free instantiation parameters */
        RingIterBeg( candidate_list, candidate_iter ) {
            AddNoteMessage( INF_CANDIATE_DEFINITION,
                            &candidate_iter->tspec->locn );
            ScopeBurn( candidate_iter->parm_scope );
        } RingIterEnd( candidate_iter )

        tspec = tprimary;
    }

    return tspec;
}

TYPE TemplateClassInstantiation( PTREE tid, PTREE parms,
                                 tc_instantiate control )
{
    SYMBOL class_template;
    char *template_name;
    TYPE type_instantiated;
    SCOPE parm_scope;
    TEMPLATE_INFO *tinfo;
    TEMPLATE_SPECIALIZATION *tprimary;
    TEMPLATE_SPECIALIZATION *tspec;

    type_instantiated = TypeError;
    class_template = NULL;

    if( tid->op == PT_ID ) {
        template_name = tid->u.id.name;
        if( tid->sym_name != NULL ) {
            if( ( tid->sym_name->name_type != NULL )
             && SymIsClassTemplateModel( tid->sym_name->name_type ) ) {
                class_template = tid->sym_name->name_type;
            } else {
                class_template = ClassTemplateLookup( GetCurrScope(),
                                                      template_name );
            }
        }
    } else {
        /* we are dealing with a scoped template here */
        PTREE right;

        DbgAssert( NodeIsBinaryOp( tid, CO_STORAGE ) );

        right = tid->u.subtree[1];
        DbgAssert( ( right->op == PT_ID ) );

        template_name = right->u.id.name;

        DbgAssert( tid->sym_name != NULL );
        class_template = tid->sym_name->name_type;
    }

    if( class_template != NULL ) {
        tinfo = class_template->u.tinfo;
        tprimary = RingFirst( tinfo->specializations );
        parms = processClassTemplateParms( tinfo, parms );
        if( parms != NULL ) {
            /* parms have been validated; we can instantiate the class! */
            if( ScopeAccessType( SCOPE_TEMPLATE_DECL ) ) {
                type_instantiated = tinfo->unbound_type;

                /* we could be inside a function template? */
                tspec = RingFirst( tinfo->specializations );

                type_instantiated =
                    instantiateUnboundClass( tinfo, tspec, parms,
                                             template_name );

                NodeFreeDupedExpr( parms );
            } else {
                parm_scope = NULL;
                tspec = findTemplateClassSpecialization( tinfo, parms,
                                                         &parm_scope );

                type_instantiated =
                    instantiateClass( tinfo, parms, tspec, parm_scope,
                                      &(tid->locn), control );
                NodeFreeDupedExpr( parms );
            }
        }
    } else {
        /* TODO: I guess we need some error handling here */
        DbgAssert( 0 );
        PTreeFreeSubtrees( parms );
    }
    if( control & TCI_NO_DECL_SPEC ) {
        PTreeFreeSubtrees( tid );
        return( NULL );
    }
    return( type_instantiated );
}

void TemplateClassDirective( PTREE list, tc_directive tcd_control )
/*****************************************************************/
{
    DECL_SPEC *dspec;
    PTREE tid;
    PTREE parms;
    tc_instantiate tci_control;

    tid = list->u.subtree[0];
    parms = list->u.subtree[1];
    PTreeFree( list );
    tci_control = TCI_NO_DECL_SPEC;
    if( tcd_control & TCD_EXTERN ) {
        tci_control |= TCI_NO_MEMBERS;
    }
    if( tcd_control & TCD_INSTANTIATE ) {
        tci_control |= TCI_EXPLICIT_FULL;
    }
    dspec = PTypeClassInstantiation( TemplateClassInstantiation( tid, parms, tci_control ), tid );
    DbgAssert( dspec == NULL );
}

static PTREE fakeUpParm( SYMBOL sym )
{
    PTREE parm;

    parm = NULL;
    switch( sym->id ) {
    case SC_STATIC:
        parm = PTreeIntConstant( sym->u.uval, TYP_SINT );
        parm->type = sym->sym_type;
        break;
    case SC_ADDRESS_ALIAS:
        parm = MakeNodeSymbol( sym->u.alias );
        break;
    }
    DbgAssert( parm != NULL );
    return( parm );
}

static PTREE fakeUpTemplateParms( SCOPE parm_scope, arg_list *type_args )
{
    TYPE *curr_type_arg;
    PTREE parm;
    PTREE parms;
    SYMBOL curr;
    SYMBOL stop;
    unsigned num_parms;

    curr_type_arg = type_args->type_list;
    parms = NULL;
    curr = NULL;
    stop = ScopeOrderedStart( parm_scope );
    for(;;) {
        curr = ScopeOrderedNext( stop, curr );
        if( curr == NULL ) break;
        if( curr->id == SC_TYPEDEF ) {
            parm = PTreeType( *curr_type_arg );
            ++curr_type_arg;
        } else {
            parm = fakeUpParm( curr );
        }
        parms = PTreeBinary( CO_LIST, parms, parm );
    }
    parms = NodeReverseArgs( &num_parms, parms );
    return( parms );
}

static TYPE makeBoundClass( SCOPE scope, char *name, SCOPE parm_scope,
                            arg_list *type_args, TOKEN_LOCN *locn )
{
    TYPE type_instantiated;
    SYMBOL class_template;
    TEMPLATE_INFO *tinfo;
    TEMPLATE_SPECIALIZATION *tspec;
    PTREE parms;

    type_instantiated = NULL;
    class_template = ClassTemplateLookup( scope, name );
    if( class_template != NULL ) {
        parms = fakeUpTemplateParms( parm_scope, type_args );
        tinfo = class_template->u.tinfo;
        tspec = RingFirst( tinfo->specializations );
        type_instantiated =
            instantiateClass( tinfo, parms, tspec, NULL, locn, TCI_NULL );
        PTreeFreeSubtrees( parms );
    }
    return( type_instantiated );
}

TYPE TemplateUnboundInstantiate( TYPE unbound_class, arg_list *type_args, TOKEN_LOCN *locn )
/******************************************************************************************/
{
    char *template_name;
    SCOPE template_scope;
    SCOPE parm_scope;
    TYPE new_type;

    new_type = unbound_class->of;
    if( new_type == NULL ) {
        parm_scope = TemplateClassParmScope( unbound_class );
        if( parm_scope != NULL ) {
            template_scope = TypeScope( unbound_class );
            template_name = SimpleTypeName( unbound_class );
            DbgAssert( template_name != NULL );
            new_type = makeBoundClass( template_scope, template_name,
                                       parm_scope, type_args, locn );
        }
    }
    return( new_type );
}

void TemplateHandleClassMember( DECL_INFO *dinfo )
/************************************************/
{
    TEMPLATE_DATA *data;
    TOKEN_LOCN *locn;
    REWRITE *r;

    DbgAssert( dinfo->template_member );
    r = ParseGetRecordingInProgress( &locn );
    r = RewritePackageClassTemplateMember( r, locn );
    data = currentTemplate;
    data->member_defn = r;
    data->member_found = TRUE;
    data->template_name = SimpleTypeName( dinfo->id->u.subtree[0]->type );
    data->template_scope =
        ScopeNearestFileOrClass( TypeScope( dinfo->id->u.subtree[0]->type )->enclosing );
    data->unbound_type = dinfo->id->u.subtree[0]->type;
    FreeDeclInfo( dinfo );
}

static boolean sameParmArgNames( SCOPE parm_scope, char **arg_names )
{
    SYMBOL curr;
    SYMBOL stop;

    curr = NULL;
    stop = ScopeOrderedStart( parm_scope );
    for(;;) {
        curr = ScopeOrderedNext( stop, curr );
        if( curr == NULL ) break;
        if( curr->name->name != *arg_names ) {
            return( FALSE );
        }
        ++arg_names;
    }
    return( TRUE );
}

void TemplateMemberAttachDefn( DECL_INFO *dinfo )
{
    CLASS_INST *instance;
    MEMBER_INST *member;

    DbgAssert( ScopeType( GetCurrScope(), SCOPE_TEMPLATE_INST ) );
    instance = GetCurrScope()->owner.inst;
    DbgAssert( instance != NULL );

    member = RingCarveAlloc( carveMEMBER_INST, &(instance->members) );
    member->dinfo = dinfo;
    member->scope = GetCurrScope();
    member->class_parm_scope = instance->scope->enclosing;
    member->class_parm_enclosing = member->class_parm_scope->enclosing;
}

/*
 * real instantiation of the template member takes place in
 * TemplateProcessInstantiations (but only if the symbol has been
 * referenced)
 */
static void instantiateMember( TEMPLATE_INFO *tinfo,
                               TEMPLATE_SPECIALIZATION *tspec,
                               CLASS_INST *instance,
                               TEMPLATE_MEMBER *member )
{
    SCOPE save_scope;
    SCOPE file_scope;
    SCOPE inst_scope;
    SCOPE class_inst_scope;
    SCOPE class_parm_scope;
    SCOPE save_parm_enclosing;
    SCOPE parm_scope;
    char **member_arg_names;
    TOKEN_LOCN *locn;
    auto TEMPLATE_CONTEXT context;

    save_scope = GetCurrScope();
    save_parm_enclosing = NULL;
    class_inst_scope = instance->scope;
    class_parm_scope = class_inst_scope->enclosing;
    member_arg_names = member->arg_names;
    if( tspec->arg_names != member_arg_names ||
        ! sameParmArgNames( class_parm_scope, member_arg_names ) ) {
        file_scope = SymScope( tinfo->sym );

        if( ScopeType( class_parm_scope, SCOPE_TEMPLATE_SPEC_PARM ) ) {
            save_parm_enclosing =
                ScopeSetEnclosing( class_parm_scope->enclosing, file_scope );
            SetCurrScope( class_parm_scope->enclosing );
        } else {
            SetCurrScope( file_scope );
        }
        parm_scope = ScopeBegin( ScopeId( class_parm_scope ) );
        copyWithNewNames( class_parm_scope, member_arg_names );
        if( ScopeType( parm_scope, SCOPE_TEMPLATE_PARM ) ) {
            ScopeSetParmClass( parm_scope, tinfo );
        }
        ScopeEstablishEnclosing( class_inst_scope, parm_scope );
    } else {
        /* template instantiation parms are identical to class instantiation */
        parm_scope = class_parm_scope;
        SetCurrScope( parm_scope );
    }
    inst_scope = ScopeBegin( SCOPE_TEMPLATE_INST );
    inst_scope->owner.inst = instance;
    locn = NULL;
    if( instance->locn_set ) {
        locn = &(instance->locn);
    }
    pushInstContext( &context, TCTX_MEMBER_DEFN, locn, NULL );
    ParseClassMemberInstantiation( member->defn );
    popInstContext();
    ScopeSetEnclosing( class_inst_scope, class_parm_scope );
    if( save_parm_enclosing != NULL ) {
        ScopeSetEnclosing( class_parm_scope->enclosing, save_parm_enclosing );
    }
    SetCurrScope( save_scope );
}

static TYPE classTemplateType( CLASS_INST *instance )
{
    SCOPE inst_scope;
    SYMBOL class_sym;

    inst_scope = instance->scope;
    class_sym = firstSymbol( inst_scope );
    return( class_sym->sym_type );
}

static boolean classTemplateWasDefined( CLASS_INST *instance )
{
    return( TypeDefined( classTemplateType( instance ) ) );
}

static boolean makeSureSymIsAMember( SCOPE scope, SYMBOL sym )
{
    if( templateData.extra_members ) {
        if( ScopeClass( scope ) == NULL ) {
            SetErrLoc( &sym->locn->tl );
            CErr2p( ERR_INVALID_TEMPLATE_MEMBER, templateData.extra_member_class );
            return( TRUE );
        }
    }
    return( FALSE );
}

SYMBOL TemplateFunctionTranslate( SYMBOL sym, SCOPE *parse_scope )
/****************************************************************/
{
    SCOPE sym_scope;
    SYMBOL replace_sym;

    sym_scope = SymScope( sym );
    replace_sym = templateData.translate_fn;
    if( replace_sym != NULL ) {
        /* so any inline functions that are parsed during this function are OK */
        templateData.translate_fn = NULL;
        sym = replace_sym;
        *parse_scope = sym_scope->enclosing;
    } else {
        makeSureSymIsAMember( sym_scope, sym );
        *parse_scope = sym_scope;
    }
    return( sym );
}

tc_fn_control TemplateFunctionControl( void )
/*******************************************/
{
    tc_fn_control ret;

    ret = templateData.fn_control;
    templateData.fn_control = TCF_NULL;
    return( ret );
}


boolean TemplateVerifyDecl( SYMBOL sym )
/**************************************/
{
    SCOPE sym_scope;

    sym_scope = SymScope( sym );
    return( makeSureSymIsAMember( sym_scope, sym ) );
}

void TemplateFunctionInstantiate( FN_TEMPLATE *fn_templ,
                                  FN_TEMPLATE_INST *fn_inst )
/***********************************************************/
{
    SYMBOL save_fn;
    SYMBOL fn_sym;
    SYMBOL bound_sym;
    SCOPE save_scope;
    SCOPE parm_scope;
    auto TEMPLATE_CONTEXT context;

    fn_sym = fn_templ->sym;
    bound_sym = fn_inst->bound_sym;

    save_scope = GetCurrScope();
    parm_scope = fn_inst->parm_scope;
    SetCurrScope( fn_inst->inst_scope );
    ScopeSetEnclosing( parm_scope, SymScope( fn_sym ) );
    ScopeSetParmFn( parm_scope, fn_sym->u.defn );

    bound_sym->flag |= SF_TEMPLATE_FN;
    bound_sym->u.alias = fn_sym;
    save_fn = templateData.translate_fn;
    templateData.translate_fn = bound_sym;
    pushInstContext( &context, TCTX_FN_DEFN, &bound_sym->locn->tl, bound_sym );
    ParseFunctionInstantiation( fn_templ->defn );
    popInstContext();
    templateData.translate_fn = save_fn;

    ScopeSetEnclosing( parm_scope, NULL );
    SetCurrScope( save_scope );
}

static void processFunctionTemplateInstantiations( void )
{
    FN_TEMPLATE *curr_defn;
    FN_TEMPLATE_INST *curr_inst;
    boolean keep_going;

    do {
        keep_going = FALSE;

        RingIterBeg( allFunctionTemplates, curr_defn ) {
            RingIterBeg( curr_defn->instantiations, curr_inst ) {

                if( ! curr_inst->processed ) {
                    keep_going = TRUE;
                    curr_inst->processed = TRUE;
                    TemplateFunctionInstantiate( curr_defn, curr_inst );
                }

            } RingIterEnd( curr_inst )
        } RingIterEnd( curr_defn )
    } while( keep_going );
}

static void freeDefns( void )
{
    unsigned i;
    REWRITE *r;
    TEMPLATE_INFO *tinfo;
    TEMPLATE_SPECIALIZATION *tprimary;
    TEMPLATE_SPECIALIZATION *tspec;
    TEMPLATE_MEMBER *member;
    CLASS_INST *curr_instance;
    MEMBER_INST *curr_member;
    DECL_INFO *curr_inline;
    FN_TEMPLATE *curr_fn;

    RingIterBeg( allClassTemplates, tinfo ) {
        tprimary = RingFirst( tinfo->specializations );
        for( i = 0; i < tprimary->num_args; ++i ) {
            RewriteFree( tinfo->defarg_list[i] );
            tinfo->defarg_list[i] = NULL;
        }
        RingIterBeg( tinfo->specializations, tspec ) {
            RewriteFree( tspec->defn );
            tspec->defn = NULL;
            PTreeFreeSubtrees( tspec->spec_args );
            RingIterBeg( tspec->member_defns, member ) {
                RewriteFree( member->defn );
                member->defn = NULL;
            } RingIterEnd( member )

            RingIterBeg( tspec->instantiations, curr_instance ) {
                for(;;) {
                    curr_inline = RingPop( &(curr_instance->inlines) );
                    if( curr_inline == NULL ) break;
                    FreeDeclInfo( curr_inline );
                }

                for(;;) {
                    curr_member = RingPop( &(curr_instance->members) );
                    if( curr_member == NULL ) break;
                    FreeDeclInfo( curr_member->dinfo );
                    CarveFree( carveMEMBER_INST, curr_member );
                }
            } RingIterEnd( curr_instance)
        } RingIterEnd( tspec )
    } RingIterEnd( tinfo )
    RingIterBeg( allFunctionTemplates, curr_fn ) {
        r = curr_fn->defn;
        curr_fn->defn = NULL;
        RewriteFree( r );
    } RingIterEnd( curr_fn )
}

static void initLastSym( NAME_SPACE *ns, void *data )
{
    data = data;
    DbgAssert( data == NULL );
    ns->last_sym = ScopeOrderedLast( ns->scope );
}

static void finishUpNameSpace( NAME_SPACE *ns, void *data )
{
    SYMBOL last_sym;
    SYMBOL curr_last;

    data = data;
    DbgAssert( data == NULL );
    last_sym = ns->last_sym;
    curr_last = ScopeOrderedLast( ns->scope );
    if( curr_last != last_sym ) {
        // could generate more symbols by processing these ones
        //processNewFileSyms( ns, last_sym, curr_last );
        // ScopeOrderedLast( ns->scope ) may different than 'curr_last'
        ns->last_sym = curr_last;
        templateData.keep_going = TRUE;
    }
}

static void processInstantiationInlines( CLASS_INST *instance )
{
    DECL_INFO *curr_inline;
    DECL_INFO *prev_inline;
    SCOPE save_scope;
    SCOPE save_enclosing;

    save_scope = GetCurrScope();
    save_enclosing = NULL;
    if( instance->inlines_scope != NULL ) {
        // set up the scopes for instantiating inline member function
        save_enclosing = instance->inlines_scope->enclosing;
        instance->inlines_scope->enclosing = instance->inlines_enclosing;
        SetCurrScope( instance->inlines_scope );
    }
    prev_inline = NULL;

    RingIterBegSafe( instance->inlines, curr_inline ) {
        if( instance->must_process
         || ( curr_inline->sym->flag & SF_REFERENCED )
         || ( curr_inline->sym->sym_type->flag & TF1_VIRTUAL ) ) {

#ifndef NDEBUG
            if( PragDbgToggle.member_inst ) {
                printf( "instantiating inline template member: %s\n",
                        DbgSymNameFull( curr_inline->sym ) );
            }
#endif

            templateData.fn_control = TCF_NULL;
            if( instance->must_process ) {
                templateData.fn_control |= TCF_GEN_FUNCTION;
            }

            ClassProcessFunction( curr_inline, TRUE );
            RingPruneWithPrev( &instance->inlines,
                               curr_inline,
                               prev_inline );
            FreeDeclInfo( curr_inline );
            templateData.keep_going = TRUE;
        } else {
            prev_inline = curr_inline;
        }
    } RingIterEndSafe( curr_inline )

    if( instance->inlines_scope != NULL ) {
        instance->inlines_scope->enclosing = save_enclosing;
    }
    SetCurrScope( save_scope );
}

static void processInstantiationMembers( CLASS_INST *instance )
{
    MEMBER_INST *curr_member;
    MEMBER_INST *prev_member;
    SCOPE sym_scope;
    SCOPE save_scope;
    SCOPE save_class_parm_scope;
    SCOPE save_class_parm_enclosing;
    DECL_INFO *dinfo;

    prev_member = NULL;
    RingIterBegSafe( instance->members, curr_member ) {
        dinfo = curr_member->dinfo;

        if( instance->must_process
         || ( dinfo->sym->flag & SF_REFERENCED )
         || ( dinfo->sym->sym_type->flag & TF1_VIRTUAL ) ) {

#ifndef NDEBUG
            if( PragDbgToggle.member_inst ) {
                printf( "instantiating template member: %s\n",
                        DbgSymNameFull( dinfo->sym ) );
            }
#endif

            sym_scope = SymScope( dinfo->sym );
            save_scope = sym_scope->enclosing;

            save_class_parm_scope = instance->scope->enclosing;
            save_class_parm_enclosing = save_class_parm_scope->enclosing;
            sym_scope->enclosing = curr_member->scope;

            templateData.fn_control = TCF_NULL;
            if( instance->must_process ) {
                templateData.fn_control |= TCF_GEN_FUNCTION;
            }

            ClassProcessFunction( dinfo, FALSE );
            RingPruneWithPrev( &instance->members,
                               curr_member,
                               prev_member );
            FreeDeclInfo( dinfo );
            templateData.keep_going = TRUE;

            save_class_parm_scope->enclosing = save_class_parm_enclosing;
            instance->scope->enclosing = save_class_parm_scope;
            sym_scope->enclosing = save_scope;
        } else {
            prev_member = curr_member;
        }
    } RingIterEndSafe( curr_member )
}

void TemplateProcessInstantiations( void )
/****************************************/
{
    TEMPLATE_INFO *curr_tinfo;
    CLASS_INST *curr_instance;
    TEMPLATE_MEMBER *curr_member;
    TEMPLATE_SPECIALIZATION *tspec;
    TOKEN_LOCN *locn;
    auto TEMPLATE_CONTEXT context;

    /* NYI: only define extra members that are required */
    ScopeWalkAllNameSpaces( initLastSym, NULL );
    // instantiate any template functions (first pass)
    processFunctionTemplateInstantiations();
    for(;;) {
        verifyOKToProceed( NULL );

        CtxSetContext( CTX_FUNC_GEN );
        templateData.keep_going = ClassDefineRefdDefaults();
        CtxSetContext( CTX_SOURCE );

        // instantiate extra class members
        templateData.extra_members = TRUE;
        RingIterBeg( allClassTemplates, curr_tinfo ) {
            RingIterBeg( curr_tinfo->specializations, tspec ) {
                RingIterBeg( tspec->instantiations, curr_instance ) {
                    if( curr_instance->specific
                     || curr_instance->dont_process ) {
                        continue;
                    }
                    if( ! classTemplateWasDefined( curr_instance ) ) {
                        continue;
                    }
                    templateData.extra_member_class =
                        classTemplateType( curr_instance );

                    if( ! curr_instance->processed ) {
                        curr_instance->processed = TRUE;
                        RingIterBeg( tspec->member_defns, curr_member ) {
                            // loop nesting is critical because extra members cannot be
                            // generated if a class has not been instantiated
                            instantiateMember( curr_tinfo, tspec,
                                               curr_instance, curr_member );
                        } RingIterEnd( curr_member )
                    }

                    locn = NULL;
                    if( curr_instance->locn_set ) {
                        locn = &(curr_instance->locn);
                    }
                    pushInstContext( &context, TCTX_MEMBER_DEFN, locn, NULL );

                    processInstantiationInlines( curr_instance );
                    processInstantiationMembers( curr_instance );

                    popInstContext();

                } RingIterEnd( curr_instance )
            } RingIterEnd( tspec )
        } RingIterEnd( curr_tinfo )
        templateData.extra_members = FALSE;
        // instantiate any template functions (delta from previous pass)
        ScopeWalkAllNameSpaces( finishUpNameSpace, NULL );
        if( ! templateData.keep_going ) break;
    }
    templateData.extra_members = FALSE;
    freeDefns();
}

boolean TemplateMemberCanBeIgnored( void )
/****************************************/
{
    return( templateData.extra_members );
}

void TemplateSpecificDefnStart( PTREE tid, PTREE parms )
/*******************************************************/
{
    SYMBOL class_template;
    CLASS_INST *instance;
    TEMPLATE_INFO *tinfo;
    TEMPLATE_SPECIALIZATION *tprimary;
    SCOPE inst_scope;
    SCOPE parm_scope;
    char *name;

    if( tid->op == PT_ID ) {
        name = tid->u.id.name;
        if( tid->sym_name != NULL ) {
            if ( ( tid->sym_name->name_type != NULL )
              && SymIsClassTemplateModel( tid->sym_name->name_type ) ) {
                class_template = tid->sym_name->name_type;
            } else {
                class_template = ClassTemplateLookup( GetCurrScope(), name );
            }
        }
    } else {
        /* we are dealing with a scoped template here */
        PTREE right;

        DbgAssert( NodeIsBinaryOp( tid, CO_STORAGE ) );

        right = tid->u.subtree[1];
        DbgAssert( ( right->op == PT_ID ) );

        name = right->u.id.name;

        DbgAssert( tid->sym_name != NULL );
        class_template = tid->sym_name->name_type;
    }

    tinfo = class_template->u.tinfo;
    tprimary = RingFirst( tinfo->specializations );
    if( tprimary->corrupted ) {
        return;
    }
    parms = processClassTemplateParms( tinfo, parms );
    if( parms != NULL ) {
        /* parms have been validated; we can instantiate the class! */
        instance = NULL;
        inst_scope = findInstScope( tprimary, parms, &instance );
        if( inst_scope != NULL ) {
            instance->specific = TRUE;
            SetCurrScope( inst_scope );
        } else {
            parm_scope = ScopeBegin( SCOPE_TEMPLATE_PARM );
            ScopeSetParmClass( parm_scope, tinfo );
            inst_scope = ScopeBegin( SCOPE_TEMPLATE_INST );
            instance = newClassInstantiation( tprimary, inst_scope,
                                              TCI_SPECIFIC );
            injectTemplateParms( NULL, parm_scope, parms, FALSE );
        }
        DbgAssert( instance->specific );
        NodeFreeDupedExpr( parms );
    } else {
        tprimary->corrupted = TRUE;
    }
}

void TemplateSpecificDefnEnd( void )
/**********************************/
{
    if( ScopeType( GetCurrScope(), SCOPE_TEMPLATE_INST ) ) {
        ScopeEnd( SCOPE_TEMPLATE_INST );
        ScopeEnd( SCOPE_TEMPLATE_PARM );
    }
}

void TemplateSpecializationDefn( PTREE tid, PTREE parms )
/*******************************************************/
{
    unsigned arg_count;

    DbgAssert( currentTemplate != NULL );
    currentTemplate->spec_args = NodeReverseArgs( &arg_count, parms );
}

SCOPE TemplateClassInstScope( TYPE class_type )
/*********************************************/
{
    SCOPE inst_scope;

    inst_scope = NULL;
    if( class_type->flag & TF1_INSTANTIATION ) {
        inst_scope = class_type->u.c.scope->enclosing;
    }
    return( inst_scope );
}

SCOPE TemplateClassParmScope( TYPE class_type )
/*********************************************/
{
    SCOPE inst_scope;
    SCOPE parm_scope;

    parm_scope = NULL;
    if( class_type->flag & TF1_INSTANTIATION ) {
        inst_scope = TemplateClassInstScope( class_type );
        if( inst_scope != NULL ) {
            parm_scope = inst_scope->enclosing;
            if( ScopeType( parm_scope, SCOPE_TEMPLATE_SPEC_PARM ) ) {
                parm_scope = parm_scope->enclosing;
            }
        }
    } else if( class_type->flag & TF1_UNBOUND ) {
        parm_scope = class_type->u.c.scope->enclosing;
    }
    return( parm_scope );
}

SYMBOL TemplateSymFromClass( TYPE class_type )
/********************************************/
{
    SYMBOL sym;
    SCOPE inst_scope;

    sym = NULL;
    inst_scope = TemplateClassInstScope( class_type );
    if( inst_scope != NULL ) {
        sym = firstSymbol( inst_scope );
    }
    return( sym );
}

SYMBOL TemplateSetFnMatchable( SYMBOL sym )
/*****************************************/
{
    DbgAssert( sym->u.alias == NULL && SymIsFunction( sym ) );
    sym->flag |= SF_TEMPLATE_FN;
    return( sym );
}

boolean TemplateUnboundSame( TYPE ub1, TYPE ub2 )
/***********************************************/
{
    SYMBOL ub1_curr;
    SYMBOL ub1_stop;
    SYMBOL ub2_curr;
    SYMBOL ub2_stop;
    CLASSINFO *ub1_info;
    CLASSINFO *ub2_info;
    type_flag uf1;
    type_flag uf2;
    SCOPE ub1_parm_scope;
    SCOPE ub2_parm_scope;

    uf1 = ub1->flag;
    uf2 = ub2->flag;
    if( uf1 != uf2 || ( uf1 & TF1_UNBOUND ) == 0 ) {
        return( FALSE );
    }
    DbgAssert( ub1->of == NULL && ub2->of == NULL );
    ub1_info = ub1->u.c.info;
    ub2_info = ub2->u.c.info;
    if( ub1_info->name != ub2_info->name ) {
        return( FALSE );
    }
    /* both are instantiations of the same class */
    ub1_parm_scope = TemplateClassParmScope( ub1 );
    ub2_parm_scope = TemplateClassParmScope( ub2 );
    if( ub1_parm_scope == NULL || ub2_parm_scope == NULL ) {
        return( FALSE );
    }
    ub1_curr = NULL;
    ub2_curr = NULL;
    ub1_stop = ScopeOrderedStart( ub1_parm_scope );
    ub2_stop = ScopeOrderedStart( ub2_parm_scope );
    for(;;) {
        ub1_curr = ScopeOrderedNext( ub1_stop, ub1_curr );
        ub2_curr = ScopeOrderedNext( ub2_stop, ub2_curr );
        if( ub1_curr == NULL ) break;
        if( ub2_curr == NULL ) break;
        DbgAssert( ub1_curr->id == ub2_curr->id );
        if( ub1_curr->id != SC_TYPEDEF ) {
            if( ! TemplateParmEqual( ub1_curr, ub2_curr ) ) {
                return( FALSE );
            }
        } else {
            if( ! TypesIdentical( ub1_curr->sym_type, ub2_curr->sym_type ) ) {
                return( FALSE );
            }
        }
    }
    DbgAssert( ub1_curr == NULL && ub2_curr == NULL );
    return( TRUE );
}

TEMPLATE_INFO *TemplateClassInfoGetIndex( TEMPLATE_INFO *e )
{
    return( CarveGetIndex( carveTEMPLATE_INFO, e ) );
}

TEMPLATE_INFO *TemplateClassInfoMapIndex( TEMPLATE_INFO *e )
{
    return( CarveMapIndex( carveTEMPLATE_INFO, e ) );
}

FN_TEMPLATE *TemplateFunctionInfoGetIndex( FN_TEMPLATE *e )
{
    return( CarveGetIndex( carveFN_TEMPLATE, e ) );
}

FN_TEMPLATE *TemplateFunctionInfoMapIndex( FN_TEMPLATE *e )
{
    return( CarveMapIndex( carveFN_TEMPLATE, e ) );
}

static void markFreeTemplateSpecialization( void *p )
{
    TEMPLATE_SPECIALIZATION *s = p;

    s->free = TRUE;
}

static void markFreeTemplateInfo( void *p )
{
    TEMPLATE_INFO *s = p;

    s->free = TRUE;
}

static void markFreeMemberInst( void *p )
{
    MEMBER_INST *s = p;

    s->free = TRUE;
}

static void markFreeClassInst( void *p )
{
    CLASS_INST *s = p;

    s->free = TRUE;
}

static void markFreeFnTemplateDefn( void *p )
{
    FN_TEMPLATE *s = p;

    s->free = TRUE;
}

static void saveTemplateSpecialization( void *p, carve_walk_base *d )
{
    TEMPLATE_SPECIALIZATION *s = p;
    TEMPLATE_SPECIALIZATION *save_next;
    TEMPLATE_INFO *save_tinfo;
    SCOPE save_decl_scope;
    SRCFILE save_locn_src_file;
    REWRITE *save_defn;
    CLASS_INST *save_instantiations;
    PTREE save_spec_args;
    unsigned char *save_ordering;
    TEMPLATE_MEMBER *member;
    void *nti;
    unsigned i;
    auto void *member_buff[2];

    if( s->free ) {
        return;
    }
    save_next = s->next;
    s->next = CarveGetIndex( carveTEMPLATE_SPECIALIZATION, save_next );
    save_tinfo = s->tinfo;
    s->tinfo = CarveGetIndex( carveTEMPLATE_INFO, save_tinfo );
    save_decl_scope = s->decl_scope;
    s->decl_scope = ScopeGetIndex( save_decl_scope );
    save_locn_src_file = s->locn.src_file;
    s->locn.src_file = SrcFileGetIndex( save_locn_src_file );
    save_defn = s->defn;
    s->defn = RewriteGetIndex( save_defn );
    save_instantiations = s->instantiations;
    s->instantiations = CarveGetIndex( carveCLASS_INST, save_instantiations );
    save_spec_args = s->spec_args;
    s->spec_args = PTreeGetIndex( save_spec_args );
    save_ordering = s->ordering;
    s->ordering = ( save_ordering != NULL ) ? (void *) save_tinfo->nr_specs : NULL;
    PCHWriteCVIndex( d->index );
    PCHWrite( s, sizeof( *s ) );
    for( i = 0; i < s->num_args; ++i ) {
        nti = NameGetIndex( s->arg_names[i] );
        PCHWrite( &nti, sizeof( nti ) );
    }
    for( i = 0; i < s->num_args; ++i ) {
        nti = TypeGetIndex( s->type_list[i] );
        PCHWrite( &nti, sizeof( nti ) );
    }
    RingIterBeg( s->member_defns, member ){
        member_buff[0] = RewriteGetIndex( member->defn );
        if( member->arg_names != s->arg_names ) {
            member_buff[1] = s->arg_names;
            PCHWrite( member_buff, sizeof( member_buff ) );
            for( i = 0; i < s->num_args; ++i ) {
                nti = NameGetIndex( member->arg_names[i] );
                PCHWrite( &nti, sizeof( nti ) );
            }
        } else {
            member_buff[1] = NULL;
            PCHWrite( member_buff, sizeof( member_buff ) );
        }
    } RingIterEnd( member )
    member_buff[0] = NULL;
    member_buff[1] = NULL;
    PCHWrite( member_buff, sizeof( member_buff ) );
    if( save_ordering != NULL ) {
        PCHWrite( save_ordering,
                  16 * ( ( save_tinfo->nr_specs - 2 ) / 128 + 1 ) );
    }
    s->spec_args = save_spec_args;
    s->next = save_next;
    s->tinfo = save_tinfo;
    s->locn.src_file = save_locn_src_file;
    s->decl_scope = save_decl_scope;
    s->defn = save_defn;
    s->instantiations = save_instantiations;
    s->ordering = save_ordering;
}

static void saveTemplateInfo( void *p, carve_walk_base *d )
{
    TEMPLATE_INFO *s = p;
    TEMPLATE_INFO *save_next;
    TEMPLATE_SPECIALIZATION *save_specializations;
    TEMPLATE_SPECIALIZATION *tprimary;
    TYPE save_unbound_type;
    SYMBOL save_sym;
    void *defarg_index;
    unsigned i;

    if( s->free ) {
        return;
    }

    tprimary = RingFirst( s->specializations );

    save_next = s->next;
    s->next = CarveGetIndex( carveTEMPLATE_INFO, save_next );
    save_specializations = s->specializations;
    s->specializations = CarveGetIndex( carveTEMPLATE_SPECIALIZATION,
                                        save_specializations );
    save_unbound_type = s->unbound_type;
    s->unbound_type = TypeGetIndex( save_unbound_type );
    save_sym = s->sym;
    s->sym = SymbolGetIndex( save_sym );
    PCHWriteCVIndex( d->index );
    PCHWrite( s, sizeof( *s ) );
    for( i = 0; i < tprimary->num_args; ++i ) {
        defarg_index = RewriteGetIndex( s->defarg_list[i] );
        PCHWrite( &defarg_index, sizeof( defarg_index ) );
    }
    s->next = save_next;
    s->specializations = save_specializations;
    s->unbound_type = save_unbound_type;
    s->sym = save_sym;
}

static void saveMemberInst( void *p, carve_walk_base *d )
{
    MEMBER_INST *s = p;
    MEMBER_INST *save_next;
    DECL_INFO *save_dinfo;
    SCOPE save_scope;
    SCOPE save_class_parm_scope;
    SCOPE save_class_parm_enclosing;

    if( s->free ) {
        return;
    }
    save_next = s->next;
    s->next = CarveGetIndex( carveMEMBER_INST, save_next );
    save_dinfo = s->dinfo;
    s->dinfo = (void *) ( s->dinfo != NULL );
    save_scope = s->scope;
    s->scope = ScopeGetIndex( save_scope );
    save_class_parm_scope = s->class_parm_scope;
    s->class_parm_scope = ScopeGetIndex( save_class_parm_scope );
    save_class_parm_enclosing = s->class_parm_enclosing;
    s->class_parm_enclosing = ScopeGetIndex( save_class_parm_enclosing );
    PCHWriteCVIndex( d->index );
    PCHWrite( s, sizeof( *s ) );
    if( save_dinfo != NULL ) {
        PCHWriteDeclInfo( save_dinfo );
    }
    s->next = save_next;
    s->dinfo = save_dinfo;
    s->scope = save_scope;
    s->class_parm_scope = save_class_parm_scope;
    s->class_parm_enclosing = save_class_parm_enclosing;
}

static void saveClassInst( void *p, carve_walk_base *d )
{
    CLASS_INST *s = p;
    CLASS_INST *save_next;
    SCOPE save_scope;
    SCOPE save_inlines_scope;
    SCOPE save_inlines_enclosing;
    DECL_INFO *save_inlines;
    SRCFILE save_locn_src_file;

    if( s->free ) {
        return;
    }
    save_next = s->next;
    s->next = CarveGetIndex( carveCLASS_INST, save_next );
    save_scope = s->scope;
    s->scope = ScopeGetIndex( save_scope );
    save_inlines_scope = s->inlines_scope;
    s->inlines_scope = ScopeGetIndex( save_inlines_scope );
    save_inlines_enclosing = s->inlines_enclosing;
    s->inlines_enclosing = ScopeGetIndex( save_inlines_enclosing );
    save_inlines = s->inlines;
    s->inlines = (void *) ( s->inlines != NULL );
    save_locn_src_file = s->locn.src_file;
    s->locn.src_file = SrcFileGetIndex( save_locn_src_file );
    PCHWriteCVIndex( d->index );
    PCHWrite( s, sizeof( *s ) );
    if( save_inlines != NULL ) {
        PCHWriteDeclInfo( save_inlines );
    }
    s->next = save_next;
    s->scope = save_scope;
    s->inlines_scope = save_inlines_scope;
    s->inlines_enclosing = save_inlines_enclosing;
    s->inlines = save_inlines;
    s->locn.src_file = save_locn_src_file;
}

static void saveFnTemplateDefn( void *p, carve_walk_base *d )
{
    FN_TEMPLATE *s = p;
    FN_TEMPLATE *save_next;
    SYMBOL save_sym;
    REWRITE *save_defn;

    if( s->free ) {
        return;
    }
    save_next = s->next;
    s->next = CarveGetIndex( carveFN_TEMPLATE, save_next );
    save_sym = s->sym;
    s->sym = SymbolGetIndex( save_sym );
    save_defn = s->defn;
    s->defn = RewriteGetIndex( save_defn );
    PCHWriteCVIndex( d->index );
    PCHWrite( s, sizeof( *s ) );
    s->next = save_next;
    s->sym = save_sym;
    s->defn = save_defn;
}

pch_status PCHWriteTemplates( void )
{
    cv_index terminator = CARVE_NULL_INDEX;
    TEMPLATE_INFO *all_class_templates;
    FN_TEMPLATE *all_function_templates;
    auto carve_walk_base data;

    PCHWrite( &templateData.max_depth, sizeof( templateData.max_depth ) );
    all_class_templates = TemplateClassInfoGetIndex( allClassTemplates );
    PCHWrite( &all_class_templates, sizeof( all_class_templates ) );
    all_function_templates = TemplateFunctionInfoGetIndex( allFunctionTemplates );
    PCHWrite( &all_function_templates, sizeof( all_function_templates ) );
    CarveWalkAllFree( carveMEMBER_INST, markFreeMemberInst );
    CarveWalkAll( carveMEMBER_INST, saveMemberInst, &data );
    PCHWriteCVIndex( terminator );
    CarveWalkAllFree( carveCLASS_INST, markFreeClassInst );
    CarveWalkAll( carveCLASS_INST, saveClassInst, &data );
    PCHWriteCVIndex( terminator );
    CarveWalkAllFree( carveFN_TEMPLATE, markFreeFnTemplateDefn );
    CarveWalkAll( carveFN_TEMPLATE, saveFnTemplateDefn, &data );
    PCHWriteCVIndex( terminator );
    CarveWalkAllFree( carveTEMPLATE_SPECIALIZATION,
                      markFreeTemplateSpecialization );
    CarveWalkAll( carveTEMPLATE_SPECIALIZATION, saveTemplateSpecialization,
                  &data );
    PCHWriteCVIndex( terminator );
    CarveWalkAllFree( carveTEMPLATE_INFO, markFreeTemplateInfo );
    CarveWalkAll( carveTEMPLATE_INFO, saveTemplateInfo, &data );
    PCHWriteCVIndex( terminator );
    return( PCHCB_OK );
}

pch_status PCHReadTemplates( void )
{
    cv_index i;
    unsigned j;
    size_t arg_names_size;
    size_t type_list_size;
    size_t defarg_list_size;
    char **arg_names;
    TYPE *type_list;
    REWRITE **defarg_list;
    MEMBER_INST *mi;
    CLASS_INST *ci;
    FN_TEMPLATE *ftd;
    TEMPLATE_SPECIALIZATION *ts;
    TEMPLATE_SPECIALIZATION *tprimary;
    TEMPLATE_INFO *ti;
    REWRITE *memb_defn;
    char **memb_arg_names;
    auto void *member_buff[2];
    auto cvinit_t data;

    PCHRead( &templateData.max_depth, sizeof( templateData.max_depth ) );
    PCHRead( &allClassTemplates, sizeof( allClassTemplates ) );
    allClassTemplates = TemplateClassInfoMapIndex( allClassTemplates );
    PCHRead( &allFunctionTemplates, sizeof( allFunctionTemplates ) );
    allFunctionTemplates = TemplateFunctionInfoMapIndex( allFunctionTemplates );
    CarveInitStart( carveMEMBER_INST, &data );
    for(;;) {
        i = PCHReadCVIndex();
        if( i == CARVE_NULL_INDEX ) break;
        mi = CarveInitElement( &data, i );
        PCHRead( mi, sizeof( *mi ) );
        mi->next = CarveMapIndex( carveMEMBER_INST, mi->next );
        mi->scope = ScopeMapIndex( mi->scope );
        mi->class_parm_scope = ScopeMapIndex( mi->class_parm_scope );
        mi->class_parm_enclosing = ScopeMapIndex( mi->class_parm_enclosing );
        if( mi->dinfo != NULL ) {
            mi->dinfo = PCHReadDeclInfo();
        }
    }
    CarveInitStart( carveCLASS_INST, &data );
    for(;;) {
        i = PCHReadCVIndex();
        if( i == CARVE_NULL_INDEX ) break;
        ci = CarveInitElement( &data, i );
        PCHRead( ci, sizeof( *ci ) );
        ci->next = CarveMapIndex( carveCLASS_INST, ci->next );
        ci->scope = ScopeMapIndex( ci->scope );
        ci->inlines_scope = ScopeMapIndex( ci->inlines_scope );
        ci->inlines_enclosing = ScopeMapIndex( ci->inlines_enclosing );
        ci->locn.src_file = SrcFileMapIndex( ci->locn.src_file );
        if( ci->inlines != NULL ) {
            ci->inlines = PCHReadDeclInfo();
        }
    }
    CarveInitStart( carveFN_TEMPLATE, &data );
    for(;;) {
        i = PCHReadCVIndex();
        if( i == CARVE_NULL_INDEX ) break;
        ftd = CarveInitElement( &data, i );
        PCHRead( ftd, sizeof( *ftd ) );
        ftd->next = CarveMapIndex( carveFN_TEMPLATE, ftd->next );
        ftd->sym = SymbolMapIndex( ftd->sym );
        ftd->defn = RewriteMapIndex( ftd->defn );
    }
    CarveInitStart( carveTEMPLATE_SPECIALIZATION, &data );
    for(;;) {
        i = PCHReadCVIndex();
        if( i == CARVE_NULL_INDEX ) break;
        ts = CarveInitElement( &data, i );
        PCHRead( ts, sizeof( *ts ) );
        ts->next = CarveMapIndex( carveTEMPLATE_SPECIALIZATION, ts->next );
        ts->tinfo = CarveMapIndex( carveTEMPLATE_INFO, ts->tinfo );
        ts->locn.src_file = SrcFileMapIndex( ts->locn.src_file );
        ts->decl_scope = ScopeMapIndex( ts->decl_scope );
        ts->defn = RewriteMapIndex( ts->defn );
        ts->instantiations = CarveMapIndex( carveCLASS_INST,
                                            ts->instantiations );
        ts->member_defns = NULL;
        ts->spec_args = PTreeMapIndex( ts->spec_args );
        arg_names_size = ts->num_args * sizeof( char * );
        arg_names = CPermAlloc( arg_names_size );
        ts->arg_names = arg_names;
        type_list_size = ts->num_args * sizeof( TYPE );
        type_list = CPermAlloc( type_list_size );
        ts->type_list = type_list;
        PCHRead( arg_names, arg_names_size );
        PCHRead( type_list, type_list_size );
        for( j = 0; j < ts->num_args; ++j ) {
            arg_names[j] = NameMapIndex( arg_names[j] );
            type_list[j] = TypeMapIndex( type_list[j] );
        }
        for(;;) {
            PCHRead( member_buff, sizeof( member_buff ) );
            if( member_buff[0] == NULL ) break;
            memb_defn = RewriteMapIndex( member_buff[0] );
            if( member_buff[1] != NULL ) {
                memb_arg_names = CPermAlloc( arg_names_size );
                member_buff[1] = memb_arg_names;
                PCHRead( memb_arg_names, arg_names_size );
                for( j = 0; j < ts->num_args; ++j ) {
                    memb_arg_names[j] = NameMapIndex( memb_arg_names[j] );
                }
            } else {
                memb_arg_names = arg_names;
            }
            addMemberEntry( ts, memb_defn, memb_arg_names );
        }
        if( ts->ordering != NULL ) {
            j = 16 * ( ( ( (unsigned) ts->ordering ) - 2 ) / 128 + 1 );
            ts->ordering = CMemAlloc( j );
            PCHRead( ts->ordering, j );
        }
    }
    CarveInitStart( carveTEMPLATE_INFO, &data );
    for(;;) {
        i = PCHReadCVIndex();
        if( i == CARVE_NULL_INDEX ) break;
        ti = CarveInitElement( &data, i );
        PCHRead( ti, sizeof( *ti ) );
        ti->next = CarveMapIndex( carveTEMPLATE_INFO, ti->next );
        ti->specializations = CarveMapIndex( carveTEMPLATE_SPECIALIZATION,
                                             ti->specializations );
        ti->unbound_type = TypeMapIndex( ti->unbound_type );
        ti->sym = SymbolMapIndex( ti->sym );
        tprimary = RingFirst( ti->specializations );
        defarg_list_size = tprimary->num_args * sizeof( REWRITE * );
        defarg_list = CPermAlloc( defarg_list_size );
        ti->defarg_list = defarg_list;
        PCHRead( defarg_list, defarg_list_size );
        for( j = 0; j < tprimary->num_args; ++j ) {
            defarg_list[j] = RewriteMapIndex( defarg_list[j] );
        }
    }
    return( PCHCB_OK );
}

pch_status PCHInitTemplates( boolean writing )
{
    cv_index n;

    if( writing ) {
        n = CarveLastValidIndex( carveCLASS_INST );
        PCHWriteCVIndex( n );
        n = CarveLastValidIndex( carveFN_TEMPLATE );
        PCHWriteCVIndex( n );
        n = CarveLastValidIndex( carveTEMPLATE_MEMBER );
        PCHWriteCVIndex( n );
        n = CarveLastValidIndex( carveTEMPLATE_SPECIALIZATION );
        PCHWriteCVIndex( n );
        n = CarveLastValidIndex( carveTEMPLATE_INFO );
        PCHWriteCVIndex( n );
    } else {
        carveCLASS_INST = CarveRestart( carveCLASS_INST );
        n = PCHReadCVIndex();
        CarveMapOptimize( carveCLASS_INST, n );
        carveFN_TEMPLATE = CarveRestart( carveFN_TEMPLATE );
        n = PCHReadCVIndex();
        CarveMapOptimize( carveFN_TEMPLATE, n );
        carveTEMPLATE_MEMBER = CarveRestart( carveTEMPLATE_MEMBER );
        n = PCHReadCVIndex();
        CarveMapOptimize( carveTEMPLATE_MEMBER, n );
        carveTEMPLATE_SPECIALIZATION = CarveRestart( carveTEMPLATE_SPECIALIZATION );
        n = PCHReadCVIndex();
        CarveMapOptimize( carveTEMPLATE_SPECIALIZATION, n );
        carveTEMPLATE_INFO = CarveRestart( carveTEMPLATE_INFO );
        n = PCHReadCVIndex();
        CarveMapOptimize( carveTEMPLATE_INFO, n );
    }
    return( PCHCB_OK );
}

pch_status PCHFiniTemplates( boolean writing )
{
    if( ! writing ) {
        CarveMapUnoptimize( carveCLASS_INST );
        CarveMapUnoptimize( carveFN_TEMPLATE );
        CarveMapUnoptimize( carveTEMPLATE_MEMBER );
        CarveMapUnoptimize( carveTEMPLATE_SPECIALIZATION );
        CarveMapUnoptimize( carveTEMPLATE_INFO );
    }
    return( PCHCB_OK );
}
