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


#ifndef _TEMPLATE_H
#define _TEMPLATE_H

#define TEMPLATE_MAX_DEPTH              100

typedef struct template_data TEMPLATE_DATA;
struct template_data {
    TEMPLATE_DATA       *next;          // (stack)
    DECL_INFO           *args;          // template arguments
    unsigned            nr_args;        // number of template arguments
    PTREE               spec_args;      // template specialization arguments
    TYPE                unbound_type;   // unbound class type
    SCOPE               decl_scope;     // template decl scope
    REWRITE             *defn;          // class template definition
    REWRITE             *member_defn;   // class template member definition
    char                *template_name; // name of the template
    SCOPE               template_scope; // conaining scope of the template
    TOKEN_LOCN          locn;           // location of class template id
    error_state_t       errors;         // error state at beginning
    unsigned            all_generic : 1;// all args are generic types
    unsigned            defn_found : 1; // a template defn has been found
    unsigned            member_found :1;// a class template member has been found
    unsigned            defn_added : 1; // class template defn has just been added
};

// these structures are private to TEMPLATE.C but they are exposed
// for debug dump routines

typedef struct member_inst MEMBER_INST; // template member instantiation
PCH_struct member_inst {
    MEMBER_INST         *next;          // (ring)
    DECL_INFO           *dinfo;         // member definition
    SCOPE               scope;
    SCOPE               class_parm_scope;
    SCOPE               class_parm_enclosing;
    unsigned            is_inline : 1;
};

typedef struct class_inst CLASS_INST;   // class template instantiation
PCH_struct class_inst {
    CLASS_INST          *next;          // (ring)
    TYPE                unbound_type;   // unbound class type
    SCOPE               scope;          // scope containing instantiation
    SCOPE               inlines_scope;  // scope for instantiating inline functions
    SCOPE               inlines_enclosing; // scope for instantiating inline functions
    DECL_INFO           *inlines;       // ring of pending inline functions
    MEMBER_INST         *members;       // ring of pending member functions
    TOKEN_LOCN          locn;           // location of first instantiation
    unsigned            must_process :1;// must be post-processed
    unsigned            dont_process :1;// should not be post-processed
    unsigned            processed : 1;  // has been post-processed
    unsigned            specific : 1;   // specific instantiation provided
    unsigned            locn_set : 1;   // locn field has been set
    unsigned            free : 1;       // used for precompiled headers
};

typedef struct template_member TEMPLATE_MEMBER; // class template member
PCH_struct template_member {
    TEMPLATE_MEMBER     *next;          // (ring)
    SCOPE               scope;          // scope for member definition
    REWRITE             *defn;          // member definition
    char                **arg_names;    // argument names
};

PCH_struct template_specialization {
    TEMPLATE_SPECIALIZATION *next;      // (ring)
    TEMPLATE_INFO       *tinfo;         // parent template info
    CLASS_INST          *instantiations;// list of current instantiations
    REWRITE             *defn;          // template def'n (may be NULL)
    TEMPLATE_MEMBER     *member_defns;  // external member defns
    SCOPE               decl_scope;     // template declaration scope
    TOKEN_LOCN          locn;           // location of class template id
    unsigned            num_args;       // number of template arguments
    TYPE                *type_list;     // template argument types
    char                **arg_names;    // argument names
    PTREE               spec_args;      // template specialization arguments
    unsigned char       *ordering;      // "at least as specialized as" bitmask
    unsigned            corrupted : 1;  // template def'n contained errors
    unsigned            defn_found : 1; // a template defn has been found
};

typedef struct unbound_template UNBOUND_TEMPLATE; // unbound template class
PCH_struct unbound_template {
    UNBOUND_TEMPLATE    *next;          // (ring)
    TYPE                unbound_type;   // unbound class type
    unsigned int        hash;           // hash code
};

PCH_struct template_info {
    TEMPLATE_INFO       *next;          // (ring)
    UNBOUND_TEMPLATE    *unbound_templates; // unbound template classes
    TEMPLATE_SPECIALIZATION *specializations;// template specializations
    REWRITE             **defarg_list;  // default arguments
    SYMBOL              sym;            // template symbol
    unsigned            nr_specs;       // number of template specializations (including the primary template)
    unsigned            free : 1;       // used for precompiled headers
};

typedef struct fn_template_inst FN_TEMPLATE_INST; // function template instantiation
PCH_struct fn_template_inst {
    FN_TEMPLATE_INST    *next;          // (ring)
    SYMBOL              bound_sym;      // bound template function symbol
    TOKEN_LOCN          locn;           // instantiation location
    SCOPE               parm_scope;     // template parameter scope
    SCOPE               inst_scope;     // template instantiation scope
    unsigned            processed : 1;  // already processed instantiation
};

typedef struct fn_template FN_TEMPLATE; // function template
PCH_struct fn_template {
    FN_TEMPLATE         *next;          // (ring)
    FN_TEMPLATE_INST    *instantiations;// list of instantiations
    SYMBOL              sym;            // template function
    SCOPE               decl_scope;     // template declaration scope
    REWRITE             *defn;          // always non-NULL
    unsigned            has_defn : 1;   // declaration or definition?
    unsigned            free : 1;       // used for precompiled headers
};

typedef enum tc_directive {
    TCD_EXTERN          = 0x01,         // compile no member fns in this module
    TCD_INSTANTIATE     = 0x02,         // compile all member fns in this module
    TCD_NULL            = 0x00
} tc_directive;

typedef enum tc_fn_control {
    TCF_GEN_FUNCTION    = 0x01,
    TCF_NULL            = 0x00
} tc_fn_control;

extern boolean IsTemplateInstantiationActive( void );
extern void TemplateDeclInit( TEMPLATE_DATA * );
extern void TemplateDeclAddArgument( DECL_INFO *new_dinfo );
extern void TemplateDeclFini( void );
extern void TemplateFunctionCheck( SYMBOL, DECL_INFO * );
extern void TemplateFunctionDeclaration( SYMBOL, boolean is_defn );
extern void TemplateFunctionAttachDefn( DECL_INFO * );
extern SYMBOL TemplateFunctionGenerate( SYMBOL, arg_list *, PTREE, TOKEN_LOCN * );
extern void TemplateClassDeclaration( PTREE, SCOPE, char * );
extern boolean TemplateClassDefinition( PTREE, SCOPE, char * );
extern TYPE TemplateClassReference( PTREE, PTREE );
extern void TemplateHandleClassMember( DECL_INFO * );
extern void TemplateMemberAttachDefn( DECL_INFO * );
extern void TemplateProcessInstantiations( void );
extern boolean TemplateMemberCanBeIgnored( void );
extern boolean TemplateVerifyDecl( SYMBOL );
extern void TemplateSpecificDefnStart( PTREE, TYPE );
extern void TemplateSpecificDefnEnd( void );
extern void TemplateSpecializationDefn( TYPE );
extern SCOPE TemplateClassInstScope( TYPE );
extern SCOPE TemplateClassParmScope( TYPE );
extern boolean TemplateParmEqual( SYMBOL, SYMBOL );
extern SYMBOL TemplateFunctionTranslate( SYMBOL, boolean, SCOPE * );
extern tc_fn_control TemplateFunctionControl( void );
extern TYPE TemplateUnboundInstantiate( TYPE, arg_list *, TOKEN_LOCN * );
extern SYMBOL ClassTemplateLookup( SCOPE scope, char * );
extern SYMBOL TemplateSymFromClass( TYPE );
extern void TemplateSetDepth( unsigned );
extern boolean TemplateUnboundSame( TYPE, TYPE );
extern void TemplateClassDirective( TYPE, TOKEN_LOCN *, tc_directive );
extern void TemplateUsingDecl( SYMBOL, TOKEN_LOCN * );

extern TEMPLATE_INFO *TemplateClassInfoGetIndex( TEMPLATE_INFO * );
extern TEMPLATE_INFO *TemplateClassInfoMapIndex( TEMPLATE_INFO * );
extern FN_TEMPLATE *TemplateFunctionInfoGetIndex( FN_TEMPLATE * );
extern FN_TEMPLATE *TemplateFunctionInfoMapIndex( FN_TEMPLATE * );
typedef int  (*AInstSCOPE)( SCOPE scope );
extern int WalkTemplateInst( SYMBOL sym, AInstSCOPE fscope  );

#endif
