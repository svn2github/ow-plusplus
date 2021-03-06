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

#ifdef __SW_FH
#include "iost.h"
#else
#include "variety.h"
#include <errno.h>
#include <iostream>
#endif
#include "exitwmsg.h"
#include "iofhdr.h"


static void _no_support_loaded() {
    __fatal_runtime_error( "C++ floating-point support not loaded", 1 );
}

_WPRTLINK _type_EFG_cnvs2d __EFG_cnvs2d
       = (_type_EFG_cnvs2d)_no_support_loaded;
_WPRTLINK _type_EFG_cnvd2f __EFG_cnvd2f
       = (_type_EFG_cnvd2f)_no_support_loaded;
_WPRTLINK _type_EFG_LDcvt  __EFG_LDcvt
       = (_type_EFG_LDcvt)_no_support_loaded;
_WPRTLINK _type_EFG_fcvt   __EFG_fcvt
       = (_type_EFG_fcvt)_no_support_loaded;
#ifdef _LONG_DOUBLE_
_WPRTLINK _type_EFG__FDLD  __EFG__FDLD
       = (_type_EFG__FDLD)_no_support_loaded;
#endif
