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


// %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
// %     Copyright (C) 1992, by WATCOM International Inc.  All rights    %
// %     reserved.  No part of this software may be reproduced or        %
// %     used in any form or by any means - graphic, electronic or       %
// %     mechanical, including photocopying, recording, taping or        %
// %     information storage and retrieval systems - except with the     %
// %     written permission of WATCOM International Inc.                 %
// %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
//
//  Modified    By              Reason
//  ========    ==              ======
//  92/01/30    Steve McDowell  Initial implementation.
//  92/09/08    Greg Bentz      Cleanup.
//  93/07/29    Greg Bentz      Change ostream::op<<(streambuf &) to
//                              ostream::op<<( streambuf * )
//  93/10/26    Raymond Tang    Split into separate files.
//  94/04/06    Greg Bentz      combine header files

#ifdef __SW_FH
#include "iost.h"
#else
#include "variety.h"
#include <iostream.h>
#endif
#include "osthdr.h"

void __AddPrefix( char iszero, char *buffer, int &size, int base,
/********************************************************************/
    long format_flags ) {
// Add a prefix to an output integer representing the base used.
// Add 0 for octal numbers, except for zero.
// Add 0x or 0X for hex numbers.
// Add nothing for decimal numbers.

    if( format_flags & ios::showbase ) {
        if( base == 8 ) {
            if( !iszero ) {
                buffer[size++] = '0';
            }
        } else if( base == 16 ) {
            buffer[size++] = '0';
            buffer[size++] = (char)((format_flags & ios::uppercase) ? 'X' : 'x');
        }
    }
}
