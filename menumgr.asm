***********************************************************************************
*
*            Copyright Apple Computer, Inc. 1986-92
*	  All Rights Reserved
*	 Written by Dan Oliver
*
*               ***	C O N F I D E N T I	A L ***
*
*
*	Change History:
*
* 21 June 1988	Harry Yee
*	Converted version 2.1 of the menu manager that went on
*	System Disk 3.2 to MAX.
*
*
* 27 June 1988	Steven Glass
*
* Changed all accesses to popXbytes.  All but two loaded y-reg with zero before
* branching so we changed these to access the new pop routines that assumed
* no error.  (these are now called popXbytes.)
*
* The error accesses still branch to the routines that assume y-reg has error
* code.  These have been renamed EpopXbytes.
*
* 30 June 1988	Steven Glass
*
* When calling the creamed routine we did a jsr to Long_Call instead of a JSL.
*
* 10 Aug 88	Dan Oliver
*
* Free allocated data area on shutdown.
*
* 02 Oct 88	Steven Glass
*
* Changed the data structure for Menu Items.  They now have two bytes for
* the item flag.
*
* Added the outline and shadow bits to the item flag
*
* Funnelled all calls to set text face to a common routine.  This saved code
* and lets me futz the text face bits.
*
* Changed parse routines so that they set check mark and flag separately instead
* of both at once.
*
*
* 14 Oct 88	Steven Glass
*
* Shutdown checks to see if it's active first before doing anything.
*
* 17 Oct 88	Harry Yee
*
* Put in code for scrollable menus. Modified Size_menu, took out code that checked to see
* if menuheight was greater than 1988.  (Does that mean 198?? --DAL Jan-91)
*
* 18 Oct 88	Harry Yee	(released in Proto 03 ROM)
* Initialized FirstItem field for custom menus to be 1. In DeleteMItem needed to decrement
* NumOfItems each time an item gets deleted.
*
* 19 Oct 88	Harry Yee
* Now using PortRect instead of BoundsRect to check if menu needs to be adjusted or not.
*
* 20 Oct 88	Harry Yee
* Not using the fields FirstItem and NumOfItems in the menu record anymore. Making space
* on direct page to hold these values. FirstItem and NumOfItems were 1 byte values,
* since I don't need FirstItem anymore, I am making NumOfItems 1 word long. NumOfItems
* will hold the total number of items in the menu. Fixed some problems dealing with
* custom menus. Made sure that a menu is not going to be scrollable if there are less
* than 3 items.
*
* 25 Oct 88	Harry Yee
* Put in code for PopupMenuSelect and tracking the pop-up menu (TrackMenu2).
* Made change to the routine pull_down during the savescreen process. The first line of
* the menu was not being cached, this was ok for regular menus, since the menu bar was
* there, but for pop-ups this was a problem, so the first line of the menu is cached for
* all regular and pop-up menus.
*
* 28 Oct 88 (morning) Harry Yee
* Changed the makefile to include the popupproc.asm code.  Added a new call DrawPopup $3D0F
* this is called by the popupproc do_draw and do_track to draw the pop-up box and drop
* shadow. A flag is also passed to this call which tells me whether to draw the name of the
* currently selected item in the pop-up box or not.
*
* 28 Oct 88 (afternoon) Harry Yee
* In routine DrawPopup set clip region to the pop-box (which is inset just a bit to account
* for the border) before drawing the item string.
*
* 31 Oct 88	Harry Yee
* Fixed problem when the pop-up rect is at bottom of the window.
*
* 02 Nov 88	Harry Yee
* Fixed more problems when the pop-up rect gets close to the bottom of the screen and the
* user trys to bring up the pop-up menu.
*
* 08 Nov 88	Harry Yee
*
* In the Oct 25 change that enabled caching of the first line of the menu this caused some
* problems in routine AllocateCache. Routine was allocating one line too less since it was
* allocating memory on the old assumption that the first line was not cached. I now increment
* the height by one so that everyone is happy (BRC #38017).
*
* 10 Nov 88	Harry Yee
*
* We now define the first two bits of the item flag. 00 = ptr, 01 = handle, 10 = resource ID.
* The first two bits of the menures byte is now also defined: 00 = ptr, 01 = handle, 10 = res ID
*
* Initial coding of NewMenu2 call ($3E0F). Don't know if it works though.
* Defined the format of menu, item and menubar resources.
*
* 11 Nov 88	Harry Yee
*
* NewMenu2 now works!! Hurrah! Now start on adding calls InsertMItem2, SetMenuTitle2,
* SetMItem2, and SetMItemName2.
*
* 15 Nov 88	Harry Yee
*
* Pop-up menus can now be resources. Hurrah! All the calls InsertMItem2, SetMenuTitle2,
* SetMItem2, and SetMItemName2 are now complete. Still need NewMenuBar2 call.
*
* 18 Nov 88	Harry Yee
*
* NewMenuBar2 has now been implemented.
*
* 23 Nov 88	Harry Yee
*
* The routines DrawPopup and PopUpMenuSelect were not unlocking the handle to the menu record
* upon exit. I now unlocke before exiting.
* DrawPopUp has been modified so that it now right justifies the result if the
* FRightJustifyResult bit was set in whatToDoFlag.
*
* I now use PPToPort to draw the up/down arrows instead of DrawIcon, so I now no longer depend
* on QDAux to be started. (BRC #37822)
*
* 29 Nov 88	Harry Yee
*
* Change PopUpMenuSelect so that the initial value passed is the item's ID instead of an offset
* into the item list (BRC #38519)
*
* In PopUpMenuSelect, if an invalid item ID is passed for the initial then an error is now
* returned (BRC #38521, #38520)
*
* Fixed problem in routine adjustTop. (WorkSheet #BCORMR518)
*
* 01 Dec 88	Harry Yee
*
* Empty menus are now valid. (BRC #38523) The routine parse was changed to check if the first
* character in the first item is a title character, if it is then I assume the menu is empty.
* (since this char. is not a valid item character and it equals the title char. then this
* signifies a termination char.)  InsertMItem was also modified to support empty menus. It always
* checked to make sure that an item could be found for the insertAfter id passed to it. Since
* the menu was empty none could be found and we exited. I now check if the menu is empty first.
*
* 02 Dec 88	Harry Yee
*
* Change the way I handle a bad initial value passed to the pop-up. If the item ID is invalid then
* the item that appears under the pop-up defaults to the first item in the menu. (BRC #38521,
* #38520)
*
* PopUpMenuSelect has been modified to work for empty pop-up menus.
*
* 05 Dec 88	Harry Yee
*
* Change GetMItem back to the way it was before (just return what is in ItemName). I used to check
* the itemFlag, and if it was a resource I would load the resource, deref the handle and
* return the ptr to the string. If it's a resource I now just return the ID and let the
* app worry about what to do with it.
*
* DeleteMItem wasn't working right for empty menus. Fixed in routine Getiptr3.
*
* 08 Dec 88	Harry Yee
*
* Putting in variable speed scroller. First 5 pixels of each up/down arrow will scroll at about
* .3 seconds per item.
*
* Fixed BRC #37987. FixMenuBar now computes the width of the apple logo correctly if it gets
* zeroed by calling SetMTitleWidth.
*
* Changed the default menu bar template so that the first menu in the menubar is indented
* by 10 pixels. This is so the AppleShare "busy" arrows have somewhere to go.
*
* 09 Dec 88	Harry Yee
*
* SetMItemStyle doesn't handle shadow and outline styles correctly. Fixed (BRC #39324)
*
* Fixed problem with drawing up/down arrows in 320 mode. Was using the 640
* boundsrect and locinfo instead of the 320 one. This has been fixed.
*
* 12 Dec 88	Harry Yee
*
* Fix GetItem to return ITEM_NOT_FOUND error if item not found. (for Andy Stadler)
* Changed the pen mode to notBIC when calling PPToPort to draw up/down arrows, so these
* arrows show up correctly when the menu is in color.
*
* 15 Dec 88	Harry Yee
*
* Put in code for user to create a second type of pop-up (with white space). PopUpMenuSelect
* had to be changed. Another input param has been added, a flag parameter.
*
* Popups now handle command key equivalents (all handled in popupproc.asm).
*
* Drop shadow for menus (popups and regular menus) were not being drawn in the color that
* the app had specified as the outline color if the _SpecialRect call completed. This was
* because the setoutline routine was called only when SpecialRect failed.
*
* 22 Dec 88
*
* Fixed some problems with creating type 2 pop-ups. When 1st item was selected and pop-up
* was down near bottom of screen we had problems.
*
* Defined another bit in the menu flag. Bit 8 is defined as the ALWAYSCALLMCHOOSE flag.
* Change put in for Andy Stadler for doing tear off menus. When set the custom menu def proc
* mChoose gets called even when the mouse is not in the menu rectangle. (It sends off the
* last draw message,if there is one, before calling mChoose).
*
* 03 Jan 89	Dan O.
*
* Choose_item did a tdc ora #rect instead of tdc clc adc #rect.  This worked as long as the
* direct page had bits 2-3 clear.
*
* 04 Jan 89	Harry Yee
*
* NewMenuBar now checks what mode we're in before setting the default starting position of the
* first menu title. Titles start at 10 pixels in for 640 mode and 5 pixels in, for 320 mode.
*
* Fixed bug in the type 2 pop-up. The pop-up was not being calculated correctly when the top had
* to be adjusted but not the bottom and the window the pop-up was in was off the screen.
*
* 09 Jan 89	Harry Yee
*
* Keyboard equivalents and check marks will appear in plain text regardless of the style
* of the menu item. BRC #39042, #39444.
*
* 18 Jan 89	Harry Yee
*
* Added two new calls HideMenuBar and ShowMenuBar. Both calls work only on the system menu bar.
* HideMenuBar hides the menu bar by subtracting the menu bar's rect from the desktop, ShowMenuBar
* does the exact opposite, the rect is added to the desktop. This fixes the bug where you
* change the font to a larger one then back to a smaller one.
*
* Changed routine Cache. If a regular pop-up menu extended beyond the top of the screen this
* routine doesn't expect any values to be negative. Therefore if <menurect+y1 is negative
* we use zero instead.
*
* When a large font was used for drawing menus and the menu had command-key equivalents, the width
* of the menu was not being calculated correctly. This was because in size_menu the values added
* to the menu width for an item having a command-key equiv. and a check mark was hard coded. This
* has been changed. The direct page variable Menu_type was never being used previously, I now use
* it to store the width of the widest item in the current font strike. It has been renamed to
* text_width. This value is calculated in MenuNewRes where GetFontInfo is being called.
* BRC #37985.
*
* 20 Jan 89	Harry Yee
*
* Menus in an info bar now work correctly. Changed the way I calculate if a menu needs to scroll
* or not. Before I was just using the PortRect to determine if the menu needed to be resized, now
* I use the intersection between the VisRgn, ClipRgn, and PortRect. BRC #40477.
*
* 27 Jan 89	Harry Yee
*
* Change the way empty menus work. To create an empty menu you now have to terminate the menu with
* either $00 (null character) or $0D (return). The original scheme was to terminate the menu with
* the title character but this caused some problems with an app. (Notes'n'file). BRC #39489.
*
* 29 Jan 89	Harry Yee
*
* Changed DrawPopUp. This routine first clears the current selection in the pop-up rect before
* checking if the itemnum is valid or not. If the selection being made is not valid there is no
* selection in the pop-up's rect. After deleting an item, I now check if the menu is a pop-up
* menu, if it is I check if the item just deleted was the currently selected item, if it is
* I then call SetCtlValue with the value of zero which then clears the selection just deleted
* in the pop-up's rect. BRC #39760.
*
* 30 Jan 89	Harry Yee
*
* Changed HiliteMenu to work with pop-ups.
*
* When caching menus I now switch to the menu manager's pixel map bank instead of going directly to
* bank $E1. This now allows shadowing to be enabled. (J. Mensch's idea)
*
* 01 Feb 89	Harry Yee
*
* Changed PopUpMenuSelect so that the menu's flag is saved upon entering routine and restored upon
* exit. I do this because the flag may need to be altered, the M_CACHE bit needs to be cleared
* and the M_POPUP bit needs to be set for everything to work correctly. (BRC #41040, 41041)
*
* 06 Feb 89	Harry Yee
*
* Changed Draw_Menu routine to set Text Mode to modeForeCopy. This was needed to make menus in
* windows work correctly. When menus are drawn in the Menu Manager's port the text mode is set up
* correctly when the port is first initialized, but for menus in windows this is not the case.
* (BRC #40708)
*
* 07 Feb 89 	Harry Yee
*
* Changed DeleteMenu, to first release the cache for the menu being deleted and also freeing
* all the caches once the menu is deleted since the position of the menus may now be out of
* order. InsertMenu now also free's all the caches for this same reason.
*
* GetColor now checks if the ctlColor field is zero or not, if it is then the default color table
* is used. SetBarColors also checks this field and if it's zero then it doesn't do anything.
*
* 22 Feb 89	Harry Yee
*
* Fix some problems with FixMenuBar and HideMenuBar. It was doing far too much making it very
* slow if there were windows open. RefreshDesktop is no longer being called for ShowMenuBar and
* for HideMenuBar the whole screen is no longer being refreshed, only the rect for the menubar
* being hidden. Also initPalette is called after the menu is drawn.
*
* 24 Feb 89	Harry Yee
*
* I used to use MaxWidth to determine how much to add to the width of a menu item if it had
* a check mark and a command key equivalent. This caused problems for AppleWorks GS which
* installed their own font with one very very wide char. I now use the character 'W' out of
* currently installed font strike as my MaxWidth char. BRC #41164, 41415
*
* A menu in a window would have problems when, 1) the window was off the left side of the
* screen and 2) the menu title was visible but the width of the menu was greater than
* the right side of the window minus the left side of the screen. Fixed. BRC #41440
*
* 15 Mar 89	Harry Yee
*
* Removing DrawPopUp call. This makes the pop-up defproc easier to maintain.
*
* 27 Mar 89	Harry Yee
*
* I now restore original foreground color in routine draw_title.
*
* 30 Mar 89	Mensch/Yee
*
* Changed GetColor to make it work with pop-up color tables that reference handle/resources.
*
* We now save and restore all grafport shit in PopUpMenuSelect (two new routines PushPortData
* and PopPortData).
*
* 04 Apr 89	Yee
*
* Make PopUpMenuSelect scrambler proof. The menu bar's handle was not getting locked
* when it should. Fixed.
*
* 06 Apr 89	Yee
*
* When drawing a popup or regular menu title, the text mode is set to fore copy. I now
* save and restore the original text mode once I am done drawing the title.
*
* 19 Apr 89	Mensch/Yee
*
* Fixed bug in menu caching that cause a bad left mask to be used for re-blitting a chached
* menu. Was using the <X> register to save the screen mode, this was being trashed by the
* routine before it was used again. We now use <Y> save screen mode. BRC#36702
*
* Also, Tidbits (the fine routine to reblit the corners) now does the top 4 lines of a menu
* instead of 3 ( the drop shadow was 1 pixel lower than tidbits saved)
*
* 24 Apr 89	Glass/Mensch/Yee (on the Eve of freezing the ROM)
*
* In routine Draw_Title we now check whether we're in the menu manager's port before
* deciding not to save the fore color and text mode we just changed. This fixes a problem
* in Word Perfect that was depending on the menu manager's port to be set up correctly.
*
* 15 May 89	Yee
*
* Memory was being trashed when a menu extended below the screen. In routine Cache I now
* check to make sure y2 is never greater than 200. This is so the height of the menu
* never extends past the bottom of the screen and we'll restore the menu just fine.
* BRC #49085.
*
* The routines DrawDwnArrow/DrawUpArrow needed RECT to be setup. There was an instance
* that RECT was not being setup. This caused garbage to be drawn on the screen in those
* instances. Now I make sure RECT is setup.
*
* 19 May 89	Yee	(for system disk d23)
*
* Calling HiliteMenu with an ID of 0 or $FFFF is not valid. ToolBox Reference manual
* says that these IDs mean first and last menu in menubar respectively.
*
* 23 May 89	Yee	(for system disk d24)
*
* Take out above fix because some apps were actually creating menus with an ID
* of zero.
*
* 25 May 89	Yee
*
* Fix routine freecache. This routine never did dispose of the menu cache correctly.
*
* When this routine was fixed it uncovered a bug in routine pullup, which only affected
* a menu if it was scrollable and only if someone had scrolled it. I was disposing of
* the cache (i.e. calling freecache) before it was getting uncached. Therefore when
* we tried to restore what was behind the menu the cache was already gone.
*
* 07 Sep 89	Yee
*
* Fix bug in NewMenuBar2. The resource ID is not being copied into a temporary location
* correctly. Only the low word is being stored to. This causes problems when we use
* this temp location to release the menubar resource. Either the menubar resource is
* not released at all (whenever high word of resource ID is zero, or the call crashes
* whenever the high word of resource ID is non-zero.)
*
* 05 Jan 90	Yee
*
* Added icon support for menu items. Added calls SetItemIcon and GetItemIcon.
*
* 29 Mar 90	Yee
* Fix bug in DeleteMenu. The handle being removed was not being unlocked after
* it was removed.
*
* 05 Apr 90
* Change the way the menu item icons are drawn. I now use DrawIcon instead
* of PPToPort to draw the icon. To use icons in menu items, the menu mgr
* now requires that QDAux be started. Also the icon structure used to look
* like a locInfo record, it's now an icon structure as defined by rIcon.
*
* 10 May 90	Yee
* Fix bug in routine DrawItemIcon.  I now make sure the item has an itemstruct assoc.
* with it before trying to get the itemstruct.
*
* 05 Jul 90 	Yee
* Added the following calls: SetItemStruct ($490F), GetItemStruct ($4A0F),
* RemoveItemStruct ($4B0F), GetItemFlag2 ($4C0F), SetItemFlag2 ($4D0F)
*
* 17-Sep-90	Dave Lyons
*
* Removed dependency on all.macros.
*
* Note--Call $4E0F, GetItemWidth (Harry's?)
*
* 19-Sep-90	Dave Lyons
*
* Added GetMItemBlink call ($4F0F).  Version is $8303.
* Adding MenuGlobal bit to make MenuSelect call InitCursor.
* (The InitCursor thing doesn't work too well yet--it flickers the cursor.)
*
* 27-Sep-90	Dave Lyons
*
* Now calls Get640Colors (QD) to get a pointer to the color_patt table
* instead of hard-coding our own.
*
* Put all.macros back.
*
* 7-Jan-91	Dave Lyons
*
* Moved the G_INITCURSOR check to where it really should be (when we decide
* the mouse was actually clicked in the menu bar).
*
* When blinking a menu item, now I call WaitUntil to wait at least MinMenuBlinkTime
* since the last blink.
*
* 9..10-Jan-91	Dave Lyons
*
* Added new call InsertPathMItems for use by Finder, Standard File, Installer.
*
* 11-Jan-91	Dave Lyons
*
* InsertPathMItems: Added InsertAfter parameter, defined bit 2 of Flags, and
* reordered parameters.  Cool.
*
* 12-Jan-91	Dave Lyons
*
* Changes to InsertPathMItems (see comments there).
*
* 16-Jan-91	Dave Lyons
*
* Fixed up some comments.  Fixed the bug that makes pop-up menus not
* always hilite menu items (sometimes it just inverts the icon).
* The problem was popPortData stuffing values into a grafport while
* fastPort was on.  Added a SetPort after the port stuffing to make
* QD realize we dicked around with the port.
*
* Made a few $E10000 into macro calls.
*
* 22-Jan-91	Dave Lyons
*
* Fixed drawing an icon in a menu so that it always draws at an even horizontal
* location.
*
* 5-Feb-91	Dave Lyons
*
* Fixed a bug in InsertPathMItems where I was disposing of one of the handles
* that gets passed back to the caller for later disposal.
*
* Changed name of GetOSIcon to GetSysIcon.
*
* 17-Feb-91	Dave Lyons
*
* Optimized some LDA/PHA into PEIs.
* MenuStartUp now sets the default menu item blink from BRAM $5E bits 3-4.
*
* 22-Feb-91	Dave Lyons
*
* Skip InsertPathMItems DInfo call if they pass device number $FFFF.
*
* 3-Mar-91	Dave Lyons
*
* Added MenuKey feature:  If the key is an Apple- key and is not the equivalent
* for any menu item in the passed menu, then we call SendRequest($0F01) to give
* system extensions a chance to handle the keypress.
*
* 14-Mar-91	Dave Lyons
*
* If the MenuKey SendRequest succeeds, I change the event into a null event so
* the caller doesn't try to handle it any further.
*
* 15-May-91	Dave Lyons
*
* InsertMenu now returns new error dupMenuID, $0F04, if a menu with the same id
* already exists in the current menu bar.
*
* 25-Jul-91	Dave Lyons
*
* Added restrictions to SendRequest($0F01=systemSaysMenuKey): Desk Manager must
* be active, CDA-events must be postable (for Installer when it disables use
* of DAs), and we must be dealing with the system menu bar.
*
* 26-Aug-91	Dave Lyons
*
* HideMenuBar now messes only with SCBs 2 through 9, instead of setting them all
* to the MasterSCB.
*
* SendRequest(systemSaysMenuKey) now has stop-after-one set.
*
* 18-Sep-91	Dave Lyons
*
* Made HideMenuBar mess with SCBs 0..MenuBarHeight-1, instead of just 2..9.
* This is for HyperCard IIgs compatibility.
*
* 7-Dec-91	Dave Lyons
*
* Moved G_INITCURSOR code to 'gotit', where it works without causing cursor flicker.
* InsertPathMItems:  Added a bcc @noError after first ExpandPath.  Probably dead
*   code, since this call is intended to always return a buffer-too-small error
*   and do a second ExpandPath.
* PopUpMenuSelect now calls get_ids instead of lda [<itemptr] to get the selected
*   item's id, for compatibility with custom pop-up menus.
*
* 8-Feb-92	Dave Lyons
*
* Added safety check on top coordinate of menu bar:  MenuSelect refuses to pull
* down a menu at Y>=150.  Minor optimizations.
*
* Version $0303 for 6.0 final.
*
***********************************************************************************
*
* 13-Mar-92	Dave Lyons
*
* Version $8304 for 6.0.1
*
* 4-Jun-92	Dave Lyons
*
* DeleteMItem now shrinks menu handle by 12 bytes instead of 10, so we don't
* waste two bytes every time we delete an item.
*
* 25-Mar-93	Dave Lyons
*
* In AllocateCache, we now clip the menu height to 200 for computing the size
* handle needed to save the screen.  We were overflowing the computation for
* tall pop-up menus.
*
* 1-Apr-93	Steve Stephenson
*
* Version $0304 for 6.0.1 (final)
*
***********************************************************************************
* 22-Jan-2023 Chris Parana
*
* New Apple logo images and colors
*
* 26-Jan-2023 Chris Parana
*
* Version $8305 for 6.0.x+
*
* New InitPalette to load the colors for the newer, better Apple logo. We have
* twice the colors now and need to load for both 320 and 640 mode accrordingly.
*
* New Apple logo data and two color tables: logocolora and logocolorb.
*
* 19-Feb-2023 Chris Parana
*
* New DrawRect draws bottom line only instead of outlining menubar
*
***********************************************************************************

	blanks off
	string asis

	print push
	print off

	include 'all.macros'

	INCLUDE 'e16.qdaux'
	INCLUDE 'e16.resources'

	print pop

	include 'MenuEquates.asm'

;-----------------------------------------------
;
;   Imported addresses from WCM.Lib
;
;-----------------------------------------------
	IMPORT pushDpage
	IMPORT pushDlong
	IMPORT allocate2
	IMPORT allocate3
	IMPORT startup
	IMPORT Epop0bytes
	IMPORT Epop2bytes
	IMPORT Epop4bytes
	IMPORT Epop6bytes
	IMPORT Epop8bytes
	IMPORT Epop10bytes
	IMPORT Epop12bytes
	IMPORT Epop14bytes
	IMPORT Epop16bytes
	IMPORT Epop18bytes
	IMPORT Epop26bytes
	IMPORT Epop32bytes

	import pop0bytes
	import pop2bytes
	import pop4bytes
	import pop6bytes
	import pop8bytes
	import pop10bytes
	import pop12bytes
	import pop14bytes
	import pop16bytes
	import pop18bytes
	import pop26bytes
	import pop32bytes

	entry FakeGetPopUpDefProc

;-----------------------------------------------
;
;   Forward addresses and entries
;
;-----------------------------------------------
	ENTRY GetMenuMgrPort
	ENTRY InitPalette
	ENTRY MenuBootInit
	ENTRY MenuGlobal
	ENTRY MenuNewRes
	ENTRY MenuReset
	ENTRY MenuShutDown
	ENTRY MenuStartup
	ENTRY MenuStatus
	ENTRY MenuVersion
	ENTRY NewMenu
	ENTRY Reserved
	ENTRY clearWAP
	ENTRY initres

	ENTRY MENUKEY
	ENTRY GETMENUBAR
	ENTRY MENUREFRESH
	ENTRY FLASHMENUBAR
	ENTRY INSERTMENU
	ENTRY DELETEMENU
	ENTRY GETSYSBAR
	ENTRY SETSYSBAR
	ENTRY FIXMENUBAR
	ENTRY COUNTMITEMS
	ENTRY NEWMENUBAR
	ENTRY GETMHANDLE
	ENTRY SETBARCOLORS
	ENTRY GETBARCOLORS
	ENTRY SETMTITLESTART
	ENTRY GETMTITLESTART
	ENTRY CALCMENUSIZE
	ENTRY SETMTITLEWIDTH
	ENTRY GETMTITLEWIDTH
	ENTRY SETMENUFLAG
	ENTRY GETMENUFLAG
	ENTRY SETMENUTITLE
	ENTRY GETMENUTITLE
	ENTRY SETMITEM
	ENTRY GETITEM
	ENTRY SETMITEMFLAG
	ENTRY GETITEMFLAG
	ENTRY SETITEMBLINK
	ENTRY DRAWMENUBAR
	ENTRY MENUSELECT
	ENTRY HILITEMENU
	ENTRY DISPOSEMENU
	ENTRY ENABLEMITEM
	ENTRY DISABLEMITEM
	ENTRY CHECKMITEM
	ENTRY SETMITEMMARK
	ENTRY INSERTMITEM
	ENTRY DELETEMITEM
	ENTRY GETITEMMARK
	ENTRY SETMITEMSTYLE
	ENTRY GETITEMSTYLE
	ENTRY SETMENUID
	ENTRY SETITEMID
	ENTRY SETMENUBAR
	ENTRY SETMITEMNAME
	ENTRY ENDINITRAM
	ENTRY STARTINITRAM
	ENTRY DefColorTable
	ENTRY SYS_CURRENT
	ENTRY LOCKMENUBAR
	ENTRY CLOSEMENUPORT
	ENTRY EVERYCACHEFREE
	ENTRY UNLOCKMENUBAR
	ENTRY SAVE_PORT
	ENTRY PUSHPORT
	ENTRY PUSHSCINFO1
	ENTRY PUSHDEFBARRECT
	ENTRY TO_UPORT
	ENTRY SCANBYTE
	ENTRY PUSHCOLORTABLE
	ENTRY LOGOCOLORA
	ENTRY LOGOCOLORB
	ENTRY MAKE_BLOCK
	ENTRY LOCKMENUHAND
	ENTRY DEREFMENUHAND
	ENTRY UNLOCKMENUHAND
	ENTRY NEXT_ITEM
	ENTRY PUSHDEFMENU
	ENTRY PUSHDATA
	ENTRY TO_MYPORT
	ENTRY GETCOLOR
	ENTRY SETOUTLINE
	ENTRY DRAWRECT
	ENTRY GETMFIRST
	ENTRY NEXT_MENU
	ENTRY GETMPTR
	ENTRY TITLEXSTART
	ENTRY DISPATCH
	ENTRY GETMEVENT
	ENTRY ONBAR
	ENTRY PULL_DOWN
	ENTRY PULLUP
	ENTRY PUSHYRAT
	ENTRY PUSHMRECT
	ENTRY GET_IDS
	ENTRY GETIFIRST
	ENTRY PUSHCOLOR
	ENTRY ALLOCATECACHE
	ENTRY FREECACHE
	ENTRY MAKECACHE
	ENTRY CACHE
	ENTRY PUSHCOLOR2
	ENTRY UNCACHE
	ENTRY LONG_CALL
	ENTRY DRAW_MENU
	ENTRY CHOOSE_ITEM
	ENTRY SIZE_MENU
	ENTRY DRAW_TITLE
	ENTRY DRAW_ITEM
	ENTRY GET_ITEMID
	ENTRY CALCITEM
	ENTRY GETITEMH
	ENTRY TEXT_GUTS
	ENTRY GETISTRG
	ENTRY GET_APPLE
	ENTRY PRINTSTRG
	ENTRY DIMMED
	ENTRY NOR_MASK
	ENTRY PUSHRECT
	ENTRY PUSHMARK
	ENTRY PUSHCOM_KEY
	ENTRY HLINE
	ENTRY GETIPTR2
	ENTRY INTO_BLOCK
	ENTRY GETIPTR
	ENTRY GROWBLOCK
	ENTRY EVERYCACHEBAD
	ENTRY BADCACHE
	ENTRY _320_MASK
	ENTRY _320_DATA
	ENTRY _640_MASK
	ENTRY _640_DATA
	ENTRY JustifyLeft
	ENTRY JustifyRight

	ENTRY FixTextFace
	ENTRY ClearTextFace
	ENTRY CheckForScrolling
	ENTRY CheckBounds
	ENTRY GetStarting
	ENTRY ResetThings
	ENTRY UpArrowIcon
	ENTRY DownArrowIcon
	ENTRY DrawUpArrow
	ENTRY DrawDwnArrow
	ENTRY AdjustBottom
	ENTRY AdjustTop
	ENTRY InitStuff
	ENTRY AdjustRect
	ENTRY Pull_Down2
	ENTRY TrackMenu2
	ENTRY GetrMenuTitle
	ENTRY GetrItemName
	ENTRY GetrItemIcon		; 12/19/89 H.Y. for icon drawing support
	ENTRY GetIconInfo		; 12/20/89 H.Y. for icon drawing support
	ENTRY DrawItemIcon		; 12/20/89 H.Y. for icon drawing support
	ENTRY GetStruct
	ENTRY LoadnRelease
	ENTRY FillItemRec
	ENTRY UpArrowLocInfo640
	ENTRY UpArrowLocInfo320
	ENTRY UpArrowBounds640
	ENTRY UpArrowBounds320
	ENTRY DownArrowLocInfo640
	ENTRY DownArrowLocInfo320
	ENTRY DownArrowBounds640
	ENTRY DownArrowBounds320
	ENTRY CommonInsert
	ENTRY GetResMTitle
	ENTRY PopupMenuSelect
	ENTRY NewMenu2
	ENTRY InsertMItem2
	ENTRY SetMenuTitle2
	ENTRY SetMItem2
	ENTRY SetMItemName2
	ENTRY NewMenuBar2
	ENTRY PushSmearLow
	ENTRY SaveColor
	ENTRY RestoreColor
	ENTRY doWhiteSpace
	ENTRY addToTop
	ENTRY addToBottom
	ENTRY NeverMind
	ENTRY HideMenuBar
	ENTRY ShowMenuBar
	ENTRY AddorSubRegion
	ENTRY Hole
	ENTRY SetItemIcon
	ENTRY GetItemIcon
	ENTRY SetItemStruct
	ENTRY GetItemStruct
	ENTRY RemoveItemStruct
	ENTRY GetItemFlag2
	ENTRY SetItemFlag2
	ENTRY GetItemWidth
	ENTRY GetMItemBlink		;19-Sep-90 DAL
	entry InsertPathMItems	;10-Jan-90 DAL

;===========================================================================
;          Menu Manager function table.
;===========================================================================
MenuCallTable	PROC EXPORT

	ENTRY FPT
FPT	DC.W (ENDFPT-FPT)/4
	DC.W 0
	DC.L MenuBootInit-1	$010F
	DC.L MenuStartup-1	$020F
	DC.L MenuShutDown-1	$030F
	DC.L MenuVersion-1	$040F
	DC.L MenuReset-1	$050F
	DC.L MenuStatus-1	$060F
	DC.L Reserved-1	$070F
	DC.L Reserved-1	$080F
	DC.L MenuKey-1	$090F
	DC.L GetMenuBar-1	$0A0F
	DC.L MenuRefresh-1	$0B0F
	DC.L FlashMenuBar-1	$0C0F
	DC.L InsertMenu-1	$0D0F
	DC.L DeleteMenu-1	$0E0F
	DC.L InsertMItem-1	$0F0F
	DC.L DeleteMItem-1	$100F
	DC.L GetSysBar-1	$110F
	DC.L SetSysBar-1	$120F
	DC.L FixMenuBar-1	$130F
	DC.L CountMItems-1	$140F
	DC.L NewMenuBar-1	$150F
	DC.L GetMHandle-1	$160F
	DC.L SetBarColors-1	$170F
	DC.L GetBarColors-1	$180F
	DC.L SetMTitleStart-1 $190F
	DC.L GetMTitleStart-1 $1A0F
	DC.L GetMenuMgrPort-1 $1B0F
	DC.L CalcMenuSize-1	$1C0F
	DC.L SetMTitleWidth-1 $1D0F
	DC.L GetMTitleWidth-1 $1E0F
	DC.L SetMenuFlag-1	$1F0F
	DC.L GetMenuFlag-1	$200F
	DC.L SetMenuTitle-1	$210F
	DC.L GetMenuTitle-1	$220F
	DC.L MenuGlobal-1	$230F     	;Added 2/18/87
	DC.L SetMItem-1	$240F
	DC.L GetItem-1	$250F
	DC.L SetMItemFlag-1	$260F
	DC.L GetItemFlag-1	$270F
	DC.L SetItemBlink-1	$280F
	DC.L MenuNewRes-1	$290F
	DC.L DrawMenuBar-1	$2A0F
	DC.L MenuSelect-1	$2B0F
	DC.L HiliteMenu-1	$2C0F
	DC.L NewMenu-1	$2D0F
	DC.L DisposeMenu-1	$2E0F
	DC.L InitPalette-1	$2F0F
	DC.L EnableMItem-1	$300F
	DC.L DisableMItem-1	$310F
	DC.L CheckMItem-1	$320F
	DC.L SetMItemMark-1	$330F
	DC.L GetItemMark-1	$340F
	DC.L SetMItemStyle-1 $350F
	DC.L GetItemStyle-1	$360F
	DC.L SetMenuID-1	$370F
	DC.L SetItemID-1	$380F
	DC.L SetMenuBar-1	$390F
	DC.L SetMItemName-1	$3A0F

******* Adding new calls for System Disk 4.1 ******************************

	DC.L FakeGetPopUpDefProc-1 $3B0F
	DC.L PopUpMenuSelect-1 $3C0F
	DC.L Hole-1	$3D0F 	;used to be DrawPopUp call
	DC.L NewMenu2-1	$3E0F

	DC.L InsertMItem2-1	$3F0F
	DC.L SetMenuTitle2-1 $400F
	DC.L SetMItem2-1	 $410F
	DC.L SetMItemName2-1 $420F
	DC.L NewMenuBar2-1	$430F

	DC.L GetResMTitle-1 $440F
	DC.L HideMenuBar-1	$450F
	DC.L ShowMenuBar-1	$460F
	DC.L SetItemIcon-1  $470F	;added 20 Dec 89 H.Y. for item icon support
	DC.L GetItemIcon-1  $480F	;added 20 Dec 89 H.Y. for item icon support
	DC.L SetItemStruct-1  $490F	;added 05 Jul 90
	DC.L GetItemStruct-1  $4A0F	;added 05 Jul 90
	DC.L RemoveItemStruct-1  $4B0F	;added 05 Jul 90
	DC.L GetItemFlag2-1   $4C0F	;added 05 Jul 90
	DC.L SetItemFlag2-1   $4D0F	;added 05 Jul 90
	DC.L GetItemWidth-1	  $4E0F	;added 10 Jul 90 for "Jay's" stuff
	dc.L GetMItemBlink-1  $4F0F	;added 19 Sep 90 DAL
	dc.l InsertPathMItems-1 $500F	;added 10-Jan-91 DAL
ENDFPT
	ENDP

;===========================================================================
;	Hole
;===========================================================================
Hole	PROC

	rtl

	ENDP

****************************************************************
*
FakeGetPopUpDefProc	PROC
*
* Jumps to code in dynamic segment so address of dynamic
* segment is not in tool table.
*
*
* Inputs:
*	space for output
*
* Outputs:
*	space for output
*
* External Refs:
	import GetPopUpDefProc
*
* Entry Points:
*	none
*
	longa on	; mode
	longi on
*
*
* Added 15 May 89	Steven Glass
*
****************************************************************


	jml GetPopUpDefProc

	ENDP


;===========================================================================
;
;	MenuStartup
;
;        	Initialize Menu Manager
;
;  IN:     PUSH:WORD - ID to use.
;          PUSH:WORD - zero page number	to use.
;
; OUT:     Nothing.
;
;===========================================================================
MenuStartup	PROC
	import SelfMod1Low
	import SelfMod1High
	import SelfMod2

TheReturnAddr	equ 1	Stack offset before	setup called.
directPage	equ TheReturnAddr+6

newZero	equ input	Stack offset after setup called.
newID	equ newZero+2


	cmp #0	Has the Menu Manager already been started?
	beq ok1

	jsl IncBusyFlg
	ldy #MENU_STARTED	Return error code.
	phd
	phb
	brl Epop4bytes

ok1	lda directPage,s	Get direct page to use.
	jsr startup	Do startup initialization for tool call.

	pea 0	Tell Tool Locator about zero page.
	pea MenuToolNum	Tool number.
	pea 0
	phd	Zero page number.
	_SetWAP

	ldx #$00FE	Clear my direct page.
lop10	stz $00,x
	dex
	bpl lop10

	lda newID,s
	sta <MyID

*** self-modify the address of the 640-mode color table 26-Sep-90 DAL
	phb
	phk
	plb

	pha
	pha
	_Get640Colors
	pla
	sta SelfMod1Low+1
	sta SelfMod2+1
	pla
	sta SelfMod1High+1
	sep #$20
	sta SelfMod2+3
	rep #$20

	plb
;
; --- Allocate and initialize RAM data area -----------------
;
	ldy <MyID	Pass ID to use.
	lda #RAMSIZE	Pass number of bytes to allocate.
	jsr allocate2	Allocate a fixed RAM area.
	sta <data	Store handle to data area.
	stx <data+2
	ldy #2	Dereference data area.
	lda [<data],y
	tay
	lda [<data]
	sta <data	Store pointer to data area.
	sty <data+2

	sep #$20
	longa off

	ldy #RAMSIZE-1
	lda #0
lop2	sta [<data],y
	dey
	cpy #(endInitRAM-startInitRAM)-1
	bne lop2

lop3	lda startInitRAM,y
	sta [<data],y
	dey
	bpl lop3

	rep #$20
	longa on

	ldx #16
lop5	lda RAMpatch,x	Compute address, direct page or data area?
	bpl ok5

	and #$7FFF	Compute address in direct page.
	pha
	tdc
	clc
	adc 1,s
	ply
	ldy #0
	bra store5

ok5	ldy <data+2	Compute address in data area.
	lda <data
	clc
	adc RAMpatch,x
	bcc store5
	iny

store5	phy	Save address.
	pha

	lda RAMoffset,x	Get offset to variable to be patched.
	bpl ok6	Is patch in direct page or data area?

	stx <work	Patch in direct page.
	and #$7FFF
	tax
	pla
	sta <0,x
	pla
	sta <2,x
	ldx <work
	bra next5

ok6	tay	Patch in data area.
	pla
	sta [<data],y
	iny
	iny
	pla
	sta [<data],y

next5	dex
	dex
	bpl lop5

;
; --- Other initialization ----------------------------------
;
	pha	Space for result.
	pha
	pea 1	Get pointer to address table command.
	_GetAddress
	pla	Get table of scan line addresses.
	sta <lineTable
	pla
	sta <lineTable+2

	jsr initres	Make resolution dependent inits.

*** If we want to use ReadBParam for a default MItemBlink value, this
*** is the place to do it.  DAL  (Later...did it!)
;	lda #3	Number of blinks for selected items.
;	sta <blink

	pha	;space for result
	pea $5E	;aug_param: bits 3-4 = menu blink (0..3)
	_ReadBParam
	pla
	lsr a
	lsr a
	lsr a
	and #3	;amount of menublink to use
	sta <blink

;
; --- Create an empty system menu bar ------------------------
;
	pha	Space for result.
	pha
	lda #0	System menu bar.
	pha
	pha
	_NewMenuBar	Allocate a system menu bar.
	pla
	sta <sysmenu	Save handle.
	pla
	sta <sysmenu+2

	jsr sys_current	Make the system menu bar current.

	_DrawMenuBar

	brl pop4bytes	no error

;
; --- Table of offsets to address that must be patched ----------------
;
;  Set the high bit	if the variable to be patched is in direct page.
;  Clear the high bit if the variable to be patched is in data area.

RAMpatch	DC.W scrnInfo	0
	DC.W memInfo	2
	DC.W scrnRect+$8000	4
	DC.W des_0+$8000	6
	DC.W memInfo	8
	DC.W scrnInfo	10
	DC.W memInfo+BoundsRect 12
	DC.W des_y+$8000	14
	DC.W image	16

;
; --- Table of offsets to address that must be patched ----------------
;
;  Set the high bit	if offset into direct page.
;  Clear the high bit if offset into data area.
;
RAMoffset	DC.W tomemory+$8000
	DC.W tomemory+4+$8000
	DC.W tomemory+8+$8000
	DC.W tomemory+12+$8000
	DC.W toscreen+$8000
	DC.W toscreen+4+$8000
	DC.W toscreen+8+$8000
	DC.W toscreen+12+$8000
	DC.W imageInfo+PixelImage

	ENDP


;===========================================================================
;
;	MenuStatus
;
;          	Return status of Menu Manager.
;
;   IN:    None.
;
;  OUT:    WORD - 1	if active, 0 if not	active.
;
;===========================================================================
MenuStatus	PROC

TheReturnAddr	equ 1	Stack offset before	startup called.
result	equ TheReturnAddr+6

	tax
	beq store
	lda #7	Dan O. version number.
store	sta result,s	Return status.


;================================================================
;          Boot Initialization code.
;================================================================
	ENTRY MenuBootInit
MenuBootInit
	ENTRY Reserved
Reserved
	ENTRY exitTool
exitTool

	lda #0	No error code.
	clc	No error.

	rtl

	ENDP


;===========================================================================
;
;	MenuReset
;
;          	Reset handler.
;
;   IN:    None.
;  OUT:    None.
;
;===========================================================================
MenuReset	PROC
;
	jsr startup	Do startup initialization for tool call.
	brl clearWAP

	ENDP


;===========================================================================
;
;	MenuShutDown
;
;          	ShutDown the Menu Manager.
;
; Change History
;
; 14 Oct 88	Steven Glass
;
; Check to see if active before trying to shutdown.
;
;===========================================================================
MenuShutDown	PROC

	cmp #0	If the tool is not active, we
	bne @Continue	just get out.

	clc
	rtl

@Continue

	jsr startup	Do startup initialization for tool call.

;
; --- Free all menus in system menu bar	--------------------------------
;
	lda <sysMenu+1	Is there a system menu bar?
	beq exit3

	jsr sys_current	<barHand = <sysMenu. Current = system.
	jsr lockMenuBar	Dereference and lock menu bar and menus.
;	                  	<barPtr = (<barHand).

	ldy #MenuList
lop1	lda [<barptr],y
	sta <work
	iny
	iny
	lda [<barptr],y
	tax
	iny
	iny
	ora <work	End of menu list?
	beq exit2

	phy	Save Y.

	phx
	pei <work
	_DisposeHandle	Free menu record.

	ply
	bra lop1

;
; --- Free system menu bar ------------------------------------
;
exit2	pei <sysmenu+2
	pei <sysmenu
	_DisposeHandle	Free system menu bar.

;
; --- Close Menu Manager's port -------------------------------
;
exit3	jsr closeMenuPort	Close Menu Manager's port.

;
;
; --- Free allocated data area.
;
	pha
	pha
	pei <data+2	Find handle of data area.
	pei <data
	_FindHandle
	_DisposeHandle
;
;
; --- Set work value in Tool Locator to	zero ------------------
;
	ENTRY clearWAP
clearWAP
	lda #0
	pha
	pea MenuToolNum	Pass Menu Manager tool number.
	pha	Pass new parameter (zero).
	pha
	_SetWAP	Tell Tool Locator about it.

	brl pop0bytes	no error

	ENDP


;===========================================================================
;
;	MenuNewRes
;
;        	Set up in Screen Resolution.
;
;   IN:  Nothing.
;  OUT:  Nothing.
;
;===========================================================================
MenuNewRes	PROC

	jsr startup	Do startup initialization for tool call.

;
; --- Fix current menu bar and redraw --------------------------------------
;
	lda <sysMenu+1	Is there a system menu bar?
	beq exit

	jsr sys_current	<barHand = <sysMenu. Current = system.
	jsr lockMenuBar	Dereference and lock menu bar and menus.
;	                  	<barPtr = (<barHand).
	ldy #ctlFlag
	lda [<barptr],y
	and #$0080	See if the current system menu bar is visible or not.
;		Since initres tries to subtract menu bar for desktop
;		we only want to do it if it's visible.
	sta <temp
;
; --- Shut down current graphics mode, start new one up ----------------------
;
	jsr closeMenuPort	Close Menu Manager's port.
	jsr initres	Reinitialize in new	mode.

;
; --- Fix current menu bar and redraw --------------------------------------
;
	lda <sysMenu+1	Is there a system menu bar?
	beq exit

	jsr sys_current	<barHand = <sysMenu. Current = system.
	jsr lockMenuBar	Dereference and lock menu bar and menus.
;	                  	<barPtr = (<barHand).

	jsr everyCacheFree	Free all caches, size may change.

	lda #320
	ldy #CtlRect+x2
	ldx <screenmode	320 or 640 mode?
	beq store
	asl a
store	sta [<barptr],y

	_DrawMenuBar	Redraw system menu bar.

	jsr unlockMenuBar	Unlock menu bar and	menus.

exit	brl pop0bytes	no error

	ENDP


;===========================================================================
;
;	MenuGlobal
;
;          	Get/Set global flag.
;
;   IN:    WORD - negative to clear bits, positive to set bits,
;                 zero to just return current global flag.
;
;  OUT:    WORD - global flag after change.
;
;===========================================================================
MenuGlobal	PROC

newState	equ input
newFlag	equ newState+2

	jsr startup	Do startup initialization for tool call.

	lda newState,s	Set or reset bits?
	bpl setBits

	and <globalFlag
	bra exit3

setBits	ora <globalFlag
exit3	sta <globalFlag
	sta newFlag,s

	brl pop2bytes	no error

	ENDP


;===========================================================================
;
;	InitRes
;
;        	Resolution dependent initialization.
;
;   IN:    <temp = 0 if menu bar visible, 1 if invisible.
;  OUT:    None.
;
;        Resolution	should already have	been set.
;
;===========================================================================
initres	PROC

	jsr save_port	Save current port.

	jsr pushport	Pass pointer to Menu Manager port.
	_OpenPort	Open port for Menu Manager.

	pea 4	Use OR mode to write text.
	_SetTextMode	Set text mode.

	jsr pushscInfo1	Pass pointer to scInfo1.
	_GetPortLoc	Get the parameters of the screen.

;
; --- Initialize for 320 mode -------------------------
;
	stz <vert_pen	Width of vertical lines
	inc <vert_pen	is one in 320.

	stz <screenmode
	lda #0
	ldy #scrnInfo
	sta [<data],y
	ldy #memInfo
	sta [<data],y
	ldy #imageInfo
	sta [<data],y
	lda #8
	ldy #imageInfo+6
	sta [<data],y

	lda <scInfo1+BoundsRect+x2 Get width of	screen.
	ldy #defmenu+CtlRect+x2 Set width of system menu bar.
	sta [<data],y
	ldy #scrnInfo+8+x2
	sta [<data],y

	cmp #320
	beq ok200	320 mode? Flag already set to zero.
;
;
; --- Initialize for 640 mode --------------------------
;
	inc <vert_pen	Vertical lines are 2 wide in 640.

	inc <screenmode	640 mode flag, 1.

	lda #$0080
	ldy #scrnInfo
	sta [<data],y
	ldy #memInfo
	sta [<data],y
	ldy #imageInfo
	sta [<data],y
	lda #4
	ldy #imageInfo+6
	sta [<data],y

;
; --- Get system font's parameters ----------------------
;
ok200	pea 0	; space for result
	PushWord #$57	; get the width of 'W' and we'll use this as our maxwidth
	_CharWidth
	pla
	sta <text_width

	lda #font_h
	jsr pushDpage
	_GetFontInfo

	lda <descent
	clc
	adc #B_LEADING
	sta <descent

	clc
	adc <font_h	Add the ascent,
	adc #T_LEADING	plus top leading.
	sta <font_h	Store the height.

;
; --- Subtract the system menu bar from	the desktop ---------
;
	inc a
	ldy #defMenu+CtlRect+y2
	sta [<data],y	Set bottom of default menu bar.

	lda <temp
	bne MenuBarInvisible

	_InitPalette	Initialize palette for color logo.

	pha
	pha
	_NewRgn	Allocate a temp region.

	lda 1,s	Save temp region handle.
	sta <work
	lda 3,s
	sta <work+2

	jsr pushdefBarRect	Pass pointer to default menu bar RECT.
	_RectRgn	Make a region out of the menubar.

	pea 0	Subtract operation.
	pei <work+2	Handle of region to	subtract.
	pei <work
	_Desktop	Subtract the menubar from the desktop.
	bcc noerr	Error?
	pla	Fix stack, _Desktop	didn't.
	pla
	pla

noerr	pei <work+2
	pei <work
	_DisposeRgn	Free the temp region.

MenuBarInvisible	jsr to_uport

	rts

	ENDP


;===========================================================================
;
;	InitPalette
;
;          	Initialize color palette for Apple Logo.
;
;   IN:    None.
;  OUT:    None.
;
;   Change History
;
;   26 Jan 23	Chris Parana
;
;===========================================================================
InitPalette	PROC

	jsr startup	Do startup initialization for tool call.

	ldx #7
lop200	phx	Save.

	lda scanbyte,x
	ldy #scrnInfo
	ora [<data],y
	and #$00FF
	inx
	inx
	phx	Scan line number.
	pha	Scan byte value.
	_SetSCB

	plx	Restore counter.
	dex
	bpl lop200

	pea 0
	jsr pushColorTable
	_GetColorTable

	ldx #6
	ldy #10

; Suggested changes from Geoff Body applied. Thanks Geoff!!

lop202	phx	Save.
	phy	Save.
	
	lda logocolora,y
	ldy #ColorTable+2 ; Palette 1-6, Color $1
	sta [<data],y
	ldy <screenmode
	beq ok202
	ldy #ColorTable+10 ; Palette 1-6 Color $5
	sta [<data],y
	ldy #ColorTable+18 ; Palette 1-6 Color $9
	sta [<data],y
	ldy #ColorTable+26 ; Palette 1-6 Color $D
	sta [<data],y
ok202	ply Restore
	phy Save
	lda logocolorb,y
	ldy #ColorTable+4 ; Palette 1-6, Color $2
	sta [<data],y
	ldy <screenmode
	beq ok203
	ldy #ColorTable+12 ; Palette 1-6 Color $6
	sta [<data],y
	ldy #ColorTable+20 ; Palette 1-6 Color $A
	sta [<data],y
	ldy #ColorTable+28 ; Palette 1-6 Color $E
	sta [<data],y
ok203	phx	Table number.
	jsr pushColorTable
	_SetColorTable
	ply	Restore.
	plx	Restore.
	dey
	dey
	dex
	bne lop202
	brl pop0bytes	no error

ENDP


;===========================================================================
;
;	MenuVersion
;
;        	Return Menu Manager's Version number.
;
;   IN:  Nothing.
;  OUT:  WORD - version number.
;
;===========================================================================
MenuVersion	PROC

TheReturnAddr	equ 1	Stack offset before	setup called.
result	equ TheReturnAddr+6

	lda #$0305	Version Number. (26-Jan-2023 CP)
	sta result,s	Store in return space.
	brl exitTool

	ENDP


;===========================================================================
;
;	GetMenuMgrPort
;
;        	Return Menu Manager's Port pointer.
;
;   IN:    Nothing.
;
;  OUT:    LONG - pointer to Menu Manager's port.
;
;===========================================================================
GetMenuMgrPort	PROC

result	equ input

	jsr startup	Do startup initialization for tool call.

	jsr pushport
	pla	Return Menu Manager's port pointer.
	sta result+2,s
	pla
	sta result+2,s

	brl pop0bytes	no error

	ENDP


;=======================================================================
;
; 	N E W M E N U 2
;
;=======================================================================
NewMenu2	PROC

menuRef	equ input
inputVerb	equ menuRef+4
result	equ inputVerb+2

myTemp	equ work	; 0 used for dereferencing
resMenuHdl	equ work+4	; 4 redefine some zero page equates
resMenuPtr	equ resMenuHdl+4	; 8
origMenuRef	equ resMenuPtr+4	; 12 save original menuref just in case it was a resource ID
count1	equ origMenuRef+4	; 16 counter for number of items in the menu
count2	equ count1+2	; 18
mem_needed	equ count2+2	; 20

itemVerb	equ temp

	jsr startup

	stz <resMenuHdl
	stz <resMenuHdl+2
	stz <origMenuRef
	stz <origMenuRef+2

	lda inputVerb,s
	asl a
	tax
	jmp (startupTable,x)

startupTable	dc.w ptrStartup	; verb = 0
	dc.w handStartup	; verb = 1
	dc.w resStartup	; verb = 2

;==================================================
;
; The menuref is the resource ID to the menu.

resStartup	lda menuRef,s	; save resource ID so we can use it to release resource
	sta <origMenuRef	; later on down the road
	lda menuRef+2,s
	sta <origMenuRef+2

	pha	; space for handle to menu resource
	pha
	PushWord #rMenu	; resource type
	lda <menuRef+8,s	; resource ID
	pha
	lda <menuRef+8,s
	pha
	_CMLoadResource	; CMLoadResource
	pla
	plx
	sta <menuRef,s
	txa
	sta <menuRef+2,s


;==================================================
;
; The menuref is a handle to the resource.

handStartup	lda menuRef+2,s
	sta <resMenuHdl+2
	lda menuRef,s
	sta <resMenuHdl

	ldy #4	; lock down the handle
	lda [<resMenuHdl],y
	ora #$8000
	sta [<resMenuHdl],y

	dey
	dey
	lda [<resMenuHdl],y	; dereference the handle and put it back on the
	sta menuRef+2,s	; stack, so we can fall down to the next code section
	lda [<resMenuHdl]
	sta menuRef,s

;==================================================
;
; The menuref is a pointer to the menu resource.
; This is where we get the memory for our menu record and fill this record
; in.

ptrStartup	lda menuRef+2,s
	sta <resMenuPtr+2	; put the ptr to the resource on our
	lda menuRef,s	; direct page for easier access
	sta <resMenuPtr

;
; pass 1 determines how much memory we need
;
	stz <count1
	stz <mem_needed	; keep track of amount of memory needed
	ldy #itemResourceID	; let's get the first item in the menu
	lda #MENUSIZE+2	; get size of menu record

lop1	clc
	adc <mem_needed
	sta <mem_needed

	lda [<resMenuPtr],y
	iny
	iny
	ora [<resMenuPtr],y
	beq noMoreItems
	inc <count1
	lda #ITEMSIZE
	iny	; skip to next item
	iny
	bra lop1

noMoreItems	lda <mem_needed
	jsr make_block	; get the memory we need
	sta <menuhand
	sta result,s	; return handle to the menu record
	stx <menuhand+2
	txa
	sta result+2,s
	bcc gotMemOK	; could'nt get the memory
	brl exit

gotMemOK	jsr lockMenuHand
	jsr derefMenuHand

	lda #0	; first zero out the memory we just got
	ldy <mem_needed
	bra enter1
lop2	sta [<menuptr],y
enter1	dey
	dey
	bpl lop2

;
; Pass 2 we start filling in the menu record
;
	ldy #resMenuID	; copy ID of menu into menu record
	lda [<resMenuPtr],y
	ldy #MenuID
	sta [<menuptr],y

	ldy #resMenuFlag	; copy menuFlag and menuRes bytes into menu record
	lda [<resMenuPtr],y
	and #$CFFF	; get rid of the low two bits of high byte
	ldy #MenuFlag
	sta [<menuptr],y

	ldy #NumOfItems	; get number of items in the menu, calculated
	lda <count1	; above when figuring out size of menu
	sta [<menuptr],y

	ldy #resTitleName	; get reference to the menu title and move it into
	lda [<resMenuPtr],y	; our menu record
	ldy #TitleName
	sta [<menuptr],y
	ldy #resTitleName+2
	lda [<resMenuPtr],y
	ldy #TitleName+2
	sta [<menuptr],y

; Load the menu title string resource so we can check to see if it's the Apple logo.
; If so, we have to set the titlewidth.
;
	jsr getrMenuTitle	; get ptr to the menu title
	sta <myTemp
	stx <myTemp+2

	lda [<myTemp]	; now check to see if this is the apple logo
	cmp #$4001	; has the apple logo already been set
	bne skip_apple_logo

	ldy #titleWidth	; set default width for the an apple logo title
	lda #24
	sta [<menuptr],y	; copy default title width into menu record

skip_apple_logo	lda #MenuSize	; keep track of where we are in the menu record
	sta <count1
	lda #itemResourceID
	sta <count2	; keep track of where we are in the resource menu record

	ldy #resMenuFlag
	lda [<resMenuPtr],y
	and #$3000	; just look at the low two bits of the high byte
	xba	; now we have the correct verb value
	lsr a
	lsr a
	lsr a
	lsr a
	sta <itemVerb

getNextItem	ldy <count2
	lda [<resMenuPtr],y
	sta <temptr2
	iny
	iny
	ora [<resMenuPtr],y
	beq ThatsAllFolks
	lda [<resMenuPtr],y
	sta <temptr2+2

	lda <itemVerb	; x contains the what the item reference is
	ldy <count1	; y is index into the menu record
	jsr fillItemRec	; now fill in the item record

	lda <count1
	clc
	adc #ITEMSIZE
	sta <count1	; update index into menu rec where next item is to go

	lda <count2
	clc
	adc #4
	sta <count2	; get next item
	bra getNextItem
;
; Let's clean everything up. Otay!
;
ThatsAllFolks	jsr unlockmenuhand

	lda <resMenuHdl+1	; see if there was a handle involved
	beq exit

	ldy #4	; There was! There was! I knew I thaw a handle.
	lda [<resMenuHdl],y	; unlock the sucker
	and #$7FFF
	sta [<resMenuHdl],y

	lda <origMenuRef	; check to see if we loaded a menu resource
	bne releaseMenuRes
	lda <origMenuRef+2
	beq exit

releaseMenuRes	PushWord #rMenu
;	lda <origMenuRef+2
;	pha
;	lda <origMenuRef
;	pha
	pei <origMenuRef+2
	pei <origMenuRef
	_CMReleaseResource

exit	brl pop6bytes

	ENDP

;=======================================================================
;
; 	FillItemRec
;
;  IN: a = item reference, i.e. ptr, handle, or resource ID
;      y = index into menu record where item is to go
;      temptr2 = item reference (ptr, handle or resource ID)
;      menuptr = ptr to menu record that item is to be inserted into
; OUT: <menuptr with the current item record inserted
;
;=======================================================================
FillItemRec	PROC

	sty <count

	asl a
	tax
	jmp (itemtable,x)

itemtable	dc.w doItemPtr	; verb = 0
	dc.w doItemHandle	; verb = 1
	dc.w doItemResource	; verb = 2

doItemResource	ldy #rMenuItem
	lda <temptr2
	ldx <temptr2+2
	jsr LoadnRelease
	sta <temptr2
	stx <temptr2+2

doItemHandle	ldy #2
	lda [<temptr2],y
	tax
	lda [<temptr2]
	sta <temptr2
	stx <temptr2+2

doItemPtr	ldx <count
	lda #ItemRecSize
	sta <count
	ldy #resItemID

fillNext	lda [<temptr2],y	; start filling in the item record portion of the
	iny	; menu record
	iny
	phy
	txy
	sta [<menuptr],y
	iny
	iny
	tyx
	ply
	cpy <count
	beq done
	brl fillNext

done	rts

	ENDP

;=======================================================================
;
; 	getResMTitle
;
;  IN:  handle to menu record
; OUT:  result contains ptr to the menu title
;
;=======================================================================
getResMTitle	PROC

menuin	equ input	; handle to menu record
result	equ menuin+4	; ptr to the title

	jsr startup

	lda menuin,s
	sta <menuhand
	lda menuin+2,s
	sta <menuhand+2

	jsr lockmenuhand
	jsr derefmenuhand

	jsr getrMenuTitle

	sta result,s
	txa
	sta result+2,s

	jsr unlockmenuhand

	brl pop4bytes

	ENDP

;=======================================================================
;
; 	getrItemName
;
;  IN:  <itemptr contains ptr current item record in menu
; OUT:  a = low word of ptr to item name, x = high word of ptr
;
;=======================================================================
getrItemName	PROC

	ldy #ItemFlag	check if there is an additional structure associated with item
	lda [<itemptr],y
	and #I_NEWSTRUCTURE
	beq OldWay	if not then field "ItemName" does indeed contain the item's name

	jsr GetStruct	Get the ptr to the new structure that now contains the
	ldy #ItemName2	item's name.
	lda [<temptr],y
	tax
	ldy #ItemName2+2
	lda [<temptr],y
	sta <temptr+2
	stx <temptr
	bra GetName	We now have the reference to the item's name in <temptr.

OldWay	ldy #ItemName
	lda [<itemptr],y
	tax
	iny
	iny
	lda [<itemptr],y
	sta <temptr+2
	stx <temptr
GetName
	ldy #ItemFlag
	lda [<itemptr],y
	and #FIRST_TWO_BITS
	bne @1
	brl doPointer
@1	cmp #HANDLE_REF
	bne @2
	brl doHandle
@2	brl doResource

;=======================================================================
;
; 	getrItemIcon
;
;  IN:  <itemptr contains ptr current item record in menu
; OUT:  a = low word of ptr to item icon, x = high word of ptr
;       a & x = 0 if there is no icon associated with the icon
;
;=======================================================================
	ENTRY getrItemIcon
getrItemIcon
	jsr GetStruct
	ldy #ItemFlag2	; Extract flag from new structure that will tell us
	lda [<temptr],y	; how the icon will be referenced, i.e. ptr, hdl, resource
	pha	; Save flag from structure on the stack for now.

	ldy #ItemIcon	; Now extract the icon ref from this structure and put
	lda [<temptr],y	; reference in <temptr.
	tax
	ldy #ItemIcon+2
	lda [<temptr],y
	sta <temptr+2
	stx <temptr

	pla	; check flag from struct to see how icon will be referenced
	and #$0003	; Bits 8 and 9 tells us how the icon data will be referenced.
	bne @ResORHdl	; If not zero then ref is not pointer.
	brl doPointer	; Zero means it's a ptr to the icon data.
@ResORHdl	cmp #$0001	; Is the icon ref a handle?
	bne @IconRefIsResource
	brl doHandle
@IconRefIsResource	ldy #rIcon
	brl doResource2

;=======================================================================
;
; 	getrMenuTitle
;
;  IN:  <menuptr contains ptr to the menu record
; OUT:  a = low word of ptr to title, x = high word of ptr
;
;=======================================================================
	ENTRY getrMenuTitle
getrMenuTitle
	ldy #TitleName	; copy the titlename into one of our direct page locations
	lda [<menuptr],y
	sta <temptr
	iny
	iny
	lda [<menuptr],y
	sta <temptr+2

	ldy #MenuFlag	; first find out how the menu title will be referenced
	lda [<menuptr],y
	and #FIRST_TWO_BITS	; first two bits of the flag tells all
	beq doPointer
	cmp #HANDLE_REF
	beq doHandle

; if not pointer or handle then the menu title must be a resource ID
;
doResource	ldy #rPString	; type (was "rString" 17-Sep-90 DAL)

	ENTRY doResource2
doResource2	lda <temptr	; resource ID
	ldx <temptr+2
	jsr LoadnRelease	; loads resource and releases it, then returns handle
	sta <temptr
	stx <temptr+2

	ENTRY doHandle
doHandle	ldy #2
	lda [<temptr],y
	tax
	lda [<temptr]
	sta <temptr
	stx <temptr+2

	ENTRY doPointer
doPointer	lda <temptr	; low word of ptr to menu title/item name/icon ref
	ldx <temptr+2	; high word of ptr to menu title/item name/icon ref

	rts

	ENDP


;=======================================================================
;
;	GetStruct
;
;  IN: <itemptr pts to a valid item record
; OUT: <temptr contains data we're looking for
;
;=======================================================================
GetStruct	PROC

	ldy #ItemName
	lda [<itemptr],y
	sta <temptr
	ldy #ItemName+2
	lda [<itemptr],y
	sta <temptr+2

	ldy #ItemFlag
	lda [<itemptr],y
	and #$0300	Bits 8 and 9 tell us how structure is referenced.
	bne @ResOrHdl	If non-zero then structure is referenced as a hdl or resource
	brl doPointer
@ResOrHdl	cmp #I_STRUCTisHANDLE
	bne @doRes
	brl doHandle
@doRes	ldy #rMyItemStruct
	brl doResource2

	ENDP

;=======================================================================
;
; 	LoadnRelease
;
;  IN:  a = low word of resource ID, x = high word of resource ID
;       y = resource type
; OUT:  a = low word of handle to resource, x = high word of handle
;
;=======================================================================
LoadnRelease	PROC

myTemp	equ work

	phy	; inputs for CMReleaseResource, type
	phx	; resource ID
	pha

	pha	; space for result
	pha
	phy	; type
	phx	; resource ID
	pha
	_CMLoadResource
	pla
	sta <myTemp
	pla
	sta <myTemp+2

	_CMReleaseResource	; remember inputs pushed at beginning of routine

	lda <myTemp
	ldx <myTemp+2

	rts

	ENDP


;===========================================================================
;
;	NewMenu
;
;        	Allocate and initialize a menu.
;
;   IN:    PUSH:LONG - pointer to menu list.
;
;  OUT:    LONG - Handle of menu, zero if error.
;
;===========================================================================
NewMenu	PROC

menuline	equ input
return	equ menuline+4

mem_needed	equ work	0
list	equ mem_needed+2	2
menu_char	equ list+4	6
item_char	equ menu_char+2	8
check_mark	equ item_char+2	10
command	equ check_mark+2	12
flag	equ command+2	14
length	equ flag+2	16
real_len	equ length+2	18
;	                 	20

	jsr startup	Do startup initialization for tool call.

;
; --- Compute size of data structure needed -----------------------------
;
	ldx #0	Just count, flag.
	jsr parse

;
; --- Allocate menu	record -----------------------------------------------
;
	lda <mem_needed	Number of bytes needed.
	jsr make_block	Allocate the memory.
	sta <menuhand	Save handle of menu.
	stx <menuhand+2
	bcs exit	Was the block allocated?

	jsr lockMenuHand	<menuhand = locked.
	jsr derefMenuHand	<menuptr = (<menuhand)

;
; --- Clear some fields of menu record -----------------------------------
;
	lda #0
	ldy <mem_needed
	bra enter3
lop3	sta [<menuptr],y
enter3	dey
	dey
	bpl lop3

;
; --- Parse Menu strings and initialize	Menu record ------------------------
;
	ldx #1	Initialize menu records flag.
	jsr parse
;
; --- Return handle	of menu ------------------------------------------------
;
exit	lda <menuhand
	sta return,s
	lda <menuhand+2
	sta return+2,s

	jsr unlockMenuHand	<menuhand = unlocked.

	brl pop4bytes	no error


; = = = = = = = = =	= = = = = = = = = =	= = = = = = = = = = =
;          Menu list parser.
;
;   IN:    x = 0 if	just counting items.
;          menuptr = pointer of data area to initialize, zero if just counting.
;          list = pointer to list of menus.
;
;  OUT:    work = number of bytes needed.
;
; = = = = = = = = =	= = = = = = = = = =	= = = = = = = = = = =
parse	lda menuline+2,s
	sta <list
	sta <strg_ptr
	lda menuline+4,s
	sta <list+2
	sta <strg_ptr+2

	lda [<strg_ptr]	Store title character.
	and #$00FF
	sta <menu_char

	stz <mem_needed	Initialize size accumulator.
	stz <item_char	No item character yet.

lop1	jsr parse_strg	Parse the string.

;
; ------ Store address of menu's title ------------------
;
	txa	Just counting?
	beq skip1

	ldy #TitleName	Store pointer to menu's title.
	lda <strg_ptr
	sta [<menuptr],y
	lda <strg_ptr+1
	iny
	sta [<menuptr],y

;
; ------- Special case Apple logo title	----------------------
;
	lda [<strg_ptr]
	cmp #$FF01	Apple logo already set?
	beq apple_len
;
************* THE FOLLOWING LINE MUST BE CONVERTED MANUALLY!!!!! *************
	cmp #$4001	Just one '@' for Apple logo.
	bne skip_logo

	lda #$FF01	Make it the real logo value.
	sta [<strg_ptr]

apple_len	ldy #TitleWidth	Set logo title width here.
	lda #24
	sta [<menuptr],y

;
; ------- Set menu flag --------------------------------------
;
skip_logo	ldy #MenuFlag
	lda <flag
	and #M_ENABLED+M_NO_XOR
	ora #M_CACHE	Because it's allocated, it has caching.
	sta [<menuptr],y

;
; ------- Set menu's ID Number ------------------------------
;
	lda <count
	sta [<menuptr]

;
; ------- Compute address of item list --------------------------
;
skip10	ldy <menuptr+2
	lda <menuptr	Set pointer to menu's item list.
	clc
	adc #MENUSIZE
	bcc ok1
	iny
ok1	sta <itemptr	Set itemptr while I'm here.
	sty <itemptr+2

;
; ------- Increment	the memory counter ---------------------------
;
skip1	lda #MENUSIZE+2	Pass size of menu record.
	bra enter1

;
; --- Parse the items in the menu ---------------------------------
;
lop2	jsr parse_item

	lda #ITEMSIZE
enter1	clc	Accumulate number of bytes needed.
	adc <mem_needed
	sta <mem_needed

;
; ------ Compute address of next string	---------------------------
;
	lda <strg_ptr
	clc
	adc <real_len
	bcc ok10
	inc <strg_ptr+2
ok10	sta <strg_ptr

;
; ------ Is this a menu or item string?	---------------------------
;
	lda [<strg_ptr]
	and #$00FF

	beq allDone	If either a null or return character is the first character
	cmp #13	of an item definition then this is an empty menu.
	beq allDone

	ldy <item_char	Is this the first item?
	bne ck_it

	sta <item_char	This will be the item mark from now on.

ck_it	cmp <item_char
	beq lop2	Is the next string an item string?

allDone	rts


; = = = = = = = = =	= = = = = = = = = =	= = = = = = = = = = =
;          Parse a string.
;
;   IN:    x = parsing flag.
;          strg_ptr	= address of string.
;
;  OUT:    check_mark = item mark character.
;          command = keyboard equivalent character.
;          flag = set for disabled, underlined, special text, XOR.
;          length =	string's length.
;          real_len	= real string's length.
; = = = = = = = = =	= = = = = = = = = =	= = = = = = = = = = =
	ENTRY parse_strg
parse_strg	phx	;Save X.
;
; --- Find end of text string ------------------------------
;
	ldy #2
lop51	iny
	lda [<strg_ptr],y
	and #$00FF
	beq eol
	cmp #13	;Return?
	beq eol
	cmp #'\'	;Start of special characters.
	bne lop51

eol	dey

	lda 1,s	;Just counting?
	beq skip50

	tyx	;Save Y in X.

	dey
	sty <length

	ldy #1
	lda [<strg_ptr],y
	and #$FF00
	ora <length
	sta [<strg_ptr],y	Set string length.

	txy	Retore text length.

;
; --- Parse special	characters ---------------------------
;
skip50	stz <check_mark	Set defaults.
	stz <command
	lda #I_NO_XOR	Set XOR highlighting flag.
	sta <flag

	iny
	lda [<strg_ptr],y	Are there any special characters?
	and #$00FF	(Actually, there should always be one).
	tax
	brl next58

lop52	iny
lop53	lda [<strg_ptr],y
	and #$00FF
	cmp #'*'	Keyboard equivalent?
	bne next51

	iny
	lda [<strg_ptr],y	Grab two characters, primary & alternate.
	iny	Two bytes.
	sta <command	Save key characters.
	and #$FF00	Get alternate key alone.
	cmp #$2000	Is alternate a space?
	bne lop52
	lda <command
	and #$00FF	Zero out alternate if a space.
	sta <command
	bra lop52	Next character.

next51	cmp #'C'	Check mark?
	bne next52

	iny
	lda [<strg_ptr],y
	and #$00FF
	sta <check_mark
	bra lop52	Next character.

next52	cmp #'N'	ID Number?
	bne next60

	pha	Space to save Y.
	pha	Space for result.
	iny
	tya	Compute address of number.
	ldx <strg_ptr+2
	clc
	adc <strg_ptr
	bcc ok60
	inx
ok60	phx	Pass address of number string.
	pha

	ldx #0	Compute length of number string.
lop60	lda [<strg_ptr],y
	and #$00FF
	cmp #'0'
	bcc done60
	cmp #'9'+1
	bcs done60
	iny
	inx
	bra lop60

done60	phx	Pass length.
	pea 0	Unsigned.
	tya
	sta 11,s	Save Y.
	_Dec2Int	Convert ASCII number string to integer.
	pla
	sta <count	Save ID number.
	ply	Restore Y, index of	character after ID.
	bra lop53

next60	cmp #'H'
	bne next61

	iny	ID number is in hex.
	lda [<strg_ptr],y
	sta <count
	iny
	bra lop52

next61	tax
	lda <flag


;-----------------------------------------------------------
;
; Add checks for shadow and outline
;

	cpx #'S'
	bne @NotS
	ora #I_NOShadow	Set shadow text flag.
	bra store_flag

@NotS	cpx #'O'
	bne @NotO
	ora #I_NOOutLine	Set outline text flag.
	bra store_flag
@NotO
	cpx #'B'
	bne next53
	ora #I_NOBOLD	Set bold text flag.
	bra store_flag

;-----------------------------------------------------------
;
; Continue with old checks for the rest of this stuff.
;
next53	cpx #'I'
	bne next54

	ora #I_NOITALIC	Set italicize text flag.
	bra store_flag

next54	cpx #'U'
	bne next55

	ora #I_NOSCORE	Set underscore text	flag.
	bra store_flag

next55	cpx #'V'
	bne next56

	ora #I_NOUNDER	Set underline flag.
	bra store_flag

next56	cpx #'D'
	bne next57

	ora #I_ENABLED	Disable item.
	bra store_flag

next57	cpx #'X'
	bne next58

	eor #I_NO_XOR	Clear XOR highlighting flag.
store_flag	sta <flag
tolop52	brl lop52

next58	txa	Zero terminator?
	beq endofline

	cpx #13	Return?
	bne tolop52

endofline	sty <real_len

	inc <strg_ptr	Move string pointer	past first byte.
	bne exit58
	inc <strg_ptr

exit58	plx
	rts


; = = = = = = = = =	= = = = = = = = = =	= = = = = = = = = = =
;          Parse an	item string an
;          build item record.
;
;   IN:    strg_ptr	= pointer to item string.
;          itemptr = pointer to item record.
;          x = zero	to just parse string, nonzero to parse and build record.
;
;  OUT:    strg_ptr	= same as in.
;          itemptr = next item space.
;          x = same	as in.
; = = = = = = = = =	= = = = = = = = = =	= = = = = = = = = = =
	ENTRY parse_item
parse_item	jsr parse_strg
;
; ------------ Link	item into item list	-----------------
;
	txy	Just counting?
	beq exit2

;
; ------------ Store item's ID number -------------------
;
	lda <count
	sta [<itemptr]	Store item's ID number.

;
; ------------ Store address of item's string -----------
;
	ldy #ItemName
	lda <strg_ptr	Store pointer to item's text string.
	sta [<itemptr],y
	lda <strg_ptr+2
	iny
	iny
store3	sta [<itemptr],y

;
; ------------ Set item's primary and alternate keyboard equvalents ------
;
	ldy #ItemChar
	lda <command	Both primary and alternate key equvalents.
	sta [<itemptr],y

;
; ------------ Set item's check mark and flag -----------------------------
;
	iny
	iny
	lda <check_mark
	sta [<itemptr],y

	iny
	iny
	lda <flag
	sta [<itemptr],y	Store mark and flag.

	jsr next_item	Get pointer to next	item space.

	ldy #NumOfItems	counter to keep track of the total number of
	lda [<menuptr],y	items in the menu
	inc a
	sta [<menuptr],y

exit2	rts

	ENDP


;===========================================================================
;
;	DisposeMenu
;
;          	Free allocated menu.
;
;   IN:    PUSH:LONG - handle of menu to delete.
;
;===========================================================================
DisposeMenu	PROC

menu	equ input

	jsr startup	Do startup initialization for tool call.

;
; --- Free the menu	record ----------------------------
;
	lda menu+2,s	Pass pointer to allocated block.
	pha
	lda menu+2,s
	pha
	_DisposeHandle	Free block.
	tay	Return result from DisposeHandle.

	brl Epop4bytes

	ENDP


;===========================================================================
;
;	NewMenuBar2
;
;  IN: PUSH:WORD - RefDescriptor, describes what the next parameter is.
;      PUSH:LONG - MenuBarTemplateRef, pointer, handle, or resource ID of template
;      PUSH:LONG - Pointer to window's port or NIL for system menu bar
;
; OUT: LONG - handle to the menu bar record
;
;===========================================================================
NewMenuBar2	PROC

	DefineStack
menuBarPtr	long
theHandle	long
origMenuBarRef	long
count1	word
count2	word
mem_needed	word

OrigB	byte
OrigD	word
RTLAdr1	block 3
RTLAdr2	block 3
menuOwner	long
menuBarRef	long
refDescriptor	word
result	long

zPageSize	equ OrigB-menuBarPtr

	phd
	phb
	phk
	plb

	tsc
	sec
	sbc #zPageSize
	tcs
	tcd	switch direct page into stack

	stz <theHandle
	stz <theHandle+2
	stz <origMenuBarRef
	stz <origMenuBarRef+2
	stz <mem_needed

	pha	space for menu bar handle
	pha
;	lda <menuOwner+2
;	pha
;	lda <menuOwner
;	pha
	pei <menuOwner+2
	pei <menuOwner
	_NewMenuBar	get a new menu bar

	pla	store menu bar hdl in our direct page
	sta <result
	pla
	sta <result+2

	lda <refDescriptor
	asl a
	tax
	jmp (table,x)

table	dc.w pointer
	dc.w handle
	dc.w resourceID

resourceID	lda <menuBarRef	save resource ID so we can use it to release this resource
	sta <origMenuBarRef	later
	lda <menuBarRef+2
	sta <origMenuBarRef+2

	pha	space for result
	pha
	PushWord #rMenuBar
;	lda <menuBarRef+2
;	pha
;	lda <menuBarRef
;	pha
	pei <menuBarRef+2
	pei <menuBarRef
	_CMLoadResource
	pla
	sta <menuBarRef
	pla
	sta <menuBarRef+2

handle	lda <menuBarRef
	sta <theHandle
	lda <menuBarRef+2
	sta <theHandle+2

	ldy #4
	lda [<theHandle],y
	ora #$8000	lock the handle and dereference it
	sta [<theHandle],y
	dey
	dey
	lda [<theHandle],y
	sta <menuBarRef+2
	lda [<theHandle]
	sta <menuBarRef

pointer	ldy #resMenuBarFlag
	lda [<menuBarRef],y
	and #FIRST_TWO_BITS
	clc
	rol a	move carry into bit 0
	rol a	move the last two bits into the first two bits
	rol a	now a-reg is in correct format for a verb
	sta <refDescriptor

	ldy #MenuRef1

nextMenu	phy
	jsr getNextMenuRef
	bcs noMore
	lda <mem_needed
	clc
	adc #4
	sta <mem_needed
	pla
	clc
	adc #4
	tay
	bra nextMenu

noMore	ply

	pha	;space for result
	pha
;	lda <result+2	;we need to increase the size of the handle returned
;	pha	;from the NewMenuBar call to insert our menu
;	lda <result	;record handles
;	pha
	pei <result+2
	pei <result
	_GetHandleSize
	pla

	clc
	adc <mem_needed
	pha
;	lda <result+2
;	pha
;	lda <result
;	pha
	pei <result+2
	pei <result
	_SetHandleSize

	ldy #4	;lock and deref this our newly sized handle
	lda [<result],y
	ora #$8000
	sta [<result],y
	dey
	dey
	lda [<result],y
	sta <menuBarPtr+2
	lda [<result]
	sta <menuBarPtr

	lda #MenuRef1	;get the first menu in the menu bar
	sta <count1	;keeps track of where we are in the menu bar record
	lda #BARSIZE
	sta <count2

getAnotherMenu	ldy <count1
	jsr getNextMenuRef
	bcs noMoreMenus

	pha	;space for handle to menu record
	pha
	ldy <refDescriptor
	phy
	pha	;MenuTemplateRef
	phx
	_NewMenu2	;was macro 16-Jan-91 DAL
	ldy <count2	;Store menu handle into our menu bar record
	pla
	sta [<menuBarPtr],y
	iny
	iny
	pla
	sta [<menuBarPtr],y
	iny
	iny
	sty <count2
	lda <count1
	clc
	adc #4
	sta <count1
	brl getAnotherMenu

noMoreMenus	ldy <count2	;terminator for menu bar record
	lda #0
	sta [<menuBarPtr],y
	iny
	iny
	sta [<menuBarPtr],y

	lda <theHandle+1
	beq exit

	ldy #4
	lda [<result],y	unlock the menu bar handle that we're passing back to caller
	and #$7FFF
	sta [<result],y

	lda [<theHandle],y	unlock the menu bar handle to the resource menu bar
	and #$7FFF
	sta [<theHandle],y

	lda <origMenuBarRef
	bne releaseMenuBarRef
	lda <origMenuBarRef+2
	beq exit

releaseMenuBarRef	PushWord #rMenuBar
;	lda <origMenuBarRef+2
;	pha
;	lda <origMenuBarRef
;	pha
	pei <origMenuBarRef+2
	pei <origMenuBarRef
	_CMReleaseResource

exit	tsc
	clc
	adc #zPageSize
	tcs

	brl pop10bytes

;=======================================================
;
; 	getNextMenuRef
;
; IN: y-reg contains the index into the menu bar record
;
;=======================================================
 	ENTRY getNextMenuRef
getNextMenuRef
	lda [<menuBarRef],y
	tax
	iny
	iny
	ora [<menuBarRef],y
	beq terminate
	lda [<menuBarRef],y

	clc
	rts

terminate	sec
	rts

	ENDP

;===========================================================================
;
;	NewMenuBar
;
;        	Allocate and initialize a menu bar.
;
;   IN:    PUSH:LONG - pointer to window's port that will own menu bar,
;	   zero for system menu bar.
;
;  OUT:    LONG - Handle of menu, zero if error.
;
;===========================================================================
NewMenuBar	PROC

owner	equ input
result	equ owner+4

	jsr startup	Do startup initialization for tool call.

	lda #BARSIZE+4	Number of bytes to allocate.
	jsr make_block	Allocate memory.
	sta result,s	Return handle.
	sta <menuhand	Put handle here and	leave barhand alone.
	txa
	sta result+2,s
	sta <menuhand+2

	jsr pushdefmenu	Pass pointer to source.
	pei <menuhand+2	Pass handle of destination.
	pei <menuhand
	pea 0	Pass number of bytes to move.
	pea BARSIZE+4
	_PtrToHand	Move source into destination.

;
; --- Set menu bar's port to use -------------------------------------
;
	jsr derefMenuHand	<menuptr = (<menuhand)

	lda <screenMode
	bne In640	Default already set to 10, so only change if in 320.

	ldy #CtlFlag+1
	lda [<menuPtr],y
	and #$FF80	Clear current starting position.
	ora #5	Set new starting position to 5 for 320 mode.
	sta [<menuPtr],y

In640	lda #menuColor	Compute address of default color table.
	jsr pushData
	ldy #CtlColor	Set default color table pointer.
	pla
	sta [<menuPtr],y
	iny
	iny
	pla
	sta [<menuPtr],y

	lda owner+2,s
	ora owner,s
	beq useSystem	Already set?

	lda owner+2,s
	ora #$8000	Set 'not system menu bar' flag.
	bra store1

useSystem	jsr pushport	Set system port as owner.
	pla
	sta owner+2,s
	pla
store1	sta owner+2,s

	ldy #CtlOwner	Assign owner.
	lda owner,s
	sta [<menuptr],y
	iny
	iny
	lda owner+2,s
	sta [<menuptr],y
	bmi exit	System menu bar?  If not exit.

;
; --- See if system	menu bar should have fall down menus -----
;
	lda #10	Number of bytes to allocate.
	jsr make_block	Allocate memory.
	phx	Save handle.
	pha
	sta <work
	stx <work+2

	pea 2	Get message.
	pea 4	Message type.
	phx	Pass handle to store message.
	pha
	_MessageCenter
	bcs noMessage

***	ldy $2	;*** bad! changed to:
	ldy #2	;19-Sep-90 DAL
	lda [<work],y
	tay
	lda [<work]
	sta <work
	sty <work+2

	jsr derefMenuHand	<menuptr = (<menuhand)

	ldy #6	Get fall down area.
	lda [<work],y
	ldy #CtlValue	Set fall down area.
	sta [<menuptr],y

noMessage	_DisposeHandle	Free message handle.

exit	brl pop4bytes

	ENDP


;===========================================================================
;
;	Make_Block
;
;          	Allocate a block of memory.
;
;   IN:    a = number of bytes to allocate.
;
;  OUT:    a = low word of handle.
;          x = high	word of handle.
;
;===========================================================================
make_block	PROC

	ldy <MyID	Pass ID.
	ldx #0	Pass attributes.
	brl allocate3

	ENDP


;===========================================================================
;
;	DrawMenuBar
;
;        	Draw Current Menu Bar
;
;   IN:    Nothing.
;  OUT:    Nothing.
;
;===========================================================================
DrawMenuBar	PROC

	jsr startup	Do startup initialization for tool call.
	jsr lockMenuBar	<barPtr = (<barHand), locked.
	beq exit2	Is there a current menu bar?

	ldy #ctlFlag
	lda [<barptr],y
	and #$0080	Check if the menu bar is visible
	bne exit2

	jsr to_myport	Switch to Menu Manager's port.
	jsr getcolor	Get menu bar's color table pointer.

;
; --- Draw menu bar's box ------------------------
;
	lda <outlineclr
	jsr setoutline

	pei <vert_pen
	pea 1 ;
	_SetPenSize

	ldy <norcolor	Pass color in Y.
	ldx <barptr+2	Pass address of RECT in A and X.
	lda <barptr
	clc
	adc #CtlRect
	bcc ok1
	inx

ok1	jsr drawrect	Draw a blank menu bar (frame and inside).

;
; --- Print Titles ------------------
;
	jsr getmfirst	Get pointer to first menu.
	beq exit	Are there any menus?

lop1	pea 0	Draw title normal.
	lda [<menuptr]
	pha	Pass Menu's ID.
	_HiliteMenu	Draw menu's title.

	jsr lockMenuBar	<barPtr = (<barHand), locked.
	jsr next_menu	Get pointer to next	menu.
	bne lop1

exit	jsr to_uport	Restore caller's port.
	jsr unlockMenuBar	Leave menu bar and menus unlocked.

exit2	brl pop0bytes	no error

	ENDP


;===========================================================================
;
;	HideMenuBar
;
;	This call takes the system menubar and hides it by adding
;	the menubar rect back to the desktop region. The invisible bit
; 	in the menubar flag is set so that any subsequent DrawMenuBar
;	or HiliteMenu calls will check this bit before doing anything.
;
;  IN: nothing
; OUT: current menu bar is set to the system menubar
;
;===========================================================================
HideMenuBar	PROC

	jsr startup

	lda <sysMenu+1	First check if there is a system menu bar
	beq exit1

	jsr sys_current	<barHand = <sysMen. Current = system
	jsr lockmenubar

	ldy #CtlFlag
	lda [<barptr],y
	tax
	and #$0080	First check if menu bar is already invisible
	bne ItsInvisible

	txa
	ora #$0080	Set invisible flag for menu bar
	sta [<barptr],y

	lda #1	Set Desktop operation for "toDesk", since we are hiding the
	sta <temp	menu bar we need to add the rect back to the desktop.
	jsr AddorSubRegion

	pha	Reset all the SCBs which were initially altered
	_GetMasterSCB	by InitPalette.
;;;	_SetAllSCBs
;*** New way 26-Aug-91 DAL -- only set SCBs 2 through 9
;	pla	;A=SCB value
;	ldx #7	;X counts from 7 down to 0, for SCBs 9 to 2
;@setNextSCB	phx
;	pha	;preserve A and X
;	inx
;	inx
;	phx
;	pha	;push SetSCB parameters
;	_SetSCB
;	pla
;	plx
;	dex
;	bpl @setNextSCB
;*** end 26-Aug-91 DAL
*** Newer way 19-Sep-91 DAL -- set SCBs 0..Height-1
	ldy #$000C	;offset to bottom om menu bar rect
	lda [<barPtr],y
	dec a
	tax
	pla	;A = SCB value
@setNextSCB	phx
	pha	;preserve A and X
	phx
	pha	;push SetSCB parameters
	_SetSCB
	pla
	plx
	dex
	bpl @setNextSCB
*** end 19-Sep-91 DAL

	ldx <barptr+2
	lda <barptr	; refresh only the menu bar that got hidden
	clc
	adc #CtlRect
	bcc noCarry
	inx
noCarry	phx
	pha
	_RefreshDesktop

ItsInvisible	jsr unlockmenubar

exit1	brl pop0bytes

	ENDP


;===========================================================================
;
;	ShowMenuBar
;
;	This call shows a hidden system menu bar by subtracting the
;	menu bar rect from the desktop and refreshing the desktop.
;	The system menu bar is made the current menu bar.
;
;===========================================================================
ShowMenuBar	PROC

	jsr startup

	lda <sysMenu+1	First check if there is a system menu bar
	beq exit2

	jsr sys_current	<barHand = <sysMen. Current = system
	jsr lockmenubar

	ldy #ctlFlag
	lda [<barptr],y
	tax
	and #$0080	First check if menu bar is visible already.
	beq ItsVisible

	txa
	and #$FF7F	Set the menu bar to visible.
	sta [<barptr],y

	lda #0
	sta <temp	Set the DeskTop operation to "fromDesk", since we're
	jsr AddorSubRegion	showing the menu bar we need to subtract it from the desktop.

	_DrawMenuBar	Show the menu bar by redrawing it.

	_InitPalette	Reinitialize the SCBs in the menu bar so the apple logo
;		shows up correctly.
ItsVisible	jsr unlockmenubar

exit2	brl pop0bytes

	ENDP

;==================================================
;
; 	AddorSubRegion
;
;  IN: <temp contains the operation for DeskTop call to perform
;      <barptr is set the system menu bar
; OUT: nothing
;
;==================================================
AddorSubRegion	PROC

	pha	First get  a new region that we are going to use
	pha	to add or subtract from the desktop region.
	_NewRgn

	lda 1,s 	Store handle to region on our direct page space for now.
	sta <work
	lda 3,s
	sta <work+2

	lda <barptr	Calculate the pointer to the system menu bar's rectangle.
	clc
	adc #ctlrect
	tax
	lda <barptr+2
	adc #0
	pha
	phx
	_RectRgn	Convert our region to a rectanglar region.

	pei <temp	Add or subtract this region from our desktop, thereby
	pei <work+2	showing or hiding the menu bar.
	pei <work
	_DeskTop
	bcc noerr
	pla
	pla
	pla

noerr	pei <work+2
	pei <work
	_DisposeRgn

	rts

	ENDP

;===========================================================================
;
;	HiliteMenu
;
;        	Print a Title.
;
;   IN:    PUSH:WORD - 0 = normal, 1 = highlighted, bit 15 =1 for invert.
;          PUSH:WORD - Menu ID.
;
;===========================================================================
HiliteMenu	PROC

menunum	equ input
flag	equ menunum+2

	jsr startup	;Do startup initialization for tool call.
	jsr lockMenuBar	;<barPtr = (<barHand), locked.
	beq exit4	;Is there a current menu bar?

	ldy #ctlFlag
	lda [<barptr],y
	and #$0080	;Is the menu bar invisible
	bne exit4	;It's invisible

	lda menunum,s	;ID of menu to hilite.
	jsr getmptr	;Get menu's pointer.
	beq exit3	;Was the menu found?

	jsr to_myport	;Switch to Menu Manager's port.
	_PenNormal

;
; --- Draw title's background -------
;
	ldy #CtlRect+y1
	lda [<barptr],y
	sta <menurect+y1

	ldy #CtlRect+y2
	lda [<barptr],y
	sta <menurect+y2

	ldy #menuFlag	;Check if this menu is a pop-up menu.
	lda [<menuptr],y	;If it is then we don't want to calculate the title's rect
	and #M_POPUP	;like we normally would for a regular menu.
	beq notPopup

	ldy #CtlRect+x1	;We don't do the fudging that titlexstart does.
	lda [<barptr],y	;The pop-up's title rect is calculated just by using the
	sta <menurect+x1	;y1, y2, and x1 coordinates of the control rect and then
;		;calculating x2 by adding the titleWidth to x1.
	ldy #TitleWidth
	clc
	adc [<menuptr],y
	sta <menurect+x2

	dec <menurect+y2	Since this is a pop-up control we must account for the
;		bottom drop shadow which is a part of the control rect.
	bra SkipThisShit

notPopup	inc <menurect+y1
	dec <menurect+y2

	lda menunum,s	Find title's starting position.
	jsr titlexstart
	stx <menurect+x1
	sty <menurect+x2

SkipThisShit	lda flag,s	Get hilite/unhilite	flag.
	tax
	bpl skip1	Requesting XOR highliting?

	ldy #MenuFlag	Will menu allow XOR	highliting?
	lda [<menuptr],y
	and #M_NO_XOR	XOR flag set?
	bne skip1

	txa
	and #$7FFF	Don't allow special XOR highlighting.
	tax

skip1	txa	Pass hilite/unhilite flag in A.
	ldx #mDrawTitle
	jsr dispatch

exit2	jsr to_uport	Restore caller's port.
exit3	jsr unlockMenuBar	Leave menu bar and menus unlocked.

exit4	brl pop4bytes	no error

	ENDP


;===========================================================================
;
;	FlashMenuBar
;
;   IN:    None.
;  OUT:    None.
;
;===========================================================================
FlashMenubar	PROC

	jsr startup	Do startup initialization for tool call.
	jsr qdraw	Draw the menu bar with InvertColor.
	jsr qdraw	Redraw the bar with	barColor.

	jsr unlockMenuBar	Leave menu bar and menus unlocked.

	brl pop0bytes	no error


; = = = = = = = = =	= = = = = = = = = = = = = = = =
;        Code optimumzation
; = = = = = = = = =	= = = = = = = = = = = = = = = =
;
qdraw	jsr lockMenuBar	<barPtr = (<barHand), locked.
	beq exit100	Is there a current menu bar?

	jsr getcolor	Get menu bar's color's.
;	                  	work = color table pointer.

	lda <hiliteclr	Swap normal and selected colors.
	sta [<work]

	ldy #2
	lda <norcolor
	sta [<work],y

	_DrawMenubar
exit100	rts

	ENDP


;===========================================================================
;
;	TitleXStart
;
;        	Find title's starting position.
;
;   IN:    a = menu	ID.
;          barptr =	menu bar pointer.
;
;  OUT:    x = x position of title's left side.
;          y = x position of title's right side.
;          menuptr set to menu pointer.
;          a = 0 and equal flag is TRUE	if no menu.
;
;===========================================================================
titlexstart	PROC

pos	equ 1
menunum	equ pos+2

	pha	Save menu ID.

	ldy #CtlFlag+1
	lda [<barptr],y
	and #$007F	Start position of titles,
	clc
	adc <vert_pen	plus width of left side vertical line,
	ldy #CtlRect+x1	plus left side of menu bar,
	adc [<barptr],y
	pha	equal left side of first menu title.

	jsr getmfirst	Get pointer of first menu.
	beq exit	Are there any menus?

lop1	ldy #TitleWidth
	lda pos,s
	tax	Save last position.
	clc
	adc [<menuptr],y
	sta pos,s

	lda [<menuptr]
	cmp menunum,s
	beq exit	Is this the menu?

	jsr next_menu	Next menu.
	bne lop1	Are there any more?
;	                  	Error to fall through.

exit	ply	Right side of title.
	pla	Menu number.

	lda <menuptr	Return error state if any.
	ora <menuptr+2
	rts

	ENDP


;===========================================================================
;
;	GetMFirst
;
;        	Find menu pointer.
;
;   IN:    barptr =	menu bar pointer.
;
;  OUT:    BEQ if menu not found.
;          BNE if menu found, <menuPtr = pointer to menu record.
;
;===========================================================================
getmfirst	PROC

	lda #0	Find first menu.

;================================================================
;	GetMPtr
;
;   IN:    a = menu ID number.
;
;================================================================
	ENTRY getmptr
getmptr	tax
	beq ok1

	ldx #3	Find given ID.

ok1	jsr getmhand	Get handle of menu.
	brl derefMenuHand	<menuptr = (<menuhand).


; = = = = = = = = =	= = = = = = = = = =	= = = = = = = = = = = = =
;          Find menu handle
;
;   IN:    a = menu's ID.
;          x = search flag:
;                0 = handle of first menu in list.
;                1 = handle of last menu in list.
;                2 = handle of menu before given menu.
;                3 = handle of given menu.
;
;  OUT:    <menuhand = handle of menu.
;
; = = = = = = = = =	= = = = = = = = = =	= = = = = = = = = = = = =
	ENTRY getmhand
getmhand

look_for	equ 1
id	equ look_for+2

	pha	Save ID to search for.
	phx	Save search flag.

	lda #MenuList	Start with first menu in menu list.
	sta <menu_cnt
	bra enter100

lop100	lda look_for,s	Is the first menu wanted?
	beq exit100

	lda [<menuptr]	Get menu's ID.
	cmp id,s	Match?
	beq gotit100

enter100	jsr next_menu	Get handle of menu from menu list.
	bne lop100

gotit100	lda look_for,s
	beq exit100

	cmp #3
	beq exit100

	dey	Backup one menu handle.
	dey
	dey
	dey
	cpy #MenuList	Did we go too far?
	bcc exit100

	sty <menu_cnt
	brl next_menu	Get handle of menu from menu list.

exit100	pla	Fix stack.
	pla
	rts

	ENDP


;===========================================================================
;
;	SetCurrentBar
;
;          	Make last parameter passed the current menu bar.
;
;   IN:    Last parameter passed = menu	bar handle.
;
;  OUT:    <barHand	= last parameter passed.
;
;===========================================================================
setCurrentBar	PROC

	lda input+2,s	Get menu bar pointer.
	sta <barhand
	lda input+4,s
	sta <barhand+2
	ora <barhand	Menu bar passed?
	bne exit

	ENTRY sys_current
sys_current
	lda <sysmenu	Caller wants the system bar.
	sta <barhand
	lda <sysmenu+2
	sta <barhand+2

exit	rts

	ENDP


;===========================================================================
;
;	LockMenuBar
;
;          	Lock current menu bar & every menu.
;
;   IN:    <barHand	= handle of current	menu bar.
;
;  OUT:    BEQ if no current menu bar.
;          BNE if <barPtr = (<barHand).
;                 <barHand = locked.
;                 Every menu in menu bar is locked.
;
;===========================================================================
lockMenuBar	PROC

	lda <barHand+1	Is there a menu bar?
	beq exit

	ldy #4	Lock menu bar.
	lda [<barHand],y
	ora #$8000
	sta [<barHand],y

	dey	Dereference menu bar.
	dey
	lda [<barHand],y
	sta <barPtr+2
	lda [<barHand]
	sta <barPtr

	pei <menu_cnt	Save.
	pei <menuhand+2
	pei <menuhand

	lda #MenuList	Start with first menu in menu list.
	sta <menu_cnt
	bra enter1

lop1	jsr lockMenuHand	<menuhand = locked.

enter1	jsr next_menu	Get handle of menu from menu list.
	bne lop1

	pla	Restore.
	sta <menuhand
	pla
	sta <menuhand+2
	pla
	sta <menu_cnt

	lda <barHand+1	Set BNE flag.
exit	rts

	ENDP


;===========================================================================
;
;	UnlockMenuBar
;
;          	Unlock current menu bar & every menu.
;
;   IN:    <barHand	= handle of current	menu bar.
;
;  OUT:    <barHand	= locked.
;          Every menu in menu bar is unlocked.
;
;===========================================================================
unlockMenuBar	PROC

	lda <barHand+1	Is there a menu bar?
	beq exit

	pei <menu_cnt	Save.
	pei <menuhand+2
	pei <menuhand

	lda #MenuList	Start with first menu in menu list.
	sta <menu_cnt
	bra enter1

lop1	jsr unlockMenuHand	<menuhand = unlocked.

enter1	jsr next_menu	Get handle of menu from menu list.
	bne lop1

	pla	Restore.
	sta <menuhand
	pla
	sta <menuhand+2
	pla
	sta <menu_cnt

	ldy #4	Unlock menu bar.
	lda [<barHand],y
	and #$7FFF
	sta [<barHand],y

exit	rts

	ENDP


;===========================================================================
;
;	LockMenuHand
;
;          	Lock <menuhand.
;
;   IN:    <menuhand = handle.
;
;  OUT:    <menuhand = locked.
;
;===========================================================================
lockMenuHand	PROC

	ldy #4
	lda [<menuhand],y	Guess if this is a handle.
	and #$7FFF
	bne exit	Attributes don't look like mine.

	lda [<menuhand],y	Attributes look like a good handle,
	ora #$8000	I'll take a chance and lock it.
	sta [<menuhand],y

exit	rts

	ENDP


;===========================================================================
;
;	UnlockMenuHand
;
;          	Unlock <menuhand.
;
;   IN:    <menuhand = handle.
;
;  OUT:    <menuhand = unlocked.
;
;===========================================================================
unlockMenuHand	PROC

	ldy #4	Unlock the menu.

	lda [<menuhand],y	Guess if this is a handle.
	and #$7FFF
	bne exit	Attributes don't look like mine.

	lda [<menuhand],y
	and #$7FFF
	sta [<menuhand],y
exit	rts

	ENDP


;===========================================================================
;
;	DerefMenuHand
;
;          	Dereference menu handle.
;
;   IN:    <menuhand = handle of menu bar record.
;
;  OUT:    BEQ if <menuHand = 0.
;          BNE if <menuHand is not zero, <menuptr = (<menuhand).
;
;===========================================================================
derefMenuHand	PROC

	ldx <menuhand+1	Is there a menu handle?
	beq store1

	ldy #1
	lda [<menuhand],y	Dereference the handle.
	tax
	lda [<menuhand]

store1	sta <menuPtr
	stx <menuPtr+1
	txa	Set equal flag.
	rts

	ENDP


;===========================================================================
;
;	To_MyPort
;
;          	Switch to Menu Manager' port.
;
;===========================================================================
to_myport	PROC

	ldy #CtlOwner+2	Use current port?
	lda [<barptr],y
	bmi exit

	jsr save_port	Save current port before switching.

	ldy #CtlOwner+2	Switch to menu bar's port.
	lda [<barptr],y
	pha
	dey
	dey
	lda [<barptr],y
	pha
	_SetPort

exit	rts

	ENDP


;===========================================================================
;
;	Save_Port
;
;          	Save current port, if not saved.
;
;===========================================================================
save_port	PROC

	inc <port_nest	Nest Counter.

	lda <old_port	Something already saved?
	ora <old_port+2
	bne exit

	pha	Space for current port handle.
	pha
	_GetPort	Get current port
	pla
	sta <old_port	Save.
	pla
	sta <old_port+2

exit	rts

	ENDP


;===========================================================================
;
;	To_UPort
;
;          	Return original port.
;
;===========================================================================
to_uport	PROC

	lda <old_port	Is there something to restore?
	tay
	ora <old_port+2
	beq exit

	dec <port_nest	Am I done calling myself?
	bne exit

	pei <old_port+2	Restore original port.
	phy
	_SetPort
	stz <old_port	Restore completed, ready for next save.
	stz <old_port+2

exit	rts

	ENDP


;===========================================================================
;
;	GetColor
;
;          	Get menu bar's color table pointer.
;
;   IN:    barptr =	pointer to menu bar.
;
;  OUT:    <unhiliteclr = unhighlighted	color.
;          <hiliteclr = highlight color.
;          <outlineclr = outline color.
;          <work = pointer to menu bar's color table.
;
;===========================================================================
getcolor	PROC
;
; -- Set colors from color table, if there is one ------------
;
	ldy #CtlColor	Get pointer to color table.
	lda [<barptr],y
	sta <work
	iny
	iny
	lda [<barptr],y
	sta <work+2
	ora <work
	bne colorTableOK

	lda #DefColorTable	If CtlColor is zero then use the default color table
	sta <work	in ROM.
	lda #^DefColorTable
	sta <work+2
	bra NotPopUpControl

colorTableOK	ldy #ctlProc+2
	lda [<barptr],y
	bpl NotPopUpControl

	ldy #PopUpCtlRecord.ctlmoreflags
	lda [<barptr],y
	and #$0018	Get ref type for color table
	beq NotPopUpControl

	bit #$0008
	bne ItsAHandleRef

ItsAResource	pha
	pha
	PushWord #$800d		;was rCtlColorTable 17-Sep-90 DAL
;	lda <work+2
;	pha
;	lda <work
;	pha
	pei <work+2
	pei <work
	_CMLoadResource
	pla
	sta <work
	pla
	sta <work+2

ItsAHandleRef	ldy #2
	lda [<work],y
	tax
	lda [<work]
	sta <work
	stx <work+2

NotPopUpControl
	ldy #4	Fetch colors from table.
lop1	lda [<work],y
	tyx
	sta <norcolor,x
	dey
	dey
	bpl lop1

exit	rts

	ENDP

*
* Added 7-Jan-91 DAL
*
MinDelayPrep	proc export
	pha
	pea 0
	pea 0
	_WaitUntil
	pla
	sta >blinkTime
	rts

	export MinMenuDelay
MinMenuDelay	pha
	lda >blinkTime
	pha
	pea MinMenuBlinkTime
	_WaitUntil
	pla
	sta >blinkTime
	rts

blinkTime	dc.w 0

	EndP

;===========================================================================
;
;	TrackMenu2
;
;        	Track user inside pop-up menu bar.
;
;===========================================================================
trackmenu2	PROC

	stz <curselect	set no selection flag to start with
	stz <inactItem	set no inactive item selected flag also

playitAgain	pha
	PushWord #0
	_WaitMouseUp
	pla
	bne keepgoing	if mouse up then we're done

	jsr MinDelayPrep	;added 7-Jan-91 DAL

	lda <blink	number of times to flash item
	asl a	double it for number of on/offs
looper	sta <count
	lda <curselect	item to flash
	beq byebye	look ma! no item to flash

	eor #$8000	flipflop hilite/unhilite bit
	sta <curselect
	ldx #mDrawItem	send draw menu message
	jsr dispatch

	ldy #$3000	time of delay
delay	dey
	bne delay

	jsr MinMenuDelay	; added 7-Jan-91 DAL

	lda <count	next flash
	dec a
	bpl looper	done?
byebye	brl Quit

keepgoing	lda #yrat	get new mouse location
	jsr pushDPage
	_GetMouse

	lda <xrat	is mouse in the pop-up menu
	cmp <menurect+x1
	bcc notinrect
	cmp <menurect+x2
	bcs notinrect
	jsr checkbounds
	bcc ckitems

notinrect	stz <count	re-initialize some flags
	stz <inactItem

	brl redrawtheItem	if so then unhilite it

ckitems	ldx #mChoose	check which item we've stumbled upon
	jsr dispatch

	tay 	save a
	lda <globalFlag 	is help on?
	and #G_HELP
	bne nohelp

	tya	don't allow disabled item selection
	and #$4000	is the item disabled?
	beq nohelp

	ldy #0	if disabled, then it's a no hit

nohelp	tya
	sta <count	store new selection
	stz <inactItem	clear inactive item flag, just in case

	tax	save
	and #$4000	is the item inactive?
	beq redrawtheItem

	stx <inactItem	remember over an inactive item

redrawtheItem	lda <curselect	is the current hilited item number the same
	cmp <count	as the new?
	beq cont_poll

	tax	is there a currently hilited item?
	beq skipit

	and #$7FFF 	pass item number as unhilited
	ldx #mDrawItem
	jsr dispatch

skipit	lda <count	newly hilited item index
	sta <curselect	it is now the currently hilited
	beq cont_poll

	ldx #mDrawItem
	jsr dispatch

cont_poll	jsr checkforScrolling
	brl playitAgain

quit	rts

	ENDP


;            	APPEND MTRACK.ASM
;
; 03/30/87 Dan - Added SpecialRect call	to frame and fill empty menu in one
;                call.  The menu will be drawn via FillRect	and FrameRect if
;                the SpecialRect function or QDAux tool is not available.
;
;===========================================================================
;
;	TrackMenu
;
;        	Track user inside menu bar.
;
;   IN:    barptr =	pointer to locked menu bar.
;          x = 2 if	button started up, 0 if started down.
;          yrat = y	starting position of cursor.
;          xrat = x	starting position of cursor.
;
;  OUT:    a = selection.
;          yrat = selected item's ID, zero if none selected.
;          xrat = selected menu's ID, or dimmed item ID if help is on.
;
;===========================================================================
trackmenu	PROC

	stx <startbutt	Save starting button state.

	jsr to_myport	Switch to Menu Manager's port.

	jsr GetColor
	lda <norcolor	Set the background pattern to background of menus.
	jsr pushcolor	Just in case we have a scrollable colored menu,
	_SetBackPat	calling ScrollRect won't have flicker effect.

	stz <event+what	Clear my event record's event code.
	bra enter1	Check the given position first.

;
; ---------------------------------------------------------------------
; --- Wait for a menu to be selected. ---------------------------------
; ---------------------------------------------------------------------

poll_bar	jsr getMEvent	Get the cursor's current position.

enter1	stz <curselect	Set no selection flag to start with.
	stz <inactItem	Set no inactive item selected flag also.

	lda <event+what	Get button event.
	cmp #MOUSEUP	Has the button been	released?
	bne next1
	brl exit	Button released, return to caller.

next1	cmp #MOUSEDOWN	Has the mouse button gone down?
	bne ok2

	stz <startbutt	Set the global flag	to BUTTON DOWN.

;
; ------- Find out which menu mouse is over ----------------------------
;
ok2	jsr onbar	Check if on menu bar at all.
	bne cont_1	Yes, on menu bar.

	lda <startbutt	Button up?
	beq poll_bar	Continue to watch cursor.
	brl exit	If up and not on bar, then return.

cont_1	jsr getmfirst	Start with the head	of the list.
	beq poll_bar	Are there any menus?

lop1	lda [<menuptr]	Get menu's ID.
	sta <titlenum	Keep menu's ID here.

	jsr titlexstart	Find the left and right sides of title.
	stx <Titlex1	Save left side of title.
	sty <Titlex2	Save right side of title.
	stx <menurect+x1	Menu's left side is same as title's.

	cpy <xrat	Is cursor over this	title?
	bcc nextmenu	I already know we're on the bar,
	cpx <xrat	are we in the same column as
	bcc gotit	the title?

nextmenu	jsr next_menu
	bne lop1	Any more menus?
	beq poll_bar	Try again with updated cursor position.

; ----------------------------------------------------------
; --- Print items into menu --------------------------------
; ----------------------------------------------------------

gotit
***
*** 7-Dec-91 DAL: the G_INITCURSOR bit in MenuGlobal makes MenuSelect call InitCursor
***
	lda <globalFlag
	and #G_INITCURSOR
	beq @noInitCursor
	_InitCursor
@noInitCursor
*** end 7-Dec-91

	jsr pull_down	Draw a blank menu.

;------------------------------------------------------
; --- Poll user for	item selection --------------------
;------------------------------------------------------

poll_menu	lda <event+what
	cmp #MOUSEDOWN	Has button gone down?
	bne next3

	stz <startbutt	Set BUTTON DOWN flag.
	bra ok7

next3	cmp #MOUSEUP
	bne ok7

; ------ Button has	been released ----------------------------------------
;
buttonup	lda <blink	Number of times to flash item.
	asl a	Double it for number of on/offs.
lop8	sta <count

	jsr MinDelayPrep	;7-Jan-91 DAL

	lda <curselect	Item to flash.
	beq quit	Exit if no selection made.

	eor #$8000	FlipFlop hilite/unhilite bit.
	sta <curselect
	ldx #mDrawItem	Send draw menu message.
	jsr dispatch

wait	ldy #$3000	Wait while the user	admires my work.
delay	dey
	bne delay

	jsr MinMenuDelay	;7-Jan-91 DAL

	lda <count	Next flash.
	dec a
	bpl lop8	Done?
quit	brl exit2	Pull up menu and return.

; ------ Check if user is on menu bar, but has left menu's title's -----
;
ok7	jsr getMEvent	Get a mouse event.

	stz <count	Start with cursor not over any item.

	jsr onbar	Is cursor on menubar?
	beq ckmenu	If not, there's nothing to worry about.

	lda <Titlex1	On menubar, still over our title?
	cmp <xrat
	bcs newmenu
	lda <Titlex2
	cmp <xrat
	bcc newmenu

	lda <uparrow	check if we have an up arrow
	beq noUpArrow
	inc <inUpArrow	tells routine CheckForScrolling to scroll up arrrow

noUpArrow	brl redrawitem	Unhilite the hilited item, if one is.

; --------- Try to pull up menu and look for another. ----------------------
;
newmenu	lda <curselect	Is an item hilited?
	beq ok8

	and #$7FFF	Pass item number as	unhilited.
	ldx #mDrawItem
	jsr dispatch	Redraw the item as unhilited.

	stz <curselect	No item selected (for pullup call).

ok8	jsr pullup
	brl enter1	Keep tracking user.

;-----------------------------------------------
;          Hit test	for item on menu.
;-----------------------------------------------
;
; --- Check if cursor is in the menu ------------------------------

ckmenu	lda <xrat
	cmp <menurect+x1	check if pt is within the left and right
	bcc notinrect	boundaries of the menu rectangle
	cmp <menurect+x2
	bcs notinrect
	jsr checkbounds
	bcc ckitems	mouse is inside the menu

notinrect	ldy #menuFlag
	lda [<menuptr],y
	and #AlwaysCallmChoose
	beq @1

	lda <curselect	check if there needs to an item unhighlighted first
	bne @1
	bra ckitems

@1	stz <count	Not over any item.
	stz <inactItem	Not over any inactive item either.

	lda <startbutt	Is button up?
	beq redrawitem	If no, no need to check off menu.
;
; ------- Pull up menu if cursor leaves	menu while button up ------------
;
	jsr pushmrect	Pass pointer to menurect.
	pea $FFF4	Horizontal grace buffer.
	pea $FFF0	Vertical grace buffer.
	_InsetRect	Expand menurect for	grace buffer.

	pha
	jsr pushyrat	Pass pointer to point to check.
	jsr pushmrect	Pass pointer to RECT to check.
	_PtInRect	Check if outside grace buffer.

	jsr pushmrect	Pass pointer to menurect.
	pea 12	Horizontal grace buffer.
	pea 16	Vertical grace buffer.
	_InsetRect	Put menurect back the way it was.

	pla	Non-zero if in, zero if not inside.
	bne redrawitem

	stz <curselect	Off a menu, return no selection.
	bra exit2

; --- Cursor is in the menu, now hit test items ------------------------------
;
ckitems	ldx #mChoose	Ask defProc to hit test items.
	jsr dispatch

	tay	Save A.
	lda <globalFlag	Is help on?
	and #G_HELP
	bne ok3	If on, allow disabled item selection.

	tya	Don't allow disabled item selection.
	and #$4000	Is the item disabled?
	beq ok3	If not, then OK.

	ldy #0	If disabled, then it's a no hit.

ok3	tya
	sta <count	Store new selection.
	stz <inactItem	Clear inactive item	flag, just in case.

	tax	Save.
	and #$4000	Is the item inactive?
	beq redrawitem

	stx <inactItem	Remember over an inactive item.

; --- Item state has changed --------------------------------------------------
;
redrawitem	lda <curselect	Is the current hilited item number
	cmp <count	the same as the new?
	beq cont_poll	State hasn't changed, continue to poll.

; --------- Unhighlight current selection --------
;
	tax
	beq skip25	Is there a currently hilited item?

	and #$7FFF	Pass item number as	unhilited.
	ldx #mDrawItem
	jsr dispatch	Redraw the item as unhilited.

; --------- Highlight new selection --------------
;
skip25	lda <count	Newly hilited item index.
	sta <curselect	It is now the currently hilited.
	beq cont_poll	Is the new state a hilited item?
;	                  	Pass item number in A.

	ldx #mDrawItem
	jsr dispatch	Redraw the new item	as hilited.

cont_poll	jsr checkForScrolling
	brl poll_menu	Continue to poll user.

;-------------------------------------
;          End of track menu.
;-------------------------------------

exit2	jsr pullup	Erase the menu.

;
; --- Return selection ---------------
;
exit	stz <yrat	Selection IDs returned in yrat, xrat.
	stz <xrat	So zero out, no selection, just in case.

	lda <curselect	Was the user over an enabled item when
	beq exit3	the button was released?
	and #$3FFF	Mask off hilite bit,
	sta <curselect	to get just the item number.

	lda <inactItem	Was the user over a	disabled item when
	beq ok1	the button was released?

	and #$3FFF
	sta <curselect	Item number to find	ID for.
	jsr get_ids	Get the menu and item ID numbers.
	sta <xrat	Return the disabled	item ID in high word
	stz <yrat	of TaskData and zero in the low word.
	bra exit3

ok1	jsr get_ids	Selection made, get	ID numbers.
;
exit3	brl to_uport	Restore caller's port.

	ENDP


;===========================================================================
;
;	CheckBounds
;
;  IN:	<menurect = rectangle of current menu pulled down
;	<yrat = current y location of mouse
; OUT:	carry clear if pt in bounds
;	carry set if pt otta bounds
;
;===========================================================================
checkBounds	PROC

	lda <upArrow	;check if there's an up arrow
	beq upperbounds	;0 = no up arrow, 1 = up arrow
	lda <yrat
	bmi WayOttaBounds
	lda <menurect+y1
	clc
	adc <font_h
	cmp <yrat	;check if pt is above or below arrow item
	bcc otherend	;it's below if clear
WayOttaBounds	inc <inUpArrow	;set flag that says mouse is in up arrow
	bra ottaBounds	;its otta bounds so set carry

upperbounds	lda <menurect+y1
	cmp <yrat	;check if pt above or below item #1
	bcs ottaBounds	;its below this item 1

otherend	lda <dwnArrow	;check if there's a down arrow
	beq lowerbounds	;0 = no down arrow, 1 = down arrow
	lda <yrat
	bmi ottabounds
	lda <menurect+y2
	sec
	sbc <font_h	;check if pt above or below the down item
	dec a
	cmp <yrat
	bcs InMenu	;we're in the menu
	inc <inDwnArrow	;set flag that says mouse is in down arrow
	bra ottaBounds

lowerbounds	lda <menurect+y2
	cmp <yrat	;check if pt above or below last item
	bcs InMenu
ottaBounds	sec
	rts

InMenu	clc
	rts

	ENDP


;===========================================================================
;
;	CheckForScrolling
;
;	checks if menu is a SCROLLER, if it is check if mouse
;	in up/down arrows, if it is then S C R O L L  man!
;
;	Flags that are set to give more info on what to do after scrolling:
;	$8000 = get rid of up arrow and redraw first item in menu list
;	$4000 = get rid of down arrow and redraw last item in menu list
;	$2000 = draw up flag
;	$1000 = draw down arrow
;
;	Scrolling Speeds: flags that are set in <count
;	$0000 = fast scrolling
;	$0800 = medium scrolling
;
;   IN:	<inUpArrow = set if in up arrow, therefore scroll
;	<inDwnArrow = set if in down arrow, therefore scroll the other way
;	<menuptr = ptr to current menu record
;	<menurect = rectangle corresponding to item in <count
;	<rect = rectangle that we calculate for _ScrollRect
;
;  OUT:	<uparrow, <dwnarrow, flags accordingly
;
;===========================================================================
checkForScrolling	PROC

	ldy #menuFlag
	lda [<menuptr],y
	and #M_SCROLL
	bne checkmore
	brl noScrolling

;--------------------------------------------------------------------------
;------  Check for up arrow  ----------------------------------------------

checkmore	lda <InUpArrow
	bne scrollup
	brl checkdown

scrollup	stz <inUpArrow	reset flag
	dec <firstVisItem	first visible item in menu decrements by one
	lda <firstVisItem
	sta <count	this is the item that is scrolling into view
	cmp #2	when first item becomes 2 then up arrow disappears and
	bne NotFirstItem1	firstitem then becomes 1

	lda <count
	ora #$8000	set flag that says get rid of up arrow and redraw
	sta <count	first item in list
	dec <firstVisItem

NotFirstItem1	ldy #menuflag	check to see whether this is a regular menu or not
	lda [<menuptr],y
	and #M_POPUP
	beq @111

	lda <menurect+y2
	cmp <saveY2
	beq @111

	clc
	adc <font_h
	sta <menurect+y2
	bra stillRoomInRect

@111	ldy #NumOfItems
	lda [<menuptr],y
	cmp <lastVisItem	if lastVisItem is actual last item in menu then we need dwn arrow
	bne NotLastItem1

	lda <count	this means that the last item in menu is now out of view
	ora #$1000	set flag that says draw down arrow
	sta <count
	dec <lastVisItem	lastVisItem decremented by 2, last item is out of view
NotLastItem1	dec <lastVisItem	and second to last item becomes the down arrow item

stillRoomInRect	jsr setSpeedUp

	ldy <font_h	horizontal scroll distance, scrolling down so it's positive
	bra Scroll_Man


;--------------------------------------------------------------------------
;------  Check for down arrow  --------------------------------------------

CheckDown	lda <InDwnArrow
	bne scrolldown
	brl noScrolling

scrolldown	stz <inDwnArrow	reset flag
	inc <lastVisItem	since we're scrolling up, last vis item is incremented
	lda <lastVisItem
	sta <count	item that is scrolling into view
	inc a
	ldy #NumOfItems	if NumOfItems = totalitems-1 then we've scrolled up as
	cmp [<menuptr],y	much as we can, so bye bye down arrow
	bne NotLastItem2

	lda <count
	ora #$4000	set flag that says redraw last item in menu and get rid
	sta <count	of the down arrow icon
	inc <lastVisItem

NotLastItem2	ldy #menuflag
	lda [<menuptr],y
	and #M_POPUP
	beq notPopUpType2

	lda <menurect+y1
	cmp <saveY1
	beq notPopUpType2

	sec
	sbc <font_h
	sta <menurect+y1
	bra around

notPopUpType2	lda <firstVisItem	if FirstItem = 1 then scrolling up will scroll this item
	cmp #1	out of view, sooo... we need to put an up arrow in
	bne NotFirstItem2

	lda <count	firstitem=1
	ora #$2000	set flag that says draw up arrow
	sta <count
	inc <firstVisItem	increment by two because item1 is scrolled out of view
NotFirstItem2	inc <firstVisItem	and item2 becomes the up arrow therefore firstitem=3

around	jsr setSpeedDwn

	lda <font_h	make it negative because we're scrolling up
	eor #$FFFF
	inc a
	tay	store value to scroll in y-reg

Scroll_Man	lda <menurect+y1	calculate the rectangle to scroll
	ldx <uparrow	our rectangle to scroll is <menurect if there are no
	beq noUp	up/down arrows, if there are subtract them from our
	clc	rect
	adc <font_h
noUp	sta <rect+y1

	lda <menurect+y2
	ldx <dwnArrow
	beq noDown
	sec
	sbc <font_h
noDown	sta <rect+y2

	jsr pushrect
	pea 0	no horizontal movement
	phy	vertical distance to scroll, set up above

	pea 0	nil for region handle
	pea 0

	_ScrollRect	scroll the menu

	inc <specialFlag	flag to tell draw_item to not use xor highlighting
	lda <count	update the item that scrolled out of view
	and #$07FF	mask off high some bits to get just the item to redraw
	ldx #mDrawItem
	jsr dispatch

	lda <count
	and #$F000	check if any special flags were set
	beq NoSpecial

	lda <count
	and #$8000
	bne redrawfirst

	lda <count
	and #$4000
	bne redrawlast
	bra DrawUpOrDown

redrawFirst	lda #1	erase up arrow and draw first item
	stz <upArrow
	bra drawit

redrawlast	ldy #NumOfItems	erase down arrow and draw last item
	lda [<menuptr],y
	stz <dwnArrow

drawit	ldx #mDrawItem
	jsr dispatch

DrawUpOrDown	lda <count
	and #$2000
	beq DrawDown

	inc <uparrow
	jsr DrawUpArrow
	bra NoSpecial

DrawDown	lda <count
	and #$1000
	beq NoSpecial
	inc <dwnarrow
	jsr DrawDwnArrow

NoSpecial	lda <count	see if the slow scroll flag is set
	and #$0800
	beq delayDone	if not then we don't need to run the delay

	pha	get starting tick value
	pha
	_GetTick
	pla	just need low word of tick count
	plx
	sta <scrollCount	put starting tick value on our direct page

getNextTick	pha
	pha
	_GetTick
	pla
	plx
	sec
	sbc <scrollCount
	cmp #20	our delay is 20 ticks or .33 seconds
	bcs delayDone
	bra getNextTick

delayDone	stz <count	set to zero so that
	stz <specialFlag

NoScrolling	rts


;==================================================
;
; SetSpeedUp
;
setSpeedUp	lda <yrat
	bmi fast
	lda <menurect+y1
	clc	the first 5 pixels of up arrow constitutes slow section
	adc #7	check if it's in the slow speed section
	cmp <yrat
	bcs fast
	bra setSlow

;==================================================
;
; SetSpeedDwn
;
setSpeedDwn	lda <menurect+y2
	sec	the first 5 pixels of down arrow constitutes slow section
	sbc #7	check if it's in the slow speed section
	cmp <yrat
	bcc fast
setSlow	lda <count
	ora #$0800	set slow poke flag in count
	sta <count

fast	rts

	ENDP

;===========================================================================
;
;	DrawUpArrow
;
;  IN:	<menurect = rectangle of last item found, need x1, x2 only
;	<rect = rect to be calculated for 1 item in menu list
;
; OUT:	nothing
;
;===========================================================================
DrawUpArrow	PROC

	lda <menurect+y1	calculate the rectangle of first item
	sta <rect+y1	and store it in <rect
	clc
	adc <font_h
	sta <rect+y2
	jsr pushrect	rect of first item in menu

	lda <norcolor	fill in rect will background color of menu
	jsr PushColor
	_FillRect

	pea 4	Transfer forground pixels only.
	_SetTextMode

	lda ScreenMode
	beq ModeIs320

	PushLong #UpArrowLocInfo640
	PushLong #UpArrowBounds640
	bra FinishThisSucker

ModeIs320
	PushLong #UpArrowLocInfo320
	PushLong #UpArrowBounds320
FinishThisSucker

	lda <text_width
	clc	don't wan't any carry to be rotating in on us
	ror a
	clc
	adc <menurect+x1	width to indent before drawing the up arrow, same
	adc <text_width	indentation as when we're drawing an item.
	pha	x coordinate of upper left corner of icon
	lda <menurect+y1
	inc a
	inc a
	pha	y coordinate of upper left corner of icon
	pea $8003
	_PPToPort

	rts

	ENDP


;===========================================================================
;
;	DrawDwnArrow
;
;===========================================================================
DrawDwnArrow	PROC

LocInfoRec	equ work

	lda <menurect+y2	calculate the rectangle for the last item in list
	sta <rect+y2	store result in <rect
	sec
	sbc <font_h
	sta <rect+y1
	jsr pushrect	rect for last item in menu

	lda <norcolor
	jsr PushColor
	_FillRect

	pea 4	Transfer forground pixels only.
	_SetTextMode

	lda ScreenMode
	beq ModeIs320

	PushLong #DownArrowLocInfo640
	PushLong #DownArrowBounds640
	bra FinishThisSucker

ModeIs320
	PushLong #DownArrowLocInfo320
	PushLong #DownArrowBounds320
FinishThisSucker
	lda <text_width
	clc	don't wan't any carry to be rotating in on us
	ror a
	clc
	adc <menurect+x1	amount of space to indent before drawing the down arrow.
	adc <text_width	indentation is same as that used when drawing an item
	pha	X coordinate of upper left corner of destination
	lda <menurect+y2
	sec
	sbc #11
	pha	Y coordinate of upper left corner of destination
	pea $8003
	_PPToPort

	rts

	ENDP

;===========================================================================
;
;	Get_IDs
;
;        	Pack MenuID and ItemID.
;
;   IN:    <menuptr	= pointer to menu.
;          <itemptr	= pointer to item.
;          <curselect = item number.
;
;  OUT:    <yrat = item ID number.
;          <xrat = menu ID number.
;
;===========================================================================
get_ids	PROC

	lda [<menuptr]	Get MenuID.
	sta <xrat

	lda <curselect	Pass item number in	A.
	ldx #mGetItemID
	jsr dispatch
	sta <yrat
	rts

	ENDP


;===========================================================================
;
;	Next_Menu
;
;        	Get next menu pointer.
;
;   IN:    barptr =	pointer to menu bar.
;          menu_cnt	= index to next menu handle in menu list.
;
;  OUT:    menuptr = NextMenu.
;          Equal flag is TRUE if no more menus.
;          menu_cnt	= menu_cnt + 4.
;
;===========================================================================
next_menu	PROC

	ldy <menu_cnt
	lda [<barptr],y
	sta <menuhand
	iny
	iny
	lda [<barptr],y
	sta <menuhand+2
	iny
	iny
	sty <menu_cnt	Store index to next	menu.

	brl derefMenuHand	<menuptr = (<menuhand).

	ENDP


;===========================================================================
;
;	GetMEvent
;
;          	Get mouse event.
;
;  OUT:    event = event record.
;          yrat = event+where+y1 in local.
;          xrat = event+where+x1 in local.
;
;===========================================================================
getMEvent	PROC

	pha	Space for return value.
	pea 6	Accept mouse up and	down events.
	lda #event	Pass pointer to my event record.
	jsr pushDpage
	_GetNextEvent
	pla	Get event flag, but	I don't use it.

	lda <event+where+y1	Convert position of	mouse to local.
	sta <yrat
	lda <event+where+x1
	sta <xrat

	jsr pushyrat
	_GlobalToLocal

	rts

	ENDP

;===========================================================================
;
;	PopUpMenuSelect
;
;        	Handle user interaction with pop-up menu. The bits M_CACHE and M_POPUP
;	must be set in the menu flag. Upon entering these bits are set and
;	restored to there original state when you exit.
;
;   IN:  PUSH:LONG - menuin: handle to menu
;        PUSH:WORD - popupflag: tells us what type of popup you want $0001 = with white space
;        PUSH:WORD - yloc:   top of current selection
;        PUSH:WORD - xloc:   left side of "popped-up" menu
;        PUSH:WORD - itemnum:item ID of current selection
;
;  OUT:  WORD - item selected
;
;===========================================================================
PopUpMenuSelect	PROC

menuin	equ input
popupflag	equ menuin+4
yloc	equ popupflag+2
xloc	equ yloc+2
itemnum	equ xloc+2
return	equ itemnum+2

	import pushPortData
	import popPortData

	jsr startup

	jsr lockmenubar

	jsr saveColor
	jsr GetColor

	lda menuin,s
	sta <menuhand
	lda menuin+2,s
	sta <menuhand+2

	jsr lockmenuhand
	jsr derefmenuhand

	ldy #menuFlag
	lda [<menuptr],y
	pha	Save original menuFlag on the stack
	ora #M_POPUP	Set the bit that says this is a pop-up menu
	and #_M_CACHE	Clear cache bit, pop-up menus cannot be cached
	sta [<menuptr],y

	jsr InitStuff	initialize some zero page equates

	jsr getifirst	get first item in menu
checkNext	beq invalidItem	item not found, so return invalid item error
	inc <currentSel	offset of item in list
	cmp itemnum+2,s	have we found our initial selection?
	beq gotit
	jsr next_item
	bra checkNext

invalidItem	ldy #NumOfItems	make sure the menu is not empty before assigning init. sel
	lda [<menuptr],y	to first item in the menu list
	bne @888
	lda #1
	sta <menurect+x1
	dec a
	sta <menurect+x2
	brl popEmpty
@888	lda #1	If item ID is invalid then I default to the first
	sta <currentSel	item in the menu list.

gotit	ldx #msize	get menu width and height
	jsr dispatch

;=============================================================================
; calculate pop-up rectangle
;
	lda yloc+2,s
	dec a
	sta <menurect+y1	top of menu
	lda xloc+2,s
	sta <menurect+x1	left edge of menu

	ldy #menuwidth
	clc
	adc [<menuptr],y
	sta <menurect+x2	right edge of menu

	ldy #menuheight
	lda [<menuptr],y
	clc
	adc <menurect+y1	bottom of menu
	inc a	make room for drop shadow
	sta <menurect+y2

	lda popupflag+2,s
	and #FType2PopUp
	sta <saveY1

	lda <currentSel	a-reg contains input to adjust rect
	jsr adjustRect	adjust rectangle to reflect current selection

	lda <currentSel	If the current selection is the first item in list then
	cmp #1	top of pop-up can't be adjusted any further.
	beq noAdjustTop

	jsr adjustTop	current port rectangle

noAdjustTop	lda <currentSel	If the current selection is the last item in the menu then
	cmp <lastVisItem	the bottom cannot be adjusted any further.
	beq noAdjustBott
	inc a
	cmp <lastVisItem
	bne @99
	lda <saveY1
	beq noAdjustBott

@99	jsr adjustBottom

noAdjustBott
	lda <portRect+x1
	bne CheckLeftSideFirst

	ldx <portRect+x1
	lda <portRect+x2
	jsr justifyRight	Move menu left if off right
	jsr justifyLeft	Move menu right if off left
	bra around

CheckLeftSideFirst
	ldx <portRect+x1
	lda <portRect+x2
	jsr justifyLeft
	ldx <portRect+x1
	lda <portRect+x2
	jsr justifyRight

around
	lda <saveY1
	beq @222

	jsr doWhiteSpace	user wants the pop-up with the white space

@222	inc <specialFlag	flag that tells pull_down2 to just draw box and shadow
	jsr pushPortData	save grafport vars...
	jsr pull_down2	draw the pop-up box, drop shadow
	dec <specialFlag

	lda <menurect+y1
	inc a
	pha
	lda <menurect+y2
	dec a
	pha

	lda <saveY2
	bne @333

	lda <menurect+y1
	clc
	adc <saveY1
	sta <menurect+y1
	bra saveWhite

@333	lda <menurect+y2
	sec
	sbc <saveY1
	sta <menurect+y2

saveWhite	pla
	sta <saveY2
	pla
	sta <saveY1

	lda <menurect+x1
	clc
	adc <vert_pen
	sta <rect+x1
	lda <menurect+x2
	sec
	sbc <vert_pen
	sta <rect+x2

	jsr NeverMind
	bra SkipPopEmpty
popEmpty	jsr PushPortData
SkipPopEmpty
	jsr trackMenu2	;track the mouse in the menu until a mouse up
	jsr popPortData	;restore this grafport
	lda <curselect	;get user selection and return it on the stack
	beq noSelection
*** 7-Dec-91 DAL -- call get_ids instead of loading [<itemptr] -- for custom pop-up support!
;;;	lda [<itemptr]	;get the ID
	jsr get_ids
*** end 7-Dec-91

noSelection	sta return+2,s

	inc <curselect
	jsr pullup	;pull up the pop-up menu

	ldy #MenuFlag	;Restore the menu flag to its original state.
	pla
	sta [<menuptr],y
	jsr unlockmenuhand

	jsr restoreColor

	jsr unlockmenubar

	brl pop12bytes

	ENDP


;==================================================
;
; doWhiteSpace
;
;  IN: <menuptr = ptr to current menu record
;      <menurect = rectangle of current menu
;
; OUT: <menurect = modified to account for white space
;
;==================================================
doWhiteSpace	PROC

top	equ work	;redefine some direct page equates
bottom	equ top+2

	stz <saveY1

	lda <firstVisItem
;	sec
;	sbc #1	;find out if top was adjusted
	dec a
	sta <top	;if it has then we may need to add white space to bottom

	ldy #NumOfItems
	lda [<menuptr],y
	sec
	sbc <lastVisItem	;find out if bottom was adjusted
	sta <bottom	;if it has then we may need to add white space to the top

	lda <top
	bne @1

	lda <bottom
	beq done	;pop-up fits on the screen

	jsr addToTop
	bra done

@1	lda <bottom
	bne done

	jsr addToBottom

done	rts


;==========================================================
;
	ENTRY addToTop
addToTop
	lda #0
	sta <saveY2

subtractNext	dec <bottom
	lda <bottom
	beq topDone
	lda <menurect+y1
	sec
	sbc <font_h
	bmi topDone
	cmp <portRect+y1
	bcc topDone
	sta <menurect+y1
	lda <saveY1
	clc
	adc <font_h
	sta <saveY1
	bra subtractNext

topDone	rts

;==========================================================
;
	ENTRY addToBottom
addToBottom
	lda #1
	sta <saveY2

addNext	dec <top
	lda <top
	beq bottomDone
	lda <menurect+y2
	clc
	adc <font_h
	cmp <portRect+y2
	beq bottomDone
	bcs bottomDone
	sta <menurect+y2
	lda <saveY1
	clc
	adc <font_h
	sta <saveY1
	bra addNext

bottomDone	rts


	ENDP

;==================================================
;
; SaveColor/RestoreColor
;
;==================================================
saveColor	PROC

xnorcolor	equ work+6	; save previous menu colors
xhiliteclr	equ xnorcolor+2
xoutlineclr	equ xhiliteclr+2

	lda <norcolor
	sta <xnorcolor
	lda <hiliteclr
	sta <xhiliteclr
	lda <outlineclr
	sta <xoutlineclr
	bra done

	ENTRY restoreColor
restoreColor
	lda <xnorcolor
	sta <norcolor
	lda <xhiliteclr
	sta <hiliteclr
	lda <xoutlineclr
	sta <outlineclr

done	rts

	ENDP

; = = = = = = = = =	= = = = = = = = = =	= = = = = = = = = = = = = =
;
;          Init some direct page flags and get our port rect
;
; = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = =
InitStuff	PROC

;
; --- Before calculating if the menus need to be scrolled, we must first find
; --- the intersection between the VisRgn, ClipRgn and PortRect
;
	lda #portRect	;find out what the current port rect is set to
	jsr pushDPage	;so we can make sure the menurect stays
	_GetPortRect	;within these bounds

	pha	;Second source rectangle
	pha
	_GetVisHandle
	pla
	plx
	jsr IntersectRects

	pha
	pha
	_GetClipHandle
	pla
	plx
	jsr IntersectRects

	lda #portRect+y1	;convert the port rect to global coordinates
	jsr pushDPage
	_LocalToGlobal

	lda #portRect+y2
	jsr pushDPage
	_LocalToGlobal

	lda <portRect+y1	;If our port is the apps window and the window is above
	bpl @1	;the screen then make the upper otta bounds 0.
	stz <portRect+y1

@1	lda #ScreenWidth	;If our port is the apps window and the window drops below
	cmp <portRect+y2	;the screen then make the lower otta bounds the screen width.
	bcs @2
	sta <portRect+y2

@2	stz <inUpArrow	;init some flags that say this is a normal menu so far
	stz <inDwnArrow
	stz <upArrow
	stz <dwnArrow
	stz <specialFlag
	stz <currentSel
	stz <saveY1
	stz <saveY2

	stz <firstVisItem	;first visible item is initially 1
	inc <firstVisItem

	ldy #NumOfItems
	lda [<menuptr],y
	sta <lastVisItem	;so far last visible item is last item in the menu list

	ldy #MenuFlag	;set flag telling us this is a normal non-scroller
	lda [<menuptr],y
	and #_M_SCROLL
	sta [<menuptr],y

	rts

;==================================================
;
; 	IntersectRects
;
; A-reg and X-reg contains a handle to a region. This routine takes this
; handle and calculates the ptr to the region's bounding rectangle and stores
; it in <temptr. It then intersects this rect with the rect found in <portRect.
;
;  IN: a = low word of handle to region, x = high word (source rect 1)
;      <portRect contains the rectangle to intersect what's in a and x.
; OUT: <portRect contains the intersection of the two rects
;
;==================================================
	ENTRY IntersectRects
IntersectRects

	sta <temptr
	stx <temptr+2
	ldy #2
	lda [<temptr],y
	tax
	lda [<temptr]
	sta <temptr
	stx <temptr+2

	lda <temptr
	ldx <temptr+2
	clc
	adc #2	Skip pass the length word
	sta <temptr
	bcc NoCarryFromAdd
	inx
	sta <temptr+2

NoCarryFromAdd	pha	Result space for SectRect call.
	lda #portRect 	Source Rectangle 1
	jsr pushDPage
	pei <temptr+2	Source Rectangle 2
	pei <temptr
	lda #portRect	Destination rectangle.
	jsr pushDPage
	_SectRect
	pla

	rts

	ENDP

; = = = = = = = = =	= = = = = = = = = =	= = = = = = = = = = = = = =
;          	AdjustTop
;
;          	Check to see if the menu is too long. If so then
;          	shorten menu until it fits and set flag that says
;	menu is scrollable.
;
;   IN:    	<menurect = current menu rect.
;	<portRect = rectangle of current port rect in global coord.
;
;  OUT:    	<menurect top is chopped off until it can fit in
;          	the boundsRect
;
; = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = =
adjustTop	PROC

adjustIt	lda <currentSel
	cmp <firstVisItem	if firstVisItem = currentSel then we're done adjusting
	bne ok	since we don't want to adjust the top of the menu rect
;		past the top of the pop-up rect
	lda <saveY1
	beq @77

	inc <firstVisItem
	brl setupScroll

@77	lda <menurect+y1
	sec
	sbc <font_h
	sta <menurect+y1
	lda <firstVisItem
	dec a
	cmp #1
	bne @1
	dec <firstVisItem
	brl DoneAdjusting
@1	brl setupScroll

ok	lda <menurect+y1
	bmi pastTop
	cmp <portRect+y1
	bcs topAdjusted

pastTop	clc
	adc <font_h
	sta <menurect+y1
	inc <firstVisItem
	bra adjustIt

topAdjusted	lda <firstVisItem	if firstVisItem is still 1 then no adjusting was done
	cmp #1
	beq DoneAdjusting

	inc <firstVisItem	account for up arrow
setUpScroll	inc <upArrow	set flag that says we have an up arrow

	ldy #menuflag	set flag in menu record that says this menu scrolls
	lda [<menuptr],y
	ora #M_SCROLL
	sta [<menuptr],y

DoneAdjusting	rts

	ENDP


; = = = = = = = = =	= = = = = = = = = =	= = = = = = = = = = = = = =
;          	AdjustBottom
;
;          	Check to see if the menu is too long. If so then
;          	shorten menu until it fits and set flag that says
;	menu is scrollable.
;
;   IN:    	<menurect = current menu rect.
;	<portRect = rectangle of current port rect in global coord.
;
;  OUT:    	<menurect bottom is chopped off until it can fit in
;          	the boundsRect
;
; = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = =
adjustBottom	PROC

	lda <menurect+y2
	cmp <portRect+y2	check if menu falls below bounds rect
;		if it does call -  S C R O L L Man
	bcc NoFancyScrolling

	lda <saveY1	Is this a type 2 popup? (a.k.a. white-space popup)
	bne DecTotalHeight

	lda <lastVisItem
	cmp #4
	bcc NoFancyScrolling

DecTotalHeight	lda <lastVisItem
	cmp <currentSel
	beq alldone2
	cmp #3
	bne @11
	lda <saveY1
	beq alldone

@11	lda <menurect+y2
	cmp <portRect+y2
	bcc alldone
	sec
	sbc <font_h
	sta <menurect+y2	;subtract height of one item at a time
	dec <lastVisItem 	;update last visible item
	bra DecTotalHeight

alldone	dec <lastVisItem	;the down arrow at bottom of menu subtracts one
;		;extra item from our view
	bra setScrollFlag

alldone2	lda <saveY1
	bne alldone
	lda <menurect+y2
	clc
	adc <font_h
	sta <menurect+y2

setScrollFlag	ldy #MenuFlag	;set flag telling us this is going to be a
	lda [<menuptr],y	;scroller
	ora #M_SCROLL
	sta [<menuptr],y

	inc <dwnarrow	;it's scrollable so we need a down arrow

NoFancyScrolling	rts

	ENDP	adjustBottom

;===========================================================================
;
;	AdjustRect
;
;        	Adjust menu rectangle to reflect current selection.
;
;  IN:	<menurect = rectangle to adjust
;	a-reg = current item selected in the pop-up menu
;
; OUT:	<menurect = adjusted
;
;===========================================================================
adjustRect	PROC

	tay	contains the currently selected pop-up item
adjust	dey
	beq adjusted

	lda <menurect+y1	move whole rect up one item at a time
	sec
	sbc <font_h
	sta <menurect+y1

	lda <menurect+y2
	sec
	sbc <font_h
	sta <menurect+y2
	bra adjust

adjusted	rts

	ENDP


;===========================================================================
;
;	MenuSelect
;
;        	Handle user interaction with menu bar.
;
;   IN:  PUSH:LONG - pointer to event record which contains
;	   point where button went down, should	be in MenuBar.
;        PUSH:LONG - MENUBAR handle, or	zero for system bar.
;
;  OUT: Task record	TaskData = Item ID in low word, menu ID in high word.
;	           item ID = 0 if no selection was made.
;
;===========================================================================
MenuSelect	PROC

menuin	equ input
eventptrIn	equ menuin+4

eventptr	equ work

	jsr startup	Do startup initialization for tool call.

	jsr setCurrentBar	<barHand = passed menu bar.
	jsr lockMenuBar	<barPtr = (<barHand), bar & menus locked.
*** lengthened branch 8-Feb-92 DAL
;;;	beq exitMenu2	Is there a current menu bar?
	bne @ok
	brl exitMenu2
@ok
*** end 8-Feb-92

	jsr getevptr	Get event pointer.

	ldy #where	Get point of event.
	lda [<eventptr],y
	sta <yrat
	iny
	iny
	lda [<eventptr],y
	sta <xrat

	jsr to_myport

*** added 8-Feb-92 DAL -- If Top of menu bar >= 150, don't do anything, it's dangerous!
	pea 0	;dummy X value
	ldy #8	;offset to menu bar rect, top
	lda [<barptr],y
	pha	;local-coord top of menu bar
	tsc
	inc a
	pea 0	;high word of point ptr
	pha	;low word of point ptr
	_LocalToGlobal
	pla	;global Y value
	plx	;ignore X value
	cmp #150
	bcs exit
*** end 8-Feb-92

*** TS3 jumps back into ROM at this point, $FD/6BDD (8-Feb-92 DAL)
TS3EntersHere	jsr pushyrat
	_GlobalToLocal

	jsr onbar	Cursor on menu bar?
	beq exit

	ldx #0	Pull down menu flag.
;;;	ldy #what	Was the button down?
;;;	lda [<eventptr],y
	lda [<eventptr]	;optimized 8-Feb-92 DAL
;;;	cmp #1
	dec a	;optimized 8-Feb-92 DAL
	beq watch_menu

	ldy #CtlValue
	lda [<barptr],y
	beq exit
	ldy #CtlRect+y1
	clc
	adc [<barptr],y
	cmp <yrat
	bcs ok

exit	stz <yrat	No selection flag.
	stz <xrat
	bra exitmenu

ok	ldx #2	Fall down menu flag.
watch_menu	jsr trackmenu	Watch the menu.

	ENTRY exitmenu
exitmenu
	jsr getevptr
	ldy #TaskData
	lda <yrat	Item ID.
	sta [<eventptr],y	Return item ID number.
	iny
	iny
	lda <xrat	Menu ID number.
	sta [<eventptr],y	Return Menu ID number.

	jsr to_uport
	jsr unlockMenuBar	Leave menu bar and menus unlocked.

	ENTRY exitMenu2
exitMenu2
	brl pop8bytes	error


; = = = = = = = = =	= = = = = = = = = = = = = = = = =
;        Get event pointer.
; = = = = = = = = =	= = = = = = = = = = = = = = = = =
	ENTRY getevptr
getevptr
	lda eventptrIn+2,s	Get pointer to event record.
	sta <eventptr
	lda eventptrIn+4,s
	sta <eventptr+2

	rts

	ENDP

;===========================================================================
;
;	MenuKey
;
;        	Find item associated with key.
;
;   IN:  PUSH:LONG - pointer to event record which contains
;	   character entered.
;        PUSH:LONG - MENUBAR handle, or	zero for system bar.
;
;  OUT:  Task recrd	TaskData = Item ID in low word, menu ID	in high word.
;	           item ID = 0 if no selection was made.
;
;===========================================================================
MenuKey	PROC

menuin	equ input
eventptrIn	equ menuin+4

eventptr	equ work
key	equ eventptr+4

	jsr startup	Do startup initialization for tool call.
	jsr setCurrentBar	<barHand = passed menu bar.
	jsr lockMenuBar	<barPtr = (<barHand), bar & menus locked.
	beq exitMenu2	Is there a current menu bar?

	jsr getevptr	Get pointer to event record.

	stz <yrat	Clear item found flag.
	stz <xrat	Clear dimmed item selected flag.

	ldy #modif	Get modifier flags.
	lda [<eventptr],y	Check if option key	was down.
	and #$0100
	beq exitmenu

	ldy #message	Get key.
	lda [<eventptr],y	Convert character to what's in record.
	sta <key	Save key.

	lda #ItemChar	Check primary character first.
	sta <work
	jsr ck_chars
	bcs gotit

	inc <work	Check alternate character next.
	jsr ck_chars
	bcc exitmenuSRQ	;was exitmenu 3-Mar-91 DAL

gotit	ldy #ItemFlag	Is item enabled and	visible?
	lda [<itemptr],y
	and #I_ENABLED+I_INVIS
	bne exitmenu	Can only select visible, enabled items.

	jsr get_ids	Get packed MenuId and ItemID.

	pea $8001	Highlight flag, xor	if possible.
	pei <xrat	Pass menu ID number	to highlight.
	_HiliteMenu	Draw menu's title highlighted.

	bra exitmenu

*** ExitMenuSRQ: added 3-Mar-91 DAL so we can call SendRequest after everything else
ExitMenuSRQ	jsr getevptr
	ldy #TaskData
	lda <yrat	Item ID.
	sta [<eventptr],y	Return item ID number.
	iny
	iny
	lda <xrat	Menu ID number.
	sta [<eventptr],y	Return Menu ID number.

	jsr to_uport
	jsr unlockMenuBar	Leave menu bar and menus unlocked.
*** if no item chosen, give SendRequest($0F01) a shot at it
	lda <yrat
	bne @notNIL

*** 25-Jul-91 DAL -- more restrictions on SendRequest($0F01):
***   Desk Manager must be active, CDA-events must be postable (for Installer),
***   and we must be dealing with the system menu bar
	pha
	_DeskStatus
	pla
	beq @notSafe

	pha
	pha
	pea 0
	pea 6	;Event Manager
	_GetWAP
	plx
	pla
	lda >$000022,x
	and #$0400	;check OS Event Mask
	beq @notSafe	;no CDA events allowed?

	lda <sysmenu
	cmp <barhand
	bne @notSafe
	lda <sysmenu+2
	cmp <barhand+2
	bne @notSafe
*** end 25-Jul-91 DAL

	pei <eventptr+2	;14-Mar-91 DAL
	pei <eventptr	;14-Mar-91 DAL
	pea $0F01	;RequestCode for unclaimed MenuKey
	pea $8000	;How=$8000: send to everyone, stop after one (26-Aug-91 DAL)
	lda #0
	pha
	pha	;target=0 (reserved)
	pei <eventptr+2
	pei <eventptr	;data in = event pointer
	pha
	pha	;data out = nil
	_SendRequest
	plx
	stx <eventptr
	plx
	stx <eventptr+2
* If the SendRequest succeeded, make it a null event
	bcs @notTaken
	sta [<eventptr]
@notTaken
@notNIL
@notSafe
*** end of 3-Mar-91 DAL

	brl pop8bytes	;error


; = = = = = = = = =	= = = = = = = = = =	= = = = = = = = = = =
;          Check key against keyboard equivalent.
;
;  IN:     work = index into item record (ItemChar or ItemAltChar).
; = = = = = = = = =	= = = = = = = = = =	= = = = = = = = = = =
ck_chars

;
; --- Check every menu in menu bar ------------------------
;
	jsr getmfirst	Get pointer to first menu in menu list.
	beq errorout	Are there any menus	to check?

;
; ------- Check all	items in this menu -----------------------------
;
lop1	ldy #MenuFlag	Is the menu enabled	and visible?
	lda [<menuptr],y
	and #M_ENABLED+M_INVIS+M_STANDARD
	bne nextmenu	Only select from visible, enabled menus.

	jsr getifirst	itemptr = pointer to first item in menu.
	beq nextmenu	Is there a first item?

lop2	ldy <work	Index to ItemChar or ItemAltChar.
	lda [<itemptr],y
	and #$00FF	Same key, and enabled flags.
	cmp <key
	beq gotit2

	jsr next_item
	bne lop2

nextmenu	jsr next_menu	Get pointer to next	menu.
	bne lop1	Any more menus?

errorout	clc	Set not found flag.
gotit2	rts

	ENDP


;===========================================================================
;
;	OnBar
;
;        	Check if xrat and yrat are in the menu bar.
;
;   IN:    barptr =	pointer to menu bar.
;
;  OUT:    Equal flag is FALSE if point	is not inside RECT.
;          Equal flag is TRUE if point is inside RECT.
;
;===========================================================================
onbar	PROC

ypt	equ 1
xpt	equ ypt+2
box	equ xpt+2

	ldx <barptr+2
	lda <barptr
	clc
	adc #CtlRect
	bcc inside
	inx


; = = = = = = = = =	= = = = = = = = = =	= = = = = = = = = = = =
;        Check if a	point is inside a RECT
;
;   IN:  a = low address of RECT.
;        x = high address of RECT.
;        xrat and yrat = point to check.
;
;  OUT:  Equal flag	is TRUE if point is	not inside RECT.
;        Equal flag	is FALSE if point is inside RECT.
; = = = = = = = = =	= = = = = = = = = =	= = = = = = = = = = = =
	ENTRY inside
inside
	tay

	pha	Space for result.

	pea 0	Pass address of point to check.
	tdc
	clc
	adc #yrat
	pha

	phx	Pass address of RECT to check.
	phy
	_PtInRect
	pla

	rts

	ENDP


;===========================================================================
;
;	MenuRefresh
;
;          	Return redraw area.
;
;   IN:    PUSH:LONG - address of routine that will redraw screen.
;
;  OUT:    None.
;
;===========================================================================
MenuRefresh	PROC

routine	equ 9

	jsr startup	Do startup initialization for tool call.

	lda routine,s
	sta <creamed
	lda routine+2,s
	sta <creamed+2

	brl pop4bytes	no error

	ENDP


;===========================================================================
;
;	SetOutLine
;
;          	Set pen to outline color.
;
;   IN:    a = pattern/color.
;
;  OUT:    Set to a	solid.
;
;===========================================================================
setoutline	PROC

	jsr pushcolor
	_SetPenPat

	rts

	ENDP


;===========================================================================
;
;	Pull_Down
;
;          	Pull down a blank menu.
;
;   IN:    <menuptr	= pointer to menu.
;          <barptr = pointer to menubar.
;          <titlenum = menu's ID number.
;          <Titlex1	= title's left side.
;          <Titlex2	= title's right side.
;          <menurect+x1 = menu's left side.
;
;  OUT:    menurect	= interior coordinates of menu (excluding frame).
;
;===========================================================================
pull_down	PROC

; ------ Highlight title --------------------------------------
;
	pea $8001	;Highlight flag.
	pei <titlenum	;Pass menu's ID.
	_HiliteMenu	;Draw the menu's title highlighted.
	jsr lockMenuBar	;<barPtr = (<barHand), bar & menus locked.
	jsr derefMenuHand	;<menuptr = (<menuhand).

	ldy #NumOfItems	;check if we have an empty menu or not before
	lda [<menuptr],y	;pulling it down
	bne notEmpty

	ldy #menuFlag
	lda [<menuptr],y
	and #M_STANDARD	;if menu is empty make sure that it's not a custom menu
	bne notEmpty	;if custom then it's not really empty because custom menus
	lda #1	;don't use the NumOfItems field anyways
	sta <menurect+x1
	dec a
	sta <menurect+x2
	rts
;
; ------ Compute RECT for menu -----------------------
;
notEmpty	ldy #CtlRect+y2
	lda [<barptr],y
	dec a	;Overlap top of menu with bottom of bar.
	sta <menurect+y1
	ldy #MenuHeight
	clc
	adc [<menuptr],y	;Plus the height for the bottom side.
	inc a	;Plus room for drop shadow.
	sta <menurect+y2

	ldy #MenuWidth
	lda <menurect+x1
	clc
	adc [<menuptr],y	;Plus the width for the right side.
	adc #2	;Plus romm for drop shadow.
	ldx <screenmode	;What resolution are we in?
	beq store1
	adc #2	;Extra drop shadow in 640 mode.
store1	sta <menurect+x2

;
; --- Convert menu RECT to global coordinates ----------------
;
	lda #menurect+y1
	jsr pushDpage
	_LocalToGlobal

	lda #menurect+y2
	jsr pushDpage
	_LocalToGlobal

	jsr initStuff	;Initialize some flags in our direct page
	jsr adjustBottom	;Check if menu extends below the screen

;
; --- Get menu on screen, move left if off right -------------
;
	lda <portRect+x1
	bne DoLeftLast

	ldx <portRect+x1
	lda <portRect+x2
	jsr justifyRight
	jsr justifyLeft
	bra doneJustification

DoLeftLast	ldx <portRect+x1
	lda <portRect+x2
	jsr justifyLeft
	ldx <portRect+x1
	lda <portRect+x2
	jsr justifyRight

doneJustification
;
; --- Get handle of	menu cache -------------------------------
;
pull_down2	PROC

	stz <sav_buff+2	Set 'no cache' flag	just in case.
	stz <sav_buff

	ldy #MenuFlag	Check if there can be a cache.
	lda [<menuptr],y
	and #M_CACHE
	bne cacheOK

	jsr allocateCache
	bcs noCache
	phx	Save allocated cache.
	pha
	sta <sav_buff	Dereference cache.
	stx <sav_buff+2
	ldy #2
	lda [<sav_buff],y
	tay
	lda [<sav_buff]
	sta <sav_buff
	sty <sav_buff+2

	lda #0	Mark cache as BAD (not containing menu).
	sta [<sav_buff]

	pla	Put cache handle into sav_buff.
	sta <sav_buff
	pla
	ora #$8000	Set temp cache flag.
	sta <sav_buff+2
	bra saveScreen

cacheOK	ldy #MenuCache+1
	lda [<menuptr],y
	sta <sav_buff+1
	beq tryCache	Is there a cache?
	dey
	lda [<menuptr],y
	sta <sav_buff

	ldy #1	Has the cache been purged?
	lda [<sav_buff],y
	bne saveScreen

	jsr freeCache	Free purged cache.

tryCache	jsr makeCache	Allocate a new cache for the menu.

	ldy #MenuCache
	lda [<menuptr],y
	sta <sav_buff
	iny
	lda [<menuptr],y
	sta <sav_buff+1
;
; --- Save screen to buffer ---------------------------------

saveScreen	lda <sav_buff+1
	beq noCache	Is there a cache?

	pea 0	Pass no purge flag.
	pei <sav_buff+2	Pass cache handle.
	pei <sav_buff
	_SetPurge	Make cache nonpurgeable for now.

	jsr cache
;
;     a = TRUE to not draw, FALSE to draw menu.
;
noCache	pha	Save draw flag.

	lda #menurect+y1	Convert upper lefty	corner to global.
	jsr pushDpage
	_GlobalToLocal

	lda #menurect+y2	Convert lower right	corner to global.
	jsr pushDpage
	_GlobalToLocal	menurect = now in global coordinates.

	ldy <menurect+x2	Subtract drop shadow from 'menurect'.
	dey
	dey
	lda <screenmode
	beq store3
	dey
	dey

store3	sty <menurect+x2
	dec <menurect+y2	subtract the bottom drop shadow

	pla
	beq drawMenu

	jsr pushmrect	Pass pointer to menurect.
	pei <vert_pen	Width of vertical line.
	pea 1	Height of horizontal lines.
	_InsetRect	Indent menurect.

	rts

;
; --- Menu has to be drawn ---------------------------------------
;
drawMenu	pei <vert_pen	Line width.
	pea 1	Line height.
	_SetPenSize

	lda #menurect	Pass pointer to menu RECT.
	jsr pushDpage
	lda <outlineclr	Compute frame color.
	jsr pushSmear	Push smeared color.
	lda <norcolor	Use menu bar's color.
	jsr pushSmear	Push smeared color.
	_SpecialRect
	bcc skip1	Error?
	cmp #3	Tool or function not found?
	bcs skip1

	pla	Remove inputs to SpecialRect.
	pla
	pla
	pla

;
; --- Draw menu old	way --------------------------------------
;
	inc <menurect+y1

	lda #menurect	Pass pointer to menu RECT.
	jsr pushDpage
	lda #0	Use BarColor.
	jsr pushcolor2	Push pointer to color pattern.
	_FillRect	Draw a blank solid color menu.

	dec <menurect+y1

	lda <outlineclr	Set outline pattern.
	jsr setoutline

	lda #menurect	Frame menu.
	jsr pushDpage
	_FrameRect

; ------- Drop shadow for menu -------------------

skip1	lda <outlineclr
	jsr setoutline

	ldy <menurect+x2
	phy	Pass last point.
	lda <menurect+y1
	clc
	adc #4
	pha

	phy	Set second point.
	ldx <menurect+y2
	phx

	lda <menurect+x1	Set starting point.
	clc
	adc #5
	pha
	phx
	_MoveTo
	_LineTo	Bottom dropshadow.

	lda <vert_pen	Vertical width.
	asl a
	pha	Line width.
	pea 1	Line height.
	_SetPenSize
	_LineTo

	lda #1
	pha
	pha
	_SetPenSize	Reset pen size to normal.

	lda <specialFlag
	beq NeverMind
	rts

	ENTRY NeverMind
NeverMind	jsr pushmrect	Pass pointer to menurect.
	pei <vert_pen	Width of vertical line.
	pea 1	Height of horizontal lines.
	_InsetRect	Indent menurect.

	ldx #mDrawMenu	Send draw menu message.
	brl dispatch

;
; = = = = = = = = =	= = = = = = = = = = = = = = = = = = = = = = = =
;          Push smeared color.
;
;   IN:    a = color in bits 4-7.
;
;  OUT:    Color smeared into all 4 nibbles and pushed on stack.
; = = = = = = = = =	= = = = = = = = = = = = = = = = = = = = = = = =
	ENTRY pushSmearLow
pushSmearLow	asl a
	asl a
	asl a
	asl a
;
pushSmear	plx	Get return address.

	and #$00F0
	pha
	lsr a
	lsr a
	lsr a
	lsr a
	ora 1,s
	sta 1,s
	xba
	ora 1,s
	sta 1,s

	phx	Put return address back.

	rts


; = = = = = = = = =	= = = = = = = = = =	= = = = = = = = = = = = = =
;          If menu is off left side of screen, move it right.
;
;   IN:    a = max right side.
;          x = minimum left side.
;          <menurect = current menu rect.
;
;  OUT:    <menurect moved to left if off max right.
;100= = = = = = = =	= = = = = = = = = =	= = = = = = = = = = = = = =
JustifyLeft	PROC

	clc	(One extra.)
	sbc <menurect+x2	Less the menu's right side.
	bcs exit100	Is the menu off the	right?

	tax	Save amount to move	menu.
	clc
	adc <menurect+x1	Move left side to left.
	sta <menurect+x1
	txa
	clc
	adc <menurect+x2	Move right side to left.
	sta <menurect+x2

exit100	rts

	ENDP

; = = = = = = = = =	= = = = = = = = = =	= = = = = = = = = = = = = =
;          If menu is off right side of screen, move it left.
;
;   IN:    a = max right side.
;          x = minimum left side.
;          <menurect = current menu rect.
;
;  OUT:    <menurect moved to left if off max right.
;100= = = = = = = =	= = = = = = = = = =	= = = = = = = = = = = = = =
JustifyRight	PROC

minX1	equ 1
maxX2	equ minX1+2

	pha
	phx

	lda <menurect+x1	Off left side?
	cmp minX1,s
	bpl exit101

	lda <menurect+x2
	sec
	sbc <menurect+x1
	clc
	adc minX1,s
	sta <menurect+x2

	lda minX1,s
	sta <menurect+x1

exit101	plx	Remove temp stack space.
	pla

	rts

	ENDP

;===========================================================================
;
;	PullUp
;
;          	Erase Menu
;
;   IN:    menurect	= RECT containing menu.
;
;===========================================================================
pullup	PROC

	ldy #NumOfItems	check to see if we have an empty menu
	lda [<menuptr],y
	bne notEmpty	if we don't proceed as normal, else nothing to pull up
	ldy #menuFlag
	lda [<menuptr],y
	and #M_STANDARD	make sure not custom menu since it doesn't use NumOfItems
	bne notEmpty
	brl unHiliteTitle

; --- Try to restore screen ---------------------------
;
notEmpty
;	jsr resetThings	just in case this menu was scrollable we need to restore
;		a few things
	lda <sav_buff+1	Was the screen area	saved to a buffer?
	beq try_wmgr

	jsr uncache

	lda <sav_buff+2	Check if it was a temp cache.
	bpl setPurge

	and #$00FF	Free temp cache.
	pha
	pei <sav_buff
	_DisposeHandle
	bra cktitle

setPurge	pea 3	Pass 'first to purge' flag.
	pei <sav_buff+2	Pass cache handle.
	pei <sav_buff
	_SetPurge	Make cache purgeable.

	jsr resetThings	If this menu is scrollable and it was scrolled then
;		the cache will be disposed of.
	bra cktitle

; --- Ask Window Manager to restore screen ------------
;
try_wmgr	jsr pushmrect	Expand menu RECT to	include frame
	pea $FFFA	and drop shadow.
	pea $FFFA	This makes the RECT	larger than needed
	_InsetRect	but takes less code.

	jsr pushmrect	Pass pointer of RECT to restore.
	_RefreshDesktop	Ask Window Manager to refresh the screen.
;;;The below is an interesting idea, but you can't actually call DrawMenuBar from here (it freaks out), and
;;;the comparison does not seem to be right either.
;*** experimental, added 10-Dec-91 DAL -- draw the menu bar if needed (in case a pop-up overlapped the system menu bar)
;	php
;	pei <temp+2
;	pei <temp
;
;	ldy #2
;	lda [<sysmenu],y
;	sta <temp+2
;	lda [<sysmenu]
;	sta <temp
;
;	ldy #12	;offset to menu bar bottom
;	lda [<temp],y
;	cmp <menurect	;bigger than top of dirty area?
;	beq @fine
;	bcc @fine
;	_DrawMenuBar
;@fine	pla
;	sta <temp
;	pla
;	sta <temp+2
;	plp
;*** end 10-Dec-91
	bcc cktitle	Error if Window Manager not running.

; --- Ask application to restore screen	---------------
;
	lda <creamed	Is there a routine to go to?
	ora <creamed+2
	beq nobody

	lda <creamed	Call application's routine.
	ldx <creamed+1
	jsl long_call

; --- Nobody will restore the screen ------------------------------------
;
nobody	pla	Fix stack.
	pla

; --- Unhighlight title if menu was down, but no selection	was made -----
;
cktitle	lda <inactItem	Was the selected item inactive?
	bne ok1	If yes, leave the menu title unhilited.

unHiliteTitle	lda <curselect
	bne exit3

ok1	pea $8000	Normal
	pei <titlenum	Menu number.
	_HiliteMenu
	jsr lockMenuBar	<barPtr = (<barHand), bar & menus locked.
	jsr derefMenuHand	<menuptr = (<menuhand).

	stz <titlenum	No selection made.

exit3	rts

	ENDP

;===========================================================================
;
;	ResetThings
;
;  IN:	<menuptr: ptr to menu record
; OUT:	nothing
;
; If menu was scrollable, we need to reset a few things:
;      The variable <firstVisItem is used to hold the first item visible, if it is zero
;      then nothing has been scrolled and the menu can remain cached if it is not zero
;      then we need to free the cache and redraw the menu the next time.
;
;===========================================================================
ResetThings	PROC

	ldy #menuflag	;first check to see if menu was scrollable
	lda [<menuptr],y
	and #M_SCROLL
	beq ottahere	;it's not so we don't need to do anything

	lda <firstVisItem
	cmp #1
	beq ottahere

	jsr freecache	free cache so that the next time menu is pulled down
;		we can redraw it
ottahere	rts

	ENDP

;
;            APPEND	MDEFPROC.ASM
;
; 03/30/87 Dan - Added SetTextFace to size_menu so width of	menu would take
;                into account special effects applied to item text.  Also,
;                reset text face to plain when done.
;
;===========================================================================
;          Dispatch	menu command.
;
;   IN:    x = message.
;          a = parameter to pass to defProc.
;          menurect	= RECT to pass.
;          yrat = y	point to pass.
;          xrat = x	point to pass.
;          menuhand	= handle of menu.
;          menuptr = pointer to menu.
;
;  OUT:    a = returned value from defProc.
;
;===========================================================================
dispatch	PROC

	sta <param	Save parameter.

	ldy #MenuProc+1	Custom menu?
	lda [<menuptr],y
	bne custom

; --- Call the standard menu defProc ---------------------------------------
;
	txa
	asl a
	tax
	jmp (standards,x)	I have none.

standards	DC.W draw_menu	mDrawMenu  = 0
	DC.W choose_item	mChoose    = 1
	DC.W size_menu	mSize      = 2
	DC.W draw_title	mDrawTitle = 3
	DC.W draw_item	mDrawItem  = 4
	DC.W get_itemID	mGetItemID = 5

;
; --- Call a custom	menu defProc ---------------------------------------
;
custom	cpx #1	Choose command?
	bne ok1

	lda <globalFlag	Is help on?
	and #G_HELP
	bne ok1	If help on, OK to check disabled menu.

	ldy #MenuFlag	Is the menu enabled?
	lda [<menuptr],y
	and #M_ENABLED
	beq ok1	If disabled, no item can be selected.

	lda #0	Return no hit flag.

	rts


ok1	phx	Remember command message.

	pei <menuhand+2	Save.
	pei <menuhand

	pha	Space for result (none used).

	phx	Pass message command.

	pei <menuhand+2	Send handle of menu.
	pei <menuhand

	jsr pushmrect	Pass address of menu's RECT.

	pei <xrat	Pass x coordinate.
	pei <yrat	Pass y coordinate.

	pei <param	Parameter to pass.

	ldy #MenuProc+1
	lda [<menuptr],y
	tax
	dey
	lda [<menuptr],y
	jsl long_call	Call application's defProc.
	pla	Get result.
	plx	Restore menu handle.
	stx <menuhand
	plx
	stx <menuhand+2
	pha	Put result back.
	jsr lockMenuBar	<barPtr = (<barHand), bar & menus locked.
	jsr derefMenuHand	<menuptr = (<menuhand).

	pla	Get return value.

	plx	Get saved command message.
	cpx #mDrawTitle
	bne exit	Was it a draw menu title command?

	tay	Did the defProc draw the title?
	bne exit	If yes, all done.

	brl draw_title	Custom defProc wants default title.

exit	rts

	ENDP


;===========================================================================
;
;      	Long call.
;
;   IN:    x = middle WORD (bits 8-23) of address of destination routine.
;          a = low WORD of address of destination routine.
;
;  OUT:    Calling this routine is the same as:
;
;                jsl   (ax)
;
;          where the low byte in 'a' is	the low byte of the	destination
;          address,	and x = the next 2 bytes of the destination address.
;
;===========================================================================
long_call	PROC

	dec a	Make low word look like a return address.
;	              	!!! High byte of address is not decremented
;	                  	because the program counter doesn't wrap
;	                  	to the next bank!!!!

	phx	Push the high byte.
	tsx	Leave only the high	byte of the address.
	inx
	txs

	pha	Push the low word of the address.

	rtl	Go to the address.
;
;  When the routine	called returns, it
;  will return to the routine that called 'longCall', not here.
;
	ENDP


;===========================================================================
;
;	Draw_Menu
;
;          	Draw the inside of a standard text menu.
;
;   IN:    menuhand	= handle of menu.
;          menuptr = pointer of menu.
;
;===========================================================================
draw_menu	PROC

counter	equ work+4

	pea 4	We need to set this just in case we're not in the
	_SetTextMode	Menu Manager's port.

	lda <lastVisItem	Load number of last visible item in menu
	sec
	sbc <firstVisItem	just in case firstVisItem not equal to 1, which may
	inc a	be the case if this was a pop-up menu
	sta <counter
	beq nothingToDraw

	lda <firstVisItem	Load item number of first visible item in menu
	jsr calcitem	Get pointer to first visible item.
	bne enter2	Are there any items?

	rts	If not, I'm done.


draw_lop	jsr getitemh	Get the height of the item.
	clc
	adc <rect+y1
	sta <rect+y2	Set the item's coordinates.

enter2	lda #0	Draw the item as normal.
	jsr text_guts	Draw the item's text part.

	lda <rect+y2	Bottom of item becomes top of next.
	sta <rect+y1

	jsr next_item	Get the pointer to next item.
	dec <counter
	bne draw_lop	Any more items?

nothingToDraw	lda <upArrow	Do we have to draw an up arrow?
	beq checkNext
	jsr DrawUpArrow

checkNext	lda <dwnArrow	Do we have to draw a down arrow?
	beq noscroll
	jsr DrawDwnArrow

noscroll	clc
	rts

	ENDP


;===========================================================================
;
;	Choose_Item
;
;         	Hit test menu items.
;
;   IN:    menuhand	= handle of menu.
;          menuptr = pointer of menu.
;          yrat = y	coordinate to check.
;          xrat = x	coordinate to check.
;          point is	on the menu.
;          menu is enabled.
;
;  OUT:    a = item	number selected (start with 1), zero if	none hit.
;                bit 15 set for selected.
;                bit 14 set if disabled.
;
;===========================================================================
choose_item	PROC

	lda <firstVisItem
	dec a
	sta <count

lop5	inc <count	Next item.
	lda <count
	jsr calcitem	Get item's RECT and pointer.
	beq not_found	Off end of menu?

	ldx #0	Check if cursor is inside item.
	tdc
	clc
	adc #rect	Pass pointer to 'rect'.
	jsr inside
	beq lop5

;
; --- Cursor over item --------------------------------------------
;
no_scroller	jsr getistrg	Never allow cursor over dividing line.
	lda [<strg_ptr]
	cmp #$2D01
	beq not_found

	lda <count
	ora #$8000	Mark item as selected.
	tax

	ldy #ItemFlag-1	Is item disabled?
	lda [<itemptr],y
	bmi disabled	If yes, mark as selected and disabled.

	ldy #MenuFlag	Is the menu enabled?
	lda [<menuptr],y
	and #M_ENABLED
	beq exit	If not, item is also not disabled.

disabled	txa	Set disabled bit.
	ora #$4000
	rts

not_found	ldx #0	Not over any item.
exit	txa	Return result in A.

	rts

	ENDP


;===========================================================================
;
;	Size_Menu
;
;          	Compute the default size of the menu.
;
;   IN:    menuptr = pointer to menu.
;          menuhand	= handle of menu.
;          menuWidth = zero to set default width.
;          menuHeight = zero to set default height.
;
;  OUT:    menuWidth = default width if	it was zero.
;          menuHeight = default height if it was zero.
;
;===========================================================================
size_menu	PROC

	stz <rect+y2	Height accumulator.
	stz <rect+x2	Width accumulator.

; --- Set every item's height, max width, and menu's height	-----
;
	jsr getifirst	Get pointer to first item.
	beq exit	Are there any items?

; ------- Find item's width --------------------
;
lop1	jsr FixTextFace


	pha	Space for result.
	jsr getistrg	Get pointer to item's string.
	phx	Pass high word.
	pha	Pass low word.
	_StringWidth	Get string's width.

	jsr GetIconInfo	a-reg contains width of icon
	tax
	beq @NoIcon	If a-reg is zero then there is no icon
	clc
	adc 1,s	Add width of item name and icon width.
	adc #5	Add in some additional slop for spacing between icon.
	sta 1,s	Put result back on the stack.
@NoIcon
	lda <text_width	Add room for the check mark.
	clc
	adc <text_width
	adc <text_width
	tax
	ldy #ItemChar
	lda [<itemptr],y
	and #$00FF
	beq ok34
	lda <text_width
	clc	Now add space for the keyboard equivalent, the apple key
	ror a	and a chacracter, plus one extra for slop
	clc
	adc <text_width
	adc <text_width	1 1/2 for check mark, 2 for cmd-key-equiv,2 for space
	adc <text_width
	adc <text_width
	adc <text_width
	tax
ok34	txa
	clc
	adc 1,s
	plx	Pull in x just to fix stack, a = value.

; ------- Keep the width of the widest item ----------------
;
	cmp <rect+x2	Is this the longest	item?
	bcc do_height
	sta <rect+x2	Save the longest width.

; ------- Accumulate item height ----------------------------
;
do_height	jsr getitemh	Get the item's height.
	clc	Keep a running height total.
	adc <rect+y2
	sta <rect+y2

; ------- Next item	--------------------------------------------
;
	jsr next_item
	bne lop1	Any more items?

; --- Set the default values -----------------------------------
;
	ldy #MenuWidth
	lda [<menuptr],y	Was menu's width given?
	bne skip1

	lda <rect+x2	Set menu's width.
	sta [<menuptr],y	Store the menu's width.

skip1	iny
	iny
	lda [<menuptr],y	Was the menu's height given.
	bne exit

	lda <rect+y2	Set menu's height.
	inc a
	inc a

store	sta [<menuptr],y	Store the menu's height.

exit	jsr ClearTextFace 	Plain text.

	rts

	ENDP


;===========================================================================
;
;	Draw_Title
;
;          	Draw menu title.
;
;   IN:    <barPtr = pointer to locked menu bar.
;          <menurect = title's enclosing rectangle.
;          <menuhand = handle of menu.
;          <menuptr	= pointer to menu.
;          <param =	 0 = normal, 1 = highlighted, bit 15 =1	for invert.
;
;===========================================================================
draw_title	PROC

sav_patt	equ 1

	pha	Space for save pattern.

	jsr getcolor	Get menu bar's colors.

	jsr ClearTextFace

	jsr pushmrect	Common need.
;
;
; --- Special case XOR hiliting ---------------------------------
;
	lda <param	Did caller ask for invert?
	bpl do_fill

	_InvertRect	Special case XOR.
	pla	All done, get rid of temp space.

	rts

;
; --- Color replace	drawing --------------------------------------
;
do_fill	ldy <norcolor	Normal color.

	lda <param	Hilite or Unhilite?
	beq ok78

	ldy <hiliteclr	Inverted color.

ok78	tya
	sta sav_patt+4,s	Save the color used	for background.
	jsr pushcolor
	_FillRect

;
; ------ Draw title	---------------------------------------------------
;
	jsr getrMenuTitle
	sta <strg_ptr
	stx <strg_ptr+2

	lda [<strg_ptr]
	cmp #$FF01	Special color apple	logo?
	beq doAppleLogo
	cmp #$4001
	bne ok30

;
; ---------- Draw Apple Logo --------------------------------------------
;
doAppleLogo	lda sav_patt,s	Get the background pattern.
	jsr get_apple	Put the Apple logo in 'image'.

	lda #imageInfo	Pass pointer to source LocInfo.
	jsr pushData
	lda #clip100	Pass pointer to source RECT.
	jsr pushData
	lda <menurect+x1
	clc
	adc #4
	pha	Pass destination X.
	ldy #CtlRect+y2
	lda [<barptr],y
	sec
	sbc #8	Height of apple logo.
	sbc <descent	System font's descent.
	pha	Pass destination Y.
	pea 0	Pass mode, copy.
	_PPToPort

	bra ck_dim

;
; ---------- Print Title string ------------------------------------------
;
ok30	pha
	_GetForeColor

	lda sav_patt+2,s
	and #$000F	Smear foreground color for text.
	jsr pushSmearLow	Push smeared color
	_SetForeColor	Set text color.

	pha	Save original text mode.
	_GetTextMode

	pea 4	Transfer forground	pixels only.
	_SetTextMode

	ldy #CtlRect+y2
	lda [<barptr],y	I want all titles on same line.
	sec
	sbc <descent
	tay	Y position to print	title.

	ldx <menurect+x1	X position to print.

	jsr printstrg	Print menu's title.


;
; If the port is the menu manager's port, don't bother restoring the text mode
; and fore color.
;
; We only did this cause Word Perfect begged.  (They also admitted how ashamed
; they were and promised to never do it again.)
;
	pha	; get the current port
	pha
	_GetPort
	pla
	plx

	sec
	sbc #port
	bcs @1
	dex
@1
	cmp <data
	bne @NotSame
	cpx <Data+2
	bne @NotSame

	pla	; they are the same so clear off text mode and fore color
	pla
	bra @AllDone	; fini

@NotSame		; different port so run old code.

	_SetTextMode	restore original text mode
	_SetForeColor

@AllDone
;
;
; --------- Dim Title ---------------------------------------------------
;
ck_dim	ldy #MenuFlag
	lda [<menuptr],y
	and #M_ENABLED	Disabled?
	beq exit

	pea dimmed>>16
	pea dimmed
	_SetPenMask

	jsr pushmrect
	lda sav_patt+4,s
	jsr pushcolor
	_FillRect

	pea nor_mask>>16
	pea nor_mask
	_SetPenMask

exit	pla	Get rid of sav_patt.

	rts

	ENDP


;===========================================================================
;
;	Draw_Item
;
;          	Draw a standard text menu item.
;
;   IN:  param = bits 0-13 = item number to draw.
;                bit 14 = 1 if item is dimmed.
;                bit 15 = 1 if item should be hilited.
;        menuptr = pointer to menu.
;
;  OUT:  itemptr = pointer to item.
;
;===========================================================================
draw_item	PROC

dflag	equ 1

;
; --- Do setups ------------------------------------
;
	ldx #0	Normal flag.
	lda <param
	bpl do_normal
	inx	Hilite flag.

do_normal	phx	Save draw flag.
	and #$3FFF	Clear hilite and dimmed bits.

	jsr calcitem	Get item pointer and set 'rect'.

;
; --- Draw item's background -----------------------
;
	jsr pushrect	Common need.
	lda <specialFlag	Flag setup by routine checkForScrolling, so that
	bne dont_xor	we just don't do an invertRect for this item
;
; ------ Special case XOR highlight ----------------
;
	lda <param	Is item dimmed?
	and #$4000
	beq ok2

	pea 2	XOR
	_SetPenMode

	pea dimmed>>16
	pea dimmed
	_SetPenMask

	pea 15	Solid ($FFFF) pattern.
	_SetSolidPenPat

	_FrameRect
	_PenNormal
	pla

	rts


ok2	ldy #ItemFlag	Special case XOR flag set?
	lda [<itemptr],y
	and #I_NO_XOR
	beq dont_xor

	_InvertRect	Invert the item.

	pla	Get rid of state flag.

	rts

;
; ------ Set up for	text item background -----------
;
dont_xor	ldy <norcolor	Find background color of item.
	lda dflag+4,s
	beq ok1
	ldy <hiliteclr
ok1	tya	Color of background	to use if text.
	jsr pushcolor	Push pointer to color pattern.
	_FillRect	Fill item's background color.

;
; --- Draw guts of item -------------------------------------
;
	pla	Get rid of state flag (needed in A).
	brl text_guts	Draw text item's guts, and exit.

	ENDP


;===========================================================================
;
;	Ck_Disable
;
;          	Disable the item.
;
;   IN:    itemptr = pointer to item.
;          barptr =	menu bar pointer.
;
;  OUT:    Item disabled if bit set in ItemFlag.
;
;===========================================================================
ck_disable	PROC

	ldy #ItemFlag	Load flag in high byte to set neg flag.
	lda [<itemptr],y
	and #I_ENABLED
	bne mash_it

	ldy #MenuFlag	You're not out of the woods yet,
	lda [<menuptr],y	a item is disabled if its menu is.
	and #M_ENABLED
	beq exit

mash_it	pea dimmed>>16
	pea dimmed
	_SetPenMask

	jsr pushrect	Pass pointer of item's RECT.
;	                  	Disabled can't be selected.
	lda <norcolor	Get menu's background color.
	and #$00FF	Always solid.

	jsr pushcolor	Push pointer to color pattern.
	_FillRect	Fill will be dithered.

	pea nor_mask>>16	Reset drawing mask to normal solid.
	pea nor_mask
	_SetPenMask

exit	rts

	ENDP


;===========================================================================
;
;	Text_Guts
;
;          	Draw text item's guts.
;
;   IN:    a = state of item, 0 = normal, 1 = selected.
;
;===========================================================================
text_guts	PROC

	ldy <norcolor	Normal color.
	tax	Is item selected?
	beq ok1
	ldy <hiliteclr	If yes, use hilite color.
ok1	tya
	and #$000F
	jsr pushSmearLow	Push smeared color
	_SetForeColor	Set color to use for text.

	jsr FixTextFace

;
; --- Dividing line	(not the same thing	as an underline) ---------------
;
	jsr getistrg	Put item's string pointer in 'strg_ptr'.

	lda [<strg_ptr]	Get the first two bytes from the string.
	cmp #$2D01	Dividing line flag?
	bne main_text

	lda <rect+y2	Center line in item.
	sec
	sbc <rect+y1
	lsr a
	clc
	adc <rect+y1
	tay

	lda <rect+x1	Draw from wall to wall.
	ldx <rect+x2
	dex	Not past right side.
	jsr hline	Draw the dividing line and exit.
	brl ck_dim

;
; --- Print item's text ----------------------------------------
;
main_text		; !!!! Font not defined yet !!!!!
	lda <rect+y2
	sec
	sbc <descent
	tay	Y = position to print item.
	phy

	lda <text_width
	clc	don't wan't any carry to be rotating in on us
	ror a
	clc
	adc <rect+x1
	adc <text_width	Ident 1 1/2 times the width of 'W' to make room for mark
	pha	X starting position	of item's text.
	jsr GetIconInfo
	tax
	beq @noIcon
	clc
	adc 1,s	Add in the width of the icon.
	adc #2	Add some extra slop for spacing in between the icon
	sta 1,s
@noIcon	plx
	ply
	jsr printstrg

	jsr DrawItemIcon	If the item has an icon this routine draws it, otherwise
;		it just returns.
;
; --- Mark item -------------------------------------------------
;
	jsr ClearTextFace	Check marks and command key equiv. always appear in plain text

	ldy #ItemCheck
	lda [<itemptr],y
	and #$00FF
	beq ck_command	Is there a mark?

	ldy #mark+1
	sta [<data],y	Put the character in a string.

	jsr pushmark	Push address of 'mark'.
	pla	Pass string's address in 'strg_ptr'.
	sta <strg_ptr
	pla
	sta <strg_ptr+2

	lda <rect+y2
	sec
	sbc <descent
	tay	Y = position to print item.

	ldx <rect+x1	Pass the x starting	position in X.
	inx
	inx

	jsr printstrg	Print the mark.

;
; --- Command character tied to item --------------------
;
ck_command	ldy #ItemChar
	lda [<itemptr],y
	and #$00FF
	beq ck_dim

	ldy #com_key+2
	sta [<data],y	Store character in command string.

	jsr pushcom_key
	pla	Pass address of com_key in 'strg_ptr'.
	sta <strg_ptr
	pla
	sta <strg_ptr+2

	lda <rect+y2
	sec
	sbc <descent
	tay	Y = position to print item.

	lda <rect+x2	Calculate starting position for printing the
	sec	command key equivalents. Allow two for this.
	sbc <text_width
	sbc <text_width
	tax	Pass x starting position.

	jsr printstrg

;
; --- Disable text -------------------------------------
;
ck_dim	jsr ck_disable	Check to disable item.

;
; --- Underline the	item --------------------------------
;
ck_underl	ldy #ItemFlag
	lda [<itemptr],y
	and #I_NOUNDER	Underline flag set?
	beq exit

	lda <rect+x1	Draw underline.
	ldx <rect+x2
	dex
	ldy <rect+y2
	dey
	jsr hline

exit	rts

	ENDP


;===========================================================================
;
; 	DrawItemIcon
;
;  IN: <itemptr pts to item record currently being worked on
;
; OUT: if item has an icon associated with it then we draw it, otherwise
;      we just return
;
;===========================================================================
DrawItemIcon	PROC

	ldy #ItemFlag	First check if item has an itemstruct record
	lda [<ItemPtr],y	associated with it.
	and #I_NEWSTRUCTURE
	beq @noIcon

	jsr GetStruct	First check if the item contains an icon.
	ldy #itemflag2
	lda [<temptr],y
	bpl @noIcon
;
; Setup parameters for PPToPort to draw the icon.
;
	jsr getrItemIcon	x = high word of ref to icon record, a = low word
	phx	a & x contain pointer to icon structure.
	pha

	pea 0	Display mode.

	lda <text_width
	clc	don't wan't any carry to be rotating in on us
	ror a
	clc
	adc <rect+x1
	adc <text_width	Ident 1 1/2 times the width of 'W' to make room for mark
	pha	x coordinate of upper left corner of destination

;
; Center icon in <rect
;
	jsr GetIconInfo
	phx	get height of icon
	lda <rect+y2
	sec
	sbc <rect+y1	calculate the height of the item's rect
	sec
	sbc 1,s	subtract height of icon from height of item rect
	clc
	ror a	take half of that to use to center icon
	sta 1,s
	lda <rect+y1	add this to the y1 coordinate of item rect
	clc	to get the y coordinate of the upper left corner
	adc 1,s	of the destination
	sta 1,s
*** added 22-Jan-91 DAL to make the color right
	lda 3,s
	and #$fffe
	sta 3,s
*** end of 22-Jan-91 DAL
	_DrawIcon
	bcc @noIcon
	cmp #$0002	QDAux not started?
	bne @noIcon

	tsc
	clc	Clean up stack.
	adc #10
	tcs

@noIcon
	rts

	ENDP

;===========================================================================
;
;	Get_ItemID
;
;          	Return item ID.
;
;   IN:    itemptr = pointer to item.
;
;  OUT:    a = item	ID number.
;
;===========================================================================
get_itemID	PROC

	lda [<itemptr]	Return item ID number.

	rts

	ENDP


;===========================================================================
;
;	CalcItem
;
;        	Setup item's parameters
;
;   IN:  a = item index, 0 = first item.
;        menuptr = pointer to menu.
;        menurect =	coordinates of menu.
;
;  OUT:  Equal flag	is TRUE if item not	found.
;        rect = item's coordinates (last item in list if item not found).
;        itemptr = pointer to item (zero if item not found).
;
;===========================================================================
calcitem	PROC

; --- Setups ----------------------------------------------------------
;
	sec
	sbc <firstVisItem	normalize it
	pha	Save item's index.

	jsr getifirst	Get the address of first item.

;
; --- Run down the item list, accumulating item heights, until ---------
; --- given item index counter is exhausted.	   ---------
;

	jsr getStarting	Get starting vertical position
	bra enter20

lop20	ldy #ITEMSIZE	Check ID of next item.
	lda [<itemptr],y	Get item's ID.
	bne ok20	No more items if ID	is zero.
;
; ------- No more items, and matching ID was not found -----------------
;
	jsr getitemh	Get the height for the last item.
	stz <itemptr	Set, off menu flag.
	stz <itemptr+2
	bra exit1

ok20	jsr getitemh	Get height of item,
	clc	and add it to the current top.
	adc <rect+y1
	sta <rect+y1	Store the top of this item.

	jsr next_item

enter20	pla	Index counter.
	dec a
	pha
	bpl lop20	Done.

;
; --- Item found and rect+y1 = top of the item, compute the	rest -----
;
	jsr getitemh	Get height of item,
exit1	clc	and add it to the top,
	adc <rect+y1
	sta <rect+y2	and store it as the	bottom.

	pla	Get rid of index counter.

;
; --- Compute the left and right side of the item -------------------
;
	lda <menurect+x1	Left side.
	sta <rect+x1

	lda <menurect+x2	Right side.
	sta <rect+x2

	lda <itemptr	Set return flag (was item found?).
	ora <itemptr+2

	rts

	ENDP

;===========================================================================
;
;	GetStarting
;
;   IN:     <menurect = menu's rectangle
;           <menuptr = ptr to menu record
;
;  OUT:     <rect = starting position
;===========================================================================
getstarting	PROC

	lda <firstVisItem
	cmp #1
	beq @1
	lda <menurect+y1
	clc
	adc <font_h
	bra @2
@1	lda <menurect+y1
@2	sta <rect+y1

	ldy <firstVisItem
	dey
lop1	beq out
	jsr next_item
	dey
	bra lop1

out	rts

	ENDP

;===========================================================================
;
;	GetItemH
;
;        	Get height of an item.
;
;   IN:    itemptr = item pointer.
;          menu_type = 0 if text menu, not zero if color menu.
;
;  OUT:    a = item's height.
;
;===========================================================================
getitemh	PROC

	ldy #ItemFlag
	lda [<itemptr],y
	and #I_INVIS
	eor #I_INVIS
	beq exit	If invisible, zero height.

	lda <font_h	Text item height.

exit	rts

	ENDP

;===========================================================================
;
;	GetIconInfo
;
;  IN: <itemptr contains ptr to current item in menu
; OUT: a-reg contains width of icon, x-reg contains height of icon
;
;===========================================================================
getIconInfo	PROC


OrigD	equ 1
MyIconRect	equ OrigD+2

	ldy #ItemFlag	; first check to see if there is an icon
	lda [<itemptr],y	; associated with this item
	and #I_NEWSTRUCTURE
	beq NoIconFound

	jsr GetStruct	; then check if this new structure contains
	ldy #ItemFlag2	; an icon field
	lda [<temptr],y
	bmi GotIcon

NoIconFound	lda #0	; there's no icon so zero the appropriate output values
	ldx #0
	ldy #0
	bra OttaHere
GotIcon
	jsr getrItemIcon	; get the icon's ref

	phx	; put it on the stack so we can reference it easier
	pha
	phd	; save current direct page register
	tsc 	; turn stack into direct page
	tcd

	ldy #oQDIconHeight
	lda [<MyIconRect],y
	tax	; x-reg contains the icon's height
	ldy #oQDIconWidth
	lda [<MyIconRect],y	; a-reg contains the icon's width
	pld	; restore original direct page register
	ply	; clean up stack
	ply

	tay
	lda <ScreenMode
	beq @In320Mode
	tya
	asl a
	tay
@In320Mode	tya

OttaHere	rts

	ENDP

;===========================================================================
;
;	getistrg
;
;          	Get item's string pointer.
;
;   IN:    itemptr = item
;
;  OUT:    strg_ptr	= item's string pointer.
;          a = low word.
;          x = high	word.
;
;===========================================================================
getistrg	PROC

	jsr getrItemName
	sta <strg_ptr
	stx <strg_ptr+2

	rts

	ENDP


;===========================================================================
;
;	GetIFirst
;
;          	Get pointer to first item in menu.
;
;   IN:    menuptr = pointer to menu.
;
;  OUT:    itemptr = pointer to first item in menu.
;          Equal flag = TRUE if no items in menu.
;
;===========================================================================
getifirst	PROC

	ldx <menuptr+2
	lda <menuptr
	clc
	adc #ItemList
	bcc store1
	inx

store1	sta <itemptr
	stx <itemptr+2

	lda [<itemptr]	Set return flag.

	rts

	ENDP


;===========================================================================
;
;	Next_Item
;
;        	Get the ID of the next menu item.
;
;   IN:  itemptr = pointer to current item.
;
;  OUT:  Equal is TRUE if there isn't any more items.
;        ELSE
;              itemptr = pointer to next item.
;
;===========================================================================
next_item	PROC

	lda <itemptr
	clc
	adc #ITEMSIZE
	bcc store
	inc <itemptr+2
store	sta <itemptr

	lda [<itemptr]	Set last item return flag.

	rts

	ENDP


;===========================================================================
;
;	HLine
;
;          	Draw a horizontal line.
;
;   IN:    PUSH:WORD - color.
;          a = starting x position.
;          x = ending x position.
;          y = line	number.
;
;  OUT:    a,x,y all the same as in.
;
;===========================================================================
hline	PROC

linenum	equ 1
xpos1	equ linenum+2
xpos2	equ xpos1+2

	phx
	pha
	phy

	pha
	phy
	_MoveTo

	lda <outLineClr	Set color of line.
	jsr setoutline

	lda xpos2,s	Line to.
	pha
	lda linenum+2,s
	pha
	_LineTo

	ply
	pla
	plx

	rts

	ENDP


;
;          APPEND MCALLS.ASM
;
;===========================================================================
;
;	FixMenuBar
;
;        	Set size of Menu bar.
;
;   IN:    None.
;
;  OUT:    WORD - height of menu bar.
;
;===========================================================================
FixMenuBar	PROC

result	equ input

myTemp	equ work

	jsr startup	Do startup initialization for tool call.
	jsr lockMenuBar	<barPtr = (<barHand), bar & menus locked.
	beq exit2	Is there a current menu bar?

	jsr to_myport	Switch to my port for text calls.

;
; --- Get the menu's pointer ---------------------
;
	jsr getmfirst	Get pointer of first menu in menu list.
	beq exit	Are there any menus?

;
; --- Set the title's width if it isn't	already set -------------
;
lop1	ldy #TitleWidth	Check if width is already set.
	lda [<menuptr],y
	bne skip10

	pha	Space for result.

	jsr getrMenuTitle	Get the menu title

	stx <mytemp+2
	sta <mytemp
	lda [<mytemp]	Check if the title is the apple logo title
	cmp #$FF01
	beq setAppleLogoWidth
	cmp #$4001
	bne notAppleLogo
setAppleLogoWidth	lda #24
	sta 1,s
	bra widthSet

notAppleLogo	PushLong <mytemp

	_StringWidth
widthSet	pla
	ldy #TitleWidth
	sta [<menuptr],y	Store width of menu	title.

skip10
;
; --- Set the width	and height of the menu ----------------------------
;
	lda #$FFFF
	pha	Default width.
	pha	Default height.
	lda [<menuptr]
	pha	Pass menu's ID.
	_CalcMenuSize

	jsr next_menu	Get the pointer to the next menu.
	bne lop1	Any more menus?

;
; --- Check if menu	bar height needs to	be set -------------
;
exit	ldy #CtlRect+y2
	lda [<barptr],y	Is the menu bar height already set?
	bne skip1	If yes, don't reset.

	ldy #CtlRect+y1
	lda [<barptr],y
	sec	Get an extra pixel here.
	adc <font_h	Add font height.
	ldy #CtlRect+y2
	sta [<barptr],y	Store menu bar's bottom side.

skip1	ldy #CtlRect+y1	Return menu bar's height.
	sec
	sbc [<barptr],y
	sta result,s

	jsr to_uport	Restore original port.
	jsr unlockMenuBar	Leave menu bar & menus unlocked.
;
exit2	brl pop0bytes	no error

	ENDP

;===========================================================================
;
;	GetItemWidth
;
;          	Computes the default size of a specified menu item.
;
;   IN:  PUSH:WORD - menuitem ID.
;
;  OUT:  WORD = default width of menu item.
;        WORD = default height of menu item.
;
;===========================================================================
GetItemWidth	PROC

itemnum	equ input
widthresult	equ itemnum+2

	jsr startup

	lda #0
	sta widthresult,s

	jsr lockMenuBar
	beq exit2

	jsr to_myport	Switch to the menu mgr's port and save user's

	lda itemnum,s	Get ptr to item record
	jsr getiptr
	beq exit

	jsr FixTextFace

	pha	Space for result.
	jsr getistrg	Get pointer to item's string.
	phx	Pass high word.
	pha	Pass low word.
	_StringWidth	Get string's width.

	jsr GetIconInfo	a-reg contains width of icon
	tax
	beq @NoIcon	If a-reg is zero then there is no icon
	clc
	adc 1,s	Add width of item name and icon width.
	adc #5	Add in some additional slop for spacing between icon.
	sta 1,s	Put result back on the stack.
@NoIcon
	lda <text_width	Add room for the check mark.
	clc
	adc <text_width
	adc <text_width
	tax
	ldy #ItemChar
	lda [<itemptr],y
	and #$00FF
	beq ok34
	lda <text_width
	clc	Now add space for the keyboard equivalent, the apple key
	ror a	and a chacracter, plus one extra for slop
	clc
	adc <text_width
	adc <text_width	1 1/2 for check mark, 2 for cmd-key-equiv,2 for space
	adc <text_width
	adc <text_width
	adc <text_width
	tax
ok34	txa
	clc
	adc 1,s
	plx	Pull in x just to fix stack, a = value.
	sta widthresult,s

	jsr ClearTextFace

exit	jsr to_uport	Restore original port.
	jsr unlockMenuBar	Leave menu bar & menus unlocked.

exit2	brl pop2bytes


	ENDP

;===========================================================================
;
;	CalcMenuSize
;
;        	Set size of Menu.
;
;   IN:  PUSH:WORD - width of menu, zero to compute, $FFFF to check first.
;        PUSH:WORD - height of menu, zero to compute, $FFFF	to check first.
;        PUSH:WORD - menu ID.
;
;  OUT:  None.
;
;===========================================================================
CalcMenuSize	PROC

menunum	equ input
height	equ menunum+2
TheWidth	equ height+2

	jsr startup	Do startup initialization for tool call.
	jsr lockMenuBar	<barPtr = (<barHand), bar & menus locked.
	beq exit2	Is there a current menu bar?

	jsr to_myport	Switch to my port for text calls.

	lda menunum,s	Get menu's ID.
	jsr getmptr	Now get its pointer.
	beq exit	Was the menu found?

	jsr freeCache	Free menu's cache, size maybe wrong.

	ldy #MenuWidth	Set menu record with given parameters.
	lda TheWidth,s
	bpl ok1

	lda [<menuptr],y	Leave MenuWidth alone.

ok1	sta [<menuptr],y
	tax	Save.
	iny
	iny
	lda height,s
	bpl ok2

	lda [<menuptr],y	Leave MenuHeight alone.

ok2	sta [<menuptr],y
	beq calc_size	Asking for default height?
	txa
	bne exit	Asking for default width?

;
; --- Compute default width and height ----------------------------------
;
calc_size	ldx #mSize	Ask defProc to compute menu size.
	jsr dispatch	Call menu's defProc.

exit	jsr to_uport	Restore original port.
	jsr unlockMenuBar	Leave menu bar & menus unlocked.

exit2	brl pop6bytes	no error

	ENDP


;===========================================================================
;
;	PushYRat
;
;        	Push address of zero page variables.
;
;===========================================================================
pushyrat	PROC

	lda #yrat
	bra enter

	ENTRY pushmrect
pushmrect
	lda #menurect
	bra enter

	ENTRY pushscInfo1
pushscInfo1
	lda #scInfo1
	bra enter

	ENTRY pushrect
pushrect	lda #rect	Most used.

enter	brl pushDpage

	ENDP

;===========================================================================
;
;	InsertMItem2
;
;        	Insert Item into ItemList.
;
;   IN:    PUSH:WORD - refDescriptor, describes what next long is (ptr, hdl, res. ID)
;          PUSH:LONG - ptr, handle, or resource ID of MenuItemTemplate
;          PUSH:WORD - item ID, zero to	insert in front, $FFFF to append.
;          PUSH:WORD - menu ID.
;
;  OUT:    None.
;
;===========================================================================
InsertMItem2	PROC

menunum	equ input
itemnum	equ menunum+2
itemstrg	equ itemnum+2
refdescriptor	equ itemstrg+4

	jsr startup	Do startup initialization for tool call.
	jsr lockMenuBar	<barPtr = (<barHand), bar & menus locked.
	beq myexit2	Is there a current menu bar?

	jsr commonInsert
	bcs myexit

	lda itemstrg,s
	sta <temptr2
	lda itemstrg+2,s
	sta <temptr2+2

	lda refdescriptor,s

	ldy <temptr
	jsr fillitemRec

	ldy #NumOfItems	update total number of items in the menu
	lda [<menuptr],y
	inc a
	sta [<menuptr],y

myexit	jsr unlockmenubar

myexit2	brl pop10bytes


;===========================================================================
;
;	InsertMItem
;
;        	Insert Item into ItemList.
;
;   IN:    PUSH:LONG - pointer ot item string to be inserted.
;          PUSH:WORD - item ID, zero to	insert in front, $FFFF to append.
;          PUSH:WORD - menu ID.
;
;  OUT:    None.
;
;===========================================================================
InsertMItem	PROC

menunum	equ input
itemnum	equ menunum+2
itemstrg	equ itemnum+2

	jsr startup	Do startup initialization for tool call.
	jsr lockMenuBar	<barPtr = (<barHand), bar & menus locked.
	beq exit2	Is there a current menu bar?

	jsr commonInsert
	bcs exit
;
; --- Insert the item ----------------------------------------------
;
	lda itemstrg,s	Pass pointer to item string.
	sta <strg_ptr
	lda itemstrg+2,s
	sta <strg_ptr+2

	ldx #1	Build record.
	jsr parse_item

exit	jsr unlockMenuBar	Leave menu bar & menus unlocked.

exit2	brl pop8bytes	no error


;===========================================================================
;
;	CommonInsert
;
;===========================================================================
	entry commonInsert
commonInsert
	lda menunum+2,s
	jsr getmptr	Get the pointer to the menu.
	beq gohome	Menu not found?

	ldy #NumOfItems	Check if the menu is empty
	lda [<menuptr],y
	bne notEmpty1
	lda itemnum+2,s
	cmp #$0000	Are we inserting at beginning
	beq @111
	cmp #$FFFF	Are we inserting at end
	bne gohome	not $0000 and not $FFFF with an empty menu means adios

@111	lda #0
	sta itemnum+2,s
	bra expand

notEmpty1	lda itemnum+2,s	Make sure given item ID is valid.
	jsr getiptr2
	beq gohome	Item not found?

;
; --- Expand menu record for new item --------------------------------
;
expand	ldx <menuhand+2	Pass menu's handle.
	lda <menuhand
	ldy #ITEMSIZE	Number of bytes to increase by.
	jsr growBlock	Expand the menu record.
	bcs gohome	Error?

	jsr freeCache	Set cache to bad if	menu has a cache.

;
; --- Make space for the item  ----------------------------------------
;
	pei <work	Save size of block.

	lda itemnum+4,s	Get pointer to where to insert item.
	jsr getiptr2
	pla
	sta <work	Restore size of block.

	lda itemnum+2,s
	beq skip2	If insert at front,	ready.

	jsr next_item	Insert after given item.

skip2	lda <itemptr	Compute number of bytes in front of item.
	sec
	sbc <menuptr
	sta <temptr	Pass to 'into_block'.

	lda <itemptr
	ldx <itemptr+2
	ldy #ITEMSIZE
	jsr into_block	Insert gap into menu record for item.

	clc
	rts

gohome	sec
	rts

	ENDP


;===========================================================================
;
;	InsertMenu
;
;        	Insert Menu into MenuList.
;
;   IN:    PUSH:LONG - handle of menu to insert.
;          PUSH:WORD - menu ID, zero to	insert at front.
;
;  OUT:    None.
;
;===========================================================================
InsertMenu	PROC

menunum	equ input
menuin	equ menunum+2

*** added 15-May-91 DAL -- make sure this isn't a duplicate menu ID
	pha
	phy

	phd
	lda 17,s
	pha
	lda 17,s
	pha
	tsc
	tcd
	ldy #2
	lda [1],y
	tax
	lda [1]
	sta 1
	stx 3
	lda [1]	;fetched menu id (first word in handle)
	plx
	plx
	pld	;A = menu ID (first word in menu handle)

	tax
	beq @notDuplicate	;I'm paranoid about the zero case

	pha
	pha	;space for GetMHandle result
	pha	;menu ID
	_GetMHandle
	plx
	plx
	beq @notDuplicate
	plx
	plx	;throw away saved YA
	ldy #6
	ldx #dupMenuID
	jml $e10184	;ToStrip
@notDuplicate	ply
	pla
*** end of 15-May-91 DAL

	jsr startup	Do startup initialization for tool call.
	jsr lockMenuBar	<barPtr = (<barHand), bar & menus locked.
	beq exit2	Is there a current menu bar?

	lda menunum,s
	beq ok2	If I'm looking for first we're ok.
	jsr getmptr	Make sure ID is valid, and get offset.
	beq exit	Was the menu found?

;
; --- Expand menu bar record for new menu --------------------------------
;
ok2	ldx <barhand+2	Pass menu bar's handle.
	lda <barhand
	ldy #4	Number of bytes to increase by.
	jsr growBlock	Expand the menu record.
	bcs exit	Error?

	lda menuin,s
	sta <menuhand
	lda menuin+2,s
	sta <menuhand+2
	jsr lockMenuHand	<menuhand = locked.
	jsr derefMenuHand	<menuptr = (<menuhand).

	ldy #CtlOwner+2	Is this a window menu bar?
	lda [<barptr],y
	bpl ok3

	ldy #MenuFlag	Don't allow caching for window menus.
	lda [<menuptr],y
	and #_M_CACHE
	sta [<menuptr],y

; --- Make space for the new menu handle  -------------------------------
;
ok3	lda menunum,s
	bne skip2	If insert after, I'm ready.

	lda #MenuList	Insert at front, reset 'menu_cnt'.
	sta <menu_cnt

skip2	ldx <barptr+2	Compute where to insert.
	lda <barptr
	clc
	adc <menu_cnt
	bcc ok1
	inx
ok1	ldy <menu_cnt	Number of bytes in front of insert.
	sty <temptr	Pass to 'into_block'.

	ldy #4
	jsr into_block	Insert gap into menu record for item.
;
; --- Store new handle into gap ---------------------------------------
;
	lda menuin,s
	sta [<temptr2]
	ldy #2
	lda menuin+2,s
	sta [<temptr2],y

	jsr everycachefree

exit	jsr unlockMenuBar	Leave menu bar & menus unlocked.
;
exit2	brl pop6bytes	no error

	ENDP


;===========================================================================
;
;	DeleteMItem
;
;        	Delete Item from ItemList.
;
;   IN:    PUSH:WORD - item ID.
;
;  OUT:    None.
;
;===========================================================================
DeleteMItem	PROC

itemnum	equ input

	jsr startup	Do startup initialization for tool call.
	jsr lockMenuBar	<barPtr = (<barHand), bar & menus locked.
	beq exit2	Is there a current menu bar?

	lda itemnum,s
	jsr getiptr	Get pointer to item	to delete.
	beq exit	Was the item found?

;
; --- Move other items over deleted item --------------------------
;
lop1	ldy #(ITEMSIZE*2)-2
	ldx #ITEMSIZE-2
lop2	lda [<itemptr],y
	phy
	txy
	sta [<itemptr],y
	ply
	dey
	dey
	dex
	dex
	bpl lop2

	jsr next_item	Any more items?
	bne lop1

;
; --- Shrink menu record for deleted item --------------------------------
;
	ldy #NumOfItems	Update number of total items in menu.
	lda [<menuptr],y
	dec a
	sta [<menuptr],y

	ldx <menuhand+2	Pass menu's handle.
	lda <menuhand
;;;	ldy #$FFF6	Number of bytes to decrease.
*** 4-Jun-92 DAL -- Should shrink menu handle by 12 bytes, not 10
	ldy #$FFF4	;Shrink by 12 bytes (ITEMSIZE)
*** end 4-Jun-92
	jsr growBlock	Shrink the menu record.

	jsr freeCache	Set cache to bad if	menu has a cache.

	ldy #menuFlag
	lda [<menuptr],y
	and #M_POPUP	Is this menu a pop-up menu?
	beq exit

	ldy #ctlProc+2
	lda [<barptr],y
	bpl exit	This must be a super control before we change current sel.

	ldy #ctlValue	If it is then we need to check if we just deleted
	lda [<barptr],y	the currently selected item.
	cmp itemnum,s
	bne exit

	ldy #ctlOwner+2	Make sure the origin is right before drawing.
	lda [<barptr],y
	pha
	dey
	dey
	lda [<barptr],y
	pha
	_StartDrawing

	pea 0	New control value, 0 = no current selection in pop-up
	pei <barhand+2
	pei <barhand	Handle to pop-up control
	_SetCtlValue

	lda #0
	pha
	pha
	_SetOrigin

exit	jsr unlockMenuBar	Leave menu bar & menus unlocked.

exit2	brl pop2bytes	no error

	ENDP


;===========================================================================
;
;	DeleteMenu
;
;        	Delete one Menu from MenuList.
;
;   IN:    PUSH:WORD - menu ID.
;
;  OUT:    None.
;
;===========================================================================
DeleteMenu	PROC

menunum	equ input

	jsr startup	Do startup initialization for tool call.
	jsr lockMenuBar	<barPtr = (<barHand), bar & menus locked.
	beq exit2	Is there a current menu bar?

;
; --- Take menu out	of menu list ---------------------------------
;
	lda menunum,s	ID to match.
	jsr getmptr	Find the menu.
	beq exit	Error?

	jsr freecache	Release cache that may be allocated for this menu.

	ldy #4
	lda [<menuhand],y	Unlock the handle of menu to be removed.
	and #$7FFF
	sta [<menuhand],y

lop2	jsr next_menu

	lda <menu_cnt
	sec
	sbc #8
	tay

	lda <menuhand
	sta [<barptr],y
	lda <menuhand+2
	iny
	iny
	sta [<barptr],y

	ora <menuhand	Any more menu's?
	bne lop2

;
; --- Shrink menu record for deleted item --------------------------------
;
	ldx <barhand+2	Pass menu bar's handle.
	lda <barhand
	ldy #$FFFC	Number of bytes to decrease.
	jsr growBlock	Shrink the menu record.

	jsr everycachefree	Menus may now be in different order.

exit	jsr unlockMenuBar	Leave menu bar & menus unlocked.

exit2	brl pop2bytes	no error

	ENDP


;===========================================================================
;
;	GrowBlock
;
;          	Increase the size of a allocated memory block.
;
;   IN:    x/a = handle top resize.
;          y = number of bytes to insert.
;
;  OUT:    <work = new size.
;          Carry is	set if unable to expand, clear if ok.
;
;===========================================================================
growBlock	PROC

	sta <temptr	Save handle.
	stx <temptr+2
	sty <work	Save size delta.

	pha	Space for result
	pha
	phx	Pass handle.
	pha
	_GetHandleSize	Get the present size of the block.

	jsr unlockMenuBar	Unlock menu bar & menus so they can move.

	pla	Get the current size.
	clc
	adc <work	Increase the size.
	sta <work	Save new size.

	pha	Pass new size.
	pei <temptr+2	Pass handle.
	pei <temptr
	_SetHandleSize	Expand the block.

	php	Save error code.
	jsr lockMenuBar	Relock menu bar & menus.
	jsr derefMenuHand	<menuptr = (<menuhand).
	plp	Return error code, if any.

	rts

	ENDP


;===========================================================================
;
;	Into_Block
;
;          	Insert zero bytes into middle of block.
;
;   IN:    x/a = pointer to insert place.
;          y = number of bytes to insert.
;          <work = number of bytes in block.
;          <temptr = number of bytes in	front of insertion point.
;
;===========================================================================
into_block	PROC

	sta <temptr2
	stx <temptr2+2
	sty <work+2	Number of bytes to insert.

	lda <work	Number of bytes in block,
	sec
	sbc <temptr	less number of bytes in front of insert,
	dec a	less one word,
	dec a
	tax	equals offset from insert to end of record.
	sbc <work+2	Less size of insert, equals offset to
	tay	data that needs to be moved.

lop1	lda [<temptr2],y
	phy
	txy
	sta [<temptr2],y
	ply
	lda #0	Clear gap as we go.
	sta [<temptr2],y
	dex
	dex
	dey
	dey
	bpl lop1

	rts

	ENDP


;===========================================================================
;
;	GetSysBar
;
;       	Return pointer to System Menu bar.
;
;   IN:  None.
;
;  OUT:  LONG - handle of system menu bar.
;
;===========================================================================
GetSysBar	PROC

result	equ input

	jsr startup	Do startup initialization for tool call.

	lda <sysmenu
	sta result,s
	lda <sysmenu+2
	sta result+2,s

	brl pop0bytes	no error

	ENDP


;===========================================================================
;
;	SetSysBar
;
;        	Install new system menu bar.
;
;   IN:    PUSH:LONG - menu bar handle.
;
;  OUT:    None.
;
;===========================================================================
SetSysBar	PROC

newbar	equ input

	jsr startup	Do startup initialization for tool call.

	lda newbar,s	Set new system menu	bar pointer.
	sta <sysmenu
	lda newbar+2,s
	sta <sysmenu+2

	brl pop4bytes	no error

	ENDP


;===========================================================================
;
;	SetMenuBar
;
;          	Set current menu bar.
;
;   IN:    PUSH:LONG - new current menu	bar, zero for system menu bar.
;
;  OUT:    None.
;
;===========================================================================
SetMenuBar	PROC

	jsr startup	Do startup initialization for tool call.
	jsr setCurrentBar	<barHand = passed menu bar.

	brl pop4bytes	no error

	ENDP


;===========================================================================
;
;	GetMenuBar
;
;          	Get current menu bar.
;
;   IN:    None.
;
;  OUT:    LONG - handle of current menu bar.
;
;===========================================================================
GetMenuBar	PROC

result	equ input

	jsr startup	Do startup initialization for tool call.

	lda <barhand	Return current menu	bar.
	sta result,s
	lda <barhand+2
	sta result+2,s

	brl pop0bytes	no error

	ENDP


;===========================================================================
;
;	CountMItems
;
;        	Return number of items in menu.
;
;   IN:    PUSH:WORD - menu ID.
;
;  OUT:    WORD - number of items in menu, $FFFF if menu not found.
;
;===========================================================================
CountMItems	PROC

menunum	equ input
result	equ menunum+2

	jsr startup	Do startup initialization for tool call.
	jsr lockMenuBar	<barPtr = (<barHand), bar & menus locked.
	beq exit2	Is there a current menu bar?

	lda #$FFFF
	sta result,s	Start with error.

	lda menunum,s	Pass menu's ID.
	jsr getmptr	Put pointer to menu	into 'menuptr'.
	beq exit	Is there a menu with that ID?

	stz <work	Item counter.
	jsr getifirst
	beq exit	Is there even one item?

lop1	inc <work
	jsr next_item	Next item.
enter1	bne lop1	Any more items?

exit	lda <work
	sta result,s	Return number of items.

	jsr unlockMenuBar	Leave menu bar & menus unlocked.

exit2	brl pop2bytes	no error

	ENDP


;===========================================================================
;
;	SetBarColors
;
;        	Set colors of menu bar.
;
;   IN:  PUSH:WORD - Normal color:    Bits 0-3 = text color	when normal.
;	                  Bits 4-7 = background	color when normal.
;	                  Bits 8-15 = zero.
;	                  $FFFF to not set.
;
;        PUSH:WORD - Selected color:  Bits 0-3 = text color	when selected.
;	                  Bits 4-7 = background	color when selected.
;	                  Bits 8-15 = zero.
;	                  $FFFF to not set.
;
;        PUSH:WORD - Outline color:   Bits 0-3 = zero.
;	                  Bits 7-4 = outine color.
;	                  Bits 8-15 = zero.
;	                  $FFFF to not set.
;
;  OUT:  None.
;
;===========================================================================
SetBarColors	PROC

newout	equ input
newinvert	equ newout+2
newbar	equ newinvert+2

	jsr startup	Do startup initialization for tool call.
	jsr lockMenuBar	<barPtr = (<barHand), bar & menus locked.
	beq exit2	Is there a current menu bar?

	ldy #CtlColor
	lda [<barptr],y
	iny
	iny
	ora [<barptr],y
	beq exit

	jsr everyCacheBad	Set cache to bad if	menu has a cache.
	jsr getcolor	work = pointer to color table.

	ldy #0
	lda newbar,s	Should bar color be	set?
	bmi next1
	sta [<work],y

next1	iny
	iny
	lda newinvert,s	Should invert color	be set.
	bmi next2
	sta [<work],y

next2	iny
	iny
	lda newout,s	Should outline color be set.
	bmi exit
	sta [<work],y

exit	jsr unlockMenuBar	Leave menu bar & menus unlocked.

exit2	brl pop6bytes	no error

	ENDP


;===========================================================================
;
;	GetBarColors
;
;        	Return menu bar's colors.
;
;   IN:  None.
;
;  OUT:  LONG - Bits 31-24 = undefined.
;               Bits 23-20 = outline color.
;               Bits 19-16 = undefined.
;               Bits 15-12 = background	color when selected.
;               Bits  11-8 = text color	when selected.
;               Bits   7-4 = background	color when not selected.
;               Bits   3-0 = text color	when not selected.
;
;===========================================================================
GetBarColors	PROC

result	equ input

	jsr startup	Do startup initialization for tool call.
	jsr lockMenuBar	<barPtr = (<barHand), bar & menus locked.
	beq exit2	Is there a current menu bar?

	jsr getcolor	Get menu bar colors.

	lda <outlineclr
	sta result+2,s

	lda <hiliteclr
	xba
	ora <norcolor
	sta result,s

	jsr unlockMenuBar	Leave menu bar & menus unlocked.

exit2	brl pop0bytes	no error

	ENDP


;===========================================================================
;
;	SetMTitleStart
;
;        	Set starting position of titles.
;
;   IN:  PUSH:WORD - starting position,	bits 0-6 used.
;
;  OUT:  None.
;
;===========================================================================
SetMTitleStart	PROC

newstart	equ input

	jsr startup	Do startup initialization for tool call.
	jsr lockMenuBar	<barPtr = (<barHand), bar & menus locked.
	beq exit2	Is there a current menu bar?

	ldy #CtlFlag+1
	lda [<barptr],y
	and #$FF80	Clear current starting position.
	ora newstart,s	Set new starting position.
	sta [<barptr],y

	jsr everyCacheFree	Free every cahce, size maybe wrong.

	jsr unlockMenuBar	Leave menu bar & menus unlocked.

exit2	brl pop2bytes	no error

	ENDP


;===========================================================================
;
;	GetMTitleStart
;
;        	Return starting position of titles.
;
;   IN:  None.
;
;  OUT:  WORD - starting position.
;
;===========================================================================
GetMTitleStart	PROC

result	equ input

	jsr startup	Do startup initialization for tool call.
	jsr lockMenuBar	<barPtr = (<barHand), bar & menus locked.
	beq exit2	Is there a current menu bar?

	ldy #CtlFlag+1
	lda [<barptr],y
	and #$007F	Get just the current starting position.
	sta result,s

	jsr unlockMenuBar	Leave menu bar & menus unlocked.

exit2	brl pop0bytes	no error

	ENDP


;===========================================================================
;
;	GetMHandle
;
;        	Find the handle of menu.
;
;   IN:    PUSH:WORD - Menu ID of menu to find.
;
;  OUT:    LONG - menu pointer, or zero	if error.
;
;===========================================================================
GetMHandle	PROC

id	equ input
result	equ id+2

	jsr startup	Do startup initialization for tool call.
	jsr lockMenuBar	<barPtr = (<barHand), bar & menus locked.
	beq exit2	Is there a current menu bar?

	lda id,s	Pass ID in A.
	jsr getmptr	Get handle of menu.

	lda <menuhand	Return found handle.
	sta result,s
	lda <menuhand+2
	sta result+2,s

	jsr unlockMenuBar	Leave menu bar & menus unlocked.

exit2	brl pop2bytes	no error

	ENDP


;===========================================================================
;
;	SetMenuID
;
;        	Set menu ID number.
;
;   IN:  PUSH:WORD - new ID.
;        PUSH:WORD - menu's ID.
;
;  OUT:  None.
;
;===========================================================================
SetMenuID	PROC

menunum	equ input
newID	equ menunum+2

	jsr startup	Do startup initialization for tool call.
	jsr lockMenuBar	<barPtr = (<barHand), bar & menus locked.
	beq exit2	Is there a current menu bar?

	lda menunum,s
	jsr getmptr	Put menu pointer into 'menuptr'.
	beq exit	Menu not found?

	lda newID,s
	sta [<menuptr]	Set new ID.

exit	jsr unlockMenuBar	Leave menu bar & menus unlocked.

exit2	brl pop4bytes	no error

	ENDP


;===========================================================================
;
;	SetMTitleWidth
;
;        	Set menu title's width.
;
;   IN:  PUSH:WORD - width.
;        PUSH:WORD - menu's ID.
;
;  OUT:  None.
;
;===========================================================================
SetMTitleWidth	PROC

menunum	equ input
newwidth	equ menunum+2

	jsr startup	Do startup initialization for tool call.
	jsr lockMenuBar	<barPtr = (<barHand), bar & menus locked.
	beq exit2	Is there a current menu bar?

	lda menunum,s
	jsr getmptr	Put menu pointer into 'menuptr'.
	beq exit	Menu not found?

	ldy #TitleWidth
	lda newwidth,s
	sta [<menuptr],y	Set new title width.

	jsr everyCacheFree	Free every cahce, size maybe wrong.

exit	jsr unlockMenuBar	Leave menu bar & menus unlocked.

exit2	brl pop4bytes	no error

	ENDP


;===========================================================================
;
;	GetMTitleWidth
;
;        	Return menu title's width.
;
;   IN:  PUSH:WORD - menu's ID.
;
;  OUT:  WORD - title's width.
;
;===========================================================================
GetMTitleWidth	PROC

menunum	equ input
result	equ menunum+2

	jsr startup	Do startup initialization for tool call.
	jsr lockMenuBar	<barPtr = (<barHand), bar & menus locked.
	beq exit2	Is there a current menu bar?

	lda menunum,s
	jsr getmptr	Put menu pointer into 'menuptr'.
	beq exit	Menu not found?

	ldy #TitleWidth
	lda [<menuptr],y	Get menu's title width,
	sta result,s	and pass it back to	caller.

exit	jsr unlockMenuBar	Leave menu bar & menus unlocked.

exit2	brl pop2bytes	no error

	ENDP


;===========================================================================
;
;	SetMenuFlag
;
;        	Set menu's MenuFlag
;
;   IN:  PUSH:WORD - new value, bits to	clear or set.
;        PUSH:WORD - menu's ID.
;
;  OUT:  None.
;
;===========================================================================
SetMenuFlag	PROC

menunum	equ input
newValue	equ menunum+2

	jsr startup	Do startup initialization for tool call.
	jsr lockMenuBar	<barPtr = (<barHand), bar & menus locked.
	beq exit2	Is there a current menu bar?

	lda menunum,s
	jsr getmptr	Put menu pointer into 'menuptr'.
	beq exit	Menu not found?

	jsr badCache	Set cache to bad if	menu has a cache.

	ldy #MenuFlag
	lda newValue,s
	bmi reset

	ora [<menuptr],y	Set desired bits.
	bra store

reset	and [<menuptr],y	Clear desired bits.
store	sta [<menuptr],y	Store new flag.

exit	jsr unlockMenuBar	Leave menu bar & menus unlocked.

exit2	brl pop4bytes	no error
	ENDP


;===========================================================================
;
;	GetMenuFlag
;
;        	Get menu's MenuFlag.
;
;   IN:    PUSH:WORD - menu's ID.
;
;  OUT:    WORD - MenuFlag.
;
;===========================================================================
GetMenuFlag	PROC

menunum	equ input
result	equ menunum+2

	jsr startup	Do startup initialization for tool call.
	jsr lockMenuBar	<barPtr = (<barHand), bar & menus locked.
	beq exit2	Is there a current menu bar?

	lda menunum,s
	jsr getmptr	Put menu pointer into 'menuptr'.
	beq exit	Menu not found?

	ldy #MenuFlag
	lda [<menuptr],y	Get menu's flag.
	sta result,s	and pass it back to	caller.

exit	jsr unlockMenuBar	Leave menu bar & menus unlocked.

exit2	brl pop2bytes	no error

	ENDP

;===========================================================================
;
;	SetMenuTitle2
;
;  IN: PUSH:WORD - refdescriptor, describes following long (ptr, handle, res ID)
;      PUSH:LONG - titleref, ptr, handle or resource ID of title
;      PUSH:WORD - id of menu that gets new title
;
;===========================================================================
SetMenuTitle2	PROC

menunum	equ input
titleref	equ menunum+2
refdescriptor	equ titleref+4

	jsr startup
	jsr lockmenubar
	beq exit2

	lda menunum,s
	jsr getmptr	;Put menu pointer into 'menuptr'.
	beq exit	;Menu not found?

	ldy #TitleName	;put titleref in menu record
	lda titleref,s
	sta [<menuptr],y
	iny
	iny
	lda titleref+2,s
	sta [<menuptr],y

;
; now we must set the menuflag to jive with what the refdescriptor is
;
	lda refdescriptor,s
	asl a
	tax

	ldy #MenuFlag	;clear out the high two bits before setting anything
	lda [<menuptr],y
	and #CLEAR_TWO_BITS

	jmp (table,x)

table	dc.w pointer
	dc.w handle
	dc.w resourceID

resourceID	ora #M_RESOURCEID
	bra pointer

handle	ora #M_HANDLE
	bra pointer

pointer	ldy #MenuFlag
	sta [<menuptr],y

	pha	;space for result
	jsr getrMenuTitle	;get the width of the menu title
	phx	;getmenutitle returns result in a-reg and x-reg
	pha
	_StringWidth

	pla
	ldy #TitleWidth
	sta [<menuptr],y

	jsr everyCacheFree	;Free every cahce, size maybe wrong.

exit	jsr unlockMenuBar

exit2	brl pop8bytes

	ENDP

;===========================================================================
;
;	SetMenuTitle
;
;        	Set menu's title.
;
;   IN:  PUSH:LONG - pointer to string.
;        PUSH:WORD - menu's ID.
;
;  OUT:  None.
;
;===========================================================================
SetMenuTitle	PROC

menunum	equ input
newstrg	equ menunum+2

	jsr startup	;Do startup initialization for tool call.
	jsr lockMenuBar	<barPtr = (<barHand), bar & menus locked.
	beq exit2	Is there a current menu bar?

	lda menunum,s
	jsr getmptr	Put menu pointer into 'menuptr'.
	beq exit	Menu not found?

	ldy #MenuFlag	Clear upper two bits of menures flag to signify that
	lda [<menuptr],y	menu title is a pointer (need to do this just in case the
	and #CLEAR_TWO_BITS	last reference was a handle or resource ID)
	sta [<menuptr],y

	ldy #TitleName
	lda newstrg,s	Get pointer to new string.
	sta [<menuptr],y
	tax
	iny
	iny
	lda newstrg+2,s
	sta [<menuptr],y

	pha	Space for result.
	pha	Pass address of string.
	phx
	_StringWidth
	pla
	ldy #TitleWidth
	sta [<menuptr],y	Store width of menu	title.

	jsr everyCacheFree	Free every cahce, size maybe wrong.

exit	jsr unlockMenuBar	Leave menu bar & menus unlocked.

exit2	brl pop6bytes	no error

	ENDP


;===========================================================================
;
;	GetMenuTitle
;
;        	Return pointer to menu's title.
;
;   IN:  PUSH:WORD - menu's ID.
;
;  OUT:  LONG - pointer to menu's title, zero if error.
;
;===========================================================================
GetMenuTitle	PROC

menunum	equ input
result	equ menunum+2

	jsr startup	Do startup initialization for tool call.
	jsr lockMenuBar	<barPtr = (<barHand), bar & menus locked.
	beq exit2	Is there a current menu bar?

	lda menunum,s
	jsr getmptr	Put menu pointer into 'menuptr'.
	beq exit	Menu not found?

	ldy #TitleName	Return pointer to menu's title.
	lda [<menuptr],y
	sta result,s
	iny
	iny
	lda [<menuptr],y
	sta result+2,s

exit	jsr unlockMenuBar	Leave menu bar & menus unlocked.

exit2	brl pop2bytes	no error

	ENDP


;===========================================================================
;
;	GetIPtr
;
;        	Find pointer of item.
;
;
;   IN:    a = item's ID, zero to find first item, $FFFF to find last.
;
;  OUT:    itemptr = pointer to item.
;          Equal flag = TRUE if error.
;
;===========================================================================
GetIPtr	PROC

; --- Search every menu in the menu bar	-----------------------------
;
	sta <work	Save ID I'm looking for.

	jsr getmfirst	Start with first menu.
	beq exit	Are there any menus?

lop3	jsr getiptr3	Search every item in menu.
	bne exit	Item found?

nextmenu	jsr next_menu	Try next menu.
	bne lop3	Any more menus?

exit	rts


	ENTRY getiptr2
getiptr2

	sta <work	Save ID to look for.
;
; ------ Search every item in the menu ------------------------------
;
	ENTRY getiptr3
getiptr3

lop1	jsr getifirst	Get pointer to first item in menu.
	bne lop2	Are there any items	in the menu?
	rts	12/5/88 HY, if no items were found we used to bra to nextmenu
;		now I just return if the menu is empty.

lop2	lda <work	ID I'm looking for.
	beq found	Looking for first one?
	cmp #$FFFF	Looking for last one?
	beq ck_last
	cmp [<itemptr]	Does item's ID match ID I'm looking for?
	bne nextitem
	bra found	If matched, I found	it.

ck_last	ldy #ITEMSIZE	Look at the ID of the next item.
	lda [<itemptr],y
	bne nextitem	Is it the last?

found	lda #1	Set not equal flag for found.
	rts

nextitem	jsr next_item	Next item.
	bne lop2	Any more items in this menu?

	rts

	ENDP


;===========================================================================
;
;	SetItemID
;
;        	Set new item ID.
;
;   IN:    PUSH:WORD - new ID.
;          PUSH:WORD - item's ID.
;
;  OUT:    None.
;
;===========================================================================
SetItemID	PROC

itemnum	equ input
newID	equ itemnum+2

	jsr startup	Do startup initialization for tool call.
	jsr lockMenuBar	<barPtr = (<barHand), bar & menus locked.
	beq exit2	Is there a current menu bar?

	lda itemnum,s
	jsr getiptr
	beq exit	Error?

	lda newID,s
	sta [<itemptr]

exit	jsr unlockMenuBar	Leave menu bar & menus unlocked.

exit2	brl pop4bytes	no error

	ENDP

;===========================================================================
;
;	SetMItem2
;
;  IN: PUSH:WORD - refdescriptor, describes what next long is (0=ptr, 1=hdl, 2=res ID)
;      PUSH:LONG - titleref, pointer, handle or resource ID of a resource menu item
;      PUSH:WORD - item's ID
;
; OUT: None.
;
;===========================================================================
SetMItem2	PROC

itemnum	equ input
titleref	equ itemnum+2	; ptr, hdl, resource ID of new item name
refdescriptor	equ titleref+4

myTemp	equ work
newFlag	equ myTemp+4

	jsr startup
	jsr lockmenubar
	bne @FoundMenuBar
	brl exit2
@FoundMenuBar
	lda itemnum,s
	jsr getiptr
	bne @FoundItem
	brl exit	Error?
@FoundItem
	jsr badCache	Set cache to bad if menu has a cache

	ldy #ItemFlag	Get flag of current item and clear the first two bits
	lda [<itemptr],y	We need to clear them because latter on we're going to
	and #CLEAR_TWO_BITS 'OR' it with the new value
	sta [<itemptr],y

	lda titleref,s
	sta <myTemp
	lda titleref+2,s
	sta <myTemp+2

	lda refdescriptor,s
	asl a
	tax
	jmp (table,x)

table	dc.w pointer
	dc.w handle
	dc.w resourceID

resourceID	lda titleref+2,s	Load the menu item resource and get the handle to it
	tax
	lda titleref,s
	ldy #rMenuItem
	jsr LoadnRelease
	sta <myTemp	Store handle back on my direct page
	stx <myTemp+2

handle	ldy #2	Dereference the menu item handle and put ptr back
	lda [<myTemp],y	into my direct page
	tax
	lda [<myTemp]
	sta <myTemp
	stx <myTemp+2

pointer	ldy #resItemFlag	Find out how the item name is being referenced, is it a
	lda [<myTemp],y	pointer, handle, or resource ID?
	and #FIRST_TWO_BITS
	sta <newFlag

	ldy #ItemFlag
	lda [<itemptr],y
	ora <newFlag
	sta [<itemptr],y	Update the item flag in our item record

	ldy #resItemName+2	Get new name from item template, which may be
	lda [<myTemp],y	a ptr, hdl, or resource ID.
	pha
	ldy #resItemName
	lda [<myTemp],y
	pha

	lda <itemptr	Move ptr to item's record into <temptr.
	sta <temptr
	lda <itemptr+2
	sta <temptr+2

	ldy #itemflag	Check if there is the new structure associated
	lda [<itemptr],y	with this item.
	and #I_NEWSTRUCTURE
	beq @oldway

	jsr GetStruct	There is so get the ptr to the new structure
	ldy #itemName2	and store the ptr in <temptr.
	bra @setit
@oldway
	ldy #itemName
@setit	pla
	sta [<temptr],y
	pla
	iny
	iny
	sta [<temptr],y

exit	jsr unlockmenubar

exit2	brl pop8bytes

	ENDP

;===========================================================================
;
;	SetMItem
;
;        	Set new item string.
;
;   IN:    PUSH:LONG - pointer to new string.
;          PUSH:WORD - item's ID.
;
;  OUT:    None.
;
;===========================================================================
SetMItem	PROC

itemnum	equ input
strg	equ itemnum+2

	jsr startup	Do startup initialization for tool call.
	jsr lockMenuBar	<barPtr = (<barHand), bar & menus locked.
	beq exit2	Is there a current menu bar?

	lda itemnum,s
	jsr getiptr
	beq exit	Error?

	jsr badCache	Set cache to bad if	menu has a cache.

	ldy #ItemFlag	Since the reference to the item name is a ptr to that name
	lda [<itemptr],y	we clear the first two bits of the item flag
	and #CLEAR_TWO_BITS
	sta [<itemptr],y

	lda strg,s	Pass pointer to string.
	sta <strg_ptr
	lda strg+2,s
	sta <strg_ptr+2

	jsr parse_strg	Get and set length of string.

	lda <itemptr	Move ptr to item's record to <temptr.
	sta <temptr
	lda <itemptr+2
	sta <temptr+2

	ldy #ItemFlag	Check if item has new structure associated
	lda [<itemptr],y	with it.
	and #I_NEWSTRUCTURE
	beq @oldway

	jsr GetStruct	There is so get the ptr to the new structure
	ldy #itemName2	and store the ptr in <temptr.
	bra @setit
@oldway
	ldy #ItemName	Set adjusted pointer to new string.
@setit	lda <strg_ptr
	sta [<temptr],y
	lda <strg_ptr+1
	iny
	sta [<temptr],y

exit	jsr unlockMenuBar	Leave menu bar & menus unlocked.

exit2	brl pop6bytes	no error

	ENDP


;===========================================================================
;
;	GetItem
;
;        	Get item's string.
;
;   IN:  PUSH:WORD - item's ID.
;
;  OUT:  LONG - pointer to item's text.
;
;===========================================================================
GetItem	PROC

itemnum	equ input
result	equ itemnum+2

	jsr startup	Do startup initialization for tool call.
	jsr lockMenuBar	<barPtr = (<barHand), bar & menus locked.
	beq exit2	Is there a current menu bar?

	lda itemnum,s	Get item's ID.
	jsr getiptr	Now get its pointer.
	bne foundSomething	Error?
	jsr unlockMenuBar
	ldy #Item_Not_Found
	brl Epop2bytes

foundSomething	lda <itemptr
	sta <temptr
	lda <itemptr+2
	sta <temptr+2

	ldy #itemflag	Check if there is the new structure associated
	lda [<itemptr],y	with this item.
	and #I_NEWSTRUCTURE
	beq @OldWay

	jsr GetStruct	There is so get the ptr to the new structure
	ldy #itemName2	and store the ptr in <temptr.
	bra @getit
@OldWay
	ldy #ItemName
@getit	lda [<temptr],y
	sta result,s
	iny
	iny
	lda [<temptr],y
	sta result+2,s

exit	jsr unlockMenuBar	Leave menu bar & menus unlocked.

exit2	brl pop2bytes	no error

	ENDP


;===========================================================================
;
;	SetMItemName2
;
;  IN: PUSH:WORD - refdescriptor, describes what next long will be
;      PUSH:LONG - titleref, pointer, handle, or resource ID of title name
;      PUSH:WORD - menuitem, ID of item that will get new title
;
; OUT: None.
;
;===========================================================================
SetMItemName2	PROC

itemnum	equ input
titleref	equ itemnum+2	; ptr, hdl, resource ID of new item name
refdescriptor	equ titleref+4

	jsr startup
	jsr lockMenuBar
	beq exit2

	lda itemnum,s	Get item's ID.
	jsr getiptr	Now get its pointer (in <itemptr).
	beq exit	Error?

	jsr badCache	Set cache to bad if	menu has a cache.

	lda <itemptr	Store ptr to item's record in <temptr.
	sta <temptr
	lda <itemptr+2
	sta <temptr+2

	ldy #itemflag	Check to see if item has new structure
	lda [<temptr],y	associated with it.
	and #I_NEWSTRUCTURE
	beq @oldway
	jsr GetStruct	There is so get the ptr to the new structure
	ldy #itemName2	and store the ptr in <temptr.
	bra getIt
@oldway
	ldy #ItemName	Insert new item name into the item record
getit
	lda titleref,s
	sta [<temptr],y
	iny
	iny
	lda titleref+2,s
	sta [<temptr],y

	lda refdescriptor,s
	asl a
	tax

	ldy #ItemFlag	Get flag of current item and clear the first two bits
	lda [<itemptr],y	We need to clear them because later on we're going to
	and #CLEAR_TWO_BITS 'OR' it with the new value

	jmp (table,x)

table	dc.w pointer
	dc.w handle
	dc.w resourceID

resourceID	ora #M_RESOURCEID
	bra pointer

handle	ora #M_HANDLE

pointer	sta [<itemptr],y

exit	jsr unlockMenuBar

exit2	brl pop8bytes

	ENDP


;===========================================================================
;
;	SetMItemName
;
;        	Set item's string.
;
;   IN:    PUSH:LONG - pointer to pascal string.
;          PUSH:WORD - item's ID.
;
;  OUT:    None.
;
;===========================================================================
SetMItemName	PROC

itemnum	equ input
newName	equ itemnum+2

	jsr startup	Do startup initialization for tool call.
	jsr lockMenuBar	<barPtr = (<barHand), bar & menus locked.
	beq exit2	Is there a current menu bar?

	lda itemnum,s	Get item's ID.
	jsr getiptr	Now get its pointer.
	beq exit	Error?

	jsr badCache	Set cache to bad if	menu has a cache.

	lda <itemptr	Store ptr to item's record in <temptr.
	sta <temptr
	lda <itemptr+2
	sta <temptr+2

	ldy #ItemFlag	Get flag of current item and clear the first two bits
	lda [<itemptr],y	We need to clear them because later on we're going to
	and #CLEAR_TWO_BITS 'OR' it with the new value
	sta [<itemptr],y

	lda [<itemptr],y	Check if item has new structure associated
	and #I_NEWSTRUCTURE	with it.
	beq @oldway

	jsr GetStruct	There is so get the ptr to the new structure
	ldy #itemName2	and store the ptr in <temptr.
	bra @getit
@oldway
	ldy #ItemName
@getit	lda newName,s
	sta [<temptr],y
	iny
	iny
	lda newName+2,s
	sta [<temptr],y

exit	jsr unlockMenuBar	Leave menu bar & menus unlocked.

exit2	brl pop6bytes	no error

	ENDP


;===========================================================================
;
;	EnableMItem
;
;          	Enable Item
;
;   IN:    PUSH:WORD - item ID.
;
;  OUT:    None.
;
;===========================================================================
EnableMItem	PROC

itemnum	equ input

	jsr startup	Do startup initialization for tool call.
	lda #$FF7F	Clear disable bit.

	ENTRY set_iflag
set_iflag

	pha	Pass newvalue.
	lda itemnum+2,s	Pass item's ID.
	pha
	_SetMItemFlag	Set the item's flag.

	brl pop2bytes	no error

	ENDP


;===========================================================================
;
;          	DisableMItem
;
;   IN:    PUSH:WORD - item ID.
;
;  OUT:    None.
;
;===========================================================================
DisableMItem	PROC

	jsr startup	Do startup initialization for tool call.

	lda #I_ENABLED	Clear disable bit.
	bra set_iflag

	ENDP


;===========================================================================
;
;	SetMItemStyle
;
;        	Set item's style.
;
;   IN:    PUSH:WORD - new style.
;          PUSH:WORD - item ID.
;
;  OUT:    None.
;
;===========================================================================
SetMItemStyle	PROC

itemnum	equ input
newstyle	equ itemnum+2

	jsr startup	Do startup initialization for tool call.

StyleBits	equ I_NoBold+I_NoItalic+I_NoScore+I_NoShadow+I_NoOutline

	pea $FFFF-StyleBits Clear existing style
	lda itemnum+2,s	Pass item's ID.
	pha
	_SetMItemFlag

; Take the input style word and convert it to the format that is in the itemFlag word
; (bold, italic and underline are in the low 3 bits of low byte. shadow and outline
; are in bits 3 and 4 of the high byte.)

	lda newstyle,s
	tax
	and #I_Nobold+I_NoItalic+I_NoScore
	pha
	txa
	xba
	and #I_NoShadow+I_NoOutline
	ora 1,s
	sta 1,s

	lda itemnum+2,s
	pha	Pass item's ID.
	_SetMItemFlag	Set the item's flag.

	brl pop4bytes	no error

	ENDP


;===========================================================================
;
;        	GetItemStyle
;
;   IN:    PUSH:WORD - item ID.
;
;  OUT:    WORD - item's style.
;
;===========================================================================
GetItemStyle	PROC

itemnum	equ input
result	equ itemnum+2

	jsr startup	Do startup initialization for tool call.
	jsr lockMenuBar	<barPtr = (<barHand), bar & menus locked.
	beq exit2	Is there a current menu bar?

	lda itemnum,s	Get item's ID.
	jsr getiptr	Now get its pointer.
	beq exit	Error?

	ldy #ItemFlag
	lda [<itemptr],y

;
; Take the word from the item flag and convert it to the format of a style word.
;
	tax
	and #I_Nobold+I_NoItalic+I_NoScore
	sta result,s
	txa
	and #I_NoShadow+I_NoOutline
	xba
	ora result,s
	sta result,s

exit	jsr unlockMenuBar	Leave menu bar & menus unlocked.

exit2	brl pop2bytes	no error

	ENDP


;===========================================================================
;
;	SetMItemFlag
;
;   IN:    PUSH:WORD - new bits for flag.
;          PUSH:WORD - item ID.
;
;  OUT:  None.
;
;===========================================================================
SetMItemFlag	PROC

itemnum	equ input
newvalue	equ itemnum+2

	jsr startup	Do startup initialization for tool call.
	jsr lockMenuBar	<barPtr = (<barHand), bar & menus locked.
	beq exit2	Is there a current menu bar?

	lda itemnum,s	Get item's ID.
	jsr getiptr	Now get its pointer.
	beq exit	Error?

	jsr badCache	Set cache to bad if	menu has a cache.

	ldy #ItemFlag
	lda newvalue,s
	bmi reset

	ora [<itemptr],y	Set desired bits.
	bra store

reset	and [<itemptr],y	Clear desired bits.
store	sta [<itemptr],y	Store new flag.

exit	jsr unlockMenuBar	Leave menu bar & menus unlocked.

exit2	brl pop4bytes	no error

	ENDP


;===========================================================================
;
;	CheckMItem
;
;   IN:    PUSH:WORD - TRUE to check, FALSE to uncheck.
;          PUSH:WORD - item's ID number.
;
;  OUT:    None.
;
;===========================================================================
CheckMItem	PROC

itemnum	equ input
newMark	equ itemnum+2

	jsr startup	Do startup initialization for tool call.
	jsr lockMenuBar	<barPtr = (<barHand), bar & menus locked.
	beq exit2	Is there a current menu bar?

	lda newMark,s
	beq setMark

	lda #$0012	Check mark.
	sta newMark,s
	bra setMark


; = = = = = = = = =	= = = = = = = = = = = = = = = = = = = = = =
;          Mark an item.
;
;   IN:    PUSH:WORD - character mark, zero for no mark.
;          PUSH:WORD - item's ID number.
;
;  OUT:    None.
; = = = = = = = = =	= = = = = = = = = = = = = = = = = = = = = =
	ENTRY SetMItemMark
SetMItemMark

	jsr startup	Do startup initialization for tool call.
	jsr lockMenuBar	<barPtr = (<barHand), bar & menus locked.
	beq exit2	Is there a current menu bar?

setMark	lda itemnum,s	Get item's ID.
	jsr getiptr	Now get its pointer.
	beq exit	Error?

	jsr badCache	Set cache to bad if	menu has a cache.

	ldy #ItemCheck
	lda [<itemptr],y
	and #$FF00	Clear current mark.
	ora newMark,s	Install new mark.
	sta [<itemptr],y

exit	jsr unlockMenuBar	Leave menu bar & menus unlocked.

exit2	brl pop4bytes	no error

	ENDP


;===========================================================================
;
;	GetItemMark
;
;          	Get an item's mark.
;
;   IN:    PUSH:WORD - item's ID number.
;
;  OUT:    WORD - item's mark, zero = no mark.
;
;===========================================================================
GetItemMark	PROC

itemnum	equ input
result	equ itemnum+2

	jsr startup	Do startup initialization for tool call.
	jsr lockMenuBar	<barPtr = (<barHand), bar & menus locked.
	beq exit2	Is there a current menu bar?

	lda itemnum,s	Get item's ID.
	jsr getiptr	Now get its pointer.
	beq exit	Error?

	ldy #ItemCheck
	lda [<itemptr],y
	and #$00FF	Get item's mark.
	sta result,s	Return mark to caller.

exit	jsr unlockMenuBar	Leave menu bar & menus unlocked.

exit2	brl pop2bytes	no error

	ENDP


;===========================================================================
;
;	GetItemFlag
;
;        	Return item's ItemFlag.
;
;   IN:  PUSH:WORD - item ID.
;
;  OUT:  WORD - Item's ItemFlag.
;
;===========================================================================
GetItemFlag	PROC

itemnum	equ input
result	equ itemnum+2

	jsr startup	Do startup initialization for tool call.
	jsr lockMenuBar	<barPtr = (<barHand), bar & menus locked.
	beq exit2	Is there a current menu bar?

	lda itemnum,s	Get item's ID.
	jsr getiptr	Now get its pointer.
	beq exit	Error?

	ldy #ItemFlag
	lda [<itemptr],y	Get current flag,
	sta result,s	return it to caller.

exit	jsr unlockMenuBar	Leave menu bar & menus unlocked.

exit2	brl pop2bytes	no error

	ENDP


;===========================================================================
;
;        	SetItemBlink
;
;   IN:  PUSH:WORD - number of times items should blink when selected.
;
;  OUT:  None.
;
;===========================================================================
SetItemBlink	PROC

new_blink	equ input

	jsr startup	Do startup initialization for tool call.

	lda new_blink,s
	sta <blink

	brl pop2bytes	no error

	ENDP

;===========================================================================
;
;        	GetItemBlink
;
;   IN:  none
;
;  OUT:  blink value (word).
;
; (New call 19-Sep-90 DAL)
;
;===========================================================================
GetMItemBlink	PROC

result	equ 7

	tax	;point X at our direct page
	lda >blink,x	;loads from Blink on Menu Mgr DP
	sta result,s
	clc
	lda #0
	rtl

	ENDP


;===========================================================================
;
;        	SetItemIcon
;
; This routine sets the ItemIcon field of the item structure referenced
; by the value now in the itemname field.
; The ItemFlag2 field in this structure is also set according to how
; the icon will be referenced.
;
;   IN:  PUSH:WORD - refdescriptor for icon data
;        PUSH:LONG - reference to icon data
;        PUSH:WORD - item ID
;
;  OUT:  None.
;
;===========================================================================
SetItemIcon	PROC

iconItemID	equ input
iconRef	equ iconItemID+2
iconVerb	equ iconRef+4

	jsr startup
	jsr lockmenubar
	beq Exit2

	lda iconItemID,s	Get item's ID.
	jsr getiptr	Now get its pointer.
	beq exit	Error?

	ldy #ItemFlag	First check if we've got our new style item record
	lda [<itemptr],y	that allows icons.
	and #I_NEWSTRUCTURE
	beq ERROR	If zero then item record not setup properly to handle icons.

	jsr GetStruct	Get pointer to this new structure.
	ldy #ItemFlag2
	lda [<temptr],y
	and #$FFFC	Clear bits 0 and 1 which indicate how the icon will be
	ora iconVerb,s	referenced and "OR" in new verb.
	ora #I_NOICON	Set bit in flag that tells us there is an icon associated w/item.
	sta [<temptr],y

	ldy #ItemIcon	Store the icon ref in our structure.
	lda iconRef,s
	sta [<temptr],y
	ldy #ItemIcon+2
	lda iconRef+2,s
	sta [<temptr],y

exit	jsr unlockmenubar

exit2	brl pop8bytes	no error

ERROR	jsr unlockmenubar
	ldy #NoStruct	error, "Invalid access of new item structure."
	brl epop8bytes

	ENDP


;===========================================================================
;
;        	GetItemIcon
;
;   IN:  PUSH:LONG - result containing reference to item's icon
;        PUSH:WORD - item ID
;
;  OUT:  LONG - Reference to item's icon. Result is zero if there is no icon.
;
;===========================================================================
GetItemIcon	PROC

iconItemID	equ input
result	equ iconItemID+2

	jsr startup
	jsr lockmenubar
	beq exit2

	lda #0	Initialize result to zero.
	sta result,s
	sta result+2,s

	lda iconItemID,s
	jsr getiptr
	beq exit	item not found

	ldy #ItemFlag	Check if correct flags are set to indicate use of the
	lda [<itemptr],y	new structure.
	and #I_NEWSTRUCTURE
	beq ERROR	If zero item record not setup to handle icons.

	jsr GetStruct	Get reference to new structure and put in <temptr.
	ldy #ItemFlag2	Make sure structure is using ItemIcon field.
	lda [<temptr],y
	and #I_NOICON
	beq exit	If not, then we're done.

	ldy #ItemIcon	 Get the reference to the icon and put in result.
	lda [<temptr],y
	sta result,s
	ldy #ItemIcon+2
	lda [<temptr],y
	sta result+2,s

exit	jsr unlockmenubar
exit2	brl pop2bytes

ERROR	jsr unlockmenubar
	ldy #NoStruct
	brl epop2bytes

	ENDP


;===========================================================================
;
;        	SetItemStruct
;
;   IN:  PUSH:WORD - ItemStructVerb, describes how STRUCT will be referenced
;        PUSH:LONG - ItemStructRef, ptr, hdl, resource ID to STRUCT
;        PUSH:WORD - ItemID, ID of item to set
;
;  OUT:  None.
;
; This call allows a menu item specified by ItemID to now be associated with
; a new structure. The ref. to this structure now resides in the ITEMNAME field
; of the item's record. Bits 10, 9, and 8 are automatically set. The ref to the
; item's name is then stored in this new structure.
;
;===========================================================================
SetItemStruct	PROC

itemnum	equ input
ItemStructRef	equ itemnum+2
ItemStructVerb	equ ItemStructRef+4

	jsr Startup
	jsr LockMenuBar
	beq exit2	If a reg is zero upon return then no menubar present.

	lda itemnum,s
	jsr getiptr	Returns ptr to item record in <itemptr
	beq exit	If a reg is zero upon return then item not found.

	jsr badCache

	ldy #ItemFlag	Set bit 10 in itemflag to indicate that the field
	lda ItemStructVerb,s itemname is now a Ref. to this new structure.
	xba	Also set bits 8 and 9 to reflect how this structure
	ora #I_NEWSTRUCTURE	will be referenced.
	ora [<itemptr],y
	sta [<itemptr],y

	ldy #ItemName+2	Save ref. to item's name on stack.
	lda [<itemptr],y
	pha
	ldy #ItemName
	lda [<itemptr],y
	pha

	lda ItemStructRef+4,s Now store the ref. to the struct in the itemname field.
	sta [<itemptr],y
	lda ItemStructRef+6,s
	iny
	iny
	sta [<itemptr],y

	jsr GetStruct	Returns a ptr to the new structure in <temptr.
	ldy #ItemName2	Store itemname in its new location.
	pla
	sta [<temptr],y
	pla
	iny
	iny
	sta [<temptr],y

exit	jsr unlockMenuBar
exit2	jml pop8bytes

	ENDP


;===========================================================================
;
;        	GetItemStruct
;
;   IN:  PUSH:LONG - Result, ref to item's struct is returned here
;        PUSH:WORD - ItemID, ID of item's struct you want
;
;  OUT:  None.
;
; If bit 10 is set, then this call returns the reference to the item's
; structure.
;
;===========================================================================
GetItemStruct	PROC

itemnum	equ input
result	equ itemnum+2

	jsr Startup
	jsr lockmenubar
	beq exit2	If a-reg is zero upon return then no menubar present.

	lda #0	Initialize result to zero for time being.
	sta result,s
	sta result+2,s

	lda itemnum,s
	jsr getiptr
	beq exit	If a-reg is zero upon return then item not found.

	ldy #ItemFlag	See if item has additional structure associated with it.
	lda [<itemptr],y
	and #I_NEWSTRUCTURE
	beq exit

	ldy #ItemName
	lda [<itemptr],y
	sta result,s
	iny
	iny
	lda [<itemptr],y
	sta result+2,s

exit	jsr unlockmenubar
exit2	jml pop2bytes

	ENDP


;===========================================================================
;
;        	RemoveItemStruct
;
;   IN:  PUSH:WORD - ItemID, ID of item's struct you want removed
;
;  OUT:  None.
;
;===========================================================================
RemoveItemStruct	PROC

itemnum	equ input

	jsr startup
	jsr lockmenubar
	beq exit2	If a-reg is zero upon return then no menubar present.

	lda itemnum,s
	jsr getiptr
	beq exit	If a-reg is zero upon return then item not found.

	ldy #ItemFlag
	lda [<itemptr],y
	and #I_NEWSTRUCTURE	First check to make sure there is a structure.
	beq exit

	jsr badCache

	jsr GetStruct	Move itemname ref from the structure back to the
	ldy #ItemName2+2	item's record.
	lda [<temptr],y
	tax
	ldy #ItemName2
	lda [<temptr],y
	ldy #ItemName
	sta [<itemptr],y
	iny
	iny
	txa
	sta [<itemptr],y

	ldy #ItemFlag
	lda [<itemptr],y
	and #$F8FF	Clear bits 10, 9, and 8.
	sta [<itemptr],y

exit	jsr unlockmenubar
exit2	jml pop2bytes

	ENDP


;===========================================================================
;
;        	GetItemFlag2
;
;   IN:  PUSH:WORD - Result
;        PUSH:WORD - ItemID, ID of item that you want flag for.
;
;  OUT:  None.
;
;===========================================================================
GetItemFlag2	PROC

itemnum	equ input
result	equ itemnum+2

	jsr startup
	jsr lockmenubar
	beq exit2	If a-reg is zero upon return then no menubar present.

	lda #0
	sta result,s

	lda itemnum,s
	jsr getiptr
	beq exit	If a-reg is zero upon return then item not found.

	ldy #ItemFlag
	lda [<itemptr],y
	and #I_NEWSTRUCTURE
	beq exit

	jsr GetStruct
	ldy #ItemFlag2
	lda [<temptr],y
	sta result,s

exit	jsr unlockmenubar
exit2	jml pop2bytes

	ENDP


;===========================================================================
;
;        	SetItemFlag2
;
;   IN:  PUSH:WORD - ItemFlag2, new value you want ItemFlag2 to be set to
;        PUSH:WORD - ItemID, ID of item that you want to set.
;
;  OUT:  None.
;
;===========================================================================
SetItemFlag2	PROC

itemnum	equ input
NewItemFlag2	equ ItemNum+2

	jsr startup
	jsr lockmenubar
	beq exit2	If a-reg is zero upon return then no menubar present.

	lda itemnum,s
	jsr getiptr
	beq exit	If a-reg is zero upon return then item not found.

	ldy #ItemFlag
	lda [<itemptr],y
	and #I_NEWSTRUCTURE
	beq exit

	jsr badCache

	jsr GetStruct
	ldy #ItemFlag2
	lda NewItemFlag2,s
	sta [<temptr],y

exit	jsr unlockmenubar
exit2	jml pop4bytes

	ENDP


;===========================================================================
;
;	PushDefBarRect
;
;          	Push address of a RAM data area value.
;
;===========================================================================
pushdefBarRect	PROC
	lda #defMenu+CtlRect
	bra pushData

	ENTRY pushmark
pushmark	lda #mark
	bra pushData

	ENTRY pushcom_key
pushcom_key	lda #com_key
	bra pushData

	ENTRY pushimage
pushimage	lda #image
	bra pushData

	ENTRY pushColorTable
pushColorTable	lda #ColorTable
	bra pushData

	ENTRY pushDefMenu
pushDefMenu	lda #defMenu
	bra pushData

	ENTRY pushport
pushport	lda #port


; = = = = = = = = =	= = = = = = = = = =	= = = = = = = = = = = = = = =
;          Push pointer to data area variable.
;
;   IN:    a = offset into data area.
;          <data = pointer to data area.
;
;  OUT:    <data+a on stack.
;100= = = = = = = =	= = = = = = = = = =	= = = = = = = = = = = = = = =
	ENTRY pushData
pushData	plx

	ldy <data+2
	clc
	adc <data
	bcc store100
	iny
store100	phy
	pha

	phx

	rts

	ENDP


;===========================================================================
;
;	CloseMenuPort
;
;          	Close Menu Manager's port.
;
;===========================================================================
closeMenuPort	PROC

	jsr pushport	Pass pointer to Menu Manager port.
	_ClosePort

	rts

	ENDP


;===========================================================================
;
;	PushColor2
;
;        	Get a solid color pattern
;
;  IN:   a = zero to use norcolor, not zero to use hiliteclr.
;
; OUT:   pointer to	pattern on stack.
;
;===========================================================================
pushcolor2	PROC

	ldy <norcolor
	tax
	beq ok
	ldy <hiliteclr
ok	tya

	ENTRY pushcolor
pushcolor

;  IN:   a = bits 7-4 equal color index.
;
	ply	Grab return address.

**  Replaced 26-Sep-90 DAL
**
**	pea color_patt>>16
**	and #$00F0
**	asl a
**	adc #color_patt

	entry SelfMod1High
SelfMod1High	pea $7777
	and #$00f0
	asl a
	entry SelfMOd1Low
SelfMod1Low	adc #$7777

	pha
	phy

	rts

	ENDP


;===========================================================================
;
;	Get_Apple
;
;        	Smear a mono bit image into color.
;
;  IN:   a = background color in bits 4-7.
;
; OUT:   x = high word address of pattern.
;        y = low word address of pattern.
;
;===========================================================================
get_apple	PROC

imagePtr	equ work	Pointer to image buffer.
background	equ imagePtr+4	Background color.
apple_mask	equ background+2	Pointer to image mask.
apple_data	equ apple_mask+2	Pointer to image data.

; --- Initialize for 320 mode -----------------
;
	and #$00F0
	asl a
***	tay
***	lda color_patt,y	;replaced 26-Sep-90 DAL
*** replaced above with below 26-Sep-90 DAL
	phx
	tax
	entry SelfMod2
SelfMod2	lda >$777777,x
	plx
*** end of 26-Sep-90 replacement

	sta <background

	jsr pushimage	Get address of 'image'.
	pla
	sta <imagePtr
	pla
	sta <imagePtr+2

	lda #_320_mask
	sta <apple_mask
	lda #_320_data
	sta <apple_data

	ldy #62

	lda <scInfo1	What mode are we in?
	and #$0080
	beq lop1

; --- Initialize for 640 mode ----------------
;
	lda #_640_mask
	sta <apple_mask
	lda #_640_data
	sta <apple_data

; --- Fill background around apple and put into image buffer ------------
;
	ldy #30
lop1	lda <background
	and (<apple_mask),y
	ora (<apple_data),y
	sta [<imagePtr],y	Store into 'image' buffer.
	dey
	dey
	bpl lop1

	rts

	ENDP


;===========================================================================
;
;	DrawRect
;
;        	Draw a solid rectangle with border.
;
;  IN:     x/a = address of RECT.
;          y = pattern/color.
;
;   Change History
;
;   18 Feb 23	Chris Parana
;
;===========================================================================


drawrect	PROC

	phx	; For draw line call.
	pha
	
	phx	; For fill call.
	pha
	
	tya
	jsr pushcolor	; Push pointer to color pattern.
	_FillRect	; Address of RECT already on stack.
	
	; Lots of help here from Antoine Vignau, Ian Brumby, Bobbi Webber-Manners, and the Apple2Infinitum Slack crew! 

	phd  ; Setup Direct Page
	tsc
	tcd
	
	ldy #02
	lda [3],y ; Left
	pha
	
	ldy #04
	lda [3],y ; Bottom
	dec A
	pha
	
	ldy #06
	lda [3],y ; Right
	pha
	
	ldy #04
	lda [3],y ; Bottom
	dec A
	pha

	_MoveTo	; Move to the starting point of the line
	_LineTo	; Draw the line to the end point
	

	pld ; Restore Direct Page
	pla
	plx
	
	; End of all the new stuff
	
	rts

	ENDP


;===========================================================================
;
;        	PrintStrg
;
;   IN:    strg_ptr	= string to print.
;          x = x poistion.
;          y = y position.
;
;===========================================================================
printstrg	PROC

	phx	Starting x position.
	phy	Starting y position.
	_MoveTo	Set pen's starting position.

	pei <strg_ptr+2	Pass pointer to string.
	pei <strg_ptr
	_DrawString

	rts

	ENDP


;            APPEND	MCACHE.ASM
;
;===========================================================================
;
;	Cache
;
;          	Fill cache.
;
;   IN:    menurect	= RECT to cache.
;          sav_buff	= handle of cache.
;
;  OUT:    a = TRUE	if menu image moved	from cache to screen.
;          a = FALSE if only screen saved, menu will have to be drawn.
;
;===========================================================================
cache	PROC

ssave	equ work	0
lmask	equ ssave+4	4
rmask	equ lmask+2	6
lsmask	equ rmask+2	8
rsmask	equ lsmask+2	10
lineAddr	equ rsmask+2	12
cWidth	equ lineAddr+2	14
cHeight	equ cWidth+2	16
cacheBuff	equ cHeight+2	18
;	                  	22
;
; --- Allocate temp	direct page ----------------------------------
;

temp1	equ temptr
temp2	equ temp1+2
tempY2	equ temptr2

	lda <menurect+y1	Just in case menu extends beyond the top of the screen
	sta <temp1	(a pop-up menu just might do this).
	bpl @1

	stz <temp1
@1
	lda <menurect+x1
	sta <temp2
	bpl @2

	stz <temp2
@2

	lda <menurect+y2	Check if the menu drops below the screen, if it
	cmp #200	does then we need to adjust it.
	bcc NotBelowScreen
	lda #200
NotBelowScreen	sta <tempY2

	_HideCursor

	ldy #2	Dereference cache handle.
	lda [<sav_buff],y
	sta <cacheBuff+2
	lda [<sav_buff]
	sta <cacheBuff

; --- Compute move parameters ---------------------------------------
;
	lda <screenmode
	bne mode640

; ------ 320 mode parameters ---------------------
;
	lda <temp2
	and #$FFFC
	sta <cWidth

	lda <menurect+x2
	tax
	and #$0003
	beq ok10
	txa
	and #$FFFC
	clc
	adc #$0004
	tax
ok10	txa
	sec
	sbc <cWidth
	bra enter1
;
; ------ 640 mode parameters ---------------------
;
mode640	lda <temp2
	and #$FFF8
	sta <cWidth

	lda <menurect+x2
	tax
	and #$0007
	beq ok11
	txa
	and #$FFF8
	clc
	adc #$0008
	tax

ok11	txa
	sec
	sbc <cWidth
	lsr a

enter1	lsr a	Get's number of bytes wide,
	dec a	make it zero relative.
	dec a
	sta <cWidth	Number of bytes wide.

	ldy #cacheWidth
	sta [<cacheBuff],y	Remember number of word wide.

	lda <tempY2	Get bottom of menu
	sec
	sbc <temp1
	sta <cHeight	Number of lines high.

	ldy #cacheHeight
	sta [<cacheBuff],y	Remember number of lines.

	lda <temp2
	and #$FFFC	320 mode.
	ldx <screenmode
	beq ok1
	and #$FFF8	640 mode.
	lsr a

ok1	lsr a
	tax	Word on line to start with.

	lda <temp1	Compute starting screen address.
	asl a
	tay
	txa
	clc
	adc [<lineTable],y
	sta <lineAddr
	ldy #cachey1x1
	sta [<cacheBuff],y	Remember starting line address.

; --- Perform move or exchange -----------------------------------------
;
	phb	Save caller's data bank pointer.
	ldy #port+4	Switch to menu manager's pixel map bank.
	lda [<data],y
	xba
	pha
	plb
	plb

	lda [<cacheBuff]	Is the menu image already cached?
	bne both

;----------------------------------------------------
;          Save screen to cache.
;----------------------------------------------------
;
	ldy #cacheCache	Starting pointer in	cache for data.

lop2	ldx <cWidth	Initialize bytes per line counter.
lop1	phy
	txy
	lda (<lineAddr),y	Fetch from screen,
	ply
	sta [<cacheBuff],y	store in cache.
	iny
	iny
	dex
	dex
	bpl lop1

	lda <lineAddr
	clc
	adc #160
	sta <lineAddr

	dec <cHeight
	bne lop2

	ldy #0	Menu not drawn from	cache flag.
	brl exit

;---------------------------------------------
;          Move cache to screen while
;          saving screen to cache.
;---------------------------------------------
both

save4	equ 1	Stack offsets.
Save3_5	equ 3	; damn that Dan O.
save3	equ 5
save2	equ 7
save1	equ 9
;
;
; --- Save tid-bits	------------------------------------
;
	lda <menurect+x2
	sec
	sbc #2
	ldx <screenmode
	beq ok4
	sbc #2

ok4	lsr a
	txy
	beq ok5
	lsr a

ok5	tax
	lda <temp1	Compute starting screen address.
	asl a
	tay
	txa
	clc
	adc [<lineTable],y
	tay
	lda |0,y
	pha	save1
	lda |160,y
	pha	save2
	lda |320,y
	pha	save3
	lda |480,y
	pha	save3_5

	lda <temp2
	lsr a
	ldx <screenmode
	beq ok6
	lsr a

ok6	tax
	lda <tempY2	Compute starting screen address.
	dec a
	asl a
	tay
	txa
	clc
	adc [<lineTable],y
	tay
	lda |0,y
	pha	save4

; --- Compute masks	for blit -----------------------------
;
	lda <temp2
	and #$0007
	ldy <screenmode	; changed to fix a dropshadow bug
	bne ok2
	and #$0003
	asl a
ok2	asl a
	tax
	lda >lmasks,x
	sta <lmask
	eor #$FFFF
	sta <lsmask

	lda <menurect+x2
	dec a
	and #$0007
	tyx	; changed to fix a dropshadow bug. Mensch
	bne ok3
	and #$0003
	asl a
	inc a	; fix purple haze problem
ok3	asl a
	tax
	lda >rmasks,x
	sta <rmask
	eor #$FFFF
	sta <rsmask

; --- Perform blit -------------------------------------------
;
	ldy #cacheCache	Starting pointer in	cache for data.

lop4	ldx <cWidth	Initialize bytes per line counter.

	lda [<cacheBuff],y	Fetch menu from cache and save.
	and <rmask
	sta <ssave

	phy
	txy
	lda (<lineAddr),y	Fetch from screen,
	sta <ssave+2	save.

	and <rsmask	Put menu on screen.
	ora <ssave
	sta (<lineAddr),y

	lda <ssave+2	Save screen in cache.
	ply
	sta [<cacheBuff],y

	iny
	iny
	dex
	dex

lop3	lda [<cacheBuff],y	Fetch menu from cache and save.
	sta <ssave

	phy
	txy
	lda (<lineAddr),y	Fetch from screen,
	sta <ssave+2	save.
	lda <ssave	Put menu on screen.
	sta (<lineAddr),y
	lda <ssave+2	Save screen in cache.
	ply
	sta [<cacheBuff],y

	iny
	iny
	dex
	dex
	bne lop3

	lda [<cacheBuff],y	Fetch menu from cache and save.
	and <lmask
	sta <ssave

	phy
	txy
	lda (<lineAddr),y	Fetch from screen,
	sta <ssave+2	save.

	and <lsmask	Put menu on screen.
	ora <ssave
	sta (<lineAddr),y

	lda <ssave+2	Save screen in cache.
	ply
	sta [<cacheBuff],y

	iny
	iny

	lda <lineAddr
	clc
	adc #160
	sta <lineAddr

	dec <cHeight
	bne lop4

; ------ Restore tid-bits ------------------------------------
;
; ------ Lower left	corner --------------------------------
;
	lda <temp2
	sta <ssave+2
	lsr a
	ldx <screenmode
	beq ok9
	lsr a
ok9	tax
	lda <tempY2	Compute starting screen address.
	dec a
	asl a
	tay
	txa
	clc
	adc [<lineTable],y
	sta <ssave

	lda <ssave+2
	ldx <screenmode
	bne Amode_640

	ldx #2
	and #1
	beq store1
	ldx #6
	bra store1

Amode_640	and #3
	asl a
	tax	Index to mask.
store1	lda >rmasks+8,x
	sta <rmask
	eor #$FFFF
	sta <rsmask

	lda save4,s
	and <rmask
	sta save4,s

	ldy <ssave
	lda |0,y
	and <rsmask
	ora save4,s
	sta |0,y

	lda <menurect+x2
	sec
	sbc #2
	ldx <screenmode
	beq ok7
	sbc #2
ok7	sta <ssave+2
	lsr a
	txy
	beq ok8
	lsr a
ok8	tax
	lda <temp1	Compute starting screen address.
	asl a
	tay
	txa
	clc
	adc [<lineTable],y
	sta <ssave

	lda <ssave+2
	ldx <screenmode
	bne mode_640

	and #1
	asl a

mode_640	and #3
	asl a
	tax	Index to mask.
	lda >lmasks,x
	sta <rmask
	eor #$FFFF
	sta <rsmask

	lda save1,s
	and <rmask
	sta save1,s

	lda save2,s
	and <rmask
	sta save2,s

	lda save3,s
	and <rmask
	sta save3,s

	lda save3_5,s
	and <rMask
	sta save3_5,s

	ldy <ssave
	lda |0,y
	and <rsmask
	ora save1,s
	sta |0,y

	lda |160,y
	and <rsmask
	ora save2,s
	sta |160,y

	lda |320,y
	and <rsmask
	ora save3,s
	sta |320,y

	lda |480,y
	and <rsMask
	ora save3_5,s
	sta |480,y

	pla	Get rid of save4.
	pla	Get rid of save3_5.
	pla	Get rid of save3.
	pla	Get rid of save2.
	pla	Get rid of save1.

; --- Return to caller -----------------------------------------
;
exit	plb	Restore caller's data bank pointer.
	phy	Save flag.
	_ShowCursor
	pla	Restore flag.

	rts

lmasks	DC.W $FFFF,$FF3F,$FF0F,$FF03,$FF00,$3F00,$0F00,$0300
rmasks	DC.W $00C0,$00F0,$00FC,$00FF,$C0FF,$F0FF,$FCFF,$FFFF

	ENDP


;===========================================================================
;
;          	UnCache
;
;   IN:    sav_buff	= handle of cache.
;
;===========================================================================
UnCache	PROC

saveCache	equ work
saveScreen	equ saveCache+2
lineAddr	equ saveScreen+2
cHeight	equ lineAddr+4
cWidth	equ cHeight+2
cacheBuff	equ cWidth+2

	_HideCursor

	ldy #2	Dereference cache handle.
	lda [<sav_buff],y
	sta <cacheBuff+2
	lda [<sav_buff]
	sta <cacheBuff

	ldy #cachey1x1
	lda [<cacheBuff],y	Starting screen address.
	sta <lineAddr

	ldy #cacheWidth	Number of bytes per	line.
	lda [<cacheBuff],y
	sta <cWidth

	ldy #cacheHeight	Number of lines.
	lda [<cacheBuff],y
	sta <cHeight

	phb	Save caller's data bank pointer.
	ldy #port+4	Switch to menu manager's pixel map bank.
	lda [<data],y
	xba
	pha
	plb
	plb

	ldy #cacheCache	Starting pointer in	cache for data.

lop2	ldx <cWidth	Initialize bytes per line counter.
lop1	lda [<cacheBuff],y
	sta <saveCache
	phy
	txy
	lda (<lineAddr),y
	sta <saveScreen
	lda <saveCache
	sta (<lineAddr),y
	ply
	lda <saveScreen
	sta [<cacheBuff],y
	iny
	iny
	dex
	dex
	bpl lop1

	lda <lineAddr	Next line.
	clc
	adc #160
	sta <lineAddr

	dec <cHeight	Any more lines?
	bne lop2

	plb	Restore caller's data bank pointer.

	lda #1	Mark cache as good.
	sta [<cacheBuff]

	_ShowCursor

	rts

	ENDP


;===========================================================================
;
;	MakeCache
;
;          	Allocate a cache for a menu.
;
;   IN:    menuptr = pointer to menu.
;          menuhand	= handle of menu.
;
;===========================================================================
makeCache	PROC

cBuff	equ work

	jsr allocateCache
	bcs exit	Was cache allocated?

	phx	Save allocated cache.
	pha

	ldy #MenuCache	Store cache handle in menu's record.
	pla
	tax
	sta [<menuptr],y
	iny
	iny
	pla
	sta [<menuptr],y

	pea 3	Pass purge level 3 (first to go).
	pha	Pass cache handle.
	phx

	jsr badCache	Dereference cahce and mark as bad.

	_SetPurge	Mark the cache as purgeable.

exit	rts

	ENDP


;===========================================================================
;
;	AllocateCache
;
;          	Allocate a menu cache.
;
;   IN:    menuptr = pointer to menu record.
;
;  OUT:    Carry clear if x/a = handle of cache, carry set if no cache.
;
;===========================================================================
allocateCache	PROC

cWidth	equ work
cHeight	equ cWidth+2

	ldy #MenuWidth
	lda [<menuptr],y	Width in pixels,
	clc
	ldx <screenmode
	bne mode640

	adc #2	plus 320 mode drop shadow width.
	bra ok2

mode640	adc #4	plus 640 mode drop shadow width.
	lsr a
ok2	lsr a
	clc
	adc #4
	sta <cWidth	Number of bytes per	line.
	and #1
	beq ok3
	inc <cWidth

; --- Allocate a cache buffer for the menu ----------------------------------
;
ok3	pha
	pha	Space for multiply result.
	pei <cWidth	Pass number of bytes per line.

	ldy #MenuHeight
	lda [<menuptr],y
*** added 25-Mar-93 DAL -- Clip the height to 200, because pop-up menus have
***   huge MenuHeight fields that do not correspond to the amount of memory
***   needed to save the screen.  In fact, they can get so big that the
***   following multiply comes out to more than $FFFF, and we ignore the
***   high word!
	cmp #200	does then we need to adjust it.
	bcc @notTooHuge
	lda #200
@notTooHuge
*** end 25-Mar-93
	inc a	plus room for the drop shadow
	sta <cHeight
	pha	Pass number of lines.

	_Multiply
	pla	Number of bytes needed.
	plx
	clc
	adc #cacheCache	Extra needed for header.
;	                  	Pass number of bytes to allocate in A.

	ldy <MyID	Pass ID to use.
	brl allocate2	Allocate memory for	the buffer.

	ENDP


;===========================================================================
;
;	BadCache
;
;          	Set cache to bad if menu has a cache.
;
;   IN:    menuptr = pointer to menu.
;
;===========================================================================
badCache	PROC

	ldy #MenuFlag	Check if there can be a cahce.
	lda [<menuptr],y
	and #M_CACHE
	beq exit

	ldy #MenuCache+1	Is there a cache?
	lda [<menuptr],y
	beq exit

	iny
	lda [<menuptr],y
	tax
	dey
	dey
	lda [<menuptr],y

;===========================================================================
;	BadCache2
;
;          	Dereference cahce and mark as bad.
;
;   IN:    x/a = handle of cache.
;
;  OUT:    work = pointer to cache, cache marked as bad (invalid image).
;
;===========================================================================
	ENTRY badCache2
badCache2

cBuff	equ work

	sta <cBuff	Dereference cahce.
	stx <cBuff+2

	ldy #2
	lda [<cBuff],y
	tay
	lda [<cBuff]
	sta <cBuff
	sty <cBuff+2

	lda #0	Mark cache as BAD (not containing menu).
	sta [<cBuff]

exit	rts

	ENDP


;===========================================================================
;
;	EveryCacheBad
;
;          	Set every menu's cache to bad.
;
;   IN:    barptr =	pointer to menu bar.
;
;===========================================================================
everyCacheBad	PROC

	jsr getmfirst	Start with first menu.
	beq exit	Are there any menus?

lop1	jsr badCache	Mark cache bad if menu has a cache.

	jsr next_menu	Try next menu.
	bne lop1	Any more menus?

exit	rts

	ENDP


;===========================================================================
;
;	FreeCache
;
;          	Free a menu's cache.
;
;   IN:    menuptr = pointer to menu.
;
;===========================================================================
freeCache	PROC

	ldy #MenuFlag	Check if there can be a cahce.
	lda [<menuptr],y
	and #M_CACHE
	beq exit

	ldy #MenuCache+1	Is there a cache?
	lda [<menuptr],y
	beq exit

	iny
	lda [<menuptr],y
	pha	Put handle of cache to be disposed of on
	dey	the stack
	dey
	lda [<menuptr],y
	pha

	ldy #MenuCache+1
	lda #0	Mark cache as gone.
	sta [<menuptr],y

	_DisposeHandle	Get rid of cache

exit	rts

	ENDP


;===========================================================================
;
;	EveryCacheFree
;
;          	Free every menu's cache.
;
;   IN:    barptr =	pointer to menu bar.
;
;===========================================================================
everyCacheFree	PROC

	jsr getmfirst	Start with first menu.
	beq exit	Are there any menus?

lop1	jsr freeCache	Mark cache bad if menu has a cache.

	jsr next_menu	Try next menu.
	bne lop1	Any more menus?

exit	rts

	ENDP

****************************************************************
*
TextFaceRoutines	PROC
*
* Sets and Clears the text face field in the grafport
* as specified in the item flag.
*
*
* Inputs:
*	none
*
* Outputs:
*	none
*
* External Refs:
*	none
*
* Entry Points:
	ENTRY FixTextFace
	ENTRY ClearTextFace
*
	longa on	; mode
	longi on
*
****************************************************************

FixTextFace
;-----------------------------------------------------------
;
; bold, underline and italic are kept in the low three bits
; of the flag.
;
; We merge these with Shadow and Outline kept in bits
; 11 and 12.
;

	ldy #ItemFlag		Get the flag
	lda [<itemptr],y
	tax		save it here
	and #$0007		low 3 bits
	pha		save it
	txa		get flag back
	and #I_NOOUTLINE+I_NOSHADOW	remove unwanted bits
	xba		put high into low
	ora 1,s		merge with rest
	sta 1,s		store it
GoBack	_SetTextFace

	rts

ClearTextFace
	pea $0000
	bra GoBack


	ENDP

	EJECT
*******************************************************************************
*
PushPortData	PROC EXPORT
*
* Description:	This routine will push grafport variables that can be changed
*	by menuselect and popupmenuselect. This pushes:
*	BkPat
*	PnLoc
*	pnSize
*	pnMode
*	pnPat
*	pnMask
*	pnVis
*	fontHandle
*	fontID
*	fontFlags
*	txSize
*	txFace
*	txMode
*	spExtra
*	chExtra
*	fgColor
*	bgColor
*
*
* Inputs:	None
*
* Outputs:	All that stuff on the stack!
*
* External Refs:
*
* Entry Points:
*
*******************************************************************************
*
* Direct page equates for my stack frame, note that I will leave this data on the
* stack and take it off with popPortData
*
FrameSize	equ $74	; 70 bytes of data + grafport pointer
portPtr	equ 1	; the place we will use for our grafport pointer
LocalPortData	equ portPtr+4	; storage area for our port pointer
;
; First set up our stack frame...
	ply	; recover the return address and save it...
	tdc	; get the current dpage
	tax	; and save it in <X>

	tsc	; get the stack pointer
	sec
	sbc #FrameSize	; adjust the stack pointer
	tcs	; make it the new stack pointer and the new
	tcd	; direct page

	phy	; restore the return address
	phx	; and save the old dpage pointer

; Now get the current grafport pointer
	pha	; room for result
	pha
	_GetPort	;
	pla
	sta <portPtr	; and save the port pointer to our dpage
	pla
	sta <portPtr+2	;

; now copy $70 bytes of data to our localportdata area

	ldy #$8E	; last address to copy from
	ldx #$6E	; last data to copy
@CopyLoop	lda [<portPtr],y	; get the byte of data
	sta <LocalPortData,x ; and save it
	dey
	dey
	dex
	dex
	bpl @CopyLoop

; now that we are done, lets get the proper direct page off the stack and end...
	pld
	rts	; now leave


	EJECT
*******************************************************************************
*
PopPortData	PROC EXPORT
*
* Description:	This routine will pop grafport variables that can be changed
*	by MenuSelect and PopUpMenuSelect.
*
*             NOTE: You must have called PushPortData first, and the stack must
*	be set to what it was when pushPortData returned.
*
*        This pops:
*	BkPat
*	PnLoc
*	pnSize
*	pnMode
*	pnPat
*	pnMask
*	pnVis
*	fontHandle
*	fontID
*	fontFlags
*	txSize
*	txFace
*	txMode
*	spExtra
*	chExtra
*	fgColor
*	bgColor
*
*
* Inputs:	None
*
* Outputs:	All that stuff on the stack!
*
* External Refs:
*
* Entry Points:
*
*******************************************************************************
*
* Direct page equates for my stack frame, note that I will leave this data on the
* stack and take it off with popPortData
*
FrameSize	equ $74	; 70 bytes of data + grafport pointer
savedDPage	equ 1
Rtn1	equ savedDPage+2
portPtr	equ Rtn1+2	; the place we will use for our grafport pointer
LocalPortData	equ portPtr+4	; storage area for our port pointer
; first copy $70 bytes of data from our localportdata area to the port
	phd	; save the old dPage
	tsc	; now make the stack the dPage
	tcd

	ldy #$8E	; last address to copy from
	ldx #$6E	; last data to copy
@CopyLoop
	lda <LocalPortData,x ; and save it
	sta [<portPtr],y	; get the byte of data
	dey
	dey
	dex
	dex
	bpl @CopyLoop

; Now that we are finished, reset the old dPage and pull all the old shit
; off the stack

*** added 16-Jan-91 DAL to make this thing work with fastPort on!
*** Just set the port to what it already is to clear the fastPort
*** dirty flags & make items always hilite properly. BRC:MS902MSC.
	pha
	pha
	_GetPort
	_SetPort
*** end of 16-Jan-91 DAL fix

	pld	; restore the directpage
	ply	; save the return address for a sec...

	tsc	; now adjust the stack pointer
	clc
	adc #FrameSize
	tcs	; and resave the stack pointer
	phy	; restore the return address
	rts	; now leave



;===========================================================================
;
;	StaticRAM
;
;        	Menu Manager static data.
;
;   Change History
;
;   22 Jan 23	Chris Parana
;
;===========================================================================
staticRAM	PROC

;
;
; --- New 320 mode Apple logo ---------------------------------------
;
	ENTRY _320_mask
_320_mask	DC.B $FF,$FF,$FF,$FF,$F0,$0F,$FF,$FF
	DC.B $FF,$FF,$FF,$FF,$00,$FF,$FF,$FF
	DC.B $FF,$FF,$00,$00,$F0,$00,$0F,$FF
	DC.B $FF,$F0,$00,$00,$00,$00,$FF,$FF
	DC.B $FF,$F0,$00,$00,$00,$0F,$FF,$FF
	DC.B $FF,$F0,$00,$00,$00,$00,$FF,$FF
	DC.B $FF,$FF,$00,$00,$00,$00,$0F,$FF
	DC.B $FF,$FF,$F0,$00,$F0,$00,$FF,$FF

	ENTRY _320_data
_320_data	DC.B $00,$00,$00,$00,$01,$20,$00,$00
	DC.B $00,$00,$00,$00,$12,$00,$00,$00
	DC.B $00,$00,$11,$12,$02,$11,$20,$00
	DC.B $00,$01,$11,$11,$11,$11,$00,$00
	DC.B $00,$01,$11,$11,$11,$10,$00,$00
	DC.B $00,$02,$11,$11,$11,$12,$00,$00
	DC.B $00,$00,$11,$11,$11,$11,$20,$00
	DC.B $00,$00,$01,$12,$02,$11,$00,$00

;
; --- New 640 mode Apple logo -------------------------------------------
;
	ENTRY _640_mask
_640_mask	DC.B $FF,$FF,$F0,$FF
	DC.B $FF,$FF,$0F,$FF
	DC.B $F0,$03,$F0,$03
	DC.B $00,$00,$00,$0F
	DC.B $C0,$00,$00,$3F
	DC.B $C0,$00,$00,$0F
	DC.B $F0,$00,$00,$03
	DC.B $FC,$00,$C0,$0F

	ENTRY _640_data
_640_data	DC.B $00,$00,$05,$00
	DC.B $00,$00,$90,$00
	DC.B $09,$54,$09,$58
	DC.B $95,$55,$55,$60
	DC.B $95,$55,$55,$80
	DC.B $25,$55,$55,$50
	DC.B $09,$55,$55,$54
	DC.B $02,$56,$25,$60

;
; --- Down Arrow for Scrolling Menus -------------------------------------
;
	ENTRY DownArrowLocInfo640
DownArrowLocInfo640
	dc.w $80
	dc.L DownArrowIcon
	dc.w 4
	ENTRY DownArrowBounds640
DownArrowBounds640	dc.w 0,0,8,16


	ENTRY DownArrowLocInfo320
DownArrowLocInfo320
	dc.w $00
	dc.L DownArrowIcon
	dc.w 4
	ENTRY DownArrowBounds320
DownArrowBounds320	dc.w 0,0,8,8


	ENTRY DownArrowIcon
DownArrowIcon	dc.b $FF,$FF,$FF,$FF	; down arrow image
	dc.b $FF,$FF,$FF,$FF
	dc.b $00,$00,$00,$00
	dc.b $F0,$00,$00,$0F
	dc.b $FF,$00,$00,$FF
	dc.b $FF,$F0,$0F,$FF
	dc.b $FF,$FF,$FF,$FF
	dc.b $FF,$FF,$FF,$FF

;
; --- Up Arrow for Scrolling Menus ---------------------------------------
;
	ENTRY UpArrowLocInfo640
UpArrowLocInfo640
	dc.w $80
	dc.L UpArrowIcon
	dc.w 4
	ENTRY UpArrowBounds640
UpArrowBounds640	dc.w 0,0,8,16


	ENTRY UpArrowLocInfo320
UpArrowLocInfo320
	dc.w $00
	dc.L UpArrowIcon
	dc.w 4
	ENTRY UpArrowBounds320
UpArrowBounds320	dc.w 0,0,8,8


	ENTRY UpArrowIcon
UpArrowIcon	dc.B $FF,$FF,$FF,$FF	; up arrow image
	dc.B $FF,$FF,$FF,$FF
	dc.B $FF,$F0,$0F,$FF
	dc.B $FF,$00,$00,$FF
	dc.B $F0,$00,$00,$0F
	dc.B $00,$00,$00,$00
	dc.B $FF,$FF,$FF,$FF
	dc.B $FF,$FF,$FF,$FF

;
; --- Tables for setting SCB and color tables for color apple logo --------
;

; New Primary Colors
	ENTRY logocolora
logocolora	DC.W $00B0
	DC.W $0FE0
	DC.W $0F60
	DC.W $0E10
	DC.W $0D2A
	DC.W $014F
	
; New Secondary Colors	
	ENTRY logocolorb
logocolorb	DC.W $0AD9
	DC.W $0FFB
	DC.W $0FA7
	DC.W $0E99
	DC.W $0E7C
	DC.W $077E
	
	ENTRY scanbyte
scanbyte	DC.B 1
	DC.B 1
	DC.B 1
	DC.B 2
	DC.B 3
	DC.B 4
	DC.B 5
	DC.B 6

;
; --- Masks for dimmed and normal text -----------------------------

	ENTRY dimmed
dimmed	DC.B $55,$AA,$55,$AA,$55,$AA,$55,$AA
	ENTRY nor_mask
nor_mask	DC.B $FF,$FF,$FF,$FF,$FF,$FF,$FF,$FF

;
;------------------------------------------------------------
;          Data used to initialize RAM data area.
;------------------------------------------------------------
;
	ENTRY startInitRAM
startInitRAM
	DC.B $01,$00,$00
	DC.B $02,$11,$00,$00

;
; +++ The following	blocks give information to QuickDraw about the
;     structure of screen RAM and data to use when moving data to or from
;     the screen.

	DC.B 0	Scan line control byte.
	DC.B 0	Reserved.
	DC.L $E12000	Starting address of	screen.
	DC.W 160	Number of bytes per	line.
	DC.W 0,0,200,320	Bounds of screen.

	DC.B 0	Scan line control byte.
	DC.B 0	Reserved.
	DC.L 0	Starting address of	image.
	DC.W 0	Number of bytes per	line.
	DC.W 0,0,0,0	Bounds of image.

	DC.W 1
	DC.W 1
	DC.W 0,0,8,16	Size of destination.

;
; +++ The following	blocks give information to QuickDraw about the
;     structure of screen RAM and data to use when moving data to or from
;     the screen.
;
	DC.B 0	Scan line control byte.
	DC.B 0	Reserved.
	DC.L 0	Starting address of	image.
	DC.W 8	Number of bytes per	line.
	DC.W 0,0,8,16	Bounds of image.

;
; --- Default System Menu Bar Template ---------------------------
;
	DC.L 0	Next Control.
	DC.L 0	Menu owner.
	DC.W 0,0,13,320	MenuBar RECT.
	DC.B $00	Flag, visible
	DC.B $0A	Hilite, active, low byte is where 1st menu starts
	DC.W 0	Value.
	DC.L 12	Menu bar definition	procedure flag.
	DC.L 0	Default action procedure, none.
	DC.L 0	Data.
	DC.L 0	RefCon.
	DC.L 0	Pointer to color table, default.
	DC.L 0	Handle of first menu in menu bar.
;
;
; --- Default menu bar color table ---------------------------
;
	ENTRY DefColorTable
DefColorTable	DC.W $00F0	Normal color, black	text on white.
	DC.W $000F	Hilited color, white text on black.
	DC.W $0000	Outline color, black.

	ENTRY endInitRAM
endInitRAM

	ENDP


***********************************************************************************
*
* InsertPathMItems -- new call 10-Jan-91 Dave Lyons
*
* Description:
*
* Takes a word-length pathname string and makes a series of InsertMItem2 calls for
* you, one for each segment of the pathname.  Each item gets an appropriate
* little icon next to it, as returned from GetSysIcon (in QD Aux).
*
* Inputs:
*
* $500F InsertPathMItems(flags: integer; thePath: longint;
*                        MenuID: integer; AfterItemID: integer;
*                        StartingItemID: integer; ResultPtr: Ptr);
*
* flags	bits 15-5 reserved (use 0)
*	bit 4 = the pathname is already fully expanded (no need for me to
*	        call ExpandPath on it) (not used yet)
*	bit 3 = 1=theDevNum is valid, 0=ignored
*                   bit 2 = 1=use Open folder icons
*	        0=use Closed folder icons
*	bit 1 = reserved (0)
*	bit 0 = 0=insert items with Device at bottom
*	        1=insert items with Device at top
* thePath	Word-length string--a complete GS/OS pathname.  This string
*	is preserved, not munged.
* theInputDevNum	Device number of the device the pathname is on, if bit 3 of flags is set.
* MenuID	The MenuID of the menu to insert into (passed to InsertMItem2)
* AfterItemID	The Menu Item ID to insert AFTER, in the specified menu.
* StartingItemID	The Menu Item ID for the first item to be inserted (we build
*	up sequentially from there).
* ResultPtr	Pointer to results buffer.
*	+000 Word  receives highest menu item ID that was inserted
*	+002 Long  receives the itemStructs handle (caller must dispose later)
*	+006 Long  receives a handle containing the expanded and munged-up path
*	           (caller must dispose later)
*
***********************************************************************************
InsertPathMItems	proc export

	phb
	phk
	plb

	phd

	phy
	pha	;pushed WAP
	pha
	pha	;pushed space for ItemStructList
	tsc
	tcd

ItemStructList	equ 1
MenuWAP	equ ItemStructList+4
oldD	equ MenuWAP+4
oldB	equ oldD+2
rtl1	equ oldB+1
rtl2	equ rtl1+3
ResultPtr	equ rtl2+3
theStartingID	equ ResultPtr+4
AfterItemID	equ theStartingID+2
theMenuID	equ AfterItemID+2
theInputDevNum	equ theMenuID+2
thePath	equ theInputDevNum+2
theFlags	equ thePath+4

	jsl DoInsertItems	;returns error code in A
	tax

	ply
	ply	;removed ItemStructList
	ply
	ply	;removed WAP

	pld
	plb

	ldy #18	;strip input parameters from the stack
	jml $e10184


*** DoInsertItems -- do the work, return error in A

exitError	rtl

DoInsertItems	jsr ExpandThePath	;result pointer in thePath if no error
	bcs exitError

*** We've now got a copy of the fully-expanded pathname at <thePath.

	jsr GetDeviceID	;input=thePath, output=A

*** Figure out how many items we're going to insert, by simply counting the
*** colons in the input string

	lda [<thePath]
	inc a
	inc a
	sta Length

	ldx #0	;number of items
	ldy #2
@count	cpy Length
	bcs @counted
	lda [<thePath],y
	and #$00ff
	cmp #':'
	bne @notColon
	inx
@notColon	iny
	bra @count
@counted	txa
	sta NumberOfSegments

*** Allocate 10 bytes per Item Struct that we'll need, and put a pointer
*** to this thing into [<ResultPtr] and <ItemStructList

	inc a	;extra item struct in case we're doing a Desktop item

	pha
	pha	;space for Multiply result
	phx
	pea 10
	_Multiply	;space needed is on stack
	pla
	ply	;ignore high word
	jsr MyAllocate	;returns pointer to locked handle in YX
	bcc @ok
	brl ExitError

@ok	sty <ItemStructList+2
	stx <ItemStructList

	tya
	ldy #4
	sta [<ResultPtr],y
	dey
	dey
	txa
	sta [<ResultPtr],y

;	ldy #2	;Y is already 2
	lda [<ItemStructList]
	tax
	lda [<ItemStructList],y
	sta <ItemStructList+2
	stx <ItemStructList

*** Set up the highest item so far to be theStartingID minus one, since
*** we increment it before using it for the first time

	lda <theStartingID
	dec a
	sta [<ResultPtr]

; Replace each seperator character (except the last trailing one) with
; a length byte, forming a series of PStrings.

	ldy #2

	sep #$20
	longa off
SearchLoop2	ldx #0	; Initialize character counter
	cpy Length	; Are we done?
	bcc @1
	brl SearchDone

@1	sty Index	; Store position of separator character
	iny	;   and begin at next character

	rep #$20
	lda [<ResultPtr]
	inc a
	sta [<ResultPtr]
	sta MenuItemID
	sep #$20

SearchLoop1	lda [<thePath],y	; Search for separator characters
	cmp #':'
	beq CreateLengthByte

	cpy Length	; End of string ?
	beq CreateLengthByte

	iny
	inx
	bra SearchLoop1

CreateLengthByte	phy

	txa	; Replace the separator character
	ldy Index	;  with a length byte
	sta [<thePath],y

	longa on
	rep #$20

*** Store pointer to the current ItemStruct into the item template

	lda <ItemStructList
	sta ItemStructPtr
	lda <ItemSTructList+2
	sta ItemStructPtr+2

;       Store the ItemStruct's ItemFlag2

	lda #$8000	; Item has an icon
	sta [<itemStructList]

;       Store the ItemStruct's ItemTitleRef pointer

	ldy #2
	clc
	lda Index
	adc <thePath
	sta [<itemStructList],y
	iny
	iny
	lda #0
	adc <thePath+2
	sta [<itemStructList],y

;       Store the ItemStruct's ItemIconRef pointer

*** Call GetSysIcon to get an icon

	pha
	pha		;space for GetSysIcon result

	lda <theFlags
	and #$0004		;Open/Closed folders bit
	tax		;flags (bit 1-0:00=file icon)
	ldy #$000f		;Folder filetype
	lda [<ResultPtr]		; If this is the first item, we need
	cmp <theStartingID		; a disk icon
	bne @aFile

	ldy theDeviceID
	ldx #1		;flag bits 1-0=01 for a device

@aFile	phx		;flags
	phy		;value (filetype or dev_id)
	lda #0
	pha
	pha		;aux value (long)
	_GetSysIcon
	plx
	pla

*** StoreIcon -- Icon is in AX

StoreIcon	ldy #8	; Store ItemIconRef pointer
	sta [<itemStructList],y
	txa
	dey
	dey
	sta [<itemStructList],y

*** Bump ItemStructList to the next one

	clc
	lda <itemStructList
	adc #10
	sta <itemStructList
	bcc @1
	inc <itemStructList+2
@1

*** Finally!  Insert the item into the menu.

	pea 0	; refDescriptor (pointer)
	pushlong #MenuItem	; menuItemTRef
	pei <AfterItemID	; 11-Jan-91 DAL
	pei <theMenuID
	_InsertMItem2
*** %%% check for error

* If flag bit 0 is set, the next item should be inserted after this one
	lda <theFlags
	lsr a
	bcc @forward
	lda [<ResultPtr]
	sta <AfterItemID	;next one to insert after
@forward

	sep #$20
	longa off

	ply
	brl SearchLoop2


; We've inserted all the items

SearchDone
	longa on
	rep #$20

	lda #0
	pha
	pha
	pei <theMenuID
	_CalcMenuSize

	rtl		;return error code in A

*
* GetDeviceID
*
* For the pathname at thePath, return the device id in theDeviceID
*
GetDeviceID	lda #$ffff
	sta theDeviceID

	ldx <theInputDevNum
	lda <theFlags
	and #$0008	;bit 3 = theDevNum is valid
	bne @gotDevNum

	lda <thePath
	sta GetDevNumPath
	lda <thePath+2
	sta GetDevNumPath+2

	pushlong #GetDevNumParms
	pea $2020	;GetDevNumber
	jsl $e100b0
	bcs @exit

	ldx theDevNum
@gotDevNum	stx DInfoDevNum
	inx	;added 22-Feb-91 DAL
	beq @exit	;added 22-Feb-91 DAL
	pushlong #DInfoParms
	pea $202C	;DInfo
	jsl $e100b0
@exit	rts

GetDevNumParms	dc.w 2
GetDevNumPath	dc.l 0
theDevNum	dc.w 0

DInfoParms	dc.w 8	;8 parameters
DInfoDevNum	dc.w 0
	dc.l deviceName
	dc.w 0	;characteristics
	dc.l 0	;total blocks
	dc.w 0	;slot num
	dc.w 0	;unit num
	dc.w 0	;version
theDeviceID	dc.w 0	;device id

deviceName	dc.w 35	;room for a 31-character device name
	ds.b 33



Index	ds.w 1	; Stores location of separator char
Length	ds.w 1	; Stores length of original pathname string
TempHdl	ds.l 1

NumberOfSegments	dc.w 0	;number of items we're going to insert

MenuItem		   ; Menu Item Template
	dc.w $0000	   ; version
MenuItemID	dc.w $0000	   ; itemID
	dc.b $00	   ; itemChar
	dc.b $00	   ; itemAltChar
	dc.w $0000	   ; itemCheck	 / additional ItemStruct
	dc.w %0000010000100000 ; itemFlag   =	<  XOR mode)
ItemStructPtr	dc.l $00000000	   ; itemStructRef	 \ ItemStrucRef is pointer

*
* ExpandThePath
*
* Input: pointer to user's path in <thePath
*
* Output: pointer to a fully expanded path, in our own handle, in <thePath
*         A/Carry=error code
*
ExpandThePath	lda <thePath+2
	ldy <thePath
	sta ep1Input+2
	sty ep1Input
	sta ep2Input+2
	sty ep2Input

*** First, do an expand path just to see how much room we need
	pushlong #FirstExpPath
	pea $200E	;ExpandPath
	jsl $e100b0
	bcc @noError	;added 7-Dec-91
	cmp #$4f
	bne @error

@noError
	lda SizeNeeded
	clc
	adc #4
	sta SizeNeeded
	jsr MyAllocate
	bcs @error

	sty <thePath+2
	stx <thePath

*** Store a copy of the handle into [<ResultPtr],6 so the caller
*** can dispose of it when they're ready to.
	tya
	ldy #6+2
	sta [<ResultPtr],y
	dey
	dey
	txa
	sta [<ResultPtr],y

*** Deref the handle (it's locked & fixed)
	lda [<thePath]
	tax
	ldy #2
	lda [<thePath],y
	sta <thePath+2
	stx <thePath
	sta ep2Output+2
	stx ep2Output

	lda SizeNeeded
	sta [<thePath]

	pushlong #SecondExpPath
	pea $200E	;ExpandPath
	jsl $e100b0	;keep error code

	pha
	clc
	lda <thePath
	adc #2
	sta <thePath
	bcc @1
	inc <thePath+2
@1	pla

	cmp #1	;condition carry
	rts

@error	sec
	rts

FirstExpPath	dc.w 2
ep1Input	dc.l 0
	dc.l theBuffer
theBuffer	dc.w 4
SizeNeeded	dc.w 0

SecondExpPath	dc.w 3
ep2Input	dc.l 0
ep2Output	dc.l 0
	dc.w 0	;don't convert to uppercase

*
* MyAllocate--size in A, returns handle in YX (or SEC, A=error)
*
MyAllocate	pha
	pha	;space for result
	pea 0	;high word of size
	pha	;size
	ldy #MyID
	lda [<MenuWAP],y
	pha	;mem id
	pea $c010	;locked, fixed, no bank cross
	pha
	pha	;location pointer (ignored)
	_NewHandle
	plx
	ply
	rts

	EndP

	END
