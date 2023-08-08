----------------------------- MODULE Directory -----------------------------
(*EXTENDS Memory, TLAPS*)
EXTENDS TLAPS, Naturals, FiniteSets, Sequences


VARIABLES directory, (* the current directory*) 
    has_been_tested, (* IF test has been performed THEN TRUE ELSE FALSE*)
    is_proved,       (* IF proved that directory is OK THEN TRUE ELSE FALSE *)
    is_error         (* IF (raise exception OR excepetion already raised*) 
                     (* THEN TRUE ELSE FALSE.*)
                     
(* Type specifies the criteria our input directory must meet:*)
Type == [
    (* directory has a preferences subdirectory directory/preferences.*)
    preferences: [
        (* directory/preferences MUST exist AND denote a directory.*)
        is_dir:{TRUE, FALSE},
        (* directory/preferences MUST enclose a preferences JSON file
        preferences.JSON. *) 
        has_file: {TRUE, FALSE}
    ]
    (* TODO: Enrich the spec with the below constraints:
    ,input: [
        (*path: {"root/input/markdown/mainmatter"}*)
        is_dir:{TRUE, FALSE},
        has_file: {TRUE, FALSE}
        (*path: {"root/input/markdown/mainmatter/mainmatter.md"}*)
    ]*)
]


(* Convenience operator; see definition of Type. *)
(* Variables a, b must be boolean.               *)
Directory(a, b) == 
    /\ directory.preferences.is_dir   = a
    /\ directory.preferences.has_file = b

(* Initial condition.*)
Init ==  
    /\ directory \in Type
    /\ Directory(FALSE, FALSE)
    /\ has_been_tested = FALSE
    /\ is_proved       = FALSE
    /\ is_error        = FALSE


(* Catch the exception "no such directory "preferences".*)
NextSystemIsDirRAISE_EXCEPTION == 
    /\ directory \in Type
    /\ Directory(FALSE, FALSE)
    /\ has_been_tested = TRUE
    /\ is_proved       = FALSE
    /\ is_error        = FALSE
    /\ UNCHANGED directory 
    /\ UNCHANGED has_been_tested 
    /\ UNCHANGED is_proved
    /\ is_error' = TRUE 

(* Raises the above exception.*)
isDirERROR == 
    /\ directory \in Type
    /\ Directory(FALSE, FALSE)
    /\ has_been_tested = TRUE
    /\ is_proved       = FALSE
    /\ is_error        = TRUE
    /\ UNCHANGED directory 
    /\ UNCHANGED has_been_tested 
    /\ UNCHANGED is_proved
    /\ UNCHANGED is_error

(* State: Directory exists and is OK.*)
isDirSUCCESS == 
    /\ directory \in Type
    /\ Directory(TRUE, FALSE)
    /\ has_been_tested = TRUE
    /\ is_proved       = TRUE
    /\ is_error        = FALSE
    /\ UNCHANGED directory 
    /\ UNCHANGED has_been_tested 
    /\ UNCHANGED is_proved
    /\ UNCHANGED is_error

(* Be prepared to perform the is-a-directory check:*)
NextSystemCHECKisDir ==  
    /\ Init 
    /\ directory' \in Type

(* Such text is actually a success.*) 
NextSystemIsDirSUCCESS == 
    /\ NextSystemCHECKisDir
    /\ Directory(TRUE, FALSE)'
    /\ has_been_tested' = TRUE
    /\ is_proved'       = TRUE
    /\ is_error'        = FALSE

(* Such text leads to the "no such directory "preferences" exception.*)    
NextSystemIsDirFAILURE == 
    /\ NextSystemCHECKisDir
    /\ Directory(FALSE, FALSE)'
    /\ has_been_tested' = TRUE
    /\ is_proved'       = FALSE
    /\ is_error'        = FALSE

(* The Next action combines the above Next subactions: *)
Next == 
    \/ NextSystemIsDirSUCCESS
    \/ NextSystemIsDirFAILURE
    \/ NextSystemIsDirRAISE_EXCEPTION 
    \/ isDirERROR
    \/ isDirSUCCESS

var == <<directory, has_been_tested, is_proved, is_error>>

Spec == Init /\ [][Next]_var


=============================================================================
\* Modification History
\* Last modified Tue Aug 08 17:37:13 CEST 2023 by gcordier
\* Created Tue Aug 08 16:52:36 CEST 2023 by gcordier
