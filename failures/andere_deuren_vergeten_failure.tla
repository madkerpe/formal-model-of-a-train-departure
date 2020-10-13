---- MODULE andere_deuren_vergeten_failure ----
EXTENDS Naturals
VARIABLES system

trein_waarden == {"perron", "vertrokken"}
deur_waarden == {"open", "dicht"}
begeleider_waarden == {"perron", "trein"}
AC_waarden == {"aan", "uit"}
licht_waarden == {"uit", "rood", "wit"}
bestuurder_waarden == {"wacht", "wil_vertrekken"}
startuur_waarden == {"aangebroken", "n_aangebroken"}
spoor_waarden == {"vrij", "n_vrij"}

BAB_waarden == {"aan", "uit"}


TypeInvariant == system \in [trein: trein_waarden, deur_beg: deur_waarden,
   deur_rest: deur_waarden, begeleider: begeleider_waarden, AC: AC_waarden,
   licht: licht_waarden, bestuurder: bestuurder_waarden, startuur: startuur_waarden, 
   spoor: spoor_waarden, BAB: BAB_waarden]

----

(* 
   Probleem was duidelijk: niks verplicht de begeleider van op te stappen binnen de 10 seconden

   1. Begeleider genereert AC
   2. Begeleider gaat op de trein en sluit alle deuren behalve die van zichzelf
   3. De begeleider controleert of alle deuren gesloten zijn (behalve één)
   4. De begeleider sluit zijn eigen deur en genereert daarmee een BAB-signaal (Begeleider Aan Boord)
   5. Trein vertrekt

   ---> Ik heb hier wel enkel hardware-veranderingen verondersteld (Een extra signaal BAB met een indicator voor de bestuurder)
*)

(*
   CHANGELOG

    -> Variabelen
        +BAB (Begeleider Aan Boord) + Initiële waarde op "uit"


    -> Acties
        +genereren van BAB (bij "beg_sluit_eigen_deur")
   
    -> Enabling condities
        +BAB moet "uit" zijn (bij "beg_sluit_eigen_deur")
        +BAB moet "aan" zijn (bij "best_wil_vertrekken")
        +AC moet gegenereert zijn voordat de begeleider zijn eigen deur sluit
        -Trein moet/mag nog niet vertrokken zijn (bij "beg_sluit_eigen_deur")

*)

(*
    TODO: Schrijf het nieuwe protocol zoals in de opgave
*)

Init == /\ TypeInvariant
        /\ system.trein = "perron"
        /\ system.deur_beg = "open"
        /\ system.deur_rest = "open"
        /\ system.begeleider = "perron"
        /\ system.bestuurder = "wacht"
        /\ system.AC = "uit"
        /\ system.licht = "uit"
        /\ system.spoor = "vrij"
        /\ system.startuur = "n_aangebroken"
        /\ system.BAB = "uit"


uur_aangebroken == /\ system.startuur = "n_aangebroken"
                   /\ system' = [system EXCEPT !.startuur = "aangebroken"]

beg_sluit_andere_deuren == /\ system.deur_rest = "open"
                           /\ system.begeleider = "trein"
						   /\ system' = system (* Aangepast om fout te simuleren *)

beg_sluit_eigen_deur == /\ system.deur_beg = "open"
                        /\ system.begeleider = "trein"
                        /\ system.BAB = "uit"
                        /\ system.AC = "aan"
                        /\ system' = [system EXCEPT !.deur_beg = "dicht", !.BAB = "aan"]

beg_stapt_af == /\ ( system.deur_beg = "open" \/ system.deur_rest = "open")
                /\ system.begeleider = "trein"
                /\ system.trein = "perron"
                /\ system' = [system EXCEPT !.begeleider = "perron"]

beg_stapt_op == /\ (system.deur_beg = "open" \/ system.deur_rest = "open")
                /\ system.trein = "perron"
                /\ system.begeleider = "perron"
                /\ system' = [system EXCEPT !.begeleider = "trein"]

activeren_AC == /\ system.startuur = "aangebroken"
                /\ system.begeleider = "perron"
                /\ system.AC = "uit"
                /\ system' = [system EXCEPT !.AC = "aan", !.licht = "rood"]

licht_op_wit == /\ system.licht = "rood"
                /\ system' = [system EXCEPT !.licht = "wit"]

best_wil_vertrekken == /\ system.spoor = "vrij"
                       /\ system.licht = "wit"
                       /\ system.bestuurder = "wacht"
                       /\ system.BAB = "aan"
                       /\ system' = [system EXCEPT !.bestuurder = "wil_vertrekken"]

trein_vertrekt == /\ system.bestuurder = "wil_vertrekken"
                  /\ system' = [system EXCEPT !.trein = "vertrokken"]

                
Next == \/ uur_aangebroken
        \/ beg_sluit_andere_deuren
        \/ beg_sluit_eigen_deur
        \/ beg_stapt_af
        \/ beg_stapt_op
        \/ activeren_AC
        \/ licht_op_wit
        \/ best_wil_vertrekken
        \/ trein_vertrekt

Liveness ==  /\ SF_system(uur_aangebroken)
             /\ SF_system(beg_sluit_andere_deuren)
             /\ SF_system(beg_stapt_af)
             /\ SF_system(activeren_AC) 
             /\ SF_system(beg_stapt_op)
             /\ SF_system(licht_op_wit)
             /\ SF_system(best_wil_vertrekken) 
             /\ SF_system(trein_vertrekt) 
             /\ SF_system(beg_sluit_eigen_deur)

Spec  ==  Init /\ [][Next]_system /\ Liveness
----
veiligheidseis1 == system.trein = "vertrokken" => system.begeleider = "trein"
veiligheidseis2 == system.trein ="vertrokken" => system.deur_rest = "dicht"
veiligheidseis3 == system.trein = "vertrokken" ~> system.deur_beg = "dicht"
liveness_eis == ( system.startuur = "aangebroken" /\ system.spoor = "vrij")  ~> (system.trein ="vertrokken")
====