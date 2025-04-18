(* generated by Ott 0.34 from: ../ott/spec.ott *)
(* to compile: Holmake compSpecTheory.uo   *)
(* for interactive use:
  app load ["pred_setTheory","finite_mapTheory","stringTheory","containerTheory","ottLib"];
*)

open HolKernel boolLib Parse bossLib ottLib;
infix THEN THENC |-> ## ;
local open arithmeticTheory stringTheory containerTheory pred_setTheory listTheory 
  finite_mapTheory in end;

val _ = new_theory "compSpec";

open string_numTheory;

Type cn = ``:string`` (* component constant name *)
Type Sn = ``:string`` (* specification constant name *)
Type q = ``:string`` (* component variable *)
Type V = ``:string`` (* specification variable *)
Type a = ``:num`` (* number variable *)
Type x = ``:string`` (* constraint variable *)
val _ = Hol_datatype ` 
I = 
   interval_closed of a => a (* closed *)
 | interval_left_half_open of a => a (* left half open *)
 | interval_right_half_open_num of a => a (* right half open bounded *)
 | interval_right_half_open_inf of a (* right half open unbounded *)
 | interval_open_num of a => a (* open bounded *)
 | interval_open_inf of a (* open unbounded *)
`;
val _ = Hol_datatype ` 
f = 
   mitl_const of 'a (* constant *)
 | mitl_not of f (* negation *)
 | mitl_and of f => f (* conjunction *)
 | mitl_implies of f => f (* implies *)
 | mitl_until of f => I => f (* until *)
 | mitl_since of f => I => f (* since *)
 | mitl_box of I => f (* always in the future within interval *)
 | mitl_diamond of I => f (* sometime in the future within interval *)
 | mitl_box_dash of I => f (* always in the past within interval *)
 | mitl_diamond_dash of I => f (* sometime in the past within interval *)
`;
val _ = Hol_datatype ` 
T =  (* temporal specification constant *)
   T_const of Sn (* constant *)
 | T_compat (* compatibility *)
 | T_top (* top *)
 | T_hat of 'a f (* lifted MITL formula *)
`;
val _ = Hol_datatype ` 
Sc =  (* specification constant *)
   Sc_const of Sn (* constant *)
 | Sc_compat (* compatibility *)
 | Sc_top (* top *)
`;
val _ = Hol_datatype ` 
c =  (* component term *)
   c_const of cn (* constant *)
 | c_comp of c => c (* composition *)
 | c_var of q (* variable *)
`;
val _ = Hol_datatype ` 
St =  (* temporal specification term *)
   St_const of 'a T (* constant *)
 | St_conj of St => St (* conjunction *)
 | St_assume of St => St (* assume-guarantee *)
 | St_par of St => St (* parallel *)
 | St_var of V (* variable *)
`;
val _ = Hol_datatype ` 
S =  (* specification term *)
   S_const of Sc (* constant *)
 | S_conj of S => S (* conjunction *)
 | S_assume of S => S (* assume-guarantee *)
 | S_par of S => S (* parallel *)
 | S_var of V (* variable *)
`;
val _ = Hol_datatype ` 
Pt =  (* temporal component specification predicate *)
   Pt_implements of c => 'a St (* implements *)
 | Pt_refines of 'a St => 'a St (* refines *)
 | Pt_asserts of 'a St (* assertional *)
 | Pt_forall_c of q => Pt (* for all components *)
 | Pt_exists_c of q => Pt (* exists component *)
 | Pt_forall_St of V => Pt (* for all specifications *)
 | Pt_exists_St of V => Pt (* exists specification *)
 | Pt_implies of Pt => Pt (* implies *)
 | Pt_and of Pt => Pt (* conjunction *)
 | Pt_or of Pt => Pt (* disjunction *)
 | Pt_not of Pt (* negation *)
 | Pt_c_eq of c => c (* component equals *)
 | Pt_St_eq of 'a St => 'a St (* temporal specification equals *)
`;
val _ = Hol_datatype ` 
P =  (* component specification predicate *)
   P_implements of c => S (* implements *)
 | P_refines of S => S (* refines *)
 | P_asserts of S (* assertional *)
 | P_forall_c of q => P (* for all components *)
 | P_exists_c of q => P (* exists component *)
 | P_forall_S of V => P (* for all specifications *)
 | P_exists_S of V => P (* exists specification *)
 | P_implies of P => P (* implies *)
 | P_and of P => P (* conjunction *)
 | P_or of P => P (* disjunction *)
 | P_not of P (* negation *)
 | P_c_eq of c => c (* component equals *)
 | P_S_eq of S => S (* specification equals *)
`;

Type Q = ``:(string set)``
Definition SVARIANT_def:
  SVARIANT (s:string set) : string = n2s (MAX_SET (IMAGE s2n s) + 1)
End

Definition fv_c:
 (fv_c (c_const cn) = {})
 /\
 (fv_c (c_comp c1 c2) =
  (fv_c c1 UNION fv_c c2))
 /\
 (fv_c (c_var x) = {x})
End

Definition fv_S:
 (fv_S (S_const Sn) = {})
 /\
 (fv_S (S_conj S1 S2) =
  (fv_S S1 UNION fv_S S2))
 /\
 (fv_S (S_assume S1 S2) =
  (fv_S S1 UNION fv_S S2))
 /\
 (fv_S (S_par S1 S2) =
  (fv_S S1 UNION fv_S S2))
 /\
 (fv_S (S_var x) = {x})
End

Definition fv_P_c:
 (fv_P_c (P_implements c S) = fv_c c)
 /\
 (fv_P_c (P_refines S1 S2) = {})
 /\
 (fv_P_c (P_asserts S) = {})
 /\
 (fv_P_c (P_forall_c x P) = fv_P_c P DELETE x)
 /\
 (fv_P_c (P_forall_S x P) = fv_P_c P)
 /\
 (fv_P_c (P_exists_c x P) = fv_P_c P DELETE x)
 /\
 (fv_P_c (P_exists_S x P) = fv_P_c P)
 /\
 (fv_P_c (P_implies P1 P2) = fv_P_c P1 UNION fv_P_c P2)
 /\
 (fv_P_c (P_and P1 P2) = fv_P_c P1 UNION fv_P_c P2)
 /\
 (fv_P_c (P_or P1 P2) = fv_P_c P1 UNION fv_P_c P2)
 /\
 (fv_P_c (P_not P) = fv_P_c P)
 /\
 (fv_P_c (P_c_eq c1 c2) = fv_c c1 UNION fv_c c2)
 /\
 (fv_P_c (P_S_eq S1 S2) = {})
End

Definition fv_P_S:
 (fv_P_S (P_implements c S) = fv_S S)
 /\
 (fv_P_S (P_refines S1 S2) = fv_S S1 UNION fv_S S2)
 /\
 (fv_P_S (P_asserts S) = fv_S S)
 /\
 (fv_P_S (P_forall_c x P) = fv_P_S P)
 /\
 (fv_P_S (P_forall_S x P) = fv_P_S P DELETE x)
 /\
 (fv_P_S (P_exists_c x P) = fv_P_S P)
 /\
 (fv_P_S (P_exists_S x P) = fv_P_S P DELETE x)
 /\
 (fv_P_S (P_implies P1 P2) = fv_P_S P1 UNION fv_P_S P2)
 /\
 (fv_P_S (P_and P1 P2) = fv_P_S P1 UNION fv_P_S P2)
 /\
 (fv_P_S (P_or P1 P2) = fv_P_S P1 UNION fv_P_S P2)
 /\
 (fv_P_S (P_not P) = fv_P_S P)
 /\
 (fv_P_S (P_c_eq c1 c2) = {})
 /\
 (fv_P_S (P_S_eq S1 S2) = fv_S S1 UNION fv_S S2)
End

Definition csubst_c:
 (csubst_c Mq (c_const cn) = c_const cn)
 /\
 (csubst_c Mq (c_comp c1 c2) = c_comp (csubst_c Mq c1) (csubst_c Mq c2))
 /\
 (csubst_c Mq (c_var x) = Mq x)
End

Definition Ssubst_S:
 (Ssubst_S MV (S_const Sn) = S_const Sn)
 /\
 (Ssubst_S MV (S_conj S1 S2) = S_conj (Ssubst_S MV S1) (Ssubst_S MV S2))
 /\
 (Ssubst_S MV (S_assume S1 S2) = S_assume (Ssubst_S MV S1) (Ssubst_S MV S2))
 /\
 (Ssubst_S MV (S_par S1 S2) = S_par (Ssubst_S MV S1) (Ssubst_S MV S2))
 /\
 (Ssubst_S MV (S_var x) = MV x)
End

Definition csubst_P:
 (csubst_P Mq (P_implements c S) = P_implements (csubst_c Mq c) S)
 /\
 (csubst_P Mq (P_refines S1 S2) = P_refines S1 S2)
 /\
 (csubst_P Mq (P_asserts S) = P_asserts S)
 /\
 (csubst_P Mq (P_forall_c x P) =
   let Mq' = (x =+ c_var x) Mq in
   let z   = if ?y. y IN fv_P_c (P_forall_c x P) /\ x IN fv_c (Mq' y)
             then SVARIANT (fv_P_c (csubst_P Mq' P)) else x in
   P_forall_c z (csubst_P ((x =+ c_var z) Mq) P))
 /\
 (csubst_P Mq (P_forall_S x P) = P_forall_S x (csubst_P Mq P))
 /\
 (csubst_P Mq (P_exists_c x P) = 
  let Mq' = (x =+ c_var x) Mq in
   let z   = if ?y. y IN fv_P_c (P_exists_c x P) /\ x IN fv_c (Mq' y)
             then SVARIANT (fv_P_c (csubst_P Mq' P)) else x in
   P_exists_c z (csubst_P ((x =+ c_var z) Mq) P))
 /\
 (csubst_P Mq (P_exists_S x P) = P_exists_S x (csubst_P Mq P))
 /\
 (csubst_P Mq (P_implies P1 P2) = P_implies (csubst_P Mq P1) (csubst_P Mq P2))
 /\
 (csubst_P Mq (P_and P1 P2) = P_and (csubst_P Mq P1) (csubst_P Mq P2))
 /\
 (csubst_P Mq (P_or P1 P2) = P_or (csubst_P Mq P1) (csubst_P Mq P2))
 /\
 (csubst_P Mq (P_not P) = P_not (csubst_P Mq P))
 /\
 (csubst_P Mq (P_c_eq c1 c2) = P_c_eq (csubst_c Mq c1) (csubst_c Mq c2))
 /\
 (csubst_P Mq (P_S_eq S1 S2) = P_S_eq S1 S2)
End

Definition Ssubst_P:
 (Ssubst_P MV (P_implements c S) = P_implements c (Ssubst_S MV S))
 /\
 (Ssubst_P MV (P_refines S1 S2) = P_refines (Ssubst_S MV S1) (Ssubst_S MV S2))
 /\
 (Ssubst_P MV (P_asserts S) = P_asserts (Ssubst_S MV S))
 /\
 (Ssubst_P MV (P_forall_c x P) = P_forall_c x (Ssubst_P MV P))
 /\
 (Ssubst_P MV (P_forall_S x P) =
   let MV' = (x =+ S_var x) MV in
   let z   = if ?y. y IN fv_P_S (P_forall_S x P) /\ x IN fv_S (MV' y)
             then SVARIANT (fv_P_S (Ssubst_P MV' P)) else x in
   P_forall_S z (Ssubst_P ((x =+ S_var z) MV) P))
 /\
 (Ssubst_P MV (P_exists_c x P) = P_exists_c x (Ssubst_P MV P))
 /\
 (Ssubst_P MV (P_exists_S x P) = 
   let MV' = (x =+ S_var x) MV in
   let z   = if ?y. y IN fv_P_S (P_exists_S x P) /\ x IN fv_S (MV' y)
             then SVARIANT (fv_P_S (Ssubst_P MV' P)) else x in
   P_exists_S z (Ssubst_P ((x =+ S_var z) MV) P))
 /\
 (Ssubst_P MV (P_implies P1 P2) = P_implies (Ssubst_P MV P1) (Ssubst_P MV P2))
 /\
 (Ssubst_P MV (P_and P1 P2) = P_and (Ssubst_P MV P1) (Ssubst_P MV P2))
 /\
 (Ssubst_P MV (P_or P1 P2) = P_or (Ssubst_P MV P1) (Ssubst_P MV P2))
 /\
 (Ssubst_P MV (P_not P) = P_not (Ssubst_P MV P))
 /\
 (Ssubst_P MV (P_c_eq c1 c2) = P_c_eq c1 c2)
 /\
 (Ssubst_P MV (P_S_eq S1 S2) = P_S_eq (Ssubst_S MV S1) (Ssubst_S MV S2))
End

Definition fv_St:
 (fv_St (St_const Tn) = {})
 /\
 (fv_St (St_conj St1 St2) =
  (fv_St St1 UNION fv_St St2))
 /\
 (fv_St (St_assume St1 St2) =
  (fv_St St1 UNION fv_St St2))
 /\
 (fv_St (St_par St1 St2) =
  (fv_St St1 UNION fv_St St2))
 /\
 (fv_St (St_var x) = {x})
End

Definition fv_Pt_c:
 (fv_Pt_c (Pt_implements c St) = fv_c c)
 /\
 (fv_Pt_c (Pt_refines St1 St2) = {})
 /\
 (fv_Pt_c (Pt_asserts St) = {})
 /\
 (fv_Pt_c (Pt_forall_c x Pt) = fv_Pt_c Pt DELETE x)
 /\
 (fv_Pt_c (Pt_forall_St x Pt) = fv_Pt_c Pt)
 /\
 (fv_Pt_c (Pt_exists_c x Pt) = fv_Pt_c Pt DELETE x)
 /\
 (fv_Pt_c (Pt_exists_St x Pt) = fv_Pt_c Pt)
 /\
 (fv_Pt_c (Pt_implies Pt1 Pt2) = fv_Pt_c Pt1 UNION fv_Pt_c Pt2)
 /\
 (fv_Pt_c (Pt_and Pt1 Pt2) = fv_Pt_c Pt1 UNION fv_Pt_c Pt2)
 /\
 (fv_Pt_c (Pt_or Pt1 Pt2) = fv_Pt_c Pt1 UNION fv_Pt_c Pt2)
 /\
 (fv_Pt_c (Pt_not Pt) = fv_Pt_c Pt)
 /\
 (fv_Pt_c (Pt_c_eq c1 c2) = fv_c c1 UNION fv_c c2)
 /\
 (fv_Pt_c (Pt_St_eq St1 St2) = {})
End

Definition fv_Pt_St:
 (fv_Pt_St (Pt_implements c St) = fv_St St)
 /\
 (fv_Pt_St (Pt_refines St1 St2) = fv_St St1 UNION fv_St St2)
 /\
 (fv_Pt_St (Pt_asserts St) = fv_St St)
 /\
 (fv_Pt_St (Pt_forall_c x Pt) = fv_Pt_St Pt)
 /\
 (fv_Pt_St (Pt_forall_St x Pt) = fv_Pt_St Pt DELETE x)
 /\
 (fv_Pt_St (Pt_exists_c x Pt) = fv_Pt_St Pt)
 /\
 (fv_Pt_St (Pt_exists_St x Pt) = fv_Pt_St Pt DELETE x)
 /\
 (fv_Pt_St (Pt_implies Pt1 Pt2) = fv_Pt_St Pt1 UNION fv_Pt_St Pt2)
 /\
 (fv_Pt_St (Pt_and Pt1 Pt2) = fv_Pt_St Pt1 UNION fv_Pt_St Pt2)
 /\
 (fv_Pt_St (Pt_or Pt1 Pt2) = fv_Pt_St Pt1 UNION fv_Pt_St Pt2)
 /\
 (fv_Pt_St (Pt_not Pt) = fv_Pt_St Pt)
 /\
 (fv_Pt_St (Pt_c_eq c1 c2) = {})
 /\
 (fv_Pt_St (Pt_St_eq St1 St2) = fv_St St1 UNION fv_St St2)
End

Definition Stsubst_St:
 (Stsubst_St MV (St_const Tn) = St_const Tn)
 /\
 (Stsubst_St MV (St_conj St1 St2) = St_conj (Stsubst_St MV St1) (Stsubst_St MV St2))
 /\
 (Stsubst_St MV (St_assume S1 S2) = St_assume (Stsubst_St MV S1) (Stsubst_St MV S2))
 /\
 (Stsubst_St MV (St_par S1 S2) = St_par (Stsubst_St MV S1) (Stsubst_St MV S2))
 /\
 (Stsubst_St MV (St_var x) = MV x)
End

Definition csubst_Pt:
 (csubst_Pt Mq (Pt_implements c St) = Pt_implements (csubst_c Mq c) St)
 /\
 (csubst_Pt Mq (Pt_refines St1 St2) = Pt_refines St1 St2)
 /\
 (csubst_Pt Mq (Pt_asserts St) = Pt_asserts St)
 /\
 (csubst_Pt Mq (Pt_forall_c x Pt) =
   let Mq' = (x =+ c_var x) Mq in
   let z   = if ?y. y IN fv_Pt_c (Pt_forall_c x Pt) /\ x IN fv_c (Mq' y)
             then SVARIANT (fv_Pt_c (csubst_Pt Mq' Pt)) else x in
   Pt_forall_c z (csubst_Pt ((x =+ c_var z) Mq) Pt))
 /\
 (csubst_Pt Mq (Pt_forall_St x Pt) = Pt_forall_St x (csubst_Pt Mq Pt))
 /\
 (csubst_Pt Mq (Pt_exists_c x Pt) = 
  let Mq' = (x =+ c_var x) Mq in
   let z   = if ?y. y IN fv_Pt_c (Pt_exists_c x Pt) /\ x IN fv_c (Mq' y)
             then SVARIANT (fv_Pt_c (csubst_Pt Mq' Pt)) else x in
   Pt_exists_c z (csubst_Pt ((x =+ c_var z) Mq) Pt))
 /\
 (csubst_Pt Mq (Pt_exists_St x Pt) = Pt_exists_St x (csubst_Pt Mq Pt))
 /\
 (csubst_Pt Mq (Pt_implies Pt1 Pt2) = Pt_implies (csubst_Pt Mq Pt1) (csubst_Pt Mq Pt2))
 /\
 (csubst_Pt Mq (Pt_and Pt1 Pt2) = Pt_and (csubst_Pt Mq Pt1) (csubst_Pt Mq Pt2))
 /\
 (csubst_Pt Mq (Pt_or Pt1 Pt2) = Pt_or (csubst_Pt Mq Pt1) (csubst_Pt Mq Pt2))
 /\
 (csubst_Pt Mq (Pt_not Pt) = Pt_not (csubst_Pt Mq Pt))
 /\
 (csubst_Pt Mq (Pt_c_eq c1 c2) = Pt_c_eq (csubst_c Mq c1) (csubst_c Mq c2))
 /\
 (csubst_Pt Mq (Pt_St_eq St1 St2) = Pt_St_eq St1 St2)
End

Definition Stsubst_Pt:
 (Stsubst_Pt MV (Pt_implements c St) = Pt_implements c (Stsubst_St MV St))
 /\
 (Stsubst_Pt MV (Pt_refines St1 St2) = Pt_refines (Stsubst_St MV St1) (Stsubst_St MV St2))
 /\
 (Stsubst_Pt MV (Pt_asserts St) = Pt_asserts (Stsubst_St MV St))
 /\
 (Stsubst_Pt MV (Pt_forall_c x Pt) = Pt_forall_c x (Stsubst_Pt MV Pt))
 /\
 (Stsubst_Pt MV (Pt_forall_St x Pt) =
   let MV' = (x =+ St_var x) MV in
   let z   = if ?y. y IN fv_Pt_St (Pt_forall_St x Pt) /\ x IN fv_St (MV' y)
             then SVARIANT (fv_Pt_St (Stsubst_Pt MV' Pt)) else x in
   Pt_forall_St z (Stsubst_Pt ((x =+ St_var z) MV) Pt))
 /\
 (Stsubst_Pt MV (Pt_exists_c x Pt) = Pt_exists_c x (Stsubst_Pt MV Pt))
 /\
 (Stsubst_Pt MV (Pt_exists_St x Pt) = 
   let MV' = (x =+ St_var x) MV in
   let z   = if ?y. y IN fv_Pt_St (Pt_exists_St x Pt) /\ x IN fv_St (MV' y)
             then SVARIANT (fv_Pt_St (Stsubst_Pt MV' Pt)) else x in
   Pt_exists_St z (Stsubst_Pt ((x =+ St_var z) MV) Pt))
 /\
 (Stsubst_Pt MV (Pt_implies Pt1 Pt2) = Pt_implies (Stsubst_Pt MV Pt1) (Stsubst_Pt MV Pt2))
 /\
 (Stsubst_Pt MV (Pt_and Pt1 Pt2) = Pt_and (Stsubst_Pt MV Pt1) (Stsubst_Pt MV Pt2))
 /\
 (Stsubst_Pt MV (Pt_or Pt1 Pt2) = Pt_or (Stsubst_Pt MV Pt1) (Stsubst_Pt MV Pt2))
 /\
 (Stsubst_Pt MV (Pt_not Pt) = Pt_not (Stsubst_Pt MV Pt))
 /\
 (Stsubst_Pt MV (Pt_c_eq c1 c2) = Pt_c_eq c1 c2)
 /\
 (Stsubst_Pt MV (Pt_St_eq St1 St2) = Pt_St_eq (Stsubst_St MV St1) (Stsubst_St MV St2))
End


Type Gt = ``:(('a Pt) set)``

Type G = ``:(P set)``
(** definitions *)

(* defns spec_proof *)
Inductive spec_proof:
(* defn spec_holds *)

[ax:] (! (G:G) (P:P) .
(clause_name "ax")
 ==> 
( ( spec_holds  ( P  INSERT  G )  P )))

[ref_in:] (! (G:G) (S1:S) (S2:S) (q:q) .
(clause_name "ref_in") /\
(( ( spec_holds G (P_forall_c q (P_implies (P_implements (c_var q) S1) (P_implements (c_var q) S2))) )))
 ==> 
( ( spec_holds G (P_refines S1 S2) )))

[ref_el:] (! (G:G) (c:c) (S2:S) (S1:S) .
(clause_name "ref_el") /\
(( ( spec_holds G (P_implements c S1) )) /\
( ( spec_holds G (P_refines S1 S2) )))
 ==> 
( ( spec_holds G (P_implements c S2) )))

[assn_in:] (! (G:G) (S:S) (q1:q) (q2:q) .
(clause_name "assn_in") /\
(( ( q1  <>  q2 ) ) /\
( ( spec_holds G (P_forall_c q1 (P_forall_c q2 (P_implies (P_implements (c_var q1) S) (P_implements (c_comp (c_var q1) (c_var q2)) S)))) )))
 ==> 
( ( spec_holds G (P_asserts S) )))

[assn_el:] (! (G:G) (c1:c) (c2:c) (S:S) .
(clause_name "assn_el") /\
(( ( spec_holds G (P_asserts S) )) /\
( ( spec_holds G (P_implements c1 S) )))
 ==> 
( ( spec_holds G (P_implements (c_comp c1 c2) S) )))

[conj_in:] (! (G:G) (c:c) (S1:S) (S2:S) .
(clause_name "conj_in") /\
(( ( spec_holds G (P_implements c S1) )) /\
( ( spec_holds G (P_implements c S2) )))
 ==> 
( ( spec_holds G (P_implements c (S_conj S1 S2)) )))

[conj_el1:] (! (G:G) (c:c) (S1:S) (S2:S) .
(clause_name "conj_el1") /\
(( ( spec_holds G (P_implements c (S_conj S1 S2)) )))
 ==> 
( ( spec_holds G (P_implements c S1) )))

[conj_el2:] (! (G:G) (c:c) (S2:S) (S1:S) .
(clause_name "conj_el2") /\
(( ( spec_holds G (P_implements c (S_conj S1 S2)) )))
 ==> 
( ( spec_holds G (P_implements c S2) )))

[par_in:] (! (G:G) (c1:c) (c2:c) (S1:S) (S2:S) .
(clause_name "par_in") /\
(( ( spec_holds G (P_implements c1 S1) )) /\
( ( spec_holds G (P_implements c2 S2) )))
 ==> 
( ( spec_holds G (P_implements (c_comp c1 c2) (S_par S1 S2)) )))

[par_el:] (! (G:G) (q1:q) (q2:q) (S1:S) (S2:S) (c:c) .
(clause_name "par_el") /\
(( ( q1  <>  q2 ) ) /\
( ( q1  NOTIN   (fv_c  c )  ) ) /\
( ( q2  NOTIN   (fv_c  c )  ) ) /\
( ( spec_holds G (P_implements c (S_par S1 S2)) )))
 ==> 
( ( spec_holds G (P_exists_c q1 (P_exists_c q2 (P_and (P_implements (c_var q1) S1) (P_and (P_implements (c_var q2) S2) (P_c_eq c (c_comp (c_var q1) (c_var q2))))))) )))

[cont_in:] (! (G:G) (c:c) (S1:S) (S2:S) (q:q) .
(clause_name "cont_in") /\
(( ( q  NOTIN   (fv_c  c )  ) ) /\
( ( spec_holds G (P_forall_c q (P_implies (P_implements (c_var q) S1) (P_implements (c_comp (c_var q) c) S2))) )))
 ==> 
( ( spec_holds G (P_implements c (S_assume S1 S2)) )))

[cont_el:] (! (G:G) (c1:c) (c2:c) (S2:S) (S1:S) .
(clause_name "cont_el") /\
(( ( spec_holds G (P_implements c1 S1) )) /\
( ( spec_holds G (P_implements c2 (S_assume S1 S2)) )))
 ==> 
( ( spec_holds G (P_implements (c_comp c1 c2) S2) )))

[cre:] (! (G:G) (c:c) (S2:S) (S3:S) (S1:S) .
(clause_name "cre") /\
(( ( spec_holds G (P_implements c (S_conj S1 S2)) )) /\
( ( spec_holds G (P_refines S2 S3) )))
 ==> 
( ( spec_holds G (P_implements c (S_conj S2 S3)) )))

[cr:] (! (G:G) (c:c) (S2:S) (S3:S) (S1:S) .
(clause_name "cr") /\
(( ( spec_holds G (P_implements c (S_conj S1 S3)) )) /\
( ( spec_holds G (P_refines S1 S2) )))
 ==> 
( ( spec_holds G (P_implements c (S_conj S2 S3)) )))

[and_in:] (! (G:G) (P1:P) (P2:P) .
(clause_name "and_in") /\
(( ( spec_holds G P1 )) /\
( ( spec_holds G P2 )))
 ==> 
( ( spec_holds G (P_and P1 P2) )))

[and_el1:] (! (G:G) (P1:P) (P2:P) .
(clause_name "and_el1") /\
(( ( spec_holds G (P_and P1 P2) )))
 ==> 
( ( spec_holds G P1 )))

[and_el2:] (! (G:G) (P2:P) (P1:P) .
(clause_name "and_el2") /\
(( ( spec_holds G (P_and P1 P2) )))
 ==> 
( ( spec_holds G P2 )))

[imp_in:] (! (G:G) (P1:P) (P2:P) .
(clause_name "imp_in") /\
(( ( spec_holds  ( P1  INSERT  G )  P2 )))
 ==> 
( ( spec_holds G (P_implies P1 P2) )))

[imp_el:] (! (G:G) (P2:P) (P1:P) .
(clause_name "imp_el") /\
(( ( spec_holds G (P_implies P1 P2) )) /\
( ( spec_holds G P1 )))
 ==> 
( ( spec_holds G P2 )))

[or_in1:] (! (G:G) (P1:P) (P2:P) .
(clause_name "or_in1") /\
(( ( spec_holds G P1 )))
 ==> 
( ( spec_holds G (P_or P1 P2) )))

[or_in2:] (! (G:G) (P1:P) (P2:P) .
(clause_name "or_in2") /\
(( ( spec_holds G P2 )))
 ==> 
( ( spec_holds G (P_or P1 P2) )))

[or_el:] (! (G:G) (P:P) (P1:P) (P2:P) .
(clause_name "or_el") /\
(( ( spec_holds G (P_or P1 P2) )) /\
( ( spec_holds  ( P1  INSERT  G )  P )) /\
( ( spec_holds  ( P2  INSERT  G )  P )))
 ==> 
( ( spec_holds G P )))

[not_in:] (! (G:G) (P1:P) (P2:P) .
(clause_name "not_in") /\
(( ( spec_holds  ( P1  INSERT  G )  P2 )) /\
( ( spec_holds  ( P1  INSERT  G )  (P_not P2) )))
 ==> 
( ( spec_holds G (P_not P1) )))

[not_el:] (! (G:G) (P:P) .
(clause_name "not_el") /\
(( ( spec_holds G (P_not (P_not P)) )))
 ==> 
( ( spec_holds G P )))

[all_el_c:] (! (G:G) (P:P) (c:c) (q:q) .
(clause_name "all_el_c") /\
(( ( spec_holds G (P_forall_c q P) )))
 ==> 
( ( spec_holds G  (csubst_P (( q  =+  c ) c_var)  P )  )))

[all_in_c:] (! (G:G) (q:q) (P:P) (q':q) .
(clause_name "all_in_c") /\
(( ( q'  NOTIN   (  (fv_P_c  P )   UNION   (BIGUNION (IMAGE fv_P_c  G ))  )  ) ) /\
( ( spec_holds G  (csubst_P (( q  =+  (c_var q') ) c_var)  P )  )))
 ==> 
( ( spec_holds G (P_forall_c q P) )))

[eq_el_c:] (! (G:G) (P:P) (c':c) (q:q) (c:c) .
(clause_name "eq_el_c") /\
(( ( spec_holds G (P_c_eq c c') )) /\
( ( spec_holds G  (csubst_P (( q  =+  c ) c_var)  P )  )))
 ==> 
( ( spec_holds G  (csubst_P (( q  =+  c' ) c_var)  P )  )))

[all_el_S:] (! (G:G) (P:P) (S:S) (V:V) .
(clause_name "all_el_S") /\
(( ( spec_holds G (P_forall_S V P) )))
 ==> 
( ( spec_holds G  (Ssubst_P (( V  =+  S ) S_var)  P )  )))

[all_in_S:] (! (G:G) (V:V) (P:P) (V':V) .
(clause_name "all_in_S") /\
(( ( V'  NOTIN   (  (fv_P_S  P )   UNION   (BIGUNION (IMAGE fv_P_S  G ))  )  ) ) /\
( ( spec_holds G  (Ssubst_P (( V  =+  (S_var V') ) S_var)  P )  )))
 ==> 
( ( spec_holds G (P_forall_S V P) )))

[eq_el_S:] (! (G:G) (P:P) (S':S) (V:V) (S:S) .
(clause_name "eq_el_S") /\
(( ( spec_holds G (P_S_eq S S') )) /\
( ( spec_holds G  (Ssubst_P (( V  =+  S ) S_var)  P )  )))
 ==> 
( ( spec_holds G  (Ssubst_P (( V  =+  S' ) S_var)  P )  )))

[ex_in_c:] (! (G:G) (q:q) (P:P) (c:c) .
(clause_name "ex_in_c") /\
(( ( spec_holds G  (csubst_P (( q  =+  c ) c_var)  P )  )))
 ==> 
( ( spec_holds G (P_exists_c q P) )))

[ex_el_c:] (! (G:G) (G':G) (P':P) (q':q) (P:P) (q:q) .
(clause_name "ex_el_c") /\
(( ( q'  NOTIN   (  (fv_P_c  P )   UNION   (fv_P_c  P' )  )  ) ) /\
( ( q'  NOTIN   (  (BIGUNION (IMAGE fv_P_c  G ))   UNION   (BIGUNION (IMAGE fv_P_c  G' ))  )  ) ) /\
( ( spec_holds G (P_exists_c q P) )) /\
( ( spec_holds  (  (csubst_P (( q  =+  (c_var q') ) c_var)  P )   INSERT  G' )  P' )))
 ==> 
( ( spec_holds  ( G  UNION  G' )  P' )))

[ex_in_S:] (! (G:G) (V:V) (P:P) (S:S) .
(clause_name "ex_in_S") /\
(( ( spec_holds G  (Ssubst_P (( V  =+  S ) S_var)  P )  )))
 ==> 
( ( spec_holds G (P_exists_S V P) )))

[ex_el_S:] (! (G:G) (G':G) (P':P) (V':V) (P:P) (V:V) .
(clause_name "ex_el_S") /\
(( ( V'  NOTIN   (  (fv_P_S  P )   UNION   (fv_P_S  P' )  )  ) ) /\
( ( V'  NOTIN   (  (BIGUNION (IMAGE fv_P_S  G ))   UNION   (BIGUNION (IMAGE fv_P_S  G' ))  )  ) ) /\
( ( spec_holds G (P_exists_S V P) )) /\
( ( spec_holds  (  (Ssubst_P (( V  =+  (S_var V') ) S_var)  P )   INSERT  G' )  P' )))
 ==> 
( ( spec_holds  ( G  UNION  G' )  P' )))
End
(** definitions *)

(* defns spec_temporal_proof *)
Inductive spec_temporal_proof:
(* defn spec_temporal_holds *)

[spec_temporal_ax:] (! (Gt:'a Gt) (Pt:'a Pt) .
(clause_name "spec_temporal_ax")
 ==> 
( ( spec_temporal_holds  ( Pt  INSERT  Gt )  Pt )))

[spec_temporal_ref_in:] (! (Gt:'a Gt) (St1:'a St) (St2:'a St) (q:q) .
(clause_name "spec_temporal_ref_in") /\
(( ( spec_temporal_holds Gt (Pt_forall_c q (Pt_implies (Pt_implements (c_var q) St1) (Pt_implements (c_var q) St2))) )))
 ==> 
( ( spec_temporal_holds Gt (Pt_refines St1 St2) )))

[spec_temporal_ref_el:] (! (Gt:'a Gt) (c:c) (St2:'a St) (St1:'a St) .
(clause_name "spec_temporal_ref_el") /\
(( ( spec_temporal_holds Gt (Pt_implements c St1) )) /\
( ( spec_temporal_holds Gt (Pt_refines St1 St2) )))
 ==> 
( ( spec_temporal_holds Gt (Pt_implements c St2) )))

[spec_temporal_assn_in:] (! (Gt:'a Gt) (St:'a St) (q1:q) (q2:q) .
(clause_name "spec_temporal_assn_in") /\
(( ( q1  <>  q2 ) ) /\
( ( spec_temporal_holds Gt (Pt_forall_c q1 (Pt_forall_c q2 (Pt_implies (Pt_implements (c_var q1) St) (Pt_implements (c_comp (c_var q1) (c_var q2)) St)))) )))
 ==> 
( ( spec_temporal_holds Gt (Pt_asserts St) )))

[spec_temporal_assn_el:] (! (Gt:'a Gt) (c1:c) (c2:c) (St:'a St) .
(clause_name "spec_temporal_assn_el") /\
(( ( spec_temporal_holds Gt (Pt_asserts St) )) /\
( ( spec_temporal_holds Gt (Pt_implements c1 St) )))
 ==> 
( ( spec_temporal_holds Gt (Pt_implements (c_comp c1 c2) St) )))

[spec_temporal_conj_in:] (! (Gt:'a Gt) (c:c) (St1:'a St) (St2:'a St) .
(clause_name "spec_temporal_conj_in") /\
(( ( spec_temporal_holds Gt (Pt_implements c St1) )) /\
( ( spec_temporal_holds Gt (Pt_implements c St2) )))
 ==> 
( ( spec_temporal_holds Gt (Pt_implements c (St_conj St1 St2)) )))

[spec_temporal_conj_el1:] (! (Gt:'a Gt) (c:c) (St1:'a St) (St2:'a St) .
(clause_name "spec_temporal_conj_el1") /\
(( ( spec_temporal_holds Gt (Pt_implements c (St_conj St1 St2)) )))
 ==> 
( ( spec_temporal_holds Gt (Pt_implements c St1) )))

[spec_temporal_conj_el2:] (! (Gt:'a Gt) (c:c) (St2:'a St) (St1:'a St) .
(clause_name "spec_temporal_conj_el2") /\
(( ( spec_temporal_holds Gt (Pt_implements c (St_conj St1 St2)) )))
 ==> 
( ( spec_temporal_holds Gt (Pt_implements c St2) )))

[spec_temporal_par_in:] (! (Gt:'a Gt) (c1:c) (c2:c) (St1:'a St) (St2:'a St) .
(clause_name "spec_temporal_par_in") /\
(( ( spec_temporal_holds Gt (Pt_implements c1 St1) )) /\
( ( spec_temporal_holds Gt (Pt_implements c2 St2) )))
 ==> 
( ( spec_temporal_holds Gt (Pt_implements (c_comp c1 c2) (St_par St1 St2)) )))

[spec_temporal_par_el:] (! (Gt:'a Gt) (q1:q) (q2:q) (St1:'a St) (St2:'a St) (c:c) .
(clause_name "spec_temporal_par_el") /\
(( ( q1  <>  q2 ) ) /\
( ( q1  NOTIN   (fv_c  c )  ) ) /\
( ( q2  NOTIN   (fv_c  c )  ) ) /\
( ( spec_temporal_holds Gt (Pt_implements c (St_par St1 St2)) )))
 ==> 
( ( spec_temporal_holds Gt (Pt_exists_c q1 (Pt_exists_c q2 (Pt_and (Pt_implements (c_var q1) St1) (Pt_and (Pt_implements (c_var q2) St2) (Pt_c_eq c (c_comp (c_var q1) (c_var q2))))))) )))

[spec_temporal_cont_in:] (! (Gt:'a Gt) (c:c) (St1:'a St) (St2:'a St) (q:q) .
(clause_name "spec_temporal_cont_in") /\
(( ( q  NOTIN   (fv_c  c )  ) ) /\
( ( spec_temporal_holds Gt (Pt_forall_c q (Pt_implies (Pt_implements (c_var q) St1) (Pt_implements (c_comp (c_var q) c) St2))) )))
 ==> 
( ( spec_temporal_holds Gt (Pt_implements c (St_assume St1 St2)) )))

[spec_temporal_cont_el:] (! (Gt:'a Gt) (c1:c) (c2:c) (St2:'a St) (St1:'a St) .
(clause_name "spec_temporal_cont_el") /\
(( ( spec_temporal_holds Gt (Pt_implements c1 St1) )) /\
( ( spec_temporal_holds Gt (Pt_implements c2 (St_assume St1 St2)) )))
 ==> 
( ( spec_temporal_holds Gt (Pt_implements (c_comp c1 c2) St2) )))

[spec_temporal_cre:] (! (Gt:'a Gt) (c:c) (St2:'a St) (St3:'a St) (St1:'a St) .
(clause_name "spec_temporal_cre") /\
(( ( spec_temporal_holds Gt (Pt_implements c (St_conj St1 St2)) )) /\
( ( spec_temporal_holds Gt (Pt_refines St2 St3) )))
 ==> 
( ( spec_temporal_holds Gt (Pt_implements c (St_conj St2 St3)) )))

[spec_temporal_cr:] (! (Gt:'a Gt) (c:c) (St2:'a St) (St3:'a St) (St1:'a St) .
(clause_name "spec_temporal_cr") /\
(( ( spec_temporal_holds Gt (Pt_implements c (St_conj St1 St3)) )) /\
( ( spec_temporal_holds Gt (Pt_refines St1 St2) )))
 ==> 
( ( spec_temporal_holds Gt (Pt_implements c (St_conj St2 St3)) )))

[spec_temporal_and_in:] (! (Gt:'a Gt) (Pt1:'a Pt) (Pt2:'a Pt) .
(clause_name "spec_temporal_and_in") /\
(( ( spec_temporal_holds Gt Pt1 )) /\
( ( spec_temporal_holds Gt Pt2 )))
 ==> 
( ( spec_temporal_holds Gt (Pt_and Pt1 Pt2) )))

[spec_temporal_and_el1:] (! (Gt:'a Gt) (Pt1:'a Pt) (Pt2:'a Pt) .
(clause_name "spec_temporal_and_el1") /\
(( ( spec_temporal_holds Gt (Pt_and Pt1 Pt2) )))
 ==> 
( ( spec_temporal_holds Gt Pt1 )))

[spec_temporal_and_el2:] (! (Gt:'a Gt) (Pt2:'a Pt) (Pt1:'a Pt) .
(clause_name "spec_temporal_and_el2") /\
(( ( spec_temporal_holds Gt (Pt_and Pt1 Pt2) )))
 ==> 
( ( spec_temporal_holds Gt Pt2 )))

[spec_temporal_imp_in:] (! (Gt:'a Gt) (Pt1:'a Pt) (Pt2:'a Pt) .
(clause_name "spec_temporal_imp_in") /\
(( ( spec_temporal_holds  ( Pt1  INSERT  Gt )  Pt2 )))
 ==> 
( ( spec_temporal_holds Gt (Pt_implies Pt1 Pt2) )))

[spec_temporal_imp_el:] (! (Gt:'a Gt) (Pt2:'a Pt) (Pt1:'a Pt) .
(clause_name "spec_temporal_imp_el") /\
(( ( spec_temporal_holds Gt (Pt_implies Pt1 Pt2) )) /\
( ( spec_temporal_holds Gt Pt1 )))
 ==> 
( ( spec_temporal_holds Gt Pt2 )))

[spec_temporal_or_in1:] (! (Gt:'a Gt) (Pt1:'a Pt) (Pt2:'a Pt) .
(clause_name "spec_temporal_or_in1") /\
(( ( spec_temporal_holds Gt Pt1 )))
 ==> 
( ( spec_temporal_holds Gt (Pt_or Pt1 Pt2) )))

[spec_temporal_or_in2:] (! (Gt:'a Gt) (Pt1:'a Pt) (Pt2:'a Pt) .
(clause_name "spec_temporal_or_in2") /\
(( ( spec_temporal_holds Gt Pt2 )))
 ==> 
( ( spec_temporal_holds Gt (Pt_or Pt1 Pt2) )))

[spec_temporal_or_el:] (! (Gt:'a Gt) (Pt:'a Pt) (Pt1:'a Pt) (Pt2:'a Pt) .
(clause_name "spec_temporal_or_el") /\
(( ( spec_temporal_holds Gt (Pt_or Pt1 Pt2) )) /\
( ( spec_temporal_holds  ( Pt1  INSERT  Gt )  Pt )) /\
( ( spec_temporal_holds  ( Pt2  INSERT  Gt )  Pt )))
 ==> 
( ( spec_temporal_holds Gt Pt )))

[spec_temporal_not_in:] (! (Gt:'a Gt) (Pt1:'a Pt) (Pt2:'a Pt) .
(clause_name "spec_temporal_not_in") /\
(( ( spec_temporal_holds  ( Pt1  INSERT  Gt )  Pt2 )) /\
( ( spec_temporal_holds  ( Pt1  INSERT  Gt )  (Pt_not Pt2) )))
 ==> 
( ( spec_temporal_holds Gt (Pt_not Pt1) )))

[spec_temporal_not_el:] (! (Gt:'a Gt) (Pt:'a Pt) .
(clause_name "spec_temporal_not_el") /\
(( ( spec_temporal_holds Gt (Pt_not (Pt_not Pt)) )))
 ==> 
( ( spec_temporal_holds Gt Pt )))

[spec_temporal_all_el_c:] (! (Gt:'a Gt) (Pt:'a Pt) (c:c) (q:q) .
(clause_name "spec_temporal_all_el_c") /\
(( ( spec_temporal_holds Gt (Pt_forall_c q Pt) )))
 ==> 
( ( spec_temporal_holds Gt  (csubst_Pt (( q  =+  c ) c_var)  Pt )  )))

[spec_temporal_all_in_c:] (! (Gt:'a Gt) (q:q) (Pt:'a Pt) (q':q) .
(clause_name "spec_temporal_all_in_c") /\
(( ( q'  NOTIN   (  (fv_Pt_c  Pt )   UNION   (BIGUNION (IMAGE fv_Pt_c  Gt ))  )  ) ) /\
( ( spec_temporal_holds Gt  (csubst_Pt (( q  =+  (c_var q') ) c_var)  Pt )  )))
 ==> 
( ( spec_temporal_holds Gt (Pt_forall_c q Pt) )))

[spec_temporal_eq_el_c:] (! (Gt:'a Gt) (Pt:'a Pt) (c':c) (q:q) (c:c) .
(clause_name "spec_temporal_eq_el_c") /\
(( ( spec_temporal_holds Gt (Pt_c_eq c c') )) /\
( ( spec_temporal_holds Gt  (csubst_Pt (( q  =+  c ) c_var)  Pt )  )))
 ==> 
( ( spec_temporal_holds Gt  (csubst_Pt (( q  =+  c' ) c_var)  Pt )  )))

[spec_temporal_all_el_S:] (! (Gt:'a Gt) (Pt:'a Pt) (St:'a St) (V:V) .
(clause_name "spec_temporal_all_el_S") /\
(( ( spec_temporal_holds Gt (Pt_forall_St V Pt) )))
 ==> 
( ( spec_temporal_holds Gt  (Stsubst_Pt (( V  =+  St ) St_var)  Pt )  )))

[spec_temporal_all_in_S:] (! (Gt:'a Gt) (V:V) (Pt:'a Pt) (V':V) .
(clause_name "spec_temporal_all_in_S") /\
(( ( V'  NOTIN   (  (fv_Pt_St  Pt )   UNION   (BIGUNION (IMAGE fv_Pt_St  Gt ))  )  ) ) /\
( ( spec_temporal_holds Gt  (Stsubst_Pt (( V  =+  (St_var V') ) St_var)  Pt )  )))
 ==> 
( ( spec_temporal_holds Gt (Pt_forall_St V Pt) )))

[spec_temporal_eq_el_S:] (! (Gt:'a Gt) (Pt:'a Pt) (St':'a St) (V:V) (St:'a St) .
(clause_name "spec_temporal_eq_el_S") /\
(( ( spec_temporal_holds Gt (Pt_St_eq St St') )) /\
( ( spec_temporal_holds Gt  (Stsubst_Pt (( V  =+  St ) St_var)  Pt )  )))
 ==> 
( ( spec_temporal_holds Gt  (Stsubst_Pt (( V  =+  St' ) St_var)  Pt )  )))

[spec_temporal_ex_in_c:] (! (Gt:'a Gt) (q:q) (Pt:'a Pt) (c:c) .
(clause_name "spec_temporal_ex_in_c") /\
(( ( spec_temporal_holds Gt  (csubst_Pt (( q  =+  c ) c_var)  Pt )  )))
 ==> 
( ( spec_temporal_holds Gt (Pt_exists_c q Pt) )))

[spec_temporal_ex_el_c:] (! (Gt:'a Gt) (Gt':'a Gt) (Pt':'a Pt) (q':q) (Pt:'a Pt) (q:q) .
(clause_name "spec_temporal_ex_el_c") /\
(( ( q'  NOTIN   (  (fv_Pt_c  Pt )   UNION   (fv_Pt_c  Pt' )  )  ) ) /\
( ( q'  NOTIN   (  (BIGUNION (IMAGE fv_Pt_c  Gt ))   UNION   (BIGUNION (IMAGE fv_Pt_c  Gt' ))  )  ) ) /\
( ( spec_temporal_holds Gt (Pt_exists_c q Pt) )) /\
( ( spec_temporal_holds  (  (csubst_Pt (( q  =+  (c_var q') ) c_var)  Pt )   INSERT  Gt' )  Pt' )))
 ==> 
( ( spec_temporal_holds  ( Gt  UNION  Gt' )  Pt' )))

[spec_temporal_ex_in_S:] (! (Gt:'a Gt) (V:V) (Pt:'a Pt) (St:'a St) .
(clause_name "spec_temporal_ex_in_S") /\
(( ( spec_temporal_holds Gt  (Stsubst_Pt (( V  =+  St ) St_var)  Pt )  )))
 ==> 
( ( spec_temporal_holds Gt (Pt_exists_St V Pt) )))

[spec_temporal_ex_el_S:] (! (Gt:'a Gt) (Gt':'a Gt) (Pt':'a Pt) (V':V) (Pt:'a Pt) (V:V) .
(clause_name "spec_temporal_ex_el_S") /\
(( ( V'  NOTIN   (  (fv_Pt_St  Pt )   UNION   (fv_Pt_St  Pt' )  )  ) ) /\
( ( V'  NOTIN   (  (BIGUNION (IMAGE fv_Pt_St  Gt ))   UNION   (BIGUNION (IMAGE fv_Pt_St  Gt' ))  )  ) ) /\
( ( spec_temporal_holds Gt (Pt_exists_St V Pt) )) /\
( ( spec_temporal_holds  (  (Stsubst_Pt (( V  =+  (St_var V') ) St_var)  Pt )   INSERT  Gt' )  Pt' )))
 ==> 
( ( spec_temporal_holds  ( Gt  UNION  Gt' )  Pt' )))
End

val _ = export_theory ();



