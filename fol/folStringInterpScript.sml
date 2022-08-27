open HolKernel boolLib Parse bossLib pred_setTheory combinTheory stringTheory string_numTheory listTheory nlistTheory folLangTheory folModelsTheory folStringTheory;

val _ = new_theory "folStringInterp";

Definition eq_interp_pred:
 eq_interp_pred s l =
  if s = "=" then (EL 0 l = EL 1 l)
  else @x.T
End

Definition bool_interp_func:
 bool_interp_func s l = 
  if      s = "0" then T
  else if s = "1" then F
  else if s = "+" then (EL 0 l <> EL 1 l)
  else if s = "*" then (EL 0 l /\ EL 1 l)
  else @x.T
End

Definition bool_interp_smodel:
 bool_interp_smodel =
  <| SDom := UNIV; SFun := bool_interp_func; SPred := eq_interp_pred |>
End

Definition mod_interp_func:
 mod_interp_func n s l =
  if      s = "0" then 0
  else if s = "1" then 1 MOD n
  else if s = "+" then (EL 0 l + EL 1 l) MOD n
  else if s = "*" then (EL 0 l * EL 1 l) MOD n
  else @x.T
End

Definition mod_interp_smodel:
 mod_interp_smodel n =
  <| SDom := UNIV; SFun := mod_interp_func n; SPred := eq_interp_pred |>
End

val _ = export_theory ();
