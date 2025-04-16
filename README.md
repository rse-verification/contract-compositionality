# Contract Compositionality

A HOL4 formalization of a theory of specifications, components, contracts, and compositionality.

## Building

Requirements:
- [Poly/ML 5.7.1](https://github.com/polyml/polyml) (or later)
- [HOL4 trindemossen-1](https://github.com/HOL-Theorem-Prover/HOL/releases/tag/trindemossen-1)

The default Makefile task, which assumes `Holmake` is available on the system, builds all core HOL4 theories:

```shell
make
```

## List of HOL4 files

- [`folStringScript.sml`](fol/folStringScript.sml): first-order logic (FOL) with string identifiers, based on the [FOL formalization in HOL4 examples](https://github.com/HOL-Theorem-Prover/HOL/tree/develop/examples/logic/folcompactness), port from Harrison's [HOL Light formalization](https://github.com/jrh13/hol-light/commit/013324af7ff715346383fb963d323138)
- [`folStringInterpScript.sml`](fol/folStringInterpScript.sml): some simple first-order theories using string identifiers, for validation
- [`compSpecUtilityScript.sml`](semantics/compSpecUtilityScript.sml): some utility definitions and results
- [`compSpecScript.sml`](semantics/compSpecScript.sml): definition of abstract syntax for specifications, components, and predicates, and definition of proof systems
- [`compSpecMetaScript.sml`](semantics/compSpecMetaScript.sml): semantics and metatheory of specifications and components, including proof system soundness
- [`compSpecFolScript.sml`](semantics/compSpecFolScript.sml): interpretation as first-order theory
- [`compSpecExampleScript.sml`](semantics/compSpecExampleScript.sml): examples of proof system use
- [`mitlScript.sml`](semantics/mitlScript.sml): MITL formal semantics
- [`compSpecMitlScript.sml`](semantics/compSpecMitlScript.sml): instantiation of specifications for MITL
- [`compSpecMitlFLDScript.sml`](semantics/compSpecMitlFLDScript.sml): instantiation for a fuel level display (FLD) system

## Key definitions and results

### First-order logic

- The abstract syntax of FOL and satisfaction relation for FOL that uses strings for atomic propositions in [`folStringScript.sml`](fol/folStringScript.sml):
  - `Datatype: sterm = ...`
  - `Datatype: sform = ...`
  - `Definition sholds: ...`
- Equivalence of `sholds` relation with `holds` relation that uses numbers for atomic propositions [from HOL4 examples](https://github.com/HOL-Theorem-Prover/HOL/tree/develop/examples/logic/folcompactness) in `folStringScript.sml`:
  - `Theorem sholds_holds: ...`
  - `Theorem holds_sholds: ...`

### Specification language syntax and semantics

- The (non-extended) specification language abstract syntax in [`compSpecScript.sml`](semantics/compSpecScript.sml):
  - `Sc =  (* specification constant *) ...`
  - `c =  (* component term *) ...`
  - `S =  (* specification term *) ...`
  - `P =  (* component specification predicate *) ...`
- Proof system for the non-extended specification language as an inductive predicate in [`compSpecScript.sml`](semantics/compSpecScript.sml):
  - `Inductive spec_proof: (* defn spec_holds *) ...`
- Semantics of the (non-extended) specification language in [`compSpecMetaScript.sml`](semantics/compSpecMetaScript.sml):
  - `Definition c_sem: ...` (semantics of components)
  - `Definition S_sem: ...` (semantics of specifications)
  - `Definition P_sem: ...` (semantics of predicates)

### Specification language metatheory

- Interpretation of the (non-extended) specification language as a FOL theory in [`compSpecFolScript.sml`](semantics/compSpecFolScript.sml):
  - `Definition spec_interp_func: ...` (interpretation of function symbols and constants)
  - `Definition spec_interp_pred: ...` (interpretation of predicates)
  - `Definition spec_interp_smodel: ...` (first-order structure/signature)
- Translation of (non-extended) specification language to FOL formulas in [`compSpecFolScript.sml`](semantics/compSpecFolScript.sml):
  - `Definition c2sterm: ...`
  - `Definition S2sterm: ...`
  - `Definition P2sform: ...`
  - `Definition cSval: ...`
- **Theorem 1**: soundness of specification language predicate translation to FOL in [`compSpecFolScript.sml`](semantics/compSpecFolScript.sml):
  - `Theorem P_sem_sholds: ...` (soundness for satisfaction relation with strings for atomic propositions)
  - `Theorem P_sem_holds: ...` (soundness for satisfaction relation with numbers for atomic propositions)
- **Theorem 2**: proof system soundness w.r.t. specification language semantics in [`compSpecMetaScript.sml`](semantics/compSpecMetaScript.sml):
  - `Definition spec_system_sound: ...` (definition of a sound proof system)
  - `Theorem spec_holds_system_sound: ...` (soundness for proof system defined in `spec_proof` inductive predicate)
- Soundness of decomposition of proof of a specification language predicate `c1 * c2 * c3 : S0` into proofs of individual components and specification refinement proof in [`compSpecMetaScript.sml`](semantics/compSpecMetaScript.sml):
  - `Theorem compositionality_contracts_three: ...`

### Specification language and proof system examples

- **Example 4**: compositional specification and proof example in [`compSpecExampleScript.sml`](semantics/compSpecExampleScript.sml):
  - `Definition example_Ps: ...` (premises)
  - `Definition example_goal: ...` (goal)
  - `Theorem example_refine_spec_holds: ...` (proof system proof of goal assuming premises)
  - `Theorem example_refine_sem_spec_holds: ...` (semantic predicate theorem using soundness of proof system)
  
### Extended specification language syntax and semantics

- Interval and MITL abstract syntax in [`compSpecScript.sml`](semantics/compSpecScript.sml):
  - `I = ...` (interval)
  - `f = ...` (MITL formula)
- MITL semantics in [`mitlScript.sml`](semantics/mitlScript.sml):
  - `Definition interval_sem: ...` (interval semantics)  
  - `Type timed_word = ...` (timed word definition)
  - `Definition mitl_general_sem: ...` (MITL semantics as sets of timed words)
- Extended specification language syntax in [`compSpecScript.sml`](semantics/compSpecScript.sml):
  - `T =  (* temporal specification constant *) ...`
  - `St =  (* temporal specification term *) ...`
  - `Pt =  (* temporal component specification predicate *) ...`
- Extended specification language proof system as inductive predicate in [`compSpecScript.sml`](semantics/compSpecScript.sml):
  - `Inductive spec_temporal_proof: (* defn spec_temporal_holds *) ...`
- Semantics of the extended specification language in [`compSpecMitlScript.sml`](semantics/compSpecMitlScript.sml):
  - `Definition St_sem: ...` (semantics of temporal specification terms)
  - `Definition Pt_sem: ...` (semantics of temporal predicates)
- Metatheory of extended specification language in [`compSpecMitlScript.sml`](semantics/compSpecMitlScript.sml):
  - `Inductive spec_temporal_mitl_proof: ...` (MITL proof system rule)
  - `Definition spec_temporal_mitl_system_sound: ...` (temporal proof system soundness)
  - `Theorem spec_temporal_mitl_holds_system_sound: ...` (soundness of MITL proof system rule)

### Fuel-level display (FLD) system model

- FLD instantiation in [`compSpecMitlFLDScript.sml`](semantics/compSpecMitlFLDScript.sml):
  - `Type state_FLD = ...` (FLD states as mappings from system variables to values)
  - `Definition state_holds_FLD: ...` (constraint expressions relation for FLD states)
  - `Type timed_word_FLD = ...` (FLD timed words)
  - `Definition omega_FLD: ...` (FLD system runs as set of timed words)
  - `Definition spec_temporal_holds_FLD_def: ...` (temporal proof system instantiation for FLD)
