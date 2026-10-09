import Submission.NK.ResidueFrob.LevelOfLocal
import Submission.NK.ResidueFrob.ExistsFrob
import Submission.NK.ResidueFrob.Inertia
import Submission.NK.ResidueFrob.levelInertiaCovered_of_tameData
import Submission.NK.LocalTame.Main
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The local–global residue-field dictionary at a place

This file assembles the three fields of `NK.FrobeniusBridge.PlaceLevelBridgeCore` from the
pieces proved in this chapter:

* `level_of_local` — `NK.ResidueFrob.level_of_local_of_data`, the residue-field form of the
  Frobenius normalisation (NSW (12.1.8));
* `exists_frob` — `NK.ResidueFrob.exists_frob_of_residueCardInput`, from the classical input
  `NK.LocalAnabelian.ResidueCardInput`;
* `inertia_surjective` — `NK.ResidueFrob.inertia_surjective_of_levelInertiaCovered`, applied to
  `NK.ResidueFrob.levelInertiaCovered_of_tameData`: **the level inertia statement is a theorem
  of this chapter**, not an input.

The point of `placeLevelBridgeCore_of_inputs` is that the two named inputs *not* contained in
`NK.FrobeniusBridge.PlaceLevelData` are displayed explicitly, and that no others are needed:

* `ResidueCardMatches A D.q` (the `q` of the local data is the residue cardinality of the base
  prime) is *necessary*: without it the hypothesis `NK.FrobeniusBridge.localFrobAt A g` admits
  elements whose residue-field action is `x ↦ x ^ (q)` for `q = #(𝓞K/𝔭) ^ a`, `a ≠ 1`, and
  `level_of_local` fails.  It is the content of `NK.LocalStructure.ResidueCardRecovery`, and it
  is not implied by `NK.LocalTame.TameData` alone.  In
  `Submission/Work/ResidueFrob/LocalStructureInputs.lean` it is discharged from the local structure
  theory (where `q` is *defined* as the residue cardinality of the completion).
* `ResidueCardInput` (the existence of a Frobenius element normalised by `κ^ur = κ(μ_{p'})`) is
  likewise not implied by `NK.LocalTame.TameData`: the latter's
  `TameStructureInput.exists_frobeniusLift` gives only an element outside `I_κ`, and
  `TameData.frobeniusLift` says that *if* such an element acts on the tame inertia by the `q`-th
  power map *then* it is normalised — but the existence of an element with that action is the
  content of `NK.LocalStructure.TameFrobeniusCore.exists_frob`, from which
  `ResidueCardInput` follows immediately
  (`NK.ResidueFrob.residueCardInput_of_tameFrobeniusCore`).
-/

namespace NK.ResidueFrob

open scoped Pointwise Classical

set_option linter.unusedSectionVars false

variable {K : Type*} [Field K] [NumberField K]
variable {K' : Type*} [Field K'] [Algebra K K'] [IsSepClosure K K']

/-- **The local structure inputs at a place determine the residue characteristic and the residue
field cardinality**: two `NK.LocalTame.TameData` at the same completion, together with the
`ℤ_ℓ²`-detection of the residue characteristic, have the same parameters. -/
theorem tameData_eq (A : NK.FrobeniusBridge.FinitePlaceOf K K') {p q p' q' : ℕ}
    (h : NK.LocalTame.TameData p q (NK.FrobeniusBridge.localField A)
      (NK.FrobeniusBridge.localClosure A))
    (h' : NK.LocalTame.TameData p' q' (NK.FrobeniusBridge.localField A)
      (NK.FrobeniusBridge.localClosure A))
    (hZ : NK.LocalTame.Zl2ResidueChar p (NK.FrobeniusBridge.localField A)
      (NK.FrobeniusBridge.localClosure A))
    (hZ' : NK.LocalTame.Zl2ResidueChar p' (NK.FrobeniusBridge.localField A)
      (NK.FrobeniusBridge.localClosure A)) :
    p = p' ∧ q = q' := by
  have hp : p = p' :=
    NK.LocalTame.residueChar_eq_of_zl2 hZ hZ' (MulEquiv.refl _)
  subst hp
  have hq : q - 1 = q' - 1 := by
    rw [← h.residueCard.card_torsion, ← h'.residueCard.card_torsion]
  have hq0 : 0 < q := by
    obtain ⟨f, hf, hqf⟩ := h.residueCard.q_eq
    rw [hqf]
    exact pow_pos (h.residueCard.hp.pos) f
  have hq0' : 0 < q' := by
    obtain ⟨f, hf, hqf⟩ := h'.residueCard.q_eq
    rw [hqf]
    exact pow_pos (h'.residueCard.hp.pos) f
  exact ⟨rfl, by omega⟩

/-- **The core of the local–global residue-field dictionary at a place.**  The three fields of
`NK.FrobeniusBridge.PlaceLevelBridgeCore A D` follow from the local data `D`, the
residue-cardinality input `ResidueCardMatches A D.q`, and the Frobenius existence input
`NK.LocalAnabelian.ResidueCardInput D.p D.q κ κ̄`.  The inertia field is supplied by
`NK.ResidueFrob.levelInertiaCovered_of_tameData`. -/
theorem placeLevelBridgeCore_of_inputs (A : NK.FrobeniusBridge.FinitePlaceOf K K')
    (D : NK.FrobeniusBridge.PlaceLevelData A)
    (hq : ResidueCardMatches A D.q)
    (hF : NK.LocalAnabelian.ResidueCardInput D.p D.q (NK.FrobeniusBridge.localField A)
      (NK.FrobeniusBridge.localClosure A)) :
    NK.FrobeniusBridge.PlaceLevelBridgeCore A D where
  level_of_local := by
    intro L _ _ _ g hg
    obtain ⟨hgD, p, q, hT, hZ, hΓ⟩ := hg
    obtain ⟨hp, hqq⟩ := tameData_eq A hT D.hT hZ D.hZ
    exact level_of_local_of_data A hT (hqq.trans hq) L g hgD hΓ
  exists_frob := exists_frob_of_residueCardInput A hF
  inertia_surjective :=
    inertia_surjective_of_levelInertiaCovered A (levelInertiaCovered_of_tameData A D.hT hq)

/-- **The local–global residue-field dictionary at a place**, from the inputs of
`placeLevelBridgeCore_of_inputs`. -/
theorem placeLevelBridge_of_inputs (A : NK.FrobeniusBridge.FinitePlaceOf K K')
    (D : NK.FrobeniusBridge.PlaceLevelData A)
    (hq : ResidueCardMatches A D.q)
    (hF : NK.LocalAnabelian.ResidueCardInput D.p D.q (NK.FrobeniusBridge.localField A)
      (NK.FrobeniusBridge.localClosure A)) :
    NK.FrobeniusBridge.PlaceLevelBridge A :=
  (placeLevelBridgeCore_of_inputs A D hq hF).toPlaceLevelBridge

/-- **The inputs of the residue-field dictionary at a place**, in one bundle.  Both fields beyond
the local data `D` are supplied by the local structure theory of the completion; see
`Submission/Work/ResidueFrob/LocalStructureInputs.lean`. -/
structure PlaceLevelInputs (A : NK.FrobeniusBridge.FinitePlaceOf K K') where
  /-- the local data (`p`, `q`, the tame structure inputs) -/
  D : NK.FrobeniusBridge.PlaceLevelData A
  /-- `q` is the residue cardinality of the base prime -/
  hq : ResidueCardMatches A D.q
  /-- the existence of the normalised Frobenius of the local field -/
  hF : NK.LocalAnabelian.ResidueCardInput D.p D.q (NK.FrobeniusBridge.localField A)
    (NK.FrobeniusBridge.localClosure A)

/-- **The local–global residue-field dictionary at every place**, from the inputs
`PlaceLevelInputs`. -/
theorem frobDictionary_of_placeLevelInputs (h : ∀ A : NK.FrobeniusBridge.FinitePlaceOf K K',
    PlaceLevelInputs A) : NK.FrobeniusBridge.FrobDictionary K K' :=
  fun A => placeLevelBridge_of_inputs A (h A).D (h A).hq (h A).hF

end NK.ResidueFrob
