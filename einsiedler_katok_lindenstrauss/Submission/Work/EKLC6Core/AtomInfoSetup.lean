import Mathlib
import Submission.Work.EKLC6Core.growth_le_HcondSig
import Submission.Work.EKLC6Core.uminus_isHoro
import Submission.Work.EKLRelCross.leafwise_acovariant
import Submission.Work.EKLC6Core.shape_mass_pos

/-!
# `EKLC6Core.AtomInfoSetup` — vocabulary and bookkeeping for `HcondSig_le_lintegral_atomInfo`

The target `Work.EKLC6Core.HcondSig_le_lintegral_atomInfo` bounds the σ-algebra conditional
entropy `HcondSig μ A (comap (aDiag t ·) A)` by the integral of the pointwise "surprisal"
`atomInfo A (Uminus t) ν t x = -log (ν x (shape A U x) / ν x (shape (comap (aDiag t ·) A) U x))`
of the `A`-atom of `x` inside its `comap (aDiag t ·) A`-atom.

This module collects the objects and elementary facts needed.

* `betaAlg t S = comap (aDiag t ·) S.m` — the pull-back σ-algebra (the conditioning algebra);
  the σ-algebra is wrapped in the structure `EKLRelCross.MSAlg` so that the local variable
  cannot be picked up by type-class search (see the note in `EKLC6Core.Hcond_mono`).
* `Wsh t S U x = shape (betaAlg t S) U x` — the `U`-shape of the pull-back atom;
* `Dpart t S U P i x = Wsh t S U x ∩ {u | u • x ∈ P.parts i}`;
* `isPlaqueAlgebra_betaAlg`, `measurableSet_shape`, `mass_Wsh`, `condExp_betaAlg_eq`.

NOTE.  This file deliberately lives in the `growth_le_HcondSig` import branch (it must, since the
target statement mentions `Work.EKLC6Core.atomInfo`, defined there).  The module
`EKLC6Core.HcondSig_le_growth` contains very similar lemmas, but the two cannot be imported
together (`atom_comap`, `shape_comap_eq`, … are defined in both), so the facts below are proved
here again in this branch.
-/

open MeasureTheory Filter Topology
open scoped ENNReal
open LeanEval.Dynamics.EinsiedlerKatokLindenstrauss

set_option linter.unusedVariables false
set_option warn.classDefReducibility false
set_option maxHeartbeats 800000

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-- The pull-back σ-algebra `comap (aDiag t ·) S.m`. -/
def betaAlg (t : Fin 3 → ℝ) (S : Work.EKLRelCross.MSAlg) : MeasurableSpace X3 :=
  MeasurableSpace.comap (fun y : X3 => aDiag t • y) S.m

@[simp] theorem betaAlg_def (t : Fin 3 → ℝ) (S : Work.EKLRelCross.MSAlg) :
    betaAlg t S = MeasurableSpace.comap (fun y : X3 => aDiag t • y) S.m := rfl

/-- The `U`-shape of the pull-back atom `[x]_{comap (aDiag t ·) S.m}`. -/
def Wsh (t : Fin 3 → ℝ) (S : Work.EKLRelCross.MSAlg) (U : Subgroup SL3) (x : X3) : Set SL3 :=
  shape (betaAlg t S) U x

@[simp] theorem Wsh_def (t : Fin 3 → ℝ) (S : Work.EKLRelCross.MSAlg) (U : Subgroup SL3)
    (x : X3) : Wsh t S U x = shape (betaAlg t S) U x := rfl

/-- The piece of the pull-back shape lying over the partition part `P.parts i`. -/
def Dpart (t : Fin 3 → ℝ) (S : Work.EKLRelCross.MSAlg) (U : Subgroup SL3) (P : FinPart X3)
    (i : Fin P.n) (x : X3) : Set SL3 :=
  Wsh t S U x ∩ {u : SL3 | u • x ∈ P.parts i}

@[simp] theorem Dpart_def (t : Fin 3 → ℝ) (S : Work.EKLRelCross.MSAlg) (U : Subgroup SL3)
    (P : FinPart X3) (i : Fin P.n) (x : X3) :
    Dpart t S U P i x = Wsh t S U x ∩ {u : SL3 | u • x ∈ P.parts i} := rfl

/-- The pull-back of a plaque algebra along `aDiag t ·` is a plaque algebra; the base set is
`(aDiag t ·) ⁻¹' Z`. -/
theorem isPlaqueAlgebra_betaAlg {U : Subgroup SL3} (hU : IsHoro U) {Z : Set X3}
    {S : Work.EKLRelCross.MSAlg} (hA : IsPlaqueAlgebra U Z S.m) (t : Fin 3 → ℝ) :
    IsPlaqueAlgebra U ((fun y : X3 => aDiag t • y) ⁻¹' Z) (betaAlg t S) := by
  have h := Work.EKLRelCross.isPlaqueAlgebra_translate (S := S) hU t hA
  have hZmem : MeasurableSet[betaAlg t S] ((fun y : X3 => aDiag t • y) ⁻¹' Z) :=
    MeasurableSpace.measurableSet_comap.mpr ⟨Z, hA.2.2.1, rfl⟩
  have hsup : (S.translate t Z).m = betaAlg t S := by
    rw [Work.EKLRelCross.MSAlg.translate, betaAlg]
    exact sup_eq_left.mpr (MeasurableSpace.generateFrom_le (fun s hs => by
      rw [Set.mem_singleton_iff] at hs
      rw [hs]
      exact hZmem))
  rw [hsup] at h
  exact h

/-- The `U`-shape of a plaque algebra at a point of its base set is measurable. -/
theorem measurableSet_shape {U : Subgroup SL3} (hU : IsHoro U) {A : MeasurableSpace X3}
    {Z : Set X3} (hA : IsPlaqueAlgebra U Z A) {x : X3} (hx : x ∈ Z) :
    MeasurableSet (shape A U x) := by
  obtain ⟨O, hOopen, hOeq⟩ := (hA.2.2.2 x hx).2.2.1
  rw [hOeq]
  exact hOopen.measurableSet.inter hU.1.measurableSet

/-- The `ν x`-mass of the pull-back shape is positive and finite. -/
theorem mass_Wsh {μ : Measure X3} [IsProbabilityMeasure μ] {U : Subgroup SL3}
    (hU : IsHoro U) {ν : X3 → Measure SL3} {X' : Set X3} (hL : IsLeafwise μ U ν X')
    {S : Work.EKLRelCross.MSAlg} {Z : Set X3} (hA : IsPlaqueAlgebra U Z S.m) (t : Fin 3 → ℝ)
    {x : X3} (hxX' : x ∈ X') (hxTZ : x ∈ (fun y : X3 => aDiag t • y) ⁻¹' Z) :
    0 < ν x (Wsh t S U x) ∧ ν x (Wsh t S U x) < ⊤ := by
  have h := shape_mass_pos hL (isPlaqueAlgebra_betaAlg hU hA t) hxX' hxTZ
  rw [Wsh_def]
  exact h

/-- The `condexp` field of `IsLeafwise` for the pulled-back plaque algebra `betaAlg t S`. -/
theorem condExp_betaAlg_eq {μ : Measure X3} [IsProbabilityMeasure μ] {U : Subgroup SL3}
    (hU : IsHoro U) {ν : X3 → Measure SL3} {X' : Set X3} (hL : IsLeafwise μ U ν X')
    {S : Work.EKLRelCross.MSAlg} {Z : Set X3} (hA : IsPlaqueAlgebra U Z S.m) (t : Fin 3 → ℝ)
    (hmp : MeasurePreserving (fun y : X3 => aDiag t • y) μ μ) (hZ : μ Zᶜ = 0)
    (f : X3 → ℝ) (hf : Measurable f) (hfb : ∃ C, ∀ y, |f y| ≤ C) :
    ∀ᵐ x ∂μ, condExp (betaAlg t S) μ f x =
      (∫ u in Wsh t S U x, f (u • x) ∂(ν x)) / (ν x (Wsh t S U x)).toReal := by
  have hAZ : MeasurableSet Z := hA.1 Z hA.2.2.1
  have hTZ : μ ((fun y : X3 => aDiag t • y) ⁻¹' Z)ᶜ = 0 := by
    rw [← Set.preimage_compl, hmp.measure_preimage hAZ.compl.nullMeasurableSet]
    exact hZ
  have hres : μ.restrict ((fun y : X3 => aDiag t • y) ⁻¹' Z) = μ :=
    Measure.restrict_eq_self_of_ae_mem (by rw [MeasureTheory.ae_iff]; exact hTZ)
  have hfield := hL.condexp ((fun y : X3 => aDiag t • y) ⁻¹' Z) (betaAlg t S)
    (isPlaqueAlgebra_betaAlg hU hA t) f hf hfb
  rw [← hres]
  filter_upwards [hfield] with x hx
  simpa only [Wsh_def] using hx

end Work.EKLC6Core

end
