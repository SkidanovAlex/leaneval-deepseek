import Mathlib
import Submission.Work.Mostow.tiDefs
import Submission.Work.Mostow.volH_le_fundamentalDomain

/-!
# `Work.Mostow.fund_domain_hull_null`

Let `Γ ≤ PO(n,1)` be a group acting on hyperbolic space `ℍⁿ = E n`, and let `DY` be a fundamental
domain for `Γ` with respect to `volH n`.  If `γ ∈ Γ` is non-trivial, then the *measurable hull*
`toMeasurable (volH n) DY` of `DY` meets its own `γ`-translate only in a `volH n`-null set:

`volH n (toMeasurable (volH n) DY ∩ γ • toMeasurable (volH n) DY) = 0`.

This is the measure-theoretic content of "the translates of a fundamental domain are essentially
disjoint": the fundamental-domain property gives `AEDisjoint (volH n) DY (γ • DY)`, the action of
`PO(n,1)` is measure preserving (`HypIsometryProp`), so it preserves null sets, and
`toMeasurable μ s =ᵐ[μ] s`.

Nothing here is specific to Mostow rigidity; the statement is the standard fact that a fundamental
domain of a measure-preserving action meets each of its non-trivial translates in a null set.
-/

namespace Work.Mostow

set_option linter.style.haveILetI false

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory
open scoped Pointwise

noncomputable section

variable {n : ℕ}

/-- The measurable hull of a fundamental domain meets each non-trivial translate of itself in a
null set. -/
theorem volH_toMeasurable_inter_smul_null (hI : Submission.Mostow.HypIsometryProp n)
    (Γ : Subgroup (LeanEval.Geometry.MostowRigidity.PO n 1)) (D : Set (Submission.Mostow.E n))
    (hD : MeasureTheory.IsFundamentalDomain Γ D (Submission.Mostow.volH n))
    (g : LeanEval.Geometry.MostowRigidity.PO n 1) (hg : g ∈ Γ)
    (hg1 : (⟨g, hg⟩ : Γ) ≠ 1) :
    Submission.Mostow.volH n
      (MeasureTheory.toMeasurable (Submission.Mostow.volH n) D ∩
        g • MeasureTheory.toMeasurable (Submission.Mostow.volH n) D) = 0 := by
  classical
  have hId : HypIsoData n := HypIsoData.ofProp hI
  -- the action laws coming from `POActionProp`-free facts, upgrade `SMul` to a `MulAction`
  letI : MulAction (PO n 1) (E n) :=
    { toSMul := Submission.Mostow.instSMulPO, one_smul := poOneSMul, mul_smul := poMulSMul }
  letI : MulAction Γ (E n) := inferInstance
  -- the action preserves the measure, hence quasipreserves it
  have hqmp : ∀ g : PO n 1,
      Measure.QuasiMeasurePreserving (fun u : E n => g • u) (volH n) (volH n) :=
    fun g => (hId.measurePreserving_smul g).quasiMeasurePreserving
  -- the fundamental domain is a.e. disjoint from its non-trivial translate
  have hone : ((1 : Γ) • D : Set (E n)) = D := by
    rw [show ((1 : Γ) • D : Set (E n)) = ((1 : PO n 1) • D) from rfl, one_smul]
  have had : AEDisjoint (volH n) D (g • D) := by
    have h0 := hD.aedisjoint (show (1 : Γ) ≠ ⟨g, hg⟩ from Ne.symm hg1)
    simp only [Function.onFun] at h0
    rwa [hone, show ((⟨g, hg⟩ : Γ) • D : Set (E n)) = (g • D) from rfl] at h0
  -- replace `D` by its measurable hull
  have htm_ae : MeasureTheory.toMeasurable (volH n) D =ᵐ[volH n] D :=
    hD.nullMeasurableSet.toMeasurable_ae_eq
  have hsmul_ae : g • MeasureTheory.toMeasurable (volH n) D =ᵐ[volH n] g • D :=
    Measure.QuasiMeasurePreserving.smul_ae_eq_of_ae_eq g (hqmp g⁻¹) htm_ae
  exact (had.congr htm_ae hsmul_ae).eq

theorem fund_domain_hull_null (j : ℕ) (hI : Submission.Mostow.HypIsometryProp j)
    (Γ : Subgroup (LeanEval.Geometry.MostowRigidity.PO j 1)) (DY : Set (Submission.Mostow.E j))
    (hDY : MeasureTheory.IsFundamentalDomain Γ DY (Submission.Mostow.volH j))
    (γ : Γ) (hγ : γ ≠ 1) :
    Submission.Mostow.volH j ((MeasureTheory.toMeasurable (Submission.Mostow.volH j) DY) ∩
      (fun x : Submission.Mostow.E j => (γ : LeanEval.Geometry.MostowRigidity.PO j 1) • x) ''
        (MeasureTheory.toMeasurable (Submission.Mostow.volH j) DY)) = 0 := by
  have hmain := volH_toMeasurable_inter_smul_null hI Γ DY hDY
    (γ : LeanEval.Geometry.MostowRigidity.PO j 1) γ.2 hγ
  simpa only [Set.image_smul] using hmain

end

end Work.Mostow
