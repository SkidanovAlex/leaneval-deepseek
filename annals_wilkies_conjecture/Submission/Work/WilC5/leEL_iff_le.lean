import Mathlib
import Submission.Work.WilC5.LRcOps
import Submission.Work.WilC5.tr_leE_axioms
import Submission.Work.WilC2.Square

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
open Classical
namespace Work.WilC5

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture FirstOrder Language
open scoped FirstOrder

/-- **The definable order of a model of `TR` agrees with the order of the language of rings:**
`leEL x y` (i.e. `y - x` is a square) holds iff `x ≤ y`. -/
theorem leEL_iff_le {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [FirstOrder.Ring.CompatibleRing M] [WilkiesDesign.CG.rexpL.Structure M]
    [(FirstOrder.Language.constantsOn ℝ).Structure M]
    (h : FirstOrder.Language.Theory.Model M WilkiesDesign.CG.TR) (x y : M) :
    Work.WilC5.leEL x y ↔ x ≤ y := by
  have hsq := Work.WilC2.model_exists_sq (M := M) h
  have hb : ∀ (n : ℕ) (f : Language.ring.Functions n) (xs : Fin n → M),
      @Structure.funMap LRc M _ n (Sum.inl (Sum.inl f)) xs =
      @Structure.funMap Language.ring M _ n f xs :=
    fun n f xs => (Work.WilC2.instRingToLRcIsExpansionOn M).map_onFunction f xs
  have hmul : ∀ a b : M, Work.WilC5.mulEL a b = a * b := by
    intro a b
    rw [Work.WilC5.mulEL, Work.WilC5.ringSymL, hb 2 Ring.mulFunc ![a, b] ]
    simp [Ring.CompatibleRing.funMap_mul]
  have hneg : ∀ a : M, Work.WilC5.negEL a = -a := by
    intro a
    rw [Work.WilC5.negEL, Work.WilC5.ringSymL, hb 1 Ring.negFunc ![a] ]
    simp [Ring.CompatibleRing.funMap_neg, Matrix.cons_val_fin_one]
  have hadd : ∀ a b : M, Work.WilC5.addEL a b = a + b := by
    intro a b
    rw [Work.WilC5.addEL, Work.WilC5.ringSymL, hb 2 Ring.addFunc ![a, b] ]
    simp [Ring.CompatibleRing.funMap_add]
  have hsub : ∀ a b : M, Work.WilC5.subEL a b = a - b := by
    intro a b
    rw [Work.WilC5.subEL, hadd, hneg]; ring
  constructor
  · rintro ⟨z, hz⟩
    rw [hmul, hsub] at hz
    nlinarith [mul_self_nonneg z]
  · intro hxy
    obtain ⟨z, hz⟩ := hsq (y - x) (sub_nonneg.mpr hxy)
    exact ⟨z, by rw [hmul, hsub]; exact hz.symm⟩

end Work.WilC5
