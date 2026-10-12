import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.ae_sliceCoeff_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The weak-state twin of `Work.BoseBoxFock.ae_sliceCoeff_le`

`Work.BoseBoxFock.ae_sliceCoeff_le` bounds the squared modulus of the fibre coefficient
`∫ conj (M_α) · slice_y` by the Cauchy–Schwarz product, for a state `Φ` that is continuous with
compact support.  Its proof is a two-line wrapper around
`Work.BoseBoxFock.ae_sliceCoeff_le_of_memLp`, whose only state hypothesis is
`MemLp Ψ ⊤`; here `Ψ = (Φ : ℂ)` is measurable and everywhere bounded (the class of the box
restriction `Φ·1_abox` of `Work.BoseBoxFock.box_to_model`), and `MemLp _ ⊤` follows from
`MeasureTheory.memLp_top_of_bound` (which needs no finiteness of the measure).
-/

namespace Work.BoseBoxFock

open MeasureTheory

theorem ae_sliceCoeff_le_weak {m n : ℕ} [NeZero m] {ℓ : ℝ} (hℓ : 0 < ℓ)
    {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ}
    (he : ∀ l l', (∫ x : EuclideanSpace ℝ (Fin 3), (starRingEnd ℂ) (e l x) * e l' x)
      = if l = l' then 1 else 0)
    (hbdd : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (hc : ∃ c : ℂ, (starRingEnd ℂ) c * c = (ℓ ^ 3)⁻¹ ∧
      (∀ᵐ x ∂(MeasureTheory.volume :
          MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))),
        e 0 x = c * Work.BoseK15.corpusBox.thetaFun ℓ x))
    (S : Finset (Fin n)) {Φ : Submission.BoseGases.X n → ℝ}
    (hΦm : Measurable Φ) (hΦb : ∃ C : ℝ, ∀ x, |Φ x| ≤ C)
    (α : Fin m →₀ ℕ) (hk : 0 < S.card - α 0) :
    ∀ᵐ y ∂(MeasureTheory.volume :
        MeasureTheory.Measure ({i // i ∉ S} → EuclideanSpace ℝ (Fin 3))),
      ‖∫ u : Fin S.card → EuclideanSpace ℝ (Fin 3),
          (starRingEnd ℂ) (Work.BoseDict.modeProd e S.card α u)
            * Work.BoseBoxFock.sliceF e S (fun x => ((Φ x : ℝ) : ℂ)) y u‖ ^ 2
        ≤ (∫ u in Submission.BoseGases.abox S.card ℓ,
              ‖Work.BoseDict.modeProd e S.card α u‖ ^ 2)
          * (∫ u in Submission.BoseGases.abox S.card ℓ,
              ‖Work.BoseBoxFock.sliceF e S (fun x => ((Φ x : ℝ) : ℂ)) y u‖ ^ 2) := by
  have hΦb' : ∃ C : ℝ, ∀ x, |Φ x| ≤ C := hΦb
  obtain ⟨B, hB⟩ := hΦb'
  have hΨbdd : ∀ x, ‖(fun x : Submission.BoseGases.X n => ((Φ x : ℝ) : ℂ)) x‖ ≤ max B 0 := by
    intro x
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact le_trans (hB x) (le_max_left B 0)
  have hmem : MeasureTheory.MemLp
      (fun x : Submission.BoseGases.X n => ((Φ x : ℝ) : ℂ)) ⊤
      (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)) :=
    MeasureTheory.memLp_top_of_bound
      (Complex.continuous_ofReal.measurable.comp hΦm).aestronglyMeasurable
      (max B 0) (Filter.Eventually.of_forall hΨbdd)
  exact ae_sliceCoeff_le_of_memLp hℓ he hbdd hsupp hc S hmem α hk

end Work.BoseBoxFock
