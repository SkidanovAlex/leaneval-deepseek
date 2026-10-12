import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.MB.SlotWeakBase
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.integrable_conjEtaOf_mul` — the `L¹` half of the dictionary's slot integral

The slot integral of the box ↔ model dictionary is `∫_z conj(η_v z)·Θ(x[j ↦ z])` with
`η_v = Σ_l v_l e_l = ` `Work.BoseDict.etaOf e v`.  Every estimate on that integral is obtained
by dominating the integrand with `z ↦ ‖η_v z‖·sup ‖Θ‖` and then integrating, which is legitimate
only once `z ↦ conj(η_v z)·F z` is known to be *integrable* for an arbitrary bounded measurable
`F`.  This module supplies exactly that.

The point is that no smoothness of the modes `e l` is assumed — only measurability, boundedness
and **support inside the corpus box** `Λ(ℓ) = ℓ • cell` (`Work.BoseK15.corpusBox`, the box of
FS's χ, whose cell is compact of volume `1`).  The support hypothesis is what makes the product
integrable: `conj(η_v)` is bounded and supported in the finite-measure, hence integrable set
`Λ(ℓ)`, and the bounded measurable factor `F` cannot destroy that.

The proof is therefore: `conj(η_v)·F` is measurable (finite sum + conjugation + product),
bounded by `(Σ_l |v l|·sup_l ‖e l‖)·sup‖F‖`, and supported in `Λ(ℓ)` — a bounded measurable
function supported in a set of finite measure is integrable
(`IntegrableOn.of_bound` on `Λ(ℓ)` followed by `IntegrableOn.integrable_of_forall_notMem_eq_zero`).
-/

namespace Work.BoseBoxFock

open MeasureTheory

set_option autoImplicit false

theorem integrable_conjEtaOf_mul {m : ℕ} {ℓ : ℝ} {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (v : Fin m → ℝ) {F : EuclideanSpace ℝ (Fin 3) → ℂ} (hFm : Measurable F)
    (hFb : ∃ C : ℝ, ∀ z, ‖F z‖ ≤ C) :
    MeasureTheory.Integrable
      (fun z : EuclideanSpace ℝ (Fin 3) => (starRingEnd ℂ) (Work.BoseDict.etaOf e v z) * F z) := by
  -- Bounds: `C l` for the modes, `CF` for `F`.
  choose C eC using hbdd
  obtain ⟨CF, hCF⟩ := hFb
  -- `η_v` is the finite sum `Σ_l (v l : ℂ) · e l`, definitionally.
  have heta_eq : ∀ z, Work.BoseDict.etaOf e v z = ∑ l : Fin m, (v l : ℂ) * e l z := fun _ => rfl
  -- Bound on `η_v`.
  have heta_b : ∀ z, ‖Work.BoseDict.etaOf e v z‖ ≤ ∑ l : Fin m, |v l| * max (C l) 0 := by
    intro z
    rw [heta_eq z]
    calc ‖∑ l : Fin m, (v l : ℂ) * e l z‖
        ≤ ∑ l : Fin m, ‖(v l : ℂ) * e l z‖ := norm_sum_le _ _
      _ ≤ ∑ l : Fin m, |v l| * max (C l) 0 := by
          refine Finset.sum_le_sum fun l _ => ?_
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left ((eC l z).trans (le_max_left _ _)) (abs_nonneg _)
  have hBt_nonneg : 0 ≤ ∑ l : Fin m, |v l| * max (C l) 0 :=
    Finset.sum_nonneg fun l _ => mul_nonneg (abs_nonneg _) (le_max_right _ _)
  -- Bound on the product.
  have hG_b : ∀ z, ‖(starRingEnd ℂ) (Work.BoseDict.etaOf e v z) * F z‖
      ≤ (∑ l : Fin m, |v l| * max (C l) 0) * max CF 0 := by
    intro z
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul (heta_b z) ((hCF z).trans (le_max_left _ _)) (norm_nonneg _) hBt_nonneg
  -- Measurability.
  have heta_m : Measurable (fun z => Work.BoseDict.etaOf e v z) := by
    rw [show (fun z => Work.BoseDict.etaOf e v z)
        = fun z => ∑ l : Fin m, (v l : ℂ) * e l z from funext heta_eq]
    exact Finset.measurable_sum _ fun l _ => measurable_const.mul (hmeas l)
  have hG_m : Measurable (fun z => (starRingEnd ℂ) (Work.BoseDict.etaOf e v z) * F z) :=
    (Complex.continuous_conj.measurable.comp heta_m).mul hFm
  -- Support: `η_v` vanishes off `Λ(ℓ)`, since every `e l` does.
  have hsuppEta : Function.support (fun z => Work.BoseDict.etaOf e v z)
      ⊆ Work.BoseK15.corpusBox.boxL ℓ := by
    intro z hz
    by_contra hzbox
    refine hz ?_
    show Work.BoseDict.etaOf e v z = 0
    rw [heta_eq z]
    exact Finset.sum_eq_zero fun l _ => by
      have h0 : e l z = 0 := by
        by_contra h
        exact hzbox (hsupp l (Function.mem_support.mpr h))
      rw [h0, mul_zero]
  -- `Λ(ℓ)` is compact, hence of finite measure.
  have hfin : volume (Work.BoseK15.corpusBox.boxL ℓ) < ⊤ :=
    (Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox ℓ).measure_lt_top
  -- A bounded measurable function supported in `Λ(ℓ)` is integrable.
  refine MeasureTheory.IntegrableOn.integrable_of_forall_notMem_eq_zero
    (s := Work.BoseK15.corpusBox.boxL ℓ) ?_ ?_
  · refine MeasureTheory.IntegrableOn.of_bound hfin ?_ _ (Filter.Eventually.of_forall hG_b)
    exact hG_m.aestronglyMeasurable
  · intro x hx
    by_contra h
    refine hx (hsuppEta ?_)
    exact Function.mem_support.mpr fun h0 => h (by rw [h0, map_zero, zero_mul])

end Work.BoseBoxFock
