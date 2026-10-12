import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.PotCubicLowBandAux.slotBesselDefs
import Submission.Work.MB.SlotWeakBase
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.PotCubicLowBandAux

open MeasureTheory

theorem slotJ_slice_excited {m n : ℕ} [NeZero m] {ℓ : ℝ} {e : Fin m → Work.BoseDict.Sp → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (j : Fin n) {Θ : Work.BoseDict.Xn n → ℂ} (hΘm : Measurable Θ)
    (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C)
    (ŷ : {i : Fin n // i ≠ j} → Work.BoseDict.Sp) :
    ∫ a : Work.BoseDict.Sp, (star (Θ (Work.BoseBoxFock.PotCubicLowBandAux.sliceRestore j a ŷ))
        * (Work.BoseBoxFock.PotCubicLowBandAux.slotJ e (Work.BoseBoxFock.boxT0 m) j Θ
            (Work.BoseBoxFock.PotCubicLowBandAux.sliceRestore j a ŷ))).re
      = ∑ l ∈ (Finset.univ.erase (0 : Fin m)),
          ‖∫ z : Work.BoseDict.Sp, star (e l z)
              * Θ (Work.BoseBoxFock.PotCubicLowBandAux.sliceRestore j z ŷ)‖ ^ 2 := by
  classical
  choose Cb hCb using hbdd
  obtain ⟨CΘ, hCΘ⟩ := hΘb
  -- the slice map `a ↦ σ_j(a,ŷ)` is measurable
  have hslice : Measurable (fun a : Work.BoseDict.Sp => sliceRestore j a ŷ) := by
    rw [measurable_pi_iff]
    intro i
    by_cases h : i = j
    · have hh : (fun a : Work.BoseDict.Sp => sliceRestore j a ŷ i) = fun a => a := by
        funext a; simp only [sliceRestore, dif_pos h]
      rw [hh]; exact measurable_id
    · have hh : (fun a : Work.BoseDict.Sp => sliceRestore j a ŷ i) = fun _ => ŷ ⟨i, h⟩ := by
        funext a; simp only [sliceRestore, dif_neg h]
      rw [hh]; exact measurable_const
  -- the one-particle integrals `U l = ∫ z, conj(e_l z) Θ(σ_j(z,ŷ))`
  set U : Fin m → ℂ := fun l => ∫ z : Work.BoseDict.Sp, star (e l z) * Θ (sliceRestore j z ŷ)
    with hU
  have hUapp : ∀ l : Fin m, U l
      = ∫ z : Work.BoseDict.Sp, star (e l z) * Θ (sliceRestore j z ŷ) := fun l => by rw [hU]
  -- integrability of the slice integrands
  have hInt_e : ∀ l : Fin m,
      Integrable (fun a : Work.BoseDict.Sp => star (Θ (sliceRestore j a ŷ)) * e l a) := by
    intro l
    exact Work.MB.integrable_of_bdd_of_support (S := Work.BoseK15.corpusBox.boxL ℓ)
      (hS := Work.BoseB4.BoxData.boxL_measurableSet Work.BoseK15.corpusBox ℓ)
      (hSfin := (Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox ℓ).measure_lt_top.ne)
      (hfm := ((Complex.continuous_conj.measurable.comp (hΘm.comp hslice)).mul
        (hmeas l)).aestronglyMeasurable)
      (C := max CΘ 0 * max (Cb l) 0)
      (hC := by
        intro a
        rw [norm_mul, norm_star]
        exact mul_le_mul (le_trans (hCΘ _) (le_max_left _ _))
          (le_trans (hCb l a) (le_max_left _ _)) (norm_nonneg _) (le_max_right _ _))
      (hsupp := by
        intro a ha
        have hz : e l a = 0 := by
          by_contra hne
          exact ha (hsupp l (Function.mem_support.mpr hne))
        rw [hz, mul_zero])
  -- the pointwise slot value
  have hslot : ∀ a : Work.BoseDict.Sp, star (Θ (sliceRestore j a ŷ))
        * slotJ e (Work.BoseBoxFock.boxT0 m) j Θ (sliceRestore j a ŷ)
      = ∑ l ∈ Finset.univ.erase (0 : Fin m),
          (star (Θ (sliceRestore j a ŷ)) * e l a) * U l := by
    intro a
    have h1 : slotJ e (Work.BoseBoxFock.boxT0 m) j Θ (sliceRestore j a ŷ)
        = ∑ l ∈ Finset.univ.erase (0 : Fin m), e l a * U l := by
      rw [slotJ_boxT0]
      refine Finset.sum_congr rfl fun l _ => ?_
      simp only [sliceRestore_apply_self, update_sliceRestore]
      rw [hUapp l]
    rw [h1, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by rw [mul_assoc]
  -- integrability of the whole complex integrand
  have hFsum : Integrable (fun a : Work.BoseDict.Sp => ∑ l ∈ Finset.univ.erase (0 : Fin m),
      (star (Θ (sliceRestore j a ŷ)) * e l a) * U l) := by
    have hgen : ∀ t : Finset (Fin m), Integrable (fun a : Work.BoseDict.Sp =>
        ∑ l ∈ t, (star (Θ (sliceRestore j a ŷ)) * e l a) * U l) := by
      intro t
      refine Finset.induction_on t ?_ ?_
      · simp only [Finset.sum_empty]
        exact integrable_zero Work.BoseDict.Sp ℂ volume
      · intro x t hx ih
        have hstep : (fun a : Work.BoseDict.Sp => ∑ l ∈ insert x t,
              (star (Θ (sliceRestore j a ŷ)) * e l a) * U l)
            = fun a => (star (Θ (sliceRestore j a ŷ)) * e x a) * U x
                + ∑ l ∈ t, (star (Θ (sliceRestore j a ŷ)) * e l a) * U l := by
          funext a
          rw [Finset.sum_insert hx]
        rw [hstep]
        exact ((hInt_e x).mul_const (U x)).add ih
    exact hgen _
  have hF : Integrable (fun a : Work.BoseDict.Sp => star (Θ (sliceRestore j a ŷ))
      * slotJ e (Work.BoseBoxFock.boxT0 m) j Θ (sliceRestore j a ŷ)) :=
    hFsum.congr (by filter_upwards with a; exact (hslot a).symm)
  -- the conjugate identification `∫ a, conj(Θ) e_l = conj U_l`
  have hstarU : ∀ l : Fin m,
      (∫ a : Work.BoseDict.Sp, star (Θ (sliceRestore j a ŷ)) * e l a) = star (U l) := by
    intro l
    have hg : (∫ a : Work.BoseDict.Sp, star (star (e l a) * Θ (sliceRestore j a ŷ)))
        = star (∫ a : Work.BoseDict.Sp, star (e l a) * Θ (sliceRestore j a ŷ)) := by
      simp only [Complex.star_def]
      rw [integral_conj]
    calc (∫ a : Work.BoseDict.Sp, star (Θ (sliceRestore j a ŷ)) * e l a)
        = ∫ a : Work.BoseDict.Sp, star (star (e l a) * Θ (sliceRestore j a ŷ)) := by
          refine integral_congr_ae ?_
          filter_upwards with a
          rw [star_mul, star_star]
      _ = star (∫ a : Work.BoseDict.Sp, star (e l a) * Θ (sliceRestore j a ŷ)) := hg
      _ = star (U l) := by rw [hUapp l]
  -- the main identity
  have hmain : (∫ a : Work.BoseDict.Sp, (star (Θ (sliceRestore j a ŷ))
        * slotJ e (Work.BoseBoxFock.boxT0 m) j Θ (sliceRestore j a ŷ)).re)
      = ∑ l ∈ Finset.univ.erase (0 : Fin m), ‖U l‖ ^ 2 := by
    have h1 : (∫ a : Work.BoseDict.Sp, (star (Θ (sliceRestore j a ŷ))
          * slotJ e (Work.BoseBoxFock.boxT0 m) j Θ (sliceRestore j a ŷ)).re)
        = (∫ a : Work.BoseDict.Sp, star (Θ (sliceRestore j a ŷ))
            * slotJ e (Work.BoseBoxFock.boxT0 m) j Θ (sliceRestore j a ŷ)).re :=
      ContinuousLinearMap.integral_comp_comm Complex.reCLM hF
    rw [h1]
    have h2 : (∫ a : Work.BoseDict.Sp, star (Θ (sliceRestore j a ŷ))
          * slotJ e (Work.BoseBoxFock.boxT0 m) j Θ (sliceRestore j a ŷ))
        = ∑ l ∈ Finset.univ.erase (0 : Fin m), star (U l) * U l := by
      rw [show (∫ a : Work.BoseDict.Sp, star (Θ (sliceRestore j a ŷ))
            * slotJ e (Work.BoseBoxFock.boxT0 m) j Θ (sliceRestore j a ŷ))
          = ∫ a : Work.BoseDict.Sp, ∑ l ∈ Finset.univ.erase (0 : Fin m),
              (star (Θ (sliceRestore j a ŷ)) * e l a) * U l from by
            refine integral_congr_ae ?_
            filter_upwards with a
            exact hslot a]
      rw [integral_finsetSum (s := Finset.univ.erase (0 : Fin m))
        (f := fun l a => (star (Θ (sliceRestore j a ŷ)) * e l a) * U l)
        (fun l _ => (hInt_e l).mul_const (U l))]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [integral_mul_const, hstarU l]
    rw [h2, Complex.re_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re,
      Complex.normSq_eq_norm_sq]
  rw [hmain]

end Work.BoseBoxFock.PotCubicLowBandAux
