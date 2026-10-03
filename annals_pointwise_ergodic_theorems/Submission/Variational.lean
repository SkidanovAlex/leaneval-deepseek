import ChallengeDeps
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Submission.Commons.Analysis.Variation.cauchySeq_of_forall_monotone_variation_le

/-!
# Basic properties of the variational norm

The variational norm of a sequence `a : ℕ → ℂ` is defined in `ChallengeDeps` as

`‖a‖_𝕍ʳ = sup_n ‖a n‖ + sup_{J, N monotone} ‖(a (N (i+1)) - a (N i))_{i < J}‖_{ℓ^r}`.

In this file we record the elementary facts used in the reductions of the main theorem:
the `sup` norm is dominated by the variational norm, the variational norm dominates the `ℓ^r`
norm of any increment vector, and a sequence with finite variational norm (`r ≥ 1`) converges.
-/

namespace Submission

open _root_.PointwiseErgodicTheorems
set_option autoImplicit false

namespace PointwiseErgodicTheorems

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal PNat

/-- The sup norm of the sequence is bounded by its variational norm. -/
lemma le_variationalNorm (r : ℝ≥0) (a : ℕ → ℂ) (n : ℕ) : ‖a n‖ₑ ≤ variationalNorm r a := by
  unfold variationalNorm
  exact le_trans (le_iSup (fun n => ‖a n‖ₑ) n) le_self_add

/-- The variational norm dominates the `ℓ^r` norm of the increments along any monotone
selection of indices. -/
lemma ofReal_norm_toLp_le_variationalNorm (r : ℝ≥0) (a : ℕ → ℂ) (J : ℕ) {N : ℕ → ℕ}
    (hN : Monotone N) :
    ENNReal.ofReal ‖(WithLp.toLp (r : ℝ≥0∞)
      (fun i : Fin J => a (N ((i : ℕ) + 1)) - a (N (i : ℕ))))‖ ≤ variationalNorm r a := by
  unfold variationalNorm
  refine le_trans ?_ le_add_self
  refine le_iSup_of_le J ?_
  refine le_iSup_of_le N ?_
  refine le_iSup_of_le hN ?_
  exact le_rfl

/-- A sequence in `ℂ` whose `r`-variational norm is finite, with `r ≥ 1`, converges. -/
theorem tendsto_of_variationalNorm_lt_top (r : ℝ≥0) (hr : 1 ≤ r) {a : ℕ → ℂ}
    (h : variationalNorm r a < ⊤) : ∃ L : ℂ, Tendsto a atTop (𝓝 L) := by
  have hrR : 1 ≤ (r : ℝ) := by exact_mod_cast hr
  have hrpos : 0 < (r : ℝ) := lt_of_lt_of_le zero_lt_one hrR
  have hrpos' : 0 < (r : ℝ≥0∞).toReal := by rw [ENNReal.coe_toReal]; exact hrpos
  have hC : 0 ≤ ((variationalNorm r a).toReal) ^ (r : ℝ) :=
    Real.rpow_nonneg ENNReal.toReal_nonneg _
  have key : ∀ (J : ℕ) (N : ℕ → ℕ), Monotone N →
      (∑ i : Fin J, ‖a (N ((i : ℕ) + 1)) - a (N (i : ℕ))‖ ^ (r : ℝ))
        ≤ ((variationalNorm r a).toReal) ^ (r : ℝ) := by
    intro J N hN
    have hb := ofReal_norm_toLp_le_variationalNorm r a J hN
    rw [ENNReal.ofReal_le_iff_le_toReal (ne_of_lt h)] at hb
    rw [PiLp.norm_eq_sum (p := (r : ℝ≥0∞)) hrpos'] at hb
    have hb' : (∑ i : Fin J, ‖a (N ((i : ℕ) + 1)) - a (N (i : ℕ))‖ ^ (r : ℝ)) ^ (1 / (r : ℝ))
        ≤ (variationalNorm r a).toReal := by
      simpa [WithLp.ofLp_toLp, ENNReal.coe_toReal] using hb
    have hnn : 0 ≤ ∑ i : Fin J, ‖a (N ((i : ℕ) + 1)) - a (N (i : ℕ))‖ ^ (r : ℝ) :=
      Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (norm_nonneg _) _)
    have h2 := Real.rpow_le_rpow (Real.rpow_nonneg hnn _) hb' hrpos.le
    rw [one_div, Real.rpow_inv_rpow hnn (ne_of_gt hrpos)] at h2
    exact h2
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete
    (Commons.Analysis.Variation.cauchySeq_of_forall_monotone_variation_le hrR hC key)
  exact ⟨L, hL⟩

/-- The variational norm is a supremum over a *countable* family: monotone index selections may
be replaced by their restrictions to `Fin (J + 1)`. -/
lemma variationalNorm_eq_iSup_fin (r : ℝ≥0) (a : ℕ → ℂ) :
    variationalNorm r a = (⨆ n, ‖a n‖ₑ) +
      ⨆ (J : ℕ) (w : Fin (J + 1) → ℕ) (_ : Monotone w),
        ENNReal.ofReal ‖(WithLp.toLp (r : ℝ≥0∞)
          (fun i : Fin J => a (w i.succ) - a (w i.castSucc)))‖ := by
  unfold variationalNorm
  congr 1
  apply le_antisymm
  · refine iSup_le (fun K => iSup_le (fun N => iSup_le (fun hN => ?_)))
    refine le_iSup_of_le K ?_
    refine le_iSup_of_le (fun j : Fin (K + 1) => N (j : ℕ)) ?_
    refine le_iSup_of_le (fun _ _ h => hN h) ?_
    exact le_rfl
  · refine iSup_le (fun K => iSup_le (fun w => iSup_le (fun hw => ?_)))
    let N : ℕ → ℕ := fun k => w ⟨min k K, Nat.lt_succ_of_le (Nat.min_le_right k K)⟩
    have hNmono : Monotone N := by
      intro x y hxy
      refine hw ?_
      simp only [Fin.le_def]
      omega
    refine le_iSup_of_le K ?_
    refine le_iSup_of_le N ?_
    refine le_iSup_of_le hNmono ?_
    have h1 : ∀ i : Fin K, N ((i : ℕ)) = w i.castSucc := by
      intro i
      simp only [N]
      congr 1
      exact Fin.ext (Nat.min_eq_left i.isLt.le)
    have h2 : ∀ i : Fin K, N ((i : ℕ) + 1) = w i.succ := by
      intro i
      simp only [N]
      congr 1
      exact Fin.ext (Nat.min_eq_left (Nat.succ_le_of_lt i.isLt))
    have hv : (fun i : Fin K => a (w i.succ) - a (w i.castSucc))
        = (fun i : Fin K => a (N ((i : ℕ) + 1)) - a (N (i : ℕ))) := by
      funext i
      rw [h1 i, h2 i]
    rw [hv]

section Measurability

variable {𝓧 : Type*} [MeasurableSpace 𝓧] {μ : Measure 𝓧}

/-- The variational norm of a pointwise measurable sequence is measurable: it is a supremum over
the countable family of finite index selections. -/
lemma measurable_variationalNorm {r : ℝ≥0} (hr : 0 < r) {u : ℕ → 𝓧 → ℂ}
    (hu : ∀ n, Measurable (u n)) :
    Measurable (fun x => variationalNorm r (fun n => u n x)) := by
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
  have hfun : (fun x => variationalNorm r (fun n => u n x))
      = fun x => (⨆ n, ‖u n x‖ₑ) +
          ⨆ (J : ℕ) (w : Fin (J + 1) → ℕ) (_ : Monotone w),
            ENNReal.ofReal ‖(WithLp.toLp (r : ℝ≥0∞)
              (fun i : Fin J => u (w i.succ) x - u (w i.castSucc) x))‖ := by
    funext x
    exact variationalNorm_eq_iSup_fin r (fun n => u n x)
  rw [hfun]
  refine Measurable.add (Measurable.iSup (fun n => (hu n).enorm)) ?_
  refine Measurable.iSup (fun J => Measurable.iSup (fun w => Measurable.iSup (fun _ => ?_)))
  have hterm : (fun x => ENNReal.ofReal ‖(WithLp.toLp (r : ℝ≥0∞)
      (fun i : Fin J => u (w i.succ) x - u (w i.castSucc) x))‖)
      = fun x => ENNReal.ofReal ((∑ i : Fin J,
          ‖u (w i.succ) x - u (w i.castSucc) x‖ ^ (r : ℝ)) ^ (1 / (r : ℝ))) := by
    funext x
    congr 1
    rw [PiLp.norm_eq_sum (p := (r : ℝ≥0∞)) (by rw [ENNReal.coe_toReal]; exact hrR)]
    simp [ENNReal.coe_toReal]
  rw [hterm]
  refine ENNReal.continuous_ofReal.measurable.comp ?_
  refine (Real.continuous_rpow_const (by positivity)).measurable.comp ?_
  refine Finset.measurable_sum _ (fun i _ => ?_)
  exact (Real.continuous_rpow_const hrR.le).measurable.comp (((hu _).sub (hu _)).norm)

/-- If the variational norm of a measurable sequence is in `Lᵖ` (`0 < p < ∞`), then it is finite
almost everywhere. -/
lemma ae_lt_top_of_eLpNorm_variationalNorm_lt_top {r : ℝ≥0} (hr : 0 < r) {u : ℕ → 𝓧 → ℂ}
    (hu : ∀ n, Measurable (u n)) {p : ℝ≥0∞} (hp : p ≠ 0) (hp' : p ≠ ⊤)
    (h : eLpNorm (fun x => variationalNorm r (fun n => u n x)) p μ < ⊤) :
    ∀ᵐ x ∂μ, variationalNorm r (fun n => u n x) < ⊤ := by
  have hmeas := measurable_variationalNorm hr hu
  have hlin : ∫⁻ x, ‖variationalNorm r (fun n => u n x)‖ₑ ^ p.toReal ∂μ < ⊤ :=
    lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp hp' h
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp hp'
  have hae : ∀ᵐ x ∂μ, ‖variationalNorm r (fun n => u n x)‖ₑ ^ p.toReal < ⊤ :=
    ae_lt_top (hmeas.enorm.pow_const _) (ne_of_lt hlin)
  filter_upwards [hae] with x hx
  by_contra hcontra
  rw [not_lt] at hcontra
  have htop : variationalNorm r (fun n => u n x) = ⊤ := top_le_iff.mp hcontra
  rw [show ‖variationalNorm r (fun n => u n x)‖ₑ = variationalNorm r (fun n => u n x) from rfl,
    htop] at hx
  rw [ENNReal.top_rpow_of_pos hq] at hx
  exact lt_irrefl _ hx

/-- If the variational norm of a measurable sequence has finite `Lᵖ` seminorm (`1 ≤ r`, `0 < p < ∞`),
then the sequence converges almost everywhere. -/
lemma ae_tendsto_of_eLpNorm_variationalNorm_lt_top {r : ℝ≥0} (hr : 1 ≤ r) {u : ℕ → 𝓧 → ℂ}
    (hu : ∀ n, Measurable (u n)) {p : ℝ≥0∞} (hp : p ≠ 0) (hp' : p ≠ ⊤)
    (h : eLpNorm (fun x => variationalNorm r (fun n => u n x)) p μ < ⊤) :
    ∀ᵐ x ∂μ, ∃ L : ℂ, Tendsto (fun n => u n x) atTop (𝓝 L) := by
  filter_upwards [ae_lt_top_of_eLpNorm_variationalNorm_lt_top
    (lt_of_lt_of_le zero_lt_one hr) hu hp hp' h] with x hx
  exact tendsto_of_variationalNorm_lt_top r hr hx

end Measurability

end PointwiseErgodicTheorems
end Submission
