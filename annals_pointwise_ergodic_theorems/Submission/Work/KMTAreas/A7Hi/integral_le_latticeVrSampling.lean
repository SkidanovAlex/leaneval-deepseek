import Mathlib
import Submission.Work.Analysis.Fourier.lattice_sup_lp_sampling
import Submission.Work.KMTAreas.A7.toLp_tsum_pi
import Submission.Work.KMTAreas.A7.variationalNorm_mul_le

namespace Work.KMTAreas.A7Hi

open MeasureTheory
open scoped FourierTransform ENNReal NNReal BigOperators
open PointwiseErgodicTheorems

noncomputable section

set_option maxHeartbeats 1600000

/-! ## Summability of the sampled weight

The two lemmas below record that the lattice values of a Schwartz function (and of a Schwartz
weight times a Schwartz function) form a summable family.  They are the only analytic input
needed beyond `Comparisons.Analysis.Fourier.sampling_reproducing`. -/

/-- The lattice values of a Schwartz function have summable norms:
`∑'_m ‖ψ (x - m)‖ < ∞`. -/
theorem summable_int_norm_schwartz_sub (ψ : SchwartzMap ℝ ℂ) (x : ℝ) :
    Summable (fun m : ℤ => ‖ψ (x - (m : ℝ))‖) := by
  obtain ⟨B, hBpos, hBdecay⟩ := Commons.Analysis.Fourier.schwartzMap_real_decay ψ 2
  refine Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_)
    ((Commons.Analysis.Fourier.summable_int_one_div_abs_shift_half_sq ⌊x⌋).mul_left B)
  have hdec : ‖ψ (x - (m : ℝ))‖ ≤ B * (1 + |x - (m : ℝ)|) ^ (-(2 : ℝ)) := by
    have h := hBdecay (x - (m : ℝ))
    simpa using h
  have hpt := Commons.Analysis.Fourier.lattice_decay_pointwise x m
  calc ‖ψ (x - (m : ℝ))‖ ≤ B * (1 + |x - (m : ℝ)|) ^ (-(2 : ℝ)) := hdec
    _ ≤ B * (1 / |(m : ℝ) - (⌊x⌋ : ℝ) - 1 / 2| ^ (2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hpt hBpos.le

/-- The lattice values of a Schwartz weight times a Schwartz function are summable:
`∑'_m ‖ψ (x - m)‖ ‖φ m‖ < ∞`. -/
theorem summable_int_schwartz_mul_schwartz (ψ φ : SchwartzMap ℝ ℂ) (x : ℝ) :
    Summable (fun m : ℤ => ψ (x - (m : ℝ)) * φ (m : ℝ)) := by
  refine Summable.of_norm_bounded
    ((summable_int_norm_schwartz_sub ψ x).mul_right (SchwartzMap.seminorm ℂ 0 0 φ))
    (fun m => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (SchwartzMap.norm_le_seminorm ℂ φ (m : ℝ))
    (norm_nonneg (ψ (x - (m : ℝ))))

/-! ## Young's inequality for the variational norm -/

/-- Summability is transported by `WithLp.toLp` on a finite coordinate set. -/
private theorem summable_toLp_pi_iff {ι : Type*} (r : NNReal) (J : ℕ)
    (v : ι → Fin J → ℂ) :
    Summable (fun j => WithLp.toLp r (v j)) ↔ Summable v := by
  constructor
  · intro hv
    have h := hv.map ((PiLp.continuousLinearEquiv (r : ℝ≥0∞) ℂ (fun _ : Fin J => ℂ)).toContinuousLinearMap)
      (by fun_prop)
    exact h.congr (fun j => rfl)
  · intro hv
    have h := hv.map ((PiLp.continuousLinearEquiv (r : ℝ≥0∞) ℂ (fun _ : Fin J => ℂ)).symm.toContinuousLinearMap)
      (by fun_prop)
    exact h.congr (fun j => rfl)

/-- A single scaled term of the variational `ℓ^r`-sum, bounded by the variation of its profile. -/
private theorem enorm_toLp_smul_sub_le {r : NNReal} (hr : 1 ≤ r)
    [Fact (1 ≤ (r : ℝ≥0∞))] {J : ℕ} (a : ℕ → ℂ) (N : ℕ → ℕ) (hN : Monotone N) (c : ℂ) :
    ‖WithLp.toLp r (fun i : Fin J => c * (a (N (i + 1)) - a (N i)))‖ₑ
      ≤ ‖c‖ₑ * Submission.PointwiseErgodicTheorems.varPart r a := by
  rw [← ofReal_norm]
  refine (Work.KMTAreas.A7.ofReal_norm_toLp_mul_le r hr (fun _ : Fin J => c)
    (fun i : Fin J => a (N (i + 1)) - a (N i))).trans ?_
  refine mul_le_mul' (iSup_le fun i => le_rfl) ?_
  exact le_iSup_of_le J (le_iSup_of_le N (le_iSup_of_le hN le_rfl))

/-- **Young's inequality for the variational norm.**  If `w : ι → ℕ → ℂ` is a family of scalar
sequences and `k : ι → ℂ` a family of coefficients such that every sequence `n ↦ k j * w j n` is
summable, then

`‖n ↦ ∑'_j k j * w j n‖_{𝕍^r} ≤ ∑'_j ‖k j‖ · ‖w j‖_{𝕍^r}  (r ≥ 1)`.

This is the variational form of the fact that a vector-valued sum is dominated by the sum of the
norms; the `ℓ^r`-triangle inequality enters through `Work.KMTAreas.A7.ofReal_norm_toLp_mul_le`
together with `enorm_tsum_le_tsum_enorm`. -/
theorem variationalNorm_tsum_mul_le {ι : Type*} (r : NNReal) (hr : 1 ≤ r)
    (k : ι → ℂ) (w : ι → ℕ → ℂ) (hsum : ∀ n, Summable (fun j => k j * w j n)) :
    PointwiseErgodicTheorems.variationalNorm r (fun n => ∑' j, k j * w j n)
      ≤ ∑' j, ‖k j‖ₑ * PointwiseErgodicTheorems.variationalNorm r (w j) := by
  letI : Fact (1 ≤ (r : ℝ≥0∞)) := ⟨by exact_mod_cast hr⟩
  by_cases htop : (∑' j, ‖k j‖ₑ * PointwiseErgodicTheorems.variationalNorm r (w j)) = ⊤
  · rw [htop]
    exact le_top
  · have hfin : (∑' j, ‖k j‖ₑ * PointwiseErgodicTheorems.variationalNorm r (w j)) < ⊤ :=
      lt_top_iff_ne_top.mpr htop
    have hsup : (⨆ n, ‖∑' j, k j * w j n‖ₑ) ≤ ∑' j, ‖k j‖ₑ * (⨆ n, ‖w j n‖ₑ) := by
      refine iSup_le fun n => ?_
      refine (enorm_tsum_le_tsum_enorm).trans ?_
      refine ENNReal.tsum_le_tsum fun j => ?_
      rw [enorm_mul]
      exact mul_le_mul' le_rfl (le_iSup (fun n => ‖w j n‖ₑ) n)
    have hvar : Submission.PointwiseErgodicTheorems.varPart r (fun n => ∑' j, k j * w j n)
        ≤ ∑' j, ‖k j‖ₑ * Submission.PointwiseErgodicTheorems.varPart r (w j) := by
      refine iSup_le fun J => iSup_le fun N => iSup_le fun hN => ?_
      set v : ι → Fin J → ℂ := fun j i => k j * w j (N (i + 1)) - k j * w j (N i) with hv
      have hpoint : ∀ i : Fin J,
          (∑' j, k j * w j (N (i + 1))) - (∑' j, k j * w j (N i)) = ∑' j, v j i := by
        intro i
        refine (Summable.tsum_sub (hsum (N (i + 1))) (hsum (N i))).symm.trans
          (tsum_congr fun j => ?_)
        simp only [hv]
      have hbdd : ∀ j, ‖WithLp.toLp r (v j)‖ₑ
          ≤ ‖k j‖ₑ * Submission.PointwiseErgodicTheorems.varPart r (w j) := by
        intro j
        have hvj : v j = fun i : Fin J => k j * (w j (N (i + 1)) - w j (N i)) := by
          funext i
          simp only [hv]
          ring
        rw [hvj]
        exact enorm_toLp_smul_sub_le hr (w j) N hN (k j)
      have hsu : (∑' j, ‖WithLp.toLp r (v j)‖ₑ) < ⊤ := by
        refine lt_of_le_of_lt (ENNReal.tsum_le_tsum hbdd) ?_
        refine lt_of_le_of_lt (ENNReal.tsum_le_tsum fun j => ?_) hfin
        calc ‖k j‖ₑ * Submission.PointwiseErgodicTheorems.varPart r (w j)
            ≤ ‖k j‖ₑ * ((⨆ n, ‖w j n‖ₑ) + Submission.PointwiseErgodicTheorems.varPart r (w j)) :=
              mul_le_mul' le_rfl le_add_self
          _ = ‖k j‖ₑ * PointwiseErgodicTheorems.variationalNorm r (w j) := by
              rw [Submission.PointwiseErgodicTheorems.variationalNorm_eq_add]
      have hvS : Summable v :=
        (summable_toLp_pi_iff r J v).mp
          (Summable.of_norm (tsum_enorm_ne_top_iff_summable_norm.mp (ne_of_lt hsu)))
      have hF : (fun i : Fin J => (∑' j, k j * w j (N (i + 1))) - (∑' j, k j * w j (N i)))
          = ∑' j, v j := by
        funext i
        rw [Pi.tsum_apply hvS]
        exact hpoint i
      calc ENNReal.ofReal ‖WithLp.toLp r
            (fun i : Fin J => (∑' j, k j * w j (N (i + 1))) - (∑' j, k j * w j (N i)))‖
          = ‖∑' j, WithLp.toLp r (v j)‖ₑ := by
              rw [hF, Work.KMTAreas.A7.toLp_tsum_pi r J v hvS, ofReal_norm]
        _ ≤ ∑' j, ‖WithLp.toLp r (v j)‖ₑ := enorm_tsum_le_tsum_enorm
        _ ≤ ∑' j, ‖k j‖ₑ * Submission.PointwiseErgodicTheorems.varPart r (w j) :=
            ENNReal.tsum_le_tsum hbdd
    have hR : (∑' j, ‖k j‖ₑ * PointwiseErgodicTheorems.variationalNorm r (w j))
        = (∑' j, ‖k j‖ₑ * (⨆ n, ‖w j n‖ₑ))
          + (∑' j, ‖k j‖ₑ * Submission.PointwiseErgodicTheorems.varPart r (w j)) := by
      rw [← ENNReal.tsum_add]
      exact tsum_congr fun j => by
        simp only [Submission.PointwiseErgodicTheorems.variationalNorm_eq_add, mul_add]
    rw [hR, Submission.PointwiseErgodicTheorems.variationalNorm_eq_add]
    exact add_le_add hsup hvar

/-! ## The lattice-sampling comparison for the `r`-variational norm -/

end

end Work.KMTAreas.A7Hi
