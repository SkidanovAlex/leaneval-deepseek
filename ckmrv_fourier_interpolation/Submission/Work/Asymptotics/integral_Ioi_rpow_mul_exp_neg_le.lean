import Mathlib
import Submission.Work.Asymptotics.TailIntegral

open MeasureTheory Filter Topology

namespace Work.Asymptotics

/-- **The tail piece of a two-regime estimate.**  On `(B,∞)` with `B ≥ 1` and `λ ≥ 0` one has
`e^{-π(λ+1)t} ≤ e^{-πλ}e^{-πt}` for `t ≥ 1`, so the integral of `t^{M+m}e^{-π(λ+1)t}` over `(B,∞)`
is at most `e^{-πλ}` times the decay constant
`Work.Asymptotics.tailDecay M m = ∫_{t ≥ 1} t^{M+m} e^{-πt} dt`
defined in `Submission.Work.Asymptotics.TailIntegral`. -/
theorem integral_Ioi_rpow_mul_exp_neg_le (M : ℝ) (hM : 0 ≤ M) {B : ℝ} (hB : 1 ≤ B)
    {lam : ℝ} (hlam : 0 ≤ lam) (m : ℕ) :
    ∫ t in Set.Ioi B, t ^ (M + m) * Real.exp (-(Real.pi * (lam + 1) * t))
      ≤ Real.exp (-(Real.pi * lam)) * Work.Asymptotics.tailDecay M m := by
  have hsub : Set.Ioi B ⊆ Set.Ici (1 : ℝ) := fun t ht => le_trans hB (le_of_lt ht)
  have hg_int_Ici : IntegrableOn (fun t : ℝ => t ^ (M + m) * Real.exp (-(Real.pi * t)))
      (Set.Ici (1 : ℝ)) :=
    integrableOn_rpow_mul_exp_neg (M + m) Real.pi (by positivity) Real.pi_pos
  have hg_int : IntegrableOn (fun t : ℝ => t ^ (M + m) * Real.exp (-(Real.pi * t)))
      (Set.Ioi B) := hg_int_Ici.mono_set hsub
  have hf_int : IntegrableOn
      (fun t : ℝ => t ^ (M + m) * Real.exp (-(Real.pi * (lam + 1) * t))) (Set.Ioi B) :=
    (integrableOn_rpow_mul_exp_neg (M + m) (Real.pi * (lam + 1)) (by positivity)
      (by positivity)).mono_set hsub
  have hconst_int : IntegrableOn
      (fun t : ℝ => Real.exp (-(Real.pi * lam)) * (t ^ (M + m) * Real.exp (-(Real.pi * t))))
      (Set.Ioi B) := hg_int.const_mul _
  have hpt : ∀ᵐ t ∂(volume.restrict (Set.Ioi B)),
      t ^ (M + m) * Real.exp (-(Real.pi * (lam + 1) * t))
        ≤ Real.exp (-(Real.pi * lam)) * (t ^ (M + m) * Real.exp (-(Real.pi * t))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht1 : (1 : ℝ) ≤ t := le_trans hB (le_of_lt ht)
    have ht0 : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht1
    have hpow : 0 ≤ t ^ (M + m) := Real.rpow_nonneg ht0.le _
    have hexp_eq : Real.exp (-(Real.pi * (lam + 1) * t))
        = Real.exp (-(Real.pi * lam * t)) * Real.exp (-(Real.pi * t)) := by
      rw [← Real.exp_add]; congr 1; ring
    have hexp_le : Real.exp (-(Real.pi * lam * t)) ≤ Real.exp (-(Real.pi * lam)) := by
      apply Real.exp_le_exp.mpr
      have : Real.pi * lam ≤ Real.pi * lam * t := by
        have := mul_le_mul_of_nonneg_left ht1 (mul_nonneg Real.pi_pos.le hlam)
        linarith
      linarith
    calc t ^ (M + m) * Real.exp (-(Real.pi * (lam + 1) * t))
        = t ^ (M + m) * (Real.exp (-(Real.pi * lam * t)) * Real.exp (-(Real.pi * t))) := by
          rw [hexp_eq]
      _ ≤ t ^ (M + m) * (Real.exp (-(Real.pi * lam)) * Real.exp (-(Real.pi * t))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hexp_le (Real.exp_pos _).le) hpow
      _ = Real.exp (-(Real.pi * lam)) * (t ^ (M + m) * Real.exp (-(Real.pi * t))) := by ring
  have hmain := integral_mono_ae hf_int hconst_int hpt
  rw [MeasureTheory.integral_const_mul] at hmain
  have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Ici (1 : ℝ))]
      (fun t : ℝ => t ^ (M + m) * Real.exp (-(Real.pi * t))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
    exact mul_nonneg (Real.rpow_nonneg (le_trans zero_le_one (Set.mem_Ici.mp ht)) _)
      (Real.exp_pos _).le
  have hmono : ∫ t in Set.Ioi B, t ^ (M + m) * Real.exp (-(Real.pi * t))
      ≤ ∫ t in Set.Ici (1 : ℝ), t ^ (M + m) * Real.exp (-(Real.pi * t)) :=
    setIntegral_mono_set hg_int_Ici hnonneg (Filter.Eventually.of_forall hsub)
  calc ∫ t in Set.Ioi B, t ^ (M + m) * Real.exp (-(Real.pi * (lam + 1) * t))
      ≤ Real.exp (-(Real.pi * lam))
          * ∫ t in Set.Ioi B, t ^ (M + m) * Real.exp (-(Real.pi * t)) := hmain
    _ ≤ Real.exp (-(Real.pi * lam))
          * ∫ t in Set.Ici (1 : ℝ), t ^ (M + m) * Real.exp (-(Real.pi * t)) :=
        mul_le_mul_of_nonneg_left hmono (Real.exp_pos _).le
    _ = Real.exp (-(Real.pi * lam)) * Work.Asymptotics.tailDecay M m := by
        rw [Work.Asymptotics.tailDecay]

end Work.Asymptotics
