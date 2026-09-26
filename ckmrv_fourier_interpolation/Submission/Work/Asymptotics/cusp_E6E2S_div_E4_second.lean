import Mathlib
import Submission.Work.Asymptotics.funnelTailBasic
import Submission.Work.Asymptotics.KPlusXiDefs
import Submission.Work.Residues.E4FunSecondOrder
import Submission.Work.Residues.E6FunSecondOrder
import Submission.Work.Kernels.TildeFacts.KPlus_z_tildeA
import Submission.Work.Asymptotics.MFix.KXiDefs
import Submission.Work.FunnelNumerics.E4_funnel_bounds
import Submission.Work.Asymptotics.E4Fun_upper_half

/-!
# The second-order cusp expansion of `E₆ E₂ˢ / E₄`

On the imaginary axis `z = it` with `t ≥ 3` one has the second-order expansion

  `E₆(z) E₂ˢ(z) / E₄(z) = (1 - 6i/(πz)) - q(744 (1 - 6i/(πz)) + 24) + O(‖q‖²)`,

where `q = qParamFun z = e^{2πiz}`.  This is the input used by the cusp (funnel) expansions of
the CKMRV kernels, cf. `Submission/Work/Asymptotics/KPlus_tail24.lean`.

The ingredients are the second-order expansions of `E₄`, `E₆` (`E4FunSecondOrder`,
`E6FunSecondOrder`), the second-order expansion of `E₂` (`Work.Asymptotics.MFix.E2Fun_two_term`),
the identity `E₂ˢ(z) = E₂(z) - 6i/(πz)` (`Work.Kernels.TildeFacts.E2S_eq`), the lower bound
`‖E₄(z)‖ ≥ 1/2` for `Im z ≥ 3` (`Work.FunnelNumerics.E4_funnel_bounds`), and the elementary
bounds `‖q‖ ≤ 1/512`, `‖1 - 6i/(πz)‖ ≤ 2`.

The algebraic core is the identity

  `(1 - 504q)(s - 24q) - (1 + 240q)(s - (744s + 24)q) = (178560 s + 17856) q²`

(with `s = 1 - 6i/(πz)` and `q` the leading terms of `E₆` and `E₂ˢ`), which is where the
coefficients `744` and `24` of the statement come from.
-/

namespace Work.Asymptotics

open UpperHalfPlane

/-- The constant in the second-order cusp bound of `E₆ E₂ˢ / E₄`: the sum of the five remainder
estimates `178560·2 + 17856` (leading term), `14 C₆` and `253 C₂` (first-order errors),
`C₆C₂/2` (product of the two first-order errors) and `758 C₄` (error of `E₄`), doubled because of
the factor `‖E₄‖⁻¹ ≤ 2`. -/
private noncomputable def Kconst (C2 C4 C6 : ℝ) : ℝ :=
  2 * (178560 * 2 + 17856 + C6 * 14 + C2 * 253 + C6 * C2 / 2 + C4 * 758)

/-- The analytic core of the cusp expansion: if `E₆`, `E₂ˢ`, `E₄` are within `O(‖q‖²)` of
`1 - 504q`, `s - 24q`, `1 + 240q` respectively, if `‖q‖ ≤ 1/2`, `‖s‖ ≤ 2` and `‖E₄‖ ≥ 1/2`,
then `E₆ E₂ˢ/E₄ - s + q(744 s + 24) = O(‖q‖²)` with an explicit constant. -/
private lemma cusp_ratio_bound (E6 E2S E4 q s : ℂ) (C2 C4 C6 : ℝ)
    (hC2 : 0 < C2) (hC4 : 0 < C4) (hC6 : 0 < C6)
    (hq : ‖q‖ ≤ 1 / 2) (hs : ‖s‖ ≤ 2)
    (hE2 : ‖E2S - (s - 24 * q)‖ ≤ C2 * ‖q‖ ^ 2)
    (hE4 : ‖E4 - (1 + 240 * q)‖ ≤ C4 * ‖q‖ ^ 2)
    (hE6 : ‖E6 - (1 - 504 * q)‖ ≤ C6 * ‖q‖ ^ 2)
    (hE4low : (1 / 2 : ℝ) ≤ ‖E4‖) :
    ‖E6 * E2S / E4 - s + q * (744 * s + 24)‖ ≤ Kconst C2 C4 C6 * ‖q‖ ^ 2 := by
  set d2 : ℂ := E2S - (s - 24 * q) with hd2
  set d4 : ℂ := E4 - (1 + 240 * q) with hd4
  set d6 : ℂ := E6 - (1 - 504 * q) with hd6
  have hd2b : ‖d2‖ ≤ C2 * ‖q‖ ^ 2 := hE2
  have hd4b : ‖d4‖ ≤ C4 * ‖q‖ ^ 2 := hE4
  have hd6b : ‖d6‖ ≤ C6 * ‖q‖ ^ 2 := hE6
  have hE4ne : E4 ≠ 0 := by
    intro h
    rw [h, norm_zero] at hE4low
    norm_num at hE4low
  have hE6eq : E6 = (1 - 504 * q) + d6 := by rw [hd6]; ring
  have hE2eq : E2S = (s - 24 * q) + d2 := by rw [hd2]; ring
  have hE4eq : E4 = (1 + 240 * q) + d4 := by rw [hd4]; ring
  have hY : E6 * E2S - E4 * (s - q * (744 * s + 24)) =
      (178560 * s + 17856) * q ^ 2 + d6 * (s - 24 * q) + (1 - 504 * q) * d2 + d6 * d2
        - d4 * (s - q * (744 * s + 24)) := by
    rw [hE6eq, hE2eq, hE4eq]; ring
  have t1 : ‖(178560 * s + 17856) * q ^ 2‖ ≤ (178560 * 2 + 17856) * ‖q‖ ^ 2 := by
    have h1 : ‖(178560 : ℂ) * s + (17856 : ℂ)‖ ≤ 178560 * 2 + 17856 := by
      have ha := norm_add_le ((178560 : ℂ) * s) (17856 : ℂ)
      rw [norm_mul] at ha
      have h2 : ‖(178560 : ℂ)‖ = 178560 := by norm_num
      have h3 : ‖(17856 : ℂ)‖ = 17856 := by norm_num
      rw [h2, h3] at ha
      nlinarith [ha, hs]
    rw [norm_mul, norm_pow]
    exact mul_le_mul h1 le_rfl (sq_nonneg _) (by positivity)
  have t2 : ‖d6 * (s - 24 * q)‖ ≤ C6 * 14 * ‖q‖ ^ 2 := by
    have hs2 : ‖s - 24 * q‖ ≤ 14 := by
      have ha := norm_sub_le s ((24 : ℂ) * q)
      rw [norm_mul] at ha
      have h4 : ‖(24 : ℂ)‖ = 24 := by norm_num
      rw [h4] at ha
      nlinarith [ha, hs, hq, norm_nonneg q]
    rw [norm_mul]
    calc ‖d6‖ * ‖s - 24 * q‖ ≤ (C6 * ‖q‖ ^ 2) * 14 :=
          mul_le_mul hd6b hs2 (norm_nonneg _) (by positivity)
      _ = C6 * 14 * ‖q‖ ^ 2 := by ring
  have t3 : ‖(1 - 504 * q) * d2‖ ≤ C2 * 253 * ‖q‖ ^ 2 := by
    have h1 : ‖(1 : ℂ) - 504 * q‖ ≤ 253 := by
      have ha := norm_sub_le (1 : ℂ) ((504 : ℂ) * q)
      rw [norm_one, norm_mul] at ha
      have h4 : ‖(504 : ℂ)‖ = 504 := by norm_num
      rw [h4] at ha
      nlinarith [ha, hq, norm_nonneg q]
    rw [norm_mul]
    calc ‖(1 : ℂ) - 504 * q‖ * ‖d2‖ ≤ 253 * (C2 * ‖q‖ ^ 2) :=
          mul_le_mul h1 hd2b (norm_nonneg _) (by norm_num)
      _ = C2 * 253 * ‖q‖ ^ 2 := by ring
  have t4 : ‖d6 * d2‖ ≤ C6 * C2 / 2 * ‖q‖ ^ 2 := by
    rw [norm_mul]
    calc ‖d6‖ * ‖d2‖ ≤ (C6 * ‖q‖ ^ 2) * (C2 * ‖q‖ ^ 2) :=
          mul_le_mul hd6b hd2b (norm_nonneg _) (by positivity)
      _ = C6 * C2 * ‖q‖ ^ 4 := by ring
      _ ≤ C6 * C2 * ((1 / 2) * ‖q‖ ^ 2) := by
          have h1 : ‖q‖ ^ 2 ≤ 1 / 4 := by nlinarith [hq, norm_nonneg q]
          have h4 : ‖q‖ ^ 4 ≤ (1 / 2) * ‖q‖ ^ 2 := by nlinarith [h1, sq_nonneg (‖q‖ ^ 2)]
          exact mul_le_mul_of_nonneg_left h4 (by positivity)
      _ = C6 * C2 / 2 * ‖q‖ ^ 2 := by ring
  have t5 : ‖d4 * (s - q * (744 * s + 24))‖ ≤ C4 * 758 * ‖q‖ ^ 2 := by
    have hinner : ‖s - q * (744 * s + 24)‖ ≤ 758 := by
      have hA : ‖q * (744 * s + 24)‖ ≤ (1 / 2) * (744 * 2 + 24) := by
        rw [norm_mul]
        have hB : ‖(744 : ℂ) * s + 24‖ ≤ 744 * 2 + 24 := by
          have ha := norm_add_le ((744 : ℂ) * s) (24 : ℂ)
          rw [norm_mul] at ha
          have h2 : ‖(744 : ℂ)‖ = 744 := by norm_num
          have h3 : ‖(24 : ℂ)‖ = 24 := by norm_num
          rw [h2, h3] at ha
          nlinarith [ha, hs]
        exact mul_le_mul hq hB (norm_nonneg _) (by norm_num)
      have ha := norm_sub_le s (q * (744 * s + 24))
      nlinarith [ha, hA, hs]
    rw [norm_mul]
    calc ‖d4‖ * ‖s - q * (744 * s + 24)‖ ≤ (C4 * ‖q‖ ^ 2) * 758 :=
          mul_le_mul hd4b hinner (norm_nonneg _) (by positivity)
      _ = C4 * 758 * ‖q‖ ^ 2 := by ring
  have htri : ‖(178560 * s + 17856) * q ^ 2 + d6 * (s - 24 * q) + (1 - 504 * q) * d2 + d6 * d2
        - d4 * (s - q * (744 * s + 24))‖
      ≤ ‖(178560 * s + 17856) * q ^ 2‖ + ‖d6 * (s - 24 * q)‖ + ‖(1 - 504 * q) * d2‖
        + ‖d6 * d2‖ + ‖d4 * (s - q * (744 * s + 24))‖ := by
    have h1 := norm_sub_le ((178560 * s + 17856) * q ^ 2 + d6 * (s - 24 * q)
      + (1 - 504 * q) * d2 + d6 * d2) (d4 * (s - q * (744 * s + 24)))
    have h2 := norm_add_le ((178560 * s + 17856) * q ^ 2 + d6 * (s - 24 * q)
      + (1 - 504 * q) * d2) (d6 * d2)
    have h3 := norm_add_le ((178560 * s + 17856) * q ^ 2 + d6 * (s - 24 * q)) ((1 - 504 * q) * d2)
    have h4 := norm_add_le ((178560 * s + 17856) * q ^ 2) (d6 * (s - 24 * q))
    linarith
  have hYb : ‖E6 * E2S - E4 * (s - q * (744 * s + 24))‖
      ≤ (178560 * 2 + 17856 + C6 * 14 + C2 * 253 + C6 * C2 / 2 + C4 * 758) * ‖q‖ ^ 2 := by
    rw [hY]
    refine le_trans htri ?_
    have hmid : ‖(178560 * s + 17856) * q ^ 2‖ + ‖d6 * (s - 24 * q)‖ + ‖(1 - 504 * q) * d2‖
        + ‖d6 * d2‖ + ‖d4 * (s - q * (744 * s + 24))‖
        ≤ (178560 * 2 + 17856) * ‖q‖ ^ 2 + C6 * 14 * ‖q‖ ^ 2 + C2 * 253 * ‖q‖ ^ 2
          + C6 * C2 / 2 * ‖q‖ ^ 2 + C4 * 758 * ‖q‖ ^ 2 := by
      linarith [t1, t2, t3, t4, t5]
    refine le_trans hmid (le_of_eq ?_)
    ring
  have hX : E6 * E2S / E4 - s + q * (744 * s + 24)
      = (E6 * E2S - E4 * (s - q * (744 * s + 24))) / E4 := by
    rw [eq_div_iff hE4ne, add_mul, sub_mul, div_mul_cancel₀ _ hE4ne]
    ring
  calc ‖E6 * E2S / E4 - s + q * (744 * s + 24)‖
      = ‖(E6 * E2S - E4 * (s - q * (744 * s + 24))) / E4‖ := by rw [hX]
    _ = ‖E6 * E2S - E4 * (s - q * (744 * s + 24))‖ / ‖E4‖ := norm_div _ _
    _ ≤ ‖E6 * E2S - E4 * (s - q * (744 * s + 24))‖ / (1 / 2) :=
        div_le_div_of_nonneg_left (norm_nonneg _) (by norm_num) hE4low
    _ = 2 * ‖E6 * E2S - E4 * (s - q * (744 * s + 24))‖ := by ring
    _ ≤ 2 * ((178560 * 2 + 17856 + C6 * 14 + C2 * 253 + C6 * C2 / 2 + C4 * 758) * ‖q‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hYb (by norm_num)
    _ = Kconst C2 C4 C6 * ‖q‖ ^ 2 := by unfold Kconst; ring

/-- `‖1 - 6i/(πz)‖ ≤ 2` for `3 ≤ Im z`. -/
private lemma norm_one_sub_six_I_div_le (z : UpperHalfPlane) (hz : 3 ≤ z.im) :
    ‖(1 : ℂ) - 6 * Complex.I / ((Real.pi : ℂ) * (z : ℂ))‖ ≤ 2 := by
  have hz3 : (3 : ℝ) ≤ ‖(z : ℂ)‖ := by
    have h1 : |(z : ℂ).im| ≤ ‖(z : ℂ)‖ := Complex.abs_im_le_norm _
    rw [UpperHalfPlane.coe_im, abs_of_nonneg (le_of_lt z.im_pos)] at h1
    linarith
  have h6 : ‖6 * Complex.I / ((Real.pi : ℂ) * (z : ℂ))‖ ≤ 1 := by
    rw [norm_div, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat,
      show ‖((Real.pi : ℝ) : ℂ)‖ = |Real.pi| from RCLike.norm_ofReal Real.pi,
      abs_of_pos Real.pi_pos]
    rw [div_le_one (by positivity)]
    nlinarith [Real.pi_gt_three, hz3]
  calc ‖(1 : ℂ) - 6 * Complex.I / ((Real.pi : ℂ) * (z : ℂ))‖
      ≤ ‖(1 : ℂ)‖ + ‖6 * Complex.I / ((Real.pi : ℂ) * (z : ℂ))‖ := norm_sub_le _ _
    _ ≤ 1 + 1 := by rw [norm_one]; linarith
    _ = 2 := by norm_num

theorem cusp_E6E2S_div_E4_second :
    ∃ C : ℝ, 0 < C ∧ ∀ (z : UpperHalfPlane) (t : ℝ), 3 ≤ t →
      (z : ℂ) = (t : ℂ) * Complex.I →
      ‖Work.Kernels.E6Fun z * Work.Kernels.E2S z / Work.Kernels.E4Fun z
          - (1 - 6 * Complex.I / ((Real.pi : ℂ) * (z : ℂ)))
          + Work.Kernels.qParamFun z
              * (744 * (1 - 6 * Complex.I / ((Real.pi : ℂ) * (z : ℂ))) + 24)‖
        ≤ C * ‖Work.Kernels.qParamFun z‖ ^ 2 := by
  obtain ⟨C2, hC2, hE2⟩ := MFix.E2Fun_two_term
  obtain ⟨C4, hC4, hE4⟩ := Work.Residues.E4FunSecondOrder
  obtain ⟨C6, hC6, hE6⟩ := Work.Residues.E6FunSecondOrder
  refine ⟨Kconst C2 C4 C6, ?_, ?_⟩
  · unfold Kconst
    positivity
  · intro z t ht hz
    have hzim : z.im = t := by
      have h := congrArg Complex.im hz
      rw [UpperHalfPlane.coe_im] at h
      simpa using h
    have hz3 : 3 ≤ z.im := by rw [hzim]; exact ht
    have hz1 : 1 ≤ z.im := le_trans (by norm_num) hz3
    set q : ℂ := Work.Kernels.qParamFun z with hq
    set s : ℂ := 1 - 6 * Complex.I / ((Real.pi : ℂ) * (z : ℂ)) with hs
    have hqb : ‖q‖ ≤ 1 / 2 := by
      rw [hq]
      have h1 : ‖Work.Kernels.qParamFun z‖ ≤ 1 / 512 :=
        Work.Asymptotics.norm_qParamFun_le_inv512 hz1
      linarith
    have hsb : ‖s‖ ≤ 2 := by
      rw [hs]
      exact norm_one_sub_six_I_div_le z hz3
    have hd2 : ‖Work.Kernels.E2S z - (s - 24 * q)‖ ≤ C2 * ‖q‖ ^ 2 := by
      have h2eq : Work.Kernels.E2S z - (s - 24 * q)
          = Work.Kernels.E2Fun z - 1 + 24 * Work.Kernels.qParamFun z := by
        rw [Work.Kernels.TildeFacts.E2S_eq, hs, hq]; ring
      rw [h2eq, hq]
      exact hE2 z hz1
    have hd4 : ‖Work.Kernels.E4Fun z - (1 + 240 * q)‖ ≤ C4 * ‖q‖ ^ 2 := by
      have h4eq : Work.Kernels.E4Fun z - (1 + 240 * q)
          = Work.Kernels.E4Fun z - 1 - 240 * Work.Kernels.qParamFun z := by
        rw [hq]; ring
      rw [h4eq, hq]
      exact hE4 z hz1
    have hd6 : ‖Work.Kernels.E6Fun z - (1 - 504 * q)‖ ≤ C6 * ‖q‖ ^ 2 := by
      have h6eq : Work.Kernels.E6Fun z - (1 - 504 * q)
          = Work.Kernels.E6Fun z - 1 + 504 * Work.Kernels.qParamFun z := by
        rw [hq]; ring
      rw [h6eq, hq]
      exact hE6 z hz1
    have hE4low : (1 / 2 : ℝ) ≤ ‖Work.Kernels.E4Fun z‖ :=
      Work.FunnelNumerics.E4_funnel_bounds.2 z hz3
    have key := cusp_ratio_bound (Work.Kernels.E6Fun z) (Work.Kernels.E2S z)
      (Work.Kernels.E4Fun z) q s C2 C4 C6 hC2 hC4 hC6 hqb hsb hd2 hd4 hd6 hE4low
    rw [hq, hs] at key
    exact key

end Work.Asymptotics
