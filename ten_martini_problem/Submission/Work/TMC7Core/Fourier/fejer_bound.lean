import Mathlib
import Submission.Work.TMC7Core.Fourier.ldt_setup

/-!
# The Fejér kernel bound

`fejerKer R θ ≤ 2 / (1 + (R · fracDist θ)²)`: the quantitative decay of the Fejér kernel away
from the integers.  This elementary estimate underlies the moving average in the
Bourgain–Jitomirskaya large deviation theorem.
-/

open MeasureTheory Filter Topology Set
open LeanEval.Analysis.TenMartini

noncomputable section

namespace Work.TMC7Core.Fourier

/-- `‖1 - e^{2πix}‖ = 2 |sin (πx)|`. -/
private theorem norm_one_sub_exp (x : ℝ) :
    ‖(1 : ℂ) - Complex.exp (2 * Real.pi * Complex.I * x)‖ = 2 * |Real.sin (Real.pi * x)| := by
  have hz : Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))
      = Complex.exp (Complex.I * ((2 * Real.pi * x : ℝ) : ℂ)) := by
    congr 1; push_cast; ring
  rw [hz, norm_sub_rev, Complex.norm_exp_I_mul_ofReal_sub_one]
  rw [show (2 * Real.pi * x) / 2 = Real.pi * x by ring, Real.norm_eq_abs, abs_mul]
  norm_num

/-- `2 · fracDist θ ≤ |sin (πθ)|`: the distance to the nearest integer controls the sine. -/
private theorem two_mul_fracDist_le_abs_sin (θ : ℝ) :
    2 * fracDist θ ≤ |Real.sin (Real.pi * θ)| := by
  set n : ℤ := round θ with hn
  have hfrac : fracDist θ = |θ - (n : ℝ)| := by rw [hn]; rfl
  have ht : |θ - (n : ℝ)| ≤ 1 / 2 := by
    have := abs_sub_round θ
    rwa [← hn] at this
  have hsin_eq : |Real.sin (Real.pi * θ)| = |Real.sin (Real.pi * (θ - (n : ℝ)))| := by
    have h := Real.sin_sub_int_mul_pi (Real.pi * θ) n
    have harg : Real.pi * θ - (n : ℝ) * Real.pi = Real.pi * (θ - (n : ℝ)) := by ring
    rw [harg] at h
    rw [h, abs_mul]; simp
  rw [hfrac, hsin_eq]
  have habs : |Real.pi * (θ - (n : ℝ))| = Real.pi * |θ - (n : ℝ)| := by
    rw [abs_mul, abs_of_nonneg Real.pi_pos.le]
  have h1 : |Real.sin (Real.pi * (θ - (n : ℝ)))| = Real.sin (Real.pi * |θ - (n : ℝ)|) := by
    rw [← habs]
    exact Real.abs_sin_eq_sin_abs_of_abs_le_pi (by rw [habs]; nlinarith [Real.pi_pos, ht])
  rw [h1]
  have hb : 0 ≤ Real.pi * |θ - (n : ℝ)| := by positivity
  have hb2 : Real.pi * |θ - (n : ℝ)| ≤ Real.pi / 2 := by
    have := mul_le_mul_of_nonneg_left ht Real.pi_pos.le
    linarith
  have h2 := Real.mul_le_sin hb hb2
  rw [show (2 / Real.pi) * (Real.pi * |θ - (n : ℝ)|) = 2 * |θ - (n : ℝ)| by
        field_simp] at h2
  exact h2

theorem fejer_bound (R : ℕ) (hR : 1 ≤ R) (θ : ℝ) :
    fejerKer R θ ≤ 2 / (1 + ((R : ℝ) * fracDist θ) ^ 2) := by
  have hRpos : (0 : ℝ) < (R : ℝ) := by exact_mod_cast hR
  have h1 := fejerKer_le_one R θ
  rcases eq_or_lt_of_le (abs_nonneg (θ - (round θ : ℝ))) with ht | ht
  · -- `θ` an integer
    have h0 : fracDist θ = 0 := ht.symm
    have hzero : ((R : ℝ) * fracDist θ) ^ 2 = 0 := by rw [h0]; ring
    rw [hzero, add_zero, div_one]
    linarith
  · -- `θ` not an integer: `fracDist θ > 0`
    have htpos : 0 < fracDist θ := ht
    have htle : fracDist θ ≤ 1 / 2 := abs_sub_round θ
    set z : ℂ := Complex.exp (2 * Real.pi * Complex.I * θ) with hz
    have h5 : 0 < ‖1 - z‖ := by
      have hne : z ≠ 1 := by
        intro h
        have h2 : ‖(1 : ℂ) - z‖ = 0 := by rw [h]; simp
        rw [hz, norm_one_sub_exp] at h2
        have hsin0 : Real.sin (Real.pi * θ) = 0 := by
          have := mul_eq_zero.mp h2
          rcases this with h3 | h3
          · linarith
          · exact abs_eq_zero.mp h3
        rcases Real.sin_eq_zero_iff.mp hsin0 with ⟨m, hm⟩
        have hθm : θ = (m : ℝ) := by nlinarith [Real.pi_pos]
        have hfrac0 : fracDist θ = 0 := by
          rw [hθm, fracDist, round_intCast]; simp
        rw [hfrac0] at htpos; exact lt_irrefl _ htpos
      rw [norm_pos_iff]; exact sub_ne_zero.mpr (Ne.symm hne)
    have hsum_eq : (∑ j ∈ Finset.range R, Complex.exp (2 * Real.pi * Complex.I * (j : ℝ) * θ))
        = ∑ j ∈ Finset.range R, z ^ j := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [hz, ← Complex.exp_nat_mul]
      congr 1
      push_cast; ring
    have hzn : ‖z‖ = 1 := by
      rw [hz]
      have heq : Complex.exp (2 * Real.pi * Complex.I * θ)
          = Complex.exp (Complex.I * ((2 * Real.pi * θ : ℝ) : ℂ)) := by
        congr 1; push_cast; ring
      rw [heq, Complex.norm_exp_I_mul_ofReal]
    have hgeom : (∑ j ∈ Finset.range R, z ^ j) * (z - 1) = z ^ R - 1 := geom_sum_mul z R
    have hbound : ‖∑ j ∈ Finset.range R, z ^ j‖ ≤ 2 / ‖1 - z‖ := by
      have h2 : ‖∑ j ∈ Finset.range R, z ^ j‖ * ‖z - 1‖ = ‖z ^ R - 1‖ := by
        rw [← norm_mul, hgeom]
      have h3 : ‖z ^ R - 1‖ ≤ 2 := by
        calc ‖z ^ R - 1‖ ≤ ‖z ^ R‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
          _ = 1 + 1 := by rw [norm_pow, hzn, one_pow, norm_one]
          _ = 2 := by norm_num
      have h4 : ‖z - 1‖ = ‖1 - z‖ := norm_sub_rev _ _
      have hgoal : ‖∑ j ∈ Finset.range R, z ^ j‖ * ‖1 - z‖ ≤ 2 := by
        rw [← h4, h2]; exact h3
      exact (le_div_iff₀ h5).mpr hgoal
    have hsin : 4 * fracDist θ ≤ ‖1 - z‖ := by
      rw [hz, norm_one_sub_exp]
      linarith [two_mul_fracDist_le_abs_sin θ]
    have hkey : fejerKer R θ ≤ 1 / (4 * ((R : ℝ) * fracDist θ) ^ 2) := by
      rw [fejerKer_def', hsum_eq, norm_div]
      have hnormR : ‖(R : ℂ)‖ = (R : ℝ) := by simp
      rw [hnormR]
      have h2 : ‖∑ j ∈ Finset.range R, z ^ j‖ ≤ 1 / (2 * fracDist θ) := by
        have h6 : 2 / ‖1 - z‖ ≤ 1 / (2 * fracDist θ) := by
          rw [div_le_div_iff₀ h5 (by positivity)]
          linarith [hsin]
        exact hbound.trans h6
      have h3 : (‖∑ j ∈ Finset.range R, z ^ j‖ / (R : ℝ)) ^ 2
          ≤ (1 / (2 * R * fracDist θ)) ^ 2 := by
        apply pow_le_pow_left₀ (div_nonneg (norm_nonneg _) hRpos.le)
        rw [div_le_iff₀ hRpos]
        calc ‖∑ j ∈ Finset.range R, z ^ j‖ ≤ 1 / (2 * fracDist θ) := h2
          _ = 1 / (2 * R * fracDist θ) * (R : ℝ) := by field_simp
      calc (‖∑ j ∈ Finset.range R, z ^ j‖ / (R : ℝ)) ^ 2
          ≤ (1 / (2 * R * fracDist θ)) ^ 2 := h3
        _ = 1 / (4 * ((R : ℝ) * fracDist θ) ^ 2) := by field_simp; ring
    set u : ℝ := (R : ℝ) * fracDist θ with hu
    have hu0 : 0 < u := by rw [hu]; exact mul_pos hRpos htpos
    rcases le_or_gt u (1 / 2) with hu' | hu'
    · have hge : 1 ≤ 2 / (1 + u ^ 2) := by
        rw [le_div_iff₀ (by positivity)]
        nlinarith [hu0, hu']
      linarith
    · have h7 : 1 / (4 * u ^ 2) ≤ 2 / (1 + u ^ 2) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [hu', sq_nonneg u]
      linarith

end Work.TMC7Core.Fourier
