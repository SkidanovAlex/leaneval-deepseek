import Mathlib
import Submission.Work.A14.defs
import Submission.Work.C7.g_form
import Submission.Work.C7.evA_Lps
import Submission.Work.CPull.evp_aux
import Submission.Work.CPull.evp_add_mul
import Submission.Work.CPull.hasSum_coeff_B3_yps
import Submission.Work.CPull.evp_sympPhi

namespace Work.A14D

open Complex Metric
open scoped BigOperators


/-!
## The analytic value of `B₄` along `y = x²/(x−1)` on the whole unit disc

The formal pullback identity `Work.C7.g_form` reads

`B₄ ∘ y = (x − φ)·(2·Li₂ + ½·L²)`,  `y = x²/(x−1)`, `φ = x/(x−1)`, `L = log(1−x)`.

Both factors have a radius of convergence `≥ 1` (the coefficients of `X − φ` are bounded,
those of `Li₂` are `1/n²`, and `L²` has coefficients of polynomial growth), so on the whole
open unit disc the evaluation `Work.CPull.evp` is multiplicative (`Work.CPull.evpMul`) and the
coefficient series of the product converges to the product of the two evaluations:

`evp (B₄∘y) z = (z − z/(z−1))·(2·evp Li₂ z + ½·log(1−z)²)`.

The first factor is evaluated with `Work.CPull.evp_sympPhi`; the second with
`Work.CPull.evp_C_mul`, `Work.CPull.evpMul` and the Taylor series of `log(1−x)`
(`Work.C7.evA_Lps`).

This is the `B₄`-analogue of `Work.A14D.pullback_B5_hasSum`; unlike the `B₂`/`B₃` versions of
`Work.PureP`/`Work.CPull` it does **not** go through `evp_subst`, hence needs no `‖z‖ < 1/2`
restriction.
-/

/-- `‖(q : ℂ)‖ = |(q : ℝ)|` for a rational `q`. -/
private lemma norm_ratCast_c (q : ℚ) : ‖(q : ℂ)‖ = |(q : ℝ)| := by simp

/-- `∑ ‖z‖ⁿ` converges on the open unit disc. -/
private lemma summable_geom_z {z : ℂ} (hz : ‖z‖ < 1) : Summable fun n : ℕ => ‖z‖ ^ n :=
  summable_geometric_of_norm_lt_one (by simpa using hz)

/-- A series whose coefficients are bounded by `C` is absolutely summable on the open unit disc. -/
private lemma summable_coeff_of_bound {f : PowerSeries ℚ} {C : ℝ}
    (hb : ∀ n, ‖((PowerSeries.coeff n f : ℚ) : ℂ)‖ ≤ C) {z : ℂ} (hz : ‖z‖ < 1) :
    Summable fun n : ℕ => ‖((PowerSeries.coeff n f : ℚ) : ℂ) * z ^ n‖ := by
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    ((summable_geom_z hz).mul_left C)
  rw [norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_right (hb n) (pow_nonneg (norm_nonneg z) n)

/-- The coefficients of `x − φ = x(x−2)/(x−1)` are bounded by `2`. -/
private lemma norm_coeff_sympW_le (n : ℕ) :
    ‖((PowerSeries.coeff n ((PowerSeries.X : PowerSeries ℚ) - Submission.CDT.sympPhi) : ℚ) : ℂ)‖ ≤ 2 := by
  have h : ((PowerSeries.coeff n ((PowerSeries.X : PowerSeries ℚ) - Submission.CDT.sympPhi) : ℚ) : ℂ)
      = (((PowerSeries.coeff n (PowerSeries.X : PowerSeries ℚ) : ℚ) : ℂ))
        - (((PowerSeries.coeff n Submission.CDT.sympPhi : ℚ) : ℂ)) := by
    rw [map_sub]; push_cast; ring
  rw [h, PowerSeries.coeff_X, Work.CPull.coeff_sympPhi_eq n]
  split_ifs <;> norm_num

/-- The coefficients of `x` are bounded by `1`. -/
private lemma norm_coeff_X_le (n : ℕ) :
    ‖((PowerSeries.coeff n (PowerSeries.X : PowerSeries ℚ) : ℚ) : ℂ)‖ ≤ 1 := by
  rw [PowerSeries.coeff_X]; split_ifs <;> norm_num

/-- The coefficients of `φ = x/(x−1)` are bounded by `1`. -/
private lemma norm_coeff_sympPhi_le (n : ℕ) :
    ‖((PowerSeries.coeff n Submission.CDT.sympPhi : ℚ) : ℂ)‖ ≤ 1 := by
  rw [Work.CPull.coeff_sympPhi_eq n]; split_ifs <;> norm_num

/-- The coefficients of `Li₂(x) = Σ xⁿ/n²` are bounded by `1`. -/
private lemma norm_coeff_Li2ps_le (n : ℕ) :
    ‖((PowerSeries.coeff n Work.C7.Li2ps : ℚ) : ℂ)‖ ≤ 1 := by
  rw [Work.C7.coeff_Li2ps]
  split_ifs with h
  · simp
  · rw [norm_ratCast]
    have hn : (1 : ℚ) ≤ (n : ℚ) := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr h)
    rw [abs_of_nonneg (by positivity), ← Rat.cast_one, Rat.cast_le]
    exact inv_le_one_of_one_le₀ (by nlinarith)

/-- Evaluation is compatible with subtraction (a local copy of the standard fact, to keep the
imports of this file light). -/
private lemma evp_sub' (f g : PowerSeries ℚ) (z : ℂ)
    (hf : Summable fun n : ℕ => ((PowerSeries.coeff n f : ℚ) : ℂ) * z ^ n)
    (hg : Summable fun n : ℕ => ((PowerSeries.coeff n g : ℚ) : ℂ) * z ^ n) :
    Work.CPull.evp (f - g) z = Work.CPull.evp f z - Work.CPull.evp g z := by
  rw [Work.CPull.evp, Work.CPull.evp, Work.CPull.evp]
  have h : (fun n : ℕ => ((PowerSeries.coeff n (f - g) : ℚ) : ℂ) * z ^ n)
      = fun n : ℕ => ((PowerSeries.coeff n f : ℚ) : ℂ) * z ^ n
          - ((PowerSeries.coeff n g : ℚ) : ℂ) * z ^ n := by
    funext n; rw [map_sub]; push_cast; ring
  rw [h, Summable.tsum_sub hf hg]

theorem pullback_B4_hasSum (z : ℂ) (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ =>
      ((PowerSeries.coeff n (Submission.CDTPlan.B4.subst Submission.CDT.sympY) : ℚ) : ℂ) * z ^ n)
      ((z - z / (z - 1)) *
        (2 * (∑' n : ℕ, ((PowerSeries.coeff n Work.C7.Li2ps : ℚ) : ℂ) * z ^ n)
          + (1 / 2) * (Complex.log (1 - z)) ^ 2)) := by
  -- the formal pullback identity `B₄ ∘ y = (x − φ)·(2Li₂ + ½L²)`
  have hB4 : Submission.CDTPlan.B4.subst Submission.CDT.sympY
      = ((PowerSeries.X : PowerSeries ℚ) - Submission.CDT.sympPhi)
        * (2 * Work.C7.Li2ps + PowerSeries.C (1 / 2 : ℚ) * (Work.C7.Lps * Work.C7.Lps)) := by
    have h := Work.C7.g_form.2.2
    rw [show Work.C7.g 3 = Submission.CDTPlan.B4.subst Submission.CDT.sympY by
      simp [Work.C7.g, Submission.CDTPlan.pureB]] at h
    rw [h, pow_two]
  rw [hB4]
  set Q : PowerSeries ℚ :=
    2 * Work.C7.Li2ps + PowerSeries.C (1 / 2 : ℚ) * (Work.C7.Lps * Work.C7.Lps) with hQ
  -- summability of the elementary factors
  have hLn : Summable fun n : ℕ => ‖((PowerSeries.coeff n Work.C7.Lps : ℚ) : ℂ) * z ^ n‖ :=
    (Work.C7.hasSum_Lps hz).summable.norm
  have hLLn : Summable fun n : ℕ =>
      ‖((PowerSeries.coeff n (Work.C7.Lps * Work.C7.Lps) : ℚ) : ℂ) * z ^ n‖ :=
    (Work.CPull.evpMul Work.C7.Lps Work.C7.Lps z hLn hLn).1
  have hPn : Summable fun n : ℕ =>
      ‖((PowerSeries.coeff n ((PowerSeries.X : PowerSeries ℚ) - Submission.CDT.sympPhi) : ℚ) : ℂ)
        * z ^ n‖ :=
    summable_coeff_of_bound norm_coeff_sympW_le hz
  have hLi2n : Summable fun n : ℕ => ‖((PowerSeries.coeff n Work.C7.Li2ps : ℚ) : ℂ) * z ^ n‖ :=
    summable_coeff_of_bound norm_coeff_Li2ps_le hz
  -- summability of the second factor `Q`
  have hQn : Summable fun n : ℕ => ‖((PowerSeries.coeff n Q : ℚ) : ℂ) * z ^ n‖ := by
    have h2 : Summable fun n : ℕ =>
        ‖((PowerSeries.coeff n (2 * Work.C7.Li2ps) : ℚ) : ℂ) * z ^ n‖ := by
      refine (hLi2n.mul_left 2).congr (fun n => ?_)
      rw [show (2 * Work.C7.Li2ps : PowerSeries ℚ) = PowerSeries.C 2 * Work.C7.Li2ps from rfl,
        PowerSeries.coeff_C_mul]
      push_cast
      simp only [norm_mul, Complex.norm_ofNat]
      ring
    have h3 : Summable fun n : ℕ =>
        ‖((PowerSeries.coeff n (PowerSeries.C (1 / 2 : ℚ) * (Work.C7.Lps * Work.C7.Lps)) : ℚ) : ℂ)
          * z ^ n‖ := by
      refine (hLLn.mul_left (1 / 2)).congr (fun n => ?_)
      rw [PowerSeries.coeff_C_mul, Rat.cast_mul,
        show ((1 / 2 : ℚ) : ℂ) * ((PowerSeries.coeff n (Work.C7.Lps * Work.C7.Lps) : ℚ) : ℂ) * z ^ n
          = ((1 / 2 : ℚ) : ℂ)
            * (((PowerSeries.coeff n (Work.C7.Lps * Work.C7.Lps) : ℚ) : ℂ) * z ^ n) by ring,
        norm_mul, norm_ratCast]
      norm_num
    have hsplit : (fun n : ℕ => ‖((PowerSeries.coeff n Q : ℚ) : ℂ) * z ^ n‖)
        = fun n : ℕ => ‖((PowerSeries.coeff n (2 * Work.C7.Li2ps) : ℚ) : ℂ) * z ^ n
            + ((PowerSeries.coeff n (PowerSeries.C (1 / 2 : ℚ) * (Work.C7.Lps * Work.C7.Lps)) : ℚ) : ℂ)
              * z ^ n‖ := by
      funext n
      congr 1
      rw [hQ, map_add]
      push_cast
      ring
    rw [hsplit]
    exact Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => norm_add_le _ _) (h2.add h3)
  -- the Cauchy product, and the evaluation of both factors
  obtain ⟨-, -, hsF, hevp⟩ :=
    Work.CPull.evpMul ((PowerSeries.X : PowerSeries ℚ) - Submission.CDT.sympPhi) Q z hPn hQn
  have hPv : Work.CPull.evp ((PowerSeries.X : PowerSeries ℚ) - Submission.CDT.sympPhi) z
      = z - z / (z - 1) := by
    have hX : Summable fun n : ℕ =>
        ((PowerSeries.coeff n (PowerSeries.X : PowerSeries ℚ) : ℚ) : ℂ) * z ^ n :=
      (summable_coeff_of_bound norm_coeff_X_le hz).of_norm
    have hPhi : Summable fun n : ℕ =>
        ((PowerSeries.coeff n Submission.CDT.sympPhi : ℚ) : ℂ) * z ^ n :=
      (summable_coeff_of_bound norm_coeff_sympPhi_le hz).of_norm
    rw [evp_sub' _ _ z hX hPhi, Work.CPull.evp_X, (Work.CPull.evp_sympPhi z hz).1]
  have hQv : Work.CPull.evp Q z
      = 2 * Work.CPull.evp Work.C7.Li2ps z + (1 / 2) * (Complex.log (1 - z)) ^ 2 := by
    have hLi2s : Summable fun n : ℕ => ((PowerSeries.coeff n Work.C7.Li2ps : ℚ) : ℂ) * z ^ n :=
      hLi2n.of_norm
    have hLLs : Summable fun n : ℕ =>
        ((PowerSeries.coeff n (Work.C7.Lps * Work.C7.Lps) : ℚ) : ℂ) * z ^ n := hLLn.of_norm
    have h2Lis : Summable fun n : ℕ =>
        ((PowerSeries.coeff n (2 * Work.C7.Li2ps) : ℚ) : ℂ) * z ^ n := by
      refine (hLi2s.mul_left 2).congr (fun n => ?_)
      rw [show (2 * Work.C7.Li2ps : PowerSeries ℚ) = PowerSeries.C 2 * Work.C7.Li2ps from rfl,
        PowerSeries.coeff_C_mul]
      push_cast; ring
    have hCs : Summable fun n : ℕ =>
        ((PowerSeries.coeff n (PowerSeries.C (1 / 2 : ℚ) * (Work.C7.Lps * Work.C7.Lps)) : ℚ) : ℂ)
          * z ^ n := by
      refine (hLLs.mul_left (((1 / 2 : ℚ) : ℂ))).congr (fun n => ?_)
      rw [PowerSeries.coeff_C_mul]
      push_cast; ring
    have hLval : Work.CPull.evp Work.C7.Lps z = Complex.log (1 - z) := Work.C7.evA_Lps hz
    have hLLval : Work.CPull.evp (Work.C7.Lps * Work.C7.Lps) z = (Complex.log (1 - z)) ^ 2 := by
      rw [(Work.CPull.evpMul Work.C7.Lps Work.C7.Lps z hLn hLn).2.2.2, hLval, pow_two]
    rw [hQ]
    rw [(Work.CPull.evp_add_mul (2 * Work.C7.Li2ps)
        (PowerSeries.C (1 / 2 : ℚ) * (Work.C7.Lps * Work.C7.Lps)) z h2Lis hCs).1]
    rw [show (2 * Work.C7.Li2ps : PowerSeries ℚ) = PowerSeries.C 2 * Work.C7.Li2ps from rfl,
      Work.CPull.evp_C_mul, Work.CPull.evp_C_mul]
    rw [hLLval]
    norm_num
  have hs := hsF.hasSum
  rw [show (∑' n : ℕ,
        ((PowerSeries.coeff n (((PowerSeries.X : PowerSeries ℚ) - Submission.CDT.sympPhi) * Q) : ℚ) : ℂ)
          * z ^ n)
      = Work.CPull.evp (((PowerSeries.X : PowerSeries ℚ) - Submission.CDT.sympPhi) * Q) z from rfl] at hs
  rw [hevp, hPv, hQv] at hs
  exact hs

end Work.A14D

