/-
# `Work.FTS.ClassC.eFam_sin_two_bound`

The angular Dirichlet eigenfunction of `Lzero` is
`eFam m θ = cos θ · gC (2m+1) (sin θ)`, with `gC = C^{(3/2)}` the Gegenbauer polynomial.  We show
that on the closed quadrant `[0, π/2]` it vanishes at the two endpoints at least like
`sin (2θ)`:

  `∃ A ≥ 0, ∀ θ ∈ [0, π/2], |eFam m θ| ≤ A · sin (2θ)`.

**Route.**  `gC (2m+1)` is odd, so `gC (2m+1) 0 = 0` (`gC_odd_zero`); by the mean value theorem
combined with a bound on the derivative on `[0,1]`, this upgrades to
`|gC (2m+1) x| ≤ 6^(2m+1) · x` for `x ∈ [0,1]`.  Multiplying by `cos θ ≥ 0` and using
`sin (2θ) = 2 sin θ cos θ` gives the claim with `A = 6^(2m+1) / 2`.

The bound on the derivatives is obtained from the three-term recurrence by a two-step induction
(`gC_bound_pair`): on `[0,1]` both `|gC n|` and `|deriv (gC n)|` are dominated by `6^n`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_orthogonal
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_Lzero

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassC

open Work.FTS.PhiStar.Gegenbauer

/-- On `[0,1]` both the Gegenbauer polynomial `gC n` and its derivative are bounded by `6 ^ n`.
Proved by two-step induction from the recurrence `(n+2) C_{n+2} = (2n+5) x C_{n+1} - (n+3) C_n`
and its derivative; the numerical estimates are `13n + 33 ≤ 36 (n+2)` for the values and
`25n + 63 ≤ 36 (n+2)` for the derivatives. -/
lemma gC_bound_pair : ∀ n : ℕ,
    (∀ x ∈ Set.Icc (0 : ℝ) 1, |gC n x| ≤ (6 : ℝ) ^ n) ∧
      (∀ x ∈ Set.Icc (0 : ℝ) 1, |deriv (gC n) x| ≤ (6 : ℝ) ^ n) := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero =>
      refine ⟨?_, ?_⟩
      · intro x _
        rw [show gC 0 = (fun _ : ℝ => (1 : ℝ)) from rfl]
        norm_num
      · intro x _
        rw [show gC 0 = (fun _ : ℝ => (1 : ℝ)) from rfl]
        simp
  | one =>
      have hderiv : deriv (fun x : ℝ => 3 * x) = fun _ : ℝ => 3 := by
        funext x
        rw [deriv_const_mul_field]
        simp
      refine ⟨?_, ?_⟩
      · intro x hx
        rw [show gC 1 = (fun x : ℝ => 3 * x) from rfl]
        rw [abs_of_nonneg (by linarith [hx.1] : (0 : ℝ) ≤ 3 * x)]
        nlinarith [hx.2]
      · intro x _
        rw [show gC 1 = (fun x : ℝ => 3 * x) from rfl, hderiv]
        norm_num
  | more n ih ih' =>
      have hcoef : (0 : ℝ) ≤ 2 * (n : ℝ) + 5 := by positivity
      have hcoef3 : (0 : ℝ) ≤ (n : ℝ) + 3 := by positivity
      have hden : (0 : ℝ) < (n : ℝ) + 2 := by positivity
      have hpowpos : (0 : ℝ) < (6 : ℝ) ^ n := by positivity
      have hp1 : (6 : ℝ) ^ (n + 1) = 6 * (6 : ℝ) ^ n := by rw [pow_succ]; ring
      have hp2 : (6 : ℝ) ^ (n + 2) = 36 * (6 : ℝ) ^ n := by
        rw [pow_succ, pow_succ]; ring
      have hncast : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      constructor
      · intro x hx
        rcases hx with ⟨hx0, hx1⟩
        have hb1 : |gC (n + 1) x| ≤ (6 : ℝ) ^ (n + 1) := ih'.1 x ⟨hx0, hx1⟩
        have hb0 : |gC n x| ≤ (6 : ℝ) ^ n := ih.1 x ⟨hx0, hx1⟩
        have heq : gC (n + 2) x
            = ((2 * (n : ℝ) + 5) * x * gC (n + 1) x - ((n : ℝ) + 3) * gC n x)
                / ((n : ℝ) + 2) := by
          rw [eq_div_iff (ne_of_gt hden), mul_comm]
          exact gC_rec n x
        have hnum : |(2 * (n : ℝ) + 5) * x * gC (n + 1) x - ((n : ℝ) + 3) * gC n x|
            ≤ (2 * (n : ℝ) + 5) * (6 : ℝ) ^ (n + 1) + ((n : ℝ) + 3) * (6 : ℝ) ^ n := by
          have ha : |(2 * (n : ℝ) + 5) * x * gC (n + 1) x|
              = (2 * (n : ℝ) + 5) * (x * |gC (n + 1) x|) := by
            simp only [abs_mul, abs_of_nonneg hx0, abs_of_nonneg hcoef]
            ring
          have hb : |((n : ℝ) + 3) * gC n x| = ((n : ℝ) + 3) * |gC n x| := by
            rw [abs_mul, abs_of_nonneg hcoef3]
          have h1 : x * |gC (n + 1) x| ≤ (6 : ℝ) ^ (n + 1) := by
            have h := mul_le_mul hx1 hb1 (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
            simpa using h
          have h2 : (2 * (n : ℝ) + 5) * (x * |gC (n + 1) x|)
              ≤ (2 * (n : ℝ) + 5) * (6 : ℝ) ^ (n + 1) := mul_le_mul_of_nonneg_left h1 hcoef
          have h3 : ((n : ℝ) + 3) * |gC n x| ≤ ((n : ℝ) + 3) * (6 : ℝ) ^ n :=
            mul_le_mul_of_nonneg_left hb0 hcoef3
          calc |(2 * (n : ℝ) + 5) * x * gC (n + 1) x - ((n : ℝ) + 3) * gC n x|
              ≤ |(2 * (n : ℝ) + 5) * x * gC (n + 1) x| + |((n : ℝ) + 3) * gC n x| :=
                abs_sub _ _
            _ = (2 * (n : ℝ) + 5) * (x * |gC (n + 1) x|) + ((n : ℝ) + 3) * |gC n x| := by
                rw [ha, hb]
            _ ≤ (2 * (n : ℝ) + 5) * (6 : ℝ) ^ (n + 1) + ((n : ℝ) + 3) * (6 : ℝ) ^ n := by
                linarith [h2, h3]
        have hfin : (2 * (n : ℝ) + 5) * (6 : ℝ) ^ (n + 1) + ((n : ℝ) + 3) * (6 : ℝ) ^ n
            ≤ (6 : ℝ) ^ (n + 2) * ((n : ℝ) + 2) := by
          rw [hp1, hp2]
          nlinarith [hpowpos, hncast]
        rw [heq, abs_div, abs_of_pos hden]
        have h2 : |(2 * (n : ℝ) + 5) * x * gC (n + 1) x - ((n : ℝ) + 3) * gC n x|
              / ((n : ℝ) + 2)
            ≤ ((2 * (n : ℝ) + 5) * (6 : ℝ) ^ (n + 1) + ((n : ℝ) + 3) * (6 : ℝ) ^ n)
              / ((n : ℝ) + 2) := div_le_div_of_nonneg_right hnum (le_of_lt hden)
        have h3 : ((2 * (n : ℝ) + 5) * (6 : ℝ) ^ (n + 1) + ((n : ℝ) + 3) * (6 : ℝ) ^ n)
              / ((n : ℝ) + 2) ≤ (6 : ℝ) ^ (n + 2) := by
          rw [div_le_iff₀ hden]
          exact hfin
        linarith [h2, h3]
      · intro x hx
        rcases hx with ⟨hx0, hx1⟩
        have hb1 : |gC (n + 1) x| ≤ (6 : ℝ) ^ (n + 1) := ih'.1 x ⟨hx0, hx1⟩
        have hd1 : |deriv (gC (n + 1)) x| ≤ (6 : ℝ) ^ (n + 1) := ih'.2 x ⟨hx0, hx1⟩
        have hd0 : |deriv (gC n) x| ≤ (6 : ℝ) ^ n := ih.2 x ⟨hx0, hx1⟩
        have heq : deriv (gC (n + 2)) x
            = ((2 * (n : ℝ) + 5) * gC (n + 1) x + (2 * (n : ℝ) + 5) * x * deriv (gC (n + 1)) x
                - ((n : ℝ) + 3) * deriv (gC n) x) / ((n : ℝ) + 2) := by
          rw [eq_div_iff (ne_of_gt hden), mul_comm]
          exact gC_rec_deriv n x
        have hta : |(2 * (n : ℝ) + 5) * gC (n + 1) x|
            = (2 * (n : ℝ) + 5) * |gC (n + 1) x| := by
          rw [abs_mul, abs_of_nonneg hcoef]
        have htb : |(2 * (n : ℝ) + 5) * x * deriv (gC (n + 1)) x|
            = (2 * (n : ℝ) + 5) * (x * |deriv (gC (n + 1)) x|) := by
          simp only [abs_mul, abs_of_nonneg hx0, abs_of_nonneg hcoef]
          ring
        have htc : |((n : ℝ) + 3) * deriv (gC n) x| = ((n : ℝ) + 3) * |deriv (gC n) x| := by
          rw [abs_mul, abs_of_nonneg hcoef3]
        have h1 : x * |deriv (gC (n + 1)) x| ≤ (6 : ℝ) ^ (n + 1) := by
          have h := mul_le_mul hx1 hd1 (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
          simpa using h
        have h2 : (2 * (n : ℝ) + 5) * |gC (n + 1) x| ≤ (2 * (n : ℝ) + 5) * (6 : ℝ) ^ (n + 1) :=
          mul_le_mul_of_nonneg_left hb1 hcoef
        have h3 : (2 * (n : ℝ) + 5) * (x * |deriv (gC (n + 1)) x|)
            ≤ (2 * (n : ℝ) + 5) * (6 : ℝ) ^ (n + 1) := mul_le_mul_of_nonneg_left h1 hcoef
        have h4 : ((n : ℝ) + 3) * |deriv (gC n) x| ≤ ((n : ℝ) + 3) * (6 : ℝ) ^ n :=
          mul_le_mul_of_nonneg_left hd0 hcoef3
        have hnum : |(2 * (n : ℝ) + 5) * gC (n + 1) x + (2 * (n : ℝ) + 5) * x * deriv (gC (n + 1)) x
              - ((n : ℝ) + 3) * deriv (gC n) x|
            ≤ (2 * (n : ℝ) + 5) * (6 : ℝ) ^ (n + 1) + (2 * (n : ℝ) + 5) * (6 : ℝ) ^ (n + 1)
              + ((n : ℝ) + 3) * (6 : ℝ) ^ n := by
          calc |(2 * (n : ℝ) + 5) * gC (n + 1) x + (2 * (n : ℝ) + 5) * x * deriv (gC (n + 1)) x
                - ((n : ℝ) + 3) * deriv (gC n) x|
              ≤ |(2 * (n : ℝ) + 5) * gC (n + 1) x + (2 * (n : ℝ) + 5) * x * deriv (gC (n + 1)) x|
                + |((n : ℝ) + 3) * deriv (gC n) x| := abs_sub _ _
            _ ≤ (|(2 * (n : ℝ) + 5) * gC (n + 1) x| + |(2 * (n : ℝ) + 5) * x * deriv (gC (n + 1)) x|)
                + |((n : ℝ) + 3) * deriv (gC n) x| := by
                have hAB := abs_add_le ((2 * (n : ℝ) + 5) * gC (n + 1) x)
                  ((2 * (n : ℝ) + 5) * x * deriv (gC (n + 1)) x)
                linarith [hAB]
            _ = (2 * (n : ℝ) + 5) * |gC (n + 1) x| + (2 * (n : ℝ) + 5) * (x * |deriv (gC (n + 1)) x|)
                + ((n : ℝ) + 3) * |deriv (gC n) x| := by
                rw [hta, htb, htc]
            _ ≤ (2 * (n : ℝ) + 5) * (6 : ℝ) ^ (n + 1) + (2 * (n : ℝ) + 5) * (6 : ℝ) ^ (n + 1)
                + ((n : ℝ) + 3) * (6 : ℝ) ^ n := by
                linarith [h2, h3, h4]
        have hfin : (2 * (n : ℝ) + 5) * (6 : ℝ) ^ (n + 1) + (2 * (n : ℝ) + 5) * (6 : ℝ) ^ (n + 1)
              + ((n : ℝ) + 3) * (6 : ℝ) ^ n ≤ (6 : ℝ) ^ (n + 2) * ((n : ℝ) + 2) := by
          rw [hp1, hp2]
          nlinarith [hpowpos, hncast]
        rw [heq, abs_div, abs_of_pos hden]
        have h2' : |(2 * (n : ℝ) + 5) * gC (n + 1) x + (2 * (n : ℝ) + 5) * x * deriv (gC (n + 1)) x
              - ((n : ℝ) + 3) * deriv (gC n) x| / ((n : ℝ) + 2)
            ≤ ((2 * (n : ℝ) + 5) * (6 : ℝ) ^ (n + 1) + (2 * (n : ℝ) + 5) * (6 : ℝ) ^ (n + 1)
              + ((n : ℝ) + 3) * (6 : ℝ) ^ n) / ((n : ℝ) + 2) :=
          div_le_div_of_nonneg_right hnum (le_of_lt hden)
        have h3' : ((2 * (n : ℝ) + 5) * (6 : ℝ) ^ (n + 1) + (2 * (n : ℝ) + 5) * (6 : ℝ) ^ (n + 1)
              + ((n : ℝ) + 3) * (6 : ℝ) ^ n) / ((n : ℝ) + 2) ≤ (6 : ℝ) ^ (n + 2) := by
          rw [div_le_iff₀ hden]
          exact hfin
        linarith [h2', h3']

/-- For an odd index `2m+1`, the bound `|gC (2m+1) x| ≤ 6^(2m+1) · x` on `[0,1]`, obtained from
`gC (2m+1) 0 = 0` and the derivative bound of `gC_bound_pair` by the mean value theorem. -/
lemma gC_odd_le_self (m : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    |gC (2 * m + 1) x| ≤ (6 : ℝ) ^ (2 * m + 1) * x := by
  rcases lt_or_eq_of_le hx.1 with hpos | hzero
  · have hxne : x ≠ 0 := ne_of_gt hpos
    have hcont : ContinuousOn (gC (2 * m + 1)) (Set.Icc (0 : ℝ) x) :=
      (contDiff_gC (2 * m + 1)).continuous.continuousOn
    have hdiff : DifferentiableOn ℝ (gC (2 * m + 1)) (Set.Ioo (0 : ℝ) x) :=
      ((contDiff_gC (2 * m + 1)).differentiable (by norm_num)).differentiableOn
    obtain ⟨c, hc, hceq⟩ := exists_deriv_eq_slope (gC (2 * m + 1)) hpos hcont hdiff
    have hcI : c ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨le_of_lt hc.1, le_trans (le_of_lt hc.2) hx.2⟩
    have hb : |deriv (gC (2 * m + 1)) c| ≤ (6 : ℝ) ^ (2 * m + 1) :=
      (gC_bound_pair (2 * m + 1)).2 c hcI
    have hmul : deriv (gC (2 * m + 1)) c * x = gC (2 * m + 1) x := by
      rw [hceq]
      simp only [sub_zero, gC_odd_zero m]
      exact div_mul_cancel₀ _ hxne
    calc |gC (2 * m + 1) x| = |deriv (gC (2 * m + 1)) c * x| := by rw [hmul]
      _ = |deriv (gC (2 * m + 1)) c| * |x| := abs_mul _ _
      _ = |deriv (gC (2 * m + 1)) c| * x := by rw [abs_of_nonneg hx.1]
      _ ≤ (6 : ℝ) ^ (2 * m + 1) * x := mul_le_mul_of_nonneg_right hb hx.1
  · rw [← hzero, gC_odd_zero m, abs_zero]
    simp

theorem eFam_sin_two_bound (m : ℕ) : ∃ A : ℝ, 0 ≤ A ∧ ∀ θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
    |Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ A * Real.sin (2 * θ) := by
  refine ⟨(6 : ℝ) ^ (2 * m + 1) / 2, by positivity, ?_⟩
  intro θ hθ
  rcases hθ with ⟨hθ0, hθ1⟩
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hsin0 : 0 ≤ Real.sin θ := Real.sin_nonneg_of_mem_Icc ⟨hθ0, by linarith [hpi]⟩
  have hcos0 : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc ⟨by linarith [hpi], hθ1⟩
  have hsin1 : Real.sin θ ≤ 1 := Real.sin_le_one θ
  have hb := gC_odd_le_self m (show Real.sin θ ∈ Set.Icc (0 : ℝ) 1 from ⟨hsin0, hsin1⟩)
  have hefam : eFam m θ = Real.cos θ * gC (2 * m + 1) (Real.sin θ) := rfl
  calc |Work.FTS.PhiStar.Gegenbauer.eFam m θ|
      = |Real.cos θ| * |gC (2 * m + 1) (Real.sin θ)| := by rw [hefam, abs_mul]
    _ = Real.cos θ * |gC (2 * m + 1) (Real.sin θ)| := by rw [abs_of_nonneg hcos0]
    _ ≤ Real.cos θ * ((6 : ℝ) ^ (2 * m + 1) * Real.sin θ) := mul_le_mul_of_nonneg_left hb hcos0
    _ = ((6 : ℝ) ^ (2 * m + 1) / 2) * Real.sin (2 * θ) := by
        rw [Real.sin_two_mul]; ring

end Work.FTS.ClassC
