import Mathlib
import Submission.Work.EQ.GermSetup
import Submission.Work.EQ.SqrtNearOne

/-!
# The algebraic identity behind `GermFE`

With `h = hOf ρ` and `S = SOf ρ u = (1 + (h u)²)^(1/2)`, the left hand side of the germ
equation equals `u^4 * GOf a ρ u`.
-/

namespace Work.EQ

open Complex Metric Filter

variable {a : ℝ}

lemma hOf_eq_mul_beta (ρ : ℂ → ℂ) (u : ℂ) : hOf ρ u = u * betaOf ρ u := by
  simp only [hOf, betaOf]; ring

lemma one_add_hOf_sq (ρ : ℂ → ℂ) (u : ℂ) :
    1 + hOf ρ u ^ 2 = 1 + u ^ 2 * (betaOf ρ u) ^ 2 := by
  rw [hOf_eq_mul_beta]; ring

lemma hOf_sub_hOf_div {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (ρ : ℂ → ℂ) (u : ℂ) :
    hOf ρ u - hOf ρ (u / lamC a) = u * ((1 / lamC a - 1) + u ^ 2 * A1Of a ρ u) := by
  have hne : lamC a ≠ 0 := lamC_ne_zero_gs ha0 ha1
  simp only [hOf, A1Of]
  field_simp
  ring

lemma hOf_mul_sub {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (ρ : ℂ → ℂ) (u : ℂ) :
    hOf ρ (lamC a * u) - hOf ρ u = u * ((1 - lamC a) + u ^ 2 * A2Of a ρ u) := by
  simp only [hOf, A2Of]
  ring

lemma hOf_mul_sub_div {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (ρ : ℂ → ℂ) (u : ℂ) :
    hOf ρ (lamC a * u) - hOf ρ (u / lamC a) =
      u * ((1 / lamC a - lamC a) + u ^ 2 * A3Of a ρ u) := by
  have hne : lamC a ≠ 0 := lamC_ne_zero_gs ha0 ha1
  simp only [hOf, A3Of]
  field_simp
  ring

/-- The germ equation, written with `hOf`: `(A - A')(A'' - A) + a A (A'' - A') S = 0`
where the three differences are the ones above. -/
lemma germLHS_eq {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (ρ : ℂ → ℂ) (u : ℂ) :
    (hOf ρ u - hOf ρ (u / lamC a)) * (hOf ρ (lamC a * u) - hOf ρ u)
        + (a : ℂ) * hOf ρ u * (hOf ρ (lamC a * u) - hOf ρ (u / lamC a)) *
          (1 + hOf ρ u ^ 2) ^ (1 / 2 : ℂ)
      = u ^ 2 * (((1 / lamC a - 1) + u ^ 2 * A1Of a ρ u) *
            ((1 - lamC a) + u ^ 2 * A2Of a ρ u)
          + (a : ℂ) * betaOf ρ u * ((1 / lamC a - lamC a) + u ^ 2 * A3Of a ρ u)
              * SOf ρ u) := by
  rw [hOf_sub_hOf_div ha0 ha1, hOf_mul_sub ha0 ha1, hOf_mul_sub_div ha0 ha1, hOf_eq_mul_beta]
  rw [show 1 + (u * betaOf ρ u) ^ 2 = 1 + u ^ 2 * (betaOf ρ u) ^ 2 by ring]
  simp only [SOf]
  ring


lemma a_eq_lamC {a : ℝ} (ha0 : 0 < a) : (a : ℂ) = (1 - lamC a) / (1 + lamC a) := by
  rw [lamC, ← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_add,
    ← Complex.ofReal_div]
  exact_mod_cast a_eq ha0

lemma one_add_lamC_ne_zero {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    (1 : ℂ) + lamC a ≠ 0 := by
  have h : (1 : ℝ) + eqLam a ≠ 0 := by
    have := eqLam_pos ha0 ha1
    linarith
  rw [lamC, ← Complex.ofReal_one, ← Complex.ofReal_add]
  exact_mod_cast h

lemma SOf_sq (ρ : ℂ → ℂ) (u : ℂ) : SOf ρ u ^ 2 = 1 + u ^ 2 * (betaOf ρ u) ^ 2 := by
  simp only [SOf, sqHalf]
  exact sqHalf_sq _

/-- `u² W = S - 1`. -/
lemma sq_mul_WOf {ρ : ℂ → ℂ} {u : ℂ} (hS2 : SOf ρ u ^ 2 = 1 + u ^ 2 * (betaOf ρ u) ^ 2)
    (h1S : (1 : ℂ) + SOf ρ u ≠ 0) : u ^ 2 * WOf ρ u = SOf ρ u - 1 := by
  rw [WOf]
  field_simp
  linear_combination (-1 : ℂ) * hS2

/-- `WOf ρ u = (S - 1)/u²` for `u ≠ 0`. -/
lemma WOf_eq_div {ρ : ℂ → ℂ} {u : ℂ} (hu : u ≠ 0)
    (hS2 : SOf ρ u ^ 2 = 1 + u ^ 2 * (betaOf ρ u) ^ 2)
    (h1S : (1 : ℂ) + SOf ρ u ≠ 0) :
    WOf ρ u = (SOf ρ u - 1) / u ^ 2 := by
  rw [WOf, div_eq_div_iff h1S (pow_ne_zero 2 hu), sub_mul, one_mul]
  linear_combination (-1 : ℂ) * hS2

/-- The germ equation with `h = hOf ρ` equals `u^4 * GOf a ρ u`. -/
theorem germFE_eq_u4_GOf {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (ρ : ℂ → ℂ) (u : ℂ)
    (hS : SOf ρ u ≠ -1) :
    (hOf ρ u - hOf ρ (u / lamC a)) * (hOf ρ (lamC a * u) - hOf ρ u)
        + (a : ℂ) * hOf ρ u * (hOf ρ (lamC a * u) - hOf ρ (u / lamC a))
          * (1 + hOf ρ u ^ 2) ^ (1 / 2 : ℂ)
      = u ^ 4 * GOf a ρ u := by
  rcases eq_or_ne u 0 with rfl | hu
  · simp [hOf, GOf, GlinOf, GnlOf, A1Of, A2Of, A3Of, WOf, SOf, betaOf]
  · have hS2 : SOf ρ u ^ 2 = 1 + u ^ 2 * (betaOf ρ u) ^ 2 := SOf_sq ρ u
    have h1S : (1 : ℂ) + SOf ρ u ≠ 0 := by
      intro h
      exact hS (by linear_combination h)
    have hS1 : SOf ρ u = 1 + u ^ 2 * WOf ρ u := by
      have h := sq_mul_WOf (ρ := ρ) hS2 h1S
      linear_combination (-1 : ℂ) * h
    have hl : ((eqLam a : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (eqLam_pos ha0 ha1))
    have hl1 : (1 : ℂ) + ((eqLam a : ℝ) : ℂ) ≠ 0 := by
      have h : (1 : ℝ) + eqLam a ≠ 0 := by linarith [eqLam_pos ha0 ha1]
      rw [← Complex.ofReal_one, ← Complex.ofReal_add]
      exact_mod_cast h
    rw [germLHS_eq ha0 ha1, hS1]
    simp only [GOf, GlinOf, GnlOf, A1Of, A2Of, A3Of, betaOf, kapC, lamC]
    rw [a_eq_lamC ha0]
    simp only [lamC]
    push_cast
    field_simp
    ring

end Work.EQ
