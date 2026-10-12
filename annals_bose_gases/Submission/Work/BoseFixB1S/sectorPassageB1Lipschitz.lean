import Mathlib.Analysis.Convex.Function
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1.rPsiB_nonneg
import Submission.Work.BoseFixB1B.RsbSide_sq_le_holds
import Submission.Work.BoseFixB1B.integratedOfPointwise
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1S.sectorPassageB1Lipschitz` — the Lipschitz bound on FS's weight

`F(t) = psiWeight 1 μ t = μ(t−μ)²/(t+μ)` satisfies `|F(t) − F(s)| ≤ 5μ|t−s|` for `t, s ≥ 0`.
This is the elementary input of the background-corrected smooth ⟹ sharp comparison: iterated with
`F(N(x)/χ) ≤ F(s) + 5μ|N(x)/χ − s|` it turns the *smooth* level into the *sharp* level plus a
`5μ·(local count)`-term, and the latter is what the word's fibre term (`wSmall1Pair_fibre_le_chiB`)
and the sharp/background/error terms pay.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Real Topology BigOperators ENNReal

namespace Work.BoseFixB1S

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **`F(t) = μt − 3μ² + 4μ³/(t+μ)`** for `t ≥ 0`. -/
lemma psiWeight_one_eq {μ t : ℝ} (hμ : 0 < μ) (ht : 0 ≤ t) :
    Work.SmallBoxSliding.psiWeight 1 μ t = μ * t - 3 * μ ^ 2 + 4 * μ ^ 3 / (t + μ) := by
  rw [Work.SmallBoxSliding.psiWeight, show (1 : ℝ) + t * μ⁻¹ = (t + μ) / μ by
    field_simp
    ring]
  have hden : t + μ ≠ 0 := by positivity
  field_simp
  ring

/-- **The Lipschitz bound**: `|F(t) − F(s)| ≤ 5μ|t − s|` for `t, s ≥ 0`. -/
lemma abs_psiWeight_one_sub_le {μ t s : ℝ} (hμ : 0 < μ) (ht : 0 ≤ t) (hs : 0 ≤ s) :
    |Work.SmallBoxSliding.psiWeight 1 μ t - Work.SmallBoxSliding.psiWeight 1 μ s|
      ≤ 5 * μ * |t - s| := by
  rw [psiWeight_one_eq hμ ht, psiWeight_one_eq hμ hs]
  have hden_t : 0 < t + μ := by linarith
  have hden_s : 0 < s + μ := by linarith
  have hprod : 0 < (t + μ) * (s + μ) := mul_pos hden_t hden_s
  have h1 : μ * t - 3 * μ ^ 2 + 4 * μ ^ 3 / (t + μ) - (μ * s - 3 * μ ^ 2 + 4 * μ ^ 3 / (s + μ))
      = μ * (t - s) + 4 * μ ^ 3 * (1 / (t + μ) - 1 / (s + μ)) := by ring
  rw [h1]
  have h2 : 1 / (t + μ) - 1 / (s + μ) = -(t - s) / ((t + μ) * (s + μ)) := by
    field_simp
    ring
  rw [h2]
  have h3 : μ * (t - s) + 4 * μ ^ 3 * (-(t - s) / ((t + μ) * (s + μ)))
      = μ * (t - s) - 4 * μ ^ 3 * ((t - s) / ((t + μ) * (s + μ))) := by ring
  rw [h3]
  have h4 : |4 * μ ^ 3 * ((t - s) / ((t + μ) * (s + μ)))|
      = 4 * μ ^ 3 * (|t - s| / ((t + μ) * (s + μ))) := by
    rw [abs_mul, abs_div, abs_of_pos hprod, abs_of_nonneg (by positivity : (0:ℝ) ≤ 4 * μ ^ 3)]
  calc |μ * (t - s) - 4 * μ ^ 3 * ((t - s) / ((t + μ) * (s + μ)))|
      ≤ |μ * (t - s)| + |4 * μ ^ 3 * ((t - s) / ((t + μ) * (s + μ)))| := abs_sub _ _
    _ = μ * |t - s| + 4 * μ ^ 3 * (|t - s| / ((t + μ) * (s + μ))) := by
        rw [h4, abs_mul, abs_of_pos hμ]
    _ ≤ μ * |t - s| + 4 * μ * |t - s| := by
        have h6 : 4 * μ ^ 3 * (|t - s| / ((t + μ) * (s + μ))) ≤ 4 * μ * |t - s| := by
          have h7 : μ ^ 2 ≤ (t + μ) * (s + μ) := by nlinarith [hden_t, hden_s, hμ]
          have h8 : (0:ℝ) ≤ |t - s| := abs_nonneg _
          rw [mul_div_assoc', div_le_iff₀ hprod]
          nlinarith [h7, h8, hμ, mul_nonneg (le_of_lt hμ) h8]
        linarith
    _ = 5 * μ * |t - s| := by ring

/-- The one-sided form used in the passage: `F(t) ≤ F(s) + 5μ|t − s|`. -/
lemma psiWeight_one_le_add {μ t s : ℝ} (hμ : 0 < μ) (ht : 0 ≤ t) (hs : 0 ≤ s) :
    Work.SmallBoxSliding.psiWeight 1 μ t
      ≤ Work.SmallBoxSliding.psiWeight 1 μ s + 5 * μ * |t - s| := by
  have h := abs_psiWeight_one_sub_le hμ ht hs
  have h' := le_abs_self
    (Work.SmallBoxSliding.psiWeight 1 μ t - Work.SmallBoxSliding.psiWeight 1 μ s)
  linarith

/-- `0 ≤ F(t)` for `t ≥ 0`. -/
lemma psiWeight_one_nonneg {μ t : ℝ} (hμ : 0 < μ) (ht : 0 ≤ t) :
    0 ≤ Work.SmallBoxSliding.psiWeight 1 μ t := by
  rw [Work.SmallBoxSliding.psiWeight]
  have hden : 0 < 1 + t * μ⁻¹ := by
    have : 0 ≤ t * μ⁻¹ := mul_nonneg ht (le_of_lt (inv_pos.mpr hμ))
    linarith
  exact div_nonneg (mul_nonneg zero_le_one (sq_nonneg _)) (le_of_lt hden)

/-- `F(t) ≤ μ(t + μ)` (for `t ≥ 0`), from the explicit form. -/
lemma psiWeight_one_le_mu_add {μ t : ℝ} (hμ : 0 < μ) (ht : 0 ≤ t) :
    Work.SmallBoxSliding.psiWeight 1 μ t ≤ μ * (t + μ) := by
  rw [psiWeight_one_eq hμ ht]
  have hden : 0 < t + μ := by linarith
  have h4 : 4 * μ ^ 3 / (t + μ) ≤ 4 * μ ^ 2 := by
    rw [div_le_iff₀ hden]; nlinarith [hμ, ht]
  linarith

/-- `F(s) ≥ μ s / 8` for `s ≥ 2μ` (the growth bound). -/
lemma psiWeight_one_ge {μ s : ℝ} (hμ : 0 < μ) (hs : 2 * μ ≤ s) :
    μ * s / 8 ≤ Work.SmallBoxSliding.psiWeight 1 μ s := by
  have hs0 : 0 < s := by linarith
  have hden : 0 < s + μ := by linarith
  have hF : Work.SmallBoxSliding.psiWeight 1 μ s = μ * (s - μ) ^ 2 / (s + μ) := by
    rw [psiWeight_one_eq hμ (le_of_lt hs0)]
    field_simp
    ring
  have hs1 : 0 ≤ s - 2 * μ := by linarith
  have hs2 : 0 ≤ 7 * s - 3 * μ := by linarith
  rw [hF, le_div_iff₀ hden]
  have hkey : 0 ≤ (s - 2 * μ) * (7 * s - 3 * μ) := mul_nonneg hs1 hs2
  nlinarith [hkey, sq_nonneg μ]

/-- **The scalar comparison** used for the smooth ⟹ sharp passage at coefficient `γ ≤ 1/200`:
`γ F(s) + 10 γ μ s ≤ ½ F(s) + ½ μ²` for all `s ≥ 0`.  (The `10γμs` collects the two Lipschitz
remainders `5γμs` produced by the `t`- and the `s`-part of `|t − s| ≤ t + s`.) -/
lemma psiWeight_one_scalar {μ s γ : ℝ} (hμ : 0 < μ) (hs : 0 ≤ s) (hγ0 : 0 ≤ γ)
    (hγ : γ ≤ 1 / 200) :
    γ * Work.SmallBoxSliding.psiWeight 1 μ s + 10 * γ * μ * s
      ≤ (1 / 2) * Work.SmallBoxSliding.psiWeight 1 μ s + (1 / 2) * μ ^ 2 := by
  have hF0 : 0 ≤ Work.SmallBoxSliding.psiWeight 1 μ s := psiWeight_one_nonneg hμ hs
  rcases le_total s (2 * μ) with h | h
  · -- small density: `F(s) ≤ 3μ²` and `s ≤ 2μ`
    have h1 : Work.SmallBoxSliding.psiWeight 1 μ s ≤ 3 * μ ^ 2 := by
      have h3 := psiWeight_one_le_mu_add hμ hs
      have h4 : μ * (s + μ) ≤ μ * (3 * μ) :=
        mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hμ)
      nlinarith [h3, h4]
    have hA : (γ - 1 / 2) * Work.SmallBoxSliding.psiWeight 1 μ s ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) hF0
    have hB : 10 * γ * μ * s ≤ 10 * γ * μ * (2 * μ) := by
      have h5 : (0:ℝ) ≤ 10 * γ * μ := by positivity
      nlinarith [h5, h, hs]
    nlinarith [hA, hB, h1, hF0, hγ, hγ0, hμ, hs]
  · -- large density: `F(s) ≥ μ s / 8` and `F(s) ≤ (3/2) μ s`
    have h1 : μ * s / 8 ≤ Work.SmallBoxSliding.psiWeight 1 μ s := psiWeight_one_ge hμ h
    have h2 : Work.SmallBoxSliding.psiWeight 1 μ s ≤ 3 * μ * s / 2 := by
      have h3 := psiWeight_one_le_mu_add hμ hs
      have h4 : μ * (s + μ) ≤ μ * (s + s / 2) :=
        mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hμ)
      nlinarith [h3, h4]
    nlinarith [h1, h2, hγ, hγ0, hμ, hs]

/-- `F(0) = μ²`. -/
lemma psiWeight_one_zero_eq {μ : ℝ} (hμ : 0 < μ) :
    Work.SmallBoxSliding.psiWeight 1 μ 0 = μ ^ 2 := by
  rw [psiWeight_one_eq hμ le_rfl]
  field_simp
  ring

/-- **The convexity/concentration split** (the form the passage actually needs):
`F(t) ≤ F(s) + 5μ·(t − s)₊ + μ²` for `t, s ≥ 0`.

For `t ≤ s` this is the convexity endpoint bound `F(t) ≤ max(F(0), F(s)) = max(μ², F(s))`
(`Work.FockBridge.convexOn_dlDensityCoeff`); for `t ≥ s` it is the Lipschitz bound
`F(t) ≤ F(s) + 5μ(t−s)`.  Unlike the two-sided Lipschitz bound it produces **no** `s`-term and only
the *one-sided* local excess `(t − s)₊`, which is what the word's positive parts (the pair term and
the excited-count/gap payment `sbKin_ge_mu_av_cnPlus`) can pay; the `μ²` is the FS background. -/
lemma psiWeight_one_le_add_pos {μ t s : ℝ} (hμ : 0 < μ) (ht : 0 ≤ t) (hs : 0 ≤ s) :
    Work.SmallBoxSliding.psiWeight 1 μ t
      ≤ Work.SmallBoxSliding.psiWeight 1 μ s + 5 * μ * max (t - s) 0 + μ ^ 2 := by
  rcases le_total t s with h | h
  · rcases eq_or_lt_of_le h with hts | hts
    · rw [hts]
      simp only [sub_self, max_self, mul_zero, zero_add]
      nlinarith [sq_nonneg μ]
    · have hs0 : 0 < s := lt_of_le_of_lt ht hts
      rw [max_eq_right (by linarith : t - s ≤ 0)]
      have hF0 : Work.SmallBoxSliding.psiWeight 1 μ 0 = μ ^ 2 := psiWeight_one_zero_eq hμ
      have hFs : 0 ≤ Work.SmallBoxSliding.psiWeight 1 μ s := psiWeight_one_nonneg hμ hs
      have hconv : ConvexOn ℝ (Set.Ici (0 : ℝ))
          (fun t => Work.SmallBoxSliding.psiWeight 1 μ t) :=
        Work.FockBridge.convexOn_dlDensityCoeff (c := 1) (μ := μ) zero_le_one hμ
      have hta0 : 0 ≤ t / s := div_nonneg ht (le_of_lt hs0)
      have hta1 : t / s ≤ 1 := by rw [div_le_one hs0]; linarith
      have hsum : (1 - t / s) + t / s = 1 := by ring
      have hrepr : (1 - t / s) • (0 : ℝ) + (t / s) • s = t := by
        rw [smul_zero, zero_add, smul_eq_mul]
        exact div_mul_cancel₀ t (ne_of_gt hs0)
      have hstep := hconv.2 (show (0 : ℝ) ∈ Set.Ici (0 : ℝ) from by rw [Set.mem_Ici])
        (show s ∈ Set.Ici (0 : ℝ) from hs)
        (show (0 : ℝ) ≤ 1 - t / s from by linarith)
        (show (0 : ℝ) ≤ t / s from hta0)
        (show (1 - t / s) + t / s = 1 from hsum)
      rw [hrepr] at hstep
      have h1 : (1 - t / s) * Work.SmallBoxSliding.psiWeight 1 μ 0 ≤ μ ^ 2 := by
        rw [hF0]; nlinarith [hta0, sq_nonneg μ]
      have h2 : (t / s) * Work.SmallBoxSliding.psiWeight 1 μ s
          ≤ Work.SmallBoxSliding.psiWeight 1 μ s := by
        nlinarith [hta1, hFs]
      have hstep' : Work.SmallBoxSliding.psiWeight 1 μ t
          ≤ (1 - t / s) * Work.SmallBoxSliding.psiWeight 1 μ 0
            + (t / s) * Work.SmallBoxSliding.psiWeight 1 μ s := by
        simpa only [smul_eq_mul] using hstep
      linarith [hstep', h1, h2]
  · have h1 := psiWeight_one_le_add hμ ht hs
    have h2 : |t - s| = t - s := abs_of_nonneg (by linarith)
    rw [h2] at h1
    rw [max_eq_left (by linarith : (0 : ℝ) ≤ t - s)]
    linarith [h1, sq_nonneg μ]

end Work.BoseFixB1S
