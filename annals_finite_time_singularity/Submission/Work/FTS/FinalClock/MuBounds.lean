/-
# `Work.FTS.FinalClock.MuBounds` — `muDyn_small`: the modulation is of order `α`

Design §2 (`FTS_PHYS_BRIDGE.md`, item 8).  Elgindi's Proposition `muestimate` (tex 1508)

  `|μ| ≤ C (α + α^{-3/2}|g|_{ℋ⁴} + α^{-5/2}|g|²_{ℋ⁴})`

(together with the `ℋ⁴` bound `|g|_{ℋ⁴} ≤ K α²` of the paper's own corollary) gives the
modulation bound that the clock needs.  This file records the resulting estimates in the shapes in
which they are consumed:

* `muDyn_small` — `|muDyn α Φ g τ| ≤ C (1 + K + K²) α` from the three `L₁₂`-estimates in the
  scaled shape of `Work.FTS.H2.MuEstimate` (`N₀`, `N`, `3D_θg/(1+z)`) plus `|g(τ)|_{ℋ⁴} ≤ K α²`.
  **The exponent is `α`, not `α²`**: the leading `α²` of the three `L₁₂`-estimates is divided by
  the `1/(2α)` of `mufunS`, so the honest order of `μ` is `α` — the paper's "it will, in fact, be of
  order `α` in the end" (after tex 1502).  The crude `α^{-3/2}|g|` of `MuEstimate` would only give
  `α^{1/2}`; the arithmetic below uses the `L₁₂`-hypotheses directly, which is legitimate because
  the *scaled* hypotheses of `MuEstimateScaled` already carry `√α|g|` in place of
  `α^{-1/2}|g|`.
* `muDyn_small_quad` — the literal order-`α²` form of the design, under the sharpened
  `L₁₂`-estimates of size `α³` (the `α^{-1/2}`-improvement that the Remark after tex 1508 says is
  available).
* `muDyn_le_half` — the usable consequence `|muDyn| ≤ 1/2` for `α` small, i.e. the `hμ`
  hypothesis of `physClock_of_dyn`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Interval.Basic
import Submission.Work.FTS.FinalClock.PhysClock
import Submission.Work.FTS.H2.MuEstimate
import Submission.Work.FTS.H2.MuEstimateScaled
import Submission.Work.FTS.H2.L12ZeroLe
import Submission.Work.Construction.MufunS

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false

noncomputable section

open Filter MeasureTheory Set
open scoped Topology Interval

namespace Work.FTS.FinalClock

open Work.Construction (L12 N0 N Ftau mufunS)
open Work.Spaces (HkNorm Dth)
open Work.FTS.Galerkin (Fam slice muDyn)

/-! ## The bridge from `L₁₂`-estimates to the `ℋ⁴` norm -/

/-- `L₁₂(f)(0)` is controlled by the `ℋ⁴`-norm of `f` (`Work.FTS.H2.L12ZeroLe`), in the
`Work.Construction.L12` spelling used by `muDyn`. -/
theorem L12_zero_le_HkNorm {α : ℝ} {f : ℝ → ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hsm : Work.Spaces.SmoothNbhd f) (hmem : Work.Spaces.HkMem α 4 f) :
    ∃ C : ℝ, 0 < C ∧ |L12 f 0| ≤ C * HkNorm α 4 f := by
  obtain ⟨C, hC, h⟩ := Work.FTS.H2.L12ZeroLe
  exact ⟨C, hC, h α f hα hα1 hsm hmem⟩

/-- The `L₁₂`-functional is Lipschitz for the *difference* of two data (the elementary linearity
step of the `τ`-Lipschitz estimate of `muDyn_holderOn`), *given* the linearity of `L₁₂` in its
argument (`Work.FM.L12_add`, `Work.FM.L12_neg`).  The linearity hypothesis `hlin` keeps the
integrability side conditions of `Work.FM.L12_add` out of the interface; it is exactly what those
lemmas supply for the densities of the two data. -/
theorem L12_sub_le {α : ℝ} {f₁ f₂ : ℝ → ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hlin : L12 f₁ 0 - L12 f₂ 0 = L12 (fun z θ => f₁ z θ - f₂ z θ) 0)
    (hsm : Work.Spaces.SmoothNbhd (fun z θ => f₁ z θ - f₂ z θ))
    (hmem : Work.Spaces.HkMem α 4 (fun z θ => f₁ z θ - f₂ z θ)) :
    ∃ C : ℝ, 0 < C ∧ |L12 f₁ 0 - L12 f₂ 0| ≤ C * HkNorm α 4 (fun z θ => f₁ z θ - f₂ z θ) := by
  obtain ⟨C, hC, h⟩ := L12_zero_le_HkNorm hα hα1 hsm hmem
  rw [hlin]
  exact ⟨C, hC, h⟩

/-! ## The arithmetic of `muDyn_small` -/

/-- `α^{-1/2}·α⁴ ≤ α²` for `0 < α ≤ 1`. -/
private theorem rpow_neg_half_mul_pow_four_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    α ^ (-(1 / 2 : ℝ)) * α ^ 4 ≤ α ^ 2 := by
  have h4 : α ^ (4 : ℝ) = α ^ 4 := Real.rpow_natCast α 4
  have h2 : α ^ (2 : ℝ) = α ^ 2 := Real.rpow_natCast α 2
  rw [← h4, ← h2, ← Real.rpow_add hα]
  have : -(1 / 2 : ℝ) + 4 = 7 / 2 := by norm_num
  rw [this]
  exact Real.rpow_le_rpow_of_exponent_ge hα hα1 (by norm_num)

/-- **The arithmetic of `muDyn_small`.**  If `X ≤ K α²` with `0 < α ≤ 1`, `K ≥ 0`, then
`(1/(2α))(2α² + 2αX + 2α^{-1/2}X² + X) ≤ 48(1 + K + K²)α`: the terms `α²`, `αX`, `X` produce
`α`, `X ≤ Kα`, `X/(2α) ≤ Kα/2`, and `α^{-1/2}X² ≤ α^{-1/2}K²α⁴ ≤ K²α^{5/2} ≤ K²α`. -/
private theorem mu_arith_small {α K X : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hK : 0 ≤ K)
    (hX0 : 0 ≤ X) (hX : X ≤ K * α ^ 2) :
    (1 / (2 * α)) * (2 * α ^ 2 + 2 * α * X + 2 * (α ^ (-(1 / 2 : ℝ)) * X ^ 2) + X)
      ≤ 48 * (1 + K + K ^ 2) * α := by
  have h2 : 2 * α * X ≤ 2 * K * α ^ 2 := by
    have hα3 : α ^ 3 ≤ α ^ 2 := pow_le_pow_of_le_one hα.le hα1 (by norm_num)
    have h := mul_le_mul_of_nonneg_left hX (by positivity : (0 : ℝ) ≤ 2 * α)
    have hk : 2 * K * α ^ 3 ≤ 2 * K * α ^ 2 := mul_le_mul_of_nonneg_left hα3 (by linarith)
    linarith
  have h3 : 2 * (α ^ (-(1 / 2 : ℝ)) * X ^ 2) ≤ 2 * K ^ 2 * α ^ 2 := by
    have hX2 : X ^ 2 ≤ K ^ 2 * α ^ 4 := by
      have h := mul_self_le_mul_self hX0 hX
      nlinarith [h, hK, hα.le, sq_nonneg α]
    have h1 : α ^ (-(1 / 2 : ℝ)) * X ^ 2 ≤ α ^ (-(1 / 2 : ℝ)) * (K ^ 2 * α ^ 4) :=
      mul_le_mul_of_nonneg_left hX2 (Real.rpow_nonneg hα.le _)
    have h4 : α ^ (-(1 / 2 : ℝ)) * (K ^ 2 * α ^ 4) ≤ K ^ 2 * α ^ 2 := by
      have h := rpow_neg_half_mul_pow_four_le hα hα1
      nlinarith [h, hK, hα.le, sq_nonneg K]
    linarith
  have hS : 2 * α ^ 2 + 2 * α * X + 2 * (α ^ (-(1 / 2 : ℝ)) * X ^ 2) + X
      ≤ (2 + 3 * K + 2 * K ^ 2) * α ^ 2 := by linarith [h2, h3, hX]
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0 : ℝ) < 2 * α)]
  nlinarith [hS, hK, sq_nonneg α, sq_nonneg K, hα.le]

/-- **The arithmetic of `muDyn_small` and `muDyn_small_quad`**: given the three `L₁₂`-bounds, the
value of `mufunS` (which is `(1/(2α))` times the *sum* of the three) obeys the displayed
bound. -/
private theorem mufunS_arith {α A0 A1 A2 X : ℝ} (hα : 0 < α)
    (h0 : |A0| ≤ α ^ 2 + α * X + α ^ (-(1 / 2 : ℝ)) * X ^ 2)
    (h1 : |A1| ≤ α ^ 2 + α * X + α ^ (-(1 / 2 : ℝ)) * X ^ 2) (h2 : |A2| ≤ X) :
    |(1 / (2 * α)) * (A0 + A1) + (1 / (2 * α)) * A2|
      ≤ (1 / (2 * α)) * (2 * α ^ 2 + 2 * α * X + 2 * (α ^ (-(1 / 2 : ℝ)) * X ^ 2) + X) := by
  have hfac : (1 / (2 * α)) * (A0 + A1) + (1 / (2 * α)) * A2
      = (1 / (2 * α)) * (A0 + A1 + A2) := by ring
  rw [hfac, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * α))]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have htri : |A0 + A1 + A2| ≤ 2 * (α ^ 2 + α * X + α ^ (-(1 / 2 : ℝ)) * X ^ 2) + X := by
    have key : |A0 + A1 + A2| ≤ |A0| + |A1| + |A2| := by
      linarith [abs_add_le A0 A1, abs_add_le (A0 + A1) A2]
    linarith
  calc |A0 + A1 + A2|
      ≤ 2 * (α ^ 2 + α * X + α ^ (-(1 / 2 : ℝ)) * X ^ 2) + X := htri
    _ = 2 * α ^ 2 + 2 * α * X + 2 * (α ^ (-(1 / 2 : ℝ)) * X ^ 2) + X := by ring

/-- **The arithmetic of `muDyn_small_quad`**: with `L₁₂`-estimates of size `α³`, `mufunS` is of
order `α²`. -/
private theorem mu_arith_quad {α K A0 A1 A2 : ℝ} (hα : 0 < α) (h1 : |A0| ≤ K * α ^ 3)
    (h2 : |A1| ≤ K * α ^ 3) (h3 : |A2| ≤ K * α ^ 3) :
    |(1 / (2 * α)) * (A0 + A1) + (1 / (2 * α)) * A2| ≤ 2 * K * α ^ 2 := by
  have hfac : (1 / (2 * α)) * (A0 + A1) + (1 / (2 * α)) * A2
      = (1 / (2 * α)) * (A0 + A1 + A2) := by ring
  rw [hfac, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * α))]
  have hK : 0 ≤ K := by
    by_contra h
    have hlt : K * α ^ 3 < 0 := mul_neg_of_neg_of_pos (lt_of_not_ge h) (pow_pos hα 3)
    have h3 : 0 ≤ K * α ^ 3 := le_trans (abs_nonneg A0) h1
    linarith
  have htri : |A0 + A1 + A2| ≤ 3 * (K * α ^ 3) := by
    have key : |A0 + A1 + A2| ≤ |A0| + |A1| + |A2| := by
      linarith [abs_add_le A0 A1, abs_add_le (A0 + A1) A2]
    linarith
  have hstep : (1 / (2 * α)) * |A0 + A1 + A2| ≤ (1 / (2 * α)) * (3 * (K * α ^ 3)) :=
    mul_le_mul_of_nonneg_left htri (by positivity)
  have hval : (1 / (2 * α)) * (3 * (K * α ^ 3)) = (3 / 2) * (K * α ^ 2) := by
    field_simp
  have hfin : (3 / 2) * (K * α ^ 2) ≤ 2 * K * α ^ 2 := by
    have hx : 0 ≤ K * α ^ 2 := mul_nonneg hK (sq_nonneg α)
    linarith
  calc (1 / (2 * α)) * |A0 + A1 + A2|
      ≤ (1 / (2 * α)) * (3 * (K * α ^ 3)) := hstep
    _ = (3 / 2) * (K * α ^ 2) := hval
    _ ≤ 2 * K * α ^ 2 := hfin

/-! ## `muDyn_small` -/

/-- **`muDyn_small` (design §2, item 8).**  From the three `L₁₂`-estimates of Elgindi's
Proposition `muestimate` — for `N₀`, for `N` (in the scaled shape of
`Work.FTS.H2.MuEstimateScaled`), and for `3 D_θ g/(1+z)` — evaluated on the slice `g(τ)`, plus the
`ℋ⁴` bound `|g(τ)|_{ℋ⁴} ≤ K α²`, the dynamic modulation constant is of order `α`:

  `|muDyn α Φ g τ| ≤ C (1 + K + K²) α`.

The exponent `α` (and not `α²`) is forced by the `1/(2α)` of `mufunS` together with the leading
`α²` of the `L₁₂`-estimates, and it agrees with the paper ("`μ` is of order `α`"). -/
theorem muDyn_small : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (Φ g : Fam) (τ K : ℝ), 0 < α → α ≤ 1 → 0 ≤ K →
      HkNorm α 4 (slice g τ) ≤ K * α ^ 2 →
      |L12 (N0 α (Ftau α g τ) (slice g τ)) 0|
          ≤ α ^ 2 + α * HkNorm α 4 (slice g τ)
            + α ^ (-(1 / 2 : ℝ)) * HkNorm α 4 (slice g τ) ^ 2 →
      |L12 (N α (Ftau α g τ) (slice Φ τ)) 0|
          ≤ α ^ 2 + α * HkNorm α 4 (slice g τ)
            + α ^ (-(1 / 2 : ℝ)) * HkNorm α 4 (slice g τ) ^ 2 →
      |L12 (fun z θ => 3 * Dth (slice g τ) z θ / (1 + z)) 0| ≤ HkNorm α 4 (slice g τ) →
      |muDyn α Φ g τ| ≤ C * (1 + K + K ^ 2) * α := by
  refine ⟨48, by norm_num, ?_⟩
  intro α Φ g τ K hα hα1 hK hX h1 h2 h3
  have hX0 : 0 ≤ HkNorm α 4 (slice g τ) := Work.Spaces.HkNorm_nonneg _ _ _
  have hmu : muDyn α Φ g τ
      = (1 / (2 * α)) * (L12 (N0 α (Ftau α g τ) (slice g τ)) 0
            + L12 (N α (Ftau α g τ) (slice Φ τ)) 0)
          + (1 / (2 * α)) * L12 (fun z θ => 3 * Dth (slice g τ) z θ / (1 + z)) 0 := rfl
  rw [hmu]
  exact le_trans (mufunS_arith hα h1 h2 h3) (mu_arith_small hα hα1 hK hX0 hX)

/-- **The `α²`-version of `muDyn_small`.**  Under the *sharpened* `L₁₂`-estimates — each of the
three of size `K α³`, i.e. the `α^{-1/2}`-improvement of the last two terms of `muestimate` that
the Remark after tex 1508 says is available — the modulation is of order `α²`, which is the
literal form `|muDyn| ≤ C α_G²` of the design. -/
theorem muDyn_small_quad : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (Φ g : Fam) (τ K : ℝ), 0 < α →
      |L12 (N0 α (Ftau α g τ) (slice g τ)) 0| ≤ K * α ^ 3 →
      |L12 (N α (Ftau α g τ) (slice Φ τ)) 0| ≤ K * α ^ 3 →
      |L12 (fun z θ => 3 * Dth (slice g τ) z θ / (1 + z)) 0| ≤ K * α ^ 3 →
      |muDyn α Φ g τ| ≤ C * K * α ^ 2 := by
  refine ⟨2, by norm_num, ?_⟩
  intro α Φ g τ K hα h1 h2 h3
  have hmu : muDyn α Φ g τ
      = (1 / (2 * α)) * (L12 (N0 α (Ftau α g τ) (slice g τ)) 0
            + L12 (N α (Ftau α g τ) (slice Φ τ)) 0)
          + (1 / (2 * α)) * L12 (fun z θ => 3 * Dth (slice g τ) z θ / (1 + z)) 0 := rfl
  rw [hmu]
  exact mu_arith_quad hα h1 h2 h3

/-- **The arithmetic of `muDyn_small_of_H4`**: `L₁₂`-bounds of size `K α²` give `μ` of order `α`. -/
private theorem mu_arith_H4 {α K A0 A1 A2 : ℝ} (hα : 0 < α)
    (h1 : |A0| ≤ K * α ^ 2) (h2 : |A1| ≤ K * α ^ 2) (h3 : |A2| ≤ K * α ^ 2) :
    |(1 / (2 * α)) * (A0 + A1) + (1 / (2 * α)) * A2| ≤ 2 * K * α := by
  have hfac : (1 / (2 * α)) * (A0 + A1) + (1 / (2 * α)) * A2
      = (1 / (2 * α)) * (A0 + A1 + A2) := by ring
  rw [hfac, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * α))]
  have key : |A0 + A1 + A2| ≤ |A0| + |A1| + |A2| := by
    linarith [abs_add_le A0 A1, abs_add_le (A0 + A1) A2]
  have htri : |A0 + A1 + A2| ≤ 3 * (K * α ^ 2) := by linarith
  have hval : (1 / (2 * α)) * (3 * (K * α ^ 2)) = (3 * K / 2) * α := by
    field_simp
  have hKα : 0 ≤ K * α := by
    have hKα2 : 0 ≤ K * α ^ 2 := le_trans (abs_nonneg A0) h1
    nlinarith [hKα2, hα]
  calc (1 / (2 * α)) * |A0 + A1 + A2|
      ≤ (1 / (2 * α)) * (3 * (K * α ^ 2)) :=
        mul_le_mul_of_nonneg_left htri (by positivity)
    _ = (3 * K / 2) * α := hval
    _ ≤ 2 * K * α := by linarith [hKα]

/-- **`muDyn_small_of_H4`: the modulation is of order `α` from the `ℋ⁴` bounds alone.**  If the
three data of `muDyn` have `ℋ⁴`-norm at most `K' α²` and are in `ℋ⁴` together with the smoothness
that `Work.FTS.H2.L12ZeroLe` needs, then `|muDyn α Φ g τ| ≤ C K' α` with an absolute `C`.  This is
the form of the design's request "|μ| ≤ C·α_G² from the H⁴ bound" with the honest exponent `α`
(see the file docstring). -/
theorem muDyn_small_of_H4 : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (Φ g : Fam) (τ K' : ℝ), 0 < α → α ≤ 1 → 0 ≤ K' →
      HkNorm α 4 (N0 α (Ftau α g τ) (slice g τ)) ≤ K' * α ^ 2 →
      HkNorm α 4 (N α (Ftau α g τ) (slice Φ τ)) ≤ K' * α ^ 2 →
      HkNorm α 4 (fun z θ => 3 * Dth (slice g τ) z θ / (1 + z)) ≤ K' * α ^ 2 →
      Work.Spaces.SmoothNbhd (N0 α (Ftau α g τ) (slice g τ)) →
      Work.Spaces.HkMem α 4 (N0 α (Ftau α g τ) (slice g τ)) →
      Work.Spaces.SmoothNbhd (N α (Ftau α g τ) (slice Φ τ)) →
      Work.Spaces.HkMem α 4 (N α (Ftau α g τ) (slice Φ τ)) →
      Work.Spaces.SmoothNbhd (fun z θ => 3 * Dth (slice g τ) z θ / (1 + z)) →
      Work.Spaces.HkMem α 4 (fun z θ => 3 * Dth (slice g τ) z θ / (1 + z)) →
      |muDyn α Φ g τ| ≤ C * K' * α := by
  obtain ⟨C0, hC0, hL⟩ := Work.FTS.H2.L12ZeroLe
  refine ⟨2 * C0, by positivity, ?_⟩
  intro α Φ g τ K' hα hα1 hK' h1 h2 h3 hs1 hm1 hs2 hm2 hs3 hm3
  have b1 : |L12 (N0 α (Ftau α g τ) (slice g τ)) 0| ≤ (C0 * K') * α ^ 2 := by
    refine le_trans (hL α _ hα hα1 hs1 hm1) ?_
    calc C0 * HkNorm α 4 (N0 α (Ftau α g τ) (slice g τ))
        ≤ C0 * (K' * α ^ 2) := mul_le_mul_of_nonneg_left h1 hC0.le
      _ = (C0 * K') * α ^ 2 := by ring
  have b2 : |L12 (N α (Ftau α g τ) (slice Φ τ)) 0| ≤ (C0 * K') * α ^ 2 := by
    refine le_trans (hL α _ hα hα1 hs2 hm2) ?_
    calc C0 * HkNorm α 4 (N α (Ftau α g τ) (slice Φ τ))
        ≤ C0 * (K' * α ^ 2) := mul_le_mul_of_nonneg_left h2 hC0.le
      _ = (C0 * K') * α ^ 2 := by ring
  have b3 : |L12 (fun z θ => 3 * Dth (slice g τ) z θ / (1 + z)) 0| ≤ (C0 * K') * α ^ 2 := by
    refine le_trans (hL α _ hα hα1 hs3 hm3) ?_
    calc C0 * HkNorm α 4 (fun z θ => 3 * Dth (slice g τ) z θ / (1 + z))
        ≤ C0 * (K' * α ^ 2) := mul_le_mul_of_nonneg_left h3 hC0.le
      _ = (C0 * K') * α ^ 2 := by ring
  have hmu : muDyn α Φ g τ
      = (1 / (2 * α)) * (L12 (N0 α (Ftau α g τ) (slice g τ)) 0
            + L12 (N α (Ftau α g τ) (slice Φ τ)) 0)
          + (1 / (2 * α)) * L12 (fun z θ => 3 * Dth (slice g τ) z θ / (1 + z)) 0 := rfl
  rw [hmu]
  have hmain := mu_arith_H4 hα b1 b2 b3
  calc |(1 / (2 * α)) * (L12 (N0 α (Ftau α g τ) (slice g τ)) 0
          + L12 (N α (Ftau α g τ) (slice Φ τ)) 0)
        + (1 / (2 * α)) * L12 (fun z θ => 3 * Dth (slice g τ) z θ / (1 + z)) 0|
      ≤ 2 * (C0 * K') * α := hmain
    _ = 2 * C0 * K' * α := by ring

/-! ## The usable consequence: `|muDyn| ≤ 1/2` -/

/-- **`muDyn_le_half`**: the modulation is below `1/2` for `α` small and `K ≤ 1`, which is the
hypothesis `hμ` of `physClock_of_dyn`. -/
theorem muDyn_le_half : ∃ α₀ : ℝ, 0 < α₀ ∧
    ∀ (α : ℝ) (Φ g : Fam) (τ K : ℝ), 0 < α → α ≤ α₀ → 0 ≤ K → K ≤ 1 →
      HkNorm α 4 (slice g τ) ≤ K * α ^ 2 →
      |L12 (N0 α (Ftau α g τ) (slice g τ)) 0|
          ≤ α ^ 2 + α * HkNorm α 4 (slice g τ)
            + α ^ (-(1 / 2 : ℝ)) * HkNorm α 4 (slice g τ) ^ 2 →
      |L12 (N α (Ftau α g τ) (slice Φ τ)) 0|
          ≤ α ^ 2 + α * HkNorm α 4 (slice g τ)
            + α ^ (-(1 / 2 : ℝ)) * HkNorm α 4 (slice g τ) ^ 2 →
      |L12 (fun z θ => 3 * Dth (slice g τ) z θ / (1 + z)) 0| ≤ HkNorm α 4 (slice g τ) →
      |muDyn α Φ g τ| ≤ 1 / 2 := by
  obtain ⟨C, hC, hsmall⟩ := muDyn_small
  refine ⟨min 1 (1 / (6 * C)), lt_min one_pos (by positivity), ?_⟩
  intro α Φ g τ K hα hα0 hK hK1 hX h1 h2 h3
  have hα1 : α ≤ 1 := le_trans hα0 (min_le_left _ _)
  have hα6 : α ≤ 1 / (6 * C) := le_trans hα0 (min_le_right _ _)
  have h := hsmall α Φ g τ K hα hα1 hK hX h1 h2 h3
  have hKsum : 1 + K + K ^ 2 ≤ 3 := by nlinarith
  have hαC : α * (6 * C) ≤ 1 := by
    have h6C : 0 < 6 * C := by positivity
    have h := mul_le_mul_of_nonneg_right hα6 (le_of_lt h6C)
    have h2 : (1 / (6 * C)) * (6 * C) = 1 := by field_simp
    rw [h2] at h
    exact h
  have hstep1 : C * (1 + K + K ^ 2) ≤ C * 3 := mul_le_mul_of_nonneg_left hKsum hC.le
  have hstep2 : C * (1 + K + K ^ 2) * α ≤ C * 3 * α :=
    mul_le_mul_of_nonneg_right hstep1 hα.le
  have hstep3 : C * 3 * α ≤ 1 / 2 := by
    have : 6 * C * α ≤ 1 := by linarith [hαC]
    linarith
  linarith [h, hstep2, hstep3]

end Work.FTS.FinalClock
