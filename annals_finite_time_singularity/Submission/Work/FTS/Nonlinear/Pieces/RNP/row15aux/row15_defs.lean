import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.Gam_bounds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Bookkeeping vocabulary for row 15 (`N₂^{ss}`)

If at some `z > 0` the mixed derivatives of `f` satisfy the pointwise bound

`|D_z^j D_θ^i f(z,θ)·w(z)| ≤ K·α³·(Cs+1)·Γ(θ)·(1+log(1+z))/(1+z)`   (`i + j ≤ 4`),

then each of the fifteen terms of `HkIntegrand α 4 f z θ` is bounded by the square of
that quantity times an angular weight.  Collecting the terms gives

`HkIntegrand α 4 f z θ ≤ (K·α³·(Cs+1))² · rlog(z)² · Gwt α θ`,

with `rlog` and `Gwt` as defined below, and the whole point of the row-15 bookkeeping is
that both factors are integrable with explicit constants (`∫_z rlog² ≤ 100`,
`∫_θ Gwt ≤ 2000/α`), so that `HkSq α 4 f ≤ 10¹²·K²·(Cs+1)²·α⁴`.

The two remaining ingredients (`HkIntegrand_le_of_mixed_bound`, the θ-integral and the
z-integral of the two weights) are proved in the sibling modules; this file only fixes the
vocabulary they share.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.RNP.row15aux

set_option autoImplicit false

/-- The radial bookkeeping weight `z ↦ (1 + log(1+z))/(1+z)` of the row-15 pointwise bound.
It is nonnegative for `z ≥ 0` and its square integrates to at most `100` over `[0,∞)`. -/
def rlog (z : ℝ) : ℝ := (1 + Real.log (1 + z)) / (1 + z)

@[simp] theorem rlog_def (z : ℝ) : rlog z = (1 + Real.log (1 + z)) / (1 + z) := rfl

/-- The angular bookkeeping weight of the row-15 pointwise bound: `Γ(θ)²` times the two
angular weights `sin(2θ)^{-η}` (for the pure `D_z`-terms, coefficient `5`, one for each
`i ≤ 4`) and `sin(2θ)^{-γ}` (for the mixed terms, coefficient `30 ≥ 25`, one for each of
the at most `25` pairs `(i,j)` of the double sum). -/
def Gwt (α θ : ℝ) : ℝ :=
  (Work.Spaces.Gam α θ) ^ 2 *
    (5 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)
      + 30 * (Real.sin (2 * θ)) ^ (-Work.Spaces.gam α))

theorem Gwt_nonneg {α θ : ℝ} (hα : 0 < α) (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Gwt α θ := by
  have hs : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have hG : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
  have h1 : 0 ≤ 5 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta) :=
    mul_nonneg (by norm_num) (Real.rpow_nonneg hs _)
  have h2 : 0 ≤ 30 * (Real.sin (2 * θ)) ^ (-Work.Spaces.gam α) :=
    mul_nonneg (by norm_num) (Real.rpow_nonneg hs _)
  have h3 : 0 ≤ (Work.Spaces.Gam α θ) ^ 2 := sq_nonneg _
  rw [Gwt]
  exact mul_nonneg h3 (add_nonneg h1 h2)

/-- `rlog` is nonnegative on `[0,∞)`. -/
theorem rlog_nonneg {z : ℝ} (hz : 0 ≤ z) : 0 ≤ rlog z := by
  rw [rlog_def]
  have h1 : (0 : ℝ) < 1 + z := by linarith
  have h2 : 0 ≤ Real.log (1 + z) := Real.log_nonneg (by linarith)
  positivity

/-- `Γ(θ) ≤ sin(2θ)^{α/5}` on `Iθ` for `α > 0`.  This is the angular weight estimate
that turns `Γ(θ)²·sin(2θ)^{-q}` into the single `rpow` weight `sin(2θ)^{2α/5-q}`.

It is proved inside `Work.Spaces.Gam_mul_weight_le` (as the step `hGam` of the proof of
`Gam_mul_weight_le`); we record it separately because several row-15 estimates need it. -/
theorem Gam_le_sin_two_rpow (α θ : ℝ) (hα : 0 < α) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.Gam α θ ≤ (Real.sin (2 * θ)) ^ (α / 5) := by
  obtain ⟨hθ0, hθ1⟩ := hθ
  have hs0 : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith⟩
  have hc0 : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith⟩
  have hs1 : Real.sin θ ≤ 1 := Real.sin_le_one θ
  have hc1 : Real.cos θ ≤ 1 := Real.cos_le_one θ
  set A : ℝ := Real.sin θ * Real.cos θ ^ 2 with hA
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hGamA : Work.Spaces.Gam α θ = A ^ (α / 3) := by
    simp only [Work.Spaces.Gam]
    rw [hA]
  have he0 : 0 ≤ Real.sin (2 * θ) := by rw [Real.sin_two_mul]; positivity
  have hA5r : A ^ (5:ℝ) ≤ (Real.sin (2 * θ)) ^ (3:ℝ) := by
    have hm : A ^ 5 ≤ (Real.sin (2 * θ)) ^ 3 := by
      rw [hA, Real.sin_two_mul]
      have h1 : (Real.sin θ) ^ 2 * (Real.cos θ) ^ 7 ≤ 1 := by
        have a : (Real.sin θ) ^ 2 ≤ 1 := pow_le_one₀ (n := 2) hs0 hs1
        have b : (Real.cos θ) ^ 7 ≤ 1 := pow_le_one₀ (n := 7) hc0 hc1
        nlinarith [mul_le_mul a b (pow_nonneg hc0 7) (by norm_num : (0:ℝ) ≤ 1)]
      have hQ : 0 ≤ (Real.sin θ) ^ 3 * (Real.cos θ) ^ 3 := by positivity
      have step : ((Real.sin θ) ^ 2 * (Real.cos θ) ^ 7) * ((Real.sin θ) ^ 3 * (Real.cos θ) ^ 3)
          ≤ 1 * ((Real.sin θ) ^ 3 * (Real.cos θ) ^ 3) :=
        mul_le_mul_of_nonneg_right h1 hQ
      nlinarith [step, hQ, sq_nonneg (Real.sin θ * Real.cos θ)]
    simpa using hm
  have h1 : A ^ (α / 3) = (A ^ (5:ℝ)) ^ (α / 15) := by
    rw [← Real.rpow_mul hA0 5 (α / 15), show (5:ℝ) * (α / 15) = α / 3 by ring]
  have h2 : ((Real.sin (2 * θ)) ^ (3:ℝ)) ^ (α / 15) = (Real.sin (2 * θ)) ^ (α / 5) := by
    rw [← Real.rpow_mul he0 3 (α / 15), show (3:ℝ) * (α / 15) = α / 5 by ring]
  have h3 : (A ^ (5:ℝ)) ^ (α / 15) ≤ ((Real.sin (2 * θ)) ^ (3:ℝ)) ^ (α / 15) :=
    Real.rpow_le_rpow (Real.rpow_nonneg hA0 5) hA5r (by linarith)
  rw [← h1, h2] at h3
  rwa [hGamA]

/-- The squared form of `Gam_le_sin_two_rpow`, on the open interval (where `sin 2θ > 0`,
so that the `rpow` algebra is clean): `Γ(θ)²·sin(2θ)^{-q} ≤ sin(2θ)^{2α/5 - q}`
whenever `2α/5 ≤ q`. -/
theorem Gam_sq_mul_sin_rpow_le {α θ q : ℝ} (hα : 0 < α) (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2))
    (hq : 2 * α / 5 ≤ q) :
    (Work.Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)
      ≤ (Real.sin (2 * θ)) ^ (2 * α / 5 - q) := by
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hs : 0 < Real.sin (2 * θ) := by
    rw [Real.sin_two_mul]
    have h1 : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
    have h2 : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩
    positivity
  have hGam : Work.Spaces.Gam α θ ≤ (Real.sin (2 * θ)) ^ (α / 5) :=
    Gam_le_sin_two_rpow α θ hα hθI
  have hGam0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθI).1
  have hsq : (Work.Spaces.Gam α θ) ^ 2 ≤ ((Real.sin (2 * θ)) ^ (α / 5)) ^ 2 :=
    by simpa using pow_le_pow_left₀ hGam0 hGam 2
  have hsq' : ((Real.sin (2 * θ)) ^ (α / 5)) ^ 2 = (Real.sin (2 * θ)) ^ (2 * α / 5) := by
    rw [← Real.rpow_natCast ((Real.sin (2 * θ)) ^ (α / 5)) 2,
      ← Real.rpow_mul (le_of_lt hs) (α / 5) ((2 : ℕ) : ℝ),
      show (α / 5) * ((2 : ℕ) : ℝ) = 2 * α / 5 by push_cast; ring]
  rw [hsq'] at hsq
  have hneg : 0 ≤ (Real.sin (2 * θ)) ^ (-q) := Real.rpow_nonneg (le_of_lt hs) _
  calc (Work.Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)
      ≤ (Real.sin (2 * θ)) ^ (2 * α / 5) * (Real.sin (2 * θ)) ^ (-q) :=
        mul_le_mul_of_nonneg_right hsq hneg
    _ = (Real.sin (2 * θ)) ^ (2 * α / 5 + (-q)) :=
        (Real.rpow_add hs (2 * α / 5) (-q)).symm
    _ = (Real.sin (2 * θ)) ^ (2 * α / 5 - q) := by ring_nf

end Work.FTS.Nonlinear.Pieces.RNP.row15aux
