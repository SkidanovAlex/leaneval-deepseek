import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.H6Pair6Aux.T6Fix

open scoped Real Topology

set_option maxHeartbeats 800000

/-!
## The `sin(2θ)`-gain for angular derivatives, from a flat `∂_θ`-datum

This file proves

`|D_z^b D_θ^a A| ≤ C · K_f · sin(2θ)`  (`1 ≤ a`, `a + b ≤ 2`)

for a source `A` that is `C^∞` on the open quadrant `(0,∞) × (0,π/2)`, where `K_f` bounds
only the *first-order* mixed derivatives of `∂_θA = pth A` (`b + i ≤ 1`).

The mechanism is completely elementary: `D_θ` carries the factor `sin(2θ)` and `D_z` does
not differentiate in `θ`, so

* `D_z^b D_θ A = sin(2θ) · D_z^b (∂_θA)` (`mixed_one_eq`), controlled by `mixed b 0 (pth A)`;
* `D_θ² A = sin(2θ) · ∂_θ(D_θA)`, and the product rule for `D_θ A = sin(2θ)·∂_θA` gives
  `∂_θ(D_θA) = 2cos(2θ)·∂_θA + D_θ(∂_θA)` (`pth_Dth_eq`), controlled by `mixed 0 0 (pth A)`
  and `mixed 0 1 (pth A)`.

No boundedness of `A` itself, and no `z`-differentiability, is needed in the second factor.
-/

/-! ## Pulling a `z`-independent factor through the radial operators -/

/-- A factor which does not depend on `z` passes through `∂_z`. -/
theorem pz_const_mul (c : ℝ → ℝ) (K : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pz (fun z θ => c θ * K z θ) z θ = c θ * Work.Spaces.pz K z θ :=
  deriv_const_mul_field (c θ)

/-- A factor which does not depend on `z` passes through `D_z^j`. -/
theorem dzIter_const_mul (c : ℝ → ℝ) (K : ℝ → ℝ → ℝ) (j : ℕ) (z θ : ℝ) :
    Work.Spaces.DzIter j (fun z θ => c θ * K z θ) z θ
      = c θ * Work.Spaces.DzIter j K z θ := by
  induction j generalizing z θ with
  | zero => rfl
  | succ j ih =>
    rw [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.DzIter_succ, Work.Spaces.Dz]
    have heq : Work.Spaces.DzIter j (fun z θ => c θ * K z θ)
        = fun z θ => c θ * Work.Spaces.DzIter j K z θ :=
      funext fun z => funext fun θ => ih z θ
    rw [heq, pz_const_mul]
    ring

/-! ## The explicit `sin(2θ)` factor in the mixed derivatives -/

/-- `D_z^j D_θ A = sin(2θ) · D_z^j(∂_θA)`. -/
theorem mixed_one_eq (g : ℝ → ℝ → ℝ) (j : ℕ) (z θ : ℝ) :
    Work.Spaces.mixed j 1 g z θ
      = Real.sin (2 * θ) * Work.Spaces.DzIter j (Work.Spaces.pth g) z θ := by
  have h : Work.Spaces.mixed j 1 g = Work.Spaces.DzIter j (Work.Spaces.Dth g) := rfl
  rw [h]
  exact dzIter_const_mul (fun θ => Real.sin (2 * θ)) (Work.Spaces.pth g) j z θ

/-- `D_z^j D_θ² A = sin(2θ) · D_z^j(∂_θ(D_θA))`. -/
theorem mixed_two_eq (g : ℝ → ℝ → ℝ) (j : ℕ) (z θ : ℝ) :
    Work.Spaces.mixed j 2 g z θ
      = Real.sin (2 * θ)
        * Work.Spaces.DzIter j (Work.Spaces.pth (Work.Spaces.Dth g)) z θ := by
  have h : Work.Spaces.mixed j 2 g
      = Work.Spaces.DzIter j (Work.Spaces.Dth (Work.Spaces.Dth g)) := rfl
  rw [h]
  exact dzIter_const_mul (fun θ => Real.sin (2 * θ))
    (Work.Spaces.pth (Work.Spaces.Dth g)) j z θ

/-- The `j = 0` instance: `D_θ A = sin(2θ) · ∂_θA`. -/
theorem mixed_zero_one_eq (g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.mixed 0 1 g z θ = Real.sin (2 * θ) * Work.Spaces.pth g z θ := by
  have h := mixed_one_eq g 0 z θ
  simpa only [Work.Spaces.DzIter_zero] using h

/-- The `j = 0` instance: `D_θ² A = sin(2θ) · ∂_θ(D_θA)`. -/
theorem mixed_zero_two_eq (g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.mixed 0 2 g z θ
      = Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.Dth g) z θ := by
  have h := mixed_two_eq g 0 z θ
  simpa only [Work.Spaces.DzIter_zero] using h

/-! ## The `θ`-slice derivative and the product rule for `D_θ` -/

/-- The `θ`-slice of a function `C^∞` on the open quadrant, differentiated. -/
theorem hasDerivAt_slice_theta {F : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen F)
    {z : ℝ} (hz : 0 < z) {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    HasDerivAt (fun θ' : ℝ => F z θ') (Work.Spaces.pth F z θ) θ := by
  have hne : Work.Stability.smoothOrder ≠ 0 := by decide
  have hd : DifferentiableOn ℝ (fun θ' : ℝ => F z θ') (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (hF.curry_θ hz).differentiableOn hne
  exact (hd.differentiableAt (isOpen_Ioo.mem_nhds hθ)).hasDerivAt

/-- The product rule for `D_θ = sin(2θ)∂_θ`: on the open quadrant,
`∂_θ(D_θA) = 2cos(2θ)·∂_θA + D_θ(∂_θA)`. -/
theorem pth_Dth_eq {A : ℝ → ℝ → ℝ} (hA : Work.FTS.EllipticEst.SmoothOpen A)
    {z θ : ℝ} (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < Real.pi / 2) :
    Work.Spaces.pth (Work.Spaces.Dth A) z θ
      = 2 * Real.cos (2 * θ) * Work.Spaces.pth A z θ
        + Work.Spaces.Dth (Work.Spaces.pth A) z θ := by
  have hmem : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ, hθ2⟩
  have hsin : HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ')) (2 * Real.cos (2 * θ)) θ := by
    have h1 : HasDerivAt (fun θ' : ℝ => 2 * θ') 2 θ := by
      simpa using (hasDerivAt_id (𝕜 := ℝ) θ).const_mul (2 : ℝ)
    have h2 := (Real.hasDerivAt_sin (2 * θ)).comp θ h1
    have h3 : Real.cos (2 * θ) * 2 = 2 * Real.cos (2 * θ) := by ring
    rw [h3] at h2
    exact h2
  have h2 : HasDerivAt (fun θ' : ℝ => Work.Spaces.pth A z θ')
      (Work.Spaces.pth (Work.Spaces.pth A) z θ) θ :=
    hasDerivAt_slice_theta hA.pth hz hmem
  have hprod := hsin.mul h2
  have hpth : Work.Spaces.pth (Work.Spaces.Dth A) z θ
      = 2 * Real.cos (2 * θ) * Work.Spaces.pth A z θ
        + Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.pth A) z θ :=
    hprod.deriv
  rw [hpth]
  rfl

/-! ## The main statement -/

theorem mixed_sinGain_of_pthFlat : ∃ C : ℝ, 0 < C ∧ ∀ (A : ℝ → ℝ → ℝ) (Kf : ℝ),
    0 ≤ Kf → Work.FTS.EllipticEst.SmoothOpen A →
    (∀ b i : ℕ, b + i ≤ 1 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed b i (Work.Spaces.pth A) z θ| ≤ Kf) →
    ∀ (a b₁ : ℕ), 1 ≤ a → a + b₁ ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed b₁ a A z θ| ≤ C * Kf * Real.sin (2 * θ) := by
  refine ⟨4, by norm_num, ?_⟩
  intro A Kf hKf hA hB a b₁ ha hab z θ hz hθ hθ2
  have hsin : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  -- the two available point bounds on the `∂_θ`-datum
  have hb0 : |Work.Spaces.pth A z θ| ≤ Kf := hB 0 0 (by norm_num) z θ hz hθ hθ2
  have hb01 : |Work.Spaces.Dth (Work.Spaces.pth A) z θ| ≤ Kf :=
    hB 0 1 (by norm_num) z θ hz hθ hθ2
  have ha_cases : a = 1 ∨ a = 2 := by omega
  rcases ha_cases with rfl | rfl
  · -- `a = 1`: `D_z^b₁ D_θ A = sin(2θ)·D_z^b₁(∂_θA)`
    have hb1 : b₁ = 0 ∨ b₁ = 1 := by omega
    rcases hb1 with rfl | rfl
    · rw [mixed_zero_one_eq, abs_mul, abs_of_pos hsin]
      nlinarith [hb0, hKf, hsin]
    · have hD : |Work.Spaces.DzIter 1 (Work.Spaces.pth A) z θ| ≤ Kf :=
        hB 1 0 (by norm_num) z θ hz hθ hθ2
      rw [mixed_one_eq, abs_mul, abs_of_pos hsin]
      nlinarith [hD, hKf, hsin]
  · -- `a = 2` and hence `b₁ = 0`: `D_θ² A = sin(2θ)·∂_θ(D_θA)`
    have hb1 : b₁ = 0 := by omega
    subst b₁
    rw [mixed_zero_two_eq, abs_mul, abs_of_pos hsin]
    have hpd := pth_Dth_eq hA hz hθ hθ2
    have h3 : |Work.Spaces.pth (Work.Spaces.Dth A) z θ| ≤ 3 * Kf := by
      rw [hpd]
      have h1 : |2 * Real.cos (2 * θ) * Work.Spaces.pth A z θ|
          = |2 * Real.cos (2 * θ)| * |Work.Spaces.pth A z θ| := by rw [abs_mul]
      have hc : |2 * Real.cos (2 * θ)| ≤ 2 := by
        rw [abs_mul, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
        linarith [Real.abs_cos_le_one (2 * θ)]
      have hAB : |2 * Real.cos (2 * θ)| * |Work.Spaces.pth A z θ| ≤ 2 * Kf :=
        mul_le_mul hc hb0 (abs_nonneg _) (by norm_num)
      calc |2 * Real.cos (2 * θ) * Work.Spaces.pth A z θ
              + Work.Spaces.Dth (Work.Spaces.pth A) z θ|
          ≤ |2 * Real.cos (2 * θ) * Work.Spaces.pth A z θ|
              + |Work.Spaces.Dth (Work.Spaces.pth A) z θ| := abs_add_le _ _
        _ = |2 * Real.cos (2 * θ)| * |Work.Spaces.pth A z θ|
              + |Work.Spaces.Dth (Work.Spaces.pth A) z θ| := by rw [h1]
        _ ≤ 2 * Kf + Kf := add_le_add hAB hb01
        _ = 3 * Kf := by ring
    nlinarith [h3, hKf, hsin]

end Work.H6Pair6Aux.T6Fix
