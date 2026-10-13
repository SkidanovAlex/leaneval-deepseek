import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TotallySplit
import Submission.Work.FTS_EllLimOK.RulingELF
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.GalBasis.GalApprox.pzIter_pthIter_comm

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.ProducerH.H2

set_option autoImplicit false

/-! ## Elementary helpers for `bounds_rates`

The proof reduces every conjunct to one of three inputs:

* the radial rate `psiDz_rate` (`|D_z^j (E g)| ≤ C·𝓧·min θ (π/2-θ)`, `j ≤ 2`), which gives the
  plain `∂_z`-bounds after dividing by `z ≥ a₀`;
* the *plain* second angular derivatives `second_theta_deriv_le_Xn6` (`|∂_θ² (E g)| ≤ K·𝓧`) and
  `second_theta_deriv_DzIter_le_Xn6` (`|∂_θ² (D_z^a (E g))| ≤ K·𝓧`, `a ≤ 2`), which bound the
  angular derivatives of the mixed quantities; the mixed quantities themselves are then obtained
  from their value at the midpoint `θ = π/4` (where `sin 2θ = 1`) by the interpolation inequality
  `slice_interp`;
* the value at `θ = π/4`, where the normalised mixed jets `D_z^j D_θ^i` of `mixed_jets_le_Xn6`
  control the plain derivatives.
-/

/-- The midpoint `π/4` of the angular interval. -/
theorem br_quarter_mem : (π / 4 : ℝ) ∈ Set.Ioo (0 : ℝ) (π / 2) :=
  ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩

/-- `|a - b| ≤ |a| + |b|`. -/
theorem br_abs_sub_le_abs_add_abs (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  rw [abs_sub_le_iff]
  constructor <;> linarith [le_abs_self a, neg_le_abs a, le_abs_self b, neg_le_abs b]

/-- `sin (2·(π/4)) = 1`. -/
theorem br_sin_two_quarter : Real.sin (2 * (π / 4)) = 1 := by
  rw [show 2 * (π / 4) = π / 2 from by ring, Real.sin_pi_div_two]

/-- `D_z^j (D_θ f) = sin(2θ) · D_z^j (∂_θ f)`: the angular normalisation commutes with the
radial iterates. -/
theorem br_dzIter_dth_eq (f : ℝ → ℝ → ℝ) (j : ℕ) :
    Work.Spaces.DzIter j (Work.Spaces.Dth f)
      = fun z θ => Real.sin (2 * θ) * Work.Spaces.DzIter j (Work.Spaces.pth f) z θ := by
  induction j with
  | zero => rfl
  | succ k ih =>
      funext z θ
      show z * deriv (fun z' => Work.Spaces.DzIter k (Work.Spaces.Dth f) z' θ) z
        = Real.sin (2 * θ)
            * (z * deriv (fun z' => Work.Spaces.DzIter k (Work.Spaces.pth f) z' θ) z)
      have hfun : (fun z' => Work.Spaces.DzIter k (Work.Spaces.Dth f) z' θ)
          = fun z' => Real.sin (2 * θ) * Work.Spaces.DzIter k (Work.Spaces.pth f) z' θ := by
        funext z'
        exact congrFun (congrFun ih z') θ
      rw [hfun, deriv_const_mul_field]
      ring

/-- At the midpoint, the normalised mixed jet `D_z^j D_θ f` is the plain iterate
`D_z^j (∂_θ f)`. -/
theorem br_mixed_quarter_eq (f : ℝ → ℝ → ℝ) (j : ℕ) (z : ℝ) :
    Work.Spaces.mixed j 1 f z (π / 4) = Work.Spaces.DzIter j (Work.Spaces.pth f) z (π / 4) := by
  have h := congrFun (congrFun (br_dzIter_dth_eq f j) z) (π / 4)
  rw [br_sin_two_quarter, one_mul] at h
  exact h

/-- At the midpoint, the plain angular derivative is the normalised one. -/
theorem br_pth_quarter_eq (f : ℝ → ℝ → ℝ) (z : ℝ) :
    Work.Spaces.pth f z (π / 4) = Work.Spaces.mixed 0 1 f z (π / 4) := by
  show Work.Spaces.pth f z (π / 4)
    = Real.sin (2 * (π / 4)) * Work.Spaces.pth f z (π / 4)
  rw [br_sin_two_quarter, one_mul]

/-- The interpolation inequality: a function on `(0,π/2)` whose derivative is bounded by `C` is
bounded by its value at `π/4` plus `C·(π/2)`. -/
theorem br_slice_interp {f : ℝ → ℝ} {C : ℝ}
    (hd : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), DifferentiableAt ℝ f θ)
    (hb : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), |deriv f θ| ≤ C)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    |f θ| ≤ |f (π / 4)| + C * (π / 2) := by
  have hq : (π / 4 : ℝ) ∈ Set.Ioo (0 : ℝ) (π / 2) := br_quarter_mem
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hb (π / 4) hq)
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (s := Set.Ioo (0 : ℝ) (π / 2))
    hd hb (convex_Ioo 0 (π / 2)) hθ hq
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at h
  have hdist : |π / 4 - θ| ≤ π / 2 := by
    rw [abs_le]; constructor <;> linarith [hθ.1, hθ.2, Real.pi_pos]
  have h5 : |f θ - f (π / 4)| ≤ C * (π / 2) := by
    have h5' : |f (π / 4) - f θ| ≤ C * (π / 2) :=
      le_trans h (mul_le_mul_of_nonneg_left hdist hC0)
    rwa [abs_sub_comm] at h5'
  have hsplit : f θ = (f θ - f (π / 4)) + f (π / 4) := by ring
  calc |f θ| = |(f θ - f (π / 4)) + f (π / 4)| := by conv_lhs => rw [hsplit]
    _ ≤ |f θ - f (π / 4)| + |f (π / 4)| := abs_add_le _ _
    _ ≤ C * (π / 2) + |f (π / 4)| := by linarith
    _ = |f (π / 4)| + C * (π / 2) := by ring

/-- `∂_θ²` of `θ ↦ c·h(z,θ)` (`c` independent of `θ`). -/
theorem br_deriv_deriv_const_mul (c z θ : ℝ) (h : ℝ → ℝ → ℝ) :
    deriv (deriv (fun θ' => c * h z θ')) θ = c * deriv (deriv (fun θ' => h z θ')) θ := by
  have h1 : ∀ x : ℝ, deriv (fun θ' => c * h z θ') x = c * deriv (fun θ' => h z θ') x :=
    fun x => deriv_const_mul_field (v := fun θ' => h z θ') (x := x) c
  show deriv (fun θ' => deriv (fun θ'' => c * h z θ'') θ') θ
    = c * deriv (fun θ' => deriv (fun θ'' => h z θ'') θ') θ
  rw [show (fun θ' => deriv (fun θ'' => c * h z θ'') θ')
      = fun θ' => c * deriv (fun θ'' => h z θ'') θ' from funext h1]
  exact deriv_const_mul_field (v := fun θ' => deriv (fun θ'' => h z θ'') θ') (x := θ) c

/-- Second-order congruence of the slice derivatives on the open interval. -/
theorem br_deriv_deriv_congr_slice {F G : ℝ → ℝ} {θ : ℝ}
    (h : ∀ θ' ∈ Set.Ioo (0 : ℝ) (π / 2), F θ' = G θ')
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) : deriv (deriv F) θ = deriv (deriv G) θ := by
  have h1 : deriv F =ᶠ[𝓝 θ] deriv G := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
    exact Filter.EventuallyEq.deriv_eq (Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hθ') h)
  exact Filter.EventuallyEq.deriv_eq h1

/-- First-order congruence of the slice derivatives on the open interval. -/
theorem br_deriv_congr_slice {F G : ℝ → ℝ} {θ : ℝ}
    (h : ∀ θ' ∈ Set.Ioo (0 : ℝ) (π / 2), F θ' = G θ')
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) : deriv F θ = deriv G θ :=
  Filter.EventuallyEq.deriv_eq (Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hθ) h)

/-- Clairaut for the plain slice derivatives, in the open-quadrant class. -/
theorem br_pz_pth_eq_of_smoothOpen {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    Work.Spaces.pz (Work.Spaces.pth f) z θ = Work.Spaces.pth (Work.Spaces.pz f) z θ := by
  have hmem : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩
  have h2 : ContDiffAt ℝ 2 (Function.uncurry f) (z, θ) :=
    (hf.contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hmem)).of_le
      (by simp [Work.Stability.smoothOrder])
  exact Work.FTS.GalBasis.GalApprox.pzIter_pthIter_comm h2 1 1 (by norm_num)

/-- Clairaut at the second radial order. -/
theorem br_pzIter_two_pth_comm_of_smoothOpen {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    Work.Spaces.pzIter 2 (Work.Spaces.pth f) z θ
      = Work.Spaces.pth (Work.Spaces.pzIter 2 f) z θ := by
  have hmem : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩
  have h3 : ContDiffAt ℝ 3 (Function.uncurry f) (z, θ) :=
    (hf.contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hmem)).of_le
      (by simp [Work.Stability.smoothOrder])
  exact Work.FTS.GalBasis.GalApprox.pzIter_pthIter_comm h3 2 1 (by norm_num)

/-- The comparison `x ≤ A / c` from `z·x ≤ A`, for `0 < c ≤ z`. -/
theorem br_le_div_const {x A z c : ℝ} (hz : 0 < z) (hA : 0 ≤ A) (hc : 0 < c) (hcz : c ≤ z)
    (h : z * x ≤ A) : x ≤ A / c := by
  have hx : x ≤ A / z := by
    rw [le_div_iff₀ hz]
    calc x * z = z * x := by ring
      _ ≤ A := h
  rw [le_div_iff₀ hc]
  calc x * c ≤ (A / z) * c := mul_le_mul_of_nonneg_right hx hc.le
    _ = A * c / z := by ring
    _ ≤ A * z / z := by
        apply div_le_div_of_nonneg_right _ hz.le
        exact mul_le_mul_of_nonneg_left hcz hA
    _ = A := by field_simp

/-- Squeezing a bound `a ≤ A·𝓧·f₀` into `a ≤ C·𝓧·f₁`. -/
theorem br_squeeze_rate {a A C X f₀ f₁ : ℝ} (h : a ≤ A * X * f₀) (hA0 : 0 ≤ A)
    (hA : A ≤ C) (hX : 0 ≤ X) (hf₀ : 0 ≤ f₀) (hf : f₀ ≤ f₁) : a ≤ C * X * f₁ := by
  have hC0 : 0 ≤ C := le_trans hA0 hA
  calc a ≤ A * X * f₀ := h
    _ ≤ C * X * f₀ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hA hX) hf₀
    _ ≤ C * X * f₁ := mul_le_mul_of_nonneg_left hf (mul_nonneg hC0 hX)

/-- Squeezing a bound `a ≤ A·𝓧` into `a ≤ C·𝓧`. -/
theorem br_squeeze_plain {a A C X : ℝ} (h : a ≤ A * X) (hA0 : 0 ≤ A) (hA : A ≤ C)
    (hX : 0 ≤ X) : a ≤ C * X := le_trans h (mul_le_mul_of_nonneg_right hA hX)


end Work.FTS_EllLimOK.ProducerH.H2
