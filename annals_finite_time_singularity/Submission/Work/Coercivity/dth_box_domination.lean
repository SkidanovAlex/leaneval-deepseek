/-
# Pointwise domination of the `D_θ f`-box terms

The estimate `thetaDerivative` of §"Linearization with angular transport" needs, for
every point `(z,θ)` of the box `(0,R) × [0,π/2]`, pointwise control of the four products

`L(D_θf)·D_θf·w²·sin(2θ)^{-γ}`,   `(3/(1+z))·sin(2θ)^{-γ}·D_θ(D_θf)·D_θf`,
`(D_θf)²·w²·sin(2θ)^{-γ}`,        `sin(2θ)^{-γ}·(D_θf)²`

by a single multiple of `(1+z)⁴`.  The pointwise input is exactly the box bound on the
first two angular/radial derivatives of `f`, namely

`|∂_θ f| ≤ C z²`,  `|∂_z ∂_θ f| ≤ C z`,  `|∂_θ² f| ≤ C`   on `(0,R) × [0,π/2]`.

The mathematics is elementary: `D_θ f = sin(2θ)·∂_θ f` supplies a factor `sin(2θ)` which
tames the singular weight `sin(2θ)^{-γ}` (`0 < γ = 1+α/10 ≤ 1.1`, so
`sin(2θ)^{-γ}·sin(2θ)² = sin(2θ)^{2-γ} ≤ 1`), while `w(z)²·z⁴ = (1+z)⁴` cancels the
singularity of the radial weight `w = (1+z)²/z²`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.GDelta.MetrizableSpace
import Submission.Work.Coercivity.thetaAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-! ## Elementary analytic helpers -/

/-- **Weight bound.**  For `s ∈ [0,1]` and `0 < γ ≤ 2` one has `s^{-γ}·s² ≤ 1`; the
factor `s²` kills the singularity of `s^{-γ}` at `s = 0`. -/
theorem rpow_neg_mul_sq_le_one {s γ : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hγ0 : 0 < γ)
    (hγ2 : γ ≤ 2) : s ^ (-γ) * s ^ 2 ≤ 1 := by
  rcases eq_or_lt_of_le hs0 with h | h
  · subst h
    rw [Real.zero_rpow (by linarith : -γ ≠ 0)]
    norm_num
  · have h2 : s ^ 2 = s ^ ((2 : ℕ) : ℝ) := (Real.rpow_natCast s 2).symm
    rw [h2, ← Real.rpow_add h (-γ) ((2 : ℕ) : ℝ)]
    rw [show -γ + ((2 : ℕ) : ℝ) = 2 - γ by push_cast; ring]
    exact Real.rpow_le_one (le_of_lt h) hs1 (by linarith)

/-- **The radial weight identity.**  `z⁴·w(z)² = (1+z)⁴` for `z ≠ 0`, where
`w(z) = (1+z)²/z²`.  This is the cancellation that makes `w²` harmless on the box. -/
theorem z4_mul_w_sq (z : ℝ) (hz : z ≠ 0) : z ^ 4 * Spaces.w z ^ 2 = (1 + z) ^ 4 := by
  rw [Spaces.w]
  field_simp

/-- **Derivative of `sin(2·)·g`.**  Away from the zeros of `sin(2·)` the derivative of
`t ↦ sin(2t) g t` is bounded by `2|g θ| + |deriv g θ|`, with *no* differentiability
hypothesis on `g`: if `g` is differentiable at `θ` this is the product rule together
with `|sin|,|cos| ≤ 1`, while if `g` is not differentiable at `θ` then neither is the
product (since `sin(2·)` is nonzero and continuous near `θ`), so its `deriv` is `0`. -/
theorem sin_two_mul_deriv_bound (g : ℝ → ℝ) {θ : ℝ} (hsin : Real.sin (2 * θ) ≠ 0) :
    |deriv (fun t : ℝ => Real.sin (2 * t) * g t) θ| ≤ 2 * |g θ| + |deriv g θ| := by
  by_cases hg : DifferentiableAt ℝ g θ
  · have h1 : HasDerivAt (fun t : ℝ => 2 * t) (2 : ℝ) θ := by
      simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
    have hsin_d : HasDerivAt (fun t : ℝ => Real.sin (2 * t)) (Real.cos (2 * θ) * 2) θ :=
      h1.sin
    have hprod : HasDerivAt (fun t : ℝ => Real.sin (2 * t) * g t)
        (Real.cos (2 * θ) * 2 * g θ + Real.sin (2 * θ) * deriv g θ) θ :=
      hsin_d.mul hg.hasDerivAt
    rw [hprod.deriv]
    have hc : |Real.cos (2 * θ)| ≤ 1 := Real.abs_cos_le_one _
    have hs : |Real.sin (2 * θ)| ≤ 1 := Real.abs_sin_le_one _
    calc |Real.cos (2 * θ) * 2 * g θ + Real.sin (2 * θ) * deriv g θ|
        ≤ |Real.cos (2 * θ) * 2 * g θ| + |Real.sin (2 * θ) * deriv g θ| := abs_add_le _ _
      _ = |Real.cos (2 * θ)| * (2 * |g θ|) + |Real.sin (2 * θ)| * |deriv g θ| := by
          rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
          ring
      _ ≤ 1 * (2 * |g θ|) + 1 * |deriv g θ| := by
          gcongr
      _ = 2 * |g θ| + |deriv g θ| := by ring
  · have hnd : ¬ DifferentiableAt ℝ (fun t : ℝ => Real.sin (2 * t) * g t) θ := by
      intro hd
      have hs : DifferentiableAt ℝ (fun t : ℝ => Real.sin (2 * t)) θ := by fun_prop
      have hdiv : DifferentiableAt ℝ
          (fun t : ℝ => Real.sin (2 * t) * g t / Real.sin (2 * t)) θ := hd.div hs hsin
      have hev : g =ᶠ[𝓝 θ] (fun t : ℝ => Real.sin (2 * t) * g t / Real.sin (2 * t)) := by
        have hcont : ContinuousAt (fun t : ℝ => Real.sin (2 * t)) θ := by fun_prop
        filter_upwards [hcont.eventually_ne hsin] with t ht
        field_simp
      exact hg (hdiv.congr_of_eventuallyEq hev)
    rw [deriv_zero_of_not_differentiableAt hnd, abs_zero]
    positivity

/-! ## The four pointwise estimates -/

/-- The first box term: `|L(D_θ f)·D_θ f·w²·sin(2θ)^{-γ}| ≤ (10C²+1)(1+z)⁴`. -/
private theorem box_L_Dth (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f : ℝ → ℝ → ℝ) (z θ C0 : ℝ)
    (hz : 0 < z) (hθ : θ ∈ Spaces.Iθ) (hC0 : 0 < C0)
    (h1 : |Spaces.pth f z θ| ≤ C0 * z ^ 2) (h2 : |Spaces.pz (Spaces.pth f) z θ| ≤ C0 * z) :
    |L (Spaces.Dth f) z θ * Spaces.Dth f z θ * Spaces.w z ^ 2
        * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))| ≤ (10 * C0 ^ 2 + 1) * (1 + z) ^ 4 := by
  have hzle : (0 : ℝ) ≤ z := le_of_lt hz
  have h1zpos : (0 : ℝ) < 1 + z := by linarith
  have h1z1 : (1 : ℝ) ≤ 1 + z := by linarith
  have hs0 : (0 : ℝ) ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hgam0 : (0 : ℝ) < Spaces.gam α := Spaces.gam_pos hα
  have hgam2 : Spaces.gam α ≤ 2 := by rw [Spaces.gam]; linarith
  have hsml : (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * (Real.sin (2 * θ)) ^ 2 ≤ 1 :=
    rpow_neg_mul_sq_le_one hs0 hs1 hgam0 hgam2
  have hsnn : (0 : ℝ) ≤ (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) := Real.rpow_nonneg hs0 _
  have h4nn : (0 : ℝ) ≤ (1 + z) ^ 4 := by positivity
  have hDth_eq : Spaces.Dth f z θ = Real.sin (2 * θ) * Spaces.pth f z θ := rfl
  have hpzDth : Spaces.pz (Spaces.Dth f) z θ
      = Real.sin (2 * θ) * Spaces.pz (Spaces.pth f) z θ :=
    deriv_const_mul_field (Real.sin (2 * θ))
  have hL : L (Spaces.Dth f) z θ
      = Real.sin (2 * θ) * (Spaces.pth f z θ + z * Spaces.pz (Spaces.pth f) z θ
          - 2 * Spaces.pth f z θ / (1 + z)) := by
    rw [L, Spaces.Dz, hpzDth, hDth_eq]
    ring
  have hbr : |Spaces.pth f z θ + z * Spaces.pz (Spaces.pth f) z θ
        - 2 * Spaces.pth f z θ / (1 + z)| ≤ 4 * (C0 * z ^ 2) := by
    have hb2 : |z * Spaces.pz (Spaces.pth f) z θ| ≤ C0 * z ^ 2 := by
      rw [abs_mul, abs_of_nonneg hzle]
      calc z * |Spaces.pz (Spaces.pth f) z θ| ≤ z * (C0 * z) :=
            mul_le_mul_of_nonneg_left h2 hzle
        _ = C0 * z ^ 2 := by ring
    have hb3 : |2 * Spaces.pth f z θ / (1 + z)| ≤ 2 * (C0 * z ^ 2) := by
      rw [abs_div, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_pos h1zpos]
      calc 2 * |Spaces.pth f z θ| / (1 + z) ≤ 2 * |Spaces.pth f z θ| :=
            div_le_self (by positivity) h1z1
        _ ≤ 2 * (C0 * z ^ 2) := by linarith [h1]
    calc |Spaces.pth f z θ + z * Spaces.pz (Spaces.pth f) z θ
            - 2 * Spaces.pth f z θ / (1 + z)|
        ≤ |Spaces.pth f z θ + z * Spaces.pz (Spaces.pth f) z θ|
            + |2 * Spaces.pth f z θ / (1 + z)| := abs_sub _ _
      _ ≤ (|Spaces.pth f z θ| + |z * Spaces.pz (Spaces.pth f) z θ|)
            + |2 * Spaces.pth f z θ / (1 + z)| := by
          linarith [abs_add_le (Spaces.pth f z θ) (z * Spaces.pz (Spaces.pth f) z θ)]
      _ ≤ (C0 * z ^ 2 + C0 * z ^ 2) + 2 * (C0 * z ^ 2) := by linarith
      _ = 4 * (C0 * z ^ 2) := by ring
  have hLb : |L (Spaces.Dth f) z θ| ≤ Real.sin (2 * θ) * (4 * (C0 * z ^ 2)) := by
    rw [hL, abs_mul, abs_of_nonneg hs0]
    exact mul_le_mul_of_nonneg_left hbr hs0
  have hDthabs : |Spaces.Dth f z θ| ≤ Real.sin (2 * θ) * (C0 * z ^ 2) := by
    rw [hDth_eq, abs_mul, abs_of_nonneg hs0]
    exact mul_le_mul_of_nonneg_left h1 hs0
  have hkey : |L (Spaces.Dth f) z θ * Spaces.Dth f z θ * Spaces.w z ^ 2
        * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))|
      = |L (Spaces.Dth f) z θ| * |Spaces.Dth f z θ| * Spaces.w z ^ 2
        * (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (Spaces.w z)), abs_of_nonneg hsnn]
  rw [hkey]
  have hstep : |L (Spaces.Dth f) z θ| * |Spaces.Dth f z θ| * Spaces.w z ^ 2
        * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))
      ≤ (Real.sin (2 * θ) * (4 * (C0 * z ^ 2))) * (Real.sin (2 * θ) * (C0 * z ^ 2))
        * Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) := by
    have hb2nn : (0 : ℝ) ≤ Real.sin (2 * θ) * (4 * (C0 * z ^ 2)) :=
      mul_nonneg hs0 (by positivity)
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (sq_nonneg (Spaces.w z))) hsnn
    exact mul_le_mul hLb hDthabs (abs_nonneg _) hb2nn
  refine le_trans hstep ?_
  have hlast : (Real.sin (2 * θ) * (4 * (C0 * z ^ 2))) * (Real.sin (2 * θ) * (C0 * z ^ 2))
        * Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))
      = ((Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * (Real.sin (2 * θ)) ^ 2)
        * (4 * C0 ^ 2) * (z ^ 4 * Spaces.w z ^ 2) := by ring
  rw [hlast, z4_mul_w_sq z (ne_of_gt hz)]
  have h4C : (0 : ℝ) ≤ 4 * C0 ^ 2 := by positivity
  have hge : 4 * C0 ^ 2 ≤ 10 * C0 ^ 2 + 1 := by nlinarith [sq_nonneg C0]
  refine le_trans ?_ (mul_le_mul_of_nonneg_right hge h4nn)
  simpa using mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hsml h4C) h4nn

/-- The third box term: `|(D_θ f)²·w²·sin(2θ)^{-γ}| ≤ (10C²+1)(1+z)⁴`. -/
private theorem box_Dth_sq_w (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f : ℝ → ℝ → ℝ) (z θ C0 : ℝ)
    (hz : 0 < z) (hθ : θ ∈ Spaces.Iθ) (_hC0 : 0 < C0)
    (h1 : |Spaces.pth f z θ| ≤ C0 * z ^ 2) :
    |(Spaces.Dth f z θ) ^ 2 * Spaces.w z ^ 2
        * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))| ≤ (10 * C0 ^ 2 + 1) * (1 + z) ^ 4 := by
  have hs0 : (0 : ℝ) ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hgam0 : (0 : ℝ) < Spaces.gam α := Spaces.gam_pos hα
  have hgam2 : Spaces.gam α ≤ 2 := by rw [Spaces.gam]; linarith
  have hsml : (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * (Real.sin (2 * θ)) ^ 2 ≤ 1 :=
    rpow_neg_mul_sq_le_one hs0 hs1 hgam0 hgam2
  have hsnn : (0 : ℝ) ≤ (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) := Real.rpow_nonneg hs0 _
  have h4nn : (0 : ℝ) ≤ (1 + z) ^ 4 := by positivity
  have hDth_eq : Spaces.Dth f z θ = Real.sin (2 * θ) * Spaces.pth f z θ := rfl
  have hsq : (Spaces.Dth f z θ) ^ 2 = Real.sin (2 * θ) ^ 2 * (Spaces.pth f z θ) ^ 2 := by
    rw [hDth_eq, mul_pow]
  have hpth_sq : (Spaces.pth f z θ) ^ 2 ≤ (C0 * z ^ 2) ^ 2 :=
    sq_le_sq' (abs_le.mp h1).1 (abs_le.mp h1).2
  have hkey : |(Spaces.Dth f z θ) ^ 2 * Spaces.w z ^ 2
        * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))|
      = (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * (Real.sin (2 * θ)) ^ 2
        * (Spaces.pth f z θ) ^ 2 * Spaces.w z ^ 2 := by
    rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (Spaces.w z)), abs_of_nonneg hsnn,
      abs_of_nonneg (sq_nonneg (Spaces.Dth f z θ)), hsq]
    ring
  rw [hkey]
  have hstep : (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * (Real.sin (2 * θ)) ^ 2
        * (Spaces.pth f z θ) ^ 2 * Spaces.w z ^ 2 ≤ 1 * (C0 * z ^ 2) ^ 2 * Spaces.w z ^ 2 := by
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg (Spaces.w z))
    exact mul_le_mul hsml hpth_sq (sq_nonneg _) (by norm_num)
  refine le_trans hstep ?_
  have he : 1 * (C0 * z ^ 2) ^ 2 * Spaces.w z ^ 2 = C0 ^ 2 * (z ^ 4 * Spaces.w z ^ 2) := by ring
  rw [he, z4_mul_w_sq z (ne_of_gt hz)]
  have hge : C0 ^ 2 ≤ 10 * C0 ^ 2 + 1 := by nlinarith [sq_nonneg C0, le_of_lt _hC0]
  exact mul_le_mul_of_nonneg_right hge h4nn

/-- The fourth box term: `|sin(2θ)^{-γ}·(D_θ f)²| ≤ (10C²+1)(1+z)⁴`. -/
private theorem box_Dth_sq (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f : ℝ → ℝ → ℝ) (z θ C0 : ℝ)
    (hz : 0 < z) (hθ : θ ∈ Spaces.Iθ) (_hC0 : 0 < C0)
    (h1 : |Spaces.pth f z θ| ≤ C0 * z ^ 2) :
    |(Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * (Spaces.Dth f z θ) ^ 2|
      ≤ (10 * C0 ^ 2 + 1) * (1 + z) ^ 4 := by
  have hzle : (0 : ℝ) ≤ z := le_of_lt hz
  have hs0 : (0 : ℝ) ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hgam0 : (0 : ℝ) < Spaces.gam α := Spaces.gam_pos hα
  have hgam2 : Spaces.gam α ≤ 2 := by rw [Spaces.gam]; linarith
  have hsml : (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * (Real.sin (2 * θ)) ^ 2 ≤ 1 :=
    rpow_neg_mul_sq_le_one hs0 hs1 hgam0 hgam2
  have hsnn : (0 : ℝ) ≤ (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) := Real.rpow_nonneg hs0 _
  have h4nn : (0 : ℝ) ≤ (1 + z) ^ 4 := by positivity
  have hDth_eq : Spaces.Dth f z θ = Real.sin (2 * θ) * Spaces.pth f z θ := rfl
  have hsq : (Spaces.Dth f z θ) ^ 2 = Real.sin (2 * θ) ^ 2 * (Spaces.pth f z θ) ^ 2 := by
    rw [hDth_eq, mul_pow]
  have hpth_sq : (Spaces.pth f z θ) ^ 2 ≤ (C0 * z ^ 2) ^ 2 :=
    sq_le_sq' (abs_le.mp h1).1 (abs_le.mp h1).2
  have hkey : |(Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * (Spaces.Dth f z θ) ^ 2|
      = (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * (Real.sin (2 * θ)) ^ 2
        * (Spaces.pth f z θ) ^ 2 := by
    rw [abs_mul, abs_of_nonneg hsnn, abs_of_nonneg (sq_nonneg (Spaces.Dth f z θ)), hsq]
    ring
  rw [hkey]
  refine le_trans (mul_le_mul hsml hpth_sq (sq_nonneg _) (by norm_num)) ?_
  have he : 1 * (C0 * z ^ 2) ^ 2 = C0 ^ 2 * z ^ 4 := by ring
  rw [he]
  have hz4le : z ^ 4 ≤ (1 + z) ^ 4 := by nlinarith [hzle, h4nn]
  have hge : C0 ^ 2 ≤ 10 * C0 ^ 2 + 1 := by nlinarith [sq_nonneg C0, le_of_lt _hC0]
  exact le_trans (mul_le_mul_of_nonneg_left hz4le (sq_nonneg C0))
    (mul_le_mul_of_nonneg_right hge h4nn)

/-- The second box term: `|(3/(1+z)) sin(2θ)^{-γ} D_θ(D_θ f)·D_θ f| ≤ (10C²+1)(1+z)⁴`. -/
private theorem box_Dth_Dth (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f : ℝ → ℝ → ℝ) (z θ C0 : ℝ)
    (hz : 0 < z) (hθ : θ ∈ Spaces.Iθ) (hC0 : 0 < C0)
    (h1 : |Spaces.pth f z θ| ≤ C0 * z ^ 2) (h3 : |Spaces.pth (Spaces.pth f) z θ| ≤ C0) :
    |(3 / (1 + z)) * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))
        * Spaces.Dth (Spaces.Dth f) z θ * Spaces.Dth f z θ|
      ≤ (10 * C0 ^ 2 + 1) * (1 + z) ^ 4 := by
  have hzle : (0 : ℝ) ≤ z := le_of_lt hz
  have h1zpos : (0 : ℝ) < 1 + z := by linarith
  have hs0 : (0 : ℝ) ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hgam0 : (0 : ℝ) < Spaces.gam α := Spaces.gam_pos hα
  have hgam2 : Spaces.gam α ≤ 2 := by rw [Spaces.gam]; linarith
  have hsml : (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * (Real.sin (2 * θ)) ^ 2 ≤ 1 :=
    rpow_neg_mul_sq_le_one hs0 hs1 hgam0 hgam2
  have hsnn : (0 : ℝ) ≤ (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) := Real.rpow_nonneg hs0 _
  have h4nn : (0 : ℝ) ≤ (1 + z) ^ 4 := by positivity
  have hDth_eq : Spaces.Dth f z θ = Real.sin (2 * θ) * Spaces.pth f z θ := rfl
  by_cases hsin : Real.sin (2 * θ) = 0
  · rw [hsin, Real.zero_rpow (by linarith [hgam0] : -(Spaces.gam α) ≠ 0)]
    have hz1 : (3 / (1 + z)) * 0 * Spaces.Dth (Spaces.Dth f) z θ * Spaces.Dth f z θ = 0 := by
      ring
    rw [hz1, abs_zero]
    positivity
  · have hder : |deriv (fun t : ℝ => Real.sin (2 * t) * Spaces.pth f z t) θ|
        ≤ 2 * |Spaces.pth f z θ| + |Spaces.pth (Spaces.pth f) z θ| :=
      sin_two_mul_deriv_bound (fun t : ℝ => Spaces.pth f z t) hsin
    have hD2 : Spaces.Dth (Spaces.Dth f) z θ
        = Real.sin (2 * θ) * deriv (fun t : ℝ => Real.sin (2 * t) * Spaces.pth f z t) θ := rfl
    have hD2b : |Spaces.Dth (Spaces.Dth f) z θ|
        ≤ Real.sin (2 * θ) * (2 * |Spaces.pth f z θ| + |Spaces.pth (Spaces.pth f) z θ|) := by
      rw [hD2, abs_mul, abs_of_nonneg hs0]
      exact mul_le_mul_of_nonneg_left hder hs0
    have hD1b : |Spaces.Dth f z θ| ≤ Real.sin (2 * θ) * |Spaces.pth f z θ| := by
      rw [hDth_eq, abs_mul, abs_of_nonneg hs0]
    have hMnn : (0 : ℝ) ≤ 2 * |Spaces.pth f z θ| + |Spaces.pth (Spaces.pth f) z θ| := by
      linarith [abs_nonneg (Spaces.pth f z θ), abs_nonneg (Spaces.pth (Spaces.pth f) z θ)]
    have hKnn : (0 : ℝ) ≤ (3 / (1 + z)) * (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) :=
      mul_nonneg (div_nonneg (by norm_num) (le_of_lt h1zpos)) hsnn
    have hkey : |(3 / (1 + z)) * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))
          * Spaces.Dth (Spaces.Dth f) z θ * Spaces.Dth f z θ|
        = (3 / (1 + z)) * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))
          * |Spaces.Dth (Spaces.Dth f) z θ| * |Spaces.Dth f z θ| := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (div_nonneg (by norm_num) (le_of_lt h1zpos)),
        abs_of_nonneg hsnn]
    rw [hkey]
    have hstep : (3 / (1 + z)) * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))
          * |Spaces.Dth (Spaces.Dth f) z θ| * |Spaces.Dth f z θ|
        ≤ (3 / (1 + z)) * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))
          * (Real.sin (2 * θ) * (2 * |Spaces.pth f z θ| + |Spaces.pth (Spaces.pth f) z θ|))
          * (Real.sin (2 * θ) * |Spaces.pth f z θ|) := by
      have hK' : (0 : ℝ) ≤ (3 / (1 + z)) * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))
          * (Real.sin (2 * θ) * (2 * |Spaces.pth f z θ| + |Spaces.pth (Spaces.pth f) z θ|)) := by
        have hsMnn : (0 : ℝ) ≤ Real.sin (2 * θ)
            * (2 * |Spaces.pth f z θ| + |Spaces.pth (Spaces.pth f) z θ|) :=
          mul_nonneg hs0 hMnn
        exact mul_nonneg hKnn hsMnn
      calc (3 / (1 + z)) * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))
            * |Spaces.Dth (Spaces.Dth f) z θ| * |Spaces.Dth f z θ|
          ≤ (3 / (1 + z)) * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))
            * (Real.sin (2 * θ) * (2 * |Spaces.pth f z θ| + |Spaces.pth (Spaces.pth f) z θ|))
            * |Spaces.Dth f z θ| :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hD2b hKnn) (abs_nonneg _)
        _ ≤ (3 / (1 + z)) * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))
            * (Real.sin (2 * θ) * (2 * |Spaces.pth f z θ| + |Spaces.pth (Spaces.pth f) z θ|))
            * (Real.sin (2 * θ) * |Spaces.pth f z θ|) :=
            mul_le_mul_of_nonneg_left hD1b hK'
    refine le_trans hstep ?_
    have hMN : (2 * |Spaces.pth f z θ| + |Spaces.pth (Spaces.pth f) z θ|)
          * |Spaces.pth f z θ| ≤ (2 * (C0 * z ^ 2) + C0) * (C0 * z ^ 2) := by
      have hM : 2 * |Spaces.pth f z θ| + |Spaces.pth (Spaces.pth f) z θ| ≤ 2 * (C0 * z ^ 2) + C0 := by
        linarith [h1, h3]
      refine mul_le_mul hM h1 (abs_nonneg _) ?_
      nlinarith [hC0, hzle]
    have h3div : 3 / (1 + z) ≤ 3 := by rw [div_le_iff₀ h1zpos]; linarith
    have hkey2 : (3 / (1 + z)) * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))
          * (Real.sin (2 * θ) * (2 * |Spaces.pth f z θ| + |Spaces.pth (Spaces.pth f) z θ|))
          * (Real.sin (2 * θ) * |Spaces.pth f z θ|)
        = (3 / (1 + z)) * ((Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * (Real.sin (2 * θ)) ^ 2)
          * ((2 * |Spaces.pth f z θ| + |Spaces.pth (Spaces.pth f) z θ|) * |Spaces.pth f z θ|) := by
      ring
    rw [hkey2]
    have hA : (3 / (1 + z)) * ((Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * (Real.sin (2 * θ)) ^ 2)
        ≤ 3 * 1 := by
      have hnn : (0 : ℝ) ≤ (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * (Real.sin (2 * θ)) ^ 2 :=
        mul_nonneg hsnn (sq_nonneg _)
      calc (3 / (1 + z)) * ((Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * (Real.sin (2 * θ)) ^ 2)
          ≤ 3 * ((Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * (Real.sin (2 * θ)) ^ 2) :=
            mul_le_mul_of_nonneg_right h3div hnn
        _ ≤ 3 * 1 := mul_le_mul_of_nonneg_left hsml (by norm_num)
    have hfin : 3 * 1 * ((2 * (C0 * z ^ 2) + C0) * (C0 * z ^ 2))
        ≤ (10 * C0 ^ 2 + 1) * (1 + z) ^ 4 := by
      have hz2le : z ^ 2 ≤ (1 + z) ^ 4 := by nlinarith [hzle, h4nn]
      have hz4le : z ^ 4 ≤ (1 + z) ^ 4 := by nlinarith [hzle, h4nn]
      nlinarith [hz2le, hz4le, h4nn, sq_nonneg C0, mul_nonneg (le_of_lt hC0) (sq_nonneg z)]
    have hMNnn : (0 : ℝ) ≤ (2 * |Spaces.pth f z θ| + |Spaces.pth (Spaces.pth f) z θ|)
        * |Spaces.pth f z θ| := mul_nonneg hMnn (abs_nonneg _)
    exact le_trans (mul_le_mul hA hMN hMNnn (by norm_num)) hfin

theorem dth_box_domination (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f : ℝ → ℝ → ℝ) (R : ℝ) (hR : 0 < R)
    (hb : ∃ C : ℝ, 0 < C ∧ ∀ z ∈ Set.Ioo 0 R, ∀ θ ∈ Spaces.Iθ,
      |Spaces.pth f z θ| ≤ C * z ^ 2 ∧ |Spaces.pz (Spaces.pth f) z θ| ≤ C * z
        ∧ |Spaces.pth (Spaces.pth f) z θ| ≤ C) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ Set.Ioo 0 R, ∀ θ ∈ Spaces.Iθ,
      |L (Spaces.Dth f) z θ * Spaces.Dth f z θ * Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))| ≤ C * (1 + z) ^ 4
      ∧ |(3 / (1 + z)) * (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * Spaces.Dth (Spaces.Dth f) z θ * Spaces.Dth f z θ| ≤ C * (1 + z) ^ 4
      ∧ |(Spaces.Dth f z θ) ^ 2 * Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))| ≤ C * (1 + z) ^ 4
      ∧ |(Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * (Spaces.Dth f z θ) ^ 2| ≤ C * (1 + z) ^ 4 := by
  obtain ⟨C0, hC0pos, hC0b⟩ := hb
  refine ⟨10 * C0 ^ 2 + 1, by positivity, ?_⟩
  intro z hz θ hθ
  obtain ⟨h1, h2, h3⟩ := hC0b z hz θ hθ
  exact ⟨box_L_Dth α hα hα1 f z θ C0 hz.1 hθ hC0pos h1 h2,
         box_Dth_Dth α hα hα1 f z θ C0 hz.1 hθ hC0pos h1 h3,
         box_Dth_sq_w α hα hα1 f z θ C0 hz.1 hθ hC0pos h1,
         box_Dth_sq α hα hα1 f z θ C0 hz.1 hθ hC0pos h1⟩

end Work.Coercivity
