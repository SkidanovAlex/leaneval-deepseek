import Mathlib
import Submission.Work.RPA3.Defs
import Submission.Work.RPA3.contDiff_param_intervalIntegral
import Submission.Work.RPA3.flux_form_closed
import Submission.Work.RPA3.flux_prim_defs
import Submission.Work.RPA3.flux_prim_smooth
import Submission.Work.RPA3.Hf_per
import Submission.Work.RPA3.bxf_btf_symm
import Submission.Work.RPA3.deriv_Hf_t

namespace Work.RPA3

open scoped ContDiff
open scoped Interval

set_option autoImplicit false

noncomputable section

/-! ## Auxiliary facts for the assembly of D1

These are the small pieces of the endgame of the flux primitive: the two elementary
`|·|`-estimates used to localise the integral, the chain rule for `z ↦ -z` in `deriv` form,
and the differentiability in `y` resp. `s` of `Hf` (which is how `is_const_of_deriv_eq_zero` is
applied to the two auxiliary functions of the argument). -/

/-- Chain rule for the composition with `z ↦ -z`, in `deriv` form. -/
lemma flux_deriv_neg_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (y : ℝ) : deriv (fun z => f (-z)) y = -deriv f (-y) := deriv_comp_neg f y

/-- If `X₀ ≤ u` then `X₀ ≤ |u|`. -/
lemma flux_abs_ge_of_le (X0 u : ℝ) (h : X0 ≤ u) : X0 ≤ |u| := le_trans h (le_abs_self u)

/-- If `u ≤ -X₀` then `X₀ ≤ |u|`. -/
lemma flux_abs_ge_of_le_neg (X0 u : ℝ) (h : u ≤ -X0) : X0 ≤ |u| := by
  by_cases hu : 0 ≤ u
  · rw [abs_of_nonneg hu]; linarith
  · rw [abs_of_neg (lt_of_not_ge hu)]; linarith

/-- The `x`-slice of the `x`-component of the flux form is continuous. -/
lemma flux_continuous_slice_bxf (L : LagFamily) (τ t : ℝ) :
    Continuous (fun u : ℝ => bxf L τ u t) := by
  have hmap : Continuous (fun u : ℝ => ((τ, (u, t)) : ℝ × (ℝ × ℝ))) := by fun_prop
  have h1 : Continuous (fun z : ℝ × (ℝ × ℝ) => bxf L z.1 z.2.1 z.2.2) :=
    (contDiff_fluxX L).continuous
  exact h1.comp hmap

/-- `y ↦ Hf L τ y t` is differentiable. -/
lemma flux_differentiable_Hf_snd (L : LagFamily) (τ t : ℝ) :
    Differentiable ℝ (fun y : ℝ => Hf L τ y t) := by
  have h1 := contDiff_Hf L
  have hmap : ContDiff ℝ 7 (fun y : ℝ => ((τ, (y, t)) : ℝ × (ℝ × ℝ))) := by fun_prop
  have h2 : ContDiff ℝ 7 (fun y : ℝ => Hf L τ y t) := by
    simpa [Function.comp_def] using h1.comp hmap
  exact h2.differentiable (by norm_num)

/-- `s ↦ Hf L τ x s` is differentiable. -/
lemma flux_differentiable_Hf_trd (L : LagFamily) (τ x : ℝ) :
    Differentiable ℝ (fun s : ℝ => Hf L τ x s) := by
  have h1 := contDiff_Hf L
  have hmap : ContDiff ℝ 7 (fun s : ℝ => ((τ, (x, s)) : ℝ × (ℝ × ℝ))) := by fun_prop
  have h2 : ContDiff ℝ 7 (fun s : ℝ => Hf L τ x s) := by
    simpa [Function.comp_def] using h1.comp hmap
  exact h2.differentiable (by norm_num)

/-- **The endgame of D1.**  For a family in `LagFamily` the primitive `Hf` of `flux_prim_defs`
vanishes for `|x| ≥ X₀` and is `2π`-periodic in the angle.

The proof.  `Hf L τ y t = -∫_{u=-X₀}^{y} bxf L τ u t du`, so `∂_y Hf = -bxf` (`deriv_Hf_x`)
and `∂_t Hf = -btf` (`deriv_Hf_t`).

* `c₊(t) := Hf L τ X₀ t` is independent of `t`, since `∂_t Hf = -btf` vanishes for `x = X₀`
  (`bxf_btf_van`, as `X₀ ≤ |X₀|`).
* `G y := Hf L τ (-y) (t+π) - Hf L τ y t` has `G' y = -bxf L τ (-y) (t+π) + bxf L τ y t = 0`, by
  `bxf_btf_symm`; so `G` is constant.  At the two ends this gives
  `c₊(t) = G(-X₀) = G(X₀) = -c₊(t)`, because `Hf L τ (-X₀) · = 0` (an empty interval).  Hence
  `c₊ = 0`; that is `Hf L τ X₀ t = 0`.
* For `x ≥ X₀`, `∫_{-X₀}^{x} bxf = ∫_{-X₀}^{X₀} bxf + ∫_{X₀}^{x} bxf` and the second integral
  vanishes because `bxf L τ u t = 0` for `X₀ ≤ u`; so `Hf L τ x t = Hf L τ X₀ t = 0`.  For
  `x ≤ -X₀`, `∫_{-X₀}^{x} bxf = -∫_{x}^{-X₀} bxf = 0` for the same reason.
* The `2π`-periodicity in `t` is `Hf_per`. -/
theorem flux_far_per (L : LagFamily) (τ x t : ℝ) (hx : L.X0 ≤ |x|) :
    Hf L τ x t = 0 ∧ Hf L τ x (t + 2 * Real.pi) = Hf L τ x t := by
  have hsymmX : ∀ y : ℝ, bxf L τ (-y) (t + Real.pi) = -bxf L τ y t :=
    fun y => (bxf_btf_symm L τ y t).1
  -- `Hf` at `-X₀` vanishes: the interval is empty
  have hneg : ∀ s : ℝ, Hf L τ (-(L.X0)) s = 0 := by
    intro s
    rw [Hf_eq_integral, intervalIntegral.integral_same, neg_zero]
  -- `c₊ = Hf L τ X₀ t` is independent of `t`
  have hX0const : ∀ t t' : ℝ, Hf L τ L.X0 t = Hf L τ L.X0 t' := by
    have hderiv : ∀ s, deriv (fun s' : ℝ => Hf L τ L.X0 s') s = 0 := by
      intro s
      rw [deriv_Hf_t L τ L.X0 s, neg_eq_zero]
      exact (bxf_btf_van L τ L.X0 s (le_abs_self L.X0)).2
    exact is_const_of_deriv_eq_zero (flux_differentiable_Hf_trd L τ L.X0) hderiv
  -- `G y = Hf L τ (-y) (t+π) - Hf L τ y t` has zero derivative, hence is constant
  have hGderiv : ∀ y, deriv (fun y' : ℝ => Hf L τ (-y') (t + Real.pi) - Hf L τ y' t) y = 0 := by
    intro y
    have hcomp : deriv (fun z : ℝ => Hf L τ (-z) (t + Real.pi)) y = -bxf L τ y t := by
      have h1 : (fun z : ℝ => Hf L τ (-z) (t + Real.pi))
          = (fun z : ℝ => (fun w : ℝ => Hf L τ w (t + Real.pi)) (-z)) := rfl
      rw [h1, flux_deriv_neg_comp (fun w : ℝ => Hf L τ w (t + Real.pi)) y,
        deriv_Hf_x L τ (-y) (t + Real.pi), hsymmX y]
      ring
    have hsub : deriv (fun y' : ℝ => Hf L τ (-y') (t + Real.pi) - Hf L τ y' t) y
        = deriv (fun z : ℝ => Hf L τ (-z) (t + Real.pi)) y
          - deriv (fun z : ℝ => Hf L τ z t) y := by
      have hA : DifferentiableAt ℝ (fun z : ℝ => Hf L τ (-z) (t + Real.pi)) y :=
        ((flux_differentiable_Hf_snd L τ (t + Real.pi)).comp
          differentiable_neg).differentiableAt
      have hB : DifferentiableAt ℝ (fun z : ℝ => Hf L τ z t) y :=
        (flux_differentiable_Hf_snd L τ t).differentiableAt
      exact (hA.hasDerivAt.sub hB.hasDerivAt).deriv
    rw [hsub, hcomp, deriv_Hf_x]
    ring
  have hGdiff : Differentiable ℝ (fun y : ℝ => Hf L τ (-y) (t + Real.pi) - Hf L τ y t) :=
    ((flux_differentiable_Hf_snd L τ (t + Real.pi)).comp differentiable_neg).sub
      (flux_differentiable_Hf_snd L τ t)
  have hGconst := is_const_of_deriv_eq_zero hGdiff hGderiv
  -- the two ends give `c₊ = -c₊ = 0`
  have hX0val : Hf L τ L.X0 t = 0 := by
    have h1 := hGconst (-(L.X0)) L.X0
    beta_reduce at h1
    rw [neg_neg, hneg t, hneg (t + Real.pi), hX0const (t + Real.pi) t] at h1
    linarith
  constructor
  · by_cases hxle : x ≤ -(L.X0)
    · have hcongr : (∫ u in x..(-(L.X0)), bxf L τ u t) = ∫ u in x..(-(L.X0)), (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro u hu
        rw [Set.uIcc_of_le hxle] at hu
        exact (bxf_btf_van L τ u t (flux_abs_ge_of_le_neg L.X0 u hu.2)).1
      rw [Hf_eq_integral, intervalIntegral.integral_symm, hcongr,
        intervalIntegral.integral_zero]
      simp
    · have hX0le : L.X0 ≤ x := by
        by_cases h0 : 0 ≤ x
        · rwa [abs_of_nonneg h0] at hx
        · exfalso
          rw [abs_of_neg (lt_of_not_ge h0)] at hx
          linarith
      have hcongr : (∫ u in L.X0..x, bxf L τ u t) = ∫ u in L.X0..x, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro u hu
        rw [Set.uIcc_of_le hX0le] at hu
        exact (bxf_btf_van L τ u t (flux_abs_ge_of_le L.X0 u hu.1)).1
      have hzero : (∫ u in L.X0..x, bxf L τ u t) = 0 := by
        rw [hcongr, intervalIntegral.integral_zero]
      have hsplit : (∫ u in (-(L.X0))..x, bxf L τ u t)
          = (∫ u in (-(L.X0))..L.X0, bxf L τ u t) + ∫ u in L.X0..x, bxf L τ u t :=
        (intervalIntegral.integral_add_adjacent_intervals
          ((flux_continuous_slice_bxf L τ t).intervalIntegrable _ _)
          ((flux_continuous_slice_bxf L τ t).intervalIntegrable _ _)).symm
      calc Hf L τ x t = -∫ u in (-(L.X0))..x, bxf L τ u t := Hf_eq_integral L τ x t
        _ = -((∫ u in (-(L.X0))..L.X0, bxf L τ u t) + ∫ u in L.X0..x, bxf L τ u t) := by
              rw [hsplit]
        _ = -((∫ u in (-(L.X0))..L.X0, bxf L τ u t) + 0) := by rw [hzero]
        _ = Hf L τ L.X0 t := by rw [add_zero, Hf_eq_integral]
        _ = 0 := hX0val
  · exact Hf_per L τ x t

/-- D1, the flux primitive: for a family Lagrangian and 2π-periodic in the angle for all τ, the flux
form ω(∂_τℓ, ·) has a primitive h, 2π-periodic in t, vanishing for |x| ≥ X₀, whose x- and
t-derivatives are minus the corresponding components of the flux form.  Define h as minus the
integral of β_x from -X₀ to x, written as the fixed-interval parametric integral over s ∈ [0,1] of
β_x(τ, -X₀+s(x+X₀), t) times (x+X₀); smoothness is contDiff_param_intervalIntegral, ∂_x h is the
FTC identity for the integral, and ∂_t h uses the closedness ∂_x β_t = ∂_t β_x (flux_form_closed)
together with β_t = 0 for |x| ≥ X₀.  The value at the right end, c₊ = -∫_{-X₀}^{X₀} β_x, is
independent of t (because ∂_t h = -β_t = 0 for |x| ≥ X₀), and the τ_π symmetry gives
β_x(τ,-x,t+π) = -β_x(τ,x,t) (the linear part S of τ_π satisfies ω(Sa,Sb) = ω(a,b)) so that
h(τ,-x,t+π) - h(τ,x,t) is independent of x, whence c₊ = -c₊ = 0 and h = 0 for |x| ≥ X₀. -/
theorem flux_primitive (L : Work.RPA3.LagFamily) :
    ∃ h : ℝ → ℝ × ℝ → ℝ, ContDiff ℝ 7 (fun z : ℝ × (ℝ × ℝ) => h z.1 z.2) ∧
      (∀ τ x t, h τ (x, t + 2 * Real.pi) = h τ (x, t)) ∧
      (∀ τ x t, L.X0 ≤ |x| → h τ (x, t) = 0) ∧
      (∀ τ x t, deriv (fun y => h τ (y, t)) x =
          -Work.RPA3.symp (deriv (fun σ => L.ℓ σ (x, t)) τ) (deriv (fun y => L.ℓ τ (y, t)) x)) ∧
      (∀ τ x t, deriv (fun s => h τ (x, s)) t =
          -Work.RPA3.symp (deriv (fun σ => L.ℓ σ (x, t)) τ) (deriv (fun s => L.ℓ τ (x, s)) t)) := by
  refine ⟨hf L, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hf] using contDiff_Hf L
  · intro τ x t
    simpa only [hf] using Hf_per L τ x t
  · intro τ x t hx
    simpa only [hf] using (flux_far_per L τ x t hx).1
  · intro τ x t
    simpa only [hf, bxf] using deriv_Hf_x L τ x t
  · intro τ x t
    simpa only [hf, btf] using deriv_Hf_t L τ x t

end

end Work.RPA3
