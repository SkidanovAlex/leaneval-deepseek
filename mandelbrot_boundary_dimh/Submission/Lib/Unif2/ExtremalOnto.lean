import Submission.Lib.Unif2.UnifDeps
import Submission.Lib.Unif2.HolomorphicLog
import Submission.Lib.Unif2.Extremal
import Mathlib.Analysis.Complex.Schwarz

/-!
# The Möbius amplification (square-root) trick for the extremal function

This module develops the classical *improvement* argument for the extremal problem

`extremalFamily x₀ = {f : X → ℂ | f holomorphic, ‖f ·‖ ≤ 1, f x₀ = 0}`.

If `f` belongs to this family but **misses a value** `a` of the unit disc, then the composite
`ψ_a ∘ f` is nowhere vanishing (`ψ_a` the Möbius transformation of the disc with `ψ_a a = 0`), so
it has a holomorphic square root `h` on `X` (here the hypothesis `Hom (π₁ X x₀) ℝ = 0` enters
through `Submission.HolomorphicOnX.exists_log_of_ne_zero`), and the map `g = ψ_{h x₀} ∘ h` is
again in the family with strictly bigger derivative at `x₀`, by the classical factor
`(1 + ‖a‖)/(2 √‖a‖) > 1`.

Consequently an *extremal* function (one maximizing `‖f'(x₀)‖`) cannot miss any value: it maps
`X` onto the open unit disc.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

noncomputable section

open Filter Set
open Classical

namespace Submission

/-! ## The Möbius transformation of the unit disc -/

/-- The Möbius transformation `w ↦ (w - a)/(1 - conj a * w)` of `ℂ`, an automorphism of the open
unit disc when `‖a‖ < 1`, sending `a` to `0`. -/
def mobiusA (a w : ℂ) : ℂ := (w - a) / (1 - (starRingEnd ℂ) a * w)

theorem mobiusA_self (a : ℂ) : mobiusA a a = 0 := by simp [mobiusA]

theorem mobiusA_apply_zero (a : ℂ) : mobiusA a 0 = -a := by simp [mobiusA]

/-- The denominator of `mobiusA a` does not vanish on the closed unit disc when `‖a‖ < 1`. -/
theorem mobiusA_denom_ne_zero {a w : ℂ} (ha : ‖a‖ < 1) (hw : ‖w‖ ≤ 1) :
    1 - (starRingEnd ℂ) a * w ≠ 0 := by
  intro h
  have h1 : (starRingEnd ℂ) a * w = 1 := by
    simp only [sub_eq_zero] at h
    exact h.symm
  have h2 : ‖(starRingEnd ℂ) a * w‖ = 1 := by rw [h1, norm_one]
  rw [norm_mul, Complex.norm_conj] at h2
  have ha' : ‖a‖ ≤ 1 := le_of_lt ha
  nlinarith [norm_nonneg a, norm_nonneg w]

/-- `mobiusA a` does not vanish away from `a`. -/
theorem mobiusA_ne_zero {a w : ℂ} (ha : ‖a‖ < 1) (hw : ‖w‖ ≤ 1) (h : w ≠ a) :
    mobiusA a w ≠ 0 := by
  rw [mobiusA, div_ne_zero_iff]
  exact ⟨sub_ne_zero.mpr h, mobiusA_denom_ne_zero ha hw⟩

/-- Key identity: `‖w - a‖² + (1 - ‖w‖²)(1 - ‖a‖²) = ‖1 - conj a * w‖²`. -/
theorem normSq_one_sub_conj_mul (a w : ℂ) :
    Complex.normSq (1 - (starRingEnd ℂ) a * w)
      = Complex.normSq (w - a) + (1 - Complex.normSq w) * (1 - Complex.normSq a) := by
  rw [Complex.normSq_sub, Complex.normSq_sub, Complex.normSq_mul, Complex.normSq_conj,
    Complex.normSq_one]
  have hre : (starRingEnd ℂ) ((starRingEnd ℂ) a * w) = starRingEnd ℂ (w * starRingEnd ℂ a) := by
    simp only [map_mul, Complex.conj_conj]
    ring
  rw [hre]
  simp only [one_mul, Complex.conj_re]
  ring

/-- The Möbius transformation maps the closed unit disc into itself. -/
theorem norm_mobiusA_le {a w : ℂ} (ha : ‖a‖ < 1) (hw : ‖w‖ ≤ 1) : ‖mobiusA a w‖ ≤ 1 := by
  have hden := mobiusA_denom_ne_zero ha hw
  have hsqw : Complex.normSq w ≤ 1 := by
    rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg w]
  have hsqa : Complex.normSq a < 1 := by
    rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg a]
  have hnum : ‖w - a‖ ≤ ‖1 - (starRingEnd ℂ) a * w‖ := by
    have h := normSq_one_sub_conj_mul a w
    have hle : Complex.normSq (w - a) ≤ Complex.normSq (1 - (starRingEnd ℂ) a * w) := by
      rw [h]
      nlinarith [Complex.normSq_nonneg a]
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at hle
    have h1 : ‖w - a‖ = Real.sqrt (‖w - a‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    have h2 : ‖1 - (starRingEnd ℂ) a * w‖ = Real.sqrt (‖1 - (starRingEnd ℂ) a * w‖ ^ 2) :=
      (Real.sqrt_sq (norm_nonneg _)).symm
    rw [h1, h2]
    exact Real.sqrt_le_sqrt hle
  rw [mobiusA, norm_div, div_le_one (norm_pos_iff.mpr hden)]
  exact hnum

/-- Analyticity of the Möbius transformation away from its pole. -/
theorem analyticAt_mobiusA (a : ℂ) {w : ℂ} (h : 1 - (starRingEnd ℂ) a * w ≠ 0) :
    AnalyticAt ℂ (mobiusA a) w := by
  have hfun : mobiusA a = fun z : ℂ => (z - a) * (1 - (starRingEnd ℂ) a * z)⁻¹ := by
    funext z; rw [mobiusA, div_eq_mul_inv]
  rw [hfun]
  exact (analyticAt_id.sub analyticAt_const).mul
    ((analyticAt_const.sub (analyticAt_const.mul analyticAt_id)).inv h)

/-- The derivative of the Möbius transformation. -/
theorem deriv_mobiusA (a w : ℂ) (h : 1 - (starRingEnd ℂ) a * w ≠ 0) :
    deriv (mobiusA a) w = (1 - (starRingEnd ℂ) a * a) / (1 - (starRingEnd ℂ) a * w) ^ 2 := by
  have hd1 : DifferentiableAt ℂ (fun z : ℂ => z - a) w := differentiableAt_id.sub_const a
  have hd2 : DifferentiableAt ℂ (fun z : ℂ => 1 - (starRingEnd ℂ) a * z) w :=
    DifferentiableAt.sub (differentiableAt_const (x := w) (c := (1 : ℂ)))
      (DifferentiableAt.mul (differentiableAt_const (x := w) (c := (starRingEnd ℂ) a))
        differentiableAt_id)
  have hfun : mobiusA a = (fun z : ℂ => z - a) / (fun z : ℂ => 1 - (starRingEnd ℂ) a * z) := by
    funext z; rfl
  rw [hfun, deriv_div hd1 hd2 h]
  have e1 : deriv (fun z : ℂ => z - a) w = 1 := by simp
  have e2 : deriv (fun z : ℂ => 1 - (starRingEnd ℂ) a * z) w = -(starRingEnd ℂ) a := by
    simp
  rw [e1, e2]
  ring

theorem deriv_mobiusA_zero (a : ℂ) : deriv (mobiusA a) 0 = 1 - (starRingEnd ℂ) a * a := by
  rw [deriv_mobiusA a 0 (by simp)]
  simp

theorem deriv_mobiusA_self {a : ℂ} (ha : ‖a‖ < 1) :
    deriv (mobiusA a) a = 1 / (1 - (starRingEnd ℂ) a * a) := by
  have hden : 1 - (starRingEnd ℂ) a * a ≠ 0 := by
    intro h
    have h1 : (starRingEnd ℂ) a * a = 1 := by
      simp only [sub_eq_zero] at h
      exact h.symm
    have h2 : Complex.normSq a = 1 := by
      have h3 : ((Complex.normSq a : ℝ) : ℂ) = 1 := by
        rw [Complex.normSq_eq_conj_mul_self, h1]
      exact_mod_cast h3
    rw [Complex.normSq_eq_norm_sq] at h2
    nlinarith [norm_nonneg a]
  rw [deriv_mobiusA a a hden, sq]
  field_simp

end Submission

namespace Submission

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- Composition of a holomorphic function on `X` with the disc automorphism `mobiusA a` is
holomorphic. -/
theorem HolomorphicOnX.mobiusA_comp {f : X → ℂ} {U : Set X} (hf : HolomorphicOnX f U)
    (hb : ∀ x ∈ U, ‖f x‖ ≤ 1) {a : ℂ} (ha : ‖a‖ < 1) :
    HolomorphicOnX (fun x => mobiusA a (f x)) U := by
  intro x hx
  have hxsrc : x ∈ (chartAt ℂ x).source := mem_chart_source ℂ x
  have hleft : (chartAt ℂ x).symm ((chartAt ℂ x) x) = x := (chartAt ℂ x).left_inv hxsrc
  have hfx : AnalyticAt ℂ (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) := hf x hx
  have hval : (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) = f x := by
    simp only [Function.comp_apply, hleft]
  have hden : 1 - (starRingEnd ℂ) a * ((f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)) ≠ 0 := by
    rw [hval]
    exact mobiusA_denom_ne_zero ha (hb x hx)
  have hcomp := (analyticAt_mobiusA a hden).comp hfx
  have hfun : (fun x => mobiusA a (f x)) ∘ (chartAt ℂ x).symm
      = mobiusA a ∘ (f ∘ (chartAt ℂ x).symm) := rfl
  rw [HolomorphicOnXAt, hfun]
  exact hcomp

/-- Multiplication by a constant preserves holomorphy (with the constant on the right). -/
theorem HolomorphicOnXAt.mul_const {f : X → ℂ} {x : X} (hf : HolomorphicOnXAt f x) (c : ℂ) :
    HolomorphicOnXAt (fun y => f y * c) x := by
  rw [HolomorphicOnXAt] at hf ⊢
  have h : (fun y => f y * c) ∘ (chartAt ℂ x).symm
      = (f ∘ (chartAt ℂ x).symm) * (fun _ => c) := by
    funext w; rfl
  rw [h]
  exact hf.mul analyticAt_const

/-- **The Möbius (square-root) amplification.**  If `f : X → ℂ` is holomorphic, bounded by `1`
in modulus, vanishes at `x₀` and misses a value `a` with `‖a‖ < 1`, then there is another bounded
holomorphic `g` vanishing at `x₀` whose derivative at `x₀` (in the chart at `x₀`) has modulus
exactly `(1 + ‖a‖)/(2 √‖a‖)` times the derivative of `f` — a factor `> 1`. -/
theorem exists_holomorphicOnX_deriv_eq_of_misses_value {x₀ : X} [ConnectedSpace X]
    [Subsingleton (Additive (FundamentalGroup X x₀) →+ ℝ)]
    {f : X → ℂ} (hf : HolomorphicOnX f univ) (hb : ∀ x, ‖f x‖ ≤ 1) (h0 : f x₀ = 0)
    {a : ℂ} (ha : ‖a‖ < 1) (hmiss : ∀ x, f x ≠ a) :
    ∃ g : X → ℂ, HolomorphicOnX g univ ∧ (∀ x, ‖g x‖ ≤ 1) ∧ g x₀ = 0 ∧
      ‖deriv (g ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)‖ =
        (1 + ‖a‖) / (2 * Real.sqrt ‖a‖) *
          ‖deriv (f ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)‖ := by
  have ha0 : a ≠ 0 := by
    intro h; exact hmiss x₀ (by rw [h0, h])
  have hanorm : 0 < ‖a‖ := norm_pos_iff.mpr ha0
  -- the nowhere vanishing holomorphic function `φ = ψ_a ∘ f` and its square root `h`
  set φ : X → ℂ := fun x => mobiusA a (f x) with hφ
  have hφhol : HolomorphicOnX φ univ := hf.mobiusA_comp (fun x _ => hb x) ha
  have hφne : ∀ x, φ x ≠ 0 := fun x => mobiusA_ne_zero ha (hb x) (hmiss x)
  obtain ⟨H, hHhol, hHexp⟩ := HolomorphicOnX.exists_log_of_ne_zero x₀ hφhol hφne
  set h : X → ℂ := fun x => Complex.exp (H x * 2⁻¹) with hh
  have hhol : HolomorphicOnX h univ := fun x hx =>
    ((hHhol x hx).mul_const ((2:ℂ)⁻¹)).cexp
  have hh2 : ∀ x, h x ^ 2 = φ x := by
    intro x
    show Complex.exp (H x * 2⁻¹) ^ 2 = φ x
    rw [hHexp x, sq, ← Complex.exp_add]
    congr 1
    ring_nf
  have hhnorm : ∀ x, ‖h x‖ ≤ 1 := by
    intro x
    have h2 : ‖h x‖ ^ 2 ≤ 1 := by
      rw [← norm_pow, hh2 x, hφ]
      exact norm_mobiusA_le ha (hb x)
    nlinarith [norm_nonneg (h x)]
  -- the value `b = h x₀` at the base point
  set b : ℂ := h x₀ with hbdef
  have hb_sq : ‖b‖ ^ 2 = ‖a‖ := by
    have h1 : b ^ 2 = φ x₀ := by rw [hbdef]; exact hh2 x₀
    have h2 : φ x₀ = -a := by
      show mobiusA a (f x₀) = -a
      rw [h0, mobiusA_apply_zero]
    rw [← norm_pow, h1, h2, norm_neg]
  have hb_sqrt : ‖b‖ = Real.sqrt ‖a‖ := by
    have h3 : (0:ℝ) ≤ Real.sqrt ‖a‖ := Real.sqrt_nonneg _
    have h4 : (Real.sqrt ‖a‖) ^ 2 = ‖a‖ := Real.sq_sqrt (norm_nonneg a)
    nlinarith [norm_nonneg b, h3, hb_sq, h4]
  have hb_lt : ‖b‖ < 1 := by
    rw [hb_sqrt]
    rw [Real.sqrt_lt' (by norm_num : (0:ℝ) < 1)]
    simpa using ha
  have hb_ne : b ≠ 0 := by
    intro h; rw [h] at hb_sq; simp at hb_sq
    linarith [hanorm]
  -- the new map `g = ψ_b ∘ h`
  refine ⟨fun x => mobiusA b (h x), hhol.mobiusA_comp (fun x _ => hhnorm x) hb_lt,
    fun x => norm_mobiusA_le hb_lt (hhnorm x), ?_, ?_⟩
  · show mobiusA (h x₀) (h x₀) = 0
    exact mobiusA_self _
  -- the derivative computation, in the chart at `x₀`
  have E1 : (fun x => mobiusA b (h x)) ∘ (chartAt ℂ x₀).symm
      = mobiusA b ∘ (h ∘ (chartAt ℂ x₀).symm) := rfl
  have E2 : (φ ∘ (chartAt ℂ x₀).symm)
      = mobiusA a ∘ (f ∘ (chartAt ℂ x₀).symm) := rfl
  have E3 : (h ∘ (chartAt ℂ x₀).symm) * (h ∘ (chartAt ℂ x₀).symm) = φ ∘ (chartAt ℂ x₀).symm := by
    funext w
    simp only [Pi.mul_apply, Function.comp_apply]
    simpa [sq] using hh2 ((chartAt ℂ x₀).symm w)
  have hx₀src : x₀ ∈ (chartAt ℂ x₀).source := mem_chart_source ℂ x₀
  have hleft : (chartAt ℂ x₀).symm ((chartAt ℂ x₀) x₀) = x₀ := (chartAt ℂ x₀).left_inv hx₀src
  have hF : AnalyticAt ℂ (f ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀) := hf x₀ (mem_univ x₀)
  have hHc : AnalyticAt ℂ (h ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀) := hhol x₀ (mem_univ x₀)
  have hGc : AnalyticAt ℂ ((fun x => mobiusA b (h x)) ∘ (chartAt ℂ x₀).symm)
      ((chartAt ℂ x₀) x₀) :=
    (hhol.mobiusA_comp (fun x _ => hhnorm x) hb_lt) x₀ (mem_univ x₀)
  have hPhic : AnalyticAt ℂ (φ ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀) := hφhol x₀ (mem_univ x₀)
  have hHcval : (h ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀) = b := by
    simp only [Function.comp_apply, hleft, hbdef]
  have hFval : (f ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀) = 0 := by
    simp only [Function.comp_apply, hleft, h0]
  have hHcne : (h ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀) ≠ 0 := by
    rw [hHcval]; exact hb_ne
  have hden_a : 1 - (starRingEnd ℂ) a * (f ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀) ≠ 0 := by
    rw [hFval]; norm_num
  -- D1: derivative of `φ` in the chart
  have D1 : deriv (φ ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)
      = (1 - (starRingEnd ℂ) a * a) * deriv (f ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀) := by
    rw [E2]
    rw [deriv_comp _ (analyticAt_mobiusA a hden_a).differentiableAt hF.differentiableAt]
    rw [hFval, deriv_mobiusA_zero]
  -- D2: derivative of the square root `h`
  have D2 : deriv (h ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)
      = deriv (φ ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)
        / (2 * (h ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)) := by
    have hdm : deriv (φ ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)
        = 2 * (h ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)
          * deriv (h ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀) := by
      rw [← E3, deriv_mul hHc.differentiableAt hHc.differentiableAt]
      ring
    rw [hdm]
    field_simp
  -- D3: derivative of `g` in the chart
  have D3 : deriv ((fun x => mobiusA b (h x)) ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)
      = (1 / (1 - (starRingEnd ℂ) b * b)) * deriv (h ∘ (chartAt ℂ x₀).symm)
          ((chartAt ℂ x₀) x₀) := by
    rw [E1]
    rw [deriv_comp _ (analyticAt_mobiusA b ?_).differentiableAt hHc.differentiableAt]
    · rw [hHcval, deriv_mobiusA_self hb_lt]
    · rw [hHcval]
      exact mobiusA_denom_ne_zero hb_lt (le_of_lt hb_lt)
  have key : deriv ((fun x => mobiusA b (h x)) ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)
      = (1 / (1 - (starRingEnd ℂ) b * b)) *
          ((1 - (starRingEnd ℂ) a * a) * deriv (f ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)
            / (2 * b)) := by
    rw [D3, D2, D1, hHcval]
  rw [key]
  have hnorm_b : ‖1 - (starRingEnd ℂ) b * b‖ = 1 - ‖b‖ ^ 2 := by
    have h1 : 1 - (starRingEnd ℂ) b * b = ((1 - Complex.normSq b : ℝ) : ℂ) := by
      rw [← Complex.normSq_eq_conj_mul_self]
      push_cast
      ring
    rw [h1, Complex.norm_real, Complex.normSq_eq_norm_sq, Real.norm_eq_abs]
    exact abs_of_nonneg (by nlinarith [norm_nonneg b, hb_lt])
  have hnorm_a : ‖1 - (starRingEnd ℂ) a * a‖ = 1 - ‖a‖ ^ 2 := by
    have h1 : 1 - (starRingEnd ℂ) a * a = ((1 - Complex.normSq a : ℝ) : ℂ) := by
      rw [← Complex.normSq_eq_conj_mul_self]
      push_cast
      ring
    rw [h1, Complex.norm_real, Complex.normSq_eq_norm_sq, Real.norm_eq_abs]
    exact abs_of_nonneg (by nlinarith [norm_nonneg a, ha])
  simp only [norm_mul, norm_div, norm_one]
  rw [hnorm_b, hnorm_a, hb_sqrt, Real.sq_sqrt (norm_nonneg a)]
  have hne1 : (1 - ‖a‖) ≠ 0 := by
    intro h; rw [sub_eq_zero] at h; linarith [ha]
  have hne2 : (2 * Real.sqrt ‖a‖) ≠ 0 := by positivity
  field_simp
  norm_num
  ring

theorem extremalFamily_surjective_of_max {x₀ : X} [ConnectedSpace X]
    [Subsingleton (Additive (FundamentalGroup X x₀) →+ ℝ)] {f : X → ℂ}
    (hf : f ∈ extremalFamily x₀)
    (hmax : ∀ g ∈ extremalFamily x₀,
      ‖deriv (g ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)‖ ≤
        ‖deriv (f ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)‖)
    (hpos : 0 < ‖deriv (f ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)‖) :
    ∀ a : ℂ, ‖a‖ < 1 → ∃ x : X, f x = a := by
  intro a ha
  by_contra hcon
  push_neg at hcon
  have hmiss : ∀ x : X, f x ≠ a := fun x hx => hcon x hx
  have ha0 : a ≠ 0 := fun h => (hmiss x₀) (by rw [h, hf.2.2])
  have hanorm : 0 < ‖a‖ := norm_pos_iff.mpr ha0
  obtain ⟨g, hghol, hgnorm, hg0, hderiv⟩ :=
    exists_holomorphicOnX_deriv_eq_of_misses_value (x₀ := x₀) hf.1 hf.2.1 hf.2.2 ha hmiss
  have hgmem : g ∈ extremalFamily x₀ := ⟨hghol, hgnorm, hg0⟩
  have hfac : 1 < (1 + ‖a‖) / (2 * Real.sqrt ‖a‖) := by
    have hsqrt_pos : 0 < Real.sqrt ‖a‖ := Real.sqrt_pos.mpr hanorm
    have hsqrt_lt_one : Real.sqrt ‖a‖ < 1 := (Real.sqrt_lt' one_pos).mpr (by norm_num at ha ⊢; exact ha)
    have hsq : (Real.sqrt ‖a‖) ^ 2 = ‖a‖ := Real.sq_sqrt (norm_nonneg a)
    have hlt : 1 + ‖a‖ > 2 * Real.sqrt ‖a‖ := by nlinarith [hsqrt_pos, hsqrt_lt_one, hsq]
    rw [lt_div_iff₀ (by positivity)]
    linarith
  have hle := hmax g hgmem
  rw [hderiv] at hle
  have hD : (0:ℝ) ≤ ‖deriv (f ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀)‖ := norm_nonneg _
  nlinarith [hfac, hpos, hD, hle]

end Submission
