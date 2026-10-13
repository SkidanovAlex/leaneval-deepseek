/-
Copyright: work module for the Elgindi finite-time singularity project.

# Elementary reductions for the slice Step-5 estimate

Let `σ₄ = sin(2θ)^{4-γ}` and `w` denote its restriction to a slice.  This module performs the
*algebraic* part of the reduction of the requested estimate

  `L := ∫ (u'''')² σ₄  ≤  C · (B2 + A3 + A2 + A1 + A0)`

to the two analytic inputs of the proof.

* `slice5_L_le_J` — from the twice-differentiated ODE `u'''' = ∂³(tan θ u) - 6 u'' - g''`
  (proved as `slice5_eqn_deriv2`), the elementary inequality `(a+b+c)² ≤ 3(a²+b²+c²)` gives

    `L ≤ 3 (J + 36 A2' + B2)`,  `J := ∫ (∂³(tan θ u))² σ₄`,  `A2' := ∫ (u'')² σ₄`,
    `B2 := ∫ (g'')² σ₄`;

* `slice5_J_le_expand` — expanding `∂³(tan θ u) = S v₃ + 3 C v₂ - 3 S v₁ - C v` with
  `v = u / cos θ` (`slice5_tanu3_weak`) and using `(a+b+c+d)² ≤ 4 Σ a²` together with
  `S², C² ≤ 1`,

    `J ≤ 4 · (∫ v₃² σ₄ + 9 ∫ v₂² σ₄ + 9 ∫ v₁² σ₄ + ∫ v² σ₄)`.

Together with `A2' ≤ A2 := ∫ (u'')² sEta` (since `σ₄ ≤ sEta` on `Iθ`), the bounds
`∫ v² σ₄ ≤ C·(A2+A1+A0)`, `∫ v₁² σ₄ ≤ C·(A2+A1+A0)` of `slice5_vweight_le`, and the Step-5
room computation bounding `∫ v₃² σ₄`, this yields the requested estimate.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.remov.slice5_eqn_deriv2
import Submission.Work.FTS.EllipticEst.remov.slice5_rel

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov

set_option autoImplicit false

/-! ## Elementary facts about `Iθ` and the weight `σ₄` -/

lemma Iθ_eq_R : Work.Spaces.Iθ = Set.Icc (0 : ℝ) (Real.pi / 2) := rfl

lemma Iθ_measurable_R : MeasurableSet Work.Spaces.Iθ := by
  rw [Iθ_eq_R]; exact measurableSet_Icc

lemma sin_two_nonneg_R {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) := by
  rw [Iθ_eq_R] at hθ
  exact Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

/-- Almost every point of `Iθ` is interior. -/
lemma ae_mem_Ioo_Iθ_R :
    ∀ᵐ θ ∂(volume : Measure ℝ).restrict Work.Spaces.Iθ, θ ∈ Set.Ioo 0 (Real.pi / 2) := by
  have h : Set.Icc (0 : ℝ) (Real.pi / 2) =ᵐ[volume] Set.Ioo 0 (Real.pi / 2) :=
    (MeasureTheory.Ioo_ae_eq_Icc (μ := (volume : Measure ℝ))).symm
  rw [Iθ_eq_R, Measure.restrict_congr_set h]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioo

/-- `σ₄ = sin(2θ)^{4-γ}` is nonnegative on `Iθ`. -/
lemma sig4_nonneg_R (γ : ℝ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.rpow (Real.sin (2 * θ)) (4 - γ) :=
  Real.rpow_nonneg (sin_two_nonneg_R hθ) _

/-- `σ₄ ≤ sEta` on `Iθ` (for `1 ≤ γ ≤ 3/2`); indeed `σ₄ ≤ 1 ≤ sEta`. -/
lemma sig4_le_sEta_R (γ : ℝ) (_hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 3 / 2) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Real.rpow (Real.sin (2 * θ)) (4 - γ) ≤ Work.FTS.EllipticEst.sEta θ := by
  have hs := sin_two_nonneg_R hθ
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have h4 : (0 : ℝ) ≤ 4 - γ := by linarith
  have h4' : (4 : ℝ) - γ ≠ 0 := by linarith
  have heta : (-(Work.Spaces.eta)) ≠ 0 := by
    rw [Work.Spaces.eta]; norm_num
  rcases eq_or_lt_of_le hs with hz | hpos
  · have hz1 : Real.rpow (0 : ℝ) (4 - γ) = 0 := Real.zero_rpow h4'
    rw [← hz, hz1, Work.FTS.EllipticEst.sEta, ← hz, Real.zero_rpow heta]
  · have hle1 : Real.rpow (Real.sin (2 * θ)) (4 - γ) ≤ 1 :=
      Real.rpow_le_one hpos.le hs1 h4
    have hge1 : 1 ≤ Work.FTS.EllipticEst.sEta θ := by
      rw [Work.FTS.EllipticEst.sEta, Real.rpow_neg hpos.le]
      have h2 : Real.rpow (Real.sin (2 * θ)) Work.Spaces.eta ≤ 1 :=
        Real.rpow_le_one hpos.le hs1 Work.Spaces.eta_nonneg
      exact (one_le_inv₀ (Real.rpow_pos_of_pos hpos _)).mpr h2
    linarith

/-! ## Elementary algebraic inequalities -/

lemma add_sq_le_three (a b c : ℝ) : (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]

lemma add_sq_le_four (a b c d : ℝ) :
    (a + b + c + d) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c),
    sq_nonneg (b - d), sq_nonneg (c - d)]

/-! ## Reduction 1: `L ≤ 3 (J + 36 A2' + B2)` -/

/-- **Reduction 1.**  From the twice-differentiated ODE `u'''' = ∂³(tan θ u) - 6 u'' - g''` on
`(0, π/2)` and `(a+b+c)² ≤ 3(a²+b²+c²)`, the weighted `L²`-norm of `u''''` is controlled by
those of `∂³(tan θ u)`, `u''` and `g''`. -/
theorem slice5_L_le_J (γ : ℝ) (u g : ℝ → ℝ)
    (hu : ContDiffOn ℝ 4 u (Set.Ioo 0 (Real.pi / 2)))
    (hode : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 u θ = g θ)
    (hIntL : MeasureTheory.IntegrableOn (fun θ => (deriv (deriv (deriv (deriv u))) θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (4 - γ)) Work.Spaces.Iθ)
    (hIntJ : MeasureTheory.IntegrableOn (fun θ =>
        (deriv (deriv (deriv (fun t => Real.tan t * u t))) θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (4 - γ)) Work.Spaces.Iθ)
    (hInt2 : MeasureTheory.IntegrableOn (fun θ => (deriv (deriv u) θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (4 - γ)) Work.Spaces.Iθ)
    (hIntB : MeasureTheory.IntegrableOn (fun θ => (deriv (deriv g) θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (4 - γ)) Work.Spaces.Iθ) :
    (∫ θ in Work.Spaces.Iθ, (deriv (deriv (deriv (deriv u))) θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (4 - γ))
      ≤ 3 * ((∫ θ in Work.Spaces.Iθ,
            (deriv (deriv (deriv (fun t => Real.tan t * u t))) θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (4 - γ))
          + 36 * (∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (4 - γ))
          + (∫ θ in Work.Spaces.Iθ, (deriv (deriv g) θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (4 - γ))) := by
  set w : ℝ → ℝ := fun θ => Real.rpow (Real.sin (2 * θ)) (4 - γ) with hw
  set X : ℝ → ℝ := fun θ => (deriv (deriv (deriv (fun t => Real.tan t * u t))) θ) ^ 2 * w θ
    with hX
  set Y : ℝ → ℝ := fun θ => (deriv (deriv u) θ) ^ 2 * w θ with hY
  set Z : ℝ → ℝ := fun θ => (deriv (deriv g) θ) ^ 2 * w θ with hZ
  set W4 : ℝ → ℝ := fun θ => (deriv (deriv (deriv (deriv u))) θ) ^ 2 * w θ with hW4
  have hIntX : MeasureTheory.IntegrableOn X Work.Spaces.Iθ := hIntJ
  have hIntY : MeasureTheory.IntegrableOn Y Work.Spaces.Iθ := hInt2
  have hIntZ : MeasureTheory.IntegrableOn Z Work.Spaces.Iθ := hIntB
  have hIntW4 : MeasureTheory.IntegrableOn W4 Work.Spaces.Iθ := hIntL
  have hw_nn : ∀ᵐ θ ∂(volume : Measure ℝ).restrict Work.Spaces.Iθ, 0 ≤ w θ := by
    filter_upwards [MeasureTheory.ae_restrict_mem Iθ_measurable_R] with θ hθ
    exact sig4_nonneg_R γ hθ
  have hae : ∀ᵐ θ ∂(volume : Measure ℝ).restrict Work.Spaces.Iθ,
      deriv (deriv (deriv (deriv u))) θ
        = deriv (deriv (deriv (fun t => Real.tan t * u t))) θ
          + -(6 * deriv (deriv u) θ) + -(deriv (deriv g) θ) := by
    filter_upwards [ae_mem_Ioo_Iθ_R] with θ hθ
    have h := slice5_eqn_deriv2 u g hu hode θ hθ
    linarith
  have hpt : ∀ᵐ θ ∂(volume : Measure ℝ).restrict Work.Spaces.Iθ,
      W4 θ ≤ 3 * (X θ + 36 * Y θ + Z θ) := by
    filter_upwards [hae, hw_nn] with θ heq hwθ
    have hkey : (deriv (deriv (deriv (deriv u))) θ) ^ 2
        ≤ 3 * ((deriv (deriv (deriv (fun t => Real.tan t * u t))) θ) ^ 2
            + (6 * deriv (deriv u) θ) ^ 2 + (deriv (deriv g) θ) ^ 2) := by
      rw [heq]
      refine (add_sq_le_three (deriv (deriv (deriv (fun t => Real.tan t * u t))) θ)
        (-(6 * deriv (deriv u) θ)) (-(deriv (deriv g) θ))).trans (le_of_eq ?_)
      ring
    have h2 : (6 * deriv (deriv u) θ) ^ 2 = 36 * (deriv (deriv u) θ) ^ 2 := by ring
    calc W4 θ = (deriv (deriv (deriv (deriv u))) θ) ^ 2 * w θ := rfl
      _ ≤ 3 * ((deriv (deriv (deriv (fun t => Real.tan t * u t))) θ) ^ 2
            + (6 * deriv (deriv u) θ) ^ 2 + (deriv (deriv g) θ) ^ 2) * w θ :=
          mul_le_mul_of_nonneg_right hkey hwθ
      _ = 3 * (X θ + 36 * Y θ + Z θ) := by
          simp only [hX, hY, hZ]; rw [h2]; ring
  have hIntG : MeasureTheory.IntegrableOn (fun θ => 3 * (X θ + 36 * Y θ + Z θ))
      Work.Spaces.Iθ := (((hIntX.add (hIntY.const_mul 36)).add hIntZ).const_mul 3)
  have hmain := MeasureTheory.integral_mono_ae hIntW4 hIntG hpt
  have hval : (∫ θ in Work.Spaces.Iθ, 3 * (X θ + 36 * Y θ + Z θ))
      = 3 * ((∫ θ in Work.Spaces.Iθ, X θ) + 36 * (∫ θ in Work.Spaces.Iθ, Y θ)
          + (∫ θ in Work.Spaces.Iθ, Z θ)) := by
    rw [MeasureTheory.integral_const_mul (f := fun θ => X θ + 36 * Y θ + Z θ)]
    have hinner : (∫ θ in Work.Spaces.Iθ, X θ + 36 * Y θ + Z θ)
        = (∫ θ in Work.Spaces.Iθ, X θ) + 36 * (∫ θ in Work.Spaces.Iθ, Y θ)
          + (∫ θ in Work.Spaces.Iθ, Z θ) := by
      rw [MeasureTheory.integral_add (f := fun θ => X θ + 36 * Y θ) (g := fun θ => Z θ)
          (hIntX.add (hIntY.const_mul 36)) hIntZ,
        MeasureTheory.integral_add (f := fun θ => X θ) (g := fun θ => 36 * Y θ) hIntX
          (hIntY.const_mul 36),
        MeasureTheory.integral_const_mul (f := fun θ => Y θ)]
    rw [hinner]
  rw [hval] at hmain
  simpa only [hW4, hX, hY, hZ, hw] using hmain

/-! ## Reduction 2: the expansion of `J` -/

/-- **Reduction 2.**  Expanding `∂³(tan θ u) = S v₃ + 3 C v₂ - 3 S v₁ - C v`
(`slice5_tanu3_weak`), using `(a+b+c+d)² ≤ 4 (a²+b²+c²+d²)` and `S², C² ≤ 1`, the integral
`J := ∫ (∂³(tan θ u))² σ₄` is dominated by the four weighted integrals of the derivatives of
`v = u / cos θ`. -/
theorem slice5_J_le_expand (γ : ℝ) (u : ℝ → ℝ)
    (hu : ContDiffOn ℝ 4 u (Set.Ioo 0 (Real.pi / 2)))
    (hIntJ : MeasureTheory.IntegrableOn (fun θ =>
        (deriv (deriv (deriv (fun t => Real.tan t * u t))) θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (4 - γ)) Work.Spaces.Iθ)
    (hInt3 : MeasureTheory.IntegrableOn (fun θ =>
        (deriv (deriv (deriv (fun t => u t / Real.cos t))) θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (4 - γ)) Work.Spaces.Iθ)
    (hInt2 : MeasureTheory.IntegrableOn (fun θ =>
        (deriv (deriv (fun t => u t / Real.cos t)) θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (4 - γ)) Work.Spaces.Iθ)
    (hInt1 : MeasureTheory.IntegrableOn (fun θ =>
        (deriv (fun t => u t / Real.cos t) θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (4 - γ)) Work.Spaces.Iθ)
    (hInt0 : MeasureTheory.IntegrableOn (fun θ => (u θ / Real.cos θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (4 - γ)) Work.Spaces.Iθ) :
    (∫ θ in Work.Spaces.Iθ,
        (deriv (deriv (deriv (fun t => Real.tan t * u t))) θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (4 - γ))
      ≤ 4 * ((∫ θ in Work.Spaces.Iθ,
            (deriv (deriv (deriv (fun t => u t / Real.cos t))) θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (4 - γ))
          + 9 * (∫ θ in Work.Spaces.Iθ,
              (deriv (deriv (fun t => u t / Real.cos t)) θ) ^ 2 *
                Real.rpow (Real.sin (2 * θ)) (4 - γ))
          + 9 * (∫ θ in Work.Spaces.Iθ,
              (deriv (fun t => u t / Real.cos t) θ) ^ 2 *
                Real.rpow (Real.sin (2 * θ)) (4 - γ))
          + (∫ θ in Work.Spaces.Iθ, (u θ / Real.cos θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (4 - γ))) := by
  set w : ℝ → ℝ := fun θ => Real.rpow (Real.sin (2 * θ)) (4 - γ) with hw
  set X : ℝ → ℝ := fun θ =>
    (deriv (deriv (deriv (fun t => u t / Real.cos t))) θ) ^ 2 * w θ with hX
  set Y : ℝ → ℝ := fun θ => (deriv (deriv (fun t => u t / Real.cos t)) θ) ^ 2 * w θ with hY
  set Z : ℝ → ℝ := fun θ => (deriv (fun t => u t / Real.cos t) θ) ^ 2 * w θ with hZ
  set T : ℝ → ℝ := fun θ => (u θ / Real.cos θ) ^ 2 * w θ with hT
  set JJ : ℝ → ℝ := fun θ =>
    (deriv (deriv (deriv (fun t => Real.tan t * u t))) θ) ^ 2 * w θ with hJJ
  have hIntX : MeasureTheory.IntegrableOn X Work.Spaces.Iθ := hInt3
  have hIntY : MeasureTheory.IntegrableOn Y Work.Spaces.Iθ := hInt2
  have hIntZ : MeasureTheory.IntegrableOn Z Work.Spaces.Iθ := hInt1
  have hIntT : MeasureTheory.IntegrableOn T Work.Spaces.Iθ := hInt0
  have hIntJJ : MeasureTheory.IntegrableOn JJ Work.Spaces.Iθ := hIntJ
  have hw_nn : ∀ᵐ θ ∂(volume : Measure ℝ).restrict Work.Spaces.Iθ, 0 ≤ w θ := by
    filter_upwards [MeasureTheory.ae_restrict_mem Iθ_measurable_R] with θ hθ
    exact sig4_nonneg_R γ hθ
  have hpt : ∀ᵐ θ ∂(volume : Measure ℝ).restrict Work.Spaces.Iθ,
      JJ θ ≤ 4 * (((X θ + 9 * Y θ) + 9 * Z θ) + T θ) := by
    filter_upwards [ae_mem_Ioo_Iθ_R, hw_nn] with θ hid hwθ
    have h := slice5_tanu3_weak u hu θ hid
    have hkey : (deriv (deriv (deriv (fun t => Real.tan t * u t))) θ) ^ 2
        ≤ 4 * ((deriv (deriv (deriv (fun t => u t / Real.cos t))) θ) ^ 2
            + 9 * (deriv (deriv (fun t => u t / Real.cos t)) θ) ^ 2
            + 9 * (deriv (fun t => u t / Real.cos t) θ) ^ 2
            + (u θ / Real.cos θ) ^ 2) := by
      rw [h]
      refine (add_sq_le_four
        (Real.sin θ * deriv (deriv (deriv (fun t => u t / Real.cos t))) θ)
        (3 * Real.cos θ * deriv (deriv (fun t => u t / Real.cos t)) θ)
        (-(3 * Real.sin θ * deriv (fun t => u t / Real.cos t) θ))
        (-(Real.cos θ * (u θ / Real.cos θ)))).trans ?_
      nlinarith [Real.sin_sq_le_one θ, Real.cos_sq_le_one θ,
        sq_nonneg (deriv (deriv (deriv (fun t => u t / Real.cos t))) θ),
        sq_nonneg (deriv (deriv (fun t => u t / Real.cos t)) θ),
        sq_nonneg (deriv (fun t => u t / Real.cos t) θ),
        sq_nonneg (u θ / Real.cos θ)]
    calc JJ θ = (deriv (deriv (deriv (fun t => Real.tan t * u t))) θ) ^ 2 * w θ := rfl
      _ ≤ 4 * ((deriv (deriv (deriv (fun t => u t / Real.cos t))) θ) ^ 2
            + 9 * (deriv (deriv (fun t => u t / Real.cos t)) θ) ^ 2
            + 9 * (deriv (fun t => u t / Real.cos t) θ) ^ 2
            + (u θ / Real.cos θ) ^ 2) * w θ := mul_le_mul_of_nonneg_right hkey hwθ
      _ = 4 * (((X θ + 9 * Y θ) + 9 * Z θ) + T θ) := by
          simp only [hX, hY, hZ, hT]; ring
  have hIntG : MeasureTheory.IntegrableOn
      (fun θ => 4 * (((X θ + 9 * Y θ) + 9 * Z θ) + T θ)) Work.Spaces.Iθ :=
    (((hIntX.add (hIntY.const_mul 9)).add (hIntZ.const_mul 9)).add hIntT).const_mul 4
  have hmain := MeasureTheory.integral_mono_ae hIntJJ hIntG hpt
  have hval : (∫ θ in Work.Spaces.Iθ, 4 * (((X θ + 9 * Y θ) + 9 * Z θ) + T θ))
      = 4 * ((∫ θ in Work.Spaces.Iθ, X θ) + 9 * (∫ θ in Work.Spaces.Iθ, Y θ)
        + 9 * (∫ θ in Work.Spaces.Iθ, Z θ) + (∫ θ in Work.Spaces.Iθ, T θ)) := by
    rw [MeasureTheory.integral_const_mul (f := fun θ => ((X θ + 9 * Y θ) + 9 * Z θ) + T θ)]
    have hinner : (∫ θ in Work.Spaces.Iθ, ((X θ + 9 * Y θ) + 9 * Z θ) + T θ)
        = (∫ θ in Work.Spaces.Iθ, X θ) + 9 * (∫ θ in Work.Spaces.Iθ, Y θ)
          + 9 * (∫ θ in Work.Spaces.Iθ, Z θ) + (∫ θ in Work.Spaces.Iθ, T θ) := by
      rw [MeasureTheory.integral_add (f := fun θ => (X θ + 9 * Y θ) + 9 * Z θ)
          (g := fun θ => T θ) ((hIntX.add (hIntY.const_mul 9)).add (hIntZ.const_mul 9)) hIntT,
        MeasureTheory.integral_add (f := fun θ => X θ + 9 * Y θ) (g := fun θ => 9 * Z θ)
          (hIntX.add (hIntY.const_mul 9)) (hIntZ.const_mul 9),
        MeasureTheory.integral_add (f := fun θ => X θ) (g := fun θ => 9 * Y θ) hIntX
          (hIntY.const_mul 9),
        MeasureTheory.integral_const_mul (f := fun θ => Y θ),
        MeasureTheory.integral_const_mul (f := fun θ => Z θ)]
    rw [hinner]
  rw [hval] at hmain
  simpa only [hJJ, hX, hY, hZ, hT, hw] using hmain

/-! ## Integrability of the auxiliary integrands -/

lemma aesm_sig4 (γ : ℝ) (hγ2 : γ ≤ 3 / 2) :
    MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => Real.rpow (Real.sin (2 * θ)) (4 - γ))
      ((volume : Measure ℝ).restrict Work.Spaces.Iθ) :=
  ((Real.continuous_rpow_const (by linarith : (0 : ℝ) ≤ 4 - γ)).measurable.comp
    (Real.continuous_sin.measurable.comp (continuous_const.mul continuous_id).measurable)
    ).aestronglyMeasurable

lemma aesm_u2 (u : ℝ → ℝ) :
    MeasureTheory.AEStronglyMeasurable (fun θ : ℝ => (deriv (deriv u) θ) ^ 2)
      ((volume : Measure ℝ).restrict Work.Spaces.Iθ) :=
  ((measurable_deriv (deriv u)).pow_const 2).aestronglyMeasurable

lemma aesm_tanu3 (u : ℝ → ℝ) :
    MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => (deriv (deriv (deriv (fun t => Real.tan t * u t))) θ) ^ 2)
      ((volume : Measure ℝ).restrict Work.Spaces.Iθ) :=
  ((measurable_deriv (deriv (deriv (fun t => Real.tan t * u t)))).pow_const 2).aestronglyMeasurable

lemma aesm_u4 (u : ℝ → ℝ) :
    MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => (deriv (deriv (deriv (deriv u))) θ) ^ 2)
      ((volume : Measure ℝ).restrict Work.Spaces.Iθ) :=
  ((measurable_deriv (deriv (deriv (deriv u)))).pow_const 2).aestronglyMeasurable

lemma aesm_g2 (g : ℝ → ℝ) :
    MeasureTheory.AEStronglyMeasurable (fun θ : ℝ => (deriv (deriv g) θ) ^ 2)
      ((volume : Measure ℝ).restrict Work.Spaces.Iθ) :=
  ((measurable_deriv (deriv g)).pow_const 2).aestronglyMeasurable

/-- Under the hypotheses of the slice Step-5 estimate, the integrands `(d2 u)^2 sg4` and
`(d3 (tan u))^2 sg4` are integrable:  the first from `sg4 <= sEta`, the second from the
twice-differentiated ODE `d3(tan theta u) = d4 u + 6 d2 u + d2 g` and
`(a+b+c)^2 <= 3 (a^2+b^2+c^2)`. -/
theorem slice5_u_deriv_integrable (γ : ℝ) (hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 3 / 2)
    (u g : ℝ → ℝ)
    (hu : ContDiffOn ℝ 4 u (Set.Ioo 0 (Real.pi / 2)))
    (hode : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 u θ = g θ)
    (hIntL : MeasureTheory.IntegrableOn (fun θ => (deriv (deriv (deriv (deriv u))) θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (4 - γ)) Work.Spaces.Iθ)
    (hInt2 : MeasureTheory.IntegrableOn (fun θ => (deriv (deriv u) θ) ^ 2 *
        Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ)
    (hIntB : MeasureTheory.IntegrableOn (fun θ => (deriv (deriv g) θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (4 - γ)) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (fun θ => (deriv (deriv u) θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (4 - γ)) Work.Spaces.Iθ ∧
    MeasureTheory.IntegrableOn (fun θ =>
        (deriv (deriv (deriv (fun t => Real.tan t * u t))) θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (4 - γ)) Work.Spaces.Iθ := by
  have hI2 : MeasureTheory.IntegrableOn (fun θ => (deriv (deriv u) θ) ^ 2 *
      Real.rpow (Real.sin (2 * θ)) (4 - γ)) Work.Spaces.Iθ := by
    refine MeasureTheory.Integrable.mono (g := fun θ => (deriv (deriv u) θ) ^ 2 *
      Work.FTS.EllipticEst.sEta θ) hInt2 ?_ ?_
    · exact (aesm_u2 u).mul (aesm_sig4 γ hγ2)
    · filter_upwards [MeasureTheory.ae_restrict_mem Iθ_measurable_R] with θ hθ
      have hle : Real.rpow (Real.sin (2 * θ)) (4 - γ) ≤ Work.FTS.EllipticEst.sEta θ :=
        sig4_le_sEta_R γ hγ1 hγ2 hθ
      have hge : 0 ≤ (deriv (deriv u) θ) ^ 2 := sq_nonneg _
      have h0 : 0 ≤ Real.rpow (Real.sin (2 * θ)) (4 - γ) := sig4_nonneg_R γ hθ
      have h1 : 0 ≤ Work.FTS.EllipticEst.sEta θ := le_trans h0 hle
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hge h0),
        abs_of_nonneg (mul_nonneg hge h1)]
      exact mul_le_mul_of_nonneg_left hle hge
  refine ⟨hI2, ?_⟩
  have hdom : MeasureTheory.IntegrableOn (fun θ => 3 *
      ((deriv (deriv (deriv (deriv u))) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ)
        + 36 * ((deriv (deriv u) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ))
        + (deriv (deriv g) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ)))
      Work.Spaces.Iθ :=
    (((hIntL.add (hI2.const_mul 36)).add hIntB).const_mul 3)
  refine MeasureTheory.Integrable.mono (g := fun θ => 3 *
      ((deriv (deriv (deriv (deriv u))) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ)
        + 36 * ((deriv (deriv u) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ))
        + (deriv (deriv g) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ))) hdom ?_ ?_
  · exact (aesm_tanu3 u).mul (aesm_sig4 γ hγ2)
  · have hode2 := slice5_eqn_deriv2 u g hu hode
    filter_upwards [ae_mem_Ioo_Iθ_R, MeasureTheory.ae_restrict_mem Iθ_measurable_R]
      with θ hid hθ
    have hA : deriv (deriv (deriv (fun t => Real.tan t * u t))) θ
        = deriv (deriv (deriv (deriv u))) θ + 6 * deriv (deriv u) θ
          + deriv (deriv g) θ := by
      have h := hode2 θ hid; linarith
    have hnn : 0 ≤ (deriv (deriv (deriv (fun t => Real.tan t * u t))) θ) ^ 2 := sq_nonneg _
    have hw : 0 ≤ Real.rpow (Real.sin (2 * θ)) (4 - γ) := sig4_nonneg_R γ hθ
    have hnn3 : 0 ≤ 3 * ((deriv (deriv (deriv (deriv u))) θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (4 - γ)
        + 36 * ((deriv (deriv u) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ))
        + (deriv (deriv g) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ)) := by
      have hA0 : 0 ≤ (deriv (deriv (deriv (deriv u))) θ) ^ 2 := sq_nonneg _
      have hA1 : 0 ≤ (deriv (deriv u) θ) ^ 2 := sq_nonneg _
      have hA2 : 0 ≤ (deriv (deriv g) θ) ^ 2 := sq_nonneg _
      nlinarith [hA0, hA1, hA2, hw]
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hnn hw),
      abs_of_nonneg hnn3]
    rw [hA]
    have hsq := add_sq_le_three (deriv (deriv (deriv (deriv u))) θ)
      (6 * deriv (deriv u) θ) (deriv (deriv g) θ)
    have h2 : (6 * deriv (deriv u) θ) ^ 2 = 36 * (deriv (deriv u) θ) ^ 2 := by ring
    calc (deriv (deriv (deriv (deriv u))) θ + 6 * deriv (deriv u) θ
            + deriv (deriv g) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ)
        ≤ 3 * ((deriv (deriv (deriv (deriv u))) θ) ^ 2
            + (6 * deriv (deriv u) θ) ^ 2 + (deriv (deriv g) θ) ^ 2)
          * Real.rpow (Real.sin (2 * θ)) (4 - γ) :=
          mul_le_mul_of_nonneg_right hsq hw
      _ = 3 * ((deriv (deriv (deriv (deriv u))) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ)
            + 36 * ((deriv (deriv u) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ))
            + (deriv (deriv g) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ)) := by
          rw [h2]; ring

/-! ## The final absorption step of the assembly

Writing `L = X^2` with `X = sqrt L`, the inequality produced by the room estimate and
Cauchy-Schwarz reads `L <= -Q + C1 (Bv2 + Bv1 + Bv0) + 6 sqrt (A2 * L) + sqrt (B2 * L)`, with
`Q >= 0`, `Bv2 + Bv1 + Bv0 <= C2 R`, `A2 <= R`, `B2 <= R`, `R >= 0`.  Dropping `-Q` and
solving the resulting quadratic inequality for `X` bounds `L` by `100 R`; then `Q` is bounded
as well. -/

/-- Resolution of the quadratic inequality `L <= R + 6 sqrt (A L) + sqrt (B L)` with
`A, B <= R` and `L, R >= 0`. -/
lemma le_of_le_add_sqrts {A B L R : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hL : 0 ≤ L) (hR : 0 ≤ R)
    (hAR : A ≤ R) (hBR : B ≤ R)
    (h : L ≤ R + 6 * Real.sqrt (A * L) + Real.sqrt (B * L)) : L ≤ 100 * R := by
  have hAL : Real.sqrt (A * L) ≤ Real.sqrt (R * L) :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hAR hL)
  have hBL : Real.sqrt (B * L) ≤ Real.sqrt (R * L) :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hBR hL)
  have hc : L ≤ R + 7 * Real.sqrt (R * L) := by linarith
  set X : ℝ := Real.sqrt L with hX
  have hX0 : 0 ≤ X := Real.sqrt_nonneg L
  have hX2 : X ^ 2 = L := Real.sq_sqrt hL
  have hRL : Real.sqrt (R * L) = Real.sqrt R * X := by
    rw [Real.sqrt_mul hR, ← hX]
  rw [hRL] at hc
  rw [show L = X ^ 2 from hX2.symm] at hc
  have hYR : (Real.sqrt R) ^ 2 = R := Real.sq_sqrt hR
  have hXle : X ≤ 8 * Real.sqrt R := by
    by_contra hcon
    push_neg at hcon
    nlinarith [hc, hcon, Real.sqrt_nonneg R, hYR, sq_nonneg X]
  have hR0 : (0 : ℝ) ≤ Real.sqrt R := Real.sqrt_nonneg R
  calc L = X ^ 2 := hX2.symm
    _ ≤ (8 * Real.sqrt R) ^ 2 := by nlinarith [hXle, hX0, hR0]
    _ = 64 * R := by rw [mul_pow, hYR]; ring
    _ ≤ 100 * R := by linarith

/-- **The numerical core of the assembly.**  From the room estimate combined with
Cauchy-Schwarz one obtains `L <= -Q + Cv * Lw + 6 sqrt (A2 L) + sqrt (B2 L)`, where `L` is the
top weighted norm, `Q >= 0`, `Lw <= Cv R`, `A2 <= R`, `B2 <= R`.  Then both `L` and `Q` are
bounded by a constant times `R`. -/
lemma slice5_final_arith {L Q A2 B2 Cv Lw R : ℝ}
    (hR : 0 ≤ R) (hL : 0 ≤ L) (hQ : 0 ≤ Q) (hCv : 0 ≤ Cv)
    (hA2 : 0 ≤ A2) (hB2 : 0 ≤ B2) (hLw : 0 ≤ Lw)
    (hA2R : A2 ≤ R) (hB2R : B2 ≤ R) (hLwR : Lw ≤ Cv * R)
    (hmain : L ≤ -Q + Cv * Lw + 6 * Real.sqrt (A2 * L) + Real.sqrt (B2 * L)) :
    L ≤ 100 * ((Cv ^ 2 + 1) * R + 1) ∧ Q ≤ 71 * ((Cv ^ 2 + 1) * R + 1) := by
  set Rt : ℝ := (Cv ^ 2 + 1) * R + 1 with hRt
  have hRt0 : 0 ≤ Rt := by
    have : 0 ≤ Cv ^ 2 + 1 := by positivity
    nlinarith [mul_nonneg this hR]
  have hRtR : R ≤ Rt := by
    have hCv2R : 0 ≤ Cv ^ 2 * R := mul_nonneg (sq_nonneg Cv) hR
    rw [hRt]; nlinarith [hCv2R]
  have hA2Rt : A2 ≤ Rt := le_trans hA2R hRtR
  have hB2Rt : B2 ≤ Rt := le_trans hB2R hRtR
  have hCLw : Cv * Lw ≤ Rt := by
    have h1 : Cv * Lw ≤ Cv * (Cv * R) := mul_le_mul_of_nonneg_left hLwR hCv
    have h1' : Cv * (Cv * R) = Cv ^ 2 * R := by ring
    have h2 : 0 ≤ Cv ^ 2 * R := mul_nonneg (sq_nonneg Cv) hR
    rw [hRt]
    nlinarith [h1, h1', h2]
  have hmain' : L ≤ Rt + 6 * Real.sqrt (A2 * L) + Real.sqrt (B2 * L) := by linarith
  have hLle : L ≤ 100 * Rt :=
    le_of_le_add_sqrts hA2 hB2 hL hRt0 hA2Rt hB2Rt hmain'
  have hQle : Q ≤ 71 * Rt := by
    have hAL : Real.sqrt (A2 * L) ≤ 10 * Rt := by
      have h1 : A2 * L ≤ Rt * (100 * Rt) := by nlinarith [hA2Rt, hLle, hRt0]
      have h2 : Real.sqrt (Rt * (100 * Rt)) = 10 * Rt := by
        rw [show Rt * (100 * Rt) = (10 * Rt) ^ 2 by ring, Real.sqrt_sq (by linarith)]
      calc Real.sqrt (A2 * L) ≤ Real.sqrt (Rt * (100 * Rt)) := Real.sqrt_le_sqrt h1
        _ = 10 * Rt := h2
    have hBL : Real.sqrt (B2 * L) ≤ 10 * Rt := by
      have h1 : B2 * L ≤ Rt * (100 * Rt) := by nlinarith [hB2Rt, hLle, hRt0]
      have h2 : Real.sqrt (Rt * (100 * Rt)) = 10 * Rt := by
        rw [show Rt * (100 * Rt) = (10 * Rt) ^ 2 by ring, Real.sqrt_sq (by linarith)]
      calc Real.sqrt (B2 * L) ≤ Real.sqrt (Rt * (100 * Rt)) := Real.sqrt_le_sqrt h1
        _ = 10 * Rt := h2
    linarith
  exact ⟨hLle, hQle⟩

end Work.FTS.EllipticEst.remov
