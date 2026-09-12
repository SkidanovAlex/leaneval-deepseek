import Mathlib
import Submission.ModelStarMap

/-!
# ModelStarBoundary -- unit-circle factor identities for the model map
# (milestone (a) part 3, stage 1: exact half-angle + arg sub-lemmas)

STATUS: verified research-isolate milestone; 0 sorries; axiom-clean
[propext, Classical.choice, Quot.sound] (check with `#print axioms`); does
NOT import `Submission.lean` (unimported module).  These are the
"smallest sub-lemmas" of the folded-boundary-correspondence programme for
the Eremenko model map `F(z) = z·∏_k (1 − z_k·z^{-1})^(2 r_k)` (see
Submission/EremenkoConverse.lean and STATUS §§34/34b/35): on the unit
circle each factor base `1 − z_k·z^{-1}` is decomposed into exact half-
angle form and its principal argument is computed, so that later modules
can prove the arc-constancy of `arg F(e^{it})` between consecutive
junction points `z_k`.

CONTENT.
  1. Exact complex half-angle decomposition of `1 − exp(θ·I)`:
     `one_sub_exp_mul_I θ : 1 − e^{iθ} = −2·I·e^{iθ/2}·sin(θ/2)`.
  2. Principal-argument formulas (both branches, covering every `θ` not a
     multiple of `2π`):
     * `arg_one_sub_exp_mul_I_pos` : `0 < θ < 2π`  ⟹  arg = θ/2 − π/2;
     * `arg_one_sub_exp_mul_I_neg` : `−2π < θ < 0` ⟹  arg = θ/2 + π/2.
  3. Circle factor positivity/slit-plane lemmas: for unit `a`, unit `z`
     with `a ≠ z` the base `1 − a·z^{-1}` has strictly positive real part,
     lies in the slit plane (principal powers are well-behaved on open arcs
     of the circle avoiding the junctions), and is nonzero.
  4. Model-map boundary corollaries: every factor base is in the slit
     plane at unit-circle points away from its junction, and the model
     product `modelProduct` (hence `modelF`, `z ≠ 0`) is nonzero on the
     circle away from all junctions.

Notes for future arc work: with `z = e^{it}`, `z_k = e^{i φ_k}`, factor k
at `t ∈ (φ_k, φ_{k+1})` has `θ_k := φ_k − t ∈ (−2π, 0)`, so
`arg(1 − z_k·z^{-1}) = (φ_k − t)/2 + π/2` (lemma 2 negative branch); the
`t`-dependence then cancels against `arg z = t` and `Σ_k r_k = 1` (the
arc-constancy computation of EremenkoConverse NOTE 90).  For factors with
`φ_k > t` the positive branch applies instead.

DEDUP (SESSION 36): all of `one_sub_exp_mul_I`, `arg_one_sub_exp_mul_I_pos`,
`arg_one_sub_exp_mul_I_neg`, `re_lt_one_of_norm_one`,
`re_one_sub_inv_pos_of_unit_ne` and `one_sub_inv_mem_slitPlane_of_unit_ne`
are now PUBLISHED in the shared commons (Commons.Analysis.Complex.*,
same statements; import e.g. `Submission.Commons.Analysis.Complex.
one_sub_exp_mul_I`); the local copies above are kept so this module stays
self-contained.  Future modules may import the commons versions instead.
-/

noncomputable section

open scoped Real BigOperators Topology
open Filter Set Complex

namespace Submission.ModelStarBoundary

/-! ## 1. Exact half-angle decomposition -/

/-- `1 − e^{iθ} = −2·i·e^{iθ/2}·sin(θ/2)`, exact, no branch issues. -/
theorem one_sub_exp_mul_I (θ : ℝ) :
    1 - Complex.exp (θ * Complex.I) =
      -2 * Complex.I * Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I) * (Real.sin (θ / 2) : ℂ) := by
  have hsum : (((θ / 2 : ℝ) : ℂ) * Complex.I) + (((θ / 2 : ℝ) : ℂ) * Complex.I) =
      θ * Complex.I := by
    push_cast
    ring
  let X : ℂ := Complex.exp (-(((θ / 2 : ℝ) : ℂ) * Complex.I)) -
      Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I)
  have hdiff : X = -2 * Complex.I * (Real.sin (θ / 2) : ℂ) := by
    have hs := Complex.two_sin (((θ / 2 : ℝ) : ℂ))
    have hmain : X = -2 * Complex.I * Complex.sin (((θ / 2 : ℝ) : ℂ)) := by
      have hI : Complex.I * -Complex.I = 1 := by
        rw [mul_neg, Complex.I_mul_I]
        norm_num
      have hsX : 2 * Complex.sin (((θ / 2 : ℝ) : ℂ)) = X * Complex.I := by
        dsimp [X]
        simpa using hs
      calc
        X = (X * Complex.I) * -Complex.I := by
          rw [mul_assoc, hI, mul_one]
        _ = (2 * Complex.sin (((θ / 2 : ℝ) : ℂ))) * -Complex.I := by rw [← hsX]
        _ = -2 * Complex.I * Complex.sin (((θ / 2 : ℝ) : ℂ)) := by ring
    calc
      X = -2 * Complex.I * Complex.sin (((θ / 2 : ℝ) : ℂ)) := hmain
      _ = -2 * Complex.I * (Real.sin (θ / 2) : ℂ) := by rw [Complex.ofReal_sin]
  calc
    1 - Complex.exp (θ * Complex.I)
        = Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I) * X := by
          dsimp [X]
          rw [mul_sub]
          rw [← Complex.exp_add (x := (((θ / 2 : ℝ) : ℂ) * Complex.I)) (y := (-(((θ / 2 : ℝ) : ℂ) * Complex.I)))]
          rw [← Complex.exp_add (x := (((θ / 2 : ℝ) : ℂ) * Complex.I)) (y := (((θ / 2 : ℝ) : ℂ) * Complex.I))]
          rw [add_neg_cancel]
          rw [Complex.exp_zero]
          rw [hsum]
    _ = -2 * Complex.I * Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I) * (Real.sin (θ / 2) : ℂ) := by
          rw [hdiff]
          ring

/-! ## 2. Principal arguments of `1 − e^{iθ}` -/

/-- For `0 < θ < 2π` (so `sin(θ/2) > 0`): principal `arg (1 − e^{iθ}) = θ/2 − π/2`. -/
theorem arg_one_sub_exp_mul_I_pos {θ : ℝ} (hθ0 : 0 < θ) (hθ2 : θ < 2 * Real.pi) :
    (1 - Complex.exp (θ * Complex.I)).arg = θ / 2 - Real.pi / 2 := by
  have hsin : 0 < Real.sin (θ / 2) := by
    exact Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [hθ2])
  have hdec := one_sub_exp_mul_I θ
  have harr : 1 - Complex.exp (θ * Complex.I) =
      (2 * (Real.sin (θ / 2) : ℂ)) * ((-Complex.I) * Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I)) := by
    rw [hdec]
    ring
  have harg := congrArg Complex.arg harr
  have h2s : (2 * (Real.sin (θ / 2) : ℂ)) ≠ 0 := by
    exact mul_ne_zero (by norm_num) (by
      exact_mod_cast (ne_of_gt hsin))
  have hw : (-Complex.I) * Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I) ≠ 0 := by
    exact mul_ne_zero (by simp) (Complex.exp_ne_zero _)
  have hargW : ((-Complex.I) * Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I)).arg = θ / 2 - Real.pi / 2 := by
    have ha1 : (-Complex.I).arg = -(Real.pi / 2) := Complex.arg_neg_I
    have ha2 : (Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I)).arg = θ / 2 := by
      have hβ2 : θ / 2 ∈ Set.Ioc (-Real.pi) (-Real.pi + 2 * Real.pi) := by
        constructor <;> linarith
      have hself : toIocMod Real.two_pi_pos (-Real.pi) (θ / 2) = θ / 2 :=
        (toIocMod_eq_self Real.two_pi_pos (a := -Real.pi) (b := (θ / 2))).2 hβ2
      rw [Complex.arg_exp_mul_I (θ / 2), hself]
    have hsum : (-Complex.I).arg + (Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I)).arg
        ∈ Set.Ioc (-Real.pi) Real.pi := by
      constructor <;> linarith
    rw [Complex.arg_mul (by simp) (Complex.exp_ne_zero _) hsum]
    rw [ha1, ha2]
    ring
  have hargR : ((2 * (Real.sin (θ / 2) : ℂ)) * ((-Complex.I) * Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I))).arg
      = θ / 2 - Real.pi / 2 := by
    have htwo : (2 * (Real.sin (θ / 2) : ℂ)) = ((2 * Real.sin (θ / 2) : ℝ) : ℂ) := by norm_num
    rw [htwo]
    rw [Complex.arg_real_mul _ (by positivity)]
    exact hargW
  calc
    (1 - Complex.exp (θ * Complex.I)).arg
        = ((2 * (Real.sin (θ / 2) : ℂ)) * ((-Complex.I) * Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I))).arg := by
          simpa [harr] using harg.symm
    _ = θ / 2 - Real.pi / 2 := hargR

/-- For `−2π < θ < 0` (so `sin(θ/2) < 0`): principal `arg (1 − e^{iθ}) = θ/2 + π/2`. -/
theorem arg_one_sub_exp_mul_I_neg {θ : ℝ} (hθm : -2 * Real.pi < θ) (hθ0 : θ < 0) :
    (1 - Complex.exp (θ * Complex.I)).arg = θ / 2 + Real.pi / 2 := by
  have hsin : Real.sin (θ / 2) < 0 := by
    exact Real.sin_neg_of_neg_of_neg_pi_lt (by linarith) (by linarith [hθm])
  have hsneg : 0 < -Real.sin (θ / 2) := by linarith
  have hdec := one_sub_exp_mul_I θ
  have harr : 1 - Complex.exp (θ * Complex.I) =
      (2 * (-(Real.sin (θ / 2)) : ℂ)) * (Complex.I * Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I)) := by
    rw [hdec]
    ring
  have harg := congrArg Complex.arg harr
  have h2s : (2 * (-(Real.sin (θ / 2)) : ℂ)) ≠ 0 := by
    exact mul_ne_zero (by norm_num) (by
      exact_mod_cast (ne_of_gt hsneg))
  have hw : Complex.I * Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I) ≠ 0 := by
    exact mul_ne_zero (by simp) (Complex.exp_ne_zero _)
  have hargW : (Complex.I * Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I)).arg = θ / 2 + Real.pi / 2 := by
    have ha1 : Complex.I.arg = Real.pi / 2 := Complex.arg_I
    have ha2 : (Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I)).arg = θ / 2 := by
      have hβ2 : θ / 2 ∈ Set.Ioc (-Real.pi) (-Real.pi + 2 * Real.pi) := by
        constructor <;> linarith
      have hself : toIocMod Real.two_pi_pos (-Real.pi) (θ / 2) = θ / 2 :=
        (toIocMod_eq_self Real.two_pi_pos (a := -Real.pi) (b := (θ / 2))).2 hβ2
      rw [Complex.arg_exp_mul_I (θ / 2), hself]
    have hsum : Complex.I.arg + (Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I)).arg
        ∈ Set.Ioc (-Real.pi) Real.pi := by
      constructor <;> linarith
    rw [Complex.arg_mul (by simp) (Complex.exp_ne_zero _) hsum]
    rw [ha1, ha2]
    ring
  have hargR : ((2 * (-(Real.sin (θ / 2)) : ℂ)) * (Complex.I * Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I))).arg
      = θ / 2 + Real.pi / 2 := by
    have htwo : (2 * (-(Real.sin (θ / 2)) : ℂ)) = ((2 * -Real.sin (θ / 2) : ℝ) : ℂ) := by norm_num
    rw [htwo]
    rw [Complex.arg_real_mul _ (by positivity)]
    exact hargW
  calc
    (1 - Complex.exp (θ * Complex.I)).arg
        = ((2 * (-(Real.sin (θ / 2)) : ℂ)) * (Complex.I * Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I))).arg := by
          simpa [harr] using harg.symm
    _ = θ / 2 + Real.pi / 2 := hargR

/-! ## 3. Circle factor: positive real part / slit plane / nonzero -/

/-- A unit-modulus complex number other than `1` has real part `< 1`. -/
theorem re_lt_one_of_norm_one {w : ℂ} (hw : ‖w‖ = 1) (hw1 : w ≠ 1) : w.re < 1 := by
  have hle : w.re ≤ 1 := by
    calc
      w.re ≤ ‖w‖ := Complex.re_le_norm w
      _ = 1 := hw
  refine lt_of_le_of_ne hle ?_
  intro hre
  apply hw1
  have hns : Complex.normSq w = 1 := by
    rw [Complex.normSq_eq_norm_sq, hw]
    norm_num
  have hsq : w.re * w.re + w.im * w.im = 1 := by
    simpa [Complex.normSq_apply] using hns
  have hsq0 : w.im ^ 2 = 0 := by
    nlinarith
  have him : w.im = 0 := sq_eq_zero_iff.mp hsq0
  apply Complex.ext <;> simp [hre, him]

/-- `‖a·z⁻¹‖ = 1` for unit `a`, unit `z`. -/
theorem norm_mul_inv_of_unit {a z : ℂ} (ha : ‖a‖ = 1) (hz : ‖z‖ = 1) : ‖a * z⁻¹‖ = 1 := by
  rw [norm_mul, norm_inv, ha, hz, inv_one, one_mul]

/-- `a·z⁻¹ = 1 ⟺ a = z` for `z ≠ 0`. -/
theorem mul_inv_eq_one_iff {a z : ℂ} (hz : z ≠ 0) : a * z⁻¹ = 1 ↔ a = z := by
  constructor
  · intro h
    calc
      a = a * (z⁻¹ * z) := by field_simp [hz]
      _ = (a * z⁻¹) * z := by ring
      _ = z := by rw [h, one_mul]
  · intro h
    rw [h]
    field_simp [hz]

/-- For unit `a ≠ unit z`: the circle factor `1 − a·z⁻¹` has positive real part. -/
theorem re_one_sub_inv_pos_of_unit_ne {a z : ℂ} (ha : ‖a‖ = 1) (hz : ‖z‖ = 1)
    (hne : a ≠ z) : 0 < (1 - a * z⁻¹).re := by
  have hz0 : z ≠ 0 := by
    intro hz0
    rw [hz0, norm_zero] at hz
    norm_num at hz
  have hw : ‖a * z⁻¹‖ = 1 := norm_mul_inv_of_unit ha hz
  have hwne : a * z⁻¹ ≠ 1 := by
    intro h
    apply hne
    exact (mul_inv_eq_one_iff hz0).1 h
  have hlt : (a * z⁻¹).re < 1 := re_lt_one_of_norm_one hw hwne
  rw [Complex.sub_re, Complex.one_re]
  linarith

/-- For unit `a`, unit `z`: `Re(1 − a·z⁻¹) ≥ 0` on the circle (equality
only at the junction `a = z`). -/
theorem re_one_sub_inv_nonneg_of_unit {a z : ℂ} (ha : ‖a‖ = 1) (hz : ‖z‖ = 1) :
    0 ≤ (1 - a * z⁻¹).re := by
  by_cases hne : a ≠ z
  · exact le_of_lt (re_one_sub_inv_pos_of_unit_ne ha hz hne)
  · have hz0 : z ≠ 0 := by
      intro hz0
      rw [hz0, norm_zero] at hz
      norm_num at hz
    have haz : a * z⁻¹ = 1 := by
      rw [mul_inv_eq_one_iff hz0]
      exact (not_not.mp hne)
    simp [haz]

/-- For unit `a ≠ unit z`: the circle factor is nonzero. -/
theorem one_sub_inv_ne_zero_of_unit_ne {a z : ℂ} (ha : ‖a‖ = 1) (hz : ‖z‖ = 1)
    (hne : a ≠ z) : 1 - a * z⁻¹ ≠ 0 := by
  intro h0
  have hz0 : z ≠ 0 := by
    intro hz0
    rw [hz0, norm_zero] at hz
    norm_num at hz
  have hx : a * z⁻¹ - 1 = 0 := by
    have hs : a * z⁻¹ - 1 = -(1 - a * z⁻¹) := by ring
    rw [hs, h0]
    simp
  exact hne ((mul_inv_eq_one_iff hz0).1 (eq_of_sub_eq_zero hx))

/-- For unit `a ≠ unit z`: the circle factor lies in the slit plane
(`0 < re`), so principal powers are single-valued/continuous on circle
arcs avoiding the junctions. -/
theorem one_sub_inv_mem_slitPlane_of_unit_ne {a z : ℂ} (ha : ‖a‖ = 1) (hz : ‖z‖ = 1)
    (hne : a ≠ z) : 1 - a * z⁻¹ ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  exact Or.inl (re_one_sub_inv_pos_of_unit_ne ha hz hne)

/-! ## 4. Model-map boundary corollaries -/

open Submission.ModelStarMap

/-- Boundary factor base in the slit plane (away from the junction). -/
theorem modelFactor_boundary_base_mem_slitPlane {a z : ℂ} (ha : ‖a‖ = 1) (hz : ‖z‖ = 1)
    (hne : a ≠ z) : 1 - a * z⁻¹ ∈ Complex.slitPlane :=
  one_sub_inv_mem_slitPlane_of_unit_ne ha hz hne

/-- The model product is nonzero on the unit circle away from all junctions:
`∏_k (1 − z₀ k · z⁻¹)^(2 r k) ≠ 0` when `z` avoids every `z₀ k`. -/
theorem modelProduct_boundary_ne_zero {n : ℕ} (z₀ : Fin n → ℂ) (r : Fin n → ℝ) {z : ℂ}
    (hz : ‖z‖ = 1) (hzj : ∀ k : Fin n, z₀ k ≠ z) :
    modelProduct z₀ r z ≠ 0 := by
  -- the norm factors through; if a factor power vanished, its norm (a
  -- positive-real power of the factor norm) would vanish; factor norm ≠ 0.
  intro h0
  have hnorm : ‖modelProduct z₀ r z‖ = 0 := by rw [h0]; norm_num
  rw [ModelStarMap.norm_modelProduct] at hnorm
  have hfz : ∀ k : Fin n, ‖1 - z₀ k * z⁻¹‖ ^ (2 * r k) ≠ 0 := by
    intro k
    -- ‖1 - z₀k z⁻¹‖ = ‖z - z₀k‖ > 0 (factor norm identity + hzj)
    have hfac : ‖1 - z₀ k * z⁻¹‖ = ‖z - z₀ k‖ := ModelStarMap.norm_factor_unit (a := z₀ k) hz
    rw [hfac]
    have hpos : 0 < ‖z - z₀ k‖ := by
      exact norm_pos_iff.mpr (fun h => hzj k (sub_eq_zero.mp h).symm)
    exact ne_of_gt (Real.rpow_pos_of_pos hpos _)
  have hprod : (∏ k : Fin n, ‖1 - z₀ k * z⁻¹‖ ^ (2 * r k)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro a ha
    exact hfz a
  exact hprod hnorm

/-- `modelF = z · product` is nonzero on the unit circle away from all
junctions and away from `z = 0`. -/
theorem modelF_boundary_ne_zero {n : ℕ} (z₀ : Fin n → ℂ) (r : Fin n → ℝ) {z : ℂ}
    (hz : ‖z‖ = 1) (hzj : ∀ k : Fin n, z₀ k ≠ z) :
    modelF z₀ r z ≠ 0 := by
  intro h0
  have hz0 : z ≠ 0 := by
    intro hz0
    rw [hz0, norm_zero] at hz
    norm_num at hz
  unfold modelF at h0
  exact modelProduct_boundary_ne_zero z₀ r hz hzj (mul_eq_zero.mp h0 |>.resolve_left hz0)

end Submission.ModelStarBoundary

end
