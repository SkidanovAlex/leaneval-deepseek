/-
Copyright: the formalization team of the Vinogradov mean value theorem project.
-/
import Submission.Vinogradov.CurveLayer

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The straightening map of a general curve (GLYZ §3.3)

This module starts the formalisation of the *general-curve* layer of the scale descent
(GLYZ Lemma 3.6, `Descent.lean`).  For a curve described by its derivative family
`D : ℕ → ℝ → E l` and a base point `t₀`, the **straightening map** is the affine map

  `curveAff l D ρ t₀ x = D 0 t₀ + ∑ i, x i • ((i+1)!)⁻¹ • (ρ^(i+1) • D (i+1) t₀)`

whose linear part has `e_i ↦ ((i+1)!)⁻¹ ρ^{i+1} D^{(i+1)}(t₀)`.  It is the exact analogue of
`Plate.affMap` for the moment curve (`curveAffLin l (gammaDeriv l) ρ t₀ = affVecDual l ρ t₀`),
and its virtue is that it maps the *moment curve* onto the *Taylor polynomial* of `D 0` at `t₀`:

* `curveAff_gammaVec` : `D 0 t₀ + curveAffLin l D ρ t₀ (γ(t)) = T(t₀ + ρ t)`  (order 0),
* `curveAffLin_gammaDeriv` : `curveAffLin l D ρ t₀ (γ^{(r)}(t)) = ρ^r • T^{(r)}(t₀ + ρ t)`
  (`r ≥ 1`),

where `T` is the degree-`l` Taylor polynomial of `D 0` at `t₀` and `taylorDeriv l D t₀ r` is the
derivative family of `T`.

The geometric consequence — the analogue of `Plate.affMap_image_plate` — is

* `curveAff_image_plate` :
  `curveAff l D ρ t₀ '' plate l δ c = curvePlate l (taylorDeriv l D t₀) (ρ * δ) (t₀ + ρ * c)`.
-/

noncomputable section
open MeasureTheory Complex Classical Filter
open scoped Real BigOperators Topology RealInnerProductSpace ENNReal NNReal

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.style.emptyLine false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

namespace Submission.Vinogradov

/-! ## 1. The straightening map -/

/-- The linear part of the straightening map of a curve at `t₀` and scale `ρ`:
`e_i ↦ ((i+1)!)⁻¹ ρ^(i+1) D^(i+1)(t₀)`. -/
noncomputable def curveAffLin (l : ℕ) (D : ℕ → ℝ → E l) (ρ t₀ : ℝ) : E l →ₗ[ℝ] E l where
  toFun x := ∑ i : Fin l,
    x i • (((i.val + 1).factorial : ℝ)⁻¹ • (ρ ^ (i.val + 1) • D (i.val + 1) t₀))
  map_add' := by
    intro x y
    simp only [PiLp.add_apply]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [add_smul]
  map_smul' := by
    intro a x
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [PiLp.smul_apply, smul_eq_mul, smul_smul, mul_assoc, RingHom.id_apply]

/-- Defining equation of `curveAffLin`. -/
lemma curveAffLin_apply (l : ℕ) (D : ℕ → ℝ → E l) (ρ t₀ : ℝ) (x : E l) :
    curveAffLin l D ρ t₀ x = ∑ i : Fin l,
      x i • (((i.val + 1).factorial : ℝ)⁻¹ • (ρ ^ (i.val + 1) • D (i.val + 1) t₀)) := rfl

/-- The straightening (affine) map of the curve `D 0` at `t₀` with scale `ρ`. -/
noncomputable def curveAff (l : ℕ) (D : ℕ → ℝ → E l) (ρ t₀ : ℝ) (x : E l) : E l :=
  D 0 t₀ + curveAffLin l D ρ t₀ x

/-- The derivative family of the degree-`l` Taylor polynomial of the curve `D 0` at `t₀`:
`taylorDeriv l D t₀ i t` is the `i`-th derivative at `t` of `∑_{j ≤ l} (s-t₀)^j/j! D j t₀`. -/
noncomputable def taylorDeriv (l : ℕ) (D : ℕ → ℝ → E l) (t₀ : ℝ) : ℕ → ℝ → E l :=
  fun i t => ∑ j ∈ Finset.Icc i l, (((t - t₀) ^ (j - i)) / ((j - i).factorial : ℝ)) • D j t₀

lemma taylorDeriv_apply (l : ℕ) (D : ℕ → ℝ → E l) (t₀ : ℝ) (i : ℕ) (t : ℝ) :
    taylorDeriv l D t₀ i t
      = ∑ j ∈ Finset.Icc i l, (((t - t₀) ^ (j - i)) / ((j - i).factorial : ℝ)) • D j t₀ := rfl

lemma taylorDeriv_zero (l : ℕ) (D : ℕ → ℝ → E l) (t₀ t : ℝ) :
    taylorDeriv l D t₀ 0 t
      = ∑ j ∈ Finset.Icc 0 l, (((t - t₀) ^ j) / (j.factorial : ℝ)) • D j t₀ := by
  rw [taylorDeriv_apply]
  simp

/-! ## 2. Two reindexing lemmas for sums over `Fin l` and `Icc 1 l` -/

lemma sum_Icc_one_eq_sum_fin {M : Type*} [AddCommMonoid M] (l : ℕ) (g : ℕ → M) :
    (∑ m ∈ Finset.Icc 1 l, g m) = ∑ i : Fin l, g (i.val + 1) := by
  refine Finset.sum_bij (fun (m : ℕ) (hm : m ∈ Finset.Icc 1 l) => (⟨m - 1, ?_⟩ : Fin l))
    ?_ ?_ ?_ ?_
  · have := Finset.mem_Icc.mp hm
    omega
  · intro m _
    exact Finset.mem_univ _
  · intro m hm m' hm' heq
    have h1 := Finset.mem_Icc.mp hm
    have h2 := Finset.mem_Icc.mp hm'
    have h3 : m - 1 = m' - 1 := congrArg Fin.val heq
    omega
  · intro i _
    refine ⟨i.val + 1, ?_, ?_⟩
    · exact Finset.mem_Icc.mpr ⟨by omega, by have := i.isLt; omega⟩
    · exact Fin.ext (by simp)
  · intro m hm
    have h1 := Finset.mem_Icc.mp hm
    congr 1
    change m = m - 1 + 1
    omega

lemma sum_Icc_zero_eq {M : Type*} [AddCommMonoid M] (l : ℕ) (g : ℕ → M) :
    (∑ m ∈ Finset.Icc 0 l, g m) = g 0 + ∑ m ∈ Finset.Icc 1 l, g m := by
  induction l with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_Icc_succ_top (show 0 ≤ n + 1 by omega),
        Finset.sum_Icc_succ_top (show 1 ≤ n + 1 by omega), ih]
      abel

/-! ## 3. The straightening identities -/

/-- The scalar core of `curveAff_gammaVec`: `t^(i+1)·((i+1)!)⁻¹·ρ^(i+1) = (ρt)^(i+1)/(i+1)!`. -/
lemma coord_term_gammaVec (ρ t : ℝ) (i : ℕ) :
    t ^ (i + 1) * (((i + 1).factorial : ℝ))⁻¹ * ρ ^ (i + 1)
      = (ρ * t) ^ (i + 1) / (((i + 1).factorial : ℝ)) := by
  rw [mul_pow]
  ring

/-- **Order `0` of the straightening identity**: the straightening map sends the moment curve to
the Taylor polynomial of the curve at `t₀`. -/
lemma curveAff_gammaVec (l : ℕ) (D : ℕ → ℝ → E l) (ρ t₀ t : ℝ) :
    D 0 t₀ + curveAffLin l D ρ t₀ (gammaVec l t) = taylorDeriv l D t₀ 0 (t₀ + ρ * t) := by
  ext j
  have hL : (D 0 t₀ + curveAffLin l D ρ t₀ (gammaVec l t)) j
      = (D 0 t₀) j + ∑ i : Fin l,
          (gammaVec l t) i * (ρ ^ (i.val + 1) * ((i.val + 1).factorial : ℝ)⁻¹)
            * (D (i.val + 1) t₀) j := by
    rw [PiLp.add_apply, curveAffLin_apply]
    congr 1
    rw [WithLp.ofLp_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [PiLp.smul_apply, smul_eq_mul]
    ring
  have hR : (taylorDeriv l D t₀ 0 (t₀ + ρ * t)) j
      = (D 0 t₀) j + ∑ i : Fin l,
          ((ρ * t) ^ (i.val + 1) / ((i.val + 1).factorial : ℝ)) * (D (i.val + 1) t₀) j := by
    rw [taylorDeriv_zero, WithLp.ofLp_sum, Finset.sum_apply]
    rw [sum_Icc_zero_eq (l := l) (g := fun m =>
      (((t₀ + ρ * t - t₀) ^ m / (m.factorial : ℝ)) • D m t₀) j)]
    rw [sum_Icc_one_eq_sum_fin (l := l) (g := fun m =>
      (((t₀ + ρ * t - t₀) ^ m / (m.factorial : ℝ)) • D m t₀) j)]
    refine congrArg₂ (· + ·) ?_ ?_
    · simp
    · refine Finset.sum_congr rfl fun i _ => ?_
      simp only [PiLp.smul_apply, smul_eq_mul]
      rw [show t₀ + ρ * t - t₀ = ρ * t by ring]
  rw [hL, hR]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [gammaVec_apply, mul_pow]
  ring

/-- The scalar core of `curveAffLin_gammaDeriv`: for `r ≤ m`,
`(m^{↓r} : ℝ) · (m!)⁻¹ = ((m-r)!)⁻¹`. -/
lemma descFactorial_mul_factorial_inv {m r : ℕ} (h : r ≤ m) :
    ((m.descFactorial r : ℕ) : ℝ) * ((m.factorial : ℕ) : ℝ)⁻¹
      = (((m - r).factorial : ℕ) : ℝ)⁻¹ := by
  have h1 : ((m - r).factorial : ℝ) * ((m.descFactorial r : ℕ) : ℝ) = (m.factorial : ℝ) := by
    have := Nat.factorial_mul_descFactorial h
    exact_mod_cast this
  have h2 : (((m - r).factorial : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp at h1 ⊢
  linarith [h1]

/-- Scalar bookkeeping for the left-hand side of `curveAffLin_gammaDeriv`. -/
lemma coeff_form_L (ρ t : ℝ) (m r : ℕ) (w : ℝ) :
    (((m.descFactorial r : ℕ) : ℝ) * t ^ (m - r) * (((m.factorial : ℕ) : ℝ)⁻¹ * (ρ ^ m * w)))
      = ((((m.descFactorial r : ℕ) : ℝ) * ((m.factorial : ℕ) : ℝ)⁻¹)
          * (t ^ (m - r) * ρ ^ m)) * w := by
  ring

/-- Scalar bookkeeping for the right-hand side of `curveAffLin_gammaDeriv`. -/
lemma coeff_form_R (ρ t : ℝ) {m r : ℕ} (h : r ≤ m) (w : ℝ) :
    ρ ^ r * ((ρ * t) ^ (m - r) / (((m - r).factorial : ℕ) : ℝ) * w)
      = (t ^ (m - r) * ρ ^ m) * ((((m - r).factorial : ℕ) : ℝ))⁻¹ * w := by
  have hpow : ρ ^ m = ρ ^ r * ρ ^ (m - r) := by
    rw [← pow_add, Nat.add_sub_cancel' h]
  rw [div_eq_mul_inv, mul_pow, hpow]
  ring

/-- **The straightening identity for derivatives**: the linear part of the straightening map sends
`γ^{(r)}(t)` to `ρ^r T^{(r)}(t₀ + ρ t)` (`r ≥ 1`). -/
lemma curveAffLin_gammaDeriv (l : ℕ) (D : ℕ → ℝ → E l) (ρ t₀ t : ℝ) (r : ℕ) (hr : 1 ≤ r) :
    curveAffLin l D ρ t₀ (gammaDeriv l r t)
      = ρ ^ r • taylorDeriv l D t₀ r (t₀ + ρ * t) := by
  ext j
  have hL : (curveAffLin l D ρ t₀ (gammaDeriv l r t)) j
      = ∑ i : Fin l, (((((i.val + 1).descFactorial r : ℕ) : ℝ)
            * ((i.val + 1).factorial : ℝ)⁻¹) * (t ^ (i.val + 1 - r) * ρ ^ (i.val + 1)))
          * (D (i.val + 1) t₀) j := by
    rw [curveAffLin_apply]
    rw [WithLp.ofLp_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [PiLp.smul_apply, smul_eq_mul, gammaDeriv_apply]
    rw [coeff_form_L ρ t (i.val + 1) r ((D (i.val + 1) t₀) j)]
  have hR : (ρ ^ r • taylorDeriv l D t₀ r (t₀ + ρ * t)) j
      = ∑ m ∈ Finset.Icc r l,
          (t ^ (m - r) * ρ ^ m) * ((((m - r).factorial : ℕ) : ℝ))⁻¹ * (D m t₀) j := by
    rw [PiLp.smul_apply, smul_eq_mul, taylorDeriv_apply, WithLp.ofLp_sum, Finset.sum_apply]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [Finset.mem_Icc] at hm
    simp only [PiLp.smul_apply, smul_eq_mul]
    rw [show t₀ + ρ * t - t₀ = ρ * t by ring,
      coeff_form_R (ρ := ρ) (t := t) hm.1 ((D m t₀) j)]
  rw [hL, hR]
  rw [← sum_Icc_one_eq_sum_fin (l := l) (g := fun m =>
    ((((m.descFactorial r : ℕ) : ℝ) * ((m.factorial : ℕ) : ℝ)⁻¹) * (t ^ (m - r) * ρ ^ m))
      * (D m t₀) j)]
  have hsub : Finset.Icc r l ⊆ Finset.Icc 1 l := by
    intro m hm
    rw [Finset.mem_Icc] at hm ⊢
    omega
  rw [← Finset.sum_subset hsub ?_]
  · refine Finset.sum_congr rfl fun m hm => ?_
    rw [Finset.mem_Icc] at hm
    rw [descFactorial_mul_factorial_inv (m := m) (r := r) hm.1]
    ring
  · intro m hm hmnot
    rw [Finset.mem_Icc] at hm
    rw [Finset.mem_Icc] at hmnot
    push_neg at hmnot
    have hlt : (m.descFactorial r) = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
    rw [hlt]
    simp

/-! ## 4. The geometric consequence: the image of a plate is the plate of the Taylor polynomial -/

/-- **The straightening map sends the moment-curve plate to the plate of the Taylor polynomial.**

This is the exact analogue of `Plate.affMap_image_plate` for a general curve: it is what allows the
model theorem (stated for the moment curve) to be applied on the straightened curve. -/
theorem curveAff_image_plate (l : ℕ) (D : ℕ → ℝ → E l) (ρ t₀ δ c : ℝ) :
    curveAff l D ρ t₀ '' plate l δ c
      = curvePlate l (taylorDeriv l D t₀) (ρ * δ) (t₀ + ρ * c) := by
  rw [← curvePlate_gammaDeriv l δ c, curvePlate, curvePlate, Set.image_image]
  congr 1
  funext y
  have hkey : curveAff l D ρ t₀ (gammaDeriv l 0 c + curvePlateLin l (gammaDeriv l) δ c y)
      = taylorDeriv l D t₀ 0 (t₀ + ρ * c)
        + curvePlateLin l (taylorDeriv l D t₀) (ρ * δ) (t₀ + ρ * c) y := by
    rw [gammaDeriv_zero, curveAff, map_add, ← add_assoc, curveAff_gammaVec]
    congr 1
    rw [curvePlateLin_apply, map_sum, curvePlateLin_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hscal : y i * δ ^ (i.val + 1) * ρ ^ (i.val + 1) = y i * (ρ * δ) ^ (i.val + 1) := by
      rw [mul_pow]
      ring
    rw [map_smul, map_smul, curveAffLin_gammaDeriv l D ρ t₀ c (i.val + 1) (by omega),
      smul_smul, smul_smul, smul_smul, hscal]
  exact hkey

/-! ## 5. The straightening map expands norms: the ball inside the straightened plate -/

/-- The diagonal scaling `y ↦ (y_i / (i+1)!)` on `E l`. -/
noncomputable def diagInv (l : ℕ) : E l →ₗ[ℝ] E l where
  toFun x := (WithLp.equiv 2 (Fin l → ℝ)).symm (fun i => ((i.val + 1).factorial : ℝ)⁻¹ * x i)
  map_add' x y := by
    ext i
    change ((i.val + 1).factorial : ℝ)⁻¹ * (x + y).ofLp i
      = ((i.val + 1).factorial : ℝ)⁻¹ * x.ofLp i
        + ((i.val + 1).factorial : ℝ)⁻¹ * y.ofLp i
    rw [show (x + y).ofLp i = x.ofLp i + y.ofLp i from rfl, mul_add]
  map_smul' c x := by
    ext i
    change ((i.val + 1).factorial : ℝ)⁻¹ * (c • x).ofLp i
      = c * (((i.val + 1).factorial : ℝ)⁻¹ * x.ofLp i)
    rw [show (c • x).ofLp i = c * x.ofLp i from rfl]
    ring

/-- Defining equation of `diagInv`. -/
lemma diagInv_apply (l : ℕ) (x : E l) (i : Fin l) :
    diagInv l x i = ((i.val + 1).factorial : ℝ)⁻¹ * x i := rfl

/-- The straightening linear map is the plate map of the curve composed with the diagonal
scaling `y_i ↦ y_i/(i+1)!`. -/
lemma curveAffLin_eq_curvePlateLin (l : ℕ) (D : ℕ → ℝ → E l) (ρ t₀ : ℝ) (x : E l) :
    curveAffLin l D ρ t₀ x = curvePlateLin l D ρ t₀ (diagInv l x) := by
  rw [curveAffLin_apply, curvePlateLin_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [diagInv_apply, smul_smul, mul_comm (x i) (((i.val + 1).factorial : ℝ))⁻¹]

/-- The diagonal scaling `diagInv` loses at most the factor `l!`. -/
lemma norm_diagInv_lower (l : ℕ) (x : E l) :
    ((l.factorial : ℝ))⁻¹ * ‖x‖ ≤ ‖diagInv l x‖ := by
  have hl : (0 : ℝ) < (l.factorial : ℝ) := by positivity
  have hsq : (((l.factorial : ℝ))⁻¹ * ‖x‖) ^ 2 ≤ ‖diagInv l x‖ ^ 2 := by
    rw [mul_pow, norm_sq_coord_sum l x, norm_sq_coord_sum l (diagInv l x), Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have hi : i.val + 1 ≤ l := by have := i.isLt; omega
    have h1 : ((i.val + 1).factorial : ℝ) ≤ (l.factorial : ℝ) := by
      exact_mod_cast Nat.factorial_le hi
    have h2 : (0 : ℝ) < ((i.val + 1).factorial : ℝ) := by positivity
    have hinv : ((l.factorial : ℝ))⁻¹ ≤ (((i.val + 1).factorial : ℝ))⁻¹ :=
      (inv_le_inv₀ hl h2).mpr h1
    rw [diagInv_apply]
    calc (((l.factorial : ℝ))⁻¹) ^ 2 * (x i) ^ 2
        = (((l.factorial : ℝ))⁻¹ * |x i|) ^ 2 := by rw [mul_pow, sq_abs]
      _ ≤ ((((i.val + 1).factorial : ℝ))⁻¹ * |x i|) ^ 2 := by
          refine pow_le_pow_left₀ (by positivity) ?_ 2
          exact mul_le_mul_of_nonneg_right hinv (abs_nonneg _)
      _ = ((((i.val + 1).factorial : ℝ))⁻¹ * x i) ^ 2 := by
        rw [mul_pow, sq_abs]
        ring
  have h3 : (0 : ℝ) ≤ ((l.factorial : ℝ))⁻¹ * ‖x‖ := by positivity
  nlinarith [hsq, h3, norm_nonneg (diagInv l x)]

/-- **The straightening map expands norms.**  Under the (quantitative) torsion and boundedness
hypotheses on the curve, the linear part of the straightening map satisfies

  `c_Λ ‖y‖ ≤ ‖curveAffLin l D ρ t₀ y‖`,   `c_Λ = (c/K_l)·ρ^l·(l!)⁻¹`,

where `K_l = l·(l-1)!·(√l·A)^(2l-1)·√l` is the constant of
`curvePlateLin_norm_lower_bound_at`.  This is what allows the ball of the moment-curve plate to be
transported to a ball inside the straightened plate. -/
lemma curveAffLin_norm_lower_bound {l : ℕ} {D : ℕ → ℝ → E l} {A c ρ t₀ : ℝ}
    (hl : 1 ≤ l) (hc : 0 < c) (hA : 1 ≤ A)
    (hbd : ∀ i : ℕ, i ≤ l + 1 → ∀ j : Fin l, |D i t₀ j| ≤ A)
    (htor : c ≤ (Matrix.gram ℝ (fun i : Fin l => D (i.val + 1) t₀)).det)
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (y : E l) :
    (c / ((l : ℝ) * ((l - 1).factorial : ℝ) * (Real.sqrt l * A) ^ (2 * l - 1)
        * Real.sqrt l) * ρ ^ l * ((l.factorial : ℝ))⁻¹) * ‖y‖
      ≤ ‖curveAffLin l D ρ t₀ y‖ := by
  rw [curveAffLin_eq_curvePlateLin]
  have h1 := curvePlateLin_norm_lower_bound_at (D := D) (A := A) (c := c) (t := t₀)
    hl hc hA hbd htor ρ hρ0 hρ1 (diagInv l y)
  have h2 := norm_diagInv_lower l y
  have h3 : (0 : ℝ) ≤ c / ((l : ℝ) * ((l - 1).factorial : ℝ) * (Real.sqrt l * A) ^ (2 * l - 1)
      * Real.sqrt l) * ρ ^ l := by positivity
  calc (c / ((l : ℝ) * ((l - 1).factorial : ℝ) * (Real.sqrt l * A) ^ (2 * l - 1)
        * Real.sqrt l) * ρ ^ l * ((l.factorial : ℝ))⁻¹) * ‖y‖
      = (c / ((l : ℝ) * ((l - 1).factorial : ℝ) * (Real.sqrt l * A) ^ (2 * l - 1)
        * Real.sqrt l) * ρ ^ l) * (((l.factorial : ℝ))⁻¹ * ‖y‖) := by ring
    _ ≤ (c / ((l : ℝ) * ((l - 1).factorial : ℝ) * (Real.sqrt l * A) ^ (2 * l - 1)
        * Real.sqrt l) * ρ ^ l) * ‖diagInv l y‖ :=
        mul_le_mul_of_nonneg_left h2 h3
    _ ≤ ‖curvePlateLin l D ρ t₀ (diagInv l y)‖ := h1


/-- **The moment-curve ball transported by the straightening map.**  The moment-curve plate
contains a ball of radius `cb·δ^l` around its centre (`exists_ball_subset_plate`); pushing it
through the straightening map (whose linear part expands norms by `c_Λ`,
`curveAffLin_norm_lower_bound`) produces a ball of radius `cb·c_Λ·δ^l` inside the straightened
plate, with `c_Λ = (c/K_l)·ρ^l·(l!)⁻¹`. -/
theorem exists_ball_subset_curveAff_plate (l : ℕ) (hl : 1 ≤ l) :
    ∃ cb : ℝ, 0 < cb ∧ ∀ (D : ℕ → ℝ → E l) (A c ρ t₀ δ c' : ℝ), 0 < c → 1 ≤ A → 0 < ρ → ρ ≤ 1 →
      0 < δ → δ ≤ 1 → |c'| ≤ 1 →
      (∀ i : ℕ, i ≤ l + 1 → ∀ j : Fin l, |D i t₀ j| ≤ A) →
      c ≤ (Matrix.gram ℝ (fun i : Fin l => D (i.val + 1) t₀)).det →
      Metric.ball (curveAff l D ρ t₀ (gammaVec l c'))
        (cb * (c / ((l : ℝ) * ((l - 1).factorial : ℝ) * (Real.sqrt l * A) ^ (2 * l - 1)
          * Real.sqrt l) * ρ ^ l * ((l.factorial : ℝ))⁻¹ * δ ^ l))
        ⊆ curveAff l D ρ t₀ '' plate l δ c' := by
  obtain ⟨cb, hcb, hball⟩ := exists_ball_subset_plate l hl
  refine ⟨cb, hcb, ?_⟩
  intro D A c ρ t₀ δ c' hc hA hρ0 hρ1 hδ0 hδ1 hc' hbd htor
  set cΛ : ℝ := c / ((l : ℝ) * ((l - 1).factorial : ℝ) * (Real.sqrt l * A) ^ (2 * l - 1)
    * Real.sqrt l) * ρ ^ l * ((l.factorial : ℝ))⁻¹ with hcΛ
  have hΛpos : 0 < cΛ := by rw [hcΛ]; positivity
  have hexp : ∀ y : E l, cΛ * ‖y‖ ≤ ‖curveAffLin l D ρ t₀ y‖ := by
    intro y
    rw [hcΛ]
    exact curveAffLin_norm_lower_bound hl hc hA hbd htor hρ0 hρ1 y
  have hinj : Function.Injective (curveAffLin l D ρ t₀) := by
    intro x y hxy
    have h : curveAffLin l D ρ t₀ (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have h2 := hexp (x - y)
    rw [h, norm_zero] at h2
    have h3 : ‖x - y‖ = 0 := by
      refine le_antisymm ?_ (norm_nonneg _)
      by_contra hcont
      push_neg at hcont
      have h4 : 0 < cΛ * ‖x - y‖ := mul_pos hΛpos hcont
      linarith
    exact sub_eq_zero.mp (norm_eq_zero.mp h3)
  have hsurj : Function.Surjective (curveAffLin l D ρ t₀) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (rfl : Module.finrank ℝ (E l) = Module.finrank ℝ (E l))).mp hinj
  intro z hz
  rw [Metric.mem_ball, dist_eq_norm] at hz
  obtain ⟨u, hu⟩ := hsurj (z - curveAff l D ρ t₀ (gammaVec l c'))
  have hnorm : cΛ * ‖u‖ < cb * (cΛ * δ ^ l) := by
    have h3 := hexp u
    rw [hu] at h3
    refine lt_of_le_of_lt h3 ?_
    rw [hcΛ]
    exact hz
  have hupper : ‖u‖ < cb * δ ^ l := by
    have h6 : cΛ * ‖u‖ < cΛ * (cb * δ ^ l) := by
      have h7 : cb * (cΛ * δ ^ l) = cΛ * (cb * δ ^ l) := by ring
      linarith [hnorm, h7]
    exact lt_of_mul_lt_mul_left h6 hΛpos.le
  refine ⟨gammaVec l c' + u, ?_, ?_⟩
  · apply hball δ c' hδ0 hδ1 hc'
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
    exact hupper
  · rw [curveAff, map_add, hu, curveAff]
    abel

end Submission.Vinogradov



