/-
Copyright: the formalization team of the Vinogradov mean value theorem project.
-/
import Submission.Vinogradov.FromDecLin
import Submission.Vinogradov.GaugeBump
import Submission.Commons.Analysis.Inequalities.sum_rpow_le_card_rpow_mul_sum_rpow
import Submission.Commons.Analysis.MomentCurve.exists_box_coeff_gam
import Submission.Commons.Analysis.InnerProductSpace.ball_subset_image_box
import Submission.Commons.Analysis.InnerProductSpace.exists_lower_bound_of_det_gram
import Submission.Commons.Analysis.InnerProductSpace.exists_lower_bound_of_det_gram_quant

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# General curves: plates, decoupling constants, and the moment-curve specialisation

Guo–Li–Yung–Zorin-Kranich, *A short proof of ℓ² decoupling for the moment curve*
(arXiv:1912.09798), §3.3 (Lemma 3.6) and §3.4 (Lemma 3.8) need decoupling inequalities for
curves `γ : [0,1] → ℝ^l` that are *not* the moment curve: they are the images of the moment
curve under the linear maps appearing in the quotient construction of §3.4 (the orthogonal
projection onto the complement of `span{Γ^{(1)}(ξ'), …, Γ^{(k-l)}(ξ')}`), and they satisfy the
torsion condition `|γ^{(1)} ∧ ⋯ ∧ γ^{(l)}| ≳ 1`.

This module sets up the *curve-independent* layer:

* `curvePlateLin l D δ t` — the linear map with `e_i ↦ δ^(i+1) • D^(i+1)(t)`, where `D i t` is
  the `i`-th derivative of the curve at `t` (so the curve is described by its derivative
  family `D : ℕ → ℝ → E l`);
* `curvePlate l D δ t` — the plate `{D 0 t + curvePlateLin l D δ t y | y ∈ [-1,1]^l}`, the
  analogue of `plate` for a general curve;
* `CurveDec l D m lam C` — the `ℓ²`-decoupling inequality at scale `m` for the curve `D`, in
  the `λ`-enlarged plate convention, and the identification
  `CurveDec l (gammaDeriv l) m lam C ↔ DecLinScale l m lam C` with the moment-curve theorem
  of `FromDecLin.lean`.

The point of the general-curve formulation is that decoupling for a curve forces decoupling for
its images: this is exactly GLYZ Lemma 3.6, whose proof is a scale descent in which the curves
at all intermediate scales are again described by the same data `D` (their derivative families
are the images of the moment curve's derivative families), so that no separate theory of
"curves" (differentiability, Taylor expansions of abstract curves) is needed.
-/

noncomputable section
open MeasureTheory Complex Classical Filter
open scoped Real BigOperators Topology RealInnerProductSpace ENNReal NNReal

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.style.emptyLine false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Submission.Vinogradov

/-! ## 1. The plate of a general curve -/

/-- The unit box `[-1,1]^l` in `E l`. -/
def unitBox (l : ℕ) : Set (E l) := {y | ∀ i : Fin l, |y i| ≤ 1}

/-- **The linear part of the plate map of a general curve.**  The curve is described by its
derivative family `D : ℕ → ℝ → E l`; the map sends the standard basis vector `e_i` to
`δ^(i+1) • D^(i+1)(t)`, so that `curvePlateLin l D δ t '' unitBox` is the parallelepiped with
sides `2δ^{i+1}D^{(i+1)}(t)`. -/
noncomputable def curvePlateLin (l : ℕ) (D : ℕ → ℝ → E l) (δ t : ℝ) : E l →ₗ[ℝ] E l where
  toFun y := ∑ i : Fin l, y i • (δ ^ (i.val + 1) • D (i.val + 1) t)
  map_add' := by
    intro y z
    simp only [PiLp.add_apply]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [add_smul]
  map_smul' := by
    intro c y
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [PiLp.smul_apply, smul_eq_mul]
    exact (smul_smul c (y i) (δ ^ (i.val + 1) • D (i.val + 1) t)).symm

/-- Defining equation of `curvePlateLin`. -/
lemma curvePlateLin_apply (l : ℕ) (D : ℕ → ℝ → E l) (δ t : ℝ) (y : E l) :
    curvePlateLin l D δ t y
      = ∑ i : Fin l, y i • (δ ^ (i.val + 1) • D (i.val + 1) t) := rfl

/-- **The plate of a general curve**: the parallelepiped centred at `D 0 t` with sides parallel
to the derivatives `D^{(1)}(t), …, D^{(l)}(t)` and lengths `δ¹, …, δ^l`. -/
def curvePlate (l : ℕ) (D : ℕ → ℝ → E l) (δ t : ℝ) : Set (E l) :=
  (fun y => D 0 t + curvePlateLin l D δ t y) '' unitBox l

/-! ## 2. The moment curve is an instance -/

/-- The plate map of a general curve, for the moment-curve data, is the plate map of the
moment curve. -/
lemma curvePlateLin_gammaDeriv (l : ℕ) (δ t : ℝ) :
    curvePlateLin l (gammaDeriv l) δ t = plateMapLin l δ t := by
  refine LinearMap.ext fun y => ?_
  rw [curvePlateLin_apply, plateMapLin_apply, affVecDual_eq_sum_gammaDeriv]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [diagFact_apply]
  congr 1
  field_simp

/-- **The moment curve's plate is the plate of its derivative family.** -/
@[simp] lemma curvePlate_gammaDeriv (l : ℕ) (δ t : ℝ) :
    curvePlate l (gammaDeriv l) δ t = plate l δ t := by
  have h0 : gammaDeriv l 0 t = gammaVec l t := gammaDeriv_zero l t
  have himg : (fun y => gammaDeriv l 0 t + curvePlateLin l (gammaDeriv l) δ t y) '' unitBox l
      = (fun z => gammaVec l t + z) '' (plateMapLin l δ t '' unitBox l) := by
    rw [← h0, curvePlateLin_gammaDeriv, Set.image_image]
  rw [curvePlate, himg, unitBox, plateMapLin_image_box]
  ext z
  constructor
  · rintro ⟨w, ⟨v, hv, rfl⟩, rfl⟩
    simpa using hv
  · intro hv
    exact ⟨z - gammaVec l t, ⟨z, hv, rfl⟩, by simp⟩

/-! ## 3. The decoupling inequality for a general curve -/

/-- **The `ℓ²`-decoupling inequality for a general curve** at scale `m`, with the plate
enlargement `lam`.  This is GLYZ Definition 1.1 with the moment curve replaced by the curve
described by the derivative family `D`; `CurveDec (gammaDeriv l) m lam C` is exactly
`DecLinScale l m lam C`. -/
def CurveDec (l : ℕ) (D : ℕ → ℝ → E l) (m : ℕ) (lam : ℝ) (C : ℝ≥0∞) : Prop :=
  ∀ f : Fin m → E l → ℂ,
    (∀ j, IsFourierRep l (curvePlate l D (lam / (2 * m)) (pieceCenter m j)) (f j)) →
    lpNorm l (pE l) (fun x => ∑ j, f j x) ≤ C * l2Norm (fun j => lpNorm l (pE l) (f j))

/-- **The moment-curve specialisation**: the general-curve decoupling inequality for the
moment curve's derivative family is the `λ`-enlarged moment-curve decoupling inequality. -/
theorem curveDec_gammaDeriv_iff (l m : ℕ) (lam : ℝ) (C : ℝ≥0∞) :
    CurveDec l (gammaDeriv l) m lam C ↔ DecLinScale l m lam C := by
  simp only [CurveDec, DecLinScale, plateScale, curvePlate_gammaDeriv]

/-- Monotonicity of the general-curve decoupling inequality in the constant. -/
lemma CurveDec.mono {l m : ℕ} {D : ℕ → ℝ → E l} {lam : ℝ} {C C' : ℝ≥0∞} (h : C ≤ C')
    (hD : CurveDec l D m lam C) : CurveDec l D m lam C' :=
  fun f hf => (hD f hf).trans (mul_le_mul_left h _)


/-- The critical exponent of the degree-`l` moment curve is at least `1`. -/
lemma one_le_pE (l : ℕ) (hl : 1 ≤ l) : 1 ≤ pE l := by
  rw [pE]
  have h : 1 ≤ l * (l + 1) := by nlinarith
  exact_mod_cast h

/-- **The trivial decoupling inequality.**  With no hypothesis whatsoever on the tuple, the
`L^{p_l}` norm of the sum is bounded by `m^{1/2}` times the `ℓ²` norm of the pieces: by the
triangle inequality for the `L^p` seminorm (`eLpNorm_sum_le`) and Cauchy–Schwarz.
This is the bound used at the *top* of the scale descent of GLYZ §3.3 (Lemma 3.6). -/
theorem curveDec_trivial (l : ℕ) (hl : 1 ≤ l) (D : ℕ → ℝ → E l) (m : ℕ) (lam : ℝ) :
    CurveDec l D m lam ((m : ℝ≥0∞) ^ (1 / 2 : ℝ)) := by
  intro f hf
  have hp1 : 1 ≤ pE l := one_le_pE l hl
  have h1 : lpNorm l (pE l) (fun x => ∑ j, f j x)
      ≤ ∑ j : Fin m, lpNorm l (pE l) (f j) := by
    have hsum : (fun x => ∑ j : Fin m, f j x) = (∑ j : Fin m, f j) := by
      funext x
      simp only [Finset.sum_apply]
    rw [hsum]
    simp only [lpNorm]
    exact eLpNorm_sum_le (μ := volume) (p := pE l) (s := Finset.univ)
      (f := fun j => f j) hp1
  refine h1.trans ?_
  set a : Fin m → ℝ≥0∞ := fun j => lpNorm l (pE l) (f j)
  have h2 : (∑ j : Fin m, a j) ^ (2 : ℝ)
      ≤ (m : ℝ≥0∞) ^ ((2 : ℝ) - 1) * ∑ j : Fin m, (a j) ^ (2 : ℝ) := by
    have h := Commons.Analysis.Inequalities.sum_rpow_le_card_rpow_mul_sum_rpow
      (Finset.univ : Finset (Fin m)) a (by norm_num : (1 : ℝ) ≤ 2)
    simpa [Finset.card_univ] using h
  have h3 := ENNReal.rpow_le_rpow h2 (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [← ENNReal.rpow_mul, show (2 : ℝ) * (1 / 2) = 1 by norm_num, ENNReal.rpow_one,
    show (2 : ℝ) - 1 = 1 by norm_num, ENNReal.rpow_one,
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)] at h3
  simpa [l2Norm, a] using h3


/-! ## 4. The model plate contains a ball -/

/-- The coordinates of `curvePlateLin`: the `j`-th coordinate of
`curvePlateLin l D δ t y` is `Σ_i y_i · δ^{i+1} · (D^{(i+1)} t)_j`. -/
lemma ofLp_curvePlateLin (l : ℕ) (D : ℕ → ℝ → E l) (δ t : ℝ) (y : E l) :
    WithLp.ofLp (curvePlateLin l D δ t y)
      = fun j => ∑ i : Fin l, y i * (δ ^ (i.val + 1) * D (i.val + 1) t j) := by
  rw [curvePlateLin_apply, WithLp.ofLp_sum]
  funext j
  rw [Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [WithLp.ofLp_smul, PiLp.smul_apply, Pi.smul_apply, smul_eq_mul]

/-- **The plate of the moment curve contains a ball of radius `≍ δ^l`.**  This is the
quantitative non-degeneracy of the moment-curve plate: because the derivative vectors
`Γ^{(i+1)}(u) = Σ_{j≥i} u^{j-i}/(j-i)! Γ^{(j+1)}(0)` form (in the basis `Γ^{(j+1)}(0) = (j+1)!e_j`)
a lower triangular matrix with diagonal `(i+1)!`, the plate map is uniformly invertible with
inverse of norm `≍ δ^{-l}`.  The statement is the `E l`-valued form of the commons lemma
`Commons.Analysis.MomentCurve.exists_box_coeff_gam`. -/
theorem exists_ball_subset_plate (l : ℕ) (hl : 1 ≤ l) :
    ∃ c : ℝ, 0 < c ∧ ∀ (δ u : ℝ), 0 < δ → δ ≤ 1 → |u| ≤ 1 →
      Metric.ball (gammaVec l u) (c * δ ^ l) ⊆ plate l δ u := by
  obtain ⟨c, hc, hbox⟩ := Commons.Analysis.MomentCurve.exists_box_coeff_gam l hl
  refine ⟨c, hc, ?_⟩
  intro δ u hδ0 hδ1 hu x hx
  have hgam : ∀ (i : Fin l) (j : Fin l),
      Commons.Analysis.MomentCurve.gam l u (i.val + 1) j
        = gammaDeriv l (i.val + 1) u j := by
    intro i j
    rw [gammaDeriv_apply, Commons.Analysis.MomentCurve.gam_apply]
  rw [Metric.mem_ball, dist_eq_norm] at hx
  have hcoord : ∀ j : Fin l, |(x - gammaVec l u) j| ≤ c * δ ^ l := by
    intro j
    have h1 : ‖(x - gammaVec l u).ofLp j‖ ≤ ‖x - gammaVec l u‖ := PiLp.norm_apply_le _ j
    rw [Real.norm_eq_abs] at h1
    linarith
  obtain ⟨y, hy, hyz⟩ := hbox δ u hδ0 hδ1 hu (fun j => (x - gammaVec l u) j) hcoord
  set yE : E l := (WithLp.equiv 2 (Fin l → ℝ)).symm y with hyE
  have hyE_coe : ∀ i : Fin l, yE i = y i := fun i => rfl
  have hyvec : curvePlateLin l (gammaDeriv l) δ u yE = x - gammaVec l u := by
    apply WithLp.ofLp_injective
    rw [ofLp_curvePlateLin]
    funext j
    simp only [hyE_coe]
    simpa only [← hgam] using hyz j
  have hmem : x ∈ curvePlate l (gammaDeriv l) δ u := by
    refine ⟨yE, ?_, ?_⟩
    · intro i
      rw [hyE_coe i]
      exact hy i
    · simp only [hyvec, gammaDeriv_zero]
      abel
  rwa [curvePlate_gammaDeriv] at hmem


/-! ## 5. The hypotheses on a curve: boundedness, torsion, Taylor remainder

The general-curve theorem (GLYZ Lemma 3.6) is applied to a curve described by its derivative
family `D : ℕ → ℝ → E l`, and the three hypotheses it uses are the following.  In the
application of §3.4 the curve is `D i t = M (Γ^{(i)}(t))` with `M` the coordinate projection
onto `H = V^{k-l}(ξ')^⊥`; the three properties are transported from the moment curve
(linearity for the Taylor expansion and the boundedness, and
`Commons.Analysis.MomentCurve.projected_torsion_det` for the torsion, which holds for
`|t - ξ'| ≥ 1/4`, i.e. precisely on the interval `I` complementary to `I' ∋ ξ'`). -/

/-- The derivative family `D` of a curve is *coordinate-wise bounded* by `A` on `[0,1]`, up to
order `l+1`.  (A coordinate-wise bound is the convenient form: the moment curve's coordinates are
falling factorials times powers of `t`, and all conversion factors `√l` are absorbed into the
constants of the tower.) -/
def CurveBounded (l : ℕ) (D : ℕ → ℝ → E l) (A : ℝ) : Prop :=
  ∀ i : ℕ, i ≤ l + 1 → ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → ∀ j : Fin l, |D i t j| ≤ A

/-- The derivative family `D` has *torsion* at least `c` on `[0,1]`: the Gram determinant of
`D^{(1)}(t), …, D^{(l)}(t)` is at least `c` for every `t ∈ [0,1]`.  This is GLYZ (3.7)
`|γ^{(1)} ∧ ⋯ ∧ γ^{(l)}| ≳ 1` in determinant form. -/
def CurveTorsion (l : ℕ) (D : ℕ → ℝ → E l) (c : ℝ) : Prop :=
  ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
    c ≤ (Matrix.gram ℝ (fun i : Fin l => D (i.val + 1) t)).det

/-- The *Taylor remainder bound* for the derivative family `D`: truncating the Taylor expansion
of `D^{(i)}` at the point `t` at order `m ≤ l` leaves an error at most `R |u|^{m+1-i}`.  For the
moment curve the expansion is *exact* up to the truncation (it is a polynomial of degree `l`), so
`R ≤ Σ_{j > m} ‖Γ^{(j)}‖/j! ≤ 1` uniformly on `[0,1]`; for the projected curve the same bound
holds by linearity and contractivity. -/
def CurveTaylor (l : ℕ) (D : ℕ → ℝ → E l) (R : ℝ) : Prop :=
  ∀ (i m : ℕ) (t u : ℝ), i ≤ m → m ≤ l → t ∈ Set.Icc (0 : ℝ) 1 → |u| ≤ 1 →
    ‖D i (t + u) - ∑ j ∈ Finset.Icc i m, (u ^ (j - i) / ((j - i).factorial : ℝ)) • D j t‖
      ≤ R * |u| ^ (m + 1 - i)

/-- A coordinate-wise bound gives a norm bound: `‖v‖ ≤ √l · A` when `|v j| ≤ A`. -/
lemma norm_le_sqrt_card_mul_of_coord_le {l : ℕ} (v : E l) {A : ℝ} (hA : 0 ≤ A)
    (h : ∀ j : Fin l, |v j| ≤ A) : ‖v‖ ≤ (l : ℝ).sqrt * A := by
  have hsq : ‖v‖ ^ 2 = ∑ j : Fin l, (v j) ^ 2 := norm_sq_coord_sum l v
  have hsum : ∑ j : Fin l, (v j) ^ 2 ≤ ∑ _j : Fin l, A ^ 2 :=
    Finset.sum_le_sum fun j _ => by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (h j) 2
  have hcard : ∑ _j : Fin l, A ^ 2 = (l : ℝ) * A ^ 2 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h2 : ‖v‖ ^ 2 ≤ (l : ℝ) * A ^ 2 := by
    rw [hsq]
    rw [hcard] at hsum
    exact hsum
  have h3 : ‖v‖ ≤ Real.sqrt ((l : ℝ) * A ^ 2) := by
    rw [← Real.sqrt_sq (norm_nonneg v)]
    exact Real.sqrt_le_sqrt h2
  rwa [Real.sqrt_mul (Nat.cast_nonneg l), Real.sqrt_sq hA] at h3


/-- **Absorption into the coefficients of a plate.**  If the plate map of the curve `D` at scale
`δ` expands norms by at least `c' δ^l` (which is the quantitative form of the torsion of `D`),
then the plate contains the ball of radius `c' δ^l` around the point `D 0 t` of the curve.  The
hypothesis is exactly the conclusion of the commons lemma
`Commons.Analysis.InnerProductSpace.exists_lower_bound_of_det_gram` (in its *quantitative* form,
which is what makes the constant uniform in `t`). -/
theorem ball_subset_curvePlate_of_lower_at {l : ℕ} {D : ℕ → ℝ → E l} {c' t : ℝ}
    (hc' : 0 < c')
    (h : ∀ (δ : ℝ), 0 < δ → δ ≤ 1 → ∀ w : Fin l → ℝ,
      c' * δ ^ l * ‖w‖ ≤ ‖∑ i : Fin l, w i • (δ ^ (i.val + 1) • D (i.val + 1) t)‖) :
    ∀ (δ : ℝ), 0 < δ → δ ≤ 1 →
      Metric.ball (D 0 t) (c' * δ ^ l) ⊆ curvePlate l D δ t := by
  intro δ hδ0 hδ1 x hx
  have hpos : 0 < c' * δ ^ l := mul_pos hc' (pow_pos hδ0 l)
  have hlow : ∀ w : Fin l → ℝ,
      (c' * δ ^ l) * ‖w‖ ≤ ‖∑ i : Fin l, w i • (δ ^ (i.val + 1) • D (i.val + 1) t)‖ :=
    fun w => h δ hδ0 hδ1 w
  have hball := Commons.Analysis.InnerProductSpace.ball_subset_image_box hpos
    (fun i : Fin l => δ ^ (i.val + 1) • D (i.val + 1) t) hlow
  have hx' : x - D 0 t ∈ Metric.ball 0 (c' * δ ^ l) := by
    rw [Metric.mem_ball] at hx ⊢
    rw [dist_eq_norm] at hx ⊢
    simpa using hx
  obtain ⟨w, hw, hweq⟩ := hball hx'
  refine ⟨(WithLp.equiv 2 (Fin l → ℝ)).symm w, fun i => hw i, ?_⟩
  have hcoe : ∀ i : Fin l, (WithLp.equiv 2 (Fin l → ℝ)).symm w i = w i := fun i => rfl
  have hsum : (∑ i : Fin l, (WithLp.equiv 2 (Fin l → ℝ)).symm w i
        • (δ ^ (i.val + 1) • D (i.val + 1) t))
      = ∑ i : Fin l, w i • (δ ^ (i.val + 1) • D (i.val + 1) t) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hcoe i]
  have hweq' : (∑ i : Fin l, w i • (δ ^ (i.val + 1) • D (i.val + 1) t)) = x - D 0 t := hweq
  simp only [curvePlateLin_apply, hsum]
  rw [hweq']
  abel


/-- **Absorption into the coefficients of a plate** (uniform over `t`): the pointwise version
`ball_subset_curvePlate_of_lower_at` assembled over `t ∈ [0,1]`. -/
theorem ball_subset_curvePlate_of_lower {l : ℕ} {D : ℕ → ℝ → E l} {c' : ℝ} (hc' : 0 < c')
    (h : ∀ (δ : ℝ), 0 < δ → δ ≤ 1 → ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ w : Fin l → ℝ,
      c' * δ ^ l * ‖w‖ ≤ ‖∑ i : Fin l, w i • (δ ^ (i.val + 1) • D (i.val + 1) t)‖) :
    ∀ (δ : ℝ), 0 < δ → δ ≤ 1 → ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Metric.ball (D 0 t) (c' * δ ^ l) ⊆ curvePlate l D δ t :=
  fun δ hδ0 hδ1 t ht =>
    ball_subset_curvePlate_of_lower_at hc' (fun δ' hδ0' hδ1' w => h δ' hδ0' hδ1' t ht w)
      δ hδ0 hδ1

/-- **Quantitative lower bound for the plate map of a curve with torsion.**  If the derivative
family `D` is coordinate-wise bounded by `A ≥ 1` on `[0,1]` and has torsion at least `c > 0`
(GLYZ (3.7) in Gram-determinant form), then the plate map at scale `δ` expands norms by at least
a constant times `δ^l`:

`c / (l·(l-1)!·(√l A)^{2l-1}·√l) · δ^l · ‖y‖ ≤ ‖curvePlateLin l D δ t y‖`.

This is the quantitative form of the torsion condition, obtained from the commons lemma
`Commons.Analysis.InnerProductSpace.exists_lower_bound_of_det_gram_quant` (which is uniform in
`t`). -/
theorem curvePlateLin_norm_lower_bound_at {l : ℕ} {D : ℕ → ℝ → E l} {A c t : ℝ}
    (hl : 1 ≤ l) (hc : 0 < c) (hA : 1 ≤ A)
    (hbd : ∀ i : ℕ, i ≤ l + 1 → ∀ j : Fin l, |D i t j| ≤ A)
    (htor : c ≤ (Matrix.gram ℝ (fun i : Fin l => D (i.val + 1) t)).det) :
    ∀ (δ : ℝ), 0 < δ → δ ≤ 1 → ∀ y : E l,
      (c / ((l : ℝ) * ((l - 1).factorial : ℝ) * (Real.sqrt l * A) ^ (2 * l - 1)
          * Real.sqrt l)) * δ ^ l * ‖y‖ ≤ ‖curvePlateLin l D δ t y‖ := by
  intro δ hδ0 hδ1 y
  have hA0 : 0 ≤ A := le_trans zero_le_one hA
  have hδlpos : 0 < δ ^ l := pow_pos hδ0 l
  have hδlne : δ ^ l ≠ 0 := ne_of_gt hδlpos
  have hsqrtl1 : 1 ≤ Real.sqrt l := by
    rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by exact_mod_cast hl)
  have hA' : 1 ≤ Real.sqrt l * A := by
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ Real.sqrt l * A := mul_le_mul hsqrtl1 hA zero_le_one (Real.sqrt_nonneg l)
  have hsA : ∀ i : Fin l, ‖D (i.val + 1) t‖ ≤ Real.sqrt l * A := fun i =>
    norm_le_sqrt_card_mul_of_coord_le (D (i.val + 1) t) hA0
      (fun j => hbd (i.val + 1) (by omega) j)
  set K : ℝ := (l : ℝ) * ((l - 1).factorial : ℝ) * (Real.sqrt l * A) ^ (2 * l - 1) with hKdef
  have hfact : (0 : ℝ) < ((l - 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos (l - 1)
  have hKpos : 0 < K := by
    rw [hKdef]
    exact mul_pos (mul_pos (by exact_mod_cast hl) hfact)
      (pow_pos (lt_of_lt_of_le zero_lt_one hA') _)
  set W : Fin l → ℝ := fun i => y i * (δ ^ (i.val + 1) / δ ^ l) with hWdef
  set U : E l := ∑ i : Fin l, W i • D (i.val + 1) t with hUdef
  have hmain : c * ‖W‖ ≤ K * ‖U‖ := by
    have h := Commons.Analysis.InnerProductSpace.exists_lower_bound_of_det_gram_quant
      hl (fun i : Fin l => D (i.val + 1) t) hc hA' hsA htor W
    rw [hUdef, hKdef]
    exact h
  have hUeq : curvePlateLin l D δ t y = δ ^ l • U := by
    rw [curvePlateLin_apply, hUdef, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, smul_smul]
    congr 1
    simp only [hWdef]
    field_simp
  have hWge : ∀ i : Fin l, |y i| ≤ |W i| := by
    intro i
    have hle : 1 ≤ δ ^ (i.val + 1) / δ ^ l := by
      rw [one_le_div hδlpos]
      exact pow_le_pow_of_le_one hδ0.le hδ1 (by omega : i.val + 1 ≤ l)
    have habs : |δ ^ (i.val + 1) / δ ^ l| = δ ^ (i.val + 1) / δ ^ l :=
      abs_of_nonneg (div_nonneg (pow_nonneg hδ0.le _) hδlpos.le)
    simp only [hWdef, abs_mul, habs]
    exact le_mul_of_one_le_right (abs_nonneg _) hle
  have hysup : ‖(fun i : Fin l => y i)‖ ≤ ‖W‖ := by
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg W)).mpr fun i => ?_
    have h1 : |y i| ≤ |W i| := hWge i
    have h2 : |W i| ≤ ‖W‖ := by simpa using norm_le_pi_norm W i
    exact le_trans h1 h2
  have hnormy : ‖y‖ ≤ Real.sqrt l * ‖(fun i : Fin l => y i)‖ :=
    norm_le_sqrt_card_mul_of_coord_le y (norm_nonneg _)
      (fun j => by simpa using norm_le_pi_norm (fun i : Fin l => y i) j)
  have hylw : ‖y‖ ≤ Real.sqrt l * ‖W‖ :=
    le_trans hnormy (mul_le_mul_of_nonneg_left hysup (Real.sqrt_nonneg l))
  have hstep1 : (c / (K * Real.sqrt l)) * δ ^ l * ‖y‖
      ≤ (c / (K * Real.sqrt l)) * δ ^ l * (Real.sqrt l * ‖W‖) :=
    mul_le_mul_of_nonneg_left hylw (by positivity)
  have hstep2 : (c / (K * Real.sqrt l)) * δ ^ l * (Real.sqrt l * ‖W‖)
      = δ ^ l * (c * ‖W‖) / K := by
    field_simp
  have hstep3 : δ ^ l * (c * ‖W‖) / K ≤ δ ^ l * (K * ‖U‖) / K :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hmain (pow_nonneg hδ0.le l)) hKpos.le
  have hstep4 : δ ^ l * (K * ‖U‖) / K = δ ^ l * ‖U‖ := by
    rw [mul_div_assoc, mul_div_cancel_left₀ _ hKpos.ne']
  have hnormU : ‖curvePlateLin l D δ t y‖ = δ ^ l * ‖U‖ := by
    rw [hUeq, norm_smul, Real.norm_eq_abs, abs_of_pos hδlpos]
  calc (c / (K * Real.sqrt l)) * δ ^ l * ‖y‖
      ≤ (c / (K * Real.sqrt l)) * δ ^ l * (Real.sqrt l * ‖W‖) := hstep1
    _ = δ ^ l * (c * ‖W‖) / K := hstep2
    _ ≤ δ ^ l * (K * ‖U‖) / K := hstep3
    _ = δ ^ l * ‖U‖ := hstep4
    _ = ‖curvePlateLin l D δ t y‖ := hnormU.symm


/-- **Quantitative lower bound for the plate map of a curve with torsion** (uniform over `t`):
the pointwise version `curvePlateLin_norm_lower_bound_at` for a `D` that is coordinate-wise
bounded and has torsion everywhere on `[0,1]`. -/
theorem curvePlateLin_norm_lower_bound {l : ℕ} {D : ℕ → ℝ → E l} {A c : ℝ}
    (hl : 1 ≤ l) (hc : 0 < c) (hA : 1 ≤ A)
    (hbd : CurveBounded l D A) (htor : CurveTorsion l D c) :
    ∀ (δ : ℝ), 0 < δ → δ ≤ 1 → ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y : E l,
      (c / ((l : ℝ) * ((l - 1).factorial : ℝ) * (Real.sqrt l * A) ^ (2 * l - 1)
          * Real.sqrt l)) * δ ^ l * ‖y‖ ≤ ‖curvePlateLin l D δ t y‖ :=
  fun δ hδ0 hδ1 t ht y =>
    curvePlateLin_norm_lower_bound_at hl hc hA (fun i hi j => hbd i hi t ht j) (htor t ht)
      δ hδ0 hδ1 y


/-- **The plate of a curve with torsion contains a ball of radius `≍ δ^l`.**  This is the
absorption step of GLYZ Lemma 3.6 ((G2) in the project's plan): the Taylor remainder of the
curve is `O(κ^{l+1})`, the shortest side of a plate of side length `κ^{(l+1)/l}` is
`(κ^{(l+1)/l})^l = κ^{l+1}`, and this lemma says precisely that a ball of that radius fits
inside the plate. -/
theorem exists_ball_subset_curvePlate_of_torsion {l : ℕ} {D : ℕ → ℝ → E l} {A c : ℝ}
    (hl : 1 ≤ l) (hc : 0 < c) (hA : 1 ≤ A) (hbd : CurveBounded l D A)
    (htor : CurveTorsion l D c) :
    ∃ c' : ℝ, 0 < c' ∧ ∀ (δ : ℝ), 0 < δ → δ ≤ 1 → ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Metric.ball (D 0 t) (c' * δ ^ l) ⊆ curvePlate l D δ t := by
  set c' : ℝ := c / ((l : ℝ) * ((l - 1).factorial : ℝ) * (Real.sqrt l * A) ^ (2 * l - 1)
    * Real.sqrt l) with hc'def
  have hA0 : 0 ≤ A := le_trans zero_le_one hA
  have hfact : (0 : ℝ) < ((l - 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos (l - 1)
  have hsqrtl1 : 1 ≤ Real.sqrt l := by
    rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by exact_mod_cast hl)
  have hsqrtlpos : 0 < Real.sqrt l := lt_of_lt_of_le zero_lt_one hsqrtl1
  have hKpos : 0 < (l : ℝ) * ((l - 1).factorial : ℝ) * (Real.sqrt l * A) ^ (2 * l - 1)
      * Real.sqrt l := by
    have h1 : 0 < (l : ℝ) * ((l - 1).factorial : ℝ) :=
      mul_pos (by exact_mod_cast hl) hfact
    have hA' : 1 ≤ Real.sqrt l * A := by
      calc (1 : ℝ) = 1 * 1 := by ring
        _ ≤ Real.sqrt l * A := mul_le_mul hsqrtl1 hA zero_le_one (Real.sqrt_nonneg l)
    exact mul_pos (mul_pos h1 (pow_pos (lt_of_lt_of_le zero_lt_one hA') _)) hsqrtlpos
  have hc'pos : 0 < c' := by
    rw [hc'def]; exact div_pos hc hKpos
  refine ⟨c', hc'pos, ?_⟩
  refine ball_subset_curvePlate_of_lower hc'pos fun δ hδ0 hδ1 t ht w => ?_
  have hw : ‖w‖ ≤ ‖((WithLp.equiv 2 (Fin l → ℝ)).symm w : E l)‖ := by
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i => ?_
    have hcoe : ((WithLp.equiv 2 (Fin l → ℝ)).symm w : E l) i = w i := rfl
    have h := PiLp.norm_apply_le ((WithLp.equiv 2 (Fin l → ℝ)).symm w : E l) i
    rw [hcoe] at h
    simpa using h
  have hlin : curvePlateLin l D δ t ((WithLp.equiv 2 (Fin l → ℝ)).symm w : E l)
      = ∑ i : Fin l, w i • (δ ^ (i.val + 1) • D (i.val + 1) t) := by
    rw [curvePlateLin_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hcoe : ((WithLp.equiv 2 (Fin l → ℝ)).symm w : E l) i = w i := rfl
    rw [hcoe]
  have hlow := curvePlateLin_norm_lower_bound hl hc hA hbd htor δ hδ0 hδ1 t ht
    ((WithLp.equiv 2 (Fin l → ℝ)).symm w : E l)
  rw [hlin] at hlow
  calc c' * δ ^ l * ‖w‖ ≤ c' * δ ^ l * ‖((WithLp.equiv 2 (Fin l → ℝ)).symm w : E l)‖ :=
        mul_le_mul_of_nonneg_left hw (mul_nonneg hc'pos.le (pow_nonneg hδ0.le l))
    _ ≤ ‖∑ i : Fin l, w i • (δ ^ (i.val + 1) • D (i.val + 1) t)‖ := hlow


/-- **Pointwise form of the ball inside the plate.**  For a derivative family `D` that is
coordinate-wise bounded by `A ≥ 1` at `t` and has torsion at least `c > 0` at `t`, the plate
`curvePlate l D δ t` contains the ball of radius `c' δ^l` around `D 0 t`, where

`c' = c / (l·(l-1)!·(√l A)^{2l-1}·√l)`

is *explicit* — this is what makes the constant uniform in the application to the projected
curve, where the torsion hypothesis only holds on part of `[0,1]`. -/
theorem ball_subset_curvePlate_of_bounded_torsion_at {l : ℕ} {D : ℕ → ℝ → E l} {A c t : ℝ}
    (hl : 1 ≤ l) (hc : 0 < c) (hA : 1 ≤ A)
    (hbd : ∀ i : ℕ, i ≤ l + 1 → ∀ j : Fin l, |D i t j| ≤ A)
    (htor : c ≤ (Matrix.gram ℝ (fun i : Fin l => D (i.val + 1) t)).det) :
    ∀ (δ : ℝ), 0 < δ → δ ≤ 1 →
      Metric.ball (D 0 t) ((c / ((l : ℝ) * ((l - 1).factorial : ℝ) * (Real.sqrt l * A) ^ (2 * l - 1)
          * Real.sqrt l)) * δ ^ l) ⊆ curvePlate l D δ t := by
  have hA0 : 0 ≤ A := le_trans zero_le_one hA
  have hfact : (0 : ℝ) < ((l - 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos (l - 1)
  have hsqrtl1 : 1 ≤ Real.sqrt l := by
    rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by exact_mod_cast hl)
  have hsqrtlpos : 0 < Real.sqrt l := lt_of_lt_of_le zero_lt_one hsqrtl1
  have hKpos : 0 < (l : ℝ) * ((l - 1).factorial : ℝ) * (Real.sqrt l * A) ^ (2 * l - 1)
      * Real.sqrt l := by
    have h1 : 0 < (l : ℝ) * ((l - 1).factorial : ℝ) :=
      mul_pos (by exact_mod_cast hl) hfact
    have hA' : 1 ≤ Real.sqrt l * A := by
      calc (1 : ℝ) = 1 * 1 := by ring
        _ ≤ Real.sqrt l * A := mul_le_mul hsqrtl1 hA zero_le_one (Real.sqrt_nonneg l)
    exact mul_pos (mul_pos h1 (pow_pos (lt_of_lt_of_le zero_lt_one hA') _)) hsqrtlpos
  have hc'pos : 0 < c / ((l : ℝ) * ((l - 1).factorial : ℝ) * (Real.sqrt l * A) ^ (2 * l - 1)
      * Real.sqrt l) := div_pos hc hKpos
  refine ball_subset_curvePlate_of_lower_at (D := D)
    (c' := c / ((l : ℝ) * ((l - 1).factorial : ℝ) * (Real.sqrt l * A) ^ (2 * l - 1)
      * Real.sqrt l)) hc'pos fun δ hδ0 hδ1 w => ?_
  have hlow := curvePlateLin_norm_lower_bound_at hl hc hA hbd htor δ hδ0 hδ1
    ((WithLp.equiv 2 (Fin l → ℝ)).symm w : E l)
  have hw : ‖w‖ ≤ ‖((WithLp.equiv 2 (Fin l → ℝ)).symm w : E l)‖ := by
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i => ?_
    have hcoe : ((WithLp.equiv 2 (Fin l → ℝ)).symm w : E l) i = w i := rfl
    have h := PiLp.norm_apply_le ((WithLp.equiv 2 (Fin l → ℝ)).symm w : E l) i
    rw [hcoe] at h
    simpa using h
  have hlin : curvePlateLin l D δ t ((WithLp.equiv 2 (Fin l → ℝ)).symm w : E l)
      = ∑ i : Fin l, w i • (δ ^ (i.val + 1) • D (i.val + 1) t) := by
    rw [curvePlateLin_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hcoe : ((WithLp.equiv 2 (Fin l → ℝ)).symm w : E l) i = w i := rfl
    rw [hcoe]
  rw [hlin] at hlow
  calc (c / ((l : ℝ) * ((l - 1).factorial : ℝ) * (Real.sqrt l * A) ^ (2 * l - 1)
          * Real.sqrt l)) * δ ^ l * ‖w‖
      ≤ (c / ((l : ℝ) * ((l - 1).factorial : ℝ) * (Real.sqrt l * A) ^ (2 * l - 1)
          * Real.sqrt l)) * δ ^ l * ‖((WithLp.equiv 2 (Fin l → ℝ)).symm w : E l)‖ :=
        mul_le_mul_of_nonneg_left hw (mul_nonneg hc'pos.le (pow_nonneg hδ0.le l))
    _ ≤ ‖∑ i : Fin l, w i • (δ ^ (i.val + 1) • D (i.val + 1) t)‖ := hlow


/-- **Enlarging the plate.**  `curvePlate l D δ t ⊆ curvePlate l D δ' t` for `0 ≤ δ ≤ δ'`:
the box absorbs the change of scale, with coefficients rescaled by `(δ/δ')^{i+1}`.  (No
non-degeneracy of `D` is needed.) -/
lemma curvePlate_mono {l : ℕ} {D : ℕ → ℝ → E l} {δ δ' t : ℝ} (hδ : 0 ≤ δ) (hδδ : δ ≤ δ') :
    curvePlate l D δ t ⊆ curvePlate l D δ' t := by
  rcases eq_or_lt_of_le hδδ with h | h
  · rw [h]
  have hδ'pos : 0 < δ' := lt_of_le_of_lt hδ h
  rintro x ⟨y, hy, hxy⟩
  have hq_nonneg : 0 ≤ δ / δ' := div_nonneg hδ hδ'pos.le
  have hq_le : δ / δ' ≤ 1 := (div_le_one hδ'pos).mpr hδδ
  refine ⟨(WithLp.equiv 2 (Fin l → ℝ)).symm
    (fun i => y i * (δ / δ') ^ (i.val + 1)), ?_, ?_⟩
  · intro i
    have hcoe : ((WithLp.equiv 2 (Fin l → ℝ)).symm
        (fun i => y i * (δ / δ') ^ (i.val + 1))) i = y i * (δ / δ') ^ (i.val + 1) := rfl
    rw [hcoe, abs_mul]
    have h1 : |(δ / δ') ^ (i.val + 1)| ≤ 1 := by
      rw [abs_of_nonneg (pow_nonneg hq_nonneg _)]
      exact pow_le_one₀ hq_nonneg hq_le
    calc |y i| * |(δ / δ') ^ (i.val + 1)| ≤ 1 * 1 :=
          mul_le_mul (hy i) h1 (abs_nonneg _) (by norm_num)
      _ = 1 := by ring
  · have hcoe : ∀ i : Fin l, ((WithLp.equiv 2 (Fin l → ℝ)).symm
        (fun i => y i * (δ / δ') ^ (i.val + 1))) i = y i * (δ / δ') ^ (i.val + 1) :=
      fun i => rfl
    have hsum : (∑ i : Fin l, ((WithLp.equiv 2 (Fin l → ℝ)).symm
          (fun i => y i * (δ / δ') ^ (i.val + 1))) i • (δ' ^ (i.val + 1) • D (i.val + 1) t))
        = ∑ i : Fin l, y i • (δ ^ (i.val + 1) • D (i.val + 1) t) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      have hs : (δ / δ') ^ (i.val + 1) * δ' ^ (i.val + 1) = δ ^ (i.val + 1) := by
        rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero _ hδ'pos.ne')]
      rw [hcoe i, smul_smul, mul_assoc, hs, ← smul_smul]
    have hold : curvePlateLin l D δ t y
        = ∑ i : Fin l, y i • (δ ^ (i.val + 1) • D (i.val + 1) t) :=
      curvePlateLin_apply l D δ t y
    have hold' : curvePlateLin l D δ' t ((WithLp.equiv 2 (Fin l → ℝ)).symm
        (fun i => y i * (δ / δ') ^ (i.val + 1)))
        = ∑ i : Fin l, ((WithLp.equiv 2 (Fin l → ℝ)).symm
            (fun i => y i * (δ / δ') ^ (i.val + 1))) i • (δ' ^ (i.val + 1) • D (i.val + 1) t) :=
      curvePlateLin_apply l D δ' t _
    change D 0 t + curvePlateLin l D δ' t ((WithLp.equiv 2 (Fin l → ℝ)).symm
      (fun i => y i * (δ / δ') ^ (i.val + 1))) = x
    have hxy' : D 0 t + curvePlateLin l D δ t y = x := hxy
    rw [← hxy', hold', hsum, hold]

/-! ## 6. Reparametrisation of a curve: restricting to a subinterval

`CurveBounded`, `CurveTorsion` and `CurveTaylor` are stated on `[0,1]`, while the curves that
GLYZ's §3.4 feeds into the general-curve theorem live on a dyadic subinterval `[a, a+c] ⊆ [0,1]`
(for the projected moment curve the torsion only holds away from `ξ'`).  The reparametrisation

`intervalCurve l a c D i σ = c^i • D i (a + cσ)`

is the derivative family of `σ ↦ D 0 (a + cσ)`, so that the pieces of `[0,1]` (in `σ`)
correspond to the pieces of `[a, a+c]` (in `t`), and — crucially — the plates are the *same
sets*, so every `IsFourierRep` statement transports by rewriting alone. -/

/-- The derivative family of the reparametrised curve `σ ↦ D 0 (a + cσ)`. -/
noncomputable def intervalCurve (l : ℕ) (a c : ℝ) (D : ℕ → ℝ → E l) : ℕ → ℝ → E l :=
  fun i σ => c ^ i • D i (a + c * σ)

lemma intervalCurve_apply (l : ℕ) (a c : ℝ) (D : ℕ → ℝ → E l) (i : ℕ) (σ : ℝ) :
    intervalCurve l a c D i σ = c ^ i • D i (a + c * σ) := rfl

/-- **The plate of the reparametrised curve is the plate of the original curve** at the
corresponding point and with the scale multiplied by `c`. -/
lemma curvePlate_intervalCurve (l : ℕ) (a c : ℝ) (D : ℕ → ℝ → E l) (δ σ : ℝ) :
    curvePlate l (intervalCurve l a c D) δ σ = curvePlate l D (c * δ) (a + c * σ) := by
  have hfun : (fun y : E l => intervalCurve l a c D 0 σ
        + curvePlateLin l (intervalCurve l a c D) δ σ y)
      = (fun y : E l => D 0 (a + c * σ) + curvePlateLin l D (c * δ) (a + c * σ) y) := by
    funext y
    congr 1
    · rw [intervalCurve_apply, pow_zero, one_smul]
    · rw [curvePlateLin_apply, curvePlateLin_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [intervalCurve_apply]
      congr 1
      rw [smul_smul]
      congr 1
      rw [mul_pow]
      ring
  rw [curvePlate, curvePlate, hfun]

/-- **`CurveDec` transports to the reparametrised curve** by a pure rewriting, since the plates
are the same sets (`curvePlate_intervalCurve`).  The right-hand side is the explicit form used
when the general-curve theorem is applied on a subinterval `[a, a+c] ⊆ [0,1]`. -/
lemma curveDec_intervalCurve_iff (l : ℕ) (a c : ℝ) (D : ℕ → ℝ → E l) (m : ℕ) (lam : ℝ)
    (C : ℝ≥0∞) :
    CurveDec l (intervalCurve l a c D) m lam C ↔
      ∀ f : Fin m → E l → ℂ,
        (∀ j, IsFourierRep l
          (curvePlate l D (c * (lam / (2 * m))) (a + c * pieceCenter m j)) (f j)) →
        lpNorm l (pE l) (fun x => ∑ j, f j x) ≤ C * l2Norm (fun j => lpNorm l (pE l) (f j)) := by
  simp only [CurveDec, curvePlate_intervalCurve]




/-! ## 7. The moment curve's coordinate bound (moved here from `Projection.lean`) -/

/-- The coordinates of `gammaDeriv k i t` are bounded by `k!` for `|t| ≤ 1`. -/
lemma gammaDeriv_coord_abs_le (k : ℕ) {t : ℝ} (ht : |t| ≤ 1) (i : ℕ) (j : Fin k) :
    |gammaDeriv k i t j| ≤ (k.factorial : ℝ) := by
  rw [gammaDeriv_apply, abs_mul]
  have hj : j.val + 1 ≤ k := by have := j.isLt; omega
  have h1 : (((j.val + 1).descFactorial i : ℕ) : ℝ) ≤ (k.factorial : ℝ) := by
    have h2 : (j.val + 1).descFactorial i ≤ (j.val + 1).factorial := by
      by_cases h : i ≤ j.val + 1
      · rw [Nat.descFactorial_eq_div h]; exact Nat.div_le_self _ _
      · rw [not_le] at h
        rw [Nat.descFactorial_eq_zero_iff_lt.mpr h]; exact Nat.zero_le _
    have h3 : (j.val + 1).factorial ≤ k.factorial := Nat.factorial_le hj
    exact_mod_cast le_trans h2 h3
  have h4 : |t ^ (j.val + 1 - i)| ≤ 1 := by
    rw [abs_pow]; exact pow_le_one₀ (abs_nonneg t) ht
  have hd0 : (0 : ℝ) ≤ (((j.val + 1).descFactorial i : ℕ) : ℝ) := Nat.cast_nonneg _
  have hk0 : (0 : ℝ) ≤ (k.factorial : ℝ) := Nat.cast_nonneg _
  calc |(((j.val + 1).descFactorial i : ℕ) : ℝ)| * |t ^ (j.val + 1 - i)|
      = (((j.val + 1).descFactorial i : ℕ) : ℝ) * |t ^ (j.val + 1 - i)| := by
        rw [abs_of_nonneg hd0]
    _ ≤ (k.factorial : ℝ) * 1 := mul_le_mul h1 h4 (abs_nonneg _) hk0
    _ = (k.factorial : ℝ) := by ring

/-- The moment curve's derivative family is coordinate-wise bounded by `l!` on `[0,1]`. -/
lemma CurveBounded_gammaDeriv (l : ℕ) : CurveBounded l (gammaDeriv l) (l.factorial : ℝ) := by
  intro i _ t ht j
  exact gammaDeriv_coord_abs_le l (by rw [abs_of_nonneg ht.1]; exact ht.2) i j


/-! ## 8. Transport of the curve hypotheses under reparametrisation

The reparametrisation `intervalCurve` of §6 is used to run the general-curve theorem on a
subinterval `[a,a+c] ⊆ [0,1]`.  Here we record how the three curve hypotheses transport:

* `CurveBounded` is preserved with the same constant `A` (for `0 ≤ c ≤ 1`);
* `CurveTorsion` loses the factor `c^{l(l+1)}` (the Gram determinant scales by
  `∏ᵢ c^{2(i+1)} = c^{l(l+1)}`);
* `CurveTaylor` is preserved with the same `R` (`0 ≤ c ≤ 1`, `0 ≤ R`), because after scaling by
  `c^i` the Taylor remainder of the reparametrised curve is *exactly* the original remainder at
  the displaced point `τ + c·u`. -/

/-- A coordinate-wise bound is preserved by reparametrisation (with the same constant, for
`0 ≤ c ≤ 1`). -/
lemma CurveBounded_intervalCurve {l : ℕ} {D : ℕ → ℝ → E l} {A a c : ℝ}
    (hD : CurveBounded l D A) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (ha0 : 0 ≤ a) (hac : a + c ≤ 1) :
    CurveBounded l (intervalCurve l a c D) A := by
  intro i hi σ hσ j
  have hσ0 : 0 ≤ σ := hσ.1
  have hσ1 : σ ≤ 1 := hσ.2
  have ht : a + c * σ ∈ Set.Icc (0 : ℝ) 1 := ⟨by nlinarith, by nlinarith⟩
  rw [intervalCurve_apply, PiLp.smul_apply, smul_eq_mul, abs_mul]
  have h1 : |c ^ i| ≤ 1 := by
    rw [abs_of_nonneg (pow_nonneg hc0 i)]
    exact pow_le_one₀ hc0 hc1
  calc |c ^ i| * |D i (a + c * σ) j| ≤ 1 * A :=
        mul_le_mul h1 (hD i hi _ ht j) (abs_nonneg _) zero_le_one
    _ = A := by ring

/-- The Gram matrix of the diagonally scaled family `c^{i+1} v_i`. -/
lemma gram_smul_diag {l : ℕ} (c : ℝ) (v : Fin l → E l) :
    Matrix.gram ℝ (fun i : Fin l => c ^ (i.val + 1) • v i)
      = (Matrix.diagonal fun i : Fin l => c ^ (i.val + 1)) * Matrix.gram ℝ v
        * (Matrix.diagonal fun i : Fin l => c ^ (i.val + 1)) := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.gram_apply,
    real_inner_smul_left, real_inner_smul_right, ite_mul, mul_ite, zero_mul, mul_zero,
    Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true,
    Finset.sum_const_zero]
  ring

/-- `2 · (1 + 2 + ⋯ + l) = l(l+1)`. -/
lemma two_mul_sum_fin_succ_val (l : ℕ) :
    2 * (∑ i : Fin l, (i.val + 1)) = l * (l + 1) := by
  induction l with
  | zero => simp
  | succ n ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [mul_add, ih]
      ring

/-- A torsion bound is preserved by reparametrisation, with the Gram determinant scaled by
`c^{l(l+1)}`. -/
lemma CurveTorsion_intervalCurve {l : ℕ} {D : ℕ → ℝ → E l} {c₀ a c : ℝ}
    (hD : CurveTorsion l D c₀) (hc0 : 0 ≤ c) (ha0 : 0 ≤ a) (hac : a + c ≤ 1) {σ : ℝ}
    (hσ : σ ∈ Set.Icc (0 : ℝ) 1) :
    c₀ * c ^ (l * (l + 1)) ≤ (Matrix.gram ℝ
      (fun i : Fin l => intervalCurve l a c D (i.val + 1) σ)).det := by
  have ht : a + c * σ ∈ Set.Icc (0 : ℝ) 1 := ⟨by nlinarith [hσ.1], by nlinarith [hσ.2]⟩
  have hfun : (fun i : Fin l => intervalCurve l a c D (i.val + 1) σ)
      = fun i : Fin l => c ^ (i.val + 1) • D (i.val + 1) (a + c * σ) := by
    funext i
    rw [intervalCurve_apply]
  set S : ℕ := ∑ i : Fin l, (i.val + 1) with hS
  have hSS : S + S = l * (l + 1) := by
    rw [hS, ← two_mul]
    exact two_mul_sum_fin_succ_val l
  have hpow : c ^ (l * (l + 1)) = c ^ S * c ^ S := by
    rw [← hSS, pow_add]
  have hdet : (Matrix.gram ℝ (fun i : Fin l => intervalCurve l a c D (i.val + 1) σ)).det
      = c ^ S * (Matrix.gram ℝ fun i : Fin l => D (i.val + 1) (a + c * σ)).det * c ^ S := by
    simp only [hfun, gram_smul_diag, Matrix.det_mul, Matrix.det_diagonal,
      Finset.prod_pow_eq_pow_sum, hS]
  rw [hdet, hpow]
  calc c₀ * (c ^ S * c ^ S)
      ≤ (Matrix.gram ℝ fun i : Fin l => D (i.val + 1) (a + c * σ)).det * (c ^ S * c ^ S) :=
        mul_le_mul_of_nonneg_right (hD _ ht) (mul_self_nonneg _)
    _ = c ^ S * (Matrix.gram ℝ fun i : Fin l => D (i.val + 1) (a + c * σ)).det * c ^ S := by
        ring

/-- **The torsion bound is preserved by reparametrisation, LOCALISED to a subinterval**: only the
torsion on `[a, a+c]` is needed.  This is the form used for the projected curve of GLYZ §3.4, whose
torsion is only known for `|t − ξ'| ≥ 1/4`. -/
lemma CurveTorsion_intervalCurve_of {l : ℕ} {D : ℕ → ℝ → E l} {c₀ a c : ℝ}
    (hD : ∀ t ∈ Set.Icc a (a + c),
      c₀ ≤ (Matrix.gram ℝ (fun i : Fin l => D (i.val + 1) t)).det)
    (hc0 : 0 ≤ c) (ha0 : 0 ≤ a) (hac : a + c ≤ 1) {σ : ℝ} (hσ : σ ∈ Set.Icc (0 : ℝ) 1) :
    c₀ * c ^ (l * (l + 1)) ≤ (Matrix.gram ℝ
      (fun i : Fin l => intervalCurve l a c D (i.val + 1) σ)).det := by
  have ht : a + c * σ ∈ Set.Icc a (a + c) := ⟨by nlinarith [hσ.1], by nlinarith [hσ.2]⟩
  have hfun : (fun i : Fin l => intervalCurve l a c D (i.val + 1) σ)
      = fun i : Fin l => c ^ (i.val + 1) • D (i.val + 1) (a + c * σ) := by
    funext i
    rw [intervalCurve_apply]
  set S : ℕ := ∑ i : Fin l, (i.val + 1) with hS
  have hSS : S + S = l * (l + 1) := by
    rw [hS, ← two_mul]
    exact two_mul_sum_fin_succ_val l
  have hpow : c ^ (l * (l + 1)) = c ^ S * c ^ S := by
    rw [← hSS, pow_add]
  have hdet : (Matrix.gram ℝ (fun i : Fin l => intervalCurve l a c D (i.val + 1) σ)).det
      = c ^ S * (Matrix.gram ℝ fun i : Fin l => D (i.val + 1) (a + c * σ)).det * c ^ S := by
    simp only [hfun, gram_smul_diag, Matrix.det_mul, Matrix.det_diagonal,
      Finset.prod_pow_eq_pow_sum, hS]
  rw [hdet, hpow]
  calc c₀ * (c ^ S * c ^ S)
      ≤ (Matrix.gram ℝ fun i : Fin l => D (i.val + 1) (a + c * σ)).det * (c ^ S * c ^ S) :=
        mul_le_mul_of_nonneg_right (hD _ ht) (mul_self_nonneg _)
    _ = c ^ S * (Matrix.gram ℝ fun i : Fin l => D (i.val + 1) (a + c * σ)).det * c ^ S := by
        ring

/-- The Taylor remainder bound is preserved by reparametrisation with the same constant, for
`0 ≤ c ≤ 1` and `0 ≤ R`. -/
lemma CurveTaylor_intervalCurve {l : ℕ} {D : ℕ → ℝ → E l} {R a c : ℝ}
    (hD : CurveTaylor l D R) (hR : 0 ≤ R) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (ha0 : 0 ≤ a)
    (hac : a + c ≤ 1) : CurveTaylor l (intervalCurve l a c D) R := by
  intro i m σ u hi hm hσ hu
  have ht : a + c * σ ∈ Set.Icc (0 : ℝ) 1 := ⟨by nlinarith [hσ.1], by nlinarith [hσ.2]⟩
  have hcu : |c * u| ≤ 1 := by
    rw [abs_mul]
    calc |c| * |u| = c * |u| := by rw [abs_of_nonneg hc0]
      _ ≤ c * 1 := mul_le_mul_of_nonneg_left hu hc0
      _ = c := mul_one c
      _ ≤ 1 := hc1
  have hD' := hD i m (a + c * σ) (c * u) hi hm ht hcu
  have hkey : (∑ j ∈ Finset.Icc i m, (u ^ (j - i) / ((j - i).factorial : ℝ))
        • (intervalCurve l a c D j σ))
      = c ^ i • (∑ j ∈ Finset.Icc i m, (((c * u) ^ (j - i)) / ((j - i).factorial : ℝ))
          • D j (a + c * σ)) := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hij : i ≤ j := (Finset.mem_Icc.mp hj).1
    have hci : c ^ i * c ^ (j - i) = c ^ j := by rw [← pow_add]; congr 1; omega
    have hscal : (u ^ (j - i) / ((j - i).factorial : ℝ)) * c ^ j
        = c ^ i * ((c * u) ^ (j - i) / ((j - i).factorial : ℝ)) := by
      rw [mul_pow, ← hci]
      ring
    show (u ^ (j - i) / ((j - i).factorial : ℝ)) • (c ^ j • D j (a + c * σ))
        = c ^ i • (((c * u) ^ (j - i) / ((j - i).factorial : ℝ)) • D j (a + c * σ))
    rw [smul_smul, hscal, smul_smul]
  rw [hkey]
  have hleft : intervalCurve l a c D i (σ + u) - c ^ i
      • (∑ j ∈ Finset.Icc i m, (((c * u) ^ (j - i)) / ((j - i).factorial : ℝ))
          • D j (a + c * σ))
      = c ^ i • (D i ((a + c * σ) + c * u)
          - ∑ j ∈ Finset.Icc i m, (((c * u) ^ (j - i)) / ((j - i).factorial : ℝ))
              • D j (a + c * σ)) := by
    rw [intervalCurve_apply, ← smul_sub, show a + c * (σ + u) = (a + c * σ) + c * u by ring]
  rw [hleft, norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hc0 i)]
  have hci : c ^ i ≤ 1 := pow_le_one₀ hc0 hc1
  have hcu' : |c * u| ^ (m + 1 - i) ≤ |u| ^ (m + 1 - i) := by
    rw [abs_mul, abs_of_nonneg hc0]
    refine pow_le_pow_left₀ (mul_nonneg hc0 (abs_nonneg u)) ?_ _
    calc c * |u| ≤ 1 * |u| := mul_le_mul_of_nonneg_right hc1 (abs_nonneg u)
      _ = |u| := one_mul _
  calc c ^ i * ‖D i ((a + c * σ) + c * u)
        - ∑ j ∈ Finset.Icc i m, (((c * u) ^ (j - i)) / ((j - i).factorial : ℝ))
            • D j (a + c * σ)‖
      ≤ c ^ i * (R * |c * u| ^ (m + 1 - i)) :=
        mul_le_mul_of_nonneg_left hD' (pow_nonneg hc0 i)
    _ ≤ 1 * (R * |u| ^ (m + 1 - i)) :=
        mul_le_mul hci (mul_le_mul_of_nonneg_left hcu' hR) (by positivity) zero_le_one
    _ = R * |u| ^ (m + 1 - i) := by ring


end Submission.Vinogradov
