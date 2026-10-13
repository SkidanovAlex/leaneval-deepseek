/-
# `Work.FTS.PressureOn.vorticity_cross_eq` — the curl of the cross product

`curl (u ⨯ ω) = (div ω) u - (div u) ω + (ω · ∇)u - (u · ∇)ω`, i.e. at a point `x` where both `u`
and `ω` are differentiable,

  `vorticity (fun y => crossVec (u y) (ω y)) x
     = div ω x • u x - div u x • ω x + fderiv ℝ u x (ω x) - fderiv ℝ ω x (u x)`.

This is the pointwise identity needed for the vorticity form of the Euler equation
(`∂ₜω + (u·∇)ω = (ω·∇)u`, equivalently `∂ₜω = curl(u × ω)`), cf. `Defs.lean`
(`PressureReconstructionOn` takes the pointwise vorticity equation on `Uax` as a hypothesis).

The proof is the classical ε-δ contraction, but organised so that no coordinate computation is
needed: writing `e i = WithLp.toLp 2 (Pi.single i 1)` for the standard basis of `ℝ³`,

* `vorticity g x = ∑ i, e i ⨯₃ fderiv ℝ g x (e i)` (definition),
* `fderiv ℝ (fun y => crossVec (u y) (ω y)) x (e i)
     = crossVec (fderiv ℝ u x (e i)) (ω x) + crossVec (u x) (fderiv ℝ ω x (e i))`
  (the pointwise cross product is a bounded bilinear map, `vorticityCross_isBoundedBilinearMap`),
* `e i ⨯₃ (a ⨯₃ b) = (e i ⬝ a) b - (a ⬝ e i) b'`-type expansions: the scalar triple product identity
  `cross_cross_eq_smul_sub_smul'`,
* `e i ⬝ v = v i` (`vorticityCross_dot_e_left/right`) and `∑ i, v i • e i = v`,
* `div g x = ∑ i, (fderiv ℝ g x (e i)) i` (`vorticityCross_div_eq_sum_diag`, trace in the basis `e`).

Summing the resulting four families over `i` and using the basis expansion gives the identity.
-/
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.Trace
import Submission.Work.FTS.PressureOn.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity
open scoped Matrix

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.FTS.PressureOn

/-! ## The norm bound and bilinearity of the cross product -/

/-- On `ℝ³ = EuclideanSpace ℝ (Fin 3)` the inner product is the (Euclidean) dot product of the
underlying coordinate functions. -/
private lemma inner_eq_dotProduct (a b : R3) : inner ℝ a b = WithLp.ofLp a ⬝ᵥ WithLp.ofLp b := by
  rw [PiLp.inner_apply, dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  rw [RCLike.inner_apply]
  simp [mul_comm]

/-- The (unfolded) cross product of two vectors of `ℝ³`. -/
private lemma ofLp_crossVec (a b : R3) :
    WithLp.ofLp (crossVec a b) = WithLp.ofLp a ⨯₃ WithLp.ofLp b := rfl

/-- **The norm bound for the cross product**: `‖a ⨯ b‖ ≤ ‖a‖ ‖b‖`.  It follows from the Binet–Cauchy
identity `(a ⨯ b) ⬝ (a ⨯ b) = (a ⬝ a)(b ⬝ b) - (a ⬝ b)²`. -/
lemma vorticityCross_norm_crossVec_le (a b : R3) : ‖crossVec a b‖ ≤ ‖a‖ * ‖b‖ := by
  have h1 : ‖crossVec a b‖ ^ 2
      = (WithLp.ofLp a ⨯₃ WithLp.ofLp b) ⬝ᵥ (WithLp.ofLp a ⨯₃ WithLp.ofLp b) := by
    rw [← real_inner_self_eq_norm_sq, inner_eq_dotProduct]
    rfl
  have h2 : (WithLp.ofLp a ⨯₃ WithLp.ofLp b) ⬝ᵥ (WithLp.ofLp a ⨯₃ WithLp.ofLp b)
      = (WithLp.ofLp a ⬝ᵥ WithLp.ofLp a) * (WithLp.ofLp b ⬝ᵥ WithLp.ofLp b)
        - (WithLp.ofLp a ⬝ᵥ WithLp.ofLp b) * (WithLp.ofLp b ⬝ᵥ WithLp.ofLp a) :=
    cross_dot_cross _ _ _ _
  have h3 : WithLp.ofLp a ⬝ᵥ WithLp.ofLp a = ‖a‖ ^ 2 := by
    rw [← inner_eq_dotProduct, real_inner_self_eq_norm_sq]
  have h4 : WithLp.ofLp b ⬝ᵥ WithLp.ofLp b = ‖b‖ ^ 2 := by
    rw [← inner_eq_dotProduct, real_inner_self_eq_norm_sq]
  have h5 : (WithLp.ofLp a ⬝ᵥ WithLp.ofLp b) * (WithLp.ofLp b ⬝ᵥ WithLp.ofLp a) =
      (inner ℝ a b) ^ 2 := by
    rw [dotProduct_comm (WithLp.ofLp b), ← inner_eq_dotProduct a b]
    ring
  have h6 : ‖crossVec a b‖ ^ 2 ≤ (‖a‖ * ‖b‖) ^ 2 := by
    rw [h1, h2, h3, h4, h5]
    nlinarith [sq_nonneg (inner ℝ a b)]
  have h7 : ‖crossVec a b‖ ≤ Real.sqrt ((‖a‖ * ‖b‖) ^ 2) :=
    (Real.le_sqrt (by positivity) (by positivity)).2 h6
  rwa [Real.sqrt_sq (by positivity)] at h7

/-- **The cross product is a bounded bilinear map** on `ℝ³`.  (The only non-formal ingredient is the
norm bound `vorticityCross_norm_crossVec_le`; the algebraic laws are those of `crossProduct`.) -/
lemma vorticityCross_isBoundedBilinearMap :
    IsBoundedBilinearMap ℝ (fun p : R3 × R3 => crossVec p.1 p.2) where
  add_left x₁ x₂ y := by
    change WithLp.toLp 2 (WithLp.ofLp (x₁ + x₂) ⨯₃ WithLp.ofLp y)
      = WithLp.toLp 2 (WithLp.ofLp x₁ ⨯₃ WithLp.ofLp y)
        + WithLp.toLp 2 (WithLp.ofLp x₂ ⨯₃ WithLp.ofLp y)
    rw [WithLp.ofLp_add, map_add, LinearMap.add_apply, WithLp.toLp_add]
  smul_left c x y := by
    change WithLp.toLp 2 ((c • WithLp.ofLp x) ⨯₃ WithLp.ofLp y)
      = c • WithLp.toLp 2 (WithLp.ofLp x ⨯₃ WithLp.ofLp y)
    rw [map_smul, LinearMap.smul_apply, WithLp.toLp_smul]
  add_right x y₁ y₂ := by
    change WithLp.toLp 2 (WithLp.ofLp x ⨯₃ WithLp.ofLp (y₁ + y₂))
      = WithLp.toLp 2 (WithLp.ofLp x ⨯₃ WithLp.ofLp y₁)
        + WithLp.toLp 2 (WithLp.ofLp x ⨯₃ WithLp.ofLp y₂)
    rw [WithLp.ofLp_add, map_add, WithLp.toLp_add]
  smul_right c x y := by
    change WithLp.toLp 2 (WithLp.ofLp x ⨯₃ (c • WithLp.ofLp y))
      = c • WithLp.toLp 2 (WithLp.ofLp x ⨯₃ WithLp.ofLp y)
    rw [map_smul, WithLp.toLp_smul]
  bound := ⟨1, one_pos, fun x y => by rw [one_mul]; exact vorticityCross_norm_crossVec_le x y⟩

/-! ## The derivative of a pointwise cross product -/

/-- **Product rule for the cross product**: at a point where `u` and `ω` are differentiable, the
derivative of `y ↦ u y ⨯ ω y` in the direction `e i` is
`(fderiv u x (e i)) ⨯ ω x + u x ⨯ (fderiv ω x (e i))`. -/
lemma vorticityCross_fderiv_crossVec_apply {u ω : R3 → R3} {x : R3} (i : Fin 3)
    (hu : HasFDerivAt u (fderiv ℝ u x) x) (hω : HasFDerivAt ω (fderiv ℝ ω x) x) :
    fderiv ℝ (fun y => crossVec (u y) (ω y)) x (e i)
      = crossVec (fderiv ℝ u x (e i)) (ω x) + crossVec (u x) (fderiv ℝ ω x (e i)) := by
  have hB := vorticityCross_isBoundedBilinearMap
  have hpair : HasFDerivAt (fun y => (u y, ω y))
      ((fderiv ℝ u x).prod (fderiv ℝ ω x)) x := hu.prodMk hω
  have hcomp := (hB.hasFDerivAt (u x, ω x)).comp x hpair
  have hf : fderiv ℝ (fun y => crossVec (u y) (ω y)) x
      = (hB.deriv (u x, ω x)).comp ((fderiv ℝ u x).prod (fderiv ℝ ω x)) := by
    show fderiv ℝ ((fun p : R3 × R3 => crossVec p.1 p.2) ∘ fun y => (u y, ω y)) x = _
    rw [hcomp.fderiv]
  rw [hf, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    IsBoundedBilinearMap.deriv_apply]
  rw [add_comm]

/-! ## The standard basis `e` of `ℝ³` -/

/-- The vector `e i` is the `i`-th basis vector: dotting with it is taking the `i`-th coordinate. -/
private lemma dot_e_left (i : Fin 3) (w : Fin 3 → ℝ) : WithLp.ofLp (e i) ⬝ᵥ w = w i := by
  rw [FiniteTimeSingularity.e, WithLp.ofLp_toLp, dotProduct]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- The right version of `dot_e_left`. -/
private lemma dot_e_right (i : Fin 3) (v : Fin 3 → ℝ) : v ⬝ᵥ WithLp.ofLp (e i) = v i := by
  rw [dotProduct_comm, dot_e_left]

/-- The basis expansion `v = ∑ i, (v i) • e i` in `ℝ³`. -/
lemma vorticityCross_sum_smul_e (v : R3) : ∑ i : Fin 3, (v i) • e i = v := by
  rw [WithLp.ext_iff]
  have h := Module.Basis.sum_repr (Pi.basisFun ℝ (Fin 3)) (WithLp.ofLp v)
  simp only [Pi.basisFun_apply, Pi.basisFun_repr] at h
  simpa only [WithLp.ofLp_sum, WithLp.ofLp_smul, FiniteTimeSingularity.e,
    WithLp.ofLp_toLp] using h

/-- A linear map is the sum of its diagonal matrix entries in the basis `e`. -/
lemma vorticityCross_fderiv_apply_sum_smul (L : R3 →L[ℝ] R3) (v : R3) :
    L v = ∑ i : Fin 3, (v i) • L (e i) := by
  conv_lhs => rw [← vorticityCross_sum_smul_e v]
  rw [map_sum]
  exact Finset.sum_congr rfl (fun i _ => by rw [map_smul])

/-! ## Divergence as the sum of the diagonal entries -/

/-- The basis `e 0, e 1, e 2` of `ℝ³` (whose coordinates are the coordinate functions). -/
noncomputable def vorticityCross_eBasis : Module.Basis (Fin 3) ℝ R3 :=
  Module.Basis.ofEquivFun (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ))

/-- `vorticityCross_eBasis` is the standard basis `e`. -/
lemma vorticityCross_eBasis_apply (i : Fin 3) : vorticityCross_eBasis i = e i := by
  simp only [vorticityCross_eBasis, Module.Basis.coe_ofEquivFun, FiniteTimeSingularity.e]
  rfl

/-- The coordinates of a vector in `vorticityCross_eBasis` are its coordinates. -/
lemma vorticityCross_eBasis_repr (v : R3) (i : Fin 3) : vorticityCross_eBasis.repr v i = v i := by
  rw [vorticityCross_eBasis, Module.Basis.ofEquivFun_repr_apply]
  rfl

/-- **The divergence is the sum of the diagonal entries of the derivative**: for the standard basis
`e` of `ℝ³`, `div g x = ∑ i, (fderiv ℝ g x (e i)) i`. -/
lemma vorticityCross_div_eq_sum_diag (g : R3 → R3) (x : R3) :
    div g x = ∑ i : Fin 3, (fderiv ℝ g x (e i)) i := by
  rw [div, LinearMap.trace_eq_matrix_trace ℝ vorticityCross_eBasis, Matrix.trace]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply, vorticityCross_eBasis_apply,
    vorticityCross_eBasis_repr]
  rfl

/-! ## The identity `curl (u ⨯ ω) = (div ω) u - (div u) ω + (ω · ∇)u - (u · ∇)ω` -/

theorem vorticity_cross_eq {u ω : R3 → R3} {x : R3}
    (hu : HasFDerivAt u (fderiv ℝ u x) x) (hω : HasFDerivAt ω (fderiv ℝ ω x) x) :
    FiniteTimeSingularity.vorticity (fun y => crossVec (u y) (ω y)) x
      = FiniteTimeSingularity.div ω x • u x - FiniteTimeSingularity.div u x • ω x
        + fderiv ℝ u x (ω x) - fderiv ℝ ω x (u x) := by
  have hd : ∀ i : Fin 3, fderiv ℝ (fun y => crossVec (u y) (ω y)) x (e i)
      = crossVec (fderiv ℝ u x (e i)) (ω x) + crossVec (u x) (fderiv ℝ ω x (e i)) :=
    fun i => vorticityCross_fderiv_crossVec_apply i hu hω
  have hL : WithLp.ofLp (vorticity (fun y => crossVec (u y) (ω y)) x)
      = ∑ i : Fin 3, WithLp.ofLp (e i) ⨯₃
          WithLp.ofLp (fderiv ℝ (fun y => crossVec (u y) (ω y)) x (e i)) := by
    rw [FiniteTimeSingularity.vorticity]
  have hstep : (∑ i : Fin 3, WithLp.ofLp (e i) ⨯₃
          WithLp.ofLp (fderiv ℝ (fun y => crossVec (u y) (ω y)) x (e i)))
      = ∑ i : Fin 3, ( (WithLp.ofLp (ω x) i) • WithLp.ofLp (fderiv ℝ u x (e i))
        - (WithLp.ofLp (fderiv ℝ u x (e i)) i) • WithLp.ofLp (ω x)
        + (WithLp.ofLp (fderiv ℝ ω x (e i)) i) • WithLp.ofLp (u x)
        - (WithLp.ofLp (u x) i) • WithLp.ofLp (fderiv ℝ ω x (e i)) ) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [hd i]
    change WithLp.ofLp (e i) ⨯₃
        (WithLp.ofLp (fderiv ℝ u x (e i)) ⨯₃ WithLp.ofLp (ω x)
          + WithLp.ofLp (u x) ⨯₃ WithLp.ofLp (fderiv ℝ ω x (e i)))
      = _
    rw [map_add, cross_cross_eq_smul_sub_smul', cross_cross_eq_smul_sub_smul',
      dot_e_left, dot_e_right, dot_e_right, dot_e_left]
    abel
  have hs1 : (∑ i : Fin 3, (WithLp.ofLp (ω x) i) • WithLp.ofLp (fderiv ℝ u x (e i)))
      = WithLp.ofLp (fderiv ℝ u x (ω x)) := by
    rw [show (∑ i : Fin 3, (WithLp.ofLp (ω x) i) • WithLp.ofLp (fderiv ℝ u x (e i)))
          = WithLp.ofLp (∑ i : Fin 3, (WithLp.ofLp (ω x) i) • fderiv ℝ u x (e i)) from by
        rw [WithLp.ofLp_sum]
        exact Finset.sum_congr rfl (fun i _ => by rw [WithLp.ofLp_smul])]
    rw [vorticityCross_fderiv_apply_sum_smul (fderiv ℝ u x) (ω x)]
  have hs2 : (∑ i : Fin 3, (WithLp.ofLp (fderiv ℝ u x (e i)) i) • WithLp.ofLp (ω x))
      = WithLp.ofLp (div u x • ω x) := by
    rw [← Finset.sum_smul, ← vorticityCross_div_eq_sum_diag u x, ← WithLp.ofLp_smul]
  have hs3 : (∑ i : Fin 3, (WithLp.ofLp (fderiv ℝ ω x (e i)) i) • WithLp.ofLp (u x))
      = WithLp.ofLp (div ω x • u x) := by
    rw [← Finset.sum_smul, ← vorticityCross_div_eq_sum_diag ω x, ← WithLp.ofLp_smul]
  have hs4 : (∑ i : Fin 3, (WithLp.ofLp (u x) i) • WithLp.ofLp (fderiv ℝ ω x (e i)))
      = WithLp.ofLp (fderiv ℝ ω x (u x)) := by
    rw [show (∑ i : Fin 3, (WithLp.ofLp (u x) i) • WithLp.ofLp (fderiv ℝ ω x (e i)))
          = WithLp.ofLp (∑ i : Fin 3, (WithLp.ofLp (u x) i) • fderiv ℝ ω x (e i)) from by
        rw [WithLp.ofLp_sum]
        exact Finset.sum_congr rfl (fun i _ => by rw [WithLp.ofLp_smul])]
    rw [vorticityCross_fderiv_apply_sum_smul (fderiv ℝ ω x) (u x)]
  have key : WithLp.ofLp (vorticity (fun y => crossVec (u y) (ω y)) x)
      = WithLp.ofLp ((fderiv ℝ u x (ω x) - div u x • ω x) + div ω x • u x
          - fderiv ℝ ω x (u x)) := by
    rw [hL, hstep, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      hs1, hs2, hs3, hs4]
    rw [WithLp.ofLp_sub, WithLp.ofLp_add, WithLp.ofLp_sub]
  have hkey := congrArg (WithLp.toLp 2) key
  simp only [WithLp.toLp_ofLp] at hkey
  rw [hkey]
  abel

end Work.FTS.PressureOn
