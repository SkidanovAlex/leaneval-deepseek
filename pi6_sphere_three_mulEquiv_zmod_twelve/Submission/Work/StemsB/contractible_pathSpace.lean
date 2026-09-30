import Mathlib
import Submission.Work.StemsB.Fibrations

/-!
# The based path space is contractible

For a based topological space `(X, x₀)` the **path space** `PathSpace X x₀`
(`Submission/Work/StemsB/Fibrations.lean`) is the subspace of the compact-open function space
`C(I, X)` consisting of the paths that start at `x₀`.

This space is contractible: the constant path at `x₀` is a deformation retract, the homotopy
being the path reparametrisation

  `H(t, γ)(s) = γ (t * s)`,

so that `H(0, γ)` is the constant path at `x₀ = γ 0` and `H(1, γ) = γ`.  Continuity of `H` is the
statement that evaluation of continuous maps is continuous (the defining property of the
compact-open topology), applied to the continuous map
`((PathSpace X x₀ × I) × I → X), (γ, t, s) ↦ γ (t * s)`; we curry it twice, the inner currying
producing the path `s ↦ γ (t * s)`.

The contractibility of the path space is what turns the path–loop fibration
`evalOne : PathSpace X x₀ → X` (proved to be a Serre fibration in
`Submission/Work/StemsB/isSerreFibration_evalOne.lean`) into a fibration with contractible total
space, the input of the Serre spectral sequence argument for the rational Hurewicz theorem
(`Submission/Work/StemsB/CONTRACTS.md` §A).
-/

open scoped unitInterval
open ContinuousMap

namespace Work.StemsB

noncomputable section

variable (X : Type*) [TopologicalSpace X] (x₀ : X)

/-- The constant path at `x₀`, viewed as a point of the based path space. -/
def constPath : PathSpace X x₀ := ⟨ContinuousMap.const I x₀, rfl⟩

@[simp]
theorem constPath_apply (s : I) : (constPath X x₀).1 s = x₀ := rfl

/-- The uncurried reparametrisation map `(γ, t, s) ↦ γ (t * s)`, as a continuous map
`(PathSpace X x₀ × I) × I → X`.  Continuity is `ContinuousMap` evaluation at `t * s`. -/
def evalReparam : C((PathSpace X x₀ × I) × I, X) where
  toFun q := q.1.1.1 (q.1.2 * q.2)
  continuous_toFun := by fun_prop

/-- The reparametrisation map `(γ, t) ↦ (s ↦ γ (t * s))` as a continuous map into the path space.
It is the currying of `evalReparam`, restricted to the subtype of based paths: the curried path
sends `0` to `γ (t * 0) = γ 0 = x₀`. -/
def pathReparam : C(PathSpace X x₀ × I, PathSpace X x₀) where
  toFun q := ⟨(evalReparam X x₀).curry q, by
    change q.1.1 (q.2 * 0) = x₀
    rw [mul_zero]
    exact q.1.2⟩
  continuous_toFun := Continuous.subtype_mk (evalReparam X x₀).curry.continuous (by
    intro q
    change q.1.1 (q.2 * 0) = x₀
    rw [mul_zero]
    exact q.1.2)

@[simp]
theorem pathReparam_apply (γ : PathSpace X x₀) (t s : I) :
    (pathReparam X x₀ (γ, t)).1 s = γ.1 (t * s) := rfl

/-- The based path space is contracted onto the constant path at `x₀` by path reparametrisation:
this is the homotopy `H(t, γ)(s) = γ (t * s)`, from the constant map at `constPath X x₀`
(at `t = 0`) to the identity (at `t = 1`). -/
def pathReparamHom : ContinuousMap.Homotopy
    (ContinuousMap.const (PathSpace X x₀) (constPath X x₀))
    (ContinuousMap.id (PathSpace X x₀)) where
  toFun p := pathReparam X x₀ (p.2, p.1)
  continuous_toFun := (pathReparam X x₀).continuous.comp (by fun_prop)
  map_zero_left γ := by
    apply Subtype.ext
    apply ContinuousMap.ext
    intro s
    change γ.1 (0 * s) = x₀
    rw [zero_mul]
    exact γ.2
  map_one_left γ := by
    apply Subtype.ext
    apply ContinuousMap.ext
    intro s
    change γ.1 (1 * s) = γ.1 s
    rw [one_mul]

/-- **The based path space of a based space is contractible.**  The identity is homotopic to the
constant map at the constant path `constPath X x₀`, by the reparametrisation homotopy
`pathReparamHom`, read in the reverse direction. -/
theorem contractible_pathSpace (X : Type*) [TopologicalSpace X] (x₀ : X) :
    ContractibleSpace (PathSpace X x₀) := by
  rw [contractible_iff_id_nullhomotopic]
  exact ⟨constPath X x₀, ⟨(pathReparamHom X x₀).symm⟩⟩

end

end Work.StemsB
