import Mathlib
import Submission.Work.MotR.Defs
import Submission.Work.MotR.Transcendental.Defs
import Submission.Work.MotR.Transcendental.isScalarTower_overSectionAlgebra_overFunctionFieldAlgebra

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Node R5: a positive-dimensional `𝔽`-variety has a transcendental function

For `X` a positive-dimensional variety over a field `𝔽` (an irreducible reduced separated scheme
of finite type over `Spec 𝔽`, of positive topological Krull dimension), the function field
`X.functionField = 𝒪_{X, η}` has positive transcendence degree over `𝔽`: there is a *transcendental*
element.

This is the arithmetic input shared by the function-field classes (b), (c), (d) of Lin–Shinder,
*Motivic invariants of birational maps*, Annals of Math. **199** (1), 2024, Theorem 1.2 (1): the
field `X.functionField` is a function field in the sense of the paper, i.e. it is not algebraic over
its field of constants.

## Route

Suppose that every element of the function field were algebraic over `𝔽`.  Let `x ∈ X` be a point
and `U ∋ x` an affine open neighbourhood; write `A = Γ(X, U)`.  Because `X` is integral, `A` is a
domain and `X.functionField = Frac A`.  The constants act on `A` and on the function field
compatibly (`Work.MotR.Transcendental.overSectionAlgebra` and
`Work.MotR.Transcendental.isScalarTower_overSectionAlgebra_overFunctionFieldAlgebra`), so
every element of `A` is algebraic over `𝔽`, i.e. `A` is integral over `𝔽`.  A domain which is
integral over a field is a field (`isField_of_isDomain_of_isIntegral`, via the Artinian-algebra
fact that an integral non-zero-divisor over an Artinian ring is a unit).  Hence `A` is a field, and
`U ≅ Spec A` is a single point.

So *every* point of `X` has a singleton open neighbourhood: `X` is discrete.  A discrete space has
topological Krull dimension `≤ 0` (`topologicalKrullDim_zero_of_discreteTopology`), contradicting
`0 < topologicalKrullDim X`.  -/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory

namespace Work.MotR.Transcendental

noncomputable section

/-- **A domain which is integral over a field is a field.**

For `A` a domain with an `𝔽`-algebra structure and integral over the field `𝔽`, every nonzero
element of `A` is a unit: a nonzero element is integral, hence not a zero divisor, and an integral
non-zero-divisor over the Artinian ring `𝔽` is a unit
(`IsArtinianRing.isUnit_of_nonZeroDivisor_of_isIntegral'`). -/
theorem isField_of_isDomain_of_isIntegral {𝔽 A : Type*} [Field 𝔽] [CommRing A] [IsDomain A]
    [Algebra 𝔽 A] (h : Algebra.IsIntegral 𝔽 A) : IsField A := by
  haveI := h
  exact ⟨⟨0, 1, zero_ne_one⟩, fun x y => mul_comm x y, fun {a} ha =>
    (IsArtinianRing.isUnit_of_nonZeroDivisor_of_isIntegral' (R := 𝔽)
      (mem_nonZeroDivisors_iff_ne_zero.mpr ha)).exists_right_inv⟩

theorem exists_transcendental_of_pos_topologicalKrullDim (𝔽 : Type) [Field 𝔽] (X : AlgebraicGeometry.Scheme) [MotivicInvariants.Variety 𝔽 X] (hX : 0 < topologicalKrullDim X) :
    letI := Work.FFResidual.overFunctionFieldAlgebra 𝔽 X
    ∃ t : X.functionField, Transcendental 𝔽 t := by
  letI := Work.FFResidual.overFunctionFieldAlgebra 𝔽 X
  by_contra h
  -- the function field is algebraic over `𝔽`
  have halg : Algebra.IsAlgebraic 𝔽 X.functionField := ⟨fun t => by
    by_contra ht
    exact h ⟨t, ht⟩⟩
  haveI : Algebra.IsAlgebraic 𝔽 X.functionField := halg
  -- every point has an affine open neighbourhood on which the section ring is a field,
  -- hence a singleton open neighbourhood
  have hpoint : ∀ x : X, ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧ ∀ y ∈ U, y = x := by
    intro x
    let U : X.Opens := (X.affineCover.f (X.affineCover.idx x)).opensRange
    have hUaff : IsAffineOpen U := isAffineOpen_opensRange _
    have hxU : x ∈ U := X.affineCover.covers x
    haveI : Nonempty U := ⟨⟨x, hxU⟩⟩
    haveI hdom : IsDomain ↑Γ(X, U) := IsIntegral.component_integral U
    haveI hfr : IsFractionRing ↑Γ(X, U) ↑X.functionField :=
      functionField_isFractionRing_of_isAffineOpen X U hUaff
    letI : Algebra 𝔽 ↑Γ(X, U) := overSectionAlgebra 𝔽 X U
    haveI htow : IsScalarTower 𝔽 ↑Γ(X, U) ↑X.functionField :=
      isScalarTower_overSectionAlgebra_overFunctionFieldAlgebra 𝔽 X U
    -- the section ring is integral over `𝔽`, since the function field is algebraic over `𝔽`
    have hInt : Algebra.IsIntegral 𝔽 ↑Γ(X, U) := by
      refine ⟨fun a => ?_⟩
      have h2 : _root_.IsIntegral 𝔽 (algebraMap ↑Γ(X, U) ↑X.functionField a) :=
        isAlgebraic_iff_isIntegral.mp
          (Algebra.IsAlgebraic.isAlgebraic (algebraMap ↑Γ(X, U) ↑X.functionField a))
      have hinj : Function.Injective
          (IsScalarTower.toAlgHom 𝔽 ↑Γ(X, U) ↑X.functionField) := by
        intro p q hpq
        apply IsFractionRing.injective ↑Γ(X, U) ↑X.functionField
        simpa [IsScalarTower.toAlgHom_apply] using hpq
      refine (isIntegral_algHom_iff _ hinj).mp ?_
      simpa [IsScalarTower.toAlgHom_apply] using h2
    have hfield : IsField ↑Γ(X, U) := isField_of_isDomain_of_isIntegral hInt
    -- the section ring `Γ(X, U)` is a field, so the affine open `U ≅ Spec Γ(X, U)` is a single
    -- point: `Spec` of a field has a unique prime ideal, and `fromSpec` recovers the point
    refine ⟨U, hUaff, hxU, fun y hy => ?_⟩
    haveI hsub : Subsingleton (PrimeSpectrum ↑Γ(X, U)) :=
      PrimeSpectrum.subsingleton_iff_isField_of_isReduced.mpr hfield
    have hpy : hUaff.primeIdealOf ⟨y, hy⟩ = hUaff.primeIdealOf ⟨x, hxU⟩ := Subsingleton.elim _ _
    calc y = hUaff.fromSpec (hUaff.primeIdealOf ⟨y, hy⟩) :=
          (hUaff.fromSpec_primeIdealOf ⟨y, hy⟩).symm
      _ = hUaff.fromSpec (hUaff.primeIdealOf ⟨x, hxU⟩) := by rw [hpy]
      _ = x := hUaff.fromSpec_primeIdealOf ⟨x, hxU⟩
  -- hence `X` is discrete
  haveI hdisc : DiscreteTopology X := discreteTopology_iff_isOpen_singleton.mpr fun x => by
    obtain ⟨U, hUaff, hxU, hsingle⟩ := hpoint x
    have hEq : (U : Set X) = {x} := by
      ext y
      exact ⟨fun hy => hsingle y hy,
        fun hy => by rw [Set.mem_singleton_iff] at hy; rw [hy]; exact hxU⟩
    rw [← hEq]
    exact U.isOpen
  exact not_lt_of_ge (topologicalKrullDim_zero_of_discreteTopology X) hX

end

end Work.MotR.Transcendental
