import Mathlib
import Submission.Work.Compact.Noncompact.Good

/-!
# The class of a relative cycle whose boundary vanishes

For a space `X`, a subset `S ⊆ X` and a chain `z ∈ C_{k+1}(X)` whose boundary is supported in `S`,
`Work.Compact.Noncompact.hatClass S k z` is the class of `z` in `H_{k+1}(X, X∖S)`.

When the boundary of `z` actually *vanishes* (`bdry X k z = 0`), the chain `z` is an absolute
cycle, say `z = (iCycles (k+1)) zeta` for a cycle `zeta` of the singular chains of `X`.  The class of
`z` in the relative homology is then the image of the absolute class of `zeta` under the map induced
by the cokernel projection `C_*(X) ⟶ C_*(X)/C_*(X∖S)`.  That is the content of
`hatClass_of_d_eq_zero` below.

The proof is formal: `hatClass` is by definition `homologyπ` applied to the cycle `hatCycHom` built
from `z`, and `hatCycHom` is the image under `cyclesMap` of `cokernel.π` of the cycle `zeta`; the
conclusion follows from naturality of `homologyπ` (`HomologicalComplex.homologyπ_naturality`).
-/

namespace Work.Compact.Noncompact

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

set_option maxHeartbeats 800000

noncomputable section

/-- The span of a single element, evaluated at `1`. -/
lemma toSpanSingleton_one {R : Type*} [Ring R] {M : Type*} [AddCommGroup M] [Module R M] (x : M) :
    (LinearMap.toSpanSingleton R M x) (1 : R) = x := by
  rw [LinearMap.toSpanSingleton_apply, one_smul]

/-- The `ℤ`-linear map `1 ↦ x` as a morphism of `ModuleCat`, evaluated at `1`. -/
lemma ofHom_toSpanSingleton_one {R : Type*} [Ring R] {M : ModuleCat R} (x : M) :
    (ModuleCat.ofHom (LinearMap.toSpanSingleton R M x)).hom (1 : R) = x := by
  rw [ModuleCat.hom_ofHom, toSpanSingleton_one]

theorem hatClass_of_d_eq_zero {X : TopCat} (S : Set X) (k : ℕ)
    (z : Work.Compact.Noncompact.Ch X (k + 1))
    (hz : Work.Compact.Noncompact.bdry X k z = 0)
    (hzS : Work.Compact.Noncompact.bdry X k z ∈ Work.Compact.Noncompact.suppS X S k)
    (zeta : (Work.Cohomology.singularChains ℤ X).cycles (k + 1))
    (hzeta : ((Work.Cohomology.singularChains ℤ X).iCycles (k + 1)).hom zeta = z) :
    Work.Compact.Noncompact.hatClass S k z hzS
      = HomologicalComplex.homologyMap (CategoryTheory.Limits.cokernel.π
          (Work.Cohomology.inclChains X S)) (k + 1)
        ((HomologicalComplex.homologyπ (Work.Cohomology.singularChains ℤ X) (k + 1)).hom zeta) := by
  -- The cycle of `z` in the relative complex is the image of `zeta` under `cyclesMap`.
  have hcyc : (hatCycHom S k z hzS).hom 1
      = (HomologicalComplex.cyclesMap (cokernel.π (Work.Cohomology.inclChains X S)) (k + 1)).hom zeta := by
    have hA : ((RC X S).iCycles (k + 1)).hom ((hatCycHom S k z hzS).hom 1) = hatQ S k z := by
      have h := iCycles_hatCycHom S k z hzS
      have h2 := congrArg (fun (f : ModuleCat.of ℤ ℤ ⟶ (RC X S).X (k + 1)) => f.hom 1) h
      rw [ModuleCat.comp_apply] at h2
      rw [h2]
      exact ofHom_toSpanSingleton_one (hatQ S k z)
    have hB : ((RC X S).iCycles (k + 1)).hom
        ((HomologicalComplex.cyclesMap (cokernel.π (Work.Cohomology.inclChains X S))
          (k + 1)).hom zeta) = hatQ S k z := by
      have h := HomologicalComplex.cyclesMap_i
        (cokernel.π (Work.Cohomology.inclChains X S)) (k + 1)
      have h2 := congrArg (fun (f : (Work.Cohomology.singularChains ℤ X).cycles (k + 1) ⟶
        (RC X S).X (k + 1)) => f.hom zeta) h
      rw [ModuleCat.comp_apply, ModuleCat.comp_apply] at h2
      rw [h2, hzeta]
    have hinj : Function.Injective ((RC X S).iCycles (k + 1)).hom :=
      (ModuleCat.mono_iff_injective _).mp inferInstance
    exact hinj (hA.trans hB.symm)
  -- `hatClass` is `homologyπ` applied to that cycle; conclude by naturality.
  show (hatClassHom S k z hzS).hom 1 = _
  rw [hatClassHom, ModuleCat.comp_apply, hcyc]
  have hnat := HomologicalComplex.homologyπ_naturality
    (cokernel.π (Work.Cohomology.inclChains X S)) (k + 1)
  have h2 := congrArg (fun (m : (Work.Cohomology.singularChains ℤ X).cycles (k + 1) ⟶
    (RC X S).homology (k + 1)) => m.hom zeta) hnat
  rw [ModuleCat.comp_apply, ModuleCat.comp_apply] at h2
  exact h2.symm

end

end Work.Compact.Noncompact
