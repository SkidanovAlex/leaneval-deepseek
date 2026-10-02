import Mathlib
import Submission.Work.Cohomology.sdChainMap
import Submission.Work.Cohomology.sdLC_boundary
import Submission.Work.Cohomology.toChain_boundaryLC
import Submission.Work.Cohomology.SubdivisionHomotopyData
import Submission.Work.Cohomology.tElem_boundary
import Submission.Work.Cohomology.tRel_eval

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The barycentric subdivision is chain homotopic to the identity

The subdivision operator `sdChainMap X : C_*(X) ⟶ C_*(X)` (`Submission/Work/Cohomology/sdChainMap.lean`)
is chain homotopic to the identity of the singular chain complex of `X` with `ℤ` coefficients.

The homotopy is the classical one: on a singular simplex `σ : Δⁿ ⟶ X` it is the push-forward
`σ_*(cLC n)` of the `(n+1)`-chain `cLC n ∈ C_{n+1}(Δⁿ)` constructed in
`Submission/Work/Cohomology/SubdivisionHomotopyData.lean` by the cone recursion
`cLC (n+1) = cone_{bary} (sdLC (n+1) - iotaLC (n+1) - ∑ᵢ (-1)ⁱ δᵢ (cLC n))`, whose boundary is
computed in `cLC_boundary`.  Concretely the homotopy component is `tHom X n : C_n(X) ⟶ C_{n+1}(X)`
(`tHom_gen`); the per-simplex identity `∂(Tσ) = Sd σ - σ - T(∂σ)` is `tElem_boundary` and the
evaluation of the induced chain map `sdChainMap - id` on generators is `tRel_eval`.

The last steps assemble these into Mathlib's `Homotopy` structure: `Homotopy.nullHomotopicMap'`
turns the family `tRel X` (the components `tHom X n` transported along the relation `n + 1 = m`)
into the chain map `∑ (∂T + T∂)`, which is identified with `sdChainMap X - id`, and
`Homotopy.equivSubZero` converts `Homotopy (sdChainMap X - id) 0` into the desired statement.
-/

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-- Evaluation of `nullHomotopicMap' (tRel X)` in degree zero, where the homotopy condition "falls
off the end": only the `T∂` term survives, and `tHom X 0 = 0`. -/
lemma tRel_eval_zero (X : TopCat) (σ : (TopCat.toSSet.obj X) _⦋0⦌) :
    (Homotopy.nullHomotopicMap' (tRel X)).f 0 (gen X 0 σ) = 0 := by
  rw [Homotopy.nullHomotopicMap'_f_of_not_rel_left (c := ComplexShape.down ℕ)
    (k₁ := 1) (k₀ := 0) (r₁₀ := (show (ComplexShape.down ℕ).Rel 1 0 from rfl))
    (hk₀ := fun l => by rw [ComplexShape.down_Rel]; omega) (h := tRel X)]
  simp [tRel_self, tHom_zero]

theorem sdHomotopy (X : TopCat) :
    Nonempty (Homotopy (sdChainMap X)
      (CategoryTheory.CategoryStruct.id (singularChains ℤ X))) := by
  refine ⟨?_⟩
  have hnull : Homotopy (Homotopy.nullHomotopicMap' (tRel X)) 0 := Homotopy.nullHomotopy' (tRel X)
  have heq : sdChainMap X - 𝟙 (singularChains ℤ X) = Homotopy.nullHomotopicMap' (tRel X) := by
    apply HomologicalComplex.hom_ext
    intro i
    apply SSet.chainComplex_hom_ext (X := TopCat.toSSet.obj X)
    intro σ
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    rcases i with _ | m
    · show (sdChainMap X - 𝟙 (singularChains ℤ X)).f 0 (gen X 0 σ) =
        (Homotopy.nullHomotopicMap' (tRel X)).f 0 (gen X 0 σ)
      have hL : (sdChainMap X - 𝟙 (singularChains ℤ X)).f 0 (gen X 0 σ)
          = sdElem X 0 σ - gen X 0 σ := by
        simp only [HomologicalComplex.sub_f_apply, HomologicalComplex.id_f, ModuleCat.hom_sub,
          LinearMap.sub_apply, ModuleCat.hom_id, LinearMap.id_apply]
        rw [show (sdChainMap X).f 0 (gen X 0 σ) = sdElem X 0 σ from by
          show Sd X 0 (gen X 0 σ) = sdElem X 0 σ
          rw [Sd_gen]]
      rw [hL, tRel_eval_zero, sdElem_zero, sub_self]
    · show (sdChainMap X - 𝟙 (singularChains ℤ X)).f (m + 1) (gen X (m + 1) σ) =
        (Homotopy.nullHomotopicMap' (tRel X)).f (m + 1) (gen X (m + 1) σ)
      have hL : (sdChainMap X - 𝟙 (singularChains ℤ X)).f (m + 1) (gen X (m + 1) σ)
          = sdElem X (m + 1) σ - gen X (m + 1) σ := by
        simp only [HomologicalComplex.sub_f_apply, HomologicalComplex.id_f, ModuleCat.hom_sub,
          LinearMap.sub_apply, ModuleCat.hom_id, LinearMap.id_apply]
        rw [show (sdChainMap X).f (m + 1) (gen X (m + 1) σ) = sdElem X (m + 1) σ from by
          show Sd X (m + 1) (gen X (m + 1) σ) = sdElem X (m + 1) σ
          rw [Sd_gen]]
      rw [hL, tRel_eval X m σ, tElem_boundary X m σ]
      abel
  have h1 : Homotopy (sdChainMap X - 𝟙 (singularChains ℤ X)) 0 := (Homotopy.ofEq heq).trans hnull
  exact (Homotopy.equivSubZero (f := sdChainMap X)
    (g := 𝟙 (singularChains ℤ X))).symm h1

end

end Work.Cohomology
