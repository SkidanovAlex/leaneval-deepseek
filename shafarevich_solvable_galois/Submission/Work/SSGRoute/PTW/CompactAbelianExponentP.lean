import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Submission.Work.SSGRoute.PTW.avgOp_isCompact
import Submission.Work.SSGRoute.PTW.avgOp_isSymmetric
import Submission.Work.SSGRoute.PTW.avgOp_ker_le_orthogonal_orbit
import Submission.Work.SSGRoute.PTW.avgOp_range_le_closure_nonzero_eigenspaces
import Submission.Work.SSGRoute.PTW.exists_character_of_finiteDim_regRep_submodule
import Submission.Work.SSGRoute.PTW.exists_open_index_p_notMem_ker_of_character
import Submission.Work.SSGRoute.PTW.exists_regRep_ne_self
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Separation of points of a compact abelian group of exponent `p` by open index-`p` subgroups

Main theorem of this file,
`Work.SSGRoute.PTW.exists_open_index_p_notMem_of_compact_abelian_exponent_p`: for a compact
Hausdorff abelian group `Q` of exponent `p` (`q ^ p = 1` for all `q`) and `y ≠ 1` there is an open
subgroup `U ≤ Q` of index `p` with `y ∉ U`.

This is the cone of the L² / regular representation argument (Gelfand–Raikov for compact abelian
groups, in the form needed for the Frattini/`p`-power criterion
`Work.SSGRoute.PTW.mem_all_open_index_p_iff_mem_closure_pthPowers`):

1. `μ` = Haar probability measure on `Q` (`haarMeasure` of the positive compact `Q` itself, which
   is automatically normalized to `μ Q = 1`), `H := Lp ℂ 2 μ`;
2. `regRep y ≠ 1` for `y ≠ 1` (`Work.SSGRoute.PTW.exists_regRep_ne_self`), so there is `ξ` with
   `regRep y ξ ≠ ξ`;
3. the averaging operator `A := avgOp ξ = ∫ g, |regRep g ξ⟩⟨regRep g ξ| dμ(g)` is a nonzero
   compact self-adjoint operator on `H` commuting with the regular representation
   (`avgOp_ne_zero`, `avgOp_isCompact`, `avgOp_isSymmetric`, `avgOp_regRep`);
4. `Work.SSGRoute.PTW.exists_eigenspace_regRep_ne_one` (from the kernel and range descriptions
   `avgOp_ker_le_orthogonal_orbit`, `avgOp_range_le_closure_nonzero_eigenspaces`) provides a
   nonzero eigenvalue `lam` whose (finite dimensional, `regRep`-invariant) eigenspace `E` carries a
   vector `v` with `regRep y v ≠ v`;
5. `Work.SSGRoute.PTW.exists_character_of_finiteDim_regRep_submodule` turns the finite dimensional
   subrepresentation `E` into a continuous character `χ : Q →* ℂˣ` with `χ y ≠ 1`;
6. since `Q` has exponent `p`, `χ (Q) ⊆ μ_p`, so `ker χ` is an open index-`p` subgroup avoiding
   `y` (`Work.SSGRoute.PTW.exists_open_index_p_notMem_ker_of_character`).
-/

namespace Work.SSGRoute.PTW

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open MeasureTheory Filter Metric
open scoped Topology InnerProductSpace ENNReal

/-- **Separation of points of a compact abelian group of exponent `p`.** -/
theorem exists_open_index_p_notMem_of_compact_abelian_exponent_p (Q : Type*) [CommGroup Q]
    [TopologicalSpace Q] [IsTopologicalGroup Q] [CompactSpace Q] [T2Space Q]
    (p : ℕ) [Fact p.Prime] (hexp : ∀ q : Q, q ^ p = 1) (y : Q) (hy : y ≠ 1) :
    ∃ U : Subgroup Q, IsOpen (U : Set Q) ∧ U.index = p ∧ y ∉ U := by
  classical
  -- `Q` is given its Borel `σ`-algebra
  letI : MeasurableSpace Q := borel Q
  haveI : BorelSpace Q := ⟨rfl⟩
  -- the Haar probability measure on `Q`
  let K₀ : TopologicalSpace.PositiveCompacts Q :=
    { carrier := Set.univ
      isCompact' := isCompact_univ
      interior_nonempty' := ⟨1, by simp⟩ }
  let ν : Measure Q := MeasureTheory.Measure.haarMeasure K₀
  have hν : ν Set.univ = 1 := by
    have h : ν (K₀ : Set Q) = 1 := MeasureTheory.Measure.haarMeasure_self (K₀ := K₀)
    rwa [show (K₀ : Set Q) = Set.univ from rfl] at h
  haveI : IsProbabilityMeasure ν := ⟨hν⟩
  haveI : Measure.IsMulLeftInvariant ν :=
    MeasureTheory.Measure.isMulLeftInvariant_haarMeasure K₀
  haveI : IsLocallyFiniteMeasure ν := inferInstance
  haveI : Measure.InnerRegularCompactLTTop ν := inferInstance
  -- 1. a vector moved by `y`
  obtain ⟨ξ, hξ⟩ := exists_regRep_ne_self (μ := ν) y hy
  -- 2. a nonzero eigenspace of `avgOp ξ` on which `y` acts nontrivially
  obtain ⟨lam, hlam, v, hvmem, hv0, hvy⟩ :=
    exists_eigenspace_regRep_ne_one (μ := ν) ξ y hξ
      (avgOp_ker_le_orthogonal_orbit (μ := ν) ξ)
      (avgOp_range_le_closure_nonzero_eigenspaces (μ := ν) ξ
        (avgOp_isCompact (μ := ν) ξ) (avgOp_isSymmetric (μ := ν) ξ))
  -- 3. the finite dimensional invariant subspace, and its character
  let E : Submodule ℂ (Lp ℂ 2 ν) := Module.End.eigenspace
    ((avgOp (μ := ν) ξ : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν) : Lp ℂ 2 ν →ₗ[ℂ] Lp ℂ 2 ν) lam
  have hE : ∀ (h : Q), ∀ v ∈ E, regRep (μ := ν) h v ∈ E :=
    fun h w hw => avgOp_regRep_mem_eigenspace (μ := ν) ξ h lam hw
  haveI : FiniteDimensional ℂ E :=
    ContinuousLinearMap.finite_dimensional_eigenspace (avgOp_isCompact (μ := ν) ξ) lam hlam
  have hyρ : restrictRepHom (μ := ν) E hE y ≠ 1 := by
    intro h1
    refine hvy ?_
    exact congrArg (fun T : E ≃ₗᵢ[ℂ] E => ((T ⟨v, hvmem⟩ : E) : Lp ℂ 2 ν)) h1
  obtain ⟨χ, hχcont, hχy⟩ :=
    exists_character_of_finiteDim_regRep_submodule (μ := ν) E hE y hyρ
  -- 4. the open index-`p` subgroup
  have hexpχ : ∀ g : Q, χ g ^ p = 1 := by
    intro g
    rw [← map_pow, hexp g, map_one]
  exact exists_open_index_p_notMem_ker_of_character p χ hχcont hexpχ y hχy

end Work.SSGRoute.PTW
