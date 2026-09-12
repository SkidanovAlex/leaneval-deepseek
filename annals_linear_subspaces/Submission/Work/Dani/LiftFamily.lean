import Mathlib
import Submission.GeometryOfNumbers.ImageLatticeCovolume
import Submission.Work.Lattice.IsometryLatticeBounded

/-!
# Lifting a family from the flowed lattice `g(ℤᵈ)` to the integer lattice

The §3 flow lattice is `Λ_t = g(ℤᵈ)` with `g = a_t ∘ s_x` a linear automorphism
(`Submission.ImageLattice.imageSpan`), so the production step of `Submission.ApproxInterface`
delivers its `k` vectors `v i` *inside the lattice `Λ_t`*, while the interface
(`ApproxInterface.conjunct1_of_flow_production`) needs **integer** vectors `m i ∈ ℤᵈ` whose
flowed wedge is the wedge of the `v i`.

This module provides that conversion:

* `exists_int_lift` — for `g : ℝᵈ ≃ₗ[ℝ] ℝᵈ` and a family `v` with `v i ∈ imageSpan g` there are
  integer-lattice vectors `m i ∈ ℤᵈ` with `g (m i) = v i` (via the coefficient expansion in the
  image basis `imageBasis g = (B d).toBasis.map g`);
* `linearIndependent_of_lift` — the lifted family is `ℝ`-independent when `v` is (uses only the
  injectivity of `g`);
* `iMulti_lift` — the wedge identity `⋀^k (g ∘ m) = ⋀^k g (⋀^k m)`.

Module `Submission.Work.Dani.LiftFamily`, namespace `Submission.LiftFamily`.
-/

noncomputable section

open Module exteriorPower InnerProductGeometry Real
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

namespace Submission.LiftFamily

open Submission.ExteriorCoordinates
open Submission.ImageLattice
open Submission.GraysonLattice
open Submission.GraysonData

variable {d : ℕ}

/-- **The integer lift.**  Every family in the image lattice `g(ℤᵈ)` is the `g`-image of a family
of the standard integer lattice `ℤᵈ`. -/
theorem exists_int_lift (g : RD d ≃ₗ[ℝ] RD d) (k : ℕ) (v : Fin k → RD d)
    (hmem : ∀ i, v i ∈ imageSpan (d := d) g) :
    ∃ m : Fin k → RD d, (∀ i, m i ∈ stdIntLattice d) ∧ ∀ i, g (m i) = v i := by
  classical
  have hcoe : ∀ i, ∃ c : Fin d → ℤ,
      (∑ j : Fin d, c j • (imageBasis (d := d) g j)) = v i := by
    intro i
    have h1 : v i ∈ Submodule.span ℤ (Set.range ⇑(imageBasis (d := d) g)) := hmem i
    obtain ⟨c, hc⟩ :=
      (Submodule.mem_span_range_iff_exists_fun ℤ (v := ⇑(imageBasis (d := d) g))).mp h1
    exact ⟨c, hc⟩
  choose c hc using hcoe
  have hreal : ∀ i, (∑ j : Fin d, ((c i j : ℤ) : ℝ) • (imageBasis (d := d) g j)) = v i := by
    intro i
    have h2 : (∑ j : Fin d, ((c i j : ℤ) : ℝ) • (imageBasis (d := d) g j)) =
        ∑ j : Fin d, (c i j) • (imageBasis (d := d) g j) :=
      Finset.sum_congr rfl (fun j _ => Int.cast_smul_eq_zsmul ℝ (c i j) _)
    rw [h2]; exact hc i
  refine ⟨fun i => ∑ j : Fin d, ((c i j : ℤ) : ℝ) •
      (EuclideanSpace.basisFun (Fin d) ℝ j), ?_, ?_⟩
  · intro i
    refine Submodule.sum_mem _ (fun j _ => ?_)
    have : (EuclideanSpace.basisFun (Fin d) ℝ j) ∈ stdIntLattice d :=
      Submodule.subset_span ⟨j, rfl⟩
    rw [Int.cast_smul_eq_zsmul]
    exact Submodule.smul_mem (stdIntLattice d) (c i j) this
  · intro i
    have hmap : g (∑ j : Fin d, ((c i j : ℤ) : ℝ) • (EuclideanSpace.basisFun (Fin d) ℝ j)) =
        ∑ j : Fin d, ((c i j : ℤ) : ℝ) • g (EuclideanSpace.basisFun (Fin d) ℝ j) := by
      rw [map_sum]
      exact Finset.sum_congr rfl (fun j _ => (map_smul g _ _))
    rw [hmap]
    have hb : ∀ j : Fin d, g (EuclideanSpace.basisFun (Fin d) ℝ j) =
        imageBasis (d := d) g j := fun j => rfl
    rw [Finset.sum_congr rfl (fun j _ => by rw [hb j])]
    exact hreal i

/-- The lifted family is `ℝ`-independent when the original one is. -/
theorem linearIndependent_of_lift (g : RD d ≃ₗ[ℝ] RD d) {k : ℕ} {m v : Fin k → RD d}
    (hmv : ∀ i, g (m i) = v i) (hv : LinearIndependent ℝ v) :
    LinearIndependent ℝ m :=
  LinearIndependent.of_comp ((g : RD d →ₗ[ℝ] RD d))
    (by rw [show ((g : RD d →ₗ[ℝ] RD d) ∘ m) = v from funext hmv]; exact hv)

/-- The wedge identity: `⋀^k (g ∘ m) = ⋀^k g (⋀^k m)`. -/
theorem iMulti_lift (g : RD d ≃ₗ[ℝ] RD d) {k : ℕ} (m : Fin k → RD d) :
    exteriorPower.ιMulti ℝ k (fun i => g (m i)) =
      exteriorPower.map k (g : RD d →ₗ[ℝ] RD d) (exteriorPower.ιMulti ℝ k m) := by
  rw [exteriorPower.map_apply_ιMulti]
  rfl

end Submission.LiftFamily

end
