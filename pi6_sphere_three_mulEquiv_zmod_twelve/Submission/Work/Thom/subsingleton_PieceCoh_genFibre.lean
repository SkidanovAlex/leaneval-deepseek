import Mathlib
import Submission.Work.TangentClasses.Bundle
import Submission.Work.Thom.localThom_full
import Submission.Work.Thom.subsingleton_PieceCohA
import Submission.Work.Thom.localThom_genFibre

set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

/-!
# The vanishing of the relative cohomology of a bundle piece, for an arbitrary fibre

`Work.Thom.subsingleton_PieceCoh_of_lt_rankA` proves that the relative cohomology of the piece of
the Thom pair over a set `W` contained in a chart of a real bundle vanishes below the rank, *for
the standard fibre* `EuclideanSpace ℝ (Fin n)`.  Many bundles in this chapter (for instance the
realification of a complex bundle, or the tangent bundle of a smooth manifold) have a fibre which
is only a finite-dimensional real normed space, with no `EuclideanSpace` structure available.

This module removes that restriction.  The only content is that the model fibre of a bundle is
irrelevant: a continuous linear equivalence `F ≃L[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ F))`
(Mathiib's `ContinuousLinearEquiv.ofFinrankEq`, which needs merely a dimension equality — not an
isometry, which need not exist) induces a homeomorphism of the pieces

`(Z|_W, Z|_W ∖ 0) ≃ₜ (↥W × ℝ^{finrank F}, ↥W × (ℝ^{finrank F} ∖ 0))`

carrying the complement of the zero section to the punctured product, and relative cohomology is
invariant under a homeomorphism of pairs
(`Work.Cohomology.relCohomology_homeomorph_pairs`).

* `Work.Thom.subsingleton_PieceCoh_genFibre_of_euclidean` — the reduction, from the Euclidean
  model `H^m(W × ℝⁿ, W × (ℝⁿ∖0)) = 0` for `m < n`;
* `Work.Thom.subsingleton_PieceCoh_genFibre` — the unconditional statement.
-/

open Work.TangentClasses

namespace Work.Thom

noncomputable section

variable {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {ι : Type}

/-- **Vanishing of the relative cohomology of a bundle piece below the rank, for an arbitrary
finite-dimensional fibre, from the Euclidean model.**  If `H^m(W × ℝⁿ, W × (ℝⁿ∖0)) = 0` for every
space `W` and every `m < n` (`hEuc`), then for every real bundle `Z` over `B` with model fibre `F`
and every `W` contained in a single chart of `Z`, the relative cohomology of the piece over `W`
vanishes in degrees below `finrank ℝ F`. -/
theorem subsingleton_PieceCoh_genFibre_of_euclidean
    (hEuc : ∀ (n : ℕ) (W : Type) [TopologicalSpace W] (m : ℕ), m < n →
      Subsingleton ((Work.Cohomology.relComplex ℤ (TopCat.of (W × (Fin n → ℝ)))
        {p : W × (Fin n → ℝ) | (p.2 : Fin n → ℝ) ≠ 0}).homology m))
    [FiniteDimensional ℝ F] (ι : Type) [Inhabited ι]
    (Z : Work.TangentClasses.RealBundle B F ι) (i : ι)
    {W : Set B} (hW : W ⊆ Z.baseSet i) {m : ℕ} (hm : m < Module.finrank ℝ F) :
    Subsingleton (Work.Thom.PieceCoh Z W m) := by
  -- the chart homeomorphism `(X|_W, X|_W∖0) ≅ (↥W × F, ↥W × (F∖0))`
  obtain ⟨hW1, hW2⟩ := pieceChartHomeo Z i hW
  -- the fibre homeomorphism `F ≃ₜ ℝ^{finrank F}`
  have hfr : Module.finrank ℝ F =
      Module.finrank ℝ (EuclideanSpace ℝ (Fin (Module.finrank ℝ F))) := by
    rw [finrank_euclideanSpace_fin]
  let eF : F ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ F)) :=
    ContinuousLinearEquiv.ofFinrankEq (𝕜 := ℝ) (E := F)
      (F := EuclideanSpace ℝ (Fin (Module.finrank ℝ F))) hfr
  let e2 : ↥W × F ≃ₜ ↥W × (Fin (Module.finrank ℝ F) → ℝ) :=
    Homeomorph.prodCongr (Homeomorph.refl ↥W)
      (eF.toHomeomorph.trans (PiLp.homeomorph 2 (fun _ : Fin (Module.finrank ℝ F) => ℝ)))
  let e : ↥(Z.proj ⁻¹' W) ≃ₜ ↥W × (Fin (Module.finrank ℝ F) → ℝ) := hW1.trans e2
  have hiff : ∀ z : ↥(Z.proj ⁻¹' W),
      z ∈ {y : ↥(Z.proj ⁻¹' W) | (y : Z.TotalSpace) ∈ zeroComplement Z} ↔
        e z ∈ {p : ↥W × (Fin (Module.finrank ℝ F) → ℝ) |
          (p.2 : Fin (Module.finrank ℝ F) → ℝ) ≠ 0} := by
    intro z
    simp only [Set.mem_ofPred_eq]
    rw [hW2 z]
    have hthis : (e z).2 = (eF (hW1 z).2).ofLp := rfl
    rw [hthis]
    have key : (eF (hW1 z).2).ofLp ≠ 0 ↔ (hW1 z).2 ≠ 0 := by
      constructor
      · intro h h0
        apply h
        rw [h0, map_zero]
        rfl
      · intro h h0
        apply h
        exact (ContinuousLinearEquiv.map_eq_zero_iff eF).mp
          ((WithLp.ofLp_eq_zero (p := 2)).mp h0)
    exact key.symm
  -- relative cohomology is invariant under the homeomorphism of pairs
  obtain ⟨iso⟩ := Work.Cohomology.relCohomology_homeomorph_pairs
    {y : ↥(Z.proj ⁻¹' W) | (y : Z.TotalSpace) ∈ zeroComplement Z}
    {p : ↥W × (Fin (Module.finrank ℝ F) → ℝ) | (p.2 : Fin (Module.finrank ℝ F) → ℝ) ≠ 0}
    e hiff m
  exact Work.Cohomology.subsingleton_of_iso iso.symm (hEuc (Module.finrank ℝ F) ↥W m hm)

/-- **Vanishing of the relative cohomology of a bundle piece below the rank.**  For a real vector
bundle `Z` with model fibre `F` and a set `W ⊆ B` contained in a single chart `i` of the bundle,
the relative cohomology of the piece of the Thom pair over `W`,
`Work.Thom.PieceCoh Z W m = H^m(X|_W, X|_W ∖ 0)`, vanishes for `m < finrank ℝ F`. -/
theorem subsingleton_PieceCoh_genFibre {B : Type} [TopologicalSpace B]
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {ι : Type} [Inhabited ι] (Z : Work.TangentClasses.RealBundle B F ι) (i : ι)
    {W : Set B} (hW : W ⊆ Z.baseSet i) {m : ℕ} (hm : m < Module.finrank ℝ F) :
    Subsingleton (Work.Thom.PieceCoh Z W m) :=
  subsingleton_PieceCoh_genFibre_of_euclidean
    (fun n W _ m hm => subsingleton_relComplex_euclidean_punctured
      (fun n W _ m hm => subsingleton_relComplex_cube n W m hm) n W m hm)
    ι Z i hW hm

end

end Work.Thom
