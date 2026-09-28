import Mathlib
import Submission.Work.Thom.Cohomology
import Submission.Work.Serre.C1CylExplicit
import Submission.Work.Serre.CsrSharp.relChainsRHomeomorphCompat
import Submission.Work.StemsB.RelChainsR
import Submission.Work.StemsB.RelCochainDualR
import Submission.Work.StemsB.FieldDualUCT

namespace Work.Serre.DiscPair

open CategoryTheory CategoryTheory.Limits

/-!
# The bottom fibre pair of a mapping cylinder

Let `q : X → B` be a continuous map and `w : B`.  Inside the mapping cylinder `cyl q` of `q`, the
bottom copy `range (cylIncl q)` of the source meets the fibre `(cylRetract q)⁻¹ {w}` of the
retraction in the image of the fibre `q⁻¹ {w}`: the (open) embedding `cylIncl q` identifies `X`
with its image in `cyl q` (`Work.Serre.cylHomeoExplicit`, the explicit witness of
`Work.Serre.cylHomeo`), and `cylRetract q ∘ cylIncl q = q`
(`Work.Serre.cylRetract_cylIncl`).

Consequently the pair `(range (cylIncl q), range (cylIncl q) ∩ (cylRetract q)⁻¹ {w})` is isomorphic,
as a pair, to `(X, q⁻¹ {w})`, and the invariance of relative rational homology under a
homeomorphism of pairs (`Work.Serre.CsrSharp.relChainsRHomeomorphCompat`) together with the
universal coefficient theorem over `ℚ` transports the vanishing of the relative homology of
`(X, q⁻¹ {w})` to the relative cohomology of the bottom fibre pair.

The universal coefficient step is proved here, from `Work.StemsB.relComplexIsoDualR` and
`Work.StemsB.fieldDualUCT`, under names of its own (see the section below), so that this file does
not depend on the cone-pair chapter.
-/

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

/-! ## The universal coefficient theorem over `ℚ`, in the form used here -/

/-- The `ℚ`-dual of a zero module is zero. -/
theorem isZero_dualRatModule {M : ModuleCat ℚ} (h : IsZero M) :
    IsZero (ModuleCat.of ℚ (↥M →ₗ[ℚ] ℚ)) :=
  ModuleCat.isZero_iff_subsingleton.mpr
    ⟨fun f g => LinearMap.ext fun x => by
      haveI : Subsingleton ↥M := ModuleCat.isZero_iff_subsingleton.mp h
      rw [Subsingleton.elim x 0]
      simp⟩

/-- **Vanishing of relative homology implies vanishing of relative cohomology over `ℚ`**, by the
two halves of the universal coefficient theorem over the field `ℚ`
(`Work.StemsB.relComplexIsoDualR` and `Work.StemsB.fieldDualUCT`). -/
theorem isZero_relCoh_of_isZero_relH_rat {X : Type} [TopologicalSpace X] (A : Set X) (n : ℕ)
    (h : IsZero ((Work.StemsB.relChainsR ℚ (TopCat.of X) A).homology n)) :
    IsZero (Work.Thom.RelCoh ℚ n X A) := by
  obtain ⟨e⟩ := Work.StemsB.relComplexIsoDualR ℚ (TopCat.of X) A
  obtain ⟨g⟩ := Work.StemsB.fieldDualUCT ℚ (Work.StemsB.relChainsR ℚ (TopCat.of X) A) n
  exact IsZero.of_iso (isZero_dualRatModule h) ((HomologicalComplex.homologyMapIso e n).trans g)

/-- **The bottom fibre pair of the mapping cylinder has the relative cohomology of `(X, q⁻¹ {w})`.**
If the relative rational homology `H_k(X, q⁻¹ {w}; ℚ)` vanishes, then so does the relative rational
cohomology `H^k` of the pair `(range (cylIncl q), range (cylIncl q) ∩ (cylRetract q)⁻¹ {w})`. -/
theorem isZero_relCoh_fibreBottom {B : Type} [TopologicalSpace B] {X : Type} [TopologicalSpace X]
    (q : C(X, B)) (w : B) (k : ℕ)
    (h : CategoryTheory.Limits.IsZero
      ((Work.StemsB.relChainsR ℚ (TopCat.of X) (q ⁻¹' ({w} : Set B))).homology k)) :
    CategoryTheory.Limits.IsZero (Work.Thom.RelCoh ℚ k ↥(Set.range (Work.Serre.cylIncl q))
      {x : ↥(Set.range (Work.Serre.cylIncl q)) |
        (x : Work.Serre.cyl q) ∈ Set.range (Work.Serre.cylIncl q) ∩
          ((Work.Serre.cylRetract q) ⁻¹' ({w} : Set B))}) := by
  classical
  -- the explicit homeomorphism of the source with the bottom copy of the cylinder
  obtain ⟨e, he⟩ := Work.Serre.cylHomeoExplicit q
  have hret : ∀ p : X, (Work.Serre.cylRetract q) ((Work.Serre.cylIncl q) p) = q p :=
    fun p => ContinuousMap.congr_fun (Work.Serre.cylRetract_cylIncl q) p
  -- it carries the fibre `q⁻¹ {w}` onto the second member of the pair
  have hB : ∀ x : X, x ∈ q ⁻¹' ({w} : Set B) ↔
      e x ∈ {x : ↥(Set.range (Work.Serre.cylIncl q)) |
        (x : Work.Serre.cyl q) ∈ Set.range (Work.Serre.cylIncl q) ∩
          ((Work.Serre.cylRetract q) ⁻¹' ({w} : Set B))} := by
    intro x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq, Set.mem_inter_iff,
      Set.mem_range]
    constructor
    · intro hx
      exact ⟨⟨x, (he x).symm⟩, by rw [he x, hret x]; exact hx⟩
    · rintro ⟨-, hw⟩
      rw [he x, hret x] at hw
      exact hw
  -- transport the vanishing of relative homology along the homeomorphism of pairs …
  refine isZero_relCoh_of_isZero_relH_rat _ k ?_
  obtain ⟨iso⟩ := Work.Serre.CsrSharp.relChainsRHomeomorphCompat X _ (q ⁻¹' ({w} : Set B)) _ e hB k
  -- … and pass to relative cohomology over `ℚ`
  exact IsZero.of_iso h iso.symm

end Work.Serre.DiscPair
