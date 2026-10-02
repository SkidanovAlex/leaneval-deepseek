import Mathlib
import Submission.Work.Serre.DiscPair.discPairExtension
import Submission.Work.Serre.DiscPair.oldPartRelCohIso
import Submission.Work.Serre.discPairCellVanishingSucc
import Submission.Work.Serre.DiscPair.isIso_relCohMap_incl_of_isZero
import Submission.Work.Serre.ThomCylDefs
import Submission.Work.Serre.ratH_zero_of_pathConnected
import Submission.Work.Serre.ratCoh_ratH_iso_rat

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The "target line" of the disc-pair bundle

`Work.Serre.DiscPair.discPairTargetLine` computes the rational relative cohomology of the
mapping-cylinder pair `(cyl q, range (cylIncl q))` of a Serre fibration `q` over a space obtained
from a path connected space `Γ` by attaching `D`-cells (`D ≥ 2`), with path connected fibres whose
rational homology is that of `S^r` (through degree `N`): the group

  `H^{r+1}(cyl q, range (cylIncl q); ℚ)`

is a line `ℚ`.

The group is the one in which the *relative Thom class* of the disc-pair bundle lives, so this is
the "the relative Thom class is unique up to scalars" statement — the degree `m = 0` input of the
cellular step of the CW-model Thom case (`Work.Serre.ThomCylAt`).

The proof is a chain of four isomorphisms.

* **The extension across the attached cells.**  With
  `N₀ = (cylRetract q) ⁻¹' S ∪ range (cylIncl q)` (`S = range (attachIncl …)`, the old part of the
  base) and `A = range (cylIncl q)`, the relative groups `H^{r+1}(cyl q, N₀)` and
  `H^{r+2}(cyl q, N₀)` vanish (`Work.Serre.discPairCellVanishingSucc`, the new-cell groups are
  concentrated in degree `D + r + 1 > r + 2`), so the triple long exact sequence (the "third map is
  an isomorphism" fragment `Work.Serre.DiscPair.isIso_relCohMap_incl_of_isZero`) identifies
  `H^{r+1}(cyl q, A)` with `H^{r+1}(N₀, N₀ ∩ A)`.
* **The old part.**  `Work.Serre.DiscPair.oldPartRelCohIso` identifies `H^{r+1}(N₀, N₀ ∩ A)` with
  the relative cohomology `H^{r+1}(cyl (q|_S), range (cylIncl (q|_S)))` of the mapping cylinder of
  the restricted fibration.
* **The induction hypothesis.**  `Work.Serre.ThomCylAt r N (q|_S)` supplies a class `U` whose mixed
  cup with the retraction is an isomorphism in the range; in degree `m = 0` this is an isomorphism
  `H^0(S) ≅ H^{r+1}(cyl (q|_S), range (cylIncl (q|_S)))`.
* **`H^0(S) ≅ ℚ`.**  `S = range (attachIncl …)` is the image of the path connected `Γ` under a
  continuous surjection, hence path connected, and `H^0` of a path connected space with `ℚ`
  coefficients is `ℚ` (`Work.Serre.ratH_zero_of_pathConnected`,
  `Work.Serre.ratCoh_ratH_iso_rat`).
-/

namespace Work.Serre.DiscPair

open CategoryTheory CategoryTheory.Limits

noncomputable section

theorem discPairTargetLine (r N D : ℕ) (hr : 1 ≤ r) (hD : 2 ≤ D) (hrN : r ≤ N)
    {Γ : Type} [TopologicalSpace Γ] (hΓ : PathConnectedSpace Γ) (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D - 2), Γ))
    {X : Type} [TopologicalSpace X] (q : C(X, Work.RatHurewicz.attachCells (D - 2) Γ ι f))
    (hq : Work.StemsB.IsSerreFibration q)
    (hpc : ∀ γ : Work.RatHurewicz.attachCells (D - 2) Γ ι f,
      PathConnectedSpace (Work.StemsB.fibre q γ))
    (hvan : ∀ γ : Work.RatHurewicz.attachCells (D - 2) Γ ι f, ∀ t : ℕ, 0 < t → t ≠ r → t ≤ N →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q γ)) t))
    (hgen : ∀ γ : Work.RatHurewicz.attachCells (D - 2) Γ ι f,
      Nonempty (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q γ)) r ≅ ModuleCat.of ℚ ℚ))
    (IH : Work.Serre.ThomCylAt r N (Work.Serre.restrictFibre q
      (Set.range (Work.RatHurewicz.attachIncl (D - 2) Γ ι f)))) :
    Nonempty (Work.Thom.RelCoh ℚ (r + 1) (Work.Serre.cyl q)
      (Set.range (Work.Serre.cylIncl q)) ≅ ModuleCat.of ℚ ℚ) := by
  classical
  -- ### The old part `S` of the base is path connected
  have hsurj : Function.Surjective (fun γ : Γ =>
      (⟨Work.RatHurewicz.attachIncl (D - 2) Γ ι f γ, ⟨γ, rfl⟩⟩ :
        ↥(Set.range (Work.RatHurewicz.attachIncl (D - 2) Γ ι f)))) :=
    fun x => by obtain ⟨γ, hγ⟩ := x.2; exact ⟨γ, Subtype.ext hγ⟩
  haveI hSpc : PathConnectedSpace ↥(Set.range (Work.RatHurewicz.attachIncl (D - 2) Γ ι f)) :=
    hsurj.pathConnectedSpace (by fun_prop)
  -- ### The new-cell groups vanish in degrees `r + 1` and `r + 2`
  have hz1 : CategoryTheory.Limits.IsZero (Work.Thom.RelCoh ℚ (r + 1) (Work.Serre.cyl q)
      (discPairNew D Γ ι f X q)) :=
    Work.Serre.discPairCellVanishingSucc r N D hr hD hΓ ι f q hq hvan hpc (r + 1)
      (by omega) (by omega)
  have hz2 : CategoryTheory.Limits.IsZero (Work.Thom.RelCoh ℚ (r + 2) (Work.Serre.cyl q)
      (discPairNew D Γ ι f X q)) :=
    Work.Serre.discPairCellVanishingSucc r N D hr hD hΓ ι f q hq hvan hpc (r + 2)
      (by omega) (by omega)
  -- ### Step 1: shrink the relative part from the old part to the bottom copy
  have hiso_ext : CategoryTheory.IsIso (Work.Thom.relCohMap
      (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(discPairNew D Γ ι f X q), Work.Serre.cyl q))
      {x : ↥(discPairNew D Γ ι f X q) | (x : Work.Serre.cyl q) ∈ Set.range (Work.Serre.cylIncl q)}
      (Set.range (Work.Serre.cylIncl q)) (fun _ hx => hx) ℚ (r + 1)) :=
    isIso_relCohMap_incl_of_isZero (TopCat.of (Work.Serre.cyl q))
      (Set.range (Work.Serre.cylIncl q)) (discPairNew D Γ ι f X q) Set.subset_union_right
      (r + 1) hz1 hz2
  haveI := hiso_ext
  let e_ext := asIso (Work.Thom.relCohMap
      (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(discPairNew D Γ ι f X q), Work.Serre.cyl q))
      {x : ↥(discPairNew D Γ ι f X q) | (x : Work.Serre.cyl q) ∈ Set.range (Work.Serre.cylIncl q)}
      (Set.range (Work.Serre.cylIncl q)) (fun _ hx => hx) ℚ (r + 1))
  -- ### Step 2: the identification of the old part
  obtain ⟨e_old⟩ := oldPartRelCohIso D hD ι f q (r + 1)
  -- ### Step 3: the relative Thom class over the old part, in degree `m = 0`
  obtain ⟨U, hU⟩ := IH
  let qS : C(↥(q ⁻¹' Set.range (Work.RatHurewicz.attachIncl (D - 2) Γ ι f)),
      ↥(Set.range (Work.RatHurewicz.attachIncl (D - 2) Γ ι f))) :=
    Work.Serre.restrictFibre q (Set.range (Work.RatHurewicz.attachIncl (D - 2) Γ ι f))
  haveI hU0 : CategoryTheory.IsIso (ModuleCat.ofHom
      (((Work.Thom.mixedCupC ℚ (Set.range (Work.Serre.cylIncl qS)) 0 (r + 1)).flip U) ∘ₗ
        (Work.Thom.CohMap (Work.Serre.cylRetract qS) ℚ 0).hom)) := hU 0 (by omega)
  let e_IH := (asIso (ModuleCat.ofHom
      (((Work.Thom.mixedCupC ℚ (Set.range (Work.Serre.cylIncl qS)) 0 (r + 1)).flip U) ∘ₗ
        (Work.Thom.CohMap (Work.Serre.cylRetract qS) ℚ 0).hom))).symm
  -- ### Step 4: `H^0(S; ℚ) ≅ ℚ`
  obtain ⟨e_top⟩ := (Work.Serre.ratCoh_ratH_iso_rat
      (TopCat.of ↥(Set.range (Work.RatHurewicz.attachIncl (D - 2) Γ ι f))) 0).mpr
    (Work.Serre.ratH_zero_of_pathConnected ↥(Set.range (Work.RatHurewicz.attachIncl (D - 2) Γ ι f)))
  -- ### The degree bookkeeping `0 + (r + 1) = r + 1`
  let e_cast : Work.Thom.RelCoh ℚ (r + 1) (Work.Serre.cyl qS)
        (Set.range (Work.Serre.cylIncl qS)) ≅
      Work.Thom.RelCoh ℚ (0 + (r + 1)) (Work.Serre.cyl qS)
        (Set.range (Work.Serre.cylIncl qS)) :=
    eqToIso (congrArg (fun n => Work.Thom.RelCoh ℚ n (Work.Serre.cyl qS)
      (Set.range (Work.Serre.cylIncl qS))) (Nat.zero_add (r + 1)).symm)
  exact ⟨e_ext ≪≫ e_old ≪≫ e_cast ≪≫ e_IH ≪≫ e_top⟩

end

end Work.Serre.DiscPair
