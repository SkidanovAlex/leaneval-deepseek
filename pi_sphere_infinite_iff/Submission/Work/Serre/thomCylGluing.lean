import Mathlib
import Submission.Work.Serre.CellStep.Geom
import Submission.Work.Serre.CellStep.compressRel_cellU
import Submission.Work.RatHurewicz.thomCylAt_of_compress
import Submission.Work.RatHurewicz.cupBijectiveOverPiece
import Submission.Work.RatHurewicz.cupBijectiveOfThom
import Submission.Work.RatHurewicz.AttachPush.CellInterior
import Submission.Work.Serre.bijective_mixedCup_of_openCover
import Submission.Work.Serre.bijective_mixedCup_of_disjoint_iUnion
import Submission.Work.Serre.cellStepAssembly
import Submission.Work.Serre.thomCylLadderEps
import Submission.Work.Serre.thomCylAtOfWeakEquivBase
import Submission.Work.Serre.cupIso_of_ne_zero_of_thomCylAt
import Submission.Work.RatHurewicz.discPairSourceRankOne
import Submission.Work.RatHurewicz.towerStepData
import Submission.Work.Serre.DiscPair.pathConnectedSpace_preimage_of_isSerreFibration
import Submission.Work.Serre.CWModel.Defs
import Submission.Work.Serre.pathConnectedSpace_cellShellSet
import Submission.Work.Serre.bijective_cup_zero_of_ne_zero

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option synthInstance.maxHeartbeats 400000


/-!
# The cellular step of the CW-model Thom case, from the shell pieces

`Work.Serre.thomCylCellStep_of_shells` reduces the cellular step `Work.Serre.thomCylCellStep` to
the *shell* pieces: the open annular pieces `{ρ < ‖y‖ < R}` inside the attached cells.

The proof uses the two-set cover of `Γ' = attachCells (D-2) Γ ι f`

  `Γ' = cellU f ρ ∪ cellV f R`      (`0 < ρ < R ≤ 1`)

(with `cellU f ρ = (⋃ᵢ ρ-ball)ᶜ` a thickening of the old part and `cellV f R = ⋃ᵢ R-ball`), whose
intersection is the union of the shells `cellShellImg f ρ R = ⋃ᵢ χᵢ''{ρ < ‖·‖ < R}`
(`Work.Serre.cellU_inter_cellV`).  The three Mayer–Vietoris inputs are

* over `cellU f ρ`: the induction hypothesis (`Work.RatHurewicz.thomCylAt_of_compress`), then the
  local cup isomorphism `Work.RatHurewicz.cupBijective_cylPre_of_thomCylAt`;
* over `cellV f R = ⋃ᵢ χᵢ'' {‖·‖ < R}`: the disjoint union of the (weakly contractible) open balls,
  glued by `Work.RatHurewicz.cupBijective_cylPre` + `Work.Serre.bijective_mixedCup_of_disjoint_iUnion`;
* over the shell `⋃ᵢ χᵢ'' {ρ < ‖·‖ < R}`: the same, from the *shell* inputs.

This is the correct cover for the cellular step: the shell `≃ S^{D-1} × (ρ,R)` is *not*
contractible and cannot be covered by contractible pieces with contractible intersections (the
Mayer–Vietoris/acyclicity argument), so its cup isomorphism has to come from a *thickening*
argument (the shell is a thickening of the interior sphere `S^{D-1}`, one dimension down) — which is
what the `hshell` hypothesis supplies.
-/

namespace Work.Serre

open CategoryTheory CategoryTheory.Limits
open scoped Topology

open Work.RatHurewicz

noncomputable section

set_option maxHeartbeats 3200000

variable {D : ℕ} {Γ : Type} [TopologicalSpace Γ] {ι : Type} {X : Type} [TopologicalSpace X]

/-! ## Small helpers (local copies of the `subSet` toolkit) -/

/-- The trace of `A ⊆ Z` on a subset `T ⊆ Z`, read as a subset of `↥T`. -/
abbrev glueSub {Z : Type} (A T : Set Z) : Set ↥T := {y | (y : Z) ∈ A}

/-- The canonical inclusion `↥T → Z`. -/
abbrev glueInclT {Z : Type} [TopologicalSpace Z] (T : Set Z) : C(↥T, Z) :=
  ⟨(Subtype.val : ↥T → Z), continuous_subtype_val⟩

/-- The canonical inclusion `↥(glueSub S T) → ↥T`. -/
abbrev glueInclST {Z : Type} [TopologicalSpace Z] (S T : Set Z) :
    C(↥(glueSub S T), ↥T) :=
  ⟨(Subtype.val : ↥(glueSub S T) → ↥T), continuous_subtype_val⟩

/-- The canonical inclusion `↥(glueSub S T) → Z`. -/
abbrev glueInclSZ {Z : Type} [TopologicalSpace Z] (S T : Set Z) :
    C(↥(glueSub S T), Z) := (glueInclT T).comp (glueInclST S T)

/-- The canonical homeomorphism `↥(glueSub S T) ≃ₜ ↥S` for `S ⊆ T`. -/
def glueHomeo {Z : Type} [TopologicalSpace Z] (S T : Set Z) (hST : S ⊆ T) :
    ↥(glueSub S T) ≃ₜ ↥S where
  toFun y := ⟨y.1.1, y.2⟩
  invFun z := ⟨⟨z.1, hST z.2⟩, z.2⟩
  left_inv y := Subtype.ext (Subtype.ext rfl)
  right_inv z := Subtype.ext rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The two spellings of the restriction of a class to a sub-ambient coincide. -/
theorem relCohMap_glue_comp {Z : Type} [TopologicalSpace Z] (A S T : Set Z) (hST : S ⊆ T)
    (n : ℕ) (U₀ : Work.Thom.RelCoh ℚ n Z A) :
    (Work.Thom.relCohMap (glueInclST S T) (glueSub (glueSub A T) (glueSub S T))
        (glueSub A T) (fun _ hy => hy) ℚ n).hom
      ((Work.Thom.relCohMap (glueInclT T) (glueSub A T) A (fun _ hy => hy) ℚ n).hom U₀)
    = (Work.Thom.relCohMap (glueInclSZ S T) (glueSub (glueSub A T) (glueSub S T)) A
        (fun _ hy => hy) ℚ n).hom U₀ :=
  Work.Thom.relCohMap_compA_apply (glueSub (glueSub A T) (glueSub S T)) (glueSub A T) A
    (glueInclST S T) (glueInclT T) (fun _ hy => hy) (fun _ hy => hy) (fun _ hy => hy) ℚ n U₀

/-- **The cup bijectivity transported to a sub-ambient.** -/
theorem bijective_cup_glueSub {Z : Type} [TopologicalSpace Z] (A S T : Set Z) (hST : S ⊆ T)
    (n₀ K : ℕ) (U₀ : Work.Thom.RelCoh ℚ n₀ Z A)
    (hb : ∀ m, m + n₀ ≤ K → Function.Bijective (fun x : Work.Thom.Coh ℚ m ↥S =>
      (Work.Thom.mixedCupC ℚ (glueSub A S) m n₀) x
        ((Work.Thom.relCohMap (glueInclT S) (glueSub A S) A (fun _ hy => hy) ℚ n₀).hom U₀))) :
    ∀ m, m + n₀ ≤ K → Function.Bijective (fun x : Work.Thom.Coh ℚ m ↥(glueSub S T) =>
      (Work.Thom.mixedCupC ℚ (glueSub (glueSub A T) (glueSub S T)) m n₀) x
        ((Work.Thom.relCohMap (glueInclST S T) (glueSub (glueSub A T) (glueSub S T))
            (glueSub A T) (fun _ hy => hy) ℚ n₀).hom
          ((Work.Thom.relCohMap (glueInclT T) (glueSub A T) A (fun _ hy => hy) ℚ n₀).hom U₀))) := by
  have he : ∀ y : ↥(glueSub S T),
      y ∈ glueSub (glueSub A T) (glueSub S T) ↔
        (glueHomeo S T hST : C(↥(glueSub S T), ↥S)) y ∈ glueSub A S := fun y => Iff.rfl
  intro m hm
  have hb' := Work.RatHurewicz.bijective_mixedCup_of_homeo (glueHomeo S T hST)
    (glueSub (glueSub A T) (glueSub S T)) (glueSub A S) he m n₀
    ((Work.Thom.relCohMap (glueInclT S) (glueSub A S) A (fun _ hy => hy) ℚ n₀).hom U₀) (hb m hm)
  have hside : ((Work.Thom.relCohMap (glueHomeo S T hST : C(↥(glueSub S T), ↥S))
        (glueSub (glueSub A T) (glueSub S T)) (glueSub A S) (fun x hx => (he x).mp hx) ℚ n₀).hom
      ((Work.Thom.relCohMap (glueInclT S) (glueSub A S) A (fun _ hy => hy) ℚ n₀).hom U₀))
    = ((Work.Thom.relCohMap (glueInclST S T) (glueSub (glueSub A T) (glueSub S T))
          (glueSub A T) (fun _ hy => hy) ℚ n₀).hom
        ((Work.Thom.relCohMap (glueInclT T) (glueSub A T) A (fun _ hy => hy) ℚ n₀).hom U₀)) := by
    rw [Work.Thom.relCohMap_compA_apply (glueSub (glueSub A T) (glueSub S T)) (glueSub A S) A
      (glueHomeo S T hST : C(↥(glueSub S T), ↥S)) (glueInclT S) (fun x hx => (he x).mp hx)
      (fun _ hy => hy) (fun _ hy => hy) ℚ n₀ U₀,
      relCohMap_glue_comp A S T hST n₀ U₀]
    have hmap : (glueInclT S).comp (glueHomeo S T hST : C(↥(glueSub S T), ↥S)) =
        glueInclSZ S T := ContinuousMap.ext fun y => rfl
    exact congrArg (fun φ => φ.hom U₀) (Work.Thom.relCohMap_congrA
      (glueSub (glueSub A T) (glueSub S T)) A hmap
      (fun _ hy => hy) (fun _ hy => hy) ℚ n₀)
  rw [hside] at hb'
  exact hb'

/-! ## Path connectedness and contractibility of the pieces -/

/-- **The old part `S = range (attachIncl n Γ ι f)` is path connected.** -/
theorem pathConnectedSpace_ladS (n : ℕ) (Γ : Type) [TopologicalSpace Γ] [PathConnectedSpace Γ]
    (ι : Type) (f : ι → C(Work.RatHurewicz.cellSphere n, Γ)) :
    PathConnectedSpace ↥(Set.range (Work.RatHurewicz.attachIncl n Γ ι f)) := by
  have h : IsPathConnected (Set.range (Work.RatHurewicz.attachIncl n Γ ι f)) := by
    simpa only [Set.image_univ] using
      (isPathConnected_univ (X := Γ)).image (f := Work.RatHurewicz.attachIncl n Γ ι f)
        (Work.RatHurewicz.attachIncl n Γ ι f).continuous
  exact isPathConnected_iff_pathConnectedSpace.mp h

/-- **The witness of the induction hypothesis over a path connected base is non-zero.** -/
theorem thomCylAt_choose_ne_zero {B : Type} [TopologicalSpace B] [PathConnectedSpace B]
    {E : Type} [TopologicalSpace E] (p : C(E, B)) {r N : ℕ} (hr : 1 ≤ r) (hN : r ≤ N)
    (h : ThomCylAt r N p) : h.choose ≠ 0 := by
  intro h0
  have hspec := h.choose_spec 0 (by omega)
  have hzero : (((Work.Thom.mixedCupC ℚ (Set.range (cylIncl p)) 0 (r + 1)).flip h.choose) ∘ₗ
      (Work.Thom.CohMap (cylRetract p) ℚ 0).hom)
      = (0 : Work.Thom.Coh ℚ 0 B →ₗ[ℚ]
          Work.Thom.RelCoh ℚ (0 + (r + 1)) (cyl p) (Set.range (cylIncl p))) := by
    rw [h0]
    ext x
    simp
  rw [hzero] at hspec
  have hbij : Function.Bijective (0 : Work.Thom.Coh ℚ 0 B →ₗ[ℚ]
      Work.Thom.RelCoh ℚ (0 + (r + 1)) (cyl p) (Set.range (cylIncl p))) := by
    have hh := (CategoryTheory.ConcreteCategory.isIso_iff_bijective
      (ModuleCat.ofHom (0 : Work.Thom.Coh ℚ 0 B →ₗ[ℚ]
        Work.Thom.RelCoh ℚ (0 + (r + 1)) (cyl p) (Set.range (cylIncl p))))).mp hspec
    simpa using hh
  obtain ⟨eB⟩ := (ratCoh_ratH_iso_rat (TopCat.of B) 0).mpr (ratH_zero_of_pathConnected B)
  have hne : eB.inv.hom (1 : ℚ) ≠ 0 := by
    intro hh
    have h1 : eB.hom.hom (eB.inv.hom (1 : ℚ)) = (1 : ℚ) := by
      have h3 := congrArg (fun (g : ModuleCat.of ℚ ℚ ⟶ ModuleCat.of ℚ ℚ) =>
        ModuleCat.Hom.hom g (1 : ℚ)) (Iso.inv_hom_id eB)
      simpa [ModuleCat.hom_comp] using h3
    rw [hh, map_zero] at h1
    exact one_ne_zero h1.symm
  exact hne (hbij.1 rfl)

/-- **The extension class of the cellular step is non-zero.** -/
theorem cellStepU_ne_zero (r N D : ℕ) (hr : 1 ≤ r) (hN : r ≤ N) (hD : 2 ≤ D)
    {Γ : Type} [TopologicalSpace Γ] (hΓ : PathConnectedSpace Γ) (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D - 2), Γ))
    {X : Type} [TopologicalSpace X] (q : C(X, Work.RatHurewicz.attachCells (D - 2) Γ ι f))
    (hq : Work.StemsB.IsSerreFibration q)
    (hvan : ∀ γ : Work.RatHurewicz.attachCells (D - 2) Γ ι f, ∀ t : ℕ, 0 < t → t ≠ r → t ≤ N →
      CategoryTheory.Limits.IsZero (ratH (TopCat.of (Work.StemsB.fibre q γ)) t))
    (hpc : ∀ γ : Work.RatHurewicz.attachCells (D - 2) Γ ι f,
      PathConnectedSpace (Work.StemsB.fibre q γ))
    (IH : ThomCylAt r N (restrictFibre q (Set.range (Work.RatHurewicz.attachIncl (D - 2) Γ ι f)))) :
    cellStepU r N D hr hN hD hΓ ι f q hq hvan hpc IH ≠ 0 := by
  haveI : PathConnectedSpace ↥(Set.range (Work.RatHurewicz.attachIncl (D - 2) Γ ι f)) :=
    pathConnectedSpace_ladS (D - 2) Γ ι f
  exact extensionClass_ne_zero r q (Set.range (Work.RatHurewicz.attachIncl (D - 2) Γ ι f))
    Work.RatHurewicz.isClosed_range_attachIncl IH.choose
    (thomCylAt_choose_ne_zero _ hr hN IH) _
    (cellStepU_spec r N D hr hN hD hΓ ι f q hq hvan hpc IH)

/-- **The thickening `cellU f ρ` of the old part is path connected** (for `0 < ρ < 1`): it
compresses onto the old part in dimension zero, and the old part is path connected. -/
theorem pathConnectedSpace_cellU (n : ℕ) (Γ : Type) [TopologicalSpace Γ] [PathConnectedSpace Γ]
    (ι : Type) (f : ι → C(Work.RatHurewicz.cellSphere n, Γ)) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    PathConnectedSpace ↥(cellU (Γ := Γ) (ι := ι) f ρ) := by
  haveI hS : PathConnectedSpace ↥(Set.range (Work.RatHurewicz.attachIncl n Γ ι f)) :=
    pathConnectedSpace_ladS n Γ ι f
  have hSV : Set.range (Work.RatHurewicz.attachIncl n Γ ι f) ⊆ cellU (Γ := Γ) (ι := ι) f ρ :=
    fun x hx => by
      rw [cellU, Set.mem_compl_iff]
      intro hc
      exact Set.disjoint_left.mp
        (disjoint_cellBallImg_range (n := n) (Γ := Γ) (ι := ι) f hρ1) hc hx
  obtain ⟨s⟩ := hS.nonempty
  refine ⟨?_, ?_⟩
  · exact ⟨⟨(s : ↥(Set.range (Work.RatHurewicz.attachIncl n Γ ι f))).1,
      hSV (s : ↥(Set.range (Work.RatHurewicz.attachIncl n Γ ι f))).2⟩⟩
  · intro x y
    have hc := Work.Serre.CellStep.compressRel_cellU n Γ ι f hρ0 hρ1 0
    obtain ⟨a, ha⟩ := Work.RatHurewicz.joined_of_compressRel_zero hc x
    obtain ⟨b, hb⟩ := Work.RatHurewicz.joined_of_compressRel_zero hc y
    have hab : Joined (a : ↥(cellU (Γ := Γ) (ι := ι) f ρ))
        (b : ↥(cellU (Γ := Γ) (ι := ι) f ρ)) := by
      let ιS : C(↥(Set.range (Work.RatHurewicz.attachIncl n Γ ι f)),
          ↥(cellU (Γ := Γ) (ι := ι) f ρ)) :=
        ⟨fun x => ⟨x.1, hSV x.2⟩, Continuous.subtype_mk continuous_subtype_val _⟩
      have h := (PathConnectedSpace.joined
        (⟨a.1.1, a.2⟩ : ↥(Set.range (Work.RatHurewicz.attachIncl n Γ ι f)))
        (⟨b.1.1, b.2⟩ : ↥(Set.range (Work.RatHurewicz.attachIncl n Γ ι f)))).map ιS.continuous
      rw [show ιS ⟨a.1.1, a.2⟩ = a from Subtype.ext rfl,
        show ιS ⟨b.1.1, b.2⟩ = b from Subtype.ext rfl] at h
      exact h
    exact ha.trans (hab.trans hb.symm)

/-- **The shell piece of a cell is path connected.** -/
theorem pathConnectedSpace_cellImg_cellShellSet (n : ℕ) (Γ : Type) [TopologicalSpace Γ]
    (ι : Type) (f : ι → C(Work.RatHurewicz.cellSphere n, Γ)) {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R)
    (hR1 : R ≤ 1) (i : ι) :
    PathConnectedSpace ↥(cellImg (Γ := Γ) (ι := ι) f i (cellShellSet n ρ R)) := by
  have h : IsPathConnected (cellShellSet n ρ R) :=
    isPathConnected_iff_pathConnectedSpace.mpr (pathConnectedSpace_cellShellSet n hρ hρR hR1)
  have h2 : IsPathConnected (cellImg (Γ := Γ) (ι := ι) f i (cellShellSet n ρ R)) := by
    simpa only [cellImg] using h.image (Work.RatHurewicz.cellMap n Γ ι f i).continuous
  exact isPathConnected_iff_pathConnectedSpace.mp h2

/-! ## The cellular step, from the shell pieces -/

/-- **The cellular step of the CW-model Thom case, from the shell pieces.**

Let `Γ' = Work.RatHurewicz.attachCells (D-2) Γ ι f`, `q : C(X,Γ')` a Serre fibration with path
connected fibres that are rationally `S^r` through degree `N`, and let the conclusion be known over
the old part `S = range (attachIncl (D-2) Γ ι f)`.  Suppose moreover that for every cell `i` the
conclusion holds over the shell `χᵢ'' {ρ < ‖·‖ < R}` of the `i`-th cell.  Then the conclusion holds
for `q`. -/
theorem thomCylCellStep_of_shells (r N D : ℕ) (hr : 1 ≤ r) (hN : r ≤ N) (hD : 2 ≤ D)
    {Γ : Type} [TopologicalSpace Γ] (hΓ : PathConnectedSpace Γ) (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D - 2), Γ))
    {X : Type} [TopologicalSpace X] (q : C(X, Work.RatHurewicz.attachCells (D - 2) Γ ι f))
    (hq : Work.StemsB.IsSerreFibration q)
    (hvan : ∀ γ : Work.RatHurewicz.attachCells (D - 2) Γ ι f, ∀ t : ℕ, 0 < t → t ≠ r → t ≤ N →
      CategoryTheory.Limits.IsZero (ratH (TopCat.of (Work.StemsB.fibre q γ)) t))
    (hgen : ∀ γ : Work.RatHurewicz.attachCells (D - 2) Γ ι f,
      Nonempty (ratH (TopCat.of (Work.StemsB.fibre q γ)) r ≅ ModuleCat.of ℚ ℚ))
    (hpc : ∀ γ : Work.RatHurewicz.attachCells (D - 2) Γ ι f,
      PathConnectedSpace (Work.StemsB.fibre q γ))
    (IH : ThomCylAt r N (restrictFibre q (Set.range (Work.RatHurewicz.attachIncl (D - 2) Γ ι f))))
    (ρ R : ℝ) (hρ : 0 < ρ) (hρR : ρ < R) (hR1 : R ≤ 1)
    (hball : ∀ i : ι, ∀ m : ℕ, m + (r + 1) ≤ N + 1 → Function.Bijective
      (fun x : Work.Thom.Coh ℚ m ↥((cylRetract q) ⁻¹'
          (cellImg (Γ := Γ) (ι := ι) f i (cellOpenBallSet (D - 2) R))) =>
        (Work.Thom.mixedCupC ℚ (glueSub (Set.range (cylIncl q)) ((cylRetract q) ⁻¹'
            (cellImg (Γ := Γ) (ι := ι) f i (cellOpenBallSet (D - 2) R)))) m (r + 1)) x
          ((Work.Thom.relCohMap (glueInclT ((cylRetract q) ⁻¹'
              (cellImg (Γ := Γ) (ι := ι) f i (cellOpenBallSet (D - 2) R))))
            (glueSub (Set.range (cylIncl q)) ((cylRetract q) ⁻¹'
              (cellImg (Γ := Γ) (ι := ι) f i (cellOpenBallSet (D - 2) R))))
            (Set.range (cylIncl q)) (fun _ hy => hy) ℚ (r + 1)).hom
            (cellStepU r N D hr hN hD hΓ ι f q hq hvan hpc IH))))
    (hshell : ∀ i : ι, ∀ m : ℕ, m + (r + 1) ≤ N + 1 → Function.Bijective
      (fun x : Work.Thom.Coh ℚ m ↥((cylRetract q) ⁻¹'
          (cellImg (Γ := Γ) (ι := ι) f i (cellShellSet (D - 2) ρ R))) =>
        (Work.Thom.mixedCupC ℚ (glueSub (Set.range (cylIncl q)) ((cylRetract q) ⁻¹'
            (cellImg (Γ := Γ) (ι := ι) f i (cellShellSet (D - 2) ρ R)))) m (r + 1)) x
          ((Work.Thom.relCohMap (glueInclT ((cylRetract q) ⁻¹'
              (cellImg (Γ := Γ) (ι := ι) f i (cellShellSet (D - 2) ρ R))))
            (glueSub (Set.range (cylIncl q)) ((cylRetract q) ⁻¹'
              (cellImg (Γ := Γ) (ι := ι) f i (cellShellSet (D - 2) ρ R))))
            (Set.range (cylIncl q)) (fun _ hy => hy) ℚ (r + 1)).hom
            (cellStepU r N D hr hN hD hΓ ι f q hq hvan hpc IH)))) :
    ThomCylAt r N q := by
  classical
  have hρ1 : ρ < 1 := lt_of_lt_of_le hρR hR1
  have hR0 : 0 < R := lt_trans hρ hρR
  set A : Set (cyl q) := Set.range (cylIncl q) with hA
  set W₁ : Set (cyl q) := (cylRetract q) ⁻¹' (cellU (Γ := Γ) (ι := ι) f ρ) with hW₁
  set W₂ : Set (cyl q) := (cylRetract q) ⁻¹' (cellV (Γ := Γ) (ι := ι) f R) with hW₂
  set Wb : ι → Set (cyl q) :=
    fun i => (cylRetract q) ⁻¹' (cellImg (Γ := Γ) (ι := ι) f i (cellOpenBallSet (D - 2) R))
    with hWb
  set Ws : ι → Set (cyl q) :=
    fun i => (cylRetract q) ⁻¹' (cellImg (Γ := Γ) (ι := ι) f i (cellShellSet (D - 2) ρ R))
    with hWs
  have hW₁o : IsOpen W₁ :=
    (isOpen_cellU (Γ := Γ) (ι := ι) f hρ1).preimage (cylRetract q).continuous
  have hW₂o : IsOpen W₂ :=
    (isOpen_cellV (Γ := Γ) (ι := ι) f hR1).preimage (cylRetract q).continuous
  have hcov : W₁ ∪ W₂ = Set.univ := by
    rw [hW₁, hW₂, ← Set.preimage_union, cellU_union_cellV (Γ := Γ) (ι := ι) f hρR,
      Set.preimage_univ]
  have hW₂eq : W₂ = ⋃ i, Wb i := by
    rw [hW₂, hWb, cellV, cellOpenBallImg, Set.preimage_iUnion]
  have hW₁₂eq : W₁ ∩ W₂ = ⋃ i, Ws i := by
    rw [hW₁, hW₂, ← Set.preimage_inter, cellU_inter_cellV (Γ := Γ) (ι := ι) f hR1 hρR,
      cellShellImg, hWs, Set.preimage_iUnion]
  -- the extension class
  set U₀ : Work.Thom.RelCoh ℚ (r + 1) (cyl q) (Set.range (cylIncl q)) :=
    cellStepU r N D hr hN hD hΓ ι f q hq hvan hpc IH with hU₀def
  have hU₀ : U₀ ≠ 0 := by
    rw [hU₀def]
    exact cellStepU_ne_zero r N D hr hN hD hΓ ι f q hq hvan hpc IH
  haveI hΓ' : PathConnectedSpace (Work.RatHurewicz.attachCells (D - 2) Γ ι f) := by
    haveI := hΓ
    exact Work.Serre.CWModel.pathConnectedSpace_attachCells (D - 2) Γ ι f
  -- the Thom condition over the thickening
  have hThick : ThomCylAt r N (restrictFibre q (cellU (Γ := Γ) (ι := ι) f ρ)) := by
    refine Work.RatHurewicz.thomCylAt_of_compress r N hr q hq
      (Set.range (Work.RatHurewicz.attachIncl (D - 2) Γ ι f))
      (cellU (Γ := Γ) (ι := ι) f ρ) ?_ ?_ ?_ ?_ IH
    · exact fun x hx => by
        rw [cellU, Set.mem_compl_iff]
        intro hc
        exact Set.disjoint_left.mp
          (disjoint_cellBallImg_range (n := D - 2) (Γ := Γ) (ι := ι) f hρ1) hc hx
    · exact Work.RatHurewicz.isClosed_range_attachIncl
    · exact isOpen_cellU (Γ := Γ) (ι := ι) f hρ1
    · intro d
      exact Work.Serre.CellStep.compressRel_cellU (D - 2) Γ ι f hρ hρ1 d
  -- the local statement over the thickening
  have hloc₁ : ∀ m : ℕ, m + (r + 1) ≤ N + 1 → Function.Bijective
      (fun x : Work.Thom.Coh ℚ m ↥W₁ =>
        (Work.Thom.mixedCupC ℚ (glueSub A W₁) m (r + 1)) x
          ((Work.Thom.relCohMap (glueInclT W₁) (glueSub A W₁) A
            (fun _ hy => hy) ℚ (r + 1)).hom U₀)) := by
    intro m hm
    haveI hpcU : PathConnectedSpace ↥(cellU (Γ := Γ) (ι := ι) f ρ) :=
      pathConnectedSpace_cellU (D - 2) Γ ι f hρ hρ1
    exact Work.RatHurewicz.cupBijective_cylPre_of_thomCylAt r N hr hN hΓ' q hq hpc hvan hgen
      (cellU (Γ := Γ) (ι := ι) f ρ) (isOpen_cellU (Γ := Γ) (ι := ι) f hρ1) hpcU hThick U₀ hU₀ m hm
  -- the local statement over the union of the balls
  have hloc₂ : ∀ m : ℕ, m + (r + 1) ≤ N + 1 → Function.Bijective
      (fun x : Work.Thom.Coh ℚ m ↥W₂ =>
        (Work.Thom.mixedCupC ℚ (glueSub A W₂) m (r + 1)) x
          ((Work.Thom.relCohMap (glueInclT W₂) (glueSub A W₂) A
            (fun _ hy => hy) ℚ (r + 1)).hom U₀)) := by
    have hVopen : ∀ i : ι, IsOpen (glueSub (Wb i) W₂) :=
      fun i => (Work.RatHurewicz.isOpen_cellMap_image (n := D - 2) (Y := Γ) (ι := ι) (f := f)
        (i := i) (isOpen_cellOpenBallSet (D - 2) R)
        (cellOpenBallSet_subset_cellInner hR1)).preimage
        ((cylRetract q).comp (glueInclT W₂)).continuous
    have hcovW : (⋃ i, glueSub (Wb i) W₂) = Set.univ := by
      refine Set.eq_univ_iff_forall.mpr (fun x => ?_)
      have hx : (x : cyl q) ∈ ⋃ i, Wb i := by rw [← hW₂eq]; exact x.2
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_iUnion.mpr ⟨i, hi⟩
    have hdisj : ∀ i j : ι, i ≠ j → Disjoint (glueSub (Wb i) W₂) (glueSub (Wb j) W₂) := by
      intro i j hij
      rw [Set.disjoint_left]
      intro x hx hx'
      rw [hWb] at hx hx'
      exact Set.disjoint_left.mp
        (disjoint_cellOpenBallImg (Γ := Γ) (ι := ι) f hR1 hij)
        (Set.mem_preimage.mp hx) (Set.mem_preimage.mp hx')
    have hloc : ∀ i : ι, ∀ m : ℕ, m + (r + 1) ≤ N + 1 → Function.Bijective
        (fun x : Work.Thom.Coh ℚ m ↥(glueSub (Wb i) W₂) =>
          (Work.Thom.mixedCupC ℚ (glueSub (glueSub A W₂) (glueSub (Wb i) W₂)) m (r + 1)) x
            ((Work.Thom.relCohMap (glueInclT (glueSub (Wb i) W₂))
                (glueSub (glueSub A W₂) (glueSub (Wb i) W₂)) (glueSub A W₂)
                (fun _ hy => hy) ℚ (r + 1)).hom
              ((Work.Thom.relCohMap (glueInclT W₂) (glueSub A W₂) A
                (fun _ hy => hy) ℚ (r + 1)).hom U₀))) :=
      fun i => bijective_cup_glueSub A (Wb i) W₂ (fun x hx => by
          rw [hW₂eq]
          exact Set.mem_iUnion.mpr ⟨i, hx⟩) (r + 1) (N + 1) U₀
        (fun m hm => hball i m hm)
    exact Work.Serre.bijective_mixedCup_of_disjoint_iUnion (glueSub A W₂)
      (fun i => glueSub (Wb i) W₂) hVopen hcovW hdisj (r + 1) (N + 1) (by omega)
      ((Work.Thom.relCohMap (glueInclT W₂) (glueSub A W₂) A (fun _ hy => hy) ℚ (r + 1)).hom U₀)
      hloc
  -- the local statement over the union of the shells
  have hloc₁₂ : ∀ m : ℕ, m + (r + 1) ≤ N + 1 → Function.Bijective
      (fun x : Work.Thom.Coh ℚ m ↥(W₁ ∩ W₂) =>
        (Work.Thom.mixedCupC ℚ (glueSub A (W₁ ∩ W₂)) m (r + 1)) x
          ((Work.Thom.relCohMap (glueInclT (W₁ ∩ W₂)) (glueSub A (W₁ ∩ W₂)) A
            (fun _ hy => hy) ℚ (r + 1)).hom U₀)) := by
    have hVopen : ∀ i : ι, IsOpen (glueSub (Ws i) (W₁ ∩ W₂)) :=
      fun i => (Work.RatHurewicz.isOpen_cellMap_image (n := D - 2) (Y := Γ) (ι := ι) (f := f)
        (i := i) (isOpen_cellShellSet (D - 2) ρ R)
        (cellShellSet_subset_cellInner hR1)).preimage
        ((cylRetract q).comp (glueInclT (W₁ ∩ W₂))).continuous
    have hcovW : (⋃ i, glueSub (Ws i) (W₁ ∩ W₂)) = Set.univ := by
      refine Set.eq_univ_iff_forall.mpr (fun x => ?_)
      have hx : (x : cyl q) ∈ ⋃ i, Ws i := by rw [← hW₁₂eq]; exact x.2
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_iUnion.mpr ⟨i, hi⟩
    have hdisj : ∀ i j : ι, i ≠ j → Disjoint (glueSub (Ws i) (W₁ ∩ W₂))
        (glueSub (Ws j) (W₁ ∩ W₂)) := by
      intro i j hij
      rw [Set.disjoint_left]
      intro x hx hx'
      rw [hWs] at hx hx'
      exact Set.disjoint_left.mp
        (disjoint_cellImg (Γ := Γ) (ι := ι) f hij (cellShellSet_subset_cellInner hR1))
        (Set.mem_preimage.mp hx) (Set.mem_preimage.mp hx')
    have hloc : ∀ i : ι, ∀ m : ℕ, m + (r + 1) ≤ N + 1 → Function.Bijective
        (fun x : Work.Thom.Coh ℚ m ↥(glueSub (Ws i) (W₁ ∩ W₂)) =>
          (Work.Thom.mixedCupC ℚ (glueSub (glueSub A (W₁ ∩ W₂)) (glueSub (Ws i) (W₁ ∩ W₂)))
              m (r + 1)) x
            ((Work.Thom.relCohMap (glueInclT (glueSub (Ws i) (W₁ ∩ W₂)))
                (glueSub (glueSub A (W₁ ∩ W₂)) (glueSub (Ws i) (W₁ ∩ W₂)))
                (glueSub A (W₁ ∩ W₂)) (fun _ hy => hy) ℚ (r + 1)).hom
              ((Work.Thom.relCohMap (glueInclT (W₁ ∩ W₂)) (glueSub A (W₁ ∩ W₂)) A
                (fun _ hy => hy) ℚ (r + 1)).hom U₀))) :=
      fun i => bijective_cup_glueSub A (Ws i) (W₁ ∩ W₂) (fun x hx => by
          rw [hW₁₂eq]
          exact Set.mem_iUnion.mpr ⟨i, hx⟩) (r + 1) (N + 1) U₀
        (fun m hm => hshell i m hm)
    exact Work.Serre.bijective_mixedCup_of_disjoint_iUnion (glueSub A (W₁ ∩ W₂))
      (fun i => glueSub (Ws i) (W₁ ∩ W₂)) hVopen hcovW hdisj (r + 1) (N + 1) (by omega)
      ((Work.Thom.relCohMap (glueInclT (W₁ ∩ W₂)) (glueSub A (W₁ ∩ W₂)) A
        (fun _ hy => hy) ℚ (r + 1)).hom U₀)
      hloc
  -- the global bijectivity in positive degrees
  have hglob : ∀ m : ℕ, 1 ≤ m → m + (r + 1) ≤ N + 1 → Function.Bijective
      (fun x : Work.Thom.Coh ℚ m (cyl q) =>
        (Work.Thom.mixedCupC ℚ A m (r + 1)) x U₀) :=
    Work.Serre.bijective_mixedCup_of_openCover A W₁ W₂ hW₁o hW₂o hcov (r + 1) (N + 1) U₀
      hloc₁ hloc₂ hloc₁₂
  -- the cylinder is path connected, and the degree-zero case
  haveI hXpc' : PathConnectedSpace ↥(Set.univ : Set X) := by
    obtain ⟨b₀⟩ := hΓ'.nonempty
    exact Work.Serre.DiscPair.pathConnectedSpace_preimage_of_isSerreFibration q hq
      (V := Set.univ)
      ((Homeomorph.Set.univ (Work.RatHurewicz.attachCells (D - 2) Γ ι f)).symm.surjective
        |>.pathConnectedSpace (Homeomorph.Set.univ _).symm.continuous)
      b₀ (by trivial) (hpc b₀)
  haveI hXpc : PathConnectedSpace X :=
    (Homeomorph.Set.univ X).surjective.pathConnectedSpace (Homeomorph.Set.univ X).continuous
  haveI hcylpc : PathConnectedSpace (cyl q) := Work.Serre.pathConnectedSpace_cyl q
  have hcast : ∀ {a b : ℕ} (h : a = b) {x : Work.Thom.RelCoh ℚ a (cyl q) A}, x ≠ 0 →
      (h ▸ x : Work.Thom.RelCoh ℚ b (cyl q) A) ≠ 0 := by
    intro a b h x hx
    cases h
    exact hx
  refine ⟨U₀, fun m hm => ?_⟩
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · subst hm0
    haveI : PathConnectedSpace (cyl q) := hcylpc
    have hlin : Nonempty (Work.Thom.RelCoh ℚ (r + 1) (cyl q) (Set.range (cylIncl q))
        ≅ ModuleCat.of ℚ ℚ) :=
      Work.RatHurewicz.discPairSourceRankOne r N D hr hD hN hΓ ι f q hq hpc hvan hgen IH
    refine (CategoryTheory.ConcreteCategory.isIso_iff_bijective _).mpr ?_
    simpa only [hU₀def, hA, ModuleCat.hom_ofHom] using
      (Work.Serre.bijective_cup_zero_of_ne_zero r q U₀ hU₀ hlin)
  · have h1 : Function.Bijective (fun x : Work.Thom.Coh ℚ m (cyl q) =>
        (Work.Thom.mixedCupC ℚ A m (r + 1)) x U₀) := hglob m hmpos hm
    have h2 : Function.Bijective ((Work.Thom.CohMap (cylRetract q) ℚ m).hom) :=
      (CategoryTheory.ConcreteCategory.isIso_iff_bijective _).mp (isIso_cohMap_cylRetract q m)
    exact (CategoryTheory.ConcreteCategory.isIso_iff_bijective _).mpr (h1.comp h2)

/-- **The local cup bijectivity over a shell piece, from `ThomCylAt` over it.**  This is the
interface through which the shell step (the shell is a *thickening* of the interior sphere
`S^{D-1}`, one dimension down) feeds the Mayer–Vietoris assembly of
`Work.Serre.thomCylCellStep_of_shells`. -/
theorem bijective_cup_shell_of_thomCylAt (r N D : ℕ) (hr : 1 ≤ r) (hN : r ≤ N) (hD : 2 ≤ D)
    {Γ : Type} [TopologicalSpace Γ] (hΓ : PathConnectedSpace Γ) (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D - 2), Γ))
    {X : Type} [TopologicalSpace X] (q : C(X, Work.RatHurewicz.attachCells (D - 2) Γ ι f))
    (hq : Work.StemsB.IsSerreFibration q)
    (hvan : ∀ γ : Work.RatHurewicz.attachCells (D - 2) Γ ι f, ∀ t : ℕ, 0 < t → t ≠ r → t ≤ N →
      CategoryTheory.Limits.IsZero (ratH (TopCat.of (Work.StemsB.fibre q γ)) t))
    (hgen : ∀ γ : Work.RatHurewicz.attachCells (D - 2) Γ ι f,
      Nonempty (ratH (TopCat.of (Work.StemsB.fibre q γ)) r ≅ ModuleCat.of ℚ ℚ))
    (hpc : ∀ γ : Work.RatHurewicz.attachCells (D - 2) Γ ι f,
      PathConnectedSpace (Work.StemsB.fibre q γ))
    (IH : ThomCylAt r N (restrictFibre q (Set.range (Work.RatHurewicz.attachIncl (D - 2) Γ ι f))))
    {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R) (hR1 : R ≤ 1) (i : ι)
    (hTh : ThomCylAt r N (restrictFibre q
      (cellImg (Γ := Γ) (ι := ι) f i (cellShellSet (D - 2) ρ R)))) :
    ∀ m : ℕ, m + (r + 1) ≤ N + 1 → Function.Bijective
      (fun x : Work.Thom.Coh ℚ m ↥((cylRetract q) ⁻¹'
          (cellImg (Γ := Γ) (ι := ι) f i (cellShellSet (D - 2) ρ R))) =>
        (Work.Thom.mixedCupC ℚ (glueSub (Set.range (cylIncl q)) ((cylRetract q) ⁻¹'
            (cellImg (Γ := Γ) (ι := ι) f i (cellShellSet (D - 2) ρ R)))) m (r + 1)) x
          ((Work.Thom.relCohMap (glueInclT ((cylRetract q) ⁻¹'
              (cellImg (Γ := Γ) (ι := ι) f i (cellShellSet (D - 2) ρ R))))
            (glueSub (Set.range (cylIncl q)) ((cylRetract q) ⁻¹'
              (cellImg (Γ := Γ) (ι := ι) f i (cellShellSet (D - 2) ρ R))))
            (Set.range (cylIncl q)) (fun _ hy => hy) ℚ (r + 1)).hom
            (cellStepU r N D hr hN hD hΓ ι f q hq hvan hpc IH))) := by
  intro m hm
  haveI hpcV : PathConnectedSpace ↥(cellImg (Γ := Γ) (ι := ι) f i (cellShellSet (D - 2) ρ R)) :=
    pathConnectedSpace_cellImg_cellShellSet (D - 2) Γ ι f hρ hρR hR1 i
  haveI hΓ' : PathConnectedSpace (Work.RatHurewicz.attachCells (D - 2) Γ ι f) := by
    haveI := hΓ
    exact Work.Serre.CWModel.pathConnectedSpace_attachCells (D - 2) Γ ι f
  exact Work.RatHurewicz.cupBijective_cylPre_of_thomCylAt r N hr hN hΓ' q hq hpc hvan hgen
    (cellImg (Γ := Γ) (ι := ι) f i (cellShellSet (D - 2) ρ R))
    (Work.RatHurewicz.isOpen_cellMap_image (n := D - 2) (Y := Γ) (ι := ι) (f := f) (i := i)
      (isOpen_cellShellSet (D - 2) ρ R) (cellShellSet_subset_cellInner hR1))
    hpcV hTh _ (cellStepU_ne_zero r N D hr hN hD hΓ ι f q hq hvan hpc IH) m hm


end

end Work.Serre
