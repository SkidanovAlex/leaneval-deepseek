import Mathlib
import Submission.Work.Serre.ThomCylCellStepAltDef
import Submission.Work.RatHurewicz.cellStepAt
import Submission.Work.RatHurewicz.cellShellThom
import Submission.Work.RatHurewicz.cellwiseNonvanishing
import Submission.Work.RatHurewicz.cvGoodIUnion
import Submission.Work.RatHurewicz.SphereAssembly
import Submission.Work.RatHurewicz.SphereCover
import Submission.Work.Serre.thomCylGluing
import Submission.Work.Serre.thomCylCellStepBall
import Submission.Work.Serre.compressRel_cellShellImg
import Submission.Work.Serre.cellImgQuarterSphereHomeo
import Submission.Work.Serre.cylRestrictHomeo
import Submission.Work.Serre.isSerreFibration_restrictFibre
import Submission.Work.Serre.CWModelThomAux
import Submission.Work.StemsB.c2oddRangeTwo

set_option synthInstance.maxHeartbeats 400000

/-!
# The shell step of the cellular induction with a supplied Thom class

The cell step `Work.RatHurewicz.CellStepAt D` is assembled by
`Work.Serre.thomCylCellStep_of_shellsBall` from the *shell* family, which
`Work.Serre.bijective_cup_shell_of_thomCylAt` produces from `Work.Serre.ThomCylAt` over the shell
`cellImg i (cellShellSet (D-2) ρ R)`.  `Work.RatHurewicz.cellShellThom` reduces the latter to the
*sphere case* `Work.RatHurewicz.SphThom (D-2)`, i.e. `Work.Serre.SphereThom (D-2) r N`.

That reduction needs a **non-zero class** over the pair of the sphere's fibration, and the
existence of such a class is exactly the missing seed of the whole development (`SphThom 0` for
`D = 2`, i.e. the Thom class over `S¹`).

The point of this file is that **inside the cellular step the non-zero class is free**: the
extension class `Work.Serre.cellStepU` is non-zero (`Work.Serre.cellStepU_ne_zero`, no extra
hypotheses) and restricts non-trivially to the pair over *every* piece of the attached space
(`Work.RatHurewicz.cellwiseNonvanishing`).  So we prove the *conditional* form of the sphere case,
`Work.RatHurewicz.sphereThom_of_nonzeroClass`,

> over `cellSphere k` (any `k ≥ 0`), for any Serre fibration with the fibre data and any *non-zero*
> class `U ∈ H^{r+1}(cyl p, range (cylIncl p))`, the cup map with `U` is bijective in the range, so
> `Work.Serre.ThomCylAt r N p` holds,

using the orthant cover of the sphere (`cvPiece k`, whose pieces have contractible intersections
for every `k`, including `k = 0` where the sphere is `S¹` and the pieces are arcs), and we then
transport it to the `1/4`-sphere of an attached cell and up to the shell by
`Work.RatHurewicz.thomCylAt_of_compress`.

The result is `Work.RatHurewicz.cellStepAtShell` : **`CellStepAt D` for every `D ≥ 2`, with no
residual hypothesis**, hence `Work.Serre.ThomCylCellStepAlt` (the single open node of the E3(b)
tower) and so the requested Gysin theorem.
-/

namespace Work.RatHurewicz

open CategoryTheory CategoryTheory.Limits
open scoped Topology

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

/-! ## The orthant cover of the model sphere, for all `k` -/

/-- **The orthant cover of the model sphere `cellSphere k = S^{k+1}`, for every `k ≥ 0`.**  The
pieces `cvPiece k (Sum.inl j) = {x_j > 0}` and `cvPiece k (Sum.inr ()) = {∑ x < 0}` cover the
sphere; for `k = 0` this is the cover of the circle `S¹` by the three arcs
`{x₀ > 0}`, `{x₁ > 0}`, `{x₀ + x₁ < 0}`.

`Work.RatHurewicz.iUnion_cvPiece` states the same for `k ≥ 1`; the proof does not use `1 ≤ k`, so
it is reproduced here in the form needed for `k = 0`. -/
theorem iUnion_cvPieceAll (k : ℕ) :
    (⋃ i : Fin (k + 2) ⊕ Unit, cvPiece k i) = Set.univ := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  by_contra h
  have hmem : ∀ i, x ∉ cvPiece k i := fun i hi => h ⟨i, hi⟩
  have hle : ∀ j : Fin (k + 2), (x : EuclideanSpace ℝ (Fin (k + 2))) j ≤ 0 := by
    intro j
    have h' := hmem (Sum.inl j)
    simpa only [cvPiece, Set.mem_setOf_eq, not_lt] using h'
  have hlt : ∃ j : Fin (k + 2), (x : EuclideanSpace ℝ (Fin (k + 2))) j < 0 := by
    by_contra hc
    push_neg at hc
    have hnn : ∀ j, (x : EuclideanSpace ℝ (Fin (k + 2))) j = 0 := fun j =>
      le_antisymm (hle j) (hc j)
    have hnorm : ‖(x : EuclideanSpace ℝ (Fin (k + 2)))‖ = 0 := by
      rw [← sq_eq_zero_iff, EuclideanSpace.real_norm_sq_eq]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [hnn j]
      norm_num
    have h1 := x.2
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero, hnorm] at h1
    norm_num at h1
  obtain ⟨j, hj⟩ := hlt
  have h' := hmem (Sum.inr ())
  have hsum : (∑ i : Fin (k + 2), (x : EuclideanSpace ℝ (Fin (k + 2))) i) < 0 := by
    have hsplit : (∑ i : Fin (k + 2), (x : EuclideanSpace ℝ (Fin (k + 2))) i)
        = (x : EuclideanSpace ℝ (Fin (k + 2))) j
          + ∑ i ∈ (Finset.univ : Finset (Fin (k + 2))).erase j,
              (x : EuclideanSpace ℝ (Fin (k + 2))) i :=
      (Finset.add_sum_erase _ _ (Finset.mem_univ j)).symm
    rw [hsplit]
    have h2 : (∑ i ∈ (Finset.univ : Finset (Fin (k + 2))).erase j,
        (x : EuclideanSpace ℝ (Fin (k + 2))) i) ≤ 0 :=
      Finset.sum_nonpos fun i _ => hle i
    linarith
  simp only [cvPiece, Set.mem_setOf_eq, not_lt] at h'
  linarith

/-- The model sphere `cellSphere k` is path connected, for every `k`. -/
theorem pathConnectedSpace_cellSphereAll (k : ℕ) : PathConnectedSpace (cellSphere k) := by
  have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin (k + 2))) := by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
    exact_mod_cast (by omega : 1 < k + 2)
  exact (isPathConnected_iff_pathConnectedSpace).mp
    (isPathConnected_sphere hrank 0 (by norm_num : (0 : ℝ) ≤ 1))

/-! ## The local condition over the pieces of the orthant cover, for all `k` -/

/-- **The three local conditions over the pieces of the orthant cover of `cellSphere k`**, for
*every* `k` (in particular `k = 0`): the mixed cup product with `U` restricted to the piece is
bijective in every degree of the range, and the relative cohomology of the pair over the piece
vanishes in degrees `≤ n₀ - 1`.

This is `Work.RatHurewicz.cvGood_piece` (`Submission/Work/RatHurewicz/SphereAssembly.lean`) with
the unused hypothesis `1 ≤ k` removed, so that it applies to the circle `k = 0`. -/
theorem cvGood_cvPiece (k r N : ℕ) (hr : 1 ≤ r) (hN : r ≤ N)
    {X : Type} [TopologicalSpace X] (p : C(X, cellSphere k))
    (hp : Work.StemsB.IsSerreFibration p)
    (hpc : ∀ γ : cellSphere k, PathConnectedSpace (Work.StemsB.fibre p γ))
    (hvan : ∀ γ : cellSphere k, ∀ t : ℕ, 0 < t → t ≠ r → t ≤ N →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre p γ)) t))
    (hgen : ∀ γ : cellSphere k,
      Nonempty (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre p γ)) r ≅ ModuleCat.of ℚ ℚ))
    (U : Work.Thom.RelCoh ℚ (r + 1) (Work.Serre.cyl p) (Work.Serre.cylBot p)) (hU : U ≠ 0)
    (T : Finset (Fin (k + 2) ⊕ Unit)) (hT : T.Nonempty) :
    CvGood (Work.Serre.cylBot p) (r + 1) (N + 1) U
      (Work.Serre.cylPre p (⋂ i ∈ T, cvPiece k i)) := by
  classical
  by_cases hne : (⋂ i ∈ T, cvPiece k i).Nonempty
  · haveI hcont : ContractibleSpace ↥(⋂ i ∈ T, cvPiece k i) :=
      contractibleSpace_cvInter k T hT hne
    haveI hVpc : PathConnectedSpace ↥(⋂ i ∈ T, cvPiece k i) := inferInstance
    obtain ⟨b₀, hb₀⟩ := hne
    let b : ↥(⋂ i ∈ T, cvPiece k i) := ⟨b₀, hb₀⟩
    haveI hVc : ∀ j : ℕ, Subsingleton (HomotopyGroup (Fin j) ↥(⋂ i ∈ T, cvPiece k i) b) :=
      fun j => Work.Stems.subsingleton_of_contractible b
    have hconc := Work.Serre.relCoh_cylPre_concentrated p hp r N hr hN hpc hvan hgen
      (⋂ i ∈ T, cvPiece k i) (isOpen_cvInter k T) b hVc hVpc
    have hΓ : PathConnectedSpace (cellSphere k) := pathConnectedSpace_cellSphereAll k
    refine ⟨?_, ?_, ?_⟩
    · intro m hm hmK
      exact cupBijective_cylPre r N hr hΓ p hp hpc hvan hgen (⋂ i ∈ T, cvPiece k i)
        (isOpen_cvInter k T) b hVc hVpc U hU m hmK
    · exact cupBijective_cylPre r N hr hΓ p hp hpc hvan hgen (⋂ i ∈ T, cvPiece k i)
        (isOpen_cvInter k T) b hVc hVpc U hU 0 (by omega)
    · intro k' hk'
      exact ModuleCat.isZero_iff_subsingleton.mp (hconc.1 k' (by omega) (by omega))
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne, show Work.Serre.cylPre p (∅ : Set (cellSphere k)) = ∅ from Set.preimage_empty]
    refine ⟨fun m hm hmK => cupBij_empty _ (r + 1) m U, cupBij_empty _ (r + 1) 0 U, ?_⟩
    intro k' hk'
    haveI : IsEmpty ↥(∅ : Set (Work.Serre.cyl p)) := ⟨fun x => x.2⟩
    exact ModuleCat.isZero_iff_subsingleton.mp (Work.Serre.isZero_relCoh_of_isEmpty_space _ _)

/-! ## The sphere case with a supplied non-zero class -/

/-- **The sphere case of the cellular step, conditional on a non-zero class.**  For a Serre
fibration `p` over the model sphere `cellSphere k` (`k ≥ 0`) with the fibre data over *every* point
of the sphere and a **non-zero** class `U ∈ H^{r+1}(cyl p, range (cylIncl p))`, the cup product with
`U` is bijective in the range `m + r + 1 ≤ N + 1`; hence `Work.Serre.ThomCylAt r N p`.

The proof is the local-to-global argument over the orthant cover: over each piece (and each
nonempty finite intersection of pieces) the base is contractible, so the local Thom class exists
and cupping with any non-zero class is an isomorphism
(`Work.RatHurewicz.cupBijective_cylPre`, whose non-vanishing input is
`Work.RatHurewicz.cellwiseNonvanishing`); the gluing is
`Work.RatHurewicz.cvGoodIUnion` (`m ≥ 1`) together with the degree-`0` clause. -/
theorem sphereThom_of_nonzeroClass (k r N : ℕ) (hr : 1 ≤ r) (hN : r ≤ N)
    {X : Type} [TopologicalSpace X] (p : C(X, cellSphere k))
    (hp : Work.StemsB.IsSerreFibration p)
    (hpc : ∀ γ : cellSphere k, PathConnectedSpace (Work.StemsB.fibre p γ))
    (hvan : ∀ γ : cellSphere k, ∀ t : ℕ, 0 < t → t ≠ r → t ≤ N →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre p γ)) t))
    (hgen : ∀ γ : cellSphere k,
      Nonempty (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre p γ)) r ≅ ModuleCat.of ℚ ℚ))
    (U : Work.Thom.RelCoh ℚ (r + 1) (Work.Serre.cyl p) (Set.range (Work.Serre.cylIncl p)))
    (hU : U ≠ 0) :
    Work.Serre.ThomCylAt r N p := by
  classical
  have hfib : ∀ γ : cellSphere k, Nonempty (Work.StemsB.fibre p γ) := fun γ => (hpc γ).nonempty
  have hglue := cvGoodIUnion p hfib (r + 1) (N + 1) (fun i => cvPiece k i)
    (fun i => isOpen_cvPiece k i)
    (fun T hT => cvGood_cvPiece k r N hr hN p hp hpc hvan hgen U hU T hT)
  have hunion : Work.Serre.cylPre p (⋃ i : Fin (k + 2) ⊕ Unit, cvPiece k i) = Set.univ := by
    rw [iUnion_cvPieceAll k]
    exact Set.preimage_univ
  have hcup : ∀ m' : ℕ, m' + (r + 1) ≤ N + 1 → Function.Bijective
      (fun x : Work.Thom.Coh ℚ m' (Work.Serre.cyl p) =>
        (Work.Thom.mixedCupC ℚ (Work.Serre.cylBot p) m' (r + 1)) x U) := by
    intro m' hm'
    rcases Nat.eq_zero_or_pos m' with h0 | hpos
    · subst h0
      refine cupBij_univ _ (r + 1) 0 U ?_
      rw [← hunion]
      exact hglue.2.1
    · refine cupBij_univ _ (r + 1) m' U ?_
      rw [← hunion]
      exact hglue.1 m' hpos hm'
  refine ⟨U, fun m hm => ?_⟩
  have hbij := hcup m (by omega)
  have hret : Function.Bijective (Work.Thom.CohMap (Work.Serre.cylRetract p) ℚ m).hom :=
    (CategoryTheory.ConcreteCategory.isIso_iff_bijective _).mp
      (Work.RatHurewicz.Dfr.isIso_CohMap_cylRetract p m)
  refine (CategoryTheory.ConcreteCategory.isIso_iff_bijective _).mpr ?_
  exact hbij.comp hret

/-! ## The `1/4`-sphere of an attached cell, with a supplied class -/

/-- **The sphere seed with a supplied non-zero class.**  For the `1/4`-sphere
`S = cellImg i (quarterSet n)` of the `i`-th cell of `Γ' = attachCells n Γ ι f` and any **non-zero**
class `U ∈ H^{r+1}(cyl q, range (cylIncl q))` over the ambient space, the conclusion
`Work.Serre.ThomCylAt r N (q|_S)` holds.

Proof.  The restriction of `U` to the pair over `S` is non-zero
(`Work.RatHurewicz.cellwiseNonvanishing`).  Since `S` is closed, the mapping cylinder of `q|_S` is
the part of `cyl q` over `S` (`Work.Serre.cylRestrictHomeo`), and `S ≅ cellSphere n`
(`Work.Serre.cellImgQuarterSphereHomeo`), so the class transports to a non-zero class over the
mapping cylinder of the transported fibration `e₀ ∘ (q|_S)` over `cellSphere n`; there
`Work.RatHurewicz.sphereThom_of_nonzeroClass` applies, and `Work.Serre.thomCylAt_of_homeo`
transports the conclusion back. -/
theorem quarterSphereThom_of_nonzeroClass (n : ℕ) {Γ : Type} [TopologicalSpace Γ]
    (hΓ : PathConnectedSpace Γ) (ι : Type)
    (f : ι → C(cellSphere n, Γ)) (i : ι) {X : Type} [TopologicalSpace X]
    (q : C(X, attachCells n Γ ι f)) (hq : Work.StemsB.IsSerreFibration q) (r N : ℕ)
    (hr : 1 ≤ r) (hN : r ≤ N)
    (hpc : ∀ γ : attachCells n Γ ι f, PathConnectedSpace (Work.StemsB.fibre q γ))
    (hvan : ∀ γ : attachCells n Γ ι f, ∀ t : ℕ, 0 < t → t ≠ r → t ≤ N →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q γ)) t))
    (hgen : ∀ γ : attachCells n Γ ι f,
      Nonempty (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q γ)) r ≅ ModuleCat.of ℚ ℚ))
    (U : Work.Thom.RelCoh ℚ (r + 1) (Work.Serre.cyl q) (Set.range (Work.Serre.cylIncl q)))
    (hU : U ≠ 0) :
    Work.Serre.ThomCylAt r N
      (Work.Serre.restrictFibre q (Work.Serre.cellImg (f := f) i (Work.Serre.quarterSet n))) := by
  classical
  set S : Set (attachCells n Γ ι f) :=
    Work.Serre.cellImg (f := f) i (Work.Serre.quarterSet n) with hS
  obtain ⟨e₀⟩ := Work.Serre.cellImgQuarterSphereHomeo n Γ ι f i
  -- the ambient space is path connected
  haveI hΓ' : PathConnectedSpace (attachCells n Γ ι f) := by
    haveI := hΓ
    exact Work.Serre.CWModel.pathConnectedSpace_attachCells n Γ ι f
  -- a point of the piece
  haveI hneSphere : Nonempty (cellSphere n) :=
    ⟨⟨EuclideanSpace.single 0 (1 : ℝ), by
        rw [Metric.mem_sphere, dist_eq_norm, sub_zero, PiLp.norm_single]
        norm_num⟩⟩
  obtain ⟨z₁⟩ := hneSphere
  let b : ↥S := e₀.symm z₁
  -- the piece is closed
  have hScl : IsClosed S := by
    rw [hS]
    exact Work.Serre.DiscPair.isClosed_cellMap_sphere n Γ ι f i (ρ := 1 / 4) (by norm_num)
  -- (1) the restriction of `U` to the pair over the piece
  let US : Work.Thom.RelCoh ℚ (r + 1) ↥((Work.Serre.cylRetract q) ⁻¹' S)
      (Work.Serre.DiscPair.cylPreBot q S) :=
    (Work.Thom.relCohMap (⟨Subtype.val, continuous_subtype_val⟩ :
        C(↥((Work.Serre.cylRetract q) ⁻¹' S), Work.Serre.cyl q))
      (Work.Serre.DiscPair.cylPreBot q S) (Set.range (Work.Serre.cylIncl q))
      (fun _ hx => hx) ℚ (r + 1)).hom U
  have hUS : US ≠ 0 :=
    cellwiseNonvanishing r N hr hN hΓ' q hq hpc hvan hgen S b.1 b.2 U hU
  -- (2) transport along the identification of the mapping cylinder of `q|_S`
  obtain ⟨eCyl, hbot⟩ := Work.Serre.cylRestrictHomeo q S hScl
  have heC : ∀ y ∈ Set.range (Work.Serre.cylIncl (Work.Serre.restrictFibre q S)),
      eCyl y ∈ Work.Serre.DiscPair.cylPreBot q S := fun y hy => (hbot y).mp hy
  haveI hisoR : CategoryTheory.IsIso (Work.Thom.relCohMap
      (eCyl : C(Work.Serre.cyl (Work.Serre.restrictFibre q S),
        ↥((Work.Serre.cylRetract q) ⁻¹' S)))
      (Set.range (Work.Serre.cylIncl (Work.Serre.restrictFibre q S)))
      (Work.Serre.DiscPair.cylPreBot q S) heC ℚ (r + 1)) :=
    Work.Thom.CapGlue.isIso_relComplexMap_homeomorph
      (Set.range (Work.Serre.cylIncl (Work.Serre.restrictFibre q S)))
      (Work.Serre.DiscPair.cylPreBot q S) eCyl hbot ℚ (r + 1)
  let U₂ : Work.Thom.RelCoh ℚ (r + 1)
      (Work.Serre.cyl (Work.Serre.restrictFibre q S))
      (Set.range (Work.Serre.cylIncl (Work.Serre.restrictFibre q S))) :=
    (Work.Thom.relCohMap
      (eCyl : C(Work.Serre.cyl (Work.Serre.restrictFibre q S),
        ↥((Work.Serre.cylRetract q) ⁻¹' S)))
      (Set.range (Work.Serre.cylIncl (Work.Serre.restrictFibre q S)))
      (Work.Serre.DiscPair.cylPreBot q S) heC ℚ (r + 1)).hom US
  have hU₂ : U₂ ≠ 0 := by
    have hb : Function.Injective (Work.Thom.relCohMap
        (eCyl : C(Work.Serre.cyl (Work.Serre.restrictFibre q S),
          ↥((Work.Serre.cylRetract q) ⁻¹' S)))
        (Set.range (Work.Serre.cylIncl (Work.Serre.restrictFibre q S)))
        (Work.Serre.DiscPair.cylPreBot q S) heC ℚ (r + 1)).hom :=
      ((CategoryTheory.ConcreteCategory.isIso_iff_bijective _).mp hisoR).1
    exact fun h0 => hUS (hb (by simpa using h0))
  -- (3) transport along the homeomorphism `↥S ≃ₜ cellSphere n`
  let p : C(↥(q ⁻¹' S), cellSphere n) :=
    ((⟨e₀, e₀.continuous_toFun⟩ : C(↥S, cellSphere n)).comp
      (Work.Serre.restrictFibre q S))
  have he_q : ∀ x, e₀ (Work.Serre.restrictFibre q S x) = p x := fun x => rfl
  have hd : ∀ x, e₀.symm (p x) = Work.Serre.restrictFibre q S x :=
    fun x => e₀.symm_apply_apply _
  let H : Work.Serre.cyl (Work.Serre.restrictFibre q S) ≃ₜ Work.Serre.cyl p :=
    Work.Serre.cylHomeoOfHomeo (Work.Serre.restrictFibre q S) p e₀ he_q hd
  have hHI : ∀ y, H (Work.Serre.cylIncl (Work.Serre.restrictFibre q S) y)
      = Work.Serre.cylIncl p y := fun y =>
    Work.Serre.cylHomeoOfHomeo_apply_cylIncl (Work.Serre.restrictFibre q S) p e₀ he_q hd y
  have hHs : ∀ y, H.symm (Work.Serre.cylIncl p y)
      = Work.Serre.cylIncl (Work.Serre.restrictFibre q S) y := fun y =>
    Work.Serre.cylHomeoOfHomeo_symm_apply_cylIncl (Work.Serre.restrictFibre q S) p e₀ he_q hd y
  have heH : ∀ y : Work.Serre.cyl (Work.Serre.restrictFibre q S),
      y ∈ Set.range (Work.Serre.cylIncl (Work.Serre.restrictFibre q S)) ↔
        H y ∈ Set.range (Work.Serre.cylIncl p) := by
    intro y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, hHI x⟩
    · rintro ⟨x, hx⟩
      refine ⟨x, ?_⟩
      rw [← hHs x, hx, H.symm_apply_apply]
  have hfH : ∀ y ∈ Set.range (Work.Serre.cylIncl (Work.Serre.restrictFibre q S)),
      H y ∈ Set.range (Work.Serre.cylIncl p) := fun y hy => (heH y).mp hy
  haveI hisoH : CategoryTheory.IsIso (Work.Thom.relCohMap (H : C(_, _))
      (Set.range (Work.Serre.cylIncl (Work.Serre.restrictFibre q S)))
      (Set.range (Work.Serre.cylIncl p)) hfH ℚ (r + 1)) :=
    Work.Thom.CapGlue.isIso_relComplexMap_homeomorph
      (Set.range (Work.Serre.cylIncl (Work.Serre.restrictFibre q S)))
      (Set.range (Work.Serre.cylIncl p)) H heH ℚ (r + 1)
  let Up : Work.Thom.RelCoh ℚ (r + 1) (Work.Serre.cyl p)
      (Set.range (Work.Serre.cylIncl p)) :=
    (CategoryTheory.asIso (Work.Thom.relCohMap (H : C(_, _))
      (Set.range (Work.Serre.cylIncl (Work.Serre.restrictFibre q S)))
      (Set.range (Work.Serre.cylIncl p)) hfH ℚ (r + 1))).inv U₂
  have hUp : Up ≠ 0 := by
    intro h0
    refine hU₂ ?_
    have h1 : (CategoryTheory.asIso (Work.Thom.relCohMap (H : C(_, _))
        (Set.range (Work.Serre.cylIncl (Work.Serre.restrictFibre q S)))
        (Set.range (Work.Serre.cylIncl p)) hfH ℚ (r + 1))).hom Up = U₂ :=
      CategoryTheory.Iso.inv_hom_id_apply _ U₂
    rw [h0, map_zero] at h1
    exact h1.symm
  -- the fibre data of the transported fibration
  have hfib : ∀ z : cellSphere n, Work.StemsB.fibre p z ≃ₜ Work.StemsB.fibre q (e₀.symm z) :=
    fun z => (Work.Serre.CWThom.fibreHomeo_comp_homeo e₀ (Work.Serre.restrictFibre q S) z).trans
      (Work.Serre.CWThom.fibreHomeo_restrictFibre q S (e₀.symm z))
  have hserre : Work.StemsB.IsSerreFibration p :=
    Work.Serre.CWThom.isSerreFibration_comp_homeo e₀
      (Work.Serre.isSerreFibration_restrictFibre q hq S)
  have hpc' : ∀ z : cellSphere n, PathConnectedSpace (Work.StemsB.fibre p z) := fun z =>
    Work.Serre.CWThom.pathConnectedSpace_of_homeo (hfib z).symm (hpc (e₀.symm z))
  have hvan' : ∀ z : cellSphere n, ∀ t : ℕ, 0 < t → t ≠ r → t ≤ N →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre p z)) t) := by
    intro z t ht htr htN
    exact CategoryTheory.Limits.IsZero.of_iso (hvan (e₀.symm z) t ht htr htN)
      (Classical.choice (Work.StemsB.c2odd_ratH_iso_of_homeo (hfib z) t))
  have hgen' : ∀ z : cellSphere n, Nonempty (Work.Serre.ratH
      (TopCat.of (Work.StemsB.fibre p z)) r ≅ ModuleCat.of ℚ ℚ) := fun z =>
    ⟨(Classical.choice (Work.StemsB.c2odd_ratH_iso_of_homeo (hfib z) r)).trans
      (hgen (e₀.symm z)).some⟩
  have hmain : Work.Serre.ThomCylAt r N p :=
    sphereThom_of_nonzeroClass n r N hr hN p hserre hpc' hvan' hgen' Up hUp
  have hback : Work.Serre.ThomCylAt r N (Work.Serre.restrictFibre q S) :=
    Work.Serre.thomCylAt_of_homeo r N e₀ p (Work.Serre.restrictFibre q S)
      (fun x => (e₀.symm_apply_apply (Work.Serre.restrictFibre q S x)).symm) hmain
  rw [hS] at hback
  exact hback

/-! ## The shell step with a supplied class -/

/-- **The shell step of the cellular induction, with a supplied non-zero class.**  Over the shell
`{1/8 < ‖·‖ < 3/8}` of the `i`-th cell of `Γ' = attachCells (D-2) Γ ι f`, the Thom condition holds
as soon as a non-zero class over the ambient pair is given: the shell is a thickening of its middle
sphere `≅ cellSphere (D-2)` (`Work.Serre.compressRel_cellShellImg`), and the middle sphere carries
the class by `Work.RatHurewicz.quarterSphereThom_of_nonzeroClass`. -/
theorem cellShellThom_of_nonzeroClass (D : ℕ) (hD : 2 ≤ D) (r N : ℕ) (hr : 1 ≤ r) (hN : r ≤ N)
    {Γ : Type} [TopologicalSpace Γ] (hΓ : PathConnectedSpace Γ) (ι : Type)
    (f : ι → C(cellSphere (D - 2), Γ)) {X : Type} [TopologicalSpace X]
    (q : C(X, attachCells (D - 2) Γ ι f)) (i : ι)
    (hq : Work.StemsB.IsSerreFibration q)
    (hpc : ∀ γ : attachCells (D - 2) Γ ι f, PathConnectedSpace (Work.StemsB.fibre q γ))
    (hvan : ∀ γ : attachCells (D - 2) Γ ι f, ∀ t : ℕ, 0 < t → t ≠ r → t ≤ N →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q γ)) t))
    (hgen : ∀ γ : attachCells (D - 2) Γ ι f,
      Nonempty (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q γ)) r ≅ ModuleCat.of ℚ ℚ))
    (U : Work.Thom.RelCoh ℚ (r + 1) (Work.Serre.cyl q) (Set.range (Work.Serre.cylIncl q)))
    (hU : U ≠ 0) :
    Work.Serre.ThomCylAt r N (Work.Serre.restrictFibre q
      (Work.Serre.cellImg (f := f) i (Work.Serre.cellShellSet (D - 2) (1/8) (3/8)))) := by
  classical
  set S : Set (attachCells (D - 2) Γ ι f) :=
    Work.Serre.cellImg (f := f) i (Work.Serre.quarterSet (D - 2)) with hS
  set V : Set (attachCells (D - 2) Γ ι f) :=
    Work.Serre.cellImg (f := f) i (Work.Serre.cellShellSet (D - 2) (1 / 8) (3 / 8)) with hV
  have hSV : S ⊆ V := by
    rw [hS, hV]
    exact Set.image_mono (quarterSet_subset_cellShellSet (D - 2))
  have hScl : IsClosed S := by
    rw [hS]
    exact Work.Serre.DiscPair.isClosed_cellMap_sphere (D - 2) Γ ι f i (ρ := 1 / 4) (by norm_num)
  have hVop : IsOpen V := by
    rw [hV]
    exact Work.RatHurewicz.isOpen_cellMap_image
      (Work.Serre.isOpen_cellShellSet (D - 2) (1 / 8) (3 / 8))
      (Work.Serre.cellShellSet_subset_cellInner (by norm_num))
  have hcomp : ∀ d, CompressRel ↥V
      {x : ↥V | (x : attachCells (D - 2) Γ ι f) ∈ S} d := by
    intro d
    rw [hV, hS]
    exact Work.Serre.compressRel_cellShellImg (D - 2) Γ ι f (ρ := 1 / 8) (R := 3 / 8)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) i d
  have hseed : Work.Serre.ThomCylAt r N (Work.Serre.restrictFibre q S) := by
    rw [hS]
    exact quarterSphereThom_of_nonzeroClass (D - 2) hΓ ι f i q hq r N hr hN hpc hvan hgen U hU
  exact Work.RatHurewicz.thomCylAt_of_compress r N hr q hq S V hSV hScl hVop hcomp hseed

/-! ## The cellular step at every level, and the crux -/

/-- **The cellular step `CellStepAt D` for every `D ≥ 2`.**  The shell family is supplied by
`Work.RatHurewicz.cellShellThom_of_nonzeroClass` applied to the *extension class*
`Work.Serre.cellStepU`, which is non-zero (`Work.Serre.cellStepU_ne_zero`), and converted by
`Work.Serre.bijective_cup_shell_of_thomCylAt`; the remaining pieces are
`Work.Serre.thomCylCellStep_of_shellsBall` (which discharges the ball family and the degree-`0`
clause). -/
theorem cellStepAtShell (D : ℕ) (hD : 2 ≤ D) : CellStepAt D := by
  intro r N hr hN Γ _ hΓ ι f X _ q hq hvan hgen hpc IH
  have hU : Work.Serre.cellStepU r N D hr hN hD hΓ ι f q hq hvan hpc IH ≠ 0 :=
    Work.Serre.cellStepU_ne_zero r N D hr hN hD hΓ ι f q hq hvan hpc IH
  refine Work.Serre.thomCylCellStep_of_shellsBall r N D hr hN hD hΓ ι f q hq hvan hgen hpc IH
    (1/8) (3/8) (by norm_num) (by norm_num) (by norm_num) (fun i m hm => ?_)
  exact Work.Serre.bijective_cup_shell_of_thomCylAt r N D hr hN hD hΓ ι f q hq hvan hgen hpc IH
    (ρ := 1/8) (R := 3/8) (by norm_num) (by norm_num) (by norm_num) i
    (cellShellThom_of_nonzeroClass D hD r N hr hN hΓ ι f q i hq hpc hvan hgen
      (Work.Serre.cellStepU r N D hr hN hD hΓ ι f q hq hvan hpc IH) hU) m hm

/-- **The cellular step of the CW-model Thom case** (`Work.Serre.ThomCylCellStepAlt`), the single
open node of the E3(b) tower, proved from `CellStepAt D` for every `D ≥ 2` (with the vacuous case
`N < r` handled directly). -/
theorem thomCylCellStepAlt_free : Work.Serre.ThomCylCellStepAlt := by
  intro r N hr D hD Γ _ hΓ ι f X _ q hq hvan hgen hpc IH
  rcases lt_or_ge N r with h | h
  · exact ⟨0, fun m hm => by exfalso; omega⟩
  · exact cellStepAtShell D hD r N hr h hΓ ι f q hq hvan hgen hpc IH

end

end Work.RatHurewicz
