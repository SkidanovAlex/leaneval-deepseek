import Mathlib
import Submission.Work.RatHurewicz.SphereThomDefs
import Submission.Work.RatHurewicz.SphereCover
import Submission.Work.RatHurewicz.cupBijectiveOverPiece
import Submission.Work.Serre.bijective_mixedCup_of_openCover
import Submission.Work.Serre.DiscPair.existsNonzeroRelCohTower
import Submission.Work.Serre.attachCellsPUnitSphere
import Submission.Work.Serre.bijective_mixedCup_of_openCover_zero
import Submission.Work.Serre.relCoh_cylPre_concentrated
import Submission.Work.RatHurewicz.cvGoodIUnion

set_option synthInstance.maxHeartbeats 400000

/-!
# Assembly of the sphere case of the CW-model Thom theorem

This module reduces `Work.Serre.SphereThom k r N` (for `1 ≤ k`, `1 ≤ r`) to

* the existence of a non-zero relative class `U₀ ∈ H^{r+1}(cyl p, A)` over the sphere
  (`Work.RatHurewicz.hasNonzeroRelCoh_cellSphere`),
* the three local properties of the pieces of the orthant cover
  (`Work.RatHurewicz.cvGood_piece`, from `cupBijective_cylPre` and `relCoh_cylPre_concentrated`),
* the local-to-global gluing `Work.RatHurewicz.cvGoodIUnion`.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.RatHurewicz

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-- The intersection of the covering pieces is open. -/
theorem isOpen_cvInter (k : ℕ) (T : Finset (Fin (k + 2) ⊕ Unit)) :
    IsOpen (⋂ i ∈ T, cvPiece k i) := by
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T ha ih =>
      rw [Finset.set_biInter_insert]
      exact (isOpen_cvPiece k a).inter ih

/-- **The local conditions over an empty piece are trivial.** -/
theorem cupBij_empty {X : Type} [TopologicalSpace X] (A : Set X) (n₀ m : ℕ)
    (U₀ : Work.Thom.RelCoh ℚ n₀ X A) : CupBij A n₀ U₀ (∅ : Set X) m := by
  haveI : IsEmpty ↥(∅ : Set X) := ⟨fun x => x.2⟩
  haveI h1 : Subsingleton ↥(Work.Thom.Coh ℚ m ↥(∅ : Set X)) :=
    ModuleCat.isZero_iff_subsingleton.mp (Work.Serre.isZero_coh_of_isEmpty_space m)
  haveI h2 : Subsingleton ↥(Work.Thom.RelCoh ℚ (m + n₀) ↥(∅ : Set X)
      {y : ↥(∅ : Set X) | (y : X) ∈ A}) :=
    ModuleCat.isZero_iff_subsingleton.mp (Work.Serre.isZero_relCoh_of_isEmpty_space _ _)
  exact ⟨fun a b _ => Subsingleton.elim a b, fun b => ⟨0, Subsingleton.elim _ b⟩⟩

/-- **The local conditions over the pieces of the orthant cover**, from
`Work.RatHurewicz.cupBijective_cylPre` (for the cup conditions) and
`Work.Serre.relCoh_cylPre_concentrated` (for the vanishing of the relative cohomology in
degrees `≤ r`). -/
theorem cvGood_piece (k r N : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) (hrN : r ≤ N)
    {X : Type} [TopologicalSpace X] (p : C(X, cellSphere k))
    (hp : Work.StemsB.IsSerreFibration p)
    (hpc : ∀ γ : cellSphere k, PathConnectedSpace (Work.StemsB.fibre p γ))
    (hvan : ∀ γ : cellSphere k, ∀ t : ℕ, 0 < t → t ≠ r → t ≤ N →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre p γ)) t))
    (hgen : ∀ γ : cellSphere k,
      Nonempty (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre p γ)) r ≅ ModuleCat.of ℚ ℚ))
    (U₀ : Work.Thom.RelCoh ℚ (r + 1) (Work.Serre.cyl p) (Work.Serre.cylBot p))
    (hU₀ : U₀ ≠ 0)
    (T : Finset (Fin (k + 2) ⊕ Unit)) (hT : T.Nonempty) :
    CvGood (Work.Serre.cylBot p) (r + 1) (N + 1) U₀
      (Work.Serre.cylPre p (⋂ i ∈ T, cvPiece k i)) := by
  classical
  by_cases hne : (⋂ i ∈ T, cvPiece k i).Nonempty
  · -- the nonempty case
    haveI hcont : ContractibleSpace ↥(⋂ i ∈ T, cvPiece k i) :=
      contractibleSpace_cvInter k T hT hne
    haveI hVpc : PathConnectedSpace ↥(⋂ i ∈ T, cvPiece k i) := inferInstance
    obtain ⟨b₀, hb₀⟩ := hne
    let b : ↥(⋂ i ∈ T, cvPiece k i) := ⟨b₀, hb₀⟩
    haveI hVc : ∀ j : ℕ, Subsingleton (HomotopyGroup (Fin j) ↥(⋂ i ∈ T, cvPiece k i) b) :=
      fun j => Work.Stems.subsingleton_of_contractible b
    have hconc := Work.Serre.relCoh_cylPre_concentrated p hp r N hr hrN hpc hvan hgen
      (⋂ i ∈ T, cvPiece k i) (isOpen_cvInter k T) b hVc hVpc
    haveI hΓ : PathConnectedSpace (cellSphere k) := by
      have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin (k + 2))) := by
        rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
        exact_mod_cast (by omega : 1 < k + 2)
      exact (isPathConnected_iff_pathConnectedSpace).mp
        (isPathConnected_sphere hrank 0 (by norm_num : (0 : ℝ) ≤ 1))
    refine ⟨?_, ?_, ?_⟩
    · intro m hm hmK
      exact cupBijective_cylPre r N hr hΓ p hp hpc hvan hgen (⋂ i ∈ T, cvPiece k i)
        (isOpen_cvInter k T) b hVc hVpc U₀ hU₀ m hmK
    · exact cupBijective_cylPre r N hr hΓ p hp hpc hvan hgen (⋂ i ∈ T, cvPiece k i)
        (isOpen_cvInter k T) b hVc hVpc U₀ hU₀ 0 (by omega)
    · intro k' hk'
      exact ModuleCat.isZero_iff_subsingleton.mp (hconc.1 k' (by omega) (by omega))
  · -- the empty intersection
    rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne, show Work.Serre.cylPre p (∅ : Set (cellSphere k)) = ∅ from Set.preimage_empty]
    refine ⟨fun m hm hmK => cupBij_empty _ (r + 1) m U₀, cupBij_empty _ (r + 1) 0 U₀, ?_⟩
    intro k' hk'
    haveI : IsEmpty ↥(∅ : Set (Work.Serre.cyl p)) := ⟨fun x => x.2⟩
    exact ModuleCat.isZero_iff_subsingleton.mp (Work.Serre.isZero_relCoh_of_isEmpty_space _ _)

/-- **The sphere carries a non-zero relative class** for every Serre fibration with rationally
spherical fibres (transport along `attachCells (k-1) PUnit PUnit const ≃ₜ cellSphere k`). -/
theorem hasNonzeroRelCoh_cellSphere {k n : ℕ} (h : k = n + 1) :
    Work.Serre.DiscPair.HasNonzeroRelCoh (cellSphere k) := by
  subst h
  obtain ⟨φ⟩ := Work.Serre.attachCellsPUnitSphere n
  exact Work.Serre.DiscPair.hasNonzeroRelCoh_of_homeo φ
    (Work.Serre.DiscPair.hasNonzeroRelCoh_attachCells (n + 2) (by omega) PUnit
      (fun _ : PUnit => ContinuousMap.const (cellSphere n) PUnit.unit)
      Work.Serre.DiscPair.hasNonzeroRelCoh_punit)

/-- **The local condition over the whole space**: if the mixed cup product with `U₀` restricted to
the whole space is bijective (i.e. the local condition over `Set.univ`), then so is the ambient
cup map with `U₀`. -/
theorem cupBij_univ {X : Type} [TopologicalSpace X] (A : Set X) (n₀ m : ℕ)
    (U₀ : Work.Thom.RelCoh ℚ n₀ X A) (h : CupBij A n₀ U₀ Set.univ m) :
    Function.Bijective (fun x : Work.Thom.Coh ℚ m X =>
      (Work.Thom.mixedCupC ℚ A m n₀) x U₀) := by
  have h' := bijective_mixedCup_of_homeo (Homeomorph.Set.univ X).symm A
    {y : ↥(Set.univ : Set X) | (y : X) ∈ A} (fun x => Iff.rfl) m n₀
    ((Work.Thom.relCohMap (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(Set.univ : Set X), X))
      {y : ↥(Set.univ : Set X) | (y : X) ∈ A} A (fun _ hy => hy) ℚ n₀).hom U₀) h
  have hclass : (Work.Thom.relCohMap
        ((Homeomorph.Set.univ X).symm : C(X, ↥(Set.univ : Set X))) A
        {y : ↥(Set.univ : Set X) | (y : X) ∈ A} (fun x hx => by simpa using hx) ℚ n₀).hom
      ((Work.Thom.relCohMap (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(Set.univ : Set X), X))
        {y : ↥(Set.univ : Set X) | (y : X) ∈ A} A (fun _ hy => hy) ℚ n₀).hom U₀) = U₀ := by
    rw [← ModuleCat.comp_apply]
    have hcomp : ((⟨Subtype.val, continuous_subtype_val⟩ : C(↥(Set.univ : Set X), X)).comp
        ((Homeomorph.Set.univ X).symm : C(X, ↥(Set.univ : Set X)))) = ContinuousMap.id X := by
      ext x; rfl
    rw [Work.Thom.relCohMap_compA A {y : ↥(Set.univ : Set X) | (y : X) ∈ A} A
      ((Homeomorph.Set.univ X).symm : C(X, ↥(Set.univ : Set X)))
      (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(Set.univ : Set X), X))
      (fun x hx => by simpa using hx) (fun y hy => hy) (fun x hx => by simpa using hx) ℚ n₀]
    rw [Work.Thom.relCohMap_congrA A A hcomp (fun x hx => by simpa using hx)
      (fun x hx => hx) ℚ n₀]
    exact congrArg (fun (φ : Work.Thom.RelCoh ℚ n₀ X A ⟶ Work.Thom.RelCoh ℚ n₀ X A) => φ.hom U₀)
      (Work.Thom.relCohMap_idA A ℚ n₀)
  rw [hclass] at h'
  exact h'

/-- **The sphere case of the CW-model Thom theorem** (for `r ≤ N`), reduced to the local-to-global
gluing `Work.RatHurewicz.cvGoodIUnion` and the existence of a non-zero relative class
`Work.RatHurewicz.hasNonzeroRelCoh_cellSphere`. -/
theorem sphereThom_of_localGluing (k r N : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) (hrN : r ≤ N)
    {X : Type} [TopologicalSpace X] (p : C(X, cellSphere k))
    (hp : Work.StemsB.IsSerreFibration p)
    (hΓ : PathConnectedSpace (cellSphere k))
    (hpc : ∀ γ : cellSphere k, PathConnectedSpace (Work.StemsB.fibre p γ))
    (hvan : ∀ γ : cellSphere k, ∀ t : ℕ, 0 < t → t ≠ r → t ≤ N →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre p γ)) t))
    (hgen : ∀ γ : cellSphere k,
      Nonempty (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre p γ)) r ≅ ModuleCat.of ℚ ℚ)) :
    Work.Serre.ThomCylAt r N p := by
  obtain ⟨U₀, hU₀⟩ := hasNonzeroRelCoh_cellSphere (k := k) (n := k - 1) (by omega)
    p r N hr hrN hp hpc hvan hgen
  refine ⟨U₀, fun m hm => ?_⟩
  have hfib : ∀ γ : cellSphere k, Nonempty (Work.StemsB.fibre p γ) := fun γ => (hpc γ).nonempty
  have hglue := cvGoodIUnion p hfib (r + 1) (N + 1) (fun i => cvPiece k i)
    (fun i => isOpen_cvPiece k i)
    (fun T hT => cvGood_piece k r N hk hr hrN p hp hpc hvan hgen U₀ hU₀ T hT)
  have hunion : Work.Serre.cylPre p (⋃ i : Fin (k + 2) ⊕ Unit, cvPiece k i) = Set.univ := by
    rw [iUnion_cvPiece k hk]
    exact Set.preimage_univ
  have hcup : ∀ m' : ℕ, m' + (r + 1) ≤ N + 1 → Function.Bijective
      (fun x : Work.Thom.Coh ℚ m' (Work.Serre.cyl p) =>
        (Work.Thom.mixedCupC ℚ (Work.Serre.cylBot p) m' (r + 1)) x U₀) := by
    intro m' hm'
    rcases Nat.eq_zero_or_pos m' with h0 | hpos
    · subst h0
      refine cupBij_univ _ (r + 1) 0 U₀ ?_
      rw [← hunion]
      exact hglue.2.1
    · refine cupBij_univ _ (r + 1) m' U₀ ?_
      rw [← hunion]
      exact hglue.1 m' hpos hm'
  have hbij := hcup m (by omega)
  have hret : Function.Bijective
      (Work.Thom.CohMap (Work.Serre.cylRetract p) ℚ m).hom :=
    (CategoryTheory.ConcreteCategory.isIso_iff_bijective _).mp
      (Work.RatHurewicz.Dfr.isIso_CohMap_cylRetract p m)
  refine (CategoryTheory.ConcreteCategory.isIso_iff_bijective _).mpr ?_
  exact hbij.comp hret

end

end Work.RatHurewicz


