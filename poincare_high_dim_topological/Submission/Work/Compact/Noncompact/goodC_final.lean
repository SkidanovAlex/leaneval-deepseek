import Mathlib
import Submission.Work.Compact.Noncompact.Good
import Submission.Work.Compact.Noncompact.Basic
import Submission.Work.Compact.Noncompact.goodV_union
import Submission.Work.Compact.Noncompact.goodC_closedBall
import Submission.Work.Compact.Noncompact.goodC_union
import Submission.Work.Compact.Noncompact.isZero_hatH_convex
import Submission.Work.Compact.Noncompact.forall_localMap_eq_zero_of_exists
import Submission.Work.Compact.Noncompact.exists_balls_rho
import Submission.Work.Compact.Noncompact.exists_hatClass
import Submission.Work.Compact.Noncompact.hatClass_natural

/-!
# Hatcher's Lemma 3.27 for an arbitrary compact subset of a manifold

For a Hausdorff `(k+1)`-manifold `M` and a compact set `A ⊆ M`,
`Work.Compact.Noncompact.GoodC k (TopCat.of M) A` states that the localization
`H_{k+1}(M, M∖A) → ∏_{x∈A} H_{k+1}(M, M∖{x})` is injective and that `H_j(M, M∖A) = 0` for
`j > k+1`.  This file proves it, following Hatcher's proof of Lemma 3.27.

The ingredients (all proved elsewhere in `Submission/Work/Compact/Noncompact/`):

* `goodC_closedBall`: the base case, a closed ball inside a chart (Hatcher's step (3));
* `goodC_union`, `goodV_union`: the Mayer–Vietoris step (Hatcher's step (1));
* `isZero_hatH_convex`: the vanishing for compact convex chart pieces, and the companion
  `gcf_goodV_iUnion_convex` for finite unions of such pieces;
* `exists_balls_rho`: the covering lemma of Hatcher's step (4);
* `exists_hatClass`, `hatClass_natural`: classes of relative cycles and their naturality.

The new content here is Hatcher's step (4) (`gcf_chart_data`, `gcf_vanish_inChart`,
`gcf_unique_inChart`): a compact set inside one chart is covered by finitely many closed balls
centred at points of the set and avoiding the support of `∂z`; the relative cycle `z` then
represents the given class on the (larger) union of balls, where `GoodC` is available, and the
injectivity of the localization at the centre of a ball (`localMap_injective_ball`) propagates the
triviality of the localizations back.  Hatcher's step (2) (`gcf_goodC_biUnion_chart`) then
assembles a finite union of compact chart pieces, and the final theorem covers an arbitrary
compact set by finitely many such pieces.
-/

namespace Work.Compact.Noncompact

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000

noncomputable section

/-! ## Elementary set-theoretic bookkeeping -/

lemma gcf_iUnion_mem_empty {ι M : Type*} (f : ι → Set M) :
    (⋃ i ∈ (∅ : Finset ι), f i) = (∅ : Set M) := by simp

lemma gcf_iUnion_insert_mem {ι M : Type*} [DecidableEq ι] (t : Finset ι) (j : ι)
    (f : ι → Set M) : (⋃ i ∈ insert j t, f i) = (⋃ i ∈ t, f i) ∪ f j := by
  ext x
  simp only [Set.mem_iUnion, Finset.mem_insert, Set.mem_union]
  constructor
  · rintro ⟨i, (rfl | hi), hx⟩
    · exact Or.inr hx
    · exact Or.inl ⟨i, hi, hx⟩
  · rintro (⟨i, hi, hx⟩ | hx)
    · exact ⟨i, Or.inr hi, hx⟩
    · exact ⟨j, Or.inl rfl, hx⟩

lemma gcf_iUnion_univ_mem {ι M : Type*} [Fintype ι] (f : ι → Set M) :
    (⋃ i ∈ (Finset.univ : Finset ι), f i) = ⋃ i, f i := by
  ext x
  simp only [Set.mem_iUnion, Finset.mem_univ]
  constructor
  · rintro ⟨i, _, hx⟩; exact ⟨i, hx⟩
  · rintro ⟨i, hx⟩; exact ⟨i, trivial, hx⟩

lemma gcf_mem_iUnion_finset {ι M : Type*} (s : Finset ι) (f : ι → Set M) (x : M) :
    x ∈ (⋃ i ∈ s, f i) ↔ ∃ i ∈ s, x ∈ f i := by
  simp only [Set.mem_iUnion, exists_prop]

lemma gcf_inter_iUnion_mem {ι M : Type*} (t : Finset ι) (f : ι → Set M) (g : Set M) :
    (⋃ i ∈ t, f i) ∩ g = ⋃ i ∈ t, (f i ∩ g) := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_iUnion, exists_prop]
  tauto

lemma gcf_piece_inter {M E : Type*} [TopologicalSpace M] [TopologicalSpace E]
    (e : OpenPartialHomeomorph M E)
    (C D : Set E) :
    (e.source ∩ e ⁻¹' C) ∩ (e.source ∩ e ⁻¹' D) = e.source ∩ e ⁻¹' (C ∩ D) := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_preimage]
  tauto

lemma gcf_inter_iUnion_piece {ι M E : Type*} [TopologicalSpace M] [TopologicalSpace E]
    (e : OpenPartialHomeomorph M E) (t : Finset ι) (C : ι → Set E) (j : ι) :
    (⋃ i ∈ t, (e.source ∩ e ⁻¹' C i)) ∩ (e.source ∩ e ⁻¹' C j)
      = ⋃ i ∈ t, (e.source ∩ e ⁻¹' (C i ∩ C j)) := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_iUnion, exists_prop]
  constructor
  · rintro ⟨⟨i, hi, hx1, hx2⟩, hx3, hx4⟩
    exact ⟨i, hi, hx1, hx2, hx4⟩
  · rintro ⟨i, hi, hx1, hx2, hx3⟩
    exact ⟨⟨i, hi, hx1, hx2⟩, hx1, hx3⟩

/-! ## The empty set -/

lemma gcf_isZero_hatH_empty (X : TopCat) (j : ℕ) : IsZero (hatH X (∅ : Set X) j) := by
  change IsZero ((RC X ((∅ : Set X)ᶜ)).homology j)
  rw [Set.compl_empty, RC_eq_relChains]
  exact isZero_relChains_univ_homology X j

lemma gcf_goodV_empty (k : ℕ) (X : TopCat) : GoodV k X (∅ : Set X) :=
  ⟨isCompact_empty, fun j _ => gcf_isZero_hatH_empty X j⟩

lemma gcf_goodC_empty (k : ℕ) (X : TopCat) : GoodC k X (∅ : Set X) := by
  refine ⟨isCompact_empty, ?_, fun j _ => gcf_isZero_hatH_empty X j⟩
  intro u _
  haveI : Subsingleton (hatH X (∅ : Set X) (k + 1)) :=
    ModuleCat.isZero_iff_subsingleton.1 (gcf_isZero_hatH_empty X (k + 1))
  exact Subsingleton.elim u 0

lemma gcf_goodV_of_goodC {k : ℕ} {X : TopCat} {A : Set X} (h : GoodC k X A) : GoodV k X A :=
  ⟨h.1, h.2.2⟩

/-! ## Convex pieces in a chart -/

theorem gcf_goodV_convex {k : ℕ} {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (k + 1))) M]
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (k + 1))))
    {C : Set (EuclideanSpace ℝ (Fin (k + 1)))} (hCvx : Convex ℝ C) (hCcpt : IsCompact C)
    (hCsub : C ⊆ e.target) : GoodV k (TopCat.of M) (e.source ∩ e ⁻¹' C) :=
  ⟨isCompact_inter_preimage e hCcpt hCsub,
   fun j hj => isZero_hatH_convex (n := k + 1) (by omega) e hCvx hCcpt hCsub hj⟩

/-- `GoodV` of a finite union of compact convex pieces of a single chart. -/
theorem gcf_goodV_iUnion_convex {k : ℕ} {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (k + 1))) M]
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (k + 1))))
    {ι : Type*} (s : Finset ι) :
    ∀ (C : ι → Set (EuclideanSpace ℝ (Fin (k + 1)))),
      (∀ i, Convex ℝ (C i)) → (∀ i, IsCompact (C i)) → (∀ i, C i ⊆ e.target) →
      GoodV k (TopCat.of M) (⋃ i ∈ s, (e.source ∩ e ⁻¹' C i)) := by
  classical
  induction s using Finset.induction with
  | empty =>
      intro C _ _ _
      rw [gcf_iUnion_mem_empty]
      exact gcf_goodV_empty k (TopCat.of M)
  | insert j t hjt ih =>
      intro C h1 h2 h3
      rw [gcf_iUnion_insert_mem]
      refine goodV_union _ _ (ih C h1 h2 h3) (gcf_goodV_convex e (h1 j) (h2 j) (h3 j)) ?_
      rw [gcf_inter_iUnion_piece]
      exact ih (fun i => C i ∩ C j) (fun i => (h1 i).inter (h1 j)) (fun i => (h2 i).inter (h2 j))
        (fun i => Set.Subset.trans Set.inter_subset_left (h3 i))

/-- `GoodC` of a finite union of closed balls (with centres) of a single chart. -/
theorem gcf_goodC_iUnion_closedBall {k : ℕ} {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (k + 1))) M]
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (k + 1))))
    {ι : Type*} (s : Finset ι) (a : ι → M) (ρ : ι → ℝ)
    (ha : ∀ i, a i ∈ e.source) (hρ : ∀ i, 0 < ρ i)
    (hsub : ∀ i, Metric.ball (e (a i)) (ρ i) ⊆ e.target) :
    GoodC k (TopCat.of M)
      (⋃ i ∈ s, (e.source ∩ e ⁻¹' Metric.closedBall (e (a i)) (ρ i / 2))) := by
  classical
  induction s using Finset.induction with
  | empty =>
      rw [gcf_iUnion_mem_empty]
      exact gcf_goodC_empty k (TopCat.of M)
  | insert j t hjt ih =>
      rw [gcf_iUnion_insert_mem]
      refine goodC_union _ _ ih (goodC_closedBall e (hρ j) (hsub j)) ?_
      rw [gcf_inter_iUnion_piece]
      refine gcf_goodV_iUnion_convex e t
        (fun i => Metric.closedBall (e (a i)) (ρ i / 2) ∩ Metric.closedBall (e (a j)) (ρ j / 2))
        (fun i => (convex_closedBall _ _).inter (convex_closedBall _ _))
        (fun i => (isCompact_closedBall _ _).inter (isCompact_closedBall _ _)) ?_
      intro i
      exact Set.Subset.trans Set.inter_subset_left
        (Set.Subset.trans (Metric.closedBall_subset_ball (by linarith [hρ i])) (hsub i))

/-! ## Two elementary identities for `hatRes` -/

lemma gcf_hatRes_congr {X : TopCat} {A B : Set X} (h₁ h₂ : A ⊆ B) (k : ℕ) :
    hatRes (X := X) h₁ k = hatRes (X := X) h₂ k := by
  show relMapHom (X := X) (Set.compl_subset_compl.mpr h₁) k
      = relMapHom (X := X) (Set.compl_subset_compl.mpr h₂) k
  exact relMapHom_eq_of_subset_eq _ _ k

lemma gcf_hatRes_hatRes {X : TopCat} {S T U : Set X} (h₁ : S ⊆ T) (h₂ : T ⊆ U) (k : ℕ)
    (w : hatH X U k) :
    hatRes (X := X) h₁ k (hatRes (X := X) h₂ k w) = hatRes (X := X) (h₁.trans h₂) k w := by
  have h := congrArg (fun (f : hatH X U k ⟶ hatH X S k) => f.hom w)
    (hatRes_comp (X := X) h₁ h₂ k)
  simpa only [ModuleCat.comp_apply] using h

lemma gcf_relMapHom_relMapHom {X : TopCat} {S T U : Set X} (h₁ : S ⊆ T) (h₂ : T ⊆ U)
    (n : ℕ) (w : (RC X S).homology n) :
    relMapHom (X := X) h₂ n (relMapHom (X := X) h₁ n w)
      = relMapHom (X := X) (h₁.trans h₂) n w := by
  have h := congrArg (fun (f : (RC X S).homology n ⟶ (RC X U).homology n) => f.hom w)
    (relMapHom_comp h₁ h₂ n)
  simpa only [ModuleCat.comp_apply] using h

/-! ## Hatcher's step (4): a compact set inside a single chart -/

/-- The covering data of Hatcher's step (4): a compact set `A` inside a chart, together with a
finitely indexed family of closed balls centred at points of `A` which still avoid the support of
`∂z`, and which is a `GoodC` set by `gcf_goodC_iUnion_closedBall`. -/
theorem gcf_chart_data {k : ℕ} {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (k + 1))) M]
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (k + 1))))
    {A : Set M} (hA : IsCompact A) (hAe : A ⊆ e.source) (j' : ℕ)
    (z : Ch (TopCat.of M) (j' + 1))
    (hz : bdry (TopCat.of M) j' z ∈ suppS (TopCat.of M) (Aᶜ) j') :
    ∃ (m : ℕ) (a : Fin m → M) (ρ : Fin m → ℝ) (K : Set M),
      (∀ i, a i ∈ A) ∧ (∀ i, 0 < ρ i) ∧
      (∀ i, Metric.ball (e (a i)) (ρ i) ⊆ e.target) ∧
      K = ⋃ i, (e.source ∩ e⁻¹' Metric.closedBall (e (a i)) (ρ i / 2)) ∧
      A ⊆ K ∧ bdry (TopCat.of M) j' z ∈ suppS (TopCat.of M) (Kᶜ) j' ∧
      GoodC k (TopCat.of M) K := by
  classical
  obtain ⟨m, a, ρ, ha, hρ, htarget, hcover, hsupp⟩ :=
    exists_balls_rho (n := k + 1) e hA hAe j' (bdry (TopCat.of M) j' z) hz
  refine ⟨m, a, ρ, ⋃ i, (e.source ∩ e⁻¹' Metric.closedBall (e (a i)) (ρ i / 2)),
    ha, hρ, htarget, rfl, ?_, hsupp, ?_⟩
  · intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover hx)
    exact Set.mem_iUnion.mpr ⟨i, ⟨hi.1, Metric.ball_subset_closedBall hi.2⟩⟩
  · have h := gcf_goodC_iUnion_closedBall (k := k) e (s := Finset.univ) a ρ
      (fun i => hAe (ha i)) hρ htarget
    rwa [gcf_iUnion_univ_mem] at h

/-- Hatcher's step (4), vanishing half: for `A ⊆ e.source` compact and `k + 1 < j` a class in
`H_j(M, M∖A)` vanishes. -/
theorem gcf_vanish_inChart {k : ℕ} {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (k + 1))) M]
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (k + 1))))
    {A : Set M} (hA : IsCompact A) (hAe : A ⊆ e.source) {j : ℕ} (hj : k + 1 < j)
    (u : hatH (TopCat.of M) A j) : u = 0 := by
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  obtain ⟨z, hz, hzu⟩ := exists_hatClass (TopCat.of M) (Aᶜ) j' u
  obtain ⟨m, a, ρ, K, ha, hρ, htarget, hKdef, hAK, hsupp, hKgood⟩ :=
    gcf_chart_data (k := k) e hA hAe j' z hz
  have hnat := (hatClass_natural (X := TopCat.of M) (S := Kᶜ) (T := Aᶜ)
      (Set.compl_subset_compl.mpr hAK) j' z hsupp hz).trans hzu
  have hb : hatClass (X := TopCat.of M) (Kᶜ) j' z hsupp = 0 :=
    (ModuleCat.isZero_iff_subsingleton.1 (hKgood.2.2 (j' + 1) hj)).allEq _ _
  rw [← hnat, hb, map_zero]

/-- Hatcher's step (4), uniqueness half: for `A ⊆ e.source` compact, a class in
`H_{k+1}(M, M∖A)` whose localizations at all points of `A` vanish is zero. -/
theorem gcf_unique_inChart {k : ℕ} {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (k + 1))) M]
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (k + 1))))
    {A : Set M} (hA : IsCompact A) (hAe : A ⊆ e.source)
    (u : hatH (TopCat.of M) A (k + 1))
    (hu : ∀ (x : M) (hx : x ∈ A),
      hatRes (X := TopCat.of M) (B := A) (Set.singleton_subset_iff.mpr hx) (k + 1) u = 0) :
    u = 0 := by
  classical
  obtain ⟨z, hz, hzu⟩ := exists_hatClass (TopCat.of M) (Aᶜ) k u
  obtain ⟨m, a, ρ, K, ha, hρ, htarget, hKdef, hAK, hsupp, hKgood⟩ :=
    gcf_chart_data (k := k) e hA hAe k z hz
  have hnat := (hatClass_natural (X := TopCat.of M) (S := Kᶜ) (T := Aᶜ)
      (Set.compl_subset_compl.mpr hAK) k z hsupp hz).trans hzu
  have hloc : ∀ y (hy : y ∈ K),
      relMapHom (X := TopCat.of M) (A := Kᶜ) (B := ({y}ᶜ : Set M))
        (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hy)) (k + 1)
        (hatClass (X := TopCat.of M) (Kᶜ) k z hsupp) = 0 := by
    intro y hy
    have hyU : y ∈ ⋃ i, (e.source ∩ e⁻¹' Metric.closedBall (e (a i)) (ρ i / 2)) := by
      rw [← hKdef]
      exact hy
    obtain ⟨i, hyi⟩ := Set.mem_iUnion.mp hyU
    have haiP : a i ∈ e.source ∩ e⁻¹' Metric.closedBall (e (a i)) (ρ i / 2) :=
      ⟨hAe (ha i), by
        rw [Set.mem_preimage]
        exact Metric.mem_closedBall_self (by linarith [hρ i])⟩
    have haiK : a i ∈ K := by
      rw [hKdef]
      exact Set.mem_iUnion.mpr ⟨i, haiP⟩
    have hPK : (e.source ∩ e⁻¹' Metric.closedBall (e (a i)) (ρ i / 2)) ⊆ K := by
      rw [hKdef]
      exact fun x hx => Set.mem_iUnion.mpr ⟨i, hx⟩
    have hPa : ((e.source ∩ e⁻¹' Metric.closedBall (e (a i)) (ρ i / 2)))ᶜ ⊆ ({a i}ᶜ : Set M) :=
      fun x hx hxa => hx (hxa ▸ haiP)
    have hyP : ((e.source ∩ e⁻¹' Metric.closedBall (e (a i)) (ρ i / 2)))ᶜ ⊆ ({y}ᶜ : Set M) :=
      fun x hx hxy => hx (hxy ▸ hyi)
    have hinj : Function.Injective (relMapHom (X := TopCat.of M)
        (A := ((e.source ∩ e⁻¹' Metric.closedBall (e (a i)) (ρ i / 2)))ᶜ)
        (B := ({a i}ᶜ : Set M)) hPa (k + 1)) :=
      localMap_injective_ball e (hρ i) (htarget i) (hAe (ha i))
        (by rw [dist_self]; linarith [hρ i]) hPa
    have hlocA : relMapHom (X := TopCat.of M) (A := Kᶜ) (B := ({a i}ᶜ : Set M))
        (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr haiK)) (k + 1)
        (hatClass (X := TopCat.of M) (Kᶜ) k z hsupp) = 0 := by
      rw [relMapHom_eq_of_subset_eq
          (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr haiK))
          ((Set.compl_subset_compl.mpr hAK).trans
            (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr (ha i)))) (k + 1),
        ← gcf_relMapHom_relMapHom (Set.compl_subset_compl.mpr hAK)
          (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr (ha i))) (k + 1)
          (hatClass (X := TopCat.of M) (Kᶜ) k z hsupp)]
      rw [hnat]
      exact hu (a i) (ha i)
    have hmid : relMapHom (X := TopCat.of M) (A := Kᶜ)
        (B := ((e.source ∩ e⁻¹' Metric.closedBall (e (a i)) (ρ i / 2)))ᶜ)
        (Set.compl_subset_compl.mpr hPK) (k + 1)
        (hatClass (X := TopCat.of M) (Kᶜ) k z hsupp) = 0 := by
      apply hinj
      rw [gcf_relMapHom_relMapHom (Set.compl_subset_compl.mpr hPK) hPa (k + 1)
        (hatClass (X := TopCat.of M) (Kᶜ) k z hsupp)]
      rw [relMapHom_eq_of_subset_eq ((Set.compl_subset_compl.mpr hPK).trans hPa)
        (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr haiK)) (k + 1), map_zero]
      exact hlocA
    rw [relMapHom_eq_of_subset_eq (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hy))
        ((Set.compl_subset_compl.mpr hPK).trans hyP) (k + 1),
      ← gcf_relMapHom_relMapHom (Set.compl_subset_compl.mpr hPK) hyP (k + 1)
        (hatClass (X := TopCat.of M) (Kᶜ) k z hsupp)]
    rw [show relMapHom (X := TopCat.of M) (A := Kᶜ)
        (B := ((e.source ∩ e⁻¹' Metric.closedBall (e (a i)) (ρ i / 2)))ᶜ)
        (Set.compl_subset_compl.mpr hPK) (k + 1)
        (hatClass (X := TopCat.of M) (Kᶜ) k z hsupp) = 0 from hmid, map_zero]
  have hβ0 : hatClass (X := TopCat.of M) (Kᶜ) k z hsupp = 0 :=
    hKgood.2.1 _ (fun y hy => hloc y hy)
  rw [← hnat, hβ0, map_zero]

/-- Hatcher's Lemma 3.27 for a compact subset of one chart. -/
theorem gcf_goodC_inChart {k : ℕ} {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (k + 1))) M]
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (k + 1))))
    (A : Set M) (hA : IsCompact A) (hAe : A ⊆ e.source) :
    GoodC k (TopCat.of M) A := by
  refine ⟨hA, ?_, ?_⟩
  · intro u hu
    exact gcf_unique_inChart (k := k) e hA hAe u hu
  · intro j hj
    rw [ModuleCat.isZero_iff_subsingleton]
    exact ⟨fun u v => (gcf_vanish_inChart (k := k) e hA hAe hj u).trans
      (gcf_vanish_inChart (k := k) e hA hAe hj v).symm⟩

/-! ## Hatcher's step (2): finite unions of compact chart pieces -/

theorem gcf_goodC_biUnion_chart {k : ℕ} {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (k + 1))) M]
    {ι : Type*} (s : Finset ι) :
    ∀ (A : ι → Set M), (∀ i ∈ s, IsCompact (A i)) →
      (∀ i ∈ s, ∃ e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (k + 1))),
        A i ⊆ e.source) →
      GoodC k (TopCat.of M) (⋃ i ∈ s, A i) := by
  classical
  induction s using Finset.induction with
  | empty =>
      intro A _ _
      rw [gcf_iUnion_mem_empty]
      exact gcf_goodC_empty k (TopCat.of M)
  | insert j t hjt ih =>
      intro A hcpt hchart
      rw [gcf_iUnion_insert_mem]
      have hAt : GoodC k (TopCat.of M) (⋃ i ∈ t, A i) :=
        ih A (fun i hi => hcpt i (Finset.mem_insert_of_mem hi))
          (fun i hi => hchart i (Finset.mem_insert_of_mem hi))
      have hAj : GoodC k (TopCat.of M) (A j) := by
        obtain ⟨e, he⟩ := hchart j (Finset.mem_insert_self j t)
        exact gcf_goodC_inChart e (A j) (hcpt j (Finset.mem_insert_self j t)) he
      have hI : GoodV k (TopCat.of M) ((⋃ i ∈ t, A i) ∩ A j) := by
        obtain ⟨e, he⟩ := hchart j (Finset.mem_insert_self j t)
        refine gcf_goodV_of_goodC (gcf_goodC_inChart e ((⋃ i ∈ t, A i) ∩ A j)
          (hAt.1.inter (hcpt j (Finset.mem_insert_self j t))) ?_)
        intro x hx
        exact he hx.2
      exact goodC_union _ _ hAt hAj hI

/-! ## Assembly: an arbitrary compact set -/

/-- **Hatcher's Lemma 3.27 (a)+(b) for an arbitrary compact set** (the crux of Proposition 3.29,
`i = n` case).  For a Hausdorff `(k+1)`-manifold `M` and compact `A ⊆ M`, the localization
`H_{k+1}(M, M∖A) → ∏_{x∈A} H_{k+1}(M, M∖{x})` is injective and `H_j(M, M∖A) = 0` for `j > k+1`;
this is `Work.Compact.Noncompact.GoodC k (TopCat.of M) A`.

Route (Hatcher's proof, four steps; nearly all infrastructure is already in
`Submission/Work/Compact/Noncompact/`):

1. *Union step for the vanishing part*: `GoodV k A → GoodV k B → GoodV k (A∩B) → GoodV k (A∪B)`
   (the statement in `Submission/Work/Compact/Noncompact/goodV_union.lean`), from the relative
   Mayer–Vietoris LES: `hatH X (A∩B) (j+1) → hatH X (A∪B) j → hatH X A j ⊕ hatH X B j` is exact and
   both outer terms vanish for `j > k+1`.
2. *Union step for the full statement*: `GoodC k A → GoodC k B → GoodV k (A∩B) → GoodC k (A∪B)`
   (the statement in `Submission/Work/Compact/Noncompact/goodC_union.lean`).  The components of the
   diagonal `hatH X (A∪B) (k+1) → hatH X A (k+1) ⊕ hatH X B (k+1)` are `hatRes (A ⊆ A∪B)` and
   `hatRes (B ⊆ A∪B)`; the diagonal is injective by
   `Work.Compact.Noncompact.relChains_diagonal_injective` applied to the open sets `Aᶜ, Bᶜ`, whose
   hypothesis `IsZero (hatH X (A∩B) (k+2))` is the vanishing clause of `GoodV k (A∩B)`.
3. *Base case, a closed ball in a chart*: `GoodC k (e.source ∩ e⁻¹' Metric.closedBall c (ρ/2))` for
   `Metric.ball c ρ ⊆ e.target`, from `Work.Compact.Noncompact.localMap_injective_ball` (applied at
   the centre, using `Work.Compact.Noncompact.relMapHom_eq_of_subset_eq`) and
   `Work.Compact.Noncompact.isZero_hatH_convex`.  (This is the statement in
   `Submission/Work/Compact/Noncompact/goodC_ball.lean`.)
4. *Inside one chart* (Hatcher's step (4)): for compact `A ⊆ e.source`, `GoodC k A`.  Take a
   relative cycle `z` for `A` (use the surjectivity of `Work.Compact.Noncompact.hatClass`, see
   `exists_hatClass.lean`); cover `A` inside the chart by finitely many closed balls `K_i` avoiding
   the support of `∂z` using `Work.Compact.Noncompact.exists_suppS_compl_iUnion_balls` (with the
   chain `∂z ∈ suppS X Aᶜ k` written in expanded form via
   `Work.Compact.Noncompact.mem_suppS_iff_of_expansion`); let `K = ⋃ K_i ⊇ A`, so `z` is also a
   relative cycle for `K` and its class in `hatH X K (k+1)` maps to `hatClass A k z hz` under
   `hatRes (A ⊆ K)` (`Work.Compact.Noncompact.hatClass_natural`).  `GoodC k K` follows from step 3
   and step 2 by induction on the number of balls.  The `K_i` are balls meeting `A`, and the
   localization maps at points of such a ball vanish because they do on `A`
   (`Work.Compact.Noncompact.localMap_injective_ball` gives injectivity of the relative
   `H(M, M∖K_i) → H(M, M∖{x})` for suitable `x` in the ball); hence the class in `hatH X K (k+1)`
   has all localizations zero, so it is zero by `GoodC k K`, and `hatClass A k z hz = 0`.  The
   vanishing clause for `A` is the same argument in degree `j > k+1` (lift the class to `K` and use
   `GoodV k K`).
5. *Assembly*: write a compact `A` as a finite union of compact pieces `A_1, …, A_m` each contained
   in the source of a chart (`e.source` is open, `M` is locally compact, `A` is compact; for each
   point of `A` choose a chart with a compact neighbourhood inside its source), then induct on `m`
   using steps 1 and 2: the set `A_m ∩ (A_1 ∪ … ∪ A_{m-1})` is a finite union of compact sets inside
   charts, so it satisfies `GoodC` by the induction hypothesis.

Note: the statements of steps 1, 2, 3, 4 exist on disk at the paths quoted above (each with a
`sorry`) and are being proved in parallel; import and reuse them if they are sorry-free, otherwise
prove what you need yourself.  The target statement of *this* module must be proved without
`sorry`. -/
theorem goodC_final {k : ℕ} {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (k + 1))) M] (A : Set M) (hA : IsCompact A) :
    Work.Compact.Noncompact.GoodC k (TopCat.of M) A := by
  classical
  have hkey : ∀ x : A, ∃ (N : Set M)
      (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (k + 1)))),
      IsCompact N ∧ x.1 ∈ interior N ∧ N ⊆ e.source := by
    intro x
    set ee : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (k + 1))) :=
      chartAt (EuclideanSpace ℝ (Fin (k + 1))) x.1 with hee
    have hxsrc : x.1 ∈ ee.source := mem_chart_source _ _
    obtain ⟨δ, hδpos, hδ⟩ := exists_closedBall_subset_target ee hxsrc
    refine ⟨ee.source ∩ ee ⁻¹' Metric.closedBall (ee x.1) δ, ee, ?_, ?_,
      Set.inter_subset_left⟩
    · exact isCompact_inter_preimage ee (isCompact_closedBall _ _) hδ
    · have hsub2 : ee.source ∩ ee ⁻¹' Metric.ball (ee x.1) δ ⊆
          ee.source ∩ ee ⁻¹' Metric.closedBall (ee x.1) δ :=
        Set.inter_subset_inter_right _ (Set.preimage_mono Metric.ball_subset_closedBall)
      have hmem : x.1 ∈ ee.source ∩ ee ⁻¹' Metric.ball (ee x.1) δ :=
        ⟨hxsrc, by rw [Set.mem_preimage]; exact Metric.mem_ball_self hδpos⟩
      exact interior_maximal hsub2 (ee.isOpen_inter_preimage Metric.isOpen_ball) hmem
  choose N e hNcpt hNint hNe using hkey
  obtain ⟨t, ht⟩ := hA.elim_finite_subcover (fun x : A => interior (N x))
      (fun _ => isOpen_interior) (fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hNint ⟨x, hx⟩⟩)
  have hcpts : ∀ i ∈ t, IsCompact (A ∩ N i) := fun i _ => hA.inter (hNcpt i)
  have hchars : ∀ i ∈ t, ∃ e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (k + 1))),
      (A ∩ N i) ⊆ e.source := fun i _ => ⟨e i, Set.Subset.trans Set.inter_subset_right (hNe i)⟩
  have hgood := gcf_goodC_biUnion_chart (k := k) t (fun i : A => A ∩ N i) hcpts hchars
  have hunion : (⋃ i ∈ t, (A ∩ N i)) = A := by
    apply Set.Subset.antisymm
    · exact Set.iUnion_subset (fun i => Set.iUnion_subset (fun _ => Set.inter_subset_left))
    · intro a ha
      obtain ⟨i, hi, hai⟩ :=
        (gcf_mem_iUnion_finset t (fun i : A => interior (N i)) a).mp (ht ha)
      exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨hi, ⟨ha, interior_subset hai⟩⟩⟩
  rwa [hunion] at hgood

end

end Work.Compact.Noncompact
