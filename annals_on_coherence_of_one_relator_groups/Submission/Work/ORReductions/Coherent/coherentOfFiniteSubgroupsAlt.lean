import Mathlib
import Submission.Work.ORReductions.Basic
import Submission.Work.ORReductions.SubgroupAlg
import Submission.Work.ORReductions.SubgroupAlg.subgroupAlgMap_mem_range_iff
import Submission.Work.ORReductions.Coherent.mem_span_of_subgroupAlgMap_mem_span
import Submission.Work.ORReductions.SubgroupAlg.ker_le_span_of_subgroup

/-!
# Coherence detected on finitely generated subgroups (assembly, own copy)

Same statement as `Work.ORReductions.Coherent.coherent_of_finite_subgroups`, assembled against the
locally requested leaves `mem_span_of_subgroupAlgMap_mem_span` and `ker_le_span_mapRange_alt`.
-/

namespace Work.ORReductions.Coherent

open Work.ORReductions

lemma linearCombination_mapRange_alt {A B : Type*} [Semiring A] [Semiring B] (φ : A →+* B)
    {ι : Type*} (y : ι → A) (c : ι →₀ A) :
    Finsupp.linearCombination B (fun i => φ (y i)) (Finsupp.mapRange (φ : A → B) (map_zero φ) c) =
      φ (Finsupp.linearCombination A y c) := by
  induction c using Finsupp.induction with
  | zero => simp
  | single_add a b c ha hb ih =>
    rw [Finsupp.mapRange_add (map_add φ), Finsupp.mapRange_single,
      map_add (Finsupp.linearCombination B (fun i => φ (y i))),
      map_add (Finsupp.linearCombination A y),
      Finsupp.linearCombination_single, Finsupp.linearCombination_single, ih,
      map_add φ, smul_eq_mul, smul_eq_mul, map_mul]

theorem coherent_of_finite_subgroups_alt (G : Type*) [Group G] (K : Type*) [Field K]
    (h : ∀ (s : Finset G), ∃ (H : Subgroup G), (s : Set G) ⊆ (H : Set G) ∧
      Ring.Coherent (MonoidAlgebra K H)) :
    Ring.Coherent (MonoidAlgebra K G) := by
  intro I hI
  classical
  obtain ⟨n, s, hs⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hI
  let sfin : Finset G := Finset.univ.biUnion (fun i : Fin n => (s i).coeff.support)
  obtain ⟨H, hHsub, hcoh⟩ := h sfin
  have hmem : ∀ i, s i ∈ Set.range (subgroupAlgMap H K) := by
    intro i
    rw [SubgroupAlg.subgroupAlgMap_mem_range_iff]
    exact Set.Subset.trans
      (Finset.coe_subset.mpr (Finset.subset_biUnion_of_mem (fun i : Fin n => (s i).coeff.support)
        (Finset.mem_univ i))) hHsub
  let y : Fin n → MonoidAlgebra K H := fun i => Classical.choose (hmem i)
  have hy : ∀ i, subgroupAlgMap H K (y i) = s i := fun i => Classical.choose_spec (hmem i)
  have hrange : (fun i : Fin n => subgroupAlgMap H K (y i)) = s := funext hy
  have hspanB : Submodule.span (MonoidAlgebra K G)
      (Set.range (fun i : Fin n => subgroupAlgMap H K (y i))) = I := by
    rw [hrange]; exact hs
  let J : Ideal (MonoidAlgebra K H) := Ideal.span (Set.range y)
  have hJI : J ≤ Ideal.comap (subgroupAlgMap H K) I := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    refine Ideal.mem_comap.mpr ?_
    rw [hy i, ← hs]
    exact Submodule.subset_span (Set.mem_range_self i)
  have hJeq : (J : Submodule (MonoidAlgebra K H) (MonoidAlgebra K H)) =
      Submodule.span (MonoidAlgebra K H) (Set.range y) := by
    refine le_antisymm ?_ ?_
    · intro x hx
      refine mem_span_of_subgroupAlgMap_mem_span H K y x ?_
      have h2 : subgroupAlgMap H K x ∈ I := Ideal.mem_comap.mp (hJI hx)
      rw [← hspanB] at h2
      exact h2
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact Ideal.subset_span ⟨i, rfl⟩
  have hJfg : J.FG := by
    rw [hJeq]
    exact Submodule.fg_span (Set.finite_range y)
  have hfpJ : Module.FinitePresentation (MonoidAlgebra K H) J := hcoh J hJfg
  let fA : (Fin n →₀ MonoidAlgebra K H) →ₗ[MonoidAlgebra K H] MonoidAlgebra K H :=
    Finsupp.linearCombination (MonoidAlgebra K H) y
  have hrangeA : fA.range = (J : Submodule (MonoidAlgebra K H) (MonoidAlgebra K H)) := by
    rw [Finsupp.range_linearCombination, ← hJeq]
  let lA : (Fin n →₀ MonoidAlgebra K H) →ₗ[MonoidAlgebra K H] J :=
    LinearMap.codRestrict J fA (fun c => by
      have : fA c ∈ fA.range := LinearMap.mem_range_self fA c
      rwa [hrangeA] at this)
  have hlA : Function.Surjective lA := by
    rw [← LinearMap.range_eq_top, LinearMap.range_codRestrict, hrangeA,
      Submodule.comap_subtype_self]
  have hkerA : (LinearMap.ker lA).FG := by
    haveI := hfpJ
    exact Module.FinitePresentation.fg_ker lA hlA
  obtain ⟨m, k, hk⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hkerA
  have hkerAeq : LinearMap.ker lA = LinearMap.ker fA :=
    LinearMap.ker_codRestrict J fA _
  have hk' : Submodule.span (MonoidAlgebra K H) (Set.range k) =
      LinearMap.ker (Finsupp.linearCombination (MonoidAlgebra K H) y) := by
    rw [hk, hkerAeq]
  have hC2 := Work.ORReductions.SubgroupAlg.ker_le_span_of_subgroup H K y k hk'
  have heasy : Submodule.span (MonoidAlgebra K G)
      (Set.range (fun l : Fin m => Finsupp.mapRange (subgroupAlgMap H K) (map_zero _) (k l))) ≤
      LinearMap.ker (Finsupp.linearCombination (MonoidAlgebra K G)
        (fun j => subgroupAlgMap H K (y j))) := by
    rw [Submodule.span_le]
    rintro _ ⟨l, rfl⟩
    refine LinearMap.mem_ker.mpr ?_
    rw [linearCombination_mapRange_alt (subgroupAlgMap H K) y (k l)]
    have h0 : Finsupp.linearCombination (MonoidAlgebra K H) y (k l) = 0 :=
      LinearMap.mem_ker.mp (hk' ▸ Submodule.subset_span (Set.mem_range_self l))
    rw [h0, map_zero]
  have hkerBfg : (LinearMap.ker (Finsupp.linearCombination (MonoidAlgebra K G)
      (fun j => subgroupAlgMap H K (y j)))).FG := by
    rw [le_antisymm hC2 heasy]
    exact Submodule.fg_span (Set.finite_range _)
  let lB : (Fin n →₀ MonoidAlgebra K G) →ₗ[MonoidAlgebra K G] I :=
    LinearMap.codRestrict I (Finsupp.linearCombination (MonoidAlgebra K G)
      (fun j => subgroupAlgMap H K (y j))) (fun c => by
        have h1 : Finsupp.linearCombination (MonoidAlgebra K G)
            (fun j => subgroupAlgMap H K (y j)) c ∈
            Submodule.span (MonoidAlgebra K G)
              (Set.range (fun j => subgroupAlgMap H K (y j))) := by
          rw [← Finsupp.range_linearCombination]
          exact LinearMap.mem_range_self _ c
        rwa [hspanB] at h1)
  have hlB : Function.Surjective lB := by
    rw [← LinearMap.range_eq_top, LinearMap.range_codRestrict, Finsupp.range_linearCombination,
      hspanB, Submodule.comap_subtype_self]
  have hkerB : (LinearMap.ker lB).FG := by
    rw [LinearMap.ker_codRestrict]
    exact hkerBfg
  exact Module.finitePresentation_of_surjective lB hlB hkerB

end Work.ORReductions.Coherent
