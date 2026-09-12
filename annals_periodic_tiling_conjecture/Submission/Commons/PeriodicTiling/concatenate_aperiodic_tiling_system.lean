import Mathlib
import Submission.Commons.PeriodicTiling.IsAperiodicTilingEquation_map_addEquiv
import Submission.Commons.PeriodicTiling.rigid_partition_zmod
import Submission.Commons.PeriodicTiling.rigid_partition_concat_solvable
import Submission.Commons.PeriodicTiling.periodic_tiling_set_of_rigid_partition_concat

namespace Commons.PeriodicTiling

open scoped Pointwise

def IsAperiodicTilingSystem {G : Type*} [AddCommGroup G] {M : ℕ} (F : Fin M → Set G) : Prop :=
  (∃ A : Set G, ∀ i : Fin M, IsTiling (F i) A) ∧
  ∀ A : Set G, (∀ i : Fin M, IsTiling (F i) A) →
    ¬ IsPeriodicTilingSet A

theorem concatenate_aperiodic_tiling_system
    {G : Type*} [AddCommGroup G] {M : ℕ} (F : Fin M → Set G)
    (hF : ∀ i : Fin M, (F i).Finite ∧ (F i).Nonempty)
    (hSys : IsAperiodicTilingSystem F) :
    ∃ N : ℕ, 0 < N ∧ ∃ F' : Set (G × ZMod N),
      F'.Finite ∧ F'.Nonempty ∧ IsAperiodicTilingEquation F' := by
  classical
  have hM : 0 < M := by
    by_contra hnot
    have hM0 : M = 0 := Nat.eq_zero_of_not_pos hnot
    subst M
    have hper_univ : IsPeriodicTilingSet (Set.univ : Set G) := by
      refine ⟨⊤, inferInstance, {0}, ?_⟩
      ext x
      simp
    have hvac : ∀ i : Fin 0, IsTiling (F i) (Set.univ : Set G) := by
      intro i
      exact Fin.elim0 i
    exact (hSys.2 (Set.univ : Set G) hvac) hper_univ
  obtain ⟨N, hN, E, hEne, hEcover, hEdisj, hErigid⟩ := rigid_partition_zmod M hM
  have hset_add_eq (s : Set (ZMod N)) (h : ZMod N) :
      (@HAdd.hAdd (Set (ZMod N)) (ZMod N) (Set (ZMod N)) instHAddSetOfAdd_submission s h) =
      (@HAdd.hAdd (Set (ZMod N)) (ZMod N) (Set (ZMod N)) Set.instHAddSetElement s h) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, h, by simp, by simp⟩
    · rintro ⟨y, hy, z, hz, hx⟩
      have hz' : z = h := by simpa using hz
      exact ⟨y, hy, by simpa [hz', add_comm] using hx.symm⟩
  have hErigid' : ∀ i j : Fin M, ∀ h : ZMod N, h ≠ 0 →
      (E i ∩ (E j + h)).Nonempty := by
    intro i j h hh
    have hx := hErigid i j h hh
    have hset := hset_add_eq (E j) h
    simpa [hset] using hx
  let F' : Set (G × ZMod N) := {x : G × ZMod N | ∃ i : Fin M, x.1 ∈ F i ∧ x.2 ∈ E i}
  refine ⟨N, hN, F', ?_, ?_, ?_⟩
  · -- finite
    haveI : NeZero N := NeZero.of_pos hN
    have hF'eq : F' = ⋃ i : Fin M, (F i) ×ˢ (E i) := by
      ext x
      simp [F', Set.mem_iUnion, Set.mem_prod]
    rw [hF'eq]
    refine Set.finite_iUnion (fun i => ?_)
    have hEfin : (E i).Finite := by
      exact (Set.finite_univ : (Set.univ : Set (ZMod N)).Finite).subset (Set.subset_univ (E i))
    exact Set.Finite.prod (hF i).1 hEfin
  · -- nonempty
    let i0 : Fin M := ⟨0, hM⟩
    rcases (hF i0).2 with ⟨g, hg⟩
    rcases hEne i0 with ⟨e, he⟩
    refine ⟨(g, e), ?_⟩
    dsimp [F']
    exact ⟨i0, hg, he⟩
  · constructor
    · -- solvable
      rcases hSys.1 with ⟨A, hA⟩
      refine ⟨A ×ˢ ({0} : Set (ZMod N)), ?_⟩
      have hsol := rigid_partition_concat_solvable F A E hEcover hEdisj hA
      simpa [F'] using hsol
    · -- aperiodic
      intro B hB hBper
      have hB' : AddSubgroup.IsComplement B F' := by
        simpa [F'] using hB
      have hFne : ∀ i : Fin M, (F i).Nonempty := fun i => (hF i).2
      rcases periodic_tiling_set_of_rigid_partition_concat F E hN hFne hEne hEcover hEdisj hErigid' hB' hBper with
        ⟨A, hAtile, hAper⟩
      exact hSys.2 A hAtile hAper

end Commons.PeriodicTiling
