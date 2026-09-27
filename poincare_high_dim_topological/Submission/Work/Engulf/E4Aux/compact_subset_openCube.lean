import Mathlib
import Submission.Work.PL.Defs
import Submission.Work.Engulf.Basic

/-!
# A compact subset of the open unit cube lies in a strictly smaller open cube

`PL.openCube r = {x : E n | ∀ i, |x i| < r}` is the sup-norm cube of radius `r`.  We show that a
compact `K ⊆ openCube 1` is contained in `openCube β` for some `0 ≤ β < 1`.

The proof is the standard compactness argument: `openCube 1 = ⋃ (β : Ioo 0 1), openCube β` (using
that `Fin n` is finite, so the coordinatewise supremum of `|x ·|` at a point of the cube is `< 1`),
and a finite subcover is bounded by the maximum of its finitely many radii.
-/

namespace Work.Engulf.E4Aux

open Set Metric

theorem compact_subset_openCube {n : ℕ} {K : Set (PL.E n)}
    (hK : IsCompact K) (hsub : K ⊆ PL.openCube (1 : ℝ)) :
    ∃ β : ℝ, 0 ≤ β ∧ β < 1 ∧ K ⊆ PL.openCube β := by
  by_cases hn : n = 0
  · -- `E 0` is a point, so any radius `≥ 0` works.
    subst hn
    refine ⟨0, le_refl 0, one_pos, ?_⟩
    intro x _ i
    exact Fin.elim0 i
  · have i0 : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
    have huniv : (Finset.univ : Finset (Fin n)).Nonempty := ⟨i0, Finset.mem_univ i0⟩
    by_cases hne : K.Nonempty
    · -- `openCube 1` is the union of the smaller cubes `openCube β`, `β ∈ (0,1)`.
      have hcover : K ⊆ ⋃ (β : Set.Ioo (0 : ℝ) 1), PL.openCube β.1 := by
        intro x hx
        have hx1 : ∀ i, |x i| < 1 := hsub hx
        have hsup1 : Finset.univ.sup' huniv (fun i => |x i|) < 1 := by
          rw [Finset.sup'_lt_iff]
          intro i _
          exact hx1 i
        have hsup0 : 0 ≤ Finset.univ.sup' huniv (fun i => |x i|) := by
          have h := Finset.le_sup' (fun i => |x i|) (Finset.mem_univ i0)
          linarith [abs_nonneg (x i0)]
        refine Set.mem_iUnion.2 ⟨⟨(Finset.univ.sup' huniv (fun i => |x i|) + 1) / 2,
          by linarith, by linarith⟩, ?_⟩
        intro i
        have h := Finset.le_sup' (fun i => |x i|) (Finset.mem_univ i)
        linarith
      obtain ⟨t, ht⟩ := hK.elim_finite_subcover
        (fun β : Set.Ioo (0 : ℝ) 1 => PL.openCube β.1)
        (fun β => by
          rw [PL.openCube, Set.ofPred_forall]
          exact isOpen_iInter_of_finite (fun i => isOpen_lt (by fun_prop) continuous_const))
        hcover
      obtain ⟨x₀, hx₀K⟩ := hne
      -- the finite subcover is nonempty because `K` is
      have htne : t.Nonempty := by
        have hxmem : x₀ ∈ ⋃ i ∈ t, PL.openCube i.1 := ht hx₀K
        rw [Set.mem_iUnion] at hxmem
        obtain ⟨i, hxmem⟩ := hxmem
        rw [Set.mem_iUnion] at hxmem
        obtain ⟨hi, -⟩ := hxmem
        exact ⟨i, hi⟩
      -- the largest radius occurring in the finite subcover
      refine ⟨t.sup' htne (fun i => i.1), ?_, ?_, ?_⟩
      · obtain ⟨i₀, hi₀⟩ := htne
        have h2 := Finset.le_sup' (fun i => i.1) hi₀
        linarith [i₀.2.1]
      · rw [Finset.sup'_lt_iff]
        intro i hi
        exact i.2.2
      · intro x hx
        have hxmem : x ∈ ⋃ i ∈ t, PL.openCube i.1 := ht hx
        rw [Set.mem_iUnion] at hxmem
        obtain ⟨i, hxmem⟩ := hxmem
        rw [Set.mem_iUnion] at hxmem
        obtain ⟨hi, hxi⟩ := hxmem
        intro j
        have h1 : |x j| < i.1 := hxi j
        have h2 := Finset.le_sup' (fun i => i.1) hi
        linarith
    · rw [Set.not_nonempty_iff_eq_empty.mp hne]
      exact ⟨0, le_refl 0, one_pos, Set.empty_subset _⟩

end Work.Engulf.E4Aux
