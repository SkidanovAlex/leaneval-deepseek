import Mathlib
import Submission.Work.PL.Defs

namespace Work.Cells.Connell

open Set Metric

/-- A compact subset of the open unit sup-norm cube `PL.openCube 1` in `ℝⁿ` is contained in
some closed sup-norm cube `PL.closedCube α` with `0 < α < 1`.

This is the elementary "shrinking" fact behind Connell's topological h-cobordism argument:
the sup-norm of a point of `K` is a continuous function of the point, so it attains a maximum
on the compact set `K`, and that maximum is `< 1` because `K` avoids the boundary of the cube. -/
theorem exists_closedCube_subset_of_isCompact_subset_openCube {n : ℕ} {K : Set (PL.E n)}
    (hK : IsCompact K) (hK1 : K ⊆ PL.openCube (n := n) 1) :
    ∃ α : ℝ, 0 < α ∧ α < 1 ∧ K ⊆ PL.closedCube α := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · -- `ℝ⁰` is a single point, and the cubes are everything.
    subst hn
    exact ⟨1 / 2, by norm_num, by norm_num, fun x _ i => i.elim0⟩
  · rcases Set.eq_empty_or_nonempty K with hK0 | hKne
    · rw [hK0]
      exact ⟨1 / 2, by norm_num, by norm_num, Set.empty_subset _⟩
    · -- Coordinatewise supremum of `|x i|` over `K`.
      set bF : Fin n → ℝ := fun i => sSup ((fun x : PL.E n => |x i|) '' K) with hbF
      have hcont : ∀ i : Fin n, Continuous (fun x : PL.E n => |x i|) := fun i =>
        continuous_abs.comp (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) i)
      have hbF_mem : ∀ i, bF i ∈ (fun x : PL.E n => |x i|) '' K := by
        intro i
        exact (hK.image (hcont i)).sSup_mem (hKne.image _)
      have hbF_nonneg : ∀ i, 0 ≤ bF i := by
        intro i
        obtain ⟨y, hyK, hyb⟩ := hbF_mem i
        rw [show bF i = |y i| from hyb.symm]
        exact abs_nonneg _
      have hbF_lt_one : ∀ i, bF i < 1 := by
        intro i
        obtain ⟨y, hyK, hyb⟩ := hbF_mem i
        rw [show bF i = |y i| from hyb.symm]
        exact hK1 hyK i
      -- the (finite) maximum of the coordinatewise suprema
      have huniv : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, Finset.mem_univ _⟩
      set m : ℝ := (Finset.univ : Finset (Fin n)).sup' huniv bF with hm
      have hm_nonneg : 0 ≤ m := by
        rw [hm]
        exact Finset.sup'_mem (Ici (0 : ℝ))
          (fun x hx y hy => le_trans hx (le_max_left x y))
          Finset.univ huniv bF (fun i _ => hbF_nonneg i)
      have hm_lt_one : m < 1 := by
        have h : m ∈ Iio (1 : ℝ) := by
          rw [hm]
          exact Finset.sup'_mem (Iio (1 : ℝ))
            (fun x hx y hy => by simpa using max_lt hx hy)
            Finset.univ huniv bF (fun i _ => hbF_lt_one i)
        exact h
      refine ⟨(m + 1) / 2, by linarith, by linarith, ?_⟩
      intro x hx i
      have h1 : |x i| ≤ bF i :=
        le_csSup (hK.image (hcont i)).bddAbove (mem_image_of_mem _ hx)
      have h2 : bF i ≤ m := by
        rw [hm]
        exact Finset.le_sup' bF (Finset.mem_univ i)
      have h3 : m ≤ (m + 1) / 2 := by linarith
      linarith

end Work.Cells.Connell
