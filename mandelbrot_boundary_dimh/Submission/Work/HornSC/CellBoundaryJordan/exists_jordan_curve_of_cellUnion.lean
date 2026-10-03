import Mathlib
import Submission.Work.HornSC.Cells
import Submission.Work.HornSC.CellBoundaryJordan.Defs
import Submission.Work.HornSC.CellBoundaryJordan.frontier_cellUnion_eq_wallSet
import Submission.Work.HornSC.CellBoundaryJordan.exists_generic_ray_direction
import Submission.Work.HornSC.CellBoundaryJordan.exists_cycle_decomposition_disjoint
import Submission.Work.HornSC.CellBoundaryJordan.ray_wall_crossings_odd
import Submission.Work.HornSC.CellBoundaryJordan.ray_crossings_sum
import Submission.Work.HornSC.CellBoundaryJordan.exists_injective_circle_map_of_grid_cycle
import Submission.Work.HornSC.CellBoundaryJordan.grid_cycle_crossing_parity

namespace Work.HornSC.CellBoundaryJordan

open Set

/-! **A Jordan curve on the boundary of a connected union of lattice cells enclosing an interior
point.**

`A` is a finite nonempty family of closed unit lattice cells and `a` an interior point of the
union.  We produce an injective continuous map `γ : Circle → ℂ` whose image lies in the frontier
of the union, avoids `a`, and whose complement component at `a` is bounded (i.e. `a` lies in the
bounded complementary component of the Jordan curve `γ`).

Proof outline: the frontier of `cellUnion A` is its *wall set* (`frontier_cellUnion_eq_wallSet`);
the wall graph has even degree at every lattice point, so it decomposes into edge-disjoint simple
grid cycles (`exists_cycle_decomposition_disjoint`).  A generic ray issuing from `a` in a direction
`1 + εi` (`exists_generic_ray_direction`) never meets a lattice point and meets the wall set an
*odd* number of times (`ray_wall_crossings_odd`), because it begins in the interior and ends outside
the (bounded) union, and every transversal wall crossing flips membership.  The crossings split as
a disjoint union over the cycles (`ray_crossings_sum`), so some cycle is crossed oddly; by
`grid_cycle_crossing_parity` that cycle — a polygonal Jordan curve inside the frontier — encloses
`a`.  It is parametrised by `exists_injective_circle_map_of_grid_cycle`. -/
theorem exists_jordan_curve_of_cellUnion {A : Finset (ℤ × ℤ)} (hne : A.Nonempty)
    (hconn : IsConnected (cellUnion A)) {a : ℂ} (ha : a ∈ interior (cellUnion A)) :
    ∃ γ : C(Circle, ℂ), Function.Injective γ ∧ Set.range γ ⊆ frontier (cellUnion A) ∧
      a ∉ Set.range γ ∧ Bornology.IsBounded (connectedComponentIn ((Set.range γ)ᶜ) a) := by
  classical
  obtain ⟨ε, hεpos, hgen⟩ := exists_generic_ray_direction a
  obtain ⟨m, k, u, hk3, hcl, hstep, hinj, hdisj, hunion⟩ :=
    exists_cycle_decomposition_disjoint A
  obtain ⟨S, T, hS, hT, hcard, hcover⟩ :=
    ray_crossings_sum A hstep hdisj hunion hεpos hgen
  have hfinS : {t : ℝ | 0 < t ∧ a + (t : ℂ) * (⟨1, ε⟩ : ℂ) ∈ wallSet A}.Finite := by
    rw [show {t : ℝ | 0 < t ∧ a + (t : ℂ) * (⟨1, ε⟩ : ℂ) ∈ wallSet A} = (↑S : Set ℝ) from
      Set.ext (fun t => (hS t).symm)]
    exact S.finite_toSet
  have hoddS : Odd S.card := by
    have h1 := ray_wall_crossings_odd A hεpos ha hgen hfinS
    have h2 : hfinS.toFinset = S := by
      refine Finset.ext (fun t => ?_)
      simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
      exact (hS t).symm
    rwa [h2] at h1
  obtain ⟨i, hi⟩ : ∃ i : Fin m, Odd (T i).card := by
    by_contra hcon
    simp only [not_exists] at hcon
    have hev : ∀ j : Fin m, Even (T j).card := fun j => Nat.not_odd_iff_even.mp (hcon j)
    have hsum : Even S.card := by
      rw [hcard]
      exact Finset.even_sum _ (fun j _ => hev j)
    exact (Nat.not_even_iff_odd.mpr hoddS) hsum
  have hki3 : 3 ≤ k i := hk3 i
  set v : ℕ → ℤ × ℤ := fun t => u i (t % k i) with hv
  have hv_eq_of_lt : ∀ t : ℕ, t < k i → v t = u i t := by
    intro t ht
    simp only [hv]
    rw [Nat.mod_eq_of_lt ht]
  have hv_succ : ∀ t : ℕ, t < k i → v (t + 1) = u i (t + 1) := by
    intro t ht
    by_cases h : t + 1 < k i
    · exact hv_eq_of_lt _ h
    · have hk : t + 1 = k i := by omega
      have h1 : v (t + 1) = u i 0 := by simp only [hv, hk, Nat.mod_self]
      rw [h1, hk]
      exact (hcl i).symm
  have hperv : ∀ t : ℕ, v (t + k i) = v t := by
    intro t
    simp only [hv]
    rw [Nat.add_mod_right]
  have hstepv : ∀ t : ℕ, t < k i → IsUnitAdj (v t) (v (t + 1)) := by
    intro t ht
    rw [hv_eq_of_lt t ht, hv_succ t ht]
    exact hstep i t ht
  have hinjv : ∀ t t' : ℕ, t < k i → t' < k i → v t = v t' → t = t' := by
    intro t t' ht ht' h
    rw [hv_eq_of_lt t ht, hv_eq_of_lt t' ht'] at h
    exact hinj i t t' ht ht' h
  have hsegv : ∀ t : ℕ, t < k i → adjSeg (v t) (v (t + 1)) = adjSeg (u i t) (u i (t + 1)) := by
    intro t ht
    rw [hv_eq_of_lt t ht, hv_succ t ht]
  have hsetv : (⋃ j ∈ {j : ℕ | j < k i}, adjSeg (v j) (v (j + 1)))
      = (⋃ j ∈ {j : ℕ | j < k i}, adjSeg (u i j) (u i (j + 1))) := by
    refine Set.iUnion₂_congr (fun j hj => ?_)
    exact hsegv j (by simpa using hj)
  have hna : a ∉ (⋃ j ∈ {j : ℕ | j < k i}, adjSeg (u i j) (u i (j + 1))) := by
    intro hcon
    have h1 : a ∈ frontier (cellUnion A) := by
      rw [frontier_cellUnion_eq_wallSet, ← hunion]
      exact Set.mem_iUnion.mpr ⟨i, hsetv ▸ hcon⟩
    exact ((mem_interior_iff_notMem_frontier (interior_subset ha)).mp ha) h1
  have hbdd : Bornology.IsBounded
      (connectedComponentIn ((⋃ j ∈ {j : ℕ | j < k i}, adjSeg (u i j)
        (u i (j + 1)))ᶜ) a) := by
    have hfinV : ({t : ℝ | 0 < t ∧ a + (t : ℂ) * (⟨1, ε⟩ : ℂ) ∈
        (⋃ j ∈ {j : ℕ | j < k i}, adjSeg (v j) (v (j + 1)))} : Set ℝ).Finite := by
      rw [show {t : ℝ | 0 < t ∧ a + (t : ℂ) * (⟨1, ε⟩ : ℂ) ∈
          (⋃ j ∈ {j : ℕ | j < k i}, adjSeg (v j) (v (j + 1)))} = (↑(T i) : Set ℝ) from
        Set.ext (fun t => by
          rw [Set.mem_setOf_eq, hsetv]
          exact (hT i t).symm)]
      exact (T i).finite_toSet
    have hVT : hfinV.toFinset = T i := by
      refine Finset.ext (fun t => ?_)
      rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, hsetv]
      exact (hT i t).symm
    have hoddV : Odd hfinV.toFinset.card := hVT ▸ hi
    have haV : a ∉ (⋃ j ∈ {j : ℕ | j < k i}, adjSeg (v j) (v (j + 1))) := by
      rw [hsetv]
      exact hna
    have hpar := grid_cycle_crossing_parity hki3 v hperv hinjv hstepv hεpos haV hgen hfinV
    exact hsetv ▸ (hpar.mp hoddV)
  obtain ⟨γ, hγinj, hγrange⟩ :=
    exists_injective_circle_map_of_grid_cycle hki3 v hperv hinjv hstepv
  refine ⟨γ, hγinj, ?_, ?_, ?_⟩
  · rw [hγrange]
    intro z hz
    rw [frontier_cellUnion_eq_wallSet, ← hunion]
    exact Set.mem_iUnion.mpr ⟨i, hsetv ▸ hz⟩
  · rw [hγrange]
    intro hcon
    have h1 : a ∈ frontier (cellUnion A) := by
      rw [frontier_cellUnion_eq_wallSet, ← hunion]
      exact Set.mem_iUnion.mpr ⟨i, hsetv ▸ hcon⟩
    exact ((mem_interior_iff_notMem_frontier (interior_subset ha)).mp ha) h1
  · rw [hγrange, hsetv]
    exact hbdd

end Work.HornSC.CellBoundaryJordan
