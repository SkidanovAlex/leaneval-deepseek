import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.Measure.Lattice

open MeasureTheory Set
open scoped BigOperators

/-- **General finite-dimensional lattice/integral comparison.**  For any finite
index type `ι` and a function `G` on `ι → ℝ` that is antitone with respect to
the product order on the orthant (`0 ≤ x ≤ y` coordinatewise implies
`G y ≤ G x`), the right-endpoint lattice sum over the box `k ∈ [0,n)^ι` is
bounded by the integral over `[0,n]^ι`.

The proof tiles `[0,n]^ι` by the half-open unit cells `∏ i, [k i, k i + 1)`
(one per lattice point `k ∈ [0,n)^ι`), which are pairwise disjoint and have
volume `1`; on each cell the integrand dominates `G (k+1)` by antitonicity. -/
theorem lattice_sum_le_integral {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    {G : (ι → ℝ) → ℝ}
    (hanti : ∀ x y : ι → ℝ, (∀ i, 0 ≤ x i) → (∀ i, x i ≤ y i) → G y ≤ G x)
    (hint : IntegrableOn G (Set.pi Set.univ (fun _ : ι => Set.Icc (0 : ℝ) n))) :
    (∑ k ∈ Fintype.piFinset (fun _ : ι => Finset.range n),
        G (fun i => (k i : ℝ) + 1))
      ≤ ∫ u in Set.pi Set.univ (fun _ : ι => Set.Icc (0 : ℝ) n), G u := by
  classical
  set K : Finset (ι → ℕ) := Fintype.piFinset (fun _ : ι => Finset.range n) with hK
  have hKmem : ∀ k : ι → ℕ, k ∈ K ↔ ∀ i, k i ∈ Finset.range n := by
    intro k; rw [hK]; exact Fintype.mem_piFinset
  have hcell_meas : ∀ k : ι → ℕ,
      MeasurableSet (Set.pi Set.univ (fun i => Set.Ico (k i : ℝ) ((k i : ℝ) + 1))) :=
    fun _ => MeasurableSet.univ_pi (fun _ => measurableSet_Ico)
  have hcell_sub : ∀ k ∈ K,
      (Set.pi Set.univ (fun i => Set.Ico (k i : ℝ) ((k i : ℝ) + 1)))
        ⊆ Set.pi Set.univ (fun _ : ι => Set.Icc (0 : ℝ) n) := by
    intro k hk x hx
    rw [Set.mem_univ_pi]
    intro i
    have hkn : k i < n := Finset.mem_range.mp ((hKmem k).mp hk i)
    have hxi : x i ∈ Set.Ico (k i : ℝ) ((k i : ℝ) + 1) := Set.mem_univ_pi.mp hx i
    refine ⟨(Nat.cast_nonneg (k i)).trans hxi.1, ?_⟩
    have hle : (k i : ℝ) + 1 ≤ (n : ℝ) := by
      have h2 : k i + 1 ≤ n := Nat.succ_le_of_lt hkn
      exact_mod_cast h2
    exact (hxi.2.trans_le hle).le
  have hcell_int : ∀ k ∈ K,
      IntegrableOn G (Set.pi Set.univ (fun i => Set.Ico (k i : ℝ) ((k i : ℝ) + 1))) :=
    fun k hk => hint.mono_set (hcell_sub k hk)
  have hcell_disj : (↑K : Set (ι → ℕ)).Pairwise (Function.onFun Disjoint
      (fun k : ι → ℕ => Set.pi Set.univ (fun i => Set.Ico (k i : ℝ) ((k i : ℝ) + 1)))) := by
    rintro a _ b _ hab
    simp only [Function.onFun]
    rw [Set.disjoint_left]
    intro x hxa hxb
    obtain ⟨i, hi⟩ : ∃ i, a i ≠ b i := by
      by_contra h
      exact hab (funext fun i => by by_contra h'; exact h ⟨i, h'⟩)
    rcases lt_or_gt_of_ne hi with hlt | hgt
    · have h1 : x i < (b i : ℝ) :=
        lt_of_lt_of_le (Set.mem_univ_pi.mp hxa i).2
          (by exact_mod_cast Nat.succ_le_of_lt hlt)
      exact absurd (Set.mem_univ_pi.mp hxb i).1 (not_le.mpr h1)
    · have h2 : x i < (a i : ℝ) :=
        lt_of_lt_of_le (Set.mem_univ_pi.mp hxb i).2
          (by exact_mod_cast Nat.succ_le_of_lt hgt)
      exact absurd (Set.mem_univ_pi.mp hxa i).1 (not_le.mpr h2)
  have hunion :
      (⋃ k ∈ K, Set.pi Set.univ (fun i => Set.Ico (k i : ℝ) ((k i : ℝ) + 1)))
        = Set.pi Set.univ (fun _ : ι => Set.Ico (0 : ℝ) n) := by
    ext x
    rw [show (x ∈ ⋃ k ∈ K, Set.pi Set.univ (fun i => Set.Ico (k i : ℝ) ((k i : ℝ) + 1)))
        ↔ ∃ k, k ∈ K ∧ x ∈ Set.pi Set.univ
            (fun i => Set.Ico (k i : ℝ) ((k i : ℝ) + 1)) from by simp]
    constructor
    · rintro ⟨k, hk, hx⟩
      rw [Set.mem_univ_pi]
      intro i
      have hkn : k i < n := Finset.mem_range.mp ((hKmem k).mp hk i)
      have hxi := Set.mem_univ_pi.mp hx i
      exact ⟨(Nat.cast_nonneg (k i)).trans hxi.1,
        hxi.2.trans_le (by exact_mod_cast Nat.succ_le_of_lt hkn)⟩
    · intro hx
      have hx' : ∀ i, x i ∈ Set.Ico (0 : ℝ) n := Set.mem_univ_pi.mp hx
      refine ⟨fun i => ⌊x i⌋₊, ?_, ?_⟩
      · rw [hKmem]
        intro i
        refine Finset.mem_range.mpr ?_
        have h1 : (⌊x i⌋₊ : ℝ) ≤ x i := Nat.floor_le (hx' i).1
        exact_mod_cast lt_of_le_of_lt h1 (hx' i).2
      · rw [Set.mem_univ_pi]
        intro i
        exact ⟨Nat.floor_le (hx' i).1, Nat.lt_floor_add_one (x i)⟩
  have hbox_ae : (Set.pi Set.univ (fun _ : ι => Set.Ico (0 : ℝ) n)) =ᵐ[volume]
      Set.pi Set.univ (fun _ : ι => Set.Icc (0 : ℝ) n) := by
    have h := Measure.univ_pi_Ico_ae_eq_Icc (μ := fun _ : ι => (volume : Measure ℝ))
      (f := fun _ => (0 : ℝ)) (g := fun _ => (n : ℝ))
    rw [← volume_pi] at h
    simpa only [Set.pi_univ_Icc] using h
  have step1 : (∑ k ∈ K, G (fun i => (k i : ℝ) + 1))
      ≤ ∑ k ∈ K, ∫ u in Set.pi Set.univ (fun i => Set.Ico (k i : ℝ) ((k i : ℝ) + 1)), G u := by
    apply Finset.sum_le_sum
    intro k hk
    have hreal : (MeasureTheory.Measure.real (volume : Measure (ι → ℝ))
        (Set.pi Set.univ (fun i => Set.Ico (k i : ℝ) ((k i : ℝ) + 1)))) = 1 := by
      show (volume (Set.pi Set.univ (fun i => Set.Ico (k i : ℝ) ((k i : ℝ) + 1)))).toReal = 1
      rw [Real.volume_pi_Ico_toReal]
      · simp
      · intro i; simp
    have hpt : ∀ x ∈ Set.pi Set.univ (fun i => Set.Ico (k i : ℝ) ((k i : ℝ) + 1)),
        G (fun i => (k i : ℝ) + 1) ≤ G x := by
      intro x hx
      exact hanti x (fun i => (k i : ℝ) + 1)
        (fun i => (Nat.cast_nonneg (k i)).trans (Set.mem_univ_pi.mp hx i).1)
        (fun i => (Set.mem_univ_pi.mp hx i).2.le)
    have hge := setIntegral_ge_of_const_le (μ := volume)
      (s := Set.pi Set.univ (fun i => Set.Ico (k i : ℝ) ((k i : ℝ) + 1)))
      (f := G) (c := G (fun i => (k i : ℝ) + 1))
      (hcell_meas k) (by rw [Real.volume_pi_Ico]; simp) hpt (hcell_int k hk)
    rwa [hreal, one_smul] at hge
  have step2 : (∑ k ∈ K, ∫ u in Set.pi Set.univ (fun i => Set.Ico (k i : ℝ) ((k i : ℝ) + 1)), G u)
      = ∫ u in (⋃ k ∈ K, Set.pi Set.univ
          (fun i => Set.Ico (k i : ℝ) ((k i : ℝ) + 1))), G u :=
    (MeasureTheory.integral_biUnion_finset K (fun k _ => hcell_meas k) hcell_disj hcell_int).symm
  have step4 : (∫ u in Set.pi Set.univ (fun _ : ι => Set.Ico (0 : ℝ) n), G u)
      = ∫ u in Set.pi Set.univ (fun _ : ι => Set.Icc (0 : ℝ) n), G u :=
    MeasureTheory.setIntegral_congr_set hbox_ae
  calc
    (∑ k ∈ K, G (fun i => (k i : ℝ) + 1))
        ≤ ∑ k ∈ K, ∫ u in Set.pi Set.univ
            (fun i => Set.Ico (k i : ℝ) ((k i : ℝ) + 1)), G u := step1
    _ = ∫ u in (⋃ k ∈ K, Set.pi Set.univ
            (fun i => Set.Ico (k i : ℝ) ((k i : ℝ) + 1))), G u := step2
    _ = ∫ u in Set.pi Set.univ (fun _ : ι => Set.Ico (0 : ℝ) n), G u := by rw [hunion]
    _ = ∫ u in Set.pi Set.univ (fun _ : ι => Set.Icc (0 : ℝ) n), G u := step4

/-- **The `Fin 3` lattice cell comparison against the box integral**: for a
function `G` on `Fin 3 → ℝ` that is antitone with respect to the product order
on the orthant (`0 ≤ x ≤ y` coordinatewise implies `G y ≤ G x`), the
right-endpoint lattice sum over the box `k ∈ [0,n)³` is bounded by the
integral over `[0,n]³`.  (The cells `k + [0,1]³` tile `[0,n]³`, are
measure-preserving translates, and on each cell the integrand dominates
`G k`.) -/
theorem lattice_sum_le_integral_fin3 {n : ℕ} {G : (Fin 3 → ℝ) → ℝ}
    (hanti : ∀ x y : Fin 3 → ℝ, (∀ i, 0 ≤ x i) → (∀ i, x i ≤ y i) → G y ≤ G x)
    (hint : IntegrableOn G (Set.pi Set.univ (fun _ : Fin 3 => Set.Icc (0 : ℝ) n))) :
    (∑ k ∈ Fintype.piFinset (fun _ : Fin 3 => Finset.range n),
        G (fun i => (k i : ℝ) + 1))
      ≤ ∫ u in Set.pi Set.univ (fun _ : Fin 3 => Set.Icc (0 : ℝ) n), G u :=
  lattice_sum_le_integral hanti hint

end Commons.Measure.Lattice