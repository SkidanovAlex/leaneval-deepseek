import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Cohomology

open Metric

/-- Auxiliary general form of `exists_ball_sequence`, valid in any metric space.

Given a compact set `K` and a summable-to-zero scale `e n = (1/3)^n`, we take for each `n` a
finite `e n`-net `t n ⊆ K` (existing by total boundedness of `K`) and set `T n` to be the closed
`(2 * e n)`-neighbourhood of this net.  The scale `2/3^{n+1} + 1/3^n < 2/3^n` makes the `T n`
decrease into the interiors of their predecessors. -/
theorem exists_ball_sequence_aux {X : Type*} [MetricSpace X]
    (K : Set X) (hK : IsCompact K) :
    ∃ (T : ℕ → Set X)
      (k : ℕ → ℕ) (c : (n : ℕ) → Fin (k n) → X)
      (r : (n : ℕ) → Fin (k n) → ℝ),
      (∀ n j, 0 < r n j) ∧
      (∀ n, T n = ⋃ j, Metric.closedBall (c n j) (r n j)) ∧
      (∀ n j, (Metric.closedBall (c n j) (r n j)) ∩ K ≠ ∅) ∧
      (∀ n, K ⊆ T n) ∧
      (∀ n, T (n+1) ⊆ interior (T n)) ∧
      (⋂ n, T n) ⊆ K := by
  classical
  let e : ℕ → ℝ := fun n => (1/3 : ℝ)^n
  have he_pos : ∀ n, 0 < e n := fun n => pow_pos (by norm_num) n
  -- finite `e n`-nets of `K`, sitting inside `K`
  have hnet : ∀ n : ℕ, ∃ t : Set X, t ⊆ K ∧ t.Finite ∧ K ⊆ ⋃ y ∈ t, ball y (e n) :=
    fun n => Metric.finite_approx_of_totallyBounded hK.totallyBounded (e n) (he_pos n)
  choose t htK htfin htcover using hnet
  let f : ℕ → Finset X := fun n => (htfin n).toFinset
  have hf_mem : ∀ n y, y ∈ f n ↔ y ∈ t n := fun n y => (htfin n).mem_toFinset
  let k : ℕ → ℕ := fun n => (f n).card
  let c : (n : ℕ) → Fin (k n) → X := fun n j => ((f n).equivFin.symm j : X)
  let r : (n : ℕ) → Fin (k n) → ℝ := fun n _ => 2 * e n
  have hr_pos : ∀ n j, 0 < r n j := by
    intro n j; dsimp only [r]; positivity
  have hcmem : ∀ n j, c n j ∈ t n := by
    intro n j
    exact (hf_mem n (c n j)).mp (by dsimp only [c]; exact ((f n).equivFin.symm j).2)
  have hcsurj : ∀ n (y : X) (hy : y ∈ f n), c n ((f n).equivFin ⟨y, hy⟩) = y := by
    intro n y hy
    dsimp only [c]
    simp
  refine ⟨fun n => ⋃ j, Metric.closedBall (c n j) (r n j), k, c, r, hr_pos, ?_, ?_, ?_, ?_, ?_⟩
  · intro n; rfl
  · intro n j
    rw [← Set.nonempty_iff_ne_empty]
    exact ⟨c n j, Metric.mem_closedBall_self (le_of_lt (hr_pos n j)), htK n (hcmem n j)⟩
  · intro n x hx
    obtain ⟨y, hyt, hxy⟩ := Set.mem_iUnion₂.mp (htcover n hx)
    have hyf : y ∈ f n := (hf_mem n y).mpr hyt
    have hxy' : dist x y < e n := Metric.mem_ball.mp hxy
    refine Set.mem_iUnion.mpr ⟨(f n).equivFin ⟨y, hyf⟩, ?_⟩
    rw [Metric.mem_closedBall, hcsurj n y hyf]
    have hle : e n ≤ r n ((f n).equivFin ⟨y, hyf⟩) := by
      show e n ≤ 2 * e n
      linarith [he_pos n]
    exact le_of_lt (lt_of_lt_of_le hxy' hle)
  · intro n x hx
    rw [Set.mem_iUnion] at hx
    obtain ⟨q, hxq⟩ := hx
    rw [Metric.mem_closedBall] at hxq
    obtain ⟨y, hyt, hyb⟩ := Set.mem_iUnion₂.mp (htcover n (htK (n+1) (hcmem (n+1) q)))
    have hyf : y ∈ f n := (hf_mem n y).mpr hyt
    have hyb' : dist (c (n+1) q) y < e n := Metric.mem_ball.mp hyb
    have hxy : x ∈ ball (c n ((f n).equivFin ⟨y, hyf⟩)) (r n ((f n).equivFin ⟨y, hyf⟩)) := by
      rw [Metric.mem_ball, hcsurj n y hyf]
      have h1 : dist x y < r (n+1) q + e n :=
        lt_of_le_of_lt (dist_triangle x (c (n+1) q) y) (add_lt_add_of_le_of_lt hxq hyb')
      have h2 : r (n+1) q + e n < r n ((f n).equivFin ⟨y, hyf⟩) := by
        dsimp only [r, e]
        rw [pow_succ]
        nlinarith [pow_pos (by norm_num : (0:ℝ) < 1/3) n]
      linarith
    exact interior_maximal
      (fun z hz => Set.mem_iUnion.mpr ⟨(f n).equivFin ⟨y, hyf⟩, Metric.ball_subset_closedBall hz⟩)
      Metric.isOpen_ball hxy
  · intro x hx
    rw [Set.mem_iInter] at hx
    rw [← (hK.isClosed).closure_eq, Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (x := ε / 2) (y := (1/3 : ℝ))
      (by linarith) (by norm_num)
    have h2e : (2 : ℝ) * e n < ε := by dsimp only [e]; linarith
    have hxTn : x ∈ ⋃ j, Metric.closedBall (c n j) (r n j) := hx n
    rw [Set.mem_iUnion] at hxTn
    obtain ⟨q, hxq⟩ := hxTn
    rw [Metric.mem_closedBall] at hxq
    dsimp only [r] at hxq
    exact ⟨c n q, htK n (hcmem n q), by linarith⟩

theorem exists_ball_sequence {N : ℕ} (hN : 1 ≤ N)
    (K : Set (EuclideanSpace ℝ (Fin N))) (hK : IsCompact K) :
    ∃ (T : ℕ → Set (EuclideanSpace ℝ (Fin N)))
      (k : ℕ → ℕ) (c : (n : ℕ) → Fin (k n) → EuclideanSpace ℝ (Fin N))
      (r : (n : ℕ) → Fin (k n) → ℝ),
      (∀ n j, 0 < r n j) ∧
      (∀ n, T n = ⋃ j, Metric.closedBall (c n j) (r n j)) ∧
      (∀ n j, (Metric.closedBall (c n j) (r n j)) ∩ K ≠ ∅) ∧
      (∀ n, K ⊆ T n) ∧
      (∀ n, T (n+1) ⊆ interior (T n)) ∧
      (⋂ n, T n) ⊆ K := by
  exact exists_ball_sequence_aux K hK

end Work.Cohomology
