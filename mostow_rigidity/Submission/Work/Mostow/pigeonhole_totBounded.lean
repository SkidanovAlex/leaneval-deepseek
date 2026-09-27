import Mathlib

namespace Work.Mostow

/-- Pigeonhole principle for totally bounded sets: a totally bounded set `K` admits a uniform bound
`N` on the cardinality of finite subsets whose points are pairwise more than `t` apart. Equivalently,
any finite `F ⊆ K` with more than `N` points contains two distinct points at distance at most `t`. -/
theorem pigeonhole_totBounded {α : Type*} [PseudoMetricSpace α] {K : Set α}
    (hK : TotallyBounded K) {t : ℝ} (ht : 0 < t) :
    ∃ N : ℕ, ∀ F : Set α, F.Finite → F ⊆ K → N < F.ncard →
      ∃ x ∈ F, ∃ y ∈ F, x ≠ y ∧ dist x y ≤ t := by
  classical
  -- Cover `K` by finitely many balls of radius `t/2`.
  obtain ⟨C, hCfin, hCcov⟩ := (Metric.totallyBounded_iff.mp hK) (t / 2) (by linarith)
  refine ⟨C.ncard, fun F hFfin hFK hN => ?_⟩
  by_contra hcon
  push Not at hcon
  -- Every point of `F` lies in a ball of radius `t/2` centred at a point of `C`.
  have hmem : ∀ x ∈ F, ∃ c ∈ C, dist x c < t / 2 := by
    intro x hx
    have hxU : x ∈ ⋃ y ∈ C, Metric.ball y (t / 2) := hCcov (hFK hx)
    simp only [Set.mem_iUnion, Metric.mem_ball] at hxU
    obtain ⟨c, hcC, hd⟩ := hxU
    exact ⟨c, hcC, hd⟩
  -- Choose such a centre for each point of `F`, and junk values outside `F`.
  have hmem' : ∀ x : α, ∃ c : α, x ∈ F → c ∈ C ∧ dist x c < t / 2 := by
    intro x
    by_cases hx : x ∈ F
    · obtain ⟨c, hcC, hd⟩ := hmem x hx
      exact ⟨c, fun _ => ⟨hcC, hd⟩⟩
    · exact ⟨x, fun hx' => absurd hx' hx⟩
  choose f hf using hmem'
  have hfC : ∀ x ∈ F, f x ∈ C := fun x hx => (hf x hx).1
  have hfdist : ∀ x ∈ F, dist x (f x) < t / 2 := fun x hx => (hf x hx).2
  -- The chosen centres are pairwise distinct on `F`.
  have hinj : Set.InjOn f F := by
    intro x hx y hy hxy
    by_contra hxyeq
    have h1 : dist x (f x) < t / 2 := hfdist x hx
    have h2 : dist y (f y) < t / 2 := hfdist y hy
    have h4 : dist (f x) y = dist y (f y) := by rw [dist_comm, hxy]
    have hlt : dist x y < t := by
      calc dist x y ≤ dist x (f x) + dist (f x) y := dist_triangle x (f x) y
        _ = dist x (f x) + dist y (f y) := by rw [h4]
        _ < t / 2 + t / 2 := by linarith
        _ = t := by ring
    have := hcon x hx y hy hxyeq
    linarith
  have hle : F.ncard ≤ C.ncard := Set.ncard_le_ncard_of_injOn f hfC hinj hCfin
  omega

end Work.Mostow
