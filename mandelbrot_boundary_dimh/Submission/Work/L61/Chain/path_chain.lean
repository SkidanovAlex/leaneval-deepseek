import Mathlib
import Submission.Work.L61.Basic

/-!
# Path chain (helper for Shishikura §6, Lemma 6.1)

Given a continuous path `f : unitInterval → ℂ` whose image stays at distance `≥ δ > 0` from a
set `K`, and a point `t₀` on the path, we cover the path by a finite *chain* of open balls
`B(cen i, rad i)` that

* each avoid `K`,
* intersect consecutively (`B(cen i) ∩ B(cen (i+1)) ≠ ∅`),
* contain `f 0`, `f t₀` and `f 1` (the last two at prescribed indices).

The construction is the obvious one: choose a mesh `1/N` finer than the modulus of uniform
continuity of `f` (Heine–Cantor), take the balls of radius `δ/2` centred at the sample points
`f (i/N)`, and use that consecutive sample points are within `δ/2` of each other.
-/

namespace Work.L61.Chain

theorem path_chain {K : Set ℂ} (f : unitInterval → ℂ) (hf : Continuous f)
    (hsep : ∃ δ > 0, ∀ t y, y ∈ K → δ ≤ dist (f t) y) (t₀ : unitInterval) :
    ∃ (N : ℕ) (cen : Fin (N + 1) → ℂ) (rad : Fin (N + 1) → ℝ) (ib : Fin (N + 1)),
      (∀ i, 0 < rad i) ∧ (∀ i, Disjoint (Metric.ball (cen i) (rad i)) K) ∧
      f 0 ∈ Metric.ball (cen 0) (rad 0) ∧ f t₀ ∈ Metric.ball (cen ib) (rad ib) ∧
      f 1 ∈ Metric.ball (cen (Fin.last N)) (rad (Fin.last N)) ∧
      (∀ i : Fin N, (Metric.ball (cen i.castSucc) (rad i.castSucc) ∩
        Metric.ball (cen i.succ) (rad i.succ)).Nonempty) := by
  obtain ⟨δ, hδpos, hsep⟩ := hsep
  have hδ2pos : 0 < δ / 2 := by linarith
  have hδ2lt : δ / 2 < δ := by linarith
  -- Heine–Cantor: `f` is uniformly continuous on the compact `unitInterval`.
  have huc : UniformContinuous f := CompactSpace.uniformContinuous_of_continuous hf
  rw [Metric.uniformContinuous_iff] at huc
  obtain ⟨η, hηpos, hη⟩ := huc (δ / 2) hδ2pos
  -- a mesh size `1/N < η`
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hηpos
  set N : ℕ := n + 1 with hNdef
  have hNpos : 0 < N := Nat.succ_pos n
  have hNlt : (1:ℝ) / N < η := by rw [hNdef]; push_cast; exact hn
  -- the sample points `i/N` of `unitInterval`
  let u : Fin (N+1) → unitInterval := fun i => ⟨(i:ℝ)/N, by
    rw [Set.mem_Icc]
    exact ⟨by positivity, by
      rw [div_le_one (by exact_mod_cast hNpos : (0:ℝ) < N)]
      exact_mod_cast (Nat.lt_succ_iff.mp i.isLt)⟩⟩
  let t : ℝ := (t₀ : ℝ)
  have ht0 : 0 ≤ t := t₀.2.1
  have ht1 : t ≤ 1 := t₀.2.2
  -- the mesh index `j` with `|t - j/N| < 1/N`
  let j : ℕ := Nat.floor ((N:ℝ) * t)
  have hjle : j ≤ N := by
    have h1 : (j:ℝ) ≤ (N:ℝ) * t := Nat.floor_le (by positivity)
    have h2 : (N:ℝ) * t ≤ (N:ℝ) := by
      simpa using mul_le_mul_of_nonneg_left ht1 (by positivity : (0:ℝ) ≤ (N:ℝ))
    have h3 : (j:ℝ) ≤ (N:ℝ) := le_trans h1 h2
    exact_mod_cast h3
  have hjlower : (j:ℝ)/N ≤ t := by
    have h1 : (j:ℝ) ≤ (N:ℝ) * t := Nat.floor_le (by positivity)
    rw [div_le_iff₀ (by exact_mod_cast hNpos : (0:ℝ) < N)]
    linarith
  have hjupper : t < ((j:ℝ) + 1)/N := by
    have h1 : (N:ℝ) * t < (j:ℝ) + 1 := Nat.lt_floor_add_one ((N:ℝ)*t)
    rw [lt_div_iff₀ (by exact_mod_cast hNpos : (0:ℝ) < N)]
    linarith
  have hdistj : dist t₀ (u ⟨j, Nat.lt_succ_of_le hjle⟩) < η := by
    rw [Subtype.dist_eq, Real.dist_eq]
    have hval : ((u ⟨j, Nat.lt_succ_of_le hjle⟩ : unitInterval) : ℝ) = (j:ℝ)/N := rfl
    rw [hval, abs_lt]
    constructor
    · have hnn : 0 < (1:ℝ)/N := by positivity
      linarith
    · have heq : ((j:ℝ)+1)/N - (j:ℝ)/N = (1:ℝ)/N := by field_simp; ring
      linarith
  refine ⟨N, fun i => f (u i), fun _ => δ/2, ⟨j, Nat.lt_succ_of_le hjle⟩,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; exact hδ2pos
  · -- every ball is at distance `≥ δ > δ/2` from `K`
    intro i
    rw [Set.disjoint_left]
    intro x hx hxK
    rw [Metric.mem_ball] at hx
    have hle : δ ≤ dist (f (u i)) x := hsep (u i) x hxK
    have hle' : δ ≤ dist x (f (u i)) := by rwa [dist_comm] at hle
    linarith
  · rw [Metric.mem_ball]
    have h0 : u 0 = 0 := by apply Subtype.ext; simp [u]
    change dist (f 0) (f (u 0)) < δ / 2
    rw [h0, dist_self]
    exact hδ2pos
  · rw [Metric.mem_ball]
    exact hη hdistj
  · rw [Metric.mem_ball]
    have hl : u (Fin.last N) = 1 := by
      apply Subtype.ext
      simp only [u, Fin.val_last]
      exact div_self (by exact_mod_cast (ne_of_gt hNpos) : ((N:ℕ):ℝ) ≠ 0)
    change dist (f 1) (f (u (Fin.last N))) < δ / 2
    rw [hl, dist_self]
    exact hδ2pos
  · -- consecutive sample points are within `1/N < η`, hence consecutive balls meet
    intro i
    have hstep : dist (u i.succ) (u i.castSucc) < η := by
      rw [Subtype.dist_eq, Real.dist_eq]
      have h1 : ((u i.succ : unitInterval) : ℝ) = ((i:ℝ)+1)/N := by
        show ((i.succ : ℕ) : ℝ)/N = _
        rw [Fin.val_succ]; push_cast; ring
      have h2 : ((u i.castSucc : unitInterval) : ℝ) = (i:ℝ)/N := by
        show ((i.castSucc : ℕ) : ℝ)/N = _
        rw [Fin.val_castSucc]
      rw [h1, h2]
      have heq : ((i:ℝ)+1)/N - (i:ℝ)/N = (1:ℝ)/N := by field_simp; ring
      rw [heq, abs_of_pos (by positivity : (0:ℝ) < (1:ℝ)/N)]
      exact hNlt
    refine ⟨f (u i.succ), ?_, ?_⟩
    · rw [Metric.mem_ball]
      exact hη hstep
    · rw [Metric.mem_ball, dist_self]
      exact hδ2pos

end Work.L61.Chain
