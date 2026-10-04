import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.flat

open Metric Set

/-- **Uniform local existence time.**  If `F` is locally Lipschitz on a compact set `Kc`, then there
is `ρ > 0` such that every `p ∈ Kc` admits an integral curve `β` of `F` with `β 0 = p` defined on
the whole interval `[-ρ, ρ]` (with a two-sided derivative at every point of that interval).

This is the standard compactness upgrade of the Picard–Lindelöf (Cauchy–Lipschitz) theorem: the
local Lipschitz radius and constant supplied by the hypothesis vary from point to point, but on a
compact set they can be made uniform.  Concretely, cover `Kc` by finitely many balls of half the
local Lipschitz radius; the minimum of these radii, the maximum of the local sup-norms of `F` and
the maximum of the Lipschitz constants are then uniform, so the Picard–Lindelöf existence time is
uniform too.  The solution produced by Picard–Lindelöf is only a `HasDerivWithinAt` solution on the
closed interval of existence; shrinking the time by a factor `2` makes that interval a neighbourhood
of every point with `|t| ≤ ε / 2`, which yields the two-sided `HasDerivAt` statement. -/
theorem exists_uniform_local_solution
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {F : E → E} {Kc : Set E} (hKc : IsCompact Kc)
    (hloc : ∀ p ∈ Kc, ∃ L : NNReal, ∃ r : ℝ, 0 < r ∧
      LipschitzOnWith L F (Metric.closedBall p r)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ p ∈ Kc, ∃ β : ℝ → E,
      β 0 = p ∧ ∀ t : ℝ, |t| ≤ ρ → HasDerivAt β (F (β t)) t := by
  classical
  by_cases hne : Kc.Nonempty
  · -- local data at every point of `Kc`
    choose L r hr hlip using fun (p : Kc) => hloc p.1 p.2
    -- a finite cover of `Kc` by balls of half the local Lipschitz radius
    have hcover : Kc ⊆ ⋃ i : Kc, ball i.1 (r i / 2) := fun x hx =>
      mem_iUnion.2 ⟨⟨x, hx⟩, by rw [Metric.mem_ball, dist_self]; linarith [hr ⟨x, hx⟩]⟩
    obtain ⟨t, ht⟩ := hKc.elim_finite_subcover (fun i : Kc => ball i.1 (r i / 2))
      (fun _ => isOpen_ball) hcover
    have htne : t.Nonempty := by
      obtain ⟨x, hx⟩ := hne
      rcases mem_iUnion.1 (ht hx) with ⟨i, hi⟩
      rcases mem_iUnion.1 hi with ⟨hit, -⟩
      exact ⟨i, hit⟩
    -- uniform radius, uniform norm bound, uniform existence time
    let R : ℝ := t.inf' htne (fun i : Kc => r i / 2)
    let M : ℝ := t.sup' htne (fun i : Kc => ‖F i.1‖ + (L i : ℝ) * r i)
    let ε : ℝ := R / (2 * (M + 1))
    have hRpos : 0 < R := by
      dsimp only [R]
      rw [Finset.lt_inf'_iff]
      intro i _
      linarith [hr i]
    have hMnn : 0 ≤ M := by
      obtain ⟨i, hi⟩ := htne
      have h := Finset.le_sup' (fun i : Kc => ‖F i.1‖ + (L i : ℝ) * r i) hi
      dsimp only [M]
      exact le_trans (add_nonneg (norm_nonneg _) (mul_nonneg (L i).2 (hr i).le)) h
    have hεpos : 0 < ε := by
      dsimp only [ε]
      exact div_pos hRpos (by linarith)
    have hMe : M * ε ≤ R / 2 := by
      have h1 : M / (2 * (M + 1)) ≤ 1 / 2 := by
        rw [div_le_iff₀ (by linarith : (0 : ℝ) < 2 * (M + 1))]
        linarith
      dsimp only [ε]
      calc M * (R / (2 * (M + 1))) = R * (M / (2 * (M + 1))) := by ring
        _ ≤ R * (1 / 2) := mul_le_mul_of_nonneg_left h1 (le_of_lt hRpos)
        _ = R / 2 := by ring
    refine ⟨ε / 2, half_pos hεpos, fun p hp => ?_⟩
    rcases mem_iUnion.1 (ht hp) with ⟨i, hi⟩
    rcases mem_iUnion.1 hi with ⟨hit, hball⟩
    have hdist : dist p i.1 < r i / 2 := Metric.mem_ball.1 hball
    have hRle : R ≤ r i / 2 := by
      dsimp only [R]
      exact Finset.inf'_le (fun i : Kc => r i / 2) hit
    have hMge : ‖F i.1‖ + (L i : ℝ) * r i ≤ M := by
      dsimp only [M]
      exact Finset.le_sup' (fun i : Kc => ‖F i.1‖ + (L i : ℝ) * r i) hit
    -- the ball of radius `R` around `p` is contained in the ball of radius `r i` around `i`
    have hsubset : closedBall p R ⊆ closedBall i.1 (r i) := by
      intro x hx
      rw [Metric.mem_closedBall] at hx ⊢
      linarith [dist_triangle x p i.1]
    have hlip' : LipschitzOnWith (L i) F (closedBall p R) := (hlip i).mono hsubset
    have hb : ∀ x ∈ closedBall p R, ‖F x‖ ≤ M := by
      intro x hx
      have hxs : x ∈ closedBall i.1 (r i) := hsubset hx
      have hxi : dist x i.1 ≤ r i := Metric.mem_closedBall.1 hxs
      have hi_in : i.1 ∈ closedBall i.1 (r i) := by
        rw [Metric.mem_closedBall, dist_self]
        linarith [hr i]
      have hd := (hlip i).dist_le_mul x hxs i.1 hi_in
      have h1 : ‖F x‖ ≤ ‖F x - F i.1‖ + ‖F i.1‖ := by
        have h2 := norm_add_le (F x - F i.1) (F i.1)
        rwa [sub_add_cancel] at h2
      calc ‖F x‖ ≤ ‖F x - F i.1‖ + ‖F i.1‖ := h1
        _ = ‖F i.1‖ + dist (F x) (F i.1) := by rw [dist_eq_norm]; ring
        _ ≤ ‖F i.1‖ + (L i : ℝ) * dist x i.1 := add_le_add (le_refl _) hd
        _ ≤ ‖F i.1‖ + (L i : ℝ) * r i :=
            add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hxi (L i).2)
        _ ≤ M := hMge
    -- Picard–Lindelöf on the symmetric interval `[-ε, ε]` around `0`, with initial value `p`
    have hPL : IsPicardLindelof (fun _ : ℝ => F) (tmin := -ε) (tmax := ε)
        ⟨0, by rw [mem_Icc]; exact ⟨by linarith, by linarith⟩⟩ p
        (⟨R, le_of_lt hRpos⟩ : NNReal) 0 (⟨M, hMnn⟩ : NNReal) (L i) := by
      apply IsPicardLindelof.of_time_independent (f := F) (x₀ := p)
        (a := (⟨R, le_of_lt hRpos⟩ : NNReal)) (r := 0) (L := (⟨M, hMnn⟩ : NNReal)) (K := L i)
      · exact hb
      · exact hlip'
      · show M * max (ε - 0) (0 - (-ε)) ≤ R - 0
        simp only [sub_zero, zero_sub, neg_neg, max_self]
        linarith
    obtain ⟨α, hα0, hα⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
    refine ⟨α, by simpa using hα0, fun s hs => ?_⟩
    have hs1 : -ε < s := by
      have := abs_le.1 hs
      linarith
    have hs2 : s < ε := by
      have := abs_le.1 hs
      linarith
    exact (hα s ⟨hs1.le, hs2.le⟩).hasDerivAt (Icc_mem_nhds hs1 hs2)
  · -- empty case: the statement is vacuous
    exact ⟨1, one_pos, fun p hp => (hne ⟨p, hp⟩).elim⟩

end Work.Diff.STE.flat
