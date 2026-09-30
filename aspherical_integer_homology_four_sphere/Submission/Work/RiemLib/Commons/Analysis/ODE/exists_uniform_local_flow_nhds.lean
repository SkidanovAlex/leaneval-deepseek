import Mathlib
import Submission.Work.RiemLib.Commons.Analysis.ODE.uniform_local_solution_closedBall
import Submission.Work.RiemLib.Commons.Analysis.ODE.uniform_flow_compact_open

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Commons.Analysis.ODE

open Set Filter Metric
open scoped Topology ContDiff

theorem exists_uniform_local_flow_nhds
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {F : E → E} {W : Set E} (hW : IsOpen W)
    (hFW : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F W)
    {K : Set E} (hK : IsCompact K) (hKW : K ⊆ W) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ O : Set E, IsOpen O ∧ K ⊆ O ∧ O ⊆ W ∧ ∃ α : E → ℝ → E,
      (∀ p ∈ O, α p 0 = p) ∧
      (∀ p ∈ O, ∀ t : ℝ, |t| ≤ ρ → HasDerivAt (α p) (F (α p t)) t) ∧
      (∀ p ∈ O, ∀ t : ℝ, |t| ≤ ρ → α p t ∈ W) ∧
      (∀ p ∈ O, ∀ β : ℝ → E, (∀ t : ℝ, |t| ≤ ρ → HasDerivAt β (F (β t)) t) → β 0 = p →
          ∀ t : ℝ, |t| ≤ ρ → β t = α p t) := by
  classical
  rcases Set.eq_empty_or_nonempty K with hKe | hKne
  · refine ⟨1, one_pos, ∅, isOpen_empty, ?_, ?_, (fun p _ => p), ?_, ?_, ?_, ?_⟩ <;> simp [hKe]
  -- Per-point local data: a ball inside `W` on which `F` is Lipschitz.
  have hpt : ∀ x : K, ∃ rx > (0:ℝ), ∃ Lx : NNReal,
      closedBall (x:E) rx ⊆ W ∧ LipschitzOnWith Lx F (closedBall (x:E) rx) := by
    intro x
    have hxW : (x:E) ∈ W := hKW x.2
    have hC1 : ContDiffAt ℝ (1 : WithTop ℕ∞) F (x:E) :=
      (hFW.contDiffAt (hW.mem_nhds hxW)).of_le (by norm_num)
    obtain ⟨Lx, U, hU, hLipU⟩ := hC1.exists_lipschitzOnWith
    have hUW : U ∩ W ∈ 𝓝 (x:E) := Filter.inter_mem hU (hW.mem_nhds hxW)
    obtain ⟨ε, hεpos, hεsub⟩ := Metric.mem_nhds_iff.mp hUW
    refine ⟨ε/2, half_pos hεpos, Lx, ?_, ?_⟩
    · intro y hy
      have hy' : y ∈ ball (x:E) ε := by
        rw [mem_ball]; rw [mem_closedBall] at hy; linarith
      exact (hεsub hy').2
    · refine hLipU.mono ?_
      intro y hy
      have hy' : y ∈ ball (x:E) ε := by
        rw [mem_ball]; rw [mem_closedBall] at hy; linarith
      exact (hεsub hy').1
  choose rx hrxpos Lx hbody using hpt
  -- Finite subcover of `K` by halves of these balls.
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x : K => ball (x:E) (rx x / 2))
      (fun _ => isOpen_ball)
      (fun y hy => mem_iUnion.mpr ⟨⟨y, hy⟩, mem_ball_self (half_pos (hrxpos ⟨y, hy⟩))⟩)
  have htne : t.Nonempty := by
    obtain ⟨y, hy⟩ := hKne
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    have hmem := ht hy
    rw [hemp] at hmem
    simp at hmem
  -- Uniform local existence for each centre.
  have hsol : ∀ i : K, ∃ ρi > (0:ℝ), ρi ≤ rx i ∧
      ∀ p ∈ closedBall (i:E) (rx i / 2),
        ∃ β : ℝ → E, β 0 = p ∧
          (∀ t ∈ Ioo (-ρi) ρi, HasDerivAt β (F (β t)) t) ∧
          (∀ t ∈ Ioo (-ρi) ρi, β t ∈ closedBall (i:E) (rx i)) := by
    intro i
    have hMnn : 0 ≤ ‖F (i:E)‖ + (Lx i : ℝ) * rx i :=
      add_nonneg (norm_nonneg _) (mul_nonneg (by positivity) (le_of_lt (hrxpos i)))
    have hb : ∀ y ∈ closedBall (i:E) (rx i), ‖F y‖ ≤ ‖F (i:E)‖ + (Lx i : ℝ) * rx i := by
      intro y hy
      have hd : dist (F y) (F (i:E)) ≤ (Lx i : ℝ) * dist y (i:E) :=
        (hbody i).2.dist_le_mul y hy (i:E) (mem_closedBall_self (le_of_lt (hrxpos i)))
      have hdist : dist y (i:E) ≤ rx i := mem_closedBall.mp hy
      have hle1 : ‖F y - F (i:E)‖ ≤ (Lx i : ℝ) * rx i := by
        rw [← dist_eq_norm]
        exact le_trans hd (mul_le_mul_of_nonneg_left hdist (by positivity))
      calc ‖F y‖ = ‖(F y - F (i:E)) + F (i:E)‖ := by rw [sub_add_cancel]
        _ ≤ ‖F y - F (i:E)‖ + ‖F (i:E)‖ := norm_add_le _ _
        _ ≤ (Lx i : ℝ) * rx i + ‖F (i:E)‖ := by linarith
        _ = ‖F (i:E)‖ + (Lx i : ℝ) * rx i := by ring
    exact uniform_local_solution_closedBall (F := F) (z₀ := (i:E)) (R := rx i)
      (hrxpos i) (L := Lx i) hMnn (hbody i).2 hb
  choose ρ₀ hρ0pos hρ0le hβ using hsol
  let ρ : ℝ := t.inf' htne ρ₀
  have hρpos : 0 < ρ := (Finset.lt_inf'_iff htne).mpr (fun i _ => hρ0pos i)
  have hρle : ∀ i ∈ t, ρ ≤ ρ₀ i := fun i hi => Finset.inf'_le ρ₀ hi
  let sol : K → E → ℝ → E := fun i q =>
    if h : q ∈ closedBall (i:E) (rx i / 2) then (Classical.choose (hβ i q h)) else fun _ => q
  have sol_mem : ∀ (i : K) (q : E) (h : q ∈ closedBall (i:E) (rx i / 2)),
      sol i q = Classical.choose (hβ i q h) := by
    intro i q h
    dsimp only [sol]
    rw [dif_pos h]
  have sol_apply0 : ∀ (i : K) (q : E) (h : q ∈ closedBall (i:E) (rx i / 2)),
      sol i q 0 = q := by
    intro i q h
    rw [sol_mem i q h]
    exact (Classical.choose_spec (hβ i q h)).1
  have sol_deriv : ∀ (i : K) (q : E) (h : q ∈ closedBall (i:E) (rx i / 2)),
      ∀ t ∈ Ioo (-(ρ₀ i)) (ρ₀ i), HasDerivAt (sol i q) (F (sol i q t)) t := by
    intro i q h t ht
    rw [sol_mem i q h]
    exact (Classical.choose_spec (hβ i q h)).2.1 t ht
  have sol_W : ∀ (i : K) (q : E) (h : q ∈ closedBall (i:E) (rx i / 2)),
      ∀ t ∈ Ioo (-(ρ₀ i)) (ρ₀ i), sol i q t ∈ W := by
    intro i q h t ht
    rw [sol_mem i q h]
    exact (hbody i).1 ((Classical.choose_spec (hβ i q h)).2.2 t ht)
  obtain ⟨p₀, hp₀⟩ := htne
  let idx : E → K := fun q => if h : ∃ i ∈ t, q ∈ ball (i:E) (rx i / 2) then h.choose else p₀
  have hidx_spec : ∀ q (h : ∃ i ∈ t, q ∈ ball (i:E) (rx i / 2)),
      idx q ∈ t ∧ q ∈ ball ((idx q : K) : E) (rx (idx q) / 2) := by
    intro q h
    have hh : idx q = h.choose := by dsimp only [idx]; rw [dif_pos h]
    rw [hh]
    exact h.choose_spec
  let O : Set E := ⋃ i ∈ t, ball (i:E) (rx i / 2)
  have hOeq : O = ⋃ i ∈ t, ball (i:E) (rx i / 2) := rfl
  have key : ∀ p ∈ O, (idx p) ∈ t ∧ p ∈ closedBall ((idx p : K) : E) (rx (idx p) / 2) := by
    intro p hp
    rw [hOeq] at hp
    obtain ⟨i, hit, hpi⟩ := mem_iUnion₂.mp hp
    exact ⟨(hidx_spec p ⟨i, hit, hpi⟩).1, ball_subset_closedBall (hidx_spec p ⟨i, hit, hpi⟩).2⟩
  let α : E → ℝ → E := fun q t => sol (idx q) q t
  have habs : ∀ p ∈ O, ∀ t : ℝ, |t| ≤ ρ/2 → |t| < ρ₀ (idx p) := by
    intro p hp t ht
    obtain ⟨hit, -⟩ := key p hp
    have h2 : ρ/2 < ρ₀ (idx p) := lt_of_lt_of_le (by linarith [hρpos]) (hρle (idx p) hit)
    linarith
  have hα0 : ∀ p ∈ O, α p 0 = p := by
    intro p hp
    obtain ⟨hit, hpcl⟩ := key p hp
    change sol (idx p) p 0 = p
    exact sol_apply0 (idx p) p hpcl
  have hαode : ∀ p ∈ O, ∀ t : ℝ, |t| ≤ ρ/2 → HasDerivAt (α p) (F (α p t)) t := by
    intro p hp t ht
    obtain ⟨hit, hpcl⟩ := key p hp
    change HasDerivAt (sol (idx p) p) (F (sol (idx p) p t)) t
    exact sol_deriv (idx p) p hpcl t (abs_lt.mp (habs p hp t ht))
  have hαmem : ∀ p ∈ O, ∀ t : ℝ, |t| ≤ ρ/2 → α p t ∈ W := by
    intro p hp t ht
    obtain ⟨hit, hpcl⟩ := key p hp
    change sol (idx p) p t ∈ W
    exact sol_W (idx p) p hpcl t (abs_lt.mp (habs p hp t ht))
  have hαuniq : ∀ p ∈ O, ∀ β : ℝ → E,
      (∀ t : ℝ, |t| ≤ ρ/2 → HasDerivAt β (F (β t)) t) → β 0 = p →
      ∀ t : ℝ, |t| ≤ ρ/2 → β t = α p t := by
    intro p hp β hβ hβ0 t ht
    have htIcc : t ∈ Icc (-(ρ/2)) (ρ/2) := by rw [abs_le] at ht; exact ⟨ht.1, ht.2⟩
    have hαd : ∀ s ∈ Icc (-(ρ/2)) (ρ/2), HasDerivAt (α p) (F (α p s)) s := by
      intro s hs
      exact hαode p hp s (by rw [abs_le]; exact ⟨hs.1, hs.2⟩)
    have hβd : ∀ s ∈ Icc (-(ρ/2)) (ρ/2), HasDerivAt β (F (β s)) s := by
      intro s hs
      exact hβ s (by rw [abs_le]; exact ⟨hs.1, hs.2⟩)
    have hmem : ∀ s ∈ Icc (-(ρ/2)) (ρ/2), α p s ∈ W := by
      intro s hs
      exact hαmem p hp s (by rw [abs_le]; exact ⟨hs.1, hs.2⟩)
    have h0 : α p 0 = β 0 := by rw [hα0 p hp, hβ0]
    have heq := ufco_eqOn_of_hasDerivAt hW hFW (u := α p) (v := β)
      (a := -(ρ/2)) (b := ρ/2) (t₀ := 0) (by linarith) (by linarith) hαd hβd hmem h0
    exact (heq htIcc).symm
  refine ⟨ρ/2, by linarith, O, ?_, ?_, ?_, α, hα0, hαode, hαmem, hαuniq⟩
  · rw [hOeq]; exact isOpen_biUnion (fun i _ => isOpen_ball)
  · intro p hp; rw [hOeq]; exact ht hp
  · intro p hp
    rw [hOeq] at hp
    obtain ⟨i, hit, hpi⟩ := mem_iUnion₂.mp hp
    exact (hbody i).1 (closedBall_subset_closedBall (by linarith [hrxpos i]) (ball_subset_closedBall hpi))

end Commons.Analysis.ODE
