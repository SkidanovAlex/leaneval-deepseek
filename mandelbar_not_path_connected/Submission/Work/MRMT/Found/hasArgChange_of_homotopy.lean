import Mathlib
import Submission.Work.MRMT.QC.plane_surjective

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Found

open Set

/-- The argument change (winding number) of a closed loop is invariant under homotopy through
non-vanishing loops: if `H` is a homotopy `[a,b] × [0,1] → ℂ` consisting of loops avoiding `0`,
then the argument change of the loop at `a` and at `b` agree. -/
theorem hasArgChange_of_homotopy {H : ℝ → ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn (fun p : ℝ × ℝ => H p.1 p.2) (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1))
    (hloop : ∀ s ∈ Set.Icc a b, H s 1 = H s 0)
    (hne : ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc (0 : ℝ) 1, H s t ≠ 0)
    {k : ℤ} (h : Work.MRMT.QC.HasArgChange (fun t : ℝ => H a t) k) :
    Work.MRMT.QC.HasArgChange (fun t : ℝ => H b t) k := by
  have hKcomp : IsCompact (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1) :=
    isCompact_Icc.prod isCompact_Icc
  have hKne : (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1).Nonempty :=
    Set.Nonempty.prod (Set.nonempty_Icc.mpr hab) (Set.nonempty_Icc.mpr zero_le_one)
  -- the loop `H s ·` stays a fixed positive distance `m` away from `0`
  obtain ⟨p₀, hp₀, hp₀min⟩ :=
    hKcomp.exists_isMinOn hKne (continuous_norm.comp_continuousOn hcont)
  set m : ℝ := ‖H p₀.1 p₀.2‖ with hm
  have hmpos : 0 < m := by
    rw [hm]; exact norm_pos_iff.mpr (hne p₀.1 hp₀.1 p₀.2 hp₀.2)
  have hle : ∀ p ∈ Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1, m ≤ ‖H p.1 p.2‖ := by
    intro p hp; rw [hm]; exact hp₀min hp
  -- uniform continuity on the compact rectangle
  obtain ⟨δ, hδpos, hδ⟩ := (Metric.uniformContinuousOn_iff.mp
    (hKcomp.uniformContinuousOn_of_continuous hcont)) m hmpos
  -- locally, the argument change is constant
  have hloc : ∀ s ∈ Set.Icc a b, ∀ s' ∈ Set.Icc a b, dist s s' < δ →
      (Work.MRMT.QC.HasArgChange (fun t : ℝ => H s t) k ↔
        Work.MRMT.QC.HasArgChange (fun t : ℝ => H s' t) k) := by
    intro s hs s' hs' hss'
    have hcs : ContinuousOn (fun t : ℝ => H s t) (Set.Icc (0 : ℝ) 1) :=
      hcont.comp ((continuous_const.prodMk continuous_id).continuousOn)
        (by intro t ht; exact Set.mem_prod.mpr ⟨hs, ht⟩)
    have hcs' : ContinuousOn (fun t : ℝ => H s' t) (Set.Icc (0 : ℝ) 1) :=
      hcont.comp ((continuous_const.prodMk continuous_id).continuousOn)
        (by intro t ht; exact Set.mem_prod.mpr ⟨hs', ht⟩)
    have key : ∀ t ∈ Set.Icc (0 : ℝ) 1, dist (H s t) (H s' t) < m := by
      intro t ht
      have h1 : dist ((s, t) : ℝ × ℝ) (s', t) < δ := by
        have h2 : dist ((s, t) : ℝ × ℝ) (s', t) = dist s s' := by
          rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg]
        rw [h2]; exact hss'
      exact hδ (s, t) ⟨hs, ht⟩ (s', t) ⟨hs', ht⟩ h1
    refine ⟨fun hh => ?_, fun hh => ?_⟩
    · refine Work.MRMT.QC.hasArgChange_of_close hh (hloop s hs) (hloop s' hs') hcs hcs' ?_
      intro t ht
      have h4 : m ≤ ‖H s t‖ := hle (s, t) ⟨hs, ht⟩
      calc ‖H s' t - H s t‖ = dist (H s' t) (H s t) := (Complex.dist_eq _ _).symm
        _ = dist (H s t) (H s' t) := dist_comm _ _
        _ < m := key t ht
        _ ≤ ‖H s t‖ := h4
    · refine Work.MRMT.QC.hasArgChange_of_close hh (hloop s' hs') (hloop s hs) hcs' hcs ?_
      intro t ht
      have h4 : m ≤ ‖H s' t‖ := hle (s', t) ⟨hs', ht⟩
      calc ‖H s t - H s' t‖ = dist (H s t) (H s' t) := (Complex.dist_eq _ _).symm
        _ < m := key t ht
        _ ≤ ‖H s' t‖ := h4
  -- the set of parameters with the given argument change is open and closed in `[a,b]`
  let A : Set ℝ :=
    {s : ℝ | s ∈ Set.Icc a b ∧ Work.MRMT.QC.HasArgChange (fun t : ℝ => H s t) k}
  let u : Set ℝ := ⋃ s ∈ A, Metric.ball s (δ / 2)
  have hu_open : IsOpen u := isOpen_biUnion (fun i _ => Metric.isOpen_ball)
  have ha_u : a ∈ u := by
    change a ∈ ⋃ s ∈ A, Metric.ball s (δ / 2)
    rw [Set.mem_iUnion₂]
    exact ⟨a, ⟨⟨le_rfl, hab⟩, h⟩, Metric.mem_ball_self (half_pos hδpos)⟩
  have hclos : closure u ∩ Set.Icc a b ⊆ u := by
    intro y hy
    obtain ⟨hycl, hyI⟩ := hy
    obtain ⟨z, hzu, hzy⟩ := Metric.mem_closure_iff.mp hycl (δ / 2) (half_pos hδpos)
    change z ∈ ⋃ s ∈ A, Metric.ball s (δ / 2) at hzu
    rw [Set.mem_iUnion₂] at hzu
    obtain ⟨s, hsA, hzs⟩ := hzu
    have hsP : Work.MRMT.QC.HasArgChange (fun t : ℝ => H s t) k := hsA.2
    have hds : dist s y < δ := by
      have h1 : dist z s < δ / 2 := Metric.mem_ball.mp hzs
      have h2 : dist s z < δ / 2 := by rw [dist_comm]; exact h1
      have h3 : dist z y < δ / 2 := by rw [dist_comm]; exact hzy
      linarith [dist_triangle s z y]
    have hyP : Work.MRMT.QC.HasArgChange (fun t : ℝ => H y t) k :=
      (hloc s hsA.1 y hyI hds).mp hsP
    change y ∈ ⋃ s ∈ A, Metric.ball s (δ / 2)
    rw [Set.mem_iUnion₂]
    exact ⟨y, ⟨⟨hyI, hyP⟩, Metric.mem_ball_self (half_pos hδpos)⟩⟩
  have hne_inter : (Set.Icc a b ∩ u).Nonempty := ⟨a, ⟨⟨le_rfl, hab⟩, ha_u⟩⟩
  have hsub : Set.Icc a b ⊆ u :=
    isPreconnected_Icc.subset_of_closure_inter_subset hu_open hne_inter hclos
  have hb_u : b ∈ u := hsub ⟨hab, le_rfl⟩
  change b ∈ ⋃ s ∈ A, Metric.ball s (δ / 2) at hb_u
  rw [Set.mem_iUnion₂] at hb_u
  obtain ⟨s, hsA, hbs⟩ := hb_u
  exact (hloc s hsA.1 b ⟨hab, le_rfl⟩ (by
    have h1 : dist b s < δ / 2 := Metric.mem_ball.mp hbs
    have h2 : dist s b < δ / 2 := by rw [dist_comm]; exact h1
    linarith)).mp hsA.2

end Work.MRMT.Found
