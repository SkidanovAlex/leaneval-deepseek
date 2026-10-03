import Mathlib
import Submission.Work.HornSC.CellBoundaryJordan.grid_tour
import Submission.Work.HornSC.CellBoundaryJordan.grid_tour_basic
import Submission.Work.HornSC.CellBoundaryJordan.grid_tour_range
import Submission.Work.PlanarSC.gridStep_segment_inter

/-!
# The polygonal tour of a simple closed grid walk is a Jordan curve

For a `k`-periodic walk `u` with pairwise distinct vertices `u 0, …, u (k-1)` and unit steps, the
polygonal tour `tourOn u k` is injective on `[0,1]` up to the two endpoints.

For two parameters in `[0,1)` the common point lies on the step edges `(u j_s, u (j_s + 1))` and
`(u j_t, u (j_t + 1))`.  If the steps are the same the affine parametrisation of a nondegenerate
segment is injective; if not, the two unit grid segments meet only in common endpoints
(`Work.PlanarSC.gridStep_segment_inter`), so the common point is a lattice point, which forces the
parameters into the step boundaries `j/k` — and distinctness of the vertices then rules the
configuration out.  The parameter `1` is handled by `tourOn u k 1 = tourOn u k 0`.
-/

namespace Work.HornSC.CellBoundaryJordan

open Set

lemma isUnitAdj_ne {a b : ℤ × ℤ} (h : IsUnitAdj a b) : a ≠ b := by
  intro hab
  subst hab
  rcases h with h | h | h | h
  · exact absurd (congrArg Prod.fst h) (by omega)
  · exact absurd (congrArg Prod.fst h) (by omega)
  · exact absurd (congrArg Prod.snd h) (by omega)
  · exact absurd (congrArg Prod.snd h) (by omega)

lemma lpt_eq_psc (u : ℤ × ℤ) : lpt u = Work.PlanarSC.lpt 0 u := by
  apply Complex.ext <;> simp [lpt, Work.PlanarSC.lpt, Commons.Topology.Plane.gcorner]

lemma isUnitAdj_isUnitSeg {a b : ℤ × ℤ} (h : IsUnitAdj a b) : Work.PlanarSC.IsUnitSeg a b := by
  rcases h with h | h | h | h
  · have hb1 : b.1 = a.1 + 1 := by simpa using congrArg Prod.fst h
    have hb2 : b.2 = a.2 := by simpa using congrArg Prod.snd h
    refine Or.inl (Or.inr ⟨?_, ?_⟩)
    · show a.2 = b.2; omega
    · show a.1 + 1 = b.1; omega
  · have hb1 : b.1 = a.1 - 1 := by simpa using congrArg Prod.fst h
    have hb2 : b.2 = a.2 := by simpa using congrArg Prod.snd h
    refine Or.inr (Or.inr ⟨?_, ?_⟩)
    · show b.2 = a.2; omega
    · show b.1 + 1 = a.1; omega
  · have hb1 : b.1 = a.1 := by simpa using congrArg Prod.fst h
    have hb2 : b.2 = a.2 + 1 := by simpa using congrArg Prod.snd h
    refine Or.inl (Or.inl ⟨?_, ?_⟩)
    · show a.1 = b.1; omega
    · show a.2 + 1 = b.2; omega
  · have hb1 : b.1 = a.1 := by simpa using congrArg Prod.fst h
    have hb2 : b.2 = a.2 - 1 := by simpa using congrArg Prod.snd h
    refine Or.inr (Or.inl ⟨?_, ?_⟩)
    · show b.1 = a.1; omega
    · show b.2 + 1 = a.2; omega

lemma unit_seg_inter {a b a' b' : ℤ × ℤ} (h1 : IsUnitAdj a b) (h2 : IsUnitAdj a' b')
    (hne1 : (a, b) ≠ (a', b')) (hne2 : (a, b) ≠ (b', a')) :
    adjSeg a b ∩ adjSeg a' b' ⊆ ({lpt a, lpt b} : Set ℂ) ∩ ({lpt a', lpt b'} : Set ℂ) := by
  have h := Work.PlanarSC.gridStep_segment_inter (n := 0) (u := a) (v := b) (u' := a')
    (v' := b') (isUnitAdj_isUnitSeg h1) (isUnitAdj_isUnitSeg h2) hne1 hne2
  simpa only [adjSeg, ← lpt_eq_psc] using h

/-- Two points on a nondegenerate segment with equal affine coordinates are equal. -/
lemma smul_right_eq {a b : ℝ} {w : ℂ} (hw : w ≠ 0) (h : a • w = b • w) : a = b := by
  have h2 : (a - b) • w = 0 := by rw [sub_smul, h, sub_self]
  rcases smul_eq_zero.mp h2 with h3 | h3
  · exact sub_eq_zero.mp h3
  · exact absurd h3 hw

lemma edgeIdx_param_nonneg {k : ℕ} {t : ℝ} (h0 : 0 ≤ t) :
    0 ≤ (k : ℝ) * t - (edgeIdx k t : ℝ) := by
  have h := Nat.floor_le (show (0 : ℝ) ≤ (k : ℝ) * t by positivity)
  rw [edgeIdx]
  linarith

lemma edgeIdx_param_lt_one {k : ℕ} {t : ℝ} :
    (k : ℝ) * t - (edgeIdx k t : ℝ) < 1 := by
  have h := Nat.lt_floor_add_one ((k : ℝ) * t)
  rw [edgeIdx]
  linarith

/-- The affine description of the walk at a parameter `t ∈ [0,1)`. -/
lemma tourOn_edge_form {k : ℕ} (hk : 0 < k) (u : ℕ → ℤ × ℤ) {t : ℝ} (h0 : 0 ≤ t) (ht : t < 1) :
    tourOn u k t = lpt (u (edgeIdx k t)) + ((k : ℝ) * t - (edgeIdx k t : ℝ)) •
      (lpt (u (edgeIdx k t + 1)) - lpt (u (edgeIdx k t))) := by
  refine tourOn_affine (edgeIdx_lt hk h0 ht) ?_ ?_
  · linarith [edgeIdx_param_nonneg (k := k) h0]
  · linarith [edgeIdx_param_lt_one (k := k) (t := t)]

theorem tourOn_injective {k : ℕ} (hk : 3 ≤ k) (u : ℕ → ℤ × ℤ)
    (hper : ∀ i, u (i + k) = u i)
    (hinj : ∀ i j, i < k → j < k → u i = u j → i = j)
    (hstep : ∀ i, i < k → IsUnitAdj (u i) (u (i + 1))) :
    ∀ s t : ℝ, 0 ≤ s → s ≤ 1 → 0 ≤ t → t ≤ 1 → tourOn u k s = tourOn u k t →
      s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0) := by
  have hk0 : 0 < k := by omega
  have hper0 : u k = u 0 := by simpa using hper 0
  have hw : ∀ j, j < k → lpt (u (j + 1)) - lpt (u j) ≠ 0 := by
    intro j hj h
    have h' : u j = u (j + 1) := (lpt_injective (sub_eq_zero.mp h).symm)
    exact isUnitAdj_ne (hstep j hj) h'
  -- a pair of consecutive vertices cannot occur in the reverse order
  have hrev : ∀ j i : ℕ, j < k → i < k → (u j, u (j + 1)) ≠ (u (i + 1), u i) := by
    intro j i hj hi h
    have h1 : u j = u (i + 1) := congrArg Prod.fst h
    have h2 : u (j + 1) = u i := congrArg Prod.snd h
    rcases lt_or_eq_of_le (by omega : i + 1 ≤ k) with hlt | heq
    · have hj_eq : j = i + 1 := hinj j (i + 1) hj hlt h1
      rcases lt_or_eq_of_le (by omega : j + 1 ≤ k) with hlt2 | heq2
      · have h4 := hinj (j + 1) i hlt2 hi h2
        omega
      · have h3 : u (j + 1) = u 0 := by rw [heq2, hper0]
        have h4 : i = 0 := hinj i 0 hi (by omega) (by rw [← h2, h3])
        omega
    · have h3 : u j = u 0 := by rw [h1, heq, hper0]
      have hj0 : j = 0 := (hinj 0 j (by omega) hj h3.symm).symm
      rcases lt_or_eq_of_le (by omega : j + 1 ≤ k) with hlt2 | heq2
      · have h4 := hinj (j + 1) i hlt2 hi h2
        omega
      · omega
  have hkne : (k : ℝ) ≠ 0 := by positivity
  -- the core statement: injectivity on `[0,1)`
  have core : ∀ s t : ℝ, 0 ≤ s → s < 1 → 0 ≤ t → t < 1 → tourOn u k s = tourOn u k t → s = t := by
    intro s t hs0 hs1 ht0 ht1 hst
    have hjs : edgeIdx k s < k := edgeIdx_lt hk0 hs0 hs1
    have hjt : edgeIdx k t < k := edgeIdx_lt hk0 ht0 ht1
    have hfs := tourOn_edge_form hk0 u hs0 hs1
    have hft := tourOn_edge_form hk0 u ht0 ht1
    rcases eq_or_ne (edgeIdx k s) (edgeIdx k t) with heq | hne
    · -- the two parameters lie on the same step
      have h2 : ((k : ℝ) * s - (edgeIdx k s : ℝ)) •
          (lpt (u (edgeIdx k s + 1)) - lpt (u (edgeIdx k s))) =
          ((k : ℝ) * t - (edgeIdx k s : ℝ)) •
          (lpt (u (edgeIdx k s + 1)) - lpt (u (edgeIdx k s))) := by
        rw [hfs, hft, ← heq] at hst
        exact add_left_cancel hst
      have heq2 := smul_right_eq (hw (edgeIdx k s) hjs) h2
      have : (k : ℝ) * s = (k : ℝ) * t := by linarith
      exact mul_left_cancel₀ hkne this
    · -- the two parameters lie on different steps: impossible
      exfalso
      have hpair : (u (edgeIdx k s), u (edgeIdx k s + 1)) ≠
          (u (edgeIdx k t), u (edgeIdx k t + 1)) := fun h =>
        hne (hinj _ _ hjs hjt (by simpa using congrArg Prod.fst h))
      have hsub := unit_seg_inter (hstep (edgeIdx k s) hjs) (hstep (edgeIdx k t) hjt)
        hpair (fun h => hrev _ _ hjs hjt h)
      have hpt : lpt (u (edgeIdx k s)) + ((k : ℝ) * s - (edgeIdx k s : ℝ)) •
            (lpt (u (edgeIdx k s + 1)) - lpt (u (edgeIdx k s))) =
          lpt (u (edgeIdx k t)) + ((k : ℝ) * t - (edgeIdx k t : ℝ)) •
            (lpt (u (edgeIdx k t + 1)) - lpt (u (edgeIdx k t))) := by
        rw [← hfs, ← hft]
        exact hst
      have hmemA : (lpt (u (edgeIdx k s)) + ((k : ℝ) * s - (edgeIdx k s : ℝ)) •
            (lpt (u (edgeIdx k s + 1)) - lpt (u (edgeIdx k s)))) ∈
          adjSeg (u (edgeIdx k s)) (u (edgeIdx k s + 1)) := by
        rw [adjSeg, segment_eq_image']
        exact ⟨(k : ℝ) * s - (edgeIdx k s : ℝ),
          ⟨edgeIdx_param_nonneg hs0, le_of_lt edgeIdx_param_lt_one⟩, rfl⟩
      have hmemB : (lpt (u (edgeIdx k t)) + ((k : ℝ) * t - (edgeIdx k t : ℝ)) •
            (lpt (u (edgeIdx k t + 1)) - lpt (u (edgeIdx k t)))) ∈
          adjSeg (u (edgeIdx k t)) (u (edgeIdx k t + 1)) := by
        rw [adjSeg, segment_eq_image']
        exact ⟨(k : ℝ) * t - (edgeIdx k t : ℝ),
          ⟨edgeIdx_param_nonneg ht0, le_of_lt edgeIdx_param_lt_one⟩, rfl⟩
      have hmemB' : (lpt (u (edgeIdx k s)) + ((k : ℝ) * s - (edgeIdx k s : ℝ)) •
            (lpt (u (edgeIdx k s + 1)) - lpt (u (edgeIdx k s)))) ∈
          adjSeg (u (edgeIdx k t)) (u (edgeIdx k t + 1)) := by
        rw [hpt]
        exact hmemB
      have hmem := hsub ⟨hmemA, hmemB'⟩
      have hsubA : (lpt (u (edgeIdx k s)) + ((k : ℝ) * s - (edgeIdx k s : ℝ)) •
            (lpt (u (edgeIdx k s + 1)) - lpt (u (edgeIdx k s)))) ∈
          ({lpt (u (edgeIdx k s)), lpt (u (edgeIdx k s + 1))} : Set ℂ) := hmem.1
      have hsubB : (lpt (u (edgeIdx k s)) + ((k : ℝ) * s - (edgeIdx k s : ℝ)) •
            (lpt (u (edgeIdx k s + 1)) - lpt (u (edgeIdx k s)))) ∈
          ({lpt (u (edgeIdx k t)), lpt (u (edgeIdx k t + 1))} : Set ℂ) := hmem.2
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hsubA hsubB
      rcases hsubA with hA | hA
      · -- the common point is the left endpoint of the first step
        have hlam : (k : ℝ) * s - (edgeIdx k s : ℝ) = 0 := by
          have h3 : ((k : ℝ) * s - (edgeIdx k s : ℝ)) •
              (lpt (u (edgeIdx k s + 1)) - lpt (u (edgeIdx k s))) = 0 := by
            have h2 := congrArg (fun z => z - lpt (u (edgeIdx k s))) hA
            simpa using h2
          rcases smul_eq_zero.mp h3 with h4 | h4
          · exact h4
          · exact absurd h4 (hw _ hjs)
        rcases hsubB with hB | hB
        · have hEq : lpt (u (edgeIdx k s)) = lpt (u (edgeIdx k t)) := by rw [← hA, hB]
          exact hne (hinj _ _ hjs hjt (lpt_injective hEq))
        · have hmu : (k : ℝ) * t - (edgeIdx k t : ℝ) = 1 := by
            have h3 : ((k : ℝ) * t - (edgeIdx k t : ℝ)) •
                (lpt (u (edgeIdx k t + 1)) - lpt (u (edgeIdx k t))) =
                (1 : ℝ) • (lpt (u (edgeIdx k t + 1)) - lpt (u (edgeIdx k t))) := by
              rw [one_smul]
              have h4 : lpt (u (edgeIdx k t)) + ((k : ℝ) * t - (edgeIdx k t : ℝ)) •
                  (lpt (u (edgeIdx k t + 1)) - lpt (u (edgeIdx k t))) =
                  lpt (u (edgeIdx k t + 1)) := by
                calc lpt (u (edgeIdx k t)) + ((k : ℝ) * t - (edgeIdx k t : ℝ)) •
                      (lpt (u (edgeIdx k t + 1)) - lpt (u (edgeIdx k t)))
                    = lpt (u (edgeIdx k s)) + ((k : ℝ) * s - (edgeIdx k s : ℝ)) •
                      (lpt (u (edgeIdx k s + 1)) - lpt (u (edgeIdx k s))) := hpt.symm
                  _ = lpt (u (edgeIdx k t + 1)) := hB
              have h5 := congrArg (fun z => z - lpt (u (edgeIdx k t))) h4
              simpa using h5
            exact smul_right_eq (hw _ hjt) h3
          have hlt := edgeIdx_param_lt_one (k := k) (t := t)
          rw [hmu] at hlt
          exact absurd hlt (by norm_num)
      · -- the common point is the right endpoint of the first step
        have hlam : (k : ℝ) * s - (edgeIdx k s : ℝ) = 1 := by
          have h3 : ((k : ℝ) * s - (edgeIdx k s : ℝ)) •
              (lpt (u (edgeIdx k s + 1)) - lpt (u (edgeIdx k s))) =
              (1 : ℝ) • (lpt (u (edgeIdx k s + 1)) - lpt (u (edgeIdx k s))) := by
            rw [one_smul]
            have h2 := congrArg (fun z => z - lpt (u (edgeIdx k s))) hA
            simpa using h2
          exact smul_right_eq (hw _ hjs) h3
        have hlt := edgeIdx_param_lt_one (k := k) (t := s)
        rw [hlam] at hlt
        exact absurd hlt (by norm_num)
  intro s t hs0 hs1 ht0 ht1 hst
  rcases eq_or_lt_of_le hs1 with hs | hs
  · rcases eq_or_lt_of_le ht1 with ht | ht
    · exact Or.inl (hs.trans ht.symm)
    · have h0 : tourOn u k t = tourOn u k 0 := by
        rw [← hst, hs, tourOn_one, hper0, ← tourOn_zero]
      have := core t 0 ht0 ht (le_refl 0) (by norm_num) h0
      exact Or.inr (Or.inr ⟨hs, this⟩)
  · rcases eq_or_lt_of_le ht1 with ht | ht
    · have h0 : tourOn u k s = tourOn u k 0 := by
        rw [hst, ht, tourOn_one, hper0, ← tourOn_zero]
      have := core s 0 hs0 hs (le_refl 0) (by norm_num) h0
      exact Or.inr (Or.inl ⟨this, ht⟩)
    · exact Or.inl (core s t hs0 hs ht0 ht hst)

end Work.HornSC.CellBoundaryJordan
