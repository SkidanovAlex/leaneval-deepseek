import Mathlib
import Submission.Work.Whitney.ArcFraming
import Submission.Work.Whitney.PosTransitionAtAlg
import Submission.Work.Whitney.ArcChainOn
import Submission.Work.Whitney.posTransitionAt_slide

/-!
# The transition sign along an arc is well defined

Two chains of charts along the same continuous arc `γ` from `γ 0` to `γ 1` compare the charts at
the two ends: if the *end* charts are positively related at `γ 1`, then the *start* charts are
positively related at `γ 0`.  This is the statement that the sign of the transition between two
trivialisations is transported along the arc, and it is what makes the "framing of a bigon"
comparison (`Work.Whitney.OppositeType`) independent of the chosen chains
(`Work.Whitney.IsArcChain`).

The proof is an induction on the total number of junctions.  At each step the chain whose first
junction is earlier is cut down (the tail `Work.Whitney.chainData_tail`, or the restriction
`Work.Whitney.chainData_restrictStart`), the base point is slid to the junction
(`Work.Whitney.posTransitionAt_slide`) and the resulting positive transition is cancelled
(`Work.Whitney.posTransitionAt_trans_iff`).
-/

namespace Work.Whitney

open scoped Manifold ContDiff
open Topology Filter

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]

theorem chainData_transport_aux : ∀ K : ℕ, ∀ (N P : ℕ) (hN : 0 < N) (hP : 0 < P)
    (γ : ℝ → M) (hγ : Continuous γ) (a b : ℝ)
    (c d c' d' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (dd : Fin (N + 1) → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) (t : Fin (N + 1) → ℝ)
    (ff : Fin (P + 1) → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) (s : Fin (P + 1) → ℝ),
    N + P ≤ K → Work.Whitney.ChainData γ a b c d N dd t →
      Work.Whitney.ChainData γ a b c' d' P ff s →
      (Work.Whitney.PosTransitionAt c c' (γ a) ↔ Work.Whitney.PosTransitionAt d d' (γ b)) := by
  intro K₀
  induction K₀ with
  | zero =>
    intro N P hN hP γ hγ a b c d c' d' dd t ff s hle
    omega
  | succ K ih =>
    intro N P hN hP γ hγ a b c d c' d' dd t ff s hle h1 h2
    obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega⟩
    obtain ⟨m, rfl⟩ : ∃ m, P = m + 1 := ⟨P - 1, by omega⟩
    have h1c := h1
    have h2c := h2
    obtain ⟨ht0, htb, htmono, hdd0, hddN, hγa, hγb, hsm, hcov, hjunc⟩ := h1
    obtain ⟨hs0, hsb, hsmono, hff0, hffM, hγa', hγb', hsm', hcov', hjunc'⟩ := h2
    subst hdd0
    subst hddN
    subst hff0
    subst hffM
    -- the two reduction steps
    have hsucc_le_last : ∀ (n : ℕ), (Fin.succ (0 : Fin (n+1)) : Fin (n+1+1)) ≤ Fin.last (n+1) := by
      intro n
      rw [Fin.le_iff_val_le_val]
      simp
    have reduceN : 0 < k → t (Fin.succ (0 : Fin (k+1))) ≤ s (Fin.succ (0 : Fin (m+1))) →
        (Work.Whitney.PosTransitionAt (dd 0) (ff 0) (γ a) ↔
          Work.Whitney.PosTransitionAt (dd (Fin.last (k+1))) (ff (Fin.last (m+1))) (γ b)) := by
      intro hk hle1
      have hab1 : a ≤ t (Fin.succ (0 : Fin (k+1))) := by
        rw [← ht0]
        exact htmono (by simp)
      have hcov_c : γ '' Set.Icc a (t (Fin.succ (0 : Fin (k+1)))) ⊆ (dd 0).source := by
        have h := hcov (0 : Fin (k+1))
        rw [Fin.castSucc_zero, ht0] at h
        exact h
      have hcov_c' : γ '' Set.Icc a (s (Fin.succ (0 : Fin (m+1)))) ⊆ (ff 0).source := by
        have h := hcov' (0 : Fin (m+1))
        rw [Fin.castSucc_zero, hs0] at h
        exact h
      have hslide1 : Work.Whitney.PosTransitionAt (dd 0) (ff 0) (γ a) ↔
          Work.Whitney.PosTransitionAt (dd 0) (ff 0) (γ (t (Fin.succ (0 : Fin (k+1))))) :=
        Work.Whitney.posTransitionAt_slide (hsm 0) (hsm' 0) hγ hab1
          (fun x hx => ⟨hcov_c hx,
            hcov_c' (Set.image_mono (Set.Icc_subset_Icc le_rfl hle1) hx)⟩)
      have htd1 : Work.Whitney.PosTransitionAt (dd 0) (dd (Fin.succ (0 : Fin (k+1))))
          (γ (t (Fin.succ (0 : Fin (k+1))))) := by
        have h := (hjunc (0 : Fin (k+1))).2
        rw [Fin.castSucc_zero] at h
        exact h
      have hsrc1 : γ (t (Fin.succ (0 : Fin (k+1)))) ∈ (dd 0).source :=
        hcov_c ⟨t (Fin.succ (0 : Fin (k+1))), ⟨hab1, le_rfl⟩, rfl⟩
      have hsrc2 : γ (t (Fin.succ (0 : Fin (k+1)))) ∈ (dd (Fin.succ (0 : Fin (k+1)))).source :=
        (hjunc (0 : Fin (k+1))).1
      have hsrc3 : γ (t (Fin.succ (0 : Fin (k+1)))) ∈ (ff 0).source :=
        hcov_c' ⟨t (Fin.succ (0 : Fin (k+1))), ⟨hab1, hle1⟩, rfl⟩
      have hcancel1 : Work.Whitney.PosTransitionAt (dd 0) (ff 0) (γ (t (Fin.succ (0 : Fin (k+1))))) ↔
          Work.Whitney.PosTransitionAt (dd (Fin.succ (0 : Fin (k+1)))) (ff 0)
            (γ (t (Fin.succ (0 : Fin (k+1))))) :=
        Work.Whitney.posTransitionAt_trans_iff (hsm 0) (hsm (Fin.succ (0 : Fin (k+1)))) (hsm' 0)
          hsrc1 hsrc2 hsrc3 htd1
      have tail : Work.Whitney.ChainData γ (t (Fin.succ (0 : Fin (k+1)))) b
          (dd (Fin.succ (0 : Fin (k+1)))) (dd (Fin.last (k+1))) k
          (fun j : Fin (k+1) => dd (Fin.succ j)) (fun j : Fin (k+1) => t (Fin.succ j)) :=
        Work.Whitney.chainData_tail h1c
      have rest : Work.Whitney.ChainData γ (t (Fin.succ (0 : Fin (k+1)))) b
          (ff 0) (ff (Fin.last (m+1))) (m+1) ff
          (Function.update s 0 (t (Fin.succ (0 : Fin (k+1))))) :=
        Work.Whitney.chainData_restrictStart h2c hab1 hle1
      have ihres := ih k (m+1) hk (Nat.succ_pos m) γ hγ (t (Fin.succ (0 : Fin (k+1)))) b
        (dd (Fin.succ (0 : Fin (k+1)))) (dd (Fin.last (k+1))) (ff 0) (ff (Fin.last (m+1)))
        (fun j : Fin (k+1) => dd (Fin.succ j)) (fun j : Fin (k+1) => t (Fin.succ j))
        ff (Function.update s 0 (t (Fin.succ (0 : Fin (k+1))))) (by omega) tail rest
      exact hslide1.trans (hcancel1.trans ihres)
    have reduceM : 0 < m → s (Fin.succ (0 : Fin (m+1))) ≤ t (Fin.succ (0 : Fin (k+1))) →
        (Work.Whitney.PosTransitionAt (dd 0) (ff 0) (γ a) ↔
          Work.Whitney.PosTransitionAt (dd (Fin.last (k+1))) (ff (Fin.last (m+1))) (γ b)) := by
      intro hm hle1
      have hab1 : a ≤ s (Fin.succ (0 : Fin (m+1))) := by
        rw [← hs0]
        exact hsmono (by simp)
      have hcov_c : γ '' Set.Icc a (t (Fin.succ (0 : Fin (k+1)))) ⊆ (dd 0).source := by
        have h := hcov (0 : Fin (k+1))
        rw [Fin.castSucc_zero, ht0] at h
        exact h
      have hcov_c' : γ '' Set.Icc a (s (Fin.succ (0 : Fin (m+1)))) ⊆ (ff 0).source := by
        have h := hcov' (0 : Fin (m+1))
        rw [Fin.castSucc_zero, hs0] at h
        exact h
      have hslide2 : Work.Whitney.PosTransitionAt (dd 0) (ff 0) (γ a) ↔
          Work.Whitney.PosTransitionAt (dd 0) (ff 0) (γ (s (Fin.succ (0 : Fin (m+1))))) :=
        Work.Whitney.posTransitionAt_slide (hsm 0) (hsm' 0) hγ hab1
          (fun x hx => ⟨hcov_c (Set.image_mono (Set.Icc_subset_Icc le_rfl hle1) hx), hcov_c' hx⟩)
      have htd1 : Work.Whitney.PosTransitionAt (ff 0) (ff (Fin.succ (0 : Fin (m+1))))
          (γ (s (Fin.succ (0 : Fin (m+1))))) := by
        have h := (hjunc' (0 : Fin (m+1))).2
        rw [Fin.castSucc_zero] at h
        exact h
      have hsrc1 : γ (s (Fin.succ (0 : Fin (m+1)))) ∈ (dd 0).source :=
        hcov_c ⟨s (Fin.succ (0 : Fin (m+1))), ⟨hab1, hle1⟩, rfl⟩
      have hsrc2 : γ (s (Fin.succ (0 : Fin (m+1)))) ∈ (ff 0).source :=
        hcov_c' ⟨s (Fin.succ (0 : Fin (m+1))), ⟨hab1, le_rfl⟩, rfl⟩
      have hsrc3 : γ (s (Fin.succ (0 : Fin (m+1)))) ∈ (ff (Fin.succ (0 : Fin (m+1)))).source :=
        (hjunc' (0 : Fin (m+1))).1
      have hcancel2 : Work.Whitney.PosTransitionAt (dd 0) (ff 0) (γ (s (Fin.succ (0 : Fin (m+1))))) ↔
          Work.Whitney.PosTransitionAt (dd 0) (ff (Fin.succ (0 : Fin (m+1))))
            (γ (s (Fin.succ (0 : Fin (m+1))))) :=
        (Work.Whitney.posTransitionAt_trans_iff' (hsm 0) (hsm' 0)
          (hsm' (Fin.succ (0 : Fin (m+1)))) hsrc1 hsrc2 hsrc3 htd1).symm
      have rest : Work.Whitney.ChainData γ (s (Fin.succ (0 : Fin (m+1)))) b
          (dd 0) (dd (Fin.last (k+1))) (k+1) dd
          (Function.update t 0 (s (Fin.succ (0 : Fin (m+1))))) :=
        Work.Whitney.chainData_restrictStart h1c hab1 hle1
      have tail : Work.Whitney.ChainData γ (s (Fin.succ (0 : Fin (m+1)))) b
          (ff (Fin.succ (0 : Fin (m+1)))) (ff (Fin.last (m+1))) m
          (fun j : Fin (m+1) => ff (Fin.succ j)) (fun j : Fin (m+1) => s (Fin.succ j)) :=
        Work.Whitney.chainData_tail h2c
      have ihres := ih (k+1) m (Nat.succ_pos k) hm γ hγ (s (Fin.succ (0 : Fin (m+1)))) b
        (dd 0) (dd (Fin.last (k+1))) (ff (Fin.succ (0 : Fin (m+1)))) (ff (Fin.last (m+1)))
        dd (Function.update t 0 (s (Fin.succ (0 : Fin (m+1)))))
        (fun j : Fin (m+1) => ff (Fin.succ j)) (fun j : Fin (m+1) => s (Fin.succ j)) (by omega) rest tail
      exact hslide2.trans (hcancel2.trans ihres)
    rcases Nat.eq_zero_or_pos k with hk0 | hk
    · subst hk0
      rcases Nat.eq_zero_or_pos m with hm0 | hm
      · -- base case: both chains have a single chart
        subst hm0
        have hsucc : ((0 : Fin (0+1)).succ : Fin (0+1+1)) = Fin.last (0+1) := by
          simpa using Fin.succ_last (n := 0)
        have hab : a ≤ b := by
          rw [← ht0, ← htb]
          exact htmono (by simp)
        have hcov1 : γ '' Set.Icc a b ⊆ (dd 0).source := by
          have h := hcov (0 : Fin (0+1))
          rw [Fin.castSucc_zero, hsucc, ht0, htb] at h
          exact h
        have hcov1' : γ '' Set.Icc a b ⊆ (ff 0).source := by
          have h := hcov' (0 : Fin (0+1))
          rw [Fin.castSucc_zero, hsucc, hs0, hsb] at h
          exact h
        have htd : Work.Whitney.PosTransitionAt (dd 0) (dd (Fin.last (0+1))) (γ b) := by
          have h := (hjunc (0 : Fin (0+1))).2
          rw [Fin.castSucc_zero, hsucc, htb] at h
          exact h
        have hff' : Work.Whitney.PosTransitionAt (ff 0) (ff (Fin.last (0+1))) (γ b) := by
          have h := (hjunc' (0 : Fin (0+1))).2
          rw [Fin.castSucc_zero, hsucc, hsb] at h
          exact h
        have hb1 : γ b ∈ (dd 0).source := hcov1 ⟨b, ⟨hab, le_rfl⟩, rfl⟩
        have hb3 : γ b ∈ (ff 0).source := hcov1' ⟨b, ⟨hab, le_rfl⟩, rfl⟩
        have hslide : Work.Whitney.PosTransitionAt (dd 0) (ff 0) (γ a) ↔
            Work.Whitney.PosTransitionAt (dd 0) (ff 0) (γ b) :=
          Work.Whitney.posTransitionAt_slide (hsm 0) (hsm' 0) hγ hab
            (fun x hx => ⟨hcov1 hx, hcov1' hx⟩)
        have e1 : Work.Whitney.PosTransitionAt (dd 0) (ff 0) (γ b) ↔
            Work.Whitney.PosTransitionAt (dd (Fin.last (0+1))) (ff 0) (γ b) :=
          Work.Whitney.posTransitionAt_trans_iff (hsm 0) (hsm (Fin.last (0+1))) (hsm' 0)
            hb1 hγb hb3 htd
        have e2 : Work.Whitney.PosTransitionAt (dd (Fin.last (0+1))) (ff (Fin.last (0+1))) (γ b) ↔
            Work.Whitney.PosTransitionAt (dd (Fin.last (0+1))) (ff 0) (γ b) :=
          Work.Whitney.posTransitionAt_trans_iff' (hsm (Fin.last (0+1))) (hsm' 0)
            (hsm' (Fin.last (0+1))) hγb hb3 hγb' hff'
        exact hslide.trans (e1.trans e2.symm)
      · -- k = 0, m ≥ 1 : reduce M
        have ht1b : t (Fin.succ (0 : Fin (0+1))) = b := by
          rw [show (Fin.succ (0 : Fin (0+1)) : Fin (0+1+1)) = Fin.last (0+1) from by
            simpa using Fin.succ_last (n := 0)]
          exact htb
        refine reduceM hm ?_
        rw [ht1b, ← hsb]
        exact hsmono (hsucc_le_last m)
    · rcases Nat.eq_zero_or_pos m with hm0 | hm
      · -- k ≥ 1, m = 0 : reduce N
        subst hm0
        have hs1b : s (Fin.succ (0 : Fin (0+1))) = b := by
          rw [show (Fin.succ (0 : Fin (0+1)) : Fin (0+1+1)) = Fin.last (0+1) from by
            simpa using Fin.succ_last (n := 0)]
          exact hsb
        refine reduceN hk ?_
        rw [hs1b, ← htb]
        exact htmono (hsucc_le_last k)
      · by_cases hle1 : t (Fin.succ (0 : Fin (k+1))) ≤ s (Fin.succ (0 : Fin (m+1)))
        · exact reduceN hk hle1
        · exact reduceM hm (le_of_lt (not_le.mp hle1))

/-- **Transport along an arc.**  Chains of charts along the same arc `γ` relate the endpoint charts
with the same sign. -/
theorem posTransitionAt_of_isArcChain {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {γ : ℝ → M} (hγ : Continuous γ)
    {c d c' d' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    (h : Work.Whitney.IsArcChain γ c d) (h' : Work.Whitney.IsArcChain γ c' d')
    (hdd' : Work.Whitney.PosTransitionAt d d' (γ 1)) :
    Work.Whitney.PosTransitionAt c c' (γ 0) := by
  obtain ⟨N, hN, dd, t, h1⟩ := h
  obtain ⟨P, hP, ff, s, h2⟩ := h'
  have key := chainData_transport_aux (N + P) N P hN hP γ hγ 0 1 c d c' d' dd t ff s
    le_rfl h1 h2
  exact key.mpr hdd'

end Work.Whitney
