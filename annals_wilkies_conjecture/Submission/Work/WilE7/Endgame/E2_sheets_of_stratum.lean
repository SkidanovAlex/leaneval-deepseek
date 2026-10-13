import Mathlib
import Submission.Work.WilE7.Endgame.E2Aux
import Submission.Work.CoreStep.sheets_over_cell_of_hrank_localFin
import Submission.Work.CoreStep.hclosed_of_sigma
import Submission.Work.CoreStep.havoid_of_sigma
import Submission.Work.WilE7.coreLT_succ.gcase_fiber_finite
import Submission.Work.WilE7.fiber_card_bound

namespace Work.WilE7.Endgame

set_option autoImplicit false
open Classical Filter Topology
open WilkiesDesign WilkiesDesign.E
open Work.WilE7.MainDesign
open Work.WilE7.CoreLTSuccPlan
open Work.WilE7.CoreStep (pPair pDim absPtUp absPtInv absReindex absLevelPairSet absPairSet
  pairPtUp projTop projTopSet projTopLin absPtLin AttainAt vertCoord)
open Work.CoreStep (frontierSet pairSubBaseFst pairFrontierBaseFst pairBase)

theorem E2_sheets_of_stratum (hE2 : HypE2) (F : ℕ) :
    ∃ (A : ℕ) (P : Polynomial ℕ),
      ∀ (n m K D : ℕ) (S : Stratum 0 (n + (m + 1))) (b : Set (Fin n → ℝ))
        (Sig : List (SemiPf (n + pPair n m)))
        (Wl : List (Stratum 0 (pPair n m))),
        S.Good → S.X.fmt ≤ F → S.deg ≤ D →
        (∀ z ∈ S.X.set, projRank S z = n + (m + 1) - S.j) →
        IsCell n b → b.Nonempty →
        b ⊆ projFirst n (m + 1) '' absSet S →
        (∀ Z ∈ Sig, Disjoint b (projFirst n (pPair n m) '' Z.set)) →
        frontierSet n m S ⊆ ⋃ Z ∈ Sig, projFirst n (pPair n m) '' Z.set →
        (∀ W ∈ Wl, W.Good) →
        (∀ W ∈ Wl, W.X.set ⊆ (absPairSet S).set) →
        ((absPairSet S).set = ⋃ W ∈ Wl, W.X.set) →
        (∀ W ∈ Wl, pPair n m - W.j < n + (m + 1) - S.j →
          pairSubBaseFst n m W ⊆ ⋃ Z ∈ Sig, projFirst n (pPair n m) '' Z.set) →
        ∃ (k : ℕ) (s : Fin k → (Fin n → ℝ) → (Fin (m + 1) → ℝ)),
          0 < k ∧ (∀ j, ContinuousOn (s j) b) ∧
          (∀ x ∈ b, Function.Injective fun j : Fin k => s j x) ∧
          (∀ (j : Fin k) (x : Fin n → ℝ), x ∈ b → Fin.append x (s j x) ∈ absSet S) ∧
          (∀ x ∈ b, (WilkiesDesign.E.fiber (absSet S) x).ncard = k) ∧
          (∀ z ∈ absSet S, projFirst n (m + 1) z ∈ b →
            ∃ j : Fin k, s j (projFirst n (m + 1) z) = projSnd n (m + 1) z) ∧
          k ≤ P.eval D := by
  -- The degree bound on the number of sheets: the number of points of a fibre of `absSet S` over
  -- a base point is bounded by a polynomial in the degree of the semi-Pfaffian presentation.
  obtain ⟨p, hp⟩ := Work.WilE7.fiber_card_bound hE2 F
  refine ⟨0, p, ?_⟩
  intro n m K D S b Sig Wl hGood hFmt hDeg hrank hCell hbne hbsub hdisj hfront
    hWgood hWsub hWcov hWlow
  -- The closure of `absSet S` adds no point over the Σ-free cell `b`.
  have hclosed : ∀ z ∈ closure (absSet S), projFirst n (m + 1) z ∈ b → z ∈ absSet S :=
    Work.CoreStep.hclosed_of_sigma (n := n) (m := m) (s := pPair n m) S Sig hfront b hdisj
  -- Hence the fibres of `absSet S` over `b` are finite.
  have hfin : ∀ x ∈ b, (fiber (absSet S) x).Finite :=
    Work.WilE7.coreLT_succ.gcase_fiber_finite S hGood hrank b hclosed
  -- The Σ-avoidance hypothesis for the pair set.
  have havoid :=
    Work.CoreStep.havoid_of_sigma (n := n) (m := m) (s := pPair n m) S Sig Wl hWlow b hdisj
  -- The sheet decomposition over the cell.
  obtain ⟨k, s, hcont, hinj, hmem, hcard, hcov⟩ :=
    Work.CoreStep.sheets_over_cell_of_hrank_localFin S hGood hrank b hfin hCell hbsub hclosed
      Wl hWgood hWsub hWcov havoid
  -- `b` is nonempty and its points are projections of points of `absSet S`, so every fibre over
  -- `b` is nonempty, whence `0 < k`.
  obtain ⟨x₀, hx₀⟩ := hbne
  have hfibne : (fiber (absSet S) x₀).Nonempty := by
    obtain ⟨z, hz, hzπ⟩ := hbsub hx₀
    refine ⟨projSnd n (m + 1) z, ?_⟩
    rw [WilkiesDesign.E.fiber, Set.mem_ofPred_eq]
    have happ : Fin.append x₀ (projSnd n (m + 1) z) = z := by
      rw [← hzπ]
      exact Fin.append_castAdd_natAdd
    rw [happ]
    exact hz
  have hkpos : 0 < k := by
    rw [← hcard x₀ hx₀]
    exact (Set.ncard_pos (hfin x₀ hx₀)).mpr hfibne
  -- The cardinality bound.
  have hcard_bound : k ≤ p.eval D := by
    have h2 : (fiber (absSet S) x₀).ncard ≤ p.eval S.X.deg := by
      have hthis := hp n (m + 1) (Work.CoreStep.absSub S) x₀ ?_ ?_
      · rwa [Work.CoreStep.absSub_set, Work.CoreStep.absSub_deg] at hthis
      · rw [Work.CoreStep.absSub_fmt]
        have := hFmt
        simp only [WilkiesDesign.E.SemiPf.fmt, Nat.zero_add] at this
        exact this
      · rw [Work.CoreStep.absSub_set]; exact hfin x₀ hx₀
    calc k = (fiber (absSet S) x₀).ncard := (hcard x₀ hx₀).symm
      _ ≤ p.eval S.X.deg := h2
      _ ≤ p.eval D :=
          Work.WilE7.eval_mono_nat (le_trans (Nat.le_add_right _ _) hDeg)
  exact ⟨k, s, hkpos, hcont, hinj, hmem, hcard, hcov, hcard_bound⟩

end Work.WilE7.Endgame
