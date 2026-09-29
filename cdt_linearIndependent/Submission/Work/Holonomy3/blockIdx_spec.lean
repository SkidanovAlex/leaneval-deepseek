import Mathlib
import Submission.Work.Holonomy3.seeding_defs

namespace Work.Holonomy3

theorem blockIdx_spec {l d : ℕ} (m : ℕ) (hm : 0 < m) (hd : 0 < d)
    (γ : Fin (l + 2) → ℝ) (hγ0 : γ 0 = 0) (hγlast : γ (Fin.last (l + 1)) = m)
    (hmono : StrictMono γ) (j : Fin d) (p : Fin (l + 1)) :
    (blockIdx m γ j = p) ↔
      (γ p.castSucc / (m : ℝ) ≤ (j : ℝ) / d ∧ (j : ℝ) / d < γ p.succ / (m : ℝ)) := by
  classical
  -- `M` is the number of division points not exceeding `j/d`:
  -- `M = # {q : Fin (l+1) | γ q.castSucc / m ≤ j/d}`.
  let M : ℕ := (Finset.univ.filter (fun q : Fin (l + 1) =>
    γ q.castSucc / (m : ℝ) ≤ (j : ℝ) / d)).card
  -- The defining predicate is downward closed, so the filter is an initial segment
  -- and membership is equivalent to `q.val < M`.
  have hkey : ∀ q : Fin (l + 1), (q : ℕ) < M ↔ γ q.castSucc / (m : ℝ) ≤ (j : ℝ) / d := by
    intro q
    exact Fin.lt_card_filter_univ_iff_apply_of_imp
      (fun q : Fin (l + 1) => γ q.castSucc / (m : ℝ) ≤ (j : ℝ) / d)
      (fun i k hk hi => le_trans (div_le_div_of_nonneg_right
        (hmono.monotone (Fin.castSucc_le_castSucc_iff.mpr hk)) (by positivity)) hi)
  have hMmem : (0 : Fin (l + 1)) ∈ Finset.univ.filter (fun q : Fin (l + 1) =>
      γ q.castSucc / (m : ℝ) ≤ (j : ℝ) / d) := by
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have h0 : (0 : Fin (l + 1)).castSucc = (0 : Fin (l + 2)) := by simp
    rw [h0, hγ0, zero_div]
    exact div_nonneg (Nat.cast_nonneg _) (by positivity)
  have hM1 : 1 ≤ M := Finset.one_le_card.mpr ⟨0, hMmem⟩
  have hMle : M ≤ l + 1 := by
    show (Finset.univ.filter (fun q : Fin (l + 1) =>
      γ q.castSucc / (m : ℝ) ≤ (j : ℝ) / d)).card ≤ l + 1
    calc _ ≤ (Finset.univ : Finset (Fin (l + 1))).card := Finset.card_filter_le _ _
      _ = l + 1 := by simp
  -- The crux: `p.val + 1 < M` fails exactly when `j/d < γ p.succ / m`.
  have hD : ¬(p.val + 1 < M) ↔ (j : ℝ) / d < γ p.succ / (m : ℝ) := by
    rcases lt_or_ge (p.val + 1) (l + 1) with hp1 | hp1
    · -- `p` is not the last index: `⟨p.val+1,hp1⟩` has `castSucc = p.succ`.
      have hcast : (⟨p.val + 1, hp1⟩ : Fin (l + 1)).castSucc = p.succ := by
        rw [Fin.ext_iff]; simp [Fin.val_succ]
      have hkn := hkey ⟨p.val + 1, hp1⟩
      rw [hcast] at hkn
      rw [show (↑(⟨p.val + 1, hp1⟩ : Fin (l + 1)) : ℕ) = p.val + 1 from rfl] at hkn
      simp only [hkn, not_le]
    · -- `p` is the last index: `p.succ = Fin.last (l+1)` and `γ p.succ = m`.
      have hpv : p.val + 1 = l + 1 := by have := p.isLt; omega
      have hpsucc : p.succ = Fin.last (l + 1) := by
        rw [Fin.ext_iff]; simp [Fin.val_succ, Fin.val_last]; omega
      have h1 : γ p.succ / (m : ℝ) = 1 := by
        rw [hpsucc, hγlast]
        exact div_self (by exact_mod_cast hm.ne')
      have hnot : ¬(p.val + 1 < M) := by rw [hpv]; omega
      refine iff_of_true hnot ?_
      rw [h1, div_lt_one (by exact_mod_cast hd)]
      exact_mod_cast j.isLt
  have hstep1 : (blockIdx m γ j = p) ↔ (M - 1 = p.val) := by
    rw [Fin.ext_iff]; rfl
  have hstep2 : (M - 1 = p.val) ↔
      (γ p.castSucc / (m : ℝ) ≤ (j : ℝ) / d ∧ (j : ℝ) / d < γ p.succ / (m : ℝ)) := by
    have hAsub : M - 1 = p.val ↔ M = p.val + 1 := by omega
    have hB : (M = p.val + 1) ↔ (p.val < M ∧ ¬(p.val + 1 < M)) := by omega
    simp only [hAsub, hB, hkey p, hD]
  exact hstep1.trans hstep2

end Work.Holonomy3
