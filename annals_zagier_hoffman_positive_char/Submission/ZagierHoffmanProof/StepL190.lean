import Submission.ZagierHoffmanProof.StepL189
import Submission.ZagierHoffmanProof.StepL185
import Submission.ZagierHoffmanProof.StepL186
import Submission.ZagierHoffmanProof.StepL187
import Submission.ZagierHoffmanProof.StepL107

set_option autoImplicit false
set_option maxHeartbeats 20000000
open Polynomial RatFunc
open scoped BigOperators
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

/-!
# Step L190: the ambient level-k CASE dispatch

`maink_case_dispatch_amb`: the port of StepL149's `maink_case_dispatch` to route (C).
The dispatch structure is verbatim (CASE-1 vs CASE-2 and the maximal strict-index
analysis of `levelk_inDomain_cases`), but the four leaves are the AMBIENT ports
`maink_case1_j0_amb` (StepL187), `maink_case1_deep_amb` (StepL189),
`maink_case2_qqq_amb` (StepL185) and `maink_case2_j_amb` (StepL186), so the outputs
are `Lam`-admissible and the recursion hypothesis receives the ambient descent.
theorem_B/D remain ABP-gated (no route).
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- The ambient level-`k` in-domain CASE dispatch: a (`k-1`)-admissible but not
`k`-admissible weight-`w` tuple expands at EVERY ambient level `Lam >= k`, given the
ambient `ambNu` descent for the chain members. -/
theorem maink_case_dispatch_amb (w : ℕ) (k : ℕ) (r : ℕ) (s : Fin r → ℕ+) (hw : weight r s = w)
    (hk1 : 1 ≤ k) (hk2 : 2 ≤ k)
    (h1 : kAdmissible (Nat.card F) s (k - 1)) (hnot : ¬ kAdmissible (Nat.card F) s k)
    (Λ : ℕ) (hΛ : k ≤ Λ)
    (rec : ∀ (r' : ℕ) (m : Fin r' → ℕ+) (_hm : weight r' m = w),
      ambNu Λ (Nat.card F) w m < ambNu Λ (Nat.card F) w s → ¬ kAdmissible (Nat.card F) m Λ →
      AdmExpT F w Λ m) :
    AdmExpT F w Λ s := by
  classical
  rcases levelk_inDomain_cases k (Nat.card F) (card_ge_two F) hk1 s h1 hnot with
    hc1 | hc2
  · rcases hc1 with ⟨hkr', hbigp⟩
    have hbigv : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ) := by
      have hp : pad0 s (k - 1) = (s ⟨k - 1, by omega⟩ : ℕ) := pad0_of_lt s (by omega)
      omega
    by_cases hallq : ∀ x : ℕ, x < k - 1 → pad0 s x = Nat.card F
    · exact maink_case1_j0_amb F w r s hw k hk1 hk2 hkr' hbigv hallq Λ hΛ
        (fun r' m hm hnotk _ hlt => rec r' m hm hlt hnotk)
    · push Not at hallq
      obtain ⟨x0, hx0, heq0⟩ := hallq
      have hlt0 : pad0 s x0 < Nat.card F := by
        have := h1.1 x0 hx0
        omega
      let S : Finset ℕ := (Finset.range (k - 1)).filter (fun x => pad0 s x < Nat.card F)
      have hS : S.Nonempty :=
        ⟨x0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hx0, hlt0⟩⟩
      let jm : ℕ := S.max' hS
      have hjmS : jm ∈ S := Finset.max'_mem S hS
      have hjmlt : jm < k - 1 := Finset.mem_range.mp (Finset.mem_filter.mp hjmS).1
      have hjm_lt : pad0 s jm < Nat.card F := (Finset.mem_filter.mp hjmS).2
      have hmax : ∀ i : ℕ, jm < i → i < k - 1 → ¬ (pad0 s i < Nat.card F) := by
        intro i hji hik hcon
        have hiS : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hik, hcon⟩
        have := Finset.le_max' S i hiS
        omega
      have hjmr : jm < r := by omega
      have hj1 : 1 ≤ jm + 1 := by omega
      have hjk : jm + 1 ≤ k - 1 := by omega
      have hsj : (s ⟨jm + 1 - 1, by omega⟩ : ℕ) < Nat.card F := by
        have hidx : (⟨jm + 1 - 1, by omega⟩ : Fin r) = ⟨jm, hjmr⟩ := by
          apply Fin.ext
          simp only [Fin.val_mk]
          omega
        rw [hidx, ← pad0_of_lt s hjmr]
        exact hjm_lt
      have hmid : ∀ i : Fin r, jm + 1 ≤ (i : ℕ) → (i : ℕ) < k - 1 →
          (s i : ℕ) = Nat.card F := by
        intro i hi hik
        have hpad : pad0 s (i : ℕ) = (s i : ℕ) := pad0_of_lt s i.isLt
        have hle : pad0 s (i : ℕ) ≤ Nat.card F := h1.1 (i : ℕ) hik
        have hnlt : ¬ (pad0 s (i : ℕ) < Nat.card F) := hmax (i : ℕ) (by omega) hik
        rw [← hpad]
        omega
      exact maink_case1_deep_amb F w r s hw k (jm + 1) hk1 hkr' hj1 hjk hbigv hsj hmid h1
        Λ hΛ rec
  · rcases hc2 with ⟨hrk, hleq, hlastq⟩
    subst r
    have hsleq : ∀ x : ℕ, x < k - 1 → pad0 s x ≤ Nat.card F := fun x hx => h1.1 x hx
    by_cases hallq : ∀ i : Fin k, (s i : ℕ) = Nat.card F
    · exact maink_case2_qqq_amb F w k s hw hk1 hk2 hallq Λ hΛ rec
    · push Not at hallq
      obtain ⟨i0, hi0⟩ := hallq
      have hi0lt : (i0 : ℕ) < k - 1 := by
        by_contra hcon
        have hie : (i0 : ℕ) = k - 1 := by omega
        have hp : pad0 s (k - 1) = (s i0 : ℕ) := by
          rw [← hie, pad0_of_lt s i0.isLt]
        rw [hlastq] at hp
        omega
      have hi0lt' : pad0 s (i0 : ℕ) < Nat.card F := by
        have hpad : pad0 s (i0 : ℕ) = (s i0 : ℕ) := pad0_of_lt s i0.isLt
        have h := hleq (i0 : ℕ) hi0lt
        rw [hpad] at h
        rw [hpad]
        omega
      let S : Finset ℕ := (Finset.range (k - 1)).filter (fun x => pad0 s x < Nat.card F)
      have hS : S.Nonempty :=
        ⟨(i0 : ℕ), Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi0lt, hi0lt'⟩⟩
      let jm : ℕ := S.max' hS
      have hjmS : jm ∈ S := Finset.max'_mem S hS
      have hjmlt : jm < k - 1 := Finset.mem_range.mp (Finset.mem_filter.mp hjmS).1
      have hjm_lt : pad0 s jm < Nat.card F := (Finset.mem_filter.mp hjmS).2
      have hmax : ∀ i : ℕ, jm < i → i < k - 1 → ¬ (pad0 s i < Nat.card F) := by
        intro i hji hik hcon
        have hiS : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hik, hcon⟩
        have := Finset.le_max' S i hiS
        omega
      have hj1 : 1 ≤ jm + 1 := by omega
      have hjk : jm + 1 ≤ k - 1 := by omega
      have hsj : (s ⟨jm + 1 - 1, by omega⟩ : ℕ) < Nat.card F := by
        have hidx : (⟨jm + 1 - 1, by omega⟩ : Fin k) = ⟨jm, by omega⟩ := by
          apply Fin.ext
          simp only [Fin.val_mk]
          omega
        rw [hidx, ← pad0_of_lt s (by omega : jm < k)]
        exact hjm_lt
      have hqend : ∀ i : Fin k, (jm + 1 : ℕ) ≤ (i : ℕ) → (i : ℕ) < k →
          (s i : ℕ) = Nat.card F := by
        intro i hi hik
        by_cases hik' : (i : ℕ) < k - 1
        · have hpad : pad0 s (i : ℕ) = (s i : ℕ) := pad0_of_lt s i.isLt
          have hle : pad0 s (i : ℕ) ≤ Nat.card F := hleq (i : ℕ) hik'
          have hnlt : ¬ (pad0 s (i : ℕ) < Nat.card F) := hmax (i : ℕ) (by omega) hik'
          rw [← hpad]
          omega
        · have hie : (i : ℕ) = k - 1 := by omega
          have hp : pad0 s (k - 1) = (s i : ℕ) := by
            rw [← hie, pad0_of_lt s i.isLt]
          rw [hlastq] at hp
          exact hp.symm
      exact maink_case2_j_amb F w k s hw hk1 hk2 (jm + 1) hj1 hjk hsj hqend hsleq Λ hΛ rec

end ZagierHoffmanPositiveChar
