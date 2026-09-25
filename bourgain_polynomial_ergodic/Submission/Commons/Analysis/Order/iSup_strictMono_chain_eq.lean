import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Fin.Basic
import Mathlib.Order.CompleteLattice.Basic

namespace Commons.Analysis.Order

/-! Auxiliary construction: extending a strictly monotone function on `Fin (J+1)`
to a strictly monotone function on all of `ℕ`, by continuing with unit steps
after `J`. -/

/-- A strictly monotone extension of `k : Fin (J+1) → ℕ` to `ℕ → ℕ`. -/
def strictMonoExtend (J : ℕ) (k : Fin (J+1) → ℕ) : ℕ → ℕ :=
  fun n => if h : n ≤ J then k ⟨n, Nat.lt_succ_of_le h⟩
           else k ⟨J, Nat.lt_succ_self J⟩ + (n - J)

lemma strictMonoExtend_of_le {J : ℕ} {k : Fin (J+1) → ℕ} {n : ℕ} (h : n ≤ J) :
    strictMonoExtend J k n = k ⟨n, Nat.lt_succ_of_le h⟩ := dif_pos h

lemma strictMonoExtend_of_gt {J : ℕ} {k : Fin (J+1) → ℕ} {n : ℕ} (h : J < n) :
    strictMonoExtend J k n = k ⟨J, Nat.lt_succ_self J⟩ + (n - J) :=
  dif_neg (not_le.mpr h)

lemma strictMono_strictMonoExtend {J : ℕ} {k : Fin (J+1) → ℕ} (hk : StrictMono k) :
    StrictMono (strictMonoExtend J k) := by
  intro a b hab
  by_cases hb : b ≤ J
  · have ha : a ≤ J := le_trans (le_of_lt hab) hb
    rw [strictMonoExtend_of_le (J := J) (k := k) ha,
        strictMonoExtend_of_le (J := J) (k := k) hb]
    exact hk (show (⟨a, Nat.lt_succ_of_le ha⟩ : Fin (J+1)) <
                  ⟨b, Nat.lt_succ_of_le hb⟩ from hab)
  · have hb' : J < b := lt_of_not_ge hb
    by_cases ha : a ≤ J
    · rw [strictMonoExtend_of_le (J := J) (k := k) ha,
          strictMonoExtend_of_gt (J := J) (k := k) hb']
      have hle : k ⟨a, Nat.lt_succ_of_le ha⟩ ≤ k ⟨J, Nat.lt_succ_self J⟩ :=
        hk.monotone (by
          rw [Fin.le_iff_val_le_val]; exact ha)
      omega
    · have ha' : J < a := lt_of_not_ge ha
      rw [strictMonoExtend_of_gt (J := J) (k := k) ha',
          strictMonoExtend_of_gt (J := J) (k := k) hb']
      omega

theorem iSup_strictMono_chain_eq {α : Type*} [CompleteLattice α]
    (F : (J : ℕ) → (Fin (J+1) → ℕ) → α) :
    (⨆ (u : {u : ℕ → ℕ // StrictMono u}) (J : ℕ), F J (fun j => u.1 j.1)) =
    (⨆ (J : ℕ) (k : Fin (J+1) → ℕ) (_ : StrictMono k), F J k) := by
  apply le_antisymm
  · apply iSup_le; intro u
    apply iSup_le; intro J
    have hk' : StrictMono (fun j : Fin (J+1) => u.1 j.1) :=
      fun a b hab => u.2 (show a.1 < b.1 from hab)
    exact le_iSup_of_le J (le_iSup_of_le (fun j : Fin (J+1) => u.1 j.1)
      (le_iSup (fun _ : StrictMono (fun j : Fin (J+1) => u.1 j.1) =>
        F J (fun j : Fin (J+1) => u.1 j.1)) hk'))
  · apply iSup_le; intro J
    apply iSup_le; intro k
    apply iSup_le; intro hk
    have hu : StrictMono (strictMonoExtend J k) := strictMono_strictMonoExtend hk
    have heq : (fun j : Fin (J+1) => (strictMonoExtend J k) j.1) = k := by
      funext j
      rw [strictMonoExtend_of_le (J := J) (k := k) (n := j.1) (Nat.le_of_lt_succ j.2)]
    have h1 : F J (fun j : Fin (J+1) => (strictMonoExtend J k) j.1) ≤
        (⨆ (u : {u : ℕ → ℕ // StrictMono u}) (J : ℕ), F J (fun j => u.1 j.1)) :=
      le_iSup_of_le ⟨strictMonoExtend J k, hu⟩
        (le_iSup (fun J' => F J' (fun j : Fin (J'+1) => (strictMonoExtend J k) j.1)) J)
    rw [congrArg (F J) heq] at h1
    exact h1

end Commons.Analysis.Order