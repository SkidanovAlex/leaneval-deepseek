/-
# Elementary algebra of the `fkr` interpolation

Continuation of `Submission.Work.KMTPlan.A6.FkrDefs`: the elementary properties of `fkrPhi`
(its values on the blocks `(β (k-1), β k]`) and of `fkrH` (continuity and the telescoping along
the chain `β ∘ u`).
-/
import Mathlib
import Submission.Work.KMTPlan.A6.FkrDefs

set_option autoImplicit false

namespace Work.KMTPlan.A6

open MeasureTheory
open scoped ENNReal BigOperators

variable {X : Type*} [MeasurableSpace X]

/-- For `s ∈ [0,1]` the clamping in `fkrPhi` is inactive. -/
lemma fkrPhi_le (β : ℕ → ℝ) (k : ℕ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    fkrPhi β k s = min s (β k) - min s (β (k - 1)) := by
  rw [fkrPhi, min_eq_left hs1, max_eq_right hs0]

/-- `fkrPhi β k (β q)` is the full length of the `k`-th block when `k ≤ q`, and `0` when `q < k`
(assuming `β` is monotone with `0 ≤ β 0` and `β q ≤ 1`). -/
lemma fkrPhi_beta (β : ℕ → ℝ) (hβ0 : 0 ≤ β 0) (hβmono : Monotone β) {k q : ℕ}
    (hq1 : β q ≤ 1) :
    fkrPhi β k (β q) = if k ≤ q then (β k - β (k - 1)) else 0 := by
  have hq0 : 0 ≤ β q := le_trans hβ0 (hβmono (Nat.zero_le q))
  rw [fkrPhi_le β k hq0 hq1]
  by_cases h : k ≤ q
  · rw [if_pos h]
    have e1 : min (β q) (β k) = β k := min_eq_right (hβmono h)
    have e2 : min (β q) (β (k - 1)) = β (k - 1) := min_eq_right (hβmono (by omega))
    rw [e1, e2]
  · rw [if_neg h]
    have h' : q ≤ k - 1 := by omega
    have e1 : min (β q) (β k) = β q := min_eq_left (hβmono (by omega))
    have e2 : min (β q) (β (k - 1)) = β q := min_eq_left (hβmono h')
    rw [e1, e2, sub_self]

/-- `t ↦ fkrPhi β k t` is continuous. -/
lemma continuous_fkrPhi (β : ℕ → ℝ) (k : ℕ) : Continuous (fun t => fkrPhi β k t) := by
  have h1 : Continuous (fun t : ℝ => min (max 0 (min t 1)) (β k)) := by fun_prop
  have h2 : Continuous (fun t : ℝ => min (max 0 (min t 1)) (β (k - 1))) := by fun_prop
  exact h1.sub h2

/-- `fkrH` is continuous in `t`. -/
lemma continuous_fkrH (K : ℕ) (β : ℕ → ℝ) (w : ℕ → X → ℂ) (x : X) :
    Continuous (fun t => fkrH K β w x t) := by
  unfold fkrH
  refine continuous_finsetSum _ (fun k _ => ?_)
  exact continuous_const.mul (Complex.continuous_ofReal.comp (continuous_fkrPhi β k))

/-- **Telescoping of `fkrH` along the chain `β ∘ u`.**  If `β` is monotone, `0 ≤ β 0` and
`β j ≤ 1` for `j ≤ K`, then the increment of `fkrH` between the nodes `β p` and `β q` is the sum
of the densities over the blocks strictly in between. -/
lemma fkrH_beta_sub (K : ℕ) (β : ℕ → ℝ) (w : ℕ → X → ℂ) (x : X) (hβ0 : 0 ≤ β 0)
    (hβmono : Monotone β) (hβ1K : ∀ k ≤ K, β k ≤ 1) {p q : ℕ} (hpq : p ≤ q) (hqK : q ≤ K) :
    fkrH K β w x (β q) - fkrH K β w x (β p)
      = ∑ k ∈ Finset.Icc (p + 1) q, w k x * ((β k - β (k - 1) : ℝ) : ℂ) := by
  have hp1 : β p ≤ 1 := le_trans (hβmono hpq) (hβ1K q hqK)
  have key : ∀ k ∈ Finset.Icc 1 K,
      fkrPhi β k (β q) - fkrPhi β k (β p)
        = if k ∈ Finset.Icc (p + 1) q then (β k - β (k - 1)) else 0 := by
    intro k hk
    simp only [Finset.mem_Icc] at hk
    rw [fkrPhi_le β k (le_trans hβ0 (hβmono (Nat.zero_le q))) (hβ1K q hqK),
      fkrPhi_le β k (le_trans hβ0 (hβmono (Nat.zero_le p))) hp1]
    by_cases h : p + 1 ≤ k ∧ k ≤ q
    · rw [if_pos (Finset.mem_Icc.mpr h)]
      have e1 : min (β q) (β k) = β k := min_eq_right (hβmono h.2)
      have e2 : min (β q) (β (k - 1)) = β (k - 1) := min_eq_right (hβmono (by omega))
      have e3 : min (β p) (β k) = β p := min_eq_left (hβmono (by omega))
      have e4 : min (β p) (β (k - 1)) = β p := min_eq_left (hβmono (by omega))
      rw [e1, e2, e3, e4]; ring
    · rw [if_neg (by simpa [Finset.mem_Icc] using h)]
      rcases lt_or_ge k (p + 1) with hlt | hge
      · have h1 : k ≤ p := by omega
        have e1 : min (β q) (β k) = β k := min_eq_right (hβmono (by omega))
        have e2 : min (β q) (β (k - 1)) = β (k - 1) := min_eq_right (hβmono (by omega))
        have e3 : min (β p) (β k) = β k := min_eq_right (hβmono h1)
        have e4 : min (β p) (β (k - 1)) = β (k - 1) := min_eq_right (hβmono (by omega))
        rw [e1, e2, e3, e4]; ring
      · have hq : q < k := by omega
        have e1 : min (β q) (β k) = β q := min_eq_left (hβmono (by omega))
        have e2 : min (β q) (β (k - 1)) = β q := min_eq_left (hβmono (by omega))
        have e3 : min (β p) (β k) = β p := min_eq_left (hβmono (by omega))
        have e4 : min (β p) (β (k - 1)) = β p := min_eq_left (hβmono (by omega))
        rw [e1, e2, e3, e4]; ring
  have hsum : ∑ k ∈ Finset.Icc 1 K, (w k x * ((fkrPhi β k (β q) : ℝ) : ℂ)
        - w k x * ((fkrPhi β k (β p) : ℝ) : ℂ))
      = ∑ k ∈ Finset.Icc 1 K,
          (if k ∈ Finset.Icc (p + 1) q then w k x * ((β k - β (k - 1) : ℝ) : ℂ) else 0) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [← mul_sub, ← Complex.ofReal_sub, key k hk]
    by_cases h : k ∈ Finset.Icc (p + 1) q
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h, Complex.ofReal_zero, mul_zero]
  rw [fkrH, fkrH, ← Finset.sum_sub_distrib, hsum, Finset.sum_ite_mem]
  congr 1
  rw [Finset.inter_eq_right.mpr]
  intro k hk
  simp only [Finset.mem_Icc] at hk ⊢
  exact ⟨by omega, le_trans hk.2 hqK⟩

/-- **The chain identity for `fkrH`.**  If `w k x * (β k - β (k-1)) = g k x - g (k-1) x` for all
`k ∈ {1,…,K}` then `fkrH` reproduces the values `g` at the nodes. -/
lemma fkrH_chain (K : ℕ) (β : ℕ → ℝ) (w : ℕ → X → ℂ) (g : ℕ → X → ℂ) (x : X) (hβ0 : 0 ≤ β 0)
    (hβmono : Monotone β) (hβ1K : ∀ k ≤ K, β k ≤ 1)
    (hdens : ∀ k ∈ Finset.Icc 1 K, w k x * ((β k - β (k - 1) : ℝ) : ℂ) = g k x - g (k - 1) x)
    {p q : ℕ} (hpq : p ≤ q) (hqK : q ≤ K) :
    fkrH K β w x (β q) - fkrH K β w x (β p) = g q x - g p x := by
  have htel : ∀ q', p ≤ q' →
      (∑ k ∈ Finset.Icc (p + 1) q', (g k x - g (k - 1) x)) = g q' x - g p x := by
    intro q' hq'
    induction q', hq' using Nat.le_induction with
    | base => rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty, sub_self]
    | succ m hm ih =>
        rw [Finset.sum_Icc_succ_top (by omega), ih]
        simp only [Nat.add_sub_cancel]
        ring
  rw [fkrH_beta_sub K β w x hβ0 hβmono hβ1K hpq hqK,
    Finset.sum_congr rfl (fun k hk => by
      simp only [Finset.mem_Icc] at hk
      exact hdens k (Finset.mem_Icc.mpr ⟨by omega, le_trans hk.2 hqK⟩)),
    htel q hpq]

end Work.KMTPlan.A6
