/-
# Higman's Lemma 12: dispatching the canonical form to the four cases

Given the canonical form of `Q3/L12/case_core.lean` together with the resonance congruence (★),
the anisotropy and the coprimalities, this file dispatches to `case_B_ab`, `case_B_r`,
`case_C_I`, `case_C_II` and `case_D` according to the four possible cases of `(r, s)`.

Two small facts are also proved here, used by the outer normalisation:

* `pow_surjective`: `x ↦ x ^ k` is onto `𝔽_{2 ^ n}` when `k` is coprime to `2 ^ n - 1`;
* `support_nonempty`: if the squaring form `C α ^ (1 + 2 ^ r) + C' β ^ (1 + 2 ^ s) + Σ g k l …`
  is anisotropic then the double sum has a nonzero coefficient.  Indeed otherwise the form
  vanishes at `(α, 1)` for the `α` with `α ^ (1 + 2 ^ r) = C' / C`.
-/

import Mathlib
import Submission.Work.Higman.Q3.L12.case_core
import Submission.Work.Higman.Q3.L12.case_C
import Submission.Work.Higman.Q3.L12.case_C_II
import Submission.Work.Higman.Q3.L12.case_D
import Submission.Work.Higman.Q3.L12.res_r_ab_pin

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Work.Higman.Q3.L12

open Work.Higman

open scoped BigOperators

variable {n : ℕ}

/-- `x ↦ x ^ k` is onto `𝔽_{2 ^ n}` when `k` is coprime to `2 ^ n - 1`. -/
lemma pow_surjective {n : ℕ} (hn : 0 < n) {k : ℕ} (hk : 0 < k)
    (hcop : Nat.Coprime k (2 ^ n - 1)) :
    ∀ y : GaloisField 2 n, ∃ x : GaloisField 2 n, x ^ k = y := by
  intro y
  rcases eq_or_ne y 0 with rfl | hy
  · exact ⟨0, zero_pow (by omega)⟩
  · obtain ⟨u, hu⟩ := units_pow_surjective (F := GaloisField 2 n) (A := k)
      (by rw [GaloisField.card 2 n (by omega)]; exact hcop) (Units.mk0 y hy)
    refine ⟨(u : GaloisField 2 n), ?_⟩
    have := congrArg (fun z : (GaloisField 2 n)ˣ => (z : GaloisField 2 n)) hu
    simpa using this

/-- If `a ≡ 0 (mod n)`, `0 < a < 2 * n` then `a = n`. -/
lemma eq_of_modEq_zero_of_pos_of_lt {n a : ℕ} (hpos : 0 < a) (hlt : a < 2 * n)
    (h : a ≡ 0 [MOD n]) : a = n := by
  have hd : n ∣ a := by
    rw [Nat.dvd_iff_mod_eq_zero]
    simpa [Nat.ModEq] using h
  obtain ⟨k, hk⟩ := hd
  have hk0 : 0 < k := by
    by_contra hk'
    simp at hk'
    rw [hk', mul_zero] at hk
    omega
  have hk2 : k < 2 := by
    have h1 : n * k < 2 * n := by rw [← hk]; exact hlt
    have h2 : n * k < n * 2 := by simpa only [Nat.mul_comm 2 n] using h1
    exact Nat.lt_of_mul_lt_mul_left h2
  have hk1 : k = 1 := by omega
  rw [hk1, mul_one] at hk
  exact hk

/-- The support of the double sum is nonempty when the squaring form is anisotropic. -/
lemma support_nonempty {n : ℕ} (hn : 2 ≤ n) {r s : ℕ} (hr : r < n)
    {C C' : GaloisField 2 n} (hC : C ≠ 0) (hC' : C' ≠ 0) {g : ℕ → ℕ → GaloisField 2 n}
    (hcopr : Nat.Coprime (1 + 2 ^ r) (2 ^ n - 1))
    (hani : ∀ α β : GaloisField 2 n, (α, β) ≠ 0 →
      C * α ^ (1 + 2 ^ r) + C' * β ^ (1 + 2 ^ s) +
        ∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n, g k l * α ^ (2 ^ k) * β ^ (2 ^ l) ≠ 0) :
    ∃ k l : ℕ, k < n ∧ l < n ∧ g k l ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  have hsum : ∀ α β : GaloisField 2 n,
      (∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n, g k l * α ^ (2 ^ k) * β ^ (2 ^ l)) = 0 := by
    intro α β
    refine Finset.sum_eq_zero (fun k hk => Finset.sum_eq_zero (fun l hl => ?_))
    rw [hcon k l (Finset.mem_range.mp hk) (Finset.mem_range.mp hl), zero_mul, zero_mul]
  obtain ⟨α, hα⟩ := pow_surjective (by omega) (by positivity) hcopr (C' / C)
  have hval : C * α ^ (1 + 2 ^ r) + C' * 1 ^ (1 + 2 ^ s) +
      (∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n, g k l * α ^ (2 ^ k) * 1 ^ (2 ^ l)) = 0 := by
    rw [hsum α 1, add_zero, hα, one_pow]
    field_simp
    rw [show (1 : GaloisField 2 n) + 1 = 0 from CharTwo.add_self_eq_zero 1, mul_zero]
  refine hani α 1 (by simp) ?_
  simpa using hval

/-- **Dispatch of the canonical form to the four cases.**

The hypotheses are the canonical data of `pinned_canonical` plus the case disjunction; the
conclusion is `Good n Q`, i.e. one of the three Higman normal forms. -/
theorem canonical_dispatch {n : ℕ} (hn : 2 ≤ n) {r s : ℕ} (hrn : r < n) (hsn : s < n)
    {C C' : GaloisField 2 n} (hC : C ≠ 0) (hC' : C' ≠ 0)
    {g : ℕ → ℕ → GaloisField 2 n}
    (Q : GaloisField 2 n × GaloisField 2 n → GaloisField 2 n)
    (hQ : ∀ α β : GaloisField 2 n, Q (α, β) = C * α ^ (1 + 2 ^ r) + C' * β ^ (1 + 2 ^ s) +
        ∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n, g k l * α ^ (2 ^ k) * β ^ (2 ^ l))
    (hani : ∀ v : GaloisField 2 n × GaloisField 2 n, v ≠ 0 → Q v ≠ 0)
    (hres : ∀ k l : ℕ, k < n → l < n → g k l ≠ 0 →
        (1 + 2 ^ s) * 2 ^ k + (1 + 2 ^ r) * 2 ^ l ≡ (1 + 2 ^ r) * (1 + 2 ^ s)
          [MOD 2 ^ n - 1])
    (hcopr : Nat.Coprime (1 + 2 ^ r) (2 ^ n - 1)) (hcops : Nat.Coprime (1 + 2 ^ s) (2 ^ n - 1))
    (hcase : (r = 0 ∧ s = 0) ∨ (r = s ∧ r ≠ 0) ∨ (r ≠ 0 ∧ s = 0) ∨
      (r ≠ 0 ∧ s ≠ 0 ∧ (r + s) % n ≠ 0 ∧ (r + n - s) % n ≠ 0)) :
    Good n Q := by
  rcases hcase with ⟨hr0, hs0⟩ | ⟨hrs, hrne⟩ | ⟨hrne, hs0⟩ | ⟨hrne, hsne, hrs, hrms⟩
  · subst hr0; subst hs0
    refine case_B_ab hn hC hC' Q hQ hani ?_
    intro k l hk hl hg
    have h := hres k l hk hl hg
    simpa only [pow_zero, Nat.add_zero, Nat.reduceAdd, Nat.add_one] using h
  · subst hrs
    refine case_B_r hn hrn hrne hcopr hC hC' Q hQ hani ?_
    intro k l hk hl hg
    exact hres k l hk hl hg
  · subst hs0
    have hresC : ∀ k l : ℕ, k < n → l < n → g k l ≠ 0 →
        2 * 2 ^ k + 2 ^ l * (1 + 2 ^ r) ≡ 2 * (1 + 2 ^ r) [MOD 2 ^ n - 1] := by
      intro k l hk hl hg
      have h := hres k l hk hl hg
      simpa only [pow_zero, Nat.add_zero, Nat.reduceAdd, Nat.mul_comm (1 + 2 ^ r)] using h
    have hsupp : ∃ k l : ℕ, k < n ∧ l < n ∧ g k l ≠ 0 := by
      refine support_nonempty (s := 0) hn hrn hC hC' hcopr ?_
      intro α β h
      rw [← hQ α β]
      exact hani (α, β) h
    rcases res_r_ab_pin hn hrn hrne hresC hsupp with ⟨h2r, hpin⟩ | ⟨h2r, hpin⟩
    · exact case_C_I hn hrn
        (eq_of_modEq_zero_of_pos_of_lt (by omega) (by omega) h2r) hC hC' Q hQ hani hpin
    · have h2r' : 2 * r = n + 1 := by
        have := eq_of_modEq_zero_of_pos_of_lt (n := n) (a := 2 * r - 1)
          (by omega) (by omega) h2r
        omega
      exact case_C_II hn hrn h2r' hC hC' Q hQ hani hpin
  · have hsupp : ∃ k l : ℕ, k < n ∧ l < n ∧ g k l ≠ 0 := by
      refine support_nonempty (s := s) hn hrn hC hC' hcopr ?_
      intro α β h
      rw [← hQ α β]
      exact hani (α, β) h
    exact case_D (s := s) hn hrn hsn hrne hsne hrs hrms hcopr hcops hC hC' Q hQ hani hres hsupp

end Work.Higman.Q3.L12
