/-
# Higman's Lemma 12: the `C` case

The `C` case of the case analysis of Higman's Lemma 12: one axis of the pinned squaring form is
abelian (`s = 0`) and the other has non-abelian type `r ≠ 0`.

With the canonical normalisation of `Q3/L12/case_core.lean`, the resonance congruence reads

    2 * 2 ^ k + 2 ^ l * (1 + 2 ^ r) ≡ 2 * (1 + 2 ^ r)      (mod 2 ^ n - 1)

and `Work.Higman.Q3.L12.res_r_ab` shows that either `2 r + 1 ≡ 0` with support `(n-1, r+1)`, or
`2 r - 1 ≡ 0` with support `(r-1, r)`.  The first shape is `reduce_ab_r`'s hypothesis; the second
becomes the first after the extra twist `α ↦ α ^ (2 ^ (n-r))` (which replaces `r` by `n - r`), so
it is reduced to the first.
-/

import Mathlib
import Submission.Work.Higman.Q3.L12.case_core

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

/-- `sqrtF x = x ^ (2 ^ (n - 1))` for `𝔽_{2 ^ n}`. -/
lemma sqrtF_eq_pow {n : ℕ} (hn : 1 ≤ n) (x : GaloisField 2 n) :
    sqrtF (GaloisField 2 n) x = x ^ (2 ^ (n - 1)) := by
  have h1 : (frobeniusEquiv (GaloisField 2 n) 2) (x ^ (2 ^ (n - 1))) = x := by
    change (x ^ (2 ^ (n - 1))) ^ 2 = x
    rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel hn, pow_two_pow_card hn]
  rw [sqrtF]
  conv_lhs => rw [← h1]
  exact RingEquiv.symm_apply_apply _ _

/-- The squaring form of `cCocycle` with `θ = frob ^ r`, in coordinates. -/
lemma cCocycle_frob_self {n r : ℕ} (hn : 1 ≤ n)
    (v : GaloisField 2 n × GaloisField 2 n) (ε : GaloisField 2 n) :
    cCocycle (GaloisField 2 n) ((frob n ^ r : GaloisField 2 n ≃+* GaloisField 2 n)) ε v v =
      v.1 ^ (1 + 2 ^ r) + ε * (v.1 ^ (2 ^ (n - 1)) * v.2 ^ (2 ^ (r + 1))) + v.2 ^ 2 := by
  have hs : sqrtF (GaloisField 2 n) v.1 = v.1 ^ (2 ^ (n - 1)) := sqrtF_eq_pow hn v.1
  have h2 : (frob n ^ r) (v.2 * v.2) = v.2 ^ (2 ^ (r + 1)) := by
    rw [frob_pow_apply, ← pow_two, ← pow_mul, ← pow_succ']
  have h1 : v.1 * v.1 ^ (2 ^ r) = v.1 ^ (1 + 2 ^ r) := mul_pow_two_pow_eq v.1
  simp only [cCocycle, frob_pow_apply, hs, h2, ← pow_two v.2]
  rw [h1]
  ring

/-- **Case `C`, first shape**: diagonal `C α ^ (1 + 2 ^ r) + C' β ^ 2` with `2 r + 1 = n` and
support at `(n - 1, r + 1)`.  `reduce_ab_r` brings it to the `cCocycle` squaring form with
`θ = frob ^ r`. -/
theorem case_C_I {n r : ℕ} (hn : 2 ≤ n) (hr : r < n) (h2r : 2 * r + 1 = n)
    {C C' : GaloisField 2 n} (hC : C ≠ 0) (hC' : C' ≠ 0)
    {g : ℕ → ℕ → GaloisField 2 n}
    (Q : GaloisField 2 n × GaloisField 2 n → GaloisField 2 n)
    (hQ : ∀ α β : GaloisField 2 n, Q (α, β) = C * α ^ (1 + 2 ^ r) + C' * β ^ 2 +
        ∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n, g k l * α ^ (2 ^ k) * β ^ (2 ^ l))
    (hani : ∀ v : GaloisField 2 n × GaloisField 2 n, v ≠ 0 → Q v ≠ 0)
    (hsup : ∀ k l : ℕ, k < n → l < n → g k l ≠ 0 → k = n - 1 ∧ l = r + 1) :
    Good n Q := by
  have hn1 : 0 < n := by omega
  have hrn : r + 1 < n := by omega
  have h1n : n - 1 < n := by omega
  have hQ' : ∀ α β : GaloisField 2 n, Q (α, β) = C * α ^ (1 + 2 ^ r) + C' * β ^ 2 +
      g (n - 1) (r + 1) * α ^ (2 ^ (n - 1)) * β ^ (2 ^ (r + 1)) := by
    intro α β
    rw [hQ α β, sum_single h1n hrn hsup α β]
  obtain ⟨Φ, Ψ, ε, hΦΨ⟩ :=
    reduce_ab_r (n := n) (hn := by omega) (r := r) (C := C) (C' := C')
      (f := g (n - 1) (r + 1)) h2r hC hC'
  have hkey : ∀ v : GaloisField 2 n × GaloisField 2 n,
      Ψ (Q (Φ v)) = cCocycle (GaloisField 2 n)
        ((frob n ^ r : GaloisField 2 n ≃+* GaloisField 2 n)) ε v v := by
    intro v
    have h1 : Ψ (Q (Φ v)) = v.1 ^ (1 + 2 ^ r) + ε *
        (v.1 ^ (2 ^ (n - 1)) * v.2 ^ (2 ^ (r + 1))) + v.2 ^ 2 := by
      rw [hQ']
      have h := hΦΨ v
      simp only [add_assoc, mul_assoc] at h ⊢
      exact h
    rw [h1, ← cCocycle_frob_self (by omega : 1 ≤ n) v ε]
  have haniC := aniso_transfer hkey hani
  have hε := epsilon_C_of_anisotropic
    ((frob n ^ r : GaloisField 2 n ≃+* GaloisField 2 n)) ε haniC
  have h2n : 2 ^ r * (2 ^ r * 2) = 2 ^ n := by
    rw [show 2 ^ r * 2 = 2 ^ (r + 1) from (pow_succ 2 r).symm, ← pow_add,
      show r + (r + 1) = n by omega]
  have hθ : ∀ a : GaloisField 2 n,
      (((frob n ^ r : GaloisField 2 n ≃+* GaloisField 2 n))
        (((frob n ^ r : GaloisField 2 n ≃+* GaloisField 2 n)) a)) ^ 2 = a := by
    intro a
    have h1 : ((frob n ^ r) ((frob n ^ r) a)) ^ 2 = a ^ (2 ^ r * (2 ^ r * 2)) := by
      rw [frob_pow_apply, frob_pow_apply, ← pow_mul, ← pow_mul]
    rw [h1, h2n]
    exact pow_two_pow_card (by omega) a
  have hgc : n.gcd r = 1 := by
    have h1 : n.gcd r ∣ n := Nat.gcd_dvd_left n r
    have h2 : n.gcd r ∣ 2 * r := Dvd.dvd.mul_left (Nat.gcd_dvd_right n r) 2
    have h3 : 2 * r = n - 1 := by omega
    have h4 : n.gcd r ∣ n - 1 := by rw [← h3]; exact h2
    have h5 : n.gcd r ∣ 1 := by
      have h6 : n - (n - 1) = 1 := by omega
      rw [← h6]
      exact Nat.dvd_sub h1 h4
    exact Nat.dvd_one.mp h5
  have hodd : Odd (orderOf (frob n ^ r : GaloisField 2 n ≃+* GaloisField 2 n)) := by
    rw [orderOf_frobeniusEquiv_pow n r (by omega), hgc, Nat.div_one]
    exact ⟨r, h2r.symm⟩
  exact ⟨_, ε, Φ, Ψ, hodd, Or.inr (Or.inl ⟨hθ, hε, hkey⟩)⟩

end Work.Higman.Q3.L12
