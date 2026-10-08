/-
# Higman's Lemma 12: the second `C` case

The second shape of the `C` case of the case analysis of Higman's Lemma 12: one axis of the
pinned squaring form is abelian (`s = 0`) and the other has non-abelian type `r ≠ 0`, in the
branch `2 * r = n + 1` (equivalently `2 * r - 1 = n`) of the resonance congruence
`Work.Higman.Q3.L12.res_r_ab`.  Then the cross term sits at `(r - 1, r)`.

The first shape (`2 * r + 1 = n`, support `(n - 1, r + 1)`) is `case_C_I` of
`Q3/L12/case_C.lean`.  The second shape is reduced to the first by the Frobenius twist

    α ↦ α ^ (2 ^ (n - r))     (an additive bijection of `𝔽_{2ⁿ}`),

which sends the diagonal exponent `1 + 2 ^ r` to

    2 ^ (n - r) * (1 + 2 ^ r) = 2 ^ (n - r) + 2 ^ n ≡ 1 + 2 ^ (n - r)     (mod 2 ^ n - 1)

and the cross exponent `(r - 1, r)` to `(n - 1, n - r + 1)`.  Since `2 * r = n + 1`, the new type
`r' = n - r` satisfies `2 * r' + 1 = n` and `r' + 1 = r`, so the twisted form is exactly the input
of `Work.Higman.Q3.reduce_ab_r` with `r'` in place of `r`.
-/

import Mathlib
import Submission.Work.Higman.Q3.L12.case_core
import Submission.Work.Higman.Q3.L12.case_C

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

/-- With `2 * r = n + 1`, the Frobenius twist `α ↦ α ^ (2 ^ (n - r))` turns the diagonal
exponent `1 + 2 ^ r` into `1 + 2 ^ (n - r)`. -/
lemma twist_exp_diag {n r : ℕ} (hn : 1 ≤ n) (h2r : 2 * r = n + 1) (x : GaloisField 2 n) :
    (x ^ (2 ^ (n - r))) ^ (1 + 2 ^ r) = x ^ (1 + 2 ^ (n - r)) := by
  have hexp : 2 ^ (n - r) * (1 + 2 ^ r) = 2 ^ (n - r) + 2 ^ n := by
    rw [mul_add, mul_one, ← pow_add, show n - r + r = n by omega]
  rw [← pow_mul, hexp, pow_add, pow_two_pow_card hn x, mul_comm,
    ← pow_succ' x (2 ^ (n - r)), Nat.add_comm (2 ^ (n - r)) 1]

/-- With `1 ≤ r` and `2 * r = n + 1`, the Frobenius twist `α ↦ α ^ (2 ^ (n - r))` sends the
cross exponent `(r - 1, r)` to `(n - 1, n - r + 1)`. -/
lemma twist_exp_cross {n r : ℕ} (hn : 1 ≤ n) (hr1 : 1 ≤ r) (h2r : 2 * r = n + 1)
    (x : GaloisField 2 n) :
    (x ^ (2 ^ (n - r))) ^ (2 ^ (r - 1)) = x ^ (2 ^ (n - 1)) := by
  rw [← pow_mul, show 2 ^ (n - r) * 2 ^ (r - 1) = 2 ^ (n - 1) by
    rw [← pow_add, show n - r + (r - 1) = n - 1 by omega]]

/-- The same twist applied to the second coordinate exponent: `r = (n - r) + 1`. -/
lemma twist_exp_second {n r : ℕ} (h2r : 2 * r = n + 1) (y : GaloisField 2 n) :
    y ^ (2 ^ r) = y ^ (2 ^ (n - r + 1)) := by
  rw [show n - r + 1 = r by omega]

theorem case_C_II {n r : ℕ} (hn : 2 ≤ n) (hr : r < n) (h2r : 2 * r = n + 1)
    {C C' : GaloisField 2 n} (hC : C ≠ 0) (hC' : C' ≠ 0)
    {g : ℕ → ℕ → GaloisField 2 n}
    (Q : GaloisField 2 n × GaloisField 2 n → GaloisField 2 n)
    (hQ : ∀ α β : GaloisField 2 n, Q (α, β) = C * α ^ (1 + 2 ^ r) + C' * β ^ 2 +
        ∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n, g k l * α ^ (2 ^ k) * β ^ (2 ^ l))
    (hani : ∀ v : GaloisField 2 n × GaloisField 2 n, v ≠ 0 → Q v ≠ 0)
    (hsup : ∀ k l : ℕ, k < n → l < n → g k l ≠ 0 → k = r - 1 ∧ l = r) :
    Work.Higman.Q3.L12.Good n Q := by
  have hn1 : 1 ≤ n := by omega
  have hn0 : 0 < n := by omega
  have hr1 : 1 ≤ r := by omega
  -- The twisted type `r' = n - r` satisfies `2 * r' + 1 = n` and `r' + 1 = r`.
  have hr' : 2 * (n - r) + 1 = n := by omega
  have hr'1 : n - r + 1 = r := by omega
  -- Collapse the double sum: the support is the single point `(r - 1, r)`.
  have hQ' : ∀ α β : GaloisField 2 n,
      Q (α, β) = C * α ^ (1 + 2 ^ r) + C' * β ^ 2 +
        g (r - 1) r * α ^ (2 ^ (r - 1)) * β ^ (2 ^ r) := by
    intro α β
    rw [hQ α β, sum_single (show r - 1 < n by omega) hr hsup α β]
  -- The Frobenius twist `(α, β) ↦ (α ^ (2 ^ (n - r)), β)`.
  let Φ₀ : GaloisField 2 n × GaloisField 2 n ≃+ GaloisField 2 n × GaloisField 2 n :=
    AddEquiv.prodCongr ((frob n ^ (n - r)).toAddEquiv) (AddEquiv.refl (GaloisField 2 n))
  -- The twisted form has diagonal exponent `1 + 2 ^ (n - r)` and cross exponent
  -- `(n - 1, n - r + 1)`, the input shape of `reduce_ab_r`.
  have htwist : ∀ w : GaloisField 2 n × GaloisField 2 n,
      Q (Φ₀ w) = C * w.1 ^ (1 + 2 ^ (n - r)) + C' * w.2 ^ 2 +
        g (r - 1) r * w.1 ^ (2 ^ (n - 1)) * w.2 ^ (2 ^ (n - r + 1)) := by
    rintro ⟨a, b⟩
    have h1 : (Φ₀ (a, b)).1 = a ^ (2 ^ (n - r)) := by
      show (frob n ^ (n - r)) a = a ^ (2 ^ (n - r))
      rw [frob_pow_apply]
    have h2 : (Φ₀ (a, b)).2 = b := rfl
    have hA : (a ^ (2 ^ (n - r))) ^ (1 + 2 ^ r) = a ^ (1 + 2 ^ (n - r)) :=
      twist_exp_diag hn1 h2r a
    have hB : (a ^ (2 ^ (n - r))) ^ (2 ^ (r - 1)) = a ^ (2 ^ (n - 1)) :=
      twist_exp_cross hn1 hr1 h2r a
    have hCb : b ^ (2 ^ r) = b ^ (2 ^ (n - r + 1)) := twist_exp_second h2r b
    rw [show Q (Φ₀ (a, b)) = Q ((Φ₀ (a, b)).1, (Φ₀ (a, b)).2) from rfl,
      hQ' _ _, h1, h2, hA, hB, hCb]
  -- `reduce_ab_r` with the type `n - r` normalises the twisted form.
  obtain ⟨Φ₁, Ψ₁, ε, hred⟩ :=
    reduce_ab_r (n := n) hn1 (r := n - r) hr' (C := C) (C' := C')
      (f := g (r - 1) r) hC hC'
  have hkey : ∀ v : GaloisField 2 n × GaloisField 2 n,
      Ψ₁ (Q ((Φ₁.trans Φ₀) v)) =
        cCocycle (GaloisField 2 n)
          ((frob n ^ (n - r) : GaloisField 2 n ≃+* GaloisField 2 n)) ε v v := by
    intro v
    show Ψ₁ (Q (Φ₀ (Φ₁ v))) = _
    rw [htwist (Φ₁ v), hred v, cCocycle_frob_self (n := n) (r := n - r) hn1 v ε]
    ring
  -- Anisotropy of `Q` transfers to the `cCocycle` squaring form, giving the Column-III
  -- condition on `ε`.
  have haniC : ∀ u : GaloisField 2 n × GaloisField 2 n, u ≠ 0 →
      cCocycle (GaloisField 2 n)
        ((frob n ^ (n - r) : GaloisField 2 n ≃+* GaloisField 2 n)) ε u u ≠ 0 :=
    aniso_transfer hkey hani
  have hε : ∀ ρ : GaloisField 2 n,
      ε ≠ ρ⁻¹ + ((frob n ^ (n - r) : GaloisField 2 n ≃+* GaloisField 2 n)) ρ ^ 2 * ρ :=
    epsilon_C_of_anisotropic _ ε haniC
  -- The `C` condition `2 θ ^ 2 = 1`: `θ = frob ^ (n - r)` and `2 * (n - r) + 1 = n`.
  have h2n : 2 ^ (n - r) * (2 ^ (n - r) * 2) = 2 ^ n := by
    rw [show 2 ^ (n - r) * 2 = 2 ^ (n - r + 1) from (pow_succ 2 (n - r)).symm, ← pow_add,
      show n - r + (n - r + 1) = n by omega]
  have hθ : ∀ a : GaloisField 2 n,
      (((frob n ^ (n - r) : GaloisField 2 n ≃+* GaloisField 2 n))
        (((frob n ^ (n - r)) a))) ^ 2 = a := by
    intro a
    have h1 : ((frob n ^ (n - r)) ((frob n ^ (n - r)) a)) ^ 2 =
        a ^ (2 ^ (n - r) * (2 ^ (n - r) * 2)) := by
      rw [frob_pow_apply, frob_pow_apply, ← pow_mul, ← pow_mul]
    rw [h1, h2n]
    exact pow_two_pow_card hn1 a
  -- `n gcd (n - r) = 1`, so `frob ^ (n - r)` has odd order `n`.
  have hodd : Odd (orderOf (frob n ^ (n - r) : GaloisField 2 n ≃+* GaloisField 2 n)) := by
    rw [orderOf_frobeniusEquiv_pow n (n - r) hn0]
    have hgc : n.gcd (n - r) = 1 := by
      have h1 : n.gcd (n - r) ∣ n := Nat.gcd_dvd_left n (n - r)
      have h2 : n.gcd (n - r) ∣ 2 * (n - r) :=
        Dvd.dvd.mul_left (Nat.gcd_dvd_right n (n - r)) 2
      have h4 : n.gcd (n - r) ∣ n - 1 := by
        rw [← show 2 * (n - r) = n - 1 by omega]; exact h2
      have h5 : n.gcd (n - r) ∣ 1 := by
        have h6 : n - (n - 1) = 1 := by omega
        rw [← h6]
        exact Nat.dvd_sub h1 h4
      exact Nat.dvd_one.mp h5
    rw [hgc, Nat.div_one]
    exact ⟨n - r, hr'.symm⟩
  exact ⟨_, ε, Φ₁.trans Φ₀, Ψ₁, hodd, Or.inr (Or.inl ⟨hθ, hε, hkey⟩)⟩

end Work.Higman.Q3.L12
