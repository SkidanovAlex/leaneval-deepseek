import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Commutators of normal-form elements lie in `⟨c ^ p⟩`

Let `X` be a group, `p` a natural number (in the intended application an odd prime), and let
`c, y ∈ X` with `orderOf c = p ^ 2` and `y⁻¹ * c * y = c ^ (1 + m * p)`.  Then the commutator of
two elements of the normal form `c ^ i * y ^ j` lies in the cyclic subgroup `⟨c ^ p⟩`.

The two ingredients are
* the conjugation formula `c ^ a * y ^ b = y ^ b * c ^ (a * (1 + m * p) ^ b)` (valid for natural
  exponents, derived from the `b = 1` case by induction);
* the centrality of `c ^ p` in `⟨c, y⟩`, which follows from `y⁻¹ * c ^ p * y = c ^ ((1+m*p)*p)
  = c ^ p` since `c ^ (p ^ 2) = 1`.

Writing `u = c ^ i * y ^ j` and `u' = c ^ i' * y ^ j'` one then computes
`u * u' = y ^ (j + j') * c ^ A`, `u' * u = y ^ (j + j') * c ^ B` with
`A = i * (1 + m * p) ^ (j + j') + i' * (1 + m * p) ^ j'` and
`B = i' * (1 + m * p) ^ (j + j') + i * (1 + m * p) ^ j`, whence
`⁅u, u'⁆ = c ^ (A - B)`; and `p ∣ A - B` because `1 + m * p ≡ 1 (mod p)`.  So
`⁅u, u'⁆ = (c ^ p) ^ K ∈ ⟨c ^ p⟩`.
-/

namespace Work.PGroup.Symplectic

open scoped commutatorElement

set_option linter.unusedVariables false

theorem commutator_mem_zpowers_of_normal_form {X : Type*} [Group X] {p m : ℕ} (hp : p.Prime)
    (hodd : p ≠ 2) {c y : X} (hc : orderOf c = p ^ 2) (hy : y ^ p = 1)
    (hconj : y⁻¹ * c * y = c ^ (1 + m * p))
    {u u' : X} (hu : ∃ i j : ℕ, u = c ^ i * y ^ j) (hu' : ∃ i' j' : ℕ, u' = c ^ i' * y ^ j') :
    ⁅u, u'⁆ ∈ Subgroup.zpowers (c ^ p) := by
  -- Conjugation by `y ^ j` acts on `c` by the exponent `(1 + m * p) ^ j`.
  have hyc : ∀ j : ℕ, (y^j)⁻¹ * c * y^j = c ^ ((1+m*p)^j) := by
    intro j
    induction j with
    | zero => simp
    | succ k ih =>
      have hstep : (y ^ (k+1))⁻¹ * c * y ^ (k+1) = y⁻¹ * ((y^k)⁻¹ * c * y^k) * y := by
        rw [pow_succ, mul_inv_rev]; group
      rw [hstep, ih]
      have hconv : y⁻¹ * c ^ ((1+m*p)^k) * y = ((y⁻¹) * c * (y⁻¹)⁻¹) ^ ((1+m*p)^k) := by
        rw [conj_pow, inv_inv]
      rw [hconv, inv_inv, hconj, ← pow_mul, pow_succ']
  -- Hence `c ^ a * y ^ b = y ^ b * c ^ (a * (1 + m * p) ^ b)`.
  have hcy : ∀ a b : ℕ, c^a * y^b = y^b * c^(a * (1+m*p)^b) := by
    intro a b
    have h1 : (y^b)⁻¹ * c^a * y^b = c ^ (a * (1+m*p)^b) := by
      have hconv : (y^b)⁻¹ * c^a * y^b = ((y^b)⁻¹ * c * (y^b)⁻¹⁻¹) ^ a := by
        rw [conj_pow, inv_inv]
      rw [hconv, inv_inv, hyc b, ← pow_mul, mul_comm]
    calc c^a * y^b = y^b * ((y^b)⁻¹ * c^a * y^b) := by group
      _ = y^b * c^(a * (1+m*p)^b) := by rw [h1]
  -- `c ^ p` is centralized by `y` (so also by every power of `y`).
  have hcomm_cp_y : Commute (c^p) y := by
    have hcp2 : c ^ (p^2) = 1 := by rw [← hc]; exact pow_orderOf_eq_one c
    have hycp : y⁻¹ * c^p * y = c^p := by
      have h1 : y⁻¹ * c^p * y = (y⁻¹ * c * (y⁻¹)⁻¹)^p := by rw [conj_pow, inv_inv]
      rw [h1, inv_inv, hconj, ← pow_mul]
      have hexp : (1 + m*p) * p = p + m * p^2 := by ring
      rw [hexp, pow_add, mul_comm m (p^2), pow_mul, hcp2, one_pow, mul_one]
    show c^p * y = y * c^p
    calc c^p * y = y * (y⁻¹ * c^p * y) := by group
      _ = y * c^p := by rw [hycp]
  -- `p ∣ (1 + m * p) ^ k - 1`.
  have hdvd : ∀ k : ℕ, (p:ℤ) ∣ ((1 + m*p : ℕ) : ℤ)^k - 1 := by
    intro k
    obtain ⟨K, hK⟩ : ∃ K : ℕ, (1+m*p)^k = 1 + p*K := by
      induction k with
      | zero => exact ⟨0, by ring⟩
      | succ k ih =>
        obtain ⟨K, hK⟩ := ih
        exact ⟨m + K + K*m*p, by rw [pow_succ, hK]; ring⟩
    refine ⟨(K:ℤ), ?_⟩
    have : ((1+m*p:ℕ):ℤ)^k = 1 + (p:ℤ)*K := by
      rw [← Nat.cast_pow, hK]; push_cast; ring
    rw [this]; ring
  obtain ⟨i, j, rfl⟩ := hu
  obtain ⟨i', j', rfl⟩ := hu'
  set A : ℕ := i * (1+m*p)^(j+j') + i' * (1+m*p)^j' with hAdef
  set B : ℕ := i' * (1+m*p)^(j+j') + i * (1+m*p)^j with hBdef
  -- `p` divides `A - B`.
  have hAdiv : (p:ℤ) ∣ (A:ℤ) - (B:ℤ) := by
    rw [hAdef, hBdef]
    have hcastA : ((i * (1+m*p)^(j+j') + i' * (1+m*p)^j' : ℕ):ℤ)
        = (i:ℤ) * ((1+m*p:ℕ):ℤ)^(j+j') + (i':ℤ) * ((1+m*p:ℕ):ℤ)^j' := by push_cast; ring
    have hcastB : ((i' * (1+m*p)^(j+j') + i * (1+m*p)^j : ℕ):ℤ)
        = (i':ℤ) * ((1+m*p:ℕ):ℤ)^(j+j') + (i:ℤ) * ((1+m*p:ℕ):ℤ)^j := by push_cast; ring
    rw [hcastA, hcastB, pow_add]
    have e1 : (p:ℤ) ∣ (i:ℤ) * ((1+m*p:ℕ):ℤ)^j * (((1+m*p:ℕ):ℤ)^j' - 1) :=
      dvd_mul_of_dvd_right (hdvd j') _
    have e2 : (p:ℤ) ∣ (i':ℤ) * ((1+m*p:ℕ):ℤ)^j' * (1 - ((1+m*p:ℕ):ℤ)^j) :=
      dvd_mul_of_dvd_right (by simpa using dvd_neg.mpr (hdvd j)) _
    have hEq : (i:ℤ) * (((1+m*p:ℕ):ℤ)^j * ((1+m*p:ℕ):ℤ)^j') + (i':ℤ) * ((1+m*p:ℕ):ℤ)^j'
          - ((i':ℤ) * (((1+m*p:ℕ):ℤ)^j * ((1+m*p:ℕ):ℤ)^j') + (i:ℤ) * ((1+m*p:ℕ):ℤ)^j)
        = (i:ℤ) * ((1+m*p:ℕ):ℤ)^j * (((1+m*p:ℕ):ℤ)^j' - 1)
          + (i':ℤ) * ((1+m*p:ℕ):ℤ)^j' * (1 - ((1+m*p:ℕ):ℤ)^j) := by ring
    rw [hEq]
    exact dvd_add e1 e2
  obtain ⟨K, hK⟩ := hAdiv
  refine Subgroup.mem_zpowers_iff.mpr ⟨K, ?_⟩
  -- Normal forms of the products.
  have huu : c^i * y^j * (c^i' * y^j') = y^(j+j') * c^A := by
    rw [hAdef]
    calc c^i * y^j * (c^i' * y^j')
        = c^i * (y^j * (c^i' * y^j')) := by rw [mul_assoc]
      _ = c^i * (y^j * (y^j' * c^(i' * (1+m*p)^j'))) := by rw [hcy i' j']
      _ = c^i * ((y^j * y^j') * c^(i' * (1+m*p)^j')) := by rw [← mul_assoc (y^j) (y^j') _]
      _ = c^i * (y^(j+j') * c^(i' * (1+m*p)^j')) := by rw [← pow_add]
      _ = (c^i * y^(j+j')) * c^(i' * (1+m*p)^j') := by rw [← mul_assoc]
      _ = (y^(j+j') * c^(i * (1+m*p)^(j+j'))) * c^(i' * (1+m*p)^j') := by rw [hcy i (j+j')]
      _ = y^(j+j') * (c^(i * (1+m*p)^(j+j')) * c^(i' * (1+m*p)^j')) := by rw [mul_assoc]
      _ = y^(j+j') * c^(i * (1+m*p)^(j+j') + i' * (1+m*p)^j') := by rw [← pow_add]
  have hu'u : c^i' * y^j' * (c^i * y^j) = y^(j+j') * c^B := by
    rw [hBdef]
    calc c^i' * y^j' * (c^i * y^j)
        = c^i' * (y^j' * (c^i * y^j)) := by rw [mul_assoc]
      _ = c^i' * (y^j' * (y^j * c^(i * (1+m*p)^j))) := by rw [hcy i j]
      _ = c^i' * ((y^j' * y^j) * c^(i * (1+m*p)^j)) := by rw [← mul_assoc (y^j') (y^j) _]
      _ = c^i' * (y^(j'+j) * c^(i * (1+m*p)^j)) := by rw [← pow_add]
      _ = (c^i' * y^(j'+j)) * c^(i * (1+m*p)^j) := by rw [← mul_assoc]
      _ = (y^(j'+j) * c^(i' * (1+m*p)^(j'+j))) * c^(i * (1+m*p)^j) := by rw [hcy i' (j'+j)]
      _ = y^(j'+j) * (c^(i' * (1+m*p)^(j'+j)) * c^(i * (1+m*p)^j)) := by rw [mul_assoc]
      _ = y^(j'+j) * c^(i' * (1+m*p)^(j'+j) + i * (1+m*p)^j) := by rw [← pow_add]
      _ = y^(j+j') * c^(i' * (1+m*p)^(j+j') + i * (1+m*p)^j) := by rw [Nat.add_comm j' j]
  -- The commutator in terms of `A` and `B`.
  have hcomm : ⁅c^i * y^j, c^i' * y^j'⁆ = y^(j+j') * c^A * (y^(j+j') * c^B)⁻¹ := by
    rw [commutatorElement_def, huu]
    rw [mul_assoc]
    rw [← mul_inv_rev (c^i' * y^j') (c^i * y^j)]
    rw [hu'u]
  -- `c ^ A * (c ^ B)⁻¹ = (c ^ p) ^ K`.
  have hAB : c^A * (c^B)⁻¹ = (c^p)^K := by
    rw [← zpow_natCast c A, ← zpow_natCast c B, ← zpow_neg, ← zpow_add]
    have hK' : (A:ℤ) + -(B:ℤ) = (p:ℤ) * K := by
      rw [sub_eq_add_neg] at hK; exact hK
    rw [hK', zpow_mul, zpow_natCast]
  -- Since `c ^ p` is central in `⟨c, y⟩`, the `y`-conjugation is invisible.
  have hfinal : y^(j+j') * c^A * (y^(j+j') * c^B)⁻¹ = (c^p)^K := by
    have hre : y^(j+j') * c^A * (y^(j+j') * c^B)⁻¹
        = y^(j+j') * (c^A * (c^B)⁻¹) * (y^(j+j'))⁻¹ := by
      rw [mul_inv_rev]; group
    rw [hre, hAB]
    have hcommX : Commute ((c^p)^K) (y^(j+j')) := (hcomm_cp_y.zpow_left K).pow_right (j+j')
    rw [← hcommX.eq, mul_assoc, mul_inv_cancel, mul_one]
  rw [hcomm]
  exact hfinal.symm

end Work.PGroup.Symplectic
