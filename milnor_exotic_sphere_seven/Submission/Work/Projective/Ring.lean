import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The cohomology ring `H^*(ℂPⁿ; ℤ) = ℤ[h]/(h^{n+1})`

This module builds the *abstract* cohomology ring of complex projective space, the ring in which
the Chern and Pontryagin classes of `TℂPⁿ` are computed:

* `Work.Projective.CPRing n := Polynomial ℤ ⧸ (X^(n+1))` — the truncated polynomial ring, our model
  of `H^*(ℂPⁿ;ℤ)`;
* `Work.Projective.hC n` — the hyperplane class `h` (the generator of `H²(ℂPⁿ;ℤ)`), with
  `Work.Projective.hC_pow_succ : h^(n+1) = 0` and `Work.Projective.hC_pow_ne_zero : h^k ≠ 0` for
  `k ≤ n`;
* `Work.Projective.coeffFun n k` — the `k`-th coefficient functional, i.e. the projection onto
  `H^{2k}(ℂPⁿ;ℤ) = ℤ⟨h^k⟩`, with `coeffFun_mk_apply`, `coeffFun_hC_pow` and its linearity
  (`coeffFun_add`, `coeffFun_smul`);
* `Work.Projective.fundClass` — **the fundamental class functional** `⟨·, [ℂPⁿ]⟩`, the top
  coefficient `coeffFun n n`; thus `⟨h^k, [ℂPⁿ]⟩ = 1` for `k = n` and `0` for `k < n`
  (`fundClass_hC_pow`).

The convention is that a cohomology class in `H^{2k}(ℂPⁿ;ℤ)` is a multiple of `h^k` and that the
pairing with the fundamental class is `fundClass`.  The Chern and Pontryagin classes of `TℂPⁿ` are
computed in `Work.Projective.Chern` (`c(TℂPⁿ) = (1+h)^{n+1}`, `p₁ = (n+1)h²`,
`p₂ = C(n+1,2)h⁴`), and the numbers `(σ, p₁², p₂)` in `Work.Projective.Numbers`.

## Main definitions and results

* `Work.Projective.CPRing`, `Work.Projective.relIdeal`, `Work.Projective.hC`;
* `Work.Projective.hC_pow_succ`, `Work.Projective.hC_pow_ne_zero`;
* `Work.Projective.coeffFun`, `Work.Projective.coeffFun_mk_apply`, `Work.Projective.coeffFun_hC_pow`;
* `Work.Projective.fundClass`, `Work.Projective.fundClass_mk_apply`,
  `Work.Projective.fundClass_hC_pow`, `Work.Projective.fundClass_hC_pow_self`.
-/

set_option maxHeartbeats 800000

namespace Work.Projective

noncomputable section

/-- The ideal `(X^(n+1)) ⊆ ℤ[X]`. -/
def relIdeal (n : ℕ) : Ideal (Polynomial ℤ) := Ideal.span {Polynomial.X ^ (n + 1)}

/-- **The cohomology ring of `ℂPⁿ`**: `ℤ[h]/(h^{n+1})`, as the quotient of the polynomial ring by
`X^(n+1)`. -/
abbrev CPRing (n : ℕ) : Type := Polynomial ℤ ⧸ relIdeal n

/-- **The hyperplane class** `h ∈ H²(ℂPⁿ;ℤ)`, the generator of the truncated polynomial ring. -/
def hC (n : ℕ) : CPRing n := Ideal.Quotient.mk _ Polynomial.X

theorem hC_pow (n k : ℕ) : hC n ^ k = Ideal.Quotient.mk _ (Polynomial.X ^ k) := by
  rw [hC, ← map_pow]

/-- **`h^(n+1) = 0`**: the defining relation of the cohomology ring of `ℂPⁿ`. -/
theorem hC_pow_succ (n : ℕ) : hC n ^ (n + 1) = 0 := by
  rw [hC_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span rfl

/-- A polynomial all of whose coefficients in degrees `≤ n` vanish is a multiple of `X^(n+1)`. -/
theorem mem_relIdeal_iff (n : ℕ) (p : Polynomial ℤ) :
    p ∈ relIdeal n ↔ ∀ k ≤ n, p.coeff k = 0 := by
  unfold relIdeal
  rw [Ideal.mem_span_singleton, Polynomial.X_pow_dvd_iff]
  constructor
  · intro h k hk
    exact h k (Nat.lt_succ_of_le hk)
  · intro h k hk
    exact h k (Nat.lt_succ_iff.mp hk)

/-- Two polynomials with the same class in `ℤ[h]/(h^{n+1})` have the same coefficients in all
degrees `≤ n`. -/
theorem coeff_eq_of_sub_mem {n : ℕ} {p q : Polynomial ℤ} (h : p - q ∈ relIdeal n) {k : ℕ}
    (hk : k ≤ n) : p.coeff k = q.coeff k := by
  have h' := (mem_relIdeal_iff n (p - q)).mp h k hk
  rw [Polynomial.coeff_sub, sub_eq_zero] at h'
  exact h'

/-! ## The coefficient functionals -/

/-- **The `k`-th coefficient functional** `H^*(ℂPⁿ;ℤ) → ℤ` for `k : Fin (n+1)`: the coefficient of
`X^k` of a representative polynomial, i.e. the projection onto the degree-`2k` part `ℤ⟨h^k⟩`. -/
def coeffFun (n : ℕ) (k : Fin (n + 1)) : CPRing n → ℤ := fun x => (Quotient.out x).coeff k

/-- **The computation rule for `coeffFun`** on the class of a polynomial `p`: the coefficient of
`X^k` in `p` (independent of the representative, by `coeff_eq_of_sub_mem`). -/
theorem coeffFun_mk_apply (n : ℕ) (k : Fin (n + 1)) (p : Polynomial ℤ) :
    coeffFun n k (Ideal.Quotient.mk _ p) = p.coeff k := by
  have h : Quotient.out (Ideal.Quotient.mk (relIdeal n) p) - p ∈ relIdeal n := by
    rw [← Ideal.Quotient.eq]
    rw [show Ideal.Quotient.mk (relIdeal n) (Quotient.out (Ideal.Quotient.mk (relIdeal n) p)) =
      Ideal.Quotient.mk (relIdeal n) p from Quotient.out_eq _]
  show (Quotient.out (Ideal.Quotient.mk (relIdeal n) p)).coeff (k : ℕ) = p.coeff k
  exact coeff_eq_of_sub_mem h (Nat.lt_succ_iff.mp k.isLt)

/-- `coeffFun` is additive. -/
theorem coeffFun_add (n : ℕ) (k : Fin (n + 1)) (x y : CPRing n) :
    coeffFun n k (x + y) = coeffFun n k x + coeffFun n k y := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [← map_add, coeffFun_mk_apply, coeffFun_mk_apply, coeffFun_mk_apply, Polynomial.coeff_add]

/-- `coeffFun` is `ℤ`-linear. -/
theorem coeffFun_smul (n : ℕ) (k : Fin (n + 1)) (a : ℤ) (x : CPRing n) :
    coeffFun n k (a • x) = a * coeffFun n k x := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [← map_zsmul, coeffFun_mk_apply, coeffFun_mk_apply, Polynomial.coeff_smul, smul_eq_mul]

/-- `coeffFun` as a bundled `ℤ`-linear map. -/
def coeffFunₗ (n : ℕ) (k : Fin (n + 1)) : CPRing n →ₗ[ℤ] ℤ where
  toFun := coeffFun n k
  map_add' := coeffFun_add n k
  map_smul' := coeffFun_smul n k

@[simp] theorem coeffFunₗ_apply (n : ℕ) (k : Fin (n + 1)) (x : CPRing n) :
    coeffFunₗ n k x = coeffFun n k x := rfl

/-- **The coefficient of `h^k` in `h^j`**: `1` if `k = j` and `0` otherwise. -/
theorem coeffFun_hC_pow (n : ℕ) (j : Fin (n + 1)) (k : Fin (n + 1)) :
    coeffFun n k (hC n ^ (j : ℕ)) = if k = j then 1 else 0 := by
  rw [hC_pow, coeffFun_mk_apply, Polynomial.coeff_X_pow]
  by_cases h : k = j
  · subst h; rw [if_pos rfl, if_pos rfl]
  · rw [if_neg (fun hh => h (Fin.ext hh)), if_neg h]

/-- The powers `h^k`, `k ≤ n`, are nonzero. -/
theorem hC_pow_ne_zero (n : ℕ) {k : ℕ} (hk : k ≤ n) : hC n ^ k ≠ 0 := by
  intro h0
  have h := coeffFun_hC_pow n ⟨k, Nat.lt_succ_of_le hk⟩ ⟨k, Nat.lt_succ_of_le hk⟩
  rw [h0] at h
  rw [show coeffFun n ⟨k, Nat.lt_succ_of_le hk⟩ (0 : CPRing n) = 0 from by
    rw [show (0 : CPRing n) = Ideal.Quotient.mk (relIdeal n) 0 by rw [map_zero],
      coeffFun_mk_apply, Polynomial.coeff_zero], if_pos rfl] at h
  exact one_ne_zero h.symm

instance instNontrivialCPRing (n : ℕ) : Nontrivial (CPRing n) :=
  ⟨⟨hC n ^ n, 0, hC_pow_ne_zero n le_rfl⟩⟩

/-! ## The fundamental class functional -/

/-- **The fundamental class functional** `⟨·, [ℂPⁿ]⟩ : H^*(ℂPⁿ;ℤ) → ℤ`: the coefficient of the top
class `hⁿ`.  It is `ℤ`-linear (`fundClass_add`, `fundClass_smul`) and
`⟨h^k, [ℂPⁿ]⟩ = 1` for `k = n`, `= 0` for `k < n`. -/
def fundClass (n : ℕ) : CPRing n → ℤ := coeffFun n ⟨n, Nat.lt_succ_self n⟩

theorem fundClass_eq (n : ℕ) : fundClass n = coeffFun n ⟨n, Nat.lt_succ_self n⟩ := rfl

theorem fundClass_mk_apply (n : ℕ) (p : Polynomial ℤ) :
    fundClass n (Ideal.Quotient.mk _ p) = p.coeff n :=
  coeffFun_mk_apply n ⟨n, Nat.lt_succ_self n⟩ p

theorem fundClass_add (n : ℕ) (x y : CPRing n) :
    fundClass n (x + y) = fundClass n x + fundClass n y :=
  coeffFun_add n ⟨n, Nat.lt_succ_self n⟩ x y

theorem fundClass_smul (n : ℕ) (a : ℤ) (x : CPRing n) :
    fundClass n (a • x) = a * fundClass n x :=
  coeffFun_smul n ⟨n, Nat.lt_succ_self n⟩ a x

/-- `fundClass` as a bundled `ℤ`-linear map. -/
def fundClassₗ (n : ℕ) : CPRing n →ₗ[ℤ] ℤ := coeffFunₗ n ⟨n, Nat.lt_succ_self n⟩

@[simp] theorem fundClassₗ_apply (n : ℕ) (x : CPRing n) : fundClassₗ n x = fundClass n x := rfl

/-- `coeffFun` vanishes on `0`. -/
theorem coeffFun_zero (n : ℕ) (k : Fin (n + 1)) : coeffFun n k (0 : CPRing n) = 0 := by
  rw [show (0 : CPRing n) = Ideal.Quotient.mk (relIdeal n) 0 by rw [map_zero], coeffFun_mk_apply,
    Polynomial.coeff_zero]

/-- `fundClass` vanishes on `0`. -/
theorem fundClass_zero (n : ℕ) : fundClass n (0 : CPRing n) = 0 := by
  rw [show (0 : CPRing n) = Ideal.Quotient.mk (relIdeal n) 0 by rw [map_zero], fundClass_mk_apply,
    Polynomial.coeff_zero]

/-- **`⟨h^k, [ℂPⁿ]⟩` is `1` in the top degree and `0` below it.** -/
theorem fundClass_hC_pow (n : ℕ) (k : ℕ) (hk : k ≤ n) :
    fundClass n (hC n ^ k) = if k = n then 1 else 0 := by
  rw [fundClass_eq, coeffFun_hC_pow n ⟨k, Nat.lt_succ_of_le hk⟩ ⟨n, Nat.lt_succ_self n⟩]
  by_cases h : (⟨k, Nat.lt_succ_of_le hk⟩ : Fin (n + 1)) = ⟨n, Nat.lt_succ_self n⟩
  · rw [if_pos h.symm, if_pos (congrArg Fin.val h)]
  · rw [if_neg (fun hh => h hh.symm), if_neg (fun hh => h (Fin.ext hh))]

/-- **`⟨h^n, [ℂPⁿ]⟩ = 1`**: the top class pairs to `1` with the fundamental class. -/
theorem fundClass_hC_pow_self (n : ℕ) : fundClass n (hC n ^ n) = 1 := by
  rw [fundClass_hC_pow n n le_rfl, if_pos rfl]

end

end Work.Projective
