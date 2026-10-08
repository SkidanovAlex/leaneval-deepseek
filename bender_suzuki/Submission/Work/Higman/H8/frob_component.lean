/-
Copyright (c) 2024. All rights reserved.

# The Frobenius-component lemma in Singer coordinates

Field-level form of the module statement needed to close case (β) of `Work.Higman.H8.c4_sq_a2`:
in `Hom_{𝔽₂}(GF(2^n), GF(2^n))` with `ξ` acting as conjugation by multiplication by a generator
`ν` of `GF(2^n)ˣ`, an irreducible non-zero `𝔽₂⟨ξ⟩`-submodule consists of zero or bijections.

The proof route (see `H8/NOTES_c4_sq_a2_SESSION11.md` §9): write every additive `f` as
`Σ_{k<n} pol f k · x ^ (2^k)` (`Work.Higman.additive_frob`); the `k`-th coefficient transforms as
`pol (ξ f) k = ν^(1-2^k) · pol f k`, and the scalars `ν^(1-2^k)` are *pairwise distinct*
(`Work.Higman.H8.pow_two_modEq_one_eq`), so the two-point interpolating polynomial can kill any
single component inside `T`; iterating, `T` has an element with exactly one non-zero component,
whence `T ⊆ M_k = {x ↦ c x^(2^k)}` by irreducibility, and every non-zero element of `M_k` is a
bijection.
-/

import Mathlib
import Submission.Work.Higman.exists_singer_iso
import Submission.Work.Higman.core_alt_pairing_new
import Submission.Work.Higman.QuadAux
import Submission.Work.Higman.polyRep_add
import Submission.Work.Higman.H8.frob_orbit

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
open Polynomial

namespace Work.Higman.H8

variable {n : ℕ}

/-- `GaloisField 2 n` is a fintype (not a global instance in Mathlib). -/
noncomputable instance galoisFintype : Fintype (GaloisField 2 n) := Fintype.ofFinite _

/-- Decidable equality on `GaloisField 2 n`. -/
noncomputable instance galoisDecEq : DecidableEq (GaloisField 2 n) := Classical.decEq _

/-- `ZMod 2` has only `0` and `1`. -/
lemma zmod2_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a; decide

/-- Multiplication by `ν`, as an `𝔽₂`-linear endomorphism of `GF(2 ^ n)`. -/
noncomputable def mulLin (ν : GaloisField 2 n) : GaloisField 2 n →ₗ[ZMod 2] GaloisField 2 n where
  toFun x := ν * x
  map_add' x y := by rw [mul_add]
  map_smul' c x := by
    rcases zmod2_eq_zero_or_one c with rfl | rfl <;> simp

@[simp] lemma mulLin_apply (ν x : GaloisField 2 n) : mulLin ν x = ν * x := rfl

/-- The Singer action on `Hom_{𝔽₂}(F,F)`: `f ↦ (x ↦ ν * f (ν⁻¹ * x))`. -/
noncomputable def conjAction (ν : (GaloisField 2 n)ˣ)
    (f : GaloisField 2 n →ₗ[ZMod 2] GaloisField 2 n) :
    GaloisField 2 n →ₗ[ZMod 2] GaloisField 2 n :=
  (mulLin (ν : GaloisField 2 n)).comp (f.comp (mulLin (((ν⁻¹ : (GaloisField 2 n)ˣ) :
    GaloisField 2 n))))

@[simp] lemma conjAction_apply (ν : (GaloisField 2 n)ˣ)
    (f : GaloisField 2 n →ₗ[ZMod 2] GaloisField 2 n) (x : GaloisField 2 n) :
    conjAction ν f x = (ν : GaloisField 2 n) * f (((ν⁻¹ : (GaloisField 2 n)ˣ) :
      GaloisField 2 n) * x) := rfl

/-- The `k`-th Frobenius coefficient of an additive map `f : F → F`. -/
noncomputable def pol {n : ℕ} (f : GaloisField 2 n → GaloisField 2 n) (k : ℕ) :
    GaloisField 2 n := (polyRep f).coeff (2 ^ k)

lemma card_galois (hn : n ≠ 0) : Nat.card (GaloisField 2 n) = 2 ^ n :=
  GaloisField.card 2 n hn

/-- Every additive map on `GF(2^n)` is its Frobenius expansion. -/
lemma frob_expansion {n : ℕ} (hn : n ≠ 0) (f : GaloisField 2 n → GaloisField 2 n)
    (hf : ∀ x y, f (x + y) = f x + f y) (x : GaloisField 2 n) :
    f x = ∑ k ∈ Finset.range n, pol f k * x ^ (2 ^ k) := by
  have hcard : Fintype.card (GaloisField 2 n) = 2 ^ n := by
    rw [← Nat.card_eq_fintype_card, card_galois hn]
  exact additive_frob hcard f hf x

/-- **Uniqueness of the Frobenius expansion** (linear independence of the `x ^ (2 ^ k)`). -/
lemma frob_coeff_unique {n : ℕ} (hn : n ≠ 0) (a b : ℕ → GaloisField 2 n)
    (h : ∀ x : GaloisField 2 n,
      (∑ k ∈ Finset.range n, a k * x ^ (2 ^ k))
        = ∑ k ∈ Finset.range n, b k * x ^ (2 ^ k)) :
    ∀ k ∈ Finset.range n, a k = b k := by
  have key : ∀ k ∈ Finset.range n, (fun j => a j - b j) k = 0 := by
    refine monomial_indep_finset (Finset.range n) (fun k => 2 ^ k) ?_ ?_
      (fun k => a k - b k) ?_
    · intro k hk l hl hkl
      exact Nat.pow_right_injective (by norm_num) hkl
    · intro m hm
      rw [Finset.mem_range] at hm
      rw [show Fintype.card (GaloisField 2 n) = 2 ^ n by
        rw [← Nat.card_eq_fintype_card, card_galois hn]]
      exact Nat.pow_lt_pow_right (by norm_num) hm
    · intro x
      have hx := h x
      have h1 : (∑ k ∈ Finset.range n, (a k - b k) * x ^ (2 ^ k))
          = ∑ k ∈ Finset.range n, (a k * x ^ (2 ^ k) - b k * x ^ (2 ^ k)) :=
        Finset.sum_congr rfl (fun k _ => by rw [sub_mul])
      have h2 : (∑ k ∈ Finset.range n, (a k * x ^ (2 ^ k) - b k * x ^ (2 ^ k)))
          = (∑ k ∈ Finset.range n, a k * x ^ (2 ^ k))
            - ∑ k ∈ Finset.range n, b k * x ^ (2 ^ k) := by rw [Finset.sum_sub_distrib]
      rw [h1, h2, hx, sub_self]
  intro k hk
  have := key k hk
  exact sub_eq_zero.mp this

/-- The `k`-th Frobenius coefficient of the Singer-twisted map: `pol (ξ f) k = λ_k · pol f k`. -/
lemma pol_conjAction {n : ℕ} (hn : n ≠ 0) (ν : (GaloisField 2 n)ˣ)
    (f : GaloisField 2 n →ₗ[ZMod 2] GaloisField 2 n) {k : ℕ} (hk : k < n) :
    pol (conjAction ν f) k
      = (ν : GaloisField 2 n) * (((ν : GaloisField 2 n) ^ (2 ^ k))⁻¹) * pol f k := by
  -- pointwise expansion of `conjAction ν f` with explicit coefficients
  have hfun : ∀ x : GaloisField 2 n,
      conjAction ν f x = ∑ j ∈ Finset.range n,
        ((ν : GaloisField 2 n) * pol f j * (((ν : GaloisField 2 n) ^ (2 ^ j))⁻¹))
          * x ^ (2 ^ j) := by
    intro x
    have h1 := frob_expansion hn f f.map_add
      (((ν⁻¹ : (GaloisField 2 n)ˣ) : GaloisField 2 n) * x)
    rw [conjAction_apply, h1, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Units.val_inv_eq_inv_val, mul_pow, inv_pow]
    ring
  -- uniqueness of the Frobenius expansion identifies the coefficients
  have h3 : ∀ x : GaloisField 2 n,
      conjAction ν f x = ∑ j ∈ Finset.range n, pol (conjAction ν f) j * x ^ (2 ^ j) :=
    fun x => frob_expansion hn (conjAction ν f) (conjAction ν f).map_add x
  have huniq := frob_coeff_unique hn (fun j => pol (conjAction ν f) j)
    (fun j => (ν : GaloisField 2 n) * pol f j * (((ν : GaloisField 2 n) ^ (2 ^ j))⁻¹))
    (fun x => by rw [← h3 x, hfun x])
  have hk' := huniq k (Finset.mem_range.mpr hk)
  rw [hk']; ring

/-- The Singer eigenvalue attached to `k`: `λ_k = ν ^ (1 - 2 ^ k) = ν * (ν ^ (2 ^ k))⁻¹`. -/
noncomputable def lam (ν : (GaloisField 2 n)ˣ) (k : ℕ) : GaloisField 2 n :=
  (ν : GaloisField 2 n) * (((ν : GaloisField 2 n) ^ (2 ^ k))⁻¹)

/-- **Singleton Frobenius classes.**  For `ν` of order `2 ^ n - 1`, two Singer eigenvalues
`λ_{k₁}`, `λ_{k₂}` (`k₁, k₂ < n`) that are Frobenius conjugate (`λ_{k₁} = λ_{k₂} ^ (2 ^ s)`)
coincide; this is `Work.Higman.H8.frob_orbit_eq` in field coordinates. -/
theorem lam_frob_inj {n : ℕ} (hn : 2 ≤ n) (ν : (GaloisField 2 n)ˣ) (hν : orderOf ν = 2 ^ n - 1)
    {k₁ k₂ s : ℕ} (hk₁ : k₁ < n) (hk₂ : k₂ < n)
    (h : lam ν k₁ = (lam ν k₂) ^ (2 ^ s)) : k₁ = k₂ := by
  have hn1 : 1 ≤ n := by omega
  -- (1) transfer to the unit group
  have hU : (ν * (ν ^ (2 ^ k₁))⁻¹ : (GaloisField 2 n)ˣ)
      = (ν * (ν ^ (2 ^ k₂))⁻¹) ^ (2 ^ s) := by
    apply Units.ext
    simpa [lam, Units.val_pow_eq_pow_val] using h
  -- (2) clear the inverses: multiply by `ν^(2^k₁) * ν^(2^(s+k₂))`
  have hkey : (ν : (GaloisField 2 n)ˣ) ^ (1 + 2 ^ (s + k₂)) = ν ^ (2 ^ s + 2 ^ k₁) := by
    have h1 := congrArg (fun u : (GaloisField 2 n)ˣ =>
      u * (ν ^ (2 ^ k₁) * ν ^ (2 ^ (s + k₂)))) hU
    have e1 : (ν * (ν ^ (2 ^ k₁))⁻¹) * (ν ^ (2 ^ k₁) * ν ^ (2 ^ (s + k₂)))
        = ν ^ (1 + 2 ^ (s + k₂)) := by
      rw [mul_assoc, ← mul_assoc ((ν ^ (2 ^ k₁))⁻¹), inv_mul_cancel, one_mul, ← pow_succ',
        Nat.add_comm]
    have e2 : ((ν * (ν ^ (2 ^ k₂))⁻¹) ^ (2 ^ s)) * (ν ^ (2 ^ k₁) * ν ^ (2 ^ (s + k₂)))
        = ν ^ (2 ^ s + 2 ^ k₁) := by
      rw [mul_pow, inv_pow, ← pow_mul,
        show 2 ^ k₂ * 2 ^ s = 2 ^ (s + k₂) from by rw [mul_comm, ← pow_add]]
      rw [mul_assoc, mul_comm (ν ^ (2 ^ k₁)) (ν ^ (2 ^ (s + k₂))),
        ← mul_assoc ((ν ^ (2 ^ (s + k₂)))⁻¹), inv_mul_cancel, one_mul, ← pow_add]
    rw [e1, e2] at h1
    exact h1
  -- (3) read off the congruence modulo `2 ^ n - 1`
  have hfin : IsOfFinOrder ν := by
    refine (isOfFinOrder_iff_pow_eq_one).mpr ⟨2 ^ n - 1, ?_, ?_⟩
    · have : 1 < 2 ^ n := Nat.one_lt_pow (by omega) (by omega)
      omega
    · rw [← hν]; exact pow_orderOf_eq_one ν
  have hmod : 1 + 2 ^ (s + k₂) ≡ 2 ^ s + 2 ^ k₁ [MOD 2 ^ n - 1] := by
    have h1 : 1 + 2 ^ (s + k₂) ≡ 2 ^ s + 2 ^ k₁ [MOD orderOf ν] :=
      (hfin.pow_eq_pow_iff_modEq).mp hkey
    rwa [hν] at h1
  -- (4) reduce the exponents modulo `n`
  have hred : 1 + 2 ^ ((s + k₂) % n) ≡ 2 ^ (s % n) + 2 ^ k₁ [MOD 2 ^ n - 1] := by
    have hA := pow_two_modEq_mod' (n := n) (m := s + k₂) hn1
    have hB := pow_two_modEq_mod' (n := n) (m := s) hn1
    have h1 : 1 + 2 ^ ((s + k₂) % n) ≡ 2 ^ s + 2 ^ k₁ [MOD 2 ^ n - 1] :=
      ((Nat.ModEq.refl 1).add hA.symm).trans hmod
    exact h1.trans (hB.add (Nat.ModEq.refl (2 ^ k₁)))
  -- (5) put it in the shape of `frob_orbit_eq`
  have hshape : 2 ^ (s % n) + 2 ^ k₁ ≡ 1 + 2 ^ ((s % n + k₂) % n) [MOD 2 ^ n - 1] := by
    have hexp : (s + k₂) % n = (s % n + k₂) % n := by
      rw [Nat.add_mod, Nat.mod_eq_of_lt hk₂]
    rw [← hexp]
    exact hred.symm
  exact (frob_orbit_eq hn (k₁ := k₂) (k₂ := k₁) (u := s % n) hk₂ hk₁
    (Nat.mod_lt _ (by omega)) hshape).symm

/-- **The roots of the `𝔽₂`-minimal polynomial of `λ_{k₂}`, among the eigenvalues `λ_k`, are
exactly `λ_{k₂}`.**  This is the combination of the general root/conjugate fact for `minpoly`
(`IsConjRoot.isConjRoot_iff_aeval_eq_zero`) with the singleton-class input `lam_frob_inj`; it is
what makes `Q(ξ)` (`Q = minPoly λ_{k₂}`) kill precisely the `k₂`-component of an element of
`T` while preserving every other component. -/
theorem minpoly_lam_aeval_eq_zero_iff {n : ℕ} (hn : 2 ≤ n) (ν : (GaloisField 2 n)ˣ)
    (hν : orderOf ν = 2 ^ n - 1) {k k₂ : ℕ} (hk : k < n) (hk₂ : k₂ < n) :
    (Polynomial.aeval (lam ν k)) (minpoly (ZMod 2) (lam ν k₂)) = 0 ↔ k = k₂ := by
  sorry

/-- **Field form of the Frobenius-component lemma.**  Let `ν` generate `GF(2^n)ˣ` (`n ≥ 2`) and
let `T ≤ Hom_{𝔽₂}(GF(2^n), GF(2^n))` be a non-zero `𝔽₂⟨ξ⟩`-submodule, `ξ = conjAction ν`, which is
irreducible.  Then every non-zero element of `T` is a bijection. -/
theorem frob_component_bijective {n : ℕ} (hn : 2 ≤ n)
    (ν : (GaloisField 2 n)ˣ) (hν : orderOf ν = 2 ^ n - 1)
    (T : Submodule (ZMod 2) (GaloisField 2 n →ₗ[ZMod 2] GaloisField 2 n))
    (hTξ : ∀ f ∈ T, conjAction ν f ∈ T)
    (hirr : ∀ T' : Submodule (ZMod 2) (GaloisField 2 n →ₗ[ZMod 2] GaloisField 2 n),
      (∀ f ∈ T', conjAction ν f ∈ T') → T' ≤ T → T' = ⊥ ∨ T' = T) :
    ∀ f ∈ T, f ≠ 0 → Function.Bijective f := by
  sorry

end Work.Higman.H8
