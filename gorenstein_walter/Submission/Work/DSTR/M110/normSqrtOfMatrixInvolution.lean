import Mathlib
import Submission.Work.DSTR.M110.frobeniusRingAut
import Submission.Work.DSTR.M110.SplitCase.FixedField
import Submission.Work.DSTR.M110.lamFixedOfSemilinear
import Submission.Work.DSTR.M110.frobeniusInvolutionEq

namespace Work.DSTR.M110

open Polynomial

/-! ## The `k = 0` degenerate case

`GaloisField p 0` is the splitting field of `X ^ p ^ 0 - X = X - X`, hence isomorphic to
`ZMod p`, so it has no non-trivial ring automorphism. -/

/-- `GaloisField p 0` is `ZMod p` (as an algebra). -/
noncomputable def galoisFieldZeroAlgEquivZmod (p : ℕ) [Fact p.Prime] :
    GaloisField p 0 ≃ₐ[ZMod p] ZMod p := by
  have h := Polynomial.SplittingField.algEquivSplittingFieldAux (X ^ p ^ 0 - X : (ZMod p)[X])
  have hdeg : (X ^ p ^ 0 - X : (ZMod p)[X]).natDegree = 0 := by
    have h0 : (X ^ p ^ 0 - X : (ZMod p)[X]) = 0 := by rw [pow_zero, pow_one, sub_self]
    rw [h0]; simp
  rw [hdeg] at h
  exact h

/-- Any ring automorphism of `GaloisField p 0` is the identity. -/
theorem galoisField_zero_ringAut_trivial (p : ℕ) [Fact p.Prime]
    (σ : GaloisField p 0 ≃+* GaloisField p 0) : σ = 1 := by
  have e : GaloisField p 0 ≃+* ZMod p := (galoisFieldZeroAlgEquivZmod p).toRingEquiv
  have hρ : e.symm.trans (σ.trans e) = 1 := Subsingleton.elim _ _
  ext x
  have hx : e (σ x) = e x := by
    have h2 := congr_arg (fun (f : ZMod p ≃+* ZMod p) => f (e x)) hρ
    simpa [RingEquiv.trans_apply] using h2
  exact e.injective hx

/-! ## Norm surjectivity for a Frobenius involution

If `σ` acts on `F = GF(p ^ (2m))` as the `m`-fold Frobenius `x ↦ x ^ (p ^ m)`, then every
`σ`-fixed nonzero element `lam` is a norm `μ * σ μ`, because the multiplicative group `Fˣ` is
cyclic of order `(p ^ m) ^ 2 - 1 = (p ^ m - 1) * (p ^ m + 1)`; if `λ = g ^ n` then `σ`-fixedness
gives `(p ^ m + 1) ∣ n`, whence `λ` is a `(p ^ m + 1)`-st power. -/

theorem exists_mul_sigma_mul_of_frobeniusPow (p k m : ℕ) [Fact p.Prime] (hm : 1 ≤ m)
    (hk : k = 2 * m)
    (σ : GaloisField p k ≃+* GaloisField p k)
    (hσpow : ∀ x : GaloisField p k, σ x = x ^ (p ^ m))
    (lam : GaloisField p k) (hfix : σ lam = lam) (hne : lam ≠ 0) :
    ∃ μ : GaloisField p k, μ * σ μ = lam := by
  classical
  have hpm2 : 2 ≤ p ^ m := by
    have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
    calc 2 ≤ p := hp2
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ m := Nat.pow_le_pow_right (by omega) hm
  have hpm1 : 1 ≤ p ^ m := by omega
  have hk0 : k ≠ 0 := by omega
  have hcardF : Nat.card (GaloisField p k) = (p ^ m) ^ 2 := by
    rw [GaloisField.card p k hk0, hk, two_mul, pow_add, pow_two]
  have hcardU : Nat.card (GaloisField p k)ˣ = (p ^ m) ^ 2 - 1 := by
    rw [Nat.card_units, hcardF]
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (GaloisField p k)ˣ)
  have hgorder : orderOf g = (p ^ m) ^ 2 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, hcardU]
  -- `lam` as a unit
  let u : (GaloisField p k)ˣ := Units.mk0 lam hne
  have huval : (u : GaloisField p k) = lam := rfl
  have hlam_pow : lam ^ (p ^ m) = lam := (hσpow lam).symm.trans hfix
  have huq : u ^ (p ^ m) = u := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, huval]
    exact hlam_pow
  -- write `u = g ^ n`
  have hmem : u ∈ Submonoid.powers g := mem_powers_iff_mem_zpowers.mpr (hg u)
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff u g).mp hmem
  -- `g ^ (n * (p ^ m - 1)) = 1`
  have hcancel : g ^ (n * (p ^ m - 1)) = 1 := by
    have h1 : (g ^ n) ^ (p ^ m) = g ^ n := by rw [hn, huq]
    rw [← pow_mul] at h1
    have hArith : n * p ^ m = n + n * (p ^ m - 1) := by
      have hpp : p ^ m = (p ^ m - 1) + 1 := by omega
      nth_rewrite 1 [hpp]
      rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
    have hsplit : g ^ (n * p ^ m) = g ^ n * g ^ (n * (p ^ m - 1)) := by
      rw [hArith, pow_add]
    rw [hsplit] at h1
    exact mul_left_cancel (by rw [mul_one]; exact h1)
  have hdvd : orderOf g ∣ n * (p ^ m - 1) := orderOf_dvd_iff_pow_eq_one.mpr hcancel
  rw [hgorder] at hdvd
  have hfact : (p ^ m) ^ 2 - 1 = (p ^ m + 1) * (p ^ m - 1) := by
    have := Nat.sq_sub_sq (p ^ m) 1
    simpa using this
  rw [hfact] at hdvd
  have hpm1pos : 0 < p ^ m - 1 := by omega
  have hdvd2 : p ^ m + 1 ∣ n := Nat.dvd_of_mul_dvd_mul_right hpm1pos hdvd
  obtain ⟨w, hw⟩ := hdvd2
  have hwn : w * (1 + p ^ m) = n := by
    rw [Nat.add_comm 1 (p ^ m), Nat.mul_comm w (p ^ m + 1)]
    exact hw.symm
  have hunit : (g ^ w : (GaloisField p k)ˣ) * (g ^ w : (GaloisField p k)ˣ) ^ (p ^ m) = u := by
    have h : (g ^ w : (GaloisField p k)ˣ) ^ 1 * (g ^ w : (GaloisField p k)ˣ) ^ (p ^ m) = u := by
      rw [← pow_add, ← pow_mul, hwn, hn]
    simpa using h
  refine ⟨((g ^ w : (GaloisField p k)ˣ) : GaloisField p k), ?_⟩
  rw [hσpow, ← Units.val_pow_eq_pow_val, ← Units.val_mul, hunit]
  exact huval

theorem normSqrtOfMatrixInvolution (p k : ℕ) [Fact p.Prime]
    (σ : GaloisField p k ≃+* GaloisField p k)
    (hσ2 : ∀ x : GaloisField p k, σ (σ x) = x) (hσ1 : σ ≠ 1)
    (A : GL (Fin 2) (GaloisField p k)) (lam : GaloisField p k)
    (hA : (A : Matrix (Fin 2) (Fin 2) (GaloisField p k)) *
        Matrix.GeneralLinearGroup.map (σ : GaloisField p k →+* GaloisField p k) A =
          lam • 1) :
    ∃ μ : GaloisField p k, μ * σ μ = lam := by
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0
    exact absurd (galoisField_zero_ringAut_trivial p σ) hσ1
  · obtain ⟨hlam_fix, hlam_ne⟩ := lamFixedOfSemilinear (GaloisField p k) σ hσ2 A lam hA
    obtain ⟨m, hk2m, hσpow⟩ := frobeniusInvolutionEq p k (by omega) σ hσ2 hσ1
    have hm : 1 ≤ m := by omega
    exact exists_mul_sigma_mul_of_frobeniusPow p k m hm hk2m σ hσpow lam hlam_fix hlam_ne

end Work.DSTR.M110
