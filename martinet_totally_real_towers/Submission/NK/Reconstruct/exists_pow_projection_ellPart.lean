import Mathlib
import Submission.NK.Reconstruct.ellPart

/-!
# Projecting a finite abelian group onto its ℓ-primary part

For a finite commutative group `A` and any `ℓ : ℕ` there is a single exponent `c` such that for
**every** `x : A` the power `x ^ c` lies in the ℓ-primary part `ellPart A ℓ`, while the "error term"
`x * (x ^ c)⁻¹` is killed by a power coprime to `ℓ`.

The construction: writing `d = orderOf x` and `u = gcd d (ℓ ^ d)`, the number
`v x = d / u` is the "ℓ-prime-free part" of `d`, and `d = u * v x`.  A uniform exponent `c` is
obtained by Euler's theorem applied to `M = ∏ x, v x` (which is coprime to `ℓ`): take
`c = M ^ φ(ℓ ^ Nat.card A)`.  Then `M ∣ c` and `c ≡ 1 [MOD ℓ ^ Nat.card A]`, which is exactly what
is needed.
-/

set_option linter.style.haveILetI false

namespace NK.Reconstruct

/-- **Arithmetic core.**  For `1 ≤ ℓ` and `1 ≤ d`, the "ℓ-prime-free part" `d / gcd d (ℓ ^ d)` of
`d` is coprime to `ℓ`.  Indeed if a prime `p` divides `ℓ` then the full `p`-adic valuation of `d`
is already contained in `gcd d (ℓ ^ d)` (because `p ^ d ∣ ℓ ^ d`), so nothing is left in the
quotient. -/
theorem coprime_div_gcd_pow_self (ℓ d : ℕ) (hℓ : 1 ≤ ℓ) (hd : 1 ≤ d) :
    Nat.Coprime (d / Nat.gcd d (ℓ ^ d)) ℓ := by
  rcases eq_or_lt_of_le hℓ with h1 | h2
  · rw [← h1]; simp
  rw [Nat.coprime_comm]
  by_contra h
  obtain ⟨p, hp, hpℓ, hpv⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
  have hℓ0 : ℓ ≠ 0 := by omega
  have hd0 : d ≠ 0 := by omega
  have hpow0 : ℓ ^ d ≠ 0 := pow_ne_zero d hℓ0
  have hgpos : 0 < Nat.gcd d (ℓ ^ d) := Nat.gcd_pos_of_pos_left _ (by omega)
  have hv0 : d / Nat.gcd d (ℓ ^ d) ≠ 0 := by
    have : 0 < d / Nat.gcd d (ℓ ^ d) :=
      Nat.div_pos (Nat.gcd_le_left _ (by omega)) hgpos
    omega
  have h1 : 1 ≤ (d / Nat.gcd d (ℓ ^ d)).factorization p :=
    (hp.dvd_iff_one_le_factorization hv0).mp hpv
  have hf1 : (d / Nat.gcd d (ℓ ^ d)).factorization p
      = d.factorization p - (Nat.gcd d (ℓ ^ d)).factorization p := by
    rw [Nat.factorization_div (Nat.gcd_dvd_left d (ℓ ^ d))]
    simp
  have hgcd : (Nat.gcd d (ℓ ^ d)).factorization p = d.factorization p := by
    have hcong := congrArg (fun f : ℕ →₀ ℕ => f p) (Nat.factorization_gcd hd0 hpow0)
    rw [Finsupp.inf_apply] at hcong
    rw [hcong]
    apply Nat.min_eq_left
    have hℓfac : 1 ≤ ℓ.factorization p :=
      (hp.dvd_iff_one_le_factorization hℓ0).mp hpℓ
    have hpowfac : (ℓ ^ d).factorization p = d * ℓ.factorization p := by
      rw [Nat.factorization_pow]
      simp
    rw [hpowfac]
    have hlt : d.factorization p < d * ℓ.factorization p :=
      calc d.factorization p < d := Nat.factorization_lt p hd0
        _ = d * 1 := (mul_one d).symm
        _ ≤ d * ℓ.factorization p := Nat.mul_le_mul_left d hℓfac
    exact le_of_lt hlt
  rw [hf1, hgcd, tsub_self] at h1
  omega

theorem exists_pow_projection_ellPart {A : Type*} [CommGroup A] [Finite A] (ℓ : ℕ) :
    ∃ c : ℕ, ∀ x : A, x ^ c ∈ ellPart A ℓ ∧
      ∃ m : ℕ, Nat.Coprime m ℓ ∧ (x * (x ^ c)⁻¹) ^ m = 1 := by
  classical
  rcases eq_or_ne ℓ 0 with hℓ0 | hℓ0
  · subst hℓ0
    refine ⟨1, fun x => ⟨?_, 1, ?_, ?_⟩⟩
    · rw [mem_ellPart_iff]
      exact ⟨1, by simp⟩
    · exact Nat.coprime_one_left 0
    · simp
  · have hℓ1 : 1 ≤ ℓ := Nat.one_le_iff_ne_zero.mpr hℓ0
    letI := Fintype.ofFinite A
    let v : A → ℕ := fun x => orderOf x / (orderOf x).gcd (ℓ ^ orderOf x)
    have hv_cop : ∀ x, Nat.Coprime (v x) ℓ := fun x =>
      coprime_div_gcd_pow_self ℓ (orderOf x) hℓ1
        (Nat.pos_of_dvd_of_pos (orderOf_dvd_natCard x) Nat.card_pos)
    have hv_pos : ∀ x : A, 0 < v x := fun x => by
      dsimp only [v]
      have hd : 0 < orderOf x :=
        Nat.pos_of_dvd_of_pos (orderOf_dvd_natCard x) Nat.card_pos
      exact Nat.div_pos (Nat.gcd_le_left _ hd) (Nat.gcd_pos_of_pos_left _ hd)
    let M : ℕ := ∏ x, v x
    have hM_pos : 0 < M := by
      have h := Finset.prod_pos (s := Finset.univ) (f := v) (fun x _ => hv_pos x)
      simpa [M] using h
    have hM_cop : Nat.Coprime M ℓ := by
      have h := Nat.Coprime.prod_left (fun x (_ : x ∈ Finset.univ) => hv_cop x)
      simpa [M] using h
    let c : ℕ := M ^ Nat.totient (ℓ ^ Nat.card A)
    have hc_pos : 0 < c := pow_pos hM_pos _
    have hc1 : 1 ≤ c := Nat.one_le_iff_ne_zero.mpr (ne_of_gt hc_pos)
    have hM_dvd_c : M ∣ c := dvd_pow_self M
      (ne_of_gt (Nat.totient_pos.mpr (pow_pos (by omega : 0 < ℓ) _)))
    have hc_mod : c ≡ 1 [MOD ℓ ^ Nat.card A] :=
      Nat.ModEq.pow_totient (hM_cop.pow_right _)
    have hc_sub : ℓ ^ Nat.card A ∣ c - 1 :=
      (Nat.modEq_iff_dvd' (n := ℓ ^ Nat.card A) (a := 1) (b := c) hc1).mp hc_mod.symm
    refine ⟨c, ?_⟩
    intro x
    have hd_le : orderOf x ≤ Nat.card A :=
      Nat.le_of_dvd Nat.card_pos (orderOf_dvd_natCard x)
    have huv : (orderOf x).gcd (ℓ ^ orderOf x) * v x = orderOf x := by
      dsimp only [v]
      rw [mul_comm]
      exact Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)
    have hu_ℓ : (orderOf x).gcd (ℓ ^ orderOf x) ∣ ℓ ^ Nat.card A :=
      dvd_trans (Nat.gcd_dvd_right _ _) (pow_dvd_pow ℓ hd_le)
    have hv_c : v x ∣ c :=
      dvd_trans (Finset.dvd_prod_of_mem v (Finset.mem_univ x)) hM_dvd_c
    refine ⟨?_, v x, hv_cop x, ?_⟩
    · -- `x ^ c` is ℓ-primary
      rw [mem_ellPart_iff]
      refine ⟨Nat.card A, ?_⟩
      rw [← pow_mul]
      apply orderOf_dvd_iff_pow_eq_one.mp
      rw [← huv]
      simpa [mul_comm] using Nat.mul_dvd_mul hu_ℓ hv_c
    · -- the error term is killed by the ℓ-prime-free part
      have hc_eq : c = (c - 1) + 1 := (Nat.succ_pred_eq_of_pos hc_pos).symm
      have hxc : x ^ c = x * x ^ (c - 1) := by
        conv_lhs => rw [hc_eq]
        rw [pow_succ, mul_comm]
      have hy : x * (x ^ c)⁻¹ = (x ^ (c - 1))⁻¹ := by
        rw [hxc]
        group
      have hu_c : (orderOf x).gcd (ℓ ^ orderOf x) ∣ c - 1 :=
        dvd_trans hu_ℓ hc_sub
      have hdvd : orderOf x ∣ (c - 1) * v x := by
        rw [← huv, mul_comm ((orderOf x).gcd (ℓ ^ orderOf x)) (v x),
          mul_comm (c - 1) (v x)]
        exact Nat.mul_dvd_mul_left (v x) hu_c
      rw [hy, inv_pow, ← pow_mul, inv_eq_one]
      exact orderOf_dvd_iff_pow_eq_one.mp hdvd

end NK.Reconstruct
