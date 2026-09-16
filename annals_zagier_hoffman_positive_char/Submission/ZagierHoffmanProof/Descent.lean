import Submission.ZagierHoffmanProof.ATSeries
import Submission.Commons.Data.Nat.mod_pow_eq_zero_iff
import Submission.Commons.Data.Nat.mod_pow_eq_pred_iff
import Submission.Commons.Combinatorics.Multinomial.digit_reduction
import Submission.Commons.Data.Nat.div_pow_shift_zero
import Submission.Commons.Data.Nat.div_pow_shift_pred

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Polynomial
open scoped BigOperators

/-!
# The Frobenius descent for the Anderson–Thakur coefficients

Chen (arXiv:1506.06463, §3, Step 1) computes `H_{q^M - 1}` by *descending* the no-carry
`q`-power weighted partitions of `q^M - 1` to those of `q^{M-1} - 1`: the reduction map
`ā ↦ ā̃ ↦ ã̃` (`a_i = q·b_i + (q-1)δ_{i0}`) is a bijection on the no-carry vectors, and
`C_ā = C_{ā̃}·C_{ã̃}` with `C_{ā̃} = 1`.

This file starts the formalisation of that descent in the workspace normalisation
(`atCoeff`, `NoCarryVec`, `atCoeff_eq_sum_multi`).  The first ingredient is the *no-carry
congruence lemma*: if `a` partitions `q ^ M - 1` (`M ≥ 1`) without carries in base
`p = ringChar F`, then `a 0 ≡ q - 1 (mod q)` and every other entry of `a` is divisible by `q`.
This is where the base-`p` digit structure of `q = p ^ l` is used
(`Commons.Data.Nat.mod_pow_eq_pred_iff`, `...mod_pow_eq_zero_iff`).
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F]

/-- `(q ^ M - 1) % q = q - 1` for `q ≥ 1` and `M ≥ 1`. -/
lemma pow_sub_one_mod (q M : ℕ) (hM : 1 ≤ M) (hq : 1 ≤ q) : (q ^ M - 1) % q = q - 1 := by
  obtain ⟨M', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : M ≠ 0)
  have hmul : q * (q ^ M' - 1) = q ^ (M' + 1) - q := by
    rw [Nat.mul_sub_left_distrib, mul_one, pow_succ, mul_comm]
  have h1 : q ^ (M' + 1) - 1 = q * (q ^ M' - 1) + (q - 1) := by
    have hqle : q ≤ q ^ (M' + 1) := by
      calc q = q ^ 1 := (pow_one q).symm
        _ ≤ q ^ (M' + 1) := Nat.pow_le_pow_right hq (by omega)
    omega
  rw [h1, Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

/-- **The no-carry congruence lemma.**  If a family of multiplicities partitions `q ^ M - 1`
(`M ≥ 1`) without carries in base `p = ringChar F`, then `a 0 ≡ q - 1 (mod q)` and every entry of
index `≠ 0` is divisible by `q`. -/
lemma noCarry_mod_and_dvd {B M : ℕ} (hB : 0 < B) (hM : 1 ≤ M) (a : Fin B → ℕ)
    (hsum : (∑ i, a i * Nat.card F ^ ((i : ℕ))) = Nat.card F ^ M - 1)
    (hnc : NoCarryVec F a) :
    a ⟨0, hB⟩ % Nat.card F = Nat.card F - 1 ∧ ∀ i, i ≠ ⟨0, hB⟩ → Nat.card F ∣ a i := by
  obtain ⟨l, hp, hpq⟩ := card_eq_ringChar_pow F
  have hp1 : 1 ≤ ringChar F := hp.one_le
  have hq2 : 2 ≤ Nat.card F := carlitz_card_ge_two F
  have hmod : a ⟨0, hB⟩ % Nat.card F = Nat.card F - 1 := by
    have hsplit : (∑ k, a k * Nat.card F ^ ((k : ℕ)))
        = (∑ k ∈ (Finset.univ : Finset (Fin B)).erase ⟨0, hB⟩, a k * Nat.card F ^ ((k : ℕ)))
          + a ⟨0, hB⟩ * Nat.card F ^ ((⟨0, hB⟩ : Fin B) : ℕ) :=
      (Finset.sum_erase_add _ _ (Finset.mem_univ _)).symm
    have hdvd : Nat.card F ∣ ∑ k ∈ (Finset.univ : Finset (Fin B)).erase ⟨0, hB⟩,
        a k * Nat.card F ^ ((k : ℕ)) := by
      refine Finset.dvd_sum (fun k hk => ?_)
      rw [Finset.mem_erase] at hk
      obtain ⟨hk0, -⟩ := hk
      have hk1 : 1 ≤ (k : ℕ) := by
        rcases Nat.eq_zero_or_pos (k : ℕ) with h | h
        · exfalso
          exact hk0 (Fin.ext (by simpa using h))
        · exact h
      simpa [pow_one] using Dvd.dvd.mul_left (pow_dvd_pow (Nat.card F) hk1) (a k)
    obtain ⟨c, hc⟩ := hdvd
    have : (∑ k, a k * Nat.card F ^ ((k : ℕ))) % Nat.card F = a ⟨0, hB⟩ % Nat.card F := by
      rw [hsplit, hc, pow_zero, mul_one, Nat.add_comm, Nat.add_mul_mod_self_left]
    rw [hsum, pow_sub_one_mod (Nat.card F) M hM (by omega)] at this
    exact this.symm
  have hd : ∀ j, j < l → a ⟨0, hB⟩ / (ringChar F) ^ j % (ringChar F) = (ringChar F) - 1 := by
    refine (Commons.Data.Nat.mod_pow_eq_pred_iff (ringChar F) l (a ⟨0, hB⟩) hp1).mp ?_
    rw [← hpq]
    exact hmod
  have hkey : ∀ {i : Fin B}, i ≠ ⟨0, hB⟩ → Nat.card F ∣ a i := by
    intro i hi
    rw [hpq, Nat.dvd_iff_mod_eq_zero]
    refine (Commons.Data.Nat.mod_pow_eq_zero_iff (ringChar F) l (a i) hp1).mpr ?_
    intro j hj
    have hlt := hnc j
    have h0j : a ⟨0, hB⟩ / (ringChar F) ^ j % (ringChar F) = (ringChar F) - 1 := hd j hj
    have hpair : (∑ k ∈ ({⟨0, hB⟩, i} : Finset (Fin B)),
          a k / (ringChar F) ^ j % (ringChar F))
        = a ⟨0, hB⟩ / (ringChar F) ^ j % (ringChar F) + a i / (ringChar F) ^ j % (ringChar F) :=
      Finset.sum_pair (Ne.symm hi)
    have hle : (∑ k ∈ ({⟨0, hB⟩, i} : Finset (Fin B)), a k / (ringChar F) ^ j % (ringChar F))
        ≤ ∑ k, a k / (ringChar F) ^ j % (ringChar F) :=
      Finset.sum_le_sum_of_subset_of_nonneg (by intro x _; exact Finset.mem_univ x)
        (by intro x _ _; exact Nat.zero_le _)
    rw [hpair, h0j] at hle
    omega
  exact ⟨hmod, fun i hi => hkey hi⟩

/-- The `ℕ`-divisibility half of `noCarry_mod_and_dvd`. -/
lemma noCarry_dvd_of_sum {B M : ℕ} (hB : 0 < B) (hM : 1 ≤ M) (a : Fin B → ℕ)
    (hsum : (∑ i, a i * Nat.card F ^ ((i : ℕ))) = Nat.card F ^ M - 1)
    (hnc : NoCarryVec F a) {i : Fin B} (hi : i ≠ ⟨0, hB⟩) :
    Nat.card F ∣ a i :=
  (noCarry_mod_and_dvd F hB hM a hsum hnc).2 i hi

/-- The congruence half of `noCarry_mod_and_dvd`: `a 0 ≡ q - 1 (mod q)`. -/
lemma noCarry_zero_mod {B M : ℕ} (hB : 0 < B) (hM : 1 ≤ M) (a : Fin B → ℕ)
    (hsum : (∑ i, a i * Nat.card F ^ ((i : ℕ))) = Nat.card F ^ M - 1)
    (hnc : NoCarryVec F a) :
    a ⟨0, hB⟩ % Nat.card F = Nat.card F - 1 :=
  (noCarry_mod_and_dvd F hB hM a hsum hnc).1

/-- `(m : atQ F) ^ q = (m : atQ F)`: natural numbers are fixed by the `q`-th power map. -/
lemma natCast_pow_card_eq (m : ℕ) : ((m : atQ F)) ^ (Nat.card F) = (m : atQ F) := by
  haveI : Fintype F := Fintype.ofFinite F
  have hcard : Fintype.card F = Nat.card F := Fintype.card_eq_nat_card
  rw [show ((m : atQ F)) = algebraMap F (atQ F) ((m : F)) from (map_natCast _ m).symm]
  rw [← map_pow, ← hcard, FiniteField.pow_card]

/-- The **ascent** of a multiplicity vector: `b ↦ (k ↦ q * b k + (q - 1) * [k = 0])`. -/
noncomputable def ascentMap {B : ℕ} (b : Fin B → ℕ) : Fin B → ℕ :=
  fun k => Nat.card F * b k + (if (k : ℕ) = 0 then Nat.card F - 1 else 0)

/-- The **descent** of a multiplicity vector: `a ↦ (k ↦ a k / q)`. -/
noncomputable def descentMap {B : ℕ} (a : Fin B → ℕ) : Fin B → ℕ :=
  fun k => a k / Nat.card F

lemma ascentMap_apply {B : ℕ} (b : Fin B → ℕ) (k : Fin B) :
    ascentMap F b k = Nat.card F * b k + (if (k : ℕ) = 0 then Nat.card F - 1 else 0) := rfl

lemma descentMap_apply {B : ℕ} (a : Fin B → ℕ) (k : Fin B) :
    descentMap F a k = a k / Nat.card F := rfl

lemma ascentMap_mul_sum {B : ℕ} (b : Fin B → ℕ) :
    (∑ k : Fin B, Nat.card F * b k * Nat.card F ^ ((k : ℕ)))
      = Nat.card F * (∑ k : Fin B, b k * Nat.card F ^ ((k : ℕ))) := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun k _ => by ring)

lemma ascentMap_pair_sum {B : ℕ} (hB : 0 < B) :
    (∑ k : Fin B, (if (k : ℕ) = 0 then Nat.card F - 1 else 0) * Nat.card F ^ ((k : ℕ)))
      = Nat.card F - 1 := by
  rw [Finset.sum_eq_single (⟨0, hB⟩ : Fin B)]
  · simp
  · intro k _ hk
    rw [if_neg (fun h => hk (Fin.ext h)), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

lemma ascentMap_sum {B M : ℕ} (hB : 0 < B) (b : Fin B → ℕ)
    (hsum : (∑ k : Fin B, b k * Nat.card F ^ ((k : ℕ))) = Nat.card F ^ M - 1) :
    (∑ k : Fin B, ascentMap F b k * Nat.card F ^ ((k : ℕ))) = Nat.card F ^ (M + 1) - 1 := by
  have h1 : (∑ k : Fin B, ascentMap F b k * Nat.card F ^ ((k : ℕ)))
      = (∑ k : Fin B, Nat.card F * b k * Nat.card F ^ ((k : ℕ)))
        + (∑ k : Fin B, (if (k : ℕ) = 0 then Nat.card F - 1 else 0) * Nat.card F ^ ((k : ℕ))) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [ascentMap_apply, add_mul]
  rw [h1, ascentMap_mul_sum F, ascentMap_pair_sum F hB, hsum]
  have hq1 : 1 ≤ Nat.card F := by have := carlitz_card_ge_two F; omega
  have hpow : Nat.card F ^ (M + 1) = Nat.card F * Nat.card F ^ M := by
    rw [pow_succ, mul_comm]
  have hmul : Nat.card F * (Nat.card F ^ M - 1)
      = Nat.card F * Nat.card F ^ M - Nat.card F := by
    rw [Nat.mul_sub_left_distrib, mul_one]
  have hle : Nat.card F ≤ Nat.card F * Nat.card F ^ M := by
    calc Nat.card F = Nat.card F * 1 := (mul_one _).symm
      _ ≤ Nat.card F * Nat.card F ^ M := Nat.mul_le_mul_left _ (Nat.one_le_pow M (Nat.card F) (by omega))
  omega

/-- The ascent preserves the no-carry condition. -/
lemma ascentMap_noCarry {B : ℕ} (hB : 0 < B) (b : Fin B → ℕ) (hnc : NoCarryVec F b) :
    NoCarryVec F (ascentMap F b) := by
  obtain ⟨l, hp, hpq⟩ := card_eq_ringChar_pow F
  have hp2 : 2 ≤ ringChar F := hp.two_le
  intro j
  have hstep : ∀ k : Fin B,
      ascentMap F b k / (ringChar F) ^ j % (ringChar F)
        = (if j < l then (if (k : ℕ) = 0 then (ringChar F) - 1 else 0)
            else b k / (ringChar F) ^ (j - l) % (ringChar F)) := by
    intro k
    rw [ascentMap_apply, hpq]
    by_cases hk : (k : ℕ) = 0
    · have h1 : (if (k : ℕ) = 0 then ((ringChar F) ^ l - 1) else 0) = ((ringChar F) ^ l - 1) :=
        if_pos hk
      have h2 : (if (k : ℕ) = 0 then ((ringChar F) - 1) else 0) = ((ringChar F) - 1) :=
        if_pos hk
      rw [h1]
      refine Eq.trans (Commons.Data.Nat.div_pow_shift_pred (ringChar F) l (b k) j hp2) ?_
      rw [h2]
    · have h1 : (if (k : ℕ) = 0 then ((ringChar F) ^ l - 1) else 0) = 0 := if_neg hk
      have h2 : (if (k : ℕ) = 0 then ((ringChar F) - 1) else 0) = 0 := if_neg hk
      rw [h1, add_zero, h2]
      exact Commons.Data.Nat.div_pow_shift_zero (ringChar F) l (b k) j hp2
  rw [Finset.sum_congr rfl (fun k _ => hstep k)]
  by_cases hj : j < l
  · rw [Finset.sum_congr rfl (fun k _ => if_pos hj)]
    have hone : (∑ k : Fin B, (if (k : ℕ) = 0 then (ringChar F) - 1 else 0))
        = (ringChar F) - 1 := by
      rw [Finset.sum_eq_single (⟨0, hB⟩ : Fin B)]
      · simp
      · intro k _ hk
        exact if_neg (fun h => hk (Fin.ext h))
      · intro h
        exact absurd (Finset.mem_univ _) h
    rw [hone]
    omega
  · rw [Finset.sum_congr rfl (fun k _ => if_neg hj)]
    exact hnc (j - l)


lemma atGamma_mul_atD_zero : (atGamma F 0 * (atD F 0)⁻¹ : atQ F) = 1 := by
  simp only [atGamma_zero, atD, carlitzFact_zero, map_one, Polynomial.C_1, map_one,
    inv_one, mul_one]

/-- The ascent is compatible with the denominators `Γ_k = γ_k / D_k`: since `γ_0/D_0 = 1`, the
product picks up exactly a `q`-th power. -/
lemma ascentMap_prod {B : ℕ} (hB : 0 < B) (b : Fin B → ℕ) :
    (∏ k : Fin B, (atGamma F ((k : ℕ)) * (atD F ((k : ℕ)))⁻¹) ^ (ascentMap F b k))
      = (∏ k : Fin B, (atGamma F ((k : ℕ)) * (atD F ((k : ℕ)))⁻¹) ^ (b k)) ^ (Nat.card F) := by
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl (fun k _ => ?_)
  by_cases hk : (k : ℕ) = 0
  · have hk0 : k = (⟨0, hB⟩ : Fin B) := Fin.ext hk
    subst hk0
    have h0 : (((⟨0, hB⟩ : Fin B)) : ℕ) = 0 := rfl
    rw [h0, atGamma_mul_atD_zero, one_pow]
    simp
  · rw [ascentMap_apply, if_neg hk, add_zero, ← pow_mul, Nat.mul_comm (b k) (Nat.card F)]


/-- **The decomposition of a no-carry partition of `q ^ M - 1`**: every entry is `q` times its
quotient, plus `q - 1` at the index `0` only. -/
lemma noCarry_decomp {B M : ℕ} (hB : 0 < B) (hM : 1 ≤ M) (a : Fin B → ℕ)
    (hsum : (∑ i : Fin B, a i * Nat.card F ^ ((i : ℕ))) = Nat.card F ^ M - 1)
    (hnc : NoCarryVec F a) (k : Fin B) :
    a k = Nat.card F * (a k / Nat.card F) + (if (k : ℕ) = 0 then Nat.card F - 1 else 0) := by
  have hmod : a k % Nat.card F = if (k : ℕ) = 0 then Nat.card F - 1 else 0 := by
    by_cases hk : (k : ℕ) = 0
    · rw [if_pos hk]
      have hk0 : k = (⟨0, hB⟩ : Fin B) := Fin.ext hk
      rw [hk0]
      exact noCarry_zero_mod F hB hM a hsum hnc
    · rw [if_neg hk]
      have hdv : Nat.card F ∣ a k :=
        noCarry_dvd_of_sum F hB hM a hsum hnc (fun h => hk (congrArg Fin.val h))
      exact Nat.mod_eq_zero_of_dvd hdv
  have hdm : Nat.card F * (a k / Nat.card F) + (if (k : ℕ) = 0 then Nat.card F - 1 else 0) = a k := by
    rw [← hmod]
    exact Nat.div_add_mod (a k) (Nat.card F)
  exact hdm.symm

/-- The ascent of a vector bounded by `q ^ M` is bounded by `q ^ (M+1)`. -/
lemma ascentMap_lt {B M : ℕ} (hB : 0 < B) (b : Fin B → ℕ) (hb : ∀ k, b k < Nat.card F ^ M)
    (k : Fin B) : ascentMap F b k < Nat.card F ^ (M + 1) := by
  have hq2 : 2 ≤ Nat.card F := carlitz_card_ge_two F
  rw [ascentMap_apply]
  have hbk : b k ≤ Nat.card F ^ M - 1 := by have := hb k; omega
  have hcase : (if (k : ℕ) = 0 then Nat.card F - 1 else 0) ≤ Nat.card F - 1 := by
    by_cases hk : (k : ℕ) = 0
    · rw [if_pos hk]
    · rw [if_neg hk]; omega
  have hK : Nat.card F * (Nat.card F ^ M - 1) = Nat.card F ^ (M + 1) - Nat.card F := by
    rw [Nat.mul_sub_left_distrib, mul_one, pow_succ, mul_comm]
  have hM1 : Nat.card F ≤ Nat.card F ^ (M + 1) := by
    calc Nat.card F = Nat.card F ^ 1 := (pow_one _).symm
      _ ≤ Nat.card F ^ (M + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have := Nat.mul_le_mul_left (Nat.card F) hbk
  omega

/-- The descent of a vector bounded by `q ^ (M+1)` is bounded by `q ^ M`. -/
lemma descentMap_lt {B M : ℕ} (a : Fin B → ℕ) (ha : ∀ k, a k < Nat.card F ^ (M + 1))
    (k : Fin B) : descentMap F a k < Nat.card F ^ M := by
  have hq2 : 2 ≤ Nat.card F := carlitz_card_ge_two F
  rw [descentMap_apply]
  have h1 : a k / Nat.card F ≤ (Nat.card F ^ (M + 1) - 1) / Nat.card F :=
    Nat.div_le_div_right (by have := ha k; omega)
  have h2 : (Nat.card F ^ (M + 1) - 1) / Nat.card F = Nat.card F ^ M - 1 := by
    have hmul : Nat.card F * (Nat.card F ^ M - 1) = Nat.card F * Nat.card F ^ M - Nat.card F := by
      rw [Nat.mul_sub_left_distrib, mul_one]
    have hle : Nat.card F ≤ Nat.card F * Nat.card F ^ M := by
      calc Nat.card F = Nat.card F * 1 := (mul_one _).symm
        _ ≤ Nat.card F * Nat.card F ^ M :=
            Nat.mul_le_mul_left _ (Nat.one_le_pow M (Nat.card F) (by omega))
    have hsub : Nat.card F ^ (M + 1) - 1
        = Nat.card F * (Nat.card F ^ M - 1) + (Nat.card F - 1) := by
      have hpow : Nat.card F ^ (M + 1) = Nat.card F * Nat.card F ^ M := by rw [pow_succ, mul_comm]
      omega
    rw [hsub, Nat.mul_add_div (by omega : 0 < Nat.card F)]
    have hzero : (Nat.card F - 1) / Nat.card F = 0 := Nat.div_eq_of_lt (by omega)
    rw [hzero, add_zero]
  rw [h2] at h1
  exact lt_of_le_of_lt h1 (Nat.sub_one_lt (pow_pos (by omega) M).ne')


/-- `(p^l * x + r) / p^(j+l) = x / p^j` when `r < p^l`. -/
lemma div_pow_add_of_lt {p l x r j : ℕ} (hp : 0 < p) (hr : r < p ^ l) :
    (p ^ l * x + r) / p ^ (j + l) = x / p ^ j := by
  have h1 : (p ^ l * x + r) / p ^ l = x := by
    rw [Nat.mul_add_div (pow_pos hp l) x r, Nat.div_eq_of_lt hr, add_zero]
  rw [show p ^ (j + l) = p ^ l * p ^ j from by rw [Nat.add_comm, pow_add]]
  rw [← Nat.div_div_eq_div_mul, h1]

/-- The descent is compatible with the partition relation: `∑ a k * q^k = q^(M+1) - 1`,
`a 0 ≡ q - 1` and `q ∣ a k` (`k ≠ 0`) imply `∑ (a k / q) * q^k = q^M - 1`. -/
lemma descentMap_sum {B M : ℕ} (hB : 0 < B) (a : Fin B → ℕ)
    (hsum : (∑ k : Fin B, a k * Nat.card F ^ ((k : ℕ))) = Nat.card F ^ (M + 1) - 1)
    (hnc : NoCarryVec F a) :
    (∑ k : Fin B, descentMap F a k * Nat.card F ^ ((k : ℕ))) = Nat.card F ^ M - 1 := by
  have hq2 : 2 ≤ Nat.card F := carlitz_card_ge_two F
  have hsplit : (∑ k : Fin B, a k * Nat.card F ^ ((k : ℕ)))
      = Nat.card F * (∑ k : Fin B, descentMap F a k * Nat.card F ^ ((k : ℕ)))
        + (Nat.card F - 1) := by
    have hterm : ∀ k : Fin B, a k * Nat.card F ^ ((k : ℕ))
        = Nat.card F * (descentMap F a k * Nat.card F ^ ((k : ℕ)))
          + (if (k : ℕ) = 0 then Nat.card F - 1 else 0) * Nat.card F ^ ((k : ℕ)) := by
      intro k
      rw [noCarry_decomp F hB (by omega) a hsum hnc k, descentMap_apply]
      ring
    calc (∑ k : Fin B, a k * Nat.card F ^ ((k : ℕ)))
        = ∑ k : Fin B, (Nat.card F * (descentMap F a k * Nat.card F ^ ((k : ℕ)))
            + (if (k : ℕ) = 0 then Nat.card F - 1 else 0) * Nat.card F ^ ((k : ℕ))) :=
          Finset.sum_congr rfl (fun k _ => hterm k)
      _ = (∑ k : Fin B, Nat.card F * (descentMap F a k * Nat.card F ^ ((k : ℕ))))
            + (∑ k : Fin B, (if (k : ℕ) = 0 then Nat.card F - 1 else 0)
                * Nat.card F ^ ((k : ℕ))) := Finset.sum_add_distrib
      _ = Nat.card F * (∑ k : Fin B, descentMap F a k * Nat.card F ^ ((k : ℕ)))
            + (Nat.card F - 1) := by
          rw [ascentMap_pair_sum F hB, Finset.mul_sum]
  have hkey : Nat.card F * (∑ k : Fin B, descentMap F a k * Nat.card F ^ ((k : ℕ)))
      = Nat.card F * (Nat.card F ^ M - 1) := by
    have hpow : Nat.card F ^ (M + 1) = Nat.card F * Nat.card F ^ M := by rw [pow_succ, mul_comm]
    have := hsplit.symm.trans hsum
    rw [Nat.mul_sub_left_distrib, mul_one]
    omega
  exact Nat.eq_of_mul_eq_mul_left (by omega) hkey

/-- The descent preserves the no-carry condition. -/
lemma descentMap_noCarry {B M : ℕ} (hB : 0 < B) (a : Fin B → ℕ)
    (hsum : (∑ k : Fin B, a k * Nat.card F ^ ((k : ℕ))) = Nat.card F ^ (M + 1) - 1)
    (hnc : NoCarryVec F a) : NoCarryVec F (descentMap F a) := by
  obtain ⟨l, hp, hpq⟩ := card_eq_ringChar_pow F
  have hp0 : 0 < ringChar F := hp.pos
  intro j
  have hterm : ∀ k : Fin B, descentMap F a k / (ringChar F) ^ j % (ringChar F)
      = a k / (ringChar F) ^ (j + l) % (ringChar F) := by
    intro k
    rw [descentMap_apply, hpq]
    have hdec := noCarry_decomp F hB (by omega) a hsum hnc k
    rw [hpq] at hdec
    conv_rhs => rw [hdec]
    rw [div_pow_add_of_lt (p := ringChar F) (l := l) (x := a k / (ringChar F) ^ l) (j := j) hp0 ?_]
    by_cases hk : (k : ℕ) = 0
    · rw [if_pos hk]
      exact Nat.sub_one_lt (pow_pos hp0 l).ne'
    · rw [if_neg hk]
      exact pow_pos hp0 l
  rw [Finset.sum_congr rfl (fun k _ => hterm k)]
  exact hnc (j + l)


lemma ascentMap_div {B : ℕ} (b : Fin B → ℕ) (k : Fin B) :
    ascentMap F b k / Nat.card F = b k := by
  have hq2 : 2 ≤ Nat.card F := carlitz_card_ge_two F
  rw [ascentMap_apply]
  have hcase : (if (k : ℕ) = 0 then Nat.card F - 1 else 0) < Nat.card F := by
    by_cases hk : (k : ℕ) = 0
    · rw [if_pos hk]; omega
    · rw [if_neg hk]; omega
  rw [Nat.add_comm, Nat.add_mul_div_left _ _ (by omega : 0 < Nat.card F),
    Nat.div_eq_of_lt hcase, zero_add]

lemma ascentMap_mod {B : ℕ} (b : Fin B → ℕ) (k : Fin B) :
    ascentMap F b k % Nat.card F = if (k : ℕ) = 0 then Nat.card F - 1 else 0 := by
  have hq2 : 2 ≤ Nat.card F := carlitz_card_ge_two F
  rw [ascentMap_apply]
  have hcase : (if (k : ℕ) = 0 then Nat.card F - 1 else 0) < Nat.card F := by
    by_cases hk : (k : ℕ) = 0
    · rw [if_pos hk]; omega
    · rw [if_neg hk]; omega
  rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hcase]

lemma descentMap_ascentMap {B : ℕ} (b : Fin B → ℕ) :
    descentMap F (ascentMap F b) = b := by
  funext k
  rw [descentMap_apply, ascentMap_div]

lemma ascentMap_descentMap {B M : ℕ} (hB : 0 < B) (hM : 1 ≤ M) (a : Fin B → ℕ)
    (hsum : (∑ k : Fin B, a k * Nat.card F ^ ((k : ℕ))) = Nat.card F ^ M - 1)
    (hnc : NoCarryVec F a) :
    ascentMap F (descentMap F a) = a := by
  funext k
  rw [ascentMap_apply, descentMap_apply]
  exact (noCarry_decomp F hB hM a hsum hnc k).symm

lemma multinomial_ascentMap {B : ℕ} (hB : 0 < B) (b : Fin B → ℕ) :
    ((Nat.multinomial Finset.univ (ascentMap F b) : ℕ) : atQ F)
      = ((Nat.multinomial Finset.univ b : ℕ) : atQ F) ^ (Nat.card F) := by
  obtain ⟨l, hp, hpq⟩ := card_eq_ringChar_pow F
  have hmod : (fun k : Fin B => ascentMap F b k % (ringChar F) ^ l)
      = fun k : Fin B => (if (k : ℕ) = 0 then (ringChar F) ^ l - 1 else 0) := by
    funext k
    rw [← hpq, ascentMap_mod F b k]
  have hdiv : (fun k : Fin B => ascentMap F b k / (ringChar F) ^ l) = b := by
    funext k
    rw [← hpq, ascentMap_div F b k]
  have hone : ((Nat.multinomial Finset.univ
      (fun k : Fin B => (if (k : ℕ) = 0 then (ringChar F) ^ l - 1 else 0)) : ℕ)
        : ZMod (ringChar F)) = 1 := by
    have hcong : Nat.multinomial ({⟨0, hB⟩} : Finset (Fin B))
          (fun k : Fin B => if (k : ℕ) = 0 then (ringChar F) ^ l - 1 else 0)
        = Nat.multinomial Finset.univ
          (fun k : Fin B => if (k : ℕ) = 0 then (ringChar F) ^ l - 1 else 0) :=
      Nat.multinomial_congr_of_sdiff (fun x _ => Finset.mem_univ x)
        (fun x hx => by
          rw [Finset.mem_sdiff] at hx
          rw [if_neg]
          intro h
          exact hx.2 (Finset.mem_singleton.mpr (Fin.ext h)))
        (fun x _ => rfl)
    rw [← hcong, Nat.multinomial_singleton]
    exact Nat.cast_one
  have hdz : ((Nat.multinomial Finset.univ (ascentMap F b) : ℕ) : ZMod (ringChar F))
      = ((Nat.multinomial Finset.univ b : ℕ) : ZMod (ringChar F)) := by
    rw [Commons.Combinatorics.Multinomial.digit_reduction (ringChar F) l hp (ascentMap F b),
      hmod, hdiv, hone, one_mul]
  have heq : ((Nat.multinomial Finset.univ (ascentMap F b) : ℕ) : atQ F)
      = ((Nat.multinomial Finset.univ b : ℕ) : atQ F) := by
    refine (CharP.cast_eq_iff_mod_eq (R := atQ F) (p := ringChar F)).mpr ?_
    exact (ZMod.natCast_eq_natCast_iff _ _ (ringChar F)).mp hdz
  rw [heq, natCast_pow_card_eq F]

open Classical in
/-- **Chen's Step 1 (the Frobenius descent)**: `c_{q ^ (M+1) - 1} = (c_{q ^ M - 1}) ^ q`. -/
theorem atCoeff_card_pow_sub_one_succ (M : ℕ) :
    atCoeff F (Nat.card F ^ (M + 1) - 1)
      = (atCoeff F (Nat.card F ^ M - 1)) ^ (Nat.card F) := by
  have hq2 : 2 ≤ Nat.card F := carlitz_card_ge_two F
  have hsub1 : Nat.card F ^ (M + 1) - 1 + 1 = Nat.card F ^ (M + 1) :=
    Nat.sub_add_cancel (Nat.one_le_pow (M + 1) (Nat.card F) (by omega))
  have hsub2 : Nat.card F ^ M - 1 + 1 = Nat.card F ^ M :=
    Nat.sub_add_cancel (Nat.one_le_pow M (Nat.card F) (by omega))
  have hle : Nat.card F ^ M ≤ Nat.card F ^ (M + 1) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  rw [atCoeff_eq_sum_multi F (Nat.card F ^ (M + 1) - 1) (Nat.card F ^ (M + 1))
      (by rw [hsub1]),
    atCoeff_eq_sum_multi F (Nat.card F ^ M - 1) (Nat.card F ^ (M + 1))
      (by rw [Nat.sub_add_cancel (Nat.one_le_pow M (Nat.card F) (by omega))]; exact hle),
    hsub1, hsub2, carlitz_sum_pow_card]
  refine Finset.sum_bij (fun a _ => descentMap F a) ?_ ?_ ?_ ?_
  · -- the descent lands in the level-`M` set
    intro a ha
    rw [Finset.mem_filter, Fintype.mem_piFinset] at ha ⊢
    obtain ⟨hbound, hsum, hnc⟩ := ha
    refine ⟨?_, ?_, ?_⟩
    · intro k
      exact Finset.mem_range.mpr (descentMap_lt F a (fun j => Finset.mem_range.mp (hbound j)) k)
    · exact descentMap_sum F (B := Nat.card F ^ (M + 1)) (by positivity) a hsum hnc
    · exact descentMap_noCarry F (B := Nat.card F ^ (M + 1)) (by positivity) a hsum hnc
  · -- injectivity
    intro a₁ ha₁ a₂ ha₂ heq
    rw [Finset.mem_filter, Fintype.mem_piFinset] at ha₁ ha₂
    obtain ⟨-, hsum₁, hnc₁⟩ := ha₁
    obtain ⟨-, hsum₂, hnc₂⟩ := ha₂
    have h1 := ascentMap_descentMap F (B := Nat.card F ^ (M + 1)) (by positivity)
      (by omega) a₁ hsum₁ hnc₁
    have h2 := ascentMap_descentMap F (B := Nat.card F ^ (M + 1)) (by positivity)
      (by omega) a₂ hsum₂ hnc₂
    rw [← h1, ← h2, heq]
  · -- surjectivity
    intro b hb
    rw [Finset.mem_filter, Fintype.mem_piFinset] at hb
    obtain ⟨hbound, hsum, hnc⟩ := hb
    refine ⟨ascentMap F b, ?_, descentMap_ascentMap F b⟩
    rw [Finset.mem_filter, Fintype.mem_piFinset]
    refine ⟨?_, ?_, ?_⟩
    · intro k
      exact Finset.mem_range.mpr
        (ascentMap_lt F (B := Nat.card F ^ (M + 1)) (by positivity) b
          (fun j => Finset.mem_range.mp (hbound j)) k)
    · exact ascentMap_sum F (B := Nat.card F ^ (M + 1)) (by positivity) b hsum
    · exact ascentMap_noCarry F (B := Nat.card F ^ (M + 1)) (by positivity) b hnc
  · -- the summands
    intro a ha
    rw [Finset.mem_filter, Fintype.mem_piFinset] at ha
    obtain ⟨-, hsum, hnc⟩ := ha
    have hdec : ascentMap F (descentMap F a) = a := by
      refine ascentMap_descentMap F (B := Nat.card F ^ (M + 1)) (by positivity) ?_ a hsum hnc
      omega
    rw [← hdec, multinomial_ascentMap F (B := Nat.card F ^ (M + 1)) (by positivity) (descentMap F a),
      ascentMap_prod F (B := Nat.card F ^ (M + 1)) (by positivity) (descentMap F a), ← mul_pow,
      descentMap_ascentMap]

end ZagierHoffmanPositiveChar

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F]

/-- ★★★ **Chen's Step 1** (arXiv:1506.06463, Theorem 3.3 for `N_i = 0`): the Anderson–Thakur
coefficient `c_{q ^ M - 1}` equals `1` for every `M`.  Equivalently
`H_{q^M-1} = Γ_{q^M}` in the `H`-normalisation, i.e. `α_{q^M} = Γ_{q^M}`. -/
theorem atCoeff_card_pow_sub_one (M : ℕ) : atCoeff F (Nat.card F ^ M - 1) = 1 := by
  induction M with
  | zero => rw [pow_zero, Nat.sub_self]; exact atCoeff_zero F
  | succ M ih => rw [atCoeff_card_pow_sub_one_succ F M, ih, one_pow]


end ZagierHoffmanPositiveChar
