/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submission.ZagierHoffmanProof.PrimeZeta
import Submission.ZagierHoffmanProof.AnyQ

set_option autoImplicit false
set_option maxHeartbeats 4000000

open Polynomial RatFunc
open scoped BigOperators WithZero
open WithZero

/-!
# `F_q`-linear independence of MZVs of distinct degree over a prime field

Over a field `F` of **prime** cardinality the exact `∞`-adic valuation of *every* MZV is known
(`PrimeZeta.val_zeta_prime`, Thakur's Theorem 1 and its multizeta consequence): with
`T(k) = k + jMin k` and

  `sSeqG F r 𝔰 (r-1) = Σ_{j<r} Σ_{i < r-1-j} T^{i+1}(𝔰_j)`,

one has `v (ζ_A F 𝔰) = exp (-(sSeqG F r 𝔰 (r-1)))`.  Hence the classical "distinct valuations"
argument gives:

★ `zeta_linearIndependent_prime`: over a field of prime cardinality, MZVs of pairwise distinct
  degrees are linearly independent over the base field.

This strictly generalises `DegAnyF.zeta_linearIndependent_le_card` (which is restricted to tuples
with entries `≤ q`, valid for every finite field) and `LinIndep.zeta_linearIndependent_entriesVal`
(entries `q^k·m`, `m ≤ q`): over a prime field no restriction on the entries is needed, only the
distinctness of the degrees.

Everything in this file is unconditional for prime `q`.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- The degree exponent `sSeqG F r 𝔰 (r-1)` of the tuple `𝔰` (prime `q`). -/
noncomputable def degPrime {r : ℕ} (𝔰 : Fin r → ℕ+) : ℤ := sSeqG F r 𝔰 (r - 1)

/-- The exact degree of an MZV over a prime field. -/
theorem val_zeta_sSeqG (hp : (Nat.card F).Prime) {r : ℕ} (hr : 1 ≤ r) (𝔰 : Fin r → ℕ+) :
    Valued.v (ζ_A F 𝔰) = WithZero.exp (-(sSeqG F r 𝔰 (r - 1))) :=
  val_zeta_prime F hp (by omega) 𝔰

/-- ★★★ **Over a field of prime cardinality, MZVs of pairwise distinct degrees are linearly
independent over the base field.** -/
theorem zeta_linearIndependent_prime {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hp : (Nat.card F).Prime)
    (𝔰 : ι → Σ r : ℕ, Fin r → ℕ+)
    (hr : ∀ i, 1 ≤ (𝔰 i).1)
    (hdeg : Function.Injective (fun i => sSeqG F (𝔰 i).1 (𝔰 i).2 ((𝔰 i).1 - 1)))
    (c : ι → F) (h : (∑ i, cst F (c i) * ζ_A F (𝔰 i).2) = 0) :
    ∀ i, c i = 0 := by
  classical
  set I : Finset ι := Finset.univ.filter (fun i => c i ≠ 0) with hI
  by_contra hcon
  simp only [not_forall] at hcon
  obtain ⟨i0, hi0⟩ := hcon
  have hInon : I.Nonempty := ⟨i0, by simp [hI, hi0]⟩
  obtain ⟨j0, hj0I, hj0min⟩ :=
    Finset.exists_min_image I (fun i => sSeqG F (𝔰 i).1 (𝔰 i).2 ((𝔰 i).1 - 1)) hInon
  have hcj0 : c j0 ≠ 0 := by
    have h' := hj0I
    rw [hI] at h'
    simpa using h'
  have hsub : (∑ i ∈ I, cst F (c i) * ζ_A F (𝔰 i).2)
      = ∑ i, cst F (c i) * ζ_A F (𝔰 i).2 := by
    rw [hI]
    refine Finset.sum_subset (Finset.filter_subset _ _) ?_
    intro i _ hi
    have hci : c i = 0 := by
      by_contra hc
      exact hi (by simp [hc])
    have hz : cst F (0 : F) = 0 := map_zero (cstHom F)
    rw [hci, hz, zero_mul]
  have hv : ∀ i ∈ I \ {j0},
      Valued.v (cst F (c i) * ζ_A F (𝔰 i).2)
        < Valued.v (cst F (c j0) * ζ_A F (𝔰 j0).2) := by
    intro i hi
    rw [Finset.mem_sdiff, Finset.mem_singleton] at hi
    obtain ⟨hiI, hij⟩ := hi
    have hci : c i ≠ 0 := by
      have h' := hiI
      rw [hI] at h'
      simpa using h'
    rw [map_mul, map_mul, v_cst_of_ne_zero F hci, v_cst_of_ne_zero F hcj0, one_mul, one_mul,
      val_zeta_sSeqG F hp (hr i) (𝔰 i).2, val_zeta_sSeqG F hp (hr j0) (𝔰 j0).2,
      WithZero.exp_lt_exp]
    have h2 := hj0min i hiI
    have h3 : sSeqG F (𝔰 i).1 (𝔰 i).2 ((𝔰 i).1 - 1)
        ≠ sSeqG F (𝔰 j0).1 (𝔰 j0).2 ((𝔰 j0).1 - 1) := fun hh => hij (hdeg hh)
    omega
  have hval' := Valuation.map_sum_eq_of_lt (v := Valued.v) hj0I hv
  have hzero : Valued.v (∑ i ∈ I, cst F (c i) * ζ_A F (𝔰 i).2) = 0 := by
    rw [hsub, h, map_zero]
  rw [hval', map_mul, v_cst_of_ne_zero F hcj0, one_mul,
    val_zeta_sSeqG F hp (hr j0) (𝔰 j0).2] at hzero
  exact WithZero.exp_ne_zero hzero

end ZagierHoffmanPositiveChar

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-! ## The degree-collision obstruction at weight `q + 2` -/

/-- For a prime field, `jMin (q+1) = q−1`. -/
lemma jMin_card_add_one (hp : (Nat.card F).Prime) :
    jMin F ⟨Nat.card F + 1, by have h := card_ge_two F; omega⟩ = Nat.card F - 1 := by
  have hq2 : 2 ≤ Nat.card F := two_le_card F
  have hnc : noCarry (Nat.card F) (Nat.card F - 1) (Nat.card F) := by
    intro i
    rcases Nat.eq_zero_or_pos i with hi0 | hipos
    · subst hi0
      have hmod : (Nat.card F - 1) % Nat.card F = Nat.card F - 1 :=
        Nat.mod_eq_of_lt (by omega)
      rw [pow_zero, Nat.div_one, Nat.div_one, hmod, Nat.mod_self, add_zero]
      omega
    · have hipos' : 1 ≤ i := hipos
      have h1 : (Nat.card F - 1) / Nat.card F ^ i = 0 := by
        apply Nat.div_eq_of_lt
        calc Nat.card F - 1 < Nat.card F := by omega
          _ ≤ Nat.card F ^ i := Nat.le_pow hipos
      have h2 : Nat.card F / Nat.card F ^ i % Nat.card F = if i = 1 then 1 else 0 := by
        rcases lt_or_eq_of_le hipos' with h | h
        · have hzero : Nat.card F / Nat.card F ^ i = 0 := by
            apply Nat.div_eq_of_lt
            calc Nat.card F = Nat.card F ^ 1 := (pow_one _).symm
              _ < Nat.card F ^ i := Nat.pow_lt_pow_right (by omega) h
          rw [hzero, if_neg (by omega), Nat.zero_mod]
        · subst h
          rw [pow_one, Nat.div_self (by omega : 0 < Nat.card F),
            if_pos rfl, Nat.mod_eq_of_lt (by omega : 1 < Nat.card F)]
      rw [h1, h2]
      by_cases h : i = 1
      · subst h
        rw [if_pos rfl, Nat.zero_mod]
        have := card_ge_two F
        omega
      · rw [if_neg h, Nat.zero_mod]
        have := card_ge_two F
        omega
  apply le_antisymm
  · have hgood : IsGoodJ F (Nat.card F + 1) (Nat.card F - 1) := by
      haveI : CharP F (Nat.card F) := charP_of_card_prime F hp
      have hring : ringChar F = Nat.card F := ringChar.eq F (Nat.card F)
      rw [isGoodJ_iff_noCarry_char F (Nat.card F + 1) (Nat.card F - 1) (by omega)]
      refine ⟨by omega, dvd_refl _, ?_⟩
      rw [hring]
      exact hnc
    exact jMin_le F hgood
  · have h1 : 1 ≤ jMin F ⟨Nat.card F + 1, by have h := card_ge_two F; omega⟩ :=
      jMin_pos F _
    have h2 : Nat.card F - 1 ∣ jMin F ⟨Nat.card F + 1, by have h := card_ge_two F; omega⟩ :=
      jMin_dvd F _
    obtain ⟨m, hm⟩ := h2
    have hm1 : 1 ≤ m := by
      by_contra hcon
      have h0 : m = 0 := by omega
      rw [h0, mul_zero] at hm
      omega
    have : Nat.card F - 1 ≤ (Nat.card F - 1) * m := by
      calc Nat.card F - 1 = (Nat.card F - 1) * 1 := (mul_one _).symm
        _ ≤ (Nat.card F - 1) * m := Nat.mul_le_mul_left _ hm1
    omega

/-- ★ **The degree exponent of the level-one blocks `(2,·)` and `(q+1,·)` agrees over a prime
field**: `T 2 = T (q+1) = 2q`.  Consequently the tuples `(2,q)` and `(q+1,1)` — both of weight
`q+2` — have the same MZV degree, so the "distinct degrees" argument cannot prove `F_q`-linear
independence of the MZVs of weight `q+2` (independence nevertheless holds up to weight `2q`
by arXiv 2604.25451). -/
theorem TT_two_eq_TT_card_add_one (hp : (Nat.card F).Prime) :
    TT (Nat.card F) (two_le_card F) 2 = TT (Nat.card F) (two_le_card F) (Nat.card F + 1) := by
  have hq2 : 2 ≤ Nat.card F := two_le_card F
  rw [TT_eq_add_jMin F hp (by omega : 1 ≤ 2),
    TT_eq_add_jMin F hp (by omega : 1 ≤ Nat.card F + 1), jMin_card_add_one F hp,
    jMin_eq_pred_mul_char F (by omega : 1 ≤ 2) hq2]
  omega

end ZagierHoffmanPositiveChar
