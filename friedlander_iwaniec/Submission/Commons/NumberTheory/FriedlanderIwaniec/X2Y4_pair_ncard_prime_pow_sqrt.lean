import Mathlib
import Submission.Commons.NumberTheory.FriedlanderIwaniec.X2Y4_pair_roots_mod_prime_pow_card_mod_four_one
import Submission.Commons.NumberTheory.FriedlanderIwaniec.X2Y4_pair_roots_mod_prime_pow_card_mod_four_three
import Submission.Commons.NumberTheory.FriedlanderIwaniec.X2Y4_fiber_ncard_le_prime_pow
import Submission.Commons.NumberTheory.FriedlanderIwaniec.X2Y4_sum_pow_sq_valZ_lt
import Submission.Commons.Analysis.Real.X2Y4_prime_pow_sqrt_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.style.haveILetI false

namespace Commons.NumberTheory.FriedlanderIwaniec

open Finset

/-- For `y ∈ ZMod (p ^ e)`, the fourth power `y ^ 4` vanishes exactly when the
`p`-adic valuation of `y` is at least `⌈e / 4⌉ = (e + 3) / 4`. -/
private lemma X2Y4_pow_four_eq_zero_iff_valZ {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e)
    (y : ZMod (p ^ e)) :
    (y ^ 4 = 0) ↔ ((e + 3) / 4 ≤ X2Y4_valZ p e y) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero (p ^ e) := ⟨(pow_pos hp.pos e).ne'⟩
  set V := (e + 3) / 4 with hV
  have hVle : V ≤ e := by omega
  have h4Vge : e ≤ 4 * V := by omega
  have h4Vle : 4 * V ≤ e + 3 := by omega
  have hycast : y ^ 4 = (((y.val ^ 4 : ℕ)) : ZMod (p ^ e)) := by
    nth_rewrite 1 [← ZMod.natCast_zmod_val y]
    rw [← Nat.cast_pow]
  constructor
  · intro hy
    by_contra hlt
    rw [not_le] at hlt
    have hyne : y ≠ 0 := by
      rintro rfl
      simp [X2Y4_valZ] at hlt
      omega
    have hval : X2Y4_valZ p e y = padicValNat p y.val := by simp [X2Y4_valZ, hyne]
    rw [hval] at hlt
    have hyv : y.val ≠ 0 := by
      intro h0; exact hyne (by rw [← ZMod.natCast_zmod_val y, h0]; simp)
    have h4v : 4 * padicValNat p y.val < e := by
      have h1 : padicValNat p y.val ≤ V - 1 := by omega
      omega
    have hndvd : ¬ p ^ e ∣ y.val ^ 4 := by
      intro hd
      have hle : e ≤ padicValNat p (y.val ^ 4) :=
        (padicValNat_dvd_iff_le (pow_ne_zero 4 hyv)).mp hd
      rw [padicValNat.pow] at hle
      omega
    rw [hycast, ZMod.natCast_eq_zero_iff] at hy
    exact hndvd hy
  · intro hge
    by_cases hy : y = 0
    · subst hy; simp
    have hval : X2Y4_valZ p e y = padicValNat p y.val := by simp [X2Y4_valZ, hy]
    rw [hval] at hge
    have hyv : y.val ≠ 0 := by
      intro h0; exact hy (by rw [← ZMod.natCast_zmod_val y, h0]; simp)
    have hdvd : p ^ e ∣ y.val ^ 4 := by
      have hge4 : e ≤ 4 * padicValNat p y.val := by omega
      exact (padicValNat_dvd_iff_le (pow_ne_zero 4 hyv)).mpr (by rw [padicValNat.pow]; omega)
    rw [hycast, ZMod.natCast_eq_zero_iff]
    exact hdvd

/-- Fibre bound over the second coordinate: the number of `x` with `x ^ 2 + y ^ 4 = 0`
is `p ^ (e / 2)` when `y ^ 4 = 0` and at most `2 * p ^ (2 v_p(y))` otherwise. -/
private lemma X2Y4_fiber_bound_if {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e) (y : ZMod (p ^ e)) :
    ({x : ZMod (p ^ e) | x ^ 2 + y ^ 4 = 0}).ncard
      ≤ (if y ^ 4 = 0 then p ^ (e / 2) else 2 * p ^ (2 * X2Y4_valZ p e y)) := by
  by_cases hy4 : y ^ 4 = 0
  · rw [if_pos hy4]
    have hset : ({x : ZMod (p ^ e) | x ^ 2 + y ^ 4 = 0} : Set (ZMod (p ^ e)))
        = {x : ZMod (p ^ e) | x ^ 2 = 0} := by
      ext x; rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, hy4, add_zero]
    rw [hset]
    exact le_of_eq (X2Y4_ncard_sq_zero_prime_pow hp he)
  · rw [if_neg hy4]
    have hy : y ≠ 0 := fun h => hy4 (by rw [h]; simp)
    have hval : X2Y4_valZ p e y = padicValNat p y.val := by simp [X2Y4_valZ, hy]
    rw [hval]
    have hlt : X2Y4_valZ p e y < (e + 3) / 4 := by
      by_contra hcon
      rw [not_lt] at hcon
      exact hy4 ((X2Y4_pow_four_eq_zero_iff_valZ hp he y).mpr hcon)
    rw [hval] at hlt
    have h4 : 4 * padicValNat p y.val < e := by
      have h1 : padicValNat p y.val ≤ (e + 3) / 4 - 1 := by omega
      have h2 : 4 * ((e + 3) / 4) ≤ e + 3 := by omega
      omega
    exact X2Y4_fiber_ncard_le_prime_pow hp he hy h4

theorem X2Y4_pair_ncard_prime_pow_sqrt {p e : ℕ} (hp : p.Prime) (he : 2 ≤ e) :
    (({x : ZMod (p ^ e) × ZMod (p ^ e) | x.1 ^ 2 + x.2 ^ 4 = 0}).ncard : ℝ)
      ≤ 3 * (p : ℝ) ^ (e - 1) * Real.sqrt ((p : ℝ) ^ e) := by
  have he1 : 1 ≤ e := by omega
  haveI : NeZero (p ^ e) := ⟨(pow_pos hp.pos e).ne'⟩
  -- fibrewise upper bound
  have hsum_le : ({x : ZMod (p ^ e) × ZMod (p ^ e) | x.1 ^ 2 + x.2 ^ 4 = 0}).ncard
      ≤ ∑ y : ZMod (p ^ e),
          (if y ^ 4 = 0 then p ^ (e / 2) else 2 * p ^ (2 * X2Y4_valZ p e y)) := by
    rw [X2Y4_ncard_eq_sum_fiber]
    exact Finset.sum_le_sum (fun y _ => X2Y4_fiber_bound_if hp he1 y)
  -- the filter of `y` with `y ^ 4 ≠ 0` is the valuation filter `valZ < (e+3)/4`
  have hNotFilter : (Finset.univ.filter (fun y : ZMod (p ^ e) => ¬ y ^ 4 = 0))
      = (Finset.univ.filter (fun y : ZMod (p ^ e) => X2Y4_valZ p e y < (e + 3) / 4)) := by
    ext y
    rw [Finset.mem_filter, Finset.mem_filter]
    constructor
    · rintro ⟨-, hy4⟩
      refine ⟨Finset.mem_univ _, ?_⟩
      by_contra hcon
      rw [not_lt] at hcon
      exact hy4 ((X2Y4_pow_four_eq_zero_iff_valZ hp he1 y).mpr hcon)
    · rintro ⟨-, hlt⟩
      refine ⟨Finset.mem_univ _, ?_⟩
      intro hy4
      have := (X2Y4_pow_four_eq_zero_iff_valZ hp he1 y).mp hy4
      omega
  -- evaluate the cardinality of the vanishing-fourth-power set
  have hfilter_card : (Finset.univ.filter (fun y : ZMod (p ^ e) => y ^ 4 = 0)).card
      = p ^ (e - (e + 3) / 4) := by
    rw [← Fintype.card_subtype (fun y : ZMod (p ^ e) => y ^ 4 = 0)]
    rw [show Fintype.card {y : ZMod (p ^ e) // y ^ 4 = 0}
        = Fintype.card (↥{y : ZMod (p ^ e) | y ^ 4 = 0}) from rfl, Set.fintypeCard_eq_ncard]
    exact ncard_pow_four_eq_zero_zmod_prime_pow p e hp he1
  -- split the sum according to `y ^ 4 = 0`
  have hsum_eq : (∑ y : ZMod (p ^ e),
        (if y ^ 4 = 0 then p ^ (e / 2) else 2 * p ^ (2 * X2Y4_valZ p e y)))
      = p ^ (e / 2) * (Finset.univ.filter (fun y : ZMod (p ^ e) => y ^ 4 = 0)).card
        + 2 * (∑ y ∈ (Finset.univ : Finset (ZMod (p ^ e))).filter
              (fun y => X2Y4_valZ p e y < (e + 3) / 4),
            p ^ (2 * X2Y4_valZ p e y)) := by
    rw [← Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset (ZMod (p ^ e))))
          (p := fun y : ZMod (p ^ e) => y ^ 4 = 0)
          (f := fun y => if y ^ 4 = 0 then p ^ (e / 2) else 2 * p ^ (2 * X2Y4_valZ p e y))]
    congr 1
    · have hconst : ∀ y ∈ (Finset.univ.filter (fun y : ZMod (p ^ e) => y ^ 4 = 0)),
          (if y ^ 4 = 0 then p ^ (e / 2) else 2 * p ^ (2 * X2Y4_valZ p e y)) = p ^ (e / 2) := by
        intro y hy
        rw [if_pos (Finset.mem_filter.mp hy).2]
      rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul, mul_comm]
    · rw [hNotFilter, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y hy
      have hlt : X2Y4_valZ p e y < (e + 3) / 4 := (Finset.mem_filter.mp hy).2
      have hy4 : y ^ 4 ≠ 0 := fun h =>
        absurd ((X2Y4_pow_four_eq_zero_iff_valZ hp he1 y).mp h) (by omega)
      rw [if_neg hy4]
  -- natural-number bound
  have hNat : ({x : ZMod (p ^ e) × ZMod (p ^ e) | x.1 ^ 2 + x.2 ^ 4 = 0}).ncard
      ≤ p ^ (e / 2 + (e - (e + 3) / 4)) + 2 * p ^ (e + (e + 3) / 4 - 1) := by
    refine le_trans hsum_le ?_
    rw [hsum_eq, hfilter_card, X2Y4_sum_pow_sq_valZ_lt hp he1]
    have h1 : p ^ (e / 2) * p ^ (e - (e + 3) / 4) = p ^ (e / 2 + (e - (e + 3) / 4)) := by
      rw [← pow_add]
    have h2 : p ^ (e - 1) * (p ^ ((e + 3) / 4) - 1) ≤ p ^ (e + (e + 3) / 4 - 1) := by
      calc p ^ (e - 1) * (p ^ ((e + 3) / 4) - 1)
          ≤ p ^ (e - 1) * p ^ ((e + 3) / 4) := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
        _ = p ^ (e + (e + 3) / 4 - 1) := by rw [← pow_add]; congr 1; omega
    rw [h1]
    exact Nat.add_le_add_left (Nat.mul_le_mul_left 2 h2) _
  -- real comparison
  have hreal := Commons.Analysis.Real.X2Y4_prime_pow_sqrt_bound (p := p) (e := e) hp.two_le he
  calc (({x : ZMod (p ^ e) × ZMod (p ^ e) | x.1 ^ 2 + x.2 ^ 4 = 0}).ncard : ℝ)
      ≤ ((p ^ (e / 2 + (e - (e + 3) / 4)) + 2 * p ^ (e + (e + 3) / 4 - 1) : ℕ) : ℝ) := by
        exact_mod_cast hNat
    _ = (p : ℝ) ^ (e / 2 + (e - (e + 3) / 4)) + 2 * (p : ℝ) ^ (e + (e + 3) / 4 - 1) := by
        push_cast; ring
    _ ≤ 3 * (p : ℝ) ^ (e - 1) * Real.sqrt ((p : ℝ) ^ e) := hreal

end Commons.NumberTheory.FriedlanderIwaniec
