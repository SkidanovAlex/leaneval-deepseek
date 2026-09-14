

import Mathlib
import Submission.Vdw.MultiPrimeFourier
import Submission.Vdw.MultiPrimeSigma
import Submission.Commons.NumberTheory.Nat.crt_combination_bijective_pi

open Finset
open scoped BigOperators

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-!
# Beginning of the multi-prime assembly: coefficient bounds and reindexing

Two inputs for the multi-prime §4 assembly:

* `indexFourierCoeff_le`: from `MIndexBound` (the paper's Proposition
  `ftgen2`) plus the crude cardinality bound `indexClassFinset_card_le` one
  gets the pointwise per-prime coefficient bound
  `‖indexFourierCoeff p n k a‖ ≤ K·p^{n-k}·(if a = 0 then 1 else p^{-1/2})`
  with `K = max C₀ 2^((n+1)^4)`.
* `multiPrime_sum_reindex`: the frequency-tuple sum of a function of the CRT
  combination `a ↦ (Σ_p (-(a p j)).val·(C/p))_j` equals the sum over the
  frequencies modulo `C = ∏ p ∈ s, p` — the bijection
  `Commons.NumberTheory.Nat.crt_combination_bijective_pi` composed with the
  (involutive) componentwise negation, via `Fintype.sum_bijective`.

Axioms: propext / Classical.choice / Quot.sound only.
-/


namespace Submission.Vdw
noncomputable section

/-- The pointwise coefficient bound coming from `MIndexBound` together with the
crude cardinality bound for the zero frequency. -/
theorem indexFourierCoeff_le (n : ℕ) (hM : MIndexBound n) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (p : ℕ) [Fact (Nat.Prime p)] (k : ℕ), k ≤ n →
      ∀ a : Fin n → ZMod p,
        ‖indexFourierCoeff p n k a‖ ≤ K * (p : ℝ) ^ ((n : ℝ) - (k : ℝ)) *
          (if a = 0 then 1 else (p : ℝ) ^ (-(1/2) : ℝ)) := by
  obtain ⟨C₀, hC₀0, hC₀⟩ := hM
  refine ⟨max C₀ ((2 : ℝ) ^ ((n + 1) ^ 4)), le_max_of_le_left hC₀0, ?_⟩
  intro p _ k hk a
  haveI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by
    have h : 1 ≤ p := (Fact.out : Nat.Prime p).one_lt.le
    exact_mod_cast h
  have hp0 : (0 : ℝ) < (p : ℝ) := lt_of_lt_of_le one_pos hp1
  have hpk : ((p ^ (n - k) : ℕ) : ℝ) = (p : ℝ) ^ ((n : ℝ) - (k : ℝ)) := by
    rw [Nat.cast_pow, ← Real.rpow_natCast (p : ℝ) (n - k), Nat.cast_sub hk]
  by_cases ha : a = 0
  · subst ha
    have hnorm : ‖indexFourierCoeff p n k 0‖ = ((indexClassFinset p n k).card : ℝ) := by
      rw [indexFourierCoeff]
      simp
    rw [hnorm, if_pos rfl, mul_one]
    have hcard := indexClassFinset_card_le p n k hk
    have hcardR : ((indexClassFinset p n k).card : ℝ)
        ≤ (2 : ℝ) ^ ((n + 1) ^ 4) * (p : ℝ) ^ ((n : ℝ) - (k : ℝ)) := by
      have h2 : ((indexClassFinset p n k).card : ℝ)
          ≤ ((2 ^ ((n + 1) ^ 4) * p ^ (n - k) : ℕ) : ℝ) := by exact_mod_cast hcard
      have h3 : ((2 ^ ((n + 1) ^ 4) * p ^ (n - k) : ℕ) : ℝ)
          = (2 : ℝ) ^ ((n + 1) ^ 4) * (p : ℝ) ^ ((n : ℝ) - (k : ℝ)) := by
        rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_pow, ← Real.rpow_natCast (p : ℝ) (n - k),
          Nat.cast_sub hk]
        norm_num
      rw [h3] at h2
      exact h2
    refine le_trans hcardR ?_
    have h1 : (0 : ℝ) ≤ (p : ℝ) ^ ((n : ℝ) - (k : ℝ)) := by positivity
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) h1
  · rw [if_neg ha]
    have h1 := hC₀ p k hk a ha
    have hrp : (p : ℝ) ^ ((n : ℝ) - (k : ℝ) - 1/2)
        = (p : ℝ) ^ ((n : ℝ) - (k : ℝ)) * (p : ℝ) ^ (-(1/2) : ℝ) := by
      rw [← Real.rpow_add hp0]
      congr 1
    rw [hrp] at h1
    have h2 : (0 : ℝ) ≤ (p : ℝ) ^ (-(1/2) : ℝ) := by positivity
    have h3 : C₀ ≤ max C₀ ((2 : ℝ) ^ ((n + 1) ^ 4)) := le_max_left _ _
    calc ‖indexFourierCoeff p n k a‖
        ≤ C₀ * ((p : ℝ) ^ ((n : ℝ) - (k : ℝ)) * (p : ℝ) ^ (-(1/2) : ℝ)) := h1
      _ = (C₀ * (p : ℝ) ^ ((n : ℝ) - (k : ℝ))) * (p : ℝ) ^ (-(1/2) : ℝ) := by ring
      _ ≤ (max C₀ ((2 : ℝ) ^ ((n + 1) ^ 4)) * (p : ℝ) ^ ((n : ℝ) - (k : ℝ)))
            * (p : ℝ) ^ (-(1/2) : ℝ) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right h3 (by positivity)) h2

/-- **The reindexing identity**: the sum over frequency tuples of a function of
the CRT combination equals the sum over the frequencies modulo `C`. -/
theorem multiPrime_sum_reindex {s : Finset ℕ} (hprime : ∀ p ∈ s, Nat.Prime p)
    [inst : ∀ p : {p // p ∈ s}, NeZero (p : ℕ)] [hC : NeZero (∏ p ∈ s, p)]
    (n : ℕ) (F : (Fin n → ZMod (∏ p ∈ s, p)) → ℝ) :
    (∑ a : (∀ p : {p // p ∈ s}, Fin n → ZMod (p : ℕ)),
        F (fun j => ∑ p : {p // p ∈ s}, (((-(a p j)).val : ℕ) : ZMod (∏ p ∈ s, p)) *
          (((∏ p ∈ s, p) / (p : ℕ) : ℕ) : ZMod (∏ p ∈ s, p))))
      = ∑ c : Fin n → ZMod (∏ p ∈ s, p), F c := by
  classical
  have hbij := Commons.NumberTheory.Nat.crt_combination_bijective_pi s
    (fun p hp => (hprime p hp).pos)
    (fun p hp p' hp' hne => (Nat.coprime_primes (hprime p hp) (hprime p' hp')).mpr hne) n
  have hneg : Function.Bijective
      (fun a : (∀ p : {p // p ∈ s}, Fin n → ZMod (p : ℕ)) => fun p => -(a p)) :=
    Function.Involutive.bijective (fun a => by funext p i; simp)
  have hcomp := hbij.comp hneg
  exact Fintype.sum_bijective _ hcomp _ _ (fun a => rfl)

/-- **The box character-sum bound in the frequency-tuple form**: the joint box
character sum is bounded by the product of the composite frequency weights at
the CRT combination of the (negated) frequencies. -/
lemma boxCharSum_bound {s : Finset ℕ} (hprime : ∀ p ∈ s, Nat.Prime p)
    [inst : ∀ p : {p // p ∈ s}, NeZero (p : ℕ)] [hC : NeZero (∏ p ∈ s, p)]
    (n H : ℕ) (a : ∀ p : {p // p ∈ s}, Fin n → ZMod (p : ℕ)) :
    ‖∑ f : ↥(Box n H), ∏ p : {p // p ∈ s}, ZMod.stdAddChar
        (-(∑ j, a p j * (boxResidue n H (p : ℕ) f) j))‖
      ≤ ∏ i : Fin n, freqWeightZ (∏ p ∈ s, p) H
          (((∑ p : {p // p ∈ s}, ((-(a p i)).val * ((∏ p ∈ s, p) / (p : ℕ)) : ℕ)) :
            ZMod (∏ p ∈ s, p))) := by
  classical
  have hsum : (∑ f : ↥(Box n H), ∏ p : {p // p ∈ s}, ZMod.stdAddChar
        (-(∑ j, a p j * (boxResidue n H (p : ℕ) f) j)))
      = ∑ v : BddVec n H, ∏ p : {p // p ∈ s}, ∏ j : Fin n,
          ZMod.stdAddChar (((v j : ℤ) : ZMod (p : ℕ)) * (-(a p j))) := by
    refine Fintype.sum_bijective (fun f : ↥(Box n H) => boxEquivBddVec n H f)
      (boxEquivBddVec n H).bijective
      (fun f : ↥(Box n H) => ∏ p : {p // p ∈ s}, ZMod.stdAddChar
        (-(∑ j, a p j * (boxResidue n H (p : ℕ) f) j)))
      (fun v : BddVec n H => ∏ p : {p // p ∈ s}, ∏ j : Fin n,
        ZMod.stdAddChar (((v j : ℤ) : ZMod (p : ℕ)) * (-(a p j)))) ?_
    intro f
    refine Finset.prod_congr rfl (fun p _ => ?_)
    have hcoeff : ∀ j : Fin n, boxResidue n H (p : ℕ) f j
        = ((((boxEquivBddVec n H) f) j : ℤ) : ZMod (p : ℕ)) := fun j => rfl
    have h1 : -(∑ j, a p j * (boxResidue n H (p : ℕ) f) j)
        = ∑ j, (boxResidue n H (p : ℕ) f) j * (-(a p j)) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      ring
    have h2 : ZMod.stdAddChar (-(∑ j, a p j * (boxResidue n H (p : ℕ) f) j))
        = ∏ j : Fin n, ZMod.stdAddChar
            ((boxResidue n H (p : ℕ) f) j * (-(a p j))) := by
      rw [h1]
      exact Commons.NumberTheory.ZMod.AddChar.map_sum_eq_prod ZMod.stdAddChar Finset.univ
        (fun j : Fin n => (boxResidue n H (p : ℕ) f) j * (-(a p j)))
    rw [h2]
    refine Finset.prod_congr rfl (fun j _ => ?_)
    rw [hcoeff j]
  rw [hsum]
  have h := norm_sum_joint_box_char_le s (fun p hp => (hprime p hp).pos)
    ((∏ p ∈ s, p)) rfl n H (fun p j => -(a p j))
  refine le_trans h ?_
  refine Finset.prod_le_prod (fun i _ => freqWeightZ_nonneg _ H _) (fun i _ => ?_)
  rw [Nat.cast_sum]

/-- The product of the vanishing-gain factors equals `(mof C c)^{-1/2}`. -/
lemma prod_qvan_eq_mof_rpow (C n : ℕ) (c : Fin n → ZMod C) :
    (∏ p ∈ C.primeFactors, (if Qvan C n p c then (1 : ℝ) else (p : ℝ) ^ (-(1/2) : ℝ)))
      = ((mof C n c : ℝ)) ^ (-(1/2) : ℝ) := by
  have h1 : (∏ p ∈ C.primeFactors, (if Qvan C n p c then (1 : ℝ) else (p : ℝ) ^ (-(1/2) : ℝ)))
      = ∏ p ∈ C.primeFactors.filter (fun p => ¬ Qvan C n p c), (p : ℝ) ^ (-(1/2) : ℝ) := by
    rw [Finset.prod_filter]
    refine Finset.prod_congr rfl (fun p hp => ?_)
    by_cases h : Qvan C n p c <;> simp [h]
  rw [h1, mof, Nat.cast_prod]
  exact Real.finsetProd_rpow _ _ (fun p hp => by positivity) (-(1/2 : ℝ))

/-- The pointwise coefficient bound for a family of primes. -/
lemma prod_coeff_bound (n : ℕ) (K : ℝ) (hK : 0 ≤ K)
    (hKb : ∀ (p : ℕ) [Fact (Nat.Prime p)] (k : ℕ), k ≤ n → ∀ a : Fin n → ZMod p,
      ‖indexFourierCoeff p n k a‖ ≤ K * (p : ℝ) ^ ((n : ℝ) - (k : ℝ)) *
        (if a = 0 then 1 else (p : ℝ) ^ (-(1/2) : ℝ)))
    {s : Finset ℕ} [inst : ∀ p : {p // p ∈ s}, Fact (Nat.Prime (p : ℕ))]
    [instn : ∀ p : {p // p ∈ s}, NeZero (p : ℕ)]
    (k : {p // p ∈ s} → ℕ) (hk : ∀ p, k p ≤ n)
    (a : ∀ p : {p // p ∈ s}, Fin n → ZMod (p : ℕ)) :
    (∏ p : {p // p ∈ s}, ‖indexFourierCoeff (p : ℕ) n (k p) (a p)‖)
      ≤ K ^ (Fintype.card {p // p ∈ s})
          * (∏ p : {p // p ∈ s}, (p : ℝ) ^ ((n : ℝ) - (k p : ℝ)))
          * (∏ p : {p // p ∈ s}, if a p = 0 then (1 : ℝ) else (p : ℝ) ^ (-(1/2) : ℝ)) := by
  refine le_trans (Finset.prod_le_prod (fun p _ => norm_nonneg _)
    (fun p _ => hKb (p : ℕ) (k p) (hk p) (a p))) (le_of_eq ?_)
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]


/-! ## θ-generic forms -/

/-- The pointwise coefficient bound coming from `MIndexBound` together with the
crude cardinality bound for the zero frequency. -/
theorem indexFourierCoeff_le_saving (n : ℕ) (θ : ℝ) (hM : MIndexBoundSaving n θ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (p : ℕ) [Fact (Nat.Prime p)] (k : ℕ), k ≤ n →
      ∀ a : Fin n → ZMod p,
        ‖indexFourierCoeff p n k a‖ ≤ K * (p : ℝ) ^ ((n : ℝ) - (k : ℝ)) *
          (if a = 0 then 1 else (p : ℝ) ^ ((-θ) : ℝ)) := by
  obtain ⟨C₀, hC₀0, hC₀⟩ := hM
  refine ⟨max C₀ ((2 : ℝ) ^ ((n + 1) ^ 4)), le_max_of_le_left hC₀0, ?_⟩
  intro p _ k hk a
  haveI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by
    have h : 1 ≤ p := (Fact.out : Nat.Prime p).one_lt.le
    exact_mod_cast h
  have hp0 : (0 : ℝ) < (p : ℝ) := lt_of_lt_of_le one_pos hp1
  have hpk : ((p ^ (n - k) : ℕ) : ℝ) = (p : ℝ) ^ ((n : ℝ) - (k : ℝ)) := by
    rw [Nat.cast_pow, ← Real.rpow_natCast (p : ℝ) (n - k), Nat.cast_sub hk]
  by_cases ha : a = 0
  · subst ha
    have hnorm : ‖indexFourierCoeff p n k 0‖ = ((indexClassFinset p n k).card : ℝ) := by
      rw [indexFourierCoeff]
      simp
    rw [hnorm, if_pos rfl, mul_one]
    have hcard := indexClassFinset_card_le p n k hk
    have hcardR : ((indexClassFinset p n k).card : ℝ)
        ≤ (2 : ℝ) ^ ((n + 1) ^ 4) * (p : ℝ) ^ ((n : ℝ) - (k : ℝ)) := by
      have h2 : ((indexClassFinset p n k).card : ℝ)
          ≤ ((2 ^ ((n + 1) ^ 4) * p ^ (n - k) : ℕ) : ℝ) := by exact_mod_cast hcard
      have h3 : ((2 ^ ((n + 1) ^ 4) * p ^ (n - k) : ℕ) : ℝ)
          = (2 : ℝ) ^ ((n + 1) ^ 4) * (p : ℝ) ^ ((n : ℝ) - (k : ℝ)) := by
        rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_pow, ← Real.rpow_natCast (p : ℝ) (n - k),
          Nat.cast_sub hk]
        norm_num
      rw [h3] at h2
      exact h2
    refine le_trans hcardR ?_
    have h1 : (0 : ℝ) ≤ (p : ℝ) ^ ((n : ℝ) - (k : ℝ)) := by positivity
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) h1
  · rw [if_neg ha]
    have h1 := hC₀ p k hk a ha
    have hrp : (p : ℝ) ^ ((n : ℝ) - (k : ℝ) - θ)
        = (p : ℝ) ^ ((n : ℝ) - (k : ℝ)) * (p : ℝ) ^ ((-θ) : ℝ) := by
      rw [← Real.rpow_add hp0]
      congr 1
    rw [hrp] at h1
    have h2 : (0 : ℝ) ≤ (p : ℝ) ^ ((-θ) : ℝ) := by positivity
    have h3 : C₀ ≤ max C₀ ((2 : ℝ) ^ ((n + 1) ^ 4)) := le_max_left _ _
    calc ‖indexFourierCoeff p n k a‖
        ≤ C₀ * ((p : ℝ) ^ ((n : ℝ) - (k : ℝ)) * (p : ℝ) ^ ((-θ) : ℝ)) := h1
      _ = (C₀ * (p : ℝ) ^ ((n : ℝ) - (k : ℝ))) * (p : ℝ) ^ ((-θ) : ℝ) := by ring
      _ ≤ (max C₀ ((2 : ℝ) ^ ((n + 1) ^ 4)) * (p : ℝ) ^ ((n : ℝ) - (k : ℝ)))
            * (p : ℝ) ^ ((-θ) : ℝ) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right h3 (by positivity)) h2


/-- The product of the vanishing-gain factors equals `(mof C c)^{-θ}`. -/
lemma prod_qvan_eq_mof_rpow_saving (C n : ℕ) (θ : ℝ) (c : Fin n → ZMod C) :
    (∏ p ∈ C.primeFactors, (if Qvan C n p c then (1 : ℝ) else (p : ℝ) ^ ((-θ) : ℝ)))
      = ((mof C n c : ℝ)) ^ ((-θ) : ℝ) := by
  have h1 : (∏ p ∈ C.primeFactors, (if Qvan C n p c then (1 : ℝ) else (p : ℝ) ^ ((-θ) : ℝ)))
      = ∏ p ∈ C.primeFactors.filter (fun p => ¬ Qvan C n p c), (p : ℝ) ^ ((-θ) : ℝ) := by
    rw [Finset.prod_filter]
    refine Finset.prod_congr rfl (fun p hp => ?_)
    by_cases h : Qvan C n p c <;> simp [h]
  rw [h1, mof, Nat.cast_prod]
  exact Real.finsetProd_rpow _ _ (fun p hp => by positivity) (-(θ : ℝ))


/-- The pointwise coefficient bound for a family of primes. -/
lemma prod_coeff_bound_saving (n : ℕ) (θ : ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hKb : ∀ (p : ℕ) [Fact (Nat.Prime p)] (k : ℕ), k ≤ n → ∀ a : Fin n → ZMod p,
      ‖indexFourierCoeff p n k a‖ ≤ K * (p : ℝ) ^ ((n : ℝ) - (k : ℝ)) *
        (if a = 0 then 1 else (p : ℝ) ^ ((-θ) : ℝ)))
    {s : Finset ℕ} [inst : ∀ p : {p // p ∈ s}, Fact (Nat.Prime (p : ℕ))]
    [instn : ∀ p : {p // p ∈ s}, NeZero (p : ℕ)]
    (k : {p // p ∈ s} → ℕ) (hk : ∀ p, k p ≤ n)
    (a : ∀ p : {p // p ∈ s}, Fin n → ZMod (p : ℕ)) :
    (∏ p : {p // p ∈ s}, ‖indexFourierCoeff (p : ℕ) n (k p) (a p)‖)
      ≤ K ^ (Fintype.card {p // p ∈ s})
          * (∏ p : {p // p ∈ s}, (p : ℝ) ^ ((n : ℝ) - (k p : ℝ)))
          * (∏ p : {p // p ∈ s}, if a p = 0 then (1 : ℝ) else (p : ℝ) ^ ((-θ) : ℝ)) := by
  refine le_trans (Finset.prod_le_prod (fun p _ => norm_nonneg _)
    (fun p _ => hKb (p : ℕ) (k p) (hk p) (a p))) (le_of_eq ?_)
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]


end
end Submission.Vdw
