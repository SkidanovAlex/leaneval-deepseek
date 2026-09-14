import Mathlib
import Submission.Vdw.MultiPrimeAssembly
import Submission.Vdw.MultiPrimeWeightBound
import Submission.Commons.Data.Nat.squarefree_prod_primes
import Submission.Commons.Data.ZMod.crt_combination_reduction
import Submission.Commons.NumberTheory.Nat.crt_combination_bijective_pi

open Finset
open scoped BigOperators

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-!
# The multi-prime count assembly (paper §4, Corollary `Dequi2`)

This module closes the multi-prime §4 chapter: it assembles the exact Fourier
expansion `MultiPrimeFourier.multiPrime_fourier_expansion`, the per-prime
coefficient bound `MultiPrimeAssembly.prod_coeff_bound`, the joint box
character-sum bound `MultiPrimeAssembly.boxCharSum_bound`, the pattern
decomposition `MultiPrimeSigma.pattern_sum_le` and the divisor-sum estimate
`MultiPrimeWeightBound.divisor_sum_le` into the multi-prime counting bound
`#{f ∈ Box n H : index (f mod p) ≥ k p  ∀ p ∈ s} ≤ K^{#s}·H^n / ∏_{p ∈ s} p^{k p}`
in the regime `∏_{p∈s} p ≤ H^{1+1/(2n)}`, together with the derived
per-discriminant index-condition input `PerIrrBound` used by Case I and
Case III.

Axioms: propext / Classical.choice / Quot.sound only.
-/

namespace Submission.Vdw
noncomputable section

/-- The CRT combination of a family of frequencies `a`: the frequency modulo
`C = ∏ p ∈ s, p` whose reduction mod each `p ∈ s` is `a p`. -/
def crtFreq {s : Finset ℕ} (n : ℕ) (a : ∀ p : {p // p ∈ s}, Fin n → ZMod (p : ℕ)) :
    Fin n → ZMod (∏ p ∈ s, p) :=
  fun i => ∑ p : {p // p ∈ s}, (((a p i).val : ℕ) : ZMod (∏ p ∈ s, p)) *
      (((∏ p ∈ s, p) / (p : ℕ) : ℕ) : ZMod (∏ p ∈ s, p))

/-- The pointwise CRT correspondence: the `p₀`-th coordinate of the CRT
combination vanishes mod `p₀` iff the `p₀`-frequency vanishes.  (Direct
instance of the commons lemma `crt_combination_reduction`.) -/
lemma crtFreq_val_mod_eq_zero_iff {s : Finset ℕ} (hprime : ∀ p ∈ s, Nat.Prime p)
    (n : ℕ) (a : ∀ p : {p // p ∈ s}, Fin n → ZMod (p : ℕ)) (p₀ : {p // p ∈ s})
    (i : Fin n) :
    (crtFreq n a i).val % (p₀ : ℕ) = 0 ↔ a p₀ i = 0 :=
  Commons.Data.ZMod.crt_combination_reduction s hprime n (p₀ : ℕ) p₀.2 a i

/-- **(A) The product-form correspondence**: the vanishing of the whole
`p₀`-frequency is equivalent to the `Qvan` condition for the CRT combination. -/
lemma qvan_crtFreq {s : Finset ℕ} (hprime : ∀ p ∈ s, Nat.Prime p)
    (n : ℕ) (a : ∀ p : {p // p ∈ s}, Fin n → ZMod (p : ℕ)) (p₀ : {p // p ∈ s}) :
    Qvan (∏ p ∈ s, p) n (p₀ : ℕ) (crtFreq n a) ↔ a p₀ = 0 := by
  rw [Qvan]
  constructor
  · intro h
    funext i
    exact (crtFreq_val_mod_eq_zero_iff hprime n a p₀ i).mp (h i)
  · intro h i
    rw [crtFreq_val_mod_eq_zero_iff hprime n a p₀ i, h]
    rfl

/-- The product of the subtype elements equals the Finset product, cast to a
commutative semiring. -/
lemma prod_subtype_natCast {R : Type*} [CommSemiring R] (s : Finset ℕ) :
    (∏ i : {p // p ∈ s}, ((i : ℕ) : R)) = (((∏ p ∈ s, p : ℕ)) : R) := by
  have h1 : (∏ i : {p // p ∈ s}, ((i : ℕ) : R)) = ∏ p ∈ s, ((p : ℕ) : R) :=
    Finset.prod_attach s (fun p => ((p : ℕ) : R))
  rw [h1, Nat.cast_prod]

/-- The norm of the inverse Fourier normalisation. -/
lemma norm_inv_prod_pow (s : Finset ℕ) [NeZero (∏ p ∈ s, p)] (n : ℕ) :
    ‖(∏ i : {p // p ∈ s}, (((i : ℕ) : ℂ)) ^ n)⁻¹‖
      = ((∏ p ∈ s, p : ℕ) : ℝ) ^ (-(n : ℝ)) := by
  have hCpos : (0 : ℝ) < ((∏ p ∈ s, p : ℕ) : ℝ) := by
    rw [Nat.cast_pos]
    exact Nat.pos_of_ne_zero (NeZero.ne _)
  have hprod : (∏ i : {p // p ∈ s}, (((i : ℕ) : ℂ)) ^ n)
      = (((∏ p ∈ s, p : ℕ)) : ℂ) ^ n := by
    rw [Finset.prod_pow, prod_subtype_natCast]
  rw [hprod, norm_inv, norm_pow, Complex.norm_natCast,
    ← Real.rpow_natCast ((∏ p ∈ s, p : ℕ) : ℝ) n, ← Real.rpow_neg hCpos.le]

/-- **The norm bound of the multi-prime Fourier expansion**: the joint
index-condition count is at most the Fourier normalisation times the sum over
frequency tuples of the product of the per-prime coefficient norms and the box
character-sum norm. -/
theorem multiPrime_norm_le {s : Finset ℕ} (hprime : ∀ p ∈ s, Nat.Prime p)
    [inst : ∀ p : {p // p ∈ s}, Fact (Nat.Prime (p : ℕ))]
    [instn : ∀ p : {p // p ∈ s}, NeZero (p : ℕ)] [hCN : NeZero (∏ p ∈ s, p)]
    (n H : ℕ) (k : {p // p ∈ s} → ℕ) :
    ((Nat.card {f : ↥(Box n H) // ∀ i : {p // p ∈ s},
        indexClass (F := ZMod (i : ℕ)) n (k i) (boxResidue n H (i : ℕ) f)} : ℕ) : ℝ)
      ≤ ((∏ p ∈ s, p : ℕ) : ℝ) ^ (-(n : ℝ)) *
        ∑ a : (∀ i : {p // p ∈ s}, Fin n → ZMod (i : ℕ)),
          (∏ i : {p // p ∈ s}, ‖indexFourierCoeff (i : ℕ) n (k i) (a i)‖) *
          ‖∑ f : ↥(Box n H), ∏ i : {p // p ∈ s},
              ZMod.stdAddChar (-(∑ j, a i j * (boxResidue n H (i : ℕ) f) j))‖ := by
  classical
  have hfe := multiPrime_fourier_expansion (fun p : {p // p ∈ s} => (p : ℕ)) n H k
  have hfe' : (((Nat.card {f : ↥(Box n H) // ∀ i : {p // p ∈ s},
        indexClass (F := ZMod (i : ℕ)) n (k i) (boxResidue n H (i : ℕ) f)} : ℕ)) : ℂ)
      = (∏ i : {p // p ∈ s}, (((i : ℕ) : ℂ)) ^ n)⁻¹ *
        ∑ a : (∀ i : {p // p ∈ s}, Fin n → ZMod (i : ℕ)),
          (∏ i : {p // p ∈ s}, indexFourierCoeff (i : ℕ) n (k i) (a i)) *
          (∑ f : ↥(Box n H), ∏ i : {p // p ∈ s},
              ZMod.stdAddChar (-(∑ j, a i j * (boxResidue n H (i : ℕ) f) j))) := by
    simpa only [indexFourierCoeff, Finset.prod_attach] using hfe
  have hnn : (0 : ℝ) ≤ ((∏ p ∈ s, p : ℕ) : ℝ) ^ (-(n : ℝ)) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  calc ((Nat.card {f : ↥(Box n H) // ∀ i : {p // p ∈ s},
        indexClass (F := ZMod (i : ℕ)) n (k i) (boxResidue n H (i : ℕ) f)} : ℕ) : ℝ)
      = ‖(((Nat.card {f : ↥(Box n H) // ∀ i : {p // p ∈ s},
        indexClass (F := ZMod (i : ℕ)) n (k i) (boxResidue n H (i : ℕ) f)} : ℕ)) : ℂ)‖ := by
        rw [Complex.norm_natCast]
    _ = ‖(∏ i : {p // p ∈ s}, (((i : ℕ) : ℂ)) ^ n)⁻¹ *
        ∑ a : (∀ i : {p // p ∈ s}, Fin n → ZMod (i : ℕ)),
          (∏ i : {p // p ∈ s}, indexFourierCoeff (i : ℕ) n (k i) (a i)) *
          (∑ f : ↥(Box n H), ∏ i : {p // p ∈ s},
              ZMod.stdAddChar (-(∑ j, a i j * (boxResidue n H (i : ℕ) f) j)))‖ := by
        rw [hfe']
    _ ≤ ‖(∏ i : {p // p ∈ s}, (((i : ℕ) : ℂ)) ^ n)⁻¹‖ *
        ‖∑ a : (∀ i : {p // p ∈ s}, Fin n → ZMod (i : ℕ)),
          (∏ i : {p // p ∈ s}, indexFourierCoeff (i : ℕ) n (k i) (a i)) *
          (∑ f : ↥(Box n H), ∏ i : {p // p ∈ s},
              ZMod.stdAddChar (-(∑ j, a i j * (boxResidue n H (i : ℕ) f) j)))‖ :=
        norm_mul_le _ _
    _ = ((∏ p ∈ s, p : ℕ) : ℝ) ^ (-(n : ℝ)) *
        ‖∑ a : (∀ i : {p // p ∈ s}, Fin n → ZMod (i : ℕ)),
          (∏ i : {p // p ∈ s}, indexFourierCoeff (i : ℕ) n (k i) (a i)) *
          (∑ f : ↥(Box n H), ∏ i : {p // p ∈ s},
              ZMod.stdAddChar (-(∑ j, a i j * (boxResidue n H (i : ℕ) f) j)))‖ := by
        rw [norm_inv_prod_pow]
    _ ≤ ((∏ p ∈ s, p : ℕ) : ℝ) ^ (-(n : ℝ)) *
        ∑ a : (∀ i : {p // p ∈ s}, Fin n → ZMod (i : ℕ)),
          (∏ i : {p // p ∈ s}, ‖indexFourierCoeff (i : ℕ) n (k i) (a i)‖) *
          ‖∑ f : ↥(Box n H), ∏ i : {p // p ∈ s},
              ZMod.stdAddChar (-(∑ j, a i j * (boxResidue n H (i : ℕ) f) j))‖ := by
        refine mul_le_mul_of_nonneg_left ?_ hnn
        refine le_trans (norm_sum_le _ _) ?_
        refine Finset.sum_le_sum (fun a _ => ?_)
        refine le_trans (norm_mul_le _ _) ?_
        rw [norm_prod]

/-- The CRT combination in the "cast of the sum" form used by the box
character-sum bound. -/
lemma crtFreq_eq_cast_sum {s : Finset ℕ} (n : ℕ)
    (b : ∀ p : {p // p ∈ s}, Fin n → ZMod (p : ℕ)) :
    crtFreq n b = fun i => ((∑ p : {p // p ∈ s},
      (b p i).val * ((∏ p ∈ s, p) / (p : ℕ)) : ℕ) : ZMod (∏ p ∈ s, p)) := by
  funext i
  rw [crtFreq]
  rw [Nat.cast_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [Nat.cast_mul]

/-- The negation of a family of frequencies. -/
def aNeg {s : Finset ℕ} {n : ℕ} (a : ∀ p : {p // p ∈ s}, Fin n → ZMod (p : ℕ)) :
    ∀ p : {p // p ∈ s}, Fin n → ZMod (p : ℕ) := fun p => -(a p)

/-- The product over `s` of the "vanishing" indicators equals
`(mof C c)^{-1/2}`, where `c` is the CRT combination of `-a`. -/
lemma prod_indicator_eq_mof {s : Finset ℕ} (hprime : ∀ p ∈ s, Nat.Prime p)
    (n : ℕ) (a : ∀ p : {p // p ∈ s}, Fin n → ZMod (p : ℕ)) :
    (∏ i : {p // p ∈ s}, (if a i = 0 then (1 : ℝ)
        else (((i : ℕ) : ℝ)) ^ (-(1/2) : ℝ)))
      = ((mof (∏ p ∈ s, p) n (crtFreq n (aNeg a)) : ℝ)) ^ (-(1/2) : ℝ) := by
  classical
  have hq : ∀ i : {p // p ∈ s},
      (Qvan (∏ p ∈ s, p) n (i : ℕ) (crtFreq n (aNeg a)) ↔ a i = 0) := by
    intro i
    have h := qvan_crtFreq hprime n (aNeg a) i
    rw [show (aNeg a) i = -(a i) from rfl, neg_eq_zero] at h
    exact h
  have h1 : (∏ i : {p // p ∈ s}, (if a i = 0 then (1 : ℝ)
        else (((i : ℕ) : ℝ)) ^ (-(1/2) : ℝ)))
      = ∏ i : {p // p ∈ s}, (if Qvan (∏ p ∈ s, p) n (i : ℕ) (crtFreq n (aNeg a))
          then (1 : ℝ) else (((i : ℕ) : ℝ)) ^ (-(1/2) : ℝ)) :=
    Finset.prod_congr rfl (fun i _ => by
      by_cases h : a i = 0
      · rw [if_pos h, if_pos ((hq i).mpr h)]
      · rw [if_neg h, if_neg (fun hh => h ((hq i).mp hh))])
  rw [h1]
  have h2 : (∏ i : {p // p ∈ s}, (if Qvan (∏ p ∈ s, p) n (i : ℕ) (crtFreq n (aNeg a))
        then (1 : ℝ) else (((i : ℕ) : ℝ)) ^ (-(1/2) : ℝ)))
      = ∏ p ∈ s, (if Qvan (∏ p ∈ s, p) n p (crtFreq n (aNeg a))
          then (1 : ℝ) else ((p : ℕ) : ℝ) ^ (-(1/2) : ℝ)) :=
    Finset.prod_attach s (fun p => if Qvan (∏ p ∈ s, p) n p (crtFreq n (aNeg a))
      then (1 : ℝ) else ((p : ℕ) : ℝ) ^ (-(1/2) : ℝ))
  rw [h2]
  have h3 : (∏ p ∈ s, (if Qvan (∏ p ∈ s, p) n p (crtFreq n (aNeg a))
        then (1 : ℝ) else ((p : ℕ) : ℝ) ^ (-(1/2) : ℝ)))
      = ∏ p ∈ (∏ p ∈ s, p).primeFactors, (if Qvan (∏ p ∈ s, p) n p (crtFreq n (aNeg a))
          then (1 : ℝ) else ((p : ℕ) : ℝ) ^ (-(1/2) : ℝ)) := by
    show s.prod _ = (∏ p ∈ s, p).primeFactors.prod _
    rw [Nat.primeFactors_prod hprime]
  rw [h3]
  exact prod_qvan_eq_mof_rpow (∏ p ∈ s, p) n _

/-- The fiber-weight product equals `wvec`. -/
lemma prod_freqWeightZ_eq_wvec {s : Finset ℕ} [NeZero (∏ p ∈ s, p)]
    (hprime : ∀ p ∈ s, Nat.Prime p) (n H : ℕ)
    (c : Fin n → ZMod (∏ p ∈ s, p)) :
    (∏ i : Fin n, freqWeightZ (∏ p ∈ s, p) H (c i))
      = wvec (∏ p ∈ s, p) n H c := by
  have hC0 : 0 < ∏ p ∈ s, p := Nat.pos_of_ne_zero (NeZero.ne _)
  have hCsq : (∏ p ∈ s, p) = ∏ p ∈ (∏ p ∈ s, p).primeFactors, p :=
    (Nat.prod_primeFactors_of_squarefree (Commons.Data.Nat.squarefree_prod_primes hprime)).symm
  exact (wvec_eq_prod (∏ p ∈ s, p) n H c hC0 hCsq).symm

/-- The CRT combination of the negated frequencies, as an explicit pointwise
sum (the form in which it appears in `multiPrime_sum_reindex`). -/
lemma crtFreq_aNeg_eq {s : Finset ℕ} (n : ℕ)
    (a : ∀ p : {p // p ∈ s}, Fin n → ZMod (p : ℕ)) :
    crtFreq n (aNeg a) = fun j => ∑ p : {p // p ∈ s},
      ((((-(a p j)).val : ℕ)) : ZMod (∏ p ∈ s, p)) *
        (((∏ p ∈ s, p) / (p : ℕ) : ℕ) : ZMod (∏ p ∈ s, p)) := by
  unfold crtFreq
  rfl

lemma crtFreq_aNeg_apply {s : Finset ℕ} (n : ℕ)
    (a : ∀ p : {p // p ∈ s}, Fin n → ZMod (p : ℕ)) (i : Fin n) :
    crtFreq n (aNeg a) i = ((∑ p : {p // p ∈ s},
      ((-(a p i)).val * ((∏ p ∈ s, p) / (p : ℕ)) : ℕ)) : ZMod (∏ p ∈ s, p)) := by
  unfold crtFreq
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [show (aNeg a) p i = -(a p i) from rfl, Nat.cast_mul]

/-- **The frequency-sum estimate of the multi-prime §4 chapter.** -/
theorem multiPrime_freq_sum_le {s : Finset ℕ} (hprime : ∀ p ∈ s, Nat.Prime p)
    [inst : ∀ p : {p // p ∈ s}, Fact (Nat.Prime (p : ℕ))]
    [instn : ∀ p : {p // p ∈ s}, NeZero (p : ℕ)] [hCN : NeZero (∏ p ∈ s, p)]
    (n H : ℕ) (k : {p // p ∈ s} → ℕ) (hk : ∀ p, k p ≤ n) (C0 : ℝ) (hC0 : 0 ≤ C0)
    (hC0b : ∀ (p : ℕ) [Fact (Nat.Prime p)] (j : ℕ), j ≤ n → ∀ a : Fin n → ZMod p,
        ‖indexFourierCoeff p n j a‖ ≤ C0 * (p : ℝ) ^ ((n : ℝ) - (j : ℝ)) *
          (if a = 0 then 1 else (p : ℝ) ^ (-(1/2) : ℝ))) :
    (∑ a : (∀ i : {p // p ∈ s}, Fin n → ZMod (i : ℕ)),
        (∏ i : {p // p ∈ s}, ‖indexFourierCoeff (i : ℕ) n (k i) (a i)‖) *
        ‖∑ f : ↥(Box n H), ∏ i : {p // p ∈ s},
            ZMod.stdAddChar (-(∑ j, a i j * (boxResidue n H (i : ℕ) f) j))‖)
      ≤ (C0 ^ (Fintype.card {p // p ∈ s}) *
          (∏ i : {p // p ∈ s}, ((i : ℕ) : ℝ) ^ ((n : ℝ) - (k i : ℝ)))) *
        (∑ c : Fin n → ZMod (∏ p ∈ s, p),
          ((mof (∏ p ∈ s, p) n c : ℝ) ^ (-(1/2) : ℝ)) * wvec (∏ p ∈ s, p) n H c) := by
  classical
  set A : ℝ := C0 ^ (Fintype.card {p // p ∈ s}) *
    (∏ i : {p // p ∈ s}, ((i : ℕ) : ℝ) ^ ((n : ℝ) - (k i : ℝ))) with hA
  have hA0 : 0 ≤ A := by
    rw [hA]
    refine mul_nonneg (pow_nonneg hC0 _) ?_
    exact Finset.prod_nonneg (fun i _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hpt : ∀ a : (∀ i : {p // p ∈ s}, Fin n → ZMod (i : ℕ)),
      (∏ i : {p // p ∈ s}, ‖indexFourierCoeff (i : ℕ) n (k i) (a i)‖) *
      ‖∑ f : ↥(Box n H), ∏ i : {p // p ∈ s},
          ZMod.stdAddChar (-(∑ j, a i j * (boxResidue n H (i : ℕ) f) j))‖
      ≤ A * ((∏ i : {p // p ∈ s}, (if a i = 0 then (1 : ℝ)
          else (((i : ℕ) : ℝ)) ^ (-(1/2) : ℝ))) *
        (∏ j : Fin n, freqWeightZ (∏ p ∈ s, p) H (crtFreq n (aNeg a) j))) := by
    intro a
    have hcoeff := prod_coeff_bound n C0 hC0 (fun p _ j hj b => hC0b p j hj b)
      (s := s) k hk a
    have hbox := boxCharSum_bound hprime n H (fun p => a p)
    have hbox' : ‖∑ f : ↥(Box n H), ∏ i : {p // p ∈ s},
          ZMod.stdAddChar (-(∑ j, a i j * (boxResidue n H (i : ℕ) f) j))‖
        ≤ ∏ j : Fin n, freqWeightZ (∏ p ∈ s, p) H (crtFreq n (aNeg a) j) := by
      refine le_trans hbox ?_
      refine le_of_eq (Finset.prod_congr rfl (fun j _ => ?_))
      rw [crtFreq_aNeg_apply n a j]
    have hb0 : 0 ≤ A * ((∏ i : {p // p ∈ s}, (if a i = 0 then (1 : ℝ)
          else (((i : ℕ) : ℝ)) ^ (-(1/2) : ℝ))) *
        (∏ j : Fin n, freqWeightZ (∏ p ∈ s, p) H (crtFreq n (aNeg a) j))) := by
      refine mul_nonneg hA0 ?_
      refine mul_nonneg ?_ ?_
      · exact Finset.prod_nonneg (fun i _ => by
          by_cases h : a i = 0
          · rw [if_pos h]; norm_num
          · rw [if_neg h]; exact Real.rpow_nonneg (Nat.cast_nonneg _) _)
      · exact Finset.prod_nonneg (fun j _ => freqWeightZ_nonneg _ H _)
    have h1 : (∏ i : {p // p ∈ s}, ‖indexFourierCoeff (i : ℕ) n (k i) (a i)‖)
        ≤ A * (∏ i : {p // p ∈ s}, (if a i = 0 then (1 : ℝ)
            else (((i : ℕ) : ℝ)) ^ (-(1/2) : ℝ))) := by
      rw [hA]
      refine le_trans hcoeff (le_of_eq ?_)
      ring
    calc (∏ i : {p // p ∈ s}, ‖indexFourierCoeff (i : ℕ) n (k i) (a i)‖) *
          ‖∑ f : ↥(Box n H), ∏ i : {p // p ∈ s},
              ZMod.stdAddChar (-(∑ j, a i j * (boxResidue n H (i : ℕ) f) j))‖
        ≤ (A * (∏ i : {p // p ∈ s}, (if a i = 0 then (1 : ℝ)
            else (((i : ℕ) : ℝ)) ^ (-(1/2) : ℝ)))) *
          (∏ j : Fin n, freqWeightZ (∏ p ∈ s, p) H (crtFreq n (aNeg a) j)) :=
          mul_le_mul h1 hbox' (norm_nonneg _) (by
            refine mul_nonneg hA0 ?_
            exact Finset.prod_nonneg (fun i _ => by
              by_cases h : a i = 0
              · rw [if_pos h]; norm_num
              · rw [if_neg h]; exact Real.rpow_nonneg (Nat.cast_nonneg _) _))
        _ = A * ((∏ i : {p // p ∈ s}, (if a i = 0 then (1 : ℝ)
            else (((i : ℕ) : ℝ)) ^ (-(1/2) : ℝ))) *
          (∏ j : Fin n, freqWeightZ (∏ p ∈ s, p) H (crtFreq n (aNeg a) j))) := by ring
  have hsum : (∑ a : (∀ i : {p // p ∈ s}, Fin n → ZMod (i : ℕ)),
        (∏ i : {p // p ∈ s}, ‖indexFourierCoeff (i : ℕ) n (k i) (a i)‖) *
        ‖∑ f : ↥(Box n H), ∏ i : {p // p ∈ s},
            ZMod.stdAddChar (-(∑ j, a i j * (boxResidue n H (i : ℕ) f) j))‖)
      ≤ A * ∑ a : (∀ i : {p // p ∈ s}, Fin n → ZMod (i : ℕ)),
        ((∏ i : {p // p ∈ s}, (if a i = 0 then (1 : ℝ)
            else (((i : ℕ) : ℝ)) ^ (-(1/2) : ℝ))) *
          (∏ j : Fin n, freqWeightZ (∏ p ∈ s, p) H (crtFreq n (aNeg a) j))) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun a _ => hpt a)
  have key : (∑ a : (∀ i : {p // p ∈ s}, Fin n → ZMod (i : ℕ)),
        ((∏ i : {p // p ∈ s}, (if a i = 0 then (1 : ℝ)
            else (((i : ℕ) : ℝ)) ^ (-(1/2) : ℝ))) *
          (∏ j : Fin n, freqWeightZ (∏ p ∈ s, p) H (crtFreq n (aNeg a) j))))
      = ∑ c : Fin n → ZMod (∏ p ∈ s, p),
          ((mof (∏ p ∈ s, p) n c : ℝ) ^ (-(1/2) : ℝ)) * wvec (∏ p ∈ s, p) n H c := by
    rw [← multiPrime_sum_reindex (s := s) hprime n
      (fun c => ((mof (∏ p ∈ s, p) n c : ℝ) ^ (-(1/2) : ℝ)) * wvec (∏ p ∈ s, p) n H c)]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [prod_indicator_eq_mof hprime n a,
      prod_freqWeightZ_eq_wvec hprime n H (crtFreq n (aNeg a)), crtFreq_aNeg_eq]
  calc (∑ a : (∀ i : {p // p ∈ s}, Fin n → ZMod (i : ℕ)),
        (∏ i : {p // p ∈ s}, ‖indexFourierCoeff (i : ℕ) n (k i) (a i)‖) *
        ‖∑ f : ↥(Box n H), ∏ i : {p // p ∈ s},
            ZMod.stdAddChar (-(∑ j, a i j * (boxResidue n H (i : ℕ) f) j))‖)
      ≤ A * ∑ a : (∀ i : {p // p ∈ s}, Fin n → ZMod (i : ℕ)),
        ((∏ i : {p // p ∈ s}, (if a i = 0 then (1 : ℝ)
            else (((i : ℕ) : ℝ)) ^ (-(1/2) : ℝ))) *
          (∏ j : Fin n, freqWeightZ (∏ p ∈ s, p) H (crtFreq n (aNeg a) j))) := hsum
    _ = A * ∑ c : Fin n → ZMod (∏ p ∈ s, p),
          ((mof (∏ p ∈ s, p) n c : ℝ) ^ (-(1/2) : ℝ)) * wvec (∏ p ∈ s, p) n H c := by
        rw [key]
    _ = (C0 ^ (Fintype.card {p // p ∈ s}) *
          (∏ i : {p // p ∈ s}, ((i : ℕ) : ℝ) ^ ((n : ℝ) - (k i : ℝ)))) *
        (∑ c : Fin n → ZMod (∏ p ∈ s, p),
          ((mof (∏ p ∈ s, p) n c : ℝ) ^ (-(1/2) : ℝ)) * wvec (∏ p ∈ s, p) n H c) := by
        rw [hA]

/-- The predicate `Qvan` holds at the zero frequency. -/
lemma qvan_zero (C n p : ℕ) : Qvan C n p (0 : Fin n → ZMod C) := by
  intro i
  simp

/-- `mof` at the zero frequency is `1`. -/
lemma mof_zero (C n : ℕ) : mof C n (0 : Fin n → ZMod C) = 1 := by
  rw [mof, Finset.filter_eq_empty_iff.mpr (fun x _ => by simp [Qvan]), Finset.prod_empty]

/-- The composite weight constant of `divisor_sum_le`. -/
def sigConst (n : ℕ) : ℕ := 2 * (n * 10 ^ (n - 1) * 3 ^ n + 10 ^ n)

/-- `wvec` at the zero frequency. -/
lemma wvec_zero {s : Finset ℕ} [NeZero (∏ p ∈ s, p)] (hprime : ∀ p ∈ s, Nat.Prime p)
    (n H : ℕ) :
    wvec (∏ p ∈ s, p) n H (0 : Fin n → ZMod (∏ p ∈ s, p))
      = (((2 * H + 1 : ℕ)) : ℝ) ^ n := by
  rw [← prod_freqWeightZ_eq_wvec hprime n H (0 : Fin n → ZMod (∏ p ∈ s, p))]
  have h1 : ∀ i : Fin n, freqWeightZ (∏ p ∈ s, p) H
      ((0 : Fin n → ZMod (∏ p ∈ s, p)) i) = (((2 * H + 1 : ℕ)) : ℝ) := by
    intro i; simp [freqWeightZ]
  rw [Finset.prod_congr rfl (fun i _ => h1 i), Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

/-- The frequency sum of the multi-prime expansion, bounded by the divisor-sum
estimate. -/
lemma sum_mof_wvec_le {s : Finset ℕ} (hprime : ∀ p ∈ s, Nat.Prime p)
    [hCN : NeZero (∏ p ∈ s, p)] (n H : ℕ) (hn : 1 ≤ n) (hH : 1 ≤ H)
    (hC2 : 2 ≤ ∏ p ∈ s, p)
    (hCrad : ((∏ p ∈ s, p : ℕ) : ℝ) ≤ (H : ℝ) ^ (1 + 1 / (2 * (n : ℝ))))
    (hlog : (1 + Real.log ((∏ p ∈ s, p : ℕ) : ℝ)) ^ n ≤ (H : ℝ) ^ (1 / (4 * (n : ℝ))))
    (hlog2 : (1 + Real.log ((∏ p ∈ s, p : ℕ) : ℝ)) ^ n ≤ (H : ℝ) ^ (1 / 2 : ℝ)) :
    (∑ c : Fin n → ZMod (∏ p ∈ s, p),
        ((mof (∏ p ∈ s, p) n c : ℝ) ^ (-(1/2) : ℝ)) * wvec (∏ p ∈ s, p) n H c)
      ≤ (((2 * H + 1 : ℕ)) : ℝ) ^ n + (sigConst n : ℝ) ^ (s.card) * (H : ℝ) ^ n := by
  classical
  have hC0 : 0 < ∏ p ∈ s, p := Nat.pos_of_ne_zero (NeZero.ne _)
  have hCsq : (∏ p ∈ s, p) = ∏ p ∈ (∏ p ∈ s, p).primeFactors, p :=
    (Nat.prod_primeFactors_of_squarefree
      (Commons.Data.Nat.squarefree_prod_primes hprime)).symm
  have hds : (∑ c ∈ (Finset.univ : Finset (Fin n → ZMod (∏ p ∈ s, p))).erase 0,
        ((mof (∏ p ∈ s, p) n c : ℝ) ^ (-(1/2) : ℝ)) * wvec (∏ p ∈ s, p) n H c)
      ≤ (sigConst n : ℝ) ^ s.card * (H : ℝ) ^ n := by
    refine le_trans (pattern_sum_le (∏ p ∈ s, p) n H hC0 hCsq) ?_
    refine le_trans (divisor_sum_le n H (∏ p ∈ s, p) hn hC2 hH hCsq hCrad hlog hlog2) ?_
    rw [Nat.primeFactors_prod hprime]
    exact le_of_eq rfl
  have hF0 : ((mof (∏ p ∈ s, p) n (0 : Fin n → ZMod (∏ p ∈ s, p)) : ℝ) ^ (-(1/2) : ℝ))
      * wvec (∏ p ∈ s, p) n H (0 : Fin n → ZMod (∏ p ∈ s, p))
      = (((2 * H + 1 : ℕ)) : ℝ) ^ n := by
    rw [mof_zero, Nat.cast_one, Real.one_rpow, one_mul, wvec_zero hprime n H]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ
    (0 : Fin n → ZMod (∏ p ∈ s, p)))]
  exact add_le_add (le_of_eq hF0) hds

/-- `∏ᵢ i^{n - k_i} = C^n / D` and `C^{-n}·C^n/D = 1/D`. -/
lemma norm_mul_prod_eq_inv (s : Finset ℕ) (hprime : ∀ p ∈ s, Nat.Prime p) (n : ℕ)
    (k : {p // p ∈ s} → ℕ) :
    (((∏ p ∈ s, p : ℕ)) : ℝ) ^ (-(n : ℝ)) *
        (∏ i : {p // p ∈ s}, ((i : ℕ) : ℝ) ^ ((n : ℝ) - (k i : ℝ)))
      = 1 / (∏ i : {p // p ∈ s}, ((i : ℕ) : ℝ) ^ (k i)) := by
  have hp1 : ∀ i : {p // p ∈ s}, (0 : ℝ) < ((i : ℕ) : ℝ) := fun i =>
    lt_of_lt_of_le one_pos (by
      have := hprime (i : ℕ) i.2
      exact_mod_cast this.one_lt.le)
  have hCpos : (0 : ℝ) < (((∏ p ∈ s, p : ℕ)) : ℝ) := by
    rw [Nat.cast_pos]
    exact Nat.pos_of_ne_zero (Finset.prod_ne_zero_iff.mpr
      (fun p hp => (hprime p hp).ne_zero))
  have hDpos : (0 : ℝ) < ∏ i : {p // p ∈ s}, ((i : ℕ) : ℝ) ^ (k i) :=
    Finset.prod_pos (fun i _ => pow_pos (hp1 i) _)
  have h1 : ∀ i : {p // p ∈ s}, ((i : ℕ) : ℝ) ^ ((n : ℝ) - (k i : ℝ))
      = ((i : ℕ) : ℝ) ^ n / ((i : ℕ) : ℝ) ^ (k i) := by
    intro i
    rw [Real.rpow_sub (hp1 i), Real.rpow_natCast, Real.rpow_natCast]
  rw [Finset.prod_congr rfl (fun i _ => h1 i), Finset.prod_div_distrib]
  have h2 : (∏ i : {p // p ∈ s}, ((i : ℕ) : ℝ) ^ n) = (((∏ p ∈ s, p : ℕ)) : ℝ) ^ n := by
    rw [Finset.prod_pow, ← prod_subtype_natCast]
  rw [h2]
  have h3 : (((∏ p ∈ s, p : ℕ)) : ℝ) ^ (-(n : ℝ))
      = ((((∏ p ∈ s, p : ℕ)) : ℝ) ^ n)⁻¹ := by
    rw [Real.rpow_neg hCpos.le, Real.rpow_natCast]
  rw [h3]
  field_simp

/-- **The multi-prime counting bound** (paper §4, Corollary `Dequi2`, elementary
regime): there is `K` such that for every family `s` of primes, every `k` with
`k p ≤ n`, and every `H` in the regime `∏_{p∈s} p ≤ H^{1+1/(2n)}`,
`(1+log ∏_{p∈s} p)^n ≤ H^{1/(4n)}`, `(1+log ∏_{p∈s} p)^n ≤ √H`, the number of
box polynomials whose reductions have index at least `k p` modulo each `p ∈ s`
is at most `K^{#s}·H^n / ∏_{p∈s} p^{k p}`. -/
theorem multiPrime_count_le (n : ℕ) (hn : 3 ≤ n) (hM : MIndexBound n) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (s : Finset ℕ) (hprime : ∀ p ∈ s, Nat.Prime p)
      [inst : ∀ p : {p // p ∈ s}, Fact (Nat.Prime (p : ℕ))]
      [instn : ∀ p : {p // p ∈ s}, NeZero (p : ℕ)]
      (H : ℕ) (k : {p // p ∈ s} → ℕ) (hk : ∀ p, k p ≤ n),
      2 ≤ (∏ p ∈ s, p) → 1 ≤ H →
      (((∏ p ∈ s, p : ℕ)) : ℝ) ≤ (H : ℝ) ^ (1 + 1 / (2 * (n : ℝ))) →
      (1 + Real.log (((∏ p ∈ s, p : ℕ)) : ℝ)) ^ n ≤ (H : ℝ) ^ (1 / (4 * (n : ℝ))) →
      (1 + Real.log (((∏ p ∈ s, p : ℕ)) : ℝ)) ^ n ≤ (H : ℝ) ^ (1 / 2 : ℝ) →
      ((Nat.card {f : ↥(Box n H) // ∀ i : {p // p ∈ s},
          indexClass (F := ZMod (i : ℕ)) n (k i) (boxResidue n H (i : ℕ) f)} : ℕ) : ℝ)
        ≤ K ^ (Fintype.card {p // p ∈ s}) * (H : ℝ) ^ n /
            (∏ i : {p // p ∈ s}, (((i : ℕ)) : ℝ) ^ (k i)) := by
  classical
  obtain ⟨C0, hC00, hC0b⟩ := indexFourierCoeff_le n hM
  have hC0one : 1 ≤ max 1 (2 * C0 * ((3 : ℝ) ^ n + (sigConst n : ℝ))) := le_max_left _ _
  refine ⟨max 1 (2 * C0 * ((3 : ℝ) ^ n + (sigConst n : ℝ))), hC0one, ?_⟩
  intro s hprime inst instn H k hk hC2 hH1 hCrad hlog hlog2
  have hn1 : 1 ≤ n := by omega
  have hCN : NeZero (∏ p ∈ s, p) := ⟨by omega⟩
  haveI := hCN
  -- the two Fourier inputs
  have hnorm := multiPrime_norm_le hprime n H k
  have hfreq := multiPrime_freq_sum_le hprime n H k hk C0 hC00
    (fun p _ j hj a => hC0b p j hj a)
  have hsum := sum_mof_wvec_le hprime n H hn1 hH1 hC2 hCrad hlog hlog2
  -- the nonnegativity of the coefficient factor
  have hA0 : (0 : ℝ) ≤ C0 ^ (Fintype.card {p // p ∈ s}) *
      (∏ i : {p // p ∈ s}, ((i : ℕ) : ℝ) ^ ((n : ℝ) - (k i : ℝ))) :=
    mul_nonneg (pow_nonneg hC00 _)
      (Finset.prod_nonneg (fun i _ => Real.rpow_nonneg (Nat.cast_nonneg _) _))
  have hCn0 : (0 : ℝ) ≤ (((∏ p ∈ s, p : ℕ)) : ℝ) ^ (-(n : ℝ)) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  -- step 1: insert the frequency-sum estimate
  have step1 : ((Nat.card {f : ↥(Box n H) // ∀ i : {p // p ∈ s},
        indexClass (F := ZMod (i : ℕ)) n (k i) (boxResidue n H (i : ℕ) f)} : ℕ) : ℝ)
      ≤ (((∏ p ∈ s, p : ℕ)) : ℝ) ^ (-(n : ℝ)) *
        ((C0 ^ (Fintype.card {p // p ∈ s}) *
            (∏ i : {p // p ∈ s}, ((i : ℕ) : ℝ) ^ ((n : ℝ) - (k i : ℝ)))) *
          (∑ c : Fin n → ZMod (∏ p ∈ s, p),
            ((mof (∏ p ∈ s, p) n c : ℝ) ^ (-(1/2) : ℝ)) * wvec (∏ p ∈ s, p) n H c)) := by
    refine le_trans hnorm ?_
    refine le_trans (mul_le_mul_of_nonneg_left hfreq hCn0) ?_
    exact mul_le_mul_of_nonneg_left (le_of_eq rfl) hCn0
  -- step 2: apply the divisor-sum estimate
  have step2 : (((∏ p ∈ s, p : ℕ)) : ℝ) ^ (-(n : ℝ)) *
        ((C0 ^ (Fintype.card {p // p ∈ s}) *
            (∏ i : {p // p ∈ s}, ((i : ℕ) : ℝ) ^ ((n : ℝ) - (k i : ℝ)))) *
          (∑ c : Fin n → ZMod (∏ p ∈ s, p),
            ((mof (∏ p ∈ s, p) n c : ℝ) ^ (-(1/2) : ℝ)) * wvec (∏ p ∈ s, p) n H c))
      ≤ (((∏ p ∈ s, p : ℕ)) : ℝ) ^ (-(n : ℝ)) *
        ((C0 ^ (Fintype.card {p // p ∈ s}) *
            (∏ i : {p // p ∈ s}, ((i : ℕ) : ℝ) ^ ((n : ℝ) - (k i : ℝ)))) *
          ((((2 * H + 1 : ℕ)) : ℝ) ^ n + (sigConst n : ℝ) ^ (s.card) * (H : ℝ) ^ n)) := by
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum hA0) hCn0
  -- step 3: the coefficient/frequency factor is `C0^{#ι}·D^{-1}`
  have hkey : (((∏ p ∈ s, p : ℕ)) : ℝ) ^ (-(n : ℝ)) *
        (∏ i : {p // p ∈ s}, ((i : ℕ) : ℝ) ^ ((n : ℝ) - (k i : ℝ)))
      = 1 / (∏ i : {p // p ∈ s}, ((i : ℕ) : ℝ) ^ (k i)) :=
    norm_mul_prod_eq_inv s hprime n k
  -- step 4: `(2H+1)^n ≤ 3^n·H^n`
  have h3H : (((2 * H + 1 : ℕ)) : ℝ) ^ n ≤ (3 : ℝ) ^ n * (H : ℝ) ^ n := by
    have h1 : (((2 * H + 1 : ℕ)) : ℝ) ≤ 3 * (H : ℝ) := by
      have h2 : (((2 * H + 1 : ℕ)) : ℝ) = 2 * (H : ℝ) + 1 := by push_cast; ring
      have h3 : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH1
      rw [h2]; linarith
    have h4 : (0 : ℝ) ≤ (((2 * H + 1 : ℕ)) : ℝ) := by positivity
    calc (((2 * H + 1 : ℕ)) : ℝ) ^ n ≤ (3 * (H : ℝ)) ^ n := pow_le_pow_left₀ h4 h1 n
      _ = (3 : ℝ) ^ n * (H : ℝ) ^ n := mul_pow 3 (H : ℝ) n
  -- step 5: the cardinality bound `#s ≥ 1`
  have hcard1 : 1 ≤ Fintype.card {p // p ∈ s} := by
    have h1 : Fintype.card {p // p ∈ s} = s.card := by
      rw [← Finset.card_attach]; rfl
    rw [h1]
    refine Finset.card_pos.mpr ?_
    by_contra hcon
    rw [Finset.not_nonempty_iff_eq_empty] at hcon
    rw [hcon] at hC2
    simp at hC2
  -- step 6: the constant absorption
  have habs : C0 ^ (Fintype.card {p // p ∈ s}) *
        ((3 : ℝ) ^ n + (sigConst n : ℝ) ^ (s.card))
      ≤ (2 * C0 * ((3 : ℝ) ^ n + (sigConst n : ℝ))) ^ (Fintype.card {p // p ∈ s}) := by
    have hc1 : (1 : ℝ) ≤ (sigConst n : ℝ) := by
      have h2 : 1 ≤ sigConst n := by
        rw [sigConst]
        have : 1 ≤ 10 ^ n := Nat.one_le_pow n 10 (by norm_num)
        omega
      exact_mod_cast h2
    have hcard_eq : s.card = Fintype.card {p // p ∈ s} := by
      rw [← Finset.card_attach]; rfl
    have h3n1 : (1 : ℝ) ≤ (3 : ℝ) ^ n := one_le_pow₀ (by norm_num)
    have h3n0 : (0 : ℝ) ≤ (3 : ℝ) ^ n := le_trans zero_le_one h3n1
    have hsig0 : (0 : ℝ) ≤ (sigConst n : ℝ) := le_trans zero_le_one hc1
    have hbase1 : (1 : ℝ) ≤ (3 : ℝ) ^ n + 1 := by linarith
    have hbase2 : (1 : ℝ) ≤ (3 : ℝ) ^ n + (sigConst n : ℝ) := by linarith
    -- the key inequality
    have hkeyineq : (3 : ℝ) ^ n + (sigConst n : ℝ) ^ s.card
        ≤ 2 * ((3 : ℝ) ^ n + (sigConst n : ℝ)) ^ s.card := by
      have h1 : (3 : ℝ) ^ n ≤ ((3 : ℝ) ^ n + 1) ^ s.card := by
        calc (3 : ℝ) ^ n ≤ (3 : ℝ) ^ n + 1 := by linarith
          _ = ((3 : ℝ) ^ n + 1) ^ 1 := (pow_one _).symm
          _ ≤ ((3 : ℝ) ^ n + 1) ^ s.card :=
              pow_le_pow_right₀ hbase1 (by rw [hcard_eq]; exact hcard1)
      have h2 : (sigConst n : ℝ) ^ s.card ≤ ((3 : ℝ) ^ n + (sigConst n : ℝ)) ^ s.card :=
        pow_le_pow_left₀ hsig0 (by linarith) _
      have h3 : ((3 : ℝ) ^ n + 1) ^ s.card ≤ ((3 : ℝ) ^ n + (sigConst n : ℝ)) ^ s.card :=
        pow_le_pow_left₀ (by positivity) (by linarith) _
      linarith
    have h2pow : (2 : ℝ) ≤ (2 : ℝ) ^ Fintype.card {p // p ∈ s} := by
      calc (2 : ℝ) = (2 : ℝ) ^ 1 := (pow_one 2).symm
        _ ≤ (2 : ℝ) ^ Fintype.card {p // p ∈ s} :=
            pow_le_pow_right₀ (by norm_num) hcard1
    calc C0 ^ (Fintype.card {p // p ∈ s}) *
          ((3 : ℝ) ^ n + (sigConst n : ℝ) ^ (s.card))
        ≤ C0 ^ (Fintype.card {p // p ∈ s}) *
            (2 * ((3 : ℝ) ^ n + (sigConst n : ℝ)) ^ s.card) :=
          mul_le_mul_of_nonneg_left hkeyineq (pow_nonneg hC00 _)
      _ = 2 * (C0 ^ (Fintype.card {p // p ∈ s}) *
            ((3 : ℝ) ^ n + (sigConst n : ℝ)) ^ s.card) := by ring
      _ ≤ 2 ^ (Fintype.card {p // p ∈ s}) * (C0 ^ (Fintype.card {p // p ∈ s}) *
            ((3 : ℝ) ^ n + (sigConst n : ℝ)) ^ s.card) :=
          mul_le_mul_of_nonneg_right h2pow (by positivity)
      _ = (2 * C0 * ((3 : ℝ) ^ n + (sigConst n : ℝ))) ^ (Fintype.card {p // p ∈ s}) := by
          rw [hcard_eq, mul_pow, mul_pow]
          ring
  -- assembling
  have hfin : ((Nat.card {f : ↥(Box n H) // ∀ i : {p // p ∈ s},
        indexClass (F := ZMod (i : ℕ)) n (k i) (boxResidue n H (i : ℕ) f)} : ℕ) : ℝ)
      ≤ (max 1 (2 * C0 * ((3 : ℝ) ^ n + (sigConst n : ℝ))) ^ (Fintype.card {p // p ∈ s})
          * (H : ℝ) ^ n) / (∏ i : {p // p ∈ s}, ((i : ℕ) : ℝ) ^ (k i)) := by
    have hDpos : (0 : ℝ) < ∏ i : {p // p ∈ s}, ((i : ℕ) : ℝ) ^ (k i) :=
      Finset.prod_pos (fun i _ => pow_pos (by
        have h := hprime (i : ℕ) i.2
        exact_mod_cast (lt_of_lt_of_le one_pos h.one_lt.le)) _)
    have hDinv : (0 : ℝ) ≤ 1 / (∏ i : {p // p ∈ s}, ((i : ℕ) : ℝ) ^ (k i)) :=
      div_nonneg zero_le_one hDpos.le
    have hSig1 : (1 : ℝ) ≤ (sigConst n : ℝ) := by
      have h2 : 1 ≤ sigConst n := by
        rw [sigConst]
        have : 1 ≤ 10 ^ n := Nat.one_le_pow n 10 (by norm_num)
        omega
      exact_mod_cast h2
    have hSig0 : (0 : ℝ) ≤ (sigConst n : ℝ) := le_trans zero_le_one hSig1
    have hK0nn : (0 : ℝ) ≤ 2 * C0 * ((3 : ℝ) ^ n + (sigConst n : ℝ)) := by
      have : (0 : ℝ) ≤ (3 : ℝ) ^ n + (sigConst n : ℝ) := by positivity
      positivity
    have hKpow : (2 * C0 * ((3 : ℝ) ^ n + (sigConst n : ℝ))) ^ (Fintype.card {p // p ∈ s})
        ≤ (max 1 (2 * C0 * ((3 : ℝ) ^ n + (sigConst n : ℝ)))) ^
            (Fintype.card {p // p ∈ s}) :=
      pow_le_pow_left₀ hK0nn (le_max_right _ _) _
    have hHn0 : (0 : ℝ) ≤ (H : ℝ) ^ n := by positivity
    have hZH : ((((2 * H + 1 : ℕ)) : ℝ) ^ n + (sigConst n : ℝ) ^ (s.card) * (H : ℝ) ^ n)
        ≤ ((3 : ℝ) ^ n + (sigConst n : ℝ) ^ (s.card)) * (H : ℝ) ^ n := by
      have := h3H
      nlinarith [this, hHn0, pow_nonneg hSig0 (s.card)]
    have hKH : C0 ^ (Fintype.card {p // p ∈ s}) *
          ((3 : ℝ) ^ n + (sigConst n : ℝ) ^ (s.card)) * (H : ℝ) ^ n
        ≤ (max 1 (2 * C0 * ((3 : ℝ) ^ n + (sigConst n : ℝ)))) ^
            (Fintype.card {p // p ∈ s}) * (H : ℝ) ^ n := by
      have hle : C0 ^ (Fintype.card {p // p ∈ s}) *
            ((3 : ℝ) ^ n + (sigConst n : ℝ) ^ (s.card))
          ≤ (max 1 (2 * C0 * ((3 : ℝ) ^ n + (sigConst n : ℝ)))) ^
              (Fintype.card {p // p ∈ s}) := le_trans habs hKpow
      exact mul_le_mul_of_nonneg_right hle hHn0
    calc ((Nat.card {f : ↥(Box n H) // ∀ i : {p // p ∈ s},
          indexClass (F := ZMod (i : ℕ)) n (k i) (boxResidue n H (i : ℕ) f)} : ℕ) : ℝ)
        ≤ (((∏ p ∈ s, p : ℕ)) : ℝ) ^ (-(n : ℝ)) *
            ((C0 ^ (Fintype.card {p // p ∈ s}) *
                (∏ i : {p // p ∈ s}, ((i : ℕ) : ℝ) ^ ((n : ℝ) - (k i : ℝ)))) *
              ((((2 * H + 1 : ℕ)) : ℝ) ^ n + (sigConst n : ℝ) ^ (s.card) * (H : ℝ) ^ n)) :=
            le_trans step1 step2
      _ ≤ (((∏ p ∈ s, p : ℕ)) : ℝ) ^ (-(n : ℝ)) *
            ((C0 ^ (Fintype.card {p // p ∈ s}) *
                (∏ i : {p // p ∈ s}, ((i : ℕ) : ℝ) ^ ((n : ℝ) - (k i : ℝ)))) *
              (((3 : ℝ) ^ n + (sigConst n : ℝ) ^ (s.card)) * (H : ℝ) ^ n)) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hZH hA0) hCn0
      _ = (1 / (∏ i : {p // p ∈ s}, ((i : ℕ) : ℝ) ^ (k i))) *
            (C0 ^ (Fintype.card {p // p ∈ s}) *
              (((3 : ℝ) ^ n + (sigConst n : ℝ) ^ (s.card)) * (H : ℝ) ^ n)) := by
          rw [← hkey]; ring
      _ ≤ (1 / (∏ i : {p // p ∈ s}, ((i : ℕ) : ℝ) ^ (k i))) *
            ((max 1 (2 * C0 * ((3 : ℝ) ^ n + (sigConst n : ℝ)))) ^
              (Fintype.card {p // p ∈ s}) * (H : ℝ) ^ n) := by
          refine mul_le_mul_of_nonneg_left ?_ hDinv
          calc C0 ^ (Fintype.card {p // p ∈ s}) *
                (((3 : ℝ) ^ n + (sigConst n : ℝ) ^ (s.card)) * (H : ℝ) ^ n)
              = (C0 ^ (Fintype.card {p // p ∈ s}) *
                  ((3 : ℝ) ^ n + (sigConst n : ℝ) ^ (s.card))) * (H : ℝ) ^ n := by ring
            _ ≤ (max 1 (2 * C0 * ((3 : ℝ) ^ n + (sigConst n : ℝ)))) ^
                  (Fintype.card {p // p ∈ s}) * (H : ℝ) ^ n := hKH
      _ = (max 1 (2 * C0 * ((3 : ℝ) ^ n + (sigConst n : ℝ))) ^
              (Fintype.card {p // p ∈ s}) * (H : ℝ) ^ n) /
            (∏ i : {p // p ∈ s}, ((i : ℕ) : ℝ) ^ (k i)) := by ring
  exact hfin

/-! ## θ,δ-generic forms -/

/-- The product over `s` of the "vanishing" indicators equals
`(mof C c)^{-1/2}`, where `c` is the CRT combination of `-a`. -/
lemma prod_indicator_eq_mof_theta {s : Finset ℕ} (hprime : ∀ p ∈ s, Nat.Prime p)
    (n : ℕ) (θ : ℝ) (a : ∀ p : {p // p ∈ s}, Fin n → ZMod (p : ℕ)) :
    (∏ i : {p // p ∈ s}, (if a i = 0 then (1 : ℝ)
        else (((i : ℕ) : ℝ)) ^ (-θ)))
      = ((mof (∏ p ∈ s, p) n (crtFreq n (aNeg a)) : ℝ)) ^ (-θ) := by
  classical
  have hq : ∀ i : {p // p ∈ s},
      (Qvan (∏ p ∈ s, p) n (i : ℕ) (crtFreq n (aNeg a)) ↔ a i = 0) := by
    intro i
    have h := qvan_crtFreq hprime n (aNeg a) i
    rw [show (aNeg a) i = -(a i) from rfl, neg_eq_zero] at h
    exact h
  have h1 : (∏ i : {p // p ∈ s}, (if a i = 0 then (1 : ℝ)
        else (((i : ℕ) : ℝ)) ^ (-θ)))
      = ∏ i : {p // p ∈ s}, (if Qvan (∏ p ∈ s, p) n (i : ℕ) (crtFreq n (aNeg a))
          then (1 : ℝ) else (((i : ℕ) : ℝ)) ^ (-θ)) :=
    Finset.prod_congr rfl (fun i _ => by
      by_cases h : a i = 0
      · rw [if_pos h, if_pos ((hq i).mpr h)]
      · rw [if_neg h, if_neg (fun hh => h ((hq i).mp hh))])
  rw [h1]
  have h2 : (∏ i : {p // p ∈ s}, (if Qvan (∏ p ∈ s, p) n (i : ℕ) (crtFreq n (aNeg a))
        then (1 : ℝ) else (((i : ℕ) : ℝ)) ^ (-θ)))
      = ∏ p ∈ s, (if Qvan (∏ p ∈ s, p) n p (crtFreq n (aNeg a))
          then (1 : ℝ) else ((p : ℕ) : ℝ) ^ (-θ)) :=
    Finset.prod_attach s (fun p => if Qvan (∏ p ∈ s, p) n p (crtFreq n (aNeg a))
      then (1 : ℝ) else ((p : ℕ) : ℝ) ^ (-θ))
  rw [h2]
  have h3 : (∏ p ∈ s, (if Qvan (∏ p ∈ s, p) n p (crtFreq n (aNeg a))
        then (1 : ℝ) else ((p : ℕ) : ℝ) ^ (-θ)))
      = ∏ p ∈ (∏ p ∈ s, p).primeFactors, (if Qvan (∏ p ∈ s, p) n p (crtFreq n (aNeg a))
          then (1 : ℝ) else ((p : ℕ) : ℝ) ^ (-θ)) := by
    show s.prod _ = (∏ p ∈ s, p).primeFactors.prod _
    rw [Nat.primeFactors_prod hprime]
  rw [h3]
  exact prod_qvan_eq_mof_rpow_saving (∏ p ∈ s, p) n θ _


theorem multiPrime_freq_sum_le_theta {s : Finset ℕ} (hprime : ∀ p ∈ s, Nat.Prime p)
    [inst : ∀ p : {p // p ∈ s}, Fact (Nat.Prime (p : ℕ))]
    [instn : ∀ p : {p // p ∈ s}, NeZero (p : ℕ)] [hCN : NeZero (∏ p ∈ s, p)]
    (n H : ℕ) (θ : ℝ) (k : {p // p ∈ s} → ℕ) (hk : ∀ p, k p ≤ n) (C0 : ℝ) (hC0 : 0 ≤ C0)
    (hC0b : ∀ (p : ℕ) [Fact (Nat.Prime p)] (j : ℕ), j ≤ n → ∀ a : Fin n → ZMod p,
        ‖indexFourierCoeff p n j a‖ ≤ C0 * (p : ℝ) ^ ((n : ℝ) - (j : ℝ)) *
          (if a = 0 then 1 else (p : ℝ) ^ (-θ))) :
    (∑ a : (∀ i : {p // p ∈ s}, Fin n → ZMod (i : ℕ)),
        (∏ i : {p // p ∈ s}, ‖indexFourierCoeff (i : ℕ) n (k i) (a i)‖) *
        ‖∑ f : ↥(Box n H), ∏ i : {p // p ∈ s},
            ZMod.stdAddChar (-(∑ j, a i j * (boxResidue n H (i : ℕ) f) j))‖)
      ≤ (C0 ^ (Fintype.card {p // p ∈ s}) *
          (∏ i : {p // p ∈ s}, ((i : ℕ) : ℝ) ^ ((n : ℝ) - (k i : ℝ)))) *
        (∑ c : Fin n → ZMod (∏ p ∈ s, p),
          ((mof (∏ p ∈ s, p) n c : ℝ) ^ (-θ)) * wvec (∏ p ∈ s, p) n H c) := by
  classical
  set A : ℝ := C0 ^ (Fintype.card {p // p ∈ s}) *
    (∏ i : {p // p ∈ s}, ((i : ℕ) : ℝ) ^ ((n : ℝ) - (k i : ℝ))) with hA
  have hA0 : 0 ≤ A := by
    rw [hA]
    refine mul_nonneg (pow_nonneg hC0 _) ?_
    exact Finset.prod_nonneg (fun i _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hpt : ∀ a : (∀ i : {p // p ∈ s}, Fin n → ZMod (i : ℕ)),
      (∏ i : {p // p ∈ s}, ‖indexFourierCoeff (i : ℕ) n (k i) (a i)‖) *
      ‖∑ f : ↥(Box n H), ∏ i : {p // p ∈ s},
          ZMod.stdAddChar (-(∑ j, a i j * (boxResidue n H (i : ℕ) f) j))‖
      ≤ A * ((∏ i : {p // p ∈ s}, (if a i = 0 then (1 : ℝ)
          else (((i : ℕ) : ℝ)) ^ (-θ))) *
        (∏ j : Fin n, freqWeightZ (∏ p ∈ s, p) H (crtFreq n (aNeg a) j))) := by
    intro a
    have hcoeff := prod_coeff_bound_saving n θ C0 hC0 (fun p _ j hj b => hC0b p j hj b)
      (s := s) k hk a
    have hbox := boxCharSum_bound hprime n H (fun p => a p)
    have hbox' : ‖∑ f : ↥(Box n H), ∏ i : {p // p ∈ s},
          ZMod.stdAddChar (-(∑ j, a i j * (boxResidue n H (i : ℕ) f) j))‖
        ≤ ∏ j : Fin n, freqWeightZ (∏ p ∈ s, p) H (crtFreq n (aNeg a) j) := by
      refine le_trans hbox ?_
      refine le_of_eq (Finset.prod_congr rfl (fun j _ => ?_))
      rw [crtFreq_aNeg_apply n a j]
    have hb0 : 0 ≤ A * ((∏ i : {p // p ∈ s}, (if a i = 0 then (1 : ℝ)
          else (((i : ℕ) : ℝ)) ^ (-θ))) *
        (∏ j : Fin n, freqWeightZ (∏ p ∈ s, p) H (crtFreq n (aNeg a) j))) := by
      refine mul_nonneg hA0 ?_
      refine mul_nonneg ?_ ?_
      · exact Finset.prod_nonneg (fun i _ => by
          by_cases h : a i = 0
          · rw [if_pos h]; norm_num
          · rw [if_neg h]; exact Real.rpow_nonneg (Nat.cast_nonneg _) _)
      · exact Finset.prod_nonneg (fun j _ => freqWeightZ_nonneg _ H _)
    have h1 : (∏ i : {p // p ∈ s}, ‖indexFourierCoeff (i : ℕ) n (k i) (a i)‖)
        ≤ A * (∏ i : {p // p ∈ s}, (if a i = 0 then (1 : ℝ)
            else (((i : ℕ) : ℝ)) ^ (-θ))) := by
      rw [hA]
      refine le_trans hcoeff (le_of_eq ?_)
      ring
    calc (∏ i : {p // p ∈ s}, ‖indexFourierCoeff (i : ℕ) n (k i) (a i)‖) *
          ‖∑ f : ↥(Box n H), ∏ i : {p // p ∈ s},
              ZMod.stdAddChar (-(∑ j, a i j * (boxResidue n H (i : ℕ) f) j))‖
        ≤ (A * (∏ i : {p // p ∈ s}, (if a i = 0 then (1 : ℝ)
            else (((i : ℕ) : ℝ)) ^ (-θ)))) *
          (∏ j : Fin n, freqWeightZ (∏ p ∈ s, p) H (crtFreq n (aNeg a) j)) :=
          mul_le_mul h1 hbox' (norm_nonneg _) (by
            refine mul_nonneg hA0 ?_
            exact Finset.prod_nonneg (fun i _ => by
              by_cases h : a i = 0
              · rw [if_pos h]; norm_num
              · rw [if_neg h]; exact Real.rpow_nonneg (Nat.cast_nonneg _) _))
        _ = A * ((∏ i : {p // p ∈ s}, (if a i = 0 then (1 : ℝ)
            else (((i : ℕ) : ℝ)) ^ (-θ))) *
          (∏ j : Fin n, freqWeightZ (∏ p ∈ s, p) H (crtFreq n (aNeg a) j))) := by ring
  have hsum : (∑ a : (∀ i : {p // p ∈ s}, Fin n → ZMod (i : ℕ)),
        (∏ i : {p // p ∈ s}, ‖indexFourierCoeff (i : ℕ) n (k i) (a i)‖) *
        ‖∑ f : ↥(Box n H), ∏ i : {p // p ∈ s},
            ZMod.stdAddChar (-(∑ j, a i j * (boxResidue n H (i : ℕ) f) j))‖)
      ≤ A * ∑ a : (∀ i : {p // p ∈ s}, Fin n → ZMod (i : ℕ)),
        ((∏ i : {p // p ∈ s}, (if a i = 0 then (1 : ℝ)
            else (((i : ℕ) : ℝ)) ^ (-θ))) *
          (∏ j : Fin n, freqWeightZ (∏ p ∈ s, p) H (crtFreq n (aNeg a) j))) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun a _ => hpt a)
  have key : (∑ a : (∀ i : {p // p ∈ s}, Fin n → ZMod (i : ℕ)),
        ((∏ i : {p // p ∈ s}, (if a i = 0 then (1 : ℝ)
            else (((i : ℕ) : ℝ)) ^ (-θ))) *
          (∏ j : Fin n, freqWeightZ (∏ p ∈ s, p) H (crtFreq n (aNeg a) j))))
      = ∑ c : Fin n → ZMod (∏ p ∈ s, p),
          ((mof (∏ p ∈ s, p) n c : ℝ) ^ (-θ)) * wvec (∏ p ∈ s, p) n H c := by
    rw [← multiPrime_sum_reindex (s := s) hprime n
      (fun c => ((mof (∏ p ∈ s, p) n c : ℝ) ^ (-θ)) * wvec (∏ p ∈ s, p) n H c)]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [prod_indicator_eq_mof_theta hprime n θ a,
      prod_freqWeightZ_eq_wvec hprime n H (crtFreq n (aNeg a)), crtFreq_aNeg_eq]
  calc (∑ a : (∀ i : {p // p ∈ s}, Fin n → ZMod (i : ℕ)),
        (∏ i : {p // p ∈ s}, ‖indexFourierCoeff (i : ℕ) n (k i) (a i)‖) *
        ‖∑ f : ↥(Box n H), ∏ i : {p // p ∈ s},
            ZMod.stdAddChar (-(∑ j, a i j * (boxResidue n H (i : ℕ) f) j))‖)
      ≤ A * ∑ a : (∀ i : {p // p ∈ s}, Fin n → ZMod (i : ℕ)),
        ((∏ i : {p // p ∈ s}, (if a i = 0 then (1 : ℝ)
            else (((i : ℕ) : ℝ)) ^ (-θ))) *
          (∏ j : Fin n, freqWeightZ (∏ p ∈ s, p) H (crtFreq n (aNeg a) j))) := hsum
    _ = A * ∑ c : Fin n → ZMod (∏ p ∈ s, p),
          ((mof (∏ p ∈ s, p) n c : ℝ) ^ (-θ)) * wvec (∏ p ∈ s, p) n H c := by
        rw [key]
    _ = (C0 ^ (Fintype.card {p // p ∈ s}) *
          (∏ i : {p // p ∈ s}, ((i : ℕ) : ℝ) ^ ((n : ℝ) - (k i : ℝ)))) *
        (∑ c : Fin n → ZMod (∏ p ∈ s, p),
          ((mof (∏ p ∈ s, p) n c : ℝ) ^ (-θ)) * wvec (∏ p ∈ s, p) n H c) := by
        rw [hA]


lemma sum_mof_wvec_le_theta {s : Finset ℕ} (hprime : ∀ p ∈ s, Nat.Prime p)
    [hCN : NeZero (∏ p ∈ s, p)] (n H : ℕ) (θ δ : ℝ) (hn : 1 ≤ n)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hθn : θ ≤ (n : ℝ)) (hH : 1 ≤ H)
    (hC2 : 2 ≤ ∏ p ∈ s, p)
    (hCrad : ((∏ p ∈ s, p : ℕ) : ℝ) ≤ (H : ℝ) ^ (1 + δ))
    (hlog : (1 + Real.log ((∏ p ∈ s, p : ℕ) : ℝ)) ^ n
      ≤ (H : ℝ) ^ Submission.Vdw.logGap n θ δ)
    (hlog2 : (1 + Real.log ((∏ p ∈ s, p : ℕ) : ℝ)) ^ n ≤ (H : ℝ) ^ θ) :
    (∑ c : Fin n → ZMod (∏ p ∈ s, p),
        ((mof (∏ p ∈ s, p) n c : ℝ) ^ (-θ)) * wvec (∏ p ∈ s, p) n H c)
      ≤ (((2 * H + 1 : ℕ)) : ℝ) ^ n + (sigConst n : ℝ) ^ (s.card) * (H : ℝ) ^ n := by
  classical
  have hC0 : 0 < ∏ p ∈ s, p := Nat.pos_of_ne_zero (NeZero.ne _)
  have hCsq : (∏ p ∈ s, p) = ∏ p ∈ (∏ p ∈ s, p).primeFactors, p :=
    (Nat.prod_primeFactors_of_squarefree
      (Commons.Data.Nat.squarefree_prod_primes hprime)).symm
  have hds : (∑ c ∈ (Finset.univ : Finset (Fin n → ZMod (∏ p ∈ s, p))).erase 0,
        ((mof (∏ p ∈ s, p) n c : ℝ) ^ (-θ)) * wvec (∏ p ∈ s, p) n H c)
      ≤ (sigConst n : ℝ) ^ s.card * (H : ℝ) ^ n := by
    refine le_trans (pattern_sum_le_saving (∏ p ∈ s, p) n H θ hC0 hCsq) ?_
    refine le_trans
      (divisor_sum_le_theta n H (∏ p ∈ s, p) θ δ hn hθ0 hθ1 hθn hC2 hH hCsq hCrad hlog hlog2) ?_
    rw [Nat.primeFactors_prod hprime]
    exact le_of_eq rfl
  have hF0 : ((mof (∏ p ∈ s, p) n (0 : Fin n → ZMod (∏ p ∈ s, p)) : ℝ) ^ (-θ))
      * wvec (∏ p ∈ s, p) n H (0 : Fin n → ZMod (∏ p ∈ s, p))
      = (((2 * H + 1 : ℕ)) : ℝ) ^ n := by
    rw [mof_zero, Nat.cast_one, Real.one_rpow, one_mul, wvec_zero hprime n H]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ
    (0 : Fin n → ZMod (∏ p ∈ s, p)))]
  exact add_le_add (le_of_eq hF0) hds


theorem multiPrime_count_le_theta (n : ℕ) (hn : 3 ≤ n) (θ δ : ℝ) (hθ0 : 0 ≤ θ)
    (hθ1 : θ ≤ 1) (hθn : θ ≤ (n : ℝ)) (hM : MIndexBoundSaving n θ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (s : Finset ℕ) (hprime : ∀ p ∈ s, Nat.Prime p)
      [inst : ∀ p : {p // p ∈ s}, Fact (Nat.Prime (p : ℕ))]
      [instn : ∀ p : {p // p ∈ s}, NeZero (p : ℕ)]
      (H : ℕ) (k : {p // p ∈ s} → ℕ) (hk : ∀ p, k p ≤ n),
      2 ≤ (∏ p ∈ s, p) → 1 ≤ H →
      (((∏ p ∈ s, p : ℕ)) : ℝ) ≤ (H : ℝ) ^ (1 + δ) →
      (1 + Real.log (((∏ p ∈ s, p : ℕ)) : ℝ)) ^ n ≤ (H : ℝ) ^ (logGap n θ δ) →
      (1 + Real.log (((∏ p ∈ s, p : ℕ)) : ℝ)) ^ n ≤ (H : ℝ) ^ θ →
      ((Nat.card {f : ↥(Box n H) // ∀ i : {p // p ∈ s},
          indexClass (F := ZMod (i : ℕ)) n (k i) (boxResidue n H (i : ℕ) f)} : ℕ) : ℝ)
        ≤ K ^ (Fintype.card {p // p ∈ s}) * (H : ℝ) ^ n /
            (∏ i : {p // p ∈ s}, (((i : ℕ)) : ℝ) ^ (k i)) := by
  classical
  obtain ⟨C0, hC00, hC0b⟩ := indexFourierCoeff_le_saving n θ hM
  have hC0one : 1 ≤ max 1 (2 * C0 * ((3 : ℝ) ^ n + (sigConst n : ℝ))) := le_max_left _ _
  refine ⟨max 1 (2 * C0 * ((3 : ℝ) ^ n + (sigConst n : ℝ))), hC0one, ?_⟩
  intro s hprime inst instn H k hk hC2 hH1 hCrad hlog hlog2
  have hn1 : 1 ≤ n := by omega
  have hCN : NeZero (∏ p ∈ s, p) := ⟨by omega⟩
  haveI := hCN
  -- the two Fourier inputs
  have hnorm := multiPrime_norm_le hprime n H k
  have hfreq := multiPrime_freq_sum_le_theta hprime n H θ k hk C0 hC00
    (fun p _ j hj a => hC0b p j hj a)
  have hsum := sum_mof_wvec_le_theta hprime n H θ δ hn1 hθ0 hθ1 hθn hH1 hC2 hCrad hlog hlog2
  -- the nonnegativity of the coefficient factor
  have hA0 : (0 : ℝ) ≤ C0 ^ (Fintype.card {p // p ∈ s}) *
      (∏ i : {p // p ∈ s}, ((i : ℕ) : ℝ) ^ ((n : ℝ) - (k i : ℝ))) :=
    mul_nonneg (pow_nonneg hC00 _)
      (Finset.prod_nonneg (fun i _ => Real.rpow_nonneg (Nat.cast_nonneg _) _))
  have hCn0 : (0 : ℝ) ≤ (((∏ p ∈ s, p : ℕ)) : ℝ) ^ (-(n : ℝ)) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  -- step 1: insert the frequency-sum estimate
  have step1 : ((Nat.card {f : ↥(Box n H) // ∀ i : {p // p ∈ s},
        indexClass (F := ZMod (i : ℕ)) n (k i) (boxResidue n H (i : ℕ) f)} : ℕ) : ℝ)
      ≤ (((∏ p ∈ s, p : ℕ)) : ℝ) ^ (-(n : ℝ)) *
        ((C0 ^ (Fintype.card {p // p ∈ s}) *
            (∏ i : {p // p ∈ s}, ((i : ℕ) : ℝ) ^ ((n : ℝ) - (k i : ℝ)))) *
          (∑ c : Fin n → ZMod (∏ p ∈ s, p),
            ((mof (∏ p ∈ s, p) n c : ℝ) ^ (-θ)) * wvec (∏ p ∈ s, p) n H c)) := by
    refine le_trans hnorm ?_
    refine le_trans (mul_le_mul_of_nonneg_left hfreq hCn0) ?_
    exact mul_le_mul_of_nonneg_left (le_of_eq rfl) hCn0
  -- step 2: apply the divisor-sum estimate
  have step2 : (((∏ p ∈ s, p : ℕ)) : ℝ) ^ (-(n : ℝ)) *
        ((C0 ^ (Fintype.card {p // p ∈ s}) *
            (∏ i : {p // p ∈ s}, ((i : ℕ) : ℝ) ^ ((n : ℝ) - (k i : ℝ)))) *
          (∑ c : Fin n → ZMod (∏ p ∈ s, p),
            ((mof (∏ p ∈ s, p) n c : ℝ) ^ (-θ)) * wvec (∏ p ∈ s, p) n H c))
      ≤ (((∏ p ∈ s, p : ℕ)) : ℝ) ^ (-(n : ℝ)) *
        ((C0 ^ (Fintype.card {p // p ∈ s}) *
            (∏ i : {p // p ∈ s}, ((i : ℕ) : ℝ) ^ ((n : ℝ) - (k i : ℝ)))) *
          ((((2 * H + 1 : ℕ)) : ℝ) ^ n + (sigConst n : ℝ) ^ (s.card) * (H : ℝ) ^ n)) := by
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum hA0) hCn0
  -- step 3: the coefficient/frequency factor is `C0^{#ι}·D^{-1}`
  have hkey : (((∏ p ∈ s, p : ℕ)) : ℝ) ^ (-(n : ℝ)) *
        (∏ i : {p // p ∈ s}, ((i : ℕ) : ℝ) ^ ((n : ℝ) - (k i : ℝ)))
      = 1 / (∏ i : {p // p ∈ s}, ((i : ℕ) : ℝ) ^ (k i)) :=
    norm_mul_prod_eq_inv s hprime n k
  -- step 4: `(2H+1)^n ≤ 3^n·H^n`
  have h3H : (((2 * H + 1 : ℕ)) : ℝ) ^ n ≤ (3 : ℝ) ^ n * (H : ℝ) ^ n := by
    have h1 : (((2 * H + 1 : ℕ)) : ℝ) ≤ 3 * (H : ℝ) := by
      have h2 : (((2 * H + 1 : ℕ)) : ℝ) = 2 * (H : ℝ) + 1 := by push_cast; ring
      have h3 : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH1
      rw [h2]; linarith
    have h4 : (0 : ℝ) ≤ (((2 * H + 1 : ℕ)) : ℝ) := by positivity
    calc (((2 * H + 1 : ℕ)) : ℝ) ^ n ≤ (3 * (H : ℝ)) ^ n := pow_le_pow_left₀ h4 h1 n
      _ = (3 : ℝ) ^ n * (H : ℝ) ^ n := mul_pow 3 (H : ℝ) n
  -- step 5: the cardinality bound `#s ≥ 1`
  have hcard1 : 1 ≤ Fintype.card {p // p ∈ s} := by
    have h1 : Fintype.card {p // p ∈ s} = s.card := by
      rw [← Finset.card_attach]; rfl
    rw [h1]
    refine Finset.card_pos.mpr ?_
    by_contra hcon
    rw [Finset.not_nonempty_iff_eq_empty] at hcon
    rw [hcon] at hC2
    simp at hC2
  -- step 6: the constant absorption
  have habs : C0 ^ (Fintype.card {p // p ∈ s}) *
        ((3 : ℝ) ^ n + (sigConst n : ℝ) ^ (s.card))
      ≤ (2 * C0 * ((3 : ℝ) ^ n + (sigConst n : ℝ))) ^ (Fintype.card {p // p ∈ s}) := by
    have hc1 : (1 : ℝ) ≤ (sigConst n : ℝ) := by
      have h2 : 1 ≤ sigConst n := by
        rw [sigConst]
        have : 1 ≤ 10 ^ n := Nat.one_le_pow n 10 (by norm_num)
        omega
      exact_mod_cast h2
    have hcard_eq : s.card = Fintype.card {p // p ∈ s} := by
      rw [← Finset.card_attach]; rfl
    have h3n1 : (1 : ℝ) ≤ (3 : ℝ) ^ n := one_le_pow₀ (by norm_num)
    have h3n0 : (0 : ℝ) ≤ (3 : ℝ) ^ n := le_trans zero_le_one h3n1
    have hsig0 : (0 : ℝ) ≤ (sigConst n : ℝ) := le_trans zero_le_one hc1
    have hbase1 : (1 : ℝ) ≤ (3 : ℝ) ^ n + 1 := by linarith
    have hbase2 : (1 : ℝ) ≤ (3 : ℝ) ^ n + (sigConst n : ℝ) := by linarith
    -- the key inequality
    have hkeyineq : (3 : ℝ) ^ n + (sigConst n : ℝ) ^ s.card
        ≤ 2 * ((3 : ℝ) ^ n + (sigConst n : ℝ)) ^ s.card := by
      have h1 : (3 : ℝ) ^ n ≤ ((3 : ℝ) ^ n + 1) ^ s.card := by
        calc (3 : ℝ) ^ n ≤ (3 : ℝ) ^ n + 1 := by linarith
          _ = ((3 : ℝ) ^ n + 1) ^ 1 := (pow_one _).symm
          _ ≤ ((3 : ℝ) ^ n + 1) ^ s.card :=
              pow_le_pow_right₀ hbase1 (by rw [hcard_eq]; exact hcard1)
      have h2 : (sigConst n : ℝ) ^ s.card ≤ ((3 : ℝ) ^ n + (sigConst n : ℝ)) ^ s.card :=
        pow_le_pow_left₀ hsig0 (by linarith) _
      have h3 : ((3 : ℝ) ^ n + 1) ^ s.card ≤ ((3 : ℝ) ^ n + (sigConst n : ℝ)) ^ s.card :=
        pow_le_pow_left₀ (by positivity) (by linarith) _
      linarith
    have h2pow : (2 : ℝ) ≤ (2 : ℝ) ^ Fintype.card {p // p ∈ s} := by
      calc (2 : ℝ) = (2 : ℝ) ^ 1 := (pow_one 2).symm
        _ ≤ (2 : ℝ) ^ Fintype.card {p // p ∈ s} :=
            pow_le_pow_right₀ (by norm_num) hcard1
    calc C0 ^ (Fintype.card {p // p ∈ s}) *
          ((3 : ℝ) ^ n + (sigConst n : ℝ) ^ (s.card))
        ≤ C0 ^ (Fintype.card {p // p ∈ s}) *
            (2 * ((3 : ℝ) ^ n + (sigConst n : ℝ)) ^ s.card) :=
          mul_le_mul_of_nonneg_left hkeyineq (pow_nonneg hC00 _)
      _ = 2 * (C0 ^ (Fintype.card {p // p ∈ s}) *
            ((3 : ℝ) ^ n + (sigConst n : ℝ)) ^ s.card) := by ring
      _ ≤ 2 ^ (Fintype.card {p // p ∈ s}) * (C0 ^ (Fintype.card {p // p ∈ s}) *
            ((3 : ℝ) ^ n + (sigConst n : ℝ)) ^ s.card) :=
          mul_le_mul_of_nonneg_right h2pow (by positivity)
      _ = (2 * C0 * ((3 : ℝ) ^ n + (sigConst n : ℝ))) ^ (Fintype.card {p // p ∈ s}) := by
          rw [hcard_eq, mul_pow, mul_pow]
          ring
  -- assembling
  have hfin : ((Nat.card {f : ↥(Box n H) // ∀ i : {p // p ∈ s},
        indexClass (F := ZMod (i : ℕ)) n (k i) (boxResidue n H (i : ℕ) f)} : ℕ) : ℝ)
      ≤ (max 1 (2 * C0 * ((3 : ℝ) ^ n + (sigConst n : ℝ))) ^ (Fintype.card {p // p ∈ s})
          * (H : ℝ) ^ n) / (∏ i : {p // p ∈ s}, ((i : ℕ) : ℝ) ^ (k i)) := by
    have hDpos : (0 : ℝ) < ∏ i : {p // p ∈ s}, ((i : ℕ) : ℝ) ^ (k i) :=
      Finset.prod_pos (fun i _ => pow_pos (by
        have h := hprime (i : ℕ) i.2
        exact_mod_cast (lt_of_lt_of_le one_pos h.one_lt.le)) _)
    have hDinv : (0 : ℝ) ≤ 1 / (∏ i : {p // p ∈ s}, ((i : ℕ) : ℝ) ^ (k i)) :=
      div_nonneg zero_le_one hDpos.le
    have hSig1 : (1 : ℝ) ≤ (sigConst n : ℝ) := by
      have h2 : 1 ≤ sigConst n := by
        rw [sigConst]
        have : 1 ≤ 10 ^ n := Nat.one_le_pow n 10 (by norm_num)
        omega
      exact_mod_cast h2
    have hSig0 : (0 : ℝ) ≤ (sigConst n : ℝ) := le_trans zero_le_one hSig1
    have hK0nn : (0 : ℝ) ≤ 2 * C0 * ((3 : ℝ) ^ n + (sigConst n : ℝ)) := by
      have : (0 : ℝ) ≤ (3 : ℝ) ^ n + (sigConst n : ℝ) := by positivity
      positivity
    have hKpow : (2 * C0 * ((3 : ℝ) ^ n + (sigConst n : ℝ))) ^ (Fintype.card {p // p ∈ s})
        ≤ (max 1 (2 * C0 * ((3 : ℝ) ^ n + (sigConst n : ℝ)))) ^
            (Fintype.card {p // p ∈ s}) :=
      pow_le_pow_left₀ hK0nn (le_max_right _ _) _
    have hHn0 : (0 : ℝ) ≤ (H : ℝ) ^ n := by positivity
    have hZH : ((((2 * H + 1 : ℕ)) : ℝ) ^ n + (sigConst n : ℝ) ^ (s.card) * (H : ℝ) ^ n)
        ≤ ((3 : ℝ) ^ n + (sigConst n : ℝ) ^ (s.card)) * (H : ℝ) ^ n := by
      have := h3H
      nlinarith [this, hHn0, pow_nonneg hSig0 (s.card)]
    have hKH : C0 ^ (Fintype.card {p // p ∈ s}) *
          ((3 : ℝ) ^ n + (sigConst n : ℝ) ^ (s.card)) * (H : ℝ) ^ n
        ≤ (max 1 (2 * C0 * ((3 : ℝ) ^ n + (sigConst n : ℝ)))) ^
            (Fintype.card {p // p ∈ s}) * (H : ℝ) ^ n := by
      have hle : C0 ^ (Fintype.card {p // p ∈ s}) *
            ((3 : ℝ) ^ n + (sigConst n : ℝ) ^ (s.card))
          ≤ (max 1 (2 * C0 * ((3 : ℝ) ^ n + (sigConst n : ℝ)))) ^
              (Fintype.card {p // p ∈ s}) := le_trans habs hKpow
      exact mul_le_mul_of_nonneg_right hle hHn0
    calc ((Nat.card {f : ↥(Box n H) // ∀ i : {p // p ∈ s},
          indexClass (F := ZMod (i : ℕ)) n (k i) (boxResidue n H (i : ℕ) f)} : ℕ) : ℝ)
        ≤ (((∏ p ∈ s, p : ℕ)) : ℝ) ^ (-(n : ℝ)) *
            ((C0 ^ (Fintype.card {p // p ∈ s}) *
                (∏ i : {p // p ∈ s}, ((i : ℕ) : ℝ) ^ ((n : ℝ) - (k i : ℝ)))) *
              ((((2 * H + 1 : ℕ)) : ℝ) ^ n + (sigConst n : ℝ) ^ (s.card) * (H : ℝ) ^ n)) :=
            le_trans step1 step2
      _ ≤ (((∏ p ∈ s, p : ℕ)) : ℝ) ^ (-(n : ℝ)) *
            ((C0 ^ (Fintype.card {p // p ∈ s}) *
                (∏ i : {p // p ∈ s}, ((i : ℕ) : ℝ) ^ ((n : ℝ) - (k i : ℝ)))) *
              (((3 : ℝ) ^ n + (sigConst n : ℝ) ^ (s.card)) * (H : ℝ) ^ n)) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hZH hA0) hCn0
      _ = (1 / (∏ i : {p // p ∈ s}, ((i : ℕ) : ℝ) ^ (k i))) *
            (C0 ^ (Fintype.card {p // p ∈ s}) *
              (((3 : ℝ) ^ n + (sigConst n : ℝ) ^ (s.card)) * (H : ℝ) ^ n)) := by
          rw [← hkey]; ring
      _ ≤ (1 / (∏ i : {p // p ∈ s}, ((i : ℕ) : ℝ) ^ (k i))) *
            ((max 1 (2 * C0 * ((3 : ℝ) ^ n + (sigConst n : ℝ)))) ^
              (Fintype.card {p // p ∈ s}) * (H : ℝ) ^ n) := by
          refine mul_le_mul_of_nonneg_left ?_ hDinv
          calc C0 ^ (Fintype.card {p // p ∈ s}) *
                (((3 : ℝ) ^ n + (sigConst n : ℝ) ^ (s.card)) * (H : ℝ) ^ n)
              = (C0 ^ (Fintype.card {p // p ∈ s}) *
                  ((3 : ℝ) ^ n + (sigConst n : ℝ) ^ (s.card))) * (H : ℝ) ^ n := by ring
            _ ≤ (max 1 (2 * C0 * ((3 : ℝ) ^ n + (sigConst n : ℝ)))) ^
                  (Fintype.card {p // p ∈ s}) * (H : ℝ) ^ n := hKH
      _ = (max 1 (2 * C0 * ((3 : ℝ) ^ n + (sigConst n : ℝ))) ^
              (Fintype.card {p // p ∈ s}) * (H : ℝ) ^ n) /
            (∏ i : {p // p ∈ s}, ((i : ℕ) : ℝ) ^ (k i)) := by ring
  exact hfin

end
end Submission.Vdw
