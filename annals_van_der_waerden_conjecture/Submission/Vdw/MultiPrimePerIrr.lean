import Mathlib
import Submission.Vdw.MultiPrimeCount
import Submission.Vdw.FourierIndexBound
import Submission.Commons.Analysis.ExpLog.eventually_one_add_log_pow_le_rpow

open Finset
open scoped BigOperators

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-!
# From the multi-prime counting bound to the §4 index-condition input

`MultiPrimeCount.multiPrime_count_le` is the multi-prime counting bound in the
regime `∏_{p∈s} p ≤ H^{1+1/(2n)}`, valid once the logarithmic side conditions
`(1+log ∏p)^n ≤ H^{1/(4n)}` and `≤ √H` hold.  Those are *eventual* in `H`, so
the bound takes the eventual form `PerIrrBoundEv`, from which the paper's `§4`
input `PerIrrBound` (Corollary `fbound2`, index-condition form, consumed by
Case I and Case III) follows by the trivial box bound in the bounded range.

Axioms: propext / Classical.choice / Quot.sound only.
-/

namespace Submission.Vdw
noncomputable section

/-- The eventual form of the §4 index-condition input: the paper's Corollary
`fbound2` holds for all sufficiently large `H`. -/
def PerIrrBoundEv (n : ℕ) : Prop :=
  ∃ H₀ c : ℕ, 1 ≤ c ∧ ∀ H : ℕ, H₀ ≤ H → ∀ D : ℕ, D ≠ 0 → Squarefull D → 2 ≤ D →
    (∀ p ∈ D.primeFactors, n < p) →
    (∀ p ∈ D.primeFactors, D.factorization p < n) →
    (radical D : ℝ) ≤ (H : ℝ) ^ (1 + 1 / (2 * (n : ℝ))) →
    ((Nat.card {f : ↥(Box n H) // ∀ p : D.primeFactors,
        indexClass (F := ZMod (p : ℕ)) n (D.factorization (p : ℕ))
          (boxResidue n H (p : ℕ) f)} : ℕ) : ℝ)
      ≤ (c : ℝ) ^ omega D * (H : ℝ) ^ n / (D : ℝ)

/-- The radical of a nonzero natural number is positive. -/
lemma radical_pos' (D : ℕ) : 0 < radical D := by
  rw [radical_eq_prod_primeFactors]
  exact Finset.prod_pos (fun p hp => (Nat.prime_of_mem_primeFactors hp).pos)

/-- The product of the subtype elements of `D.primeFactors`, weighted by the
factorization exponent, is `D`. -/
lemma prod_subtype_factorization_eq (D : ℕ) (hD : D ≠ 0) :
    (∏ i : {p // p ∈ D.primeFactors}, ((i : ℕ) : ℝ) ^ (D.factorization (i : ℕ)))
      = (D : ℝ) := by
  have h1 : (∏ i : {p // p ∈ D.primeFactors}, ((i : ℕ) : ℝ) ^ (D.factorization (i : ℕ)))
      = ∏ i : {p // p ∈ D.primeFactors},
          (((i : ℕ) ^ D.factorization (i : ℕ) : ℕ) : ℝ) :=
    Finset.prod_congr rfl (fun i _ => (Nat.cast_pow (α := ℝ) (i : ℕ) _).symm)
  rw [h1, ← Nat.cast_prod]
  have h2 : (∏ i : {p // p ∈ D.primeFactors}, (i : ℕ) ^ D.factorization (i : ℕ))
      = ∏ p ∈ D.primeFactors, p ^ D.factorization p :=
    Finset.prod_attach D.primeFactors (fun p => p ^ D.factorization p)
  rw [h2, (Nat.prod_primeFactors_pow_factorization hD).symm]

/-- `ω D` is the number of elements of the subtype `D.primeFactors`. -/
lemma card_subtype_primeFactors (D : ℕ) :
    Fintype.card {p // p ∈ D.primeFactors} = omega D := by
  rw [omega]
  rw [← Finset.card_attach]; rfl

/-- **The multi-prime count gives the eventual §4 input.** -/
theorem perIrrBoundEv_of_MIndexBound (n : ℕ) (hn : 3 ≤ n) (hM : MIndexBound n) :
    PerIrrBoundEv n := by
  obtain ⟨K, hK1, hK⟩ := multiPrime_count_le n hn hM
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hn1R : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hev1 : ∀ᶠ H : ℕ in Filter.atTop,
      (1 + Real.log ((H : ℝ) ^ 2)) ^ n ≤ (H : ℝ) ^ (1 / (4 * (n : ℝ))) :=
    Commons.Analysis.ExpLog.eventually_one_add_log_pow_le_rpow n 2 (1 / (4 * (n : ℝ)))
      (by positivity)
  have hev2 : ∀ᶠ H : ℕ in Filter.atTop,
      (1 + Real.log ((H : ℝ) ^ 2)) ^ n ≤ (H : ℝ) ^ (1 / 2 : ℝ) :=
    Commons.Analysis.ExpLog.eventually_one_add_log_pow_le_rpow n 2 (1 / 2 : ℝ)
      (by norm_num)
  have hev : ∀ᶠ H : ℕ in Filter.atTop,
      ((1 + Real.log ((H : ℝ) ^ 2)) ^ n ≤ (H : ℝ) ^ (1 / (4 * (n : ℝ))) ∧
        (1 + Real.log ((H : ℝ) ^ 2)) ^ n ≤ (H : ℝ) ^ (1 / 2 : ℝ)) ∧ 1 ≤ H :=
    hev1.and hev2 |>.and (Filter.eventually_ge_atTop 1)
  obtain ⟨H₀, hH₀⟩ := Filter.eventually_atTop.mp hev
  refine ⟨H₀, Nat.ceil K, Nat.one_le_ceil_iff.mpr (lt_of_lt_of_le zero_lt_one hK1), ?_⟩
  intro H hH D hD0 hsq hD2 hgt hfac hrad
  obtain ⟨⟨hlogH, hlogH2⟩, hH1⟩ := hH₀ H hH
  have hprime : ∀ p ∈ D.primeFactors, Nat.Prime p :=
    fun p hp => Nat.prime_of_mem_primeFactors hp
  haveI : ∀ p : {p // p ∈ D.primeFactors}, Fact (Nat.Prime (p : ℕ)) :=
    fun p => ⟨Nat.prime_of_mem_primeFactors p.2⟩
  haveI : ∀ p : {p // p ∈ D.primeFactors}, NeZero (p : ℕ) :=
    fun p => ⟨(Nat.prime_of_mem_primeFactors p.2).ne_zero⟩
  -- `2 ≤ ∏ p ∈ D.primeFactors, p`
  have hC2 : 2 ≤ ∏ p ∈ D.primeFactors, p := by
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (by omega : D ≠ 1)
    have hpmem : p ∈ D.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpd, hD0⟩
    have hdvd : p ∣ ∏ q ∈ D.primeFactors, q := Finset.dvd_prod_of_mem (fun q => q) hpmem
    exact le_trans hp.two_le
      (Nat.le_of_dvd (Finset.prod_pos (fun q hq => (hprime q hq).pos)) hdvd)
  -- `1 ≤ H`
  have hHge1 : 1 ≤ H := by
    have h1 : (1 : ℝ) ≤ (∏ p ∈ D.primeFactors, p : ℕ) := by
      have h2 : 1 ≤ ∏ p ∈ D.primeFactors, p :=
        Nat.one_le_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr
          (fun p hp => (hprime p hp).ne_zero))
      exact_mod_cast h2
    have h3 : (1 : ℝ) ≤ (H : ℝ) ^ (1 + 1 / (2 * (n : ℝ))) := le_trans h1 hrad
    rcases Nat.eq_zero_or_pos H with h0 | hpos
    · exfalso
      rw [h0, Nat.cast_zero, Real.zero_rpow (by positivity)] at h3
      linarith
    · exact hpos
  have hHR : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hHge1
  -- the logarithmic side conditions
  have hBase1 : (1 : ℝ) ≤ (∏ p ∈ D.primeFactors, p : ℕ) := by
    have h2 : 1 ≤ ∏ p ∈ D.primeFactors, p :=
      Nat.one_le_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr
        (fun p hp => (hprime p hp).ne_zero))
    exact_mod_cast h2
  have hlogH' : (1 + Real.log ((H : ℝ) ^ (2 : ℝ))) ^ n
      ≤ (H : ℝ) ^ (1 / (4 * (n : ℝ))) := by
    rw [Real.rpow_two]; exact hlogH
  have hlogH2' : (1 + Real.log ((H : ℝ) ^ (2 : ℝ))) ^ n
      ≤ (H : ℝ) ^ (1 / 2 : ℝ) := by
    rw [Real.rpow_two]; exact hlogH2
  have hle : Real.log ((∏ p ∈ D.primeFactors, p : ℕ) : ℝ) ≤ Real.log ((H : ℝ) ^ (2 : ℝ)) := by
    refine Real.log_le_log (by positivity) ?_
    have hexp : (1 : ℝ) + 1 / (2 * (n : ℝ)) ≤ 2 := by
      have h2n : (0 : ℝ) < 2 * (n : ℝ) := by positivity
      have h : 1 / (2 * (n : ℝ)) ≤ 1 := by
        rw [div_le_one h2n]
        linarith
      linarith
    exact le_trans hrad (Real.rpow_le_rpow_of_exponent_le hHR hexp)
  have hbaselog : (0 : ℝ) ≤ 1 + Real.log ((∏ p ∈ D.primeFactors, p : ℕ) : ℝ) := by
    have := Real.log_nonneg hBase1
    linarith
  have hlog1 : (1 + Real.log ((∏ p ∈ D.primeFactors, p : ℕ) : ℝ)) ^ n
      ≤ (H : ℝ) ^ (1 / (4 * (n : ℝ))) :=
    le_trans (pow_le_pow_left₀ hbaselog (by linarith) n) hlogH'
  have hlog2 : (1 + Real.log ((∏ p ∈ D.primeFactors, p : ℕ) : ℝ)) ^ n
      ≤ (H : ℝ) ^ (1 / 2 : ℝ) :=
    le_trans (pow_le_pow_left₀ hbaselog (by linarith) n) hlogH2'
  -- the main bound
  have hmain := hK D.primeFactors hprime H (fun p => D.factorization (p : ℕ))
    (fun p => le_of_lt (hfac (p : ℕ) p.2)) hC2 hHge1 hrad hlog1 hlog2
  refine le_trans hmain ?_
  rw [card_subtype_primeFactors D, prod_subtype_factorization_eq D hD0]
  have hKD : K ^ (omega D) ≤ ((Nat.ceil K : ℕ) : ℝ) ^ (omega D) :=
    pow_le_pow_left₀ (le_trans zero_le_one hK1) (Nat.le_ceil K) _
  have hDpos' : (0 : ℝ) < (D : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hD0
  have hHnD : (0 : ℝ) ≤ (H : ℝ) ^ n / (D : ℝ) := by positivity
  calc K ^ (omega D) * (H : ℝ) ^ n / (D : ℝ)
      = K ^ (omega D) * ((H : ℝ) ^ n / (D : ℝ)) := by ring
    _ ≤ ((Nat.ceil K : ℕ) : ℝ) ^ (omega D) * ((H : ℝ) ^ n / (D : ℝ)) :=
        mul_le_mul_of_nonneg_right hKD hHnD
    _ = ((Nat.ceil K : ℕ) : ℝ) ^ (omega D) * (H : ℝ) ^ n / (D : ℝ) := by ring

/-- **The eventual §4 input implies the §4 input.**  In the bounded range
`H < H₀` the trivial box bound suffices, using `√D ≤ H^{1+1/(2n)}`-type
squarefullness to see that the target bound is at least `c`. -/
theorem perIrrBound_of_perIrrBoundEv (n : ℕ) (hn : 3 ≤ n) (h : PerIrrBoundEv n) :
    ∃ c, 1 ≤ c ∧ PerIrrBound n c := by
  obtain ⟨H₀, c₀, hc₀1, hc₀⟩ := h
  refine ⟨max c₀ ((2 * H₀ + 1) ^ n), le_trans hc₀1 (le_max_left _ _), ?_⟩
  intro H D hD0 hsq hD2 hgt hrad hfac
  by_cases hHH : H₀ ≤ H
  · refine le_trans (hc₀ H hHH D hD0 hsq hD2 hgt hfac hrad) ?_
    have hc : (c₀ : ℝ) ≤ ((max c₀ ((2 * H₀ + 1) ^ n) : ℕ) : ℝ) := by
      exact_mod_cast le_max_left c₀ ((2 * H₀ + 1) ^ n)
    have h1 : (c₀ : ℝ) ^ omega D ≤ ((max c₀ ((2 * H₀ + 1) ^ n) : ℕ) : ℝ) ^ omega D :=
      pow_le_pow_left₀ (by positivity) hc _
    have h2 : (0 : ℝ) ≤ (H : ℝ) ^ n / (D : ℝ) := by
      have : (0 : ℝ) < (D : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hD0
      positivity
    calc (c₀ : ℝ) ^ omega D * (H : ℝ) ^ n / (D : ℝ)
        = (c₀ : ℝ) ^ omega D * ((H : ℝ) ^ n / (D : ℝ)) := by ring
      _ ≤ ((max c₀ ((2 * H₀ + 1) ^ n) : ℕ) : ℝ) ^ omega D * ((H : ℝ) ^ n / (D : ℝ)) :=
          mul_le_mul_of_nonneg_right h1 h2
      _ = ((max c₀ ((2 * H₀ + 1) ^ n) : ℕ) : ℝ) ^ omega D * (H : ℝ) ^ n / (D : ℝ) := by ring
  · push_neg at hHH
    have hH1 : 1 ≤ H := by
      have h1 : (1 : ℝ) ≤ (radical D : ℝ) := by
        have : 1 ≤ radical D := Nat.one_le_iff_ne_zero.mpr (ne_of_gt (radical_pos' D))
        exact_mod_cast this
      have h3 : (1 : ℝ) ≤ (H : ℝ) ^ (1 + 1 / (2 * (n : ℝ))) := le_trans h1 hrad
      rcases Nat.eq_zero_or_pos H with h0 | hpos
      · exfalso
        rw [h0, Nat.cast_zero, Real.zero_rpow (by positivity)] at h3
        linarith
      · exact hpos
    have homega1 : 1 ≤ omega D := by
      obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (by omega : D ≠ 1)
      have hmem : p ∈ D.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpd, hD0⟩
      rw [omega]
      exact Finset.card_pos.mpr ⟨p, hmem⟩
    -- trivial box bound
    have hcount : ((Nat.card {f : ↥(Box n H) // ∀ p : D.primeFactors,
        indexClass (F := ZMod (p : ℕ)) n (D.factorization (p : ℕ))
          (boxResidue n H (p : ℕ) f)} : ℕ) : ℝ) ≤ (((2 * H + 1) ^ n : ℕ) : ℝ) := by
      have h1 : Nat.card {f : ↥(Box n H) // ∀ p : D.primeFactors,
          indexClass (F := ZMod (p : ℕ)) n (D.factorization (p : ℕ))
            (boxResidue n H (p : ℕ) f)} ≤ Nat.card ↥(Box n H) :=
        Nat.card_le_card_of_injective (fun x => x.1) (fun a b hab => Subtype.ext hab)
      have h2 : Nat.card ↥(Box n H) = (2 * H + 1) ^ n := by
        rw [← Commons.Data.Set.ncard_eq_natCard (Box n H), Box_ncard_eq]
      calc ((Nat.card {f : ↥(Box n H) // ∀ p : D.primeFactors,
            indexClass (F := ZMod (p : ℕ)) n (D.factorization (p : ℕ))
              (boxResidue n H (p : ℕ) f)} : ℕ) : ℝ)
          ≤ ((Nat.card ↥(Box n H) : ℕ) : ℝ) := by exact_mod_cast h1
        _ = (((2 * H + 1) ^ n : ℕ) : ℝ) := by rw [h2]
    have hleC : (((2 * H + 1) ^ n : ℕ) : ℝ) ≤ ((max c₀ ((2 * H₀ + 1) ^ n) : ℕ) : ℝ) := by
      have h1 : (2 * H + 1) ^ n ≤ (2 * H₀ + 1) ^ n := Nat.pow_le_pow_left (by omega) n
      exact_mod_cast le_trans h1 (le_max_right _ _)
    -- `D ≤ H^{((n-1)(1+1/(2n)))}`
    have hDpow : (D : ℝ) ≤ (H : ℝ) ^ (((n : ℝ) - 1) * (1 + 1 / (2 * (n : ℝ)))) := by
      have hDrad : D ≤ (radical D) ^ (n - 1) := by
        have hprod : ∏ p ∈ D.primeFactors, p ^ D.factorization p
            ≤ ∏ p ∈ D.primeFactors, p ^ (n - 1) :=
          Finset.prod_le_prod (fun p _ => Nat.zero_le _) (fun p hp =>
            Nat.pow_le_pow_right
              (Nat.one_le_iff_ne_zero.mpr (Nat.prime_of_mem_primeFactors hp).ne_zero)
              (Nat.le_sub_one_of_lt (hfac p hp)))
        have hprod2 : ∏ p ∈ D.primeFactors, p ^ (n - 1) = (radical D) ^ (n - 1) := by
          rw [radical_eq_prod_primeFactors, Finset.prod_pow]
        calc D = ∏ p ∈ D.primeFactors, p ^ D.factorization p :=
              Nat.prod_primeFactors_pow_factorization hD0
          _ ≤ ∏ p ∈ D.primeFactors, p ^ (n - 1) := hprod
          _ = (radical D) ^ (n - 1) := hprod2
      have h1 : (D : ℝ) ≤ (radical D : ℝ) ^ ((n - 1 : ℕ) : ℝ) := by
        rw [Real.rpow_natCast]; exact_mod_cast hDrad
      have h2 : (radical D : ℝ) ^ ((n - 1 : ℕ) : ℝ)
          ≤ ((H : ℝ) ^ (1 + 1 / (2 * (n : ℝ)))) ^ ((n - 1 : ℕ) : ℝ) :=
        Real.rpow_le_rpow (by positivity) hrad (by positivity)
      have h3 : ((H : ℝ) ^ (1 + 1 / (2 * (n : ℝ)))) ^ ((n - 1 : ℕ) : ℝ)
          = (H : ℝ) ^ (((n : ℝ) - 1) * (1 + 1 / (2 * (n : ℝ)))) := by
        rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ (H : ℝ))]
        congr 1
        have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega : 1 ≤ n)]; norm_num
        rw [hcast]; ring
      exact le_trans h1 (le_trans h2 (le_of_eq h3))
    have hHR1 : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH1
    have hexple : (H : ℝ) ^ (((n : ℝ) - 1) * (1 + 1 / (2 * (n : ℝ)))) ≤ (H : ℝ) ^ n := by
      rw [← Real.rpow_natCast (H : ℝ) n]
      refine Real.rpow_le_rpow_of_exponent_le hHR1 ?_
      have hdiv : ((n : ℝ) - 1) * (1 / (2 * (n : ℝ))) ≤ 1 := by
        rw [mul_one_div, div_le_one (by positivity)]
        linarith
      have hlin : (n : ℝ) - 1 ≤ (n : ℝ) := by linarith
      rw [mul_add, mul_one]
      linarith
    have hDpos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hD0
    have hcmax0 : (0 : ℝ) ≤ ((max c₀ ((2 * H₀ + 1) ^ n) : ℕ) : ℝ) := by positivity
    have hmain2 : (((2 * H + 1) ^ n : ℕ) : ℝ) * (D : ℝ)
        ≤ ((max c₀ ((2 * H₀ + 1) ^ n) : ℕ) : ℝ) * (H : ℝ) ^ n := by
      calc (((2 * H + 1) ^ n : ℕ) : ℝ) * (D : ℝ)
          ≤ ((max c₀ ((2 * H₀ + 1) ^ n) : ℕ) : ℝ) * (D : ℝ) :=
            mul_le_mul_of_nonneg_right hleC hDpos.le
        _ ≤ ((max c₀ ((2 * H₀ + 1) ^ n) : ℕ) : ℝ) * (H : ℝ) ^ n :=
            mul_le_mul_of_nonneg_left (le_trans hDpow hexple) hcmax0
    have hfinal : (((2 * H + 1) ^ n : ℕ) : ℝ)
        ≤ ((max c₀ ((2 * H₀ + 1) ^ n) : ℕ) : ℝ) * (H : ℝ) ^ n / (D : ℝ) := by
      rw [le_div_iff₀ hDpos]
      exact hmain2
    have hcmax1 : (1 : ℝ) ≤ ((max c₀ ((2 * H₀ + 1) ^ n) : ℕ) : ℝ) := by
      exact_mod_cast le_trans hc₀1 (le_max_left _ _)
    have hcpow : ((max c₀ ((2 * H₀ + 1) ^ n) : ℕ) : ℝ)
        ≤ ((max c₀ ((2 * H₀ + 1) ^ n) : ℕ) : ℝ) ^ omega D := by
      calc ((max c₀ ((2 * H₀ + 1) ^ n) : ℕ) : ℝ)
          = ((max c₀ ((2 * H₀ + 1) ^ n) : ℕ) : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ ((max c₀ ((2 * H₀ + 1) ^ n) : ℕ) : ℝ) ^ omega D :=
            pow_le_pow_right₀ hcmax1 homega1
    have hfin : ((max c₀ ((2 * H₀ + 1) ^ n) : ℕ) : ℝ) * (H : ℝ) ^ n / (D : ℝ)
        ≤ ((max c₀ ((2 * H₀ + 1) ^ n) : ℕ) : ℝ) ^ omega D * (H : ℝ) ^ n / (D : ℝ) := by
      have hnn : (0 : ℝ) ≤ (H : ℝ) ^ n / (D : ℝ) := by positivity
      calc ((max c₀ ((2 * H₀ + 1) ^ n) : ℕ) : ℝ) * (H : ℝ) ^ n / (D : ℝ)
          = ((max c₀ ((2 * H₀ + 1) ^ n) : ℕ) : ℝ) * ((H : ℝ) ^ n / (D : ℝ)) := by ring
        _ ≤ ((max c₀ ((2 * H₀ + 1) ^ n) : ℕ) : ℝ) ^ omega D * ((H : ℝ) ^ n / (D : ℝ)) :=
            mul_le_mul_of_nonneg_right hcpow hnn
        _ = ((max c₀ ((2 * H₀ + 1) ^ n) : ℕ) : ℝ) ^ omega D * (H : ℝ) ^ n / (D : ℝ) := by ring
    exact le_trans hcount (le_trans hfinal hfin)

end
end Submission.Vdw
