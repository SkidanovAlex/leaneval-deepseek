import Mathlib
import Submission.Vdw.CaseIRestricted
import Submission.Vdw.CaseITail
import Submission.Vdw.CaseISmallPrime
import Submission.Vdw.CaseIExact
import Submission.Vdw.DiscriminantCap
import Submission.Vdw.LinearFactor
import Submission.Commons.Analysis.ExpLog.eventually_one_add_log_pow_le_rpow
import Submission.Commons.Data.Nat.eventually_heightCap_le_pow
import Submission.Commons.Analysis.Asymptotics.isBigO_of_natCast_le_mul_pow
import Submission.Commons.Analysis.Asymptotics.isBigO_of_eventually_le
import Submission.Vdw.CaseIIIRegion

open Polynomial Asymptotics
open scoped BigOperators
open Filter

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-!
# Case I, direct regime: the `C_f ≤ H`, `D_f > H^(2+2δ)` region and its count

This module assembles the *direct-regime* Case-I count (Roadmap S1 chain): the
number of monic irreducible degree-`n` polynomials in the height-`H` box whose
field discriminant `D_f = |Disc K_f|` is squarefull, whose ramified product
`C_f = radical D_f` is `≤ H`, and whose discriminant exceeds `H^(2+2δ)`
(`δ = 1/(2n)`), is `O(H^(n-1))`.

The ingredients (all previously proved):

* `CaseIRestricted.mem_restrictedSieve_of_fieldDisc` — every such `f` satisfies
  the restricted sieve conditions at the large primes `p > n` of `D_f`;
* `CaseIDisc.discSplit` + `CaseISmallPrime.discSmallPart_fieldDisc_le` — the
  small-prime part `S := discSmallPart n D_f` of the discriminant is bounded by
  the `n`-only constant `smallConst n`, so the large-prime part
  `d := discLargePart n D_f = D_f/S` still exceeds `H^(2+2δ)/S₀(n)`;
* `CaseIExact.restrictedPerDiscriminant_exact_le` — the per-modulus sieve
  bound `≤ 4^n·2^((n+1)^4·ω(d))·H^n/d`;
* `CaseITail.squarefull_tail_bound` — the squarefull tail sum
  `Σ_{Y<D≤Z, sqfull} c^ω(D)/D ≤ (1+log Z)^(2c)/Y^(1/2)`;
* `DiscriminantCap.fieldDisc_height_bound` — the ceiling `Z` of the range.

The result is `CaseIDirect_isBigO`.

Axioms of every statement: propext / Classical.choice / Quot.sound only.
-/

namespace Submission.Vdw

noncomputable section

/-- **The small-prime constant** `S₀(n) = primorial n ^ (n + n·⌊log_2 n⌋)`: the
bound for `discSmallPart n D_f` (Session-134, `CaseISmallPrime`). -/
def smallConst (n : ℕ) : ℕ := primorial n ^ (n + n * Nat.log 2 n)

/-- **The Case-I direct-regime counting threshold**
`Y = ⌊H^(2+2δ)/S₀(n)⌋`, `δ = 1/(2n)`. -/
def caseIThr (n H : ℕ) : ℕ :=
  Nat.floor (((H : ℝ) ^ (2 + 1 / (n : ℝ))) / (smallConst n : ℝ))

/-- **The discriminant height ceiling** `Z = (2n−1)!·(n(H+1))^(2n−1)`
(`DiscriminantCap.fieldDisc_height_bound`). -/
def caseICap (n H : ℕ) : ℕ := (2 * n - 1).factorial * (n * (H + 1)) ^ (2 * n - 1)

/-- **The Case-I direct region (box level)**: monic irreducible degree-`n` box
polynomials with squarefull field discriminant `D_f`, ramified product
`C_f = radical D_f ≤ H`, and `D_f > H^(2+2δ)`. -/
def CaseIDirectBox (n H : ℕ) : Set ↥(Box n H) :=
  {f | ∃ h : Irreducible (f.1.map φℚ),
      Squarefull (fieldDiscExp f.1 h) ∧ radical (fieldDiscExp f.1 h) ≤ H ∧
      (H : ℝ) ^ (2 + 1 / (n : ℝ)) < (fieldDiscExp f.1 h : ℝ)}

/-- The restricted sieve set at modulus `d` (box level): the box polynomials
satisfying the residue index conditions at every prime `p | d`. -/
def sieveAt (n H : ℕ) (d : ℕ) : Set ↥(Box n H) :=
  {f | ∀ p : d.primeFactors, indexClass (F := ZMod (p : ℕ)) n
        (min (d.factorization (p : ℕ)) n) (boxResidue n H (p : ℕ) f)}

/-- The index set of modulus values: `⌊H^(2+2δ)/S₀⌋ < d ≤ Z`, `d` squarefull,
all prime factors of `d` exceeding `n` (so `d` is its own large-prime part),
`radical d ≤ H` and every exponent `v_p(d) < n`.  These are exactly the
conditions satisfied by `d = discLargePart n D_f` for a member of the region. -/
def caseIIndex (n H : ℕ) : Finset ℕ :=
  ((Finset.Icc (caseIThr n H + 1) (caseICap n H)).filter Squarefull).filter
    (fun d => (∀ p ∈ d.primeFactors, n < p) ∧ radical d ≤ H ∧
      (∀ p ∈ d.primeFactors, d.factorization p < n))

/-- The primorial (product of primes `≤ n`) is positive. -/
lemma primorial_pos' (n : ℕ) : 0 < primorial n := by
  unfold primorial
  exact Finset.prod_pos (fun p hp => (Finset.mem_filter.mp hp).2.pos)

/-- `smallConst n > 0`. -/
lemma smallConst_pos (n : ℕ) : 0 < smallConst n := by
  unfold smallConst
  exact pow_pos (primorial_pos' n) _

/-- The large part of a number whose prime factors all exceed `n` is the number
itself. -/
lemma discLargePart_self (n D : ℕ) (hD : D ≠ 0)
    (h : ∀ p ∈ D.primeFactors, n < p) : discLargePart n D = D := by
  unfold discLargePart
  have hfil : (Nat.primeFactors D).filter (fun p => n < p) = Nat.primeFactors D := by
    exact Finset.filter_true_of_mem h
  rw [hfil]
  exact (Nat.prod_primeFactors_pow_factorization hD).symm

/-- The radical is monotone for divisibility. -/
lemma radical_le_of_dvd {a b : ℕ} (hab : a ∣ b) (hb : b ≠ 0) : radical a ≤ radical b := by
  rw [radical_eq_prod_primeFactors a, radical_eq_prod_primeFactors b]
  exact Finset.prod_le_prod_of_subset_of_one_le (primeFactors_subset_of_dvd hab hb)
    (fun p _ => Nat.zero_le p)
    (fun p hp _ => (Nat.mem_primeFactors.mp hp).1.one_le)

/-- **The large-prime part of a squarefull number is squarefull.** -/
lemma squarefull_discLargePart (n D : ℕ) (hD : D ≠ 0) (hsq : Squarefull D) :
    Squarefull (discLargePart n D) := by
  intro p hp hpd
  have hdvd : discLargePart n D ∣ D := discLargePart_dvd n D hD
  have hd0 : discLargePart n D ≠ 0 :=
    Nat.ne_of_gt (Nat.pos_of_dvd_of_pos hdvd (Nat.pos_of_ne_zero hD))
  have hmem : p ∈ (discLargePart n D).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp, hpd, hd0⟩
  rw [Nat.Prime.pow_dvd_iff_le_factorization hp hd0, (factorization_discLargePart hD hmem).symm]
  have hdiv : p ^ 2 ∣ D := hsq p hp (dvd_trans hpd hdvd)
  rwa [Nat.Prime.pow_dvd_iff_le_factorization hp hD] at hdiv

/-- The large part is at most the number itself. -/
lemma discLargePart_le (n D : ℕ) (hD : D ≠ 0) : discLargePart n D ≤ D :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero hD) (discLargePart_dvd n D hD)

/-- The large part of `D ≠ 0` is nonzero. -/
lemma discLargePart_ne_zero (n D : ℕ) (hD : D ≠ 0) : discLargePart n D ≠ 0 :=
  Nat.ne_of_gt (Nat.pos_of_dvd_of_pos (discLargePart_dvd n D hD) (Nat.pos_of_ne_zero hD))


/-- **Region membership**: every member of `CaseIDirectBox` satisfies the
restricted sieve conditions at the large-prime part `d = discLargePart n D_f`
of its own field discriminant, and `d` lies in the index set. -/
theorem CaseIDirectBox_subset_biUnion (n H : ℕ) (hn : 3 ≤ n) (hH : 1 ≤ H) :
    CaseIDirectBox n H ⊆ {f : ↥(Box n H) | ∃ d ∈ caseIIndex n H, f ∈ sieveAt n H d} := by
  classical
  intro f hf
  obtain ⟨h, hsq, hC, hlarge⟩ := hf
  haveI : Fact (Irreducible (f.1.map φℚ)) := ⟨h⟩
  have hmon : f.1.Monic := f.2.1
  have hdeg : f.1.natDegree = n := Polynomial.natDegree_eq_of_degree_eq_some f.2.2.1
  have hD0 : fieldDiscExp f.1 h ≠ 0 := by
    simp only [fieldDiscExp, fieldDisc]
    exact Int.natAbs_ne_zero.mpr (NumberField.discr_ne_zero (Kpoly f.1))
  set D := fieldDiscExp f.1 h with hDdef
  set d := discLargePart n D with hddef
  have hd0 : d ≠ 0 := discLargePart_ne_zero n D hD0
  -- upper range
  have hdle : d ≤ caseICap n H := by
    have h1 : d ≤ D := discLargePart_le n D hD0
    have h2 : D ≤ caseICap n H :=
      fieldDisc_height_bound f.1 hmon n H hdeg (fun k hk => f.2.2.2 k hk)
    omega
  -- lower range
  have hsmallD : discSmallPart n D ≤ smallConst n :=
    discSmallPart_fieldDisc_le f.1 hmon n hdeg
  have hYd : caseIThr n H < d := by
    have hS0pos : (0 : ℝ) < (smallConst n : ℝ) := by exact_mod_cast smallConst_pos n
    have h1 : (caseIThr n H : ℝ) ≤ ((H : ℝ) ^ (2 + 1 / (n : ℝ))) / (smallConst n : ℝ) := by
      simp only [caseIThr]
      exact Nat.floor_le (by positivity)
    have h2 : ((H : ℝ) ^ (2 + 1 / (n : ℝ))) / (smallConst n : ℝ) < (D : ℝ) / (smallConst n : ℝ) :=
      div_lt_div_of_pos_right hlarge hS0pos
    have h3 : (D : ℝ) / (smallConst n : ℝ) ≤ (d : ℝ) := by
      rw [div_le_iff₀ hS0pos]
      have hDd : (D : ℝ) = (d : ℝ) * (discSmallPart n D : ℝ) := by
        have h : D = d * discSmallPart n D := (discSplit n D hD0).symm
        conv_lhs => rw [h]
        rw [Nat.cast_mul]
      rw [hDd]
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hsmallD) (by positivity)
    have := lt_of_le_of_lt h1 (lt_of_lt_of_le h2 h3)
    exact_mod_cast this
  -- index-set membership
  have hmem : d ∈ caseIIndex n H := by
    rw [caseIIndex, Finset.mem_filter, Finset.mem_filter]
    refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
    · rw [Finset.mem_Icc]; exact ⟨by omega, hdle⟩
    · exact squarefull_discLargePart n D hD0 hsq
    · intro p hp
      exact (mem_primeFactors_discLargePart hD0 hp).1
    · -- radical d ≤ H
      have hdvd : d ∣ D := discLargePart_dvd n D hD0
      calc radical d ≤ radical D := radical_le_of_dvd hdvd hD0
        _ ≤ H := hC
    · intro p hp
      have hpD : p ∈ d.primeFactors := hp
      have hfac := (factorization_discLargePart hD0 hp).symm
      have hpD' : p ∈ D.primeFactors :=
        primeFactors_subset_of_dvd (discLargePart_dvd n D hD0) hD0 hpD
      have hprim : Nat.Prime p := (Nat.mem_primeFactors.mp hpD).1
      haveI : Fact (Nat.Prime p) := ⟨hprim⟩
      have hpgt : n < p := (mem_primeFactors_discLargePart hD0 hp).1
      have hlt : D.factorization p < n := by
        have h1 : (fieldDisc f.1).factorization p < n :=
          fieldDisc_factorization_lt_of_prime_gt n H (by omega) f.1 hmon hdeg f.2 hpgt
            ((mem_primeFactors_discLargePart hD0 hp).2)
        exact h1
      rw [hfac]; exact hlt
  refine ⟨d, hmem, ?_⟩
  -- sieve conditions
  intro p
  exact mem_restrictedSieve_of_fieldDisc n H (by omega) f.1 hmon hdeg f.2 p


/-- **The region count is at most the sum over the index set of the per-modulus
restricted sieve bounds.** -/
theorem CaseIDirectBox_ncard_le_sum (n H : ℕ) (hn : 3 ≤ n) (hH : 1 ≤ H) :
    ((CaseIDirectBox n H).ncard : ℝ) ≤
      ∑ d ∈ caseIIndex n H,
        (4 : ℝ) ^ n * (2 : ℝ) ^ (((n + 1) ^ 4) * omega d) * (H : ℝ) ^ n / (d : ℝ) := by
  classical
  haveI : Finite ↥(Box n H) := box_finite n H
  have hfin : ({f : ↥(Box n H) | ∃ d ∈ caseIIndex n H, f ∈ sieveAt n H d}).Finite :=
    Set.toFinite _
  have h1 : (CaseIDirectBox n H).ncard ≤
      ({f : ↥(Box n H) | ∃ d ∈ caseIIndex n H, f ∈ sieveAt n H d}).ncard :=
    Set.ncard_le_ncard (CaseIDirectBox_subset_biUnion n H hn hH) hfin
  have h2 := ncard_biUnion_finset_le (caseIIndex n H) (sieveAt n H)
  have h3 : ∀ d ∈ caseIIndex n H, ((sieveAt n H d).ncard : ℝ) ≤
      (4 : ℝ) ^ n * (2 : ℝ) ^ (((n + 1) ^ 4) * omega d) * (H : ℝ) ^ n / (d : ℝ) := by
    intro d hd
    rw [caseIIndex, Finset.mem_filter, Finset.mem_filter] at hd
    obtain ⟨⟨hdIcc, _hsqd⟩, hlt, hrad, hfac⟩ := hd
    have hd0 : d ≠ 0 := by
      have := (Finset.mem_Icc.mp hdIcc).1
      omega
    have hself : discLargePart n d = d := discLargePart_self n d hd0 hlt
    have hC : radical (discLargePart n d) ≤ H := by rw [hself]; exact hrad
    have hsmall : ∀ p ∈ (discLargePart n d).primeFactors,
        (discLargePart n d).factorization p < n := by
      intro p hp
      rw [hself] at hp ⊢
      exact hfac p hp
    have hterm := restrictedPerDiscriminant_exact_le n H (by omega) hH d hd0 hC hsmall
    rw [hself] at hterm
    have hcard : (sieveAt n H d).ncard =
        Nat.card {f : ↥(Box n H) // ∀ p : d.primeFactors, indexClass (F := ZMod (p : ℕ)) n
          (min (d.factorization (p : ℕ)) n) (boxResidue n H (p : ℕ) f)} :=
      (Nat.card_coe_set_eq _).symm
    rw [hcard]
    simpa only [omega] using hterm
  have hcast : ((CaseIDirectBox n H).ncard : ℝ) ≤
      ((∑ d ∈ caseIIndex n H, (sieveAt n H d).ncard : ℕ) : ℝ) := by
    exact_mod_cast le_trans h1 h2
  calc ((CaseIDirectBox n H).ncard : ℝ)
      ≤ ((∑ d ∈ caseIIndex n H, (sieveAt n H d).ncard : ℕ) : ℝ) := hcast
    _ = ∑ d ∈ caseIIndex n H, ((sieveAt n H d).ncard : ℝ) := by
        rw [Nat.cast_sum]
    _ ≤ ∑ d ∈ caseIIndex n H,
          ((4 : ℝ) ^ n * (2 : ℝ) ^ (((n + 1) ^ 4) * omega d) * (H : ℝ) ^ n / (d : ℝ)) :=
        Finset.sum_le_sum h3

/-- **The sum over the index set is bounded by the squarefull tail sum.**  The
two hypotheses `1 ≤ caseIThr n H < caseICap n H` (automatic eventually in `H`)
make the tail bound usable. -/
theorem caseIIndex_sum_le_tail (n H : ℕ) (hn : 3 ≤ n) (hH : 1 ≤ H)
    (hY1 : 1 ≤ caseIThr n H) (hYT : caseIThr n H < caseICap n H) :
    ∑ d ∈ caseIIndex n H,
        (4 : ℝ) ^ n * (2 : ℝ) ^ (((n + 1) ^ 4) * omega d) * (H : ℝ) ^ n / (d : ℝ) ≤
      (4 : ℝ) ^ n * (H : ℝ) ^ n *
        ((1 + Real.log (caseICap n H : ℝ)) ^ (2 * 2 ^ ((n + 1) ^ 4)) /
          (caseIThr n H : ℝ) ^ ((1 : ℝ) / 2)) := by
  classical
  set c : ℕ := 2 ^ ((n + 1) ^ 4) with hc_def
  have hc1 : 1 ≤ c := Nat.one_le_two_pow
  have hcR : (c : ℝ) = (2 : ℝ) ^ ((n + 1) ^ 4) := by
    rw [hc_def]; push_cast; ring
  have htail := squarefull_tail_bound c hc1 ((1 : ℝ) / 2) (by norm_num) le_rfl
    (caseIThr n H) (caseICap n H) hY1 hYT
  have hsub : caseIIndex n H ⊆ Finset.Icc (caseIThr n H + 1) (caseICap n H) := by
    intro d hd
    rw [caseIIndex, Finset.mem_filter, Finset.mem_filter] at hd
    exact hd.1.1
  have hsqmem : ∀ d ∈ caseIIndex n H, Squarefull d := by
    intro d hd
    rw [caseIIndex, Finset.mem_filter, Finset.mem_filter] at hd
    exact hd.1.2
  have hsum1 : ∑ d ∈ caseIIndex n H, (c : ℝ) ^ omega d / (d : ℝ) ≤
      ∑ d ∈ Finset.Icc (caseIThr n H + 1) (caseICap n H),
        (if Squarefull d then (c : ℝ) ^ omega d / (d : ℝ) else 0) := by
    calc ∑ d ∈ caseIIndex n H, (c : ℝ) ^ omega d / (d : ℝ)
        = ∑ d ∈ caseIIndex n H,
            (if Squarefull d then (c : ℝ) ^ omega d / (d : ℝ) else 0) := by
          refine Finset.sum_congr rfl (fun d hd => ?_)
          simp [hsqmem d hd]
      _ ≤ ∑ d ∈ Finset.Icc (caseIThr n H + 1) (caseICap n H),
            (if Squarefull d then (c : ℝ) ^ omega d / (d : ℝ) else 0) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg hsub (fun d hdt hds => ?_)
          by_cases hsq : Squarefull d
          · simp only [hsq, if_true]
            have hd0 : (0 : ℝ) < (d : ℝ) := by
              have := (Finset.mem_Icc.mp hdt).1
              exact_mod_cast (by omega : 0 < d)
            positivity
          · simp [hsq]
  have hfactor : ∑ d ∈ caseIIndex n H,
        (4 : ℝ) ^ n * (2 : ℝ) ^ (((n + 1) ^ 4) * omega d) * (H : ℝ) ^ n / (d : ℝ) =
      ((4 : ℝ) ^ n * (H : ℝ) ^ n) *
        (∑ d ∈ caseIIndex n H, (c : ℝ) ^ omega d / (d : ℝ)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [pow_mul, ← hcR]
    ring
  rw [hfactor]
  refine le_trans (mul_le_mul_of_nonneg_left hsum1 (by positivity)) ?_
  refine le_trans (mul_le_mul_of_nonneg_left htail (by positivity)) ?_
  rw [hc_def]


/-- **The Case-I direct region is `O(H^(n-1))`** (with an explicit real
constant).  Assembly of the per-modulus sieve sum, the squarefull tail bound
and the two eventual estimates (log absorption, threshold lower bound). -/
theorem CaseIDirectBox_bound_real (n : ℕ) (hn : 3 ≤ n) :
    ∃ C : ℝ, ∀ᶠ H : ℕ in atTop,
      ((CaseIDirectBox n H).ncard : ℝ) ≤ C * (H : ℝ) ^ (n - 1) := by
  set S : ℕ := smallConst n with hS_def
  have hSpos : (0 : ℝ) < (S : ℝ) := by
    rw [hS_def]; exact_mod_cast smallConst_pos n
  have hnR : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  -- (A) the threshold lies in the admissible range
  have hthr : ∀ᶠ H : ℕ in atTop, 1 ≤ caseIThr n H ∧ caseIThr n H < caseICap n H := by
    have hbig : ∀ᶠ H : ℕ in atTop, (2 : ℝ) * (S : ℝ) ≤ (H : ℝ) ^ (2 + 1 / (n : ℝ)) :=
      Commons.Analysis.ExpLog.eventually_natCast_rpow_atTop_ge _ _ (by positivity)
    have hcmp : ∀ᶠ H : ℕ in atTop, (H : ℝ) ^ (2 + 1 / (n : ℝ)) < (caseICap n H : ℝ) := by
      have hlt : ∀ᶠ H : ℕ in atTop,
          (H : ℝ) ^ (2 + 1 / (n : ℝ)) < (H : ℝ) ^ (((2 * n - 1 : ℕ)) : ℝ) := by
        filter_upwards [eventually_ge_atTop (2 : ℕ)] with H hH
        have hH1 : (1 : ℝ) < (H : ℝ) := by exact_mod_cast (by omega : 1 < H)
        refine Real.rpow_lt_rpow_of_exponent_lt hH1 ?_
        have h1 : 1 / (n : ℝ) ≤ 1 := by
          rw [div_le_one hnpos]; linarith
        have h2n : (((2 * n - 1 : ℕ)) : ℝ) = 2 * (n : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega : 1 ≤ 2 * n)]
          push_cast
          ring
        rw [h2n]
        linarith
      have hcap : ∀ᶠ H : ℕ in atTop,
          (H : ℝ) ^ (((2 * n - 1 : ℕ)) : ℝ) ≤ (caseICap n H : ℝ) := by
        refine Filter.eventually_atTop.mpr ⟨1, fun H _ => ?_⟩
        have hnat : H ^ (2 * n - 1) ≤ caseICap n H := by
          simp only [caseICap]
          calc H ^ (2 * n - 1) ≤ (n * (H + 1)) ^ (2 * n - 1) :=
                Nat.pow_le_pow_left (by nlinarith [Nat.zero_le H]) _
            _ = 1 * (n * (H + 1)) ^ (2 * n - 1) := (one_mul _).symm
            _ ≤ (2 * n - 1).factorial * (n * (H + 1)) ^ (2 * n - 1) :=
                Nat.mul_le_mul_right _ (by have := Nat.factorial_pos (2 * n - 1); omega)
        calc (H : ℝ) ^ (((2 * n - 1 : ℕ)) : ℝ) = (H : ℝ) ^ (2 * n - 1) :=
              Real.rpow_natCast _ _
          _ ≤ (caseICap n H : ℝ) := by exact_mod_cast hnat
      filter_upwards [hlt, hcap] with H h1 h2
      exact lt_of_lt_of_le h1 h2
    filter_upwards [hbig, hcmp] with H h1 h2
    have hSpos' : (0 : ℝ) < (smallConst n : ℝ) := by rw [← hS_def]; exact hSpos
    refine ⟨?_, ?_⟩
    · simp only [caseIThr]
      refine Nat.le_floor ?_
      rw [le_div_iff₀ hSpos']
      linarith
    · simp only [caseIThr]
      refine (Nat.floor_lt (div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg H) _)
        (le_of_lt hSpos'))).mpr ?_
      have hS1 : (1 : ℝ) ≤ (smallConst n : ℝ) := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (smallConst_pos n).ne')
      have hx : (0 : ℝ) ≤ (H : ℝ) ^ (2 + 1 / (n : ℝ)) :=
        Real.rpow_nonneg (Nat.cast_nonneg H) _
      have hle : (H : ℝ) ^ (2 + 1 / (n : ℝ)) / (smallConst n : ℝ) ≤
          (H : ℝ) ^ (2 + 1 / (n : ℝ)) := by
        rw [div_le_iff₀ hSpos']
        simpa using mul_le_mul_of_nonneg_left hS1 hx
      linarith
  -- (B) log absorption
  have hlog : ∀ᶠ H : ℕ in atTop,
      (1 + Real.log (caseICap n H : ℝ)) ^ (2 * 2 ^ ((n + 1) ^ 4)) ≤
        (H : ℝ) ^ ((1 : ℝ) / (2 * n)) := by
    have hpow := Commons.Analysis.ExpLog.eventually_one_add_log_pow_le_rpow
      (2 * 2 ^ ((n + 1) ^ 4)) 1 ((1 : ℝ) / (4 * n)) (by positivity)
    have hconst : ∀ᶠ H : ℕ in atTop,
        (((4 * n ^ 2 : ℕ) : ℝ) + 1) ^ (2 * 2 ^ ((n + 1) ^ 4)) ≤
          (H : ℝ) ^ ((1 : ℝ) / (4 * n)) :=
      Commons.Analysis.ExpLog.eventually_natCast_rpow_atTop_ge _ _ (by positivity)
    have hcap : ∀ᶠ H : ℕ in atTop, caseICap n H ≤ H ^ (4 * n ^ 2) := by
      filter_upwards [Commons.Data.Nat.eventually_heightCap_le_pow n (by omega)] with H hH
      simpa only [caseICap] using hH
    have hge1 : ∀ᶠ H : ℕ in atTop, (1 : ℝ) ≤ (H : ℝ) :=
      (eventually_ge_atTop (1 : ℕ)).mono (fun H h => by exact_mod_cast h)
    filter_upwards [hpow, hconst, hcap, hge1] with H hpow hconst hcap hge1
    have hHpos : (0 : ℝ) < (H : ℝ) := lt_of_lt_of_le one_pos hge1
    have hZ1 : (1 : ℝ) ≤ (caseICap n H : ℝ) := by
      have hnat : 1 ≤ caseICap n H := by
        simp only [caseICap]
        exact Nat.one_le_iff_ne_zero.mpr
          (Nat.mul_ne_zero (Nat.factorial_ne_zero _)
            (pow_ne_zero _ (Nat.mul_ne_zero (by omega : n ≠ 0) (by omega : H + 1 ≠ 0))))
      exact_mod_cast hnat
    have hlogZ : Real.log (caseICap n H : ℝ) ≤ ((4 * n ^ 2 : ℕ) : ℝ) * Real.log (H : ℝ) := by
      have hpos : (0 : ℝ) < ((H : ℝ) ^ (4 * n ^ 2)) := by positivity
      calc Real.log (caseICap n H : ℝ) ≤ Real.log ((H : ℝ) ^ (4 * n ^ 2)) :=
            Real.log_le_log (by linarith) (by exact_mod_cast hcap)
        _ = ((4 * n ^ 2 : ℕ) : ℝ) * Real.log (H : ℝ) := Real.log_pow _ _
    have hlogH0 : (0 : ℝ) ≤ Real.log (H : ℝ) := Real.log_nonneg hge1
    have hstep : 1 + Real.log (caseICap n H : ℝ) ≤
        (((4 * n ^ 2 : ℕ) : ℝ) + 1) * (1 + Real.log (H : ℝ)) := by
      have hc : (0 : ℝ) ≤ ((4 * n ^ 2 : ℕ) : ℝ) := by positivity
      nlinarith [hlogZ, hlogH0]
    have hpow' : (1 + Real.log ((H : ℝ) ^ 1)) ^ (2 * 2 ^ ((n + 1) ^ 4)) ≤
        (H : ℝ) ^ ((1 : ℝ) / (4 * n)) := hpow
    rw [pow_one] at hpow'
    calc (1 + Real.log (caseICap n H : ℝ)) ^ (2 * 2 ^ ((n + 1) ^ 4))
        ≤ ((((4 * n ^ 2 : ℕ) : ℝ) + 1) * (1 + Real.log (H : ℝ))) ^
            (2 * 2 ^ ((n + 1) ^ 4)) :=
          pow_le_pow_left₀ (by positivity) hstep _
      _ = (((4 * n ^ 2 : ℕ) : ℝ) + 1) ^ (2 * 2 ^ ((n + 1) ^ 4)) *
            (1 + Real.log (H : ℝ)) ^ (2 * 2 ^ ((n + 1) ^ 4)) := mul_pow _ _ _
      _ ≤ (H : ℝ) ^ ((1 : ℝ) / (4 * n)) * (H : ℝ) ^ ((1 : ℝ) / (4 * n)) :=
          mul_le_mul hconst hpow' (by positivity) (by positivity)
      _ = (H : ℝ) ^ ((1 : ℝ) / (2 * n)) := by
          rw [← Real.rpow_add hHpos]
          congr 1
          field_simp
          ring
  -- (C) the threshold lower bound
  have hY : ∀ᶠ H : ℕ in atTop,
      (H : ℝ) ^ (1 + 1 / (2 * (n : ℝ))) / Real.sqrt (2 * (S : ℝ)) ≤
        (caseIThr n H : ℝ) ^ ((1 : ℝ) / 2) := by
    have hbig : ∀ᶠ H : ℕ in atTop,
        (2 : ℝ) * (S : ℝ) ≤ (H : ℝ) ^ (2 + 1 / (n : ℝ)) :=
      Commons.Analysis.ExpLog.eventually_natCast_rpow_atTop_ge _ _ (by positivity)
    filter_upwards [hbig] with H hbig
    have hSpos' : (0 : ℝ) < (smallConst n : ℝ) := by rw [← hS_def]; exact hSpos
    have hfloor : ((H : ℝ) ^ (2 + 1 / (n : ℝ))) / (smallConst n : ℝ) - 1 ≤
        (caseIThr n H : ℝ) := by
      have h := Nat.lt_floor_add_one (((H : ℝ) ^ (2 + 1 / (n : ℝ))) / (smallConst n : ℝ))
      simp only [caseIThr]
      linarith
    have hkey : (H : ℝ) ^ (2 + 1 / (n : ℝ)) ≤ 2 * (S : ℝ) * (caseIThr n H : ℝ) := by
      have h1 : (2 : ℝ) * (S : ℝ) * (((H : ℝ) ^ (2 + 1 / (n : ℝ))) / (S : ℝ) - 1) ≤
          2 * (S : ℝ) * (caseIThr n H : ℝ) :=
        mul_le_mul_of_nonneg_left hfloor (by positivity)
      have hx : (2 : ℝ) * (S : ℝ) * (((H : ℝ) ^ (2 + 1 / (n : ℝ))) / (S : ℝ)) =
          2 * ((H : ℝ) ^ (2 + 1 / (n : ℝ))) := by
        field_simp
      have h2 : (H : ℝ) ^ (2 + 1 / (n : ℝ)) ≤
          2 * (S : ℝ) * (((H : ℝ) ^ (2 + 1 / (n : ℝ))) / (S : ℝ) - 1) := by
        rw [mul_sub, hx, mul_one]
        linarith
      linarith
    have hsq : ((H : ℝ) ^ (1 + 1 / (2 * (n : ℝ)))) ^ 2 ≤
        (Real.sqrt (2 * (S : ℝ)) * Real.sqrt (caseIThr n H : ℝ)) ^ 2 := by
      have h1 : ((H : ℝ) ^ (1 + 1 / (2 * (n : ℝ)))) ^ 2 = (H : ℝ) ^ (2 + 1 / (n : ℝ)) := by
        rw [← Real.rpow_natCast ((H : ℝ) ^ (1 + 1 / (2 * (n : ℝ)))) 2,
          ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ (H : ℝ))]
        congr 1
        push_cast
        field_simp
      have h2 : (Real.sqrt (2 * (S : ℝ)) * Real.sqrt (caseIThr n H : ℝ)) ^ 2 =
          2 * (S : ℝ) * (caseIThr n H : ℝ) := by
        rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 * (S : ℝ)),
          Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (caseIThr n H : ℝ))]
      rw [h1, h2]
      exact hkey
    have hmain := Real.sqrt_le_sqrt hsq
    rw [Real.sqrt_sq (Real.rpow_nonneg (Nat.cast_nonneg H) _),
      Real.sqrt_sq (by positivity : (0 : ℝ) ≤ Real.sqrt (2 * (S : ℝ)) * Real.sqrt (caseIThr n H : ℝ))] at hmain
    have hsqrt : (caseIThr n H : ℝ) ^ ((1 : ℝ) / 2) = Real.sqrt (caseIThr n H : ℝ) :=
      (Real.sqrt_eq_rpow _).symm
    rw [hsqrt, div_le_iff₀ (Real.sqrt_pos.mpr (by positivity))]
    simpa [mul_comm] using hmain
  -- (D) assembly
  refine ⟨(4 : ℝ) ^ n * Real.sqrt (2 * (S : ℝ)), ?_⟩
  filter_upwards [hthr, hlog, hY, eventually_ge_atTop (1 : ℕ)] with H hthr hlog hY hH1
  have hHpos : (0 : ℝ) < (H : ℝ) := by exact_mod_cast (by omega : 0 < H)
  have h1 := CaseIDirectBox_ncard_le_sum n H hn (by omega : 1 ≤ H)
  have h2 := caseIIndex_sum_le_tail n H hn (by omega : 1 ≤ H) hthr.1 hthr.2
  have h3 : ((CaseIDirectBox n H).ncard : ℝ) ≤
      (4 : ℝ) ^ n * (H : ℝ) ^ n *
        ((1 + Real.log (caseICap n H : ℝ)) ^ (2 * 2 ^ ((n + 1) ^ 4)) /
          (caseIThr n H : ℝ) ^ ((1 : ℝ) / 2)) := le_trans h1 h2
  have hbr : (1 + Real.log (caseICap n H : ℝ)) ^ (2 * 2 ^ ((n + 1) ^ 4)) /
        (caseIThr n H : ℝ) ^ ((1 : ℝ) / 2) ≤
      (H : ℝ) ^ ((1 : ℝ) / (2 * n)) /
        ((H : ℝ) ^ (1 + 1 / (2 * (n : ℝ))) / Real.sqrt (2 * (S : ℝ))) :=
    div_le_div₀ (by positivity) hlog (div_pos (by positivity) (by positivity)) hY
  have hsplit : (H : ℝ) ^ (1 + 1 / (2 * (n : ℝ))) =
      (H : ℝ) * (H : ℝ) ^ ((1 : ℝ) / (2 * n)) := by
    rw [Real.rpow_add hHpos, Real.rpow_one]
  have heq : (H : ℝ) ^ ((1 : ℝ) / (2 * n)) /
        ((H : ℝ) ^ (1 + 1 / (2 * (n : ℝ))) / Real.sqrt (2 * (S : ℝ))) =
      Real.sqrt (2 * (S : ℝ)) / (H : ℝ) := by
    rw [hsplit]
    have hHa : (H : ℝ) ^ ((1 : ℝ) / (2 * n)) ≠ 0 :=
      ne_of_gt (Real.rpow_pos_of_pos hHpos _)
    have hs : Real.sqrt (2 * (S : ℝ)) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.mpr (by positivity))
    field_simp
  have hdiv : (H : ℝ) ^ n / (H : ℝ) = (H : ℝ) ^ (n - 1) := by
    have := pow_sub₀ (H : ℝ) hHpos.ne' (show 1 ≤ n by omega)
    rw [pow_one] at this
    exact this.symm
  have hbr' : (1 + Real.log (caseICap n H : ℝ)) ^ (2 * 2 ^ ((n + 1) ^ 4)) /
        (caseIThr n H : ℝ) ^ ((1 : ℝ) / 2) ≤ Real.sqrt (2 * (S : ℝ)) / (H : ℝ) :=
    le_trans hbr (le_of_eq heq)
  have hfinal : (4 : ℝ) ^ n * (H : ℝ) ^ n * (Real.sqrt (2 * (S : ℝ)) / (H : ℝ)) =
      (4 : ℝ) ^ n * Real.sqrt (2 * (S : ℝ)) * (H : ℝ) ^ (n - 1) := by
    rw [← hdiv]
    field_simp
  calc ((CaseIDirectBox n H).ncard : ℝ)
      ≤ (4 : ℝ) ^ n * (H : ℝ) ^ n *
          ((1 + Real.log (caseICap n H : ℝ)) ^ (2 * 2 ^ ((n + 1) ^ 4)) /
            (caseIThr n H : ℝ) ^ ((1 : ℝ) / 2)) := h3
    _ ≤ (4 : ℝ) ^ n * (H : ℝ) ^ n * (Real.sqrt (2 * (S : ℝ)) / (H : ℝ)) :=
        mul_le_mul_of_nonneg_left hbr' (by positivity)
    _ = (4 : ℝ) ^ n * Real.sqrt (2 * (S : ℝ)) * (H : ℝ) ^ (n - 1) := hfinal

/-- **The Case-I direct region as a set of integer polynomials**
(`CaseIDirectBox` is its box-level incarnation). -/
def CaseIDirect (n H : ℕ) : Set ℤ[X] :=
  {f | ∃ h : Irreducible (f.map φℚ),
      f ∈ Box n H ∧ Squarefull (fieldDiscExp f h) ∧ radical (fieldDiscExp f h) ≤ H ∧
      (H : ℝ) ^ (2 + 1 / (n : ℝ)) < (fieldDiscExp f h : ℝ)}

/-- `CaseIDirectBox` is the box-level incarnation of `CaseIDirect`. -/
theorem CaseIDirect_eq_image (n H : ℕ) :
    CaseIDirect n H = Subtype.val '' (CaseIDirectBox n H) := by
  ext f
  constructor
  · rintro ⟨h, hbox, h1, h2, h3⟩
    exact ⟨⟨f, hbox⟩, ⟨h, h1, h2, h3⟩, rfl⟩
  · rintro ⟨g, ⟨h, h1, h2, h3⟩, rfl⟩
    exact ⟨h, g.2, h1, h2, h3⟩

/-- The region count is the same at either level. -/
theorem CaseIDirect_ncard_eq (n H : ℕ) :
    (CaseIDirect n H).ncard = (CaseIDirectBox n H).ncard := by
  rw [CaseIDirect_eq_image n H]
  exact Set.ncard_image_of_injective _ Subtype.val_injective

/-- **Case I direct regime: `O(H^(n-1))`** (box level, real constant form). -/
theorem CaseIDirectBox_isBigO (n : ℕ) (hn : 3 ≤ n) :
    (fun H : ℕ => ((CaseIDirectBox n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) := by
  obtain ⟨C, hC⟩ := CaseIDirectBox_bound_real n hn
  set C' : ℕ := Nat.ceil C with hC'_def
  have hCC' : C ≤ (C' : ℝ) := Nat.le_ceil C
  have hle : ∀ᶠ H : ℕ in atTop, (CaseIDirectBox n H).ncard ≤ C' * H ^ (n - 1) := by
    filter_upwards [hC] with H hH
    have h1 : ((CaseIDirectBox n H).ncard : ℝ) ≤ (C' : ℝ) * (H : ℝ) ^ (n - 1) :=
      le_trans hH (mul_le_mul_of_nonneg_right hCC' (by positivity))
    exact_mod_cast h1
  exact (Commons.Analysis.Asymptotics.isBigO_of_eventually_le _ _ hle).trans
    (Commons.Analysis.Asymptotics.isBigO_of_natCast_le_mul_pow (n - 1) C'
      (fun H => C' * H ^ (n - 1)) (Eventually.of_forall (fun H => le_rfl)))

/-- **Case I direct regime: `O(H^(n-1))`** (polynomial level). -/
theorem CaseIDirect_isBigO (n : ℕ) (hn : 3 ≤ n) :
    (fun H : ℕ => ((CaseIDirect n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) := by
  have hle : ∀ᶠ H : ℕ in atTop,
      (CaseIDirect n H).ncard ≤ (CaseIDirectBox n H).ncard :=
    Eventually.of_forall (fun H => le_of_eq (CaseIDirect_ncard_eq n H))
  exact (Commons.Analysis.Asymptotics.isBigO_of_eventually_le _ _ hle).trans
    (CaseIDirectBox_isBigO n hn)

end
end Submission.Vdw
