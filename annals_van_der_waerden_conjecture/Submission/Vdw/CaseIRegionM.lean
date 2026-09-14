import Mathlib
import Submission.Vdw.CaseIRegion
import Submission.Commons.Analysis.ExpLog.eventually_one_add_log_pow_le_rpow
import Submission.Commons.Data.Nat.eventually_heightCap_le_pow
import Submission.Commons.Analysis.Asymptotics.isBigO_of_natCast_le_mul_pow
import Submission.Commons.Analysis.Asymptotics.isBigO_of_eventually_le

open Polynomial Asymptotics
open scoped BigOperators
open Filter

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-!
# Case I, direct regime, with the threshold exponent as a parameter

`CaseIRegion` proves that the direct-regime region `C_f ≤ H`, `D_f > H^(2+2δ)`
(`δ = 1/(2n)`) has `O(H^(n-1))` many members.  Here the same argument is re-run
with the threshold parameterised by a single integer `M`: the exponents
`2 + 1/n`, `1 + 1/(2n)`, `1/(4n)`, `1/(2n)` become `2 + 4/M`, `1 + 2/M`, `1/M`,
`2/M` — i.e. `δ = 2/M` — so that the region can be instantiated at the Weyl
threshold `δ = weylδ n = 2^{-n}/(2n)` (`M = 4n·2^n`).  Everything else (the
per-modulus sieve bound `CaseIExact.restrictedPerDiscriminant_exact_le`, the
squarefull tail `CaseITail.squarefull_tail_bound`, the height cap
`DiscriminantCap.fieldDisc_height_bound`, `smallConst`, `caseICap`, `sieveAt`)
is reused verbatim.

The only new side condition is `2 + 4/M < 2n − 1` (to see
`⌊H^{2+4/M}/S₀⌋ < Z` eventually), which holds for `M = 4n·2^n`, `n ≥ 3`.

Axioms: propext / Classical.choice / Quot.sound only.
-/

namespace Submission.Vdw

noncomputable section

/-- **The Case-I direct-regime counting threshold**
`Y = ⌊H^(2+2δ)/S₀(n)⌋`, `δ = 1/(2n)`. -/
def caseIThrM (n M H : ℕ) : ℕ :=
  Nat.floor (((H : ℝ) ^ ((2 : ℝ) + 4 / (M : ℝ))) / (smallConst n : ℝ))

/-- **The Case-I direct region (box level)**: monic irreducible degree-`n` box
polynomials with squarefull field discriminant `D_f`, ramified product
`C_f = radical D_f ≤ H`, and `D_f > H^(2+2δ)`. -/
def CaseIDirectBoxM (n M H : ℕ) : Set ↥(Box n H) :=
  {f | ∃ h : Irreducible (f.1.map φℚ),
      Squarefull (fieldDiscExp f.1 h) ∧ radical (fieldDiscExp f.1 h) ≤ H ∧
      (H : ℝ) ^ ((2 : ℝ) + 4 / (M : ℝ)) < (fieldDiscExp f.1 h : ℝ)}

/-- The index set of modulus values: `⌊H^(2+2δ)/S₀⌋ < d ≤ Z`, `d` squarefull,
all prime factors of `d` exceeding `n` (so `d` is its own large-prime part),
`radical d ≤ H` and every exponent `v_p(d) < n`.  These are exactly the
conditions satisfied by `d = discLargePart n D_f` for a member of the region. -/
def caseIIndexM (n M H : ℕ) : Finset ℕ :=
  ((Finset.Icc (caseIThrM n M H + 1) (caseICap n H)).filter Squarefull).filter
    (fun d => (∀ p ∈ d.primeFactors, n < p) ∧ radical d ≤ H ∧
      (∀ p ∈ d.primeFactors, d.factorization p < n))

/-- **Region membership**: every member of `CaseIDirectBox` satisfies the
restricted sieve conditions at the large-prime part `d = discLargePart n D_f`
of its own field discriminant, and `d` lies in the index set. -/
theorem CaseIDirectBoxM_subset_biUnion (n M H : ℕ) (hn : 3 ≤ n) (hM : 1 ≤ M) (hH : 1 ≤ H) :
    CaseIDirectBoxM n M H ⊆ {f : ↥(Box n H) | ∃ d ∈ caseIIndexM n M H, f ∈ sieveAt n H d} := by
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
  have hYd : caseIThrM n M H < d := by
    have hS0pos : (0 : ℝ) < (smallConst n : ℝ) := by exact_mod_cast smallConst_pos n
    have h1 : (caseIThrM n M H : ℝ) ≤ ((H : ℝ) ^ ((2 : ℝ) + 4 / (M : ℝ))) / (smallConst n : ℝ) := by
      simp only [caseIThrM]
      exact Nat.floor_le (by positivity)
    have h2 : ((H : ℝ) ^ ((2 : ℝ) + 4 / (M : ℝ))) / (smallConst n : ℝ) < (D : ℝ) / (smallConst n : ℝ) :=
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
  have hmem : d ∈ caseIIndexM n M H := by
    rw [caseIIndexM, Finset.mem_filter, Finset.mem_filter]
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
theorem CaseIDirectBoxM_ncard_le_sum (n M H : ℕ) (hn : 3 ≤ n) (hM : 1 ≤ M) (hH : 1 ≤ H) :
    ((CaseIDirectBoxM n M H).ncard : ℝ) ≤
      ∑ d ∈ caseIIndexM n M H,
        (4 : ℝ) ^ n * (2 : ℝ) ^ (((n + 1) ^ 4) * omega d) * (H : ℝ) ^ n / (d : ℝ) := by
  classical
  haveI : Finite ↥(Box n H) := box_finite n H
  have hfin : ({f : ↥(Box n H) | ∃ d ∈ caseIIndexM n M H, f ∈ sieveAt n H d}).Finite :=
    Set.toFinite _
  have h1 : (CaseIDirectBoxM n M H).ncard ≤
      ({f : ↥(Box n H) | ∃ d ∈ caseIIndexM n M H, f ∈ sieveAt n H d}).ncard :=
    Set.ncard_le_ncard (CaseIDirectBoxM_subset_biUnion n M H hn hM hH) hfin
  have h2 := ncard_biUnion_finset_le (caseIIndexM n M H) (sieveAt n H)
  have h3 : ∀ d ∈ caseIIndexM n M H, ((sieveAt n H d).ncard : ℝ) ≤
      (4 : ℝ) ^ n * (2 : ℝ) ^ (((n + 1) ^ 4) * omega d) * (H : ℝ) ^ n / (d : ℝ) := by
    intro d hd
    rw [caseIIndexM, Finset.mem_filter, Finset.mem_filter] at hd
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
  have hcast : ((CaseIDirectBoxM n M H).ncard : ℝ) ≤
      ((∑ d ∈ caseIIndexM n M H, (sieveAt n H d).ncard : ℕ) : ℝ) := by
    exact_mod_cast le_trans h1 h2
  calc ((CaseIDirectBoxM n M H).ncard : ℝ)
      ≤ ((∑ d ∈ caseIIndexM n M H, (sieveAt n H d).ncard : ℕ) : ℝ) := hcast
    _ = ∑ d ∈ caseIIndexM n M H, ((sieveAt n H d).ncard : ℝ) := by
        rw [Nat.cast_sum]
    _ ≤ ∑ d ∈ caseIIndexM n M H,
          ((4 : ℝ) ^ n * (2 : ℝ) ^ (((n + 1) ^ 4) * omega d) * (H : ℝ) ^ n / (d : ℝ)) :=
        Finset.sum_le_sum h3

/-- **The sum over the index set is bounded by the squarefull tail sum.**  The
two hypotheses `1 ≤ caseIThrM n M H < caseICap n H` (automatic eventually in `H`)
make the tail bound usable. -/
theorem caseIIndexM_sum_le_tail (n M H : ℕ) (hn : 3 ≤ n) (hM : 1 ≤ M) (hH : 1 ≤ H)
    (hY1 : 1 ≤ caseIThrM n M H) (hYT : caseIThrM n M H < caseICap n H) :
    ∑ d ∈ caseIIndexM n M H,
        (4 : ℝ) ^ n * (2 : ℝ) ^ (((n + 1) ^ 4) * omega d) * (H : ℝ) ^ n / (d : ℝ) ≤
      (4 : ℝ) ^ n * (H : ℝ) ^ n *
        ((1 + Real.log (caseICap n H : ℝ)) ^ (2 * 2 ^ ((n + 1) ^ 4)) /
          (caseIThrM n M H : ℝ) ^ ((1 : ℝ) / 2)) := by
  classical
  set c : ℕ := 2 ^ ((n + 1) ^ 4) with hc_def
  have hc1 : 1 ≤ c := Nat.one_le_two_pow
  have hcR : (c : ℝ) = (2 : ℝ) ^ ((n + 1) ^ 4) := by
    rw [hc_def]; push_cast; ring
  have htail := squarefull_tail_bound c hc1 ((1 : ℝ) / 2) (by norm_num) le_rfl
    (caseIThrM n M H) (caseICap n H) hY1 hYT
  have hsub : caseIIndexM n M H ⊆ Finset.Icc (caseIThrM n M H + 1) (caseICap n H) := by
    intro d hd
    rw [caseIIndexM, Finset.mem_filter, Finset.mem_filter] at hd
    exact hd.1.1
  have hsqmem : ∀ d ∈ caseIIndexM n M H, Squarefull d := by
    intro d hd
    rw [caseIIndexM, Finset.mem_filter, Finset.mem_filter] at hd
    exact hd.1.2
  have hsum1 : ∑ d ∈ caseIIndexM n M H, (c : ℝ) ^ omega d / (d : ℝ) ≤
      ∑ d ∈ Finset.Icc (caseIThrM n M H + 1) (caseICap n H),
        (if Squarefull d then (c : ℝ) ^ omega d / (d : ℝ) else 0) := by
    calc ∑ d ∈ caseIIndexM n M H, (c : ℝ) ^ omega d / (d : ℝ)
        = ∑ d ∈ caseIIndexM n M H,
            (if Squarefull d then (c : ℝ) ^ omega d / (d : ℝ) else 0) := by
          refine Finset.sum_congr rfl (fun d hd => ?_)
          simp [hsqmem d hd]
      _ ≤ ∑ d ∈ Finset.Icc (caseIThrM n M H + 1) (caseICap n H),
            (if Squarefull d then (c : ℝ) ^ omega d / (d : ℝ) else 0) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg hsub (fun d hdt hds => ?_)
          by_cases hsq : Squarefull d
          · simp only [hsq, if_true]
            have hd0 : (0 : ℝ) < (d : ℝ) := by
              have := (Finset.mem_Icc.mp hdt).1
              exact_mod_cast (by omega : 0 < d)
            positivity
          · simp [hsq]
  have hfactor : ∑ d ∈ caseIIndexM n M H,
        (4 : ℝ) ^ n * (2 : ℝ) ^ (((n + 1) ^ 4) * omega d) * (H : ℝ) ^ n / (d : ℝ) =
      ((4 : ℝ) ^ n * (H : ℝ) ^ n) *
        (∑ d ∈ caseIIndexM n M H, (c : ℝ) ^ omega d / (d : ℝ)) := by
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
theorem CaseIDirectBoxM_bound_real (n M : ℕ) (hn : 3 ≤ n) (hM : 1 ≤ M)
    (hMn : (2 : ℝ) + 4 / (M : ℝ) < 2 * (n : ℝ) - 1) :
    ∃ C : ℝ, ∀ᶠ H : ℕ in atTop,
      ((CaseIDirectBoxM n M H).ncard : ℝ) ≤ C * (H : ℝ) ^ (n - 1) := by
  set S : ℕ := smallConst n with hS_def
  have hSpos : (0 : ℝ) < (S : ℝ) := by
    rw [hS_def]; exact_mod_cast smallConst_pos n
  have hnR : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  -- (A) the threshold lies in the admissible range
  have hthr : ∀ᶠ H : ℕ in atTop, 1 ≤ caseIThrM n M H ∧ caseIThrM n M H < caseICap n H := by
    have hbig : ∀ᶠ H : ℕ in atTop, (2 : ℝ) * (S : ℝ) ≤ (H : ℝ) ^ ((2 : ℝ) + 4 / (M : ℝ)) :=
      Commons.Analysis.ExpLog.eventually_natCast_rpow_atTop_ge _ _ (by positivity)
    have hcmp : ∀ᶠ H : ℕ in atTop, (H : ℝ) ^ ((2 : ℝ) + 4 / (M : ℝ)) < (caseICap n H : ℝ) := by
      have hlt : ∀ᶠ H : ℕ in atTop,
          (H : ℝ) ^ ((2 : ℝ) + 4 / (M : ℝ)) < (H : ℝ) ^ (((2 * n - 1 : ℕ)) : ℝ) := by
        filter_upwards [eventually_ge_atTop (2 : ℕ)] with H hH
        have hH1 : (1 : ℝ) < (H : ℝ) := by exact_mod_cast (by omega : 1 < H)
        refine Real.rpow_lt_rpow_of_exponent_lt hH1 ?_
        have h2n : (((2 * n - 1 : ℕ)) : ℝ) = 2 * (n : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega : 1 ≤ 2 * n)]
          push_cast
          ring
        rw [h2n]
        exact hMn
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
    · simp only [caseIThrM]
      refine Nat.le_floor ?_
      rw [le_div_iff₀ hSpos']
      linarith
    · simp only [caseIThrM]
      refine (Nat.floor_lt (div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg H) _)
        (le_of_lt hSpos'))).mpr ?_
      have hS1 : (1 : ℝ) ≤ (smallConst n : ℝ) := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (smallConst_pos n).ne')
      have hx : (0 : ℝ) ≤ (H : ℝ) ^ ((2 : ℝ) + 4 / (M : ℝ)) :=
        Real.rpow_nonneg (Nat.cast_nonneg H) _
      have hle : (H : ℝ) ^ ((2 : ℝ) + 4 / (M : ℝ)) / (smallConst n : ℝ) ≤
          (H : ℝ) ^ ((2 : ℝ) + 4 / (M : ℝ)) := by
        rw [div_le_iff₀ hSpos']
        simpa using mul_le_mul_of_nonneg_left hS1 hx
      linarith
  -- (B) log absorption
  have hlog : ∀ᶠ H : ℕ in atTop,
      (1 + Real.log (caseICap n H : ℝ)) ^ (2 * 2 ^ ((n + 1) ^ 4)) ≤
        (H : ℝ) ^ ((2 : ℝ) / (M : ℝ)) := by
    have hMinv : (0 : ℝ) < (1 : ℝ) / (M : ℝ) := by
      have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
      positivity
    have hpow := Commons.Analysis.ExpLog.eventually_one_add_log_pow_le_rpow
      (2 * 2 ^ ((n + 1) ^ 4)) 1 ((1 : ℝ) / (M : ℝ)) hMinv
    have hconst : ∀ᶠ H : ℕ in atTop,
        (((4 * n ^ 2 : ℕ) : ℝ) + 1) ^ (2 * 2 ^ ((n + 1) ^ 4)) ≤
          (H : ℝ) ^ ((1 : ℝ) / (M : ℝ)) :=
      Commons.Analysis.ExpLog.eventually_natCast_rpow_atTop_ge _ _ hMinv
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
        (H : ℝ) ^ ((1 : ℝ) / (M : ℝ)) := hpow
    rw [pow_one] at hpow'
    calc (1 + Real.log (caseICap n H : ℝ)) ^ (2 * 2 ^ ((n + 1) ^ 4))
        ≤ ((((4 * n ^ 2 : ℕ) : ℝ) + 1) * (1 + Real.log (H : ℝ))) ^
            (2 * 2 ^ ((n + 1) ^ 4)) :=
          pow_le_pow_left₀ (by positivity) hstep _
      _ = (((4 * n ^ 2 : ℕ) : ℝ) + 1) ^ (2 * 2 ^ ((n + 1) ^ 4)) *
            (1 + Real.log (H : ℝ)) ^ (2 * 2 ^ ((n + 1) ^ 4)) := mul_pow _ _ _
      _ ≤ (H : ℝ) ^ ((1 : ℝ) / (M : ℝ)) * (H : ℝ) ^ ((1 : ℝ) / (M : ℝ)) :=
          mul_le_mul hconst hpow' (by positivity) (by positivity)
      _ = (H : ℝ) ^ ((2 : ℝ) / (M : ℝ)) := by
          rw [← Real.rpow_add hHpos]
          congr 1
          field_simp
          ring
  -- (C) the threshold lower bound
  have hY : ∀ᶠ H : ℕ in atTop,
      (H : ℝ) ^ ((1 : ℝ) + 2 / (M : ℝ)) / Real.sqrt (2 * (S : ℝ)) ≤
        (caseIThrM n M H : ℝ) ^ ((1 : ℝ) / 2) := by
    have hbig : ∀ᶠ H : ℕ in atTop,
        (2 : ℝ) * (S : ℝ) ≤ (H : ℝ) ^ ((2 : ℝ) + 4 / (M : ℝ)) :=
      Commons.Analysis.ExpLog.eventually_natCast_rpow_atTop_ge _ _ (by positivity)
    filter_upwards [hbig] with H hbig
    have hSpos' : (0 : ℝ) < (smallConst n : ℝ) := by rw [← hS_def]; exact hSpos
    have hfloor : ((H : ℝ) ^ ((2 : ℝ) + 4 / (M : ℝ))) / (smallConst n : ℝ) - 1 ≤
        (caseIThrM n M H : ℝ) := by
      have h := Nat.lt_floor_add_one (((H : ℝ) ^ ((2 : ℝ) + 4 / (M : ℝ))) / (smallConst n : ℝ))
      simp only [caseIThrM]
      linarith
    have hkey : (H : ℝ) ^ ((2 : ℝ) + 4 / (M : ℝ)) ≤ 2 * (S : ℝ) * (caseIThrM n M H : ℝ) := by
      have h1 : (2 : ℝ) * (S : ℝ) * (((H : ℝ) ^ ((2 : ℝ) + 4 / (M : ℝ))) / (S : ℝ) - 1) ≤
          2 * (S : ℝ) * (caseIThrM n M H : ℝ) :=
        mul_le_mul_of_nonneg_left hfloor (by positivity)
      have hx : (2 : ℝ) * (S : ℝ) * (((H : ℝ) ^ ((2 : ℝ) + 4 / (M : ℝ))) / (S : ℝ)) =
          2 * ((H : ℝ) ^ ((2 : ℝ) + 4 / (M : ℝ))) := by
        field_simp
      have h2 : (H : ℝ) ^ ((2 : ℝ) + 4 / (M : ℝ)) ≤
          2 * (S : ℝ) * (((H : ℝ) ^ ((2 : ℝ) + 4 / (M : ℝ))) / (S : ℝ) - 1) := by
        rw [mul_sub, hx, mul_one]
        linarith
      linarith
    have hsq : ((H : ℝ) ^ ((1 : ℝ) + 2 / (M : ℝ))) ^ 2 ≤
        (Real.sqrt (2 * (S : ℝ)) * Real.sqrt (caseIThrM n M H : ℝ)) ^ 2 := by
      have h1 : ((H : ℝ) ^ ((1 : ℝ) + 2 / (M : ℝ))) ^ 2 = (H : ℝ) ^ ((2 : ℝ) + 4 / (M : ℝ)) := by
        rw [← Real.rpow_natCast ((H : ℝ) ^ ((1 : ℝ) + 2 / (M : ℝ))) 2,
          ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ (H : ℝ))]
        congr 1
        push_cast
        field_simp
        ring
      have h2 : (Real.sqrt (2 * (S : ℝ)) * Real.sqrt (caseIThrM n M H : ℝ)) ^ 2 =
          2 * (S : ℝ) * (caseIThrM n M H : ℝ) := by
        rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 * (S : ℝ)),
          Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (caseIThrM n M H : ℝ))]
      rw [h1, h2]
      exact hkey
    have hmain := Real.sqrt_le_sqrt hsq
    rw [Real.sqrt_sq (Real.rpow_nonneg (Nat.cast_nonneg H) _),
      Real.sqrt_sq (by positivity : (0 : ℝ) ≤ Real.sqrt (2 * (S : ℝ)) * Real.sqrt (caseIThrM n M H : ℝ))] at hmain
    have hsqrt : (caseIThrM n M H : ℝ) ^ ((1 : ℝ) / 2) = Real.sqrt (caseIThrM n M H : ℝ) :=
      (Real.sqrt_eq_rpow _).symm
    rw [hsqrt, div_le_iff₀ (Real.sqrt_pos.mpr (by positivity))]
    simpa [mul_comm] using hmain
  -- (D) assembly
  refine ⟨(4 : ℝ) ^ n * Real.sqrt (2 * (S : ℝ)), ?_⟩
  filter_upwards [hthr, hlog, hY, eventually_ge_atTop (1 : ℕ)] with H hthr hlog hY hH1
  have hHpos : (0 : ℝ) < (H : ℝ) := by exact_mod_cast (by omega : 0 < H)
  have h1 := CaseIDirectBoxM_ncard_le_sum n M H hn hM (by omega : 1 ≤ H)
  have h2 := caseIIndexM_sum_le_tail n M H hn hM (by omega : 1 ≤ H) hthr.1 hthr.2
  have h3 : ((CaseIDirectBoxM n M H).ncard : ℝ) ≤
      (4 : ℝ) ^ n * (H : ℝ) ^ n *
        ((1 + Real.log (caseICap n H : ℝ)) ^ (2 * 2 ^ ((n + 1) ^ 4)) /
          (caseIThrM n M H : ℝ) ^ ((1 : ℝ) / 2)) := le_trans h1 h2
  have hbr : (1 + Real.log (caseICap n H : ℝ)) ^ (2 * 2 ^ ((n + 1) ^ 4)) /
        (caseIThrM n M H : ℝ) ^ ((1 : ℝ) / 2) ≤
      (H : ℝ) ^ ((2 : ℝ) / (M : ℝ)) /
        ((H : ℝ) ^ ((1 : ℝ) + 2 / (M : ℝ)) / Real.sqrt (2 * (S : ℝ))) :=
    div_le_div₀ (by positivity) hlog (div_pos (by positivity) (by positivity)) hY
  have hsplit : (H : ℝ) ^ ((1 : ℝ) + 2 / (M : ℝ)) =
      (H : ℝ) * (H : ℝ) ^ ((2 : ℝ) / (M : ℝ)) := by
    rw [Real.rpow_add hHpos, Real.rpow_one]
  have heq : (H : ℝ) ^ ((2 : ℝ) / (M : ℝ)) /
        ((H : ℝ) ^ ((1 : ℝ) + 2 / (M : ℝ)) / Real.sqrt (2 * (S : ℝ))) =
      Real.sqrt (2 * (S : ℝ)) / (H : ℝ) := by
    rw [hsplit]
    have hHa : (H : ℝ) ^ ((2 : ℝ) / (M : ℝ)) ≠ 0 :=
      ne_of_gt (Real.rpow_pos_of_pos hHpos _)
    have hs : Real.sqrt (2 * (S : ℝ)) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.mpr (by positivity))
    field_simp
  have hdiv : (H : ℝ) ^ n / (H : ℝ) = (H : ℝ) ^ (n - 1) := by
    have := pow_sub₀ (H : ℝ) hHpos.ne' (show 1 ≤ n by omega)
    rw [pow_one] at this
    exact this.symm
  have hbr' : (1 + Real.log (caseICap n H : ℝ)) ^ (2 * 2 ^ ((n + 1) ^ 4)) /
        (caseIThrM n M H : ℝ) ^ ((1 : ℝ) / 2) ≤ Real.sqrt (2 * (S : ℝ)) / (H : ℝ) :=
    le_trans hbr (le_of_eq heq)
  have hfinal : (4 : ℝ) ^ n * (H : ℝ) ^ n * (Real.sqrt (2 * (S : ℝ)) / (H : ℝ)) =
      (4 : ℝ) ^ n * Real.sqrt (2 * (S : ℝ)) * (H : ℝ) ^ (n - 1) := by
    rw [← hdiv]
    field_simp
  calc ((CaseIDirectBoxM n M H).ncard : ℝ)
      ≤ (4 : ℝ) ^ n * (H : ℝ) ^ n *
          ((1 + Real.log (caseICap n H : ℝ)) ^ (2 * 2 ^ ((n + 1) ^ 4)) /
            (caseIThrM n M H : ℝ) ^ ((1 : ℝ) / 2)) := h3
    _ ≤ (4 : ℝ) ^ n * (H : ℝ) ^ n * (Real.sqrt (2 * (S : ℝ)) / (H : ℝ)) :=
        mul_le_mul_of_nonneg_left hbr' (by positivity)
    _ = (4 : ℝ) ^ n * Real.sqrt (2 * (S : ℝ)) * (H : ℝ) ^ (n - 1) := hfinal

/-- **The Case-I direct region as a set of integer polynomials**
(`CaseIDirectBox` is its box-level incarnation). -/
def CaseIDirectM (n M H : ℕ) : Set ℤ[X] :=
  {f | ∃ h : Irreducible (f.map φℚ),
      f ∈ Box n H ∧ Squarefull (fieldDiscExp f h) ∧ radical (fieldDiscExp f h) ≤ H ∧
      (H : ℝ) ^ ((2 : ℝ) + 4 / (M : ℝ)) < (fieldDiscExp f h : ℝ)}

/-- `CaseIDirectBox` is the box-level incarnation of `CaseIDirect`. -/
theorem CaseIDirectM_eq_image (n M H : ℕ) :
    CaseIDirectM n M H = Subtype.val '' (CaseIDirectBoxM n M H) := by
  ext f
  constructor
  · rintro ⟨h, hbox, h1, h2, h3⟩
    exact ⟨⟨f, hbox⟩, ⟨h, h1, h2, h3⟩, rfl⟩
  · rintro ⟨g, ⟨h, h1, h2, h3⟩, rfl⟩
    exact ⟨h, g.2, h1, h2, h3⟩

/-- The region count is the same at either level. -/
theorem CaseIDirectM_ncard_eq (n M H : ℕ) :
    (CaseIDirectM n M H).ncard = (CaseIDirectBoxM n M H).ncard := by
  rw [CaseIDirectM_eq_image n M H]
  exact Set.ncard_image_of_injective _ Subtype.val_injective

/-- **Case I direct regime: `O(H^(n-1))`** (box level, real constant form). -/
theorem CaseIDirectBoxM_isBigO (n M : ℕ) (hn : 3 ≤ n) (hM : 1 ≤ M)
    (hMn : (2 : ℝ) + 4 / (M : ℝ) < 2 * (n : ℝ) - 1) :
    (fun H : ℕ => ((CaseIDirectBoxM n M H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) := by
  obtain ⟨C, hC⟩ := CaseIDirectBoxM_bound_real n M hn hM hMn
  set C' : ℕ := Nat.ceil C with hC'_def
  have hCC' : C ≤ (C' : ℝ) := Nat.le_ceil C
  have hle : ∀ᶠ H : ℕ in atTop, (CaseIDirectBoxM n M H).ncard ≤ C' * H ^ (n - 1) := by
    filter_upwards [hC] with H hH
    have h1 : ((CaseIDirectBoxM n M H).ncard : ℝ) ≤ (C' : ℝ) * (H : ℝ) ^ (n - 1) :=
      le_trans hH (mul_le_mul_of_nonneg_right hCC' (by positivity))
    exact_mod_cast h1
  exact (Commons.Analysis.Asymptotics.isBigO_of_eventually_le _ _ hle).trans
    (Commons.Analysis.Asymptotics.isBigO_of_natCast_le_mul_pow (n - 1) C'
      (fun H => C' * H ^ (n - 1)) (Eventually.of_forall (fun H => le_rfl)))

/-- **Case I direct regime: `O(H^(n-1))`** (polynomial level). -/
theorem CaseIDirectM_isBigO (n M : ℕ) (hn : 3 ≤ n) (hM : 1 ≤ M)
    (hMn : (2 : ℝ) + 4 / (M : ℝ) < 2 * (n : ℝ) - 1) :
    (fun H : ℕ => ((CaseIDirectM n M H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) := by
  have hle : ∀ᶠ H : ℕ in atTop,
      (CaseIDirectM n M H).ncard ≤ (CaseIDirectBoxM n M H).ncard :=
    Eventually.of_forall (fun H => le_of_eq (CaseIDirectM_ncard_eq n M H))
  exact (Commons.Analysis.Asymptotics.isBigO_of_eventually_le _ _ hle).trans
    (CaseIDirectBoxM_isBigO n M hn hM hMn)

end
end Submission.Vdw
