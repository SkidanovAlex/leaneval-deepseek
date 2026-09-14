import Mathlib
import Submission.Vdw.CaseIRegion
import Submission.Commons.Analysis.ExpLog.eventually_one_add_log_pow_le_rpow
import Submission.Commons.Data.Nat.eventually_heightCap_le_pow

open Polynomial Asymptotics
open scoped BigOperators
open Filter

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-!
# Case I (full range `C ≤ H^(1+δ)`): the reduction to a single per-discriminant
Fourier bound

The paper's Case I counts the polynomials with `C_f ≤ H^(1+δ)`,
`D_f > H^(2+2δ)` via the per-discriminant estimate

    #{f ∈ Box n H : Disc(K_f) = D} = O(c^ω(D)·H^n/D)      (`C ≤ H^(1+δ)`)

obtained for `C < H` by the elementary congruence/sieve argument (the
project's `CaseIRegion`, unconditional) and for the full range `C < H^(1+δ)`
by Fourier analysis (`§4`, Corollary 33 — the deep input).

This module isolates exactly that input: `PerDDiscBound n c` is the per-`D`
estimate with all constants explicit, and

* `CaseIFull_ncard_le_sum` — `#CaseIFull ≤ Σ_{D} c^ω(D)·H^n/D` over the
  squarefull `D ∈ (⌊H^(2+2δ)⌋, Z]` (via `ncard_biUnion_finset_le` and the
  per-`D` hypothesis);
* `CaseIFull_bound_real` — `∃ C, ∀ᶠ H, #CaseIFull ≤ C·H^(n−1)`
  (squarefull tail bound + log absorption, exactly as in `CaseIRegion`);
* `CaseIFull_isBigO` — the Case-I region is `O(H^(n-1))` GIVEN the per-`D`
  Fourier bound.

Axioms of every statement: propext / Classical.choice / Quot.sound only.
-/

namespace Submission.Vdw

noncomputable section

/-- **The Case-I direct-regime counting threshold** `Y = ⌊H^(2+2δ)⌋`. -/
def caseIThrF (n H : ℕ) : ℕ := Nat.floor ((H : ℝ) ^ (2 + 1 / (n : ℝ)))

open Classical in
/-- **The per-discriminant Fourier bound with explicit constant** (paper §4,
Corollary 33, in the form used in Case I): the number of box polynomials with
field discriminant exactly `D` is at most `c^ω(D)·H^n/D`, for a nonzero
squarefull `D` in the Case-I range — `radical D ≤ H^(1+δ)`, all prime divisors
`> n` dividing `D` with exponent `< n` (which holds automatically for
`D = D_f`, `f` in the box, by Lemma 24 field and `index ≤ n-1`), and
`D > H^(2+2δ)` (so that the estimate is never weaker than the trivial bound
`1`). -/
def PerDDiscBound (n c : ℕ) : Prop :=
  ∀ H D : ℕ, D ≠ 0 → Squarefull D →
    (radical D : ℝ) ≤ (H : ℝ) ^ (1 + 1 / (2 * (n : ℝ))) →
    (∀ p ∈ D.primeFactors, n < p → D.factorization p < n) →
    (H : ℝ) ^ (2 + 1 / (n : ℝ)) < (D : ℝ) →
    ((Nat.card {f : ↥(Box n H) // ∃ h : Irreducible (f.1.map φℚ),
        fieldDiscExp f.1 h = D} : ℕ) : ℝ) ≤ (c : ℝ) ^ omega D * (H : ℝ) ^ n / (D : ℝ)

/-- **The Case-I region** (box level): squarefull field discriminant with
`C_f ≤ H^(1+δ)` and `D_f > H^(2+2δ)`. -/
def CaseIFullBox (n H : ℕ) : Set ↥(Box n H) :=
  {f | ∃ h : Irreducible (f.1.map φℚ),
      Squarefull (fieldDiscExp f.1 h) ∧
      (radical (fieldDiscExp f.1 h) : ℝ) ≤ (H : ℝ) ^ (1 + 1 / (2 * (n : ℝ))) ∧
      (H : ℝ) ^ (2 + 1 / (n : ℝ)) < (fieldDiscExp f.1 h : ℝ)}

/-- The polynomial-level Case-I region. -/
def CaseIFull (n H : ℕ) : Set ℤ[X] :=
  {f | ∃ h : Irreducible (f.map φℚ),
      f ∈ Box n H ∧ Squarefull (fieldDiscExp f h) ∧
      (radical (fieldDiscExp f h) : ℝ) ≤ (H : ℝ) ^ (1 + 1 / (2 * (n : ℝ))) ∧
      (H : ℝ) ^ (2 + 1 / (n : ℝ)) < (fieldDiscExp f h : ℝ)}

open Classical in
/-- The admissible discriminant values: `⌊H^(2+2δ)⌋ < D ≤ Z`, `D` squarefull,
`radical D ≤ H^(1+δ)`, and all prime divisors of `D` exceeding `n` occurring
with exponent `< n` (the side conditions of `PerDDiscBound` that hold
automatically for `D = D_f` of a region member). -/
def caseIFullIndex (n H : ℕ) : Finset ℕ :=
  ((Finset.Icc (caseIThrF n H + 1) (caseICap n H)).filter Squarefull).filter
    (fun D => (radical D : ℝ) ≤ (H : ℝ) ^ (1 + 1 / (2 * (n : ℝ))) ∧
      (∀ p ∈ D.primeFactors, n < p → D.factorization p < n))

/-- The per-discriminant fiber (box level). -/
def fiberAt (n H D : ℕ) : Set ↥(Box n H) :=
  {f | ∃ h : Irreducible (f.1.map φℚ), fieldDiscExp f.1 h = D}

/-- **Region membership**: every member of `CaseIFullBox` has its field
discriminant in the index set. -/
theorem CaseIFullBox_subset_biUnion (n H : ℕ) (hn : 3 ≤ n) (hH : 1 ≤ H) :
    CaseIFullBox n H ⊆
      {f : ↥(Box n H) | ∃ D ∈ caseIFullIndex n H, f ∈ fiberAt n H D} := by
  classical
  intro f hf
  obtain ⟨h, hsq, hC, hlarge⟩ := hf
  haveI : Fact (Irreducible (f.1.map φℚ)) := ⟨h⟩
  have hmon : f.1.Monic := f.2.1
  have hdeg : f.1.natDegree = n := Polynomial.natDegree_eq_of_degree_eq_some f.2.2.1
  refine ⟨fieldDiscExp f.1 h, ?_, h, rfl⟩
  have hZ : fieldDiscExp f.1 h ≤ caseICap n H :=
    fieldDisc_height_bound f.1 hmon n H hdeg (fun k hk => f.2.2.2 k hk)
  have hY : caseIThrF n H < fieldDiscExp f.1 h := by
    have h1 : (caseIThrF n H : ℝ) ≤ (H : ℝ) ^ (2 + 1 / (n : ℝ)) := by
      simp only [caseIThrF]
      exact Nat.floor_le (by positivity)
    have := lt_of_le_of_lt h1 hlarge
    exact_mod_cast this
  have hfac : ∀ p ∈ (fieldDiscExp f.1 h).primeFactors, n < p →
      (fieldDiscExp f.1 h).factorization p < n := by
    intro p hp hpgt
    have hpp : Nat.Prime p := (Nat.mem_primeFactors.mp hp).1
    haveI : Fact (Nat.Prime p) := ⟨hpp⟩
    have hdvd : p ∣ fieldDisc f.1 := by
      have := (Nat.mem_primeFactors.mp hp).2.1
      simpa [fieldDiscExp] using this
    have hlt := fieldDisc_factorization_lt_of_prime_gt n H (by omega) f.1 hmon hdeg f.2 hpgt hdvd
    simpa [fieldDiscExp] using hlt
  rw [caseIFullIndex, Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨⟨by omega, hZ⟩, hsq⟩, hC, hfac⟩

/-- Finiteness of the region. -/
theorem CaseIFullBox_finite (n H : ℕ) : (CaseIFullBox n H).Finite := Set.toFinite _

/-- **The region count is at most the per-discriminant sum.** -/
theorem CaseIFullBox_ncard_le_sum (n H c : ℕ) (hn : 3 ≤ n) (hH : 1 ≤ H)
    (hper : PerDDiscBound n c) :
    ((CaseIFullBox n H).ncard : ℝ) ≤
      ∑ D ∈ caseIFullIndex n H, (c : ℝ) ^ omega D * (H : ℝ) ^ n / (D : ℝ) := by
  classical
  haveI : Finite ↥(Box n H) := box_finite n H
  have hfin : ({f : ↥(Box n H) | ∃ D ∈ caseIFullIndex n H, f ∈ fiberAt n H D}).Finite :=
    Set.toFinite _
  have h1 : (CaseIFullBox n H).ncard ≤
      ({f : ↥(Box n H) | ∃ D ∈ caseIFullIndex n H, f ∈ fiberAt n H D}).ncard :=
    Set.ncard_le_ncard (CaseIFullBox_subset_biUnion n H hn hH) hfin
  have h2 := ncard_biUnion_finset_le (caseIFullIndex n H) (fiberAt n H)
  have h3 : ∀ D ∈ caseIFullIndex n H,
      ((fiberAt n H D).ncard : ℝ) ≤ (c : ℝ) ^ omega D * (H : ℝ) ^ n / (D : ℝ) := by
    intro D hD
    rw [caseIFullIndex, Finset.mem_filter, Finset.mem_filter] at hD
    obtain ⟨⟨hDIcc, hDsq⟩, hDrad, hDfac⟩ := hD
    have hD0 : D ≠ 0 := by
      have := (Finset.mem_Icc.mp hDIcc).1
      omega
    have hcard : (fiberAt n H D).ncard = Nat.card {f : ↥(Box n H) //
        ∃ h : Irreducible (f.1.map φℚ), fieldDiscExp f.1 h = D} :=
      (Nat.card_coe_set_eq _).symm
    rw [hcard]
    refine hper H D hD0 hDsq hDrad hDfac ?_
    have hDgt : caseIThrF n H < D := by
      have := (Finset.mem_Icc.mp hDIcc).1
      omega
    have h1 : (caseIThrF n H : ℝ) ≤ (H : ℝ) ^ (2 + 1 / (n : ℝ)) := by
      simp only [caseIThrF]
      exact Nat.floor_le (by positivity)
    have h2 : (H : ℝ) ^ (2 + 1 / (n : ℝ)) < (D : ℝ) := by
      have h3 : (H : ℝ) ^ (2 + 1 / (n : ℝ)) < (caseIThrF n H : ℝ) + 1 :=
        Nat.lt_floor_add_one _
      have h4 : (caseIThrF n H : ℝ) + 1 ≤ (D : ℝ) := by
        have : caseIThrF n H + 1 ≤ D := by omega
        exact_mod_cast this
      linarith
    exact h2
  have hcast : ((CaseIFullBox n H).ncard : ℝ) ≤
      ((∑ D ∈ caseIFullIndex n H, (fiberAt n H D).ncard : ℕ) : ℝ) := by
    exact_mod_cast le_trans h1 h2
  calc ((CaseIFullBox n H).ncard : ℝ)
      ≤ ((∑ D ∈ caseIFullIndex n H, (fiberAt n H D).ncard : ℕ) : ℝ) := hcast
    _ = ∑ D ∈ caseIFullIndex n H, ((fiberAt n H D).ncard : ℝ) := by rw [Nat.cast_sum]
    _ ≤ ∑ D ∈ caseIFullIndex n H, ((c : ℝ) ^ omega D * (H : ℝ) ^ n / (D : ℝ)) :=
        Finset.sum_le_sum h3

/-- **The per-discriminant sum is bounded by the squarefull tail sum.** -/
theorem caseIFull_sum_le_tail (n H c : ℕ) (hn : 3 ≤ n) (hH : 1 ≤ H) (hc : 1 ≤ c)
    (hY1 : 1 ≤ caseIThrF n H) (hYT : caseIThrF n H < caseICap n H) :
    ∑ D ∈ caseIFullIndex n H, ((c : ℝ) ^ omega D * (H : ℝ) ^ n / (D : ℝ)) ≤
      (c : ℝ) * (H : ℝ) ^ n *
        ((1 + Real.log (caseICap n H : ℝ)) ^ (2 * c) /
          (caseIThrF n H : ℝ) ^ ((1 : ℝ) / 2)) := by
  classical
  have htail := squarefull_tail_bound c hc ((1 : ℝ) / 2) (by norm_num) le_rfl
    (caseIThrF n H) (caseICap n H) hY1 hYT
  have hsub : caseIFullIndex n H ⊆ Finset.Icc (caseIThrF n H + 1) (caseICap n H) := by
    intro D hD
    rw [caseIFullIndex, Finset.mem_filter, Finset.mem_filter] at hD
    exact hD.1.1
  have hsqmem : ∀ D ∈ caseIFullIndex n H, Squarefull D := by
    intro D hD
    rw [caseIFullIndex, Finset.mem_filter, Finset.mem_filter] at hD
    exact hD.1.2
  have hsum1 : ∑ D ∈ caseIFullIndex n H, (c : ℝ) ^ omega D / (D : ℝ) ≤
      ∑ D ∈ Finset.Icc (caseIThrF n H + 1) (caseICap n H),
        (if Squarefull D then (c : ℝ) ^ omega D / (D : ℝ) else 0) := by
    calc ∑ D ∈ caseIFullIndex n H, (c : ℝ) ^ omega D / (D : ℝ)
        = ∑ D ∈ caseIFullIndex n H,
            (if Squarefull D then (c : ℝ) ^ omega D / (D : ℝ) else 0) := by
          refine Finset.sum_congr rfl (fun D hD => ?_)
          simp [hsqmem D hD]
      _ ≤ ∑ D ∈ Finset.Icc (caseIThrF n H + 1) (caseICap n H),
            (if Squarefull D then (c : ℝ) ^ omega D / (D : ℝ) else 0) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg hsub (fun D hD hDs => ?_)
          by_cases hsq : Squarefull D
          · simp only [hsq, if_true]
            have hD0 : (0 : ℝ) < (D : ℝ) := by
              have := (Finset.mem_Icc.mp hD).1
              exact_mod_cast (by omega : 0 < D)
            positivity
          · simp [hsq]
  have hfactor : ∑ D ∈ caseIFullIndex n H, ((c : ℝ) ^ omega D * (H : ℝ) ^ n / (D : ℝ)) =
      (H : ℝ) ^ n * (∑ D ∈ caseIFullIndex n H, (c : ℝ) ^ omega D / (D : ℝ)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun D _ => ?_)
    ring
  rw [hfactor]
  refine le_trans (mul_le_mul_of_nonneg_left hsum1 (by positivity)) ?_
  refine le_trans (mul_le_mul_of_nonneg_left htail (by positivity)) ?_
  rw [mul_assoc]
  exact le_mul_of_one_le_left (by positivity) (by exact_mod_cast hc)

/-- **The log-absorption estimate** for the Case-I cap
`Z = caseICap n H`: `(1 + log Z)^(2c) ≤ H^(1/(2n))` eventually, `c = 2^((n+1)^4)`. -/
lemma eventually_one_add_log_caseICap (n K : ℕ) (hn : 3 ≤ n) :
    ∀ᶠ H : ℕ in atTop,
      (1 + Real.log (caseICap n H : ℝ)) ^ K ≤
        (H : ℝ) ^ ((1 : ℝ) / (2 * n)) := by
  have hpow := Commons.Analysis.ExpLog.eventually_one_add_log_pow_le_rpow
    K 1 ((1 : ℝ) / (4 * n)) (by positivity)
  have hconst : ∀ᶠ H : ℕ in atTop,
      (((4 * n ^ 2 : ℕ) : ℝ) + 1) ^ K ≤
        (H : ℝ) ^ ((1 : ℝ) / (4 * n)) :=
    Commons.Analysis.ExpLog.eventually_natCast_rpow_atTop_ge _ _ (by positivity)
  have hcap : ∀ᶠ H : ℕ in atTop, caseICap n H ≤ H ^ (4 * n ^ 2) := by
    filter_upwards [Commons.Data.Nat.eventually_heightCap_le_pow n (by omega)] with H hH
    simpa only [caseICap] using hH
  have hge1 : ∀ᶠ H : ℕ in atTop, (1 : ℝ) ≤ (H : ℝ) :=
    (eventually_ge_atTop (1 : ℕ)).mono (fun H h => by exact_mod_cast h)
  filter_upwards [hpow, hconst, hcap, hge1] with H hpow hconst hcap hge1
  have hHpos : (0 : ℝ) < (H : ℝ) := lt_of_lt_of_le one_pos hge1
  have hlogZ : Real.log (caseICap n H : ℝ) ≤ ((4 * n ^ 2 : ℕ) : ℝ) * Real.log (H : ℝ) := by
    have hpos1 : (0 : ℝ) < (caseICap n H : ℝ) := by
      have hnat : 0 < caseICap n H := by
        simp only [caseICap]
        exact Nat.mul_pos (Nat.factorial_pos _)
          (pow_pos (Nat.mul_pos (lt_of_lt_of_le (by norm_num : (0:ℕ) < 3) hn)
            (Nat.succ_pos H)) _)
      exact_mod_cast hnat
    calc Real.log (caseICap n H : ℝ) ≤ Real.log ((H : ℝ) ^ (4 * n ^ 2)) :=
          Real.log_le_log hpos1 (by exact_mod_cast hcap)
      _ = ((4 * n ^ 2 : ℕ) : ℝ) * Real.log (H : ℝ) := Real.log_pow _ _
  have hlogH0 : (0 : ℝ) ≤ Real.log (H : ℝ) := Real.log_nonneg hge1
  have hstep : 1 + Real.log (caseICap n H : ℝ) ≤
      (((4 * n ^ 2 : ℕ) : ℝ) + 1) * (1 + Real.log (H : ℝ)) := by
    have hc : (0 : ℝ) ≤ ((4 * n ^ 2 : ℕ) : ℝ) := by positivity
    nlinarith [hlogZ, hlogH0]
  have hpow' : (1 + Real.log ((H : ℝ) ^ 1)) ^ K ≤
      (H : ℝ) ^ ((1 : ℝ) / (4 * n)) := hpow
  rw [pow_one] at hpow'
  calc (1 + Real.log (caseICap n H : ℝ)) ^ K
      ≤ ((((4 * n ^ 2 : ℕ) : ℝ) + 1) * (1 + Real.log (H : ℝ))) ^ K :=
        pow_le_pow_left₀ (by positivity) hstep _
    _ = (((4 * n ^ 2 : ℕ) : ℝ) + 1) ^ K *
          (1 + Real.log (H : ℝ)) ^ K := mul_pow _ _ _
    _ ≤ (H : ℝ) ^ ((1 : ℝ) / (4 * n)) * (H : ℝ) ^ ((1 : ℝ) / (4 * n)) :=
        mul_le_mul hconst hpow' (by positivity) (by positivity)
    _ = (H : ℝ) ^ ((1 : ℝ) / (2 * n)) := by
        rw [← Real.rpow_add hHpos]
        congr 1
        field_simp
        ring

/-- **The Case-I region is `O(H^(n-1))` given the per-discriminant Fourier
bound.** -/
theorem CaseIFullBox_bound_real (n c : ℕ) (hn : 3 ≤ n) (hc : 1 ≤ c)
    (hper : PerDDiscBound n c) :
    ∃ C : ℝ, ∀ᶠ H : ℕ in atTop,
      ((CaseIFullBox n H).ncard : ℝ) ≤ C * (H : ℝ) ^ (n - 1) := by
  -- threshold range
  have hthr : ∀ᶠ H : ℕ in atTop,
      1 ≤ caseIThrF n H ∧ caseIThrF n H < caseICap n H := by
    have hbig : ∀ᶠ H : ℕ in atTop, (2 : ℝ) ≤ (H : ℝ) ^ (2 + 1 / (n : ℝ)) :=
      Commons.Analysis.ExpLog.eventually_natCast_rpow_atTop_ge _ _ (by positivity)
    have hcmp : ∀ᶠ H : ℕ in atTop,
        (H : ℝ) ^ (2 + 1 / (n : ℝ)) < (caseICap n H : ℝ) := by
      have hlt : ∀ᶠ H : ℕ in atTop,
          (H : ℝ) ^ (2 + 1 / (n : ℝ)) < (H : ℝ) ^ (((2 * n - 1 : ℕ)) : ℝ) := by
        filter_upwards [eventually_ge_atTop (2 : ℕ)] with H hH
        have hH1 : (1 : ℝ) < (H : ℝ) := by exact_mod_cast (by omega : 1 < H)
        refine Real.rpow_lt_rpow_of_exponent_lt hH1 ?_
        have hnR : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
        have h1 : 1 / (n : ℝ) ≤ 1 := by rw [div_le_one hnpos]; linarith
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
    refine ⟨?_, ?_⟩
    · simp only [caseIThrF]
      refine Nat.le_floor ?_
      have h2 : (1 : ℝ) ≤ 2 := by norm_num
      linarith
    · simp only [caseIThrF]
      refine (Nat.floor_lt (by positivity)).mpr ?_
      exact h2
  -- threshold lower bound
  have hY : ∀ᶠ H : ℕ in atTop,
      (H : ℝ) ^ (1 + 1 / (2 * (n : ℝ))) / Real.sqrt 2 ≤
        (caseIThrF n H : ℝ) ^ ((1 : ℝ) / 2) := by
    have hbig : ∀ᶠ H : ℕ in atTop, (2 : ℝ) ≤ (H : ℝ) ^ (2 + 1 / (n : ℝ)) :=
      Commons.Analysis.ExpLog.eventually_natCast_rpow_atTop_ge _ _ (by positivity)
    filter_upwards [hbig] with H hbig
    have hfloor : (H : ℝ) ^ (2 + 1 / (n : ℝ)) - 1 ≤ (caseIThrF n H : ℝ) := by
      have h := Nat.lt_floor_add_one ((H : ℝ) ^ (2 + 1 / (n : ℝ)))
      simp only [caseIThrF]
      linarith
    have hkey : (H : ℝ) ^ (2 + 1 / (n : ℝ)) ≤ 2 * (caseIThrF n H : ℝ) := by
      have h1 : (H : ℝ) ^ (2 + 1 / (n : ℝ)) ≤
          2 * ((H : ℝ) ^ (2 + 1 / (n : ℝ)) - 1) := by linarith [hbig]
      have h2 : (2 : ℝ) * ((H : ℝ) ^ (2 + 1 / (n : ℝ)) - 1) ≤
          2 * (caseIThrF n H : ℝ) := by linarith [hfloor]
      linarith
    have hsq : ((H : ℝ) ^ (1 + 1 / (2 * (n : ℝ)))) ^ 2 ≤
        (Real.sqrt 2 * Real.sqrt (caseIThrF n H : ℝ)) ^ 2 := by
      have h1 : ((H : ℝ) ^ (1 + 1 / (2 * (n : ℝ)))) ^ 2 =
          (H : ℝ) ^ (2 + 1 / (n : ℝ)) := by
        rw [← Real.rpow_natCast ((H : ℝ) ^ (1 + 1 / (2 * (n : ℝ)))) 2,
          ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ (H : ℝ))]
        congr 1
        push_cast
        field_simp
      have h2 : (Real.sqrt 2 * Real.sqrt (caseIThrF n H : ℝ)) ^ 2 =
          2 * (caseIThrF n H : ℝ) := by
        rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
          Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (caseIThrF n H : ℝ))]
      rw [h1, h2]
      exact hkey
    have hmain := Real.sqrt_le_sqrt hsq
    rw [Real.sqrt_sq (Real.rpow_nonneg (Nat.cast_nonneg H) _),
      Real.sqrt_sq (by positivity : (0 : ℝ) ≤ Real.sqrt 2 * Real.sqrt (caseIThrF n H : ℝ))]
      at hmain
    have hsqrt : (caseIThrF n H : ℝ) ^ ((1 : ℝ) / 2) = Real.sqrt (caseIThrF n H : ℝ) :=
      (Real.sqrt_eq_rpow _).symm
    rw [hsqrt, div_le_iff₀ (Real.sqrt_pos.mpr (by norm_num))]
    simpa [mul_comm] using hmain
  refine ⟨(c : ℝ) * Real.sqrt 2, ?_⟩
  have hge1 : ∀ᶠ H : ℕ in atTop, (1 : ℝ) ≤ (H : ℝ) :=
    (eventually_ge_atTop (1 : ℕ)).mono (fun H h => by exact_mod_cast h)
  filter_upwards [hthr, hY, eventually_one_add_log_caseICap n (2 * c) hn, hge1,
    eventually_ge_atTop (1 : ℕ)] with H hthr hY hlog hge1 hH1
  have hHpos : (0 : ℝ) < (H : ℝ) := lt_of_lt_of_le one_pos hge1
  have h1 := CaseIFullBox_ncard_le_sum n H c hn (by omega : 1 ≤ H) hper
  have h2 := caseIFull_sum_le_tail n H c hn (by omega : 1 ≤ H) hc hthr.1 hthr.2
  have h3 : ((CaseIFullBox n H).ncard : ℝ) ≤
      (c : ℝ) * (H : ℝ) ^ n *
        ((1 + Real.log (caseICap n H : ℝ)) ^ (2 * c) /
          (caseIThrF n H : ℝ) ^ ((1 : ℝ) / 2)) := le_trans h1 h2
  have hbr : (1 + Real.log (caseICap n H : ℝ)) ^ (2 * c) /
        (caseIThrF n H : ℝ) ^ ((1 : ℝ) / 2) ≤
      (H : ℝ) ^ ((1 : ℝ) / (2 * n)) /
        ((H : ℝ) ^ (1 + 1 / (2 * (n : ℝ))) / Real.sqrt 2) :=
    div_le_div₀ (by positivity) hlog (div_pos (by positivity) (by positivity)) hY
  have heq : (H : ℝ) ^ ((1 : ℝ) / (2 * n)) /
        ((H : ℝ) ^ (1 + 1 / (2 * (n : ℝ))) / Real.sqrt 2) = Real.sqrt 2 / (H : ℝ) := by
    rw [show (H : ℝ) ^ (1 + 1 / (2 * (n : ℝ))) =
        (H : ℝ) * (H : ℝ) ^ ((1 : ℝ) / (2 * n)) by
      rw [Real.rpow_add hHpos, Real.rpow_one]]
    have hHa : (H : ℝ) ^ ((1 : ℝ) / (2 * n)) ≠ 0 :=
      ne_of_gt (Real.rpow_pos_of_pos hHpos _)
    have hs : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
    field_simp
  have hdiv : (H : ℝ) ^ n / (H : ℝ) = (H : ℝ) ^ (n - 1) := by
    have := pow_sub₀ (H : ℝ) hHpos.ne' (show 1 ≤ n by omega)
    rw [pow_one] at this
    exact this.symm
  have hbr' : (1 + Real.log (caseICap n H : ℝ)) ^ (2 * c) /
        (caseIThrF n H : ℝ) ^ ((1 : ℝ) / 2) ≤ Real.sqrt 2 / (H : ℝ) :=
    le_trans hbr (le_of_eq heq)
  calc ((CaseIFullBox n H).ncard : ℝ)
      ≤ (c : ℝ) * (H : ℝ) ^ n *
          ((1 + Real.log (caseICap n H : ℝ)) ^ (2 * c) /
            (caseIThrF n H : ℝ) ^ ((1 : ℝ) / 2)) := h3
    _ ≤ (c : ℝ) * (H : ℝ) ^ n * (Real.sqrt 2 / (H : ℝ)) :=
        mul_le_mul_of_nonneg_left hbr' (by positivity)
    _ = ((c : ℝ) * Real.sqrt 2) * (H : ℝ) ^ (n - 1) := by
        rw [show (c : ℝ) * (H : ℝ) ^ n * (Real.sqrt 2 / (H : ℝ)) =
            (c : ℝ) * Real.sqrt 2 * ((H : ℝ) ^ n / (H : ℝ)) by ring, hdiv]

/-- **`CaseIFull` is `O(H^(n-1))` given the per-discriminant Fourier bound**
(polynomial level). -/
theorem CaseIFull_isBigO (n c : ℕ) (hn : 3 ≤ n) (hc : 1 ≤ c)
    (hper : PerDDiscBound n c) :
    (fun H : ℕ => ((CaseIFull n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) := by
  obtain ⟨C, hC⟩ := CaseIFullBox_bound_real n c hn hc hper
  set C' : ℕ := Nat.ceil C with hC'_def
  have hCC' : C ≤ (C' : ℝ) := Nat.le_ceil C
  have hle : ∀ᶠ H : ℕ in atTop, (CaseIFullBox n H).ncard ≤ C' * H ^ (n - 1) := by
    filter_upwards [hC] with H hH
    have h1 : ((CaseIFullBox n H).ncard : ℝ) ≤ (C' : ℝ) * (H : ℝ) ^ (n - 1) :=
      le_trans hH (mul_le_mul_of_nonneg_right hCC' (by positivity))
    exact_mod_cast h1
  have hbox : (fun H : ℕ => ((CaseIFullBox n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) :=
    (Commons.Analysis.Asymptotics.isBigO_of_eventually_le _ _ hle).trans
      (Commons.Analysis.Asymptotics.isBigO_of_natCast_le_mul_pow (n - 1) C'
        (fun H => C' * H ^ (n - 1)) (Eventually.of_forall (fun H => le_rfl)))
  -- transfer to the polynomial level
  have himg : ∀ H, CaseIFull n H = Subtype.val '' (CaseIFullBox n H) := by
    intro H
    ext f
    constructor
    · rintro ⟨h, hbox, h1, h2, h3⟩
      exact ⟨⟨f, hbox⟩, ⟨h, h1, h2, h3⟩, rfl⟩
    · rintro ⟨g, ⟨h, h1, h2, h3⟩, rfl⟩
      exact ⟨h, g.2, h1, h2, h3⟩
  have hle2 : ∀ᶠ H : ℕ in atTop,
      (CaseIFull n H).ncard ≤ (CaseIFullBox n H).ncard :=
    Eventually.of_forall (fun H => by
      rw [himg H]
      exact le_of_eq (Set.ncard_image_of_injective _ Subtype.val_injective))
  exact (Commons.Analysis.Asymptotics.isBigO_of_eventually_le _ _ hle2).trans hbox

end

end Submission.Vdw
