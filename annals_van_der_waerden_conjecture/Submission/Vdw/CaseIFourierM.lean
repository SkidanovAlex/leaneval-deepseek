import Mathlib
import Submission.Vdw.CaseIFourier
import Submission.Vdw.PerDDiscTheta
import Submission.Vdw.CaseIRegionM
import Submission.Commons.Analysis.ExpLog.eventually_one_add_log_pow_le_rpow
import Submission.Commons.Data.Nat.eventually_heightCap_le_pow
import Submission.Commons.Analysis.Asymptotics.isBigO_of_natCast_le_mul_pow
import Submission.Commons.Analysis.Asymptotics.isBigO_of_eventually_le

open Polynomial Asymptotics
open scoped BigOperators
open Function
open Filter
open vanDerWaerdenConjecture

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-!
# Case I, the `C_f ≤ H^(1+δ)`, `D_f > H^(2+2δ)` region, with `δ = 2/M` as parameter

`CaseIFourier` bounds this region using the per-discriminant Fourier input
`PerDDiscBound n c` at the fixed threshold `δ = 1/(2n)`.  Here the same
assembly is run with `δ = 2/M` for an integer parameter `M`, using
`PerDDiscTheta.PerDDiscBoundTheta n (2/M) c` — which at the Weyl threshold
`δ = 2^{-n}/(2n)` (`M = 4n·2^n`) is supplied *unconditionally* by
`PerIrrWeyl.perIrrBoundTheta_weyl` + `PerDDiscTheta.perDDiscBoundTheta_of_perIrrBoundTheta`.
The exponents `2 + 1/n`, `1 + 1/(2n)`, `1/(4n)`, `1/(2n)` become `2 + 4/M`,
`1 + 2/M`, `1/M`, `2/M`; the side condition `2 + 4/M < 2n − 1` is as in
`CaseIRegionM`.

Axioms: propext / Classical.choice / Quot.sound only.
-/

namespace Submission.Vdw

noncomputable section

/-- **The Case-I direct-regime counting threshold** `Y = ⌊H^(2+2δ)⌋`. -/
def caseIThrFM (M H : ℕ) : ℕ := Nat.floor ((H : ℝ) ^ ((2 : ℝ) + 4 / (M : ℝ)))


/-- **The Case-I region** (box level): squarefull field discriminant with
`C_f ≤ H^(1+δ)` and `D_f > H^(2+2δ)`. -/
def CaseIFullBoxM (n M H : ℕ) : Set ↥(Box n H) :=
  {f | ∃ h : Irreducible (f.1.map φℚ),
      Squarefull (fieldDiscExp f.1 h) ∧
      (radical (fieldDiscExp f.1 h) : ℝ) ≤ (H : ℝ) ^ ((1 : ℝ) + 2 / (M : ℝ)) ∧
      (H : ℝ) ^ ((2 : ℝ) + 4 / (M : ℝ)) < (fieldDiscExp f.1 h : ℝ)}

/-- The polynomial-level Case-I region. -/
def CaseIFullM (n M H : ℕ) : Set ℤ[X] :=
  {f | ∃ h : Irreducible (f.map φℚ),
      f ∈ Box n H ∧ Squarefull (fieldDiscExp f h) ∧
      (radical (fieldDiscExp f h) : ℝ) ≤ (H : ℝ) ^ ((1 : ℝ) + 2 / (M : ℝ)) ∧
      (H : ℝ) ^ ((2 : ℝ) + 4 / (M : ℝ)) < (fieldDiscExp f h : ℝ)}


/-- The admissible discriminant values: `⌊H^(2+2δ)⌋ < D ≤ Z`, `D` squarefull,
`radical D ≤ H^(1+δ)`, and all prime divisors of `D` exceeding `n` occurring
with exponent `< n` (the side conditions of `PerDDiscBound` that hold
automatically for `D = D_f` of a region member). -/
def caseIFullIndexM (n M H : ℕ) : Finset ℕ :=
  ((Finset.Icc (caseIThrFM M H + 1) (caseICap n H)).filter Squarefull).filter
    (fun D => (radical D : ℝ) ≤ (H : ℝ) ^ ((1 : ℝ) + 2 / (M : ℝ)) ∧
      (∀ p ∈ D.primeFactors, n < p → D.factorization p < n))

/-- **Region membership**: every member of `CaseIFullBox` has its field
discriminant in the index set. -/
theorem CaseIFullBoxM_subset_biUnion (n M H : ℕ) (hn : 3 ≤ n) (hM : 1 ≤ M) (hH : 1 ≤ H) :
    CaseIFullBoxM n M H ⊆
      {f : ↥(Box n H) | ∃ D ∈ caseIFullIndexM n M H, f ∈ fiberAt n H D} := by
  classical
  intro f hf
  obtain ⟨h, hsq, hC, hlarge⟩ := hf
  haveI : Fact (Irreducible (f.1.map φℚ)) := ⟨h⟩
  have hmon : f.1.Monic := f.2.1
  have hdeg : f.1.natDegree = n := Polynomial.natDegree_eq_of_degree_eq_some f.2.2.1
  refine ⟨fieldDiscExp f.1 h, ?_, h, rfl⟩
  have hZ : fieldDiscExp f.1 h ≤ caseICap n H :=
    fieldDisc_height_bound f.1 hmon n H hdeg (fun k hk => f.2.2.2 k hk)
  have hY : caseIThrFM M H < fieldDiscExp f.1 h := by
    have h1 : (caseIThrFM M H : ℝ) ≤ (H : ℝ) ^ ((2 : ℝ) + 4 / (M : ℝ)) := by
      simp only [caseIThrFM]
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
  rw [caseIFullIndexM, Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨⟨by omega, hZ⟩, hsq⟩, hC, hfac⟩

/-- Finiteness of the region. -/
theorem CaseIFullBoxM_finite (n M H : ℕ) : (CaseIFullBoxM n M H).Finite := Set.toFinite _

/-- **The region count is at most the per-discriminant sum.** -/
theorem CaseIFullBoxM_ncard_le_sum (n M H c : ℕ) (hn : 3 ≤ n) (hM : 1 ≤ M) (hH : 1 ≤ H)
    (hper : PerDDiscBoundTheta n ((2 : ℝ) / (M : ℝ)) c) :
    ((CaseIFullBoxM n M H).ncard : ℝ) ≤
      ∑ D ∈ caseIFullIndexM n M H, (c : ℝ) ^ omega D * (H : ℝ) ^ n / (D : ℝ) := by
  classical
  haveI : Finite ↥(Box n H) := box_finite n H
  have hfin : ({f : ↥(Box n H) | ∃ D ∈ caseIFullIndexM n M H, f ∈ fiberAt n H D}).Finite :=
    Set.toFinite _
  have h1 : (CaseIFullBoxM n M H).ncard ≤
      ({f : ↥(Box n H) | ∃ D ∈ caseIFullIndexM n M H, f ∈ fiberAt n H D}).ncard :=
    Set.ncard_le_ncard (CaseIFullBoxM_subset_biUnion n M H hn hM hH) hfin
  have h2 := ncard_biUnion_finset_le (caseIFullIndexM n M H) (fiberAt n H)
  have h3 : ∀ D ∈ caseIFullIndexM n M H,
      ((fiberAt n H D).ncard : ℝ) ≤ (c : ℝ) ^ omega D * (H : ℝ) ^ n / (D : ℝ) := by
    intro D hD
    rw [caseIFullIndexM, Finset.mem_filter, Finset.mem_filter] at hD
    obtain ⟨⟨hDIcc, hDsq⟩, hDrad, hDfac⟩ := hD
    have hD0 : D ≠ 0 := by
      have := (Finset.mem_Icc.mp hDIcc).1
      omega
    have hcard : (fiberAt n H D).ncard = Nat.card {f : ↥(Box n H) //
        ∃ h : Irreducible (f.1.map φℚ), fieldDiscExp f.1 h = D} :=
      (Nat.card_coe_set_eq _).symm
    rw [hcard]
    refine hper H D hD0 hDsq hDrad hDfac ?_
    have hDgt : caseIThrFM M H < D := by
      have := (Finset.mem_Icc.mp hDIcc).1
      omega
    have h1 : (caseIThrFM M H : ℝ) ≤ (H : ℝ) ^ ((2 : ℝ) + 4 / (M : ℝ)) := by
      simp only [caseIThrFM]
      exact Nat.floor_le (by positivity)
    have h2 : (H : ℝ) ^ ((2 : ℝ) + 4 / (M : ℝ)) < (D : ℝ) := by
      have h3 : (H : ℝ) ^ ((2 : ℝ) + 4 / (M : ℝ)) < (caseIThrFM M H : ℝ) + 1 :=
        Nat.lt_floor_add_one _
      have h4 : (caseIThrFM M H : ℝ) + 1 ≤ (D : ℝ) := by
        have : caseIThrFM M H + 1 ≤ D := by omega
        exact_mod_cast this
      linarith
    have h2' : (H : ℝ) ^ ((2 : ℝ) + 2 * (2 / (M : ℝ))) < (D : ℝ) := by
      have he : (2 : ℝ) + 2 * (2 / (M : ℝ)) = (2 : ℝ) + 4 / (M : ℝ) := by ring
      rw [he]; exact h2
    exact h2'
  have hcast : ((CaseIFullBoxM n M H).ncard : ℝ) ≤
      ((∑ D ∈ caseIFullIndexM n M H, (fiberAt n H D).ncard : ℕ) : ℝ) := by
    exact_mod_cast le_trans h1 h2
  calc ((CaseIFullBoxM n M H).ncard : ℝ)
      ≤ ((∑ D ∈ caseIFullIndexM n M H, (fiberAt n H D).ncard : ℕ) : ℝ) := hcast
    _ = ∑ D ∈ caseIFullIndexM n M H, ((fiberAt n H D).ncard : ℝ) := by rw [Nat.cast_sum]
    _ ≤ ∑ D ∈ caseIFullIndexM n M H, ((c : ℝ) ^ omega D * (H : ℝ) ^ n / (D : ℝ)) :=
        Finset.sum_le_sum h3

/-- **The per-discriminant sum is bounded by the squarefull tail sum.** -/
theorem caseIFullM_sum_le_tail (n M H c : ℕ) (hn : 3 ≤ n) (hM : 1 ≤ M) (hH : 1 ≤ H) (hc : 1 ≤ c)
    (hY1 : 1 ≤ caseIThrFM M H) (hYT : caseIThrFM M H < caseICap n H) :
    ∑ D ∈ caseIFullIndexM n M H, ((c : ℝ) ^ omega D * (H : ℝ) ^ n / (D : ℝ)) ≤
      (c : ℝ) * (H : ℝ) ^ n *
        ((1 + Real.log (caseICap n H : ℝ)) ^ (2 * c) /
          (caseIThrFM M H : ℝ) ^ ((1 : ℝ) / 2)) := by
  classical
  have htail := squarefull_tail_bound c hc ((1 : ℝ) / 2) (by norm_num) le_rfl
    (caseIThrFM M H) (caseICap n H) hY1 hYT
  have hsub : caseIFullIndexM n M H ⊆ Finset.Icc (caseIThrFM M H + 1) (caseICap n H) := by
    intro D hD
    rw [caseIFullIndexM, Finset.mem_filter, Finset.mem_filter] at hD
    exact hD.1.1
  have hsqmem : ∀ D ∈ caseIFullIndexM n M H, Squarefull D := by
    intro D hD
    rw [caseIFullIndexM, Finset.mem_filter, Finset.mem_filter] at hD
    exact hD.1.2
  have hsum1 : ∑ D ∈ caseIFullIndexM n M H, (c : ℝ) ^ omega D / (D : ℝ) ≤
      ∑ D ∈ Finset.Icc (caseIThrFM M H + 1) (caseICap n H),
        (if Squarefull D then (c : ℝ) ^ omega D / (D : ℝ) else 0) := by
    calc ∑ D ∈ caseIFullIndexM n M H, (c : ℝ) ^ omega D / (D : ℝ)
        = ∑ D ∈ caseIFullIndexM n M H,
            (if Squarefull D then (c : ℝ) ^ omega D / (D : ℝ) else 0) := by
          refine Finset.sum_congr rfl (fun D hD => ?_)
          simp [hsqmem D hD]
      _ ≤ ∑ D ∈ Finset.Icc (caseIThrFM M H + 1) (caseICap n H),
            (if Squarefull D then (c : ℝ) ^ omega D / (D : ℝ) else 0) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg hsub (fun D hD hDs => ?_)
          by_cases hsq : Squarefull D
          · simp only [hsq, if_true]
            have hD0 : (0 : ℝ) < (D : ℝ) := by
              have := (Finset.mem_Icc.mp hD).1
              exact_mod_cast (by omega : 0 < D)
            positivity
          · simp [hsq]
  have hfactor : ∑ D ∈ caseIFullIndexM n M H, ((c : ℝ) ^ omega D * (H : ℝ) ^ n / (D : ℝ)) =
      (H : ℝ) ^ n * (∑ D ∈ caseIFullIndexM n M H, (c : ℝ) ^ omega D / (D : ℝ)) := by
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
lemma eventually_one_add_log_caseICapM (n M K : ℕ) (hn : 3 ≤ n) (hM : 1 ≤ M) :
    ∀ᶠ H : ℕ in atTop,
      (1 + Real.log (caseICap n H : ℝ)) ^ K ≤
        (H : ℝ) ^ ((2 : ℝ) / (M : ℝ)) := by
  have hMinv : (0 : ℝ) < (1 : ℝ) / (M : ℝ) := by
    have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
    positivity
  have hpow := Commons.Analysis.ExpLog.eventually_one_add_log_pow_le_rpow
    K 1 ((1 : ℝ) / (M : ℝ)) hMinv
  have hconst : ∀ᶠ H : ℕ in atTop,
      (((4 * n ^ 2 : ℕ) : ℝ) + 1) ^ K ≤
        (H : ℝ) ^ ((1 : ℝ) / (M : ℝ)) :=
    Commons.Analysis.ExpLog.eventually_natCast_rpow_atTop_ge _ _ hMinv
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
      (H : ℝ) ^ ((1 : ℝ) / (M : ℝ)) := hpow
  rw [pow_one] at hpow'
  calc (1 + Real.log (caseICap n H : ℝ)) ^ K
      ≤ ((((4 * n ^ 2 : ℕ) : ℝ) + 1) * (1 + Real.log (H : ℝ))) ^ K :=
        pow_le_pow_left₀ (by positivity) hstep _
    _ = (((4 * n ^ 2 : ℕ) : ℝ) + 1) ^ K *
          (1 + Real.log (H : ℝ)) ^ K := mul_pow _ _ _
    _ ≤ (H : ℝ) ^ ((1 : ℝ) / (M : ℝ)) * (H : ℝ) ^ ((1 : ℝ) / (M : ℝ)) :=
        mul_le_mul hconst hpow' (by positivity) (by positivity)
    _ = (H : ℝ) ^ ((2 : ℝ) / (M : ℝ)) := by
        rw [← Real.rpow_add hHpos]
        congr 1
        field_simp
        ring

/-- **The Case-I region is `O(H^(n-1))` given the per-discriminant Fourier
bound.** -/
theorem CaseIFullBoxM_bound_real (n M c : ℕ) (hn : 3 ≤ n) (hM : 1 ≤ M) (hc : 1 ≤ c)
    (hMn : (2 : ℝ) + 4 / (M : ℝ) < 2 * (n : ℝ) - 1)
    (hper : PerDDiscBoundTheta n ((2 : ℝ) / (M : ℝ)) c) :
    ∃ C : ℝ, ∀ᶠ H : ℕ in atTop,
      ((CaseIFullBoxM n M H).ncard : ℝ) ≤ C * (H : ℝ) ^ (n - 1) := by
  -- threshold range
  have hthr : ∀ᶠ H : ℕ in atTop,
      1 ≤ caseIThrFM M H ∧ caseIThrFM M H < caseICap n H := by
    have hbig : ∀ᶠ H : ℕ in atTop, (2 : ℝ) ≤ (H : ℝ) ^ ((2 : ℝ) + 4 / (M : ℝ)) :=
      Commons.Analysis.ExpLog.eventually_natCast_rpow_atTop_ge _ _ (by positivity)
    have hcmp : ∀ᶠ H : ℕ in atTop,
        (H : ℝ) ^ ((2 : ℝ) + 4 / (M : ℝ)) < (caseICap n H : ℝ) := by
      have hlt : ∀ᶠ H : ℕ in atTop,
          (H : ℝ) ^ ((2 : ℝ) + 4 / (M : ℝ)) < (H : ℝ) ^ (((2 * n - 1 : ℕ)) : ℝ) := by
        filter_upwards [eventually_ge_atTop (2 : ℕ)] with H hH
        have hH1 : (1 : ℝ) < (H : ℝ) := by exact_mod_cast (by omega : 1 < H)
        refine Real.rpow_lt_rpow_of_exponent_lt hH1 ?_
        have h1 : (2 : ℝ) + 4 / (M : ℝ) < 2 * (n : ℝ) - 1 := hMn
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
    · simp only [caseIThrFM]
      refine Nat.le_floor ?_
      have h2 : (1 : ℝ) ≤ 2 := by norm_num
      linarith
    · simp only [caseIThrFM]
      refine (Nat.floor_lt (by positivity)).mpr ?_
      exact h2
  -- threshold lower bound
  have hY : ∀ᶠ H : ℕ in atTop,
      (H : ℝ) ^ ((1 : ℝ) + 2 / (M : ℝ)) / Real.sqrt 2 ≤
        (caseIThrFM M H : ℝ) ^ ((1 : ℝ) / 2) := by
    have hbig : ∀ᶠ H : ℕ in atTop, (2 : ℝ) ≤ (H : ℝ) ^ ((2 : ℝ) + 4 / (M : ℝ)) :=
      Commons.Analysis.ExpLog.eventually_natCast_rpow_atTop_ge _ _ (by positivity)
    filter_upwards [hbig] with H hbig
    have hfloor : (H : ℝ) ^ ((2 : ℝ) + 4 / (M : ℝ)) - 1 ≤ (caseIThrFM M H : ℝ) := by
      have h := Nat.lt_floor_add_one ((H : ℝ) ^ ((2 : ℝ) + 4 / (M : ℝ)))
      simp only [caseIThrFM]
      linarith
    have hkey : (H : ℝ) ^ ((2 : ℝ) + 4 / (M : ℝ)) ≤ 2 * (caseIThrFM M H : ℝ) := by
      have h1 : (H : ℝ) ^ ((2 : ℝ) + 4 / (M : ℝ)) ≤
          2 * ((H : ℝ) ^ ((2 : ℝ) + 4 / (M : ℝ)) - 1) := by linarith [hbig]
      have h2 : (2 : ℝ) * ((H : ℝ) ^ ((2 : ℝ) + 4 / (M : ℝ)) - 1) ≤
          2 * (caseIThrFM M H : ℝ) := by linarith [hfloor]
      linarith
    have hsq : ((H : ℝ) ^ ((1 : ℝ) + 2 / (M : ℝ))) ^ 2 ≤
        (Real.sqrt 2 * Real.sqrt (caseIThrFM M H : ℝ)) ^ 2 := by
      have h1 : ((H : ℝ) ^ ((1 : ℝ) + 2 / (M : ℝ))) ^ 2 =
          (H : ℝ) ^ ((2 : ℝ) + 4 / (M : ℝ)) := by
        rw [← Real.rpow_natCast ((H : ℝ) ^ ((1 : ℝ) + 2 / (M : ℝ))) 2,
          ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ (H : ℝ))]
        congr 1
        push_cast
        field_simp
        ring
      have h2 : (Real.sqrt 2 * Real.sqrt (caseIThrFM M H : ℝ)) ^ 2 =
          2 * (caseIThrFM M H : ℝ) := by
        rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
          Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (caseIThrFM M H : ℝ))]
      rw [h1, h2]
      exact hkey
    have hmain := Real.sqrt_le_sqrt hsq
    rw [Real.sqrt_sq (Real.rpow_nonneg (Nat.cast_nonneg H) _),
      Real.sqrt_sq (by positivity : (0 : ℝ) ≤ Real.sqrt 2 * Real.sqrt (caseIThrFM M H : ℝ))]
      at hmain
    have hsqrt : (caseIThrFM M H : ℝ) ^ ((1 : ℝ) / 2) = Real.sqrt (caseIThrFM M H : ℝ) :=
      (Real.sqrt_eq_rpow _).symm
    rw [hsqrt, div_le_iff₀ (Real.sqrt_pos.mpr (by norm_num))]
    simpa [mul_comm] using hmain
  refine ⟨(c : ℝ) * Real.sqrt 2, ?_⟩
  have hge1 : ∀ᶠ H : ℕ in atTop, (1 : ℝ) ≤ (H : ℝ) :=
    (eventually_ge_atTop (1 : ℕ)).mono (fun H h => by exact_mod_cast h)
  filter_upwards [hthr, hY, eventually_one_add_log_caseICapM n M (2 * c) hn hM, hge1,
    eventually_ge_atTop (1 : ℕ)] with H hthr hY hlog hge1 hH1
  have hHpos : (0 : ℝ) < (H : ℝ) := lt_of_lt_of_le one_pos hge1
  have h1 := CaseIFullBoxM_ncard_le_sum n M H c hn hM (by omega : 1 ≤ H) hper
  have h2 := caseIFullM_sum_le_tail n M H c hn hM (by omega : 1 ≤ H) hc hthr.1 hthr.2
  have h3 : ((CaseIFullBoxM n M H).ncard : ℝ) ≤
      (c : ℝ) * (H : ℝ) ^ n *
        ((1 + Real.log (caseICap n H : ℝ)) ^ (2 * c) /
          (caseIThrFM M H : ℝ) ^ ((1 : ℝ) / 2)) := le_trans h1 h2
  have hbr : (1 + Real.log (caseICap n H : ℝ)) ^ (2 * c) /
        (caseIThrFM M H : ℝ) ^ ((1 : ℝ) / 2) ≤
      (H : ℝ) ^ ((2 : ℝ) / (M : ℝ)) /
        ((H : ℝ) ^ ((1 : ℝ) + 2 / (M : ℝ)) / Real.sqrt 2) :=
    div_le_div₀ (by positivity) hlog (div_pos (by positivity) (by positivity)) hY
  have heq : (H : ℝ) ^ ((2 : ℝ) / (M : ℝ)) /
        ((H : ℝ) ^ ((1 : ℝ) + 2 / (M : ℝ)) / Real.sqrt 2) = Real.sqrt 2 / (H : ℝ) := by
    rw [show (H : ℝ) ^ ((1 : ℝ) + 2 / (M : ℝ)) =
        (H : ℝ) * (H : ℝ) ^ ((2 : ℝ) / (M : ℝ)) by
      rw [Real.rpow_add hHpos, Real.rpow_one]]
    have hHa : (H : ℝ) ^ ((2 : ℝ) / (M : ℝ)) ≠ 0 :=
      ne_of_gt (Real.rpow_pos_of_pos hHpos _)
    have hs : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
    field_simp
  have hdiv : (H : ℝ) ^ n / (H : ℝ) = (H : ℝ) ^ (n - 1) := by
    have := pow_sub₀ (H : ℝ) hHpos.ne' (show 1 ≤ n by omega)
    rw [pow_one] at this
    exact this.symm
  have hbr' : (1 + Real.log (caseICap n H : ℝ)) ^ (2 * c) /
        (caseIThrFM M H : ℝ) ^ ((1 : ℝ) / 2) ≤ Real.sqrt 2 / (H : ℝ) :=
    le_trans hbr (le_of_eq heq)
  calc ((CaseIFullBoxM n M H).ncard : ℝ)
      ≤ (c : ℝ) * (H : ℝ) ^ n *
          ((1 + Real.log (caseICap n H : ℝ)) ^ (2 * c) /
            (caseIThrFM M H : ℝ) ^ ((1 : ℝ) / 2)) := h3
    _ ≤ (c : ℝ) * (H : ℝ) ^ n * (Real.sqrt 2 / (H : ℝ)) :=
        mul_le_mul_of_nonneg_left hbr' (by positivity)
    _ = ((c : ℝ) * Real.sqrt 2) * (H : ℝ) ^ (n - 1) := by
        rw [show (c : ℝ) * (H : ℝ) ^ n * (Real.sqrt 2 / (H : ℝ)) =
            (c : ℝ) * Real.sqrt 2 * ((H : ℝ) ^ n / (H : ℝ)) by ring, hdiv]

/-- **`CaseIFull` is `O(H^(n-1))` given the per-discriminant Fourier bound**
(polynomial level). -/
theorem CaseIFullM_isBigO (n M c : ℕ) (hn : 3 ≤ n) (hM : 1 ≤ M) (hc : 1 ≤ c)
    (hMn : (2 : ℝ) + 4 / (M : ℝ) < 2 * (n : ℝ) - 1)
    (hper : PerDDiscBoundTheta n ((2 : ℝ) / (M : ℝ)) c) :
    (fun H : ℕ => ((CaseIFullM n M H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) := by
  obtain ⟨C, hC⟩ := CaseIFullBoxM_bound_real n M c hn hM hc hMn hper
  set C' : ℕ := Nat.ceil C with hC'_def
  have hCC' : C ≤ (C' : ℝ) := Nat.le_ceil C
  have hle : ∀ᶠ H : ℕ in atTop, (CaseIFullBoxM n M H).ncard ≤ C' * H ^ (n - 1) := by
    filter_upwards [hC] with H hH
    have h1 : ((CaseIFullBoxM n M H).ncard : ℝ) ≤ (C' : ℝ) * (H : ℝ) ^ (n - 1) :=
      le_trans hH (mul_le_mul_of_nonneg_right hCC' (by positivity))
    exact_mod_cast h1
  have hbox : (fun H : ℕ => ((CaseIFullBoxM n M H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) :=
    (Commons.Analysis.Asymptotics.isBigO_of_eventually_le _ _ hle).trans
      (Commons.Analysis.Asymptotics.isBigO_of_natCast_le_mul_pow (n - 1) C'
        (fun H => C' * H ^ (n - 1)) (Eventually.of_forall (fun H => le_rfl)))
  -- transfer to the polynomial level
  have himg : ∀ H, CaseIFullM n M H = Subtype.val '' (CaseIFullBoxM n M H) := by
    intro H
    ext f
    constructor
    · rintro ⟨h, hbox, h1, h2, h3⟩
      exact ⟨⟨f, hbox⟩, ⟨h, h1, h2, h3⟩, rfl⟩
    · rintro ⟨g, ⟨h, h1, h2, h3⟩, rfl⟩
      exact ⟨h, g.2, h1, h2, h3⟩
  have hle2 : ∀ᶠ H : ℕ in atTop,
      (CaseIFullM n M H).ncard ≤ (CaseIFullBoxM n M H).ncard :=
    Eventually.of_forall (fun H => by
      rw [himg H]
      exact le_of_eq (Set.ncard_image_of_injective _ Subtype.val_injective))
  exact (Commons.Analysis.Asymptotics.isBigO_of_eventually_le _ _ hle2).trans hbox
end
end Submission.Vdw
