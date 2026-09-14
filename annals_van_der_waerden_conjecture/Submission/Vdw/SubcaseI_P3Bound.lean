import Mathlib
import Submission.Vdw.FourierIndexBound
import Submission.Commons.Data.Nat.exists_dvd_mul_le_of_primeFactors_lt
import Submission.Commons.Algebra.BigOperators.prod_filter_lt_split
import Submission.Commons.Algebra.BigOperators.prod_filter_lt_le
import Submission.Commons.NumberTheory.Nat.coprime_iff_forall_primeFactors_not_dvd
import Submission.Commons.Data.Set.ncard_eq_natCard
import Submission.Commons.Data.Nat.eventually_heightCap_le_pow
import Submission.Commons.Analysis.ExpLog.eventually_one_add_log_pow_le_rpow
import Submission.Commons.Analysis.Asymptotics.isBigO_of_natCast_le_mul_pow

open Polynomial Filter Asymptotics
open scoped BigOperators
open Function
open vanDerWaerdenConjecture

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-!
# Case III, subcase (i): interface for the window construction (definitions only)

Bhargava's Case III, subcase (i) (`A_f = ∏_{p | C_f, p > H^(δ/2)} p ≤ H`,
`C_f > H^(1+δ)`) is counted by the Case-I argument applied at an
*intermediate divisor* `B` of `C_f`: the paper takes `B` between `H^(1+δ/2)`
and `H^(1+δ)` with `A_f | B | C_f`, sets `D' := ∏_{p | B} p^(v_p(D_f))`
(so `D' > H^(2+δ)`), and applies the per-modulus Fourier bound (the paper's
Corollary `fbound2`, formalized as `FourierIndexBound.PerIrrBound`) to the
index conditions at the primes of `B`:

    #{f ∈ Box n H : ∀ p | B, index_p(f̄) ≥ v_p(D')} ≤ c^(ω(D'))·H^n/D',

summed over the squarefull tail `D' > H^(2+δ)` (`CaseITail.squarefull_tail_bound`).

This module fixes the *interface* of that construction (the definitions), so
that the remaining proof work — the region-membership lemma, the sum bound and
the big-O — has a concrete target:

* `sub1Thr n H = ⌊H^(1+1/(4n))/2⌋` — the lower end of the window (halved so
  that `sub1Thr·⌈H^(1/(4n))⌉ ≤ H^(1+1/(2n))`, see below);
* `midPart n H C`, `smallPart n C` — the three-way split of
  `C = radical D` into the primes `≥ ⌈H^(1/(4n))⌉` (`largePart`), the primes
  `n < p < ⌈H^(1/(4n))⌉` and the primes `p ≤ n`;
* `sub1Mod n D B = ∏_{p | B} p^(v_p(D))` — the squarefull number attached to
  an admissible modulus `B | radical D`;
* `sub1Sieve n H D'` — the index-condition set at `D'`;
* `sub1Index n H` — the candidate values of `D'` (finitely many, so that the
  counting can be summed over them).

**Window arithmetic.**  With `X = sub1Thr n H = ⌊H^(1+1/(4n))/2⌋` and
`Y = ⌈H^(1/(4n))⌉` one has `X·Y ≤ H^(1+1/(2n))` (using
`⌊x/2⌋ ≤ x/2`, `⌈y⌉ ≤ y+1` and `H^(1+1/(4n)) ≤ H^(1+1/(2n))`), and — because
`M := largePart C Y ≤ H ≤ X` and `M·S ≥ C/S₀(n) > H^(1+δ)/S₀(n) ≥ H^(1+1/(4n)) ≥ X`
(with `S = midPart`, `S₀ = smallConst n ≤ H^(1/(4n))`) — the commons greedy
lemma `Commons.Data.Nat.exists_dvd_mul_le_of_primeFactors_lt`
(`M ≤ X`, `X ≤ M·S`, `∀ p ∈ S.primeFactors, p < Y` give
`∃ B, B | M·S, X ≤ B, (B:ℝ) < (X:ℝ)·(Y:ℝ)`) produces a divisor
`B | C` with `X ≤ B < H^(1+δ)`, whose prime factors are all `> n`
(the primes of `M` are `≥ Y > n`, those of `S` are `> n` by construction).
This is the window divisor of the paper, and `sub1Mod n D B` is the
associated squarefull number with `radical = B ≤ H^(1+δ)`, `D' | D` and
`D' ≥ B² ≥ X² > H^(2+δ)` — the inputs of `PerIrrBound` and of the squarefull
tail.

The remaining glue (a future session) is: (i) the Finset identity
`radical D = largePart C Y · midPart n H C · smallPart n C` (two applications
of `Finset.prod_filter_mul_prod_filter_not`), giving `M·S ≥ C/S₀` and
`S₀ ≤ smallConst n`; (ii) `sub1Mod` bookkeeping (`sub1Mod dvd D`,
`primeFactors (sub1Mod n D B) = B.primeFactors`, `Squarefull (sub1Mod …)`,
`radical (sub1Mod n D B) = B`, `factorization` monotonicity via
`Nat.factorization_le_iff_dvd`); (iii) the region membership
`SubcaseI_P3 n H ⊆ ⋃_{D' ∈ sub1Index} sub1Sieve n H D'` (eventually in `H`);
(iv) the sum/tail/big-O assembly, mirroring `CaseIRegion`.  With those, the
`SubcaseI_P3` residual of `FinalAssembly` is *implied by* `PerIrrBound`, so the
challenge theorem reduces to THREE literature inputs (`PerIrrBound`,
`SubcaseI_P2`, `ImprimitiveBad`).

Axioms: none (only definitions here).
-/

namespace Submission.Vdw

noncomputable section

/-- The window threshold `X = ⌊H^(1+1/(4n))/2⌋`. -/
def sub1Thr (n H : ℕ) : ℕ := Nat.floor (((H : ℝ) ^ (1 + 1 / (4 * (n : ℝ)))) / 2)

/-- The medium-prime part of `C`: the product of the primes `n < p < ⌈H^(1/(4n))⌉`. -/
def midPart (n H C : ℕ) : ℕ :=
  ∏ p ∈ C.primeFactors.filter (fun p => n < p ∧ p < lowerThr (4 * n) H), p

/-- The `≤ n` part of `C`. -/
def smallPart (n C : ℕ) : ℕ := ∏ p ∈ C.primeFactors.filter (fun p => p ≤ n), p

/-- The squarefull number attached to a modulus `B`: `∏_{p | B} p^(v_p(D))`. -/
def sub1Mod (D B : ℕ) : ℕ := ∏ p ∈ B.primeFactors, p ^ D.factorization p

/-- The sieve set at modulus `D'`: the index conditions with the exponents of `D'`. -/
def sub1Sieve (n H : ℕ) (D' : ℕ) : Set ↥(Box n H) :=
  {f | ∀ p : D'.primeFactors, indexClass (F := ZMod (p : ℕ)) n (D'.factorization (p : ℕ))
        (boxResidue n H (p : ℕ) f)}

/-- The candidate discriminants of the subcase-(i) windows. -/
def sub1Index (n H : ℕ) : Finset ℕ :=
  ((Finset.Icc 1 (caseICap n H)).filter Squarefull).filter
    (fun D' => sub1Thr n H ≤ radical D' ∧
      (∀ p ∈ D'.primeFactors, n < p) ∧
      (∀ p ∈ D'.primeFactors, D'.factorization p < n) ∧
      (radical D' : ℝ) ≤ (H : ℝ) ^ (1 + 1 / (2 * (n : ℝ))))


/-! ## The attached squarefull number `sub1Mod` -/

lemma sub1Mod_dvd {D B : ℕ} (hD : D ≠ 0) (hB : B ∣ D) : sub1Mod D B ∣ D := by
  have h := Finset.prod_dvd_prod_of_subset B.primeFactors D.primeFactors
    (fun p => p ^ D.factorization p) (primeFactors_subset_of_dvd hB hD)
  rwa [← Nat.prod_primeFactors_pow_factorization hD] at h

lemma sub1Mod_ne_zero {D B : ℕ} (hD : D ≠ 0) (hB : B ∣ D) : sub1Mod D B ≠ 0 := by
  have h := sub1Mod_dvd hD hB
  intro h0
  exact hD (Nat.zero_dvd.mp (h0 ▸ h))

lemma sub1Mod_factorization_le {D B p : ℕ} (hD : D ≠ 0) (hB : B ∣ D) :
    (sub1Mod D B).factorization p ≤ D.factorization p :=
  Finsupp.le_def.mp
    ((Nat.factorization_le_iff_dvd (sub1Mod_ne_zero hD hB) hD).mpr (sub1Mod_dvd hD hB)) p

lemma sub1Mod_primeFactors {D B : ℕ} (hD : D ≠ 0) (hB : B ∣ D) :
    (sub1Mod D B).primeFactors = B.primeFactors := by
  classical
  have hne : sub1Mod D B ≠ 0 := sub1Mod_ne_zero hD hB
  refine subset_antisymm ?_ ?_
  · intro q hq
    rw [Nat.mem_primeFactors] at hq
    obtain ⟨hqq, hqd, _⟩ := hq
    obtain ⟨p, hp, hpq⟩ :=
      ((hqq.prime).dvd_finsetProd_iff (fun r => r ^ D.factorization r)).mp hqd
    have hpp : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
    have hqp : q = p := by
      rcases hpp.eq_one_or_self_of_dvd q (Nat.Prime.dvd_of_dvd_pow hqq hpq) with h | h
      · exact absurd h hqq.ne_one
      · exact h
    rw [hqp]
    exact hp
  · intro q hq
    have hqmem : q ∈ B.primeFactors := hq
    rw [Nat.mem_primeFactors] at hq ⊢
    obtain ⟨hqq, hqd, _⟩ := hq
    have hqD : q ∣ D := dvd_trans hqd hB
    have hone : D.factorization q ≠ 0 := by
      have h1 := (hqq.dvd_iff_one_le_factorization hD).mp hqD
      omega
    refine ⟨hqq, ?_, hne⟩
    exact dvd_trans (dvd_pow_self q hone)
      (Finset.dvd_prod_of_mem (fun r => r ^ D.factorization r) hqmem)

lemma sub1Mod_squarefull {D B : ℕ} (hD : D ≠ 0) (hB : B ∣ D) (hsq : Squarefull D) :
    Squarefull (sub1Mod D B) := by
  classical
  intro q hqq hqd
  obtain ⟨p, hp, hpq⟩ :=
    ((hqq.prime).dvd_finsetProd_iff (fun r => r ^ D.factorization r)).mp hqd
  have hpp : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
  have hqp : q = p := by
    rcases hpp.eq_one_or_self_of_dvd q (Nat.Prime.dvd_of_dvd_pow hqq hpq) with h | h
    · exact absurd h hqq.ne_one
    · exact h
  have hpD : p ∣ D := dvd_trans (Nat.dvd_of_mem_primeFactors hp) hB
  have h2 : 2 ≤ D.factorization p := by
    have h := hsq p hpp hpD
    rwa [Nat.Prime.pow_dvd_iff_le_factorization hpp hD] at h
  rw [hqp]
  exact dvd_trans (pow_dvd_pow p h2)
    (Finset.dvd_prod_of_mem (fun r => r ^ D.factorization r) hp)

lemma sub1Mod_mem_primeFactors_iff {D B p : ℕ} (hD : D ≠ 0) (hB : B ∣ D) :
    p ∈ (sub1Mod D B).primeFactors ↔ p ∈ B.primeFactors := by
  rw [sub1Mod_primeFactors hD hB]

lemma sub1Mod_radical {D B : ℕ} (hD : D ≠ 0) (hB : B ∣ D) (hsqB : Squarefree B) :
    radical (sub1Mod D B) = B := by
  rw [radical_eq_prod_primeFactors, sub1Mod_primeFactors hD hB]
  exact Nat.prod_primeFactors_of_squarefree hsqB


/-! ## The three-way split of `radical D` -/

/-- `radical D` factors as the large-prime part (`≥ ⌈H^(1/(4n))⌉`), the
medium-prime part (`n < p < ⌈H^(1/(4n))⌉`) and the `≤ n` part. -/
theorem radical_split {D n H : ℕ} (hnY : n < lowerThr (4 * n) H) :
    largePart (radical D) (lowerThr (4 * n) H) * midPart n H (radical D) *
      smallPart n (radical D) = radical D := by
  have hprod : (∏ p ∈ (radical D).primeFactors, p) = radical D := by
    show (∏ p ∈ (radical D).primeFactors, p) = ∏ p ∈ D.primeFactors, p
    rw [radical_primeFactors D]
  unfold largePart midPart smallPart
  rw [mul_assoc, ← Commons.Algebra.BigOperators.prod_filter_lt_split
      (s := (radical D).primeFactors) hnY, mul_comm,
    ← Commons.Algebra.BigOperators.prod_filter_lt_le (s := (radical D).primeFactors)
      (lowerThr (4 * n) H)]
  exact hprod

/-- The `≤ n` part of `radical D` is bounded by the `≤ n` part of `D`. -/
lemma smallPart_le_discSmallPart (n D : ℕ) (hD : D ≠ 0) :
    smallPart n (radical D) ≤ discSmallPart n D := by
  unfold smallPart discSmallPart
  rw [radical_primeFactors D]
  refine Finset.prod_le_prod (fun p _ => Nat.zero_le p) (fun p hp => ?_)
  have hpp : Nat.Prime p := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
  have hpD : p ∣ D := Nat.dvd_of_mem_primeFactors (Finset.mem_filter.mp hp).1
  calc p = p ^ 1 := (pow_one p).symm
    _ ≤ p ^ D.factorization p :=
        pow_le_pow_right₀ hpp.one_le ((hpp.dvd_iff_one_le_factorization hD).mp hpD)

/-- The `≤ n` part of the radical of a field discriminant is bounded by the
small-prime cap `smallConst n`. -/
lemma smallPart_fieldDisc_le_smallConst (f : ℤ[X]) [Fact (Irreducible (f.map φℚ))]
    (hf : f.Monic) (n : ℕ) (hdeg : f.natDegree = n) :
    smallPart n (radical (fieldDisc f)) ≤ smallConst n :=
  le_trans (smallPart_le_discSmallPart n (fieldDisc f) (fieldDisc_ne_zero f))
    (discSmallPart_fieldDisc_le f hf n hdeg)


/-! ## The window arithmetic -/

/-- The window arithmetic: `sub1Thr·⌈H^(1/(4n))⌉ ≤ H^(1+δ)`. -/
lemma sub1Thr_mul_lowerThr_le (n H : ℕ) (hn : 1 ≤ n) (hH : 1 ≤ H) :
    (sub1Thr n H : ℝ) * (lowerThr (4 * n) H : ℝ) ≤
      (H : ℝ) ^ (1 + 1 / (2 * (n : ℝ))) := by
  have hH0 : (0 : ℝ) ≤ (H : ℝ) := by positivity
  have hH1 : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
  have hHpos : (0 : ℝ) < (H : ℝ) := by
    have h1 : (0 : ℕ) < H := by omega
    exact_mod_cast h1
  have h1 : (sub1Thr n H : ℝ) ≤ ((H : ℝ) ^ (1 + 1 / (4 * (n : ℝ)))) / 2 := by
    rw [sub1Thr]
    exact Nat.floor_le (by positivity)
  have h2 : (lowerThr (4 * n) H : ℝ) ≤ (H : ℝ) ^ ((1 : ℝ) / (4 * (n : ℝ))) + 1 := by
    have h := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ (H : ℝ) ^ ((1 : ℝ) / (4 * (n : ℝ))) by
      positivity)
    have hcast : ((Nat.ceil ((H : ℝ) ^ ((1 : ℝ) / (4 * (n : ℝ))))) : ℝ) =
        (lowerThr (4 * n) H : ℝ) := by
      simp [lowerThr, Commons.Analysis.ExpLog.lowerThreshold]
    rw [← hcast]
    exact le_of_lt h
  have h3 : ((H : ℝ) ^ (1 + 1 / (4 * (n : ℝ)))) / 2 *
      ((H : ℝ) ^ ((1 : ℝ) / (4 * (n : ℝ))) + 1) ≤ (H : ℝ) ^ (1 + 1 / (2 * (n : ℝ))) := by
    have hmul : ((H : ℝ) ^ (1 + 1 / (4 * (n : ℝ)))) *
        ((H : ℝ) ^ ((1 : ℝ) / (4 * (n : ℝ)))) = (H : ℝ) ^ (1 + 1 / (2 * (n : ℝ))) := by
      rw [← Real.rpow_add hHpos]
      congr 1
      field_simp
      ring
    have hle : (1 : ℝ) ≤ (H : ℝ) ^ (1 + 1 / (2 * (n : ℝ))) := by
      calc (1 : ℝ) = (1 : ℝ) ^ (1 + 1 / (2 * (n : ℝ))) := by rw [Real.one_rpow]
        _ ≤ (H : ℝ) ^ (1 + 1 / (2 * (n : ℝ))) :=
            Real.rpow_le_rpow (by norm_num) hH1 (by positivity)
    have hmono : (1 : ℝ) ≤ (H : ℝ) ^ (1 + 1 / (4 * (n : ℝ))) := by
      calc (1 : ℝ) = (1 : ℝ) ^ (1 + 1 / (4 * (n : ℝ))) := by rw [Real.one_rpow]
        _ ≤ (H : ℝ) ^ (1 + 1 / (4 * (n : ℝ))) :=
            Real.rpow_le_rpow (by norm_num) hH1 (by positivity)
    have hexp : (H : ℝ) ^ (1 + 1 / (4 * (n : ℝ))) ≤ (H : ℝ) ^ (1 + 1 / (2 * (n : ℝ))) := by
      apply Real.rpow_le_rpow_of_exponent_le hH1
      have hn0 : (0 : ℝ) < (n : ℝ) := by
        have h1 : (0 : ℕ) < n := by omega
        exact_mod_cast h1
      have hthis : (1 : ℝ) / (4 * (n : ℝ)) ≤ 1 / (2 * (n : ℝ)) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        linarith
      linarith
    nlinarith [hmul, hle, hmono, hexp]
  calc (sub1Thr n H : ℝ) * (lowerThr (4 * n) H : ℝ)
      ≤ ((H : ℝ) ^ (1 + 1 / (4 * (n : ℝ)))) / 2 *
          ((H : ℝ) ^ ((1 : ℝ) / (4 * (n : ℝ))) + 1) :=
        mul_le_mul h1 h2 (by positivity) (by positivity)
    _ ≤ (H : ℝ) ^ (1 + 1 / (2 * (n : ℝ))) := h3



/-! ## Squarefreeness of the two parts and their coprimality -/

/-- The prime support of `midPart n H C`. -/
lemma midPart_primeFactors (n H C : ℕ) :
    (midPart n H C).primeFactors =
      C.primeFactors.filter (fun p => n < p ∧ p < lowerThr (4 * n) H) := by
  rw [midPart]
  exact Nat.primeFactors_prod (fun p hp =>
    Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1)

lemma midPart_squarefree (n H C : ℕ) : Squarefree (midPart n H C) := by
  rw [midPart]
  exact squarefree_prod_primes (fun p hp =>
    Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1)

lemma midPart_ne_zero (n H C : ℕ) : midPart n H C ≠ 0 :=
  (midPart_squarefree n H C).ne_zero

/-- The large-prime part and the medium-prime part are coprime (their prime
supports are disjoint). -/
lemma largePart_midPart_coprime (C n H : ℕ) :
    Nat.Coprime (largePart C (lowerThr (4 * n) H)) (midPart n H C) := by
  rw [Commons.NumberTheory.Nat.coprime_iff_forall_primeFactors_not_dvd
    (q := midPart n H C) (midPart_ne_zero n H C)]
  intro p hp hpdvd
  have hpp : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
  have hplt : p < lowerThr (4 * n) H := by
    have hmem := hp
    rw [midPart_primeFactors n H C] at hmem
    exact (Finset.mem_filter.mp hmem).2.2
  have hle : lowerThr (4 * n) H ≤ p := by
    have hmem : p ∈ (largePart C (lowerThr (4 * n) H)).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hpp, hpdvd, (squarefree_largePart C _).ne_zero⟩
    rw [largePart_primeFactors C (lowerThr (4 * n) H)] at hmem
    exact (Finset.mem_filter.mp hmem).2
  omega

/-- `largePart · midPart` is squarefree. -/
lemma largePart_mul_midPart_squarefree (C n H : ℕ) :
    Squarefree (largePart C (lowerThr (4 * n) H) * midPart n H C) :=
  squarefree_mul_iff.mpr
    ⟨Nat.coprime_iff_isRelPrime.mp (largePart_midPart_coprime C n H),
      squarefree_largePart C _, midPart_squarefree n H C⟩


/-! ## Region membership for the subcase-(i) window -/

/-- **Region membership.**  Every member of the subcase-(i) region
`SubcaseI_P3 n H` lies in the sieve set of a candidate window
`D' ∈ sub1Index n H` (eventually in `H`). -/
theorem SubcaseI_P3_subset_biUnion (n H : ℕ) (hn : 3 ≤ n) (hH : 1 ≤ H)
    (hX : H ≤ sub1Thr n H)
    (hS0 : (smallConst n : ℝ) ≤ (H : ℝ) ^ ((1 : ℝ) / (4 * (n : ℝ))))
    (hnY : n < lowerThr (4 * n) H) :
    {f : ↥(Box n H) | f.1 ∈ SubcaseI_P3 n H} ⊆
      {f : ↥(Box n H) | ∃ D' ∈ sub1Index n H, f ∈ sub1Sieve n H D'} := by
  classical
  intro f hf
  obtain ⟨hsub, hCw, hC⟩ := hf
  have hsubmem : f.1 ∈ SubcaseI n H := hsub
  obtain ⟨hbad, hSI, hgal, hdd, hA⟩ := hsub
  haveI : Fact (Irreducible (f.1.map φℚ)) := ⟨hSI⟩
  have hmon : f.1.Monic := f.2.1
  have hdeg : f.1.natDegree = n := Polynomial.natDegree_eq_of_degree_eq_some f.2.2.1
  have hbox : f.1 ∈ Box n H := f.2
  set Y := lowerThr (4 * n) H with hY
  set D := fieldDisc f.1 with hD
  have hD0 : D ≠ 0 := fieldDisc_ne_zero f.1
  set M := largePart (radical D) Y with hM
  set S := midPart n H (radical D) with hS
  set S₀ := smallPart n (radical D) with hS0'
  -- `M ≤ H`
  have hMH : M ≤ H := by
    have hA' : ¬ (H < M) := by
      have h1 : A_large n H f.1 hSI = M := by
        simp only [A_large, ramifiedProduct, hM, hD, hY, fieldDiscExp]
      rw [h1] at hA
      exact hA
    omega
  -- squarefullness of `D`
  have hsqD : Squarefull D := by
    obtain ⟨_, _, hsq'⟩ := PrimitiveBad_exists_squarefull_fieldDisc n H f.1
      (SubcaseI_subset_PrimitiveBad n H hsubmem)
    simpa [hD, fieldDiscExp] using hsq'
  -- the split and the small-prime cap
  have hsplit : M * S * S₀ = radical D := by
    rw [hM, hS, hS0']
    rw [hY]
    exact radical_split hnY
  have hS0le : S₀ ≤ smallConst n := by
    rw [hS0', hD]
    exact smallPart_fieldDisc_le_smallConst f.1 hmon n hdeg
  have hClarge : (H : ℝ) ^ (1 + 1 / (2 * (n : ℝ))) < (radical D : ℝ) := by
    have hEq : radical (fieldDiscExp f.1 hCw) = radical D := rfl
    rw [← hEq]
    exact hC
  -- `X ≤ M·S`
  have hXMS : sub1Thr n H ≤ M * S := by
    have hsm : (0 : ℝ) < (smallConst n : ℝ) := by exact_mod_cast smallConst_pos n
    have h1 : (radical D : ℝ) ≤ ((M * S : ℕ) : ℝ) * (smallConst n : ℝ) := by
      have h2 : (S₀ : ℝ) ≤ (smallConst n : ℝ) := by exact_mod_cast hS0le
      have h3 : (radical D : ℝ) = ((M * S : ℕ) : ℝ) * (S₀ : ℝ) := by
        rw [← hsplit]
        push_cast
        ring
      rw [h3]
      exact mul_le_mul_of_nonneg_left h2 (by positivity)
    have h2 : (H : ℝ) ^ (1 + 1 / (2 * (n : ℝ))) / (smallConst n : ℝ) ≤ ((M * S : ℕ) : ℝ) := by
      rw [div_le_iff₀ hsm]
      exact le_trans (le_of_lt hClarge) h1
    have h3 : 2 * sub1Thr n H ≤ (H : ℝ) ^ (1 + 1 / (4 * (n : ℝ))) := by
      have h := Nat.floor_le (show (0 : ℝ) ≤
        ((H : ℝ) ^ (1 + 1 / (4 * (n : ℝ)))) / 2 by positivity)
      rw [sub1Thr]
      push_cast
      linarith
    have h4 : (H : ℝ) ^ (1 + 1 / (4 * (n : ℝ))) ≤
        (H : ℝ) ^ (1 + 1 / (2 * (n : ℝ))) / (smallConst n : ℝ) := by
      rw [le_div_iff₀ hsm]
      calc (H : ℝ) ^ (1 + 1 / (4 * (n : ℝ))) * (smallConst n : ℝ)
          ≤ (H : ℝ) ^ (1 + 1 / (4 * (n : ℝ))) *
              (H : ℝ) ^ ((1 : ℝ) / (4 * (n : ℝ))) :=
            mul_le_mul_of_nonneg_left hS0 (by positivity)
        _ = (H : ℝ) ^ (1 + 1 / (2 * (n : ℝ))) := by
            rw [← Real.rpow_add (by
              have h1 : (0 : ℕ) < H := by omega
              exact_mod_cast h1 : (0 : ℝ) < (H : ℝ))]
            congr 1
            ring
    have h5 : (sub1Thr n H : ℝ) ≤ ((M * S : ℕ) : ℝ) := by linarith
    exact_mod_cast h5
  -- the greedy divisor
  have hM1 : 1 ≤ M := by
    rw [hM]
    exact Finset.one_le_prod (fun p _ =>
      (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp ‹p ∈ _›).1).one_le)
  have hSSq : ∀ p ∈ S.primeFactors, p < Y := by
    intro p hp
    rw [midPart_primeFactors n H (radical D)] at hp
    exact (Finset.mem_filter.mp hp).2.2
  have hY1 : 1 < Y := by omega
  obtain ⟨B, hBdvd, hXB, hBX⟩ :=
    Commons.Data.Nat.exists_dvd_mul_le_of_primeFactors_lt M S (sub1Thr n H) Y
      hM1 (le_trans hMH hX) hY1 hXMS hSSq
  -- `M·S` is squarefree, so `B` is squarefree
  have hBsq : Squarefree B :=
    (largePart_mul_midPart_squarefree (radical D) n H).squarefree_of_dvd (by
      simpa [hM, hS] using hBdvd)
  have hMSne : M * S ≠ 0 := (largePart_mul_midPart_squarefree (radical D) n H).ne_zero
  have hBD : B ∣ D := by
    have h2 : M * S ∣ radical D := ⟨S₀, hsplit.symm⟩
    have h3 : radical D ∣ D := by
      rw [radical_eq_prod_primeFactors]
      exact Nat.prod_primeFactors_dvd D
    exact dvd_trans hBdvd (dvd_trans h2 h3)
  -- the primes of `B` exceed `n`
  have hBgt : ∀ p ∈ B.primeFactors, n < p := by
    intro p hp
    have hpp : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
    have hpMS : p ∣ M * S := dvd_trans (Nat.dvd_of_mem_primeFactors hp) hBdvd
    rcases hpp.dvd_mul.mp hpMS with hpM | hpS
    · have hmem : p ∈ (largePart (radical D) Y).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hpp, hpM, (squarefree_largePart (radical D) Y).ne_zero⟩
      have h2 : Y ≤ p := by
        rw [largePart_primeFactors (radical D) Y] at hmem
        exact (Finset.mem_filter.mp hmem).2
      omega
    · have hmem : p ∈ (midPart n H (radical D)).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hpp, hpS, midPart_ne_zero n H (radical D)⟩
      rw [midPart_primeFactors n H (radical D)] at hmem
      exact (Finset.mem_filter.mp hmem).2.1
  -- the window is `< H^(1+δ)`
  have hBlt : (B : ℝ) < (H : ℝ) ^ (1 + 1 / (2 * (n : ℝ))) :=
    lt_of_lt_of_le hBX (sub1Thr_mul_lowerThr_le n H (by omega) hH)
  -- conclusion
  refine ⟨sub1Mod D B, ?_, ?_⟩
  · rw [sub1Index, Finset.mem_filter, Finset.mem_filter]
    have h1le : 1 ≤ sub1Mod D B := by
      rw [sub1Mod]
      refine Finset.one_le_prod (fun p hp => ?_)
      have hpp : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
      have hpD : p ∣ D := dvd_trans (Nat.dvd_of_mem_primeFactors hp) hBD
      have hv : D.factorization p ≠ 0 := by
        have h1 := (hpp.dvd_iff_one_le_factorization hD0).mp hpD
        omega
      exact hpp.one_le.trans (Nat.le_self_pow hv p)
    have hDle : sub1Mod D B ≤ caseICap n H := by
      have h1 : sub1Mod D B ∣ D := sub1Mod_dvd hD0 hBD
      have h2 : D ≤ caseICap n H := fieldDisc_height_bound f.1 hmon n H hdeg
        (fun k hk => f.2.2.2 k hk)
      exact le_trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hD0) h1) h2
    have hIcc : sub1Mod D B ∈ Finset.Icc 1 (caseICap n H) :=
      Finset.mem_Icc.mpr ⟨h1le, hDle⟩
    refine ⟨⟨hIcc, ?_⟩, ?_, ?_, ?_, ?_⟩
    · exact sub1Mod_squarefull hD0 hBD hsqD
    · rw [sub1Mod_radical hD0 hBD hBsq]
      exact hXB
    · intro p hp
      exact hBgt p ((sub1Mod_mem_primeFactors_iff hD0 hBD).mp hp)
    · intro p hp
      have hpB : p ∈ B.primeFactors := (sub1Mod_mem_primeFactors_iff hD0 hBD).mp hp
      have hpp : Nat.Prime p := Nat.prime_of_mem_primeFactors hpB
      haveI : Fact (Nat.Prime p) := ⟨hpp⟩
      have hpgt : n < p := hBgt p hpB
      have hpD : p ∣ D := dvd_trans (Nat.dvd_of_mem_primeFactors hpB) hBD
      have h1 : D.factorization p < n := by
        rw [hD]
        exact fieldDisc_factorization_lt_of_prime_gt n H (by omega) f.1 hmon hdeg hbox hpgt
          (by simpa [hD] using hpD)
      exact lt_of_le_of_lt (sub1Mod_factorization_le hD0 hBD) h1
    · rw [sub1Mod_radical hD0 hBD hBsq]
      exact le_of_lt hBlt
  · intro p
    have hpB : (p : ℕ) ∈ B.primeFactors := (sub1Mod_mem_primeFactors_iff hD0 hBD).mp p.2
    have hpp : Nat.Prime (p : ℕ) := Nat.prime_of_mem_primeFactors hpB
    haveI : Fact (Nat.Prime (p : ℕ)) := ⟨hpp⟩
    have hpgt : n < (p : ℕ) := hBgt p hpB
    have hpD : (p : ℕ) ∣ D := dvd_trans (Nat.dvd_of_mem_primeFactors hpB) hBD
    have h1 : (D.factorization (p : ℕ)) ≤ boxIndex (p : ℕ) n H f := by
      have hentry := restrictedSieve_entry f.1 hmon hdeg (by omega) hpgt
        (by simpa [hD] using hpD)
      simpa [boxIndex, reductionPoly, hD] using hentry
    exact (boxIndex_iff_indexClass (p : ℕ) n H ((sub1Mod D B).factorization (p : ℕ)) f).mp
      (le_trans (sub1Mod_factorization_le hD0 hBD) h1)


/-! ## The counting bound and the `O(H^(n-1))` estimate -/

/-- The polynomial-level count of a set inside the box is at most the count of
its box-level counterpart. -/
lemma ncard_le_ncard_box {n H : ℕ} {s : Set ℤ[X]} (hs : s ⊆ Box n H) :
    s.ncard ≤ ({f : ↥(Box n H) | f.1 ∈ s} : Set ↥(Box n H)).ncard := by
  classical
  haveI : Fintype ↥s := ((box_finite n H).subset hs).fintype
  haveI : Fintype ↥({f : ↥(Box n H) | f.1 ∈ s} : Set ↥(Box n H)) := Set.toFinite _ |>.fintype
  rw [Commons.Data.Set.ncard_eq_natCard s,
    Commons.Data.Set.ncard_eq_natCard ({f : ↥(Box n H) | f.1 ∈ s} : Set ↥(Box n H))]
  exact Nat.card_le_card_of_injective
    (fun x : s => (⟨⟨x.1, hs x.2⟩, x.2⟩ : {f : ↥(Box n H) | f.1 ∈ s}))
    (fun x y hxy => Subtype.ext (congrArg (fun t : {f : ↥(Box n H) | f.1 ∈ s} => (t.1.1 : ℤ[X])) hxy))

/-- The polynomial-level count of `SubcaseI_P3 n H` is at most the sum over the
candidate windows of the `PerIrrBound` bounds. -/
theorem SubcaseI_P3_ncard_le_sum (n c H : ℕ) (hn : 3 ≤ n) (hc : 1 ≤ c)
    (h : PerIrrBound n c) (hH : 2 ≤ H) (hX : H ≤ sub1Thr n H)
    (hS0 : (smallConst n : ℝ) ≤ (H : ℝ) ^ ((1 : ℝ) / (4 * (n : ℝ))))
    (hnY : n < lowerThr (4 * n) H) :
    (({f : ↥(Box n H) | f.1 ∈ SubcaseI_P3 n H} : Set ↥(Box n H)).ncard : ℝ) ≤
      ∑ D' ∈ sub1Index n H, (c : ℝ) ^ omega D' * (H : ℝ) ^ n / (D' : ℝ) := by
  classical
  have hmem := SubcaseI_P3_subset_biUnion n H hn (by omega : 1 ≤ H) hX hS0 hnY
  have hfin : ({f : ↥(Box n H) | ∃ D' ∈ sub1Index n H, f ∈ sub1Sieve n H D'} :
      Set ↥(Box n H)).Finite := Set.toFinite _
  have hcard := Set.ncard_le_ncard hmem hfin
  have h2 := ncard_biUnion_finset_le (sub1Index n H) (sub1Sieve n H)
  have h3 : ∀ D' ∈ sub1Index n H, ((sub1Sieve n H D').ncard : ℝ) ≤
      (c : ℝ) ^ omega D' * (H : ℝ) ^ n / (D' : ℝ) := by
    intro D' hD'
    rw [sub1Index, Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc] at hD'
    obtain ⟨⟨hIcc, hsq⟩, hXle, hgt, hfac, hrad⟩ := hD'
    have hD0 : D' ≠ 0 := by have := hIcc.1; omega
    have hD'2 : 2 ≤ D' := by
      by_contra hcon
      push_neg at hcon
      have hD'1 : D' = 1 := by omega
      have h2 : sub1Thr n H ≤ 1 := by
        have h3 : radical D' = 1 := by rw [hD'1]; simp [radical]
        rw [h3] at hXle
        exact hXle
      omega
    have hsieve := h H D' hD0 hsq hD'2 hgt hrad hfac
    have hbridge : (sub1Sieve n H D').ncard = Nat.card {f : ↥(Box n H) //
        ∀ p : D'.primeFactors, indexClass (F := ZMod (p : ℕ)) n (D'.factorization (p : ℕ))
          (boxResidue n H (p : ℕ) f)} := (Nat.card_coe_set_eq _).symm
    rw [hbridge]
    exact hsieve
  calc (({f : ↥(Box n H) | f.1 ∈ SubcaseI_P3 n H} : Set ↥(Box n H)).ncard : ℝ)
      ≤ (({f : ↥(Box n H) | ∃ D' ∈ sub1Index n H, f ∈ sub1Sieve n H D'} :
          Set ↥(Box n H)).ncard : ℝ) := by exact_mod_cast hcard
    _ ≤ ((∑ D' ∈ sub1Index n H, (sub1Sieve n H D').ncard : ℕ) : ℝ) := by exact_mod_cast h2
    _ = ∑ D' ∈ sub1Index n H, ((sub1Sieve n H D').ncard : ℝ) := by rw [Nat.cast_sum]
    _ ≤ ∑ D' ∈ sub1Index n H, (c : ℝ) ^ omega D' * (H : ℝ) ^ n / (D' : ℝ) :=
        Finset.sum_le_sum h3

/-- The sum over the candidate windows is bounded by the squarefull tail. -/
theorem sub1Index_sum_le_tail (n c H : ℕ) (hc : 1 ≤ c)
    (hY1 : 1 ≤ sub1Thr n H ^ 2 - 1) (hYZ : sub1Thr n H ^ 2 - 1 < caseICap n H) :
    ∑ D' ∈ sub1Index n H, (c : ℝ) ^ omega D' * (H : ℝ) ^ n / (D' : ℝ) ≤
      (H : ℝ) ^ n * ((1 + Real.log (caseICap n H : ℝ)) ^ (2 * c) /
        ((sub1Thr n H ^ 2 - 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 2)) := by
  classical
  have htail := squarefull_tail_bound c hc ((1 : ℝ) / 2) (by norm_num) le_rfl
    (sub1Thr n H ^ 2 - 1) (caseICap n H) hY1 hYZ
  have hsub : sub1Index n H ⊆ Finset.Icc ((sub1Thr n H ^ 2 - 1) + 1) (caseICap n H) := by
    intro D' hD'
    rw [sub1Index, Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc] at hD'
    obtain ⟨⟨hIcc, hsq⟩, hXle, hgt, hfac, hrad⟩ := hD'
    have hD0 : D' ≠ 0 := by have := hIcc.1; omega
    have h1 : (radical D') ^ 2 ≤ D' := radical_sq_le_of_squarefull D' hD0 hsq
    have h2 : sub1Thr n H ≤ radical D' := hXle
    have h3 : sub1Thr n H ^ 2 ≤ (radical D') ^ 2 := Nat.pow_le_pow_left h2 2
    exact Finset.mem_Icc.mpr ⟨by omega, hIcc.2⟩
  have hsqmem : ∀ D' ∈ sub1Index n H, Squarefull D' := by
    intro D' hD'
    rw [sub1Index, Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc] at hD'
    exact hD'.1.2
  have hsum1 : ∑ D' ∈ sub1Index n H, (c : ℝ) ^ omega D' / (D' : ℝ) ≤
      ∑ D' ∈ Finset.Icc ((sub1Thr n H ^ 2 - 1) + 1) (caseICap n H),
        (if Squarefull D' then (c : ℝ) ^ omega D' / (D' : ℝ) else 0) := by
    calc ∑ D' ∈ sub1Index n H, (c : ℝ) ^ omega D' / (D' : ℝ)
        = ∑ D' ∈ sub1Index n H,
            (if Squarefull D' then (c : ℝ) ^ omega D' / (D' : ℝ) else 0) := by
          refine Finset.sum_congr rfl (fun D' hD' => ?_)
          simp [hsqmem D' hD']
      _ ≤ ∑ D' ∈ Finset.Icc ((sub1Thr n H ^ 2 - 1) + 1) (caseICap n H),
            (if Squarefull D' then (c : ℝ) ^ omega D' / (D' : ℝ) else 0) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg hsub (fun D' _ _ => ?_)
          by_cases hsq : Squarefull D'
          · simp only [hsq, if_true]
            positivity
          · simp [hsq]
  have hfactor : ∑ D' ∈ sub1Index n H, (c : ℝ) ^ omega D' * (H : ℝ) ^ n / (D' : ℝ) =
      (H : ℝ) ^ n * (∑ D' ∈ sub1Index n H, (c : ℝ) ^ omega D' / (D' : ℝ)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun D' _ => ?_)
    ring
  rw [hfactor]
  refine le_trans (mul_le_mul_of_nonneg_left hsum1 (by positivity)) ?_
  refine le_trans (mul_le_mul_of_nonneg_left
    (le_trans htail (le_of_eq rfl)) (by positivity)) ?_
  exact le_rfl


/-! ## The final assembly: `PerIrrBound` implies `SubcaseI_P3 = O(H^(n-1))`

This closes the subcase-(i) residual: the three proved ingredients
(`ncard_le_ncard_box`, `SubcaseI_P3_ncard_le_sum`, `sub1Index_sum_le_tail`)
combined with the four eventual estimates (`H ≤ sub1Thr`, log absorption
`(1+log Z)^(2c) ≤ H^(1/(4n))`, `sub1Thr² - 1 < caseICap`,
`H^(1+1/(4n)) ≤ 8√(sub1Thr²-1)`) give the `O(H^(n-1))` bound.
-/

theorem SubcaseI_P3_subset_box (n H : ℕ) : SubcaseI_P3 n H ⊆ Box n H :=
  fun f hf => Bad_subset_Box n H (irreducibleBad_subset_Bad n H hf.1.1)

/-- Auxiliary: `H ≤ sub1Thr n H` eventually. -/
lemma eventually_le_sub1Thr (n : ℕ) (hn : 3 ≤ n) : ∀ᶠ H : ℕ in atTop, H ≤ sub1Thr n H := by
  have hExpo : (0 : ℝ) < 1 / (4 * (n : ℝ)) := by
    have : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    positivity
  have h2 : ∀ᶠ H : ℕ in atTop, (2 : ℝ) ≤ (H : ℝ) ^ ((1 : ℝ) / (4 * (n : ℝ))) :=
    Commons.Analysis.ExpLog.eventually_natCast_rpow_atTop_ge _ _ hExpo
  filter_upwards [h2, eventually_ge_atTop (1 : ℕ)] with H h2 hH1
  have hHpos : (0 : ℝ) < (H : ℝ) := by exact_mod_cast (by omega : 0 < H)
  simp only [sub1Thr]
  refine Nat.le_floor ?_
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
  have hsp : (H : ℝ) ^ (1 + 1 / (4 * (n : ℝ))) =
      (H : ℝ) * (H : ℝ) ^ ((1 : ℝ) / (4 * (n : ℝ))) := by
    rw [Real.rpow_add hHpos, Real.rpow_one]
  rw [hsp]
  calc (H : ℝ) * 2 = 2 * (H : ℝ) := by ring
    _ ≤ (H : ℝ) ^ ((1 : ℝ) / (4 * (n : ℝ))) * (H : ℝ) :=
        mul_le_mul_of_nonneg_right h2 hHpos.le
    _ = (H : ℝ) * (H : ℝ) ^ ((1 : ℝ) / (4 * (n : ℝ))) := by ring

/-- Auxiliary: `sub1Thr n H ^ 2 - 1 < caseICap n H` eventually. -/
lemma eventually_sub1Thr_sq_lt_cap (n : ℕ) (hn : 3 ≤ n) :
    ∀ᶠ H : ℕ in atTop, sub1Thr n H ^ 2 - 1 < caseICap n H := by
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
  have hsmall : ∀ᶠ H : ℕ in atTop,
      ((sub1Thr n H ^ 2 - 1 : ℕ) : ℝ) < (H : ℝ) ^ (((2 * n - 1 : ℕ)) : ℝ) := by
    filter_upwards [eventually_le_sub1Thr n hn, eventually_ge_atTop (2 : ℕ)] with H hle hH2
    have hHpos : (0 : ℝ) < (H : ℝ) := by exact_mod_cast (by omega : 0 < H)
    have hXle : (sub1Thr n H : ℝ) ≤ (H : ℝ) ^ (1 + 1 / (4 * (n : ℝ))) / 2 := by
      have := Nat.floor_le (show (0 : ℝ) ≤ ((H : ℝ) ^ (1 + 1 / (4 * (n : ℝ)))) / 2 by positivity)
      simpa only [sub1Thr] using this
    have hX1n : 1 ≤ sub1Thr n H := le_trans (by omega : 1 ≤ H) hle
    have hsq2 : ((H : ℝ) ^ (1 + 1 / (4 * (n : ℝ)))) ^ 2 =
        (H : ℝ) ^ (2 + 1 / (2 * (n : ℝ))) := by
      rw [← Real.rpow_natCast ((H : ℝ) ^ (1 + 1 / (4 * (n : ℝ)))) 2,
        ← Real.rpow_mul hHpos.le]
      congr 1
      push_cast
      field_simp
      ring
    have h1 : (sub1Thr n H : ℝ) ^ 2 ≤ ((H : ℝ) ^ (1 + 1 / (4 * (n : ℝ))) / 2) ^ 2 := by
      rw [sq, sq]
      exact mul_self_le_mul_self (by linarith) hXle
    have h3 : ((H : ℝ) ^ (1 + 1 / (4 * (n : ℝ))) / 2) ^ 2 ≤
        ((H : ℝ) ^ (1 + 1 / (4 * (n : ℝ)))) ^ 2 := by
      rw [div_pow]
      have := sq_nonneg ((H : ℝ) ^ (1 + 1 / (4 * (n : ℝ))))
      nlinarith [this]
    have hsq : (sub1Thr n H : ℝ) ^ 2 ≤ (H : ℝ) ^ (2 + 1 / (2 * (n : ℝ))) := by
      rw [← hsq2]
      linarith
    have hS : ((sub1Thr n H ^ 2 - 1 : ℕ) : ℝ) = (sub1Thr n H : ℝ) ^ 2 - 1 := by
      have h1 : 1 ≤ sub1Thr n H ^ 2 := one_le_pow₀ hX1n
      rw [Nat.cast_sub h1, Nat.cast_pow, Nat.cast_one]
    have hlt : (2 : ℝ) + 1 / (2 * (n : ℝ)) < (((2 * n - 1 : ℕ)) : ℝ) := by
      have hn3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hcast : (((2 * n - 1 : ℕ)) : ℝ) = 2 * (n : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ 2 * n)]
        push_cast
        ring
      rw [hcast]
      have hpos : (0 : ℝ) < 2 * (n : ℝ) := by linarith
      have hle : 1 / (2 * (n : ℝ)) ≤ 1 := by
        rw [div_le_one hpos]; linarith
      linarith
    have h4 : (H : ℝ) ^ (2 + 1 / (2 * (n : ℝ))) < (H : ℝ) ^ (((2 * n - 1 : ℕ)) : ℝ) := by
      have hH1 : (1 : ℝ) < (H : ℝ) := by exact_mod_cast (by omega : 1 < H)
      exact Real.rpow_lt_rpow_of_exponent_lt hH1 hlt
    rw [hS]
    linarith
  filter_upwards [hcap, hsmall] with H hcap hsmall
  have : ((sub1Thr n H ^ 2 - 1 : ℕ) : ℝ) < (caseICap n H : ℝ) := lt_of_lt_of_le hsmall hcap
  exact_mod_cast this

/-- Auxiliary: the logarithmic factor is absorbed by `H^(1/(4n))`. -/
lemma eventually_log_absorb (n c : ℕ) (hn : 3 ≤ n) :
    ∀ᶠ H : ℕ in atTop,
      (1 + Real.log (caseICap n H : ℝ)) ^ (2 * c) ≤
        (H : ℝ) ^ ((1 : ℝ) / (4 * (n : ℝ))) := by
  have hExpo : (0 : ℝ) < 1 / (8 * (n : ℝ)) := by
    have : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    positivity
  have hpow := Commons.Analysis.ExpLog.eventually_one_add_log_pow_le_rpow
    (2 * c) 1 ((1 : ℝ) / (8 * (n : ℝ))) hExpo
  have hconst : ∀ᶠ H : ℕ in atTop,
      (((4 * n ^ 2 : ℕ) : ℝ) + 1) ^ (2 * c) ≤ (H : ℝ) ^ ((1 : ℝ) / (8 * (n : ℝ))) :=
    Commons.Analysis.ExpLog.eventually_natCast_rpow_atTop_ge _ _ hExpo
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
  have hpow' : (1 + Real.log ((H : ℝ) ^ 1)) ^ (2 * c) ≤
      (H : ℝ) ^ ((1 : ℝ) / (8 * (n : ℝ))) := hpow
  rw [pow_one] at hpow'
  have hexp : (1 : ℝ) / (8 * (n : ℝ)) + 1 / (8 * (n : ℝ)) = 1 / (4 * (n : ℝ)) := by
    have hnR : (n : ℝ) ≠ 0 := by
      have : n ≠ 0 := by omega
      exact_mod_cast this
    field_simp
    ring
  calc (1 + Real.log (caseICap n H : ℝ)) ^ (2 * c)
      ≤ ((((4 * n ^ 2 : ℕ) : ℝ) + 1) * (1 + Real.log (H : ℝ))) ^ (2 * c) :=
        pow_le_pow_left₀ (by positivity) hstep _
    _ = (((4 * n ^ 2 : ℕ) : ℝ) + 1) ^ (2 * c) * (1 + Real.log (H : ℝ)) ^ (2 * c) :=
        mul_pow _ _ _
    _ ≤ (H : ℝ) ^ ((1 : ℝ) / (8 * (n : ℝ))) * (H : ℝ) ^ ((1 : ℝ) / (8 * (n : ℝ))) :=
        mul_le_mul hconst hpow' (by positivity) (by positivity)
    _ = (H : ℝ) ^ ((1 : ℝ) / (4 * (n : ℝ))) := by
        rw [← Real.rpow_add hHpos, hexp]

/-- Auxiliary: `H^(1+1/(4n)) ≤ 8 √(sub1Thr² - 1)` eventually. -/
lemma eventually_rpow_le_eight_sqrt (n : ℕ) (hn : 3 ≤ n) :
    ∀ᶠ H : ℕ in atTop,
      (H : ℝ) ^ (1 + 1 / (4 * (n : ℝ))) ≤
        8 * Real.sqrt ((sub1Thr n H ^ 2 - 1 : ℕ) : ℝ) := by
  have h4 : ∀ᶠ H : ℕ in atTop, (4 : ℝ) ≤ (H : ℝ) ^ (1 + 1 / (4 * (n : ℝ))) :=
    Commons.Analysis.ExpLog.eventually_natCast_rpow_atTop_ge _ _ (by positivity)
  filter_upwards [h4, eventually_le_sub1Thr n hn, eventually_ge_atTop (2 : ℕ)] with H h4 hle hH2
  have hX2n : 2 ≤ sub1Thr n H := le_trans hH2 hle
  have hX2 : (2 : ℝ) ≤ (sub1Thr n H : ℝ) := by exact_mod_cast hX2n
  have hyl : (H : ℝ) ^ (1 + 1 / (4 * (n : ℝ))) / 2 < (sub1Thr n H : ℝ) + 1 := by
    have := Nat.lt_floor_add_one (((H : ℝ) ^ (1 + 1 / (4 * (n : ℝ)))) / 2)
    simpa only [sub1Thr] using this
  have hXge : (H : ℝ) ^ (1 + 1 / (4 * (n : ℝ))) / 4 ≤ (sub1Thr n H : ℝ) := by linarith
  have hSc : ((sub1Thr n H ^ 2 - 1 : ℕ) : ℝ) = (sub1Thr n H : ℝ) ^ 2 - 1 := by
    have hX1 : 1 ≤ sub1Thr n H := le_trans (by omega : 1 ≤ H) hle
    have h1 : 1 ≤ sub1Thr n H ^ 2 := one_le_pow₀ hX1
    rw [Nat.cast_sub h1, Nat.cast_pow, Nat.cast_one]
  have hsqrt : (sub1Thr n H : ℝ) / 2 ≤ Real.sqrt ((sub1Thr n H ^ 2 - 1 : ℕ) : ℝ) := by
    have h1 : Real.sqrt (((sub1Thr n H : ℝ) / 2) ^ 2) ≤
        Real.sqrt ((sub1Thr n H ^ 2 - 1 : ℕ) : ℝ) := by
      apply Real.sqrt_le_sqrt
      rw [hSc]
      nlinarith [hX2]
    rwa [Real.sqrt_sq (by positivity : (0 : ℝ) ≤ (sub1Thr n H : ℝ) / 2)] at h1
  linarith

theorem SubcaseI_P3_isBigO_of_perIrrBound (n c : ℕ) (hn : 3 ≤ n) (hc : 1 ≤ c)
    (h : PerIrrBound n c) :
    (fun H : ℕ => ((SubcaseI_P3 n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) := by
  have hExpo : (0 : ℝ) < 1 / (4 * (n : ℝ)) := by
    have : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    positivity
  have hS0e : ∀ᶠ H : ℕ in atTop,
      (smallConst n : ℝ) ≤ (H : ℝ) ^ ((1 : ℝ) / (4 * (n : ℝ))) :=
    Commons.Analysis.ExpLog.eventually_natCast_rpow_atTop_ge _ _ hExpo
  have hnY : ∀ᶠ H : ℕ in atTop, n < lowerThr (4 * n) H :=
    (eventually_lt_lowerThr (4 * n) (by omega)).mono (fun H h => by omega)
  have hY1 : ∀ᶠ H : ℕ in atTop, 1 ≤ sub1Thr n H ^ 2 - 1 := by
    filter_upwards [eventually_le_sub1Thr n hn, eventually_ge_atTop (2 : ℕ)] with H hle hH2
    have h2 : 2 ≤ sub1Thr n H := le_trans hH2 hle
    have h4 : 4 ≤ sub1Thr n H ^ 2 := by nlinarith
    omega
  have hgen : ∀ᶠ H : ℕ in atTop, (SubcaseI_P3 n H).ncard ≤ 8 * H ^ (n - 1) := by
    filter_upwards [eventually_ge_atTop (2 : ℕ), eventually_le_sub1Thr n hn, hS0e, hnY,
      hY1, eventually_sub1Thr_sq_lt_cap n hn, eventually_log_absorb n c hn,
      eventually_rpow_le_eight_sqrt n hn] with H hH1 hHX hS0 hnY hY1 hYZ hlogAbs hbig
    have hHpos : (0 : ℝ) < (H : ℝ) := by exact_mod_cast (by omega : 0 < H)
    have hb1 := ncard_le_ncard_box (SubcaseI_P3_subset_box n H)
    have hb2 := SubcaseI_P3_ncard_le_sum n c H hn hc h hH1 hHX hS0 hnY
    have hb3 := sub1Index_sum_le_tail n c H hc hY1 hYZ
    have hstep1 : ((SubcaseI_P3 n H).ncard : ℝ) ≤
        (H : ℝ) ^ n * ((1 + Real.log (caseICap n H : ℝ)) ^ (2 * c) /
          ((sub1Thr n H ^ 2 - 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 2)) :=
      le_trans (le_trans (by exact_mod_cast hb1) hb2) hb3
    have hSp_pos : (0 : ℝ) < ((sub1Thr n H ^ 2 - 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 2) := by
      apply Real.rpow_pos_of_pos
      exact_mod_cast (by omega : 0 < sub1Thr n H ^ 2 - 1)
    have hBpos : (0 : ℝ) < (H : ℝ) ^ (1 + 1 / (4 * (n : ℝ))) := Real.rpow_pos_of_pos hHpos _
    have hSle : (H : ℝ) ^ (1 + 1 / (4 * (n : ℝ))) ≤
        8 * ((sub1Thr n H ^ 2 - 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 2) := by
      have heq : ((sub1Thr n H ^ 2 - 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 2) =
          Real.sqrt ((sub1Thr n H ^ 2 - 1 : ℕ) : ℝ) := (Real.sqrt_eq_rpow _).symm
      rw [heq]; exact hbig
    have hineq : (1 + Real.log (caseICap n H : ℝ)) ^ (2 * c) /
          ((sub1Thr n H ^ 2 - 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 2) ≤
        8 * (H : ℝ) ^ ((1 : ℝ) / (4 * (n : ℝ))) /
          (H : ℝ) ^ (1 + 1 / (4 * (n : ℝ))) := by
      rw [div_le_div_iff₀ hSp_pos hBpos]
      calc (1 + Real.log (caseICap n H : ℝ)) ^ (2 * c) * (H : ℝ) ^ (1 + 1 / (4 * (n : ℝ)))
          ≤ (H : ℝ) ^ ((1 : ℝ) / (4 * (n : ℝ))) * (H : ℝ) ^ (1 + 1 / (4 * (n : ℝ))) :=
            mul_le_mul_of_nonneg_right hlogAbs hBpos.le
        _ ≤ (H : ℝ) ^ ((1 : ℝ) / (4 * (n : ℝ))) *
              (8 * ((sub1Thr n H ^ 2 - 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 2)) :=
            mul_le_mul_of_nonneg_left hSle (Real.rpow_nonneg (Nat.cast_nonneg H) _)
        _ = 8 * (H : ℝ) ^ ((1 : ℝ) / (4 * (n : ℝ))) *
              ((sub1Thr n H ^ 2 - 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 2) := by ring
    have hExpId : (n : ℝ) + 1 / (4 * (n : ℝ)) - (1 + 1 / (4 * (n : ℝ))) =
        ((n - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega : 1 ≤ n)]
      push_cast
      ring
    have hAB : (H : ℝ) ^ n * (8 * (H : ℝ) ^ ((1 : ℝ) / (4 * (n : ℝ))) /
          (H : ℝ) ^ (1 + 1 / (4 * (n : ℝ)))) = 8 * (H : ℝ) ^ (n - 1) := by
      rw [← Real.rpow_natCast (H : ℝ) n]
      have h1 : (H : ℝ) ^ (n : ℝ) * (8 * (H : ℝ) ^ ((1 : ℝ) / (4 * (n : ℝ))) /
            (H : ℝ) ^ (1 + 1 / (4 * (n : ℝ)))) =
          8 * (((H : ℝ) ^ (n : ℝ) * (H : ℝ) ^ ((1 : ℝ) / (4 * (n : ℝ)))) /
            (H : ℝ) ^ (1 + 1 / (4 * (n : ℝ)))) := by ring
      rw [h1]
      have h2 : (H : ℝ) ^ (n : ℝ) * (H : ℝ) ^ ((1 : ℝ) / (4 * (n : ℝ))) =
          (H : ℝ) ^ ((n : ℝ) + 1 / (4 * (n : ℝ))) := (Real.rpow_add hHpos _ _).symm
      rw [h2]
      have h3 : (H : ℝ) ^ ((n : ℝ) + 1 / (4 * (n : ℝ))) /
            (H : ℝ) ^ (1 + 1 / (4 * (n : ℝ))) =
          (H : ℝ) ^ ((n : ℝ) + 1 / (4 * (n : ℝ)) - (1 + 1 / (4 * (n : ℝ)))) :=
        (Real.rpow_sub hHpos _ _).symm
      rw [h3, hExpId, Real.rpow_natCast]
    have hmain : ((SubcaseI_P3 n H).ncard : ℝ) ≤ 8 * (H : ℝ) ^ (n - 1) := by
      calc ((SubcaseI_P3 n H).ncard : ℝ)
          ≤ (H : ℝ) ^ n * ((1 + Real.log (caseICap n H : ℝ)) ^ (2 * c) /
              ((sub1Thr n H ^ 2 - 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 2)) := hstep1
        _ ≤ (H : ℝ) ^ n * (8 * (H : ℝ) ^ ((1 : ℝ) / (4 * (n : ℝ))) /
              (H : ℝ) ^ (1 + 1 / (4 * (n : ℝ)))) :=
            mul_le_mul_of_nonneg_left hineq (by positivity)
        _ = 8 * (H : ℝ) ^ (n - 1) := hAB
    exact_mod_cast hmain
  exact Commons.Analysis.Asymptotics.isBigO_of_natCast_le_mul_pow (n - 1) 8 _ hgen


end

end Submission.Vdw
