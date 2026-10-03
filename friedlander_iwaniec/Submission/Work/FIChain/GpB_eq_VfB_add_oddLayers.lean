/-
# `Work.FIChain.GpB_eq_VfB_add_oddLayers`

The Rosser–Iwaniec identity for the `B`-delay upper weight:

    `Gp(y,D) = V(y) + ∑_{n odd} T_n(D,y)`,

i.e. `GpB B ν y D = VfB ν y + OddLayerSum B ν (layerCut B D + 1) D y`.

The proof is the standard peeling of the largest prime `q < y`: with `P(y) = q·P(q)`,
`V(y) = (1-ν q)·V(q)` and the recursions

* `Gp(y,D) = Gp(q,D) - [q^{B+1} ≤ D] · ν q · Gm(q,D/q)`,
* `Gm(y,E) = Gm(q,E) - ν q · Gp(q,E/q)`,

the layer sums satisfy the matching pair of recursions

* `T_odd(y) = T_odd(q) + ν q·([q^{B+1} ≤ D] · T_even(q,D/q) + [q^{B+1} > D]·V(q))`,
* `T_even(y) = T_even(q) + ν q·T_odd(q,D/q)`,

whence `T_odd(y) = Gp(y,D) - V(y)` and `T_even(y) = V(y) - Gm(y,E)` by induction on the number of
primes below `y`.  The truncation at `layerCut B D + 1` uses the vanishing of `T_n(D,y)` for
`n ≥ log₂⌈D⌉₊ + ⌈B⌉₊ + 4` (a chain of `n` primes forces `D ≥ 2^n`).
-/
import Mathlib
import Submission.Work.FIChain.LamPlusBLayerDefs

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIChain

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## The even layer sum -/

/-- The truncated sum of the layer sums over the nonzero **even** indices:
`∑_{n < K, n even, n ≠ 0} T_n(D,y)`.  It is the companion of `OddLayerSum` in the inductive proof
of the Rosser–Iwaniec identity. -/
def EvenPosLayerSum (B : ℝ) (ν : ℕ → ℝ) (K : ℕ) (D y : ℝ) : ℝ :=
  ∑ n ∈ (Finset.range K).filter (fun n : ℕ => Even n ∧ n ≠ 0), TnB B ν n D y

/-! ## The sifting modulus `PB` and its prime divisors -/

lemma PB_eq_primorial (y : ℝ) : PB y = primorial (⌈y⌉₊ - 1) := by
  rw [PB, primorial_eq_prod_primesLE, Nat.primesBelow_eq_primesLE_sub_one]

lemma PB_ne_zero (y : ℝ) : PB y ≠ 0 := by
  rw [PB_eq_primorial]; exact (primorial_pos _).ne'

lemma PB_pos (y : ℝ) : 0 < PB y := by
  rw [PB_eq_primorial]; exact primorial_pos _

lemma PB_squarefree (y : ℝ) : Squarefree (PB y) := by
  rw [PB_eq_primorial]; exact squarefree_primorial _

lemma PB_primeFactors (y : ℝ) : (PB y).primeFactors = Nat.primesBelow ⌈y⌉₊ := by
  rw [PB_eq_primorial, primeFactors_primorial, Nat.primesBelow_eq_primesLE_sub_one]

lemma primeFactors_PB_lt {y : ℝ} {d : ℕ} (hd : d ∣ PB y) {p : ℕ} (hp : p ∈ d.primeFactors) :
    p < ⌈y⌉₊ := by
  obtain ⟨hpp, hpd, -⟩ := Nat.mem_primeFactors.mp hp
  have hdvd : p ∣ PB y := dvd_trans hpd hd
  have hmem : p ∈ (PB y).primeFactors := Nat.mem_primeFactors.mpr ⟨hpp, hdvd, PB_ne_zero y⟩
  rw [PB_primeFactors] at hmem
  exact (Nat.mem_primesBelow.mp hmem).1

lemma not_dvd_PB {p : ℕ} {y : ℝ} (hp : p.Prime) (hy : ¬ p < ⌈y⌉₊) : ¬ p ∣ PB y := by
  intro hdvd
  have hmem : p ∈ (PB y).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hdvd, PB_ne_zero y⟩
  rw [PB_primeFactors] at hmem
  exact hy (Nat.mem_primesBelow.mp hmem).1

/-! ## Congruence: only `Nat.primesBelow ⌈y⌉₊` matters -/

lemma VfB_congr {y y' : ℝ} (ν : ℕ → ℝ) (h : Nat.primesBelow ⌈y⌉₊ = Nat.primesBelow ⌈y'⌉₊) :
    VfB ν y = VfB ν y' := by
  rw [VfB, VfB, h]

lemma PB_congr {y y' : ℝ} (h : Nat.primesBelow ⌈y⌉₊ = Nat.primesBelow ⌈y'⌉₊) :
    PB y = PB y' := by
  rw [PB, PB, h]

lemma GpB_congr {y y' : ℝ} (h : Nat.primesBelow ⌈y⌉₊ = Nat.primesBelow ⌈y'⌉₊) (B : ℝ)
    (ν : ℕ → ℝ) (D : ℝ) : GpB B ν y D = GpB B ν y' D := by
  rw [GpB, GpB, PB_congr h]

lemma GmB_congr {y y' : ℝ} (h : Nat.primesBelow ⌈y⌉₊ = Nat.primesBelow ⌈y'⌉₊) (B : ℝ)
    (ν : ℕ → ℝ) (D : ℝ) : GmB B ν y D = GmB B ν y' D := by
  rw [GmB, GmB, PB_congr h]

lemma TnB_congr (B : ℝ) (ν : ℕ → ℝ) :
    ∀ n : ℕ, ∀ D y y' : ℝ, Nat.primesBelow ⌈y⌉₊ = Nat.primesBelow ⌈y'⌉₊ →
      TnB B ν n D y = TnB B ν n D y' := by
  intro n
  induction n with
  | zero => intro D y y' h; rw [TnB, TnB, VfB_congr ν h]
  | succ n ihn =>
      intro D y y' h
      rw [TnB, TnB, h]

lemma OddLayerSum_congr {y y' : ℝ} (h : Nat.primesBelow ⌈y⌉₊ = Nat.primesBelow ⌈y'⌉₊) (B : ℝ)
    (ν : ℕ → ℝ) (M : ℕ) (D : ℝ) :
    OddLayerSum B ν M D y = OddLayerSum B ν M D y' := by
  rw [OddLayerSum, OddLayerSum]
  exact Finset.sum_congr rfl (fun n _ => TnB_congr B ν n D y y' h)

lemma EvenPosLayerSum_congr {y y' : ℝ} (h : Nat.primesBelow ⌈y⌉₊ = Nat.primesBelow ⌈y'⌉₊) (B : ℝ)
    (ν : ℕ → ℝ) (M : ℕ) (D : ℝ) :
    EvenPosLayerSum B ν M D y = EvenPosLayerSum B ν M D y' := by
  rw [EvenPosLayerSum, EvenPosLayerSum]
  exact Finset.sum_congr rfl (fun n _ => TnB_congr B ν n D y y' h)

/-! ## The layer condition at a prime -/

lemma TcondB_one (B : ℝ) (D : ℝ) (q : ℕ) :
    TcondB B 1 D q ↔ D < (q : ℝ) ^ (B + 1) := by
  unfold TcondB
  constructor
  · intro h; exact h.1 rfl
  · intro h; exact ⟨fun _ => h, fun h2 => absurd h2 (by omega)⟩

lemma TcondB_of_odd (B : ℝ) (D : ℝ) (q : ℕ) {n : ℕ} (h2 : 2 ≤ n) (hodd : Odd n) :
    TcondB B n D q ↔ (q : ℝ) ^ (B + 1) ≤ D := by
  unfold TcondB
  constructor
  · intro h; exact h.2 h2 hodd
  · intro h; exact ⟨fun hn1 => absurd hn1 (by omega), fun _ _ => h⟩

lemma TcondB_of_even (B : ℝ) (D : ℝ) (q : ℕ) {n : ℕ} (h2 : 2 ≤ n) (heven : Even n) :
    TcondB B n D q :=
  ⟨fun hn1 => absurd hn1 (by omega),
    fun _ hodd => absurd hodd (Nat.not_odd_iff_even.mpr heven)⟩

/-! ## Peeling the largest prime `q` -/

/-- Splitting the recursion of `TnB` at the largest prime `q < y`. -/
lemma TnB_succ_split {q : ℕ} (_hq : q.Prime) {z : ℝ}
    (hz : Nat.primesBelow ⌈z⌉₊ = insert q (Nat.primesBelow q))
    (B : ℝ) (ν : ℕ → ℝ) (m : ℕ) (D : ℝ) :
    TnB B ν (m + 1) D z
      = TnB B ν (m + 1) D (q : ℝ)
        + (if TcondB B (m + 1) D q then ν q * TnB B ν m (D / q) (q : ℝ) else 0) := by
  have h1 : TnB B ν (m + 1) D z
      = ∑ p ∈ (Nat.primesBelow ⌈z⌉₊).filter (fun p => TcondB B (m + 1) D p),
          ν p * TnB B ν m (D / (p : ℝ)) (p : ℝ) := by rw [TnB]
  have h2 : TnB B ν (m + 1) D (q : ℝ)
      = ∑ p ∈ (Nat.primesBelow q).filter (fun p => TcondB B (m + 1) D p),
          ν p * TnB B ν m (D / (p : ℝ)) (p : ℝ) := by rw [TnB, Nat.ceil_natCast]
  rw [h1, h2, hz, Finset.filter_insert]
  by_cases hc : TcondB B (m + 1) D q
  · rw [if_pos hc, if_pos hc,
      Finset.sum_insert (fun h => Nat.notMem_primesBelow q (Finset.mem_filter.mp h).1)]
    ring
  · rw [if_neg hc, if_neg hc]
    ring

lemma PB_split {q : ℕ} {z : ℝ} (hz : Nat.primesBelow ⌈z⌉₊ = insert q (Nat.primesBelow q)) :
    PB z = q * PB (q : ℝ) := by
  rw [PB, PB, Nat.ceil_natCast, hz, Finset.prod_insert (Nat.notMem_primesBelow q)]

lemma VfB_split {q : ℕ} {z : ℝ} (hz : Nat.primesBelow ⌈z⌉₊ = insert q (Nat.primesBelow q))
    (ν : ℕ → ℝ) : VfB ν z = (1 - ν q) * VfB ν (q : ℝ) := by
  rw [VfB, VfB, Nat.ceil_natCast, hz, Finset.prod_insert (Nat.notMem_primesBelow q)]

/-! ## The recursions for `GpB` and `GmB` -/

private lemma sum_divisors_mul_prime_aux (q M : ℕ) (hq : q.Prime) (hcop : q.Coprime M)
    (F : ℕ → ℝ) :
    ∑ d ∈ (q * M).divisors, F d = (∑ d ∈ M.divisors, F d) + ∑ d ∈ M.divisors, F (q * d) := by
  rw [Nat.divisors_mul, Finset.mul_def, Finset.sum_image hcop.mul_injOn_divisors,
    Finset.sum_product, hq.divisors, Finset.sum_pair (hq.ne_one.symm)]
  simp

lemma GpB_split {q : ℕ} (hq : q.Prime) {z : ℝ}
    (hz : Nat.primesBelow ⌈z⌉₊ = insert q (Nat.primesBelow q))
    {B : ℝ} (hB : 0 ≤ B) (ν : ℕ → ℝ)
    (hνmul : ∀ m n : ℕ, Nat.Coprime m n → ν (m * n) = ν m * ν n) (D : ℝ) :
    GpB B ν z D = GpB B ν (q : ℝ) D -
      (if (q : ℝ) ^ (B + 1) ≤ D then ν q * GmB B ν (q : ℝ) (D / q) else 0) := by
  have hqnot : ¬ q ∣ PB (q : ℝ) := by
    refine not_dvd_PB hq ?_
    rw [Nat.ceil_natCast]
    exact not_lt.mpr le_rfl
  have hcop : q.Coprime (PB (q : ℝ)) := hq.coprime_iff_not_dvd.mpr hqnot
  have key : ∀ d ∈ (PB (q : ℝ)).divisors,
      Squarefree d ∧ ¬ q ∣ d ∧ (∀ p ∈ d.primeFactors, p < q) ∧ d ≠ 0 := by
    intro d hd
    obtain ⟨hdvd, -⟩ := Nat.mem_divisors.mp hd
    refine ⟨Squarefree.squarefree_of_dvd hdvd (PB_squarefree _),
      fun h => hqnot (dvd_trans h hdvd), fun p hp => ?_,
      (Nat.pos_of_dvd_of_pos hdvd (PB_pos _)).ne'⟩
    have hlt := primeFactors_PB_lt hdvd hp
    rwa [Nat.ceil_natCast] at hlt
  have hsum2 : (∑ d ∈ (PB (q : ℝ)).divisors,
        (if rdPlusB B D (q * d) then ((ArithmeticFunction.moebius (q * d) : ℤ) : ℝ) else 0)
          * ν (q * d))
      = -(if (q : ℝ) ^ (B + 1) ≤ D then ν q * GmB B ν (q : ℝ) (D / q) else 0) := by
    have hterm : ∀ d ∈ (PB (q : ℝ)).divisors,
        (if rdPlusB B D (q * d) then ((ArithmeticFunction.moebius (q * d) : ℤ) : ℝ) else 0)
            * ν (q * d)
          = -ν q * ((if (q : ℝ) ^ (B + 1) ≤ D then
                (if rdMinusB B (D / q) d then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0)
              else 0) * ν d) := by
      intro d hd
      obtain ⟨hsq, hqd, hbig, -⟩ := key d hd
      rw [moebius_mul_prime hq hqd,
        rdPlusB_mul_prime hB hq hsq hqd hbig D,
        hνmul q d (hq.coprime_iff_not_dvd.mpr hqd)]
      by_cases hc : (q : ℝ) ^ (B + 1) ≤ D
      · by_cases hM : rdMinusB B (D / q) d
        · rw [if_pos ⟨hc, hM⟩, if_pos hc, if_pos hM]; ring
        · rw [if_neg (fun h => hM h.2), if_pos hc, if_neg hM]; ring
      · rw [if_neg (fun h => hc h.1), if_neg hc]; ring
    have hXY : (∑ d ∈ (PB (q : ℝ)).divisors,
          ((if (q : ℝ) ^ (B + 1) ≤ D then
              (if rdMinusB B (D / q) d then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0)
            else 0) * ν d))
        = (if (q : ℝ) ^ (B + 1) ≤ D then GmB B ν (q : ℝ) (D / q) else 0) := by
      by_cases hc : (q : ℝ) ^ (B + 1) ≤ D
      · rw [if_pos hc, GmB]
        exact Finset.sum_congr rfl (fun d _ => by rw [if_pos hc])
      · rw [if_neg hc]
        refine Finset.sum_eq_zero (fun d _ => ?_)
        rw [if_neg hc]; ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hXY]
    by_cases hc : (q : ℝ) ^ (B + 1) ≤ D
    · rw [if_pos hc, if_pos hc]; ring
    · rw [if_neg hc, if_neg hc]; ring
  rw [GpB, GpB, PB_split hz,
    sum_divisors_mul_prime_aux q (PB (q : ℝ)) hq hcop
      (fun d => (if rdPlusB B D d then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0) * ν d),
    hsum2]
  ring

lemma GmB_split {q : ℕ} (hq : q.Prime) {z : ℝ}
    (hz : Nat.primesBelow ⌈z⌉₊ = insert q (Nat.primesBelow q))
    {B : ℝ} (hB : 0 ≤ B) (ν : ℕ → ℝ)
    (hνmul : ∀ m n : ℕ, Nat.Coprime m n → ν (m * n) = ν m * ν n) (E : ℝ) :
    GmB B ν z E = GmB B ν (q : ℝ) E - ν q * GpB B ν (q : ℝ) (E / q) := by
  have hqnot : ¬ q ∣ PB (q : ℝ) := by
    refine not_dvd_PB hq ?_
    rw [Nat.ceil_natCast]
    exact not_lt.mpr le_rfl
  have hcop : q.Coprime (PB (q : ℝ)) := hq.coprime_iff_not_dvd.mpr hqnot
  have key : ∀ d ∈ (PB (q : ℝ)).divisors,
      Squarefree d ∧ ¬ q ∣ d ∧ (∀ p ∈ d.primeFactors, p < q) ∧ d ≠ 0 := by
    intro d hd
    obtain ⟨hdvd, -⟩ := Nat.mem_divisors.mp hd
    refine ⟨Squarefree.squarefree_of_dvd hdvd (PB_squarefree _),
      fun h => hqnot (dvd_trans h hdvd), fun p hp => ?_,
      (Nat.pos_of_dvd_of_pos hdvd (PB_pos _)).ne'⟩
    have hlt := primeFactors_PB_lt hdvd hp
    rwa [Nat.ceil_natCast] at hlt
  have hsum2 : (∑ d ∈ (PB (q : ℝ)).divisors,
        (if rdMinusB B E (q * d) then ((ArithmeticFunction.moebius (q * d) : ℤ) : ℝ) else 0)
          * ν (q * d))
      = -ν q * GpB B ν (q : ℝ) (E / q) := by
    have hterm : ∀ d ∈ (PB (q : ℝ)).divisors,
        (if rdMinusB B E (q * d) then ((ArithmeticFunction.moebius (q * d) : ℤ) : ℝ) else 0)
            * ν (q * d)
          = -ν q * ((if rdPlusB B (E / q) d then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0)
              * ν d) := by
      intro d hd
      obtain ⟨hsq, hqd, hbig, -⟩ := key d hd
      rw [moebius_mul_prime hq hqd,
        rdMinusB_mul_prime hB hq hsq hqd hbig E,
        hνmul q d (hq.coprime_iff_not_dvd.mpr hqd)]
      by_cases hM : rdPlusB B (E / q) d
      · rw [if_pos hM, if_pos hM]; ring
      · rw [if_neg hM, if_neg hM]; ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    congr 1
  rw [GmB, GmB, PB_split hz,
    sum_divisors_mul_prime_aux q (PB (q : ℝ)) hq hcop
      (fun d => (if rdMinusB B E d then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0) * ν d),
    hsum2]
  ring

/-! ## Reindexing the layer sums -/

lemma sum_shift_odd (B : ℝ) (ν : ℕ → ℝ) (E : ℝ) (q M : ℕ) :
    (∑ n ∈ (Finset.range M).filter (fun n : ℕ => Odd n ∧ 3 ≤ n), TnB B ν (n - 1) E (q : ℝ))
      = EvenPosLayerSum B ν (M - 1) E (q : ℝ) := by
  rw [EvenPosLayerSum]
  refine Finset.sum_nbij' (fun n => n - 1) (fun r => r + 1) ?_ ?_ ?_ ?_ ?_
  · intro n hn
    obtain ⟨hnM, hnodd, hn3⟩ := Finset.mem_filter.mp hn
    rw [Finset.mem_range] at hnM
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),
      Nat.Odd.sub_odd hnodd odd_one, by omega⟩
  · intro r hr
    obtain ⟨hrM, hrev, hr0⟩ := Finset.mem_filter.mp hr
    rw [Finset.mem_range] at hrM
    have h2 : 2 ≤ r := by obtain ⟨k, hk⟩ := hrev; omega
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hrev.add_one, by omega⟩
  · intro n hn
    obtain ⟨hnM, hnodd, hn3⟩ := Finset.mem_filter.mp hn
    rw [Finset.mem_range] at hnM
    omega
  · intro r hr
    obtain ⟨hrM, hrev, hr0⟩ := Finset.mem_filter.mp hr
    rw [Finset.mem_range] at hrM
    omega
  · intro n _
    rfl

lemma sum_shift_even (B : ℝ) (ν : ℕ → ℝ) (E : ℝ) (q M : ℕ) :
    (∑ n ∈ (Finset.range M).filter (fun n : ℕ => Even n ∧ n ≠ 0), TnB B ν (n - 1) E (q : ℝ))
      = OddLayerSum B ν (M - 1) E (q : ℝ) := by
  rw [OddLayerSum]
  refine Finset.sum_nbij' (fun n => n - 1) (fun r => r + 1) ?_ ?_ ?_ ?_ ?_
  · intro n hn
    obtain ⟨hnM, hrev, hn0⟩ := Finset.mem_filter.mp hn
    rw [Finset.mem_range] at hnM
    have h1 : 1 ≤ n := by obtain ⟨k, hk⟩ := hrev; omega
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),
      Nat.Even.sub_odd h1 hrev odd_one⟩
  · intro r hr
    obtain ⟨hrM, hrodd⟩ := Finset.mem_filter.mp hr
    rw [Finset.mem_range] at hrM
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hrodd.add_one, by omega⟩
  · intro n hn
    obtain ⟨hnM, hrev, hn0⟩ := Finset.mem_filter.mp hn
    rw [Finset.mem_range] at hnM
    have h1 : 1 ≤ n := by obtain ⟨k, hk⟩ := hrev; omega
    omega
  · intro r hr
    obtain ⟨hrM, hrodd⟩ := Finset.mem_filter.mp hr
    rw [Finset.mem_range] at hrM
    omega
  · intro n _
    rfl

/-- In the `q^{B+1} ≤ D` regime the layer condition at an odd index is exactly `3 ≤ n`; in the
other regime it is exactly `n = 1`.  Hence the first layer sum is `ν q · (T_even(q,D/q))` or
`ν q · V(q)`. -/
lemma oddLayerSum_restrict {q : ℕ} (B : ℝ) (ν : ℕ → ℝ) (D : ℝ) {M : ℕ}
    (hM : 2 ≤ M) :
    (∑ n ∈ (Finset.range M).filter Odd,
        (if TcondB B n D q then ν q * TnB B ν (n - 1) (D / q) (q : ℝ) else 0))
      = ν q * (if (q : ℝ) ^ (B + 1) ≤ D then EvenPosLayerSum B ν (M - 1) (D / q) (q : ℝ)
          else VfB ν (q : ℝ)) := by
  by_cases hG : (q : ℝ) ^ (B + 1) ≤ D
  · rw [if_pos hG]
    have hiff : ∀ n : ℕ, Odd n → (TcondB B n D q ↔ 3 ≤ n) := by
      intro n hodd
      constructor
      · intro hc
        by_contra h3
        have hn1 : n = 1 := by obtain ⟨k, hk⟩ := hodd; omega
        subst hn1
        exact absurd (TcondB_one B D q |>.mp hc) (not_lt.mpr hG)
      · intro h3
        exact (TcondB_of_odd B D q (by omega) hodd).mpr hG
    rw [show (∑ n ∈ (Finset.range M).filter Odd,
          (if TcondB B n D q then ν q * TnB B ν (n - 1) (D / q) (q : ℝ) else 0))
        = ∑ n ∈ (Finset.range M).filter Odd,
          (if 3 ≤ n then ν q * TnB B ν (n - 1) (D / q) (q : ℝ) else 0) from
      Finset.sum_congr rfl (fun n hn => by
        have hodd := (Finset.mem_filter.mp hn).2
        by_cases h3 : 3 ≤ n
        · rw [if_pos ((hiff n hodd).mpr h3), if_pos h3]
        · rw [if_neg (fun hc => h3 ((hiff n hodd).mp hc)), if_neg h3])]
    rw [← Finset.sum_filter, Finset.filter_filter, ← Finset.mul_sum,
      sum_shift_odd B ν (D / q) q M]
  · rw [if_neg hG]
    have hDlt : D < (q : ℝ) ^ (B + 1) := not_le.mp hG
    have hiff : ∀ n : ℕ, Odd n → (TcondB B n D q ↔ n = 1) := by
      intro n hodd
      constructor
      · intro hc
        by_contra hne
        have h3 : 3 ≤ n := by obtain ⟨k, hk⟩ := hodd; omega
        exact hG ((TcondB_of_odd B D q (by omega) hodd).mp hc)
      · intro h1
        subst h1
        exact (TcondB_one B D q).mpr hDlt
    rw [Finset.sum_eq_single 1]
    · have hc1 : TcondB B 1 D q := (TcondB_one B D q).mpr hDlt
      have hT : TnB B ν (1 - 1) (D / q) (q : ℝ) = VfB ν (q : ℝ) := by
        rw [show (1 : ℕ) - 1 = 0 from rfl, TnB]
      rw [if_pos hc1, hT]
    · intro n hn hne
      exact if_neg (fun hc => hne ((hiff n (Finset.mem_filter.mp hn).2).mp hc))
    · intro h1not
      exfalso
      exact h1not (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), odd_one⟩)

/-- The recursion for `OddLayerSum` when a prime `q` is adjoined to the sifting set. -/
lemma OddLayerSum_split {q : ℕ} (hq : q.Prime) {z : ℝ}
    (hz : Nat.primesBelow ⌈z⌉₊ = insert q (Nat.primesBelow q))
    (B : ℝ) (ν : ℕ → ℝ) (D : ℝ) {M : ℕ} (hM : 2 ≤ M) :
    OddLayerSum B ν M D z = OddLayerSum B ν M D (q : ℝ) +
      ν q * (if (q : ℝ) ^ (B + 1) ≤ D then EvenPosLayerSum B ν (M - 1) (D / q) (q : ℝ)
        else VfB ν (q : ℝ)) := by
  have e1 : OddLayerSum B ν M D z
      = ∑ n ∈ (Finset.range M).filter Odd,
          (TnB B ν n D (q : ℝ) +
            (if TcondB B n D q then ν q * TnB B ν (n - 1) (D / q) (q : ℝ) else 0)) := by
    rw [OddLayerSum]
    refine Finset.sum_congr rfl (fun n hn => ?_)
    have hn1 : 1 ≤ n := by
      obtain ⟨k, hk⟩ := (Finset.mem_filter.mp hn).2
      omega
    have h := TnB_succ_split hq hz B ν (n - 1) D
    rw [Nat.sub_add_cancel hn1] at h
    exact h
  rw [e1, Finset.sum_add_distrib, OddLayerSum]
  rw [oddLayerSum_restrict B ν D hM]

/-- The recursion for `EvenPosLayerSum` when a prime `q` is adjoined to the sifting set. -/
lemma EvenPosLayerSum_split {q : ℕ} (hq : q.Prime) {z : ℝ}
    (hz : Nat.primesBelow ⌈z⌉₊ = insert q (Nat.primesBelow q))
    (B : ℝ) (ν : ℕ → ℝ) (D : ℝ) (M : ℕ) :
    EvenPosLayerSum B ν M D z
      = EvenPosLayerSum B ν M D (q : ℝ) + ν q * OddLayerSum B ν (M - 1) (D / q) (q : ℝ) := by
  have e1 : EvenPosLayerSum B ν M D z
      = ∑ n ∈ (Finset.range M).filter (fun n : ℕ => Even n ∧ n ≠ 0),
          (TnB B ν n D (q : ℝ) + ν q * TnB B ν (n - 1) (D / q) (q : ℝ)) := by
    rw [EvenPosLayerSum]
    refine Finset.sum_congr rfl (fun n hn => ?_)
    obtain ⟨hnM, hrev, hn0⟩ := Finset.mem_filter.mp hn
    have hn1 : 1 ≤ n := by obtain ⟨k, hk⟩ := hrev; omega
    have h2 : 2 ≤ n := by obtain ⟨k, hk⟩ := hrev; omega
    have h := TnB_succ_split hq hz B ν (n - 1) D
    rw [Nat.sub_add_cancel hn1] at h
    rw [h, if_pos (TcondB_of_even B D q h2 hrev)]
  rw [e1, Finset.sum_add_distrib, EvenPosLayerSum]
  rw [show (∑ n ∈ (Finset.range M).filter (fun n : ℕ => Even n ∧ n ≠ 0),
        ν q * TnB B ν (n - 1) (D / q) (q : ℝ))
      = ν q * OddLayerSum B ν (M - 1) (D / q) (q : ℝ) from by
        rw [← Finset.mul_sum, sum_shift_even B ν (D / q) q M]]

/-! ## Vanishing of the layers beyond the truncation

A nonzero layer sum `T_n(D,y)` requires a chain of `n` distinct primes, which forces `D ≥ 2^n`
(every odd step at a level `≥ 3` imposes `p^{B+1} ≤ D` and `B ≥ 2`).  Hence `T_n(D,y) = 0` once
`n ≥ log₂⌈D⌉₊ + ⌈B⌉₊ + 4`. -/

lemma pow_le_of_TnB_ne_zero (B : ℝ) (hB : 2 ≤ B) (ν : ℕ → ℝ) :
    ∀ n : ℕ, 3 ≤ n → ∀ D y : ℝ, TnB B ν n D y ≠ 0 → (2 : ℝ) ^ n ≤ D := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro h3 D y hne
    rcases Nat.lt_or_ge n 4 with hn4 | hn4
    · -- `3 ≤ n < 4`, so `n = 3`
      have hn3 : n = 3 := by omega
      rw [hn3] at hne ⊢
      have hsum : TnB B ν 3 D y
          = ∑ p ∈ (Nat.primesBelow ⌈y⌉₊).filter (fun p => TcondB B 3 D p),
              ν p * TnB B ν 2 (D / (p : ℝ)) (p : ℝ) := by
        rw [show (3 : ℕ) = 2 + 1 from rfl, TnB]
      rw [hsum] at hne
      obtain ⟨p, hp, hpnz⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
      have hcond : TcondB B 3 D p := (Finset.mem_filter.mp hp).2
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
        have hpbb : p.Prime := (Nat.mem_primesBelow.mp (Finset.mem_filter.mp hp).1).2
        exact_mod_cast hpbb.two_le
      have hcond' : (p : ℝ) ^ (B + 1) ≤ D := (TcondB_of_odd B D p (by norm_num) (by norm_num)).mp hcond
      have hpB : (2 : ℝ) ^ (B + 1) ≤ (p : ℝ) ^ (B + 1) :=
        Real.rpow_le_rpow (by norm_num) hp2 (by linarith)
      have h2B : (2 : ℝ) ^ 3 ≤ (2 : ℝ) ^ (B + 1) := by
        have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
          (by linarith : (3 : ℝ) ≤ B + 1)
        simpa [Real.rpow_natCast] using h
      linarith [h2B, hpB, hcond']
    · -- `n ≥ 4`: peel one prime and use the induction hypothesis at `n - 1`
      have hn1 : 1 ≤ n := by omega
      have hprev : 3 ≤ n - 1 := by omega
      have hlt : n - 1 < n := by omega
      have hsum : TnB B ν (n - 1 + 1) D y
          = ∑ p ∈ (Nat.primesBelow ⌈y⌉₊).filter (fun p => TcondB B (n - 1 + 1) D p),
              ν p * TnB B ν (n - 1) (D / (p : ℝ)) (p : ℝ) := by
        rw [TnB]
      rw [Nat.sub_add_cancel hn1] at hsum
      rw [hsum] at hne
      obtain ⟨p, hp, hpnz⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
      have hpbb : p.Prime := (Nat.mem_primesBelow.mp (Finset.mem_filter.mp hp).1).2
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpbb.two_le
      have hp0 : (0 : ℝ) < (p : ℝ) := lt_of_lt_of_le (by norm_num) hp2
      have htnz : TnB B ν (n - 1) (D / (p : ℝ)) (p : ℝ) ≠ 0 := fun h => hpnz (by rw [h, mul_zero])
      have hpow := ih (n - 1) hlt hprev (D / (p : ℝ)) (p : ℝ) htnz
      have hmul : (2 : ℝ) ^ (n - 1) * (p : ℝ) ≤ D := by
        have := mul_le_mul_of_nonneg_right hpow (le_of_lt hp0)
        rwa [div_mul_cancel₀ D hp0.ne'] at this
      calc (2 : ℝ) ^ n = (2 : ℝ) ^ (n - 1) * 2 := by
            rw [← pow_succ, Nat.sub_add_cancel hn1]
        _ ≤ (2 : ℝ) ^ (n - 1) * (p : ℝ) :=
            mul_le_mul_of_nonneg_left hp2 (by positivity)
        _ ≤ D := hmul

lemma TnB_eq_zero_of_layerCut (B : ℝ) (hB : 2 ≤ B) (ν : ℕ → ℝ) (D y : ℝ) {n : ℕ}
    (hn : Nat.log 2 ⌈D⌉₊ + ⌈B⌉₊ + 4 ≤ n) : TnB B ν n D y = 0 := by
  by_contra hne
  have h3 : 3 ≤ n := by
    have hB0 : 0 < ⌈B⌉₊ := Nat.ceil_pos.mpr (by linarith)
    omega
  have hpow := pow_le_of_TnB_ne_zero B hB ν n h3 D y hne
  have hDceil : (2 : ℕ) ^ n ≤ ⌈D⌉₊ := by
    have h1 : ((2 : ℕ) ^ n : ℝ) ≤ ((⌈D⌉₊ : ℕ) : ℝ) := by
      push_cast
      exact le_trans hpow (Nat.le_ceil D)
    exact_mod_cast h1
  have hlt : (2 : ℕ) ^ n < 2 ^ (Nat.log 2 ⌈D⌉₊ + 1) :=
    lt_of_le_of_lt hDceil (Nat.lt_pow_succ_log_self (by norm_num) ⌈D⌉₊)
  have hnle : n < Nat.log 2 ⌈D⌉₊ + 1 :=
    (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hlt
  omega

/-! ## The induction -/

private theorem main_ind (B : ℝ) (hB : 2 ≤ B) (ν : ℕ → ℝ) (hν1 : ν 1 = 1)
    (hνmul : ∀ m n : ℕ, Nat.Coprime m n → ν (m * n) = ν m * ν n) :
    ∀ m : ℕ, ∀ z : ℝ, ⌈z⌉₊ = m → ∀ D : ℝ, ∀ M : ℕ,
      (Nat.primesBelow m).card < M →
      (OddLayerSum B ν M D z = GpB B ν z D - VfB ν z ∧
       EvenPosLayerSum B ν M D z = VfB ν z - GmB B ν z D) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro z hz D M hM
    rcases Nat.lt_or_ge m 3 with hm3 | hm3
    · -- base case: no primes below `z`
      have hSl : Nat.primesBelow m = ∅ := by
        interval_cases m
        · exact Nat.primesBelow_zero
        · exact Nat.primesBelow_one
        · exact Nat.primesBelow_two
      have hzSl : Nat.primesBelow ⌈z⌉₊ = ∅ := by rw [hz, hSl]
      have hV : VfB ν z = 1 := by rw [VfB, hzSl, Finset.prod_empty]
      have hPb : PB z = 1 := by rw [PB, hzSl, Finset.prod_empty]
      have hGp : GpB B ν z D = 1 := by
        rw [GpB, hPb, Nat.divisors_one, Finset.sum_singleton]
        have hr : rdPlusB B D 1 := by
          intro e he hodd
          rw [Nat.divisors_one, Finset.mem_singleton] at he
          subst he
          simp at hodd
        rw [if_pos hr, ArithmeticFunction.moebius_apply_one, hν1]
        norm_num
      have hGm : GmB B ν z D = 1 := by
        rw [GmB, hPb, Nat.divisors_one, Finset.sum_singleton]
        have hr : rdMinusB B D 1 := by
          intro e he _ he1
          rw [Nat.divisors_one, Finset.mem_singleton] at he
          subst he
          exact absurd rfl he1
        rw [if_pos hr, ArithmeticFunction.moebius_apply_one, hν1]
        norm_num
      have hz2 : z ≤ 2 := by
        have hz2' : ⌈z⌉₊ ≤ 2 := by rw [hz]; omega
        simpa using Nat.ceil_le.mp hz2'
      have hvan : ∀ n : ℕ, n ≠ 0 → TnB B ν n D z = 0 := fun n hn =>
        TnB_eq_zero_of_le_two B ν (Nat.pos_of_ne_zero hn) D hz2
      constructor
      · have hsum0 : (∑ n ∈ (Finset.range M).filter Odd, TnB B ν n D z) = 0 :=
          Finset.sum_eq_zero (fun n hn => hvan n (fun h0 => by
            rw [h0] at hn
            obtain ⟨k, hk⟩ := (Finset.mem_filter.mp hn).2
            omega))
        rw [OddLayerSum, hsum0, hGp, hV]
        norm_num
      · have hsum0 : (∑ n ∈ (Finset.range M).filter (fun n : ℕ => Even n ∧ n ≠ 0),
            TnB B ν n D z) = 0 :=
          Finset.sum_eq_zero (fun n hn => hvan n (Finset.mem_filter.mp hn).2.2)
        rw [EvenPosLayerSum, hsum0, hV, hGm]
        norm_num
    · -- inductive step
      have hmpos : 1 ≤ m := by omega
      have hsucc : Nat.primesBelow m
          = if Nat.Prime (m - 1) then insert (m - 1) (Nat.primesBelow (m - 1))
            else Nat.primesBelow (m - 1) := by
        rw [← Nat.sub_add_cancel hmpos]
        exact Nat.primesBelow_succ (m - 1)
      have hkm : m - 1 < m := by omega
      have hceil : ⌈((m - 1 : ℕ) : ℝ)⌉₊ = m - 1 := Nat.ceil_natCast _
      by_cases hkp : (m - 1).Prime
      · have hz' : Nat.primesBelow ⌈z⌉₊ = insert (m - 1) (Nat.primesBelow (m - 1)) := by
          rw [hz, hsucc, if_pos hkp]
        have hcard : (Nat.primesBelow (m - 1)).card + 1 = (Nat.primesBelow m).card := by
          rw [hsucc, if_pos hkp, Finset.card_insert_of_notMem (Nat.notMem_primesBelow _)]
        have hM1 : (Nat.primesBelow (m - 1)).card < M := by omega
        have hM2 : (Nat.primesBelow (m - 1)).card < M - 1 := by omega
        have hMm2 : 2 ≤ M := by omega
        obtain ⟨ih1o, ih1e⟩ := ih (m - 1) hkm ((m - 1 : ℕ) : ℝ) hceil D M hM1
        obtain ⟨ih2o, ih2e⟩ :=
          ih (m - 1) hkm ((m - 1 : ℕ) : ℝ) hceil (D / ((m - 1 : ℕ) : ℝ)) (M - 1) hM2
        have hB0 : (0 : ℝ) ≤ B := by linarith
        constructor
        · rw [OddLayerSum_split hkp hz' B ν D hMm2, ih1o, ih2e,
            GpB_split hkp hz' hB0 ν hνmul D, VfB_split hz' ν]
          by_cases hG : (((m - 1 : ℕ) : ℝ)) ^ (B + 1) ≤ D
          · rw [if_pos hG, if_pos hG]; ring
          · rw [if_neg hG, if_neg hG]; ring
        · rw [EvenPosLayerSum_split hkp hz' B ν D M, ih1e, ih2o,
            GmB_split hkp hz' hB0 ν hνmul D, VfB_split hz' ν]
          ring
      · have hz' : Nat.primesBelow ⌈z⌉₊ = Nat.primesBelow (m - 1) := by
          rw [hz, hsucc, if_neg hkp]
        have hcard : (Nat.primesBelow (m - 1)).card = (Nat.primesBelow m).card := by
          rw [hsucc, if_neg hkp]
        have hM1 : (Nat.primesBelow (m - 1)).card < M := by omega
        obtain ⟨ih1o, ih1e⟩ := ih (m - 1) hkm ((m - 1 : ℕ) : ℝ) hceil D M hM1
        have hc : Nat.primesBelow ⌈z⌉₊ = Nat.primesBelow ⌈((m - 1 : ℕ) : ℝ)⌉₊ := by rw [hz', hceil]
        constructor
        · rw [OddLayerSum_congr hc B ν M D, ih1o, GpB_congr hc B ν D, VfB_congr ν hc]
        · rw [EvenPosLayerSum_congr hc B ν M D, ih1e, GmB_congr hc B ν D, VfB_congr ν hc]

/-! ## The identity -/

theorem GpB_eq_VfB_add_oddLayers (B : ℝ) (hB : 2 ≤ B) (ν : ℕ → ℝ) (hν1 : ν 1 = 1)
    (hνmul : ∀ m n : ℕ, Nat.Coprime m n → ν (m * n) = ν m * ν n) (D y : ℝ) :
    Work.FIChain.GpB B ν y D = Work.FIChain.VfB ν y + Work.FIChain.OddLayerSum B ν (Work.FIChain.layerCut B D + 1) D y := by
  set Mbig := layerCut B D + 1 + (Nat.primesBelow ⌈y⌉₊).card + 1 with hMbig
  have hcard : (Nat.primesBelow ⌈y⌉₊).card < Mbig := by rw [hMbig]; omega
  obtain ⟨hodd, -⟩ := main_ind B hB ν hν1 hνmul ⌈y⌉₊ y rfl D Mbig hcard
  have hvan : ∀ n : ℕ, layerCut B D + 1 ≤ n → TnB B ν n D y = 0 := by
    intro n hn
    refine TnB_eq_zero_of_layerCut B hB ν D y ?_
    simp only [layerCut] at hn
    omega
  have hsum : OddLayerSum B ν Mbig D y = OddLayerSum B ν (layerCut B D + 1) D y := by
    rw [OddLayerSum, OddLayerSum]
    refine (Finset.sum_subset ?_ ?_).symm
    · intro n hn
      obtain ⟨hnK, hnodd⟩ := Finset.mem_filter.mp hn
      rw [Finset.mem_range] at hnK
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hnodd⟩
    · intro n hn hnot
      obtain ⟨hnM, hnodd⟩ := Finset.mem_filter.mp hn
      rw [Finset.mem_range] at hnM
      refine hvan n ?_
      by_contra h
      exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hnodd⟩)
  linarith

end

end Work.FIChain
