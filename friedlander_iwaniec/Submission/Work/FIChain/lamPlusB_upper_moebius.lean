/-
# `Work.FIChain.lamPlusB_upper_moebius`

The two facts the FI endgame needs about the `B`-delay Rosser–Iwaniec upper weight
`λ⁺_B = Work.FIChain.lamPlusB B D` (defined in `Submission/Work/FIChain/lamPlusBDefs.lean`), for
`B ≥ 2` and `D > 1`:

* `BoundingSieve.IsUpperMoebius (lamPlusB B D)` — equivalently
  `ρ n = Σ_{d ∣ n} λ⁺_B(d) ≥ [n = 1]`, the `SieveInput` conjunct;
* the support bound `Squarefree d → rdPlusB B D d → (d : ℝ) < D`.

This is a verbatim port of `Submission/Work/FIChain/lamPlus_upper_moebius_and_support.lean` (the
case `B = 2`) with the exponent `2` of `cval` replaced by a general real `B ≥ 2`.  The only places
where the exponent enters are

* the weight `cvalB B e = e · (minFac e)^B` (generalising `cval e = e · (minFac e)²`);
* the recursions, where `q³ ≤ D` becomes `q^{B+1} ≤ D` (since `cvalB B q = q·q^B = q^{B+1}`).

The generic arithmetic (`card_aux`, `minFac_mul_prime`, `card_mul_div_minFac`, the
divisor-splitting, the Möbius-at-a-prime factorisation, `lt_cval_of_mul`, `sqKernel`, …) is
imported from that file and reused unchanged.
-/
import Mathlib
import Submission.Work.FIChain.lamPlusBDefs
import Submission.Work.FIChain.lamPlus_upper_moebius_and_support

open Finset
open scoped BigOperators

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace Work.FIChain

noncomputable section

open Classical

attribute [local instance] Classical.propDecidable

/-! ## The general-`B` weight and the general-`B` lower support condition -/

/-- The weight `e · (minFac e)^B` appearing in the `B`-delay Rosser–Iwaniec support conditions. -/
def cvalB (B : ℝ) (e : ℕ) : ℝ := (e : ℝ) * (e.minFac : ℝ) ^ B

/-- The general-`B` **lower** support condition: every divisor `e ≠ 1` of `d` with an even number
of prime factors satisfies `e · (minFac e)^B ≤ D`. -/
def rdMinusB (B D : ℝ) (d : ℕ) : Prop :=
  ∀ e ∈ d.divisors, Even e.primeFactors.card → e ≠ 1 → cvalB B e ≤ D

lemma rdPlusB_iff_cvalB (B D : ℝ) (d : ℕ) :
    rdPlusB B D d ↔ ∀ e ∈ d.divisors, Odd e.primeFactors.card → cvalB B e ≤ D := by
  simp only [rdPlusB, cvalB]

lemma rdMinusB_iff_cvalB (B D : ℝ) (d : ℕ) :
    rdMinusB B D d ↔
      ∀ e ∈ d.divisors, Even e.primeFactors.card → e ≠ 1 → cvalB B e ≤ D :=
  Iff.rfl

/-- The weight at a prime: `cvalB B q = q · q^B = q^{B+1}`. -/
lemma cvalB_prime (B : ℝ) {q : ℕ} (hq : q.Prime) : cvalB B q = (q : ℝ) ^ (B + 1) := by
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq.pos
  unfold cvalB
  rw [hq.minFac_eq, Real.rpow_add hqpos, Real.rpow_one]
  ring

/-! ## Elementary inequalities for `cvalB` -/

/-- **The key inequality.**  For a squarefree `e` with at least two prime factors, removing the
smallest prime factor `p` multiplies the weight `cvalB B` by at least `1/p`:
`cvalB B e ≤ q · cvalB B (e / minFac e)` for any `q ≥ minFac e` (and `B ≥ 0`). -/
lemma cvalB_le_minFac_mul_cvalB_div (B : ℝ) (hB : 0 ≤ B) (e q : ℕ) (hsq : Squarefree e)
    (h2 : 2 ≤ e.primeFactors.card) (hle : e.minFac ≤ q) :
    cvalB B e ≤ (q : ℝ) * cvalB B (e / e.minFac) := by
  have he1 : e ≠ 1 := by intro h; rw [h] at h2; simp at h2
  have hcard := card_mul_div_minFac e hsq he1
  have hf1 : e / e.minFac ≠ 1 := by
    intro h; rw [h] at hcard; simp at hcard; omega
  have hrf : 2 ≤ ((e / e.minFac).minFac) := (Nat.minFac_prime hf1).two_le
  have hdiv : (e / e.minFac).minFac ∣ e :=
    dvd_trans (Nat.minFac_dvd _) (Nat.div_dvd_of_dvd (Nat.minFac_dvd e))
  have hle' : e.minFac ≤ (e / e.minFac).minFac := Nat.minFac_le_of_dvd hrf hdiv
  have hp0 : (0 : ℝ) ≤ (e.minFac : ℝ) := by positivity
  have hf0' : (0 : ℝ) ≤ ((e / e.minFac : ℕ) : ℝ) := by positivity
  have hpr : (e.minFac : ℝ) ≤ (((e / e.minFac).minFac : ℕ) : ℝ) := by exact_mod_cast hle'
  have hpq : (e.minFac : ℝ) ≤ (q : ℝ) := by exact_mod_cast hle
  have h1 : (e.minFac : ℝ) ^ B ≤ (((e / e.minFac).minFac : ℕ) : ℝ) ^ B :=
    Real.rpow_le_rpow hp0 hpr hB
  have hB' : (e.minFac : ℝ) * (e.minFac : ℝ) ^ B
      ≤ (q : ℝ) * ((((e / e.minFac).minFac : ℕ) : ℝ)) ^ B :=
    mul_le_mul hpq h1 (Real.rpow_nonneg hp0 B) (by positivity)
  have hmulR : (e : ℝ) = ((e / e.minFac : ℕ) : ℝ) * (e.minFac : ℝ) := by
    rw [← Nat.cast_mul, Nat.div_mul_cancel (Nat.minFac_dvd e)]
  unfold cvalB
  calc (e : ℝ) * (e.minFac : ℝ) ^ B
      = ((e / e.minFac : ℕ) : ℝ) * ((e.minFac : ℝ) * (e.minFac : ℝ) ^ B) := by
        rw [hmulR]; ring
    _ ≤ ((e / e.minFac : ℕ) : ℝ) * ((q : ℝ) * ((((e / e.minFac).minFac : ℕ) : ℝ)) ^ B) :=
        mul_le_mul_of_nonneg_left hB' hf0'
    _ = (q : ℝ) * (((e / e.minFac : ℕ) : ℝ) * ((((e / e.minFac).minFac : ℕ) : ℝ)) ^ B) := by
        ring

/-- For `e ≠ 1` (so `minFac e ≥ 1`) and `B ≥ 2`, the exponent-`B` weight dominates the
exponent-`2` weight: `cval e ≤ cvalB B e`. -/
lemma cval_le_cvalB (B : ℝ) (hB : 2 ≤ B) {e : ℕ} (he1 : e ≠ 1) : cval e ≤ cvalB B e := by
  have hmf1 : (1 : ℝ) ≤ (e.minFac : ℝ) := by
    exact_mod_cast (le_of_lt (Nat.minFac_prime he1).one_lt)
  have hexp : (e.minFac : ℝ) ^ 2 ≤ (e.minFac : ℝ) ^ B := by
    have h : (e.minFac : ℝ) ^ ((2 : ℕ) : ℝ) ≤ (e.minFac : ℝ) ^ B :=
      Real.rpow_le_rpow_of_exponent_le hmf1 hB
    rwa [Real.rpow_natCast] at h
  unfold cval cvalB
  exact mul_le_mul_of_nonneg_left hexp (by positivity)

/-- **Removing the smallest prime factor increases `cvalB`.**  If `d` is squarefree, `d ≠ 1`, and
`e · minFac d = d` with `e ≠ 1`, then `d < cvalB B e` (for `B ≥ 2`). -/
lemma lt_cvalB_of_mul {B : ℝ} (hB : 2 ≤ B) {d e : ℕ} (hsq : Squarefree d) (hd1 : d ≠ 1)
    (he : e * d.minFac = d) (he1 : e ≠ 1) : (d : ℝ) < cvalB B e := by
  have hlt := lt_cval_of_mul hsq hd1 he he1
  have hle := cval_le_cvalB B hB he1
  linarith

/-- An upper-admissible squarefree `d` satisfies `d < D` (for `D > 1` and `B ≥ 2`). -/
lemma rdPlusB_lt {B D : ℝ} (hB : 2 ≤ B) (hD : 1 < D) {d : ℕ} (hsq : Squarefree d)
    (hd : rdPlusB B D d) : (d : ℝ) < D := by
  have hd2 : rdPlus D d := by
    intro e he hodd
    have he1 : e ≠ 1 := by intro h1; rw [h1] at hodd; simp at hodd
    have h1 : cval e ≤ cvalB B e := cval_le_cvalB B hB he1
    have h2 : cvalB B e ≤ D := hd e he hodd
    simpa only [cval] using le_trans h1 h2
  exact rdPlus_lt hD hsq hd2

/-! ## The two recursions for the general-`B` support conditions -/

/-- **First recursion.**  Multiplying the modulus by a prime `q` larger than all its prime
factors exchanges the lower `B`-support condition at level `D` with the upper one at level `D/q`. -/
lemma rdMinusB_mul_prime {B : ℝ} (hB : 0 ≤ B) {q d : ℕ} (hq : q.Prime) (hd : Squarefree d)
    (hcop : ¬ q ∣ d) (hbig : ∀ p ∈ d.primeFactors, p < q) (D : ℝ) :
    rdMinusB B D (q * d) ↔ rdPlusB B (D / q) d := by
  have hd0 : d ≠ 0 := fun h => hcop (h ▸ dvd_zero q)
  have hqd0 : q * d ≠ 0 := Nat.mul_ne_zero hq.ne_zero hd0
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq.pos
  have hmin_lt : ∀ {f : ℕ}, f ∣ d → f ≠ 1 → f.minFac < q := by
    intro f hfd hf1
    have hf0 : f ≠ 0 := div_ne_zero_of_dvd hfd hd0
    exact hbig _ (primeFactors_subset_of_dvd hfd hd0
      (Nat.mem_primeFactors.mpr ⟨Nat.minFac_prime hf1, Nat.minFac_dvd f, hf0⟩))
  rw [rdMinusB_iff_cvalB, rdPlusB_iff_cvalB]
  constructor
  · intro h f hf hodd
    obtain ⟨hfd, -⟩ := Nat.mem_divisors.mp hf
    have hf0 : f ≠ 0 := div_ne_zero_of_dvd hfd hd0
    have hf1 : f ≠ 1 := by intro h1; rw [h1] at hodd; simp at hodd
    have hfqd : q * f ∈ (q * d).divisors :=
      Nat.mem_divisors.mpr ⟨Nat.mul_dvd_mul_left q hfd, hqd0⟩
    have hnot : ¬ q ∣ f := fun hqf => hcop (dvd_trans hqf hfd)
    have h2 := card_aux q f hq hf0 hnot
    have heven : Even (q * f).primeFactors.card := by
      rw [h2]; exact even_succ_of_odd hodd
    have hne1 : q * f ≠ 1 := by
      have : 2 ≤ q * f := Nat.mul_le_mul hq.two_le (Nat.one_le_iff_ne_zero.mpr hf0)
      omega
    have hle := h (q * f) hfqd heven hne1
    have hcq : cvalB B (q * f) = (q : ℝ) * cvalB B f := by
      unfold cvalB
      rw [minFac_mul_prime hq hf1 (hmin_lt hfd hf1), Nat.cast_mul]
      ring
    rw [hcq] at hle
    rw [le_div_iff₀ hqpos]
    linarith
  · intro h e he heven he1
    obtain ⟨hedvd, -⟩ := Nat.mem_divisors.mp he
    by_cases hqe : q ∣ e
    · obtain ⟨f, rfl⟩ := hqe
      have hfd : f ∣ d := (Nat.mul_dvd_mul_iff_left hq.pos).mp hedvd
      have hfmem : f ∈ d.divisors := Nat.mem_divisors.mpr ⟨hfd, hd0⟩
      have hf0 : f ≠ 0 := div_ne_zero_of_dvd hfd hd0
      have h3 := card_aux q f hq hf0 (fun hqf => hcop (dvd_trans hqf hfd))
      have hodd : Odd f.primeFactors.card := by
        rw [h3] at heven
        exact odd_of_even_succ heven
      have hf1 : f ≠ 1 := by intro h1; rw [h1] at hodd; simp at hodd
      have hle := h f hfmem hodd
      have hcq : cvalB B (q * f) = (q : ℝ) * cvalB B f := by
        unfold cvalB
        rw [minFac_mul_prime hq hf1 (hmin_lt hfd hf1), Nat.cast_mul]
        ring
      rw [hcq]
      rw [le_div_iff₀ hqpos] at hle
      linarith
    · have hed : e ∣ d := ((hq.coprime_iff_not_dvd.mpr hqe).symm).dvd_of_dvd_mul_left hedvd
      have hsqe : Squarefree e := Squarefree.squarefree_of_dvd hed hd
      have he0 : e ≠ 0 := div_ne_zero_of_dvd hed hd0
      have he2 : 2 ≤ e.primeFactors.card := by
        have h1 : 1 ≤ e.primeFactors.card := by
          have hne : e.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr (by omega)
          exact Finset.card_pos.mpr hne
        obtain ⟨k, hk⟩ := heven
        omega
      have hcf := card_mul_div_minFac e hsqe he1
      have hodd : Odd (e / e.minFac).primeFactors.card := by
        rw [hcf] at heven
        exact odd_of_even_succ heven
      have hfmem : e / e.minFac ∈ d.divisors :=
        Nat.mem_divisors.mpr ⟨dvd_trans (Nat.div_dvd_of_dvd (Nat.minFac_dvd e)) hed, hd0⟩
      have hle := h _ hfmem hodd
      have hleminfac : e.minFac ≤ q := by
        have hp : (e.minFac).Prime := Nat.minFac_prime he1
        have hdvd : e.minFac ∣ q * d := dvd_trans (Nat.minFac_dvd e) hedvd
        rcases hp.dvd_mul.mp hdvd with h1 | h1
        · have : q = e.minFac := (hq.dvd_iff_eq hp.ne_one).mp h1
          omega
        · exact le_of_lt (hbig _ (Nat.mem_primeFactors.mpr ⟨hp, h1, hd0⟩))
      have hkey := cvalB_le_minFac_mul_cvalB_div B hB e q hsqe he2 hleminfac
      rw [le_div_iff₀ hqpos] at hle
      linarith

/-- **Second recursion.**  Multiplying the modulus by a prime `q` larger than all its prime
factors turns the upper `B`-support condition at level `D` into `q^{B+1} ≤ D` together with the
lower condition at level `D/q`. -/
lemma rdPlusB_mul_prime {B : ℝ} (hB : 0 ≤ B) {q d : ℕ} (hq : q.Prime) (hd : Squarefree d)
    (hcop : ¬ q ∣ d) (hbig : ∀ p ∈ d.primeFactors, p < q) (D : ℝ) :
    rdPlusB B D (q * d) ↔ (q : ℝ) ^ (B + 1) ≤ D ∧ rdMinusB B (D / q) d := by
  have hd0 : d ≠ 0 := fun h => hcop (h ▸ dvd_zero q)
  have hqd0 : q * d ≠ 0 := Nat.mul_ne_zero hq.ne_zero hd0
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq.pos
  have hmin_lt : ∀ {f : ℕ}, f ∣ d → f ≠ 1 → f.minFac < q := by
    intro f hfd hf1
    have hf0 : f ≠ 0 := div_ne_zero_of_dvd hfd hd0
    exact hbig _ (primeFactors_subset_of_dvd hfd hd0
      (Nat.mem_primeFactors.mpr ⟨Nat.minFac_prime hf1, Nat.minFac_dvd f, hf0⟩))
  rw [rdPlusB_iff_cvalB, rdMinusB_iff_cvalB]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have hmem : q ∈ (q * d).divisors := Nat.mem_divisors.mpr ⟨dvd_mul_right q d, hqd0⟩
      have hodd : Odd q.primeFactors.card := by rw [hq.primeFactors]; simp
      have hle := h q hmem hodd
      have hcq : cvalB B q = (q : ℝ) ^ (B + 1) := cvalB_prime B hq
      rwa [hcq] at hle
    · intro e he heven he1
      obtain ⟨hed, -⟩ := Nat.mem_divisors.mp he
      have he0 : e ≠ 0 := div_ne_zero_of_dvd hed hd0
      have hmeme : q * e ∈ (q * d).divisors :=
        Nat.mem_divisors.mpr ⟨Nat.mul_dvd_mul_left q hed, hqd0⟩
      have h2 := card_aux q e hq he0 (fun hqe => hcop (dvd_trans hqe hed))
      have hodd : Odd (q * e).primeFactors.card := by
        rw [h2]; exact Even.add_one heven
      have hle := h (q * e) hmeme hodd
      have hcq : cvalB B (q * e) = (q : ℝ) * cvalB B e := by
        unfold cvalB
        rw [minFac_mul_prime hq he1 (hmin_lt hed he1), Nat.cast_mul]
        ring
      rw [hcq] at hle
      rw [le_div_iff₀ hqpos]
      linarith
  · rintro ⟨h3, h⟩ e he hodd
    obtain ⟨hedvd, -⟩ := Nat.mem_divisors.mp he
    by_cases hqe : q ∣ e
    · obtain ⟨f, rfl⟩ := hqe
      have hfd : f ∣ d := (Nat.mul_dvd_mul_iff_left hq.pos).mp hedvd
      have hf0 : f ≠ 0 := div_ne_zero_of_dvd hfd hd0
      rcases eq_or_ne f 1 with hf | hf
      · have hcq : cvalB B (q * f) = (q : ℝ) ^ (B + 1) := by
          rw [hf, mul_one]; exact cvalB_prime B hq
        rw [hcq]; exact h3
      · have h2 := card_aux q f hq hf0 (fun hqf => hcop (dvd_trans hqf hfd))
        have heven' : Even f.primeFactors.card := by
          rw [h2] at hodd
          exact even_of_odd_succ hodd
        have hle := h f (Nat.mem_divisors.mpr ⟨hfd, hd0⟩) heven' hf
        have hcq : cvalB B (q * f) = (q : ℝ) * cvalB B f := by
          unfold cvalB
          rw [minFac_mul_prime hq hf (hmin_lt hfd hf), Nat.cast_mul]
          ring
        rw [hcq]
        rw [le_div_iff₀ hqpos] at hle
        linarith
    · have hed : e ∣ d := ((hq.coprime_iff_not_dvd.mpr hqe).symm).dvd_of_dvd_mul_left hedvd
      have hsqe : Squarefree e := Squarefree.squarefree_of_dvd hed hd
      have he0 : e ≠ 0 := div_ne_zero_of_dvd hed hd0
      have he1 : e ≠ 1 := by intro h1; rw [h1] at hodd; simp at hodd
      have hcard : e.primeFactors.card = 1 ∨ 3 ≤ e.primeFactors.card := by
        obtain ⟨k, hk⟩ := hodd
        omega
      rcases hcard with hc1 | hc3
      · have hep : e.Prime := prime_of_card_primeFactors_eq_one hsqe hc1
        have helt : e < q := hbig e (Nat.mem_primeFactors.mpr ⟨hep, hed, hd0⟩)
        have hcq : cvalB B e = (e : ℝ) ^ (B + 1) := cvalB_prime B hep
        rw [hcq]
        have hle : (e : ℝ) ≤ (q : ℝ) := by exact_mod_cast (le_of_lt helt)
        have h3' : (e : ℝ) ^ (B + 1) ≤ (q : ℝ) ^ (B + 1) :=
          Real.rpow_le_rpow (by positivity) hle (by linarith)
        linarith
      · have hcf := card_mul_div_minFac e hsqe he1
        have heven : Even (e / e.minFac).primeFactors.card := by
          rw [hcf] at hodd
          exact even_of_odd_succ hodd
        have hf1 : e / e.minFac ≠ 1 := by
          intro h1
          rw [h1] at hcf
          simp at hcf
          omega
        have hfmem : e / e.minFac ∈ d.divisors :=
          Nat.mem_divisors.mpr ⟨dvd_trans (Nat.div_dvd_of_dvd (Nat.minFac_dvd e)) hed, hd0⟩
        have hle := h _ hfmem heven hf1
        have hleminfac : e.minFac ≤ q := le_of_lt (hbig _
          (Nat.mem_primeFactors.mpr ⟨Nat.minFac_prime he1, dvd_trans (Nat.minFac_dvd e) hed, hd0⟩))
        have hkey := cvalB_le_minFac_mul_cvalB_div B hB e q hsqe (by omega) hleminfac
        rw [le_div_iff₀ hqpos] at hle
        linarith

/-! ## The Möbius sums `WmB`, `WpB` and their recursions -/

/-- The general-`B` lower Rosser–Iwaniec Möbius sum `Σ_{d ∣ n, rdMinusB D d} μ(d)`. -/
noncomputable def WmB (B : ℝ) (n : ℕ) (D : ℝ) : ℝ :=
  ∑ d ∈ n.divisors, (if rdMinusB B D d then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0)

/-- The general-`B` upper Rosser–Iwaniec Möbius sum `Σ_{d ∣ n, rdPlusB D d} μ(d)`. -/
noncomputable def WpB (B : ℝ) (n : ℕ) (D : ℝ) : ℝ :=
  ∑ d ∈ n.divisors, (if rdPlusB B D d then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0)

lemma WmB_mul_prime {B : ℝ} (hB : 0 ≤ B) {q d : ℕ} (hq : q.Prime) (hd : Squarefree d)
    (hcop : ¬ q ∣ d) (hbig : ∀ p ∈ d.primeFactors, p < q) (D : ℝ) :
    WmB B (q * d) D = WmB B d D - WpB B d (D / q) := by
  have hd0 : d ≠ 0 := fun h => hcop (h ▸ dvd_zero q)
  have hterm : ∀ f ∈ d.divisors,
      (if rdMinusB B D (q * f) then ((ArithmeticFunction.moebius (q * f) : ℤ) : ℝ) else 0)
        = - (if rdPlusB B (D / q) f then ((ArithmeticFunction.moebius f : ℤ) : ℝ) else 0) := by
    intro f hf
    obtain ⟨hfd, -⟩ := Nat.mem_divisors.mp hf
    have hsqf : Squarefree f := Squarefree.squarefree_of_dvd hfd hd
    have hqnf : ¬ q ∣ f := fun hqf => hcop (dvd_trans hqf hfd)
    have hbig' : ∀ p ∈ f.primeFactors, p < q :=
      fun p hp => hbig p (primeFactors_subset_of_dvd hfd hd0 hp)
    have hiff := rdMinusB_mul_prime hB hq hsqf hqnf hbig' D
    have hmu := moebius_mul_prime hq hqnf
    by_cases h1 : rdPlusB B (D / q) f
    · rw [if_pos (hiff.mpr h1), if_pos h1, hmu] <;> ring
    · rw [if_neg (fun hc => h1 (hiff.mp hc)), if_neg h1] <;> ring
  calc WmB B (q * d) D
      = (∑ f ∈ d.divisors, (if rdMinusB B D f then ((ArithmeticFunction.moebius f : ℤ) : ℝ) else 0))
        + (∑ f ∈ d.divisors,
            (if rdMinusB B D (q * f) then ((ArithmeticFunction.moebius (q * f) : ℤ) : ℝ) else 0)) := by
          rw [WmB, sum_divisors_mul_prime_ri
              (fun f => if rdMinusB B D f then ((ArithmeticFunction.moebius f : ℤ) : ℝ) else 0)
              q d hq hcop]
    _ = (∑ f ∈ d.divisors, (if rdMinusB B D f then ((ArithmeticFunction.moebius f : ℤ) : ℝ) else 0))
        - (∑ f ∈ d.divisors,
            (if rdPlusB B (D / q) f then ((ArithmeticFunction.moebius f : ℤ) : ℝ) else 0)) := by
          rw [Finset.sum_congr rfl hterm, Finset.sum_neg_distrib]; ring
    _ = WmB B d D - WpB B d (D / q) := by rw [WmB, WpB]

lemma WpB_mul_prime {B : ℝ} (hB : 0 ≤ B) {q d : ℕ} (hq : q.Prime) (hd : Squarefree d)
    (hcop : ¬ q ∣ d) (hbig : ∀ p ∈ d.primeFactors, p < q) (D : ℝ) :
    WpB B (q * d) D = WpB B d D - (if (q : ℝ) ^ (B + 1) ≤ D then WmB B d (D / q) else 0) := by
  have hd0 : d ≠ 0 := fun h => hcop (h ▸ dvd_zero q)
  have hterm : ∀ f ∈ d.divisors,
      (if rdPlusB B D (q * f) then ((ArithmeticFunction.moebius (q * f) : ℤ) : ℝ) else 0)
        = - (if (q : ℝ) ^ (B + 1) ≤ D then
              (if rdMinusB B (D / q) f then ((ArithmeticFunction.moebius f : ℤ) : ℝ) else 0)
              else 0) := by
    intro f hf
    obtain ⟨hfd, -⟩ := Nat.mem_divisors.mp hf
    have hsqf : Squarefree f := Squarefree.squarefree_of_dvd hfd hd
    have hqnf : ¬ q ∣ f := fun hqf => hcop (dvd_trans hqf hfd)
    have hbig' : ∀ p ∈ f.primeFactors, p < q :=
      fun p hp => hbig p (primeFactors_subset_of_dvd hfd hd0 hp)
    have hiff := rdPlusB_mul_prime hB hq hsqf hqnf hbig' D
    have hmu := moebius_mul_prime hq hqnf
    by_cases h2 : (q : ℝ) ^ (B + 1) ≤ D
    · rw [if_pos h2]
      by_cases h1 : rdMinusB B (D / q) f
      · rw [if_pos (hiff.mpr ⟨h2, h1⟩), if_pos h1, hmu] <;> ring
      · rw [if_neg (fun hc => h1 (hiff.mp hc).2), if_neg h1] <;> ring
    · rw [if_neg (fun hc => h2 (hiff.mp hc).1), if_neg h2] <;> ring
  calc WpB B (q * d) D
      = (∑ f ∈ d.divisors, (if rdPlusB B D f then ((ArithmeticFunction.moebius f : ℤ) : ℝ) else 0))
        + (∑ f ∈ d.divisors,
            (if rdPlusB B D (q * f) then ((ArithmeticFunction.moebius (q * f) : ℤ) : ℝ) else 0)) := by
          rw [WpB, sum_divisors_mul_prime_ri
              (fun f => if rdPlusB B D f then ((ArithmeticFunction.moebius f : ℤ) : ℝ) else 0)
              q d hq hcop]
    _ = (∑ f ∈ d.divisors, (if rdPlusB B D f then ((ArithmeticFunction.moebius f : ℤ) : ℝ) else 0))
        - (∑ f ∈ d.divisors, (if (q : ℝ) ^ (B + 1) ≤ D then
            (if rdMinusB B (D / q) f then ((ArithmeticFunction.moebius f : ℤ) : ℝ) else 0) else 0)) := by
          rw [Finset.sum_congr rfl hterm, Finset.sum_neg_distrib]; ring
    _ = WpB B d D - (if (q : ℝ) ^ (B + 1) ≤ D then WmB B d (D / q) else 0) := by
          rw [WpB]
          by_cases hc : (q : ℝ) ^ (B + 1) ≤ D
          · simp only [if_pos hc, WmB]
          · simp only [if_neg hc]
            simp

/-! ## The minorant/majorant property of `λ⁻_B` / `λ⁺_B` -/

theorem WmB_WpB_bounds {B : ℝ} (hB : 2 ≤ B) : ∀ n : ℕ, Squarefree n →
    (∀ D : ℝ, 0 ≤ D → WmB B n D ≤ (if n = 1 then 1 else 0)) ∧
    (∀ D : ℝ, 0 ≤ D → (if n = 1 then 1 else 0) ≤ WpB B n D) := by
  have hB0 : (0 : ℝ) ≤ B := le_trans (by norm_num) hB
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    rcases eq_or_ne n 0 with h0 | h0
    · exact absurd (h0 ▸ hn) not_squarefree_zero
    rcases eq_or_ne n 1 with h1 | h1
    · subst h1
      constructor
      · intro D _
        rw [WmB, Nat.divisors_one, Finset.sum_singleton]
        have hrd : rdMinusB B D 1 := by
          rw [rdMinusB]
          intro e he _ he1
          exact absurd (Nat.dvd_one.mp (Nat.mem_divisors.mp he).1) he1
        rw [if_pos hrd, ArithmeticFunction.moebius_apply_one, if_pos rfl]
        norm_num
      · intro D _
        rw [WpB, Nat.divisors_one, Finset.sum_singleton]
        have hrd : rdPlusB B D 1 := by
          rw [rdPlusB]
          intro e he hodd
          exact absurd hodd (by rw [Nat.dvd_one.mp (Nat.mem_divisors.mp he).1]; simp)
        rw [if_pos hrd, ArithmeticFunction.moebius_apply_one, if_pos rfl]
        norm_num
    · have hn2 : 1 < n := by omega
      set q := n.primeFactors.max' (Nat.nonempty_primeFactors.mpr hn2) with hqdef
      have hqmem : q ∈ n.primeFactors := Finset.max'_mem _ _
      have hqprime : q.Prime := (Nat.mem_primeFactors.mp hqmem).1
      have hqdvd : q ∣ n := (Nat.mem_primeFactors.mp hqmem).2.1
      have hqmax : ∀ p ∈ n.primeFactors, p ≤ q := fun p hp => Finset.le_max' _ p hp
      set m := n / q with hmdef
      have hmul : q * m = n := Nat.mul_div_cancel' hqdvd
      have hmsq : Squarefree m := by
        have hh := hn; rw [← hmul] at hh; exact hh.of_mul_right
      have hmlt : m < n := Nat.div_lt_self (Nat.pos_of_ne_zero h0) hqprime.one_lt
      have hcop : ¬ q ∣ m := by
        intro hdiv
        have hqq : q * q ∣ q * m := Nat.mul_dvd_mul_left q hdiv
        rw [hmul] at hqq
        exact (Nat.squarefree_iff_prime_squarefree.mp hn) q hqprime hqq
      have hbig : ∀ p ∈ m.primeFactors, p < q := by
        intro p hp
        have hp_n : p ∈ n.primeFactors := by
          obtain ⟨hp1, hp2, -⟩ := Nat.mem_primeFactors.mp hp
          exact Nat.mem_primeFactors.mpr
            ⟨hp1, dvd_trans hp2 (by rw [← hmul]; exact dvd_mul_left m q), h0⟩
        have hle : p ≤ q := hqmax p hp_n
        have hne : p ≠ q := by
          intro hpq
          exact hcop (hpq ▸ (Nat.mem_primeFactors.mp hp).2.1)
        omega
      have ih' := ih m hmlt hmsq
      constructor
      · intro D hD
        have hDq : 0 ≤ D / q := div_nonneg hD (by positivity)
        have hWm : WmB B n D = WmB B m D - WpB B m (D / q) := by
          rw [← hmul]; exact WmB_mul_prime hB0 hqprime hmsq hcop hbig D
        rw [hWm, if_neg h1]
        have h1' := ih'.1 D hD
        have h2' := ih'.2 (D / q) hDq
        linarith
      · intro D hD
        have hDq : 0 ≤ D / q := div_nonneg hD (by positivity)
        have hWp : WpB B n D
            = WpB B m D - (if (q : ℝ) ^ (B + 1) ≤ D then WmB B m (D / q) else 0) := by
          rw [← hmul]; exact WpB_mul_prime hB0 hqprime hmsq hcop hbig D
        rw [hWp, if_neg h1]
        have h1' := ih'.2 D hD
        have h2' := ih'.1 (D / q) hDq
        have hnn : (0 : ℝ) ≤ (if m = 1 then 1 else 0) := by split <;> norm_num
        by_cases hc : (q : ℝ) ^ (B + 1) ≤ D
        · rw [if_pos hc]; linarith
        · rw [if_neg hc]; linarith

/-! ## The target -/

theorem lamPlusB_upper_moebius (B : ℝ) (hB : 2 ≤ B) (D : ℝ) (hD : 1 < D) :
    BoundingSieve.IsUpperMoebius (Work.FIChain.lamPlusB B D) ∧
      (∀ d : ℕ, Squarefree d → Work.FIChain.rdPlusB B D d → (d : ℝ) < D) := by
  refine ⟨?_, ?_⟩
  · intro n
    have hD0 : 0 ≤ D := le_of_lt (lt_trans zero_lt_one hD)
    rcases eq_or_ne n 0 with h0 | hn0
    · subst h0
      rw [Nat.divisors_zero, Finset.sum_empty]
      norm_num
    · have hsl : Squarefree (sqKernel n) := squarefree_sqKernel n
      have hsub : (sqKernel n).divisors ⊆ n.divisors := by
        intro d hd
        exact Nat.mem_divisors.mpr
          ⟨dvd_trans (Nat.mem_divisors.mp hd).1 (sqKernel_dvd n), hn0⟩
      have hzero : ∀ d ∈ n.divisors, d ∉ (sqKernel n).divisors →
          (if rdPlusB B D d then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0) = 0 := by
        intro d hd hnot
        have hnsq : ¬ Squarefree d := fun hsq =>
          hnot (Nat.mem_divisors.mpr
            ⟨dvd_sqKernel_of_squarefree_dvd hn0 hsq (Nat.mem_divisors.mp hd).1,
             sqKernel_ne_zero hn0⟩)
        rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnsq]
        split <;> norm_num
      have hbound := (WmB_WpB_bounds hB (sqKernel n) hsl).2 D hD0
      have hkn : (if n = 1 then (1 : ℝ) else 0)
          ≤ (if sqKernel n = 1 then (1 : ℝ) else 0) := by
        by_cases hn1 : n = 1
        · subst hn1
          rw [if_pos rfl, if_pos sqKernel_one]
        · rw [if_neg hn1]
          split <;> norm_num
      have hsum : WpB B (sqKernel n) D = ∑ d ∈ n.divisors, lamPlusB B D d := by
        rw [WpB, Finset.sum_subset hsub hzero]
        exact Finset.sum_congr rfl (fun d _ => by rw [lamPlusB])
      calc (if n = 1 then (1 : ℝ) else 0)
          ≤ (if sqKernel n = 1 then (1 : ℝ) else 0) := hkn
        _ ≤ WpB B (sqKernel n) D := hbound
        _ = ∑ d ∈ n.divisors, lamPlusB B D d := hsum
  · intro d hsq hd
    exact rdPlusB_lt hB hD hsq hd

end

end Work.FIChain
