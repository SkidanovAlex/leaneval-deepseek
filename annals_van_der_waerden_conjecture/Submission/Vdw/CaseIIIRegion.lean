import Mathlib
import Submission.Vdw.CaseI
import Submission.Vdw.CaseIIIField
import Submission.Commons.Analysis.Asymptotics.isBigO_of_eventually_le

open Polynomial Asymptotics
open scoped BigOperators
open Filter

set_option autoImplicit false
set_option linter.style.haveILetI false

/-!
# Case III: the region predicate, the large-prime part `A`, and subcase (ii)

This module fixes the **shape** of the Case-III subcase-(ii) region and its
counting interface.  The arithmetic counting half (`CaseIIIAssembly`,
`CaseIIIWrapper`) bounds `CaseIIIArithSet B n H` (box polys admitting an
admissible squarefree `A`, primes `≥ B`, with `p | Disc f`), and the
field-side chain (`CaseIIIField`) supplies per-prime divisibility from the
field data.  Here we assemble the *region*:

* `largePart D B` — the large-prime part `A := ∏_{p | D, B ≤ p} p` of a
  natural discriminant `D` (in the application `D = D_f = fieldDisc f`,
  `B` = the prime threshold; the primes of `C_f = radical D_f` are the same
  as those of `D_f`, since a prime divides the radical iff it divides the
  number);
* pure facts: `largePart` is squarefree and its prime factors are exactly the
  primes `p | D` with `B ≤ p` (`Nat.primeFactors_prod` — Mathlib);
* `squarefull_fieldDisc`-region `CaseIIISubcase2 n H B` — irreducible box
  polynomials `f` of degree `n` with squarefull `D_f`, `DD(u_f) ≠ 0`, and
  `H < largePart (fieldDisc f) B` (= subcase (ii): the large-prime part of
  `C_f` exceeds `H`);
* `mem_arith_of_largePart` — such an `f` lies in the arithmetic set
  `CaseIIIArithSet B n H` (chains of `CaseIIIField`);
* `CaseIIISubcase2_subset_arith` / `CaseIIISubcase2_ncard_le_arith` — the
  region count is at most the arithmetic count;
* `CaseIIISubcase2_isBigO_of_threshold` — for any threshold family
  `Bfun : ℕ → ℕ` eventually satisfying `n < Bfun H` and `H ≤ (Bfun H)^M`
  (i.e. `Bfun H ≥ H^(1/M)`), the subcase-(ii) region count is
  `O(H^(n-1))`.

Members of the eventual Case-III-bad class (irreducible, primitive-proper,
`C_f > H^(1+δ)`, subcase-(ii) `A > H`, `DD(u_f) ≠ 0`) enter
`CaseIIISubcase2 n H B` with `B := ⌈H^(δ/2)⌉` via
`squarefull_fieldDisc_of_primitive_card_lt` (squarefullness) and the Gauss
link `irreducible_rat_not_reducible` (irreducibility) — the remaining
region-design details (choosing `Bfun`, the `DD(u_f) = 0` piece, subcase (i),
and the eventual Case I/II/III covering of the irreducible part) are recorded
for the assembly sessions.
-/

namespace Submission.Vdw

noncomputable section

/-- The **large-prime part** of a natural number `D` above the threshold `B`:
`A := ∏_{p | D, B ≤ p} p` (squarefree, primes exactly the prime divisors of
`D` that are `≥ B`).  In the application `D = D_f = |Disc K_f|` and
`B` is the Case-III threshold; since a prime divides `C_f = radical(D_f)`
iff it divides `D_f`, the primes of `C_f` above `B` are exactly those here. -/
def largePart (D B : ℕ) : ℕ :=
  ∏ p ∈ D.primeFactors.filter (fun p => B ≤ p), p

/-- A product of primes (each appearing at most once, over a Finset) is
squarefree. -/
lemma squarefree_prod_primes {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) :
    Squarefree (∏ p ∈ s, p) := by
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp hpp
  have hq : (∏ p ∈ s, p) ≠ 0 := Finset.prod_ne_zero_iff.2 (fun p hp => (hs p hp).ne_zero)
  have hpd : p ∣ (∏ p ∈ s, p) := dvd_trans (dvd_mul_left p p) hpp
  have hmem : p ∈ s := by
    have hpF : p ∈ (∏ p ∈ s, p).primeFactors := Nat.Prime.mem_primeFactors hp hpd hq
    rwa [Nat.primeFactors_prod hs] at hpF
  let rest : ℕ := ∏ q ∈ s.erase p, q
  have hs_insert : s = insert p (s.erase p) := (Finset.insert_erase hmem).symm
  have hprod : (∏ q ∈ s, q) = p * rest := by
    rw [← Finset.insert_erase hmem, Finset.prod_insert (by simp)]
  have hpp' : p * p ∣ p * rest := by rwa [hprod] at hpp
  rcases hpp' with ⟨k, hk⟩
  have hk' : rest = p * k := by
    have : p * rest = p * (p * k) := by
      simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hk
    exact Nat.mul_left_cancel (Nat.pos_of_ne_zero hp.ne_zero) this
  have hpd_rest : p ∣ rest := ⟨k, hk'⟩
  have hrest0 : rest ≠ 0 := by
    dsimp [rest]
    exact Finset.prod_ne_zero_iff.2 (fun q hq => (hs q (Finset.mem_of_mem_erase hq)).ne_zero)
  have hmem2 : p ∈ rest.primeFactors := Nat.Prime.mem_primeFactors hp hpd_rest hrest0
  have hmemErase : p ∈ s.erase p := by
    have hpf : (∏ q ∈ s.erase p, q).primeFactors = s.erase p :=
      Nat.primeFactors_prod (fun q hq => hs q (Finset.mem_of_mem_erase hq))
    have hmem2' : p ∈ (∏ q ∈ s.erase p, q).primeFactors := by simpa [rest] using hmem2
    rwa [hpf] at hmem2'
  exact (Finset.mem_erase.mp hmemErase).1 rfl

/-- `largePart` is squarefree: it is a product of distinct primes (the prime
divisors of `D` that are `≥ B`). -/
lemma squarefree_largePart (D B : ℕ) : Squarefree (largePart D B) := by
  unfold largePart
  exact squarefree_prod_primes (by
    intro p hp
    exact Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1)

/-- The prime factors of `largePart D B` are exactly the prime divisors of
`D` that are `≥ B`. -/
lemma largePart_primeFactors (D B : ℕ) :
    (largePart D B).primeFactors = (D.primeFactors).filter (fun p => B ≤ p) := by
  unfold largePart
  exact Nat.primeFactors_prod (by
    intro p hp
    exact Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1)

/-- Every prime divisor of `largePart D B` divides `D` (for `D ≠ 0`). -/
lemma prime_dvd_of_mem_largePart_primeFactors {D B p : ℕ} (hD : D ≠ 0)
    (hp : p ∈ (largePart D B).primeFactors) : p ∣ D := by
  have hpf := largePart_primeFactors D B
  have hp' : p ∈ (D.primeFactors).filter (fun p => B ≤ p) := by rwa [hpf] at hp
  have hpD : p ∈ D.primeFactors := (Finset.mem_filter.mp hp').1
  exact (Nat.mem_primeFactors_of_ne_zero hD).mp hpD |>.2

/-- Every prime divisor of `largePart D B` is at least the threshold `B`. -/
lemma le_of_mem_largePart_primeFactors {D B p : ℕ}
    (hp : p ∈ (largePart D B).primeFactors) : B ≤ p := by
  have hpf := largePart_primeFactors D B
  have hp' : p ∈ (D.primeFactors).filter (fun p => B ≤ p) := by rwa [hpf] at hp
  exact (Finset.mem_filter.mp hp').2

/-- A prime divisor `p` of `D` with `B ≤ p` divides `largePart D B`. -/
lemma prime_dvd_largePart_of_le {D B p : ℕ} (hpF : p ∈ D.primeFactors) (hB : B ≤ p) :
    p ∣ largePart D B := by
  unfold largePart
  have hp' : p ∈ (D.primeFactors).filter (fun p => B ≤ p) := Finset.mem_filter.mpr ⟨hpF, hB⟩
  exact Finset.dvd_prod_of_mem (fun q : ℕ => q) hp'

/-- `largePart D B` is a divisor of `D` (each of its prime factors divides
`D`, and `largePart D B` is squarefree). -/
lemma largePart_dvd {D B : ℕ} (hD : D ≠ 0) : largePart D B ∣ D := by
  classical
  have hsq : Squarefree (largePart D B) := squarefree_largePart D B
  have hpf : ∀ p ∈ (largePart D B).primeFactors, p ∣ D := fun p hp => prime_dvd_of_mem_largePart_primeFactors hD hp
  exact dvd_of_forall_primeFactors_dvd_of_squarefree (largePart D B) D hsq hpf

/-- `largePart D B` is nonzero when `D ≠ 0`. -/
lemma largePart_ne_zero {D B : ℕ} (hD : D ≠ 0) : largePart D B ≠ 0 := by
  intro hz
  have hdvd : largePart D B ∣ D := largePart_dvd hD
  have hz0 : largePart D B = 0 := hz
  -- 0 | D only if D = 0
  rcases hdvd with ⟨c, hc⟩
  rw [hz0, zero_mul] at hc
  exact hD hc

end

section Region

/-- `fieldDisc` with an explicit irreducibility proof (instance-free — usable
inside set comprehensions, where no `Fact` instance is available). -/
noncomputable def fieldDiscExp (f : ℤ[X]) (h : Irreducible (f.map φℚ)) : ℕ :=
  @fieldDisc (f := f) (Fact.mk h)

/-- The **Case-III subcase-(ii) region** (squarefull-`D_f` form): irreducible
box polynomials `f` of degree `n` (the irreducibility witness `h` makes the
field data `D_f = fieldDiscExp f h` available) such that `D_f` is squarefull,
`DD(u_f) ≠ 0`, and the large-prime part `A = largePart D_f B` exceeds `H`.
(The Case-III-bad polys — irreducible, primitive proper, `C_f > H^(1+δ)`,
subcase (ii) `A > H` — lie here via `squarefull_fieldDisc_of_primitive_card_lt`
and the Gauss irreducibility link; see the module docstring.) -/
noncomputable def CaseIIISubcase2 (n H B : ℕ) : Set ℤ[X] :=
  {f | ∃ h : Irreducible (f.map φℚ),
    f ∈ Box n H ∧ Squarefull (fieldDiscExp f h) ∧
      concDDZ n (upperCoeffs n f) ≠ 0 ∧ H < largePart (fieldDiscExp f h) B}

/-- **Region membership.**  For a monic irreducible box polynomial `f`
(degree `n ≥ 3`) with squarefull `D_f`, `DD(u_f) ≠ 0`, and large-prime part
`A = largePart (fieldDisc f) B > H`: every prime `p | A` satisfies
`B ≤ p`, divides `D_f` (hence `Disc(f)`), and exceeds `n` (from `n < B`), so
the `CaseIIIField` chain puts `f` in the arithmetic subcase-(ii) set
`CaseIIIArithSet B n H`. -/
theorem mem_arith_of_largePart (n H B : ℕ) (hn : 3 ≤ n) (hB : n < B) (f : ℤ[X])
    [Fact (Irreducible (f.map φℚ))] (hfbox : f ∈ Box n H)
    (hsq : Squarefull (fieldDisc f))
    (hdd : concDDZ n (upperCoeffs n f) ≠ 0)
    (hA : H < largePart (fieldDisc f) B) :
    f ∈ CaseIIIArithSet B n H := by
  classical
  have hD0 : fieldDisc f ≠ 0 := by
    unfold fieldDisc
    exact Int.natAbs_ne_zero.mpr (NumberField.discr_ne_zero (Kpoly f))
  have hsqA : Squarefree (largePart (fieldDisc f) B) := squarefree_largePart (fieldDisc f) B
  have hBp : ∀ p ∈ (largePart (fieldDisc f) B).primeFactors, B ≤ p := fun p hp =>
    le_of_mem_largePart_primeFactors (D := fieldDisc f) (B := B) (p := p) hp
  have hpD : ∀ p ∈ (largePart (fieldDisc f) B).primeFactors, p ∣ fieldDisc f := fun p hp =>
    prime_dvd_of_mem_largePart_primeFactors (D := fieldDisc f) (B := B) hD0 hp
  have hpgt : ∀ p ∈ (largePart (fieldDisc f) B).primeFactors, n < p := fun p hp =>
    lt_of_lt_of_le hB (hBp p hp)
  exact mem_caseIIIArithSet_of_field n H B hn f hfbox hsq hdd
    (A := largePart (fieldDisc f) B) hA hsqA hBp hpD hpgt

/-- The region lies in the arithmetic subcase-(ii) set. -/
theorem CaseIIISubcase2_subset_arith (n H B : ℕ) (hn : 3 ≤ n) (hB : n < B) :
    CaseIIISubcase2 n H B ⊆ CaseIIIArithSet B n H := by
  intro f hf
  rcases hf with ⟨h, hbox, hsq, hdd, hA⟩
  haveI : Fact (Irreducible (f.map φℚ)) := ⟨h⟩
  simpa [fieldDiscExp] using
    (mem_arith_of_largePart n H B hn hB f hbox hsq hdd hA)

/-- Region members lie in the box, so the region is finite. -/
lemma CaseIIISubcase2_finite (n H B : ℕ) : (CaseIIISubcase2 n H B).Finite := by
  apply (box_finite n H).subset
  intro f hf
  rcases hf with ⟨h, hbox, hsq, hdd, hA⟩
  exact hbox

/-- The region count is at most the arithmetic count of
`caseIII_subcase2_box_ncard_le` / `caseIII_subcase2_threshold_le`. -/
theorem CaseIIISubcase2_ncard_le_arith (n H B : ℕ) (hn : 3 ≤ n) (hB : n < B) :
    (CaseIIISubcase2 n H B).ncard ≤ (CaseIIIArithSet B n H).ncard := by
  classical
  have hfinA : (CaseIIIArithSet B n H).Finite := by
    apply (box_finite n H).subset
    intro f hf
    exact hf.1
  exact Set.ncard_le_ncard (CaseIIISubcase2_subset_arith n H B hn hB) hfinA

/-- **Case-III subcase (ii), region count: `O(H^(n-1))`.**  For any
threshold family `Bfun : ℕ → ℕ` eventually satisfying `n < Bfun H` and
`H ≤ (Bfun H)^M` (i.e. `Bfun H ≥ H^(1/M)`), the squarefull-`D_f`
subcase-(ii) region count is eventually `O(H^(n-1))` — via the inclusion into
`CaseIIIArithSet (Bfun H) n H` and the uniform threshold bound of
`CaseIIIWrapper`.  (Choosing `Bfun H := ⌈H^(δ/2)⌉`, `M := 4n`, for the
paper's `δ = 1/(2n)`, is the remaining region-design step.) -/
theorem CaseIIISubcase2_isBigO_of_threshold (n M : ℕ) (hn : 3 ≤ n)
    (Bfun : ℕ → ℕ)
    (hthr : ∀ᶠ H : ℕ in atTop, n < Bfun H ∧ H ≤ (Bfun H) ^ M) :
    (fun H : ℕ => ((CaseIIISubcase2 n H (Bfun H)).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) := by
  classical
  have hle : ∀ᶠ H : ℕ in atTop,
      (CaseIIISubcase2 n H (Bfun H)).ncard ≤ (CaseIIIArithSet (Bfun H) n H).ncard := by
    filter_upwards [hthr] with H hthr
    exact CaseIIISubcase2_ncard_le_arith n H (Bfun H) hn hthr.1
  have hmain : (fun H : ℕ => ((CaseIIISubcase2 n H (Bfun H)).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((CaseIIIArithSet (Bfun H) n H).ncard : ℝ)) :=
    Commons.Analysis.Asymptotics.isBigO_of_eventually_le
      (fun H : ℕ => (CaseIIISubcase2 n H (Bfun H)).ncard)
      (fun H : ℕ => (CaseIIIArithSet (Bfun H) n H).ncard) hle
  exact hmain.trans (caseIII_subcase2_isBigO_of_threshold n M hn Bfun hthr)

end Region


section Ramified

/-- The ramified-prime product `C_f` (= `radical D_f`, by
`ramified_iff_prime_dvd_fieldDisc`) has the same prime factors as `D_f`, so
the large-prime part is the same whether computed from `C_f` or from `D_f`
— matching the paper's definition `A := ∏_{p | C, p ≥ B} p`. -/
lemma ramifiedProduct_largePart_eq (f : ℤ[X]) [Fact (Irreducible (f.map φℚ))]
    (B : ℕ) : largePart (ramifiedProduct f) B = largePart (fieldDisc f) B := by
  unfold largePart ramifiedProduct radical
  rw [Nat.primeFactors_prod_primeFactors]

/-- Primes of `C_f` at least `B` and primes of `D_f` at least `B` give the
same membership condition (the `largePart` over `C_f` primes). -/
lemma mem_largePart_ramifiedProduct_primeFactors_iff (f : ℤ[X])
    [Fact (Irreducible (f.map φℚ))] (B p : ℕ) :
    p ∈ (largePart (ramifiedProduct f) B).primeFactors ↔ p ∈ (largePart (fieldDisc f) B).primeFactors := by
  rw [ramifiedProduct_largePart_eq]

end Ramified

end Submission.Vdw

