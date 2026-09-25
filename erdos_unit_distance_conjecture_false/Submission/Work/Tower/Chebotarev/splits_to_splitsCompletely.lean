import Mathlib
import Submission.Work.Tower.Chebotarev.Defs
import Submission.Work.Defs.Basic

/-!
# From the `normalizedFactors` formulation of complete splitting to the explicit one

`Work.Tower.Splits q L` packages complete splitting of the rational prime `q` in the number
field `L` through the data of the prime ideals in `normalizedFactors (q 𝓞 L)`: each of them is
unramified with residue field `𝔽_q`, and there are `[L : ℚ]` of them.

`Work.Defs.SplitsCompletely q L` is the equivalent explicit statement: there is an enumeration
`𝔮 : Fin [L : ℚ] → Ideal (𝓞 L)` of pairwise incomparable primes containing `q`, with residue
field `𝔽_q`, whose product is `q 𝓞 L`.

This file bridges the two.  The mathematical content is:

* the residue-field condition forces `q` to be a **prime** (`𝓞 L ⧸ P` is a field of
  characteristic `q`);
* the prime below any prime above `q` is then the ideal `q ℤ`, so the ramification index
  hypothesis `e = 1` (which is an equality of *localised* invariants) says exactly that each
  prime occurs with multiplicity one in the factorisation of `q 𝓞 L`;
* hence `normalizedFactors (q 𝓞 L)` is a set of `[L : ℚ]` distinct primes whose product is
  `q 𝓞 L`, and enumerating it gives the explicit factorisation.

-/

set_option linter.style.haveILetI false

namespace Work.Tower.Chebotarev

open NumberField Ideal Polynomial UniqueFactorizationMonoid
open scoped Classical nonZeroDivisors NumberField

/-- **The rational prime is prime.**  The hypothesis that the residue field of a prime ideal
above `q` is `𝔽_q` forces `q` to be a prime: the residue field `𝓞 L ⧸ P` is a field, and the
ring isomorphism `𝓞 L ⧸ P ≃+* ZMod q` makes `q` its characteristic. -/
lemma splits_prime {L : Type} [Field L] [NumberField L] {q : ℕ}
    (h : Work.Tower.Splits q L) : q.Prime := by
  have hqpos : 0 < q := h.1
  have hI_ne_bot : Ideal.span {(q : 𝓞 L)} ≠ ⊥ :=
    Ideal.span_singleton_eq_bot.not.mpr (by exact_mod_cast hqpos.ne')
  have hpos : 0 < (normalizedFactors (Ideal.span {(q : 𝓞 L)})).toFinset.card := by
    rw [h.2.2.2]; exact Module.finrank_pos
  obtain ⟨P, hP⟩ := Finset.card_pos.mp hpos
  have hPM : P ∈ normalizedFactors (Ideal.span {(q : 𝓞 L)}) := Multiset.mem_toFinset.mp hP
  have hPprime : P.IsPrime := Ideal.isPrime_of_prime (prime_of_normalized_factor P hPM)
  have hIP : Ideal.span {(q : 𝓞 L)} ≤ P := ((Ideal.mem_normalizedFactors_iff hI_ne_bot).mp hPM).2
  have hPne : P ≠ ⊥ := fun hbot => hI_ne_bot (le_bot_iff.mp (hbot ▸ hIP))
  haveI : P.IsMaximal := hPprime.isMaximal hPne
  haveI : Field (𝓞 L ⧸ P) := Ideal.Quotient.field P
  obtain ⟨e⟩ := h.2.2.1 P hPM
  haveI : IsDomain (ZMod q) := MulEquiv.isDomain (𝓞 L ⧸ P) e.symm.toMulEquiv
  rcases CharP.char_is_prime_or_zero (ZMod q) q with hq | hq
  · exact hq
  · exact absurd hq hqpos.ne'

/-- **Multiplicity one.**  Let `P` be a prime above `q` with `P.ramificationIdx ℤ = 1` (the
localised unramifiedness condition).  Since the prime of `ℤ` below `P` is `q ℤ`, this says
exactly that `P` occurs with multiplicity one in `normalizedFactors (q 𝓞 L)`; equivalently
`q 𝓞 L` is the squarefree product of the primes above it. -/
lemma count_normalizedFactors_span_eq_one {L : Type} [Field L] [NumberField L] {q : ℕ}
    (hq : q.Prime) {P : Ideal (𝓞 L)} (hP : P.IsPrime) (hP0 : P ≠ ⊥)
    (hPq : (q : 𝓞 L) ∈ P) (hram : P.ramificationIdx ℤ = 1) :
    (normalizedFactors (Ideal.span {(q : 𝓞 L)})).count P = 1 := by
  -- the prime of `ℤ` below `P` is `q ℤ`
  have hne : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne_zero
  have hprimeZ : (Ideal.span {(q : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime hne).mpr (Nat.prime_iff_prime_int.mp hq)
  have hmaxZ : (Ideal.span {(q : ℤ)}).IsMaximal :=
    hprimeZ.isMaximal (Ideal.span_singleton_eq_bot.not.mpr hne)
  have hleZ : Ideal.span {(q : ℤ)} ≤ P.under ℤ := by
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_under]; simpa using hPq
  have hne0 : P.under ℤ ≠ ⊥ := by
    intro hbot; rw [hbot] at hleZ
    exact (Ideal.span_singleton_eq_bot.not.mpr hne) (le_bot_iff.mp hleZ)
  haveI : (P.under ℤ).IsPrime := hP.under ℤ
  have hJmax : (P.under ℤ).IsMaximal := (hP.under ℤ).isMaximal hne0
  have hunder : P.under ℤ = Ideal.span {(q : ℤ)} :=
    (IsMaximal.eq_of_le hmaxZ hJmax.ne_top hleZ).symm
  have hmap_ne : (P.under ℤ).map (algebraMap ℤ (𝓞 L)) ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot hne0
  have hmap_eq : (P.under ℤ).map (algebraMap ℤ (𝓞 L)) = Ideal.span {(q : 𝓞 L)} := by
    rw [hunder, Ideal.map_span, Set.image_singleton,
      show (algebraMap ℤ (𝓞 L)) (q : ℤ) = (q : 𝓞 L) by simp]
  -- the localised ramification index is the multiplicity in `normalizedFactors`
  haveI := hP
  calc (normalizedFactors (Ideal.span {(q : 𝓞 L)})).count P
      = (normalizedFactors ((P.under ℤ).map (algebraMap ℤ (𝓞 L)))).count P := by rw [hmap_eq]
    _ = (P.under ℤ).ramificationIdx' P :=
        (Ideal.IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count hmap_ne hP hP0).symm
    _ = P.ramificationIdx ℤ := Ideal.ramificationIdx'_eq_ramificationIdx' (P.under ℤ) P hmap_ne
    _ = 1 := hram

/-- A completely split prime in the `normalizedFactors` formulation gives the explicit
factorisation of `q 𝓞 L` into `[L : ℚ]` pairwise incomparable primes with residue field `𝔽_q`. -/
theorem splits_to_splitsCompletely {L : Type} [Field L] [NumberField L] {q : ℕ}
    (h : Work.Tower.Splits q L) : Work.Defs.SplitsCompletely q L := by
  classical
  have hqprime : q.Prime := splits_prime h
  obtain ⟨hqpos, hram, hres, hcard⟩ := h
  unfold Work.Defs.SplitsCompletely
  set I : Ideal (𝓞 L) := Ideal.span {(q : 𝓞 L)} with hIdef
  have hI_ne_bot : I ≠ ⊥ := by
    rw [hIdef]; exact Ideal.span_singleton_eq_bot.not.mpr (by exact_mod_cast hqpos.ne')
  set M : Multiset (Ideal (𝓞 L)) := normalizedFactors I with hMdef
  set s : Finset (Ideal (𝓞 L)) := M.toFinset with hsdef
  -- every prime above `q` occurs with multiplicity one
  have hcount : ∀ P ∈ s, M.count P = 1 := by
    intro P hPs
    have hPM : P ∈ M := Multiset.mem_toFinset.mp hPs
    have hPprime : P.IsPrime := Ideal.isPrime_of_prime (prime_of_normalized_factor P hPM)
    have hIP : I ≤ P := ((Ideal.mem_normalizedFactors_iff hI_ne_bot).mp hPM).2
    have hPne : P ≠ ⊥ := fun hbot => hI_ne_bot (le_bot_iff.mp (hbot ▸ hIP))
    have hPq : (q : 𝓞 L) ∈ P := hIP (Ideal.mem_span_singleton_self _)
    exact count_normalizedFactors_span_eq_one hqprime hPprime hPne hPq
      (hram P (by simpa [hMdef, hIdef] using hPM)).1
  -- hence `q 𝓞 L` is the product of the (distinct) primes above it
  have hprod : I = ∏ P ∈ s, P := by
    rw [← Ideal.prod_normalizedFactors_eq_self hI_ne_bot]
    rw [← hMdef, Finset.prod_multiset_count]
    exact Finset.prod_congr rfl (fun P hP => by rw [hcount P hP, pow_one])
  have hscard : s.card = Module.finrank ℚ L := hcard
  let e : s ≃ Fin (Module.finrank ℚ L) := Finset.equivFinOfCardEq hscard
  refine ⟨fun i => (e.symm i : Ideal (𝓞 L)), ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact Ideal.isPrime_of_prime
      (prime_of_normalized_factor _ (Multiset.mem_toFinset.mp (e.symm i).2))
  · intro i
    have hmem : (e.symm i : Ideal (𝓞 L)) ∈ M := Multiset.mem_toFinset.mp (e.symm i).2
    have hIP : I ≤ (e.symm i : Ideal (𝓞 L)) :=
      ((Ideal.mem_normalizedFactors_iff hI_ne_bot).mp hmem).2
    exact hIP (Ideal.mem_span_singleton_self _)
  · intro i
    exact hres _ (Multiset.mem_toFinset.mp (e.symm i).2)
  · intro i j hij hle
    apply hij
    have hmi : (e.symm i : Ideal (𝓞 L)) ∈ M := Multiset.mem_toFinset.mp (e.symm i).2
    have hmj : (e.symm j : Ideal (𝓞 L)) ∈ M := Multiset.mem_toFinset.mp (e.symm j).2
    have hi : (e.symm i : Ideal (𝓞 L)).IsPrime :=
      Ideal.isPrime_of_prime (prime_of_normalized_factor _ hmi)
    have hj : (e.symm j : Ideal (𝓞 L)).IsPrime :=
      Ideal.isPrime_of_prime (prime_of_normalized_factor _ hmj)
    have hine : (e.symm i : Ideal (𝓞 L)) ≠ ⊥ := fun hbot =>
      hI_ne_bot (le_bot_iff.mp (hbot ▸ ((Ideal.mem_normalizedFactors_iff hI_ne_bot).mp hmi).2))
    have heq : (e.symm i : Ideal (𝓞 L)) = (e.symm j : Ideal (𝓞 L)) :=
      IsMaximal.eq_of_le (hi.isMaximal hine) hj.ne_top hle
    have hsub : e.symm i = e.symm j := Subtype.ext heq
    simpa using congrArg e hsub
  · calc Ideal.span {(q : 𝓞 L)} = I := hIdef.symm
      _ = ∏ P ∈ s, P := hprod
      _ = ∏ i : Fin (Module.finrank ℚ L), (e.symm i : Ideal (𝓞 L)) := by
            rw [← Finset.prod_coe_sort s (fun x : Ideal (𝓞 L) => x)]
            exact (Equiv.prod_comp e.symm (fun x : s => (x : Ideal (𝓞 L)))).symm

end Work.Tower.Chebotarev
