import Mathlib
import Submission.Work.BW.DefsMult
import Submission.Work.BW.RB.A4
import Submission.Work.BW.RB.srel_cut_prime
import Submission.Work.BW.rayDeg_additive
import Submission.Work.BW.rayDeg_hyperplane
import Submission.Work.BW.RB.primLen_sup_span_le_sum_loc

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW.RB

open Work.BW
open Classical

noncomputable section

set_option linter.style.haveILetI false

/-! ## Auxiliary algebra -/

/-- Minimal primes are monotone for the *reverse* order on ideals: if `J ≤ I ≤ q` and `q` is
minimal over `J`, then `q` is minimal over `I`. -/
theorem minimalPrimes_of_le {R : Type*} [CommRing R] {J I : Ideal R} (hJI : J ≤ I)
    {q : Ideal R} (hq : q ∈ J.minimalPrimes) (hIq : I ≤ q) : q ∈ I.minimalPrimes :=
  ⟨⟨hq.1.1, hIq⟩, fun r hr hrq => hq.2 ⟨hr.1, hJI.trans hr.2⟩ hrq⟩

/-- `Srel` vanishes at an ideal all of whose prime overideals are inadmissible. -/
lemma srel_eq_zero_of_no_adm {N : ℕ} (D : Fin (N + 1) →₀ ℕ) (L : Ideal (MR N))
    (hnone : ∀ q ∈ L.minimalPrimes, ¬ OnGPrime N q) : Srel N D L = 0 := by
  classical
  rw [Srel]
  refine (finsum_cond_eq_sum
    (fun q : Ideal (MR N) => q ∈ L.minimalPrimes ∧ OnGPrime N q)
    (∅ : Finset (Ideal (MR N))) ?_
    (fun q => ((primLen L q).toNat : ℚ) * rayDeg N D q)).trans Finset.sum_empty
  intro a ha
  exact absurd ha.2 (hnone a ha.1)

/-- `Srel` of the cut of an inadmissible prime vanishes. -/
lemma srel_sup_span_eq_zero_of_not_adm {N : ℕ} (D : Fin (N + 1) →₀ ℕ) (r : Ideal (MR N))
    (_hr : r.IsPrime) (hnot : ¬ OnGPrime N r) (P : MR N) :
    Srel N D (r ⊔ Ideal.span {P}) = 0 := by
  refine srel_eq_zero_of_no_adm D _ fun q hq hqadm => hnot ?_
  exact OnGPrime_anti (le_sup_left.trans hq.le) hqadm

/-- Adding an element already in a prime does not change `Srel`. -/
lemma srel_sup_span_eq_self_of_mem {N : ℕ} (D : Fin (N + 1) →₀ ℕ) (r : Ideal (MR N))
    (hr : r.IsPrime) (P : MR N) (hP : P ∈ r) : Srel N D (r ⊔ Ideal.span {P}) = Srel N D r := by
  rw [sup_eq_left.mpr (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hP))]

/-- **The per-parent bound.**  For a minimal prime `p` of a multihomogeneous ideal and a
multihomogeneous element `P` of multidegree `D`, cutting the prime `p` by `P` does not increase
`Srel` beyond `rayDeg p`. -/
theorem srel_sup_span_le_rayDeg {N : ℕ} (D : Fin (N + 1) →₀ ℕ) (hD : ∀ i, 1 ≤ D i)
    (J : Ideal (MR N)) (hJmh : MultiHom N J) (P : MR N) (hPmh : P ∈ homPiece N D)
    (p : Ideal (MR N)) (hp : p ∈ J.minimalPrimes) :
    Srel N D (p ⊔ Ideal.span {P}) ≤ rayDeg N D p := by
  by_cases hadm : OnGPrime N p
  · by_cases hPp : P ∈ p
    · rw [srel_sup_span_eq_self_of_mem D p hp.isPrime P hPp, srel_self_of_isPrime D p hp.isPrime hadm]
    · calc Srel N D (p ⊔ Ideal.span {P}) ≤ Srel N D p :=
            srel_cut_prime D hD p hp.isPrime (multiHom_minimalPrimes J hJmh p hp) P hPmh hPp hadm
        _ = rayDeg N D p := srel_self_of_isPrime D p hp.isPrime hadm
  · rw [srel_sup_span_eq_zero_of_not_adm D p hp.isPrime hadm P]
    exact rayDeg_nonneg D p


/-- **The multiplicity inequality for one minimal prime of the cut.**

Let `J` be an ideal of `R = MR N` that is unmixed at the cone points (`hunmixed`: every associated
prime of `R/J` inside an admissible maximal ideal is a minimal prime of `J`), let `P ∈ R` and let
`q` be an *admissible* minimal prime of `K = J + (P)`.  Then the multiplicity of `K` at `q` is at
most the sum, over the minimal primes `p` of `J` contained in `q`, of the multiplicity of `J` at
`p` times the multiplicity of `p + (P)` at `q`:

  `ℓ_q(K) ≤ ∑_{p ∈ Min J, p ⊆ q} ℓ_p(J) · ℓ_q(p + (P))`.

This is the "no excess" statement that the unmixedness hypothesis buys: the cycle of `K` is the
sum of the cuts of the components of `J`, each component contributing with its own multiplicity.

Route: take a minimal primary decomposition `J = ⨅ i, Q_i` (`Ideal.IsMinimalPrimaryDecomposition`;
the `Q_i` are primary with pairwise distinct radicals, which are exactly `Ass(R/J)`).  Cutting by
`P` and iterating `locLenAt_sup_inf_le` (length additivity across an intersection) gives
`locLenAt q (J + (P)) ≤ ∑ i, locLenAt q (Q_i + (P))`.  For the `i` with `radical Q_i ⊆ q`
(these radicals are minimal primes of `J` by `hunmixed`, applied at an admissible maximal ideal
containing `q`) the primary cut bound `locLenAt_primary_cut_le` gives
`locLenAt q (Q_i + (P)) ≤ locLenAt (radical Q_i) Q_i · locLenAt q (radical Q_i + (P))`, and
`locLenAt (radical Q_i) Q_i = locLenAt (radical Q_i) J = primLen J (radical Q_i)`.  For the
remaining `i` one has `radical Q_i ⊄ q`, hence `Q_i + (P) ⊄ q` and the length vanishes. -/
theorem primLen_sup_span_le_sum {N : ℕ} (J : Ideal (MR N)) (P : MR N)
    (hunmixed : ∀ 𝔪 : Ideal (MR N), 𝔪.IsMaximal → OnGPrime N 𝔪 →
      ∀ p ∈ associatedPrimes (MR N) (MR N ⧸ J), p ≤ 𝔪 → p ∈ J.minimalPrimes)
    (q : Ideal (MR N)) (hq : q ∈ (J ⊔ Ideal.span {P}).minimalPrimes) (hqadm : OnGPrime N q) :
    ((primLen (J ⊔ Ideal.span {P}) q).toNat : ℚ) ≤
      ∑ᶠ (p : Ideal (MR N)) (_ : p ∈ J.minimalPrimes ∧ p ≤ q),
        (((primLen J p).toNat : ℚ) * ((primLen (p ⊔ Ideal.span {P}) q).toNat : ℚ)) := by
  obtain ⟨x, hx, hqx⟩ := hqadm
  have hsurj : Function.Surjective (MvPolynomial.eval x) := fun c =>
    ⟨MvPolynomial.C c, by simp⟩
  have hmax : (ptIdeal N x).IsMaximal := by
    rw [ptIdeal]
    exact RingHom.ker_isMaximal_of_surjective _ hsurj
  exact primLen_sup_span_le_sum_loc J P q hq fun p hp hpq =>
    hunmixed (ptIdeal N x) hmax ⟨x, hx, le_rfl⟩ p hp (le_trans hpq hqx)


/-- A finite sub-sum over minimal primes of `L` (all admissible) is at most `Srel N D L`. -/
lemma finset_sum_le_srel {N : ℕ} (D : Fin (N + 1) →₀ ℕ) (L : Ideal (MR N))
    (S : Finset (Ideal (MR N))) (hsub : ∀ q ∈ S, q ∈ L.minimalPrimes ∧ OnGPrime N q) :
    ∑ q ∈ S, (((primLen L q).toNat : ℚ) * rayDeg N D q) ≤ Srel N D L := by
  classical
  obtain ⟨SL, hSL⟩ : ∃ S : Finset (Ideal (MR N)), ∀ q, q ∈ S ↔ q ∈ L.minimalPrimes :=
    ⟨(Ideal.finite_minimalPrimes_of_isNoetherianRing (MR N) L).toFinset,
      fun q => Set.Finite.mem_toFinset
        (Ideal.finite_minimalPrimes_of_isNoetherianRing (MR N) L)⟩
  have h1 : Srel N D L = ∑ q ∈ SL,
      (if q ∈ L.minimalPrimes ∧ OnGPrime N q then ((primLen L q).toNat : ℚ) * rayDeg N D q
        else 0) :=
    finsum_cond_eq_sum (fun q : Ideal (MR N) => q ∈ L.minimalPrimes ∧ OnGPrime N q) SL
      (fun a ha => (hSL a).mpr ha.1) _
  have h2 : ∑ q ∈ S, (((primLen L q).toNat : ℚ) * rayDeg N D q)
      = ∑ q ∈ S, (if q ∈ L.minimalPrimes ∧ OnGPrime N q then
          ((primLen L q).toNat : ℚ) * rayDeg N D q else 0) :=
    Finset.sum_congr rfl fun q hq => (if_pos (hsub q hq)).symm
  rw [h2, h1]
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun q hq => (hSL q).mpr (hsub q hq).1) ?_
  intro q _ _
  by_cases hc : q ∈ L.minimalPrimes ∧ OnGPrime N q
  · rw [if_pos hc]; exact mul_nonneg (by positivity) (rayDeg_nonneg D q)
  · rw [if_neg hc]

/-- The per-`q` comparison in the bookkeeping for the one-step cut. -/
lemma cut_term_le {N : ℕ} (D : Fin (N + 1) →₀ ℕ) (J : Ideal (MR N)) (P : MR N)
    (hunmixed : ∀ 𝔪 : Ideal (MR N), 𝔪.IsMaximal → OnGPrime N 𝔪 →
      ∀ p ∈ associatedPrimes (MR N) (MR N ⧸ J), p ≤ 𝔪 → p ∈ J.minimalPrimes)
    (q : Ideal (MR N)) (hq : q ∈ (J ⊔ Ideal.span {P}).minimalPrimes) (hqadm : OnGPrime N q) :
    ((primLen (J ⊔ Ideal.span {P}) q).toNat : ℚ) * rayDeg N D q ≤
      (∑ᶠ (p : Ideal (MR N)) (_ : p ∈ J.minimalPrimes ∧ p ≤ q),
        (((primLen J p).toNat : ℚ) * ((primLen (p ⊔ Ideal.span {P}) q).toNat : ℚ)))
        * rayDeg N D q := by
  exact mul_le_mul_of_nonneg_right (primLen_sup_span_le_sum J P hunmixed q hq hqadm)
    (rayDeg_nonneg D q)


/-- The per-`q` comparison with the inner sum converted to a `Finset` sum over `T`. -/
lemma cut_term_le' {N : ℕ} (D : Fin (N + 1) →₀ ℕ) (J : Ideal (MR N)) (P : MR N)
    (hunmixed : ∀ 𝔪 : Ideal (MR N), 𝔪.IsMaximal → OnGPrime N 𝔪 →
      ∀ p ∈ associatedPrimes (MR N) (MR N ⧸ J), p ≤ 𝔪 → p ∈ J.minimalPrimes)
    (T : Finset (Ideal (MR N))) (hT : ∀ p, p ∈ T ↔ p ∈ J.minimalPrimes)
    (q : Ideal (MR N)) (hq : q ∈ (J ⊔ Ideal.span {P}).minimalPrimes) (hqadm : OnGPrime N q) :
    ((primLen (J ⊔ Ideal.span {P}) q).toNat : ℚ) * rayDeg N D q ≤
      (∑ p ∈ T, (if p ≤ q then
          (((primLen J p).toNat : ℚ) * ((primLen (p ⊔ Ideal.span {P}) q).toNat : ℚ))
        else 0)) * rayDeg N D q := by
  classical
  refine mul_le_mul_of_nonneg_right ?_ (rayDeg_nonneg D q)
  refine le_trans (primLen_sup_span_le_sum J P hunmixed q hq hqadm) (le_of_eq ?_)
  rw [finsum_cond_eq_sum (fun p : Ideal (MR N) => p ∈ J.minimalPrimes ∧ p ≤ q) T
    (fun a ha => (hT a).mpr ha.1)]
  refine Finset.sum_congr rfl fun p hpT => ?_
  by_cases hpq : p ≤ q
  · rw [if_pos ⟨(hT p).mp hpT, hpq⟩, if_pos hpq]
  · rw [if_neg (fun h => hpq h.2), if_neg hpq]

/-- For a minimal prime `p` of `J` and a minimal prime `q` of `J ⊔ (P)` above `p`, the prime `q`
is minimal over `p ⊔ (P)`. -/
lemma mem_minimalPrimes_sup_span_of_le {N : ℕ} (J : Ideal (MR N)) (P : MR N)
    (p : Ideal (MR N)) (hp : p ∈ J.minimalPrimes) (q : Ideal (MR N))
    (hqK : q ∈ (J ⊔ Ideal.span {P}).minimalPrimes) (hpq : p ≤ q) :
    q ∈ (p ⊔ Ideal.span {P}).minimalPrimes := by
  classical
  refine minimalPrimes_of_le (J := J ⊔ Ideal.span {P}) (I := p ⊔ Ideal.span {P}) ?_ hqK ?_
  · exact sup_le_sup hp.1.2 le_rfl
  · refine sup_le hpq ?_
    exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (hqK.le (Ideal.mem_sup_right
      (Ideal.mem_span_singleton_self P))))


/-- **The one-step cut, for `J` unmixed at the cone points.**

For an ideal `J` of `R = MR N` that is generated by multihomogeneous elements and is unmixed at the
cone points (`hunmixed`), an ideal `I ⊇ J` generated by elements of multidegree `D`, and an element
`P ∈ I` of multidegree `D` that lies in no minimal prime `p` of `J` with `I ≰ p`, adding `P` to `J`
does not increase `Srel`:

  `Srel N D (J ⊔ (P)) ≤ Srel N D J`.

The proof splits the minimal primes of `J` by whether they contain `I`; the cut multiplicity of
`J ⊔ (P)` at each admissible minimal prime is bounded by the sum of the cut multiplicities of the
components (`primLen_sup_span_le_sum`), and each component `p` contributes at most its own
`rayDeg p` (`srel_cut_prime` for `P ∉ p`, trivial for `P ∈ p`). -/
theorem srel_cut_unmixed {N : ℕ} (D : Fin (N + 1) →₀ ℕ) (hD : ∀ i, 1 ≤ D i)
    (I J : Ideal (MR N)) (hIgen : ∃ s : Set (MR N), (∀ P ∈ s, P ∈ homPiece N D) ∧ I = Ideal.span s)
    (hJI : J ≤ I) (hJmh : MultiHom N J)
    (hunmixed : ∀ 𝔪 : Ideal (MR N), 𝔪.IsMaximal → OnGPrime N 𝔪 →
      ∀ p ∈ associatedPrimes (MR N) (MR N ⧸ J), p ≤ 𝔪 → p ∈ J.minimalPrimes)
    (P : MR N) (hP : P ∈ homPiece N D) (hPI : P ∈ I)
    (hav : ∀ p ∈ J.minimalPrimes, ¬ I ≤ p → P ∉ p) :
    Srel N D (J ⊔ Ideal.span {P}) ≤ Srel N D J := by
  classical
  set K : Ideal (MR N) := J ⊔ Ideal.span {P} with hKdef
  obtain ⟨SK, hSK⟩ : ∃ S : Finset (Ideal (MR N)), ∀ q, q ∈ S ↔ q ∈ K.minimalPrimes :=
    ⟨(Ideal.finite_minimalPrimes_of_isNoetherianRing (MR N) K).toFinset,
      fun q => Set.Finite.mem_toFinset (Ideal.finite_minimalPrimes_of_isNoetherianRing (MR N) K)⟩
  obtain ⟨T, hT⟩ : ∃ S : Finset (Ideal (MR N)), ∀ q, q ∈ S ↔ q ∈ J.minimalPrimes :=
    ⟨(Ideal.finite_minimalPrimes_of_isNoetherianRing (MR N) J).toFinset,
      fun q => Set.Finite.mem_toFinset (Ideal.finite_minimalPrimes_of_isNoetherianRing (MR N) J)⟩
  have hL : Srel N D K = ∑ q ∈ SK,
      (if OnGPrime N q then ((primLen K q).toNat : ℚ) * rayDeg N D q else 0) := by
    rw [Srel]
    rw [finsum_cond_eq_sum (fun q : Ideal (MR N) => q ∈ K.minimalPrimes ∧ OnGPrime N q) SK
      (fun a ha => (hSK a).mpr ha.1)]
    refine Finset.sum_congr rfl fun q hq => ?_
    by_cases h2 : OnGPrime N q
    · rw [if_pos ⟨(hSK q).mp hq, h2⟩, if_pos h2]
    · rw [if_neg (fun h => h2 h.2), if_neg h2]
  have hR : Srel N D J = ∑ p ∈ T,
      (if OnGPrime N p then ((primLen J p).toNat : ℚ) * rayDeg N D p else 0) := by
    rw [Srel]
    rw [finsum_cond_eq_sum (fun p : Ideal (MR N) => p ∈ J.minimalPrimes ∧ OnGPrime N p) T
      (fun a ha => (hT a).mpr ha.1)]
    refine Finset.sum_congr rfl fun p hp => ?_
    by_cases h2 : OnGPrime N p
    · rw [if_pos ⟨(hT p).mp hp, h2⟩, if_pos h2]
    · rw [if_neg (fun h => h2 h.2), if_neg h2]
  rw [hL, hR]
  calc ∑ q ∈ SK, (if OnGPrime N q then ((primLen K q).toNat : ℚ) * rayDeg N D q else 0)
      ≤ ∑ q ∈ SK, (if OnGPrime N q then
          (∑ p ∈ T, (if p ≤ q then (((primLen J p).toNat : ℚ) *
            ((primLen (p ⊔ Ideal.span {P}) q).toNat : ℚ)) else 0)) * rayDeg N D q
          else 0) := by
        refine Finset.sum_le_sum fun q hq => ?_
        by_cases hqa : OnGPrime N q
        · rw [if_pos hqa, if_pos hqa]
          exact cut_term_le' D J P hunmixed T hT q ((hSK q).mp hq) hqa
        · rw [if_neg hqa, if_neg hqa]
    _ = ∑ p ∈ T, (∑ q ∈ SK, (if OnGPrime N q ∧ p ≤ q then (((primLen J p).toNat : ℚ) *
          ((primLen (p ⊔ Ideal.span {P}) q).toNat : ℚ)) * rayDeg N D q else 0)) := by
        have h1 : (∑ q ∈ SK, (if OnGPrime N q then
              (∑ p ∈ T, (if p ≤ q then (((primLen J p).toNat : ℚ) *
                ((primLen (p ⊔ Ideal.span {P}) q).toNat : ℚ)) else 0)) * rayDeg N D q else 0))
            = ∑ q ∈ SK, ∑ p ∈ T, (if OnGPrime N q then
                ((if p ≤ q then (((primLen J p).toNat : ℚ) *
                  ((primLen (p ⊔ Ideal.span {P}) q).toNat : ℚ)) else 0) * rayDeg N D q) else 0) := by
          refine Finset.sum_congr rfl fun q _ => ?_
          by_cases hq : OnGPrime N q
          · rw [if_pos hq, Finset.sum_mul]
            refine Finset.sum_congr rfl fun p _ => by rw [if_pos hq]
          · rw [if_neg hq, Finset.sum_eq_zero]
            intro p _
            rw [if_neg hq]
        rw [h1, Finset.sum_comm]
        refine Finset.sum_congr rfl fun p _ => ?_
        refine Finset.sum_congr rfl fun q _ => ?_
        by_cases hq : OnGPrime N q
        · by_cases hpq : p ≤ q
          · rw [if_pos hq, if_pos hpq, if_pos ⟨hq, hpq⟩]
          · rw [if_pos hq, if_neg hpq, if_neg (fun h => hpq h.2), zero_mul]
        · rw [if_neg hq, if_neg (fun h => hq h.1)]
    _ ≤ ∑ p ∈ T, (((primLen J p).toNat : ℚ) * Srel N D (p ⊔ Ideal.span {P})) := by
        refine Finset.sum_le_sum fun p hpT => ?_
        have hpMin : p ∈ J.minimalPrimes := (hT p).mp hpT
        have hsum_eq : (∑ q ∈ SK, (if OnGPrime N q ∧ p ≤ q then (((primLen J p).toNat : ℚ) *
              ((primLen (p ⊔ Ideal.span {P}) q).toNat : ℚ)) * rayDeg N D q else 0))
            = ((primLen J p).toNat : ℚ) * ∑ q ∈ SK.filter (fun q => OnGPrime N q ∧ p ≤ q),
                (((primLen (p ⊔ Ideal.span {P}) q).toNat : ℚ) * rayDeg N D q) := by
          rw [Finset.mul_sum, Finset.sum_filter]
          refine Finset.sum_congr rfl fun q _ => ?_
          by_cases hc : OnGPrime N q ∧ p ≤ q
          · rw [if_pos hc, if_pos hc]; ring
          · rw [if_neg hc, if_neg hc]
        rw [hsum_eq]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine finset_sum_le_srel D (p ⊔ Ideal.span {P}) _ ?_
        intro q hq
        rw [Finset.mem_filter] at hq
        exact ⟨mem_minimalPrimes_sup_span_of_le J P p hpMin q ((hSK q).mp hq.1) hq.2.2, hq.2.1⟩
    _ ≤ ∑ p ∈ T, (if OnGPrime N p then ((primLen J p).toNat : ℚ) * rayDeg N D p else 0) := by
        refine Finset.sum_le_sum fun p hpT => ?_
        have hpMin : p ∈ J.minimalPrimes := (hT p).mp hpT
        by_cases hpa : OnGPrime N p
        · rw [if_pos hpa]
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact srel_sup_span_le_rayDeg D hD J hJmh P hP p hpMin
        · rw [if_neg hpa, srel_sup_span_eq_zero_of_not_adm D p hpMin.isPrime hpa P, mul_zero]

end

end Work.BW.RB
