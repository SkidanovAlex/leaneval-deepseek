import Mathlib
import Submission.Work.BW.BWGradedBase

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- **`q` is minimal over `p + (r)` for any `r ∈ q \ p`.** Let `R` be Noetherian, `p` a prime, `Q` a
`p`-primary ideal, `P ∉ p`, and `q` a minimal prime of `Q + (P)`. Then for every `r ∉ p` with
`r ∈ q` one has `q ∈ (p ⊔ Ideal.span {r}).minimalPrimes`.

Route: `q` is a minimal prime of `Q + (P)`, hence of the larger ideal `p + (P)`, and the prime
`q' := q/p` of `D := R/p` is minimal over `P`, so it has height `1` (Krull's principal ideal result
gives `≤ 1`, and `P ≠ 0` in the domain `D` gives `≥ 1`). Hence the localisation `A := (R/p)_{q'}` is a
one-dimensional local domain, whose only primes are `(0)` and its maximal ideal `𝔫 = q'A`. For
`r ∉ p`, the image `r̄` of `r` in `A` is nonzero (and lies in `q'A` when `r ∈ q`), so `(r̄) ≠ 0` and any
prime containing `(r̄)` is `𝔫`; hence `q'` is the only prime of `D` between `(r)` and `q'`, i.e.
`q ∈ (p ⊔ Ideal.span {r}).minimalPrimes`. -/
theorem cut_minimalPrimes {R : Type*} [CommRing R] [IsNoetherianRing R]
    (p Q : Ideal R) (hp : p.IsPrime) (hQ : Q.IsPrimary) (hrad : Q.radical = p)
    (P : R) (hPp : P ∉ p) (q : Ideal R) (hq : q ∈ (Q ⊔ Ideal.span {P}).minimalPrimes)
    (r : R) (hrp : r ∉ p) (hrq : r ∈ q) :
    q ∈ (p ⊔ Ideal.span {r}).minimalPrimes := by
  haveI : p.IsPrime := hp
  have hqprime : q.IsPrime := hq.isPrime
  haveI : q.IsPrime := hqprime
  -- `Q ≤ p` and `p ≤ q`
  have hQp : Q ≤ p := by rw [← hrad]; exact Ideal.le_radical
  have hQq : Q ≤ q := le_trans le_sup_left hq.le
  have hpQ : p ≤ q := by
    rw [← hrad]
    exact hqprime.radical_le_iff.mpr hQq
  -- the radicals of `Q ⊔ (P)` and `p ⊔ (P)` coincide
  have hp_le_rad : p ≤ (Q ⊔ Ideal.span {P}).radical := by
    rw [← hrad]; exact Ideal.radical_mono le_sup_left
  have hsp_le_rad : Ideal.span {P} ≤ (Q ⊔ Ideal.span {P}).radical :=
    le_trans le_sup_right Ideal.le_radical
  have hQsp : Q ⊔ Ideal.span {P} ≤ p ⊔ Ideal.span {P} :=
    sup_le (le_trans hQp le_sup_left) le_sup_right
  have hrad_eq : (Q ⊔ Ideal.span {P}).radical = (p ⊔ Ideal.span {P}).radical := by
    refine le_antisymm (Ideal.radical_mono hQsp) ?_
    rw [← Ideal.radical_idem (Q ⊔ Ideal.span {P})]
    exact Ideal.radical_mono (sup_le hp_le_rad hsp_le_rad)
  have hqrad : q ∈ (p ⊔ Ideal.span {P}).minimalPrimes := by
    have hset : (p ⊔ Ideal.span {P}).minimalPrimes = (Q ⊔ Ideal.span {P}).minimalPrimes := by
      rw [← Ideal.radical_minimalPrimes (I := p ⊔ Ideal.span {P}),
        ← Ideal.radical_minimalPrimes (I := Q ⊔ Ideal.span {P}), hrad_eq]
    rwa [hset]
  -- pass to the quotient `D = R ⧸ p`
  have hQmap : Q.map (Ideal.Quotient.mk p) = ⊥ := by
    rw [Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
    exact hQp
  have hmapI : (Q ⊔ Ideal.span {P}).map (Ideal.Quotient.mk p)
      = Ideal.span {(Ideal.Quotient.mk p) P} := by
    rw [Ideal.map_sup, hQmap, bot_sup_eq, Ideal.map_span, Set.image_singleton]
  have hmap_eq : ((Q ⊔ Ideal.span {P}) ⊔ RingHom.ker (Ideal.Quotient.mk p))
      = p ⊔ Ideal.span {P} := by
    rw [Ideal.mk_ker]
    exact le_antisymm (sup_le hQsp le_sup_left)
      (sup_le le_sup_right (le_trans le_sup_right le_sup_left))
  -- `q' = q/p` is a minimal prime of `(P')` in the domain `D`
  have hq' : q.map (Ideal.Quotient.mk p)
      ∈ (Ideal.span {(Ideal.Quotient.mk p) P}).minimalPrimes := by
    rw [← hmapI, Ideal.minimalPrimes_map_of_surjective (I := Q ⊔ Ideal.span {P})
      Ideal.Quotient.mk_surjective]
    refine ⟨q, ?_, rfl⟩
    rwa [hmap_eq]
  haveI : IsDomain (R ⧸ p) := inferInstance
  -- `P' ≠ 0` in `D`
  have hfmt : (Ideal.Quotient.mk p) P ≠ 0 := by
    intro h
    exact hPp (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hfmr : (Ideal.Quotient.mk p) r ≠ 0 := by
    intro h
    exact hrp (Ideal.Quotient.eq_zero_iff_mem.mp h)
  -- `q'` is nonzero, so has height `≥ 1`
  have hPq : P ∈ q := hq.le (Ideal.mem_sup_right (Ideal.subset_span (Set.mem_singleton P)))
  have hq'ne : q.map (Ideal.Quotient.mk p) ≠ ⊥ := by
    intro h
    have : (Ideal.Quotient.mk p) P ∈ (⊥ : Ideal (R ⧸ p)) := by
      rw [← h]; exact Ideal.mem_map_of_mem _ hPq
    exact hfmt (Ideal.mem_bot.mp this)
  have hq'h_ne0 : (q.map (Ideal.Quotient.mk p)).height ≠ 0 :=
    fun h => hq'ne (Ideal.height_eq_zero_iff_eq_bot.mp h)
  have hge1 : 1 ≤ (q.map (Ideal.Quotient.mk p)).height :=
    ENat.one_le_iff_ne_zero.mpr hq'h_ne0
  -- Krull's principal ideal theorem: `q'` has height `≤ 1`
  have hle1 : (q.map (Ideal.Quotient.mk p)).height ≤ 1 :=
    Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes
      (Ideal.span {(Ideal.Quotient.mk p) P}) (q.map (Ideal.Quotient.mk p)) hq'
  have hq'height : (q.map (Ideal.Quotient.mk p)).height = 1 := le_antisymm hle1 hge1
  -- `(r')` also has height `1` in `D`
  have hfr_mem : (Ideal.Quotient.mk p) r ∈ q.map (Ideal.Quotient.mk p) :=
    Ideal.mem_map_of_mem _ hrq
  have hfr_nzd : (Ideal.Quotient.mk p) r ∈ nonZeroDivisors (R ⧸ p) :=
    mem_nonZeroDivisors_iff_ne_zero.mpr hfmr
  have hfr_notunit : ¬ IsUnit ((Ideal.Quotient.mk p) r) := by
    intro hu
    have htop : Ideal.span {(Ideal.Quotient.mk p) r} = ⊤ :=
      Ideal.span_singleton_eq_top.mpr hu
    have hle : Ideal.span {(Ideal.Quotient.mk p) r} ≤ q.map (Ideal.Quotient.mk p) :=
      (Ideal.span_singleton_le_iff_mem _).mpr hfr_mem
    rw [htop] at hle
    exact hq'.isPrime.ne_top (top_le_iff.mp hle)
  have hspanr_height : (Ideal.span {(Ideal.Quotient.mk p) r}).height = 1 :=
    Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors hfr_nzd hfr_notunit
  -- hence `q'` is minimal over `(r')`
  haveI : (q.map (Ideal.Quotient.mk p)).IsPrime := hq'.isPrime
  haveI : (q.map (Ideal.Quotient.mk p)).FiniteHeight :=
    (Ideal.finiteHeight_iff (q.map (Ideal.Quotient.mk p))).mpr
      (Or.inr (by rw [hq'height]; exact ENat.coe_ne_top 1))
  have hq'min : q.map (Ideal.Quotient.mk p)
      ∈ (Ideal.span {(Ideal.Quotient.mk p) r}).minimalPrimes :=
    Ideal.mem_minimalPrimes_of_height_le ((Ideal.span_singleton_le_iff_mem _).mpr hfr_mem)
      (by simp [hq'height, hspanr_height])
  -- transfer back to `R`
  refine Ideal.mem_minimalPrimes_sup (p := q) (I := p) (J := Ideal.span {r}) hpQ ?_
  have hm : (Ideal.span {r}).map (Ideal.Quotient.mk p)
      = Ideal.span {(Ideal.Quotient.mk p) r} := by
    rw [Ideal.map_span, Set.image_singleton]
  rwa [hm]

end Work.BW
