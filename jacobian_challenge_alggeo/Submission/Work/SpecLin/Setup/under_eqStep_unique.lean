/-
# At most one "vertical" step in a chain of primes of `R[X]` over a valuation ring `R`
-/
import Mathlib
import Submission.Work.SpecLin.Setup.eq_bot_of_isPrime_le_map_C

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

namespace Work.SpecLin.Setup

open Polynomial PrimeSpectrum Ideal

section Helpers

variable {R : Type*} [CommRing R]

/-- The contraction of the extension `q·R[X]` of an ideal `q` back to `R` is `q`. -/
lemma under_map_C (q : Ideal R) :
    (Ideal.map (C : R →+* Polynomial R) q).under R = q := by
  ext x
  rw [Ideal.mem_under, Polynomial.algebraMap_eq, Ideal.mem_map_C_iff]
  constructor
  · intro h; simpa using h 0
  · intro h n
    match n with
    | 0 => simpa using h
    | _ + 1 => simp

end Helpers

section Three

variable {R : Type*} [CommRing R]

/-- There are no three primes of `R[X]` lying over the same prime of `R`: the fibre of
`Spec R[X] → Spec R` over a prime `q` is `Spec κ(q)[X]`, which has Krull dimension one. -/
theorem no_three_of_under_eq (q : Ideal R) [q.IsPrime]
    (p1 p2 p3 : Ideal (Polynomial R)) [p1.IsPrime] [p2.IsPrime] [p3.IsPrime]
    (h1 : p1.under R = q) (h2 : p2.under R = q) (h3 : p3.under R = q)
    (h12 : p1 < p2) (h23 : p2 < p3) : False := by
  have E : q.primesOver (Polynomial R) ≃o PrimeSpectrum (Polynomial q.ResidueField) :=
    (PrimeSpectrum.primesOverOrderIsoFiber R (Polynomial R) q).trans
      (PrimeSpectrum.comapEquiv (polyEquivTensor R q.ResidueField).symm.toRingEquiv)
  have hAB : (⟨p1, inferInstance, ⟨h1.symm⟩⟩ : q.primesOver (Polynomial R))
      < ⟨p2, inferInstance, ⟨h2.symm⟩⟩ := Subtype.mk_lt_mk.mpr h12
  have hBC : (⟨p2, inferInstance, ⟨h2.symm⟩⟩ : q.primesOver (Polynomial R))
      < ⟨p3, inferInstance, ⟨h3.symm⟩⟩ := Subtype.mk_lt_mk.mpr h23
  have hP12 : (E ⟨p1, inferInstance, ⟨h1.symm⟩⟩).asIdeal
      < (E ⟨p2, inferInstance, ⟨h2.symm⟩⟩).asIdeal :=
    asIdeal_lt_asIdeal _ _ |>.mpr (E.lt_iff_lt.mpr hAB)
  have hP23 : (E ⟨p2, inferInstance, ⟨h2.symm⟩⟩).asIdeal
      < (E ⟨p3, inferInstance, ⟨h3.symm⟩⟩).asIdeal :=
    asIdeal_lt_asIdeal _ _ |>.mpr (E.lt_iff_lt.mpr hBC)
  have hP2ne : (E ⟨p2, inferInstance, ⟨h2.symm⟩⟩).asIdeal ≠ ⊥ := by
    intro h
    rw [h] at hP12
    exact absurd (hP12.trans_le (bot_le : (⊥ : Ideal q.ResidueField[X]) ≤ _)) (lt_irrefl _)
  have hmax : (E ⟨p2, inferInstance, ⟨h2.symm⟩⟩).asIdeal.IsMaximal :=
    Ideal.IsPrime.isMaximal_of_ne_bot (E ⟨p2, inferInstance, ⟨h2.symm⟩⟩).isPrime hP2ne
  have hP3nt : (E ⟨p3, inferInstance, ⟨h3.symm⟩⟩).asIdeal ≠ ⊤ :=
    (E ⟨p3, inferInstance, ⟨h3.symm⟩⟩).isPrime.ne_top
  have heq : (E ⟨p2, inferInstance, ⟨h2.symm⟩⟩).asIdeal
      = (E ⟨p3, inferInstance, ⟨h3.symm⟩⟩).asIdeal :=
    IsMaximal.eq_of_le (I := _) (J := _) hmax hP3nt (le_of_lt hP23)
  rw [heq] at hP23
  exact absurd hP23 (lt_irrefl _)

end Three

section Bad

variable {R : Type*} [CommRing R] [IsDomain R] [ValuationRing R]

/-- **No "bad configuration", third case.**  Let `R` be a valuation ring, `q ⊊ q'` primes of `R`,
and `x ⊊ x'` primes of `R[X]` with `x.under R = x'.under R = q`.  Then `x'` cannot be contained in
the extension `q'·R[X]`.

Proof: reduce modulo `q`.  Since `q ⊆ x ⊆ x'`, the image `𝔞 := x' ⧸ qR[X]` of `x'` in
`V[X] := (R ⧸ q)[X]` is a prime ideal, it is nonzero (else `x' ⊆ qR[X] ⊆ x`), it contracts to `⊥`
in `V`, and it is contained in `mV[X]` for the proper ideal `m := q' ⧸ q`.  This contradicts
`eq_bot_of_isPrime_le_map_C`. -/
theorem no_bad_config_case3 {q q' : Ideal R} [hqp : q.IsPrime] [hq'p : q'.IsPrime]
    (hqq' : q < q') {x x' : Ideal (Polynomial R)} [x.IsPrime] [x'.IsPrime]
    (hx : x.under R = q) (hx' : x'.under R = q) (hxx' : x < x')
    (hle : x' ≤ Ideal.map (C : R →+* Polynomial R) q') : False := by
  haveI hdom : IsDomain (R ⧸ q) := (Ideal.Quotient.isDomain_iff_prime q).mpr hqp
  haveI hval : ValuationRing (R ⧸ q) :=
    Function.Surjective.valuationRing (Ideal.Quotient.mk q) Ideal.Quotient.mk_surjective
  let ψ : Polynomial R →+* Polynomial (R ⧸ q) := Polynomial.mapRingHom (Ideal.Quotient.mk q)
  have hsurj : Function.Surjective ψ :=
    Polynomial.map_surjective _ Ideal.Quotient.mk_surjective
  have hker : RingHom.ker ψ = Ideal.map (C : R →+* Polynomial R) q := by
    ext a
    rw [RingHom.mem_ker, Ideal.mem_map_C_iff]
    constructor
    · intro h n
      have h2 := congrArg (fun f : Polynomial (R ⧸ q) => f.coeff n) h
      simp only [ψ, Polynomial.coe_mapRingHom, Polynomial.coeff_map, Polynomial.coeff_zero] at h2
      exact Ideal.Quotient.eq_zero_iff_mem.mp h2
    · intro h
      change ψ a = 0
      ext n
      simp only [ψ, Polynomial.coe_mapRingHom, Polynomial.coeff_map, Polynomial.coeff_zero]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (h n)
  have hCmem : Ideal.map (C : R →+* Polynomial R) q ≤ x' := by
    rw [Ideal.map_le_iff_le_comap]
    rw [show Ideal.comap (C : R →+* Polynomial R) x' = x'.under R from by
      rw [show (C : R →+* Polynomial R) = algebraMap R (Polynomial R) from
        Polynomial.algebraMap_eq.symm, Ideal.under_def]]
    rw [hx']
  have hCmemx : Ideal.map (C : R →+* Polynomial R) q ≤ x := by
    rw [Ideal.map_le_iff_le_comap]
    rw [show Ideal.comap (C : R →+* Polynomial R) x = x.under R from by
      rw [show (C : R →+* Polynomial R) = algebraMap R (Polynomial R) from
        Polynomial.algebraMap_eq.symm, Ideal.under_def]]
    rw [hx]
  let 𝔞 : Ideal (Polynomial (R ⧸ q)) := Ideal.map ψ x'
  have h𝔞prime : 𝔞.IsPrime :=
    Ideal.map_isPrime_of_surjective (f := ψ) hsurj (I := x') (hker.le.trans hCmem)
  have h𝔞ne : 𝔞 ≠ ⊥ := by
    intro hbot
    have h1 : x' ≤ Ideal.map (C : R →+* Polynomial R) q :=
      hker ▸ (Ideal.map_eq_bot_iff_le_ker ψ).mp hbot
    exact absurd (lt_of_le_of_lt (h1.trans hCmemx) hxx') (lt_irrefl _)
  have hcomap : Ideal.comap ψ (Ideal.map ψ x') = x' := by
    rw [Ideal.comap_map_of_surjective ψ hsurj]
    rw [show Ideal.comap ψ (⊥ : Ideal (Polynomial (R ⧸ q)))
        = Ideal.map (C : R →+* Polynomial R) q from by
      rw [← RingHom.ker_eq_comap_bot, hker]]
    exact sup_eq_left.mpr hCmem
  have h𝔞und : 𝔞.under (R ⧸ q) = ⊥ := by
    apply Ideal.comap_injective_of_surjective (Ideal.Quotient.mk q) Ideal.Quotient.mk_surjective
    rw [Ideal.under_def, Polynomial.algebraMap_eq, Ideal.comap_comap]
    rw [show ((C : (R ⧸ q) →+* Polynomial (R ⧸ q))).comp (Ideal.Quotient.mk q)
        = ψ.comp (C : R →+* Polynomial R) from by
      ext r; simp [ψ, Polynomial.coe_mapRingHom, Polynomial.map_C]]
    rw [← Ideal.comap_comap, hcomap]
    rw [show Ideal.comap (C : R →+* Polynomial R) x' = q from by
      rw [show (C : R →+* Polynomial R) = algebraMap R (Polynomial R) from
        Polynomial.algebraMap_eq.symm, ← Ideal.under_def, hx']]
    rw [show Ideal.comap (Ideal.Quotient.mk q) (⊥ : Ideal (R ⧸ q)) = q from by
      rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]]
  have h𝔞le : 𝔞 ≤ Ideal.map (C : (R ⧸ q) →+* Polynomial (R ⧸ q))
      (Ideal.map (Ideal.Quotient.mk q) q') := by
    have h1 : 𝔞 ≤ Ideal.map ψ (Ideal.map (C : R →+* Polynomial R) q') := Ideal.map_mono hle
    rwa [show Ideal.map ψ (Ideal.map (C : R →+* Polynomial R) q')
        = Ideal.map (C : (R ⧸ q) →+* Polynomial (R ⧸ q)) (Ideal.map (Ideal.Quotient.mk q) q')
        from by
      rw [Ideal.map_map, Ideal.map_map]
      congr 1
      ext r; simp [ψ, Polynomial.coe_mapRingHom, Polynomial.map_C]] at h1
  have hm : Ideal.map (Ideal.Quotient.mk q) q' ≠ ⊤ := by
    intro htop
    have h1 : (1 : R ⧸ q) ∈ Ideal.map (Ideal.Quotient.mk q) q' := htop ▸ Submodule.mem_top
    obtain ⟨a, ha, haeq⟩ :=
      (Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mk q) Ideal.Quotient.mk_surjective).mp h1
    have ha1 : a - 1 ∈ q := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      rw [map_sub, haeq, map_one, sub_self]
    have h2 : a - 1 ∈ q' := hqq'.le ha1
    have h3 : (1 : R) ∈ q' := by simpa using sub_mem ha h2
    exact hq'p.ne_top (Ideal.eq_top_iff_one q' |>.mpr h3)
  exact h𝔞ne (eq_bot_of_isPrime_le_map_C hm h𝔞prime h𝔞und h𝔞le)

end Bad

/-- **At most one "equal step"** for chains of primes of `R[X]` over a valuation ring `R`.

Let `l` be a strictly increasing chain of primes of `Polynomial R` and let `p i` be the contraction
of `l i` to `R`.  If two *different* consecutive steps of the chain have the same contraction, then
the two indices are equal: at most one step of `l` can be "vertical".  No hypothesis on the
dimension of `R` is needed or used.

This is the key combinatorial input to `ringKrullDim_polynomial_valuationRing`.

Suggested route.
* The fibre of `Spec R[X] → Spec R` over a prime `p` is order-isomorphic to the spectrum of
  `κ(p)[X]`, which has Krull dimension one (`PrimeSpectrum.primesOverOrderIsoFiber` +
  `polyEquivTensor` + `Polynomial.ringKrullDim_of_isNoetherianRing`, as in the proof of
  `Polynomial.ringKrullDim_le`).  Hence three primes of `R[X]` forming a chain over one prime of
  `R` are impossible (a chain of length two in the fibre would force `2 ≤ krullDim (Spec κ(p)[X])`).
* "Bad configuration": there are no primes `x < x'` of `R[X]` with equal contractions `q`, and
  primes `y < y'` with equal contractions `q'`, such that `x' ≤ y` and `q < q'`.
  - If `x' + q' * R[X] = ⊤` then `1 ∈ y`, contradiction with `y` prime.
  - Otherwise, if `x' ⊄ q' * R[X]`, the image of `x'` in the fibre `κ(q')[X]` generates a nonzero
    ideal contained in the prime of the fibre corresponding to `y`; as `y < y'` are distinct primes
    over `q'`, `κ(q')[X]` would contain a two-step chain `0 < ȳ < ȳ'`, contradicting
    `dim κ(q')[X] = 1`.
  - If `x' ⊆ q' * R[X]`, reduce modulo `q`: `V := R ⧸ q` is a valuation ring with ideal
    `m := q' ⧸ q`, and the image `𝔞` of `x'` in `V[X]` is a nonzero prime with `𝔞 ⊓ V = ⊥` and
    `𝔞 ≤ mV[X]` (note `x' ≠ x` and `x' ⊇ qR[X]` give `𝔞 ≠ 0`).  This is impossible: for
    `0 ≠ f ∈ 𝔞`, all coefficients of `f` lie in `m`; by `ValuationRing.dvd_total`, pick a
    coefficient `c` of `f` dividing all coefficients of `f`; then `f = C c * g` with `g ∈ 𝔞`
    (since `c ∉ 𝔞` because `𝔞 ⊓ V = ⊥` and `𝔞` is prime) and `g ∉ mV[X]` (its `X ^ j`-th
    coefficient is `1`), contradiction.
* Conclude by contradiction: given equal steps at distinct indices `i < j`, if `j = i + 1` three
  primes over one prime of `R` arise; if `i + 2 ≤ j` the bad configuration arises (the contraction
  of `l (i+1)` is strictly smaller than that of `l j`, otherwise `l i < l (i+1) < l j` would be
  three primes over one prime of `R`). -/
theorem under_eqStep_unique {R : Type*} [CommRing R] [IsDomain R] [ValuationRing R]
    (l : LTSeries (PrimeSpectrum (Polynomial R))) :
    ∀ i j : Fin l.length,
      (l i.castSucc).asIdeal.under R = (l i.succ).asIdeal.under R →
      (l j.castSucc).asIdeal.under R = (l j.succ).asIdeal.under R → i = j := by
  suffices key : ∀ i j : Fin l.length, i < j →
      (l i.castSucc).asIdeal.under R = (l i.succ).asIdeal.under R →
      (l j.castSucc).asIdeal.under R = (l j.succ).asIdeal.under R → False by
    intro i j hi hj
    rcases lt_trichotomy i j with h | h | h
    · exact (key i j h hi hj).elim
    · exact h
    · exact (key j i h hj hi).elim
  intro i j hij hi hj
  -- the underlying strictly increasing chain of primes of `R[X]` and its contractions
  have hP : StrictMono (fun k : Fin (l.length + 1) => (l k).asIdeal) :=
    fun a b hab => (PrimeSpectrum.asIdeal_lt_asIdeal (l a) (l b)).mpr (l.strictMono hab)
  have hQ : Monotone (fun k : Fin (l.length + 1) => (l k).asIdeal.under R) :=
    fun a b hab => Ideal.comap_mono (l.monotone hab)
  have hbc : i.succ ≤ j.castSucc := Fin.succ_le_castSucc_iff.mpr hij
  rcases lt_or_eq_of_le hbc with hlt | heq
  · rcases eq_or_lt_of_le (hQ (le_of_lt hlt)) with heq' | hlt'
    · -- `i.succ` and `j.castSucc` have the same contraction: three primes over it
      exact no_three_of_under_eq ((l i.castSucc).asIdeal.under R) (l i.castSucc).asIdeal
        (l i.succ).asIdeal (l j.castSucc).asIdeal rfl hi.symm (heq'.symm.trans hi.symm)
        (hP Fin.castSucc_lt_succ) (hP hlt)
    · -- `Q i.succ < Q j.castSucc`
      by_cases hcase : (l i.succ).asIdeal ≤ Ideal.map (C : R →+* Polynomial R)
          ((l j.castSucc).asIdeal.under R)
      · -- bad configuration, third case
        exact no_bad_config_case3 (hi.symm ▸ hlt') rfl hi.symm (hP Fin.castSucc_lt_succ) hcase
      · -- otherwise `q'·R[X]` is a third prime over `Q j.castSucc`
        have hle : Ideal.map (C : R →+* Polynomial R) ((l j.castSucc).asIdeal.under R)
            ≤ (l j.castSucc).asIdeal := by
          rw [Ideal.map_le_iff_le_comap]
          rw [show Ideal.comap (C : R →+* Polynomial R) (l j.castSucc).asIdeal
              = ((l j.castSucc).asIdeal).under R from by
            rw [show (C : R →+* Polynomial R) = algebraMap R (Polynomial R) from
              Polynomial.algebraMap_eq.symm, Ideal.under_def]]
        have hne : Ideal.map (C : R →+* Polynomial R) ((l j.castSucc).asIdeal.under R)
            ≠ (l j.castSucc).asIdeal :=
          fun hEq => hcase ((hP hlt).le.trans (le_of_eq hEq.symm))
        have hlt2 := lt_of_le_of_ne hle hne
        exact no_three_of_under_eq
          ((Ideal.map (C : R →+* Polynomial R) ((l j.castSucc).asIdeal.under R)).under R)
          (Ideal.map (C : R →+* Polynomial R) ((l j.castSucc).asIdeal.under R))
          (l j.castSucc).asIdeal (l j.succ).asIdeal rfl
          (under_map_C ((l j.castSucc).asIdeal.under R)).symm
          (hj.symm.trans (under_map_C ((l j.castSucc).asIdeal.under R)).symm)
          hlt2 (hP Fin.castSucc_lt_succ)
  · -- `i.succ = j.castSucc`: three primes over `Q i.castSucc`
    exact no_three_of_under_eq ((l i.castSucc).asIdeal.under R) (l i.castSucc).asIdeal
      (l i.succ).asIdeal (l j.succ).asIdeal rfl hi.symm
      (hj.symm.trans ((congrArg (fun k : Fin (l.length + 1) => (l k).asIdeal.under R)
        heq.symm).trans hi.symm))
      (hP Fin.castSucc_lt_succ) (hP (Fin.succ_lt_succ_iff.mpr hij))


end Work.SpecLin.Setup
