import Mathlib
import Submission.Commons.NumberTheory.NumberField.orderOf_frobenius_eq_inertiaDeg

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

namespace NK.CFTLib.IdeleHasse.Descent

open NumberField IsDedekindDomain

/-- The residue field `𝓞 M ⧸ w` of the ring of integers of `M` at the height-one prime `w`,
introduced as a standalone `def` so that its field structure does not compete with the
canonically installed quotient ring structure of `𝓞 M ⧸ w`.  The two types are definitionally
equal, so `Nat.card` does not distinguish them. -/
def ResidueFieldOf (M : Type) [Field M] [NumberField M]
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 M)) : Type := 𝓞 M ⧸ w.asIdeal

noncomputable instance (M : Type) [Field M] [NumberField M]
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 M)) : Field (ResidueFieldOf M w) :=
  letI : w.asIdeal.IsMaximal := inferInstance
  Ideal.Quotient.field w.asIdeal

/-- Let `M/K` be a finite extension of number fields whose ring of integers contains a primitive
`q`-th root of unity `ζ` (`q` a prime not dividing the cardinality `n` of the residue field of `K`
at the finite place `Q`).  If `N` divides the multiplicative order of `n` modulo `q`, then `N`
divides the local degree `e(w|Q) · f(w|Q)` at every place `w` of `M` above `Q`.

PROOF PLAN.  Let `n := Nat.card (𝓞 K ⧸ Q.asIdeal)`, `f := w.asIdeal.inertiaDeg (𝓞 K)` and
`κ := 𝓞 M ⧸ w.asIdeal` (a finite field, `w` is maximal).  Then
`Nat.card κ = n ^ f` by
`Commons.NumberTheory.NumberField.natCard_residue_eq_pow_inertiaDeg` in the module
`Submission.Commons.NumberTheory.NumberField.orderOf_frobenius_eq_inertiaDeg`
(`import Submission.Commons.NumberTheory.NumberField.orderOf_frobenius_eq_inertiaDeg`).

Reduce `ζ` to `ζbar := Ideal.Quotient.mk w.asIdeal ζ ∈ κ`.  Since `ζ` is a primitive `q`-th root
of unity, `(cyclotomic q M).IsRoot ζ` (`IsPrimitiveRoot.isRoot_cyclotomic`), so
`(cyclotomic q κ).IsRoot ζbar`.  If `ζbar = 1`, then `q = Φ_q(1) = 0` in `κ`, so
`ringChar κ ∣ q`, and `ringChar κ` is prime, hence `ringChar κ = q`, and `q ∣ Nat.card κ = n^f`
(`FiniteField.card`), contradicting `¬ q ∣ n` (`q` prime).  Hence `ζbar ≠ 1`, so
`orderOf ζbar = q` (`IsPrimitiveRoot.eq_orderOf` applied to `IsPrimitiveRoot ζbar q`, obtained
from `isRoot_cyclotomic_iff`).  Consequently `q ∣ Nat.card κ - 1 = n^f - 1` (Lagrange:
`orderOf ζbar ∣ Nat.card κˣ`, and `Nat.card κˣ = Nat.card κ - 1`).

Finally `n^f ≡ 1 (mod q)` means `((n : ZMod q)) ^ f = 1`, so
`orderOf ((n : ZMod q)) ∣ f` (`orderOf_dvd_iff_pow_eq_one`); with `hNord` this gives
`N ∣ f`, and `f ∣ e * f`.

Formalisation notes.  The case `ζbar = 1` ((`q : κ) = 0`) is handled by reducing the geometric sum
`∑_{i<q} ζ^i = 0` (`IsPrimitiveRoot.geom_sum_eq_zero`) to the residue field, which turns it into
`(q : κ) = 0`; then `CharP κ q` (`CharP.charP_iff_prime_eq_zero`) together with
`Nat.cast_card_eq_zero` yields `q ∣ Nat.card κ`.  The residue field is packaged as the standalone
type `ResidueFieldOf M w` (`def`, definitionally equal to `𝓞 M ⧸ w.asIdeal`) so that its field
structure does not compete with the canonically installed quotient ring structure of
`𝓞 M ⧸ w.asIdeal` during instance search. -/
theorem dvd_localDegree_of_isPrimitiveRoot
    {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    [FiniteDimensional K M]
    (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 M))
    (hw : w.asIdeal.LiesOver Q.asIdeal)
    {q N : ℕ} (hq : q.Prime)
    (hqndvd : ¬ q ∣ Nat.card (𝓞 K ⧸ Q.asIdeal))
    (hNord : N ∣ orderOf ((Nat.card (𝓞 K ⧸ Q.asIdeal) : ZMod q)))
    (ζ : 𝓞 M) (hζ : IsPrimitiveRoot (ζ : M) q) :
    N ∣ w.asIdeal.ramificationIdx (𝓞 K) * w.asIdeal.inertiaDeg (𝓞 K) := by
  classical
  haveI hLies : w.asIdeal.LiesOver Q.asIdeal := hw
  haveI hmaxM : w.asIdeal.IsMaximal := inferInstance
  haveI hfinQ : Finite (𝓞 M ⧸ w.asIdeal) :=
    Commons.NumberTheory.NumberField.finite_quotient_heightOneSpectrum w
  haveI hfin : Finite (ResidueFieldOf M w) := hfinQ
  haveI hft : Fintype (ResidueFieldOf M w) := Fintype.ofFinite _
  haveI hfinK : Finite (𝓞 K ⧸ Q.asIdeal) :=
    Commons.NumberTheory.NumberField.finite_quotient_heightOneSpectrum Q
  -- the residue field of `M` at `w` has cardinality `n ^ f`
  have hcard : Nat.card (ResidueFieldOf M w) =
      (Nat.card (𝓞 K ⧸ Q.asIdeal)) ^ (w.asIdeal.inertiaDeg (𝓞 K)) :=
    Commons.NumberTheory.NumberField.natCard_residue_eq_pow_inertiaDeg Q w hw
  -- the class of `ζ` in the residue field
  let ζbar : ResidueFieldOf M w := Ideal.Quotient.mk w.asIdeal ζ
  have hζq : ζ ^ q = 1 := by
    apply NumberField.RingOfIntegers.coe_injective
    rw [map_pow, map_one]
    exact hζ.pow_eq_one
  have hζbarq : ζbar ^ q = 1 := by
    show Ideal.Quotient.mk w.asIdeal ζ ^ q = 1
    rw [← map_pow, hζq, map_one]
  -- ## the arithmetic core: `q ∣ n ^ f - 1`
  have hkey : q ∣ Nat.card (𝓞 K ⧸ Q.asIdeal) ^ (w.asIdeal.inertiaDeg (𝓞 K)) - 1 := by
    by_cases h1 : ζbar = 1
    · -- `ζbar = 1` forces `q = 0` in the residue field, and then `q ∣ n ^ f`
      exfalso
      have hsumO : ∑ i ∈ Finset.range q, ζ ^ i = 0 := by
        have h : ∑ i ∈ Finset.range q, (ζ : M) ^ i = 0 :=
          IsPrimitiveRoot.geom_sum_eq_zero hζ hq.one_lt
        apply NumberField.RingOfIntegers.coe_injective
        rw [map_sum, map_zero]
        simp only [map_pow]
        exact h
      have hpush : ∑ i ∈ Finset.range q, ζbar ^ i = 0 := by
        show ∑ i ∈ Finset.range q, (Ideal.Quotient.mk w.asIdeal ζ) ^ i = 0
        have h := congrArg (Ideal.Quotient.mk w.asIdeal) hsumO
        simpa using h
      rw [h1] at hpush
      have hq0 : (q : ResidueFieldOf M w) = 0 := by simpa using hpush
      haveI hcharP : CharP (ResidueFieldOf M w) q :=
        (CharP.charP_iff_prime_eq_zero hq).mpr hq0
      have hqdvd : q ∣ Nat.card (ResidueFieldOf M w) := by
        rw [Nat.card_eq_fintype_card]
        exact (CharP.cast_eq_zero_iff (ResidueFieldOf M w) q _).mp (Nat.cast_card_eq_zero _)
      rw [hcard] at hqdvd
      exact hqndvd (hq.dvd_of_dvd_pow hqdvd)
    · -- otherwise `ζbar` has order `q`, so `q ∣ #κ - 1` by Lagrange
      have hord : orderOf ζbar = q := by
        rcases (Nat.dvd_prime hq).mp (orderOf_dvd_iff_pow_eq_one.mpr hζbarq) with h | h
        · exact absurd (orderOf_eq_one_iff.mp h) h1
        · exact h
      have hζbar0 : ζbar ≠ 0 := by
        intro h
        rw [h, zero_pow hq.pos.ne'] at hζbarq
        exact one_ne_zero hζbarq.symm
      let u : (ResidueFieldOf M w)ˣ := Units.mk0 ζbar hζbar0
      have hu : (u : ResidueFieldOf M w) = ζbar := rfl
      have hord_u : orderOf u = q := by rw [← orderOf_units, hu]; exact hord
      have hdvdM : q ∣ Nat.card (ResidueFieldOf M w) - 1 := by
        have h := orderOf_dvd_natCard u
        rw [hord_u, Nat.card_units] at h
        exact h
      rw [hcard] at hdvdM
      exact hdvdM
  -- ## `n ^ f ≡ 1 (mod q)`, so the order of `n` mod `q` divides `f`
  have hnf1 : ((Nat.card (𝓞 K ⧸ Q.asIdeal) : ZMod q)) ^
      (w.asIdeal.inertiaDeg (𝓞 K)) = 1 := by
    have hle : 1 ≤ Nat.card (𝓞 K ⧸ Q.asIdeal) ^ (w.asIdeal.inertiaDeg (𝓞 K)) :=
      one_le_pow₀ (Nat.card_pos (α := 𝓞 K ⧸ Q.asIdeal))
    have h0 : ((Nat.card (𝓞 K ⧸ Q.asIdeal) ^
        (w.asIdeal.inertiaDeg (𝓞 K)) : ℕ) : ZMod q) - 1 = 0 := by
      have hz : (((Nat.card (𝓞 K ⧸ Q.asIdeal) ^
          (w.asIdeal.inertiaDeg (𝓞 K)) - 1 : ℕ) : ℤ) : ZMod q) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mpr (Int.natCast_dvd_natCast.mpr hkey)
      rw [Int.cast_natCast] at hz
      rwa [Nat.cast_sub hle, Nat.cast_one] at hz
    rw [← Nat.cast_pow]
    exact sub_eq_zero.mp h0
  have hordn : orderOf ((Nat.card (𝓞 K ⧸ Q.asIdeal) : ZMod q)) ∣
      w.asIdeal.inertiaDeg (𝓞 K) :=
    orderOf_dvd_iff_pow_eq_one.mpr hnf1
  exact (hNord.trans hordn).trans
    (dvd_mul_left (w.asIdeal.inertiaDeg (𝓞 K)) (w.asIdeal.ramificationIdx (𝓞 K)))

end NK.CFTLib.IdeleHasse.Descent
