import Mathlib
import Submission.Work.SpecLin.Setup.exists_ltseries_of_unique_eqStep
import Submission.Work.SpecLin.Setup.under_eqStep_unique

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SpecLin.Setup

set_option linter.style.haveILetI false

open Polynomial

/-- The prime spectrum of a valuation domain is linearly ordered: the primes of `R` are totally
ordered by inclusion.  This is recorded as a (local) `LinearOrder` instance so that the compression
lemma `Work.SpecLin.Setup.exists_ltseries_of_unique_eqStep` applies to the contraction map
`Spec R[X] → Spec R`. -/
@[instance_reducible]
noncomputable def linearOrderPrimeSpectrum (R : Type*) [CommRing R] [IsDomain R] [ValuationRing R] :
    LinearOrder (PrimeSpectrum R) := by
  classical
  exact
    { (inferInstance : PartialOrder (PrimeSpectrum R)) with
      le_total := fun a b => by
        rcases le_total a.asIdeal b.asIdeal with h | h
        · exact Or.inl ((PrimeSpectrum.asIdeal_le_asIdeal a b).mp h)
        · exact Or.inr ((PrimeSpectrum.asIdeal_le_asIdeal b a).mp h)
      toDecidableLE := Classical.decRel _ }

/-- **Pointwise upper bound (prime spectrum form).**  For `R` a valuation domain and `Q` a prime of
`R[X]`, the height of `Q` is at most one more than the height of its contraction to `R`.

The "at most one vertical step" input is `Work.SpecLin.Setup.under_eqStep_unique`, compressed by
`Work.SpecLin.Setup.exists_ltseries_of_unique_eqStep`. -/
theorem orderHeight_le_under_height_add_one {R : Type*} [CommRing R] [IsDomain R]
    [ValuationRing R] (Q : PrimeSpectrum (Polynomial R)) :
    Order.height Q ≤ (Q.asIdeal.under R).height + 1 := by
  letI : LinearOrder (PrimeSpectrum R) := linearOrderPrimeSpectrum R
  have hmono : Monotone (PrimeSpectrum.comap (algebraMap R (Polynomial R))) := by
    intro a b hab
    show (PrimeSpectrum.comap (algebraMap R (Polynomial R)) a).asIdeal ≤
      (PrimeSpectrum.comap (algebraMap R (Polynomial R)) b).asIdeal
    rw [PrimeSpectrum.comap_asIdeal, PrimeSpectrum.comap_asIdeal]
    exact Ideal.comap_mono ((PrimeSpectrum.asIdeal_le_asIdeal a b).mp hab)
  have hmain : Order.height Q ≤
      Order.height (PrimeSpectrum.comap (algebraMap R (Polynomial R)) Q) + 1 := by
    rw [Order.height_le_iff]
    intro l hl
    obtain ⟨m, hm_last, hm_len⟩ :=
      exists_ltseries_of_unique_eqStep (PrimeSpectrum.comap (algebraMap R (Polynomial R)))
        hmono l (by
          intro i j hi hj
          apply under_eqStep_unique l i j
          · simpa [PrimeSpectrum.comap_asIdeal, Ideal.under_def] using
              congrArg PrimeSpectrum.asIdeal hi
          · simpa [PrimeSpectrum.comap_asIdeal, Ideal.under_def] using
              congrArg PrimeSpectrum.asIdeal hj)
    have hmle : m.last ≤ PrimeSpectrum.comap (algebraMap R (Polynomial R)) Q := by
      rw [hm_last]
      exact hmono hl
    calc (↑l.length : ℕ∞) ≤ ↑(m.length + 1) := by exact_mod_cast hm_len
      _ = (↑m.length : ℕ∞) + 1 := ENat.natCast_add _ _
      _ ≤ Order.height (PrimeSpectrum.comap (algebraMap R (Polynomial R)) Q) + 1 :=
          add_le_add (Order.length_le_height hmle) le_rfl
  have hFeq : Order.height (PrimeSpectrum.comap (algebraMap R (Polynomial R)) Q) =
      (Q.asIdeal.under R).height := by
    rw [← PrimeSpectrum.height_eq_orderHeight
        (PrimeSpectrum.comap (algebraMap R (Polynomial R)) Q),
      PrimeSpectrum.comap_asIdeal, Ideal.under_def]
  rw [hFeq] at hmain
  exact hmain

/-- **Pointwise upper bound.**  For `R` a valuation domain and `𝔮` a prime of `R[X]`, the height of
`𝔮` is at most one more than the height of its contraction to `R`. -/
theorem height_le_under_height_add_one {R : Type*} [CommRing R] [IsDomain R] [ValuationRing R]
    (q : Ideal (Polynomial R)) [q.IsPrime] :
    q.height ≤ (q.under R).height + 1 := by
  let Q : PrimeSpectrum (Polynomial R) := ⟨q, ‹q.IsPrime›⟩
  have hQ : Q.asIdeal = q := rfl
  have h := orderHeight_le_under_height_add_one Q
  rw [hQ] at h
  rw [← PrimeSpectrum.height_eq_orderHeight Q] at h
  exact h

/-- **The Krull dimension of a polynomial ring over a valuation ring.**

For a valuation ring `R`, `dim R[X] = dim R + 1`.  This is the sharp form of the general
inequality `dim R[X] ≤ 2 * dim R + 1` (`Polynomial.ringKrullDim_le`) for a Prüfer/Bézout domain;
it fails for general `R` (Seidenberg).  It is the commutative-algebra input of
`Work.SpecLin.Setup.krullDimLE_tensor`.

Suggested route.
* Lower bound: `ringKrullDim_succ_le_ringKrullDim_polynomial`.
* Upper bound: by `ringKrullDim_le_iff_isMaximal_height_le` it suffices to prove, for every prime
  `𝔮` of `Polynomial R` with `p := 𝔮.under R`, the pointwise bound `𝔮.height ≤ p.height + 1`; then
  use `Ideal.height_le_ringKrullDim_of_isPrime` for `p`.
* For the pointwise bound use `Order.height_le_iff`: given
  `l : LTSeries (PrimeSpectrum (Polynomial R))` with `l.last ≤ 𝔮`, one must show
  `l.length ≤ (l.last.asIdeal.under R).height + 1`.  Apply the compression result proved in
  parallel at `SpecLin/Setup/exists_ltseries_of_unique_eqStep` (file
  `Submission/Work/SpecLin/Setup/exists_ltseries_of_unique_eqStep.lean`) to
  `f := PrimeSpectrum.comap (algebraMap R (Polynomial R))`, which needs the assertion that the
  contraction map has **at most one equal step** along a chain (proved in parallel at
  `SpecLin/Setup/under_eqStep_unique`): if
  `(l i).asIdeal.under R = (l i.succ).asIdeal.under R` and
  `(l j).asIdeal.under R = (l j.succ).asIdeal.under R` then `i = j`.
  That assertion is proved by: (a) the fibre of `Spec R[X] → Spec R` over a prime is (order
  isomorphic to) `Spec κ(p)[X]`, of Krull dimension one, so three primes over one prime of `R` are
  impossible; (b) the "bad configuration" `x < x'` over `q`, `y < y'` over `q'` with `x' ≤ y` and
  `q < q'` is impossible (case `x' + q'R[X] = ⊤` gives `1 ∈ y`; case `x' ⊄ q'R[X]` gives two
  nonzero primes in `κ(q')[X]`, which is one-dimensional; case `x' ⊆ q'R[X]`, after reducing modulo
  `q`, gives a nonzero prime `𝔞` of `V[X]` (`V = R ⧸ q` a valuation ring, `m = q' ⧸ q`) with
  `𝔞 ⊓ V = ⊥` and `𝔞 ≤ mV[X]`, impossible as some `g ∈ 𝔞` has a unit coefficient: take
  `0 ≠ f ∈ 𝔞`, all of whose coefficients lie in `m`, and divide `f` by a coefficient dividing all
  of them, which exists by `ValuationRing.dvd_total`).
* Finally `Order.length_le_height` converts the compressed chain `m` in `Spec R` into the bound
  `l.length ≤ (f l.last).height + 1`.
If the two parallel results are not yet available, this target may of course be proved from
scratch (or with inlined versions of them). -/
theorem ringKrullDim_polynomial_valuationRing {R : Type*} [CommRing R] [IsDomain R] [ValuationRing R] :
    ringKrullDim (Polynomial R) = ringKrullDim R + 1 := by
  refine le_antisymm ?_ ringKrullDim_succ_le_ringKrullDim_polynomial
  rw [ringKrullDim_le_iff_height_le]
  intro q hq
  haveI := hq
  have h1 : q.height ≤ (q.under R).height + 1 := height_le_under_height_add_one q
  have h2 : (q.under R).height ≤ ringKrullDim R := Ideal.height_le_ringKrullDim_of_isPrime
  calc (↑q.height : WithBot ℕ∞) ≤ ↑((q.under R).height + 1) := WithBot.coe_le_coe.mpr h1
    _ = (↑(q.under R).height : WithBot ℕ∞) + 1 := WithBot.coe_add _ _
    _ ≤ ringKrullDim R + 1 := by gcongr

end Work.SpecLin.Setup
