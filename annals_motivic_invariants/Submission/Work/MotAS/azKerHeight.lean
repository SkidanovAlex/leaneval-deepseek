import Mathlib
import Submission.Work.MotAS.azThetaDefs
import Submission.Work.MotAS.azFracRange
import Submission.Work.MotK.TGen.CubTResidue
import Submission.Work.MotV.trdeg_fractionRing_mvPolynomial

set_option linter.unusedVariables false -- v435-speed

/-!
# `Work.MotAS.azKerHeight` — the kernel of the AS chart parametrisation has height one

`Work.MotAS.azTheta a b g` (`Submission/Work/MotAS/censusAS2_junk_fwVec0.lean`) is the
`K`-algebra map `K[x₀,x₁,x₂] → K(u,v)` obtained by substituting the rational parametrisation
`(χ₁/χ₄, χ₂/χ₄, χ₃/χ₄)` of the AS chart surface `{f̂₀ = 0}` into `K[x₀,x₁,x₂]`; geometrically it is
the (inverse) chart map of the `AS` (Artin–Schreier) link restricted to the plane `ẑ₃ = 1`, whose
image has fraction field the two-variable rational function field `K(u,v)`
(`Work.MotAS.azFracRange`).

This file proves that its kernel — the vanishing ideal of the *curve* `{f̂₀ = 0}` in the plane —
has height one, from the same three hypotheses that enter `azFracRange`:

* `h3`: `θ f̂₃ ≠ 0` (the parametrisation is non-degenerate),
* `h1`, `h2`: `u · θ f̂₃ = θ f̂₁`, `v · θ f̂₃ = θ f̂₂` (the two coordinate functions of the
  parametrising plane are quotients of elements of the range).

## Route

`height p = dim K[x₀,x₁,x₂] - dim (R ⧸ p) = 3 - trdeg_K K(u,v) = 1`, formalised as
`height_eq_one_of_trdeg_eq_two` below (a universe-polymorphic version of
`Work.MotK.CensusBridge.height_eq_one_of_trdeg_eq_two`, needed because `K` is an arbitrary universe
in the statement):

* `height ≤ 1`: `trdeg_K K(u,v) = 2` forces the quotient `R ⧸ p` to have two nested primes, whose
  pullbacks to `R` give a chain `p < Q₁ < Q₂`; with `ringKrullDim K[x₀,x₁,x₂] = 3` this yields
  `p.height + 2 ≤ 3` (Noether normalisation, `Work.MotK.TGen.two_primes_of_trdeg`);
* `1 ≤ height`: `p ≠ ⊥`, because otherwise the residue field would be the three-variable rational
  function field, of transcendence degree three.

The only bookkeeping specific to `azTheta` is that `FractionRing ((azTheta a b g).range)` —
the object `azFracRange` describes — is the fraction field of `R ⧸ ker (azTheta a b g)`, since
`R ⧸ ker θ ≃ₐ[K] θ.range` (`Ideal.quotientKerEquivRange`) and `IsFractionRing.algEquivOfAlgEquiv`
transports this to the fraction rings. -/

universe u

namespace Work.MotAS

/-- `RatFunc K = K(t)` has transcendence degree one over `K`. -/
private lemma trdeg_ratFunc_eq_one (K : Type u) [Field K] : Algebra.trdeg K (RatFunc K) = 1 := by
  haveI : Algebra.IsAlgebraic (Polynomial K) (RatFunc K) :=
    (IsFractionRing.comap_isAlgebraic_iff (A := Polynomial K) (K := RatFunc K)
      (C := RatFunc K)).mpr inferInstance
  have hz : Algebra.trdeg (Polynomial K) (RatFunc K) = 0 := trdeg_eq_zero
  have h := trdeg_add_eq K (Polynomial K) (A := RatFunc K)
  rw [hz, add_zero] at h
  rw [Polynomial.trdeg_of_isDomain] at h
  exact h.symm

/-- `trdeg_K K(u)(v) = 2`, by the tower law. -/
private lemma trdeg_ratFunc_ratFunc_eq_two (K : Type u) [Field K] :
    Algebra.trdeg K (RatFunc (RatFunc K)) = 2 := by
  have h1 : Algebra.trdeg K (RatFunc K) = 1 := trdeg_ratFunc_eq_one K
  have h2 : Algebra.trdeg (RatFunc K) (RatFunc (RatFunc K)) = 1 := by
    haveI : Algebra.IsAlgebraic (Polynomial (RatFunc K)) (RatFunc (RatFunc K)) :=
      (IsFractionRing.comap_isAlgebraic_iff (A := Polynomial (RatFunc K))
        (K := RatFunc (RatFunc K)) (C := RatFunc (RatFunc K))).mpr inferInstance
    have hz : Algebra.trdeg (Polynomial (RatFunc K)) (RatFunc (RatFunc K)) = 0 := trdeg_eq_zero
    have h := trdeg_add_eq (RatFunc K) (Polynomial (RatFunc K)) (A := RatFunc (RatFunc K))
    rw [hz, add_zero] at h
    rw [Polynomial.trdeg_of_isDomain] at h
    exact h.symm
  have h := trdeg_add_eq K (RatFunc K) (A := RatFunc (RatFunc K))
  rw [h1, h2] at h
  rw [← h]
  norm_num

/-- `trdeg_K Frac K[X₀,…,X_{m-1}] = m`; the universe of the right-hand side is corrected by
`Cardinal.lift` since `K` may live in any universe. -/
private lemma trdeg_fractionRing_mvPolynomial (K : Type u) [Field K] (m : ℕ) :
    Algebra.trdeg K (FractionRing (MvPolynomial (Fin m) K))
      = Cardinal.lift.{u, 0} (Cardinal.mk (Fin m)) := by
  have halg : Algebra.IsAlgebraic (MvPolynomial (Fin m) K)
      (FractionRing (MvPolynomial (Fin m) K)) := Work.MotV.isAlgebraic_fractionRing_self _
  have h := trdeg_add_eq K (MvPolynomial (Fin m) K)
    (A := FractionRing (MvPolynomial (Fin m) K))
  have h2 : Algebra.trdeg (MvPolynomial (Fin m) K)
      (FractionRing (MvPolynomial (Fin m) K)) = 0 := trdeg_eq_zero
  rw [h2, add_zero] at h
  rw [← h, MvPolynomial.trdeg_of_isDomain]

/-- **A prime of `K[X₀,X₁,X₂]` whose residue field has transcendence degree two has height one.**
This is the codimension-one case of the dimension formula
`height p = 3 - trdeg_K (Frac (R ⧸ p))` for the three-dimensional polynomial ring, stated here in
the universe of `K` (unlike `Work.MotK.CensusBridge.height_eq_one_of_trdeg_eq_two`). -/
private theorem height_eq_one_of_trdeg_eq_two (K : Type u) [Field K]
    (p : Ideal (MvPolynomial (Fin 3) K)) [p.IsPrime]
    (htr : Algebra.trdeg K (FractionRing (MvPolynomial (Fin 3) K ⧸ p)) = 2) :
    p.height = 1 := by
  classical
  haveI hdom : IsDomain (MvPolynomial (Fin 3) K ⧸ p) := Ideal.Quotient.isDomain p
  haveI hft : Algebra.FiniteType K (MvPolynomial (Fin 3) K ⧸ p) :=
    Algebra.FiniteType.quotient K p
  -- Two nested primes in `A = R ⧸ p`, the lower one non-zero (Noether normalisation)
  obtain ⟨𝔭₁, 𝔭₂, h𝔭₁, h𝔭₂, hlt, hne⟩ :=
    Work.MotK.TGen.two_primes_of_trdeg (A := MvPolynomial (Fin 3) K ⧸ p) (by rw [htr])
  haveI := h𝔭₁
  haveI := h𝔭₂
  -- their pullbacks to `R`
  have hQ₁prime : (𝔭₁.comap (Ideal.Quotient.mk p)).IsPrime := Ideal.comap_isPrime _ _
  have hQ₂prime : (𝔭₂.comap (Ideal.Quotient.mk p)).IsPrime := Ideal.comap_isPrime _ _
  haveI := hQ₁prime
  haveI := hQ₂prime
  have hPQ₁ : p ≤ 𝔭₁.comap (Ideal.Quotient.mk p) := by
    have h := Ideal.ker_le_comap (Ideal.Quotient.mk p) (K := 𝔭₁)
    rwa [Ideal.mk_ker] at h
  have hlt₁ : p < 𝔭₁.comap (Ideal.Quotient.mk p) := by
    refine lt_of_le_of_ne hPQ₁ fun heq => hne ?_
    have hm := Ideal.map_comap_of_surjective (Ideal.Quotient.mk p)
      Ideal.Quotient.mk_surjective 𝔭₁
    have hmap : Ideal.map (Ideal.Quotient.mk p) (Ideal.comap (Ideal.Quotient.mk p) 𝔭₁) = ⊥ := by
      rw [heq.symm, Ideal.map_quotient_self]
    exact hm.symm.trans hmap
  have hlt₂ : 𝔭₁.comap (Ideal.Quotient.mk p) < 𝔭₂.comap (Ideal.Quotient.mk p) := by
    refine lt_of_le_of_ne (Ideal.comap_mono hlt.le) fun heq => ?_
    have hA := Ideal.map_comap_of_surjective (Ideal.Quotient.mk p)
      Ideal.Quotient.mk_surjective 𝔭₁
    have hB := Ideal.map_comap_of_surjective (Ideal.Quotient.mk p)
      Ideal.Quotient.mk_surjective 𝔭₂
    have hAB : 𝔭₁ = 𝔭₂ := by rw [← hA, ← hB, heq]
    exact absurd hAB (ne_of_lt hlt)
  -- `ringKrullDim R = 3`, so a chain of length two above `p` gives `p.height ≤ 1`
  have hdim : ringKrullDim (MvPolynomial (Fin 3) K) = 3 := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field]
    norm_num
  have ha1 : p.height + 1 ≤ (𝔭₁.comap (Ideal.Quotient.mk p)).height :=
    Ideal.height_add_one_le_of_lt_of_isPrime hlt₁
  have hb1 : (𝔭₁.comap (Ideal.Quotient.mk p)).height + 1
      ≤ (𝔭₂.comap (Ideal.Quotient.mk p)).height :=
    Ideal.height_add_one_le_of_lt_of_isPrime hlt₂
  have hc2 : (𝔭₂.comap (Ideal.Quotient.mk p)).height ≤ 3 := by
    have h := Ideal.height_le_ringKrullDim_of_isPrime (I := 𝔭₂.comap (Ideal.Quotient.mk p))
    rw [hdim] at h
    exact WithBot.coe_le_coe.mp h
  have hle : p.height ≤ 1 := by
    have key : p.height + (1 + 1) ≤ 1 + (1 + 1) := by
      calc p.height + (1 + 1) = (p.height + 1) + 1 := by rw [add_assoc]
        _ ≤ (𝔭₁.comap (Ideal.Quotient.mk p)).height + 1 := add_le_add ha1 le_rfl
        _ ≤ (𝔭₂.comap (Ideal.Quotient.mk p)).height := hb1
        _ ≤ 3 := hc2
        _ = 1 + (1 + 1) := by norm_num
    exact (ENat.add_le_add_iff_right (by norm_num : ((1 : ℕ∞) + 1) ≠ ⊤)).mp key
  -- `p ≠ ⊥`: otherwise the residue field would have transcendence degree three
  have hne_bot : p ≠ ⊥ := by
    intro hbot
    have hEq : Algebra.trdeg K (FractionRing (MvPolynomial (Fin 3) K ⧸ p))
        = Algebra.trdeg K (FractionRing (MvPolynomial (Fin 3) K)) := by
      rw [hbot]
      exact AlgEquiv.trdeg_eq (IsFractionRing.algEquivOfAlgEquiv
        (AlgEquiv.quotientBot K (MvPolynomial (Fin 3) K)))
    rw [htr, trdeg_fractionRing_mvPolynomial K 3, Cardinal.lift_mk_fin] at hEq
    norm_num at hEq
  have hge : (1 : ℕ∞) ≤ p.height := by
    rw [Order.one_le_iff_ne_zero]
    intro h0
    exact hne_bot (Ideal.height_eq_zero_iff_eq_bot.mp h0)
  exact le_antisymm hle hge

theorem azKerHeight {K : Type*} [Field K] (a b g : K)
    (h3 : Work.MotAS.azTheta a b g (Work.MotAS.fwVecAS2 a b g 3) ≠ 0)
    (h1 : Work.MotAS.azU K * Work.MotAS.azTheta a b g (Work.MotAS.fwVecAS2 a b g 3)
        = Work.MotAS.azTheta a b g (Work.MotAS.fwVecAS2 a b g 1))
    (h2 : Work.MotAS.azV K * Work.MotAS.azTheta a b g (Work.MotAS.fwVecAS2 a b g 3)
        = Work.MotAS.azTheta a b g (Work.MotAS.fwVecAS2 a b g 2)) :
    (RingHom.ker (Work.MotAS.azTheta a b g)).height = 1 := by
  -- the fraction field of the range of `θ` is `K(u,v)`
  obtain ⟨e⟩ := azFracRange a b g h3 h1 h2
  haveI : (RingHom.ker (azTheta a b g)).IsPrime := RingHom.ker_isPrime _
  -- transport to `Frac (K[x₀,x₁,x₂] ⧸ ker θ)`, the fraction field of `θ.range`
  have htrQ : Algebra.trdeg K
      (FractionRing (MvPolynomial (Fin 3) K ⧸ RingHom.ker (azTheta a b g))) = 2 := by
    have e2 : FractionRing (MvPolynomial (Fin 3) K ⧸ RingHom.ker (azTheta a b g)) ≃ₐ[K]
        FractionRing ↥((azTheta a b g).range) :=
      IsFractionRing.algEquivOfAlgEquiv (Ideal.quotientKerEquivRange (azTheta a b g))
    rw [AlgEquiv.trdeg_eq e2, AlgEquiv.trdeg_eq e, trdeg_ratFunc_ratFunc_eq_two]
  exact height_eq_one_of_trdeg_eq_two K (RingHom.ker (azTheta a b g)) htrQ

end Work.MotAS
