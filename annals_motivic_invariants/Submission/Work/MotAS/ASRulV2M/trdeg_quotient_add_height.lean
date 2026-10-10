import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option linter.style.haveILetI false

namespace Work.MotAS.ASRulV2M

universe u

/-- If `f : R →+* S` is a surjective ring homomorphism with `S` a domain, then `Spec S` sits
(contravariantly, via `comap f`) as the upper set of primes of `R` containing `ker f`, so
`dim S = coheight (ker f)`.  We only need the inequality. -/
private theorem coheight_bot_le_coheight_ker {R S : Type*} [CommRing R] [CommRing S] [IsDomain S]
    (f : R →+* S) (hf : Function.Surjective f) :
    Order.coheight (⊥ : PrimeSpectrum S)
      ≤ Order.coheight (⟨RingHom.ker f, RingHom.ker_isPrime f⟩ : PrimeSpectrum R) := by
  have hmono : Monotone (PrimeSpectrum.comap f) := fun _ _ hab => Ideal.comap_mono hab
  have hinj : Function.Injective (PrimeSpectrum.comap f) := by
    intro x y hxy
    refine PrimeSpectrum.ext (Ideal.comap_injective_of_surjective f hf ?_)
    simpa only [PrimeSpectrum.comap_asIdeal] using congrArg PrimeSpectrum.asIdeal hxy
  have hstrict : StrictMono (PrimeSpectrum.comap f) := hmono.strictMono_of_injective hinj
  have hbot : PrimeSpectrum.comap f (⊥ : PrimeSpectrum S)
      = (⟨RingHom.ker f, RingHom.ker_isPrime f⟩ : PrimeSpectrum R) := by
    apply PrimeSpectrum.ext
    rw [PrimeSpectrum.comap_asIdeal, PrimeSpectrum.asIdeal_bot]
    exact (RingHom.ker_eq_comap_bot f).symm
  have h := Order.coheight_le_coheight_apply_of_strictMono (PrimeSpectrum.comap f) hstrict
    (⊥ : PrimeSpectrum S)
  rwa [hbot] at h

/-- For a finitely generated domain `A` over a field `K`, the transcendence degree of its fraction
field is a natural number `s`, and `Spec A` carries a chain of primes of length `s` starting at the
zero ideal: Noether normalisation writes `A` as a finite extension of `K[T₁,…,T_s]`, and the chain
`(T₁) ⊆ (T₁,T₂) ⊆ ⋯` lifts along the integral extension. -/
private theorem trdeg_eq_natCast_and_chain {K A : Type u} [Field K] [CommRing A] [IsDomain A]
    [Algebra K A] [Algebra.FiniteType K A] :
    ∃ s : ℕ, Algebra.trdeg K (FractionRing A) = (s : Cardinal) ∧
      (s : ℕ∞) ≤ Order.coheight (⊥ : PrimeSpectrum A) := by
  classical
  obtain ⟨s, g, hg_inj, hg_fin⟩ := exists_finite_inj_algHom_of_fg K A
  letI : Algebra (MvPolynomial (Fin s) K) A := g.toRingHom.toAlgebra
  haveI hFin : Module.Finite (MvPolynomial (Fin s) K) A := hg_fin
  have hinj : Function.Injective (algebraMap (MvPolynomial (Fin s) K) A) := by
    show Function.Injective (g : MvPolynomial (Fin s) K → A)
    exact hg_inj
  haveI hFaith : FaithfulSMul (MvPolynomial (Fin s) K) A :=
    (faithfulSMul_iff_algebraMap_injective (MvPolynomial (Fin s) K) A).mpr hinj
  haveI hInt : Algebra.IsIntegral (MvPolynomial (Fin s) K) A :=
    Algebra.IsIntegral.of_finite _ _
  -- the transcendence degree is `s`
  have htrA : Algebra.trdeg K (FractionRing A) = Algebra.trdeg K A := by
    haveI : Algebra.IsAlgebraic A (FractionRing A) :=
      (IsFractionRing.comap_isAlgebraic_iff (A := A) (K := FractionRing A)
        (C := FractionRing A)).mpr inferInstance
    have hh := trdeg_add_eq K A (A := FractionRing A)
    have hz : Algebra.trdeg A (FractionRing A) = 0 := trdeg_eq_zero
    rw [hz, add_zero] at hh
    exact hh.symm
  have htrB : Algebra.trdeg K A = Algebra.trdeg K (MvPolynomial (Fin s) K) := by
    have hh := trdeg_add_eq K (MvPolynomial (Fin s) K) (A := A)
    have hz : Algebra.trdeg (MvPolynomial (Fin s) K) A = 0 := trdeg_eq_zero
    rw [hz, add_zero] at hh
    exact hh.symm
  have htr : Algebra.trdeg K (FractionRing A) = (s : Cardinal) := by
    rw [htrA, htrB, MvPolynomial.trdeg_of_isDomain, Cardinal.mk_fin, Cardinal.lift_natCast]
  refine ⟨s, htr, ?_⟩
  -- the polynomial ring `K[T₁,…,T_s]` has a chain of primes of length `s` above `⊥`
  have hdimB : Order.krullDim (PrimeSpectrum (MvPolynomial (Fin s) K)) = (s : WithBot ℕ∞) := by
    change ringKrullDim (MvPolynomial (Fin s) K) = (s : WithBot ℕ∞)
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field,
      zero_add, Nat.card_fin]
  have hcoB : (s : ℕ∞) ≤ Order.coheight (⊥ : PrimeSpectrum (MvPolynomial (Fin s) K)) := by
    have h2 : (↑(Order.coheight (⊥ : PrimeSpectrum (MvPolynomial (Fin s) K))) : WithBot ℕ∞)
        = (s : WithBot ℕ∞) := by
      rw [Order.coheight_bot_eq_krullDim, hdimB]
    exact (WithBot.coe_inj.mp h2).ge
  obtain ⟨l, hlhead, hllen⟩ :=
    Order.exists_series_of_le_coheight (⊥ : PrimeSpectrum (MvPolynomial (Fin s) K)) hcoB
  -- lift the chain along the integral extension `K[T₁,…,T_s] → A`
  have hker : RingHom.ker (algebraMap (MvPolynomial (Fin s) K) A) = ⊥ :=
    (RingHom.injective_iff_ker_eq_bot _).mp hinj
  have hlies : (⊥ : Ideal A).LiesOver (l.head).asIdeal := by
    rw [Ideal.liesOver_iff, hlhead, PrimeSpectrum.asIdeal_bot, Ideal.under_def]
    exact hker.symm.trans (RingHom.ker_eq_comap_bot (algebraMap (MvPolynomial (Fin s) K) A))
  haveI : (⊥ : Ideal A).LiesOver (l.head).asIdeal := hlies
  obtain ⟨L, hLlen, hLhead, -⟩ :=
    Ideal.exists_ltSeries_of_hasGoingUp (R := MvPolynomial (Fin s) K) (S := A) l (⊥ : Ideal A)
  have hhead : L.head = (⊥ : PrimeSpectrum A) := by
    rw [hLhead]
    exact PrimeSpectrum.ext rfl
  have h := Order.length_le_coheight_head (p := L)
  rw [hLlen, hllen, hhead] at h
  exact h

/-- The dimension formula for a prime ideal of a polynomial ring over a field: the transcendence
degree of the residue field plus the height of the prime is at most the number of variables.

`A := K[X₀,…,X_{n-1}] ⧸ P` is a finitely generated domain over `K`, so (Noether normalisation,
`trdeg_eq_natCast_and_chain`) its transcendence degree over `K` is a natural number `s` and there is
a chain of primes of `A` of length `s` above `⊥`; pulled back to the polynomial ring this is a chain
of primes above `P` of length `s`, i.e. `s ≤ coheight P`.  Since also `m ≤ height P`, we get
`m + s ≤ height P + coheight P ≤ dim K[X₀,…,X_{n-1}] = n`. -/
theorem trdeg_quotient_add_height {K : Type*} [Field K] (n : ℕ)
    (P : Ideal (MvPolynomial (Fin n) K)) [P.IsPrime] (m : ℕ) (hm : m ≤ P.height) :
    Algebra.trdeg K (FractionRing (MvPolynomial (Fin n) K ⧸ P)) + (m : Cardinal) ≤ (n : Cardinal) := by
  classical
  have hPp : P.IsPrime := inferInstance
  let A := MvPolynomial (Fin n) K ⧸ P
  haveI hAdom : IsDomain A := Ideal.Quotient.isDomain P
  haveI hAft : Algebra.FiniteType K A := Algebra.FiniteType.quotient K P
  -- Noether normalisation: the transcendence degree is a natural number, and realised by a chain.
  obtain ⟨s, htr, hchain⟩ := trdeg_eq_natCast_and_chain (K := K) (A := A)
  -- Pulling the chain of `A` back to the polynomial ring gives `coheight P ≥ s`.
  have hspec : (⟨RingHom.ker (Ideal.Quotient.mk P),
        RingHom.ker_isPrime (Ideal.Quotient.mk P)⟩ : PrimeSpectrum (MvPolynomial (Fin n) K))
      = ⟨P, hPp⟩ := PrimeSpectrum.ext Ideal.mk_ker
  have hcoR : (s : ℕ∞) ≤
      Order.coheight (⟨P, hPp⟩ : PrimeSpectrum (MvPolynomial (Fin n) K)) := by
    have h := coheight_bot_le_coheight_ker (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
    rw [hspec] at h
    exact hchain.trans h
  -- and `m ≤ height P`.
  have hheight : (m : ℕ∞) ≤
      Order.height (⟨P, hPp⟩ : PrimeSpectrum (MvPolynomial (Fin n) K)) := by
    rw [← PrimeSpectrum.height_eq_orderHeight
      (⟨P, hPp⟩ : PrimeSpectrum (MvPolynomial (Fin n) K))]
    exact hm
  -- the ambient polynomial ring has Krull dimension `n`.
  have hkr : Order.krullDim (PrimeSpectrum (MvPolynomial (Fin n) K)) = (n : WithBot ℕ∞) := by
    change ringKrullDim (MvPolynomial (Fin n) K) = (n : WithBot ℕ∞)
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field,
      zero_add, Nat.card_fin]
  haveI : Nonempty (PrimeSpectrum (MvPolynomial (Fin n) K)) := ⟨⟨P, hPp⟩⟩
  have hsum : Order.height (⟨P, hPp⟩ : PrimeSpectrum (MvPolynomial (Fin n) K))
      + Order.coheight (⟨P, hPp⟩ : PrimeSpectrum (MvPolynomial (Fin n) K)) ≤ (n : ℕ∞) := by
    have h1 : (↑(Order.height (⟨P, hPp⟩ : PrimeSpectrum (MvPolynomial (Fin n) K))
        + Order.coheight (⟨P, hPp⟩ : PrimeSpectrum (MvPolynomial (Fin n) K))) : WithBot ℕ∞)
        ≤ (n : WithBot ℕ∞) := by
      rw [← hkr, Order.krullDim_eq_iSup_height_add_coheight_of_nonempty
        (α := PrimeSpectrum (MvPolynomial (Fin n) K))]
      exact WithBot.coe_le_coe.mpr
        (le_iSup (fun a : PrimeSpectrum (MvPolynomial (Fin n) K) =>
          Order.height a + Order.coheight a) ⟨P, hPp⟩)
    exact WithBot.coe_le_coe.mp h1
  have hsnm : s + m ≤ n := by
    have h1 : (s : ℕ∞) + (m : ℕ∞) ≤ (n : ℕ∞) :=
      calc (s : ℕ∞) + (m : ℕ∞) = (m : ℕ∞) + (s : ℕ∞) := add_comm _ _
        _ ≤ Order.height (⟨P, hPp⟩ : PrimeSpectrum (MvPolynomial (Fin n) K))
            + Order.coheight (⟨P, hPp⟩ : PrimeSpectrum (MvPolynomial (Fin n) K)) :=
              add_le_add hheight hcoR
        _ ≤ (n : ℕ∞) := hsum
    have h2 : ((s + m : ℕ) : ℕ∞) ≤ ((n : ℕ) : ℕ∞) := h1
    exact ENat.natCast_le_natCast.mp h2
  change Algebra.trdeg K (FractionRing A) + (m : Cardinal) ≤ (n : Cardinal)
  rw [htr]
  have hcast : ((s + m : ℕ) : Cardinal) = (s : Cardinal) + (m : Cardinal) := Nat.cast_add s m
  rw [← hcast]
  exact Nat.cast_le.mpr hsnm

end Work.MotAS.ASRulV2M
