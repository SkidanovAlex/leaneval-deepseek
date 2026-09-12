import Mathlib
import Submission.Commons.Algebra.MvPolynomial.ringKrullDim_quotient_of_homogeneous_mprimary
import Submission.Commons.RingTheory.KrullDimension.ringKrullDim_eq_of_isIntegral

set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

namespace Commons.RingTheory.Ideal.Hilbert

open MvPolynomial

universe u

/-! ## Auxiliary lemmas -/

/-- The irrelevant ideal is proper (it is contained in the augmentation kernel). -/
lemma idealOfVars_ne_top {k : Type*} [Field k] {m : ℕ} :
    MvPolynomial.idealOfVars (Fin m) k ≠ ⊤ := by
  intro htop
  have hle : MvPolynomial.idealOfVars (Fin m) k ≤ RingHom.ker MvPolynomial.constantCoeff := by
    rw [MvPolynomial.idealOfVars, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    simp [RingHom.mem_ker]
  have : (1 : MvPolynomial (Fin m) k) ∈ RingHom.ker MvPolynomial.constantCoeff :=
    hle (htop ▸ Submodule.mem_top)
  simp [RingHom.mem_ker] at this

/-- Membership in the irrelevant ideal is to have vanishing constant term. -/
lemma mem_idealOfVars_iff_coeff_zero {σ : Type*} {K : Type*} [Field K] (x : MvPolynomial σ K) :
    x ∈ MvPolynomial.idealOfVars σ K ↔ MvPolynomial.coeff 0 x = 0 := by
  rw [MvPolynomial.idealOfVars,
    show Set.range (MvPolynomial.X) = MvPolynomial.X '' (Set.univ : Set σ) from by simp,
    MvPolynomial.mem_ideal_span_X_image]
  constructor
  · intro h
    by_contra hc
    have hm : (0 : σ →₀ ℕ) ∈ x.support := MvPolynomial.mem_support_iff.mpr hc
    obtain ⟨i, -, hi⟩ := h 0 hm
    exact hi (by simp)
  · intro h m hm
    have hm0 : m ≠ 0 := by
      rintro rfl
      exact (MvPolynomial.mem_support_iff.mp hm) h
    obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hm0
    exact ⟨i, Set.mem_univ i, hi⟩

/-- A homogeneous polynomial of positive degree lies in the irrelevant ideal. -/
lemma isHomogeneous_mem_idealOfVars {σ : Type*} {K : Type*} [Field K]
    {y : MvPolynomial σ K} {j : ℕ} (hy : y.IsHomogeneous j) (hj : 1 ≤ j) :
    y ∈ MvPolynomial.idealOfVars σ K := by
  rw [MvPolynomial.idealOfVars,
    show Set.range (MvPolynomial.X) = MvPolynomial.X '' (Set.univ : Set σ) from by simp,
    MvPolynomial.mem_ideal_span_X_image]
  intro m hm
  have hdeg : Finsupp.degree m = j := by
    by_contra hc
    exact (MvPolynomial.mem_support_iff.mp hm) (hy.coeff_eq_zero hc)
  have hm0 : m ≠ 0 := by
    intro h0
    have h0' : Finsupp.degree m = 0 := by rw [h0, Finsupp.degree_eq_zero_iff]
    omega
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hm0
  exact ⟨i, Set.mem_univ i, hi⟩

/-- The height of the image of a prime ideal in a quotient is at most its height. -/
theorem height_map_quotient_le {R : Type*} [CommRing R] {P Q : Ideal R} (hPQ : P ≤ Q) [Q.IsPrime] :
    (Q.map (Ideal.Quotient.mk P)).height ≤ Q.height := by
  haveI hprime : (Q.map (Ideal.Quotient.mk P)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hPQ)
  have hsm : StrictMono (PrimeSpectrum.comap (Ideal.Quotient.mk P)) :=
    RingHom.strictMono_comap_of_surjective (f := Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
  have hc : (PrimeSpectrum.comap (Ideal.Quotient.mk P))
      (⟨Q.map (Ideal.Quotient.mk P), hprime⟩ : PrimeSpectrum (R ⧸ P)) =
      (⟨Q, ‹Q.IsPrime›⟩ : PrimeSpectrum R) := by
    rw [PrimeSpectrum.ext_iff]
    show Ideal.comap (Ideal.Quotient.mk P) (Ideal.map (Ideal.Quotient.mk P) Q) = Q
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    exact sup_eq_left.mpr hPQ
  have h := Order.height_le_height_apply_of_strictMono
    (PrimeSpectrum.comap (Ideal.Quotient.mk P)) hsm
    (⟨Q.map (Ideal.Quotient.mk P), hprime⟩ : PrimeSpectrum (R ⧸ P))
  rw [hc] at h
  calc (Q.map (Ideal.Quotient.mk P)).height
      = Order.height (⟨Q.map (Ideal.Quotient.mk P), hprime⟩ : PrimeSpectrum (R ⧸ P)) := by
        rw [← PrimeSpectrum.height_eq_orderHeight]
    _ ≤ Order.height (⟨Q, ‹Q.IsPrime›⟩ : PrimeSpectrum R) := h
    _ = Q.height := by rw [← PrimeSpectrum.height_eq_orderHeight]

/-- Every maximal ideal of a polynomial ring over a field has height the number of variables. -/
theorem maximalIdeal_height_lower {k : Type u} [Field k] :
    ∀ (s : ℕ) (p : Ideal (MvPolynomial (Fin s) k)), p.IsMaximal → (s : ℕ∞) ≤ p.height := by
  intro s
  induction s with
  | zero => intro p hp; exact zero_le
  | succ s ih =>
    intro p hp
    let e := (MvPolynomial.finSuccEquiv k s).toRingEquiv
    let P : Ideal (Polynomial (MvPolynomial (Fin s) k)) := p.map e
    haveI hp' : p.IsMaximal := hp
    haveI hP : P.IsMaximal := Ideal.map_isMaximal_of_equiv e
    haveI hc : (Ideal.comap Polynomial.C P).IsMaximal := Polynomial.isMaximal_comap_C_of_isJacobsonRing P
    haveI hlie : P.LiesOver (Ideal.comap Polynomial.C P) := Ideal.LiesOver.mk rfl
    have h1 : P.height = (Ideal.comap Polynomial.C P).height + 1 :=
      Polynomial.height_eq_height_add_one _ P
    have h2 : (s : ℕ∞) ≤ (Ideal.comap Polynomial.C P).height := ih _ hc
    have h3 : ((s + 1 : ℕ) : ℕ∞) ≤ P.height := by
      have h3a : ((s : ℕ∞) + 1) ≤ P.height := by
        rw [h1]; exact add_le_add h2 le_rfl
      have hs1 : ((s + 1 : ℕ) : ℕ∞) = (s : ℕ∞) + 1 := by push_cast; ring
      rwa [hs1]
    have h4 : (p.map e).height = p.height := RingEquiv.height_map e p
    rw [← h4]
    exact h3

theorem maximalIdeal_height_eq_card {k : Type u} [Field k] {s : ℕ}
    (p : Ideal (MvPolynomial (Fin s) k)) [p.IsMaximal] : p.height = (s : ℕ∞) := by
  refine le_antisymm ?_ (maximalIdeal_height_lower s p ‹p.IsMaximal›)
  have h := Ideal.height_le_ringKrullDim_of_isPrime (I := p)
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add,
    Nat.card_eq_fintype_card, Fintype.card_fin] at h
  exact WithBot.coe_le_coe.mp h

/-- In a finitely generated domain over a field, every maximal ideal has height the Krull
dimension. -/
theorem fg_domain_maximalIdeal_height_eq_ringKrullDim {k B : Type*} [Field k] [CommRing B]
    [IsDomain B] [Algebra k B] [Algebra.FiniteType k B] (n : Ideal B) [n.IsMaximal] :
    (n.height : WithBot ℕ∞) = ringKrullDim B := by
  obtain ⟨s, g, hg_inj, hg_fin⟩ := exists_finite_inj_algHom_of_fg k B
  letI : Algebra (MvPolynomial (Fin s) k) B := g.toRingHom.toAlgebra
  have hmap : algebraMap (MvPolynomial (Fin s) k) B = g.toRingHom := rfl
  haveI : Module.Finite (MvPolynomial (Fin s) k) B := hg_fin
  haveI : IsScalarTower k (MvPolynomial (Fin s) k) B :=
    IsScalarTower.of_algebraMap_eq fun x => (g.commutes x).symm
  haveI : Algebra.IsIntegral (MvPolynomial (Fin s) k) B := Algebra.IsIntegral.of_finite _ _
  haveI : FaithfulSMul (MvPolynomial (Fin s) k) B :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (by rw [hmap]; exact hg_inj)
  let p' : Ideal (MvPolynomial (Fin s) k) := n.comap (algebraMap (MvPolynomial (Fin s) k) B)
  haveI hp'max : p'.IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal n
  have hp'height : p'.height = (s : ℕ∞) := maximalIdeal_height_eq_card (s := s) p'
  have hdimB : ringKrullDim B = (s : WithBot ℕ∞) := by
    rw [Commons.RingTheory.KrullDimension.ringKrullDim_eq_of_isIntegral
        (by rw [hmap]; exact hg_inj),
      MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add,
      Nat.card_eq_fintype_card, Fintype.card_fin]
  refine le_antisymm (Ideal.height_le_ringKrullDim_of_isPrime (I := n)) ?_
  rw [hdimB]
  haveI : p'.FiniteHeight := ⟨Or.inr (by rw [hp'height]; exact ENat.natCast_ne_top s)⟩
  obtain ⟨l, hlast, hlen⟩ := Ideal.exists_ltSeries_length_eq_height p'
  have hls : l.length = s := by
    rw [hp'height] at hlen
    exact Nat.cast_injective hlen
  haveI : n.LiesOver (RelSeries.last l).asIdeal := by
    rw [hlast]
    exact Ideal.LiesOver.mk rfl
  obtain ⟨L, hLlen, hLlast, -⟩ := Ideal.exists_ltSeries_of_hasGoingDown l n
  have hfin : L.length ≤ n.height := by
    calc L.length ≤ Order.height (RelSeries.last L) := Order.length_le_height_last (p := L)
      _ = Order.height (⟨n, ‹n.IsMaximal›.isPrime⟩ : PrimeSpectrum B) := by rw [hLlast]
      _ = n.height := by rw [← PrimeSpectrum.height_eq_orderHeight]
  rw [hLlen, hls] at hfin
  exact_mod_cast hfin

noncomputable section
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Minimal primes of a homogeneous ideal are contained in the irrelevant ideal. -/
theorem minimalPrimes_le_idealOfVars {k : Type} [Field k] {m : ℕ}
    (J : Ideal (MvPolynomial (Fin m) k))
    (hJ : ∀ x ∈ J, ∀ j, MvPolynomial.homogeneousComponent j x ∈ J)
    {p : Ideal (MvPolynomial (Fin m) k)} (hp : p ∈ J.minimalPrimes) :
    p ≤ MvPolynomial.idealOfVars (Fin m) k := by
  classical
  haveI hpp : p.IsPrime := hp.1.1
  have hJhom : J.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin m) k) := by
    rw [Ideal.IsHomogeneous.iff_eq]
    refine le_antisymm (Ideal.toIdeal_homogeneousCore_le _ J) ?_
    intro x hx
    rw [← MvPolynomial.sum_homogeneousComponent x]
    refine Ideal.sum_mem _ fun i hi => ?_
    exact Ideal.mem_homogeneousCore_of_homogeneous_of_mem
      ⟨i, MvPolynomial.homogeneousComponent_mem i x⟩ (hJ x hx i)
  have hphom : p.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin m) k) := by
    rw [Ideal.IsHomogeneous.iff_eq]
    refine le_antisymm (Ideal.toIdeal_homogeneousCore_le _ p) ?_
    have hqprime :
        ((Ideal.homogeneousCore (MvPolynomial.homogeneousSubmodule (Fin m) k) p).toIdeal).IsPrime :=
      Ideal.IsPrime.homogeneousCore hpp
    have hJle_hc : J ≤
        (Ideal.homogeneousCore (MvPolynomial.homogeneousSubmodule (Fin m) k) p).toIdeal := by
      rw [← Ideal.IsHomogeneous.toIdeal_homogeneousCore_eq_self hJhom]
      exact (Ideal.homogeneousCore.gc (MvPolynomial.homogeneousSubmodule (Fin m) k)).monotone_l
        (Ideal.homogeneousCore_mono _ hp.1.2)
    exact hp.2 ⟨hqprime, hJle_hc⟩ (Ideal.toIdeal_homogeneousCore_le _ p)
  intro x hx
  rw [mem_idealOfVars_iff_coeff_zero]
  have hxmem : ∀ n, MvPolynomial.homogeneousComponent n x ∈ p :=
    (MvPolynomial.mem_iff_homogeneousComponent_mem (I := p) hphom x).mp hx
  have h0 : MvPolynomial.C (MvPolynomial.coeff 0 x) ∈ p := by
    rw [← MvPolynomial.homogeneousComponent_zero]
    exact hxmem 0
  by_contra hne
  have h1 : (1 : MvPolynomial (Fin m) k) ∈ p := by
    have hmem := p.mul_mem_left (MvPolynomial.C (MvPolynomial.coeff 0 x)⁻¹) h0
    rwa [← MvPolynomial.C_mul, inv_mul_cancel₀ hne, MvPolynomial.C_1] at hmem
  exact hpp.ne_top ((Ideal.eq_top_iff_one p).mpr h1)

end

theorem ringKrullDim_quotient_eq_height_idealOfVars {k : Type} [Field k] {m : ℕ}
    (J : Ideal (MvPolynomial (Fin m) k))
    (hJ : ∀ x ∈ J, ∀ j, MvPolynomial.homogeneousComponent j x ∈ J)
    (hJle : J ≤ MvPolynomial.idealOfVars (Fin m) k) :
    ringKrullDim (MvPolynomial (Fin m) k ⧸ J) =
      ((MvPolynomial.idealOfVars (Fin m) k).map (Ideal.Quotient.mk J)).height := by
  classical
  have hn_eq : MvPolynomial.idealOfVars (Fin m) k = RingHom.ker MvPolynomial.constantCoeff := by
    ext x
    rw [RingHom.mem_ker, mem_idealOfVars_iff_coeff_zero, MvPolynomial.constantCoeff_eq]
  have hnprime : (MvPolynomial.idealOfVars (Fin m) k).IsPrime := by
    rw [hn_eq]; exact RingHom.ker_isPrime _
  haveI hnmax : (MvPolynomial.idealOfVars (Fin m) k).IsMaximal := by
    rw [hn_eq]
    exact RingHom.ker_isMaximal_of_surjective MvPolynomial.constantCoeff
      (fun x => ⟨MvPolynomial.C x, by simp⟩)
  haveI hnAmax : ((MvPolynomial.idealOfVars (Fin m) k).map (Ideal.Quotient.mk J)).IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
      (by rw [Ideal.mk_ker]; exact hJle)
  haveI hnAprime : ((MvPolynomial.idealOfVars (Fin m) k).map (Ideal.Quotient.mk J)).IsPrime :=
    hnAmax.isPrime
  refine le_antisymm ?_ (Ideal.height_le_ringKrullDim_of_isPrime (I := _))
  rw [ringKrullDim_le_iff_height_le]
  intro Q hQ
  rw [WithBot.coe_le_coe]
  rw [show Q.height = Order.height (⟨Q, hQ⟩ : PrimeSpectrum (MvPolynomial (Fin m) k ⧸ J)) from
      PrimeSpectrum.height_eq_orderHeight (⟨Q, hQ⟩ : PrimeSpectrum (MvPolynomial (Fin m) k ⧸ J))]
  apply Order.height_le
  intro l hl
  obtain ⟨P, hP, hPle⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal (MvPolynomial (Fin m) k ⧸ J)))
    (J := (l.toFun 0).asIdeal) bot_le
  have hPprime : P.IsPrime := hP.1.1
  haveI hPprimeI : P.IsPrime := hPprime
  have hp_mem : P.comap (Ideal.Quotient.mk J) ∈ J.minimalPrimes := by
    have h := Ideal.minimalPrimes_comap_of_surjective (f := Ideal.Quotient.mk J)
      Ideal.Quotient.mk_surjective hP
    rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker] at h
    exact h
  have hP_le_nA : P ≤ (MvPolynomial.idealOfVars (Fin m) k).map (Ideal.Quotient.mk J) := by
    rw [← Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective P]
    exact Ideal.map_mono (minimalPrimes_le_idealOfVars J hJ hp_mem)
  haveI : Algebra.FiniteType k (MvPolynomial (Fin m) k ⧸ J) := Algebra.FiniteType.quotient k J
  haveI : Algebra.FiniteType k ((MvPolynomial (Fin m) k ⧸ J) ⧸ P) :=
    Algebra.FiniteType.quotient k P
  haveI : (((MvPolynomial.idealOfVars (Fin m) k).map (Ideal.Quotient.mk J)).map
      (Ideal.Quotient.mk P)).IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
      (by rw [Ideal.mk_ker]; exact hP_le_nA)
  have hchain := Commons.Algebra.MvPolynomial.LTSeries_length_le_ringKrullDim_quotient l hPle
  have hM := fg_domain_maximalIdeal_height_eq_ringKrullDim (k := k)
    (B := (MvPolynomial (Fin m) k ⧸ J) ⧸ P)
    (n := ((MvPolynomial.idealOfVars (Fin m) k).map (Ideal.Quotient.mk J)).map (Ideal.Quotient.mk P))
  rw [← hM] at hchain
  have hchain' : l.length ≤ (((MvPolynomial.idealOfVars (Fin m) k).map
      (Ideal.Quotient.mk J)).map (Ideal.Quotient.mk P)).height := WithBot.coe_le_coe.mp hchain
  exact hchain'.trans (height_map_quotient_le hP_le_nA)

end Commons.RingTheory.Ideal.Hilbert
