import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Submission.Commons.RingTheory.KrullDimension.ringKrullDim_eq_of_isIntegral
import Submission.Commons.RingTheory.Trdeg.trdeg_fractionRing_mvPolynomial

open Polynomial
universe u
set_option linter.style.haveILetI false
set_option linter.style.emptyLine false
namespace Commons.RingTheory.KrullDimension

-- (from the earlier scratch file, correctly proved)
theorem exists_ringKrullDim_eq_and_trdeg_eq (K : Type u) [Field K] (A : Type u) [CommRing A]
    [IsDomain A] [Algebra K A] [Algebra.FiniteType K A] :
    ∃ s : ℕ, Algebra.trdeg K A = (s : Cardinal) ∧ ringKrullDim A = (s : WithBot ℕ∞) := by
  obtain ⟨s, g, hg, hfin⟩ := exists_finite_inj_algHom_of_fg K A
  letI : Algebra (MvPolynomial (Fin s) K) A := g.toRingHom.toAlgebra
  haveI : IsScalarTower K (MvPolynomial (Fin s) K) A :=
    IsScalarTower.of_algebraMap_eq fun x => (g.commutes x).symm
  haveI : Module.Finite (MvPolynomial (Fin s) K) A := hfin
  haveI : FaithfulSMul (MvPolynomial (Fin s) K) A :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hg
  haveI : Algebra.IsIntegral (MvPolynomial (Fin s) K) A := Algebra.IsIntegral.of_finite _ _
  refine ⟨s, ?_, ?_⟩
  · have h1 : Algebra.trdeg (MvPolynomial (Fin s) K) A = 0 :=
      trdeg_eq_zero_iff.mpr Algebra.IsIntegral.isAlgebraic
    have h2 := trdeg_add_eq K (MvPolynomial (Fin s) K) (A := A)
    rw [h1, add_zero] at h2
    rw [← h2, MvPolynomial.trdeg_of_isDomain, Cardinal.lift_mk_fin]
  · have hdim : ringKrullDim A = ringKrullDim (MvPolynomial (Fin s) K) :=
      ringKrullDim_eq_of_isIntegral hg
    rw [hdim, MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field,
      zero_add, Nat.card_eq_fintype_card, Fintype.card_fin]

section
attribute [local instance] Polynomial.algebra

theorem height_eq_one_of_isPrime_ne_bot_of_comap_C_eq_bot {B : Type*} [CommRing B] [IsDomain B]
    (Q : Ideal B[X]) [Q.IsPrime] (hQ : Q.comap (Polynomial.C : B →+* B[X]) = ⊥) (hne : Q ≠ ⊥) :
    Q.height = 1 := by
  set M : Submonoid B[X] := (nonZeroDivisors B).map (Polynomial.C : B →+* B[X]) with hM
  haveI : IsLocalization M (FractionRing B)[X] :=
    Polynomial.isLocalization (nonZeroDivisors B) (FractionRing B)
  have hdisj : Disjoint (M : Set B[X]) (Q : Set B[X]) := by
    rw [Set.disjoint_left]
    intro x hxM hxQ
    obtain ⟨b, hb, rfl⟩ := hxM
    have hb1 : b ∈ Q.comap (Polynomial.C : B →+* B[X]) := by
      rw [Ideal.mem_comap]; exact hxQ
    rw [hQ] at hb1
    simp only [Ideal.mem_bot] at hb1
    exact one_ne_zero ((mem_nonZeroDivisors_iff.mp hb).1 1 (by rw [hb1, zero_mul]))
  rw [← IsLocalization.height_map_of_disjoint M Q (S := (FractionRing B)[X]) hdisj]
  haveI hQ' : (Q.map (algebraMap B[X] (FractionRing B)[X])).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint M (FractionRing B)[X] Q inferInstance hdisj
  have hne' : Q.map (algebraMap B[X] (FractionRing B)[X]) ≠ ⊥ := by
    have hinj : Function.Injective (algebraMap B[X] (FractionRing B)[X]) := by
      rw [show (algebraMap B[X] (FractionRing B)[X]) =
        Polynomial.mapRingHom (algebraMap B (FractionRing B)) from rfl]
      exact Polynomial.map_injective _ (IsLocalization.injective (FractionRing B) le_rfl)
    intro h
    exact hne ((Ideal.map_eq_bot_iff_of_injective (I := Q) hinj).mp h)
  haveI : (Q.map (algebraMap B[X] (FractionRing B)[X])).IsMaximal := hQ'.isMaximal hne'
  exact IsPrincipalIdealRing.height_eq_one_of_isMaximal _
    (Polynomial.not_isField (FractionRing B))

theorem ringKrullDim_quotient_polynomial_eq_of_comap_C_eq_bot {K : Type u} [Field K] {B : Type u}
    [CommRing B] [IsDomain B] [Algebra K B] [Algebra.FiniteType K B]
    (Q : Ideal B[X]) [Q.IsPrime] (hQ : Q.comap (Polynomial.C : B →+* B[X]) = ⊥) (hne : Q ≠ ⊥) :
    ringKrullDim (B[X] ⧸ Q) = ringKrullDim B := by
  set x : B[X] ⧸ Q := Ideal.Quotient.mk Q Polynomial.X with hx_def
  have haeval : Polynomial.aeval x = Ideal.Quotient.mkₐ B Q := by
    apply Polynomial.algHom_ext
    rw [Polynomial.aeval_X, Ideal.Quotient.mkₐ_eq_mk]
  have hx : IsAlgebraic B x := by
    rw [isAlgebraic_iff_not_injective]
    intro hinj
    obtain ⟨f, hfQ, hfne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    refine hfne ?_
    have h0 : Polynomial.aeval x f = 0 := by
      rw [haeval, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem.mpr hfQ]
    exact hinj (by rw [h0, map_zero])
  have hTop : Algebra.adjoin B {x} = ⊤ := by
    have h1 : (Algebra.adjoin B {(Polynomial.X : B[X])}).map (Ideal.Quotient.mkₐ B Q)
        = Algebra.adjoin B {x} := AlgHom.map_adjoin_singleton _ _
    rw [← h1, Polynomial.adjoin_X (R := B), Algebra.map_top]
    exact (AlgHom.range_eq_top _).mpr (Ideal.Quotient.mkₐ_surjective B Q)
  have halg : Algebra.IsAlgebraic B (B[X] ⧸ Q) := by
    rw [Algebra.isAlgebraic_def]
    intro y
    have hle : Algebra.adjoin B {x} ≤ Subalgebra.algebraicClosure B (B[X] ⧸ Q) := by
      rw [Algebra.adjoin_le_iff]
      rintro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact (Subalgebra.mem_algebraicClosure B (B[X] ⧸ Q)).mpr hx
    exact (Subalgebra.mem_algebraicClosure B (B[X] ⧸ Q)).mp
      (hle (by rw [hTop]; trivial))
  obtain ⟨s, hs, hdim⟩ := exists_ringKrullDim_eq_and_trdeg_eq K (B[X] ⧸ Q)
  obtain ⟨t, ht, hdimt⟩ := exists_ringKrullDim_eq_and_trdeg_eq K B
  have hst : s = t := by
    have htr : Algebra.trdeg K (B[X] ⧸ Q) = Algebra.trdeg K B := by
      have hinj : Function.Injective (algebraMap B (B[X] ⧸ Q)) := by
        intro a b hab
        have hQa : Polynomial.C (a - b) ∈ Q := by
          refine Ideal.Quotient.eq_zero_iff_mem.mp ?_
          change (algebraMap B (B[X] ⧸ Q)) (a - b) = 0
          rw [map_sub, hab, sub_self]
        have hmem : a - b ∈ Q.comap (Polynomial.C : B →+* B[X]) := by
          rw [Ideal.mem_comap]; exact hQa
        rw [hQ] at hmem
        exact sub_eq_zero.mp hmem
      haveI : FaithfulSMul B (B[X] ⧸ Q) :=
        ⟨fun {m₁ m₂} h => hinj (by simpa [Algebra.algebraMap_eq_smul_one] using h 1)⟩
      have h0 : Algebra.trdeg B (B[X] ⧸ Q) = 0 := trdeg_eq_zero_iff.mpr halg
      have h2 := trdeg_add_eq K B (A := B[X] ⧸ Q)
      rw [h0, add_zero] at h2
      exact h2.symm
    rw [hs, ht] at htr
    exact Nat.cast_injective htr
  rw [hdim, hdimt, hst]


/-- The one-step dimension/height formula: for a prime `P` of `A[X]` over a finitely generated
domain `A` over a field, `ht(P) + dim(A[X]/P) = ht(P ∩ A) + dim(A/(P ∩ A)) + 1`. -/
theorem height_add_ringKrullDim_quotient_polynomial {K : Type u} [Field K] {A : Type u}
    [CommRing A] [IsDomain A] [Algebra K A] [Algebra.FiniteType K A]
    (P : Ideal (Polynomial A)) [P.IsPrime] :
    P.height + ringKrullDim (Polynomial A ⧸ P) =
      (P.comap (Polynomial.C : A →+* Polynomial A)).height +
        ringKrullDim (A ⧸ P.comap (Polynomial.C : A →+* Polynomial A)) + 1 := by
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing K A
  set q : Ideal A := P.comap (Polynomial.C : A →+* Polynomial A) with hqdef
  haveI hqprime : q.IsPrime := hqdef ▸ Ideal.IsPrime.comap (Polynomial.C : A →+* Polynomial A)
  set I : Ideal (Polynomial A) := q.map (Polynomial.C : A →+* Polynomial A) with hIdef
  have hle : I ≤ P := by rw [hIdef, Ideal.map_le_iff_le_comap, hqdef]
  have hIker : RingHom.ker (Polynomial.mapRingHom (Ideal.Quotient.mk q)) = I := by
    rw [Polynomial.ker_mapRingHom, Ideal.mk_ker]
  set e : Polynomial (A ⧸ q) ≃+* (Polynomial A ⧸ I) :=
    Ideal.polynomialQuotientEquivQuotientPolynomial q with hedef
  set Pb : Ideal (Polynomial A ⧸ I) := P.map (Ideal.Quotient.mk I) with hPbdef
  haveI hPbprime : Pb.IsPrime := hPbdef ▸ Ideal.isPrime_map_quotientMk_of_isPrime hle
  set g : Polynomial (A ⧸ q) →+* (Polynomial A ⧸ P) :=
    (DoubleQuot.quotQuotEquivQuotOfLE hle).toRingHom.comp
      ((Ideal.Quotient.mk Pb).comp (e : Polynomial (A ⧸ q) →+* (Polynomial A ⧸ I))) with hgdef
  set Q : Ideal (Polynomial (A ⧸ q)) := RingHom.ker g with hQdef
  haveI hQprime : Q.IsPrime := hQdef ▸ RingHom.ker_isPrime g
  have hgsurj : Function.Surjective g := by
    rw [hgdef]
    exact (DoubleQuot.quotQuotEquivQuotOfLE hle).surjective.comp
      ((Ideal.Quotient.mk_surjective).comp e.surjective)
  have hker : Q = Pb.comap (e : Polynomial (A ⧸ q) →+* (Polynomial A ⧸ I)) := by
    have h1 : g = ((DoubleQuot.quotQuotEquivQuotOfLE hle).toRingHom.comp
        (Ideal.Quotient.mk Pb)).comp (e : Polynomial (A ⧸ q) →+* (Polynomial A ⧸ I)) := by
      rw [hgdef, RingHom.comp_assoc]
    rw [hQdef, h1, ← RingHom.comap_ker]
    congr 1
    rw [← RingHom.comap_ker,
      show (DoubleQuot.quotQuotEquivQuotOfLE hle).toRingHom =
        ((DoubleQuot.quotQuotEquivQuotOfLE hle : _ ≃+* _) : _ →+* _) from rfl,
      RingHom.ker_coe_equiv, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
  have hQheight : Q.height = Pb.height := by
    rw [hker]; exact RingEquiv.height_comap e Pb
  haveI hliesover : P.LiesOver q := Ideal.LiesOver.mk (by rw [hqdef, Ideal.under_def, Polynomial.algebraMap_eq])
  have hPheight : P.height = q.height + Pb.height := by
    have h := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (R := A) (S := Polynomial A) q P
    simpa [hPbdef, hIdef] using h
  have hdim : ringKrullDim (Polynomial (A ⧸ q) ⧸ Q) = ringKrullDim (Polynomial A ⧸ P) := by
    rw [hQdef]
    exact ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivOfSurjective hgsurj)
  have hQcomap : Q.comap (Polynomial.C : (A ⧸ q) →+* Polynomial (A ⧸ q)) = ⊥ := by
    rw [eq_bot_iff]
    intro d hd
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective d
    rw [Ideal.mem_comap, hQdef, RingHom.mem_ker] at hd
    have hgval : g (Polynomial.C (Ideal.Quotient.mk q a)) =
        Ideal.Quotient.mk P (Polynomial.C a) := by
      rw [hgdef, RingHom.comp_apply, RingHom.comp_apply]
      have h1 : (↑e : Polynomial (A ⧸ q) →+* Polynomial A ⧸ I) (Polynomial.C (Ideal.Quotient.mk q a)) =
          Ideal.Quotient.mk I (Polynomial.C a) := by
        rw [show Polynomial.C (Ideal.Quotient.mk q a) =
          (Polynomial.C a).map (Ideal.Quotient.mk q) from by simp]
        exact Ideal.polynomialQuotientEquivQuotientPolynomial_map_mk q (Polynomial.C a)
      rw [h1]
      exact DoubleQuot.quotQuotEquivQuotOfLE_quotQuotMk (Polynomial.C a) hle
    rw [hgval, Ideal.Quotient.eq_zero_iff_mem] at hd
    rw [Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem, hqdef, Ideal.mem_comap]
    exact hd
  by_cases hQbot : Q = ⊥
  · have hPb0 : Pb.height = 0 := by rw [← hQheight, hQbot, Ideal.height_bot]
    rw [hPheight, hPb0, ← hdim, hQbot,
      RingEquiv.ringKrullDim (RingEquiv.quotientBot (Polynomial (A ⧸ q))),
      Polynomial.ringKrullDim_of_isNoetherianRing]
    simp only [WithBot.coe_add, add_zero, zero_add]
    abel
  · have hQheight1 : Q.height = 1 :=
      height_eq_one_of_isPrime_ne_bot_of_comap_C_eq_bot Q hQcomap hQbot
    have hdimQ : ringKrullDim (Polynomial (A ⧸ q) ⧸ Q) = ringKrullDim (A ⧸ q) :=
      ringKrullDim_quotient_polynomial_eq_of_comap_C_eq_bot (K := K) (B := A ⧸ q) Q hQcomap hQbot
    have hPb1 : Pb.height = 1 := by rw [← hQheight, hQheight1]
    rw [hPheight, hPb1, ← hdim, hdimQ]
    simp only [WithBot.coe_add, WithBot.coe_one]
    abel
/-- For the polynomial ring `K[X_1,…,X_n]` over a field `K` and a prime ideal `P`, the dimension of
the quotient plus the height of `P` equals `n` (catenarity + equidimensionality of affine space). -/
theorem ringKrullDim_quotient_add_height_eq {K : Type*} [Field K] (n : ℕ)
    (P : Ideal (MvPolynomial (Fin n) K)) [P.IsPrime] :
    ringKrullDim (MvPolynomial (Fin n) K ⧸ P) + P.height = (n : WithBot ℕ∞) := by
  induction n with
  | zero =>
    have hdim : ringKrullDim (MvPolynomial (Fin 0) K) = 0 := by
      rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add,
        Nat.card_eq_fintype_card, Fintype.card_fin]
      norm_num
    have h1 : P.height = 0 := by
      have h := P.height_le_ringKrullDim_of_isPrime
      rw [hdim] at h
      exact le_antisymm (WithBot.coe_le_coe.mp h) bot_le
    have h2 : ringKrullDim (MvPolynomial (Fin 0) K ⧸ P) = 0 := by
      refine le_antisymm ?_ (ringKrullDim_nonneg_of_nontrivial)
      calc ringKrullDim (MvPolynomial (Fin 0) K ⧸ P) ≤ ringKrullDim (MvPolynomial (Fin 0) K) :=
            ringKrullDim_quotient_le P
        _ = 0 := hdim
    rw [h2, h1]
    norm_num
  | succ n ih =>
    set e : MvPolynomial (Fin (n + 1)) K ≃ₐ[K] Polynomial (MvPolynomial (Fin n) K) :=
      MvPolynomial.finSuccEquiv K n with hedef
    set P' : Ideal (Polynomial (MvPolynomial (Fin n) K)) :=
      P.map (e : MvPolynomial (Fin (n + 1)) K →+* Polynomial (MvPolynomial (Fin n) K)) with hP'def
    set q : Ideal (MvPolynomial (Fin n) K) :=
      P'.comap (Polynomial.C : MvPolynomial (Fin n) K →+* Polynomial (MvPolynomial (Fin n) K))
      with hqdef
    haveI hP'prime : P'.IsPrime := by
      rw [hP'def]
      exact Ideal.map_isPrime_of_equiv
        (e : MvPolynomial (Fin (n + 1)) K ≃ₐ[K] Polynomial (MvPolynomial (Fin n) K))
    have hheight : P.height = P'.height := by
      rw [hP'def]
      exact (RingEquiv.height_map
        (e : MvPolynomial (Fin (n + 1)) K ≃+* Polynomial (MvPolynomial (Fin n) K)) P).symm
    have hdim : ringKrullDim (Polynomial (MvPolynomial (Fin n) K) ⧸ P') =
        ringKrullDim (MvPolynomial (Fin (n + 1)) K ⧸ P) := by
      rw [hP'def]
      exact (ringKrullDim_eq_of_ringEquiv
        (Ideal.quotientEquiv P (P.map (e : MvPolynomial (Fin (n + 1)) K →+*
          Polynomial (MvPolynomial (Fin n) K))) e.toRingEquiv rfl)).symm
    have hH := height_add_ringKrullDim_quotient_polynomial (K := K)
      (A := MvPolynomial (Fin n) K) P'
    have hIH := ih q
    rw [← hdim, hheight, add_comm, hH,
      add_comm (↑q.height) (ringKrullDim (MvPolynomial (Fin n) K ⧸ q)), hIH]
    simp only [WithBot.coe_add, Nat.cast_add, Nat.cast_one]

end

end Commons.RingTheory.KrullDimension