import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotK.TwRuling

open Polynomial MvPolynomial

-- CONTEXT.  Second brick consumed by `Work.MotK.TwRuling.SdThetaKernel` (the presentation
-- `ker (sdTheta) = (sdualT)` of the target ruling divisor, hence `TGen.SdualTClass` ->
-- `TGenCensus_wired` -> `Work.MotK.LinkCertT`); it is the on-disk statement
-- `Work.MotK.TwRuling.CoeffMapInjectiveOfPrimeMonic` copied under a fresh name so that it can be
-- delegated (the original file will be re-pointed to it and its `sorry` removed).
--
-- Content: the composite `Φ := (θ ∘ finSuccEquiv.symm) ∘ Polynomial.CAlgHom : K[X₀,X₁] →ₐ[K] A` is
-- injective.  Note `MvPolynomial.finSuccEquiv K 2 : MvPolynomial (Fin 3) K ≃ₐ[K]
-- Polynomial (MvPolynomial (Fin 2) K)` sends `X 0 ↦ Polynomial.X` and `X (i+1) ↦ C (X i)`, so `Φ` is
-- "the coefficient map" `R := MvPolynomial (Fin 2) K → A` and `Φ (X i) = θ (X (i+1))`.
--
-- ROUTE (transcendence degree; the needed API — `Algebra.trdeg_add_eq`, `trdeg_eq_zero_iff` and the
-- algebraic-extension additivity — is in Mathlib, `FieldTheory/FinTrdeg.lean`).
-- Let `q := RingHom.ker Φ`; since `A` is a field, `q` is prime, so either `q = ⊥` (which is exactly
-- injectivity) or `hTr q hq hq_ne_bot` gives `trdeg K (FractionRing (R ⧸ q)) ≤ 1`.
-- In the second case let `F := FractionRing (R ⧸ q)`, identified with the fraction field of `Φ(R)`
-- inside `A` (use `IsFractionRing` for the range).  The element `θ (Polynomial.X)` generates
-- `θ.range` over `Φ(R)`, and it is *integral*, hence algebraic, over `Φ(R)`:
-- `(finSuccEquiv K 2 G)` is monic (`hmonic`) with coefficients in `R` and `θ G = 0` (`hθG`), giving
-- `Σ Φ cᵢ · θ(X₀)^i = 0` with leading coefficient `1`.  By `hfrac`
-- (`Subfield.closure (range (algebraMap θ.range A)) = ⊤`) the field `A` is generated over `F` by
-- `θ (Polynomial.X)`, so `A / F` is algebraic and `Algebra.trdeg K A = Algebra.trdeg K F ≤ 1`,
-- contradicting `htrdeg : Algebra.trdeg K A = 2`.
--
-- (`hG : Prime G` is not used by this route — harmless; it comes from the caller.  The sibling node
-- `SdThetaFracTop`, which supplies `hfrac`, is the one that is false in characteristic 2; this brick
-- itself is characteristic-free and usable whenever that node is.)
theorem CoeffMapInjectivePrimeMonic
    {K : Type} [Field K] {A : Type} [Field A] [Algebra K A]
    (θ : MvPolynomial (Fin 3) K →ₐ[K] A) (G : MvPolynomial (Fin 3) K)
    (hG : Prime G)
    (hmonic : (MvPolynomial.finSuccEquiv K 2 G).Monic)
    (hθG : θ G = 0)
    (hfrac : Subfield.closure (Set.range (algebraMap θ.range A)) = ⊤)
    (htrdeg : Algebra.trdeg K A = 2)
    (hTr : ∀ (q : Ideal (MvPolynomial (Fin 2) K)), q.IsPrime → q ≠ ⊥ →
      Algebra.trdeg K (FractionRing (MvPolynomial (Fin 2) K ⧸ q)) ≤ 1) :
    Function.Injective ((θ.comp (MvPolynomial.finSuccEquiv K 2).symm.toAlgHom).comp
      Polynomial.CAlgHom) := by
  -- `hG` is not needed by this route (see the comment above); reference it so that it is not an
  -- unused binder, and keep the statement untouched.
  have hG' : Prime G := hG
  -- Decompose `θ = Ψ ∘ finSuccEquiv` with `Ψ : R[X] →ₐ[K] A`, `R := K[X₀,X₁]`.
  let Ψ : Polynomial (MvPolynomial (Fin 2) K) →ₐ[K] A :=
    θ.comp (MvPolynomial.finSuccEquiv K 2).symm.toAlgHom
  let Φ : MvPolynomial (Fin 2) K →ₐ[K] A := Ψ.comp Polynomial.CAlgHom
  change Function.Injective ⇑Φ
  rw [RingHom.injective_iff_ker_eq_bot]
  set q : Ideal (MvPolynomial (Fin 2) K) := RingHom.ker Φ with hq
  by_contra hqne
  have hqprime : q.IsPrime := by rw [hq]; exact RingHom.ker_isPrime Φ
  have htrF : Algebra.trdeg K (FractionRing (MvPolynomial (Fin 2) K ⧸ q)) ≤ 1 :=
    hTr q hqprime hqne
  -- The quotient `Q := R ⧸ q` is a domain and `Φ` factors through it.
  let Q := MvPolynomial (Fin 2) K ⧸ q
  haveI hQd : IsDomain Q := Ideal.Quotient.isDomain q
  have hlift : ∀ a ∈ q, Φ a = 0 :=
    fun a ha => (RingHom.mem_ker (f := Φ)).mp (by rw [← hq]; exact ha)
  let ψ : Q →ₐ[K] A := Ideal.Quotient.liftₐ q Φ hlift
  have hψ_mk : ∀ r : MvPolynomial (Fin 2) K, ψ (Ideal.Quotient.mk q r) = Φ r := by
    intro r
    have h := AlgHom.congr_fun (Ideal.Quotient.liftₐ_comp q Φ hlift) r
    simpa only [ψ, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] using h
  have hψ_inj : Function.Injective ψ := by
    intro x y hxy
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [hψ_mk, hψ_mk] at hxy
    have hmem : r - s ∈ q := by
      rw [hq]
      exact (RingHom.mem_ker (f := Φ)).mpr (by rw [map_sub, hxy, sub_self])
    exact Ideal.Quotient.eq.mpr hmem
  -- Pass to the fraction field `Fq` of `Q`; `ψF` embeds it into `A`.
  let Fq := FractionRing Q
  let ψF : Fq →ₐ[K] A := IsFractionRing.liftAlgHom hψ_inj
  have hψF_inj : Function.Injective ψF := RingHom.injective ψF.toRingHom
  -- `F'` is the fraction field of `Φ(R)` inside `A`, an intermediate field of `A / K`.
  let F' : IntermediateField K A := ψF.fieldRange
  have hΦF' : ∀ r : MvPolynomial (Fin 2) K, Φ r ∈ F' := by
    intro r
    show Φ r ∈ ψF.fieldRange
    rw [AlgHom.mem_fieldRange]
    refine ⟨algebraMap Q Fq (Ideal.Quotient.mk q r), ?_⟩
    show IsFractionRing.lift hψ_inj (algebraMap Q Fq (Ideal.Quotient.mk q r)) = Φ r
    rw [IsFractionRing.lift_algebraMap]
    exact hψ_mk r
  -- The element `t := Ψ X = θ (X 0)`.
  let t : A := Ψ Polynomial.X
  let p : (MvPolynomial (Fin 2) K)[X] := MvPolynomial.finSuccEquiv K 2 G
  have hp_monic : p.Monic := hmonic
  have hΨp : Ψ p = 0 := by
    show Ψ ((MvPolynomial.finSuccEquiv K 2) G) = 0
    simp only [Ψ, AlgHom.comp_apply, AlgEquiv.toAlgHom_apply, AlgEquiv.symm_apply_apply, hθG]
  -- `Qpoly ∈ F'[X]` is monic (leading coefficient `Φ 1 = 1`) and annihilates `t`.
  let Qpoly : (↥F')[X] :=
    p.sum fun n a => Polynomial.C (⟨Φ a, hΦF' a⟩ : ↥F') * Polynomial.X ^ n
  have hQpoly_aeval : Polynomial.aeval t Qpoly = 0 := by
    have h1 : Polynomial.aeval t Qpoly = ∑ n ∈ p.support, Φ (p.coeff n) * t ^ n := by
      simp only [Qpoly, Polynomial.sum_def, map_sum]
      apply Finset.sum_congr rfl
      intro n hn
      rw [map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X]
      rfl
    have h2 : Ψ p = ∑ n ∈ p.support, Φ (p.coeff n) * t ^ n := by
      conv_lhs => rw [← Polynomial.sum_C_mul_X_pow_eq p, Polynomial.sum_def]
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro n hn
      rw [map_mul, map_pow]
      rfl
    rw [h1, ← h2, hΨp]
  have hQpoly_ne : Qpoly ≠ 0 := by
    intro h0
    have h1 : Qpoly.coeff p.natDegree = 1 := by
      show (p.sum fun n a => Polynomial.C (⟨Φ a, hΦF' a⟩ : ↥F')
        * Polynomial.X ^ n).coeff p.natDegree = 1
      rw [Polynomial.coeff_sum, Polynomial.sum_def]
      refine (Finset.sum_eq_single p.natDegree ?_ ?_).trans ?_
      · intro n _hn hne
        rw [Polynomial.coeff_C_mul_X_pow, if_neg (Ne.symm hne)]
      · intro hnot
        exact absurd (Polynomial.mem_support_iff.mpr
          (by rw [hp_monic.coeff_natDegree]; exact one_ne_zero)) hnot
      · rw [Polynomial.coeff_C_mul_X_pow, if_pos rfl]
        apply Subtype.ext
        show Φ (p.coeff p.natDegree) = (1 : A)
        rw [hp_monic.coeff_natDegree, map_one]
    have hc := congrArg (fun f : (↥F')[X] => f.coeff p.natDegree) h0
    rw [h1] at hc
    simp only [Polynomial.coeff_zero] at hc
    exact one_ne_zero hc
  have ht_alg : IsAlgebraic ↥F' t := by
    rw [isAlgebraic_iff_not_injective]
    intro hinj
    exact hQpoly_ne (hinj (by simp only [hQpoly_aeval, map_zero]))
  -- `A` is generated over `F'` by `t`.
  let S : Subalgebra ↥F' A := Algebra.adjoin ↥F' ({t} : Set A)
  have hS : S.IsAlgebraic := Algebra.isAlgebraic_adjoin_singleton_iff.mpr ht_alg
  have hΦS : ∀ r, Φ r ∈ S := fun r => S.algebraMap_mem ⟨Φ r, hΦF' r⟩
  have htS : t ∈ S := Algebra.subset_adjoin (Set.mem_singleton t : t ∈ ({t} : Set A))
  have hΨS : ∀ q : (MvPolynomial (Fin 2) K)[X], Ψ q ∈ S := by
    intro q
    induction q using Polynomial.induction_on with
    | C a => exact hΦS a
    | add p q hp hq => rw [map_add]; exact S.add_mem hp hq
    | monomial n a ih =>
        have hstep : Ψ (Polynomial.C a * Polynomial.X ^ (n + 1))
            = Ψ (Polynomial.C a * Polynomial.X ^ n) * t := by
          conv_lhs => rw [pow_succ, ← mul_assoc]
          rw [map_mul]
        exact hstep.symm ▸ S.mul_mem ih htS
  have hθS : (↑θ.range : Set A) ⊆ (↑S : Set A) := by
    intro y hy
    have hy' : y ∈ θ.range := hy
    rw [AlgHom.mem_range] at hy'
    obtain ⟨a, rfl⟩ := hy'
    have hθa : θ a = Ψ ((MvPolynomial.finSuccEquiv K 2) a) := by
      simp only [Ψ, AlgHom.comp_apply, AlgEquiv.toAlgHom_apply, AlgEquiv.symm_apply_apply]
    rw [hθa]
    exact hΨS _
  have hΦrange : Set.range (algebraMap ↥θ.range A) ⊆ (↑S : Set A) := by
    rintro x ⟨y, rfl⟩
    exact hθS y.2
  have hEeq : ((hS.toIntermediateField).toSubfield : Set A) = (↑S : Set A) := by
    rw [IntermediateField.coe_toSubfield, ← IntermediateField.coe_toSubalgebra]
    rfl
  -- `S` is actually a subfield (being algebraic over the field `F'`), so its carrier is `univ`.
  have hS_top : S = ⊤ := by
    have hcl : Subfield.closure (↑S : Set A) = (hS.toIntermediateField).toSubfield := by
      rw [← hEeq, Subfield.closure_eq]
    have htop : (hS.toIntermediateField).toSubfield = ⊤ := by
      rw [← hcl]
      exact top_le_iff.mp (hfrac ▸ Subfield.closure_mono hΦrange)
    have hSuniv : (↑S : Set A) = Set.univ := by
      rw [← hEeq, htop]; rfl
    exact Subalgebra.ext fun x => ⟨fun _ => trivial, fun _ => by
      show x ∈ (↑S : Set A)
      rw [hSuniv]
      trivial⟩
  have hAlg : Algebra.IsAlgebraic ↥F' A := by
    rw [Algebra.isAlgebraic_iff, ← hS_top]
    exact hS
  haveI := hAlg
  -- `trdeg K F' = trdeg K A = 2`, but `F' ≅ Fq` and `hTr` gives `trdeg K Fq ≤ 1`.
  have htr1 : Algebra.trdeg K ↥F' = 2 := by
    have h := trdeg_add_eq K ↥F' (A := A)
    have h0 : Algebra.trdeg ↥F' A = 0 := trdeg_eq_zero
    rw [h0, add_zero] at h
    exact h.trans htrdeg
  have e : Fq ≃ₐ[K] ↥F' := by
    refine AlgEquiv.ofBijective (ψF.codRestrict F'.toSubalgebra ?_) ?_
    · intro x
      rw [AlgHom.fieldRange_toSubalgebra]
      exact ⟨x, rfl⟩
    · constructor
      · intro x y hxy
        exact hψF_inj (congrArg Subtype.val hxy)
      · intro y
        obtain ⟨x, hx⟩ := (AlgHom.mem_fieldRange).mp y.2
        exact ⟨x, Subtype.ext hx⟩
  have hle : Algebra.trdeg K ↥F' ≤ 1 := by
    rw [← AlgEquiv.trdeg_eq e]
    exact htrF
  rw [htr1] at hle
  exact absurd hle (by norm_num)

end Work.MotK.TwRuling
