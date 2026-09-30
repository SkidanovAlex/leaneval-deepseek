import Mathlib
import Submission.Work.CurveBasics.Order.kxPrimeOfPlace_ne_bot_of_nonneg
import Submission.Work.CurveBasics.Order.kxPrimeOfPlace_fraction_of_nonneg
import Submission.Work.CurveBasics.Place.valuationSubring_ne_top
import Submission.Work.KeyLemma.Curve.genericSum
import Submission.Work.KeyLemma.Curve.card_branches_fixed
import Submission.Work.CurveBasics.Order.kxClosure_residue_surjective
import Submission.Work.CurveBasics.Order.valuationSubring_eq_atPrime
import Submission.Work.CurveBasics.Order.Bridge
import Submission.Work.CurveBasics.Place.Valuation
import Submission.Work.KeyLemma.Curve.ordBaseBaseField
import Submission.Work.CurveBasics.Order.Setup
import Submission.Work.CurveBasics.Order.SumPrimesAux
import Submission.Work.CurveBasics.Order.ord_lem
import Submission.Work.CurveBasics.Order.integralClosure_adjoin_finite_of_transcendental
import Submission.Work.CurveBasics.Order.kxPrimeOfPlace_liesOver
import Submission.Work.CurveBasics.Order.isLocalization_valuationSubring_of_crux
import Submission.Work.CurveBasics.Place.mem_valuationSubring_iff
import Submission.Work.CurveBasics.Place.ord_uniformizer

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.

/-
# The centre map `𝒪_Q → R_P` of a conjugate point, corrected form

The statement proved here is the lemma `Work.KeyLemma.Curve.BranchSum.center_loc` with one
hypothesis added, namely

  `[IsLocalization.AtPrime (Localization.AtPrime P) P]`

which says that the *given* algebra structure
`Algebra ↥(integralClosure ↥(ordBase) N) (Localization.AtPrime P)` is the localisation of
`R := integralClosure (ordBase C h) N` at `P`.  Without it, the algebra structures

  `algebraMap R (Localization.AtPrime P)`  and  `algebraMap (Localization.AtPrime P) N`

are *arbitrary* hypotheses, and the conclusion is false: twisting `algebraMap
(Localization.AtPrime P) N` by a non-trivial ring automorphism of `N` (e.g. `x ↦ -x` in
`N = E = k(x)`, `h = x - 1`, `N = E`) still satisfies `IsScalarTower` and `IsFractionRing`
while making it impossible to lift the elements `y ∈ 𝒪_Q` with `β⁻¹y ∉ 𝒪_Q`.  See
`NOTES_center_loc.md` in this directory.

With the added hypothesis the intended mathematics goes through:  `σ` is a `k[h]`-algebra map,
so it carries `B = k[h]^int ⊆ K(C)` into `R`, the contraction of `P` along it is the prime
`q_Q = B ∩ 𝔪_Q` at `Q` (maximal, since `q_Q ≠ 0`) and hence `σ(B ∖ q_Q) ⊆ R ∖ P`; together with
`𝒪_Q = B_{q_Q}` this puts `σ(𝒪_Q)` into `R_P`, and the centre map is the restriction of `σ`.
-/

universe u

namespace Work.KeyLemma.Curve.BranchSum

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

theorem center_loc_of_isLocalizationAtPrime {k : Type u} [Field k] [IsAlgClosed k]
    (C : Work.CurveBasics.Curve k) (h : C.functionField) (hht : Transcendental k h)
    [FiniteDimensional ↥(Work.KeyLemma.Curve.baseField C h) ↥C.functionField]
    [Algebra.IsSeparable ↥(Work.KeyLemma.Curve.baseField C h) ↥C.functionField]
    {N : Type u} [Field N] [Algebra ↥(Work.KeyLemma.Curve.baseField C h) N] [Algebra k N]
    [IsScalarTower k ↥(Work.KeyLemma.Curve.baseField C h) N]
    [IsGalois ↥(Work.KeyLemma.Curve.baseField C h) N]
    [Algebra ↥C.functionField N]
    [IsScalarTower ↥(Work.KeyLemma.Curve.baseField C h) ↥C.functionField N]
    [FiniteDimensional ↥(Work.KeyLemma.Curve.baseField C h) N]
    [Algebra ↥(Work.CurveBasics.Curve.ordBase C h) N]
    [IsScalarTower ↥(Work.CurveBasics.Curve.ordBase C h) ↥(Work.KeyLemma.Curve.baseField C h) N]
    (hKE : (algebraMap ↥(Work.KeyLemma.Curve.baseField C h) N)
      = (algebraMap ↥C.functionField N).comp
        (algebraMap ↥(Work.KeyLemma.Curve.baseField C h) ↥C.functionField))
    (hAE : (algebraMap ↥(Work.CurveBasics.Curve.ordBase C h) N)
      = (algebraMap ↥C.functionField N).comp
        (algebraMap ↥(Work.CurveBasics.Curve.ordBase C h) ↥C.functionField))
    [IsFractionRing ↥(integralClosure ↥(Work.CurveBasics.Curve.ordBase C h) N) N]
    (P : Ideal ↥(integralClosure ↥(Work.CurveBasics.Curve.ordBase C h) N)) [P.IsPrime]
    [P.LiesOver (Work.CurveBasics.Curve.ordIdeal C h)]
    [Algebra k (Localization.AtPrime P)]
    [Algebra ↥(integralClosure ↥(Work.CurveBasics.Curve.ordBase C h) N) (Localization.AtPrime P)]
    [IsLocalization.AtPrime (Localization.AtPrime P) P]
    [Algebra (Localization.AtPrime P) N]
    [IsScalarTower ↥(integralClosure ↥(Work.CurveBasics.Curve.ordBase C h) N)
      (Localization.AtPrime P) N]
    [IsScalarTower k (Localization.AtPrime P) N]
    [IsFractionRing (Localization.AtPrime P) N]
    (hSTalg : ∀ r : ↥(integralClosure ↥(Work.CurveBasics.Curve.ordBase C h) N),
      algebraMap (Localization.AtPrime P) N
          (algebraMap ↥(integralClosure ↥(Work.CurveBasics.Curve.ordBase C h) N)
            (Localization.AtPrime P) r)
        = algebraMap ↥(integralClosure ↥(Work.CurveBasics.Curve.ordBase C h) N) N r)
    (σ : ↥C.functionField →ₐ[↥(Work.KeyLemma.Curve.baseField C h)] N)
    (Q : C.Place) (hQ : 0 ≤ C.ordAt h Q)
    (hPr : ∀ x ∈ Work.CurveBasics.kxPrimeOfPlace C h Q hQ, ∃ c ∈ P,
      algebraMap ↥(integralClosure ↥(Work.CurveBasics.Curve.ordBase C h) N) N c
        = σ (algebraMap ↥(C.ordClosure h) ↥C.functionField x)) :
    ∃ χ : Q.valuationSubring →+* Localization.AtPrime P, IsLocalHom χ ∧
      ∀ y : Q.valuationSubring,
        algebraMap (Localization.AtPrime P) N (χ y) = σ (y : C.functionField) := by
  classical
  haveI hDed : IsDedekindDomain ↥(C.ordClosure h) :=
    Work.CurveBasics.Curve.kxClosure_isDedekindDomain C h
  have hqne : Work.CurveBasics.kxPrimeOfPlace C h Q hQ ≠ ⊥ :=
    Work.CurveBasics.Order.kxPrimeOfPlace_ne_bot_of_nonneg C h hht Q hQ
  have hqmax : (Work.CurveBasics.kxPrimeOfPlace C h Q hQ).IsMaximal :=
    Ideal.IsPrime.isMaximal_of_ne_bot (Work.CurveBasics.kxPrimeOfPlace_isPrime C h Q hQ) hqne
  have hBEco : ∀ b : ↥(C.ordClosure h),
      algebraMap ↥(C.ordClosure h) ↥C.functionField b = (b : C.functionField) := fun b => rfl
  have hKEco : ∀ y : ↥(Work.KeyLemma.Curve.baseField C h),
      algebraMap ↥(Work.KeyLemma.Curve.baseField C h) ↥C.functionField y = (y : C.functionField) :=
    fun y => rfl
  have hAEco : ∀ x : ↥(Work.CurveBasics.Curve.ordBase C h),
      algebraMap ↥(Work.CurveBasics.Curve.ordBase C h) ↥C.functionField x = (x : C.functionField) :=
    fun x => rfl
  have hAKco : ∀ x : ↥(Work.CurveBasics.Curve.ordBase C h),
      ((algebraMap ↥(Work.CurveBasics.Curve.ordBase C h) ↥(Work.KeyLemma.Curve.baseField C h) x)
        : C.functionField) = (x : C.functionField) :=
    fun x => Work.KeyLemma.Curve.algebraMap_ordBase_baseField k C h x
  have hcomm : ∀ a : ↥(Work.CurveBasics.Curve.ordBase C h),
      σ (algebraMap ↥(Work.CurveBasics.Curve.ordBase C h) ↥C.functionField a)
        = algebraMap ↥(Work.CurveBasics.Curve.ordBase C h) N a := by
    intro a
    rw [show algebraMap ↥(Work.CurveBasics.Curve.ordBase C h) ↥C.functionField a
          = algebraMap ↥(Work.KeyLemma.Curve.baseField C h) ↥C.functionField
              (algebraMap ↥(Work.CurveBasics.Curve.ordBase C h)
                ↥(Work.KeyLemma.Curve.baseField C h) a) from by rw [hKEco, hAKco, hAEco]]
    rw [σ.commutes]
    rw [hKE, hAE]
    rw [RingHom.comp_apply, RingHom.comp_apply, hKEco, hAKco, hAEco]
  let σA : ↥C.functionField →ₐ[↥(Work.CurveBasics.Curve.ordBase C h)] N :=
    { σ.toRingHom with commutes' := hcomm }
  let ψ : ↥(C.ordClosure h) →ₐ[↥(Work.CurveBasics.Curve.ordBase C h)] N :=
    σA.comp (Subalgebra.val (C.ordClosure h))
  have hψ : ∀ b : ↥(C.ordClosure h),
      ψ b = σ ((b : ↥(C.ordClosure h)) : ↥C.functionField) := fun b => rfl
  have h3 : σ.toRingHom.comp (algebraMap ↥(Work.CurveBasics.Curve.ordBase C h) ↥C.functionField)
      = algebraMap ↥(Work.CurveBasics.Curve.ordBase C h) N := by
    ext a; exact hcomm a
  have hmem : ∀ b : ↥(C.ordClosure h),
      ψ b ∈ integralClosure ↥(Work.CurveBasics.Curve.ordBase C h) N := by
    intro b
    rw [mem_integralClosure_iff, hψ]
    show (algebraMap ↥(Work.CurveBasics.Curve.ordBase C h) N).IsIntegralElem
      (σ (((b : ↥(C.ordClosure h)) : ↥C.functionField)))
    rw [← h3]
    exact RingHom.IsIntegralElem.map
      ((mem_integralClosure_iff (R := ↥(Work.CurveBasics.Curve.ordBase C h))
        (A := ↥C.functionField)).mp b.2) σ.toRingHom
  let σB : ↥(C.ordClosure h) →ₐ[↥(Work.CurveBasics.Curve.ordBase C h)]
      ↥(integralClosure ↥(Work.CurveBasics.Curve.ordBase C h) N) := ψ.codRestrict _ hmem
  have hσB : ∀ b : ↥(C.ordClosure h),
      algebraMap ↥(integralClosure ↥(Work.CurveBasics.Curve.ordBase C h) N) N (σB b)
        = σ ((b : ↥(C.ordClosure h)) : ↥C.functionField) := fun b => rfl
  let g : ↥(C.ordClosure h) →+* ↥(integralClosure ↥(Work.CurveBasics.Curve.ordBase C h) N) :=
    σB.toRingHom
  have hg : ∀ b : ↥(C.ordClosure h), g b = σB b := fun b => rfl
  have hcomap : Ideal.comap g P = Work.CurveBasics.kxPrimeOfPlace C h Q hQ := by
    refine (hqmax.eq_of_le ?_ ?_).symm
    · intro htop
      have h1 : (1 : ↥(C.ordClosure h)) ∈ Ideal.comap g P := by rw [htop]; trivial
      rw [Ideal.mem_comap] at h1
      refine (inferInstance : P.IsPrime).ne_top ?_
      exact Ideal.eq_top_iff_one P |>.mpr (by simpa using h1)
    · intro x hx
      obtain ⟨c, hcP, hc⟩ := hPr x hx
      have hgx : g x = c := by
        apply IsFractionRing.injective
          ↥(integralClosure ↥(Work.CurveBasics.Curve.ordBase C h) N) N
        rw [hg x, hσB x, ← hBEco x]
        exact hc.symm
      rw [Ideal.mem_comap, hgx]
      exact hcP
  have hfraction : ∀ y : ↥(Q.valuationSubring), ∃ (b s : ↥(C.ordClosure h)),
      s ∉ Work.CurveBasics.kxPrimeOfPlace C h Q hQ ∧
        (s : C.functionField) * (y : C.functionField) = (b : C.functionField) :=
    fun y => Work.CurveBasics.Order.kxPrimeOfPlace_fraction_of_nonneg C h hht Q hQ
      (y : C.functionField) y.2
  have hgs_comp : ∀ s : ↥(C.ordClosure h),
      algebraMap (Localization.AtPrime P) N
          (algebraMap ↥(integralClosure ↥(Work.CurveBasics.Curve.ordBase C h) N)
            (Localization.AtPrime P) (g s))
        = σ ((s : ↥(C.ordClosure h)) : ↥C.functionField) := by
    intro s
    rw [hSTalg (g s)]
    exact hσB s
  have hex : ∀ y : ↥(Q.valuationSubring), ∃ c : Localization.AtPrime P,
      algebraMap (Localization.AtPrime P) N c = σ (y : C.functionField) := by
    intro y
    obtain ⟨b, s, hs, hys⟩ := hfraction y
    have hgsP : g s ∈ P.primeCompl := by
      rw [Ideal.mem_primeCompl_iff]
      intro hgP
      exact hs (hcomap ▸ Ideal.mem_comap.mpr hgP)
    have hs0 : ((s : ↥(C.ordClosure h)) : C.functionField) ≠ 0 := by
      intro h0
      have hs_zero : s = 0 := by
        apply Subtype.ext
        simpa using h0
      exact (hs_zero ▸ hs) (Ideal.zero_mem _)
    have hsn : σ ((s : ↥(C.ordClosure h)) : ↥C.functionField) ≠ 0 := fun h0 =>
      hs0 (RingHom.injective σ.toRingHom (by simpa using h0))
    let u : (Localization.AtPrime P)ˣ :=
      (IsLocalization.map_units (Localization.AtPrime P) ⟨g s, hgsP⟩).unit
    have hu : (u : Localization.AtPrime P)
        = algebraMap ↥(integralClosure ↥(Work.CurveBasics.Curve.ordBase C h) N)
            (Localization.AtPrime P) (g s) := IsUnit.unit_spec _
    refine ⟨algebraMap ↥(integralClosure ↥(Work.CurveBasics.Curve.ordBase C h) N)
      (Localization.AtPrime P) (g b) * ↑(u⁻¹), ?_⟩
    have huc : algebraMap (Localization.AtPrime P) N (↑u : Localization.AtPrime P)
        = σ ((s : ↥(C.ordClosure h)) : ↥C.functionField) := by
      rw [hu]
      exact hgs_comp s
    have hinv : algebraMap (Localization.AtPrime P) N (↑(u⁻¹) : Localization.AtPrime P)
        = (σ ((s : ↥(C.ordClosure h)) : ↥C.functionField))⁻¹ := by
      rw [← huc]
      exact eq_inv_of_mul_eq_one_right (by rw [← map_mul, Units.mul_inv, map_one])
    rw [map_mul, hgs_comp b, hinv]
    rw [← hys, map_mul, mul_assoc,
      mul_comm (σ (y : C.functionField))
        ((σ ((s : ↥(C.ordClosure h)) : ↥C.functionField))⁻¹),
      ← mul_assoc, mul_inv_cancel₀ hsn, one_mul]
  refine ⟨{ toFun := fun y => Classical.choose (hex y)
            map_one' := ?_
            map_mul' := ?_
            map_zero' := ?_
            map_add' := ?_ }, ?_, ?_⟩
  · apply IsFractionRing.injective (Localization.AtPrime P) N
    rw [map_one, Classical.choose_spec (hex 1)]
    simp
  · intro y z
    apply IsFractionRing.injective (Localization.AtPrime P) N
    rw [map_mul, Classical.choose_spec (hex (y * z)), Classical.choose_spec (hex y),
      Classical.choose_spec (hex z), Subring.coe_mul, map_mul]
  · apply IsFractionRing.injective (Localization.AtPrime P) N
    rw [map_zero, Classical.choose_spec (hex 0)]
    simp
  · intro y z
    apply IsFractionRing.injective (Localization.AtPrime P) N
    rw [map_add, Classical.choose_spec (hex (y + z)), Classical.choose_spec (hex y),
      Classical.choose_spec (hex z), Subring.coe_add, map_add]
  · refine ⟨fun a ha => ?_⟩
    by_contra hna
    have hma : a ∈ IsLocalRing.maximalIdeal ↥(Q.valuationSubring) := by
      by_contra hcon
      exact hna ((IsLocalRing.notMem_maximalIdeal).mp hcon)
    obtain ⟨b, s, hs, hys⟩ := hfraction a
    have hbq : b ∈ Work.CurveBasics.kxPrimeOfPlace C h Q hQ := by
      show Subring.inclusion (Work.CurveBasics.kxClosure_le_valuationSubring C h Q hQ) b
        ∈ IsLocalRing.maximalIdeal ↥(Q.valuationSubring)
      have hcoe : (Subring.inclusion
            (Work.CurveBasics.kxClosure_le_valuationSubring C h Q hQ) b : ↥(Q.valuationSubring))
          = (⟨((b : ↥(C.ordClosure h)) : C.functionField),
              Work.CurveBasics.kxClosure_le_valuationSubring C h Q hQ b.2⟩
              : ↥(Q.valuationSubring)) := by
        apply Subtype.ext
        rw [Subring.coe_inclusion]
      have hmul : (⟨((s : ↥(C.ordClosure h)) : C.functionField),
            Work.CurveBasics.kxClosure_le_valuationSubring C h Q hQ s.2⟩
            : ↥(Q.valuationSubring)) * a
          = (⟨((b : ↥(C.ordClosure h)) : C.functionField),
              Work.CurveBasics.kxClosure_le_valuationSubring C h Q hQ b.2⟩
              : ↥(Q.valuationSubring)) := by
        apply Subtype.ext
        rw [Subring.coe_mul]
        exact hys
      rw [hcoe, ← hmul]
      exact Ideal.mul_mem_left _ _ hma
    have hgbP : g b ∈ P := by
      have hbq' : b ∈ Ideal.comap g P := hcomap ▸ hbq
      exact Ideal.mem_comap.mp hbq'
    have hgsP : g s ∈ P.primeCompl := by
      rw [Ideal.mem_primeCompl_iff]
      intro hgP
      exact hs (hcomap ▸ Ideal.mem_comap.mpr hgP)
    have hχs : (Classical.choose (hex a))
          * algebraMap ↥(integralClosure ↥(Work.CurveBasics.Curve.ordBase C h) N)
              (Localization.AtPrime P) (g s)
        = algebraMap ↥(integralClosure ↥(Work.CurveBasics.Curve.ordBase C h) N)
            (Localization.AtPrime P) (g b) := by
      apply IsFractionRing.injective (Localization.AtPrime P) N
      rw [map_mul, Classical.choose_spec (hex a), hgs_comp s, hgs_comp b, ← map_mul, mul_comm, hys]
    have hmemm : algebraMap ↥(integralClosure ↥(Work.CurveBasics.Curve.ordBase C h) N)
          (Localization.AtPrime P) (g b)
        ∈ IsLocalRing.maximalIdeal (Localization.AtPrime P) := by
      rw [← IsLocalization.AtPrime.map_eq_maximalIdeal P (Localization.AtPrime P)]
      exact Ideal.mem_map_of_mem _ hgbP
    have hunit : IsUnit (algebraMap
        ↥(integralClosure ↥(Work.CurveBasics.Curve.ordBase C h) N)
        (Localization.AtPrime P) (g s)) :=
      IsLocalization.map_units (Localization.AtPrime P) ⟨g s, hgsP⟩
    refine (IsLocalRing.notMem_maximalIdeal.mpr ha) ?_
    change Classical.choose (hex a) ∈ IsLocalRing.maximalIdeal (Localization.AtPrime P)
    by_contra hnot
    have h1 : IsUnit (Classical.choose (hex a)) :=
      (IsLocalRing.notMem_maximalIdeal).mp hnot
    have h2 : IsUnit (Classical.choose (hex a)
        * algebraMap ↥(integralClosure ↥(Work.CurveBasics.Curve.ordBase C h) N)
            (Localization.AtPrime P) (g s)) := h1.mul hunit
    have h3 : (Classical.choose (hex a)
          * algebraMap ↥(integralClosure ↥(Work.CurveBasics.Curve.ordBase C h) N)
              (Localization.AtPrime P) (g s))
        ∈ IsLocalRing.maximalIdeal (Localization.AtPrime P) := by
      rw [hχs]
      exact hmemm
    exact (IsLocalRing.notMem_maximalIdeal.mpr h2) h3
  · intro y
    exact Classical.choose_spec (hex y)

end Work.KeyLemma.Curve.BranchSum
