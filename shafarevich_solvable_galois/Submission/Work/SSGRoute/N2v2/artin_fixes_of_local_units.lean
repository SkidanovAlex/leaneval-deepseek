import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Submission.Work.SSG8Escape.localField_not_real_of_no_involutions
import Submission.Work.SSGRoute.GrunwaldEscapeCore.productFormula_sum
import Submission.Work.SSGRoute.SSG8Escape.Setup
import Submission.Work.SSGRoute.n4_idele_factor
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped NumberField Pointwise
open NumberField IsDedekindDomain
open NK.GlobalCFT

namespace Work.SSGRoute.N2v2

/-! ## Auxiliary lemmas

Three independent inputs feed the proof of `artin_fixes_of_local_units`:

* `arch_localFactor_eq_one_aux` — the local factor of *any* homomorphism on the idèle group is
  trivial at an archimedean place: the completion is `ℂ` (this is exactly the prime-`2` correction
  `Work.SSG8Escape.localField_not_real_of_no_involutions`, whose hypothesis `hKimag` excludes real
  places when `p = 2`), and `ℂˣ` is divisible, hence admits no non-trivial homomorphism to a finite
  group;
* `localImageAt_unifUnit_decomp_aux` — the local component of a global unit at a finite prime is a
  power of a uniformiser times a local unit, the exponent being the `q`-adic exponent of the
  principal idèle;
* `chi_fracIdele_sum_unifUnit_aux` — the character value at the Artin symbol of a fractional ideal,
  expanded in terms of the local factors at the uniformisers.
-/

/-- **Archimedean local factors are trivial.**  Let `k` be a number field, `Ω` an algebraic closure
of `k`, `K` a finite intermediate field containing a primitive `p`-th root of unity `ζ`, and assume
that for `p = 2` the group `Gal(Ω/K)` has no involution other than `1`.  Then for any finite group
`G` and any monoid homomorphism `Φ : 𝕀_↥K →* G`, the local factor at an *archimedean* place `v` of
`↥K`, i.e. `Φ ∘ onePlace_v`, is trivial on `K_vˣ`. -/
theorem arch_localFactor_eq_one_aux
    (p : ℕ) [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K]
    (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p)
    (hKimag : p = 2 → ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → c = 1)
    {G : Type} [Group G] [Fintype G]
    (Φ : NK.GlobalCFT.Idele ↥K →* G)
    (v : NK.GlobalCFT.Place ↥K) (hv : ¬ v.IsFinite)
    (u : (NK.GlobalCFT.Place.localField ↥K v)ˣ) :
    Φ (NK.HassePrinciple.onePlace v u) = 1 := by
  classical
  -- `v` is an archimedean place, so the local field is the completion at an infinite place
  obtain ⟨w, rfl⟩ := NK.GlobalCFT.Place.isInfinite_iff.mp (Classical.not_not.mp hv)
  -- there is no ring homomorphism to `ℝ`: the prime-`2` correction
  have hno : ¬ ∃ φ : w.Completion →+* ℝ, True :=
    Work.SSG8Escape.localField_not_real_of_no_involutions p K ζ hζ hKimag
      (NK.GlobalCFT.Place.ofInfinite w) (by simp)
  have hC : w.IsComplex := by
    rw [← NumberField.InfinitePlace.not_isReal_iff_isComplex]
    intro hR
    exact hno ⟨NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hR, trivial⟩
  let e : w.Completion ≃+* ℂ :=
    NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hC
  -- every local unit has an `Fintype.card G`-th root, because this holds in `ℂ`
  have hcard : 0 < Fintype.card G := Fintype.card_pos
  obtain ⟨z, hz⟩ : ∃ z : (w.Completion)ˣ, z ^ Fintype.card G = u := by
    obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (e (u : w.Completion)) hcard
    have hc0 : c ≠ 0 := by
      intro h0
      have h1 : (u : w.Completion) = 0 := by
        refine e.injective ?_
        rw [map_zero, ← hc, h0, zero_pow hcard.ne']
      exact Units.ne_zero u h1
    have hc0' : e.symm c ≠ 0 := by
      intro h0
      refine hc0 ?_
      rw [← RingEquiv.apply_symm_apply e c, h0, map_zero]
    refine ⟨Units.mk0 (e.symm c) hc0', ?_⟩
    have hval : ((Units.mk0 (e.symm c) hc0' ^ Fintype.card G : (w.Completion)ˣ) : w.Completion)
        = (u : w.Completion) := by
      rw [Units.val_pow_eq_pow_val, Units.val_mk0]
      exact e.injective (by rw [map_pow, RingEquiv.apply_symm_apply, hc])
    exact Units.ext hval
  -- a homomorphism from a rootable group to a finite group is trivial
  have hone : NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofInfinite w)
      (z ^ Fintype.card G) =
      (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofInfinite w) z) ^ Fintype.card G := by
    rw [← NK.CFTLib.IdeleHasse.onePlaceHom_apply (K := ↥K)
        (NK.GlobalCFT.Place.ofInfinite w) (z ^ Fintype.card G),
      ← NK.CFTLib.IdeleHasse.onePlaceHom_apply (K := ↥K)
        (NK.GlobalCFT.Place.ofInfinite w) z,
      map_pow]
  rw [← hz, hone, map_pow]
  exact pow_card_eq_one

/-- **The local decomposition of a global unit at a finite prime, with the exponent matched.**  The
local component `a_q` of a global unit `a` is `ϖ_q ^ e` times a local unit, where `e` is the
`q`-adic exponent of the principal idèle of `a`. -/
theorem localImageAt_unifUnit_decomp_aux {K : Type} [Field K] [NumberField K]
    (a : Kˣ) (q : NK.Chebotarev.PrimeIdeal K) :
    ∃ u ∈ NK.GlobalCFT.Place.localUnits K (NK.GlobalCFT.Place.ofFinite q),
      NK.CFTLib.IdeleHasse.localImageAt (K := K) (NK.GlobalCFT.Place.ofFinite q) a =
        (NK.GlobalCFT.IdeleClassGroup.unifUnit K q) ^
          (NK.GlobalCFT.Idele.exp q (NK.GlobalCFT.Idele.principalIdele K a)) * u := by
  classical
  set n : ℤ := NK.GlobalCFT.Idele.exp q (NK.GlobalCFT.Idele.principalIdele K a) with hn
  refine ⟨(NK.GlobalCFT.IdeleClassGroup.unifUnit K q) ^ (-n)
      * NK.CFTLib.IdeleHasse.localImageAt (K := K) (NK.GlobalCFT.Place.ofFinite q) a, ?_, ?_⟩
  · -- the correction is a local unit: its valuation is `1`
    rw [NK.GlobalCFT.Place.mem_localUnits_ofFinite_iff_valued_eq_one]
    have hcoe : ((((NK.GlobalCFT.IdeleClassGroup.unifUnit K q) ^ (-n)
          * NK.CFTLib.IdeleHasse.localImageAt (K := K) (NK.GlobalCFT.Place.ofFinite q) a :
            (q.adicCompletion K)ˣ) : q.adicCompletion K))
        = ((((NK.GlobalCFT.IdeleClassGroup.unifUnit K q) ^ (-n) :
              (q.adicCompletion K)ˣ) : q.adicCompletion K))
          * (NK.CFTLib.IdeleHasse.localImageAt (K := K) (NK.GlobalCFT.Place.ofFinite q) a :
              q.adicCompletion K) := Units.val_mul _ _
    rw [hcoe, map_mul, NK.GlobalCFT.IdeleClassGroup.valued_unifUnit_zpow, hn]
    have hexp : Valued.v ((NK.CFTLib.IdeleHasse.localImageAt (K := K)
          (NK.GlobalCFT.Place.ofFinite q) a : (q.adicCompletion K)ˣ) : q.adicCompletion K)
        = WithZero.exp (-(NK.GlobalCFT.Idele.exp q
            (NK.GlobalCFT.Idele.principalIdele K a))) := by
      rw [← Work.SSGRoute.ZDataMup.principalIdele_apply_eq_localImageAt (K := K) a
        (NK.GlobalCFT.Place.ofFinite q)]
      exact Idele.exp_val q (Idele.principalIdele K a)
    rw [hexp, ← WithZero.exp_add]
    simp
  · -- the decomposition itself: `ϖ^n · (ϖ^{-n} · b) = b`
    rw [← mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, one_mul]

/-- **The character of the Artin symbol of a fractional ideal, in terms of the uniformiser
parts.**  For `Φ : 𝕀_K →* Gal(L/K)` and `χ : Gal(L/K) →* Multiplicative (ZMod p)`, the value of
`χ ∘ Φ` on `fracIdele 𝔵` is the sum, over the primes occurring in `𝔵`, of the exponent times the
value at the local factor `Φ (onePlace (ofFinite q) (unifUnit K q))`.  No arithmetic is involved:
`fracIdele 𝔵 = ∏_q ideleOfPrime q ^ count q 𝔵` and `ideleOfPrime q = onePlace q (unifUnit K q)`. -/
theorem chi_fracIdele_sum_unifUnit_aux (p : ℕ) {K L : Type} [Field K] [NumberField K]
    [Field L] [Algebra K L]
    (Φ : NK.GlobalCFT.Idele K →* (L ≃ₐ[K] L))
    (χ : (L ≃ₐ[K] L) →* Multiplicative (ZMod p))
    (𝔵 : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K) :
    (χ (Φ (NK.NUV2.RouteB.RayModulus.fracIdele 𝔵))).toAdd =
      ∑ q ∈ (FractionalIdeal.finite_factors 𝔵).toFinset,
        (FractionalIdeal.count K q 𝔵 : ZMod p) *
          (χ (Φ (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite q)
            (NK.GlobalCFT.IdeleClassGroup.unifUnit K q)))).toAdd := by
  classical
  set S : Finset (NK.Chebotarev.PrimeIdeal K) := (FractionalIdeal.finite_factors 𝔵).toFinset
    with hS
  have hsupp : ∀ q : NK.Chebotarev.PrimeIdeal K, q ∉ S → FractionalIdeal.count K q 𝔵 = 0 := by
    intro q hq
    by_contra h
    exact hq (by rw [hS]; exact (Set.Finite.mem_toFinset _).mpr h)
  -- `fracIdele 𝔵` as a finite product of prime idèles
  have hfrac : NK.NUV2.RouteB.RayModulus.fracIdele 𝔵 = ∏ q ∈ S,
      (NK.HeckeL.ideleOfPrime K q) ^ (FractionalIdeal.count K q 𝔵) := by
    rw [show NK.NUV2.RouteB.RayModulus.fracIdele 𝔵 =
        NK.GlobalCFT.IdeleClassGroup.ideleOfFun K (fun q => FractionalIdeal.count K q 𝔵)
          (FractionalIdeal.finite_factors 𝔵) from rfl, hS]
    exact Work.SSGRoute.N4Escape.ideleOfFun_eq_prod_ideleOfPrime S _ _ hsupp
  -- the additive form of the multiplicativity of `.toAdd`
  have hmul : ∀ a b : Multiplicative (ZMod p), (a * b).toAdd = a.toAdd + b.toAdd := by
    intro a b
    simpa using (Multiplicative.ofAdd_add (a.toAdd) (b.toAdd)).symm
  -- the term at a single prime
  have hterm : ∀ q : NK.Chebotarev.PrimeIdeal K,
      (χ (Φ ((NK.HeckeL.ideleOfPrime K q) ^ (FractionalIdeal.count K q 𝔵)))).toAdd
        = (FractionalIdeal.count K q 𝔵 : ZMod p) *
            (χ (Φ (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite q)
              (NK.GlobalCFT.IdeleClassGroup.unifUnit K q)))).toAdd := by
    intro q
    rw [← NK.NUV2.ARL.onePlace_unifUnit_eq_ideleOfPrime (K := K) q, map_zpow, map_zpow]
    have h : ((χ (Φ (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite q)
        (NK.GlobalCFT.IdeleClassGroup.unifUnit K q)))) ^ (FractionalIdeal.count K q 𝔵)).toAdd
        = (FractionalIdeal.count K q 𝔵) •
          (χ (Φ (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite q)
            (NK.GlobalCFT.IdeleClassGroup.unifUnit K q)))).toAdd := by simp
    rw [h, zsmul_eq_mul]
  -- the induction on finite sets of primes (products are taken in the commutative idèle group only)
  have hind : ∀ s : Finset (NK.Chebotarev.PrimeIdeal K),
      (χ (Φ (∏ q ∈ s, (NK.HeckeL.ideleOfPrime K q) ^ (FractionalIdeal.count K q 𝔵)))).toAdd
        = ∑ q ∈ s, (FractionalIdeal.count K q 𝔵 : ZMod p) *
            (χ (Φ (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite q)
              (NK.GlobalCFT.IdeleClassGroup.unifUnit K q)))).toAdd := by
    intro s
    induction s using Finset.induction with
    | empty => simp
    | insert a s ha ih =>
        rw [Finset.prod_insert ha, map_mul, map_mul, hmul, hterm a, ih, Finset.sum_insert ha]
  rw [hfrac, hind S]

/-- **Artin fixes the symbol of the `T'`-free part of `div a` once the local factors cancel**
(variant in which the unramifiedness hypothesis of `artin_fixes_of_local_factors` is replaced by the
explicit statement that the local units at primes outside `T'` are killed by `Φ`). -/
theorem artin_fixes_of_local_units
    (p : ℕ) [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p)
    (hKimag : p = 2 → ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → c = 1)
    (F : IntermediateField ↥K Ω) [FiniteDimensional ↥K F] [IsGalois ↥K F] [NumberField ↥F]
    [IsMulCommutative (↥F ≃ₐ[↥K] ↥F)]
    (c : (↥K)ˣ) (hc : NK.LocalAnabelian.kummerField (p := p) (K' := Ω) c ≤ F)
    (χ : (↥F ≃ₐ[↥K] ↥F) →* Multiplicative (ZMod p))
    (hχ : ∀ σ : Ω ≃ₐ[↥K] Ω,
      χ (AlgEquiv.restrictNormalHom F σ) =
        Multiplicative.ofAdd (Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ c σ))
    (a : (↥K)ˣ) (T' : Finset (NK.Chebotarev.PrimeIdeal ↥K))
    (Φ : NK.GlobalCFT.Idele ↥K →* (↥F ≃ₐ[↥K] ↥F))
    (hΦprin : ∀ x : (↥K)ˣ, Φ (NK.GlobalCFT.Idele.principalIdele ↥K x) = 1)
    (hΦnorm : ∀ y : NK.GlobalCFT.Idele ↥F, Φ (NK.GlobalCFT.Idele.normIdeleHom ↥K ↥F y) = 1)
    (hunits : ∀ 𝔮 : NK.Chebotarev.PrimeIdeal ↥K, 𝔮 ∉ T' →
      ∀ u : (NK.GlobalCFT.Place.localField ↥K (NK.GlobalCFT.Place.ofFinite 𝔮))ˣ,
        u ∈ NK.GlobalCFT.Place.localUnits ↥K (NK.GlobalCFT.Place.ofFinite 𝔮) →
        Φ (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔮) u) = 1)
    (hTfix : (∏ 𝔭 ∈ T', χ (Φ (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔭)
        (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofFinite 𝔭) a)))) = 1) :
    χ (Φ (NK.NUV2.RouteB.RayModulus.fracIdele (Work.SSGRoute.tFreePart (K := ↥K) T' a))) = 1 := by
  classical
  haveI : IsAlgClosed Ω := (inferInstance : IsAlgClosure k Ω).isAlgClosed
  have hcomm : ∀ x y : (↥F ≃ₐ[↥K] ↥F), x * y = y * x := fun x y => mul_comm' x y
  -- ## The idèle-summands occurring in the computation
  -- the finite set of primes: `T'` together with the primes where `a` has non-zero valuation
  set S' : Finset (NK.Chebotarev.PrimeIdeal ↥K) :=
    T' ∪ (Idele.finite_exp_support (Idele.principalIdele ↥K a)).toFinset with hS'
  set sF : Finset (NK.GlobalCFT.Place ↥K) := S'.image NK.GlobalCFT.Place.ofFinite with hsF
  set sI : Finset (NK.GlobalCFT.Place ↥K) :=
    (Finset.univ : Finset (NumberField.InfinitePlace ↥K)).image
      NK.GlobalCFT.Place.ofInfinite with hsI
  set s : Finset (NK.GlobalCFT.Place ↥K) := sF ∪ sI with hs
  -- ## The local factors outside `s` are trivial
  have hvanish : ∀ v : NK.GlobalCFT.Place ↥K, v ∉ s →
      Φ (NK.HassePrinciple.onePlace v (NK.CFTLib.IdeleHasse.localImageAt v a)) = 1 := by
    intro v hv
    by_cases hfin : v.IsFinite
    · obtain ⟨q, rfl⟩ := NK.GlobalCFT.Place.isFinite_iff.mp hfin
      have hq : q ∉ S' := by
        intro hmem
        exact hv (by
          rw [hs, hsF]
          exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hmem))
      have hqT : q ∉ T' := fun h => hq (by rw [hS']; exact Finset.mem_union_left _ h)
      have hexp : Idele.exp q (Idele.principalIdele ↥K a) = 0 := by
        by_contra hne
        exact hq (by
          rw [hS']
          exact Finset.mem_union_right _ ((Set.Finite.mem_toFinset _).mpr hne))
      obtain ⟨u, hu, hdec⟩ := localImageAt_unifUnit_decomp_aux (K := ↥K) a q
      have haq : NK.CFTLib.IdeleHasse.localImageAt (K := ↥K)
          (NK.GlobalCFT.Place.ofFinite q) a = u := by
        rw [hdec, hexp, zpow_zero, one_mul]
      rw [haq]
      exact hunits q hqT u hu
    · have hinf : v.IsInfinite := Classical.not_not.mp hfin
      obtain ⟨w, rfl⟩ := NK.GlobalCFT.Place.isInfinite_iff.mp hinf
      exact absurd (by
        rw [hs, hsI]
        exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ w))) hv
  -- ## The product formula and its character-version
  have hprod : NK.CFTLib.IdeleHasse.cprod hcomm s
      (fun v => Φ (NK.HassePrinciple.onePlace v (NK.CFTLib.IdeleHasse.localImageAt v a)))
      = 1 :=
    Work.SSGRoute.ZDataMup.cprod_localFactor_eq_one (K := ↥K) (L := ↥F) hcomm Φ hΦprin
      hΦnorm a s hvanish
  have hsum : ∑ v ∈ s, (χ (Φ (NK.HassePrinciple.onePlace v
      (NK.CFTLib.IdeleHasse.localImageAt v a)))).toAdd = 0 := by
    have h1 : (χ (NK.CFTLib.IdeleHasse.cprod hcomm s
        (fun v => Φ (NK.HassePrinciple.onePlace v
          (NK.CFTLib.IdeleHasse.localImageAt v a))))).toAdd = 0 := by
      rw [hprod]
      simp
    rw [Work.SSGRoute.GrunwaldEscapeCore.cprod_map_prod hcomm χ s
      (fun v => Φ (NK.HassePrinciple.onePlace v (NK.CFTLib.IdeleHasse.localImageAt v a)))] at h1
    rw [Work.SSGRoute.GrunwaldEscapeCore.toAdd_prod_eq_sum p] at h1
    exact h1
  -- ## Splitting the sum
  have hdisj : Disjoint sF sI := by
    rw [Finset.disjoint_left]
    intro v hv1 hv2
    rw [hsF] at hv1
    obtain ⟨q, -, hq⟩ := Finset.mem_image.mp hv1
    rw [hsI] at hv2
    obtain ⟨w, -, hw⟩ := Finset.mem_image.mp hv2
    exact NK.GlobalCFT.Place.ofInfinite_ne_ofFinite w q (hw.trans hq.symm)
  have hsplit : ∑ v ∈ sF, (χ (Φ (NK.HassePrinciple.onePlace v
        (NK.CFTLib.IdeleHasse.localImageAt v a)))).toAdd
      + ∑ v ∈ sI, (χ (Φ (NK.HassePrinciple.onePlace v
        (NK.CFTLib.IdeleHasse.localImageAt v a)))).toAdd = 0 := by
    have hunion := Finset.sum_union (f := fun v => (χ (Φ (NK.HassePrinciple.onePlace v
      (NK.CFTLib.IdeleHasse.localImageAt v a)))).toAdd) hdisj
    rw [← hunion, ← hs]
    exact hsum
  -- the archimedean places contribute nothing
  have hIzero : ∑ v ∈ sI, (χ (Φ (NK.HassePrinciple.onePlace v
      (NK.CFTLib.IdeleHasse.localImageAt v a)))).toAdd = 0 := by
    refine Finset.sum_eq_zero fun v hv => ?_
    rw [hsI] at hv
    obtain ⟨w, -, hw⟩ := Finset.mem_image.mp hv
    obtain rfl : v = NK.GlobalCFT.Place.ofInfinite w := hw.symm
    have h1 : (χ (Φ (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofInfinite w)
        (NK.CFTLib.IdeleHasse.localImageAt (NK.GlobalCFT.Place.ofInfinite w) a)))).toAdd = 0 := by
      rw [arch_localFactor_eq_one_aux p K ζ hζ hKimag Φ (NK.GlobalCFT.Place.ofInfinite w)
        (by simp [NK.GlobalCFT.Place.IsFinite])
        (NK.CFTLib.IdeleHasse.localImageAt (NK.GlobalCFT.Place.ofInfinite w) a), map_one]
      simp
    exact h1
  have hFzero : ∑ v ∈ sF, (χ (Φ (NK.HassePrinciple.onePlace v
      (NK.CFTLib.IdeleHasse.localImageAt v a)))).toAdd = 0 := by
    have h2 := hsplit
    rw [hIzero, add_zero] at h2
    exact h2
  -- reindex the finite places
  have hS'zero : ∑ q ∈ S', (χ (Φ (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite q)
      (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K)
        (NK.GlobalCFT.Place.ofFinite q) a)))).toAdd = 0 := by
    have hinj : Set.InjOn (NK.GlobalCFT.Place.ofFinite)
        (↑S' : Set (NK.Chebotarev.PrimeIdeal ↥K)) :=
      fun x _ y _ h => NK.GlobalCFT.Place.ofFinite_inj.mp h
    have h2 := Finset.sum_image (f := fun v => (χ (Φ (NK.HassePrinciple.onePlace v
        (NK.CFTLib.IdeleHasse.localImageAt v a)))).toAdd) (s := S')
      (g := NK.GlobalCFT.Place.ofFinite) hinj
    rw [← h2, ← hsF]
    exact hFzero
  -- the terms over `T'` vanish by hypothesis
  have hT'sum : ∑ q ∈ T', (χ (Φ (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite q)
      (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K)
        (NK.GlobalCFT.Place.ofFinite q) a)))).toAdd = 0 := by
    have h1 := congrArg Multiplicative.toAdd hTfix
    rw [Work.SSGRoute.GrunwaldEscapeCore.toAdd_prod_eq_sum p] at h1
    simpa using h1
  have hsdiff : ∑ q ∈ S' \ T', (χ (Φ (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite q)
      (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K)
        (NK.GlobalCFT.Place.ofFinite q) a)))).toAdd = 0 := by
    have hsub : T' ⊆ S' := by
      intro q hq
      rw [hS']
      exact Finset.mem_union_left _ hq
    have h3 := Finset.sum_sdiff (f := fun q => (χ (Φ (NK.HassePrinciple.onePlace
      (NK.GlobalCFT.Place.ofFinite q) (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K)
        (NK.GlobalCFT.Place.ofFinite q) a)))).toAdd) hsub
    rw [hT'sum, hS'zero, add_zero] at h3
    exact h3
  -- ## The term-wise identification at the primes outside `T'`
  have hterm : ∀ q ∈ S' \ T',
      (χ (Φ (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite q)
        (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K)
          (NK.GlobalCFT.Place.ofFinite q) a)))).toAdd
      = (FractionalIdeal.count ↥K q (Work.SSGRoute.tFreePart (K := ↥K) T' a) : ZMod p)
          * (χ (Φ (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite q)
            (NK.GlobalCFT.IdeleClassGroup.unifUnit ↥K q)))).toAdd := by
    intro q hq
    rw [Finset.mem_sdiff] at hq
    obtain ⟨-, hqT'⟩ := hq
    obtain ⟨u, hu, hdec⟩ := localImageAt_unifUnit_decomp_aux (K := ↥K) a q
    have hkill : Φ (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite q) u) = 1 :=
      hunits q hqT' u hu
    have hcount : FractionalIdeal.count ↥K q (Work.SSGRoute.tFreePart (K := ↥K) T' a)
        = Idele.exp q (Idele.principalIdele ↥K a) :=
      Work.SSGRoute.tFreePart_count_eq_exp T' a hqT'
    -- the one-place idèle of a product is the product of the one-place idèles
    have hone : NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite q)
        ((NK.GlobalCFT.IdeleClassGroup.unifUnit ↥K q)
            ^ (Idele.exp q (Idele.principalIdele ↥K a)) * u)
        = (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite q)
            (NK.GlobalCFT.IdeleClassGroup.unifUnit ↥K q))
          ^ (Idele.exp q (Idele.principalIdele ↥K a))
          * NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite q) u := by
      rw [← NK.CFTLib.IdeleHasse.onePlaceHom_apply (K := ↥K) (NK.GlobalCFT.Place.ofFinite q)
            ((NK.GlobalCFT.IdeleClassGroup.unifUnit ↥K q)
              ^ (Idele.exp q (Idele.principalIdele ↥K a)) * u),
          ← NK.CFTLib.IdeleHasse.onePlaceHom_apply (K := ↥K) (NK.GlobalCFT.Place.ofFinite q)
            (NK.GlobalCFT.IdeleClassGroup.unifUnit ↥K q),
          ← NK.CFTLib.IdeleHasse.onePlaceHom_apply (K := ↥K) (NK.GlobalCFT.Place.ofFinite q) u,
          map_mul, map_zpow]
    have hstep : Φ ((NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite q)
          (NK.GlobalCFT.IdeleClassGroup.unifUnit ↥K q))
          ^ (Idele.exp q (Idele.principalIdele ↥K a))
          * NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite q) u)
        = (Φ (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite q)
            (NK.GlobalCFT.IdeleClassGroup.unifUnit ↥K q)))
          ^ (Idele.exp q (Idele.principalIdele ↥K a)) := by
      rw [map_mul, map_zpow, hkill, mul_one]
    rw [hdec, hone, hstep, map_zpow]
    rw [show ((χ (Φ (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite q)
          (NK.GlobalCFT.IdeleClassGroup.unifUnit ↥K q))))
          ^ (Idele.exp q (Idele.principalIdele ↥K a))).toAdd
        = (Idele.exp q (Idele.principalIdele ↥K a))
            • (χ (Φ (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite q)
              (NK.GlobalCFT.IdeleClassGroup.unifUnit ↥K q)))).toAdd from rfl,
      zsmul_eq_mul, hcount]
  -- ## Assembly
  have hkey : (χ (Φ (NK.NUV2.RouteB.RayModulus.fracIdele
      (Work.SSGRoute.tFreePart (K := ↥K) T' a)))).toAdd = 0 := by
    rw [chi_fracIdele_sum_unifUnit_aux p Φ χ (Work.SSGRoute.tFreePart (K := ↥K) T' a)]
    have hmem : ∀ q, q ∈ (FractionalIdeal.finite_factors
        (Work.SSGRoute.tFreePart (K := ↥K) T' a)).toFinset ↔
        FractionalIdeal.count ↥K q (Work.SSGRoute.tFreePart (K := ↥K) T' a) ≠ 0 :=
      fun q => Set.Finite.mem_toFinset _
    have hsub : S' \ T' ⊆ (FractionalIdeal.finite_factors
        (Work.SSGRoute.tFreePart (K := ↥K) T' a)).toFinset := by
      intro q hq
      rw [Finset.mem_sdiff] at hq
      obtain ⟨hqS', hqT'⟩ := hq
      rw [hmem q]
      rw [Work.SSGRoute.tFreePart_count_eq_exp T' a hqT']
      rw [hS'] at hqS'
      rcases Finset.mem_union.mp hqS' with h | h
      · exact absurd h hqT'
      · exact (Set.Finite.mem_toFinset _).mp h
    have hzero : ∀ x ∈ (FractionalIdeal.finite_factors
          (Work.SSGRoute.tFreePart (K := ↥K) T' a)).toFinset, x ∉ S' \ T' →
        (FractionalIdeal.count ↥K x (Work.SSGRoute.tFreePart (K := ↥K) T' a) : ZMod p)
          * (χ (Φ (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite x)
            (NK.GlobalCFT.IdeleClassGroup.unifUnit ↥K x)))).toAdd = 0 := by
      intro x _ hxnot
      have hcount0 : FractionalIdeal.count ↥K x (Work.SSGRoute.tFreePart (K := ↥K) T' a) = 0 := by
        by_cases hxT : x ∈ T'
        · exact Work.SSGRoute.tFreePart_count_eq_zero T' a hxT
        · have hxnotS' : x ∉ S' := by
            intro hmem
            exact hxnot (Finset.mem_sdiff.mpr ⟨hmem, hxT⟩)
          have hexp0 : Idele.exp x (Idele.principalIdele ↥K a) = 0 := by
            by_contra hne
            exact hxnotS' (by
              rw [hS']
              exact Finset.mem_union_right _ ((Set.Finite.mem_toFinset _).mpr hne))
          rw [Work.SSGRoute.tFreePart_count_eq_exp T' a hxT, hexp0]
      rw [hcount0, Int.cast_zero, zero_mul]
    rw [← Finset.sum_subset hsub hzero]
    rw [Finset.sum_congr rfl (fun q hq => (hterm q hq).symm)]
    exact hsdiff
  refine Multiplicative.toAdd.injective ?_
  rw [hkey]
  rfl

end Work.SSGRoute.N2v2
