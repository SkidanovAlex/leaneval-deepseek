import Mathlib
import Submission.Work.MotV5.Nodes.UEPR.map_maximalIdeal_eq_of_ramificationIdx_eq_one

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotV5.Nodes.UEPR

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option maxHeartbeats 3200000

/-
**Ramification forces `e ≠ 1`.**  In the setting of the bridge
(`V = w.valuationSubring =` the localization of `B = integralClosure A Ω` at `P`, with
`A = v.valuationSubring`), if the extension `w` of `v` is ramified in the sense that its value
group is strictly bigger than the image of the value group of `v` (the hypothesis `hram`), then the
ramification index of `P` over `m_A` is not `1` (it is in fact `≥ 2`, but `≠ 1` is what is needed).

Proof route:
1. `haveI` the DVR/Dedekind instances; let `Vloc := Localization.subalgebra.ofField Ω P.primeCompl hP`
   so that `↥Vloc ≅ Localization.AtPrime P` (`IsLocalization.algEquiv`), `IsFractionRing ↥Vloc Ω`,
   `IsDiscreteValuationRing ↥Vloc`.
2. Suppose `P.ramificationIdx ↥A = 1`.  By
   `Work.MotV5.Nodes.UEPR.map_maximalIdeal_eq_of_ramificationIdx_eq_one`
   (`Submission.Work.MotV5.Nodes.UEPR.map_maximalIdeal_eq_of_ramificationIdx_eq_one`) applied with
   `q := P` and transferred along `IsLocalization.algEquiv` (note the sibling file
   `Submission/Work/MotR/R4/invariance_of_totallyRamified_place.lean`, step 5, does the same
   transfer),
   `Ideal.map (algebraMap ↥A ↥Vloc) m_A = IsLocalRing.maximalIdeal ↥Vloc`.
3. Choose a uniformizer `ϖ` of the DVR `↥A` (so `m_A = Ideal.span {ϖ}`); then
   `IsLocalRing.maximalIdeal ↥Vloc = Ideal.span {algebraMap ↥A ↥Vloc ϖ}`, i.e. `ϖ` is also a
   uniformizer of `↥Vloc`.
4. For `y ≠ 0` in `Ω`, `IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible` writes
   `y = u • (algebraMap ↥Vloc Ω (algebraMap ↥A ↥Vloc ϖ)) ^ n` with `u : (↥Vloc)ˣ`, `n : ℤ`; the image
   of `u` is a unit of `w.valuationSubring` (use `hbridge`), hence `w` of it is `1`, so
   `w y = w (algebraMap F Ω ϖ) ^ n = f (v ϖ) ^ n = f (v ((ϖ : F) ^ n))`, i.e. `w y = f (v x)` for
   some `x : F` with `x ≠ 0`.
5. This contradicts `hram`.
-/
theorem ramificationIdx_ne_one {F Ω Γ : Type*} [Field F] [Field Ω] [Algebra F Ω] [FiniteDimensional F Ω] [IsGalois F Ω] (v : Valuation F (WithZero (Multiplicative ℤ))) (hv : v.IsNontrivial) [LinearOrderedCommGroupWithZero Γ] (f : WithZero (Multiplicative ℤ) →*₀ Γ) (hf : StrictMono f) (w : Valuation Ω Γ) (hw : ∀ x : F, w (algebraMap F Ω x) = f (v x)) (hram : ∃ y : Ω, y ≠ 0 ∧ ∀ x : F, x ≠ 0 → w y ≠ f (v x)) (P : Ideal ↥(integralClosure ↥(v.valuationSubring) Ω)) [P.IsPrime] [P.LiesOver (IsLocalRing.maximalIdeal ↥(v.valuationSubring))] (hP : P.primeCompl ≤ nonZeroDivisors ↥(integralClosure ↥(v.valuationSubring) Ω)) [IsFractionRing ↥(integralClosure ↥(v.valuationSubring) Ω) Ω] (hbridge : w.valuationSubring.toSubring = (Localization.subalgebra.ofField Ω P.primeCompl hP).toSubring) : P.ramificationIdx ↥(v.valuationSubring) ≠ 1 := by
  classical
  haveI hv' : v.IsNontrivial := hv
  let A := ↥(v.valuationSubring)
  let B := ↥(integralClosure ↥(v.valuationSubring) Ω)
  let Vloc := Localization.subalgebra.ofField Ω P.primeCompl hP
  -- ## 0. the structural instances
  haveI hLRA : IsLocalRing A := inferInstance
  haveI hDedA : IsDedekindDomain A := inferInstance
  haveI hFracA : IsFractionRing A F := inferInstance
  haveI hDVR_A : IsDiscreteValuationRing A := inferInstance
  haveI hIcB : IsIntegralClosure B A Ω := inferInstance
  haveI hDomB : IsDomain B := inferInstance
  haveI hDedB : IsDedekindDomain B := IsIntegralClosure.isDedekindDomain A F Ω B
  haveI hSTABΩ : IsScalarTower A B Ω := inferInstance
  haveI hSTBVΩ : IsScalarTower B ↥Vloc Ω := inferInstance
  haveI hSTAFΩ : IsScalarTower A F Ω := inferInstance
  haveI hLocV : IsLocalization P.primeCompl ↥Vloc := inferInstance
  haveI hLocPV : IsLocalization.AtPrime ↥Vloc P := inferInstance
  haveI hFrV : IsFractionRing ↥Vloc Ω := inferInstance
  haveI hLRV : IsLocalRing ↥Vloc := IsLocalization.AtPrime.isLocalRing ↥Vloc P
  -- ## 1. `P ≠ ⊥`
  have hmA_ne_bot : IsLocalRing.maximalIdeal A ≠ ⊥ := by
    intro hbot
    obtain ⟨x, hx0, hx1⟩ := hv.exists_lt_one
    have hxA : x ∈ v.valuationSubring := le_of_lt hx1
    have hxmem : (⟨x, hxA⟩ : A) ∈ IsLocalRing.maximalIdeal A := by
      rw [Valuation.mem_maximalIdeal_iff]; exact hx1
    rw [hbot] at hxmem
    have hxz : (⟨x, hxA⟩ : A) = 0 := by simpa using hxmem
    exact hx0 (congrArg Subtype.val hxz)
  have hinjAB : Function.Injective (algebraMap A B) := by
    intro a b hab
    have h2 : algebraMap A F a = algebraMap A F b := by
      apply (algebraMap F Ω).injective
      show algebraMap F Ω (algebraMap A F a) = algebraMap F Ω (algebraMap A F b)
      rw [← IsScalarTower.algebraMap_apply A F Ω a,
        ← IsScalarTower.algebraMap_apply A F Ω b,
        IsScalarTower.algebraMap_apply A B Ω a,
        IsScalarTower.algebraMap_apply A B Ω b, hab]
    exact IsFractionRing.injective A F h2
  have hPne : P ≠ ⊥ := by
    intro hbot
    have h2 : P.under A = ⊥ := by
      rw [hbot]
      exact Ideal.comap_bot_of_injective (f := algebraMap A B) hinjAB
    exact hmA_ne_bot ((Ideal.over_def P (IsLocalRing.maximalIdeal A)).trans h2)
  haveI hDVR_V : IsDiscreteValuationRing ↥Vloc :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain B hPne ↥Vloc
  intro hramidx
  -- ## 2. the maximal ideal of `A` maps onto the maximal ideal of the localization at `P`
  haveI hmAprime : (IsLocalRing.maximalIdeal A).IsPrime :=
    (IsLocalRing.maximalIdeal.isMaximal A).isPrime
  have h₁ : Ideal.map (algebraMap A (Localization.AtPrime P)) (IsLocalRing.maximalIdeal A)
      = IsLocalRing.maximalIdeal (Localization.AtPrime P) :=
    map_maximalIdeal_eq_of_ramificationIdx_eq_one (IsLocalRing.maximalIdeal A) P hramidx
  -- ## 3. transfer to `Vloc` and build the uniformizer
  let e : Localization.AtPrime P ≃ₐ[B] ↥Vloc :=
    IsLocalization.algEquiv P.primeCompl (Localization.AtPrime P) ↥Vloc
  let φ : A →+* ↥Vloc := (algebraMap B ↥Vloc).comp (algebraMap A B)
  have hφe : ∀ a : A, e (algebraMap A (Localization.AtPrime P) a) = φ a := by
    intro a
    rw [IsScalarTower.algebraMap_apply A B (Localization.AtPrime P)]
    exact e.commutes (algebraMap A B a)
  obtain ⟨ϖ, hϖirr⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hspanA : IsLocalRing.maximalIdeal A = Ideal.span {ϖ} := hϖirr.maximalIdeal_eq
  have hspanS : IsLocalRing.maximalIdeal (Localization.AtPrime P)
      = Ideal.span {algebraMap A (Localization.AtPrime P) ϖ} := by
    rw [← h₁, hspanA, Ideal.map_span, Set.image_singleton]
  haveI hDVR_S : IsDiscreteValuationRing (Localization.AtPrime P) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain B hPne _
  have hirrS : Irreducible (algebraMap A (Localization.AtPrime P) ϖ) :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer
      (algebraMap A (Localization.AtPrime P) ϖ)).mpr hspanS
  have hirrT : Irreducible (e (algebraMap A (Localization.AtPrime P) ϖ)) :=
    (MulEquiv.irreducible_iff e.toRingEquiv.toMulEquiv).mpr hirrS
  have hirrφ : Irreducible (φ ϖ) := by
    rw [show φ ϖ = e (algebraMap A (Localization.AtPrime P) ϖ) from (hφe ϖ).symm]
    exact hirrT
  -- ## 4. units of `Vloc` have valuation `1`
  have hunit : ∀ u : (↥Vloc)ˣ, w (algebraMap ↥Vloc Ω (u : ↥Vloc)) = 1 := by
    intro u
    have hmem : ∀ z : ↥Vloc, algebraMap ↥Vloc Ω z ∈ w.valuationSubring.toSubring := by
      intro z
      rw [hbridge]
      exact Subalgebra.mem_toSubring.mpr z.2
    have hle : ∀ z : ↥Vloc, w (algebraMap ↥Vloc Ω z) ≤ 1 := fun z =>
      (Valuation.mem_valuationSubring_iff w _).mp
        ((ValuationSubring.mem_toSubring _ _).mp (hmem z))
    have h1 : w (algebraMap ↥Vloc Ω (u : ↥Vloc)) ≤ 1 := hle _
    have h2 : w (algebraMap ↥Vloc Ω ((u⁻¹ : (↥Vloc)ˣ) : ↥Vloc)) ≤ 1 := hle _
    have h3 : w (algebraMap ↥Vloc Ω (u : ↥Vloc))
        * w (algebraMap ↥Vloc Ω ((u⁻¹ : (↥Vloc)ˣ) : ↥Vloc)) = 1 := by
      rw [← map_mul]
      rw [show algebraMap ↥Vloc Ω (u : ↥Vloc)
            * algebraMap ↥Vloc Ω ((u⁻¹ : (↥Vloc)ˣ) : ↥Vloc) = 1 by
          rw [← map_mul, Units.mul_inv, map_one]]
      exact map_one w
    have hb : (1 : Γ) ≤ w (algebraMap ↥Vloc Ω ((u⁻¹ : (↥Vloc)ˣ) : ↥Vloc)) := by
      have h4 : w (algebraMap ↥Vloc Ω (u : ↥Vloc))
          * w (algebraMap ↥Vloc Ω ((u⁻¹ : (↥Vloc)ˣ) : ↥Vloc))
          ≤ 1 * w (algebraMap ↥Vloc Ω ((u⁻¹ : (↥Vloc)ˣ) : ↥Vloc)) :=
        mul_le_mul_of_nonneg_right h1 zero_le
      rw [one_mul] at h4
      rwa [h3] at h4
    rw [le_antisymm h2 hb, mul_one] at h3
    exact h3
  -- ## 5. every nonzero value of `w` is in the image of `f ∘ v`
  have key : ∀ y : Ω, y ≠ 0 → ∃ x : F, x ≠ 0 ∧ w y = f (v x) := by
    intro y hy
    obtain ⟨n, u, hu⟩ :=
      IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible (R := ↥Vloc) (K := Ω)
        hirrφ hy
    have hϖne : ϖ ≠ 0 := hϖirr.ne_zero
    have hx0 : algebraMap A F ϖ ≠ 0 := fun hh => hϖne (IsFractionRing.injective A F hh)
    refine ⟨(algebraMap A F ϖ) ^ n, zpow_ne_zero n hx0, ?_⟩
    have hπ : (algebraMap ↥Vloc Ω) (φ ϖ) = algebraMap F Ω (algebraMap A F ϖ) := by
      have h1 : (algebraMap ↥Vloc Ω) (φ ϖ) = algebraMap A Ω ϖ := by
        show algebraMap ↥Vloc Ω (algebraMap B ↥Vloc (algebraMap A B ϖ)) = algebraMap A Ω ϖ
        rw [← IsScalarTower.algebraMap_apply B ↥Vloc Ω,
          ← IsScalarTower.algebraMap_apply A B Ω]
      rw [h1, IsScalarTower.algebraMap_apply A F Ω]
    rw [hu, Units.smul_def, Algebra.smul_def, map_mul, hunit u, one_mul, hπ,
      map_zpow₀ w (algebraMap F Ω (algebraMap A F ϖ)) n,
      hw (algebraMap A F ϖ),
      map_zpow₀ v (algebraMap A F ϖ) n,
      map_zpow₀ f (v (algebraMap A F ϖ)) n]
  -- ## 6. contradiction
  obtain ⟨y, hy, hramy⟩ := hram
  obtain ⟨x, hx, hwxy⟩ := key y hy
  exact hramy x hx hwxy

end Work.MotV5.Nodes.UEPR
