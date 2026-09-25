import Mathlib
import Submission.Work.WingbergEndgame.Defs

/-!
# The genus certificate `(ℤ/2)^6 ↠ ...` for the **wide** unramified pro-`2` group of `gsF`

`Work.WingbergRoute.gsM_quotient_of_maximal_continuous` proves that the *narrow* maximal
unramified pro-`2` group `Work.ClassFieldTower.galoisGroup M` of the totally real base
`gsF = ℚ(√(5·13·17·29·37·41·53))` (`Work.WingbergRoute.gsF`) admits a **continuous surjection**
onto the elementary abelian group `(ℤ/2)^6`, by restricting to the unramified multiquadratic
certificate extension

```
gsM = ℚ(√5, √13, √17, √29, √37, √41, √53)  ⊇  gsF ,
```

of degree `2^6 = 64` (`Work.QuadraticFields.gs_certificate`,
`Work.WingbergRoute.gsM_aut_gsF_equiv_pi`).

This module proves the corresponding statement for the **wide** object
`Work.WingbergEndgame.UnramifiedProTwoExtension F` of `Submission/Work/WingbergEndgame/Defs.lean`,
i.e. the maximal pro-`2` extension unramified at the finite *and* the infinite places — the object
that the Martinet route actually needs, because unramifiedness at infinity is what makes all of its
levels totally real.

## Main results

* `Work.WingbergEndgame.exists_continuous_surjection_of_finite_unramified` — the general step: every
  finite everywhere-unramified pro-`2` Galois extension `L/F` of a number field `F` is a
  *continuous* quotient `Gal(F_∞/F) ↠ Gal(L/F)` of the wide maximal pro-`2` extension, and the
  quotient map is continuous for the Krull topology;
* ★ `Work.WingbergEndgame.certificate_quotient_six` — the certificate instance at `gsF`:
  `Gal(gsF_∞/gsF) ↠ (ℤ/2)^6`, continuously.

## How it is proved

The structure `UnramifiedProTwoExtension` records the universal property of `F_∞` (`universal`):
for every finite Galois pro-`2` extension `L/F` with trivial relative different *and* unramified at
the infinite places there is an `F`-embedding `ϕ : L →ₐ[F] F_∞`.  Its image
`E = ϕ.fieldRange ≤ F_∞` is a *finite* subextension, so

* restriction `Gal(F_∞/F) →* Gal(E/F)` is surjective (Mathlib,
  `AlgEquiv.restrictNormalHom_surjective`, since `F_∞/F` is normal),
* restriction is continuous for the Krull topology (Mathlib,
  `InfiniteGalois.restrictNormalHom_continuous`, since `E/F` is finite and normal),
* the transport along `L ≃ₐ[F] E` (`AlgEquiv.autCongr`) is a homeomorphism between discrete
  finite groups.

Continuity is *not* automatic: an arbitrary homomorphism from a compact profinite group to a
finite discrete group need not be continuous.  It is the fact that the map is restriction to a
finite subextension that makes it so.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open scoped Classical
open scoped NumberField
open NumberField

noncomputable section

namespace Work.WingbergEndgame

/-! ## 1. Restriction to a finite everywhere-unramified subextension is a continuous surjection -/

/-- **Every finite everywhere-unramified pro-`2` Galois extension is a continuous quotient of the
wide maximal pro-`2` extension.**

Let `F` be a number field and `F_∞` the maximal pro-`2` extension of `F` unramified at *all*
places, finite and infinite (`UnramifiedProTwoExtension F`).  If `L/F` is a finite Galois extension
with `2`-group Galois group, trivial relative different (unramified at the finite primes) and
unramified at the infinite places, then there is a *surjective continuous* group homomorphism

`Gal(F_∞/F) →* Gal(L/F)`

for the Krull topology on the source and the (discrete) topology on the finite target.

The embedding `L →ₐ[F] F_∞` is the universal property `UnramifiedProTwoExtension.universal`;
restriction of automorphisms to the finite normal subextension `E = ϕ.fieldRange` is surjective and
continuous, and the transport along `L ≃ₐ[F] E` is a map between finite discrete groups. -/
theorem exists_continuous_surjection_of_finite_unramified
    {F : Type*} [Field F] [NumberField F]
    (M : UnramifiedProTwoExtension F) (L : Type) [Field L] [NumberField L]
    [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    (hunr : differentIdeal (𝓞 F) (𝓞 L) = ⊤)
    (hinf : IsUnramifiedAtInfinitePlaces F L)
    (hpg : IsPGroup 2 (L ≃ₐ[F] L)) :
    ∃ φ : galoisGroup M →* (L ≃ₐ[F] L), Function.Surjective φ ∧ Continuous φ := by
  obtain ⟨ϕ, _⟩ := M.universal L hpg hunr hinf
  let E : IntermediateField F M.K := ϕ.fieldRange
  let e : L ≃ₐ[F] ↥E := AlgHom.equivFieldRange ϕ
  haveI hNorE : Normal F ↥E := (IsGalois.of_algEquiv e).to_normal
  haveI hNorK : Normal F M.K := (inferInstance : IsGalois F M.K).to_normal
  haveI hfdE : FiniteDimensional F ↥E := e.toLinearEquiv.finiteDimensional
  haveI hdiscE : DiscreteTopology (↥E ≃ₐ[F] ↥E) :=
    krullTopology_discreteTopology_of_finiteDimensional F ↥E
  refine ⟨(AlgEquiv.autCongr e.symm).toMonoidHom.comp
      (AlgEquiv.restrictNormalHom (F := F) (K₁ := M.K) ↥E), ?_, ?_⟩
  · intro y
    obtain ⟨σ, hσ⟩ := AlgEquiv.restrictNormalHom_surjective (K₁ := ↥E) (M.K)
      ((AlgEquiv.autCongr e.symm).symm y)
    refine ⟨σ, ?_⟩
    show (AlgEquiv.autCongr e.symm) ((AlgEquiv.restrictNormalHom ↥E) σ) = y
    rw [hσ]
    exact (AlgEquiv.autCongr e.symm).apply_symm_apply y
  · have h1 : Continuous (AlgEquiv.restrictNormalHom (F := F) (K₁ := M.K) ↥E) :=
      InfiniteGalois.restrictNormalHom_continuous (k := F) (K := M.K) E
    have h2 : Continuous ((AlgEquiv.autCongr e.symm).toMonoidHom) :=
      continuous_of_discreteTopology (f := ⇑(AlgEquiv.autCongr e.symm).toMonoidHom)
    simpa only [MonoidHom.coe_comp, Function.comp_def] using h2.comp h1

/-! ## 2. The genus certificate at `gsF` -/

/-- **The `(ℤ/2)^6`-quotient of the wide unramified pro-`2` group of `gsF`.**

For *every* wide maximal pro-`2` extension `E` of the totally real quadratic field
`gsF = ℚ(√(5·13·17·29·37·41·53))` (`UnramifiedProTwoExtension gsF`), the Galois group
`Γ = Gal(gsF_∞/gsF)` admits a continuous surjection onto the elementary abelian group
`(ℤ/2)^6 = Fin 6 → Multiplicative (ZMod 2)`, i.e. `(ℤ/2)^6` is a pro-`2` quotient of `Γ`.

The witness is the multiquadratic genus-certificate extension
`gsM = ℚ(√5, √13, √17, √29, √37, √41, √53)` of `gsF`: it is unramified at the finite primes
(`Work.QuadraticFields.gs_unramified`), unramified at the infinite places
(`Work.QuadraticFields.gs_unramified_at_infinite_places`), Galois over `gsF` with
`2`-group Galois group of order `2 ^ 6`, and its Galois group is `(ℤ/2)^6`
(`Work.WingbergRoute.gsM_aut_gsF_equiv_pi`).  The universal property of the wide maximal
extension exhibits `Gal(gsM/gsF)` as a continuous quotient of `Γ`
(`exists_continuous_surjection_of_finite_unramified`), and `(ℤ/2)^6 ≃ Gal(gsM/gsF)` transports
the surjection. -/
theorem certificate_quotient_six (E : Work.WingbergEndgame.UnramifiedProTwoExtension Work.WingbergEndgame.gsF) :
    ∃ φ : Work.WingbergEndgame.galoisGroup E →* (Fin 6 → Multiplicative (ZMod 2)),
      Function.Surjective φ ∧ Continuous φ := by
  classical
  -- `gsM` is Galois over `ℚ` (it is multiquadratic), hence over the intermediate field `gsF`.
  haveI hgalQ : IsGalois ℚ Work.QuadraticFields.gsM :=
    Work.QuadraticFields.multiQuad_isGalois Work.QuadraticFields.gsPrimesQ
  haveI hgal : IsGalois ↥Work.QuadraticFields.gsF Work.QuadraticFields.gsM :=
    IsGalois.tower_top_of_isGalois (F := ℚ) (E := Work.QuadraticFields.gsM)
      Work.QuadraticFields.gsF
  -- `[gsM : gsF] = 64`, so `gsM/gsF` is finite dimensional over `gsF`.
  have hfd : FiniteDimensional ↥Work.QuadraticFields.gsF Work.QuadraticFields.gsM :=
    Module.finite_of_finrank_eq_succ (by rw [Work.QuadraticFields.gs_finrank])
  haveI hfdI : FiniteDimensional ↥Work.QuadraticFields.gsF Work.QuadraticFields.gsM := hfd
  -- The Galois group of `gsM/gsF` has order `2 ^ 6`, hence is a `2`-group.
  have hcard : Nat.card (Work.QuadraticFields.gsM ≃ₐ[↥Work.QuadraticFields.gsF]
      Work.QuadraticFields.gsM) = 2 ^ 6 := by
    rw [IsGalois.card_aut_eq_finrank, Work.QuadraticFields.gs_finrank]
    norm_num
  have hpg : IsPGroup 2 (Work.QuadraticFields.gsM ≃ₐ[↥Work.QuadraticFields.gsF]
      Work.QuadraticFields.gsM) := IsPGroup.of_card hcard
  -- `gsM/gsF` is unramified at the finite primes ...
  have hunr : differentIdeal (𝓞 ↥Work.QuadraticFields.gsF) (𝓞 Work.QuadraticFields.gsM) = ⊤ :=
    Work.ClassFieldTower.differentIdeal_eq_top_of_isUnramifiedAtFinitePrimes
      Work.QuadraticFields.gs_unramified
  -- ... and at the infinite places.
  have hinf : IsUnramifiedAtInfinitePlaces ↥Work.QuadraticFields.gsF Work.QuadraticFields.gsM :=
    Work.QuadraticFields.gs_certificate.2.1
  -- Hence `Gal(gsM/gsF)` is a *continuous* quotient of the wide unramified pro-`2` group.
  obtain ⟨φ, hsurj, hcont⟩ :=
    exists_continuous_surjection_of_finite_unramified E Work.QuadraticFields.gsM hunr hinf hpg
  -- `Gal(gsM/gsF) ≃ (ℤ/2)^6`, i.e. `≃ (Fin 6 → Multiplicative (ZMod 2))`.
  obtain ⟨e6⟩ := Work.WingbergRoute.gsM_aut_gsF_equiv_pi
  -- The source of this transport is a finite group, hence discrete.
  refine ⟨e6.toMonoidHom.comp φ, ?_, ?_⟩
  · intro y
    obtain ⟨z, hz⟩ := e6.surjective y
    obtain ⟨w, hw⟩ := hsurj z
    exact ⟨w, by simp [hz, hw]⟩
  · exact (continuous_of_discreteTopology (f := ⇑e6.toMonoidHom)).comp hcont

end Work.WingbergEndgame
