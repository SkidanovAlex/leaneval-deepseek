import Mathlib
import Submission.Work.WingbergRoute.Defs
import Submission.Work.WingbergRoute.gsM_aut_gsF_equiv_pi
import Submission.Work.QuadraticFields.CertificateRealSummary
import Submission.Work.ClassFieldTower.All

/-!
# The `(ℤ/2)^6`-quotient of `G_∅(gsF)`, continuously

`Work.WingbergRoute.gsM_quotient_of_maximal` exhibits `(ℤ/2)^6` as a *quotient* of the maximal
unramified pro-`2` Galois group `G_∅ = Gal(gsF_∅/gsF)` of the totally real quadratic field
`gsF = ℚ(√2576450045)`, by restricting `G_∅` to the unramified multiquadratic certificate
extension `gsM/gsF` of degree `2^6`.  For the pro-`p`-group formalism of this workspace
(`Work.ConCohomology`, `Work.RelatorRank`, ...) one needs the quotient map to be *continuous*
for the Krull topology on `G_∅` — a continuous surjection onto `(ℤ/2)^6` is what exhibits
`(ℤ/2)^6` as a *pro-`2` quotient*, i.e. six independent unramified quadratic characters, which
is the `d(G_∅) ≥ 6` input of the unramified (Wingberg) route.

The continuity is not formal: `(ℤ/2)^6` is a *finite* discrete group and `G_∅` is a compact
profinite group, but an arbitrary homomorphism from a compact group to a finite discrete group
need not be continuous.  What makes the map at hand continuous is that it is *by construction*
a restriction of automorphisms to a **finite** subextension: the universal property of `gsF_∅`
embeds `gsM` as a finite subextension `E ⊆ gsF_∅`, and restriction
`Gal(gsF_∅/gsF) →* Gal(E/gsF)` is continuous for the Krull topologies (Mathlib,
`InfiniteGalois.restrictNormalHom_continuous`), while the transport along `gsM ≃ₐ[gsF] E` is a
map between finite (hence discrete) groups.

## Main results

* `Work.WingbergRoute.exists_surjective_galoisGroup_of_finite_unramified_continuous` — the
  continuous version of
  `Work.ClassFieldTower.exists_surjective_galoisGroup_of_finite_unramified`;
* `Work.WingbergRoute.gsM_quotient_of_maximal_continuous`.
-/

set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open scoped NumberField
open NumberField

namespace Work.WingbergRoute

open Work.QuadraticFields

noncomputable section

/-- **Every finite unramified pro-`2` Galois extension of `F` is a *continuous* quotient of
`G_∅`.**

This is `Work.ClassFieldTower.exists_surjective_galoisGroup_of_finite_unramified` with the
continuity of the quotient map recorded.  Let `F` be a number field and
`M : MaximalUnramifiedProP F 2` the maximal unramified pro-`2` extension of `F`.  If `L/F` is a
finite Galois extension, unramified over `F` (`differentIdeal (𝓞 F) (𝓞 L) = ⊤`) with `2`-group
Galois group, then the universal property of `M` gives an `F`-embedding `ϕ : L →ₐ[F] M.K`; its
image `E = ϕ.fieldRange` is a *finite* subextension of `M.K/F`, and the restriction map

`Gal(M.K/F) →* Gal(E/F) ≃* Gal(L/F)`

is surjective, and continuous for the Krull topology on the source, because restriction to a
finite subextension is continuous and the transport along `ϕ` happens between finite discrete
groups. -/
theorem exists_surjective_galoisGroup_of_finite_unramified_continuous
    {F : Type} [Field F] [NumberField F]
    (M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} F 2) (L : Type) [Field L] [NumberField L]
    [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    (hunr : differentIdeal (𝓞 F) (𝓞 L) = ⊤)
    (hpg : IsPGroup 2 (L ≃ₐ[F] L)) :
    ∃ φ : Work.ClassFieldTower.galoisGroup M →* (L ≃ₐ[F] L),
      Function.Surjective φ ∧ Continuous φ := by
  obtain ⟨ϕ, _⟩ := M.universal L hpg hunr
  let E : IntermediateField F M.K := ϕ.fieldRange
  let e : L ≃ₐ[F] ↥E := AlgHom.equivFieldRange ϕ
  have hgalE : IsGalois F ↥E := IsGalois.of_algEquiv e
  have hNorE : Normal F ↥E := hgalE.to_normal
  have hNorK : Normal F M.K := (inferInstance : IsGalois F M.K).to_normal
  have hfdE : FiniteDimensional F ↥E := e.toLinearEquiv.finiteDimensional
  have hdiscE : DiscreteTopology (↥E ≃ₐ[F] ↥E) :=
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
      continuous_of_discreteTopology
    simpa only [MonoidHom.coe_comp, Function.comp_def] using h2.comp h1

/-- **`(ℤ/2)^6` is a continuous quotient of the maximal unramified pro-`2` Galois group of
`gsF`.**

The unramified multiquadratic certificate `gsM/gsF` has degree `64 = 2^6` and Galois group of
exponent `2`, so it is `(ℤ/2)^6`
(`Work.WingbergRoute.gsM_aut_gsF_equiv_pi`), and it is unramified over `gsF`
(`Work.QuadraticFields.gs_unramified`), so the universal property of the maximal unramified
pro-`2` extension `gsF_∅` exhibits it as a quotient of `G_∅ = Gal(gsF_∅/gsF)`
(`Work.ClassFieldTower.exists_surjective_galoisGroup_of_finite_unramified`).  The quotient map
is continuous for the Krull topology by
`Work.WingbergRoute.exists_surjective_galoisGroup_of_finite_unramified_continuous`, and the
transport to the elementary abelian group `Fin 6 → Multiplicative (ZMod 2)` happens between
finite (hence discrete) groups. -/
theorem gsM_quotient_of_maximal_continuous
    (M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} ↥Work.QuadraticFields.gsF 2) :
    ∃ φ : Work.ClassFieldTower.galoisGroup M →* (Fin 6 → Multiplicative (ZMod 2)),
      Function.Surjective φ ∧ Continuous φ := by
  classical
  -- `gsM` is Galois over `ℚ` (it is multiquadratic), hence over the intermediate field `gsF`.
  haveI hgalQ : IsGalois ℚ gsM := multiQuad_isGalois gsPrimesQ
  haveI hgal : IsGalois ↥Work.QuadraticFields.gsF gsM :=
    IsGalois.tower_top_of_isGalois (F := ℚ) (E := gsM) Work.QuadraticFields.gsF
  -- `[gsM : gsF] = 64`, so `gsM/gsF` is finite dimensional.
  have hfd : FiniteDimensional ↥Work.QuadraticFields.gsF gsM :=
    Module.finite_of_finrank_eq_succ (by rw [gs_finrank])
  haveI hfdI : FiniteDimensional ↥Work.QuadraticFields.gsF gsM := hfd
  -- The Galois group of `gsM/gsF` has order `2 ^ 6`, hence is a `2`-group.
  have hcard : Nat.card (gsM ≃ₐ[↥Work.QuadraticFields.gsF] gsM) = 2 ^ 6 := by
    rw [IsGalois.card_aut_eq_finrank, gs_finrank]
    norm_num
  have hpg : IsPGroup 2 (gsM ≃ₐ[↥Work.QuadraticFields.gsF] gsM) := IsPGroup.of_card hcard
  -- `gsM/gsF` is unramified at the finite places.
  have hunr : differentIdeal (𝓞 ↥Work.QuadraticFields.gsF) (𝓞 gsM) = ⊤ :=
    Work.ClassFieldTower.differentIdeal_eq_top_of_isUnramifiedAtFinitePrimes gs_unramified
  -- Hence `Gal(gsM/gsF)` is a *continuous* quotient of the maximal unramified pro-`2` group.
  obtain ⟨φ, hsurj, hcont⟩ :=
    exists_surjective_galoisGroup_of_finite_unramified_continuous M gsM hunr hpg
  -- `Gal(gsM/gsF) ≃ (ℤ/2)^6`, i.e. `≃ (Fin 6 → Multiplicative (ZMod 2))`.
  obtain ⟨e⟩ := gsM_aut_gsF_equiv_pi
  -- The source of this transport is a finite group, hence discrete.
  have hdisc : DiscreteTopology (gsM ≃ₐ[↥Work.QuadraticFields.gsF] gsM) :=
    krullTopology_discreteTopology_of_finiteDimensional ↥Work.QuadraticFields.gsF gsM
  refine ⟨e.toMonoidHom.comp φ, ?_, ?_⟩
  · intro y
    obtain ⟨z, hz⟩ := e.surjective y
    obtain ⟨w, hw⟩ := hsurj z
    exact ⟨w, by simp [hz, hw]⟩
  · exact (continuous_of_discreteTopology (f := ⇑e.toMonoidHom)).comp hcont

end

end Work.WingbergRoute
