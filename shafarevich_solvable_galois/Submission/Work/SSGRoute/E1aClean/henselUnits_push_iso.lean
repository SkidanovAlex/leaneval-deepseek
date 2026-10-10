import Mathlib.RingTheory.Henselian
import Mathlib.Tactic.Have
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.E1aClean.unitsPushTarget
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.E1aClean

open CategoryTheory SSGRoute.PTExt

noncomputable section

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 800000

attribute [local instance 10000] Rep.hV2 Rep.hV1 Submodule.module

/-- **Concrete exactness criterion for short complexes of representations.**

A short complex of (linear) representations over a ring `R` is exact at the middle term if and
only if it is exact on underlying elements: every element killed by `S.g` is in the image of
`S.f`.  This is the `ModuleCat` criterion `ShortComplex.moduleCat_exact_iff` transported along the
forgetful functor `Rep R G ⥤ ModuleCat R` (which is faithful and preserves homology). -/
theorem rep_shortComplex_exact_iff {R : Type} [Ring R] {G : Type} [Group G]
    (S : ShortComplex (Rep.{0} R G)) :
    S.Exact ↔ ∀ (x₂ : S.X₂.V), S.g.hom x₂ = 0 →
      ∃ x₁ : S.X₁.V, S.f.hom x₁ = x₂ := by
  rw [← ShortComplex.exact_map_iff_of_faithful (S := S)
    (forget₂ (Rep.{0} R G) (ModuleCat.{0} R))]
  exact ShortComplex.moduleCat_exact_iff _

/-- **The coefficient push `(K^h)ˣ → K_qˣ` of the local dictionary, over `D_q`.**

The conclusion is packaged as the `Prop`-valued definition `HenUnitsPushTarget` of
`E1aClean/unitsPushTarget.lean` (the `⧸`-quotient of units, the `Ext`-`postcomp` proof argument and
the `Rep` coercions are resolved there).

For a finite place `A` of `Ω` over the prime `q` of `K`, with the isomorphism
`e : D_q ≃* Gal(K^h/k^h)` which restricts to `τ` on `K` (`he`, from
`Work.SSGRoute.E1aClean.decompField_hensel_groupIso`), the embedding `φ : K^h →+* K_q` which is the
identity on `K` (`hφ`), fixes the image of the decomposition field under the local action (`hfix`,
from `Work.SSGRoute.E1aClean.decompFieldHenselEmb_fixes_decomp`) and is injective (`hφinj`), and
given that multiplication by `p` is a bijection on the quotient `K_qˣ / φ((K^h)ˣ)` (`hQ`, the
conclusion of `Work.SSGRoute.E1aClean.unitsQuotient_pow_bijective_fixed`, which supplies it once
`φ`, `hφinj` and the relative-algebraic-closedness of the image from
`E1aClean.decompField_embeds_completion` are given), the coefficient map
`Units.map φ : (K^h)ˣ → K_qˣ` is a morphism of `D_q`-representations from
`Rep.res e.toMonoidHom (unitsK ↥k^h ↥K^h)` to `localUnitsK (ofFinite q)` and postcomposing with it
is a bijection on `Ext¹_{D_q}(X, ·)` for every finite `p`-torsion coefficient `X`.

Route.  `θ` is `Rep.ofHom` of the additive map underlying `Units.map φ`; its intertwining is exactly
`Work.SSGRoute.E1aClean.henselEmb_equivariant` (same binders, conclusion `φ ((e τ) x) =
localAutHom τ (φ x)`).  Build the short complex `S : 0 → X₁ →θ→ X₂ → Q → 0` in `Rep Coeff ↥D_q`
with `X₁ = Rep.res e.toMonoidHom (unitsK ↥k^h ↥K^h)`, `X₂ = localUnitsK (ofFinite q)` and `Q` the
cokernel; it is short exact because `φ` is injective (`Rep.mono_iff_injective`) and `S.g` is the
cokernel projection (`Rep.epi_iff_surjective`).  Then apply the engine
`Work.SSGRoute.ExtChain.postcomp_mk₀_bijective_of_ptorsion_uniqueDivisible p X hN S hS 0 hQ'`
(`ExtChain/ext_push_engine.lean`), noting `(Ext.mk₀ θ).postcomp X (add_zero 1) =
(Ext.mk₀ S.f).postcomp X (add_zero (0+1))`.  The only non-template work (per both reviewers) is the
transport between the `Rep`-cokernel quotient and the explicit quotient
`Additive (Units K_q) ⧸ (MonoidHom.range (Units.map φ.toMonoidHom)).toAddSubgroup` on which `hQ` is
stated; `localUnitsRep` is `Rep.ofDistribMulAction _ (Additive ((localField)ˣ))`, so it is a
`Submodule`-vs-`AdditiveSubgroup`-quotient identification. -/
theorem henselUnits_push_iso
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [NumberField K]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hAq : ∀ x : NumberField.RingOfIntegers K, x ∈ q.asIdeal ↔ A.valuation (((x : K) : Ω)) < 1)
    (e : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)) ≃*
        (Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A ≃ₐ[Work.SSGRoute.E1aClean.decompField k Ω A]
          Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A))
    (he : ∀ (τ : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q))) (x : K),
        ((e τ) ⟨(x : Ω), Work.SSGRoute.E1aClean.le_henselField k Ω K A x.2⟩ : Ω)
          = ((τ : K ≃ₐ[k] K) x : Ω))
    (φ : ↥(Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A) →+*
        (NK.GlobalCFT.Place.localField K (NK.GlobalCFT.Place.ofFinite q)))
    (hφ : ∀ x : ↥K, φ ⟨(x : Ω), Work.SSGRoute.E1aClean.le_henselField k Ω K A x.2⟩ =
        algebraMap ↥K (NK.GlobalCFT.Place.localField K (NK.GlobalCFT.Place.ofFinite q)) x)
    (hfix : ∀ (τ : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)))
        (x : ↥(Work.SSGRoute.E1aClean.decompField k Ω A)),
        NK.HassePrinciple.localAutHom (K := k) (L := ↥K) (NK.GlobalCFT.Place.ofFinite q) τ
            (φ ⟨(x : Ω), Work.SSGRoute.E1aClean.decompField_le_henselField k Ω K A x.2⟩)
          = φ ⟨(x : Ω), Work.SSGRoute.E1aClean.decompField_le_henselField k Ω K A x.2⟩)
    (hφinj : Function.Injective φ)
    (p : ℕ) [Fact p.Prime]
    (hQ : Function.Bijective (fun z : Additive (Units (NK.GlobalCFT.Place.localField K
        (NK.GlobalCFT.Place.ofFinite q))) ⧸
        (MonoidHom.range (Units.map φ.toMonoidHom)).toAddSubgroup => p • z)) :
    Work.SSGRoute.E1aClean.HenUnitsPushTarget k Ω K A hA q hAq e he φ hφ hfix hφinj p hQ := by
  classical
  -- ## Notation
  let D := ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q))
  let Kq := NK.GlobalCFT.Place.localField K (NK.GlobalCFT.Place.ofFinite q)
  let Kh := ↥(Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A)
  let φu : Khˣ →* Kqˣ := Units.map φ.toMonoidHom
  let H : AddSubgroup (Additive Kqˣ) := (MonoidHom.range (Units.map φ.toMonoidHom)).toAddSubgroup
  haveI hHnorm : H.Normal := inferInstance
  -- ## The `D`-action on the local units
  letI hMD : MulDistribMulAction D (Kqˣ) :=
    NK.HassePrinciple.instMulDistribMulActionLocalUnits (K := k) (L := ↥K)
      (NK.GlobalCFT.Place.ofFinite q)
  letI hD : DistribMulAction D (Additive Kqˣ) := NK.HassePrinciple.instDistribMulActionAdditiveOfMul
  -- ## The action of `K^h ≃ₐ k^h` on the units of the henselisation
  letI hMK : DistribMulAction (Kh ≃ₐ[↥(Work.SSGRoute.E1aClean.decompField k Ω A)] Kh) (Additive Khˣ) :=
    Work.SSGRoute.instDistribMulActionAddUnitsΩ ↥(Work.SSGRoute.E1aClean.decompField k Ω A) Kh
  -- ## The action of `D` on the units of the completion is the local action
  have hcoe : ∀ (σ : D) (w : Kqˣ), ((σ • w : Kqˣ) : Kq) =
      NK.HassePrinciple.localAutHom (K := k) (L := ↥K) (NK.GlobalCFT.Place.ofFinite q) σ (w : Kq) := by
    intro σ w
    show ((NK.HassePrinciple.localUnitsEquiv (K := k) (L := ↥K)
      (NK.GlobalCFT.Place.ofFinite q) σ w : Kqˣ) : Kq) = _
    rw [NK.HassePrinciple.coe_localUnitsEquiv]
  -- ## Equivariance of `φ` on units
  have heq : ∀ (τ : D) (u : Khˣ),
      (τ • Additive.ofMul (φu u) : Additive Kqˣ) = Additive.ofMul (φu ((e τ) • u)) := by
    intro τ u
    have h1 : (τ • Additive.ofMul (φu u) : Additive Kqˣ) = Additive.ofMul (τ • (φu u)) := rfl
    rw [h1]
    apply Additive.ofMul.injective
    apply Units.ext
    show ((τ • (φu u) : Kqˣ) : Kq) = ((φu ((e τ) • u) : Kqˣ) : Kq)
    rw [hcoe, Units.coe_map, Units.coe_map]
    show NK.HassePrinciple.localAutHom (K := k) (L := ↥K) (NK.GlobalCFT.Place.ofFinite q) τ
        (φ (u : Kh)) = φ (((e τ) • u : Khˣ) : Kh)
    rw [show (((e τ) • u : Khˣ) : Kh) = (e τ) (u : Kh) from rfl]
    exact (Work.SSGRoute.E1aClean.henselEmb_equivariant k Ω K A hA q hAq e he φ hφ hfix τ u).symm
  -- ## The source action, evaluated
  have hsource : ∀ (σ : ↥(Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A) ≃ₐ[↥(Work.SSGRoute.E1aClean.decompField k Ω A)]
        ↥(Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A)) (w : Additive Khˣ),
      ((SSGRoute.PTExt.unitsK ↥(Work.SSGRoute.E1aClean.decompField k Ω A)
        ↥(Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A)).ρ σ) w = σ • w :=
    fun σ w => rfl
  have htoMul : ∀ (σ : ↥(Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A) ≃ₐ[↥(Work.SSGRoute.E1aClean.decompField k Ω A)]
        ↥(Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A)) (w : Additive Khˣ),
      Additive.toMul (σ • w) = σ • Additive.toMul w :=
    fun σ w => rfl
  -- ## Membership in the image subgroup
  have hHmem : ∀ x : Additive Kqˣ, x ∈ H ↔ ∃ u : Khˣ, Additive.ofMul (φu u) = x := by
    intro x
    rw [Additive.mem_toAddSubgroup, MonoidHom.mem_range]
    constructor
    · rintro ⟨u, hu⟩; exact ⟨u, hu⟩
    · rintro ⟨u, hu⟩; exact ⟨u, hu⟩
  have hHstab : ∀ (τ : D) (x : Additive Kqˣ), x ∈ H → τ • x ∈ H := by
    intro τ x hx
    obtain ⟨u, rfl⟩ := (hHmem x).mp hx
    exact (hHmem (τ • Additive.ofMul (φu u))).mpr ⟨(e τ) • u, (heq τ u).symm⟩
  -- ## The quotient `K_qˣ / φ((K^h)ˣ)`
  let V := Additive Kqˣ ⧸ H
  let smulMap : D → (Additive Kqˣ →+ Additive Kqˣ) := fun τ =>
    { toFun := fun x => τ • x
      map_zero' := smul_zero τ
      map_add' := fun a b => smul_add τ a b }
  let hsmul : D → V → V := fun τ =>
    QuotientAddGroup.map H H (smulMap τ) (fun x hx => hHstab τ x hx)
  letI : SMul D V := ⟨hsmul⟩
  have smul_mk : ∀ (τ : D) (x : Additive Kqˣ),
      τ • (QuotientAddGroup.mk x : V) = QuotientAddGroup.mk (τ • x) := by
    intro τ x
    show QuotientAddGroup.map H H (smulMap τ) (fun x hx => hHstab τ x hx)
        (QuotientAddGroup.mk x) = QuotientAddGroup.mk (τ • x)
    exact QuotientAddGroup.map_mk H H (smulMap τ) (fun x hx => hHstab τ x hx) x
  letI : DistribMulAction D V := Function.Surjective.distribMulAction (QuotientAddGroup.mk' H)
    (QuotientAddGroup.mk'_surjective H) (fun τ x => (smul_mk τ x).symm)
  have coeff_smul_mk : ∀ (c : Coeff) (x : Additive Kqˣ),
      c • (QuotientAddGroup.mk x : V) = QuotientAddGroup.mk (c • x) := by
    intro c x
    obtain ⟨n⟩ := c
    exact map_zsmul (QuotientAddGroup.mk' H) n x
  letI : SMulCommClass D Coeff V := ⟨fun τ c v => by
    refine QuotientAddGroup.induction_on v ?_
    intro x
    show τ • (c • (QuotientAddGroup.mk x : V)) = c • (τ • (QuotientAddGroup.mk x : V))
    rw [coeff_smul_mk c x, smul_mk τ (c • x), smul_mk τ x, coeff_smul_mk c (τ • x)]
    congr 1
    obtain ⟨n⟩ := c
    show τ • (n • x) = n • (τ • x)
    exact map_zsmul (smulMap τ) n x⟩
  -- ## The quotient representation
  let Q' : Rep.{0} Coeff D := Rep.ofDistribMulAction Coeff D V
  -- ## The projection `K_qˣ ↠ K_qˣ/φ((K^h)ˣ)`
  let proj : SSGRoute.PTExt.localUnitsK (k := k) (NK.GlobalCFT.Place.ofFinite q) ⟶ Q' :=
    Rep.ofHom
      { toFun := fun x => QuotientAddGroup.mk' H x
        map_add' := fun x y => map_add (QuotientAddGroup.mk' H) x y
        map_smul' := fun c x => by
          show QuotientAddGroup.mk' H (c • x) = c • QuotientAddGroup.mk' H x
          exact (coeff_smul_mk c x).symm
        isIntertwining' := fun τ => by
          apply LinearMap.ext
          intro x
          show QuotientAddGroup.mk' H (τ • x) = τ • QuotientAddGroup.mk' H x
          exact (smul_mk τ x).symm }
  -- ## The coefficient morphism `(K^h)ˣ → K_qˣ`
  let θmap : Additive Khˣ →+ Additive Kqˣ :=
    { toFun := fun v => Additive.ofMul (φu (Additive.toMul v))
      map_zero' := by
        show Additive.ofMul (φu (Additive.toMul (0 : Additive Khˣ))) = 0
        rw [show Additive.toMul (0 : Additive Khˣ) = 1 from rfl, map_one]
        rfl
      map_add' := fun x y => by
        show Additive.ofMul (φu (Additive.toMul (x + y))) =
          Additive.ofMul (φu (Additive.toMul x)) + Additive.ofMul (φu (Additive.toMul y))
        rw [show Additive.toMul (x + y) = Additive.toMul x * Additive.toMul y from rfl, map_mul]
        rfl }
  have hint : ∀ (τ : D) (v : Additive Khˣ),
      θmap (((SSGRoute.PTExt.unitsK ↥(Work.SSGRoute.E1aClean.decompField k Ω A)
        ↥(Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A)).ρ (e τ)) v)
        = τ • (Additive.ofMul (φu (Additive.toMul v)) : Additive Kqˣ) := by
    intro τ v
    rw [hsource (e τ) v]
    change Additive.ofMul (φu (Additive.toMul ((e τ) • v))) =
      τ • Additive.ofMul (φu (Additive.toMul v))
    rw [htoMul (e τ) v]
    exact (heq τ (Additive.toMul v)).symm
  let θ : Rep.res e.toMonoidHom
        (SSGRoute.PTExt.unitsK ↥(Work.SSGRoute.E1aClean.decompField k Ω A)
          ↥(Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A)) ⟶
      SSGRoute.PTExt.localUnitsK (k := k) (NK.GlobalCFT.Place.ofFinite q) :=
    Rep.ofHom
      { toFun := fun v => θmap v
        map_add' := fun x y => map_add θmap x y
        map_smul' := fun c x => by
          obtain ⟨n⟩ := c
          show θmap (n • x) = n • θmap x
          exact map_zsmul θmap n x
        isIntertwining' := fun τ => by
          apply LinearMap.ext
          intro v
          show θmap (((SSGRoute.PTExt.unitsK ↥(Work.SSGRoute.E1aClean.decompField k Ω A)
            ↥(Work.SSGRoute.E1aClean.henselOverDecomp k Ω K A)).ρ (e τ)) v) = τ • θmap v
          exact hint τ v }
  -- ## The short complex `0 → (K^h)ˣ → K_qˣ → K_qˣ/φ((K^h)ˣ) → 0`
  have hφuinj : Function.Injective φu := by
    intro u v huv
    apply Units.ext
    apply hφinj
    show ((φu u : Kqˣ) : Kq) = ((φu v : Kqˣ) : Kq)
    exact congrArg (fun w : Kqˣ => (w : Kq)) huv
  have hθinj : Function.Injective (fun v : Additive Khˣ => θmap v) := by
    intro x y hxy
    have h1 : φu (Additive.toMul x) = φu (Additive.toMul y) := Additive.ofMul.injective hxy
    exact Additive.toMul.injective (hφuinj h1)
  have hzero : θ ≫ proj = 0 := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    show QuotientAddGroup.mk (θmap x) = 0
    rw [show θmap x = Additive.ofMul (φu (Additive.toMul x)) from rfl]
    rw [QuotientAddGroup.eq_zero_iff]
    exact (hHmem _).mpr ⟨Additive.toMul x, rfl⟩
  let S : ShortComplex (Rep.{0} Coeff D) := ShortComplex.mk θ proj hzero
  have hExact : S.Exact := by
    rw [rep_shortComplex_exact_iff]
    intro x₂ hx₂
    have hx₂' : (QuotientAddGroup.mk (x₂ : Additive Kqˣ) : V) = 0 := hx₂
    have hmem : (x₂ : Additive Kqˣ) ∈ H :=
      (@QuotientAddGroup.eq_zero_iff (Additive Kqˣ) _ H hHnorm (x₂ : Additive Kqˣ)).mp hx₂'
    obtain ⟨u, hu⟩ := (hHmem (x₂ : Additive Kqˣ)).mp hmem
    exact ⟨Additive.ofMul u, hu⟩
  have hS : S.ShortExact := ShortComplex.ShortExact.mk' hExact
    ((Rep.mono_iff_injective S.f).mpr hθinj)
    ((Rep.epi_iff_surjective S.g).mpr (by
      intro y
      exact QuotientAddGroup.induction_on y (fun x => ⟨x, rfl⟩)))
  -- ## The `Ext`-theoretic engine
  have hbij : ∀ (X : Rep.{0} Coeff D) (_ : Finite X.V), (∀ x : X.V, p • x = 0) →
      Function.Bijective ((CategoryTheory.Abelian.Ext.mk₀ θ).postcomp X (add_zero 1)) := by
    intro X _ hN
    have hmain := Work.SSGRoute.ExtChain.postcomp_mk₀_bijective_of_ptorsion_uniqueDivisible
      (G := D) p X hN hS 0 hQ
    exact hmain
  exact ⟨θ, fun u => rfl, hbij⟩

end

end Work.SSGRoute.E1aClean
