import Mathlib
import Submission.Work.SSGRoute.PTCore.H2_level_defs
import Submission.Work.SSGRoute.coindU_aux
import Submission.Work.SSGRoute.PT.KrullCorrespondence
import Submission.Work.SSGRoute.PT.H1Transfer
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The pieces of the level structure of `H²(G_F, k̄ˣ)`

This file proves the three properties of the level inflation `psiTilde L` of `H2_level_defs.lean`:

* `H2_level_hilbert90` — Hilbert 90 at the fixing subgroup (characteristic-free);
* `H2_level_injective` — `psiTilde L` is injective;
* `H2_level_mono` — the ranges of the `psiTilde L` are nested;
* `H2_level_cover` — every class lives on a finite level.
-/

noncomputable section

open scoped Classical
open Work.AbsoluteKummer

namespace Work.SSGRoute.PTCore

variable {F : Type} [Field F] [IsGalois F (AlgebraicClosure F)]

/-! ## Hilbert 90 over an algebraic closure (characteristic-free) -/

/-- **Hilbert 90 over an algebraic closure.**  For an algebraic closure `Ω` of an arbitrary field
`k`, every continuous crossed homomorphism `Ω ≃ₐ[k] Ω → Ωˣ` is a coboundary, i.e.
`H¹(Gal(Ω/k), Ωˣ) = 0`. -/
theorem subsingleton_H1_addUnits_of_isAlgClosure
    {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] :
    Subsingleton (Work.AbsoluteKummer.H1 (Ω ≃ₐ[k] Ω) (Additive Ωˣ)) := by
  refine subsingleton_of_forall_eq 0 ?_
  intro x
  obtain ⟨F₀, hF₀⟩ := QuotientAddGroup.mk'_surjective
    ((Work.AbsoluteKummer.B1 (Ω ≃ₐ[k] Ω) (Additive Ωˣ)).comap
      (Work.AbsoluteKummer.Z1 (Ω ≃ₐ[k] Ω) (Additive Ωˣ)).subtype) x
  rw [show x = Work.AbsoluteKummer.H1π (Ω ≃ₐ[k] Ω) (Additive Ωˣ) F₀ from hF₀.symm,
    Work.AbsoluteKummer.H1π_eq_zero_iff, Work.AbsoluteKummer.mem_B1_iff]
  obtain ⟨hcross, hloc⟩ := (Work.AbsoluteKummer.mem_Z1_iff _).mp F₀.2
  have humap : ∀ (σ : Ω ≃ₐ[k] Ω) (u : Ωˣ),
      Work.SSGRoute.umap k Ω σ u = Work.SSGRoute.algEquivUnitsMapΩ k Ω σ u :=
    fun σ u => Units.ext (by rw [Work.SSGRoute.umap_coe, Work.SSGRoute.algEquivUnitsMapΩ_coe])
  have hcross' : ∀ σ τ : Ω ≃ₐ[k] Ω,
      Additive.toMul ((F₀ : (Ω ≃ₐ[k] Ω) → Additive Ωˣ) (σ * τ))
        = Additive.toMul ((F₀ : (Ω ≃ₐ[k] Ω) → Additive Ωˣ) σ)
          * Work.SSGRoute.umap k Ω σ (Additive.toMul ((F₀ : (Ω ≃ₐ[k] Ω) → Additive Ωˣ) τ)) := by
    intro σ τ
    have h := congrArg Additive.toMul (hcross σ τ)
    simp only [toMul_add, Work.SSGRoute.addUnits_smul_toMulΩ] at h
    rw [h, ← humap σ (Additive.toMul ((F₀ : (Ω ≃ₐ[k] Ω) → Additive Ωˣ) τ)), mul_comm]
  have hloc' : Work.AbsoluteKummer.IsLocallyConstant
      (fun σ : Ω ≃ₐ[k] Ω => Additive.toMul ((F₀ : (Ω ≃ₐ[k] Ω) → Additive Ωˣ) σ)) :=
    Work.AbsoluteKummer.IsLocallyConstant.map Additive.toMul hloc
  obtain ⟨b, hb⟩ := Work.SSGRoute.hilbert90_isAlgClosure (k := k) (Ω := Ω)
    (fun σ : Ω ≃ₐ[k] Ω => Additive.toMul ((F₀ : (Ω ≃ₐ[k] Ω) → Additive Ωˣ) σ)) hcross' hloc'
  refine ⟨Additive.ofMul b, ?_⟩
  funext σ
  rw [Work.GroupCohomology.d0_apply]
  have hb' : (F₀ : (Ω ≃ₐ[k] Ω) → Additive Ωˣ) σ
      = Additive.ofMul (Work.SSGRoute.umap k Ω σ b / b) := by
    rw [← ofMul_toMul ((F₀ : (Ω ≃ₐ[k] Ω) → Additive Ωˣ) σ), hb σ]
  have hsmul : σ • Additive.ofMul b = Additive.ofMul (Work.SSGRoute.umap k Ω σ b) := by
    show Additive.ofMul (Work.SSGRoute.algEquivUnitsMapΩ k Ω σ b)
        = Additive.ofMul (Work.SSGRoute.umap k Ω σ b)
    rw [humap σ b]
  rw [hb', hsmul, ofMul_div]

/-! ## The fixing-subgroup homeomorphism (characteristic-free) -/

/-- **The isomorphism `Gal(k̄/L) ≃* Gal(k̄/↥L)` is continuous** (characteristic-free version of
`Work.SSGRoute.PT.continuous_fixingSubgroupEquiv`). -/
theorem continuous_fixingSubgroupEquiv_free
    (L : FiniteGaloisIntermediateField F (AlgebraicClosure F)) :
    Continuous ((IntermediateField.fixingSubgroupEquiv
        (L : IntermediateField F (AlgebraicClosure F))).toMonoidHom :
      ↥(lvlFix L) → (AlgebraicClosure F ≃ₐ[↥(L : IntermediateField F (AlgebraicClosure F))]
        AlgebraicClosure F)) := by
  classical
  let f : ↥(lvlFix L) →* (AlgebraicClosure F ≃ₐ[↥(L : IntermediateField F (AlgebraicClosure F))]
      AlgebraicClosure F) :=
    (IntermediateField.fixingSubgroupEquiv
      (L : IntermediateField F (AlgebraicClosure F))).toMonoidHom
  refine continuous_of_continuousAt_one f ?_
  rw [ContinuousAt, f.map_one, Filter.tendsto_def]
  intro U hU
  rw [krullTopology_mem_nhds_one_iff ↥(L : IntermediateField F (AlgebraicClosure F))
    (AlgebraicClosure F)] at hU
  obtain ⟨N, hNfin, hNU⟩ := hU
  haveI : FiniteDimensional ↥(L : IntermediateField F (AlgebraicClosure F)) N := hNfin
  haveI hMfin : FiniteDimensional F ↥(N.restrictScalars F) :=
    FiniteDimensional.trans F ↥(L : IntermediateField F (AlgebraicClosure F)) ↥N
  have hopen : IsOpen ((N.restrictScalars F).fixingSubgroup : Set (AbsGal F)) :=
    IntermediateField.fixingSubgroup_isOpen (N.restrictScalars F)
  have hmem : (Subtype.val ⁻¹' ((N.restrictScalars F).fixingSubgroup : Set (AbsGal F))) ∈
      nhds (1 : ↥(lvlFix L)) :=
    (hopen.preimage continuous_subtype_val).mem_nhds (by simp)
  refine Filter.mem_of_superset hmem ?_
  intro x hx
  show (IntermediateField.fixingSubgroupEquiv
    (L : IntermediateField F (AlgebraicClosure F)) x) ∈ U
  apply hNU
  change (IntermediateField.fixingSubgroupEquiv
    (L : IntermediateField F (AlgebraicClosure F)) x) ∈ N.fixingSubgroup
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro y hy
  have hyM : y ∈ (N.restrictScalars F : IntermediateField F (AlgebraicClosure F)) := hy
  rw [IntermediateField.mem_restrictScalars] at hyM
  have hx' : (x : AbsGal F) ∈ (N.restrictScalars F).fixingSubgroup := hx
  rw [IntermediateField.mem_fixingSubgroup_iff] at hx'
  exact hx' y hyM

/-- **`Gal(k̄/L) ≃* Gal(k̄/↥L)` is a homeomorphism** (characteristic-free version of
`Work.SSGRoute.PT.isHomeomorph_fixingSubgroupEquiv`). -/
theorem isHomeomorph_fixingSubgroupEquiv_free
    (L : FiniteGaloisIntermediateField F (AlgebraicClosure F)) :
    IsHomeomorph ((IntermediateField.fixingSubgroupEquiv
        (L : IntermediateField F (AlgebraicClosure F))) :
      ↥(lvlFix L) → (AlgebraicClosure F ≃ₐ[↥(L : IntermediateField F (AlgebraicClosure F))]
        AlgebraicClosure F)) := by
  haveI : CompactSpace ↥(lvlFix L) := by
    have hclosed : IsClosed ((lvlFix L : Subgroup (AbsGal F)) : Set (AbsGal F)) :=
      IntermediateField.fixingSubgroup_isClosed (L : IntermediateField F (AlgebraicClosure F))
    haveI : CompactSpace (AbsGal F) := inferInstance
    exact isCompact_iff_compactSpace.mp hclosed.isCompact
  haveI : T2Space (AlgebraicClosure F ≃ₐ[↥(L : IntermediateField F (AlgebraicClosure F))]
      AlgebraicClosure F) :=
    krullTopology_t2 (K := ↥(L : IntermediateField F (AlgebraicClosure F)))
      (L := AlgebraicClosure F)
  exact (isHomeomorph_iff_continuous_bijective).mpr
    ⟨continuous_fixingSubgroupEquiv_free L,
      (IntermediateField.fixingSubgroupEquiv
        (L : IntermediateField F (AlgebraicClosure F))).bijective⟩

/-! ## Hilbert 90 at a finite Galois level -/

/-- **Hilbert 90 for the fixing subgroup of a finite Galois level.**  Every continuous crossed
homomorphism `Gal(k̄/L) → k̄ˣ` is a coboundary. -/
theorem H2_level_hilbert90 (L : FiniteGaloisIntermediateField F (AlgebraicClosure F))
    (f : ↥(lvlFix L) → UnitsK F)
    (hf : ∀ σ τ : ↥(lvlFix L), f (σ * τ) = (σ : AbsGal F) • f τ + f σ)
    (hc : Work.AbsoluteKummer.IsLocallyConstant f) :
    ∃ b : UnitsK F, ∀ σ : ↥(lvlFix L), (σ : AbsGal F) • b - b = f σ := by
  haveI hAlg : IsAlgClosure ↥(L : IntermediateField F (AlgebraicClosure F)) (AlgebraicClosure F) :=
    ⟨IsAlgClosure.isAlgClosed F, inferInstance⟩
  haveI habs : Subsingleton (Work.AbsoluteKummer.H1
      (AlgebraicClosure F ≃ₐ[↥(L : IntermediateField F (AlgebraicClosure F))] AlgebraicClosure F)
      (Additive ((AlgebraicClosure F)ˣ))) :=
    subsingleton_H1_addUnits_of_isAlgClosure
      (k := ↥(L : IntermediateField F (AlgebraicClosure F))) (Ω := AlgebraicClosure F)
  have hΦ : IsHomeomorph ((IntermediateField.fixingSubgroupEquiv
      (L : IntermediateField F (AlgebraicClosure F))) :
      ↥(lvlFix L) → (AlgebraicClosure F ≃ₐ[↥(L : IntermediateField F (AlgebraicClosure F))]
        AlgebraicClosure F)) :=
    isHomeomorph_fixingSubgroupEquiv_free L
  haveI hsub : Subsingleton (Work.AbsoluteKummer.H1 ↥(lvlFix L) (UnitsK F)) :=
    ⟨fun a b => (Work.SSGRoute.PT.h1Transfer
      (G := AlgebraicClosure F ≃ₐ[↥(L : IntermediateField F (AlgebraicClosure F))]
        AlgebraicClosure F)
      (G' := ↥(lvlFix L))
      (M := Additive ((AlgebraicClosure F)ˣ)) (M' := UnitsK F)
      (IntermediateField.fixingSubgroupEquiv (L : IntermediateField F (AlgebraicClosure F)))
      hΦ (AddEquiv.refl (UnitsK F)) (fun g' m' => rfl)).injective (Subsingleton.elim _ _)⟩
  have hZ : f ∈ Work.AbsoluteKummer.Z1 ↥(lvlFix L) (UnitsK F) := by
    rw [Work.AbsoluteKummer.mem_Z1_iff]
    exact ⟨hf, hc⟩
  have hclass : Work.AbsoluteKummer.H1π ↥(lvlFix L) (UnitsK F) ⟨f, hZ⟩ = 0 :=
    Subsingleton.elim _ _
  rw [Work.AbsoluteKummer.H1π_eq_zero_iff, Work.AbsoluteKummer.mem_B1_iff] at hclass
  obtain ⟨b, hb⟩ := hclass
  refine ⟨b, fun σ => ?_⟩
  have h := congrFun hb σ
  rw [Work.GroupCohomology.d0_apply] at h
  show (σ : AbsGal F) • b - b = f σ
  exact h


/-! ## Injectivity of the level inflation -/

set_option maxHeartbeats 800000 in
/-- **The transgression argument.**  If Hilbert 90 holds at `Gal(k̄/L)` (the hypothesis `hH90`),
then the level inflation `psiTilde L` has trivial kernel: its kernel is the image of the
transgression `H¹(Gal(k̄/L), k̄ˣ) → H²(Gal(L/F), Lˣ)`, whose domain vanishes. -/
theorem psiTilde_eq_zero_iff (L : FiniteGaloisIntermediateField F (AlgebraicClosure F))
    (hH90 : ∀ (f : ↥(lvlFix L) → UnitsK F),
      (∀ σ τ : ↥(lvlFix L), f (σ * τ) = (σ : AbsGal F) • f τ + f σ) →
      Work.AbsoluteKummer.IsLocallyConstant f →
      ∃ b : UnitsK F, ∀ σ : ↥(lvlFix L), (σ : AbsGal F) • b - b = f σ)
    (x : LevelH2 L) : psiTilde L x = 0 ↔ x = 0 := by
  classical
  refine ⟨fun hx => ?_, fun hx => by rw [hx, map_zero]⟩
  obtain ⟨c, rfl⟩ := QuotientAddGroup.mk'_surjective
    ((LevelCob L).comap (LevelCocycles L).subtype).toAddSubgroup x
  rw [psiTilde_mk, Work.AbsoluteKummer.H2π_eq_zero_iff] at hx
  obtain ⟨f, hf, hfd⟩ := (Work.AbsoluteKummer.mem_B2_iff _).mp hx
  set FF : AbsGal F → UnitsK F := (f : AbsGal F → UnitsK F) with hFF
  have hloc : Work.AbsoluteKummer.IsLocallyConstant FF :=
    (Work.AbsoluteKummer.mem_C1c_iff f).mp hf
  set lam : UnitsL L := (c : LevelGal L × LevelGal L → UnitsL L) (1, 1) with hlam
  set CC' : LevelGal L × LevelGal L → UnitsL L :=
    (c : LevelGal L × LevelGal L → UnitsL L)
      - (groupCohomology.d₁₂ (LevelRep L)).hom (fun _ : LevelGal L => lam) with hCC'
  set FF' : AbsGal F → UnitsK F := FF - fun _ => inclL L lam with hFF'
  have hkey : ∀ g h : AbsGal F, g • FF h - FF (g * h) + FF g
      = inclL L ((c : LevelGal L × LevelGal L → UnitsL L) (resL L g, resL L h)) := by
    intro g h
    have h1 := congrFun hfd (g, h)
    rw [Work.GroupCohomology.d1_apply] at h1
    exact h1
  have hconsteval : ∀ p : LevelGal L × LevelGal L,
      (groupCohomology.d₁₂ (LevelRep L)).hom (fun _ : LevelGal L => lam) p
        = (LevelRep L).ρ p.1 lam := by
    intro p
    obtain ⟨g, k⟩ := p
    rw [groupCohomology.d₁₂_hom_apply]
    abel
  have hkey' : ∀ g h : AbsGal F, g • FF' h - FF' (g * h) + FF' g
      = inclL L (CC' (resL L g, resL L h)) := by
    intro g h
    have h1 := hkey g h
    have h2 : CC' (resL L g, resL L h)
        = (c : LevelGal L × LevelGal L → UnitsL L) (resL L g, resL L h)
          - (LevelRep L).ρ (resL L g) lam := by
      rw [hCC']
      show (c : LevelGal L × LevelGal L → UnitsL L) (resL L g, resL L h)
          - (groupCohomology.d₁₂ (LevelRep L)).hom (fun _ : LevelGal L => lam)
            (resL L g, resL L h) = _
      rw [hconsteval]
    rw [h2, map_sub]
    have h3 : g • FF' h - FF' (g * h) + FF' g
        = (g • FF h - FF (g * h) + FF g) - g • inclL L lam := by
      rw [hFF']; simp only [Pi.sub_apply, smul_sub]; abel
    rw [h3, h1, inclL_rho]
  have hCC'mem : CC' ∈ LevelCocycles L := by
    rw [hCC']
    refine sub_mem c.2 ?_
    exact groupCohomology.coboundaries₂_le_cocycles₂ (LevelRep L)
      (LinearMap.mem_range.mpr ⟨fun _ : LevelGal L => lam, rfl⟩)
  have hCC'_one : CC' (1, 1) = 0 := by
    rw [hCC']
    show (c : LevelGal L × LevelGal L → UnitsL L) (1, 1)
        - (groupCohomology.d₁₂ (LevelRep L)).hom (fun _ : LevelGal L => lam) (1, 1) = 0
    rw [hconsteval]
    show lam - (LevelRep L).ρ (1 : LevelGal L) lam = 0
    rw [map_one]
    simp
  -- the restriction of `FF'` to the fixing subgroup is a crossed homomorphism
  have hcross : ∀ σ τ : ↥(lvlFix L),
      (fun υ : ↥(lvlFix L) => FF' (υ : AbsGal F)) (σ * τ)
        = (σ : AbsGal F) • (fun υ : ↥(lvlFix L) => FF' (υ : AbsGal F)) τ
          + (fun υ : ↥(lvlFix L) => FF' (υ : AbsGal F)) σ := by
    intro σ τ
    have h1 := hkey' (σ : AbsGal F) (τ : AbsGal F)
    rw [show resL L (σ : AbsGal F) = 1 from (mem_ker_resL_iff L _).mpr σ.2,
      show resL L (τ : AbsGal F) = 1 from (mem_ker_resL_iff L _).mpr τ.2,
      hCC'_one, map_zero] at h1
    show FF' ((σ : AbsGal F) * (τ : AbsGal F))
      = (σ : AbsGal F) • FF' (τ : AbsGal F) + FF' (σ : AbsGal F)
    have h2 : (σ : AbsGal F) • FF' (τ : AbsGal F) + FF' (σ : AbsGal F)
        - FF' ((σ : AbsGal F) * (τ : AbsGal F)) = 0 := by
      rw [← h1]; abel
    exact (sub_eq_zero.mp h2).symm
  have hloc' : Work.AbsoluteKummer.IsLocallyConstant
      (fun υ : ↥(lvlFix L) => FF' (υ : AbsGal F)) := by
    rw [hFF']
    exact (hloc.sub (Work.AbsoluteKummer.isLocallyConstant_const _)).comp continuous_subtype_val
  obtain ⟨b, hb⟩ := hH90 (fun υ : ↥(lvlFix L) => FF' (υ : AbsGal F)) hcross hloc'
  set FF₂ : AbsGal F → UnitsK F := FF' - Work.GroupCohomology.d0 (AbsGal F) (UnitsK F) b with hFF₂
  have hd1d0 : (Work.GroupCohomology.d1 (AbsGal F) (UnitsK F))
      ((Work.GroupCohomology.d0 (AbsGal F) (UnitsK F)) b) = 0 := by
    funext p
    obtain ⟨g, h⟩ := p
    rw [Work.GroupCohomology.d1_apply, Work.GroupCohomology.d0_apply,
      Work.GroupCohomology.d0_apply, Work.GroupCohomology.d0_apply, smul_sub, mul_smul,
      Pi.zero_apply]
    abel
  have hkey₂ : ∀ g h : AbsGal F, g • FF₂ h - FF₂ (g * h) + FF₂ g
      = inclL L (CC' (resL L g, resL L h)) := by
    intro g h
    have h1 := hkey' g h
    have h2 : FF₂ = FF' - Work.GroupCohomology.d0 (AbsGal F) (UnitsK F) b := hFF₂
    rw [h2]
    have hsub : (Work.GroupCohomology.d1 (AbsGal F) (UnitsK F))
        (FF' - Work.GroupCohomology.d0 (AbsGal F) (UnitsK F) b)
        = (Work.GroupCohomology.d1 (AbsGal F) (UnitsK F)) FF' := by
      rw [map_sub, hd1d0, sub_zero]
    have h3 : g • (FF' - Work.GroupCohomology.d0 (AbsGal F) (UnitsK F) b) h
        - (FF' - Work.GroupCohomology.d0 (AbsGal F) (UnitsK F) b) (g * h)
        + (FF' - Work.GroupCohomology.d0 (AbsGal F) (UnitsK F) b) g
        = (Work.GroupCohomology.d1 (AbsGal F) (UnitsK F)
            (FF' - Work.GroupCohomology.d0 (AbsGal F) (UnitsK F) b)) (g, h) := rfl
    rw [h3, hsub, ← h1, Work.GroupCohomology.d1_apply]
  have hFF₂_ker : ∀ σ : ↥(lvlFix L), FF₂ (σ : AbsGal F) = 0 := by
    intro σ
    rw [hFF₂]
    simp only [Pi.sub_apply]
    rw [Work.GroupCohomology.d0_apply, hb σ, sub_self]
  -- right invariance of `FF₂` under `Gal(k̄/L)`
  have hright : ∀ (g n : AbsGal F), n ∈ lvlFix L → FF₂ (g * n) = FF₂ g := by
    intro g n hn
    have hD : ∀ x : AbsGal F, g • (FF₂ (x * n) - FF₂ x) = FF₂ (g * x * n) - FF₂ (g * x) := by
      intro x
      have h1 := hkey₂ g (x * n)
      have h2 := hkey₂ g x
      have h3 : resL L (x * n) = resL L x := by
        rw [map_mul, show resL L n = 1 from (mem_ker_resL_iff L n).mpr hn, mul_one]
      rw [h3] at h1
      have h5 : g • FF₂ (x * n) - FF₂ (g * x * n) = g • FF₂ x - FF₂ (g * x) := by
        have h4 : g • FF₂ (x * n) - FF₂ (g * (x * n)) + FF₂ g
            = g • FF₂ x - FF₂ (g * x) + FF₂ g := h1.trans h2.symm
        rw [show g * (x * n) = g * x * n from by group] at h4
        exact add_right_cancel h4
      have h6 : (g • FF₂ (x * n) - g • FF₂ x) - (FF₂ (g * x * n) - FF₂ (g * x)) = 0 := by
        have h8 : (g • FF₂ (x * n) - g • FF₂ x) - (FF₂ (g * x * n) - FF₂ (g * x))
            = (g • FF₂ (x * n) - FF₂ (g * x * n)) - (g • FF₂ x - FF₂ (g * x)) := by abel
        rw [h8, h5, sub_self]
      rw [smul_sub]
      exact sub_eq_zero.mp h6
    have hD1 : FF₂ (1 * n) - FF₂ 1 = 0 := by
      rw [one_mul]
      have h1 : FF₂ n = 0 := hFF₂_ker ⟨n, hn⟩
      have h2 : FF₂ (1 : AbsGal F) = 0 := hFF₂_ker (1 : ↥(lvlFix L))
      rw [h1, h2, sub_self]
    have hg : FF₂ (g * n) - FF₂ g = g • (FF₂ (1 * n) - FF₂ 1) := by
      have h := hD 1
      rw [one_mul, mul_one] at h
      exact h.symm
    rw [hD1, smul_zero] at hg
    exact sub_eq_zero.mp hg
  have hright' : ∀ g h : AbsGal F, resL L g = resL L h → FF₂ g = FF₂ h := by
    intro g h hgh
    have hmem : g⁻¹ * h ∈ lvlFix L := by
      rw [← mem_ker_resL_iff L]
      rw [map_mul, map_inv, hgh, inv_mul_cancel]
    have h2 : h = g * (g⁻¹ * h) := by group
    rw [h2, hright g (g⁻¹ * h) hmem]
  -- values of `FF₂` are fixed by `Gal(k̄/L)`
  have hNnormal : (lvlFix L).Normal := by
    have hker : (resL L).ker = lvlFix L :=
      IntermediateField.restrictNormalHom_ker (L : IntermediateField F (AlgebraicClosure F))
    rw [← hker]
    exact MonoidHom.normal_ker _
  have hfixed : ∀ g : AbsGal F, ∀ σ ∈ lvlFix L, σ • FF₂ g = FF₂ g := by
    intro g σ hσ
    have h1 := hkey₂ σ g
    have h2 : resL L σ = 1 := (mem_ker_resL_iff L σ).mpr hσ
    have h3 : CC' (1, resL L g) = 0 := by
      have h4 : CC' (1, resL L g) = CC' (1, 1) :=
        groupCohomology.cocycles₂_map_one_fst ⟨CC', hCC'mem⟩ (resL L g)
      rw [h4, hCC'_one]
    rw [h2, h3, map_zero] at h1
    have hσ0 : FF₂ σ = 0 := hFF₂_ker ⟨σ, hσ⟩
    have h5 : σ • FF₂ g = FF₂ (σ * g) := by
      have h := h1
      rw [hσ0, add_zero] at h
      exact sub_eq_zero.mp h
    have h6 : g⁻¹ * σ * g ∈ lvlFix L := hNnormal.conj_mem σ hσ g⁻¹
    have h7 : σ * g = g * (g⁻¹ * σ * g) := by group
    rw [h7, hright g (g⁻¹ * σ * g) h6] at h5
    exact h5
  have hfix : ∀ g : AbsGal F, ∃ x : UnitsL L, inclL L x = FF₂ g := by
    intro g
    exact exists_eq_inclL_of_fixed L (FF₂ g) (hfixed g)
  have hsurj : ∀ γ : LevelGal L, ∃ g : AbsGal F, resL L g = γ := resL_surjective L
  set sec : LevelGal L → AbsGal F := fun γ => Classical.choose (hsurj γ) with hsec
  have hsec_spec : ∀ γ, resL L (sec γ) = γ := fun γ => Classical.choose_spec (hsurj γ)
  set gg : LevelGal L → UnitsL L := fun γ => Classical.choose (hfix (sec γ)) with hgg
  have hgg_spec : ∀ γ, inclL L (gg γ) = FF₂ (sec γ) :=
    fun γ => Classical.choose_spec (hfix (sec γ))
  -- the descended cocycle is the differential of `gg`
  have hCC'eq : CC' = (groupCohomology.d₁₂ (LevelRep L)).hom gg := by
    funext p
    obtain ⟨γ, δ⟩ := p
    apply inclL_injective L
    have hA : inclL L (CC' (γ, δ))
        = (sec γ) • FF₂ (sec δ) - FF₂ (sec (γ * δ)) + FF₂ (sec γ) := by
      have h1 := hkey₂ (sec γ) (sec δ)
      rw [hsec_spec γ, hsec_spec δ] at h1
      rw [← h1]
      have h5 : FF₂ (sec γ * sec δ) = FF₂ (sec (γ * δ)) :=
        hright' _ _ (by rw [map_mul, hsec_spec γ, hsec_spec δ, hsec_spec])
      rw [h5]
    have hR : inclL L ((LevelRep L).ρ γ (gg δ) - gg (γ * δ) + gg γ)
        = (sec γ) • FF₂ (sec δ) - FF₂ (sec (γ * δ)) + FF₂ (sec γ) := by
      simp only [map_sub, map_add]
      rw [show (LevelRep L).ρ γ (gg δ)
          = (LevelRep L).ρ (resL L (sec γ)) (gg δ) from by rw [hsec_spec γ]]
      rw [inclL_rho L (sec γ) (gg δ), hgg_spec δ, hgg_spec (γ * δ), hgg_spec γ]
    rw [hA, show (groupCohomology.d₁₂ (LevelRep L)).hom gg (γ, δ)
        = (LevelRep L).ρ γ (gg δ) - gg (γ * δ) + gg γ from by
      rw [groupCohomology.d₁₂_hom_apply]]
    exact hR.symm
  have hCC'cob : CC' ∈ LevelCob L := by
    rw [hCC'eq, LevelCob, groupCohomology.coboundaries₂]
    exact LinearMap.mem_range.mpr ⟨gg, rfl⟩
  have hc_cob : (c : LevelGal L × LevelGal L → UnitsL L) ∈ LevelCob L := by
    have hdec : (c : LevelGal L × LevelGal L → UnitsL L)
        = CC' + (groupCohomology.d₁₂ (LevelRep L)).hom (fun _ : LevelGal L => lam) := by
      rw [hCC']; abel
    rw [hdec]
    exact add_mem hCC'cob (LinearMap.mem_range.mpr ⟨fun _ : LevelGal L => lam, rfl⟩)
  rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
  exact Submodule.mem_comap.mpr hc_cob

/-- **Injectivity of the level inflation** (from Hilbert 90 at `Gal(k̄/L)`). -/
theorem H2_level_injective (L : FiniteGaloisIntermediateField F (AlgebraicClosure F))
    (hH90 : ∀ (f : ↥(lvlFix L) → UnitsK F),
      (∀ σ τ : ↥(lvlFix L), f (σ * τ) = (σ : AbsGal F) • f τ + f σ) →
      Work.AbsoluteKummer.IsLocallyConstant f →
      ∃ b : UnitsK F, ∀ σ : ↥(lvlFix L), (σ : AbsGal F) • b - b = f σ) :
    Function.Injective (psiTilde L) := by
  intro x y hxy
  have h0 : psiTilde L (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  exact sub_eq_zero.mp ((psiTilde_eq_zero_iff L hH90 (x - y)).mp h0)

end Work.SSGRoute.PTCore
