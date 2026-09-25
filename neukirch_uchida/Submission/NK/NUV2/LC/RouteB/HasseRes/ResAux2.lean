import Mathlib
import Submission.NK.NUV2.LC.RouteB.DictionaryDeps2

/-!
# The split case of the vanishing direction of the localisation dictionary

Infrastructure for `NK.NUV2.LC.RouteB.loc_eq_zero_of_localLevelGroup_subsingleton`.

The module builds, for an inclusion `V ≤ U` of closed subgroups of `Gal(K'/K)`, the
*restriction* maps on the two colimits of the `HassePrinciple` chapter

* `resMu_h p h : MuColim p U → MuColim p V` (coefficients `μ_p`),
* `resUnits_h h : H2Units U → H2Units V` (coefficients the units),

together with

* the Kummer square `kummerColim p V (resMu_h h x) = resUnits_h h (kummerColim p U x)`,
* the comparison square between the `μ_p`-colimit and `NK.BrauerHasse.H2Profinite`
  (`muToH2Sub_h`, the general-subgroup version of `NK.NUV2.ABHN.muToH2`), and
* the naturality of the level comparison `NK.NUV2.ABHN.levelCompareRoot` for the restriction.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open CategoryTheory Representation

namespace NK.NUV2.LC.RouteB

open NK.BrauerHasse


section Generic

variable {k : Type} [CommRing k] {G₀ G₁ : Type} [Group G₀] [Group G₁]

/-- **Composition of `groupCohomology.map` with the identity group homomorphism on the right**: for
`φ : Rep.res f A ⟶ B` and `ψ : B ⟶ C` over the target group of `f`, the composite of the induced
maps is induced by `φ ≫ ψ` (the group homomorphism of the composite being `f.comp (id) = f`). -/
lemma map_comp_id_right_h (f : G₁ →* G₀) {A : Rep k G₀} {B : Rep k G₁} {C : Rep k G₁}
    (φ : Rep.res f A ⟶ B) (ψ : B ⟶ C) :
    groupCohomology.map f φ 2 ≫ groupCohomology.map (MonoidHom.id G₁) ψ 2
      = groupCohomology.map f (φ ≫ ψ) 2 := by
  have h := groupCohomology.map_comp (f := f) (g := MonoidHom.id G₁)
    (A := A) (B := B) (C := C) (φ := φ) (ψ := ψ) (n := 2)
  rw [← h]
  refine groupCohomology.map_congr (f := f.comp (MonoidHom.id G₁)) (g := f) (A := A) (B := C)
    (φ := (Rep.resFunctor (MonoidHom.id G₁)).map φ ≫ ψ) (ψ := φ ≫ ψ)
    (MonoidHom.comp_id f) ?_ 2
  rfl

/-- **Composition of `groupCohomology.map` with the identity group homomorphism on the left**. -/
lemma map_id_comp_left_h {A : Rep k G₀} {B : Rep k G₀} (f : G₁ →* G₀) {C : Rep k G₁}
    (φ : A ⟶ B) (ψ : Rep.res f B ⟶ C) :
    groupCohomology.map (MonoidHom.id G₀) φ 2 ≫ groupCohomology.map f ψ 2
      = groupCohomology.map f (Rep.resMap f φ ≫ ψ) 2 := by
  have h := groupCohomology.map_comp (f := MonoidHom.id G₀) (g := f)
    (A := A) (B := B) (C := C) (φ := φ) (ψ := ψ) (n := 2)
  rw [← h]
  refine groupCohomology.map_congr (f := (MonoidHom.id G₀).comp f) (g := f) (A := A) (B := C)
    (φ := (Rep.resFunctor f).map φ ≫ ψ) (ψ := Rep.resMap f φ ≫ ψ)
    (MonoidHom.id_comp f) ?_ 2
  rfl

end Generic

section Restrict

variable {K K' : Type} [Field K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-! ## §1. The level groups -/

/-- The restriction of the level group surjection along an inclusion `V ≤ U` of closed subgroups:
the composite `V ⧸ (V ⊓ Gal(K'/L)) → U ⧸ (U ⊓ Gal(K'/L)) → Gal(L/K)` is the surjection of `V`. -/
lemma levelGroupRestrictHom_levelInclHom_h {U V : Subgroup Gal(K'/K)} (h : V ≤ U)
    (L : FiniteGaloisIntermediateField K K') (q : LevelGroup V L) :
    NK.HassePrinciple.levelGroupRestrictHom U L (levelInclHom h L q) =
      NK.HassePrinciple.levelGroupRestrictHom V L q := by
  induction q using QuotientGroup.induction_on with
  | H v => rfl

/-- The inclusion of level groups commutes with the inflation maps. -/
lemma levelInclHom_comp_levelQuotHom_h {U V : Subgroup Gal(K'/K)} (hV : V ≤ U)
    {L M : FiniteGaloisIntermediateField K K'} (h : L ≤ M) :
    (levelInclHom hV L).comp (levelQuotHom (U := V) h) =
      (levelQuotHom (U := U) h).comp (levelInclHom hV M) := by
  apply MonoidHom.ext
  intro x
  induction x using QuotientGroup.induction_on with
  | H y => rfl

/-! ## §2. The coefficient morphisms of the restriction -/

/-- **The coefficient morphism of the restriction on `μ_p`**: the identity of `μ_p(L)`. -/
noncomputable def muResCoeff_h (p : ℕ) {U V : Subgroup Gal(K'/K)} (h : V ≤ U)
    (L : FiniteGaloisIntermediateField K K') :
    Rep.res (levelInclHom h L) (NK.HassePrinciple.muLevelRep (K := K) (K' := K') p U L) ⟶
      NK.HassePrinciple.muLevelRep (K := K) (K' := K') p V L :=
  Rep.ofHom (LinearMap.intertwiningMap_of_isIntertwiningMap
    (ρ := (Rep.res (levelInclHom h L)
      (NK.HassePrinciple.muLevelRep (K := K) (K' := K') p U L)).ρ)
    (σ := (NK.HassePrinciple.muLevelRep (K := K) (K' := K') p V L).ρ)
    (f := LinearMap.id)
    (fun q x => by
      simp only [MonoidHom.comp_apply]
      rw [levelGroupRestrictHom_levelInclHom_h (K := K) (K' := K') h L q]
      rfl))

/-- The coefficient morphism of the restriction acts by the identity on `μ_p(L)`. -/
lemma muResCoeff_apply_h (p : ℕ) {U V : Subgroup Gal(K'/K)} (h : V ≤ U)
    (L : FiniteGaloisIntermediateField K K')
    (x : (Rep.res (levelInclHom h L)
      (NK.HassePrinciple.muLevelRep (K := K) (K' := K') p U L)).V) :
    (muResCoeff_h (K := K) (K' := K') p h L).hom.toLinearMap x = x := rfl

/-- **The coefficient morphism of the restriction on the units**: the identity of `Lˣ`. -/
noncomputable def unitsResCoeff_h {U V : Subgroup Gal(K'/K)} (h : V ≤ U)
    (L : FiniteGaloisIntermediateField K K') :
    Rep.res (levelInclHom h L) (NK.HassePrinciple.unitsLevelRep (K := K) (K' := K') U L) ⟶
      NK.HassePrinciple.unitsLevelRep (K := K) (K' := K') V L :=
  Rep.ofHom (LinearMap.intertwiningMap_of_isIntertwiningMap
    (ρ := (Rep.res (levelInclHom h L)
      (NK.HassePrinciple.unitsLevelRep (K := K) (K' := K') U L)).ρ)
    (σ := (NK.HassePrinciple.unitsLevelRep (K := K) (K' := K') V L).ρ)
    (f := LinearMap.id)
    (fun q x => by
      simp only [MonoidHom.comp_apply]
      rw [levelGroupRestrictHom_levelInclHom_h (K := K) (K' := K') h L q]
      rfl))

/-- The coefficient morphism of the restriction on the units acts by the identity. -/
lemma unitsResCoeff_apply_h {U V : Subgroup Gal(K'/K)} (h : V ≤ U)
    (L : FiniteGaloisIntermediateField K K')
    (x : (Rep.res (levelInclHom h L)
      (NK.HassePrinciple.unitsLevelRep (K := K) (K' := K') U L)).V) :
    (unitsResCoeff_h (K := K) (K' := K') h L).hom.toLinearMap x = x := rfl

/-! ## §3. The restriction on the level cohomology -/

/-- **The restriction on the level cohomology with `μ_p`-coefficients.** -/
noncomputable def muResLevel_h (p : ℕ) {U V : Subgroup Gal(K'/K)} (h : V ≤ U)
    (L : FiniteGaloisIntermediateField K K') :
    NK.HassePrinciple.MuLevelH2 (K := K) (K' := K') p U L ⟶
      NK.HassePrinciple.MuLevelH2 (K := K) (K' := K') p V L :=
  groupCohomology.map (levelInclHom h L) (muResCoeff_h (K := K) (K' := K') p h L) 2

/-- **The restriction on the level cohomology with unit coefficients.** -/
noncomputable def unitsResLevel_h {U V : Subgroup Gal(K'/K)} (h : V ≤ U)
    (L : FiniteGaloisIntermediateField K K') :
    NK.HassePrinciple.UnitsLevelH2 (K := K) (K' := K') U L ⟶
      NK.HassePrinciple.UnitsLevelH2 (K := K) (K' := K') V L :=
  groupCohomology.map (levelInclHom h L) (unitsResCoeff_h (K := K) (K' := K') h L) 2

/-- **The restriction commutes with the Kummer inclusion of the coefficients.** -/
theorem muResCoeff_muToUnits_h (p : ℕ) {U V : Subgroup Gal(K'/K)} (h : V ≤ U)
    (L : FiniteGaloisIntermediateField K K') :
    (muResCoeff_h (K := K) (K' := K') p h L ≫ NK.HassePrinciple.muToUnits (K := K) (K' := K') p V L) =
      (Rep.resMap (levelInclHom h L) (NK.HassePrinciple.muToUnits (K := K) (K' := K') p U L) ≫
        unitsResCoeff_h (K := K) (K' := K') h L) := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  simp only [Rep.hom_comp, Representation.IntertwiningMap.comp_toLinearMap, LinearMap.comp_apply,
    Rep.resMap_hom_toLinearMap, NK.HassePrinciple.muToUnits]
  rw [show (Rep.Hom.hom (muResCoeff_h (K := K) (K' := K') p h L)).toLinearMap x = x from rfl,
    show (Rep.Hom.hom (unitsResCoeff_h (K := K) (K' := K') h L)).toLinearMap
      ((Rep.Hom.hom (NK.HassePrinciple.kummerIncl p K ↥L)).toLinearMap x) =
      (Rep.Hom.hom (NK.HassePrinciple.kummerIncl p K ↥L)).toLinearMap x from rfl]

/-- **The restriction commutes with inflation** (`μ_p`-coefficients). -/
theorem muResLevel_levelMap_h (p : ℕ) {U V : Subgroup Gal(K'/K)} (h : V ≤ U)
    {L M : FiniteGaloisIntermediateField K K'} (hLM : L ≤ M) :
    muResLevel_h (K := K) (K' := K') p h L ≫ NK.HassePrinciple.muLevelMap (K := K) (K' := K') p V hLM =
      NK.HassePrinciple.muLevelMap (K := K) (K' := K') p U hLM ≫
        muResLevel_h (K := K) (K' := K') p h M := by
  have hcomp : (levelInclHom h L).comp (levelQuotHom (U := V) hLM) =
      (levelQuotHom (U := U) hLM).comp (levelInclHom h M) :=
    levelInclHom_comp_levelQuotHom_h h hLM
  have hcoe : ((Rep.resMap (levelQuotHom (U := V) hLM)
        (muResCoeff_h (K := K) (K' := K') p h L)) ≫
      NK.HassePrinciple.muLevelMapCoeff (K := K) (K' := K') p V hLM).hom.toLinearMap =
      ((Rep.resMap (levelInclHom h M)
        (NK.HassePrinciple.muLevelMapCoeff (K := K) (K' := K') p U hLM)) ≫
        muResCoeff_h (K := K) (K' := K') p h M).hom.toLinearMap := by
    apply LinearMap.ext
    intro x
    rfl
  have hmc := groupCohomology.map_comp (f := levelInclHom h L)
    (g := NK.BrauerHasse.levelQuotHom (U := V) hLM)
    (A := NK.HassePrinciple.muLevelRep (K := K) (K' := K') p U L)
    (B := NK.HassePrinciple.muLevelRep (K := K) (K' := K') p V L)
    (C := NK.HassePrinciple.muLevelRep (K := K) (K' := K') p V M)
    (φ := muResCoeff_h (K := K) (K' := K') p h L)
    (ψ := NK.HassePrinciple.muLevelMapCoeff (K := K) (K' := K') p V hLM) (n := 2)
  have hmc' := groupCohomology.map_comp (f := NK.BrauerHasse.levelQuotHom (U := U) hLM)
    (g := levelInclHom h M)
    (A := NK.HassePrinciple.muLevelRep (K := K) (K' := K') p U L)
    (B := NK.HassePrinciple.muLevelRep (K := K) (K' := K') p U M)
    (C := NK.HassePrinciple.muLevelRep (K := K) (K' := K') p V M)
    (φ := NK.HassePrinciple.muLevelMapCoeff (K := K) (K' := K') p U hLM)
    (ψ := muResCoeff_h (K := K) (K' := K') p h M) (n := 2)
  rw [muResLevel_h, NK.HassePrinciple.muLevelMap, muResLevel_h, NK.HassePrinciple.muLevelMap,
    ← hmc, ← hmc']
  exact groupCohomology.map_congr hcomp hcoe 2

/-- Elementwise form of `muResLevel_levelMap_h`. -/
theorem muResLevel_levelMap_apply_h (p : ℕ) {U V : Subgroup Gal(K'/K)} (h : V ≤ U)
    {L M : FiniteGaloisIntermediateField K K'} (hLM : L ≤ M)
    (a : NK.HassePrinciple.MuLevelH2 (K := K) (K' := K') p U L) :
    (muResLevel_h (K := K) (K' := K') p h M) ((NK.HassePrinciple.muLevelMap (K := K) (K' := K') p U hLM) a) =
      (NK.HassePrinciple.muLevelMap (K := K) (K' := K') p V hLM)
        ((muResLevel_h (K := K) (K' := K') p h L) a) := by
  have h1 := congrArg (fun (k : NK.HassePrinciple.MuLevelH2 (K := K) (K' := K') p U L ⟶
      NK.HassePrinciple.MuLevelH2 (K := K) (K' := K') p V M) => k.hom a)
    (muResLevel_levelMap_h (K := K) (K' := K') p h hLM)
  simpa using h1.symm

/-- **The restriction commutes with inflation** (unit coefficients). -/
theorem unitsResLevel_levelMap_h {U V : Subgroup Gal(K'/K)} (h : V ≤ U)
    {L M : FiniteGaloisIntermediateField K K'} (hLM : L ≤ M) :
    unitsResLevel_h (K := K) (K' := K') h L ≫ NK.HassePrinciple.unitsLevelMap (K := K) (K' := K') V hLM =
      NK.HassePrinciple.unitsLevelMap (K := K) (K' := K') U hLM ≫
        unitsResLevel_h (K := K) (K' := K') h M := by
  have hcomp : (levelInclHom h L).comp (levelQuotHom (U := V) hLM) =
      (levelQuotHom (U := U) hLM).comp (levelInclHom h M) :=
    levelInclHom_comp_levelQuotHom_h h hLM
  have hcoe : ((Rep.resMap (levelQuotHom (U := V) hLM)
        (unitsResCoeff_h (K := K) (K' := K') h L)) ≫
      NK.HassePrinciple.unitsLevelMapCoeff (K := K) (K' := K') V hLM).hom.toLinearMap =
      ((Rep.resMap (levelInclHom h M)
        (NK.HassePrinciple.unitsLevelMapCoeff (K := K) (K' := K') U hLM)) ≫
        unitsResCoeff_h (K := K) (K' := K') h M).hom.toLinearMap := by
    apply LinearMap.ext
    intro x
    rfl
  have hmc := groupCohomology.map_comp (f := levelInclHom h L)
    (g := NK.BrauerHasse.levelQuotHom (U := V) hLM)
    (A := NK.HassePrinciple.unitsLevelRep (K := K) (K' := K') U L)
    (B := NK.HassePrinciple.unitsLevelRep (K := K) (K' := K') V L)
    (C := NK.HassePrinciple.unitsLevelRep (K := K) (K' := K') V M)
    (φ := unitsResCoeff_h (K := K) (K' := K') h L)
    (ψ := NK.HassePrinciple.unitsLevelMapCoeff (K := K) (K' := K') V hLM) (n := 2)
  have hmc' := groupCohomology.map_comp (f := NK.BrauerHasse.levelQuotHom (U := U) hLM)
    (g := levelInclHom h M)
    (A := NK.HassePrinciple.unitsLevelRep (K := K) (K' := K') U L)
    (B := NK.HassePrinciple.unitsLevelRep (K := K) (K' := K') U M)
    (C := NK.HassePrinciple.unitsLevelRep (K := K) (K' := K') V M)
    (φ := NK.HassePrinciple.unitsLevelMapCoeff (K := K) (K' := K') U hLM)
    (ψ := unitsResCoeff_h (K := K) (K' := K') h M) (n := 2)
  rw [unitsResLevel_h, NK.HassePrinciple.unitsLevelMap, unitsResLevel_h,
    NK.HassePrinciple.unitsLevelMap, ← hmc, ← hmc']
  exact groupCohomology.map_congr hcomp hcoe 2

/-- Elementwise form of `unitsResLevel_levelMap_h`. -/
theorem unitsResLevel_levelMap_apply_h {U V : Subgroup Gal(K'/K)} (h : V ≤ U)
    {L M : FiniteGaloisIntermediateField K K'} (hLM : L ≤ M)
    (a : NK.HassePrinciple.UnitsLevelH2 (K := K) (K' := K') U L) :
    (unitsResLevel_h (K := K) (K' := K') h M) ((NK.HassePrinciple.unitsLevelMap (K := K) (K' := K') U hLM) a) =
      (NK.HassePrinciple.unitsLevelMap (K := K) (K' := K') V hLM)
        ((unitsResLevel_h (K := K) (K' := K') h L) a) := by
  have h1 := congrArg (fun (k : NK.HassePrinciple.UnitsLevelH2 (K := K) (K' := K') U L ⟶
      NK.HassePrinciple.UnitsLevelH2 (K := K) (K' := K') V M) => k.hom a)
    (unitsResLevel_levelMap_h (K := K) (K' := K') h hLM)
  simpa using h1.symm

/-! ## §4. The Kummer square at the level -/

/-- **Naturality of the Kummer morphism for the restriction.** -/
theorem kummerLevel_muResLevel_h (p : ℕ) {U V : Subgroup Gal(K'/K)} (h : V ≤ U)
    (L : FiniteGaloisIntermediateField K K') (a : NK.HassePrinciple.MuLevelH2 (K := K) (K' := K') p U L) :
    (NK.HassePrinciple.kummerLevel p V L).hom ((muResLevel_h (K := K) (K' := K') p h L).hom a) =
      (unitsResLevel_h (K := K) (K' := K') h L).hom
        ((NK.HassePrinciple.kummerLevel p U L).hom a) := by
  have hL : (NK.HassePrinciple.kummerLevel p V L).hom ((muResLevel_h (K := K) (K' := K') p h L).hom a)
      = ((muResLevel_h (K := K) (K' := K') p h L ≫
          NK.HassePrinciple.kummerLevel p V L)).hom a := rfl
  have hR : (unitsResLevel_h (K := K) (K' := K') h L).hom
        ((NK.HassePrinciple.kummerLevel p U L).hom a)
      = ((NK.HassePrinciple.kummerLevel p U L ≫
          unitsResLevel_h (K := K) (K' := K') h L)).hom a := rfl
  rw [hL, hR]
  have e1 : (muResLevel_h (K := K) (K' := K') p h L ≫ NK.HassePrinciple.kummerLevel p V L)
      = groupCohomology.map (levelInclHom h L)
          (muResCoeff_h (K := K) (K' := K') p h L ≫
            NK.HassePrinciple.muToUnits (K := K) (K' := K') p V L) 2 := by
    rw [muResLevel_h, NK.HassePrinciple.kummerLevel]
    exact map_comp_id_right_h (levelInclHom h L) (muResCoeff_h (K := K) (K' := K') p h L)
      (NK.HassePrinciple.muToUnits (K := K) (K' := K') p V L)
  have e2 : (NK.HassePrinciple.kummerLevel p U L ≫ unitsResLevel_h (K := K) (K' := K') h L)
      = groupCohomology.map (levelInclHom h L)
          (Rep.resMap (levelInclHom h L) (NK.HassePrinciple.muToUnits (K := K) (K' := K') p U L) ≫
            unitsResCoeff_h (K := K) (K' := K') h L) 2 := by
    rw [unitsResLevel_h, NK.HassePrinciple.kummerLevel]
    exact map_id_comp_left_h (levelInclHom h L) (NK.HassePrinciple.muToUnits (K := K) (K' := K') p U L)
      (unitsResCoeff_h (K := K) (K' := K') h L)
  rw [e1, e2, muResCoeff_muToUnits_h]

/-! ## §5. The restriction on the colimits -/

/-- **The restriction map on the `μ_p`-colimit.** -/
noncomputable def resMu_h (p : ℕ) {U V : Subgroup Gal(K'/K)} (h : V ≤ U) :
    NK.HassePrinciple.MuColim (K := K) (K' := K') p U →
      NK.HassePrinciple.MuColim (K := K) (K' := K') p V :=
  (NK.HassePrinciple.muLevelSystem (K := K) (K' := K') p U).lift
    (fun L a => NK.HassePrinciple.MuColim.ofLevel p V L
      (muResLevel_h (K := K) (K' := K') p h L a))
    (by
      intro L L' hLL' a
      show NK.HassePrinciple.MuColim.ofLevel p V L'
          (muResLevel_h (K := K) (K' := K') p h L'
            ((NK.HassePrinciple.muLevelMap (K := K) (K' := K') p U
              ((FiniteGaloisIntermediateField.le_iff L L').mp hLL')) a)) =
        NK.HassePrinciple.MuColim.ofLevel p V L
          (muResLevel_h (K := K) (K' := K') p h L a)
      rw [muResLevel_levelMap_apply_h (K := K) (K' := K') p h
        ((FiniteGaloisIntermediateField.le_iff L L').mp hLL') a]
      exact NK.BrauerTwist.LevelSystem.ofLevel_map
        (S := NK.HassePrinciple.muLevelSystem (K := K) (K' := K') p V) hLL'
        ((muResLevel_h (K := K) (K' := K') p h L) a))

/-- The computation rule for the restriction on the `μ_p`-colimit. -/
@[simp]
lemma resMu_ofLevel_h (p : ℕ) {U V : Subgroup Gal(K'/K)} (h : V ≤ U)
    (L : FiniteGaloisIntermediateField K K')
    (a : NK.HassePrinciple.MuLevelH2 (K := K) (K' := K') p U L) :
    resMu_h (K := K) (K' := K') p h (NK.HassePrinciple.MuColim.ofLevel p U L a) =
      NK.HassePrinciple.MuColim.ofLevel p V L (muResLevel_h (K := K) (K' := K') p h L a) := rfl

/-- **The restriction map on the units colimit.** -/
noncomputable def resUnits_h {U V : Subgroup Gal(K'/K)} (h : V ≤ U) :
    NK.HassePrinciple.H2Units (K := K) (K' := K') U →
      NK.HassePrinciple.H2Units (K := K) (K' := K') V :=
  (NK.HassePrinciple.unitsLevelSystem (K := K) (K' := K') U).lift
    (fun L a => NK.HassePrinciple.H2Units.ofLevel V L
      (unitsResLevel_h (K := K) (K' := K') h L a))
    (by
      intro L L' hLL' a
      show NK.HassePrinciple.H2Units.ofLevel V L'
          (unitsResLevel_h (K := K) (K' := K') h L'
            ((NK.HassePrinciple.unitsLevelMap (K := K) (K' := K') U
              ((FiniteGaloisIntermediateField.le_iff L L').mp hLL')) a)) =
        NK.HassePrinciple.H2Units.ofLevel V L
          (unitsResLevel_h (K := K) (K' := K') h L a)
      rw [unitsResLevel_levelMap_apply_h (K := K) (K' := K') h
        ((FiniteGaloisIntermediateField.le_iff L L').mp hLL') a]
      exact NK.BrauerTwist.LevelSystem.ofLevel_map
        (S := NK.HassePrinciple.unitsLevelSystem (K := K) (K' := K') V) hLL'
        ((unitsResLevel_h (K := K) (K' := K') h L) a))

/-- The computation rule for the restriction on the units colimit. -/
@[simp]
lemma resUnits_ofLevel_h {U V : Subgroup Gal(K'/K)} (h : V ≤ U)
    (L : FiniteGaloisIntermediateField K K')
    (a : NK.HassePrinciple.UnitsLevelH2 (K := K) (K' := K') U L) :
    resUnits_h (K := K) (K' := K') h (NK.HassePrinciple.H2Units.ofLevel U L a) =
      NK.HassePrinciple.H2Units.ofLevel V L (unitsResLevel_h (K := K) (K' := K') h L a) := rfl

/-- The zero of the units colimit is the class of the zero of any level. -/
lemma H2Units_ofLevel_zero'_h (V : Subgroup Gal(K'/K))
    (L : FiniteGaloisIntermediateField K K') :
    NK.HassePrinciple.H2Units.ofLevel V L
      (0 : NK.HassePrinciple.UnitsLevelH2 (K := K) (K' := K') V L) = 0 := by
  have h := NK.NUV2.ABHN.H2Units.ofLevel_add (K := K) (K' := K') V L
    (0 : NK.HassePrinciple.UnitsLevelH2 (K := K) (K' := K') V L) 0
  rw [add_zero] at h
  have h2 : NK.HassePrinciple.H2Units.ofLevel V L
        (0 : NK.HassePrinciple.UnitsLevelH2 (K := K) (K' := K') V L)
      + NK.HassePrinciple.H2Units.ofLevel V L
        (0 : NK.HassePrinciple.UnitsLevelH2 (K := K) (K' := K') V L)
      = NK.HassePrinciple.H2Units.ofLevel V L
        (0 : NK.HassePrinciple.UnitsLevelH2 (K := K) (K' := K') V L) + 0 := by
    rw [add_zero]
    exact h.symm
  exact add_left_cancel h2

/-- The zero of the `μ_p`-colimit is the class of the zero of the bottom level. -/
lemma MuColim_ofLevel_zero_h (p : ℕ) (V : Subgroup Gal(K'/K)) :
    NK.HassePrinciple.MuColim.ofLevel p V (⊥ : FiniteGaloisIntermediateField K K')
      (0 : NK.HassePrinciple.MuLevelH2 (K := K) (K' := K') p V ⊥) = 0 := by
  have h := NK.NUV2.ABHN.MuColim.ofLevel_add (K := K) (K' := K') p V
    (⊥ : FiniteGaloisIntermediateField K K')
    (0 : NK.HassePrinciple.MuLevelH2 (K := K) (K' := K') p V ⊥) 0
  rw [add_zero] at h
  have h2 : NK.HassePrinciple.MuColim.ofLevel p V (⊥ : FiniteGaloisIntermediateField K K')
        (0 : NK.HassePrinciple.MuLevelH2 (K := K) (K' := K') p V ⊥)
      + NK.HassePrinciple.MuColim.ofLevel p V (⊥ : FiniteGaloisIntermediateField K K')
        (0 : NK.HassePrinciple.MuLevelH2 (K := K) (K' := K') p V ⊥)
      = NK.HassePrinciple.MuColim.ofLevel p V (⊥ : FiniteGaloisIntermediateField K K')
        (0 : NK.HassePrinciple.MuLevelH2 (K := K) (K' := K') p V ⊥) + 0 := by
    rw [add_zero]
    exact h.symm
  exact add_left_cancel h2

/-- **Every class of the `μ_p`-colimit comes from a level.** -/
lemma MuColim_ofLevel_surjective_h (p : ℕ) (V : Subgroup Gal(K'/K))
    (x : NK.HassePrinciple.MuColim (K := K) (K' := K') p V) :
    ∃ (L : FiniteGaloisIntermediateField K K')
      (a : NK.HassePrinciple.MuLevelH2 (K := K) (K' := K') p V L),
      NK.HassePrinciple.MuColim.ofLevel p V L a = x :=
  (NK.HassePrinciple.muLevelSystem (K := K) (K' := K') p V).ofLevel_surjective x

/-- **The Kummer square at the level of the colimits**: the restriction of the Kummer image is the
Kummer image of the restriction. -/
theorem kummerColim_resMu_h (p : ℕ) {U V : Subgroup Gal(K'/K)} (h : V ≤ U)
    (x : NK.HassePrinciple.MuColim (K := K) (K' := K') p U) :
    NK.HassePrinciple.kummerColim (K := K) (K' := K') p V
        (resMu_h (K := K) (K' := K') p h x) =
      resUnits_h (K := K) (K' := K') h
        (NK.HassePrinciple.kummerColim (K := K) (K' := K') p U x) := by
  obtain ⟨L, a, rfl⟩ := MuColim_ofLevel_surjective_h (K := K) (K' := K') p U x
  rw [resMu_ofLevel_h (K := K) (K' := K') p h L a, NK.HassePrinciple.kummerColim_ofLevel,
    NK.HassePrinciple.kummerColim_ofLevel,
    resUnits_ofLevel_h (K := K) (K' := K') h L
      ((NK.HassePrinciple.kummerLevel (K := K) (K' := K') p U L).hom a),
    kummerLevel_muResLevel_h]

/-! ## §6. The comparison with the trivial coefficients -/

/-- **Naturality of the level comparison for the restriction.** -/
theorem levelCompare_muResLevel_h (p : ℕ) [NeZero p] {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    {U V : Subgroup Gal(K'/K)} (h : V ≤ U)
    (L : FiniteGaloisIntermediateField K K')
    (a : NK.HassePrinciple.MuLevelH2 (K := K) (K' := K') p U L) :
    NK.NUV2.ABHN.levelCompareRoot p hζ V L (muResLevel_h (K := K) (K' := K') p h L a) =
      H2.map (levelInclHom h L) (NK.NUV2.ABHN.levelCompareRoot p hζ U L a) := by
  show NK.IndecomposedDeep.H2congr (A := NK.HassePrinciple.muLevelRep (K := K) (K' := K') p V L)
        (B := NK.NUV2.ABHN.trivLevelRep (K := K) (K' := K') p V L)
        (NK.NUV2.ABHN.muAddEquiv p ζ hζ L)
        (NK.NUV2.ABHN.muAddEquiv_equivariance p hζ V L)
        (groupCohomology.map (levelInclHom h L) (muResCoeff_h (K := K) (K' := K') p h L) 2 a) =
      groupCohomology.map (levelInclHom h L)
        (NK.BrauerHasse.trivHom (levelInclHom h L)) 2
        (NK.IndecomposedDeep.H2congr
          (A := NK.HassePrinciple.muLevelRep (K := K) (K' := K') p U L)
          (B := NK.NUV2.ABHN.trivLevelRep (K := K) (K' := K') p U L)
          (NK.NUV2.ABHN.muAddEquiv p ζ hζ L)
          (NK.NUV2.ABHN.muAddEquiv_equivariance p hζ U L) a)
  exact NK.IndecomposedDeep.H2congr_map (levelInclHom h L)
    (muResCoeff_h (K := K) (K' := K') p h L)
    (NK.BrauerHasse.trivHom (levelInclHom h L))
    (NK.NUV2.ABHN.muAddEquiv p ζ hζ L) (NK.NUV2.ABHN.muAddEquiv p ζ hζ L)
    (NK.NUV2.ABHN.muAddEquiv_equivariance p hζ U L)
    (NK.NUV2.ABHN.muAddEquiv_equivariance p hζ V L)
    (fun x => rfl) a

/-- The level comparison sends zero to zero. -/
lemma levelCompare_zero_h (p : ℕ) [NeZero p] {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (V : Subgroup Gal(K'/K)) (L : FiniteGaloisIntermediateField K K') :
    NK.NUV2.ABHN.levelCompareRoot p hζ V L
      (0 : NK.HassePrinciple.MuLevelH2 (K := K) (K' := K') p V L) = 0 := by
  show NK.IndecomposedDeep.H2congr (A := NK.HassePrinciple.muLevelRep (K := K) (K' := K') p V L)
      (B := NK.NUV2.ABHN.trivLevelRep (K := K) (K' := K') p V L)
      (NK.NUV2.ABHN.muAddEquiv p ζ hζ L)
      (NK.NUV2.ABHN.muAddEquiv_equivariance p hζ V L)
      (0 : NK.HassePrinciple.MuLevelH2 (K := K) (K' := K') p V L) = 0
  exact NK.IndecomposedDeep.H2congr_zero _ _

/-- **The comparison map from the `μ_p`-colimit at a closed subgroup `V` to the profinite
cohomology `H²(V, Z/p)`**, the general-subgroup version of `NK.NUV2.ABHN.muToH2`. -/
noncomputable def muToH2Sub_h (p : ℕ) [NeZero p] {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (V : Subgroup Gal(K'/K)) :
    NK.HassePrinciple.MuColim (K := K) (K' := K') p V →
      H2Profinite (K := K) (K' := K') p V :=
  (NK.HassePrinciple.muLevelSystem (K := K) (K' := K') p V).lift
    (fun L a => H2Profinite.ofLevel L (NK.NUV2.ABHN.levelCompareRoot p hζ V L a))
    (by
      intro L L' hLL' a
      show H2Profinite.ofLevel L'
          (NK.NUV2.ABHN.levelCompareRoot p hζ V L'
            ((NK.HassePrinciple.muLevelMap (K := K) (K' := K') p V
              ((FiniteGaloisIntermediateField.le_iff L L').mp hLL')) a)) =
        H2Profinite.ofLevel L (NK.NUV2.ABHN.levelCompareRoot p hζ V L a)
      rw [NK.NUV2.ABHN.levelCompare_muLevelMap p hζ V
          ((FiniteGaloisIntermediateField.le_iff L L').mp hLL') a,
        H2Profinite.ofLevel_levelMap])

/-- The computation rule for `muToH2Sub_h`. -/
@[simp]
lemma muToH2Sub_ofLevel_h (p : ℕ) [NeZero p] {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (V : Subgroup Gal(K'/K)) (L : FiniteGaloisIntermediateField K K')
    (a : NK.HassePrinciple.MuLevelH2 (K := K) (K' := K') p V L) :
    muToH2Sub_h (K := K) (K' := K') p hζ V (NK.HassePrinciple.MuColim.ofLevel p V L a) =
      H2Profinite.ofLevel L (NK.NUV2.ABHN.levelCompareRoot p hζ V L a) := rfl

/-- `muToH2Sub_h` sends zero to zero. -/
lemma muToH2Sub_zero_h (p : ℕ) [NeZero p] {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (V : Subgroup Gal(K'/K)) :
    muToH2Sub_h (K := K) (K' := K') p hζ V
      (0 : NK.HassePrinciple.MuColim (K := K) (K' := K') p V) = 0 := by
  rw [show (0 : NK.HassePrinciple.MuColim (K := K) (K' := K') p V) =
      NK.HassePrinciple.MuColim.ofLevel p V (⊥ : FiniteGaloisIntermediateField K K') 0
    from (MuColim_ofLevel_zero_h (K := K) (K' := K') p V).symm]
  rw [muToH2Sub_ofLevel_h (K := K) (K' := K') p hζ V ⊥ 0, levelCompare_zero_h,
    NK.BrauerHasse.ofLevel_zero]

/-- The general-subgroup comparison restricts to the one at `⊤`. -/
lemma muToH2Sub_top_h (p : ℕ) [NeZero p] {ζ : K} (hζ : IsPrimitiveRoot ζ p) :
    muToH2Sub_h (K := K) (K' := K') p hζ ⊤ = NK.NUV2.ABHN.muToH2 p hζ := rfl

end Restrict

section NumberFieldBase

variable {K K' : Type} [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-- **The comparison square for the restriction.** -/
theorem res_muToH2Sub_h (p : ℕ) [NeZero p] {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    {U V : Subgroup Gal(K'/K)} (h : V ≤ U)
    (x : NK.HassePrinciple.MuColim (K := K) (K' := K') p U) :
    NK.LocalDecomposition.H2Profinite.res p h (muToH2Sub_h (K := K) (K' := K') p hζ U x) =
      muToH2Sub_h (K := K) (K' := K') p hζ V (resMu_h (K := K) (K' := K') p h x) := by
  obtain ⟨L, a, rfl⟩ := MuColim_ofLevel_surjective_h (K := K) (K' := K') p U x
  rw [muToH2Sub_ofLevel_h (K := K) (K' := K') p hζ U L a,
    NK.LocalDecomposition.H2Profinite.res_ofLevel,
    resMu_ofLevel_h (K := K) (K' := K') p h L a,
    muToH2Sub_ofLevel_h (K := K) (K' := K') p hζ V L (muResLevel_h (K := K) (K' := K') p h L a),
    levelCompare_muResLevel_h]

end NumberFieldBase

/-- **Split case of the vanishing direction**: if the local level group at the level `⟨E⟩` is
trivial (equivalently `v` splits completely in `E`), the class vanishes at `A`.
This is the `⟸` direction of the dictionary of `exists_cyclicClassColim` in the case
`localNormPreimage v = ⊤`; the complementary case is handled by
`NUV2/LC/RouteB/localNormPreimage_eq_unitsNorm_of_nonsplit`.

Route.  With `L₀ := ⟨E⟩`, `cls' := (unitsTransport L₀).symm (cycClassOf g hg b)`:
* `htriv` says `⊤ ⊓ D_A ≤ L₀.fixingSubgroup` (via `Subgroup.subgroupOf_eq_top`,
  `QuotientGroup.subsingleton_quotient_top`), so the same argument as in
  `NK.NUV2.LC.RouteB.loc_ofLevel_eq_zero_of_le_fixingSubgroup`
  (`onePlaceClassesKummer.lean`) gives `Subsingleton (H2 p (LocalLevelGroup ⊤ A.1 L₀))`;
* by `hγ`, `γ b` is the class of `cls'` at the level `L₀`; the map
  `resUnits_h (le : ⊤ ⊓ D_A ≤ ⊤) : H2Units ⊤ → H2Units (⊤ ⊓ D_A)` defined by `LevelSystem.lift`
  from the level maps `H2.map (levelInclHom · L)` (`BrauerHasse.levelInclHom`, compatibility from
  its naturality) sends it to `ofLevel^{⊤⊓D_A}_{L₀}(H2.map ... cls')`, which is `0` because the
  target level group is trivial;
* the Kummer square `kummerColim p (⊤ ⊓ D_A) (resMu_h (le) x) = resUnits_h (le) (kummerColim p ⊤ x)`
  (`resMu_h` defined the same way on `MuColim`, from `kummerLevel_naturality`) together with `hY`
  gives `kummerColim p (⊤ ⊓ D_A) (resMu_h (Y b)) = 0`, hence `resMu_h (Y b) = 0` by
  `NK.HassePrinciple.kummerColim_injective`;
* the comparison square `H2Profinite.loc p ⊤ (muToH2 p hζ y) A = muToH2 (resMu_h (le) y)` (by
  `H2Profinite.lift_unique`, level-wise from `levelCompare_muLevelMap` and the naturality of the
  level comparison in the group variable, cf. `NK.IndecomposedDeep.H2congr_map`) finishes.

Since `NK.LocDecomposition`/`NK.LocalDecomposition` already provide
`H2Profinite.res` with the computation rule `res_ofLevel`, the Z/p-side restriction is available;
only the `MuColim`-side restriction and the two squares are new.  Note that `LocalLevelGroup ⊤ A L`
is `LevelGroup (⊤ ⊓ D_A) L`, so the restriction can also be phrased with `LevelGroup`. -/
theorem loc_eq_zero_of_localLevelGroup_subsingleton_h (p : ℕ) (hp : p.Prime) [NeZero p]
    {F : Type} [Field F] [NumberField F] (F' : Type) [Field F'] [Algebra F F']
    [IsSepClosure F F'] (ζ : F) (hζ : IsPrimitiveRoot ζ p)
    (E : IntermediateField F F') [FiniteDimensional F E] [IsGalois F E] [NumberField ↥E]
    (hdeg : Module.finrank F E = p)
    (g : ↥E ≃ₐ[F] ↥E) (hg : ∀ σ : ↥E ≃ₐ[F] ↥E, σ ∈ Subgroup.zpowers g)
    (γ : Fˣ → NK.HassePrinciple.H2Units (K := F) (K' := F') (⊤ : Subgroup Gal(F'/F)))
    (Y : Fˣ → NK.HassePrinciple.MuColim (K := F) (K' := F') p (⊤ : Subgroup Gal(F'/F)))
    (hγ : ∀ b : Fˣ, NK.HassePrinciple.H2Units.ofLevel (K := F) (K' := F')
          (⊤ : Subgroup Gal(F'/F)) (⟨E⟩ : FiniteGaloisIntermediateField F F')
          ((NK.NUV2.LC.unitsTransport (K := F) (K' := F')
            (⟨E⟩ : FiniteGaloisIntermediateField F F')).symm
            (NK.CFTLib.IdeleHasse.Descent.cycClassOf (K := F) (F := ↥E) g hg b)) = γ b)
    (hY : ∀ b : Fˣ, NK.HassePrinciple.kummerColim (K := F) (K' := F') p
          (⊤ : Subgroup Gal(F'/F)) (Y b) = γ b)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))
    (A : NK.BrauerHasse.OverFinitePrime F F')
    (hA : A.1.comap (algebraMap F F') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime F v)
    (b : Fˣ)
    (htriv : Subsingleton (NK.BrauerHasse.LocalLevelGroup (⊤ : Subgroup Gal(F'/F)) A.1
      (⟨E⟩ : FiniteGaloisIntermediateField F F'))) :
    NK.BrauerHasse.H2Profinite.loc p ⊤
      (NK.NUV2.ABHN.muToH2 (K := F) (K' := F') p hζ (Y b)) A = 0 := by
  let L₀ : FiniteGaloisIntermediateField F F' := ⟨E⟩
  let V : Subgroup Gal(F'/F) := ⊤ ⊓ NK.BrauerHasse.stabSubgroup A.1
  let cls : NK.HassePrinciple.UnitsLevelH2 (K := F) (K' := F') ⊤ L₀ :=
    (NK.NUV2.LC.unitsTransport (K := F) (K' := F') L₀).symm
      (NK.CFTLib.IdeleHasse.Descent.cycClassOf (K := F) (F := ↥E) g hg b)
  have hγ' : NK.HassePrinciple.H2Units.ofLevel (K := F) (K' := F') ⊤ L₀ cls = γ b := hγ b
  -- The restriction of the level-`L₀` units class dies, the level group being trivial.
  have hcls : (unitsResLevel_h (K := F) (K' := F')
      (inf_le_left : V ≤ (⊤ : Subgroup Gal(F'/F))) L₀).hom cls = 0 := by
    haveI : Subsingleton (LevelGroup V L₀) := htriv
    haveI : Subsingleton (NK.HassePrinciple.UnitsLevelH2 (K := F) (K' := F') V L₀) :=
      ModuleCat.isZero_iff_subsingleton.mp
        (show CategoryTheory.Limits.IsZero
            (NK.HassePrinciple.UnitsLevelH2 (K := F) (K' := F') V L₀) from
          isZero_groupCohomology_succ_of_subsingleton
            (NK.HassePrinciple.unitsLevelRep (K := F) (K' := F') V L₀) 1)
    exact Subsingleton.elim _ _
  have key : ∀ (x : NK.HassePrinciple.MuColim (K := F) (K' := F') p ⊤),
      NK.HassePrinciple.kummerColim (K := F) (K' := F') p ⊤ x = γ b →
      NK.LocalDecomposition.H2Profinite.res p (inf_le_left : V ≤ (⊤ : Subgroup Gal(F'/F)))
        (NK.NUV2.ABHN.muToH2 (K := F) (K' := F') p hζ x) = 0 := by
    intro x hx
    obtain ⟨L, a, rfl⟩ := MuColim_ofLevel_surjective_h (K := F) (K' := F') p ⊤ x
    have hk : NK.HassePrinciple.kummerColim (K := F) (K' := F') p V
        (resMu_h (K := F) (K' := F') p (inf_le_left : V ≤ (⊤ : Subgroup Gal(F'/F)))
          (NK.HassePrinciple.MuColim.ofLevel p ⊤ L a)) = 0 := by
      rw [kummerColim_resMu_h (K := F) (K' := F') p (inf_le_left : V ≤ (⊤ : Subgroup Gal(F'/F)))
          (NK.HassePrinciple.MuColim.ofLevel p ⊤ L a),
        hx, ← hγ',
        resUnits_ofLevel_h (K := F) (K' := F')
          (inf_le_left : V ≤ (⊤ : Subgroup Gal(F'/F))) L₀ cls, hcls]
      exact H2Units_ofLevel_zero'_h (K := F) (K' := F') V L₀
    have hzero : resMu_h (K := F) (K' := F') p (inf_le_left : V ≤ (⊤ : Subgroup Gal(F'/F)))
        (NK.HassePrinciple.MuColim.ofLevel p ⊤ L a) = 0 :=
      NK.HassePrinciple.kummerColim_injective (K := F) (K' := F') p hp V
        (hk.trans (kummerColim_zero (K := F) (K' := F') p V).symm)
    rw [← muToH2Sub_top_h (K := F) (K' := F') p hζ,
      res_muToH2Sub_h (K := F) (K' := F') p hζ (inf_le_left : V ≤ (⊤ : Subgroup Gal(F'/F)))
        (NK.HassePrinciple.MuColim.ofLevel p ⊤ L a), hzero]
    exact muToH2Sub_zero_h (K := F) (K' := F') p hζ V
  exact (NK.LocalDecomposition.loc_eq_zero_iff_res_eq_zero p (⊤ : Subgroup Gal(F'/F)) A
    (NK.NUV2.ABHN.muToH2 (K := F) (K' := F') p hζ (Y b))).mpr (key (Y b) (hY b))

end NK.NUV2.LC.RouteB
