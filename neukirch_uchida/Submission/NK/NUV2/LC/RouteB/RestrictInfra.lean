import Mathlib
import Submission.NK.NUV2.LC.RouteB.DictionaryDeps2


set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open CategoryTheory Representation

namespace NK.NUV2.LC.RouteB

namespace Restrict


open NK.BrauerHasse


section Generic

variable {k : Type} [CommRing k] {G₀ G₁ : Type} [Group G₀] [Group G₁]

/-- **Composition of `groupCohomology.map` with the identity group homomorphism on the right**: for
`φ : Rep.res f A ⟶ B` and `ψ : B ⟶ C` over the target group of `f`, the composite of the induced
maps is induced by `φ ≫ ψ` (the group homomorphism of the composite being `f.comp (id) = f`). -/
lemma map_comp_id_right (f : G₁ →* G₀) {A : Rep k G₀} {B : Rep k G₁} {C : Rep k G₁}
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
lemma map_id_comp_left {A : Rep k G₀} {B : Rep k G₀} (f : G₁ →* G₀) {C : Rep k G₁}
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
lemma levelGroupRestrictHom_levelInclHom {U V : Subgroup Gal(K'/K)} (h : V ≤ U)
    (L : FiniteGaloisIntermediateField K K') (q : LevelGroup V L) :
    NK.HassePrinciple.levelGroupRestrictHom U L (levelInclHom h L q) =
      NK.HassePrinciple.levelGroupRestrictHom V L q := by
  induction q using QuotientGroup.induction_on with
  | H v => rfl

/-- The inclusion of level groups commutes with the inflation maps. -/
lemma levelInclHom_comp_levelQuotHom {U V : Subgroup Gal(K'/K)} (hV : V ≤ U)
    {L M : FiniteGaloisIntermediateField K K'} (h : L ≤ M) :
    (levelInclHom hV L).comp (levelQuotHom (U := V) h) =
      (levelQuotHom (U := U) h).comp (levelInclHom hV M) := by
  apply MonoidHom.ext
  intro x
  induction x using QuotientGroup.induction_on with
  | H y => rfl

/-! ## §2. The coefficient morphisms of the restriction -/

/-- **The coefficient morphism of the restriction on `μ_p`**: the identity of `μ_p(L)`. -/
noncomputable def muResCoeff (p : ℕ) {U V : Subgroup Gal(K'/K)} (h : V ≤ U)
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
      rw [levelGroupRestrictHom_levelInclHom (K := K) (K' := K') h L q]
      rfl))

/-- The coefficient morphism of the restriction acts by the identity on `μ_p(L)`. -/
lemma muResCoeff_apply (p : ℕ) {U V : Subgroup Gal(K'/K)} (h : V ≤ U)
    (L : FiniteGaloisIntermediateField K K')
    (x : (Rep.res (levelInclHom h L)
      (NK.HassePrinciple.muLevelRep (K := K) (K' := K') p U L)).V) :
    (muResCoeff (K := K) (K' := K') p h L).hom.toLinearMap x = x := rfl

/-- **The coefficient morphism of the restriction on the units**: the identity of `Lˣ`. -/
noncomputable def unitsResCoeff {U V : Subgroup Gal(K'/K)} (h : V ≤ U)
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
      rw [levelGroupRestrictHom_levelInclHom (K := K) (K' := K') h L q]
      rfl))

/-- The coefficient morphism of the restriction on the units acts by the identity. -/
lemma unitsResCoeff_apply {U V : Subgroup Gal(K'/K)} (h : V ≤ U)
    (L : FiniteGaloisIntermediateField K K')
    (x : (Rep.res (levelInclHom h L)
      (NK.HassePrinciple.unitsLevelRep (K := K) (K' := K') U L)).V) :
    (unitsResCoeff (K := K) (K' := K') h L).hom.toLinearMap x = x := rfl

/-! ## §3. The restriction on the level cohomology -/

/-- **The restriction on the level cohomology with `μ_p`-coefficients.** -/
noncomputable def muResLevel (p : ℕ) {U V : Subgroup Gal(K'/K)} (h : V ≤ U)
    (L : FiniteGaloisIntermediateField K K') :
    NK.HassePrinciple.MuLevelH2 (K := K) (K' := K') p U L ⟶
      NK.HassePrinciple.MuLevelH2 (K := K) (K' := K') p V L :=
  groupCohomology.map (levelInclHom h L) (muResCoeff (K := K) (K' := K') p h L) 2

/-- **The restriction on the level cohomology with unit coefficients.** -/
noncomputable def unitsResLevel {U V : Subgroup Gal(K'/K)} (h : V ≤ U)
    (L : FiniteGaloisIntermediateField K K') :
    NK.HassePrinciple.UnitsLevelH2 (K := K) (K' := K') U L ⟶
      NK.HassePrinciple.UnitsLevelH2 (K := K) (K' := K') V L :=
  groupCohomology.map (levelInclHom h L) (unitsResCoeff (K := K) (K' := K') h L) 2

/-- **The restriction commutes with the Kummer inclusion of the coefficients.** -/
theorem muResCoeff_muToUnits (p : ℕ) {U V : Subgroup Gal(K'/K)} (h : V ≤ U)
    (L : FiniteGaloisIntermediateField K K') :
    (muResCoeff (K := K) (K' := K') p h L ≫ NK.HassePrinciple.muToUnits (K := K) (K' := K') p V L) =
      (Rep.resMap (levelInclHom h L) (NK.HassePrinciple.muToUnits (K := K) (K' := K') p U L) ≫
        unitsResCoeff (K := K) (K' := K') h L) := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  simp only [Rep.hom_comp, Representation.IntertwiningMap.comp_toLinearMap, LinearMap.comp_apply,
    Rep.resMap_hom_toLinearMap, NK.HassePrinciple.muToUnits]
  rw [show (Rep.Hom.hom (muResCoeff (K := K) (K' := K') p h L)).toLinearMap x = x from rfl,
    show (Rep.Hom.hom (unitsResCoeff (K := K) (K' := K') h L)).toLinearMap
      ((Rep.Hom.hom (NK.HassePrinciple.kummerIncl p K ↥L)).toLinearMap x) =
      (Rep.Hom.hom (NK.HassePrinciple.kummerIncl p K ↥L)).toLinearMap x from rfl]

/-- **The restriction commutes with inflation** (`μ_p`-coefficients). -/
theorem muResLevel_levelMap (p : ℕ) {U V : Subgroup Gal(K'/K)} (h : V ≤ U)
    {L M : FiniteGaloisIntermediateField K K'} (hLM : L ≤ M) :
    muResLevel (K := K) (K' := K') p h L ≫ NK.HassePrinciple.muLevelMap (K := K) (K' := K') p V hLM =
      NK.HassePrinciple.muLevelMap (K := K) (K' := K') p U hLM ≫
        muResLevel (K := K) (K' := K') p h M := by
  have hcomp : (levelInclHom h L).comp (levelQuotHom (U := V) hLM) =
      (levelQuotHom (U := U) hLM).comp (levelInclHom h M) :=
    levelInclHom_comp_levelQuotHom h hLM
  have hcoe : ((Rep.resMap (levelQuotHom (U := V) hLM)
        (muResCoeff (K := K) (K' := K') p h L)) ≫
      NK.HassePrinciple.muLevelMapCoeff (K := K) (K' := K') p V hLM).hom.toLinearMap =
      ((Rep.resMap (levelInclHom h M)
        (NK.HassePrinciple.muLevelMapCoeff (K := K) (K' := K') p U hLM)) ≫
        muResCoeff (K := K) (K' := K') p h M).hom.toLinearMap := by
    apply LinearMap.ext
    intro x
    rfl
  have hmc := groupCohomology.map_comp (f := levelInclHom h L)
    (g := NK.BrauerHasse.levelQuotHom (U := V) hLM)
    (A := NK.HassePrinciple.muLevelRep (K := K) (K' := K') p U L)
    (B := NK.HassePrinciple.muLevelRep (K := K) (K' := K') p V L)
    (C := NK.HassePrinciple.muLevelRep (K := K) (K' := K') p V M)
    (φ := muResCoeff (K := K) (K' := K') p h L)
    (ψ := NK.HassePrinciple.muLevelMapCoeff (K := K) (K' := K') p V hLM) (n := 2)
  have hmc' := groupCohomology.map_comp (f := NK.BrauerHasse.levelQuotHom (U := U) hLM)
    (g := levelInclHom h M)
    (A := NK.HassePrinciple.muLevelRep (K := K) (K' := K') p U L)
    (B := NK.HassePrinciple.muLevelRep (K := K) (K' := K') p U M)
    (C := NK.HassePrinciple.muLevelRep (K := K) (K' := K') p V M)
    (φ := NK.HassePrinciple.muLevelMapCoeff (K := K) (K' := K') p U hLM)
    (ψ := muResCoeff (K := K) (K' := K') p h M) (n := 2)
  rw [muResLevel, NK.HassePrinciple.muLevelMap, muResLevel, NK.HassePrinciple.muLevelMap,
    ← hmc, ← hmc']
  exact groupCohomology.map_congr hcomp hcoe 2

/-- Elementwise form of `muResLevel_levelMap`. -/
theorem muResLevel_levelMap_apply (p : ℕ) {U V : Subgroup Gal(K'/K)} (h : V ≤ U)
    {L M : FiniteGaloisIntermediateField K K'} (hLM : L ≤ M)
    (a : NK.HassePrinciple.MuLevelH2 (K := K) (K' := K') p U L) :
    (muResLevel (K := K) (K' := K') p h M) ((NK.HassePrinciple.muLevelMap (K := K) (K' := K') p U hLM) a) =
      (NK.HassePrinciple.muLevelMap (K := K) (K' := K') p V hLM)
        ((muResLevel (K := K) (K' := K') p h L) a) := by
  have h1 := congrArg (fun (k : NK.HassePrinciple.MuLevelH2 (K := K) (K' := K') p U L ⟶
      NK.HassePrinciple.MuLevelH2 (K := K) (K' := K') p V M) => k.hom a)
    (muResLevel_levelMap (K := K) (K' := K') p h hLM)
  simpa using h1.symm

/-- **The restriction commutes with inflation** (unit coefficients). -/
theorem unitsResLevel_levelMap {U V : Subgroup Gal(K'/K)} (h : V ≤ U)
    {L M : FiniteGaloisIntermediateField K K'} (hLM : L ≤ M) :
    unitsResLevel (K := K) (K' := K') h L ≫ NK.HassePrinciple.unitsLevelMap (K := K) (K' := K') V hLM =
      NK.HassePrinciple.unitsLevelMap (K := K) (K' := K') U hLM ≫
        unitsResLevel (K := K) (K' := K') h M := by
  have hcomp : (levelInclHom h L).comp (levelQuotHom (U := V) hLM) =
      (levelQuotHom (U := U) hLM).comp (levelInclHom h M) :=
    levelInclHom_comp_levelQuotHom h hLM
  have hcoe : ((Rep.resMap (levelQuotHom (U := V) hLM)
        (unitsResCoeff (K := K) (K' := K') h L)) ≫
      NK.HassePrinciple.unitsLevelMapCoeff (K := K) (K' := K') V hLM).hom.toLinearMap =
      ((Rep.resMap (levelInclHom h M)
        (NK.HassePrinciple.unitsLevelMapCoeff (K := K) (K' := K') U hLM)) ≫
        unitsResCoeff (K := K) (K' := K') h M).hom.toLinearMap := by
    apply LinearMap.ext
    intro x
    rfl
  have hmc := groupCohomology.map_comp (f := levelInclHom h L)
    (g := NK.BrauerHasse.levelQuotHom (U := V) hLM)
    (A := NK.HassePrinciple.unitsLevelRep (K := K) (K' := K') U L)
    (B := NK.HassePrinciple.unitsLevelRep (K := K) (K' := K') V L)
    (C := NK.HassePrinciple.unitsLevelRep (K := K) (K' := K') V M)
    (φ := unitsResCoeff (K := K) (K' := K') h L)
    (ψ := NK.HassePrinciple.unitsLevelMapCoeff (K := K) (K' := K') V hLM) (n := 2)
  have hmc' := groupCohomology.map_comp (f := NK.BrauerHasse.levelQuotHom (U := U) hLM)
    (g := levelInclHom h M)
    (A := NK.HassePrinciple.unitsLevelRep (K := K) (K' := K') U L)
    (B := NK.HassePrinciple.unitsLevelRep (K := K) (K' := K') U M)
    (C := NK.HassePrinciple.unitsLevelRep (K := K) (K' := K') V M)
    (φ := NK.HassePrinciple.unitsLevelMapCoeff (K := K) (K' := K') U hLM)
    (ψ := unitsResCoeff (K := K) (K' := K') h M) (n := 2)
  rw [unitsResLevel, NK.HassePrinciple.unitsLevelMap, unitsResLevel,
    NK.HassePrinciple.unitsLevelMap, ← hmc, ← hmc']
  exact groupCohomology.map_congr hcomp hcoe 2

/-- Elementwise form of `unitsResLevel_levelMap`. -/
theorem unitsResLevel_levelMap_apply {U V : Subgroup Gal(K'/K)} (h : V ≤ U)
    {L M : FiniteGaloisIntermediateField K K'} (hLM : L ≤ M)
    (a : NK.HassePrinciple.UnitsLevelH2 (K := K) (K' := K') U L) :
    (unitsResLevel (K := K) (K' := K') h M) ((NK.HassePrinciple.unitsLevelMap (K := K) (K' := K') U hLM) a) =
      (NK.HassePrinciple.unitsLevelMap (K := K) (K' := K') V hLM)
        ((unitsResLevel (K := K) (K' := K') h L) a) := by
  have h1 := congrArg (fun (k : NK.HassePrinciple.UnitsLevelH2 (K := K) (K' := K') U L ⟶
      NK.HassePrinciple.UnitsLevelH2 (K := K) (K' := K') V M) => k.hom a)
    (unitsResLevel_levelMap (K := K) (K' := K') h hLM)
  simpa using h1.symm

/-! ## §4. The Kummer square at the level -/

/-- **Naturality of the Kummer morphism for the restriction.** -/
theorem kummerLevel_muResLevel (p : ℕ) {U V : Subgroup Gal(K'/K)} (h : V ≤ U)
    (L : FiniteGaloisIntermediateField K K') (a : NK.HassePrinciple.MuLevelH2 (K := K) (K' := K') p U L) :
    (NK.HassePrinciple.kummerLevel p V L).hom ((muResLevel (K := K) (K' := K') p h L).hom a) =
      (unitsResLevel (K := K) (K' := K') h L).hom
        ((NK.HassePrinciple.kummerLevel p U L).hom a) := by
  have hL : (NK.HassePrinciple.kummerLevel p V L).hom ((muResLevel (K := K) (K' := K') p h L).hom a)
      = ((muResLevel (K := K) (K' := K') p h L ≫
          NK.HassePrinciple.kummerLevel p V L)).hom a := rfl
  have hR : (unitsResLevel (K := K) (K' := K') h L).hom
        ((NK.HassePrinciple.kummerLevel p U L).hom a)
      = ((NK.HassePrinciple.kummerLevel p U L ≫
          unitsResLevel (K := K) (K' := K') h L)).hom a := rfl
  rw [hL, hR]
  have e1 : (muResLevel (K := K) (K' := K') p h L ≫ NK.HassePrinciple.kummerLevel p V L)
      = groupCohomology.map (levelInclHom h L)
          (muResCoeff (K := K) (K' := K') p h L ≫
            NK.HassePrinciple.muToUnits (K := K) (K' := K') p V L) 2 := by
    rw [muResLevel, NK.HassePrinciple.kummerLevel]
    exact map_comp_id_right (levelInclHom h L) (muResCoeff (K := K) (K' := K') p h L)
      (NK.HassePrinciple.muToUnits (K := K) (K' := K') p V L)
  have e2 : (NK.HassePrinciple.kummerLevel p U L ≫ unitsResLevel (K := K) (K' := K') h L)
      = groupCohomology.map (levelInclHom h L)
          (Rep.resMap (levelInclHom h L) (NK.HassePrinciple.muToUnits (K := K) (K' := K') p U L) ≫
            unitsResCoeff (K := K) (K' := K') h L) 2 := by
    rw [unitsResLevel, NK.HassePrinciple.kummerLevel]
    exact map_id_comp_left (levelInclHom h L) (NK.HassePrinciple.muToUnits (K := K) (K' := K') p U L)
      (unitsResCoeff (K := K) (K' := K') h L)
  rw [e1, e2, muResCoeff_muToUnits]

/-! ## §5. The restriction on the colimits -/

/-- **The restriction map on the `μ_p`-colimit.** -/
noncomputable def resMu (p : ℕ) {U V : Subgroup Gal(K'/K)} (h : V ≤ U) :
    NK.HassePrinciple.MuColim (K := K) (K' := K') p U →
      NK.HassePrinciple.MuColim (K := K) (K' := K') p V :=
  (NK.HassePrinciple.muLevelSystem (K := K) (K' := K') p U).lift
    (fun L a => NK.HassePrinciple.MuColim.ofLevel p V L
      (muResLevel (K := K) (K' := K') p h L a))
    (by
      intro L L' hLL' a
      show NK.HassePrinciple.MuColim.ofLevel p V L'
          (muResLevel (K := K) (K' := K') p h L'
            ((NK.HassePrinciple.muLevelMap (K := K) (K' := K') p U
              ((FiniteGaloisIntermediateField.le_iff L L').mp hLL')) a)) =
        NK.HassePrinciple.MuColim.ofLevel p V L
          (muResLevel (K := K) (K' := K') p h L a)
      rw [muResLevel_levelMap_apply (K := K) (K' := K') p h
        ((FiniteGaloisIntermediateField.le_iff L L').mp hLL') a]
      exact NK.BrauerTwist.LevelSystem.ofLevel_map
        (S := NK.HassePrinciple.muLevelSystem (K := K) (K' := K') p V) hLL'
        ((muResLevel (K := K) (K' := K') p h L) a))

/-- The computation rule for the restriction on the `μ_p`-colimit. -/
@[simp]
lemma resMu_ofLevel (p : ℕ) {U V : Subgroup Gal(K'/K)} (h : V ≤ U)
    (L : FiniteGaloisIntermediateField K K')
    (a : NK.HassePrinciple.MuLevelH2 (K := K) (K' := K') p U L) :
    resMu (K := K) (K' := K') p h (NK.HassePrinciple.MuColim.ofLevel p U L a) =
      NK.HassePrinciple.MuColim.ofLevel p V L (muResLevel (K := K) (K' := K') p h L a) := rfl

/-- **The restriction map on the units colimit.** -/
noncomputable def resUnits {U V : Subgroup Gal(K'/K)} (h : V ≤ U) :
    NK.HassePrinciple.H2Units (K := K) (K' := K') U →
      NK.HassePrinciple.H2Units (K := K) (K' := K') V :=
  (NK.HassePrinciple.unitsLevelSystem (K := K) (K' := K') U).lift
    (fun L a => NK.HassePrinciple.H2Units.ofLevel V L
      (unitsResLevel (K := K) (K' := K') h L a))
    (by
      intro L L' hLL' a
      show NK.HassePrinciple.H2Units.ofLevel V L'
          (unitsResLevel (K := K) (K' := K') h L'
            ((NK.HassePrinciple.unitsLevelMap (K := K) (K' := K') U
              ((FiniteGaloisIntermediateField.le_iff L L').mp hLL')) a)) =
        NK.HassePrinciple.H2Units.ofLevel V L
          (unitsResLevel (K := K) (K' := K') h L a)
      rw [unitsResLevel_levelMap_apply (K := K) (K' := K') h
        ((FiniteGaloisIntermediateField.le_iff L L').mp hLL') a]
      exact NK.BrauerTwist.LevelSystem.ofLevel_map
        (S := NK.HassePrinciple.unitsLevelSystem (K := K) (K' := K') V) hLL'
        ((unitsResLevel (K := K) (K' := K') h L) a))

/-- The computation rule for the restriction on the units colimit. -/
@[simp]
lemma resUnits_ofLevel {U V : Subgroup Gal(K'/K)} (h : V ≤ U)
    (L : FiniteGaloisIntermediateField K K')
    (a : NK.HassePrinciple.UnitsLevelH2 (K := K) (K' := K') U L) :
    resUnits (K := K) (K' := K') h (NK.HassePrinciple.H2Units.ofLevel U L a) =
      NK.HassePrinciple.H2Units.ofLevel V L (unitsResLevel (K := K) (K' := K') h L a) := rfl

/-- The zero of the units colimit is the class of the zero of any level. -/
lemma H2Units_ofLevel_zero' (V : Subgroup Gal(K'/K))
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
lemma MuColim_ofLevel_zero (p : ℕ) (V : Subgroup Gal(K'/K)) :
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
lemma MuColim_ofLevel_surjective (p : ℕ) (V : Subgroup Gal(K'/K))
    (x : NK.HassePrinciple.MuColim (K := K) (K' := K') p V) :
    ∃ (L : FiniteGaloisIntermediateField K K')
      (a : NK.HassePrinciple.MuLevelH2 (K := K) (K' := K') p V L),
      NK.HassePrinciple.MuColim.ofLevel p V L a = x :=
  (NK.HassePrinciple.muLevelSystem (K := K) (K' := K') p V).ofLevel_surjective x

/-- **The Kummer square at the level of the colimits**: the restriction of the Kummer image is the
Kummer image of the restriction. -/
theorem kummerColim_resMu (p : ℕ) {U V : Subgroup Gal(K'/K)} (h : V ≤ U)
    (x : NK.HassePrinciple.MuColim (K := K) (K' := K') p U) :
    NK.HassePrinciple.kummerColim (K := K) (K' := K') p V
        (resMu (K := K) (K' := K') p h x) =
      resUnits (K := K) (K' := K') h
        (NK.HassePrinciple.kummerColim (K := K) (K' := K') p U x) := by
  obtain ⟨L, a, rfl⟩ := MuColim_ofLevel_surjective (K := K) (K' := K') p U x
  rw [resMu_ofLevel (K := K) (K' := K') p h L a, NK.HassePrinciple.kummerColim_ofLevel,
    NK.HassePrinciple.kummerColim_ofLevel,
    resUnits_ofLevel (K := K) (K' := K') h L
      ((NK.HassePrinciple.kummerLevel (K := K) (K' := K') p U L).hom a),
    kummerLevel_muResLevel]

/-! ## §6. The comparison with the trivial coefficients -/

/-- **Naturality of the level comparison for the restriction.** -/
theorem levelCompare_muResLevel (p : ℕ) [NeZero p] {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    {U V : Subgroup Gal(K'/K)} (h : V ≤ U)
    (L : FiniteGaloisIntermediateField K K')
    (a : NK.HassePrinciple.MuLevelH2 (K := K) (K' := K') p U L) :
    NK.NUV2.ABHN.levelCompareRoot p hζ V L (muResLevel (K := K) (K' := K') p h L a) =
      H2.map (levelInclHom h L) (NK.NUV2.ABHN.levelCompareRoot p hζ U L a) := by
  show NK.IndecomposedDeep.H2congr (A := NK.HassePrinciple.muLevelRep (K := K) (K' := K') p V L)
        (B := NK.NUV2.ABHN.trivLevelRep (K := K) (K' := K') p V L)
        (NK.NUV2.ABHN.muAddEquiv p ζ hζ L)
        (NK.NUV2.ABHN.muAddEquiv_equivariance p hζ V L)
        (groupCohomology.map (levelInclHom h L) (muResCoeff (K := K) (K' := K') p h L) 2 a) =
      groupCohomology.map (levelInclHom h L)
        (NK.BrauerHasse.trivHom (levelInclHom h L)) 2
        (NK.IndecomposedDeep.H2congr
          (A := NK.HassePrinciple.muLevelRep (K := K) (K' := K') p U L)
          (B := NK.NUV2.ABHN.trivLevelRep (K := K) (K' := K') p U L)
          (NK.NUV2.ABHN.muAddEquiv p ζ hζ L)
          (NK.NUV2.ABHN.muAddEquiv_equivariance p hζ U L) a)
  exact NK.IndecomposedDeep.H2congr_map (levelInclHom h L)
    (muResCoeff (K := K) (K' := K') p h L)
    (NK.BrauerHasse.trivHom (levelInclHom h L))
    (NK.NUV2.ABHN.muAddEquiv p ζ hζ L) (NK.NUV2.ABHN.muAddEquiv p ζ hζ L)
    (NK.NUV2.ABHN.muAddEquiv_equivariance p hζ U L)
    (NK.NUV2.ABHN.muAddEquiv_equivariance p hζ V L)
    (fun x => rfl) a

/-- The level comparison sends zero to zero. -/
lemma levelCompare_zero (p : ℕ) [NeZero p] {ζ : K} (hζ : IsPrimitiveRoot ζ p)
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
noncomputable def muToH2Sub (p : ℕ) [NeZero p] {ζ : K} (hζ : IsPrimitiveRoot ζ p)
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

/-- The computation rule for `muToH2Sub`. -/
@[simp]
lemma muToH2Sub_ofLevel (p : ℕ) [NeZero p] {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (V : Subgroup Gal(K'/K)) (L : FiniteGaloisIntermediateField K K')
    (a : NK.HassePrinciple.MuLevelH2 (K := K) (K' := K') p V L) :
    muToH2Sub (K := K) (K' := K') p hζ V (NK.HassePrinciple.MuColim.ofLevel p V L a) =
      H2Profinite.ofLevel L (NK.NUV2.ABHN.levelCompareRoot p hζ V L a) := rfl

/-- `muToH2Sub` sends zero to zero. -/
lemma muToH2Sub_zero (p : ℕ) [NeZero p] {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (V : Subgroup Gal(K'/K)) :
    muToH2Sub (K := K) (K' := K') p hζ V
      (0 : NK.HassePrinciple.MuColim (K := K) (K' := K') p V) = 0 := by
  rw [show (0 : NK.HassePrinciple.MuColim (K := K) (K' := K') p V) =
      NK.HassePrinciple.MuColim.ofLevel p V (⊥ : FiniteGaloisIntermediateField K K') 0
    from (MuColim_ofLevel_zero (K := K) (K' := K') p V).symm]
  rw [muToH2Sub_ofLevel (K := K) (K' := K') p hζ V ⊥ 0, levelCompare_zero,
    NK.BrauerHasse.ofLevel_zero]

/-- The general-subgroup comparison restricts to the one at `⊤`. -/
lemma muToH2Sub_top (p : ℕ) [NeZero p] {ζ : K} (hζ : IsPrimitiveRoot ζ p) :
    muToH2Sub (K := K) (K' := K') p hζ ⊤ = NK.NUV2.ABHN.muToH2 p hζ := rfl

end Restrict

section NumberFieldBase

variable {K K' : Type} [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-- **The comparison square for the restriction.** -/
theorem res_muToH2Sub (p : ℕ) [NeZero p] {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    {U V : Subgroup Gal(K'/K)} (h : V ≤ U)
    (x : NK.HassePrinciple.MuColim (K := K) (K' := K') p U) :
    NK.LocalDecomposition.H2Profinite.res p h (muToH2Sub (K := K) (K' := K') p hζ U x) =
      muToH2Sub (K := K) (K' := K') p hζ V (resMu (K := K) (K' := K') p h x) := by
  obtain ⟨L, a, rfl⟩ := MuColim_ofLevel_surjective (K := K) (K' := K') p U x
  rw [muToH2Sub_ofLevel (K := K) (K' := K') p hζ U L a,
    NK.LocalDecomposition.H2Profinite.res_ofLevel,
    resMu_ofLevel (K := K) (K' := K') p h L a,
    muToH2Sub_ofLevel (K := K) (K' := K') p hζ V L (muResLevel (K := K) (K' := K') p h L a),
    levelCompare_muResLevel]

end NumberFieldBase

end Restrict

end NK.NUV2.LC.RouteB
