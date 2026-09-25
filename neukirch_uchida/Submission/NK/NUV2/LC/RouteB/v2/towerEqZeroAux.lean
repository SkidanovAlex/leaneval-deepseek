import Mathlib
import Submission.NK.NUV2.LC.LocalLevelSystem
import Submission.NK.HassePrinciple.LocalUnits
import Submission.NK.NUV2.LC.localLevelMap
import Submission.NK.GlobalCFT.Inclusion.globalCFT_liesOver_unique
import Submission.NK.HassePrinciple.liesOver_smul_of_restrict
import Submission.NK.HassePrinciple.localRingEquiv_localAlgebraMapUnits_of_restrict
import Submission.NK.HassePrinciple.repIso_quotientToInvariants_fixedField

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped NumberField NumberField.LiesOver
open CategoryTheory

namespace NK.NUV2.LC.RouteB.v2

variable {F L M : Type} [Field F] [NumberField F] [Field L] [NumberField L]
  [Field M] [NumberField M]
  [Algebra F L] [Algebra F M] [Algebra L M] [IsScalarTower F L M]
  [FiniteDimensional F L] [IsGalois F L] [FiniteDimensional F M] [IsGalois F M]

/-- Restricting an automorphism of `M` fixing `w'` gives an automorphism of `L` fixing `w`. -/
theorem restrictNormal_smul_eq_of_liesOver {w : NK.GlobalCFT.Place L} {w' : NK.GlobalCFT.Place M}
    (h : NK.GlobalCFT.Place.LiesOver w' w) (σ : Gal(M/F))
    (hσ : σ • w' = w') :
    ((AlgEquiv.restrictNormalHom (K₁ := M) (E := L)) σ) • w = w := by
  have h1 := NK.HassePrinciple.liesOver_smul_of_restrict (K := F) (F := L) (L := M) σ
    (AlgEquiv.restrictNormalHom (K₁ := M) (E := L) σ)
    (fun y => AlgEquiv.restrictNormal_commutes (E := L) σ y) h
  rw [hσ] at h1
  exact NK.GlobalCFT.Inclusion.globalCFT_liesOver_unique h1 h

/-- The corestriction of the restriction `Gal(M/F) →* Gal(L/F)` to the stabilisers. -/
noncomputable def localStabilizerMapTower {w : NK.GlobalCFT.Place L}
    {w' : NK.GlobalCFT.Place M} (h : NK.GlobalCFT.Place.LiesOver w' w) :
    MulAction.stabilizer Gal(M/F) w' →* MulAction.stabilizer Gal(L/F) w where
  toFun σ :=
    ⟨(AlgEquiv.restrictNormalHom (K₁ := M) (E := L)) σ.1, by
      rw [MulAction.mem_stabilizer_iff]
      exact restrictNormal_smul_eq_of_liesOver h σ.1 (MulAction.mem_stabilizer_iff.mp σ.2)⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' σ τ := Subtype.ext (map_mul _ σ.1 τ.1)

@[simp] theorem localStabilizerMapTower_coe {w : NK.GlobalCFT.Place L}
    {w' : NK.GlobalCFT.Place M} (h : NK.GlobalCFT.Place.LiesOver w' w)
    (σ : MulAction.stabilizer Gal(M/F) w') :
    (↑(localStabilizerMapTower (F := F) (L := L) (M := M) h σ) : Gal(L/F)) =
      (AlgEquiv.restrictNormalHom (K₁ := M) (E := L)) σ.1 := rfl

theorem localStabilizerMapTower_comp_subtype {w : NK.GlobalCFT.Place L}
    {w' : NK.GlobalCFT.Place M} (h : NK.GlobalCFT.Place.LiesOver w' w) :
    (MulAction.stabilizer Gal(L/F) w).subtype.comp
        (localStabilizerMapTower (F := F) (L := L) (M := M) h) =
      (AlgEquiv.restrictNormalHom (K₁ := M) (E := L)).comp
        (MulAction.stabilizer Gal(M/F) w').subtype :=
  MonoidHom.ext fun σ => rfl

/-! ### Casts of the local algebra map -/

lemma localAlgebraMapUnits_cast_tower {a a' : NK.GlobalCFT.Place M}
    {b b' : NK.GlobalCFT.Place L} (h1 : a = a') (h2 : b = b')
    (Ha : NK.GlobalCFT.Place.LiesOver a b) (H : NK.GlobalCFT.Place.LiesOver a' b')
    (x : (NK.GlobalCFT.Place.localField L b)ˣ) :
    h1 ▸ (NK.GlobalCFT.Place.localAlgebraMapUnits a b Ha x)
      = NK.GlobalCFT.Place.localAlgebraMapUnits a' b' H (h2 ▸ x) := by
  cases h1
  exact NK.HassePrinciple.localAlgebraMapUnits_cast _ h2 Ha H x

/-! ### The local units equivariance of the tower coefficient map -/

@[simp] theorem coe_localUnitsEquiv {w : NK.GlobalCFT.Place L}
    (σ : MulAction.stabilizer Gal(L/F) w) (u : (NK.GlobalCFT.Place.localField L w)ˣ) :
    ((NK.HassePrinciple.localUnitsEquiv w σ u : (NK.GlobalCFT.Place.localField L w)ˣ) :
        NK.GlobalCFT.Place.localField L w)
      = NK.HassePrinciple.localAut w σ (u : NK.GlobalCFT.Place.localField L w) := by
  rw [NK.HassePrinciple.localUnitsEquiv, Units.coe_mapEquiv]
  rfl

theorem localUnitsEquiv_eq_cast {w : NK.GlobalCFT.Place L}
    (σ : MulAction.stabilizer Gal(L/F) w) (u : (NK.GlobalCFT.Place.localField L w)ˣ) :
    NK.HassePrinciple.localUnitsEquiv w σ u
      = (MulAction.mem_stabilizer_iff.mp σ.2) ▸
          (Units.map (NK.GlobalCFT.Place.localRingEquiv σ.1 w).toMonoidHom u) := by
  apply Units.ext
  rw [coe_localUnitsEquiv]
  rw [NK.HassePrinciple.units_val_cast, Units.coe_map]
  rw [NK.HassePrinciple.localAut_apply, NK.HassePrinciple.ringEquiv_cast_apply_eq]
  rfl

theorem localUnitsEquiv_localAlgebraMapUnits_tower {w : NK.GlobalCFT.Place L}
    {w' : NK.GlobalCFT.Place M} (h : NK.GlobalCFT.Place.LiesOver w' w)
    (σ : MulAction.stabilizer Gal(M/F) w') (u : (NK.GlobalCFT.Place.localField L w)ˣ) :
    NK.GlobalCFT.Place.localAlgebraMapUnits w' w h
        (NK.HassePrinciple.localUnitsEquiv w
          (localStabilizerMapTower (F := F) (L := L) (M := M) h σ) u)
      = NK.HassePrinciple.localUnitsEquiv w' σ
          (NK.GlobalCFT.Place.localAlgebraMapUnits w' w h u) := by
  have hσ : σ.1 • w' = w' := MulAction.mem_stabilizer_iff.mp σ.2
  have hAstab : ((AlgEquiv.restrictNormalHom (K₁ := M) (E := L)) σ.1) • w = w :=
    restrictNormal_smul_eq_of_liesOver h σ.1 hσ
  have hA : ∀ y : L, algebraMap L M
      (((AlgEquiv.restrictNormalHom (K₁ := M) (E := L)) σ.1) y) = σ.1 (algebraMap L M y) :=
    fun y => AlgEquiv.restrictNormal_commutes (E := L) σ.1 y
  have h' : NK.GlobalCFT.Place.LiesOver (σ.1 • w')
      (((AlgEquiv.restrictNormalHom (K₁ := M) (E := L)) σ.1) • w) :=
    NK.HassePrinciple.liesOver_smul_of_restrict (K := F) (F := L) (L := M) σ.1
      ((AlgEquiv.restrictNormalHom (K₁ := M) (E := L)) σ.1) hA h
  have key := NK.HassePrinciple.localRingEquiv_localAlgebraMapUnits_of_restrict
      (K := F) (F := L) (L := M) σ.1
      ((AlgEquiv.restrictNormalHom (K₁ := M) (E := L)) σ.1) hA h h' u
  rw [show localStabilizerMapTower (F := F) (L := L) (M := M) h σ =
      (⟨(AlgEquiv.restrictNormalHom (K₁ := M) (E := L)) σ.1, hAstab⟩ :
        MulAction.stabilizer Gal(L/F) w) from Subtype.ext rfl]
  rw [localUnitsEquiv_eq_cast, localUnitsEquiv_eq_cast]
  rw [key, localAlgebraMapUnits_cast_tower hσ hAstab h' h
    (Units.map (NK.GlobalCFT.Place.localRingEquiv
      ((AlgEquiv.restrictNormalHom (K₁ := M) (E := L)) σ.1) w).toMonoidHom u)]

/-! ### The coefficient morphism of the tower -/

noncomputable def localUnitsMapTowerCoeff {w : NK.GlobalCFT.Place L}
    {w' : NK.GlobalCFT.Place M} (h : NK.GlobalCFT.Place.LiesOver w' w) :
    Rep.res (localStabilizerMapTower (F := F) (L := L) (M := M) h)
        (NK.HassePrinciple.localUnitsRep F L w) ⟶
      NK.HassePrinciple.localUnitsRep F M w' :=
  Rep.ofHom
    { toFun := ⇑(NK.GlobalCFT.Place.localAlgebraMapUnits w' w h).toAdditive
      map_add' := fun x y =>
        map_add (NK.GlobalCFT.Place.localAlgebraMapUnits w' w h).toAdditive x y
      map_smul' := fun n x => by
        obtain ⟨z⟩ := n
        exact AddMonoidHom.map_zsmul
          (NK.GlobalCFT.Place.localAlgebraMapUnits w' w h).toAdditive z x
      isIntertwining' := fun σ => by
        apply LinearMap.ext
        intro x
        show Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits w' w h
              (NK.HassePrinciple.localUnitsEquiv w
                (localStabilizerMapTower (F := F) (L := L) (M := M) h σ) (Additive.toMul x)))
            = Additive.ofMul (NK.HassePrinciple.localUnitsEquiv w' σ
                (NK.GlobalCFT.Place.localAlgebraMapUnits w' w h (Additive.toMul x)))
        congr 1
        exact localUnitsEquiv_localAlgebraMapUnits_tower h σ (Additive.toMul x) }

/-! ### The tower coefficient map is compatible with the global algebra maps -/

theorem localAlgebraMapUnits_congr_tower {w : NK.GlobalCFT.Place M}
    {v : NK.GlobalCFT.Place L} (h h' : NK.GlobalCFT.Place.LiesOver w v) :
    NK.GlobalCFT.Place.localAlgebraMapUnits w v h =
      NK.GlobalCFT.Place.localAlgebraMapUnits w v h' := rfl

theorem localAlgebraMapUnits_ofInfinite_tower {w : NumberField.InfinitePlace M}
    {v : NumberField.InfinitePlace L} [hwv : w.LiesOver v]
    (h : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofInfinite w)
      (NK.GlobalCFT.Place.ofInfinite v)) :
    NK.GlobalCFT.Place.localAlgebraMapUnits (NK.GlobalCFT.Place.ofInfinite w)
        (NK.GlobalCFT.Place.ofInfinite v) h =
      Units.map (NumberField.LiesOver.completionMap (v := v) (w := w)).toMonoidHom := by
  unfold NK.GlobalCFT.Place.localAlgebraMapUnits
  simp only [dif_pos hwv]

theorem localAlgebraMapUnits_ofFinite_tower {q : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers M)} {Q : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers L)} [hqQ : q.asIdeal.LiesOver Q.asIdeal]
    (h : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q)
      (NK.GlobalCFT.Place.ofFinite Q)) :
    NK.GlobalCFT.Place.localAlgebraMapUnits (NK.GlobalCFT.Place.ofFinite q)
        (NK.GlobalCFT.Place.ofFinite Q) h =
      Units.map (Commons.RingTheory.Henselian.adicCompletionMap Q q hqQ).toMonoidHom := by
  unfold NK.GlobalCFT.Place.localAlgebraMapUnits
  simp only [dif_pos hqQ]

private theorem adicCompletionMap_algebraMap_tower
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers M))
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (h : q.asIdeal.LiesOver Q.asIdeal) (x : L) :
    Commons.RingTheory.Henselian.adicCompletionMap Q q h
        (algebraMap L (Q.adicCompletion L) x) =
      algebraMap M (q.adicCompletion M) (algebraMap L M x) := by
  have h1 : algebraMap L (Q.adicCompletion L) x = (x : Q.adicCompletion L) := by
    rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]; rfl
  have h2 : (algebraMap L M x : q.adicCompletion M) =
      algebraMap M (q.adicCompletion M) (algebraMap L M x) := by
    rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]; rfl
  rw [h1, ← h2, Commons.RingTheory.Henselian.adicCompletionMap_apply]

private theorem completionMap_algebraMap_tower (w : NumberField.InfinitePlace M)
    (v : NumberField.InfinitePlace L) [hwv : w.LiesOver v] (x : L) :
    NumberField.LiesOver.completionMap (v := v) (w := w) (algebraMap L v.Completion x) =
      algebraMap M w.Completion (algebraMap L M x) := by
  haveI hST : IsScalarTower L M w.Completion := by
    refine IsScalarTower.of_algebraMap_eq fun a => ?_
    have e2 := NumberField.InfinitePlace.Completion.algebraMap_toCompletion (v := w)
      (R := M) (algebraMap L M a)
    have e3 := NumberField.InfinitePlace.Completion.algebraMap_toCompletion (v := w) (R := L) a
    apply NumberField.InfinitePlace.Completion.ext
    rw [e3, e2, UniformSpace.Completion.algebraMap_def, UniformSpace.Completion.algebraMap_def]
    simp [WithAbs.algebraMap_right_apply]
  rw [← RingHom.algebraMap_toAlgebra (NumberField.LiesOver.completionMap (v := v) (w := w))]
  rw [← IsScalarTower.algebraMap_apply L v.Completion w.Completion x]
  exact IsScalarTower.algebraMap_apply L M w.Completion x

/-- The tower local units map is compatible with the global algebra maps on units. -/
theorem localAlgebraMapUnits_algebraMap_units {w : NK.GlobalCFT.Place L}
    {w' : NK.GlobalCFT.Place M} (h : NK.GlobalCFT.Place.LiesOver w' w) (y : Lˣ) :
    NK.GlobalCFT.Place.localAlgebraMapUnits w' w h
        (Units.map (algebraMap L (NK.GlobalCFT.Place.localField L w)).toMonoidHom y)
      = Units.map (algebraMap M (NK.GlobalCFT.Place.localField M w')).toMonoidHom
          (Units.map (algebraMap L M).toMonoidHom y) := by
  rcases w with wv | qv <;> rcases w' with ww | qw
  · rcases h with ⟨w₁, v₁, hw, hv, hL⟩ | ⟨q₁, Q₁, hw, hv, hQ⟩
    · have hL' : ww.LiesOver wv := by
        rw [← NK.GlobalCFT.Place.ofInfinite_inj.mp hw,
          ← NK.GlobalCFT.Place.ofInfinite_inj.mp hv] at hL
        exact hL
      haveI := hL'
      rw [localAlgebraMapUnits_ofInfinite_tower (Or.inl ⟨w₁, v₁, hw, hv, hL⟩)]
      apply Units.ext
      simp only [Units.coe_map]
      exact completionMap_algebraMap_tower ww wv (y : L)
    · exact absurd hw (by simp)
  · rcases h with ⟨w₁, v₁, hw, hv, hL⟩ | ⟨q₁, Q₁, hw, hv, hQ⟩
    · exact absurd hw (by simp)
    · exact absurd hv (by simp)
  · rcases h with ⟨w₁, v₁, hw, hv, hL⟩ | ⟨q₁, Q₁, hw, hv, hQ⟩
    · exact absurd hv (by simp)
    · exact absurd hw (by simp)
  · rcases h with ⟨w₁, v₁, hw, hv, hL⟩ | ⟨q₁, Q₁, hw, hv, hQ⟩
    · exact absurd hw (by simp)
    · have hQ' : qw.asIdeal.LiesOver qv.asIdeal := by
        rw [← NK.GlobalCFT.Place.ofFinite_inj.mp hw,
          ← NK.GlobalCFT.Place.ofFinite_inj.mp hv] at hQ
        exact hQ
      haveI := hQ'
      rw [localAlgebraMapUnits_ofFinite_tower (Or.inr ⟨q₁, Q₁, hw, hv, hQ⟩)]
      apply Units.ext
      simp only [Units.coe_map]
      exact adicCompletionMap_algebraMap_tower qw qv hQ' (y : L)

@[simp] theorem unitsToLocalUnits_hom_ofMul {w : NK.GlobalCFT.Place L} (u : Lˣ) :
    (NK.HassePrinciple.unitsToLocalUnits F L w).hom (Additive.ofMul u)
      = Additive.ofMul (NK.HassePrinciple.unitsToLocalUnitsHom w u) := rfl

@[simp] theorem unitsInclTowerCoeff_ofMul (x : Lˣ) :
    (NK.NUV2.LC.unitsInclTowerCoeff (F := F) (L := L) (M := M)).hom (Additive.ofMul x)
      = Additive.ofMul (Units.map (algebraMap L M).toMonoidHom x) := rfl

@[simp] theorem localUnitsMapTowerCoeff_ofMul {w : NK.GlobalCFT.Place L}
    {w' : NK.GlobalCFT.Place M} (h : NK.GlobalCFT.Place.LiesOver w' w)
    (x : (NK.GlobalCFT.Place.localField L w)ˣ) :
    (localUnitsMapTowerCoeff (F := F) (L := L) (M := M) h).hom (Additive.ofMul x)
      = Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits w' w h x) := rfl

/-! ### Functoriality of `groupCohomology.map` -/

theorem map_f_comp_id {k H G : Type} [CommRing k] [Group G] [Group H] (f : G →* H)
    {A : Rep k H} {B C : Rep k G} (φ : Rep.res f A ⟶ B) (ψ : B ⟶ C) (n : ℕ) :
    groupCohomology.map f (φ ≫ ψ) n =
      groupCohomology.map f φ n ≫ groupCohomology.map (MonoidHom.id G) ψ n := by
  rw [← groupCohomology.map_comp f (MonoidHom.id G) φ ψ n]
  refine groupCohomology.map_congr (MonoidHom.comp_id f).symm ?_ n
  rfl

theorem map_id_comp_apply {k H G : Type} [CommRing k] [Group G] [Group H] (f : G →* H)
    {A : Rep k H} {C : Rep k G} (X : Rep.res f A ⟶ C) (n : ℕ) :
    groupCohomology.map f (𝟙 (Rep.res f A)) n ≫ groupCohomology.map (MonoidHom.id G) X n =
      groupCohomology.map f X n := by
  rw [← map_f_comp_id f (𝟙 (Rep.res f A)) X n]
  simp

theorem map_resFunctor_map {k H G : Type} [CommRing k] [Group G] [Group H] (f : G →* H)
    {A B : Rep k H} (θ : A ⟶ B) (n : ℕ) :
    groupCohomology.map f ((Rep.resFunctor f).map θ) n =
      groupCohomology.map (MonoidHom.id H) θ n ≫
        groupCohomology.map f (𝟙 (Rep.res f B)) n := by
  have hnat := (groupCohomology.resNatTrans k f n).naturality θ
  have h1 : (Rep.resFunctor f ⋙ groupCohomology.functor k G n).map θ =
      groupCohomology.map (MonoidHom.id G) ((Rep.resFunctor f).map θ) n := by
    simp only [Functor.comp_map, groupCohomology.functor_map]
  rw [h1] at hnat
  have hnat' : groupCohomology.map f (𝟙 (Rep.res f A)) n ≫
        groupCohomology.map (MonoidHom.id G) ((Rep.resFunctor f).map θ) n =
      groupCohomology.map (MonoidHom.id H) θ n ≫
        groupCohomology.map f (𝟙 (Rep.res f B)) n := hnat.symm
  calc groupCohomology.map f ((Rep.resFunctor f).map θ) n
      = groupCohomology.map f (𝟙 (Rep.res f A)) n ≫
          groupCohomology.map (MonoidHom.id G) ((Rep.resFunctor f).map θ) n :=
        (map_id_comp_apply f ((Rep.resFunctor f).map θ) n).symm
    _ = groupCohomology.map (MonoidHom.id H) θ n ≫
          groupCohomology.map f (𝟙 (Rep.res f B)) n := hnat'

/-! ### The level square -/

/-- the local level map `v`. -/
noncomputable def localLevelMap {w : NK.GlobalCFT.Place L} {w' : NK.GlobalCFT.Place M}
    (h : NK.GlobalCFT.Place.LiesOver w' w) :
    groupCohomology (NK.HassePrinciple.localUnitsRep F L w) 2 ⟶
      groupCohomology (NK.HassePrinciple.localUnitsRep F M w') 2 :=
  groupCohomology.map (localStabilizerMapTower (F := F) (L := L) (M := M) h)
      (𝟙 (Rep.res (localStabilizerMapTower (F := F) (L := L) (M := M) h)
        (NK.HassePrinciple.localUnitsRep F L w))) 2 ≫
    groupCohomology.map (MonoidHom.id (MulAction.stabilizer Gal(M/F) w'))
      (localUnitsMapTowerCoeff (F := F) (L := L) (M := M) h) 2

theorem locUnits_naturality_aux {w : NK.GlobalCFT.Place L} {w' : NK.GlobalCFT.Place M}
    (h : NK.GlobalCFT.Place.LiesOver w' w) :
    groupCohomology.map (MonoidHom.id (MulAction.stabilizer Gal(L/F) w))
        (NK.HassePrinciple.unitsToLocalUnits F L w) 2 ≫
      (groupCohomology.map (localStabilizerMapTower (F := F) (L := L) (M := M) h)
          (𝟙 (Rep.res (localStabilizerMapTower (F := F) (L := L) (M := M) h)
            (NK.HassePrinciple.localUnitsRep F L w))) 2 ≫
        groupCohomology.map (MonoidHom.id (MulAction.stabilizer Gal(M/F) w'))
          (localUnitsMapTowerCoeff (F := F) (L := L) (M := M) h) 2)
      = groupCohomology.map (localStabilizerMapTower (F := F) (L := L) (M := M) h)
          ((Rep.resFunctor (localStabilizerMapTower (F := F) (L := L) (M := M) h)).map
              (NK.HassePrinciple.unitsToLocalUnits F L w) ≫
            localUnitsMapTowerCoeff (F := F) (L := L) (M := M) h) 2 := by
  rw [← Category.assoc]
  rw [← map_resFunctor_map (localStabilizerMapTower (F := F) (L := L) (M := M) h)
    (NK.HassePrinciple.unitsToLocalUnits F L w) 2]
  rw [← map_f_comp_id (localStabilizerMapTower (F := F) (L := L) (M := M) h)
    ((Rep.resFunctor (localStabilizerMapTower (F := F) (L := L) (M := M) h)).map
      (NK.HassePrinciple.unitsToLocalUnits F L w))
    (localUnitsMapTowerCoeff (F := F) (L := L) (M := M) h) 2]

theorem unitsLevelMapTower_comp_locUnitsV3 {w : NK.GlobalCFT.Place L}
    {w' : NK.GlobalCFT.Place M} (h : NK.GlobalCFT.Place.LiesOver w' w) :
    (NK.NUV2.LC.unitsLevelMapTower (F := F) (L := L) (M := M)) ≫
        (NK.HassePrinciple.locUnits F M w')
      = (NK.HassePrinciple.locUnits F L w) ≫
        (localLevelMap (F := F) (L := L) (M := M) h) := by
  simp only [NK.HassePrinciple.locUnits, NK.NUV2.LC.unitsLevelMapTower, localLevelMap,
    groupCohomology.resNatTrans_app]
  conv_lhs => rw [map_id_comp_apply, ← groupCohomology.map_comp]
  conv_rhs => rw [Category.assoc]
  conv_rhs => rw [locUnits_naturality_aux (F := F) (L := L) (M := M) h]
  conv_rhs => rw [← groupCohomology.map_comp]
  refine groupCohomology.map_congr
    (G := MulAction.stabilizer Gal(M/F) w') (H := Gal(L/F))
    (A := NK.HassePrinciple.unitsRep F L)
    (B := NK.HassePrinciple.localUnitsRep F M w')
    (f := (AlgEquiv.restrictNormalHom (K₁ := M) (E := L)).comp
      (MulAction.stabilizer Gal(M/F) w').subtype)
    (g := (MulAction.stabilizer Gal(L/F) w).subtype.comp
      (localStabilizerMapTower (F := F) (L := L) (M := M) h))
    (localStabilizerMapTower_comp_subtype (F := F) (L := L) (M := M) h).symm ?_ 2
  ext x
  conv_lhs => rw [← ofMul_toMul x]
  conv_rhs => rw [← ofMul_toMul x]
  simp only [Rep.hom_comp_toLinearMap, Rep.resMap_hom_toLinearMap, LinearMap.comp_apply,
    LinearMap.id_apply, Rep.hom_id, Representation.IntertwiningMap.toLinearMap_apply,
    Representation.IntertwiningMap.id_apply,
    unitsToLocalUnits_hom_ofMul, unitsInclTowerCoeff_ofMul, localUnitsMapTowerCoeff_ofMul]
  exact (localAlgebraMapUnits_algebraMap_units h (Additive.toMul x)).symm

theorem locUnits_tower_eq_zero {F L M : Type} [Field F] [NumberField F] [Field L] [NumberField L]
    [Field M] [NumberField M]
    [Algebra F L] [Algebra F M] [Algebra L M] [IsScalarTower F L M]
    [FiniteDimensional F L] [IsGalois F L] [FiniteDimensional F M] [IsGalois F M]
    (b : groupCohomology (NK.HassePrinciple.unitsRep F L) 2)
    {w : NK.GlobalCFT.Place L} {w' : NK.GlobalCFT.Place M} (h : NK.GlobalCFT.Place.LiesOver w' w)
    (hb : (NK.HassePrinciple.locUnits F L w).hom b = 0) :
    (NK.HassePrinciple.locUnits F M w').hom
      ((NK.NUV2.LC.unitsLevelMapTower (F := F) (L := L) (M := M)) b) = 0 := by
  have hsq := unitsLevelMapTower_comp_locUnitsV3 (F := F) (L := L) (M := M) h
  have h2 : (NK.HassePrinciple.locUnits F M w').hom
        ((NK.NUV2.LC.unitsLevelMapTower (F := F) (L := L) (M := M)) b)
      = (localLevelMap (F := F) (L := L) (M := M) h).hom
          ((NK.HassePrinciple.locUnits F L w).hom b) := by
    have hh := congrArg (fun f : groupCohomology (NK.HassePrinciple.unitsRep F L) 2 ⟶
        groupCohomology (NK.HassePrinciple.localUnitsRep F M w') 2 => f.hom b) hsq
    simpa using hh
  rw [h2, hb]
  exact map_zero _

end NK.NUV2.LC.RouteB.v2
