/-
Area AV: the scaled `𝔾_m`-action on `ℙ¹` — the overlap compatibility of the two charts.

We prove that the two chart descriptions `srcChartHom k 0` and `srcChartHom k 1` of the
scaling morphism agree on the overlap of the two charts `srcChartι k 0` and `srcChartι k 1`
of `srcScheme k = ℙ¹ × 𝔾_m`.

The overlap is identified with the "double chart" `D(x₀x₁) × 𝔾_m`; on it the two ring
descriptions are `x₁/x₀ ↦ (x₁/x₀) T⁻¹` and `x₀/x₁ ↦ (x₀/x₁) T`, which agree after the
identification `x₀/x₁ = (x₁/x₀)⁻¹`.
-/
import Mathlib
import Submission.Work.AbVar.P1Action.SourceChart
import Submission.Work.AbVar.ProjectiveLine.awaySurjective

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

open CategoryTheory AlgebraicGeometry MonObj MvPolynomial HomogeneousLocalization Limits
open scoped MonoidalCategory TensorProduct

namespace Work.AbVar.P1Action

section

variable (k : Type*) [Field k]

/-! ## The basic open `D₊(Xᵢ)` of `ℙ¹`, viewed inside `ℙ¹` -/

/-- The standard basic open `D₊(Xᵢ)` of `ℙ¹`. -/
noncomputable def p1BasicOpen (i : Fin 2) : (Over.left (Work.AbVar.P1 k)).Opens :=
  Proj.basicOpen (Work.AbVar.ProjectiveLine.StdG k) (MvPolynomial.X i)

/-- The range of the chart inclusion `srcChartMap k i`. -/
lemma srcChartMap_opensRange (i : Fin 2) :
    (srcChartMap k i).opensRange
      = pullback.fst (Work.AbVar.P1 k).hom (gmHom k) ⁻¹ᵁ (p1BasicOpen k i) := by
  apply TopologicalSpace.Opens.ext
  rw [Scheme.Hom.coe_opensRange, srcChartMap, AlgebraicGeometry.Scheme.Pullback.range_map]
  have hC : Set.range (chartObjHom k i) = ↑(p1BasicOpen k i) := by
    rw [← Scheme.Hom.coe_opensRange]
    congr 1
    simp only [p1BasicOpen, chartObjHom]
    exact Proj.opensRange_awayι _ _ _ _
  rw [hC, Set.range_eq_univ.mpr (show Function.Surjective
        (⇑(𝟙 (Spec (CommRingCat.of (L k))))) from fun x => ⟨x, rfl⟩),
    Set.preimage_univ, Set.inter_univ]
  exact (Scheme.Hom.coe_preimage (f := pullback.fst (Work.AbVar.P1 k).hom (gmHom k))
    (U := p1BasicOpen k i)).symm

/-- The range of the chart inclusion `srcChartι k i`. -/
lemma srcChartι_opensRange (i : Fin 2) :
    (srcChartι k i).opensRange
      = pullback.fst (Work.AbVar.P1 k).hom (gmHom k) ⁻¹ᵁ (p1BasicOpen k i) := by
  change ((srcChartIso k i).inv ≫ srcChartMap k i).opensRange
      = pullback.fst (Work.AbVar.P1 k).hom (gmHom k) ⁻¹ᵁ (p1BasicOpen k i)
  rw [Scheme.Hom.opensRange_comp_of_isIso]
  exact srcChartMap_opensRange k i

/-! ## The double chart `D₊(X₀X₁) × 𝔾_m` of the source -/

/-- `k[x₀,x₁]`-localisation at `x₀x₁`, as a `k`-algebra. -/
noncomputable def dblAlg :
    k →+* Away (Work.AbVar.ProjectiveLine.StdG k) (MvPolynomial.X 0 * MvPolynomial.X 1) :=
  (fromZeroRingHom (Work.AbVar.ProjectiveLine.StdG k)
      (Submonoid.powers (MvPolynomial.X 0 * MvPolynomial.X 1))).comp
    (Work.AbVar.ProjectiveLine.constToZero (R := k))

noncomputable instance instAlgebraDouble :
    Algebra k (Away (Work.AbVar.ProjectiveLine.StdG k) (MvPolynomial.X 0 * MvPolynomial.X 1)) :=
  (dblAlg k).toAlgebra

/-- The coordinate ring of the double chart `D₊(X₀X₁) × 𝔾_m`. -/
noncomputable abbrev srcDoubleRing : Type _ :=
  Away (Work.AbVar.ProjectiveLine.StdG k) (MvPolynomial.X 0 * MvPolynomial.X 1) ⊗[k] L k

lemma X01_mem_stdG :
    (MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) k) ∈
      Work.AbVar.ProjectiveLine.StdG k 2 :=
  SetLike.mul_mem_graded (Work.AbVar.ProjectiveLine.X_mem_stdG 0)
    (Work.AbVar.ProjectiveLine.X_mem_stdG 1)

/-- The open immersion `D₊(X₀X₁) ⟶ ℙ¹`. -/
noncomputable abbrev srcDoubleObjHom :
    Spec (CommRingCat.of (Away (Work.AbVar.ProjectiveLine.StdG k)
      (MvPolynomial.X 0 * MvPolynomial.X 1))) ⟶ (Work.AbVar.P1 k).left :=
  Proj.awayι (Work.AbVar.ProjectiveLine.StdG k) (MvPolynomial.X 0 * MvPolynomial.X 1)
    (X01_mem_stdG k) (by norm_num)

instance srcDoubleObjHom_isOpenImmersion : IsOpenImmersion (srcDoubleObjHom k) :=
  inferInstanceAs (IsOpenImmersion (Proj.awayι (Work.AbVar.ProjectiveLine.StdG k)
    (MvPolynomial.X 0 * MvPolynomial.X 1) (X01_mem_stdG k) (by norm_num)))

/-- The structure morphism of `D₊(X₀X₁)`. -/
lemma srcDoubleObjHom_hom :
    srcDoubleObjHom k ≫ (Work.AbVar.P1 k).hom
      = Spec.map (CommRingCat.ofHom (algebraMap k
          (Away (Work.AbVar.ProjectiveLine.StdG k) (MvPolynomial.X 0 * MvPolynomial.X 1)))) := by
  show Proj.awayι (Work.AbVar.ProjectiveLine.StdG k) (MvPolynomial.X 0 * MvPolynomial.X 1)
      (X01_mem_stdG k) (by norm_num) ≫ (Work.AbVar.P1 k).hom = _
  have h1 : Proj.awayι (Work.AbVar.ProjectiveLine.StdG k)
        (MvPolynomial.X 0 * MvPolynomial.X 1) (X01_mem_stdG k) (by norm_num) ≫
        Proj.toSpecZero (Work.AbVar.ProjectiveLine.StdG k)
      = Spec.map (CommRingCat.ofHom (HomogeneousLocalization.fromZeroRingHom
          (Work.AbVar.ProjectiveLine.StdG k)
          (Submonoid.powers (MvPolynomial.X 0 * MvPolynomial.X 1)))) :=
    Proj.awayι_toSpecZero _ _ _ _
  have h2 : (HomogeneousLocalization.fromZeroRingHom
        (Work.AbVar.ProjectiveLine.StdG k)
        (Submonoid.powers (MvPolynomial.X 0 * MvPolynomial.X 1))).comp
        (Work.AbVar.p1BaseEquiv k).toRingHom
      = algebraMap k (Away (Work.AbVar.ProjectiveLine.StdG k)
          (MvPolynomial.X 0 * MvPolynomial.X 1)) := by
    rw [Work.AbVar.P1Action.p1BaseEquiv_toRingHom_eq]
    rfl
  calc Proj.awayι (Work.AbVar.ProjectiveLine.StdG k) (MvPolynomial.X 0 * MvPolynomial.X 1)
        (X01_mem_stdG k) (by norm_num) ≫ (Work.AbVar.P1 k).hom
      = Proj.awayι (Work.AbVar.ProjectiveLine.StdG k) (MvPolynomial.X 0 * MvPolynomial.X 1)
          (X01_mem_stdG k) (by norm_num) ≫ (Proj.toSpecZero (Work.AbVar.ProjectiveLine.StdG k)
            ≫ Spec.map (CommRingCat.ofHom (Work.AbVar.p1BaseEquiv k).toRingHom)) := by
        rw [Work.AbVar.p1_hom]
    _ = (Proj.awayι (Work.AbVar.ProjectiveLine.StdG k) (MvPolynomial.X 0 * MvPolynomial.X 1)
            (X01_mem_stdG k) (by norm_num) ≫ Proj.toSpecZero (Work.AbVar.ProjectiveLine.StdG k))
          ≫ Spec.map (CommRingCat.ofHom (Work.AbVar.p1BaseEquiv k).toRingHom) :=
        (Category.assoc _ _ _).symm
    _ = Spec.map (CommRingCat.ofHom (HomogeneousLocalization.fromZeroRingHom
            (Work.AbVar.ProjectiveLine.StdG k)
            (Submonoid.powers (MvPolynomial.X 0 * MvPolynomial.X 1))))
          ≫ Spec.map (CommRingCat.ofHom (Work.AbVar.p1BaseEquiv k).toRingHom) := by
        rw [h1]
    _ = Spec.map (CommRingCat.ofHom ((HomogeneousLocalization.fromZeroRingHom
            (Work.AbVar.ProjectiveLine.StdG k)
            (Submonoid.powers (MvPolynomial.X 0 * MvPolynomial.X 1))).comp
            (Work.AbVar.p1BaseEquiv k).toRingHom)) := by
        rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    _ = Spec.map (CommRingCat.ofHom (algebraMap k
          (Away (Work.AbVar.ProjectiveLine.StdG k) (MvPolynomial.X 0 * MvPolynomial.X 1)))) := by
        rw [h2]

/-- The fibre product `D₊(X₀X₁) × 𝔾_m`. -/
noncomputable abbrev srcDoubleScheme : Scheme :=
  pullback (srcDoubleObjHom k ≫ (Work.AbVar.P1 k).hom) (gmHom k)

/-- The inclusion of the double chart into the source. -/
noncomputable abbrev srcDoubleMap : srcDoubleScheme k ⟶ srcScheme k :=
  pullback.map (srcDoubleObjHom k ≫ (Work.AbVar.P1 k).hom) (gmHom k)
    (Work.AbVar.P1 k).hom (gmHom k) (srcDoubleObjHom k) (𝟙 _) (𝟙 _)
    (by rw [Category.assoc, Category.comp_id]) (by rw [Category.comp_id, Category.id_comp])

instance srcDoubleMap_isOpenImmersion : IsOpenImmersion (srcDoubleMap k) :=
  Scheme.pullback_map_isOpenImmersion _ _ _ _ _ _ _ _ _

lemma srcDoubleMap_fst :
    srcDoubleMap k ≫ pullback.fst (Work.AbVar.P1 k).hom (gmHom k)
      = pullback.fst (srcDoubleObjHom k ≫ (Work.AbVar.P1 k).hom) (gmHom k) ≫ srcDoubleObjHom k := by
  simp only [srcDoubleMap, pullback.map, pullback.lift_fst, Category.comp_id]

lemma srcDoubleMap_snd :
    srcDoubleMap k ≫ pullback.snd (Work.AbVar.P1 k).hom (gmHom k)
      = pullback.snd (srcDoubleObjHom k ≫ (Work.AbVar.P1 k).hom) (gmHom k) := by
  simp only [srcDoubleMap, pullback.map, pullback.lift_snd, Category.comp_id]

/-- The identification of `D₊(X₀X₁) × 𝔾_m` with `Spec (srcDoubleRing k)`. -/
noncomputable abbrev srcDoubleIso :
    srcDoubleScheme k ≅ Spec (CommRingCat.of (srcDoubleRing k)) :=
  pullback.congrHom (srcDoubleObjHom_hom k) (rfl : gmHom k = gmHom k) ≪≫
    pullbackSpecIso k (Away (Work.AbVar.ProjectiveLine.StdG k)
      (MvPolynomial.X 0 * MvPolynomial.X 1)) (L k)

lemma srcDoubleIso_inv_fst :
    (srcDoubleIso k).inv ≫ pullback.fst (srcDoubleObjHom k ≫ (Work.AbVar.P1 k).hom) (gmHom k)
      = Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeLeftRingHom
            (R := k) (A := Away (Work.AbVar.ProjectiveLine.StdG k)
              (MvPolynomial.X 0 * MvPolynomial.X 1)) (B := L k))) := by
  rw [← Iso.inv_hom_id_assoc (srcDoubleIso k) (Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeLeftRingHom (R := k)
      (A := Away (Work.AbVar.ProjectiveLine.StdG k) (MvPolynomial.X 0 * MvPolynomial.X 1))
      (B := L k))))]
  congr 1
  simp only [srcDoubleIso, Iso.trans_hom, pullback.congrHom_hom, pullback.map, pullback.lift_fst,
    Category.comp_id, pullbackSpecIso_hom_fst, Category.assoc]

lemma srcDoubleIso_inv_snd :
    (srcDoubleIso k).inv ≫ pullback.snd (srcDoubleObjHom k ≫ (Work.AbVar.P1 k).hom) (gmHom k)
      = Spec.map (CommRingCat.ofHom
          ((RingHomClass.toRingHom (Algebra.TensorProduct.includeRight
            (R := k) (A := Away (Work.AbVar.ProjectiveLine.StdG k)
              (MvPolynomial.X 0 * MvPolynomial.X 1)) (B := L k))))) := by
  rw [← Iso.inv_hom_id_assoc (srcDoubleIso k) (Spec.map (CommRingCat.ofHom
    ((RingHomClass.toRingHom (Algebra.TensorProduct.includeRight (R := k)
      (A := Away (Work.AbVar.ProjectiveLine.StdG k) (MvPolynomial.X 0 * MvPolynomial.X 1))
      (B := L k))))))]
  congr 1
  simp only [srcDoubleIso, Iso.trans_hom, pullback.congrHom_hom, pullback.map, pullback.lift_snd,
    Category.comp_id, Category.id_comp, pullbackSpecIso_hom_snd, Category.assoc]

/-- The inclusion of the double chart, as a morphism from `Spec (srcDoubleRing k)`. -/
noncomputable abbrev srcDoubleι :
    Spec (CommRingCat.of (srcDoubleRing k)) ⟶ srcScheme k :=
  (srcDoubleIso k).inv ≫ srcDoubleMap k

instance srcDoubleι_isOpenImmersion : IsOpenImmersion (srcDoubleι k) :=
  IsOpenImmersion.comp _ _

lemma srcDoubleMap_opensRange :
    (srcDoubleMap k).opensRange
      = pullback.fst (Work.AbVar.P1 k).hom (gmHom k) ⁻¹ᵁ (p1BasicOpen k 0 ⊓ p1BasicOpen k 1) := by
  apply TopologicalSpace.Opens.ext
  rw [Scheme.Hom.coe_opensRange, srcDoubleMap, AlgebraicGeometry.Scheme.Pullback.range_map]
  have hC : Set.range (srcDoubleObjHom k) = ↑(p1BasicOpen k 0 ⊓ p1BasicOpen k 1) := by
    rw [← Scheme.Hom.coe_opensRange]
    congr 1
    rw [show (srcDoubleObjHom k).opensRange
        = Proj.basicOpen (Work.AbVar.ProjectiveLine.StdG k)
            (MvPolynomial.X 0 * MvPolynomial.X 1) from
      Proj.opensRange_awayι _ _ _ _]
    rw [Proj.basicOpen_mul]
    rfl
  rw [hC, Set.range_eq_univ.mpr (show Function.Surjective
        (⇑(𝟙 (Spec (CommRingCat.of (L k))))) from fun x => ⟨x, rfl⟩),
    Set.preimage_univ, Set.inter_univ]
  exact (Scheme.Hom.coe_preimage (f := pullback.fst (Work.AbVar.P1 k).hom (gmHom k))
    (U := p1BasicOpen k 0 ⊓ p1BasicOpen k 1)).symm

lemma srcDoubleι_opensRange :
    (srcDoubleι k).opensRange
      = pullback.fst (Work.AbVar.P1 k).hom (gmHom k) ⁻¹ᵁ (p1BasicOpen k 0 ⊓ p1BasicOpen k 1) := by
  change ((srcDoubleIso k).inv ≫ srcDoubleMap k).opensRange = _
  rw [Scheme.Hom.opensRange_comp_of_isIso]
  exact srcDoubleMap_opensRange k

lemma srcChartι_range (i : Fin 2) :
    Set.range (srcChartι k i)
      = ↑(pullback.fst (Work.AbVar.P1 k).hom (gmHom k) ⁻¹ᵁ (p1BasicOpen k i)) := by
  rw [← Scheme.Hom.coe_opensRange, srcChartι_opensRange]

lemma srcDoubleι_range :
    Set.range (srcDoubleι k)
      = ↑(pullback.fst (Work.AbVar.P1 k).hom (gmHom k) ⁻¹ᵁ (p1BasicOpen k 0 ⊓ p1BasicOpen k 1)) := by
  rw [← Scheme.Hom.coe_opensRange, srcDoubleι_opensRange]

/-- The overlap of the two charts is the double chart. -/
lemma srcChartι_range_inter :
    Set.range (pullback.fst (srcChartι k 0) (srcChartι k 1) ≫ srcChartι k 0)
      = Set.range (srcDoubleι k) := by
  rw [AlgebraicGeometry.Scheme.Pullback.range_fst_comp, srcChartι_range k 0,
    srcChartι_range k 1, srcDoubleι_range]
  rw [Scheme.Hom.preimage_inf]
  rfl

/-- The isomorphism between the overlap of the two charts and the double chart. -/
noncomputable def srcOverlapIso :
    pullback (srcChartι k 0) (srcChartι k 1) ≅ Spec (CommRingCat.of (srcDoubleRing k)) :=
  IsOpenImmersion.isoOfRangeEq
    (pullback.fst (srcChartι k 0) (srcChartι k 1) ≫ srcChartι k 0) (srcDoubleι k)
    (srcChartι_range_inter k)

/-- The `k`-algebra map `k[x₁/x₀] ⟶ k[x₁/x₀, x₀/x₁]`. -/
noncomputable abbrev dblAwayMap0 : chartRing k 0 →+* Away (Work.AbVar.ProjectiveLine.StdG k)
    (MvPolynomial.X 0 * MvPolynomial.X 1) :=
  awayMap (Work.AbVar.ProjectiveLine.StdG k) (Work.AbVar.ProjectiveLine.X_mem_stdG 1) (by
    show (MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) k)
      = MvPolynomial.X 0 * MvPolynomial.X 1
    rfl)

/-- The `k`-algebra map `k[x₀/x₁] ⟶ k[x₁/x₀, x₀/x₁]`. -/
noncomputable abbrev dblAwayMap1 : chartRing k 1 →+* Away (Work.AbVar.ProjectiveLine.StdG k)
    (MvPolynomial.X 0 * MvPolynomial.X 1) :=
  awayMap (Work.AbVar.ProjectiveLine.StdG k) (Work.AbVar.ProjectiveLine.X_mem_stdG 0) (by
    show (MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) k)
      = MvPolynomial.X 1 * MvPolynomial.X 0
    rw [mul_comm])

lemma dblAwayMap0_base (c : k) :
    dblAwayMap0 k (algebraMap k (chartRing k 0) c) =
      algebraMap k (Away (Work.AbVar.ProjectiveLine.StdG k)
        (MvPolynomial.X 0 * MvPolynomial.X 1)) c := by
  change awayMap _ _ _ (algebraMap k (chartRing k 0) c) = _
  rw [show algebraMap k (chartRing k 0) c = HomogeneousLocalization.fromZeroRingHom
      (Work.AbVar.ProjectiveLine.StdG k) (Submonoid.powers (MvPolynomial.X 0))
      (Work.AbVar.ProjectiveLine.constToZero (R := k) c) from rfl]
  rw [awayMap_fromZeroRingHom]
  rfl

lemma dblAwayMap1_base (c : k) :
    dblAwayMap1 k (algebraMap k (chartRing k 1) c) =
      algebraMap k (Away (Work.AbVar.ProjectiveLine.StdG k)
        (MvPolynomial.X 0 * MvPolynomial.X 1)) c := by
  change awayMap _ _ _ (algebraMap k (chartRing k 1) c) = _
  rw [show algebraMap k (chartRing k 1) c = HomogeneousLocalization.fromZeroRingHom
      (Work.AbVar.ProjectiveLine.StdG k) (Submonoid.powers (MvPolynomial.X 1))
      (Work.AbVar.ProjectiveLine.constToZero (R := k) c) from rfl]
  rw [awayMap_fromZeroRingHom]
  rfl

/-- The `k`-algebra map `k[x₁/x₀] ⟶ k[x₁/x₀, x₀/x₁]`. -/
noncomputable def dblMap0Hom :
    chartRing k 0 →ₐ[k] Away (Work.AbVar.ProjectiveLine.StdG k)
      (MvPolynomial.X 0 * MvPolynomial.X 1) where
  toRingHom := dblAwayMap0 k
  commutes' := dblAwayMap0_base k

/-- The `k`-algebra map `k[x₀/x₁] ⟶ k[x₁/x₀, x₀/x₁]`. -/
noncomputable def dblMap1Hom :
    chartRing k 1 →ₐ[k] Away (Work.AbVar.ProjectiveLine.StdG k)
      (MvPolynomial.X 0 * MvPolynomial.X 1) where
  toRingHom := dblAwayMap1 k
  commutes' := dblAwayMap1_base k

/-! ## The chart maps from the double chart -/

/-- The map `D₊(X₀X₁) × 𝔾_m ⟶ D₊(Xᵢ) × 𝔾_m` induced by localisation at `X_{other i}`. -/
noncomputable def dblRingMap (i : Fin 2) :
    srcChartRing k i →+* srcDoubleRing k :=
  match i with
  | 0 => Algebra.TensorProduct.map (dblMap0Hom k) (AlgHom.id k (L k))
  | 1 => Algebra.TensorProduct.map (dblMap1Hom k) (AlgHom.id k (L k))

/-- The morphism `Spec (srcDoubleRing k) ⟶ Spec (srcChartRing k i)`. -/
noncomputable def dblToChart (i : Fin 2) :
    Spec (CommRingCat.of (srcDoubleRing k)) ⟶ Spec (CommRingCat.of (srcChartRing k i)) :=
  Spec.map (CommRingCat.ofHom (dblRingMap k i))

lemma dblRingMap_zero_tmul (a : chartRing k 0) (b : L k) :
    dblRingMap k 0 (a ⊗ₜ[k] b) = dblAwayMap0 k a ⊗ₜ[k] b := by
  show (Algebra.TensorProduct.map (dblMap0Hom k) (AlgHom.id k (L k))) (a ⊗ₜ[k] b) = _
  rw [Algebra.TensorProduct.map_tmul]
  rfl

lemma dblRingMap_one_tmul (a : chartRing k 1) (b : L k) :
    dblRingMap k 1 (a ⊗ₜ[k] b) = dblAwayMap1 k a ⊗ₜ[k] b := by
  show (Algebra.TensorProduct.map (dblMap1Hom k) (AlgHom.id k (L k))) (a ⊗ₜ[k] b) = _
  rw [Algebra.TensorProduct.map_tmul]
  rfl

lemma includeLeft_dblRingMap_zero :
    (dblRingMap k 0).comp (Algebra.TensorProduct.includeLeftRingHom (R := k)
        (A := chartRing k 0) (B := L k))
      = (Algebra.TensorProduct.includeLeftRingHom (R := k)
          (A := Away (Work.AbVar.ProjectiveLine.StdG k)
            (MvPolynomial.X 0 * MvPolynomial.X 1)) (B := L k)).comp (dblAwayMap0 k) := by
  apply RingHom.ext; intro a
  rw [RingHom.comp_apply, RingHom.comp_apply, Algebra.TensorProduct.includeLeftRingHom_apply,
    Algebra.TensorProduct.includeLeftRingHom_apply]
  exact dblRingMap_zero_tmul k a 1

lemma includeRight_dblRingMap_zero :
    (dblRingMap k 0).comp (RingHomClass.toRingHom (Algebra.TensorProduct.includeRight (R := k)
        (A := chartRing k 0) (B := L k)))
      = (RingHomClass.toRingHom (Algebra.TensorProduct.includeRight (R := k)
          (A := Away (Work.AbVar.ProjectiveLine.StdG k)
            (MvPolynomial.X 0 * MvPolynomial.X 1)) (B := L k))) := by
  apply RingHom.ext; intro b
  rw [RingHom.comp_apply]
  change dblRingMap k 0 ((1 : chartRing k 0) ⊗ₜ[k] b)
      = ((1 : Away (Work.AbVar.ProjectiveLine.StdG k)
          (MvPolynomial.X 0 * MvPolynomial.X 1)) ⊗ₜ[k] b)
  rw [dblRingMap_zero_tmul, map_one]

lemma includeLeft_dblRingMap_one :
    (dblRingMap k 1).comp (Algebra.TensorProduct.includeLeftRingHom (R := k)
        (A := chartRing k 1) (B := L k))
      = (Algebra.TensorProduct.includeLeftRingHom (R := k)
          (A := Away (Work.AbVar.ProjectiveLine.StdG k)
            (MvPolynomial.X 0 * MvPolynomial.X 1)) (B := L k)).comp (dblAwayMap1 k) := by
  apply RingHom.ext; intro a
  rw [RingHom.comp_apply, RingHom.comp_apply, Algebra.TensorProduct.includeLeftRingHom_apply,
    Algebra.TensorProduct.includeLeftRingHom_apply]
  exact dblRingMap_one_tmul k a 1

lemma includeRight_dblRingMap_one :
    (dblRingMap k 1).comp (RingHomClass.toRingHom (Algebra.TensorProduct.includeRight (R := k)
        (A := chartRing k 1) (B := L k)))
      = (RingHomClass.toRingHom (Algebra.TensorProduct.includeRight (R := k)
          (A := Away (Work.AbVar.ProjectiveLine.StdG k)
            (MvPolynomial.X 0 * MvPolynomial.X 1)) (B := L k))) := by
  apply RingHom.ext; intro b
  rw [RingHom.comp_apply]
  change dblRingMap k 1 ((1 : chartRing k 1) ⊗ₜ[k] b)
      = ((1 : Away (Work.AbVar.ProjectiveLine.StdG k)
          (MvPolynomial.X 0 * MvPolynomial.X 1)) ⊗ₜ[k] b)
  rw [dblRingMap_one_tmul, map_one]

lemma dblToChart_includeLeft_zero :
    dblToChart k 0 ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := k) (A := chartRing k 0) (B := L k)))
      = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
          (R := k) (A := Away (Work.AbVar.ProjectiveLine.StdG k)
            (MvPolynomial.X 0 * MvPolynomial.X 1)) (B := L k)))
        ≫ Spec.map (CommRingCat.ofHom (dblAwayMap0 k)) := by
  rw [dblToChart, ← Spec.map_comp, ← CommRingCat.ofHom_comp, includeLeft_dblRingMap_zero,
    CommRingCat.ofHom_comp, Spec.map_comp]

lemma dblToChart_includeRight_zero :
    dblToChart k 0 ≫ Spec.map (CommRingCat.ofHom (RingHomClass.toRingHom
        (Algebra.TensorProduct.includeRight (R := k) (A := chartRing k 0) (B := L k))))
      = Spec.map (CommRingCat.ofHom (RingHomClass.toRingHom
          (Algebra.TensorProduct.includeRight (R := k)
            (A := Away (Work.AbVar.ProjectiveLine.StdG k)
              (MvPolynomial.X 0 * MvPolynomial.X 1)) (B := L k)))) := by
  rw [dblToChart, ← Spec.map_comp, ← CommRingCat.ofHom_comp, includeRight_dblRingMap_zero]

lemma dblToChart_includeLeft_one :
    dblToChart k 1 ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := k) (A := chartRing k 1) (B := L k)))
      = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
          (R := k) (A := Away (Work.AbVar.ProjectiveLine.StdG k)
            (MvPolynomial.X 0 * MvPolynomial.X 1)) (B := L k)))
        ≫ Spec.map (CommRingCat.ofHom (dblAwayMap1 k)) := by
  rw [dblToChart, ← Spec.map_comp, ← CommRingCat.ofHom_comp, includeLeft_dblRingMap_one,
    CommRingCat.ofHom_comp, Spec.map_comp]

lemma dblToChart_includeRight_one :
    dblToChart k 1 ≫ Spec.map (CommRingCat.ofHom (RingHomClass.toRingHom
        (Algebra.TensorProduct.includeRight (R := k) (A := chartRing k 1) (B := L k))))
      = Spec.map (CommRingCat.ofHom (RingHomClass.toRingHom
          (Algebra.TensorProduct.includeRight (R := k)
            (A := Away (Work.AbVar.ProjectiveLine.StdG k)
              (MvPolynomial.X 0 * MvPolynomial.X 1)) (B := L k)))) := by
  rw [dblToChart, ← Spec.map_comp, ← CommRingCat.ofHom_comp, includeRight_dblRingMap_one]

/-- The first projection of the double-chart inclusion. -/
lemma srcDoubleι_fst :
    srcDoubleι k ≫ pullback.fst (Work.AbVar.P1 k).hom (gmHom k)
      = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
          (R := k) (A := Away (Work.AbVar.ProjectiveLine.StdG k)
            (MvPolynomial.X 0 * MvPolynomial.X 1)) (B := L k)))
        ≫ srcDoubleObjHom k := by
  change ((srcDoubleIso k).inv ≫ srcDoubleMap k) ≫ pullback.fst (Work.AbVar.P1 k).hom (gmHom k) = _
  rw [Category.assoc, srcDoubleMap_fst, ← Category.assoc, srcDoubleIso_inv_fst]

/-- The second projection of the double-chart inclusion. -/
lemma srcDoubleι_snd :
    srcDoubleι k ≫ pullback.snd (Work.AbVar.P1 k).hom (gmHom k)
      = Spec.map (CommRingCat.ofHom (RingHomClass.toRingHom
          (Algebra.TensorProduct.includeRight (R := k)
            (A := Away (Work.AbVar.ProjectiveLine.StdG k)
              (MvPolynomial.X 0 * MvPolynomial.X 1)) (B := L k)))) := by
  change ((srcDoubleIso k).inv ≫ srcDoubleMap k) ≫ pullback.snd (Work.AbVar.P1 k).hom (gmHom k) = _
  rw [Category.assoc, srcDoubleMap_snd, srcDoubleIso_inv_snd]

lemma specMap_awayMap0_awayι :
    Spec.map (CommRingCat.ofHom (dblAwayMap0 k)) ≫ chartObjHom k 0
      = srcDoubleObjHom k :=
  Proj.SpecMap_awayMap_awayι (Work.AbVar.ProjectiveLine.StdG k)
    (Work.AbVar.ProjectiveLine.X_mem_stdG 0) (by norm_num)
    (Work.AbVar.ProjectiveLine.X_mem_stdG 1)
    (by
      show (MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) k)
        = MvPolynomial.X 0 * MvPolynomial.X 1
      rfl)

lemma specMap_awayMap1_awayι :
    Spec.map (CommRingCat.ofHom (dblAwayMap1 k)) ≫ chartObjHom k 1
      = srcDoubleObjHom k :=
  Proj.SpecMap_awayMap_awayι (Work.AbVar.ProjectiveLine.StdG k)
    (Work.AbVar.ProjectiveLine.X_mem_stdG 1) (by norm_num)
    (Work.AbVar.ProjectiveLine.X_mem_stdG 0)
    (by
      show (MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) k)
        = MvPolynomial.X 1 * MvPolynomial.X 0
      rw [mul_comm])

lemma dblToChart_ι_zero : dblToChart k 0 ≫ srcChartι k 0 = srcDoubleι k := by
  apply pullback.hom_ext (f := (Work.AbVar.P1 k).hom) (g := gmHom k)
  · rw [Category.assoc, srcChartι_fst, ← Category.assoc, dblToChart_includeLeft_zero,
      Category.assoc, specMap_awayMap0_awayι]
    exact (srcDoubleι_fst k).symm
  · rw [Category.assoc, srcChartι_snd, dblToChart_includeRight_zero]
    exact (srcDoubleι_snd k).symm

lemma dblToChart_ι_one : dblToChart k 1 ≫ srcChartι k 1 = srcDoubleι k := by
  apply pullback.hom_ext (f := (Work.AbVar.P1 k).hom) (g := gmHom k)
  · rw [Category.assoc, srcChartι_fst, ← Category.assoc, dblToChart_includeLeft_one,
      Category.assoc, specMap_awayMap1_awayι]
    exact (srcDoubleι_fst k).symm
  · rw [Category.assoc, srcChartι_snd, dblToChart_includeRight_one]
    exact (srcDoubleι_snd k).symm

/-! ## The affine comparison on the double chart -/

/-- The scaled chart map on the double chart ring. -/
noncomputable abbrev dblBeta (i : Fin 2) : chartRing k i →+* srcDoubleRing k :=
  (dblRingMap k i).comp (thetaRing k i)

lemma dblToChart_srcChartHom (i : Fin 2) :
    dblToChart k i ≫ srcChartHom k i
      = Spec.map (CommRingCat.ofHom (dblBeta k i)) ≫ chartObjHom k i := by
  change Spec.map (CommRingCat.ofHom (dblRingMap k i)) ≫
      (Spec.map (CommRingCat.ofHom (thetaRing k i)) ≫ chartObjHom k i) = _
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

lemma dblRingMap_base (i : Fin 2) (r : k) :
    dblRingMap k i (algebraMap k (srcChartRing k i) r) =
      algebraMap k (srcDoubleRing k) r := by
  fin_cases i
  · exact (Algebra.TensorProduct.map (dblMap0Hom k) (AlgHom.id k (L k))).commutes r
  · exact (Algebra.TensorProduct.map (dblMap1Hom k) (AlgHom.id k (L k))).commutes r

lemma dblAwayMap_awayU_mul :
    dblAwayMap0 k (Work.AbVar.ProjectiveLine.awayU (R := k) 0 1)
      * dblAwayMap1 k (Work.AbVar.ProjectiveLine.awayU (R := k) 1 0) = 1 := by
  apply HomogeneousLocalization.val_injective
    (Submonoid.powers (MvPolynomial.X 0 * MvPolynomial.X 1))
  rw [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_one]
  rw [show dblAwayMap0 k (Work.AbVar.ProjectiveLine.awayU (R := k) 0 1)
      = awayMap (Work.AbVar.ProjectiveLine.StdG k) (Work.AbVar.ProjectiveLine.X_mem_stdG 1) _
          (Work.AbVar.ProjectiveLine.awayU (R := k) 0 1) from rfl]
  rw [show dblAwayMap1 k (Work.AbVar.ProjectiveLine.awayU (R := k) 1 0)
      = awayMap (Work.AbVar.ProjectiveLine.StdG k) (Work.AbVar.ProjectiveLine.X_mem_stdG 0) _
          (Work.AbVar.ProjectiveLine.awayU (R := k) 1 0) from rfl]
  rw [show Work.AbVar.ProjectiveLine.awayU (R := k) 0 1
      = Away.mk (Work.AbVar.ProjectiveLine.StdG k) (Work.AbVar.ProjectiveLine.X_mem_stdG 0) 1
          (MvPolynomial.X 1) (by simpa using Work.AbVar.ProjectiveLine.X_mem_stdG 1) from rfl]
  rw [show Work.AbVar.ProjectiveLine.awayU (R := k) 1 0
      = Away.mk (Work.AbVar.ProjectiveLine.StdG k) (Work.AbVar.ProjectiveLine.X_mem_stdG 1) 1
          (MvPolynomial.X 0) (by simpa using Work.AbVar.ProjectiveLine.X_mem_stdG 0) from rfl]
  rw [awayMap_mk, awayMap_mk]
  simp only [Away.val_mk]
  rw [Localization.mk_mul, ← Localization.mk_one, Localization.mk_eq_mk_iff,
    Localization.r_iff_exists]
  refine ⟨⟨(MvPolynomial.X 0 * MvPolynomial.X 1) ^ 1, ⟨1, rfl⟩⟩, ?_⟩
  simp only [Submonoid.coe_mul, Submonoid.coe_one]
  ring

lemma dblAwayMap1_mul_dblAwayMap0 :
    dblAwayMap1 k (Work.AbVar.ProjectiveLine.awayU (R := k) 1 0)
      * dblAwayMap0 k (Work.AbVar.ProjectiveLine.awayU (R := k) 0 1) = 1 := by
  calc dblAwayMap1 k (Work.AbVar.ProjectiveLine.awayU (R := k) 1 0)
        * dblAwayMap0 k (Work.AbVar.ProjectiveLine.awayU (R := k) 0 1)
      = dblAwayMap0 k (Work.AbVar.ProjectiveLine.awayU (R := k) 0 1)
        * dblAwayMap1 k (Work.AbVar.ProjectiveLine.awayU (R := k) 1 0) := mul_comm _ _
    _ = 1 := dblAwayMap_awayU_mul k

/-- The value of `dblBeta k 0` on the chart coordinate. -/
lemma dblBeta_awayU_zero :
    dblBeta k 0 (Work.AbVar.ProjectiveLine.awayU (R := k) 0 1)
      = dblAwayMap0 k (Work.AbVar.ProjectiveLine.awayU (R := k) 0 1)
          ⊗ₜ[k] LaurentPolynomial.T (-1) := by
  show (dblRingMap k 0) (thetaRing k 0 (Work.AbVar.ProjectiveLine.awayU (R := k) 0 1)) = _
  rw [show thetaRing k 0 (Work.AbVar.ProjectiveLine.awayU (R := k) 0 1)
      = Work.AbVar.ProjectiveLine.awayU (R := k) 0 1 ⊗ₜ[k] LaurentPolynomial.T (-1) from by
    show (Polynomial.aeval (Work.AbVar.ProjectiveLine.awayU (R := k) 0 1
          ⊗ₜ[k] LaurentPolynomial.T (-1))).toRingHom
        ((Work.AbVar.ProjectiveLine.awayToPoly (R := k) 0)
          (Work.AbVar.ProjectiveLine.awayU (R := k) 0 1)) = _
    rw [← Work.AbVar.ProjectiveLine.polyToAway_X (R := k) (i := 0) (j := 1),
      Work.AbVar.ProjectiveLine.awayToPoly_awayU (R := k) (by decide : (1 : Fin 2) ≠ 0)]
    exact Polynomial.aeval_X _]
  rw [dblRingMap_zero_tmul]

/-- The value of `dblBeta k 1` on the chart coordinate. -/
lemma dblBeta_awayU_one :
    dblBeta k 1 (Work.AbVar.ProjectiveLine.awayU (R := k) 1 0)
      = dblAwayMap1 k (Work.AbVar.ProjectiveLine.awayU (R := k) 1 0)
          ⊗ₜ[k] LaurentPolynomial.T 1 := by
  show (dblRingMap k 1) (thetaRing k 1 (Work.AbVar.ProjectiveLine.awayU (R := k) 1 0)) = _
  rw [show thetaRing k 1 (Work.AbVar.ProjectiveLine.awayU (R := k) 1 0)
      = Work.AbVar.ProjectiveLine.awayU (R := k) 1 0 ⊗ₜ[k] LaurentPolynomial.T 1 from by
    show (Polynomial.aeval (Work.AbVar.ProjectiveLine.awayU (R := k) 1 0
          ⊗ₜ[k] LaurentPolynomial.T 1)).toRingHom
        ((Work.AbVar.ProjectiveLine.awayToPoly (R := k) 1)
          (Work.AbVar.ProjectiveLine.awayU (R := k) 1 0)) = _
    rw [← Work.AbVar.ProjectiveLine.polyToAway_X (R := k) (i := 1) (j := 0),
      Work.AbVar.ProjectiveLine.awayToPoly_awayU (R := k) (by decide : (0 : Fin 2) ≠ 1)]
    exact Polynomial.aeval_X _]
  rw [dblRingMap_one_tmul]

lemma dblAwayMap0_awayU_unit :
    IsUnit (dblAwayMap0 k (Work.AbVar.ProjectiveLine.awayU (R := k) 0 1)) :=
  isUnit_iff_exists_inv.mpr ⟨_, dblAwayMap_awayU_mul k⟩

lemma dblBeta_awayU_zero_unit :
    IsUnit (dblBeta k 0 (Away.isLocalizationElem (Work.AbVar.ProjectiveLine.X_mem_stdG 0)
      (Work.AbVar.ProjectiveLine.X_mem_stdG 1))) := by
  rw [show Away.isLocalizationElem (Work.AbVar.ProjectiveLine.X_mem_stdG 0)
        (Work.AbVar.ProjectiveLine.X_mem_stdG 1)
      = Work.AbVar.ProjectiveLine.awayU (R := k) 0 1 from by
    simp only [Away.isLocalizationElem, Work.AbVar.ProjectiveLine.awayU, pow_one]]
  rw [dblBeta_awayU_zero]
  rw [show dblAwayMap0 k (Work.AbVar.ProjectiveLine.awayU (R := k) 0 1)
        ⊗ₜ[k] LaurentPolynomial.T (-1)
      = (Algebra.TensorProduct.includeLeftRingHom (R := k)
            (A := Away (Work.AbVar.ProjectiveLine.StdG k)
              (MvPolynomial.X 0 * MvPolynomial.X 1)) (B := L k)
            (dblAwayMap0 k (Work.AbVar.ProjectiveLine.awayU (R := k) 0 1)))
        * (Algebra.TensorProduct.includeRight (R := k)
            (A := Away (Work.AbVar.ProjectiveLine.StdG k)
              (MvPolynomial.X 0 * MvPolynomial.X 1)) (B := L k)
            (LaurentPolynomial.T (-1))) from by
    rw [Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.TensorProduct.includeRight_apply,
      Algebra.TensorProduct.tmul_mul_tmul]
    simp]
  exact IsUnit.mul
    (IsUnit.map (Algebra.TensorProduct.includeLeftRingHom (R := k)
      (A := Away (Work.AbVar.ProjectiveLine.StdG k) (MvPolynomial.X 0 * MvPolynomial.X 1))
      (B := L k)) (dblAwayMap0_awayU_unit k))
    (IsUnit.map (Algebra.TensorProduct.includeRight (R := k)
      (A := Away (Work.AbVar.ProjectiveLine.StdG k) (MvPolynomial.X 0 * MvPolynomial.X 1))
      (B := L k)).toRingHom (LaurentPolynomial.isUnit_T (-1)))

lemma dblBeta_awayU_mul_one :
    dblBeta k 1 (Work.AbVar.ProjectiveLine.awayU (R := k) 1 0)
      * dblBeta k 0 (Work.AbVar.ProjectiveLine.awayU (R := k) 0 1) = 1 := by
  rw [dblBeta_awayU_zero, dblBeta_awayU_one, Algebra.TensorProduct.tmul_mul_tmul,
    dblAwayMap1_mul_dblAwayMap0]
  rw [show (LaurentPolynomial.T (1:ℤ)) * (LaurentPolynomial.T (-1)) = 1 from by
    rw [← LaurentPolynomial.T_add]; simp]
  rw [← Algebra.TensorProduct.one_def]

lemma dblBeta_apply (i : Fin 2) (x : chartRing k i) :
    dblBeta k i x = dblRingMap k i (thetaRing k i x) := rfl

/-- Two ring homomorphisms out of a chart ring of `ℙ¹` agree as soon as they agree on the
base and on the coordinate `x_j/x_i`. -/
lemma away_ringHom_ext {B : Type*} [CommRing B] {i j : Fin 2} (hij : j ≠ i)
    (φ ψ : Away (Work.AbVar.ProjectiveLine.StdG k) (MvPolynomial.X i) →+* B)
    (hbase : ∀ c : k, φ (algebraMap k (Away (Work.AbVar.ProjectiveLine.StdG k)
        (MvPolynomial.X i)) c) = ψ (algebraMap k _ c))
    (hgen : φ (Work.AbVar.ProjectiveLine.awayU (R := k) i j)
      = ψ (Work.AbVar.ProjectiveLine.awayU (R := k) i j)) : φ = ψ := by
  have hpol : φ.comp (Work.AbVar.ProjectiveLine.polyToAway (R := k) i j).toRingHom
      = ψ.comp (Work.AbVar.ProjectiveLine.polyToAway (R := k) i j).toRingHom := by
    apply Polynomial.ringHom_ext
    · intro r
      show φ (Work.AbVar.ProjectiveLine.polyToAway (R := k) i j (Polynomial.C r))
        = ψ (Work.AbVar.ProjectiveLine.polyToAway (R := k) i j (Polynomial.C r))
      rw [Work.AbVar.ProjectiveLine.polyToAway_C]
      exact hbase r
    · show φ (Work.AbVar.ProjectiveLine.polyToAway (R := k) i j Polynomial.X)
        = ψ (Work.AbVar.ProjectiveLine.polyToAway (R := k) i j Polynomial.X)
      rw [Work.AbVar.ProjectiveLine.polyToAway_X]
      exact hgen
  apply RingHom.ext
  intro x
  obtain ⟨P, rfl⟩ := Work.AbVar.ProjectiveLine.awaySurjective (R := k) hij x
  exact RingHom.congr_fun hpol P

theorem dblChartHom_compat :
    dblToChart k 0 ≫ srcChartHom k 0 = dblToChart k 1 ≫ srcChartHom k 1 := by
  rw [dblToChart_srcChartHom, dblToChart_srcChartHom]
  letI : Algebra (chartRing k 0) (Away (Work.AbVar.ProjectiveLine.StdG k)
      (MvPolynomial.X 0 * MvPolynomial.X 1)) := (dblAwayMap0 k).toAlgebra
  haveI hloc : IsLocalization.Away (Away.isLocalizationElem
      (Work.AbVar.ProjectiveLine.X_mem_stdG 0) (Work.AbVar.ProjectiveLine.X_mem_stdG 1))
      (Away (Work.AbVar.ProjectiveLine.StdG k) (MvPolynomial.X 0 * MvPolynomial.X 1)) :=
    Away.isLocalization_mul (Work.AbVar.ProjectiveLine.X_mem_stdG 0)
      (Work.AbVar.ProjectiveLine.X_mem_stdG 1) rfl (by norm_num)
  let lam : Away (Work.AbVar.ProjectiveLine.StdG k) (MvPolynomial.X 0 * MvPolynomial.X 1)
      →+* srcDoubleRing k :=
    IsLocalization.Away.lift
      (S := Away (Work.AbVar.ProjectiveLine.StdG k) (MvPolynomial.X 0 * MvPolynomial.X 1))
      (Away.isLocalizationElem (Work.AbVar.ProjectiveLine.X_mem_stdG 0)
        (Work.AbVar.ProjectiveLine.X_mem_stdG 1)) (dblBeta_awayU_zero_unit k)
  have hlam0 : lam.comp (dblAwayMap0 k) = dblBeta k 0 :=
    IsLocalization.Away.lift_comp
      (S := Away (Work.AbVar.ProjectiveLine.StdG k) (MvPolynomial.X 0 * MvPolynomial.X 1))
      (Away.isLocalizationElem (Work.AbVar.ProjectiveLine.X_mem_stdG 0)
        (Work.AbVar.ProjectiveLine.X_mem_stdG 1))
      (dblBeta_awayU_zero_unit k)
  have hlam1 : lam.comp (dblAwayMap1 k) = dblBeta k 1 := by
    refine away_ringHom_ext (k := k) (i := 1) (j := 0) (hij := by decide)
      (φ := lam.comp (dblAwayMap1 k)) (ψ := dblBeta k 1) ?_ ?_
    · intro c
      show lam (dblAwayMap1 k (algebraMap k (chartRing k 1) c))
        = dblBeta k 1 (algebraMap k (chartRing k 1) c)
      rw [dblAwayMap1_base, ← dblAwayMap0_base, ← RingHom.comp_apply, hlam0]
      rw [dblBeta_apply, thetaRing_algebraMap, dblRingMap_base, dblBeta_apply,
        thetaRing_algebraMap, dblRingMap_base]
    · show lam (dblAwayMap1 k (Work.AbVar.ProjectiveLine.awayU (R := k) 1 0))
        = dblBeta k 1 (Work.AbVar.ProjectiveLine.awayU (R := k) 1 0)
      have h1 : lam (dblAwayMap1 k (Work.AbVar.ProjectiveLine.awayU (R := k) 1 0))
          * dblBeta k 0 (Work.AbVar.ProjectiveLine.awayU (R := k) 0 1) = 1 := by
        rw [← hlam0, RingHom.comp_apply, ← RingHom.map_mul, dblAwayMap1_mul_dblAwayMap0,
          map_one]
      calc lam (dblAwayMap1 k (Work.AbVar.ProjectiveLine.awayU (R := k) 1 0))
          = lam (dblAwayMap1 k (Work.AbVar.ProjectiveLine.awayU (R := k) 1 0))
              * (dblBeta k 1 (Work.AbVar.ProjectiveLine.awayU (R := k) 1 0)
                * dblBeta k 0 (Work.AbVar.ProjectiveLine.awayU (R := k) 0 1)) := by
            rw [dblBeta_awayU_mul_one, _root_.mul_one]
        _ = (lam (dblAwayMap1 k (Work.AbVar.ProjectiveLine.awayU (R := k) 1 0))
              * dblBeta k 0 (Work.AbVar.ProjectiveLine.awayU (R := k) 0 1))
              * dblBeta k 1 (Work.AbVar.ProjectiveLine.awayU (R := k) 1 0) := by ring
        _ = 1 * dblBeta k 1 (Work.AbVar.ProjectiveLine.awayU (R := k) 1 0) := by rw [h1]
        _ = dblBeta k 1 (Work.AbVar.ProjectiveLine.awayU (R := k) 1 0) := by
            rw [_root_.one_mul]
  have hgoal0 : Spec.map (CommRingCat.ofHom (dblBeta k 0)) ≫ chartObjHom k 0
      = Spec.map (CommRingCat.ofHom lam) ≫ srcDoubleObjHom k := by
    rw [← specMap_awayMap0_awayι, ← Category.assoc, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, hlam0]
  have hgoal1 : Spec.map (CommRingCat.ofHom (dblBeta k 1)) ≫ chartObjHom k 1
      = Spec.map (CommRingCat.ofHom lam) ≫ srcDoubleObjHom k := by
    rw [← specMap_awayMap1_awayι, ← Category.assoc, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, hlam1]
  rw [hgoal0, hgoal1]

theorem srcCover_overlap (k : Type*) [Field k] :
    CategoryTheory.CategoryStruct.comp
        (CategoryTheory.Limits.pullback.fst (Work.AbVar.P1Action.srcChartι k 0)
          (Work.AbVar.P1Action.srcChartι k 1))
        (Work.AbVar.P1Action.srcChartHom k 0)
      = CategoryTheory.CategoryStruct.comp
        (CategoryTheory.Limits.pullback.snd (Work.AbVar.P1Action.srcChartι k 0)
          (Work.AbVar.P1Action.srcChartι k 1))
        (Work.AbVar.P1Action.srcChartHom k 1) := by
  have key : dblToChart k 0 ≫ srcChartHom k 0 = dblToChart k 1 ≫ srcChartHom k 1 :=
    dblChartHom_compat k
  have hfst : (srcOverlapIso k).hom ≫ dblToChart k 0
      = pullback.fst (srcChartι k 0) (srcChartι k 1) := by
    apply (cancel_mono (srcChartι k 0)).mp
    rw [Category.assoc, dblToChart_ι_zero]
    exact IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have hsnd : (srcOverlapIso k).hom ≫ dblToChart k 1
      = pullback.snd (srcChartι k 0) (srcChartι k 1) := by
    apply (cancel_mono (srcChartι k 1)).mp
    rw [Category.assoc, dblToChart_ι_one, ← pullback.condition]
    exact IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  calc pullback.fst (srcChartι k 0) (srcChartι k 1) ≫ srcChartHom k 0
      = ((srcOverlapIso k).hom ≫ dblToChart k 0) ≫ srcChartHom k 0 := by rw [hfst]
    _ = (srcOverlapIso k).hom ≫ (dblToChart k 0 ≫ srcChartHom k 0) := Category.assoc _ _ _
    _ = (srcOverlapIso k).hom ≫ (dblToChart k 1 ≫ srcChartHom k 1) := by rw [key]
    _ = ((srcOverlapIso k).hom ≫ dblToChart k 1) ≫ srcChartHom k 1 :=
        (Category.assoc _ _ _).symm
    _ = pullback.snd (srcChartι k 0) (srcChartι k 1) ≫ srcChartHom k 1 := by rw [hsnd]

end

end Work.AbVar.P1Action
