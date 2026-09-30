import Mathlib
import Submission.Work.AbVar.Basic
import Submission.Work.AbVar.ProjectiveLine
import Submission.Work.AbVar.ProjectiveLine.chart
import Submission.Work.AbVar.ProjectiveLine.awayTensorIsDomain

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.AbVar.ProjectiveLine
open CategoryTheory Limits AlgebraicGeometry
open scoped AlgebraicGeometry
noncomputable section
universe u

variable {k : Type u} [Field k]

lemma p1_X_mem (k : Type u) [Field k] (i : Fin 2) :
    (MvPolynomial.X i : MvPolynomial (Fin 2) k) ∈ P1Grading k 1 :=
  (MvPolynomial.mem_homogeneousSubmodule 1 _).mpr (MvPolynomial.isHomogeneous_X k i)

abbrev ChartRing (k : Type u) [Field k] (i : Fin 2) : Type u :=
  HomogeneousLocalization (P1Grading k)
    (Submonoid.powers (MvPolynomial.X i : MvPolynomial (Fin 2) k))

abbrev chartImm (k : Type u) [Field k] (i : Fin 2) : Spec ↧(ChartRing k i) ⟶ Proj (P1Grading k) :=
  Proj.awayι (P1Grading k) (MvPolynomial.X i) (p1_X_mem k i) one_pos

abbrev specK (k : Type u) [Field k] (K : Type u) [Field K] [Algebra ↥(P1Grading k 0) K] :
    Spec (.of K) ⟶ Spec (.of ↥(P1Grading k 0)) :=
  Spec.map (CommRingCat.ofHom (algebraMap ↥(P1Grading k 0) K))

abbrev bigPullback (k : Type u) [Field k] (K : Type u) [Field K] [Algebra ↥(P1Grading k 0) K] :
    Scheme :=
  pullback (Proj.toSpecZero (P1Grading k)) (specK k K)

abbrev fstMap (k : Type u) [Field k] (K : Type u) [Field K] [Algebra ↥(P1Grading k 0) K] :
    bigPullback k K ⟶ Proj (P1Grading k) :=
  pullback.fst (Proj.toSpecZero (P1Grading k)) (specK k K)

abbrev chartPiece (k : Type u) [Field k] (K : Type u) [Field K] [Algebra ↥(P1Grading k 0) K]
    (i : Fin 2) : Scheme :=
  pullback (chartImm k i) (fstMap k K)

abbrev pieceSnd (k : Type u) [Field k] (K : Type u) [Field K] [Algebra ↥(P1Grading k 0) K]
    (i : Fin 2) : chartPiece k K i ⟶ bigPullback k K :=
  pullback.snd (chartImm k i) (fstMap k K)

/-- The generic point `(0)` of `Proj k[X₀,X₁]`. -/
def p1ZeroPoint (k : Type u) [Field k] : Proj (P1Grading k) :=
  { asHomogeneousIdeal := ⊥
    isPrime := by
      show (⊥ : Ideal (MvPolynomial (Fin 2) k)).IsPrime
      infer_instance
    not_irrelevant_le := by
      intro h
      have hX : (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) ∈ P1Grading k 1 := p1_X_mem k 0
      have hmem : (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) ∈
          (⊥ : HomogeneousIdeal (P1Grading k)) :=
        h (HomogeneousIdeal.mem_irrelevant_of_mem (P1Grading k) (by norm_num) hX)
      have h2 : (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) ∈
          (⊥ : HomogeneousIdeal (P1Grading k)).toIdeal := HomogeneousIdeal.mem_iff.mpr hmem
      rw [HomogeneousIdeal.toIdeal_bot] at h2
      exact MvPolynomial.X_ne_zero 0 (Ideal.mem_bot.mp h2) }

lemma p1ZeroPoint_mem (k : Type u) [Field k] (i : Fin 2) :
    p1ZeroPoint k ∈ (Proj.basicOpen (P1Grading k) (MvPolynomial.X i) :
      Set (Proj (P1Grading k))) := by
  change (MvPolynomial.X i : MvPolynomial (Fin 2) k) ∉ (⊥ : HomogeneousIdeal (P1Grading k))
  intro h
  have h2 : (MvPolynomial.X i : MvPolynomial (Fin 2) k) ∈
      (⊥ : HomogeneousIdeal (P1Grading k)).toIdeal := HomogeneousIdeal.mem_iff.mpr h
  rw [HomogeneousIdeal.toIdeal_bot] at h2
  exact MvPolynomial.X_ne_zero i (Ideal.mem_bot.mp h2)

lemma p1_basicOpen_inf_nonempty (k : Type u) [Field k] :
    ((Proj.basicOpen (P1Grading k) (MvPolynomial.X 0) ⊓
      Proj.basicOpen (P1Grading k) (MvPolynomial.X 1) : (Proj (P1Grading k)).Opens) :
      Set (Proj (P1Grading k))).Nonempty := by
  refine ⟨p1ZeroPoint k, ?_⟩
  have h : p1ZeroPoint k ∈ (Proj.basicOpen (P1Grading k) (MvPolynomial.X 0) :
        Set (Proj (P1Grading k))) ∧
      p1ZeroPoint k ∈ (Proj.basicOpen (P1Grading k) (MvPolynomial.X 1) :
        Set (Proj (P1Grading k))) :=
    ⟨p1ZeroPoint_mem k 0, p1ZeroPoint_mem k 1⟩
  simpa only [TopologicalSpace.Opens.coe_inf, Set.mem_inter_iff] using h

lemma p1_adjoin_X_eq_top (k : Type u) [Field k] :
    Algebra.adjoin ↥(P1Grading k 0)
      (Set.range fun i : Fin 2 => (MvPolynomial.X i : MvPolynomial (Fin 2) k)) = ⊤ := by
  rw [eq_top_iff]
  intro p _
  refine MvPolynomial.induction_on p (fun a => ?_) (fun p q hp hq => ?_) (fun p i hp => ?_)
  · have hC : (MvPolynomial.C a : MvPolynomial (Fin 2) k) ∈ P1Grading k 0 :=
      (MvPolynomial.mem_homogeneousSubmodule 0 _).mpr (MvPolynomial.isHomogeneous_C (Fin 2) a)
    have h := (Algebra.adjoin ↥(P1Grading k 0)
      (Set.range fun i : Fin 2 => (MvPolynomial.X i : MvPolynomial (Fin 2) k))).algebraMap_mem
      ⟨MvPolynomial.C a, hC⟩
    simpa using h
  · exact add_mem hp hq
  · exact mul_mem hp (Algebra.subset_adjoin ⟨i, rfl⟩)

lemma p1_basicOpen_sup_eq_top (k : Type u) [Field k] :
    Proj.basicOpen (P1Grading k) (MvPolynomial.X 0) ⊔
      Proj.basicOpen (P1Grading k) (MvPolynomial.X 1) = ⊤ := by
  have hiSup : (⨆ i : Fin 2, Proj.basicOpen (P1Grading k) (MvPolynomial.X i)) = ⊤ :=
    Proj.iSup_basicOpen_eq_top' (P1Grading k) (fun i : Fin 2 => MvPolynomial.X i)
      (fun i => ⟨1, p1_X_mem k i⟩) (p1_adjoin_X_eq_top k)
  have h : (⨆ i : Fin 2, Proj.basicOpen (P1Grading k) (MvPolynomial.X i)) =
      Proj.basicOpen (P1Grading k) (MvPolynomial.X 0) ⊔
        Proj.basicOpen (P1Grading k) (MvPolynomial.X 1) := by
    refine le_antisymm (iSup_le fun i => ?_) (sup_le ?_ ?_)
    · fin_cases i
      · exact le_sup_left
      · exact le_sup_right
    · exact le_iSup (fun i : Fin 2 => Proj.basicOpen (P1Grading k) (MvPolynomial.X i)) 0
    · exact le_iSup (fun i : Fin 2 => Proj.basicOpen (P1Grading k) (MvPolynomial.X i)) 1
  rw [← h]; exact hiSup


section Topology

variable {X : Type*} [TopologicalSpace X]

lemma isPreirreducible_union_of_isOpen {s t : Set X}
    (hs : IsPreirreducible s) (ht : IsPreirreducible t) (hso : IsOpen s) (hto : IsOpen t)
    (hne : (s ∩ t).Nonempty) : IsPreirreducible (s ∪ t) := by
  intro u v hu hv hu' hv'
  obtain ⟨x, hxst, hxu⟩ := hu'
  obtain ⟨y, hyst, hyv⟩ := hv'
  have hne_ts : (t ∩ s).Nonempty := hne.mono fun z hz => ⟨hz.2, hz.1⟩
  rcases hxst with hxs | hxt
  · by_cases hsv : (s ∩ v).Nonempty
    · obtain ⟨z, hzs, hzu, hzv⟩ := hs u v hu hv ⟨x, hxs, hxu⟩ hsv
      exact ⟨z, Or.inl hzs, hzu, hzv⟩
    · have hyt : y ∈ t := by
        rcases hyst with hys | hyt
        · exact absurd ⟨y, hys, hyv⟩ hsv
        · exact hyt
      have htu : (t ∩ u).Nonempty := by
        obtain ⟨z, -, hzt, hzu⟩ := hs t u hto hu hne ⟨x, hxs, hxu⟩
        exact ⟨z, hzt, hzu⟩
      obtain ⟨z, hzt, hzu, hzv⟩ := ht u v hu hv htu ⟨y, hyt, hyv⟩
      exact ⟨z, Or.inr hzt, hzu, hzv⟩
  · by_cases htv : (t ∩ v).Nonempty
    · obtain ⟨z, hzt, hzu, hzv⟩ := ht u v hu hv ⟨x, hxt, hxu⟩ htv
      exact ⟨z, Or.inr hzt, hzu, hzv⟩
    · have hys : y ∈ s := by
        rcases hyst with hys | hyt
        · exact hys
        · exact absurd ⟨y, hyt, hyv⟩ htv
      have hsu : (s ∩ u).Nonempty := by
        obtain ⟨z, -, hzs, hzu⟩ := ht s u hso hu hne_ts ⟨x, hxt, hxu⟩
        exact ⟨z, hzs, hzu⟩
      obtain ⟨z, hzs, hzu, hzv⟩ := hs u v hu hv hsu ⟨y, hys, hyv⟩
      exact ⟨z, Or.inl hzs, hzu, hzv⟩

lemma isIrreducible_union_of_isOpen {s t : Set X}
    (hs : IsIrreducible s) (ht : IsIrreducible t) (hso : IsOpen s) (hto : IsOpen t)
    (hne : (s ∩ t).Nonempty) : IsIrreducible (s ∪ t) :=
  ⟨hs.1.inl, isPreirreducible_union_of_isOpen hs.2 ht.2 hso hto hne⟩

end Topology

theorem subsingleton_spec_zero (k : Type u) [Field k] :
    Subsingleton (Spec (CommRingCat.of ↥(P1Grading k 0))) := by
  haveI : Subsingleton ↥(Spec (CommRingCat.of k)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum k))
  let e : Spec (CommRingCat.of ↥(P1Grading k 0)) ≅ Spec (CommRingCat.of k) :=
    Scheme.Spec.mapIso ((p1BaseEquiv k).toCommRingCatIso).op
  have h : Function.Injective
      (e.hom.homeomorph : ↥(Spec (CommRingCat.of ↥(P1Grading k 0))) → _) :=
    e.hom.homeomorph.injective
  exact ⟨fun x y => h (Subsingleton.elim _ _)⟩

theorem chart_tensor_isDomain (k : Type u) [Field k] (K : Type u) [Field K]
    [Algebra ↥(P1Grading k 0) K] (i : Fin 2) :
    IsDomain (TensorProduct ↥(P1Grading k 0) (ChartRing k i) K) :=
  awayTensorIsDomain k i K

theorem irreducible_chart_piece (k : Type u) [Field k] (K : Type u) [Field K]
    [Algebra ↥(P1Grading k 0) K] (i : Fin 2) :
    IrreducibleSpace (chartPiece k K i) := by
  have h1 : IsPullback (pullback.fst (chartImm k i) (fstMap k K))
      (pullback.snd (chartImm k i) (fstMap k K)) (chartImm k i) (fstMap k K) :=
    IsPullback.of_hasPullback _ _
  have h2 : IsPullback (fstMap k K) (pullback.snd (Proj.toSpecZero (P1Grading k)) (specK k K))
      (Proj.toSpecZero (P1Grading k)) (specK k K) := IsPullback.of_hasPullback _ _
  have h3 := h1.paste_vert h2
  rw [chartImm, Proj.awayι_toSpecZero, ← HomogeneousLocalization.algebraMap_eq] at h3
  let W : Scheme := pullback (Spec.map (CommRingCat.ofHom (algebraMap ↥(P1Grading k 0)
      (ChartRing k i)))) (specK k K)
  haveI : IrreducibleSpace W := by
    haveI hdom : IsDomain (TensorProduct ↥(P1Grading k 0) (ChartRing k i) K) :=
      chart_tensor_isDomain k K i
    haveI : IsDomain (CommRingCat.of (TensorProduct ↥(P1Grading k 0) (ChartRing k i) K)) :=
      inferInstanceAs (IsDomain (TensorProduct ↥(P1Grading k 0) (ChartRing k i) K))
    haveI : IrreducibleSpace (Spec (CommRingCat.of (TensorProduct ↥(P1Grading k 0) (ChartRing k i) K))) :=
      inferInstance
    exact (pullbackSpecIso ↥(P1Grading k 0) (ChartRing k i)
      K).symm.hom.homeomorph.irreducibleSpace_iff.mp inferInstance
  exact h3.isoPullback.hom.homeomorph.irreducibleSpace_iff.mpr inferInstance

theorem irreducible_bigPullback (k : Type u) [Field k] (K : Type u) [Field K]
    [Algebra ↥(P1Grading k 0) K] : IrreducibleSpace (bigPullback k K) := by
  haveI : Subsingleton (Spec (CommRingCat.of ↥(P1Grading k 0))) := subsingleton_spec_zero k
  haveI hy : Surjective (specK k K) := ⟨fun x => ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩⟩
  haveI hfst : Surjective (fstMap k K) := inferInstance
  have hrange (i : Fin 2) : Set.range (pieceSnd k K i) =
      (fstMap k K) ⁻¹' (↑(Proj.basicOpen (P1Grading k) (MvPolynomial.X i)) :
        Set (Proj (P1Grading k))) := by
    rw [← Scheme.Hom.coe_opensRange (pieceSnd k K i)]
    rw [Scheme.Hom.opensRange_pullbackSnd]
    rw [show Scheme.Hom.opensRange (chartImm k i) =
        Proj.basicOpen (P1Grading k) (MvPolynomial.X i) from
      Proj.opensRange_awayι (P1Grading k) (MvPolynomial.X i) (p1_X_mem k i) one_pos]
    exact TopologicalSpace.Opens.map_coe _ _
  have hpiece (i : Fin 2) : IsIrreducible (Set.range (pieceSnd k K i)) := by
    haveI : IrreducibleSpace (chartPiece k K i) := irreducible_chart_piece k K i
    let U : (bigPullback k K).Opens := Scheme.Hom.opensRange (pieceSnd k K i)
    haveI hU : IrreducibleSpace U.toScheme := by
      have e : chartPiece k K i ≅ U.toScheme :=
        IsOpenImmersion.isoOfRangeEq (pieceSnd k K i) U.ι (by
          rw [Scheme.Opens.range_ι, Scheme.Hom.coe_opensRange])
      exact e.hom.homeomorph.irreducibleSpace_iff.mp inferInstance
    rw [show Set.range (pieceSnd k K i) = ↑U from (Scheme.Hom.coe_opensRange _).symm,
      isIrreducible_iff_irreducibleSpace]
    exact hU
  have hcover : Set.range (pieceSnd k K 0) ∪ Set.range (pieceSnd k K 1) = Set.univ := by
    rw [hrange 0, hrange 1, ← Set.preimage_union]
    have htop : (↑(Proj.basicOpen (P1Grading k) (MvPolynomial.X 0)) : Set (Proj (P1Grading k))) ∪
        ↑(Proj.basicOpen (P1Grading k) (MvPolynomial.X 1)) = Set.univ := by
      rw [← TopologicalSpace.Opens.coe_sup, p1_basicOpen_sup_eq_top]
      rfl
    rw [htop]
    simp
  have hinter : (Set.range (pieceSnd k K 0) ∩ Set.range (pieceSnd k K 1)).Nonempty := by
    rw [hrange 0, hrange 1, ← Set.preimage_inter]
    obtain ⟨x, hx⟩ := p1_basicOpen_inf_nonempty k
    have hx' : x ∈ (↑(Proj.basicOpen (P1Grading k) (MvPolynomial.X 0)) :
        Set (Proj (P1Grading k))) ∩ ↑(Proj.basicOpen (P1Grading k) (MvPolynomial.X 1)) := by
      simpa only [TopologicalSpace.Opens.coe_inf] using hx
    obtain ⟨z, hz⟩ := hfst.surj x
    exact ⟨z, by rw [Set.mem_preimage, hz]; exact hx'⟩
  have hopen (i : Fin 2) : IsOpen (Set.range (pieceSnd k K i)) := by
    rw [← Scheme.Hom.coe_opensRange (pieceSnd k K i)]
    exact (Scheme.Hom.opensRange (pieceSnd k K i)).isOpen
  rw [irreducibleSpace_def]
  rw [show (⊤ : Set (bigPullback k K)) =
      Set.range (pieceSnd k K 0) ∪ Set.range (pieceSnd k K 1) from hcover.symm]
  exact isIrreducible_union_of_isOpen (hpiece 0) (hpiece 1) (hopen 0) (hopen 1) hinter


theorem geometricallyIrreducible_toSpecZero (k : Type u) [Field k] :
    GeometricallyIrreducible (Proj.toSpecZero (P1Grading k)) := by
  rw [GeometricallyIrreducible.eq_geometrically,
    geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
  intro K _ _
  exact irreducible_bigPullback k K

open CategoryTheory in
theorem geometricallyIrreducible {k : Type*} [Field k] :
    AlgebraicGeometry.GeometricallyIrreducible (Work.AbVar.P1 k).hom := by
  haveI hiso : IsIso (Spec.map (CommRingCat.ofHom (p1BaseEquiv k).toRingHom)) := by
    rw [show Spec.map (CommRingCat.ofHom (p1BaseEquiv k).toRingHom) =
        (Scheme.Spec.mapIso ((p1BaseEquiv k).toCommRingCatIso).op).hom from rfl]
    infer_instance
  rw [p1_hom]
  refine ⟨?_⟩
  exact MorphismProperty.RespectsIso.postcomp (AlgebraicGeometry.geometrically
    fun X : Scheme => IrreducibleSpace X)
    (Spec.map (CommRingCat.ofHom (p1BaseEquiv k).toRingHom)) (Proj.toSpecZero (P1Grading k))
    (geometricallyIrreducible_toSpecZero k).geometrically_irreducibleSpace

end
end Work.AbVar.ProjectiveLine
