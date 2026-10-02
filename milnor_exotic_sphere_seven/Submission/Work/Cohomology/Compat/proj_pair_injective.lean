import Mathlib
import Submission.Work.Cohomology.Compat.prodSphereDefs
import Submission.Work.Cohomology.Compat.prodSphereAux
import Submission.Work.Cohomology.Compat.homotopyEquiv_A1set
import Submission.Work.Cohomology.Compat.homotopyEquiv_B1set
import Submission.Work.Cohomology.Compat.contractible_A1set_inter_B1set
import Submission.Work.Cohomology.mvLeft_zero_injective
import Submission.Work.Cohomology.sphereHomologyTop
import Submission.Work.Cohomology.excisionAux
import Submission.Work.Cohomology.Compat.proj2A1_injective
import Submission.Work.Cohomology.Compat.proj1B1_injective
import Submission.Work.Cohomology.Compat.homologyMap_eq_zero_of_avoiding_sphN

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology Limits
namespace Work.Cohomology.Compat
noncomputable section

abbrev Yt (p q : ℕ) : TopCat := TopCat.of ↥(Yset p q)
abbrev A1t (p q : ℕ) : TopCat := TopCat.of ↥(A1set p q)
abbrev B1t (p q : ℕ) : TopCat := TopCat.of ↥(B1set p q)

-- the chain complexes
abbrev ChA1 (p q : ℕ) : ChainComplex (ModuleCat ℤ) ℕ := singularChains ℤ (A1t p q)
abbrev ChB1 (p q : ℕ) : ChainComplex (ModuleCat ℤ) ℕ := singularChains ℤ (B1t p q)
abbrev ChY (p q : ℕ) : ChainComplex (ModuleCat ℤ) ℕ := singularChains ℤ (Yt p q)
abbrev ChSp (p : ℕ) : ChainComplex (ModuleCat ℤ) ℕ := singularChains ℤ (sphTop (p+1))
abbrev ChSq (q : ℕ) : ChainComplex (ModuleCat ℤ) ℕ := singularChains ℤ (sphTop (q+1))

theorem isIso_mvRightX_of_contractible {X : TopCat} (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) [ContractibleSpace ↥(U ∩ V)] (n : ℕ) (hn : 1 ≤ n) :
    IsIso (mvRightX U V hU hV hcov n) := by
  haveI : IsIso (HomologicalComplex.homologyMap (mvRight U V) n) := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, (Nat.sub_add_cancel hn).symm⟩
    haveI hpath : PathConnectedSpace ↥(U ∩ V) := inferInstance
    haveI hzero : IsZero (HInter (X := X) U V (m + 1)) :=
      homologyContractible (X := TopCat.of ↥(U ∩ V)) (m + 1) (by omega)
    refine isIso_of_exact_of_zero_of_inj
      (f := HomologicalComplex.homologyMap (mvLeft U V) (m + 1))
      (g := HomologicalComplex.homologyMap (mvRight U V) (m + 1))
      (δ := mvδ U V m)
      (f' := HomologicalComplex.homologyMap (mvLeft U V) m) ?_ ?_ ?_ ?_ ?_
    · exact (ShortComplex.moduleCat_exact_iff_range_eq_ker _).1 (mv_H_exact₁ U V m)
    · exact (ShortComplex.moduleCat_exact_iff_range_eq_ker _).1 (mv_H_exact₂ U V (m + 1))
    · exact (ShortComplex.moduleCat_exact_iff_range_eq_ker _).1 (mv_H_exact₃ U V m)
    · exact IsZero.eq_zero_of_src hzero _
    · rcases m with _ | m
      · exact mvLeft_zero_injective U V
      · exact injective_of_isZero_src _
          (homologyContractible (X := TopCat.of ↥(U ∩ V)) (m + 1) (by omega))
  rw [mvRightX]
  infer_instance

theorem isIso_mvRightX_A1_B1 (p q n : ℕ) (hn : 1 ≤ n) :
    IsIso (mvRightX (X := Yt p q) (A1set p q) (B1set p q)
      (isOpen_A1set p q) (isOpen_B1set p q) (A1set_union_B1set p q) n) := by
  haveI : ContractibleSpace ↥(A1set p q ∩ B1set p q) := contractible_A1set_inter_B1set p q
  exact isIso_mvRightX_of_contractible _ _ _ _ _ n hn


-- the Mayer-Vietoris chain map C(A1) ⊞ C(B1) ⟶ C(Y)
abbrev MvC (p q : ℕ) : ChA1 p q ⊞ ChB1 p q ⟶ ChY p q :=
  mvRight (X := Yt p q) (A1set p q) (B1set p q)
    ≫ smallToSing (X := Yt p q) (A1set p q) (B1set p q)

abbrev proj1Ch (p q : ℕ) : ChY p q ⟶ ChSp p :=
  chainMap ℤ (Yt p q) (sphTop (p+1)) (proj₁Y p q)

abbrev proj2Ch (p q : ℕ) : ChY p q ⟶ ChSq q :=
  chainMap ℤ (Yt p q) (sphTop (q+1)) (proj₂Y p q)

abbrev alpha (p q n : ℕ) : (ChA1 p q).homology n ⟶ (ChSq q).homology n :=
  HomologicalComplex.homologyMap (chainMap ℤ (A1t p q) (sphTop (q+1)) (proj₂A1 p q)) n

abbrev beta (p q n : ℕ) : (ChB1 p q).homology n ⟶ (ChSp p).homology n :=
  HomologicalComplex.homologyMap (chainMap ℤ (B1t p q) (sphTop (p+1)) (proj₁B1 p q)) n

-- corners (from the previous test file)
lemma corner_inl (p q : ℕ) :
    biprod.inl (X := ChA1 p q) (Y := ChB1 p q) ≫ MvC p q
      = inclChains (Yt p q) (A1set p q) := by
  rw [show MvC p q = (biprod.desc (smallOfU (X := Yt p q) (A1set p q) (B1set p q))
      (-(smallOfV (X := Yt p q) (A1set p q) (B1set p q))))
        ≫ smallToSing (X := Yt p q) (A1set p q) (B1set p q) from rfl]
  rw [← Category.assoc, biprod.inl_desc]
  exact smallOfU_comp_smallToSing (X := Yt p q) (A1set p q) (B1set p q)

lemma corner_inr (p q : ℕ) :
    biprod.inr (X := ChA1 p q) (Y := ChB1 p q) ≫ MvC p q
      = -(inclChains (Yt p q) (B1set p q)) := by
  rw [show MvC p q = (biprod.desc (smallOfU (X := Yt p q) (A1set p q) (B1set p q))
      (-(smallOfV (X := Yt p q) (A1set p q) (B1set p q))))
        ≫ smallToSing (X := Yt p q) (A1set p q) (B1set p q) from rfl]
  rw [← Category.assoc, biprod.inr_desc]
  rw [Preadditive.neg_comp, smallOfV_comp_smallToSing]

-- the four homology level corners
lemma homCorner_11 (p q n : ℕ) (hn : 1 ≤ n) :
    HomologicalComplex.homologyMap (biprod.inl (X := ChA1 p q) (Y := ChB1 p q)) n
      ≫ HomologicalComplex.homologyMap (MvC p q ≫ proj1Ch p q) n = 0 := by
  rw [← HomologicalComplex.homologyMap_comp]
  rw [show biprod.inl (X := ChA1 p q) (Y := ChB1 p q) ≫ (MvC p q ≫ proj1Ch p q)
      = (biprod.inl (X := ChA1 p q) (Y := ChB1 p q) ≫ MvC p q) ≫ proj1Ch p q
      from (Category.assoc _ _ _).symm]
  rw [corner_inl]
  rw [show inclChains (Yt p q) (A1set p q) ≫ proj1Ch p q
      = chainMap ℤ (A1t p q) (sphTop (p+1))
          (subtypeIncl (Yt p q) (A1set p q) ≫ proj₁Y p q) from by
    rw [proj1Ch, inclChains, ← chainMap_comp']]
  exact homologyMap_eq_zero_of_avoiding_sphN (A1t p q) p n hn
      (subtypeIncl (Yt p q) (A1set p q) ≫ proj₁Y p q) (fun z => z.2)

lemma homCorner_12 (p q n : ℕ) (hn : 1 ≤ n) :
    HomologicalComplex.homologyMap (biprod.inr (X := ChA1 p q) (Y := ChB1 p q)) n
      ≫ HomologicalComplex.homologyMap (MvC p q ≫ proj1Ch p q) n
      = -(beta p q n) := by
  rw [← HomologicalComplex.homologyMap_comp]
  rw [show biprod.inr (X := ChA1 p q) (Y := ChB1 p q) ≫ (MvC p q ≫ proj1Ch p q)
      = (biprod.inr (X := ChA1 p q) (Y := ChB1 p q) ≫ MvC p q) ≫ proj1Ch p q
      from (Category.assoc _ _ _).symm]
  rw [corner_inr]
  rw [Preadditive.neg_comp, HomologicalComplex.homologyMap_neg]
  rw [show inclChains (Yt p q) (B1set p q) ≫ proj1Ch p q
      = chainMap ℤ (B1t p q) (sphTop (p+1)) (proj₁B1 p q) from by
    rw [proj1Ch, inclChains, chainMap_comp']
    congr 1]

lemma homCorner_21 (p q n : ℕ) (hn : 1 ≤ n) :
    HomologicalComplex.homologyMap (biprod.inl (X := ChA1 p q) (Y := ChB1 p q)) n
      ≫ HomologicalComplex.homologyMap (MvC p q ≫ proj2Ch p q) n = alpha p q n := by
  rw [← HomologicalComplex.homologyMap_comp]
  rw [show biprod.inl (X := ChA1 p q) (Y := ChB1 p q) ≫ (MvC p q ≫ proj2Ch p q)
      = (biprod.inl (X := ChA1 p q) (Y := ChB1 p q) ≫ MvC p q) ≫ proj2Ch p q
      from (Category.assoc _ _ _).symm]
  rw [corner_inl]
  rw [show inclChains (Yt p q) (A1set p q) ≫ proj2Ch p q
      = chainMap ℤ (A1t p q) (sphTop (q+1)) (proj₂A1 p q) from by
    rw [proj2Ch, inclChains, chainMap_comp']
    congr 1]

lemma homCorner_22 (p q n : ℕ) (hn : 1 ≤ n) :
    HomologicalComplex.homologyMap (biprod.inr (X := ChA1 p q) (Y := ChB1 p q)) n
      ≫ HomologicalComplex.homologyMap (MvC p q ≫ proj2Ch p q) n = 0 := by
  rw [← HomologicalComplex.homologyMap_comp]
  rw [show biprod.inr (X := ChA1 p q) (Y := ChB1 p q) ≫ (MvC p q ≫ proj2Ch p q)
      = (biprod.inr (X := ChA1 p q) (Y := ChB1 p q) ≫ MvC p q) ≫ proj2Ch p q
      from (Category.assoc _ _ _).symm]
  rw [corner_inr]
  rw [Preadditive.neg_comp, HomologicalComplex.homologyMap_neg]
  rw [show inclChains (Yt p q) (B1set p q) ≫ proj2Ch p q
      = chainMap ℤ (B1t p q) (sphTop (q+1))
          (subtypeIncl (Yt p q) (B1set p q) ≫ proj₂Y p q) from by
    rw [proj2Ch, inclChains, ← chainMap_comp']]
  rw [homologyMap_eq_zero_of_avoiding_sphN (B1t p q) q n hn
      (subtypeIncl (Yt p q) (B1set p q) ≫ proj₂Y p q) (fun z => z.2), neg_zero]

/-- If `f ≫ g` is injective and `f` is surjective then `g` is injective. -/
lemma injective_of_comp_injective_of_surjective {M N P : ModuleCat ℤ} (f : M ⟶ N) (g : N ⟶ P)
    (hfg : Function.Injective (f ≫ g).hom) (hf : Function.Surjective f.hom) :
    Function.Injective g.hom := by
  intro x y hxy
  obtain ⟨a, ha⟩ := hf x
  obtain ⟨b, hb⟩ := hf y
  have h : (f ≫ g).hom a = (f ≫ g).hom b := by
    rw [ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply, ha, hb, hxy]
  rw [← ha, ← hb, hfg h]

set_option profiler.threshold 1000 in
/-- The pair of the two projections `Hₙ(Sᵖ × Sᵍ \ {pt}) ⟶ Hₙ(Sᵖ) ⊞ Hₙ(Sᵍ)` is injective
(`n ≥ 1`, `p, q ≥ 1`).

Suggested route: the cover `A1set ∪ B1set = Yset` has contractible intersection, so by the
extraction lemma `isIso_of_exact_of_zero_of_inj` (in
`Submission/Work/Cohomology/prodSphereAux.lean`) applied to `mv_H_exact₁/₂/₃` the map
`mvRightX (A1set p q) (B1set p q) ... n` is an isomorphism `HBiprod n ≅ Hₙ(Yset p q)`; composing it
with the pair map and using `homologyMap_biprod_lift`, `smallOfU_comp_smallToSing`
(`Submission/Work/Cohomology/excisionAux.lean`), `biprod.inl_desc`/`biprod.inr_desc` (for `mvRight`)
and `chainMap_comp` identifies the composite with the block map `(a, b) ↦ (-β b, α a)`, where
`α : Hₙ(A1set) ≅ Hₙ(Sᵍ)` and `β : Hₙ(B1set) ≅ Hₙ(Sᵖ)` are induced by the two projections (the
off-diagonal entries vanish because those projections have image in the contractible set
`sphSet ∖ {sphN}`); the block map is injective as soon as `α`, `β` are, and these are injective
because a split epimorphism `M ⟶ ℤ` with `M ≅ ℤ` is injective (a surjection `ℤ ⟶ ℤ` is
multiplication by `±1`); `Hₙ(A1set) ≅ Hₙ(Sᵍ)` is available from `homotopyEquiv_A1set`
(`Submission/Work/Cohomology/homotopyEquiv_A1set.lean`) and `Hₙ(B1set) ≅ Hₙ(Sᵖ)` from
`homotopyEquiv_B1set`. -/
theorem proj_pair_injective (p q n : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hn : 1 ≤ n) :
    Function.Injective (CategoryTheory.Limits.biprod.lift
      (HomologicalComplex.homologyMap (chainMap ℤ (TopCat.of ↥(Yset p q)) (sphTop (p+1))
        (proj₁Y p q)) n)
      (HomologicalComplex.homologyMap (chainMap ℤ (TopCat.of ↥(Yset p q)) (sphTop (q+1))
        (proj₂Y p q)) n)).hom := by
  haveI hM : IsIso (HomologicalComplex.homologyMap (MvC p q) n) := by
    rw [show HomologicalComplex.homologyMap (MvC p q) n
        = mvRightX (X := Yt p q) (A1set p q) (B1set p q)
            (isOpen_A1set p q) (isOpen_B1set p q) (A1set_union_B1set p q) n from by
      rw [MvC, mvRightX, HomologicalComplex.homologyMap_comp]
      rfl]
    exact isIso_mvRightX_A1_B1 p q n hn
  have hQ : Function.Injective (HomologicalComplex.homologyMap (MvC p q) n
      ≫ biprod.lift (HomologicalComplex.homologyMap (proj1Ch p q) n)
          (HomologicalComplex.homologyMap (proj2Ch p q) n)).hom := by
    have hkey : ∀ z : ↥((ChA1 p q ⊞ ChB1 p q).homology n),
        (HomologicalComplex.homologyMap (MvC p q) n
          ≫ biprod.lift (HomologicalComplex.homologyMap (proj1Ch p q) n)
              (HomologicalComplex.homologyMap (proj2Ch p q) n)).hom z = 0 → z = 0 := by
      intro z hz
      set a : ↥((ChA1 p q).homology n) :=
        (HomologicalComplex.homologyMap (biprod.fst (X := ChA1 p q) (Y := ChB1 p q)) n).hom z
        with ha
      set b : ↥((ChB1 p q).homology n) :=
        (HomologicalComplex.homologyMap (biprod.snd (X := ChA1 p q) (Y := ChB1 p q)) n).hom z
        with hb
      have hdecomp : (HomologicalComplex.homologyMap
              (biprod.inl (X := ChA1 p q) (Y := ChB1 p q)) n).hom a
            + (HomologicalComplex.homologyMap
                (biprod.inr (X := ChA1 p q) (Y := ChB1 p q)) n).hom b = z := by
        have htot := congrArg (fun (g : (ChA1 p q ⊞ ChB1 p q).homology n
              ⟶ (ChA1 p q ⊞ ChB1 p q).homology n) => g.hom z)
          (homologyMap_total' (ChA1 p q) (ChB1 p q) n)
        simpa only [ModuleCat.hom_add, ModuleCat.hom_comp, LinearMap.add_apply,
          LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply, ha, hb] using htot
      have hfst : (HomologicalComplex.homologyMap (MvC p q) n
            ≫ biprod.lift (HomologicalComplex.homologyMap (proj1Ch p q) n)
                (HomologicalComplex.homologyMap (proj2Ch p q) n)) ≫ biprod.fst
          = HomologicalComplex.homologyMap (MvC p q ≫ proj1Ch p q) n := by
        rw [Category.assoc, biprod.lift_fst, ← HomologicalComplex.homologyMap_comp]
      have hsnd : (HomologicalComplex.homologyMap (MvC p q) n
            ≫ biprod.lift (HomologicalComplex.homologyMap (proj1Ch p q) n)
                (HomologicalComplex.homologyMap (proj2Ch p q) n)) ≫ biprod.snd
          = HomologicalComplex.homologyMap (MvC p q ≫ proj2Ch p q) n := by
        rw [Category.assoc, biprod.lift_snd, ← HomologicalComplex.homologyMap_comp]
      have hz1 : (HomologicalComplex.homologyMap (MvC p q ≫ proj1Ch p q) n).hom z = 0 := by
        rw [← hfst, ModuleCat.hom_comp, LinearMap.comp_apply, hz, map_zero]
      have hz2 : (HomologicalComplex.homologyMap (MvC p q ≫ proj2Ch p q) n).hom z = 0 := by
        rw [← hsnd, ModuleCat.hom_comp, LinearMap.comp_apply, hz, map_zero]
      have e1 : (HomologicalComplex.homologyMap (MvC p q ≫ proj1Ch p q) n).hom
          ((HomologicalComplex.homologyMap
            (biprod.inl (X := ChA1 p q) (Y := ChB1 p q)) n).hom a) = 0 := by
        have h := congrArg (fun (g : (ChA1 p q).homology n
            ⟶ (ChSp p).homology n) => g.hom a) (homCorner_11 p q n hn)
        simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
          LinearMap.zero_apply] using h
      have e2 : (HomologicalComplex.homologyMap (MvC p q ≫ proj1Ch p q) n).hom
          ((HomologicalComplex.homologyMap
            (biprod.inr (X := ChA1 p q) (Y := ChB1 p q)) n).hom b)
          = -(beta p q n).hom b := by
        have h := congrArg (fun (g : (ChB1 p q).homology n
            ⟶ (ChSp p).homology n) => g.hom b) (homCorner_12 p q n hn)
        simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_neg,
          LinearMap.neg_apply] using h
      have e3 : (HomologicalComplex.homologyMap (MvC p q ≫ proj2Ch p q) n).hom
          ((HomologicalComplex.homologyMap
            (biprod.inl (X := ChA1 p q) (Y := ChB1 p q)) n).hom a)
          = (alpha p q n).hom a := by
        have h := congrArg (fun (g : (ChA1 p q).homology n
            ⟶ (ChSq q).homology n) => g.hom a) (homCorner_21 p q n hn)
        simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h
      have e4 : (HomologicalComplex.homologyMap (MvC p q ≫ proj2Ch p q) n).hom
          ((HomologicalComplex.homologyMap
            (biprod.inr (X := ChA1 p q) (Y := ChB1 p q)) n).hom b) = 0 := by
        have h := congrArg (fun (g : (ChB1 p q).homology n
            ⟶ (ChSq q).homology n) => g.hom b) (homCorner_22 p q n hn)
        simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
          LinearMap.zero_apply] using h
      have hb0 : b = 0 := by
        have hmain : (HomologicalComplex.homologyMap (MvC p q ≫ proj1Ch p q) n).hom z
            = -(beta p q n).hom b := by
          rw [← hdecomp, map_add, e1, e2, zero_add]
        have hbeta : (beta p q n).hom b = 0 := neg_eq_zero.mp (hmain ▸ hz1)
        refine proj1B1_injective p q n hp hn ?_
        rw [hbeta, map_zero]
      have ha0 : a = 0 := by
        have hmain : (HomologicalComplex.homologyMap (MvC p q ≫ proj2Ch p q) n).hom z
            = (alpha p q n).hom a := by
          rw [← hdecomp, map_add, e3, e4, add_zero]
        have halpha : (alpha p q n).hom a = 0 := hmain ▸ hz2
        refine proj2A1_injective p q n hq hn ?_
        rw [halpha, map_zero]
      rw [← hdecomp, ha0, hb0]
      simp
    intro x y hxy
    have h0 : (HomologicalComplex.homologyMap (MvC p q) n
          ≫ biprod.lift (HomologicalComplex.homologyMap (proj1Ch p q) n)
              (HomologicalComplex.homologyMap (proj2Ch p q) n)).hom (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    exact sub_eq_zero.mp (hkey _ h0)
  have hMepi : Function.Surjective (HomologicalComplex.homologyMap (MvC p q) n).hom :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  exact injective_of_comp_injective_of_surjective _ _ hQ hMepi

end
end Work.Cohomology.Compat
