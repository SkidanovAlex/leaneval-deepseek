import Mathlib
import Submission.Work.ThomBordism.valuePmOneV2Defs
import Submission.Work.Tubular.PuncturedDiscPair.puncturedNormalPair_vanishing
import Submission.Work.ThomBordism.tubeRelChains_tubeInvPunct_nonzero
import Submission.Work.ThomBordism.tubeDiscRetract
import Submission.Work.Orient.Boundary.HalfVanishing

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

namespace Work.ThomBordism

open CategoryTheory

noncomputable section

/-- The tube inverse identifies the punctured tube pair `(C.U ∖ {pt}, tubeInvPunct)` with the
punctured disc-bundle pair, and the fibrewise radial capping identifies the latter with the
punctured normal pair `(ν ∖ {0_x}, ν ∖ 0)`; hence the two relative homology groups are isomorphic in
every degree. -/
theorem tubeRelChains_iso_puncturedNormalPair {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt]
    {k : ℕ} (hk : 1 ≤ k) (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) (x : V.pt) (n : ℕ) :
    Nonempty ((Work.Cohomology.relChains (TopCat.of ↥(Work.ThomBordism.tubePtSet E C x))
        {a : ↥(Work.ThomBordism.tubePtSet E C x) |
          (a : ↥C.U) ∈ Work.ThomBordism.tubeInvPunct E C}).homology n ≅
      (Work.Cohomology.relChains (TopCat.of (Work.Tubular.PuncturedDiscPair.Punct E x))
        (Work.Tubular.PuncturedDiscPair.PunctRel E x)).homology n) := by
  classical
  have hε : 0 < ε := C.eps_pos
  let X₁ : TopCat := TopCat.of ↥(Work.ThomBordism.tubePtSet E C x)
  let A₁ : Set ↥(Work.ThomBordism.tubePtSet E C x) :=
    {a | (a : ↥C.U) ∈ Work.ThomBordism.tubeInvPunct E C}
  let X₂ : TopCat := TopCat.of (Work.Tubular.PuncturedDiscPair.Punct E x)
  let A₂ : Set (Work.Tubular.PuncturedDiscPair.Punct E x) :=
    Work.Tubular.PuncturedDiscPair.PunctRel E x
  -- ## The two maps of pairs
  have hφne : ∀ t : ↥(Work.ThomBordism.tubePtSet E C x),
      C.inv t.1.1 ≠ Work.Tubular.PuncturedDiscPair.basePt E x := by
    intro t h
    have hbase : Work.Tubular.tubeMap E (Work.Tubular.PuncturedDiscPair.basePt E x) = E.e x := by
      rw [Work.Tubular.PuncturedDiscPair.basePt, Work.Tubular.tubeMap_mk, add_zero]
    have h2 : C.inv (Work.Tubular.tubeMap E (Work.Tubular.PuncturedDiscPair.basePt E x)) =
        Work.Tubular.PuncturedDiscPair.basePt E x :=
      C.inv_tubeMap _ (by
        rw [Work.Tubular.PuncturedDiscPair.normalNorm_basePt]; exact hε.le)
    have h3 : C.inv (Work.Tubular.tubeMap E (Work.Tubular.PuncturedDiscPair.basePt E x))
        = C.inv t.1.1 := by rw [h2]; exact h.symm
    have h4 : Work.Tubular.tubeMap E (C.inv t.1.1) = t.1.1 := C.tubeMap_inv _ t.1.2
    have h5 : Work.Tubular.tubeMap E (C.inv (Work.Tubular.tubeMap E
        (Work.Tubular.PuncturedDiscPair.basePt E x)))
        = Work.Tubular.tubeMap E (Work.Tubular.PuncturedDiscPair.basePt E x) :=
      C.tubeMap_inv _ (by rw [hbase]; exact C.zero_mem_U x)
    rw [h3] at h5
    rw [h5, hbase] at h4
    exact (mem_tubePtSet E C x).mp t.2 h4.symm
  have hφcont' : Continuous fun t : ↥(Work.ThomBordism.tubePtSet E C x) => C.inv t.1.1 :=
    C.continuousOn_inv.comp_continuous (continuous_subtype_val.comp continuous_subtype_val)
      (fun t => t.1.2)
  let φfun : ↥(Work.ThomBordism.tubePtSet E C x) →
      Work.Tubular.PuncturedDiscPair.Punct E x := fun t => ⟨C.inv t.1.1, hφne t⟩
  have hφcont : Continuous φfun := Continuous.subtype_mk hφcont' (fun t => hφne t)
  let φ : X₁ ⟶ X₂ := TopCat.ofHom ⟨φfun, hφcont⟩
  have hψU : ∀ q : Work.Tubular.PuncturedDiscPair.Punct E x,
      Work.Tubular.tubeMap E (cap E ε q.1) ∈ C.U := fun q =>
    C.mem_U _ (cap_mem_disc E hε.le q.1)
  have hψne : ∀ q : Work.Tubular.PuncturedDiscPair.Punct E x,
      Work.Tubular.tubeMap E (cap E ε q.1) ≠ E.e x := by
    intro q h
    have h2 : C.inv (Work.Tubular.tubeMap E (cap E ε q.1)) = cap E ε q.1 :=
      C.inv_tubeMap _ (cap_mem_disc E hε.le q.1)
    rw [h, inv_embed E C x] at h2
    exact cap_ne_basePt hε E x q.2 h2.symm
  let ψfun : Work.Tubular.PuncturedDiscPair.Punct E x →
      ↥(Work.ThomBordism.tubePtSet E C x) :=
    fun q => ⟨⟨Work.Tubular.tubeMap E (cap E ε q.1), hψU q⟩, hψne q⟩
  have hψcont : Continuous ψfun :=
    Continuous.subtype_mk (Continuous.subtype_mk
      ((Work.Tubular.continuous_tubeMap E).comp
        ((ttm_continuous_cap E hε).comp continuous_subtype_val))
      (fun q => hψU q)) (fun q => hψne q)
  let ψ : X₂ ⟶ X₁ := TopCat.ofHom ⟨ψfun, hψcont⟩
  -- ## The compositions
  have hcomp1 : φ ≫ ψ = 𝟙 X₁ := by
    apply TopCat.ext
    intro t
    apply Subtype.ext
    apply Subtype.ext
    show Work.Tubular.tubeMap E (cap E ε (C.inv t.1.1)) = t.1.1
    rw [cap_eq_self_of_le E hε.le (C.inv_mem t.1.1 t.1.2), C.tubeMap_inv t.1.1 t.1.2]
  -- ## The radial homotopy from the composite `ψ ≫ φ` to the identity
  have hHcont : Continuous fun z : ↑unitInterval × ↥X₂ =>
      radialRescaleHomotopyFun E (capCoeff ε) (z.1, z.2.1) :=
    (continuous_radialRescaleHomotopyFun E (capCoeff ε) (continuous_capCoeff hε)).comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  let Hfun : ↑unitInterval × ↥X₂ → ↥X₂ := fun z =>
    ⟨radialRescaleHomotopyFun E (capCoeff ε) (z.1, z.2.1),
      radialRescaleHomotopyFun_ne_basePt hε E x z.1 z.2.2⟩
  have hHfun_cont : Continuous Hfun :=
    Continuous.subtype_mk hHcont
      (fun z => radialRescaleHomotopyFun_ne_basePt hε E x z.1 z.2.2)
  let H : TopCat.Homotopy (ψ ≫ φ) (𝟙 X₂) :=
    { toContinuousMap := ⟨Hfun, hHfun_cont⟩
      map_zero_left := fun q => by
        apply Subtype.ext
        show radialRescaleHomotopyFun E (capCoeff ε) ((0 : ↑unitInterval), q.1)
          = C.inv (Work.Tubular.tubeMap E (cap E ε q.1))
        rw [radialRescaleHomotopyFun_zero, C.inv_tubeMap _ (cap_mem_disc E hε.le q.1)]
        rfl
      map_one_left := fun q => by
        apply Subtype.ext
        show radialRescaleHomotopyFun E (capCoeff ε) ((1 : ↑unitInterval), q.1) = q.1
        rw [radialRescaleHomotopyFun_one] }
  -- ## The two preservation conditions on the relative sets
  have hf : ∀ a ∈ A₁, φ.hom a ∈ A₂ := by
    intro a ha
    have ha' : C.inv a.1.1 ∈ Work.Tubular.normalNonzero E := ha
    exact (Work.Tubular.mem_normalNonzero).mp ha'
  have hf' : ∀ b ∈ A₂, ψ.hom b ∈ A₁ := by
    intro b hb
    have hb' : 0 < Work.Tubular.normalNorm E b.1 :=
      lt_of_le_of_ne (Work.Tubular.normalNorm_nonneg E b.1)
        (Ne.symm (show Work.Tubular.normalNorm E b.1 ≠ 0 from hb))
    have h1 : C.inv (Work.Tubular.tubeMap E (cap E ε b.1)) = cap E ε b.1 :=
      C.inv_tubeMap _ (cap_mem_disc E hε.le b.1)
    show C.inv (Work.Tubular.tubeMap E (cap E ε b.1)) ∈ Work.Tubular.normalNonzero E
    rw [h1, Work.Tubular.mem_normalNonzero, normalNorm_cap E hε.le]
    exact ne_of_gt (lt_min hb' hε)
  -- ## The assembly
  have hwφ : Work.Cohomology.subtypeIncl X₁ A₁ ≫ φ
      = Work.Orient.Boundary.pairRestrict φ hf ≫ Work.Cohomology.subtypeIncl X₂ A₂ :=
    Work.Orient.Boundary.pairRestrict_subtypeIncl φ hf
  have hwψ : Work.Cohomology.subtypeIncl X₂ A₂ ≫ ψ
      = Work.Orient.Boundary.pairRestrict ψ hf' ≫ Work.Cohomology.subtypeIncl X₁ A₁ :=
    Work.Orient.Boundary.pairRestrict_subtypeIncl ψ hf'
  have hpair1 : Work.Orient.Boundary.pairRestrict φ hf ≫ Work.Orient.Boundary.pairRestrict ψ hf'
      = 𝟙 (TopCat.of A₁) :=
    Work.Orient.Boundary.pairRestrict_comp_eq_id φ ψ hf hf' hcomp1
  have w₁₂ : Work.Cohomology.subtypeIncl X₁ A₁ ≫ (φ ≫ ψ)
      = (Work.Orient.Boundary.pairRestrict φ hf ≫ Work.Orient.Boundary.pairRestrict ψ hf')
        ≫ Work.Cohomology.subtypeIncl X₁ A₁ := by
    rw [hcomp1, hpair1, Category.comp_id, Category.id_comp]
  have w₂₁ : Work.Cohomology.subtypeIncl X₂ A₂ ≫ (ψ ≫ φ)
      = (Work.Orient.Boundary.pairRestrict ψ hf' ≫ Work.Orient.Boundary.pairRestrict φ hf)
        ≫ Work.Cohomology.subtypeIncl X₂ A₂ := by
    calc Work.Cohomology.subtypeIncl X₂ A₂ ≫ (ψ ≫ φ)
        = (Work.Cohomology.subtypeIncl X₂ A₂ ≫ ψ) ≫ φ := (Category.assoc _ _ _).symm
      _ = (Work.Orient.Boundary.pairRestrict ψ hf' ≫ Work.Cohomology.subtypeIncl X₁ A₁) ≫ φ := by
            rw [hwψ]
      _ = Work.Orient.Boundary.pairRestrict ψ hf' ≫ (Work.Cohomology.subtypeIncl X₁ A₁ ≫ φ) :=
            Category.assoc _ _ _
      _ = Work.Orient.Boundary.pairRestrict ψ hf'
            ≫ (Work.Orient.Boundary.pairRestrict φ hf ≫ Work.Cohomology.subtypeIncl X₂ A₂) := by
            rw [hwφ]
      _ = (Work.Orient.Boundary.pairRestrict ψ hf' ≫ Work.Orient.Boundary.pairRestrict φ hf)
            ≫ Work.Cohomology.subtypeIncl X₂ A₂ := (Category.assoc _ _ _).symm
  have hw_id : Work.Cohomology.subtypeIncl X₂ A₂ ≫ 𝟙 X₂
      = 𝟙 (TopCat.of A₂) ≫ Work.Cohomology.subtypeIncl X₂ A₂ := by
    rw [Category.comp_id, Category.id_comp]
  have hH : ∀ (t : ↑unitInterval) (q : ↥X₂), q ∈ A₂ → H (t, q) ∈ A₂ := by
    intro t q hq
    have hq' : q.1 ∈ Work.Tubular.normalNonzero E :=
      (Work.Tubular.mem_normalNonzero).mpr
        (show Work.Tubular.normalNorm E q.1 ≠ 0 from hq)
    exact (Work.Tubular.mem_normalNonzero).mp
      (radialRescaleHomotopyFun_mem_normalNonzero E (capCoeff ε) (capCoeff_pos hε) hq')
  have hcomp1hom : HomologicalComplex.homologyMap
      (Work.Cohomology.relChainsMapOf X₁ X₂ A₁ A₂ φ
          (Work.Orient.Boundary.pairRestrict φ hf) hwφ ≫
        Work.Cohomology.relChainsMapOf X₂ X₁ A₂ A₁ ψ
          (Work.Orient.Boundary.pairRestrict ψ hf') hwψ) n
      = 𝟙 ((Work.Cohomology.relChains X₁ A₁).homology n) := by
    have hchain : Work.Cohomology.relChainsMapOf X₁ X₂ A₁ A₂ φ
          (Work.Orient.Boundary.pairRestrict φ hf) hwφ ≫
        Work.Cohomology.relChainsMapOf X₂ X₁ A₂ A₁ ψ
          (Work.Orient.Boundary.pairRestrict ψ hf') hwψ
        = 𝟙 (Work.Cohomology.relChains X₁ A₁) := by
      rw [Work.Cohomology.relChainsMapOf_comp A₁ A₂ A₁ φ
        (Work.Orient.Boundary.pairRestrict φ hf) hwφ ψ
        (Work.Orient.Boundary.pairRestrict ψ hf') hwψ w₁₂]
      exact Work.Orient.Boundary.relChainsMapOf_id_of (φ ≫ ψ)
        (Work.Orient.Boundary.pairRestrict φ hf ≫ Work.Orient.Boundary.pairRestrict ψ hf')
        w₁₂ hcomp1 hpair1
    rw [hchain, HomologicalComplex.homologyMap_id]
  have hcomp2hom : HomologicalComplex.homologyMap
      (Work.Cohomology.relChainsMapOf X₂ X₁ A₂ A₁ ψ
          (Work.Orient.Boundary.pairRestrict ψ hf') hwψ ≫
        Work.Cohomology.relChainsMapOf X₁ X₂ A₁ A₂ φ
          (Work.Orient.Boundary.pairRestrict φ hf) hwφ) n
      = 𝟙 ((Work.Cohomology.relChains X₂ A₂).homology n) := by
    rw [Work.Cohomology.relChainsMapOf_comp A₂ A₁ A₂ ψ
      (Work.Orient.Boundary.pairRestrict ψ hf') hwψ φ
      (Work.Orient.Boundary.pairRestrict φ hf) hwφ w₂₁]
    rw [Work.PTGeometric.HOF.relChainsMapOf_homologyMap_eq_of_homotopic A₂ A₂
      (Work.Orient.Boundary.pairRestrict ψ hf' ≫ Work.Orient.Boundary.pairRestrict φ hf)
      (𝟙 (TopCat.of A₂)) w₂₁ hw_id H hH n]
    rw [Work.Orient.Boundary.relChainsMapOf_id (X := X₂) A₂ hw_id,
      HomologicalComplex.homologyMap_id]
  have hleft : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (Work.Cohomology.relChainsMapOf X₂ X₁ A₂ A₁ ψ
          (Work.Orient.Boundary.pairRestrict ψ hf') hwψ) n)).comp
      (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (Work.Cohomology.relChainsMapOf X₁ X₂ A₁ A₂ φ
          (Work.Orient.Boundary.pairRestrict φ hf) hwφ) n)) = LinearMap.id := by
    have h2 : ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (Work.Cohomology.relChainsMapOf X₁ X₂ A₁ A₂ φ
            (Work.Orient.Boundary.pairRestrict φ hf) hwφ ≫
          Work.Cohomology.relChainsMapOf X₂ X₁ A₂ A₁ ψ
            (Work.Orient.Boundary.pairRestrict ψ hf') hwψ) n) = LinearMap.id := by
      rw [hcomp1hom]
      exact ModuleCat.hom_id
    rw [← h2, HomologicalComplex.homologyMap_comp, ModuleCat.hom_comp]
  have hright : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (Work.Cohomology.relChainsMapOf X₁ X₂ A₁ A₂ φ
          (Work.Orient.Boundary.pairRestrict φ hf) hwφ) n)).comp
      (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (Work.Cohomology.relChainsMapOf X₂ X₁ A₂ A₁ ψ
          (Work.Orient.Boundary.pairRestrict ψ hf') hwψ) n)) = LinearMap.id := by
    have h2 : ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (Work.Cohomology.relChainsMapOf X₂ X₁ A₂ A₁ ψ
            (Work.Orient.Boundary.pairRestrict ψ hf') hwψ ≫
          Work.Cohomology.relChainsMapOf X₁ X₂ A₁ A₂ φ
            (Work.Orient.Boundary.pairRestrict φ hf) hwφ) n) = LinearMap.id := by
      rw [hcomp2hom]
      exact ModuleCat.hom_id
    rw [← h2, HomologicalComplex.homologyMap_comp, ModuleCat.hom_comp]
  have keyL : ∀ x, (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (Work.Cohomology.relChainsMapOf X₂ X₁ A₂ A₁ ψ
          (Work.Orient.Boundary.pairRestrict ψ hf') hwψ) n))
      ((ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (Work.Cohomology.relChainsMapOf X₁ X₂ A₁ A₂ φ
          (Work.Orient.Boundary.pairRestrict φ hf) hwφ) n)) x) = x :=
    fun x => by simpa using congrArg (fun f => f x) hleft
  have keyR : ∀ y, (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (Work.Cohomology.relChainsMapOf X₁ X₂ A₁ A₂ φ
          (Work.Orient.Boundary.pairRestrict φ hf) hwφ) n))
      ((ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (Work.Cohomology.relChainsMapOf X₂ X₁ A₂ A₁ ψ
          (Work.Orient.Boundary.pairRestrict ψ hf') hwψ) n)) y) = y :=
    fun y => by simpa using congrArg (fun f => f y) hright
  have hinj : Function.Injective (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (Work.Cohomology.relChainsMapOf X₁ X₂ A₁ A₂ φ
        (Work.Orient.Boundary.pairRestrict φ hf) hwφ) n)) := by
    intro a b hab
    rw [← keyL a, hab, keyL b]
  have hsurj : Function.Surjective (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (Work.Cohomology.relChainsMapOf X₁ X₂ A₁ A₂ φ
        (Work.Orient.Boundary.pairRestrict φ hf) hwφ) n)) :=
    fun y => ⟨(ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (Work.Cohomology.relChainsMapOf X₂ X₁ A₂ A₁ ψ
        (Work.Orient.Boundary.pairRestrict ψ hf') hwψ) n)) y, keyR y⟩
  exact ⟨LinearEquiv.toModuleIso (LinearEquiv.ofBijective _ ⟨hinj, hsurj⟩)⟩

end

end Work.ThomBordism
