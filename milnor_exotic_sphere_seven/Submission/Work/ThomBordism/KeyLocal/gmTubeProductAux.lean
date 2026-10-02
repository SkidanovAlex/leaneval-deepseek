import Mathlib
import Submission.Work.ThomBordism.KeyLocal.gmTubeAux
import Submission.Work.ThomBordism.KeyLocal.hasFDerivAt_readFrame_of_continuousAt
import Submission.Work.ThomBordism.KeyLocal.germPullbackEucAt
import Submission.Work.ThomBordism.someOpen_relCohMap_injective

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

open CategoryTheory

/-!
# The auxiliary lemmas of the (GM) tube comparison

* `linearIndependent_tanFrame`, `inner_tanFrame_gframe` -- the two frame facts feeding `gmSign`;
* `hasFDerivAt_of_comp_add` -- differentiation at `c` from differentiation at `0` of the translate;
* `hasFDerivAt_ambTubeProduct` -- the derivative of the ambient product coordinate map at the
  embedding point, together with the sign of its determinant (the `gmSign` input);
* `tcfdUSet` and `tcfdIncl_relative_injective` -- the localisation injectivity of the inclusion of
  the open ambient piece into the chart piece.
-/

namespace Work.ThomBordism.KeyLocal

noncomputable section

open Work.Tubular Work.ThomBordism.PontryaginThom Work.ThomBordism.FrameSigns

open scoped Topology

variable {V : Work.ThomBordism.Man8} {k : ℕ}

theorem linearIndependent_tanFrame (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i : CoverIdx V k) (x : V.pt) (hx : x ∈ ND.D.baseSet i) :
    LinearIndependent ℝ (Work.ThomBordism.tanFrame E i x) := by
  rw [Work.ThomBordism.tanFrame_apply]
  exact Work.ThomBordism.PontryaginThom.frame_linearIndependent (f := E.e)
    (Work.ThomBordism.embedding_contMDiff E) E.injective_mfderiv
    (Work.ThomBordism.PontryaginThom.coverChart i) (ND.baseSet_sub i.1 i.2 x hx)

theorem inner_tanFrame_gframe (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i : CoverIdx V k) (x : V.pt) (hx : x ∈ ND.D.baseSet i) (a : Fin 8) (b : Fin k) :
    inner ℝ (Work.ThomBordism.tanFrame E i x a)
      (Work.ThomBordism.Gauss.gframe E ND i x b) = 0 := by
  rw [Work.ThomBordism.Gauss.gframe_apply]
  exact Work.Tubular.inner_eq_zero_of_mem_normalSpace
    (Submodule.smul_mem _ _ (Work.Tubular.orthFrame_mem E ND i hx b))
    (Work.ThomBordism.tanFrame_mem_tangentSpace E ND i hx a)

/-- Derivative at `c` from the derivative at `0` of the translate. -/
theorem hasFDerivAt_of_comp_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {f' : E →L[ℝ] F} {c : E}
    (hf : HasFDerivAt (fun z => f (c + z)) f' 0) : HasFDerivAt f f' c := by
  rw [hasFDerivAt_iff_isLittleO]
  have ht : Filter.Tendsto (fun y : E => y - c) (nhds c) (nhds (0 : E)) := by
    have h : Continuous fun y : E => y - c := continuous_id.sub continuous_const
    simpa using h.tendsto c
  have hcomp := hf.isLittleO.comp_tendsto ht
  simpa only [Function.comp_def, add_sub_cancel, add_zero, sub_zero] using hcomp

theorem hasFDerivAt_ambTubeProduct (hk : 1 ≤ k)
    (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : TubeChart E ε)
    (ND : NormalData V k E.e) (i : CoverIdx V k) (x : V.pt) (hx : x ∈ ND.D.baseSet i) :
    ∃ L : Work.Tubular.Euc (8 + k) →L[ℝ] Work.Tubular.Euc (8 + k),
      HasFDerivAt (ambTubeProduct E C ND i x) L (E.e x) ∧
      Function.Bijective L ∧
      Real.sign (LinearMap.det L.toLinearMap) = FrameSigns.frameSign V i.1 x := by
  classical
  obtain ⟨L1, L2, hd, h1, h2⟩ := tubeCoordsFDeriv E ND C i x hx
  have hK : HasFDerivAt (fun y : Work.Tubular.Euc (8 + k) =>
      (chartMap V i.1 (NormalTotal.proj (C.inv y)), NormalTotal.vec (C.inv y)))
      (L1.prod L2) (E.e x) := by
    refine hasFDerivAt_of_comp_add (f := fun y : Work.Tubular.Euc (8 + k) =>
      (chartMap V i.1 (NormalTotal.proj (C.inv y)), NormalTotal.vec (C.inv y))) ?_
    simpa only using hd
  have hK1 : HasFDerivAt (fun y : Work.Tubular.Euc (8 + k) =>
      chartMap V i.1 (NormalTotal.proj (C.inv y))) L1 (E.e x) := hK.fst
  have hK2 : HasFDerivAt (fun y : Work.Tubular.Euc (8 + k) =>
      NormalTotal.vec (C.inv y)) L2 (E.e x) := hK.snd
  have hAc : ContinuousAt (fun y : Work.Tubular.Euc (8 + k) =>
      Work.ThomBordism.Gauss.gframe E ND i (NormalTotal.proj (C.inv y))) (E.e x) := by
    rw [continuousAt_pi]
    exact fun a => continuousAt_gframe_inv E C ND i x hx a
  have hVa : NormalTotal.vec (C.inv (E.e x)) = 0 := vec_inv_embed_tcfd E C x
  have hF2 : HasFDerivAt (fun y : Work.Tubular.Euc (8 + k) =>
      Work.ThomBordism.readFrame
        (Work.ThomBordism.Gauss.gframe E ND i (NormalTotal.proj (C.inv y)))
        (NormalTotal.vec (C.inv y)))
      ((Work.ThomBordism.readFrame (Work.ThomBordism.Gauss.gframe E ND i x)).comp L2)
      (E.e x) := by
    have h := hasFDerivAt_readFrame_of_continuousAt (N := 8 + k) (n := 8 + k) hAc hK2 hVa
    rwa [proj_inv_embed_tcfd E C x] at h
  have hF1 : HasFDerivAt (fun y : Work.Tubular.Euc (8 + k) =>
      chartMap V i.1 (NormalTotal.proj (C.inv y)) - chartMap V i.1 x) L1 (E.e x) :=
    hK1.sub_const (chartMap V i.1 x)
  have hpair : HasFDerivAt (fun y : Work.Tubular.Euc (8 + k) =>
      (chartMap V i.1 (NormalTotal.proj (C.inv y)) - chartMap V i.1 x,
       Work.ThomBordism.readFrame
         (Work.ThomBordism.Gauss.gframe E ND i (NormalTotal.proj (C.inv y)))
         (NormalTotal.vec (C.inv y))))
      (L1.prod ((Work.ThomBordism.readFrame (Work.ThomBordism.Gauss.gframe E ND i x)).comp L2))
      (E.e x) := hF1.prodMk hF2
  have hcomp : HasFDerivAt (fun y : Work.Tubular.Euc (8 + k) =>
      Work.Whitney.tcmSumLin 8 k
        (chartMap V i.1 (NormalTotal.proj (C.inv y)) - chartMap V i.1 x,
         Work.ThomBordism.readFrame
           (Work.ThomBordism.Gauss.gframe E ND i (NormalTotal.proj (C.inv y)))
           (NormalTotal.vec (C.inv y))))
      (((Work.Whitney.tcmSumLin 8 k) : Work.Tubular.Euc 8 × Work.Tubular.Euc k →L[ℝ]
          Work.Tubular.Euc (8 + k)).comp
        (L1.prod ((Work.ThomBordism.readFrame (Work.ThomBordism.Gauss.gframe E ND i x)).comp L2)))
      (E.e x) :=
    (ContinuousLinearMap.hasFDerivAt ((Work.Whitney.tcmSumLin 8 k) : Work.Tubular.Euc 8 × Work.Tubular.Euc k →L[ℝ] Work.Tubular.Euc (8 + k))).comp (E.e x) hpair
  have hsign : Real.sign (LinearMap.det
      (((Work.Whitney.tcmSumLin 8 k) : Work.Tubular.Euc 8 × Work.Tubular.Euc k →L[ℝ]
          Work.Tubular.Euc (8 + k)).comp
        (L1.prod ((Work.ThomBordism.readFrame (Work.ThomBordism.Gauss.gframe E ND i x)).comp L2))).toLinearMap)
      = FrameSigns.frameSign V i.1 x := by
    have hg := gmSign hk (Work.ThomBordism.tanFrame E i x)
      (Work.ThomBordism.Gauss.gframe E ND i x) L1 L2
      (linearIndependent_tanFrame E ND i x hx)
      (Work.ThomBordism.Gauss.orthonormal_gframe E ND i hx)
      (inner_tanFrame_gframe E ND i x hx) h1 h2
    have hpc := pairSign_tanFrame_gframe E ND hk i x hx
    have hLM : (((Work.Whitney.tcmSumLin 8 k) : Work.Tubular.Euc 8 × Work.Tubular.Euc k →L[ℝ]
        Work.Tubular.Euc (8 + k)).comp
          (L1.prod ((Work.ThomBordism.readFrame (Work.ThomBordism.Gauss.gframe E ND i x)).comp L2))).toLinearMap
        = ((Work.Whitney.tcmSumLin 8 k) : Work.Tubular.Euc 8 × Work.Tubular.Euc k →L[ℝ]
            Work.Tubular.Euc (8 + k)).toLinearMap.comp
          ((L1.prod ((Work.ThomBordism.readFrame (Work.ThomBordism.Gauss.gframe E ND i x)).comp L2))).toLinearMap :=
      ContinuousLinearMap.toLinearMap_comp _ _
    calc Real.sign (LinearMap.det
          (((Work.Whitney.tcmSumLin 8 k) : Work.Tubular.Euc 8 × Work.Tubular.Euc k →L[ℝ]
              Work.Tubular.Euc (8 + k)).comp
            (L1.prod ((Work.ThomBordism.readFrame (Work.ThomBordism.Gauss.gframe E ND i x)).comp L2))).toLinearMap)
        = Real.sign (LinearMap.det (((Work.Whitney.tcmSumLin 8 k) : Work.Tubular.Euc 8 ×
              Work.Tubular.Euc k →L[ℝ] Work.Tubular.Euc (8 + k)).toLinearMap.comp
            ((L1.prod ((Work.ThomBordism.readFrame (Work.ThomBordism.Gauss.gframe E ND i x)).comp L2))).toLinearMap)) := by
          rw [hLM]
      _ = OrthFrame.pairSign (Work.ThomBordism.tanFrame E i x)
            (Work.ThomBordism.Gauss.gframe E ND i x) := hg
      _ = FrameSigns.frameSign V i.1 x := hpc
  refine ⟨_, hcomp, ?_, hsign⟩
  have hdet : LinearMap.det (((Work.Whitney.tcmSumLin 8 k) : Work.Tubular.Euc 8 ×
      Work.Tubular.Euc k →L[ℝ] Work.Tubular.Euc (8 + k)).comp
        (L1.prod ((Work.ThomBordism.readFrame (Work.ThomBordism.Gauss.gframe E ND i x)).comp L2))).toLinearMap
      ≠ 0 := by
    intro h0
    have hz : Real.sign (LinearMap.det (((Work.Whitney.tcmSumLin 8 k) : Work.Tubular.Euc 8 ×
        Work.Tubular.Euc k →L[ℝ] Work.Tubular.Euc (8 + k)).comp
          (L1.prod ((Work.ThomBordism.readFrame (Work.ThomBordism.Gauss.gframe E ND i x)).comp L2))).toLinearMap)
        = 0 := by rw [h0, Real.sign_zero]
    rw [hsign] at hz
    rcases FrameSigns.frameSign_eq_one_or_neg_one V i.1 x with h | h <;> rw [h] at hz <;> norm_num at hz
  have hker : (((Work.Whitney.tcmSumLin 8 k) : Work.Tubular.Euc 8 × Work.Tubular.Euc k →L[ℝ]
      Work.Tubular.Euc (8 + k)).comp
        (L1.prod ((Work.ThomBordism.readFrame (Work.ThomBordism.Gauss.gframe E ND i x)).comp L2))).toLinearMap.ker
      = ⊥ := by
    by_contra h
    exact hdet ((LinearMap.det_eq_zero_iff_ker_ne_bot).mpr h)
  have hinj : Function.Injective (((Work.Whitney.tcmSumLin 8 k) : Work.Tubular.Euc 8 ×
      Work.Tubular.Euc k →L[ℝ] Work.Tubular.Euc (8 + k)).comp
        (L1.prod ((Work.ThomBordism.readFrame (Work.ThomBordism.Gauss.gframe E ND i x)).comp L2))) :=
    LinearMap.ker_eq_bot.mp hker
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hinj⟩


/-! ## The inclusion of the open ambient piece -/

/-- The open piece `tcfdSet`, viewed as an open subset of the chart piece. -/
def tcfdUSet (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : TubeChart E ε)
    (ND : NormalData V k E.e) (i : CoverIdx V k) : Set ↥(tubeBaseSet E C ND i) :=
  {u | (u : Work.Tubular.Euc (8 + k)) ∈ tcfdSet E C ND i}

/-- **The inclusion of the open ambient piece induces an injection on the relative cohomology of
the chart piece**, relative to the punctured set of the chart piece. -/
theorem tcfdIncl_relative_injective (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : TubeChart E ε)
    (ND : NormalData V k E.e) (i : CoverIdx V k) (x : V.pt) (hx : x ∈ ND.D.baseSet i) :
    Function.Injective (ModuleCat.Hom.hom (Work.Thom.relCohMap (tcfdIncl E C ND i)
      {z : ↥(tcfdSet E C ND i) | (z : Work.Tubular.Euc (8 + k)) ≠ E.e x}
      (tubeFootPunct E C ND i x ∪ tubeBaseSetPunct E C ND i)
      (fun z hz => by
        rw [tubeBasePunct_eq]
        exact hz) ℤ (8 + k))) := by
  classical
  set A' : Set ↥(tubeBaseSet E C ND i) :=
    tubeFootPunct E C ND i x ∪ tubeBaseSetPunct E C ND i with hA'def
  have hAeq : A' = {y : ↥(tubeBaseSet E C ND i) | (y : Work.Tubular.Euc (8 + k)) ≠ E.e x} :=
    tubeBasePunct_eq E C ND i x
  have hU : IsOpen (tcfdUSet E C ND i) := by
    show IsOpen ((fun u : ↥(tubeBaseSet E C ND i) =>
      (u : Work.Tubular.Euc (8 + k))) ⁻¹' tcfdSet E C ND i)
    exact (isOpen_tcfdSet E C ND i).preimage
      (continuous_subtype_val.comp continuous_subtype_val)
  have hAopen : IsOpen A' := by
    rw [hAeq]
    exact isClosed_singleton.isOpen_compl.preimage
      (continuous_subtype_val.comp continuous_subtype_val)
  have hcov : tcfdUSet E C ND i ∪ A' = Set.univ := by
    rw [hAeq]
    rw [Set.eq_univ_iff_forall]
    intro u
    by_cases h : (u : Work.Tubular.Euc (8 + k)) = E.e x
    · exact Or.inl (by
        show (u : Work.Tubular.Euc (8 + k)) ∈ tcfdSet E C ND i
        rw [h]
        exact embed_mem_tcfdSet E C ND i x hx)
    · exact Or.inr h
  have hinj_j : Function.Injective (ModuleCat.Hom.hom (Work.Thom.relCohMap
      (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(tcfdUSet E C ND i),
        ↥(tubeBaseSet E C ND i)))
      ({y : ↥(tcfdUSet E C ND i) | (y : ↥(tubeBaseSet E C ND i)) ∈ A'})
      A' (fun _ hx => hx) ℤ (8 + k))) :=
    ((CategoryTheory.ConcreteCategory.isIso_iff_bijective _).mp
      (Work.Cohomology.capRel_excision_isIso (TopCat.of ↥(tubeBaseSet E C ND i))
        (tcfdUSet E C ND i) A' hU hAopen hcov (8 + k) (fun _ hx => hx))).1
  -- the two inverse maps between the ambient piece and its image in the chart piece
  set eC : C(↥(tcfdSet E C ND i), ↥(tcfdUSet E C ND i)) :=
    ⟨fun z => ⟨tcfdIncl E C ND i z, z.2⟩,
      Continuous.subtype_mk (tcfdIncl E C ND i).continuous (fun z => z.2)⟩ with heC
  set eI : C(↥(tcfdUSet E C ND i), ↥(tcfdSet E C ND i)) :=
    ⟨fun u => ⟨(u.1 : Work.Tubular.Euc (8 + k)), u.2⟩,
      Continuous.subtype_mk
        ((continuous_subtype_val : Continuous (Subtype.val : ↥(C.U) → Work.Tubular.Euc (8 + k))).comp
          ((continuous_subtype_val : Continuous (Subtype.val : ↥(tubeBaseSet E C ND i) → ↥(C.U))).comp
            (continuous_subtype_val :
              Continuous (Subtype.val : ↥(tcfdUSet E C ND i) → ↥(tubeBaseSet E C ND i)))))
        (fun u => u.2)⟩ with heI
  have heI_eC : eI.comp eC = ContinuousMap.id ↥(tcfdSet E C ND i) := by
    apply ContinuousMap.ext
    intro z
    rfl
  have heC_eI : eC.comp eI = ContinuousMap.id ↥(tcfdUSet E C ND i) := by
    apply ContinuousMap.ext
    intro u
    rfl
  have hmemC : ∀ z ∈ ({z : ↥(tcfdSet E C ND i) | (z : Work.Tubular.Euc (8 + k)) ≠ E.e x}),
      eC z ∈ {y : ↥(tcfdUSet E C ND i) | (y : ↥(tubeBaseSet E C ND i)) ∈ A'} := by
    intro z hz
    rw [hAeq]
    exact hz
  have hmemeI : ∀ u ∈ ({y : ↥(tcfdUSet E C ND i) | (y : ↥(tubeBaseSet E C ND i)) ∈ A'}),
      eI u ∈ {z : ↥(tcfdSet E C ND i) | (z : Work.Tubular.Euc (8 + k)) ≠ E.e x} := by
    intro u hu
    rw [hAeq] at hu
    exact hu
  have hid : ∀ w : Work.Thom.RelCoh ℤ (8 + k) ↥(tcfdUSet E C ND i)
      ({y : ↥(tcfdUSet E C ND i) | (y : ↥(tubeBaseSet E C ND i)) ∈ A'}),
      (Work.Thom.relCohMap eI
          ({y : ↥(tcfdUSet E C ND i) | (y : ↥(tubeBaseSet E C ND i)) ∈ A'})
          {z : ↥(tcfdSet E C ND i) | (z : Work.Tubular.Euc (8 + k)) ≠ E.e x}
          hmemeI ℤ (8 + k)).hom
        ((Work.Thom.relCohMap eC
          {z : ↥(tcfdSet E C ND i) | (z : Work.Tubular.Euc (8 + k)) ≠ E.e x}
          ({y : ↥(tcfdUSet E C ND i) | (y : ↥(tubeBaseSet E C ND i)) ∈ A'}) hmemC
          ℤ (8 + k)).hom w) = w := by
    intro w
    rw [Work.Thom.relCohMap_compA_apply
      ({y : ↥(tcfdUSet E C ND i) | (y : ↥(tubeBaseSet E C ND i)) ∈ A'})
      {z : ↥(tcfdSet E C ND i) | (z : Work.Tubular.Euc (8 + k)) ≠ E.e x}
      ({y : ↥(tcfdUSet E C ND i) | (y : ↥(tubeBaseSet E C ND i)) ∈ A'})
      eI eC hmemeI hmemC (fun u hu => hmemC (eI u) (hmemeI u hu)) ℤ (8 + k) w]
    rw [show (Work.Thom.relCohMap (eC.comp eI)
        ({y : ↥(tcfdUSet E C ND i) | (y : ↥(tubeBaseSet E C ND i)) ∈ A'})
        ({y : ↥(tcfdUSet E C ND i) | (y : ↥(tubeBaseSet E C ND i)) ∈ A'})
        (fun u hu => hmemC (eI u) (hmemeI u hu)) ℤ (8 + k))
        = (Work.Thom.relCohMap (ContinuousMap.id ↥(tcfdUSet E C ND i))
            ({y : ↥(tcfdUSet E C ND i) | (y : ↥(tubeBaseSet E C ND i)) ∈ A'})
            ({y : ↥(tcfdUSet E C ND i) | (y : ↥(tubeBaseSet E C ND i)) ∈ A'})
            (fun _ hz => hz) ℤ (8 + k)) from
      Work.Thom.relCohMap_congrA _ _ heC_eI _ _ ℤ (8 + k)]
    rw [Work.Thom.relCohMap_idA]
    rfl
  have hinj_eC : Function.Injective (ModuleCat.Hom.hom (Work.Thom.relCohMap eC
      {z : ↥(tcfdSet E C ND i) | (z : Work.Tubular.Euc (8 + k)) ≠ E.e x}
      ({y : ↥(tcfdUSet E C ND i) | (y : ↥(tubeBaseSet E C ND i)) ∈ A'}) hmemC
      ℤ (8 + k))) := by
    intro w₁ w₂ hw
    have h := congrArg (fun z => (Work.Thom.relCohMap eI
        ({y : ↥(tcfdUSet E C ND i) | (y : ↥(tubeBaseSet E C ND i)) ∈ A'})
        {z : ↥(tcfdSet E C ND i) | (z : Work.Tubular.Euc (8 + k)) ≠ E.e x}
        hmemeI ℤ (8 + k)).hom z) hw
    rw [hid w₁, hid w₂] at h
    exact h
  have hcomp : ∀ w : Work.Thom.RelCoh ℤ (8 + k) (↥(tubeBaseSet E C ND i)) A',
      (Work.Thom.relCohMap eC
          {z : ↥(tcfdSet E C ND i) | (z : Work.Tubular.Euc (8 + k)) ≠ E.e x}
          ({y : ↥(tcfdUSet E C ND i) | (y : ↥(tubeBaseSet E C ND i)) ∈ A'}) hmemC
          ℤ (8 + k)).hom
        ((Work.Thom.relCohMap
          (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(tcfdUSet E C ND i),
            ↥(tubeBaseSet E C ND i)))
          ({y : ↥(tcfdUSet E C ND i) | (y : ↥(tubeBaseSet E C ND i)) ∈ A'})
          A' (fun _ hx => hx) ℤ (8 + k)).hom w)
        = (Work.Thom.relCohMap (tcfdIncl E C ND i)
            {z : ↥(tcfdSet E C ND i) | (z : Work.Tubular.Euc (8 + k)) ≠ E.e x}
            A' (fun z hz => by rw [hAeq]; exact hz) ℤ (8 + k)).hom w := by
    intro w
    rw [Work.Thom.relCohMap_compA_apply
      ({z : ↥(tcfdSet E C ND i) | (z : Work.Tubular.Euc (8 + k)) ≠ E.e x})
      ({y : ↥(tcfdUSet E C ND i) | (y : ↥(tubeBaseSet E C ND i)) ∈ A'})
      A' eC (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(tcfdUSet E C ND i),
        ↥(tubeBaseSet E C ND i)))
      hmemC (fun _ hx => hx) (fun z hz => by rw [hAeq]; exact hz) ℤ (8 + k) w]
    rfl
  intro w₁ w₂ hw
  have h1 : (Work.Thom.relCohMap eC
      {z : ↥(tcfdSet E C ND i) | (z : Work.Tubular.Euc (8 + k)) ≠ E.e x}
      ({y : ↥(tcfdUSet E C ND i) | (y : ↥(tubeBaseSet E C ND i)) ∈ A'}) hmemC
      ℤ (8 + k)).hom
      ((Work.Thom.relCohMap
        (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(tcfdUSet E C ND i),
          ↥(tubeBaseSet E C ND i)))
        ({y : ↥(tcfdUSet E C ND i) | (y : ↥(tubeBaseSet E C ND i)) ∈ A'})
        A' (fun _ hx => hx) ℤ (8 + k)).hom w₁)
      = (Work.Thom.relCohMap eC
      {z : ↥(tcfdSet E C ND i) | (z : Work.Tubular.Euc (8 + k)) ≠ E.e x}
      ({y : ↥(tcfdUSet E C ND i) | (y : ↥(tubeBaseSet E C ND i)) ∈ A'}) hmemC
      ℤ (8 + k)).hom
      ((Work.Thom.relCohMap
        (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(tcfdUSet E C ND i),
          ↥(tubeBaseSet E C ND i)))
        ({y : ↥(tcfdUSet E C ND i) | (y : ↥(tubeBaseSet E C ND i)) ∈ A'})
        A' (fun _ hx => hx) ℤ (8 + k)).hom w₂) := by
    rw [hcomp w₁, hcomp w₂, hw]
  exact hinj_j (hinj_eC h1)


end

end Work.ThomBordism.KeyLocal
