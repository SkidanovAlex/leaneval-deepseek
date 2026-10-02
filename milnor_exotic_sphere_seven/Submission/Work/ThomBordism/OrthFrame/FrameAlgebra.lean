import Mathlib
import Submission.Work.Tubular.exists_euclidean_normalBundle
import Submission.Work.ThomBordism.Grassmann.Grassmannian
import Submission.Work.ThomBordism.PontryaginThom.NormalData
import Submission.Work.ThomBordism.PontryaginThom.FramesRange
import Submission.Work.ThomBordism.OrthFrame.Defs
import Submission.Work.ThomBordism.OrthFrame.sign_det_combMat

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Frame algebra of the normal data of an embedded `8`-manifold

The elementary facts about the chart tangent frame
`tanFrame E i x = frame E.e (coverChart i) x` of an embedding `E : V ↪ ℝ^{8+k}` and the orthonormal
normal frame `Work.Tubular.orthFrame E ND i x`, which the frame statement
`Work.ThomBordism.orthFrameOrientation` consumes:

* continuity on the base sets, and membership in the tangent space;
* orthogonality of the two frames (the tangent and the normal bundle are orthogonal complements);
* the spans (`span_tanFrame`, and `Work.Tubular.span_orthFrame` for the normal frame);
* linear independence of the concatenation `pairFrame` and the non-vanishing of the determinant of
  its coordinate matrix (`pairMat`).

The *multiplicativity* of the determinant sign along the decomposition is
`Work.ThomBordism.OrthFrame.sign_det_pairMat`.
-/

open scoped Manifold ContDiff Topology BigOperators

namespace Work.ThomBordism

open Work.ThomBordism.PontryaginThom Work.ThomBordism.OrthFrame Work.ThomBordism.Grassmann

noncomputable section

variable {V : Man8} {k : ℕ}

/-- The **chart tangent frame** of the embedding `E` in the chart of the index `i`, at `x`. -/
def tanFrame (E : EmbeddingData V (8 + k)) (i : CoverIdx V k) (x : V.pt) : Fin 8 → Euc (8 + k) :=
  frame E.e (coverChart i) x

theorem tanFrame_apply (E : EmbeddingData V (8 + k)) (i : CoverIdx V k) (x : V.pt) :
    tanFrame E i x = frame E.e (coverChart i) x := rfl

/-- The smoothness of the embedding, in the form the frame lemmas want. -/
theorem embedding_contMDiff (E : EmbeddingData V (8 + k)) :
    ContMDiff (𝓡 8) (𝓡 (8 + k)) 1 E.e := E.smooth.of_le (by norm_num)

theorem continuousOn_tanFrame (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i : CoverIdx V k) (a : Fin 8) :
    ContinuousOn (fun x => tanFrame E i x a) (ND.D.baseSet i) :=
  ((continuousOn_pi.mp (continuousOn_frame (f := E.e) (embedding_contMDiff E)
    (coverChart i))) a).mono
      (fun x hx => ND.baseSet_sub i.1 i.2 x hx)

/-- The chart tangent frame lies in the tangent space. -/
theorem tanFrame_mem_tangentSpace (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i : CoverIdx V k) {x : V.pt} (hx : x ∈ ND.D.baseSet i) (a : Fin 8) :
    tanFrame E i x a ∈ Work.Tubular.tangentSpace E x := by
  have hsrc : x ∈ (coverChart i).1.source := ND.baseSet_sub i.1 i.2 x hx
  have hrange := range_coeffMap_frame_eq_mfderiv (V := V) (k := k) E.e (embedding_contMDiff E)
    (coverChart i) hsrc
  have hcoord : coeffMap (frame E.e (coverChart i) x) (Pi.single a (1 : ℝ))
      = eucToFun (8 + k) (tanFrame E i x a) := by
    -- the `a`-th coordinate vector of `Fin 8` collects the `a`-th frame vector
    rw [coeffMap_eq_sum]
    have hsum : (∑ j, ((Pi.single a (1 : ℝ)) : Fin 8 → ℝ) j • frame E.e (coverChart i) x j)
        = ((Pi.single a (1 : ℝ)) : Fin 8 → ℝ) a • frame E.e (coverChart i) x a :=
      Finset.sum_eq_single a (fun b _ hb => by rw [Pi.single_eq_of_ne hb, zero_smul])
        (fun ha => absurd (Finset.mem_univ a) ha)
    rw [hsum, Pi.single_eq_same, one_smul]
    rfl
  have key : eucToFun (8 + k) (tanFrame E i x a)
      ∈ LinearMap.range (coeffMap (frame E.e (coverChart i) x)) :=
    ⟨Pi.single a (1 : ℝ), hcoord⟩
  rw [hrange] at key
  obtain ⟨u, hu, hueq⟩ := Submodule.mem_map.mp key
  have hua : tanFrame E i x a = u := by
    have h2 := congrArg (funToEuc (8 + k)) hueq
    simpa using h2.symm
  rw [Work.Tubular.tangentSpace, hua]
  exact hu

/-- The tangent chart frame and the normal frame are orthogonal. -/
theorem tanFrame_inner_orthFrame (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i : CoverIdx V k) {x : V.pt} (hx : x ∈ ND.D.baseSet i) (a : Fin 8) (b : Fin k) :
    inner ℝ (tanFrame E i x a) (Work.Tubular.orthFrame E ND i x b) = 0 :=
  Work.Tubular.inner_eq_zero_of_mem_normalSpace (Work.Tubular.orthFrame_mem E ND i hx b)
    (tanFrame_mem_tangentSpace E ND i hx a)

/-- The span of the chart tangent frame is the tangent space. -/
theorem span_tanFrame (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i : CoverIdx V k) {x : V.pt} (hx : x ∈ ND.D.baseSet i) :
    Submodule.span ℝ (Set.range (tanFrame E i x)) = Work.Tubular.tangentSpace E x := by
  have hsrc : x ∈ (coverChart i).1.source := ND.baseSet_sub i.1 i.2 x hx
  have hfinT : Module.finrank ℝ (Work.Tubular.tangentSpace E x) = 8 := by
    haveI : FiniteDimensional ℝ (TangentSpace (𝓡 8) x) :=
      inferInstanceAs (FiniteDimensional ℝ (Euc 8))
    have hrn := LinearMap.finrank_range_add_finrank_ker
      ((mfderiv (𝓡 8) (𝓡 (8 + k)) E.e x).toLinearMap)
    rw [LinearMap.ker_eq_bot.mpr (E.injective_mfderiv x)] at hrn
    simp only [finrank_bot, add_zero] at hrn
    change Module.finrank ℝ ↥((mfderiv (𝓡 8) (𝓡 (8 + k)) E.e x).toLinearMap.range) = 8
    rw [hrn]
    exact finrank_euclideanSpace_fin
  have hfinS : Module.finrank ℝ ↥(Submodule.span ℝ (Set.range (tanFrame E i x))) = 8 := by
    have hli := frame_linearIndependent (f := E.e) (hf := embedding_contMDiff E)
      (hinj := E.injective_mfderiv) (coverChart i) hsrc
    change Module.finrank ℝ ↥(Submodule.span ℝ (Set.range (frame E.e (coverChart i) x))) = 8
    rw [finrank_span_eq_card hli]
    simp
  refine Submodule.eq_of_le_of_finrank_eq ?_ (by rw [hfinS, hfinT])
  refine Submodule.span_le.mpr ?_
  rintro v ⟨a, rfl⟩
  exact tanFrame_mem_tangentSpace E ND i hx a

/-- The pair frame of the tangent chart frame and the normal frame is linearly independent. -/
theorem linearIndependent_pairFrame (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i : CoverIdx V k) {x : V.pt} (hx : x ∈ ND.D.baseSet i) :
    LinearIndependent ℝ (pairFrame (tanFrame E i x) (Work.Tubular.orthFrame E ND i x)) := by
  have hF := frame_linearIndependent (f := E.e) (hf := embedding_contMDiff E)
    (hinj := E.injective_mfderiv) (coverChart i) (ND.baseSet_sub i.1 i.2 x hx)
  have hG := (Work.Tubular.orthFrame_orthonormal E ND i hx).linearIndependent
  rw [pairFrame, linearIndependent_sum]
  refine ⟨?_, ?_, ?_⟩
  · change LinearIndependent ℝ (tanFrame E i x)
    exact hF
  · change LinearIndependent ℝ (Work.Tubular.orthFrame E ND i x)
    exact hG
  · refine (disjoint_iff).mpr ?_
    change Submodule.span ℝ (Set.range (tanFrame E i x)) ⊓
      Submodule.span ℝ (Set.range (Work.Tubular.orthFrame E ND i x)) = ⊥
    rw [span_tanFrame E ND i hx, Work.Tubular.span_orthFrame E ND i hx,
      Work.Tubular.tangentSpace_inf_normalSpace]

/-- The pair frame of the tangent chart frame and the normal frame spans the ambient space. -/
theorem span_pairFrame (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i : CoverIdx V k) {x : V.pt} (hx : x ∈ ND.D.baseSet i) :
    Submodule.span ℝ (Set.range (pairFrame (tanFrame E i x) (Work.Tubular.orthFrame E ND i x)))
      = ⊤ := by
  have hrange : Set.range (Sum.elim (tanFrame E i x) (Work.Tubular.orthFrame E ND i x))
      = Set.range (tanFrame E i x) ∪ Set.range (Work.Tubular.orthFrame E ND i x) := by
    ext v; constructor
    · rintro ⟨c, rfl⟩
      rcases c with a | b
      · exact Or.inl ⟨a, rfl⟩
      · exact Or.inr ⟨b, rfl⟩
    · rintro (⟨a, rfl⟩ | ⟨b, rfl⟩)
      · exact ⟨Sum.inl a, rfl⟩
      · exact ⟨Sum.inr b, rfl⟩
  rw [pairFrame, hrange, Submodule.span_union, span_tanFrame E ND i hx,
    Work.Tubular.span_orthFrame E ND i hx, Work.Tubular.tangentSpace_sup_normalSpace]

end

end Work.ThomBordism
