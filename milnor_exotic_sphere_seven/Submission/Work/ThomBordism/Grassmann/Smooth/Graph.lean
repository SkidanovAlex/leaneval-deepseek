import Mathlib
import Submission.Work.ThomBordism.Grassmann.Smooth.Plumbing

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

/-!
# The graph of a linear map `ℝ^k → ℝ^m` inside `ℝ^{k+m}`

For `S : ChartIdx k m` and a linear map `c : ℝ^k → ℝ^m` we consider the graph of `c` in
`ℝ^{k+m}`, realized as the image of the linear map `graphMap S c = inclS S + inclC S ∘ c`.  Its
Gram–Schmidt orthonormalisation `graphFrame S c` is an orthonormal frame of the graph, and hence a
point `graphPoint S c` of the oriented Grassmannian: this is the inverse of the graph chart.
-/

open scoped Topology

namespace Work.ThomBordism.Grassmann.Smooth

noncomputable section

variable {k m : ℕ}

/-! ## Apply-forms of the plumbing identities -/

@[simp] theorem projS_inclS_apply (S : ChartIdx k m) (v : Amb k) : projS S (inclS S v) = v := by
  have h := congrFun (congrArg (fun f : Amb k →L[ℝ] Amb k => (⇑f)) (projS_inclS S)) v
  simpa using h

@[simp] theorem projC_inclS_apply (S : ChartIdx k m) (v : Amb k) : projC S (inclS S v) = 0 := by
  have h := congrFun (congrArg (fun f : Amb k →L[ℝ] Amb m => (⇑f)) (projC_inclS S)) v
  simpa using h

@[simp] theorem projS_inclC_apply (S : ChartIdx k m) (v : Amb m) : projS S (inclC S v) = 0 := by
  have h := congrFun (congrArg (fun f : Amb m →L[ℝ] Amb k => (⇑f)) (projS_inclC S)) v
  simpa using h

@[simp] theorem projC_inclC_apply (S : ChartIdx k m) (v : Amb m) : projC S (inclC S v) = v := by
  have h := congrFun (congrArg (fun f : Amb m →L[ℝ] Amb m => (⇑f)) (projC_inclC S)) v
  simpa using h

/-! ## The standard basis decomposition -/

/-- A vector of `ℝⁿ` is the sum of its coordinates times the standard basis vectors. -/
theorem sum_single_smul (n : ℕ) (v : Amb n) :
    (∑ i : Fin n, v i • EuclideanSpace.single i 1) = v := by
  refine WithLp.ofLp_injective 2 ?_
  have h1 : (ofLpCLM n (∑ i : Fin n, v i • EuclideanSpace.single i 1))
      = ∑ i : Fin n, v i • (Pi.single i (1 : ℝ) : Fin n → ℝ) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul]
    congr 1
  rw [show (∑ i : Fin n, v i • EuclideanSpace.single i 1).ofLp
      = ofLpCLM n (∑ i : Fin n, v i • EuclideanSpace.single i 1) from rfl, h1]
  funext x
  rw [Finset.sum_apply, Finset.sum_eq_single x]
  · rw [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
  · intro y _ hy; rw [Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hy), smul_zero]
  · intro hx; exact absurd (Finset.mem_univ x) hx

/-! ## The graph -/

/-- The graph of `c`, as a linear map `ℝ^k → ℝ^{k+m}`. -/
def graphMap (S : ChartIdx k m) (c : Amb k →L[ℝ] Amb m) : Amb k →L[ℝ] Amb (k + m) :=
  inclS S + (inclC S).comp c

@[simp] theorem graphMap_apply (S : ChartIdx k m) (c : Amb k →L[ℝ] Amb m) (v : Amb k) :
    graphMap S c v = inclS S v + inclC S (c v) := rfl

@[simp] theorem projS_graphMap (S : ChartIdx k m) (c : Amb k →L[ℝ] Amb m) (v : Amb k) :
    projS S (graphMap S c v) = v := by
  rw [graphMap_apply, map_add, projS_inclS_apply, projS_inclC_apply, add_zero]

@[simp] theorem projC_graphMap (S : ChartIdx k m) (c : Amb k →L[ℝ] Amb m) (v : Amb k) :
    projC S (graphMap S c v) = c v := by
  rw [graphMap_apply, map_add, projC_inclS_apply, projC_inclC_apply, zero_add]

theorem graphMap_injective (S : ChartIdx k m) (c : Amb k →L[ℝ] Amb m) :
    Function.Injective (graphMap S c) := by
  intro v w h
  have h1 := congrArg (projS S) h
  rwa [projS_graphMap, projS_graphMap] at h1

/-- The graph vectors: the images of the standard basis under `graphMap S c`. -/
def graphVec (S : ChartIdx k m) (c : Amb k →L[ℝ] Amb m) (i : Fin k) : Amb (k + m) :=
  graphMap S c (EuclideanSpace.single i 1)

@[simp] theorem projS_graphVec (S : ChartIdx k m) (c : Amb k →L[ℝ] Amb m) (i : Fin k) :
    projS S (graphVec S c i) = EuclideanSpace.single i 1 :=
  projS_graphMap S c _

theorem linearIndependent_graphVec (S : ChartIdx k m) (c : Amb k →L[ℝ] Amb m) :
    LinearIndependent ℝ (graphVec S c) := by
  have h := (EuclideanSpace.orthonormal_single (𝕜 := ℝ) (ι := Fin k)).linearIndependent
  have h2 := h.map' (graphMap S c).toLinearMap
    ((LinearMap.ker_eq_bot).mpr (graphMap_injective S c))
  change LinearIndependent ℝ (((graphMap S c).toLinearMap) ∘
    (fun i : Fin k => EuclideanSpace.single i 1))
  exact h2

theorem frameMatrix_graphVec (S : ChartIdx k m) (c : Amb k →L[ℝ] Amb m) :
    frameMatrix S (graphVec S c) = (1 : Matrix (Fin k) (Fin k) ℝ) := by
  ext i j
  have h : frameMatrix S (graphVec S c) i j = (projS S (graphVec S c j)) i := by
    rw [projS_apply_amb]
    rfl
  rw [h, projS_graphVec, EuclideanSpace.single_apply]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, Matrix.one_apply_eq]
  · rw [if_neg hij, Matrix.one_apply_ne hij]

/-- The Gram–Schmidt orthonormalisation of the graph vectors. -/
noncomputable def graphFrame (S : ChartIdx k m) (c : Amb k →L[ℝ] Amb m) : Fin k → Amb (k + m) :=
  InnerProductSpace.gramSchmidtNormed ℝ (graphVec S c)

theorem orthonormal_graphFrame (S : ChartIdx k m) (c : Amb k →L[ℝ] Amb m) :
    Orthonormal ℝ (graphFrame S c) :=
  InnerProductSpace.gramSchmidtNormed_orthonormal (linearIndependent_graphVec S c)

theorem span_graphFrame_eq (S : ChartIdx k m) (c : Amb k →L[ℝ] Amb m) :
    Submodule.span ℝ (Set.range (graphFrame S c)) = Submodule.span ℝ (Set.range (graphVec S c)) := by
  rw [graphFrame, InnerProductSpace.span_gramSchmidtNormed_range,
    InnerProductSpace.span_gramSchmidt]

/-- The graph of `c`, with the orientation of the graph basis, as a point of the oriented
Grassmannian. -/
noncomputable def graphPoint (S : ChartIdx k m) (c : Amb k →L[ℝ] Amb m) : OG k m :=
  Quotient.mk'' (⟨graphFrame S c, orthonormal_graphFrame S c⟩ : Stiefel k m)

theorem graphMap_mem_span_graphFrame (S : ChartIdx k m) (c : Amb k →L[ℝ] Amb m) (v : Amb k) :
    graphMap S c v ∈ Submodule.span ℝ (Set.range (graphFrame S c)) := by
  have hv : v = ∑ i : Fin k, v i • EuclideanSpace.single i 1 := (sum_single_smul k v).symm
  have h1 : graphMap S c v = ∑ i : Fin k, v i • graphVec S c i := by
    conv_lhs => rw [hv]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul]; rfl
  rw [h1, span_graphFrame_eq]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
    (Submodule.subset_span ⟨i, rfl⟩)

end

end Work.ThomBordism.Grassmann.Smooth
