import Submission.Work.ThomBordism.PontryaginThom.ComplementCont

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# The complement bundle of a family of planes: the gluing data

This file turns the pointwise linear algebra of `Complement.lean`/`ComplementCont.lean` into a
**real vector bundle** (gluing data, `Work.TangentClasses.RealBundle` = Mathlib's
`VectorBundleCore`): the complement of a family of rank-`8` planes in `ℝ^{k+8}`, varying over a
cover of a topological space `X`.

The data is a family, indexed by the charts `i : ι` of a cover `U i`, of

* a projection `P i x : ℝ^{k+8} →L[ℝ] ℝ^k` (the projection onto the complement along the plane),
* an insertion `I i x : ℝ^k →L[ℝ] ℝ^{k+8}` (its right inverse, `P i x ∘ I i x = id`),

continuous on `U i`, with the *single* geometric hypothesis that all the projections at a point have
the *same* kernel (`ker_agree`): the planes at `x` coincide, which is what the geometry of an
immersion supplies (the images of `d f_x` in different charts are the same subspace of the ambient
space).

The **transition function** from the chart `i` to the chart `j` of the complement bundle is
`coordChange i j x = P j x ∘ I i x` (`ComplementData.toRealBundle`), and the cocycle identity is
`cocycle_of_projections`: it uses `P j ∘ I j = id` and `ker P j = ker P l` only, through the
elementary fact that `I j (P j y) - y ∈ ker P j`.

With `P i x = planeProj (A i x) S i h` and `I i x = planeInj (A i x) S i h` (`Complement.lean`,
`ker_planeProj` supplies `ker P = range (coeffMap A)`), this is precisely the normal bundle of an
immersion `V ↪ ℝ^{k+8}` restricted to the complement; the remaining work of the construction is to
produce `P`, `I` from the immersion (the frames `A i x` of `im d f_x` in the chart `i`, their
continuity and the agreement of their spans), and then the isomorphism
`TV ⊕ ν ≅ ε^{k+8}`, which is the gluing form of the splitting `ℝ^{k+8} = im d f_x ⊕ ν_x`.
-/

open scoped Topology

namespace Work.ThomBordism.PontryaginThom

open Work.ThomBordism.Grassmann Work.TangentClasses

noncomputable section

variable {X : Type*} [TopologicalSpace X] {k : ℕ} {ι : Type*}

/-! ## The abstract cocycle identity -/

/-- **The cocycle identity of two projections with the same kernel** (linear-map form).  Let `P₂`,
`P₃` be maps of `E` to `F` with the same kernel and `I₁`, `I₂` right inverses of `P₁`, `P₂`.  Then
`(P₃ ∘ I₂) ∘ (P₂ ∘ I₁) = P₃ ∘ I₁`: the transition functions of the complement bundle of a *single*
plane compose.

The proof is the elementary computation `I₂ (P₂ (I₁ v)) - I₁ v ∈ ker P₂ = ker P₃`, i.e.
`P₃ (I₂ (P₂ (I₁ v))) = P₃ (I₁ v)`. -/
theorem cocycle_of_projections {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F]
    [Module ℝ F] (P₁ P₂ P₃ : E →ₗ[ℝ] F) (I₁ I₂ : F →ₗ[ℝ] E)
    (h₁ : P₁.comp I₁ = 1) (h₂ : P₂.comp I₂ = 1)
    (hker : LinearMap.ker P₂ = LinearMap.ker P₃) :
    (P₃.comp I₂).comp (P₂.comp I₁) = P₃.comp I₁ := by
  apply LinearMap.ext
  intro v
  have h2v : P₂ (I₂ (P₂ (I₁ v))) = P₂ (I₁ v) := by
    have h := congrFun (congrArg DFunLike.coe h₂) (P₂ (I₁ v))
    simpa using h
  have hmem : I₂ (P₂ (I₁ v)) - I₁ v ∈ LinearMap.ker P₂ := by
    rw [LinearMap.mem_ker, map_sub, h2v, sub_self]
  rw [hker] at hmem
  have h0 : P₃ (I₂ (P₂ (I₁ v))) = P₃ (I₁ v) := by
    rw [LinearMap.mem_ker, map_sub] at hmem
    exact sub_eq_zero.mp hmem
  simpa using h0

/-- **The cocycle identity of two projections with the same kernel** (continuous-linear-map form):
the version used for the gluing data of the complement bundle. -/
theorem cocycle_of_projections_clm {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (P₁ P₂ P₃ : E →L[ℝ] F) (I₁ I₂ : F →L[ℝ] E)
    (h₁ : P₁.comp I₁ = ContinuousLinearMap.id ℝ F)
    (h₂ : P₂.comp I₂ = ContinuousLinearMap.id ℝ F)
    (hker : LinearMap.ker (P₂ : E →ₗ[ℝ] F) = LinearMap.ker (P₃ : E →ₗ[ℝ] F)) :
    (P₃.comp I₂).comp (P₂.comp I₁) = P₃.comp I₁ := by
  have hLM := cocycle_of_projections (P₁ := (P₁ : E →ₗ[ℝ] F)) (P₂ := (P₂ : E →ₗ[ℝ] F))
    (P₃ := (P₃ : E →ₗ[ℝ] F)) (I₁ := (I₁ : F →ₗ[ℝ] E)) (I₂ := (I₂ : F →ₗ[ℝ] E))
    (by ext v; simpa using congrFun (congrArg DFunLike.coe h₁) v)
    (by ext v; simpa using congrFun (congrArg DFunLike.coe h₂) v)
    hker
  refine ContinuousLinearMap.ext fun v => ?_
  exact congrFun (congrArg DFunLike.coe hLM) v

/-! ## The complement bundle -/

/-- **The data of a rank-`k` complement over a cover**: projections `P i x` and insertions `I i x`
of the complement of a plane in `ℝ^{k+8}`, continuous on the open sets `U i`, with
`P i x ∘ I i x = id` and with *all the projections at a point having the same kernel* (the plane is
the same in every chart). -/
structure ComplementData (X : Type*) [TopologicalSpace X] (k : ℕ) (ι : Type*) where
  /-- the open cover -/
  baseSet : ι → Set X
  isOpen_baseSet : ∀ i, IsOpen (baseSet i)
  /-- a chosen index over each point -/
  indexAt : X → ι
  mem_baseSet_at : ∀ x, x ∈ baseSet (indexAt x)
  /-- the projection onto the complement along the plane -/
  P : ∀ i, X → (Fin (8 + k) → ℝ) →L[ℝ] (Fin k → ℝ)
  /-- the insertion of the complement -/
  I : ∀ i, X → (Fin k → ℝ) →L[ℝ] (Fin (8 + k) → ℝ)
  continuousOn_P : ∀ i, ContinuousOn (fun x => P i x) (baseSet i)
  continuousOn_I : ∀ i, ContinuousOn (fun x => I i x) (baseSet i)
  /-- the insertion is a right inverse of the projection -/
  P_comp_I : ∀ i x, (P i x).comp (I i x) = ContinuousLinearMap.id ℝ (Fin k → ℝ)
  /-- the plane is the same in every chart -/
  ker_agree : ∀ i j x, x ∈ baseSet i → x ∈ baseSet j →
    LinearMap.ker ((P i x : (Fin (8 + k) → ℝ) →ₗ[ℝ] (Fin k → ℝ)))
      = LinearMap.ker ((P j x : (Fin (8 + k) → ℝ) →ₗ[ℝ] (Fin k → ℝ)))

namespace ComplementData

variable (D : ComplementData X k ι)

/-- The transition function of the complement bundle of `D`: `P j x ∘ I i x` on the overlap of the
charts `i` and `j`, and `0` outside it (where the transition function is never used). -/
noncomputable def coordChange (i j : ι) (x : X) : (Fin k → ℝ) →L[ℝ] (Fin k → ℝ) := by
  classical
  exact if x ∈ D.baseSet i ∧ x ∈ D.baseSet j then (D.P j x).comp (D.I i x) else 0

/-- The computation rule of the transition function, on the overlap. -/
theorem coordChange_of_mem (i j : ι) (x : X) (hx : x ∈ D.baseSet i ∧ x ∈ D.baseSet j) :
    D.coordChange i j x = (D.P j x).comp (D.I i x) := by
  classical
  rw [coordChange, if_pos hx]

/-- The transition function vanishes outside the overlap. -/
theorem coordChange_of_notMem (i j : ι) (x : X)
    (hx : ¬ (x ∈ D.baseSet i ∧ x ∈ D.baseSet j)) : D.coordChange i j x = 0 := by
  classical
  rw [coordChange, if_neg hx]

/-- The transition function is continuous on the overlap: it is `x ↦ (P j x).comp (I i x)`. -/
theorem continuousOn_coordChange (i j : ι) :
    ContinuousOn (D.coordChange i j) (D.baseSet i ∩ D.baseSet j) := by
  have hP : ContinuousOn (fun x => D.P j x) (D.baseSet i ∩ D.baseSet j) :=
    (D.continuousOn_P j).mono Set.inter_subset_right
  have hI : ContinuousOn (fun x => D.I i x) (D.baseSet i ∩ D.baseSet j) :=
    (D.continuousOn_I i).mono Set.inter_subset_left
  have hmain : ContinuousOn (fun x =>
      (ContinuousLinearMap.compL ℝ (Fin k → ℝ) (Fin (8 + k) → ℝ) (Fin k → ℝ))
        (D.P j x) (D.I i x)) (D.baseSet i ∩ D.baseSet j) :=
    (continuousOn_const.clm_apply hP).clm_apply hI
  refine hmain.congr (fun x hx => ?_)
  rw [D.coordChange_of_mem i j x hx]
  simp only [ContinuousLinearMap.compL_apply]

/-- **The complement bundle** of the data `D`: the transition function from the chart `i` to the
chart `j` is `P j x ∘ I i x`. -/
noncomputable def toRealBundle : RealBundle X (Fin k → ℝ) ι where
  baseSet := D.baseSet
  isOpen_baseSet := D.isOpen_baseSet
  indexAt := D.indexAt
  mem_baseSet_at := D.mem_baseSet_at
  coordChange := D.coordChange
  coordChange_self i x hx v := by
    rw [D.coordChange_of_mem i i x ⟨hx, hx⟩, D.P_comp_I i x]
    rfl
  continuousOn_coordChange := D.continuousOn_coordChange
  coordChange_comp i j l x hx v := by
    have hx1 : x ∈ D.baseSet i := hx.1.1
    have hx2 : x ∈ D.baseSet j := hx.1.2
    have hx3 : x ∈ D.baseSet l := hx.2
    rw [D.coordChange_of_mem i j x ⟨hx1, hx2⟩, D.coordChange_of_mem j l x ⟨hx2, hx3⟩,
      D.coordChange_of_mem i l x ⟨hx1, hx3⟩]
    have h := cocycle_of_projections_clm (P₁ := D.P i x) (P₂ := D.P j x) (P₃ := D.P l x)
      (I₁ := D.I i x) (I₂ := D.I j x) (D.P_comp_I i x) (D.P_comp_I j x)
      (D.ker_agree j l x hx2 hx3)
    simpa using congrFun (congrArg DFunLike.coe h) v

@[simp] theorem toRealBundle_baseSet (i : ι) : D.toRealBundle.baseSet i = D.baseSet i := rfl

@[simp] theorem toRealBundle_indexAt (x : X) : D.toRealBundle.indexAt x = D.indexAt x := rfl

@[simp] theorem toRealBundle_coordChange (i j : ι) (x : X) :
    D.toRealBundle.coordChange i j x = D.coordChange i j x := rfl

/-- The complement bundle has rank `k` (the fibre is `ℝ^k`). -/
theorem toRealBundle_rank : D.toRealBundle.rank = k := by
  rw [RealBundle.rank, Module.finrank_fin_fun]

/-- The kernel of the projection `P i x` is the plane at `x`; `ker_agree` says it does not depend
on the chart. -/
theorem ker_eq (i j : ι) (x : X) (hx : x ∈ D.baseSet i) (hy : x ∈ D.baseSet j) :
    LinearMap.ker ((D.P i x : (Fin (8 + k) → ℝ) →ₗ[ℝ] (Fin k → ℝ)))
      = LinearMap.ker ((D.P j x : (Fin (8 + k) → ℝ) →ₗ[ℝ] (Fin k → ℝ))) :=
  D.ker_agree i j x hx hy

end ComplementData

end

end Work.ThomBordism.PontryaginThom
