import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-!
# Adjoint of the adjoint of a closed densely defined operator

For a densely defined closed partially defined linear operator `T` between complete inner
product spaces we prove `T†† = T`.

The proof goes through the graph: `T†.graph = T.graph.adjoint`, and the double `adjoint` of a
closed submodule (w.r.t. the `Submodule.adjoint` operation on graphs) is the submodule itself.
-/


open WithLp

noncomputable section

namespace Commons.Analysis.InnerProductSpace.LinearPMap

variable {𝕜 X Y : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [InnerProductSpace 𝕜 X]
  [NormedAddCommGroup Y] [InnerProductSpace 𝕜 Y]

/-- `WithLp.toLp` as a linear map. -/
abbrev toLpLM : X × Y →ₗ[𝕜] WithLp 2 (X × Y) :=
  (WithLp.linearEquiv 2 𝕜 (X × Y)).symm.toLinearMap

/-- `WithLp.ofLp` as a linear map. -/
abbrev ofLpLM : WithLp 2 (X × Y) →ₗ[𝕜] X × Y :=
  (WithLp.linearEquiv 2 𝕜 (X × Y)).toLinearMap

/-- The swap-and-sign map `(x, y) ↦ (-y, x)` between `L²` products, as a linear isometry
equivalence. -/
def witJ : WithLp 2 (X × Y) ≃ₗᵢ[𝕜] WithLp 2 (Y × X) :=
  LinearEquiv.isometryOfInner
    ((WithLp.linearEquiv 2 𝕜 (X × Y)).trans
      ((LinearEquiv.skewSwap 𝕜 X Y).trans (WithLp.linearEquiv 2 𝕜 (Y × X)).symm))
    (by
      intro x y
      simp only [LinearEquiv.trans_apply, LinearEquiv.skewSwap_apply, WithLp.coe_linearEquiv,
        WithLp.coe_symm_linearEquiv]
      rw [WithLp.prod_inner_apply, WithLp.prod_inner_apply]
      simp only
      rw [inner_neg_left, inner_neg_right]
      ring)

lemma witJ_toLp (p : X × Y) :
    (witJ (𝕜 := 𝕜) (X := X) (Y := Y)) (WithLp.toLp 2 p) =
      WithLp.toLp 2 (LinearEquiv.skewSwap 𝕜 X Y p) := by
  simp [witJ, LinearEquiv.trans_apply]

lemma ofLp_comp_toLp :
    (toLpLM (𝕜 := 𝕜) (X := X) (Y := Y)).comp (ofLpLM (𝕜 := 𝕜) (X := X) (Y := Y)) =
      LinearMap.id := by
  apply LinearMap.ext; intro x; rfl

lemma toLp_comp_ofLp :
    (ofLpLM (𝕜 := 𝕜) (X := X) (Y := Y)).comp (toLpLM (𝕜 := 𝕜) (X := X) (Y := Y)) =
      LinearMap.id := by
  apply LinearMap.ext; intro x; rfl

lemma witJ_comp_apply (x : WithLp 2 (X × Y)) :
    (witJ (𝕜:=𝕜) (X:=Y) (Y:=X)) ((witJ (𝕜:=𝕜) (X:=X) (Y:=Y)) x) = -x := by
  conv_lhs => rw [← WithLp.toLp_ofLp 2 x]
  rw [witJ_toLp (𝕜:=𝕜) (X:=X) (Y:=Y), witJ_toLp (𝕜:=𝕜) (X:=Y) (Y:=X)]
  rw [← WithLp.toLp_neg]
  congr 1

lemma witJ_comp :
    ((witJ (𝕜:=𝕜) (X:=Y) (Y:=X)).toLinearEquiv.toLinearMap).comp
      ((witJ (𝕜:=𝕜) (X:=X) (Y:=Y)).toLinearEquiv.toLinearMap) = - LinearMap.id := by
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, LinearMap.neg_apply, LinearMap.id_apply,
    LinearEquiv.coe_toLinearMap, LinearIsometryEquiv.coe_toLinearEquiv]
  exact witJ_comp_apply x

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- Image of the graph-adjoint of a submodule under `WithLp.toLp`, expressed as an orthogonal
complement of the image of the submodule, transported by the swap isometry `witJ`. -/
theorem submodule_adjoint_map_toLp (g : Submodule 𝕜 (E × F)) :
    (Submodule.adjoint g).map (toLpLM (𝕜 := 𝕜) (X := F) (Y := E))
      = ((g.map (toLpLM (𝕜 := 𝕜) (X := E) (Y := F))).orthogonal).map
          ((witJ (𝕜 := 𝕜) (X := E) (Y := F)).toLinearEquiv.toLinearMap) := by
  rw [Submodule.adjoint]
  rw [← Submodule.map_comp]
  have hid : (toLpLM (𝕜 := 𝕜) (X := F) (Y := E)).comp
      (ofLpLM (𝕜 := 𝕜) (X := F) (Y := E)) = LinearMap.id := ofLp_comp_toLp
  rw [hid, Submodule.map_id]
  have h : ((LinearEquiv.skewSwap 𝕜 F E).symm.trans
        (WithLp.linearEquiv 2 𝕜 (F × E)).symm).toLinearMap
      = - ((witJ (𝕜 := 𝕜) (X := E) (Y := F)).toLinearEquiv.toLinearMap.comp
            (toLpLM (𝕜 := 𝕜) (X := E) (Y := F))) := by
    apply LinearMap.ext
    intro p
    obtain ⟨a,b⟩ := p
    simp only [LinearMap.neg_apply, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      LinearEquiv.trans_apply, LinearEquiv.skewSwap_symm_apply, WithLp.coe_symm_linearEquiv,
      toLpLM]
    change WithLp.toLp 2 (b, -a) = - ((witJ (𝕜 := 𝕜) (X := E) (Y := F)) (WithLp.toLp 2 (a, b)))
    rw [witJ_toLp, ← WithLp.toLp_neg]
    congr 1
    ext <;> simp
  rw [h, Submodule.map_neg, Submodule.map_comp]
  rw [Submodule.map_orthogonal_equiv]

/-- Taking images under `WithLp.toLp` commutes with taking topological closures. -/
lemma map_topologicalClosure_toLp (g : Submodule 𝕜 (E × F)) :
    (g.map (toLpLM (𝕜 := 𝕜) (X := E) (Y := F))).topologicalClosure
      = (g.topologicalClosure).map (toLpLM (𝕜 := 𝕜) (X := E) (Y := F)) := by
  apply SetLike.ext
  intro x
  show x ∈ ((g.map (toLpLM (𝕜 := 𝕜) (X := E) (Y := F))).topologicalClosure :
      Set (WithLp 2 (E × F))) ↔
    x ∈ (((g.topologicalClosure).map (toLpLM (𝕜 := 𝕜) (X := E) (Y := F))) :
      Set (WithLp 2 (E × F)))
  simp only [Submodule.topologicalClosure_coe, Submodule.map_coe]
  change x ∈ closure ((WithLp.homeomorphProd 2 E F).symm '' (g : Set (E × F))) ↔
    x ∈ (WithLp.homeomorphProd 2 E F).symm '' closure (g : Set (E × F))
  rw [← (WithLp.homeomorphProd 2 E F).symm.image_closure]

/-- The double `Submodule.adjoint` of a submodule is the topological closure of the submodule. -/
theorem submodule_adjoint_adjoint_eq_topologicalClosure (g : Submodule 𝕜 (E × F))
    [CompleteSpace E] [CompleteSpace F] :
    (Submodule.adjoint g).adjoint = g.topologicalClosure := by
  have h1 := submodule_adjoint_map_toLp (𝕜 := 𝕜) g
  have h2 := submodule_adjoint_map_toLp (𝕜 := 𝕜) (Submodule.adjoint g)
  rw [h1] at h2
  rw [Submodule.map_orthogonal_equiv] at h2
  rw [← Submodule.map_comp] at h2
  rw [witJ_comp] at h2
  rw [Submodule.map_neg, Submodule.map_id, Submodule.orthogonal_orthogonal_eq_closure] at h2
  have h3 := congrArg (Submodule.map (ofLpLM (𝕜 := 𝕜) (X := E) (Y := F))) h2
  rw [← Submodule.map_comp, toLp_comp_ofLp, Submodule.map_id] at h3
  rw [h3, map_topologicalClosure_toLp, ← Submodule.map_comp, toLp_comp_ofLp, Submodule.map_id]

/-- The adjoint of a densely defined closed operator is densely defined. -/
theorem dense_domain_adjoint {T : E →ₗ.[𝕜] F} [CompleteSpace E] [CompleteSpace F]
    (hT : Dense (T.domain : Set E)) (hTc : T.IsClosed) : Dense (T.adjoint.domain : Set F) := by
  have hbot : (T.adjoint.domain)ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro z hz
    have hxg : (0, z) ∈ (T.adjoint.graph).adjoint := by
      rw [Submodule.mem_adjoint_iff]
      intro a b hab
      have haz : a ∈ T.adjoint.domain := by
        rw [LinearPMap.mem_graph_iff] at hab
        obtain ⟨y, hy1, _⟩ := hab
        have hy1' : (y : F) = a := by simpa using hy1
        rw [← hy1']
        exact y.2
      have hza : inner 𝕜 a z = 0 := (Submodule.mem_orthogonal _ _).mp hz a haz
      simp [hza]
    have hK : (T.adjoint.graph).adjoint = T.graph := by
      rw [LinearPMap.adjoint_graph_eq_graph_adjoint hT]
      rw [submodule_adjoint_adjoint_eq_topologicalClosure, hTc.submodule_topologicalClosure_eq]
    have h0z : (0, z) ∈ T.graph := by rw [← hK]; exact hxg
    exact LinearPMap.graph_fst_eq_zero_snd T h0z rfl
  rw [Submodule.dense_iff_topologicalClosure_eq_top, ← Submodule.orthogonal_orthogonal_eq_closure,
    hbot, Submodule.bot_orthogonal_eq_top]

end Commons.Analysis.InnerProductSpace.LinearPMap

namespace Commons.Analysis.InnerProductSpace.LinearPMap

theorem adjoint_adjoint_of_isClosed {K E F : Type*} [RCLike K] [NormedAddCommGroup E] [InnerProductSpace K E] [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace K F] [CompleteSpace F] (T : LinearPMap (RingHom.id K) E F) (hT : Dense (T.domain : Set E)) (hTc : T.IsClosed) : LinearPMap.adjoint (LinearPMap.adjoint T) = T := by
  have hS : Dense (T.adjoint.domain : Set F) := dense_domain_adjoint hT hTc
  have hg : T.adjoint.adjoint.graph = T.graph := by
    rw [LinearPMap.adjoint_graph_eq_graph_adjoint hS]
    rw [LinearPMap.adjoint_graph_eq_graph_adjoint hT]
    rw [submodule_adjoint_adjoint_eq_topologicalClosure, hTc.submodule_topologicalClosure_eq]
  exact LinearPMap.eq_of_eq_graph hg

end Commons.Analysis.InnerProductSpace.LinearPMap