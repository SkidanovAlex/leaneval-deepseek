import Mathlib
import Submission.Work.PL.Defs
import Submission.Work.Engulf.Basic

namespace Work.Engulf.E4Aux


/-- **Consistency of the affine witnesses.**  Two affine maps which both realise `g` as `ψ ∘ A`
on the simplices of two faces and whose values on those simplices lie in the open unit cube agree
at every common vertex of the two faces.  This is the well-definedness step of
`exists_vertex_image`: at a vertex `v` of both faces, `ψ (A v) = g v = ψ (B v)`, and `ψ` is
injective on the open cube (`CubeChart.emb`). -/
lemma affine_witness_eq {n N : ℕ} {M : Type*} [TopologicalSpace M] {ψ : PL.CubeChart n M}
    {g : PL.E N → M}
    {s t : Finset (PL.E N)}
    {A B : PL.E N →ᵃ[ℝ] PL.E n}
    (hA : Set.EqOn g (fun x => ψ.toFun (A x)) (PL.simp s))
    (hB : Set.EqOn g (fun x => ψ.toFun (B x)) (PL.simp t))
    (hAc : ∀ x ∈ PL.simp s, A x ∈ PL.openCube 1)
    (hBc : ∀ x ∈ PL.simp t, B x ∈ PL.openCube 1)
    {v : PL.E N} (hvs : v ∈ s) (hvt : v ∈ t) : A v = B v := by
  have hv1 : v ∈ PL.simp s := Work.Engulf.subset_simp hvs
  have hv2 : v ∈ PL.simp t := Work.Engulf.subset_simp hvt
  have h1 : ψ.toFun (A v) = g v := (hA hv1).symm
  have h2 : g v = ψ.toFun (B v) := hB hv2
  have hinj : Set.InjOn ψ.toFun (PL.openCube (n := n) 1) := by
    intro x hx y hy h
    have h' : (PL.openCube (n := n) 1).domRestrict ψ.toFun ⟨x, hx⟩
        = (PL.openCube (n := n) 1).domRestrict ψ.toFun ⟨y, hy⟩ := h
    exact congrArg Subtype.val (ψ.emb.toIsEmbedding.injective h')
  exact hinj (hAc v hv1) (hBc v hv2) (by rw [h1, h2])

/-- **The vertex map of `E4a`** (needed to feed `GPaForm` and `VertexPerturbForm`).  Let `g : E N → M` be `ψ`-affine on every face of `K`, with the affine witnesses taking their values on `simp s` into the open unit cube (so that `ψ ∘ A` is the restriction of `g` to that face, as a map to `M`).  Then there is a single vertex map `y` on the vertex set of `K`, with values in the open unit cube, which on each face `s` evaluates at `v ∈ s` to the affine witness of `s`.  (Well-definedness at a vertex lying in two faces: `ψ (A v) = g v = ψ (B v)` and `ψ` is injective on the open cube.) -/
theorem exists_vertex_image {n N : ℕ} {M : Type*} [TopologicalSpace M]
    {ψ : PL.CubeChart n M} {K : PL.Cx N} (hKfin : K.faces.Finite)
    {g : PL.E N → M}
    (haff : ∀ s ∈ K.faces, ∃ A : PL.E N →ᵃ[ℝ] PL.E n,
      Set.EqOn g (fun x => ψ.toFun (A x)) (PL.simp s) ∧ ∀ x ∈ PL.simp s, A x ∈ PL.openCube 1) :
    ∃ y : ↥(hKfin.toFinset.biUnion id) → PL.E n,
      (∀ v, y v ∈ PL.openCube 1) ∧
      ∀ s (hs : s ∈ K.faces), ∃ A : PL.E N →ᵃ[ℝ] PL.E n,
        Set.EqOn g (fun x => ψ.toFun (A x)) (PL.simp s) ∧
        (∀ x ∈ PL.simp s, A x ∈ PL.openCube 1) ∧
        ∀ v (hv : v ∈ s),
          y ⟨v, Finset.mem_biUnion.mpr ⟨s, (Set.Finite.mem_toFinset hKfin).mpr hs, hv⟩⟩ = A v := by
  classical
  -- The vertex set of `K`: the union of all faces.
  let V : Finset (PL.E N) := hKfin.toFinset.biUnion id
  -- Every vertex lies on some face, and conversely.
  have hmem : ∀ v : ↥V, ∃ s ∈ K.faces, (v : PL.E N) ∈ s := by
    intro v
    obtain ⟨s, hs, hv⟩ := Finset.mem_biUnion.mp v.2
    exact ⟨s, (Set.Finite.mem_toFinset hKfin).mp hs, hv⟩
  -- A chosen face through each vertex and its affine witness from `haff`.
  let faceOf : ↥V → Finset (PL.E N) := fun v => Classical.choose (hmem v)
  have faceOf_mem : ∀ v, faceOf v ∈ K.faces := fun v => (Classical.choose_spec (hmem v)).1
  have mem_faceOf : ∀ v, (v : PL.E N) ∈ faceOf v := fun v => (Classical.choose_spec (hmem v)).2
  let witOf : ↥V → PL.E N →ᵃ[ℝ] PL.E n :=
    fun v => Classical.choose (haff (faceOf v) (faceOf_mem v))
  have witOf_spec : ∀ v, (Set.EqOn g (fun x => ψ.toFun (witOf v x)) (PL.simp (faceOf v)) ∧
      ∀ x ∈ PL.simp (faceOf v), witOf v x ∈ PL.openCube 1) :=
    fun v => Classical.choose_spec (haff (faceOf v) (faceOf_mem v))
  -- The vertex map: evaluate the chosen witness of a face through `v` at `v`.
  let y : ↥V → PL.E n := fun v => witOf v (v : PL.E N)
  have y_apply : ∀ v, y v = witOf v (v : PL.E N) := fun v => rfl
  refine ⟨y, ?_, ?_⟩
  · intro v
    exact (witOf_spec v).2 _ (Work.Engulf.subset_simp (mem_faceOf v))
  · -- Every face's own witness realises `g` on that face and agrees with `y` at its vertices.
    intro s hs
    refine ⟨Classical.choose (haff s hs), (Classical.choose_spec (haff s hs)).1,
      (Classical.choose_spec (haff s hs)).2, ?_⟩
    intro v hv
    rw [y_apply]
    exact affine_witness_eq (witOf_spec _).1 (Classical.choose_spec (haff s hs)).1
      (witOf_spec _).2 (Classical.choose_spec (haff s hs)).2 (mem_faceOf _) hv

end Work.Engulf.E4Aux
