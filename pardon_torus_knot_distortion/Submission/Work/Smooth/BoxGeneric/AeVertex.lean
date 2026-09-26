import Mathlib
import Submission.Work.Smooth.BoxGeneric.Defs
import Submission.Work.Smooth.BoxGeneric.AeMain
import Submission.Work.Smooth.BoxGeneric.Vertex.aeNoVertex_of_ae_centre
import Submission.Work.Smooth.BoxGeneric.Vertex.vertexDir_mem_fderiv_range_of_not_isolated
import Submission.Work.Smooth.BoxGeneric.LocalSurface.isLocalArcAt_of_vertex_tangent
import Submission.Work.Smooth.BoxGeneric.LocalSurface.isLocalArcAt_of_uniqueActiveFace
import Submission.Work.Smooth.BoxGeneric.LocalSurface.isLocalArcAt_of_corner
import Submission.Work.Smooth.BoxGeneric.LocalSurface.isLocalArcAt_of_tangentialCorner

/-!
# The vertex strata of the box spheres: almost every vertex point is tangential

The first version of the chapter excluded the vertices of the box by the genericity input
`Work.Smooth.BoxGeneric.AeNoVertex` ("for almost every level, no point of the surface is a vertex
of the box sphere").  That input is *not* needed.  At a vertex point of the surface the box sphere
is the corner cone `C = {v | max_i v_i = 0}` (in suitable coordinates), and

* if the vertex-ray direction `Work.Smooth.BoxGeneric.Vertex.vertexDir σ ε` is **tangent** to the
  surface at that point, then the opposite direction lies in the interior of the negative orthant,
  so `T_yF ∩ {v ≤ 0}` is a genuine sector and the level set is locally the union of the two branches
  of its boundary — a "V", which is a topological arc
  (`Work.Smooth.BoxGeneric.LocalSurface.isLocalArcAt_of_vertex_tangent`);
* if it is *not* tangent, then the vertex ray crosses the surface transversally at that point (the
  standard fact that a limit of secant directions is a tangent direction), so the level is an
  **isolated** point of the set `{s | boxVertex c σ ε s ∈ F}`; and the isolated points of a subset of
  `ℝ` are countable, hence null.

This file proves the second half — countability of the isolated points, and the resulting
almost-everywhere tangency of the vertex points (`AeVertexTangent`).  The first half is the local
model lemma `Submission.Work.Smooth.BoxGeneric.LocalSurface.isLocalArcAt_of_vertex_tangent`.
-/

open LeanEval.KnotTheory.PardonDistortion
open MeasureTheory Set

namespace Work.Smooth.BoxGeneric

noncomputable section

variable {ψ : Submission.Diffeo} {c : R3} {σ : Equiv.Perm (Fin 3)}

/-! ## The isolated points of a subset of `ℝ` are countable -/

/-- **The isolated points of a subset `A ⊆ ℝ` are countable.**  Each isolated point `s` has an open
interval meeting `A` only at `s`; if `q < s < r` are rationals inside that interval, the assignment
`s ↦ (q, r)` is injective, so the isolated points inject into `ℚ × ℚ`. -/
theorem countable_isolatedPoints (A : Set ℝ) :
    {s : ℝ | s ∈ A ∧ ∃ δ : ℝ, 0 < δ ∧ Set.Ioo (s - δ) (s + δ) ∩ A = {s}}.Countable := by
  have hcount : (⋃ qr : ℚ × ℚ, {s : ℝ | s ∈ A ∧ (qr.1 : ℝ) < s ∧ s < (qr.2 : ℝ) ∧
      Set.Ioo (qr.1 : ℝ) (qr.2 : ℝ) ∩ A = {s}}).Countable :=
    Set.countable_iUnion fun qr => Set.Subsingleton.countable fun x hx y hy => by
      rw [Set.mem_ofPred_eq] at hx hy
      have hy' : y ∈ Set.Ioo (qr.1 : ℝ) (qr.2 : ℝ) ∩ A := ⟨⟨hy.2.1, hy.2.2.1⟩, hy.1⟩
      rw [hx.2.2.2] at hy'
      exact (Set.mem_singleton_iff.mp hy').symm
  refine Set.Countable.mono ?_ hcount
  rintro s ⟨hsA, δ, hδ, hδA⟩
  obtain ⟨q, hq₁, hq₂⟩ := exists_rat_btwn (show s - δ < s by linarith)
  obtain ⟨r, hr₁, hr₂⟩ := exists_rat_btwn (show s < s + δ by linarith)
  refine Set.mem_iUnion.mpr ⟨(q, r), hsA, hq₂, hr₁, ?_⟩
  refine Set.Subset.antisymm ?_ ?_
  · intro x hx
    have hx' : x ∈ Set.Ioo (s - δ) (s + δ) ∩ A :=
      ⟨⟨lt_of_lt_of_le hq₁ (le_of_lt hx.1.1), lt_of_le_of_lt (le_of_lt hx.1.2) hr₂⟩, hx.2⟩
    rw [hδA] at hx'
    exact hx'
  · intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact ⟨⟨hq₂, hr₁⟩, hsA⟩

/-! ## Almost every vertex point is tangential -/

/-- **Almost every level has only tangential vertex points.**  For `ψ`, `c`, `σ`:

for almost every `s`, at every vertex point `boxVertex c σ ε s` of the surface (sign pattern
`ε : Fin 3 → {±1}`) the vertex-ray direction `Vertex.vertexDir σ ε` is *tangent* to the surface,
i.e. lies in the image of the derivative of the parametrisation at a parameter over that point. -/
def AeVertexTangent (ψ : Submission.Diffeo) (c : R3) (σ : Equiv.Perm (Fin 3)) : Prop :=
  ∀ᵐ s ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
    ∀ ε : Fin 3 → ℝ, (∀ i : Fin 3, ε i = 1 ∨ ε i = -1) →
      boxVertex c σ ε s ∈ (Work.Smooth.Morse.torus ψ).carrier →
        ∃ p : ℝ × ℝ, Work.Smooth.Morse.param ψ p = boxVertex c σ ε s ∧
          ∃ r : ℝ × ℝ, fderiv ℝ (Work.Smooth.Morse.param ψ) p r = Vertex.vertexDir σ ε

/-- **`AeVertexTangent` from the tangency step** "a non-isolated vertex point has a tangential
ray" (`Vertex.vertexDir_mem_fderiv_range_of_not_isolated`).  The bad levels are those at which some
vertex point is *isolated* in the set `{s | boxVertex c σ ε s ∈ F}`, and the isolated points of a
subset of `ℝ` are countable, hence null. -/
theorem aeVertexTangent_of_not_isolated (ψ : Submission.Diffeo) (c : R3)
    (σ : Equiv.Perm (Fin 3))
    (hstep : ∀ ε : Fin 3 → ℝ, (∀ i : Fin 3, ε i = 1 ∨ ε i = -1) → ∀ s : ℝ,
      boxVertex c σ ε s ∈ (Work.Smooth.Morse.torus ψ).carrier →
      (∀ δ : ℝ, 0 < δ → ∃ t : ℝ, t ≠ s ∧ |t - s| < δ ∧
        boxVertex c σ ε t ∈ (Work.Smooth.Morse.torus ψ).carrier) →
      ∃ p : ℝ × ℝ, Work.Smooth.Morse.param ψ p = boxVertex c σ ε s ∧
        ∃ r : ℝ × ℝ, fderiv ℝ (Work.Smooth.Morse.param ψ) p r = Vertex.vertexDir σ ε) :
    AeVertexTangent ψ c σ := by
  rw [AeVertexTangent, MeasureTheory.ae_iff]
  have hbad : {s : ℝ | ¬ (∀ ε : Fin 3 → ℝ, (∀ i : Fin 3, ε i = 1 ∨ ε i = -1) →
        boxVertex c σ ε s ∈ (Work.Smooth.Morse.torus ψ).carrier →
          ∃ p : ℝ × ℝ, Work.Smooth.Morse.param ψ p = boxVertex c σ ε s ∧
            ∃ r : ℝ × ℝ, fderiv ℝ (Work.Smooth.Morse.param ψ) p r = Vertex.vertexDir σ ε)} ⊆
      ⋃ ε ∈ {ε : Fin 3 → ℝ | ∀ i : Fin 3, ε i = 1 ∨ ε i = -1},
        {s : ℝ | s ∈ {s : ℝ | boxVertex c σ ε s ∈ (Work.Smooth.Morse.torus ψ).carrier} ∧
          ∃ δ : ℝ, 0 < δ ∧ Set.Ioo (s - δ) (s + δ) ∩
            {s : ℝ | boxVertex c σ ε s ∈ (Work.Smooth.Morse.torus ψ).carrier} = {s}} := by
    intro s hs
    rw [Set.mem_ofPred_eq] at hs
    rw [not_forall] at hs
    obtain ⟨ε, hs⟩ := hs
    rw [Classical.not_imp] at hs
    obtain ⟨hε, hs⟩ := hs
    rw [Classical.not_imp] at hs
    obtain ⟨hmem, hnotang⟩ := hs
    refine Set.mem_biUnion hε ⟨hmem, ?_⟩
    by_contra hiso
    refine hnotang (hstep ε hε s hmem fun δ hδ => ?_)
    have hne : Set.Ioo (s - δ) (s + δ) ∩
        {s' : ℝ | boxVertex c σ ε s' ∈ (Work.Smooth.Morse.torus ψ).carrier} ≠ {s} := by
      intro hcon
      exact hiso ⟨δ, hδ, hcon⟩
    have hsS : s ∈ Set.Ioo (s - δ) (s + δ) ∩
        {s' : ℝ | boxVertex c σ ε s' ∈ (Work.Smooth.Morse.torus ψ).carrier} :=
      ⟨⟨sub_lt_self s hδ, lt_add_of_pos_right s hδ⟩, hmem⟩
    obtain ⟨t, htS, htne⟩ : ∃ t, t ∈ Set.Ioo (s - δ) (s + δ) ∩
        {s' : ℝ | boxVertex c σ ε s' ∈ (Work.Smooth.Morse.torus ψ).carrier} ∧ t ≠ s := by
      by_contra hno
      push_neg at hno
      exact hne (Set.Subset.antisymm (fun x hx => by
          rw [Set.mem_singleton_iff]; exact hno x hx)
        (fun x hx => by
          rw [Set.mem_singleton_iff] at hx
          rw [hx]; exact hsS))
    refine ⟨t, htne, ?_, htS.2⟩
    have ht' := htS.1
    rw [Set.mem_Ioo] at ht'
    exact abs_lt.mpr ⟨by linarith, by linarith⟩
  refine MeasureTheory.measure_mono_null hbad ?_
  have hcount : (⋃ ε ∈ {ε : Fin 3 → ℝ | ∀ i : Fin 3, ε i = 1 ∨ ε i = -1},
      {s : ℝ | s ∈ {s : ℝ | boxVertex c σ ε s ∈ (Work.Smooth.Morse.torus ψ).carrier} ∧
        ∃ δ : ℝ, 0 < δ ∧ Set.Ioo (s - δ) (s + δ) ∩
          {s : ℝ | boxVertex c σ ε s ∈ (Work.Smooth.Morse.torus ψ).carrier} = {s}}).Countable :=
    finite_signPatterns.countable.biUnion (fun ε _ => countable_isolatedPoints _)
  exact hcount.measure_zero MeasureTheory.volume

/-- **For every `ψ, c, σ`, almost every level has only tangential vertex points.**  This is the
unconditional form of `AeVertexTangent`: the isolated vertex levels are countable
(`countable_isolatedPoints`) and a non-isolated vertex point has a tangential ray
(`Vertex.vertexDir_mem_fderiv_range_of_not_isolated`). -/
theorem aeVertexTangent (ψ : Submission.Diffeo) (c : R3) (σ : Equiv.Perm (Fin 3)) :
    AeVertexTangent ψ c σ :=
  aeVertexTangent_of_not_isolated ψ c σ
    (fun _ _ _ hy hacc => Vertex.vertexDir_mem_fderiv_range_of_not_isolated hy hacc)

/-! ## A vertex point has three tight signed faces -/

/-- At the vertex `boxVertex c σ ε s` of a box of level `s ≥ 0` with sign pattern `ε`, each of the
three signed faces `(i, ε i)` is tight at the level `s`. -/
theorem isActiveSignedFace_boxVertex {s : ℝ} {ε : Fin 3 → ℝ} (hs : 0 ≤ s)
    (hε : ∀ i : Fin 3, ε i = 1 ∨ ε i = -1) (i : Fin 3) :
    IsActiveSignedFace c σ s i (ε i) (boxVertex c σ ε s) := by
  refine ⟨?_, fun j => ((isBoxVertexPoint_boxVertex c σ hε hs).isActiveFace j).2 j⟩
  rw [faceLin_apply, signedFace, boxVertex_apply]
  have hb : Submission.boxSide i ≠ 0 := ne_of_gt (Submission.boxSide_pos i)
  rcases hε i with h | h
  · rw [h]
    field_simp
    ring
  · rw [h]
    field_simp
    ring

/-- The face norm of each face at the vertex `boxVertex c σ ε s` is `s`. -/
theorem faceNorm_boxVertex {s : ℝ} {ε : Fin 3 → ℝ} (hs : 0 ≤ s)
    (hε : ∀ i : Fin 3, ε i = 1 ∨ ε i = -1) (i : Fin 3) :
    faceNorm c σ i (boxVertex c σ ε s) = s :=
  (isBoxVertexPoint_boxVertex c σ hε hs) i

/-! ## The local model of a good level, with the vertex points handled by tangency -/

/-- **The local model of a good level, without any vertex input.**  This is
`Work.Smooth.BoxGeneric.isLocalArc_levelSet_of_regular` with the hypothesis "no point of the level
set is a vertex" replaced by the *a.e. tangency* of the vertex points: at every vertex point
`boxVertex c σ ε s` of the surface, the vertex-ray direction `Vertex.vertexDir σ ε` is tangent to
the surface.

Indeed, a point of the level set which is not a vertex is handled by the case analysis and the two
corner models (`isLocalArcAt_of_uniqueActiveFace`, `isLocalArcAt_of_corner`); a vertex point is
handled by `LocalSurface.isLocalArcAt_of_vertex_tangent`, whose regularity hypothesis on the three
tight faces is supplied by the a.e. regularity of the signed faces at the values `± s`. -/
theorem isLocalArc_levelSet_of_regular_tangent {s : ℝ} (hs : 0 < s)
    (hreg : ∀ (i : Fin 3) (ε : ℝ), (ε = 1 ∨ ε = -1) →
      Work.Smooth.Morse.IsRegularValue ψ (signedFace c σ i) (ε * s))
    (hcorn : ∀ y ∈ (Work.Smooth.Morse.torus ψ).carrier, Submission.boxNorm c σ y = s →
      ∀ (i j : Fin 3) (ε ε' : ℝ), i ≠ j → (ε = 1 ∨ ε = -1) → (ε' = 1 ∨ ε' = -1) →
        IsActiveSignedFace c σ s i ε y → IsActiveSignedFace c σ s j ε' y →
        (∃ p : ℝ × ℝ, Work.Smooth.Morse.param ψ p = y ∧
          fderiv ℝ (Work.Smooth.Morse.pullback ψ (faceLin c σ i ε)) p ≠ 0) →
        (∃ p : ℝ × ℝ, Work.Smooth.Morse.param ψ p = y ∧
          fderiv ℝ (Work.Smooth.Morse.pullback ψ (faceLin c σ j ε')) p ≠ 0) →
        (∃ p : ℝ × ℝ, Work.Smooth.Morse.param ψ p = y ∧
          fderiv ℝ (Work.Smooth.Morse.pullback ψ
            (fun z : R3 => faceLin c σ i ε z - faceLin c σ j ε' z)) p ≠ 0) →
        CornerTransverseAt ψ c σ i j ε ε' y)
    (htan : ∀ ε : Fin 3 → ℝ, (∀ i : Fin 3, ε i = 1 ∨ ε i = -1) →
      boxVertex c σ ε s ∈ (Work.Smooth.Morse.torus ψ).carrier →
        ∃ p : ℝ × ℝ, Work.Smooth.Morse.param ψ p = boxVertex c σ ε s ∧
          ∃ r : ℝ × ℝ, fderiv ℝ (Work.Smooth.Morse.param ψ) p r = Vertex.vertexDir σ ε) :
    Work.Smooth.Morse.IsLocalArc ψ
      (Work.Smooth.Morse.levelSet ψ (Submission.boxNorm c σ) s) := by
  intro x hx
  rw [Work.Smooth.Morse.mem_levelSet] at hx
  obtain ⟨hxcar, hxbox⟩ := hx
  by_cases hvertex : IsBoxVertexPoint c σ s x
  · obtain ⟨ε, hε, hxeq⟩ := eq_boxVertex_of_isBoxVertexPoint c σ (le_of_lt hs) hvertex
    subst hxeq
    refine LocalSurface.isLocalArcAt_of_vertex_tangent hs hε hxcar ?_ (htan ε hε hxcar)
    intro i
    exact exists_fderiv_pullback_faceLin_ne_zero (hε i) hxcar
      (isActiveSignedFace_boxVertex (le_of_lt hs) hε i) (hreg i (ε i) (hε i))
  · rcases Case.exists_active_signed_of_not_vertex hs hxbox hvertex with
      ⟨i, ε, hε, hact, huniq⟩ | ⟨i, j, ε, ε', hij, hε, hε', hacti, hactj, huniq⟩
    · exact LocalSurface.isLocalArcAt_of_uniqueActiveFace hs hε hxcar hact huniq
        (exists_fderiv_pullback_faceLin_ne_zero hε hxcar hact (hreg i ε hε))
    · have hregi := exists_fderiv_pullback_faceLin_ne_zero hε hxcar hacti (hreg i ε hε)
      have hregj := exists_fderiv_pullback_faceLin_ne_zero hε' hxcar hactj (hreg j ε' hε')
      by_cases hcrit : ∃ p : ℝ × ℝ, Work.Smooth.Morse.param ψ p = x ∧
          fderiv ℝ (Work.Smooth.Morse.pullback ψ
            (fun z : R3 => faceLin c σ i ε z - faceLin c σ j ε' z)) p = 0
      · exact LocalSurface.isLocalArcAt_of_tangentialCorner hs hij hε hε' hxcar hacti hactj
          huniq hcrit hregi
      · have hregbis : ∃ p : ℝ × ℝ, Work.Smooth.Morse.param ψ p = x ∧
            fderiv ℝ (Work.Smooth.Morse.pullback ψ
              (fun z : R3 => faceLin c σ i ε z - faceLin c σ j ε' z)) p ≠ 0 := by
          obtain ⟨p, hp, -⟩ := hregi
          exact ⟨p, hp, fun h0 => hcrit ⟨p, hp, h0⟩⟩
        exact LocalSurface.isLocalArcAt_of_corner hs hij hε hε' hxcar hacti hactj huniq
          (hcorn x hxcar hxbox i j ε ε' hij hε hε' hacti hactj hregi hregj hregbis)

/-- **For almost every level, the box-norm level set on the surface is a compact, locally-arc set**
— i.e. a compact `1`-manifold — with no genericity input at all.  This is the "essential content" of
the chapter: the three local models at smooth points, corners and vertices, plus two-dimensional
Sard. -/
theorem ae_isCompact_isLocalArc_levelSet_unconditional (ψ : Submission.Diffeo) (c : R3)
    (σ : Equiv.Perm (Fin 3)) :
    ∀ᵐ s ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      IsCompact (Work.Smooth.Morse.levelSet ψ (Submission.boxNorm c σ) s) ∧
      Work.Smooth.Morse.IsLocalArc ψ
        (Work.Smooth.Morse.levelSet ψ (Submission.boxNorm c σ) s) := by
  have htan := aeVertexTangent ψ c σ
  have hreg := FaceRegular.ae_face_regular_of_sardCoord (Sard.sardCoord ψ) c σ
  have hcorn := AeCorner.ae_transverseCorner_of_regularBisector (ψ := ψ) c σ
  have hne : ∀ᵐ s ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), s ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    simpa using measure_singleton (0 : ℝ)
  have hcont : Continuous (Submission.boxNorm c σ) :=
    Work.Topology.SphereSlicing.boxNorm_continuous c σ
  filter_upwards [hreg, hcorn, htan, hne] with s hs_reg hs_corn hs_tan hs_ne
  rcases lt_or_gt_of_ne hs_ne with hslt | hsgt
  · have hbox : {y : R3 | Submission.boxNorm c σ y = s} = (∅ : Set R3) := by
      rw [← Work.Topology.SphereSlicing.BoxSphere_eq_frontier s c σ]
      exact BoxSphere_eq_empty_of_neg hslt c σ
    have hempty : Work.Smooth.Morse.levelSet ψ (Submission.boxNorm c σ) s = ∅ := by
      rw [Work.Smooth.Morse.levelSet, hbox, Set.inter_empty]
    rw [hempty]
    exact ⟨isCompact_empty, fun x hx => absurd hx (Set.notMem_empty x)⟩
  · exact ⟨Work.Smooth.Morse.Surface.isCompact_levelSet ψ hcont s,
      isLocalArc_levelSet_of_regular_tangent hsgt (fun i ε hε => hs_reg i ε hε) hs_corn hs_tan⟩

/-- **For almost every level, the level set is a finite disjoint union of simple closed curves of
the surface**, from the classification of compact `1`-manifolds and nothing else. -/
theorem ae_isCircleUnion_levelSet_unconditional (ψ : Submission.Diffeo) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (hclass : Work.Smooth.Morse.CompactOneManifoldInput ψ) :
    ∀ᵐ s ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      Work.Smooth.Morse.IsCircleUnion ψ
        (Work.Smooth.Morse.levelSet ψ (Submission.boxNorm c σ) s) := by
  have htan := aeVertexTangent ψ c σ
  have hreg := FaceRegular.ae_face_regular_of_sardCoord (Sard.sardCoord ψ) c σ
  have hcorn := AeCorner.ae_transverseCorner_of_regularBisector (ψ := ψ) c σ
  have hne : ∀ᵐ s ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), s ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    simpa using measure_singleton (0 : ℝ)
  have hcont : Continuous (Submission.boxNorm c σ) :=
    Work.Topology.SphereSlicing.boxNorm_continuous c σ
  filter_upwards [hreg, hcorn, htan, hne] with s hs_reg hs_corn hs_tan hs_ne
  rcases lt_or_gt_of_ne hs_ne with hslt | hsgt
  · have hbox : {y : R3 | Submission.boxNorm c σ y = s} = (∅ : Set R3) := by
      rw [← Work.Topology.SphereSlicing.BoxSphere_eq_frontier s c σ]
      exact BoxSphere_eq_empty_of_neg hslt c σ
    have hempty : Work.Smooth.Morse.levelSet ψ (Submission.boxNorm c σ) s = ∅ := by
      rw [Work.Smooth.Morse.levelSet, hbox, Set.inter_empty]
    rw [hempty]
    exact ⟨0, Fin.elim0, (fun i => i.elim0), (fun i => i.elim0), by ext x; simp⟩
  · exact hclass _ (Work.Smooth.Morse.Surface.isCompact_levelSet ψ hcont s)
      (isLocalArc_levelSet_of_regular_tangent hsgt (fun i ε hε => hs_reg i ε hε) hs_corn hs_tan)

/-! ## The target, unconditionally -/

/-- **Almost every box sphere meets the surface in general position** — with *no* vertex input: the
only hypotheses are the classification of compact `1`-manifolds and the tangency step for the vertex
points. -/
theorem aeTransverseBox_of_tangent_step (ψ : Submission.Diffeo) (c : R3) (σ : Equiv.Perm (Fin 3))
    (hstep : ∀ ε : Fin 3 → ℝ, (∀ i : Fin 3, ε i = 1 ∨ ε i = -1) → ∀ s : ℝ,
      boxVertex c σ ε s ∈ (Work.Smooth.Morse.torus ψ).carrier →
      (∀ δ : ℝ, 0 < δ → ∃ t : ℝ, t ≠ s ∧ |t - s| < δ ∧
        boxVertex c σ ε t ∈ (Work.Smooth.Morse.torus ψ).carrier) →
      ∃ p : ℝ × ℝ, Work.Smooth.Morse.param ψ p = boxVertex c σ ε s ∧
        ∃ r : ℝ × ℝ, fderiv ℝ (Work.Smooth.Morse.param ψ) p r = Vertex.vertexDir σ ε)
    (hclass : Work.Smooth.Morse.CompactOneManifoldInput ψ) :
    AeTransverseBox ψ c σ := by
  have htan := aeVertexTangent_of_not_isolated ψ c σ hstep
  have hreg := FaceRegular.ae_face_regular_of_sardCoord (Sard.sardCoord ψ) c σ
  have hcorn := AeCorner.ae_transverseCorner_of_regularBisector (ψ := ψ) c σ
  have hne : ∀ᵐ s ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), s ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    simpa using measure_singleton (0 : ℝ)
  filter_upwards [hreg, hcorn, htan, hne] with s hs_reg hs_corn hs_tan hs_ne
  rcases lt_or_gt_of_ne hs_ne with hslt | hsgt
  · have hbox : {y : R3 | Submission.boxNorm c σ y = s} = (∅ : Set R3) := by
      rw [← Work.Topology.SphereSlicing.BoxSphere_eq_frontier s c σ]
      exact BoxSphere_eq_empty_of_neg hslt c σ
    rw [hbox]
    exact transverseSphere_empty _
  · have hcont : Continuous (Submission.boxNorm c σ) :=
      Work.Topology.SphereSlicing.boxNorm_continuous c σ
    refine transverseSphere_of_compact_isLocalArc hclass ?_ ?_
    · rw [Set.inter_comm, ← Work.Smooth.Morse.levelSet]
      exact Work.Smooth.Morse.Surface.isCompact_levelSet ψ hcont s
    · rw [Set.inter_comm, ← Work.Smooth.Morse.levelSet]
      exact isLocalArc_levelSet_of_regular_tangent hsgt (fun i ε hε => hs_reg i ε hε) hs_corn
        hs_tan

/-- **Almost every box sphere meets the surface in general position**, from the classification of
compact `1`-manifolds alone: no vertex genericity input, no Sard input. -/
theorem aeTransverseBox_unconditional (ψ : Submission.Diffeo) (c : R3) (σ : Equiv.Perm (Fin 3))
    (hclass : Work.Smooth.Morse.CompactOneManifoldInput ψ) : AeTransverseBox ψ c σ :=
  aeTransverseBox_of_tangent_step ψ c σ
    (fun ε _ s hy hacc => Vertex.vertexDir_mem_fderiv_range_of_not_isolated hy hacc) hclass

/-- **The target `Work.BoxShrink.AeSliced` for a single diffeomorphism**, from the classification of
compact `1`-manifolds and the classical slicing input — with no vertex genericity input. -/
theorem aeSliced_unconditional (ψ : Submission.Diffeo) (c : R3) (σ : Equiv.Perm (Fin 3))
    (hclass : Work.Smooth.Morse.CompactOneManifoldInput ψ)
    (hslice : Work.Topology.SphereSlicing.SliceInput (Work.Smooth.Morse.torus ψ)) :
    Work.BoxShrink.AeSliced ψ c σ :=
  aeSliced_of_aeTransverseBox ψ c σ (aeTransverseBox_unconditional ψ c σ hclass) hslice

/-- **The target `Work.BoxShrink.AeSlicedAll`** from the classification of compact `1`-manifolds and
the classical slicing input. -/
theorem aeSlicedAll_of_classify
    (hclass : ∀ ψ : Submission.Diffeo, Work.Smooth.Morse.CompactOneManifoldInput ψ)
    (hslice : ∀ ψ : Submission.Diffeo,
      Work.Topology.SphereSlicing.SliceInput (Work.Smooth.Morse.torus ψ)) :
    Work.BoxShrink.AeSlicedAll :=
  fun ψ c σ => aeSliced_unconditional ψ c σ (hclass ψ) (hslice ψ)

/-- **The target `Work.BoxShrink.AeSlicedAll`** from the classification of compact `1`-manifolds and
the sphere-side Jordan–Schoenflies theorem. -/
theorem aeSlicedAll_of_classify_of_jordanSchoenflies
    (hclass : ∀ ψ : Submission.Diffeo, Work.Smooth.Morse.CompactOneManifoldInput ψ)
    (hjordan : Work.Topology.Classical.JordanSchoenfliesSphere) :
    Work.BoxShrink.AeSlicedAll :=
  aeSlicedAll_of_classify hclass fun ψ => sliceInput_of_jordanSchoenflies hjordan ψ

/-- **The target `Work.BoxShrink.AeSlicedAll`** from the classification of compact `1`-manifolds and
the *planar* Jordan–Schoenflies theorem (`Work.Smooth.SphereJordan.PlaneHypothesis`). -/
theorem aeSlicedAll_of_classify_of_planeHypothesis
    (hclass : ∀ ψ : Submission.Diffeo, Work.Smooth.Morse.CompactOneManifoldInput ψ)
    (hplane : Work.Smooth.SphereJordan.PlaneHypothesis) :
    Work.BoxShrink.AeSlicedAll :=
  aeSlicedAll_of_classify_of_jordanSchoenflies hclass
    (Work.Smooth.SphereJordan.jordanSchoenfliesSphere hplane)

/-- **The target `Work.BoxShrink.AeSlicedAll` from the classical input of the sibling chapters**
`Work.Topology.SphereSlicing` (`ClassicalInput standard = SliceInput standard ∧ CleanOneCurve
standard`) together with the classification of compact `1`-manifolds. -/
theorem aeSlicedAll_of_classify_of_classicalInput
    (hclass : ∀ ψ : Submission.Diffeo, Work.Smooth.Morse.CompactOneManifoldInput ψ)
    (hCI : Work.Topology.SphereSlicing.ClassicalInput Work.CoreTopology.standard) :
    Work.BoxShrink.AeSlicedAll :=
  aeSlicedAll_of_classify hclass fun ψ =>
    (Work.Topology.SphereSlicing.sliceInput_map_homeomorph_iff ψ.toHomeomorph).mpr hCI.1

end

end Work.Smooth.BoxGeneric
