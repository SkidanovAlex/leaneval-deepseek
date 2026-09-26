import Mathlib
import Submission.Work.Smooth.BoxGeneric.Defs
import Submission.Work.Smooth.BoxGeneric.Vertex

namespace Work.Smooth.BoxGeneric.Vertex

open LeanEval.KnotTheory.PardonDistortion
open MeasureTheory
open Set

noncomputable section

/-- The direction vector of the vertex ray of `Work.Smooth.BoxGeneric.boxVertex` with sign pattern
`ε`: the vertex of the box with centre `c` and sign pattern `ε` at level `s` is
`c + s • vertexDir σ ε`. -/
def vertexDir (σ : Equiv.Perm (Fin 3)) (ε : Fin 3 → ℝ) : R3 :=
  WithLp.toLp 2 fun j : Fin 3 => ε (σ.symm j) * Submission.boxSide (σ.symm j)

@[simp] theorem vertexDir_apply (σ : Equiv.Perm (Fin 3)) (ε : Fin 3 → ℝ) (j : Fin 3) :
    vertexDir σ ε j = ε (σ.symm j) * Submission.boxSide (σ.symm j) := rfl

/-- **The box vertex is an affine function of the centre and the level**: it is the translate of
the centre `c` by `s • vertexDir σ ε`. -/
theorem boxVertex_eq_add_smul (c : R3) (σ : Equiv.Perm (Fin 3)) (ε : Fin 3 → ℝ) (s : ℝ) :
    Work.Smooth.BoxGeneric.boxVertex c σ ε s = c + s • vertexDir σ ε := by
  rw [vertexDir, WithLp.ext_iff]
  funext j
  simp only [Work.Smooth.BoxGeneric.boxVertex_ofLp, WithLp.ofLp_add, WithLp.ofLp_smul,
    Pi.add_apply, Pi.smul_apply]
  ring

/-- The finite set of sign patterns `ε : Fin 3 → {±1}`. -/
def signSet : Set (Fin 3 → ℝ) := {ε | ∀ i : Fin 3, ε i = 1 ∨ ε i = -1}

theorem signSet_finite : signSet.Finite := Work.Smooth.BoxGeneric.finite_signPatterns

theorem signSet_countable : signSet.Countable := signSet_finite.countable

/-- The set of pairs `(c, s)` for which the vertex of the box `PBox s c σ` with sign pattern `ε`
lies on the surface `F = ψ(standard torus)`. -/
def badPiece (ψ : Submission.Diffeo) (σ : Equiv.Perm (Fin 3)) (ε : Fin 3 → ℝ) :
    Set (R3 × ℝ) :=
  {q : R3 × ℝ |
    Work.Smooth.BoxGeneric.boxVertex q.1 σ ε q.2 ∈ (Work.Smooth.Morse.torus ψ).carrier}

@[simp] theorem mem_badPiece {ψ : Submission.Diffeo} {σ : Equiv.Perm (Fin 3)} {ε : Fin 3 → ℝ}
    {q : R3 × ℝ} :
    q ∈ badPiece ψ σ ε ↔
      Work.Smooth.BoxGeneric.boxVertex q.1 σ ε q.2 ∈ (Work.Smooth.Morse.torus ψ).carrier :=
  Iff.rfl

theorem continuous_boxVertex (σ : Equiv.Perm (Fin 3)) (ε : Fin 3 → ℝ) :
    Continuous fun q : R3 × ℝ => Work.Smooth.BoxGeneric.boxVertex q.1 σ ε q.2 := by
  rw [show (fun q : R3 × ℝ => Work.Smooth.BoxGeneric.boxVertex q.1 σ ε q.2) =
      fun q : R3 × ℝ => q.1 + q.2 • vertexDir σ ε from
    funext fun q => boxVertex_eq_add_smul q.1 σ ε q.2]
  fun_prop

/-- **Each piece of the bad set is null in the product measure.**  For a fixed sign pattern `ε`, the
set of `(c, s)` with `boxVertex c σ ε s ∈ F` has measure zero: for fixed `s` the section in `c` is
a translate of `F`, hence null, and Fubini in the `s`-direction concludes. -/
theorem prod_measure_badPiece (ψ : Submission.Diffeo) (σ : Equiv.Perm (Fin 3))
    (hF : MeasureTheory.volume ((Work.Smooth.Morse.torus ψ).carrier : Set R3) = 0)
    (ε : Fin 3 → ℝ) :
    ((MeasureTheory.volume : Measure R3).prod (MeasureTheory.volume : Measure ℝ))
      (badPiece ψ σ ε) = 0 := by
  have hFclosed : IsClosed (Work.Smooth.Morse.torus ψ).carrier :=
    (Work.Smooth.Morse.Surface.isCompact_torus ψ).isClosed
  have hmeas : MeasurableSet (badPiece ψ σ ε) :=
    hFclosed.measurableSet.preimage (continuous_boxVertex σ ε).measurable
  rw [MeasureTheory.Measure.prod_apply_symm hmeas]
  have hsec : ∀ s : ℝ,
      (MeasureTheory.volume : Measure R3) ((fun c : R3 => (c, s)) ⁻¹' (badPiece ψ σ ε)) = 0 := by
    intro s
    have hset : (fun c : R3 => (c, s)) ⁻¹' (badPiece ψ σ ε) =
        (fun c : R3 => c + s • vertexDir σ ε) ⁻¹'
          (Work.Smooth.Morse.torus ψ).carrier := by
      ext c
      simp only [Set.mem_preimage, mem_badPiece, boxVertex_eq_add_smul]
    rw [hset, MeasureTheory.measure_preimage_add_right]
    exact hF
  simp only [hsec, MeasureTheory.lintegral_zero]

/-- **Almost every centre has almost every box sphere avoiding the vertices.**  The bad set
`{(c, s) : the box of centre c and level s has a vertex on the surface}` is contained in the finite
union of the null pieces `badPiece ψ σ ε`; it is therefore null in `volume.prod volume = volume`,
and Fubini gives the conclusion. -/
theorem aeNoVertex_of_ae_centre {ψ : Submission.Diffeo} (σ : Equiv.Perm (Fin 3))
    (hF : MeasureTheory.volume
      ((Work.Smooth.Morse.torus ψ).carrier : Set LeanEval.KnotTheory.PardonDistortion.R3) = 0) :
    ∀ᵐ c ∂(MeasureTheory.volume : MeasureTheory.Measure LeanEval.KnotTheory.PardonDistortion.R3),
      Work.Smooth.BoxGeneric.AeNoVertex ψ c σ := by
  classical
  set BadSub : Set (R3 × ℝ) := ⋃ ε ∈ signSet, badPiece ψ σ ε with hBadSub
  have hBad0 : ((MeasureTheory.volume : Measure R3).prod (MeasureTheory.volume : Measure ℝ))
      BadSub = 0 := by
    rw [hBadSub, measure_biUnion_null_iff signSet_countable]
    intro ε _
    exact prod_measure_badPiece ψ σ hF ε
  have hfub : (fun c : R3 => (MeasureTheory.volume : Measure ℝ) (Prod.mk c ⁻¹' BadSub)) =ᵐ[
      (MeasureTheory.volume : Measure R3)] 0 :=
    MeasureTheory.Measure.measure_ae_null_of_prod_null hBad0
  filter_upwards [hfub] with c hc
  rw [Work.Smooth.BoxGeneric.AeNoVertex, MeasureTheory.ae_iff]
  refine measure_mono_null ?_ hc
  intro s hs
  have hex : ∃ y : R3, y ∈ (Work.Smooth.Morse.torus ψ).carrier ∧
      IsBoxVertexPoint c σ s y := by
    by_contra hcon
    exact hs fun y hy hyv => hcon ⟨y, hy, hyv⟩
  obtain ⟨y, hy, hvert⟩ := hex
  have hs0 : 0 ≤ s :=
    le_trans (Work.Smooth.BoxGeneric.faceNorm_nonneg c σ 0 y) (le_of_eq (hvert 0))
  obtain ⟨ε, hε, hyε⟩ :=
    Work.Smooth.BoxGeneric.eq_boxVertex_of_isBoxVertexPoint c σ hs0 hvert
  show (c, s) ∈ BadSub
  rw [hBadSub]
  refine Set.mem_biUnion hε ?_
  rw [mem_badPiece, ← hyε]
  exact hy

end

end Work.Smooth.BoxGeneric.Vertex
