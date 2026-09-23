import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian

namespace Commons.Geometry.Manifold.Riemannian

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set Metric

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {n : WithTop ℕ∞}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)]
  [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)] [∀ b, IsTopologicalAddGroup (E b)]
  [∀ b, ContinuousConstSMul ℝ (E b)]
  [FiberBundle F E] [VectorBundle ℝ F E]

/-- **The fibre inner product of a `RiemannianBundle` built from `⟨g⟩` is `g`.**  If the fibres of
`E` are given the inner product space structure induced by the family of inner products
`g : RiemannianMetric E`, then `inner ℝ v w = g.inner b v w`. -/
lemma inner_eq_riemannianMetric_inner (g : RiemannianMetric E) :
    letI : RiemannianBundle E := ⟨g⟩
    ∀ (b : B) (v w : E b), inner ℝ v w = g.inner b v w := by
  intro b v w
  rfl

/-- **Auxiliary form of `isContMDiffRiemannianBundle_scaleMetric`.**  Suppose `G` is a family of
bilinear forms on the fibres which (i) is `C^n` as a section of the hom-bundle, and (ii) represents
the inner product induced by `g`.  If `g'.inner b v w = c * g.inner b v w`, then `⟨g'⟩` makes `E`
into a `C^n` Riemannian bundle, with witness `c • G`.

This is stated with the witness and its smoothness as explicit hypotheses so that the instance
arguments of `IsContMDiffRiemannianBundle` never have to be compared across two different
`RiemannianBundle` instances in the corresponding `Exists`-elimination (which is very costly for
the elaborator/kernel); the main theorem below destructures `h` and calls this lemma. -/
lemma isContMDiffRiemannianBundle_scaleMetric_aux
    (g g' : RiemannianMetric E) {c : ℝ}
    (hinner : ∀ (b : B) (v w : E b), g'.inner b v w = c * g.inner b v w)
    (G : (b : B) → E b →L[ℝ] E b →L[ℝ] ℝ)
    (hG : ContMDiff IB (IB.prod (modelWithCornersSelf ℝ (F →L[ℝ] F →L[ℝ] ℝ))) n
      (fun b : B => TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) b (G b)))
    (hGinner : letI : RiemannianBundle E := ⟨g⟩
      ∀ (b : B) (v w : E b), inner ℝ v w = G b v w) :
    letI : RiemannianBundle E := ⟨g'⟩
    IsContMDiffRiemannianBundle IB n F E := by
  -- `G` and `g.inner` agree pointwise, both representing the same inner product.
  have hG_eq : ∀ b, G b = g.inner b := by
    intro b
    ext v w
    exact (hGinner b v w).symm.trans (inner_eq_riemannianMetric_inner g b v w)
  -- The scaled family `c • G` is again a `C^n` section of the hom-bundle.
  have hsmul : ContMDiff IB (IB.prod (modelWithCornersSelf ℝ (F →L[ℝ] F →L[ℝ] ℝ))) n
      (fun b : B => TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) b ((c • G) b)) :=
    ContMDiff.const_smul_section (F := F →L[ℝ] F →L[ℝ] ℝ)
      (V := fun b => E b →L[ℝ] E b →L[ℝ] ℝ) (a := c) (s := G) hG
  letI : RiemannianBundle E := ⟨g'⟩
  refine ⟨fun b => (c • G) b, hsmul, ?_⟩
  intro b v w
  rw [inner_eq_riemannianMetric_inner g' b v w]
  exact (hinner b v w).trans (by
    calc c * g.inner b v w = c * G b v w := by rw [← hG_eq b]
      _ = (c • G) b v w := by simp)

/-- **`IsContMDiffRiemannianBundle` survives scaling of the fibre metric by a positive constant.**
If the bundle instance given by the fibre metrics `g` is a smooth Riemannian bundle, and
`g'.inner b v w = c * g.inner b v w` with `c > 0`, then the bundle instance given by `g'` is a
smooth Riemannian bundle too.

Hint: `h.exists_contMDiff` gives a smooth section `b ↦ ⟨b, g₀ b⟩` with `⟪v,w⟫ = g₀ b v w`, so
`g₀ = g` pointwise; then `ContMDiff.const_smul_section (a := c)` gives smoothness of
`b ↦ ⟨b, (c • g₀) b⟩`, and `TotalSpace.mk_inj` converts the `⟨b, ·⟩` form to the `mk'` form used by
`IsContMDiffRiemannianBundle`. -/
theorem isContMDiffRiemannianBundle_scaleMetric
    (g g' : RiemannianMetric E) {c : ℝ} (hc : 0 < c)
    (hinner : ∀ (b : B) (v w : E b), g'.inner b v w = c * g.inner b v w)
    (h : letI : RiemannianBundle E := ⟨g⟩; IsContMDiffRiemannianBundle IB n F E) :
    letI : RiemannianBundle E := ⟨g'⟩
    IsContMDiffRiemannianBundle IB n F E := by
  letI : RiemannianBundle E := ⟨g⟩
  obtain ⟨G, hG, hGinner⟩ := h
  exact isContMDiffRiemannianBundle_scaleMetric_aux g g' hinner G hG hGinner

end Commons.Geometry.Manifold.Riemannian
