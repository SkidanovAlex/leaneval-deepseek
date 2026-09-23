import Mathlib

namespace Commons.Geometry.Manifold.Riemannian

open scoped Manifold ContDiff Bundle Topology Pointwise
open Bundle ContDiff Set Metric

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)]
  [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)] [∀ b, IsTopologicalAddGroup (E b)]
  [∀ b, ContinuousConstSMul ℝ (E b)]
  [FiberBundle F E] [VectorBundle ℝ F E]

/-- Scaling a von Neumann bounded set by a constant gives a von Neumann bounded set. -/
lemma isVonNBounded_smul_set {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [ContinuousConstSMul ℝ E] {s : Set E} (hs : Bornology.IsVonNBounded ℝ s) (c : ℝ) :
    Bornology.IsVonNBounded ℝ (c • s) := by
  rw [Bornology.isVonNBounded_iff_tendsto_smallSets_nhds] at hs ⊢
  have hcc : Filter.Tendsto (fun x : ℝ => x * c) (𝓝 0) (𝓝 0) := by
    have h := (Filter.tendsto_id (x := 𝓝 (0 : ℝ))).mul_const c
    simpa using h
  simpa [Function.comp_def, smul_smul] using hs.comp hcc

/-- For a function `q : E → ℝ` which is homogeneous of degree two,
the sublevel set `{q < r}` is, for `r > 0`, the image of the unit sublevel set `{q < 1}`
under the homothety of ratio `√r`. -/
lemma smul_sqrt_setOf_lt_one {E : Type*} [AddCommGroup E] [Module ℝ E]
    {q : E → ℝ} (hq : ∀ (a : ℝ) (v : E), q (a • v) = a * a * q v)
    {r : ℝ} (hr : 0 < r) :
    Real.sqrt r • {v : E | q v < 1} = {v : E | q v < r} := by
  have hpos : 0 < Real.sqrt r := Real.sqrt_pos.2 hr
  have hsq : Real.sqrt r * Real.sqrt r = r := by
    rw [← sq, Real.sq_sqrt hr.le]
  ext w
  constructor
  · rintro ⟨v, hv, rfl⟩
    change q (Real.sqrt r • v) < r
    rw [hq, hsq]
    calc r * q v < r * 1 := mul_lt_mul_of_pos_left hv hr
      _ = r := mul_one r
  · intro hw
    change q w < r at hw
    refine ⟨(Real.sqrt r)⁻¹ • w, ?_, ?_⟩
    · change q ((Real.sqrt r)⁻¹ • w) < 1
      have h1 : (Real.sqrt r)⁻¹ * (Real.sqrt r)⁻¹ = r⁻¹ := by
        rw [← mul_inv, hsq]
      rw [hq, h1]
      calc r⁻¹ * q w < r⁻¹ * r := mul_lt_mul_of_pos_left hw (inv_pos.2 hr)
        _ = 1 := inv_mul_cancel₀ hr.ne'
    · simpa using smul_inv_smul₀ hpos.ne' w

/-- **Scaling a fibre metric by a positive constant.**  For a family of inner products `g` on the
fibres of a vector bundle and a constant `c > 0`, there is a family `g'` of inner products (the
fields `inner, symm, pos` and the topological conditions `continuousAt`, `isVonNBounded` all
survive) with `g'.inner b v w = c * g.inner b v w`. -/
theorem exists_scaleMetric
    (g : RiemannianMetric E) {c : ℝ} (hc : 0 < c) :
    ∃ g' : RiemannianMetric E, ∀ (b : B) (v w : E b), g'.inner b v w = c * g.inner b v w := by
  have hinner : ∀ (b : B) (v w : E b), (c • g.inner b) v w = c * g.inner b v w := by
    intro b v w
    simp only [smul_apply, smul_eq_mul]
  have hquad : ∀ (b : B), ∀ (a : ℝ) (v : E b),
      g.inner b (a • v) (a • v) = a * a * g.inner b v v := by
    intro b a v
    simp only [map_smul, smul_apply, smul_eq_mul]
    ring
  refine ⟨{ inner := fun b => c • g.inner b
            symm := ?_
            pos := ?_
            continuousAt := ?_
            isVonNBounded := ?_ }, fun b v w => hinner b v w⟩
  · intro b v w
    rw [hinner, hinner, g.symm b v w]
  · intro b v hv
    rw [hinner]
    exact mul_pos hc (g.pos b v hv)
  · intro b
    have heq : (fun v : E b => (c • g.inner b) v v) = fun v : E b => c * (g.inner b v v) := by
      funext v
      exact hinner b v v
    rw [heq]
    exact (g.continuousAt b).const_mul c
  · intro b
    have hset : {v : E b | (c • g.inner b) v v < 1} = {v : E b | g.inner b v v < c⁻¹} := by
      ext v
      change ((c • g.inner b) v v < 1) ↔ (g.inner b v v < c⁻¹)
      rw [hinner b v v, inv_eq_one_div, lt_div_iff₀ hc, mul_comm]
    rw [hset, ← smul_sqrt_setOf_lt_one (hquad b) (inv_pos.2 hc)]
    exact isVonNBounded_smul_set (g.isVonNBounded b) _

end Commons.Geometry.Manifold.Riemannian
