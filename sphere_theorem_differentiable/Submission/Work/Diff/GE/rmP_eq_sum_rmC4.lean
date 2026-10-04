import Mathlib
import Submission.Work.Diff.GE.rmPDeps

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.GE

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

set_option linter.unusedSectionVars false

/-! ## Expanding a section in the coordinate frame of a chart -/

/-- A section, evaluated at a point `y` of the chart at `x₀`, is the linear combination of the
coordinate frame vectors `σ_i y = cFrame x₀ i y = frameVector x₀ y (cBasis i)` with the coefficients
given by the chart coordinates `coordFun x₀ W y`. -/
lemma section_eq_sum_coordFun
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    (x₀ : M) {W : Π y : M, TangentSpace I y} {y : M}
    (hy : y ∈ (chartAt H x₀).source) :
    W y = ∑ i, (cBasis (E := E)).coord i (Submission.ChartCurv.coordFun (I := I) x₀ W y)
      • cFrame (I := I) x₀ i y := by
  rw [← Submission.ChartCurv.frameVector_coordFun_eq (I := I) (x₀ := x₀) (W := W) hy]
  conv_lhs => rw [← Submission.ChartCurv.sum_coord_smul_eq
    (Submission.ChartCurv.coordFun (I := I) x₀ W y)]
  rw [Submission.Geodesic.frameVector_sum (I := I) Finset.univ x₀ y
    (fun i => (cBasis (E := E)).coord i (Submission.ChartCurv.coordFun (I := I) x₀ W y))
    (fun i => cBasis (E := E) i)]
  exact Finset.sum_congr rfl (fun i _ => by rw [cFrame_apply])

/-! ## Elementary multitinear expansions -/

/-- Multilinearity of `rmVec` in its three vector slots, as a nested sum over `Fin n`. -/
private lemma rmVec_sum3
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞)
    (x : M) (n : ℕ) (c₁ c₂ c₃ : Fin n → ℝ) (u v w : Fin n → TangentSpace I x) :
    rmVec cov x (∑ a, c₁ a • u a) (∑ b, c₂ b • v b) (∑ d, c₃ d • w d)
      = ∑ a, ∑ b, ∑ d, (c₁ a * c₂ b * c₃ d) • rmVec cov x (u a) (v b) (w d) := by
  rw [Work.Diff.GE.rmVec_sum_left (ι := Fin n) cov hcov x Finset.univ c₁ u
    (∑ b, c₂ b • v b) (∑ d, c₃ d • w d)]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Work.Diff.GE.rmVec_sum_middle (ι := Fin n) cov hcov x Finset.univ c₂ v (u a)
    (∑ d, c₃ d • w d)]
  simp only [Finset.smul_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Work.Diff.GE.rmVec_sum_right (ι := Fin n) cov hcov x Finset.univ c₃ w (u a) (v b)]
  simp only [Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  ring_nf

/-- Bilinearity of `g.inner x` in the second slot, on a sum. -/
private lemma inner_smul_sum
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (g : SMet I M) (n : ℕ) (x : M) (u : TangentSpace I x)
    (c : Fin n → ℝ) (v : Fin n → TangentSpace I x) :
    g.inner x u (∑ i, c i • v i) = ∑ i, c i * g.inner x u (v i) := by
  simp only [map_sum, map_smul, smul_eq_mul]

/-- Bilinearity of `g.inner x` in the first slot, on a triple sum. -/
private lemma inner_nested3_left
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (g : SMet I M) (x : M) (n : ℕ)
    (c : Fin n → Fin n → Fin n → ℝ) (u : Fin n → Fin n → Fin n → TangentSpace I x)
    (z : TangentSpace I x) :
    g.inner x (∑ a, ∑ b, ∑ d, c a b d • u a b d) z
      = ∑ a, ∑ b, ∑ d, c a b d * g.inner x (u a b d) z := by
  simp only [map_sum, sum_apply, map_smul, smul_apply, smul_eq_mul]

/-- Bilinearity of `g.inner x` on a triple sum in the first slot and a single sum in the second. -/
private lemma inner_nested3
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (g : SMet I M) (x : M) (n : ℕ)
    (c : Fin n → Fin n → Fin n → ℝ) (u : Fin n → Fin n → Fin n → TangentSpace I x)
    (c' : Fin n → ℝ) (z : Fin n → TangentSpace I x) :
    g.inner x (∑ a, ∑ b, ∑ d, c a b d • u a b d) (∑ k, c' k • z k)
      = ∑ a, ∑ b, ∑ d, ∑ k, c a b d * c' k * g.inner x (u a b d) (z k) := by
  rw [inner_nested3_left g x n c u (∑ k, c' k • z k)]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
    Finset.sum_congr rfl (fun d _ => ?_)))
  rw [inner_smul_sum g n x _ _ _, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  ring

/-- The index bookkeeping: the fourfold sum produced by the multilinearity expansion (index order
`a b d k`) equals the one in the order of `rmC4` (`a b k d`). -/
private lemma sum_reorder_main (n : ℕ) (c₁ c₂ c₃ c₄ : Fin n → ℝ)
    (R : Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ a, ∑ b, ∑ d, ∑ k, (c₁ a * c₂ b * c₄ d) * c₃ k * R a b d k)
      = ∑ i, ∑ j, ∑ k, ∑ l, c₁ i * c₂ j * c₃ k * c₄ l * R i j l k := by
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => by ring))

/-! ## The expansion of the frozen curvature form in the coordinate frame -/

/-- Expansion of the frozen pointwise curvature form in the coordinate frame of a chart.

`Submission.Diff.rmP (G t) y u v w z = (G t).inner y (rmVec (lcOf (G t)) y u v w) z` is the pairing
`⟪R(u,v)w, z⟫`.  For `y` in the source of the chart at `x₀`, expanding the four arguments in the
coordinate frame `σ_i y = cFrame x₀ i y = frameVector x₀ y (cBasis i)` — which is what `coordFun`
does: `A y = Σ_i (cBasis.coord i (coordFun x₀ A y)) • σ_i y` — turns `rmP` into the weighted sum of
the coordinate-frame components `rmC4 G x₀ t y i j k l = rmP (G t) y (σ_i y) (σ_j y) (σ_k y) (σ_l y)`
(recall the frozen slot convention: the third argument of `rmP` is the *pairing* slot and the fourth
is `rmVec`'s third vector slot, which is exactly how `rmC4` is defined).

Usable route: `Work.Diff.GE.rmVec_sum_left/middle/right` and `rmVec_smul_left/middle/right`
(multilinearity of `rmVec` in its three vector slots, in `Submission.Work.Diff.GE.curvbasic`, using
`hcov : ContMDiffCovariantDerivative (lcOf (G t)) ∞` from `hLC (G t)`),
additivity/`ℝ`-homogeneity of `(G t).inner y` in its last argument,
`Submission.Geodesic.frameVector_sum` and `Submission.ChartCurv.sum_coord_smul_eq` to write the
expanded arguments as finite sums, and `Submission.ChartCurv.frameVector_coordFun_eq` to identify
`A y` with `frameVector x₀ y (coordFun x₀ A y)` (needs `hy`). -/
theorem rmP_eq_sum_rmC4
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [T2Space M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I (⊤ : ℕ∞) E (fun x : M ↦ TangentSpace I x)]
    (hLC : Submission.Diff.LCSmooth I M)
    (G : ℝ → Submission.Diff.SMet I M) (x₀ : M) (t : ℝ) {y : M}
    (hy : y ∈ (chartAt H x₀).source)
    {A B C D : Π y : M, TangentSpace I y} :
    Submission.Diff.rmP (G t) y (A y) (B y) (C y) (D y)
      = ∑ i, ∑ j, ∑ k, ∑ l,
          ((Work.Diff.GE.cBasis (E := E)).coord i
              (Submission.ChartCurv.coordFun (I := I) x₀ A y))
          * ((Work.Diff.GE.cBasis (E := E)).coord j
              (Submission.ChartCurv.coordFun (I := I) x₀ B y))
          * ((Work.Diff.GE.cBasis (E := E)).coord k
              (Submission.ChartCurv.coordFun (I := I) x₀ C y))
          * ((Work.Diff.GE.cBasis (E := E)).coord l
              (Submission.ChartCurv.coordFun (I := I) x₀ D y))
          * Work.Diff.GE.rmC4 (I := I) G x₀ t y i j k l := by
  classical
  obtain ⟨hcov, -, -⟩ := hLC (G t)
  obtain ⟨hcov⟩ := hcov
  -- the coordinate-frame expansions of the four arguments
  have hA := section_eq_sum_coordFun (I := I) x₀ (W := A) hy
  have hB := section_eq_sum_coordFun (I := I) x₀ (W := B) hy
  have hC := section_eq_sum_coordFun (I := I) x₀ (W := C) hy
  have hD := section_eq_sum_coordFun (I := I) x₀ (W := D) hy
  simp only [Submission.Diff.rmP, Work.Diff.GE.rmC4]
  rw [hA, hB, hC, hD]
  -- multilinearity in the three vector slots of `rmVec`, then bilinearity of the metric
  have hvec : rmVec (lcOf (G t)) y
        (∑ i, (cBasis (E := E)).coord i (Submission.ChartCurv.coordFun (I := I) x₀ A y)
          • cFrame (I := I) x₀ i y)
        (∑ j, (cBasis (E := E)).coord j (Submission.ChartCurv.coordFun (I := I) x₀ B y)
          • cFrame (I := I) x₀ j y)
        (∑ l, (cBasis (E := E)).coord l (Submission.ChartCurv.coordFun (I := I) x₀ D y)
          • cFrame (I := I) x₀ l y)
      = ∑ a, ∑ b, ∑ d,
          (((cBasis (E := E)).coord a (Submission.ChartCurv.coordFun (I := I) x₀ A y))
              * ((cBasis (E := E)).coord b (Submission.ChartCurv.coordFun (I := I) x₀ B y))
              * ((cBasis (E := E)).coord d (Submission.ChartCurv.coordFun (I := I) x₀ D y)))
            • rmVec (lcOf (G t)) y (cFrame (I := I) x₀ a y) (cFrame (I := I) x₀ b y)
                (cFrame (I := I) x₀ d y) :=
    rmVec_sum3 (lcOf (G t)) hcov y (Module.finrank ℝ E)
      (fun i => (cBasis (E := E)).coord i (Submission.ChartCurv.coordFun (I := I) x₀ A y))
      (fun j => (cBasis (E := E)).coord j (Submission.ChartCurv.coordFun (I := I) x₀ B y))
      (fun l => (cBasis (E := E)).coord l (Submission.ChartCurv.coordFun (I := I) x₀ D y))
      (fun i => cFrame (I := I) x₀ i y) (fun j => cFrame (I := I) x₀ j y)
      (fun l => cFrame (I := I) x₀ l y)
  rw [hvec]
  rw [inner_nested3 (G t) y (Module.finrank ℝ E)
    (fun a b d =>
      ((cBasis (E := E)).coord a (Submission.ChartCurv.coordFun (I := I) x₀ A y))
        * ((cBasis (E := E)).coord b (Submission.ChartCurv.coordFun (I := I) x₀ B y))
        * ((cBasis (E := E)).coord d (Submission.ChartCurv.coordFun (I := I) x₀ D y)))
    (fun a b d => rmVec (lcOf (G t)) y (cFrame (I := I) x₀ a y) (cFrame (I := I) x₀ b y)
      (cFrame (I := I) x₀ d y))
    (fun k => (cBasis (E := E)).coord k (Submission.ChartCurv.coordFun (I := I) x₀ C y))
    (fun k => cFrame (I := I) x₀ k y)]
  exact sum_reorder_main (Module.finrank ℝ E) _ _ _ _
    (fun i j l k => (G t).inner y
      (rmVec (lcOf (G t)) y (cFrame (I := I) x₀ i y) (cFrame (I := I) x₀ j y)
        (cFrame (I := I) x₀ l y)) (cFrame (I := I) x₀ k y))

end Work.Diff.GE
