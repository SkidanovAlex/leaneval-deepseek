import Mathlib
import Submission.Work.Diff.STE.Man.Sect

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Change of chart for the chart matrices of a section of `Sym² T*M`

This file proves the **gauge (transition) formula** for the chart matrices `bilChart` of an
arbitrary pointwise bilinear form `h : Bil I M` (`Work.Diff.STE.bilChart_change`, Layer B2 of the
STE design, §3 of `DESIGN.md`).

The chart matrix of `h` in the chart at `x₀` is, by definition,
`bilChart h x₀ a b y = h (χ₀⁻¹ y) (frameVector x₀ · (b a)) (frameVector x₀ · (b b))` where `b` is
`Module.finBasis ℝ E`.  Evaluating at `y = χ₀ p` (with `p` in the chart source) therefore gives

  `bilChart h x₀ a b (χ₀ p) = h p (σ₀ a) (σ₀ b)`,   `σ₀ a := frameVector x₀ p (b a)`.

The right chart is handled by the two pointwise facts

* `frameVector_change`: `u = ∑ c, ((finBasis ℝ E).repr ((linearMapAt ℝ p) u)) c • σ₁ c`
  (a `Module.finBasis` expansion, using that `linearMapAt` is the inverse of `symmL` on the base
  set of the trivialisation), and
* `symm_eq_frameVector`: `(trivializationAt …x₀).symm p v = frameVector x₀ p v`
  (both sides are `symmL`, see `Trivialization.symmL_apply`),

together with the bilinearity of `h p` (expanded by hand in the `calc`, since a generic
`ContinuousLinearMap`-bilinearity lemma cannot be instantiated at `TangentSpace I p` — that type
carries no normed-space instance in this context).

The result is the matrix identity
`chart₀ = (coefficient matrix of σ₀ in the frame σ₁)ᵀ · chart₁ · (…)`.
-/

noncomputable section

open Bundle Manifold Module

namespace Work.Diff.STE.fill

/-- The `symm` of the tangent trivialisation at `x₀` is the trivialisation-constant frame vector:
both are `Trivialization.symmL`. -/
lemma symm_eq_frameVector
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (x₀ p : M) (hp : p ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) (v : E) :
    (trivializationAt E (TangentSpace I) x₀).symm p v
      = Submission.Geodesic.frameVector x₀ p v :=
  (Trivialization.symmL_apply (R := ℝ) (trivializationAt E (TangentSpace I) x₀) hp v).symm

/-- **Change of frame.**  On the base set of the tangent trivialisation at `x₁`, a tangent vector
`u` is the `Module.finBasis`-combination of the frame vectors of the chart at `x₁` whose
coefficients are the coordinates of `u` in that trivialisation: this is
`Basis.sum_repr` transported along the linear equivalence
`(trivializationAt E (TangentSpace I) x₁).linearEquivAt ℝ p hp₁ : TangentSpace I p ≃ₗ[ℝ] E`. -/
lemma frameVector_change
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (x₁ p : M) (hp₁ : p ∈ (trivializationAt E (TangentSpace I) x₁).baseSet)
    (u : TangentSpace I p) :
    u = ∑ c : Fin (Module.finrank ℝ E),
        ((Module.finBasis ℝ E).repr
          ((trivializationAt E (TangentSpace I) x₁).linearMapAt ℝ p u)) c
        • Submission.Geodesic.frameVector x₁ p (Module.finBasis ℝ E c) := by
  let e := trivializationAt E (TangentSpace I) x₁
  have hbm : p ∈ e.baseSet := hp₁
  let Φ : TangentSpace I p ≃ₗ[ℝ] E := e.linearEquivAt ℝ p hbm
  have hlin : ∀ w : TangentSpace I p, e.linearMapAt ℝ p w = Φ w := fun w => by
    rw [Trivialization.linearMapAt_def_of_mem e hbm]
    rfl
  have hsym : ∀ w : E, Φ.symm w = e.symmL ℝ p w := fun w => by
    rw [Trivialization.linearEquivAt_symm_apply, Trivialization.symmL_apply _ hbm]
  have key : u = ∑ c : Fin (Module.finrank ℝ E),
      ((Module.finBasis ℝ E).repr (e.linearMapAt ℝ p u)) c
        • e.symmL ℝ p (Module.finBasis ℝ E c) := by
    calc u = Φ.symm (Φ u) := (LinearEquiv.symm_apply_apply Φ u).symm
      _ = Φ.symm (∑ c : Fin (Module.finrank ℝ E),
            ((Module.finBasis ℝ E).repr (Φ u)) c • Module.finBasis ℝ E c) := by
            rw [Module.Basis.sum_repr]
      _ = ∑ c : Fin (Module.finrank ℝ E),
            ((Module.finBasis ℝ E).repr (Φ u)) c • Φ.symm (Module.finBasis ℝ E c) := by
            simp only [map_sum, map_smul]
      _ = ∑ c : Fin (Module.finrank ℝ E),
            ((Module.finBasis ℝ E).repr (e.linearMapAt ℝ p u)) c
              • e.symmL ℝ p (Module.finBasis ℝ E c) := by
            refine Finset.sum_congr rfl (fun c _ => ?_)
            rw [hsym (Module.finBasis ℝ E c), ← hlin u]
  simpa only [Submission.Geodesic.frameVector] using key

/-- **The gauge formula for the chart matrices of a section.**  On the overlap of the charts at
`x₀` and `x₁`, the chart matrix of `h` in the chart at `x₀` is obtained from the chart matrix in
the chart at `x₁` by the matrix of the change of frame between the two trivialisations. -/
theorem bilChart_change
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (x₀ x₁ p : M)
    (hp₀ : p ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (hp₁ : p ∈ (trivializationAt E (TangentSpace I) x₁).baseSet)
    (a b : Fin (Module.finrank ℝ E)) :
    Work.Diff.STE.bilChart h x₀ a b ((extChartAt I x₀) p)
      = ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
        (((Module.finBasis ℝ E).repr ((trivializationAt E (TangentSpace I) x₁).linearMapAt ℝ p
            ((trivializationAt E (TangentSpace I) x₀).symm p (Module.finBasis ℝ E a))) c)
          * ((Module.finBasis ℝ E).repr ((trivializationAt E (TangentSpace I) x₁).linearMapAt ℝ p
            ((trivializationAt E (TangentSpace I) x₀).symm p (Module.finBasis ℝ E b))) d))
        * Work.Diff.STE.bilChart h x₁ c d ((extChartAt I x₁) p) := by
  -- `p` lies in the two charts, so `χ₀⁻¹ (χ₀ p) = p` and `χ₁⁻¹ (χ₁ p) = p`
  have hb0 : p ∈ (chartAt H x₀).source := by
    simpa [TangentBundle.trivializationAt_baseSet] using hp₀
  have hb1 : p ∈ (chartAt H x₁).source := by
    simpa [TangentBundle.trivializationAt_baseSet] using hp₁
  have hsrc₀ : p ∈ (extChartAt I x₀).source := by rw [extChartAt_source]; exact hb0
  have hsrc₁ : p ∈ (extChartAt I x₁).source := by rw [extChartAt_source]; exact hb1
  have hsp0 : (extChartAt I x₀).symm ((extChartAt I x₀) p) = p := (extChartAt I x₀).left_inv hsrc₀
  have hsp1 : (extChartAt I x₁).symm ((extChartAt I x₁) p) = p := (extChartAt I x₁).left_inv hsrc₁
  -- unfold `bilChart` at the two chart centres
  simp only [Work.Diff.STE.bilChart]
  rw [hsp0, hsp1]
  -- replace `symm` by the frame vectors in the coefficients on the right
  simp only [symm_eq_frameVector (I := I) x₀ p hp₀]
  -- abbreviations for the two coefficient functions and the frame of the chart at `x₁`
  let A : Fin (Module.finrank ℝ E) → ℝ := fun c =>
    (Module.finBasis ℝ E).repr ((trivializationAt E (TangentSpace I) x₁).linearMapAt ℝ p
      (Submission.Geodesic.frameVector x₀ p (Module.finBasis ℝ E a))) c
  let B : Fin (Module.finrank ℝ E) → ℝ := fun d =>
    (Module.finBasis ℝ E).repr ((trivializationAt E (TangentSpace I) x₁).linearMapAt ℝ p
      (Submission.Geodesic.frameVector x₀ p (Module.finBasis ℝ E b))) d
  let w : Fin (Module.finrank ℝ E) → TangentSpace I p :=
    fun i => Submission.Geodesic.frameVector x₁ p (Module.finBasis ℝ E i)
  have hA : Submission.Geodesic.frameVector x₀ p (Module.finBasis ℝ E a) = ∑ c, A c • w c := by
    simpa only [A, w] using frameVector_change (I := I) x₁ p hp₁
      (Submission.Geodesic.frameVector x₀ p (Module.finBasis ℝ E a))
  have hB : Submission.Geodesic.frameVector x₀ p (Module.finBasis ℝ E b) = ∑ d, B d • w d := by
    simpa only [B, w] using frameVector_change (I := I) x₁ p hp₁
      (Submission.Geodesic.frameVector x₀ p (Module.finBasis ℝ E b))
  -- expand `h p` in the frame of the chart at `x₁` (bilinearity, by hand)
  calc (h p) (Submission.Geodesic.frameVector x₀ p (Module.finBasis ℝ E a))
          (Submission.Geodesic.frameVector x₀ p (Module.finBasis ℝ E b))
      = (h p) (∑ c, A c • w c) (∑ d, B d • w d) := by
          conv_lhs => rw [hA, hB]
    _ = ∑ c, ∑ d, (A c * B d) * (h p (w c) (w d)) := by
          have h1 : (h p) (∑ c, A c • w c) = ∑ c, A c • (h p) (w c) := by
            rw [map_sum]
            exact Finset.sum_congr rfl (fun c _ => by rw [map_smul])
          rw [h1]
          have h2 : ∀ v : TangentSpace I p, (∑ c, A c • (h p) (w c)) v
              = ∑ c, A c * (h p (w c)) v := by
            intro v
            rw [sum_apply]
            exact Finset.sum_congr rfl (fun c _ => by rw [smul_apply, smul_eq_mul])
          rw [h2]
          refine Finset.sum_congr rfl (fun c _ => ?_)
          have h3 : (h p (w c)) (∑ d, B d • w d) = ∑ d, B d * (h p (w c) (w d)) := by
            rw [map_sum]
            exact Finset.sum_congr rfl (fun d _ => by rw [map_smul, smul_eq_mul])
          rw [h3, Finset.mul_sum]
          exact Finset.sum_congr rfl (fun d _ => by ring)

end Work.Diff.STE.fill
