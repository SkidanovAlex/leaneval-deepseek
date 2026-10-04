import Mathlib
import Submission.Work.Diff.GE.deps
import Submission.Work.Diff.GE.curvbasic
import Submission.Work.Diff.GE.frobSq_rot
import Submission.Work.Diff.GE.rmFrame_eq_rot

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `rmNormSq (G t) y = N4 (GramM) (rmC4)`: `|Rm|²` in the coordinate frame of a chart

`rmNormSq g y` is the Frobenius norm of the curvature array computed in the
`Classical.epsilon`-chosen orthonormal frame `onFrame g y`.  The chart at `x₀` provides another
frame, the *coordinate frame* `cFrame x₀ · y` (`= frameVector x₀ y (bb i)` for the canonical basis
`bb` of the model space), whose Gram matrix is `GramM G x₀ t y` and in which the curvature
components are `rmC4 G x₀ t y`.  This file proves

`rmNormSq (G t) y = N4 (GramM (I := I) G x₀ t y) (rmC4 (I := I) G x₀ t y)`.

The route is the frame-independence of the Frobenius norm.  Writing the coordinate frame in the
orthonormal frame, `cFrame x₀ i y = ∑ j, B i j • onFrame (G t) y j` with `B` the (invertible)
matrix of coordinates and `Γ = GramM = B * Bᵀ` (Parseval), the multilinearity of the curvature
(`rmFrame_eq_rot`: `rmFrame g y e = rot B (rmFrame g y onFrame)`) and the general frame change
(`frobSq_rot`: `N4 (B * Bᵀ) (rot B R) = frobSq R`) give the claim.

The auxiliary statement `rmNormSq_eq_N4_of_span` is the same identity for an arbitrary spanning
family, and `cFrame_span_chart` is the fact that the coordinate frame is a basis at every point of
the chart.  Neither needs `[I.Boundaryless]`.
-/

namespace Work.Diff.GE

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators Matrix
open Bundle ContDiff Set VectorField CovariantDerivative Metric

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

/-- Bilinearity of the metric on two linear combinations of an orthonormal family:
`⟨∑ a_k v_k, ∑ c_l v_l⟩ = ∑ a_k c_k` when `⟨v_k, v_l⟩ = δ_{kl}`. -/
private lemma inner_sum_smul_sum_smul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {n : ℕ} (g : SMet I M) (x : M) (v : Fin n → TangentSpace I x)
    (hv : ∀ k l, g.inner x (v k) (v l) = if k = l then 1 else 0)
    (a c : Fin n → ℝ) :
    g.inner x (∑ k, a k • v k) (∑ l, c l • v l) = ∑ k, a k * c k := by
  have hL : g.inner x (∑ k, a k • v k) = ∑ k, a k • g.inner x (v k) := by
    rw [map_sum]
    exact Finset.sum_congr rfl (fun k _ => map_smul (g.inner x) (a k) (v k))
  have hR : ∀ k, g.inner x (v k) (∑ l, c l • v l) = c k := by
    intro k
    rw [map_sum]
    rw [Finset.sum_congr rfl (fun l _ => by rw [map_smul, hv k l, smul_eq_mul])]
    rw [Finset.sum_congr rfl (fun l _ => by rw [mul_ite, mul_one, mul_zero]),
      Fintype.sum_ite_eq k (fun l => c l)]
  rw [hL, sum_apply]
  exact Finset.sum_congr rfl (fun k _ => by rw [smul_apply, hR k, smul_eq_mul])

/-- **`|Rm|²` computed in an arbitrary spanning family.**  If `e : Fin (finrank ℝ E) → TₓM` spans
the tangent space at `x` and `Γ` is its Gram matrix (`Γ i j = g.inner x (e i) (e j)`), then the
Frobenius norm of the curvature computed in the chosen orthonormal frame equals the full
contraction of the curvature components in `e` with `Γ⁻¹`. -/
theorem rmNormSq_eq_N4_of_span
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    (hLC : LCSmooth I M) {g : SMet I M} (x : M)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (Γ : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ)
    (hΓ : ∀ i j, Γ i j = g.inner x (e i) (e j))
    (hb : Submodule.span ℝ (Set.range e) = ⊤) :
    rmNormSq g x = N4 Γ (rmFrame g x e) := by
  classical
  by_cases hn : 0 < Module.finrank ℝ E
  · letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
    haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
    haveI : Nonempty (Fin (Module.finrank ℝ E)) := Fin.pos_iff_nonempty.mp hn
    -- the `Classical.epsilon` frame is orthonormal, hence a basis
    have hon : Orthonormal ℝ (onFrame g x) := by
      rw [orthonormal_iff_ite]
      intro i j
      rw [show Inner.inner ℝ (onFrame g x i) (onFrame g x j)
            = g.inner x (onFrame g x i) (onFrame g x j) from rfl]
      exact isONFrame_onFrame g x i j
    have hcard : Fintype.card (Fin (Module.finrank ℝ E))
        = Module.finrank ℝ (TangentSpace I x) := by rw [Fintype.card_fin]; rfl
    let b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) :=
      basisOfOrthonormalOfCardEqFinrank hon hcard
    have hbcoe : ⇑b = onFrame g x := coe_basisOfOrthonormalOfCardEqFinrank hon hcard
    have honb : Orthonormal ℝ (⇑b) := by rw [hbcoe]; exact hon
    -- `e` is a basis too (it spans and has `finrank` elements)
    have hli : LinearIndependent ℝ e := by
      rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank, hb, finrank_top]
      exact hcard
    have hsp : ⊤ ≤ Submodule.span ℝ (Set.range e) := by rw [hb]
    let c : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) :=
      Module.Basis.mk hli hsp
    have hc : ⇑c = e := Module.Basis.coe_mk hli hsp
    -- the matrix of coordinates of `e` in the orthonormal basis `b`
    let B : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
      (b.toMatrix ⇑c)ᵀ
    have hB_apply : ∀ i j, B i j = (b.repr (c i)) j := fun i j => by
      simp only [B, Matrix.transpose_apply, Module.Basis.toMatrix_apply]
    have hAe_b : ∀ i, e i = ∑ j, B i j • b j := by
      intro i
      have h1 : (∑ j, B i j • b j) = c i := by
        rw [show (∑ j, B i j • b j) = ∑ j, (b.repr (c i)) j • b j from
              Finset.sum_congr rfl (fun j _ => by rw [hB_apply i j])]
        exact b.sum_repr (c i)
      rw [h1, congrFun hc i]
    have hBunit : IsUnit B.det := by
      have h1 : c.toMatrix ⇑b * (b.toMatrix ⇑c) = 1 := by
        rw [Module.Basis.toMatrix_mul_toMatrix, Module.Basis.toMatrix_self]
      have hne : (b.toMatrix ⇑c).det ≠ 0 := Matrix.det_ne_zero_of_left_inverse h1
      rw [show B.det = (b.toMatrix ⇑c).det from by simp only [B, Matrix.det_transpose]]
      exact isUnit_iff_ne_zero.mpr hne
    -- the Gram matrix `Γ` is `B * Bᵀ`
    have hBBt : Γ = B * Bᵀ := by
      ext i j
      rw [hΓ i j, Matrix.mul_apply]
      rw [Finset.sum_congr rfl (fun k _ => by rw [Matrix.transpose_apply])]
      rw [hAe_b i, hAe_b j]
      exact inner_sum_smul_sum_smul g x (⇑b)
        (fun k l => by
          rw [show g.inner x (b k) (b l) = Inner.inner ℝ (b k) (b l) from rfl]
          exact (orthonormal_iff_ite.mp honb) k l)
        (fun k => B i k) (fun l => B j l)
    have hAe : ∀ i, e i = ∑ j, B i j • onFrame g x j := by
      intro i
      rw [hAe_b i]
      exact Finset.sum_congr rfl (fun j _ => by rw [congrFun hbcoe j])
    rw [show rmNormSq g x = frobSq (rmFrame g x (onFrame g x)) from rfl]
    rw [← frobSq_rot B hBunit (rmFrame g x (onFrame g x)),
        ← rmFrame_eq_rot hLC g x (onFrame g x) e B hAe, hBBt]
  · -- `finrank ℝ E = 0`: both sides are empty sums
    have h0 : Module.finrank ℝ E = 0 := Nat.eq_zero_of_not_pos hn
    haveI : IsEmpty (Fin (Module.finrank ℝ E)) := by rw [h0]; infer_instance
    simp only [rmNormSq, rmC, Submission.Diff.Alg.frobSq, N4, Finset.univ_eq_empty,
      Finset.sum_empty]

section ChartFrame

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- At every point of the chart at `x₀`, the coordinate frame `cFrame x₀ ·` is a basis: its span is
everything.  (The expansion of any section in the coordinate frame is
`Commons.Geometry.Manifold.Tangent.eqOn_sum_frameSection_of_basis`.) -/
theorem cFrame_span_chart (x₀ : M) {p : M} (hp : p ∈ (chartAt H x₀).source) :
    Submodule.span ℝ (Set.range (fun i : Fin (Module.finrank ℝ E) ↦ cFrame (I := I) x₀ i p))
      = ⊤ := by
  refine Submodule.eq_top_iff'.2 fun w => ?_
  have hb : p ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]; exact hp
  set c := (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ p w with hc
  have hspec : Submission.Geodesic.frameSection (I := I) x₀ c p
      = ∑ i : Fin (Module.finrank ℝ E), ((Module.finBasis ℝ E).coord i) c
          • cFrame (I := I) x₀ i p := by
    have h1 := Commons.Geometry.Manifold.Tangent.eqOn_sum_frameSection_of_basis (I := I)
      (b := Module.finBasis ℝ E) x₀ (Submission.Geodesic.frameSection (I := I) x₀ c) hp
    have h2 : (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ p
        (Submission.Geodesic.frameSection (I := I) x₀ c p) = c := by
      show (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ p
        ((trivializationAt E (TangentSpace I) x₀).symmL ℝ p c) = c
      exact Bundle.Trivialization.continuousLinearMapAt_symmL _ hb c
    have h3 := h1
    simp only [] at h3
    rw [h3, h2]
    rfl
  have hlhs : Submission.Geodesic.frameSection (I := I) x₀ c p = w :=
    (trivializationAt E (TangentSpace I) x₀).symmL_continuousLinearMapAt hb w
  rw [← hlhs, hspec]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
  exact Submodule.subset_span (Set.mem_range_self i)

end ChartFrame

/-- **`|Rm|²` in the coordinate frame of a chart.** -/
theorem rmNormSq_eq_N4
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    (hLC : LCSmooth I M) (G : ℝ → SMet I M) {x₀ : M} (t : ℝ) {y : M}
    (hy : y ∈ (chartAt H x₀).source) :
    rmNormSq (G t) y
      = N4 (GramM (I := I) G x₀ t y) (rmC4 (I := I) G x₀ t y) := by
  refine rmNormSq_eq_N4_of_span (I := I) hLC y (fun i ↦ cFrame (I := I) x₀ i y)
    (GramM (I := I) G x₀ t y) (fun i j ↦ rfl) (cFrame_span_chart (I := I) x₀ hy)

end Work.Diff.GE
