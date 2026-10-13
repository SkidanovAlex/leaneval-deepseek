import Mathlib
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE2.local_graph_of_submersion
import Submission.Work.WilE9.Ift.ift_exists

set_option autoImplicit false
noncomputable section

namespace Work.WilE7

open Classical Filter Topology

/-- Local section (implicit function / submersion graph) for a system `F` of `q` EA
polynomials in `p + q` variables: if `F` vanishes at `(x₀, y₀)` and its Jacobian in the
fibre (`y`) directions is invertible there, then locally near `x₀` the zero set of `F` is
the graph of a continuous — indeed `C¹` — function `φ`, and this graph is locally unique. -/
theorem localSection {p q r : ℕ} (c : WilkiesDesign.E.EAChain (p + q) r)
    (F : Fin q → WilkiesDesign.E.EAPoly (p + q) r) (x₀ : Fin p → ℝ) (y₀ : Fin q → ℝ)
    (h0 : ∀ a, WilkiesDesign.E.eaEval c (F a) (Fin.append x₀ y₀) = 0)
    (hdet : (Matrix.of fun (a : Fin q) (l : Fin q) =>
      WilkiesDesign.E.eaEval c (WilkiesDesign.E.eaD c (Fin.natAdd p l) (F a))
        (Fin.append x₀ y₀)).det ≠ 0) :
    ∃ (U : Set (Fin p → ℝ)) (φ : (Fin p → ℝ) → (Fin q → ℝ)) (B : Set (Fin q → ℝ)),
      IsOpen U ∧ x₀ ∈ U ∧ IsOpen B ∧ y₀ ∈ B ∧ φ x₀ = y₀ ∧ ContinuousOn φ U ∧
      (∀ x ∈ U, ∀ a, WilkiesDesign.E.eaEval c (F a) (Fin.append x (φ x)) = 0) ∧
      (∀ x ∈ U, ∀ v ∈ B, (∀ a, WilkiesDesign.E.eaEval c (F a) (Fin.append x v) = 0) → v = φ x) := by
  classical
  -- The fibre Jacobian at `(x₀, y₀)`, i.e. the matrix of `hdet`.
  set A : Matrix (Fin q) (Fin q) ℝ :=
    (Matrix.of fun (a : Fin q) (l : Fin q) =>
      WilkiesDesign.E.eaEval c (WilkiesDesign.E.eaD c (Fin.natAdd p l) (F a))
        (Fin.append x₀ y₀)) with hA
  have hAdet : A.det ≠ 0 := by simpa only [hA] using hdet
  have hAunit : IsUnit A.det := isUnit_iff_ne_zero.mpr hAdet
  -- The curried graph map `(u, v) ↦ (a ↦ eaEval c (F a) (append u v))`.
  let g : (Fin p → ℝ) → (Fin q → ℝ) → (Fin q → ℝ) :=
    fun u v a => WilkiesDesign.E.eaEval c (F a) (Fin.append u v)
  have huncurry : Function.uncurry g = Work.WilE9.Ift.graphEval c F := rfl
  -- Smoothness of the graph map.
  have hcont : ContDiffAt ℝ 1 (Function.uncurry g) (x₀, y₀) := by
    rw [huncurry]
    exact (Work.WilE9.Ift.graphEval_contDiff c F).contDiffAt.of_le le_top
  -- Vanishing at the base point.
  have hg0 : g x₀ y₀ = 0 := by
    funext a
    exact h0 a
  -- The derivative of the graph map, and its invertibility in the fibre directions.
  have hderiv : HasFDerivAt (Work.WilE9.Ift.graphEval c F)
      (ContinuousLinearMap.pi fun a : Fin q =>
        Work.WilE9.Ift.ambDeriv c (F a) (Fin.append x₀ y₀) ∘SL Work.WilE9.Ift.appendCLM p q)
      (x₀, y₀) := Work.WilE9.Ift.hasFDerivAt_graphEval c F x₀ y₀
  have hinv : (fderiv ℝ (Function.uncurry g) (x₀, y₀) ∘SL
      ContinuousLinearMap.inr ℝ (Fin p → ℝ) (Fin q → ℝ)).IsInvertible := by
    have hL : fderiv ℝ (Function.uncurry g) (x₀, y₀) =
        ContinuousLinearMap.pi fun a : Fin q =>
          Work.WilE9.Ift.ambDeriv c (F a) (Fin.append x₀ y₀) ∘SL Work.WilE9.Ift.appendCLM p q := by
      rw [huncurry]
      exact hderiv.fderiv
    have hpt : ∀ v : Fin q → ℝ,
        ((fderiv ℝ (Function.uncurry g) (x₀, y₀)) ∘SL
          ContinuousLinearMap.inr ℝ (Fin p → ℝ) (Fin q → ℝ)) v = Matrix.mulVec A v := by
      intro v
      rw [hL, hA]
      exact Work.WilE9.Ift.graphEval_snd c F x₀ y₀ v
    refine ⟨(Matrix.toLinearEquiv' A (Matrix.invertibleOfIsUnitDet A hAunit)).toContinuousLinearEquiv,
      ?_⟩
    apply ContinuousLinearMap.ext
    intro v
    rw [hpt v]
    change (Matrix.toLin' A) v = Matrix.mulVec A v
    exact Matrix.toLin'_apply A v
  -- Apply the submersion graph theorem.
  obtain ⟨φ, U, B, hUo, hBo, hx0U, hy0B, hφcd, hφ0, hφeq, hφuniq⟩ :=
    Work.WilE2.local_graph_of_submersion g x₀ y₀ hcont hg0 hinv
  refine ⟨U, φ, B, hUo, hx0U, hBo, hy0B, hφ0, hφcd.continuousOn, ?_, ?_⟩
  · intro x hx a
    exact congrFun (hφeq x hx) a
  · intro x hx v hv hv0
    apply hφuniq x hx v hv
    funext a
    exact hv0 a

end Work.WilE7
