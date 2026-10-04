import Mathlib
import Submission.Work.Diff.L.Defs
import Submission.Work.Diff.GE.curvbasic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The curvature form `R4 (rmFrame g x e)` is the curvature paired with the frame vectors

`R4 (rmFrame g x e) a b c d` is Hamilton's `R(a, b, c, d) = ∑ Rᵢⱼₖₗ aᵢ bⱼ cₖ dₗ` formed from the
frame components `rmFrame g x e i j k l = g(R(eᵢ,eⱼ)e_l, e_k)`.  This file proves that it is the
plain evaluation of the pointwise curvature `rmVec (lcOf g) x` on the expanded vectors, paired with
`g.inner x` — i.e. that `rmFrame`-component contraction and vector substitution commute.

Everything is the multilinearity of `rmVec` (`Work.Diff.GE.rmVec_sum_left/middle/right`), the
bilinearity of `g.inner x`, and the index bookkeeping of the four sums.  No orthonormality of `e`
(and no torsion-freeness or metric compatibility) is used: the identity holds for an arbitrary
frame, which is what the `Work.Diff.L` assembly needs.

The headline lemma is the `initSMet` instance of `R4_rmFrame_eq_inner`, with the inner product
spelled as the ambient-instance `inner ℝ`.
-/

set_option linter.unusedSectionVars false

namespace Work.Diff.L

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [T2Space M]

section Helpers

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-! ## Elementary expansion lemmas -/

/-- Multilinearity of `rmVec` in its three vector slots, as a nested sum over `Fin n`. -/
private lemma rmVec_sum3
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞)
    (x : M) (n : ℕ) (c₁ c₂ c₃ : Fin n → ℝ) (u v w : Fin n → TangentSpace I x) :
    rmVec cov x (∑ a, c₁ a • u a) (∑ b, c₂ b • v b) (∑ d, c₃ d • w d)
      = ∑ a, ∑ b, ∑ d, (c₁ a * c₂ b * c₃ d) • rmVec cov x (u a) (v b) (w d) := by
  rw [Work.Diff.GE.rmVec_sum_left cov hcov (s := Finset.univ)]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Work.Diff.GE.rmVec_sum_middle cov hcov (s := Finset.univ)]
  simp only [Finset.smul_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Work.Diff.GE.rmVec_sum_right cov hcov (s := Finset.univ)]
  simp only [Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  ring_nf

/-- Bilinearity of `g.inner x` in the second slot on a sum. -/
private lemma inner_smul_sum (g : SMet I M) (n : ℕ) (x : M) (u : TangentSpace I x)
    (c : Fin n → ℝ) (v : Fin n → TangentSpace I x) :
    g.inner x u (∑ i, c i • v i) = ∑ i, c i * g.inner x u (v i) := by
  simp only [map_sum, map_smul, smul_eq_mul]

/-- Bilinearity of `g.inner x` in the first slot on a triple sum. -/
private lemma inner_nested3_left (g : SMet I M) (x : M) (n : ℕ)
    (c : Fin n → Fin n → Fin n → ℝ) (u : Fin n → Fin n → Fin n → TangentSpace I x)
    (z : TangentSpace I x) :
    g.inner x (∑ a, ∑ b, ∑ d, c a b d • u a b d) z
      = ∑ a, ∑ b, ∑ d, c a b d * g.inner x (u a b d) z := by
  simp only [map_sum, sum_apply, map_smul, smul_apply, smul_eq_mul]

/-- Bilinearity of `g.inner x` on a triple sum in the first slot and a single sum in the second. -/
private lemma inner_nested3 (g : SMet I M) (x : M) (n : ℕ)
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

/-- Index bookkeeping: the fourfold sum produced by the multilinearity expansion (index order
`a b d k`, curvature slot `d` inside the third vector slot) is the one in `R4`'s order
(`a b k d`), with the `l`-sum and the `k`-sum interchanged. -/
private lemma sum_reorder4 (n : ℕ) (G : Fin n → Fin n → Fin n → Fin n → ℝ)
    (a b c d : Fin n → ℝ) :
    (∑ i, ∑ j, ∑ k, ∑ l, G i j l k * a i * b j * c k * d l)
      = ∑ i, ∑ j, ∑ k, ∑ l, (a i * b j * d k) * c l * G i j k l := by
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => by ring))

/-! ## The identity -/

/-- `R4` of the frame components of the curvature is the pointwise curvature evaluated on the
expanded vectors: for any frame `e` at `x` and coefficients `a, b, c, d`,
`R4 (rmFrame g x e) a b c d = g(R(∑ᵢaᵢeᵢ, ∑ⱼbⱼeⱼ)∑ₖdₖeₖ, ∑ₗcₗeₗ)`. -/
theorem R4_rmFrame_eq_inner (g : SMet I M)
    (hcov : ContMDiffCovariantDerivative (lcOf g) ∞)
    (x : M) (e : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (a b c d : Fin (Module.finrank ℝ E) → ℝ) :
    R4 (rmFrame g x e) a b c d
      = g.inner x (rmVec (lcOf g) x (∑ i, a i • e i) (∑ j, b j • e j) (∑ k, d k • e k))
          (∑ l, c l • e l) := by
  rw [rmVec_sum3 (lcOf g) hcov x (Module.finrank ℝ E) a b d e e e]
  rw [inner_nested3 g x (Module.finrank ℝ E) (fun i j k => a i * b j * d k)
        (fun i j k => rmVec (lcOf g) x (e i) (e j) (e k)) c e]
  unfold R4 rmFrame
  exact sum_reorder4 (Module.finrank ℝ E)
    (fun i j k l => g.inner x (rmVec (lcOf g) x (e i) (e j) (e k)) (e l)) a b c d

end Helpers

/-- The curvature form of the ambient metric expanded in a frame: `R4 (rmFrame initSMet x e) a b c d`
is the ambient inner product of `R(∑ᵢaᵢeᵢ, ∑ⱼbⱼeⱼ)∑ₖdₖeₖ` with `∑ₗcₗeₗ`.  (`e` need not be
orthonormal.) -/
theorem R4_rmFrame_initSMet_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M]
    [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]
    (hLC : LCSmooth I M)
    (x : M) (e : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (a b c d : Fin (Module.finrank ℝ E) → ℝ) :
    R4 (rmFrame (initSMet (I := I) (M := M)) x e) a b c d
      = inner ℝ (rmVec (lcOf (initSMet (I := I) (M := M))) x
          (∑ i, a i • e i) (∑ j, b j • e j) (∑ k, d k • e k)) (∑ l, c l • e l) := by
  have hcov : ContMDiffCovariantDerivative (lcOf (initSMet (I := I) (M := M))) ∞ := by
    obtain ⟨hcov, -, -⟩ := hLC (initSMet (I := I) (M := M))
    exact hcov.some
  rw [R4_rmFrame_eq_inner (initSMet (I := I) (M := M)) hcov x e a b c d]
  exact initSMet_inner x _ _

end Work.Diff.L
