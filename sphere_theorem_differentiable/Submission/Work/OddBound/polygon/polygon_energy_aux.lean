import Mathlib
import Submission.Work.OddBound.LiftKit

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Auxiliary lemmas for the polygonal energy bound

This module collects the four elementary ingredients of
`Work.OddBound.polygon.polygon_energy_le_curve_energy` (the energy of the inscribed polygon of a
`C¹` curve is at most the energy of the curve), so that the file holding the theorem itself
contains nothing but the theorem:

* `continuous_curveSpeed` — the Riemannian speed of a globally `C¹` curve is continuous;
* `riemannianDist_le_curveLength_Icc` — the Riemannian distance is bounded by the length of the
  curve on an arbitrary interval `[a,b]`;
* `sum_range_integral_chain` — interval integrals telescope along a chain of points;
* `integral_eq_sum_division` — the integral over `[0,1]` is the sum over the `N` equal pieces.
-/

namespace Work.OddBound.polygon

open scoped ContDiff Manifold
open Bundle
open ContDiff
open Set
open MeasureTheory
open scoped Interval

set_option linter.unusedSectionVars false

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]

/-- **The Riemannian speed of a globally `C¹` curve is continuous.**  This is the tangent map
`tangentMap 𝓘(ℝ) I c` (continuous because `c` is `C¹`) composed with the constant unit section of
the tangent bundle of the model space `ℝ`, followed by the inner product of the two copies of the
velocity (continuous along continuous sections of a continuous Riemannian bundle) and a square
root. -/
lemma continuous_curveSpeed {c : ℝ → M} (hc : ContMDiff 𝓘(ℝ) I 1 c) :
    Continuous (fun t : ℝ => Submission.Length.curveSpeed (I := I) c t) := by
  haveI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) := by
    obtain ⟨Φ, hΦsm, hΦ⟩ := (inferInstance : IsContMDiffRiemannianBundle I ∞ E
      (fun x : M ↦ TangentSpace I x)).exists_contMDiff
    exact ⟨Φ, hΦsm.continuous, hΦ⟩
  have hT : Continuous (tangentMap 𝓘(ℝ) I c) := hc.continuous_tangentMap le_rfl
  have hκ : Continuous (fun t : ℝ =>
      (Bundle.TotalSpace.mk' ℝ t (1 : TangentSpace 𝓘(ℝ) t) : TangentBundle 𝓘(ℝ) ℝ)) :=
    ((contMDiff_vectorSpace_iff_contDiff (𝕜 := ℝ) (n := ∞) (E := ℝ)
      (V := fun t : ℝ => (1 : TangentSpace 𝓘(ℝ) t))).mpr contDiff_const).continuous
  have hcomp : Continuous (fun t : ℝ =>
      (⟨c t, (mfderiv 𝓘(ℝ) I c t) (1 : ℝ)⟩ : TangentBundle I M)) := hT.comp hκ
  have hinner : Continuous (fun t : ℝ => inner ℝ ((mfderiv 𝓘(ℝ) I c t) (1 : ℝ))
      ((mfderiv 𝓘(ℝ) I c t) (1 : ℝ))) := by
    have h := ContinuousOn.inner_bundle (b := c)
      (v := fun t : ℝ => (mfderiv 𝓘(ℝ) I c t) (1 : ℝ))
      (w := fun t : ℝ => (mfderiv 𝓘(ℝ) I c t) (1 : ℝ))
      (s := Set.univ) hcomp.continuousOn hcomp.continuousOn
    rwa [continuousOn_univ] at h
  convert hinner.sqrt using 1
  ext t
  rw [Submission.Length.curveSpeed_def, Submission.Geodesic.curveVelocity_apply]

/-- **The Riemannian distance is bounded by the length of a `C¹` curve on an arbitrary
interval.**  For `a ≤ b` the curve segment `[a,b] ∋ t ↦ c t` is reparametrised to `[0,1]` (an
orientation preserving affine substitution, under which the length is invariant), and
`Submission.Distance.riemannianDist_le_curveLength` bounds the distance by the length of that
segment. -/
lemma riemannianDist_le_curveLength_Icc {c : ℝ → M} (hc : ContMDiff 𝓘(ℝ) I 1 c) {a b : ℝ}
    (hab : a ≤ b) :
    Submission.Distance.riemannianDist (I := I) (c a) (c b)
      ≤ Submission.Length.curveLength (I := I) c a b := by
  rcases eq_or_lt_of_le hab with h | h
  · subst h
    rw [Submission.Distance.riemannianDist_self, Submission.Length.curveLength_self]
  · set h' : ℝ := b - a with hh
    have hpos : 0 < h' := sub_pos.mpr h
    have haff : ContMDiff 𝓘(ℝ) 𝓘(ℝ) 1 (fun s : ℝ => h' * s + a) :=
      ((contMDiff_const (c := h')).mul contMDiff_id).add contMDiff_const |>.of_le le_top
    have hγ : ContMDiff 𝓘(ℝ) I 1 (fun s : ℝ => c (h' * s + a)) := hc.comp haff
    refine (Submission.Distance.riemannianDist_le_curveLength (I := I)
      (fun s : ℝ => c (h' * s + a)) hγ (c a) (c b) ?_ ?_).trans (le_of_eq ?_)
    · show c (h' * 0 + a) = c a
      congr 1; ring
    · show c (h' * 1 + a) = c b
      congr 1; rw [hh]; ring
    · have hcomp := Submission.Length.curveLength_comp_mul_add_of_le (I := I) (γ := c)
        (c := h') (d := a) (a := 0) (b := 1) hpos zero_le_one
        (fun t _ => hc.mdifferentiableAt (by norm_num))
      rw [hcomp]
      norm_num
      congr 1
      rw [hh]; ring

/-- **Telescoping of interval integrals along a chain.**  For a continuous `f` and any sequence of
points `x`, the sum of the integrals of `f` over the successive intervals `[x k, x (k+1)]`,
`k < n`, is the integral over `[x 0, x n]`.  (No monotonicity of `x` is needed: interval integrals
are additive over adjacent intervals in the signed sense.) -/
lemma sum_range_integral_chain (f : ℝ → ℝ) (hf : Continuous f) (x : ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range n, ∫ t in x k..x (k+1), f t = ∫ t in x 0..x n, f t := by
  induction n with
  | zero => rw [Finset.sum_range_zero, intervalIntegral.integral_same]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)]

/-- **The interval integral is the sum over the `N` equal pieces of `[0,1]`.**  For a continuous `f`
and `0 < N`, the sum of the integrals of `f` over the successive intervals
`[i/N, (i+1)/N]`, `i = 0, …, N-1`, is the integral of `f` over `[0,1]`. -/
lemma integral_eq_sum_division (f : ℝ → ℝ) (hf : Continuous f) {N : ℕ} (hN : 0 < N) :
    ∑ i ∈ Finset.range N, ∫ t in ((i:ℝ)/N)..(((i:ℝ)+1)/N), f t = ∫ t in (0:ℝ)..1, f t := by
  have hchain := sum_range_integral_chain f hf (fun k : ℕ => ((k:ℝ))/N) N
  have hsucc : ∀ k : ℕ, ((((k+1 : ℕ)) : ℝ))/N = (((k:ℝ))+1)/N := by
    intro k; rw [Nat.cast_add, Nat.cast_one]
  simp only [hsucc] at hchain
  rw [hchain]
  have hNn : ((N:ℝ)) ≠ 0 := by positivity
  simp only [Nat.cast_zero, zero_div, div_self hNn]

end Work.OddBound.polygon
