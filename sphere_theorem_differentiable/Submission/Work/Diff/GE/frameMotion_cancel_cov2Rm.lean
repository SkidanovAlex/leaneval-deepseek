import Mathlib
import Submission.Work.Diff.GE.CurvDerivDefs
import Submission.Work.Diff.GE.kato_cov3RmExt_field
import Submission.Work.Diff.GE.covRic_eq_sum_covRm
import Submission.Work.Diff.GE.curvbasic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.style.haveILetI false

namespace Work.Diff.GE

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

/-! ## Elementary multilinearity of `cov2Rm` in its first two slots, summed form

`Kato3.cov2Rm_lin_first` / `Kato3.cov2Rm_lin_snd` give the pointwise `ℝ`-bilinearity of
`∇²Rm` in the two differentiation slots; the finite-sum form is what is needed to expand a
covariant derivative in an orthonormal frame. -/

theorem cov2Rm_add_fst (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (v₁ v₂ w a b c d : TangentSpace I x) :
    cov2Rm g x (v₁ + v₂) w a b c d = cov2Rm g x v₁ w a b c d + cov2Rm g x v₂ w a b c d := by
  have h := Kato3.cov2Rm_lin_first (I := I) (M := M) hLC g x 1 1 v₁ v₂ w a b c d
  simpa using h

theorem cov2Rm_smul_fst (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (r : ℝ) (v w a b c d : TangentSpace I x) :
    cov2Rm g x (r • v) w a b c d = r * cov2Rm g x v w a b c d := by
  have h := Kato3.cov2Rm_lin_first (I := I) (M := M) hLC g x r 0 v 0 w a b c d
  simpa using h

theorem cov2Rm_sum_fst (hLC : LCSmooth I M) (g : SMet I M) (x : M) {ι : Type*}
    (s : Finset ι) (c : ι → ℝ) (v : ι → TangentSpace I x) (w a b c' d : TangentSpace I x) :
    cov2Rm g x (∑ i ∈ s, c i • v i) w a b c' d = ∑ i ∈ s, c i * cov2Rm g x (v i) w a b c' d := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (cov2Rm_smul_fst (I := I) (M := M) hLC g x 0 (0 : TangentSpace I x)
      w a b c' d)
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi,
        cov2Rm_add_fst (I := I) (M := M) hLC g x,
        cov2Rm_smul_fst (I := I) (M := M) hLC g x, ih]

theorem cov2Rm_add_snd (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (v w₁ w₂ a b c d : TangentSpace I x) :
    cov2Rm g x v (w₁ + w₂) a b c d = cov2Rm g x v w₁ a b c d + cov2Rm g x v w₂ a b c d := by
  have h := Kato3.cov2Rm_lin_snd (I := I) (M := M) hLC g x 1 1 v w₁ w₂ a b c d
  simpa using h

theorem cov2Rm_smul_snd (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (r : ℝ) (v w a b c d : TangentSpace I x) :
    cov2Rm g x v (r • w) a b c d = r * cov2Rm g x v w a b c d := by
  have h := Kato3.cov2Rm_lin_snd (I := I) (M := M) hLC g x r 0 v w 0 a b c d
  simpa using h

theorem cov2Rm_sum_snd (hLC : LCSmooth I M) (g : SMet I M) (x : M) {ι : Type*}
    (s : Finset ι) (c : ι → ℝ) (v : ι → TangentSpace I x) (w a b c' d : TangentSpace I x) :
    cov2Rm g x w (∑ i ∈ s, c i • v i) a b c' d = ∑ i ∈ s, c i * cov2Rm g x w (v i) a b c' d := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (cov2Rm_smul_snd (I := I) (M := M) hLC g x 0 w
      (0 : TangentSpace I x) a b c' d)
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi,
        cov2Rm_add_snd (I := I) (M := M) hLC g x,
        cov2Rm_smul_snd (I := I) (M := M) hLC g x, ih]

/-- **Cancellation of the frame-motion terms in the trace of `∇²Rm`.**  Let `F` be a family of
globally `C^∞` vector fields which is `g`-orthonormal near `x`.  Then the two terms produced by
differentiating the frame `m ↦ F m` inside the trace `∑ m, cov2Rm g · (F m ·) (F m ·) a b c d`
cancel in the sum:

`∑ m, (cov2Rm g x (∇_v F m) (F m x) a b c d + cov2Rm g x (F m x) (∇_v F m) a b c d) = 0`,

where `∇_v F m = lcOf g (F m) x v`.  Proof: expand `∇_v F m = ∑ k, ω m k • F k x` with
`ω m k := g.inner x (∇_v F m) (F k x)` (orthonormal-frame expansion, e.g.
`Work.Diff.GE.sum_smul_inner_eq_self`); orthonormality near `x` plus metric compatibility of `lcOf g`
(component `2.2` of the hypothesis `hLC`, i.e. `Work.Diff.GE.covRic_frame_skew`) give
`ω m k + ω k m = 0`; the pointwise `ℝ`-bilinearity of `cov2Rm g x` in its first two slots
(`Work.Diff.GE.Kato3.cov2Rm_lin_first`, `Work.Diff.GE.Kato3.cov2Rm_lin_snd`) then turns the sum into
an antisymmetric matrix contracted with the summand pair
`(k,m) ↦ cov2Rm g x (F k x) (F m x) a b c d`, which vanishes
(`Work.Diff.GE.covRic_skew_sum_zero`, or a private copy of the same algebra). -/
theorem frameMotion_cancel_cov2Rm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (x : M)
    (F : Fin (Module.finrank ℝ E) → (Π y : M, TangentSpace I y))
    (hFs : ∀ i, Work.Diff.GE.SmoothField M (F i))
    (hFON : Work.Diff.GE.OnFrameNear g x F)
    (v : TangentSpace I x) (a b c d : TangentSpace I x) :
    ∑ m, (Work.Diff.GE.cov2Rm g x (Submission.Diff.lcOf g (F m) x v) (F m x) a b c d
        + Work.Diff.GE.cov2Rm g x (F m x) (Submission.Diff.lcOf g (F m) x v) a b c d) = 0 := by
  classical
  -- the frame is orthonormal at `x` itself
  have hONx : IsONFrame g x (fun m => F m x) := hFON.self_of_nhds
  -- the matrix `ω m k = ⟪∇_v F m, F k⟫` is skew
  have hskew : ∀ m k, g.inner x (lcOf g (F m) x v) (F k x)
      = -g.inner x (lcOf g (F k) x v) (F m x) := by
    intro m k
    have h := covRic_frame_skew (I := I) (M := M) hLC g x v F hFs hFON m k
    rw [← g.symm x (lcOf g (F k) x v) (F m x)] at h
    linarith
  by_cases hfr : 0 < Module.finrank ℝ E
  · -- expansion of `∇_v F m` in the orthonormal frame at `x`
    have hexp : ∀ m, lcOf g (F m) x v = ∑ k, g.inner x (lcOf g (F m) x v) (F k x) • F k x :=
      fun m => (sum_smul_inner_eq_self (I := I) (M := M) g x hfr (fun i => F i x) hONx
        (lcOf g (F m) x v)).symm
    -- first family of terms
    have hP : (∑ m, cov2Rm g x (lcOf g (F m) x v) (F m x) a b c d)
        = ∑ m, ∑ k, g.inner x (lcOf g (F m) x v) (F k x)
            * cov2Rm g x (F k x) (F m x) a b c d := by
      refine Finset.sum_congr rfl fun m _ => ?_
      conv_lhs => rw [hexp m]
      exact cov2Rm_sum_fst (I := I) (M := M) hLC g x Finset.univ _
        (fun k => F k x) (F m x) a b c d
    -- second family of terms
    have hR : (∑ m, cov2Rm g x (F m x) (lcOf g (F m) x v) a b c d)
        = ∑ m, ∑ k, g.inner x (lcOf g (F m) x v) (F k x)
            * cov2Rm g x (F m x) (F k x) a b c d := by
      refine Finset.sum_congr rfl fun m _ => ?_
      conv_lhs => rw [hexp m]
      exact cov2Rm_sum_snd (I := I) (M := M) hLC g x Finset.univ _
        (fun k => F k x) (F m x) a b c d
    rw [Finset.sum_add_distrib, hP, hR]
    exact covRic_skew_sum_zero (fun m k => g.inner x (lcOf g (F m) x v) (F k x))
      (fun u w => cov2Rm g x (F u x) (F w x) a b c d) hskew
  · -- degenerate case: the frame is empty and so is the sum
    have h0 : Module.finrank ℝ E = 0 := Nat.eq_zero_of_not_pos hfr
    haveI : IsEmpty (Fin (Module.finrank ℝ E)) := by rw [h0]; infer_instance
    simp [Finset.univ_eq_empty]

end Work.Diff.GE

