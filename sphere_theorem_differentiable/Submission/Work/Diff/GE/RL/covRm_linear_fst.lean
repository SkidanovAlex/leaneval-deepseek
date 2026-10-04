import Mathlib
import Submission.Work.Diff.GE.RL.Kit

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `ℝ`-linearity of `covRm` in its first argument (the direction `v`)

`covRm g x v a b c d = dRmPhi g x v (smoothExt x a) … (smoothExt x d)` (`covRm_eq_dRmPhi`), and
`dRmPhi g x v A B C D` is

`mvfderiv I (fun y ↦ rmP g y (A y) (B y) (C y) (D y)) x v − Σₖ rmP … ((lcOf g) · x v) …`

The direction `v` occurs only *linearly*: as the argument of the continuous linear map
`mvfderiv I F x` and of each of the four continuous linear maps `(lcOf g) T x`, and each of these
occurrences sits in a slot in which `rmP` is `ℝ`-linear (`rmP_add_fst/snd/thd/fth`,
`rmP_smul_fst/snd/thd/fth`).  So `dRmPhi` — and hence `covRm` — is `ℝ`-linear in `v`, which is the
statement of `CovRmLinFst`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.GE.RL

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

/-- `dRmPhi` is `ℝ`-linear in its direction argument `v`.  The direction appears only as the
argument of the continuous linear maps `mvfderiv I _ x` and `(lcOf g) T x`, and every such
occurrence sits in a slot in which `rmP` is linear. -/
theorem dRmPhi_linear_dir (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (A B C D : Π y : M, TangentSpace I y) (r s : ℝ) (v₁ v₂ : TangentSpace I x) :
    dRmPhi g x (r • v₁ + s • v₂) A B C D
      = r * dRmPhi g x v₁ A B C D + s * dRmPhi g x v₂ A B C D := by
  -- the derivative term: `mvfderiv I F x` is a continuous linear map
  have hdir : mvfderiv I (fun y : M => rmP g y (A y) (B y) (C y) (D y)) x (r • v₁ + s • v₂)
      = r * mvfderiv I (fun y : M => rmP g y (A y) (B y) (C y) (D y)) x v₁
        + s * mvfderiv I (fun y : M => rmP g y (A y) (B y) (C y) (D y)) x v₂ := by
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  -- the four connection corrections, each in the slot of `rmP` where it occurs
  have hconnA : (lcOf g) A x (r • v₁ + s • v₂)
      = r • (lcOf g) A x v₁ + s • (lcOf g) A x v₂ := by
    rw [map_add, map_smul, map_smul]
  have hconnB : (lcOf g) B x (r • v₁ + s • v₂)
      = r • (lcOf g) B x v₁ + s • (lcOf g) B x v₂ := by
    rw [map_add, map_smul, map_smul]
  have hconnC : (lcOf g) C x (r • v₁ + s • v₂)
      = r • (lcOf g) C x v₁ + s • (lcOf g) C x v₂ := by
    rw [map_add, map_smul, map_smul]
  have hconnD : (lcOf g) D x (r • v₁ + s • v₂)
      = r • (lcOf g) D x v₁ + s • (lcOf g) D x v₂ := by
    rw [map_add, map_smul, map_smul]
  have hc₁ : rmP g x ((lcOf g) A x (r • v₁ + s • v₂)) (B x) (C x) (D x)
      = r * rmP g x ((lcOf g) A x v₁) (B x) (C x) (D x)
        + s * rmP g x ((lcOf g) A x v₂) (B x) (C x) (D x) := by
    rw [hconnA]
    simp only [rmP_add_fst g hLC, rmP_smul_fst g hLC]
  have hc₂ : rmP g x (A x) ((lcOf g) B x (r • v₁ + s • v₂)) (C x) (D x)
      = r * rmP g x (A x) ((lcOf g) B x v₁) (C x) (D x)
        + s * rmP g x (A x) ((lcOf g) B x v₂) (C x) (D x) := by
    rw [hconnB]
    simp only [rmP_add_snd g hLC, rmP_smul_snd g hLC]
  have hc₃ : rmP g x (A x) (B x) ((lcOf g) C x (r • v₁ + s • v₂)) (D x)
      = r * rmP g x (A x) (B x) ((lcOf g) C x v₁) (D x)
        + s * rmP g x (A x) (B x) ((lcOf g) C x v₂) (D x) := by
    rw [hconnC]
    simp only [rmP_add_thd g hLC, rmP_smul_thd g hLC]
  have hc₄ : rmP g x (A x) (B x) (C x) ((lcOf g) D x (r • v₁ + s • v₂))
      = r * rmP g x (A x) (B x) (C x) ((lcOf g) D x v₁)
        + s * rmP g x (A x) (B x) (C x) ((lcOf g) D x v₂) := by
    rw [hconnD]
    simp only [rmP_add_fth g hLC, rmP_smul_fth g hLC]
  simp only [dRmPhi]
  rw [hdir, hc₁, hc₂, hc₃, hc₄]
  ring

theorem covRm_linear_fst
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) :
    Work.Diff.GE.RL.CovRmLinFst g := by
  intro x r s v₁ v₂ a b c d
  have h1 := covRm_eq_dRmPhi (g := g) (x := x) (v := r • v₁ + s • v₂) (a := a) (b := b)
    (c := c) (d := d)
  have h2 := covRm_eq_dRmPhi (g := g) (x := x) (v := v₁) (a := a) (b := b) (c := c) (d := d)
  have h3 := covRm_eq_dRmPhi (g := g) (x := x) (v := v₂) (a := a) (b := b) (c := c) (d := d)
  have hlin := dRmPhi_linear_dir (I := I) (M := M) hLC g x
    (smoothExt x a) (smoothExt x b) (smoothExt x c) (smoothExt x d) r s v₁ v₂
  rw [h1, hlin, h2, h3]

end Work.Diff.GE.RL
