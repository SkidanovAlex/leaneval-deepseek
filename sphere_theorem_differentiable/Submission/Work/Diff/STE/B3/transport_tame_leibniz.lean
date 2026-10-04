/-
# The transport identity of the DeTurck operator: the Leibniz algebra

This module contains the second-order Leibniz rules for the partial derivatives `pdR` with
`ContDiffAt` (local) hypotheses — the local forms of `Work.Diff.STE.B3.transport_triple2` — and the
key consequence needed for the transport identity: the relation between the second derivatives of
the orthonormal-frame chart matrix `Mf` and of the coordinate-frame chart matrix `Gf` along the
frame-change identity `Mf = Σ_{ik} Ff a i · Gf i k · Ff b k`.

The point of the `ContDiffAt` form is that `Ff` and `Gf` are smooth only on the chart region, so the
global-smoothness hypotheses of `transport_triple2` do not apply; the local form does.
-/
import Mathlib
import Submission.Work.Diff.STE.B3.TransportDefs
import Submission.Work.Diff.STE.B3.transport_triple2

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open LeanEval.Geometry.SphereTheorem Submission.Diff
open scoped Manifold ContDiff Bundle Topology BigOperators Matrix
open Bundle ContDiff Set

namespace Work.Diff.STE.B3

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

/-! ## 1. The local Leibniz rules -/

/-- **Leibniz rule for the first partial derivative** (`ContDiffAt` form). -/
lemma pdR_mul_at {d : ℕ} {f g : (Fin d → ℝ) → ℝ} {z : Fin d → ℝ} (p : Fin d)
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    Work.Diff.STE.pdR p (fun y => f y * g y) z
      = f z * Work.Diff.STE.pdR p g z + g z * Work.Diff.STE.pdR p f z := by
  show fderiv ℝ (fun y => f y * g y) z (Pi.single p 1) = _
  rw [fderiv_fun_mul hf hg]
  simp [Work.Diff.STE.pdR, smul_eq_mul]

/-- **Second order Leibniz rule** (`ContDiffAt` form):

`∂_q∂_p (f · g)(z) = f z · ∂_q∂_p g z + ∂_p g z · ∂_q f z + ∂_q g z · ∂_p f z
  + g z · ∂_q∂_p f z`. -/
lemma pdR2_mul_at {d : ℕ} {f g : (Fin d → ℝ) → ℝ} {z : Fin d → ℝ} (q p : Fin d)
    (hf : ContDiffAt ℝ 2 f z) (hg : ContDiffAt ℝ 2 g z) :
    Work.Diff.STE.pdR q (Work.Diff.STE.pdR p (fun y => f y * g y)) z
      = f z * Work.Diff.STE.pdR q (Work.Diff.STE.pdR p g) z
        + Work.Diff.STE.pdR p g z * Work.Diff.STE.pdR q f z
        + Work.Diff.STE.pdR q g z * Work.Diff.STE.pdR p f z
        + g z * Work.Diff.STE.pdR q (Work.Diff.STE.pdR p f) z := by
  have hdf : DifferentiableAt ℝ f z := hf.differentiableAt (by norm_num)
  have hdg : DifferentiableAt ℝ g z := hg.differentiableAt (by norm_num)
  have hdfd : DifferentiableAt ℝ (fderiv ℝ f) z :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))
  have hdgd : DifferentiableAt ℝ (fderiv ℝ g) z :=
    ((hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))
  have hdfp : DifferentiableAt ℝ (Work.Diff.STE.pdR p f) z := by
    have h := (hdfd.hasFDerivAt.clm_apply (hasFDerivAt_const (Pi.single p (1 : ℝ)) z)).differentiableAt
    show DifferentiableAt ℝ (fun y => fderiv ℝ f y (Pi.single p (1 : ℝ))) z
    exact h
  have hdgp : DifferentiableAt ℝ (Work.Diff.STE.pdR p g) z := by
    have h := (hdgd.hasFDerivAt.clm_apply (hasFDerivAt_const (Pi.single p (1 : ℝ)) z)).differentiableAt
    show DifferentiableAt ℝ (fun y => fderiv ℝ g y (Pi.single p (1 : ℝ))) z
    exact h
  have hev : Work.Diff.STE.pdR p (fun y => f y * g y) =ᶠ[nhds z]
      (fun y => f y * Work.Diff.STE.pdR p g y + g y * Work.Diff.STE.pdR p f y) := by
    filter_upwards [hf.eventually (by norm_num), hg.eventually (by norm_num)] with y hyf hyg
    exact pdR_mul_at p (hyf.differentiableAt (by norm_num)) (hyg.differentiableAt (by norm_num))
  have hd1 : DifferentiableAt ℝ (fun y => f y * Work.Diff.STE.pdR p g y) z := hdf.mul hdgp
  have hd2 : DifferentiableAt ℝ (fun y => g y * Work.Diff.STE.pdR p f y) z := hdg.mul hdfp
  have hsum : fderiv ℝ (fun y => f y * Work.Diff.STE.pdR p g y
        + g y * Work.Diff.STE.pdR p f y) z
      = fderiv ℝ (fun y => f y * Work.Diff.STE.pdR p g y) z
        + fderiv ℝ (fun y => g y * Work.Diff.STE.pdR p f y) z := fderiv_add hd1 hd2
  calc Work.Diff.STE.pdR q (Work.Diff.STE.pdR p (fun y => f y * g y)) z
      = fderiv ℝ (Work.Diff.STE.pdR p (fun y => f y * g y)) z (Pi.single q 1) := rfl
    _ = fderiv ℝ (fun y => f y * Work.Diff.STE.pdR p g y + g y * Work.Diff.STE.pdR p f y) z
          (Pi.single q 1) := by rw [hev.fderiv_eq]
    _ = (fderiv ℝ (fun y => f y * Work.Diff.STE.pdR p g y) z
           + fderiv ℝ (fun y => g y * Work.Diff.STE.pdR p f y) z) (Pi.single q 1) := by
          rw [hsum]
    _ = f z * Work.Diff.STE.pdR q (Work.Diff.STE.pdR p g) z
        + Work.Diff.STE.pdR p g z * Work.Diff.STE.pdR q f z
        + Work.Diff.STE.pdR q g z * Work.Diff.STE.pdR p f z
        + g z * Work.Diff.STE.pdR q (Work.Diff.STE.pdR p f) z := by
          rw [fderiv_fun_mul hdf hdgp, fderiv_fun_mul hdg hdfp]
          simp only [Work.Diff.STE.pdR, add_apply, smul_apply, smul_eq_mul]
          ring

/-- **Second order Leibniz rule for a triple product** (`ContDiffAt` form): the nine-term
expansion of `∂_c∂_d (A · B · C)`. -/
lemma pdR2_triple_at {n : ℕ} {A B C : (Fin n → ℝ) → ℝ} {z : Fin n → ℝ} (c d : Fin n)
    (hA : ContDiffAt ℝ 2 A z) (hB : ContDiffAt ℝ 2 B z) (hC : ContDiffAt ℝ 2 C z) :
    Work.Diff.STE.pdR c (Work.Diff.STE.pdR d (fun y => A y * B y * C y)) z
      = Work.Diff.STE.pdR c (Work.Diff.STE.pdR d A) z * B z * C z
        + Work.Diff.STE.pdR c A z * Work.Diff.STE.pdR d B z * C z
        + Work.Diff.STE.pdR c A z * B z * Work.Diff.STE.pdR d C z
        + Work.Diff.STE.pdR d A z * Work.Diff.STE.pdR c B z * C z
        + Work.Diff.STE.pdR d A z * B z * Work.Diff.STE.pdR c C z
        + A z * Work.Diff.STE.pdR c (Work.Diff.STE.pdR d B) z * C z
        + A z * Work.Diff.STE.pdR c B z * Work.Diff.STE.pdR d C z
        + A z * Work.Diff.STE.pdR d B z * Work.Diff.STE.pdR c C z
        + A z * B z * Work.Diff.STE.pdR c (Work.Diff.STE.pdR d C) z := by
  have hAd : DifferentiableAt ℝ A z := hA.differentiableAt (by norm_num)
  have hBd : DifferentiableAt ℝ B z := hB.differentiableAt (by norm_num)
  have hAB2 : ContDiffAt ℝ 2 (fun y => A y * B y) z := hA.mul hB
  have hABd : Work.Diff.STE.pdR d (fun y => A y * B y) z
      = A z * Work.Diff.STE.pdR d B z + B z * Work.Diff.STE.pdR d A z :=
    pdR_mul_at d hAd hBd
  have hABc : Work.Diff.STE.pdR c (fun y => A y * B y) z
      = A z * Work.Diff.STE.pdR c B z + B z * Work.Diff.STE.pdR c A z :=
    pdR_mul_at c hAd hBd
  have h2 : Work.Diff.STE.pdR c (Work.Diff.STE.pdR d (fun y => A y * B y)) z
      = A z * Work.Diff.STE.pdR c (Work.Diff.STE.pdR d B) z
        + Work.Diff.STE.pdR d B z * Work.Diff.STE.pdR c A z
        + Work.Diff.STE.pdR c B z * Work.Diff.STE.pdR d A z
        + B z * Work.Diff.STE.pdR c (Work.Diff.STE.pdR d A) z :=
    pdR2_mul_at c d hA hB
  have hmain : Work.Diff.STE.pdR c (Work.Diff.STE.pdR d (fun y => A y * B y * C y)) z
      = (A z * B z) * Work.Diff.STE.pdR c (Work.Diff.STE.pdR d C) z
        + Work.Diff.STE.pdR d C z * Work.Diff.STE.pdR c (fun y => A y * B y) z
        + Work.Diff.STE.pdR c C z * Work.Diff.STE.pdR d (fun y => A y * B y) z
        + C z * Work.Diff.STE.pdR c (Work.Diff.STE.pdR d (fun y => A y * B y)) z :=
    pdR2_mul_at c d hAB2 hC
  rw [hmain, hABd, hABc, h2]
  ring

end Work.Diff.STE.B3

section SumRules

/-- **Linearity of `pdR` over a finite sum of functions** (`ContDiffAt` form). -/
lemma pdR_fun_sum_at {d : ℕ} {ι : Type*} [Fintype ι] {f : ι → (Fin d → ℝ) → ℝ}
    {z : Fin d → ℝ} (c : Fin d) (hf : ∀ i, DifferentiableAt ℝ (f i) z) :
    Work.Diff.STE.pdR c (fun w => ∑ i, f i w) z = ∑ i, Work.Diff.STE.pdR c (f i) z := by
  have hfun : (fun w : Fin d → ℝ => ∑ i, f i w) = (∑ i, f i) := by
    funext w; simp only [Finset.sum_apply]
  rw [Work.Diff.STE.pdR, hfun, fderiv_sum (fun i _ => hf i), _root_.sum_apply]
  exact Finset.sum_congr rfl fun i _ => rfl

/-- **Linearity of `pdR` over a finite sum of functions**, second order (`ContDiffAt` form). -/
lemma pdR2_fun_sum_at {d : ℕ} {ι : Type*} [Fintype ι] {f : ι → (Fin d → ℝ) → ℝ}
    {z : Fin d → ℝ} (c e : Fin d)
    (hf : ∀ i, ContDiffAt ℝ 2 (f i) z) :
    Work.Diff.STE.pdR c (Work.Diff.STE.pdR e (fun w => ∑ i, f i w)) z
      = ∑ i, Work.Diff.STE.pdR c (Work.Diff.STE.pdR e (f i)) z := by
  have h1 : ∀ i, DifferentiableAt ℝ (f i) z := fun i => (hf i).differentiableAt (by norm_num)
  have hfun : (fun w : Fin d → ℝ => ∑ i, f i w) = (∑ i, f i) := by
    funext w; simp only [Finset.sum_apply]
  -- the eventual equality of the first derivatives
  have hev : (fun w => Work.Diff.STE.pdR e (fun w' => ∑ i, f i w') w)
      =ᶠ[nhds z] (fun w => ∑ i, Work.Diff.STE.pdR e (f i) w) := by
    filter_upwards [Filter.eventually_all.2 (fun i => (hf i).eventually (by norm_num))] with w hw
    rw [Work.Diff.STE.pdR, hfun]
    rw [fderiv_sum (fun i _ => (hw i).differentiableAt (by norm_num)), _root_.sum_apply]
    exact Finset.sum_congr rfl fun i _ => rfl
  have h2 : Work.Diff.STE.pdR c (Work.Diff.STE.pdR e (fun w => ∑ i, f i w)) z
      = Work.Diff.STE.pdR c (fun w => ∑ i, Work.Diff.STE.pdR e (f i) w) z := by
    have hh := congrArg (fun (L : (Fin d → ℝ) →L[ℝ] ℝ) => L (Pi.single c 1)) hev.fderiv_eq
    exact hh
  rw [h2, pdR_fun_sum_at c (fun i => by
    have hdi : DifferentiableAt ℝ (fderiv ℝ (f i)) z :=
      (((hf i).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))
    exact (hdi.hasFDerivAt.clm_apply (hasFDerivAt_const
      (Pi.single e (1 : ℝ)) z)).differentiableAt)]

end SumRules
