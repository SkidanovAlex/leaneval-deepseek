/-
# The chain rule for `exp` at a zero of a `𝔸`-valued function

`Work.Diff.Evol.exp_chain_rule`: if `B : M → 𝔸` is `C^∞` with `B x = 0`, then

* `d (exp ∘ B)_x = dB_x` (the first derivative, from `d exp_0 = id`), and
* for every `C^∞` field `W`, the second derivative of `exp ∘ B` along `W` equals the second
  derivative of `B` along `W` plus the square `(dB_x (W x)) * (dB_x (W x))`.

The second statement is proved without any chart computation on the manifold: writing
`F = exp ∘ B` and `h = F - B`, the chain rule gives, pointwise,
`d h_y (W y) = Ψ (B y) (d B_y (W y))` where `Ψ X = d exp_X - id`, and `Ψ ∘ B` is a smooth
`(𝔸 →L[ℝ] 𝔸)`-valued function whose product with `d B (W)` is differentiated by the product rule
`Work.Diff.Evol.mvfderiv_clm_apply`.  Since `B x = 0` we have `Ψ (B x) = Ψ 0 = 0`, so the term
involving the derivative of `d B (W)` drops out, and the second derivative of `Ψ ∘ B` is the
diagonal second derivative of `exp` at `0`, which is the multiplication
(`Work.Diff.Evol.exp_second_deriv_zero`).
-/

import Mathlib
import Submission.Work.Diff.Evol.Vocab
import Submission.Work.Diff.Evol.exp_second_deriv_zero
import Submission.Work.Diff.Evol.mvfderiv_clm_apply
import Submission.Commons.Geometry.Manifold.VectorField.mvfderiv_apply_contMDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedSectionVars false

namespace Work.Diff.Evol

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set Filter VectorField Commons.Geometry.Manifold.VectorField

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I (((⊤ : ℕ∞) : WithTop ℕ∞)) M] [I.Boundaryless] [T2Space M]
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-! ### Auxiliary facts about `exp` on a real Banach algebra -/

theorem exp_diffAt (y : 𝔸) : DifferentiableAt ℝ (NormedSpace.exp : 𝔸 → 𝔸) y :=
  ((NormedSpace.exp_analytic y).contDiffAt (n := (1 : ℕ∞ω))).differentiableAt (by norm_num)

theorem exp_contDiff : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) (NormedSpace.exp : 𝔸 → 𝔸) :=
  contDiff_iff_contDiffAt.mpr fun z => (NormedSpace.exp_analytic z).contDiffAt

theorem mfderiv_apply_eq_mvfderiv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : M → F) (x : M) (v : TangentSpace I x) :
    (mfderiv% f x) v = mvfderiv I f x v := by
  simp only [mvfderiv, ContinuousLinearMap.comp_apply]
  rfl

/-! ### The chain rule for `exp ∘ B` and the difference `exp ∘ B - B` -/

theorem mvfderiv_exp_comp_apply (B : M → 𝔸) (hB : SmoothMap I M B) (y : M)
    (v : TangentSpace I y) :
    mvfderiv I (fun z : M => NormedSpace.exp (B z)) y v
      = (fderiv ℝ (NormedSpace.exp : 𝔸 → 𝔸) (B y)) (mvfderiv I B y v) := by
  have hBmd : MDifferentiableAt I 𝓘(ℝ, 𝔸) B y := hB.contMDiffAt.mdifferentiableAt (by simp)
  have hexpd : DifferentiableAt ℝ (NormedSpace.exp : 𝔸 → 𝔸) (B y) := exp_diffAt (B y)
  have hexp : MDifferentiableAt 𝓘(ℝ, 𝔸) 𝓘(ℝ, 𝔸) (NormedSpace.exp : 𝔸 → 𝔸) (B y) :=
    hexpd.mdifferentiableAt
  rw [show (fun z : M => NormedSpace.exp (B z)) = (NormedSpace.exp ∘ B) from rfl,
    mvfderiv_comp_apply (I := 𝓘(ℝ, 𝔸)) (I' := I) (M := 𝔸) (M' := M)
      (f := B) (g := NormedSpace.exp) y hexp hBmd v,
    mvfderiv_eq_fderiv]
  rfl

theorem mvfderiv_exp_sub_apply (B : M → 𝔸) (hB : SmoothMap I M B) (y : M)
    (v : TangentSpace I y) :
    mvfderiv I (fun z : M => NormedSpace.exp (B z) - B z) y v
      = (fderiv ℝ (NormedSpace.exp : 𝔸 → 𝔸) (B y) - ContinuousLinearMap.id ℝ 𝔸)
          (mvfderiv I B y v) := by
  have hBmd : MDifferentiableAt I 𝓘(ℝ, 𝔸) B y := hB.contMDiffAt.mdifferentiableAt (by simp)
  have hexpd : DifferentiableAt ℝ (NormedSpace.exp : 𝔸 → 𝔸) (B y) := exp_diffAt (B y)
  have hdiff : MDifferentiableAt I 𝓘(ℝ, 𝔸) (fun z : M => NormedSpace.exp (B z)) y :=
    hexpd.comp_mdifferentiableAt hBmd
  rw [show (fun z : M => NormedSpace.exp (B z) - B z)
        = ((fun z : M => NormedSpace.exp (B z)) - B) from rfl,
    mvfderiv_sub (I := I) hdiff hBmd, sub_apply, mvfderiv_exp_comp_apply B hB y v,
    sub_apply, ContinuousLinearMap.id_apply]

/-! ### The second derivative along a field of `exp ∘ B - B` -/

theorem mvfderiv_second_exp_sub (B : M → 𝔸) (hB : SmoothMap I M B) (x : M) (hBx : B x = 0)
    (W : Π y : M, TangentSpace I y) (hW : SmoothField I M W) :
    mvfderiv I (fun y : M => mvfderiv I (fun z : M => NormedSpace.exp (B z) - B z) y (W y))
        x (W x)
      = (mvfderiv I B x (W x)) * (mvfderiv I B x (W x)) := by
  set Ψ : 𝔸 → (𝔸 →L[ℝ] 𝔸) :=
    fun X => fderiv ℝ (NormedSpace.exp : 𝔸 → 𝔸) X - ContinuousLinearMap.id ℝ 𝔸 with hΨ
  set Q : M → 𝔸 := fun y => mvfderiv I B y (W y) with hQ
  have hQsm : ContMDiff I 𝓘(ℝ, 𝔸) ∞ Q := mvfderiv_apply_contMDiff hB hW
  have hQmd : MDifferentiableAt I 𝓘(ℝ, 𝔸) Q x := hQsm.contMDiffAt.mdifferentiableAt (by simp)
  have hpt : (fun y : M => mvfderiv I (fun z : M => NormedSpace.exp (B z) - B z) y (W y))
      = (fun y : M => Ψ (B y) (Q y)) := by
    funext y
    rw [mvfderiv_exp_sub_apply B hB y (W y)]
  rw [hpt]
  have hBmd : MDifferentiableAt I 𝓘(ℝ, 𝔸) B x := hB.contMDiffAt.mdifferentiableAt (by simp)
  have hexp2 : ContDiffAt ℝ (2 : ℕ∞ω) (NormedSpace.exp : 𝔸 → 𝔸) (B x) :=
    (NormedSpace.exp_analytic (B x)).contDiffAt
  have hfd : ContDiffAt ℝ (1 : ℕ∞ω)
      (fun X : 𝔸 => fderiv ℝ (NormedSpace.exp : 𝔸 → 𝔸) X) (B x) :=
    hexp2.fderiv_right (m := 1) (n := 2) (by norm_num)
  have hcst : ContDiffAt ℝ (1 : ℕ∞ω)
      (fun _ : 𝔸 => ContinuousLinearMap.id ℝ 𝔸) (B x) := contDiffAt_const
  have hΨc : ContDiffAt ℝ (1 : ℕ∞ω) Ψ (B x) := by
    rw [hΨ]; exact hfd.sub hcst
  have hΨd : DifferentiableAt ℝ Ψ (B x) := hΨc.differentiableAt (by norm_num)
  have hAmd : MDifferentiableAt I 𝓘(ℝ, (𝔸 →L[ℝ] 𝔸)) (fun y : M => Ψ (B y)) x :=
    hΨd.comp_mdifferentiableAt hBmd
  rw [mvfderiv_clm_apply (I := I) (F₁ := 𝔸) (F₂ := 𝔸)
    (A := fun y : M => Ψ (B y)) (V := Q) hAmd hQmd (W x)]
  have hΨ0 : Ψ 0 = 0 := by
    have h0 : fderiv ℝ (NormedSpace.exp : 𝔸 → 𝔸) 0 = ContinuousLinearMap.id ℝ 𝔸 :=
      (hasFDerivAt_exp_zero (𝕂 := ℝ)).fderiv
    rw [hΨ]
    simp only [h0, sub_self]
  have hAx : Ψ (B x) = 0 := by rw [hBx, hΨ0]
  rw [hAx, zero_apply, add_zero]
  have hchain : (mvfderiv I (fun y : M => Ψ (B y)) x) (W x)
      = (fderiv ℝ (fderiv ℝ (NormedSpace.exp : 𝔸 → 𝔸)) 0) (Q x) := by
    have hΨmd : MDifferentiableAt 𝓘(ℝ, 𝔸) 𝓘(ℝ, (𝔸 →L[ℝ] 𝔸)) Ψ (B x) := hΨd.mdifferentiableAt
    have h1 : (mvfderiv I (fun y : M => Ψ (B y)) x) (W x)
        = (mvfderiv 𝓘(ℝ, 𝔸) Ψ (B x)) (mvfderiv I B x (W x)) := by
      rw [show (fun y : M => Ψ (B y)) = (Ψ ∘ B) from rfl,
        mvfderiv_comp_apply (I := 𝓘(ℝ, 𝔸)) (I' := I) (M := 𝔸) (M' := M) (f := B) (g := Ψ)
          x hΨmd hBmd (W x)]
      rw [mfderiv_apply_eq_mvfderiv B x (W x)]
    rw [h1, mvfderiv_eq_fderiv, hBx]
    have hΨderiv : fderiv ℝ Ψ 0 = fderiv ℝ (fderiv ℝ (NormedSpace.exp : 𝔸 → 𝔸)) 0 := by
      have hc1 : ContDiffAt ℝ (1 : ℕ∞ω)
          (fun X : 𝔸 => fderiv ℝ (NormedSpace.exp : 𝔸 → 𝔸) X) 0 :=
        ((NormedSpace.exp_analytic 0).contDiffAt (n := (2 : ℕ∞ω))).fderiv_right
          (m := 1) (n := 2) (by norm_num)
      have hd1 : DifferentiableAt ℝ (fun X : 𝔸 => fderiv ℝ (NormedSpace.exp : 𝔸 → 𝔸) X) 0 :=
        hc1.differentiableAt (by norm_num)
      rw [hΨ]
      rw [show (fun X : 𝔸 => fderiv ℝ NormedSpace.exp X - ContinuousLinearMap.id ℝ 𝔸)
          = ((fun X : 𝔸 => fderiv ℝ NormedSpace.exp X)
              - fun _ : 𝔸 => ContinuousLinearMap.id ℝ 𝔸) from rfl]
      rw [fderiv_sub hd1 (differentiableAt_const _), fderiv_const_apply, sub_zero]
    rw [hΨderiv]
    rfl
  rw [hchain]
  simpa using Work.Diff.Evol.exp_second_deriv_zero (Q x)

/-! ### The main theorem -/

theorem exp_chain_rule
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I (((⊤ : ℕ∞) : WithTop ℕ∞)) M] [I.Boundaryless] [T2Space M]
    {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
    (B : M → 𝔸) (hB : Work.Diff.Evol.SmoothMap I M B) (x : M) (hBx : B x = 0) :
    (∀ v : TangentSpace I x,
        mvfderiv I (fun y : M => NormedSpace.exp (B y)) x v = mvfderiv I B x v) ∧
      (∀ (W : Π y : M, TangentSpace I y), Work.Diff.Evol.SmoothField I M W →
        mvfderiv I (fun y : M => mvfderiv I (fun z : M => NormedSpace.exp (B z)) y (W y)) x (W x)
          = mvfderiv I (fun y : M => mvfderiv I B y (W y)) x (W x)
            + (mvfderiv I B x (W x)) * (mvfderiv I B x (W x))) := by
  have hexp0 : fderiv ℝ (NormedSpace.exp : 𝔸 → 𝔸) 0 = ContinuousLinearMap.id ℝ 𝔸 :=
    (hasFDerivAt_exp_zero (𝕂 := ℝ)).fderiv
  constructor
  · intro v
    rw [mvfderiv_exp_comp_apply B hB x v, hBx, hexp0, ContinuousLinearMap.id_apply]
  · intro W hW
    have hexpS : ContMDiff I 𝓘(ℝ, 𝔸) ∞ (fun z : M => NormedSpace.exp (B z)) :=
      exp_contDiff.comp_contMDiff hB
    have hsubC : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞))
        (fun X : 𝔸 => NormedSpace.exp X - X) := exp_contDiff.sub contDiff_id
    have hsubS : ContMDiff I 𝓘(ℝ, 𝔸) ∞ (fun z : M => NormedSpace.exp (B z) - B z) :=
      hsubC.comp_contMDiff hB
    have hPs : ContMDiff I 𝓘(ℝ, 𝔸) ∞
        (fun y : M => mvfderiv I (fun z : M => NormedSpace.exp (B z) - B z) y (W y)) :=
      mvfderiv_apply_contMDiff hsubS hW
    have hQs : ContMDiff I 𝓘(ℝ, 𝔸) ∞ (fun y : M => mvfderiv I B y (W y)) :=
      mvfderiv_apply_contMDiff hB hW
    have hPmd : MDifferentiableAt I 𝓘(ℝ, 𝔸)
        (fun y : M => mvfderiv I (fun z : M => NormedSpace.exp (B z) - B z) y (W y)) x :=
      hPs.contMDiffAt.mdifferentiableAt (by simp)
    have hQmd : MDifferentiableAt I 𝓘(ℝ, 𝔸) (fun y : M => mvfderiv I B y (W y)) x :=
      hQs.contMDiffAt.mdifferentiableAt (by simp)
    have hsplit : (fun y : M => mvfderiv I (fun z : M => NormedSpace.exp (B z)) y (W y))
        = (fun y : M => mvfderiv I (fun z : M => NormedSpace.exp (B z) - B z) y (W y)
            + mvfderiv I B y (W y)) := by
      funext y
      rw [mvfderiv_exp_sub_apply B hB y (W y), mvfderiv_exp_comp_apply B hB y (W y),
        sub_apply, ContinuousLinearMap.id_apply, sub_add_cancel]
    rw [hsplit,
      show (fun y : M => mvfderiv I (fun z : M => NormedSpace.exp (B z) - B z) y (W y)
            + mvfderiv I B y (W y))
          = ((fun y : M => mvfderiv I (fun z : M => NormedSpace.exp (B z) - B z) y (W y))
              + fun y : M => mvfderiv I B y (W y)) from rfl,
      mvfderiv_add hPmd hQmd, add_apply,
      mvfderiv_second_exp_sub B hB x hBx W hW, add_comm]

end Work.Diff.Evol
