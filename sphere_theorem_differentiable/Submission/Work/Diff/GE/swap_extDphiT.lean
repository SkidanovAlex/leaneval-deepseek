import Mathlib
import Submission.Work.Diff.GE.swap_defs
import Submission.Work.Diff.GE.swap_curvsection
import Submission.Work.Diff.GE.kato_covRm_field
import Submission.Work.Diff.GE.contMDiff_rmP_fields

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The covariant derivative of the curvature contraction `Φ = R(·,·)·Rm`

`Work.Diff.GE.extD_phiT_fields` computes `extD (phiT g)` on the six fields `(Xs,Ys,Ps,As,Bs,Cs,Ds)`:
it is the sum of the two brackets appearing in `Work.Diff.GE.cov3Rm_swap`, namely the four
`curvDeriv = ∇R` terms (`B₁`) and the four `covRm = ∇Rm` terms (`B₂`).

The proof is the Leibniz rule for the contraction: `phiT g F = T₀ + T₁ + T₂ + T₃` with
`T_j = rmP (R(Y,P)(slot j)) (other slots)`, each `mvfderiv T_j` is computed by
`Work.Diff.GE.kato_covRm_field` (giving `B₂` plus the four slot-corrections), the derivative of the
curvature section `A_j = R(Y,P)(slot j)` is `Work.Diff.GE.covAlong_curv_fields` (giving `B₁` plus the
three terms that cancel against the other corrections), and the six corrections
`∑ i, phiT g (upd (lcOf g) Xs F i) x` cancel against everything else.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.GE

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

/-- `mvfderiv` of a sum of four scalar functions. -/
theorem mvfderiv_add4 {f₁ f₂ f₃ f₄ : M → ℝ} {x : M} {v : TangentSpace I x}
    (h₁ : MDiffAt f₁ x) (h₂ : MDiffAt f₂ x) (h₃ : MDiffAt f₃ x) (h₄ : MDiffAt f₄ x) :
    mvfderiv I (f₁ + f₂ + f₃ + f₄) x v
      = mvfderiv I f₁ x v + mvfderiv I f₂ x v + mvfderiv I f₃ x v + mvfderiv I f₄ x v := by
  have h₁₂ : MDiffAt (f₁ + f₂) x := h₁.add h₂
  have h₁₂₃ : MDiffAt (f₁ + f₂ + f₃) x := h₁₂.add h₃
  rw [show (f₁ + f₂ + f₃ + f₄ : M → ℝ) = (f₁ + f₂ + f₃) + f₄ from rfl,
    mvfderiv_add h₁₂₃ h₄,
    show (f₁ + f₂ + f₃ : M → ℝ) = (f₁ + f₂) + f₃ from rfl, mvfderiv_add h₁₂ h₃,
    mvfderiv_add h₁ h₂]
  simp only [ContinuousLinearMap.add_apply]

/-- **The Leibniz rule for the curvature contraction `Φ`.** -/
theorem extD_phiT_fields (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    {Xs Ys Ps As Bs Cs Ds : Π y : M, TangentSpace I y}
    (hXs : CMDiff ∞ (T% Xs)) (hYs : CMDiff ∞ (T% Ys)) (hPs : CMDiff ∞ (T% Ps))
    (hAs : CMDiff ∞ (T% As)) (hBs : CMDiff ∞ (T% Bs)) (hCs : CMDiff ∞ (T% Cs))
    (hDs : CMDiff ∞ (T% Ds)) :
    extD (lcOf g) (phiT g) x Xs (hexad Ys Ps As Bs Cs Ds)
      = (rmP g x (curvDeriv g x (Xs x) (Ys x) (Ps x) (As x)) (Bs x) (Cs x) (Ds x)
          + rmP g x (As x) (curvDeriv g x (Xs x) (Ys x) (Ps x) (Bs x)) (Cs x) (Ds x)
          + rmP g x (As x) (Bs x) (curvDeriv g x (Xs x) (Ys x) (Ps x) (Cs x)) (Ds x)
          + rmP g x (As x) (Bs x) (Cs x) (curvDeriv g x (Xs x) (Ys x) (Ps x) (Ds x)))
        + (covRm g x (Xs x) (rmVec (lcOf g) x (Ys x) (Ps x) (As x)) (Bs x) (Cs x) (Ds x)
          + covRm g x (Xs x) (As x) (rmVec (lcOf g) x (Ys x) (Ps x) (Bs x)) (Cs x) (Ds x)
          + covRm g x (Xs x) (As x) (Bs x) (rmVec (lcOf g) x (Ys x) (Ps x) (Cs x)) (Ds x)
          + covRm g x (Xs x) (As x) (Bs x) (Cs x) (rmVec (lcOf g) x (Ys x) (Ps x) (Ds x))) := by
  have hcov : CovSmooth (lcOf g) := (hLC g).1.some
  -- the four curvature sections `A_j = R(Y,P)(slot j)`
  set A0 : Π y : M, TangentSpace I y := fun y => curv (lcOf g) Ys Ps As y with hA0
  set A1 : Π y : M, TangentSpace I y := fun y => curv (lcOf g) Ys Ps Bs y with hA1
  set A2 : Π y : M, TangentSpace I y := fun y => curv (lcOf g) Ys Ps Cs y with hA2
  set A3 : Π y : M, TangentSpace I y := fun y => curv (lcOf g) Ys Ps Ds y with hA3
  have hA0s : CMDiff ∞ (T% A0) := by
    rw [hA0]; exact contMDiff_curv_fields (lcOf g) hcov hYs hPs hAs
  have hA1s : CMDiff ∞ (T% A1) := by
    rw [hA1]; exact contMDiff_curv_fields (lcOf g) hcov hYs hPs hBs
  have hA2s : CMDiff ∞ (T% A2) := by
    rw [hA2]; exact contMDiff_curv_fields (lcOf g) hcov hYs hPs hCs
  have hA3s : CMDiff ∞ (T% A3) := by
    rw [hA3]; exact contMDiff_curv_fields (lcOf g) hcov hYs hPs hDs
  -- the four summands of `phiT`
  set T0 : M → ℝ := fun y => rmP g y (A0 y) (Bs y) (Cs y) (Ds y) with hT0
  set T1 : M → ℝ := fun y => rmP g y (As y) (A1 y) (Cs y) (Ds y) with hT1
  set T2 : M → ℝ := fun y => rmP g y (As y) (Bs y) (A2 y) (Ds y) with hT2
  set T3 : M → ℝ := fun y => rmP g y (As y) (Bs y) (Cs y) (A3 y) with hT3
  have hT0s : MDiffAt T0 x := by
    rw [hT0]
    exact (rmP_fields_smooth (I := I) (M := M) hLC g hA0s hBs hCs hDs).contMDiffAt.mdifferentiableAt
      (by simp)
  have hT1s : MDiffAt T1 x := by
    rw [hT1]
    exact (rmP_fields_smooth (I := I) (M := M) hLC g hAs hA1s hCs hDs).contMDiffAt.mdifferentiableAt
      (by simp)
  have hT2s : MDiffAt T2 x := by
    rw [hT2]
    exact (rmP_fields_smooth (I := I) (M := M) hLC g hAs hBs hA2s hDs).contMDiffAt.mdifferentiableAt
      (by simp)
  have hT3s : MDiffAt T3 x := by
    rw [hT3]
    exact (rmP_fields_smooth (I := I) (M := M) hLC g hAs hBs hCs hA3s).contMDiffAt.mdifferentiableAt
      (by simp)
  -- `phiT` is the sum of the four summands
  have hphi : phiT g (hexad Ys Ps As Bs Cs Ds) = T0 + T1 + T2 + T3 := by
    funext y
    simp only [phiT, hexad_zero, hexad_one, hexad_two, hexad_three, hexad_four, hexad_five,
      hA0, hA1, hA2, hA3, hT0, hT1, hT2, hT3, Pi.add_apply]
  -- the `Ext`-Leibniz expansion of each summand
  have hT0x : mvfderiv I T0 x (Xs x)
      = covRm g x (Xs x) (A0 x) (Bs x) (Cs x) (Ds x)
        + rmP g x ((lcOf g) A0 x (Xs x)) (Bs x) (Cs x) (Ds x)
        + rmP g x (A0 x) ((lcOf g) Bs x (Xs x)) (Cs x) (Ds x)
        + rmP g x (A0 x) (Bs x) ((lcOf g) Cs x (Xs x)) (Ds x)
        + rmP g x (A0 x) (Bs x) (Cs x) ((lcOf g) Ds x (Xs x)) := by
    rw [hT0]
    linarith [(kato_covRm_field (I := I) (M := M) hLC g x Xs A0 Bs Cs Ds hXs hA0s hBs hCs hDs).1]
  have hT1x : mvfderiv I T1 x (Xs x)
      = covRm g x (Xs x) (As x) (A1 x) (Cs x) (Ds x)
        + rmP g x ((lcOf g) As x (Xs x)) (A1 x) (Cs x) (Ds x)
        + rmP g x (As x) ((lcOf g) A1 x (Xs x)) (Cs x) (Ds x)
        + rmP g x (As x) (A1 x) ((lcOf g) Cs x (Xs x)) (Ds x)
        + rmP g x (As x) (A1 x) (Cs x) ((lcOf g) Ds x (Xs x)) := by
    rw [hT1]
    linarith [(kato_covRm_field (I := I) (M := M) hLC g x Xs As A1 Cs Ds hXs hAs hA1s hCs hDs).1]
  have hT2x : mvfderiv I T2 x (Xs x)
      = covRm g x (Xs x) (As x) (Bs x) (A2 x) (Ds x)
        + rmP g x ((lcOf g) As x (Xs x)) (Bs x) (A2 x) (Ds x)
        + rmP g x (As x) ((lcOf g) Bs x (Xs x)) (A2 x) (Ds x)
        + rmP g x (As x) (Bs x) ((lcOf g) A2 x (Xs x)) (Ds x)
        + rmP g x (As x) (Bs x) (A2 x) ((lcOf g) Ds x (Xs x)) := by
    rw [hT2]
    linarith [(kato_covRm_field (I := I) (M := M) hLC g x Xs As Bs A2 Ds hXs hAs hBs hA2s hDs).1]
  have hT3x : mvfderiv I T3 x (Xs x)
      = covRm g x (Xs x) (As x) (Bs x) (Cs x) (A3 x)
        + rmP g x ((lcOf g) As x (Xs x)) (Bs x) (Cs x) (A3 x)
        + rmP g x (As x) ((lcOf g) Bs x (Xs x)) (Cs x) (A3 x)
        + rmP g x (As x) (Bs x) ((lcOf g) Cs x (Xs x)) (A3 x)
        + rmP g x (As x) (Bs x) (Cs x) ((lcOf g) A3 x (Xs x)) := by
    rw [hT3]
    linarith [(kato_covRm_field (I := I) (M := M) hLC g x Xs As Bs Cs A3 hXs hAs hBs hCs hA3s).1]
  -- the covariant derivative of each curvature section
  have hA0d : (lcOf g) A0 x (Xs x)
      = curvDeriv g x (Xs x) (Ys x) (Ps x) (As x)
        + curv (lcOf g) (fun y : M => (lcOf g) Ys y (Xs y)) Ps As x
        + curv (lcOf g) Ys (fun y : M => (lcOf g) Ps y (Xs y)) As x
        + curv (lcOf g) Ys Ps (fun y : M => (lcOf g) As y (Xs y)) x := by
    rw [hA0]
    exact covAlong_curv_fields (I := I) (M := M) hLC g x hXs hYs hPs hAs
  have hA1d : (lcOf g) A1 x (Xs x)
      = curvDeriv g x (Xs x) (Ys x) (Ps x) (Bs x)
        + curv (lcOf g) (fun y : M => (lcOf g) Ys y (Xs y)) Ps Bs x
        + curv (lcOf g) Ys (fun y : M => (lcOf g) Ps y (Xs y)) Bs x
        + curv (lcOf g) Ys Ps (fun y : M => (lcOf g) Bs y (Xs y)) x := by
    rw [hA1]
    exact covAlong_curv_fields (I := I) (M := M) hLC g x hXs hYs hPs hBs
  have hA2d : (lcOf g) A2 x (Xs x)
      = curvDeriv g x (Xs x) (Ys x) (Ps x) (Cs x)
        + curv (lcOf g) (fun y : M => (lcOf g) Ys y (Xs y)) Ps Cs x
        + curv (lcOf g) Ys (fun y : M => (lcOf g) Ps y (Xs y)) Cs x
        + curv (lcOf g) Ys Ps (fun y : M => (lcOf g) Cs y (Xs y)) x := by
    rw [hA2]
    exact covAlong_curv_fields (I := I) (M := M) hLC g x hXs hYs hPs hCs
  have hA3d : (lcOf g) A3 x (Xs x)
      = curvDeriv g x (Xs x) (Ys x) (Ps x) (Ds x)
        + curv (lcOf g) (fun y : M => (lcOf g) Ys y (Xs y)) Ps Ds x
        + curv (lcOf g) Ys (fun y : M => (lcOf g) Ps y (Xs y)) Ds x
        + curv (lcOf g) Ys Ps (fun y : M => (lcOf g) Ds y (Xs y)) x := by
    rw [hA3]
    exact covAlong_curv_fields (I := I) (M := M) hLC g x hXs hYs hPs hDs
  -- the values of the curvature sections are `rmVec`
  have hA0x : A0 x = rmVec (lcOf g) x (Ys x) (Ps x) (As x) := by
    rw [hA0]; exact curv_section_apply_eq_rmVec (I := I) (M := M) hLC g hYs hPs hAs x
  have hA1x : A1 x = rmVec (lcOf g) x (Ys x) (Ps x) (Bs x) := by
    rw [hA1]; exact curv_section_apply_eq_rmVec (I := I) (M := M) hLC g hYs hPs hBs x
  have hA2x : A2 x = rmVec (lcOf g) x (Ys x) (Ps x) (Cs x) := by
    rw [hA2]; exact curv_section_apply_eq_rmVec (I := I) (M := M) hLC g hYs hPs hCs x
  have hA3x : A3 x = rmVec (lcOf g) x (Ys x) (Ps x) (Ds x) := by
    rw [hA3]; exact curv_section_apply_eq_rmVec (I := I) (M := M) hLC g hYs hPs hDs x
  rw [extD_eq, hphi, mvfderiv_add4 hT0s hT1s hT2s hT3s,
    hT0x, hT1x, hT2x, hT3x, hA0d, hA1d, hA2d, hA3d]
  -- put the right-hand side's `rmVec` into the same `curv`-section normal form
  rw [← curv_section_apply_eq_rmVec (I := I) (M := M) hLC g hYs hPs hAs x,
    ← curv_section_apply_eq_rmVec (I := I) (M := M) hLC g hYs hPs hBs x,
    ← curv_section_apply_eq_rmVec (I := I) (M := M) hLC g hYs hPs hCs x,
    ← curv_section_apply_eq_rmVec (I := I) (M := M) hLC g hYs hPs hDs x]
  simp only [rmP_add_fst (I := I) (M := M) g hLC x, rmP_add_snd (I := I) (M := M) g hLC x,
    rmP_add_thd (I := I) (M := M) g hLC x, rmP_add_fth (I := I) (M := M) g hLC x]
  rw [Fin.sum_univ_six]
  simp (config := { decide := true }) only [phiT, hexad_zero, hexad_one, hexad_two, hexad_three,
    hexad_four, hexad_five, upd, covAlong, Function.update_apply, Fin.isValue, reduceIte,
    hA0, hA1, hA2, hA3]
  rw [show (fun y : M => (lcOf g) Ys y (Xs y)) = covAlong (lcOf g) Xs Ys from rfl,
    show (fun y : M => (lcOf g) Ps y (Xs y)) = covAlong (lcOf g) Xs Ps from rfl,
    show (fun y : M => (lcOf g) As y (Xs y)) = covAlong (lcOf g) Xs As from rfl,
    show (fun y : M => (lcOf g) Bs y (Xs y)) = covAlong (lcOf g) Xs Bs from rfl,
    show (fun y : M => (lcOf g) Cs y (Xs y)) = covAlong (lcOf g) Xs Cs from rfl,
    show (fun y : M => (lcOf g) Ds y (Xs y)) = covAlong (lcOf g) Xs Ds from rfl]
  ring

end Work.Diff.GE
