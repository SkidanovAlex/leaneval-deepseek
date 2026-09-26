import Mathlib
import Submission.Work.Drive.Final.AnyEventDefs

/-!
# The dent moves the sweep height by at most `a' ‖ℓ‖ (κ/r) ‖d(par)‖`

This file proves the quantitative `C¹` bound recorded in `Final/NOTES_LEAD_L4b.md` §1 (the estimate
that `dent_annulus_regular` consumes):

  `‖d(ℓ ∘ D.deform ∘ par) − d(sweepHeight)‖ ≤ a' ‖ℓ‖ (κ/r) ‖d(par)‖`

The mathematics is two lines: the dent is the identity plus the bump
`z ↦ z + a' χ(‖z − centre‖/r) • d`, so by `ℓ`-linearity

  `ℓ (D.deform z) = ℓ z + (a' χ(‖z − centre‖/r)) (ℓ d)`,

i.e. the deformed sweep height is the undeformed one plus the bump
`q' ↦ (a' ℓ d) χ(‖par q' − centre‖/r)`; and the derivative of a bump of the radius divided by `r` is
bounded by `κ/r`.  The only point at which the composite is not visibly differentiable is
`par q = centre`, where the hypothesis `χ = 1` on `|t| ≤ 1/2` makes the bump *locally constant* (so
the derivative vanishes and the bound is trivial).  Since `‖ℓ d‖ ≤ ‖ℓ‖` (as `d` is a unit vector),
`|a' ℓ d| ≤ a' ‖ℓ‖`, which gives the constant of the statement.

## Contents

* `lipschitzWith_norm_sub_div` — `z ↦ ‖z − c‖/r` is Lipschitz with constant `r⁻¹`;
* `norm_fderiv_chi_norm_div_comp_le` — differentiability of `q' ↦ χ(‖f q' − c‖/r)` at `q`
  together with the derivative bound `‖fderiv‖ ≤ κ r⁻¹ ‖fderiv f q‖`;
* `anyDentDatum_deform_wall` — the algebraic identity `ℓ ∘ D.deform = ℓ + bump`;
* `fderiv_sweepHeight_dent_sub_le` — the statement of the file.
-/

open LeanEval.KnotTheory.PardonDistortion Set

namespace Work.Drive.Final

noncomputable section

open Filter

/-! ## The two analytic bricks -/

/-- The function `z ↦ ‖z - c‖ / r` (a rescaled distance to the centre of the dent) is Lipschitz with
constant `r⁻¹`. -/
theorem lipschitzWith_norm_sub_div {E : Type*} [NormedAddCommGroup E] {c : E} {r : ℝ}
    (hr : 0 < r) :
    LipschitzWith ⟨r⁻¹, inv_nonneg.mpr hr.le⟩ (fun z : E => ‖z - c‖ / r) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  change dist (‖x - c‖ / r) (‖y - c‖ / r) ≤ r⁻¹ * dist x y
  have h1 : |‖x - c‖ - ‖y - c‖| ≤ ‖x - y‖ := by
    have h := abs_norm_sub_norm_le (x - c) (y - c)
    have he : (x - c) - (y - c) = x - y := by abel
    rwa [he] at h
  rw [Real.dist_eq, div_sub_div_same, abs_div, abs_of_pos hr, dist_eq_norm, div_eq_inv_mul]
  calc r⁻¹ * |‖x - c‖ - ‖y - c‖| = |‖x - c‖ - ‖y - c‖| * r⁻¹ := by ring
    _ ≤ ‖x - y‖ * r⁻¹ := mul_le_mul_of_nonneg_right h1 (inv_nonneg.mpr hr.le)
    _ = r⁻¹ * ‖x - y‖ := by ring

/-- **The derivative of a bump of rescaled distance.**  Let `χ` be differentiable with
`|deriv χ| ≤ κ` and equal to `1` on `[-1/2, 1/2]`, let `r > 0` and let `f` be differentiable at `q`.
Then `q' ↦ χ(‖f q' − c‖/r)` is differentiable at `q` and its derivative is bounded by
`κ r⁻¹ ‖fderiv f q‖`.

The case `f q = c` is where the norm is not differentiable: there the hypothesis `χ = 1` near `0`
(and continuity of `f`) makes the composite *locally constant*, so both conclusions are immediate. -/
theorem norm_fderiv_chi_norm_div_comp_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (χ : ℝ → ℝ) (κ r : ℝ) (c : E) (f : ℝ × ℝ → E) (q : ℝ × ℝ)
    (hr : 0 < r) (hκ : 0 ≤ κ) (hχd : Differentiable ℝ χ)
    (hχb : ∀ t : ℝ, |deriv χ t| ≤ κ)
    (hχ1 : ∀ t : ℝ, |t| ≤ 1 / 2 → χ t = 1)
    (hf : DifferentiableAt ℝ f q) :
    DifferentiableAt ℝ (fun q' : ℝ × ℝ => χ (‖f q' - c‖ / r)) q ∧
      ‖fderiv ℝ (fun q' : ℝ × ℝ => χ (‖f q' - c‖ / r)) q‖ ≤
        κ * r⁻¹ * ‖fderiv ℝ f q‖ := by
  by_cases hq : f q = c
  · -- the composite is locally the constant `1`
    have hev : (fun q' : ℝ × ℝ => χ (‖f q' - c‖ / r)) =ᶠ[nhds q] fun _ => (1 : ℝ) := by
      have hc : ∀ᶠ q' in nhds q, ‖f q' - f q‖ < r / 2 := by
        have h1 : ContinuousAt (fun q' : ℝ × ℝ => ‖f q' - f q‖) q :=
          (hf.continuousAt.sub continuousAt_const).norm
        exact h1.eventually_lt continuousAt_const (by simpa using half_pos hr)
      filter_upwards [hc] with q' hq'
      apply hχ1
      have he : ‖f q' - c‖ = ‖f q' - f q‖ := by rw [← hq]
      rw [he, abs_div, abs_of_pos hr, abs_of_nonneg (norm_nonneg _), div_le_iff₀ hr]
      linarith
    have hd : DifferentiableAt ℝ (fun q' : ℝ × ℝ => χ (‖f q' - c‖ / r)) q :=
      hev.differentiableAt_iff.mpr (differentiableAt_const (1 : ℝ))
    refine ⟨hd, ?_⟩
    have hzero : fderiv ℝ (fun q' : ℝ × ℝ => χ (‖f q' - c‖ / r)) q = 0 := by
      rw [hev.fderiv_eq]
      simp
    rw [hzero, norm_zero]
    positivity
  · -- away from the centre the chain rule applies
    have hy : f q - c ≠ 0 := sub_ne_zero.mpr hq
    have hsub : DifferentiableAt ℝ (fun z : E => z - c) (f q) :=
      differentiableAt_id.sub_const c
    have hηd : DifferentiableAt ℝ (fun z : E => ‖z - c‖ / r) (f q) := by
      have h1 : DifferentiableAt ℝ (fun z : E => ‖z - c‖) (f q) :=
        DifferentiableAt.norm ℝ hsub hy
      exact h1.mul_const r⁻¹
    have hχs : DifferentiableAt ℝ χ (‖f q - c‖ / r) := hχd.differentiableAt
    have hmid : DifferentiableAt ℝ (fun q' : ℝ × ℝ => ‖f q' - c‖ / r) q := hηd.comp q hf
    have hHd : DifferentiableAt ℝ (fun q' : ℝ × ℝ => χ (‖f q' - c‖ / r)) q :=
      hχs.comp q hmid
    refine ⟨hHd, ?_⟩
    have hg : DifferentiableAt ℝ (fun z : E => χ (‖z - c‖ / r)) (f q) := hχs.comp (f q) hηd
    have hcomp : fderiv ℝ (fun q' : ℝ × ℝ => χ (‖f q' - c‖ / r)) q =
        (fderiv ℝ (fun z : E => χ (‖z - c‖ / r)) (f q)).comp (fderiv ℝ f q) :=
      fderiv_comp (𝕜 := ℝ) q hg hf
    rw [hcomp]
    have hχnorm : ‖fderiv ℝ χ (‖f q - c‖ / r)‖ ≤ κ := by
      rw [← toSpanSingleton_deriv (f := χ) (x := ‖f q - c‖ / r),
        ContinuousLinearMap.norm_toSpanSingleton, Real.norm_eq_abs]
      exact hχb _
    have hηnorm : ‖fderiv ℝ (fun z : E => ‖z - c‖ / r) (f q)‖ ≤ r⁻¹ :=
      norm_fderiv_le_of_lipschitz ℝ (lipschitzWith_norm_sub_div (E := E) (c := c) hr)
    have hgnorm : ‖fderiv ℝ (fun z : E => χ (‖z - c‖ / r)) (f q)‖ ≤ κ * r⁻¹ := by
      rw [show (fun z : E => χ (‖z - c‖ / r)) = χ ∘ (fun z : E => ‖z - c‖ / r) from rfl,
        fderiv_comp (𝕜 := ℝ) (f q) hχs hηd]
      calc ‖(fderiv ℝ χ (‖f q - c‖ / r)).comp
              (fderiv ℝ (fun z : E => ‖z - c‖ / r) (f q))‖
          ≤ ‖fderiv ℝ χ (‖f q - c‖ / r)‖ *
              ‖fderiv ℝ (fun z : E => ‖z - c‖ / r) (f q)‖ :=
            ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ κ * r⁻¹ := by gcongr
    calc ‖(fderiv ℝ (fun z : E => χ (‖z - c‖ / r)) (f q)).comp (fderiv ℝ f q)‖
        ≤ ‖fderiv ℝ (fun z : E => χ (‖z - c‖ / r)) (f q)‖ * ‖fderiv ℝ f q‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ κ * r⁻¹ * ‖fderiv ℝ f q‖ := by gcongr

/-! ## The algebraic identity: the dent moves the level functional by the bump -/

/-- The displacement of the level functional under the dent of an `AnyDentDatum`:
`ℓ (D.deform z) = ℓ z + (a' χ(‖z − centre‖/r)) (ℓ d)`. -/
theorem anyDentDatum_deform_wall {ψ : Submission.Diffeo} {K : Knot} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ} {v : R3} {h R : ℝ} {ℓ : R3 →L[ℝ] ℝ} {U : Set R3}
    (D : AnyDentDatum ψ K s c σ u v h R ℓ U) (z : R3) :
    ℓ (D.deform z) = ℓ z + (D.a' * D.χ (‖z - D.centre‖ / D.r)) * ℓ D.d := by
  simp only [AnyDentDatum.deform, dentDeform, map_add, map_smul, smul_eq_mul]

/-! ## The estimate -/

/-- **The dent changes the derivative of the sweep height by at most `a' ‖ℓ‖ (κ/r) ‖d(par)‖`.**

This is the quantitative `C¹` bound of the design's `L4b` (`Final/NOTES_LEAD_L4b.md` §1.3), the
estimate that makes the deformed level function regular in the annulus of the dent. -/
theorem fderiv_sweepHeight_dent_sub_le {ψ : Submission.Diffeo} {K : Knot} {s u h R : ℝ}
    {c v : R3} {σ : Equiv.Perm (Fin 3)} {ℓ : R3 →L[ℝ] ℝ} {U : Set R3}
    (D : Work.Drive.Final.AnyDentDatum ψ K s c σ u v h R ℓ U) (hχ : ContDiff ℝ 1 D.χ)
    (hχ1 : ∀ t : ℝ, |t| ≤ 1 / 2 → D.χ t = 1) (q : ℝ × ℝ) :
    ‖fderiv ℝ (fun q' : ℝ × ℝ => ℓ (D.deform (Work.BoxShrink.Pinch.par ψ q'))) q -
        fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) q‖ ≤
      D.a' * ‖ℓ‖ * (D.κ / D.r) * ‖fderiv ℝ (Work.BoxShrink.Pinch.par ψ) q‖ := by
  have hχd : Differentiable ℝ D.χ := hχ.differentiable (by simp)
  have hpar : DifferentiableAt ℝ (Work.BoxShrink.Pinch.par ψ) q :=
    ((Work.BoxShrink.Pinch.par_contDiff ψ).differentiable (by simp)).differentiableAt
  -- the composite `χ ∘ (‖ · − centre‖/r) ∘ par` is differentiable with a bounded derivative
  obtain ⟨hHd, hHb⟩ := norm_fderiv_chi_norm_div_comp_le D.χ D.κ D.r D.centre
    (Work.BoxShrink.Pinch.par ψ) q D.r_pos (le_of_lt D.κ_pos) hχd D.χ_deriv_bound hχ1 hpar
  -- the deformed sweep height is the sweep height plus the bump `(a' ℓ d) χ(‖par − centre‖/r)`
  have hdec : (fun q' : ℝ × ℝ => ℓ (D.deform (Work.BoxShrink.Pinch.par ψ q'))) =
      fun q' => Work.Drive.EpsForm.sweepHeight ψ ℓ q' +
        (D.a' * ℓ D.d) * D.χ (‖Work.BoxShrink.Pinch.par ψ q' - D.centre‖ / D.r) := by
    funext q'
    change ℓ (D.deform (Work.BoxShrink.Pinch.par ψ q')) =
      ℓ (Work.BoxShrink.Pinch.par ψ q') +
        (D.a' * ℓ D.d) * D.χ (‖Work.BoxShrink.Pinch.par ψ q' - D.centre‖ / D.r)
    rw [anyDentDatum_deform_wall]
    ring
  have hS : DifferentiableAt ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) q :=
    (ContinuousLinearMap.differentiableAt ℓ).comp q hpar
  have hHderiv : HasFDerivAt (fun q' : ℝ × ℝ => Work.Drive.EpsForm.sweepHeight ψ ℓ q' +
        (D.a' * ℓ D.d) * D.χ (‖Work.BoxShrink.Pinch.par ψ q' - D.centre‖ / D.r))
      (fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) q +
        (D.a' * ℓ D.d) • fderiv ℝ (fun q' : ℝ × ℝ =>
          D.χ (‖Work.BoxShrink.Pinch.par ψ q' - D.centre‖ / D.r)) q) q :=
    hS.hasFDerivAt.add (hHd.hasFDerivAt.const_smul (D.a' * ℓ D.d))
  have hfderiv : fderiv ℝ (fun q' : ℝ × ℝ => ℓ (D.deform (Work.BoxShrink.Pinch.par ψ q'))) q =
      fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) q +
        (D.a' * ℓ D.d) • fderiv ℝ (fun q' : ℝ × ℝ =>
          D.χ (‖Work.BoxShrink.Pinch.par ψ q' - D.centre‖ / D.r)) q := by
    rw [hdec]
    exact hHderiv.fderiv
  rw [hfderiv, add_sub_cancel_left]
  have hAabs : |D.a' * ℓ D.d| ≤ D.a' * ‖ℓ‖ := by
    rw [abs_mul, abs_of_pos D.a'_pos]
    refine mul_le_mul_of_nonneg_left ?_ (le_of_lt D.a'_pos)
    calc |ℓ D.d| = ‖ℓ D.d‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖ℓ‖ * ‖D.d‖ := ℓ.le_opNorm D.d
      _ = ‖ℓ‖ := by rw [D.d_norm, mul_one]
  calc ‖(D.a' * ℓ D.d) • fderiv ℝ (fun q' : ℝ × ℝ =>
          D.χ (‖Work.BoxShrink.Pinch.par ψ q' - D.centre‖ / D.r)) q‖
      = |D.a' * ℓ D.d| * ‖fderiv ℝ (fun q' : ℝ × ℝ =>
          D.χ (‖Work.BoxShrink.Pinch.par ψ q' - D.centre‖ / D.r)) q‖ := by
        rw [norm_smul, Real.norm_eq_abs]
    _ ≤ (D.a' * ‖ℓ‖) * (D.κ * D.r⁻¹ * ‖fderiv ℝ (Work.BoxShrink.Pinch.par ψ) q‖) :=
        mul_le_mul hAabs hHb (norm_nonneg _)
          (mul_nonneg (le_of_lt D.a'_pos) (norm_nonneg ℓ))
    _ = D.a' * ‖ℓ‖ * (D.κ / D.r) * ‖fderiv ℝ (Work.BoxShrink.Pinch.par ψ) q‖ := by
        rw [div_eq_mul_inv]; ring

end

end Work.Drive.Final
