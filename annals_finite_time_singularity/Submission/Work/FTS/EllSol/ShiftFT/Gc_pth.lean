/-
Copyright: work module for the Elgindi finite-time singularity project (area `FTS.EllSol`).

# The `θ`-derivative of the truncating solution `Gc`

`Work.FTS.EllSol.ShiftFT.Gc N b u` is the particular solution of the shifted equation
`L_b G = chi N · L_b u`,

  `Gc N b u t θ = chi N t · u t θ + e^{bt} ∫_t^{2N} e^{-bs} (chi N)'(s) u(s,θ) ds`,

obtained by integrating by parts the *improper* integral `∫_t^∞ e^{-bs}(chi N)'(s) u(s,θ) ds`
(the primitive of the shifted quantity `e^{-bs}u`); see the module docstring of
`Submission/Work/FTS/EllSol/ShiftFT/ShiftPrimDefs.lean`.

The lemma proved here is the **angular** differentiation rule: for `C²` data `u` on the open
strip `ℝ × (0,π/2)` and every `θ ∈ (0,π/2)`,

  `∂_θ (Gc N b u)(t,θ) = (chi N)(t)·∂_θu(t,θ)
     + e^{bt} ∫_t^{2N} e^{-bs} (chi N)'(s) ∂_θu(s,θ) ds`.

The only analytic content is differentiating under the integral sign
(`intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`): the integration variable
runs over the *compact* interval `[t,2N]` and the cutoff `(chi N)'` is smooth, while `∂_θu` is
continuous on a compact box `uIcc t (2N) × Icc aθ bθ` contained in the open strip (because
`θ ∈ (0,π/2)` is interior) — so the derivative integrand admits a constant dominating function.
-/
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllSol.ShiftFT.ShiftPrimDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.ShiftFT

open MeasureTheory Set Filter
open scoped Real Topology

noncomputable section

set_option autoImplicit false

/-! ## Auxiliary: the `θ`-partial of a `C²` datum is continuous

This is the `n = 1` instance of the general fact that the curried partial derivative of a
function of class `C^{n+1}` on an open set is of class `C^n` there. -/
private theorem contDiffOn_uncurry_pth_two {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : ContDiffOn ℝ 2 (Function.uncurry G) V) :
    ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pth G)) V := by
  have hchain : ∀ p ∈ V, Work.Spaces.pth G p.1 p.2 = fderiv ℝ (Function.uncurry G) p (0, 1) :=
    fun p hp => Work.Spaces.pth_eq_fderiv
      ((h.differentiableOn (by norm_num)).differentiableAt (hV.mem_nhds hp))
  have hfd : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry G) p) V :=
    h.fderiv_of_isOpen hV (m := 1) (by norm_num)
  have hcomp : ContDiffOn ℝ 1
      (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) p) (0, 1)) V := by
    simpa using hfd.clm_apply contDiffOn_const
  exact hcomp.congr (fun p hp => hchain p hp)

/-! ## Auxiliary: differentiation of the `θ`-slice of the integral -/

/-- The `θ`-derivative of the `t`-integrated kernel `∫_t^{2N} e^{-bs}(chi N)'(s)u(s,θ)ds`:
`∂_θ` acts on `u` alone. -/
private theorem hasDerivAt_slice_integral (N b t : ℝ) (u : ℝ → ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      HasDerivAt
        (fun x => ∫ s in t..(2 * N),
          Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s * u s x)
        (∫ s in t..(2 * N),
          Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s * Work.Spaces.pth u s θ)
        θ := by
  intro θ hθ
  have hθ1 : 0 < θ := hθ.1
  have hθ2 : θ < Real.pi / 2 := hθ.2
  -- an angular window around `θ` still contained in `(0,π/2)`
  obtain ⟨aθ, bθ, haθ, hθa, hθb, hbθ⟩ :
      ∃ aθ bθ : ℝ, 0 < aθ ∧ aθ < θ ∧ θ < bθ ∧ bθ < Real.pi / 2 :=
    ⟨θ / 2, (θ + Real.pi / 2) / 2, by linarith, by linarith,
      by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hVopen : IsOpen ((Set.univ : Set ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    ((isOpen_univ : IsOpen (Set.univ : Set ℝ))).prod isOpen_Ioo
  -- the compact box of integration, inside the open strip
  have hbox : ∀ p ∈ Set.uIcc t (2 * N) ×ˢ Set.Icc aθ bθ,
      p ∈ (Set.univ : Set ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    intro p hp
    rw [Set.mem_prod] at hp ⊢
    exact ⟨trivial, lt_of_lt_of_le haθ hp.2.1, lt_of_le_of_lt hp.2.2 hbθ⟩
  have hchi : Continuous (deriv (Work.FTS.EllSol.Trunc.chi N)) :=
    (Work.FTS.EllSol.Trunc.chi_contDiff 1 N).continuous_deriv (by norm_num)
  have hexp : Continuous (fun s : ℝ => Real.exp (-(b * s))) :=
    Real.continuous_exp.comp ((continuous_const.mul continuous_id).neg)
  -- the kernel `s ↦ e^{-bs}(chi N)'(s)` on the box
  have hbase : ContinuousOn (fun p : ℝ × ℝ =>
      Real.exp (-(b * p.1)) * deriv (Work.FTS.EllSol.Trunc.chi N) p.1)
      (Set.uIcc t (2 * N) ×ˢ Set.Icc aθ bθ) :=
    (((hexp.comp continuous_fst).mul (hchi.comp continuous_fst)).continuousOn)
  have hpthc : ContinuousOn (Function.uncurry (Work.Spaces.pth u))
      ((Set.univ : Set ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (contDiffOn_uncurry_pth_two hVopen hu).continuousOn
  have hup : ContinuousOn (Function.uncurry u)
      ((Set.univ : Set ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) := hu.continuousOn
  have hcontF : ContinuousOn (fun p : ℝ × ℝ =>
      Real.exp (-(b * p.1)) * deriv (Work.FTS.EllSol.Trunc.chi N) p.1 * u p.1 p.2)
      (Set.uIcc t (2 * N) ×ˢ Set.Icc aθ bθ) := hbase.mul (hup.mono hbox)
  have hcontF' : ContinuousOn (fun p : ℝ × ℝ =>
      Real.exp (-(b * p.1)) * deriv (Work.FTS.EllSol.Trunc.chi N) p.1
        * Work.Spaces.pth u p.1 p.2)
      (Set.uIcc t (2 * N) ×ˢ Set.Icc aθ bθ) := hbase.mul (hpthc.mono hbox)
  -- a constant dominating the derivative integrand on the box
  obtain ⟨B, hB⟩ := (isCompact_uIcc.prod isCompact_Icc).exists_bound_of_continuousOn hcontF'
  -- the slices, for fixed angle in the window
  have hsliceF : ∀ x ∈ Set.Ioo aθ bθ, ContinuousOn (fun s : ℝ =>
      Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s * u s x)
      (Set.uIcc t (2 * N)) := by
    intro x hx
    refine hcontF.comp (continuousOn_id.prodMk continuousOn_const) ?_
    intro s hs
    exact ⟨hs, ⟨le_of_lt hx.1, le_of_lt hx.2⟩⟩
  have hsliceF' : ContinuousOn (fun s : ℝ =>
      Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s * Work.Spaces.pth u s θ)
      (Set.uIcc t (2 * N)) := by
    refine hcontF'.comp (continuousOn_id.prodMk continuousOn_const) ?_
    intro s hs
    exact ⟨hs, ⟨le_of_lt hθa, le_of_lt hθb⟩⟩
  have hF_meas : ∀ᶠ x in 𝓝 θ, AEStronglyMeasurable (fun s : ℝ =>
      Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s * u s x)
      (volume.restrict (Set.uIoc t (2 * N))) := by
    filter_upwards [isOpen_Ioo.mem_nhds ⟨hθa, hθb⟩] with x hx
    exact ((hsliceF x hx).mono Set.uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc
  have hF_int : IntervalIntegrable (fun s : ℝ =>
      Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s * u s θ) volume t (2 * N) :=
    (hsliceF θ ⟨hθa, hθb⟩).intervalIntegrable
  have hF'_meas : AEStronglyMeasurable (fun s : ℝ =>
      Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s * Work.Spaces.pth u s θ)
      (volume.restrict (Set.uIoc t (2 * N))) :=
    (hsliceF'.mono Set.uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc
  have h_bound : ∀ᵐ s ∂volume, s ∈ Set.uIoc t (2 * N) → ∀ x ∈ Set.Ioo aθ bθ,
      ‖Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s * Work.Spaces.pth u s x‖
        ≤ (fun _ : ℝ => B) s :=
    Eventually.of_forall fun s hs x hx =>
      hB (s, x) ⟨Set.uIoc_subset_uIcc hs, ⟨le_of_lt hx.1, le_of_lt hx.2⟩⟩
  have h_diff : ∀ᵐ s ∂volume, s ∈ Set.uIoc t (2 * N) → ∀ x ∈ Set.Ioo aθ bθ,
      HasDerivAt (fun x' => Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s
          * u s x')
        (Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s
          * Work.Spaces.pth u s x) x := by
    refine Eventually.of_forall fun s _hs x hx => ?_
    have hxV : (s, x) ∈ (Set.univ : Set ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      ⟨trivial, lt_of_lt_of_le haθ (le_of_lt hx.1), lt_trans hx.2 hbθ⟩
    have hdu : DifferentiableAt ℝ (Function.uncurry u) (s, x) :=
      (hu.differentiableOn (by norm_num)).differentiableAt (hVopen.mem_nhds hxV)
    exact (Work.Spaces.differentiableAt_curry_right hdu).hasDerivAt.const_mul _
  exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := t) (b := 2 * N) (x₀ := θ) (s := Set.Ioo aθ bθ)
    (bound := fun _ : ℝ => B)
    (F := fun x s => Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s * u s x)
    (F' := fun x s => Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s
      * Work.Spaces.pth u s x)
    (isOpen_Ioo.mem_nhds ⟨hθa, hθb⟩) hF_meas hF_int hF'_meas h_bound
    intervalIntegrable_const h_diff).2

/-! ## The target -/

theorem Gc_pth (N b : ℝ) (u : ℝ → ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    ∀ t θ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      Work.Spaces.pth (Work.FTS.EllSol.ShiftFT.Gc N b u) t θ
      = Work.FTS.EllSol.Trunc.chi N t * Work.Spaces.pth u t θ
        + Real.exp (b * t) * ∫ s in t..(2 * N),
            Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s
              * Work.Spaces.pth u s θ := by
  intro t θ hθ
  have hVopen : IsOpen ((Set.univ : Set ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    ((isOpen_univ : IsOpen (Set.univ : Set ℝ))).prod isOpen_Ioo
  have hkey := hasDerivAt_slice_integral N b t u hu θ hθ
  have hdiffu : HasDerivAt (fun x => u t x) (Work.Spaces.pth u t θ) θ := by
    have hdu : DifferentiableAt ℝ (Function.uncurry u) (t, θ) :=
      (hu.differentiableOn (by norm_num)).differentiableAt (hVopen.mem_nhds ⟨trivial, hθ⟩)
    exact (Work.Spaces.differentiableAt_curry_right hdu).hasDerivAt
  have h1 : HasDerivAt (fun x => Work.FTS.EllSol.Trunc.chi N t * u t x)
      (Work.FTS.EllSol.Trunc.chi N t * Work.Spaces.pth u t θ) θ :=
    hdiffu.const_mul _
  have h2 : HasDerivAt
      (fun x => Real.exp (b * t) * ∫ s in t..(2 * N),
        Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s * u s x)
      (Real.exp (b * t) * ∫ s in t..(2 * N),
        Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s
          * Work.Spaces.pth u s θ) θ :=
    hkey.const_mul _
  have hsum := h1.add h2
  have hfun : (fun x => Work.FTS.EllSol.ShiftFT.Gc N b u t x) = fun x =>
      Work.FTS.EllSol.Trunc.chi N t * u t x
        + Real.exp (b * t) * ∫ s in t..(2 * N),
            Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s * u s x := by
    funext x; rfl
  change deriv (fun x => Work.FTS.EllSol.ShiftFT.Gc N b u t x) θ = _
  rw [hfun]
  exact hsum.deriv

end

end Work.FTS.EllSol.ShiftFT
