import Mathlib
import Submission.Work.RPV.Defs
import Submission.Work.RPB.Defs
import Submission.Work.RPB.B5.chordPS_contDiff

/-!
# B5: elementary tools for the chart-region Lagrangian computation

Helpers used by `Work.RPB.B5.chart_region_lag` (and available to the sibling
lemmas `Work.RPB.B5.chart_deriv_x` / `Work.RPB.B5.chart_deriv_t`):

* `symp_smul_add`, `symp_self` — the bilinearity/skew facts for `Work.RPV.symp` in exactly the
  shape the final cancellation uses;
* `hasDerivAt_pair_comp` — the two-variable chain rule `s ↦ Φ (s, ψ s)` for a `PS`-valued `Φ`,
  rewritten into the *partial* derivatives at the point, so that it can be applied without ever
  naming an `fderiv`;
* `chordSurf_pair_contDiffAt` — the chord surface is smooth in the `(t, r)` variables at every
  point with `0 < r < π` (the phase `a` being smooth only on the strip `[0,1] × ℝ × [0,π]`, the
  statement is at a *point*, and in `τ` the point is allowed to be on the boundary of `[0,1]`).
-/

set_option autoImplicit false

open Filter
open scoped Topology ContDiff

noncomputable section

namespace Work.RPB.B5

/-- Bilinearity of `Work.RPV.symp` in the shape used for the chart computation. -/
theorem symp_smul_add (a b : ℝ) (u v w : Work.RPV.PS) :
    Work.RPV.symp (a • u) (v + b • w) = a * (Work.RPV.symp u v + b * Work.RPV.symp u w) := by
  simp only [Work.RPV.symp, Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add]
  ring

/-- `Work.RPV.symp` is alternating. -/
theorem symp_self (u : Work.RPV.PS) : Work.RPV.symp u u = 0 := by
  simp only [Work.RPV.symp]; ring

/-- **Two-variable chain rule for `s ↦ Φ (s, ψ s)`.**  If `Φ : ℝ × ℝ → PS` is differentiable at
`(t, ψ t)` and `ψ` is differentiable at `t`, then `s ↦ Φ (s, ψ s)` is differentiable at `t` with
derivative the sum of the two partial derivatives: the `t`-slope of the first argument plus
`deriv ψ t` times the slope in the second argument. -/
theorem hasDerivAt_pair_comp {Φ : ℝ × ℝ → Work.RPV.PS} {ψ : ℝ → ℝ} {t : ℝ}
    (hΦ : DifferentiableAt ℝ Φ (t, ψ t)) (hψ : DifferentiableAt ℝ ψ t) :
    HasDerivAt (fun s => Φ (s, ψ s))
      (deriv (fun u => Φ (u, ψ t)) t + deriv ψ t • deriv (fun σ => Φ (t, σ)) (ψ t)) t := by
  have hL : HasFDerivAt Φ (fderiv ℝ Φ (t, ψ t)) (t, ψ t) := hΦ.hasFDerivAt
  have hpair : HasDerivAt (fun s : ℝ => (s, ψ s)) ((1 : ℝ), deriv ψ t) t :=
    (hasDerivAt_id t).prodMk hψ.hasDerivAt
  have hc : HasDerivAt (Φ ∘ fun s : ℝ => (s, ψ s))
      ((fderiv ℝ Φ (t, ψ t)) (1, deriv ψ t)) t :=
    hL.comp_hasDerivAt t hpair
  have hslice1 : deriv (fun u => Φ (u, ψ t)) t = (fderiv ℝ Φ (t, ψ t)) (1, 0) := by
    have h1 : HasFDerivAt (fun u : ℝ => Φ (u, ψ t))
        ((fderiv ℝ Φ (t, ψ t)).comp
          ((ContinuousLinearMap.id ℝ ℝ).prod (0 : ℝ →L[ℝ] ℝ))) t :=
      hL.comp t ((hasFDerivAt_id t).prodMk (hasFDerivAt_const (ψ t) t))
    rw [h1.hasDerivAt.deriv]
    simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply]
  have hslice2 : deriv (fun σ => Φ (t, σ)) (ψ t) = (fderiv ℝ Φ (t, ψ t)) (0, 1) := by
    have h1 : HasFDerivAt (fun σ : ℝ => Φ (t, σ))
        ((fderiv ℝ Φ (t, ψ t)).comp
          (((0 : ℝ →L[ℝ] ℝ)).prod (ContinuousLinearMap.id ℝ ℝ))) (ψ t) :=
      hL.comp (ψ t) ((hasFDerivAt_const t (ψ t)).prodMk (hasFDerivAt_id (ψ t)))
    rw [h1.hasDerivAt.deriv]
    simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply]
  refine hc.congr_deriv ?_
  rw [hslice1, hslice2, show ((1 : ℝ), deriv ψ t) = (1, 0) + deriv ψ t • ((0 : ℝ), 1) by simp]
  rw [map_add, map_smul]

/-- **Smoothness of the chord surface in `(t, r)`.**  For `τ ∈ [0,1]` and `0 < r < π`, the map
`z ↦ chordSurf CI.c a τ z.1 z.2` is `C^8` at every `(t, r)`.

The phase `a` is only known to be smooth on the strip `[0,1] × ℝ × [0,π]`, so the statement is
local in `(t, r)`; the `τ`-coordinate is held fixed (and may be `0` or `1`). -/
theorem chordSurf_pair_contDiffAt (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (ha : Work.RPB.IsChordPhase CI.c a) {τ t r : ℝ}
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (hr : r ∈ Set.Ioo (0 : ℝ) Real.pi) :
    ContDiffAt ℝ 8 (fun z : ℝ × ℝ => Work.RPB.chordSurf CI.c a τ z.1 z.2) (t, r) := by
  set s : Set (ℝ × ℝ) := Set.univ ×ˢ Set.Icc (0 : ℝ) Real.pi with hs
  set strip : Set (ℝ × (ℝ × ℝ)) :=
    Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Icc (0 : ℝ) Real.pi with hstrip
  have hsnhds : s ∈ 𝓝 (t, r) := by
    rw [hs]; exact prod_mem_nhds univ_mem (Icc_mem_nhds hr.1 hr.2)
  have hmem : ((τ, (t, r)) : ℝ × (ℝ × ℝ)) ∈ strip := by
    rw [hstrip]; exact ⟨hτ, trivial, hr.1.le, hr.2.le⟩
  -- the phase, as a function of `z`
  have hphase : ContDiffWithinAt ℝ ∞ (fun z : ℝ × ℝ => a τ z.1 z.2) s (t, r) := by
    let A : ℝ × (ℝ × ℝ) → ℝ := fun w => a w.1 w.2.1 w.2.2
    have hA : ContDiffWithinAt ℝ ∞ A strip ((τ, (t, r))) := ha.1.contDiffWithinAt hmem
    have hF : ContDiffWithinAt ℝ ∞
        (fun z : ℝ × ℝ => ((τ, (z.1, z.2)) : ℝ × (ℝ × ℝ))) s (t, r) :=
      (by fun_prop : ContDiff ℝ ∞
        (fun z : ℝ × ℝ => ((τ, (z.1, z.2)) : ℝ × (ℝ × ℝ)))).contDiffAt.contDiffWithinAt
    have hmap : Set.MapsTo (fun z : ℝ × ℝ => ((τ, (z.1, z.2)) : ℝ × (ℝ × ℝ))) s strip := by
      intro z hz
      rw [hs, Set.mem_prod] at hz
      rw [hstrip]
      exact ⟨hτ, trivial, hz.2.1, hz.2.2⟩
    exact hA.comp (t, r) hF hmap
  -- the triple map into `ℂ × (ℂ × ℝ)`
  have hinner : ContDiffWithinAt ℝ ∞
      (fun z : ℝ × ℝ => (CI.c τ (z.1 + z.2), (CI.c τ (z.1 - z.2), a τ z.1 z.2)))
      s (t, r) := by
    have hplus : ContDiffWithinAt ℝ ∞
        (fun z : ℝ × ℝ => CI.c τ (z.1 + z.2)) s (t, r) :=
      (CI.smooth.comp (by fun_prop : ContDiff ℝ ∞
        (fun z : ℝ × ℝ => (τ, z.1 + z.2)))).contDiffAt.contDiffWithinAt
    have hminus : ContDiffWithinAt ℝ ∞
        (fun z : ℝ × ℝ => CI.c τ (z.1 - z.2)) s (t, r) :=
      (CI.smooth.comp (by fun_prop : ContDiff ℝ ∞
        (fun z : ℝ × ℝ => (τ, z.1 - z.2)))).contDiffAt.contDiffWithinAt
    exact hplus.prodMk (hminus.prodMk hphase)
  -- compose with the smooth chord map
  have hout : ContDiffAt ℝ ∞
      (fun v : ℂ × (ℂ × ℝ) => Work.RPV.chordPS v.1 v.2.1 v.2.2)
      (CI.c τ (t + r), (CI.c τ (t - r), a τ t r)) :=
    (Work.RPB.B5.chordPS_contDiff ⊤).contDiffAt
  have hcomp0 := ContDiffAt.comp (t, r) hout (hinner.contDiffAt hsnhds)
  exact hcomp0.of_le (by norm_num)

end Work.RPB.B5
