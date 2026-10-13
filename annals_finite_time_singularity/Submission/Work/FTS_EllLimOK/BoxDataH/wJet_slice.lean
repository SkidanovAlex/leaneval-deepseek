import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_EllLimOK.BoxDataH.WithinVec

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `FTS_EllLimOK.BoxDataH.wJet_slice` — the slice derivatives of a `C²`-within-the-box function

`WithinVec` defines the six within-partials `wPz`, `wPth`, `wPzz`, `wPtz`, `wPzt`, `wPtt` of a
function `F : ℝ × ℝ → ℝ` on the closed box `cbox a b = [a,b] × [0,π/2]`.  This module shows that
they are the derivatives of the corresponding one-variable slices: for
`F` of class `C²` *within* the box (only!), and every `(z,θ) ∈ cbox a b`,

* `∂_z (z' ↦ F (z',θ)) = wPz F (z,θ)`, `∂_θ (θ' ↦ F (z,θ')) = wPth F (z,θ)`,
* `∂_z (z' ↦ wPz F (z',θ)) = wPzz F (z,θ)`, `∂_θ (θ' ↦ wPz F (z,θ')) = wPtz F (z,θ)`,
* `∂_z (z' ↦ wPth F (z',θ)) = wPzt F (z,θ)`, `∂_θ (θ' ↦ wPth F (z,θ')) = wPtt F (z,θ)`,

where all the derivatives are taken *within* the corresponding closed interval (`Set.Icc a b`,
resp. `Set.Icc 0 (π/2)`); the endpoints are covered.

The proof is the chain rule for within-derivatives
(`HasFDerivWithinAt.comp_hasDerivWithinAt`) applied to the two coordinate curves
`z' ↦ (z',θ)` and `θ' ↦ (z,θ')`, which map the interval into the box, together with the bridges
`wPz_eq_fderivWithin` etc. of `WithinVec` and the `C¹`-regularity of `fderivWithin ℝ F (cbox a b)`
(`ContDiffOn.fderivWithin`).
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.BoxDataH

open Work.FTS_EllLimOK.BoxRegAux (dz dth dir1 consD)
open Work.FTS_EllLimOK (cbox mem_cbox)

set_option autoImplicit false

/-! ## The two coordinate curves of the box -/

/-- The `z`-curve `z' ↦ (z',θ)` of the box, as a within-derivative on `[c,d]`. -/
theorem wJetSlice_zCurve {c d : ℝ} (θ z : ℝ) :
    HasDerivWithinAt (fun z' => ((z', θ) : ℝ × ℝ)) ((1 : ℝ), (0 : ℝ)) (Set.Icc c d) z :=
  ((hasDerivAt_id z).prodMk (hasDerivAt_const z θ)).hasDerivWithinAt

/-- The `θ`-curve `θ' ↦ (z,θ')` of the box, as a within-derivative on `[c,d]`. -/
theorem wJetSlice_thCurve {c d : ℝ} (z θ : ℝ) :
    HasDerivWithinAt (fun θ' => ((z, θ') : ℝ × ℝ)) ((0 : ℝ), (1 : ℝ)) (Set.Icc c d) θ :=
  ((hasDerivAt_const θ z).prodMk (hasDerivAt_id θ)).hasDerivWithinAt

/-! ## The slices of a function -/

/-- **The `z`-slice of a function** with a within-derivative `L` on the box: its `z`-derivative
within `[a,b]` is `L dz`. -/
theorem wJetSlice_slice_z {a b : ℝ} {F : ℝ × ℝ → ℝ} {L : (ℝ × ℝ) →L[ℝ] ℝ}
    {z θ : ℝ} (hθ : θ ∈ Set.Icc 0 (π / 2))
    (hF : HasFDerivWithinAt F L (cbox a b) (z, θ)) :
    HasDerivWithinAt (fun z' => F (z', θ)) (L dz) (Set.Icc a b) z := by
  have hcurve := wJetSlice_zCurve (c := a) (d := b) θ z
  have hst : MapsTo (fun z' => ((z', θ) : ℝ × ℝ)) (Set.Icc a b) (cbox a b) :=
    fun z' hz => ⟨hz, hθ⟩
  have h := hF.comp_hasDerivWithinAt z hcurve hst
  simpa [Function.comp_def, dz] using h

/-- **The `θ`-slice of a function** with a within-derivative `L` on the box: its `θ`-derivative
within `[0,π/2]` is `L dth`. -/
theorem wJetSlice_slice_th {a b : ℝ} {F : ℝ × ℝ → ℝ} {L : (ℝ × ℝ) →L[ℝ] ℝ}
    {z θ : ℝ} (hz : z ∈ Set.Icc a b)
    (hF : HasFDerivWithinAt F L (cbox a b) (z, θ)) :
    HasDerivWithinAt (fun θ' => F (z, θ')) (L dth) (Set.Icc 0 (π / 2)) θ := by
  have hcurve := wJetSlice_thCurve (c := 0) (d := π / 2) z θ
  have hst : MapsTo (fun θ' => ((z, θ') : ℝ × ℝ)) (Set.Icc 0 (π / 2)) (cbox a b) :=
    fun θ' hθ => ⟨hz, hθ⟩
  have h := hF.comp_hasDerivWithinAt θ hcurve hst
  simpa [Function.comp_def, dth] using h

/-! ## The slices of a continuous-linear-map-valued function -/

/-- **The `z`-slice of a `(ℝ × ℝ) →L[ℝ] ℝ`-valued function**, evaluated at a fixed direction
`v`: its `z`-derivative within `[a,b]` is `(P' dz) v`, where `P'` is the within-derivative of
`P`. -/
theorem wJetSlice_slice_z_clm {a b : ℝ} {P : ℝ × ℝ → ((ℝ × ℝ) →L[ℝ] ℝ)}
    {P' : (ℝ × ℝ) →L[ℝ] ((ℝ × ℝ) →L[ℝ] ℝ)} {z θ : ℝ}
    (hθ : θ ∈ Set.Icc 0 (π / 2)) (v : ℝ × ℝ)
    (hP : HasFDerivWithinAt P P' (cbox a b) (z, θ)) :
    HasDerivWithinAt (fun z' => P (z', θ) v) ((P' dz) v) (Set.Icc a b) z := by
  have hcurve := wJetSlice_zCurve (c := a) (d := b) θ z
  have hst : MapsTo (fun z' => ((z', θ) : ℝ × ℝ)) (Set.Icc a b) (cbox a b) :=
    fun z' hz => ⟨hz, hθ⟩
  have hc := hP.comp_hasDerivWithinAt z hcurve hst
  have hu : HasDerivWithinAt (fun _ : ℝ => v) (0 : ℝ × ℝ) (Set.Icc a b) z :=
    (hasDerivAt_const z v).hasDerivWithinAt
  have h := hc.clm_apply hu
  simpa [Function.comp_def, dz] using h

/-- **The `θ`-slice of a `(ℝ × ℝ) →L[ℝ] ℝ`-valued function**, evaluated at a fixed direction
`v`: its `θ`-derivative within `[0,π/2]` is `(P' dth) v`. -/
theorem wJetSlice_slice_th_clm {a b : ℝ} {P : ℝ × ℝ → ((ℝ × ℝ) →L[ℝ] ℝ)}
    {P' : (ℝ × ℝ) →L[ℝ] ((ℝ × ℝ) →L[ℝ] ℝ)} {z θ : ℝ}
    (hz : z ∈ Set.Icc a b) (v : ℝ × ℝ)
    (hP : HasFDerivWithinAt P P' (cbox a b) (z, θ)) :
    HasDerivWithinAt (fun θ' => P (z, θ') v) ((P' dth) v) (Set.Icc 0 (π / 2)) θ := by
  have hcurve := wJetSlice_thCurve (c := 0) (d := π / 2) z θ
  have hst : MapsTo (fun θ' => ((z, θ') : ℝ × ℝ)) (Set.Icc 0 (π / 2)) (cbox a b) :=
    fun θ' hθ => ⟨hz, hθ⟩
  have hc := hP.comp_hasDerivWithinAt θ hcurve hst
  have hu : HasDerivWithinAt (fun _ : ℝ => v) (0 : ℝ × ℝ) (Set.Icc 0 (π / 2)) θ :=
    (hasDerivAt_const θ v).hasDerivWithinAt
  have h := hc.clm_apply hu
  simpa [Function.comp_def, dth] using h

/-! ## The six slice derivatives -/

theorem wJet_slice {a b : ℝ} {F : ℝ × ℝ → ℝ} (hab : a < b)
    (hsm : ContDiffOn ℝ 2 F (Work.FTS_EllLimOK.cbox a b)) :
    (∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc 0 (π / 2),
      HasDerivWithinAt (fun z' => F (z', θ))
        (Work.FTS_EllLimOK.BoxDataH.wPz (Work.FTS_EllLimOK.cbox a b) F (z, θ))
        (Set.Icc a b) z) ∧
    (∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc 0 (π / 2),
      HasDerivWithinAt (fun θ' => F (z, θ'))
        (Work.FTS_EllLimOK.BoxDataH.wPth (Work.FTS_EllLimOK.cbox a b) F (z, θ))
        (Set.Icc 0 (π / 2)) θ) ∧
    (∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc 0 (π / 2),
      HasDerivWithinAt (fun z' => Work.FTS_EllLimOK.BoxDataH.wPz (Work.FTS_EllLimOK.cbox a b) F (z', θ))
        (Work.FTS_EllLimOK.BoxDataH.wPzz (Work.FTS_EllLimOK.cbox a b) F (z, θ))
        (Set.Icc a b) z) ∧
    (∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc 0 (π / 2),
      HasDerivWithinAt (fun θ' => Work.FTS_EllLimOK.BoxDataH.wPz (Work.FTS_EllLimOK.cbox a b) F (z, θ'))
        (Work.FTS_EllLimOK.BoxDataH.wPtz (Work.FTS_EllLimOK.cbox a b) F (z, θ))
        (Set.Icc 0 (π / 2)) θ) ∧
    (∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc 0 (π / 2),
      HasDerivWithinAt (fun z' => Work.FTS_EllLimOK.BoxDataH.wPth (Work.FTS_EllLimOK.cbox a b) F (z', θ))
        (Work.FTS_EllLimOK.BoxDataH.wPzt (Work.FTS_EllLimOK.cbox a b) F (z, θ))
        (Set.Icc a b) z) ∧
    (∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc 0 (π / 2),
      HasDerivWithinAt (fun θ' => Work.FTS_EllLimOK.BoxDataH.wPth (Work.FTS_EllLimOK.cbox a b) F (z, θ'))
        (Work.FTS_EllLimOK.BoxDataH.wPtt (Work.FTS_EllLimOK.cbox a b) F (z, θ))
        (Set.Icc 0 (π / 2)) θ) := by
  have hU : UniqueDiffOn ℝ (cbox a b) := uniqueDiffOn_cbox hab
  have hFd : DifferentiableOn ℝ F (cbox a b) := hsm.differentiableOn (by norm_num)
  have hPsm : ContDiffOn ℝ 1 (fderivWithin ℝ F (cbox a b)) (cbox a b) :=
    hsm.fderivWithin hU (by norm_num)
  have hPd : DifferentiableOn ℝ (fderivWithin ℝ F (cbox a b)) (cbox a b) :=
    hPsm.differentiableOn (by norm_num)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz θ hθ
    have hp : (z, θ) ∈ cbox a b := ⟨hz, hθ⟩
    have h := wJetSlice_slice_z hθ ((hFd (z, θ) hp).hasFDerivWithinAt)
    rwa [← wPz_eq_fderivWithin (hU (z, θ) hp)] at h
  · intro z hz θ hθ
    have hp : (z, θ) ∈ cbox a b := ⟨hz, hθ⟩
    have h := wJetSlice_slice_th hz ((hFd (z, θ) hp).hasFDerivWithinAt)
    rwa [← wPth_eq_fderivWithin (hU (z, θ) hp)] at h
  · intro z hz θ hθ
    have hp : (z, θ) ∈ cbox a b := ⟨hz, hθ⟩
    have h := wJetSlice_slice_z_clm hθ dz ((hPd (z, θ) hp).hasFDerivWithinAt)
    rw [← wPzz_eq_fderivWithin hU hp] at h
    exact h.congr (fun z' hz' => wPz_eq_fderivWithin (hU (z', θ) ⟨hz', hθ⟩))
      (wPz_eq_fderivWithin (hU (z, θ) hp))
  · intro z hz θ hθ
    have hp : (z, θ) ∈ cbox a b := ⟨hz, hθ⟩
    have h := wJetSlice_slice_th_clm hz dz ((hPd (z, θ) hp).hasFDerivWithinAt)
    rw [← wPtz_eq_fderivWithin hU hp] at h
    exact h.congr (fun θ' hθ' => wPz_eq_fderivWithin (hU (z, θ') ⟨hz, hθ'⟩))
      (wPz_eq_fderivWithin (hU (z, θ) hp))
  · intro z hz θ hθ
    have hp : (z, θ) ∈ cbox a b := ⟨hz, hθ⟩
    have h := wJetSlice_slice_z_clm hθ dth ((hPd (z, θ) hp).hasFDerivWithinAt)
    rw [← wPzt_eq_fderivWithin hU hp] at h
    exact h.congr (fun z' hz' => wPth_eq_fderivWithin (hU (z', θ) ⟨hz', hθ⟩))
      (wPth_eq_fderivWithin (hU (z, θ) hp))
  · intro z hz θ hθ
    have hp : (z, θ) ∈ cbox a b := ⟨hz, hθ⟩
    have h := wJetSlice_slice_th_clm hz dth ((hPd (z, θ) hp).hasFDerivWithinAt)
    rw [← wPtt_eq_fderivWithin hU hp] at h
    exact h.congr (fun θ' hθ' => wPth_eq_fderivWithin (hU (z, θ') ⟨hz, hθ'⟩))
      (wPth_eq_fderivWithin (hU (z, θ) hp))

end Work.FTS_EllLimOK.BoxDataH
