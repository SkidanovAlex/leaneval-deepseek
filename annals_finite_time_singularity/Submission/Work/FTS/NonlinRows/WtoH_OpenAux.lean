/-
Copyright: work module for the Elgindi finite-time singularity project.

# The `SmoothOpen` (open-quadrant) port of the `WtoH` calculus layer

`Submission/Work/FTS/H2/Q/Base.lean` provides the calculus layer of Elgindi's Proposition
`WtoH` in the class `Work.FTS.LocData.SmoothQuad` (`C^∞` on `(-1,∞) × (0,π/2)`).  The primed
rows of `Submission/Work/FTS/NonlinRows/` are stated for the *open*-quadrant class
`Work.FTS.EllipticEst.SmoothOpen` (`C^∞` on `(0,∞) × (0,π/2)` only), so the class-dependent
pieces of that layer have to be re-proved here:

* `contDiffOn_divZ2_QO` — smoothness of `divZ2 f = f/z²` on the open quadrant;
* `contDiffOn/contDiffAt_divZ2_zslice_O` — smoothness of its `z`-slices;
* `contDiffOn/contDiffAt_DthIter_divZ2_zslice_O` — smoothness of the `z`-slices of its
  `D_θ`-iterates;
* `pzIter_divZ2_expansion_aux_O`, `expand_aux_O` — the Leibniz expansions of `∂_z^m f` through
  `f = z²·divZ2 f`;
* `tri_aux_O` — the `𝒲^{4,∞}`-bound on `(z+1)^{j+3} ∂_z^j (D_θ^i (divZ2 f))` used by
  `WtoH_Mixed_Q`/`WtoH_Radial_Q`.

The class-agnostic pieces (`pzIter_mul_local_sm`, `pzIter_sq_mul_sm`, `pzIter_three_mul_sm`,
`tri_bound_sm`, `Work.Spaces.factor_bound`, `Work.Elliptic.pzIter_congr_of_eventually`,
`Work.Elliptic.DthIter_divZ2_eq`) are imported and used unchanged; the port only replaces
`Ioi (-1)` by `Ioi 0` in the slice smoothness inputs, which is exactly what `SmoothOpen`
supplies (through `Work.FTS.LocData.contDiffOn_slice_z`).

Everything here is fully proved (no deferred steps).
-/
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.H2.Q.Base
import Submission.Work.Elliptic.WtoH_Mixed_g_eq
import Submission.Work.Spaces.factor_bound
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.LocData.SmoothChain

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.NonlinRows

open Work.Spaces

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- The open quadrant `(0,∞) × (0,π/2)` on which the weights are honest. -/
abbrev QO : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)

theorem isOpen_QO : IsOpen QO := isOpen_Ioi.prod isOpen_Ioo

/-! ## `divZ2 f` on the open quadrant -/

/-- `divZ2 f = f/z²` is `C^∞` (genuine smooth order) on the open quadrant, for
`SmoothOpen f`. -/
theorem contDiffOn_divZ2_QO {f : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen f) :
    ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry (Work.Elliptic.divZ2 f)) QO := by
  have hf : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f) QO := by
    simpa only [Work.FTS.EllipticEst.SmoothOpen, Work.FTS.EllipticEst.Q0] using hsm
  have hden : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => p.1 ^ 2) QO := contDiffOn_fst.pow 2
  have hdiv := hf.div hden (fun p hp => pow_ne_zero 2 (ne_of_gt hp.1))
  refine hdiv.congr fun p hp => ?_
  rfl

/-- The `z`-slices of `divZ2 f` are `C^∞` (genuine smooth order) on `(0,∞)`, for
`SmoothOpen f` and `θ ∈ (0,π/2)`. -/
theorem contDiffOn_divZ2_zslice_O {f : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen f)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    ContDiffOn ℝ Work.Stability.smoothOrder (fun z' => Work.Elliptic.divZ2 f z' θ)
      (Set.Ioi 0) :=
  Work.FTS.LocData.contDiffOn_slice_z (contDiffOn_divZ2_QO hsm) hθ

/-- The `z`-slices of `divZ2 f` are `C^∞` (genuine smooth order) at every `z > 0`. -/
theorem contDiffAt_divZ2_zslice_O {f : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen f)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    ∀ z : ℝ, 0 < z →
      ContDiffAt ℝ Work.Stability.smoothOrder (fun z' => Work.Elliptic.divZ2 f z' θ) z :=
  fun z hz => (contDiffOn_divZ2_zslice_O hsm hθ).contDiffAt (isOpen_Ioi.mem_nhds hz)

/-- The `z`-slices of the `D_θ`-iterates of `divZ2 f` are `C^∞` (genuine smooth order) on
`(0,∞)`, for `SmoothOpen f` and `θ ∈ (0,π/2)`. -/
theorem contDiffOn_DthIter_divZ2_zslice_O {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (i : ℕ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    ContDiffOn ℝ Work.Stability.smoothOrder
      (fun z' => Work.Spaces.DthIter i (Work.Elliptic.divZ2 f) z' θ) (Set.Ioi 0) :=
  Work.FTS.LocData.contDiffOn_slice_z
    (Work.FTS.LocData.contDiffOn_DthIter isOpen_QO (contDiffOn_divZ2_QO hsm) i) hθ

/-- The `z`-slices of the `D_θ`-iterates of `divZ2 f` are `C^∞` at every `z > 0`. -/
theorem contDiffAt_DthIter_divZ2_zslice_O {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (i : ℕ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    ∀ z : ℝ, 0 < z → ContDiffAt ℝ Work.Stability.smoothOrder
      (fun z' => Work.Spaces.DthIter i (Work.Elliptic.divZ2 f) z' θ) z :=
  fun z hz => (contDiffOn_DthIter_divZ2_zslice_O hsm i hθ).contDiffAt
    (isOpen_Ioi.mem_nhds hz)

/-! ## The Leibniz expansions of `∂_z^m f` through `f = z²·divZ2 f` -/

/-- `∂_z^m f = z² ∂_z^m κ + 2m z ∂_z^{m-1} κ + m(m-1) ∂_z^{m-2} κ` with
`κ = divZ2 f`, for `SmoothOpen f`, `z > 0` and `θ ∈ (0,π/2)`. -/
theorem pzIter_divZ2_expansion_aux_O {f : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen f)
    {m : ℕ} (hm : m ≤ 4) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.Spaces.pzIter m f z θ = z ^ 2 * Work.Spaces.pzIter m (Work.Elliptic.divZ2 f) z θ
      + (2 * (m : ℝ)) * z * Work.Spaces.pzIter (m - 1) (Work.Elliptic.divZ2 f) z θ
      + ((m : ℝ) * ((m : ℝ) - 1))
          * Work.Spaces.pzIter (m - 2) (Work.Elliptic.divZ2 f) z θ := by
  have hκ : ContDiffAt ℝ Work.Stability.smoothOrder
      (fun z' => Work.Elliptic.divZ2 f z' θ) z :=
    contDiffAt_divZ2_zslice_O hsm hθ z hz
  have hcongr : Work.Spaces.pzIter m f z θ
      = Work.Spaces.pzIter m (fun z θ => z ^ 2 * Work.Elliptic.divZ2 f z θ) z θ := by
    refine Work.Elliptic.pzIter_congr_nhds m ?_
    filter_upwards [IsOpen.mem_nhds isOpen_Ioi hz] with z' hz'
    exact Work.Elliptic.divZ2_eq_mul (ne_of_gt hz')
  rw [hcongr, Work.FTS.H2.Q.pzIter_sq_mul_sm m hm hκ]

/-- `∂_z^l D_θ^i f = z² ∂_z^l κ + 2l z ∂_z^{l-1}κ + l(l-1) ∂_z^{l-2}κ` with
`κ = D_θ^i (divZ2 f)`, for `SmoothOpen f`, `z > 0`, `θ ∈ (0,π/2)` and `l ≤ 4`. -/
theorem expand_aux_O {f : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen f) (i l : ℕ)
    (hl : l ≤ 4) {z : ℝ} (hz : 0 < z) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.Spaces.pzIter l (Work.Spaces.DthIter i f) z θ
      = z ^ 2 * Work.Spaces.pzIter l (Work.Spaces.DthIter i (Work.Elliptic.divZ2 f)) z θ
        + (2 * (l : ℝ)) * z
            * Work.Spaces.pzIter (l - 1) (Work.Spaces.DthIter i (Work.Elliptic.divZ2 f)) z θ
        + ((l : ℝ) * ((l : ℝ) - 1))
            * Work.Spaces.pzIter (l - 2) (Work.Spaces.DthIter i (Work.Elliptic.divZ2 f)) z θ := by
  have hκ : ContDiffAt ℝ Work.Stability.smoothOrder
      (fun z' => Work.Spaces.DthIter i (Work.Elliptic.divZ2 f) z' θ) z :=
    contDiffAt_DthIter_divZ2_zslice_O hsm i hθ z hz
  have hmemIoi : Set.Ioi (0 : ℝ) ∈ 𝓝 z :=
    isOpen_Ioi.mem_nhds (by simp only [Set.mem_Ioi]; exact hz)
  have hev : ∀ᶠ z' in 𝓝 z, ∀ θ' : ℝ,
      Work.Spaces.DthIter i f z' θ' = z' ^ 2 * Work.Spaces.DthIter i (Work.Elliptic.divZ2 f) z' θ' := by
    filter_upwards [hmemIoi] with z' hz' θ'
    exact Work.Elliptic.DthIter_divZ2_eq i (ne_of_gt hz')
  rw [Work.Elliptic.pzIter_congr_of_eventually (u := Work.Spaces.DthIter i f)
    (v := fun z θ => z ^ 2 * Work.Spaces.DthIter i (Work.Elliptic.divZ2 f) z θ)
    (z := z) (θ := θ) l hev]
  exact Work.FTS.H2.Q.pzIter_sq_mul_sm l hl hκ

/-! ## The triangular estimate for `D_θ^i (divZ2 f)` -/

/-- The triangular estimate of `tri_aux_sm`, in the open-quadrant class `SmoothOpen`: the
`𝒲^{4,∞}`-bounds on `(z+1)^j ∂_z^j D_θ^i ((z+1)³/z²·f)` give
`|(z+1)^{j+3} ∂_z^j D_θ^i (divZ2 f)| ≤ 6000·Λ` for `j ≤ l`. -/
theorem tri_aux_O {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f)
    (hmem : Work.Spaces.WlInfMem α 4 (fun z θ => (z + 1) ^ 3 / z ^ 2 * f z θ))
    {i l : ℕ} (hi : 1 ≤ i) (hli : l + i ≤ 4) {z : ℝ} (hz : 0 < z) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hGev : ∀ z' : ℝ, 0 < z' → ∀ θ' : ℝ,
      Work.Spaces.DthIter i (fun z θ => (z + 1) ^ 3 / z ^ 2 * f z θ) z' θ'
        = (z' + 1) ^ 3 * Work.Spaces.DthIter i (Work.Elliptic.divZ2 f) z' θ') :
    ∀ j ≤ l, |(z + 1) ^ (j + 3) * Work.Spaces.pzIter j (Work.Spaces.DthIter i (Work.Elliptic.divZ2 f)) z θ|
      ≤ 6000 * (Work.Spaces.WlInf α 4 (fun z θ => (z + 1) ^ 3 / z ^ 2 * f z θ)
          * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) := by
  set Λ : ℝ := Work.Spaces.WlInf α 4 (fun z θ => (z + 1) ^ 3 / z ^ 2 * f z θ)
      * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) with hΛ
  have hmemIoi : Set.Ioi (0 : ℝ) ∈ 𝓝 z :=
    isOpen_Ioi.mem_nhds (by simp only [Set.mem_Ioi]; linarith)
  have hev : ∀ᶠ z' in 𝓝 z, ∀ θ' : ℝ,
      Work.Spaces.DthIter i (fun z θ => (z + 1) ^ 3 / z ^ 2 * f z θ) z' θ'
        = (z' + 1) ^ 3 * Work.Spaces.DthIter i (Work.Elliptic.divZ2 f) z' θ' := by
    filter_upwards [hmemIoi] with z' hz' θ'
    exact hGev z' hz' θ'
  have hbound : ∀ j ≤ l,
      |(z + 1) ^ j * Work.Spaces.pzIter j
        (fun z θ => (z + 1) ^ 3 * Work.Spaces.DthIter i (Work.Elliptic.divZ2 f) z θ) z θ| ≤ Λ := by
    intro j hj
    have hji : j + i ≤ 4 := by omega
    have h1 := Work.Spaces.factor_bound α hα (fun z θ => (z + 1) ^ 3 / z ^ 2 * f z θ)
      hmem j i (by omega) (fun _ => hji) z θ (le_of_lt hz)
      ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    rw [if_neg (by omega : ¬ (i = 0))] at h1
    have hEq : Work.Spaces.pzIter j
          (fun z θ => (z + 1) ^ 3 * Work.Spaces.DthIter i (Work.Elliptic.divZ2 f) z θ) z θ
        = Work.Spaces.pzIter j
          (Work.Spaces.DthIter i (fun z θ => (z + 1) ^ 3 / z ^ 2 * f z θ)) z θ :=
      (Work.Elliptic.pzIter_congr_of_eventually
        (u := Work.Spaces.DthIter i (fun z θ => (z + 1) ^ 3 / z ^ 2 * f z θ))
        (v := fun z θ => (z + 1) ^ 3 * Work.Spaces.DthIter i (Work.Elliptic.divZ2 f) z θ)
        (z := z) (θ := θ) j hev).symm
    rw [hEq, hΛ]
    exact h1
  have hκ : ContDiffAt ℝ Work.Stability.smoothOrder
      (fun z' => Work.Spaces.DthIter i (Work.Elliptic.divZ2 f) z' θ) z :=
    contDiffAt_DthIter_divZ2_zslice_O hsm i hθ z hz
  have hmain : ∀ j ≤ l,
      |(z + 1) ^ (j + 3) * Work.Spaces.pzIter j (Work.Spaces.DthIter i (Work.Elliptic.divZ2 f)) z θ|
        ≤ 6000 * Λ :=
    Work.FTS.H2.Q.tri_bound_sm
      (G := fun z θ => (z + 1) ^ 3 * Work.Spaces.DthIter i (Work.Elliptic.divZ2 f) z θ)
      (κ := Work.Spaces.DthIter i (Work.Elliptic.divZ2 f)) rfl (by omega) hz hκ hbound
  intro j hj
  have hj' := hmain j hj
  rw [hΛ] at hj'
  exact hj'

end Work.FTS.NonlinRows
