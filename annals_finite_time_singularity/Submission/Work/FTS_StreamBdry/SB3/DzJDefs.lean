/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Work.FTS_StreamBdry.SB3.DzJDefs` — the scaled parameter integral `J`

The level-0 representation of the stream function (SB1) expresses the `U`-slot part of `Ψ` as

  `psiP αG Ψ z θ = -(s2 θ / αG) · ∫_0^1 v^{3/αG-1} · U'(Ψ)(z v, θ) dv`,

i.e. as a *scaled parameter integral*: the integrand is the derivative slot evaluated at the
dilated point `z v`.  The operator `D_z = z ∂_z` acts on the dilation parameter by the scaling
identity

  `D_z (fun z θ => ∫_0^1 v^c g (z v) θ dv) = fun z θ => ∫_0^1 v^c Dz g (z v) θ dv`,

which is the statement `Work.FTS_StreamBdry.SB3.Dz_J_eq` (in `DzJ.lean`).  It is the tool that
turns the vertical derivatives of `psiP` into the vertical derivatives of the slot `U'(Ψ)`
(SB3 / `Work.FTS_StreamBdry.DzIterIint`).

This module only fixes the vocabulary (`J`) and the elementary slice facts; the substantive
lemma lives in `DzJ.lean`.
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS_StreamBdry.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_StreamBdry.SB3

open Work.FTS.StreamBdryIface (Uprime SlotBd)

set_option autoImplicit false

/-- **The scaled parameter integral** `J c g z θ = ∫_0^1 v^c · g (z v, θ) dv`. -/
def J (c : ℝ) (g : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => ∫ v in (0 : ℝ)..1, v ^ c * g (z * v) θ

@[simp] lemma J_apply (c : ℝ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    J c g z θ = ∫ v in (0 : ℝ)..1, v ^ c * g (z * v) θ := rfl

/-- `Iint` *is* the scaled parameter integral of the slot `U'(Ψ)` at `c = 3/αG - 1`. -/
lemma Iint_eq_J (αG : ℝ) (Ψ : ℝ → ℝ → ℝ) :
    Iint αG Ψ = J (3 / αG - 1) (Uprime αG Ψ) := rfl

/-- The open quadrant is open. -/
theorem isOpen_Qd : IsOpen Work.Construction.Qd := isOpen_Ioi.prod isOpen_Ioo

/-- **Slice continuity of a scaled slice.**  If `g` is jointly continuous on the open quadrant,
then for `x > 0` and `θ ∈ (0,π/2)` the `v`-slice `v ↦ g (x v, θ)` is continuous on `(0,∞)`.
(Every point `(x v, θ)` with `v > 0` lies in the open quadrant, where `g` is continuous.) -/
theorem continuousOn_scaled_slice {g : ℝ → ℝ → ℝ}
    (hg : ContinuousOn (Function.uncurry g) Work.Construction.Qd)
    {x : ℝ} (hx : 0 < x) {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) (π / 2)) :
    ContinuousOn (fun v => g (x * v) θ) (Ioi 0) := by
  have h1 : ContinuousOn (fun v : ℝ => (x * v, θ)) (Ioi 0) := by fun_prop
  have h2 := hg.comp h1 (fun v hv => ⟨mul_pos hx hv, hθ⟩)
  simpa [Function.comp_def, Function.uncurry] using h2

end Work.FTS_StreamBdry.SB3
