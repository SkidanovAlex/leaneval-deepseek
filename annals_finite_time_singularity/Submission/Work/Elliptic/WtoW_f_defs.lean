/-
Copyright: work module for the Elgindi finite-time singularity project.

# Shared definitions for the lemma `Work.Elliptic.WtoW_f_bound`

The lemma `WtoW_f_bound` bounds `(z+1)^c ∂_z^c D_θ^a f` by
`|∂_θ f|_{𝒲^{4,∞}} · sin(2θ)`.  Its proof writes `D_θ^a f` as
`D_θ^{a-1}(sin(2θ) · ∂_θ f)` and applies the Leibniz rule for `D_θ^{a-1}`; the
angular factor `sin(2θ)` is replaced by the explicit bounded function
`sin(2θ) · sigCoeff i θ`, where `D_θ^i (sin(2·)) = sin(2·) · sigCoeff i`.

This file only collects the definition of `sigCoeff`; the two facts about it
(the identity `D_θ^i (sin (2·)) = sin(2·) · sigCoeff i` for `i ≤ 3` and the bound
`|sigCoeff i| ≤ 48`) are proved as `Work.Elliptic.WtoW_f_DthIter_sin_two_eq` and
`Work.Elliptic.WtoW_f_sigCoeff_bound` in `Submission/Work/Elliptic/WtoW_f_bound.lean`.
-/
import Mathlib.Analysis.Complex.Trigonometric
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Elliptic

set_option autoImplicit false

/-- The bounded angular coefficient `γ_i` with `D_θ^i (sin (2·)) = sin(2·) · γ_i`:
`γ_0 = 1`, `γ_1 = 2 cos 2θ`, `γ_2 = 4(cos²2θ - sin²2θ)`,
`γ_3 = 8 cos³2θ - 40 sin²2θ cos 2θ` (and `γ_i = 0` for `i ≥ 4`, which never occurs
in the application since `a ≤ 4` so `i ≤ 3`). -/
noncomputable def sigCoeff : ℕ → ℝ → ℝ
  | 0 => fun _ => 1
  | 1 => fun θ => 2 * Real.cos (2 * θ)
  | 2 => fun θ => 4 * (Real.cos (2 * θ)) ^ 2 - 4 * (Real.sin (2 * θ)) ^ 2
  | 3 => fun θ => 8 * (Real.cos (2 * θ)) ^ 3
      - 40 * (Real.sin (2 * θ)) ^ 2 * Real.cos (2 * θ)
  | _ => fun _ => 0

end Work.Elliptic
