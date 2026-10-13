import Mathlib.Analysis.Normed.Field.Basic
import Submission.Work.FTS_RegExport.RXT.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.Sys.PullDefs` — the pulled-back unknown `φ = w/ω` and its coefficients

This is the (self-contained) interface used by `weighted_integrated_mp` (T5c of the RX-St1 leaf
plan) in the logarithmic coordinates `s = log z`, `ψ = log tan θ` of
`Work.FTS_RegExport.RXT.Defs`.

Only the *hypotheses* of T5c are used (continuity of `w`, the two partial-derivative relations
`D_z w = wz/z`, `D_θ w = wθ/sin 2θ` with *continuous* `wz`, `wθ`, and the integral identity),
so everything here is stated in terms of `wz`, `wθ` directly (no `C¹` on the slab is assumed).

The pulled-back unknown is `pw α w s ψ τ = w (eˢ) (arctan e^ψ) τ / om α s ψ` with
`om α s ψ = ω α (eˢ) (arctan e^ψ)`.  Its derivatives are

* `pws α wz w  = ∂_sφ = wz/om − 2φ/(1+z)`   (`= dphi_s` of `RXT.Pullback`),
* `pwψ α wθ w  = ∂_ψφ = wθ/(2·om) − α·c2m(θ)·φ`   (`= dphi_ψ` of `RXT.Pullback`),

the second because `dθ/dψ = sin 2θ/2` and `∂_θw = wθ/sin 2θ`.

The coefficients of the pulled-back transport equation are
`coefA Vz = Vz`, `coefB b = 2b`, `coefC α Vz b = 2Vz/(1+z) + 2α·c2m(θ)·b`
(the original angular velocity being `Vθ = b·sin 2θ`), and the source is `srcF α R = R/om`;
the algebraic core is `pw_alg`.
-/

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_RegExport.RXT.Sys

open Work.FTS_RegExport.RXT (cz cth om)

set_option autoImplicit false

/-- The pulled-back unknown `φ = w/ω` in logarithmic coordinates. -/
def pw (α : ℝ) (w : ℝ → ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ → ℝ :=
  fun s ψ τ => w (cz s) (cth ψ) τ / om α s ψ

/-- The `s`-derivative `∂_sφ = wz/om − 2φ/(1+z)` of the pulled-back unknown. -/
def pws (α : ℝ) (wz : ℝ → ℝ → ℝ → ℝ) (w : ℝ → ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ → ℝ :=
  fun s ψ τ => wz (cz s) (cth ψ) τ / om α s ψ - 2 * pw α w s ψ τ / (1 + cz s)

/-- The `ψ`-derivative `∂_ψφ = wθ/(2·om) − α·c2m(θ)·φ` of the pulled-back unknown. -/
def pwψ (α : ℝ) (wθ : ℝ → ℝ → ℝ → ℝ) (w : ℝ → ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ → ℝ :=
  fun s ψ τ => wθ (cz s) (cth ψ) τ / (2 * om α s ψ)
    - pw α w s ψ τ * (α * Work.Construction.c2m (cth ψ))

/-- The source `R/om` of the pulled-back equation. -/
def srcF (α : ℝ) (R : ℝ → ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ → ℝ :=
  fun s ψ τ => R (cz s) (cth ψ) τ / om α s ψ

/-- The `s`-coefficient `a = Vz`. -/
def coefA (Vz : ℝ → ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ → ℝ := fun s ψ τ => Vz (cz s) (cth ψ) τ

/-- The `ψ`-coefficient `b = 2Vθ/sin 2θ = 2·(Vθ = b sin 2θ)`. -/
def coefB (Vθ : ℝ → ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ → ℝ := fun s ψ τ => 2 * Vθ (cz s) (cth ψ) τ

/-- The zero-order coefficient `c = 2Vz/(1+z) + 2α·c2m(θ)·b` (`b = Vθ/sin 2θ`). -/
def coefC (α : ℝ) (Vz Vθ : ℝ → ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ → ℝ :=
  fun s ψ τ => 2 * Vz (cz s) (cth ψ) τ / (1 + cz s)
    + α * Work.Construction.c2m (cth ψ) * (2 * Vθ (cz s) (cth ψ) τ)

/-- `pw` in terms of the numerator: `pw α w s ψ τ = w (cz s) (cth ψ) τ / om α s ψ`. -/
lemma pw_apply (α : ℝ) (w : ℝ → ℝ → ℝ → ℝ) (s ψ τ : ℝ) :
    pw α w s ψ τ = w (cz s) (cth ψ) τ / om α s ψ := rfl

/-- **The algebraic core of the pull-back**: dividing the original equation
`∂_τw = R − (Vz·wz + b·wθ)` by `om = ω(cz s, cth ψ)` produces the pulled-back transport
equation with coefficients `coefA Vz`, `coefB b`, `coefC α Vz b` and source `srcF α R`. -/
lemma pw_alg {α : ℝ} (hα : 0 < α) {Vz b R w wz wθ : ℝ → ℝ → ℝ → ℝ} {s ψ τ : ℝ} :
    (R (cz s) (cth ψ) τ - (Vz (cz s) (cth ψ) τ * wz (cz s) (cth ψ) τ
        + b (cz s) (cth ψ) τ * wθ (cz s) (cth ψ) τ)) / om α s ψ
      = srcF α R s ψ τ
        - (coefA Vz s ψ τ * pws α wz w s ψ τ + coefB b s ψ τ * pwψ α wθ w s ψ τ
          + coefC α Vz b s ψ τ * pw α w s ψ τ) := by
  have h1 : (1 + cz s) ≠ 0 := by have := Work.FTS_RegExport.RXT.cz_pos s; positivity
  have h2 : om α s ψ ≠ 0 :=
    ne_of_gt (Work.FTS_RegExport.RXT.om_pos (α := α) hα)
  have h3 : om α s ψ * om α s ψ ≠ 0 := mul_ne_zero h2 h2
  simp only [srcF, coefA, coefB, coefC, pws, pwψ, pw]
  field_simp
  ring

end Work.FTS_RegExport.RXT.Sys
