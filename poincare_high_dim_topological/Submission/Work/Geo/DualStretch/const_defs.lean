/-
A6 `Geo/DualStretch` — bookkeeping for the stretch with a *constant* rescaling factor.

`Work.Geo.DualStretch.stretchM β p P hP (fun _ => m) x` rescales the high mass of `x` by the
constant `m > 0` and renormalises.  This file fixes the two quantities that describe the rescaled
mass decomposition, exactly as `denOf`/`wtOf` do for the taper `taperM`:

* `denC β p P hP m x = 1 + (m - 1) * SOf x` : the renormalisation factor;
* `wtC β p P hP m x τ` : the rescaled mass of the level set `τ`, i.e. `massG x τ / denC` on the low
  side and `m * massG x τ / denC` on the high side.

The point of the constant version is that the *inverse* stretch of a point `y` is
`stretchM β p P hP (fun z => (taperM … z)⁻¹) y = stretchM β p P hP (fun _ => (taperM … y)⁻¹) y`,
i.e. a constant-factor stretch at `y`; its bookkeeping (membership of the image in `P.space`,
positivity and normalisation of the rescaled weights, transformation of `SOf`, `AOf`, `BOf` and of
the join segment) is what the right inverse law needs.
-/
import Mathlib
import Submission.Work.Geo.DualStretch.Defs
import Submission.Work.Geo.DualStretch.Basic
import Submission.Work.Geo.DualStretch.massG_api

open Set Metric
open scoped Classical

namespace Work.Geo.DualStretch

open _root_.PL (E Cx)

variable {n : ℕ}

/-- The renormalisation factor `1 + (m - 1) * S(x)` of the stretch with constant factor `m`. -/
noncomputable def denC (β : ℝ) (p : ℕ) (P : Cx n) (hP : P.faces.Finite) (m : ℝ) (x : E n) : ℝ :=
  1 + (m - 1) * SOf β p P hP x

/-- The mass of the level set `τ` after rescaling the high mass by the constant `m` and
renormalising by `denC`. -/
noncomputable def wtC (β : ℝ) (p : ℕ) (P : Cx n) (hP : P.faces.Finite) (m : ℝ) (x : E n)
    (τ : Finset (E n)) : ℝ :=
  (if LowFace β p τ then (1 : ℝ) else m) * massG P hP x τ / denC β p P hP m x

end Work.Geo.DualStretch
