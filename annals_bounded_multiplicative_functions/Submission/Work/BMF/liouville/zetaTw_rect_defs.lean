import Mathlib
import Submission.Work.BMF.liouville.zeta_tw_perron
import Submission.Commons.NumberTheory.Zeta.psi_sub_id_powLog_real

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Shared definitions for the twisted principal-character Perron rectangle shift

The twisted Perron integrand is `zetaTwG u x w = -(ζ′/ζ)(w + iu)·x^w/w`.  It has a single
simple pole inside the rectangle `[σ₁, 1 + 1/log x] × [-T, T]` of the `w`-plane, located at
`w₀ = 1 - iu` (where `ζ(w + iu)` has its pole), with residue `x^{w₀}/w₀ = x^{1-iu}/(1-iu)`.

This file records, once and for all, the pole location `zetaTwPole`, the residue `zetaTwRes`,
the factor `zetaTwPhi w = x^w/w`, the principal part `zetaTwP` (i.e. `res/(w - w₀)`) and the
remainder `zetaTwH` after subtracting the principal part (written as an everywhere-defined
function using `dslope`, so that it is holomorphic at `w₀` as well).
-/

namespace Work.BMF.liouville

open Complex

noncomputable section

/-- The pole of the twisted Perron integrand `zetaTwG u x` in the `w`-plane: `w₀ = 1 - i·u`. -/
noncomputable def zetaTwPole (u : ℝ) : ℂ := 1 - Complex.I * (u : ℂ)

/-- The residue of `zetaTwG u x` at `w = zetaTwPole u`, namely `x^{1-iu}/(1-iu)`. -/
noncomputable def zetaTwRes (u x : ℝ) : ℂ := (x : ℂ) ^ zetaTwPole u / zetaTwPole u

/-- The factor `φ w = x^w/w` of the twisted Perron integrand. -/
noncomputable def zetaTwPhi (x : ℝ) (w : ℂ) : ℂ := (x : ℂ) ^ w / w

/-- The principal part `zetaTwRes u x / (w - zetaTwPole u)` of the twisted Perron integrand. -/
noncomputable def zetaTwP (u x : ℝ) (w : ℂ) : ℂ := zetaTwRes u x / (w - zetaTwPole u)

/-- The remainder of the twisted Perron integrand after subtracting its principal part, written
with a `dslope` so that it is defined (and holomorphic) also at `w = zetaTwPole u`:
`zetaTwH u x w = dslope (x^·/·) w₀ w - (x^w/w)·(ζ₁′/ζ₁)(w + iu)`. -/
noncomputable def zetaTwH (u x : ℝ) (w : ℂ) : ℂ :=
  dslope (zetaTwPhi x) (zetaTwPole u) w -
    zetaTwPhi x w * Commons.NumberTheory.Zeta.zeta1LogDeriv (w + (u : ℂ) * Complex.I)

end

end Work.BMF.liouville
