/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.MotK
-/
import Mathlib
import Submission.Work.MotK.TGen.ChartDefs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The six prime factors of the two divisor polynomials of the T-twisted link

The certificate `Work.MotK.LinkCertTGenInf` is taken with the two affine-chart divisors

  `Fdiv a b h = GambT a b h · f̂₄`,   `Gdiv a b h = FambT a b h · ǧ₄`

(`Work.MotK.TGen.Fdiv`, `Work.MotK.TGen.Gdiv`), where `GambT = kleinTwFhom p chart3` is the source
equation and `FambT = kleinTwGhomV p chart3` the target equation of the T-twisted Crauder--Katz
link at the `K`-point `p = kleinPointT a b h` and the affine chart `chart3`.

This file splits the two equations into their irreducible factors (the *census* factors); the
four clauses of `Work.MotK.TGenCensus` (`Submission/Work/MotK/LinkCertTGenInf.lean`) are the
statements that each of them is a height-one principal prime and that its residue field is the
expected one (a `RatFunc` of a twisted Klein function field, or the rational surface for the junk
factors).  See `GUIDE_CENSUS.md` in this directory for the routes.

* `linT = kleinTwBilin p chart3 = a·b·x₁ + a²·h·x₂` — junk (linear), **proved**
  (`TGen.JunkClassKleinTwBilinChart`);
* `sT = kleinTwS (kleinTwStereo p chart3)` (degree 10) — the source ruling divisor, class
  `RatFunc (twistFieldTG K D (h²))`;
* `cubT = kleinTwBilin p (kleinTwR chart3)` (cubic) — junk (a cone);
* `sdualT = kleinTwSDualV chart3` (quintic) — the target ruling divisor, class
  `RatFunc (twistFieldTG K D h)`;
* `bwVec a b h 4 = ǧ₄` (cubic) — junk, **proved** (`TGen.JunkClassBwVec4`);
* `fwVec a b h 4 = f̂₄` (quartic) — junk.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Work.MotK.TGen

open MvPolynomial

variable {K : Type*} [Field K]

/-- The **linear** factor `b(p, chart3) = a·b·x₁ + a²·h·x₂` of the source equation `GambT`. -/
noncomputable def linT (a b h : K) : MvPolynomial (Fin 3) K :=
  kleinTwBilin (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
    (pRa a b h) (chart3 K)

/-- The **degree-10** factor `s(y(v))` (`y = kleinTwStereo p`) of the source equation `GambT`:
the divisor of the source ruling, ruled over the residual curve `C' = Jac²(C)`. -/
noncomputable def sT (a b h : K) : MvPolynomial (Fin 3) K :=
  kleinTwS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
    (kleinTwStereo (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
      (pRa a b h) (chart3 K))

/-- The **cubic** factor `b(p, kleinTwR chart3)` of the target equation `FambT`: the cone
divisor of the target side. -/
noncomputable def cubT (a b h : K) : MvPolynomial (Fin 3) K :=
  kleinTwBilin (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h) (pRa a b h)
    (kleinTwR (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h) (chart3 K))

/-- The **quintic** factor `s'(chart3)` of the target equation `FambT`: the divisor of the target
ruling, ruled over the twisted Klein curve `C_h` itself. -/
noncomputable def sdualT (a b h : K) : MvPolynomial (Fin 3) K :=
  kleinTwSDualV (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h) (chart3 K)

/-- The source equation is the product of its two factors. -/
theorem GambT_eq (a b h : K) : GambT a b h = linT a b h * sT a b h := rfl

/-- The target equation is the product of its two factors. -/
theorem FambT_eq (a b h : K) : FambT a b h = cubT a b h * sdualT a b h := rfl

theorem Fdiv_eq (a b h : K) : Fdiv a b h = linT a b h * sT a b h * fwVec a b h 4 := by
  rw [Fdiv, GambT_eq]

theorem Gdiv_eq (a b h : K) : Gdiv a b h = cubT a b h * sdualT a b h * bwVec a b h 4 := by
  rw [Gdiv, FambT_eq]

end Work.MotK.TGen
