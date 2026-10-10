/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.MotK
-/
import Submission.Work.MotV.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The T-twist field for an *arbitrary* base field `K` and Kummer class `h`

`Work.MotV.twistFieldT` is the T-twist field of `D` at `h` for the specific base field
`K = RatFunc 𝕜` (the `S45` route over `𝔸¹_t`).  This file provides the same construction for an
arbitrary field `K` of characteristic `≠ 5` and an arbitrary `h ≠ 0` (lead addendum
`MOTIVIC_C6_R4_LEAD.md`): R4 needs it at a function field with `h = π` a uniformiser.

The construction is verbatim `Work.MotV`'s, with `AlgebraicClosure (RatFunc 𝕜)` replaced by
`AlgebraicClosure K`:

* `KbG K = AlgebraicClosure K`, `OmG D = Affine.FunctionField (D.E.baseChange (KbG K))`;
* `root5G h` is a fifth root of `h` in `KbG K` (`K` need not contain a fifth root of `h`);
* `twCoordG D h i = w^{-i}·κ_i/κ_0` are the twisted Klein coordinates;
* `twistFieldTG D h = K(y_0, …, y_4) ⊆ OmG D` is the T-twist field `K(C_h)`.
-/

set_option autoImplicit false
open WeierstrassCurve WeierstrassCurve.Affine

namespace Work.MotK

variable (K : Type*) [Field K]

/-- An algebraic closure of `K` (the analogue of `Work.MotV.Kb` for a general base field). -/
abbrev KbG : Type _ := AlgebraicClosure K

/-- The function field of `E` over `AlgebraicClosure K` (the analogue of `Work.MotV.Om`). -/
abbrev OmG (D : Work.MotV.KleinData K) : Type _ :=
  Affine.FunctionField (D.E.baseChange (KbG K))

/-- A fifth root of `h` in `AlgebraicClosure K`. -/
noncomputable def root5G (h : K) : KbG K :=
  Classical.choose (IsAlgClosed.exists_pow_nat_eq (algebraMap K (KbG K) h)
    (by norm_num : 0 < 5))

/-- The twisted Klein coordinates `y_i = w^{-i}·κ_i/κ_0`, `w^5 = h`. -/
noncomputable def twCoordG (D : Work.MotV.KleinData K) (h : K) (i : Fin 5) : OmG K D :=
  ((algebraMap (KbG K) (OmG K D) (root5G K h))⁻¹) ^ (i : ℕ) *
    (Work.MotV.kleinCoord D (KbG K) i / Work.MotV.kleinCoord D (KbG K) 0)

/-- **The T-twist field** `K(C_h)` for a general base field `K`: the subfield of `K̄(E)` generated
over `K` by the twisted Klein coordinates. -/
noncomputable def twistFieldTG (D : Work.MotV.KleinData K) (h : K) :
    IntermediateField K (OmG K D) :=
  IntermediateField.adjoin K (Set.range (twCoordG K D h))

end Work.MotK
