import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.ZMod.ValMinAbs
import Submission.Work.BoseK15.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseB7AK.LatBox.Defs` — the concrete truncated dual-lattice box

The §10 chapter's interface (`Work.BoseB7AK.Q3KernelG`, `Work.BoseK15.Q3Kernel'`)
is stated for an abstract finite `AddCommGroup Mode` and an injective momentum map
`kmom : Mode → ℝ³`.  This module fixes the **concrete** box model on which the two
guarded label additivities (`kmom_add`, `kmom_add_inner`) can be *proved*:

    `Mode := Fin 3 → ZMod n`   (`n` odd, so that the group has no element of order 2),
    `kmom i := ℓ⁻¹ • (2π · c (i μ))_μ`,   `c := ZMod.valMinAbs`,

i.e. the representative of each momentum coordinate with the smallest absolute
value (`ZMod.valMinAbs`, values in `[-n/2, n/2]`).

Why the wrap-around is a *theorem* here rather than a hypothesis: `ZMod.valMinAbs`
is a *section* of the quotient `ℤ → ZMod n`, not a homomorphism, so
`kmom (i - j) = kmom i - kmom j` holds exactly when the *difference of the
representatives* still lies in the fundamental domain `(-n/2, n/2]` — i.e. when
the momentum difference does not wrap.  `Work.BoseB7AK.LatBox.kmom_rows` proves

* `kmom (-i) = -kmom i` (odd `n`), injectivity, `OnDualLattice ℓ kmom`;
* the additivity at a pair whenever the representatives satisfy the no-wrap
  condition `(c i_μ − c j_μ)·2 ∈ Ioc (−n) n`;
* its clean sufficient form: if the two indices have representatives bounded by
  `C₁`, `C₂` with `2(C₁ + C₂) ≤ n`, the additivity holds.

The last form is what the honest box needs: at FS's parameters the localised
indices `s` (`f_L s ≠ 0`) have `‖kmom s‖ ≤ K_L√(μa)`, i.e. representatives bounded
by `C₁ = K_L√(μa)·ℓ/(2π)`, while the high indices `k ∈ P_H` run up to the UV
cutoff.  Hence the two guarded additivities hold at the concrete box **provided
the high indices used are at least `C₁` inside the lattice range** — which is
exactly the condition under which the truncated box model matches FS's own
(where the mode set is the *truncated* lattice and no wrap occurs).
`Work.BoseB7AK.LatBox.valMinAbs_sub_not_add` records that the condition cannot be
dropped: the section is *not* additive at the boundary.
-/

noncomputable section

open scoped BigOperators Pointwise
open MeasureTheory Classical

namespace Work.BoseB7AK.LatBox

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- **The concrete box momentum map**: each coordinate of `i` is sent to its
smallest-absolute-value representative times `2π/ℓ`.  This is
`ℓ⁻¹ • Work.BoseB4.vec (fun μ => (i μ).valMinAbs)`. -/
def kmom (n : ℕ) (ℓ : ℝ) (i : Fin 3 → ZMod n) : ℝ³ :=
  WithLp.toLp 2 (fun μ : Fin 3 => ℓ⁻¹ * (2 * Real.pi * (((i μ).valMinAbs : ℤ) : ℝ)))

@[simp] lemma kmom_apply (n : ℕ) (ℓ : ℝ) (i : Fin 3 → ZMod n) (μ : Fin 3) :
    kmom n ℓ i μ = ℓ⁻¹ * (2 * Real.pi * (((i μ).valMinAbs : ℤ) : ℝ)) := rfl

end Work.BoseB7AK.LatBox
