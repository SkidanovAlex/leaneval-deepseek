/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Unramifiedness at `w` is local unramifiedness of `L_w/K_v`

For a finite Galois extension `L/K` of number fields, a finite prime `w` of `L` lying over the
finite prime `v` of `K`, the global statement "`w` is unramified over `K`" (i.e. the inertia
subgroup `I_w` is trivial, equivalently the ramification index `e(w/v)` is `1`) is *equivalent*
to the local statement that the extension of local fields `L_w/K_v` is unramified, i.e.

`[κ_w : κ_v] = [L_w : K_v]`.

The substance is the comparison of the residue field degrees with the inertia degree:
`[κ_w : κ_v] = f(w/v) = v.asIdeal.inertiaDegIn (𝓞 L)` (proved below), together with the
fundamental identity `[L_w : K_v] = #D_w = e(w/v) · f(w/v)`.

## Main results

* `Work.LocalFields.finrank_residueFieldOf_eq_inertiaDegIn` :
  `[κ_w : κ_v] = v.asIdeal.inertiaDegIn (𝓞 L)`.
* `Work.LocalFields.isUnramifiedAt_iff_isUnramifiedLocalExtension`.
-/
import Mathlib
import Submission.Work.LocalFields.Basic
import Submission.Work.LocalFields.Decomposition
import Submission.Work.LocalFields.LocalExtension
import Submission.Work.LocalFields.finrank_completion_eq_card_decompositionGroup
import Submission.Work.LocalFields.isUnramifiedAt_iff_ramificationIdxIn_eq_one
import Submission.Work.LocalFields.CompletionLocalField

namespace Work.LocalFields

open scoped NumberField Valued WithZero

set_option linter.style.haveILetI false

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- **The residue field degree at the completions is the inertia degree.**

For a finite Galois extension `L/K` of number fields and a finite prime `w` of `L` lying over the
finite prime `v` of `K`, the degree of the residue field extension of the local extension
`L_w/K_v`, `[κ_w : κ_v] = finrank κ_v κ_w`, is the inertia degree `f(w/v)` of `w` over `v`.

Both sides are computed from the cardinality of the residue field, which is unchanged by
completion: `Nat.card κ_v = Nat.card (𝓞 K ⧸ v)` and `Nat.card κ_w = Nat.card (𝓞 L ⧸ w)`
(`Work.LocalFields.residueEquiv`), while
`Nat.card (𝓞 L ⧸ w) = Nat.card (𝓞 K ⧸ v) ^ f(w/v)`
(`Ideal.cardQuot_pow_inertiaDeg`, the localised fundamental identity) and
`Nat.card κ_w = Nat.card κ_v ^ [κ_w : κ_v]` (`Module.natCard_eq_pow_finrank`).  Since
`Nat.card κ_v > 1`, exponentiation with base `Nat.card κ_v` is injective. -/
theorem finrank_residueFieldOf_eq_inertiaDegIn (v : FinitePrime K) (w : FinitePrime L)
    [hw : w.asIdeal.LiesOver v.asIdeal] :
    Module.finrank (residueFieldOf K v) (residueFieldOf L w) = v.asIdeal.inertiaDegIn (𝓞 L) := by
  -- `κ_v = 𝓞 K ⧸ v` and `κ_w = 𝓞 L ⧸ w`, as far as cardinalities are concerned.
  have hcf : Nat.card (residueFieldOf K v) = Nat.card (𝓞 K ⧸ v.asIdeal) :=
    (Nat.card_congr (residueEquiv v).toEquiv).symm
  have hcf' : Nat.card (residueFieldOf L w) = Nat.card (𝓞 L ⧸ w.asIdeal) :=
    (Nat.card_congr (residueEquiv w).toEquiv).symm
  -- `#κ_w = #κ_v ^ [κ_w : κ_v]`.
  have hfin : Nat.card (residueFieldOf L w) =
      Nat.card (residueFieldOf K v) ^
        Module.finrank (residueFieldOf K v) (residueFieldOf L w) :=
    Module.natCard_eq_pow_finrank
  -- `#(𝓞 L ⧸ w) = #(𝓞 K ⧸ v) ^ f(w/v)`.
  have hglobal : Nat.card (𝓞 K ⧸ v.asIdeal) ^ w.asIdeal.inertiaDeg (𝓞 K) =
      Nat.card (𝓞 L ⧸ w.asIdeal) := by
    haveI : Module.Finite (𝓞 K) (𝓞 L) := IsIntegralClosure.finite (𝓞 K) K L (𝓞 L)
    rw [← Submodule.cardQuot_apply, ← Submodule.cardQuot_apply]
    exact Ideal.cardQuot_pow_inertiaDeg v.asIdeal w.asIdeal
  have hge : 2 ≤ Nat.card (residueFieldOf K v) := by
    rw [natCard_residueFieldOf v]; exact one_lt_residueCard
  -- Compare the exponents of `#κ_v`.
  have key : Module.finrank (residueFieldOf K v) (residueFieldOf L w) =
      w.asIdeal.inertiaDeg (𝓞 K) := by
    apply Nat.pow_right_injective hge
    change Nat.card (residueFieldOf K v) ^
        Module.finrank (residueFieldOf K v) (residueFieldOf L w) =
      Nat.card (residueFieldOf K v) ^ w.asIdeal.inertiaDeg (𝓞 K)
    rw [← hfin, hcf', ← hglobal, ← hcf]
  rw [key, Ideal.inertiaDegIn_eq_inertiaDeg v.asIdeal w.asIdeal Gal(L/K)]

/-- **Unramifiedness is a local condition.**

For a finite Galois extension `L/K` of number fields, a finite prime `w` of `L` lying over the
finite prime `v` of `K`, the prime `w` is unramified over `K` (equivalently its inertia subgroup
`I_w` is trivial, equivalently `e(w/v) = 1`) if and only if the local extension `L_w/K_v` is
unramified, i.e. `[κ_w : κ_v] = [L_w : K_v]`.

Indeed `IsUnramifiedAt K w ↔ e(w/v) = 1`
(`Work.LocalFields.isUnramifiedAt_iff_ramificationIdxIn_eq_one`), while the fundamental identity of
ramification theory gives `[L_w : K_v] = #D_w = e(w/v) · f(w/v)`
(`Work.LocalFields.finrank_completion_eq_card_decompositionGroup`,
`Work.LocalFields.card_decompositionGroup`) and `[κ_w : κ_v] = f(w/v)`
(`Work.LocalFields.finrank_residueFieldOf_eq_inertiaDegIn`).  Since `f(w/v) ≠ 0`, the equation
`f(w/v) = e(w/v) · f(w/v)` is equivalent to `e(w/v) = 1`. -/
theorem isUnramifiedAt_iff_isUnramifiedLocalExtension {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (v : Work.LocalFields.FinitePrime K) (w : Work.LocalFields.FinitePrime L)
    [hw : w.asIdeal.LiesOver v.asIdeal] :
    Work.LocalFields.IsUnramifiedAt K w ↔
      Work.LocalFields.IsUnramifiedLocalExtension
        (Work.LocalFields.Completion K v) (Work.LocalFields.Completion L w) := by
  rw [isUnramifiedAt_iff_ramificationIdxIn_eq_one v w]
  -- `[κ_w : κ_v] = f(w/v)`.
  have hres : Module.finrank (residueFieldOf K v) (residueFieldOf L w) =
      v.asIdeal.inertiaDegIn (𝓞 L) :=
    finrank_residueFieldOf_eq_inertiaDegIn v w
  -- `[L_w : K_v] = e(w/v) · f(w/v)`.
  have hcomp : Module.finrank (Completion K v) (Completion L w) =
      v.asIdeal.ramificationIdxIn (𝓞 L) * v.asIdeal.inertiaDegIn (𝓞 L) := by
    rw [finrank_completion_eq_card_decompositionGroup v w, card_decompositionGroup v w]
  have hf : 0 < v.asIdeal.inertiaDegIn (𝓞 L) := by
    haveI : Module.Finite (𝓞 K) (𝓞 L) := IsIntegralClosure.finite (𝓞 K) K L (𝓞 L)
    exact Nat.pos_of_ne_zero (Ideal.inertiaDegIn_ne_zero Gal(L/K))
  unfold IsUnramifiedLocalExtension
  rw [hres, hcomp]
  constructor
  · intro h; rw [h, one_mul]
  · intro h; exact Nat.eq_of_mul_eq_mul_right hf (by rw [one_mul]; exact h.symm)

end Work.LocalFields
