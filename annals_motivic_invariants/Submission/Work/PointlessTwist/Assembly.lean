/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.PointlessTwist
-/
import Mathlib
import ChallengeDeps
import Submission.Work.PointlessTwist.Constants
import Submission.Work.PointlessTwist.Constants.nonempty_constantTateData
import Submission.Work.PointlessTwist.bridge.trivialGaloisAction_of_constantsOnly

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The arithmetic half of `PointlessTwistData`, per field class

This file names, for each of the four field classes of Lin–Shinder Theorem 1.2 (1) (a)–(d), the
**residual** of the pointless-twist arithmetic at a **concrete** choice of the data
`(C₅ : FiveTorsionCurve 𝕜, L : CyclicExtension 𝕜 5)`, and proves that the residual gives
`HasPointlessTwist 𝕜` — the arithmetic half of `Work.Twist.PointlessTwistData 𝕜`.

The residuals are, per class:

| class | `𝕜` | `(C₅, L)` | residual | why this is the residual |
|---|---|---|---|---|
| (a) number fields | `ℚ` (or any number field `𝕜`) | Tate normal form over `𝕜`; `L` the degree-`5` subfield of `𝕜(ζ_{5^k})` (`existsCyclicExtension_numberField`) | `NumberFieldResidual 𝕜` | the place `v ∣ 5` is totally ramified in `L/𝕜` with residue degree `1`, `E` has good reduction at `v` and `P = (0,0)` reduces to a point of order `5` of `Ẽ(κ_v)`; the reduction map on points is `σ`-invariant (Silverman *AEC* VII.2.1–2.2) |
| (b) function fields over a number field | `ℚ(ζ₅)(t)` | constant Tate normal form with `c ∈ ℚ(ζ₅)` (`ConstantTateData 𝔽 (RatFunc 𝔽) c`); `L = 𝔽(s)`, `s ^ 5 = t` (Kummer, `existsCyclicExtension_of_zeta5` + `Kummer.not_exists_pow_five_eq_X`) | `KummerResidual 𝔽` | for the *constant* curve, `E(𝔽(s)) = E(𝔽)` (no non-constant `ℙ¹ → E`), so `σ` acts trivially on `E(L)` |
| (c) function fields over a finite field | `𝔽₁₁(t)` (`5 ∣ 11 - 1`) | same (`c ∈ 𝔽₁₁`) | `KummerResidual 𝔽₁₁` | same |
| (d) function fields over an algebraically closed field | `ℂ(t)` | same (`c ∈ ℂ`) | `KummerResidual ℂ` | same — the paper's route (iii) |

For (b)–(d) the residual `KummerResidual 𝔽` is a *true* statement (it is the classical
`E(𝔽(s)) = E(𝔽)`) which is strictly stronger than `PointlessOf`; for (a) `NumberFieldResidual 𝕜`
is *equivalent* to `PointlessOf` at its data, because any obstruction can be replaced by the
tautological one (`hasInvariantObstruction_iff_pointless`).  In every case the missing input is a
theorem of Silverman, *AEC*, VII.2.1 (the reduction map on the points of a Weierstrass curve over a
discretely valued field) — see `NOTES.md` §"the exact gap".

## Main results

* `NumberFieldResidual 𝕜`, `KummerResidual 𝔽` — the two residuals.
* `hasPointlessTwist_of_numberFieldResidual`, `hasPointlessTwist_of_kummerResidual` — the
  residuals give `HasPointlessTwist` at the concrete data.
* `Residual_numberField`, `Residual_functionField_numberField`, `Residual_functionField_finite`,
  `Residual_functionField_algClosed` — the residuals at the four concrete fields.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

open WeierstrassCurve WeierstrassCurve.Affine

namespace Work.PointlessTwist

noncomputable section

/-! ## 1. The number-field residual (class (a)) -/

/-- **The residual of the number-field class.**  At a number field `𝕜`, a quintic twist whose class
is detected by a **place**: a `ReductionPlace` (an additive, `σ`-invariant map out of `E(L)` which
does not kill `P`), i.e. the reduction map at a place `v` of `𝕜` at which `L/𝕜` is totally ramified
with residue degree `1` and `E` has good reduction with `P` reducing to a point of order `5`.

At the concrete data of the class — the Tate normal form over `𝕜` and `L` the degree-`5` cyclic
subfield of `𝕜(ζ_{5^k})`, which is totally ramified at `5` — this is Silverman, *AEC*, VII.2.1–2.2.

For fixed data the residual is *equivalent* to `PointlessOf` (`hasInvariantObstruction_iff_pointless`);
what the equivalence does not give is that the obstruction comes from a place, which is the form in
which it can be proved. -/
def NumberFieldResidual (𝕜 : Type) [Field 𝕜] [DecidableEq 𝕜] [NumberField 𝕜] : Prop :=
  ∃ (C₅ : FiveTorsionCurve 𝕜) (L : CyclicExtension 𝕜 5), HasReductionPlace (twistOf C₅ L)

/-- **The number-field residual gives the arithmetic half.** -/
theorem hasPointlessTwist_of_numberFieldResidual {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]
    [NumberField 𝕜] (h : NumberFieldResidual 𝕜) : HasPointlessTwist 𝕜 := by
  obtain ⟨C₅, L, hD⟩ := h
  exact hasPointlessTwist_of_pointlessOf C₅ L (pointlessOf_of_hasReductionPlace C₅ L hD)

/-- The number-field residual is the local-obstruction form of the parent chapter's residual
(`Work.Twist.HasPointlessTwistByObstruction 𝕜`) for a fixed pair `(C₅, L)`. -/
theorem hasPointlessTwistByObstruction_of_numberFieldResidual {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]
    [NumberField 𝕜] (h : NumberFieldResidual 𝕜) :
    Work.Twist.HasPointlessTwistByObstruction 𝕜 := by
  obtain ⟨C₅, L, hD⟩ := h
  obtain ⟨r⟩ := hD
  exact ⟨twistOf C₅ L, ⟨
    { G := r.G
      addCommGroup := r.addCommGroup
      toFun := r.red
      map_PL := r.red_PL_ne_zero
      map_shift := fun R => by rw [map_sub, r.red_galMap R, sub_self] }⟩⟩

/-- **The residual of class (a) at `ℚ`** (the smallest number field): the place-`5` local
obstruction for the Tate normal form over `ℚ` and the degree-`5` cyclic subfield of `ℚ(ζ_{25})`. -/
abbrev Residual_numberField : Prop := NumberFieldResidual ℚ

/-! ## 2. The function-field residual (classes (b), (c), (d)) -/

/-- **The residual of the function-field classes.**  At the concrete data over the field of
constants `𝔽`:

* `𝕜 = 𝔽(t) = RatFunc 𝔽`, `L = 𝔽(s)` with `s ^ 5 = t` the Kummer extension
  (`existsCyclicExtension_of_zeta5`, whose input `t ∉ 𝕜 ^ 5` is
  `Work.PointlessTwist.Kummer.not_exists_pow_five_eq_X`);
* `C₅` the **constant** Tate normal form with a good parameter `c ∈ 𝔽` (`ConstantTateData`);

the generator `σ ∈ Gal(L/𝕜)` acts **trivially** on `E(L)`.  This is the classical
`E(𝔽(s)) = E(𝔽)` (a `𝔽(s)`-point of a constant curve is a morphism `ℙ¹ → E`, and there is no
non-constant one); it is the paper's route (iii).

The residual is a true statement which is *strictly stronger* than `PointlessOf` at its data. -/
def KummerResidual (𝔽 : Type) [Field 𝔽] [DecidableEq 𝔽] [DecidableEq (RatFunc 𝔽)] : Prop :=
  ∃ (c : 𝔽), (Work.TorsorExistence.Tate.tateCurve c).Δ ≠ 0 ∧
    (Work.TorsorExistence.Tate.tateCurve c).c₄ ^ 3
      ≠ 1728 * (Work.TorsorExistence.Tate.tateCurve c).Δ ∧
    ∃ (d : ConstantTateData 𝔽 (RatFunc 𝔽) c) (L : CyclicExtension (RatFunc 𝔽) 5),
      TrivialGaloisAction d.C₅ L

/-- **The function-field residual gives the arithmetic half** (at `𝕜 = RatFunc 𝔽`). -/
theorem hasPointlessTwist_of_kummerResidual {𝔽 : Type} [Field 𝔽] [DecidableEq 𝔽]
    [DecidableEq (RatFunc 𝔽)] (h : KummerResidual 𝔽) : HasPointlessTwist (RatFunc 𝔽) := by
  obtain ⟨c, _hΔ, _hj, d, L, hL⟩ := h
  exact hasPointlessTwist_of_pointlessOf d.C₅ L (pointlessOf_of_trivialGaloisAction d.C₅ L hL)

/-! ## 3. The sharp residual of the function-field classes: `ConstantsOnly` at the concrete data

The residual `KummerResidual 𝔽` above is stated with `TrivialGaloisAction`, which is *equivalent* at
the fixed concrete data to `ConstantsOnly` (the classical `E(𝔽(s)) = E(𝔽)`) by
`bridge.trivialGaloisAction_of_constantsOnly` — **proved** (delegated, `Work.PointlessTwist.bridge`).
Here is the sharp form, stated directly in terms of `ConstantsOnly`, with the whole chain to
`HasPointlessTwist` closed. -/

/-- **The sharp residual of the function-field classes.**  At the concrete data over the field of
constants `𝔽` — a good Tate parameter `c ∈ 𝔽`, the constant Tate model over `𝕜 = 𝔽(t)`, the Kummer
extension `L = 𝔽(s)` with `s ^ 5 = t` — the *classical* statement `E(𝔽(s)) = E(𝔽)` for the constant
curve `Tate.tateCurve c` (`ConstantsOnly`).

This is the sharpest form of the residual of classes (b)–(d): it names the concrete curve, the
concrete extension and the classical theorem, and the whole chain to `HasPointlessTwist 𝕜` is proved
(`hasPointlessTwist_of_kummerResidualSharp`). -/
structure KummerResidualSharp (𝔽 : Type) [Field 𝔽] [DecidableEq 𝔽] [DecidableEq (RatFunc 𝔽)] where
  /-- The parameter of the Tate normal form, in the field of constants. -/
  c : 𝔽
  /-- The Tate normal form is nonsingular. -/
  hΔ : (Work.TorsorExistence.Tate.tateCurve c).Δ ≠ 0
  /-- Its `j`-invariant is `≠ 1728` (characteristic-free form). -/
  hj : (Work.TorsorExistence.Tate.tateCurve c).c₄ ^ 3
    ≠ 1728 * (Work.TorsorExistence.Tate.tateCurve c).Δ
  /-- The constant Tate model over `𝔽(t)`. -/
  d : ConstantTateData 𝔽 (RatFunc 𝔽) c
  /-- The Kummer cyclic quintic extension `𝔽(s)`, `s ^ 5 = t`. -/
  L : CyclicExtension (RatFunc 𝔽) 5
  /-- The instances needed to compare `𝔽` with the top field of the extension. -/
  [decEq : DecidableEq L.L]
  [algebra : Algebra 𝔽 L.L]
  [tower : IsScalarTower 𝔽 (RatFunc 𝔽) L.L]
  /-- **The classical input**: `E(𝔽(s)) = E(𝔽)`, i.e. every `L`-point of the constant curve is
  constant. -/
  constantsOnly : ConstantsOnly 𝔽 (Work.TorsorExistence.Tate.tateCurve c) L.L

attribute [instance] KummerResidualSharp.decEq KummerResidualSharp.algebra
  KummerResidualSharp.tower

/-- **The sharp residual of the function-field classes gives the arithmetic half.**  This closes the
chain

  `ConstantsOnly 𝔽 (Tate.tateCurve c) L` → `TrivialGaloisAction d.C₅ L` → `PointlessOf d.C₅ L`
    → `HasPointlessTwist (RatFunc 𝔽)`

at the concrete data.  The first arrow is
`Work.PointlessTwist.bridge.trivialGaloisAction_of_constantsOnly` (proved), the second
`pointlessOf_of_trivialGaloisAction` (proved), the third `hasPointlessTwist_of_pointlessOf`. -/
theorem hasPointlessTwist_of_kummerResidualSharp {𝔽 : Type} [Field 𝔽] [DecidableEq 𝔽]
    [DecidableEq (RatFunc 𝔽)] (h : KummerResidualSharp 𝔽) : HasPointlessTwist (RatFunc 𝔽) := by
  letI := h.decEq
  letI := h.algebra
  letI := h.tower
  exact hasPointlessTwist_of_pointlessOf h.d.C₅ h.L
    (pointlessOf_of_trivialGaloisAction h.d.C₅ h.L
      (bridge.trivialGaloisAction_of_constantsOnly h.c h.d h.L h.constantsOnly))

/-- **The sharp residual of class (b)** — function fields over the number field `ℚ(ζ₅)`. -/
abbrev ResidualSharp_functionField_numberField : Prop :=
  Nonempty (@KummerResidualSharp (CyclotomicField 5 ℚ) _ (Classical.decEq (CyclotomicField 5 ℚ))
    (Classical.decEq (RatFunc (CyclotomicField 5 ℚ))))

/-- **The sharp residual of class (b) gives the arithmetic half.** -/
theorem hasPointlessTwist_of_residualSharp_numberField
    (h : ResidualSharp_functionField_numberField) :
    ∃ d : DecidableEq (RatFunc (CyclotomicField 5 ℚ)),
      @HasPointlessTwist (RatFunc (CyclotomicField 5 ℚ)) _ d := by
  obtain ⟨h'⟩ := h
  exact ⟨Classical.decEq _,
    @hasPointlessTwist_of_kummerResidualSharp (CyclotomicField 5 ℚ) inferInstance
      (Classical.decEq (CyclotomicField 5 ℚ)) (Classical.decEq (RatFunc (CyclotomicField 5 ℚ)))
      h'⟩

section FiniteFieldSharp

local instance : Fact (Nat.Prime 11) := ⟨by norm_num⟩

/-- **The sharp residual of class (c)** — function fields over the finite field `𝔽₁₁`. -/
abbrev ResidualSharp_functionField_finite : Prop :=
  Nonempty (@KummerResidualSharp (ZMod 11) inferInstance inferInstance
    (Classical.decEq (RatFunc (ZMod 11))))

/-- **The sharp residual of class (c) gives the arithmetic half.** -/
theorem hasPointlessTwist_of_residualSharp_finite
    (h : ResidualSharp_functionField_finite) :
    ∃ d : DecidableEq (RatFunc (ZMod 11)),
      @HasPointlessTwist (RatFunc (ZMod 11)) _ d := by
  obtain ⟨h'⟩ := h
  exact ⟨Classical.decEq _,
    @hasPointlessTwist_of_kummerResidualSharp (ZMod 11) inferInstance inferInstance
      (Classical.decEq (RatFunc (ZMod 11))) h'⟩

end FiniteFieldSharp

/-- **The sharp residual of class (d)** — function fields over the algebraically closed field `ℂ`. -/
abbrev ResidualSharp_functionField_algClosed : Prop :=
  Nonempty (@KummerResidualSharp ℂ inferInstance inferInstance (Classical.decEq (RatFunc ℂ)))

/-- **The sharp residual of class (d) gives the arithmetic half.** -/
theorem hasPointlessTwist_of_residualSharp_algClosed
    (h : ResidualSharp_functionField_algClosed) :
    ∃ d : DecidableEq (RatFunc ℂ), @HasPointlessTwist (RatFunc ℂ) _ d := by
  obtain ⟨h'⟩ := h
  exact ⟨Classical.decEq _,
    @hasPointlessTwist_of_kummerResidualSharp ℂ inferInstance inferInstance
      (Classical.decEq (RatFunc ℂ)) h'⟩

/-- **The residual of class (b)**: function fields over the number field `ℚ(ζ₅)`, which contains a
primitive `5`-th root of unity (so that the Kummer construction applies). -/
abbrev Residual_functionField_numberField : Prop :=
  @KummerResidual (CyclotomicField 5 ℚ) _ (Classical.decEq (CyclotomicField 5 ℚ))
    (Classical.decEq (RatFunc (CyclotomicField 5 ℚ)))

section FiniteField

-- `𝔽₁₁` is a field; the `Fact` instance is local so that the abbreviation below elaborates.
local instance : Fact (Nat.Prime 11) := ⟨by norm_num⟩

/-- **The residual of class (c)**: function fields over the finite field `𝔽₁₁` (`5 ∣ 11 - 1`, so
`𝔽₁₁` contains a primitive `5`-th root of unity). -/
abbrev Residual_functionField_finite : Prop :=
  @KummerResidual (ZMod 11) _ (Classical.decEq (ZMod 11)) (Classical.decEq (RatFunc (ZMod 11)))

end FiniteField

/-- **The residual of class (d)**: function fields over the algebraically closed field `ℂ`. -/
abbrev Residual_functionField_algClosed : Prop :=
  @KummerResidual ℂ _ (Classical.decEq ℂ) (Classical.decEq (RatFunc ℂ))

end

end Work.PointlessTwist
