/-
# `Work.PSU3.StageB.theta_bar_mul` — Peterfalvi II, Ch. VII §3 (2), cleared form

`Work.PSU3.StageB.ThetaBar` computes the `bar`-value of `f (ω s^a)` in the *quotient* form

$$\overline{f(\omega s^a)} = \frac{\zeta\,\bar\omega}{1+\zeta a^2},\qquad \zeta = \kappa(\zeta),\ a^2 = (\kappa a)^2 .$$

Writing that form out requires the denominator `1 + ζ a²` to be invertible, which is *not*
available at this point of the argument.  The content of Ch. VII §3 (2) is really the
un-divided identity

$$(1+\zeta a^2)\,\overline{f(\omega s^a)} = \zeta\,\bar\omega ,$$

obtained from the two evaluations of `f (ω⁻¹ s^{a⁻¹})` (`ThetaBarA`, `ThetaBarB`) by clearing
`c = ζ`; the division form then *follows*.  In characteristic two the clearing is particularly
transparent: the agreement of the two evaluations, after applying `bar`, reads
`A (c⁻¹ U) = c⁻¹ (c⁻¹ U) + c⁻¹ W`; multiplying by `c²` gives `c A U = U + c W`, and
`1 + 1 = 0` turns that into `(1 + cA) U = c W`.

The two ingredients of this file are

* `char2_clear_denom` — the elementary field algebra (no group theory);
* the `bar`-image of the agreement of the two evaluations, a computation inside the frame
  using `qact_bar` and `bar = 1` on `Q₀`.
-/
import Mathlib
import Submission.Work.PSU3.StageB.Theta
import Submission.Work.PSU3.StageB.ThetaBarPrep
import Submission.Work.PSU3.StageB.ThetaOmegaAux
import Submission.Work.PSU3.StageB.ThetaBar

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint
open Work.RankOneUniqueness
open Work.ThmF
open Work.PSU3
open Classical

namespace Work.PSU3.StageB

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}

/-! ## §1. Clearing denominators in characteristic two -/

/-- **Clearing denominators in characteristic two.**  If `A * (c⁻¹ * U) = c⁻¹ * (c⁻¹ * U) + c⁻¹ * W`
with `c ≠ 0` in a field of characteristic two, then `(1 + c * A) * U = c * W`.

This is the un-divided form of `U = c * W / (1 + c * A)`: multiplying the hypothesis by `c²`
gives `c * A * U = U + c * W`, and `1 + 1 = 0` gives `(1 + c * A) * U = U + c * A * U = c * W`.
No hypothesis on `1 + c * A` is needed, which is exactly the point. -/
lemma char2_clear_denom {F : Type*} [Field F] [CharP F 2] {c A U W : F} (hc : c ≠ 0)
    (h : A * (c⁻¹ * U) = c⁻¹ * (c⁻¹ * U) + c⁻¹ * W) :
    (1 + c * A) * U = c * W := by
  have htwo : (2 : F) = 0 := by
    have h' : ((2 : ℕ) : F) = 0 := (CharP.cast_eq_zero_iff F 2 2).mpr (dvd_refl 2)
    simpa using h'
  have hself : ∀ x : F, x + x = 0 := fun x => by rw [← two_mul, htwo, zero_mul]
  -- multiplying by `c`:
  have hcL : c * (A * (c⁻¹ * U)) = A * U := by
    calc c * (A * (c⁻¹ * U)) = (c * A) * (c⁻¹ * U) := (mul_assoc c A (c⁻¹ * U)).symm
      _ = ((c * A) * c⁻¹) * U := (mul_assoc (c * A) c⁻¹ U).symm
      _ = ((A * c) * c⁻¹) * U := by rw [mul_comm c A]
      _ = (A * (c * c⁻¹)) * U := by rw [mul_assoc A c c⁻¹]
      _ = (A * 1) * U := by rw [mul_inv_cancel₀ hc]
      _ = A * U := by rw [mul_one]
  have hcR1 : c * (c⁻¹ * (c⁻¹ * U) + c⁻¹ * W) = c⁻¹ * U + W := by
    rw [mul_add, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]
    rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  have hcR : c * (c * (c⁻¹ * (c⁻¹ * U) + c⁻¹ * W)) = U + c * W := by
    rw [hcR1, mul_add, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  have h1 : c * A * U = U + c * W := by
    have h2 : c * (c * (A * (c⁻¹ * U))) =
        c * (c * (c⁻¹ * (c⁻¹ * U) + c⁻¹ * W)) := by rw [h]
    rw [hcL, hcR] at h2
    rwa [← mul_assoc] at h2
  calc (1 + c * A) * U = U + c * A * U := by rw [add_mul, one_mul]
    _ = U + (U + c * W) := by rw [h1]
    _ = c * W := by rw [← add_assoc, hself U, zero_add]

/-! ## §2. Peterfalvi §3 (2), multiplicative form -/

/-- **Peterfalvi II, Ch. VII §3 (2)**, in the un-divided (multiplicative) form.

The two evaluations `ThetaBarA` and `ThetaBarB` of `f (ω⁻¹ s^{a⁻¹})` agree; applying `bar` and
using `bar (x^d) = κ(d) · bar x` together with `bar (s^a) = 1` turns this into
`a² (ζ⁻¹ U) = ζ⁻¹ (ζ⁻¹ U) + ζ⁻¹ W` with `U = bar (f (ω s^a))`, `W = bar ω`; clearing the
denominator gives `(1 + ζ a²) U = ζ W`. -/
theorem theta_bar_mul {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}
    (fr : Work.PSU3.CoarseFrame H Q t n) (h : Submission.Blueprint.IsSplitRankOne H Q t)
    {ω : G} (hω : Work.PSU3.OmegaHyp fr ω)
    (hW : (Work.PSU3.StageB.hcan h (Work.PSU3.StageB.omQ fr hω) : G) ∈ Work.ThmF.W H t)
    (hfω : (Work.PSU3.StageB.fcan h (Work.PSU3.StageB.omQ fr hω) : G) =
      (fr.ζ : G)⁻¹ * ω⁻¹ * (fr.ζ : G))
    (hzinv : (Work.PSU3.StageB.hcan h ((Work.PSU3.StageB.omQ fr hω)⁻¹) : G) =
      (fr.ζ : G)⁻¹ * (fr.ζ : G)⁻¹ * (fr.ζ : G)⁻¹)
    (a : fr.KW) (ha : (a : G) ∈ Work.ThmF.Ksub H t) :
    (1 + ((fr.κ fr.ζ : (Work.PSU3.E n)ˣ) : Work.PSU3.E n) *
        (((fr.κ a : (Work.PSU3.E n)ˣ) : Work.PSU3.E n)) ^ 2) *
      Multiplicative.toAdd (fr.bar (Work.PSU3.StageB.fcan h
        (Work.PSU3.StageB.omQ fr hω * Work.PSU3.StageB.sconj fr a ha)))
    = ((fr.κ fr.ζ : (Work.PSU3.E n)ˣ) : Work.PSU3.E n) *
        Multiplicative.toAdd (fr.bar (Work.PSU3.StageB.omQ fr hω)) := by
  -- the two evaluations of `f (ω⁻¹ s^{a⁻¹})`
  have hA := ThetaBarA fr h hω hfω a ha
  have hB := ThetaBarB fr h hω hfω hzinv a ha
  -- `s^{a⁻¹} ∈ Q₀ = Z(Q)`, so it commutes with `ω⁻¹`
  have hswap : (omQ fr hω)⁻¹ * sconj fr a⁻¹ ((Ksub H t).inv_mem ha) =
      sconj fr a⁻¹ ((Ksub H t).inv_mem ha) * (omQ fr hω)⁻¹ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    exact (fr.Q0_central (sconj fr a⁻¹ ((Ksub H t).inv_mem ha))
      (sconj_mem_Q0 fr a⁻¹ _) (omQ fr hω)⁻¹ (Q.inv_mem (omQ fr hω).2)).symm
  -- the agreement of the two evaluations
  have key : qact fr h (a * a)
        (qact fr h fr.ζ⁻¹ (fcan h (omQ fr hω * sconj fr a ha))) * sconj fr a ha =
      qact fr h ((fr.ζ * fr.ζ)⁻¹) (fcan h (omQ fr hω * sconj fr a ha)) *
        qact fr h fr.ζ⁻¹ (omQ fr hω) := by
    rw [← hA, ← hB, hswap]
  -- abbreviations matching the goal
  set U0 : E n := Multiplicative.toAdd (fr.bar (fcan h (omQ fr hω * sconj fr a ha))) with hU0
  set W0 : E n := Multiplicative.toAdd (fr.bar (omQ fr hω)) with hW0
  set c : E n := ((fr.κ fr.ζ : (E n)ˣ) : E n) with hcdef
  set A2 : E n := ((fr.κ a : (E n)ˣ) : E n) ^ 2 with hA2def
  -- take `bar` of the agreement
  have hbar' : A2 * (c⁻¹ * U0) = c⁻¹ * (c⁻¹ * U0) + c⁻¹ * W0 := by
    have hh := congrArg (fun z : ↥Q => Multiplicative.toAdd (fr.bar z)) key
    simp only [map_mul, Units.val_mul, toAdd_mul, qact_bar,
      bar_eq_one_of_mem_Q0 fr (sconj_mem_Q0 fr a ha), toAdd_one, add_zero] at hh
    have e1 : ((fr.κ a : (E n)ˣ) : E n) * ((fr.κ a : (E n)ˣ) : E n) = A2 := by
      rw [hA2def, pow_two]
    have e2 : ((fr.κ fr.ζ⁻¹ : (E n)ˣ) : E n) = c⁻¹ := by
      rw [hcdef, map_inv, Units.val_inv_eq_inv_val]
    have e3 : ((fr.κ ((fr.ζ * fr.ζ)⁻¹) : (E n)ˣ) : E n) = c⁻¹ * c⁻¹ := by
      rw [hcdef, map_inv, map_mul, Units.val_inv_eq_inv_val, Units.val_mul, mul_inv_rev]
    rw [e1, e2, e3] at hh
    rwa [mul_assoc] at hh
  have hc0 : c ≠ 0 := by
    rw [hcdef]
    exact Units.ne_zero _
  exact char2_clear_denom hc0 hbar'

end Work.PSU3.StageB
