import Mathlib
import Submission.Work.PSU3.StageB.Omega.API
import Submission.Work.PSU3.StageB.ThetaOmegaAux

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Work.PSU3.StageB.Omega

open Submission.Blueprint
open Work.ThmF
open Work.PSU3
open Work.PSU3.StageB

/-!
# `Work.PSU3.StageB.Omega.coset_sep` — Peterfalvi II, Ch. VII §2, item (7)

Peterfalvi's (7) of §2 (p. 269): let `ω, ω' ∈ Q ∖ Q₀` and, for `i = 1, 2`, let `x_i, y_i ∈ Q₀` and
`a_i ∈ D` with `x₁ ≠ x₂` and `f(ω x_i) = (ω' y_i)^{a_i}`.  Then `a₂ ∉ a₁K`, i.e. `a₁⁻¹a₂ ∉ K`.

The point of the proof is that the two hypotheses are two instances of the equation of item (6)
for the **same** base point `ω x₁`, the two `Q₀`-elements being `1` and `x₁⁻¹ x₂` (which is `≠ 1`
exactly because `x₁ ≠ x₂`); item (6) (the hypothesis `h6` below) then gives `a₁⁻¹a₂ ∉ K`.
-/

theorem coset_sep {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}
    (hS : Work.PSU3.PSU3Hyp H Q t) (fr : Work.PSU3.CoarseFrame H Q t n)
    (h6 : ∀ {ω : ↥Q}, (ω : G) ∉ fr.Q0 → ∀ {x y : ↥Q}, (x : G) ∈ fr.Q0 → x ≠ 1 →
      ∀ (hy : (y : G) ∈ fr.Q0) {a : ↥(Submission.Blueprint.twoPoint H t)},
      Work.PSU3.StageB.fcan hS.split (ω * x) =
        Work.PSU3.StageB.qconj hS.split a (Work.PSU3.StageB.fcan hS.split ω * y) →
        (a : G) ∉ Work.ThmF.Ksub H t)
    {ω ω' : ↥Q} (hω : (ω : G) ∉ fr.Q0) (hω' : (ω' : G) ∉ fr.Q0)
    {x₁ x₂ y₁ y₂ : ↥Q} (hx₁ : (x₁ : G) ∈ fr.Q0) (hx₂ : (x₂ : G) ∈ fr.Q0)
    (hxx : x₁ ≠ x₂) (hy₁ : (y₁ : G) ∈ fr.Q0) (hy₂ : (y₂ : G) ∈ fr.Q0)
    {a₁ a₂ : ↥(Submission.Blueprint.twoPoint H t)}
    (h₁ : Work.PSU3.StageB.fcan hS.split (ω * x₁) =
      Work.PSU3.StageB.qconj hS.split a₁ (ω' * y₁))
    (h₂ : Work.PSU3.StageB.fcan hS.split (ω * x₂) =
      Work.PSU3.StageB.qconj hS.split a₂ (ω' * y₂)) :
    (a₁ : G)⁻¹ * (a₂ : G) ∉ Work.ThmF.Ksub H t := by
  -- `a₁⁻¹ a₂ ∈ D`
  have hcD : (a₁ : G)⁻¹ * (a₂ : G) ∈ twoPoint H t :=
    (twoPoint H t).mul_mem ((twoPoint H t).inv_mem a₁.2) a₂.2
  -- the new base point `ω x₁` is still outside `Q₀`
  have hωx₁ : ((ω * x₁ : ↥Q) : G) ∉ fr.Q0 := by
    intro hcon
    have hbar : fr.bar (ω * x₁) = 1 := (fr.bar_eq_one_iff (ω * x₁)).mpr hcon
    have hb1 : fr.bar x₁ = 1 := (fr.bar_eq_one_iff x₁).mpr hx₁
    rw [map_mul, hb1, mul_one] at hbar
    exact hω ((fr.bar_eq_one_iff ω).mp hbar)
  -- the `Q₀`-shift `x₁⁻¹ x₂` is non-trivial precisely because `x₁ ≠ x₂`
  have hxQ0 : (((x₁⁻¹ * x₂ : ↥Q)) : G) ∈ fr.Q0 := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (fr.Q0).mul_mem ((fr.Q0).inv_mem hx₁) hx₂
  have hxne : (x₁⁻¹ * x₂ : ↥Q) ≠ 1 := by
    intro h
    have hG : (x₁ : G)⁻¹ * (x₂ : G) = 1 := by
      have hc := congrArg (fun z : ↥Q => (z : G)) h
      simpa using hc
    refine hxx (Subtype.ext ?_)
    show (x₁ : G) = (x₂ : G)
    have h2 : (x₁ : G) * ((x₁ : G)⁻¹ * (x₂ : G)) = (x₂ : G) := by group
    rw [hG, mul_one] at h2
    exact h2
  -- the shift on the right (`y₁ y₂` conjugated by `a₁`) lies in `Q₀`
  have hyQ0 : ((qconj hS.split a₁ (y₁ * y₂) : ↥Q) : G) ∈ fr.Q0 := by
    rw [qconj_coe, Subgroup.coe_mul]
    simpa using conj_mem_Q0_of_mem_D hS fr ((twoPoint H t).inv_mem a₁.2)
      ((fr.Q0).mul_mem hy₁ hy₂)
  -- the two hypotheses, with the `Q`-elements coerced to `G`
  have h1c : ((fcan hS.split (ω * x₁) : ↥Q) : G) =
      (a₁ : G)⁻¹ * ((ω' : G) * (y₁ : G)) * (a₁ : G) := by
    rw [h₁, qconj_coe, Subgroup.coe_mul]
  have h2c : ((fcan hS.split (ω * x₂) : ↥Q) : G) =
      (a₂ : G)⁻¹ * ((ω' : G) * (y₂ : G)) * (a₂ : G) := by
    rw [h₂, qconj_coe, Subgroup.coe_mul]
  -- hence `ω'` in terms of `f(ω x₁)`
  have hω'e : (ω' : G) =
      (a₁ : G) * ((fcan hS.split (ω * x₁) : ↥Q) : G) * (a₁ : G)⁻¹ * (y₁ : G)⁻¹ := by
    rw [h1c]; group
  have hy₁inv : (y₁ : G)⁻¹ = (y₁ : G) := Q0_inv_eq_self fr hy₁
  -- the equation of item (6) for the base point `ω x₁` and the shift `x₁⁻¹ x₂`
  have heq : fcan hS.split ((ω * x₁) * (x₁⁻¹ * x₂)) =
      qconj hS.split (⟨(a₁ : G)⁻¹ * (a₂ : G), hcD⟩ : ↥(twoPoint H t))
        (fcan hS.split (ω * x₁) * qconj hS.split a₁ (y₁ * y₂)) := by
    refine Subtype.ext ?_
    have harg : (ω * x₁) * (x₁⁻¹ * x₂) = ω * x₂ := by group
    rw [harg, qconj_coe, Subgroup.coe_mul, qconj_coe, Subgroup.coe_mul]
    rw [h2c, hω'e, hy₁inv]
    group
  exact h6 (ω := ω * x₁) (x := x₁⁻¹ * x₂) (y := qconj hS.split a₁ (y₁ * y₂))
    (a := ⟨(a₁ : G)⁻¹ * (a₂ : G), hcD⟩) hωx₁ hxQ0 hxne hyQ0 heq

end Work.PSU3.StageB.Omega
