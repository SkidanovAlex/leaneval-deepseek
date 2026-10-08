import Mathlib
import Submission.Work.PSU3.StageB.Theta
import Submission.Work.PSU3.StageB.ThetaBarPrep
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

/-- The elementary arithmetic of `theta_law`: if `V = e² · c⁻¹ · U` in a field then
`U = (e⁻¹)² · c · V`. -/
lemma theta_law_arith {F : Type*} [Field F] {e c U V : F} (he : e ≠ 0) (hc : c ≠ 0)
    (h : V = e * e * (c⁻¹ * U)) : U = (e⁻¹) ^ 2 * c * V := by
  rw [h, inv_pow, ← pow_two]
  rw [show (e ^ 2)⁻¹ * c * (e ^ 2 * (c⁻¹ * U)) = (e ^ 2)⁻¹ * e ^ 2 * (c * c⁻¹) * U by ring]
  rw [inv_mul_cancel₀ (pow_ne_zero 2 he), mul_inv_cancel₀ hc]
  ring

/-- Peterfalvi II, Ch. VII §3: the "law" relating the coordinates of `f (ω s^a)` and of
`f (ω⁻¹ s^{a⁻¹})`. -/
theorem theta_law {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}
    (fr : Work.PSU3.CoarseFrame H Q t n) (h : Submission.Blueprint.IsSplitRankOne H Q t)
    {ω : G} (hω : Work.PSU3.OmegaHyp fr ω)
    (hfω : (Work.PSU3.StageB.fcan h (Work.PSU3.StageB.omQ fr hω) : G) =
      (fr.ζ : G)⁻¹ * ω⁻¹ * (fr.ζ : G))
    (a : fr.KW) (ha : (a : G) ∈ Work.ThmF.Ksub H t) :
    Multiplicative.toAdd (fr.bar (Work.PSU3.StageB.fcan h
        (Work.PSU3.StageB.omQ fr hω * Work.PSU3.StageB.sconj fr a ha)))
      = ((((fr.κ a : (Work.PSU3.E n)ˣ) : Work.PSU3.E n))⁻¹) ^ 2 *
        ((fr.κ fr.ζ : (Work.PSU3.E n)ˣ) : Work.PSU3.E n) *
        Multiplicative.toAdd (fr.bar (Work.PSU3.StageB.fcan h
          ((Work.PSU3.StageB.omQ fr hω)⁻¹ * Work.PSU3.StageB.sconjInv fr a ha))) := by
  -- `s^{a⁻¹}` is by definition `sconjInv a`
  have hsub : sconj fr a⁻¹ ((Ksub H t).inv_mem ha) = sconjInv fr a ha := by
    apply Subtype.ext
    rw [sconj_coe, sconjInv_coe]
    simp
  -- Peterfalvi §2 (2) with `(ω, a) ↦ (ω⁻¹, a⁻¹)`
  have hkey := ThetaBarA fr h hω hfω a ha
  rw [hsub] at hkey
  have hbar := congrArg (fun z : ↥Q => Multiplicative.toAdd (fr.bar z)) hkey
  -- take `bar`
  have hV : Multiplicative.toAdd (fr.bar (fcan h ((omQ fr hω)⁻¹ * sconjInv fr a ha)))
      = ((fr.κ a : (E n)ˣ) : E n) * ((fr.κ a : (E n)ˣ) : E n) *
        (((fr.κ fr.ζ : (E n)ˣ) : E n)⁻¹ *
          Multiplicative.toAdd (fr.bar (fcan h (omQ fr hω * sconj fr a ha)))) := by
    have hh := hbar
    simp only [map_mul, toAdd_mul, qact_bar fr h,
      bar_eq_one_of_mem_Q0 fr (sconj_mem_Q0 fr a ha), toAdd_one, add_zero] at hh
    have hκa : ((fr.κ a * fr.κ a : (E n)ˣ) : E n)
        = ((fr.κ a : (E n)ˣ) : E n) * ((fr.κ a : (E n)ˣ) : E n) := by
      simp
    have hκz : ((fr.κ fr.ζ⁻¹ : (E n)ˣ) : E n) = (((fr.κ fr.ζ : (E n)ˣ) : E n))⁻¹ := by
      rw [map_inv]
      exact Units.val_inv_eq_inv_val _
    rw [hκa, hκz] at hh
    exact hh
  rw [hV]
  exact theta_law_arith (Units.ne_zero _) (Units.ne_zero _) rfl

end Work.PSU3.StageB
