import Submission.Work.ThmF.Setup
import Submission.Work.ThmF.ChV12.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Ch. V §2, Lemma 5: the distinguished involution of order 3 (`X = ⟨Q₀, K, t⟩`)

Definitions of the object `X = ⟨Q₀, K, t⟩` used in Peterfalvi II, Ch. V §2 Lemma 5 (p. 246),
together with the hypothesis bundle `Hyp5` (`st` of order 3) and the elementary consequence
`t s t = s t s`.  The mathematical leaves (`lemma5a`, `lemma5b`, `lemma5`, `lemma5d`) are
stated in the sibling modules; see `NOTES_LEAD_probe0445.md` and
`_design/lemma5_probe0445.lean` for the design.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs

namespace Work.ThmF.Lemma5

open Submission.Blueprint

variable {G : Type} [Group G] [Finite G]

/-- Hypotheses of Lemma 5: (B0)–(B2), a split rank-one datum, and the distinguished involution
`s ∈ Q` with `st` of order `3` (equivalently, the structure identity with `r = s`). -/
structure Hyp5 (H Q : Subgroup G) (t s : G) : Prop where
  sit : Situation G
  split : IsSplitRankOne H Q t
  s_mem : s ∈ Q
  s_inv : orderOf s = 2
  ord3 : orderOf (s * t) = 3

/-- `X = ⟨Q₀, K, t⟩`. -/
def X5 (H : Subgroup G) (t : G) : Subgroup G := Subgroup.closure (Q0 H ∪ Kset H t ∪ {t})

theorem t_mem_X5 (H : Subgroup G) (t : G) : t ∈ X5 H t :=
  Subgroup.subset_closure (Or.inr rfl)

/-- `t` as an element of `X`. -/
def tX (H : Subgroup G) (t : G) : ↥(X5 H t) := ⟨t, t_mem_X5 H t⟩

theorem Q0_subset_X5 (H : Subgroup G) (t : G) : Q0 H ⊆ (X5 H t : Set G) :=
  fun x hx => Subgroup.subset_closure (Or.inl (Or.inl hx))

theorem Kset_subset_X5 (H : Subgroup G) (t : G) : Kset H t ⊆ (X5 H t : Set G) :=
  fun x hx => Subgroup.subset_closure (Or.inl (Or.inr hx))

/-- The elementary consequence of `orderOf (s * t) = 3` used throughout Lemma 5. -/
theorem tst_eq_sts {H Q : Subgroup G} {t s : G} (h : Hyp5 H Q t s) :
    t * s * t = s * t * s := by
  have hss : s * s = 1 := by
    have h1 := pow_orderOf_eq_one s
    rw [h.s_inv] at h1
    simpa [pow_two] using h1
  have htt : t * t = 1 := by
    have h1 := pow_orderOf_eq_one t
    rw [h.split.invol] at h1
    simpa [pow_two] using h1
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have h3 : (s * t) ^ 3 = 1 := by
    have h1 := pow_orderOf_eq_one (s * t)
    rw [h.ord3] at h1
    exact h1
  have h3' : (s * t) * ((s * t) * (s * t)) = 1 := by
    simpa [pow_succ, pow_two, mul_assoc] using h3
  have hsq : (s * t) * (s * t) = t * s := by
    have h8 : (s * t) * (s * t) = (s * t)⁻¹ := by
      have h10 := congrArg (fun z => z * (s * t)⁻¹) h3'
      simpa [mul_assoc] using h10
    rw [h8, mul_inv_rev, hsinv, htinv]
  have h9 : s * (t * s * t) = s * (s * t * s) := by
    rw [show s * (t * s * t) = (s * t) * (s * t) by group, hsq]
    rw [show s * (s * t * s) = (s * s) * (t * s) by group, hss, one_mul]
  exact mul_left_cancel h9

end Work.ThmF.Lemma5
