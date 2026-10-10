import Mathlib.Algebra.Group.Subgroup.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Degree-`3` cochain bookkeeping for the model bridge `H3loc ≃+ H³_cont`

`Submission/Work/SSGRoute/LTDDefs/H2locAux.lean` provides the degree-`2` bookkeeping
(`restrictFun2`, `extendFun2`) used by the model bridge `H2loc ≃+ H²(↥H, M)`
(`LTDDefs/H2locEquivH2.lean`).  This file provides the degree-`3` analogue: restriction of a
`3`-cochain on `G_k` to a subgroup `H`, and extension by `0` off `H`.

The local cohomology `H3loc` of `LTDDefs`-style (`kummerBase_euler_h3loc.lean`) is built from
functions on the *whole* group `G_k = Ω ≃ₐ[k] Ω` whose `3`-cocycle and local-constancy conditions
are imposed only on the subgroup `H = decomp k A`; the continuous model `Work.SSGRoute.Z3`
(`kummerBase_euler_h3_absKummer.lean`) is built from continuous cochains on the group `↥H` itself.
The two `fun`-level operations defined here are the ones that compare the two, exactly as
`restrictFun2`/`extendFun2` compare the degree-`2` models.
-/

namespace Work.SSGRoute.LTDDefs.H3loc

open Classical

noncomputable section

/-- Restriction of a `3`-cochain on a group `Γ` to the subgroup `↥H`. -/
def restrictFun3 {Γ : Type*} [Group Γ] {M : Type} (H : Subgroup Γ)
    (e : Γ → Γ → Γ → M) : ↥H × ↥H × ↥H → M :=
  fun q => e q.1 q.2.1 q.2.2

/-- Extension by `0` off `H` of a `3`-cochain of the subgroup `↥H`. -/
def extendFun3 {Γ : Type*} [Group Γ] {M : Type} [Zero M] (H : Subgroup Γ)
    (e : ↥H × ↥H × ↥H → M) : Γ → Γ → Γ → M :=
  fun g h l => if hg : g ∈ H then
    (if hh : h ∈ H then (if hl : l ∈ H then e (⟨g, hg⟩, ⟨h, hh⟩, ⟨l, hl⟩) else 0) else 0) else 0

@[simp] lemma restrictFun3_apply {Γ : Type*} [Group Γ] {M : Type} (H : Subgroup Γ)
    (e : Γ → Γ → Γ → M) (g h l : ↥H) : restrictFun3 H e (g, h, l) = e g h l := rfl

@[simp] lemma extendFun3_apply {Γ : Type*} [Group Γ] {M : Type} [Zero M] (H : Subgroup Γ)
    (e : ↥H × ↥H × ↥H → M) {g h l : Γ} (hg : g ∈ H) (hh : h ∈ H) (hl : l ∈ H) :
    extendFun3 H e g h l = e (⟨g, hg⟩, ⟨h, hh⟩, ⟨l, hl⟩) := by
  simp only [extendFun3, dif_pos hg, dif_pos hh, dif_pos hl]

lemma extendFun3_add {Γ : Type*} [Group Γ] {M : Type} [AddCommGroup M] (H : Subgroup Γ)
    {c d : ↥H × ↥H × ↥H → M} : extendFun3 H (c + d) = extendFun3 H c + extendFun3 H d := by
  funext g h l
  by_cases hg : g ∈ H <;> by_cases hh : h ∈ H <;> by_cases hl : l ∈ H <;>
    simp [extendFun3, hg, hh, hl, Pi.add_apply]

lemma extendFun3_zero {Γ : Type*} [Group Γ] {M : Type} [Zero M] (H : Subgroup Γ) :
    extendFun3 H (0 : ↥H × ↥H × ↥H → M) = 0 := by
  funext g h l
  by_cases hg : g ∈ H <;> by_cases hh : h ∈ H <;> by_cases hl : l ∈ H <;>
    simp [extendFun3, hg, hh, hl]

/-- Restriction after extension by `0` off `H` is the identity. -/
lemma restrictFun3_extendFun3 {Γ : Type*} [Group Γ] {M : Type} [Zero M] (H : Subgroup Γ)
    (e : ↥H × ↥H × ↥H → M) : restrictFun3 H (extendFun3 H e) = e := by
  funext q
  obtain ⟨g, h, l⟩ := q
  simp only [restrictFun3_apply, extendFun3_apply H e g.2 h.2 l.2]

end

end Work.SSGRoute.LTDDefs.H3loc
