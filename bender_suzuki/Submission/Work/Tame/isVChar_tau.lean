import Mathlib
import Submission.Work.Tame.Defs
import Submission.Work.Tame.Tau
import Submission.Work.Tame.projEC_mul
import Submission.Work.Tame.projEC_one
import Submission.Work.Tame.isVChar_resFunHom

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Tame

noncomputable section

open Classical

variable {X : Type*} [Group X] [Fintype X]

/-- `projEC` as a group homomorphism `𝔑_i → 𝔏 ⊓ 𝔑_i`, using the decomposition
`𝔑_i = 𝔎_i(𝔏 ⊓ 𝔑_i)` (`hsup`, Definition 9.1(ii)(c)) and `𝔎_i ⊓ 𝔏 = ⊥` (`hinf`); this is what
makes `α_{i1}` of (9.4) the pullback of a virtual character along a group homomorphism. -/
noncomputable def projECMonoidHom {Lhat : Set X} {K : Subgroup X}
    (hsup : Lgrp (K : Set X) = K ⊔ (Lgrp Lhat ⊓ Lgrp (K : Set X)))
    (hinf : K ⊓ Lgrp Lhat = ⊥) :
    ↥(Lgrp (K : Set X)) →* ↥(Lgrp Lhat ⊓ Lgrp (K : Set X)) where
  toFun := projEC Lhat K
  map_one' := projEC_one hinf
  map_mul' := projEC_mul hsup hinf

/-- Feit–Thompson (9.4) expanded: `α^τ = Ind_𝔏^X α + Σ_i Ind_{𝔑_i}^X (α_{i1} - α_{i2})`. -/
theorem tau_eq (Lhat : Set X) (n : ℕ) (Hs : Fin n → Subgroup X)
    (α : ↥(Lgrp Lhat) → ℂ) :
    tau Lhat n Hs α =
      Induction.indFun (Lgrp Lhat) α +
        ∑ i : Fin n, Induction.indFun (Lgrp (Hs i : Set X))
          (alphaI1LM Lhat (Hs i) α - alphaI2LM Lhat (Hs i) α) := by
  funext x
  rw [tau_apply]
  simp only [Pi.add_apply, Finset.sum_apply]

/-- Feit–Thompson, after (9.4) (p. 805): "If `α ∈ 𝓘₀(L̂)` then (9.4) implies that `α^τ` is a
generalized character of `𝔛`."

Indeed `α^τ = Ind_𝔏^X α + Σ_i Ind_{𝔑_i}^X (α_{i1} - α_{i2})`; induction preserves virtual
characters, `α_{i1}` is the pullback of the virtual character `α_i` along the group homomorphism
`inclusion ∘ projEC : 𝔑_i →* 𝔏` (multiplicativity of `projEC`, which uses `𝔎_i ⊴ 𝔑_i`), and
`α_{i2}` is an induced virtual character.

The hypothesis `HasTameData Lhat n Hs` gives, for each supporting subgroup, Definition 9.1(ii)(c)
(`𝔑_i = 𝔎_i ⊔ (𝔏 ⊓ 𝔑_i)` and `𝔎_i ⊓ 𝔏 = ⊥`), which is what makes `projEC` a homomorphism; when
`n = 0` the sum is empty. -/
theorem isVChar_tau {X : Type*} [Group X] [Fintype X] {Lhat : Set X} {n : ℕ}
    {Hs : Fin n → Subgroup X} (h : IsTamelyImbedded Lhat n Hs) (hD : HasTameData Lhat n Hs)
    {α : ↥(Lgrp Lhat) → ℂ} (hα : α ∈ I0 Lhat) :
    CharCore.IsVChar (tau Lhat n Hs α) := by
  have hαv : CharCore.IsVChar α := hα.1
  rcases hD with hne | hn0
  · -- `𝔇 ≠ ∅`: the supporting subgroups give `projEC : 𝔑_i →* 𝔏 ⊓ 𝔑_i` (Definition 9.1(ii)(c)).
    have hsummand : ∀ i : Fin n,
        CharCore.IsVChar (Induction.indFun (Lgrp (Hs i : Set X))
          (alphaI1LM Lhat (Hs i) α - alphaI2LM Lhat (Hs i) α)) := by
      intro i
      have hsup := h.supp_prod hne i
      have hinf := h.supp_inf hne i
      -- `α_{i1}` is the pullback of `α` along `inclusion ∘ projEC : 𝔑_i →* 𝔏`.
      have h1 : CharCore.IsVChar (alphaI1LM Lhat (Hs i) α) := by
        rw [show alphaI1LM Lhat (Hs i) α =
          Induction.resFunHom ((Subgroup.inclusion inf_le_left).comp
            (projECMonoidHom hsup hinf)) α from rfl]
        exact isVChar_resFunHom _ hαv
      -- `α_{i2} = Ind_{𝔏 ⊓ 𝔑_i}^{𝔑_i} (α|_{𝔏 ⊓ 𝔑_i})`.
      have h2 : CharCore.IsVChar (alphaI2LM Lhat (Hs i) α) := by
        rw [show alphaI2LM Lhat (Hs i) α =
          Induction.indFun ((Lgrp Lhat ⊓ Lgrp (Hs i : Set X)).subgroupOf (Lgrp (Hs i : Set X)))
            (Induction.resFunHom ((Subgroup.inclusion inf_le_left).comp
              ((Subgroup.subgroupOfEquivOfLe
                (inf_le_right : Lgrp Lhat ⊓ Lgrp (Hs i : Set X) ≤ Lgrp (Hs i : Set X))).toMonoidHom)) α)
          from rfl]
        exact Work.Induction.isVChar_indFun (isVChar_resFunHom _ hαv)
      exact Work.Induction.isVChar_indFun (CharCore.IsVChar.sub h1 h2)
    rw [tau_eq Lhat n Hs α]
    exact CharCore.IsVChar.add (Work.Induction.isVChar_indFun hαv)
      (CharCore.IsVChar.sum (s := Finset.univ) (fun i _ => hsummand i))
  · -- `n = 0`: the sum is empty and `α^τ = Ind_𝔏^X α`.
    subst hn0
    rw [tau_eq Lhat 0 Hs α]
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
    exact Work.Induction.isVChar_indFun hαv

end

end Work.Tame

