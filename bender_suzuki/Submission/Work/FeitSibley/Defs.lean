import Submission.Blueprint.Interfaces

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Area `FeitSibley`: the Feit–Sibley theorem (Peterfalvi II, Appendice XII)

This module fixes the vocabulary of the area.  The target statement is
`Submission.Blueprint.FeitSibleyProp`:

> `G` finite, `H = Q ⋊ D < G` with `(|D|, |Q|) = 1` and `Q ∩ Qˣ = 1` for `x ∉ H`;
> `Q = S × Q₁` with `(|S|, |Q₁|) = 1`, `S` nilpotent, `D` fixed-point-free on `Q₁`,
> `Q₁` not a `2`-group, `|D|` odd.  Then `𝒮 = {χ ∈ Irr H | Q₁ ⊄ ker χ}` has at least two
> members and is coherent for `Ind_H^G`.

Everything is packaged in the structure `FSData`, whose fields are *verbatim* the hypotheses
of `FeitSibleyProp`.  The lemmas of the area are stated for `(h : FSData G)`; the final
theorem `feitSibley` unfolds the structure back into `FeitSibleyProp`.

## Conventions

* `conj x Q = x Q x⁻¹` (the challenge's conjugation, as in `Submission.Blueprint.conj`).
* `scriptS H Q₁ = 𝒮 = {χ ∈ Irr H | Q₁ ⊄ ker χ}` and
  `scriptSR H Q₁ R = 𝒮(R) = {χ ∈ 𝒮 | R ≤ ker χ}`.
* `indLin H = Ind_H^G` as a `ℤ`-linear map on class functions
  (`Work.Induction.indFun`; definitionally `Submission.Blueprint.indLinear`).
* Characters are functions `G → ℂ`; `Work.CharCore.Irr` is a `Finset`, and `𝒮` is a `Finset`
  of functions on the subgroup `↥H`.
* `IsFpfOn D A`: every `1 ≠ d ∈ D` fixes only `1` of `A`.
-/

noncomputable section

open Classical

namespace Work.FeitSibley

variable {G : Type} [Group G]

/-- Global classical decidability of propositions (low priority, like `open Classical`), so
that statements mentioning `Work.CharCore.Irr ↥H` elaborate in files that do not themselves
`open Classical`. -/
instance (priority := 10) instDecidablePredClassical {α : Type*} (p : α → Prop) :
    DecidablePred p := fun _ => Classical.propDecidable _

/-- `D` acts *fixed point freely* on the subgroup `A`: if `d ∈ D`, `d ≠ 1` and `x ∈ A` with
`d x d⁻¹ = x`, then `x = 1`.  (Only the stated direction is used; `D` is not assumed to
normalise `A` in the definition.) -/
def IsFpfOn (D A : Subgroup G) : Prop :=
  ∀ d ∈ D, d ≠ 1 → ∀ x ∈ A, d * x * d⁻¹ = x → x = 1

/-- The hypotheses of the Feit–Sibley theorem, verbatim from
`Submission.Blueprint.FeitSibleyProp`: `H = Q ⋊ D` is a proper subgroup with `(|D|,|Q|) = 1`
and `Q` a T.I. subgroup with `N_G(Q) = H`; `Q = S × Q₁` with `(|S|,|Q₁|) = 1`, `S` nilpotent,
`D` fixed-point-free on `Q₁`, `Q₁` not a `2`-group, and `|D|` odd. -/
structure FSData (G : Type) [Group G] [Fintype G] where
  /-- the "Borel" `H = Q ⋊ D`. -/
  H : Subgroup G
  /-- the T.I. Hall subgroup `Q`. -/
  Q : Subgroup G
  /-- the Frobenius complement `D`. -/
  D : Subgroup G
  /-- the first direct factor `S` of `Q`. -/
  S : Subgroup G
  /-- the second direct factor `Q₁` of `Q`. -/
  Q1 : Subgroup G
  /-- `H` is a proper subgroup. -/
  H_ne_top : H ≠ ⊤
  /-- `Q ≤ H`. -/
  Q_le_H : Q ≤ H
  /-- `Q` is normal in `H`. -/
  Q_normal_in_H : H ≤ Subgroup.normalizer (Q : Set G)
  /-- `D ≤ H`. -/
  D_le_H : D ≤ H
  /-- `Q` and `D` meet trivially. -/
  Q_inf_D : Q ⊓ D = ⊥
  /-- `Q` and `D` generate `H`. -/
  Q_sup_D : Q ⊔ D = H
  /-- `|D|` and `|Q|` are coprime. -/
  coprime_D_Q : Nat.Coprime (Nat.card D) (Nat.card Q)
  /-- `Q` is a T.I. subgroup: `Q ∩ Qˣ = 1` for `x ∉ H`. -/
  Q_TI : ∀ x : G, x ∉ H → Q ⊓ Submission.Blueprint.conj x Q = ⊥
  /-- `S · Q₁ = Q`. -/
  S_sup_Q1 : S ⊔ Q1 = Q
  /-- `S ∩ Q₁ = 1`. -/
  S_inf_Q1 : S ⊓ Q1 = ⊥
  /-- `S` and `Q₁` commute elementwise. -/
  commute : ∀ a ∈ S, ∀ b ∈ Q1, a * b = b * a
  /-- `|S|` and `|Q₁|` are coprime. -/
  coprime_S_Q1 : Nat.Coprime (Nat.card S) (Nat.card Q1)
  /-- `S` is nilpotent. -/
  S_nilpotent : Group.IsNilpotent S
  /-- `D` acts fixed point freely on `Q₁`. -/
  D_fpf_Q1 : IsFpfOn D Q1
  /-- `Q₁` is not a `2`-group. -/
  Q1_not_two : ¬ IsPGroup 2 Q1
  /-- `|D|` is odd. -/
  D_odd : Odd (Nat.card D)

section Vocabulary

variable [Fintype G]

/-- `𝒮 = {χ ∈ Irr H | Q₁ ⊄ ker χ}`, Peterfalvi's set of characters (App. XII). -/
abbrev scriptS (H Q1 : Subgroup G) : Finset (H → ℂ) :=
  Submission.Blueprint.excludingKernel H Q1

/-- `𝒮(R) = {χ ∈ 𝒮 | R ≤ ker χ}`, for `R ≤ Q`. -/
def scriptSR (H Q1 R : Subgroup G) : Finset (H → ℂ) :=
  (scriptS H Q1).filter (fun χ => ∀ x : H, (x : G) ∈ R → χ x = χ 1)

/-- `Ind_H^G` as a `ℤ`-linear map on class functions (`Work.Induction.indFun`). -/
abbrev indLin (H : Subgroup G) : (H → ℂ) →ₗ[ℤ] (G → ℂ) :=
  Submission.Blueprint.indLinear H

theorem indLin_apply (H : Subgroup G) (φ : H → ℂ) : indLin H φ = Work.Induction.indFun H φ := rfl

end Vocabulary

end Work.FeitSibley
