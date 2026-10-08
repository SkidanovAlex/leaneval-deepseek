import Submission.Work.BSW.Char.Setup

open scoped MatrixGroups

namespace Work.BSW

open Subgroup Work.GW2

open OddOrder.RepresentationTheory

/-- Bender's generalized character `α* = ind_K^G (1_K − ρ₁)` (B74 §2, p. 230), in the form that the
TI isometry applies to: it is the class function of `G` obtained by inducing the difference of the
trivial class function of `K` and the linear character `ρ₁`.

Its degree is `0`, it vanishes outside the `G`-conjugates of `K#`, and on `K` it takes the values
`2 − 2 Re ρ₁(x)`.  By the Brauer–Suzuki TI isometry its norm is `3` (see
`Submission/Work/BSW/NOTES_BSW_order.md`, Steps 2–3). -/
noncomputable def alphaFun {G : Type} [Group G] [Fintype G] (K : Subgroup G)
    [Invertible (Nat.card ↥K : ℂ)] (ρ : ↥K →* ℂˣ) : ClassFunction G ℂ :=
  ClassFunction.induce K (linearClassFunction 1 - linearClassFunction ρ)

/-- Bender's generalized character `β* = ind_K^G (ρ₁ − ρ₂)` (B74 §2, p. 230): degree `0`, vanishing
outside the conjugates of `K#`, with values `2 Re ρ₁(x) − 2 Re ρ₂(x)` on `K` and norm `2`. -/
noncomputable def betaFun {G : Type} [Group G] [Fintype G] (K : Subgroup G)
    [Invertible (Nat.card ↥K : ℂ)] (ρ₁ ρ₂ : ↥K →* ℂˣ) : ClassFunction G ℂ :=
  ClassFunction.induce K (linearClassFunction ρ₁ - linearClassFunction ρ₂)

end Work.BSW
