/-
Copyright (c) 2024. All rights reserved.

# Squares of a class-two Suzuki subgroup lie in `Ω₁`

`Work.Higman.Q3.Dsq_sq_mem_powSub_two`: in the `C₄` setting, if `D ⊴ P` is `ξ`-invariant with
`A ≤ D` and `⁅D,D⁆ = powSub A 2 = Ω₁(P)`, then `D` is a Suzuki 2-group of class two with
`Ω₁(D) = Z(D) = A²`, so every square of an element of `D` lies in `A²`.

This is what kills the branch `E' = A²` of the `C₄` exclusion: there `E ⊴ P` is `ξ`-invariant
with `E' = A²`, and an element `x ∈ E∖A` with `x² ∉ A²` would contradict this lemma.
-/

import Submission.Work.Higman.OmegaAux
import Submission.Work.Higman.center_eq_omega1_new
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.Q3.sq_mem_center_of_class_two
import Submission.Work.Higman.NSM.redcase

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped commutatorElement

namespace Work.Higman.Q3

theorem Dsq_sq_mem_powSub_two {P : Type} [Group P] [Finite P]
    (h : Work.Higman.IsSuzuki2Grp P) {A D : Subgroup P}
    (hAxi : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hNA : Work.Higman.omega1 P ≤ A)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hDn : D.Normal) (hDinv : D.map (h.xi : MulAut P).toMonoidHom = D)
    (hAD : A ≤ D)
    (hDd : ⁅D, D⁆ = Work.Higman.powSub A 2) :
    ∀ x ∈ D, x ^ 2 ∈ Work.Higman.powSub A 2 := by
  -- `A ^ 2 = Ω₁(P) ≠ ⊥`
  have hA2ne : Work.Higman.powSub A 2 ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card ↥(Work.Higman.omega1 P) = 1 := by rw [← htop, hbot]; simp
    have h4 := h.omega1_card_ge_four
    omega
  -- `Ω₁(P) ≤ D`
  have hOmD : Work.Higman.omega1 P ≤ D := by
    rw [← htop]
    exact (Work.Higman.powSub_le (A := A) (n := 2) (by norm_num)).trans hAD
  -- `D` is not abelian, because `[D,D] = A² ≠ ⊥`
  have hni : ∃ x y : ↥D, x * y ≠ y * x := by
    by_contra hcon
    push Not at hcon
    have hDab : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x := fun x hx y hy =>
      congrArg Subtype.val (hcon ⟨x, hx⟩ ⟨y, hy⟩)
    have hbot : ⁅D, D⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (hDab x hx y hy).symm
    exact hA2ne (by rw [← hDd]; exact hbot)
  haveI hDSz : Work.Higman.IsSuzuki2Grp ↥D :=
    Work.Higman.NSM.isSuzuki2Grp_subgroup h hDinv hOmD hni
  -- `Z(D) = Ω₁(D) = Ω₁(P)` inside `D`
  have hZm : Subgroup.center ↥D = (Work.Higman.powSub A 2).subgroupOf D := by
    rw [Work.Higman.center_eq_omega1_new hDSz, Work.Higman.NSM.omega1_subgroupOf h hDSz, htop]
  -- the two hypotheses of the class-two lemma, inside `↥D`
  have hZc : ⁅(⊤ : Subgroup ↥D), ⊤⁆ ≤ Subgroup.center ↥D := by
    intro u hu
    rw [Work.Higman.NSM.commutator_subgroupOf D, hDd] at hu
    rw [hZm]
    exact hu
  have h2c : ∀ u v : ↥D, (u * v * u⁻¹ * v⁻¹) ^ 2 = 1 := by
    intro u v
    have hmem : u * v * u⁻¹ * v⁻¹ ∈ ⁅(⊤ : Subgroup ↥D), ⊤⁆ :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top u) (Subgroup.mem_top v)
    rw [Work.Higman.NSM.commutator_subgroupOf D, hDd] at hmem
    have hP : ((u * v * u⁻¹ * v⁻¹ : ↥D) : P) ∈ Work.Higman.omega1 P := by
      rw [← htop]
      exact (Subgroup.mem_subgroupOf ..).mp hmem
    have h2 : ((u * v * u⁻¹ * v⁻¹ : ↥D) : P) ^ 2 = 1 := h.mem_omega1.mp hP
    exact Subtype.ext (by simpa using h2)
  intro x hx
  have hx2 : (⟨x, hx⟩ : ↥D) ^ 2 ∈ Subgroup.center ↥D :=
    sq_mem_center_of_class_two hZc h2c ⟨x, hx⟩
  rw [hZm] at hx2
  simpa using (Subgroup.mem_subgroupOf ..).mp hx2

end Work.Higman.Q3
