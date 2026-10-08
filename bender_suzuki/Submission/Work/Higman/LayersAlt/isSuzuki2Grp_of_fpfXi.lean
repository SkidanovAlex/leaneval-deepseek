/-
Copyright (c) 2024. All rights reserved.

# `ξ` itself is a Suzuki-automorphism

Let `P` be a Suzuki 2-group (Higman 1963) in the sense of `Work.Higman.IsSuzuki2Grp`: a finite
non-abelian 2-group with more than one involution carrying a cyclic group of automorphisms that
permutes the involutions transitively.  If moreover `ξ : MulAut P` satisfies `FpfXi ξ` — i.e.
`|P| = |Z(P)| ^ 3`, `orderOf ξ = |Z(P)| - 1`, and every non-trivial power of `ξ` is
fixed-point-free on `P` — then `ξ` *itself* is transitive on the involutions, so that `ξ` can be
used as the automorphism witnessing the Suzuki 2-group hypothesis.

The point is the counting: by `center_eq_omega1_of_fpf` the centre `Z(P) = Ω₁(P)` is elementary
abelian and consists of the identity together with the involutions, so `#Invol P = |Z(P)| - 1 =
orderOf ξ`.  On the other hand the `⟨ξ⟩`-orbit of an involution `x` has `orderOf ξ` elements
(the stabiliser of `x ≠ 1` is trivial by fixed-point-freeness) and consists of involutions;
hence it is *all* of `Invol P`, which is exactly transitivity.
-/

import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.typeB
import Submission.Work.Higman.LayersAlt.GroupSide

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Work.Higman.LayersAlt

/-- **`ξ` is a Suzuki-automorphism.**  A fixed-point-free automorphism of order `|Z(P)| - 1` of
a Suzuki 2-group `P` (with `|P| = |Z(P)| ^ 3`) permutes the involutions of `P` transitively;
hence it realises the `IsSuzuki2Grp` structure on `P`. -/
theorem isSuzuki2Grp_of_fpfXi {P : Type} [Group P] [Finite P] (h : Work.Higman.IsSuzuki2Grp P)
    {ξ : MulAut P} (hξ : Work.Higman.FpfXi ξ) :
    ∃ h' : Work.Higman.IsSuzuki2Grp P, h'.xi = ξ := by
  classical
  -- `Z(P) = Ω₁(P)`, hence `#Invol P = |Z(P)| - 1 = orderOf ξ`
  have hZ : Subgroup.center P = omega1 P := center_eq_omega1_of_fpf h hξ
  have hInvol : (Invol P).ncard = orderOf ξ := by
    have h1 : Nat.card (omega1 P) = Nat.card ↥(Subgroup.center P) := by rw [hZ]
    have h2 := h.card_omega1
    rw [h1] at h2
    rw [hξ.order]
    omega
  refine ⟨{ isPGroup := h.isPGroup, noncomm := h.noncomm, manyInvol := h.manyInvol, xi := ξ, trans := ?_ }, rfl⟩
  -- transitivity of `ξ` on the involutions
  intro x y hx hy
  have hstep : ∀ k : ℕ, (ξ ^ k) x ∈ Invol P := by
    intro k
    rw [mem_Invol, MulEquiv.orderOf_eq (ξ ^ k) x, hx]
  -- every element of the orbit of `x` is a non-trivial involution
  have hne1 : ∀ k : ℕ, (ξ ^ k) x ≠ 1 := by
    intro k h0
    have h1 := hstep k
    rw [h0, mem_Invol, orderOf_one] at h1
    exact absurd h1 (by norm_num)
  -- the elements `ξ ^ k x`, `k < orderOf ξ`, are distinct
  have key : ∀ a b : ℕ, a < orderOf ξ → b < orderOf ξ →
      (ξ ^ a) x = (ξ ^ b) x → a = b := by
    intro a b ha hb hab
    rcases le_total a b with hle | hle
    · have h2 : (ξ ^ (b - a)) ((ξ ^ a) x) = (ξ ^ b) x := by
        rw [← MulAut.mul_apply, ← pow_add, Nat.sub_add_cancel hle]
      have h3 : (ξ ^ (b - a)) ((ξ ^ a) x) = (ξ ^ a) x := h2.trans hab.symm
      have h4 : ξ ^ (b - a) = 1 := by
        by_contra hc
        exact hne1 a (hξ.fpf (b - a) hc ((ξ ^ a) x) h3)
      have h5 : orderOf ξ ∣ b - a := orderOf_dvd_iff_pow_eq_one.mpr h4
      have h6 : b - a < orderOf ξ := lt_of_le_of_lt (Nat.sub_le b a) hb
      rcases Nat.eq_zero_or_pos (b - a) with h0 | hpos
      · omega
      · exact absurd (Nat.le_of_dvd hpos h5) (not_le.mpr h6)
    · have h2 : (ξ ^ (a - b)) ((ξ ^ b) x) = (ξ ^ a) x := by
        rw [← MulAut.mul_apply, ← pow_add, Nat.sub_add_cancel hle]
      have h3 : (ξ ^ (a - b)) ((ξ ^ b) x) = (ξ ^ b) x := h2.trans hab
      have h4 : ξ ^ (a - b) = 1 := by
        by_contra hc
        exact hne1 b (hξ.fpf (a - b) hc ((ξ ^ b) x) h3)
      have h5 : orderOf ξ ∣ a - b := orderOf_dvd_iff_pow_eq_one.mpr h4
      have h6 : a - b < orderOf ξ := lt_of_le_of_lt (Nat.sub_le a b) ha
      rcases Nat.eq_zero_or_pos (a - b) with h0 | hpos
      · omega
      · exact absurd (Nat.le_of_dvd hpos h5) (not_le.mpr h6)
  -- the orbit of `x` is all the involutions, since it has `orderOf ξ = #Invol P` elements
  have hinj : Function.Injective (fun k : Fin (orderOf ξ) => (ξ ^ (k : ℕ)) x) := by
    intro a b hab
    exact Fin.ext (key a b a.isLt b.isLt hab)
  have hrange : Set.range (fun k : Fin (orderOf ξ) => (ξ ^ (k : ℕ)) x) = (Invol P : Set P) := by
    refine Set.eq_of_subset_of_ncard_le ?_ ?_ (Set.toFinite _)
    · rintro _ ⟨k, rfl⟩
      exact hstep k
    · rw [Set.ncard_range_of_injective hinj, Nat.card_fin, ← hInvol]
  obtain ⟨k, hk⟩ : y ∈ Set.range (fun k : Fin (orderOf ξ) => (ξ ^ (k : ℕ)) x) := by
    rw [hrange]
    exact hy
  exact ⟨(k : ℕ), hk⟩

end Work.Higman.LayersAlt
