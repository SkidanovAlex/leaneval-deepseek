import Mathlib
import Submission.Work.ZassenhausSuzuki.Odd.OddDefs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Two Sylow `2`-subgroups sharing a non-trivial element coincide (TI case)

Let `Q` be a Sylow `2`-subgroup which is *TI with respect to a subgroup* `H ≥ N_G(Q)`:
`Q ∩ Qˣ = 1` for every `x ∉ H`.  Note that then `H = N_G(Q)` (unless `Q = 1`): for
`x ∈ N_G(Q) \ H` the hypothesis would give `Q = Q ∩ Qˣ = 1`.

The point of the lemma is that *every* Sylow `2`-subgroup meeting `Q` non-trivially is `Q`.
Indeed, if `S = Q^a` is any Sylow `2`-subgroup and `S ∩ Q ≠ 1`, then conjugeting by `a⁻¹`
gives `Q ∩ Q^{a⁻¹} ≠ 1`, so `a⁻¹ ∈ N_G(Q) = H`, so `S = Q`.  Consequently two arbitrary
Sylow `2`-subgroups `P`, `P'` sharing a non-identity element `x` are equal: write
`P' = Q^a`; then `a⁻¹ x a ∈ Q` and `a⁻¹ x a ∈ P^{a⁻¹}`, so `P^{a⁻¹}` meets `Q` non-trivially,
whence `P^{a⁻¹} = Q` and `P = Q^a = P'`.
-/

set_option autoImplicit false

open Submission.Blueprint
open scoped Pointwise

namespace Work.ZassenhausSuzuki.Odd

/-- Membership in a conjugate `g H g⁻¹ = H.map (MulAut.conj g)`. -/
private lemma mem_conj_iff {G : Type} [Group G] {g : G} {H : Subgroup G} {x : G} :
    x ∈ Submission.Blueprint.conj g H ↔ g⁻¹ * x * g ∈ H := by
  have h : Submission.Blueprint.conj g H = MulAut.conj g • H := rfl
  rw [h, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def]
  simp only [MulAut.inv_apply, MulAut.conj_symm_apply]

/-- Conjugating by `g` undoes conjugating by `g⁻¹`. -/
private lemma conj_conj_inv {G : Type} [Group G] (g : G) (H : Subgroup G) :
    Submission.Blueprint.conj g (Submission.Blueprint.conj g⁻¹ H) = H := by
  ext x
  rw [mem_conj_iff, mem_conj_iff]
  rw [show (g⁻¹)⁻¹ * (g⁻¹ * x * g) * g⁻¹ = x by group]

theorem sylow_eq_of_mem {G : Type} [Group G] [Finite G] {H Q : Subgroup G}
    (hTI : ∀ g : G, g ∉ H → Q ⊓ Submission.Blueprint.conj g Q = ⊥)
    (hHle : H ≤ Subgroup.normalizer (Q : Set G))
    (P₀ : Sylow 2 G) (hP0 : (P₀ : Subgroup G) = Q)
    {P P' : Sylow 2 G} {x : G} (hx : x ≠ 1) (hxP : x ∈ P) (hxP' : x ∈ P') : P = P' := by
  -- `H` contains the normalizer of `Q`: if `a ∈ N_G(Q)` but `a ∉ H`, TI gives `Q = ⊥`.
  have TI : ∀ a : G, Q ⊓ Submission.Blueprint.conj a Q ≠ ⊥ →
      Submission.Blueprint.conj a Q = Q := by
    intro a h
    by_contra hne
    by_cases ha : a ∈ H
    · exact hne (Subgroup.mem_normalizer_iff_map_conj_eq.mp (hHle ha))
    · exact h (hTI a ha)
  -- Any Sylow `2`-subgroup meeting `Q` non-trivially equals `Q`.
  have key : ∀ S : Sylow 2 G, (S : Subgroup G) ⊓ Q ≠ ⊥ → (S : Subgroup G) = Q := by
    intro S hS
    obtain ⟨a, ha⟩ := MulAction.exists_smul_eq G P₀ S
    have hSeq : (S : Subgroup G) = Submission.Blueprint.conj a Q := by
      rw [← ha, Sylow.coe_subgroup_smul, hP0]
      rfl
    have hinf : Q ⊓ Submission.Blueprint.conj a Q ≠ ⊥ := by
      rw [hSeq] at hS
      rwa [inf_comm] at hS
    rw [hSeq, TI a hinf]
  -- Now write `P' = Q^a` for some `a`.
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq G P₀ P'
  have hP'eq : (P' : Subgroup G) = Submission.Blueprint.conj a Q := by
    rw [← ha, Sylow.coe_subgroup_smul, hP0]
    rfl
  have hyQ : a⁻¹ * x * a ∈ Q := by
    have : x ∈ Submission.Blueprint.conj a Q := by rw [← hP'eq]; exact hxP'
    rwa [mem_conj_iff] at this
  have hyP : a⁻¹ * x * a ∈ ((a⁻¹ • P : Sylow 2 G) : Subgroup G) := by
    rw [Sylow.coe_subgroup_smul]
    change a⁻¹ * x * a ∈ Submission.Blueprint.conj a⁻¹ (P : Subgroup G)
    rw [mem_conj_iff]
    rw [show (a⁻¹)⁻¹ * (a⁻¹ * x * a) * a⁻¹ = x by group]
    exact hxP
  have hne : ((a⁻¹ • P : Sylow 2 G) : Subgroup G) ⊓ Q ≠ ⊥ := by
    intro hbot
    have hmem : a⁻¹ * x * a = 1 := by
      have : a⁻¹ * x * a ∈ (⊥ : Subgroup G) := by rw [← hbot]; exact ⟨hyP, hyQ⟩
      rwa [Subgroup.mem_bot] at this
    exact hx (by
      have h : x = a * (a⁻¹ * x * a) * a⁻¹ := by group
      rw [h, hmem]
      group)
  have hS : ((a⁻¹ • P : Sylow 2 G) : Subgroup G) = Q := key (a⁻¹ • P) hne
  -- Undo the conjugation: `P = Q^a = P'`.
  have hconj : Submission.Blueprint.conj a Q = (P : Subgroup G) := by
    have h1 : ((a⁻¹ • P : Sylow 2 G) : Subgroup G)
        = Submission.Blueprint.conj a⁻¹ (P : Subgroup G) := by
      rw [Sylow.coe_subgroup_smul]; rfl
    rw [h1] at hS
    have := congrArg (Submission.Blueprint.conj a) hS
    rw [conj_conj_inv] at this
    exact this.symm
  exact Sylow.ext (hconj.symm.trans hP'eq.symm)

end Work.ZassenhausSuzuki.Odd
