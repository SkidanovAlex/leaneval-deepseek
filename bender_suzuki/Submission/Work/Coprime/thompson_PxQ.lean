import Mathlib
import Submission.Work.Coprime.Defs
import Submission.Work.Coprime.Basic
import Submission.Work.Coprime.commutator_normal
import Submission.Work.Coprime.commutator_commutator_eq
import Submission.Work.Coprime.commutator_fixedPoints_sup
import Submission.Work.Coprime.isTrivialOn_of_commutator_le_fixedPoints
import Submission.Work.Coprime.fixedPoints_ne_bot_of_isPGroup
import Submission.Work.Coprime.PxQUtil.commutator_ne_top_of_isPGroup
import Submission.Work.Coprime.PxQUtil.commutator_eq_bot_of_commutator_eq_bot

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Thompson's `P × Q` lemma

Let `P` be a finite `p`-group and `Q` a finite `p'`-group acting by automorphisms on a finite
`p`-group `G`, the two actions commuting.  If `Q` centralises the fixed points `C_G(P)` of `P`,
then `Q` acts trivially on `G` (Thompson's `A × B` lemma, Gorenstein, *Finite Groups*, Theorem
5.3.4).

The proof is by strong induction on `|G|`.  In a minimal counterexample every proper `P × Q`-
invariant subgroup is centralised by `Q` (induction hypothesis), so:
* `[G,Q] = G`, since otherwise `[G,Q]` is a proper invariant subgroup and the coprime identity
  `[[G,Q],Q] = [G,Q]` (`commutator_commutator_eq`) yields `[G,Q] = 1`;
* `[G,P] ≠ G` because `P` and `G` are both `p`-groups (`commutator_ne_top_of_isPGroup`), so `Q`
  centralises `[G,P]`;
* the three-subgroups lemma turns this into `P` centralising `[G,Q]`
  (`commutator_eq_bot_of_commutator_eq_bot`); together with the hypothesis
  `C_G(P) ≤ C_G(Q)` this gives `[G,Q] ≤ C_G(Q)`, and `[[G,Q],Q] = [G,Q]` forces `[G,Q] = 1`.
-/

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
open scoped Pointwise

namespace Work.Coprime

universe u v w

section Helpers

variable {P : Type u} {Q : Type v} {G : Type w} [Group P] [Group Q] [Group G]
  [MulDistribMulAction P G] [MulDistribMulAction Q G] [SMulCommClass P Q G]

/-- `SMulCommClass` passes to invariant subgroups. -/
private theorem smulCommClass_subgroup (H : Subgroup G) [FT.IsInvariant P H]
    [FT.IsInvariant Q H] : SMulCommClass P Q H where
  smul_comm p q x := Subtype.ext (by
    show ((p • (q • x) : H) : G) = ((q • (p • x) : H) : G)
    rw [FT.coe_subgroup_smul, FT.coe_subgroup_smul, FT.coe_subgroup_smul, FT.coe_subgroup_smul,
      smul_comm])

/-- `SMulCommClass` is symmetric. -/
private theorem smulCommClass_symm : SMulCommClass Q P G where
  smul_comm q p x := (smul_comm p q x).symm

/-- The commutator `[G,P]` is invariant under the commuting action of `Q`. -/
private theorem isInvariant_commutator_of_smulCommClass {A : Type*} {B : Type*} {G : Type*}
    [Group A] [Group B] [Group G] [MulDistribMulAction A G] [MulDistribMulAction B G]
    [SMulCommClass A B G] : FT.IsInvariant B (FT.commutator A (⊤ : Subgroup G)) := by
  have hgen : ∀ (b : B) (a : A) (wd : G),
      b • (wd⁻¹ * (a • wd)) = (b • wd)⁻¹ * (a • (b • wd)) := fun b a wd => by
    rw [smul_mul', smul_inv', (smul_comm a b wd).symm]
  rw [Work.Coprime.commutator_eq_closure]
  refine FT.IsInvariant.closure fun b => ?_
  ext y
  simp only [Set.mem_smul_set_iff_inv_smul_mem, Work.Coprime.commutatorGens,
    Set.mem_ofPred_eq, Subgroup.mem_top, true_and]
  constructor
  · rintro ⟨a, wd, hw⟩
    refine ⟨a, b • wd, ?_⟩
    rw [← hgen b a wd, ← hw, smul_inv_smul]
  · rintro ⟨a, wd, rfl⟩
    exact ⟨a, b⁻¹ • wd, hgen b⁻¹ a wd⟩

/-- A subgroup `H` acted on by `A` is acted on trivially by `A` iff `FT.commutator A H = ⊥`. -/
private theorem commutator_subgroup_eq_bot_iff_isTrivialOn {A : Type*} {G : Type*} [Group A]
    [Group G] [MulDistribMulAction A G] (H : Subgroup G) [FT.IsInvariant A H] :
    FT.commutator A H = ⊥ ↔ FT.IsTrivialOn A H := by
  constructor
  · intro h a y
    refine Subtype.ext ?_
    have h1 : (y : G)⁻¹ * (a • (y : G)) = 1 := by
      have h2 : (y : G)⁻¹ * (a • (y : G)) ∈ (⊥ : Subgroup G) := by
        rw [← h]; exact FT.le_commutator a y.2
      simpa using h2
    calc a • (y : G) = (y : G) * ((y : G)⁻¹ * (a • (y : G))) := by group
      _ = (y : G) := by rw [h1, mul_one]
  · intro h
    refine le_bot_iff.mp ?_
    refine FT.commutator_le (fun a x hx => ?_)
    rw [Subgroup.mem_bot]
    have hv : a • x = x := by
      have := congrArg (Subtype.val) (h a ⟨x, hx⟩)
      simpa [FT.coe_subgroup_smul] using this
    rw [hv, inv_mul_cancel]

end Helpers

/-- Thompson's `A × B` lemma in the `P × Q` form, proved by strong induction on `|G|`. -/
private theorem PxQ_aux :
    ∀ (n : ℕ) {P : Type u} {Q : Type v} {G : Type w} [Group P] [Group Q] [Group G]
      [Finite P] [Finite Q] [Finite G] [MulDistribMulAction P G] [MulDistribMulAction Q G]
      [SMulCommClass P Q G],
      Nat.card G = n → ∀ (p : ℕ), p.Prime → IsPGroup p P → ¬ p ∣ Nat.card Q → IsPGroup p G →
      (Nat.card Q).Coprime (Nat.card G) →
      (∀ q : Q, ∀ x : G, (∀ pp : P, pp • x = x) → q • x = x) → FT.IsTrivialOn Q G := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n IH =>
    intro P Q G _ _ _ _ _ _ _ _ _ hcard p hp hP hQndvd hG hQG hfix
    by_cases htriv : FT.IsTrivialOn Q G
    · exact htriv
    · exfalso
      haveI : Fact p.Prime := ⟨hp⟩
      haveI hsolG : Group.IsSolvable G := by
        haveI : Group.IsNilpotent G := hG.isNilpotent
        infer_instance
      haveI hntG : Nontrivial G := by
        rw [← not_subsingleton_iff_nontrivial]
        intro hsub
        exact htriv fun q x => Subsingleton.elim _ _
      haveI hscSymm : SMulCommClass Q P G := smulCommClass_symm
      haveI hinvQ : FT.IsInvariant Q (FT.commutator P (⊤ : Subgroup G)) :=
        isInvariant_commutator_of_smulCommClass (A := P) (B := Q)
      haveI hinvP : FT.IsInvariant P (FT.commutator Q (⊤ : Subgroup G)) :=
        isInvariant_commutator_of_smulCommClass (A := Q) (B := P)
      -- **Minimality.** Every proper `P × Q`-invariant subgroup is acted on trivially by `Q`.
      have hconf : ∀ (H : Subgroup G) [FT.IsInvariant P H] [FT.IsInvariant Q H], H < ⊤ →
          FT.IsTrivialOn Q H := by
        intro H hPi hQi hHlt
        haveI := hPi
        haveI := hQi
        haveI : SMulCommClass P Q H := smulCommClass_subgroup H
        have hlt : Nat.card H < n := by
          have h1 : Nat.card H < Nat.card ↥(⊤ : Subgroup G) := Subgroup.card_lt_of_lt hHlt
          rw [Subgroup.card_top, hcard] at h1
          exact h1
        refine IH (Nat.card H) hlt rfl p hp hP hQndvd (hG.to_subgroup H)
          (hQG.coprime_dvd_right (Subgroup.card_subgroup_dvd_card H)) (fun q x hx => ?_)
        refine Subtype.ext ?_
        have hx' : q • (x : G) = (x : G) := hfix q (x : G) (fun pp => by
          have hpp := congrArg (Subtype.val) (hx pp)
          simpa [FT.coe_subgroup_smul] using hpp)
        simpa [FT.coe_subgroup_smul] using hx'
      -- **Step 1.** `[G,Q] = G`: otherwise `[G,Q]` is proper and the identity `[[G,Q],Q] = [G,Q]`
      -- for a coprime action forces `[G,Q] = 1`.
      have hGQtop : FT.commutator Q (⊤ : Subgroup G) = ⊤ := by
        by_contra hne
        have hlt : FT.commutator Q (⊤ : Subgroup G) < ⊤ := lt_top_iff_ne_top.mpr hne
        have htrivQ : FT.IsTrivialOn Q ↥(FT.commutator Q (⊤ : Subgroup G)) := hconf _ hlt
        have hbot : FT.commutator Q (FT.commutator Q (⊤ : Subgroup G)) = ⊥ :=
          (commutator_subgroup_eq_bot_iff_isTrivialOn _).mpr htrivQ
        rw [commutator_commutator_eq Q hQG (Or.inr hsolG)] at hbot
        exact htriv ((FT.commutator_eq_bot_iff).mp hbot)
      -- **Step 2.** `[G,P] < G` since `P` and `G` are both `p`-groups, hence `Q` centralises
      -- `[G,P]`, and the three-subgroups lemma gives that `P` centralises `[G,Q]`.
      have hGPne : FT.commutator P (⊤ : Subgroup G) ≠ ⊤ :=
        PxQUtil.commutator_ne_top_of_isPGroup p hp hP hG hntG
      have hGPlt : FT.commutator P (⊤ : Subgroup G) < ⊤ := lt_top_iff_ne_top.mpr hGPne
      have htrivP : FT.IsTrivialOn Q ↥(FT.commutator P (⊤ : Subgroup G)) := hconf _ hGPlt
      have hbot1 : FT.commutator Q (FT.commutator P (⊤ : Subgroup G)) = ⊥ :=
        (commutator_subgroup_eq_bot_iff_isTrivialOn _).mpr htrivP
      have hbot2 : FT.commutator P (FT.commutator Q (⊤ : Subgroup G)) = ⊥ :=
        PxQUtil.commutator_eq_bot_of_commutator_eq_bot hbot1
      have htrivPQ : FT.IsTrivialOn P ↥(FT.commutator Q (⊤ : Subgroup G)) :=
        (commutator_subgroup_eq_bot_iff_isTrivialOn _).mp hbot2
      -- **Step 3.** Hence `[G,Q] ≤ C_G(P) ≤ C_G(Q)` and `[[G,Q],Q] = [G,Q] = 1`.
      have hsub : FT.commutator Q (⊤ : Subgroup G) ≤ FT.fixedPoints P G := by
        intro x hx
        rw [FT.mem_fixedPoints]
        intro pp
        have := congrArg (Subtype.val) (htrivPQ pp ⟨x, hx⟩)
        simpa [FT.coe_subgroup_smul] using this
      have hfixle : FT.fixedPoints P G ≤ FT.fixedPoints Q G := by
        intro x hx
        rw [FT.mem_fixedPoints] at hx ⊢
        intro q
        exact hfix q x hx
      have htrivQ2 : FT.IsTrivialOn Q ↥(FT.commutator Q (⊤ : Subgroup G)) := by
        intro q y
        refine Subtype.ext ?_
        have hy : (y : G) ∈ FT.fixedPoints Q G := hfixle (hsub y.2)
        have := hy q
        simpa [FT.coe_subgroup_smul] using this
      have hbot3 : FT.commutator Q (FT.commutator Q (⊤ : Subgroup G)) = ⊥ :=
        (commutator_subgroup_eq_bot_iff_isTrivialOn _).mpr htrivQ2
      rw [commutator_commutator_eq Q hQG (Or.inr hsolG)] at hbot3
      exact htriv ((FT.commutator_eq_bot_iff).mp hbot3)

/-- **Thompson's `P × Q` lemma.** Let `P` be a `p`-group and `Q` a `p'`-group of automorphisms of
a `p`-group `G`, with commuting actions.  If every element of `G` fixed by `P` is fixed by `Q`,
then `Q` acts trivially on `G`. -/
theorem thompson_PxQ (p : ℕ) (hp : p.Prime) {P Q G : Type*} [Group P] [Group Q] [Group G]
    [Finite P] [Finite Q] [Finite G] [MulDistribMulAction P G] [MulDistribMulAction Q G]
    [SMulCommClass P Q G] (hP : IsPGroup p P) (hQ : ¬ p ∣ Nat.card Q) (hG : IsPGroup p G)
    (hQG : (Nat.card Q).Coprime (Nat.card G))
    (hfix : ∀ q : Q, ∀ x : G, (∀ pp : P, pp • x = x) → q • x = x) : FT.IsTrivialOn Q G :=
  PxQ_aux (Nat.card G) rfl p hp hP hQ hG hQG hfix

end Work.Coprime
