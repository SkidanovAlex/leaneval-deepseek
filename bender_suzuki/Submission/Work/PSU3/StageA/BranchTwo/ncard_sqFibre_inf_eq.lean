import Mathlib
import Submission.Work.PSU3.StageA.BranchTwo.sq_mem_Q0sub
import Submission.Work.PSU3.StageA.caseC_data
import Submission.Work.PSU3.StageA.centD_eq_centralizer_s

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.PSU3.StageA.BranchTwo.ncard_sqFibre_inf_eq`

Branch (ii) of Peterfalvi II Ch. V §2 Lemma 2 c) (`lemma2cHig`) is the "Sz"-configuration: for
the structure-identity data `(s, r)` and a prime-order `P ≤ V = centD H t`, with

  `C = Q ⊓ C_G(P)`,  `ℓ = |Q0sub H ⊓ C_G(P)|`,

one has `|C| = ℓ²` and equal squares in `C` differ by an element of `Q0sub H`.  In this branch
`C` is a group of order `ℓ²` in which *every square lies in* `K := Q0sub H ⊓ C_G(P)`
(Higman: in the Suzuki `2`-group `Q` every square is central, `Z(Q) = Q0sub H`; and squares of
elements of `C_G(P)` centralise `P`) and in which the fibres of the squaring map are contained in
cosets of `K`.  Consequently the fibres over the `ℓ` elements of `K` form a partition of `C` into
`ℓ` parts, each of size `≤ ℓ`, so each has exactly `ℓ` elements:

  `#{x ∈ Q ⊓ C_G(P) | x² = s} = |Q0sub H ⊓ C_G(P)|`.

This is the statement proved here, with no use of the branch hypotheses beyond the two numerical
ones (`|C| = ℓ²`, equal squares lie in `Q0sub H`).

## Contents

* `card_sqFiber_eq_card_of_card_sq` — the abstract counting lemma (a finite group `X` with a
  subgroup `K` such that `|X| = |K|²`, all squares lie in `K`, and `x² = y² → x y⁻¹ ∈ K`: then
  every squaring fibre over an element of `K` has exactly `|K|` elements).
* `ncard_set_eq_card_subtype` — the bookkeeping identifying the fibre of squaring inside a
  subgroup, viewed as a subset of `G`, with the corresponding subtype of the subgroup.
* `ncard_sqFibre_inf_eq` — the requested statement.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.PSU3.StageA.BranchTwo

/-- **Counting the fibres of squaring.**  Let `X` be a finite group and `K ≤ X` a subgroup with

* `|X| = |K|²`,
* `x² ∈ K` for every `x ∈ X`, and
* `x² = y² → x * y⁻¹ ∈ K` for all `x y ∈ X`.

Then for every `s ∈ K` the squaring fibre `{x | x² = s}` has exactly `|K|` elements.

Indeed `x ↦ x²` maps `X` onto a subset of `K`, and its fibre over `y²` is contained in the coset
`K * y`, hence has at most `|K|` elements.  As the fibres over the `|K|` elements of `K`
partition `X`, a sum of `|K|` terms each `≤ |K|` equals `|K|²`, so each term is `|K|`. -/
theorem card_sqFiber_eq_card_of_card_sq {X : Type*} [Group X] [Finite X] (K : Subgroup X)
    (hcard : Nat.card X = Nat.card K ^ 2)
    (hmem : ∀ x : X, x ^ 2 ∈ K)
    (hfib : ∀ x y : X, x ^ 2 = y ^ 2 → x * y⁻¹ ∈ K) :
    ∀ s ∈ K, Nat.card {x : X // x ^ 2 = s} = Nat.card K := by
  classical
  haveI : Fintype ↥K := Fintype.ofFinite _
  intro s hs
  -- the fibres over the elements of `K` partition `X`
  have hsum : Nat.card X = ∑ u : ↥K, Nat.card {x : X // x ^ 2 = (u : X)} := by
    have e : (Σ u : ↥K, {x : X // x ^ 2 = (u : X)}) ≃ X :=
      { toFun := fun p => p.2.1
        invFun := fun x => ⟨⟨x ^ 2, hmem x⟩, ⟨x, rfl⟩⟩
        left_inv := fun p => by
          obtain ⟨u, x, hx⟩ := p
          have hu : u = ⟨x ^ 2, hmem x⟩ := Subtype.ext hx.symm
          subst hu
          rfl
        right_inv := fun x => rfl }
    rw [← Nat.card_congr e, Nat.card_sigma]
  -- each fibre has at most `|K|` elements
  have hle : ∀ u : ↥K, Nat.card {x : X // x ^ 2 = (u : X)} ≤ Nat.card K := by
    intro u
    by_cases h : Nonempty {x : X // x ^ 2 = (u : X)}
    · obtain ⟨x0, hx0⟩ := h
      -- `y ↦ x0 * y⁻¹` injects the fibre over `u` into `K`
      refine Nat.card_le_card_of_injective
        (fun y : {x : X // x ^ 2 = (u : X)} =>
          (⟨x0 * y.1⁻¹, hfib x0 y.1 (by rw [hx0, y.2])⟩ : ↥K)) ?_
      intro a b hab
      have h1 : x0 * a.1⁻¹ = x0 * b.1⁻¹ := congrArg Subtype.val hab
      have h2 : a.1⁻¹ = b.1⁻¹ := mul_left_cancel h1
      exact Subtype.ext (inv_injective h2)
    · have h0 : Nat.card {x : X // x ^ 2 = (u : X)} = 0 :=
        Nat.card_eq_zero.mpr (Or.inl (not_nonempty_iff.mp h))
      rw [h0]; exact Nat.zero_le _
  -- the sum of the constants is `|K|² = |X|`, so every fibre has exactly `|K|` elements
  have hsumK : (∑ _u : ↥K, Nat.card K) = Nat.card K ^ 2 := by
    rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, nsmul_eq_mul,
      pow_two, Nat.cast_id, Nat.mul_comm]
  have heq : (∑ u : ↥K, Nat.card {x : X // x ^ 2 = (u : X)}) = ∑ _u : ↥K, Nat.card K := by
    rw [← hsum, hcard, hsumK]
  have hall := (Finset.sum_eq_sum_iff_of_le
    (fun u (_ : u ∈ Finset.univ) => hle u)).mp heq
  simpa using hall ⟨s, hs⟩

/-- The fibre of the squaring map inside a subgroup `C`, viewed as a subset of the ambient group,
has the cardinality of the corresponding subtype of `C`. -/
theorem ncard_set_eq_card_subtype {G : Type*} [Group G] (C : Subgroup G) (s : G) :
    {x : G | x ∈ C ∧ x ^ 2 = s}.ncard = Nat.card {x : ↥C // (x : G) ^ 2 = s} := by
  rw [← Nat.card_coe_set_eq]
  exact Nat.card_congr
    { toFun := fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩
      invFun := fun y => ⟨y.1.1, y.1.2, y.2⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

/-- **Bender–Suzuki, Stage A, branch (ii): the squaring fibre inside `Q ⊓ C_G(P)`.**

In the local configuration of Peterfalvi II Ch. V §2 Lemma 2 c) (ii), the number of square roots
of the distinguished involution `s` inside the centraliser `C = Q ⊓ C_G(P)` is exactly
`ℓ = |Q0sub H ⊓ C_G(P)|`.

The two numerical hypotheses are `|C| = ℓ²` and the fact that equal squares in `C` differ by an
element of `Q0sub H`; `C` is `2`-closed (it is a subgroup of the `2`-group `Q`), squares in `C`
are central in `Q` (`sq_mem_Q0sub`), hence lie in `Q0sub H ⊓ C_G(P)`, and a coset argument
finishes the count (`card_sqFiber_eq_card_of_card_sq`). -/
theorem ncard_sqFibre_inf_eq {G : Type} [Group G] [Finite G]
    {H Q : Subgroup G} {t : G} {P : Subgroup G}
    (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    (hFT : Submission.Blueprint.FeitThompsonProp)
    (hnab : ¬ Submission.Blueprint.IsAbelianSubgroup Q)
    {s : G} (hs : s ∈ Q) (hs2 : orderOf s = 2) (hs1 : s ≠ 1)
    (hP : P ≤ Submission.Blueprint.centD H t) (hp : (Nat.card P).Prime)
    (hscP : s ∈ Subgroup.centralizer (P : Set G))
    (hcardC : Nat.card ↥(Q ⊓ Subgroup.centralizer (P : Set G)) =
      Nat.card ↥(Work.ThmF.Q0sub H ⊓ Subgroup.centralizer (P : Set G)) ^ 2)
    (heqsq : ∀ x ∈ Q ⊓ Subgroup.centralizer (P : Set G),
      ∀ y ∈ Q ⊓ Subgroup.centralizer (P : Set G),
        x ^ 2 = y ^ 2 → x * y⁻¹ ∈ Work.ThmF.Q0sub H) :
    {x : G | x ∈ Q ⊓ Subgroup.centralizer (P : Set G) ∧ x ^ 2 = s}.ncard =
      Nat.card ↥(Work.ThmF.Q0sub H ⊓ Subgroup.centralizer (P : Set G)) := by
  classical
  -- abbreviations for the two subgroups
  have hsC : s ∈ Q ⊓ Subgroup.centralizer (P : Set G) := Subgroup.mem_inf.mpr ⟨hs, hscP⟩
  have hKC : Work.ThmF.Q0sub H ⊓ Subgroup.centralizer (P : Set G) ≤
      Q ⊓ Subgroup.centralizer (P : Set G) :=
    inf_le_inf_right _ (Work.PSU3.StageA.Q0sub_le_Q hS.split)
  -- the abstract counting lemma, applied inside `↥(Q ⊓ C_G(P))`
  have hcount := card_sqFiber_eq_card_of_card_sq
    (X := ↥(Q ⊓ Subgroup.centralizer (P : Set G)))
    ((Work.ThmF.Q0sub H ⊓ Subgroup.centralizer (P : Set G)).subgroupOf
      (Q ⊓ Subgroup.centralizer (P : Set G)))
    (by
      have h1 : Nat.card ↥((Work.ThmF.Q0sub H ⊓ Subgroup.centralizer (P : Set G)).subgroupOf
          (Q ⊓ Subgroup.centralizer (P : Set G))) =
          Nat.card ↥(Work.ThmF.Q0sub H ⊓ Subgroup.centralizer (P : Set G)) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKC).toEquiv
      rw [h1]; exact hcardC)
    -- all squares of `Q ⊓ C_G(P)` lie in `Q0sub H ⊓ C_G(P)`
    (by
      intro x
      rw [Subgroup.mem_subgroupOf, Subgroup.coe_pow]
      exact Subgroup.mem_inf.mpr
        ⟨Work.PSU3.StageA.BranchTwo.sq_mem_Q0sub hS hC4 hFT hnab _ (Subgroup.mem_inf.mp x.2).1,
          Subgroup.pow_mem _ (Subgroup.mem_inf.mp x.2).2 2⟩)
    -- equal squares differ by an element of `Q0sub H ⊓ C_G(P)`
    (by
      intro x y hxy
      have hG : ((x : ↥(Q ⊓ Subgroup.centralizer (P : Set G))) : G) ^ 2 =
          ((y : ↥(Q ⊓ Subgroup.centralizer (P : Set G))) : G) ^ 2 := by
        have h := congrArg (fun z : ↥(Q ⊓ Subgroup.centralizer (P : Set G)) => (z : G)) hxy
        simpa only [Subgroup.coe_pow] using h
      rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
      exact Subgroup.mem_inf.mpr ⟨heqsq _ x.2 _ y.2 hG,
        Subgroup.mul_mem _ (Subgroup.mem_inf.mp x.2).2
          (Subgroup.inv_mem _ (Subgroup.mem_inf.mp y.2).2)⟩)
    ⟨s, hsC⟩
    -- `s` is an involution of `H`, hence lies in `Q0sub H`, and it centralises `P`
    (by
      rw [Subgroup.mem_subgroupOf]
      exact Subgroup.mem_inf.mpr
        ⟨Work.ThmF.Q0_le_Q0sub H (Work.ThmF.mem_Q0_iff.mpr (Or.inl ⟨hS.split.le hs, hs2⟩)),
          hscP⟩)
  -- bookkeeping: identify the two descriptions of the fibre and of `K`
  have hsub : Nat.card {x : ↥(Q ⊓ Subgroup.centralizer (P : Set G)) // (x : G) ^ 2 = s} =
      Nat.card {x : ↥(Q ⊓ Subgroup.centralizer (P : Set G)) // x ^ 2 = ⟨s, hsC⟩} :=
    Nat.card_congr
      { toFun := fun y => ⟨y.1, Subtype.ext (by rw [Subgroup.coe_pow]; exact y.2)⟩
        invFun := fun y => ⟨y.1, by
          have h := congrArg (fun z : ↥(Q ⊓ Subgroup.centralizer (P : Set G)) => (z : G)) y.2
          simpa only [Subgroup.coe_pow] using h⟩
        left_inv := fun y => rfl
        right_inv := fun y => rfl }
  have hKcard : Nat.card ↥((Work.ThmF.Q0sub H ⊓ Subgroup.centralizer (P : Set G)).subgroupOf
      (Q ⊓ Subgroup.centralizer (P : Set G))) =
      Nat.card ↥(Work.ThmF.Q0sub H ⊓ Subgroup.centralizer (P : Set G)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKC).toEquiv
  rw [ncard_set_eq_card_subtype (Q ⊓ Subgroup.centralizer (P : Set G)) s, hsub, hcount, hKcard]

end Work.PSU3.StageA.BranchTwo
