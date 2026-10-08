import Mathlib
import Submission.Work.PSU3.BenderST
import Submission.Work.PSU3.BenderST.Defs
import Submission.Work.PSU3.BenderST.transport
import Submission.Work.PSU3.BenderST.reduction

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.PSU3.BenderST.transfer` — from the standard datum of a Bender pair to arbitrary data

`Work.PSU3.BenderST.StdClause P` is the three-way conclusion of `BenderSTProp` for the
*standard* split rank-one datum `(P.B, P.U, P.w)` of a `BenderPair`.  This file shows

* `stConcl_iso` — the conclusion `STConcl` is invariant under a group isomorphism;
* `benderSTProp_of_stdClause` — it transfers to **every** split rank-one datum `(B,U,w)` of
  the group: by `split_datum_conj_standard` the datum is conjugate to the standard one, and
  each clause of `StdClause` is invariant under conjugation.
-/

set_option autoImplicit false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint (involutions twoPoint IsAbelianSubgroup IsSplitRankOne)

namespace Work.PSU3.BenderST

/-- The three-way conclusion of `BenderSTProp` for the datum `(B,U,w)` and the pair `(s,r)`
(the body of `BenderSTProp`, with `q = #Inv(B) + 1`). -/
def STConcl {G : Type} [Group G] (B U : Subgroup G) (w s r : G) : Prop :=
  let q := (involutions (B : Set G)).ncard + 1
  (orderOf (s * w) = 3 ∧ IsAbelianSubgroup U ∧ Nat.card U = q) ∨
  (orderOf (s * w) = 5 ∧ ¬ IsAbelianSubgroup U ∧ Nat.card U = q ^ 2 ∧
    ∀ x ∈ U, ∀ y ∈ U, x ^ 2 = y ^ 2 →
      x * y⁻¹ ∈ Subgroup.closure (involutions (U : Set G))) ∨
  (orderOf (s * w) = 3 ∧ Nat.card U = q ^ 3 ∧
    ∃ x ∈ twoPoint B w, x ≠ 1 ∧ ∀ u ∈ involutions (B : Set G), x * u = u * x)

/-- `StdClause` is the same predicate read on the standard datum. -/
theorem stdClause_iff (G : Type) [Group G] [Finite G] (P : Submission.BenderPair G) :
    StdClause P ↔ ∀ s r : G, s ∈ P.U → orderOf s = 2 → r ∈ P.U →
      P.w * s * P.w = r⁻¹ * P.w * r → STConcl P.B P.U P.w s r := Iff.rfl

/-- `STConcl` is invariant under a group isomorphism. -/
theorem stConcl_iso {Y M : Type} [Group Y] [Group M] (e : Y ≃* M)
    {B U : Subgroup Y} {w s r : Y}
    (h : STConcl (B.map e.toMonoidHom) (U.map e.toMonoidHom) (e w) (e s) (e r)) :
    STConcl B U w s r := by
  have hord : orderOf (s * w) = orderOf (e s * e w) := by
    have h1 : orderOf (e (s * w)) = orderOf (s * w) :=
      orderOf_injective e.toMonoidHom e.injective (s * w)
    rw [← h1, map_mul]
  have hUc : Nat.card ↥(U.map e.toMonoidHom) = Nat.card ↥U :=
    Subgroup.card_map_of_injective e.injective
  have hBc : (involutions ((B.map e.toMonoidHom) : Set M)).ncard =
      (involutions (B : Set Y)).ncard := ncard_involutions_map e B
  have hDmap : twoPoint (B.map e.toMonoidHom) (e w) = (twoPoint B w).map e.toMonoidHom :=
    twoPoint_map e B w
  have hclmap : Subgroup.closure (involutions ((U.map e.toMonoidHom) : Set M)) =
      (Subgroup.closure (involutions (U : Set Y))).map e.toMonoidHom := by
    rw [involutions_map_eq e U]
    exact (MonoidHom.map_closure e.toMonoidHom (involutions (U : Set Y))).symm
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3⟩
  · refine Or.inl ⟨?_, ?_, ?_⟩
    · rw [hord]; exact h1
    · exact (isAbelianSubgroup_map e U).mp h2
    · rw [← hUc, ← hBc]; exact h3
  · refine Or.inr (Or.inl ⟨?_, ?_, ?_, ?_⟩)
    · rw [hord]; exact h1
    · intro hab
      exact h2 ((isAbelianSubgroup_map e U).mpr hab)
    · rw [← hUc, ← hBc]; exact h3
    · intro x hx y hy hxy
      have hxy' : (e x) ^ 2 = (e y) ^ 2 := by rw [← map_pow, ← map_pow, hxy]
      have h4' := h4 (e x) (Subgroup.mem_map_of_mem e.toMonoidHom hx)
        (e y) (Subgroup.mem_map_of_mem e.toMonoidHom hy) hxy'
      rw [hclmap] at h4'
      obtain ⟨z, hz, hze⟩ := Subgroup.mem_map.mp h4'
      have hzx : z = x * y⁻¹ := e.injective (by
        show e.toMonoidHom z = e.toMonoidHom (x * y⁻¹)
        rw [hze, map_mul, map_inv, MulEquiv.coe_toMonoidHom])
      rwa [hzx] at hz
  · refine Or.inr (Or.inr ⟨?_, ?_, ?_⟩)
    · rw [hord]; exact h1
    · rw [← hUc, ← hBc]; exact h2
    · obtain ⟨x', hx'D, hx'1, hx'cent⟩ := h3
      have hx'D' : x' ∈ (twoPoint B w).map e.toMonoidHom := by rwa [← hDmap]
      obtain ⟨x, hxD, hxe⟩ := Subgroup.mem_map.mp hx'D'
      refine ⟨x, hxD, ?_, ?_⟩
      · intro hx1
        exact hx'1 (by rw [← hxe, hx1, map_one])
      · intro u hu
        have hu' : e u ∈ involutions ((B.map e.toMonoidHom) : Set M) := by
          rw [involutions_map_eq e B]
          exact ⟨u, hu, rfl⟩
        have hcent := hx'cent (e u) hu'
        have hxex : e x = x' := hxe
        refine e.injective ?_
        rw [map_mul, map_mul, hxex]
        exact hcent

/-- **The transfer**: if the standard datum of a Bender pair satisfies the (three-way)
conclusion of `BenderSTProp`, then so does every split rank-one datum of the group. -/
theorem benderSTProp_of_stdClause {G : Type} [Group G] [Finite G]
    (P : Submission.BenderPair G) (hstd : IsSplitRankOne P.B P.U P.w) (hC : StdClause P)
    {B U : Subgroup G} {w : G} (h : IsSplitRankOne B U w)
    (s r : G) (hs : s ∈ U) (hs2 : orderOf s = 2) (hr : r ∈ U)
    (hsr : w * s * w = r⁻¹ * w * r) : STConcl B U w s r := by
  obtain ⟨g, hgB, hgU, hgw⟩ := datum_conj_standard P hstd h
  set e : G ≃* G := MulAut.conj g with he
  have heB : B.map e.toMonoidHom = P.B := hgB
  have heU : U.map e.toMonoidHom = P.U := hgU
  have hew : e w = P.w := hgw
  have hmem : ∀ {x : G}, x ∈ U → e x ∈ P.U := by
    intro x hx
    have : e x ∈ U.map e.toMonoidHom := Subgroup.mem_map_of_mem e.toMonoidHom hx
    rwa [heU] at this
  have hs2' : orderOf (e s) = 2 := by
    simpa using (orderOf_injective e.toMonoidHom e.injective s).trans hs2
  have hsr' : P.w * e s * P.w = (e r)⁻¹ * P.w * (e r) := by
    have h1 : e (w * s * w) = e (r⁻¹ * w * r) := by rw [hsr]
    simp only [map_mul, map_inv] at h1
    rwa [hew] at h1
  refine stConcl_iso e ?_
  rw [heB, heU, hew]
  exact hC (e s) (e r) (hmem hs) hs2' (hmem hr) hsr'

end Work.PSU3.BenderST
