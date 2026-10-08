import Mathlib
import Submission.Work.AppXIShadow.Basic
import Submission.Work.AppXIShadow.AppII7
import Submission.Work.AppXIShadow.ncard_of_insert_range_card

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.AppXIShadow.card_fixP_eq_card_CQ_add_one`

In the standing context `CtxF H Q t s r P` of Peterfalvi II Ch. V §3, the fixed points of `P`
on `Ω = G ⧸ H` are the base point `∞ = H` together with the `C_Q(P)`-translates of `t • ∞`,
and the map `y ↦ y • (t • ∞)` is injective on `C_Q(P)`; hence

  `|fixP H P| = |C_Q(P)| + 1`.

The input is App. II (7) (`Work.AppXIShadow.CQ_regular_on_fixP`): `∞ ∈ fixP H P` and every
`ω ∈ fixP H P`, `ω ≠ ∞` has a *unique* preimage under `y ↦ y • (t • ∞)`, `y ∈ C_Q(P)`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open Classical LeanEval.GroupTheory.Defs Submission.Blueprint

namespace Work.AppXIShadow

open Work.ThmF.ChV3

theorem card_fixP_eq_card_CQ_add_one {G : Type} [Group G] [Finite G] {H Q : Subgroup G}
    {t s r : G} {P : Subgroup G} (c : Work.ThmF.ChV3.CtxF H Q t s r P) :
    Nat.card ↥(Work.AppXIShadow.fixP H P) = Nat.card ↥(Work.ThmF.ChV3.CQ Q P) + 1 := by
  classical
  have hreg := (CQ_regular_on_fixP c).2
  have htfix : ((t : G) : G ⧸ H) ∈ fixP H P := (CQ_regular_on_fixP c).1
  have htne : ((t : G) : G ⧸ H) ≠ ((1 : G) : G ⧸ H) :=
    (Work.ZassenhausTwoGroup.IsTIQ.basePt_ne_iff H t).mpr c.split.not_mem
  set β : ↥(CQ Q P) → G ⧸ H := fun y => (y : G) • ((t : G) : G ⧸ H) with hβ
  -- `y • (t • ∞)` is a fixed point of `P` for every `y ∈ C_Q(P)`
  have hβmem : ∀ y : ↥(CQ Q P), β y ∈ fixP H P := by
    intro y
    rw [hβ]
    intro x hx
    have hyx : x * (y : G) = (y : G) * x := Subgroup.mem_centralizer_iff.mp y.2.2 x hx
    rw [← mul_smul, hyx, mul_smul, smul_t_eq_t c hx]
  -- `fixP H P` is the base point together with the `C_Q(P)`-translates of `t • ∞`
  have hset : fixP H P = insert ((1 : G) : G ⧸ H) (Set.range β) := by
    apply Set.Subset.antisymm
    · intro ω hω
      by_cases h0 : ω = ((1 : G) : G ⧸ H)
      · exact Set.mem_insert_iff.mpr (Or.inl h0)
      · obtain ⟨⟨y, hy⟩, hyω, -⟩ := hreg ω hω h0
        exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_range.mpr ⟨⟨y, hy⟩, by
          rw [hβ]
          exact hyω⟩))
    · intro ω hω
      rcases Set.mem_insert_iff.mp hω with h | ⟨y, hy⟩
      · rw [h]; exact one_mem_fixP c
      · rw [← hy]; exact hβmem y
  -- the base point is not a translate of `t • ∞`
  have hbase : ((1 : G) : G ⧸ H) ∉ Set.range β := by
    rintro ⟨y, hy⟩
    have hyH : (y : G) ∈ H := CQ_le_H c y.2
    have h1 := congrArg (fun ω : G ⧸ H => ((y : G))⁻¹ • ω) hy
    have h3 : ((y : G))⁻¹ • β y = ((t : G) : G ⧸ H) := by
      rw [hβ, ← mul_smul, inv_mul_cancel, one_smul]
    have h2 : ((y : G))⁻¹ • ((1 : G) : G ⧸ H) = ((1 : G) : G ⧸ H) :=
      Work.ZassenhausTwoGroup.IsTIQ.smul_basePt_of_mem H (H.inv_mem hyH)
    rw [h3, h2] at h1
    exact htne h1
  -- `y ↦ y • (t • ∞)` is injective on `C_Q(P)` (uniqueness in App. II (7))
  have hinj : Function.Injective β := by
    intro y y' h
    obtain ⟨z, hz, huniq⟩ := hreg ((t : G) : G ⧸ H) htfix htne
    have hp1 : ((⟨1, (CQ Q P).one_mem⟩ : ↥(CQ Q P)) : G) • ((t : G) : G ⧸ H) =
        ((t : G) : G ⧸ H) := by
      rw [Work.ThreePoints.smul_mk, one_mul]
    have hp2 : ((⟨(y : G)⁻¹ * (y' : G),
        (CQ Q P).mul_mem ((CQ Q P).inv_mem y.2) y'.2⟩ : ↥(CQ Q P)) : G) •
          ((t : G) : G ⧸ H) = ((t : G) : G ⧸ H) := by
      show ((y : G)⁻¹ * (y' : G)) • ((t : G) : G ⧸ H) = ((t : G) : G ⧸ H)
      rw [mul_smul]
      have h1 : ((y : G))⁻¹ • β y' = ((t : G) : G ⧸ H) := by
        rw [← h, hβ, ← mul_smul, inv_mul_cancel, one_smul]
      simpa only [hβ] using h1
    have hEq : (⟨(y : G)⁻¹ * (y' : G),
        (CQ Q P).mul_mem ((CQ Q P).inv_mem y.2) y'.2⟩ : ↥(CQ Q P)) =
        ⟨1, (CQ Q P).one_mem⟩ :=
      (huniq _ hp2).trans (huniq _ hp1).symm
    have hval : (y : G)⁻¹ * (y' : G) = 1 := congrArg Subtype.val hEq
    refine Subtype.ext ?_
    calc (y : G) = (y : G) * ((y : G)⁻¹ * (y' : G)) := by rw [hval, mul_one]
      _ = (y' : G) := by group
  calc Nat.card ↥(fixP H P) = (fixP H P).ncard := Nat.card_coe_set_eq (fixP H P)
    _ = Nat.card ↥(CQ Q P) + 1 := ncard_of_insert_range_card hset hbase hinj

end Work.AppXIShadow
