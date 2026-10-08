import Mathlib
import Submission.Work.Coprime.Defs
import Submission.Work.Coprime.Basic
import Submission.Work.Coprime.fixedPoints_ne_bot_of_isPGroup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped Pointwise

namespace Work.Coprime.PxQUtil

universe u v

/-- The commutator `[G, P]` maps onto `[G ⧸ N, P]` for a `P`-invariant normal subgroup `N`. -/
private theorem map_commutator_quotient (P : Type u) {G : Type v} [Group P] [Group G]
    [MulDistribMulAction P G] (N : Subgroup G) [N.Normal] [FT.IsInvariant P N] :
    (FT.commutator P (⊤ : Subgroup G)).map (QuotientGroup.mk' N)
      = FT.commutator P (⊤ : Subgroup (G ⧸ N)) := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    refine FT.commutator_le (H := (⊤ : Subgroup G))
      (K := (FT.commutator P (⊤ : Subgroup (G ⧸ N))).comap (QuotientGroup.mk' N)) fun a x _ => ?_
    rw [Subgroup.mem_comap]
    have hkey : (QuotientGroup.mk' N) (x⁻¹ * (a • x))
        = ((QuotientGroup.mk' N) x)⁻¹ * (a • (QuotientGroup.mk' N) x) := by
      rw [map_mul, map_inv]
      rfl
    rw [hkey]
    exact FT.le_commutator a trivial
  · refine FT.commutator_le (H := (⊤ : Subgroup (G ⧸ N)))
      (K := (FT.commutator P (⊤ : Subgroup G)).map (QuotientGroup.mk' N)) fun a x _ => ?_
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N x
    refine Subgroup.mem_map.mpr ⟨g⁻¹ * (a • g), FT.le_commutator a trivial, ?_⟩
    rw [map_mul, map_inv]
    rfl

/-- **A finite `p`-group of automorphisms of a finite `p`-group has proper commutator.**

If `P` is a finite `p`-group acting by automorphisms on a nontrivial finite `p`-group `G`,
then `[G, P] ≠ G`.  The proof is by strong induction on `|G|`: in the non-abelian case
quotient by the (nontrivial, proper, `P`-invariant) centre, in the abelian case by the
(possibly trivial) fixed point subgroup `C_G(P)`; when `P` acts trivially one concludes
`[G,P] = 1 ≠ G`. -/
private theorem commutator_ne_top_aux (p : ℕ) (hp : p.Prime) (P : Type u) [Group P] [Finite P]
    (hP : IsPGroup p P) :
    ∀ (n : ℕ) (G : Type v) [Group G] [Finite G] [MulDistribMulAction P G],
      Nat.card G = n → IsPGroup p G → Nontrivial G → FT.commutator P (⊤ : Subgroup G) ≠ ⊤ := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro n
  refine Nat.strong_induction_on (p := fun n => ∀ (G : Type v) [Group G] [Finite G]
      [MulDistribMulAction P G], Nat.card G = n → IsPGroup p G → Nontrivial G →
      FT.commutator P (⊤ : Subgroup G) ≠ ⊤) n ?_
  intro m ih G _ _ _ hcard hG hnt
  haveI : Nontrivial G := hnt
  -- Quotient by a nontrivial proper `P`-invariant normal subgroup and apply the IH.
  have hstep : ∀ (N : Subgroup G) [N.Normal] [FT.IsInvariant P N], Nontrivial ↥N → N ≠ ⊤ →
      FT.commutator P (⊤ : Subgroup G) ≠ ⊤ := by
    intro N hNn hNi hNnt hNtop hcomm
    haveI := hNn
    haveI := hNi
    have hcard_lt : Nat.card (G ⧸ N) < Nat.card G := by
      have h1 : Nat.card G = Nat.card (G ⧸ N) * Nat.card ↥N :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup N
      have h2 : 1 < Nat.card ↥N := Finite.one_lt_card
      have h3 : 0 < Nat.card (G ⧸ N) := Nat.card_pos
      nlinarith
    have hntq : Nontrivial (G ⧸ N) := QuotientGroup.nontrivial_iff.mpr hNtop
    have hpq : IsPGroup p (G ⧸ N) := hG.to_quotient N
    have hmap := map_commutator_quotient P N
    rw [hcomm, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)] at hmap
    exact ih (Nat.card (G ⧸ N)) (hcard ▸ hcard_lt) (G ⧸ N) rfl hpq hntq hmap.symm
  by_cases hab : IsMulCommutative G
  · -- abelian case: quotient by the fixed points
    haveI : IsMulCommutative G := hab
    haveI : FT.IsInvariant P (FT.fixedPoints P G) := inferInstance
    haveI : (FT.fixedPoints P G).Normal := inferInstance
    by_cases htop : FT.fixedPoints P G = ⊤
    · -- the action is trivial, so `[G, P] = 1`
      intro hcomm
      have htriv : FT.IsTrivialOn P G := FT.fixedPoints_eq_top_iff.mp htop
      have hbot : FT.commutator P (⊤ : Subgroup G) = ⊥ := FT.commutator_eq_bot_iff.mpr htriv
      rw [hbot] at hcomm
      exact bot_ne_top hcomm
    · exact hstep (FT.fixedPoints P G)
        ((Subgroup.nontrivial_iff_ne_bot _).mpr
          (fixedPoints_ne_bot_of_isPGroup P p hp hP hG hnt)) htop
  · -- non-abelian case: quotient by the centre
    have hZne : Subgroup.center G ≠ ⊤ := fun h => hab (Subgroup.center_eq_top_iff.mp h)
    haveI : (Subgroup.center G).Normal := Subgroup.instNormalCenter
    haveI : FT.IsInvariant P (Subgroup.center G) := inferInstance
    exact hstep (Subgroup.center G) (IsPGroup.center_nontrivial hG) hZne

theorem commutator_ne_top_of_isPGroup (p : ℕ) (hp : p.Prime) {P G : Type*} [Group P] [Group G]
    [Finite P] [Finite G] [MulDistribMulAction P G] (hP : IsPGroup p P) (hG : IsPGroup p G)
    (hnt : Nontrivial G) : FT.commutator P (⊤ : Subgroup G) ≠ ⊤ :=
  commutator_ne_top_aux p hp P hP (Nat.card G) G rfl hG hnt

end Work.Coprime.PxQUtil
