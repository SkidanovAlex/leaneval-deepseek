import Mathlib
import Submission.Work.Coprime.fixedPoints_quotient
import Submission.Work.Coprime.cocycle_is_coboundary
import Submission.Work.Coprime.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Gaschütz's lemma `C_{G/N}(A) = C_G(A)N/N` with a solvable coefficient

`Work.Coprime.fixedPoints_quotient` proves `C_{G/N}(A) = C_G(A)N/N` for a coprime action when
`A` or the whole group `G` is solvable.  The Appendix VII reduction of Peterfalvi I only ever
quotients by a *solvable* normal subgroup `N` (the Frattini subgroup `Φ(K)`, which is nilpotent,
or a subgroup `Z` of an abelian `K`), and reconstructing `IsSolvable G` from `IsSolvable ↥N` is
not possible in general.

This file records the version actually needed: the coefficient (the normal subgroup `N` itself)
may be the solvable side.  The proof is the same as that of `Work.Coprime.fixedPoints_quotient`,
but it feeds the hypothesis `IsSolvable A ∨ IsSolvable ↥N` directly into
`Work.Coprime.cocycle_is_coboundary_aux`, whose statement is already phrased with the coefficient
type as the possible solvable side; the induced action on `N` and the Schur–Zassenhaus machinery
underneath then give the required fixed-point identity.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open scoped Pointwise

namespace Work.Hering.AppVII

theorem fixedPoints_quotient_of_solvable_coeff {A G : Type*} [Group A] [Finite A] [Group G]
    [Finite G] [MulDistribMulAction A G] (hcop : (Nat.card A).Coprime (Nat.card G))
    (N : Subgroup G) [N.Normal] [FT.IsInvariant A N]
    (hsol : Group.IsSolvable A ∨ Group.IsSolvable ↥N) :
    (FT.fixedPoints A G).map (QuotientGroup.mk' N) = FT.fixedPoints A (G ⧸ N) := by
  refine le_antisymm (FT.map_fixedPoints_le N) ?_
  intro x hx
  rw [FT.mem_fixedPoints] at hx
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N x
  have hxg : ∀ a : A, a • (g : G ⧸ N) = (g : G ⧸ N) := by
    intro a
    have h := hx a
    rwa [QuotientGroup.mk'_apply] at h
  -- The cocycle `a ↦ g⁻¹(a • g)` with values in `N`.
  let Φ : A → ↥N := fun a => ⟨g⁻¹ * (a • g), by
    have h := hxg a
    rw [FT.quotient_smul_mk] at h
    exact QuotientGroup.eq.mp h.symm⟩
  have key : ∀ c : A, ((Φ c : ↥N) : G) = g⁻¹ * (c • g) := fun c => rfl
  have hcross : ∀ a b : A, Φ (a * b) = Φ a * (a • Φ b) := by
    intro a b
    apply Subtype.ext
    simp only [Subgroup.coe_mul, FT.coe_subgroup_smul]
    rw [key (a * b), key a, key b, smul_mul', smul_inv', mul_smul]
    group
  -- Coprimality descends to `N`.
  have hcN : (Nat.card A).Coprime (Nat.card ↥N) :=
    hcop.coprime_dvd_right ⟨N.index, (Subgroup.card_mul_index N).symm⟩
  obtain ⟨n, hn⟩ := Work.Coprime.cocycle_is_coboundary_aux A hcN hsol Φ hcross
  refine Subgroup.mem_map.mpr ⟨g * (n : G), ?_, ?_⟩
  · rw [FT.mem_fixedPoints]
    intro a
    have hn' : ((Φ a : ↥N) : G) = (n : G) * (a • (n : G))⁻¹ := by
      have := congrArg (Subtype.val) (hn a)
      rw [key a] at this
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv, FT.coe_subgroup_smul] using this
    have hΦa : a • g = g * ((Φ a : ↥N) : G) := by
      rw [key a]
      group
    rw [smul_mul', hΦa, hn']
    group
  · rw [map_mul]
    have hn1 : (QuotientGroup.mk' N) (n : G) = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact n.2
    rw [hn1, mul_one]

end Work.Hering.AppVII
