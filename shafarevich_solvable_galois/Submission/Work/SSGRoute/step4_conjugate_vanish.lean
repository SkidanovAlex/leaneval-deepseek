import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.twistLayer
import Submission.Work.SSGRoute.place_basics
import Submission.Work.SSGRoute.step4_transport_of_sha13
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open _root_.SSGRoute
open scoped Pointwise

/-!
# Step 4: transport of the local vanishing conditions to conjugate places

An additive `1`-cocycle `x` on the full Galois group `G_ℚ` with values in `E(n,τ)` and acting
through the restriction `res K : G_ℚ →* Gal(K/ℚ)` satisfies, whenever `res K σ = 1`,

  `x σ = (res K g) • x (g⁻¹ σ g)`,

because `x (σ * g) = x σ + x g` (as `res K σ = 1`) while `x (g * (g⁻¹ σ g)) = x g + (res K g) • x
(g⁻¹ σ g)` and the two left-hand sides coincide.

Consequently a vanishing condition imposed at a place `A` (`x` kills the inertia of `A`, or `x`
kills the intersection `D_A ∩ G_K` under a splitting/valuation hypothesis) transfers verbatim to
every `G_ℚ`-conjugate place `B = g • A`: conjugation by `g` moves inertia groups and decomposition
groups, the field `K` is normal so `G_K` is conjugation-stable, and the cocycle identity above
upgrades `x (g⁻¹ σ g) = 0` to `x σ = 0`.
-/

section Core

variable {Γ G M : Type} [Group Γ] [Group G] [AddCommGroup M] [DistribMulAction G M]

/-- **Conjugation identity for the values of an additive `1`-cocycle.**  If `act σ = 1`, then
`x σ = act g • x (g⁻¹ * σ * g)`. -/
theorem step4_cocycle_conj_eq {act : Γ →* G} {x : Γ → M} (hx : IsCocycleOn act ⊤ x)
    {σ : Γ} (hσ : act σ = 1) (g : Γ) :
    x σ = act g • x (g⁻¹ * σ * g) := by
  have h1 := hx σ (Subgroup.mem_top σ) g (Subgroup.mem_top g)
  have h2 := hx g (Subgroup.mem_top g) (g⁻¹ * σ * g) (Subgroup.mem_top _)
  have hL : g * (g⁻¹ * σ * g) = σ * g := by group
  rw [hL] at h2
  rw [hσ, one_smul] at h1
  rw [h1] at h2
  exact add_right_cancel (by rw [h2, add_comm (x g)])

end Core

theorem step4_conjugate_vanish (p : ℕ)
    (K : IntermediateField ℚ SSGRoute.QBar) [Normal ℚ K] (n i j : ℕ)
    (S : Finset (ValuationSubring SSGRoute.QBar))
    (y : SSGRoute.GalQ → Work.CohomologicalShrinking.E p (K ≃ₐ[ℚ] K) n i j)
    (hy : SSGRoute.IsCocycleOn (Work.SSGRoute.restrict K) ⊤ y)
    (hyT_S : ∀ A ∈ S, ∀ τ : SSGRoute.GalQ, SSGRoute.IsInertia ℚ A τ → y τ = 0)
    (hy0_S : ∀ A ∈ S, (¬ SSGRoute.IsSplitIn ℚ K A ∨ A.valuation (p : SSGRoute.QBar) < 1) →
      ∀ τ ∈ SSGRoute.decomp ℚ A, τ ∈ K.fixingSubgroup → y τ = 0) :
    (∀ B : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ B →
      (∃ A ∈ S, SSGRoute.IsConjPlace ℚ A B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia ℚ B σ → y σ = 0) ∧
    (∀ B : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ B →
      (∃ A ∈ S, SSGRoute.IsConjPlace ℚ A B) →
      (¬ SSGRoute.IsSplitIn ℚ K B ∨ B.valuation (p : SSGRoute.QBar) < 1) →
      ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp ℚ B → y σ = 0) := by
  constructor
  · -- ## Part 1: transfer of the inertia vanishing condition
    intro B _hBfin hconj σ hσK hσI
    obtain ⟨A, hAS, g, hg⟩ := hconj
    -- `g⁻¹ σ g` lies in the inertia of `A`
    have hIτ : SSGRoute.IsInertia ℚ A (g⁻¹ * σ * g) := by
      apply (isInertia_conj A g (g⁻¹ * σ * g)).mp
      have hgt : g * (g⁻¹ * σ * g) * g⁻¹ = σ := by group
      rw [hgt, hg]
      exact hσI
    have hyτ : y (g⁻¹ * σ * g) = 0 := hyT_S A hAS _ hIτ
    have hactσ : (Work.SSGRoute.restrict K) σ = 1 :=
      (step4_restrict_eq_one_iff K σ).mpr hσK
    rw [step4_cocycle_conj_eq hy hactσ g, hyτ, smul_zero]
  · -- ## Part 2: transfer of the decomposition-group vanishing condition
    intro B _hBfin hconj hcond σ hσK hσD
    obtain ⟨A, hAS, g, hg⟩ := hconj
    -- `g⁻¹ σ g` lies in the decomposition group of `A`
    have hτD : g⁻¹ * σ * g ∈ SSGRoute.decomp ℚ A := by
      rw [MulAction.mem_stabilizer_iff] at hσD ⊢
      rw [← hg] at hσD
      rw [mul_smul, mul_smul, hσD, inv_smul_smul]
    -- it still fixes `K`, since `K/ℚ` is normal
    have hτK : g⁻¹ * σ * g ∈ K.fixingSubgroup := by
      simpa using (step4_conj_mem_fixingSubgroup K (g := g⁻¹) hσK)
    -- the splitting / valuation hypothesis is conjugation invariant
    have hcondA : ¬ SSGRoute.IsSplitIn ℚ K A ∨ A.valuation (p : SSGRoute.QBar) < 1 := by
      rcases hcond with h | h
      · left
        intro hs
        exact h (hg ▸ (step4_isSplitIn_smul K A g).mpr hs)
      · right
        exact (step4_smul_valuation_p_lt_one p A g).mp (hg.symm ▸ h)
    have hyτ : y (g⁻¹ * σ * g) = 0 := hy0_S A hAS hcondA _ hτD hτK
    have hactσ : (Work.SSGRoute.restrict K) σ = 1 :=
      (step4_restrict_eq_one_iff K σ).mpr hσK
    rw [step4_cocycle_conj_eq hy hactσ g, hyτ, smul_zero]

end Work.SSGRoute
