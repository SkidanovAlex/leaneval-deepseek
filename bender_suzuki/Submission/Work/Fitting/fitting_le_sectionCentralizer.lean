import Mathlib
import Submission.Work.Fitting.Defs
import Submission.Work.Fitting.fitting_isNilpotent
import Submission.Work.Fitting.mem_sectionCentralizer_iff_commutator

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The Fitting subgroup centralizes every chief factor

This file proves `Work.Fitting.fitting_le_sectionCentralizer`: for a finite group `G`,
the Fitting subgroup `F(G)` is contained in the centralizer `C_G(K/H)` of every chief
factor `K/H` of `G`.

The mathematical content is the standard fact that a **normal nilpotent** subgroup
centralizes every chief factor; since `F(G)` is normal and nilpotent
(`Work.Fitting.fitting_isNilpotent`), the claim about `F(G)` follows.

## The argument

Let `N ≤ G` be normal and nilpotent, and let `K/H` be a chief factor of `G`. We show
`⁅K, N⁆ ≤ H`. Put `M = ⁅K, N⁆ ⊔ H`, which is normal with `H ≤ M ≤ K`; by the chief-factor
property `M = H` or `M = K`. In the first case `⁅K, N⁆ ≤ H` is immediate. In the second
case `K = ⁅K, N⁆ ⊔ H`, and we prove `K ≤ N.lowerCentralSeries i ⊔ H` for every `i` by
induction: the case `i = 0` uses `⁅K, N⁆ ≤ N`, and the inductive step uses

  `⁅K, N⁆ ≤ ⁅N.lowerCentralSeries i ⊔ H, N⁆
           = ⁅N.lowerCentralSeries i, N⁆ ⊔ ⁅H, N⁆ ≤ N.lowerCentralSeries (i+1) ⊔ H`.

Since `N` is nilpotent, some `N.lowerCentralSeries c = ⊥`, whence `K ≤ H`, contradicting
`H < K`.

The key point is the very last line: `K ≤ γᵢ(N)` propagates because `K = ⁅K, N⁆` and
`⁅γᵢ(N), N⁆ = γᵢ₊₁(N)` — nilpotency drives the chief factor down to `1`.
-/

noncomputable section

set_option linter.style.haveILetI false

open Classical

open scoped commutatorElement

namespace Work.Fitting

/-- A normal nilpotent subgroup `N` of a group `G` centralizes every chief factor `K/H`,
i.e. `⁅K, N⁆ ≤ H`. -/
theorem commutator_le_of_isChiefFactor_of_nilpotent {G : Type*} [Group G]
    {H K N : Subgroup G} [H.Normal] [N.Normal] (hN : Group.IsNilpotent ↥N)
    (h : IsChiefFactor H K) : ⁅K, N⁆ ≤ H := by
  haveI : K.Normal := h.2.1
  have hHK : H < K := h.2.2.1
  have hMnorm : (⁅K, N⁆ ⊔ H).Normal := inferInstance
  rcases h.2.2.2 (⁅K, N⁆ ⊔ H) hMnorm le_sup_right
      (sup_le (Subgroup.commutator_le_left K N) hHK.le) with heq | heq
  · exact le_sup_left.trans_eq heq
  · exfalso
    have hKle : ∀ i, K ≤ N.lowerCentralSeries i ⊔ H := by
      intro i
      induction i with
      | zero =>
        rw [Subgroup.lowerCentralSeries_zero, ← heq]
        exact sup_le ((Subgroup.commutator_le_right K N).trans le_sup_left) le_sup_right
      | succ i ih =>
        rw [Subgroup.lowerCentralSeries_succ, ← heq]
        refine sup_le ?_ le_sup_right
        calc ⁅K, N⁆ ≤ ⁅N.lowerCentralSeries i ⊔ H, N⁆ := Subgroup.commutator_mono_left ih
          _ = ⁅N.lowerCentralSeries i, N⁆ ⊔ ⁅H, N⁆ := Subgroup.commutator_sup_right _ _ _
          _ ≤ ⁅N.lowerCentralSeries i, N⁆ ⊔ H :=
              sup_le_sup le_rfl (Subgroup.commutator_le_left H N)
    obtain ⟨c, hc⟩ := (Subgroup.isNilpotent_iff_lowerCentralSeries N).mp hN
    have hKH : K ≤ H := by
      have hcl := hKle c
      rw [hc, bot_sup_eq] at hcl
      exact hcl
    exact (not_lt_of_ge hKH) hHK

/-- The Fitting subgroup `F(G)` is contained in the centralizer `C_G(K/H)` of every
chief factor `K/H` of `G`. -/
theorem fitting_le_sectionCentralizer (G : Type*) [Group G] [Finite G] {H K : Subgroup G}
    [H.Normal] (h : Work.Fitting.IsChiefFactor H K) :
    Work.Fitting.fitting G ≤ Work.Fitting.sectionCentralizer H K := by
  have hFnil : Group.IsNilpotent ↥(Work.Fitting.fitting G) := fitting_isNilpotent G
  have hcomm : ⁅K, Work.Fitting.fitting G⁆ ≤ H :=
    commutator_le_of_isChiefFactor_of_nilpotent hFnil h
  intro x hx
  rw [mem_sectionCentralizer_iff_commutator]
  intro k hk
  have h1 : ⁅k, x⁆ ∈ H := (Subgroup.commutator_le.mp hcomm) k hk x hx
  rw [commutatorElement_def] at h1
  have h2 : x * k * x⁻¹ * k⁻¹ = ⁅k, x⁆⁻¹ := by
    rw [commutatorElement_def]; group
  rw [h2]
  exact H.inv_mem h1

end Work.Fitting
