import ChallengeDeps
import Submission.Work.BoseFixB2.Sector.integral_sq_finset_sum_of_orthogonal
import Submission.Work.BoseFixB2.Sector.jointProj_orthogonal
import Submission.Work.BoseFixB2.Sector.jointProj_resolution
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB2.Sector.normB_secProj_sum` — Pythagoras for the `n₊ = k` sectors

FS §6 (`lem:LocMatrices`, `final_v2.tex` ll. 1365–1445) grades a box state `Ψ` by the
spectrum of the excitation-number operator `n₊ = ΣᵢQᵢ`, `Qᵢ = 1 − Pᵢ`, and uses
throughout that the sectors `1_{n₊ = k}Ψ` give an **orthogonal decomposition of the
`L²` norm**:

    Σ_{k=0}^{n} ‖1_{n₊ = k}Ψ‖² = ‖Ψ‖².

In the corpus's box vocabulary (`Submission.Work.BoseFixB2.Defs`,
`Submission.Work.BoseBoxFix.Defs`) the sector is

    `secProj ℓ k Φ = Σ_{S ⊆ {0,…,n−1}, |S| = k} E_S Φ`,   `E_S = ∏_{i∈S}Q_i ∏_{j∉S}P_j`

(`jointProj ℓ S`), the box norm is `normB v μ n Φ = ∫_{abox n ℓ} Φ²`, and the statement
proved here is

    Σ_{k ≤ n} normB v μ n (secProj ℓ k Φ) = normB v μ n Φ,   ℓ = fsSide v μ, 0 < ℓ.

## The proof

Nothing spectral is needed: the whole content is the **orthogonality of the joint
sectors** together with the resolution of the identity.  Concretely, with
`f S := jointProj ℓ S Φ`:

* `jointProj_resolution` gives `Σ_{S ∈ (range n).powerset} f S = Φ`, so
  `normB Φ = ∫ (Σ_S f S)²`;
* `jointProj_orthogonal` says the `f S` are pairwise orthogonal for the box pairing
  (two distinct sets of slots differ in at least one slot `< n`, and the slot operators
  `Pᵢ, Qᵢ = 1 − Pᵢ` are orthogonal projections), so the double sum
  `Σ_S Σ_T ∫ f S · f T` collapses to its diagonal `Σ_S ∫ (f S)²`
  (`Work.BoseFixB2.Sector.integral_sq_finset_sum_of_orthogonal`, Pythagoras for the box pairing);
* each layer `secProj ℓ k Φ = Σ_{|S| = k} f S` is again a sum of pairwise orthogonal
  terms of the same kind, and the layers are the fibres of the cardinality map, so
  `Σ_k Σ_{|S| = k} ∫ (f S)² = Σ_S ∫ (f S)²` (`Finset.sum_powerset`).

The last two displays are the same number, which is the identity.

No positivity of `Φ`, no smoothness beyond continuity (`ContinuousOn.integrableOn_compact`
on the compact box `abox n ℓ`, `0 < ℓ`) and no hypothesis on `v, h, μ` beyond
`0 < fsSide v μ` is used.

## Imports

This module imports `Sector.jointProj_resolution`, `Sector.jointProj_orthogonal` and the
general Pythagoras lemma `Sector.integral_sq_finset_sum_of_orthogonal`, and deliberately
**not** `Sector.jointProj_selfadjoint` / `Sector.secProj_orthogonal`: the latter pulls in
the module `Submission.Work.BoseFixB2.Sector.blockOp_continuous`, which declares the same
name `Work.BoseFixB2.Sector.blockOp_continuous` as the copy inlined in
`Sector/jointProj_orthogonal.lean`, so Lean refuses to load both in one environment
("environment already contains ...").  Neither of them is used below: the orthogonality
input is `jointProj_orthogonal`, which carries its own continuity lemma
(`jointProj_continuous`).
-/

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Filter Metric

namespace Work.BoseFixB2.Sector

open Submission.BoseGases Work.BoseFixB2

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. Pythagoras for the box pairing

The analytic core of the argument — for a finite family of continuous functions that is
pairwise orthogonal for the box pairing, the box integral of the square of the sum is the
sum of the box integrals of the squares — is the general lemma
`Work.BoseFixB2.Sector.integral_sq_finset_sum_of_orthogonal`
(`Submission/Work/BoseFixB2/Sector/integral_sq_finset_sum_of_orthogonal.lean`), imported
above and used below; nothing in this file proves it again. -/

/-! ## 2. The norm decomposition -/

/-- **Pythagoras for the sectors** (`ℓ`-general form, `ℓ > 0`): the squared box norms of
the sectors `secProj ℓ k Φ`, `k = 0, …, n`, add up to the squared box norm of `Φ`. -/
lemma sqNormB_secProj_sum {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ}
    (hΦ : Continuous Φ) :
    (∑ k ∈ Finset.range (n + 1), Work.BoseKinLoc.sqNormB n ℓ (secProj ℓ k Φ))
      = Work.BoseKinLoc.sqNormB n ℓ Φ := by
  -- pairwise orthogonality of the joint sectors
  have horth : ∀ S ∈ (Finset.range n).powerset, ∀ T ∈ (Finset.range n).powerset, S ≠ T →
      ∫ x in Submission.BoseGases.abox n ℓ,
        jointProj ℓ S Φ x * jointProj ℓ T Φ x = 0 := by
    intro S hS T hT hne
    refine jointProj_orthogonal hℓ ?_ Φ Φ hΦ hΦ
    rw [Finset.inter_eq_left.mpr (Finset.mem_powerset.mp hS),
      Finset.inter_eq_left.mpr (Finset.mem_powerset.mp hT)]
    exact hne
  -- the resolution of the identity, as an identity of functions
  have hfun : (fun x : Submission.BoseGases.X n => ∑ S ∈ (Finset.range n).powerset,
      jointProj ℓ S Φ x) = Φ := by
    funext x
    rw [← congrFun (jointProj_resolution hℓ Φ hΦ) x]
    exact (Finset.sum_apply x _ _).symm
  -- step A: `‖Φ‖²` is the sum of the diagonal contributions of all joint sectors
  have hA : (∑ S ∈ (Finset.range n).powerset,
      ∫ x in Submission.BoseGases.abox n ℓ, (jointProj ℓ S Φ x) ^ 2)
      = ∫ x in Submission.BoseGases.abox n ℓ, Φ x ^ 2 := by
    conv_rhs => rw [← hfun]
    exact (integral_sq_finset_sum_of_orthogonal hℓ ((Finset.range n).powerset)
      (fun S => jointProj ℓ S Φ)
      (fun S _ => jointProj_continuous hℓ S hΦ) horth).symm
  -- step B: the `k`-th sector is a sum of pairwise orthogonal joint sectors
  have hB : ∀ k ∈ Finset.range (n + 1),
      (∫ x in Submission.BoseGases.abox n ℓ, (secProj ℓ k Φ x) ^ 2)
      = ∑ S ∈ (Finset.range n).powersetCard k,
          ∫ x in Submission.BoseGases.abox n ℓ, (jointProj ℓ S Φ x) ^ 2 := by
    intro k _
    have ho : ∀ S ∈ (Finset.range n).powersetCard k, ∀ T ∈ (Finset.range n).powersetCard k,
        S ≠ T →
        ∫ x in Submission.BoseGases.abox n ℓ,
          jointProj ℓ S Φ x * jointProj ℓ T Φ x = 0 := by
      intro S hS T hT hne
      refine jointProj_orthogonal hℓ ?_ Φ Φ hΦ hΦ
      rw [Finset.inter_eq_left.mpr (Finset.mem_powersetCard.mp hS).1,
        Finset.inter_eq_left.mpr (Finset.mem_powersetCard.mp hT).1]
      exact hne
    have h := integral_sq_finset_sum_of_orthogonal hℓ ((Finset.range n).powersetCard k)
      (fun S => jointProj ℓ S Φ)
      (fun S _ => jointProj_continuous hℓ S hΦ) ho
    simpa only [secProj, Finset.sum_apply] using h
  have hmain : (∑ k ∈ Finset.range (n + 1),
      ∫ x in Submission.BoseGases.abox n ℓ, (secProj ℓ k Φ x) ^ 2)
      = ∫ x in Submission.BoseGases.abox n ℓ, Φ x ^ 2 := by
    have h₁ : (∑ k ∈ Finset.range (n + 1),
        ∫ x in Submission.BoseGases.abox n ℓ, (secProj ℓ k Φ x) ^ 2)
        = ∑ k ∈ Finset.range (n + 1),
            ∑ S ∈ (Finset.range n).powersetCard k,
              ∫ x in Submission.BoseGases.abox n ℓ, (jointProj ℓ S Φ x) ^ 2 :=
      Finset.sum_congr rfl hB
    have hfib := Finset.sum_powerset (s := Finset.range n)
      (f := fun S => ∫ x in Submission.BoseGases.abox n ℓ, (jointProj ℓ S Φ x) ^ 2)
    rw [Finset.card_range] at hfib
    rw [h₁]
    exact hfib.symm.trans hA
  rw [show (∑ k ∈ Finset.range (n + 1),
        Work.BoseKinLoc.sqNormB n ℓ (secProj ℓ k Φ))
      = (∑ k ∈ Finset.range (n + 1),
        ∫ x in Submission.BoseGases.abox n ℓ, (secProj ℓ k Φ x) ^ 2) from
      Finset.sum_congr rfl (fun _ _ => rfl)]
  rw [show Work.BoseKinLoc.sqNormB n ℓ Φ
      = (∫ x in Submission.BoseGases.abox n ℓ, Φ x ^ 2) from rfl]
  exact hmain

/-- **The norm decomposition of FS §6 along the sectors of `n₊`** (FS's
`Σ_k ‖1_{n₊=k}Ψ‖² = ‖Ψ‖²`): the squared box norms of the sectors
`1_{n₊=k}Ψ = secProj ℓ k Φ` at FS's parameters `ℓ = fsSide v μ` add up to the squared box
norm of `Φ`.  The only hypotheses are `0 < fsSide v μ` and continuity of `Φ`. -/
theorem normB_secProj_sum {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {μ : ℝ} {n : ℕ} (hℓ : 0 < Work.BoseFixB2.fsSide v μ) {Φ : Submission.BoseGases.X n → ℝ} (hΦ : Continuous Φ) : (∑ k ∈ Finset.range (n + 1), Work.BoseBoxFix.normB v μ n (Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) k Φ)) = Work.BoseBoxFix.normB v μ n Φ := by
  simpa only [Work.BoseBoxFix.normB, fsSide] using
    sqNormB_secProj_sum (ℓ := fsSide v μ) hℓ hΦ

end Work.BoseFixB2.Sector
