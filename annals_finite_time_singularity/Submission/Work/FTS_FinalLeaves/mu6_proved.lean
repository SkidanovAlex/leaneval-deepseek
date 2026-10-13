import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS.StrongEps.EpsLimit
import Submission.Work.FTS.StrongGlobal.Defs
import Submission.Work.FTS.Galerkin.Defs
import Submission.Work.FTS.StrongGlobal.dynRHS_congr

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.Galerkin Work.FTS.FinalV2

namespace Work.FTS_FinalLeaves

theorem mu6_proved {α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hα1 : α ≤ 1) (hML : Work.FTS.StrongEps.MuLamOK α C₀ Φs E)
    (hLip : Work.FTS.FinalV2.MuLipC α C₀ Φs E) {g : Work.FTS.Galerkin.Fam}
    (hOK : Work.FTS.FinalV2.DynOK' α C₀ Φs E g) :
    (∀ τ : ℝ, 0 ≤ τ →
        |Work.FTS.Galerkin.muDyn α (Work.FTS.Nonlin.PsiCan Φs E g) g τ| ≤ 1 / 2) ∧
    ContinuousOn (Work.FTS.Galerkin.muDyn α (Work.FTS.Nonlin.PsiCan Φs E g) g) (Set.Ici 0) ∧
    ∀ β : ℝ, 0 < β → β ≤ 1 → ∀ S : ℝ, 0 < S → ∃ L : ℝ, 0 ≤ L ∧
      ∀ τ ∈ Set.Icc (0 : ℝ) S, ∀ τ' ∈ Set.Icc (0 : ℝ) S,
        |Work.FTS.Galerkin.muDyn α (Work.FTS.Nonlin.PsiCan Φs E g) g τ
          - Work.FTS.Galerkin.muDyn α (Work.FTS.Nonlin.PsiCan Φs E g) g τ'|
          ≤ L * |τ - τ'| ^ β := by
  have hLA : Work.FTS.FinalV2.LimApprox α C₀ Φs E g := hOK.2
  obtain ⟨Lμ, hLμ0, hLμ⟩ := hLip
  set F : ℝ → ℝ := fun τ => muDyn α (Work.FTS.Nonlin.PsiCan Φs E g) g τ with hF
  -- `muDyn` only depends on the fake-time slice of the family
  have hslice : ∀ (gg : Fam) (τ : ℝ), muDyn α (Work.FTS.Nonlin.PsiCan Φs E gg) gg τ
      = muDyn α (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.FinalV2.cst (slice gg τ)))
          (Work.FTS.FinalV2.cst (slice gg τ)) 0 := fun gg τ => rfl
  -- Conjunct 1: the uniform bound `|μ| ≤ 1/2`, obtained by approximation from class-`C` slices.
  have hbdd : ∀ τ : ℝ, 0 ≤ τ → |F τ| ≤ 1 / 2 := by
    intro τ hτ
    obtain ⟨gn, B, L, hgn, hglip, hgj, hgm⟩ := hLA (τ + 1) (by linarith)
    have hb : ∀ n, |muDyn α (Work.FTS.Nonlin.PsiCan Φs E (gn n)) (gn n) τ| ≤ 1 / 2 := by
      intro n
      obtain ⟨hc, hx, -⟩ := hgn n τ ⟨hτ, by linarith⟩
      have hh := (hML (slice (gn n) τ) hc hx).1
      rwa [hslice (gn n) τ]
    have hlim : Tendsto (fun n => |muDyn α (Work.FTS.Nonlin.PsiCan Φs E (gn n)) (gn n) τ|)
        atTop (𝓝 |F τ|) := by
      have hh := (hgm τ ⟨hτ, by linarith⟩).abs
      simpa [hF] using hh
    exact le_of_tendsto_of_tendsto hlim tendsto_const_nhds (Eventually.of_forall hb)
  -- Lipschitz on every `[0,S]`: the `τ`-Lipschitz modulus of the approximating class-`C`
  -- families in the `ℋ⁴`-norm, composed with the class-`C` Lipschitz bound `hLip` on `muDyn`.
  have hLipF : ∀ S : ℝ, 0 < S → ∃ K : ℝ, 0 ≤ K ∧
      ∀ τ ∈ Icc (0 : ℝ) S, ∀ τ' ∈ Icc (0 : ℝ) S, |F τ - F τ'| ≤ K * |τ - τ'| := by
    intro S hS
    obtain ⟨gn, B, L, hgn, hglip, hgj, hgm⟩ := hLA (max S 1) (lt_max_of_lt_right one_pos)
    refine ⟨max (Lμ * L) 0, le_max_right _ _, ?_⟩
    intro τ hτ τ' hτ'
    have hτT : τ ∈ Icc (0 : ℝ) (max S 1) := ⟨hτ.1, le_trans hτ.2 (le_max_left _ _)⟩
    have hτ'T : τ' ∈ Icc (0 : ℝ) (max S 1) := ⟨hτ'.1, le_trans hτ'.2 (le_max_left _ _)⟩
    have hb : ∀ n, |muDyn α (Work.FTS.Nonlin.PsiCan Φs E (gn n)) (gn n) τ
        - muDyn α (Work.FTS.Nonlin.PsiCan Φs E (gn n)) (gn n) τ'| ≤ Lμ * (L * |τ - τ'|) := by
      intro n
      obtain ⟨hc, hx, -⟩ := hgn n τ hτT
      obtain ⟨hc', hx', -⟩ := hgn n τ' hτ'T
      have h1 := hLμ (slice (gn n) τ) (slice (gn n) τ') hc hc' hx hx'
      rw [← hslice (gn n) τ, ← hslice (gn n) τ'] at h1
      calc |muDyn α (Work.FTS.Nonlin.PsiCan Φs E (gn n)) (gn n) τ
              - muDyn α (Work.FTS.Nonlin.PsiCan Φs E (gn n)) (gn n) τ'|
          ≤ Lμ * Work.FTS.Nonlin.Xn α (slice (gn n) τ - slice (gn n) τ') := h1
        _ ≤ Lμ * (L * |τ - τ'|) := mul_le_mul_of_nonneg_left (hglip n τ hτT τ' hτ'T) hLμ0
    have hlim : Tendsto (fun n => |muDyn α (Work.FTS.Nonlin.PsiCan Φs E (gn n)) (gn n) τ
        - muDyn α (Work.FTS.Nonlin.PsiCan Φs E (gn n)) (gn n) τ'|) atTop (𝓝 |F τ - F τ'|) := by
      have hh := ((hgm τ hτT).sub (hgm τ' hτ'T)).abs
      simpa [hF] using hh
    have h2 := le_of_tendsto_of_tendsto hlim tendsto_const_nhds (Eventually.of_forall hb)
    calc |F τ - F τ'| ≤ Lμ * (L * |τ - τ'|) := h2
      _ = (Lμ * L) * |τ - τ'| := by ring
      _ ≤ max (Lμ * L) 0 * |τ - τ'| :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _)
  -- Conjunct 2: continuity on `[0,∞)` from the local Lipschitz bound.
  have hcont : ContinuousOn F (Ici 0) := by
    have hloc : LocallyLipschitzOn (Ici 0) F := by
      intro x hx
      have hx0 : 0 ≤ x := hx
      obtain ⟨K, hK0, hK⟩ := hLipF (x + 1) (by linarith)
      refine ⟨⟨K, hK0⟩, Icc 0 (x + 1), ?_, ?_⟩
      · rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
        exact ⟨Iio (x + 1), Iio_mem_nhds (by linarith), fun y hy => ⟨hy.2, hy.1.le⟩⟩
      · exact LipschitzOnWith.of_dist_le_mul (fun τ hτ τ' hτ' => by
          rw [Real.dist_eq, Real.dist_eq]; exact hK τ hτ τ' hτ')
    exact hloc.continuousOn
  refine ⟨?_, ?_, ?_⟩
  · simpa only [hF] using hbdd
  · simpa only [hF] using hcont
  -- Conjunct 3: `β`-Hölder on `[0,S]` from the Lipschitz bound, `|τ-τ'| ≤ max 1 S^{1-β}|τ-τ'|^β`.
  · intro β hβ0 hβ1 S hS
    obtain ⟨K, hK0, hK⟩ := hLipF S hS
    refine ⟨K * max 1 (S ^ (1 - β)), mul_nonneg hK0 (le_trans zero_le_one (le_max_left _ _)), ?_⟩
    intro τ hτ τ' hτ'
    have hmain : |F τ - F τ'| ≤ K * max 1 (S ^ (1 - β)) * |τ - τ'| ^ β := by
      have h1 : |F τ - F τ'| ≤ K * |τ - τ'| := hK τ hτ τ' hτ'
      have hx0 : 0 ≤ |τ - τ'| := abs_nonneg _
      have hxS : |τ - τ'| ≤ S := by
        rw [abs_sub_le_iff]
        exact ⟨by linarith [hτ.2, hτ'.1], by linarith [hτ'.2, hτ.1]⟩
      have h2 : |τ - τ'| ≤ max 1 (S ^ (1 - β)) * |τ - τ'| ^ β := by
        rcases hx0.eq_or_lt with h | h
        · rw [← h, Real.zero_rpow (ne_of_gt hβ0), mul_zero]
        · have hxb : 0 ≤ |τ - τ'| ^ β := Real.rpow_nonneg hx0 β
          have hone : |τ - τ'| ^ (1 - β) ≤ max 1 (S ^ (1 - β)) :=
            le_trans (Real.rpow_le_rpow hx0 hxS (by linarith)) (le_max_right _ _)
          calc |τ - τ'| = |τ - τ'| ^ (β + (1 - β)) := by
                rw [show β + (1 - β) = 1 by ring, Real.rpow_one]
            _ = |τ - τ'| ^ β * |τ - τ'| ^ (1 - β) := Real.rpow_add h β (1 - β)
            _ ≤ |τ - τ'| ^ β * max 1 (S ^ (1 - β)) := mul_le_mul_of_nonneg_left hone hxb
            _ = max 1 (S ^ (1 - β)) * |τ - τ'| ^ β := by ring
      calc |F τ - F τ'| ≤ K * |τ - τ'| := h1
        _ ≤ K * (max 1 (S ^ (1 - β)) * |τ - τ'| ^ β) := mul_le_mul_of_nonneg_left h2 hK0
        _ = K * max 1 (S ^ (1 - β)) * |τ - τ'| ^ β := by ring
    simpa only [hF] using hmain

end Work.FTS_FinalLeaves
