import Mathlib
import Submission.Grassmann.ExpansionBound

/-!
# The KMS second-moment step: a lower bound on the level-`1` weight

This file continues `ExpansionBound.lean`.  For a set `S` of vertices of `Gr k ℓ` with
density `ρ = #S/N` and expansion `Φ(S)`, put `f = 1_S - ρ`.  The spectral expansion

  `⟨A f, f⟩ = ∑_i θ_i ‖f^{=i}‖²`

(a theorem of `Levels.lean`), together with `⟨A f, f⟩ = d · #S · (1 - ρ - Φ(S))` and the
monotonicity of the Eberlein eigenvalues `θ_0 > θ_1 > θ_2 > ⋯`, gives the fundamental
KMS lower bound on the weight of the level-`1` part of `f`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

open PseudorandomGrassmann
open Module Finset Filter
open Classical

local notation "𝔽₂" => ZMod 2

namespace Submission.Grassmann
namespace F2

noncomputable section

variable {k ℓ : ℕ}

attribute [-instance] Subtype.instDecidableEq

/-! ## Positivity of the standard inner product -/

lemma stdInner_nonneg (f : GrVertex k ℓ → ℚ) : 0 ≤ stdInner k ℓ f f := by
  rw [stdInner_apply]
  exact Finset.sum_nonneg (fun L _ => mul_self_nonneg _)

/-! ## Splitting a sum over `range (ℓ+1)` into the `0`, `1` and `≥ 2` parts -/

lemma split_sum_range (f : ℕ → ℚ) (hℓ : 1 ≤ ℓ) :
    ∑ i ∈ Finset.range (ℓ + 1), f i
      = f 0 + f 1 + ∑ j ∈ Finset.range (ℓ - 1), f (j + 2) := by
  have h2 : ∑ i ∈ Finset.range ℓ, f (i + 1)
      = ∑ i ∈ Finset.range (ℓ - 1), f (i + 1 + 1) + f 1 := by
    conv_lhs => rw [show ℓ = (ℓ - 1) + 1 from by omega]
    exact Finset.sum_range_succ' (fun i => f (i + 1)) (ℓ - 1)
  rw [Finset.sum_range_succ' f ℓ, h2]
  rw [Finset.sum_congr rfl (fun j _ => by rw [show j + 1 + 1 = j + 2 from by omega])]
  ring

/-! ## The centred indicator is orthogonal to the level-`0` (constant) space -/

lemma center_mem_ortho_LvlAll_zero (S : Finset (GrVertex k ℓ)) (hS : S.Nonempty) :
    (fun L => ind S L - dens S) ∈ (stdInner k ℓ).orthogonal (LvlAll k ℓ 0) := by
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  intro y hy
  rw [LvlAll_zero] at hy
  obtain ⟨c, rfl⟩ := Vup_zero_const hy
  rw [stdInner_apply]
  have hsum : ∑ L, c * (ind S L - dens S) = 0 := by
    rw [← Finset.mul_sum]
    have h1 : ∑ L, (ind S L - dens S)
        = (S.card : ℚ) - dens S * (Fintype.card (GrVertex k ℓ) : ℚ) := by
      rw [Finset.sum_sub_distrib, sum_ind_eq', Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul]
      ring
    rw [h1, dens_mul_card S hS, sub_self, mul_zero]
  exact hsum

/-! ## The level-`1` weight lower bound -/

/-- **KMS level-`1` weight bound.**  For `f` orthogonal to the constants, some level-`1`
function `g₁` satisfies `⟨Af,f⟩ - θ₂‖f‖² ≤ (θ₁ - θ₂)‖g₁‖²`. -/
theorem level_weight_bound (hℓ : 1 ≤ ℓ) (hk : 2 * ℓ ≤ k) (f : GrVertex k ℓ → ℚ)
    (hf0 : f ∈ (stdInner k ℓ).orthogonal (LvlAll k ℓ 0)) :
    ∃ g1 : GrVertex k ℓ → ℚ, g1 ∈ LvlAll k ℓ 1 ∧
      stdInner k ℓ (adjOpLM (k := k) (ℓ := ℓ) f) f - thetaQ k ℓ 2 * stdInner k ℓ f f
        ≤ (thetaQ k ℓ 1 - thetaQ k ℓ 2) * stdInner k ℓ g1 g1 := by
  have hcodim : ℓ ≤ k - ℓ := by omega
  obtain ⟨g, hgm, hgo, hsum, hnorm, hinner⟩ := inner_adjOp_eq_sum_Lvl (k := k) (ℓ := ℓ) hℓ hk f
  -- the level-`0` component has zero norm
  have hg0 : stdInner k ℓ (g 0) (g 0) = 0 := by
    have h1 : g 0 ∈ (stdInner k ℓ).orthogonal (LvlAll k ℓ 0) := by
      have h2 : f - (f - g 0) ∈ (stdInner k ℓ).orthogonal (LvlAll k ℓ 0) :=
        Submodule.sub_mem _ hf0 (hgo 0 (by omega))
      rwa [show f - (f - g 0) = g 0 from by abel] at h2
    exact (LinearMap.BilinForm.mem_orthogonal_iff.mp h1) (g 0) (hgm 0 (by omega))
  refine ⟨g 1, hgm 1 (by omega), ?_⟩
  set T : ℚ := ∑ j ∈ Finset.range (ℓ - 1), stdInner k ℓ (g (j + 2)) (g (j + 2)) with hT
  have hnorm' : stdInner k ℓ f f
      = stdInner k ℓ (g 0) (g 0) + stdInner k ℓ (g 1) (g 1) + T := by
    rw [hnorm, split_sum_range (fun i => stdInner k ℓ (g i) (g i)) hℓ, hT]
  have hinner' : stdInner k ℓ (adjOpLM (k := k) (ℓ := ℓ) f) f
      = thetaQ k ℓ 0 * stdInner k ℓ (g 0) (g 0) + thetaQ k ℓ 1 * stdInner k ℓ (g 1) (g 1)
        + ∑ j ∈ Finset.range (ℓ - 1),
            thetaQ k ℓ (j + 2) * stdInner k ℓ (g (j + 2)) (g (j + 2)) := by
    rw [hinner, split_sum_range (fun i => thetaQ k ℓ i * stdInner k ℓ (g i) (g i)) hℓ]
  have htail : ∑ j ∈ Finset.range (ℓ - 1),
        thetaQ k ℓ (j + 2) * stdInner k ℓ (g (j + 2)) (g (j + 2)) ≤ thetaQ k ℓ 2 * T := by
    rw [hT, Finset.mul_sum]
    refine Finset.sum_le_sum (fun j hj => ?_)
    rw [Finset.mem_range] at hj
    exact mul_le_mul_of_nonneg_right
      (thetaQ_le_of_le (show 2 ≤ j + 2 by omega) (show j + 2 ≤ ℓ by omega) hcodim)
      (stdInner_nonneg _)
  rw [hinner', hnorm']
  simp only [hg0, mul_zero, zero_add]
  nlinarith [htail]

/-- **The KMS bound, in terms of the expansion ratio.** -/
theorem level_one_weight_ge (hℓ : 1 ≤ ℓ) (hk : 2 * ℓ ≤ k) (S : Finset (GrVertex k ℓ))
    (hS : S.Nonempty) {α : ℚ} (hα : Φ (Gr k ℓ) S hS ≤ α) :
    ∃ g1 : GrVertex k ℓ → ℚ, g1 ∈ LvlAll k ℓ 1 ∧
      degQ k ℓ * (S.card : ℚ) * (1 - α - dens S)
          - thetaQ k ℓ 2 * ((S.card : ℚ) * (1 - dens S))
        ≤ (thetaQ k ℓ 1 - thetaQ k ℓ 2) * stdInner k ℓ g1 g1 := by
  obtain ⟨g1, hg1, hle⟩ :=
    level_weight_bound (k := k) (ℓ := ℓ) hℓ hk (fun L => ind S L - dens S)
      (center_mem_ortho_LvlAll_zero S hS)
  refine ⟨g1, hg1, ?_⟩
  have h2 := inner_adjOp_centered_ge (k := k) (ℓ := ℓ) hℓ S hS hα
  rw [stdInner_center_self S hS] at hle
  linarith

/-- **Spectral gap of the Grassmann graph** (in the regime `2ℓ ≤ k`): on the orthogonal
complement of the constants the adjacency operator is bounded by the second Eberlein
eigenvalue `θ_1`.  Together with `exists_eigenvector_theta_one` this identifies `θ_1` as the
second largest eigenvalue. -/
theorem inner_adjOp_le_theta_one (hℓ : 1 ≤ ℓ) (hk : 2 * ℓ ≤ k) {f : GrVertex k ℓ → ℚ}
    (hf0 : f ∈ (stdInner k ℓ).orthogonal (LvlAll k ℓ 0)) :
    stdInner k ℓ (adjOpLM (k := k) (ℓ := ℓ) f) f ≤ thetaQ k ℓ 1 * stdInner k ℓ f f := by
  have hcodim : ℓ ≤ k - ℓ := by omega
  obtain ⟨g, hgm, hgo, hsum, hnorm, hinner⟩ := inner_adjOp_eq_sum_Lvl (k := k) (ℓ := ℓ) hℓ hk f
  have hg0 : stdInner k ℓ (g 0) (g 0) = 0 := by
    have h1 : g 0 ∈ (stdInner k ℓ).orthogonal (LvlAll k ℓ 0) := by
      have h2 : f - (f - g 0) ∈ (stdInner k ℓ).orthogonal (LvlAll k ℓ 0) :=
        Submodule.sub_mem _ hf0 (hgo 0 (by omega))
      rwa [show f - (f - g 0) = g 0 from by abel] at h2
    exact (LinearMap.BilinForm.mem_orthogonal_iff.mp h1) (g 0) (hgm 0 (by omega))
  set T : ℚ := ∑ j ∈ Finset.range (ℓ - 1), stdInner k ℓ (g (j + 2)) (g (j + 2)) with hT
  have hnorm' : stdInner k ℓ f f
      = stdInner k ℓ (g 0) (g 0) + stdInner k ℓ (g 1) (g 1) + T := by
    rw [hnorm, split_sum_range (fun i => stdInner k ℓ (g i) (g i)) hℓ, hT]
  have hinner' : stdInner k ℓ (adjOpLM (k := k) (ℓ := ℓ) f) f
      = thetaQ k ℓ 0 * stdInner k ℓ (g 0) (g 0) + thetaQ k ℓ 1 * stdInner k ℓ (g 1) (g 1)
        + ∑ j ∈ Finset.range (ℓ - 1),
            thetaQ k ℓ (j + 2) * stdInner k ℓ (g (j + 2)) (g (j + 2)) := by
    rw [hinner, split_sum_range (fun i => thetaQ k ℓ i * stdInner k ℓ (g i) (g i)) hℓ]
  have htail : ∑ j ∈ Finset.range (ℓ - 1),
        thetaQ k ℓ (j + 2) * stdInner k ℓ (g (j + 2)) (g (j + 2)) ≤ thetaQ k ℓ 1 * T := by
    rw [hT, Finset.mul_sum]
    refine Finset.sum_le_sum (fun j hj => ?_)
    rw [Finset.mem_range] at hj
    exact mul_le_mul_of_nonneg_right
      (thetaQ_le_of_le (show 1 ≤ j + 2 by omega) (show j + 2 ≤ ℓ by omega) hcodim)
      (stdInner_nonneg _)
  rw [hinner', hnorm']
  simp only [hg0, mul_zero, zero_add]
  nlinarith [htail]

/-- **High-degree functions are strongly contracted.**  If `f` is orthogonal to the
degree-`≤ d` space `V_d` then the adjacency operator contracts it by at most the Eberlein
eigenvalue `θ_{d+1}`.  (The case `d = 0` is `inner_adjOp_le_theta_one`.) -/
theorem inner_adjOp_le_theta_of_mem_ortho (hℓ : 1 ≤ ℓ) (hk : 2 * ℓ ≤ k) {d : ℕ} (hd : d ≤ ℓ)
    {f : GrVertex k ℓ → ℚ}
    (hf : f ∈ (stdInner k ℓ).orthogonal (Vup (k := k) (ℓ := ℓ) d)) :
    stdInner k ℓ (adjOpLM (k := k) (ℓ := ℓ) f) f ≤ thetaQ k ℓ (d + 1) * stdInner k ℓ f f := by
  have hcodim : ℓ ≤ k - ℓ := by omega
  obtain ⟨g, hgm, hgo, hsum, hnorm, hinner⟩ := inner_adjOp_eq_sum_Lvl (k := k) (ℓ := ℓ) hℓ hk f
  have hzero : ∀ i, i ≤ d → stdInner k ℓ (g i) (g i) = 0 := by
    intro i hi
    have hmem_i : g i ∈ Vup (k := k) (ℓ := ℓ) i := by
      have h := hgm i (by omega)
      rcases Nat.eq_zero_or_pos i with h0 | hpos
      · subst h0; rwa [LvlAll_zero] at h
      · rw [LvlAll_succ (by omega), Lvl, Submodule.mem_inf] at h
        exact h.1
    have hmem : g i ∈ Vup (k := k) (ℓ := ℓ) d :=
      Vup_mono (k := k) (ℓ := ℓ) hℓ hi hd hmem_i
    have h1 : stdInner k ℓ f (g i) = 0 := by
      rw [stdInner_comm]
      exact (LinearMap.BilinForm.mem_orthogonal_iff.mp hf) (g i) hmem
    have h2 : stdInner k ℓ (f - g i) (g i) = 0 := by
      rw [stdInner_comm]
      exact (LinearMap.BilinForm.mem_orthogonal_iff.mp (hgo i (by omega))) (g i)
        (hgm i (by omega))
    have h3 : stdInner k ℓ (f - g i) (g i)
        = stdInner k ℓ f (g i) - stdInner k ℓ (g i) (g i) := by
      rw [stdInner_apply, stdInner_apply, stdInner_apply]
      rw [Finset.sum_congr rfl (fun L (_ : L ∈ Finset.univ) =>
        show (f - g i) L * g i L = f L * g i L - g i L * g i L from by
          simp only [Pi.sub_apply]; ring)]
      rw [Finset.sum_sub_distrib]
    linarith
  have hnorm_d : (∑ i ∈ Finset.range (ℓ + 1), stdInner k ℓ (g i) (g i))
      = ∑ i ∈ Finset.range (ℓ + 1),
          (if d < i then stdInner k ℓ (g i) (g i) else 0) := by
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [Finset.mem_range] at hi
    by_cases h : d < i
    · rw [if_pos h]
    · rw [if_neg h, hzero i (by omega)]
  have hbound : (∑ i ∈ Finset.range (ℓ + 1), thetaQ k ℓ i * stdInner k ℓ (g i) (g i))
      ≤ thetaQ k ℓ (d + 1) * ∑ i ∈ Finset.range (ℓ + 1),
          (if d < i then stdInner k ℓ (g i) (g i) else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun i hi => ?_)
    rw [Finset.mem_range] at hi
    by_cases h : d < i
    · rw [if_pos h]
      exact mul_le_mul_of_nonneg_right
        (thetaQ_le_of_le (show d + 1 ≤ i by omega) (show i ≤ ℓ by omega) hcodim)
        (stdInner_nonneg _)
    · rw [if_neg h, hzero i (by omega), mul_zero, mul_zero]
  rw [hinner]
  calc (∑ i ∈ Finset.range (ℓ + 1), thetaQ k ℓ i * stdInner k ℓ (g i) (g i))
      ≤ thetaQ k ℓ (d + 1) * ∑ i ∈ Finset.range (ℓ + 1),
          (if d < i then stdInner k ℓ (g i) (g i) else 0) := hbound
    _ = thetaQ k ℓ (d + 1) * (∑ i ∈ Finset.range (ℓ + 1), stdInner k ℓ (g i) (g i)) := by
        rw [hnorm_d]
    _ = thetaQ k ℓ (d + 1) * stdInner k ℓ f f := by rw [hnorm]

end

end F2
end Submission.Grassmann
