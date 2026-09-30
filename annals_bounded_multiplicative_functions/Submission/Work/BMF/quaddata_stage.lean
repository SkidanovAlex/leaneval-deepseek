import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.interfaces
import Submission.Work.BMF.polyrel_basic
import Submission.Work.BMF.quaddata_core
import Submission.Work.BMF.poly_growth
import Submission.Work.BMF.fam_card_le
import Submission.Work.BMF.prime_card_le
import Submission.Work.BMF.sigma_filter_sq
import Submission.Work.BMF.edge_count_core
import Submission.Work.BMF.quaddata_aux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

open Polynomial Finset Real Complex
open BoundedMultiplicativeFunctions

/-- MRTTZ Prop. 3.6 / MRT Fourier Prop. 3.2 (building the family of related phases). Given three
chained phase families (scales `(X,H)`, `(X/a₁,H/a₁)`, `(X/(a₁a₂),H/(a₁a₂))`) whose incidence
counts over the narrow prime ranges `[aᵢ,bᵢ]` are `≫ π₀(aᵢ)` as produced by two scaling-down
steps, there exist `P₁ ∈ [b₁/2, a₁]`, `P₂ ∈ [b₂, 2a₂]` with `P₁P₂ = a₁a₂` and a `QuadData` at
scale `(X/(P₁P₂), H/(P₁P₂))` with `≫ π₀(P₁)² X/H` edges related modulo `1/p₂` for
`≫ π₀(P₂)` primes `p₂ ∈ [P₂/2, P₂]`. -/
theorem quaddata_stage (k : ℕ) (hk : 1 ≤ k) (c₀ Cᵢ : ℝ) (hc₀ : 0 < c₀) (hCᵢ : 0 < Cᵢ) :
    ∃ c C A P₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < A ∧ 0 < P₀ ∧ c ≤ c₀ ∧
      ∀ (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) (X H a₁ b₁ a₂ b₂ c₁ c₂ : ℝ)
        (F₀ : PhaseFamily k f c₀ X H) (F₁ : PhaseFamily k f c₁ (X / a₁) (H / a₁))
        (F₂ : PhaseFamily k f c₂ (X / (a₁ * a₂)) (H / (a₁ * a₂))),
        c₀ ≤ c₁ → c₀ ≤ c₂ → P₀ ≤ a₁ → a₁ ≤ b₁ → 5 * b₁ ≤ 7 * a₁ → P₀ ≤ a₂ → a₂ ≤ b₂ →
        5 * b₂ ≤ 7 * a₂ → 200 * b₁ ^ 2 ≤ X / H → 0 < X →
        (∀ x' ∈ F₁.fam, c₀ * pi0 a₁ ≤
          ((incPairs k Cᵢ F₀.fam a₁ b₁ H (3 * H / a₁) (H / a₁) F₀.pol (F₁.pol x') x').card : ℝ)) →
        (∀ x'' ∈ F₂.fam, c₀ * pi0 a₂ ≤
          ((incPairs k Cᵢ F₁.fam a₂ b₂ (H / a₁) (3 * H / (a₁ * a₂)) (H / (a₁ * a₂))
            F₁.pol (F₂.pol x'') x'').card : ℝ)) →
        ∃ P₁ P₂ : ℝ, P₁ * P₂ = a₁ * a₂ ∧ b₁ / 2 ≤ P₁ ∧ P₁ ≤ a₁ ∧ b₂ ≤ P₂ ∧ P₂ ≤ 2 * a₂ ∧
          Nonempty (QuadData k f c C (X / (P₁ * P₂)) (H / (P₁ * P₂)) P₁ P₂) := by
  obtain ⟨Cπ, P₀π, hCπ, hP₀π, hprime⟩ := prime_card_le
  refine ⟨qdc c₀ Cπ, qdC k Cᵢ, 1, qdP₀ c₀ Cπ P₀π, ?_, ?_, by norm_num, ?_, ?_, ?_⟩
  · -- 0 < c
    exact lt_min hc₀ (lt_min (by positivity) (by positivity))
  · -- 0 < C
    have h1 : 0 < qdCone k Cᵢ := transConst_pos hCᵢ hCᵢ
    have h2 : 0 < symmConst k (qdCone k Cᵢ) := symmConst_pos h1
    have h3 : 0 < transConst k (symmConst k (qdCone k Cᵢ)) (qdCone k Cᵢ) := transConst_pos h2 h1
    exact lt_of_lt_of_le h3 (le_add_of_nonneg_right zero_le_one)
  · -- 0 < P₀
    exact lt_of_lt_of_le hP₀π (le_max_left _ _)
  · -- c ≤ c₀
    exact min_le_left _ _
  · intro f hf X H a₁ b₁ a₂ b₂ c₁ c₂ F₀ F₁ F₂ hcc₁ hcc₂ hP₀a₁ ha₁b₁ hn₁ hP₀a₂ ha₂b₂ hn₂ hXH hX hind₁ hind₂
    refine quaddata_aux k hk c₀ Cᵢ hc₀ hCᵢ Cπ P₀π hCπ hP₀π hprime
      (qdP₀ c₀ Cπ P₀π) (qdc c₀ Cπ) (qdC k Cᵢ)
      (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_right _ _))
      (le_trans (by norm_num) (le_trans (le_max_right _ _) (le_max_right _ _)))
      ?_ (min_le_left _ _) ?_ ?_ (le_add_of_nonneg_right zero_le_one)
      f hf X H a₁ b₁ a₂ b₂ c₁ c₂ F₀ F₁ F₂ hcc₁ hcc₂ hP₀a₁ ha₁b₁ hn₁ hP₀a₂ ha₂b₂ hn₂ hXH hX hind₁ hind₂
    · exact lt_min hc₀ (lt_min (by positivity) (by positivity))
    · exact min_le_right _ _ |>.trans (min_le_left _ _)
    · exact min_le_right _ _ |>.trans (min_le_right _ _)

end Work.BMF
