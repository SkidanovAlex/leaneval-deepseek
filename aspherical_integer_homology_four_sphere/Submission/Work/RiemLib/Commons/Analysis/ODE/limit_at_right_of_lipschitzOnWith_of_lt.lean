import Mathlib.Analysis.Normed.Order.Lattice

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Commons.Analysis.ODE

open Filter
open scoped Topology
open scoped NNReal

set_option autoImplicit false

lemma limit_at_right_of_lipschitzOnWith_of_lt {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {f : ℝ → E} {a b : ℝ} {K : ℝ≥0} (hab : a < b) (h : LipschitzOnWith K f (Set.Ioo a b)) :
    ∃ l : E, Tendsto f (𝓝[<] b) (𝓝 l) := by
  have hK : (0 : ℝ) ≤ (K : ℝ) := NNReal.coe_nonneg K
  have hcauchy : Cauchy (map f (𝓝[<] b)) := by
    rw [Metric.cauchy_iff]
    refine ⟨?_, ?_⟩
    · rw [map_neBot_iff]; infer_instance
    · intro ε hε
      obtain ⟨r, hrb, hr⟩ : ∃ r : ℝ, r < b ∧ (K : ℝ) * (b - r) < ε := by
        refine ⟨b - ε / ((K : ℝ) + 1), ?_, ?_⟩
        · have : 0 < ε / ((K : ℝ) + 1) := div_pos hε (by positivity)
          linarith
        · rw [sub_sub_cancel, ← mul_div_assoc,
            div_lt_iff₀ (by positivity : (0 : ℝ) < (K : ℝ) + 1)]
          nlinarith [hε, hK]
      have hmb : max a r < b := max_lt hab hrb
      have ham : a ≤ max a r := le_max_left a r
      have hrm : r ≤ max a r := le_max_right a r
      refine ⟨f '' Set.Ioo (max a r) b, ?_, ?_⟩
      · rw [Filter.mem_map]
        exact mem_of_superset (Ioo_mem_nhdsLT hmb) (fun x hx => ⟨x, hx, rfl⟩)
      · intro x hx y hy
        rcases hx with ⟨p, hp, rfl⟩
        rcases hy with ⟨q, hq, rfl⟩
        have hpab : p ∈ Set.Ioo a b := ⟨lt_of_le_of_lt ham hp.1, hp.2⟩
        have hqab : q ∈ Set.Ioo a b := ⟨lt_of_le_of_lt ham hq.1, hq.2⟩
        have hdist : dist p q ≤ b - max a r := by
          rw [Real.dist_eq, abs_sub_le_iff]
          exact ⟨by linarith [hp.1, hp.2, hq.1, hq.2],
                 by linarith [hp.1, hp.2, hq.1, hq.2]⟩
        calc dist (f p) (f q) ≤ (K : ℝ) * dist p q := h.dist_le_mul p hpab q hqab
          _ ≤ (K : ℝ) * (b - max a r) := mul_le_mul_of_nonneg_left hdist hK
          _ ≤ (K : ℝ) * (b - r) := mul_le_mul_of_nonneg_left (by linarith) hK
          _ < ε := hr
  obtain ⟨l, hl⟩ := CompleteSpace.complete hcauchy
  exact ⟨l, hl⟩

end Commons.Analysis.ODE