import Mathlib
import Submission.Work.PARIMPL.ParSplit.ParWall
import Submission.Work.PARIMPL.ParSplit.g_mem_of_split

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option maxRecDepth 4000
set_option autoImplicit false
set_option linter.unusedVariables false

open Classical Filter Set Metric
open scoped Topology
open Polynomial

noncomputable section

namespace Work.PARIMPL.ParSplit

open LeanEval.ComplexAnalysis (Tantibar)

variable {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}

/-! ## Algebraic preliminaries -/

/-- `star ∘ Tantibar` is a holomorphic quadratic: `star (Tantibar c w) = w² + star c`. -/
theorem star_Tantibar (c w : ℂ) : star (Tantibar c w) = w ^ 2 + star c := by
  simp only [Tantibar, star_add, star_pow, starRingEnd_apply, star_star]

/-- The holomorphic second iterate `Tsq c` is `(Tantibar c)^[2]`. -/
theorem Tsq_eq_iterate_Tantibar (c : ℂ) : Work.Landing.Tsq c = (Tantibar c)^[2] := by
  funext z
  rw [show (2:ℕ) = 1 + 1 from rfl, Function.iterate_add_apply, Function.iterate_one]
  simp [Work.Landing.Tsq, Tantibar, map_add, map_pow]

/-- **`Gpoly` is the holomorphic partner of the antiholomorphic square root**: `G_c(u)` is the
conjugate of `g(u) = (T_c)^[5] u`. -/
theorem eval_Gpoly_eq_star_gtc (c u : ℂ) : (Gpoly c).eval u = star (gtc c u) := by
  rw [Gpoly_eval]
  have hiter : (Work.Landing.Tsq c)^[2] u = (Tantibar c)^[4] u := by
    rw [Tsq_eq_iterate_Tantibar c, ← Function.iterate_mul]
  rw [hiter]
  show ((Tantibar c)^[4] u)^2 + star c = star ((Tantibar c)^[5] u)
  rw [Function.iterate_succ_apply' (Tantibar c) 4 u, star_Tantibar]

/-- `star (a / b) = star a / star b` for `ℂ`. -/
theorem star_div_ℂ (a b : ℂ) : star (a / b) = star a / star b := by simp

/-- `star (a / 2) = star a / 2`. -/
theorem star_div_two (a : ℂ) : star (a / 2) = star a / 2 := by
  rw [star_div_ℂ]
  norm_num

/-- The conjugate of a symmetric difference quotient of conjugates. -/
theorem star_diff_quot (a b E : ℂ) :
    star ((star a - star b) / E) = (a - b) / star E := by
  rw [star_div_ℂ, star_sub, star_star, star_star]

/-- The elementary identity `g (g z) = Ft z`. -/
theorem gtc_comp_apply (c z : ℂ) : gtc c (gtc c z) = Ft c z := by
  rw [← Function.comp_apply (f := gtc c) (g := gtc c), ← Ft_eq_g_comp c]

/-- For `z ≠ 0`, `z / conj z = z² / normSq z`. -/
theorem div_star_eq (z : ℂ) (hz : z ≠ 0) :
    z / star z = z ^ 2 / ((Complex.normSq z : ℝ) : ℂ) := by
  have hsz : star z ≠ 0 := by
    intro h
    exact hz (by rw [← star_star z, h, star_zero])
  have hn : ((Complex.normSq z : ℝ) : ℂ) ≠ 0 := by
    rw [← Complex.mul_conj z]
    exact mul_ne_zero hz hsz
  rw [div_eq_div_iff hsz hn, ← Complex.mul_conj z]
  simp only [starRingEnd_apply]
  ring

/-! ## The symmetric difference quotient `parH` is a difference quotient of `Gam` -/

/-- The degree bound for the shifted polynomial `Gam`. -/
theorem natDegree_Gam (S : SplitData d) (c : ℂ) : (Gam S c).natDegree ≤ wallN := by
  rw [Gam]
  calc ((Gpoly c).comp (X + C (S.m c))).natDegree
      ≤ (Gpoly c).natDegree * (X + C (S.m c)).natDegree := natDegree_comp_le
    _ ≤ 32 * 1 := by
        apply Nat.mul_le_mul (natDegree_Gpoly c)
        calc (X + C (S.m c) : Polynomial ℂ).natDegree
            ≤ max (X : Polynomial ℂ).natDegree (C (S.m c)).natDegree := natDegree_add_le _ _
          _ ≤ 1 := by rw [natDegree_X, natDegree_C]; simp
    _ ≤ wallN := by norm_num [wallN]

/-- Evaluation of the shifted polynomial `Gam`. -/
theorem Gam_eval (S : SplitData d) (c w : ℂ) :
    (Gam S c).eval w = (Gpoly c).eval (S.m c + w) := by
  rw [Gam, eval_comp, eval_add, eval_X, eval_C, add_comm]

/-- **The core identity**: the symmetric difference quotient `parH` is the difference quotient
`(Gam Δ − Gam (−Δ))/E` of the shifted polynomial `Gam`, `Δ = E/2`. -/
theorem eval_sub_eval_neg_Gam (S : SplitData d) (c : ℂ) :
    (Gam S c).eval (S.E c / 2) - (Gam S c).eval (-(S.E c / 2)) = S.E c * parH S c := by
  have hlt : (Gam S c).natDegree < wallN + 1 := Nat.lt_succ_of_le (natDegree_Gam S c)
  rw [eval_eq_sum_range' hlt (S.E c / 2), eval_eq_sum_range' hlt (-(S.E c / 2)), parH]
  set Δ := S.E c / 2 with hΔdef
  rw [show S.E c = 2 * Δ from by rw [hΔdef]; ring]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro l hl
  simp only [gam]
  by_cases h : l % 2 = 1
  · rw [if_pos h, Odd.neg_pow (Nat.odd_iff.mpr h)]
    have hl1 : 1 ≤ l := by omega
    have hpow : Δ ^ l = Δ ^ (l - 1) * Δ := by
      conv_lhs => rw [show l = (l - 1) + 1 from (Nat.sub_add_cancel hl1).symm]
      rw [pow_succ]
    rw [hpow]; ring
  · rw [if_neg h, mul_zero]
    have hev : Even l := by
      rw [Nat.even_iff]
      have := Nat.mod_lt l (by norm_num : 0 < 2)
      omega
    rw [hev.neg_pow]
    ring

/-- `parH` as a difference quotient of `Gpoly` at the two split fixed points. -/
theorem parH_eq (S : SplitData d) (c : ℂ) (hE : S.E c ≠ 0) :
    parH S c
      = ((Gpoly c).eval (S.m c + S.E c / 2) - (Gpoly c).eval (S.m c - S.E c / 2))
          / S.E c := by
  have h := eval_sub_eval_neg_Gam S c
  rw [Gam_eval, Gam_eval] at h
  rw [show S.m c + -(S.E c / 2) = S.m c - S.E c / 2 from by ring] at h
  rw [h, mul_div_cancel_left₀ (parH S c) hE]

/-! ## `Gc / ‖Gc‖` is the normalized square of the half-difference -/

/-- `Gc S c / ‖Gc S c‖ = (S.E c) / conj (S.E c)` whenever `S.E c ≠ 0`. -/
theorem Gc_div_norm_eq (S : SplitData d) (c : ℂ) (hE : S.E c ≠ 0) :
    Gc S c / (‖Gc S c‖ : ℂ) = S.E c / star (S.E c) := by
  have hΔ : S.E c / 2 ≠ 0 := by
    intro h; exact hE (by linear_combination 2 * h)
  have hnorm : ‖Gc S c‖ = Complex.normSq (S.E c / 2) := by
    rw [Gc, norm_pow, Complex.normSq_eq_norm_sq]
  have h1 : Gc S c / (‖Gc S c‖ : ℂ) = (S.E c / 2) / star (S.E c / 2) := by
    rw [hnorm, Gc, ← div_star_eq (S.E c / 2) hΔ]
  rw [h1, star_div_two,
    div_div_div_cancel_right₀ (show (2 : ℂ) ≠ 0 by norm_num) (S.E c) (star (S.E c))]

/-! ## The minus version of `g_mem_of_split` -/

/-- The image of the **second** split fixed point under `g` stays in the dynamical disc. -/
theorem g_mem_of_split_sub (S : SplitData d) :
    ∃ ρ' : ℝ, 0 < ρ' ∧ ρ' ≤ S.ρ ∧
      ∀ c ∈ Metric.ball c₀ ρ', gtc c (S.m c - S.E c / 2) ∈ Metric.ball d.z₁ S.R := by
  have hmem : c₀ ∈ ball c₀ S.ρ := mem_ball_self S.hρ
  have hm : ContinuousAt S.m c₀ := S.cont_m.continuousAt (isOpen_ball.mem_nhds hmem)
  have hE : ContinuousAt S.E c₀ := S.cont_E.continuousAt (isOpen_ball.mem_nhds hmem)
  have hpair : ContinuousAt (fun c : ℂ => (c, S.m c - S.E c / 2)) c₀ :=
    continuousAt_id.prodMk (hm.sub (hE.div_const 2))
  have hcontΦ' : ContinuousAt (fun c : ℂ => (Tantibar c)^[5] (S.m c - S.E c / 2)) c₀ :=
    ContinuousAt.comp (f := fun c : ℂ => (c, S.m c - S.E c / 2)) (x := c₀)
      continuous_gtc_prod.continuousAt hpair
  have hcontΦ : ContinuousAt (fun c : ℂ => gtc c (S.m c - S.E c / 2)) c₀ := hcontΦ'
  have hbase : gtc c₀ (S.m c₀ - S.E c₀ / 2) = d.z₁ := by
    rw [S.m₀, S.E₀, zero_div, sub_zero]
    exact d.per_half
  have hmem0 : gtc c₀ (S.m c₀ - S.E c₀ / 2) ∈ ball d.z₁ S.R := by
    rw [hbase]; exact mem_ball_self S.hR
  obtain ⟨ε, hε0, hε⟩ := Metric.mem_nhds_iff.mp
    (hcontΦ.preimage_mem_nhds (isOpen_ball.mem_nhds hmem0))
  exact ⟨min S.ρ ε, lt_min S.hρ hε0, min_le_left _ _, fun c hc =>
    hε (mem_ball.mpr (lt_of_lt_of_le (mem_ball.mp hc) (min_le_right _ _)))⟩

/-! ## The main statement -/

theorem parLam_eq {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}
    (S : Work.PARIMPL.ParSplit.SplitData d) :
    ∃ ρ' > 0, ρ' ≤ S.ρ ∧ ∀ c ∈ Metric.ball c₀ ρ',
      (Work.PARIMPL.ParSplit.Gc S c ≠ 0 →
        Work.PARIMPL.ParSplit.parLam S c
          = ((Work.PARIMPL.ParSplit.parSigma S c : ℂ) * Work.PARIMPL.ParSplit.Gc S c)
              / ‖Work.PARIMPL.ParSplit.Gc S c‖) := by
  obtain ⟨ρ₁, hρ₁, hρ₁ρ, hmem₁⟩ := g_mem_of_split S
  obtain ⟨ρ₂, hρ₂, hρ₂ρ, hmem₂⟩ := g_mem_of_split_sub S
  refine ⟨min ρ₁ ρ₂, lt_min hρ₁ hρ₂, le_trans (min_le_left _ _) hρ₁ρ, ?_⟩
  intro c hc hGc
  rw [mem_ball] at hc
  have hcρ : c ∈ ball c₀ S.ρ :=
    mem_ball.mpr (lt_of_lt_of_le hc (le_trans (min_le_left _ _) hρ₁ρ))
  have hc₁ : c ∈ ball c₀ ρ₁ := mem_ball.mpr (lt_of_lt_of_le hc (min_le_left _ _))
  have hc₂ : c ∈ ball c₀ ρ₂ := mem_ball.mpr (lt_of_lt_of_le hc (min_le_right _ _))
  have hE : S.E c ≠ 0 := by
    intro h; exact hGc (by rw [Gc]; simp [h])
  have hmem₁' : gtc c (S.m c + S.E c / 2) ∈ ball d.z₁ S.R := hmem₁ c hc₁
  have hmem₂' : gtc c (S.m c - S.E c / 2) ∈ ball d.z₁ S.R := hmem₂ c hc₂
  rw [parLam, parH_eq S c hE, eval_Gpoly_eq_star_gtc, eval_Gpoly_eq_star_gtc]
  have hdich := S.swap_or_fix_of_split hcρ hmem₁'
  by_cases hA : gtc c (S.m c + S.E c / 2) = S.m c - S.E c / 2
  · -- swap side: `parSigma = -1`
    have hσ : parSigma S c = -1 := by rw [parSigma]; exact if_pos hA
    have hB : gtc c (S.m c - S.E c / 2) = S.m c + S.E c / 2 := by
      rw [← hA, gtc_comp_apply]
      exact S.fixed_add c hcρ
    rw [hA, hB, hσ]
    rw [show ((-1 : ℝ) : ℂ) = -1 from by norm_num]
    rw [show ((-1 : ℂ) * Gc S c) / (‖Gc S c‖ : ℂ) = -(Gc S c / (‖Gc S c‖ : ℂ))
          from by ring]
    rw [Gc_div_norm_eq S c hE]
    rw [star_diff_quot (S.m c - S.E c / 2) (S.m c + S.E c / 2) (S.E c)]
    rw [show (S.m c - S.E c / 2) - (S.m c + S.E c / 2) = -S.E c from by ring]
    ring
  · -- fix side: `parSigma = 1`
    have hgp : gtc c (S.m c + S.E c / 2) = S.m c + S.E c / 2 := by
      rcases hdich with h | h
      · exact h
      · exact absurd h hA
    have hσ : parSigma S c = 1 := by rw [parSigma]; exact if_neg hA
    have h1 : gtc c (gtc c (S.m c - S.E c / 2)) = S.m c - S.E c / 2 := by
      rw [gtc_comp_apply]
      exact S.fixed_sub c hcρ
    have hgn : gtc c (S.m c - S.E c / 2) = S.m c - S.E c / 2 := by
      have hfix : Ft c (gtc c (S.m c - S.E c / 2)) = gtc c (S.m c - S.E c / 2) := by
        rw [Ft_eq_g_comp, Function.comp_apply, h1]
      rcases (S.unique c hcρ _ hmem₂').mp hfix with h | h
      · exfalso
        have hnp : S.m c - S.E c / 2 = S.m c + S.E c / 2 := by
          rw [← h1, h, hgp]
        have : S.E c = 0 := by linear_combination (-1 : ℂ) * hnp
        exact hE this
      · exact h
    rw [hgp, hgn, hσ]
    rw [show ((1 : ℝ) : ℂ) = 1 from by norm_num]
    rw [one_mul, Gc_div_norm_eq S c hE]
    rw [star_diff_quot (S.m c + S.E c / 2) (S.m c - S.E c / 2) (S.E c)]
    rw [show (S.m c + S.E c / 2) - (S.m c - S.E c / 2) = S.E c from by ring]

end Work.PARIMPL.ParSplit
