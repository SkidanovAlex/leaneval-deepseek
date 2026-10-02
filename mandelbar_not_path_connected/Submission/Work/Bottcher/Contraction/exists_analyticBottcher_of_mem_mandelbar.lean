import Mathlib
import Submission.Work.Bottcher.Defs
import Submission.Work.Escape.Defs
import Submission.Work.Escape.Basic
import Submission.Work.Escape.tendsto_greenIter
import Submission.Work.Bottcher.Green.greenParam_pos_iff
import Submission.Work.Bottcher.Green.green_comm
import Submission.Work.Bottcher.Green.green_pos_iff
import Submission.Work.Bottcher.Green.green_nonneg
import Submission.Work.Bottcher.Core.norm_bottcher_eq_exp_green
import Submission.Work.Bottcher.Contraction.exists_analytic_log_normFactor_of_mem_mandelbar
import Submission.Work.Bottcher.Contraction.tendsto_fourPow_inv_log_norm_pMap_iterate
import Submission.Work.Bottcher.Contraction.bExp_re
import Submission.Work.Bottcher.Contraction.analyticOnNhd_bExp
import Submission.Work.Bottcher.Contraction.tendsto_bExp
import Submission.Work.Bottcher.Contraction.bottcher_comm_Tantibar_of_analytic
import Submission.Work.Bottcher.Core.norm_iterate_pMap_ge

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter Function
open scoped Topology ComplexConjugate

namespace Work.Bottcher.Contraction

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-!
# Existence of the analytic Böttcher coordinate for tricorn parameters

The proof reduces the Böttcher theorem for the holomorphic quartic `p_c = T_c ∘ T_c` to the
existence of a *holomorphic logarithm* `L` of the normalised factor `p_c z / z^4` on the escape
set (the content of `exists_analytic_log_normFactor_of_mem_mandelbar`): with such an `L` one sets

`S z = ∑_k 4^{-(k+1)} L ((p_c)^[k] z)`,   `φ z = z * exp (S z)`.

Then `S (p_c z) = 4 S z - L z` (reindexing), so `exp (S (p_c z)) * η z = exp (4 S z)`
(`η = p_c z / z^4`) and `φ (p_c z) = φ z ^ 4`; the real part of the series telescopes to
`Re (S z) = G_c z - log ‖z‖`, giving `‖φ z‖ = exp (G_c z)`; and `S z → 0` at infinity gives
`φ z / z → 1`.
-/

/-- Hypothesis package: `L` is a holomorphic logarithm of the normalised factor
`p_c z / z ^ 4` on the escape set, which vanishes at infinity. -/
structure IsNormLog (c : ℂ) (L : ℂ → ℂ) : Prop where
  analytic : AnalyticOnNhd ℂ L (Work.Bottcher.EscapeSet c)
  exp_eq : ∀ z : ℂ, 0 < Work.Bottcher.green c z →
    Complex.exp (L z) = Work.Bottcher.pMap c z / z ^ 4
  tendsto : Tendsto L (cocompact ℂ) (nhds 0)

variable {c : ℂ} {L : ℂ → ℂ}


/-- For a mandelbar parameter the critical Green potential vanishes. -/
theorem greenParam_eq_zero_of_mem_mandelbar (c : ℂ) (hc : c ∈ Mandelbar) :
    Work.Bottcher.greenParam c = 0 := by
  refine le_antisymm ?_ (by simpa [Work.Bottcher.greenParam_def] using
    (Work.Bottcher.Green.green_nonneg c 0))
  by_contra h
  push_neg at h
  exact (Work.Bottcher.Green.greenParam_pos_iff c).mp h hc

/-- The Böttcher exponent series `S z = ∑_k 4^{-(k+1)} · L ((p_c)^[k] z)`. -/
noncomputable def bExp (c : ℂ) (L : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∑' k : ℕ, ((1 / 4 : ℝ) ^ (k + 1) : ℂ) * L ((Work.Bottcher.pMap c)^[k] z)

theorem bExp_def (c : ℂ) (L : ℂ → ℂ) (z : ℂ) :
    bExp c L z = ∑' k : ℕ, ((1 / 4 : ℝ) ^ (k + 1) : ℂ) * L ((Work.Bottcher.pMap c)^[k] z) := rfl


/-- The Green function of the second iterate: `G_c(p_c z) = 4 G_c z`. -/
theorem green_pMap_one (c z : ℂ) :
    Work.Bottcher.green c (Work.Bottcher.pMap c z) = 4 * Work.Bottcher.green c z := by
  rw [Work.Bottcher.pMap_eq_iterate_two, Function.iterate_succ_apply', Function.iterate_one,
    Work.Bottcher.Green.green_comm, Work.Bottcher.Green.green_comm]
  ring

/-- The Green function along the `p_c`-orbit: `G_c (p_c^k z) = 4^k G_c z`. -/
theorem green_pMap_iterate_pow (c z : ℂ) (k : ℕ) :
    Work.Bottcher.green c ((Work.Bottcher.pMap c)^[k] z) = 4 ^ k * Work.Bottcher.green c z := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', green_pMap_one, ih, pow_succ]
      ring

/-- The `p_c`-orbit of an escaping point tends to infinity. -/
theorem tendsto_iterate_pMap_cocompact (c : ℂ) {z : ℂ} (hz : 0 < Work.Bottcher.green c z) :
    Tendsto (fun k : ℕ => (Work.Bottcher.pMap c)^[k] z) atTop (cocompact ℂ) := by
  have hT : Tendsto (fun n : ℕ => ‖(Tantibar c)^[n] z‖) atTop atTop :=
    (Work.Bottcher.Green.green_pos_iff c z).mp hz
  have h2 : Tendsto (fun k : ℕ => 2 * k) atTop atTop :=
    tendsto_atTop_atTop.mpr (fun b => ⟨b, fun a ha => by omega⟩)
  have hnorm : Tendsto (fun k : ℕ => ‖(Work.Bottcher.pMap c)^[k] z‖) atTop atTop := by
    refine (hT.comp h2).congr' (Eventually.of_forall (fun k => ?_))
    simp only [Function.comp_apply]
    rw [Work.Bottcher.pMap_iterate]
  exact tendsto_cocompact_of_tendsto_dist_comp_atTop 0 (by simpa using hnorm)

/-- The terms of the Böttcher series are summable at every escaping point. -/
theorem summable_bExp_terms (hL : IsNormLog c L) {z : ℂ}
    (hz : 0 < Work.Bottcher.green c z) :
    Summable (fun k : ℕ => ((1 / 4 : ℝ) ^ (k + 1) : ℂ) * L ((Work.Bottcher.pMap c)^[k] z)) := by
  have hbdd : ∀ᶠ w : ℂ in cocompact ℂ, ‖L w‖ ≤ 1 := by
    have h0 : Tendsto (fun w : ℂ => ‖L w‖) (cocompact ℂ) (nhds (0 : ℝ)) := by
      simpa using hL.tendsto.norm
    exact h0.eventually (eventually_le_nhds zero_lt_one)
  have hkle : ∀ᶠ k : ℕ in atTop, ‖L ((Work.Bottcher.pMap c)^[k] z)‖ ≤ 1 :=
    (tendsto_iterate_pMap_cocompact c hz).eventually hbdd
  refine Summable.of_norm_bounded_eventually_nat (g := fun k : ℕ => (1 / 4 : ℝ) ^ k)
    (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
      (by norm_num : (1 / 4 : ℝ) < 1)) ?_
  filter_upwards [hkle] with k hk
  have hcoef : ‖(((1 / 4 : ℝ) ^ (k + 1) : ℂ))‖ = (1 / 4 : ℝ) ^ (k + 1) := by
    rw [← Complex.ofReal_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [norm_mul, hcoef]
  have hmono : (1 / 4 : ℝ) ^ (k + 1) ≤ (1 / 4 : ℝ) ^ k :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ k)
  calc (1 / 4 : ℝ) ^ (k + 1) * ‖L ((Work.Bottcher.pMap c)^[k] z)‖
      ≤ (1 / 4 : ℝ) ^ (k + 1) * 1 := mul_le_mul_of_nonneg_left hk (by positivity)
    _ = (1 / 4 : ℝ) ^ (k + 1) := mul_one _
    _ ≤ (1 / 4 : ℝ) ^ k := hmono

/-- **The shift identity**: the Böttcher series of `p_c z` is `4 S z - L z`, which is exactly the
statement that `φ = z * exp S` solves the Böttcher equation of `p_c`. -/
theorem bExp_shift (hL : IsNormLog c L) {z : ℂ} (hz : 0 < Work.Bottcher.green c z) :
    bExp c L (Work.Bottcher.pMap c z) = 4 * bExp c L z - L z := by
  classical
  set F : ℕ → ℂ := fun k => ((1 / 4 : ℝ) ^ (k + 1) : ℂ) * L ((Work.Bottcher.pMap c)^[k] z) with hF
  have hsum : Summable F := summable_bExp_terms hL hz
  have hz1 : 0 < Work.Bottcher.green c (Work.Bottcher.pMap c z) := by
    rw [show Work.Bottcher.green c (Work.Bottcher.pMap c z)
        = 4 * Work.Bottcher.green c z from green_pMap_one c z]
    positivity
  have hsum1 : Summable (fun k : ℕ => ((1 / 4 : ℝ) ^ (k + 1) : ℂ) *
      L ((Work.Bottcher.pMap c)^[k] (Work.Bottcher.pMap c z))) :=
    summable_bExp_terms hL hz1
  -- reindex the left hand side
  have hcoe : ∀ k : ℕ, ((1 / 4 : ℝ) ^ (k + 1) : ℂ) = 4 * ((1 / 4 : ℝ) ^ (k + 2) : ℂ) := by
    intro k
    rw [pow_succ]
    push_cast
    ring
  have hleft : bExp c L (Work.Bottcher.pMap c z) = 4 * (∑' k : ℕ, F (k + 1)) := by
    rw [bExp_def]
    have hfun : (fun k : ℕ => ((1 / 4 : ℝ) ^ (k + 1) : ℂ) *
          L ((Work.Bottcher.pMap c)^[k] (Work.Bottcher.pMap c z)))
        = fun k : ℕ => 4 * F (k + 1) := by
      funext k
      rw [hF, ← Function.iterate_succ_apply]
      rw [hcoe k]
      ring
    rw [hfun, tsum_mul_left]
  have htail : (∑' k : ℕ, F (k + 1)) = bExp c L z - F 0 := by
    have h := hsum.sum_add_tsum_nat_add 1
    rw [Finset.sum_range_one] at h
    have h' : (∑' k : ℕ, F (k + 1)) = (∑' k : ℕ, F k) - F 0 := by
      rw [eq_sub_iff_add_eq, add_comm]
      exact h
    rw [bExp_def]
    rw [show (fun k : ℕ => ((1 / 4 : ℝ) ^ (k + 1) : ℂ) * L ((Work.Bottcher.pMap c)^[k] z)) = F from
      (funext fun k => by rw [hF])]
    exact h'
  rw [hleft, htail, hF]
  simp only [Function.iterate_zero_apply]
  push_cast
  ring

/-- The Böttcher series is holomorphic on the escape set (this is
`Work.Bottcher.Contraction.analyticOnNhd_bExp` restated for `bExp`). -/
theorem analyticOnNhd_bExp' (hL : IsNormLog c L) :
    AnalyticOnNhd ℂ (bExp c L) (Work.Bottcher.EscapeSet c) := by
  show AnalyticOnNhd ℂ (fun z : ℂ => ∑' k : ℕ, ((1 / 4 : ℝ) ^ (k + 1) : ℂ) *
      L ((Work.Bottcher.pMap c)^[k] z)) (Work.Bottcher.EscapeSet c)
  exact analyticOnNhd_bExp c hL.analytic hL.tendsto

/-- The Böttcher series vanishes at infinity. -/
theorem bExp_tendsto_zero (hL : IsNormLog c L) :
    Tendsto (bExp c L) (cocompact ℂ) (nhds (0 : ℂ)) := by
  show Tendsto (fun z : ℂ => ∑' k : ℕ, ((1 / 4 : ℝ) ^ (k + 1) : ℂ) *
      L ((Work.Bottcher.pMap c)^[k] z)) (cocompact ℂ) (nhds 0)
  exact tendsto_bExp c hL.tendsto

/-- **The analytic Böttcher coordinate of the tricorn at a mandelbar parameter.** -/
theorem exists_analyticBottcher_of_mem_mandelbar (c : ℂ)
    (hc : c ∈ LeanEval.ComplexAnalysis.Mandelbar) :
    ∃ φ : ℂ → ℂ,
      AnalyticOnNhd ℂ φ (Work.Bottcher.EscapeSet c) ∧
        (∀ z : ℂ, 0 < Work.Bottcher.green c z → φ (Work.Bottcher.pMap c z) = (φ z) ^ 4) ∧
        (∀ z : ℂ, 0 < Work.Bottcher.green c z →
          ‖φ z‖ = Real.exp (Work.Bottcher.green c z)) ∧
        Filter.Tendsto (fun z : ℂ => φ z / z) (Filter.cocompact ℂ) (nhds (1 : ℂ)) := by
  obtain ⟨L, h1, h2, h3⟩ := exists_analytic_log_normFactor_of_mem_mandelbar c hc
  have hL : IsNormLog c L := ⟨h1, h2, h3⟩
  have hg0 : Work.Bottcher.green c 0 = 0 := by
    rw [← Work.Bottcher.greenParam_def]
    exact greenParam_eq_zero_of_mem_mandelbar c hc
  have hzne : ∀ z : ℂ, 0 < Work.Bottcher.green c z → z ≠ 0 := by
    intro z hz rfl
    rw [hg0] at hz
    exact lt_irrefl 0 hz
  refine ⟨fun z => z * Complex.exp (bExp c L z), ?_, ?_, ?_, ?_⟩
  · exact analyticOnNhd_id.mul (analyticOnNhd_bExp' hL).cexp
  · intro z hz
    have hz0 : z ≠ 0 := hzne z hz
    have hLz := hL.exp_eq z hz
    have hpc : Work.Bottcher.pMap c z ≠ 0 := by
      intro h
      rw [h, zero_div] at hLz
      exact Complex.exp_ne_zero (L z) hLz
    have hS := bExp_shift hL hz
    have hexp4 : Complex.exp (4 * bExp c L z) = Complex.exp (bExp c L z) ^ 4 := by
      simpa using (Complex.exp_nat_mul (bExp c L z) 4)
    calc (Work.Bottcher.pMap c z) * Complex.exp (bExp c L (Work.Bottcher.pMap c z))
        = (Work.Bottcher.pMap c z) * Complex.exp (4 * bExp c L z - L z) := by rw [hS]
      _ = (Work.Bottcher.pMap c z) * (Complex.exp (bExp c L z) ^ 4 / Complex.exp (L z)) := by
          rw [Complex.exp_sub, hexp4]
      _ = (Work.Bottcher.pMap c z) * (Complex.exp (bExp c L z) ^ 4 / (Work.Bottcher.pMap c z / z ^ 4)) := by
          rw [hLz]
      _ = (z * Complex.exp (bExp c L z)) ^ 4 := by
          field_simp
  · intro z hz
    have hz0 : z ≠ 0 := hzne z hz
    have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    have hre : (bExp c L z).re = Work.Bottcher.green c z - Real.log ‖z‖ := by
      rw [bExp_def]
      exact bExp_re c hL.analytic hL.exp_eq hL.tendsto hg0 hz hz0
    rw [norm_mul, Complex.norm_exp, hre, Real.exp_sub, Real.exp_log hzpos]
    field_simp
  · have h1' : Tendsto (fun z : ℂ => Complex.exp (bExp c L z)) (cocompact ℂ) (nhds 1) := by
      simpa using (bExp_tendsto_zero hL).cexp
    refine h1'.congr' ?_
    have hne : ∀ᶠ z : ℂ in cocompact ℂ, z ≠ 0 := by
      refine Filter.mem_cocompact.2 ⟨{0}, isCompact_singleton, ?_⟩
      intro z hz
      simpa using hz
    filter_upwards [hne] with z hz
    field_simp

end Work.Bottcher.Contraction
