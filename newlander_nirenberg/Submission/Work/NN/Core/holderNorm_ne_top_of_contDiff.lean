/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# Finiteness of the `C^{k,α}` norm of a smooth function on a polydisc

A globally `C^{k+1}` function has finite `C^{k,α}` norm on every *bounded* open set,
for `0 < α ≤ 1`:

* the iterated derivatives of order `i ≤ k` are continuous, hence bounded on the
  (compact) closure of a ball containing the set;
* the `i`-th iterated derivative is itself `C^1` (as `i < k + 1`), hence Lipschitz
  on that ball, and a Lipschitz function with bounded divided differences of
  exponent `1` has bounded divided differences of every exponent `α ≤ 1`
  (`div_rpow_le_max`).

Applied to `Ω = polydisc 0 ρ ⊆ closedBall 0 R` with `R = ∑ⱼ max 0 (ρⱼ) ≥ 0`
(so that `R` is an upper bound for every `ρⱼ`, and `Ω` is empty whenever some
`ρⱼ ≤ 0`, in which case all suprema vanish), this gives
`Work.NN.Core.holderNorm_ne_top_of_contDiff`.
-/
import Mathlib
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Polydisc

namespace Work.NN.Core

open scoped NNReal ENNReal ContDiff
open Set

/-- Elementary Hölder estimate: if `q ≤ 2 C`, `q ≤ L d` with `C, L ≥ 0`, `d > 0` and
`0 ≤ α ≤ 1`, then `q / d ^ α ≤ max L (2 C)`.  Small distances are controlled by the
Lipschitz bound (`d ^ (1 - α) ≤ 1`), large ones by the sup bound (`d ^ (-α) ≤ 1`). -/
private lemma div_rpow_le_max {d q C L α : ℝ} (hC : 0 ≤ C) (hL : 0 ≤ L) (hd : 0 < d)
    (hqd : q ≤ 2 * C) (hlip : q ≤ L * d) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    q / d ^ α ≤ max L (2 * C) := by
  have hdle : 0 ≤ d := le_of_lt hd
  have hsub : d / d ^ α = d ^ (1 - α) := by rw [Real.rpow_sub hd (1 : ℝ) α, Real.rpow_one]
  by_cases h1 : d ≤ 1
  · have hp : d ^ (1 - α) ≤ 1 := Real.rpow_le_one hdle h1 (by linarith)
    calc q / d ^ α ≤ (L * d) / d ^ α :=
          div_le_div_of_nonneg_right hlip (Real.rpow_nonneg hdle α)
      _ = L * (d / d ^ α) := by rw [mul_div_assoc]
      _ = L * d ^ (1 - α) := by rw [hsub]
      _ ≤ L * 1 := mul_le_mul_of_nonneg_left hp hL
      _ = L := mul_one L
      _ ≤ max L (2 * C) := le_max_left _ _
  · have h1' : 1 ≤ d := le_of_lt (not_le.mp h1)
    have hαle : 1 ≤ d ^ α := Real.one_le_rpow h1' hα0
    calc q / d ^ α ≤ (2 * C) / d ^ α :=
          div_le_div_of_nonneg_right hqd (Real.rpow_nonneg hdle α)
      _ ≤ 2 * C := div_le_self (by linarith) hαle
      _ ≤ max L (2 * C) := le_max_right _ _

theorem holderNorm_ne_top_of_contDiff {n : ℕ} {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {ρ : Fin n → ℝ} {k : ℕ} {f : (Fin n → ℂ) → ℂ}
    (hf : ContDiff ℝ (k + 1) f) :
    Work.CR.Flat.holderNorm k α f (Work.CR.Flat.polydisc 0 ρ) ≠ ⊤ := by
  set Ω : Set (Fin n → ℂ) := Work.CR.Flat.polydisc 0 ρ with hΩdef
  have hΩopen : IsOpen Ω := Work.CR.Flat.isOpen_polydisc 0 ρ
  -- an explicit radius containing the polydisc
  set R : ℝ := ∑ j : Fin n, max 0 (ρ j) with hRdef
  have hR0 : 0 ≤ R := Finset.sum_nonneg fun j _ => le_max_left 0 (ρ j)
  have hleR : ∀ j, ρ j ≤ R := fun j =>
    (le_max_right 0 (ρ j)).trans
      (Finset.single_le_sum (fun i _ => le_max_left 0 (ρ i)) (Finset.mem_univ j))
  have hRsub : Ω ⊆ Metric.closedBall (0 : Fin n → ℂ) R := by
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg hR0]
    intro j
    simpa using (hz j).le.trans (hleR j)
  -- all iterated derivatives up to order `k+1` are bounded on that ball
  have hbdd : ∀ i ≤ k + 1, ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ Metric.closedBall (0 : Fin n → ℂ) R, ‖iteratedFDeriv ℝ i f x‖ ≤ C := by
    intro i hi
    obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : Fin n → ℂ) R).exists_bound_of_continuousOn
      ((hf.continuous_iteratedFDeriv (m := i) (by exact_mod_cast hi)).continuousOn)
    exact ⟨max B 0, le_max_right _ _, fun x hx => (hB x hx).trans (le_max_left _ _)⟩
  rw [Work.CR.Flat.holderNorm, ENNReal.sum_ne_top]
  intro i hi
  rw [Finset.mem_range] at hi
  have hik : i ≤ k := Nat.lt_succ_iff.mp hi
  rw [ENNReal.add_ne_top]
  constructor
  · -- the sup of the `i`-th derivative
    obtain ⟨C, hC0, hC⟩ := hbdd i (by omega)
    have hle : Work.CR.Flat.iterDerivNorm i f Ω ≤ ENNReal.ofReal C := by
      simp only [Work.CR.Flat.iterDerivNorm]
      refine iSup₂_le fun x hx => ?_
      rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (s := Ω) (f := f) i hΩopen hx]
      exact ENNReal.ofReal_le_ofReal (hC x (hRsub hx))
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  · -- the Hölder seminorm of the `i`-th derivative
    obtain ⟨C, hC0, hC⟩ := hbdd i (by omega)
    obtain ⟨L, hL0, hL⟩ := hbdd (i + 1) (by omega)
    have hle : Work.CR.Flat.holderSeminorm i α f Ω ≤ ENNReal.ofReal (max L (2 * C)) := by
      simp only [Work.CR.Flat.holderSeminorm]
      refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
      rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (s := Ω) (f := f) i hΩopen hx,
        iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (s := Ω) (f := f) i hΩopen hy]
      refine ENNReal.ofReal_le_ofReal ?_
      have hdiff : ∀ z, DifferentiableAt ℝ (iteratedFDeriv ℝ i f) z :=
        hf.differentiable_iteratedFDeriv (m := i)
          (by exact_mod_cast (show i < k + 1 by omega))
      have hlip : ‖iteratedFDeriv ℝ i f x - iteratedFDeriv ℝ i f y‖ ≤ L * ‖x - y‖ := by
        have h := Convex.norm_image_sub_le_of_norm_fderiv_le
          (f := iteratedFDeriv ℝ i f) (s := Metric.closedBall (0 : Fin n → ℂ) R) (C := L)
          (fun z _ => hdiff z)
          (fun z hz => by rw [norm_fderiv_iteratedFDeriv]; exact hL z hz)
          (convex_closedBall _ _) (hRsub hx) (hRsub hy)
        simpa only [norm_sub_rev] using h
      exact div_rpow_le_max (d := ‖x - y‖)
        (q := ‖iteratedFDeriv ℝ i f x - iteratedFDeriv ℝ i f y‖) hC0 hL0
        (norm_pos_iff.mpr (sub_ne_zero.mpr hxy))
        (by linarith [hC x (hRsub hx), hC y (hRsub hy),
          norm_sub_le (iteratedFDeriv ℝ i f x) (iteratedFDeriv ℝ i f y)])
        hlip (le_of_lt hα) hα1
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle

end Work.NN.Core
