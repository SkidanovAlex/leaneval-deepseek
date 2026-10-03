import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Repel.Basic
import Submission.Work.Repel.Spec
import Submission.Work.Repel.Setup
import Submission.Work.Repel.step1_point
import Submission.Work.Repel.dim_arith
import Submission.Work.Repel.alphaOf_bounds
import Submission.Work.Repel.rotOf_fam
import Submission.Work.Repel.rotOf_pushdown_rescale
import Submission.Work.Repel.pushdown_deriv
import Submission.Work.Repel.germ1_differentiableOn
import Submission.Work.Repel.level1_close
import Submission.Work.Repel.lift_cover
import Submission.Work.Repel.returns_to_ifs
import Submission.Work.Repel.setup_exists
import Submission.Work.Repel.chain_setup_exists
import Submission.Work.Repel.end_bound_piExp
import Submission.Work.Repel.counting
import Submission.Work.Repel.boxes

import Submission.Work.Repel.end_bound_piExp
import Submission.Work.Repel.alphaOf_exp_eq
import Submission.Work.Repel.boxes_full_period

namespace Work.Repel

open MandelDim Complex Set Metric Filter Topology
open LeanEval.Dynamics.MandelbrotBoundary

noncomputable section

/-! ## Elementary numerical/geometric helpers -/

/-- `‖e^{2πiα} - 1‖ ≤ 4π‖α‖` for `‖α‖ ≤ 1/8`. -/
lemma lam_sub_one_le {α : ℂ} (hα : ‖α‖ ≤ 1 / 8) : ‖lam α - 1‖ ≤ 4 * Real.pi * ‖α‖ := by
  have h2pi : ‖(2 : ℂ) * Real.pi * I‖ = 2 * Real.pi := by
    rw [show (2 : ℂ) * Real.pi * I = (((2 : ℝ) * Real.pi : ℝ) : ℂ) * I by push_cast; ring]
    rw [norm_mul, Complex.norm_I, mul_one]
    have h2 : ‖(((2 : ℝ) * Real.pi : ℝ) : ℂ)‖ ^ 2 = (2 * Real.pi) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp
      ring
    nlinarith [norm_nonneg ((((2 : ℝ) * Real.pi : ℝ)) : ℂ), h2, Real.pi_pos]
  have h1 : ‖2 * Real.pi * I * α‖ ≤ 1 := by
    rw [norm_mul, h2pi]
    nlinarith [hα, norm_nonneg α, Real.pi_lt_four, Real.pi_pos]
  have h3 := Complex.norm_exp_sub_one_le h1
  have h4 : ‖2 * Real.pi * I * α‖ = 2 * Real.pi * ‖α‖ := by
    rw [norm_mul, h2pi]
  have h5 : lam α - 1 = Complex.exp (2 * Real.pi * I * α) - 1 := rfl
  rw [h5]
  calc ‖Complex.exp (2 * Real.pi * I * α) - 1‖ ≤ 2 * ‖2 * Real.pi * I * α‖ := h3
    _ = 2 * (2 * Real.pi * ‖α‖) := by rw [h4]
    _ = 4 * Real.pi * ‖α‖ := by ring

/-- `π(-(1/alphaOf a₁ a₂ β)) = π(1/(a₂+β))`: the integer part `a₁` drops out. -/
lemma piExp_neg_inv_alphaOf (a₁ a₂ : ℕ) (β : ℂ) :
    piExp (-(1 / alphaOf a₁ a₂ β)) = piExp (1 / ((a₂ : ℂ) + β)) := by
  rw [piExp, piExp]
  rw [show 2 * Real.pi * I * -(1 / alphaOf a₁ a₂ β)
      = -(2 * Real.pi * I * (1 / alphaOf a₁ a₂ β)) by ring]
  exact alphaOf_exp_eq a₁ a₂ β

/-- The level-1 rotation number `1/(a₂+β)` lies in Shishikura's class `𝓕₁`. -/
lemma inF1_one_div_add (a₂ : ℕ) (β : ℂ) (b : ℝ) (ha₂ : 2 ≤ a₂) (hβre : 0 ≤ β.re)
    (hβim : |β.im| ≤ b) (hb : b < (a₂ : ℝ)) : InF1 (1 / ((a₂ : ℂ) + β)) := by
  have ha₂R : (2 : ℝ) ≤ (a₂ : ℝ) := by exact_mod_cast ha₂
  set z : ℂ := (a₂ : ℂ) + β with hz
  have hzre : (a₂ : ℝ) ≤ z.re := by
    rw [hz, Complex.add_re]
    simp
    linarith
  have hzim : z.im = β.im := by
    rw [hz, Complex.add_im]
    simp
  have hzpos : 0 < Complex.normSq z := by
    refine Complex.normSq_pos.mpr ?_
    intro h
    have h0 : z.re = 0 := by rw [h]; simp
    linarith
  have hlt : |z.im| < z.re := by
    rw [hzim]
    have h1 : |β.im| < (a₂ : ℝ) := lt_of_le_of_lt hβim hb
    linarith
  unfold InF1
  rw [one_div, Complex.inv_re, Complex.inv_im]
  rw [abs_div, abs_neg, abs_of_pos hzpos, div_lt_div_iff_of_pos_right hzpos]
  exact hlt

/-- Adding a constant preserves `T`-equivariance. -/
lemma isTEquivariantOn_add_const {R : ℂ → ℂ} {DR : Set ℂ} (c : ℂ)
    (h : IsTEquivariantOn R DR) : IsTEquivariantOn (fun w => R w + c) DR :=
  ⟨h.1, fun w hw => by
    change R (w + 1) + c = R w + c + 1
    rw [h.2 w hw]
    ring⟩

/-- `fam α` is differentiable everywhere. -/
lemma differentiable_fam (α : ℂ) : Differentiable ℂ (fam α) := by
  unfold fam
  fun_prop

/-- `max` of five reals: each member is below the nested maximum. -/
lemma max5_le {a b c d e x : ℝ} (h : x = a ∨ x = b ∨ x = c ∨ x = d ∨ x = e) :
    x ≤ max (max (max (max a b) c) d) e := by
  rcases h with rfl | rfl | rfl | rfl | rfl
  · exact le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _))
      (le_max_left _ _)) (le_max_left _ _)
  · exact le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _))
      (le_max_left _ _)) (le_max_left _ _)
  · exact le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)
  · exact le_trans (le_max_right _ _) (le_max_left _ _)
  · exact le_max_right _ _

/-- The six auxiliary bounds used for the scale `η`: each one is below
`max (max a b) (max (max c d) (max e g))`. -/
lemma le_max6_1 {a b c d e g : ℝ} : a ≤ max (max a b) (max (max c d) (max e g)) :=
  le_trans (le_max_left a b) (le_max_left (max a b) (max (max c d) (max e g)))
lemma le_max6_2 {a b c d e g : ℝ} : b ≤ max (max a b) (max (max c d) (max e g)) :=
  le_trans (le_max_right a b) (le_max_left (max a b) (max (max c d) (max e g)))
lemma le_max6_3 {a b c d e g : ℝ} : c ≤ max (max a b) (max (max c d) (max e g)) :=
  le_trans (le_trans (le_max_left c d) (le_max_left (max c d) (max e g)))
    (le_max_right (max a b) (max (max c d) (max e g)))
lemma le_max6_4 {a b c d e g : ℝ} : d ≤ max (max a b) (max (max c d) (max e g)) :=
  le_trans (le_trans (le_max_right c d) (le_max_left (max c d) (max e g)))
    (le_max_right (max a b) (max (max c d) (max e g)))
lemma le_max6_5 {a b c d e g : ℝ} : e ≤ max (max a b) (max (max c d) (max e g)) :=
  le_trans (le_trans (le_max_left e g) (le_max_right (max c d) (max e g)))
    (le_max_right (max a b) (max (max c d) (max e g)))
lemma le_max6_6 {a b c d e g : ℝ} : g ≤ max (max a b) (max (max c d) (max e g)) :=
  le_trans (le_trans (le_max_right e g) (le_max_right (max c d) (max e g)))
    (le_max_right (max a b) (max (max c d) (max e g)))

/-- A complex number with positive real part has argument in `(-2π/3, 2π/3)`. -/
lemma arg_lt_two_pi_div_three_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    |Complex.arg z| < 2 * Real.pi / 3 := by
  have h := Complex.abs_arg_le_pi_div_two_iff.mpr (le_of_lt hz)
  have h2 : Real.pi / 2 < 2 * Real.pi / 3 := by linarith [Real.pi_pos]
  linarith

/-- A bound for `‖·‖` on a compact set. -/
lemma exists_bound_norm_on_compact {L : Set ℂ} (hL : IsCompact L) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z ∈ L, ‖z‖ ≤ M := by
  obtain ⟨M, hM⟩ := hL.exists_bound_of_continuousOn (continuous_norm.continuousOn)
  refine ⟨max M 0, le_max_right _ _, fun z hz => ?_⟩
  have h1 : ‖z‖ ≤ M := by simpa using hM z hz
  exact le_trans h1 (le_max_left _ _)

/-- `d.E = Φ ∘ φ` is holomorphic on `d.DE`. -/
lemma differentiableOn_E {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : ParabData f₀ D₀) :
    DifferentiableOn ℂ d.E d.DE :=
  DifferentiableOn.comp d.Φ_holo (d.φ_holo.mono (fun w hw => hw.1)) (fun w hw => hw.2)

/-- A bound for `‖π (d.E ·)‖` on a compact subset of `d.DE`. -/
lemma exists_bound_piExp_on_compact {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : ParabData f₀ D₀)
    {K : Set ℂ} (hK : IsCompact K) (hKsub : K ⊆ d.DE) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ w ∈ K, ‖piExp (d.E w)‖ ≤ B := by
  have hpi : Continuous piExp := by unfold piExp; fun_prop
  have hcont : ContinuousOn (fun w => piExp (d.E w)) d.DE :=
    hpi.comp_continuousOn (differentiableOn_E d).continuousOn
  obtain ⟨B₀, hB₀⟩ := hK.exists_bound_of_continuousOn (hcont.mono hKsub)
  exact ⟨max B₀ 0, le_max_right _ _, fun w hw => le_trans (hB₀ w hw) (le_max_left _ _)⟩

/-- A bound for `‖pushdown d.E‖` on a compact subset of the domain of the pushed-down horn map. -/
lemma exists_bound_pushdown_on_compact {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : ParabData f₀ D₀)
    (hd : HornData d) {K : Set ℂ} (hK : IsCompact K)
    (hKsub : K ⊆ insert 0 (piExp '' (hd.Bu ∪ hd.Bl))) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ w ∈ K, ‖pushdown d.E w‖ ≤ B := by
  obtain ⟨B₀, hB₀⟩ := hK.exists_bound_of_continuousOn (hd.g_holo.continuousOn.mono hKsub)
  exact ⟨max B₀ 0, le_max_right _ _, fun w hw => le_trans (hB₀ w hw) (le_max_left _ _)⟩

/-- **The bound `B` of Step 1 (level 1).**  If every principal lift of `L/s` either lies in the
horn-map compact `K` or in the ends `{|Im| ≥ y}`, then `‖π (d.E w)‖` is bounded on those lifts
(`w = log (ζ/s)/(2πi)`).  The bound comes from `K` (compactness) and, in the ends, from the
factorisation `π (d.E w) = π w · π (d.E w - w)` with `Work.Repel.end_bound_piExp`. -/
lemma exists_bound_piExp_E {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : ParabData f₀ D₀) {s : ℂ} (hs : s ≠ 0)
    {L K : Set ℂ} (hLc : IsCompact L) (hKc : IsCompact K) (hKsub : K ⊆ d.DE)
    {y : ℝ} (hy : d.η₀ < y)
    (hcover : ∀ ζ ∈ L, ζ ≠ 0 → Complex.log (ζ / s) / (2 * Real.pi * I) ∈ K ∨
      y ≤ |(Complex.log (ζ / s) / (2 * Real.pi * I)).im|) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ ζ ∈ L, ζ ≠ 0 →
      ‖piExp (d.E (Complex.log (ζ / s) / (2 * Real.pi * I)))‖ ≤ B := by
  obtain ⟨B_K, hB_K0, hB_K⟩ := exists_bound_piExp_on_compact d hKc hKsub
  obtain ⟨C, hC0, hC⟩ := end_bound_piExp d hy
  obtain ⟨M, hM0, hM⟩ := exists_bound_norm_on_compact hLc
  refine ⟨max (max B_K (C * M / ‖s‖)) 0, le_max_right _ _, ?_⟩
  intro ζ hζL hζne
  set w : ℂ := Complex.log (ζ / s) / (2 * Real.pi * I) with hw
  have hπw : piExp w = ζ / s := Work.Horn.MandelDim.piExp_log_div (ζ / s) (div_ne_zero hζne hs)
  rcases hcover ζ hζL hζne with hwK | hwy
  · exact le_trans (hB_K w hwK) (le_trans (le_max_left _ _) (le_max_left _ _))
  · have hfac : piExp (d.E w) = piExp w * piExp (d.E w - w) := by
      rw [← piExp_add]
      congr 1
      ring
    rw [hfac, hπw, norm_mul]
    have h1 : ‖ζ / s‖ ≤ M / ‖s‖ := by
      rw [norm_div]; exact div_le_div_of_nonneg_right (hM ζ hζL) (norm_nonneg s)
    have h2 : ‖piExp (d.E w - w)‖ ≤ C := hC w hwy
    calc ‖ζ / s‖ * ‖piExp (d.E w - w)‖ ≤ (M / ‖s‖) * C :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = C * M / ‖s‖ := by ring
      _ ≤ max (max B_K (C * M / ‖s‖)) 0 :=
          le_trans (le_max_right _ _) (le_max_left _ _)


/-! ## The assembly -/

lemma re_inv_two_alphaOf (a₁ a₂ : ℕ) (β : ℂ)
    (h : |((1 : ℂ) / ((a₂ : ℂ) + β)).re| ≤ 1 / 2) :
    ((a₁ : ℝ) - 1 / 2) / 2 ≤ (1 / (2 * alphaOf a₁ a₂ β)).re := by
  have h1α : 1 / alphaOf a₁ a₂ β = (a₁ : ℂ) - 1 / ((a₂ : ℂ) + β) := by
    rw [alphaOf] <;> simp only [one_div, inv_inv] <;> norm_num
  have h2 : 1 / (2 * alphaOf a₁ a₂ β) = (1 / alphaOf a₁ a₂ β) / 2 := by
    rw [div_div]; ring_nf
  have h3 : (((a₁ : ℂ) - 1 / ((a₂ : ℂ) + β)) / 2).re =
      ((a₁ : ℝ) - ((1 : ℂ) / ((a₂ : ℂ) + β)).re) / 2 := by
    rw [Complex.div_ofNat_re, Complex.sub_re, Complex.natCast_re] <;> norm_num
  rw [h2, h1α, h3]
  linarith [(abs_le.mp h).1, (abs_le.mp h).2]

lemma re_inv_two_rotOf (a₂ : ℕ) (β : ℂ) {g : ℂ → ℂ} (hg : rotOf g = 1 / ((a₂ : ℂ) + β))
    (hβre : 0 ≤ β.re) : (a₂ : ℝ) / 2 ≤ (1 / (2 * rotOf g)).re := by
  have hinv : 1 / rotOf g = (a₂ : ℂ) + β := by
    rw [hg] <;> simp only [one_div, inv_inv] <;> norm_num
  have h2 : 1 / (2 * rotOf g) = (1 / rotOf g) / 2 := by rw [div_div]; ring_nf
  have h3 : (((a₂ : ℂ) + β) / 2).re = ((a₂ : ℝ) + β.re) / 2 := by
    rw [Complex.div_ofNat_re, Complex.add_re, Complex.natCast_re] <;> norm_num
  rw [h2, hinv, h3]
  linarith


end

end Work.Repel
