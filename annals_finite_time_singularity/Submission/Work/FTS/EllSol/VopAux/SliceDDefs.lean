/-
Copyright: work module for the Elgindi finite-time singularity project.

# The dominating function and the `L`-expansion of the single-slice `∂_θ²`-estimate
  in the open-trace class

For a slice `u : ℝ → ℝ` that is `C^∞` on the **open** interval `(0, π/2)` (nothing is assumed
outside), the single-slice estimate `sliceF K α u ≤ C_K · sliceF K α u''` (`sliceF` of
`Submission/Work/FTS/EllSol/VopAux/SliceTraceDefs.lean`) is proved by a pointwise induction on
the number of angular derivatives.  The dominating function carried by that induction is the
*pointwise* quantity

`sliceD K α u θ = (u θ)²·thEta θ + (u' θ)²·thEta θ + (u'' θ)²·thEta θ
                   + ∑_{1 ≤ m ≤ K} (L^m u'' θ)²·thGam α θ`,   `L = D_θ = sin(2θ)∂_θ`,

i.e. the datum terms of the estimate together with the zeroth- and first-order terms of `u`
against the weight `sin(2θ)^{-η}` (which is *weaker* than `sin(2θ)^{-γ}` on `Iθ`, since
`γ = 1 + α/10 > η = 99/100`).

This module contains

* the definition `sliceD` and its elementary monotonicity lemmas;
* the weight comparisons `sin(2θ)^{2-γ} ≤ thEta`, `sin(2θ)^{4-γ} ≤ thEta`,
  `sin(2θ)^{4-γ} ≤ thGam` on `Iθ`;
* the O(1) bounds `|L^a (sin²2·) θ| ≤ D·sin²(2θ)` and `|L^a (2 cos 2·) θ| ≤ E` for `a ≤ K`;
* the **expansion** of `L^{n+2} u` on the open interval in the two Leibniz sums
  (`sd_LopIter_expand_open`), which is the algebraic core of the induction.

The pointwise induction itself is in the sibling `SliceDPointwise`; the integration against `Iθ`
and the assembly of the estimate is in `sliceF_le_sliceV`.
-/
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.FTS.EllSol.VopAux.SliceTraceDefs
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs
import Submission.Work.FTS.EllipticEst.Lop_iter_sin_sq_bound
import Submission.Work.FTS.EllipticEst.Lop_iter_cos_eq
import Submission.Work.FTS.LocData.DthIter_mul_smoothQuad
import Submission.Work.FTS.EllipticEst.Lop_sin_mul

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.VopAux

open Work.FTS.EllipticEst

set_option autoImplicit false

/-! ## The dominating function `sliceD` -/

/-- The pointwise dominating function of the single-slice `∂_θ²`-estimate in the open-trace
class: the zeroth-, first- and second-order terms of the slice against the weight
`sin(2θ)^{-η}`, plus the higher angular derivatives of the datum `u''` against
`sin(2θ)^{-γ}`. -/
def sliceD (K : ℕ) (α : ℝ) (u : ℝ → ℝ) (θ : ℝ) : ℝ :=
  (u θ) ^ 2 * thEta θ
    + (deriv u θ) ^ 2 * thEta θ
    + (sliceV u θ) ^ 2 * thEta θ
    + ∑ m ∈ Finset.Icc 1 K, (LopIter m (sliceV u) θ) ^ 2 * thGam α θ

theorem sliceD_nonneg (K : ℕ) (α : ℝ) (u : ℝ → ℝ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ sliceD K α u θ := by
  have h1 : 0 ≤ (u θ) ^ 2 * thEta θ := mul_nonneg (sq_nonneg _) (thEta_nonneg hθ)
  have h2 : 0 ≤ (deriv u θ) ^ 2 * thEta θ := mul_nonneg (sq_nonneg _) (thEta_nonneg hθ)
  have h3 : 0 ≤ (sliceV u θ) ^ 2 * thEta θ := mul_nonneg (sq_nonneg _) (thEta_nonneg hθ)
  have h4 : 0 ≤ ∑ m ∈ Finset.Icc 1 K, (LopIter m (sliceV u) θ) ^ 2 * thGam α θ :=
    Finset.sum_nonneg fun m _ => mul_nonneg (sq_nonneg _) (thGam_nonneg hθ)
  rw [sliceD]
  linarith

/-- The zeroth-order term of `sliceD`. -/
theorem sd_self_sq_le_sliceD (K : ℕ) (α : ℝ) (u : ℝ → ℝ) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    (u θ) ^ 2 * thEta θ ≤ sliceD K α u θ := by
  have h1 : 0 ≤ (deriv u θ) ^ 2 * thEta θ := mul_nonneg (sq_nonneg _) (thEta_nonneg hθ)
  have h2 : 0 ≤ (sliceV u θ) ^ 2 * thEta θ := mul_nonneg (sq_nonneg _) (thEta_nonneg hθ)
  have h3 : 0 ≤ ∑ m ∈ Finset.Icc 1 K, (LopIter m (sliceV u) θ) ^ 2 * thGam α θ :=
    Finset.sum_nonneg fun m _ => mul_nonneg (sq_nonneg _) (thGam_nonneg hθ)
  rw [sliceD]
  linarith

/-- The first-order term of `sliceD`. -/
theorem sd_deriv_sq_le_sliceD (K : ℕ) (α : ℝ) (u : ℝ → ℝ) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    (deriv u θ) ^ 2 * thEta θ ≤ sliceD K α u θ := by
  have h1 : 0 ≤ (u θ) ^ 2 * thEta θ := mul_nonneg (sq_nonneg _) (thEta_nonneg hθ)
  have h2 : 0 ≤ (sliceV u θ) ^ 2 * thEta θ := mul_nonneg (sq_nonneg _) (thEta_nonneg hθ)
  have h3 : 0 ≤ ∑ m ∈ Finset.Icc 1 K, (LopIter m (sliceV u) θ) ^ 2 * thGam α θ :=
    Finset.sum_nonneg fun m _ => mul_nonneg (sq_nonneg _) (thGam_nonneg hθ)
  rw [sliceD]
  linarith

/-- The datum term `(u'')²thEta` of `sliceD`. -/
theorem sd_sliceV_sq_le_sliceD (K : ℕ) (α : ℝ) (u : ℝ → ℝ) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    (sliceV u θ) ^ 2 * thEta θ ≤ sliceD K α u θ := by
  have h1 : 0 ≤ (u θ) ^ 2 * thEta θ := mul_nonneg (sq_nonneg _) (thEta_nonneg hθ)
  have h2 : 0 ≤ (deriv u θ) ^ 2 * thEta θ := mul_nonneg (sq_nonneg _) (thEta_nonneg hθ)
  have h3 : 0 ≤ ∑ m ∈ Finset.Icc 1 K, (LopIter m (sliceV u) θ) ^ 2 * thGam α θ :=
    Finset.sum_nonneg fun m _ => mul_nonneg (sq_nonneg _) (thGam_nonneg hθ)
  rw [sliceD]
  linarith

/-- The higher `θ`-derivatives of the datum occurring in `sliceD`. -/
theorem sd_LopIter_sliceV_sq_le_sliceD (K : ℕ) (α : ℝ) (u : ℝ → ℝ) {m : ℕ}
    (hm : m ∈ Finset.Icc 1 K) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (LopIter m (sliceV u) θ) ^ 2 * thGam α θ ≤ sliceD K α u θ := by
  have h1 : 0 ≤ (u θ) ^ 2 * thEta θ := mul_nonneg (sq_nonneg _) (thEta_nonneg hθ)
  have h2 : 0 ≤ (deriv u θ) ^ 2 * thEta θ := mul_nonneg (sq_nonneg _) (thEta_nonneg hθ)
  have h3 : 0 ≤ (sliceV u θ) ^ 2 * thEta θ := mul_nonneg (sq_nonneg _) (thEta_nonneg hθ)
  have h4 : (LopIter m (sliceV u) θ) ^ 2 * thGam α θ
      ≤ ∑ m' ∈ Finset.Icc 1 K, (LopIter m' (sliceV u) θ) ^ 2 * thGam α θ :=
    Finset.single_le_sum (f := fun m' => (LopIter m' (sliceV u) θ) ^ 2 * thGam α θ)
      (fun m' _ => mul_nonneg (sq_nonneg _) (thGam_nonneg hθ)) hm
  rw [sliceD]
  linarith

/-! ## The weight comparisons on `Iθ` -/

theorem sd_sin_sq_le_one {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (Real.sin (2 * θ)) ^ 2 ≤ 1 := by
  have h0 := Work.FTS.EllipticEst.sin_two_nonneg hθ
  have h1 := Work.FTS.EllipticEst.sin_two_le_one θ
  nlinarith

/-- Multiplication of two powers of a non-negative base (the junk value `0 ^ 0` is avoided by
the hypotheses on the exponents). -/
theorem sd_rpow_mul_self {x a b : ℝ} (hx : 0 ≤ x) (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a + b ≠ 0) : x ^ a * x ^ b = x ^ (a + b) := by
  rcases eq_or_lt_of_le hx with h | h
  · subst h
    rw [Real.zero_rpow ha, Real.zero_rpow hb, Real.zero_rpow hab]
    ring
  · rw [Real.rpow_add h a b]

/-- `x^m · x^{-p} = x^{m-p}` for `x ≥ 0` and the relevant exponents non-zero. -/
theorem sd_pow_mul_rpow {x : ℝ} (hx : 0 ≤ x) {m : ℕ} (hm : m ≠ 0) {p : ℝ}
    (hp : p ≠ 0) (hmp : (m : ℝ) ≠ p) :
    x ^ m * x ^ (-p) = x ^ ((m : ℝ) - p) := by
  rw [← Real.rpow_natCast x m]
  have h := sd_rpow_mul_self (x := x) (a := (m : ℝ)) (b := -p) hx
    (Nat.cast_ne_zero.mpr hm) (neg_ne_zero.mpr hp) (by
      intro hc
      exact hmp (by linarith))
  simpa only [sub_eq_add_neg] using h

theorem sd_gam_ne {α : ℝ} (hα0 : 0 < α) : Work.Spaces.gam α ≠ 0 := by
  rw [Work.Spaces.gam]; intro h; linarith

theorem sd_two_sub_gam_ne {α : ℝ} (hα1 : α ≤ 1) : (2 : ℝ) - Work.Spaces.gam α ≠ 0 := by
  rw [Work.Spaces.gam]; intro h; linarith

theorem sd_four_sub_gam_ne {α : ℝ} (hα1 : α ≤ 1) : (4 : ℝ) - Work.Spaces.gam α ≠ 0 := by
  rw [Work.Spaces.gam]; intro h; linarith

/-- `sin(2θ)^{4-γ} ≤ thEta` on `Iθ` for `α ≤ 1`. -/
theorem sd_four_sub_gam_le_thEta {α : ℝ} (hα1 : α ≤ 1) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    (Real.sin (2 * θ)) ^ (4 - Work.Spaces.gam α) ≤ thEta θ := by
  have h4 : 0 < 4 - Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith
  have hle : -(Work.Spaces.eta) ≤ 4 - Work.Spaces.gam α := by
    rw [Work.Spaces.gam, Work.Spaces.eta]; linarith
  exact Work.FTS.EllipticEst.sin_two_rpow_le_rpow h4 hle hθ

/-- `sin(2θ)^{2-γ} ≤ thEta` on `Iθ` for `α ≤ 1`. -/
theorem sd_two_sub_gam_le_thEta {α : ℝ} (hα1 : α ≤ 1) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) ≤ thEta θ := by
  have h2 : 0 < 2 - Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith
  have hle : -(Work.Spaces.eta) ≤ 2 - Work.Spaces.gam α := by
    rw [Work.Spaces.gam, Work.Spaces.eta]; linarith
  exact Work.FTS.EllipticEst.sin_two_rpow_le_rpow h2 hle hθ

/-- `sin(2θ)^{4-γ} ≤ thGam α` on `Iθ` for `α ≤ 1`. -/
theorem sd_four_sub_gam_le_thGam {α : ℝ} (hα1 : α ≤ 1) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    (Real.sin (2 * θ)) ^ (4 - Work.Spaces.gam α) ≤ thGam α θ := by
  have h4 : 0 < 4 - Work.Spaces.gam α := by
    rw [Work.Spaces.gam]; linarith
  have hle : -(Work.Spaces.gam α) ≤ 4 - Work.Spaces.gam α := by linarith
  exact Work.FTS.EllipticEst.sin_two_rpow_le_rpow h4 hle hθ

/-- `sin(2θ)^2 · thGam α θ = sin(2θ)^{2-γ}` on `Iθ` for `0 < α ≤ 1`. -/
theorem sd_sin_sq_mul_thGam {α : ℝ} {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) (hα0 : 0 < α)
    (hα1 : α ≤ 1) :
    (Real.sin (2 * θ)) ^ 2 * thGam α θ = (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) := by
  rw [thGam]
  exact sd_pow_mul_rpow (Work.FTS.EllipticEst.sin_two_nonneg hθ) (by norm_num)
    (sd_gam_ne hα0) (by intro hc; exact sd_two_sub_gam_ne hα1 (sub_eq_zero.mpr hc))

/-! ## The O(1) bounds on `L^a (sin²2·)` and `L^a (2 cos 2·)` -/

/-- A uniform bound `D ≥ 1` for the iterates of `sin²(2·)`, `a ≤ K`. -/
theorem sd_LopIter_sin_sq_bound (K : ℕ) : ∃ D : ℝ, 1 ≤ D ∧ ∀ a ≤ K, ∀ θ ∈ Work.Spaces.Iθ,
    |LopIter a (fun θ : ℝ => (Real.sin (2 * θ)) ^ 2) θ|
      ≤ D * (Real.sin (2 * θ)) ^ 2 := by
  obtain ⟨C, hCpos, hC⟩ := Work.FTS.EllipticEst.Lop_iter_sin_sq_bound K
  refine ⟨max C 1, le_max_right _ _, ?_⟩
  intro a ha θ hθ
  have hs : 0 ≤ (Real.sin (2 * θ)) ^ 2 := sq_nonneg _
  calc |LopIter a (fun θ : ℝ => (Real.sin (2 * θ)) ^ 2) θ|
      ≤ C * (Real.sin (2 * θ)) ^ 2 := hC a ha θ hθ
    _ ≤ max C 1 * (Real.sin (2 * θ)) ^ 2 :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hs

/-- A uniform bound for the iterates of `2 cos(2·)`, `a ≤ K`. -/
theorem sd_LopIter_cos_bound (K : ℕ) : ∃ E : ℝ, 0 < E ∧ ∀ a ≤ K, ∀ θ ∈ Work.Spaces.Iθ,
    |LopIter a (fun θ : ℝ => 2 * Real.cos (2 * θ)) θ| ≤ E := by
  obtain ⟨D, hD1, hDss⟩ := sd_LopIter_sin_sq_bound K
  refine ⟨4 * D, by positivity, ?_⟩
  intro a ha θ hθ
  have hD0 : 0 ≤ D := le_trans zero_le_one hD1
  rcases Nat.eq_zero_or_pos a with h0 | hpos
  · subst h0
    simp only [LopIter_zero]
    have hc : |Real.cos (2 * θ)| ≤ 1 := Real.abs_cos_le_one (2 * θ)
    have h2 : |2 * Real.cos (2 * θ)| ≤ 2 := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith
    linarith [hD1]
  · obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
    rw [Work.FTS.EllipticEst.Lop_iter_cos_eq _ (by omega)]
    simp only [Nat.add_sub_cancel]
    rw [abs_mul, show |(-4 : ℝ)| = 4 by norm_num]
    have hb := hDss b (by omega) θ hθ
    have hs1 := sd_sin_sq_le_one hθ
    have hs : 0 ≤ (Real.sin (2 * θ)) ^ 2 := sq_nonneg _
    calc 4 * |LopIter b (fun θ : ℝ => (Real.sin (2 * θ)) ^ 2) θ|
        ≤ 4 * (D * (Real.sin (2 * θ)) ^ 2) := by linarith [hb]
      _ ≤ 4 * (D * 1) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          exact mul_le_mul_of_nonneg_left hs1 hD0
      _ = 4 * D := by ring

/-! ## The local machinery on the open interval `(0, π/2)` -/

/-- The open angular interval carrying the merely open-smooth slices. -/
abbrev sdU : Set ℝ := Set.Ioo (0 : ℝ) (Real.pi / 2)

theorem sd_isOpen_sdU : IsOpen sdU := isOpen_Ioo

theorem sd_smoothOrder_add_one_le :
    Work.Stability.smoothOrder + 1 ≤ Work.Stability.smoothOrder :=
  le_of_eq Work.FTS.LocData.smoothOrder_add_one

theorem sd_one_le_smoothOrder : (1 : WithTop ℕ∞) ≤ Work.Stability.smoothOrder := by
  simp [Work.Stability.smoothOrder]

/-- The raw `∀ n, ContDiffOn ℝ n` hypothesis on an open set upgrades to the genuine `C^∞`
order `smoothOrder`. -/
theorem sd_contDiffOn_smoothOrder {u : ℝ → ℝ}
    (hu : ∀ n : ℕ, ContDiffOn ℝ n u sdU) : ContDiffOn ℝ Work.Stability.smoothOrder u sdU :=
  contDiffOn_infty.mpr hu

/-- `deriv` preserves `C^∞`-on-an-open-set. -/
theorem sd_contDiffOn_deriv {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ Work.Stability.smoothOrder u sdU) :
    ContDiffOn ℝ Work.Stability.smoothOrder (deriv u) sdU :=
  hu.deriv_of_isOpen sd_isOpen_sdU sd_smoothOrder_add_one_le

/-- The iterates of `L = sin(2θ) ∂_θ` preserve `C^∞`-on-`sdU`. -/
theorem sd_LopIter_contDiffOn {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ Work.Stability.smoothOrder u sdU) (n : ℕ) :
    ContDiffOn ℝ Work.Stability.smoothOrder (LopIter n u) sdU := by
  induction n with
  | zero => simpa only [LopIter_zero] using hu
  | succ n ih =>
      have hsin : ContDiffOn ℝ Work.Stability.smoothOrder
          (fun θ : ℝ => Real.sin (2 * θ)) sdU := by fun_prop
      rw [LopIter_succ]
      have heq : Work.Spaces.Lop (LopIter n u)
          = (fun θ : ℝ => Real.sin (2 * θ)) * deriv (LopIter n u) := rfl
      rw [heq]
      exact hsin.mul (sd_contDiffOn_deriv ih)

/-- Additivity of the iterates of `L` on `sdU`, in the genuine `C^∞` order. -/
theorem sd_LopIter_add_eqOn {f g : ℝ → ℝ}
    (hf : ContDiffOn ℝ Work.Stability.smoothOrder f sdU)
    (hg : ContDiffOn ℝ Work.Stability.smoothOrder g sdU) (n : ℕ) :
    Set.EqOn (LopIter n (fun θ => f θ + g θ))
      (fun θ => LopIter n f θ + LopIter n g θ) sdU := by
  induction n with
  | zero => intro θ _; rfl
  | succ n ih =>
      intro θ hθ
      have hmem : sdU ∈ 𝓝 θ := sd_isOpen_sdU.mem_nhds hθ
      have hdf : DifferentiableAt ℝ (LopIter n f) θ :=
        (((sd_LopIter_contDiffOn hf n).of_le sd_one_le_smoothOrder).contDiffAt hmem)
            |>.differentiableAt_one
      have hdg : DifferentiableAt ℝ (LopIter n g) θ :=
        (((sd_LopIter_contDiffOn hg n).of_le sd_one_le_smoothOrder).contDiffAt hmem)
            |>.differentiableAt_one
      have heq : LopIter n (fun θ => f θ + g θ) =ᶠ[𝓝 θ]
          (fun θ => LopIter n f θ + LopIter n g θ) := ih.eventuallyEq_of_mem hmem
      have hder : deriv (fun θ => LopIter n f θ + LopIter n g θ) θ
          = deriv (LopIter n f) θ + deriv (LopIter n g) θ :=
        deriv_add hdf hdg
      rw [LopIter_succ, LopIter_succ, LopIter_succ]
      simp only [Work.Spaces.Lop]
      rw [heq.deriv_eq, hder]
      ring

/-- Pointwise form of `sd_LopIter_add_eqOn`. -/
theorem sd_LopIter_add {f g : ℝ → ℝ}
    (hf : ContDiffOn ℝ Work.Stability.smoothOrder f sdU)
    (hg : ContDiffOn ℝ Work.Stability.smoothOrder g sdU) (n : ℕ) {θ : ℝ} (hθ : θ ∈ sdU) :
    LopIter n (fun θ => f θ + g θ) θ = LopIter n f θ + LopIter n g θ :=
  sd_LopIter_add_eqOn hf hg n hθ

/-- The iterated Leibniz rule for `LopIter` on `sdU` (genuine smooth order). -/
theorem sd_LopIter_mul_eqOn {f g : ℝ → ℝ}
    (hf : ContDiffOn ℝ Work.Stability.smoothOrder f sdU)
    (hg : ContDiffOn ℝ Work.Stability.smoothOrder g sdU) (j : ℕ) :
    Set.EqOn (LopIter j (f * g))
      (fun θ => ∑ a ∈ Finset.range (j + 1),
        (j.choose a : ℝ) * (LopIter a f θ * LopIter (j - a) g θ)) sdU := by
  intro θ hθ
  have h := Work.FTS.LocData.Lop_iter_mul_eqOn_smooth f g sdU sd_isOpen_sdU hf hg j hθ
  simpa only [LopIter] using h

/-- `deriv (fun t => sin (2t)) θ = 2 cos (2θ)`. -/
theorem sd_deriv_sin_two (θ : ℝ) :
    deriv (fun t : ℝ => Real.sin (2 * t)) θ = 2 * Real.cos (2 * θ) := by
  have h := (Real.hasDerivAt_sin (2 * θ)).comp θ ((hasDerivAt_id θ).const_mul (2 : ℝ))
  simpa [Function.comp_def, mul_comm] using h.deriv

/-- The second iterate of `L` on a `C^∞` slice: `L²u = sin(2θ)²·u'' + 2 cos(2θ)·(L u)`. -/
theorem sd_LopIter_two_eqOn {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ Work.Stability.smoothOrder u sdU) :
    Set.EqOn (LopIter 2 u)
      (fun θ => (Real.sin (2 * θ)) ^ 2 * sliceV u θ
        + 2 * Real.cos (2 * θ) * LopIter 1 u θ) sdU := by
  intro θ hθ
  have hdu : ContDiffOn ℝ Work.Stability.smoothOrder (deriv u) sdU := sd_contDiffOn_deriv hu
  have hsin : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun θ : ℝ => Real.sin (2 * θ)) sdU := by fun_prop
  have hF : LopIter 2 u θ
      = LopIter 1 ((fun θ : ℝ => Real.sin (2 * θ)) * deriv u) θ := by
    rw [LopIter_succ, LopIter_succ, LopIter_zero]
    rfl
  rw [hF, sd_LopIter_mul_eqOn hsin hdu 1 hθ]
  have hd : deriv (fun s : ℝ => Real.sin (2 * s)) θ = 2 * Real.cos (2 * θ) :=
    sd_deriv_sin_two θ
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.choose_zero_right, Nat.choose_self, Nat.cast_one, one_mul, tsub_zero, tsub_self,
    LopIter, Function.iterate_one, Function.iterate_zero_apply, Work.Spaces.Lop, sliceV, hd]
  ring

/-! ## Locality of the iterates of `L` -/

theorem sd_eventuallyEq_nhds_mono {u v : ℝ → ℝ} {θ : ℝ} (h : u =ᶠ[𝓝 θ] v) :
    ∀ᶠ θ' in 𝓝 θ, u =ᶠ[𝓝 θ'] v := by
  obtain ⟨t, hts, htopen, hθt⟩ := mem_nhds_iff.mp h
  filter_upwards [htopen.mem_nhds hθt] with θ' hθ'
  exact eventually_of_mem (htopen.mem_nhds hθ') hts

theorem sd_Lop_eventuallyEq {u v : ℝ → ℝ} {θ : ℝ} (h : u =ᶠ[𝓝 θ] v) :
    ∀ᶠ θ' in 𝓝 θ, Work.Spaces.Lop u θ' = Work.Spaces.Lop v θ' := by
  filter_upwards [sd_eventuallyEq_nhds_mono h] with θ' hθ'
  simp only [Work.Spaces.Lop]
  rw [hθ'.deriv_eq]

theorem sd_LopIter_eventuallyEq {u v : ℝ → ℝ} {θ : ℝ} (h : u =ᶠ[𝓝 θ] v) (m : ℕ) :
    ∀ᶠ θ' in 𝓝 θ, LopIter m u θ' = LopIter m v θ' := by
  induction m with
  | zero =>
      filter_upwards [h] with θ' hθ'
      simpa only [LopIter_zero] using hθ'
  | succ m ih =>
      have h' : LopIter m u =ᶠ[𝓝 θ] LopIter m v := ih
      simpa only [LopIter_succ] using sd_Lop_eventuallyEq h'

theorem sd_LopIter_congr_nhds {u v : ℝ → ℝ} {θ : ℝ} (h : u =ᶠ[𝓝 θ] v) (m : ℕ) :
    LopIter m u θ = LopIter m v θ :=
  (sd_LopIter_eventuallyEq h m).self_of_nhds

/-! ## The expansion of `L^{n+2} u` on the open interval -/

/-- **The expansion of `L^{n+2}u` on the open interval.**  If `u` is `C^∞` on `(0, π/2)` then at
every `θ ∈ (0, π/2)`

`L^{n+2} u θ = ∑_{a ≤ n} C(n,a)·L^a(sin²(2·)) θ · L^{n-a}(u'') θ
             + ∑_{a ≤ n} C(n,a)·L^a(2 cos(2·)) θ · L^{n+1-a}(u) θ`,

obtained by writing `L²u = sin²(2·)·u'' + 2cos(2·)·(Lu)` (a germ identity) and applying the
iterated Leibniz rule to the two products. -/
theorem sd_LopIter_expand_open (n : ℕ) (u : ℝ → ℝ)
    (hu : ∀ k : ℕ, ContDiffOn ℝ k u sdU) {θ : ℝ} (hθ : θ ∈ sdU) :
    LopIter (n + 2) u θ
      = (∑ a ∈ Finset.range (n + 1), (n.choose a : ℝ)
            * LopIter a (fun θ : ℝ => (Real.sin (2 * θ)) ^ 2) θ
            * LopIter (n - a) (sliceV u) θ)
        + (∑ a ∈ Finset.range (n + 1), (n.choose a : ℝ)
            * LopIter a (fun θ : ℝ => 2 * Real.cos (2 * θ)) θ
            * LopIter (n + 1 - a) u θ) := by
  have huso : ContDiffOn ℝ Work.Stability.smoothOrder u sdU := sd_contDiffOn_smoothOrder hu
  -- the germ identity `L² u = sin(2·)² u'' + 2 cos(2·) (L u)`
  have h2 : LopIter 2 u =ᶠ[𝓝 θ]
      (fun θ' : ℝ => (Real.sin (2 * θ')) ^ 2 * sliceV u θ'
        + 2 * Real.cos (2 * θ') * LopIter 1 u θ') :=
    (sd_LopIter_two_eqOn huso).eventuallyEq_of_mem (sd_isOpen_sdU.mem_nhds hθ)
  have hiter : LopIter (n + 2) u θ = LopIter n (LopIter 2 u) θ := by
    simp only [LopIter, Function.iterate_add_apply]
  rw [hiter, sd_LopIter_congr_nhds h2 n]
  -- smoothness of the two summands of the split
  have hddu : ContDiffOn ℝ Work.Stability.smoothOrder (sliceV u) sdU := by
    have h := sd_contDiffOn_deriv (sd_contDiffOn_deriv huso)
    simpa only [sliceV] using h
  have hss : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun θ' : ℝ => (Real.sin (2 * θ')) ^ 2) sdU := by
    have h1 : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun θ' : ℝ => Real.sin (2 * θ')) sdU := by fun_prop
    simpa using h1.pow 2
  have hcc : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun θ' : ℝ => 2 * Real.cos (2 * θ')) sdU := by fun_prop
  have hLu : ContDiffOn ℝ Work.Stability.smoothOrder (LopIter 1 u) sdU :=
    sd_LopIter_contDiffOn huso 1
  have hf1 : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun θ' : ℝ => (Real.sin (2 * θ')) ^ 2 * sliceV u θ') sdU := hss.mul hddu
  have hf2 : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun θ' : ℝ => 2 * Real.cos (2 * θ') * LopIter 1 u θ') sdU := hcc.mul hLu
  rw [sd_LopIter_add hf1 hf2 n hθ]
  -- Leibniz for each of the two products
  have hprod1 : (fun θ' : ℝ => (Real.sin (2 * θ')) ^ 2 * sliceV u θ')
      = (fun θ' : ℝ => (Real.sin (2 * θ')) ^ 2) * sliceV u := rfl
  have hprod2 : (fun θ' : ℝ => 2 * Real.cos (2 * θ') * LopIter 1 u θ')
      = (fun θ' : ℝ => 2 * Real.cos (2 * θ')) * LopIter 1 u := rfl
  have hmul1 := sd_LopIter_mul_eqOn hss hddu n hθ
  have hmul2 := sd_LopIter_mul_eqOn hcc hLu n hθ
  rw [hprod1, hprod2, hmul1, hmul2]
  congr 1
  · refine Finset.sum_congr rfl (fun a _ => ?_)
    ring
  · refine Finset.sum_congr rfl (fun a ha => ?_)
    have ha' : a ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
    have hidx : LopIter (n - a) (LopIter 1 u) = LopIter (n + 1 - a) u := by
      have h1 : LopIter (n - a) (LopIter 1 u) = LopIter (n - a) (Work.Spaces.Lop u) := by
        simp only [LopIter, Function.iterate_one]
      rw [h1, ← LopIter_succ_apply]
      congr 1
      omega
    rw [hidx]
    ring

/-! ## Auxiliary arithmetic for the induction -/

/-- Cauchy–Schwarz for a finite sum: `(Σ f)² w ≤ card · Σ f² w` for `w ≥ 0`. -/
theorem sd_sum_sq_mul_le {ι : Type*} (s : Finset ι) (F : ι → ℝ) {w : ℝ} (hw : 0 ≤ w) :
    (∑ a ∈ s, F a) ^ 2 * w ≤ (s.card : ℝ) * ∑ a ∈ s, (F a) ^ 2 * w := by
  have h1 := sq_sum_le_card_mul_sum_sq (s := s) (f := F)
  have h2 : (∑ a ∈ s, F a) ^ 2 * w ≤ ((s.card : ℝ) * ∑ a ∈ s, (F a) ^ 2) * w :=
    mul_le_mul_of_nonneg_right h1 hw
  have h3 : ((s.card : ℝ) * ∑ a ∈ s, (F a) ^ 2) * w
      = (s.card : ℝ) * ∑ a ∈ s, (F a) ^ 2 * w := by
    rw [mul_assoc, Finset.sum_mul]
  linarith [h2, le_of_eq h3]

/-- `∑_{a ≤ n} C(n,a)² ≤ (n+1)·4^n`. -/
theorem sd_choose_sq_sum_le (n : ℕ) :
    (∑ a ∈ Finset.range (n + 1), ((n.choose a : ℝ)) ^ 2) ≤ ((n : ℝ) + 1) * (4 : ℝ) ^ n := by
  have h4 : ((2 : ℝ) ^ n) ^ 2 = (4 : ℝ) ^ n := by
    rw [pow_two, ← mul_pow, show (2 : ℝ) * 2 = 4 by norm_num]
  calc (∑ a ∈ Finset.range (n + 1), ((n.choose a : ℝ)) ^ 2)
      ≤ ∑ _a ∈ Finset.range (n + 1), ((2 : ℝ) ^ n) ^ 2 := by
        refine Finset.sum_le_sum (fun a _ => ?_)
        have h1 : ((n.choose a : ℕ) : ℝ) ≤ (2 : ℝ) ^ n := by
          have := Nat.choose_le_two_pow n a
          exact_mod_cast this
        have h2 : 0 ≤ ((n.choose a : ℕ) : ℝ) := Nat.cast_nonneg _
        have h3 : 0 ≤ (2 : ℝ) ^ n := by positivity
        calc ((n.choose a : ℝ)) ^ 2 = (((n.choose a : ℕ) : ℝ)) ^ 2 := rfl
          _ ≤ ((2 : ℝ) ^ n) ^ 2 := pow_le_pow_left₀ h2 h1 2
    _ = ((n : ℝ) + 1) * ((2 : ℝ) ^ n) ^ 2 := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring
    _ = ((n : ℝ) + 1) * (4 : ℝ) ^ n := by rw [h4]

end Work.FTS.EllSol.VopAux
