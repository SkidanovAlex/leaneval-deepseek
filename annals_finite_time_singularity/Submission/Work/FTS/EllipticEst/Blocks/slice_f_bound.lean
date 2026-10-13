import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs
import Submission.Work.FTS.EllipticEst.SliceAux
import Submission.Work.FTS.EllipticEst.Lop_iter_mul
import Submission.Work.FTS.EllipticEst.Lop_iter_cos_eq
import Submission.Work.FTS.EllipticEst.LopIterSinSqDefs
import Submission.Work.FTS.EllipticEst.GfunContDiff
import Submission.Work.FTS.EllipticEst.Lop_sin_mul
import Submission.Work.FTS.EllipticEst.slice_deriv_sq_le
import Submission.Work.FTS.EllipticEst.Blocks.slice_self_sq_le
import Submission.Work.FTS.EllipticEst.Blocks.sf_LopIter_two
import Submission.Work.FTS.EllipticEst.Blocks.sf_LopIter_add

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Blocks

set_option autoImplicit false

/-! ## Auxiliary lemmas for `slice_f_bound`

Write `s = sin(2θ)`, `L = D_θ = sin(2θ) ∂_θ`, `v = sliceV u = u''`, `γ = gam α`, `η = eta`,
`P = slicePhi α K u θ` and `B` for the explicit constant built in the proof (depending only on
`K`).  The plan is:

* `L²u = s²·v + 2cos(2θ)·(L u)`, and for `i ≥ 2` two applications of the iterated Leibniz rule
  expand `L^i u` into the two sums of `sfF1`, `sfF2`.
* Since `|L^a(s²) θ| ≤ D·s²` (`sfb_Lop_sin_sq_bound`) and `|L^a(2cos 2θ) θ| ≤ 4D`
  (`sfb_cos_iter_bound`), each `v`-term is bounded by a fixed multiple of `P` (using `s^4 ≤ 1`
  and `s^{4-γ} ≤ sin(2θ)^{-η} = thEta`) and each `u`-term by `16 D² B^{i-1} P` (strong
  induction on `i`; the indices occurring in the `u`-terms are `1 ≤ j ≤ i-1`).
* `sq_sum_le_card_mul_sum_sq` and the binomial bound `Σ_a C(n,a)² ≤ (n+1)4^n`
  (`sfb_choose_sq_sum_le`) turn this into `(L^i u θ)² sin(2θ)^{-γ} ≤ 34(i-1)²D²4^{i-2}B^{i-1}P
  ≤ B^i·P`.
* The `u`-term `(u θ)² sin(2θ)^{-η}` is `Blocks.slice_self_sq_le` combined with
  `∫_{Iθ} sin(2θ)^η ≤ π/2`. -/

/-- Multiplication of two powers of the same non-negative base (the junk value `0^0` is avoided
by the hypotheses on the exponents). -/
private lemma sfb_rpow_mul_self {x a b : ℝ} (hx : 0 ≤ x) (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a + b ≠ 0) : x ^ a * x ^ b = x ^ (a + b) := by
  rcases eq_or_lt_of_le hx with h | h
  · subst h
    rw [Real.zero_rpow ha, Real.zero_rpow hb, Real.zero_rpow hab]
    ring
  · rw [Real.rpow_add h a b]

/-- `x^m · x^{-p} = x^{m-p}` for `x ≥ 0` and the relevant exponents non-zero. -/
private lemma sfb_pow_mul_rpow {x : ℝ} (hx : 0 ≤ x) {m : ℕ} (hm : m ≠ 0) {p : ℝ}
    (hp : p ≠ 0) (hmp : (m : ℝ) ≠ p) :
    x ^ m * x ^ (-p) = x ^ ((m : ℝ) - p) := by
  rw [← Real.rpow_natCast x m]
  have h := sfb_rpow_mul_self (x := x) (a := (m : ℝ)) (b := -p) hx
    (Nat.cast_ne_zero.mpr hm) (neg_ne_zero.mpr hp) (by
      intro hc
      exact hmp (by linarith))
  simpa only [sub_eq_add_neg] using h

/-- `gam α ≠ 0` for `α > 0`. -/
private lemma sfb_gam_ne {α : ℝ} (hα0 : 0 < α) : Work.Spaces.gam α ≠ 0 := by
  rw [Work.Spaces.gam]; intro h; linarith

/-- `2 - gam α ≠ 0` for `α ≤ 1`. -/
private lemma sfb_two_sub_gam_ne {α : ℝ} (hα1 : α ≤ 1) : (2 : ℝ) - Work.Spaces.gam α ≠ 0 := by
  rw [Work.Spaces.gam]; intro h; linarith

/-- `4 - gam α ≠ 0` for `α ≤ 1`. -/
private lemma sfb_four_sub_gam_ne {α : ℝ} (hα1 : α ≤ 1) : (4 : ℝ) - Work.Spaces.gam α ≠ 0 := by
  rw [Work.Spaces.gam]; intro h; linarith

/-- `deriv (fun t => sin (2t)) θ = 2 cos (2θ)`. -/
private lemma sfb_deriv_sin_two (θ : ℝ) :
    deriv (fun t : ℝ => Real.sin (2 * t)) θ = 2 * Real.cos (2 * θ) := by
  have h := (Real.hasDerivAt_sin (2 * θ)).comp θ ((hasDerivAt_id θ).const_mul (2 : ℝ))
  simpa [Function.comp_def, mul_comm] using h.deriv

/-- `sin(2θ)^2 ≤ 1` on `Iθ`. -/
private lemma sfb_sin_sq_le_one {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (Real.sin (2 * θ)) ^ 2 ≤ 1 := by
  have h0 := sin_two_nonneg hθ
  have h1 := sin_two_le_one θ
  nlinarith

/-- `sin(2θ)^{4-γ} ≤ sin(2θ)^{-η}` on `Iθ` for `α ≤ 1`. -/
private lemma sfb_sin_rpow_four_sub_gam_le_thEta {α : ℝ} (hα1 : α ≤ 1) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    (Real.sin (2 * θ)) ^ (4 - Work.Spaces.gam α) ≤ thEta θ := by
  have h4 : 0 < 4 - Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith
  have hle : -(Work.Spaces.eta) ≤ 4 - Work.Spaces.gam α := by
    rw [Work.Spaces.gam, Work.Spaces.eta]; linarith
  exact sin_two_rpow_le_rpow h4 hle hθ

/-- `sliceA u ≥ 0`. -/
private lemma sfb_sliceA_nonneg (u : ℝ → ℝ) : 0 ≤ sliceA u :=
  setIntegral_nonneg measurableSet_Icc
    (fun _ hθ => mul_nonneg (sq_nonneg _) (thEta_nonneg hθ))

/-- `slicePhi α K u θ ≥ 0` on `Iθ`. -/
private lemma sfb_slicePhi_nonneg (K : ℕ) (α : ℝ) (u : ℝ → ℝ) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ slicePhi α K u θ := by
  have hs := sin_two_nonneg hθ
  have h1 : 0 ≤ (sliceV u θ) ^ 2 * thEta θ := mul_nonneg (sq_nonneg _) (thEta_nonneg hθ)
  have h2 : 0 ≤ ∑ m ∈ Finset.Icc 1 K, (LopIter m (sliceV u) θ) ^ 2 * thGam α θ :=
    Finset.sum_nonneg (fun m _ => mul_nonneg (sq_nonneg _) (thGam_nonneg hθ))
  have h3 : 0 ≤ sliceA u * (thEta θ + (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
      + (Real.sin (2 * θ)) ^ (4 - Work.Spaces.gam α)) := by
    refine mul_nonneg (sfb_sliceA_nonneg u) ?_
    have h4 : 0 ≤ (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) := Real.rpow_nonneg hs _
    have h5 : 0 ≤ (Real.sin (2 * θ)) ^ (4 - Work.Spaces.gam α) := Real.rpow_nonneg hs _
    linarith [thEta_nonneg hθ]
  change 0 ≤ (sliceV u θ) ^ 2 * thEta θ
    + (∑ m ∈ Finset.Icc 1 K, (LopIter m (sliceV u) θ) ^ 2 * thGam α θ)
    + sliceA u * (thEta θ + (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
        + (Real.sin (2 * θ)) ^ (4 - Work.Spaces.gam α))
  linarith

/-- The data term `(u''θ)² sin(2θ)^{-η}` is dominated by `slicePhi`. -/
private lemma sfb_sliceV_sq_thEta_le_phi (K : ℕ) (α : ℝ) (u : ℝ → ℝ) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    (sliceV u θ) ^ 2 * thEta θ ≤ slicePhi α K u θ := by
  have h2 : 0 ≤ ∑ m ∈ Finset.Icc 1 K, (LopIter m (sliceV u) θ) ^ 2 * thGam α θ :=
    Finset.sum_nonneg (fun m _ => mul_nonneg (sq_nonneg _) (thGam_nonneg hθ))
  have hs := sin_two_nonneg hθ
  have h3 : 0 ≤ sliceA u * (thEta θ + (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
      + (Real.sin (2 * θ)) ^ (4 - Work.Spaces.gam α)) := by
    refine mul_nonneg (sfb_sliceA_nonneg u) ?_
    have h4 : 0 ≤ (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) := Real.rpow_nonneg hs _
    have h5 : 0 ≤ (Real.sin (2 * θ)) ^ (4 - Work.Spaces.gam α) := Real.rpow_nonneg hs _
    linarith [thEta_nonneg hθ]
  change (sliceV u θ) ^ 2 * thEta θ
    ≤ (sliceV u θ) ^ 2 * thEta θ
      + (∑ m ∈ Finset.Icc 1 K, (LopIter m (sliceV u) θ) ^ 2 * thGam α θ)
      + sliceA u * (thEta θ + (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
          + (Real.sin (2 * θ)) ^ (4 - Work.Spaces.gam α))
  linarith

/-- Each summand `(D_θ^m u'' θ)² sin(2θ)^{-γ}`, `1 ≤ m ≤ K`, is dominated by `slicePhi`. -/
private lemma sfb_LopIter_sliceV_sq_le_phi (K : ℕ) (α : ℝ) (u : ℝ → ℝ) {m : ℕ}
    (hm : m ∈ Finset.Icc 1 K) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (LopIter m (sliceV u) θ) ^ 2 * thGam α θ ≤ slicePhi α K u θ := by
  have h1 : 0 ≤ (sliceV u θ) ^ 2 * thEta θ := mul_nonneg (sq_nonneg _) (thEta_nonneg hθ)
  have hs := sin_two_nonneg hθ
  have h3 : 0 ≤ sliceA u * (thEta θ + (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
      + (Real.sin (2 * θ)) ^ (4 - Work.Spaces.gam α)) := by
    refine mul_nonneg (sfb_sliceA_nonneg u) ?_
    have h4 : 0 ≤ (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) := Real.rpow_nonneg hs _
    have h5 : 0 ≤ (Real.sin (2 * θ)) ^ (4 - Work.Spaces.gam α) := Real.rpow_nonneg hs _
    linarith [thEta_nonneg hθ]
  have hsum : (LopIter m (sliceV u) θ) ^ 2 * thGam α θ
      ≤ ∑ j ∈ Finset.Icc 1 K, (LopIter j (sliceV u) θ) ^ 2 * thGam α θ :=
    Finset.single_le_sum (f := fun j => (LopIter j (sliceV u) θ) ^ 2 * thGam α θ)
      (fun j _ => mul_nonneg (sq_nonneg _) (thGam_nonneg hθ)) hm
  change (LopIter m (sliceV u) θ) ^ 2 * thGam α θ
    ≤ (sliceV u θ) ^ 2 * thEta θ
      + (∑ j ∈ Finset.Icc 1 K, (LopIter j (sliceV u) θ) ^ 2 * thGam α θ)
      + sliceA u * (thEta θ + (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
          + (Real.sin (2 * θ)) ^ (4 - Work.Spaces.gam α))
  linarith

/-- `sliceA u · sin(2θ)^{-η}` is dominated by `slicePhi`. -/
private lemma sfb_sliceA_thEta_le_phi (K : ℕ) (α : ℝ) (u : ℝ → ℝ) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    sliceA u * thEta θ ≤ slicePhi α K u θ := by
  have hA := sfb_sliceA_nonneg u
  have hs := sin_two_nonneg hθ
  have h4 : 0 ≤ (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) := Real.rpow_nonneg hs _
  have h5 : 0 ≤ (Real.sin (2 * θ)) ^ (4 - Work.Spaces.gam α) := Real.rpow_nonneg hs _
  have h1 : 0 ≤ (sliceV u θ) ^ 2 * thEta θ := mul_nonneg (sq_nonneg _) (thEta_nonneg hθ)
  have h2 : 0 ≤ ∑ m ∈ Finset.Icc 1 K, (LopIter m (sliceV u) θ) ^ 2 * thGam α θ :=
    Finset.sum_nonneg (fun m _ => mul_nonneg (sq_nonneg _) (thGam_nonneg hθ))
  have hbracket : thEta θ ≤ thEta θ + (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
      + (Real.sin (2 * θ)) ^ (4 - Work.Spaces.gam α) := by linarith
  have hmul := mul_le_mul_of_nonneg_left hbracket hA
  change sliceA u * thEta θ
    ≤ (sliceV u θ) ^ 2 * thEta θ
      + (∑ m ∈ Finset.Icc 1 K, (LopIter m (sliceV u) θ) ^ 2 * thGam α θ)
      + sliceA u * (thEta θ + (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
          + (Real.sin (2 * θ)) ^ (4 - Work.Spaces.gam α))
  linarith

/-- `sliceA u · sin(2θ)^{2-γ}` is dominated by `slicePhi`. -/
private lemma sfb_sliceA_rpow_le_phi (K : ℕ) (α : ℝ) (u : ℝ → ℝ) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    sliceA u * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) ≤ slicePhi α K u θ := by
  have hA := sfb_sliceA_nonneg u
  have hs := sin_two_nonneg hθ
  have h4 : 0 ≤ (Real.sin (2 * θ)) ^ (4 - Work.Spaces.gam α) := Real.rpow_nonneg hs _
  have h1 : 0 ≤ (sliceV u θ) ^ 2 * thEta θ := mul_nonneg (sq_nonneg _) (thEta_nonneg hθ)
  have h2 : 0 ≤ ∑ m ∈ Finset.Icc 1 K, (LopIter m (sliceV u) θ) ^ 2 * thGam α θ :=
    Finset.sum_nonneg (fun m _ => mul_nonneg (sq_nonneg _) (thGam_nonneg hθ))
  have hbracket : (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
      ≤ thEta θ + (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
        + (Real.sin (2 * θ)) ^ (4 - Work.Spaces.gam α) := by
    linarith [thEta_nonneg hθ]
  have hmul := mul_le_mul_of_nonneg_left hbracket hA
  change sliceA u * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
    ≤ (sliceV u θ) ^ 2 * thEta θ
      + (∑ m ∈ Finset.Icc 1 K, (LopIter m (sliceV u) θ) ^ 2 * thGam α θ)
      + sliceA u * (thEta θ + (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
          + (Real.sin (2 * θ)) ^ (4 - Work.Spaces.gam α))
  linarith

/-! ## Locality of the iterates of `L` -/

private lemma sfb_eventuallyEq_nhds_mono {u v : ℝ → ℝ} {θ : ℝ} (h : u =ᶠ[𝓝 θ] v) :
    ∀ᶠ θ' in 𝓝 θ, u =ᶠ[𝓝 θ'] v := by
  obtain ⟨t, hts, htopen, hθt⟩ := mem_nhds_iff.mp h
  filter_upwards [htopen.mem_nhds hθt] with θ' hθ'
  exact eventually_of_mem (htopen.mem_nhds hθ') hts

private lemma sfb_Lop_eventuallyEq {u v : ℝ → ℝ} {θ : ℝ} (h : u =ᶠ[𝓝 θ] v) :
    ∀ᶠ θ' in 𝓝 θ, Work.Spaces.Lop u θ' = Work.Spaces.Lop v θ' := by
  filter_upwards [sfb_eventuallyEq_nhds_mono h] with θ' hθ'
  simp only [Work.Spaces.Lop]
  rw [hθ'.deriv_eq]

private lemma sfb_LopIter_eventuallyEq {u v : ℝ → ℝ} {θ : ℝ} (h : u =ᶠ[𝓝 θ] v) (m : ℕ) :
    ∀ᶠ θ' in 𝓝 θ, LopIter m u θ' = LopIter m v θ' := by
  induction m with
  | zero =>
      filter_upwards [h] with θ' hθ'
      simpa only [LopIter_zero] using hθ'
  | succ m ih =>
      have h' : LopIter m u =ᶠ[𝓝 θ] LopIter m v := ih
      simpa only [LopIter_succ] using sfb_Lop_eventuallyEq h'

private lemma sfb_LopIter_congr_nhds {u v : ℝ → ℝ} {θ : ℝ} (h : u =ᶠ[𝓝 θ] v) (m : ℕ) :
    LopIter m u θ = LopIter m v θ :=
  (sfb_LopIter_eventuallyEq h m).self_of_nhds

/-- An open neighbourhood of a point of smoothness consisting of points of smoothness. -/
private lemma sfb_contDiffAt_open {u : ℝ → ℝ} {θ : ℝ} (hu : ContDiffAt ℝ ⊤ u θ) :
    ∃ t : Set ℝ, IsOpen t ∧ θ ∈ t ∧ ∀ x ∈ t, ContDiffAt ℝ ⊤ u x := by
  obtain ⟨s, hs, hsm⟩ := hu.contDiffOn le_rfl
    (fun h => absurd h.symm (ne_of_lt (WithTop.coe_lt_top (a := (⊤ : ℕ∞)))))
  obtain ⟨t, hts, htopen, hθt⟩ := mem_nhds_iff.mp hs
  exact ⟨t, htopen, hθt, fun x hx => (htopen.contDiffOn_iff.mp (hsm.mono hts)) hx⟩

/-! ## The iterates of `sin(2θ)²` and of `2 cos(2θ)` -/

private lemma sfb_LopIter_sin_sq_factor (a : ℕ) :
    LopIter a (fun θ : ℝ => (Real.sin (2 * θ)) ^ 2)
      = fun θ : ℝ => (Real.sin (2 * θ)) ^ 2 * Work.FTS.EllipticEst.gfun a θ := by
  induction a with
  | zero => funext θ; simp
  | succ n ih =>
      rw [LopIter_succ, ih, Work.FTS.EllipticEst.gfun_succ]
      funext θ
      have hsin : DifferentiableAt ℝ (fun t : ℝ => Real.sin (2 * t)) θ := by fun_prop
      have hg : DifferentiableAt ℝ (Work.FTS.EllipticEst.gfun n) θ :=
        ((GfunContDiff n).differentiable (by simp)).differentiableAt
      have hh : DifferentiableAt ℝ
          (fun t : ℝ => Real.sin (2 * t) * Work.FTS.EllipticEst.gfun n t) θ := hsin.mul hg
      have h1 : (fun t : ℝ => (Real.sin (2 * t)) ^ 2 * Work.FTS.EllipticEst.gfun n t)
          = fun t : ℝ => Real.sin (2 * t) * (Real.sin (2 * t) * Work.FTS.EllipticEst.gfun n t) := by
        funext t; ring
      rw [h1, Lop_sin_mul _ θ hh]
      have hderiv : deriv (fun t : ℝ => Real.sin (2 * t) * Work.FTS.EllipticEst.gfun n t) θ
          = 2 * Real.cos (2 * θ) * Work.FTS.EllipticEst.gfun n θ
            + Real.sin (2 * θ) * deriv (Work.FTS.EllipticEst.gfun n) θ := by
        have hprod : (fun t : ℝ => Real.sin (2 * t) * Work.FTS.EllipticEst.gfun n t)
            = (fun t : ℝ => Real.sin (2 * t)) * Work.FTS.EllipticEst.gfun n := rfl
        rw [hprod, deriv_mul hsin hg, sfb_deriv_sin_two θ]
      rw [hderiv]
      ring

private theorem sfb_exists_bound_gfun (K : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ i ≤ K, ∀ θ ∈ Work.Spaces.Iθ,
      |Work.FTS.EllipticEst.gfun i θ| ≤ C := by
  induction K with
  | zero =>
      refine ⟨1, one_pos, ?_⟩
      intro i hi θ _
      have hi0 : i = 0 := Nat.le_zero.mp hi
      subst hi0
      simp
  | succ K ih =>
      obtain ⟨C, hCpos, hC⟩ := ih
      obtain ⟨D, hD⟩ := isCompact_Icc.exists_bound_of_continuousOn
        (f := Work.FTS.EllipticEst.gfun (K + 1))
        ((GfunContDiff (K + 1)).continuous.continuousOn)
      refine ⟨max C (D + 1), lt_max_of_lt_left hCpos, ?_⟩
      intro i hi θ hθ
      rcases Nat.lt_or_eq_of_le hi with hlt | heq
      · exact le_trans (hC i (Nat.lt_succ_iff.mp hlt) θ hθ) (le_max_left _ _)
      · subst heq
        have hDθ := hD θ hθ
        rw [Real.norm_eq_abs] at hDθ
        exact le_trans hDθ (le_trans (le_add_of_nonneg_right zero_le_one) (le_max_right _ _))

private theorem sfb_Lop_sin_sq_bound (K : ℕ) : ∃ D : ℝ, 1 ≤ D ∧ ∀ a ≤ K,
    ∀ θ ∈ Work.Spaces.Iθ,
    |LopIter a (fun θ : ℝ => (Real.sin (2 * θ)) ^ 2) θ|
      ≤ D * (Real.sin (2 * θ)) ^ 2 := by
  obtain ⟨C, hCpos, hC⟩ := sfb_exists_bound_gfun K
  refine ⟨max C 1, le_max_right _ _, ?_⟩
  intro a ha θ hθ
  have hval : LopIter a (fun θ : ℝ => (Real.sin (2 * θ)) ^ 2) θ
      = (Real.sin (2 * θ)) ^ 2 * Work.FTS.EllipticEst.gfun a θ :=
    congrFun (sfb_LopIter_sin_sq_factor a) θ
  rw [hval, abs_mul, abs_of_nonneg (pow_nonneg (sin_two_nonneg hθ) 2)]
  calc (Real.sin (2 * θ)) ^ 2 * |Work.FTS.EllipticEst.gfun a θ|
      ≤ (Real.sin (2 * θ)) ^ 2 * max C 1 :=
        mul_le_mul_of_nonneg_left (le_trans (hC a ha θ hθ) (le_max_left _ _))
          (pow_nonneg (sin_two_nonneg hθ) 2)
    _ = max C 1 * (Real.sin (2 * θ)) ^ 2 := by ring

private theorem sfb_cos_iter_bound {K : ℕ} {D : ℝ} (hD : 1 ≤ D)
    (hss : ∀ a ≤ K, ∀ θ ∈ Work.Spaces.Iθ,
      |LopIter a (fun θ : ℝ => (Real.sin (2 * θ)) ^ 2) θ| ≤ D * (Real.sin (2 * θ)) ^ 2) :
    ∀ a ≤ K, ∀ θ ∈ Work.Spaces.Iθ,
      |LopIter a (fun θ : ℝ => 2 * Real.cos (2 * θ)) θ| ≤ 4 * D := by
  intro a ha θ hθ
  have hD0 : 0 ≤ D := le_trans zero_le_one hD
  rcases Nat.eq_zero_or_pos a with h0 | hpos
  · subst h0
    have hcos : |2 * Real.cos (2 * θ)| ≤ 2 := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      have := Real.abs_cos_le_one (2 * θ)
      linarith
    simp only [LopIter_zero]
    linarith
  · obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
    have hval : LopIter (b + 1) (fun θ : ℝ => 2 * Real.cos (2 * θ)) θ
        = -4 * LopIter b (fun θ : ℝ => (Real.sin (2 * θ)) ^ 2) θ := by
      rw [Lop_iter_cos_eq (b + 1) (by omega)]
      simp only [Nat.add_sub_cancel]
    rw [hval, abs_mul, show |(-4 : ℝ)| = 4 by norm_num]
    have hb : |LopIter b (fun θ : ℝ => (Real.sin (2 * θ)) ^ 2) θ|
        ≤ D * (Real.sin (2 * θ)) ^ 2 := hss b (by omega) θ hθ
    have h1 : D * (Real.sin (2 * θ)) ^ 2 ≤ D * 1 :=
      mul_le_mul_of_nonneg_left (sfb_sin_sq_le_one hθ) hD0
    linarith

private lemma sfb_choose_sq_sum_le (n : ℕ) :
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

/-! ## The expansion of `L^{n+2} u` -/

/-- The `u''`-terms of the expansion of `L^{n+2} u`. -/
private def sfF1 (n : ℕ) (u : ℝ → ℝ) (θ : ℝ) (a : ℕ) : ℝ :=
  (n.choose a : ℝ) * LopIter a (fun θ : ℝ => (Real.sin (2 * θ)) ^ 2) θ
    * LopIter (n - a) (sliceV u) θ

/-- The `u`-terms of the expansion of `L^{n+2} u`. -/
private def sfF2 (n : ℕ) (u : ℝ → ℝ) (θ : ℝ) (a : ℕ) : ℝ :=
  (n.choose a : ℝ) * LopIter a (fun θ : ℝ => 2 * Real.cos (2 * θ)) θ
    * LopIter (n + 1 - a) u θ

private lemma sfb_LopIter_expand_succ (n : ℕ) {u : ℝ → ℝ} {θ : ℝ}
    (hu : ContDiffAt ℝ ⊤ u θ) :
    LopIter (n + 2) u θ
      = (∑ a ∈ Finset.range (n + 1), sfF1 n u θ a)
        + (∑ a ∈ Finset.range (n + 1), sfF2 n u θ a) := by
  obtain ⟨t, htopen, hθt, hCt⟩ := sfb_contDiffAt_open hu
  -- the germ identity `L² u = sin(2·)² u'' + 2cos(2·) (L u)`
  have h2 : LopIter 2 u =ᶠ[𝓝 θ]
      (fun θ' : ℝ => (Real.sin (2 * θ')) ^ 2 * sliceV u θ'
        + 2 * Real.cos (2 * θ') * LopIter 1 u θ') := by
    filter_upwards [htopen.mem_nhds hθt] with θ' hθ'
    exact sf_LopIter_two (hCt θ' hθ')
  -- the iterates only see the germ
  have hiter : LopIter (n + 2) u θ = LopIter n (LopIter 2 u) θ := by
    simp only [LopIter, Function.iterate_add_apply]
  rw [hiter, sfb_LopIter_congr_nhds h2 n]
  -- smoothness of the two summands of the split
  have hdu : ContDiffAt ℝ ⊤ (deriv u) θ := ContDiffAt.derivWithin (m := ⊤) hu (by simp)
  have hddu : ContDiffAt ℝ ⊤ (sliceV u) θ := by
    have h := ContDiffAt.derivWithin (m := ⊤) hdu (by simp)
    simpa only [sliceV] using h
  have hss : ContDiffAt ℝ ⊤ (fun θ' : ℝ => (Real.sin (2 * θ')) ^ 2) θ := by
    have h1 : ContDiffAt ℝ ⊤ (fun θ' : ℝ => Real.sin (2 * θ')) θ := by fun_prop
    simpa using h1.pow 2
  have hcc : ContDiffAt ℝ ⊤ (fun θ' : ℝ => 2 * Real.cos (2 * θ')) θ := by fun_prop
  have hLu : ContDiffAt ℝ ⊤ (LopIter 1 u) θ := by
    have := Work.Spaces.Lop_iter_contDiffAt u θ hu 1
    simpa only [Work.FTS.EllipticEst.LopIter] using this
  have hf1 : ContDiffAt ℝ ⊤ (fun θ' : ℝ => (Real.sin (2 * θ')) ^ 2 * sliceV u θ') θ :=
    hss.mul hddu
  have hf2 : ContDiffAt ℝ ⊤ (fun θ' : ℝ => 2 * Real.cos (2 * θ') * LopIter 1 u θ') θ :=
    hcc.mul hLu
  rw [sf_LopIter_add hf1 hf2]
  -- Leibniz for each of the two products
  have hprod1 : (fun θ' : ℝ => (Real.sin (2 * θ')) ^ 2 * sliceV u θ')
      = (fun θ' : ℝ => (Real.sin (2 * θ')) ^ 2) * sliceV u := rfl
  have hprod2 : (fun θ' : ℝ => 2 * Real.cos (2 * θ') * LopIter 1 u θ')
      = (fun θ' : ℝ => 2 * Real.cos (2 * θ')) * LopIter 1 u := rfl
  have hmul1 := Lop_iter_mul hss hddu (i := n)
  have hmul2 := Lop_iter_mul hcc hLu (i := n)
  rw [hprod1, hprod2, hmul1, hmul2]
  have hsum1 : (∑ a ∈ Finset.range (n + 1), (n.choose a : ℝ)
        * LopIter a (fun θ' : ℝ => (Real.sin (2 * θ')) ^ 2) θ
        * LopIter (n - a) (sliceV u) θ)
      = ∑ a ∈ Finset.range (n + 1), sfF1 n u θ a := by
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rfl
  have hsum2 : (∑ a ∈ Finset.range (n + 1), (n.choose a : ℝ)
        * LopIter a (fun θ' : ℝ => 2 * Real.cos (2 * θ')) θ
        * LopIter (n - a) (LopIter 1 u) θ)
      = ∑ a ∈ Finset.range (n + 1), sfF2 n u θ a := by
    refine Finset.sum_congr rfl (fun a ha => ?_)
    have ha' : a ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
    have hidx : LopIter (n - a) (LopIter 1 u) = LopIter (n + 1 - a) u := by
      have h1 : LopIter (n - a) (LopIter 1 u) = LopIter (n - a) (Work.Spaces.Lop u) := by
        simp only [LopIter, Function.iterate_one]
      rw [h1, ← LopIter_succ_apply]
      congr 1
      omega
    have hbase : (n.choose a : ℝ) * LopIter a (fun θ' : ℝ => 2 * Real.cos (2 * θ')) θ
        * LopIter (n + 1 - a) u θ = sfF2 n u θ a := rfl
    simpa only [hidx] using hbase
  rw [hsum1, hsum2]

/-- Cauchy–Schwarz for a finite sum: `(Σ f)² w ≤ card · Σ f² w` for `w ≥ 0`. -/
private lemma sfb_sum_sq_mul_le {ι : Type*} (s : Finset ι) (F : ι → ℝ) {w : ℝ} (hw : 0 ≤ w) :
    (∑ a ∈ s, F a) ^ 2 * w ≤ (s.card : ℝ) * ∑ a ∈ s, (F a) ^ 2 * w := by
  have h1 := sq_sum_le_card_mul_sum_sq (s := s) (f := F)
  have h2 : (∑ a ∈ s, F a) ^ 2 * w ≤ ((s.card : ℝ) * ∑ a ∈ s, (F a) ^ 2) * w :=
    mul_le_mul_of_nonneg_right h1 hw
  have h3 : ((s.card : ℝ) * ∑ a ∈ s, (F a) ^ 2) * w
      = (s.card : ℝ) * ∑ a ∈ s, (F a) ^ 2 * w := by
    rw [mul_assoc, Finset.sum_mul]
  linarith [h2, le_of_eq h3]


/-- **The `∂_θ²`-slice estimate of the angular `θ`-Poincaré inequality.**  For a smooth slice `u` vanishing at `θ = 0, π/2`, with `v = u''`, `A = ∫_{Iθ} v² sin(2θ)^{-η}` and the dominating function

`slicePhi α K u θ = v θ² sin(2θ)^{-η} + ∑_{m=1}^{K} (D_θ^m v θ)² sin(2θ)^{-γ} + A·(sin(2θ)^{-η} + sin(2θ)^{2-γ} + sin(2θ)^{4-γ})`

(`γ = gam α = 1 + α/10`, `η = eta = 99/100`), one has for every `θ ∈ Iθ`

`(u θ)² sin(2θ)^{-η} ≤ C · slicePhi α K u θ`  and  `(D_θ^i u θ)² sin(2θ)^{-γ} ≤ C · slicePhi α K u θ` for every `1 ≤ i ≤ K`,

with `C` independent of `α ∈ (0,1]` and of `u`.

NOTE.  Use namespace `Work.FTS.EllipticEst.Blocks` (a declaration `Work.FTS.EllipticEst.slice_f_bound` with this statement already exists in a `sorry`-containing sibling; do not import it).  The auxiliary statement `(u θ)² ≤ (π/2)²·A·∫ sin(2θ)^η` you may need is a sibling target of the same wave (`…FTS.EllipticEst.Blocks.slice_self_sq_le`); if it is present import it, otherwise prove it yourself as a private lemma.

ROUTE (pointwise, by strong induction on the number of `D_θ`'s; write `L = D_θ = sin(2θ)∂_θ`).
* `i = 1`: `(L u θ)² sin(2θ)^{-γ} = sin(2θ)^{2-γ}(∂_θ u θ)²`, and `(∂_θ u)² ≤ A·∫sin(2θ)^η` by `slice_deriv_sq_le` (valid as `u 0 = u(π/2)`); the factor `sin(2θ)^{2-γ}` is one of the fixed terms of `slicePhi`.  The term `(u θ)² sin(2θ)^{-η}` follows from `u θ = ∫_0^θ ∂_θ u`, `(u θ)² ≤ (π/2)² A ∫sin^η` (via `slice_deriv_sq_le` and `∫ sin^η ≤ π/2`).
* `i ≥ 2`: pointwise `L²u = sin(2θ)²·v + 2cos(2θ)·(L u)`, and by the Leibniz rule `Lop_iter_mul` applied to `L^{i-2}(sin²(2θ)·v + 2cos(2θ)·(L u))`, the iterate `L^i u` is a finite combination of terms `L^a(sin²)·L^{i-2-a}v` and `L^a(2cos 2θ)·L^{i-1-a}u` with binomial coefficients.  Since `|L^a(sin²) θ| ≤ C_a sin(2θ)²` (`Lop_iter_sin_sq_bound`, sorry-free) and `L^a(2cos 2θ) = -4L^{a-1}(sin²)` for `a ≥ 1` (`Lop_iter_cos_eq`, sorry-free; so also `O(sin²)`), while `a = 0` gives `|2cos 2θ| ≤ 2`, every term is dominated either by a fixed term of `slicePhi` (the `v`-terms, using `sin(2θ)^{4-γ} ≤ sin(2θ)^{-η}` and `sin(2θ)^{4-γ} ≤ sin(2θ)^{-γ}`) or, for the `u`-terms, by `C'·slicePhi` through the induction hypothesis (index `< i`, using `sin(2θ)^{4-γ} ≤ sin(2θ)^{-γ}`); the constant grows by a fixed factor per step, harmless on the finite range `1 ≤ i ≤ K`.  At `θ = 0, π/2` all weights vanish and both sides are `0`. -/
theorem slice_f_bound (K : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (u : ℝ → ℝ), 0 < α → α ≤ 1 → Work.FTS.EllipticEst.SliceSmooth u → u 0 = 0
      → u (Real.pi / 2) = 0
      → MeasureTheory.IntegrableOn
          (fun θ => (Work.FTS.EllipticEst.sliceV u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
          Work.Spaces.Iθ
      → (∀ m ∈ Finset.Icc 1 K, MeasureTheory.IntegrableOn
          (fun θ => (Work.FTS.EllipticEst.LopIter m (Work.FTS.EllipticEst.sliceV u) θ) ^ 2
            * Work.FTS.EllipticEst.thGam α θ) Work.Spaces.Iθ)
      → (∀ θ ∈ Work.Spaces.Iθ, (u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ
            ≤ C * Work.FTS.EllipticEst.slicePhi α K u θ)
        ∧ (∀ i ∈ Finset.Icc 1 K, ∀ θ ∈ Work.Spaces.Iθ,
            (Work.FTS.EllipticEst.LopIter i u θ) ^ 2 * Work.FTS.EllipticEst.thGam α θ
              ≤ C * Work.FTS.EllipticEst.slicePhi α K u θ) := by
  obtain ⟨D, hD1, hDss⟩ := sfb_Lop_sin_sq_bound K
  have hDcos := sfb_cos_iter_bound hD1 hDss
  set B : ℝ := 2 + Real.pi / 2 + 34 * ((K : ℝ) + 1) ^ 2 * D ^ 2 * (4 : ℝ) ^ K with hBdef
  have hBextra : 0 ≤ 34 * ((K : ℝ) + 1) ^ 2 * D ^ 2 * (4 : ℝ) ^ K := by positivity
  have hB1 : 1 ≤ B := by rw [hBdef]; linarith [Real.pi_pos]
  have hB0 : 0 ≤ B := le_trans zero_le_one hB1
  have hBpi : Real.pi / 2 ≤ B := by rw [hBdef]; linarith
  have hBstep : ∀ n ≤ K, 34 * ((n : ℝ) + 1) ^ 2 * D ^ 2 * (4 : ℝ) ^ n ≤ B := by
    intro n hn
    have h1 : ((n : ℝ) + 1) ^ 2 ≤ ((K : ℝ) + 1) ^ 2 := by
      have hn' : (n : ℝ) ≤ (K : ℝ) := by exact_mod_cast hn
      nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]
    have h2 : (4 : ℝ) ^ n ≤ (4 : ℝ) ^ K := pow_le_pow_right₀ (by norm_num) hn
    have h3 : 0 ≤ D ^ 2 := sq_nonneg D
    have h4 : 0 ≤ ((n : ℝ) + 1) ^ 2 := sq_nonneg _
    calc 34 * ((n : ℝ) + 1) ^ 2 * D ^ 2 * (4 : ℝ) ^ n
        ≤ 34 * ((K : ℝ) + 1) ^ 2 * D ^ 2 * (4 : ℝ) ^ K := by gcongr
      _ ≤ B := by rw [hBdef]; linarith [Real.pi_pos]
  refine ⟨B ^ K + (Real.pi / 2) ^ 3 + 1, ?_, ?_⟩
  · have hBK : 0 < B ^ K := pow_pos (lt_of_lt_of_le zero_lt_one hB1) K
    have hpi : 0 < (Real.pi / 2) ^ 3 := by positivity
    linarith
  · intro α u hα0 hα1 hsm h0 h1 hint hint2
    have hP0 : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ slicePhi α K u θ :=
      fun θ hθ => sfb_slicePhi_nonneg K α u hθ
    -- the `u`-term
    have hgoal1 : ∀ θ ∈ Work.Spaces.Iθ, (u θ) ^ 2 * thEta θ
        ≤ (B ^ K + (Real.pi / 2) ^ 3 + 1) * slicePhi α K u θ := by
      intro θ hθ
      have hself := slice_self_sq_le hsm h0 h1 hint θ hθ
      have hBint : (∫ x in Work.Spaces.Iθ, (Real.sin (2 * x)) ^ (Work.Spaces.eta))
          ≤ Real.pi / 2 :=
        (integrableOn_sin_two_rpow (p := Work.Spaces.eta)
          (by rw [Work.Spaces.eta]; norm_num)).2
      have hA0 : 0 ≤ sliceA u := sfb_sliceA_nonneg u
      have hth : 0 ≤ thEta θ := thEta_nonneg hθ
      have hp : 0 ≤ slicePhi α K u θ := hP0 θ hθ
      have hc0 : 0 ≤ (Real.pi / 2) ^ 2 * sliceA u := mul_nonneg (by positivity) hA0
      calc (u θ) ^ 2 * thEta θ
          ≤ ((Real.pi / 2) ^ 2 * (sliceA u
              * (∫ x in Work.Spaces.Iθ, (Real.sin (2 * x)) ^ (Work.Spaces.eta)))) * thEta θ :=
            mul_le_mul_of_nonneg_right hself hth
        _ = (Real.pi / 2) ^ 2 * sliceA u
              * ((∫ x in Work.Spaces.Iθ, (Real.sin (2 * x)) ^ (Work.Spaces.eta)) * thEta θ) := by
            ring
        _ ≤ (Real.pi / 2) ^ 2 * sliceA u * ((Real.pi / 2) * thEta θ) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hBint hth) hc0
        _ = (Real.pi / 2) ^ 3 * (sliceA u * thEta θ) := by ring
        _ ≤ (Real.pi / 2) ^ 3 * slicePhi α K u θ :=
            mul_le_mul_of_nonneg_left (sfb_sliceA_thEta_le_phi K α u hθ) (by positivity)
        _ ≤ (B ^ K + (Real.pi / 2) ^ 3 + 1) * slicePhi α K u θ := by
            refine mul_le_mul_of_nonneg_right ?_ hp
            have hBK : 0 < B ^ K := pow_pos (lt_of_lt_of_le zero_lt_one hB1) K
            have hpi : 0 < (Real.pi / 2) ^ 3 := by positivity
            linarith
    -- strong induction for the `L^i u` bounds
    have key : ∀ i ≤ K, 1 ≤ i → ∀ θ ∈ Work.Spaces.Iθ,
        (LopIter i u θ) ^ 2 * thGam α θ ≤ B ^ i * slicePhi α K u θ := by
      intro i
      refine Nat.strong_induction_on i ?_
      intro m ih hmK hm1 θ hθ
      rcases eq_or_lt_of_le hm1 with hEq | hLt
      · -- `m = 1`: `(L u)² sin(2θ)^{-γ} = sin(2θ)^{2-γ} (∂_θ u)²`
        have hm1' : m = 1 := hEq.symm
        subst hm1'
        have hdu := slice_deriv_sq_le hsm (by rw [h0, h1]) hint
        have hBint : (∫ x in Work.Spaces.Iθ, (Real.sin (2 * x)) ^ (Work.Spaces.eta))
            ≤ Real.pi / 2 :=
          (integrableOn_sin_two_rpow (p := Work.Spaces.eta)
            (by rw [Work.Spaces.eta]; norm_num)).2
        have hA0 : 0 ≤ sliceA u := sfb_sliceA_nonneg u
        have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg hθ
        have hgame : Work.Spaces.gam α ≠ 0 := sfb_gam_ne hα0
        have h2g : (2 : ℝ) - Work.Spaces.gam α ≠ 0 := sfb_two_sub_gam_ne hα1
        have hLval : LopIter 1 u θ = Real.sin (2 * θ) * deriv u θ := by
          simp only [LopIter_succ, LopIter_zero, Work.Spaces.Lop]
        have hrpow : (Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            = (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) :=
          sfb_pow_mul_rpow (sin_two_nonneg hθ) (by norm_num) hgame
            (by intro hc; exact h2g (sub_eq_zero.mpr hc))
        rw [hLval]
        rw [show thGam α θ = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) from rfl]
        calc (Real.sin (2 * θ) * deriv u θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            = (Real.sin (2 * θ)) ^ 2
              * ((deriv u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by ring
          _ ≤ (Real.sin (2 * θ)) ^ 2
              * ((sliceA u * (∫ x in Work.Spaces.Iθ, (Real.sin (2 * x)) ^ (Work.Spaces.eta)))
                  * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
              refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hs 2)
              exact mul_le_mul_of_nonneg_right (hdu θ hθ) (Real.rpow_nonneg hs _)
          _ = (sliceA u * (∫ x in Work.Spaces.Iθ, (Real.sin (2 * x)) ^ (Work.Spaces.eta)))
              * ((Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
              ring
          _ = (sliceA u * (∫ x in Work.Spaces.Iθ, (Real.sin (2 * x)) ^ (Work.Spaces.eta)))
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) := by rw [hrpow]
          _ ≤ (sliceA u * (Real.pi / 2)) * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) := by
              refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hs _)
              exact mul_le_mul_of_nonneg_left hBint hA0
          _ = (Real.pi / 2) * (sliceA u * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) := by
              ring
          _ ≤ (Real.pi / 2) * slicePhi α K u θ :=
              mul_le_mul_of_nonneg_left (sfb_sliceA_rpow_le_phi K α u hθ) (by positivity)
          _ ≤ B ^ 1 * slicePhi α K u θ := by
              rw [pow_one]
              exact mul_le_mul_of_nonneg_right hBpi (hP0 θ hθ)
      · -- `m ≥ 2`
        have hm2 : 2 ≤ m := hLt
        obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
        have hnK : n ≤ K := by omega
        have huAt : ContDiffAt ℝ ⊤ u θ := by
          refine hsm.contDiffAt (isOpen_Ioo.mem_nhds ?_)
          rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
          exact ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
        have hP0θ : 0 ≤ slicePhi α K u θ := hP0 θ hθ
        have hg0 : 0 ≤ thGam α θ := thGam_nonneg hθ
        have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg hθ
        have hs4 : ((Real.sin (2 * θ)) ^ 2) ^ 2 ≤ 1 := by
          have h := sfb_sin_sq_le_one hθ
          nlinarith
        have hexp := sfb_LopIter_expand_succ (u := u) (θ := θ) n huAt
        have hIH : ∀ j, 1 ≤ j → j ≤ n + 1 →
            (LopIter j u θ) ^ 2 * thGam α θ ≤ B ^ (n + 1) * slicePhi α K u θ := by
          intro j hj1 hjK
          have hlt : j < n + 2 := by omega
          have hjK' : j ≤ K := by omega
          calc (LopIter j u θ) ^ 2 * thGam α θ ≤ B ^ j * slicePhi α K u θ :=
                ih j hlt hjK' hj1 θ hθ
            _ ≤ B ^ (n + 1) * slicePhi α K u θ :=
                mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hB1 hjK) hP0θ
        -- the `u''`-terms
        have hterm1 : ∀ a ∈ Finset.range (n + 1), (sfF1 n u θ a) ^ 2 * thGam α θ
            ≤ ((n.choose a : ℝ)) ^ 2 * (D ^ 2 * slicePhi α K u θ) := by
          intro a ha
          have hunfold : sfF1 n u θ a = (n.choose a : ℝ)
              * LopIter a (fun θ : ℝ => (Real.sin (2 * θ)) ^ 2) θ
              * LopIter (n - a) (sliceV u) θ := rfl
          rw [hunfold]
          have ha' : a ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
          have haK : a ≤ K := by omega
          have hsq : (LopIter a (fun θ : ℝ => (Real.sin (2 * θ)) ^ 2) θ) ^ 2
              ≤ D ^ 2 * ((Real.sin (2 * θ)) ^ 2) ^ 2 := by
            rw [← sq_abs]
            calc |LopIter a (fun θ : ℝ => (Real.sin (2 * θ)) ^ 2) θ| ^ 2
                ≤ (D * (Real.sin (2 * θ)) ^ 2) ^ 2 :=
                  pow_le_pow_left₀ (abs_nonneg _) (hDss a haK θ hθ) 2
              _ = D ^ 2 * ((Real.sin (2 * θ)) ^ 2) ^ 2 := by ring
          rcases lt_or_eq_of_le ha' with hlt | heq
          · have hm1 : 1 ≤ n - a := by omega
            have hmK : n - a ≤ K := by omega
            have hmv := sfb_LopIter_sliceV_sq_le_phi K α u (Finset.mem_Icc.mpr ⟨hm1, hmK⟩) hθ
            have hX : 0 ≤ (LopIter (n - a) (sliceV u) θ) ^ 2 * thGam α θ :=
              mul_nonneg (sq_nonneg _) hg0
            have hstep1 : (LopIter a (fun θ : ℝ => (Real.sin (2 * θ)) ^ 2) θ) ^ 2
                * ((LopIter (n - a) (sliceV u) θ) ^ 2 * thGam α θ)
                ≤ D ^ 2 * ((Real.sin (2 * θ)) ^ 2) ^ 2
                  * ((LopIter (n - a) (sliceV u) θ) ^ 2 * thGam α θ) :=
              mul_le_mul_of_nonneg_right hsq hX
            have hstep2 : D ^ 2 * ((Real.sin (2 * θ)) ^ 2) ^ 2
                * ((LopIter (n - a) (sliceV u) θ) ^ 2 * thGam α θ)
                ≤ D ^ 2 * ((LopIter (n - a) (sliceV u) θ) ^ 2 * thGam α θ) := by
              have h2 := mul_le_mul_of_nonneg_right hs4 hX
              calc D ^ 2 * ((Real.sin (2 * θ)) ^ 2) ^ 2
                    * ((LopIter (n - a) (sliceV u) θ) ^ 2 * thGam α θ)
                  = D ^ 2 * (((Real.sin (2 * θ)) ^ 2) ^ 2
                      * ((LopIter (n - a) (sliceV u) θ) ^ 2 * thGam α θ)) := by ring
                _ ≤ D ^ 2 * (1 * ((LopIter (n - a) (sliceV u) θ) ^ 2 * thGam α θ)) :=
                    mul_le_mul_of_nonneg_left h2 (sq_nonneg D)
                _ = D ^ 2 * ((LopIter (n - a) (sliceV u) θ) ^ 2 * thGam α θ) := by ring
            have hstep3 : D ^ 2 * ((LopIter (n - a) (sliceV u) θ) ^ 2 * thGam α θ)
                ≤ D ^ 2 * slicePhi α K u θ := mul_le_mul_of_nonneg_left hmv (sq_nonneg D)
            have hcomb : ((n.choose a : ℝ)
                * LopIter a (fun θ : ℝ => (Real.sin (2 * θ)) ^ 2) θ
                * LopIter (n - a) (sliceV u) θ) ^ 2 * thGam α θ
                = ((n.choose a : ℝ)) ^ 2
                  * ((LopIter a (fun θ : ℝ => (Real.sin (2 * θ)) ^ 2) θ) ^ 2
                    * ((LopIter (n - a) (sliceV u) θ) ^ 2 * thGam α θ)) := by ring
            rw [hcomb]
            exact mul_le_mul_of_nonneg_left (le_trans (le_trans hstep1 hstep2) hstep3)
              (sq_nonneg _)
          · subst a
            rw [Nat.sub_self, LopIter_zero, Nat.choose_self, Nat.cast_one, one_pow, one_mul]
            have hsqn : (LopIter n (fun θ : ℝ => (Real.sin (2 * θ)) ^ 2) θ) ^ 2
                ≤ D ^ 2 * ((Real.sin (2 * θ)) ^ 2) ^ 2 := by
              rw [← sq_abs]
              calc |LopIter n (fun θ : ℝ => (Real.sin (2 * θ)) ^ 2) θ| ^ 2
                  ≤ (D * (Real.sin (2 * θ)) ^ 2) ^ 2 :=
                    pow_le_pow_left₀ (abs_nonneg _) (hDss n hnK θ hθ) 2
                _ = D ^ 2 * ((Real.sin (2 * θ)) ^ 2) ^ 2 := by ring
            have hrpow : ((Real.sin (2 * θ)) ^ 2) ^ 2 * thGam α θ
                = (Real.sin (2 * θ)) ^ (4 - Work.Spaces.gam α) := by
              have h4a : ((Real.sin (2 * θ)) ^ 2) ^ 2 = (Real.sin (2 * θ)) ^ 4 := by ring
              rw [h4a, show thGam α θ = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) from rfl]
              exact sfb_pow_mul_rpow (sin_two_nonneg hθ) (by norm_num) (sfb_gam_ne hα0)
                (by intro hc; exact sfb_four_sub_gam_ne hα1 (sub_eq_zero.mpr hc))
            have hcomb : (LopIter n (fun θ : ℝ => (Real.sin (2 * θ)) ^ 2) θ * sliceV u θ) ^ 2
                * thGam α θ
                = (LopIter n (fun θ : ℝ => (Real.sin (2 * θ)) ^ 2) θ) ^ 2
                  * ((sliceV u θ) ^ 2 * thGam α θ) := by ring
            rw [hcomb]
            have h4le := sfb_sin_rpow_four_sub_gam_le_thEta hα1 hθ
            have hvle := sfb_sliceV_sq_thEta_le_phi K α u hθ
            calc (LopIter n (fun θ : ℝ => (Real.sin (2 * θ)) ^ 2) θ) ^ 2
                  * ((sliceV u θ) ^ 2 * thGam α θ)
                ≤ D ^ 2 * ((Real.sin (2 * θ)) ^ 2) ^ 2 * ((sliceV u θ) ^ 2 * thGam α θ) :=
                  mul_le_mul_of_nonneg_right hsqn (mul_nonneg (sq_nonneg _) hg0)
              _ = D ^ 2 * ((sliceV u θ) ^ 2
                    * (((Real.sin (2 * θ)) ^ 2) ^ 2 * thGam α θ)) := by ring
              _ = D ^ 2 * ((sliceV u θ) ^ 2
                    * (Real.sin (2 * θ)) ^ (4 - Work.Spaces.gam α)) := by rw [hrpow]
              _ ≤ D ^ 2 * ((sliceV u θ) ^ 2 * thEta θ) := by
                  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg D)
                  exact mul_le_mul_of_nonneg_left h4le (sq_nonneg _)
              _ ≤ 1 * (D ^ 2 * slicePhi α K u θ) := by
                  simpa using mul_le_mul_of_nonneg_left hvle (sq_nonneg D)
        -- the `u`-terms
        have hterm2 : ∀ a ∈ Finset.range (n + 1), (sfF2 n u θ a) ^ 2 * thGam α θ
            ≤ ((n.choose a : ℝ)) ^ 2 * (16 * D ^ 2 * B ^ (n + 1) * slicePhi α K u θ) := by
          intro a ha
          have hunfold : sfF2 n u θ a = (n.choose a : ℝ)
              * LopIter a (fun θ : ℝ => 2 * Real.cos (2 * θ)) θ * LopIter (n + 1 - a) u θ := rfl
          rw [hunfold]
          have ha' : a ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
          rcases Nat.eq_zero_or_pos a with h0a | hpos
          · subst a
            rw [Nat.choose_zero_right, Nat.cast_one, one_pow, Nat.sub_zero, one_mul]
            have hccval : LopIter 0 (fun θ : ℝ => 2 * Real.cos (2 * θ)) θ
                = 2 * Real.cos (2 * θ) := by simp only [LopIter_zero]
            rw [hccval]
            have hc1 : |Real.cos (2 * θ)| ≤ 1 := Real.abs_cos_le_one (2 * θ)
            have hc2 : (Real.cos (2 * θ)) ^ 2 ≤ 1 := by
              rw [← sq_abs]
              nlinarith [hc1, abs_nonneg (Real.cos (2 * θ))]
            have hc4 : (2 * Real.cos (2 * θ)) ^ 2 ≤ 4 := by nlinarith [hc2]
            have hIHn := hIH (n + 1) (by omega) (by omega)
            have hcomb : (2 * Real.cos (2 * θ) * LopIter (n + 1) u θ) ^ 2 * thGam α θ
                = (2 * Real.cos (2 * θ)) ^ 2 * ((LopIter (n + 1) u θ) ^ 2 * thGam α θ) := by
              ring
            rw [hcomb]
            calc (2 * Real.cos (2 * θ)) ^ 2 * ((LopIter (n + 1) u θ) ^ 2 * thGam α θ)
                ≤ 4 * ((LopIter (n + 1) u θ) ^ 2 * thGam α θ) :=
                  mul_le_mul_of_nonneg_right hc4 (mul_nonneg (sq_nonneg _) hg0)
              _ ≤ 4 * (B ^ (n + 1) * slicePhi α K u θ) :=
                  mul_le_mul_of_nonneg_left hIHn (by norm_num)
              _ ≤ 1 * (16 * D ^ 2 * B ^ (n + 1) * slicePhi α K u θ) := by
                  have hmul : (4 : ℝ) ≤ 16 * D ^ 2 := by nlinarith [hD1, sq_nonneg D]
                  calc 4 * (B ^ (n + 1) * slicePhi α K u θ)
                      ≤ (16 * D ^ 2) * (B ^ (n + 1) * slicePhi α K u θ) :=
                        mul_le_mul_of_nonneg_right hmul (mul_nonneg (pow_nonneg hB0 _) hP0θ)
                    _ = 1 * (16 * D ^ 2 * B ^ (n + 1) * slicePhi α K u θ) := by ring
          · obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
            have hbK : b + 1 ≤ K := by omega
            have hccb := hDcos (b + 1) hbK θ hθ
            have hcsq : (LopIter (b + 1) (fun θ : ℝ => 2 * Real.cos (2 * θ)) θ) ^ 2
                ≤ (4 * D) ^ 2 := by
              rw [← sq_abs]
              exact pow_le_pow_left₀ (abs_nonneg _) hccb 2
            have hj1 : 1 ≤ n + 1 - (b + 1) := by omega
            have hjK : n + 1 - (b + 1) ≤ n + 1 := by omega
            have hIHj := hIH (n + 1 - (b + 1)) hj1 hjK
            have hX : 0 ≤ (LopIter (n + 1 - (b + 1)) u θ) ^ 2 * thGam α θ :=
              mul_nonneg (sq_nonneg _) hg0
            have hcomb : ((n.choose (b + 1) : ℝ)
                * LopIter (b + 1) (fun θ : ℝ => 2 * Real.cos (2 * θ)) θ
                * LopIter (n + 1 - (b + 1)) u θ) ^ 2 * thGam α θ
                = ((n.choose (b + 1) : ℝ)) ^ 2
                  * ((LopIter (b + 1) (fun θ : ℝ => 2 * Real.cos (2 * θ)) θ) ^ 2
                    * ((LopIter (n + 1 - (b + 1)) u θ) ^ 2 * thGam α θ)) := by ring
            rw [hcomb]
            calc ((n.choose (b + 1) : ℝ)) ^ 2
                  * ((LopIter (b + 1) (fun θ : ℝ => 2 * Real.cos (2 * θ)) θ) ^ 2
                    * ((LopIter (n + 1 - (b + 1)) u θ) ^ 2 * thGam α θ))
                ≤ ((n.choose (b + 1) : ℝ)) ^ 2
                  * ((4 * D) ^ 2 * ((LopIter (n + 1 - (b + 1)) u θ) ^ 2 * thGam α θ)) :=
                  mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcsq hX) (sq_nonneg _)
              _ ≤ ((n.choose (b + 1) : ℝ)) ^ 2
                  * ((4 * D) ^ 2 * (B ^ (n + 1) * slicePhi α K u θ)) :=
                  mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hIHj (by positivity))
                    (sq_nonneg _)
              _ = ((n.choose (b + 1) : ℝ)) ^ 2
                  * (16 * D ^ 2 * B ^ (n + 1) * slicePhi α K u θ) := by ring
        -- the two sums
        have hS1sq : (∑ a ∈ Finset.range (n + 1), sfF1 n u θ a) ^ 2 * thGam α θ
            ≤ ((n : ℝ) + 1) ^ 2 * D ^ 2 * (4 : ℝ) ^ n * slicePhi α K u θ := by
          have hcs := sfb_sum_sq_mul_le (Finset.range (n + 1)) (fun a => sfF1 n u θ a) hg0
          have hcs' : (∑ a ∈ Finset.range (n + 1), sfF1 n u θ a) ^ 2 * thGam α θ
              ≤ ((n : ℝ) + 1) * ∑ a ∈ Finset.range (n + 1),
                (sfF1 n u θ a) ^ 2 * thGam α θ := by
            simpa only [Finset.card_range, Nat.cast_add, Nat.cast_one] using hcs
          calc (∑ a ∈ Finset.range (n + 1), sfF1 n u θ a) ^ 2 * thGam α θ
              ≤ ((n : ℝ) + 1) * ∑ a ∈ Finset.range (n + 1),
                  (sfF1 n u θ a) ^ 2 * thGam α θ := hcs'
            _ ≤ ((n : ℝ) + 1) * ∑ a ∈ Finset.range (n + 1),
                  (((n.choose a : ℝ)) ^ 2 * (D ^ 2 * slicePhi α K u θ)) :=
                mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm1) (by positivity)
            _ = ((n : ℝ) + 1) * (D ^ 2 * slicePhi α K u θ)
                  * (∑ a ∈ Finset.range (n + 1), ((n.choose a : ℝ)) ^ 2) := by
                rw [← Finset.sum_mul]
                ring_nf
            _ ≤ ((n : ℝ) + 1) * (D ^ 2 * slicePhi α K u θ)
                  * (((n : ℝ) + 1) * (4 : ℝ) ^ n) :=
                mul_le_mul_of_nonneg_left (sfb_choose_sq_sum_le n) (by positivity)
            _ = ((n : ℝ) + 1) ^ 2 * D ^ 2 * (4 : ℝ) ^ n * slicePhi α K u θ := by ring_nf
        have hS2sq : (∑ a ∈ Finset.range (n + 1), sfF2 n u θ a) ^ 2 * thGam α θ
            ≤ ((n : ℝ) + 1) ^ 2 * (4 : ℝ) ^ n
              * (16 * D ^ 2 * B ^ (n + 1) * slicePhi α K u θ) := by
          have hcs := sfb_sum_sq_mul_le (Finset.range (n + 1)) (fun a => sfF2 n u θ a) hg0
          have hcs' : (∑ a ∈ Finset.range (n + 1), sfF2 n u θ a) ^ 2 * thGam α θ
              ≤ ((n : ℝ) + 1) * ∑ a ∈ Finset.range (n + 1),
                (sfF2 n u θ a) ^ 2 * thGam α θ := by
            simpa only [Finset.card_range, Nat.cast_add, Nat.cast_one] using hcs
          calc (∑ a ∈ Finset.range (n + 1), sfF2 n u θ a) ^ 2 * thGam α θ
              ≤ ((n : ℝ) + 1) * ∑ a ∈ Finset.range (n + 1),
                  (sfF2 n u θ a) ^ 2 * thGam α θ := hcs'
            _ ≤ ((n : ℝ) + 1) * ∑ a ∈ Finset.range (n + 1),
                  (((n.choose a : ℝ)) ^ 2
                    * (16 * D ^ 2 * B ^ (n + 1) * slicePhi α K u θ)) :=
                mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm2) (by positivity)
            _ = ((n : ℝ) + 1) * (16 * D ^ 2 * B ^ (n + 1) * slicePhi α K u θ)
                  * (∑ a ∈ Finset.range (n + 1), ((n.choose a : ℝ)) ^ 2) := by
                rw [← Finset.sum_mul]
                ring_nf
            _ ≤ ((n : ℝ) + 1) * (16 * D ^ 2 * B ^ (n + 1) * slicePhi α K u θ)
                  * (((n : ℝ) + 1) * (4 : ℝ) ^ n) :=
                mul_le_mul_of_nonneg_left (sfb_choose_sq_sum_le n)
                  (mul_nonneg (by positivity) (mul_nonneg (mul_nonneg (by positivity)
                    (pow_nonneg hB0 _)) hP0θ))
            _ = ((n : ℝ) + 1) ^ 2 * (4 : ℝ) ^ n
                  * (16 * D ^ 2 * B ^ (n + 1) * slicePhi α K u θ) := by
                ring_nf
        -- assembly
        rw [hexp]
        have hsq21 : ((∑ a ∈ Finset.range (n + 1), sfF1 n u θ a)
              + (∑ a ∈ Finset.range (n + 1), sfF2 n u θ a)) ^ 2
            ≤ 2 * ((∑ a ∈ Finset.range (n + 1), sfF1 n u θ a) ^ 2
              + (∑ a ∈ Finset.range (n + 1), sfF2 n u θ a) ^ 2) := by
          nlinarith [sq_nonneg ((∑ a ∈ Finset.range (n + 1), sfF1 n u θ a)
            - (∑ a ∈ Finset.range (n + 1), sfF2 n u θ a))]
        have hstep : ((∑ a ∈ Finset.range (n + 1), sfF1 n u θ a)
              + (∑ a ∈ Finset.range (n + 1), sfF2 n u θ a)) ^ 2 * thGam α θ
            ≤ 2 * (((∑ a ∈ Finset.range (n + 1), sfF1 n u θ a) ^ 2 * thGam α θ)
              + ((∑ a ∈ Finset.range (n + 1), sfF2 n u θ a) ^ 2 * thGam α θ)) := by
          have h1 := mul_le_mul_of_nonneg_right hsq21 hg0
          have h2 : 2 * ((∑ a ∈ Finset.range (n + 1), sfF1 n u θ a) ^ 2
                + (∑ a ∈ Finset.range (n + 1), sfF2 n u θ a) ^ 2) * thGam α θ
              = 2 * (((∑ a ∈ Finset.range (n + 1), sfF1 n u θ a) ^ 2 * thGam α θ)
                + ((∑ a ∈ Finset.range (n + 1), sfF2 n u θ a) ^ 2 * thGam α θ)) := by ring
          linarith [h1, le_of_eq h2]
        have hbnd : 2 * (((∑ a ∈ Finset.range (n + 1), sfF1 n u θ a) ^ 2 * thGam α θ)
              + ((∑ a ∈ Finset.range (n + 1), sfF2 n u θ a) ^ 2 * thGam α θ))
            ≤ 2 * (((n : ℝ) + 1) ^ 2 * D ^ 2 * (4 : ℝ) ^ n * slicePhi α K u θ
              + ((n : ℝ) + 1) ^ 2 * (4 : ℝ) ^ n
                * (16 * D ^ 2 * B ^ (n + 1) * slicePhi α K u θ)) :=
          mul_le_mul_of_nonneg_left (add_le_add hS1sq hS2sq) (by norm_num)
        have hfinal1 : 2 * (((n : ℝ) + 1) ^ 2 * D ^ 2 * (4 : ℝ) ^ n * slicePhi α K u θ
              + ((n : ℝ) + 1) ^ 2 * (4 : ℝ) ^ n
                * (16 * D ^ 2 * B ^ (n + 1) * slicePhi α K u θ))
            ≤ 34 * ((n : ℝ) + 1) ^ 2 * D ^ 2 * (4 : ℝ) ^ n * B ^ (n + 1)
              * slicePhi α K u θ := by
          have hcore : 2 * (1 + 16 * B ^ (n + 1)) ≤ 34 * B ^ (n + 1) := by
            have hBp : 1 ≤ B ^ (n + 1) := one_le_pow₀ hB1
            linarith
          have hfac : 0 ≤ ((n : ℝ) + 1) ^ 2 * D ^ 2 * (4 : ℝ) ^ n * slicePhi α K u θ :=
            mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg D))
              (pow_nonneg (by norm_num) n)) hP0θ
          calc 2 * (((n : ℝ) + 1) ^ 2 * D ^ 2 * (4 : ℝ) ^ n * slicePhi α K u θ
                + ((n : ℝ) + 1) ^ 2 * (4 : ℝ) ^ n
                  * (16 * D ^ 2 * B ^ (n + 1) * slicePhi α K u θ))
              = ((n : ℝ) + 1) ^ 2 * D ^ 2 * (4 : ℝ) ^ n * slicePhi α K u θ
                * (2 * (1 + 16 * B ^ (n + 1))) := by ring_nf
            _ ≤ ((n : ℝ) + 1) ^ 2 * D ^ 2 * (4 : ℝ) ^ n * slicePhi α K u θ
                * (34 * B ^ (n + 1)) := mul_le_mul_of_nonneg_left hcore hfac
            _ = 34 * ((n : ℝ) + 1) ^ 2 * D ^ 2 * (4 : ℝ) ^ n * B ^ (n + 1)
                * slicePhi α K u θ := by ring_nf
        have hlast : 34 * ((n : ℝ) + 1) ^ 2 * D ^ 2 * (4 : ℝ) ^ n * B ^ (n + 1)
              * slicePhi α K u θ ≤ B ^ (n + 2) * slicePhi α K u θ := by
          have hfac : 0 ≤ B ^ (n + 1) * slicePhi α K u θ :=
            mul_nonneg (pow_nonneg hB0 _) hP0θ
          have h := mul_le_mul_of_nonneg_right (hBstep n hnK) hfac
          calc 34 * ((n : ℝ) + 1) ^ 2 * D ^ 2 * (4 : ℝ) ^ n * B ^ (n + 1)
                * slicePhi α K u θ
              = (34 * ((n : ℝ) + 1) ^ 2 * D ^ 2 * (4 : ℝ) ^ n)
                * (B ^ (n + 1) * slicePhi α K u θ) := by ring
            _ ≤ B * (B ^ (n + 1) * slicePhi α K u θ) := h
            _ = B ^ (n + 2) * slicePhi α K u θ := by
                rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
                ring
        exact le_trans hstep (le_trans hbnd (le_trans hfinal1 hlast))
    refine ⟨hgoal1, ?_⟩
    intro i hi θ hθ
    have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
    have hiK : i ≤ K := (Finset.mem_Icc.mp hi).2
    calc (LopIter i u θ) ^ 2 * thGam α θ ≤ B ^ i * slicePhi α K u θ := key i hiK hi1 θ hθ
      _ ≤ B ^ K * slicePhi α K u θ :=
          mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hB1 hiK) (hP0 θ hθ)
      _ ≤ (B ^ K + (Real.pi / 2) ^ 3 + 1) * slicePhi α K u θ := by
          refine mul_le_mul_of_nonneg_right ?_ (hP0 θ hθ)
          have hpi : 0 < (Real.pi / 2) ^ 3 := by positivity
          linarith

end Work.FTS.EllipticEst.Blocks
