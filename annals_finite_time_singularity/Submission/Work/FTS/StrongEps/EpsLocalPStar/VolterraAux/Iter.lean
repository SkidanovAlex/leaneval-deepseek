import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.StrongEps.EpsSpace
import Submission.Work.FTS.Galerkin.Defs
import Submission.Work.FTS.StrongEps.EpsLocalPStar.VolterraAux.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn Fam slice)

namespace Work.FTS.StrongEps.EpsLocalPStar

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The Picard iteration and its limit -/

/-- The Picard iterates of the Volterra map `u ↦ h₀ + ∫₀^· F(u s) ds`. -/
def iter (F : Fn → Fn) (h₀ : Fn) : ℕ → Fam
  | 0 => fun z θ _ => h₀ z θ
  | n + 1 => fun z θ τ => h₀ z θ + ∫ s in (0 : ℝ)..τ, F (slice (iter F h₀ n) s) z θ

@[simp] theorem iter_zero (F : Fn → Fn) (h₀ : Fn) :
    iter F h₀ 0 = fun z θ _ => h₀ z θ := rfl

theorem iter_succ (F : Fn → Fn) (h₀ : Fn) (n : ℕ) :
    iter F h₀ (n + 1)
      = fun z θ τ => h₀ z θ + ∫ s in (0 : ℝ)..τ, F (slice (iter F h₀ n) s) z θ := rfl

/-- The `n`-th increment of the Picard iteration. -/
def wseq (F : Fn → Fn) (h₀ : Fn) (n : ℕ) (τ : ℝ) : Fn :=
  fun z θ => slice (iter F h₀ (n + 1)) τ z θ - slice (iter F h₀ n) τ z θ

/-- The limit family: the sum of the increments, starting from the *first* increment (the
`0`-th increment needs no size bound and is added separately). -/
def limFam (F : Fn → Fn) (h₀ : Fn) : Fam :=
  fun z θ τ => h₀ z θ + wseq F h₀ 0 τ z θ + ∑' n, wseq F h₀ (n + 1) τ z θ

theorem slice_iter_zero (F : Fn → Fn) (h₀ : Fn) (n : ℕ) (z θ : ℝ) :
    slice (iter F h₀ n) 0 z θ = h₀ z θ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show h₀ z θ + (∫ s in (0 : ℝ)..0, F (slice (iter F h₀ n) s) z θ) = h₀ z θ
    rw [intervalIntegral.integral_same, add_zero]

theorem wseq_zero (F : Fn → Fn) (h₀ : Fn) (n : ℕ) (z θ : ℝ) :
    wseq F h₀ n 0 z θ = 0 := by
  simp only [wseq, slice_iter_zero, sub_self]

theorem limFam_zero (F : Fn → Fn) (h₀ : Fn) (z θ : ℝ) : limFam F h₀ z θ 0 = h₀ z θ := by
  simp only [limFam, tsum_zero, add_zero, wseq_zero]

/-- The increments telescope to the difference of the iterates. -/
theorem sum_wseq (F : Fn → Fn) (h₀ : Fn) (N : ℕ) (τ z θ : ℝ) :
    ∑ n ∈ Finset.range N, wseq F h₀ n τ z θ
      = slice (iter F h₀ N) τ z θ - h₀ z θ := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [wseq, iter_zero]
    ring


/-- The shifted telescoping of the increments. -/
theorem sum_wseq_shift (F : Fn → Fn) (h₀ : Fn) (N : ℕ) (τ z θ : ℝ) :
    ∑ n ∈ Finset.range N, wseq F h₀ (n + 1) τ z θ
      = slice (iter F h₀ (N + 1)) τ z θ - h₀ z θ - wseq F h₀ 0 τ z θ := by
  have h := sum_wseq F h₀ (N + 1) τ z θ
  rw [Finset.sum_range_succ'] at h
  linarith [h]

/-- The limit of `F` along the Picard iterates. -/
def FlimM (F : Fn → Fn) (h₀ : Fn) (z θ τ : ℝ) : ℝ :=
  F h₀ z θ
    + ∑' n, (F (slice (iter F h₀ (n + 1)) τ) z θ - F (slice (iter F h₀ n) τ) z θ)

theorem sum_FlimM (F : Fn → Fn) (h₀ : Fn) (N : ℕ) (τ z θ : ℝ) :
    ∑ n ∈ Finset.range N,
        (F (slice (iter F h₀ (n + 1)) τ) z θ - F (slice (iter F h₀ n) τ) z θ)
      = F (slice (iter F h₀ N) τ) z θ - F h₀ z θ := by
  induction N with
  | zero =>
    have h : slice (iter F h₀ 0) τ = h₀ := rfl
    rw [h, sub_self]
    simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    ring


end Work.FTS.StrongEps.EpsLocalPStar
