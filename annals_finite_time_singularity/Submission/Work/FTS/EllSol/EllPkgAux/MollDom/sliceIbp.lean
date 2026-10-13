/-
# `Work.FTS.EllSol.EllPkgAux.MollDom.sliceIbp` — one-dimensional integration by parts
against the logarithmic mollifying kernel `sKer δ`.

For `0 < δ ≤ 1/2`, `f` differentiable everywhere with continuous derivative `f'`, and any
centre `σ`,

  `∫_ℝ (sKer δ)' (σ - t) · f t dt = ∫_ℝ sKer δ (σ - t) · f' t dt`.

Both integrands are supported in the compact window `(σ - 1, σ + 1]` (the kernel `sKer δ` and
its derivative vanish for `|u| ≥ δ` and `δ ≤ 1/2 ≤ 1`), so the two integrals over `ℝ` are the
ordinary interval integrals over `[σ - 1, σ + 1]`; there the statement is the usual integration
by parts `∫ u v' = u b · v b - u a · v a - ∫ u' v` applied to `u t = sKer δ (σ - t)`
(so `u' t = -((sKer δ)' (σ - t))`) and `v = f`.  The two boundary terms vanish because
`sKer δ (±1) = 0` (as `δ ≤ 1/2`).
-/
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Submission.Work.FTS.EllSol.PkgK5.K5c.MollDefs
import Submission.Work.FTS.EllSol.EllPkgAux.thMollTransfer2

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux.MollDom

/-- The derivative of the mollifying kernel `sKer ε` vanishes outside the support of `sKer ε`:
at a point `x` with `ε < |x|` the kernel is locally identically zero, hence so is its
derivative. -/
private theorem deriv_sKer_eq_zero_of_lt_abs {ε x : ℝ} (hε : 0 < ε) (hx : ε < |x|) :
    deriv (Work.FTS.EllSol.PkgK5.K5c.sKer ε) x = 0 := by
  have hev : Work.FTS.EllSol.PkgK5.K5c.sKer ε =ᶠ[nhds x] (fun _ : ℝ => (0 : ℝ)) := by
    rw [Filter.eventuallyEq_iff_exists_mem]
    rcases lt_abs.mp hx with h | h
    · exact ⟨Set.Ioi ε, isOpen_Ioi.mem_nhds h, fun y hy => by
        refine Work.FTS.EllSol.PkgK5.K5c.sKer_eq_zero_of_le_abs hε ?_
        have hy' : ε < y := hy
        rw [abs_of_pos (by linarith)]
        linarith⟩
    · exact ⟨Set.Iio (-ε), isOpen_Iio.mem_nhds (by simp only [Set.mem_Iio]; linarith),
        fun y hy => by
        refine Work.FTS.EllSol.PkgK5.K5c.sKer_eq_zero_of_le_abs hε ?_
        have hy' : y < -ε := hy
        rw [abs_of_neg (by linarith)]
        linarith⟩
  rw [hev.deriv_eq, deriv_const]

theorem sliceIbp {f f' : ℝ → ℝ} {δ σ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2)
    (hder : ∀ t : ℝ, HasDerivAt f (f' t) t) (hf'c : Continuous f') :
    ∫ t : ℝ, deriv (Work.FTS.EllSol.PkgK5.K5c.sKer δ) (σ - t) * f t
      = ∫ t : ℝ, Work.FTS.EllSol.PkgK5.K5c.sKer δ (σ - t) * f' t := by
  -- ## the integrands vanish off the window `(σ - 1, σ + 1]`, so the integrals over `ℝ` are the
  -- interval integrals over `[σ - 1, σ + 1]`
  have key_gl : ∀ g : ℝ → ℝ, (∀ t : ℝ, t ∉ Set.Ioc (σ - 1) (σ + 1) → g t = 0) →
      (∫ t : ℝ, g t) = ∫ t in (σ - 1)..(σ + 1), g t := by
    intro g hg
    rw [intervalIntegral.integral_of_le (show σ - 1 ≤ σ + 1 by linarith)]
    exact (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hg).symm
  have hlt : ∀ t : ℝ, t ∉ Set.Ioc (σ - 1) (σ + 1) → δ < |σ - t| := by
    intro t ht
    rw [Set.mem_Ioc, not_and_or] at ht
    rcases ht with h | h
    · rw [not_lt] at h
      rw [abs_of_pos (by linarith)]; linarith
    · rw [not_le] at h
      rw [abs_of_neg (by linarith)]; linarith
  have hvan_d : ∀ t : ℝ, t ∉ Set.Ioc (σ - 1) (σ + 1) →
      deriv (Work.FTS.EllSol.PkgK5.K5c.sKer δ) (σ - t) * f t = 0 := by
    intro t ht
    rw [deriv_sKer_eq_zero_of_lt_abs hδ (hlt t ht), zero_mul]
  have hvan_k : ∀ t : ℝ, t ∉ Set.Ioc (σ - 1) (σ + 1) →
      Work.FTS.EllSol.PkgK5.K5c.sKer δ (σ - t) * f' t = 0 := by
    intro t ht
    rw [Work.FTS.EllSol.PkgK5.K5c.sKer_eq_zero_of_le_abs hδ (le_of_lt (hlt t ht)), zero_mul]
  rw [key_gl _ hvan_d, key_gl _ hvan_k]
  -- ## integration by parts on the interval `[σ - 1, σ + 1]`
  have hu : ∀ x ∈ Set.uIcc (σ - 1) (σ + 1),
      HasDerivAt (fun t : ℝ => Work.FTS.EllSol.PkgK5.K5c.sKer δ (σ - t))
        (-(deriv (Work.FTS.EllSol.PkgK5.K5c.sKer δ) (σ - x))) x := by
    intro x _
    have h : HasDerivAt (Work.FTS.EllSol.PkgK5.K5c.sKer δ)
        (deriv (Work.FTS.EllSol.PkgK5.K5c.sKer δ) (σ - x)) (σ - x) :=
      ((Work.FTS.EllSol.EllPkgAux.contDiff_sKer δ (n := 1)).differentiable_one (σ - x)).hasDerivAt
    exact h.comp_const_sub σ x
  have hv : ∀ x ∈ Set.uIcc (σ - 1) (σ + 1), HasDerivAt f (f' x) x := fun x _ => hder x
  have hu' : IntervalIntegrable (fun t : ℝ => -(deriv (Work.FTS.EllSol.PkgK5.K5c.sKer δ) (σ - t)))
      volume (σ - 1) (σ + 1) :=
    ((((Work.FTS.EllSol.EllPkgAux.contDiff_sKer δ (n := 1)).continuous_deriv_one).comp
      (continuous_const.sub continuous_id)).neg).intervalIntegrable _ _
  have hv' : IntervalIntegrable f' volume (σ - 1) (σ + 1) := hf'c.intervalIntegrable _ _
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' hv'
  -- ## the two boundary terms vanish because `sKer δ (±1) = 0` (`δ ≤ 1/2`)
  have hb1 : Work.FTS.EllSol.PkgK5.K5c.sKer δ (σ - (σ + 1)) = 0 := by
    rw [show σ - (σ + 1) = -1 by ring]
    exact Work.FTS.EllSol.PkgK5.K5c.sKer_eq_zero_of_le_abs hδ (by rw [abs_neg, abs_one]; linarith)
  have hb2 : Work.FTS.EllSol.PkgK5.K5c.sKer δ (σ - (σ - 1)) = 0 := by
    rw [show σ - (σ - 1) = 1 by ring]
    exact Work.FTS.EllSol.PkgK5.K5c.sKer_eq_zero_of_le_abs hδ (by rw [abs_one]; linarith)
  rw [hb1, hb2] at h
  simp only [zero_mul, zero_sub, neg_zero] at h
  have hkey : (∫ x in (σ - 1)..(σ + 1), deriv (Work.FTS.EllSol.PkgK5.K5c.sKer δ) (σ - x) * f x)
      = -(∫ x in (σ - 1)..(σ + 1),
          (-(deriv (Work.FTS.EllSol.PkgK5.K5c.sKer δ) (σ - x))) * f x) := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    ring
  rw [hkey, h]

end Work.FTS.EllSol.EllPkgAux.MollDom
