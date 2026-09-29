import Mathlib
import Submission.Work.GenShared.periods_defs
import Submission.Work.GenShared.rreg_Dv
import Submission.Work.GenShared.hasDerivAt_rval
import Submission.Work.GenShared.riccati_aux
import Submission.Work.GenShared.ratfunc_zero_open
import Submission.Work.GenShared.hasDerivAt_deriv_div
import Submission.Work.GenShared.exists_good_point

/-!
# `Work.GenShared.riccati_core` — the Riccati obstruction to a rational relation

Let `y1` be a nonzero holomorphic solution, on a disc `ball x0 δ`, of the order-two equation
`p₂ y'' + p₁ y' + p₀ y = 0` with `p₂` nonvanishing there, and suppose the associated Riccati
equation `p₂(u' + u²) + p₁ u + p₀ = 0` has **no** solution `u ∈ ℂ(x)`.

Then the `ℂ(x)`-span of `y1, y1'` meets the kernel of evaluation at the origin only in `0`: any
rational relation `a·y1 + b·y1' ≡ 0` on the disc (valid where `a`, `b` are regular) forces
`a = b = 0`.

**Proof.**  If `b = 0` then `a·y1 ≡ 0` on a nonempty open set of points where `a` is regular and
`y1` does not vanish; since the value function of the rational `a` is rational, it is zero
(`ratfunc_zero_open`).

If `b ≠ 0`, put `u := -(a.num·b.denom)/(a.denom·b.num) ∈ ℂ(x)` — the rational function `-a/b` in
canonical form.  By `exists_good_point` there is a point `z` of the disc at which `y1 z ≠ 0`, `a`,
`b` are regular and `b.num` does not vanish; at such a point the relation gives
`Rval (a) z / Rval b z = -y1'z/y1 z`, i.e. `Rval u z = y1'z/y1 z`; the same computation holds
eventually near `z`, so `Rval (dRat u) z`, the derivative of `Rval u` (`hasDerivAt_rval`), equals
the derivative of the logarithmic derivative `y1'/y1`, which is `y1''/y1 - (y1'/y1)²`
(`hasDerivAt_deriv_div`).  Hence the Riccati expression `p₂(u' + u²) + p₁ u + p₀` of the rational
function `u` evaluates to `(p₂ y1'' + p₁ y1' + p₀ y1)/y1 = 0` on a nonempty open set, so it is zero
by `ratfunc_zero_open` — contradicting the hypothesis on `u`.
-/

namespace Work.GenShared

open Complex Metric Work.GenShared Filter
open scoped Topology
open Submission.CDT (dRat)

/-- The value at a "good" point of the rational function `-(a·b⁻¹)` written with canonical
numerators/denominators: it is `y1'/y1` for any solution relation `a·y1 + b·y1' = 0`. -/
lemma rval_neg_mul_inv_apply {a b : RatFunc ℂ} {y1 : ℂ → ℂ} {x0 : ℂ} {δ : ℝ}
    (hrel : ∀ z ∈ ball x0 δ, Rreg a z → Rreg b z →
      Rval a z * y1 z + Rval b z * deriv y1 z = 0)
    {z : ℂ} (hz : z ∈ ball x0 δ) (hra : Rreg a z) (hrb : Rreg b z)
    (hbn : b.num.eval z ≠ 0) (hyz : y1 z ≠ 0) :
    Rval (algebraMap (Polynomial ℂ) (RatFunc ℂ) (-(a.num * b.denom))
          / algebraMap (Polynomial ℂ) (RatFunc ℂ) (a.denom * b.num)) z
      = deriv y1 z / y1 z := by
  have hra' : a.denom.eval z ≠ 0 := hra
  have hrb' : b.denom.eval z ≠ 0 := hrb
  have hq : (a.denom * b.num).eval z ≠ 0 := by
    rw [Polynomial.eval_mul]; exact mul_ne_zero hra' hbn
  rw [Rval_div _ _ z hq]
  simp only [Polynomial.eval_neg, Polynomial.eval_mul]
  rw [div_eq_div_iff (mul_ne_zero hra' hbn) hyz]
  have hh : a.num.eval z * y1 z * b.denom.eval z
      + a.denom.eval z * b.num.eval z * deriv y1 z = 0 := by
    have h := hrel z hz hra hrb
    rw [Rval, Rval] at h
    field_simp at h
    rw [mul_zero] at h
    exact h
  linear_combination -hh

theorem riccati_core {k : ℕ} (p2 p1 p0 : Polynomial ℂ) (hp2 : p2 ≠ 0)
    (hric : ∀ u : RatFunc ℂ,
      algebraMap (Polynomial ℂ) (RatFunc ℂ) p2 * (dRat u + u ^ 2)
        + algebraMap (Polynomial ℂ) (RatFunc ℂ) p1 * u
        + algebraMap (Polynomial ℂ) (RatFunc ℂ) p0 ≠ 0)
    (x0 : ℂ) {δ : ℝ} (hδ : 0 < δ)
    (hp2ne : ∀ z ∈ ball x0 δ, p2.eval z ≠ 0)
    (y1 : ℂ → ℂ) (hy1d : DifferentiableOn ℂ y1 (ball x0 δ))
    (hy1ne : ∃ z ∈ ball x0 δ, y1 z ≠ 0)
    (hode : ∀ z ∈ ball x0 δ,
      p2.eval z * deriv (deriv y1) z + p1.eval z * deriv y1 z + p0.eval z * y1 z = 0)
    (a b : RatFunc ℂ)
    (hrel : ∀ z ∈ ball x0 δ, Rreg a z → Rreg b z →
      Rval a z * y1 z + Rval b z * deriv y1 z = 0) :
    a = 0 ∧ b = 0 := by
  by_cases hb : b = 0
  · subst hb
    refine ⟨?_, rfl⟩
    have hUo : IsOpen (ball x0 δ ∩ {z : ℂ | y1 z ≠ 0}) := by
      rw [isOpen_iff_mem_nhds]
      rintro z ⟨hzb, hyz⟩
      have h1 : ∀ᶠ t in 𝓝 z, t ∈ ball x0 δ := IsOpen.mem_nhds isOpen_ball hzb
      have h2 : ∀ᶠ t in 𝓝 z, y1 t ≠ 0 :=
        (ContinuousOn.continuousAt hy1d.continuousOn
          (IsOpen.mem_nhds isOpen_ball hzb)).eventually_ne hyz
      exact h1.and h2
    have hUne : (ball x0 δ ∩ {z : ℂ | y1 z ≠ 0}).Nonempty := hy1ne
    refine ratfunc_zero_open hUo hUne ?_
    rintro z ⟨hzb, hyz⟩ hra
    have hreg0 : Rreg (0 : RatFunc ℂ) z := by simp [Rreg]
    have h0 := hrel z hzb hra hreg0
    have hRval0 : Rval (0 : RatFunc ℂ) z = 0 := by simp [Rval]
    rw [hRval0, zero_mul, add_zero] at h0
    exact (mul_eq_zero.mp h0).resolve_right hyz
  · set u : RatFunc ℂ := algebraMap (Polynomial ℂ) (RatFunc ℂ) (-(a.num * b.denom))
        / algebraMap (Polynomial ℂ) (RatFunc ℂ) (a.denom * b.num) with hu
    set U : Set ℂ := {z | z ∈ ball x0 δ ∧ a.denom.eval z ≠ 0 ∧ b.denom.eval z ≠ 0
        ∧ b.num.eval z ≠ 0 ∧ y1 z ≠ 0} with hU
    have hcont : ∀ z ∈ ball x0 δ, ContinuousAt y1 z := fun z hz =>
      ContinuousOn.continuousAt hy1d.continuousOn (IsOpen.mem_nhds isOpen_ball hz)
    have hUo : IsOpen U := by
      rw [isOpen_iff_mem_nhds]
      rintro z ⟨hzb, hra, hrb, hbn, hyz⟩
      have h1 : ∀ᶠ t in 𝓝 z, t ∈ ball x0 δ := IsOpen.mem_nhds isOpen_ball hzb
      have h2 : ∀ᶠ t in 𝓝 z, a.denom.eval t ≠ 0 :=
        a.denom.continuous.continuousAt.eventually_ne hra
      have h3 : ∀ᶠ t in 𝓝 z, b.denom.eval t ≠ 0 :=
        b.denom.continuous.continuousAt.eventually_ne hrb
      have h4 : ∀ᶠ t in 𝓝 z, b.num.eval t ≠ 0 :=
        b.num.continuous.continuousAt.eventually_ne hbn
      have h5 : ∀ᶠ t in 𝓝 z, y1 t ≠ 0 := (hcont z hzb).eventually_ne hyz
      exact h1.and (h2.and (h3.and (h4.and h5)))
    have hUne : U.Nonempty := by
      obtain ⟨z, hz, hyz, hra, hrb, hbn⟩ := exists_good_point hy1d hy1ne hb
      exact ⟨z, hz, hra, hrb, hbn, hyz⟩
    have hkey : algebraMap (Polynomial ℂ) (RatFunc ℂ) p2 * (dRat u + u ^ 2)
        + algebraMap (Polynomial ℂ) (RatFunc ℂ) p1 * u
        + algebraMap (Polynomial ℂ) (RatFunc ℂ) p0 = 0 := by
      refine ratfunc_zero_open hUo hUne ?_
      rintro z ⟨hzb, hra, hrb, hbn, hyz⟩ _
      have hra' : a.denom.eval z ≠ 0 := hra
      have hq : (a.denom * b.num).eval z ≠ 0 := by
        rw [Polynomial.eval_mul]; exact mul_ne_zero hra' hbn
      have hreg_u : Rreg u z := by rw [hu]; exact rreg_div_poly hq
      have hreg_du : Rreg (dRat u) z := rreg_dRat hreg_u
      have hreg_u2 : Rreg (u ^ 2) z := by rw [pow_two]; exact rreg_mul hreg_u hreg_u
      have hreg_sum1 : Rreg (dRat u + u ^ 2) z := rreg_add hreg_du hreg_u2
      have hreg_p1 : Rreg (algebraMap (Polynomial ℂ) (RatFunc ℂ) p1) z := rreg_algMap p1 z
      have hreg_p2 : Rreg (algebraMap (Polynomial ℂ) (RatFunc ℂ) p2) z := rreg_algMap p2 z
      have hreg_p0 : Rreg (algebraMap (Polynomial ℂ) (RatFunc ℂ) p0) z := rreg_algMap p0 z
      have hreg_A : Rreg (algebraMap (Polynomial ℂ) (RatFunc ℂ) p2 * (dRat u + u ^ 2)) z :=
        rreg_mul hreg_p2 hreg_sum1
      have hreg_B : Rreg (algebraMap (Polynomial ℂ) (RatFunc ℂ) p1 * u) z := rreg_mul hreg_p1 hreg_u
      have hreg_AB : Rreg (algebraMap (Polynomial ℂ) (RatFunc ℂ) p2 * (dRat u + u ^ 2)
          + algebraMap (Polynomial ℂ) (RatFunc ℂ) p1 * u) z := rreg_add hreg_A hreg_B
      have hu_z : Rval u z = deriv y1 z / y1 z := by
        rw [hu]; exact rval_neg_mul_inv_apply hrel hzb hra hrb hbn hyz
      have hu_ev : (fun t => Rval u t) =ᶠ[𝓝 z] (fun t => deriv y1 t / y1 t) := by
        have h1 : ∀ᶠ t in 𝓝 z, t ∈ ball x0 δ := IsOpen.mem_nhds isOpen_ball hzb
        have h2 : ∀ᶠ t in 𝓝 z, Rreg a t := by
          simpa [Rreg] using a.denom.continuous.continuousAt.eventually_ne hra'
        have h3 : ∀ᶠ t in 𝓝 z, Rreg b t := by
          simpa [Rreg] using b.denom.continuous.continuousAt.eventually_ne hrb
        have h4 : ∀ᶠ t in 𝓝 z, b.num.eval t ≠ 0 :=
          b.num.continuous.continuousAt.eventually_ne hbn
        have h5 : ∀ᶠ t in 𝓝 z, y1 t ≠ 0 := (hcont z hzb).eventually_ne hyz
        filter_upwards [h1, h2, h3, h4, h5] with t htball hta htb htn htyn
        rw [hu]
        exact rval_neg_mul_inv_apply hrel htball hta htb htn htyn
      have hdu_z : Rval (dRat u) z = deriv (deriv y1) z / y1 z - (deriv y1 z / y1 z) ^ 2 := by
        have h1 : HasDerivAt (fun t => Rval u t) (Rval (dRat u) z) z :=
          hasDerivAt_rval u z hreg_u
        have h2 : deriv (fun t => Rval u t) z = Rval (dRat u) z := h1.deriv
        have h3 : deriv (fun t => Rval u t) z = deriv (fun t => deriv y1 t / y1 t) z :=
          Filter.EventuallyEq.deriv_eq hu_ev
        rw [← h2, h3]
        exact (hasDerivAt_deriv_div hy1d hzb hyz).deriv
      have hexp : Rval (algebraMap (Polynomial ℂ) (RatFunc ℂ) p2 * (dRat u + u ^ 2)
            + algebraMap (Polynomial ℂ) (RatFunc ℂ) p1 * u
            + algebraMap (Polynomial ℂ) (RatFunc ℂ) p0) z
          = p2.eval z * (Rval (dRat u) z + Rval u z ^ 2) + p1.eval z * Rval u z + p0.eval z := by
        rw [rval_add hreg_AB hreg_p0, rval_add hreg_A hreg_B,
            rval_mul hreg_p2 hreg_sum1, rval_mul hreg_p1 hreg_u,
            rval_add hreg_du hreg_u2, pow_two, rval_mul hreg_u hreg_u,
            rval_algMap, rval_algMap, rval_algMap]
        ring
      rw [hexp, hdu_z, hu_z]
      have hfin : p2.eval z * (deriv (deriv y1) z / y1 z - (deriv y1 z / y1 z) ^ 2
            + (deriv y1 z / y1 z) ^ 2) + p1.eval z * (deriv y1 z / y1 z) + p0.eval z
          = (p2.eval z * deriv (deriv y1) z + p1.eval z * deriv y1 z
              + p0.eval z * y1 z) / y1 z := by
        field_simp
        ring
      rw [hfin, hode z hzb, zero_div]
    exact absurd hkey (hric u)

end Work.GenShared
