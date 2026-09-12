import Mathlib
import Submission.Core.D2

/-!
# D3: from the per-arc bound (R2) to the circle mean `∫ log|2-f_a| ≥ 0`

CONTEXT (Plan.md DESIGN NOTE 5, R4/D3): on the circle, `f_a(z) = a·∏(1+z z̄_j)^{p_j}`
(weights `p_j ≥ 0`, `∑p_j = n ≥ 1`) vanishes exactly at the m ≤ n jump
points (the antipodes `-z_j`, `p_j > 0`).  The circle minus these points is a
union of m open arcs.  On each arc, in the coordinate `t := arg f_a` (with
`dt/dθ = n/2`), the function equals `Φ(t)·e^{it}` with `Φ := |f_a|` and
`q := Φ/2` UNIMODAL in `t`, so the single-arc bound
(`Submission.Core.D2.unimodal_bound`, R2) gives, on the arc's `t`-interval
`I_j`:

    ∫_{I_j} log‖2 - f_a‖ dt ≥ (|I_j| - π)·log 2.

Summing over the m arcs (Σ_j |I_j| = nπ because `dt/dθ = n/2` and the arcs
partition the circle):

    Σ_j ∫_{I_j} log‖2 - f_a‖ dt ≥ (n - m)·π·log 2 ≥ 0,

i.e. the mean of `log|2 - f_a|` over the circle is nonnegative (step D3).

## Lemmas

(1) `per_arc_bound` (THE ANALYTIC CORE of D3; below as a precise skeleton):
    from `unimodal_bound` (R2) for `q := ‖f‖/2`, plus the pointwise
    structure `f t = ‖f t‖ · e^{it}` and `‖f‖ ≤ 2`, derive the Φ-form bound
    `∫_a^b log‖2 - f t‖ ≥ (b - a - π)·log 2` for any interval `[a,b]`.
    [Proof route: `log‖2 - f‖ = log 2 + log‖1 - q·e^{it}‖` a.e. on `[a,b]`
    (off the finitely many points where `q(t)=1` and `e^{it}=1`), apply
    `unimodal_bound`, and integrate the constant `log 2` over `[a,b]`.]
(2) `arc_sum_bound` (PROVED BELOW): pure summation: if finitely many
    intervals `[u_j, v_j]` (j : Fin m) satisfy the per-arc bound and
    `∑(v_j - u_j) = n·π` with `m ≤ n`, then
    `∑_j ∫_{u_j}^{v_j} ≥ (n-m)·π·log 2`.
    [Arithmetic only; the log-2 factors and interval lengths telescope.]
(3) [future, f_a-specific, NOT formalized yet] the geometric facts that
    instantiate (1)+(2): f_a has exactly m ≤ n jump points; dt/dθ = n/2 on
    each arc; the arcs' t-intervals partition a length-`nπ` interval;
    q = |f_a|/2 is continuous and unimodal on each arc; f_a = Φ·e^{it}.
    These need the full `f_a`-machinery (Complex.log-based real powers,
    argument slope computation, log-concavity).  When proved they plug into
    `arc_mean_nonneg` below.

(4) `arc_mean_nonneg` (SKELETON; the D3 target): with the circle parametrized
    so that the m arcs correspond to t-intervals `[u_j, v_j]` partitioning
    `[0, n·π]` and `g(t) := log‖2 - f(t)‖` on the arc data, the conclusion
    is `0 ≤ ∫ over the circle of g`, stated here abstractly as
    `0 ≤ (n - m)·π·log 2 ≤ Σ_j ∫_{u_j}^{v_j} g` — i.e. once (1)-(3) hold,
    the sum of per-arc integrals is ≥ 0.  (The circle-integral form
    `(1/2π)∫_0^{2π} log|2-f_a(e^{iθ})| ≥ 0` follows by the change of
    variables `dθ = (2/n)dt`; kept for the f_a instantiation.)
-/

noncomputable section

open scoped Real Complex
open Complex
open MeasureTheory
open Interval

namespace Submission.Core

/-- **Per-arc bound (instantiation of R2).**  On an interval `[a,b]` where
`f` is continuous, `f t = ‖f t‖·e^{it}`, `‖f‖ ≤ c` for a `c < 2` (a uniform
margin: in the application `‖f_a‖ ≤ aM < 2`), and `q := ‖f‖/2` is unimodal,
`∫_a^b log‖2 - f t‖ ≥ (b - a - π)·log 2`.

The margin `c < 2` is essential: it makes `‖2 - f‖ ≥ 2 - c > 0` everywhere,
so `log‖2 - f‖ = log 2 + log‖1 - q·e^{it}‖` holds pointwise (no log-0
convention issues) and the integrand is continuous on `[a,b]`. -/
theorem per_arc_bound (a b : ℝ) (f : ℝ → ℂ) {c : ℝ}
    (hle : a ≤ b)
    (hfc : ContinuousOn f (Set.Icc a b))
    (harg : ∀ t ∈ Set.Icc a b, f t = ‖f t‖ * E t)
    (hΦ : ∀ t ∈ Set.Icc a b, ‖f t‖ ≤ c)
    (hc2 : c < 2)
    (hu : ∃ m : ℝ, UnimodalOn a b m (fun t : ℝ => ‖f t‖ / 2)) :
    (∫ t in a..b, Real.log ‖(2 : ℂ) - f t‖)
      ≥ (b - a - Real.pi) * Real.log 2 := by
  classical
  let q : ℝ → ℝ := fun t => ‖f t‖ / 2
  have hqcont : ContinuousOn q (Set.Icc a b) := by
    dsimp [q]
    exact (ContinuousOn.norm hfc).div_const 2
  have hq0 : ∀ t : ℝ, a ≤ t → t ≤ b → 0 ≤ q t := by
    intro t hta htb
    dsimp [q]
    positivity
  have hq1 : ∀ t : ℝ, a ≤ t → t ≤ b → q t ≤ 1 := by
    intro t hta htb
    dsimp [q]
    have hle2 : ‖f t‖ ≤ c := hΦ t (by exact ⟨hta, htb⟩)
    nlinarith
  -- R2 applied to q := ‖f‖/2
  have hR : (∫ t in a..b, Real.log ‖(1 : ℂ) - (q t : ℂ) * E t‖)
      ≥ -Real.pi * Real.log 2 := by
    exact unimodal_bound a b q hle hqcont hu hq0 hq1
  -- the margin gives positivity everywhere on [a,b]
  have hxeq : ∀ t ∈ Set.Icc a b,
      ‖(2 : ℂ) - f t‖ = 2 * ‖(1 : ℂ) - (q t : ℂ) * E t‖ := by
    intro t ht
    have hlin : (2 : ℂ) - f t = (2 : ℂ) * ((1 : ℂ) - (q t : ℂ) * E t) := by
      rw [harg t ht]
      dsimp [q]
      norm_num
      ring_nf
    rw [hlin, norm_mul]
    norm_num
  have hposL : ∀ t ∈ Set.Icc a b, 0 < ‖(2 : ℂ) - f t‖ := by
    intro t ht
    have hn : ‖(2 : ℂ)‖ ≤ ‖(2 : ℂ) - f t‖ + ‖f t‖ := by
      have := norm_add_le (a := (2 : ℂ) - f t) (b := f t)
      simpa using this
    have hle2 : ‖f t‖ ≤ c := hΦ t ht
    have h2c : 0 < 2 - c := sub_pos.mpr hc2
    have h2n : ‖(2 : ℂ)‖ = 2 := by norm_num
    nlinarith [h2n]
  have hpos : ∀ t ∈ Set.Icc a b, 0 < ‖(1 : ℂ) - (q t : ℂ) * E t‖ := by
    intro t ht
    have hx := hxeq t ht
    have hl := hposL t ht
    nlinarith
  -- pointwise identity
  have hident : ∀ t ∈ Set.Icc a b,
      Real.log ‖(2 : ℂ) - f t‖ =
        Real.log 2 + Real.log ‖(1 : ℂ) - (q t : ℂ) * E t‖ := by
    intro t ht
    calc
      Real.log ‖(2 : ℂ) - f t‖
          = Real.log (2 * ‖(1 : ℂ) - (q t : ℂ) * E t‖) := by rw [hxeq t ht]
      _ = Real.log 2 + Real.log ‖(1 : ℂ) - (q t : ℂ) * E t‖ := by
          rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt (hpos t ht))]
  -- convert the integral of the ‖·‖-form to the log2 + M form
  have hEq : (∫ t in a..b, Real.log ‖(2 : ℂ) - f t‖) =
      (∫ t in a..b, Real.log 2 + Real.log ‖(1 : ℂ) - (q t : ℂ) * E t‖) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have htI : t ∈ Set.Icc a b := by
      simpa [Set.uIcc_of_le hle] using ht
    exact hident t htI
  -- split the constant
  have hM : IntervalIntegrable (fun t : ℝ => Real.log ‖(1 : ℂ) - (q t : ℂ) * E t‖) volume a b := by
    have hnormcont : ContinuousOn (fun t : ℝ => ‖(1 : ℂ) - (q t : ℂ) * E t‖) (Set.uIcc a b) := by
      have hgcont : ContinuousOn (fun t : ℝ => (1 : ℂ) - (q t : ℂ) * E t) (Set.Icc a b) := by
        fun_prop
      have hn : ContinuousOn (fun t : ℝ => ‖(1 : ℂ) - (q t : ℂ) * E t‖) (Set.Icc a b) := hgcont.norm
      simpa [Set.uIcc_of_le hle] using hn
    have hposM : ∀ x ∈ Set.uIcc a b, ‖(1 : ℂ) - (q x : ℂ) * E x‖ ≠ 0 := by
      intro x hx
      have hxI : x ∈ Set.Icc a b := by simpa [Set.uIcc_of_le hle] using hx
      exact ne_of_gt (hpos x hxI)
    exact IntervalIntegrable.log hnormcont hposM
  have hsplit : (∫ t in a..b, Real.log 2 + Real.log ‖(1 : ℂ) - (q t : ℂ) * E t‖) =
      (b - a) * Real.log 2 + (∫ t in a..b, Real.log ‖(1 : ℂ) - (q t : ℂ) * E t‖) := by
    have hcst : IntervalIntegrable (fun _ : ℝ => Real.log 2) volume a b := by
      exact intervalIntegrable_const (a := a) (b := b) (μ := volume) (c := Real.log 2)
    rw [intervalIntegral.integral_add hcst hM]
    rw [intervalIntegral.integral_const]
    simp
  -- final arithmetic
  have hfin : (b - a) * Real.log 2 + (∫ t in a..b,
        Real.log ‖(1 : ℂ) - (q t : ℂ) * E t‖)
      ≥ (b - a - Real.pi) * Real.log 2 := by
    nlinarith [hR]
  rw [hEq, hsplit]
  exact hfin

/-- **Arc-sum bound (pure summation of per-arc bounds).**  If the
`m ≤ n` intervals `[u_j, v_j]` have total length `n·π` and each carries the
per-arc bound for the integrand `g`, then
`Σ_j ∫_{u_j}^{v_j} g ≥ (n - m)·π·log 2`. -/
theorem arc_sum_bound {m n : ℕ} (hm : m ≤ n) (u v : Fin m → ℝ) (g : ℝ → ℝ)
    (hle : ∀ j : Fin m, u j ≤ v j)
    (htotal : (∑ j : Fin m, (v j - u j)) = (n : ℝ) * Real.pi)
    (harc : ∀ j : Fin m,
      (∫ t in u j..v j, g t) ≥ ((v j - u j) - Real.pi) * Real.log 2) :
    (∑ j : Fin m, ∫ t in u j..v j, g t)
      ≥ ((n : ℝ) - (m : ℝ)) * Real.pi * Real.log 2 := by
  have hsum : (∑ j : Fin m, (∫ t in u j..v j, g t)) ≥
      ∑ j : Fin m, (((v j - u j) - Real.pi) * Real.log 2) := by
    exact Finset.sum_le_sum (fun j hj => harc j)
  have hlen : (∑ j : Fin m, ((v j - u j) - Real.pi)) = ((n : ℝ) - (m : ℝ)) * Real.pi := by
    rw [Finset.sum_sub_distrib]
    have hsumlen : (∑ j : Fin m, (v j - u j)) = (n : ℝ) * Real.pi := htotal
    have hsumc : (∑ j : Fin m, (Real.pi : ℝ)) = (m : ℝ) * Real.pi := by
      simp
    rw [hsumlen, hsumc]
    ring
  have hsum2 : (∑ j : Fin m, (((v j - u j) - Real.pi) * Real.log 2)) =
      ((n : ℝ) - (m : ℝ)) * Real.pi * Real.log 2 := by
    rw [← Finset.sum_mul]
    rw [hlen]
  have hgoal : (∑ j : Fin m, ∫ t in u j..v j, g t) ≥
      ((n : ℝ) - (m : ℝ)) * Real.pi * Real.log 2 := by
    rw [hsum2] at hsum
    exact hsum
  exact hgoal

/-- **D3 target (skeleton).**  Once the `f_a`-geometry (arcs, `dt/dθ = n/2`,
unimodality of `|f_a|/2`) is available, this is the assembled conclusion:
the sum of the per-arc integrals is ≥ 0.  (The circle-mean form follows by
the substitution `dθ = (2/n)dt`.) -/
theorem arc_mean_nonneg {m n : ℕ} (hm : m ≤ n) (u v : Fin m → ℝ) (g : ℝ → ℝ)
    (hle : ∀ j : Fin m, u j ≤ v j)
    (htotal : (∑ j : Fin m, (v j - u j)) = (n : ℝ) * Real.pi)
    (harc : ∀ j : Fin m,
      (∫ t in u j..v j, g t) ≥ ((v j - u j) - Real.pi) * Real.log 2) :
    0 ≤ (∑ j : Fin m, ∫ t in u j..v j, g t) := by
  have hb := arc_sum_bound hm u v g hle htotal harc
  have hnm : 0 ≤ (n : ℝ) - (m : ℝ) := sub_nonneg.mpr (Nat.cast_le.mpr hm)
  have hpos : 0 ≤ ((n : ℝ) - (m : ℝ)) * Real.pi * Real.log 2 := by
    positivity
  linarith

end Submission.Core

end
