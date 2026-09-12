import Mathlib
import Submission.Core.D3

/-!
# FaArcs: the `f_a` ↔ D3 dictionary (instantiation of the arc-sum bound)

GOAL (single statement to prove once the `f_a`-geometry exists): for circle
points `z_j` and weights `p_j ≥ 0` with `∑p_j = n ≥ 1`, and `a ∈ (1,2)` with
a uniform margin `‖f_a‖ ≤ c` (`c < 2`) on the circle, the circle mean is
nonnegative:

    (1/2π)·∫_0^{2π} log‖2 - f_a(e^{iθ})‖ dθ ≥ 0.

DICTIONARY between the D3 layer (proved: `per_arc_bound`, `arc_sum_bound`,
`arc_mean_nonneg`) and the `f_a`-arc geometry (to be built; see Plan.md
DESIGN NOTE 6):

  f_a(z) := a·∏_j (1 + z·conj z_j)^{p_j}     (z on the circle; f_a on the disk).

  (G1) JUMP POINTS: on the circle, `f_a` vanishes exactly at the m ≤ n
       points `-z_j` with `p_j > 0` (m := #{distinct such points}).  The
       circle minus these m points is a union of m open arcs.
  (G2) ARC COORDINATE: on each arc, `t := arg f_a` is a smooth function of
       the circle angle `θ` with `dt/dθ = n/2`; writing `r := n/2`, each
       arc corresponds to a `t`-interval of length `|I| = r·(arc length)`.
       Total: `∑_j |I_j| = r·2π = nπ`  (matches `arc_sum_bound`'s `htotal`).
  (G3) PHASE STRUCTURE: on an arc, `f_a = Φ(t)·e^{it}` with `Φ := |f_a|`,
       i.e. for `f(t) := f_a` expressed in the arc coordinate,
       `f t = ‖f t‖·E t`  (the `harg` hypothesis of `per_arc_bound`).
  (G4) UNIFORM MARGIN: `‖f_a‖ ≤ c < 2` on the circle  (this is the `hΦ`,
       `hc2` pair of `per_arc_bound`; `c` comes from `|f_a| ≤ a·M` in the
       KL proof with `a ∈ (1,2)` chosen so `a·M < 2`).
  (G5) UNIMODALITY: `q := Φ/2 = ‖f‖/2` is unimodal in the arc coordinate on
       each arc (log-concavity of `log|f_a|` in `θ`, affine in `t`).
  (G6) SUBSTITUTION (mechanical; below `affine_change`): the circle integral
       over an arc equals `(1/r)·∫` over the corresponding `t`-interval:
         ∫_{θ_j}^{θ_{j+1}} log‖2 - f_a(e^{iθ})‖ dθ
             = (1/r) · ∫_{I_j} log‖2 - f(t)‖ dt,   r := n/2.
  (G7) CHECK against `arc_sum_bound`/`arc_mean_nonneg`: with the per-arc
       bounds `∫_{I_j} log‖2 - f‖ ≥ (|I_j| - π)·log 2` (`per_arc_bound`),
       `arc_sum_bound` yields `∑_j ∫_{I_j} ≥ (n-m)·π·log 2`; multiplying by
       `1/r = 2/n ≥ 0` and using `m ≤ n` gives the circle mean ≥ 0.
       (The remaining equality to verify is exactly the substitution (G6)
       summed over arcs, plus `htotal := ∑_j |I_j| = n·π` from (G2).)

Currently proved in this module: `affine_change` (G6's engine, the affine
change-of-variables identity).  The `f_a`-geometry (G1)-(G5) is future work
(needs the Complex.log-based real-power machinery, the argument-slope
computation, and log-concavity of `log|f_a|`).
-/

noncomputable section

open scoped Real Complex
open Complex
open MeasureTheory
open Interval

namespace Submission.Core

/-- **Affine change of variables** (engine of the per-arc substitution G6):
for `0 < r` and `g` continuous on the target interval,
`∫_t (r·a+c)..(r·b+c) g = r · ∫_θ a..b g(r·θ + c)`. -/
theorem affine_change (a b c : ℝ) {r : ℝ} (hr : 0 < r) (g : ℝ → ℝ)
    (_hg : ContinuousOn g (Set.uIcc (r * a + c) (r * b + c))) :
    (∫ t in (r * a + c)..(r * b + c), g t) =
      r * (∫ θ in a..b, g (r * θ + c)) := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  rw [intervalIntegral.integral_comp_mul_add (f := g) hr0 c]
  simp only [smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hr0, one_mul]

end Submission.Core

end
