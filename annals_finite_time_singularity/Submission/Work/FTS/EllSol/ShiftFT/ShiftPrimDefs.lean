/-
Copyright: work module for the Elgindi finite-time singularity project (area `FTS.EllSol`).

# The truncation construction for `shiftedFlat_of_nice`

`Work.FTS.EllSol.ShiftedFlatAux` is the *shifted* Agmon statement: for the operator
`L_b u = ∂_t u - b·u` one has, on the strip `ℝ × (0,π/2)`, for `C²` data with vanishing
endpoint values and the three shifted slots integrable,

`∫∫ (∂_θ L_b u)² σ_a ≤ C (∫∫ (L_b u)² σ_η + √(∫∫ (L_b² u)² σ_η · ∫∫ (u_{θθ})² σ_η))`.

`Work.FTS.EllSol.ShiftFT.shiftedFlat_of_nice` is the passage from the *nice* case (data of
uniformly compact support in `t`, hypothesis `hNice`) to the general case.  The naive
truncation `u ↦ chi N · u` of the general case fails: the operator `L_b` has the kernel
`{e^{bt}A(θ)}` (the `b`-harmonic modes), and truncating such a mode produces an error
`(chi N)'·u` which is *not* controlled by the three integrable slots.

The construction used here instead truncates the *junk-free* quantity `v = L_b u` and
solves the ODE exactly.  Two mirror-image particular solutions are used:

* `Gc` (`b ≥ 0`): the *backward* solution, the improper integral `∫_t^∞ e^{-bs} v_N ds`,
  compactly supported on the right and with the exponentially decaying (as `t → -∞`)
  tail `e^{bt}C(θ)`;
* `GcFwd` (`b ≤ 0`): the *forward* solution `∫_{-∞}^t e^{-bs} v_N ds`, compactly supported
  on the left and with the decreasing tail `-e^{bt}C(θ)` as `t → +∞`.

Both are written as manifestly differentiable expressions, using the integration by parts
`∫ e^{-bs} chi N ∂_s(e^{-bs}u)` which rewrites the primitive in terms of `u` itself:

`Gc = chi N · u + e^{bt} ∫_t^{2N} e^{-bs} (chi N)'(s) u(s,θ) ds`
`GcFwd = chi N · u - e^{bt} ∫_{-2N}^{t} e^{-bs} (chi N)'(s) u(s,θ) ds`

(valid because `(chi N)'` is supported in `[-2N,2N]`).  The exponentially small tail is then
cut off by `phiTr N = chi (4096·N)`, whose transition region lies where the exponential is
tiny; the large constant `4096` makes the cutoff error small compared with the slot being
truncated (the relevant constant is `2·(sup|deriv tk|)²/4096 ≤ 2·32/4096 = 1/64 < 1/4`).
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllSol.Trunc.Defs
import Submission.Work.FTS.EllSol.FlatFT.Defs
import Submission.Work.FTS.EllSol.shiftReduceDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.ShiftFT

open MeasureTheory Set
open scoped Real Topology

noncomputable section

set_option autoImplicit false

/-- The shifted operator `L_b u = ∂_t u - b·u`. -/
def sh (b : ℝ) (u : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun t θ => Work.Spaces.pz u t θ - b * u t θ

/-- Iterated shifted operator `L_b^{n} u`. -/
def shIter : ℕ → ℝ → (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ)
  | 0, _, u => u
  | n + 1, b, u => sh b (shIter n b u)

@[simp] theorem shIter_zero (b : ℝ) (u : ℝ → ℝ → ℝ) : shIter 0 b u = u := rfl
@[simp] theorem shIter_succ (n : ℕ) (b : ℝ) (u : ℝ → ℝ → ℝ) :
    shIter (n + 1) b u = sh b (shIter n b u) := rfl

/-- The cutoff `v ↦ chi N · v` of the junk-free quantity. -/
def vTr (N b : ℝ) (u : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun t θ =>
  Work.FTS.EllSol.Trunc.chi N t * sh b u t θ

/-- The backward particular solution of `L_b G = chi N · v` (`v = L_b u`), used for `b ≥ 0`.
It is the interval integral of `e^{-bs}(chi N)'·u` over `s ∈ [t, 2N]`, which agrees with the
improper integral `∫_t^∞ e^{-bs}(chi N)'·u ds` because `(chi N)'` is supported in `[-2N,2N]`. -/
def Gc (N b : ℝ) (u : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun t θ =>
  Work.FTS.EllSol.Trunc.chi N t * u t θ
    + Real.exp (b * t)
        * ∫ s in t..(2 * N),
            Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s * u s θ

/-- The forward particular solution of `L_b G = chi N · v`, used for `b ≤ 0`. -/
def GcFwd (N b : ℝ) (u : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun t θ =>
  Work.FTS.EllSol.Trunc.chi N t * u t θ
    - Real.exp (b * t)
        * ∫ s in (-(2 * N))..t,
            Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s * u s θ

/-- The `t`-cutoff killing the exponentially small tail: `chi (4096·N)`. -/
def phiTr (N : ℝ) (t : ℝ) : ℝ := Work.FTS.EllSol.Trunc.chi (4096 * N) t

/-- The truncated data (backward solution): `u_N = phiTr N · G_N`. -/
def uTr (N b : ℝ) (u : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun t θ => phiTr N t * Gc N b u t θ

/-- The truncated data (forward solution). -/
def uTrFwd (N b : ℝ) (u : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun t θ =>
  phiTr N t * GcFwd N b u t θ

/-! ## Elementary facts about the cutoffs -/

theorem phiTr_eq_chi (N t : ℝ) : phiTr N t = Work.FTS.EllSol.Trunc.chi (4096 * N) t := rfl

theorem phiTr_contDiff (n : ℕ) (N : ℝ) : ContDiff ℝ n (phiTr N) :=
  Work.FTS.EllSol.Trunc.chi_contDiff n (4096 * N)

theorem phiTr_nonneg (N t : ℝ) : 0 ≤ phiTr N t := Work.FTS.EllSol.Trunc.chi_nonneg _ _

theorem phiTr_le_one (N t : ℝ) : phiTr N t ≤ 1 := Work.FTS.EllSol.Trunc.chi_le_one _ _

/-- `phiTr N = 1` on `[-2N, 2N]` (for `N ≥ 0`), so the second cutoff does not disturb the
support of `chi N`. -/
theorem phiTr_eq_one {N t : ℝ} (hN : 0 < N) (ht : |t| ≤ 2 * N) : phiTr N t = 1 := by
  refine Work.FTS.EllSol.Trunc.chi_eq_one (N := 4096 * N) (by linarith) ?_
  calc |t| ≤ 2 * N := ht
    _ ≤ 4096 * N := by nlinarith

/-- `phiTr N = 0` off `[-8192N, 8192N]`. -/
theorem phiTr_eq_zero {N t : ℝ} (hN : 0 < N) (ht : 2 * (4096 * N) ≤ |t|) : phiTr N t = 0 :=
  Work.FTS.EllSol.Trunc.chi_eq_zero (N := 4096 * N) (by linarith) ht

theorem deriv_phiTr (N t : ℝ) : deriv (phiTr N) t =
    deriv (Work.FTS.EllSol.Trunc.chi (4096 * N)) t := rfl

end

end Work.FTS.EllSol.ShiftFT
