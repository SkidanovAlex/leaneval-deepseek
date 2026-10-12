import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB4.Sect4Kernels
import Submission.Work.BoseB7.FSParamsVals
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseK15.tau_PH_bound` — the `tau_PH` row of `IntKernel` (FS §4/§10)

FS's kinetic symbol (`Work.BoseB4.tauFun`, FS `def:tau`) is

`τ(k) = (1 − ε_T)[‖k‖ − (2sℓ)⁻¹]₊² + ε_T[‖k‖ − (2dsℓ)⁻¹]₊²`,

a quadratic symbol with the two thresholds `(2sℓ)⁻¹` and `(2dsℓ)⁻¹` subtracted
from `‖k‖`.  The `IntKernel` field `tau_PH` (and the `EstimateIntegral` chapter
that consumes it, `Work.BoseB7A.int_A_ge`) needs exactly this pair of facts on
the high-momentum region `P_H` (`F.PH E.KH E.aScat k`, i.e.
`‖kmom k‖ ≥ (2K_Ha)⁻¹`):

* `0 ≤ ‖kmom k‖² − τ(k)`: the kinetic symbol never exceeds the free symbol;
* `‖kmom k‖² − τ(k) ≤ 2‖kmom k‖/(dsℓ)`: the *defect* is linear in `‖kmom k‖`
  with the slope `2/(dsℓ)`, which is what makes `τ ≥ ‖k‖²/2` on `‖k‖ ≫ (dsℓ)⁻¹`.

That `τ` is a *lower* bound for `‖k‖²` is clear: `(x − a)₊ ≤ x` for `a ≥ 0`, so
each subtracted square is at most `x²`.  The linear upper bound on the defect
comes from the elementary identity

`x² − (x − a)₊² ≤ 2ax`  (`a ≥ 0`, `x ≥ 0`),

which is `a(2x − a) ≤ 2ax` in the region `x ≥ a` and `x² ≤ 2ax` in the region
`x ≤ a`.  Applying it to both summands of `τ` and using `0 ≤ ε_T ≤ 1`,

`x² − τ ≤ 2x[(1 − ε_T)u + ε_Tv]  where u = (2sℓ)⁻¹, v = (2dsℓ)⁻¹`,

and since `d ≤ 2` gives `u ≤ 2v` while `0 ≤ ε_T ≤ 1`,

`(1 − ε_T)u + ε_Tv ≤ (1 − ε_T)2v + ε_Tv = (2 − ε_T)v ≤ 2v`,

whence `x² − τ ≤ 4xv = 2x/(dsℓ)`.  (Note that only `d ≤ 2`, `0 ≤ ε_T ≤ 1` and
the positivity of `s, d, ℓ` are used; the `P_H` hypothesis is *not* needed, and
the statement carries it only because that is the region where the corpus reads
the row.)

The positivity of `s, d` is `s = X > 0`, `d = X⁶ > 0` and that of `ℓ` is
`Work.BoseB7.ell_pos` (`ℓ = K_ℓ(μa)^{-1/2}` with `K_ℓ ≥ 1 > 0`, `μ, a > 0`).

The scalar core below (`tau_sub_sq_arith`) is stated with the thresholds `u, v`
and the target `L` abstract, so that the instantiation is a pure arithmetic
comparison of `(2sℓ)⁻¹`, `(2dsℓ)⁻¹` and `2x/(dsℓ)`.
-/

noncomputable section

namespace Work.BoseK15

open Work.BoseB7

/-! ## 1. The two elementary real facts -/

/-- `(x − a)₊² ≤ x²` for `x ≥ 0`, `a ≥ 0` (the positive part never exceeds `x`,
so neither does its square). -/
private lemma sq_le_sq_max_sub (x a : ℝ) (hx : 0 ≤ x) (ha : 0 ≤ a) :
    (max (x - a) 0) ^ 2 ≤ x ^ 2 :=
  pow_le_pow_left₀ (le_max_right _ _) (max_le (by linarith) hx) 2

/-- `x² − (x − a)₊² ≤ 2ax` for `x ≥ 0`, `a ≥ 0`: in the region `x ≥ a` this is
`a(2x − a) ≤ 2ax`, and in the region `x ≤ a` it is `x² ≤ 2ax`. -/
private lemma sq_sub_max_le (x a : ℝ) (hx : 0 ≤ x) (ha : 0 ≤ a) :
    x ^ 2 - (max (x - a) 0) ^ 2 ≤ 2 * a * x := by
  rcases le_or_gt x a with h | h
  · rw [max_eq_right (by linarith : x - a ≤ 0)]
    nlinarith
  · rw [max_eq_left (by linarith : (0 : ℝ) ≤ x - a)]
    nlinarith

/-! ## 2. The scalar core -/

/-- **The kinetic defect of `τ` is nonnegative and linear in `x`.**  For
`x ≥ 0`, `u, v ≥ 0`, `0 ≤ e ≤ 1`, `u ≤ 2v` and a target `L ≥ 2x·2v`,

`0 ≤ x² − ((1 − e)(x − u)₊² + e(x − v)₊²) ≤ L`.

This is the whole scalar content of `tau_PH_bound`: `u, v` are the two
thresholds `(2sℓ)⁻¹`, `(2dsℓ)⁻¹` of FS `def:tau`, `e` is `ε_T`, and
`L = 2x/(dsℓ) = 4xv` is the claimed bound. -/
private lemma tau_sub_sq_arith (x e u v L : ℝ) (hx : 0 ≤ x) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (he0 : 0 ≤ e) (he1 : e ≤ 1) (huv : u ≤ 2 * v) (hL : 2 * x * (2 * v) ≤ L) :
    0 ≤ x ^ 2 - ((1 - e) * (max (x - u) 0) ^ 2 + e * (max (x - v) 0) ^ 2) ∧
      x ^ 2 - ((1 - e) * (max (x - u) 0) ^ 2 + e * (max (x - v) 0) ^ 2) ≤ L := by
  have h1e : 0 ≤ 1 - e := by linarith
  have hAle := sq_le_sq_max_sub x u hx hu
  have hBle := sq_le_sq_max_sub x v hx hv
  have hAsub := sq_sub_max_le x u hx hu
  have hBsub := sq_sub_max_le x v hx hv
  -- split the defect along `x² = (1 − e)x² + e x²` and bound each summand
  have hstep : x ^ 2 - ((1 - e) * (max (x - u) 0) ^ 2 + e * (max (x - v) 0) ^ 2)
      ≤ 2 * x * ((1 - e) * u + e * v) := by nlinarith [hAsub, hBsub]
  have h2 : (1 - e) * u + e * v ≤ 2 * v := by nlinarith [huv, hu, hv, he0, h1e]
  have h3 : 2 * x * ((1 - e) * u + e * v) ≤ 2 * x * (2 * v) :=
    mul_le_mul_of_nonneg_left h2 (by linarith)
  exact ⟨by nlinarith [hAle, hBle, he0, h1e], le_trans hstep (le_trans h3 hL)⟩

/-! ## 3. The `tau_PH` row -/

/-- **`IntKernel.tau_PH`** (FS §4/§10): on the high-momentum region `P_H` the
kinetic symbol `τ` satisfies `τ(k) ≤ ‖k‖²` and
`‖k‖² − τ(k) ≤ 2‖k‖/(dsℓ)`.

All the hypotheses beyond FS's parameter point `hv` and the identification
`htau` of `E.tau` with FS `def:tau` are the two smallness facts
`d ≤ 2`, `0 ≤ ε_T ≤ 1` at which FS's parameters are used. -/
theorem tau_PH_bound {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    {F : Work.BoseB7.FockData Mode} {E : Work.BoseB7.Q3Env Mode}
    (hv : Work.BoseB7.FSParamsView E)
    (htau : ∀ k : Mode, E.tau k = Work.BoseB4.tauFun E.eT E.s E.d E.ell (F.kmom k))
    (hd : E.d ≤ 2) (heT0 : 0 ≤ E.eT) (heT1 : E.eT ≤ 1) :
    ∀ k : Mode, F.PH E.KH E.aScat k →
      0 ≤ ‖F.kmom k‖ ^ 2 - E.tau k ∧
        ‖F.kmom k‖ ^ 2 - E.tau k ≤ 2 * ‖F.kmom k‖ / (E.d * E.s * E.ell) := by
  intro k _hk
  -- positivity of the three parameters entering the thresholds
  have hs : 0 < E.s := by rw [hv.s_eq]; exact Work.BoseBox.fsXp_pos hv.t_pos
  have hdpos : 0 < E.d := by rw [hv.d_eq]; exact Work.BoseBox.fsXp_pos hv.t_pos
  have hell : 0 < E.ell := Work.BoseB7.ell_pos E hv
  have hdsell : 0 < E.d * E.s * E.ell := by positivity
  have hu : 0 ≤ (2 * E.s * E.ell)⁻¹ := inv_nonneg.mpr (by positivity)
  have hv' : 0 ≤ (2 * E.d * E.s * E.ell)⁻¹ := inv_nonneg.mpr (by positivity)
  -- `2·(2dsℓ)⁻¹ = (dsℓ)⁻¹`
  have h2 : 2 * (2 * E.d * E.s * E.ell)⁻¹ = (E.d * E.s * E.ell)⁻¹ := by
    field_simp
  -- `(2sℓ)⁻¹ ≤ 2(2dsℓ)⁻¹ = (dsℓ)⁻¹`, i.e. `dsℓ ≤ 2sℓ`, i.e. `d ≤ 2`
  have huv : (2 * E.s * E.ell)⁻¹ ≤ 2 * (2 * E.d * E.s * E.ell)⁻¹ := by
    rw [h2]
    exact inv_anti₀ hdsell (by nlinarith [hd, mul_pos hs hell])
  -- `2x·2·(2dsℓ)⁻¹ = 2x/(dsℓ)`
  have hL : 2 * ‖F.kmom k‖ * (2 * (2 * E.d * E.s * E.ell)⁻¹) ≤
      2 * ‖F.kmom k‖ / (E.d * E.s * E.ell) := by
    rw [h2, div_eq_mul_inv]
  have hcore := tau_sub_sq_arith ‖F.kmom k‖ E.eT (2 * E.s * E.ell)⁻¹
    (2 * E.d * E.s * E.ell)⁻¹ (2 * ‖F.kmom k‖ / (E.d * E.s * E.ell))
    (norm_nonneg _) hu hv' heT0 heT1 huv hL
  rw [htau k, Work.BoseB4.tauFun]
  exact hcore

/-- **The `tau_PH` row at FS's parameter point `FSParamsView`, with the two
smallness facts derived.**  For `t = μa³ ≤ 1` FS's choices give
`d = X⁶ ≤ 1 ≤ 2`, `0 ≤ ε_T = X^{23/4}` and `ε_T ≤ 1`, so only `hv` and `htau`
need to be supplied.  This is the form in which the corpus (`IntKernel.tau_PH`,
via `Work.BoseK15.toIntKernel`/`IntKernel_corpus`) consumes the bound. -/
theorem tau_PH_bound_of_view {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode]
    {F : Work.BoseB7.FockData Mode} {E : Work.BoseB7.Q3Env Mode}
    (hv : Work.BoseB7.FSParamsView E)
    (htau : ∀ k : Mode, E.tau k = Work.BoseB4.tauFun E.eT E.s E.d E.ell (F.kmom k)) :
    ∀ k : Mode, F.PH E.KH E.aScat k →
      0 ≤ ‖F.kmom k‖ ^ 2 - E.tau k ∧
        ‖F.kmom k‖ ^ 2 - E.tau k ≤ 2 * ‖F.kmom k‖ / (E.d * E.s * E.ell) :=
  tau_PH_bound hv htau
    (by
      rw [hv.d_eq]
      exact le_trans (Work.BoseBox.fsXp_le_one hv.t_pos hv.t_le_one (by norm_num)) (by norm_num))
    (by
      rw [hv.eT_eq]
      exact Work.BoseBox.fsXp_nonneg hv.t_pos.le)
    (by
      rw [hv.eT_eq]
      exact Work.BoseBox.fsXp_le_one hv.t_pos hv.t_le_one (by norm_num))

end Work.BoseK15
