import Mathlib
import Submission.Work.OddCurveB.Existence.Box

/-!
# `𝐆` is differentiable in the state: `Work.OddCurveB.Est.differentiableAt_Godd`

The Volterra engine `Submission.Work.VolterraLong` (and the corollary
`Work.VolterraLong.odd_volterra_long_exists`) consumes `Work.OddVolterra.Godd` as its data with
the hypothesis

`∀ s, ∀ z, DifferentiableAt ℝ (fun w => Godd n h s w) z`.

This file proves that hypothesis **with no hypothesis at all on the bump `h`** (only `2 ≤ n`).

The proof is short because the whole content sits in the two structural lemmas already proved in
`Submission.Work.OddCurveB.Existence`:

* `Godd_eq_GoddDiag` — `Godd n h s z = GoddDiag n s (h s) (deriv h s) z`: the diagonal of the Abel
  average has collapsed (`G2_self_eq_smul`), so the system sees the bump only through the two
  numbers `(h s, h'(s))` and is given by the **explicit** expression `GoddDiag`;
* `Kdiag1_eq`, `Kdiag2_eq` — at the diagonal the Abel kernels are the explicit
  "power times square root" functions

  `Kdiag1 n s hs hp t = C₁ · (X^n · √X)`, `Kdiag2 n s hs hp t = C₂ · (X^{n-1} · √X) · (t + hp)`

  with `X = Drad s hs hp t = (t + hp) (s t + hs)`, valid for *every* real `X` (both sides vanish
  for `X ≤ 0`, and `0/0 = 0` in Lean).

So everything reduces to the differentiability of the one-variable function `x ↦ x^k √x`, which
is the content of `differentiableAt_pow_mul_sqrt` below.  That in turn reduces to
`x ↦ x √x` (`differentiableAt_mul_sqrt`), whose only non-trivial point is `x = 0` — where the
difference quotient is exactly `√h → 0`, so the derivative vanishes (`hasDerivAt_zero_mul_sqrt`).

Note the exponents: `Kdiag1` needs `k = n ≥ 2` and `Kdiag2` needs `k = n - 1 ≥ 1`, which is why
the statement carries `2 ≤ n` (`n` is the half-dimension `d = 2n + 1` of the odd case).
-/

namespace Work.OddCurveB.Est

open Work.OddVolterra Work.OddCurveB.Existence

noncomputable section

/-! ## The one-variable input: `x ↦ x ^ k √x` is differentiable -/

/-- `x ↦ x √x` has derivative `0` at `0`: on the punctured neighbourhood of `0` the difference
quotient `(h √h)/h` is exactly `√h`. -/
lemma hasDerivAt_zero_mul_sqrt : HasDerivAt (fun x : ℝ => x * Real.sqrt x) 0 0 := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  simp only [zero_add, sub_zero, smul_zero, mul_zero, Real.sqrt_zero]
  show (fun h : ℝ => h * Real.sqrt h) =o[nhds 0] fun h => h
  refine Asymptotics.IsLittleO.of_bound (fun c hc => ?_)
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (pow_pos hc 2)] with h hh
  rw [Metric.mem_ball, dist_zero_right] at hh
  have hsq : Real.sqrt ‖h‖ < c := by
    have h1 := Real.sqrt_lt_sqrt (norm_nonneg h) hh
    rwa [Real.sqrt_sq hc.le] at h1
  have h1 : ‖Real.sqrt h‖ ≤ Real.sqrt ‖h‖ := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg h), Real.norm_eq_abs]
    exact Real.sqrt_le_sqrt (le_abs_self h)
  calc ‖h * Real.sqrt h‖ ≤ ‖h‖ * Real.sqrt ‖h‖ := by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left h1 (norm_nonneg h)
    _ ≤ ‖h‖ * c := mul_le_mul_of_nonneg_left hsq.le (norm_nonneg h)
    _ = c * ‖h‖ := by ring

/-- `x ↦ x √x` is differentiable everywhere (off `0` it is a product of smooth functions). -/
lemma differentiableAt_mul_sqrt (x : ℝ) :
    DifferentiableAt ℝ (fun y : ℝ => y * Real.sqrt y) x := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact hasDerivAt_zero_mul_sqrt.differentiableAt
  · exact ((hasDerivAt_id x).mul (Real.hasDerivAt_sqrt hx)).differentiableAt

/-- `x ↦ x ^ k √x` is differentiable everywhere for `k ≥ 1`, because
`x ^ k √x = x ^ (k-1) · (x √x)`. -/
lemma differentiableAt_pow_mul_sqrt {k : ℕ} (hk : 1 ≤ k) (x : ℝ) :
    DifferentiableAt ℝ (fun y : ℝ => y ^ k * Real.sqrt y) x := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hfun : (fun y : ℝ => y ^ (j + 1) * Real.sqrt y) =
      fun y : ℝ => y ^ j * (y * Real.sqrt y) := by
    funext y; rw [pow_succ]; ring
  rw [hfun]
  exact (differentiableAt_id.pow j).mul (differentiableAt_mul_sqrt x)

/-! ## The two diagonal kernels -/

/-- The first diagonal Abel kernel is differentiable in `t`, for `n ≥ 2`. -/
lemma differentiableAt_Kdiag1 (n : ℕ) (hn : 1 ≤ n) (s hs hp : ℝ) (t : ℝ) :
    DifferentiableAt ℝ (fun u : ℝ => Kdiag1 n s hs hp u) t := by
  have hfun : (fun u : ℝ => Kdiag1 n s hs hp u) = fun u : ℝ =>
      ((Nat.doubleFactorial (2 * n + 1) : ℝ) * (-1) ^ (n + 1) / Real.sqrt 2) *
        (Drad s hs hp u ^ n * Real.sqrt (Drad s hs hp u)) := by
    funext u; exact Kdiag1_eq n s hs hp u
  rw [hfun]
  refine DifferentiableAt.const_mul ?_ _
  exact (differentiableAt_pow_mul_sqrt hn (Drad s hs hp t)).comp t
    (by unfold Drad; fun_prop)

/-- The second diagonal Abel kernel is differentiable in `t`, for `n ≥ 2`. -/
lemma differentiableAt_Kdiag2 (n : ℕ) (hn : 2 ≤ n) (s hs hp : ℝ) (t : ℝ) :
    DifferentiableAt ℝ (fun u : ℝ => Kdiag2 n s hs hp u) t := by
  have hfun : (fun u : ℝ => Kdiag2 n s hs hp u) = fun u : ℝ =>
      ((Nat.doubleFactorial (2 * n - 1) : ℝ) * (-1) ^ n / Real.sqrt 2) *
        (Drad s hs hp u ^ (n - 1) * Real.sqrt (Drad s hs hp u)) * (u + hp) := by
    funext u; exact Kdiag2_eq n (by omega) s hs hp u
  rw [hfun]
  refine (DifferentiableAt.const_mul ?_ _).mul (by fun_prop)
  exact (differentiableAt_pow_mul_sqrt (k := n - 1) (by omega) (Drad s hs hp t)).comp t
    (by unfold Drad; fun_prop)

/-! ## The explicit system `GoddDiag` -/

/-- `GoddDiag` is differentiable in the state: its coordinates are explicit functions of
`(z 0, z 1, z 2, z 3)` built from `Kdiag1`, `Kdiag2` and the coordinate projections. -/
lemma differentiableAt_GoddDiag (n : ℕ) (hn : 2 ≤ n) (s hs hp : ℝ) (z : St) :
    DifferentiableAt ℝ (fun w : St => GoddDiag n s hs hp w) z := by
  rw [show (fun w : St => GoddDiag n s hs hp w) = fun w : St =>
      ![w 0, w 1,
        -(abelMass * (-(Kdiag1 n s hs hp (-(w 0)) * w 2 + Kdiag1 n s hs hp (w 1) * w 3))),
        -(abelMass * (-(Kdiag2 n s hs hp (-(w 0)) * w 2 + Kdiag2 n s hs hp (w 1) * w 3)))]
      from rfl]
  have hD0 : DifferentiableAt ℝ (fun w : St => w 0) z :=
    (differentiable_apply (𝕜 := ℝ) (0 : Fin 4)).differentiableAt
  have hD1 : DifferentiableAt ℝ (fun w : St => w 1) z :=
    (differentiable_apply (𝕜 := ℝ) (1 : Fin 4)).differentiableAt
  have hD2 : DifferentiableAt ℝ (fun w : St => w 2) z :=
    (differentiable_apply (𝕜 := ℝ) (2 : Fin 4)).differentiableAt
  have hD3 : DifferentiableAt ℝ (fun w : St => w 3) z :=
    (differentiable_apply (𝕜 := ℝ) (3 : Fin 4)).differentiableAt
  have hneg0 : DifferentiableAt ℝ (fun w : St => -(w 0)) z := hD0.neg
  have hK1a : DifferentiableAt ℝ (fun w : St => Kdiag1 n s hs hp (-(w 0))) z := by
    have h := (differentiableAt_Kdiag1 n (by omega) s hs hp (-(z 0))).comp z hneg0
    rw [Function.comp_def] at h; exact h
  have hK1b : DifferentiableAt ℝ (fun w : St => Kdiag1 n s hs hp (w 1)) z := by
    have h := (differentiableAt_Kdiag1 n (by omega) s hs hp (z 1)).comp z hD1
    rw [Function.comp_def] at h; exact h
  have hK2a : DifferentiableAt ℝ (fun w : St => Kdiag2 n s hs hp (-(w 0))) z := by
    have h := (differentiableAt_Kdiag2 n hn s hs hp (-(z 0))).comp z hneg0
    rw [Function.comp_def] at h; exact h
  have hK2b : DifferentiableAt ℝ (fun w : St => Kdiag2 n s hs hp (w 1)) z := by
    have h := (differentiableAt_Kdiag2 n hn s hs hp (z 1)).comp z hD1
    rw [Function.comp_def] at h; exact h
  refine differentiableAt_pi.mpr (fun i => ?_)
  fin_cases i
  · simpa using hD0
  · simpa using hD1
  · simpa using ((((hK1a.mul hD2).add (hK1b.mul hD3)).neg.const_mul abelMass).neg)
  · simpa using ((((hK2a.mul hD2).add (hK2b.mul hD3)).neg.const_mul abelMass).neg)

/-- **The left-hand side of the odd Volterra system is differentiable in the state `z`**, for
every bump `h : ℝ → ℝ` and every `s : ℝ`, as soon as `2 ≤ n`. -/
theorem differentiableAt_Godd {n : ℕ} (hn : 2 ≤ n) {h : ℝ → ℝ} (s : ℝ) (z : Work.OddVolterra.St) :
    DifferentiableAt ℝ (fun w : Work.OddVolterra.St => Work.OddVolterra.Godd n h s w) z := by
  have hfun : (fun w : Work.OddVolterra.St => Work.OddVolterra.Godd n h s w) =
      fun w : Work.OddVolterra.St => GoddDiag n s (h s) (deriv h s) w :=
    funext fun w => Godd_eq_GoddDiag n h s w
  rw [hfun]
  exact differentiableAt_GoddDiag n hn s (h s) (deriv h s) z

end

end Work.OddCurveB.Est
