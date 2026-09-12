import Mathlib
import Submission.Core.FaAnalytic
import Submission.Core.F1Norm
import Submission.Core.FullPeriod

/-!
# KL-F2: polar form of `f_a` on circle arcs and its argument derivative

(F2 of Plan.md DESIGN NOTE 6.)  On an arc of the circle avoiding the jump
points (the antipodes `-z_j`), Fedja's auxiliary function has a polar form

    f_a(E σ) = ‖f_a(E σ)‖ · e^{i·t(σ)},    t(σ) := Σ_j p_j · arg-branch(σ),

where each factor `1 + E(σ−θ_j)` stays off the negative real axis and the
continuous argument branch `(Complex.log (1 + E(σ−θ_j))).im` has derivative
`1/2` in `σ`.  Consequently `t` has derivative `(Σ_j p_j)/2` on each arc.

Prove all four theorems below (add helper lemmas as needed).  Each theorem
is proved below; the module must build with no unfinished proofs.

Mathlib hints:
- `E (t : ℝ) : ℂ := cexp ((t : ℂ) * I)` is from `Submission.Core.FullPeriod`
  (`E_add : E (t+s) = E t * E s`, `norm_E : ‖E t‖ = 1`, `E_two_pi`, and
  `E t = (Real.cos t : ℂ) + (Real.sin t : ℂ) * I` are available there or in
  `Submission/KL.lean` C0 — re-prove small ones locally if missing).
- Conjugation: `Complex.conj_exp`, `starRingEnd ℂ (E t) = E (-t)`,
  `norm_E_sub_E`, `norm_one_add_E : ‖(1:ℂ) + E t‖ = 2 * |Real.cos (t/2)|`
  (the latter two live in `Submission/KL.lean` namespace `Submission.KL`;
  re-prove a local `norm_one_add_E` here if needed).
- `Complex.log` (principal): `Complex.log_re x : x.log.re = Real.log ‖x‖`,
  `Complex.log_im x : x.log.im = x.arg`, `Complex.exp_log (hx : x ≠ 0)`,
  `Complex.cpow_def_of_ne_zero` (`x ^ y = exp (y * log x)` for `x ≠ 0`),
  `Complex.hasDerivAt_log {z} (hz : z ∈ slitPlane)`, and
  `HasDerivAt.clog_real` for real-parametrized curves (in
  Mathlib/Analysis/SpecialFunctions/Complex/LogDeriv.lean).
- `Complex.slitPlane = {z | 0 < z.re ∨ z.im ≠ 0}`; show
  `1 + E φ ≠ 0 → 1 + E φ ∈ slitPlane` by computing re/im of `1 + E φ`.
- `Complex.norm_cpow_real : ‖x ^ (y : ℂ)‖ = ‖x‖ ^ y`, and
  `Complex.ofReal_exp`, `Real.exp_log`.
- `E (t : ℝ)` satisfies `deriv (fun t : ℝ => E t) t = I * E t`; state and
  prove a local `hasDerivAt_E` if needed via `Complex.hasDerivAt_exp`.
- The target `arg_factor_hasDerivAt` asks for the REAL function
  `fun σ => (Complex.log (1 + E (σ - θ₀))).im`; use `HasDerivAt.clog_real`
  (complex-valued intermediate) then take imaginary parts via
  `HasDerivAt.im` / `Complex.hasDerivAt_im`-style lemmas, using
  `log_im`/`log_re` to identify the derivative of the imaginary part as
  `Re (I * E σ / (1 + E σ)) = 1/2` (compute with the identity
  `E φ / (1 + E φ) + conj-stuff` or `Re (1/(1 + E (-φ))) = 1/2`; a clean
  route: `E φ/(1 + E φ) = 1 - 1/(1+E φ)` and `Re (1/(1+E φ)) = 1/2` from
  `1 + E φ = 2 cos(φ/2)·E(φ/2)` giving `Re (E(-φ/2)/(2 cos(φ/2))) = 1/2`).
- `faE_eq` needs `starRingEnd ℂ (E θ) = E (-θ)` (via `Complex.conj_exp`)
  and `E_add`.
- `faE_polar` assembles `fa_norm_on_circle` (from F1Norm) with `cPow_polar`
  and `E_sum`; `a ≥ 0` makes `(a:ℂ) = ‖(a:ℂ)‖ * E 0`.
- `faE_arg_hasDerivAt` sums `arg_factor_hasDerivAt` (Finset sums of
  derivatives commute: prove locally by induction over `Finset.univ`).
- `Complex.exp_ofReal_mul_I` may help relate `E` to `Complex.exp`.
- `E_sum` is exactly true (not merely mod `2π`): `exp` is a group
  homomorphism `exp (a+b) = exp a * exp b`; prove by induction over
  `Finset.univ` using `E_add`.
- `faE_polar`'s conclusion: both sides as complex numbers.  After the norm
  identity the RHS is `(a·∏‖·‖^p) · E(Σ p_j·im)`, and the LHS product of
  the `cPow_polar` expansions gives exactly the same (multiply the real
  factors and the `E`-phases separately; use `E_sum`).
- Useful: `norm_one_add_E` identity `‖1+E φ‖ = 2*|cos(φ/2)|` for the
  jump-free hypothesis `Real.cos ((σ-θ)/2) ≠ 0` ⟺ `1 + E(σ-θ) ≠ 0`
  (needed to connect with `FaConcave`).
- To apply `fa_norm_on_circle` you need `z j := E (θ j)` to satisfy
  `‖z j‖ = 1` and `w := E σ` with `‖w‖ = 1` (`norm_E`), and the
  `hne : ∀ j, E σ ≠ -E (θ j)` which is equivalent to `1 + E (σ-θ_j) ≠ 0`
  (via `E_add`, `E (θ_j + π) = -E (θ_j)`).
- `0 ^ (p:ℂ) = 0` for `0 < p` and `cPow` continuity at `0` are NOT needed
  in this file (the polar identities are only used away from jump points).
- Real powers: `‖z‖ ^ p` with `p : ℝ` is `Real.rpow`; `‖(x:ℝ)‖ = x` for
  `0 ≤ x`; `Complex.ofReal` casts commute with `mul`/`add` (`push_cast`).
- `Finset.sum_mul`, `Finset.mul_sum`, `Finset.prod_mul_distrib`,
  `Finset.prod_congr rfl` for products over `Fin n`.
- When applying `E_add` watch out that `E (a + b) = E a * E b`; use `ring`
  for real affine arguments.
- `Complex.ext` with `Complex.ofReal_cos`/`ofReal_sin`/`Complex.ext`:
  `E φ = (cos φ : ℂ) + (sin φ : ℂ) * I` is the fastest way to get
  `re`/`im` of `E`-expressions; alternatively `Complex.exp_ofReal_mul_I`.

Note: everything here is REAL analysis on top of Mathlib's complex
exponential/log/cpow API.  Work bottom-up: (1) local lemmas: `E_neg`,
`E_sub`, `one_add_E_ne_zero_iff_cos`, `norm_one_add_E` (copy from
`Submission/KL.lean` if easier), `hasDerivAt_E`; (2) `E_sum`;
(3) `cPow_polar`; (4) `arg_factor_hasDerivAt`; (5) `faE_eq`;
(6) `faE_polar`; (7) `faE_arg_hasDerivAt`.  Verify with
`lake build Submission.Core.FaPolar`.
-/

noncomputable section

open scoped Real Complex
open Complex

namespace Submission.Core

/-- `f_a` evaluated on the circle with circle points `z_j := E(θ_j)`
(parametrized by the real angles `θ_j`), at the circle point `E σ`. -/
noncomputable def faE (n : ℕ) (a : ℝ) (θ : Fin n → ℝ) (p : Fin n → ℝ) (σ : ℝ) : ℂ :=
  fa n a (fun j : Fin n => E (θ j)) p (E σ)

/-! ## Local plumbing for the circle exponential `E` -/

lemma E_add (t s : ℝ) : E (t + s) = E t * E s := by
  dsimp [E]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma E_zero : E 0 = 1 := by simp [E]

lemma E_neg (t : ℝ) : starRingEnd ℂ (E t) = E (-t) := by
  dsimp [E]
  rw [← Complex.exp_conj]
  congr 1
  simp

lemma E_sub (a b : ℝ) : E (a - b) = E a * E (-b) := by
  calc
    E (a - b) = E (a + (-b)) := by rfl
    _ = E a * E (-b) := E_add a (-b)

lemma norm_E (t : ℝ) : ‖E t‖ = 1 := by
  dsimp [E]
  rw [Complex.norm_exp_ofReal_mul_I]

lemma E_eq_cos_sin (t : ℝ) : E t = (Real.cos t : ℂ) + (Real.sin t : ℂ) * Complex.I := by
  dsimp [E]
  rw [Complex.exp_mul_I]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]

lemma re_E (t : ℝ) : (E t).re = Real.cos t := by
  dsimp [E]
  rw [Complex.exp_mul_I]
  rw [Complex.add_re, Complex.mul_re]
  rw [Complex.cos_ofReal_re, Complex.sin_ofReal_re]
  simp

lemma im_E (t : ℝ) : (E t).im = Real.sin t := by
  dsimp [E]
  rw [Complex.exp_mul_I]
  rw [Complex.add_im, Complex.mul_im]
  rw [Complex.cos_ofReal_im, Complex.sin_ofReal_re]
  simp

/-- The exponential of a real sum is the product of the exponentials. -/
lemma E_sum {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    E (∑ i : ι, x i) = ∏ i : ι, E (x i) := by
  classical
  have h : ∀ s : Finset ι, E (∑ i ∈ s, x i) = ∏ i ∈ s, E (x i) := by
    intro s
    refine Finset.induction_on s ?base ?step
    · simp [E]
    · intro a s has ih
      rw [Finset.sum_insert has, Finset.prod_insert has, E_add]
      exact congrArg (fun y => E (x a) * y) ih
  simpa using h Finset.univ

/-- Casting a finite real product to `ℂ` commutes with the product. -/
lemma cast_prod (ι : Type*) [Fintype ι] (x : ι → ℝ) :
    ((∏ i : ι, x i : ℝ) : ℂ) = ∏ i : ι, (x i : ℂ) := by
  simp

/-- `E` has derivative `I * E t` (complex derivative of the real curve). -/
lemma hasDerivAt_E (t : ℝ) : HasDerivAt (fun s : ℝ => E s) (I * E t) t := by
  have hcos1 : HasDerivAt (fun s : ℝ => ((Real.cos s : ℝ) : ℂ)) (-(Real.sin t : ℂ)) t := by
    simpa using (HasDerivAt.ofReal_comp (Real.hasDerivAt_cos t))
  have hsin1 : HasDerivAt (fun s : ℝ => ((Real.sin s : ℝ) : ℂ)) ((Real.cos t : ℝ) : ℂ) t := by
    simpa using (HasDerivAt.ofReal_comp (Real.hasDerivAt_sin t))
  have hsinI : HasDerivAt (fun s : ℝ => ((Real.sin s : ℝ) : ℂ) * Complex.I)
      (((Real.cos t : ℝ) : ℂ) * Complex.I) t := by
    exact hsin1.mul_const I
  have hsum : HasDerivAt (fun s : ℝ => ((Real.cos s : ℝ) : ℂ) + ((Real.sin s : ℝ) : ℂ) * Complex.I)
      (-(Real.sin t : ℂ) + ((Real.cos t : ℝ) : ℂ) * Complex.I) t := hcos1.add hsinI
  have hd : (-(Real.sin t : ℂ) + ((Real.cos t : ℝ) : ℂ) * Complex.I) = I * E t := by
    rw [E_eq_cos_sin t]
    apply Complex.ext <;> simp <;> ring
  convert hsum using 1
  · ext s
    exact E_eq_cos_sin s
  · exact hd.symm

/-- The imaginary part of a real-parametrized complex curve is differentiable with derivative
the imaginary part of the complex derivative. -/
lemma hasDerivAt_im_of_hasDerivAt {F : ℝ → ℂ} {F' : ℂ} {x : ℝ} (h : HasDerivAt F F' x) :
    HasDerivAt (fun y : ℝ => (F y).im) F'.im x := by
  have hf := h.hasFDerivAt
  have himCLM : HasFDerivAt (Complex.imCLM : ℂ →L[ℝ] ℝ) Complex.imCLM (F x) :=
    Complex.imCLM.hasFDerivAt
  have hcomp := himCLM.comp x hf
  have hcomp' : HasFDerivAt (fun y : ℝ => Complex.imCLM (F y))
      (Complex.imCLM.comp (ContinuousLinearMap.toSpanSingleton ℝ F')) x := by
    simpa [Function.comp_def] using hcomp
  have hd0 : HasDerivAt (fun y : ℝ => Complex.imCLM (F y))
      ((Complex.imCLM.comp (ContinuousLinearMap.toSpanSingleton ℝ F')) 1) x :=
    hcomp'.hasDerivAt
  have hval : (Complex.imCLM.comp (ContinuousLinearMap.toSpanSingleton ℝ F')) 1 = F'.im := by
    simp
  simpa [hval, Complex.imCLM_apply] using hd0

/-- `1 + E φ ≠ 0` puts `1 + E φ` in the slit plane (where the principal log is analytic). -/
lemma one_add_E_mem_slitPlane {φ : ℝ} (h : (1 : ℂ) + E φ ≠ 0) : (1 : ℂ) + E φ ∈ slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  rw [Complex.add_re, re_E]
  rw [Complex.add_im, im_E]
  simp
  by_contra hc
  push_neg at hc
  have h1 : Real.sin φ = 0 := hc.2
  have hcos : Real.cos φ = -1 := by
    have hle : Real.cos φ ≤ -1 := by linarith
    have hge : -1 ≤ Real.cos φ := Real.neg_one_le_cos φ
    linarith
  have hE : E φ = -1 := by
    rw [E_eq_cos_sin, hcos, h1]
    simp
  apply h
  rw [hE]
  simp

/-- For `1 + E φ ≠ 0`: the imaginary part of the logarithmic derivative is `1/2`. -/
lemma one_add_E_im_val {φ : ℝ} (h : (1 : ℂ) + E φ ≠ 0) : (I * E φ / (1 + E φ)).im = 1 / 2 := by
  have hnsq : Complex.normSq (1 + E φ) = 2 * (1 + Real.cos φ) := by
    have hx : (((1 + Real.cos φ : ℝ) : ℂ) + ((Real.sin φ : ℝ) : ℂ) * Complex.I) = 1 + E φ := by
      rw [E_eq_cos_sin φ]
      push_cast
      ring
    rw [← hx]
    rw [Complex.normSq_add_mul_I]
    have hsc : Real.sin φ ^ 2 + Real.cos φ ^ 2 = 1 := Real.sin_sq_add_cos_sq φ
    nlinarith
  have hnsq_ne : Complex.normSq (1 + E φ) ≠ 0 := by
    rw [Complex.normSq_eq_norm_sq]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr h)
  have h1c : 1 + Real.cos φ ≠ 0 := by
    intro hz
    have : Complex.normSq (1 + E φ) = 0 := by
      rw [hnsq]
      linarith
    exact hnsq_ne this
  calc
    ((I * E φ) / (1 + E φ)).im = ((E φ / (1 + E φ)) * I).im := by
        congr 1
        ring
    _ = (E φ / (1 + E φ)).re := by rw [Complex.mul_I_im]
    _ = 1/2 := by
        rw [Complex.div_re]
        rw [Complex.add_re, Complex.add_im]
        rw [re_E, im_E]
        simp
        rw [hnsq]
        have hden : (2 * (1 + Real.cos φ)) ≠ 0 := mul_ne_zero (by norm_num) h1c
        field_simp [hden]
        nlinarith [Real.sin_sq_add_cos_sq φ]

/-- `‖E t + E s‖ = ‖1 + E (t - s)‖` for circle points. -/
lemma norm_E_add_E (t s : ℝ) : ‖E t + E s‖ = ‖1 + E (t - s)‖ := by
  have h1 : E (t - s) * E s = E t := by
    rw [← E_add]
    congr 1
    ring
  have hfac : E s * (1 + E (t - s)) = E t + E s := by
    calc
      E s * (1 + E (t - s)) = E s * 1 + E s * E (t - s) := by rw [mul_add]
      _ = E s + E t := by
          rw [mul_one]
          rw [mul_comm (E s) (E (t - s))]
          rw [h1]
      _ = E t + E s := by ring
  calc
    ‖E t + E s‖ = ‖E s * (1 + E (t - s))‖ := by rw [hfac]
    _ = ‖E s‖ * ‖1 + E (t - s)‖ := by rw [norm_mul]
    _ = ‖1 + E (t - s)‖ := by rw [norm_E]; ring

/-- Pointwise norm of `faE` at a jump-free `σ`:
`‖faE n a θ p σ‖ = a · ∏_j ‖1 + E(σ − θ_j)‖^{p_j}`. -/
lemma faE_norm (n : ℕ) (a : ℝ) (ha : 0 ≤ a) (θ : Fin n → ℝ) (p : Fin n → ℝ) {σ : ℝ}
    (hne : ∀ j : Fin n, (1 : ℂ) + E (σ - θ j) ≠ 0) :
    ‖faE n a θ p σ‖ = a * ∏ j : Fin n, ‖1 + E (σ - θ j)‖ ^ p j := by
  unfold faE
  rw [fa_norm_on_circle n a ha (fun j : Fin n => E (θ j)) p (by intro j; exact norm_E (θ j))
      (w := E σ) (norm_E σ)]
  · congr 1
    apply Finset.prod_congr rfl
    intro j hj
    congr 1
    exact norm_E_add_E σ (θ j)
  · intro j
    intro hEq
    apply (hne j)
    have hsub : E (σ - θ j) = E σ * E (-(θ j)) := E_sub σ (θ j)
    have hneg : E (θ j) * E (-θ j) = 1 := by
      rw [← E_add]
      congr 1
      ring
      simp [E]
    have hmain : E (σ - θ j) = -1 := by
      rw [hsub, hEq]
      calc
        (-E (θ j)) * E (-θ j) = -(E (θ j) * E (-θ j)) := by ring
        _ = -1 := by rw [hneg]
    have hzero : (1 : ℂ) + E (σ - θ j) = 0 := by
      rw [hmain]
      ring
    exact hzero

/-- `faE` expands to `a·∏_j (1 + E(σ−θ_j))^{p_j}`. -/
lemma faE_eq (n : ℕ) (a : ℝ) (θ : Fin n → ℝ) (p : Fin n → ℝ) (σ : ℝ) :
    faE n a θ p σ =
      (a : ℂ) * ∏ j : Fin n, cPow (1 + E (σ - θ j)) (p j) := by
  unfold faE fa cPow
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  congr 1
  rw [E_neg (θ j)]
  rw [← E_sub σ (θ j)]

/-- Real-linear distributivity used in `cPow_polar`. -/
lemma ofReal_mul_add_mul_I (p a b : ℝ) :
    (p : ℂ) * ((a : ℂ) + (b : ℂ) * Complex.I) = ((p * a : ℝ) : ℂ) + ((p * b : ℝ) : ℂ) * Complex.I := by
  apply Complex.ext
  · simp
  · simp

/-- **Single-factor polar form.**  For `1 + E φ ≠ 0`:
`(1 + E φ)^p = ‖1 + E φ‖^p · e^{i·p·(Complex.log (1+Eφ)).im}`. -/
lemma cPow_polar (φ : ℝ) (p : ℝ) (h : (1 : ℂ) + E φ ≠ 0) :
    cPow (1 + E φ) p =
      ((‖(1 : ℂ) + E φ‖ ^ p : ℝ) : ℂ) *
        E (p * (Complex.log (1 + E φ)).im) := by
  let w : ℂ := 1 + E φ
  have hw : w ≠ 0 := by simpa [w] using h
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hexp : Real.exp (p * (Complex.log w).re) = ‖w‖ ^ p := by
    calc
      Real.exp (p * (Complex.log w).re) = Real.exp (p * Real.log ‖w‖) := by rw [Complex.log_re]
      _ = Real.exp (Real.log ‖w‖ * p) := by rw [mul_comm]
      _ = ‖w‖ ^ p := by rw [Real.rpow_def_of_pos hwpos]
  calc
    cPow w p = w ^ (p : ℂ) := rfl
    _ = Complex.exp ((p : ℂ) * Complex.log w) := by
        rw [Complex.cpow_def_of_ne_zero hw, mul_comm]
    _ = Complex.exp ((p : ℂ) * (((Complex.log w).re : ℂ) + ((Complex.log w).im : ℂ) * Complex.I)) := by
        rw [Complex.re_add_im]
    _ = Complex.exp (((p * (Complex.log w).re : ℝ) : ℂ) + ((p * (Complex.log w).im : ℝ) : ℂ) * Complex.I) := by
        congr 1
        exact ofReal_mul_add_mul_I p (Complex.log w).re (Complex.log w).im
    _ = Complex.exp (((p * (Complex.log w).re : ℝ) : ℂ)) * Complex.exp (((p * (Complex.log w).im : ℝ) : ℂ) * Complex.I) := by
        rw [Complex.exp_add]
    _ = (Real.exp (p * (Complex.log w).re) : ℂ) * E (p * (Complex.log w).im) := by
        simp [E]
    _ = ((‖w‖ ^ p : ℝ) : ℂ) * E (p * (Complex.log w).im) := by
        rw [hexp]
    _ = ((‖(1 : ℂ) + E φ‖ ^ p : ℝ) : ℂ) * E (p * (Complex.log (1 + E φ)).im) := by
        simp [w]

/-- **Polar form of `faE` at a jump-free `σ`.**  With `0 ≤ a` and
`1 + E(σ−θ_j) ≠ 0` for every `j`,
`faE n a θ p σ = ‖faE n a θ p σ‖ · E(t σ)` for the continuous argument
branch `t σ := Σ_j p_j·(Complex.log(1+E(σ−θ_j))).im`. -/
theorem faE_polar (n : ℕ) (a : ℝ) (ha : 0 ≤ a) (θ : Fin n → ℝ) (p : Fin n → ℝ) {σ : ℝ}
    (hne : ∀ j : Fin n, (1 : ℂ) + E (σ - θ j) ≠ 0) :
    faE n a θ p σ =
      ‖faE n a θ p σ‖ *
        E (∑ j : Fin n, p j * (Complex.log (1 + E (σ - θ j))).im) := by
  calc
    faE n a θ p σ = (a : ℂ) * ∏ j : Fin n, cPow (1 + E (σ - θ j)) (p j) := by
        rw [faE_eq]
    _ = (a : ℂ) * ∏ j : Fin n,
        (((‖1 + E (σ - θ j)‖ ^ p j : ℝ) : ℂ) *
          E (p j * (Complex.log (1 + E (σ - θ j))).im)) := by
        congr 1
        apply Finset.prod_congr rfl
        intro j hj
        exact cPow_polar (σ - θ j) (p j) (hne j)
    _ = (a : ℂ) * ((∏ j : Fin n, ((‖1 + E (σ - θ j)‖ ^ p j : ℝ) : ℂ)) *
        (∏ j : Fin n, E (p j * (Complex.log (1 + E (σ - θ j))).im))) := by
        congr 1
        rw [Finset.prod_mul_distrib]
    _ = (a : ℂ) * ((∏ j : Fin n, ((‖1 + E (σ - θ j)‖ ^ p j : ℝ) : ℂ)) *
        E (∑ j : Fin n, p j * (Complex.log (1 + E (σ - θ j))).im)) := by
        congr 1
        congr 2
        rw [E_sum (fun j : Fin n => p j * (Complex.log (1 + E (σ - θ j))).im)]
    _ = ((a * ∏ j : Fin n, ‖1 + E (σ - θ j)‖ ^ p j : ℝ) : ℂ) *
        E (∑ j : Fin n, p j * (Complex.log (1 + E (σ - θ j))).im) := by
        rw [← cast_prod (Fin n) (fun j : Fin n => ‖1 + E (σ - θ j)‖ ^ p j)]
        push_cast
        ring
    _ = ‖faE n a θ p σ‖ * E (∑ j : Fin n, p j * (Complex.log (1 + E (σ - θ j))).im) := by
        congr 1
        rw [← faE_norm n a ha θ p (σ := σ) hne]

/-- **Single-factor argument derivative.**  The continuous argument branch
of `1 + E(σ−θ₀)` has derivative `1/2` in `σ` at every jump-free point. -/
lemma arg_factor_hasDerivAt (θ₀ : ℝ) {σ₀ : ℝ} (h : (1 : ℂ) + E (σ₀ - θ₀) ≠ 0) :
    HasDerivAt (fun σ : ℝ => (Complex.log (1 + E (σ - θ₀))).im) (1 / 2) σ₀ := by
  have hEder : HasDerivAt (fun σ : ℝ => E (σ - θ₀)) (I * E (σ₀ - θ₀)) σ₀ := by
    have hEmul : HasDerivAt (fun σ : ℝ => E σ * E (-θ₀)) ((I * E σ₀) * E (-θ₀)) σ₀ :=
      (hasDerivAt_E σ₀).mul_const (E (-θ₀))
    simpa [E_sub, mul_assoc] using hEmul
  have hf : HasDerivAt (fun σ : ℝ => (1 : ℂ) + E (σ - θ₀)) (I * E (σ₀ - θ₀)) σ₀ := by
    simpa using hEder.const_add (1 : ℂ)
  have hlogc : HasDerivAt (fun σ : ℝ => Complex.log (1 + E (σ - θ₀)))
      ((I * E (σ₀ - θ₀)) / (1 + E (σ₀ - θ₀))) σ₀ := by
    exact HasDerivAt.clog_real hf (one_add_E_mem_slitPlane h)
  have him := hasDerivAt_im_of_hasDerivAt hlogc
  have himv : ((I * E (σ₀ - θ₀)) / (1 + E (σ₀ - θ₀))).im = 1/2 := one_add_E_im_val h
  simpa [himv] using him

/-- **Argument-lift derivative.**  At a jump-free point, the total argument
`t(σ) := Σ_j p_j·(Complex.log (1+E(σ−θ_j))).im` has derivative
`(Σ_j p_j)/2`. -/
theorem faE_arg_hasDerivAt (n : ℕ) (θ : Fin n → ℝ) (p : Fin n → ℝ) {σ₀ : ℝ}
    (hne : ∀ j : Fin n, (1 : ℂ) + E (σ₀ - θ j) ≠ 0) :
    HasDerivAt (fun σ : ℝ => ∑ j : Fin n, p j * (Complex.log (1 + E (σ - θ j))).im)
      ((∑ j : Fin n, p j) / 2) σ₀ := by
  have hfac : ∀ j : Fin n,
      HasDerivAt (fun σ : ℝ => p j * (Complex.log (1 + E (σ - θ j))).im) (p j * (1 / 2)) σ₀ := by
    intro j
    exact (arg_factor_hasDerivAt (θ j) (hne j)).const_mul (p j)
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun j hj => hfac j)
  have hsum' : HasDerivAt (fun σ : ℝ => ∑ j : Fin n, p j * (Complex.log (1 + E (σ - θ j))).im)
      ((∑ j : Fin n, p j) * (1 / 2)) σ₀ := by
    simpa [Finset.sum_mul] using hsum
  have hval : ((∑ j : Fin n, p j) * (1 / 2)) = (∑ j : Fin n, p j) / 2 := by ring
  rw [hval.symm]
  exact hsum'
end Submission.Core

end
