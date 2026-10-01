/-
# ZeroFreeTables — P3Pos.lean

The positivity of HB's polynomial `P₃(X) = X + X² + (2/3)X³` on the relevant region
of `ℂ`: this is the *algebraic* input of Heath-Brown's `P₃` method (HB §4, §§8–10),
the one that lets the derivation drop every zero term of the sums `Σ(s,χ)`.

HB's derivation of (4.10) proceeds in two steps:

* **(4.11)**, the *boundary* check `Re p(1/(1+iy)) ≥ 0` for all real `y`; and
* **Lemma 4.1** (the maximum principle on `Re z ≥ 0`), which transports it to
  `Re p(1/z) ≥ 0` for all `z` with `Re z ≥ 1`, i.e. `Re p((σ-1)/(s-ρ)) ≥ 0`
  whenever `σ = Re s > 1 ≥ Re ρ`.

For `p = P₃` both steps are *elementary*: the identity `P3_re_eq` below exhibits

  `Re P₃(w) = (8/3)(Re w)³ + (1 + 2 Re w)·(Re w - |w|²)`,

so that `Re P₃(w) ≥ 0` holds on the whole disc `|w|² ≤ Re w` — whose boundary is
precisely the image of the imaginary axis under `z ↦ 1/(1+z)`.  On that boundary
(`w = 1/(1+iy)`, `|w|² = Re w`) the identity reads `Re P₃(w) = (8/3)/(1+y²)³`, the
exact form of (4.11) for `P₃` quoted in `Engine.lean`; and no maximum-principle
argument is needed for the polynomial case.

*The coefficient `2/3` is essential*: with `P₃(X) = X + X² + X³` the boundary value
`Re P₃(1/(1+iy))` becomes negative (already at `y = 3`), and the Table-8
certificates of `Table8Cert.lean` would have no engine to come from.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.Engine

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables

/-- **The identity behind HB's (4.11) for `P₃`.**  `Re P₃ w` is a polynomial in
`Re w` and `|w|²` only (the imaginary part of `w` enters only through `|w|²`):

`Re P₃(w) = (8/3)(Re w)³ + (1 + 2 Re w)·(Re w - |w|²)`.

Hence, on the circle `|w|² = Re w`, it is `(8/3)(Re w)³`. -/
theorem P3_re_eq (w : ℂ) :
    (P3 w).re = (8/3) * w.re^3 + (1 + 2 * w.re) * (w.re - Complex.normSq w) := by
  rcases w with ⟨a, b⟩
  simp only [P3, Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.normSq_apply, pow_succ]
  norm_num
  ring

/-- **HB (4.11) for `P₃`, sharp form.**  On the disc `|w|² ≤ Re w` — the image of
the half-plane `Re z ≥ 0` under `w = 1/(1+z)` — one has `Re P₃(w) ≥ (8/3)(Re w)³ ≥ 0`. -/
theorem P3_re_ge_sharp (w : ℂ) (h : Complex.normSq w ≤ w.re) :
    (8/3) * w.re^3 ≤ (P3 w).re := by
  rw [P3_re_eq]
  have h0 : 0 ≤ Complex.normSq w := Complex.normSq_nonneg w
  have hb : 0 ≤ w.re - Complex.normSq w := by linarith
  have h1 : 0 ≤ 1 + 2 * w.re := by linarith
  nlinarith [mul_nonneg h1 hb]

/-- **HB (4.11) for `P₃`.**  `Re P₃(w) ≥ 0` throughout the disc `|w|² ≤ Re w`. -/
theorem P3_re_ge (w : ℂ) (h : Complex.normSq w ≤ w.re) : 0 ≤ (P3 w).re := by
  have h0 : 0 ≤ Complex.normSq w := Complex.normSq_nonneg w
  have ha : 0 ≤ w.re := by linarith
  have h2 : 0 ≤ (8/3) * w.re^3 := by positivity
  linarith [P3_re_ge_sharp w h]

/-- **HB (4.11) + HB Lemma 4.1, for `P₃`.**  For every `z : ℂ` with `Re z ≥ 1`,

`Re P₃(1/z) ≥ 0`.

(Equivalently `Re P₃((σ-1)/(s-ρ)) ≥ 0` for `σ = Re s > 1` and `Re ρ ≤ 1`, which is
the form in which HB uses it in §4 and in (9.1)–(9.7); see `P3_div_re_nonneg`.) -/
theorem P3_inv_re_nonneg (z : ℂ) (hz : 1 ≤ z.re) : 0 ≤ (P3 z⁻¹).re := by
  apply P3_re_ge
  have h0 : 0 < Complex.normSq z := by
    have hz0 : 0 < z.re := by linarith
    nlinarith [Complex.normSq_apply z, sq_nonneg z.im, sq_nonneg z.re]
  rw [Complex.normSq_inv, Complex.inv_re]
  rw [le_div_iff₀ h0]
  rw [inv_mul_cancel₀ (ne_of_gt h0)]
  exact hz

/-- **The boundary value of (4.11).**  At `w = 1/(1+iy)` (so `|w|² = Re w`),

`Re P₃(1/(1+iy)) = (8/3)/(1+y²)³`.

This is the exact form in which HB's check (4.11) is used. -/
theorem P3_inv_one_add_I_mul_re (y : ℝ) :
    (P3 ((1 : ℂ) / (1 + (y : ℂ) * Complex.I))).re = (8/3) / (1 + y^2)^3 := by
  have hden : (1 : ℂ) + (y : ℂ) * Complex.I ≠ 0 := by
    intro h
    have h2 := congrArg Complex.re h
    simp at h2
  have hw : (1 : ℂ) / (1 + (y : ℂ) * Complex.I) = ⟨1/(1+y^2), -(y/(1+y^2))⟩ := by
    rw [div_eq_iff hden]
    apply Complex.ext
    · simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.one_re,
        Complex.one_im]
      field_simp
      ring
    · simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.one_re,
        Complex.one_im]
      field_simp
      ring
  rw [hw, P3_re_eq]
  simp only [Complex.normSq_apply]
  norm_num
  field_simp
  ring

/-- **HB §4, the step that needs Lemma 4.1 — for `P₃` done directly.**  For
`σ = Re s > 1` and `Re ρ ≤ 1`,

`Re P₃((σ-1)/(s-ρ)) ≥ 0`.

This is the inequality that allows the zero terms `Re P₃(α/((s-u)𝓛))` with
`Re u ≤ Re s` to be dropped from the sums `Σ(s,χ)` in HB (9.1): there
`α = a + λ₁` and `σ = 1 + a/𝓛`, so `(σ-1)/(s-u) = α/((s-u)𝓛)` up to the positive
factor `(a+λ₁)/(σ-1) = 𝓛 …` and the argument lies in the disc of `P3_re_ge`. -/
theorem P3_div_re_nonneg {s ρ : ℂ} (hs : 1 < s.re) (hρ : ρ.re ≤ 1) :
    0 ≤ (P3 ((s.re - 1) / (s - ρ))).re := by
  have h1 : 0 < s.re - 1 := by linarith
  have hsρ : (s - ρ).re = s.re - ρ.re := by simp
  have hz : 1 ≤ ((s - ρ) / ((s.re - 1 : ℝ) : ℂ)).re := by
    rw [Complex.div_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, add_zero,
      Complex.normSq_apply, hsρ, zero_div]
    rw [le_div_iff₀ (by positivity : (0:ℝ) < (s.re - 1) * (s.re - 1))]
    nlinarith [mul_le_mul_of_nonneg_right (by linarith : s.re - 1 ≤ s.re - ρ.re)
      (by linarith : (0:ℝ) ≤ s.re - 1)]
  have h := P3_inv_re_nonneg ((s - ρ) / ((s.re - 1 : ℝ) : ℂ)) hz
  have h2 : ((s - ρ) / ((s.re - 1 : ℝ) : ℂ))⁻¹ = ((s.re : ℂ) - 1) / (s - ρ) := by
    rw [inv_div]
    push_cast
    ring
  rwa [h2] at h

/-- **HB (4.11) in the half-plane form.**  For `Re z ≥ 0`, `Re P₃(1/(1+z)) ≥ 0` —
the form in which (4.11) is checked (`z = iy`) and from which HB's Lemma 4.1
transports the positivity to the whole half-plane (here proved directly, since for
`P₃` the disc condition `|w|² ≤ Re w` already holds on `w = 1/(1+z)`). -/
theorem P3_re_ge_of_re_inv {z : ℂ} (hz : 0 ≤ z.re) :
    0 ≤ (P3 ((1 : ℂ) / (1 + z))).re := by
  have hz1 : 1 ≤ ((1 : ℂ) + z).re := by simp; linarith
  have := P3_inv_re_nonneg (1 + z) hz1
  have h2 : (1 + z)⁻¹ = (1 : ℂ) / (1 + z) := by rw [one_div]
  rwa [h2] at this

end Work.ZeroFreeTables
