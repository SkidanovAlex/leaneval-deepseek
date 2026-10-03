/-
# `Submission.Work.FIArea6Hecke.R.thetaDual_decay`

**Exponential decay of the dual theta function at `∞`.**  When the first Fourier coefficient
vanishes, `ĝ(0) = gaussSum d χ 0 = 0`, every summand of

  `thetaDual d χ w = Σ_{ξ ∈ ℤ[i]} ĝ(ξ)·e^{-π|ξ|²w}`

carries the factor `e^{-π|ξ|²w}` with `|ξ|² ≥ 1`, so the whole sum decays like `e^{-πw}`:

  `‖thetaDual d χ w‖ ≤ C·e^{-πw}`   for all `w ≥ 1`.

This is the second of the two analytic inputs (the other is `continuousOn_thetaDual`) needed to
continue the completed Hecke `L`-function; note that no multiplicativity of `χ` is used: only the
size bound `‖χ‖ ≤ 1` (which makes the Gauss sums bounded by the number `(4d)²` of their terms) and
the vanishing of the `ξ = 0` term.
-/
import Mathlib
import Submission.Work.FIArea6Hecke.R.A6HeckeDual
import Submission.Work.FIArea6Hecke.R.continuousOn_thetaDual

set_option autoImplicit false

namespace Work.FIArea6Hecke.R

open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

/-- **The origin is the only lattice point with `|ξ|² < 1`**: for a nonzero `ξ ∈ ℤ²` one has
`1 ≤ ξ₁² + ξ₂²`.  This is what upgrades the pointwise Gaussian decay `e^{-π|ξ|²w}` to the uniform
factor `e^{-πw}`. -/
lemma one_le_sq_add_sq {p : ℤ × ℤ} (hp : p ≠ 0) :
    (1 : ℝ) ≤ (p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2 := by
  have hz : p.1 ≠ 0 ∨ p.2 ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hp (by ext <;> simp [hc.1, hc.2])
  rcases hz with hz | hz
  · have h1 : (1 : ℤ) ≤ p.1 ^ 2 := by
      have h2 : (1 : ℤ) ≤ |p.1| := Int.one_le_abs hz
      nlinarith [sq_abs p.1, sq_nonneg (|p.1| : ℤ)]
    have h1R : (1 : ℝ) ≤ (p.1 : ℝ) ^ 2 := by exact_mod_cast h1
    nlinarith [sq_nonneg (p.2 : ℝ)]
  · have h1 : (1 : ℤ) ≤ p.2 ^ 2 := by
      have h2 : (1 : ℤ) ≤ |p.2| := Int.one_le_abs hz
      nlinarith [sq_abs p.2, sq_nonneg (|p.2| : ℤ)]
    have h1R : (1 : ℝ) ≤ (p.2 : ℝ) ^ 2 := by exact_mod_cast h1
    nlinarith [sq_nonneg (p.1 : ℝ)]

/-- **The Gaussian splitting of the exponent**: for `w ≥ 1` and `|ξ|² ≥ 1`,
`e^{-π|ξ|²w} ≤ e^{π}·e^{-πw}·e^{-π|ξ|²}`, i.e. the decay at level `w` is the decay at level `1`
up to the global factor `e^{-π(w-1)}` — which is the assertion `(|ξ|²-1)(w-1) ≥ 0`. -/
lemma exp_neg_mul_le_exp_pi_mul (s w : ℝ) (hs : 1 ≤ s) (hw : 1 ≤ w) :
    Real.exp (-Real.pi * (s * w)) ≤ Real.exp Real.pi * Real.exp (-Real.pi * w) *
      Real.exp (-Real.pi * s) := by
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hprod : 0 ≤ (s - 1) * (w - 1) := mul_nonneg (by linarith) (by linarith)
  nlinarith [Real.pi_pos, hprod]

/-- **Exponential decay of the dual theta function.**  For `‖χ‖ ≤ 1` and `ĝ(0) = 0` there is a
constant `C` with `‖thetaDual d χ w‖ ≤ C·e^{-πw}` for all `w ≥ 1`. -/
theorem thetaDual_decay {d : ℕ} (hd : 1 ≤ d) {chi : GaussianInt → ℂ}
    (hchi : ∀ z : GaussianInt, ‖chi z‖ ≤ 1)
    (h0 : Work.FIArea5.S16Hecke.gaussSum d chi 0 = 0) :
    ∃ C : ℝ, ∀ w : ℝ, 1 ≤ w →
      ‖Work.FIArea6Hecke.R.thetaDual d chi w‖ ≤ C * Real.exp (-Real.pi * w) := by
  classical
  refine ⟨((4 * d : ℕ) : ℝ) ^ 2 * Real.exp Real.pi *
    (∑' p : ℤ × ℤ, Real.exp (-Real.pi * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2))), ?_⟩
  intro w hw
  -- summability of the level-`1` Gaussian weight over the lattice `ℤ²`
  have hsumm : Summable (fun p : ℤ × ℤ =>
      Real.exp (-Real.pi * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2))) := by
    simpa using thetaDualDominated_aux 1 one_pos
  -- the dominating (summable) function at level `w`
  have hmaj : Summable (fun p : ℤ × ℤ => ((4 * d : ℕ) : ℝ) ^ 2 * Real.exp Real.pi *
      Real.exp (-Real.pi * w) *
      Real.exp (-Real.pi * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2))) :=
    hsumm.mul_left _
  -- the pointwise bound on the summands
  have hbound : ∀ p : ℤ × ℤ,
      ‖Work.FIArea5.S16Hecke.gaussSum d chi ⟨p.1, p.2⟩ *
        Complex.exp (-Real.pi * (((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2) * w))‖
      ≤ ((4 * d : ℕ) : ℝ) ^ 2 * Real.exp Real.pi * Real.exp (-Real.pi * w) *
        Real.exp (-Real.pi * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)) := by
    intro p
    by_cases hp : p = 0
    · -- the vanishing first Fourier coefficient kills the `ξ = 0` summand
      have hz : Work.FIArea5.S16Hecke.gaussSum d chi (⟨p.1, p.2⟩ : GaussianInt) = 0 := by
        have hp' : (⟨p.1, p.2⟩ : GaussianInt) = 0 := by rw [hp]; rfl
        rw [hp']
        exact h0
      rw [hz, zero_mul, norm_zero]
      positivity
    · have hs : (1 : ℝ) ≤ (p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2 := one_le_sq_add_sq hp
      rw [norm_mul]
      have hnorm : ‖Complex.exp (-Real.pi * (((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2) * w))‖
          = Real.exp (-Real.pi * (((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2) * w)) := by
        rw [show -Real.pi * (((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2) * w)
            = ((-Real.pi * (((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2) * w) : ℝ) : ℂ) by
              push_cast; ring]
        rw [Complex.norm_exp_ofReal]
      rw [hnorm]
      have hg := thetaDualGaussBound_aux d hchi (⟨p.1, p.2⟩ : GaussianInt)
      have hexp := exp_neg_mul_le_exp_pi_mul ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2) w hs hw
      calc ‖Work.FIArea5.S16Hecke.gaussSum d chi ⟨p.1, p.2⟩‖ *
              Real.exp (-Real.pi * (((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2) * w))
          ≤ ((4 * d : ℕ) : ℝ) ^ 2 *
              Real.exp (-Real.pi * (((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2) * w)) :=
            mul_le_mul_of_nonneg_right hg (Real.exp_nonneg _)
        _ ≤ ((4 * d : ℕ) : ℝ) ^ 2 * (Real.exp Real.pi * Real.exp (-Real.pi * w) *
              Real.exp (-Real.pi * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2))) :=
            mul_le_mul_of_nonneg_left hexp (by positivity)
        _ = ((4 * d : ℕ) : ℝ) ^ 2 * Real.exp Real.pi * Real.exp (-Real.pi * w) *
              Real.exp (-Real.pi * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)) := by ring
  have hFsum : Summable (fun p : ℤ × ℤ =>
      Work.FIArea5.S16Hecke.gaussSum d chi ⟨p.1, p.2⟩ *
        Complex.exp (-Real.pi * (((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2) * w))) :=
    Summable.of_norm_bounded hmaj hbound
  rw [thetaDual]
  calc ‖∑' p : ℤ × ℤ, Work.FIArea5.S16Hecke.gaussSum d chi ⟨p.1, p.2⟩ *
        Complex.exp (-Real.pi * (((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2) * w))‖
      ≤ ∑' p : ℤ × ℤ, ‖Work.FIArea5.S16Hecke.gaussSum d chi ⟨p.1, p.2⟩ *
        Complex.exp (-Real.pi * (((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2) * w))‖ :=
        norm_tsum_le_tsum_norm hFsum.norm
    _ ≤ ∑' p : ℤ × ℤ, ((4 * d : ℕ) : ℝ) ^ 2 * Real.exp Real.pi *
        Real.exp (-Real.pi * w) *
        Real.exp (-Real.pi * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)) :=
        Summable.tsum_le_tsum hbound hFsum.norm hmaj
    _ = ((4 * d : ℕ) : ℝ) ^ 2 * Real.exp Real.pi * Real.exp (-Real.pi * w) *
        (∑' p : ℤ × ℤ, Real.exp (-Real.pi * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2))) :=
        tsum_mul_left
    _ = (((4 * d : ℕ) : ℝ) ^ 2 * Real.exp Real.pi *
        (∑' p : ℤ × ℤ, Real.exp (-Real.pi * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)))) *
        Real.exp (-Real.pi * w) := by ring

end

end Work.FIArea6Hecke.R
