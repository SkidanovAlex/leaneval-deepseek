import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Submission.Work.FTS.StrongEps.wtG_shift_le
import Submission.Work.FTS.StrongEps.wtZ_shift_le
import Submission.Work.FTS.StrongEps.wtE_shift_le
import Submission.Work.FTS.StrongEps.sinTwo_thShift_bounds
import Submission.Work.FTS.StrongEps.Weights

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.FTS.StrongEps.HkSqAux

/-! ## The shift bound for the weight `Wt`

The weight of the `ℋ^k`-spaces is `Wt α z θ = w z · sin(2θ)^{-γ/2}` with `w z = (1+z)²/z²` and
`γ = 1 + α/10` (see `Submission/Work/Spaces/Defs.lean` and
`Submission/Work/FTS/StrongEps/Weights.lean`, where `wtG α = (Wt α)²`).  The log-coordinate
shifts `zShift z p = z e^{-p}` and `thShift θ p = arctan (tan θ · e^{-p})` of the `ε`-scheme
change it by at most `e^{C(|p₁|+|p₂|)}`, *in either direction*: the two factors are shifted in
opposite directions (`w` increases as `z` decreases, `sin(2θ)^{-γ/2}` increases as `θ` moves
away from `π/4`), and the siblings `wtG_shift_le` / `wtZ_shift_le` / `wtE_shift_le` record the
other direction.

The two halves are elementary:

* **radial** — `w z ≤ e^{2|p₁|} w (zShift z p₁)`: this is `w_zShift_le` (`wtE_shift_le`) applied
  at the shifted point with the *opposite* shift, since the two shifts are inverse to each other
  (`zShift_add`, `zShift_neg_self`).
* **angular** — `sin(2θ)^{-γ/2} ≤ e^{2|p₂|} sin(2·thShift θ p₂)^{-γ/2}`: the lower bound
  `e^{-|p₂|} sin(2·thShift θ p₂) ≤ sin(2θ)` of `sinTwo_thShift_bounds` (again applied at the
  shifted point with the opposite shift) turns into an *upper* bound on the negative power
  `sin(2θ)^{-γ/2}`, because `x ↦ x^{-γ/2}` is antitone (`Real.rpow_le_rpow_of_nonpos`); the
  prefactor is `e^{(γ/2)|p₂|} ≤ e^{2|p₂|}` since `γ/2 ≤ 2`.

Multiplying the two and collecting the exponentials gives `C = 2`. -/

/-- The two `z`-shifts compose: `zShift (zShift z p) q = zShift z (p+q)`. -/
theorem zShift_add (z p q : ℝ) : zShift (zShift z p) q = zShift z (p + q) := by
  have h : -p + -q = -(p + q) := by ring
  simp only [zShift]
  rw [mul_assoc, ← Real.exp_add, h]

/-- The two `z`-shifts with opposite parameters are inverse to each other. -/
theorem zShift_neg_self (z p : ℝ) : zShift (zShift z p) (-p) = z := by
  rw [zShift_add]
  simp [zShift]

/-- The two `θ`-shifts compose: `thShift (thShift θ p) q = thShift θ (p+q)`.  (Valid for every
`θ : ℝ` — the identity `tan (arctan u) = u` that it uses carries no side condition.) -/
theorem thShift_add (θ p q : ℝ) : thShift (thShift θ p) q = thShift θ (p + q) := by
  have h : -p + -q = -(p + q) := by ring
  simp only [thShift]
  rw [Real.tan_arctan, mul_assoc, ← Real.exp_add, h]

/-- The two `θ`-shifts with opposite parameters are inverse to each other on the quadrant. -/
theorem thShift_neg_self {θ p : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    thShift (thShift θ p) (-p) = θ := by
  rw [thShift_add]
  have h0 : p + -p = 0 := by ring
  rw [h0]
  simp only [thShift, neg_zero, Real.exp_zero, mul_one]
  exact Real.arctan_tan (by linarith [hθ.1, Real.pi_pos]) hθ.2

/-- **The radial factor is shifted by at most `e^{2|p|}`** (in the "unshifted `≤` shifted"
direction needed here): `w z ≤ e^{2|p|} w (zShift z p)` for `z > 0`. -/
theorem w_shift_ge_le {z p : ℝ} (hz : 0 < z) :
    Work.Spaces.w z ≤ Real.exp (2 * |p|) * Work.Spaces.w (zShift z p) := by
  have h := w_zShift_le (zShift z p) (-p) (zShift_pos hz)
  rw [zShift_neg_self, abs_neg] at h
  exact h

/-- The angular factor `sin(2θ)^{-γ/2}` is nonnegative on the closed quadrant. -/
theorem wTheta_nonneg {α : ℝ} {θ : ℝ} (hθ : θ ∈ Set.Icc 0 (π / 2)) :
    0 ≤ Work.Spaces.wTheta α θ := by
  rw [Work.Spaces.wTheta]
  exact Real.rpow_nonneg (sin_two_nonneg hθ) _

/-- **The angular factor is shifted by at most `e^{2|p₂|}`** (again in the "unshifted `≤`
shifted" direction): `sin(2θ)^{-γ/2} ≤ e^{2|p₂|} sin(2·thShift θ p₂)^{-γ/2}` for
`α ∈ (0,1]`, `θ ∈ (0,π/2)`. -/
theorem wTheta_shift_ge_le {α : ℝ} (hα : α ∈ Set.Ioc 0 1) {θ p₂ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.wTheta α θ ≤ Real.exp (2 * |p₂|) * Work.Spaces.wTheta α (thShift θ p₂) := by
  have hθ' : thShift θ p₂ ∈ Set.Ioo 0 (Real.pi / 2) := thShift_mem hθ
  have hlo := (sinTwo_thShift_bounds (θ := thShift θ p₂) (p := -p₂) hθ').1
  rw [abs_neg, thShift_neg_self hθ] at hlo
  have hB : 0 < Real.sin (2 * thShift θ p₂) := sin_two_pos hθ'
  have hA : 0 < Real.exp (-|p₂|) * Real.sin (2 * thShift θ p₂) :=
    mul_pos (Real.exp_pos _) hB
  have hr : -(Work.Spaces.gam α / 2) ≤ 0 := by
    have : 0 ≤ Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith [hα.1]
    linarith
  have h1 := Real.rpow_le_rpow_of_nonpos hA hlo hr
  have hexpneg : (Real.exp (-|p₂|)) ^ (-(Work.Spaces.gam α / 2))
      = Real.exp (|p₂| * (Work.Spaces.gam α / 2)) := by
    rw [← Real.exp_mul]
    congr 1
    ring
  have hmul : (Real.exp (-|p₂|) * Real.sin (2 * thShift θ p₂)) ^ (-(Work.Spaces.gam α / 2))
      = Real.exp (|p₂| * (Work.Spaces.gam α / 2))
          * Real.sin (2 * thShift θ p₂) ^ (-(Work.Spaces.gam α / 2)) := by
    rw [Real.mul_rpow (Real.exp_pos _).le hB.le, hexpneg]
  rw [hmul] at h1
  have hgam : Work.Spaces.gam α / 2 ≤ 2 := by
    rw [Work.Spaces.gam]; linarith [hα.2]
  have hexp : Real.exp (|p₂| * (Work.Spaces.gam α / 2)) ≤ Real.exp (2 * |p₂|) := by
    rw [Real.exp_le_exp]
    nlinarith [abs_nonneg p₂, hgam]
  have hnn : 0 ≤ Real.sin (2 * thShift θ p₂) ^ (-(Work.Spaces.gam α / 2)) :=
    Real.rpow_nonneg hB.le _
  calc Work.Spaces.wTheta α θ
      = Real.sin (2 * θ) ^ (-(Work.Spaces.gam α / 2)) := rfl
    _ ≤ Real.exp (|p₂| * (Work.Spaces.gam α / 2))
          * Real.sin (2 * thShift θ p₂) ^ (-(Work.Spaces.gam α / 2)) := h1
    _ ≤ Real.exp (2 * |p₂|) * Real.sin (2 * thShift θ p₂) ^ (-(Work.Spaces.gam α / 2)) :=
        mul_le_mul_of_nonneg_right hexp hnn
    _ = Real.exp (2 * |p₂|) * Work.Spaces.wTheta α (thShift θ p₂) := rfl

theorem Wt_shift_le :
    ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1, ∀ z θ p₁ p₂ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) →
      Work.Spaces.Wt α z θ
        ≤ Real.exp (C * (|p₁| + |p₂|))
          * Work.Spaces.Wt α (Work.FTS.StrongEps.zShift z p₁) (Work.FTS.StrongEps.thShift θ p₂) := by
  refine ⟨2, by norm_num, ?_⟩
  intro α hα z θ p₁ p₂ hz hθ
  have h1 := w_shift_ge_le (z := z) (p := p₁) hz
  have h2 : Work.Spaces.wTheta α θ ≤ Real.exp (2 * |p₂|) * Work.Spaces.wTheta α (thShift θ p₂) :=
    wTheta_shift_ge_le (α := α) (p₂ := p₂) hα hθ
  have hθIcc : θ ∈ Set.Icc 0 (π / 2) := ⟨hθ.1.le, hθ.2.le⟩
  have hθ' : thShift θ p₂ ∈ Set.Ioo 0 (π / 2) := thShift_mem hθ
  have h2nn : 0 ≤ Work.Spaces.wTheta α θ := wTheta_nonneg hθIcc
  have h1rnn : 0 ≤ Real.exp (2 * |p₁|) * Work.Spaces.w (zShift z p₁) :=
    mul_nonneg (Real.exp_pos _).le (w_nonneg _)
  have hprod := mul_le_mul h1 h2 h2nn h1rnn
  rw [Work.Spaces.Wt, Work.Spaces.Wt]
  calc Work.Spaces.w z * Work.Spaces.wTheta α θ
      ≤ (Real.exp (2 * |p₁|) * Work.Spaces.w (zShift z p₁))
          * (Real.exp (2 * |p₂|) * Work.Spaces.wTheta α (thShift θ p₂)) := hprod
    _ = Real.exp (2 * (|p₁| + |p₂|))
          * (Work.Spaces.w (zShift z p₁) * Work.Spaces.wTheta α (thShift θ p₂)) := by
        have h2e : 2 * (|p₁| + |p₂|) = 2 * |p₁| + 2 * |p₂| := by ring
        rw [h2e, Real.exp_add]
        ring

end Work.FTS.StrongEps.HkSqAux
