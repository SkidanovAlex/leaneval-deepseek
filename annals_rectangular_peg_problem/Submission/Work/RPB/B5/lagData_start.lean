import Mathlib
import Submission.Work.RPB.B5.LagData
import Submission.Work.RPB.B5.Defs
import Submission.Work.RPB.Defs
import Submission.Work.RPB.B2.chordVec_circle
import Submission.Work.RPV.VBasic
import Submission.Work.RPV.chordPS_unit_phase_mem_Zsec

/-!
# B5: the `τ = 0` slice of the assembled family is the zero section

The assembled family `ℓ τ (x,t) = lagPt W Γc Ac rho τ x t` of `Defs.lean` is, on the left half
`x ≤ 0`, the collar at level `σ = sig x` for `x ≤ -√2` and the chord chart at the (squared) chord
parameter `rho τ x t` for `-√2 ≤ x ≤ 0`; the right half `x > 0` is the `τ_π`-image of the
reflected left half.

This module proves the `start` field of `LagFamily` for `ℓ`: the whole `τ = 0` slice lies in the
zero section `Zsec = {p = 0}`.

* **Collar branch** (`x ≤ -√2`): `σ = sig x ≥ 0` there, and at `τ = 0` the collar is inside the zero
  section by the hypothesis `D.hτ0` (this is exactly what `collar_exists` provides).
* **Chord chart branch** (`-√2 < x ≤ 0`): with `r = √(rho 0 x t) ∈ (0, π/2]` (the range of the
  middle reparametrisation, `D.hrhoval`) the chart hypothesis `D.hWchord` writes
  `W 0 t (rho 0 x t) = chordSurf CI.c a 0 t r`.  At `τ = 0` the curve is the unit circle
  (`CI.start`), and the chord phase there is `t + π/2` mod `2π` — the chord
  `e^{i(t+r)} - e^{i(t-r)} = 2 sin r · i · e^{it}` points in the direction `t + π/2`, which is the
  phase equation of `IsChordPhase` at `τ = 0`.  Then `Work.RPV.chordPS_unit_phase_mem_Zsec`
  (a generalisation of `Work.RPV.chordPS_circle`) puts the chord in the zero section.
* **Right half** (`x > 0`): `lagPt` is `tau π` of a point of the left half, and `tau π` preserves
  the zero section (`p₁ ↦ -p₁`, `p₂ ↦ p₂`, `q₂ ↦ q₂ + π`).

Note that the *`x > 0`* half of `ℓ 0` is `tau π` of `basePt` at `-x < 0`, so the key auxiliary
statement below (`hbase`) is only claimed for `y ≤ 0`: for `y > 0` the chord parameter `rho 0 y t`
is not constrained by `LagData` and `basePt` there is not (and need not be) in the zero section.
-/

open RectangularPegProblem
open Manifold Complex Real

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B5

/-- The chord phase at `τ = 0` on the whole annulus `0 < r < π`: the curve is the unit circle, so
the chord vector over the base point `t` is `2 sin r · i · e^{it}`, of direction `e^{i(t+π/2)}`;
`IsChordPhase` says the phase lifts that direction, whence `exp (a 0 t r · i) = exp ((t+π/2) · i)`.

This is `Work.RPB.B5.exp_chordPhase_zero_sub` (there stated for the smaller range `r < π/2`, which
is all the level data needs) with the range widened to `0 < r < π`; only the latter covers the
endpoint `r = π/2` of the chart, which is the value of the reparametrisation at `x = 0`
(`rho 0 0 t = π²/4`).  Used only in this file. -/
private theorem exp_chordPhase_zero_sub_pi (CI : Work.RPV.CurveIsotopy)
    (a : ℝ → ℝ → ℝ → ℝ) (ha : Work.RPB.IsChordPhase CI.c a) (t r : ℝ)
    (hr : r ∈ Set.Ioo (0 : ℝ) Real.pi) :
    Complex.exp (((a 0 t r - (t + Real.pi / 2)) : ℝ) * Complex.I) = 1 := by
  have hr0 : 0 < r := hr.1
  have hrπ : r < Real.pi := hr.2
  have hmem : r ∈ Set.Ioo (0 : ℝ) Real.pi := hr
  have hsin : 0 < Real.sin r := Real.sin_pos_of_pos_of_lt_pi hr0 hrπ
  -- the chord of the unit circle, as an explicit multiple of `exp ((t + π/2) * I)`
  have hval : ((2 * Real.sin r : ℝ) : ℂ) * Complex.exp (((t + Real.pi / 2) : ℝ) * Complex.I)
      = Work.RPB.chordVec CI.c 0 t r := by
    rw [Work.RPB.B2.chordVec_circle CI.c CI.start t r]
    push_cast
    ring
  -- whose norm is `2 sin r`
  have hnorm : ‖Work.RPB.chordVec CI.c 0 t r‖ = 2 * Real.sin r := by
    rw [← hval, norm_mul, Complex.norm_real, Complex.norm_exp_ofReal_mul_I, mul_one,
      Real.norm_eq_abs, abs_of_pos (by linarith : (0 : ℝ) < 2 * Real.sin r)]
  have hne : ((2 * Real.sin r : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; linarith
  -- `IsChordPhase` says the chord is `‖chord‖ * exp (a * I)`; cancelling the positive factor
  -- identifies the two exponential directions
  have hdir := ha.2.1 0 (by norm_num) t r hmem
  rw [hnorm, ← hval] at hdir
  have hexp : Complex.exp (((t + Real.pi / 2) : ℝ) * Complex.I)
      = Complex.exp (a 0 t r * Complex.I) := mul_left_cancel₀ hne hdir
  have hsub : (((a 0 t r - (t + Real.pi / 2)) : ℝ) : ℂ) * Complex.I
      = a 0 t r * Complex.I - ((t + Real.pi / 2) : ℝ) * Complex.I := by
    push_cast; ring
  rw [hsub, Complex.exp_sub, hexp, div_self (Complex.exp_ne_zero _)]

/-- `τ_π` preserves the zero section: it keeps `p` and only moves the angle `q₂`. -/
private theorem tau_pi_mem_Zsec {z : Work.RPV.PS} (hz : z ∈ Work.RPV.Zsec) :
    Work.RPV.tau Real.pi z ∈ Work.RPV.Zsec := by
  have h1 : z.2.1 = 0 := by simpa using congrArg Prod.fst hz
  have h2 : z.2.2 = 0 := by simpa using congrArg Prod.snd hz
  simp only [Work.RPV.Zsec, Set.mem_ofPred_eq, Work.RPV.tau, Real.cos_pi, Real.sin_pi,
    Prod.mk_eq_zero]
  exact ⟨by rw [h1]; ring, h2⟩

theorem lagData_start (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (ha : Work.RPB.IsChordPhase CI.c a) (D : Work.RPB.B5.LagData CI a) :
    ∀ x t : ℝ, Work.RPB.B5.lagPt D.W D.Γc D.Ac D.rho 0 x t ∈ Work.RPV.Zsec := by
  -- ### the chord chart branch: `W 0 t (r²) = chordSurf CI.c a 0 t r ∈ Zsec`
  have hchord0 : ∀ t : ℝ, ∀ r ∈ Set.Ioc (0 : ℝ) (Real.pi / 2),
      Work.RPB.chordSurf CI.c a 0 t r ∈ Work.RPV.Zsec := by
    intro t r hr
    have hrπ : r ∈ Set.Ioo (0 : ℝ) Real.pi := ⟨hr.1, by linarith [hr.2, Real.pi_pos]⟩
    have h1 := exp_chordPhase_zero_sub_pi CI a ha t r hrπ
    have h2 : ((a 0 t r : ℝ) : ℂ) * Complex.I
        = ((a 0 t r - (t + Real.pi / 2) : ℝ) : ℂ) * Complex.I
          + ((t + Real.pi / 2 : ℝ) : ℂ) * Complex.I := by push_cast; ring
    have hphase : Complex.exp (((a 0 t r) : ℂ) * Complex.I)
        = Complex.exp (((t + Real.pi / 2 : ℝ)) * Complex.I) := by
      rw [h2, Complex.exp_add, h1, one_mul]
    rw [Work.RPB.chordSurf, CI.start (t + r), CI.start (t - r)]
    exact Work.RPV.chordPS_unit_phase_mem_Zsec t r (a 0 t r) hphase
  -- ### the `x ≤ 0` half of `ℓ 0` is in the zero section
  have hbase : ∀ y : ℝ, y ≤ 0 → ∀ s : ℝ,
      basePt D.W D.Γc D.Ac D.rho 0 y s ∈ Work.RPV.Zsec := by
    intro y hy s
    by_cases hys : y ≤ -Real.sqrt 2
    · -- collar: `σ = sig y ≥ 0` and `D.hτ0`
      have hsig : 0 ≤ sig y := by
        have h1 : Real.sqrt 2 ≤ -y := by linarith
        have h2 : (Real.sqrt 2) ^ 2 ≤ (-y) ^ 2 :=
          pow_le_pow_left₀ (Real.sqrt_nonneg 2) h1 2
        rw [Real.sq_sqrt (by norm_num), neg_sq] at h2
        simp only [sig]
        linarith
      rw [basePt, if_pos hys, collarPt]
      exact D.hτ0 (sig y) hsig s
    · -- chord chart: `r = √(rho 0 y s) ∈ (0, π/2]`
      have hy1 : -Real.sqrt 2 < y := not_le.mp hys
      obtain ⟨hr0, hr1⟩ := D.hrhoval 0 (by norm_num) y ⟨hy1, hy⟩ s
      have hsqrt_pos : 0 < Real.sqrt (D.rho 0 y s) := Real.sqrt_pos.mpr hr0
      have hsqrt_le : Real.sqrt (D.rho 0 y s) ≤ Real.pi / 2 := by
        calc Real.sqrt (D.rho 0 y s) ≤ Real.sqrt (Real.pi ^ 2 / 4) := Real.sqrt_le_sqrt hr1
          _ = Real.pi / 2 := by
              rw [show Real.pi ^ 2 / 4 = (Real.pi / 2) ^ 2 by ring]
              exact Real.sqrt_sq (by positivity)
      rw [basePt, if_neg hys, ← Real.sq_sqrt hr0.le]
      rw [D.hWchord 0 (by norm_num) s (Real.sqrt (D.rho 0 y s)) ⟨hsqrt_pos, hsqrt_le⟩]
      exact hchord0 s (Real.sqrt (D.rho 0 y s)) ⟨hsqrt_pos, hsqrt_le⟩
  -- ### assembly: `x ≤ 0` is `basePt`, `x > 0` is `tau π` of the reflected left point
  intro x t
  by_cases hx : x ≤ 0
  · rw [lagPt, if_pos hx]
    exact hbase x hx t
  · rw [lagPt, if_neg hx]
    exact tau_pi_mem_Zsec (hbase (-x) (by linarith) (t - Real.pi))

end Work.RPB.B5
