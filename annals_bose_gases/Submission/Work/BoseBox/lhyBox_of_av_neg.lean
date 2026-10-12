import ChallengeDeps
import Submission.Work.BoseBox.Word
import Submission.Work.ModeLatticeR3
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBox.lhyBox_of_av_neg` — the box theorem at *negative* scattering length

The requested lemma: FS `thm:LHY-Box` (`Work.BoseBox.LHYBox`) holds *vacuously*
whenever the scattering length is negative.

The whole content is in the box side.  `LHYBox` quantifies over states of the
centred box `abox n ℓ` with `ℓ = sideAt μ (a v) = K_ℓ (μ · a v)^{-1/2}`
(FS `eq:def_ell`).  When `a v < 0` and `μ > 0` the base `μ · a v` is negative,
and Mathlib's `Real.rpow` on a negative base is
`x ^ y = exp (log x * y) * cos (y * π)` (`Real.rpow_def_of_neg`); at
`y = -1/2` the factor is `cos (-π/2) = 0`, so

    sideAt μ (a v) = K_ℓ * 0 = 0,

i.e. the box has **side zero** — a degenerate box.

* For `n ≥ 1` the state space `CSBox n 0` is empty: `abox n 0` is the single
  configuration in which every particle sits at the origin, a null set in
  `X n` for `n ≥ 1`, so the defining `sq_pos` norm condition of `CSBox n 0`
  is `0 < 0`.
* For `n = 0` the left hand side `ℓ³·Λ·‖Φ‖²` carries a factor `ℓ³ = 0` and the
  right hand side `boxWordU 0 0 …` is a sum of *empty* sums (`Fin 0`, `pairSet 0`),
  hence `0 = 0`.

Nothing of the FS parameter block is used: the box side degenerates before
`ParamsOK` can matter.
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory

namespace Work.BoseBox


/-! ## 1. The degenerate box side at negative scattering length -/

/-- For a negative base, Mathlib's `Real.rpow` gives `x ^ (-1/2) = 0`
(the negative-base branch contributes the factor `cos (-π/2) = 0`). -/
lemma rpow_neg_half_of_neg {x : ℝ} (hx : x < 0) : x ^ (-(1 / 2 : ℝ)) = 0 := by
  rw [Real.rpow_def_of_neg hx]
  have hc : (-(1 / 2 : ℝ)) * Real.pi = -(Real.pi / 2) := by ring
  rw [hc, Real.cos_neg, Real.cos_pi_div_two, mul_zero]

/-- **The box side vanishes for `a v < 0`**: with `μ > 0` and `a v < 0` the base
`μ · a v` is negative, so `(μ · a v)^{-1/2} = 0` and `ℓ = K_ℓ (μ · a v)^{-1/2} = 0`. -/
lemma sideAt_eq_zero_of_av_neg {v : ℝ³ → ℝ} {μ : ℝ} (hμ : 0 < μ)
    (hav : _root_.BoseGases.a v < 0) : sideAt μ (_root_.BoseGases.a v) = 0 := by
  have hneg : μ * _root_.BoseGases.a v < 0 := mul_neg_of_pos_of_neg hμ hav
  have h1 : (μ * _root_.BoseGases.a v) ^ (-(1 / 2 : ℝ)) = 0 := rpow_neg_half_of_neg hneg
  simp only [sideAt, boxSide]
  rw [h1, mul_zero]

/-! ## 2. The degenerate box `abox N 0`, `N ≥ 1`, is null -/

/-- `abox N 0` has measure zero for `N ≥ 1` (`abox_volume` gives
`(0³)^N = 0`). -/
lemma volume_abox_zero_of_pos {N : ℕ} (hN : 0 < N) :
    (volume : Measure (Submission.BoseGases.X N)) (Submission.BoseGases.abox N (0 : ℝ)) = 0 := by
  rw [Submission.BoseGases.abox_volume N 0 le_rfl]
  simp [zero_pow hN.ne']

/-- Every integral over the null set `abox N 0`, `N ≥ 1`, vanishes. -/
lemma integral_abox_zero_of_pos {N : ℕ} (hN : 0 < N) (f : Submission.BoseGases.X N → ℝ) :
    ∫ x in Submission.BoseGases.abox N (0 : ℝ), f x = 0 := by
  have h : (volume : Measure (Submission.BoseGases.X N)).restrict
      (Submission.BoseGases.abox N (0 : ℝ)) = 0 :=
    MeasureTheory.Measure.restrict_eq_zero.mpr (volume_abox_zero_of_pos hN)
  rw [show (∫ x in Submission.BoseGases.abox N (0 : ℝ), f x)
      = ∫ x, f x ∂((volume : Measure (Submission.BoseGases.X N)).restrict
          (Submission.BoseGases.abox N (0 : ℝ))) from rfl, h]
  exact MeasureTheory.integral_zero_measure f

/-- The same vanishing statement in a form that is stable under rewriting the box
side: the box side is an *explicit* argument here, so `subst` is safe (the
integrand does not depend on it). -/
lemma integral_abox_eq_zero_of_eq_zero {N : ℕ} (hN : 0 < N) {ℓ : ℝ} (hℓ : ℓ = 0)
    (f : Submission.BoseGases.X N → ℝ) :
    ∫ x in Submission.BoseGases.abox N ℓ, f x = 0 := by
  subst hℓ
  exact integral_abox_zero_of_pos hN f

/-! ## 3. The box word with no particles -/

/-- **The box word of a zero-particle configuration vanishes**, for any box side
and any parameter block: every term of `tKinWord` is a sum over `Fin 0` and the
potential word `qLHSword` is an integral of an empty sum (no kinetic slots, no
`pairSet` pairs). -/
lemma boxWordU_zero_particles (ℓ μ d s eT b : ℝ) (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v)
    (u : ℝ³) (Φ : Submission.BoseGases.X 0 → ℝ) :
    boxWordU 0 ℓ μ d s eT b v h u Φ = 0 := by
  simp only [boxWordU, tKinWord, Work.BoseKinLoc.kinForm,
    Submission.BoseGases.qLHSword, Submission.BoseGases.pairSet, Finset.univ_eq_empty,
    Finset.filter_empty, Finset.sum_empty, mul_zero, zero_add]
  simp

/-! ## 4. The lemma -/

/-- **The box bound with a vanishing box side**, stated in a form in which the
box side is a variable (so that `subst` may rewrite it also inside the type of
the state `Φ`): with `ℓ = 0` the box is degenerate and the bound holds.

* `n = 0`: the left side carries `ℓ³ = 0` and the box word is a sum of empty
  sums (`Fin 0`, `pairSet 0`), so both sides are `0`;
* `n ≥ 1`: `abox n 0` is null, so the defining norm condition `0 < ‖Φ‖²` of
  `CSBox n 0` is `0 < 0` — there is no state. -/
lemma boxBound_of_side_eq_zero {n : ℕ} {ℓ A C η₀ μ d s eT b : ℝ} {v : ℝ³ → ℝ}
    (h : Work.UBB.ScatSol v) (hℓ : ℓ = 0) (Φ : Submission.BoseGases.CSBox n ℓ) :
    ℓ ^ 3 * Work.UBB.Lambda A C η₀ μ *
        (∫ x in Submission.BoseGases.abox n ℓ, ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2)
      ≤ boxWordU n ℓ μ d s eT b v h 0 (Φ : Submission.BoseGases.X n → ℝ) := by
  subst hℓ
  rcases n with _ | m
  · -- no particles: both sides vanish
    rw [boxWordU_zero_particles]
    simp
  · -- at least one particle: the state space is empty because the box is null
    have hzero : (∫ x in Submission.BoseGases.abox (m + 1) (0 : ℝ), Φ.toFun x ^ 2) = 0 :=
      integral_abox_zero_of_pos (Nat.succ_pos m) _
    exact absurd (hzero ▸ Φ.sq_pos) (lt_irrefl 0)

theorem lhyBox_of_av_neg {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v) {η₀ C : ℝ} (hav : _root_.BoseGases.a v < 0) : Work.BoseBox.LHYBox v h η₀ C := by
  refine ⟨1, one_pos, ?_⟩
  intro μ hμ _hμa3 _hpar n Φ
  exact boxBound_of_side_eq_zero (A := _root_.BoseGases.a v) (C := C) (η₀ := η₀) h
    (sideAt_eq_zero_of_av_neg hμ hav) Φ

end Work.BoseBox
