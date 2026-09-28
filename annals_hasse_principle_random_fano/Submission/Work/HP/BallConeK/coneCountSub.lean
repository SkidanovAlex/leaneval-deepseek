import Mathlib
import Submission.Work.HP.BallConeK.Defs

set_option autoImplicit false
noncomputable section

namespace Work.HP.BallConeK

open Work.HP

/-- `Φ(t) - Φ(Y)` is the number of lattice points `a ∈ L∖{0}` with `Y < ‖a‖ ≤ t` lying in both
cones `𝒞_v^{(γ)}` and `𝒞_w^{(γ)}`.  Indeed the two balls of radii `t` and `Y` are nested
(`Y ≤ t`) and their difference removes the origin, so the count of the difference of the two
`coneCount`s is exactly the count of the annulus. -/
theorem coneCountSub {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : Submodule ℤ (ι → ℤ)) (v w : ι → ℝ) (γ t Y : ℝ) (hYt : Y ≤ t) (hY0 : 0 ≤ Y) :
    coneCount L v w γ t - coneCount L v w γ Y
      = ((({a : ι → ℤ | a ∈ L ∧ a ≠ 0 ∧ Y < eNorm a ∧ eNorm a ≤ t ∧
            toR a ∈ Cgam v γ ∧ toR a ∈ Cgam w γ}.ncard : ℕ)) : ℝ) := by
  classical
  set At : Set (ι → ℤ) :=
    {a : ι → ℤ | a ∈ L ∧ eNorm a ≤ t ∧ toR a ∈ Cgam v γ ∧ toR a ∈ Cgam w γ}
  set AY : Set (ι → ℤ) :=
    {a : ι → ℤ | a ∈ L ∧ eNorm a ≤ Y ∧ toR a ∈ Cgam v γ ∧ toR a ∈ Cgam w γ}
  set Lg : Set (ι → ℤ) :=
    {a : ι → ℤ | a ∈ L ∧ a ≠ 0 ∧ Y < eNorm a ∧ eNorm a ≤ t ∧
      toR a ∈ Cgam v γ ∧ toR a ∈ Cgam w γ}
  -- the ball of radius `Y` sits inside the ball of radius `t`
  have hsub : AY ⊆ At := by
    rintro a ⟨hL, hle, hc1, hc2⟩
    exact ⟨hL, le_trans hle hYt, hc1, hc2⟩
  have hfin : At.Finite := finite_coneBall L v w γ t
  have hfinY : AY.Finite := finite_coneBall L v w γ Y
  -- the difference of the two balls is exactly the annulus (the origin is in the small ball)
  have hsdiff : At \ AY = Lg := by
    ext a
    constructor
    · rintro ⟨⟨hL, hlet, hc1, hc2⟩, hnot⟩
      have hlt : Y < eNorm a := by
        by_contra hcon
        exact hnot ⟨hL, not_lt.mp hcon, hc1, hc2⟩
      have hne : a ≠ 0 := by
        rintro rfl
        simp [Work.HP.eNorm] at hlt
        linarith
      exact ⟨hL, hne, hlt, hlet, hc1, hc2⟩
    · rintro ⟨hL, hne, hlt, hlet, hc1, hc2⟩
      exact ⟨⟨hL, hlet, hc1, hc2⟩, fun hc => absurd hc.2.1 (not_le.mpr hlt)⟩
  have hnc : Lg.ncard = At.ncard - AY.ncard := by
    rw [← hsdiff, Set.ncard_sdiff hsub hfinY]
  have hle : AY.ncard ≤ At.ncard := Set.ncard_le_ncard hsub hfin
  have hgoal : coneCount L v w γ t = ((At.ncard : ℕ) : ℝ) := rfl
  have hgoalY : coneCount L v w γ Y = ((AY.ncard : ℕ) : ℝ) := rfl
  rw [hgoal, hgoalY, ← Nat.cast_sub hle, ← hnc]

end Work.HP.BallConeK
