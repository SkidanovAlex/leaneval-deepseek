import Mathlib
import Submission.Work.InnermostDisk.Defs
import Submission.Work.InnermostDisk.WindingAPI
import Submission.Work.TorusCover.Main

namespace Work.InnermostDisk

open Work.CoreTopology

/-- **A reparametrisation of an inessential loop is inessential.**

Let `P` be a parametrised torus with surface `F = P.carrier`, and let `γ`, `c` be closed
curves of `F`.  Suppose `γ` is the composite of `c` with a continuous `φ : ℝ → ℝ` which is
`2π`-periodic up to a shift by `k` periods, `φ (t + 2π) = φ t + k · 2π`, and that
`γ t = c (φ t)` for all `t`.  Then if `c` is inessential (zero winding vector), so is `γ`.

The proof is elementary: take any lift `Lc = (Θ, Φ)` of `c`; since `c` is inessential its
winding vector vanishes, so by `LiftOf.period_shift_winding` both `Θ` and `Φ` are `2π`-periodic
functions.  Hence `t ↦ Lc (φ t)` is a lift of `γ` whose parameters return to their starting
values after one period, because `φ (2π) = φ 0 + k · 2π` and a `2π`-periodic function is
invariant under shifts by integer multiples of `2π`.  That lift therefore has vanishing winding
vector, and since the winding vector is independent of the lift, `γ` is inessential. -/
theorem not_isEssential_of_comp {P : Work.CoreTopology.ParamTorus}
    {γ c : Work.CoreTopology.ClosedCurve P} (φ : ℝ → ℝ) (hφ : Continuous φ) (k : ℤ)
    (hper : ∀ t : ℝ, φ (t + 2 * Real.pi) = φ t + k * (2 * Real.pi))
    (hcomp : ∀ t : ℝ, γ.γ t = c.γ (φ t))
    (hc : ¬ Work.CoreTopology.IsEssential P c) :
    ¬ Work.CoreTopology.IsEssential P γ := by
  -- every lift of `c` has vanishing winding vector
  have hw : ∀ L : LiftOf P c, L.winding = (0, 0) :=
    (not_isEssential_iff_winding_eq_zero c).mp hc
  obtain ⟨Lc⟩ := Work.TorusCover.ParamTorus_exists_liftOf P c
  have hwc : Lc.winding = (0, 0) := hw Lc
  -- the two parameter functions of `Lc` are `2π`-periodic
  have hperΘ : Function.Periodic Lc.Θ (2 * Real.pi) := by
    intro t
    have h := Lc.period_shift_winding t
    rw [hwc] at h
    simpa using h.1
  have hperΦ : Function.Periodic Lc.Φ (2 * Real.pi) := by
    intro t
    have h := Lc.period_shift_winding t
    rw [hwc] at h
    simpa using h.2
  -- `φ` advances by exactly `k` periods over one period
  have hφper : φ (2 * Real.pi) = φ 0 + (k : ℝ) * (2 * Real.pi) := by
    simpa using hper 0
  -- the composite lift returns to itself after one period
  let L' : LiftOf P γ :=
    { Θ := fun t => Lc.Θ (φ t)
      Φ := fun t => Lc.Φ (φ t)
      contΘ := Lc.contΘ.comp hφ
      contΦ := Lc.contΦ.comp hφ
      lifts := fun t => (Lc.lifts (φ t)).trans (hcomp t).symm }
  have hL' : L'.winding = (0, 0) := by
    refine winding_eq_zero_of_period_eq L' ?_ ?_
    · show Lc.Θ (φ (2 * Real.pi)) = Lc.Θ (φ 0)
      rw [hφper]
      exact hperΘ.int_mul k (φ 0)
    · show Lc.Φ (φ (2 * Real.pi)) = Lc.Φ (φ 0)
      rw [hφper]
      exact hperΦ.int_mul k (φ 0)
  -- so `γ` is inessential
  rintro ⟨L, hL⟩
  exact hL (by rw [← L.winding_eq L']; exact hL')

end Work.InnermostDisk
