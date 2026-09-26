import Mathlib
import Submission.Work.Drive.EpsForm.WaypointDiscDefs

namespace Work.Drive.EpsForm

open Set

/-!
# The two chords of the corrected disc in torus coordinates

The corrected profile `profX t ·` is the polyline `W1 → W2c t → W3c t → W5c t` in the tube
coordinates at levels `0 → sig1c t → sig2c t → 1`.  Its interior intersections with the unit
circle of the tube are exactly the two chord waypoints `W2c t` and `W3c t`, which sit at the
levels `sig1 t` and `sig2 t`.  The two lemmas below make this precise and then translate it
into torus coordinates: the disc points `eFunX t (sig1 t)` and `eFunX t (sig2 t)` are the torus
points of meridian parameters `phLift t` and `phLift t + dlt t`.
-/

noncomputable section

/-- If the corrected profile at level `s` is the point of the unit circle with tube angle `φ`,
then the corresponding disc point is the torus point with meridian parameter `φ`. -/
theorem eFunX_eq_torusMap_of {t s φ : ℝ} (h : profX t s = (Real.cos φ, Real.sin φ)) :
    eFunX t s = Work.Core.torusMap t φ := by
  have h1 : (profX t s).1 = Real.cos φ := by rw [h]
  have h2 : (profX t s).2 = Real.sin φ := by rw [h]
  apply WithLp.ofLp_injective 2
  funext i
  fin_cases i
  · show eFunX t s 0 = Work.Core.torusMap t φ 0
    rw [eFunX_apply_zero, Work.Core.torusMap_apply_zero, h1]
  · show eFunX t s 1 = Work.Core.torusMap t φ 1
    rw [eFunX_apply_one, Work.Core.torusMap_apply_one, h1]
  · show eFunX t s 2 = Work.Core.torusMap t φ 2
    rw [eFunX_apply_two, Work.Core.torusMap_apply_two, h2]

/-- The two chord levels are ordered throughout the chord range. -/
theorem sig1_le_sig2_of_mem {t : ℝ} (ht : t ∈ Set.Icc u0 v0) : sig1 t ≤ sig2 t := by
  have hb := bump_nonneg_of_inRange (Set.mem_Icc.mp ht)
  unfold sig1 sig2; linarith

/-- The corrected profile meets the unit circle at the lower chord level exactly at the
point `W2c t`. -/
theorem profX_sig1 {t : ℝ} (ht : t ∈ Set.Icc u0 v0) : profX t (sig1 t) = W2c t := by
  have hin : inRange t := Set.mem_Icc.mp ht
  have hs : sig1c t = sig1 t := by simp only [sig1c, if_pos hin]
  rw [profX_br1 (le_of_eq hs.symm), hs,
    seg_right (P := W1) (Q := W2c t) (a := 0) (b := sig1 t)
      (by intro hh; linarith [sig1_pos t])]

/-- The corrected profile meets the unit circle at the upper chord level exactly at the
point `W3c t`.  At the ends `t = u0`, `t = v0` of the chord range the two chord levels and
the waypoints `W2c`, `W3c` collapse, and the branch-1 computation applies. -/
theorem profX_sig2 {t : ℝ} (ht : t ∈ Set.Icc u0 v0) : profX t (sig2 t) = W3c t := by
  have hin : inRange t := Set.mem_Icc.mp ht
  have hs1c : sig1c t = sig1 t := by simp only [sig1c, if_pos hin]
  have hs2c : sig2c t = sig2 t := by simp only [sig2c, if_pos hin]
  by_cases hs : sig2 t ≤ sig1c t
  · -- the chord levels have collapsed: `sig1 t = sig2 t`, `dlt t = 0` and `W2c t = W3c t`
    have hle : sig2 t = sig1 t :=
      le_antisymm (by rw [← hs1c]; exact hs) (sig1_le_sig2_of_mem ht)
    have hbump : bump t = 0 := by unfold sig1 sig2 at hle; linarith
    have hdlt : dlt t = 0 := by unfold dlt; rw [hbump]; ring
    rw [profX_br1 hs, hs1c, hle,
      seg_right (P := W1) (Q := W2c t) (a := 0) (b := sig1 t)
        (by intro hh; linarith [sig1_pos t])]
    simp only [W2c, W3c, if_pos hin, hdlt, add_zero]
  · -- the genuine chord: branch 2, evaluated at its upper end `sig2c t = sig2 t`
    rw [profX_br2 hs (le_of_eq hs2c.symm), hs2c,
      seg_right (P := W2c t) (Q := W3c t) (a := sig1c t) (b := sig2 t)
        (by rw [hs1c]; intro hh; linarith [lt_of_not_ge hs])]

/-- **The two chords of the corrected disc in torus coordinates.**  For `t` in the chord
range `[u0,v0]`, the profile points at the two chord levels are exactly the torus points
with meridian parameters `phLift t` and `phLift t + dlt t`:
`eFunX t (sig1 t) = torusMap t (phLift t)` and
`eFunX t (sig2 t) = torusMap t (phLift t + dlt t)`.

Route: `profX t s = ((2 + u) cos t, (2+u) sin t, v)` with `(u,v) = profX t s`, and
`profX t (sig1 t) = W2c t = (cos (phLift t), sin (phLift t))` (branch 1, evaluated at its
upper end `sig1c t = sig1 t > 0`), respectively
`profX t (sig2 t) = W3c t = (cos (phLift t + dlt t), sin (phLift t + dlt t))`
(branch 2, evaluated at its upper end; for `t = u0` or `t = v0` both branches collapse and
the coincidence is `W2c u0 = W5c u0`, `W2c v0 = W5c v0`, `phLift u0 = u0`,
`phLift v0 = v0 - 2π ≡ v0`). -/
theorem eFunX_chords {t : ℝ} (ht : t ∈ Set.Icc u0 v0) :
    eFunX t (sig1 t) = Work.Core.torusMap t (phLift t) ∧
    eFunX t (sig2 t) = Work.Core.torusMap t (phLift t + dlt t) := by
  have hin : inRange t := Set.mem_Icc.mp ht
  refine ⟨?_, ?_⟩
  · apply eFunX_eq_torusMap_of
    rw [profX_sig1 ht]; simp only [W2c, if_pos hin]
  · apply eFunX_eq_torusMap_of
    rw [profX_sig2 ht]; simp only [W3c, if_pos hin]

end

end Work.Drive.EpsForm
