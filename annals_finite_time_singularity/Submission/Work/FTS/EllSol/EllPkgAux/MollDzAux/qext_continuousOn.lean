import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.FTS.EllSol.EllPkgAux.MollFatouAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.EllPkgAux.MollDzAux

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.EllSol.PkgK5.K5c (Qext Qext_of_mem)

set_option autoImplicit false

/-! ## The three branches of the doubly-odd extension `Qext`

`Qext u z s` equals `u z s` for `s ∈ [0, π/2]`, `-u z (-s)` for `s < 0` and
`-u z (π - s)` for `s > π/2`.  The two lemmas below record the two *reflected* branches,
which are the ones used when the argument leaves the closed interval `[0, π/2]`. -/

/-- The branch of the doubly-odd extension `Qext` on the left of the origin. -/
theorem Qext_of_lt_zero (u : ℝ → ℝ → ℝ) (z s : ℝ) (hs : s < 0) :
    Qext u z s = -u z (-s) := by
  rw [Qext, if_neg (fun h => (not_le.mpr hs) h.1), if_pos hs]

/-- The branch of the doubly-odd extension `Qext` beyond `π/2`. -/
theorem Qext_of_pihalf_lt (u : ℝ → ℝ → ℝ) (z s : ℝ) (hs : Real.pi / 2 < s) :
    Qext u z s = -u z (Real.pi - s) := by
  have h0s : (0 : ℝ) < s := by linarith [Real.pi_pos, hs]
  rw [Qext, if_neg (fun h => (not_le.mpr hs) h.2), if_neg (not_lt.mpr h0s.le)]

/-- **Continuity of the doubly-odd extension on `(-1, π/2 + 1)`.**

For a trace-class datum `G` (`TraceClass G`) and a radius `w > 0`, the angular slice
`s ↦ Qext G w s` is continuous on `(-1, π/2 + 1)`.  On the interval `(-1, π/2 + 1)` every
reflected argument `-s` (for `s < 0`) or `π - s` (for `s > π/2`) lies in the open quadrant
interval `(0, π/2)`, where the slice is continuous by `SmoothOpen`; the two junctions
`s = 0` and `s = π/2` are handled by the vanishing traces of `TraceClass`, which make the
two one-sided limits agree with the value there. -/
theorem qext_continuousOn (G : ℝ → ℝ → ℝ) (hT : Work.FTS.EllSol.EllPkgAux.TraceClass G) {w : ℝ} (hw : 0 < w) :
    ContinuousOn (fun s : ℝ => Work.FTS.EllSol.PkgK5.K5c.Qext G w s)
      (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) := by
  obtain ⟨hsm, h0, hpi, htr0, htrpi, -, -, -⟩ := hT
  set Q : ℝ → ℝ := fun s => Qext G w s with hQ
  -- ## The angular slice of `G` at radius `w` and its two one-sided traces
  have hslice : ContinuousOn (fun θ : ℝ => G w θ) (Set.Ioo 0 (Real.pi / 2)) :=
    (hsm.curry_θ hw).continuousOn
  have hL0 : ContinuousWithinAt (fun θ : ℝ => G w θ) (Set.Ioi 0) 0 := by
    simpa [ContinuousWithinAt, h0 w] using htr0 w hw
  have hLpi : ContinuousWithinAt (fun θ : ℝ => G w θ) (Set.Iio (Real.pi / 2)) (Real.pi / 2) := by
    simpa [ContinuousWithinAt, hpi w] using htrpi w hw
  -- ## The three branches of `Q`
  have hQneg : Set.EqOn Q (fun s : ℝ => -G w (-s)) (Set.Iio 0) := fun s hs => by
    simp only [hQ]; exact Qext_of_lt_zero G w s hs
  have hQmid : Set.EqOn Q (fun s : ℝ => G w s) (Set.Ioo 0 (Real.pi / 2)) := fun s hs => by
    simp only [hQ]; exact Qext_of_mem G w s ⟨hs.1.le, hs.2.le⟩
  have hQgt : Set.EqOn Q (fun s : ℝ => -G w (Real.pi - s)) (Set.Ioi (Real.pi / 2)) :=
    fun s hs => by
      simp only [hQ]; exact Qext_of_pihalf_lt G w s hs
  have hQ0 : Q 0 = G w 0 := by
    simp only [hQ]; exact Qext_of_mem G w 0 ⟨le_rfl, by linarith [Real.pi_pos]⟩
  have hQpi : Q (Real.pi / 2) = G w (Real.pi / 2) := by
    simp only [hQ]
    exact Qext_of_mem G w (Real.pi / 2) ⟨by linarith [Real.pi_pos], le_rfl⟩
  -- ## Continuity on the three open pieces
  have hA : ContinuousOn Q (Set.Ioo (-1) 0) := by
    have hmap : MapsTo (fun s : ℝ => -s) (Set.Ioo (-1) 0) (Set.Ioo 0 (Real.pi / 2)) :=
      fun s hs => by
        simp only [Set.mem_Ioo] at hs ⊢
        exact ⟨by linarith [hs.2], by linarith [hs.1, Real.pi_gt_three]⟩
    have hcomp : ContinuousOn (fun s : ℝ => -G w (-s)) (Set.Ioo (-1) 0) :=
      (hslice.comp continuous_neg.continuousOn hmap).neg
    exact hcomp.congr (fun s hs => hQneg hs.2)
  have hB : ContinuousOn Q (Set.Ioo 0 (Real.pi / 2)) := hslice.congr hQmid
  have hC : ContinuousOn Q (Set.Ioo (Real.pi / 2) (Real.pi / 2 + 1)) := by
    have hmap : MapsTo (fun s : ℝ => Real.pi - s) (Set.Ioo (Real.pi / 2) (Real.pi / 2 + 1))
        (Set.Ioo 0 (Real.pi / 2)) := fun s hs => by
      simp only [Set.mem_Ioo] at hs ⊢
      exact ⟨by linarith [hs.2, Real.pi_gt_three], by linarith [hs.1]⟩
    have hcont : ContinuousOn (fun s : ℝ => Real.pi - s)
        (Set.Ioo (Real.pi / 2) (Real.pi / 2 + 1)) := by fun_prop
    have hcomp : ContinuousOn (fun s : ℝ => -G w (Real.pi - s))
        (Set.Ioo (Real.pi / 2) (Real.pi / 2 + 1)) :=
      (hslice.comp hcont hmap).neg
    exact hcomp.congr (fun s hs => hQgt hs.1)
  -- ## The two junctions
  have hj0L : ContinuousWithinAt Q (Set.Iio 0) 0 := by
    have hmap : MapsTo (fun s : ℝ => -s) (Set.Iio 0) (Set.Ioi 0) := fun s hs => by
      simp only [Set.mem_Iio] at hs
      simp only [Set.mem_Ioi]
      linarith
    have h' : ContinuousWithinAt (fun θ : ℝ => G w θ) (Set.Ioi 0) (-0) := by
      simpa using hL0
    have hcomp : ContinuousWithinAt (fun s : ℝ => -G w (-s)) (Set.Iio 0) 0 :=
      (h'.comp continuous_neg.continuousWithinAt hmap).neg
    refine hcomp.congr_of_eventuallyEq (Filter.eventually_of_mem self_mem_nhdsWithin hQneg) ?_
    simp [hQ0, h0 w]
  have hj0R : ContinuousWithinAt Q (Set.Ioi 0) 0 := by
    have hmem : Set.Ioo 0 (Real.pi / 2) ∈ 𝓝[Set.Ioi 0] (0 : ℝ) :=
      Ioo_mem_nhdsGT (by linarith [Real.pi_pos])
    have hEq : Q =ᶠ[𝓝[Set.Ioi 0] (0 : ℝ)] (fun s : ℝ => G w s) :=
      Filter.eventually_of_mem hmem (fun s hs => hQmid hs)
    exact hL0.congr_of_eventuallyEq hEq hQ0
  have hj0 : ContinuousAt Q 0 :=
    continuousAt_iff_continuous_left'_right'.mpr ⟨hj0L, hj0R⟩
  have hjpiL : ContinuousWithinAt Q (Set.Iio (Real.pi / 2)) (Real.pi / 2) := by
    have hmem : Set.Ioo 0 (Real.pi / 2) ∈ 𝓝[Set.Iio (Real.pi / 2)] (Real.pi / 2) :=
      Ioo_mem_nhdsLT (by linarith [Real.pi_pos])
    have hEq : Q =ᶠ[𝓝[Set.Iio (Real.pi / 2)] (Real.pi / 2)] (fun s : ℝ => G w s) :=
      Filter.eventually_of_mem hmem (fun s hs => hQmid hs)
    exact hLpi.congr_of_eventuallyEq hEq hQpi
  have hjpiR : ContinuousWithinAt Q (Set.Ioi (Real.pi / 2)) (Real.pi / 2) := by
    have hmap : MapsTo (fun s : ℝ => Real.pi - s) (Set.Ioi (Real.pi / 2))
        (Set.Iio (Real.pi / 2)) := fun s hs => by
      simp only [Set.mem_Ioi] at hs
      simp only [Set.mem_Iio]
      linarith
    have htr : ContinuousWithinAt (fun θ : ℝ => G w θ) (Set.Iio (Real.pi / 2))
        (Real.pi - Real.pi / 2) := by
      rw [show Real.pi - Real.pi / 2 = Real.pi / 2 by ring]
      exact hLpi
    have hcont : ContinuousWithinAt (fun s : ℝ => Real.pi - s) (Set.Ioi (Real.pi / 2))
        (Real.pi / 2) := by fun_prop
    have hcomp : ContinuousWithinAt (fun s : ℝ => -G w (Real.pi - s)) (Set.Ioi (Real.pi / 2))
        (Real.pi / 2) := (htr.comp hcont hmap).neg
    refine hcomp.congr_of_eventuallyEq (Filter.eventually_of_mem self_mem_nhdsWithin hQgt) ?_
    rw [hQpi, show Real.pi - Real.pi / 2 = Real.pi / 2 by ring, hpi w, neg_zero]
  have hjpi : ContinuousAt Q (Real.pi / 2) :=
    continuousAt_iff_continuous_left'_right'.mpr ⟨hjpiL, hjpiR⟩
  -- ## Assembly
  refine continuousOn_of_forall_continuousAt fun s hs => ?_
  rcases lt_trichotomy s 0 with h | rfl | h
  · exact hA.continuousAt (isOpen_Ioo.mem_nhds ⟨hs.1, h⟩)
  · exact hj0
  · rcases lt_trichotomy s (Real.pi / 2) with h2 | rfl | h2
    · exact hB.continuousAt (isOpen_Ioo.mem_nhds ⟨h, h2⟩)
    · exact hjpi
    · exact hC.continuousAt (isOpen_Ioo.mem_nhds ⟨h2, hs.2⟩)

end Work.FTS.EllSol.EllPkgAux.MollDzAux
