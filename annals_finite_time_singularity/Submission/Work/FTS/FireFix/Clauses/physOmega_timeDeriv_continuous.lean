/-
# Continuity of `∂ₜ(−physOmega α A B g C)` on the physical window

This is the `hωcont` clause of the generic reconstruction theorem
`Work.FTS.FireFix.blowupAt_of_physical'` (read at `ω = −physOmega α A B g C`, `T = C.T`), derived
from the corrected regularity package `RegPkgGal.RegPkg'` of the self-similar profile.

## The route

Write `τ(t) = clockInv C t` for the extended inverse clock, so that

  `physOmega α A B g C x t = physVort α A B g x (τ(t))`.

The time derivative of the (negated) physical vorticity is then given by the chain rule,

  `∂ₜ(−physOmega …)(x,t) = − (C.A (τ(t)))⁻¹ • ∂_τ physVort … x (τ(t))`
  (`Support.timeDeriv_physOmega_eq`, valid for every `t ∈ [0, C.T)` — including `t = 0`, where the
  tangent extension of the clock provides the two-sided derivative `(C.A 0)⁻¹`);

so `∂ₜ(−physOmega …)` is the product of the two functions

* `t ↦ (C.A (τ(t)))⁻¹`, continuous on `[0, C.T)` (`clockInv_amplitude_inv_continuousOn`, from the
  continuity of `C.A` on `[0,∞)` and its positivity, so that the composition with the continuous
  inverse clock and the inversion are legitimate);
* `q ↦ ∂_τ physVort … q.1 (τ(q.2))`, continuous on `ℝ³ × [0, C.T)`.

For the second one, the strip hypothesis `hreg` turns `physVort α A B g` into a fully
strip-admissible vorticity (`Prime.physVort_bundle`), on which the two Hölder statements

* `x ↦ ∂_τ physVort … x τ` is Hölder in `x`, uniformly on the strip
  (`CoreResiduals.BiotSavart.timeDeriv_xHolderOn_general`), and
* `τ ↦ ∂_τ physVort … x τ` is Hölder in `τ`, uniformly in `x` (the `TimeDerivStripHolder` clause of
  the bundle)

combine, by the elementary two-term argument `Support.holder_pair_continuousWithinAt`, into the
continuity of `∂_τ physVort …` within `ℝ³ × [0,∞)` at every point of `ℝ³ × [0, C.T)`; composing
with the continuous clock map `q ↦ (q.1, τ(q.2))`, whose image on `ℝ³ × [0, C.T)` lies in
`ℝ³ × [0, ∞)`, gives the joint continuity through the clock.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Submission.Work.FTS.FireFix.Defs
import Submission.Work.FTS.FireFix.PhysData
import Submission.Work.FTS.FireFix.Prime.PhysVortBundle
import Submission.Work.CoreResiduals.BiotSavart.timeDeriv_xHolderOn_general
import Submission.Work.FTS.FireFix.Clauses.Support.holder_pair_continuousWithinAt
import Submission.Work.FTS.FireFix.Clauses.Support.timeDeriv_physOmega_eq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Filter Topology MeasureTheory
open scoped Topology

namespace Work.FTS.FireFix.Clauses

/-! ## The amplitude factor `t ↦ (C.A (τ(t)))⁻¹` -/

/-- **The amplitude factor of the chain rule is continuous on the physical window.**  The extended
inverse clock `clockInv C` is continuous on `[0, C.T)` (it is differentiable there, with the
tangent extension at `0`), it takes values in `[0,∞)` on that window, and `C.A` is continuous and
positive on `[0,∞)`; hence the composite `t ↦ C.A (clockInv C t)` is continuous on `[0, C.T)` and
nowhere zero there, so its inverse is too. -/
theorem clockInv_amplitude_inv_continuousOn {C : Work.FTS.Physical.PhysClock} :
    ContinuousOn (fun t : ℝ => (C.A (Work.FTS.Physical.clockInv C t))⁻¹)
      (Set.Ico (0 : ℝ) C.T) := by
  have hclock : ContinuousOn (fun t : ℝ => Work.FTS.Physical.clockInv C t)
      (Set.Ico (0 : ℝ) C.T) := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with h | h
    · rw [← h]
      exact (Work.FTS.Physical.clockInv_hasDerivAt_zero C).continuousAt.continuousWithinAt
    · exact (Work.FTS.Physical.clockInv_hasDerivAt C ⟨h, ht.2⟩).continuousAt.continuousWithinAt
  have hA : ContinuousOn (fun t : ℝ => C.A (Work.FTS.Physical.clockInv C t))
      (Set.Ico (0 : ℝ) C.T) := by
    have h := C.hAcont.comp hclock
      (fun t ht => Work.FTS.Physical.clockInv_nonneg C ht)
    simpa only [Function.comp_def] using h
  exact hA.inv₀
    (fun t ht => ne_of_gt (C.hApos _ (Work.FTS.Physical.clockInv_nonneg C ht)))

/-! ## Joint continuity of `∂_τ physVort` through the clock -/

/-- **The fake-time derivative of the physical vorticity, read through the extended inverse clock,
is continuous on the physical window `ℝ³ × [0, C.T)`.**

At every point `q₀` of the window we choose the fake-time strip `[0, τ(q₀.2) + 1]`, which carries
the full bundle of `physVort α A B g` (`Prime.physVort_bundle`); its two Hölder clauses (in `x`,
uniformly in `τ`, from the space derivative bound; and in `τ`, uniformly in `x`, from the bundle)
give the continuity of `(x,τ) ↦ ∂_τ physVort … x τ` within `ℝ³ × [0,∞)` at `(q₀.1, τ(q₀.2))`, and
the clock map `q ↦ (q.1, τ(q.2))` is continuous with image in `ℝ³ × [0,∞)`. -/
theorem timeDeriv_physVort_clock_continuousOn {α : ℝ} (hα : 0 < α)
    {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ} {C : Work.FTS.Physical.PhysClock}
    (hreg : ∀ S : ℝ, 0 < S → Work.FTS.RegPkgGal.RegPkg' α S A B g) :
    ContinuousOn (fun q : EuclideanSpace ℝ (Fin 3) × ℝ =>
        FiniteTimeSingularity.timeDeriv (Work.FTS.Regularity.physVort α A B g) q.1
          (Work.FTS.Physical.clockInv C q.2))
      (Set.univ ×ˢ Set.Ico (0 : ℝ) C.T) := by
  intro q₀ hq₀
  set Φ : EuclideanSpace ℝ (Fin 3) × ℝ → EuclideanSpace ℝ (Fin 3) × ℝ :=
    fun q => (q.1, Work.FTS.Physical.clockInv C q.2)
  have hτ₀ : 0 ≤ Work.FTS.Physical.clockInv C q₀.2 :=
    Work.FTS.Physical.clockInv_nonneg C hq₀.2
  have hSpos : 0 < Work.FTS.Physical.clockInv C q₀.2 + 1 := by linarith
  -- the fake-time bundle and its two Hölder clauses
  obtain ⟨_R, _hR, hbun⟩ := Work.FTS.FireFix.Prime.physVort_bundle
    (hreg (Work.FTS.Physical.clockInv C q₀.2 + 1) hSpos)
  obtain ⟨c, hc, Cx, _hCx, hx⟩ := Work.CoreResiduals.BiotSavart.timeDeriv_xHolderOn_general
    (α := (⟨α, hα.le⟩ : NNReal)) hα hSpos hbun
  obtain ⟨N, hN⟩ := hbun.2.2
  -- joint continuity of `∂_τ physVort` within `ℝ³ × [0,∞)`
  have hΨ : ContinuousWithinAt
      (fun p : EuclideanSpace ℝ (Fin 3) × ℝ =>
        FiniteTimeSingularity.timeDeriv (Work.FTS.Regularity.physVort α A B g) p.1 p.2)
      (Set.univ ×ˢ Set.Ici (0 : ℝ)) (Φ q₀) := by
    refine Support.holder_pair_continuousWithinAt
      (C := Cx) (N := N) (c := c) (a := α)
      (S := Work.FTS.Physical.clockInv C q₀.2 + 1)
      (t₀ := Work.FTS.Physical.clockInv C q₀.2) (x₀ := q₀.1)
      hc hα hτ₀ (by linarith) (fun x x' t ht => ?_) (fun x t t' ht ht' => ?_)
    · have h := hx x x' t ht
      calc dist (FiniteTimeSingularity.timeDeriv (Work.FTS.Regularity.physVort α A B g) x t)
              (FiniteTimeSingularity.timeDeriv (Work.FTS.Regularity.physVort α A B g) x' t)
          = ‖FiniteTimeSingularity.timeDeriv (Work.FTS.Regularity.physVort α A B g) x t -
              FiniteTimeSingularity.timeDeriv (Work.FTS.Regularity.physVort α A B g) x' t‖ := by
            rw [dist_eq_norm]
        _ ≤ Cx * ‖x - x'‖ ^ c := h
    · have h := hN x t ht t' ht'
      calc dist (FiniteTimeSingularity.timeDeriv (Work.FTS.Regularity.physVort α A B g) x t)
              (FiniteTimeSingularity.timeDeriv (Work.FTS.Regularity.physVort α A B g) x t')
          = ‖FiniteTimeSingularity.timeDeriv (Work.FTS.Regularity.physVort α A B g) x t -
              FiniteTimeSingularity.timeDeriv (Work.FTS.Regularity.physVort α A B g) x t'‖ := by
            rw [dist_eq_norm]
        _ ≤ N * |t - t'| ^ α := h
  -- the clock map and the composition
  have hclockAt : ContinuousAt (Work.FTS.Physical.clockInv C) q₀.2 := by
    rcases eq_or_lt_of_le hq₀.2.1 with h | h
    · rw [← h]
      exact (Work.FTS.Physical.clockInv_hasDerivAt_zero C).continuousAt
    · exact (Work.FTS.Physical.clockInv_hasDerivAt C ⟨h, hq₀.2.2⟩).continuousAt
  have hclockWithin : ContinuousWithinAt (fun q : EuclideanSpace ℝ (Fin 3) × ℝ =>
      Work.FTS.Physical.clockInv C q.2) (Set.univ ×ˢ Set.Ico (0 : ℝ) C.T) q₀ := by
    have h := hclockAt.comp (continuous_snd.continuousAt (x := q₀))
    simpa only [Function.comp_def] using h.continuousWithinAt
  have hΦ : ContinuousWithinAt Φ (Set.univ ×ˢ Set.Ico (0 : ℝ) C.T) q₀ :=
    continuous_fst.continuousWithinAt.prodMk hclockWithin
  have hmap : Set.MapsTo Φ (Set.univ ×ˢ Set.Ico (0 : ℝ) C.T)
      (Set.univ ×ˢ Set.Ici (0 : ℝ)) :=
    fun q hq => ⟨trivial, Work.FTS.Physical.clockInv_nonneg C hq.2⟩
  have hcomp := ContinuousWithinAt.comp (x := q₀) (f := Φ) hΨ hΦ hmap
  simpa only [Φ, Function.comp_def] using hcomp

/-! ## The target -/

theorem physOmega_timeDeriv_continuous {α : ℝ} (hα : 0 < α)
    {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ} {C : Work.FTS.Physical.PhysClock}
    (hreg : ∀ S : ℝ, 0 < S → Work.FTS.RegPkgGal.RegPkg' α S A B g) :
    ContinuousOn (fun q : EuclideanSpace ℝ (Fin 3) × ℝ =>
        FiniteTimeSingularity.timeDeriv
          (fun y s => - Work.FTS.Physical.physOmega α A B g C y s) q.1 q.2)
      (Set.univ ×ˢ Set.Ico (0 : ℝ) C.T) := by
  have hB : ContinuousOn (fun q : EuclideanSpace ℝ (Fin 3) × ℝ =>
        FiniteTimeSingularity.timeDeriv (Work.FTS.Regularity.physVort α A B g) q.1
          (Work.FTS.Physical.clockInv C q.2))
      (Set.univ ×ˢ Set.Ico (0 : ℝ) C.T) :=
    timeDeriv_physVort_clock_continuousOn hα hreg
  have hAinv := clockInv_amplitude_inv_continuousOn (C := C)
  have h1 : ContinuousOn (fun q : EuclideanSpace ℝ (Fin 3) × ℝ =>
      (C.A (Work.FTS.Physical.clockInv C q.2))⁻¹) (Set.univ ×ˢ Set.Ico (0 : ℝ) C.T) := by
    have h : ContinuousOn (fun q : EuclideanSpace ℝ (Fin 3) × ℝ =>
        (C.A (Work.FTS.Physical.clockInv C q.2))⁻¹) (Set.univ ×ˢ Set.Ico (0 : ℝ) C.T) :=
      hAinv.comp
        (g := fun t : ℝ => (C.A (Work.FTS.Physical.clockInv C t))⁻¹)
        (f := fun q : EuclideanSpace ℝ (Fin 3) × ℝ => q.2)
        (continuous_snd : Continuous (fun q : EuclideanSpace ℝ (Fin 3) × ℝ => q.2)).continuousOn
        (fun _ hq => hq.2)
    simpa only [Function.comp_def] using h
  have hH : ContinuousOn (fun q : EuclideanSpace ℝ (Fin 3) × ℝ =>
      - ((C.A (Work.FTS.Physical.clockInv C q.2))⁻¹ •
        FiniteTimeSingularity.timeDeriv (Work.FTS.Regularity.physVort α A B g) q.1
          (Work.FTS.Physical.clockInv C q.2)))
      (Set.univ ×ˢ Set.Ico (0 : ℝ) C.T) :=
    (h1.smul hB).neg
  refine hH.congr (fun q hq => ?_)
  exact Support.timeDeriv_physOmega_eq hα hreg q.1 hq.2

end Work.FTS.FireFix.Clauses
