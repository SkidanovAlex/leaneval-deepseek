import Mathlib
import Submission.Work.Area.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The image of a circle under a one-pole map is a null set

For `F z = 1/z + H z` on the punctured unit disc (with `H` holomorphic on the disc) and
`0 < r < 1`, the image of the circle `|z| = r` under `F` has two-dimensional Lebesgue
measure zero.

The proof is a Hausdorff-dimension argument.

* `F` is complex differentiable on the punctured disc `𝔻 \ {0}` (it agrees there with the
  holomorphic map `z ↦ 1/z + H z`), hence on the circle `|z| = r ⊂ 𝔻 \ {0}`, so
  `DifferentiableOn.dimH_image_le` gives `dimH (F '' sphere) ≤ dimH (sphere)`.
* The circle is the image of the interval `[-π, π]` under `circleMap 0 r`, which is
  differentiable, whence `dimH (sphere) ≤ dimH ([-π, π]) = 1`.
* Since `1 < 2`, `dimH (F '' sphere) < 2`, and the two-dimensional Hausdorff measure
  `μH[2]` of that set vanishes; as `volume = c • μH[2]` on `ℂ` (via
  `euclideanHausdorffMeasure`), `volume` of the image is zero as well.

Note that the injectivity hypothesis is not needed.
-/

namespace Work.Area

open MeasureTheory Set

theorem img_sphere_null (F H : ℂ → ℂ) (hH : DifferentiableOn ℂ H (Metric.ball 0 1))
    (hF : Set.InjOn F (Metric.ball 0 1 \ {0}))
    (hexp : ∀ z ∈ Metric.ball 0 1 \ {0}, F z = 1 / z + H z)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    MeasureTheory.volume (F '' (Metric.sphere 0 r)) = 0 := by
  -- `F` agrees with a holomorphic map on the punctured disc, hence is complex differentiable there.
  have hFd : DifferentiableOn ℂ F (Metric.ball 0 1 \ {0}) := by
    have hG : DifferentiableOn ℂ (fun z : ℂ => 1 / z + H z) (Metric.ball 0 1 \ {0}) := by
      intro z hz
      have hz0 : z ≠ 0 := hz.2
      have hHd : DifferentiableAt ℂ H z := hH.differentiableAt (Metric.isOpen_ball.mem_nhds hz.1)
      exact (((differentiableAt_const (1:ℂ)).div differentiableAt_id hz0).add hHd).differentiableWithinAt
    exact hG.congr (fun z hz => hexp z hz)
  -- The circle of radius `r < 1` is contained in the punctured unit disc.
  have hsub : Metric.sphere (0:ℂ) r ⊆ Metric.ball (0:ℂ) 1 \ {0} := by
    intro z hz
    rw [mem_sphere_zero_iff_norm] at hz
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_ball, dist_eq_norm, sub_zero, hz]; exact hr1
    · intro h0
      rw [h0, norm_zero] at hz
      linarith
  -- `F` is injective on the circle as well (not needed below, but part of the setting).
  have hFinj : Set.InjOn F (Metric.sphere (0:ℂ) r) := Set.InjOn.mono hsub hF
  -- The circle of radius `r` is the image of `[-π, π]` under `circleMap 0 r`.
  have hγ : circleMap 0 r '' (Set.Icc (-Real.pi) Real.pi) = Metric.sphere (0:ℂ) r := by
    ext z
    constructor
    · rintro ⟨θ, -, rfl⟩
      rw [mem_sphere_zero_iff_norm, circleMap_zero]
      simp [Complex.norm_exp_ofReal_mul_I, abs_of_pos hr]
    · intro hz
      rw [mem_sphere_zero_iff_norm] at hz
      refine ⟨z.arg, ⟨le_of_lt (Complex.arg_mem_Ioc z).1, (Complex.arg_mem_Ioc z).2⟩, ?_⟩
      rw [circleMap_zero, ← hz, Complex.norm_mul_exp_arg_mul_I]
  have hγd : DifferentiableOn ℝ (circleMap 0 r) (Set.Icc (-Real.pi) Real.pi) := by
    have hf : circleMap 0 r = fun θ : ℝ => (r : ℂ) * Complex.exp (↑θ * Complex.I) := by
      funext θ; exact circleMap_zero r θ
    rw [hf]; fun_prop
  have hFR : DifferentiableOn ℝ F (Metric.sphere (0:ℂ) r) := (hFd.mono hsub).restrictScalars ℝ
  have hcomp : DifferentiableOn ℝ (F ∘ circleMap 0 r) (Set.Icc (-Real.pi) Real.pi) :=
    hFR.comp hγd (fun θ _ => circleMap_mem_sphere 0 hr.le θ)
  -- Hausdorff dimension of the image is at most that of the parameter interval.
  have hB : dimH (F '' Metric.sphere (0:ℂ) r) ≤ dimH (Set.Icc (-Real.pi) Real.pi : Set ℝ) := by
    rw [← hγ, image_image]
    exact hcomp.dimH_image_le
  have hI : dimH (Set.Icc (-Real.pi) Real.pi : Set ℝ) = 1 := by
    rw [Real.dimH_of_mem_nhds (x := (0:ℝ))
      (Icc_mem_nhds (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]))]
    simp
  -- Hence `dimH (F '' sphere 0 r) < 2`.
  have hdH : dimH (F '' Metric.sphere (0:ℂ) r) < (2 : NNReal) := by
    have h2 : dimH (F '' Metric.sphere (0:ℂ) r) ≤ 1 := by rw [← hI]; exact hB
    calc dimH (F '' Metric.sphere (0:ℂ) r) ≤ 1 := h2
      _ < (2 : NNReal) := by norm_num
  -- `volume` on `ℂ` is a non-zero multiple of the two-dimensional Hausdorff measure.
  have hac : MeasureTheory.volume ≪
      (MeasureTheory.Measure.hausdorffMeasure (((2:NNReal):ℝ)) : Measure ℂ) := by
    have hvol : (MeasureTheory.Measure.euclideanHausdorffMeasure 2 : Measure ℂ) =
        MeasureTheory.volume := by
      have h := InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := ℂ)
      simpa [Complex.finrank_real_complex] using h
    rw [← hvol, MeasureTheory.Measure.euclideanHausdorffMeasure_def]
    intro s hs
    have key : (MeasureTheory.Measure.hausdorffMeasure (((2:ℕ):ℝ)) : Measure ℂ) s = 0 := by
      simpa using hs
    rw [Measure.smul_apply, key, smul_zero]
  exact measure_zero_of_dimH_lt hac hdH

end Work.Area
