import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Submission.Work.BoseBoxFock.aliasImageIdentity
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.touchingSum_fourierForm` — the bricks of the touching-image Fourier form

The six *touching* images of the autocorrelation (the lattice vectors `m` with `‖latVec m‖ = 1`)
are the only images whose `p`-symbol is *not* exponentially small; the reduction of the touching
sum to the `p`-integral

    Σ_{‖latVec m‖ = 1} ∫_u 𝒢(u)‖u − ℓ•latVec m‖⁻⁴ du
      = −π²(2π)⁻³ ∫_p ‖p‖‖kinFT g p‖² Σ_{‖latVec m‖ = 1} cos(inner ℝ (ℓ•latVec m) p) dp

**Proof route** (heat side, so no finite-part subtleties appear):

1. per `m ≠ 0`, `Work.BoseBoxFock.imageHeat_swap` converts the Riesz image into the `t`-integral
   of the heat image;
2. `Work.BoseBoxFock.heatImage_fourierForm` is the exact Fourier form of the heat image
   (pointwise in `t > 0`);
3. `Work.BoseBoxFock.heatImage_t_rpow` produces the factor `−π²‖p‖` (via the subordination
   `∫_{t>0} t^{-3/2}(e^{-tc}−1)dt = −2√π√c`);
4. summing over the six touching lattice vectors gives the statement.

The *arithmetic of the constants* is `(π^{3/2}/2)·(2π)⁻³·(−2√π) = −π²(2π)⁻³`, i.e.
`π^{3/2}√π = π²`.

**Status.**  This file contains only the *bricks* (sorry-free): the tangency vanishing on the
closed-ball class, the compact support, the identification of `imgW`, and the finite box
`{-1,0,1}³` that carries the six touching lattice vectors.  The two Fourier-form statements built
on them are filed as `Work.BoseBoxFock.touchingFourierForm`
(`Submission/Work/BoseBoxFock/touchingFourierForm.lean`), whose proof is the assembly above.
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1600000

/-! ## 1. The tangency vanishing on the closed-ball class -/

/-- The sphere `{x | ‖x‖ = r}` has measure zero in `ℝ³`. -/
private lemma volume_sphere_eq_zero (r : ℝ) :
    volume {x : E3 | ‖x‖ = r} = 0 := by
  refine measure_mono_null ?_ (MeasureTheory.Measure.addHaar_sphere (μ := volume) (0 : E3) r)
  intro x hx
  simp only [Set.mem_ofPred_eq] at hx
  rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
  exact hx

/-- **The tangency vanishing (closed-ball class).** -/
theorem aliasKernel_latVec_eq_zero_closed {ℓ : ℝ} (hℓ : 0 < ℓ) {g : E3 → ℂ}
    (hg : ContDiff ℝ (⊤ : ENat) g)
    (hgsupp : tsupport g ⊆ Metric.closedBall 0 (ℓ / 2))
    {m : Fin 3 → ℤ} (hm : m ≠ 0) : aliasKernel g (ℓ • latVec m) = 0 := by
  have h1 : 1 ≤ ‖latVec m‖ := one_le_norm_latVec hm
  have hbad : {x : E3 | g x * (starRingEnd ℂ) (g (x - ℓ • latVec m)) ≠ 0}
      ⊆ {x : E3 | ‖x‖ = ℓ / 2} := by
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    have hx1 : g x ≠ 0 := fun h => hx (by simp [h])
    have hx2 : g (x - ℓ • latVec m) ≠ 0 := fun h => hx (by simp [h])
    have hmem1 : ‖x‖ ≤ ℓ / 2 := by
      have := hgsupp (subset_closure (Function.mem_support.mpr hx1))
      rwa [Metric.mem_closedBall, dist_eq_norm, sub_zero] at this
    have hmem2 : ‖x - ℓ • latVec m‖ ≤ ℓ / 2 := by
      have := hgsupp (subset_closure (Function.mem_support.mpr hx2))
      rwa [Metric.mem_closedBall, dist_eq_norm, sub_zero] at this
    have hsl : ℓ ≤ ‖ℓ • latVec m‖ := by
      rw [norm_smul, Real.norm_of_nonneg hℓ.le]
      calc ℓ = ℓ * 1 := (mul_one ℓ).symm
        _ ≤ ℓ * ‖latVec m‖ := mul_le_mul_of_nonneg_left h1 hℓ.le
    have htri : ‖ℓ • latVec m‖ ≤ ‖x‖ + ‖x - ℓ • latVec m‖ := by
      have h := norm_add_le x (ℓ • latVec m - x)
      have h1 : x + (ℓ • latVec m - x) = ℓ • latVec m := by abel
      rw [h1, norm_sub_rev (ℓ • latVec m) x] at h
      exact h
    linarith
  rw [aliasKernel]
  have hzero : (fun x : E3 => g x * (starRingEnd ℂ) (g (x - ℓ • latVec m))) =ᵐ[volume] 0 := by
    rw [Filter.EventuallyEq, MeasureTheory.ae_iff]
    exact measure_mono_null hbad (volume_sphere_eq_zero (ℓ / 2))
  rw [show autocorr g (ℓ • latVec m)
      = ∫ x : E3, g x * (starRingEnd ℂ) (g (x - ℓ • latVec m)) from rfl,
    MeasureTheory.integral_eq_zero_of_ae hzero]
  simp

/-- `g` smooth with closed-ball support has compact support. -/
theorem hcc_of_closedBall {ℓ : ℝ} {g : E3 → ℂ}
    (hgsupp : tsupport g ⊆ Metric.closedBall 0 (ℓ / 2)) : HasCompactSupport g := by
  rw [HasCompactSupport, Metric.isCompact_iff_isClosed_bounded]
  exact ⟨isClosed_tsupport g, (Metric.isBounded_closedBall).subset hgsupp⟩

/-! ## 2. The per-`m` weight and the finite box of the touching lattice vectors -/

/-- For `m ≠ 0`, `imgW ℓ m u = (‖u - ℓ • latVec m‖ ^ 4)⁻¹`. -/
theorem imgW_eq_of_ne_zero {ℓ : ℝ} {m : Fin 3 → ℤ} (hm : m ≠ 0) (u : E3) :
    imgW ℓ m u = (‖u - ℓ • latVec m‖ ^ 4)⁻¹ := imgW_ne_zero hm u

/-- The box `{-1,0,1}³` in `ℤ³`. -/
def unitBox : Finset (Fin 3 → ℤ) :=
  Fintype.piFinset (fun _ : Fin 3 => ({-1, 0, 1} : Finset ℤ))

/-- Every lattice vector of norm `1` lies in the box `{-1,0,1}³` (its squared norm is the sum of
the squares of its three integer coordinates). -/
theorem mem_unitBox_of_norm_eq_one {m : Fin 3 → ℤ} (hm : ‖latVec m‖ = 1) :
    m ∈ unitBox := by
  rw [unitBox, Fintype.mem_piFinset]
  intro i
  have hsq : ‖latVec m‖ ^ 2 = ∑ i, ((m i : ℝ)) ^ 2 := by
    rw [latVec, PiLp.norm_sq_eq_of_L2]
    simp
  have hone : ∑ i, ((m i : ℝ)) ^ 2 = 1 := by rw [← hsq, hm]; norm_num
  have hle : ((m i : ℝ)) ^ 2 ≤ 1 := by
    rw [← hone]
    exact Finset.single_le_sum (fun j _ => sq_nonneg ((m j : ℝ))) (Finset.mem_univ i)
  have habs : |((m i : ℤ) : ℝ)| ≤ 1 := by
    rw [← Real.sqrt_sq_eq_abs, Real.sqrt_le_one]
    exact hle
  have hz : |m i| ≤ 1 := by exact_mod_cast habs
  have h3 : m i ≤ 1 := (abs_le.mp hz).2
  have h4 : -1 ≤ m i := (abs_le.mp hz).1
  simp only [Finset.mem_insert, Finset.mem_singleton]
  omega

/-- A lattice vector of norm `1` is nonzero. -/
theorem latVec_ne_zero_of_norm_eq_one {m : Fin 3 → ℤ} (hm : ‖latVec m‖ = 1) : m ≠ 0 := by
  intro h
  rw [h, aliasLatVec_zero, norm_zero] at hm
  exact one_ne_zero hm.symm

end Work.BoseBoxFock
