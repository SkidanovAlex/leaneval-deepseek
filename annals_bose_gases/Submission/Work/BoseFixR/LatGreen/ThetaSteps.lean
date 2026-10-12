import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.BoseFixR.LatGreen.HeatK1Aux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.LatGreen.ThetaSteps` — the Fubini steps of Poisson/Jacobi summation in `ℝ³`

`heatPeriod_eq_thetaSum`: the `ℤ³`-periodisation of the three-dimensional heat kernel factorises
into the product of the three one-dimensional periodisations (the coordinate splitting
`piFinThreeEquiv` turns the `ℤ³`-sum into a triple sum, which is a product of sums by
`tsum_mul_tsum_of_summable_norm`).

`thetaTerm1_tsum_mul_eq_thetaTerm_tsum`: conversely the product of the three one-dimensional
Fourier series reassembles into the three-dimensional Fourier series.
-/

set_option maxHeartbeats 1000000

noncomputable section

open scoped Real BigOperators
open MeasureTheory Set

namespace Work.BoseFixR.LatGreen

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The three-dimensional Fourier terms are absolutely summable (their norm is
`exp(−4π²t‖k‖²)`, a Gaussian over `ℤ³`). -/
theorem summable_thetaTerm {t : ℝ} (ht : 0 < t) (u : ℝ³) :
    Summable fun k : Fin 3 → ℤ => thetaTerm t u k := by
  have h0 : Summable fun m : ℤ => ‖thetaTerm1 t (u 0) m‖ := summable_thetaTerm1 ht (u 0)
  have h1 : Summable fun m : ℤ => ‖thetaTerm1 t (u 1) m‖ := summable_thetaTerm1 ht (u 1)
  have h2 : Summable fun m : ℤ => ‖thetaTerm1 t (u 2) m‖ := summable_thetaTerm1 ht (u 2)
  have h12n : Summable fun q : ℤ × ℤ =>
      ‖thetaTerm1 t (u 1) q.1 * thetaTerm1 t (u 2) q.2‖ := h1.mul_norm h2
  have h012 : Summable fun p : ℤ × ℤ × ℤ =>
      thetaTerm1 t (u 0) p.1 * (thetaTerm1 t (u 1) p.2.1 * thetaTerm1 t (u 2) p.2.2) :=
    summable_mul_of_summable_norm (f := fun m : ℤ => thetaTerm1 t (u 0) m)
      (g := fun q : ℤ × ℤ => thetaTerm1 t (u 1) q.1 * thetaTerm1 t (u 2) q.2) h0 h12n
  rw [← Equiv.summable_iff piFinThreeEquiv.symm]
  change Summable fun p : ℤ × ℤ × ℤ => thetaTerm t u (piFinThreeEquiv.symm p)
  have h : (fun p : ℤ × ℤ × ℤ => thetaTerm t u (piFinThreeEquiv.symm p))
      = fun p : ℤ × ℤ × ℤ =>
          thetaTerm1 t (u 0) p.1 * (thetaTerm1 t (u 1) p.2.1 * thetaTerm1 t (u 2) p.2.2) := by
    funext p
    exact (prod_thetaTerm1_eq_thetaTerm t u (piFinThreeEquiv.symm p)).symm
  rw [h]
  exact h012

/-- The `ℤ³`-periodisation of the three-dimensional heat kernel is the product of the three
one-dimensional periodisations. -/
theorem heatPeriod_eq_prod {t : ℝ} (ht : 0 < t) (u : ℝ³) :
    heatPeriod t u
      = (∑' m : ℤ, heatK1 t (u 0 - m))
        * ((∑' m : ℤ, heatK1 t (u 1 - m)) * (∑' m : ℤ, heatK1 t (u 2 - m))) := by
  have hA : Summable fun m : ℤ => heatK1 t (u 0 - m) := summable_heatK1 ht (u 0)
  have hB : Summable fun m : ℤ => heatK1 t (u 1 - m) := summable_heatK1 ht (u 1)
  have hC : Summable fun m : ℤ => heatK1 t (u 2 - m) := summable_heatK1 ht (u 2)
  have hBC : Summable fun q : ℤ × ℤ => heatK1 t (u 1 - q.1) * heatK1 t (u 2 - q.2) :=
    Summable.mul_of_nonneg hB hC (fun _ => heatK1_nonneg ht _) (fun _ => heatK1_nonneg ht _)
  have hABC : Summable fun p : ℤ × ℤ × ℤ =>
      heatK1 t (u 0 - p.1) * (heatK1 t (u 1 - p.2.1) * heatK1 t (u 2 - p.2.2)) :=
    Summable.mul_of_nonneg hA hBC (fun _ => heatK1_nonneg ht _)
      (fun q => mul_nonneg (heatK1_nonneg ht _) (heatK1_nonneg ht _))
  have hterm : ∀ n : Fin 3 → ℤ, heatK3 t (u - latVec n)
      = heatK1 t (u 0 - (n 0 : ℝ))
        * (heatK1 t (u 1 - (n 1 : ℝ)) * heatK1 t (u 2 - (n 2 : ℝ))) := by
    intro n
    rw [heatK3_eq_prod_heatK1 ht]
    simp only [sub_latVec_apply]
    ring
  calc heatPeriod t u
      = ∑' n : Fin 3 → ℤ, heatK3 t (u - latVec n) := by rw [heatPeriod]
    _ = ∑' n : Fin 3 → ℤ, heatK1 t (u 0 - (n 0 : ℝ))
          * (heatK1 t (u 1 - (n 1 : ℝ)) * heatK1 t (u 2 - (n 2 : ℝ))) :=
        tsum_congr hterm
    _ = ∑' p : ℤ × ℤ × ℤ, heatK1 t (u 0 - (p.1 : ℝ))
          * (heatK1 t (u 1 - (p.2.1 : ℝ)) * heatK1 t (u 2 - (p.2.2 : ℝ))) := by
        have h := Equiv.tsum_eq piFinThreeEquiv
          (fun p : ℤ × ℤ × ℤ => heatK1 t (u 0 - (p.1 : ℝ))
              * (heatK1 t (u 1 - (p.2.1 : ℝ)) * heatK1 t (u 2 - (p.2.2 : ℝ))))
        simpa using h
    _ = (∑' m : ℤ, heatK1 t (u 0 - m))
        * ((∑' m : ℤ, heatK1 t (u 1 - m)) * (∑' m : ℤ, heatK1 t (u 2 - m))) := by
        rw [← Summable.tsum_mul_tsum (f := fun m : ℤ => heatK1 t (u 0 - m))
          (g := fun q : ℤ × ℤ => heatK1 t (u 1 - q.1) * heatK1 t (u 2 - q.2)) hA hBC hABC]
        congr 1
        exact (Summable.tsum_mul_tsum (f := fun m : ℤ => heatK1 t (u 1 - m))
          (g := fun m : ℤ => heatK1 t (u 2 - m)) hB hC hBC).symm

/-- The product of the three one-dimensional Fourier series is the three-dimensional Fourier
series. -/
theorem thetaTerm1_tsum_mul_eq_thetaTerm_tsum {t : ℝ} (ht : 0 < t) (u : ℝ³) :
    (∑' m : ℤ, thetaTerm1 t (u 0) m)
        * ((∑' m : ℤ, thetaTerm1 t (u 1) m) * (∑' m : ℤ, thetaTerm1 t (u 2) m))
      = ∑' k : Fin 3 → ℤ, thetaTerm t u k := by
  have h0n : Summable fun m : ℤ => ‖thetaTerm1 t (u 0) m‖ := summable_thetaTerm1 ht (u 0)
  have h1n : Summable fun m : ℤ => ‖thetaTerm1 t (u 1) m‖ := summable_thetaTerm1 ht (u 1)
  have h2n : Summable fun m : ℤ => ‖thetaTerm1 t (u 2) m‖ := summable_thetaTerm1 ht (u 2)
  have h12n : Summable fun q : ℤ × ℤ =>
      ‖thetaTerm1 t (u 1) q.1 * thetaTerm1 t (u 2) q.2‖ := h1n.mul_norm h2n
  calc (∑' m : ℤ, thetaTerm1 t (u 0) m)
        * ((∑' m : ℤ, thetaTerm1 t (u 1) m) * (∑' m : ℤ, thetaTerm1 t (u 2) m))
      = (∑' m : ℤ, thetaTerm1 t (u 0) m)
          * (∑' q : ℤ × ℤ, thetaTerm1 t (u 1) q.1 * thetaTerm1 t (u 2) q.2) := by
        rw [tsum_mul_tsum_of_summable_norm (f := fun m : ℤ => thetaTerm1 t (u 1) m)
          (g := fun m : ℤ => thetaTerm1 t (u 2) m) h1n h2n]
    _ = ∑' p : ℤ × ℤ × ℤ,
          thetaTerm1 t (u 0) p.1 * (thetaTerm1 t (u 1) p.2.1 * thetaTerm1 t (u 2) p.2.2) := by
        rw [tsum_mul_tsum_of_summable_norm (f := fun m : ℤ => thetaTerm1 t (u 0) m)
          (g := fun q : ℤ × ℤ => thetaTerm1 t (u 1) q.1 * thetaTerm1 t (u 2) q.2) h0n h12n]
    _ = ∑' k : Fin 3 → ℤ,
          thetaTerm1 t (u 0) (k 0) * (thetaTerm1 t (u 1) (k 1) * thetaTerm1 t (u 2) (k 2)) := by
        simpa using (Equiv.tsum_eq piFinThreeEquiv
          (fun p : ℤ × ℤ × ℤ => thetaTerm1 t (u 0) p.1
            * (thetaTerm1 t (u 1) p.2.1 * thetaTerm1 t (u 2) p.2.2))).symm
    _ = ∑' k : Fin 3 → ℤ, thetaTerm t u k :=
        tsum_congr (fun k => prod_thetaTerm1_eq_thetaTerm t u k)

/-- Real part of a three-dimensional Fourier term. -/
theorem thetaTerm_re (t : ℝ) (u : ℝ³) (k : Fin 3 → ℤ) :
    (thetaTerm t u k).re
      = Real.exp (-(4 * Real.pi ^ 2 * t) * ‖latVec k‖ ^ 2)
        * Real.cos (2 * Real.pi * ∑ i, (k i : ℝ) * u i) := by
  set θ : ℂ := (((∑ i, (k i : ℝ) * u i) : ℝ) : ℂ) with hθ
  have hre : (-(2 * Real.pi * Complex.I * θ)).re = 0 := by
    simp [hθ]
  have him : (-(2 * Real.pi * Complex.I * θ)).im
      = -(2 * Real.pi * ∑ i, (k i : ℝ) * u i) := by
    simp [hθ]
  unfold thetaTerm
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.exp_re, hre, him,
    Real.exp_zero, one_mul, zero_mul, sub_zero, Real.cos_neg]

end Work.BoseFixR.LatGreen
