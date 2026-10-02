import Mathlib
import Submission.Work.MRMT.Found.fw_decay_cauchyTransform_le
import Submission.Work.MRMT.Found.fw_memLp_dzbar
import Submission.Work.MRMT.Found.fw_ae_eq_hsolA_of_ae_eq_mul_one_add
import Submission.Work.MRMT.Found.forward_limit_pd
import Submission.Work.MRMT.Found.principalData_aux
import Submission.Work.MRMT.Found.hsolA_spec

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FBif

open MeasureTheory Filter Topology Complex Function
open scoped Distributions Topology ENNReal
open Work.MRMT Work.MRMT.Found

/-- **Uniform decay of a family of `C¹` Beltrami solutions.**

For smooth compactly supported coefficients `μn` with a *uniform* bound `k < 1` in sup-norm and a
*uniform* support radius `M`, the `C¹` homeomorphisms `Fn : ℂ ≃ₜ ℂ` solving the Beltrami equation
`∂̄ (Fn) = μn · ∂ (Fn)` and normalised at infinity by `Fn z = z + O(1/‖z‖)` satisfy an explicit
decay bound depending only on `k` and `M`.

The classical proof (Ahlfors--Bers) normalises `Fn(z) - z = cauchyTransform (∂̄ Fn) z`; the energy
bound `∫ ‖∂̄ Fn‖² ≤ (k √(area)/(1 - k))²` for the normalised solution, together with
Cauchy--Schwarz on the support, bounds the Cauchy transform of `∂̄ Fn` by
`2 E √(area) / (π ‖z‖)`.  All ingredients are available in `Work.MRMT.Found`:
`fw_memLp_dzbar`, `fw_ae_eq_hsolA_of_ae_eq_mul_one_add`, `fpd_hsolA_norm_le`,
`fpd_norm_sq_Lp`, `fpd_sub_id_eq_cauchyTransform_dzbar` and `fw_decay_cauchyTransform_le`. -/
theorem qc_decay_uniform {μn : ℕ → ℂ → ℂ} {Fn : ℕ → ℂ ≃ₜ ℂ} {k M : ℝ}
    (hk0 : 0 ≤ k) (hk1 : k < 1) (hM0 : 0 ≤ M)
    (hμnC : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (μn n))
    (hμnS : ∀ n, HasCompactSupport (μn n))
    (hμnB : ∀ n z, ‖μn n z‖ ≤ k)
    (hμnSp : ∀ n z, μn n z ≠ 0 → ‖z‖ ≤ M)
    (hFC : ∀ n, ContDiff ℝ 1 (Fn n : ℂ → ℂ))
    (hFB : ∀ n z, Work.MRMT.dzbar (Fn n : ℂ → ℂ) z = μn n z * Work.MRMT.dz (Fn n : ℂ → ℂ) z)
    (hFD : ∀ n, ∃ C R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ → ‖Fn n z - z‖ ≤ C / ‖z‖) :
    ∀ n z, max (2 * M) 1 ≤ ‖z‖ →
      ‖Fn n z - z‖ ≤
        (2 * (k * Real.sqrt ((MeasureTheory.volume (Metric.closedBall (0 : ℂ) M)).toReal) / (1 - k))
          * Real.sqrt ((MeasureTheory.volume (Metric.closedBall (0 : ℂ) M)).toReal) / Real.pi) / ‖z‖ := by
  intro n z hz
  have hk1pos : 0 < 1 - k := by linarith
  have hE0 : 0 ≤ k * Real.sqrt ((volume (Metric.closedBall (0 : ℂ) M)).toReal) / (1 - k) := by
    positivity
  have hAdmn : Admissible (μn n) :=
    ⟨(hμnC n).continuous.aestronglyMeasurable, ⟨k, hk1, ae_of_all _ (hμnB n)⟩,
      (hμnS n).isBounded.subset subset_closure⟩
  have hLpn : MemLp (μn n) 2 (volume : Measure ℂ) :=
    (hμnC n).continuous.memLp_of_hasCompactSupport (hμnS n)
  have hbn : ∀ᵐ z ∂(volume : Measure ℂ), ‖μn n z‖ ≤ k := ae_of_all _ (hμnB n)
  obtain ⟨hmem, hcs⟩ := fw_memLp_dzbar (hFC n) (hμnS n) (hμnB n) (hFB n)
  have heq : (fun z => dzbar (Fn n : ℂ → ℂ) z) =ᵐ[(volume : Measure ℂ)]
      ((hsolA (μn n) hAdmn hLpn : Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) := by
    refine fw_ae_eq_hsolA_of_ae_eq_mul_one_add hk1 hAdmn hLpn hmem hbn ?_
    filter_upwards [dz_sub_one_eq_beurlingL2_pd (hFC n) (hFD n) hcs hmem] with w hw
    rw [hFB n w]
    have hw' : dz (Fn n : ℂ → ℂ) w
        = 1 + ((beurlingL2 (hmem.toLp (fun z => dzbar (Fn n : ℂ → ℂ) z)) :
            Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ) w := by
      linear_combination hw
    rw [hw']
  have htoLp : hmem.toLp (fun z => dzbar (Fn n : ℂ → ℂ) z) = hsolA (μn n) hAdmn hLpn := by
    rw [Lp.ext_iff]
    exact (MemLp.coeFn_toLp hmem).trans heq
  have hnorm : ‖hsolA (μn n) hAdmn hLpn‖
      ≤ k * Real.sqrt ((volume (Metric.closedBall (0 : ℂ) M)).toReal) / (1 - k) :=
    fpd_hsolA_norm_le hk0 hk1 hAdmn hLpn hbn (hμnSp n)
  have hEint : ∫ w, ‖dzbar (Fn n : ℂ → ℂ) w‖ ^ 2
      ≤ (k * Real.sqrt ((volume (Metric.closedBall (0 : ℂ) M)).toReal) / (1 - k)) ^ 2 := by
    have h2 : ∫ w, ‖dzbar (Fn n : ℂ → ℂ) w‖ ^ 2 = ‖hsolA (μn n) hAdmn hLpn‖ ^ 2 := by
      rw [← fpd_norm_sq_Lp (hsolA (μn n) hAdmn hLpn), ← htoLp]
      apply integral_congr_ae
      filter_upwards [MemLp.coeFn_toLp hmem] with w hw
      rw [hw]
    rw [h2]
    exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  have hmain := fw_decay_cauchyTransform_le (ω := fun w => dzbar (Fn n : ℂ → ℂ) w)
    (M := M) (E := k * Real.sqrt ((volume (Metric.closedBall (0 : ℂ) M)).toReal) / (1 - k))
    hM0 hE0 hmem (fun w hw => hμnSp n w (fun h0 => hw (by rw [hFB n w, h0, zero_mul]))) hEint
  rw [fpd_sub_id_eq_cauchyTransform_dzbar (hFC n) hcs (hFD n) z]
  exact hmain z hz

end Work.FBif
