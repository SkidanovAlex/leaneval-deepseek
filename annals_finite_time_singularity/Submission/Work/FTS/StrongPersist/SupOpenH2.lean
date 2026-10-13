import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.L3Rhs.AuxAgmon
import Submission.Work.FTS.StrongPersist.SupOpenH2Defs
import Submission.Work.FTS.StrongPersist.SupOpenH2A
import Submission.Work.FTS.StrongPersist.SupOpenH2B
import Submission.Work.H2.T1Q.SliceSupOpen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.StrongPersist.SupOpenH2` — the open-quadrant Agmon bound

`|h z θ| ≤ C α^{-1/2} |h|_{ℋ²}` on the open quadrant `Q0`, for `h` only assumed `C^∞` on the
open quadrant and honestly in `ℋ²` (`HQo α 2 h`).

Route.  Fix `(z,θ) ∈ Q0`, `z > 0`.  The angular Agmon inequality
`Work.H2.T1Q.SliceSupOpen` bounds `h(z,θ)²` by the two angular integrals
`∫_θ h(z,·)²` and `∫_θ (∂_θh)² sin(2θ)^{2-γ}` at the fixed radius `z`; multiplying by the radial
weight `(w z)² z` converts these into the two `θ`-integrated quantities
`z(w z)² ∫_θ h²σ^{-η}` and `z(w z)² ∫_θ (D_θh)²σ^{-γ}`, which are bounded at `z` by their global
`ℋ²`-integrals (`zavg_A`, `zavg_B`, via the "log-window averaging" of `SupOpenH2Z`), using
`(w z)² z ≥ 256/27` (`w_sq_mul_self_ge`) to undo the radial weight.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist

set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option linter.unusedVariables false

theorem SupOpenH2 : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 →
    ∀ h : Work.FTS.Galerkin.Fn, Work.FTS.VocabO.HQo α 2 h →
    ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      |h z θ| ≤ C * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 2 h := by
  refine ⟨100, by norm_num, ?_⟩
  intro α hα hα1 h hQ z θ hzθ
  obtain ⟨hso, hmem⟩ := hQ
  obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hzθ
  have hθmem : θ ∈ Set.Ioo 0 (π / 2) := ⟨hθ0, hθ1⟩
  have hγ1 : 1 < Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith
  have hγm1 : Work.Spaces.gam α - 1 = α / 10 := by rw [Work.Spaces.gam]; ring
  -- ## the angular Agmon inequality at radius `z`
  have hslice : ContDiffOn ℝ 1 (fun θ' => h z θ') (Set.Ioo 0 (π / 2)) := by
    have hsle : (1 : WithTop ℕ∞) ≤ Work.Stability.smoothOrder := by
      rw [Work.Stability.smoothOrder]
      exact WithTop.coe_le_coe.mpr le_top
    exact (Work.FTS.LocData.contDiffOn_slice_θ hso hz).of_le hsle
  have hu2 : IntegrableOn (fun θ' => (h z θ') ^ 2) Work.Spaces.Iθ := integrableOn_hsq hso hmem hz
  have hint2 : IntegrableOn (fun θ' => (Work.Spaces.pth h z θ') ^ 2
      * (Real.sin (2 * θ')) ^ (2 - Work.Spaces.gam α)) Work.Spaces.Iθ :=
    integrableOn_pth_sq hα hα1 hso hmem hz
  have hsup := Work.H2.T1Q.SliceSupOpen α (fun θ' => h z θ') hα hα1 hslice hu2 hint2 θ hθmem
  -- ## weighted comparison of the plain angular `L²`-norm
  have hint1 : IntegrableOn (fun θ' => (h z θ') ^ 2
      * (Real.sin (2 * θ')) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ :=
    integrableOn_hsq_sEta hso hmem hz
  have hcmp := int_sq_le_two_weighted (aesm_sq_slice_of_SmoothOpen hso hz) hint1
  -- ## convert `∂_θ` to `D_θ`
  have hconv : (∫ θ' in Work.Spaces.Iθ, (Work.Spaces.pth h z θ') ^ 2
        * (Real.sin (2 * θ')) ^ (2 - Work.Spaces.gam α))
      = ∫ θ' in Work.Spaces.Iθ, (Work.Spaces.Dth h z θ') ^ 2
        * (Real.sin (2 * θ')) ^ (-(Work.Spaces.gam α)) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ' hθ' => ?_
    show (Work.Spaces.pth h z θ') ^ 2 * (Real.sin (2 * θ')) ^ (2 - Work.Spaces.gam α)
      = (Work.Spaces.Dth h z θ') ^ 2 * (Real.sin (2 * θ')) ^ (-(Work.Spaces.gam α))
    rw [show Work.Spaces.Dth h z θ' = Real.sin (2 * θ') * Work.Spaces.pth h z θ' from rfl]
    rw [show (Real.sin (2 * θ') * Work.Spaces.pth h z θ') ^ 2
          * (Real.sin (2 * θ')) ^ (-(Work.Spaces.gam α))
        = (Work.Spaces.pth h z θ') ^ 2
          * ((Real.sin (2 * θ')) ^ 2 * (Real.sin (2 * θ')) ^ (-(Work.Spaces.gam α)))
        from by rw [mul_pow]; ring]
    rw [sin_two_sq_mul_neg_Iθ (p := Work.Spaces.gam α) hθ' (gam_ne_two hα1)]
  -- ## the two `z`-averaging bounds
  have hA := zavg_A hso hmem hz
  have hB := zavg_B hα hso hmem hz
  have hWnn : (0 : ℝ) ≤ (Work.Spaces.w z) ^ 2 * z := by positivity
  have hWge : (256 : ℝ) / 27 ≤ (Work.Spaces.w z) ^ 2 * z := w_sq_mul_self_ge hz
  -- ## combine
  have hstep : (Work.Spaces.w z) ^ 2 * z * (h z θ) ^ 2
      ≤ (8 / Real.pi) * ((Work.Spaces.w z) ^ 2 * z
          * (∫ θ' in Work.Spaces.Iθ, (h z θ') ^ 2 * (Real.sin (2 * θ')) ^ (-(Work.Spaces.eta))))
        + (200 / (Work.Spaces.gam α - 1)) * ((Work.Spaces.w z) ^ 2 * z
          * (∫ θ' in Work.Spaces.Iθ, (Work.Spaces.Dth h z θ') ^ 2
            * (Real.sin (2 * θ')) ^ (-(Work.Spaces.gam α)))) := by
    have hsup' : (h z θ) ^ 2 ≤ (4 / Real.pi) * (∫ θ' in Work.Spaces.Iθ, (h z θ') ^ 2)
        + (200 / (Work.Spaces.gam α - 1)) * (∫ θ' in Work.Spaces.Iθ,
            (Work.Spaces.pth h z θ') ^ 2 * (Real.sin (2 * θ')) ^ (2 - Work.Spaces.gam α)) :=
      hsup
    rw [hconv] at hsup'
    have hcmp2 : (4 / Real.pi) * (∫ θ' in Work.Spaces.Iθ, (h z θ') ^ 2)
        ≤ (8 / Real.pi) * (∫ θ' in Work.Spaces.Iθ,
            (h z θ') ^ 2 * (Real.sin (2 * θ')) ^ (-(Work.Spaces.eta))) := by
      have hml := mul_le_mul_of_nonneg_left hcmp (by positivity : (0:ℝ) ≤ 4 / Real.pi)
      calc (4 / Real.pi) * (∫ θ' in Work.Spaces.Iθ, (h z θ') ^ 2)
          ≤ (4 / Real.pi) * (2 * (∫ θ' in Work.Spaces.Iθ,
              (h z θ') ^ 2 * (Real.sin (2 * θ')) ^ (-(Work.Spaces.eta)))) := hml
        _ = (8 / Real.pi) * (∫ θ' in Work.Spaces.Iθ,
              (h z θ') ^ 2 * (Real.sin (2 * θ')) ^ (-(Work.Spaces.eta))) := by ring
    have h1 : (h z θ) ^ 2 ≤ (8 / Real.pi) * (∫ θ' in Work.Spaces.Iθ,
          (h z θ') ^ 2 * (Real.sin (2 * θ')) ^ (-(Work.Spaces.eta)))
        + (200 / (Work.Spaces.gam α - 1)) * (∫ θ' in Work.Spaces.Iθ,
            (Work.Spaces.Dth h z θ') ^ 2 * (Real.sin (2 * θ')) ^ (-(Work.Spaces.gam α))) := by
      nlinarith [hsup', hcmp2]
    calc (Work.Spaces.w z) ^ 2 * z * (h z θ) ^ 2
        ≤ (Work.Spaces.w z) ^ 2 * z * ((8 / Real.pi) * (∫ θ' in Work.Spaces.Iθ,
              (h z θ') ^ 2 * (Real.sin (2 * θ')) ^ (-(Work.Spaces.eta)))
            + (200 / (Work.Spaces.gam α - 1)) * (∫ θ' in Work.Spaces.Iθ,
                (Work.Spaces.Dth h z θ') ^ 2
                  * (Real.sin (2 * θ')) ^ (-(Work.Spaces.gam α)))) :=
          mul_le_mul_of_nonneg_left h1 hWnn
      _ = (8 / Real.pi) * ((Work.Spaces.w z) ^ 2 * z
            * (∫ θ' in Work.Spaces.Iθ, (h z θ') ^ 2
              * (Real.sin (2 * θ')) ^ (-(Work.Spaces.eta))))
          + (200 / (Work.Spaces.gam α - 1)) * ((Work.Spaces.w z) ^ 2 * z
            * (∫ θ' in Work.Spaces.Iθ, (Work.Spaces.Dth h z θ') ^ 2
              * (Real.sin (2 * θ')) ^ (-(Work.Spaces.gam α)))) := by ring
  have hAB : (8 / Real.pi) * ((Work.Spaces.w z) ^ 2 * z
          * (∫ θ' in Work.Spaces.Iθ, (h z θ') ^ 2 * (Real.sin (2 * θ')) ^ (-(Work.Spaces.eta))))
        + (200 / (Work.Spaces.gam α - 1)) * ((Work.Spaces.w z) ^ 2 * z
          * (∫ θ' in Work.Spaces.Iθ, (Work.Spaces.Dth h z θ') ^ 2
            * (Real.sin (2 * θ')) ^ (-(Work.Spaces.gam α))))
      ≤ ((8 / Real.pi) * 9 + (200 / (Work.Spaces.gam α - 1)) * 9) * Work.Spaces.HkSq α 2 h := by
    have h8 : (0 : ℝ) ≤ 8 / Real.pi := by positivity
    have h200 : (0 : ℝ) ≤ 200 / (Work.Spaces.gam α - 1) := by
      apply div_nonneg (by norm_num); linarith
    have hA' := mul_le_mul_of_nonneg_left hA h8
    have hB' := mul_le_mul_of_nonneg_left hB h200
    linarith [hA', hB']
  have hfac : 200 / (Work.Spaces.gam α - 1) = 2000 / α := by
    rw [hγm1]; field_simp; norm_num
  have hcoef : (27 / 256) * ((8 / Real.pi) * 9 + (200 / (Work.Spaces.gam α - 1)) * 9)
      ≤ 10000 / α := by
    rw [hfac]
    have hπ : 8 / Real.pi ≤ 3 := by
      rw [div_le_iff₀ Real.pi_pos]; linarith [Real.pi_gt_three]
    have h3α : 8 / Real.pi ≤ 3 / α := by
      rw [div_le_div_iff₀ Real.pi_pos hα]
      nlinarith [Real.pi_gt_three, hα.le, hα1]
    have hsum : 8 / Real.pi + 2000 / α ≤ 2003 / α := by
      have h4 : (3 : ℝ) / α + 2000 / α = 2003 / α := by ring
      linarith [h3α, h4]
    have h5 : 2003 / α ≤ 10000 / α :=
      div_le_div_of_nonneg_right (by norm_num) hα.le
    have h6 : (0 : ℝ) ≤ 8 / Real.pi + 2000 / α := by positivity
    have hrel : (27 / 256) * ((8 / Real.pi) * 9 + (2000 / α) * 9)
        = (243 / 256) * (8 / Real.pi + 2000 / α) := by ring
    rw [hrel]
    calc (243 / 256) * (8 / Real.pi + 2000 / α)
        ≤ 1 * (8 / Real.pi + 2000 / α) :=
          mul_le_mul_of_nonneg_right (by norm_num) h6
      _ ≤ 2003 / α := by rw [one_mul]; exact hsum
      _ ≤ 10000 / α := h5
  have hsq : (h z θ) ^ 2 ≤ (10000 / α) * Work.Spaces.HkSq α 2 h := by
    have hWh : (Work.Spaces.w z) ^ 2 * z * (h z θ) ^ 2
        ≤ ((8 / Real.pi) * 9 + (200 / (Work.Spaces.gam α - 1)) * 9)
          * Work.Spaces.HkSq α 2 h := le_trans hstep hAB
    have h1 : (h z θ) ^ 2 ≤ (27 / 256) * ((Work.Spaces.w z) ^ 2 * z * (h z θ) ^ 2) := by
      have hle : (1 : ℝ) ≤ (27 / 256) * ((Work.Spaces.w z) ^ 2 * z) := by linarith [hWge]
      nlinarith [hle, sq_nonneg (h z θ)]
    have hSq : (0 : ℝ) ≤ Work.Spaces.HkSq α 2 h := Work.Spaces.HkSq_nonneg α 2 h
    have h2 : (27 / 256) * (((8 / Real.pi) * 9 + (200 / (Work.Spaces.gam α - 1)) * 9)
          * Work.Spaces.HkSq α 2 h)
        ≤ (10000 / α) * Work.Spaces.HkSq α 2 h := by
      have := hcoef
      nlinarith [this, hSq]
    linarith [h1, hWh, h2]
  -- ## square roots
  have h100 : (0 : ℝ) ≤ 100 * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 2 h := by
    have h1 : (0 : ℝ) ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα.le _
    have h2 : (0 : ℝ) ≤ Work.Spaces.HkNorm α 2 h := Real.sqrt_nonneg _
    exact mul_nonneg (mul_nonneg (by norm_num) h1) h2
  have hsq2 : (h z θ) ^ 2 ≤ (100 * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 2 h) ^ 2 := by
    rw [mul_pow, mul_pow, Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 2 h)]
    have hrp : (α ^ (-(1 / 2 : ℝ))) ^ 2 = α ^ (-(1 : ℝ)) := by
      rw [pow_two, ← Real.rpow_add hα]; ring_nf
    rw [hrp, Real.rpow_neg_one]
    have hdiv : (10000 / α) * Work.Spaces.HkSq α 2 h
        ≤ 10000 * α⁻¹ * Work.Spaces.HkSq α 2 h := by
      rw [div_eq_mul_inv]
    linarith [hsq, hdiv]
  calc |h z θ| = Real.sqrt ((h z θ) ^ 2) := (Real.sqrt_sq_eq_abs (h z θ)).symm
    _ ≤ Real.sqrt ((100 * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 2 h) ^ 2) :=
        Real.sqrt_le_sqrt hsq2
    _ = 100 * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 2 h := Real.sqrt_sq h100

end Work.FTS.StrongPersist
