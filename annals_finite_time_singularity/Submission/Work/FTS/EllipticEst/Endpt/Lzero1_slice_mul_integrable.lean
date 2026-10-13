import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.abs_mul_sinCos2_le_weighted
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.remov.wsAux
import Submission.Work.FTS.EllipticEst.Endpt.Lzero1_mul_sinCos2_eq
import Submission.Work.FTS.EllipticEst.Endpt.slice_regularity_of_uncurry

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Endpt

set_option autoImplicit false

/-- The `θ`-slice of `Lzero1 (fun θ' => Ψ z θ')` multiplied by the kernel `sinθcos²θ` is
integrable, assuming the slice and its derivative are bounded.

Pointwise on `(0, π/2)` (where `Real.cos θ ≠ 0`),
`(Lzero1 u θ) * sinθcos²θ = -(u'' θ) * sinθcos²θ + sin θ * u θ + sin²θ cos θ * u' θ
 - 6 * u θ * sinθcos²θ` (from `(tan·u)' = (1/cos²)·u + tan·u'` and
`sinθcos²θ/cos²θ = sinθ`, `tanθ·sinθcos²θ = sin²θcosθ`). The last three terms are bounded by
`7 * C` since `|u| ≤ C`, `|u'| ≤ C` and the angular factors lie in `[0,1]`; the `u''`-term is
dominated by `(u'' θ · w z / sin(2θ)^{η/2})² + 1` via
`Work.FTS.EllipticEst.abs_mul_sinCos2_le_weighted`, which is integrable by `hmB` (divided by
`w z ≠ 0`). Needed: `deriv`-rewriting of `(tan · u)'` (via `deriv_mul` and `Real.deriv_tan`),
the a.e. equality `pthIter 2 Ψ z · = deriv (deriv (Ψ z ·))` on `Iθ` (definitional), and
a.e.-strong measurability of the slice (from `hsm`). -/
theorem Lzero1_slice_mul_integrable {α : ℝ} {Ψ : ℝ → ℝ → ℝ} {z C : ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hmB : Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 Ψ)) (hz : 0 < z)
    (hC : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), |Ψ z θ| ≤ C ∧ |deriv (fun θ' => Ψ z θ') θ| ≤ C) :
    MeasureTheory.IntegrableOn
      (fun θ => Work.FTS.EllipticEst.Lzero1 (fun θ' => Ψ z θ') θ * Work.Elliptic.sinCos2 θ)
      Work.Spaces.Iθ := by
  -- the slice `θ ↦ Ψ z θ` is `C²` on the open interval, with continuous first two derivatives
  obtain ⟨hslice2, hdu_cont, hddu_cont⟩ := slice_regularity_of_uncurry hz hsm
  -- `C` is nonnegative because the open interval is nonempty
  have hC0 : 0 ≤ C :=
    le_trans (abs_nonneg _) (hC (Real.pi / 4) ⟨by linarith [Real.pi_pos],
      by linarith [Real.pi_pos]⟩).1
  -- the pointwise identity on the open interval
  have hpoint : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.FTS.EllipticEst.Lzero1 (fun θ' => Ψ z θ') θ * Work.Elliptic.sinCos2 θ
        = -(deriv (deriv (fun θ' => Ψ z θ')) θ) * Work.Elliptic.sinCos2 θ
          + Real.sin θ * (fun θ' => Ψ z θ') θ
          + (Real.sin θ) ^ 2 * Real.cos θ * deriv (fun θ' => Ψ z θ') θ
          - 6 * (fun θ' => Ψ z θ') θ * Work.Elliptic.sinCos2 θ := by
    intro θ hθ
    exact Lzero1_mul_sinCos2_eq hθ
      ((hslice2.contDiffAt (isOpen_Ioo.mem_nhds hθ)).differentiableAt (by norm_num))
  -- continuity on the open interval of the explicit form, hence a.e. strong measurability
  have hcont_sc : ContinuousOn (fun θ : ℝ => Work.Elliptic.sinCos2 θ)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    unfold Work.Elliptic.sinCos2
    fun_prop
  have hu_cont : ContinuousOn (fun θ' => Ψ z θ') (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hslice2.continuousOn
  have hcontG : ContinuousOn (fun θ : ℝ =>
      -(deriv (deriv (fun θ' => Ψ z θ')) θ) * Work.Elliptic.sinCos2 θ
        + Real.sin θ * (fun θ' => Ψ z θ') θ
        + (Real.sin θ) ^ 2 * Real.cos θ * deriv (fun θ' => Ψ z θ') θ
        - 6 * (fun θ' => Ψ z θ') θ * Work.Elliptic.sinCos2 θ)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    have h1 : ContinuousOn (fun θ : ℝ =>
        -(deriv (deriv (fun θ' => Ψ z θ')) θ) * Work.Elliptic.sinCos2 θ)
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) := hddu_cont.neg.mul hcont_sc
    have h2 : ContinuousOn (fun θ : ℝ => Real.sin θ * (fun θ' => Ψ z θ') θ)
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) := Real.continuous_sin.continuousOn.mul hu_cont
    have h3 : ContinuousOn (fun θ : ℝ =>
        (Real.sin θ) ^ 2 * Real.cos θ * deriv (fun θ' => Ψ z θ') θ)
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      ((Real.continuous_sin.continuousOn.pow 2).mul Real.continuous_cos.continuousOn).mul hdu_cont
    have h4 : ContinuousOn (fun θ : ℝ => 6 * (fun θ' => Ψ z θ') θ * Work.Elliptic.sinCos2 θ)
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      (continuousOn_const.mul hu_cont).mul hcont_sc
    exact ((h1.add h2).add h3).sub h4
  have hcontF : ContinuousOn
      (fun θ : ℝ => Work.FTS.EllipticEst.Lzero1 (fun θ' => Ψ z θ') θ * Work.Elliptic.sinCos2 θ)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hcontG.congr hpoint
  have haesm : AEStronglyMeasurable
      (fun θ : ℝ => Work.FTS.EllipticEst.Lzero1 (fun θ' => Ψ z θ') θ * Work.Elliptic.sinCos2 θ)
      (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    hcontF.aestronglyMeasurable measurableSet_Ioo
  -- the dominating function is integrable on `Iθ`
  have hsq : MeasureTheory.IntegrableOn (fun θ : ℝ =>
      (Work.Spaces.pthIter 2 Ψ z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) Work.Spaces.Iθ :=
    (hmB.1 z hz.le).congr_fun (fun θ _ => by simp [Work.Spaces.HkIntegrand]) measurableSet_Icc
  have hGint : MeasureTheory.IntegrableOn (fun θ : ℝ =>
      (Work.Spaces.pthIter 2 Ψ z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 + 1 + 8 * C)
      Work.Spaces.Iθ := by
    have h1 : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ)) Work.Spaces.Iθ :=
      MeasureTheory.integrableOn_const Work.FTS.EllipticEst.remov.ws_vol_Iθ_ne_top
    have h8 : MeasureTheory.IntegrableOn (fun _ : ℝ => 8 * C) Work.Spaces.Iθ :=
      MeasureTheory.integrableOn_const Work.FTS.EllipticEst.remov.ws_vol_Iθ_ne_top
    exact (hsq.add h1).add h8
  have hGintIoo : MeasureTheory.IntegrableOn (fun θ : ℝ =>
      (Work.Spaces.pthIter 2 Ψ z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 + 1 + 8 * C)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hGint.mono_set Set.Ioo_subset_Icc_self
  -- the pointwise bound on the open interval
  have hbound : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      ‖Work.FTS.EllipticEst.Lzero1 (fun θ' => Ψ z θ') θ * Work.Elliptic.sinCos2 θ‖
        ≤ (Work.Spaces.pthIter 2 Ψ z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 + 1 + 8 * C := by
    intro θ hθ
    have hθIθ : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    obtain ⟨hΨ, hdΨ⟩ := hC θ hθ
    rw [Real.norm_eq_abs, hpoint θ hθ]
    -- the `u''`-term, absorbed by the weighted `L²` square
    have hA : |-(deriv (deriv (fun θ' => Ψ z θ')) θ) * Work.Elliptic.sinCos2 θ|
        ≤ (Work.Spaces.pthIter 2 Ψ z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 + 1 := by
      rw [neg_mul, abs_neg]
      exact Work.FTS.EllipticEst.abs_mul_sinCos2_le_weighted
        (f := fun θ' => deriv (deriv (fun θ'' => Ψ z θ'')) θ') hz hθIθ
    -- the three bounded terms
    have hB : |Real.sin θ * (fun θ' => Ψ z θ') θ| ≤ C := by
      rw [abs_mul]
      calc |Real.sin θ| * |(fun θ' => Ψ z θ') θ| ≤ 1 * C :=
            mul_le_mul (Real.abs_sin_le_one θ) hΨ (abs_nonneg _) (by norm_num)
        _ = C := by ring
    have hCc : |(Real.sin θ) ^ 2 * Real.cos θ * deriv (fun θ' => Ψ z θ') θ| ≤ C := by
      rw [abs_mul, abs_mul, abs_pow]
      have hs1 : |Real.sin θ| ^ 2 ≤ 1 := by
        nlinarith [abs_nonneg (Real.sin θ), Real.abs_sin_le_one θ]
      have hc1 : |Real.cos θ| ≤ 1 := Real.abs_cos_le_one θ
      calc |Real.sin θ| ^ 2 * |Real.cos θ| * |deriv (fun θ' => Ψ z θ') θ|
          ≤ 1 * 1 * C := by
            refine mul_le_mul (mul_le_mul hs1 hc1 (abs_nonneg _) (by norm_num)) hdΨ
              (abs_nonneg _) (by norm_num)
        _ = C := by ring
    have hD : |6 * (fun θ' => Ψ z θ') θ * Work.Elliptic.sinCos2 θ| ≤ 6 * C := by
      rw [abs_mul]
      have h6 : |(6 : ℝ) * (fun θ' => Ψ z θ') θ| ≤ 6 * C := by
        rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 6)]
        exact mul_le_mul_of_nonneg_left hΨ (by norm_num)
      have hsc1 : |Work.Elliptic.sinCos2 θ| ≤ 1 :=
        Work.FTS.EllipticEst.abs_sinCos2_le_one hθIθ
      calc |(6 : ℝ) * (fun θ' => Ψ z θ') θ| * |Work.Elliptic.sinCos2 θ| ≤ (6 * C) * 1 :=
            mul_le_mul h6 hsc1 (abs_nonneg _) (by linarith)
        _ = 6 * C := by ring
    -- triangle inequality and assembly
    have htri : |-(deriv (deriv (fun θ' => Ψ z θ')) θ) * Work.Elliptic.sinCos2 θ
          + Real.sin θ * (fun θ' => Ψ z θ') θ
          + (Real.sin θ) ^ 2 * Real.cos θ * deriv (fun θ' => Ψ z θ') θ
          - 6 * (fun θ' => Ψ z θ') θ * Work.Elliptic.sinCos2 θ|
        ≤ |-(deriv (deriv (fun θ' => Ψ z θ')) θ) * Work.Elliptic.sinCos2 θ|
          + |Real.sin θ * (fun θ' => Ψ z θ') θ|
          + |(Real.sin θ) ^ 2 * Real.cos θ * deriv (fun θ' => Ψ z θ') θ|
          + |6 * (fun θ' => Ψ z θ') θ * Work.Elliptic.sinCos2 θ| := by
      have h1 := abs_add_le
        (-(deriv (deriv (fun θ' => Ψ z θ')) θ) * Work.Elliptic.sinCos2 θ
          + Real.sin θ * (fun θ' => Ψ z θ') θ
          + (Real.sin θ) ^ 2 * Real.cos θ * deriv (fun θ' => Ψ z θ') θ)
        (-(6 * (fun θ' => Ψ z θ') θ * Work.Elliptic.sinCos2 θ))
      rw [abs_neg] at h1
      have h2 := abs_add_le
        (-(deriv (deriv (fun θ' => Ψ z θ')) θ) * Work.Elliptic.sinCos2 θ
          + Real.sin θ * (fun θ' => Ψ z θ') θ)
        ((Real.sin θ) ^ 2 * Real.cos θ * deriv (fun θ' => Ψ z θ') θ)
      have h3 := abs_add_le
        (-(deriv (deriv (fun θ' => Ψ z θ')) θ) * Work.Elliptic.sinCos2 θ)
        (Real.sin θ * (fun θ' => Ψ z θ') θ)
      have hg : |-(deriv (deriv (fun θ' => Ψ z θ')) θ) * Work.Elliptic.sinCos2 θ
            + Real.sin θ * (fun θ' => Ψ z θ') θ
            + (Real.sin θ) ^ 2 * Real.cos θ * deriv (fun θ' => Ψ z θ') θ
            - 6 * (fun θ' => Ψ z θ') θ * Work.Elliptic.sinCos2 θ|
          = |(-(deriv (deriv (fun θ' => Ψ z θ')) θ) * Work.Elliptic.sinCos2 θ
            + Real.sin θ * (fun θ' => Ψ z θ') θ
            + (Real.sin θ) ^ 2 * Real.cos θ * deriv (fun θ' => Ψ z θ') θ)
            + -(6 * (fun θ' => Ψ z θ') θ * Work.Elliptic.sinCos2 θ)| := by
        rw [sub_eq_add_neg]
      rw [hg]
      linarith
    linarith
  -- the transfer from the open interval to `Iθ` (the two endpoints are null)
  have hIntIoo : MeasureTheory.IntegrableOn (fun θ : ℝ =>
      Work.FTS.EllipticEst.Lzero1 (fun θ' => Ψ z θ') θ * Work.Elliptic.sinCos2 θ)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    MeasureTheory.Integrable.mono' hGintIoo haesm (by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
      exact hbound θ hθ)
  exact MeasureTheory.IntegrableOn.congr_set_ae hIntIoo (by
    show Work.Spaces.Iθ =ᵐ[volume] Set.Ioo (0 : ℝ) (Real.pi / 2)
    rw [Work.Spaces.Iθ]
    exact (MeasureTheory.Ioo_ae_eq_Icc (a := (0 : ℝ)) (b := Real.pi / 2)).symm)

end Work.FTS.EllipticEst.Endpt
