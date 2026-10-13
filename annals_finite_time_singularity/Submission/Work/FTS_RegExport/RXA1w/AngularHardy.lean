import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS_RegExport.C4.hardyTheta_slice_C1
import Submission.Work.FTS_RegExport.C4.Dth_mixed_eq_C4
import Submission.Work.FTS_RegExport.RXA1w.Helpers
import Submission.Work.FTS.EllipticEst.SliceDecompDefs
import Submission.Work.FTS.H2.LinfQ

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The angular Hardy inequality for a mixed slot at the finite order `C⁴`

`angular_hardy_C4`: for a datum `f` which is `C⁴` on the open quadrant, honestly in `ℋ⁴` and
satisfying the boundary traces, and for `a + b ≤ 2`, `z > 0`, `θ ∈ (0,π/2)`,

  `(D_z^bD_θ^af(z,θ))² ≤ (100/(γ-1)) ∫_σ sin(2σ)^{-γ} (D_z^bD_θ^{a+1}f(z,σ))² dσ`.

The proof uses the `C¹`-slice angular Hardy inequality `hardyTheta_slice_C1` on the `θ`-slice
of the slot, the identity `∂_θ = D_θ / sin(2·)` and `D_θ(D_z^bD_θ^af) = D_z^bD_θ^{a+1}f`
(`Dth_mixed_eq_C4`).
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXA1w

/-- The identity `∂_θ u = D_θ u / sin(2·)` on the open interval. -/
private lemma pth_eq_Dth_div {u : ℝ → ℝ → ℝ} {z σ : ℝ} (hσ : 0 < Real.sin (2 * σ)) :
    Work.Spaces.pth u z σ = Work.Spaces.Dth u z σ / Real.sin (2 * σ) := by
  rw [show Work.Spaces.Dth u z σ = Real.sin (2 * σ) * Work.Spaces.pth u z σ from rfl]
  field_simp

/-- The exponent identity `sin(2σ)^{2-γ} = sin(2σ)² · sin(2σ)^{-γ}`. -/
private lemma sin_rpow_split {β : ℝ} {σ : ℝ} (hσ : 0 < Real.sin (2 * σ)) :
    (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam β)
      = (Real.sin (2 * σ)) ^ 2 * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam β)) := by
  rw [show (2 - Work.Spaces.gam β) = ((2 : ℕ) : ℝ) + (-(Work.Spaces.gam β)) by
    push_cast; ring, Real.rpow_add hσ, Real.rpow_natCast]

theorem angular_hardy_C4 {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) {f : ℝ → ℝ → ℝ}
    (h4 : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hmem : Work.Spaces.HkMem β 4 f) (htr : Work.FTS.Nonlin.BdryTraces β 4 f)
    (b a : ℕ) (hab : a + b ≤ 2) {z : ℝ} (hz : 0 < z) (θ : ℝ)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    (Work.Spaces.mixed b a f z θ) ^ 2 ≤
      (100 / (Work.Spaces.gam β - 1)) *
        ∫ σ in Work.Spaces.Iθ,
          (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam β))
            * (Work.Spaces.mixed b (a + 1) f z σ) ^ 2 := by
  have hgam_ne : Work.Spaces.gam β ≠ 0 := ne_of_gt (Work.Spaces.gam_pos hβ)
  have hslice := contDiffOn_slice_mixed h4 b a 1 (by omega) hz
  have hpth : ContDiffOn ℝ 1
      (fun θ' => Work.Spaces.pth (Work.Spaces.mixed b a f) z θ') (Set.Ioo 0 (Real.pi / 2)) := by
    have h2 : ContDiffOn ℝ 1
        (Function.uncurry (Work.Spaces.pth (Work.Spaces.mixed b a f)))
        Work.FTS.EllipticEst.Q0 :=
      Work.FTS.StrongEps.contDiffOn_uncurry_pth_fin Work.FTS.EllipticEst.isOpen_Q0
        (contDiffOn_uncurry_mixed_Q0 h4 b a 2 (by omega))
    exact Work.FTS.StrongEps.EComparison.contDiffOn_slice_t hz h2
  have h0 : Filter.Tendsto (fun θ' => Work.Spaces.mixed b a f z θ') (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    Work.FTS.H2.tendsto_nhdsGT_zero_of_traces β hβ
      ((htr a b (by omega)).2 z (Set.mem_Ioi.mpr hz) |>.1)
  have hHk := hmem.1 z (Set.mem_Ici.mpr hz.le)
  have hbound : ∀ σ ∈ Work.Spaces.Iθ,
      (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam β)) * (Work.Spaces.mixed b (a + 1) f z σ) ^ 2
        ≤ Work.Spaces.HkIntegrand β 4 f z σ := by
    intro σ hσ
    rcases eq_or_lt_of_le hσ.1 with h0' | hpos
    · subst h0'
      rw [show Real.sin (2 * (0 : ℝ)) = 0 by simp,
        Real.zero_rpow (neg_ne_zero.mpr hgam_ne), zero_mul]
      exact Work.Spaces.HkIntegrand_nonneg β 4 f z 0
    rcases eq_or_lt_of_le hσ.2 with h1' | hlt
    · subst h1'
      rw [show Real.sin (2 * (Real.pi / 2)) = 0 by
          rw [show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi],
        Real.zero_rpow (neg_ne_zero.mpr hgam_ne), zero_mul]
      exact Work.Spaces.HkIntegrand_nonneg β 4 f z (Real.pi / 2)
    · have hσ' : σ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hpos, hlt⟩
      have hsin : 0 < Real.sin (2 * σ) := Work.FTS.H2.sin_two_pos_of_mem_Ioo hσ'
      have hm1 : (Work.Spaces.mixed b (a + 1) f z σ) ^ 2
          ≤ (Work.Spaces.mixed b (a + 1) f z σ * Work.Spaces.w z) ^ 2 := by
        rw [mul_pow]
        simpa using mul_le_mul_of_nonneg_left (Work.FTS.H2.one_le_w_sq hz)
          (sq_nonneg (Work.Spaces.mixed b (a + 1) f z σ))
      have hm2 := mixed_slot_sq_w_le_HkIntegrand (f := f) hβ b (a + 1) (by omega) (by omega)
        z hσ'
      calc (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam β))
            * (Work.Spaces.mixed b (a + 1) f z σ) ^ 2
          ≤ (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam β))
              * ((Work.Spaces.mixed b (a + 1) f z σ * Work.Spaces.w z) ^ 2) :=
            mul_le_mul_of_nonneg_left hm1 (Real.rpow_nonneg hsin.le _)
        _ = (Work.Spaces.mixed b (a + 1) f z σ * Work.Spaces.w z) ^ 2
              * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam β)) := by ring
        _ ≤ ((Real.sin (2 * σ)) ^ (Work.Spaces.gam β) * Work.Spaces.HkIntegrand β 4 f z σ)
              * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam β)) :=
            mul_le_mul_of_nonneg_right hm2 (Real.rpow_nonneg hsin.le _)
        _ = Work.Spaces.HkIntegrand β 4 f z σ := by
            have hassoc : ((Real.sin (2 * σ)) ^ (Work.Spaces.gam β)
                  * Work.Spaces.HkIntegrand β 4 f z σ)
                  * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam β))
                = Work.Spaces.HkIntegrand β 4 f z σ
                  * ((Real.sin (2 * σ)) ^ (Work.Spaces.gam β)
                    * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam β))) := by ring
            rw [hassoc, ← Real.rpow_add hsin,
              show Work.Spaces.gam β + -(Work.Spaces.gam β) = 0 by ring,
              Real.rpow_zero, mul_one]
  have haesm : AEStronglyMeasurable
      (fun σ => (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam β))
        * (Work.Spaces.mixed b (a + 1) f z σ) ^ 2) (volume.restrict Work.Spaces.Iθ) := by
    refine Work.Spaces.aesm_slice_of_continuousOn_Qd
      (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam β))
        * (Work.Spaces.mixed b (a + 1) f p.1 p.2) ^ 2) ?_ hz
    have hm : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed b (a + 1) f p.1 p.2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
      (contDiffOn_uncurry_mixed_Q0 h4 b (a + 1) 0 (by omega)).continuousOn
    have hs : ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam β)))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
      ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
        (fun p hp => Or.inl (ne_of_gt (Work.FTS.H2.sin_two_pos_of_mem_Ioo hp.2)))
    exact hs.mul (hm.pow 2)
  have hintW : MeasureTheory.IntegrableOn
      (fun σ => (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam β))
        * (Work.Spaces.mixed b (a + 1) f z σ) ^ 2) Work.Spaces.Iθ :=
    hHk.mono' haesm (ae_restrict_of_forall_mem measurableSet_Icc fun σ hσ => by
      rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg (Work.FTS.H2.sin_two_nonneg hσ) _)
        (sq_nonneg _))]
      exact hbound σ hσ)
  have hint : MeasureTheory.IntegrableOn
      (fun σ => (Work.Spaces.pth (Work.Spaces.mixed b a f) z σ) ^ 2
        * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam β)) Work.Spaces.Iθ := by
    refine hintW.congr ?_
    rw [Work.FTS.EllipticEst.restrict_Iθ_eq_restrict_Ioo]
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo fun σ hσ => ?_
    have hsin : 0 < Real.sin (2 * σ) := Work.FTS.H2.sin_two_pos_of_mem_Ioo hσ
    have hD : Work.Spaces.Dth (Work.Spaces.mixed b a f) z σ
        = Work.Spaces.mixed b (a + 1) f z σ :=
      Work.FTS_RegExport.C4.Dth_mixed_eq_C4 h4 b a (by omega) hz hσ
    show (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam β)) * (Work.Spaces.mixed b (a + 1) f z σ) ^ 2
        = (Work.Spaces.pth (Work.Spaces.mixed b a f) z σ) ^ 2
          * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam β)
    rw [pth_eq_Dth_div hsin, hD, sin_rpow_split (β := β) hsin]
    field_simp <;> try ring
  have hHardy := Work.FTS_RegExport.C4.hardyTheta_slice_C1 (g := Work.Spaces.mixed b a f)
    hβ hβ1 hz hslice hpth h0 hint θ hθ
  have hcongr : (∫ σ in Work.Spaces.Iθ, (Work.Spaces.pth (Work.Spaces.mixed b a f) z σ) ^ 2
        * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam β))
      = ∫ σ in Work.Spaces.Iθ, (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam β))
          * (Work.Spaces.mixed b (a + 1) f z σ) ^ 2 := by
    refine Work.FTS.EllipticEst.setIntegral_Iθ_congr_of_forall_Ioo fun σ hσ => ?_
    have hsin : 0 < Real.sin (2 * σ) := Work.FTS.H2.sin_two_pos_of_mem_Ioo hσ
    have hD : Work.Spaces.Dth (Work.Spaces.mixed b a f) z σ
        = Work.Spaces.mixed b (a + 1) f z σ :=
      Work.FTS_RegExport.C4.Dth_mixed_eq_C4 h4 b a (by omega) hz hσ
    rw [pth_eq_Dth_div hsin, hD, sin_rpow_split (β := β) hsin]
    field_simp <;> try ring
  rw [← hcongr]
  exact hHardy

end Work.FTS_RegExport.RXA1w
