/-
# `HkMem_mul_of_WlInf6_cd6` — the `𝒲^{6,∞}`-priced product rule with `C^6` (not `C^∞`) data

`Work.FTS.StrongPersist.H6Pair6Aux.HkMem_mul_of_WlInf6` proves that the product of a
`𝒲^{6,∞}`-function `f` and an `ℋ⁶`-function `g` is again `ℋ⁶`, under the hypothesis that both
`f` and `g` are `C^∞` on the open quadrant.  The consumers of the level-six rows of the
nonlinear estimate only have `C^6` data (`Work.FTS.StrongPersist.H6Rows.piecesC6`), and the
product rule is used there in the form proved here.

The proof is the `C^6` shift of the chain
`WProd6.prod_majorant_winf6` + `WProd6.zslot_le_winf6` + `WProd6.mslot_le_winf6` +
`WProd6.dzIter_w_mean_le6`, whose `C^6` instances are the `Cd6/` lemmas:

* `Cd6.zslot_le_winf6_cd6` — the radial slots of the product against `HkIntegrand α 6 g`
  (via the `C^6` Leibniz rule `Cd6.mixedMul_cd6` and `Cd6.dzIter_le_WlInf6_cd6`);
* `Cd6.mslot_le_winf6_cd6` — the mixed slots against `GmajW6 α g`
  (via `Cd6.mixed_le_WlInf6_cd6` and the mean-term bound `Cd6.dzIter_w_mean_le6_cd6`);
* `prod_majorant_cd6` below, summing the slots to the pointwise majorant

  `HkIntegrand α 6 (f·g) ≤ K |f|²_{𝒲^{6,∞}} GmajW6 α g`  on `Q0`.

The majorant is then integrated:

* on the angular slice `K |f|² · GmajW6 α g z ·` is integrable by `HkMem α 6 g`;
* the resulting `z`-integral is dominated by `(K |f|² Kg) · HgInt6 α g`, whose `z`-integral is
  `(K |f|² Kg) · HkSq α 6 g < ∞` by `HkMem α 6 g` (`HgInt6` is the angular integral of the
  `ℋ⁶`-integrand of `g`, so its `z`-integral is `HkSq α 6 g` by definition);
* the a.e. strong measurability of the slice integral comes from the continuity of
  `HkIntegrand α 6 (f·g)` on the open quadrant (`Cd6.continuousOn_HkIntegrand_cd6`), which the
  `C^6` hypothesis supplies.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6.Cd6Basic
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6.zslot_le_winf6_cd6
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6.mslot_le_winf6_cd6
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6.dzIter_w_mean_le6_cd6
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6.Gmaj6
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6.Majorant6
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.Blocks.HalfInfra

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.N0pair6bWork

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-- **The pointwise majorant of the `ℋ⁶`-integrand of a product** (the `C^6` shift of
`Work.FTS.StrongPersist.H6Rows.WProd6.prod_majorant_winf6`): summing the at most seven radial
slots and the at most forty-nine mixed slots of `HkIntegrand α 6 (f·g)` gives
`HkIntegrand α 6 (f·g) ≤ (7 Cz + 49 Cm) |f|²_{𝒲^{6,∞}} GmajW6 α g`. -/
theorem prod_majorant_cd6 {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f g : ℝ → ℝ → ℝ}
    (hf : ContDiffOn ℝ 6 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hfm : Work.Spaces.WlInfMem α 6 f)
    (hgsm : ContDiffOn ℝ 6 (Function.uncurry g) Work.FTS.EllipticEst.Q0)
    (hgm : Work.Spaces.HkMem α 6 g)
    {Cz Cm : ℝ} (hCz0 : 0 < Cz) (hCm0 : 0 < Cm)
    (hzslot : ∀ i : ℕ, i ≤ 6 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (Work.Spaces.DzIter i (fun z θ => f z θ * g z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        ≤ Cz * (Work.Spaces.WlInf α 6 f) ^ 2 * Work.Spaces.HkIntegrand α 6 g z θ)
    (hmslot : ∀ I J : ℕ, 1 ≤ I → I + J ≤ 6 → ∀ z θ : ℝ, 0 < z → 0 < θ →
      θ < Real.pi / 2 →
      (Work.Spaces.mixed J I (fun z θ => f z θ * g z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
        ≤ Cm * (Work.Spaces.WlInf α 6 f) ^ 2
            * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 6 (fun z θ => f z θ * g z θ) z θ
        ≤ (7 * Cz + 49 * Cm) * (Work.Spaces.WlInf α 6 f) ^ 2
            * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ := by
  intro z hz θ hθ
  have hGnn : 0 ≤ Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ :=
    Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6_nonneg hα g hθ
  have hbase : 0 ≤ (7 * Cz + 49 * Cm) * (Work.Spaces.WlInf α 6 f) ^ 2
      * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ :=
    mul_nonneg (mul_nonneg (by linarith) (sq_nonneg _)) hGnn
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hzz | hzpos
  · have hz0 : z = 0 := hzz.symm
    subst hz0
    rw [Work.Blocks.Half.HkIntegrand_zero_z]
    exact hbase
  · by_cases hθi : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)
    · have hGle : Work.Spaces.HkIntegrand α 6 g z θ
          ≤ Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ :=
        Work.FTS.StrongPersist.H6Rows.WProd6.HkIntegrand_le_GmajW6 hα g hθ
      have hsum1 : (∑ i ∈ Finset.range (6 + 1),
            (Work.Spaces.DzIter i (fun z θ => f z θ * g z θ) z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          ≤ 7 * (Cz * (Work.Spaces.WlInf α 6 f) ^ 2
              * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ) := by
        calc (∑ i ∈ Finset.range (6 + 1),
              (Work.Spaces.DzIter i (fun z θ => f z θ * g z θ) z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
            ≤ ∑ _i ∈ Finset.range (6 + 1), (Cz * (Work.Spaces.WlInf α 6 f) ^ 2
                * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ) := by
              refine Finset.sum_le_sum fun i hi => ?_
              have hi6 : i ≤ 6 := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
              refine le_trans (hzslot i hi6 z θ hzpos hθi.1 hθi.2) ?_
              exact mul_le_mul_of_nonneg_left hGle (mul_nonneg (le_of_lt hCz0) (sq_nonneg _))
          _ = 7 * (Cz * (Work.Spaces.WlInf α 6 f) ^ 2
                * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ) := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; norm_num
      have hsum2 : (∑ i ∈ Finset.range (6 + 1), ∑ j ∈ Finset.range (6 + 1),
            (if 1 ≤ i ∧ i + j ≤ 6 then
              (Work.Spaces.mixed j i (fun z θ => f z θ * g z θ) z θ
                * Work.Spaces.Wt α z θ) ^ 2 else 0))
          ≤ 49 * (Cm * (Work.Spaces.WlInf α 6 f) ^ 2
              * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ) := by
        calc (∑ i ∈ Finset.range (6 + 1), ∑ j ∈ Finset.range (6 + 1),
              (if 1 ≤ i ∧ i + j ≤ 6 then
                (Work.Spaces.mixed j i (fun z θ => f z θ * g z θ) z θ
                  * Work.Spaces.Wt α z θ) ^ 2 else 0))
            ≤ ∑ _i ∈ Finset.range (6 + 1), ∑ _j ∈ Finset.range (6 + 1),
                (Cm * (Work.Spaces.WlInf α 6 f) ^ 2
                  * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ) := by
              refine Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => ?_
              by_cases hc : 1 ≤ i ∧ i + j ≤ 6
              · rw [if_pos hc]
                exact hmslot i j hc.1 hc.2 z θ hzpos hθi.1 hθi.2
              · rw [if_neg hc]
                exact mul_nonneg (mul_nonneg (le_of_lt hCm0) (sq_nonneg _)) hGnn
          _ = 49 * (Cm * (Work.Spaces.WlInf α 6 f) ^ 2
                * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ) := by
              simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
      rw [Work.Spaces.HkIntegrand]
      calc (∑ i ∈ Finset.range (6 + 1),
            (Work.Spaces.DzIter i (fun z θ => f z θ * g z θ) z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          + (∑ i ∈ Finset.range (6 + 1), ∑ j ∈ Finset.range (6 + 1),
              (if 1 ≤ i ∧ i + j ≤ 6 then
                (Work.Spaces.mixed j i (fun z θ => f z θ * g z θ) z θ
                  * Work.Spaces.Wt α z θ) ^ 2 else 0))
          ≤ 7 * (Cz * (Work.Spaces.WlInf α 6 f) ^ 2
                * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ)
            + 49 * (Cm * (Work.Spaces.WlInf α 6 f) ^ 2
                * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ) :=
            add_le_add hsum1 hsum2
        _ = (7 * Cz + 49 * Cm) * (Work.Spaces.WlInf α 6 f) ^ 2
              * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ := by ring
    · have hsin : Real.sin (2 * θ) = 0 := Work.Spaces.sin_two_eq_zero_of_not_Ioo hθ hθi
      rw [Work.FTS.StrongPersist.H6Rows.WProd6.HkIntegrand6_eq_zero_of_sin_two_eq_zero
        (α := α) (F := fun z θ => f z θ * g z θ) (z := z) (θ := θ)
        (by rw [Work.Spaces.gam]; linarith) hsin]
      exact hbase

/-- **The `𝒲^{6,∞}`-priced product rule with `C^6` data.**  If `f` is `C^6` on the open
quadrant and of class `𝒲^{6,∞}`, and `g` is `C^6` on the open quadrant and of class `ℋ⁶`, then
`f·g` is of class `ℋ⁶`. -/
theorem HkMem_mul_of_WlInf6_cd6 {α : ℝ} {f g : ℝ → ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hfs : ContDiffOn ℝ 6 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hfw : Work.Spaces.WlInfMem α 6 f)
    (hgs : ContDiffOn ℝ 6 (Function.uncurry g) Work.FTS.EllipticEst.Q0)
    (hgm : Work.Spaces.HkMem α 6 g) :
    Work.Spaces.HkMem α 6 (fun z θ => f z θ * g z θ) := by
  obtain ⟨CB, _hCBpos, hCBmean⟩ := Cd6.dzIter_w_mean_le6_cd6
  obtain ⟨Cz, hCz, hZ⟩ := Cd6.zslot_le_winf6_cd6
  obtain ⟨Cm, hCm, hMx⟩ := Cd6.mslot_le_winf6_cd6 CB
  have hmaj := prod_majorant_cd6 hα hα1 hfs hfw hgs hgm hCz hCm
    (fun i hi z θ hz hθ0 hθ1 => hZ α f g hα hα1 hfs hfw hgs i hi z θ hz hθ0 hθ1)
    (fun I J hI hIJ z θ hz hθ0 hθ1 => hMx α f g hα hα1 hfs hfw hgs hgm
      (fun d hd z' θ' hz' hθ0' hθ1' =>
        hCBmean α g d hα hα1 hgs hgm hd z' θ' hz' hθ0' hθ1')
      I J hI hIJ z θ hz hθ0 hθ1)
  set K : ℝ := 7 * Cz + 49 * Cm with hK
  have hKpos : 0 < K := by rw [hK]; linarith
  set Kg : ℝ := 1 + 700 * (1 + 6 * (Work.Spaces.gam α - 1)⁻¹) with hKg
  have hKgpos : 0 < Kg := by
    rw [hKg]
    have h1 : (0 : ℝ) < Work.Spaces.gam α - 1 := by rw [Work.Spaces.gam_sub_one]; linarith
    have h2 : 0 ≤ (Work.Spaces.gam α - 1)⁻¹ := inv_nonneg.mpr h1.le
    linarith
  -- the product is `C^6` on the open quadrant, so its integrand is continuous there
  have hfg : ContDiffOn ℝ 6 (Function.uncurry (fun z θ => f z θ * g z θ))
      Work.FTS.EllipticEst.Q0 := Cd6.contDiffOn_uncurry_mul_cd6 hfs hgs
  have hcont : ContinuousOn
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 6 (fun z θ => f z θ * g z θ) p.1 p.2)
      Work.FTS.EllipticEst.Q0 := Cd6.continuousOn_HkIntegrand_cd6 (le_refl 6) hfg
  -- the pointwise majorant
  have hmajor : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 6 (fun z θ => f z θ * g z θ) z θ
        ≤ K * (Work.Spaces.WlInf α 6 f) ^ 2
            * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ := by
    intro z hz θ hθ
    rw [hK]
    exact hmaj z hz θ hθ
  -- integrability of the angular slices of the product's integrand
  have hslice : ∀ z ∈ Work.Spaces.Iz, IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 6
      (fun z θ => f z θ * g z θ) z θ) Work.Spaces.Iθ := by
    intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hzz | hzpos
    · have hz0 : z = 0 := hzz.symm
      subst hz0
      have hzero : (fun θ => Work.Spaces.HkIntegrand α 6 (fun z θ => f z θ * g z θ) 0 θ)
          = fun _ : ℝ => (0 : ℝ) :=
        funext fun θ => Work.Blocks.Half.HkIntegrand_zero_z α 6 _ θ
      rw [hzero]
      exact integrableOn_zero
    · refine Integrable.mono'
        ((Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6_integrableOn_theta hα hα1 hgm hz).const_mul
          (K * (Work.Spaces.WlInf α 6 f) ^ 2)) ?_ ?_
      · exact Work.Spaces.aesm_slice_of_continuousOn_Qd _
          (Cd6.continuousOn_HkIntegrand_cd6 (le_refl 6) hfg) hzpos
      · filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
        rw [Real.norm_of_nonneg (Work.Spaces.HkIntegrand_nonneg α 6 _ z θ)]
        exact hmajor z hz θ hθ
  -- the angular integral of the majorant at every radius
  have hbdd : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 (fun z θ => f z θ * g z θ) z θ)
        ≤ (K * (Work.Spaces.WlInf α 6 f) ^ 2 * Kg)
            * Work.FTS.StrongPersist.H6Rows.WProd6.HgInt6 α g z := by
    intro z hz
    have hint : IntegrableOn (fun θ => (K * (Work.Spaces.WlInf α 6 f) ^ 2)
        * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ) Work.Spaces.Iθ :=
      (Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6_integrableOn_theta hα hα1 hgm hz).const_mul _
    have h1 : (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6
          (fun z θ => f z θ * g z θ) z θ)
        ≤ ∫ θ in Work.Spaces.Iθ, (K * (Work.Spaces.WlInf α 6 f) ^ 2)
            * Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ :=
      integral_mono_of_nonneg
        (Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 6 _ z θ) hint
        (ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => hmajor z hz θ hθ))
    rw [MeasureTheory.integral_const_mul] at h1
    have h2 : (∫ θ in Work.Spaces.Iθ, Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ)
        ≤ Kg * Work.FTS.StrongPersist.H6Rows.WProd6.HgInt6 α g z := by
      simpa only [hKg] using
        Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6_theta_integral_le (α := α) (g := g)
          hα hα1 hgm hz
    calc (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6
            (fun z θ => f z θ * g z θ) z θ)
        ≤ (K * (Work.Spaces.WlInf α 6 f) ^ 2)
            * (∫ θ in Work.Spaces.Iθ,
              Work.FTS.StrongPersist.H6Rows.WProd6.GmajW6 α g z θ) := h1
      _ ≤ (K * (Work.Spaces.WlInf α 6 f) ^ 2)
            * (Kg * Work.FTS.StrongPersist.H6Rows.WProd6.HgInt6 α g z) :=
          mul_le_mul_of_nonneg_left h2 (mul_nonneg hKpos.le (sq_nonneg _))
      _ = (K * (Work.Spaces.WlInf α 6 f) ^ 2 * Kg)
            * Work.FTS.StrongPersist.H6Rows.WProd6.HgInt6 α g z := by ring
  -- the dominating function of the `z`-integral
  have hdom : IntegrableOn (fun z => (K * (Work.Spaces.WlInf α 6 f) ^ 2 * Kg)
      * Work.FTS.StrongPersist.H6Rows.WProd6.HgInt6 α g z) Work.Spaces.Iz :=
    hgm.2.const_mul _
  -- a.e. strong measurability of the `z`-slice integral
  have haesm : AEStronglyMeasurable (fun z => ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 6 (fun z θ => f z θ * g z θ) z θ)
      (volume.restrict Work.Spaces.Iz) := by
    have h := (Work.Spaces.aesm_of_continuousOn_Qd
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 6 (fun z θ => f z θ * g z θ) p.1 p.2)
      hcont).integral_prod_right'
    have hfun : (fun z => ∫ θ, Work.Spaces.HkIntegrand α 6 (fun z θ => f z θ * g z θ) z θ
          ∂(volume.restrict Work.Spaces.Iθ))
        = (fun z => ∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α 6 (fun z θ => f z θ * g z θ) z θ) := rfl
    rw [← hfun]
    exact h
  have hzg : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 6 (fun z θ => f z θ * g z θ) z θ) Work.Spaces.Iz := by
    refine Integrable.mono' hdom haesm ?_
    filter_upwards [ae_restrict_mem (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici)]
      with z hz
    rw [Real.norm_of_nonneg (integral_nonneg fun θ =>
      Work.Spaces.HkIntegrand_nonneg α 6 _ z θ)]
    exact hbdd z hz
  exact ⟨hslice, hzg⟩

end Work.FTS.StrongPersist.H6Rows.N0pair6bWork
