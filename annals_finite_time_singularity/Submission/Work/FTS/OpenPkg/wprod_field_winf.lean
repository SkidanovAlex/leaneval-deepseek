/-
# `Work.FTS.OpenPkg.wprod_field_winf` — the `𝒲^{4,∞}`-priced product rule

The `wprod` clause of the primed norm interface `Work.FTS.OpenPkg.N4Norm'` (Elgindi's
`WProductRule`, tex 1086), in the open-quadrant class:

```
∃ C > 0, ∀ α ∈ (0,1], ∀ f g,
  SmoothOpen f → WlInfMem α 4 f → HQo α 4 g →
    HkMem α 4 (f·g) ∧ Xn α (f·g) ≤ C α^{-1/2} |f|_{𝒲^{4,∞}} · Xn α g.
```

The coefficient `f` is priced by the *weighted* norm `𝒲^{4,∞}` (`WlInf`/`WlInfMem`), so that it
need not itself lie in `ℋ⁴` — this is the form used by the rows of the §8 estimate for the
coefficients `F_*`, `D_θF_*`, `D_zF_*` (the plain `D`-sup norm `WDp` is *not* enough: the spike
family of `NOTES_wprod_field_honest_FALSE.md` refutes that version).

Route (the open-quadrant port of the proved `Work.FTS.H2.WProdQ`, with the radial-Hardy input of
the `g`-side replaced by its *mean-term* counterpart, since the open class carries no boundary
vanishing of the `g`-slices):

* `WProdWin/zslot_le_winf` — the five pure `D_z`-slots of `f·g`, priced by `HkIntegrand α 4 g`;
* `WProdWin/dzIter_w_mean_le` — the mean-term angular bound `(D_z^d g·w)² ≤ C(w²∫(D_z^d g)² +
  (γ-1)⁻¹ Aang α g d z)`, `d ≤ 3`, from `sob_theta_mean`;
* `WProdWin/mslot_le_winf` — the mixed slots, combining the `𝒲^{4,∞}`-bounds of `f`
  (`Mixed_le_WlInf_open`/`DzIter_le_WlInf_open`) with the two `g`-side bounds (`HkIntegrand`
  for the slots that see a `θ`-derivative, the mean-term bound for the pure radial ones);
* `WProdWin/Basic` — the majorant `GmajW`, its integral `HgInt` and the angular factor `TW`;
* this module: sum the slots into `HkIntegrand α 4 (f·g) ≤ K |f|²_𝒲 GmajW`, integrate, and
  convert the `HkSq`-bound into the stated `Xn`-bound.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.H2.WProdQ
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.FTS.OpenPkg.WProdWin.Basic
import Submission.Work.FTS.OpenPkg.WProdWin.dzIter_w_mean_le
import Submission.Work.FTS.OpenPkg.WProdWin.zslot_le_winf
import Submission.Work.FTS.OpenPkg.WProdWin.mslot_le_winf
import Submission.Work.FTS.OpenPkg.DzIter_le_WlInf_open
import Submission.Work.FTS.OpenPkg.Mixed_le_WlInf_open

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.OpenPkg

set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- `√(x⁻¹) = x^(-1/2)` for `x > 0`. -/
theorem sqrt_inv_eq_rpow_neg_half {x : ℝ} (hx : 0 < x) :
    Real.sqrt x⁻¹ = x ^ (-(1 / 2 : ℝ)) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg_one, ← Real.rpow_mul hx.le]
  congr 1
  ring

/-- **The pointwise majorant of the `𝒲^{4,∞}`-priced product rule.**

Summing the five pure `D_z`-slots (`hzslot`) and the at most 25 mixed slots (`hmslot`) of
`HkIntegrand α 4 (f·g)`, using `HkIntegrand α 4 g ≤ GmajW α g`. -/
theorem prod_majorant_winf {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hfm : Work.Spaces.WlInfMem α 4 f)
    (hgsm : Work.FTS.EllipticEst.SmoothOpen g) (hgm : Work.Spaces.HkMem α 4 g)
    {Cz Cm : ℝ} (hCz0 : 0 < Cz) (hCm0 : 0 < Cm)
    (hzslot : ∀ i : ℕ, i ≤ 4 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (Work.Spaces.DzIter i (fun z θ => f z θ * g z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        ≤ Cz * (Work.Spaces.WlInf α 4 f) ^ 2 * Work.Spaces.HkIntegrand α 4 g z θ)
    (hmslot : ∀ I J : ℕ, 1 ≤ I → I + J ≤ 4 → ∀ z θ : ℝ, 0 < z → 0 < θ →
      θ < Real.pi / 2 →
      (Work.Spaces.mixed J I (fun z θ => f z θ * g z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
        ≤ Cm * (Work.Spaces.WlInf α 4 f) ^ 2 * WProdWin.GmajW α g z θ) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 4 (fun z θ => f z θ * g z θ) z θ
        ≤ (5 * Cz + 25 * Cm) * (Work.Spaces.WlInf α 4 f) ^ 2 * WProdWin.GmajW α g z θ := by
  intro z hz θ hθ
  have hGnn : 0 ≤ WProdWin.GmajW α g z θ := WProdWin.GmajW_nonneg hα g hθ
  have hbase : 0 ≤ (5 * Cz + 25 * Cm) * (Work.Spaces.WlInf α 4 f) ^ 2
      * WProdWin.GmajW α g z θ :=
    mul_nonneg (mul_nonneg (by linarith) (sq_nonneg _)) hGnn
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hzz | hzpos
  · have hz0 : z = 0 := hzz.symm
    subst hz0
    rw [Work.Spaces.HkIntegrand_zero_z]
    exact hbase
  · by_cases hθi : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)
    · have hGle : Work.Spaces.HkIntegrand α 4 g z θ ≤ WProdWin.GmajW α g z θ :=
        WProdWin.HkIntegrand_le_GmajW hα g hθ
      have hsum1 : (∑ i ∈ Finset.range (4 + 1),
            (Work.Spaces.DzIter i (fun z θ => f z θ * g z θ) z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          ≤ 5 * (Cz * (Work.Spaces.WlInf α 4 f) ^ 2 * WProdWin.GmajW α g z θ) := by
        calc (∑ i ∈ Finset.range (4 + 1),
              (Work.Spaces.DzIter i (fun z θ => f z θ * g z θ) z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
            ≤ ∑ _i ∈ Finset.range (4 + 1), (Cz * (Work.Spaces.WlInf α 4 f) ^ 2
                * WProdWin.GmajW α g z θ) := by
              refine Finset.sum_le_sum fun i hi => ?_
              have hi4 : i ≤ 4 := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
              refine le_trans (hzslot i hi4 z θ hzpos hθi.1 hθi.2) ?_
              exact mul_le_mul_of_nonneg_left hGle (mul_nonneg (le_of_lt hCz0) (sq_nonneg _))
          _ = 5 * (Cz * (Work.Spaces.WlInf α 4 f) ^ 2 * WProdWin.GmajW α g z θ) := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; norm_num
      have hsum2 : (∑ i ∈ Finset.range (4 + 1), ∑ j ∈ Finset.range (4 + 1),
            (if 1 ≤ i ∧ i + j ≤ 4 then
              (Work.Spaces.mixed j i (fun z θ => f z θ * g z θ) z θ
                * Work.Spaces.Wt α z θ) ^ 2 else 0))
          ≤ 25 * (Cm * (Work.Spaces.WlInf α 4 f) ^ 2 * WProdWin.GmajW α g z θ) := by
        calc (∑ i ∈ Finset.range (4 + 1), ∑ j ∈ Finset.range (4 + 1),
              (if 1 ≤ i ∧ i + j ≤ 4 then
                (Work.Spaces.mixed j i (fun z θ => f z θ * g z θ) z θ
                  * Work.Spaces.Wt α z θ) ^ 2 else 0))
            ≤ ∑ _i ∈ Finset.range (4 + 1), ∑ _j ∈ Finset.range (4 + 1),
                (Cm * (Work.Spaces.WlInf α 4 f) ^ 2 * WProdWin.GmajW α g z θ) := by
              refine Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => ?_
              by_cases hc : 1 ≤ i ∧ i + j ≤ 4
              · rw [if_pos hc]
                exact hmslot i j hc.1 hc.2 z θ hzpos hθi.1 hθi.2
              · rw [if_neg hc]
                exact mul_nonneg (mul_nonneg (le_of_lt hCm0) (sq_nonneg _)) hGnn
          _ = 25 * (Cm * (Work.Spaces.WlInf α 4 f) ^ 2 * WProdWin.GmajW α g z θ) := by
              simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
      rw [Work.Spaces.HkIntegrand]
      calc (∑ i ∈ Finset.range (4 + 1),
            (Work.Spaces.DzIter i (fun z θ => f z θ * g z θ) z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          + (∑ i ∈ Finset.range (4 + 1), ∑ j ∈ Finset.range (4 + 1),
              (if 1 ≤ i ∧ i + j ≤ 4 then
                (Work.Spaces.mixed j i (fun z θ => f z θ * g z θ) z θ
                  * Work.Spaces.Wt α z θ) ^ 2 else 0))
          ≤ 5 * (Cz * (Work.Spaces.WlInf α 4 f) ^ 2 * WProdWin.GmajW α g z θ)
            + 25 * (Cm * (Work.Spaces.WlInf α 4 f) ^ 2 * WProdWin.GmajW α g z θ) :=
            add_le_add hsum1 hsum2
        _ = (5 * Cz + 25 * Cm) * (Work.Spaces.WlInf α 4 f) ^ 2 * WProdWin.GmajW α g z θ := by
            ring
    · have hsin : Real.sin (2 * θ) = 0 := Work.Spaces.sin_two_eq_zero_of_not_Ioo hθ hθi
      rw [Work.FTS.H2.WPQ.HkIntegrand_eq_zero_of_sin_two_eq_zero
        (F := fun z θ => f z θ * g z θ) (by rw [Work.Spaces.gam]; linarith) hsin]
      exact hbase

theorem wprod_field_winf :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ f g : Work.FTS.Galerkin.Fn,
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.WlInfMem α 4 f →
      Work.FTS.VocabO.HQo α 4 g →
      Work.Spaces.HkMem α 4 (fun z θ => f z θ * g z θ) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => f z θ * g z θ)
        ≤ C * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.WlInf α 4 f * Work.FTS.Nonlin.Xn α g := by
  obtain ⟨Cz, hCz0, hzslot⟩ := WProdWin.zslot_le_winf
  obtain ⟨CB, hCB0, hCmean⟩ := WProdWin.dzIter_w_mean_le
  obtain ⟨Cm, hCm0, hmslot⟩ := WProdWin.mslot_le_winf CB
  refine ⟨Real.sqrt (28701 * (5 * Cz + 25 * Cm)), Real.sqrt_pos.mpr (by linarith), ?_⟩
  intro α hα hα1 f g hf hfm hg
  obtain ⟨hgsm, hgm⟩ := hg
  set K : ℝ := 5 * Cz + 25 * Cm with hKdef
  set Kg : ℝ := 1 + 700 * (1 + 4 * (Work.Spaces.gam α - 1)⁻¹) with hKgdef
  have hKpos : 0 < K := by rw [hKdef]; linarith
  have hKgpos : 0 < Kg := by
    rw [hKgdef]
    have h1 : (0 : ℝ) < Work.Spaces.gam α - 1 := by rw [Work.Spaces.gam_sub_one]; linarith
    have h2 : 0 ≤ (Work.Spaces.gam α - 1)⁻¹ := inv_nonneg.mpr h1.le
    linarith
  have hWnn : 0 ≤ Work.Spaces.WlInf α 4 f := Work.FTS.H2.WPQ.WlInf_nonneg' hfm
  -- the product is smooth on the open quadrant
  have hfgsm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ * g z θ) :=
    hf.mul hgsm
  -- the pointwise majorant, with the two slot lemmas instantiated
  have hmajor : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 4 (fun z θ => f z θ * g z θ) z θ
        ≤ K * (Work.Spaces.WlInf α 4 f) ^ 2 * WProdWin.GmajW α g z θ := by
    have h := prod_majorant_winf hα hα1 hf hfm hgsm hgm hCz0 hCm0
      (fun i hi z θ hz hθ1 hθ2 => hzslot α f g hα hα1 hf hfm hgsm i hi z θ hz hθ1 hθ2)
      (fun I J hI hIJ z θ hz hθ1 hθ2 =>
        hmslot α f g hα hα1 hf hfm hgsm hgm
          (fun d hd z' θ' hz' hθ1' hθ2' => hCmean α g d hα hα1 hgsm hgm hd z' θ' hz' hθ1' hθ2')
          I J hI hIJ z θ hz hθ1 hθ2)
    intro z hz θ hθ
    rw [hKdef]
    exact h z hz θ hθ
  -- integrability of the angular slices of the product's integrand
  have hslice : ∀ z ∈ Work.Spaces.Iz, IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 4
      (fun z θ => f z θ * g z θ) z θ) Work.Spaces.Iθ := by
    intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hzz | hzpos
    · have hz0 : z = 0 := hzz.symm
      subst hz0
      have hzero : (fun θ => Work.Spaces.HkIntegrand α 4 (fun z θ => f z θ * g z θ) 0 θ)
          = fun _ : ℝ => (0 : ℝ) :=
        funext fun θ => Work.Spaces.HkIntegrand_zero_z α 4 _ θ
      rw [hzero]
      exact integrableOn_zero
    · refine Integrable.mono'
        ((WProdWin.GmajW_integrableOn_theta hα hα1 hgm hz).const_mul (K
          * (Work.Spaces.WlInf α 4 f) ^ 2)) ?_ ?_
      · exact Work.Spaces.aesm_slice_of_continuousOn_Qd _
          (hfgsm.continuousOn_HkIntegrand α 4) hzpos
      · filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
        rw [Real.norm_of_nonneg (Work.Spaces.HkIntegrand_nonneg α 4 _ z θ)]
        exact hmajor z hz θ hθ
  -- the angular integral of the majorant at every radius
  have hinner : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 (fun z θ => f z θ * g z θ) z θ)
        ≤ K * (Work.Spaces.WlInf α 4 f) ^ 2 * (Kg * WProdWin.HgInt α g z) := by
    intro z hz
    have hint : IntegrableOn (fun θ => (K * (Work.Spaces.WlInf α 4 f) ^ 2)
        * WProdWin.GmajW α g z θ) Work.Spaces.Iθ :=
      (WProdWin.GmajW_integrableOn_theta hα hα1 hgm hz).const_mul _
    have h1 : (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4
          (fun z θ => f z θ * g z θ) z θ)
        ≤ ∫ θ in Work.Spaces.Iθ, (K * (Work.Spaces.WlInf α 4 f) ^ 2)
            * WProdWin.GmajW α g z θ :=
      integral_mono_of_nonneg
        (Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 4 _ z θ) hint
        (ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => hmajor z hz θ hθ))
    rw [MeasureTheory.integral_const_mul] at h1
    have h2 : (∫ θ in Work.Spaces.Iθ, WProdWin.GmajW α g z θ)
        ≤ Kg * WProdWin.HgInt α g z := by
      simpa only [hKgdef] using WProdWin.GmajW_theta_integral_le hα hα1 hgm hz
    calc (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4
          (fun z θ => f z θ * g z θ) z θ)
        ≤ (K * (Work.Spaces.WlInf α 4 f) ^ 2)
            * (∫ θ in Work.Spaces.Iθ, WProdWin.GmajW α g z θ) := h1
      _ ≤ (K * (Work.Spaces.WlInf α 4 f) ^ 2) * (Kg * WProdWin.HgInt α g z) :=
          mul_le_mul_of_nonneg_left h2 (mul_nonneg hKpos.le (sq_nonneg _))
  -- the dominating function of the `z`-integral
  have hbdd : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 (fun z θ => f z θ * g z θ) z θ)
        ≤ (K * (Work.Spaces.WlInf α 4 f) ^ 2 * Kg) * WProdWin.HgInt α g z := by
    intro z hz
    have h1 := hinner z hz
    calc (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4
          (fun z θ => f z θ * g z θ) z θ)
        ≤ K * (Work.Spaces.WlInf α 4 f) ^ 2 * (Kg * WProdWin.HgInt α g z) := h1
      _ = (K * (Work.Spaces.WlInf α 4 f) ^ 2 * Kg) * WProdWin.HgInt α g z := by ring
  have hdom : IntegrableOn (fun z => (K * (Work.Spaces.WlInf α 4 f) ^ 2 * Kg)
      * WProdWin.HgInt α g z) Work.Spaces.Iz :=
    hgm.2.const_mul (K * (Work.Spaces.WlInf α 4 f) ^ 2 * Kg)
  -- a.e. strong measurability of the `z`-slice integral
  have haesm : AEStronglyMeasurable (fun z => ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 4 (fun z θ => f z θ * g z θ) z θ)
      (volume.restrict Work.Spaces.Iz) := by
    have h := (Work.Spaces.aesm_of_continuousOn_Qd
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 4 (fun z θ => f z θ * g z θ) p.1 p.2)
      (hfgsm.continuousOn_HkIntegrand α 4)).integral_prod_right'
    have hfun : (fun z => ∫ θ, Work.Spaces.HkIntegrand α 4 (fun z θ => f z θ * g z θ) z θ
          ∂(volume.restrict Work.Spaces.Iθ))
        = (fun z => ∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α 4 (fun z θ => f z θ * g z θ) z θ) := rfl
    rw [← hfun]
    exact h
  have hzg : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 4 (fun z θ => f z θ * g z θ) z θ) Work.Spaces.Iz := by
    refine Integrable.mono' hdom haesm ?_
    filter_upwards [ae_restrict_mem (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici)]
      with z hz
    rw [Real.norm_of_nonneg (integral_nonneg fun θ =>
      Work.Spaces.HkIntegrand_nonneg α 4 _ z θ)]
    exact hbdd z hz
  refine ⟨⟨hslice, hzg⟩, ?_⟩
  have hSq : Work.Spaces.HkSq α 4 (fun z θ => f z θ * g z θ)
      ≤ (K * (Work.Spaces.WlInf α 4 f) ^ 2 * Kg) * Work.Spaces.HkSq α 4 g := by
    have h1 : Work.Spaces.HkSq α 4 (fun z θ => f z θ * g z θ)
        ≤ ∫ z in Work.Spaces.Iz, (K * (Work.Spaces.WlInf α 4 f) ^ 2 * Kg)
            * WProdWin.HgInt α g z := by
      rw [Work.Spaces.HkSq]
      exact setIntegral_mono_of_nonneg
        (fun z _ => integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 4 _ z θ)
        (fun z hz => hbdd z hz) hdom
    refine le_trans h1 ?_
    rw [MeasureTheory.integral_const_mul, WProdWin.HgInt_z_integral]
  -- the passage to the `ℋ⁴`-norm
  have hXn : Work.FTS.Nonlin.Xn α (fun z θ => f z θ * g z θ)
      ≤ Real.sqrt (K * Kg) * Work.Spaces.WlInf α 4 f * Work.FTS.Nonlin.Xn α g := by
    have h1 : Real.sqrt (Work.Spaces.HkSq α 4 (fun z θ => f z θ * g z θ))
        ≤ Real.sqrt ((K * Kg) * (Work.Spaces.WlInf α 4 f) ^ 2 * Work.Spaces.HkSq α 4 g) := by
      refine Real.sqrt_le_sqrt ?_
      calc Work.Spaces.HkSq α 4 (fun z θ => f z θ * g z θ)
          ≤ (K * (Work.Spaces.WlInf α 4 f) ^ 2 * Kg) * Work.Spaces.HkSq α 4 g := hSq
        _ = (K * Kg) * (Work.Spaces.WlInf α 4 f) ^ 2 * Work.Spaces.HkSq α 4 g := by ring
    refine le_trans h1 ?_
    rw [show Work.FTS.Nonlin.Xn α g = Real.sqrt (Work.Spaces.HkSq α 4 g) from rfl,
      Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (K * Kg) * (Work.Spaces.WlInf α 4 f) ^ 2),
      Real.sqrt_mul (by positivity : (0 : ℝ) ≤ K * Kg),
      Real.sqrt_sq hWnn]
  refine le_trans hXn ?_
  -- `√(K Kg) ≤ √(28701 K) α^{-1/2}`
  have hKg_le : Kg ≤ 28701 * α⁻¹ := by
    have h1 : (0 : ℝ) < Work.Spaces.gam α - 1 := by rw [Work.Spaces.gam_sub_one]; linarith
    have hginv : (Work.Spaces.gam α - 1)⁻¹ = 10 / α := by
      rw [Work.Spaces.gam_sub_one, inv_div]
    have hαinv : (1 : ℝ) ≤ α⁻¹ := by rw [one_le_inv₀ hα]; exact hα1
    rw [hKgdef, hginv, div_eq_mul_inv]
    ring_nf
    nlinarith [hαinv]
  have hsqrt : Real.sqrt (K * Kg) ≤ Real.sqrt (28701 * K) * α ^ (-(1 / 2 : ℝ)) := by
    have h1 : K * Kg ≤ 28701 * K * α⁻¹ := by
      calc K * Kg ≤ K * (28701 * α⁻¹) := mul_le_mul_of_nonneg_left hKg_le hKpos.le
        _ = 28701 * K * α⁻¹ := by ring
    refine le_trans (Real.sqrt_le_sqrt h1) ?_
    rw [show (28701 : ℝ) * K * α⁻¹ = (28701 * K) * α⁻¹ from by ring,
      Real.sqrt_mul (show (0 : ℝ) ≤ 28701 * K by positivity),
      sqrt_inv_eq_rpow_neg_half hα]
  have hmain : Real.sqrt (K * Kg) * Work.Spaces.WlInf α 4 f * Work.FTS.Nonlin.Xn α g
      ≤ Real.sqrt (28701 * K) * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.WlInf α 4 f
        * Work.FTS.Nonlin.Xn α g := by
    calc Real.sqrt (K * Kg) * Work.Spaces.WlInf α 4 f * Work.FTS.Nonlin.Xn α g
        = Real.sqrt (K * Kg) * (Work.Spaces.WlInf α 4 f * Work.FTS.Nonlin.Xn α g) := by ring
      _ ≤ (Real.sqrt (28701 * K) * α ^ (-(1 / 2 : ℝ)))
            * (Work.Spaces.WlInf α 4 f * Work.FTS.Nonlin.Xn α g) :=
          mul_le_mul_of_nonneg_right hsqrt (mul_nonneg hWnn (Real.sqrt_nonneg _))
      _ = Real.sqrt (28701 * K) * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.WlInf α 4 f
            * Work.FTS.Nonlin.Xn α g := by ring
  calc Real.sqrt (K * Kg) * Work.Spaces.WlInf α 4 f * Work.FTS.Nonlin.Xn α g
      ≤ Real.sqrt (28701 * K) * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.WlInf α 4 f
          * Work.FTS.Nonlin.Xn α g := hmain
    _ = Real.sqrt (28701 * (5 * Cz + 25 * Cm)) * α ^ (-(1 / 2 : ℝ))
          * Work.Spaces.WlInf α 4 f * Work.FTS.Nonlin.Xn α g := by
        rw [hKdef]

end Work.FTS.OpenPkg
