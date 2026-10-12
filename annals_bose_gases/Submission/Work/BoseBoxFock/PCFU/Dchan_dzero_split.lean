import ChallengeDeps
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.BoseBoxFock.PCFU.Bchan_dzero_split
import Submission.Work.BoseBoxFock.PCFU.Dchan_eq_imageSum
import Submission.Work.BoseBoxFock.PCFU.imageSum_shift_split
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock.PCFU

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option linter.unusedVariables false

/-!
# `Work.BoseBoxFock.PCFU.Dchan_dzero_split`

The `d = 0` split of the `(D)`-channel at the image sum of the low cut-off kernel — the exact
`(D)`-twin of the proved `Work.BoseBoxFock.PCFU.Achan_dzero_split`/`Bchan_dzero_split`.

`Dchan_eq_imageSum` writes the `(D)`-channel as

    Dchan = ℓ³ ∫_x Θ(x)·∫_w χ_Λ(w)KχfrU(w)·∫_{u ∈ acube ℓ}
              (Σ'_d Κ(u + w + ℓ•latVec d))·Q_jP_iΘ(x[j↦u]) ,

with `Κ = lowKer fc κ` and `κ = (d²·ℓ)⁻¹`.  The present module performs the **exact** split of the
image sum into its `d = 0` term and the rest:

    Σ'_d Κ(u + w + ℓ•latVec d) = Κ(−w − u) + Σ'_{d ≠ 0} Κ(u + w + ℓ•latVec d) ,

and by the shift form of `lowSlot_eq_lowKer` (proved here, `lowSlot_update_shift`) the `d = 0`
term integrated against the fibre is *exactly* the word factor

    ∫_{u ∈ acube ℓ} Κ(−w−u)·Q_jP_iΘ(x[j↦u]) = lowSlot fc κ ℓ j (Q_jP_iΘ) (x[j ↦ −w]) .

The distribution of the double integral over the two pieces is the generic splitting lemma
`iterate_split` (a Bochner-integral identity), applied to the *jointly integrable* integrands on
`abox n ℓ ×ˢ boxL ℓ`. -/

/-! ## 1. Auxiliary lemmas -/

/-- **Generic iterate-split.**  If `f = f1 + f2` pointwise and the two joint integrands are
integrable on the product, then the iterated integral of `f` splits. -/
private theorem iterate_split {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
    (A : β → ℂ) (B : α → ℂ) (f f1 f2 : β → α → ℂ)
    (hpt : ∀ w x, f w x = f1 w x + f2 w x)
    (h1 : Integrable (fun p : α × β => A p.2 * (B p.1 * f1 p.2 p.1)) (μ.prod ν))
    (h2 : Integrable (fun p : α × β => A p.2 * (B p.1 * f2 p.2 p.1)) (μ.prod ν)) :
    (∫ x, B x * ∫ w, A w * f w x ∂ν ∂μ)
      = (∫ x, B x * ∫ w, A w * f1 w x ∂ν ∂μ)
        + (∫ x, B x * ∫ w, A w * f2 w x ∂ν ∂μ) := by
  have key : ∀ g : β → α → ℂ,
      Integrable (fun p : α × β => A p.2 * (B p.1 * g p.2 p.1)) (μ.prod ν) →
      (∫ p : α × β, A p.2 * (B p.1 * g p.2 p.1) ∂(μ.prod ν))
        = ∫ x, B x * ∫ w, A w * g w x ∂ν ∂μ := by
    intro g hg
    rw [MeasureTheory.integral_prod _ hg]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    show (∫ w : β, A w * (B x * g w x) ∂ν) = B x * ∫ w, A w * g w x ∂ν
    rw [show (fun w => A w * (B x * g w x)) = fun w => B x * (A w * g w x) from
      funext (fun w => by ring)]
    exact MeasureTheory.integral_const_mul _ _
  have hF := key f (h1.add h2 |>.congr (Filter.Eventually.of_forall (fun p => by
    simp only [Pi.add_apply]; rw [hpt p.2 p.1]; ring)))
  have hsum : (∫ p : α × β, A p.2 * (B p.1 * f p.2 p.1) ∂(μ.prod ν))
      = (∫ p : α × β, A p.2 * (B p.1 * f1 p.2 p.1) ∂(μ.prod ν))
        + ∫ p : α × β, A p.2 * (B p.1 * f2 p.2 p.1) ∂(μ.prod ν) := by
    rw [show (fun p : α × β => A p.2 * (B p.1 * f p.2 p.1))
        = (fun p : α × β => A p.2 * (B p.1 * f1 p.2 p.1))
          + (fun p : α × β => A p.2 * (B p.1 * f2 p.2 p.1)) from
      funext (fun p => by simp only [Pi.add_apply]; rw [hpt p.2 p.1]; ring)]
    exact MeasureTheory.integral_add h1 h2
  rw [← hF, hsum, key f1 h1, key f2 h2]

/-- `‖↑r‖ = |r|` for a real `r` seen in `ℂ`. -/
private lemma complexNorm_ofReal (r : ℝ) : ‖((r : ℝ) : ℂ)‖ = |r| := norm_ofReal_eq_abs r

/-- **The image sum of the low cut-off kernel in the `s`-frame form**
(`Ksfr_eq_lowKer`, rewritten as a division). -/
private lemma imageSum_eq_Ksfr {v : E3 → ℝ} {fc : Work.BoseBoxFix.LowCut} {μ : ℝ} {N : ℕ}
    (hℓ : 0 < Work.BoseBoxFock.ellH v μ)
    (hκ : 0 < ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
        * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹)
    (hN : 2 * (((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
        * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹) * Work.BoseBoxFock.ellH v μ
          / (2 * Real.pi) ≤ (N : ℝ)) (z : E3) :
    (∑' d : Fin 3 → ℤ, ((lowKer fc
        (((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
          * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹)
        (z + Work.BoseBoxFock.ellH v μ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))
      = (Work.BoseBoxFock.Ksfr v fc μ N z + 1) / ((Work.BoseBoxFock.ellH v μ : ℂ) ^ 3) := by
  have h := Ksfr_eq_lowKer (v := v) (fc := fc) (μ := μ) (N := N) hℓ hκ hN z
  have h3 : ((Work.BoseBoxFock.ellH v μ : ℂ)) ^ 3 ≠ 0 := by
    rw [← Complex.ofReal_pow, ne_eq, Complex.ofReal_eq_zero]
    exact pow_ne_zero 3 (ne_of_gt hℓ)
  rw [eq_div_iff h3, h]
  ring

/-- **The `d = 0` term of `lowSlot`**: the slot-`j` lift of the low-momentum multiplier at the
shifted configuration `x[j ↦ b]` is the set-integral of the low kernel against the fibre
`u ↦ ψ(x[j↦u])`. -/
private lemma lowSlot_update_shift {fc : Work.BoseBoxFix.LowCut} {κ ℓ C : ℝ}
    (hκ : 0 < κ) (hℓ : 0 < ℓ)
    {n : ℕ} (j : Fin n) (ψ : Submission.BoseGases.X n → ℝ) (x : Submission.BoseGases.X n)
    (b : E3)
    (hψm : AEStronglyMeasurable (fun z : E3 => ψ (Function.update x j z)) volume)
    (hψb : ∀ z ∈ Submission.BoseGases.acube ℓ, |ψ (Function.update x j z)| ≤ C) (hC : 0 ≤ C) :
    ((Work.BoseBoxFix.lowSlot fc κ ℓ j ψ (Function.update x j b) : ℝ) : ℂ)
      = ∫ u in Submission.BoseGases.acube ℓ,
          ((lowKer fc κ (b - u) : ℝ) : ℂ) * ((ψ (Function.update x j u) : ℝ) : ℂ) := by
  have hψm' : AEStronglyMeasurable
      (fun z : E3 => ψ (Function.update (Function.update x j b) j z)) volume := by
    simpa [Function.update_idem] using hψm
  have hψb' : ∀ z ∈ Submission.BoseGases.acube ℓ,
      |ψ (Function.update (Function.update x j b) j z)| ≤ C := by
    simpa [Function.update_idem] using hψb
  have hL := lowSlot_eq_lowKer (fc := fc) (κ := κ) (ℓ := ℓ) (C := C)
    hκ hℓ (n := n) j (Function.update x j b) hψm' hψb' hC
  rw [hL]
  simp only [Function.update_self, Function.update_idem]
  rw [show (∫ u in Submission.BoseGases.acube ℓ,
        ((lowKer fc κ (b - u) : ℝ) : ℂ) * ((ψ (Function.update x j u) : ℝ) : ℂ))
      = ∫ u in Submission.BoseGases.acube ℓ,
          ((lowKer fc κ (b - u) * ψ (Function.update x j u) : ℝ) : ℂ) from by
      refine MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.acube_measurable ℓ)
        (fun u _ => ?_)
      rw [Complex.ofReal_mul]]
  rw [show (∫ u in Submission.BoseGases.acube ℓ,
          ((lowKer fc κ (b - u) * ψ (Function.update x j u) : ℝ) : ℂ))
      = ((∫ u in Submission.BoseGases.acube ℓ,
          lowKer fc κ (b - u) * ψ (Function.update x j u) : ℝ) : ℂ) from integral_ofReal]
  congr 1
  rw [show (∫ u in Submission.BoseGases.acube ℓ,
          lowKer fc κ (b - u) * ψ (Function.update x j u))
      = ∫ u : E3, (Submission.BoseGases.acube ℓ).indicator
          (fun u => lowKer fc κ (b - u) * ψ (Function.update x j u)) u from
      (MeasureTheory.integral_indicator (μ := (volume : Measure E3))
        (Submission.BoseGases.acube_measurable ℓ)).symm]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
  by_cases hu : u ∈ Submission.BoseGases.acube ℓ
  · simp only [Set.indicator_of_mem hu]
  · simp only [Set.indicator_of_notMem hu, mul_zero]

/-- `Measure.real volume (acube ℓ) = ℓ³`. -/
private lemma real_volume_acube (ℓ : ℝ) (hℓ : 0 ≤ ℓ) :
    Measure.real (volume : Measure E3) (Submission.BoseGases.acube ℓ) = ℓ ^ 3 := by
  rw [MeasureTheory.Measure.real, Submission.BoseGases.acube_volume ℓ hℓ,
    ENNReal.toReal_ofReal (by positivity)]

/-- **The `(D)`-weight `χ_Λ` is bounded** (continuous with compact support). -/
private lemma chiLam_bound (ℓ : ℝ) (hℓ : 0 < ℓ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : E3,
      ‖((Work.BoseK15.corpusBox.chiLam ℓ w : ℝ) : ℂ)‖ ≤ C := by
  have hcont : Continuous fun w : E3 =>
      ((Work.BoseK15.corpusBox.chiLam ℓ w : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (Work.BoseB4.BoxData.chiLam_cont _ ℓ)
  obtain ⟨C, hC⟩ := (Work.BoseB4.BoxData.boxL_compact (B := Work.BoseK15.corpusBox) ℓ)
    |>.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun w => ?_⟩
  by_cases hw : Work.BoseK15.corpusBox.chiLam ℓ w = 0
  · rw [hw]; simp
  · have hmem : w ∈ Work.BoseK15.corpusBox.boxL ℓ :=
      Work.BoseB4.BoxData.chiLam_supp (B := Work.BoseK15.corpusBox) hℓ
        (Function.mem_support.mpr hw)
    exact le_trans (hC w hmem) (le_max_left _ _)

/-- Measurability of the `u`-integral in the `s`-frame form, as a function of `(x, w)`. -/
private lemma measurable_ksfrIntegral {n : ℕ} {v : E3 → ℝ} {fc : Work.BoseBoxFix.LowCut}
    {μ : ℝ} {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {ψ : Submission.BoseGases.X n → ℝ} (hψm : Measurable ψ) (j : Fin n) :
    Measurable (fun p : Submission.BoseGases.X n × E3 =>
      ∫ u in Submission.BoseGases.acube ℓ,
        ((Work.BoseBoxFock.Ksfr v fc μ N (u + p.2) + 1) / ((ℓ : ℂ) ^ 3))
          * ((ψ (Function.update p.1 j u) : ℝ) : ℂ)) := by
  haveI : SFinite ((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)) := inferInstance
  have hK : Continuous (fun q : (Submission.BoseGases.X n × E3) × E3 =>
      Work.BoseBoxFock.Ksfr v fc μ N (q.2 + q.1.2)) :=
    (continuous_Ksfr).comp (continuous_snd.add continuous_fst.snd)
  have hupd : Measurable (fun q : (Submission.BoseGases.X n × E3) × E3 =>
      Function.update q.1.1 j q.2) :=
    measurable_update'.comp ((measurable_fst.fst).prodMk measurable_snd)
  have hjoint : Measurable (fun q : (Submission.BoseGases.X n × E3) × E3 =>
      ((Work.BoseBoxFock.Ksfr v fc μ N (q.2 + q.1.2) + 1) / ((ℓ : ℂ) ^ 3))
        * ((ψ (Function.update q.1.1 j q.2) : ℝ) : ℂ)) :=
    (((hK.add continuous_const).measurable).div_const _).mul
      (Complex.measurable_ofReal.comp (hψm.comp hupd))
  exact (hjoint.stronglyMeasurable.integral_prod_right'
    (ν := (volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))).measurable

/-- Measurability of the shifted low-kernel integral, as a function of `(x, w)`. -/
private lemma measurable_lowKerShiftIntegral {n : ℕ} {fc : Work.BoseBoxFix.LowCut} {κ ℓ : ℝ}
    (hκ : 0 < κ) {ψ : Submission.BoseGases.X n → ℝ} (hψm : Measurable ψ) (j : Fin n) :
    Measurable (fun p : Submission.BoseGases.X n × E3 =>
      ∫ u in Submission.BoseGases.acube ℓ,
        ((lowKer fc κ (-p.2 - u) : ℝ) : ℂ) * ((ψ (Function.update p.1 j u) : ℝ) : ℂ)) := by
  haveI : SFinite ((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)) := inferInstance
  have hcont : Continuous (fun q : (Submission.BoseGases.X n × E3) × E3 =>
      ((lowKer fc κ (-q.1.2 - q.2) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp
      ((lowKer_regular fc hκ).1.comp (continuous_fst.snd.neg.sub continuous_snd))
  have hupd : Measurable (fun q : (Submission.BoseGases.X n × E3) × E3 =>
      Function.update q.1.1 j q.2) :=
    measurable_update'.comp ((measurable_fst.fst).prodMk measurable_snd)
  have hjoint : Measurable (fun q : (Submission.BoseGases.X n × E3) × E3 =>
      ((lowKer fc κ (-q.1.2 - q.2) : ℝ) : ℂ)
        * ((ψ (Function.update q.1.1 j q.2) : ℝ) : ℂ)) :=
    hcont.measurable.mul (Complex.measurable_ofReal.comp (hψm.comp hupd))
  exact (hjoint.stronglyMeasurable.integral_prod_right'
    (ν := (volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))).measurable

/-- Bound on the `s`-frame form of the `u`-integral. -/
private lemma norm_ksfrIntegral_le {n : ℕ} {v : E3 → ℝ} {fc : Work.BoseBoxFix.LowCut}
    {μ : ℝ} {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {ψ : Submission.BoseGases.X n → ℝ} {Cθ : ℝ} (hψabs : ∀ y, |ψ y| ≤ 2 * Cθ)
    (hCθ0 : 0 ≤ Cθ) {Ks : ℝ} (hKs : ∀ z : E3, ‖Work.BoseBoxFock.Ksfr v fc μ N z‖ ≤ Ks)
    (j : Fin n) (x : Submission.BoseGases.X n) (w : E3) :
    ‖∫ u in Submission.BoseGases.acube ℓ,
        ((Work.BoseBoxFock.Ksfr v fc μ N (u + w) + 1) / ((ℓ : ℂ) ^ 3))
          * ((ψ (Function.update x j u) : ℝ) : ℂ)‖ ≤ (Ks + 1) * (2 * Cθ) := by
  have hbound : ∀ u ∈ Submission.BoseGases.acube ℓ,
      ‖((Work.BoseBoxFock.Ksfr v fc μ N (u + w) + 1) / ((ℓ : ℂ) ^ 3))
          * ((ψ (Function.update x j u) : ℝ) : ℂ)‖ ≤ ((Ks + 1) / ℓ ^ 3) * (2 * Cθ) := by
    intro u _
    rw [norm_mul, complexNorm_ofReal]
    have hKs0 : 0 ≤ Ks := le_trans (norm_nonneg _) (hKs 0)
    have h1 : ‖(Work.BoseBoxFock.Ksfr v fc μ N (u + w) + 1) / ((ℓ : ℂ) ^ 3)‖
        ≤ (Ks + 1) / ℓ ^ 3 := by
      rw [norm_div]
      have h3 : ‖((ℓ : ℂ)) ^ 3‖ = ℓ ^ 3 := by
        rw [← Complex.ofReal_pow, complexNorm_ofReal, abs_of_nonneg (by positivity)]
      rw [h3]
      gcongr
      calc ‖Work.BoseBoxFock.Ksfr v fc μ N (u + w) + 1‖
          ≤ ‖Work.BoseBoxFock.Ksfr v fc μ N (u + w)‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
        _ ≤ Ks + 1 := by rw [norm_one]; exact add_le_add (hKs _) le_rfl
    exact mul_le_mul h1 (hψabs _) (abs_nonneg _) (div_nonneg (by linarith) (by positivity))
  have hfin := MeasureTheory.norm_setIntegral_le_of_norm_le_const
    (μ := (volume : Measure E3)) (s := Submission.BoseGases.acube ℓ)
    (f := fun u : E3 => ((Work.BoseBoxFock.Ksfr v fc μ N (u + w) + 1) / ((ℓ : ℂ) ^ 3))
      * ((ψ (Function.update x j u) : ℝ) : ℂ))
    (C := ((Ks + 1) / ℓ ^ 3) * (2 * Cθ))
    (Submission.BoseGases.acube_lt_top ℓ hℓ.le) hbound
  rw [real_volume_acube ℓ hℓ.le] at hfin
  calc ‖∫ u in Submission.BoseGases.acube ℓ,
        ((Work.BoseBoxFock.Ksfr v fc μ N (u + w) + 1) / ((ℓ : ℂ) ^ 3))
          * ((ψ (Function.update x j u) : ℝ) : ℂ)‖
      ≤ ((Ks + 1) / ℓ ^ 3) * (2 * Cθ) * ℓ ^ 3 := hfin
    _ = (Ks + 1) * (2 * Cθ) := by
        field_simp

/-- Bound on the shifted low-kernel integral. -/
private lemma norm_lowKerShiftIntegral_le {n : ℕ} {fc : Work.BoseBoxFix.LowCut} {κ ℓ : ℝ}
    (hℓ : 0 < ℓ) {ψ : Submission.BoseGases.X n → ℝ} {Cθ Cnlk : ℝ}
    (hψabs : ∀ y, |ψ y| ≤ 2 * Cθ) (hCθ0 : 0 ≤ Cθ)
    (hCnlk : ∀ z : E3, |lowKer fc κ z| ≤ Cnlk) (hCnlk0 : 0 ≤ Cnlk)
    (j : Fin n) (x : Submission.BoseGases.X n) (b : E3) :
    ‖∫ u in Submission.BoseGases.acube ℓ,
        ((lowKer fc κ (b - u) : ℝ) : ℂ) * ((ψ (Function.update x j u) : ℝ) : ℂ)‖
      ≤ Cnlk * (2 * Cθ) * ℓ ^ 3 := by
  have hbound : ∀ u ∈ Submission.BoseGases.acube ℓ,
      ‖((lowKer fc κ (b - u) : ℝ) : ℂ) * ((ψ (Function.update x j u) : ℝ) : ℂ)‖
        ≤ Cnlk * (2 * Cθ) := by
    intro u _
    rw [norm_mul, complexNorm_ofReal, complexNorm_ofReal]
    exact mul_le_mul (hCnlk _) (hψabs _) (abs_nonneg _) hCnlk0
  have hfin := MeasureTheory.norm_setIntegral_le_of_norm_le_const
    (μ := (volume : Measure E3)) (s := Submission.BoseGases.acube ℓ)
    (f := fun u : E3 => ((lowKer fc κ (b - u) : ℝ) : ℂ)
      * ((ψ (Function.update x j u) : ℝ) : ℂ))
    (C := Cnlk * (2 * Cθ)) (Submission.BoseGases.acube_lt_top ℓ hℓ.le) hbound
  rw [real_volume_acube ℓ hℓ.le] at hfin
  exact hfin

/-- **The `d = 0` split of the image sum, pointwise in `(w, x)`.** -/
private lemma imageSum_split_pointwise {fc : Work.BoseBoxFix.LowCut} {κ ℓ : ℝ}
    (hκ : 0 < κ) (hℓ : 0 < ℓ) {n : ℕ} (j : Fin n) (ψ : Submission.BoseGases.X n → ℝ)
    (hψm : Measurable ψ) (hψb : ∃ C : ℝ, ∀ y, ‖ψ y‖ ≤ C) (x : Submission.BoseGases.X n)
    (w : E3) :
    (∫ u in Submission.BoseGases.acube ℓ,
        (∑' d : Fin 3 → ℤ, ((lowKer fc κ (u + w + ℓ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))
          * ((ψ (Function.update x j u) : ℝ) : ℂ))
      = (∫ u in Submission.BoseGases.acube ℓ,
            ((lowKer fc κ (-w - u) : ℝ) : ℂ) * ((ψ (Function.update x j u) : ℝ) : ℂ))
        + ∫ u in Submission.BoseGases.acube ℓ,
            (∑' d : Fin 3 → ℤ, if d = 0 then (0 : ℂ)
                else ((lowKer fc κ (u + w + ℓ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))
              * ((ψ (Function.update x j u) : ℝ) : ℂ) := by
  have h := imageSum_shift_split fc hκ hℓ j ψ hψm hψb x (-w)
  simpa only [sub_neg_eq_add] using h

theorem Dchan_dzero_split {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut)
    (μ : ℝ) (N : ℕ)
    (hℓ : 0 < Work.BoseBoxFock.ellH v μ)
    (hκ : 0 < ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
        * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹)
    (hN : 2 * (((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
        * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹) * Work.BoseBoxFock.ellH v μ
          / (2 * Real.pi) ≤ (N : ℝ))
    (Θ : Submission.BoseGases.X n → ℝ) (hΘ : Submission.BoseGases.PermInvariant n Θ)
    (hΘm : Measurable Θ) (hΘb : ∃ C : ℝ, ∀ x, |Θ x| ≤ C)
    (hΘs : Function.support Θ ⊆ Submission.BoseGases.abox n (Work.BoseBoxFock.ellH v μ)) :
    (∫ q : Submission.BoseGases.X n
          × (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)),
        ((Θ q.1 : ℝ) : ℂ)
          * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) (q.1 i)
          * Work.BoseBoxFock.PCFU.ChDU v h fc fu μ N q.2.1 (q.1 j) q.2.2
          * ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ))
      = ((Work.BoseBoxFock.ellH v μ : ℂ)) ^ 3
          * (∫ x : Submission.BoseGases.X n,
              ((Θ x : ℝ) : ℂ)
                * (∫ w : EuclideanSpace ℝ (Fin 3),
                    ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) w : ℝ) : ℂ)
                      * Work.BoseBoxFock.PCFU.KχfrU v h μ fu N w
                      * ((Work.BoseBoxFix.lowSlot fc
                            (((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
                              * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹)
                            (Work.BoseBoxFock.ellH v μ) j
                            (Submission.BoseGases.aQ (Work.BoseBoxFock.ellH v μ) j
                              (Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ))
                            (Function.update x j (-w)) : ℝ) : ℂ)))
        + ((Work.BoseBoxFock.ellH v μ : ℂ)) ^ 3
          * (∫ x : Submission.BoseGases.X n,
              ((Θ x : ℝ) : ℂ)
                * (∫ w : EuclideanSpace ℝ (Fin 3),
                    ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) w : ℝ) : ℂ)
                      * Work.BoseBoxFock.PCFU.KχfrU v h μ fu N w
                      * (∫ u in Submission.BoseGases.acube (Work.BoseBoxFock.ellH v μ),
                          (∑' d : Fin 3 → ℤ, if d = 0 then (0 : ℂ)
                            else ((Work.BoseBoxFock.PCFU.lowKer fc
                              (((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
                                * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹)
                              (u + w + Work.BoseBoxFock.ellH v μ
                                • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))
                            * ((Submission.BoseGases.aQ (Work.BoseBoxFock.ellH v μ) j
                                (Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ)
                                (Function.update x j u) : ℝ) : ℂ)))) := by
  obtain ⟨Cθ, hCθ⟩ := hΘb
  have hCθ0 : 0 ≤ Cθ := le_trans (abs_nonneg (Θ 0)) (hCθ 0)
  -- step 1: the channel at the image sum
  rw [Dchan_eq_imageSum hij v h fc fu μ N hℓ hκ hN Θ hΘ hΘm ⟨Cθ, hCθ⟩ hΘs]
  -- abbreviations
  set ℓ : ℝ := Work.BoseBoxFock.ellH v μ with hℓdef
  set κ : ℝ := ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
      * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹ with hκdef
  set ψ : Submission.BoseGases.X n → ℝ :=
      Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ) with hψdef
  have hℓpos : 0 < ℓ := hℓ
  have hκpos : 0 < κ := hκ
  -- the weight `A`, the state weight `B` and the four integrands
  set A : E3 → ℂ := fun w => ((Work.BoseK15.corpusBox.chiLam ℓ w : ℝ) : ℂ)
      * Work.BoseBoxFock.PCFU.KχfrU v h μ fu N w with hAdef
  set B : Submission.BoseGases.X n → ℂ := fun x => ((Θ x : ℝ) : ℂ) with hBdef
  set I : E3 → Submission.BoseGases.X n → ℂ := fun w x =>
      ∫ u in Submission.BoseGases.acube ℓ,
        (∑' d : Fin 3 → ℤ, ((lowKer fc κ (u + w + ℓ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))
          * ((ψ (Function.update x j u) : ℝ) : ℂ) with hIdef
  set Iks : E3 → Submission.BoseGases.X n → ℂ := fun w x =>
      ∫ u in Submission.BoseGases.acube ℓ,
        ((Work.BoseBoxFock.Ksfr v fc μ N (u + w) + 1) / ((ℓ : ℂ) ^ 3))
          * ((ψ (Function.update x j u) : ℝ) : ℂ) with hIksdef
  set J1 : E3 → Submission.BoseGases.X n → ℂ := fun w x =>
      ((Work.BoseBoxFix.lowSlot fc κ ℓ j ψ (Function.update x j (-w)) : ℝ) : ℂ) with hJ1def
  set J1s : E3 → Submission.BoseGases.X n → ℂ := fun w x =>
      ∫ u in Submission.BoseGases.acube ℓ,
        ((lowKer fc κ (-w - u) : ℝ) : ℂ) * ((ψ (Function.update x j u) : ℝ) : ℂ) with hJ1sdef
  set J2 : E3 → Submission.BoseGases.X n → ℂ := fun w x =>
      ∫ u in Submission.BoseGases.acube ℓ,
        (∑' d : Fin 3 → ℤ, if d = 0 then (0 : ℂ)
            else ((lowKer fc κ (u + w + ℓ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))
          * ((ψ (Function.update x j u) : ℝ) : ℂ) with hJ2def
  -- shrink the goal to the abbreviation form
  change ((ℓ : ℂ)) ^ 3 * (∫ x, B x * ∫ w, A w * I w x)
      = ((ℓ : ℂ)) ^ 3 * (∫ x : Submission.BoseGases.X n, B x * ∫ w : E3, A w * J1 w x)
        + ((ℓ : ℂ)) ^ 3 * (∫ x : Submission.BoseGases.X n, B x * ∫ w : E3, A w * J2 w x)
  -- bounds on the state `ψ = Q_jP_iΘ`
  have hPabs : ∀ x : Submission.BoseGases.X n, |Submission.BoseGases.aP ℓ i Θ x| ≤ Cθ :=
    fun x => Work.BoseBoxFock.Weak.aP_abs_le hℓpos i hCθ0 hCθ x
  have hψabs : ∀ y : Submission.BoseGases.X n, |ψ y| ≤ 2 * Cθ := by
    intro y
    rw [hψdef]
    exact Work.BoseBoxFock.Weak.aQ_abs_le hℓpos j hCθ0 hPabs y
  have hψmeas : Measurable ψ := by
    rw [hψdef]
    exact Work.BoseBoxFock.Weak.aQ_measurable j (Work.BoseBoxFock.Weak.aP_measurable i hΘm)
  have hψbd : ∃ C : ℝ, ∀ y, ‖ψ y‖ ≤ C :=
    ⟨2 * Cθ, fun y => by rw [Real.norm_eq_abs]; exact hψabs y⟩
  -- bounds on the weights
  obtain ⟨Cχ, hCχ0, hCχ⟩ := chiLam_bound ℓ hℓpos
  set Kw : ℝ := ∑ k : Work.BoseBoxFock.Lab N,
      |Work.BoseBoxFock.W1h v h μ fu N k * Work.BoseBoxFock.hatChih v μ N k| with hKwdef
  have hKw0 : 0 ≤ Kw := by
    rw [hKwdef]; exact Finset.sum_nonneg (fun k _ => abs_nonneg _)
  set Ks : ℝ := ∑ s ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab N),
      |Work.BoseBoxFock.fLh v fc μ N s| with hKsdef
  have hKsb : ∀ z : E3, ‖Work.BoseBoxFock.Ksfr v fc μ N z‖ ≤ Ks := by
    intro z; rw [hKsdef]; exact norm_Ksfr_le z
  have hKwb : ∀ z : E3, ‖Work.BoseBoxFock.PCFU.KχfrU v h μ fu N z‖ ≤ Kw := by
    intro z; rw [hKwdef]; exact norm_KχfrU_le v h μ fu N z
  have hAmeas : Measurable A := by
    rw [hAdef]
    exact (Complex.measurable_ofReal.comp
      (Work.BoseB4.BoxData.chiLam_cont _ ℓ).measurable).mul (measurable_KχfrU v h μ fu N)
  have hAb : ∀ w : E3, ‖A w‖ ≤ Cχ * Kw := by
    intro w
    rw [hAdef]
    rw [norm_mul]
    exact mul_le_mul (hCχ w) (hKwb w) (norm_nonneg _) hCχ0
  have hBmeas : Measurable B := by
    rw [hBdef]
    exact Complex.measurable_ofReal.comp hΘm
  have hBb : ∀ x : Submission.BoseGases.X n, ‖B x‖ ≤ Cθ := by
    intro x
    rw [hBdef, complexNorm_ofReal]
    exact hCθ x
  -- the image sum in the `s`-frame form, at the abbreviations
  have hKsfr_id : ∀ z : E3, (∑' d : Fin 3 → ℤ,
      ((lowKer fc κ (z + ℓ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))
      = (Work.BoseBoxFock.Ksfr v fc μ N z + 1) / ((ℓ : ℂ) ^ 3) := by
    intro z
    rw [hκdef, hℓdef]
    exact imageSum_eq_Ksfr (v := v) (fc := fc) (μ := μ) (N := N) hℓ hκ hN z
  have hIIks : ∀ w x, I w x = Iks w x := by
    intro w x
    simp only [hIdef, hIksdef]
    refine MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.acube_measurable ℓ)
      (fun u _ => ?_)
    rw [hKsfr_id (u + w)]
  have hIksmeas : Measurable (fun p : Submission.BoseGases.X n × E3 => Iks p.2 p.1) :=
    measurable_ksfrIntegral (v := v) (fc := fc) (μ := μ) (N := N) hℓpos hψmeas j
  have hIksb : ∀ w x, ‖Iks w x‖ ≤ (Ks + 1) * (2 * Cθ) := fun w x =>
    norm_ksfrIntegral_le (v := v) (fc := fc) (μ := μ) (N := N) hℓpos hψabs hCθ0 hKsb j x w
  -- the `d = 0` piece is the word factor
  have hJ1s : ∀ w x, J1 w x = J1s w x := by
    intro w x
    rw [hJ1def, hJ1sdef]
    exact lowSlot_update_shift (fc := fc) (κ := κ) (ℓ := ℓ) (C := 2 * Cθ) hκpos hℓpos
      (n := n) j ψ x (-w)
      (hψmeas.comp (by fun_prop : Measurable (fun z : E3 => Function.update x j z))).aestronglyMeasurable
      (fun z _ => hψabs _) (by linarith)
  obtain ⟨-, Cnlk, hCnlk0, hCnlk⟩ := lowKer_regular fc hκpos
  have hJ1smeas : Measurable (fun p : Submission.BoseGases.X n × E3 => J1s p.2 p.1) :=
    measurable_lowKerShiftIntegral (fc := fc) (κ := κ) (ℓ := ℓ) hκpos hψmeas j
  have hJ1sb : ∀ w x, ‖J1s w x‖ ≤ Cnlk * (2 * Cθ) * ℓ ^ 3 := fun w x =>
    norm_lowKerShiftIntegral_le (fc := fc) (κ := κ) hℓpos hψabs hCθ0 hCnlk hCnlk0 j x (-w)
  -- the pointwise split
  have hsplit_s : ∀ w x, I w x = J1s w x + J2 w x := by
    intro w x
    simpa only [hIdef, hJ1sdef, hJ2def] using
      imageSum_split_pointwise (fc := fc) hκpos hℓpos j ψ hψmeas hψbd x w
  have hsplit : ∀ w x, I w x = J1 w x + J2 w x := fun w x => by
    rw [hsplit_s w x, ← hJ1s w x]
  -- joint integrability on the finite-measure support `abox n ℓ ×ˢ boxL ℓ`
  have hs : (volume : Measure (Submission.BoseGases.X n × E3))
      (Submission.BoseGases.abox n ℓ ×ˢ Work.BoseK15.corpusBox.boxL ℓ) < ⊤ := by
    change (volume.prod volume : Measure (Submission.BoseGases.X n × E3)) _ < ⊤
    rw [Measure.prod_prod]
    exact ENNReal.mul_lt_top (Submission.BoseGases.abox_lt_top n ℓ hℓpos.le)
      (by rw [Work.BoseB4.BoxData.volume_boxL (B := Work.BoseK15.corpusBox) hℓpos]
          exact ENNReal.ofReal_lt_top)
  have hsupp : ∀ p : Submission.BoseGases.X n × E3,
      p ∉ Submission.BoseGases.abox n ℓ ×ˢ Work.BoseK15.corpusBox.boxL ℓ →
      A p.2 * (B p.1 * Iks p.2 p.1) = 0 := by
    intro p hp
    by_cases h1 : p.1 ∈ Submission.BoseGases.abox n ℓ
    · have h2 : p.2 ∉ Work.BoseK15.corpusBox.boxL ℓ := fun h2 => hp ⟨h1, h2⟩
      have hχ : Work.BoseK15.corpusBox.chiLam ℓ p.2 = 0 := by
        by_contra hne
        exact h2 (Work.BoseB4.BoxData.chiLam_supp (B := Work.BoseK15.corpusBox) hℓpos
          (Function.mem_support.mpr hne))
      rw [hAdef]
      simp only [hχ, Complex.ofReal_zero, zero_mul]
    · have hΘ0 : Θ p.1 = 0 := by
        by_contra hne
        exact h1 (hΘs (Function.mem_support.mpr hne))
      rw [hBdef]
      simp only [hΘ0, Complex.ofReal_zero]
      ring
  have hAIks : Integrable (fun p : Submission.BoseGases.X n × E3 =>
      A p.2 * (B p.1 * Iks p.2 p.1)) (volume : Measure (Submission.BoseGases.X n × E3)) :=
    integrable_of_bounded_support (s := Submission.BoseGases.abox n ℓ
        ×ˢ Work.BoseK15.corpusBox.boxL ℓ) hs
      ((hAmeas.comp measurable_snd).mul ((hBmeas.comp measurable_fst).mul hIksmeas))
      (fun p => by
        simp only [norm_mul]
        exact mul_le_mul (hAb p.2)
          (mul_le_mul (hBb p.1) (hIksb p.2 p.1) (norm_nonneg _) hCθ0)
          (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (mul_nonneg hCχ0 hKw0))
      hsupp
  have hAI : Integrable (fun p : Submission.BoseGases.X n × E3 =>
      A p.2 * (B p.1 * I p.2 p.1)) (volume : Measure (Submission.BoseGases.X n × E3)) :=
    hAIks.congr (Filter.Eventually.of_forall (fun p => by
      simp only [hIIks p.2 p.1]))
  have hAJ1s : Integrable (fun p : Submission.BoseGases.X n × E3 =>
      A p.2 * (B p.1 * J1s p.2 p.1)) (volume : Measure (Submission.BoseGases.X n × E3)) :=
    integrable_of_bounded_support (s := Submission.BoseGases.abox n ℓ
        ×ˢ Work.BoseK15.corpusBox.boxL ℓ) hs
      ((hAmeas.comp measurable_snd).mul ((hBmeas.comp measurable_fst).mul hJ1smeas))
      (fun p => by
        simp only [norm_mul]
        exact mul_le_mul (hAb p.2)
          (mul_le_mul (hBb p.1) (hJ1sb p.2 p.1) (norm_nonneg _) hCθ0)
          (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (mul_nonneg hCχ0 hKw0))
      (fun p hp => by
        by_cases h1 : p.1 ∈ Submission.BoseGases.abox n ℓ
        · have h2 : p.2 ∉ Work.BoseK15.corpusBox.boxL ℓ := fun h2 => hp ⟨h1, h2⟩
          have hχ : Work.BoseK15.corpusBox.chiLam ℓ p.2 = 0 := by
            by_contra hne
            exact h2 (Work.BoseB4.BoxData.chiLam_supp (B := Work.BoseK15.corpusBox) hℓpos
              (Function.mem_support.mpr hne))
          rw [hAdef]
          simp only [hχ, Complex.ofReal_zero, zero_mul]
        · have hΘ0 : Θ p.1 = 0 := by
            by_contra hne
            exact h1 (hΘs (Function.mem_support.mpr hne))
          rw [hBdef]
          simp only [hΘ0, Complex.ofReal_zero]
          ring)
  have hAJ1 : Integrable (fun p : Submission.BoseGases.X n × E3 =>
      A p.2 * (B p.1 * J1 p.2 p.1)) (volume : Measure (Submission.BoseGases.X n × E3)) :=
    hAJ1s.congr (Filter.Eventually.of_forall (fun p => by
      simp only [← hJ1s p.2 p.1]))
  have hAJ2 : Integrable (fun p : Submission.BoseGases.X n × E3 =>
      A p.2 * (B p.1 * J2 p.2 p.1)) (volume : Measure (Submission.BoseGases.X n × E3)) :=
    (hAI.sub hAJ1).congr (Filter.Eventually.of_forall (fun p => by
      simp only [Pi.sub_apply]
      rw [hsplit p.2 p.1]
      ring))
  -- the generic split of the double integral
  have hstar := iterate_split (μ := (volume : Measure (Submission.BoseGases.X n)))
    (ν := (volume : Measure E3)) A B I J1 J2 hsplit hAJ1 hAJ2
  rw [hstar]
  ring

end Work.BoseBoxFock.PCFU
