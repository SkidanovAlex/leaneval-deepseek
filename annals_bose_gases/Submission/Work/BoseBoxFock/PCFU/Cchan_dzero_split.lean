import ChallengeDeps
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.BoseBoxFock.PCFU.Bchan_dzero_split
import Submission.Work.BoseBoxFock.PCFU.Cchan_eq_imageSum
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

set_option maxHeartbeats 12000000

/-!
# `Work.BoseBoxFock.PCFU.Cchan_dzero_split`

The `d = 0` split of the `(C)`-channel at the image sum of the low cut-off kernel.

`Cchan_eq_imageSum` writes the `(C)`-channel as

    Cchan = ℓ³ ∫_x Θ x·χ_Λ(x i)·∫_w χ_Λ(w)KfrU(x i + w)
                       ·∫_{u ∈ acube ℓ} (Σ'_d Κ(u + w + ℓ•latVec d))·Q_jP_iΘ(x[j↦u]) ,

with `Κ = lowKer fc κ`.  The present module performs the **exact** split of the image sum into its
`d = 0` term and the rest, *inside the `w`-integral*: by `imageSum_shift_split` at the shift
`b = -w` the inner `u`-integral is

    ∫_{u} Κ(-w − u)·Q_jP_iΘ(x[j↦u])  +  ∫_{u} (Σ'_{d ≠ 0} Κ(u + w + ℓ•latVec d))·Q_jP_iΘ(x[j↦u]) ,

and by `lowSlot_eq_lowKer` the first summand is *exactly* the word factor
`lowSlot fc κ ℓ j (Q_jP_iΘ) (x[j↦−w])`.  Distributing the `x`- and `w`-integrals (additivity of the
Bochner integral; all pieces are bounded with support in `abox n ℓ × boxL ℓ`) gives the target
identity.

## Layout

* §1 the auxiliary integrability bricks (`integrable_of_bounded_support_cd`,
  `summable_image_lowKer_gen`);
* §2 the target, with the two pieces of the inner integral named `L1` (`d = 0`) and `Lt` (tail).
-/

/-! ## 1. Auxiliary lemmas -/

/-- **A measurable bounded function supported in a set of finite measure is integrable.** -/
private theorem integrable_of_bounded_support_cd {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {s : Set α} (hs : μ s < ⊤) {f : α → ℂ} (hm : Measurable f)
    (hb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) (hsup : Function.support f ⊆ s) : Integrable f μ := by
  obtain ⟨C, hC⟩ := hb
  refine (MeasureTheory.integrableOn_iff_integrable_of_support_subset (μ := μ) (s := s)
    (f := f) hsup).mp ?_
  exact MeasureTheory.IntegrableOn.of_bound (s := s) (μ := μ) hs
    hm.aestronglyMeasurable.restrict (max C 0)
    (Filter.Eventually.of_forall fun x => le_trans (hC x) (le_max_left _ _))

/-- `latVec 0 = 0`. -/
private lemma latVec_zero_cd : Work.BoseBoxFock.latVec (0 : Fin 3 → ℤ) = (0 : E3) := by
  ext i
  simp [Work.BoseBoxFock.latVec]

/-- `‖↑r‖ = |r|` for a real `r` seen in `ℂ`. -/
private lemma complexNorm_ofReal_cd (r : ℝ) : ‖((r : ℝ) : ℂ)‖ = |r| := norm_ofReal_eq_abs r

/-- **Summability of the image sum** of the low-momentum kernel along the lattice, at a general
scale `ℓ` and a general cut-off `κ`.  `lowKer_decay` gives `(1 + ‖·‖)^{-4}` decay, which is
summable on `ℤ³` (`summable_shift_latVec`). -/
private lemma summable_image_lowKer_gen {fc : Work.BoseBoxFix.LowCut} {κ ℓ : ℝ}
    (hκ : 0 < κ) (hℓ : 0 < ℓ) (z : E3) :
    Summable (fun d : Fin 3 → ℤ =>
      ((lowKer fc κ (z + ℓ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ)) := by
  obtain ⟨C, hC0, hC⟩ := lowKer_decay fc hκ 2
  have h4 : ∀ q : E3, (0 : ℝ) < (1 + ‖q‖) ^ 4 := fun q => by positivity
  refine Work.BoseBoxFock.summable_shift_latVec (Φ := fun q : E3 => ((lowKer fc κ q : ℝ) : ℂ))
    (C := C) hC0 (fun q => ?_) hℓ z
  rw [complexNorm_ofReal_cd, ← Real.norm_eq_abs]
  calc ‖lowKer fc κ q‖
      = ((1 + ‖q‖) ^ 4)⁻¹ * ((1 + ‖q‖) ^ 4 * ‖lowKer fc κ q‖) := by
        rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt (h4 q)), one_mul]
    _ ≤ ((1 + ‖q‖) ^ 4)⁻¹ * C := mul_le_mul_of_nonneg_left (hC q) (inv_nonneg.mpr (h4 q).le)
    _ = C * (1 + ‖q‖) ^ (-((4 : ℕ) : ℤ)) := by rw [zpow_neg, zpow_natCast]; ring

/-! ## 2. The target -/

theorem Cchan_dzero_split {n : ℕ} {i j : Fin n} (hij : i ≠ j)
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
          * Work.BoseBoxFock.PCFU.ChCU v h fc fu μ N q.2.1 (q.1 j) q.2.2
          * ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ))
      = ((Work.BoseBoxFock.ellH v μ : ℂ)) ^ 3
          * (∫ x : Submission.BoseGases.X n,
              ((Θ x : ℝ) : ℂ)
                * ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) (x i) : ℝ) : ℂ)
                * (∫ w : EuclideanSpace ℝ (Fin 3),
                    ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) w : ℝ) : ℂ)
                      * Work.BoseBoxFock.PCFU.KfrU v h μ fu N (x i + w)
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
                * ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) (x i) : ℝ) : ℂ)
                * (∫ w : EuclideanSpace ℝ (Fin 3),
                    ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) w : ℝ) : ℂ)
                      * Work.BoseBoxFock.PCFU.KfrU v h μ fu N (x i + w)
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
  have hCθn : ∀ y : Submission.BoseGases.X n, ‖Θ y‖ ≤ Cθ :=
    fun y => by rw [Real.norm_eq_abs]; exact hCθ y
  -- ## abbreviations
  set ℓ : ℝ := Work.BoseBoxFock.ellH v μ with hℓdef
  set κ : ℝ := ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
      * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹ with hκdef
  have hℓpos : 0 < ℓ := hℓ
  have hκpos : 0 < κ := hκ
  have hΘs' : Function.support Θ ⊆ Submission.BoseGases.abox n ℓ := hΘs
  set ψ : Submission.BoseGases.X n → ℝ :=
      Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ) with hψdef
  have hPabs : ∀ y : Submission.BoseGases.X n, |Submission.BoseGases.aP ℓ i Θ y| ≤ Cθ :=
    fun y => Work.BoseBoxFock.Weak.aP_abs_le hℓpos i hCθ0 hCθ y
  have hψabs : ∀ y : Submission.BoseGases.X n, |ψ y| ≤ 2 * Cθ := by
    intro y
    rw [hψdef]
    exact Work.BoseBoxFock.Weak.aQ_abs_le hℓpos j hCθ0 hPabs y
  have hψm : Measurable ψ := by
    rw [hψdef]
    exact Work.BoseBoxFock.Weak.aQ_measurable j (Work.BoseBoxFock.Weak.aP_measurable i hΘm)
  have hψb : ∃ C : ℝ, ∀ y : Submission.BoseGases.X n, ‖ψ y‖ ≤ C :=
    ⟨2 * Cθ, fun y => by rw [Real.norm_eq_abs]; exact hψabs y⟩
  have hCψ0 : 0 ≤ 2 * Cθ := by linarith
  -- ## the weight bounds
  set Kw : ℝ := ∑ k : Work.BoseBoxFock.Lab N, |Work.BoseBoxFock.W1h v h μ fu N k| with hKwdef
  have hKw0 : 0 ≤ Kw := by rw [hKwdef]; exact Finset.sum_nonneg fun k _ => abs_nonneg _
  have hKwb : ∀ z : E3, ‖Work.BoseBoxFock.PCFU.KfrU v h μ fu N z‖ ≤ Kw := fun z => by
    rw [hKwdef]; exact norm_KfrU_le v h μ fu N z
  set Ks : ℝ := ∑ s ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab N),
      |Work.BoseBoxFock.fLh v fc μ N s| with hKsdef
  have hKs0 : 0 ≤ Ks := by rw [hKsdef]; exact Finset.sum_nonneg fun s _ => abs_nonneg _
  have hKsb : ∀ z : E3, ‖Work.BoseBoxFock.Ksfr v fc μ N z‖ ≤ Ks := fun z => by
    rw [hKsdef]; exact norm_Ksfr_le z
  set Cχ : ℝ := (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹ with hCχdef
  have hCχ0 : 0 ≤ Cχ := by rw [hCχdef]; exact inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hχb : ∀ z : E3, ‖((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ)‖ ≤ Cχ := fun z => by
    rw [hCχdef]; exact norm_chiLam_le ℓ z
  obtain ⟨-, Cnlk, hCnlk0, hCnlkAbs⟩ := lowKer_regular fc hκpos
  have hlkcont : Continuous (lowKer fc κ) := (lowKer_regular fc hκpos).1
  have hboxLfin : (volume : Measure E3) (Work.BoseB4.BoxData.boxL Work.BoseK15.corpusBox ℓ)
      < ⊤ := by
    rw [Work.BoseB4.BoxData.volume_boxL (B := Work.BoseK15.corpusBox) hℓpos]
    exact ENNReal.ofReal_lt_top
  -- ## the named integrands
  set G : Submission.BoseGases.X n → ℂ := fun x => ((Θ x : ℝ) : ℂ)
      * ((Work.BoseK15.corpusBox.chiLam ℓ (x i) : ℝ) : ℂ) with hGdef
  set Qw : Submission.BoseGases.X n → E3 → ℂ := fun x w =>
      ((Work.BoseK15.corpusBox.chiLam ℓ w : ℝ) : ℂ)
        * Work.BoseBoxFock.PCFU.KfrU v h μ fu N (x i + w) with hQwdef
  set Lw : Submission.BoseGases.X n → E3 → ℂ := fun x w =>
      ∫ u in Submission.BoseGases.acube ℓ,
        (∑' d : Fin 3 → ℤ, ((lowKer fc κ (u + w + ℓ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))
          * ((ψ (Function.update x j u) : ℝ) : ℂ) with hLwdef
  set L1 : Submission.BoseGases.X n → E3 → ℂ := fun x w =>
      ∫ u in Submission.BoseGases.acube ℓ,
        ((lowKer fc κ (-w - u) : ℝ) : ℂ) * ((ψ (Function.update x j u) : ℝ) : ℂ) with hL1def
  set Lt : Submission.BoseGases.X n → E3 → ℂ := fun x w =>
      ∫ u in Submission.BoseGases.acube ℓ,
        (∑' d : Fin 3 → ℤ, if d = 0 then (0 : ℂ)
            else ((lowKer fc κ (u + w + ℓ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))
          * ((ψ (Function.update x j u) : ℝ) : ℂ) with hLtdef
  set Pfun : Submission.BoseGases.X n → E3 → ℂ := fun x w =>
      ((Work.BoseBoxFix.lowSlot fc κ ℓ j ψ (Function.update x j (-w)) : ℝ) : ℂ) with hPdef
  set Jfull : Submission.BoseGases.X n → ℂ := fun x => ∫ w : E3, Qw x w * Lw x w with hJdef
  set A1 : Submission.BoseGases.X n → ℂ := fun x => ∫ w : E3, Qw x w * Pfun x w with hA1def
  set A2 : Submission.BoseGases.X n → ℂ := fun x => ∫ w : E3, Qw x w * Lt x w with hA2def
  -- the same expansions as universally quantified `rfl`-lemmas, so that rewriting an *application*
  -- never leaves a beta-redex behind
  have hGval : ∀ x : Submission.BoseGases.X n, G x = ((Θ x : ℝ) : ℂ)
      * ((Work.BoseK15.corpusBox.chiLam ℓ (x i) : ℝ) : ℂ) := fun x => rfl
  have hQwval : ∀ (x : Submission.BoseGases.X n) (w : E3), Qw x w =
      ((Work.BoseK15.corpusBox.chiLam ℓ w : ℝ) : ℂ)
        * Work.BoseBoxFock.PCFU.KfrU v h μ fu N (x i + w) := fun x w => rfl
  have hLwval : ∀ (x : Submission.BoseGases.X n) (w : E3), Lw x w =
      ∫ u in Submission.BoseGases.acube ℓ,
        (∑' d : Fin 3 → ℤ, ((lowKer fc κ (u + w + ℓ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))
          * ((ψ (Function.update x j u) : ℝ) : ℂ) := fun x w => rfl
  have hL1val : ∀ (x : Submission.BoseGases.X n) (w : E3), L1 x w =
      ∫ u in Submission.BoseGases.acube ℓ,
        ((lowKer fc κ (-w - u) : ℝ) : ℂ) * ((ψ (Function.update x j u) : ℝ) : ℂ) := fun x w => rfl
  have hLtval : ∀ (x : Submission.BoseGases.X n) (w : E3), Lt x w =
      ∫ u in Submission.BoseGases.acube ℓ,
        (∑' d : Fin 3 → ℤ, if d = 0 then (0 : ℂ)
            else ((lowKer fc κ (u + w + ℓ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))
          * ((ψ (Function.update x j u) : ℝ) : ℂ) := fun x w => rfl
  have hPval : ∀ (x : Submission.BoseGases.X n) (w : E3), Pfun x w =
      ((Work.BoseBoxFix.lowSlot fc κ ℓ j ψ (Function.update x j (-w)) : ℝ) : ℂ) := fun x w => rfl
  have hJval : ∀ x : Submission.BoseGases.X n, Jfull x = ∫ w : E3, Qw x w * Lw x w := fun x => rfl
  have hA1val : ∀ x : Submission.BoseGases.X n, A1 x = ∫ w : E3, Qw x w * Pfun x w := fun x => rfl
  have hA2val : ∀ x : Submission.BoseGases.X n, A2 x = ∫ w : E3, Qw x w * Lt x w := fun x => rfl
  -- ## measurability of the named functions
  have hGm : Measurable G := by
    rw [hGdef]
    exact (Complex.measurable_ofReal.comp hΘm).mul
      (Complex.measurable_ofReal.comp (((Work.BoseB4.BoxData.chiLam_cont
        Work.BoseK15.corpusBox ℓ).measurable).comp (measurable_pi_apply i)))
  have hGb : ∀ x : Submission.BoseGases.X n, ‖G x‖ ≤ Cθ * Cχ := by
    intro x
    rw [hGdef, norm_mul]
    refine mul_le_mul ?_ (hχb (x i)) (norm_nonneg _) hCθ0
    rw [complexNorm_ofReal_cd]
    exact hCθ x
  have hGs : Function.support G ⊆ Submission.BoseGases.abox n ℓ := by
    intro x hx
    apply hΘs'
    rw [Function.mem_support] at hx ⊢
    intro h0
    exact hx (by rw [hGdef]; simp [h0])
  have hQwm : Measurable (fun p : Submission.BoseGases.X n × E3 => Qw p.1 p.2) := by
    rw [hQwdef]
    exact (Complex.measurable_ofReal.comp (((Work.BoseB4.BoxData.chiLam_cont
        Work.BoseK15.corpusBox ℓ).measurable).comp measurable_snd)).mul
      (((continuous_KfrU v h μ fu N).comp
        (((continuous_apply i).comp continuous_fst).add continuous_snd)).measurable)
  have hQwb : ∀ x w, ‖Qw x w‖ ≤ Cχ * Kw := by
    intro x w
    rw [hQwdef, norm_mul]
    exact mul_le_mul (hχb w) (hKwb _) (norm_nonneg _) hCχ0
  have hL1m : Measurable (fun p : Submission.BoseGases.X n × E3 => L1 p.1 p.2) := by
    rw [hL1def]
    have hjoint : Measurable (fun q : (Submission.BoseGases.X n × E3) × E3 =>
        ((lowKer fc κ (-q.1.2 - q.2) : ℝ) : ℂ)
          * ((ψ (Function.update q.1.1 j q.2) : ℝ) : ℂ)) := by
      refine (Complex.measurable_ofReal.comp (hlkcont.measurable.comp ?_)).mul
        (Complex.measurable_ofReal.comp (hψm.comp ?_))
      · exact (((continuous_snd.comp continuous_fst).neg).sub continuous_snd).measurable
      · exact measurable_update'.comp ((measurable_fst.fst).prodMk measurable_snd)
    exact (hjoint.stronglyMeasurable.integral_prod_right'
      (ν := (volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))).measurable
  -- ## the tail in `s`-frame form
  have htailEq : ∀ z : E3,
      (∑' d : Fin 3 → ℤ, if d = 0 then (0 : ℂ)
          else ((lowKer fc κ (z + ℓ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))
        = (Work.BoseBoxFock.Ksfr v fc μ N z + 1) / ((ℓ : ℂ) ^ 3)
          - ((lowKer fc κ z : ℝ) : ℂ) := by
    intro z
    have hsumm := summable_image_lowKer_gen (fc := fc) (κ := κ) (ℓ := ℓ) hκpos hℓpos z
    have h1 := hsumm.tsum_eq_add_tsum_ite (0 : Fin 3 → ℤ)
    have h2 : (∑' d : Fin 3 → ℤ, ((lowKer fc κ (z + ℓ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))
        = ((lowKer fc κ z : ℝ) : ℂ)
          + ∑' d : Fin 3 → ℤ, if d = 0 then (0 : ℂ)
              else ((lowKer fc κ (z + ℓ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ) := by
      simpa [latVec_zero_cd, smul_zero, add_zero] using h1
    have hKsfr := Ksfr_eq_lowKer (v := v) (fc := fc) (μ := μ) (N := N) hℓ hκ hN z
    rw [← hℓdef, ← hκdef] at hKsfr
    have h3 : ((ℓ : ℂ)) ^ 3 ≠ 0 := by
      rw [← Complex.ofReal_pow, ne_eq, Complex.ofReal_eq_zero]
      exact pow_ne_zero 3 (ne_of_gt hℓpos)
    have h4 : (∑' d : Fin 3 → ℤ, ((lowKer fc κ (z + ℓ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))
        = (Work.BoseBoxFock.Ksfr v fc μ N z + 1) / ((ℓ : ℂ) ^ 3) := by
      rw [eq_div_iff h3, hKsfr]
      ring
    rw [h4] at h2
    rw [h2]
    ring
  have hLt_eq : ∀ x w, Lt x w =
      ∫ u in Submission.BoseGases.acube ℓ,
        (((Work.BoseBoxFock.Ksfr v fc μ N (u + w) + 1) / ((ℓ : ℂ) ^ 3))
            - ((lowKer fc κ (u + w) : ℝ) : ℂ))
          * ((ψ (Function.update x j u) : ℝ) : ℂ) := by
    intro x w
    rw [hLtdef]
    exact MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.acube_measurable ℓ)
      (fun u _ => by rw [htailEq (u + w)])
  have hLtm : Measurable (fun p : Submission.BoseGases.X n × E3 => Lt p.1 p.2) := by
    have heq : (fun p : Submission.BoseGases.X n × E3 => Lt p.1 p.2)
        = fun p : Submission.BoseGases.X n × E3 =>
            ∫ u in Submission.BoseGases.acube ℓ,
              (((Work.BoseBoxFock.Ksfr v fc μ N (u + p.2) + 1) / ((ℓ : ℂ) ^ 3))
                  - ((lowKer fc κ (u + p.2) : ℝ) : ℂ))
                * ((ψ (Function.update p.1 j u) : ℝ) : ℂ) := by
      funext p
      exact hLt_eq p.1 p.2
    rw [heq]
    have hcont1 : Continuous (fun q : (Submission.BoseGases.X n × E3) × E3 =>
        ((Work.BoseBoxFock.Ksfr v fc μ N (q.2 + q.1.2) + 1) / ((ℓ : ℂ) ^ 3))
          - ((lowKer fc κ (q.2 + q.1.2) : ℝ) : ℂ)) := by
      have hA : Continuous (fun q : (Submission.BoseGases.X n × E3) × E3 =>
          Work.BoseBoxFock.Ksfr v fc μ N (q.2 + q.1.2)) :=
        (continuous_Ksfr (v := v) (fc := fc) (μ := μ) (N := N)).comp (by fun_prop)
      have hB : Continuous (fun q : (Submission.BoseGases.X n × E3) × E3 =>
          ((lowKer fc κ (q.2 + q.1.2) : ℝ) : ℂ)) :=
        Complex.continuous_ofReal.comp (hlkcont.comp (by fun_prop))
      exact ((hA.add continuous_const).div_const _).sub hB
    have hD : Measurable (fun q : (Submission.BoseGases.X n × E3) × E3 =>
        ((ψ (Function.update q.1.1 j q.2) : ℝ) : ℂ)) :=
      Complex.measurable_ofReal.comp (hψm.comp
        (measurable_update'.comp ((measurable_fst.fst).prodMk measurable_snd)))
    have hjoint : Measurable (fun q : (Submission.BoseGases.X n × E3) × E3 =>
        (((Work.BoseBoxFock.Ksfr v fc μ N (q.2 + q.1.2) + 1) / ((ℓ : ℂ) ^ 3))
            - ((lowKer fc κ (q.2 + q.1.2) : ℝ) : ℂ))
          * ((ψ (Function.update q.1.1 j q.2) : ℝ) : ℂ)) := hcont1.measurable.mul hD
    exact (hjoint.stronglyMeasurable.integral_prod_right'
      (ν := (volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))).measurable
  -- ## bounds on the two pieces
  have hL1b : ∀ x w, ‖L1 x w‖ ≤ Cnlk * (2 * Cθ) * ℓ ^ 3 := by
    intro x w
    rw [hL1def]
    haveI : IsFiniteMeasure ((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)) :=
      MeasureTheory.isFiniteMeasure_restrict.mpr
        (ne_of_lt (Submission.BoseGases.acube_lt_top ℓ hℓpos.le))
    have hbd : ∀ᵐ u ∂((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)),
        ‖((lowKer fc κ (-w - u) : ℝ) : ℂ) * ((ψ (Function.update x j u) : ℝ) : ℂ)‖
          ≤ Cnlk * (2 * Cθ) := by
      filter_upwards with u
      rw [norm_mul, complexNorm_ofReal_cd, complexNorm_ofReal_cd]
      exact mul_le_mul (hCnlkAbs _) (hψabs _) (abs_nonneg _) hCnlk0
    have hfin := MeasureTheory.norm_integral_le_of_norm_le_const
      (μ := (volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)) hbd
    rw [Submission.BoseGases.real_volume_acube ℓ hℓpos.le] at hfin
    exact hfin
  have himg : ∀ z : E3,
      ‖(Work.BoseBoxFock.Ksfr v fc μ N z + 1) / ((ℓ : ℂ) ^ 3)‖ ≤ (Ks + 1) / ℓ ^ 3 := by
    intro z
    rw [norm_div]
    have h3 : ‖((ℓ : ℂ)) ^ 3‖ = ℓ ^ 3 := by
      rw [← Complex.ofReal_pow, complexNorm_ofReal_cd]
      exact abs_of_nonneg (by positivity)
    rw [h3]
    gcongr
    calc ‖Work.BoseBoxFock.Ksfr v fc μ N z + 1‖
          ≤ ‖Work.BoseBoxFock.Ksfr v fc μ N z‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ Ks + 1 := by rw [norm_one]; exact add_le_add (hKsb z) le_rfl
  have hLtb : ∀ x w, ‖Lt x w‖ ≤ ((Ks + 1) / ℓ ^ 3 + Cnlk) * (2 * Cθ) * ℓ ^ 3 := by
    intro x w
    rw [hLt_eq x w]
    haveI : IsFiniteMeasure ((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)) :=
      MeasureTheory.isFiniteMeasure_restrict.mpr
        (ne_of_lt (Submission.BoseGases.acube_lt_top ℓ hℓpos.le))
    have hbd : ∀ᵐ u ∂((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)),
        ‖((((Work.BoseBoxFock.Ksfr v fc μ N (u + w) + 1) / ((ℓ : ℂ) ^ 3))
            - ((lowKer fc κ (u + w) : ℝ) : ℂ)))
          * ((ψ (Function.update x j u) : ℝ) : ℂ)‖ ≤ ((Ks + 1) / ℓ ^ 3 + Cnlk) * (2 * Cθ) := by
      filter_upwards with u
      rw [norm_mul, complexNorm_ofReal_cd]
      refine mul_le_mul ?_ (hψabs _) (abs_nonneg _)
        (add_nonneg (div_nonneg (by linarith) (by positivity)) hCnlk0)
      calc ‖((Work.BoseBoxFock.Ksfr v fc μ N (u + w) + 1) / ((ℓ : ℂ) ^ 3))
              - ((lowKer fc κ (u + w) : ℝ) : ℂ)‖
          ≤ ‖(Work.BoseBoxFock.Ksfr v fc μ N (u + w) + 1) / ((ℓ : ℂ) ^ 3)‖
              + ‖((lowKer fc κ (u + w) : ℝ) : ℂ)‖ := norm_sub_le _ _
        _ ≤ (Ks + 1) / ℓ ^ 3 + Cnlk :=
            add_le_add (himg _) (by rw [complexNorm_ofReal_cd]; exact hCnlkAbs _)
    have hfin := MeasureTheory.norm_integral_le_of_norm_le_const
      (μ := (volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)) hbd
    rw [Submission.BoseGases.real_volume_acube ℓ hℓpos.le] at hfin
    exact hfin
  -- ## §3a: the `d = 0` piece is the word factor `lowSlot`
  have hP1eq : ∀ x w, L1 x w = Pfun x w := by
    intro x w
    have hfib_m : AEStronglyMeasurable
        (fun z : E3 => ψ (Function.update (Function.update x j (-w)) j z)) volume :=
      (hψm.comp (by fun_prop : Measurable fun z : E3 =>
        Function.update (Function.update x j (-w)) j z)).aestronglyMeasurable
    have hfib_b : ∀ z ∈ Submission.BoseGases.acube ℓ,
        |ψ (Function.update (Function.update x j (-w)) j z)| ≤ 2 * Cθ := fun z _ => hψabs _
    have hL := lowSlot_eq_lowKer (fc := fc) (κ := κ) (ℓ := ℓ) (C := 2 * Cθ) (Ψ := ψ)
      hκpos hℓpos (n := n) j (Function.update x j (-w)) hfib_m hfib_b hCψ0
    have hL' : Work.BoseBoxFix.lowSlot fc κ ℓ j ψ (Function.update x j (-w))
        = ∫ z : E3, lowKer fc κ (-w - z)
            * (Submission.BoseGases.acube ℓ).indicator
                (fun z : E3 => ψ (Function.update x j z)) z := by
      simpa only [Function.update_self, Function.update_idem] using hL
    rw [hL1def, hPdef]
    show (∫ u in Submission.BoseGases.acube ℓ,
        ((lowKer fc κ (-w - u) : ℝ) : ℂ) * ((ψ (Function.update x j u) : ℝ) : ℂ))
      = ((Work.BoseBoxFix.lowSlot fc κ ℓ j ψ (Function.update x j (-w)) : ℝ) : ℂ)
    rw [hL']
    rw [show (∫ u in Submission.BoseGases.acube ℓ,
          ((lowKer fc κ (-w - u) : ℝ) : ℂ) * ((ψ (Function.update x j u) : ℝ) : ℂ))
        = ∫ u in Submission.BoseGases.acube ℓ,
            (((lowKer fc κ (-w - u) * ψ (Function.update x j u) : ℝ)) : ℂ) from by
      refine MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.acube_measurable ℓ)
        (fun u _ => ?_)
      rw [Complex.ofReal_mul]]
    rw [show (∫ u in Submission.BoseGases.acube ℓ,
          ((lowKer fc κ (-w - u) * ψ (Function.update x j u) : ℝ) : ℂ))
        = ((∫ u in Submission.BoseGases.acube ℓ,
            lowKer fc κ (-w - u) * ψ (Function.update x j u) : ℝ) : ℂ) from
      integral_ofReal]
    congr 1
    rw [show (∫ u in Submission.BoseGases.acube ℓ,
          lowKer fc κ (-w - u) * ψ (Function.update x j u))
        = ∫ u : E3, (Submission.BoseGases.acube ℓ).indicator
            (fun u => lowKer fc κ (-w - u) * ψ (Function.update x j u)) u from
      (MeasureTheory.integral_indicator (μ := (volume : Measure E3))
        (Submission.BoseGases.acube_measurable ℓ)).symm]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
    by_cases hu : u ∈ Submission.BoseGases.acube ℓ
    · simp only [Set.indicator_of_mem hu]
    · simp only [Set.indicator_of_notMem hu, mul_zero]
  -- ## §3b: the pointwise split of the image sum
  have hsplit : ∀ x w, Lw x w = Pfun x w + Lt x w := by
    intro x w
    have h1 := imageSum_shift_split (fc := fc) (κ := κ) (ℓ := ℓ) hκpos hℓpos (n := n) j ψ
      hψm hψb x (-w)
    have h2 : Lw x w = L1 x w + Lt x w := by
      rw [hLwdef, hL1def, hLtdef]
      simpa only [sub_neg_eq_add] using h1
    rw [h2, hP1eq x w]
  -- ## §4a: integrability in `w`
  have hIntL1 : ∀ x : Submission.BoseGases.X n, Integrable (fun w : E3 => Qw x w * L1 x w) := by
    intro x
    have hm : Measurable (fun w : E3 => Qw x w * L1 x w) := by
      have hc : (fun w : E3 => Qw x w * L1 x w)
          = fun w : E3 =>
              (fun p : Submission.BoseGases.X n × E3 => Qw p.1 p.2 * L1 p.1 p.2) (x, w) := rfl
      rw [hc]
      exact (hQwm.mul hL1m).comp (measurable_const.prodMk measurable_id)
    refine integrable_of_bounded_support_cd (s := Work.BoseB4.BoxData.boxL
      Work.BoseK15.corpusBox ℓ) hboxLfin hm ?_ ?_
    · exact ⟨(Cχ * Kw) * (Cnlk * (2 * Cθ) * ℓ ^ 3), fun w => by
        rw [norm_mul]
        exact mul_le_mul (hQwb x w) (hL1b x w) (norm_nonneg _) (mul_nonneg hCχ0 hKw0)⟩
    · intro w hw
      rw [Function.mem_support] at hw
      have hQ : Qw x w ≠ 0 := fun h0 => hw (by rw [h0, zero_mul])
      have hχ : Work.BoseK15.corpusBox.chiLam ℓ w ≠ 0 := by
        intro h0
        apply hQ
        rw [hQwval]
        rw [show ((Work.BoseK15.corpusBox.chiLam ℓ w : ℝ) : ℂ) = 0 from by rw [h0]; simp]
        simp
      exact Work.BoseB4.BoxData.chiLam_supp (B := Work.BoseK15.corpusBox) hℓpos
        (Function.mem_support.mpr hχ)
  have hIntLt : ∀ x : Submission.BoseGases.X n, Integrable (fun w : E3 => Qw x w * Lt x w) := by
    intro x
    have hm : Measurable (fun w : E3 => Qw x w * Lt x w) := by
      have hc : (fun w : E3 => Qw x w * Lt x w)
          = fun w : E3 =>
              (fun p : Submission.BoseGases.X n × E3 => Qw p.1 p.2 * Lt p.1 p.2) (x, w) := rfl
      rw [hc]
      exact (hQwm.mul hLtm).comp (measurable_const.prodMk measurable_id)
    refine integrable_of_bounded_support_cd (s := Work.BoseB4.BoxData.boxL
      Work.BoseK15.corpusBox ℓ) hboxLfin hm ?_ ?_
    · exact ⟨(Cχ * Kw) * (((Ks + 1) / ℓ ^ 3 + Cnlk) * (2 * Cθ) * ℓ ^ 3), fun w => by
        rw [norm_mul]
        exact mul_le_mul (hQwb x w) (hLtb x w) (norm_nonneg _) (mul_nonneg hCχ0 hKw0)⟩
    · intro w hw
      rw [Function.mem_support] at hw
      have hQ : Qw x w ≠ 0 := fun h0 => hw (by rw [h0, zero_mul])
      have hχ : Work.BoseK15.corpusBox.chiLam ℓ w ≠ 0 := by
        intro h0
        apply hQ
        rw [hQwval]
        rw [show ((Work.BoseK15.corpusBox.chiLam ℓ w : ℝ) : ℂ) = 0 from by rw [h0]; simp]
        simp
      exact Work.BoseB4.BoxData.chiLam_supp (B := Work.BoseK15.corpusBox) hℓpos
        (Function.mem_support.mpr hχ)
  have hIntP : ∀ x : Submission.BoseGases.X n, Integrable (fun w : E3 => Qw x w * Pfun x w) :=
    fun x => (hIntL1 x).congr (Filter.Eventually.of_forall (fun w => by
      show Qw x w * L1 x w = Qw x w * Pfun x w
      rw [hP1eq x w]))
  -- ## §4b: the pointwise split of the `w`-integral
  have hJ1 : ∀ x : Submission.BoseGases.X n, Jfull x = A1 x + A2 x := by
    intro x
    rw [hJval, hA1val, hA2val]
    rw [show (∫ w : E3, Qw x w * Lw x w)
        = ∫ w : E3, (Qw x w * Pfun x w + Qw x w * Lt x w) from by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun w => ?_))
      show Qw x w * Lw x w = Qw x w * Pfun x w + Qw x w * Lt x w
      rw [hsplit x w]
      ring]
    exact MeasureTheory.integral_add (hIntP x) (hIntLt x)
  -- ## §4c: bounds and integrability in `x`
  have hA1b : ∀ x : Submission.BoseGases.X n,
      ‖A1 x‖ ≤ (Cχ * Kw) * (Cnlk * (2 * Cθ) * ℓ ^ 3) * ℓ ^ 3 := by
    intro x
    rw [hA1val]
    rw [show (∫ w : E3, Qw x w * Pfun x w) = ∫ w : E3, Qw x w * L1 x w from
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun w => by
        show Qw x w * Pfun x w = Qw x w * L1 x w
        rw [hP1eq x w]))]
    have hvanish : ∀ w : E3, w ∉ Work.BoseB4.BoxData.boxL Work.BoseK15.corpusBox ℓ →
        Qw x w * L1 x w = 0 := by
      intro w hw
      have hχ : Work.BoseK15.corpusBox.chiLam ℓ w = 0 := by
        by_contra hne
        exact hw (Work.BoseB4.BoxData.chiLam_supp (B := Work.BoseK15.corpusBox) hℓpos
          (Function.mem_support.mpr hne))
      rw [hQwval]
      rw [show ((Work.BoseK15.corpusBox.chiLam ℓ w : ℝ) : ℂ) = 0 from by rw [hχ]; simp]
      simp
    rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      (s := Work.BoseB4.BoxData.boxL Work.BoseK15.corpusBox ℓ)
      (f := fun w : E3 => Qw x w * L1 x w) hvanish]
    haveI : IsFiniteMeasure ((volume : Measure E3).restrict
        (Work.BoseB4.BoxData.boxL Work.BoseK15.corpusBox ℓ)) :=
      MeasureTheory.isFiniteMeasure_restrict.mpr (ne_of_lt hboxLfin)
    have hbd : ∀ᵐ w ∂((volume : Measure E3).restrict
          (Work.BoseB4.BoxData.boxL Work.BoseK15.corpusBox ℓ)),
        ‖Qw x w * L1 x w‖ ≤ (Cχ * Kw) * (Cnlk * (2 * Cθ) * ℓ ^ 3) := by
      filter_upwards with w
      rw [norm_mul]
      exact mul_le_mul (hQwb x w) (hL1b x w) (norm_nonneg _) (mul_nonneg hCχ0 hKw0)
    have hfin := MeasureTheory.norm_integral_le_of_norm_le_const
      (μ := (volume : Measure E3).restrict (Work.BoseB4.BoxData.boxL Work.BoseK15.corpusBox ℓ))
      hbd
    rw [MeasureTheory.Measure.real_def, MeasureTheory.Measure.restrict_apply_univ,
      Work.BoseB4.BoxData.volume_boxL_toReal (B := Work.BoseK15.corpusBox) hℓpos] at hfin
    exact hfin
  have hA2b : ∀ x : Submission.BoseGases.X n,
      ‖A2 x‖ ≤ (Cχ * Kw) * (((Ks + 1) / ℓ ^ 3 + Cnlk) * (2 * Cθ) * ℓ ^ 3) * ℓ ^ 3 := by
    intro x
    rw [hA2val]
    have hvanish : ∀ w : E3, w ∉ Work.BoseB4.BoxData.boxL Work.BoseK15.corpusBox ℓ →
        Qw x w * Lt x w = 0 := by
      intro w hw
      have hχ : Work.BoseK15.corpusBox.chiLam ℓ w = 0 := by
        by_contra hne
        exact hw (Work.BoseB4.BoxData.chiLam_supp (B := Work.BoseK15.corpusBox) hℓpos
          (Function.mem_support.mpr hne))
      rw [hQwval]
      rw [show ((Work.BoseK15.corpusBox.chiLam ℓ w : ℝ) : ℂ) = 0 from by rw [hχ]; simp]
      simp
    rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      (s := Work.BoseB4.BoxData.boxL Work.BoseK15.corpusBox ℓ)
      (f := fun w : E3 => Qw x w * Lt x w) hvanish]
    haveI : IsFiniteMeasure ((volume : Measure E3).restrict
        (Work.BoseB4.BoxData.boxL Work.BoseK15.corpusBox ℓ)) :=
      MeasureTheory.isFiniteMeasure_restrict.mpr (ne_of_lt hboxLfin)
    have hbd : ∀ᵐ w ∂((volume : Measure E3).restrict
          (Work.BoseB4.BoxData.boxL Work.BoseK15.corpusBox ℓ)),
        ‖Qw x w * Lt x w‖ ≤ (Cχ * Kw) * (((Ks + 1) / ℓ ^ 3 + Cnlk) * (2 * Cθ) * ℓ ^ 3) := by
      filter_upwards with w
      rw [norm_mul]
      exact mul_le_mul (hQwb x w) (hLtb x w) (norm_nonneg _) (mul_nonneg hCχ0 hKw0)
    have hfin := MeasureTheory.norm_integral_le_of_norm_le_const
      (μ := (volume : Measure E3).restrict (Work.BoseB4.BoxData.boxL Work.BoseK15.corpusBox ℓ))
      hbd
    rw [MeasureTheory.Measure.real_def, MeasureTheory.Measure.restrict_apply_univ,
      Work.BoseB4.BoxData.volume_boxL_toReal (B := Work.BoseK15.corpusBox) hℓpos] at hfin
    exact hfin
  have hIntA1 : Integrable (fun x : Submission.BoseGases.X n => G x * A1 x) := by
    have hjoint : Measurable (fun p : Submission.BoseGases.X n × E3 =>
        G p.1 * (Qw p.1 p.2 * L1 p.1 p.2)) :=
      (hGm.comp measurable_fst).mul (hQwm.mul hL1m)
    have hSm : StronglyMeasurable (fun x : Submission.BoseGases.X n =>
        ∫ w : E3, G x * (Qw x w * L1 x w)) :=
      hjoint.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure E3))
    have hfs : (fun x : Submission.BoseGases.X n => ∫ w : E3, G x * (Qw x w * L1 x w))
        = fun x : Submission.BoseGases.X n => G x * A1 x := by
      funext x
      rw [hA1val, MeasureTheory.integral_const_mul]
      congr 1
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun w => ?_))
      show Qw x w * L1 x w = Qw x w * Pfun x w
      rw [hP1eq x w]
    rw [hfs] at hSm
    refine integrable_of_bounded_support_cd (s := Submission.BoseGases.abox n ℓ)
      (Submission.BoseGases.abox_lt_top n ℓ hℓpos.le) hSm.measurable ?_ ?_
    · exact ⟨(Cθ * Cχ) * ((Cχ * Kw) * (Cnlk * (2 * Cθ) * ℓ ^ 3) * ℓ ^ 3), fun x => by
        rw [norm_mul]
        exact mul_le_mul (hGb x) (hA1b x) (norm_nonneg _) (mul_nonneg hCθ0 hCχ0)⟩
    · intro x hx
      rw [Function.mem_support] at hx
      exact hGs (Function.mem_support.mpr (fun h0 => hx (by rw [h0, zero_mul])))
  have hIntA2 : Integrable (fun x : Submission.BoseGases.X n => G x * A2 x) := by
    have hjoint : Measurable (fun p : Submission.BoseGases.X n × E3 =>
        G p.1 * (Qw p.1 p.2 * Lt p.1 p.2)) :=
      (hGm.comp measurable_fst).mul (hQwm.mul hLtm)
    have hSm : StronglyMeasurable (fun x : Submission.BoseGases.X n =>
        ∫ w : E3, G x * (Qw x w * Lt x w)) :=
      hjoint.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure E3))
    have hfs : (fun x : Submission.BoseGases.X n => ∫ w : E3, G x * (Qw x w * Lt x w))
        = fun x : Submission.BoseGases.X n => G x * A2 x := by
      funext x
      rw [hA2val, MeasureTheory.integral_const_mul]
    rw [hfs] at hSm
    refine integrable_of_bounded_support_cd (s := Submission.BoseGases.abox n ℓ)
      (Submission.BoseGases.abox_lt_top n ℓ hℓpos.le) hSm.measurable ?_ ?_
    · exact ⟨(Cθ * Cχ) * ((Cχ * Kw) * (((Ks + 1) / ℓ ^ 3 + Cnlk) * (2 * Cθ) * ℓ ^ 3)
          * ℓ ^ 3), fun x => by
        rw [norm_mul]
        exact mul_le_mul (hGb x) (hA2b x) (norm_nonneg _) (mul_nonneg hCθ0 hCχ0)⟩
    · intro x hx
      rw [Function.mem_support] at hx
      exact hGs (Function.mem_support.mpr (fun h0 => hx (by rw [h0, zero_mul])))
  -- ## §4d: the split of the `x`-integral
  have hkey : (∫ x : Submission.BoseGases.X n, G x * Jfull x)
      = (∫ x : Submission.BoseGases.X n, G x * A1 x)
        + ∫ x : Submission.BoseGases.X n, G x * A2 x := by
    rw [show (∫ x : Submission.BoseGases.X n, G x * Jfull x)
        = ∫ x : Submission.BoseGases.X n, (G x * A1 x + G x * A2 x) from by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
      show G x * Jfull x = G x * A1 x + G x * A2 x
      rw [hJ1 x]
      ring]
    exact MeasureTheory.integral_add hIntA1 hIntA2
  -- ## §5: assembly
  have hA := Cchan_eq_imageSum hij v h fc fu μ N hℓ hκ hN Θ hΘ hΘm ⟨Cθ, hCθ⟩ hΘs
  calc (∫ q : Submission.BoseGases.X n
          × (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)),
        ((Θ q.1 : ℝ) : ℂ)
          * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) (q.1 i)
          * Work.BoseBoxFock.PCFU.ChCU v h fc fu μ N q.2.1 (q.1 j) q.2.2
          * ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ))
      = (ℓ : ℂ) ^ 3 * (∫ x : Submission.BoseGases.X n, G x * Jfull x) := by
        simpa only [hℓdef, hκdef, hGdef, hJdef, hQwdef, hLwdef, hψdef] using hA
    _ = (ℓ : ℂ) ^ 3 * ((∫ x : Submission.BoseGases.X n, G x * A1 x)
          + ∫ x : Submission.BoseGases.X n, G x * A2 x) := by rw [hkey]
    _ = (ℓ : ℂ) ^ 3 * (∫ x : Submission.BoseGases.X n, G x * A1 x)
          + (ℓ : ℂ) ^ 3 * (∫ x : Submission.BoseGases.X n, G x * A2 x) := by ring
    _ = ((Work.BoseBoxFock.ellH v μ : ℂ)) ^ 3
          * (∫ x : Submission.BoseGases.X n,
              ((Θ x : ℝ) : ℂ)
                * ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) (x i) : ℝ) : ℂ)
                * (∫ w : EuclideanSpace ℝ (Fin 3),
                    ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) w : ℝ) : ℂ)
                      * Work.BoseBoxFock.PCFU.KfrU v h μ fu N (x i + w)
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
                * ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) (x i) : ℝ) : ℂ)
                * (∫ w : EuclideanSpace ℝ (Fin 3),
                    ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) w : ℝ) : ℂ)
                      * Work.BoseBoxFock.PCFU.KfrU v h μ fu N (x i + w)
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
        simp only [hGdef, hA1def, hQwdef, hPdef, hA2def, hLtdef, hψdef, hℓdef, hκdef]

end Work.BoseBoxFock.PCFU
