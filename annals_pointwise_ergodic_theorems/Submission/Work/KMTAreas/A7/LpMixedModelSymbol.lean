/-
# The mixed-range §6 model operator in symbol form (window-parametrised)

On the guard, the model tuple of the *repaired* window `loMixedU ρ P.natDegree l₂ k₁ k₂` is the
bilinear convolution with the coefficient kernel of the model symbol `symMWin`; this is the
window-parametrised analogue of `Work.KMTPlan.A6.lowModel_eq_bilinOp_symM` (whose proof it
mirrors; the helpers `bilinOp_intervalIntegral_swap_aux`, `measurable_kernComp_family`,
`hdom_kernComp` are copied verbatim, being independent of the window).
-/
import Mathlib
import Submission.Work.KMTAreas.A7.LoMixedWinDefs

set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace Work.KMTPlan.A6

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger
open Work.KMTAreas.A7
open Work.KMTContract

lemma lpMeasurableSymSeqPair {κ : ℝ → ℤ → ℂ}
    (hκ : ∀ j : ℤ, Measurable fun t : ℝ => κ t j) :
    Measurable (fun q : ℝ × ℝ => symSeq (κ q.2) q.1) := by
  rw [show (fun q : ℝ × ℝ => symSeq (κ q.2) q.1) = fun q : ℝ × ℝ =>
      ∑' j : ℤ, κ q.2 j * eeC ((j : ℝ) * q.1) from by
    funext q; rw [symSeq]]
  refine Measurable.tsum (L := SummationFilter.unconditional ℤ) (fun j => ?_)
  have h1 : Measurable (fun q : ℝ × ℝ => κ q.2 j) := (hκ j).comp measurable_snd
  have h2 : Measurable (fun q : ℝ × ℝ => eeC ((j : ℝ) * q.1)) := by
    have hc : Continuous (fun q : ℝ × ℝ => eeC ((j : ℝ) * q.1)) := by unfold eeC; fun_prop
    exact hc.measurable
  exact h1.mul h2

/-- The joint measurability of the three-factor symbol `(t,x,y) ↦ symSeq2 K x y · symSeq (κ₁ t) x ·
symSeq (κ₂ t) y`. -/

lemma lpMeasurableSymProduct {Kar : ℤ → ℤ → ℂ} {κ₁ κ₂ : ℝ → ℤ → ℂ}
    (hKar : Measurable (fun q : ℝ × ℝ => symSeq2 Kar q.1 q.2))
    (h₁ : Measurable (fun q : ℝ × ℝ => symSeq (κ₁ q.2) q.1))
    (h₂ : Measurable (fun q : ℝ × ℝ => symSeq (κ₂ q.2) q.1)) :
    Measurable (fun q : ℝ × ℝ × ℝ =>
      symSeq2 Kar q.2.1 q.2.2 * symSeq (κ₁ q.1) q.2.1 * symSeq (κ₂ q.1) q.2.2) := by
  have hA : Measurable (fun q : ℝ × ℝ × ℝ => symSeq2 Kar q.2.1 q.2.2) :=
    hKar.comp ((measurable_fst.comp measurable_snd).prodMk
      (measurable_snd.comp measurable_snd))
  have hB : Measurable (fun q : ℝ × ℝ × ℝ => symSeq (κ₁ q.1) q.2.1) :=
    h₁.comp ((measurable_fst.comp measurable_snd).prodMk measurable_fst)
  have hC : Measurable (fun q : ℝ × ℝ × ℝ => symSeq (κ₂ q.1) q.2.2) :=
    h₂.comp ((measurable_snd.comp measurable_snd).prodMk measurable_fst)
  exact (hA.mul hB).mul hC

/-- The three-factor norm bound. -/

lemma lpBilinOpSwap {K : Real → Int → Int → Complex}
    {u v : Int → Complex} {Cu Cv : Real}
    (hKs : ∀ t ∈ Set.Icc (1/2 : Real) 1, Summable fun p : Int × Int => ‖K t p.1 p.2‖)
    (hmeas : ∀ p : Int × Int, MeasureTheory.AEStronglyMeasurable (fun t : Real => K t p.1 p.2)
      ((MeasureTheory.volume : MeasureTheory.Measure Real).restrict (Set.Ioc (1/2 : Real) 1)))
    (hdom : (∑' p : Int × Int, ∫⁻ t, ‖K t p.1 p.2‖ₑ
      ∂((MeasureTheory.volume : MeasureTheory.Measure Real).restrict (Set.Ioc (1/2 : Real) 1))) ≠ ⊤)
    (hu : ∀ y : Int, ‖u y‖ ≤ Cu) (hv : ∀ y : Int, ‖v y‖ ≤ Cv) (x : Int) :
    ∫ t in (1/2 : Real)..1, Work.KMTAreas.A7.bilinOp (K t) u v x
      = Work.KMTAreas.A7.bilinOp (fun a b => ∫ t in (1/2 : Real)..1, K t a b) u v x := by
  set mt : Measure Real := volume.restrict (Set.Ioc (1/2 : Real) 1) with hmt
  have hae : ∀ᵐ t ∂mt, t ∈ Set.Icc (1/2 : Real) 1 := by
    rw [hmt]
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
    exact ⟨le_of_lt ht.1, ht.2⟩
  have hpt : ∀ᵐ t ∂mt, Work.KMTAreas.A7.bilinOp (K t) u v x
      = ∑' p : Int × Int, K t p.1 p.2 * u (x - p.1) * v (x - p.2) := by
    filter_upwards [hae] with t ht
    exact Work.A7.ModelApproxCore_aux.bilinOp_eq_tsum (hKs t ht) hu hv x
  set cu : ℝ≥0∞ := ENNReal.ofReal (max Cu 0) with hcu
  set cv : ℝ≥0∞ := ENNReal.ofReal (max Cv 0) with hcv
  have hcu_top : cu ≠ ⊤ := by rw [hcu]; exact ENNReal.ofReal_ne_top
  have hcv_top : cv ≠ ⊤ := by rw [hcv]; exact ENNReal.ofReal_ne_top
  have hcoe : ∀ z : Complex, (‖z‖ₑ).toReal = ‖z‖ := fun z => by
    rw [show ‖z‖ₑ = ENNReal.ofReal ‖z‖ from by simp [enorm_eq_nnnorm]]; simp
  have hsec : ∀ p : Int × Int, (∫⁻ t, ‖K t p.1 p.2‖ₑ ∂mt) ≠ ⊤ :=
    fun p => ne_top_of_le_ne_top hdom (ENNReal.le_tsum (f := fun p : Int × Int => ∫⁻ t, ‖K t p.1 p.2‖ₑ ∂mt) p)
  have hterm : ∀ p : Int × Int, ∫⁻ t, ‖K t p.1 p.2 * u (x - p.1) * v (x - p.2)‖ₑ ∂mt
      ≤ (∫⁻ t, ‖K t p.1 p.2‖ₑ ∂mt) * cu * cv := by
    intro p
    calc ∫⁻ t, ‖K t p.1 p.2 * u (x - p.1) * v (x - p.2)‖ₑ ∂mt
        ≤ ∫⁻ t, (‖K t p.1 p.2‖ₑ * cu * cv) ∂mt := by
          refine lintegral_mono (fun t => ?_)
          have h1 : ‖u (x - p.1)‖ₑ ≤ cu := by
            rw [hcu]
            calc ‖u (x - p.1)‖ₑ = ENNReal.ofReal ‖u (x - p.1)‖ := by simp [enorm_eq_nnnorm]
              _ ≤ ENNReal.ofReal (max Cu 0) :=
                  ENNReal.ofReal_le_ofReal (le_trans (hu _) (le_max_left Cu 0))
          have h2 : ‖v (x - p.2)‖ₑ ≤ cv := by
            rw [hcv]
            calc ‖v (x - p.2)‖ₑ = ENNReal.ofReal ‖v (x - p.2)‖ := by simp [enorm_eq_nnnorm]
              _ ≤ ENNReal.ofReal (max Cv 0) :=
                  ENNReal.ofReal_le_ofReal (le_trans (hv _) (le_max_left Cv 0))
          rw [enorm_mul, enorm_mul]
          gcongr
      _ = (∫⁻ t, ‖K t p.1 p.2‖ₑ ∂mt) * cu * cv := by
            rw [lintegral_mul_const' cv _ hcv_top, lintegral_mul_const' cu _ hcu_top]
  have hdom2 : (∑' p : Int × Int, ∫⁻ t, ‖K t p.1 p.2 * u (x - p.1) * v (x - p.2)‖ₑ ∂mt) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hterm)
    rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_right]
    exact ne_of_lt (ENNReal.mul_lt_top (ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hdom)
      (lt_top_iff_ne_top.mpr hcu_top)) (lt_top_iff_ne_top.mpr hcv_top))
  have hsum_int : Summable (fun p : Int × Int => ‖∫ t, K t p.1 p.2 ∂mt‖) :=
    Summable.of_nonneg_of_le (fun p => norm_nonneg _)
      (fun p => by
        have h1 : ‖∫ t, K t p.1 p.2 ∂mt‖ₑ ≤ ∫⁻ t, ‖K t p.1 p.2‖ₑ ∂mt :=
          MeasureTheory.enorm_integral_le_lintegral_enorm _
        calc ‖∫ t, K t p.1 p.2 ∂mt‖ = (‖∫ t, K t p.1 p.2 ∂mt‖ₑ).toReal := (hcoe _).symm
          _ ≤ (∫⁻ t, ‖K t p.1 p.2‖ₑ ∂mt).toReal := ENNReal.toReal_mono (hsec p) h1)
      (ENNReal.summable_toReal hdom)
  simp only [intervalIntegral.integral_of_le (by norm_num : (1/2:Real) ≤ 1)]
  rw [← hmt]
  rw [integral_congr_ae hpt]
  rw [MeasureTheory.integral_tsum (fun p : Int × Int =>
    ((hmeas p).mul_const (u (x - p.1))).mul_const (v (x - p.2))) hdom2]
  rw [Work.A7.ModelApproxCore_aux.bilinOp_eq_tsum (K := fun a b : Int => ∫ t, K t a b ∂mt)
    hsum_int hu hv x]
  exact tsum_congr (fun p => by
    rw [MeasureTheory.integral_mul_const, MeasureTheory.integral_mul_const])

/-! ## §4.  Auxiliary facts about the two symbols -/


lemma lpMeasurableKernCompFamily {Kar : ℤ → ℤ → ℂ} {κ₁ κ₂ : ℝ → ℤ → ℂ}
    (hm₁ : ∀ j : ℤ, Measurable fun t : ℝ => κ₁ t j)
    (hm₂ : ∀ j : ℤ, Measurable fun t : ℝ => κ₂ t j) :
    ∀ p : ℤ × ℤ, Measurable (fun t : ℝ => kernComp Kar (κ₁ t) (κ₂ t) p.1 p.2) := by
  intro p
  show Measurable (fun t : ℝ => ∑' a' : ℤ, ∑' b' : ℤ,
    Kar (p.1 - a') (p.2 - b') * κ₁ t a' * κ₂ t b')
  refine Measurable.tsum (L := SummationFilter.unconditional ℤ) (fun a' => ?_)
  refine Measurable.tsum (L := SummationFilter.unconditional ℤ) (fun b' => ?_)
  exact (measurable_const.mul (hm₁ a')).mul (hm₂ b')

/-- **The domination bound** for the composed kernels: the `t`-integral of their `ℓ¹` masses is
finite. -/

lemma lpHdomKernComp {Kar : ℤ → ℤ → ℂ} {κ₁ κ₂ : ℝ → ℤ → ℂ} {B₁ B₂ : ℝ}
    (hKar : Summable fun p : ℤ × ℤ => ‖Kar p.1 p.2‖)
    (hκ₁ : ∀ t ∈ Set.Icc (1/2 : ℝ) 1, Summable fun j : ℤ => ‖κ₁ t j‖)
    (hκ₂ : ∀ t ∈ Set.Icc (1/2 : ℝ) 1, Summable fun j : ℤ => ‖κ₂ t j‖)
    (hb₁ : ∀ t ∈ Set.Icc (1/2 : ℝ) 1, (∑' j : ℤ, ‖κ₁ t j‖) ≤ B₁)
    (hb₂ : ∀ t ∈ Set.Icc (1/2 : ℝ) 1, (∑' j : ℤ, ‖κ₂ t j‖) ≤ B₂)
    (hB₁0 : 0 ≤ B₁)
    (hm₁ : ∀ j : ℤ, Measurable fun t : ℝ => κ₁ t j)
    (hm₂ : ∀ j : ℤ, Measurable fun t : ℝ => κ₂ t j) :
    (∑' p : ℤ × ℤ, ∫⁻ t, ‖kernComp Kar (κ₁ t) (κ₂ t) p.1 p.2‖ₑ
      ∂((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.Ioc (1/2 : ℝ) 1))) ≠ ⊤ := by
  set mt : Measure ℝ := volume.restrict (Set.Ioc (1/2 : ℝ) 1) with hmt
  have hae : ∀ᵐ t ∂mt, t ∈ Set.Icc (1/2 : ℝ) 1 := by
    rw [hmt]
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
    exact ⟨le_of_lt ht.1, ht.2⟩
  have hunivt : mt Set.univ = ENNReal.ofReal (1/2) := by
    rw [hmt, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Ioc]
    congr 1
    norm_num
  have hKtMeas : ∀ p : ℤ × ℤ, Measurable (fun t : ℝ => kernComp Kar (κ₁ t) (κ₂ t) p.1 p.2) :=
    lpMeasurableKernCompFamily hm₁ hm₂
  have hKtsum : ∀ t ∈ Set.Icc (1/2 : ℝ) 1,
      Summable (fun p : ℤ × ℤ => ‖kernComp Kar (κ₁ t) (κ₂ t) p.1 p.2‖) :=
    fun t ht => Work.A7.ModelApproxCore_aux.summable_kernComp hKar (hκ₁ t ht) (hκ₂ t ht)
  have hKtbound : ∀ t ∈ Set.Icc (1/2 : ℝ) 1,
      (∑' p : ℤ × ℤ, ‖kernComp Kar (κ₁ t) (κ₂ t) p.1 p.2‖)
        ≤ (∑' p : ℤ × ℤ, ‖Kar p.1 p.2‖) * B₁ * B₂ := by
    intro t ht
    refine le_trans (tsum_norm_kernComp_le hKar (hκ₁ t ht) (hκ₂ t ht)) ?_
    have h0 : (0 : ℝ) ≤ ∑' p : ℤ × ℤ, ‖Kar p.1 p.2‖ := tsum_nonneg (fun _ => norm_nonneg _)
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hb₁ t ht) h0) (hb₂ t ht)
      (tsum_nonneg (fun _ => norm_nonneg _)) (mul_nonneg h0 hB₁0)
  have hpoint : ∀ᵐ t ∂mt, (∑' p : ℤ × ℤ, ‖kernComp Kar (κ₁ t) (κ₂ t) p.1 p.2‖ₑ)
      ≤ ENNReal.ofReal ((∑' p : ℤ × ℤ, ‖Kar p.1 p.2‖) * B₁ * B₂) := by
    filter_upwards [hae] with t ht
    have h1 : (∑' p : ℤ × ℤ, ‖kernComp Kar (κ₁ t) (κ₂ t) p.1 p.2‖ₑ)
        = ∑' p : ℤ × ℤ, ENNReal.ofReal ‖kernComp Kar (κ₁ t) (κ₂ t) p.1 p.2‖ :=
      tsum_congr (fun p => by simp [enorm_eq_nnnorm])
    rw [h1, ← ENNReal.ofReal_tsum_of_nonneg (fun p => norm_nonneg _) (hKtsum t ht)]
    exact ENNReal.ofReal_le_ofReal (hKtbound t ht)
  rw [← MeasureTheory.lintegral_tsum (fun p => ((hKtMeas p).enorm).aemeasurable)]
  exact ne_of_lt (by
    calc ∫⁻ t, (∑' p : ℤ × ℤ, ‖kernComp Kar (κ₁ t) (κ₂ t) p.1 p.2‖ₑ) ∂mt
        ≤ ∫⁻ t, ENNReal.ofReal ((∑' p : ℤ × ℤ, ‖Kar p.1 p.2‖) * B₁ * B₂) ∂mt :=
          lintegral_mono_ae hpoint
      _ = ENNReal.ofReal ((∑' p : ℤ × ℤ, ‖Kar p.1 p.2‖) * B₁ * B₂) * mt Set.univ :=
          lintegral_const _
      _ = ENNReal.ofReal ((∑' p : ℤ × ℤ, ‖Kar p.1 p.2‖) * B₁ * B₂) * ENNReal.ofReal (1/2) := by
          rw [hunivt]
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)



/-- **The pointwise identity**: the model integrand is a bilinear convolution with the composed
kernel, at the window parameter `u`. -/
lemma lpMixedBtwist_eq_bilinOp_kernComp (ρ : ℝ) (P : ℤ[X]) (u N l₂ k₁ k₂ : ℕ)
    {Kar : ℤ → ℤ → ℂ} {κ₁ κ₂ : ℝ → ℤ → ℂ} {f g : ℤ → ℂ} {Cf Cg : ℝ} (t : ℝ) (x : ℤ)
    (hKar : Kar = Work.KMTAreas.A7.arithKerMWin ρ P u 0 l₂)
    (hκ₁ : κ₁ t = tmKer ρ 0 (varphiNt N k₁ t))
    (hκ₂ : κ₂ t = tmKer ρ l₂ (varphitildeNt P P.natDegree N k₂ t))
    (hKsum : Summable fun p : ℤ × ℤ => ‖Kar p.1 p.2‖)
    (hκ₁s : Summable fun j : ℤ => ‖κ₁ t j‖) (hκ₂s : Summable fun j : ℤ => ‖κ₂ t j‖)
    (hf : ∀ y : ℤ, ‖f y‖ ≤ Cf) (hg : ∀ y : ℤ, ‖g y‖ ≤ Cg) :
    Work.KMTAreas.A7.bilinOp (Work.KMTAreas.A7.arithKerMWin ρ P u 0 l₂)
        (Work.KMTAreas.A7.Tm ρ 0 (varphiNt N k₁ t) f)
        (Work.KMTAreas.A7.Tm ρ l₂ (varphitildeNt P P.natDegree N k₂ t) g) x
      = Work.KMTAreas.A7.bilinOp (kernComp Kar (κ₁ t) (κ₂ t)) f g x := by
  rw [← hKar, Tm_eq_convOp, Tm_eq_convOp, ← hκ₁, ← hκ₂]
  exact (Work.A7.ModelApproxCore_kernelComp (K := Kar) (κ := κ₁ t) (κ' := κ₂ t)
    (u := f) (v := g) (Cu := Cf) (Cv := Cg) hKsum hκ₁s hκ₂s hf hg x).symm

/-- **The model tuple as the `t`-integral of a bilinear convolution.** -/
lemma lpMixedTuple_eq_integral_kernComp (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ)
    (a : ℕ → NNReal) (f g : ℤ → ℂ) (l₂ k₁ k₂ n : ℕ) (x : ℤ)
    {Kar : ℤ → ℤ → ℂ} {κ₁ κ₂ : ℝ → ℤ → ℂ} {Cf Cg : ℝ}
    (h : Work.KMTAreas.A7.loGuard ρ C₀ a 0 l₂ k₁ k₂ n)
    (hKar : Kar = Work.KMTAreas.A7.arithKerMWin ρ P
      (Work.KMTAreas.A7.loMixedU ρ P.natDegree l₂ k₁ k₂) 0 l₂)
    (hκ₁ : ∀ t : ℝ, κ₁ t = tmKer ρ 0 (varphiNt (Nat.floor (a n)) k₁ t))
    (hκ₂ : ∀ t : ℝ, κ₂ t = tmKer ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t))
    (hKsum : Summable fun p : ℤ × ℤ => ‖Kar p.1 p.2‖)
    (hκ₁s : ∀ t ∈ Set.Icc (1/2 : ℝ) 1, Summable fun j : ℤ => ‖κ₁ t j‖)
    (hκ₂s : ∀ t ∈ Set.Icc (1/2 : ℝ) 1, Summable fun j : ℤ => ‖κ₂ t j‖)
    (hf : ∀ y : ℤ, ‖f y‖ ≤ Cf) (hg : ∀ y : ℤ, ‖g y‖ ≤ Cg) :
    Work.KMTAreas.A7.loMixedTuple ρ P C₀ a f g l₂ k₁ k₂ n x
      = ∫ t in (1/2 : ℝ)..1, Work.KMTAreas.A7.bilinOp (kernComp Kar (κ₁ t) (κ₂ t)) f g x := by
  rw [Work.KMTAreas.A7.loMixedTuple_apply, if_pos h,
    Work.KMTAreas.A7.loMixedOp_eq_integral_bilinOp]
  refine intervalIntegral.integral_congr (fun t ht => ?_)
  rw [Set.uIcc_of_le (by norm_num : (1/2 : ℝ) ≤ 1)] at ht
  exact lpMixedBtwist_eq_bilinOp_kernComp ρ P
    (Work.KMTAreas.A7.loMixedU ρ P.natDegree l₂ k₁ k₂) (Nat.floor (a n)) l₂ k₁ k₂ t x
    hKar (hκ₁ t) (hκ₂ t) hKsum (hκ₁s t ht) (hκ₂s t ht) hf hg


/-- **The mixed-range model operator in symbol form.**  On the guard, the model tuple
`loMixedTuple` of the repaired window is the bilinear convolution whose kernel is the coefficient
kernel `coeff2 (symMWin ρ P (loMixedU ρ P.natDegree l₂ k₁ k₂) ⌊a n⌋ 0 l₂ k₁ k₂)` of the model
symbol. -/
theorem loMixedOpEqBilinOp (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (P : ℤ[X]) (C₀ : ℕ)
    (a : ℕ → NNReal) (f g : ℤ → ℂ) (l₂ k₁ k₂ n : ℕ) (x : ℤ)
    (hf : Work.KMTAreas.A5.BoundedZ f) (hg : Work.KMTAreas.A5.BoundedZ g)
    (h : Work.KMTAreas.A7.loGuard ρ C₀ a 0 l₂ k₁ k₂ n) :
    Work.KMTAreas.A7.loMixedTuple ρ P C₀ a f g l₂ k₁ k₂ n x
      = Work.KMTAreas.A7.bilinOp
          (fun u v => coeff2
            (Work.KMTAreas.A7.symMWin ρ P (Work.KMTAreas.A7.loMixedU ρ P.natDegree l₂ k₁ k₂)
              (Nat.floor (a n)) 0 l₂ k₁ k₂) u v) f g x := by
  obtain ⟨Cf, hfC⟩ := hf
  obtain ⟨Cg, hgC⟩ := hg
  set Kar : ℤ → ℤ → ℂ :=
    Work.KMTAreas.A7.arithKerMWin ρ P (Work.KMTAreas.A7.loMixedU ρ P.natDegree l₂ k₁ k₂) 0 l₂
    with hKar
  set κ₁ : ℝ → ℤ → ℂ := fun t => tmKer ρ 0 (varphiNt (Nat.floor (a n)) k₁ t) with hκ₁
  set κ₂ : ℝ → ℤ → ℂ :=
    fun t => tmKer ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) with hκ₂
  obtain ⟨B₁, hB₁0, hB₁⟩ := uniform_tmKer_varphiNt ρ 0 (Nat.floor (a n)) k₁
  obtain ⟨B₂, hB₂0, hB₂⟩ := uniform_tmKer_varphitildeNt ρ P l₂ (Nat.floor (a n)) k₂
  have hKsum : Summable (fun p : ℤ × ℤ => ‖Kar p.1 p.2‖) := by
    rw [hKar]
    exact summable_arithKerMWin ρ P (Work.KMTAreas.A7.loMixedU ρ P.natDegree l₂ k₁ k₂) 0 l₂
  have hκ₁sum : ∀ t ∈ Set.Icc (1/2 : ℝ) 1, Summable (fun j : ℤ => ‖κ₁ t j‖) :=
    fun t ht => (hB₁ t ht).1
  have hκ₂sum : ∀ t ∈ Set.Icc (1/2 : ℝ) 1, Summable (fun j : ℤ => ‖κ₂ t j‖) :=
    fun t ht => (hB₂ t ht).1
  have hm₁ : ∀ j : ℤ, Measurable fun t : ℝ => κ₁ t j := by
    intro j
    rw [hκ₁]
    exact measurable_tmKer_varphiNt ρ 0 (Nat.floor (a n)) k₁ j
  have hm₂ : ∀ j : ℤ, Measurable fun t : ℝ => κ₂ t j := by
    intro j
    rw [hκ₂]
    exact measurable_tmKer_varphitildeNt ρ P l₂ (Nat.floor (a n)) k₂ j
  have hσm : Measurable (fun q : ℝ × ℝ × ℝ =>
      symSeq2 Kar q.2.1 q.2.2 * symSeq (κ₁ q.1) q.2.1 * symSeq (κ₂ q.1) q.2.2) :=
    lpMeasurableSymProduct (measurable_symSeq2 Kar)
      (lpMeasurableSymSeqPair hm₁) (lpMeasurableSymSeqPair hm₂)
  have hσb : ∀ t, t ∈ Set.Icc (1/2 : ℝ) 1 → ∀ x y : ℝ,
      ‖symSeq2 Kar x y * symSeq (κ₁ t) x * symSeq (κ₂ t) y‖
        ≤ (∑' p : ℤ × ℤ, ‖Kar p.1 p.2‖) * B₁ * B₂ := by
    intro t ht x y
    rw [norm_mul, norm_mul]
    refine mul_le_mul (mul_le_mul (norm_symSeq2_le hKsum x y)
      (le_trans (norm_symSeq_le (hκ₁sum t ht) x) (hB₁ t ht).2) (norm_nonneg _)
      (tsum_nonneg (fun _ => norm_nonneg _)))
      (le_trans (norm_symSeq_le (hκ₂sum t ht) y) (hB₂ t ht).2) (norm_nonneg _) ?_
    exact mul_nonneg (tsum_nonneg (fun _ => norm_nonneg _)) hB₁0
  have hsM : Work.KMTAreas.A7.symMWin ρ P (Work.KMTAreas.A7.loMixedU ρ P.natDegree l₂ k₁ k₂)
        (Nat.floor (a n)) 0 l₂ k₁ k₂
      = fun x y : ℝ => ∫ t in (1/2 : ℝ)..1,
          symSeq2 Kar x y * symSeq (κ₁ t) x * symSeq (κ₂ t) y := by
    funext x y
    show (∫ t in (1/2 : ℝ)..1,
        symSeq2 (Work.KMTAreas.A7.arithKerMWin ρ P
          (Work.KMTAreas.A7.loMixedU ρ P.natDegree l₂ k₁ k₂) 0 l₂) x y
        * symSeq (tmKer ρ 0 (varphiNt (Nat.floor (a n)) k₁ t)) x
        * symSeq (tmKer ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t)) y)
      = ∫ t in (1/2 : ℝ)..1, symSeq2 Kar x y * symSeq (κ₁ t) x * symSeq (κ₂ t) y
    rfl
  have hσm' : Measurable (fun q : ℝ × ℝ × ℝ =>
      symSeq2 (Work.KMTAreas.A7.arithKerMWin ρ P
        (Work.KMTAreas.A7.loMixedU ρ P.natDegree l₂ k₁ k₂) 0 l₂) q.2.1 q.2.2
        * symSeq (κ₁ q.1) q.2.1 * symSeq (κ₂ q.1) q.2.2) := by
    rw [← hKar]
    exact hσm
  have hσb' : ∀ t, t ∈ Set.Icc (1/2 : ℝ) 1 → ∀ x y : ℝ,
      ‖symSeq2 (Work.KMTAreas.A7.arithKerMWin ρ P
          (Work.KMTAreas.A7.loMixedU ρ P.natDegree l₂ k₁ k₂) 0 l₂) x y
        * symSeq (κ₁ t) x * symSeq (κ₂ t) y‖
      ≤ (∑' p : ℤ × ℤ, ‖Kar p.1 p.2‖) * B₁ * B₂ := by
    intro t ht x y
    rw [← hKar]
    exact hσb t ht x y
  have hLHS := lpMixedTuple_eq_integral_kernComp ρ P C₀ a f g l₂ k₁ k₂ n x
    (Kar := Kar) (κ₁ := κ₁) (κ₂ := κ₂) h hKar (fun t => congrFun hκ₁ t)
    (fun t => congrFun hκ₂ t) hKsum hκ₁sum hκ₂sum hfC hgC
  have hdom := lpHdomKernComp (Kar := Kar) (κ₁ := κ₁) (κ₂ := κ₂) (B₁ := B₁) (B₂ := B₂)
    hKsum hκ₁sum hκ₂sum (fun t ht => (hB₁ t ht).2) (fun t ht => (hB₂ t ht).2) hB₁0 hm₁ hm₂
  have hcoeff := coeff2_symMWin_eq_integral_kernComp ρ P
    (Work.KMTAreas.A7.loMixedU ρ P.natDegree l₂ k₁ k₂) (Nat.floor (a n)) 0 l₂ k₁ k₂
    (κ₁ := κ₁) (κ₂ := κ₂) (fun t => congrFun hκ₁ t) (fun t => congrFun hκ₂ t)
    hKsum hκ₁sum hκ₂sum hσm' hσb'
  have hcoeff' : coeff2 (Work.KMTAreas.A7.symMWin ρ P
        (Work.KMTAreas.A7.loMixedU ρ P.natDegree l₂ k₁ k₂) (Nat.floor (a n)) 0 l₂ k₁ k₂)
      = fun a b : ℤ => ∫ t in (1/2 : ℝ)..1, kernComp Kar (κ₁ t) (κ₂ t) a b := by
    rw [hsM, hKar]
    exact hcoeff
  have hmid : (∫ t in (1/2 : ℝ)..1, Work.KMTAreas.A7.bilinOp (kernComp Kar (κ₁ t) (κ₂ t)) f g x)
      = Work.KMTAreas.A7.bilinOp
          (fun a b : ℤ => ∫ t in (1/2 : ℝ)..1, kernComp Kar (κ₁ t) (κ₂ t) a b) f g x :=
    lpBilinOpSwap (K := fun t a b => kernComp Kar (κ₁ t) (κ₂ t) a b)
      (fun t ht => Work.A7.ModelApproxCore_aux.summable_kernComp hKsum (hκ₁sum t ht) (hκ₂sum t ht))
      (fun p => (lpMeasurableKernCompFamily hm₁ hm₂ p).aestronglyMeasurable) hdom hfC hgC x
  have hfin : Work.KMTAreas.A7.bilinOp
        (fun a b : ℤ => ∫ t in (1/2 : ℝ)..1, kernComp Kar (κ₁ t) (κ₂ t) a b) f g x
      = Work.KMTAreas.A7.bilinOp
          (fun u v => coeff2
            (Work.KMTAreas.A7.symMWin ρ P (Work.KMTAreas.A7.loMixedU ρ P.natDegree l₂ k₁ k₂)
              (Nat.floor (a n)) 0 l₂ k₁ k₂) u v) f g x :=
    congrArg (fun K : ℤ → ℤ → ℂ => Work.KMTAreas.A7.bilinOp K f g x) hcoeff'.symm
  exact hLHS.trans (hmid.trans hfin)

end Work.KMTPlan.A6
