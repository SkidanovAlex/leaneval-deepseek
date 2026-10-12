import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.BoseFixB1.ae_wSmall1Pair_le_wSmallPair_g2
import Submission.Work.BoseFixB1.aesm_wSmallPair_pair
import Submission.Work.BoseFixB1.regime_sideAt_ge
import Submission.Work.BoseFixB1B.fj_chiSmallB_support
import Submission.Work.BoseFixB1B.fj_kernel_bounds
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory

namespace Work.BoseFixB1B

set_option maxHeartbeats 1600000

/-! ## Auxiliary lemmas about the localised kernels

`wSmallPair M ℓ d u f x y = χ_{B(u)}(x)·(f(x−y)/(χ_M⋆χ_M)((x−y)/(ℓd)))/(χ⋆χ)((x−y)/ℓ)·χ_{B(u)}(y)`
is monotone in the numerator `f`, nonnegative at a pair whose numerator is nonnegative, and
its fibre at fixed first coordinate is a.e. measurable for an a.e. measurable numerator. -/

/-- an a.e. statement transfers along the measure-preserving reflection `y ↦ x - y`. -/
lemma ae_comp_sub_of_ae {p : ℝ³ → Prop} (hp : ∀ᵐ z ∂(volume : Measure ℝ³), p z) (x : ℝ³) :
    ∀ᵐ y ∂(volume : Measure ℝ³), p (x - y) :=
  (MeasureTheory.quasiMeasurePreserving_sub_left_of_right_invariant (volume : Measure ℝ³) x).ae hp

/-- `wSmallPair` is nonnegative at a pair whose numerator value is nonnegative. -/
lemma wSmallPair_nonneg_of_nonneg {M : ℕ} {ℓ d : ℝ} {u x y : ℝ³} {f : ℝ³ → ℝ}
    (hf : 0 ≤ f (x - y)) : 0 ≤ Submission.BoseGases.wSmallPair M ℓ d u f x y := by
  have h1 : 0 ≤ Submission.BoseGases.chiSmallB M ℓ d u x :=
    Submission.BoseGases.chiSmallB_nonneg M ℓ d u x
  have h2 : 0 ≤ Submission.BoseGases.chiSmallB M ℓ d u y :=
    Submission.BoseGases.chiSmallB_nonneg M ℓ d u y
  unfold Submission.BoseGases.wSmallPair Submission.BoseGases.wSmallScaled
  exact mul_nonneg (mul_nonneg h1 (div_nonneg (div_nonneg hf
    (Work.BoseFixB1.convScaleSmall_nonneg M (ℓ * d) (x - y)))
      (Submission.BoseGases.convScale_nonneg ℓ (x - y)))) h2

/-- Fibre measurability of `wSmallPair` at a fixed first coordinate, for an a.e. measurable
numerator. -/
lemma aemeasurable_wSmallPair_fibre {f : ℝ³ → ℝ} (hf : AEMeasurable f (volume : Measure ℝ³))
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (u x : ℝ³) :
    AEMeasurable (fun y : ℝ³ => Submission.BoseGases.wSmallPair M ℓ d u f x y)
      (volume : Measure ℝ³) := by
  have hnum : AEMeasurable (fun y : ℝ³ => f (x - y)) (volume : Measure ℝ³) :=
    hf.comp_quasiMeasurePreserving
      (MeasureTheory.quasiMeasurePreserving_sub_left_of_right_invariant (volume : Measure ℝ³) x)
  have hden1 : Measurable (fun y : ℝ³ => Submission.BoseGases.convScaleSmall M (ℓ * d) (x - y)) :=
    ((Submission.BoseGases.conv3Small_continuous hM).comp
      (by fun_prop : Continuous fun y : ℝ³ => (ℓ * d)⁻¹ • (x - y))).measurable
  have hden2 : Measurable (fun y : ℝ³ => Submission.BoseGases.convScale ℓ (x - y)) :=
    ((Submission.BoseGases.convScale_continuous ℓ).comp
      (by fun_prop : Continuous fun y : ℝ³ => x - y)).measurable
  have hχ : Measurable (fun y : ℝ³ => Submission.BoseGases.chiSmallB M ℓ d u y) :=
    (Work.BoseFixB1.continuous_chiSmallB M ℓ d u).measurable
  have hmain : AEMeasurable (fun y : ℝ³ =>
      Submission.BoseGases.chiSmallB M ℓ d u x *
        ((f (x - y) / Submission.BoseGases.convScaleSmall M (ℓ * d) (x - y)) /
          Submission.BoseGases.convScale ℓ (x - y)) *
        Submission.BoseGases.chiSmallB M ℓ d u y) (volume : Measure ℝ³) :=
    (aemeasurable_const.mul ((hnum.div hden1.aemeasurable).div hden2.aemeasurable)).mul
      hχ.aemeasurable
  simpa only [Submission.BoseGases.wSmallPair, Submission.BoseGases.wSmallScaled] using hmain

/-! ## The general form of the bound

For a fixed pair `(M, ℓ, d)` in the dilute regime (`R ≤ ℓd/16`, `R ≤ ℓ·chiR0`), the square of
the total fibre of the localised one-body kernel is bounded by the box volume times the double
integral of the localised two-body kernel with numerator `v`, with the *explicit* constant
`Λ²(2/smallConvLower M)(8π a v)`, `Λ = chiSupAbs·chiSmallDecay M`. -/

theorem fibre_pair_joint_general {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v} {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R) (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1)
    (hvrad : _root_.BoseGases.IsRadial v) {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR16 : R ≤ ℓ * d / 16) (hRχ : R ≤ ℓ * Submission.BoseGases.chiR0) (u : ℝ³) :
    (∫ x in Submission.BoseGases.dlBox ℓ d u,
        ∫ y in Submission.BoseGases.acube ℓ, Submission.BoseGases.wSmall1Pair h M ℓ d u x y) ^ 2
      ≤ ((Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M) ^ 2
            * (2 / Work.SmallBoxSliding.smallConvLower M) * (8 * Real.pi * _root_.BoseGases.a v))
          * (volume (Submission.BoseGases.dlBox ℓ d u)).toReal
          * (∫ x in Submission.BoseGases.dlBox ℓ d u,
              ∫ y in Submission.BoseGases.dlBox ℓ d u,
                Submission.BoseGases.wSmallPair M ℓ d u v x y) := by
  classical
  set Λ : ℝ := Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M with hΛdef
  set scl : ℝ := Work.SmallBoxSliding.smallConvLower M with hscldef
  set G : ℝ := 8 * Real.pi * _root_.BoseGases.a v with hGdef
  set χ : ℝ³ → ℝ := Submission.BoseGases.chiSmallB M ℓ d u with hχdef
  set B : Set ℝ³ := Submission.BoseGases.dlBox ℓ d u with hBdef
  set ac : Set ℝ³ := Submission.BoseGases.acube ℓ with hacdef
  set A1 : ℝ³ → ℝ := fun z => Submission.BoseGases.wSmallScaled M (ℓ * d)
    (Submission.BoseGases.g0 v h) z / Submission.BoseGases.convScale ℓ z with hA1def
  set Av : ℝ³ → ℝ := fun z => Submission.BoseGases.wSmallScaled M (ℓ * d) v z
    / Submission.BoseGases.convScale ℓ z with hAvdef
  set K : ℝ := Λ ^ 2 * (2 / scl) * G with hKdef
  obtain ⟨havnn, _⟩ := Submission.BoseGases.av_bounds_weak (v := v) hR hv hvrad hv_supp h
  have hsclpos : 0 < scl := by
    rw [hscldef]; exact Work.SmallBoxSliding.smallConvLower_pos M
  have h2scl : 0 ≤ 2 / scl := div_nonneg (by norm_num) hsclpos.le
  have hΛ0 : 0 ≤ Λ := by
    rw [hΛdef]
    exact mul_nonneg Submission.BoseGases.chiSupAbs_nonneg
      (Submission.BoseGases.chiSmallDecay_nonneg M)
  have hΛ2 : 0 ≤ Λ * (2 / scl) * Λ := mul_nonneg (mul_nonneg hΛ0 h2scl) hΛ0
  have hG0 : 0 ≤ G := by
    rw [hGdef]
    exact mul_nonneg (mul_nonneg (by norm_num) Real.pi_nonneg) havnn
  have hK0 : 0 ≤ K := by
    rw [hKdef]
    exact mul_nonneg (mul_nonneg (pow_nonneg hΛ0 2) h2scl) hG0
  -- the two auxiliary facts proved by the siblings
  obtain ⟨hA1bd, hAvbd, hg0int, hvint, hGval0⟩ :=
    Work.BoseFixB1B.fj_kernel_bounds hv hv1 hR hv_supp hM hℓ hd hR16 hRχ
  have hsupport : ∀ y : ℝ³,
      Submission.BoseGases.chiSmallB M ℓ d u y ≠ 0 → y ∈ Submission.BoseGases.dlBox ℓ d u :=
    fun y hy => Work.BoseFixB1B.fj_chiSmallB_support hM hℓ hd u y hy
  have hGval : (∫ z : ℝ³, |Submission.BoseGases.g0 v h z|) = G :=
    hGval0.trans hGdef.symm
  have hχzero : ∀ y : ℝ³, y ∉ B → χ y = 0 := by
    intro y hy
    rw [hBdef] at hy
    by_contra hne
    exact hy (hsupport y (by rwa [hχdef] at hne))
  have hχzero_ac : ∀ y : ℝ³, y ∉ ac → χ y = 0 := by
    intro y hy
    rw [hacdef] at hy
    refine hχzero y (fun hmem => hy ?_)
    rw [hBdef] at hmem
    exact Work.SmallBoxSliding.dlBox_subset_acube ℓ d u hmem
  have hχbd : ∀ z : ℝ³, |χ z| ≤ Λ := by
    intro z
    rw [hχdef, hΛdef]
    refine le_trans (Work.SmallBoxSliding.abs_chiSmallB_le (M := M) hM u z) ?_
    refine mul_le_mul_of_nonneg_left ?_ Submission.BoseGases.chiSupAbs_nonneg
    have h' := Submission.BoseGases.chiSmall_decay_coord_le_decay hM ((ℓ * d)⁻¹ • z - u)
    rwa [abs_of_nonneg (Submission.BoseGases.chiSmall_nonneg M _)] at h'
  have hχnn : ∀ z : ℝ³, 0 ≤ χ z := by
    intro z; rw [hχdef]; exact Submission.BoseGases.chiSmallB_nonneg M ℓ d u z
  have hunfold1 : ∀ x y : ℝ³,
      Submission.BoseGases.wSmall1Pair h M ℓ d u x y = χ x * A1 (x - y) * χ y := by
    intro x y
    simp only [hχdef, hA1def, Submission.BoseGases.wSmall1Pair, Submission.BoseGases.wSmallPair]
  have hunfoldv : ∀ x y : ℝ³,
      Submission.BoseGases.wSmallPair M ℓ d u v x y = χ x * Av (x - y) * χ y := by
    intro x y
    simp only [hχdef, hAvdef, Submission.BoseGases.wSmallPair]
  -- the a.e. facts about the numerators
  have hae_g0nn : ∀ᵐ z ∂(volume : Measure ℝ³), 0 ≤ Submission.BoseGases.g0 v h z :=
    Submission.BoseGases.g0_nonneg_ae hR hv hvrad hv_supp h
  have hae_le : ∀ᵐ z ∂(volume : Measure ℝ³), Submission.BoseGases.g0 v h z ≤ v z := by
    have hspec := Classical.choose_spec h
    have hb := Submission.BoseGases.scattering_bounds_ae (w := Classical.choose h) hR hv hvrad
      hv_supp hspec.1 hspec.2
    filter_upwards [hae_g0nn, hb.1] with z hz0 hw0
    have heq : Submission.BoseGases.g0 v h z = v z * (1 - Classical.choose h z) := rfl
    rw [heq]
    calc v z * (1 - Classical.choose h z) ≤ v z * 1 :=
          mul_le_mul_of_nonneg_left (by linarith) (hv z)
      _ = v z := mul_one _
  have hshift_int : ∀ x : ℝ³, Integrable (fun y : ℝ³ => |Submission.BoseGases.g0 v h (x - y)|) :=
    fun x => hg0int.comp_sub_left x
  -- pointwise bounds for the two kernels
  have hA1' : ∀ z : ℝ³, |A1 z| ≤ (2 / scl) * |Submission.BoseGases.g0 v h z| := by
    intro z
    have hbd := hA1bd z
    simp only [hA1def] at hbd ⊢
    calc |Submission.BoseGases.wSmallScaled M (ℓ * d) (Submission.BoseGases.g0 v h) z
          / Submission.BoseGases.convScale ℓ z| ≤ 2 * |Submission.BoseGases.g0 v h z| / scl := hbd
      _ = (2 / scl) * |Submission.BoseGases.g0 v h z| := by ring
  have hAv' : ∀ z : ℝ³, |Av z| ≤ (2 / scl) * |v z| := by
    intro z
    have hbd := hAvbd z
    simp only [hAvdef] at hbd ⊢
    calc |Submission.BoseGases.wSmallScaled M (ℓ * d) v z / Submission.BoseGases.convScale ℓ z|
          ≤ 2 * |v z| / scl := hbd
      _ = (2 / scl) * |v z| := by ring
  have hpt1 : ∀ x y : ℝ³, |Submission.BoseGases.wSmall1Pair h M ℓ d u x y|
      ≤ (Λ * (2 / scl) * Λ) * |Submission.BoseGases.g0 v h (x - y)| := by
    intro x y
    rw [hunfold1 x y, abs_mul, abs_mul, abs_of_nonneg (hχnn y)]
    calc |χ x| * |A1 (x - y)| * χ y
        ≤ Λ * ((2 / scl) * |Submission.BoseGases.g0 v h (x - y)|) * Λ :=
          mul_le_mul (mul_le_mul (hχbd x) (hA1' (x - y)) (abs_nonneg _) hΛ0)
            (le_trans (le_abs_self _) (hχbd y))
            (hχnn y) (mul_nonneg hΛ0 (mul_nonneg h2scl (abs_nonneg _)))
      _ = (Λ * (2 / scl) * Λ) * |Submission.BoseGases.g0 v h (x - y)| := by ring
  have hptv : ∀ x y : ℝ³, |Submission.BoseGases.wSmallPair M ℓ d u v x y|
      ≤ (Λ * (2 / scl) * Λ) * |v (x - y)| := by
    intro x y
    rw [hunfoldv x y, abs_mul, abs_mul, abs_of_nonneg (hχnn y)]
    calc |χ x| * |Av (x - y)| * χ y
        ≤ Λ * ((2 / scl) * |v (x - y)|) * Λ :=
          mul_le_mul (mul_le_mul (hχbd x) (hAv' (x - y)) (abs_nonneg _) hΛ0)
            (le_trans (le_abs_self _) (hχbd y))
            (hχnn y) (mul_nonneg hΛ0 (mul_nonneg h2scl (abs_nonneg _)))
      _ = (Λ * (2 / scl) * Λ) * |v (x - y)| := by ring
  -- `Φ₁ x = ∫_{ac} w₁ ≤ K`
  have hΦle : ∀ x : ℝ³,
      (∫ y in ac, Submission.BoseGases.wSmall1Pair h M ℓ d u x y) ≤ K := by
    intro x
    have hdom : Integrable (fun y : ℝ³ =>
        (Λ * (2 / scl) * Λ) * |Submission.BoseGases.g0 v h (x - y)|) :=
      (hshift_int x).const_mul (Λ * (2 / scl) * Λ)
    have h1 : |(∫ y in ac, Submission.BoseGases.wSmall1Pair h M ℓ d u x y)|
        ≤ (Λ * (2 / scl) * Λ) * (∫ y in ac, |Submission.BoseGases.g0 v h (x - y)|) := by
      calc |∫ y in ac, Submission.BoseGases.wSmall1Pair h M ℓ d u x y|
          = ‖∫ y in ac, Submission.BoseGases.wSmall1Pair h M ℓ d u x y‖ := by
            rw [Real.norm_eq_abs]
        _ ≤ ∫ y in ac, ‖Submission.BoseGases.wSmall1Pair h M ℓ d u x y‖ :=
            norm_integral_le_integral_norm _
        _ = ∫ y in ac, |Submission.BoseGases.wSmall1Pair h M ℓ d u x y| := by
            simp only [Real.norm_eq_abs]
        _ ≤ ∫ y in ac, (Λ * (2 / scl) * Λ) * |Submission.BoseGases.g0 v h (x - y)| :=
            integral_mono_of_nonneg (ae_of_all _ (fun y => abs_nonneg _)) hdom.integrableOn
              (ae_of_all _ (fun y => hpt1 x y))
        _ = (Λ * (2 / scl) * Λ) * (∫ y in ac, |Submission.BoseGases.g0 v h (x - y)|) :=
            integral_const_mul _ _
    have h3 : (∫ y in ac, |Submission.BoseGases.g0 v h (x - y)|)
        ≤ ∫ z : ℝ³, |Submission.BoseGases.g0 v h z| := by
      calc (∫ y in ac, |Submission.BoseGases.g0 v h (x - y)|)
          ≤ ∫ y : ℝ³, |Submission.BoseGases.g0 v h (x - y)| :=
            setIntegral_le_integral (hshift_int x) (ae_of_all _ (fun y => abs_nonneg _))
        _ = ∫ z : ℝ³, |Submission.BoseGases.g0 v h z| :=
            integral_sub_left_eq_self (fun z : ℝ³ => |Submission.BoseGases.g0 v h z|) volume x
    calc (∫ y in ac, Submission.BoseGases.wSmall1Pair h M ℓ d u x y)
        ≤ |(∫ y in ac, Submission.BoseGases.wSmall1Pair h M ℓ d u x y)| := le_abs_self _
      _ ≤ (Λ * (2 / scl) * Λ) * (∫ y in ac, |Submission.BoseGases.g0 v h (x - y)|) := h1
      _ ≤ (Λ * (2 / scl) * Λ) * (∫ z : ℝ³, |Submission.BoseGases.g0 v h z|) :=
            mul_le_mul_of_nonneg_left h3 hΛ2
      _ = K := by rw [hKdef, hGval, hΛdef, hscldef]; ring
  -- `0 ≤ᵐ Φ₁` and the bound on the total fibre
  have hΦnn : ∀ x : ℝ³,
      0 ≤ᵐ[volume.restrict ac]
        (fun y : ℝ³ => Submission.BoseGases.wSmall1Pair h M ℓ d u x y) := by
    intro x
    filter_upwards [ae_mono Measure.restrict_le_self (ae_comp_sub_of_ae hae_g0nn x)] with y hy
    exact wSmallPair_nonneg_of_nonneg hy
  have hvolB : (volume : Measure ℝ³) B ≠ ⊤ := by
    rw [hBdef]; exact ne_of_lt (Work.SmallBoxSliding.volume_dlBox_lt_top hℓ d u)
  haveI hfinB : IsFiniteMeasure (volume.restrict B) := ⟨by
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    exact lt_top_iff_ne_top.mpr hvolB⟩
  have hΦ0 : (∫ x in B, ∫ y in ac, Submission.BoseGases.wSmall1Pair h M ℓ d u x y)
      ≤ K * (volume B).toReal := by
    have h1 : (fun x : ℝ³ => (∫ y in ac, Submission.BoseGases.wSmall1Pair h M ℓ d u x y))
        ≤ᵐ[volume.restrict B] fun _ : ℝ³ => K := ae_of_all _ hΦle
    have h2 : 0 ≤ᵐ[volume.restrict B]
        (fun x : ℝ³ => (∫ y in ac, Submission.BoseGases.wSmall1Pair h M ℓ d u x y)) :=
      ae_of_all _ (fun x => integral_nonneg_of_ae (hΦnn x))
    have h3 : (∫ x : ℝ³, (∫ y in ac, Submission.BoseGases.wSmall1Pair h M ℓ d u x y)
          ∂(volume.restrict B)) ≤ ∫ x : ℝ³, K ∂(volume.restrict B) :=
      integral_mono_of_nonneg h2 (integrable_const K) h1
    calc (∫ x in B, ∫ y in ac, Submission.BoseGases.wSmall1Pair h M ℓ d u x y)
        = ∫ x : ℝ³, (∫ y in ac, Submission.BoseGases.wSmall1Pair h M ℓ d u x y)
            ∂(volume.restrict B) := rfl
      _ ≤ ∫ x : ℝ³, K ∂(volume.restrict B) := h3
      _ = K * (volume B).toReal := by
            rw [setIntegral_const, smul_eq_mul, Measure.real_def]; ring
  -- the inner comparison at fixed `x`
  have hinner : ∀ x : ℝ³, (∫ y in B, Submission.BoseGases.wSmall1Pair h M ℓ d u x y)
      ≤ (∫ y in B, Submission.BoseGases.wSmallPair M ℓ d u v x y) := by
    intro x
    have hf : 0 ≤ᵐ[volume.restrict B]
        (fun y : ℝ³ => Submission.BoseGases.wSmall1Pair h M ℓ d u x y) := by
      filter_upwards [ae_mono Measure.restrict_le_self (ae_comp_sub_of_ae hae_g0nn x)] with y hy
      exact wSmallPair_nonneg_of_nonneg hy
    have hgi : Integrable (fun y : ℝ³ => Submission.BoseGases.wSmallPair M ℓ d u v x y)
        (volume.restrict B) := by
      refine Integrable.mono' (g := fun y : ℝ³ => (Λ * (2 / scl) * Λ) * |v (x - y)|)
        (((hvint.comp_sub_left x).const_mul (Λ * (2 / scl) * Λ)).integrableOn) ?_ ?_
      · exact (((aemeasurable_wSmallPair_fibre (hv1.aestronglyMeasurable.aemeasurable) hM u
          x).aestronglyMeasurable).mono_measure Measure.restrict_le_self)
      · filter_upwards with y
        rw [Real.norm_eq_abs]
        exact hptv x y
    have hle : (fun y : ℝ³ => Submission.BoseGases.wSmall1Pair h M ℓ d u x y)
        ≤ᵐ[volume.restrict B]
          fun y : ℝ³ => Submission.BoseGases.wSmallPair M ℓ d u v x y := by
      filter_upwards [ae_mono Measure.restrict_le_self (ae_comp_sub_of_ae hae_le x)] with y hy
      exact Work.BoseFixB1.wSmallPair_mono_of_le x y hy
    exact integral_mono_of_nonneg hf hgi hle
  -- localisation of the inner integral from `ac` to `B`
  have hloc : ∀ x : ℝ³, (∫ y in ac, Submission.BoseGases.wSmall1Pair h M ℓ d u x y)
      = (∫ y in B, Submission.BoseGases.wSmall1Pair h M ℓ d u x y) := by
    intro x
    have e1 : (∫ y in ac, Submission.BoseGases.wSmall1Pair h M ℓ d u x y)
        = ∫ y : ℝ³, Submission.BoseGases.wSmall1Pair h M ℓ d u x y :=
      setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun y hy => by rw [hunfold1 x y, hχzero_ac y hy, mul_zero])
    have e2 : (∫ y in B, Submission.BoseGases.wSmall1Pair h M ℓ d u x y)
        = ∫ y : ℝ³, Submission.BoseGases.wSmall1Pair h M ℓ d u x y :=
      setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun y hy => by rw [hunfold1 x y, hχzero y hy, mul_zero])
    rw [e1, e2]
  -- the marginal `Ψ x = ∫_B w_v`: bound, measurability, integrability
  have hΨle : ∀ x : ℝ³,
      |(∫ y in B, Submission.BoseGases.wSmallPair M ℓ d u v x y)|
        ≤ Λ * (2 / scl) * Λ * (∫ z : ℝ³, |v z|) := by
    intro x
    have hdom : Integrable (fun y : ℝ³ => (Λ * (2 / scl) * Λ) * |v (x - y)|) :=
      (hvint.comp_sub_left x).const_mul (Λ * (2 / scl) * Λ)
    have h1 : |(∫ y in B, Submission.BoseGases.wSmallPair M ℓ d u v x y)|
        ≤ (Λ * (2 / scl) * Λ) * (∫ y in B, |v (x - y)|) := by
      calc |∫ y in B, Submission.BoseGases.wSmallPair M ℓ d u v x y|
          = ‖∫ y in B, Submission.BoseGases.wSmallPair M ℓ d u v x y‖ := by
            rw [Real.norm_eq_abs]
        _ ≤ ∫ y in B, ‖Submission.BoseGases.wSmallPair M ℓ d u v x y‖ :=
            norm_integral_le_integral_norm _
        _ = ∫ y in B, |Submission.BoseGases.wSmallPair M ℓ d u v x y| := by
            simp only [Real.norm_eq_abs]
        _ ≤ ∫ y in B, (Λ * (2 / scl) * Λ) * |v (x - y)| :=
            integral_mono_of_nonneg (ae_of_all _ (fun y => abs_nonneg _)) hdom.integrableOn
              (ae_of_all _ (fun y => hptv x y))
        _ = (Λ * (2 / scl) * Λ) * (∫ y in B, |v (x - y)|) := integral_const_mul _ _
    have h3 : (∫ y in B, |v (x - y)|) ≤ ∫ z : ℝ³, |v z| := by
      calc (∫ y in B, |v (x - y)|) ≤ ∫ y : ℝ³, |v (x - y)| :=
            setIntegral_le_integral (hvint.comp_sub_left x) (ae_of_all _ (fun y => abs_nonneg _))
        _ = ∫ z : ℝ³, |v z| := integral_sub_left_eq_self (fun z : ℝ³ => |v z|) volume x
    calc |∫ y in B, Submission.BoseGases.wSmallPair M ℓ d u v x y|
        ≤ (Λ * (2 / scl) * Λ) * (∫ y in B, |v (x - y)|) := h1
      _ ≤ (Λ * (2 / scl) * Λ) * (∫ z : ℝ³, |v z|) := mul_le_mul_of_nonneg_left h3 hΛ2
  have hΨmeas : AEStronglyMeasurable
      (fun x : ℝ³ => ∫ y in B, Submission.BoseGases.wSmallPair M ℓ d u v x y)
      (volume.restrict B) := by
    have hjoint : AEStronglyMeasurable
        (fun p : ℝ³ × ℝ³ => Submission.BoseGases.wSmallPair M ℓ d u v p.1 p.2)
        ((volume : Measure ℝ³).prod (volume : Measure ℝ³)) :=
      Work.BoseFixB1.aesm_wSmallPair_prod_full u hv1.aestronglyMeasurable.aemeasurable
    have hsmall : (volume.restrict B).prod (volume.restrict B)
        ≤ (volume : Measure ℝ³).prod (volume : Measure ℝ³) :=
      Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self
    exact AEStronglyMeasurable.integral_prod_right'
      (μ := volume.restrict B) (ν := volume.restrict B) (hjoint.mono_measure hsmall)
  have hΨint : Integrable
      (fun x : ℝ³ => ∫ y in B, Submission.BoseGases.wSmallPair M ℓ d u v x y)
      (volume.restrict B) := by
    refine Integrable.mono' (g := fun _ : ℝ³ => Λ * (2 / scl) * Λ * (∫ z : ℝ³, |v z|))
      (integrable_const _) hΨmeas ?_
    filter_upwards with x
    rw [Real.norm_eq_abs]
    exact hΨle x
  -- the outer comparison
  have hout : (∫ x in B, ∫ y in ac, Submission.BoseGases.wSmall1Pair h M ℓ d u x y)
      ≤ (∫ x in B, ∫ y in B, Submission.BoseGases.wSmallPair M ℓ d u v x y) := by
    have hf : 0 ≤ᵐ[volume.restrict B]
        (fun x : ℝ³ => (∫ y in ac, Submission.BoseGases.wSmall1Pair h M ℓ d u x y)) :=
      ae_of_all _ (fun x => integral_nonneg_of_ae (hΦnn x))
    have hle : (fun x : ℝ³ => (∫ y in ac, Submission.BoseGases.wSmall1Pair h M ℓ d u x y))
        ≤ᵐ[volume.restrict B]
          fun x : ℝ³ => (∫ y in B, Submission.BoseGases.wSmallPair M ℓ d u v x y) :=
      ae_of_all _ (fun x => by
        show (∫ y in ac, Submission.BoseGases.wSmall1Pair h M ℓ d u x y)
          ≤ (∫ y in B, Submission.BoseGases.wSmallPair M ℓ d u v x y)
        rw [hloc x]; exact hinner x)
    exact integral_mono_of_nonneg hf hΨint hle
  -- final assembly
  have hL0 : 0 ≤ ∫ x in B, ∫ y in ac, Submission.BoseGases.wSmall1Pair h M ℓ d u x y :=
    integral_nonneg_of_ae (ae_of_all _ (fun x => integral_nonneg_of_ae (hΦnn x)))
  calc (∫ x in B, ∫ y in ac, Submission.BoseGases.wSmall1Pair h M ℓ d u x y) ^ 2
      = (∫ x in B, ∫ y in ac, Submission.BoseGases.wSmall1Pair h M ℓ d u x y)
          * (∫ x in B, ∫ y in ac, Submission.BoseGases.wSmall1Pair h M ℓ d u x y) := by ring
    _ ≤ (∫ x in B, ∫ y in ac, Submission.BoseGases.wSmall1Pair h M ℓ d u x y)
          * (K * (volume B).toReal) := mul_le_mul_of_nonneg_left hΦ0 hL0
    _ ≤ (∫ x in B, ∫ y in B, Submission.BoseGases.wSmallPair M ℓ d u v x y)
          * (K * (volume B).toReal) :=
          mul_le_mul_of_nonneg_right hout (mul_nonneg hK0 (by positivity))
    _ = ((Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M) ^ 2
            * (2 / Work.SmallBoxSliding.smallConvLower M)
            * (8 * Real.pi * _root_.BoseGases.a v))
          * (volume (Submission.BoseGases.dlBox ℓ d u)).toReal
          * (∫ x in Submission.BoseGases.dlBox ℓ d u,
              ∫ y in Submission.BoseGases.dlBox ℓ d u,
                Submission.BoseGases.wSmallPair M ℓ d u v x y) := by
          rw [hKdef, hΛdef, hscldef, hGdef, hBdef]; ring

theorem fibre_pair_joint {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) :
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ → ∀ u : EuclideanSpace ℝ (Fin 3),
        (∫ x in Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u,
          ∫ y in Submission.BoseGases.acube (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
            Submission.BoseGases.wSmall1Pair h
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u x y) ^ 2
          ≤ C * (MeasureTheory.volume (Submission.BoseGases.dlBox
                  (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)).toReal
              * (∫ x in Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u,
                  ∫ y in Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u,
                    Submission.BoseGases.wSmallPair
                      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u v x y) := by
  obtain ⟨ε₀, hε₀, hreg⟩ := Work.BoseFixB1.regime_sideAt_ge (v := v) hav hR
  refine ⟨ε₀, (Submission.BoseGases.chiSupAbs
        * Submission.BoseGases.chiSmallDecay Work.BoseBox.mValue) ^ 2
      * (2 / Work.SmallBoxSliding.smallConvLower Work.BoseBox.mValue)
      * (8 * Real.pi * _root_.BoseGases.a v), hε₀, ?_, ?_⟩
  · have h1 : 0 ≤ Submission.BoseGases.chiSupAbs
        * Submission.BoseGases.chiSmallDecay Work.BoseBox.mValue :=
      mul_nonneg Submission.BoseGases.chiSupAbs_nonneg
        (Submission.BoseGases.chiSmallDecay_nonneg Work.BoseBox.mValue)
    have h2 : 0 ≤ (2 : ℝ) / Work.SmallBoxSliding.smallConvLower Work.BoseBox.mValue :=
      div_nonneg (by norm_num) (le_of_lt (Work.SmallBoxSliding.smallConvLower_pos _))
    exact mul_nonneg (mul_nonneg (pow_nonneg h1 2) h2)
      (mul_nonneg (mul_nonneg (by norm_num) Real.pi_nonneg) (le_of_lt hav))
  · intro μ hAdm u
    have hℓ := Work.BoseFixB1.adm_ell_pos hAdm
    have hd := Work.BoseFixB1.adm_d_pos hAdm
    have hM : 1 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M := by
      norm_num [Work.BoseBox.paramsAt, Work.BoseBox.fsParams, Work.BoseBox.mValue]
    obtain ⟨hR16, hRχ⟩ := hreg μ hAdm.1 hAdm.2.1
    exact fibre_pair_joint_general (h := h) (R := R) hR hv_supp hv hv1 hvrad hM hℓ hd hR16 hRχ u

end Work.BoseFixB1B
