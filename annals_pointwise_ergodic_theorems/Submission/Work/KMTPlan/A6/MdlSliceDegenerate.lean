import Mathlib
import Submission.Work.KMTPlan.A6.MdlDefs
import Submission.Work.KMTPlan.A6.bumpFourierMass
import Submission.Work.KMTAreas.A7.varphiNt_bounds

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Polynomial Filter
open scoped ENNReal NNReal BigOperators Topology
open Work.KMTAreas.A7

local notation "Circ" => AddCircle (1:ℝ)

/-! ## Preliminaries -/

theorem zero_mem_iwArithFreqs' (ρ : ℝ) (l : ℕ) :
    (0 : Circ) ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l :=
  Work.Analysis.IonescuWainger.mem_iwArithFreqs.mpr
    ⟨1, Work.Analysis.IonescuWainger.one_mem_iwP ρ l, by simp⟩

theorem varphiN_zero_eq (N : ℕ) (ξ : ℝ) :
    varphiN N 0 ξ = Work.KMTContract.kmtEta ((2:ℝ) ^ (Work.Analysis.EndVar.logN N : ℝ) * ξ) := by
  simp [varphiN]

theorem continuous_ee' : Continuous Work.KMTAreas.A7.ee := by
  unfold Work.KMTAreas.A7.ee
  fun_prop

theorem inv_le_zpow_of_le_one {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) {j : ℤ} (hj : j ≤ -1) :
    x⁻¹ ≤ x ^ j := by simpa using zpow_le_zpow_right_of_le_one₀ hx0 hx1 hj

theorem iwKernel_eq_zero_of_not_integrable' {m : Circ → ℂ}
    (hm : ¬ MeasureTheory.Integrable m MeasureTheory.volume) (j : ℤ) :
    Work.Analysis.IWMultiplier.iwKernel m j = 0 := by
  have hv : (MeasureTheory.volume : Measure Circ) = AddCircle.haarAddCircle := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]; simp
  rw [Work.Analysis.IWMultiplier.iwKernel, fourierCoeff]
  refine MeasureTheory.integral_undef ?_
  rw [hv] at hm
  intro h
  refine hm ?_
  have h2 : MeasureTheory.Integrable
      (fun t : Circ => (fourier (-j) t • m t) • fourier j t) AddCircle.haarAddCircle :=
    h.mul_bdd ((map_continuous (fourier j)).aestronglyMeasurable)
      (Filter.Eventually.of_forall (fun t => by rw [fourier_apply, Circle.norm_coe]))
  refine h2.congr (Filter.Eventually.of_forall (fun t => ?_))
  have h1 : fourier (-j) t * fourier j t = 1 := by
    rw [← fourier_add, neg_add_cancel]; simp
  calc (fourier (-j) t • m t) • fourier j t
      = m t * (fourier (-j) t * fourier j t) := by simp only [smul_eq_mul]; ring
    _ = m t := by rw [h1, mul_one]

/-! ## The symbol of the degenerate bump is not integrable -/

theorem zpow_le_zpow_of_le_of_neg {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) {j : ℤ} (hj : j < 0) :
    v ^ j ≤ u ^ j := by
  have hv : 0 < v := lt_of_lt_of_le hu huv
  obtain ⟨m, hm, hjm⟩ : ∃ m : ℕ, 0 < m ∧ j = -(m : ℤ) := ⟨(-j).toNat, by omega, by omega⟩
  rw [hjm, zpow_neg, zpow_natCast, zpow_neg, zpow_natCast]
  rw [inv_le_inv₀ (pow_pos hv m) (pow_pos hu m)]
  exact pow_le_pow_left₀ (le_of_lt hu) huv m

theorem periodize_eq_sum_three (φ : ℝ → ℂ) (hφ : ∀ y : ℝ, 1 ≤ |y| → φ y = 0) (ξ : Circ) :
    Work.Analysis.IonescuWainger.periodize φ ξ =
      ∑ k ∈ Finset.Icc (-1:ℤ) 1,
        φ ((AddCircle.equivIco (1:ℝ) 0 ξ).val + (k:ℝ)) := by
  rw [Work.Analysis.IonescuWainger.periodize]
  refine tsum_eq_sum (fun k hk => ?_)
  rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hk
  have hx := (AddCircle.equivIco (1:ℝ) 0 ξ).2
  rw [Set.mem_Ico] at hx
  refine hφ _ ?_
  rcases hk with hk | hk
  · have hk2 : (2:ℝ) ≤ -(k:ℝ) := by
      have : (k:ℝ) ≤ -2 := by exact_mod_cast (by omega : k ≤ -2)
      linarith
    have hneg : (AddCircle.equivIco (1:ℝ) 0 ξ).val + (k:ℝ) < 0 := by linarith [hx.2]
    rw [abs_of_neg hneg]
    linarith [hx.2, hk2]
  · have hk2 : (2:ℝ) ≤ (k:ℝ) := by exact_mod_cast (by omega : 2 ≤ k)
    have hpos : 0 ≤ (AddCircle.equivIco (1:ℝ) 0 ξ).val + (k:ℝ) := by linarith [hx.1]
    rw [abs_of_nonneg hpos]
    linarith [hx.1, hk2]

theorem continuousAt_periodize_of (φ : ℝ → ℂ) (hφ : ∀ y : ℝ, 1 ≤ |y| → φ y = 0)
    (hcont : ∀ y : ℝ, y ≠ 0 → ContinuousAt φ y) {ξ : Circ} (hξ : ξ ≠ 0) :
    ContinuousAt (Work.Analysis.IonescuWainger.periodize φ) ξ := by
  have hfun : Work.Analysis.IonescuWainger.periodize φ = fun η : Circ =>
      ∑ k ∈ Finset.Icc (-1:ℤ) 1,
        φ ((AddCircle.equivIco (1:ℝ) 0 η).val + (k:ℝ)) :=
    funext (periodize_eq_sum_three φ hφ)
  rw [hfun]
  have hval : ContinuousAt (fun η : Circ => (AddCircle.equivIco (1:ℝ) 0 η).val) ξ :=
    (continuous_subtype_val.continuousAt).comp
      (AddCircle.continuousAt_equivIco (p := (1:ℝ)) (a := 0) (x := ξ) hξ)
  have hterm : ∀ k ∈ Finset.Icc (-1:ℤ) 1, ContinuousAt (fun η : Circ =>
      φ ((AddCircle.equivIco (1:ℝ) 0 η).val + (k:ℝ))) ξ := by
    intro k hk
    refine (hcont _ ?_).comp (hval.add continuousAt_const)
    intro hzero
    have hx := (AddCircle.equivIco (1:ℝ) 0 ξ).2
    rw [Set.mem_Ico] at hx
    obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hk
    interval_cases k
    · simp only [Int.cast_neg, Int.cast_one] at hzero
      linarith [hx.2]
    · simp only [Int.cast_zero, add_zero] at hzero
      refine hξ ?_
      have hcoe : ((AddCircle.equivIco (1:ℝ) 0 ξ).val : Circ) = ξ :=
        AddCircle.coe_equivIco (p := (1:ℝ)) (a := 0) (y := ξ)
      rw [← hcoe, hzero]
      simp
    · simp only [Int.cast_one] at hzero
      linarith [hx.1]
  have hsum : ∀ s : Finset ℤ, s ⊆ Finset.Icc (-1:ℤ) 1 → ContinuousAt (fun η : Circ => ∑ k ∈ s,
      φ ((AddCircle.equivIco (1:ℝ) 0 η).val + (k:ℝ))) ξ := by
    intro s
    induction s using Finset.induction with
    | empty => intro _; simpa using continuousAt_const
    | insert a s ha ih =>
        intro hsub
        simp only [Finset.sum_insert ha]
        exact (hterm a (hsub (Finset.mem_insert_self a s))).add
          (ih (fun b hb => hsub (Finset.mem_insert_of_mem hb)))
  exact hsum _ (Finset.Subset.refl _)

theorem sum_Icc_neg_one_one (f : ℤ → ℂ) :
    (∑ k ∈ Finset.Icc (-1:ℤ) 1, f k) = f (-1) + f 0 + f 1 := by
  rw [show (Finset.Icc (-1:ℤ) 1 : Finset ℤ) = {-1, 0, 1} by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨h1, h2⟩; omega
    · rintro (rfl | rfl | rfl) <;> norm_num]
  simp [add_assoc]

/-- **The abstract non-integrability engine.** -/
theorem key_pointwise_of_bump (A : Finset Circ) (h0A : (0:Circ) ∈ A) (φ : ℝ → ℂ) {c : ℝ}
    (hc : 0 < c) {j : ℤ} (hj : j ≤ -2)
    (hvan : ∀ y : ℝ, 1 ≤ |y| → φ y = 0)
    (hcont : ∀ y : ℝ, y ≠ 0 → ContinuousAt φ y)
    {δ₀ : ℝ} (hδ₀ : 0 < δ₀) (hnear : ∀ a ∈ Set.Ioc 0 δ₀, ‖φ a‖ = (c*a)^j)
    {C₀ : ℝ} (hC₀ : ∀ y : ℝ, (1/2:ℝ) ≤ |y| → ‖φ y‖ ≤ C₀) (hC₀nn : 0 ≤ C₀) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a ∈ Set.Ioc (0:ℝ) δ,
      (1/(2*c)) * a⁻¹ ≤ ‖Work.Analysis.IonescuWainger.iwSymbolSet A
        (Work.Analysis.IonescuWainger.periodize φ) (a : Circ)‖ := by
  classical
  set S : Finset Circ := A.erase 0 with hSdef
  have hbdd : ∀ α ∈ S, ∀ᶠ ξ in 𝓝 (0 : Circ),
      ‖Work.Analysis.IonescuWainger.periodize φ (ξ - α)‖ ≤
        ‖Work.Analysis.IonescuWainger.periodize φ ((0:Circ) - α)‖ + 1 := by
    intro α hα
    have hαne : (0 : Circ) - α ≠ 0 := by
      intro h
      exact (Finset.mem_erase.mp hα).1 (by simpa using h.symm)
    have hper : ContinuousAt (Work.Analysis.IonescuWainger.periodize φ)
        ((fun ξ : Circ => ξ - α) 0) :=
      continuousAt_periodize_of φ hvan hcont hαne
    have hsub : ContinuousAt (fun ξ : Circ => ξ - α) (0 : Circ) :=
      continuousAt_id.sub continuousAt_const
    have hcomp : ContinuousAt (fun ξ : Circ =>
        Work.Analysis.IonescuWainger.periodize φ (ξ - α)) (0 : Circ) :=
      hper.tendsto.comp hsub.tendsto
    have hnorm : ContinuousAt (fun ξ : Circ =>
        ‖Work.Analysis.IonescuWainger.periodize φ (ξ - α)‖) (0 : Circ) :=
      continuous_norm.continuousAt.comp hcomp
    obtain ⟨ε, hεpos, hε⟩ := (Metric.continuousAt_iff.mp hnorm) 1 (by norm_num)
    refine Metric.eventually_nhds_iff.mpr ⟨ε, hεpos, fun ξ hξ => ?_⟩
    have h1 := hε hξ
    rw [Real.dist_eq, abs_lt] at h1
    linarith [h1.2,
      norm_nonneg (Work.Analysis.IonescuWainger.periodize φ ((0:Circ) - α))]
  have hall : ∀ᶠ ξ in 𝓝 (0 : Circ), ∀ α ∈ S,
      ‖Work.Analysis.IonescuWainger.periodize φ (ξ - α)‖ ≤
        ‖Work.Analysis.IonescuWainger.periodize φ ((0:Circ) - α)‖ + 1 :=
    S.eventually_all.mpr (fun α hα => hbdd α hα)
  have hsum : ∀ᶠ ξ in 𝓝 (0 : Circ), (∑ α ∈ S,
      ‖Work.Analysis.IonescuWainger.periodize φ (ξ - α)‖) ≤
        ∑ α ∈ S, (‖Work.Analysis.IonescuWainger.periodize φ ((0:Circ) - α)‖ + 1) :=
    hall.mono (fun ξ hξ => Finset.sum_le_sum (fun α hα => hξ α hα))
  set C : ℝ := ∑ α ∈ S, (‖Work.Analysis.IonescuWainger.periodize φ ((0:Circ) - α)‖ + 1)
    with hCdef
  have hCnn : 0 ≤ C := by
    rw [hCdef]
    exact Finset.sum_nonneg (fun α _ => add_nonneg (norm_nonneg _) zero_le_one)
  have hcoec : Continuous (fun a : ℝ => (a : Circ)) := AddCircle.continuous_mk' (1:ℝ)
  have h2 : ∀ᶠ a : ℝ in 𝓝 (0:ℝ), (∑ α ∈ S,
      ‖Work.Analysis.IonescuWainger.periodize φ ((a:Circ) - α)‖) ≤ C := by
    rw [hCdef]
    exact hcoec.continuousAt.eventually hsum
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := Metric.eventually_nhds_iff.mp h2
  have hδspos : 0 < δ₁ / 2 := by linarith
  have hKnn : 0 ≤ C + C₀ := add_nonneg hCnn hC₀nn
  refine ⟨min (δ₁/2) (min δ₀ (min (1/4) (1/(2*c*(C + C₀ + 1))))), ?_, ?_⟩
  · refine lt_min hδspos (lt_min hδ₀ (lt_min (by norm_num) (by positivity)))
  · intro a ha
    have hapos : 0 < a := ha.1
    have ha_d1 : a < δ₁ := by
      have h1 : a ≤ δ₁ / 2 := le_trans ha.2 (min_le_left _ _)
      linarith
    have ha_δ₀ : a ≤ δ₀ := le_trans ha.2 (le_trans (min_le_right _ _) (min_le_left _ _))
    have ha_14 : a ≤ 1/4 := le_trans ha.2
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
    have ha_c : a ≤ 1/(2*c*(C + C₀ + 1)) := le_trans ha.2
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
    have hsumle : (∑ α ∈ S, ‖Work.Analysis.IonescuWainger.periodize φ ((a:Circ) - α)‖) ≤ C :=
      hδ₁ (y := a) (by rw [Real.dist_eq, sub_zero, abs_of_pos hapos]; exact ha_d1)
    have hvala : (AddCircle.equivIco (1:ℝ) 0 (a : Circ)).val = a := by
      have h := AddCircle.equivIco_coe_eq (x := a) (a := (0:ℝ)) (p := (1:ℝ))
        (show a ∈ Set.Ico (0:ℝ) (0+1) from ⟨le_of_lt hapos, by linarith [ha_14]⟩)
      rw [h]
    have ha0 : a ∈ Set.Ioc (0:ℝ) δ₀ := ⟨hapos, ha_δ₀⟩
    have hper_lb : (c*a)^j - C₀ ≤ ‖Work.Analysis.IonescuWainger.periodize φ (a : Circ)‖ := by
      rw [periodize_eq_sum_three φ hvan (a : Circ), hvala,
        sum_Icc_neg_one_one (fun k : ℤ => φ (a + (k:ℝ)))]
      have h1 : φ (a + ((1:ℤ):ℝ)) = 0 := by
        refine hvan _ ?_
        rw [show ((1:ℤ):ℝ) = 1 by norm_num, abs_of_pos (by linarith)]
        linarith [hapos]
      have h0 : φ (a + ((0:ℤ):ℝ)) = φ a := by norm_num
      have h2 : ‖φ (a + ((-1:ℤ):ℝ))‖ ≤ C₀ := by
        refine hC₀ _ ?_
        rw [show ((-1:ℤ):ℝ) = -1 by norm_num, abs_of_neg (by linarith)]
        linarith [ha_14]
      rw [h1, add_zero, h0]
      calc (c*a)^j - C₀ = ‖φ a‖ - C₀ := by rw [hnear a ha0]
        _ ≤ ‖φ (a + ((-1:ℤ):ℝ)) + φ a‖ := by
            have h := norm_sub_le (φ (a + ((-1:ℤ):ℝ)) + φ a) (φ (a + ((-1:ℤ):ℝ)))
            rw [add_sub_cancel_left] at h
            linarith
    have hsplit : Work.Analysis.IonescuWainger.iwSymbolSet A
          (Work.Analysis.IonescuWainger.periodize φ) (a:Circ)
        = Work.Analysis.IonescuWainger.periodize φ ((a:Circ) - 0) +
          ∑ α ∈ S, Work.Analysis.IonescuWainger.periodize φ ((a:Circ) - α) := by
      rw [Work.Analysis.IonescuWainger.iwSymbolSet_apply, ← Finset.insert_erase h0A, ← hSdef]
      rw [Finset.sum_insert (Finset.notMem_erase 0 A)]
    have hca1 : c * a ≤ 1 := by
      have hle : c * a ≤ c * (1/(2*c*(C + C₀ + 1))) :=
        mul_le_mul_of_nonneg_left ha_c (le_of_lt hc)
      have heq : c * (1/(2*c*(C + C₀ + 1))) = 1/(2*(C + C₀ + 1)) := by field_simp
      rw [heq] at hle
      have h2 : 1/(2*(C + C₀ + 1)) ≤ 1 := by
        rw [div_le_one (by linarith [hKnn])]
        linarith [hKnn]
      linarith
    have hcainv : 2 * (C + C₀) ≤ (c * a)⁻¹ := by
      have hle : c * a ≤ 1/(2*(C + C₀ + 1)) := by
        have h := mul_le_mul_of_nonneg_left ha_c (le_of_lt hc)
        have heq : c * (1/(2*c*(C + C₀ + 1))) = 1/(2*(C + C₀ + 1)) := by field_simp
        rwa [heq] at h
      have hpos : (0:ℝ) < c * a := by positivity
      have h1 : (1/(2*(C + C₀ + 1)))⁻¹ ≤ ((c)*a)⁻¹ := by
        rw [inv_le_inv₀ (by positivity) hpos]
        exact hle
      have h2 : (1/(2*(C + C₀ + 1)))⁻¹ = 2*(C + C₀ + 1) := by rw [one_div, inv_inv]
      rw [h2] at h1
      linarith [hKnn]
    have hpow : ((c) * a)⁻¹ ≤ ((c) * a) ^ j :=
      inv_le_zpow_of_le_one (by positivity) hca1 (by omega)
    have htri : ‖Work.Analysis.IonescuWainger.periodize φ ((a:Circ) - 0)‖ -
          ‖∑ α ∈ S, Work.Analysis.IonescuWainger.periodize φ ((a:Circ) - α)‖ ≤
        ‖Work.Analysis.IonescuWainger.periodize φ ((a:Circ) - 0) +
          ∑ α ∈ S, Work.Analysis.IonescuWainger.periodize φ ((a:Circ) - α)‖ := by
      have h := norm_sub_le (Work.Analysis.IonescuWainger.periodize φ ((a:Circ) - 0) +
        ∑ α ∈ S, Work.Analysis.IonescuWainger.periodize φ ((a:Circ) - α))
        (∑ α ∈ S, Work.Analysis.IonescuWainger.periodize φ ((a:Circ) - α))
      rw [add_sub_cancel_right] at h
      linarith
    have hsum_norm : ‖∑ α ∈ S, Work.Analysis.IonescuWainger.periodize φ ((a:Circ) - α)‖
        ≤ ∑ α ∈ S, ‖Work.Analysis.IonescuWainger.periodize φ ((a:Circ) - α)‖ :=
      norm_sum_le _ _
    have h4 : ‖Work.Analysis.IonescuWainger.periodize φ ((a:Circ) - 0)‖
        = ‖Work.Analysis.IonescuWainger.periodize φ (a:Circ)‖ := by rw [sub_zero]
    rw [hsplit]
    calc (1/(2*c)) * a⁻¹ = (1/2) * ((c) * a)⁻¹ := by rw [mul_inv_rev]; ring
      _ ≤ (1/2) * ((c) * a) ^ j := by linarith [hpow]
      _ ≤ ((c) * a) ^ j - (C + C₀) := by linarith [hcainv]
      _ ≤ ‖Work.Analysis.IonescuWainger.periodize φ ((a:Circ) - 0) +
            ∑ α ∈ S, Work.Analysis.IonescuWainger.periodize φ ((a:Circ) - α)‖ := by
          linarith [htri, hsum_norm, hsumle, h4, hper_lb]

/-- The symbol of a bump satisfying the hypotheses of `key_pointwise_of_bump` is not
integrable. -/
theorem symbol_not_integrable_of_key (A : Finset Circ) (φ : ℝ → ℂ) {c : ℝ} (hc : 0 < c) {j : ℤ}
    (hj : j ≤ -2) (hvan : ∀ y : ℝ, 1 ≤ |y| → φ y = 0)
    (hcont : ∀ y : ℝ, y ≠ 0 → ContinuousAt φ y)
    {δ₀ : ℝ} (hδ₀ : 0 < δ₀) (hnear : ∀ a ∈ Set.Ioc 0 δ₀, ‖φ a‖ = (c*a)^j)
    {C₀ : ℝ} (hC₀ : ∀ y : ℝ, (1/2:ℝ) ≤ |y| → ‖φ y‖ ≤ C₀) (hC₀nn : 0 ≤ C₀)
    (h0A : (0:Circ) ∈ A) :
    ¬ MeasureTheory.Integrable
      (Work.Analysis.IonescuWainger.iwSymbolSet A
        (Work.Analysis.IonescuWainger.periodize φ)) MeasureTheory.volume := by
  intro hΦ
  obtain ⟨δ, hδpos, hkey⟩ := key_pointwise_of_bump A h0A φ hc hj hvan hcont hδ₀ hnear hC₀ hC₀nn
  have hδ1 : 0 < min δ 1 := lt_min hδpos zero_lt_one
  have hOn1 : IntegrableOn (fun a : ℝ => Work.Analysis.IonescuWainger.iwSymbolSet A
      (Work.Analysis.IonescuWainger.periodize φ) (a : Circ))
      (Set.Ioc 0 1) MeasureTheory.volume := by
    simpa only [Function.comp_def, zero_add, MeasureTheory.IntegrableOn] using
      (AddCircle.measurePreserving_mk (T := 1) (t := 0)).integrable_comp_of_integrable hΦ
  have hOn2 : IntegrableOn (fun a : ℝ => Work.Analysis.IonescuWainger.iwSymbolSet A
      (Work.Analysis.IonescuWainger.periodize φ) (a : Circ))
      (Set.Ioc 0 (min δ 1)) MeasureTheory.volume :=
    hOn1.mono_set (Set.Ioc_subset_Ioc_right (min_le_right δ 1))
  have hnorm : IntegrableOn (fun a : ℝ => ‖Work.Analysis.IonescuWainger.iwSymbolSet A
      (Work.Analysis.IonescuWainger.periodize φ) (a : Circ)‖)
      (Set.Ioc 0 (min δ 1)) MeasureTheory.volume := hOn2.norm
  have hmain : IntegrableOn (fun a : ℝ => (1/(2*c)) * a⁻¹)
      (Set.Ioc 0 (min δ 1)) MeasureTheory.volume := by
    refine MeasureTheory.Integrable.mono' hnorm ?_ ?_
    · exact (measurable_const.mul measurable_id.inv).aestronglyMeasurable
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with a ha
      have haδ : a ∈ Set.Ioc (0:ℝ) δ := ⟨ha.1, le_trans ha.2 (min_le_left δ 1)⟩
      have h := hkey a haδ
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) (inv_nonneg.mpr ha.1.le))]
      exact h
  have hinv : IntegrableOn (fun a : ℝ => a⁻¹) (Set.Ioc 0 (min δ 1)) MeasureTheory.volume := by
    have h2 : IntegrableOn (fun a : ℝ => ((2*c)) • ((1/(2*c)) * a⁻¹))
        (Set.Ioc 0 (min δ 1)) MeasureTheory.volume := hmain.const_mul _
    refine h2.congr_fun (fun a ha => ?_) measurableSet_Ioc
    have hcnz : c ≠ 0 := ne_of_gt hc
    have haz : a ≠ 0 := ne_of_gt ha.1
    simp only [smul_eq_mul]
    field_simp
  have hnot : ¬ IntervalIntegrable (fun x : ℝ => x⁻¹) MeasureTheory.volume 0 (min δ 1) := by
    rw [intervalIntegrable_inv_iff]
    rintro (h | h)
    · exact absurd h.symm (ne_of_gt hδ1)
    · exact h ⟨min_le_left 0 (min δ 1), le_max_left 0 (min δ 1)⟩
  exact hnot ((intervalIntegrable_iff (f := fun x : ℝ => x⁻¹) (a := 0) (b := min δ 1)
    (μ := MeasureTheory.volume)).mpr
      (by simpa [Set.uIoc_of_le hδ1.le] using hinv))

theorem Tle_eq_zero_of_symbol_not_integrable (ρ : ℝ) (l : ℕ) {φ : ℝ → ℂ}
    (h : ¬ MeasureTheory.Integrable
      (Work.Analysis.IonescuWainger.iwSymbolSet (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
        (Work.Analysis.IonescuWainger.periodize φ)) MeasureTheory.volume)
    (f : ℤ → ℂ) :
    Work.KMTAreas.A7.Tle ρ l φ f = 0 := by
  have hker : ∀ i : ℤ, Work.Analysis.IWMultiplier.iwKernel
      (Work.Analysis.IonescuWainger.iwSymbolSet (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
        (Work.Analysis.IonescuWainger.periodize φ)) i = 0 :=
    fun i => iwKernel_eq_zero_of_not_integrable' h i
  funext n
  rw [Tle_apply]
  have hzero : (fun i : ℤ => Work.Analysis.IWMultiplier.iwKernel
      (Work.Analysis.IonescuWainger.iwSymbolSet (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
        (Work.Analysis.IonescuWainger.periodize φ)) i * f (n - i))
      = fun _ => (0 : ℂ) := funext (fun i => by rw [hker i, zero_mul])
  rw [hzero]
  simp

/-! ## The `varphitildeNtj` instantiation -/

theorem periodize_zero (ξ : Circ) :
    Work.Analysis.IonescuWainger.periodize (fun _ : ℝ => 0) ξ = 0 := by
  rw [Work.Analysis.IonescuWainger.periodize]
  simp

theorem norm_ofReal_mul (a b : ℝ) : ‖(((a * b : ℝ)) : ℂ)‖ = |a| * |b| :=
  (RCLike.norm_ofReal (a * b)).trans (abs_mul a b)

theorem varphitildeNtj_eq (P : Polynomial ℤ) (N : ℕ) (j : ℤ) (t ξ : ℝ) :
    Work.KMTPlan.A6.varphitildeNtj P N 0 j t ξ =
      ((((((N:ℝ)^P.natDegree) * ξ : ℝ)) : ℂ))^j *
        (Work.KMTContract.kmtEta
            ((2:ℝ)^((P.natDegree:ℝ) * (Work.Analysis.EndVar.logN N : ℝ)) * ξ) *
          Work.KMTAreas.A7.ee (Work.KMTAreas.A7.PevalR P ((N:ℝ)*t) * ξ)) := by
  rw [Work.KMTPlan.A6.varphitildeNtj, Work.KMTAreas.A7.varphitildeNt,
    Work.KMTPlan.A6.bfm_varphitildeN_zero]
  simp only [Nat.cast_zero, mul_zero, Real.rpow_zero, one_mul]
  ring_nf

theorem varphitildeNtj_symbol_not_integrable (P : Polynomial ℤ) (ρ : ℝ) (l N : ℕ) (j : ℤ)
    (hj : j ≤ -2) (t : ℝ) (hntriv : ¬ (N = 0 ∧ P.natDegree ≠ 0)) :
    ¬ MeasureTheory.Integrable
      (Work.Analysis.IonescuWainger.iwSymbolSet (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
        (Work.Analysis.IonescuWainger.periodize
          (Work.KMTPlan.A6.varphitildeNtj P N 0 j t))) MeasureTheory.volume := by
  set φ : ℝ → ℂ := Work.KMTPlan.A6.varphitildeNtj P N 0 j t with hφdef
  have h0A : (0 : Circ) ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l :=
    zero_mem_iwArithFreqs' ρ l
  have hs1 : 1 ≤ (2:ℝ)^((P.natDegree:ℝ) * (Work.Analysis.EndVar.logN N : ℝ)) := by
    refine Real.one_le_rpow (by norm_num : (1:ℝ) ≤ 2) ?_
    exact mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hspos : 0 < (2:ℝ)^((P.natDegree:ℝ) * (Work.Analysis.EndVar.logN N : ℝ)) :=
    lt_of_lt_of_le zero_lt_one hs1
  have hcpos : 0 < (N:ℝ)^P.natDegree := by
    by_cases hN : N = 0
    · have hd : P.natDegree = 0 := by
        by_contra hd
        exact hntriv ⟨hN, hd⟩
      rw [hN, hd]
      norm_num
    · have hN1 : 1 ≤ N := by omega
      exact pow_pos (by exact_mod_cast (by omega : 0 < N)) _
  have hvan : ∀ y : ℝ, 1 ≤ |y| → φ y = 0 := by
    intro y hy
    rw [hφdef, varphitildeNtj_eq]
    have h1 : 1 ≤ |(2:ℝ)^((P.natDegree:ℝ) * (Work.Analysis.EndVar.logN N : ℝ)) * y| := by
      rw [abs_mul, abs_of_nonneg (le_of_lt hspos)]
      nlinarith [hs1, hy]
    rw [Work.KMTContract.kmtEta_zero h1, zero_mul, mul_zero]
  have hcont : ∀ y : ℝ, y ≠ 0 → ContinuousAt φ y := by
    intro y hy
    have hcy : ((N:ℝ)^P.natDegree) * y ≠ 0 :=
      mul_ne_zero (ne_of_gt hcpos) hy
    have hyc : (((((N:ℝ)^P.natDegree) * y : ℝ)) : ℂ) ≠ 0 := by simpa using hcy
    have h1 : ContinuousAt (fun y : ℝ => (((((N:ℝ)^P.natDegree) * y : ℝ)) : ℂ)^j) y := by
      have hc₂ : ContinuousAt (fun x : ℝ => (((x:ℝ)) : ℂ)^j) (((N:ℝ)^P.natDegree) * y) := by
        simpa only [Function.comp_def] using
          (continuousAt_zpow₀ _ j (Or.inl hyc)).comp Complex.continuous_ofReal.continuousAt
      exact hc₂.comp (continuousAt_const.mul continuousAt_id)
    have h2 : ContinuousAt (fun y : ℝ => Work.KMTContract.kmtEta
        ((2:ℝ)^((P.natDegree:ℝ) * (Work.Analysis.EndVar.logN N : ℝ)) * y)) y :=
      (contDiff_kmtEta 1).continuous.continuousAt.comp (continuousAt_const.mul continuousAt_id)
    have h3 : ContinuousAt (fun y : ℝ => Work.KMTAreas.A7.ee
        (Work.KMTAreas.A7.PevalR P ((N:ℝ)*t) * y)) y :=
      continuous_ee'.continuousAt.comp (continuousAt_const.mul continuousAt_id)
    have hfun : (Work.KMTPlan.A6.varphitildeNtj P N 0 j t)
        = fun y : ℝ => (((((N:ℝ)^P.natDegree) * y : ℝ)) : ℂ)^j *
            (Work.KMTContract.kmtEta
                ((2:ℝ)^((P.natDegree:ℝ) * (Work.Analysis.EndVar.logN N : ℝ)) * y) *
              Work.KMTAreas.A7.ee (Work.KMTAreas.A7.PevalR P ((N:ℝ)*t) * y)) :=
      funext (varphitildeNtj_eq P N j t)
    rw [hφdef, hfun]
    exact h1.mul (h2.mul h3)
  have hnear : ∀ a ∈ Set.Ioc (0:ℝ) (1/(2*(2:ℝ)^((P.natDegree:ℝ) * (Work.Analysis.EndVar.logN N : ℝ)))),
      ‖φ a‖ = (((N:ℝ)^P.natDegree) * a)^j := by
    intro a ha
    have hapos : 0 < a := ha.1
    have hsma : (2:ℝ)^((P.natDegree:ℝ) * (Work.Analysis.EndVar.logN N : ℝ)) * a ≤ 1/2 := by
      have h2 := ha.2
      rw [le_div_iff₀ (by positivity : (0:ℝ) < 2 * _)] at h2
      linarith [h2]
    rw [hφdef, varphitildeNtj_eq]
    have heta : Work.KMTContract.kmtEta
        ((2:ℝ)^((P.natDegree:ℝ) * (Work.Analysis.EndVar.logN N : ℝ)) * a) = 1 := by
      refine Work.KMTContract.kmtEta_one ?_
      rw [abs_of_nonneg (by positivity)]
      linarith [hsma]
    rw [heta, one_mul, norm_mul, norm_zpow, norm_ee, mul_one, norm_ofReal_mul,
      abs_of_nonneg (le_of_lt hapos), abs_of_nonneg (le_of_lt hcpos)]
  have hC₀ : ∀ y : ℝ, (1/2:ℝ) ≤ |y| →
      ‖φ y‖ ≤ (((N:ℝ)^P.natDegree)/2)^j := by
    intro y hy
    rw [hφdef, varphitildeNtj_eq, norm_mul, norm_mul, norm_zpow, norm_ee, mul_one]
    rw [norm_ofReal_mul, abs_of_nonneg (le_of_lt hcpos)]
    have h2 : ‖Work.KMTContract.kmtEta
        ((2:ℝ)^((P.natDegree:ℝ) * (Work.Analysis.EndVar.logN N : ℝ)) * y)‖ ≤ 1 :=
      Work.KMTContract.norm_kmtEta_le _
    have hjnn : 0 ≤ (↑N ^ P.natDegree * |y|) ^ j :=
      zpow_nonneg (mul_nonneg (by positivity) (abs_nonneg y)) j
    calc ((↑N ^ P.natDegree) * |y|) ^ j * ‖Work.KMTContract.kmtEta
            ((2:ℝ)^((P.natDegree:ℝ) * (Work.Analysis.EndVar.logN N : ℝ)) * y)‖
        ≤ ((↑N ^ P.natDegree) * |y|) ^ j * 1 := mul_le_mul_of_nonneg_left h2 hjnn
      _ = ((↑N ^ P.natDegree) * |y|) ^ j := mul_one _
      _ ≤ (((↑N ^ P.natDegree))/2)^j :=
          zpow_le_zpow_of_le_of_neg (by positivity)
            (by nlinarith [hy, pow_nonneg (show (0:ℝ) ≤ (N:ℝ) by positivity) P.natDegree])
            (by omega)
  exact symbol_not_integrable_of_key (Work.Analysis.IonescuWainger.iwArithFreqs ρ l) φ hcpos hj
    hvan hcont (by positivity) hnear hC₀ (zpow_nonneg (by positivity) j) h0A

theorem varphitildeNtj_Tle_eq_zero_self (P : Polynomial ℤ) (ρ : ℝ) (l N : ℕ) (j : ℤ)
    (hj : j ≤ -2) (t : ℝ) (g : ℤ → ℂ) :
    Work.KMTAreas.A7.Tle ρ l (Work.KMTPlan.A6.varphitildeNtj P N 0 j t) g = 0 := by
  set φ : ℝ → ℂ := Work.KMTPlan.A6.varphitildeNtj P N 0 j t with hφdef
  have hker : ∀ i : ℤ, Work.Analysis.IWMultiplier.iwKernel
      (Work.Analysis.IonescuWainger.iwSymbolSet (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
        (Work.Analysis.IonescuWainger.periodize φ)) i = 0 := by
    intro i
    by_cases htriv : N = 0 ∧ P.natDegree ≠ 0
    · have hφ0 : φ = fun _ : ℝ => 0 := by
        funext ξ
        rw [hφdef, varphitildeNtj_eq, htriv.1]
        simp only [Nat.cast_zero, zero_pow htriv.2, zero_mul, Complex.ofReal_zero]
        rw [zero_zpow j (by omega), zero_mul]
      have hΦ0 : Work.Analysis.IonescuWainger.iwSymbolSet
          (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
          (Work.Analysis.IonescuWainger.periodize φ) = fun _ => 0 := by
        rw [hφ0]
        funext ξ
        simp [Work.Analysis.IonescuWainger.iwSymbolSet_apply, periodize_zero]
      rw [hΦ0]
      simp [Work.Analysis.IWMultiplier.iwKernel, fourierCoeff]
    · exact iwKernel_eq_zero_of_not_integrable'
        (by
          rw [hφdef]
          exact varphitildeNtj_symbol_not_integrable P ρ l N j hj t htriv) i
  funext n
  rw [Tle_apply]
  have hzero : (fun i : ℤ => Work.Analysis.IWMultiplier.iwKernel
      (Work.Analysis.IonescuWainger.iwSymbolSet (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
        (Work.Analysis.IonescuWainger.periodize φ)) i * g (n - i))
      = fun _ => (0 : ℂ) := funext (fun i => by rw [hker i, zero_mul])
  rw [hzero]
  simp

end
end Work.KMTPlan.A6
