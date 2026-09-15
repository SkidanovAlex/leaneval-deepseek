import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Commons.MeasureTheory.Integral.subharmonic_convolution_ge

namespace Commons.MeasureTheory.Integral

open _root_.MeasureTheory _root_.Metric _root_.Set _root_.Filter _root_.Function
open scoped BigOperators ENNReal Topology RealInnerProductSpace InnerProductSpace

noncomputable section

set_option autoImplicit false

/-! ## Integrability of a product kernel times a locally bounded measurable function -/

private theorem integrable_prod_kernel_mul {ι : Type*} [Fintype ι] {k : ℂ → ℝ} {f : (ι → ℂ) → ℝ}
    (hk : Continuous k) (hkc : HasCompactSupport k) (hf : Measurable f)
    (hbdd : ∀ R : ℝ, ∃ M : ℝ, ∀ z : ι → ℂ, ‖z‖ ≤ R → |f z| ≤ M) :
    Integrable (fun s : ι → ℂ => (∏ j, k (s j)) * f s) := by
  classical
  obtain ⟨C, hC⟩ := hkc.exists_bound_of_continuousOn hk.continuousOn
  obtain ⟨B, hB⟩ := hkc.exists_bound_of_continuousOn continuous_norm.continuousOn
  have hB' : ∀ x ∈ tsupport k, ‖x‖ ≤ B := fun x hx => by simpa using hB x hx
  obtain ⟨M, hM⟩ := hbdd (max B 0)
  set c : ℝ := max C 0 ^ Fintype.card ι * max M 0 with hc
  set T : Set (ι → ℂ) := Metric.closedBall (0 : ι → ℂ) (max B 0) with hT
  set g : (ι → ℂ) → ℝ := fun s => c * T.indicator (fun _ => (1:ℝ)) s with hgdef
  have hg_int : Integrable g volume := by
    rw [hgdef]
    have hTfin : volume T ≠ ⊤ := ne_of_lt (isCompact_closedBall _ _).measure_lt_top
    have h1 : Integrable (T.indicator (fun _ : ι → ℂ => (1:ℝ))) volume := by
      rw [integrable_indicator_iff measurableSet_closedBall]
      exact integrableOn_const hTfin (by simp)
    exact h1.const_mul _
  have hmeas : Measurable (fun s : ι → ℂ => (∏ j, k (s j)) * f s) := by
    apply Measurable.mul
    · exact Finset.measurable_prod _ (fun j _ => hk.measurable.comp (measurable_pi_apply j))
    · exact hf
  have hbound : ∀ s : ι → ℂ, ‖(∏ j, k (s j)) * f s‖ ≤ g s := by
    intro s
    rw [hgdef]
    dsimp only
    by_cases hs : s ∈ T
    · rw [Set.indicator_of_mem hs]
      simp only [mul_one]
      have hfs : |f s| ≤ max M 0 := by
        have hs' : ‖s‖ ≤ max B 0 := by
          rw [hT, Metric.mem_closedBall, dist_zero_right] at hs; exact hs
        exact le_trans (hM s hs') (le_max_left _ _)
      have hki : ∀ i, |k (s i)| ≤ max C 0 := by
        intro i
        by_cases hi : s i ∈ tsupport k
        · exact le_trans (hC _ hi) (le_max_left _ _)
        · have hzero : k (s i) = 0 := by
            have h2 : s i ∉ Function.support k := fun h => hi (subset_tsupport k h)
            simpa [Function.mem_support] using h2
          rw [hzero, abs_zero]
          exact le_max_right _ _
      have hks : ‖(∏ j, k (s j))‖ ≤ max C 0 ^ Fintype.card ι := by
        rw [Real.norm_eq_abs, Finset.abs_prod]
        refine le_trans (Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => hki i)) ?_
        rw [Finset.prod_const, Finset.card_univ]
      rw [norm_mul]
      exact mul_le_mul hks hfs (abs_nonneg _) (by positivity)
    · rw [Set.indicator_of_notMem hs, mul_zero]
      have hzero : (∏ j, k (s j)) * f s = 0 := by
        have hnot : ¬ ∀ j, ‖s j‖ ≤ max B 0 := by
          intro h
          exact hs (by
            rw [hT, Metric.mem_closedBall, dist_zero_right]
            exact (pi_norm_le_iff_of_nonneg (le_max_right B 0)).mpr h)
        push Not at hnot
        obtain ⟨j, hj⟩ := hnot
        have hkj : k (s j) = 0 := by
          by_contra hne
          have hmem : s j ∈ tsupport k := subset_tsupport k (by simpa [Function.mem_support] using hne)
          exact absurd (le_trans (hB' _ hmem) (le_max_left B 0)) (not_le.mpr hj)
        rw [Finset.prod_eq_zero (Finset.mem_univ j) hkj, zero_mul]
      rw [hzero, norm_zero]
  exact Integrable.mono' hg_int hmeas.aestronglyMeasurable (Filter.Eventually.of_forall hbound)

/-- Complex (one-dimensional) version of the same integrability statement. -/
private theorem integrable_kernel_mul_complex {k : ℂ → ℝ} {f : ℂ → ℝ}
    (hk : Continuous k) (hkc : HasCompactSupport k) (hf : Measurable f)
    (hbdd : ∀ R : ℝ, ∃ M : ℝ, ∀ z : ℂ, ‖z‖ ≤ R → |f z| ≤ M) :
    Integrable (fun s : ℂ => f s * k s) volume := by
  classical
  obtain ⟨C, hC⟩ := hkc.exists_bound_of_continuousOn hk.continuousOn
  obtain ⟨B, hB⟩ := hkc.exists_bound_of_continuousOn continuous_norm.continuousOn
  have hB' : ∀ x ∈ tsupport k, ‖x‖ ≤ B := fun x hx => by simpa using hB x hx
  obtain ⟨M, hM⟩ := hbdd (max B 0)
  set c : ℝ := max M 0 * max C 0 with hc
  set T : Set ℂ := Metric.closedBall (0 : ℂ) (max B 0) with hT
  set g : ℂ → ℝ := fun s => c * T.indicator (fun _ => (1:ℝ)) s with hgdef
  have hg_int : Integrable g volume := by
    rw [hgdef]
    have hTfin : volume T ≠ ⊤ := ne_of_lt (isCompact_closedBall _ _).measure_lt_top
    have h1 : Integrable (T.indicator (fun _ : ℂ => (1:ℝ))) volume := by
      rw [integrable_indicator_iff measurableSet_closedBall]
      exact integrableOn_const hTfin (by simp)
    exact h1.const_mul _
  have hmeas : Measurable (fun s : ℂ => f s * k s) := hf.mul hk.measurable
  have hbound : ∀ s : ℂ, ‖f s * k s‖ ≤ g s := by
    intro s
    rw [hgdef]
    dsimp only
    by_cases hs : s ∈ T
    · rw [Set.indicator_of_mem hs]
      simp only [mul_one]
      have hgt : ‖s‖ ≤ max B 0 := by
        rw [hT, Metric.mem_closedBall, dist_zero_right] at hs; exact hs
      have hfs : ‖f s‖ ≤ max M 0 := by
        rw [Real.norm_eq_abs]
        exact le_trans (hM s hgt) (le_max_left _ _)
      have hks : ‖k s‖ ≤ max C 0 := by
        rw [Real.norm_eq_abs]
        by_cases hi : s ∈ tsupport k
        · exact le_trans (hC _ hi) (le_max_left _ _)
        · have hzero : k s = 0 := by
            have h2 : s ∉ Function.support k := fun h => hi (subset_tsupport k h)
            simpa [Function.mem_support] using h2
          rw [hzero, abs_zero]
          exact le_max_right _ _
      rw [norm_mul]
      exact mul_le_mul hfs hks (norm_nonneg _) (by positivity)
    · rw [Set.indicator_of_notMem hs, mul_zero]
      have hzero : f s * k s = 0 := by
        have hks0 : k s = 0 := by
          by_contra hne
          have hmem : s ∈ tsupport k := subset_tsupport k (by simpa [Function.mem_support] using hne)
          have hgt : max B 0 < ‖s‖ := by
            rw [hT, Metric.mem_closedBall, dist_zero_right] at hs
            exact not_le.mp hs
          exact absurd (le_trans (hB' _ hmem) (le_max_left B 0)) (not_le.mpr hgt)
        rw [hks0, mul_zero]
      rw [hzero, norm_zero]
  exact Integrable.mono' hg_int hmeas.aestronglyMeasurable (Filter.Eventually.of_forall hbound)

private theorem subharmonic_convolution_ge_cont {v k : ℂ → ℝ}
    (hk : Continuous k) (hk0 : ∀ s, 0 ≤ k s) (hkc : HasCompactSupport k)
    (hkrad : ∀ s c : ℂ, ‖c‖ = 1 → k (c * s) = k s)
    (hsmv : ∀ z w : ℂ, v z ≤ (∫ θ in (0 : ℝ)..(2 * Real.pi),
      v (z + Complex.exp (θ * Complex.I) * w)) / (2 * Real.pi))
    (hint : ∀ z : ℂ, MeasureTheory.Integrable (fun s : ℂ => v (z - s) * k s) MeasureTheory.volume)
    (z : ℂ) :
    v z * (∫ s : ℂ, k s) ≤ ∫ s : ℂ, v (z - s) * k s := by
  have hk_int : Integrable k volume := hk.integrable_of_hasCompactSupport hkc
  set G : ℂ → ℝ := fun s => v (z - s) * k s with hGdef
  have hG_int : Integrable G volume := hint z
  set φ : ℝ → ℝ := fun r => ∫ θ in Set.Ioo (-Real.pi) Real.pi,
      r * G ((r:ℂ) * Complex.exp (θ * Complex.I)) with hφdef
  set ψ : ℝ → ℝ := fun r => ∫ θ in Set.Ioo (-Real.pi) Real.pi,
      r * k ((r:ℂ) * Complex.exp (θ * Complex.I)) with hψdef
  set A : ℝ → ℝ := fun r => ∫ θ in Set.Ioo (-Real.pi) Real.pi,
      v (z - (r:ℂ) * Complex.exp (θ * Complex.I)) with hAdef
  have hGpol : (∫ s : ℂ, G s) = ∫ r in Set.Ioi (0:ℝ), φ r := by
    simpa only [hφdef] using integral_complex_eq_integral_angle_Ioo hG_int
  have hkpol : (∫ s : ℂ, k s) = ∫ r in Set.Ioi (0:ℝ), ψ r := by
    simpa only [hψdef] using integral_complex_eq_integral_angle_Ioo hk_int
  have hGint : IntegrableOn φ (Set.Ioi (0:ℝ)) volume :=
    integrableOn_integral_angle_Ioo hG_int
  have hkint : IntegrableOn ψ (Set.Ioi (0:ℝ)) volume :=
    integrableOn_integral_angle_Ioo hk_int
  -- explicit forms of `φ r` and `ψ r`
  have hφr : ∀ r : ℝ, φ r = r * (A r * k (r:ℂ)) := by
    intro r
    rw [hφdef, hAdef]
    simp only
    have hpt : ∀ θ : ℝ, r * G ((r:ℂ) * Complex.exp (θ * Complex.I))
        = r * (v (z - (r:ℂ) * Complex.exp (θ * Complex.I)) * k (r:ℂ)) := by
      intro θ
      rw [hGdef]
      simp only
      rw [radial_kernel_eval hkrad r θ]
    simp_rw [hpt]
    rw [integral_const_mul, integral_mul_const]
  have hψr : ∀ r : ℝ, ψ r = r * (k (r:ℂ) * (2 * Real.pi)) := by
    intro r
    rw [hψdef]
    simp only
    have hpt : ∀ θ : ℝ, r * k ((r:ℂ) * Complex.exp (θ * Complex.I)) = r * k (r:ℂ) := by
      intro θ; rw [radial_kernel_eval hkrad r θ]
    simp_rw [hpt]
    rw [integral_const_mul, setIntegral_const, volume_real_Ioo_negpi_pi, smul_eq_mul]
    ring
  have hAr : ∀ r : ℝ, 2 * Real.pi * v z ≤ A r := by
    intro r
    rw [hAdef]
    dsimp only
    have hconv : (∫ θ in Set.Ioo (-Real.pi) Real.pi,
          v (z - (r:ℂ) * Complex.exp (θ * Complex.I)))
        = ∫ θ in (-Real.pi)..Real.pi, v (z - (r:ℂ) * Complex.exp (θ * Complex.I)) := by
      rw [intervalIntegral.integral_of_le (a := -Real.pi) (b := Real.pi)
        (by linarith [Real.pi_pos])]
      exact setIntegral_congr_set Ioo_ae_eq_Ioc
    rw [hconv]
    exact angular_ge hsmv z r
  have hpoint : ∀ r ∈ Set.Ioi (0:ℝ), v z * ψ r ≤ φ r := by
    intro r hr
    have hrpos : 0 < r := hr
    have hknn : 0 ≤ k (r:ℂ) := hk0 _
    rw [hφr r, hψr r]
    have h1 : (2 * Real.pi * v z) * k (r:ℂ) ≤ A r * k (r:ℂ) :=
      mul_le_mul_of_nonneg_right (hAr r) hknn
    have h2 : r * ((2 * Real.pi * v z) * k (r:ℂ)) ≤ r * (A r * k (r:ℂ)) :=
      mul_le_mul_of_nonneg_left h1 (le_of_lt hrpos)
    calc v z * (r * (k (r:ℂ) * (2 * Real.pi)))
        = r * ((2 * Real.pi * v z) * k (r:ℂ)) := by ring
      _ ≤ r * (A r * k (r:ℂ)) := h2
  have hconst : IntegrableOn (fun r => v z * ψ r) (Set.Ioi (0:ℝ)) volume :=
    hkint.const_mul (v z)
  have hmono : ∫ r in Set.Ioi (0:ℝ), v z * ψ r ≤ ∫ r in Set.Ioi (0:ℝ), φ r := by
    apply integral_mono_ae
    · exact hconst
    · exact hGint
    · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with r hr
      exact hpoint r hr
  calc v z * (∫ s : ℂ, k s) = v z * ∫ r in Set.Ioi (0:ℝ), ψ r := by rw [hkpol]
    _ = ∫ r in Set.Ioi (0:ℝ), v z * ψ r := by rw [integral_const_mul]
    _ ≤ ∫ r in Set.Ioi (0:ℝ), φ r := hmono
    _ = ∫ s : ℂ, G s := hGpol.symm
    _ = ∫ s : ℂ, v (z - s) * k s := by rw [hGdef]



/-- Auxiliary induction statement. -/
private theorem conv_ge_aux (k : ℂ → ℝ)
    (hknn : ∀ s : ℂ, 0 ≤ k s) (hkcont : Continuous k) (hkcs : HasCompactSupport k)
    (hkrad : ∀ s c : ℂ, ‖c‖ = 1 → k (c * s) = k s) (hkmass : ∫ s : ℂ, k s = 1) :
    ∀ (d : ℕ) (u : (Fin d → ℂ) → ℝ),
      (∀ (z v : Fin d → ℂ), u z ≤
        (∫ θ in (0 : ℝ)..(2 * Real.pi), u (fun j => z j + Complex.exp (θ * Complex.I) * v j))
          / (2 * Real.pi)) →
      Measurable u →
      (∀ R : ℝ, ∃ M : ℝ, ∀ z : Fin d → ℂ, ‖z‖ ≤ R → |u z| ≤ M) →
      ∀ z : Fin d → ℂ,
        u z ≤ ∫ s : Fin d → ℂ, (∏ j, k (s j)) * u (fun j => z j - s j) := by
  intro d
  induction d with
  | zero =>
      intro u hsmv hu hloc z
      have hint : (∫ s : Fin 0 → ℂ, (∏ j, k (s j)) * u (fun j => z j - s j)) = u z := by
        rw [volume_pi, Measure.pi_of_empty (fun _ : Fin 0 => (volume : Measure ℂ))]
        rw [integral_dirac]
        simp only [Finset.univ_eq_empty, Finset.prod_empty, one_mul]
        congr 1
        funext j
        exact isEmptyElim j
      rw [hint]
  | succ d ih =>
      intro u hsmv hu hloc z
      let e : (Fin (d+1) → ℂ) ≃ᵐ ℂ × (Fin d → ℂ) :=
        MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d+1) => ℂ) 0
      have hp : MeasurePreserving (⇑e) volume volume :=
        volume_preserving_piFinSuccAbove (fun _ : Fin (d+1) => ℂ) 0
      have hcoe : ∀ (a : ℂ) (w : Fin d → ℂ), e.symm (a, w) = Fin.cons a w := by
        intro a w
        dsimp only [e]
        rw [MeasurableEquiv.piFinSuccAbove_symm_apply]
        funext j
        cases j using Fin.cases <;> simp [Fin.insertNthEquiv]
      have hΦ_int : Integrable (fun s : Fin (d+1) → ℂ =>
          (∏ j, k (s j)) * u (fun j => z j - s j)) volume := by
        refine integrable_prod_kernel_mul hkcont hkcs ?_ ?_
        · apply hu.comp
          fun_prop
        · intro R
          obtain ⟨M, hM⟩ := hloc (‖z‖ + R)
          refine ⟨M, fun s hs => hM _ ?_⟩
          calc ‖(fun j => z j - s j)‖ = ‖z - s‖ := rfl
            _ ≤ ‖z‖ + ‖s‖ := norm_sub_le _ _
            _ ≤ ‖z‖ + R := by linarith
      have hchange : (∫ s : Fin (d+1) → ℂ, (∏ j, k (s j)) * u (fun j => z j - s j))
          = ∫ p : ℂ × (Fin d → ℂ), (∏ j, k (e.symm p j)) * u (fun j => z j - e.symm p j) :=
        (hp.symm.integral_comp' _).symm
      have hp_int : Integrable (fun p : ℂ × (Fin d → ℂ) =>
          (∏ j, k (e.symm p j)) * u (fun j => z j - e.symm p j)) volume :=
        (hp.symm.integrable_comp_emb e.symm.measurableEmbedding).mpr hΦ_int
      have hp_int' : Integrable (fun p : ℂ × (Fin d → ℂ) =>
          (∏ j, k (e.symm p j)) * u (fun j => z j - e.symm p j)) (volume.prod volume) := by
        rw [Measure.volume_eq_prod] at hp_int
        exact hp_int
      have hinnerE : ∀ (a : ℂ) (w : Fin d → ℂ),
          (∏ j, k (e.symm (a,w) j)) * u (fun j => z j - e.symm (a,w) j)
            = (k a * ∏ i, k (w i)) * u (Fin.cons (z 0 - a) (fun i => z i.succ - w i)) := by
        intro a w
        rw [hcoe a w]
        congr 1
        · rw [Fin.prod_univ_succ]
          simp
        · congr 1
          funext j
          cases j using Fin.cases <;> simp
      have hFub : (∫ p : ℂ × (Fin d → ℂ), (∏ j, k (e.symm p j)) * u (fun j => z j - e.symm p j))
          = ∫ w : Fin d → ℂ, ∫ a : ℂ, (∏ j, k (e.symm (a,w) j)) * u (fun j => z j - e.symm (a,w) j) := by
        rw [Measure.volume_eq_prod]
        exact integral_prod_symm _ hp_int'
      have hcombined : (∫ s : Fin (d+1) → ℂ, (∏ j, k (s j)) * u (fun j => z j - s j))
          = ∫ w : Fin d → ℂ, ∫ a : ℂ, (k a * ∏ i, k (w i)) * u (Fin.cons (z 0 - a) (fun i => z i.succ - w i)) := by
        rw [hchange, hFub]
        simp_rw [hinnerE]
      have h1d : ∀ w : Fin d → ℂ,
          u (Fin.cons (z 0) (fun i => z i.succ - w i))
            ≤ ∫ a : ℂ, u (Fin.cons (z 0 - a) (fun i => z i.succ - w i)) * k a := by
        intro w
        let V : ℂ → ℝ := fun t => u (Fin.cons t (fun i => z i.succ - w i))
        have hVmeas : Measurable V := by
          change Measurable (fun t : ℂ => u (Fin.cons t (fun i => z i.succ - w i)))
          exact hu.comp (Continuous.finCons continuous_id continuous_const).measurable
        have hVbdd : ∀ (z0' : ℂ) (R : ℝ), ∃ M : ℝ, ∀ a : ℂ, ‖a‖ ≤ R → |V (z0' - a)| ≤ M := by
          intro z0' R
          obtain ⟨M, hM⟩ := hloc (max (‖z0'‖ + R) ‖(fun i : Fin d => z i.succ - w i)‖)
          refine ⟨M, fun a _ => hM _ ?_⟩
          refine (pi_norm_le_iff_of_nonneg ?_).mpr ?_
          · exact le_trans (norm_nonneg _) (le_max_right _ _)
          · intro j
            cases j using Fin.cases with
            | zero =>
                simp only [Fin.cons_zero]
                calc ‖z0' - a‖ ≤ ‖z0'‖ + ‖a‖ := norm_sub_le _ _
                  _ ≤ ‖z0'‖ + R := by linarith
                  _ ≤ max (‖z0'‖ + R) _ := le_max_left _ _
            | succ i =>
                simp only [Fin.cons_succ]
                exact le_trans (norm_le_pi_norm (fun i : Fin d => z i.succ - w i) i) (le_max_right _ _)
        have hVsmv : ∀ z' s : ℂ, V z' ≤ (∫ θ in (0:ℝ)..(2*Real.pi),
            V (z' + Complex.exp (θ * Complex.I) * s)) / (2 * Real.pi) := by
          intro z' s
          have h := hsmv (Fin.cons z' (fun i => z i.succ - w i)) (Fin.cons s (0 : Fin d → ℂ))
          have hfun : ∀ θ : ℝ,
              u (fun j : Fin (d+1) => (Fin.cons z' (fun i => z i.succ - w i) : Fin (d+1) → ℂ) j
                + Complex.exp (θ * Complex.I) * (Fin.cons s (0 : Fin d → ℂ) : Fin (d+1) → ℂ) j)
              = V (z' + Complex.exp (θ * Complex.I) * s) := by
            intro θ
            change u (fun j : Fin (d+1) => (Fin.cons z' (fun i => z i.succ - w i) : Fin (d+1) → ℂ) j
                + Complex.exp (θ * Complex.I) * (Fin.cons s (0 : Fin d → ℂ) : Fin (d+1) → ℂ) j)
              = u (Fin.cons (z' + Complex.exp (θ * Complex.I) * s) (fun i => z i.succ - w i) : Fin (d+1) → ℂ)
            congr 1
            funext j
            cases j using Fin.cases <;> simp
          have hcongr : (∫ θ in (0:ℝ)..(2*Real.pi),
              u (fun j : Fin (d+1) => (Fin.cons z' (fun i => z i.succ - w i) : Fin (d+1) → ℂ) j
                + Complex.exp (θ * Complex.I) * (Fin.cons s (0 : Fin d → ℂ) : Fin (d+1) → ℂ) j))
              = ∫ θ in (0:ℝ)..(2*Real.pi), V (z' + Complex.exp (θ * Complex.I) * s) :=
            intervalIntegral.integral_congr (fun _ _ => hfun _)
          rw [hcongr] at h
          simpa only [V] using h
        have hVint : ∀ z0' : ℂ, Integrable (fun a : ℂ => V (z0' - a) * k a) volume := by
          intro z0'
          refine integrable_kernel_mul_complex hkcont hkcs ?_ ?_
          · exact hVmeas.comp (by fun_prop)
          · intro R
            obtain ⟨M, hM⟩ := hVbdd z0' R
            exact ⟨M, fun a ha => hM a ha⟩
        have hkey := subharmonic_convolution_ge_cont hkcont hknn hkcs hkrad hVsmv hVint (z 0)
        rw [hkmass, mul_one] at hkey
        simpa only [V] using hkey
      have hu'meas : Measurable (fun c : Fin d → ℂ => u (Fin.cons (z 0) c)) :=
        hu.comp (Continuous.finCons continuous_const continuous_id).measurable
      have hu'bdd : ∀ R : ℝ, ∃ M : ℝ, ∀ c : Fin d → ℂ, ‖c‖ ≤ R → |u (Fin.cons (z 0) c)| ≤ M := by
        intro R
        obtain ⟨M, hM⟩ := hloc (max ‖z 0‖ R)
        refine ⟨M, fun c hc => hM _ ?_⟩
        refine (pi_norm_le_iff_of_nonneg ?_).mpr ?_
        · exact le_trans (norm_nonneg _) (le_max_left _ _)
        · intro j
          cases j using Fin.cases with
          | zero => simpa using le_max_left ‖z 0‖ R
          | succ i => exact le_trans (norm_le_pi_norm c i) (le_trans hc (le_max_right _ _))
      have hu'smv : ∀ (c v' : Fin d → ℂ),
          u (Fin.cons (z 0) c) ≤ (∫ θ in (0:ℝ)..(2*Real.pi),
            u (Fin.cons (z 0) (fun i => c i + Complex.exp (θ * Complex.I) * v' i))) / (2 * Real.pi) := by
        intro c v'
        have h := hsmv (Fin.cons (z 0) c) (Fin.cons (0:ℂ) v')
        have hfun : ∀ θ : ℝ, u (fun j : Fin (d+1) => (Fin.cons (z 0) c : Fin (d+1) → ℂ) j
            + Complex.exp (θ * Complex.I) * (Fin.cons (0:ℂ) v' : Fin (d+1) → ℂ) j)
            = u (Fin.cons (z 0) (fun i => c i + Complex.exp (θ * Complex.I) * v' i)) := by
          intro θ; congr 1; funext j; cases j using Fin.cases <;> simp
        have hcongr : (∫ θ in (0:ℝ)..(2*Real.pi), u (fun j : Fin (d+1) => (Fin.cons (z 0) c : Fin (d+1) → ℂ) j
              + Complex.exp (θ * Complex.I) * (Fin.cons (0:ℂ) v' : Fin (d+1) → ℂ) j))
            = ∫ θ in (0:ℝ)..(2*Real.pi),
                u (Fin.cons (z 0) (fun i => c i + Complex.exp (θ * Complex.I) * v' i)) :=
          intervalIntegral.integral_congr (fun θ _ => hfun θ)
        rw [hcongr] at h
        exact h
      have hih := ih (fun c : Fin d → ℂ => u (Fin.cons (z 0) c)) hu'smv hu'meas hu'bdd
        (fun i : Fin d => z i.succ)
      have hL_int : Integrable (fun w : Fin d → ℂ =>
          (∏ i, k (w i)) * u (Fin.cons (z 0) (fun i => z i.succ - w i))) volume := by
        refine integrable_prod_kernel_mul hkcont hkcs ?_ ?_
        · apply hu.comp
          fun_prop
        · intro R
          obtain ⟨M, hM⟩ := hu'bdd (‖(fun i : Fin d => z i.succ)‖ + R)
          refine ⟨M, fun w hw => hM _ ?_⟩
          calc ‖(fun i => z i.succ - w i)‖ = ‖(fun i : Fin d => z i.succ) - w‖ := rfl
            _ ≤ ‖(fun i : Fin d => z i.succ)‖ + ‖w‖ := norm_sub_le _ _
            _ ≤ ‖(fun i : Fin d => z i.succ)‖ + R := by linarith
      have hprod_int : Integrable (fun p : ℂ × (Fin d → ℂ) =>
          (k p.1 * ∏ i, k (p.2 i)) * u (Fin.cons (z 0 - p.1) (fun i => z i.succ - p.2 i)))
          (volume.prod volume) :=
        hp_int'.congr (Filter.Eventually.of_forall (fun p => hinnerE p.1 p.2))
      have hR_int : Integrable (fun w : Fin d → ℂ => ∫ a : ℂ,
          (k a * ∏ i, k (w i)) * u (Fin.cons (z 0 - a) (fun i => z i.succ - w i))) volume :=
        hprod_int.integral_prod_right
      have hpw : ∀ w : Fin d → ℂ,
          (∏ i, k (w i)) * u (Fin.cons (z 0) (fun i => z i.succ - w i))
            ≤ ∫ a : ℂ, (k a * ∏ i, k (w i)) * u (Fin.cons (z 0 - a) (fun i => z i.succ - w i)) := by
        intro w
        have hc : 0 ≤ ∏ i, k (w i) := Finset.prod_nonneg (fun i _ => hknn _)
        have h1 := h1d w
        have h2 : (∏ i, k (w i)) * u (Fin.cons (z 0) (fun i => z i.succ - w i))
            ≤ (∏ i, k (w i)) * ∫ a : ℂ, u (Fin.cons (z 0 - a) (fun i => z i.succ - w i)) * k a :=
          mul_le_mul_of_nonneg_left h1 hc
        have h3 : (∏ i, k (w i)) * (∫ a : ℂ, u (Fin.cons (z 0 - a) (fun i => z i.succ - w i)) * k a)
            = ∫ a : ℂ, (k a * ∏ i, k (w i)) * u (Fin.cons (z 0 - a) (fun i => z i.succ - w i)) := by
          rw [← integral_const_mul]
          apply integral_congr_ae
          filter_upwards with a
          ring
        exact h2.trans (le_of_eq h3)
      have hmono : (∫ w : Fin d → ℂ, (∏ i, k (w i)) * u (Fin.cons (z 0) (fun i => z i.succ - w i)))
          ≤ ∫ w : Fin d → ℂ, ∫ a : ℂ, (k a * ∏ i, k (w i)) * u (Fin.cons (z 0 - a) (fun i => z i.succ - w i)) :=
        integral_mono_ae hL_int hR_int (Filter.Eventually.of_forall hpw)
      have hz_eq : u (Fin.cons (z 0) (fun i => z i.succ)) = u z := by
        congr 1
        exact Fin.cons_self_tail z
      calc u z = u (Fin.cons (z 0) (fun i => z i.succ)) := hz_eq.symm
        _ ≤ ∫ w : Fin d → ℂ, (∏ i, k (w i)) * u (Fin.cons (z 0) (fun i => z i.succ - w i)) := hih
        _ ≤ ∫ w : Fin d → ℂ, ∫ a : ℂ, (k a * ∏ i, k (w i)) * u (Fin.cons (z 0 - a) (fun i => z i.succ - w i)) := hmono
        _ = ∫ s : Fin (d+1) → ℂ, (∏ j, k (s j)) * u (fun j => z j - s j) := hcombined.symm


theorem convolution_ge_of_subMeanValue {d : ℕ}
    {u : (Fin d → ℂ) → ℝ} {k : ℂ → ℝ}
    (hknn : ∀ s : ℂ, 0 ≤ k s) (hkcont : Continuous k) (hkcs : HasCompactSupport k)
    (hkrad : ∀ s c : ℂ, ‖c‖ = 1 → k (c * s) = k s)
    (hkmass : ∫ s : ℂ, k s = 1)
    (hsmv : ∀ (z v : Fin d → ℂ), u z ≤
      (∫ θ in (0 : ℝ)..(2 * Real.pi), u (fun j => z j + Complex.exp (θ * Complex.I) * v j))
        / (2 * Real.pi))
    (hu : Measurable u)
    (hloc : ∀ R : ℝ, ∃ M : ℝ, ∀ z : Fin d → ℂ, ‖z‖ ≤ R → |u z| ≤ M)
    (z : Fin d → ℂ) :
    u z ≤ ∫ s : Fin d → ℂ, (∏ j, k (s j)) * u (fun j => z j - s j) :=
  conv_ge_aux k hknn hkcont hkcs hkrad hkmass d u hsmv hu hloc z

end

end Commons.MeasureTheory.Integral