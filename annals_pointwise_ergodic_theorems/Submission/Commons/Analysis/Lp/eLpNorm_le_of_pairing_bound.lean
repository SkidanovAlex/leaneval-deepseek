import Mathlib.Order.CompletePartialOrder
import Submission.Commons.Analysis.Lp.ofReal_integral_norm_rpow_eq_lintegral_enorm_rpow
import Submission.Commons.Analysis.InnerProductSpace.inner_smul_rpow_smul_self
import Submission.Commons.Analysis.InnerProductSpace.norm_smul_rpow_smul_self
import Submission.Commons.Analysis.Integral.integrable_of_bound_of_support_subset

namespace Commons.Analysis.Lp

open MeasureTheory
open scoped ENNReal

/-- The `ℒᵖ` seminorm of a function on `ℝ` is the supremum of the `ℒᵖ` seminorms of its
restrictions to the increasing family of intervals `[-n, n]`. -/
private theorem eLpNorm_eq_iSup_indicator_Icc_aux {H : Type*} [NormedAddCommGroup H]
    (h : ℝ → H) {p : ℝ} (hp : 0 < p) (hsm : MeasureTheory.AEStronglyMeasurable h MeasureTheory.volume) :
    MeasureTheory.eLpNorm h (ENNReal.ofReal p) MeasureTheory.volume =
      ⨆ n : ℕ, MeasureTheory.eLpNorm ((Set.Icc (-(n:ℝ)) (n:ℝ)).indicator h)
        (ENNReal.ofReal p) MeasureTheory.volume := by
  have hP0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp).ne'
  have hPtop : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hf_ae : ∀ n : ℕ, AEMeasurable (fun x : ℝ =>
      ‖(Set.Icc (-(n:ℝ)) (n:ℝ)).indicator h x‖ₑ ^ p) MeasureTheory.volume :=
    fun n => ((hsm.indicator measurableSet_Icc).enorm).pow_const p
  have hf_mono : Monotone (fun n : ℕ => fun x : ℝ =>
      ‖(Set.Icc (-(n:ℝ)) (n:ℝ)).indicator h x‖ₑ ^ p) := by
    intro n m hnm x
    refine ENNReal.rpow_le_rpow ?_ hp.le
    by_cases hx : x ∈ Set.Icc (-(n:ℝ)) (n:ℝ)
    · have hxm : x ∈ Set.Icc (-(m:ℝ)) (m:ℝ) :=
        ⟨le_trans (neg_le_neg (by exact_mod_cast hnm)) hx.1, le_trans hx.2 (by exact_mod_cast hnm)⟩
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hxm]
    · rw [Set.indicator_of_notMem hx]; simp
  have hmct : ∫⁻ x, (⨆ n : ℕ, ‖(Set.Icc (-(n:ℝ)) (n:ℝ)).indicator h x‖ₑ ^ p)
        ∂(MeasureTheory.volume : Measure ℝ)
      = ⨆ n : ℕ, ∫⁻ x, ‖(Set.Icc (-(n:ℝ)) (n:ℝ)).indicator h x‖ₑ ^ p
        ∂(MeasureTheory.volume : Measure ℝ) :=
    lintegral_iSup' hf_ae (Filter.Eventually.of_forall fun x n m hnm => hf_mono hnm x)
  have hsup : (fun x : ℝ => ⨆ n : ℕ, ‖(Set.Icc (-(n:ℝ)) (n:ℝ)).indicator h x‖ₑ ^ p)
      = fun x : ℝ => ‖h x‖ₑ ^ p := by
    funext x
    refine le_antisymm (iSup_le fun n => ENNReal.rpow_le_rpow (enorm_indicator_le_enorm_self h x) hp.le) ?_
    obtain ⟨N, hN⟩ : ∃ N : ℕ, x ∈ Set.Icc (-(N:ℝ)) (N:ℝ) := by
      refine ⟨⌈|x|⌉₊, ?_⟩
      have hx : |x| ≤ ((⌈|x|⌉₊ : ℕ) : ℝ) := Nat.le_ceil |x|
      simpa using (abs_le.mp hx)
    calc ‖h x‖ₑ ^ p = ‖(Set.Icc (-(N:ℝ)) (N:ℝ)).indicator h x‖ₑ ^ p := by
          rw [Set.indicator_of_mem hN]
      _ ≤ ⨆ n : ℕ, ‖(Set.Icc (-(n:ℝ)) (n:ℝ)).indicator h x‖ₑ ^ p :=
          le_iSup (fun n : ℕ => ‖(Set.Icc (-(n:ℝ)) (n:ℝ)).indicator h x‖ₑ ^ p) N
  have hleft : MeasureTheory.eLpNorm h (ENNReal.ofReal p) MeasureTheory.volume
      = (∫⁻ x, ‖h x‖ₑ ^ p ∂(MeasureTheory.volume : Measure ℝ)) ^ (1 / p) := by
    rw [MeasureTheory.eLpNorm_eq_eLpNorm' hP0 hPtop hsm, ENNReal.toReal_ofReal hp.le]; rfl
  have hright : ∀ n : ℕ, ∫⁻ x, ‖(Set.Icc (-(n:ℝ)) (n:ℝ)).indicator h x‖ₑ ^ p
        ∂(MeasureTheory.volume : Measure ℝ)
      = (MeasureTheory.eLpNorm ((Set.Icc (-(n:ℝ)) (n:ℝ)).indicator h)
          (ENNReal.ofReal p) MeasureTheory.volume) ^ p := by
    intro n
    rw [show (∫⁻ x, ‖(Set.Icc (-(n:ℝ)) (n:ℝ)).indicator h x‖ₑ ^ p
          ∂(MeasureTheory.volume : Measure ℝ))
        = MeasureTheory.eLpNorm' ((Set.Icc (-(n:ℝ)) (n:ℝ)).indicator h) p MeasureTheory.volume ^ p
        from lintegral_rpow_enorm_eq_rpow_eLpNorm' hp]
    rw [MeasureTheory.eLpNorm_eq_eLpNorm' hP0 hPtop (hsm.indicator measurableSet_Icc),
      ENNReal.toReal_ofReal hp.le]
  calc MeasureTheory.eLpNorm h (ENNReal.ofReal p) MeasureTheory.volume
      = (∫⁻ x, ‖h x‖ₑ ^ p ∂(MeasureTheory.volume : Measure ℝ)) ^ (1 / p) := hleft
    _ = (⨆ n : ℕ, ∫⁻ x, ‖(Set.Icc (-(n:ℝ)) (n:ℝ)).indicator h x‖ₑ ^ p
          ∂(MeasureTheory.volume : Measure ℝ)) ^ (1 / p) := by
          congr 1; rw [← hsup, hmct]
    _ = ⨆ n : ℕ, (∫⁻ x, ‖(Set.Icc (-(n:ℝ)) (n:ℝ)).indicator h x‖ₑ ^ p
          ∂(MeasureTheory.volume : Measure ℝ)) ^ (1 / p) :=
          OrderIso.map_iSup (ENNReal.orderIsoRpow (1 / p) (by positivity)) _
    _ = ⨆ n : ℕ, MeasureTheory.eLpNorm ((Set.Icc (-(n:ℝ)) (n:ℝ)).indicator h)
          (ENNReal.ofReal p) MeasureTheory.volume := by
          refine iSup_congr fun n => ?_
          rw [hright n, show (1 : ℝ) / p = p⁻¹ by rw [one_div],
            ENNReal.rpow_rpow_inv hp.ne']

/-- Core duality step: if `h` is bounded, almost everywhere strongly measurable and supported
on a set `S` of finite measure, then one can build an integrable testing function `g`, again
supported on `S`, whose `L^{p'}` norm is at most `1` and whose pairing against `h` dominates the
`L^p` norm of `h`. -/
theorem exists_dual_pairing_of_finite_support
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (h : α → H) {p B : ℝ} (hp : 1 < p) (hB : 0 ≤ B)
    (hsm : AEStronglyMeasurable h μ) (hbdd : ∀ x, ‖h x‖ ≤ B)
    (S : Set α) (hS : MeasurableSet S) (hSfin : μ S ≠ ⊤)
    (hsupp : ∀ x, x ∉ S → h x = 0) :
    ∃ g : α → H, Integrable g μ ∧ (∀ x, x ∉ S → g x = 0) ∧
      eLpNorm g (ENNReal.ofReal (p / (p - 1))) μ ≤ 1 ∧
      eLpNorm h (ENNReal.ofReal p) μ ≤ enorm (∫ x, inner ℂ (h x) (g x) ∂μ) := by
  classical
  have hp_pos : 0 < p := lt_trans zero_lt_one hp
  have hp_ne : p ≠ 0 := hp_pos.ne'
  have hp1_pos : 0 < p - 1 := by linarith
  have hq_pos : 0 < p / (p - 1) := div_pos hp_pos hp1_pos
  have hq_ne : p / (p - 1) ≠ 0 := hq_pos.ne'
  -- Integrability of the `p`-th power of the norm.
  have hφ_sm : AEStronglyMeasurable (fun x => ‖h x‖ ^ p) μ :=
    (Real.continuous_rpow_const hp_pos.le).comp_aestronglyMeasurable hsm.norm
  have hφ_supp : ∀ x, x ∉ S → ‖h x‖ ^ p = 0 := by
    intro x hx
    rw [hsupp x hx, norm_zero, Real.zero_rpow hp_ne]
  have hφ_int : Integrable (fun x => ‖h x‖ ^ p) μ :=
    Commons.Analysis.Integral.integrable_of_bound_of_support_subset hS hSfin hφ_sm
      (fun x => by
        rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) p)]
        exact Real.rpow_le_rpow (norm_nonneg _) (hbdd x) hp_pos.le)
      hφ_supp
  set a : ℝ := ∫ x, ‖h x‖ ^ p ∂μ with ha
  have ha_nonneg : 0 ≤ a := by
    rw [ha]
    exact integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) p
  set c : ℝ := a ^ (1 / p - 1) with hc
  have hc_nonneg : 0 ≤ c := by
    rw [hc]; exact Real.rpow_nonneg ha_nonneg _
  -- The dual vector field.
  set G : α → H := fun x => c • ((‖h x‖ ^ (p - 2)) • h x) with hG
  have hψ_sm : AEMeasurable (fun x => ‖h x‖ ^ (p - 2)) μ :=
    ((by fun_prop : Measurable fun t : ℝ => t ^ (p - 2))).comp_aemeasurable hsm.norm.aemeasurable
  have hG_sm : AEStronglyMeasurable G μ := by
    rw [hG]
    exact (hψ_sm.aestronglyMeasurable.smul hsm).const_smul c
  have hG_bound : ∀ x, ‖G x‖ ≤ c * B ^ (p - 1) := by
    intro x
    rw [hG, Commons.Analysis.InnerProductSpace.norm_smul_rpow_smul_self (h x) hp hc_nonneg]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (norm_nonneg _) (hbdd x) hp1_pos.le) hc_nonneg
  have hG_supp : ∀ x, x ∉ S → G x = 0 := by
    intro x hx
    have hGx : G x = c • ((‖h x‖ ^ (p - 2)) • h x) := by rw [hG]
    rw [hGx, hsupp x hx]
    simp
  have hG_int : Integrable G μ :=
    Commons.Analysis.Integral.integrable_of_bound_of_support_subset hS hSfin hG_sm hG_bound hG_supp
  -- Pointwise norm identity for the indicator.
  have hnorm_pt : ∀ x, ‖S.indicator G x‖ = c * ‖h x‖ ^ (p - 1) := by
    intro x
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx, hG]
      exact Commons.Analysis.InnerProductSpace.norm_smul_rpow_smul_self (h x) hp hc_nonneg
    · rw [Set.indicator_of_notMem hx, hsupp x hx, norm_zero,
          Real.zero_rpow (by linarith : p - 1 ≠ 0)]
      ring
  -- Pointwise inner-product identity for the indicator.
  have hinner_pt : ∀ x, inner ℂ (h x) (S.indicator G x) = ((c * ‖h x‖ ^ p : ℝ) : ℂ) := by
    intro x
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx, hG]
      exact Commons.Analysis.InnerProductSpace.inner_smul_rpow_smul_self (h x) hp
    · rw [Set.indicator_of_notMem hx, hsupp x hx]
      simp [Real.zero_rpow hp_ne]
  -- Integrability of `c * ‖h ·‖ ^ p`.
  have hψ_int : Integrable (fun x => c * ‖h x‖ ^ p) μ := hφ_int.const_mul c
  -- The pairing equals `c * a`.
  have hInt : ∫ x, inner ℂ (h x) (S.indicator G x) ∂μ = ((c * a : ℝ) : ℂ) := by
    calc ∫ x, inner ℂ (h x) (S.indicator G x) ∂μ
        = ∫ x, ((c * ‖h x‖ ^ p : ℝ) : ℂ) ∂μ := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun x => hinner_pt x
      _ = ((∫ x, c * ‖h x‖ ^ p ∂μ : ℝ) : ℂ) := integral_ofReal
      _ = ((c * ∫ x, ‖h x‖ ^ p ∂μ : ℝ) : ℂ) := by rw [integral_const_mul]
      _ = ((c * a : ℝ) : ℂ) := by rw [← ha]
  -- Rewriting `eLpNorm h (ofReal p)`.
  have hrec : eLpNorm h (ENNReal.ofReal p) μ = ENNReal.ofReal (a ^ (1 / p)) := by
    have h1 : eLpNorm h (ENNReal.ofReal p) μ = (∫⁻ x, ‖h x‖ₑ ^ p ∂μ) ^ (1 / p) := by
      rw [eLpNorm_eq_eLpNorm' (ENNReal.ofReal_pos.mpr hp_pos).ne' ENNReal.ofReal_ne_top hsm,
          ENNReal.toReal_ofReal hp_pos.le]
      rfl
    rw [h1, ← Commons.Analysis.Lp.ofReal_integral_norm_rpow_eq_lintegral_enorm_rpow h hp_pos hφ_int,
        ENNReal.ofReal_rpow_of_nonneg ha_nonneg (by positivity)]
  -- `c * a = a ^ (1/p)`.
  have hca : c * a = a ^ (1 / p) := by
    rw [hc]
    have h1p_ne : (1 : ℝ) / p - 1 + 1 ≠ 0 := by
      have : (1 : ℝ) / p - 1 + 1 = 1 / p := by ring
      rw [this]
      exact div_ne_zero one_ne_zero hp_ne
    have hh := Real.rpow_add' (x := a) ha_nonneg (y := 1 / p - 1) (z := 1) h1p_ne
    rw [Real.rpow_one] at hh
    rw [show 1 / p - 1 + 1 = 1 / p by ring] at hh
    rw [← hh]
  -- Arithmetic bound: `c ^ (p/(p-1)) * a ≤ 1`.
  have hcqa : c ^ (p / (p - 1)) * a ≤ 1 := by
    rcases eq_or_lt_of_le ha_nonneg with h0 | hpos
    · have hc0 : c = 0 := by
        rw [hc, ← h0]
        exact Real.zero_rpow (by
          have h : (1:ℝ) / p < 1 := by rw [div_lt_one hp_pos]; linarith
          linarith)
      simp [hc0, ← h0, Real.zero_rpow hq_ne]
    · have hce : c ^ (p / (p - 1)) = a⁻¹ := by
        rw [hc, ← Real.rpow_mul ha_nonneg (1 / p - 1) (p / (p - 1))]
        have hexp : (1 / p - 1) * (p / (p - 1)) = -1 := by
          field_simp <;> ring
        rw [hexp, Real.rpow_neg_one]
      rw [hce, inv_mul_cancel₀ hpos.ne']
  -- The `L^{p'}` norm bound.
  have hLq : eLpNorm (S.indicator G) (ENNReal.ofReal (p / (p - 1))) μ ≤ 1 := by
    rw [eLpNorm_eq_eLpNorm' (ENNReal.ofReal_pos.mpr hq_pos).ne' ENNReal.ofReal_ne_top
        (hG_sm.indicator hS),
        ENNReal.toReal_ofReal hq_pos.le]
    have hlin : ∫⁻ x, ‖S.indicator G x‖ₑ ^ (p / (p - 1)) ∂μ
        = ENNReal.ofReal (c ^ (p / (p - 1)) * a) := by
      have key_pt : ∀ x, ‖S.indicator G x‖ₑ ^ (p / (p - 1))
          = ENNReal.ofReal (c ^ (p / (p - 1))) * ‖h x‖ₑ ^ p := by
        intro x
        have hbase : (0 : ℝ) ≤ c * ‖h x‖ ^ (p - 1) :=
          mul_nonneg hc_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
        have hexp : (p - 1) * (p / (p - 1)) = p := by field_simp
        calc ‖S.indicator G x‖ₑ ^ (p / (p - 1))
            = ENNReal.ofReal (c * ‖h x‖ ^ (p - 1)) ^ (p / (p - 1)) := by
                rw [← ofReal_norm, hnorm_pt x]
          _ = ENNReal.ofReal ((c * ‖h x‖ ^ (p - 1)) ^ (p / (p - 1))) :=
                ENNReal.ofReal_rpow_of_nonneg hbase hq_pos.le
          _ = ENNReal.ofReal (c ^ (p / (p - 1)) * ‖h x‖ ^ p) := by
                rw [Real.mul_rpow hc_nonneg (Real.rpow_nonneg (norm_nonneg _) _),
                    ← Real.rpow_mul (norm_nonneg (h x)) (p - 1) (p / (p - 1)), hexp]
          _ = ENNReal.ofReal (c ^ (p / (p - 1))) * ‖h x‖ₑ ^ p := by
                rw [ENNReal.ofReal_mul (Real.rpow_nonneg hc_nonneg _),
                    ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg (h x)) hp_pos.le,
                    ofReal_norm (h x)]
      rw [lintegral_congr key_pt]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      rw [← Commons.Analysis.Lp.ofReal_integral_norm_rpow_eq_lintegral_enorm_rpow h hp_pos hφ_int]
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hc_nonneg _)]
    rw [show eLpNorm' (S.indicator G) (p / (p - 1)) μ
          = (∫⁻ x, ‖S.indicator G x‖ₑ ^ (p / (p - 1)) ∂μ) ^ (1 / (p / (p - 1))) from rfl,
        hlin]
    calc (ENNReal.ofReal (c ^ (p / (p - 1)) * a)) ^ (1 / (p / (p - 1)))
        ≤ (ENNReal.ofReal 1) ^ (1 / (p / (p - 1))) :=
          ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hcqa) (by positivity)
      _ = 1 := by rw [ENNReal.ofReal_one, ENNReal.one_rpow]
  refine ⟨S.indicator G, hG_int.indicator hS, ?_, hLq, ?_⟩
  · intro x hx
    exact Set.indicator_of_notMem hx G
  · rw [hInt, hrec, ← hca]
    have henorm : ‖((c * a : ℝ) : ℂ)‖ₑ = ENNReal.ofReal (c * a) := by
      rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg hc_nonneg ha_nonneg)]
    rw [henorm]

/-- Duality bound for the `L^p` norm on `ℝ`: if every integrable test function `g` satisfies
`|∫ ⟪h x, g x⟫| ≤ E ‖g‖_{p'}`, then `‖h‖_p ≤ E`. -/
theorem eLpNorm_le_of_pairing_bound {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (h : ℝ → H) {p : ℝ} (hp : 1 < p) (hsm : MeasureTheory.AEStronglyMeasurable h MeasureTheory.volume) (hbdd : ∃ B : ℝ, ∀ x : ℝ, ‖h x‖ ≤ B) (E : ENNReal) (hE : E ≠ ⊤) (hpair : ∀ g : ℝ → H, MeasureTheory.Integrable g MeasureTheory.volume → enorm (∫ x : ℝ, inner ℂ (h x) (g x)) ≤ E * MeasureTheory.eLpNorm g (ENNReal.ofReal (p / (p - 1)))) : MeasureTheory.eLpNorm h (ENNReal.ofReal p) ≤ E := by
  classical
  have hp_pos : 0 < p := lt_trans zero_lt_one hp
  obtain ⟨B, hB⟩ := hbdd
  have hB0 : 0 ≤ B := le_trans (norm_nonneg (h 0)) (hB 0)
  have hbound : ∀ n : ℕ,
      MeasureTheory.eLpNorm ((Set.Icc (-(n:ℝ)) (n:ℝ)).indicator h) (ENNReal.ofReal p)
        MeasureTheory.volume ≤ E := by
    intro n
    set S : Set ℝ := Set.Icc (-(n:ℝ)) (n:ℝ) with hSdef
    have hS : MeasurableSet S := measurableSet_Icc
    have hSfin : MeasureTheory.volume S ≠ ⊤ := by
      rw [hSdef, Real.volume_Icc]; exact ENNReal.ofReal_ne_top
    have hsm_ind : AEStronglyMeasurable (S.indicator h) MeasureTheory.volume :=
      hsm.indicator hS
    have hbdd_ind : ∀ x, ‖S.indicator h x‖ ≤ B := by
      intro x
      by_cases hx : x ∈ S
      · rw [Set.indicator_of_mem hx]; exact hB x
      · rw [Set.indicator_of_notMem hx, norm_zero]; exact hB0
    have hsupp_ind : ∀ x, x ∉ S → S.indicator h x = 0 :=
      fun x hx => Set.indicator_of_notMem hx h
    obtain ⟨g, hg_int, hg_supp, hg_lin, hpair_le⟩ :=
      exists_dual_pairing_of_finite_support (S.indicator h) hp hB0 hsm_ind hbdd_ind S hS hSfin
        hsupp_ind
    have h_eq : ∫ x, inner ℂ (h x) (g x) ∂MeasureTheory.volume
        = ∫ x, inner ℂ (S.indicator h x) (g x) ∂MeasureTheory.volume := by
      apply integral_congr_ae
      filter_upwards with x
      by_cases hx : x ∈ S
      · rw [Set.indicator_of_mem hx]
      · rw [Set.indicator_of_notMem hx, hg_supp x hx]
        simp
    calc MeasureTheory.eLpNorm (S.indicator h) (ENNReal.ofReal p) MeasureTheory.volume
        ≤ enorm (∫ x, inner ℂ (S.indicator h x) (g x) ∂MeasureTheory.volume) := hpair_le
      _ = enorm (∫ x, inner ℂ (h x) (g x) ∂MeasureTheory.volume) := by rw [← h_eq]
      _ ≤ E * MeasureTheory.eLpNorm g (ENNReal.ofReal (p / (p - 1))) MeasureTheory.volume :=
            hpair g hg_int
      _ ≤ E * 1 := mul_le_mul_of_nonneg_left hg_lin (by positivity)
      _ = E := mul_one E
  rw [eLpNorm_eq_iSup_indicator_Icc_aux h hp_pos hsm]
  exact iSup_le hbound

end Commons.Analysis.Lp