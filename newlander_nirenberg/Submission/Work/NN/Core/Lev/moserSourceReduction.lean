import Mathlib
import Submission.Work.NN.Core.CnPert
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.NN.Core.Lev2.PowCacc
import Submission.Work.NN.Core.Lev.nnGradBoundPoint
import Submission.Work.NN.Core.Lev.moserSourceAux
import Submission.Work.NN.Core.Lev.srcWLipschitz

namespace Work.NN.Core.Lev

open scoped NNReal ENNReal ContDiff Topology
open MeasureTheory Set

noncomputable section

/-- The Wirtinger energy density `Σ_j (‖∂_j u‖² + ‖∂̄_j u‖²)`. -/
abbrev nnSrcEnergy {n : ℕ} (u : Work.NN.Core.Cn n → ℂ) (z : Work.NN.Core.Cn n) : ℝ :=
  ∑ j, (‖Work.CR.Flat.dCoord j u z‖^2 + ‖Work.CR.Flat.dbarCoord j u z‖^2)

lemma nnSrcEnergy_nonneg {n : ℕ} (u : Work.NN.Core.Cn n → ℂ) (z : Work.NN.Core.Cn n) :
    0 ≤ nnSrcEnergy u z :=
  Finset.sum_nonneg fun j _ => by positivity

/-- The Fréchet derivative of a function of compact support vanishes off its topological support. -/
lemma nnSrc_fderiv_eq_zero_of_notMem_tsupport {n : ℕ} {φ : Work.NN.Core.Cn n → ℝ}
    {z : Work.NN.Core.Cn n} (hz : z ∉ tsupport φ) : fderiv ℝ φ z = 0 := by
  have h : φ =ᶠ[𝓝 z] 0 := by
    filter_upwards [(isClosed_tsupport φ).isOpen_compl.mem_nhds hz] with w hw
    exact Function.notMem_support.mp fun hws => hw (subset_closure hws)
  rw [Filter.EventuallyEq.fderiv_eq h]
  simp

lemma nnSrc_mem_tsupport_of_fderiv_ne_zero {n : ℕ} {φ : Work.NN.Core.Cn n → ℝ}
    {z : Work.NN.Core.Cn n} (h : fderiv ℝ φ z ≠ 0) : z ∈ tsupport φ :=
  by_contra fun hz => h (nnSrc_fderiv_eq_zero_of_notMem_tsupport hz)

/-- A function continuous on a compact set and supported in it is integrable. -/
lemma nnSrc_integrable_of_continuousOn_compact_of_support {n : ℕ} {K : Set (Work.NN.Core.Cn n)}
    (hK : IsCompact K) {F : Work.NN.Core.Cn n → ℝ} (hF : ContinuousOn F K)
    (hsupp : Function.support F ⊆ K) : Integrable F volume := by
  have hmeas : MeasurableSet K := hK.isClosed.measurableSet
  have h1 : IntegrableOn F K volume := hF.integrableOn_compact hK
  have h2 : Integrable (K.indicator F) volume := h1.integrable_indicator hmeas
  have h3 : K.indicator F = F := by
    funext z
    by_cases hz : z ∈ K
    · rw [Set.indicator_of_mem hz]
    · have hz0 : F z = 0 := Function.notMem_support.mp fun h => hz (hsupp h)
      rw [Set.indicator_of_notMem hz, hz0]
  rwa [h3] at h2

/-- Continuity of `z ↦ max ‖u z‖ Λ` on a set where `u` is continuous. -/
lemma nnSrc_continuousOn_max_norm {n : ℕ} {s : Set (Work.NN.Core.Cn n)}
    {u : Work.NN.Core.Cn n → ℂ} (hu : ContinuousOn u s) (Λ : ℝ) :
    ContinuousOn (fun z => max ‖u z‖ Λ) s := by
  have h : ContinuousOn (fun z => ‖u z‖ ⊔ Λ) s := hu.norm.sup continuousOn_const
  simpa only [max_def] using h

/-- The Wirtinger energy density is continuous on the polydisc where `u` is `C¹`. -/
lemma nnSrc_continuousOn_energy {n : ℕ} {ρ : Fin n → ℝ} {u : Work.NN.Core.Cn n → ℂ}
    (hu : ContDiffOn ℝ 1 u (Work.CR.Flat.polydisc 0 ρ)) :
    ContinuousOn (nnSrcEnergy u) (Work.CR.Flat.polydisc 0 ρ) := by
  have hfd : ContinuousOn (fderiv ℝ u) (Work.CR.Flat.polydisc 0 ρ) :=
    hu.continuousOn_fderiv_of_isOpen (Work.CR.Flat.isOpen_polydisc 0 ρ) le_rfl
  have hdc : ∀ j, ContinuousOn (fun z => Work.CR.Flat.dCoord j u z)
      (Work.CR.Flat.polydisc 0 ρ) := by
    intro j
    have h1 : ContinuousOn (fun z => fderiv ℝ u z (Pi.single j (1 : ℂ)))
        (Work.CR.Flat.polydisc 0 ρ) := hfd.clm_apply continuousOn_const
    have h2 : ContinuousOn (fun z => fderiv ℝ u z (Pi.single j (Complex.I : ℂ)))
        (Work.CR.Flat.polydisc 0 ρ) := hfd.clm_apply continuousOn_const
    have h3 : ContinuousOn (fun z => (1/2 : ℂ) * fderiv ℝ u z (Pi.single j (1 : ℂ))
        - (1/2 : ℂ) * Complex.I * fderiv ℝ u z (Pi.single j (Complex.I : ℂ)))
        (Work.CR.Flat.polydisc 0 ρ) :=
      ((continuousOn_const.mul h1).sub (continuousOn_const.mul h2))
    have heq : (fun z => Work.CR.Flat.dCoord j u z)
        = fun z => (1/2 : ℂ) * fderiv ℝ u z (Pi.single j (1 : ℂ))
            - (1/2 : ℂ) * Complex.I * fderiv ℝ u z (Pi.single j (Complex.I : ℂ)) := by
      funext z; simp [Work.CR.Flat.dCoord]; ring
    rw [heq]; exact h3
  have hdbc : ∀ j, ContinuousOn (fun z => Work.CR.Flat.dbarCoord j u z)
      (Work.CR.Flat.polydisc 0 ρ) := by
    intro j
    have h1 : ContinuousOn (fun z => fderiv ℝ u z (Pi.single j (1 : ℂ)))
        (Work.CR.Flat.polydisc 0 ρ) := hfd.clm_apply continuousOn_const
    have h2 : ContinuousOn (fun z => fderiv ℝ u z (Pi.single j (Complex.I : ℂ)))
        (Work.CR.Flat.polydisc 0 ρ) := hfd.clm_apply continuousOn_const
    have h3 : ContinuousOn (fun z => (1/2 : ℂ) * fderiv ℝ u z (Pi.single j (1 : ℂ))
        + (1/2 : ℂ) * Complex.I * fderiv ℝ u z (Pi.single j (Complex.I : ℂ)))
        (Work.CR.Flat.polydisc 0 ρ) :=
      ((continuousOn_const.mul h1).add (continuousOn_const.mul h2))
    have heq : (fun z => Work.CR.Flat.dbarCoord j u z)
        = fun z => (1/2 : ℂ) * fderiv ℝ u z (Pi.single j (1 : ℂ))
            + (1/2 : ℂ) * Complex.I * fderiv ℝ u z (Pi.single j (Complex.I : ℂ)) := by
      funext z; simp [Work.CR.Flat.dbarCoord]; ring
    rw [heq]; exact h3
  exact continuousOn_finsetSum _ fun j _ =>
    ((hdc j).norm.pow 2).add ((hdbc j).norm.pow 2)

/-- Pointwise bound of the differential of the shifted modulus by the Wirtinger energy. -/
lemma nnSrc_exists_norm_fderiv_srcW_sq_le {n : ℕ} (hn : 0 < n) :
    ∃ C : ℝ, 0 < C ∧ ∀ {u : Work.NN.Core.Cn n → ℂ} {Λ : ℝ} {z : Work.NN.Core.Cn n},
      DifferentiableAt ℝ u z →
      ‖fderiv ℝ (srcW u Λ) z‖^2 ≤ C * nnSrcEnergy u z := by
  obtain ⟨C, hC0, hC⟩ := nnGradBoundPoint hn
  refine ⟨C, hC0, ?_⟩
  intro u Λ z hu
  have h1 : ‖fderiv ℝ (srcW u Λ) z‖ ≤ ‖fderiv ℝ u z‖ := norm_fderiv_srcW_le hu
  calc ‖fderiv ℝ (srcW u Λ) z‖^2 ≤ ‖fderiv ℝ u z‖^2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ C * nnSrcEnergy u z := hC u z

theorem moserSourceReduction {n : ℕ} (hn : 0 < n) {ρ ρ' : Fin n → ℝ}
    (hρ0 : ∀ j, 0 < ρ j) (hρ'ρ : ∀ j, ρ' j < ρ j) {A₀ : ℝ} (hA₀ : 0 < A₀) :
    ∃ A₀' : ℝ, 0 < A₀' ∧ ∀ {Λ : ℝ}, 0 ≤ Λ → ∀ u : Work.NN.Core.Cn n → ℂ,
      ContDiffOn ℝ 1 u (Work.CR.Flat.polydisc 0 ρ) →
        Work.NN.Core.Lev2.HasPowCaccSource ρ A₀ Λ u →
      ∃ K : NNReal, LipschitzOnWith K (fun z => max ‖u z‖ Λ) (Work.CR.Flat.polydisc 0 ρ') ∧
        (∀ φ : Work.NN.Core.Cn n → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
          tsupport φ ⊆ Work.CR.Flat.polydisc 0 ρ' → (∀ z, 0 ≤ φ z) →
          ∫ z in Work.CR.Flat.polydisc 0 ρ',
              (φ z)^2 * ‖fderiv ℝ (fun w => max ‖u w‖ Λ) z‖^2
            ≤ A₀' * ((∫ z in Work.CR.Flat.polydisc 0 ρ',
                      ‖fderiv ℝ φ z‖^2 * (max ‖u z‖ Λ)^2)
                  + ∫ z in Work.CR.Flat.polydisc 0 ρ', (φ z)^2 * (max ‖u z‖ Λ)^2)) := by
  obtain ⟨Cg, hCg0, hCg⟩ := nnSrc_exists_norm_fderiv_srcW_sq_le hn
  refine ⟨Cg * A₀, mul_pos hCg0 hA₀, ?_⟩
  intro Λ hΛ u hu hH
  obtain ⟨K, hK⟩ := srcWLipschitz hρ'ρ hu Λ
  refine ⟨K, hK, ?_⟩
  intro φ hφsm hφcs hφts hφnn
  -- domains
  have hρ'ρle : ∀ j, ρ' j ≤ ρ j := fun j => le_of_lt (hρ'ρ j)
  have hsub : Work.CR.Flat.polydisc 0 ρ' ⊆ Work.CR.Flat.polydisc 0 ρ :=
    Work.CR.Flat.polydisc_mono hρ'ρle
  have hφtsρ : tsupport φ ⊆ Work.CR.Flat.polydisc 0 ρ := hφts.trans hsub
  have hmeasρ : MeasurableSet (Work.CR.Flat.polydisc 0 ρ) :=
    (Work.CR.Flat.isOpen_polydisc 0 ρ).measurableSet
  have hmeasρ' : MeasurableSet (Work.CR.Flat.polydisc 0 ρ') :=
    (Work.CR.Flat.isOpen_polydisc 0 ρ').measurableSet
  have hEcontρ : ContinuousOn (nnSrcEnergy u) (Work.CR.Flat.polydisc 0 ρ) :=
    nnSrc_continuousOn_energy hu
  -- integrability of the energy integrand
  have hIntψE : Integrable (fun z => (φ z)^2 * nnSrcEnergy u z) volume := by
    refine nnSrc_integrable_of_continuousOn_compact_of_support hφcs.isCompact ?_ ?_
    · exact (hφsm.continuous.continuousOn.pow 2).mul (hEcontρ.mono hφtsρ)
    · intro z hz
      rw [Function.mem_support] at hz
      exact subset_closure (Function.mem_support.mpr fun h0 => hz (by rw [h0]; ring))
  -- continuity of the shifted modulus on tsupport φ
  have hWcont : ContinuousOn (fun z => (max ‖u z‖ Λ)^2) (tsupport φ) :=
    ((nnSrc_continuousOn_max_norm (hu.continuousOn.mono hφtsρ) Λ).pow 2)
  have hIntGradW : Integrable (fun z => ‖fderiv ℝ φ z‖^2 * (max ‖u z‖ Λ)^2) volume := by
    refine nnSrc_integrable_of_continuousOn_compact_of_support hφcs.isCompact ?_ ?_
    · exact (((hφsm.continuous_fderiv (by simp)).continuousOn.norm.pow 2)).mul hWcont
    · intro z hz
      rw [Function.mem_support] at hz
      exact nnSrc_mem_tsupport_of_fderiv_ne_zero fun h0 => hz (by rw [h0]; simp)
  have hIntφW : Integrable (fun z => (φ z)^2 * (max ‖u z‖ Λ)^2) volume := by
    refine nnSrc_integrable_of_continuousOn_compact_of_support hφcs.isCompact ?_ ?_
    · exact (hφsm.continuous.continuousOn.pow 2).mul hWcont
    · intro z hz
      rw [Function.mem_support] at hz
      exact subset_closure (Function.mem_support.mpr fun h0 => hz (by rw [h0]; ring))
  -- pointwise gradient bound
  have hgrad : ∀ z ∈ Work.CR.Flat.polydisc 0 ρ',
      ‖fderiv ℝ (fun w => max ‖u w‖ Λ) z‖^2 ≤ Cg * nnSrcEnergy u z := by
    intro z hz
    have hzP : z ∈ Work.CR.Flat.polydisc 0 ρ := hsub hz
    have hd : DifferentiableAt ℝ u z :=
      (hu.contDiffAt ((Work.CR.Flat.isOpen_polydisc 0 ρ).mem_nhds hzP)).differentiableAt
        (by norm_num)
    exact hCg hd
  -- Step 1: bound the LHS by the constant times the level-1 energy integral
  have hstep1 : ∫ z in Work.CR.Flat.polydisc 0 ρ',
        (φ z)^2 * ‖fderiv ℝ (fun w => max ‖u w‖ Λ) z‖^2
      ≤ Cg * ∫ z in Work.CR.Flat.polydisc 0 ρ', (φ z)^2 * nnSrcEnergy u z := by
    have hb : ∫ z in Work.CR.Flat.polydisc 0 ρ',
          (φ z)^2 * ‖fderiv ℝ (fun w => max ‖u w‖ Λ) z‖^2
        ≤ ∫ z in Work.CR.Flat.polydisc 0 ρ', (φ z)^2 * (Cg * nnSrcEnergy u z) := by
      refine MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun z => mul_nonneg (sq_nonneg _) (sq_nonneg _)) ?_ ?_
      · have h0 : Integrable (fun z => (φ z)^2 * (Cg * nnSrcEnergy u z)) volume :=
          (hIntψE.const_mul Cg).congr (Filter.Eventually.of_forall fun z => by ring)
        exact h0.mono_measure MeasureTheory.Measure.restrict_le_self
      · show ∀ᵐ z ∂(MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 ρ')),
            (φ z)^2 * ‖fderiv ℝ (fun w => max ‖u w‖ Λ) z‖^2
              ≤ (φ z)^2 * (Cg * nnSrcEnergy u z)
        rw [MeasureTheory.ae_restrict_iff' hmeasρ']
        exact Filter.Eventually.of_forall fun z hz =>
          mul_le_mul_of_nonneg_left (hgrad z hz) (sq_nonneg _)
    calc _ ≤ ∫ z in Work.CR.Flat.polydisc 0 ρ', (φ z)^2 * (Cg * nnSrcEnergy u z) := hb
      _ = ∫ z in Work.CR.Flat.polydisc 0 ρ', Cg * ((φ z)^2 * nnSrcEnergy u z) :=
          MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => by ring)
      _ = Cg * ∫ z in Work.CR.Flat.polydisc 0 ρ', (φ z)^2 * nnSrcEnergy u z :=
          MeasureTheory.integral_const_mul Cg _
  -- Step 2: enlarge the domain `polydisc 0 ρ' ⊆ polydisc 0 ρ`
  have hstep2 : ∫ z in Work.CR.Flat.polydisc 0 ρ', (φ z)^2 * nnSrcEnergy u z
      ≤ ∫ z in Work.CR.Flat.polydisc 0 ρ, (φ z)^2 * nnSrcEnergy u z := by
    refine MeasureTheory.setIntegral_mono_set ?_ ?_ ?_
    · exact hIntψE.mono_measure MeasureTheory.Measure.restrict_le_self
    · exact Filter.Eventually.of_forall fun z => mul_nonneg (sq_nonneg _) (nnSrcEnergy_nonneg u z)
    · filter_upwards with z hz
      exact hsub hz
  -- Step 3: the level-`1` instance of the power Caccioppoli hypothesis
  have hstep3 : ∫ z in Work.CR.Flat.polydisc 0 ρ, (φ z)^2 * nnSrcEnergy u z
      ≤ A₀ * ((∫ z in Work.CR.Flat.polydisc 0 ρ, ‖fderiv ℝ φ z‖^2 * ‖u z‖^2)
              + ∫ z in Work.CR.Flat.polydisc 0 ρ, (φ z)^2 * Λ^2) := by
    have h := hH 1 le_rfl φ hφsm hφcs hφtsρ hφnn
    simp only [Nat.cast_one, one_pow, Nat.sub_self, pow_zero, one_mul, mul_one, pow_one] at h
    simpa only [nnSrcEnergy] using h
  -- Step 4: replace `‖u z‖` and `Λ` by the shifted modulus `max ‖u z‖ Λ`
  have hstep4a : ∫ z in Work.CR.Flat.polydisc 0 ρ, ‖fderiv ℝ φ z‖^2 * ‖u z‖^2
      ≤ ∫ z in Work.CR.Flat.polydisc 0 ρ, ‖fderiv ℝ φ z‖^2 * (max ‖u z‖ Λ)^2 := by
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun z => mul_nonneg (sq_nonneg _) (sq_nonneg _)) ?_ ?_
    · exact hIntGradW.mono_measure MeasureTheory.Measure.restrict_le_self
    · exact Filter.Eventually.of_forall fun z =>
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (le_max_left _ _) 2)
          (sq_nonneg _)
  have hstep4b : ∫ z in Work.CR.Flat.polydisc 0 ρ, (φ z)^2 * Λ^2
      ≤ ∫ z in Work.CR.Flat.polydisc 0 ρ, (φ z)^2 * (max ‖u z‖ Λ)^2 := by
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun z => mul_nonneg (sq_nonneg _) (sq_nonneg _)) ?_ ?_
    · exact hIntφW.mono_measure MeasureTheory.Measure.restrict_le_self
    · exact Filter.Eventually.of_forall fun z =>
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hΛ (le_max_right _ _) 2) (sq_nonneg _)
  -- Step 5: shrink the domain back -- the integrands vanish off `tsupport φ ⊆ polydisc 0 ρ'`
  have hstep5a : ∫ z in Work.CR.Flat.polydisc 0 ρ, ‖fderiv ℝ φ z‖^2 * (max ‖u z‖ Λ)^2
      = ∫ z in Work.CR.Flat.polydisc 0 ρ', ‖fderiv ℝ φ z‖^2 * (max ‖u z‖ Λ)^2 := by
    refine MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hmeasρ hsub ?_
    intro z hz
    rw [Set.mem_sdiff] at hz
    have hzt : z ∉ tsupport φ := fun hz' => hz.2 (hφts hz')
    rw [nnSrc_fderiv_eq_zero_of_notMem_tsupport hzt]
    simp
  have hstep5b : ∫ z in Work.CR.Flat.polydisc 0 ρ, (φ z)^2 * (max ‖u z‖ Λ)^2
      = ∫ z in Work.CR.Flat.polydisc 0 ρ', (φ z)^2 * (max ‖u z‖ Λ)^2 := by
    refine MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hmeasρ hsub ?_
    intro z hz
    rw [Set.mem_sdiff] at hz
    have hzt : z ∉ tsupport φ := fun hz' => hz.2 (hφts hz')
    have hφz : φ z = 0 := Function.notMem_support.mp fun hz' => hzt (subset_closure hz')
    rw [hφz]
    simp
  -- assembly
  have hY : (∫ z in Work.CR.Flat.polydisc 0 ρ, ‖fderiv ℝ φ z‖^2 * ‖u z‖^2)
        + ∫ z in Work.CR.Flat.polydisc 0 ρ, (φ z)^2 * Λ^2
      ≤ (∫ z in Work.CR.Flat.polydisc 0 ρ', ‖fderiv ℝ φ z‖^2 * (max ‖u z‖ Λ)^2)
        + ∫ z in Work.CR.Flat.polydisc 0 ρ', (φ z)^2 * (max ‖u z‖ Λ)^2 := by
    have hm : (∫ z in Work.CR.Flat.polydisc 0 ρ, ‖fderiv ℝ φ z‖^2 * (max ‖u z‖ Λ)^2)
        + ∫ z in Work.CR.Flat.polydisc 0 ρ, (φ z)^2 * (max ‖u z‖ Λ)^2
        = (∫ z in Work.CR.Flat.polydisc 0 ρ', ‖fderiv ℝ φ z‖^2 * (max ‖u z‖ Λ)^2)
          + ∫ z in Work.CR.Flat.polydisc 0 ρ', (φ z)^2 * (max ‖u z‖ Λ)^2 := by
      rw [hstep5a, hstep5b]
    exact le_trans (add_le_add hstep4a hstep4b) (le_of_eq hm)
  calc ∫ z in Work.CR.Flat.polydisc 0 ρ',
        (φ z)^2 * ‖fderiv ℝ (fun w => max ‖u w‖ Λ) z‖^2
      ≤ Cg * ∫ z in Work.CR.Flat.polydisc 0 ρ', (φ z)^2 * nnSrcEnergy u z := hstep1
    _ ≤ Cg * ∫ z in Work.CR.Flat.polydisc 0 ρ, (φ z)^2 * nnSrcEnergy u z :=
        mul_le_mul_of_nonneg_left hstep2 hCg0.le
    _ ≤ Cg * (A₀ * ((∫ z in Work.CR.Flat.polydisc 0 ρ, ‖fderiv ℝ φ z‖^2 * ‖u z‖^2)
              + ∫ z in Work.CR.Flat.polydisc 0 ρ, (φ z)^2 * Λ^2)) :=
        mul_le_mul_of_nonneg_left hstep3 hCg0.le
    _ = (Cg * A₀) * ((∫ z in Work.CR.Flat.polydisc 0 ρ, ‖fderiv ℝ φ z‖^2 * ‖u z‖^2)
              + ∫ z in Work.CR.Flat.polydisc 0 ρ, (φ z)^2 * Λ^2) := by ring
    _ ≤ (Cg * A₀) * ((∫ z in Work.CR.Flat.polydisc 0 ρ', ‖fderiv ℝ φ z‖^2 * (max ‖u z‖ Λ)^2)
              + ∫ z in Work.CR.Flat.polydisc 0 ρ', (φ z)^2 * (max ‖u z‖ Λ)^2) :=
        mul_le_mul_of_nonneg_left hY (mul_nonneg hCg0.le hA₀.le)

end

end Work.NN.Core.Lev
