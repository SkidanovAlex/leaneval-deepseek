import Mathlib
import Submission.Work.GM.Affine.FarMass_defs
import Submission.Work.GM.Affine.region_II_vocab
import Submission.Work.GM.Affine.bsum_far_weight_bound

/-!
# `Work.GM.Affine.far_mass_eq`

The far mass of GM §9, region II,

`FarMass K f M₂ M₃ = Σ_ℓ ∫_{|τ| > 2} ‖H_ℓ(τ)‖² ‖ψ̂₁(τ)‖² dτ`,  `H_ℓ(τ) = Bsum f M₂ (ℓ + τ/M₃)`,

is rewritten by the substitution `τ = M₃ t` in each term and Tonelli's theorem (all terms
non-negative) as a single integral over the *far lattice*:

`FarMass K f M₂ M₃ = M₃ ∫_{|t| > 2/M₃} (Σ_ℓ ‖Bsum f M₂ (ℓ + t)‖²) ‖ψ̂₁(M₃ t)‖² dt`.

The proof is carried out in `ℝ≥0∞`: the per-`ℓ` substitution is `far_inner_eq` followed by a
translation, and the exchange of the `ℓ`-sum with the integral is `lintegral_tsum`.  The passage
back to Bochner integrals uses `integral_eq_lintegral_of_nonneg_ae` and `ENNReal.tsum_toReal_eq`;
the one analytic input is the a.e. summability of `ℓ ↦ ‖Bsum f M₂ (ℓ + t)‖²`, which follows from
`Bsum f M₂ ∈ L²` (`Plancherel`, `fm_lintegral_Bsum_sq_ne_top`) by comparing the sum over the lattice
with the `L²`-mass over a fundamental domain.
-/

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform ENNReal

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.GM.Affine

noncomputable section

/-! ## Elementary helpers -/

/-- Membership in `Ioi c ∪ Iio (-c)` is `c < |u|`. -/
lemma fm_mem_far_iff_abs (c u : ℝ) : u ∈ (Set.Ioi c ∪ Set.Iio (-c)) ↔ c < |u| := by
  rw [Set.mem_union, Set.mem_Ioi, Set.mem_Iio, lt_abs]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (by linarith)
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (by linarith)

/-- `SuppHyp C₀ f` with `C₀ ≥ 1` gives compact support. -/
lemma fm_hasCompactSupport_of_suppHyp {C₀ : ℝ} (hC₀ : 1 ≤ C₀) {f : ℝ → ℝ}
    (hsup : SuppHyp C₀ f) : HasCompactSupport f := by
  refine HasCompactSupport.of_support_subset_isCompact (K := Set.Icc (1 / C₀) C₀) isCompact_Icc ?_
  intro u hu
  rw [Function.mem_support] at hu
  exact hsup u hu

/-- `‖Fhat f ξ‖ ≤ ∫ u, ‖f u‖`. -/
lemma fm_norm_Fhat_le_integral_norm (f : ℝ → ℝ) (ξ : ℝ) :
    ‖Fhat f ξ‖ ≤ ∫ u, ‖(f u : ℝ)‖ := by
  rw [Fhat_eq_integral']
  calc ‖∫ u : ℝ, (f u : ℂ) * efun (-(u * ξ))‖
      ≤ ∫ u : ℝ, ‖(f u : ℂ) * efun (-(u * ξ))‖ := norm_integral_le_integral_norm _
    _ = ∫ u : ℝ, ‖(f u : ℝ)‖ := by
        refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
        change ‖(f u : ℂ) * efun (-(u * ξ))‖ = ‖(f u : ℝ)‖
        rw [norm_mul, norm_efun, mul_one, Complex.norm_real]

/-- A uniform bound for `Bsum f M₂`. -/
lemma fm_norm_Bsum_le_const {C₀ M₂ : ℝ} (hC₀ : 1 ≤ C₀) {f : ℝ → ℝ} (hf : Continuous f)
    (hsup : SuppHyp C₀ f) (hM₂ : 0 < M₂) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u, ‖Bsum f M₂ u‖ ≤ C := by
  refine ⟨∑ m ∈ R2 M₂, (m : ℝ) * (∫ v, ‖(f v : ℝ)‖), ?_, ?_⟩
  · refine Finset.sum_nonneg (fun m hm => mul_nonneg ?_ ?_)
    · have := R2_pos' hm; linarith
    · exact integral_nonneg (fun v => norm_nonneg _)
  · intro u
    rw [Bsum]
    calc ‖∑ m ∈ R2 M₂, ((m : ℝ) : ℂ) * Fhat f ((m : ℝ) * u)‖
        ≤ ∑ m ∈ R2 M₂, ‖((m : ℝ) : ℂ) * Fhat f ((m : ℝ) * u)‖ := norm_sum_le _ _
      _ = ∑ m ∈ R2 M₂, (m : ℝ) * ‖Fhat f ((m : ℝ) * u)‖ := by
          refine Finset.sum_congr rfl (fun m hm => ?_)
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (R2_pos' hm)]
      _ ≤ ∑ m ∈ R2 M₂, (m : ℝ) * (∫ v, ‖(f v : ℝ)‖) := by
          refine Finset.sum_le_sum (fun m hm => ?_)
          exact mul_le_mul_of_nonneg_left (fm_norm_Fhat_le_integral_norm f _) (le_of_lt (R2_pos' hm))

/-- The `L²`-mass of `ψ̂₁` is finite in `ℝ≥0∞`. -/
lemma fm_lintegral_psi1hat_sq_ne_top (K : ℝ) :
    (∫⁻ τ, ENNReal.ofReal (‖psi1hat K τ‖ ^ 2)) ≠ ⊤ := by
  have hint := psi1hat_sq_integrable K
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall (fun τ => sq_nonneg _))]
  exact ENNReal.ofReal_ne_top

/-- The `L²`-mass of `Bsum f M₂` is finite in `ℝ≥0∞`. -/
lemma fm_lintegral_Bsum_sq_ne_top {C₀ M₂ : ℝ} (hC₀ : 1 ≤ C₀) (hM₂ : 0 < M₂) {f : ℝ → ℝ}
    (hf : Continuous f) (hsup : SuppHyp C₀ f) :
    (∫⁻ u, ENNReal.ofReal (‖Bsum f M₂ u‖ ^ 2)) ≠ ⊤ := by
  have hHcont : Continuous (Hprof f M₂) := Hprof_continuous hf M₂
  have hHcs : HasCompactSupport (Hprof f M₂) := Hprof_hasCompactSupport hsup hC₀ hM₂.le
  have hcontC : Continuous (fun u : ℝ => ((Hprof f M₂ u : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp hHcont
  have hcsC : HasCompactSupport (fun u : ℝ => ((Hprof f M₂ u : ℝ) : ℂ)) :=
    hHcs.comp_left (g := fun z : ℝ => (z : ℂ)) (by simp)
  have hfin := lintegral_ofReal_normSq_ne_top (fun u : ℝ => ((Hprof f M₂ u : ℝ) : ℂ))
    hcontC hcsC
  have hpl := lintegral_ofReal_fourier_sq_eq (fun u : ℝ => ((Hprof f M₂ u : ℝ) : ℂ))
    hcontC hcsC
  have hpt : ∀ u : ℝ, ENNReal.ofReal (‖Bsum f M₂ u‖ ^ 2)
      = ENNReal.ofReal (‖𝓕 (fun u : ℝ => ((Hprof f M₂ u : ℝ) : ℂ)) u‖ ^ 2) := by
    intro u
    rw [Bsum_eq_Fhat_Hprof hf hsup hC₀ hM₂ u]
    rfl
  rw [lintegral_congr hpt, hpl]
  exact hfin

/-- Translation on half-open unit intervals. -/
lemma fm_lintegral_Ico_comp_add {F : ℝ → ENNReal} (c a b : ℝ) :
    (∫⁻ u in Set.Ico (a + c) (b + c), F u) = ∫⁻ t in Set.Ico a b, F (c + t) := by
  have key : ∀ u : ℝ, (Set.Ico (a + c) (b + c)).indicator F u
      = (Set.Ico a b).indicator (fun t => F (c + t)) (u - c) := by
    intro u
    have hmem : u - c ∈ Set.Ico a b ↔ u ∈ Set.Ico (a + c) (b + c) := by
      simp only [Set.mem_Ico]; constructor <;> intro h <;> constructor <;> linarith
    by_cases h : u ∈ Set.Ico (a + c) (b + c)
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hmem.mpr h)]
      congr 1; ring
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun hh => h (hmem.mp hh))]
  have h1 : (∫⁻ u in Set.Ico (a + c) (b + c), F u)
      = ∫⁻ u, (Set.Ico (a + c) (b + c)).indicator F u :=
    (MeasureTheory.lintegral_indicator measurableSet_Ico F).symm
  have h2 : (∫⁻ t in Set.Ico a b, F (c + t))
      = ∫⁻ u, ((Set.Ico a b).indicator (fun t => F (c + t)) (u - c)) := by
    rw [MeasureTheory.lintegral_sub_right_eq_self
      ((Set.Ico a b).indicator (fun t => F (c + t))) c]
    exact (MeasureTheory.lintegral_indicator measurableSet_Ico (fun t => F (c + t))).symm
  rw [h1, h2]
  exact MeasureTheory.lintegral_congr key

/-- The half-open unit intervals `Ico (k+ℓ) (k+ℓ+1)`, `ℓ ∈ ℤ`, partition the line. -/
lemma fm_iUnion_Ico_shift_eq_univ (k : ℤ) :
    (⋃ ℓ : ℤ, Set.Ico (((k + ℓ : ℤ) : ℝ)) (((k + ℓ : ℤ) : ℝ) + 1)) = Set.univ := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_Ico, Set.mem_univ, iff_true]
  refine ⟨⌊x⌋ - k, ?_, ?_⟩
  · have h1 : ((⌊x⌋ : ℤ) : ℝ) ≤ x := Int.floor_le x
    have : (((k + (⌊x⌋ - k) : ℤ)) : ℝ) = ((⌊x⌋ : ℤ) : ℝ) := by congr 1; ring
    rw [this]; exact h1
  · have h2 : x < ((⌊x⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one x
    have : (((k + (⌊x⌋ - k) : ℤ)) : ℝ) = ((⌊x⌋ : ℤ) : ℝ) := by congr 1; ring
    rw [this]; exact h2

/-- The half-open unit intervals `Ico k (k+1)`, `k ∈ ℤ`, partition the line. -/
lemma fm_iUnion_Ico_int_eq_univ : (⋃ k : ℤ, Set.Ico ((k:ℝ)) ((k:ℝ)+1)) = Set.univ := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_Ico, Set.mem_univ, iff_true]
  exact ⟨⌊x⌋, Int.floor_le x, Int.lt_floor_add_one x⟩

/-- The half-open unit intervals `Ico (k+ℓ) (k+ℓ+1)` are pairwise disjoint. -/
lemma fm_pairwise_disjoint_Ico_shift (k : ℤ) :
    Pairwise (Function.onFun Disjoint
      (fun ℓ : ℤ => Set.Ico (((k + ℓ : ℤ) : ℝ)) (((k + ℓ : ℤ) : ℝ) + 1))) := by
  intro ℓ ℓ' hne
  simp only [Function.onFun]
  rw [Set.disjoint_left]
  intro x hx hx'
  rw [Set.mem_Ico] at hx hx'
  rcases lt_trichotomy (ℓ : ℝ) (ℓ' : ℝ) with h | h | h
  · have hle : ((k + ℓ : ℤ) : ℝ) + 1 ≤ ((k + ℓ' : ℤ) : ℝ) := by
      have h1 : ℓ + 1 ≤ ℓ' := by exact_mod_cast h
      have h2 : ((k + ℓ : ℤ) : ℝ) + 1 = ((k + ℓ + 1 : ℤ) : ℝ) := by push_cast; ring
      rw [h2]
      have h3 : k + ℓ + 1 ≤ k + ℓ' := by omega
      exact_mod_cast h3
    linarith [hx.2, hx'.1]
  · exact absurd (by exact_mod_cast h : ℓ = ℓ') hne
  · have hle : ((k + ℓ' : ℤ) : ℝ) + 1 ≤ ((k + ℓ : ℤ) : ℝ) := by
      have h1 : ℓ' + 1 ≤ ℓ := by exact_mod_cast h
      have h2 : ((k + ℓ' : ℤ) : ℝ) + 1 = ((k + ℓ' + 1 : ℤ) : ℝ) := by push_cast; ring
      rw [h2]
      have h3 : k + ℓ' + 1 ≤ k + ℓ := by omega
      exact_mod_cast h3
    linarith [hx'.2, hx.1]

/-- **A.e. summability of the `ℓ`-lattice of `‖Bsum‖²`.**  If the `L²`-mass of `Bsum f M₂` is
finite then `t ↦ Σ'_ℓ ENNReal.ofReal (‖Bsum f M₂ (ℓ + t)‖²)` is finite almost everywhere: its
integral over every half-open unit interval is that `L²`-mass. -/
lemma fm_ae_tsum_ne_top_of_lintegral {M₂ : ℝ} {f : ℝ → ℝ}
    (hB : (∫⁻ u, ENNReal.ofReal (‖Bsum f M₂ u‖ ^ 2)) ≠ ⊤) :
    ∀ᵐ t : ℝ, (∑' ℓ : ℤ, ENNReal.ofReal (‖Bsum f M₂ ((ℓ : ℝ) + t)‖ ^ 2)) ≠ ⊤ := by
  set Phi : ℝ → ENNReal :=
    fun t => ∑' ℓ : ℤ, ENNReal.ofReal (‖Bsum f M₂ ((ℓ : ℝ) + t)‖ ^ 2) with hPhi
  have hbmeas : ∀ ℓ : ℤ, Measurable fun t : ℝ => ENNReal.ofReal (‖Bsum f M₂ ((ℓ : ℝ) + t)‖ ^ 2) :=
    fun ℓ => ENNReal.measurable_ofReal.comp
      (((measurable_Bsum f M₂).norm.pow_const 2).comp (measurable_const.add measurable_id))
  have hPhimeas : Measurable Phi := by
    rw [hPhi]; exact Measurable.tsum hbmeas
  have hkey : ∀ k : ℤ, (∫⁻ t in Set.Ico (k : ℝ) ((k : ℝ) + 1), Phi t) < ⊤ := by
    intro k
    have h1 : (∫⁻ t in Set.Ico (k : ℝ) ((k : ℝ) + 1), Phi t)
        = ∑' ℓ : ℤ, ∫⁻ t in Set.Ico (k : ℝ) ((k : ℝ) + 1),
            ENNReal.ofReal (‖Bsum f M₂ ((ℓ : ℝ) + t)‖ ^ 2) := by
      rw [hPhi]; exact MeasureTheory.lintegral_tsum (fun ℓ => (hbmeas ℓ).aemeasurable)
    have h2 : ∀ ℓ : ℤ,
        (∫⁻ t in Set.Ico (k : ℝ) ((k : ℝ) + 1),
            ENNReal.ofReal (‖Bsum f M₂ ((ℓ : ℝ) + t)‖ ^ 2))
          = ∫⁻ u in Set.Ico (((k + ℓ : ℤ) : ℝ)) (((k + ℓ : ℤ) : ℝ) + 1),
              ENNReal.ofReal (‖Bsum f M₂ u‖ ^ 2) := by
      intro ℓ
      have hcast1 : ((k + ℓ : ℤ) : ℝ) = (k : ℝ) + (ℓ : ℝ) := by push_cast; ring
      have hcast2 : (((k + ℓ : ℤ) : ℝ) + 1) = (k : ℝ) + 1 + (ℓ : ℝ) := by push_cast; ring
      rw [hcast2, hcast1]
      exact (fm_lintegral_Ico_comp_add (F := fun u => ENNReal.ofReal (‖Bsum f M₂ u‖ ^ 2))
        (ℓ : ℝ) (k : ℝ) ((k : ℝ) + 1)).symm
    have h3 : (∑' ℓ : ℤ, ∫⁻ u in Set.Ico (((k + ℓ : ℤ) : ℝ)) (((k + ℓ : ℤ) : ℝ) + 1),
            ENNReal.ofReal (‖Bsum f M₂ u‖ ^ 2))
        = ∫⁻ u, ENNReal.ofReal (‖Bsum f M₂ u‖ ^ 2) := by
      rw [← MeasureTheory.lintegral_iUnion
        (fun ℓ : ℤ => measurableSet_Ico) (fm_pairwise_disjoint_Ico_shift k)
        (fun u => ENNReal.ofReal (‖Bsum f M₂ u‖ ^ 2))]
      rw [fm_iUnion_Ico_shift_eq_univ, MeasureTheory.Measure.restrict_univ]
    rw [h1, tsum_congr h2, h3]
    exact lt_of_le_of_ne le_top hB
  have hnull : ∀ k : ℤ,
      volume (Set.Ico (k : ℝ) ((k : ℝ) + 1) ∩ {t : ℝ | Phi t = ⊤}) = 0 := by
    intro k
    have hset : MeasurableSet {t : ℝ | Phi t = ⊤} := hPhimeas (measurableSet_singleton ⊤)
    have hlt := ae_lt_top' hPhimeas.aemeasurable (ne_of_lt (hkey k))
    rw [MeasureTheory.ae_iff] at hlt
    rw [show {a : ℝ | ¬ Phi a < ⊤} = {t : ℝ | Phi t = ⊤} from by
      ext t; simp only [Set.mem_ofPred_eq, not_lt, top_le_iff]] at hlt
    rw [MeasureTheory.Measure.restrict_apply hset] at hlt
    rw [Set.inter_comm]; exact hlt
  have hzero : volume {t : ℝ | Phi t = ⊤} = 0 := by
    have hUn : ({t : ℝ | Phi t = ⊤}
        = ⋃ k : ℤ, (Set.Ico (k : ℝ) ((k : ℝ) + 1) ∩ {t : ℝ | Phi t = ⊤})) := by
      rw [← Set.iUnion_inter, fm_iUnion_Ico_int_eq_univ, Set.univ_inter]
    rw [hUn]; exact measure_iUnion_null hnull
  rw [MeasureTheory.ae_iff]
  have heq : {a : ℝ | ¬ (∑' ℓ : ℤ, ENNReal.ofReal (‖Bsum f M₂ ((ℓ : ℝ) + a)‖ ^ 2)) ≠ ⊤}
      = {t : ℝ | Phi t = ⊤} := by
    have h1 : ∀ a : ℝ, (∑' ℓ : ℤ, ENNReal.ofReal (‖Bsum f M₂ ((ℓ : ℝ) + a)‖ ^ 2)) = Phi a := by
      intro a; rw [hPhi]
    ext t; rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, h1 t]; simp
  rw [heq]; exact hzero

/-! ## The main identity -/

theorem far_mass_eq {C₀ K M₂ M₃ : ℝ} (hC₀ : 1 ≤ C₀) (hK : 0 < K) (hM₂ : 0 < M₂)
    (hM₃ : 0 < M₃) {f : ℝ → ℝ} (hf : Continuous f) (hsup : SuppHyp C₀ f) :
    FarMass K f M₂ M₃
      = M₃ * ∫ t in (Set.Ioi (2 / M₃) ∪ Set.Iio (-(2 / M₃))),
          (∑' ℓ : ℤ, ‖Bsum f M₂ ((ℓ : ℝ) + t)‖ ^ 2) * ‖psi1hat K (M₃ * t)‖ ^ 2 := by
  set S₁ : Set ℝ := Set.Ioi (2 / M₃) ∪ Set.Iio (-(2 / M₃)) with hS₁
  have hS₁meas : MeasurableSet S₁ := by
    rw [hS₁]; exact measurableSet_Ioi.union measurableSet_Iio
  set b : ℤ → ℝ → ENNReal := fun ℓ t => ENNReal.ofReal (‖Bsum f M₂ ((ℓ : ℝ) + t)‖ ^ 2)
    with hb
  set Wt : ℝ → ENNReal := fun t => ENNReal.ofReal (‖psi1hat K (M₃ * t)‖ ^ 2) with hW
  set E : ℤ → ENNReal := fun ℓ => ∫⁻ τ in (Set.Ioi (2 : ℝ) ∪ Set.Iio (-2)),
      ENNReal.ofReal (‖Hfun f M₂ M₃ ℓ τ‖ ^ 2 * ‖psi1hat K τ‖ ^ 2) with hE
  set R : ENNReal := ∫⁻ t in S₁, (∑' ℓ : ℤ, b ℓ t) * Wt t with hR
  have hbmeas : ∀ ℓ : ℤ, Measurable fun t : ℝ => b ℓ t := by
    intro ℓ
    rw [hb]
    exact ENNReal.measurable_ofReal.comp
      (((measurable_Bsum f M₂).norm.pow_const 2).comp (measurable_const.add measurable_id))
  have hWmeas : Measurable Wt := by
    rw [hW]
    exact ENNReal.measurable_ofReal.comp
      (((psi1hat_continuous K).measurable.comp (measurable_const.mul measurable_id)).norm.pow_const 2)
  -- ### (1) the per-`ℓ` substitution
  have hstep1 : ∀ ℓ : ℤ, E ℓ = ENNReal.ofReal M₃ * ∫⁻ t in S₁, b ℓ t * Wt t := by
    intro ℓ
    change (∫⁻ τ in (Set.Ioi (2 : ℝ) ∪ Set.Iio (-2)),
          ENNReal.ofReal (‖Hfun f M₂ M₃ ℓ τ‖ ^ 2 * ‖psi1hat K τ‖ ^ 2))
        = ENNReal.ofReal M₃ * ∫⁻ t in S₁, b ℓ t * Wt t
    rw [far_inner_eq hM₃ f ℓ]
    congr 1
    set F : ℝ → ENNReal := fun x =>
      if 2 / M₃ < |x| then
        ENNReal.ofReal (‖Bsum f M₂ ((ℓ : ℝ) + x)‖ ^ 2 * ‖psi1hat K (M₃ * x)‖ ^ 2)
      else 0 with hF
    have hcongr : ∀ u : ℝ,
        (if 2 / M₃ < |u - (ℓ : ℝ)| then
          ENNReal.ofReal (‖Bsum f M₂ u‖ ^ 2 * ‖psi1hat K (M₃ * (u - (ℓ : ℝ)))‖ ^ 2) else 0)
          = F (u - (ℓ : ℝ)) := by
      intro u
      simp only [hF]
      by_cases h : 2 / M₃ < |u - (ℓ : ℝ)|
      · rw [if_pos h, if_pos h]
        rw [show ‖Bsum f M₂ u‖ ^ 2 = ‖Bsum f M₂ ((ℓ : ℝ) + (u - (ℓ : ℝ)))‖ ^ 2 from by
              conv_lhs => rw [show u = (ℓ : ℝ) + (u - (ℓ : ℝ)) by ring]]
      · rw [if_neg h, if_neg h]
    rw [MeasureTheory.lintegral_congr hcongr, MeasureTheory.lintegral_sub_right_eq_self F (ℓ : ℝ)]
    rw [← MeasureTheory.lintegral_indicator hS₁meas]
    refine MeasureTheory.lintegral_congr (fun x => ?_)
    simp only [hF, Set.indicator_apply]
    by_cases h : x ∈ S₁
    · rw [if_pos h, if_pos ((fm_mem_far_iff_abs (2 / M₃) x).mp h)]
      simp only [hb, hW]
      exact ENNReal.ofReal_mul (sq_nonneg _)
    · rw [if_neg h, if_neg (fun hh => h ((fm_mem_far_iff_abs (2 / M₃) x).mpr hh))]
  -- ### (2) summing over `ℓ` and exchanging with the integral
  have hstep2 : (∑' ℓ : ℤ, E ℓ) = ENNReal.ofReal M₃ * R := by
    rw [tsum_congr hstep1, ENNReal.tsum_mul_left]
    congr 1
    rw [hR]
    have hswap := MeasureTheory.lintegral_tsum (μ := volume.restrict S₁)
      (f := fun ℓ t => b ℓ t * Wt t) (fun ℓ : ℤ => ((hbmeas ℓ).mul hWmeas).aemeasurable)
    exact hswap.symm.trans (MeasureTheory.lintegral_congr (fun t => ENNReal.tsum_mul_right))
  -- ### finiteness of each `E ℓ`
  have hEne : ∀ ℓ : ℤ, E ℓ ≠ ⊤ := by
    intro ℓ
    obtain ⟨CB, hCBnn, hCB⟩ := fm_norm_Bsum_le_const hC₀ hf hsup hM₂
    have hHle : ∀ τ : ℝ, ‖Hfun f M₂ M₃ ℓ τ‖ ^ 2 ≤ CB ^ 2 := by
      intro τ
      rw [Hfun_eq_Bsum]
      exact pow_le_pow_left₀ (norm_nonneg _) (hCB _) 2
    have hψmeas : Measurable (fun τ : ℝ => ENNReal.ofReal (‖psi1hat K τ‖ ^ 2)) :=
      ENNReal.measurable_ofReal.comp ((psi1hat_continuous K).measurable.norm.pow_const 2)
    have hA : (∫⁻ τ in (Set.Ioi (2 : ℝ) ∪ Set.Iio (-2)),
          ENNReal.ofReal (‖Hfun f M₂ M₃ ℓ τ‖ ^ 2 * ‖psi1hat K τ‖ ^ 2))
        ≤ ENNReal.ofReal (CB ^ 2) * ∫⁻ τ, ENNReal.ofReal (‖psi1hat K τ‖ ^ 2) := by
      calc (∫⁻ τ in (Set.Ioi (2 : ℝ) ∪ Set.Iio (-2)),
            ENNReal.ofReal (‖Hfun f M₂ M₃ ℓ τ‖ ^ 2 * ‖psi1hat K τ‖ ^ 2))
          ≤ ∫⁻ τ in (Set.Ioi (2 : ℝ) ∪ Set.Iio (-2)),
              ENNReal.ofReal (CB ^ 2) * ENNReal.ofReal (‖psi1hat K τ‖ ^ 2) := by
            refine MeasureTheory.lintegral_mono (fun τ => ?_)
            rw [ENNReal.ofReal_mul (sq_nonneg _)]
            exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (hHle τ)) (zero_le)
        _ = ENNReal.ofReal (CB ^ 2) *
              ∫⁻ τ in (Set.Ioi (2 : ℝ) ∪ Set.Iio (-2)),
                ENNReal.ofReal (‖psi1hat K τ‖ ^ 2) :=
            MeasureTheory.lintegral_const_mul _ hψmeas
        _ ≤ ENNReal.ofReal (CB ^ 2) * ∫⁻ τ, ENNReal.ofReal (‖psi1hat K τ‖ ^ 2) :=
            mul_le_mul_of_nonneg_left
              (MeasureTheory.setLIntegral_le_lintegral (Set.Ioi (2 : ℝ) ∪ Set.Iio (-2)) _)
              (zero_le)
    change (∫⁻ τ in (Set.Ioi (2 : ℝ) ∪ Set.Iio (-2)),
        ENNReal.ofReal (‖Hfun f M₂ M₃ ℓ τ‖ ^ 2 * ‖psi1hat K τ‖ ^ 2)) ≠ ⊤
    exact ne_of_lt (lt_of_le_of_lt hA (lt_top_iff_ne_top.mpr
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (fm_lintegral_psi1hat_sq_ne_top K))))
  -- ### (3) `FarMass` as `M₃ * R.toReal`
  have hterm : ∀ ℓ : ℤ,
      (∫ τ in (Set.Ioi (2 : ℝ) ∪ Set.Iio (-2)),
        ‖Hfun f M₂ M₃ ℓ τ‖ ^ 2 * ‖psi1hat K τ‖ ^ 2) = (E ℓ).toReal := by
    intro ℓ
    have hHmeas : Measurable (fun τ : ℝ => Hfun f M₂ M₃ ℓ τ) := by
      rw [show (fun τ : ℝ => Hfun f M₂ M₃ ℓ τ)
            = fun τ : ℝ => Bsum f M₂ ((ℓ : ℝ) + τ / M₃) from by
          funext τ; rw [Hfun_eq_Bsum]]
      exact (measurable_Bsum f M₂).comp (measurable_const.add (measurable_id.div_const M₃))
    have haesm : AEStronglyMeasurable
        (fun τ : ℝ => ‖Hfun f M₂ M₃ ℓ τ‖ ^ 2 * ‖psi1hat K τ‖ ^ 2)
        (volume.restrict (Set.Ioi (2 : ℝ) ∪ Set.Iio (-2))) :=
      (((hHmeas.norm.pow_const 2).mul
        ((psi1hat_continuous K).measurable.norm.pow_const 2)).aestronglyMeasurable)
    change (∫ τ in (Set.Ioi (2 : ℝ) ∪ Set.Iio (-2)),
        ‖Hfun f M₂ M₃ ℓ τ‖ ^ 2 * ‖psi1hat K τ‖ ^ 2)
      = (∫⁻ τ in (Set.Ioi (2 : ℝ) ∪ Set.Iio (-2)),
        ENNReal.ofReal (‖Hfun f M₂ M₃ ℓ τ‖ ^ 2 * ‖psi1hat K τ‖ ^ 2)).toReal
    exact MeasureTheory.integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall (fun τ => by positivity)) haesm
  have hFar : FarMass K f M₂ M₃ = M₃ * R.toReal := by
    change (∑' ℓ : ℤ, ∫ τ in (Set.Ioi (2 : ℝ) ∪ Set.Iio (-2)),
        ‖Hfun f M₂ M₃ ℓ τ‖ ^ 2 * ‖psi1hat K τ‖ ^ 2) = M₃ * R.toReal
    rw [tsum_congr hterm, ← ENNReal.tsum_toReal_eq hEne, hstep2, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hM₃.le]
  -- ### (4) the right-hand side
  have hb_eq : ∀ t : ℝ, (∑' ℓ : ℤ, b ℓ t)
      = ∑' ℓ : ℤ, ENNReal.ofReal (‖Bsum f M₂ ((ℓ : ℝ) + t)‖ ^ 2) := fun t => by rw [hb]
  have hae : ∀ᵐ t : ℝ, (∑' ℓ : ℤ, b ℓ t) ≠ ⊤ := by
    filter_upwards [fm_ae_tsum_ne_top_of_lintegral (M₂ := M₂) (f := f)
      (fm_lintegral_Bsum_sq_ne_top hC₀ hM₂ hf hsup)] with t ht
    rwa [hb_eq t]
  have hΨeq : ∀ t : ℝ, ENNReal.toReal (∑' ℓ : ℤ, b ℓ t)
      = ∑' ℓ : ℤ, ‖Bsum f M₂ ((ℓ : ℝ) + t)‖ ^ 2 := by
    intro t
    rw [ENNReal.tsum_toReal_eq (fun ℓ => ENNReal.ofReal_ne_top)]
    exact tsum_congr (fun ℓ => ENNReal.toReal_ofReal (sq_nonneg _))
  have hmeas : AEStronglyMeasurable
      (fun t : ℝ => (∑' ℓ : ℤ, ‖Bsum f M₂ ((ℓ : ℝ) + t)‖ ^ 2) * ‖psi1hat K (M₃ * t)‖ ^ 2)
      (volume.restrict S₁) := by
    have hwmeas : Measurable (fun t : ℝ => ‖psi1hat K (M₃ * t)‖ ^ 2) :=
      ((psi1hat_continuous K).measurable.comp (measurable_const.mul measurable_id)).norm.pow_const 2
    have hm : AEMeasurable
        (fun t : ℝ => ENNReal.toReal (∑' ℓ : ℤ, b ℓ t) * ‖psi1hat K (M₃ * t)‖ ^ 2)
        (volume.restrict S₁) :=
      (ENNReal.measurable_toReal.comp (Measurable.tsum hbmeas)).aemeasurable.mul
        hwmeas.aemeasurable
    refine (hm.congr ?_).aestronglyMeasurable
    filter_upwards with t
    rw [hΨeq t]
  have hstep4 : (∫ t in S₁,
      (∑' ℓ : ℤ, ‖Bsum f M₂ ((ℓ : ℝ) + t)‖ ^ 2) * ‖psi1hat K (M₃ * t)‖ ^ 2) = R.toReal := by
    rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall (fun t => mul_nonneg (tsum_nonneg (fun ℓ => sq_nonneg _))
        (sq_nonneg _))) hmeas, hR]
    congr 1
    refine MeasureTheory.lintegral_congr_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_of_ae hae] with t ht
    rw [ENNReal.ofReal_mul (tsum_nonneg (fun ℓ => sq_nonneg _))]
    congr 1
    have hsum : Summable (fun ℓ : ℤ => ‖Bsum f M₂ ((ℓ : ℝ) + t)‖ ^ 2) :=
      (ENNReal.summable_toReal ht).congr (fun ℓ => ENNReal.toReal_ofReal (sq_nonneg _))
    rw [ENNReal.ofReal_tsum_of_nonneg (fun ℓ => sq_nonneg _) hsum]
  -- ### conclusion
  rw [hFar]
  exact congrArg (fun x => M₃ * x) hstep4.symm

end

end Work.GM.Affine
