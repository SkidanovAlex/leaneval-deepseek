/-
Copyright: work module for the Elgindi finite-time singularity project.

# `EigParsevalDefs`: the Hilbert space `L²(Iθ, cos θ dθ)` and the angular eigenbasis

This module collects the definitions and the elementary facts needed for the Parseval
identity `Work.FTS.EllipticEst.LevelOneAsm.eigFun_parseval` for the angular eigenfunctions
`Θ_n(θ) = cos θ · p_n(sin θ)` of `EigBasis`:

  `∑_n (∫ f Θ_{n+1} cos)(∫ Θ_{n+1} g cos)/(∫ Θ_{n+1}² cos) = ∫ f g cos θ`

The eigenfunctions are orthogonal for the weight `cos θ` (`eigFun_orth`), have positive norm
(`eigFun_normSq_pos`) and their span is dense (`eigFun_span_dense`); the Parseval identity is
therefore the standard Hilbert-basis expansion in the space

  `L²(Iθ, cos θ dθ) = L²(angMeasure)`,
  `angMeasure = (volume.restrict Iθ).withDensity (ofReal ∘ cos)`.

The main contents here are

* `angMeasure` and its basic integral formula `integral_angMeasure`:
  `∫ F ∂angMeasure = ∫ θ in Iθ, cos θ * F θ` (holding for *every* `F`, by
  `integral_withDensity_eq_integral_toReal_smul`);
* the fact that `angMeasure` and `volume.restrict Iθ` have the *same null sets*
  (`angMeasure ≪ volume.restrict Iθ` and `restrict_absolutelyContinuous_angMeasure`), which is
  what lets one transfer a.e. statements between the weighted and unweighted pictures;
* the classes `eigLp n` of the eigenfunctions in `L²(angMeasure)`, the inner-product formula
  `inner_toLp_toLp`, the numbers `eigDn n = ∫ Θ_{n+1}² cos` and the *normalised* family
  `eigE n = (√(eigDn n))⁻¹ • Θ_{n+1}`.

The companion lemmas `EigParsevalOrth.eigE_orthonormal` and
`EigParsevalDense.eigE_span_orthogonal_eq_bot` turn `eigE` into the orthonormal basis used by
`HilbertBasis.tsum_inner_mul_inner` in the proof of `eigFun_parseval`.
-/
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.FTS.EllipticEst.LevelOneAsm.EigBasis
import Submission.Work.FTS.EllipticEst.LevelOneAsm.eigFun_orth
import Submission.Work.FTS.EllipticEst.LevelOneAsm.eigFun_normSq_pos

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.LevelOneAsm

set_option autoImplicit false

local notation "Iθ" => Work.Spaces.Iθ

/-! ## Elementary facts about `Iθ = [0, π/2]` -/

lemma cos_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Iθ) : 0 ≤ Real.cos θ :=
  Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2]⟩

/-! ## The measure `cos θ dθ` on `Iθ` -/

/-- The measure `cos θ dθ` restricted to `Iθ`: the weight for which the angular eigenfunctions
`Θ_n` are orthogonal. -/
def angMeasure : Measure ℝ :=
  (volume.restrict Iθ).withDensity (fun θ => ENNReal.ofReal (Real.cos θ))

/-- **The integral against `angMeasure` is the weighted integral on `Iθ`.**  The identity holds
for *every* `F : ℝ → ℝ` (no integrability hypothesis), thanks to
`integral_withDensity_eq_integral_toReal_smul`. -/
theorem integral_angMeasure (F : ℝ → ℝ) :
    ∫ θ, F θ ∂angMeasure = ∫ θ in Iθ, Real.cos θ * F θ := by
  rw [angMeasure, integral_withDensity_eq_integral_toReal_smul
    (Real.measurable_cos.ennreal_ofReal) (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [smul_eq_mul]
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_mem (s := Iθ) measurableSet_Icc] with θ hθ
  rw [ENNReal.toReal_ofReal (cos_nonneg_of_mem_Iθ hθ)]

theorem angMeasure_absolutelyContinuous : angMeasure ≪ volume.restrict Iθ :=
  MeasureTheory.withDensity_absolutelyContinuous _ _

theorem angMeasure_Iθ_compl : angMeasure Iθᶜ = 0 := by
  refine angMeasure_absolutelyContinuous ?_
  rw [Work.Spaces.Iθ,
    Measure.restrict_apply (s := Set.Icc (0 : ℝ) (Real.pi / 2))
      (t := (Set.Icc (0 : ℝ) (Real.pi / 2))ᶜ) measurableSet_Icc.compl]
  simp

theorem ae_mem_Iθ_angMeasure : ∀ᵐ θ ∂angMeasure, θ ∈ Iθ := by
  rw [MeasureTheory.ae_iff]
  have h : {a : ℝ | ¬ a ∈ Iθ} = Iθᶜ := rfl
  rw [h]
  exact angMeasure_Iθ_compl

instance instIsFiniteMeasureAngMeasure : IsFiniteMeasure angMeasure := by
  rw [angMeasure]
  refine MeasureTheory.isFiniteMeasure_withDensity ?_
  have hle : ∫⁻ (a : ℝ), ENNReal.ofReal (Real.cos a) ∂(volume.restrict Iθ)
      ≤ ∫⁻ (_ : ℝ), (1 : ENNReal) ∂(volume.restrict Iθ) := by
    refine MeasureTheory.lintegral_mono (fun a => ?_)
    rw [ENNReal.ofReal_le_one]
    exact Real.cos_le_one a
  have htop : ∫⁻ (_ : ℝ), (1 : ENNReal) ∂(volume.restrict Iθ) ≠ ⊤ := by
    rw [lintegral_one, Measure.restrict_apply (s := Iθ) (t := Set.univ) MeasurableSet.univ,
      Set.univ_inter, Work.Spaces.Iθ, Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  exact ne_top_of_le_ne_top htop hle

/-- The only zero of `cos` in `Iθ` is `π/2`, so `{θ ∈ Iθ | cos θ = 0}` is null. -/
theorem volume_cos_eq_zero_inter_Iθ :
    volume ({θ : ℝ | Real.cos θ = 0} ∩ Iθ) = 0 := by
  refine measure_mono_null ?_ (measure_singleton (Real.pi / 2))
  rintro x ⟨hc, hxI⟩
  rcases lt_or_eq_of_le hxI.2 with h | h
  · exact absurd hc (ne_of_gt (Real.cos_pos_of_mem_Ioo
      ⟨by linarith [hxI.1, Real.pi_pos], h⟩))
  · exact h

/-- `cos θ ≠ 0` for a.e. `θ ∈ Iθ` (the only zero of `cos` in `[0, π/2]` is `π/2`, a null set). -/
theorem cos_ne_zero_ae_restrict_Iθ :
    ∀ᵐ θ ∂(volume.restrict Iθ), Real.cos θ ≠ 0 := by
  rw [MeasureTheory.ae_restrict_iff' (s := Iθ) measurableSet_Icc, MeasureTheory.ae_iff]
  have hset : {a : ℝ | ¬ (a ∈ Iθ → Real.cos a ≠ 0)}
      = {θ : ℝ | Real.cos θ = 0} ∩ Iθ := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, not_imp, not_ne_iff]
    tauto
  rw [hset]
  exact volume_cos_eq_zero_inter_Iθ

/-- **The unweighted measure and `angMeasure` have the same null sets** (the direction that is
not automatic): a set of `angMeasure`-measure zero is Lebesgue-null on `Iθ`. -/
theorem restrict_absolutelyContinuous_angMeasure : volume.restrict Iθ ≪ angMeasure := by
  refine Measure.AbsolutelyContinuous.mk (fun s hs h0 => ?_)
  have h1 : ∫⁻ θ in s, ENNReal.ofReal (Real.cos θ) ∂(volume.restrict Iθ) = 0 := by
    rw [← MeasureTheory.withDensity_apply (μ := volume.restrict Iθ)
      (f := fun θ => ENNReal.ofReal (Real.cos θ)) hs]
    exact h0
  have h2 : ∀ᵐ θ ∂(volume.restrict Iθ).restrict s, Real.cos θ = 0 := by
    have h2a : ∀ᵐ θ ∂(volume.restrict Iθ).restrict s, ENNReal.ofReal (Real.cos θ) = 0 :=
      (MeasureTheory.lintegral_eq_zero_iff' (μ := (volume.restrict Iθ).restrict s)
        (Real.measurable_cos.ennreal_ofReal.aemeasurable)).mp h1
    filter_upwards [h2a, Filter.Eventually.filter_mono
      (MeasureTheory.ae_mono (Measure.restrict_le_self))
      (ae_restrict_mem (s := Iθ) measurableSet_Icc)] with θ hθ hIθ
    rw [ENNReal.ofReal_eq_zero] at hθ
    exact le_antisymm hθ (cos_nonneg_of_mem_Iθ hIθ)
  have h3 : ∀ᵐ θ ∂(volume.restrict Iθ), θ ∈ s → Real.cos θ = 0 := by
    rw [← MeasureTheory.ae_restrict_iff' (s := s) hs]
    exact h2
  have h4 : (volume.restrict Iθ) s ≤ (volume.restrict Iθ) {θ : ℝ | Real.cos θ = 0} := by
    rw [MeasureTheory.ae_iff] at h3
    have hsub : s ⊆ {θ : ℝ | Real.cos θ = 0} ∪ {θ : ℝ | ¬ (θ ∈ s → Real.cos θ = 0)} := by
      intro x hx
      by_cases hx' : Real.cos x = 0
      · exact Or.inl hx'
      · exact Or.inr (by simp [hx, hx'])
    calc (volume.restrict Iθ) s
        ≤ (volume.restrict Iθ)
            ({θ : ℝ | Real.cos θ = 0} ∪ {θ : ℝ | ¬ (θ ∈ s → Real.cos θ = 0)}) :=
          measure_mono hsub
      _ ≤ (volume.restrict Iθ) {θ : ℝ | Real.cos θ = 0}
            + (volume.restrict Iθ) {θ : ℝ | ¬ (θ ∈ s → Real.cos θ = 0)} :=
          measure_union_le _ _
      _ = (volume.restrict Iθ) {θ : ℝ | Real.cos θ = 0} := by rw [h3, add_zero]
  have hZ : (volume.restrict Iθ) {θ : ℝ | Real.cos θ = 0} = 0 := by
    rw [Measure.restrict_apply (s := Iθ) (t := {θ : ℝ | Real.cos θ = 0})
      (measurableSet_eq_fun Real.measurable_cos measurable_const)]
    exact volume_cos_eq_zero_inter_Iθ
  exact le_antisymm (hZ ▸ h4) zero_le

/-! ## The eigenfunctions as elements of `L²(angMeasure)` -/

/-- `|Θ_n(θ)| ≤ (Σ_k |c_k|) cos θ` on `Iθ`, hence `Θ_n` is bounded on `Iθ`. -/
theorem abs_eigFun_le_cos (n : ℕ) :
    ∀ θ ∈ Iθ, |eigFun n θ| ≤ (∑ k ∈ Finset.range n, |eigCoef n k|) * Real.cos θ := by
  intro θ hθ
  have hc : 0 ≤ Real.cos θ := cos_nonneg_of_mem_Iθ hθ
  have hs : |Real.sin θ| ≤ 1 := Real.abs_sin_le_one θ
  have hpoly : |eigPoly n (Real.sin θ)| ≤ ∑ k ∈ Finset.range n, |eigCoef n k| := by
    rw [eigPoly]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine Finset.sum_le_sum (fun k _ => ?_)
    rw [abs_mul, abs_pow]
    have hsk : |Real.sin θ| ^ (2 * k + 1) ≤ 1 := pow_le_one₀ (abs_nonneg _) hs
    calc |eigCoef n k| * |Real.sin θ| ^ (2 * k + 1)
        ≤ |eigCoef n k| * 1 := mul_le_mul_of_nonneg_left hsk (abs_nonneg _)
      _ = |eigCoef n k| := mul_one _
  rw [eigFun, abs_mul, abs_of_nonneg hc]
  calc Real.cos θ * |eigPoly n (Real.sin θ)|
      ≤ Real.cos θ * (∑ k ∈ Finset.range n, |eigCoef n k|) :=
        mul_le_mul_of_nonneg_left hpoly hc
    _ = (∑ k ∈ Finset.range n, |eigCoef n k|) * Real.cos θ := by ring

/-- The eigenfunction `Θ_n` lies in `L²(angMeasure)`. -/
theorem memLp_eigFun (n : ℕ) : MemLp (eigFun n) 2 angMeasure := by
  have hcont : Continuous (eigFun n) := by
    change Continuous (fun θ : ℝ => Real.cos θ * eigPoly n (Real.sin θ))
    refine Real.continuous_cos.mul ?_
    change Continuous (fun θ : ℝ => ∑ k ∈ Finset.range n, eigCoef n k * (Real.sin θ) ^ (2 * k + 1))
    exact continuous_finsetSum _ fun k _ =>
      continuous_const.mul (Real.continuous_sin.pow _)
  refine MemLp.of_bound hcont.aestronglyMeasurable (∑ k ∈ Finset.range n, |eigCoef n k|) ?_
  filter_upwards [ae_mem_Iθ_angMeasure] with θ hθ
  have h1 := abs_eigFun_le_cos n θ hθ
  have hC : (0 : ℝ) ≤ ∑ k ∈ Finset.range n, |eigCoef n k| :=
    Finset.sum_nonneg fun k _ => abs_nonneg _
  have h2 : (∑ k ∈ Finset.range n, |eigCoef n k|) * Real.cos θ
      ≤ ∑ k ∈ Finset.range n, |eigCoef n k| := by
    calc (∑ k ∈ Finset.range n, |eigCoef n k|) * Real.cos θ
        ≤ (∑ k ∈ Finset.range n, |eigCoef n k|) * 1 :=
          mul_le_mul_of_nonneg_left (Real.cos_le_one θ) hC
      _ = ∑ k ∈ Finset.range n, |eigCoef n k| := mul_one _
  rw [Real.norm_eq_abs]
  exact h1.trans h2

/-- The class of `Θ_n` in `L²(angMeasure)`. -/
def eigLp (n : ℕ) : Lp ℝ 2 angMeasure :=
  MemLp.toLp (eigFun n) (memLp_eigFun n)

theorem eigLp_coe (n : ℕ) : (eigLp n : ℝ → ℝ) =ᵐ[angMeasure] eigFun n :=
  MeasureTheory.MemLp.coeFn_toLp _

/-- **The `L²(angMeasure)` inner product of two classes with explicit representatives is the
weighted integral on `Iθ`.** -/
theorem inner_toLp_toLp {f g : ℝ → ℝ} (hf : MemLp f 2 angMeasure) (hg : MemLp g 2 angMeasure) :
    inner ℝ (MeasureTheory.MemLp.toLp f hf) (MeasureTheory.MemLp.toLp g hg)
      = ∫ θ in Iθ, f θ * g θ * Real.cos θ := by
  rw [MeasureTheory.L2.inner_def]
  have h1 : (fun a => inner ℝ ((MeasureTheory.MemLp.toLp f hf : ℝ → ℝ) a)
        ((MeasureTheory.MemLp.toLp g hg : ℝ → ℝ) a))
      =ᵐ[angMeasure] fun a => f a * g a := by
    filter_upwards [MeasureTheory.MemLp.coeFn_toLp hf,
      MeasureTheory.MemLp.coeFn_toLp hg] with a ha hb
    rw [ha, hb, Real.inner_apply]
  rw [integral_congr_ae h1, integral_angMeasure]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)

theorem inner_eigLp (n m : ℕ) :
    inner ℝ (eigLp n) (eigLp m) = ∫ θ in Iθ, eigFun n θ * eigFun m θ * Real.cos θ :=
  inner_toLp_toLp (memLp_eigFun n) (memLp_eigFun m)

/-- The squared `L²(angMeasure)`-norm of `Θ_{n+1}`. -/
def eigDn (n : ℕ) : ℝ := ∫ θ in Iθ, (eigFun (n + 1) θ) ^ 2 * Real.cos θ

theorem eigDn_pos (n : ℕ) : 0 < eigDn n :=
  eigFun_normSq_pos (n + 1) (Nat.le_add_left 1 n)

/-- The *normalised* eigenfunctions: `eigE n = (√(eigDn n))⁻¹ • Θ_{n+1}` as a class in
`L²(angMeasure)`. -/
def eigE (n : ℕ) : Lp ℝ 2 angMeasure :=
  (Real.sqrt (eigDn n))⁻¹ • eigLp (n + 1)

theorem eigE_coe (n : ℕ) :
    (eigE n : ℝ → ℝ) =ᵐ[angMeasure]
      fun θ => (Real.sqrt (eigDn n))⁻¹ * eigFun (n + 1) θ := by
  simp only [eigE]
  filter_upwards [MeasureTheory.Lp.coeFn_smul (c := (Real.sqrt (eigDn n))⁻¹) (eigLp (n + 1)),
    eigLp_coe (n + 1)] with θ h1 h2
  rw [h1]
  simp only [Pi.smul_apply, smul_eq_mul, h2]

/-! ## Inner products of a class with the normalised eigenfunctions -/

theorem inner_toLp_eigLp {f : ℝ → ℝ} (hf : MemLp f 2 angMeasure) (m : ℕ) :
    inner ℝ (MeasureTheory.MemLp.toLp f hf) (eigLp m)
      = ∫ θ in Iθ, f θ * eigFun m θ * Real.cos θ :=
  inner_toLp_toLp hf (memLp_eigFun m)

theorem inner_toLp_eigE {f : ℝ → ℝ} (hf : MemLp f 2 angMeasure) (n : ℕ) :
    inner ℝ (MeasureTheory.MemLp.toLp f hf) (eigE n)
      = (Real.sqrt (eigDn n))⁻¹ * ∫ θ in Iθ, f θ * eigFun (n + 1) θ * Real.cos θ := by
  rw [eigE, inner_smul_right, inner_toLp_eigLp]

theorem inner_eigE_toLp {g : ℝ → ℝ} (hg : MemLp g 2 angMeasure) (n : ℕ) :
    inner ℝ (eigE n) (MeasureTheory.MemLp.toLp g hg)
      = (Real.sqrt (eigDn n))⁻¹ * ∫ θ in Iθ, eigFun (n + 1) θ * g θ * Real.cos θ := by
  have hcomm : (∫ θ in Iθ, g θ * eigFun (n + 1) θ * Real.cos θ)
      = ∫ θ in Iθ, eigFun (n + 1) θ * g θ * Real.cos θ :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)
  rw [real_inner_comm, inner_toLp_eigE, hcomm]

/-! ## `L²(angMeasure)` membership from the hypotheses of the Parseval statement -/

theorem memLp_of_hyps {f : ℝ → ℝ}
    (hm : AEMeasurable f (volume.restrict Iθ))
    (hf : IntegrableOn (fun θ => f θ ^ 2 * Real.cos θ) Iθ) : MemLp f 2 angMeasure := by
  have haesm : AEStronglyMeasurable f angMeasure :=
    hm.aestronglyMeasurable.mono_ac angMeasure_absolutelyContinuous
  rw [MeasureTheory.memLp_two_iff_integrable_sq haesm]
  rw [angMeasure,
    MeasureTheory.integrable_withDensity_iff_integrable_smul'
      (Real.measurable_cos.ennreal_ofReal) (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  refine hf.congr ?_
  filter_upwards [ae_restrict_mem (s := Iθ) measurableSet_Icc] with θ hθ
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (cos_nonneg_of_mem_Iθ hθ)]
  ring

end Work.FTS.EllipticEst.LevelOneAsm
