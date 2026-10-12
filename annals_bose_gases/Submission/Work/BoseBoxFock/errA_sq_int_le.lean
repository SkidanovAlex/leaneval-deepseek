import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.K1pairingDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.errA_sq_int_le`

The first row error `k1ErrA` of the pair-kernel truncation converges to `0` in `L²` of the corpus
box, as the lattice cut-off `N → ∞`.

`k1ErrA v μ fu N Wa Wb z = pinQA v μ N (k1cfun fu Wa Wb ℓ N) z - latPer3 ℓ (Wa + Wb) z`
(`ℓ = ellH v μ`) is the difference of the truncated `χχ`-lattice row and the periodisation of
`Wa + Wb`.  By the PROVED `k1pinQA_split` the truncated row splits into the *cut* `Wa`-row plus the
*un-cut* `Wb`-row; using the evenness of `Wa` and `Wb` (`chat_eq_kinFT_of_even`) the two pieces are
exactly the rows whose `L²` convergence is the content of the proved siblings
`Work.BoseBoxFock.latRowSum_tendsto_L2` and `Work.BoseBoxFock.latCubeSum_tendsto_L2` (restated here
as `k1RowSum_L2` / `k1CubeSum_L2`).

The only *structural* input is the additivity of the periodisation
`latPer3 ℓ (Wa + Wb) = latPer3 ℓ Wa + latPer3 ℓ Wb`: all three weights vanish outside the common
ball `R = max Ra Rb`, so on the box `latPer` is the finite sum over `LatFourier.latFinSet ℓ R`
(`LatFourier.latPer_eq_sum_finset_of_norm_le`, valid as soon as `‖z‖ ≤ √3 ℓ`, which holds on
`corpusBox.boxL ℓ = ℓ • unitCell`).  The two pieces are then combined with the elementary `L²`
triangle inequality `∫_s ‖f+g‖² ≤ 2∫_s ‖f‖² + 2∫_s ‖g‖²`.
-/

noncomputable section

open MeasureTheory Filter
open scoped BigOperators

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-! ## 1. The periodisation on the centred box -/

/-- On the centred box `boxL ℓ = ℓ • [-1/2,1/2]³` one has `‖z‖ ≤ √3 ℓ`. -/
lemma errA_norm_le_of_mem_boxL {ℓ : ℝ} (hℓ : 0 < ℓ) {x : E3}
    (hx : x ∈ Work.BoseK15.corpusBox.boxL ℓ) : ‖x‖ ≤ Real.sqrt 3 * ℓ := by
  obtain ⟨y, hy, rfl⟩ := hx
  have hy1 : ‖y‖ ≤ 1 := by
    have h2 : ‖y‖ ^ 2 ≤ (1 : ℝ) ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      calc ∑ i : Fin 3, ‖y.ofLp i‖ ^ 2 ≤ ∑ _i : Fin 3, ((1 / 2 : ℝ)) ^ 2 := by
            apply Finset.sum_le_sum
            intro i _
            have hi : ‖y.ofLp i‖ ≤ (1 / 2 : ℝ) := by
              simpa [Real.norm_eq_abs, Work.BoseB4.unitCell] using hy i
            exact pow_le_pow_left₀ (norm_nonneg _) hi 2
        _ = 3 / 4 := by simp [Finset.sum_const, Fintype.card_fin]; norm_num
        _ ≤ (1 : ℝ) ^ 2 := by norm_num
    nlinarith [h2, norm_nonneg y]
  rw [norm_smul, Real.norm_of_nonneg hℓ.le]
  have h3 : (1 : ℝ) ≤ Real.sqrt 3 := by
    rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by norm_num)
  calc ℓ * ‖y‖ ≤ ℓ * 1 := mul_le_mul_of_nonneg_left hy1 hℓ.le
    _ = ℓ := mul_one _
    _ ≤ Real.sqrt 3 * ℓ := by nlinarith [hℓ, h3]

/-- The periodisation, as a finite sum, on the ball `‖z‖ ≤ √3 ℓ`. -/
lemma errA_latPer3_eq_sum {ℓ R : ℝ} (hℓ : 0 < ℓ) {W : E3 → ℝ}
    (hWs : ∀ x, R < ‖x‖ → W x = 0) {z : E3} (hz : ‖z‖ ≤ Real.sqrt 3 * ℓ) :
    latPer3 ℓ W z = ((ℓ ^ 3 : ℝ) : ℂ)
      * ∑ m ∈ LatFourier.latFinSet ℓ R, (W (z + ℓ • latVec m) : ℂ) := by
  rw [latPer3, latPer_eq_sum_finset_of_norm_le hℓ hWs hz]

/-- **Additivity of the periodisation** for weights vanishing outside a common ball. -/
lemma errA_latPer3_add {ℓ : ℝ} (hℓ : 0 < ℓ) {Ra Rb : ℝ} {Wa Wb : E3 → ℝ}
    (hWa : ∀ x, Ra < ‖x‖ → Wa x = 0) (hWb : ∀ x, Rb < ‖x‖ → Wb x = 0) {z : E3}
    (hz : ‖z‖ ≤ Real.sqrt 3 * ℓ) :
    latPer3 ℓ (Wa + Wb) z = latPer3 ℓ Wa z + latPer3 ℓ Wb z := by
  have h1 := latPer_eq_sum_finset_of_norm_le (R := max Ra Rb) hℓ
    (fun x hx => hWa x (lt_of_le_of_lt (le_max_left _ _) hx)) hz
  have h2 := latPer_eq_sum_finset_of_norm_le (R := max Ra Rb) hℓ
    (fun x hx => hWb x (lt_of_le_of_lt (le_max_right _ _) hx)) hz
  have h3 := latPer_eq_sum_finset_of_norm_le (W := Wa + Wb) (R := max Ra Rb) hℓ
    (fun x hx => by
      rw [Pi.add_apply, hWa x (lt_of_le_of_lt (le_max_left _ _) hx),
        hWb x (lt_of_le_of_lt (le_max_right _ _) hx), add_zero]) hz
  rw [latPer3, latPer3, latPer3, h3, h1, h2]
  have hsum : (∑ m ∈ LatFourier.latFinSet ℓ (max Ra Rb), ((Wa + Wb) (z + ℓ • latVec m) : ℂ))
      = (∑ m ∈ LatFourier.latFinSet ℓ (max Ra Rb), (Wa (z + ℓ • latVec m) : ℂ))
        + (∑ m ∈ LatFourier.latFinSet ℓ (max Ra Rb), (Wb (z + ℓ • latVec m) : ℂ)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun m _ => by simp [Pi.add_apply]
  rw [hsum]; ring

/-! ## 2. The pointwise split of the first row error -/

/-- Congruence for the lattice row in the weight family. -/
lemma errA_k1Row_congr {ℓ : ℝ} {N : ℕ} {F G : (Fin 3 → ℤ) → ℂ} (h : ∀ n, F n = G n)
    (z : E3) : k1Row ℓ N F z = k1Row ℓ N G z := by
  unfold k1Row
  exact Finset.sum_congr rfl fun k _ => by rw [h]

/-- **The split of `k1ErrA`** into the `Wa`-row and the `Wb`-row, on the box. -/
lemma errA_eq_split {v : E3 → ℝ} {μ : ℝ} (fu : Work.BoseBoxFix.LowCut) (N : ℕ) {Wa Wb : E3 → ℝ}
    (hWae : ∀ z, Wa (-z) = Wa z) (hWbe : ∀ z, Wb (-z) = Wb z) {Ra Rb : ℝ}
    (hWa : ∀ x, Ra < ‖x‖ → Wa x = 0) (hWb : ∀ x, Rb < ‖x‖ → Wb x = 0) {z : E3}
    (hz : z ∈ Work.BoseK15.corpusBox.boxL (ellH v μ)) :
    k1ErrA v μ fu N Wa Wb z
      = (rowSum (ellH v μ) fu N Wa z - latPer3 (ellH v μ) Wa z)
        + (k1Row (ellH v μ) N (k1KinWt (ellH v μ) Wb) z - latPer3 (ellH v μ) Wb z) := by
  have hℓ : 0 < ellH v μ := ellH_pos v μ
  have hadd := errA_latPer3_add hℓ hWa hWb (errA_norm_le_of_mem_boxL hℓ hz)
  have hrow : k1Row (ellH v μ) N (k1ChatWt (ellH v μ) Wb) z
      = k1Row (ellH v μ) N (k1KinWt (ellH v μ) Wb) z :=
    errA_k1Row_congr (fun n => k1ChatWt_eq_kinWt hWbe n) z
  simp only [k1ErrA]
  rw [k1pinQA_split fu hWae hWbe N z, hrow, hadd]
  ring

/-! ## 3. Uniform bounds -/

/-- The cut lattice row is uniformly bounded (its coefficients are `chat` of an even weight,
which is uniformly bounded by `chat_abs_le_uniform`). -/
lemma errA_rowSum_bound {ℓ : ℝ} (fu : Work.BoseBoxFix.LowCut) (N : ℕ) {W : E3 → ℝ}
    (hWe : ∀ z, W (-z) = W z) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z, ‖rowSum ℓ fu N W z‖ ≤ C := by
  obtain ⟨B, hB0, hB⟩ := chat_abs_le_uniform (W := W)
  refine ⟨∑ _k : Lab N, B, Finset.sum_nonneg fun _ _ => hB0, fun z => ?_⟩
  unfold rowSum
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  have hu1 : uvCut fu (uvRad ℓ N) (kmomLab ℓ N k) ≤ 1 := by rw [uvCut]; exact fu.le_one _
  have hu0 : 0 ≤ uvCut fu (uvRad ℓ N) (kmomLab ℓ N k) := by rw [uvCut]; exact fu.nonneg _
  have hchat : ‖Submission.BoseGases.kinFT (fun y => (W y : ℂ)) (kmomLab ℓ N k)‖ ≤ B := by
    rw [← chat_eq_kinFT_of_even hWe (kmomLab ℓ N k)]
    simpa using hB (kmomLab ℓ N k)
  have hu : ‖((uvCut fu (uvRad ℓ N) (kmomLab ℓ N k) : ℝ) : ℂ)‖ ≤ 1 := by
    have h : ‖((uvCut fu (uvRad ℓ N) (kmomLab ℓ N k) : ℝ) : ℂ)‖
        = |uvCut fu (uvRad ℓ N) (kmomLab ℓ N k)| := by simp
    rw [h, abs_le]
    exact ⟨by linarith, hu1⟩
  calc ‖((uvCut fu (uvRad ℓ N) (kmomLab ℓ N k) : ℝ) : ℂ)
        * Submission.BoseGases.kinFT (fun y => (W y : ℂ)) (kmomLab ℓ N k)
        * latChr ℓ (labVec N k) z‖
      = ‖((uvCut fu (uvRad ℓ N) (kmomLab ℓ N k) : ℝ) : ℂ)‖
          * ‖Submission.BoseGases.kinFT (fun y => (W y : ℂ)) (kmomLab ℓ N k)‖ := by
        rw [norm_mul, norm_mul, k1norm_latChr, mul_one]
    _ ≤ 1 * B := mul_le_mul hu hchat (norm_nonneg _) (by norm_num)
    _ = B := one_mul _

/-- The un-cut lattice row with the `kinFT`-weight of an even, compactly supported weight is
uniformly bounded. -/
lemma errA_k1Row_bound {ℓ : ℝ} (N : ℕ) {W : E3 → ℝ} (hWe : ∀ z, W (-z) = W z) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z, ‖k1Row ℓ N (k1KinWt ℓ W) z‖ ≤ C := by
  obtain ⟨B, hB0, hB⟩ := chat_abs_le_uniform (W := W)
  refine ⟨∑ _k : Lab N, B, Finset.sum_nonneg fun _ _ => hB0, fun z => ?_⟩
  unfold k1Row
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  have hk : ‖k1KinWt ℓ W (labVec N k)‖ ≤ B := by
    rw [← k1ChatWt_eq_kinWt hWe (labVec N k)]
    simpa [k1ChatWt] using hB (kmomInt ℓ (labVec N k))
  calc ‖k1KinWt ℓ W (labVec N k) * latChr ℓ (labVec N k) z‖
      = ‖k1KinWt ℓ W (labVec N k)‖ := by rw [norm_mul, k1norm_latChr, mul_one]
    _ ≤ B := hk

/-- The periodisation is uniformly bounded on the box. -/
lemma errA_latPer3_bound {ℓ R : ℝ} (hℓ : 0 < ℓ) {W : E3 → ℝ} (hWb : ∃ C, ∀ x, ‖W x‖ ≤ C)
    (hWs : ∀ x, R < ‖x‖ → W x = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ Work.BoseK15.corpusBox.boxL ℓ, ‖latPer3 ℓ W z‖ ≤ C := by
  obtain ⟨D, hD0, hD⟩ := latPer_bdd_of_norm_le hℓ hWb hWs
  refine ⟨‖((ℓ ^ 3 : ℝ) : ℂ)‖ * D, by positivity, fun z hz => ?_⟩
  rw [latPer3, norm_mul]
  exact mul_le_mul_of_nonneg_left (hD z (errA_norm_le_of_mem_boxL hℓ hz)) (norm_nonneg _)

/-! ## 4. Measurability on the box -/

/-- The cut lattice row is continuous. -/
lemma errA_continuous_rowSum (ℓ : ℝ) (fu : Work.BoseBoxFix.LowCut) (N : ℕ) (W : E3 → ℝ) :
    Continuous (rowSum ℓ fu N W) := by
  unfold rowSum
  refine continuous_finsetSum _ fun k _ => ?_
  exact (continuous_const.mul continuous_const).mul
    (by unfold latChr; fun_prop : Continuous (latChr ℓ (labVec N k)))

lemma errA_aesm_rowSum {ℓ : ℝ} (fu : Work.BoseBoxFix.LowCut) (N : ℕ) (W : E3 → ℝ) :
    AEStronglyMeasurable (rowSum ℓ fu N W)
      (volume.restrict (Work.BoseK15.corpusBox.boxL ℓ)) :=
  (errA_continuous_rowSum ℓ fu N W).aestronglyMeasurable.restrict

/-- The un-cut lattice row with the `kinFT`-weight is continuous. -/
lemma errA_continuous_k1Row (ℓ : ℝ) (N : ℕ) (F : (Fin 3 → ℤ) → ℂ) :
    Continuous (k1Row ℓ N F) := by
  unfold k1Row
  refine continuous_finsetSum _ fun k _ => ?_
  exact continuous_const.mul
    (by unfold latChr; fun_prop : Continuous (latChr ℓ (labVec N k)))

/-- On the box, the periodisation agrees with the exhibited finite sum of translates, hence is
a.e. strongly measurable. -/
lemma errA_aesm_latPer3 {ℓ R : ℝ} (hℓ : 0 < ℓ) {W : E3 → ℝ}
    (hWm : AEStronglyMeasurable W volume) (hWs : ∀ x, R < ‖x‖ → W x = 0) :
    AEStronglyMeasurable (latPer3 ℓ W)
      (volume.restrict (Work.BoseK15.corpusBox.boxL ℓ)) := by
  set G : E3 → ℂ := ∑ m ∈ LatFourier.latFinSet ℓ R,
    (fun z => ((W (z + ℓ • latVec m) : ℝ) : ℂ)) with hG
  have hGaesm : AEStronglyMeasurable G volume := by
    rw [hG]
    refine Finset.aestronglyMeasurable_sum _ fun m _ => ?_
    exact Complex.continuous_ofReal.comp_aestronglyMeasurable
      (hWm.comp_quasiMeasurePreserving
        (MeasureTheory.measurePreserving_add_right volume (ℓ • latVec m)).quasiMeasurePreserving)
  set F : E3 → ℂ := fun z => ((ℓ ^ 3 : ℝ) : ℂ) * G z with hF
  have hFaesm : AEStronglyMeasurable F volume := by
    rw [hF]; exact hGaesm.const_mul _
  refine (hFaesm.restrict (s := Work.BoseK15.corpusBox.boxL ℓ)).congr ?_
  rw [Filter.EventuallyEq,
    MeasureTheory.ae_restrict_iff' (Work.BoseK15.corpusBox.boxL_measurableSet ℓ)]
  refine Filter.Eventually.of_forall fun z hz => ?_
  rw [hF, latPer3,
    latPer_eq_sum_finset_of_norm_le hℓ hWs (errA_norm_le_of_mem_boxL hℓ hz), hG]
  simp only [Finset.sum_apply]

/-! ## 5. Two elementary `L²` facts -/

/-- A function bounded on a finite-measure set has integrable squared norm. -/
private lemma errA_integrableOn_normSq_of_bound {s : Set E3} (hs : MeasurableSet s)
    (hfin : volume s < ⊤) {F : E3 → ℂ} (hm : AEStronglyMeasurable F (volume.restrict s))
    (C : ℝ) (hC : ∀ z ∈ s, ‖F z‖ ≤ C) :
    Integrable (fun z => ‖F z‖ ^ 2) (volume.restrict s) := by
  haveI : IsFiniteMeasure (volume.restrict s) := ⟨by rwa [Measure.restrict_apply_univ]⟩
  have hm2 : AEStronglyMeasurable (fun z => ‖F z‖ ^ 2) (volume.restrict s) :=
    (hm.norm.mul hm.norm).congr (Eventually.of_forall fun z => by simp [Pi.mul_apply, sq])
  refine Integrable.of_bound hm2 ((max C 0) ^ 2) ?_
  rw [ae_restrict_iff' hs]
  refine Eventually.of_forall fun z hz => ?_
  have h1 : ‖F z‖ ≤ max C 0 := le_trans (hC z hz) (le_max_left C 0)
  rw [Real.norm_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ (norm_nonneg _) h1 2

/-- The elementary `L²` triangle inequality `‖f+g‖² ≤ 2‖f‖² + 2‖g‖²`. -/
private lemma errA_integral_normSq_add_le {s : Set E3} {f g : E3 → ℂ}
    (hf : Integrable (fun z => ‖f z‖ ^ 2) (volume.restrict s))
    (hg : Integrable (fun z => ‖g z‖ ^ 2) (volume.restrict s)) :
    (∫ z in s, ‖f z + g z‖ ^ 2)
      ≤ 2 * (∫ z in s, ‖f z‖ ^ 2) + 2 * (∫ z in s, ‖g z‖ ^ 2) := by
  have hpoint : ∀ z, ‖f z + g z‖ ^ 2 ≤ 2 * ‖f z‖ ^ 2 + 2 * ‖g z‖ ^ 2 := by
    intro z
    calc ‖f z + g z‖ ^ 2 ≤ (‖f z‖ + ‖g z‖) ^ 2 :=
          pow_le_pow_left₀ (by positivity) (norm_add_le _ _) 2
      _ ≤ 2 * (‖f z‖ ^ 2 + ‖g z‖ ^ 2) := add_sq_le
      _ = 2 * ‖f z‖ ^ 2 + 2 * ‖g z‖ ^ 2 := by ring
  calc (∫ z in s, ‖f z + g z‖ ^ 2)
      ≤ ∫ z in s, (2 * ‖f z‖ ^ 2 + 2 * ‖g z‖ ^ 2) :=
        integral_mono_of_nonneg (Eventually.of_forall fun z => by positivity)
          ((hf.const_mul 2).add (hg.const_mul 2)) (Eventually.of_forall hpoint)
    _ = 2 * (∫ z in s, ‖f z‖ ^ 2) + 2 * (∫ z in s, ‖g z‖ ^ 2) := by
        rw [integral_add (hf.const_mul 2) (hg.const_mul 2), integral_const_mul,
          integral_const_mul]

/-! ## 6. The target -/

theorem errA_sq_int_le {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ : ℝ}
    (fu : Work.BoseBoxFix.LowCut) {Wa Wb : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hWam : MeasureTheory.AEStronglyMeasurable Wa MeasureTheory.volume)
    (hWab : ∃ C : ℝ, ∀ x, ‖Wa x‖ ≤ C) (hWas : HasCompactSupport Wa)
    (hWae : ∀ z, Wa (-z) = Wa z)
    (hWbm : MeasureTheory.AEStronglyMeasurable Wb MeasureTheory.volume)
    (hWbb : ∃ C : ℝ, ∀ x, ‖Wb x‖ ≤ C) (hWbs : HasCompactSupport Wb)
    (hWbe : ∀ z, Wb (-z) = Wb z) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ N' : ℕ, N ≤ N' →
      (∫ z in Work.BoseK15.corpusBox.boxL (Work.BoseBoxFock.ellH v μ),
        ‖Work.BoseBoxFock.k1ErrA v μ fu N' Wa Wb z‖ ^ 2) ≤ ε := by
  intro ε hε
  have hℓ : 0 < ellH v μ := ellH_pos v μ
  obtain ⟨Ra, hRa⟩ := k1ExistsRadius hWas
  obtain ⟨Rb, hRb⟩ := k1ExistsRadius hWbs
  obtain ⟨N₁, hN₁⟩ :=
    k1RowSum_L2 (ℓ := ellH v μ) (R := Ra) hℓ fu hWam hWab hRa (ε / 4) (by linarith)
  obtain ⟨N₂, hN₂⟩ :=
    k1CubeSum_L2 (ℓ := ellH v μ) (R := Rb) hℓ hWbm hWbb hRb (ε / 4) (by linarith)
  refine ⟨max N₁ N₂, fun N' hN' => ?_⟩
  have hN'₁ : N₁ ≤ N' := le_trans (le_max_left _ _) hN'
  have hN'₂ : N₂ ≤ N' := le_trans (le_max_right _ _) hN'
  -- the two rows
  set f : E3 → ℂ :=
    fun z => rowSum (ellH v μ) fu N' Wa z - latPer3 (ellH v μ) Wa z with hf
  set g : E3 → ℂ :=
    fun z => k1Row (ellH v μ) N' (k1KinWt (ellH v μ) Wb) z
      - latPer3 (ellH v μ) Wb z with hg
  have hs : MeasurableSet (Work.BoseK15.corpusBox.boxL (ellH v μ)) :=
    Work.BoseK15.corpusBox.boxL_measurableSet _
  have hfin : volume (Work.BoseK15.corpusBox.boxL (ellH v μ)) < ⊤ := by
    rw [Work.BoseB4.BoxData.volume_boxL Work.BoseK15.corpusBox hℓ]
    exact ENNReal.ofReal_lt_top
  -- integrability of the two squared norms
  have hfi : Integrable (fun z => ‖f z‖ ^ 2)
      (volume.restrict (Work.BoseK15.corpusBox.boxL (ellH v μ))) := by
    rw [hf]
    obtain ⟨C1, _, hC1⟩ := errA_rowSum_bound (fu := fu) (N := N') hWae
    obtain ⟨C2, _, hC2⟩ := errA_latPer3_bound hℓ hWab hRa
    refine errA_integrableOn_normSq_of_bound hs hfin ?_ (C1 + C2) fun z hz => ?_
    · exact (errA_aesm_rowSum fu N' Wa).sub (errA_aesm_latPer3 hℓ hWam hRa)
    · calc ‖rowSum (ellH v μ) fu N' Wa z - latPer3 (ellH v μ) Wa z‖
          ≤ ‖rowSum (ellH v μ) fu N' Wa z‖ + ‖latPer3 (ellH v μ) Wa z‖ := norm_sub_le _ _
        _ ≤ C1 + C2 := add_le_add (hC1 z) (hC2 z hz)
  have hgi : Integrable (fun z => ‖g z‖ ^ 2)
      (volume.restrict (Work.BoseK15.corpusBox.boxL (ellH v μ))) := by
    rw [hg]
    obtain ⟨C1, _, hC1⟩ := errA_k1Row_bound (ℓ := ellH v μ) N' hWbe
    obtain ⟨C2, _, hC2⟩ := errA_latPer3_bound hℓ hWbb hRb
    refine errA_integrableOn_normSq_of_bound hs hfin ?_ (C1 + C2) fun z hz => ?_
    · exact ((errA_continuous_k1Row (ellH v μ) N' (k1KinWt (ellH v μ) Wb)).aestronglyMeasurable.restrict).sub
        (errA_aesm_latPer3 hℓ hWbm hRb)
    · calc ‖k1Row (ellH v μ) N' (k1KinWt (ellH v μ) Wb) z - latPer3 (ellH v μ) Wb z‖
          ≤ ‖k1Row (ellH v μ) N' (k1KinWt (ellH v μ) Wb) z‖ + ‖latPer3 (ellH v μ) Wb z‖ :=
            norm_sub_le _ _
        _ ≤ C1 + C2 := add_le_add (hC1 z) (hC2 z hz)
  -- the pointwise split
  have hid : ∀ z ∈ Work.BoseK15.corpusBox.boxL (ellH v μ),
      k1ErrA v μ fu N' Wa Wb z = f z + g z := by
    intro z hz
    rw [hf, hg]
    exact errA_eq_split fu N' hWae hWbe hRa hRb hz
  have hI1 : (∫ z in Work.BoseK15.corpusBox.boxL (ellH v μ), ‖f z‖ ^ 2) ≤ ε / 4 := by
    simpa only [hf] using hN₁ N' hN'₁
  have hI2 : (∫ z in Work.BoseK15.corpusBox.boxL (ellH v μ), ‖g z‖ ^ 2) ≤ ε / 4 := by
    simpa only [hg] using hN₂ N' hN'₂
  have hcongr : (∫ z in Work.BoseK15.corpusBox.boxL (ellH v μ),
        ‖k1ErrA v μ fu N' Wa Wb z‖ ^ 2)
      = ∫ z in Work.BoseK15.corpusBox.boxL (ellH v μ), ‖f z + g z‖ ^ 2 :=
    setIntegral_congr_fun hs fun z hz => by rw [hid z hz]
  rw [hcongr]
  calc (∫ z in Work.BoseK15.corpusBox.boxL (ellH v μ), ‖f z + g z‖ ^ 2)
      ≤ 2 * (∫ z in Work.BoseK15.corpusBox.boxL (ellH v μ), ‖f z‖ ^ 2)
        + 2 * (∫ z in Work.BoseK15.corpusBox.boxL (ellH v μ), ‖g z‖ ^ 2) :=
        errA_integral_normSq_add_le hfi hgi
    _ ≤ 2 * (ε / 4) + 2 * (ε / 4) := by linarith
    _ = ε := by ring

end Work.BoseBoxFock
