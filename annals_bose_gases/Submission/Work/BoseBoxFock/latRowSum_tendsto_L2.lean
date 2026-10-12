import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.latFourier_tendsto_periodisation
import Submission.Work.BoseBoxFock.latPartial_eq_latBall_sum
import Submission.Work.BoseBoxFock.latRowSum_coeff_tail
import Submission.Work.BoseBoxFock.latRowSum_parseval
import Submission.Work.BoseBoxFock.latTransfer_integral_real
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.latRowSum_tendsto_L2`

The finite lattice row sum `rowSum ℓ fu N W` of `Work.BoseBoxFock.rowSumDefs` — the `Lab N`-indexed
partial sum of the lattice Fourier series of `W`, cut off by the ultraviolet factor
`uvCut fu (uvRad ℓ N)` — converges, in `L²` of the centred corpus box
`corpusBox.boxL ℓ = [-ℓ/2,ℓ/2]³`, to `ℓ³` times the periodisation
`latPer ℓ W z = Σ'_m W(z + ℓ·latVec m)`.

## Route

The cut-off radius `uvRad ℓ N = (2π/ℓ)·N/4` is chosen so that `uvCut` equals `1` on the momentum
ball `{‖latVec n‖ ≤ N/4}` and vanishes for `‖latVec n‖ ≥ N/2`, while the labelling `Lab N` covers
exactly the lattice cube `cube N = [-N,N]³`.  Hence `rowSum - ballSum` is the `cube N`-indexed
character sum with the coefficients `rhoCoef`, supported in the annulus
`N/4 < ‖latVec n‖ < N/2`, and

* `‖rowSum - ℓ³latPer‖²_{L²(boxL)} = ‖rowSum - ℓ³latPer‖²_{L²(latBox)}`: both boxes are fundamental
  domains of the `ℓℤ³`-action and the integrand is invariant under it (`latTransfer_integral`);
* `‖rowSum - ℓ³latPer‖² ≤ 2‖rowSum - ballSum‖² + 2‖ballSum - ℓ³latPer‖²` pointwise;
* the first term is `ℓ³ Σ_{n ∈ cube N} ‖rhoCoef n‖²` by Parseval on the box
  (`latFinset_parseval_box`) and is bounded by the lattice tail
  `Σ'_{N/4 < ‖latVec n‖} ‖latFt n‖² → 0` (`kinFT_lattice_tail_sq_lt`);
* the second term is the `L²` distance of the partial sum of
  `Work.BoseBoxFock.latFourier_tendsto_periodisation` at the cut-off `Λ = uvRad ℓ N → ∞` to the
  periodisation, hence tends to `0`.
-/

noncomputable section

open MeasureTheory Filter
open scoped BigOperators

namespace Work.BoseBoxFock

open LatFourier

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## 0. The delegated pieces

These four propositions are proved in the sibling modules
`Work/BoseBoxFock/latTransfer_integral_real.lean`, `…/latPartial_eq_latBall_sum.lean`,
`…/latRowSum_parseval.lean`, `…/latRowSum_coeff_tail.lean` (they import `rowSumDefs`, not this
file).  They are restated here as private wrappers so that the assembly below can be written and
checked against them. -/

private theorem piece_transfer {ℓ : ℝ} (hℓ : 0 < ℓ) {f : E3 → ℝ}
    (hper : ∀ (m : Fin 3 → ℤ) (z : E3), f (z + ℓ • latVec m) = f z) :
    (∫ z in Work.BoseK15.corpusBox.boxL ℓ, f z) = ∫ z in latBox ℓ, f z :=
  latTransfer_integral_real hℓ hper

private theorem piece_latPartial {ℓ : ℝ} (hℓ : 0 < ℓ) (W : E3 → ℝ) (Λ : ℝ) (z : E3) :
    (∑' n : Fin 3 → ℤ,
        if ‖kmomInt ℓ n‖ ≤ Λ then
          Submission.BoseGases.kinFT (fun y => (W y : ℂ)) (kmomInt ℓ n)
            * Complex.exp (Complex.I * ((inner ℝ (kmomInt ℓ n) z : ℝ) : ℂ))
        else 0)
      = ∑ n ∈ latBall (Λ * ℓ / (2 * Real.pi)),
          Submission.BoseGases.kinFT (fun y => (W y : ℂ)) (kmomInt ℓ n)
            * Complex.exp (Complex.I * ((inner ℝ (kmomInt ℓ n) z : ℝ) : ℂ)) :=
  latPartial_eq_latBall_sum hℓ W Λ z

private theorem piece_parseval {ℓ : ℝ} (hℓ : 0 < ℓ) (fu : Work.BoseBoxFix.LowCut) (N : ℕ)
    (W : E3 → ℝ) :
    (∫ z in latBox ℓ, ‖rowSum ℓ fu N W z - ballSum ℓ N W z‖ ^ 2)
      = ℓ ^ 3 * ∑ n ∈ Work.BoseRowQ2.cube N, ‖rhoCoef ℓ fu N W n‖ ^ 2 :=
  latRowSum_parseval hℓ N W

private theorem piece_coeff_tail {ℓ : ℝ} (hℓ : 0 < ℓ) {fu : Work.BoseBoxFix.LowCut} {N : ℕ}
    (hN : 1 ≤ N) {W : E3 → ℝ}
    (hsumm : Summable (fun n : Fin 3 → ℤ => ‖latFt ℓ W n‖ ^ 2)) :
    (∑ n ∈ Work.BoseRowQ2.cube N, ‖rhoCoef ℓ fu N W n‖ ^ 2)
      ≤ ∑' n : Fin 3 → ℤ,
          (if (N : ℝ) / 4 < ‖latVec n‖ then ‖latFt ℓ W n‖ ^ 2 else 0) :=
  latRowSum_coeff_tail hℓ hN hsumm

/-! ## 1. The lattice character -/

/-- The lattice character `z ↦ e^{i⟪kmomInt ℓ n, z⟫}` has modulus one. -/
private lemma norm_latChr (ℓ : ℝ) (n : Fin 3 → ℤ) (z : E3) : ‖latChr ℓ n z‖ = 1 := by
  unfold latChr
  rw [mul_comm Complex.I ((inner ℝ (kmomInt ℓ n) z : ℝ) : ℂ), Complex.norm_exp_ofReal_mul_I]

/-- The lattice character is continuous. -/
private lemma continuous_latChr (ℓ : ℝ) (n : Fin 3 → ℤ) : Continuous (latChr ℓ n) := by
  unfold latChr
  fun_prop

/-! ## 2. The two arithmetic identifications -/

/-- The cut-off ball: `uvRad ℓ N · ℓ/(2π) = N/4`. -/
private lemma uvRad_mul (ℓ : ℝ) (N : ℕ) (hℓ : ℓ ≠ 0) :
    uvRad ℓ N * ℓ / (2 * Real.pi) = (N : ℝ) / 4 := by
  rw [uvRad]
  have hπ : (2 * Real.pi) ≠ 0 := by positivity
  field_simp

/-- `ballSum` is the partial sum of `latFourier_tendsto_periodisation` at the cut-off
`Λ = uvRad ℓ N`: the `latBall`-indexed sum. -/
private lemma ballSum_eq_finset (ℓ : ℝ) (N : ℕ) (hℓ : ℓ ≠ 0) (W : E3 → ℝ) (z : E3) :
    ballSum ℓ N W z
      = ∑ n ∈ latBall (uvRad ℓ N * ℓ / (2 * Real.pi)), latFt ℓ W n * latChr ℓ n z := by
  rw [ballSum, ← uvRad_mul ℓ N hℓ]

/-! ## 3. Periodicity of the row sum and of the periodisation -/

/-- The row sum is invariant under the lattice translations. -/
private lemma rowSum_add_latVec {ℓ : ℝ} (hℓ : 0 < ℓ) (fu : Work.BoseBoxFix.LowCut) (N : ℕ)
    (W : E3 → ℝ) (m : Fin 3 → ℤ) (z : E3) :
    rowSum ℓ fu N W (z + ℓ • latVec m) = rowSum ℓ fu N W z := by
  simp only [rowSum, latChr]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [exp_I_inner_add_latVec (ne_of_gt hℓ)]

/-- The periodisation is invariant under the lattice translations. -/
private lemma latPer_add_latVec {ℓ : ℝ} (hℓ : 0 < ℓ) (W : E3 → ℝ) (m : Fin 3 → ℤ) (z : E3) :
    latPer ℓ W (z + ℓ • latVec m) = latPer ℓ W z := by
  have hpt : ∀ n : Fin 3 → ℤ,
      z + ℓ • latVec m + ℓ • latVec n = z + ℓ • latVec (n + m) := by
    intro n
    rw [latVec_add, smul_add]
    abel
  have h1 : latPer ℓ W (z + ℓ • latVec m)
      = ∑' n : Fin 3 → ℤ, (W (z + ℓ • latVec (n + m)) : ℂ) := by
    simp only [latPer]
    exact tsum_congr fun n => by rw [hpt n]
  rw [h1]
  exact Equiv.tsum_eq (Equiv.addRight m) (fun n => (W (z + ℓ • latVec n) : ℂ))

/-! ## 4. The sibling theorem in `latBall` form -/

/-- `Work.BoseBoxFock.latFourier_tendsto_periodisation` with the `tsum`-with-indicator rewritten
as the finite `latBall`-sum. -/
private theorem latFourier_finset_tendsto {ℓ R : ℝ} (hℓ : 0 < ℓ) {W : E3 → ℝ}
    (hWm : AEStronglyMeasurable W volume) (hWb : ∃ C : ℝ, ∀ x, ‖W x‖ ≤ C)
    (hWs : ∀ x, R < ‖x‖ → W x = 0) :
    Tendsto (fun Λ : ℝ => ∫ z in latBox ℓ,
      ‖(∑ n ∈ latBall (Λ * ℓ / (2 * Real.pi)),
          Submission.BoseGases.kinFT (fun y => (W y : ℂ)) (kmomInt ℓ n)
            * Complex.exp (Complex.I * ((inner ℝ (kmomInt ℓ n) z : ℝ) : ℂ)))
        - (((ℓ ^ 3 : ℝ) : ℂ) * ∑' m : Fin 3 → ℤ, (W (z + ℓ • latVec m) : ℂ))‖ ^ 2)
      atTop (nhds 0) := by
  have hlim := latFourier_tendsto_periodisation (ℓ := ℓ) (R := R) hℓ hWm hWb hWs
  have hfun : (fun Λ : ℝ => ∫ z in {z : E3 | ∀ i : Fin 3, z.ofLp i ∈ Set.Icc (0 : ℝ) ℓ},
        ‖(∑' n : Fin 3 → ℤ,
            if ‖kmomInt ℓ n‖ ≤ Λ then
              Submission.BoseGases.kinFT (fun y => (W y : ℂ)) (kmomInt ℓ n)
                * Complex.exp (Complex.I * ((inner ℝ (kmomInt ℓ n) z : ℝ) : ℂ))
            else 0)
          - (((ℓ ^ 3 : ℝ) : ℂ) * ∑' m : Fin 3 → ℤ, (W (z + ℓ • latVec m) : ℂ))‖ ^ 2)
      = (fun Λ : ℝ => ∫ z in latBox ℓ,
        ‖(∑ n ∈ latBall (Λ * ℓ / (2 * Real.pi)),
            Submission.BoseGases.kinFT (fun y => (W y : ℂ)) (kmomInt ℓ n)
              * Complex.exp (Complex.I * ((inner ℝ (kmomInt ℓ n) z : ℝ) : ℂ)))
          - (((ℓ ^ 3 : ℝ) : ℂ) * ∑' m : Fin 3 → ℤ, (W (z + ℓ • latVec m) : ℂ))‖ ^ 2) := by
    funext Λ
    have hset : ({z : E3 | ∀ i : Fin 3, z.ofLp i ∈ Set.Icc (0 : ℝ) ℓ} : Set E3)
        = latBox ℓ := rfl
    rw [hset]
    refine setIntegral_congr_fun (measurableSet_latBox ℓ) fun z _ => ?_
    rw [piece_latPartial hℓ W Λ z]
  rw [hfun] at hlim
  exact hlim

/-! ## 5. Integrability on the closed cube -/

/-- A bounded, a.e. strongly measurable complex function has an integrable `‖·‖²` on the
(finite-measure) closed cube. -/
private lemma integrableOn_latBox_normSq {ℓ : ℝ} (hℓ : 0 < ℓ) {f : E3 → ℂ}
    (haesm : AEStronglyMeasurable f (volume.restrict (latBox ℓ)))
    (C : ℝ) (hC : ∀ z ∈ latBox ℓ, ‖f z‖ ≤ C) :
    Integrable (fun z => ‖f z‖ ^ 2) (volume.restrict (latBox ℓ)) := by
  haveI : IsFiniteMeasure (volume.restrict (latBox ℓ)) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ, MeasureTheory.measure_congr (latBox_ae_eq_latCell hℓ.le),
      volume_latCell hℓ.le]
    exact ENNReal.ofReal_lt_top
  refine MemLp.integrable (q := 2) (by norm_num) (MemLp.of_bound ?_ ((max C 0) ^ 2) ?_)
  · exact (haesm.norm.mul haesm.norm).congr
      (Eventually.of_forall (fun z => by simp [Pi.mul_apply, sq]))
  · rw [ae_restrict_iff' (measurableSet_latBox ℓ)]
    refine Eventually.of_forall fun z hz => ?_
    have h1 : ‖f z‖ ≤ max C 0 := le_trans (hC z hz) (le_max_left C 0)
    have h0 : 0 ≤ ‖f z‖ := norm_nonneg _
    rw [Real.norm_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ h0 h1 2

/-- The periodisation is a.e. strongly measurable on the closed cube. -/
private lemma latPer_aesm_latBox {ℓ R : ℝ} (hℓ : 0 < ℓ) {W : E3 → ℝ}
    (hWm : AEStronglyMeasurable W volume) (hWs : ∀ x, R < ‖x‖ → W x = 0) :
    AEStronglyMeasurable (latPer ℓ W) (volume.restrict (latBox ℓ)) :=
  ((latPerCut_aestronglyMeasurable hℓ hWm hWs).restrict (s := latBox ℓ)).congr
    ((ae_restrict_iff' (s := latBox ℓ) (measurableSet_latBox ℓ)).mpr
      (Eventually.of_forall fun z hz => by rw [latPerCut, Set.indicator_of_mem hz]))

/-! ## 6. Norm bounds for the two partial sums -/

/-- Uniform bound for the row sum. -/
private lemma norm_rowSum_le (ℓ : ℝ) (fu : Work.BoseBoxFix.LowCut) (N : ℕ) (W : E3 → ℝ)
    (z : E3) :
    ‖rowSum ℓ fu N W z‖ ≤ ∑ k : Lab N,
      ‖((uvCut fu (uvRad ℓ N) (kmomLab ℓ N k) : ℝ) : ℂ)
        * Submission.BoseGases.kinFT (fun y => (W y : ℂ)) (kmomLab ℓ N k)‖ := by
  rw [rowSum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [norm_mul, norm_latChr, mul_one]

/-- Uniform bound for the momentum-ball sum. -/
private lemma norm_ballSum_le (ℓ : ℝ) (N : ℕ) (W : E3 → ℝ) (z : E3) :
    ‖ballSum ℓ N W z‖ ≤ ∑ n ∈ latBall ((N : ℝ) / 4), ‖latFt ℓ W n‖ := by
  rw [ballSum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
  rw [norm_mul, norm_latChr, mul_one]

/-! ## 7. The target -/

theorem latRowSum_tendsto_L2 {ℓ R : ℝ} (hℓ : 0 < ℓ) (fu : Work.BoseBoxFix.LowCut)
    {W : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hWm : MeasureTheory.AEStronglyMeasurable W MeasureTheory.volume)
    (hWb : ∃ C : ℝ, ∀ x, ‖W x‖ ≤ C) (hWs : ∀ x, R < ‖x‖ → W x = 0) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ N' : ℕ, N ≤ N' →
      (∫ z in Work.BoseK15.corpusBox.boxL ℓ,
        ‖(∑ k : Work.BoseBoxFock.Lab N',
              ((Work.BoseBoxFock.uvCut fu (Work.BoseBoxFock.uvRad ℓ N')
                  (Work.BoseBoxFock.kmomLab ℓ N' k) : ℝ) : ℂ)
                * Submission.BoseGases.kinFT (fun y => (W y : ℂ))
                    (Work.BoseBoxFock.kmomLab ℓ N' k)
                * Complex.exp (Complex.I *
                    ((inner ℝ (Work.BoseBoxFock.kmomLab ℓ N' k) z : ℝ) : ℂ)))
          - (((ℓ ^ 3 : ℝ) : ℂ)
              * ∑' m : Fin 3 → ℤ, ((W (z + ℓ • Work.BoseBoxFock.latVec m) : ℝ) : ℂ))‖ ^ 2)
      ≤ ε := by
  classical
  intro ε hε
  -- the `ℂ`-valued formulation of `W`
  have hWc_bdd : ∃ C : ℝ, ∀ x : E3, ‖((W x : ℝ) : ℂ)‖ ≤ C :=
    ⟨hWb.choose, fun x => by simpa using hWb.choose_spec x⟩
  have hWc_supp : ∀ x : E3, R < ‖x‖ → ((W x : ℝ) : ℂ) = 0 := fun x hx => by
    rw [hWs x hx]; norm_num
  have hWc_aesm : AEStronglyMeasurable (fun x : E3 => ((W x : ℝ) : ℂ)) volume :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable hWm
  have hsumm : Summable (fun n : Fin 3 → ℤ => ‖latFt ℓ W n‖ ^ 2) :=
    summable_kinFT_lattice_of_bounded (ℓ := ℓ) (R := R) hℓ hWc_bdd hWc_supp hWc_aesm
  -- the sibling convergence, at level `ε/4`
  obtain ⟨Λ₀, hΛ₀⟩ := Filter.eventually_atTop.mp
    ((latFourier_finset_tendsto (ℓ := ℓ) (R := R) hℓ hWm hWb hWs).eventually
      (Metric.ball_mem_nhds (0 : ℝ) (by positivity : (0 : ℝ) < ε / 4)))
  -- the lattice tail, at level `ε/(4ℓ³)`
  obtain ⟨Λ₁, hΛ₁⟩ :=
    kinFT_lattice_tail_sq_lt (ℓ := ℓ) (R := R) hℓ hWb hWs (ε / (4 * ℓ ^ 3)) (by positivity)
  -- the lattice size: large enough for both cut-offs and for `N ≥ 1`
  obtain ⟨N₀, hN₀⟩ := exists_nat_ge (max (max Λ₀ Λ₁ * (4 * ℓ / (2 * Real.pi))) 1)
  refine ⟨N₀, fun N' hN' => ?_⟩
  have hN'1 : (1 : ℝ) ≤ (N' : ℝ) :=
    le_trans (le_trans (le_max_right _ _) hN₀) (by exact_mod_cast hN')
  have hN'nat : 1 ≤ N' := by exact_mod_cast hN'1
  have hKN' : max Λ₀ Λ₁ ≤ uvRad ℓ N' := by
    have hc : (0 : ℝ) < 4 * ℓ / (2 * Real.pi) := by positivity
    have h1 : max Λ₀ Λ₁ * (4 * ℓ / (2 * Real.pi)) ≤ (N' : ℝ) :=
      le_trans (le_trans (le_max_left _ _) hN₀) (by exact_mod_cast hN')
    have h2 : max Λ₀ Λ₁ ≤ (N' : ℝ) / (4 * ℓ / (2 * Real.pi)) := (le_div_iff₀ hc).mpr h1
    have h3 : (N' : ℝ) / (4 * ℓ / (2 * Real.pi)) = uvRad ℓ N' := by
      rw [uvRad]
      have hπ : (2 * Real.pi) ≠ 0 := by positivity
      field_simp
    linarith [h2, h3]
  have hΛ₀le : Λ₀ ≤ uvRad ℓ N' := le_trans (le_max_left Λ₀ Λ₁) hKN'
  have hΛ₁le : Λ₁ ≤ uvRad ℓ N' := le_trans (le_max_right Λ₀ Λ₁) hKN'
  -- rewrite the goal in the vocabulary of `rowSumDefs`
  change (∫ z in Work.BoseK15.corpusBox.boxL ℓ,
      ‖rowSum ℓ fu N' W z - (((ℓ ^ 3 : ℝ) : ℂ) * latPer ℓ W z)‖ ^ 2) ≤ ε
  -- the transfer to the corner cube
  have hper : ∀ (m : Fin 3 → ℤ) (z : E3),
      ‖rowSum ℓ fu N' W (z + ℓ • latVec m)
        - (((ℓ ^ 3 : ℝ) : ℂ) * latPer ℓ W (z + ℓ • latVec m))‖ ^ 2
        = ‖rowSum ℓ fu N' W z - (((ℓ ^ 3 : ℝ) : ℂ) * latPer ℓ W z)‖ ^ 2 := by
    intro m z
    rw [rowSum_add_latVec hℓ fu N' W m z, latPer_add_latVec hℓ W m z]
  rw [piece_transfer hℓ hper]
  -- the range bound for `latPer` on the cube
  obtain ⟨D, hD0, hD⟩ := latPer_bdd (ℓ := ℓ) (R := R) hℓ hWb hWs
  -- the two pieces of the split are integrable
  have hcontS : Continuous (rowSum ℓ fu N' W) := by
    unfold rowSum
    exact continuous_finsetSum _ fun k _ =>
      (continuous_const.mul continuous_const).mul (continuous_latChr ℓ (labVec N' k))
  have hcontP : Continuous (ballSum ℓ N' W) := by
    unfold ballSum
    exact continuous_finsetSum _ fun n _ => continuous_const.mul (continuous_latChr ℓ n)
  have hintSP : Integrable (fun z => ‖rowSum ℓ fu N' W z - ballSum ℓ N' W z‖ ^ 2)
      (volume.restrict (latBox ℓ)) :=
    integrableOn_latBox_normSq hℓ ((hcontS.sub hcontP).aestronglyMeasurable.restrict)
      (((∑ k : Lab N', ‖((uvCut fu (uvRad ℓ N') (kmomLab ℓ N' k) : ℝ) : ℂ)
            * Submission.BoseGases.kinFT (fun y => (W y : ℂ)) (kmomLab ℓ N' k)‖)
          + ∑ n ∈ latBall ((N' : ℝ) / 4), ‖latFt ℓ W n‖))
      (fun z _ => le_trans (norm_sub_le _ _)
        (add_le_add (norm_rowSum_le ℓ fu N' W z) (norm_ballSum_le ℓ N' W z)))
  have hintPG : Integrable
      (fun z => ‖ballSum ℓ N' W z - (((ℓ ^ 3 : ℝ) : ℂ) * latPer ℓ W z)‖ ^ 2)
      (volume.restrict (latBox ℓ)) :=
    integrableOn_latBox_normSq hℓ
      ((hcontP.aestronglyMeasurable.restrict).sub
        ((latPer_aesm_latBox (ℓ := ℓ) (R := R) hℓ hWm hWs).const_mul _))
      ((∑ n ∈ latBall ((N' : ℝ) / 4), ‖latFt ℓ W n‖) + ‖(((ℓ ^ 3 : ℝ) : ℂ))‖ * D)
      (fun z hz => by
        refine le_trans (norm_sub_le _ _) (add_le_add (norm_ballSum_le ℓ N' W z) ?_)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hD z hz) (norm_nonneg _))
  -- the pointwise split
  have hsplit : ∀ z : E3,
      ‖rowSum ℓ fu N' W z - (((ℓ ^ 3 : ℝ) : ℂ) * latPer ℓ W z)‖ ^ 2
        ≤ 2 * ‖rowSum ℓ fu N' W z - ballSum ℓ N' W z‖ ^ 2
          + 2 * ‖ballSum ℓ N' W z - (((ℓ ^ 3 : ℝ) : ℂ) * latPer ℓ W z)‖ ^ 2 := by
    intro z
    rw [show rowSum ℓ fu N' W z - (((ℓ ^ 3 : ℝ) : ℂ) * latPer ℓ W z)
        = (rowSum ℓ fu N' W z - ballSum ℓ N' W z)
          + (ballSum ℓ N' W z - (((ℓ ^ 3 : ℝ) : ℂ) * latPer ℓ W z)) by ring]
    calc ‖(rowSum ℓ fu N' W z - ballSum ℓ N' W z)
            + (ballSum ℓ N' W z - (((ℓ ^ 3 : ℝ) : ℂ) * latPer ℓ W z))‖ ^ 2
        ≤ (‖rowSum ℓ fu N' W z - ballSum ℓ N' W z‖
            + ‖ballSum ℓ N' W z - (((ℓ ^ 3 : ℝ) : ℂ) * latPer ℓ W z)‖) ^ 2 :=
          pow_le_pow_left₀ (by positivity) (norm_add_le _ _) 2
      _ ≤ 2 * (‖rowSum ℓ fu N' W z - ballSum ℓ N' W z‖ ^ 2
            + ‖ballSum ℓ N' W z - (((ℓ ^ 3 : ℝ) : ℂ) * latPer ℓ W z)‖ ^ 2) :=
          add_sq_le
      _ = 2 * ‖rowSum ℓ fu N' W z - ballSum ℓ N' W z‖ ^ 2
            + 2 * ‖ballSum ℓ N' W z - (((ℓ ^ 3 : ℝ) : ℂ) * latPer ℓ W z)‖ ^ 2 := by ring
  -- the two estimates
  have htail : (∑' n : Fin 3 → ℤ,
        (if (N' : ℝ) / 4 < ‖latVec n‖ then ‖latFt ℓ W n‖ ^ 2 else 0)) ≤ ε / (4 * ℓ ^ 3) := by
    refine le_trans ?_ (hΛ₁ (uvRad ℓ N') hΛ₁le)
    refine Summable.tsum_le_tsum (f := fun n : Fin 3 → ℤ =>
        if (N' : ℝ) / 4 < ‖latVec n‖ then ‖latFt ℓ W n‖ ^ 2 else 0)
      (g := fun n : Fin 3 → ℤ =>
        if uvRad ℓ N' ≤ ‖kmomInt ℓ n‖ then ‖latFt ℓ W n‖ ^ 2 else 0) (fun n => ?_) ?_ ?_
    · by_cases hc : (N' : ℝ) / 4 < ‖latVec n‖
      · rw [if_pos hc]
        have h2 : uvRad ℓ N' ≤ ‖kmomInt ℓ n‖ := by
          rw [kmomInt_eq_smul_latVec, norm_smul,
            Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi / ℓ), uvRad]
          have hlt := mul_lt_mul_of_pos_left hc
            (by positivity : (0 : ℝ) < 2 * Real.pi / ℓ)
          linarith [hlt]
        rw [if_pos h2]
      · rw [if_neg hc]
        positivity
    · exact Summable.of_nonneg_of_le (fun n => by split_ifs <;> positivity)
        (fun n => by split_ifs <;> simp) hsumm
    · exact Summable.of_nonneg_of_le (fun n => by split_ifs <;> positivity)
        (fun n => by split_ifs <;> simp) hsumm
  have hSP : (∫ z in latBox ℓ, ‖rowSum ℓ fu N' W z - ballSum ℓ N' W z‖ ^ 2) ≤ ε / 4 := by
    rw [piece_parseval (ℓ := ℓ) hℓ fu N' W]
    have h1 : (∑ n ∈ Work.BoseRowQ2.cube N', ‖rhoCoef ℓ fu N' W n‖ ^ 2) ≤ ε / (4 * ℓ ^ 3) :=
      le_trans (piece_coeff_tail (ℓ := ℓ) hℓ (fu := fu) hN'nat hsumm) htail
    calc ℓ ^ 3 * (∑ n ∈ Work.BoseRowQ2.cube N', ‖rhoCoef ℓ fu N' W n‖ ^ 2)
        ≤ ℓ ^ 3 * (ε / (4 * ℓ ^ 3)) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = ε / 4 := by
          field_simp
  have hPG : (∫ z in latBox ℓ, ‖ballSum ℓ N' W z - (((ℓ ^ 3 : ℝ) : ℂ) * latPer ℓ W z)‖ ^ 2)
      ≤ ε / 4 := by
    have h := hΛ₀ (uvRad ℓ N') hΛ₀le
    beta_reduce at h
    have heq : (∫ z in latBox ℓ,
          ‖(∑ n ∈ latBall (uvRad ℓ N' * ℓ / (2 * Real.pi)),
              Submission.BoseGases.kinFT (fun y => (W y : ℂ)) (kmomInt ℓ n)
                * Complex.exp (Complex.I * ((inner ℝ (kmomInt ℓ n) z : ℝ) : ℂ)))
            - (((ℓ ^ 3 : ℝ) : ℂ) * ∑' m : Fin 3 → ℤ, (W (z + ℓ • latVec m) : ℂ))‖ ^ 2)
        = ∫ z in latBox ℓ,
            ‖ballSum ℓ N' W z - (((ℓ ^ 3 : ℝ) : ℂ) * latPer ℓ W z)‖ ^ 2 := by
      refine setIntegral_congr_fun (measurableSet_latBox ℓ) fun z _ => ?_
      rw [uvRad_mul ℓ N' (ne_of_gt hℓ)]
      simp only [ballSum, latFt, latChr, latPer]
    rw [heq] at h
    rw [Real.dist_eq, sub_zero] at h
    rw [abs_of_nonneg (integral_nonneg fun z => by positivity)] at h
    exact h.le
  -- the assembly
  have hstep1 : (∫ z in latBox ℓ,
        ‖rowSum ℓ fu N' W z - (((ℓ ^ 3 : ℝ) : ℂ) * latPer ℓ W z)‖ ^ 2)
      ≤ ∫ z in latBox ℓ, (2 * ‖rowSum ℓ fu N' W z - ballSum ℓ N' W z‖ ^ 2
          + 2 * ‖ballSum ℓ N' W z - (((ℓ ^ 3 : ℝ) : ℂ) * latPer ℓ W z)‖ ^ 2) :=
    integral_mono_of_nonneg (Eventually.of_forall fun z => by positivity)
      ((hintSP.const_mul 2).add (hintPG.const_mul 2))
      (Eventually.of_forall hsplit)
  have hstep2 : (∫ z in latBox ℓ, (2 * ‖rowSum ℓ fu N' W z - ballSum ℓ N' W z‖ ^ 2
          + 2 * ‖ballSum ℓ N' W z - (((ℓ ^ 3 : ℝ) : ℂ) * latPer ℓ W z)‖ ^ 2))
      = 2 * (∫ z in latBox ℓ, ‖rowSum ℓ fu N' W z - ballSum ℓ N' W z‖ ^ 2)
        + 2 * (∫ z in latBox ℓ,
            ‖ballSum ℓ N' W z - (((ℓ ^ 3 : ℝ) : ℂ) * latPer ℓ W z)‖ ^ 2) := by
    rw [integral_add (hintSP.const_mul 2) (hintPG.const_mul 2), integral_const_mul,
      integral_const_mul]
  calc (∫ z in latBox ℓ,
        ‖rowSum ℓ fu N' W z - (((ℓ ^ 3 : ℝ) : ℂ) * latPer ℓ W z)‖ ^ 2)
      ≤ ∫ z in latBox ℓ, (2 * ‖rowSum ℓ fu N' W z - ballSum ℓ N' W z‖ ^ 2
          + 2 * ‖ballSum ℓ N' W z - (((ℓ ^ 3 : ℝ) : ℂ) * latPer ℓ W z)‖ ^ 2) := hstep1
    _ = 2 * (∫ z in latBox ℓ, ‖rowSum ℓ fu N' W z - ballSum ℓ N' W z‖ ^ 2)
        + 2 * (∫ z in latBox ℓ,
            ‖ballSum ℓ N' W z - (((ℓ ^ 3 : ℝ) : ℂ) * latPer ℓ W z)‖ ^ 2) := hstep2
    _ ≤ 2 * (ε / 4) + 2 * (ε / 4) := by linarith [hSP, hPG]
    _ = ε := by ring

end Work.BoseBoxFock
