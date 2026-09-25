import Mathlib
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.NN.Core.CnPert
import Submission.Work.NN.Core.Lev.moserTheta
import Submission.Work.NN.Core.Lev.gnsLipschitzOn
import Submission.Work.NN.Core.Lev.realMoserStep
import Submission.Work.NN.Core.Value.moser_sup_le_L2_core
import Submission.Work.NN.Core.volume_polydisc

set_option maxHeartbeats 2000000

namespace Work.NN.Core.Lev2

open MeasureTheory Set Filter
open scoped NNReal ENNReal ContDiff Topology

noncomputable section


/-- A function vanishing off the topological support of a function is `0` near a point outside it. -/
private lemma tsupport_eventuallyEq_zero {n : ℕ} {f : Work.NN.Core.Cn n → ℝ}
    {z : Work.NN.Core.Cn n} (hz : z ∉ tsupport f) : f =ᶠ[𝓝 z] 0 := by
  filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hz] with y hy
  exact Function.notMem_support.mp fun hys => hy (subset_closure hys)

/-- A real-valued function that is a.e. strongly measurable, bounded by `C` and vanishes off a
compact set is integrable. -/
private lemma integrable_of_vanishes_off_compact {n : ℕ} {F : Work.NN.Core.Cn n → ℝ} {C : ℝ}
    {K : Set (Work.NN.Core.Cn n)} (hF : AEStronglyMeasurable F volume) (_hC : 0 ≤ C)
    (hK : IsCompact K) (hvan : ∀ z ∉ K, F z = 0) (hbd : ∀ z, |F z| ≤ C) :
    Integrable F volume := by
  have hKmeas : MeasurableSet K := hK.isClosed.measurableSet
  have hg : Integrable (fun z => C * (K.indicator (fun _ => (1:ℝ)) z)) volume :=
    (MeasureTheory.IntegrableOn.integrable_indicator
      (MeasureTheory.integrableOn_const (ne_of_lt hK.measure_lt_top)) hKmeas).const_mul C
  refine Integrable.mono' hg hF ?_
  filter_upwards with z
  rw [Real.norm_eq_abs]
  by_cases hz : z ∈ K
  · rw [Set.indicator_of_mem hz]; simp only [mul_one]; exact hbd z
  · rw [hvan z hz, abs_zero, Set.indicator_of_notMem hz, mul_zero]

/-- **Sourced Moser boost, Lipschitz real weight.**  `W : ℂⁿ → ℝ` Lipschitz on the polydisc of
multiradius `ρ`, `Λ ≤ W` everywhere, and the *sourced* integer-level power Caccioppoli family at a
single constant `A` give the Moser boost `‖W‖_{L^{2k(2n)'}(Pd r)} ≤ (C(1+L)(1+k))^{1/(2k)}
‖W‖_{L^{2k}(Pd s)}` for `r ⊂⊂ s ⊂⊂ ρ` and cutoffs `χ` (`=1` on the closed `r`-polydisc, supported
in `Pd s`, `‖∇χ‖ ≤ L`).

NOTE ON THE HYPOTHESIS.  It is the *correctly parenthesised* sourced Caccioppoli: each of the two
integrals on the right sits inside its own parentheses,
`A * (k²Λ² * (∫ φ²W^{2k-2}) + (∫ ‖∇φ‖²W^{2k}))`.  Beware: in `Lev2/ScratchBoost.lean`
(the private declaration `srcBoostLip`) and in `Lev/sourcedChainLipschitz.lean` the same-looking
hypothesis is written with the second `∫` *not* wrapped, so it parses as a single integral of a sum
(`∫ z, (φ²W^{2k-2} + ∫ …)`) — that is a different, generally weaker hypothesis; do not copy the
use of `hH` from those files without checking.

PROOF PLAN (template `Lev/lipMoserBoost.lean`, sorry-free, unsourced case):
from `Λ ≤ W` and `Λ ≥ 0` get `Λ²W^{2k-2} ≤ W^{2k}`, so the hypothesis gives
`∫χ²‖∇(W^k)‖² ≤ A(k²+L²)∫_{Pd s}W^{2k}`, whence `∫‖∇(χW^k)‖² ≤ 2(A+1)(k²+L²)∫_{Pd s}W^{2k}`
(Leibniz + `eLpNorm` of `fderiv`); Gagliardo–Nirenberg for Lipschitz `χW^k`
(`Work.NN.Core.gagliardoNirenbergGeomMean` / `gnsLipschitzOn`) then gives
`eLpNorm (W^k) (2(2n)') (Pd r) ≤ √(C_GN·√(2(A+1))(k+L))·eLpNorm (W^k) 2 (Pd s)`, and taking the
`1/k`-th power (`k ≥ 1`, `√(k²+L²) ≤ k+L ≤ (1+k)(1+L)`) yields the claim. -/
theorem srcMoserBoost {n : ℕ} (hn : 0 < n) {A : ℝ} (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {ρ : Fin n → ℝ}, (∀ j, 0 < ρ j) → ∀ {Λ : ℝ}, 0 ≤ Λ →
      ∀ {K : NNReal} {W : Work.NN.Core.Cn n → ℝ},
        LipschitzOnWith K W (Work.CR.Flat.polydisc 0 ρ) → (∀ z, Λ ≤ W z) →
        (∀ (k : ℕ), 1 ≤ k → ∀ (φ : Work.NN.Core.Cn n → ℝ),
          ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
          tsupport φ ⊆ Work.CR.Flat.polydisc 0 ρ → (∀ z, 0 ≤ φ z) →
          ∫ z in Work.CR.Flat.polydisc 0 ρ, (φ z)^2 * ‖fderiv ℝ (fun w => (W w)^k) z‖^2
            ≤ A * ((k:ℝ)^2 * Λ^2 * (∫ z in Work.CR.Flat.polydisc 0 ρ, (φ z)^2 * (W z)^(2*k-2))
                  + (∫ z in Work.CR.Flat.polydisc 0 ρ, ‖fderiv ℝ φ z‖^2 * (W z)^(2*k)))) →
        ∀ {r s : Fin n → ℝ}, (∀ j, r j < s j) → (∀ j, s j < ρ j) →
        ∀ {χ : Work.NN.Core.Cn n → ℝ}, ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ →
          tsupport χ ⊆ Work.CR.Flat.polydisc 0 s → (∀ z, 0 ≤ χ z) → (∀ z, χ z ≤ 1) →
          (∀ z, (∀ j, ‖z j‖ ≤ r j) → χ z = 1) →
        ∀ {L : ℝ}, 0 ≤ L → (∀ z, ‖fderiv ℝ χ z‖ ≤ L) →
        ∀ (k : ℕ), 1 ≤ k →
          MeasureTheory.eLpNorm W
              (ENNReal.ofReal (2 * ((k : ℝ) * Work.NN.Core.Lev.moserTheta n)))
              (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 r))
            ≤ (ENNReal.ofReal (C * (1 + L) * (1 + (k : ℝ)))) ^ (1 / (2 * (k : ℝ))) *
              MeasureTheory.eLpNorm W (ENNReal.ofReal (2 * (k : ℝ)))
                (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 s)) := by
  obtain ⟨Cgns, hCgns, hGNS⟩ := Work.NN.Core.Lev.gnsLipschitzOn hn
  set Cc : ℝ := Cgns * (2 * (A + 1)) + 1 with hCcdef
  have hCcpos : 0 < Cc := by rw [hCcdef]; positivity
  refine ⟨Cc, hCcpos, ?_⟩
  intro ρ hρ Λ hΛ K W hLip hWle hH r s hrs hsρ χ hχcd hχcs hχsupp hχnn hχle1 hχ1 L hL0 hχL k hk
  set v : Work.NN.Core.Cn n → ℝ := fun z => (W z)^k with hv
  set G : Work.NN.Core.Cn n → ℝ := fun z => χ z * v z with hG
  -- closed polydisc of radius s: compact, contained in Pd ρ
  have hcs_compact : IsCompact {z : Work.NN.Core.Cn n | ∀ j, ‖z j‖ ≤ s j} := by
    have heq : {z : Work.NN.Core.Cn n | ∀ j, ‖z j‖ ≤ s j}
        = Set.univ.pi (fun j => Metric.closedBall (0:ℂ) (s j)) := by
      ext z; simp [Metric.mem_closedBall, dist_eq_norm]
    rw [heq]
    exact isCompact_univ_pi (fun j => isCompact_closedBall 0 (s j))
  have hcs_sub : {z : Work.NN.Core.Cn n | ∀ j, ‖z j‖ ≤ s j} ⊆ Work.CR.Flat.polydisc 0 ρ :=
    fun z hz => by
      rw [Work.CR.Flat.mem_polydisc]
      intro j
      simpa using lt_of_le_of_lt (hz j) (hsρ j)
  obtain ⟨M0, hM0⟩ :=
    hcs_compact.exists_bound_of_continuousOn (hLip.continuousOn.mono hcs_sub)
  set M : ℝ := max M0 0 with hMdef
  have hMnn : 0 ≤ M := le_max_right _ _
  have hMW : ∀ z, (∀ j, ‖z j‖ ≤ s j) → |W z| ≤ M := fun z hz =>
    by
      have h1 : ‖W z‖ ≤ M0 := hM0 z hz
      rw [← Real.norm_eq_abs]
      exact le_trans h1 (le_max_left _ _)
  -- Lipschitz continuity of χ
  have hχdiff : Differentiable ℝ χ := hχcd.differentiable (by simp)
  set Lnn : NNReal := ⟨L, hL0⟩ with hLnndef
  have hLnn : (Lnn : ℝ) = L := by rw [hLnndef]; rfl
  have hχlip : LipschitzWith Lnn χ :=
    lipschitzWith_of_nnnorm_fderiv_le hχdiff (fun z => by
      rw [← NNReal.coe_le_coe, hLnn]
      simpa using hχL z)
  -- Lipschitz constant of G on Pd s
  have hG_lip : LipschitzOnWith ⟨(k:ℝ) * M^(k-1) * (K:ℝ) + M^k * L, by positivity⟩ G
      (Work.CR.Flat.polydisc 0 s) := by
    refine LipschitzOnWith.of_dist_le_mul (fun x hx y hy => ?_)
    rw [Real.dist_eq]
    have hdist : dist x y = ‖x - y‖ := dist_eq_norm x y
    rw [hdist]
    have hxρ : x ∈ Work.CR.Flat.polydisc 0 ρ :=
      Work.CR.Flat.polydisc_mono (fun j => (hsρ j).le) hx
    have hyρ : y ∈ Work.CR.Flat.polydisc 0 ρ :=
      Work.CR.Flat.polydisc_mono (fun j => (hsρ j).le) hy
    have hxs : ∀ j, ‖x j‖ ≤ s j := fun j => le_of_lt (by simpa using hx j)
    have hys : ∀ j, ‖y j‖ ≤ s j := fun j => le_of_lt (by simpa using hy j)
    have hxy : |W x - W y| ≤ (K:ℝ) * ‖x - y‖ := by
      have h := hLip.dist_le_mul x hxρ y hyρ
      rwa [Real.dist_eq, dist_eq_norm] at h
    have hMx : |W x| ≤ M := hMW x hxs
    have hMy : |W y| ≤ M := hMW y hys
    have hmax : max |W x| |W y| ≤ M := max_le hMx hMy
    have hmaxp : (max |W x| |W y|) ^ (k-1) ≤ M ^ (k-1) :=
      pow_le_pow_left₀ (le_trans (abs_nonneg _) (le_max_left _ _)) hmax (k-1)
    have hp : |(W x)^k - (W y)^k| ≤ (k:ℝ) * M^(k-1) * ((K:ℝ) * ‖x - y‖) := by
      have h := abs_pow_sub_pow_le (W x) (W y) k
      have h2 : |W x - W y| * (k:ℝ) * (max |W x| |W y|) ^ (k-1)
          ≤ ((K:ℝ) * ‖x - y‖) * (k:ℝ) * M ^ (k-1) := by
        gcongr
      calc |(W x)^k - (W y)^k|
          ≤ |W x - W y| * (k:ℝ) * (max |W x| |W y|) ^ (k-1) := by
            simpa only [mul_assoc] using h
        _ ≤ ((K:ℝ) * ‖x - y‖) * (k:ℝ) * M ^ (k-1) := h2
        _ = (k:ℝ) * M^(k-1) * ((K:ℝ) * ‖x - y‖) := by ring
    have hχa : |χ x| ≤ 1 := by rw [abs_of_nonneg (hχnn x)]; exact hχle1 x
    have hWyk : |(W y)^k| ≤ M^k := by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hMy k
    have hχd : |χ x - χ y| ≤ L * ‖x - y‖ := by
      have h := hχlip.dist_le_mul x y
      rw [Real.dist_eq, hLnn, hdist] at h
      exact h
    have hsplit : χ x * (W x)^k - χ y * (W y)^k
        = χ x * ((W x)^k - (W y)^k) + (W y)^k * (χ x - χ y) := by ring
    rw [hsplit]
    calc |χ x * ((W x)^k - (W y)^k) + (W y)^k * (χ x - χ y)|
        ≤ |χ x * ((W x)^k - (W y)^k)| + |(W y)^k * (χ x - χ y)| := abs_add_le _ _
      _ = |χ x| * |(W x)^k - (W y)^k| + |(W y)^k| * |χ x - χ y| := by rw [abs_mul, abs_mul]
      _ ≤ 1 * ((k:ℝ) * M^(k-1) * ((K:ℝ) * ‖x - y‖)) + M^k * (L * ‖x - y‖) := by
          gcongr
      _ = ((k:ℝ) * M^(k-1) * (K:ℝ) + M^k * L) * ‖x - y‖ := by ring
  -- support of G
  have htsupp_G : tsupport G ⊆ Work.CR.Flat.polydisc 0 s := by
    have h1 : Function.support G ⊆ Function.support χ := by
      intro z hz
      rw [Function.mem_support] at hz ⊢
      intro hχ0
      exact hz (by rw [hG]; simp [hχ0])
    exact (closure_mono h1).trans (by
      have := hχsupp
      rwa [tsupport] at this)
  -- Lipschitz constant of v = W^k on Pd s
  set Lv : ℝ := (k:ℝ) * M^(k-1) * (K:ℝ) with hLvdef
  have hv_lip : LipschitzOnWith ⟨Lv, by positivity⟩ v (Work.CR.Flat.polydisc 0 s) := by
    refine LipschitzOnWith.of_dist_le_mul (fun x hx y hy => ?_)
    rw [Real.dist_eq]
    have hdist : dist x y = ‖x - y‖ := dist_eq_norm x y
    rw [hdist]
    have hxs : ∀ j, ‖x j‖ ≤ s j := fun j => le_of_lt (by simpa using hx j)
    have hys : ∀ j, ‖y j‖ ≤ s j := fun j => le_of_lt (by simpa using hy j)
    have hxρ : x ∈ Work.CR.Flat.polydisc 0 ρ :=
      Work.CR.Flat.polydisc_mono (fun j => (hsρ j).le) hx
    have hyρ : y ∈ Work.CR.Flat.polydisc 0 ρ :=
      Work.CR.Flat.polydisc_mono (fun j => (hsρ j).le) hy
    have hxy : |W x - W y| ≤ (K:ℝ) * ‖x - y‖ := by
      have h := hLip.dist_le_mul x hxρ y hyρ
      rw [Real.dist_eq, dist_eq_norm] at h; exact h
    have hMx : |W x| ≤ M := hMW x hxs
    have hMy : |W y| ≤ M := hMW y hys
    have h := abs_pow_sub_pow_le (W x) (W y) k
    have hmaxp : (max |W x| |W y|) ^ (k-1) ≤ M^(k-1) :=
      pow_le_pow_left₀ (le_trans (abs_nonneg _) (le_max_left _ _)) (max_le hMx hMy) (k-1)
    have h2 : |W x - W y| * (k:ℝ) * (max |W x| |W y|) ^ (k-1) ≤ (K:ℝ) * ‖x - y‖ * (k:ℝ) * M^(k-1) := by
      have hk0 : (0:ℝ) ≤ (k:ℝ) := by positivity
      exact mul_le_mul (mul_le_mul_of_nonneg_right hxy hk0) hmaxp (by positivity) (by positivity)
    have hvxy : v x - v y = (W x)^k - (W y)^k := by rw [hv]
    rw [hvxy]
    calc |(W x)^k - (W y)^k|
        ≤ |W x - W y| * (k:ℝ) * (max |W x| |W y|) ^ (k-1) := by
          simpa only [mul_assoc] using h
      _ ≤ (K:ℝ) * ‖x - y‖ * (k:ℝ) * M^(k-1) := h2
      _ = Lv * ‖x - y‖ := by rw [hLvdef]; ring
  -- pointwise bound on the derivative of v
  have hv_fd : ∀ z ∈ Work.CR.Flat.polydisc 0 s, ‖fderiv ℝ v z‖ ≤ Lv := by
    intro z hz
    exact norm_fderiv_le_of_lipschitzOn ℝ ((Work.CR.Flat.isOpen_polydisc 0 s).mem_nhds hz) hv_lip
  have hLv0 : 0 ≤ Lv := by positivity
  -- a.e. product rule for G
  have hae_diff : ∀ᵐ z ∂(volume : Measure (Work.NN.Core.Cn n)),
      z ∈ Work.CR.Flat.polydisc 0 s → DifferentiableAt ℝ W z := by
    have h1 := hLip.ae_differentiableWithinAt_of_mem (μ := (volume : Measure (Work.NN.Core.Cn n)))
    filter_upwards [h1] with z hz hzs
    have hzρ : z ∈ Work.CR.Flat.polydisc 0 ρ :=
      Work.CR.Flat.polydisc_mono (fun j => (hsρ j).le) hzs
    exact (hz hzρ).differentiableAt ((Work.CR.Flat.isOpen_polydisc 0 ρ).mem_nhds hzρ)
  have hAE_prod : ∀ᵐ z ∂(volume : Measure (Work.NN.Core.Cn n)),
      fderiv ℝ G z = χ z • fderiv ℝ v z + v z • fderiv ℝ χ z := by
    filter_upwards [hae_diff] with z hz
    by_cases hzs : z ∈ Work.CR.Flat.polydisc 0 s
    · have hWdiff : DifferentiableAt ℝ W z := hz hzs
      have hv_diff : DifferentiableAt ℝ v z := by
        rw [hv]
        exact hWdiff.pow k
      have hχ_diff : DifferentiableAt ℝ χ z := hχdiff.differentiableAt
      have h := fderiv_fun_mul hχ_diff hv_diff
      rw [hG]; exact h
    · have hzts : z ∉ tsupport χ := fun h => hzs (hχsupp h)
      have hχz0 : χ z = 0 := (tsupport_eventuallyEq_zero hzts).self_of_nhds
      have hdχ : fderiv ℝ χ z = 0 := by
        rw [Filter.EventuallyEq.fderiv_eq (tsupport_eventuallyEq_zero hzts)]
        simp
      have hdG : fderiv ℝ G z = 0 := by
        have hG0 : G =ᶠ[𝓝 z] 0 := by
          filter_upwards [tsupport_eventuallyEq_zero hzts] with y hy
          simp only [Pi.zero_apply] at hy ⊢
          change χ y * v y = 0
          rw [hy, zero_mul]
        rw [Filter.EventuallyEq.fderiv_eq hG0]; simp
      rw [hdG, hdχ, hχz0]; simp
  -- pointwise bound on the squared derivative of G
  set fA : Work.NN.Core.Cn n → ℝ := fun z => (χ z)^2 * ‖fderiv ℝ v z‖^2 with hfA
  set fB : Work.NN.Core.Cn n → ℝ := fun z => ‖fderiv ℝ χ z‖^2 * (W z)^(2*k) with hfB
  have hnormG_ae : ∀ᵐ z ∂(volume : Measure (Work.NN.Core.Cn n)),
      ‖fderiv ℝ G z‖^2 ≤ 2 * fA z + 2 * fB z := by
    filter_upwards [hAE_prod] with z hz
    rw [hz]
    have hvz0 : 0 ≤ v z := by rw [hv]; exact pow_nonneg (le_trans hΛ (hWle z)) k
    have h1 : ‖χ z • fderiv ℝ v z + v z • fderiv ℝ χ z‖
        ≤ χ z * ‖fderiv ℝ v z‖ + (W z)^k * ‖fderiv ℝ χ z‖ := by
      refine (norm_add_le _ _).trans (le_of_eq ?_)
      rw [norm_smul, norm_smul, Real.norm_of_nonneg (hχnn z), Real.norm_of_nonneg hvz0]
    have h2 : (χ z * ‖fderiv ℝ v z‖ + (W z)^k * ‖fderiv ℝ χ z‖)^2
        ≤ 2 * (χ z * ‖fderiv ℝ v z‖)^2 + 2 * ((W z)^k * ‖fderiv ℝ χ z‖)^2 := by
      nlinarith [sq_nonneg (χ z * ‖fderiv ℝ v z‖ - (W z)^k * ‖fderiv ℝ χ z‖)]
    calc ‖χ z • fderiv ℝ v z + v z • fderiv ℝ χ z‖^2
        ≤ (χ z * ‖fderiv ℝ v z‖ + (W z)^k * ‖fderiv ℝ χ z‖)^2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ 2 * (χ z * ‖fderiv ℝ v z‖)^2 + 2 * ((W z)^k * ‖fderiv ℝ χ z‖)^2 := h2
      _ = 2 * fA z + 2 * fB z := by
          have hW2k : ((W z)^k)^2 = (W z)^(2*k) := by rw [← pow_mul, Nat.mul_comm k 2]
          show 2 * (χ z * ‖fderiv ℝ v z‖)^2 + 2 * ((W z)^k * ‖fderiv ℝ χ z‖)^2
              = 2 * (χ z ^ 2 * ‖fderiv ℝ v z‖ ^ 2) + 2 * (‖fderiv ℝ χ z‖ ^ 2 * W z ^ (2*k))
          rw [mul_pow, mul_pow, hW2k]; ring
  -- measurability of fA, fB
  have hmeasA : AEStronglyMeasurable fA volume := by
    have h1 : Measurable (fun z => (χ z)^2) := (hχcd.continuous.pow 2).measurable
    have h2 : Measurable (fun z => ‖fderiv ℝ v z‖^2) := (measurable_fderiv ℝ v).norm.pow_const 2
    rw [hfA]
    exact (h1.mul h2).aestronglyMeasurable
  -- global Lipschitz extension of `W` (to handle measurability of powers of `W`)
  obtain ⟨V, hVlip, hVeq⟩ := hLip.extend_real
  have hVcont : Continuous V := hVlip.continuous
  have hfB_V : fB = fun z => ‖fderiv ℝ χ z‖^2 * (V z)^(2*k) := by
    funext z
    rw [hfB]
    change ‖fderiv ℝ χ z‖^2 * W z^(2*k) = ‖fderiv ℝ χ z‖^2 * V z^(2*k)
    by_cases hz : z ∈ Work.CR.Flat.polydisc 0 ρ
    · rw [hVeq hz]
    · have hzt : z ∉ tsupport χ := fun h =>
        hz (Work.CR.Flat.polydisc_mono (fun j => (hsρ j).le) (hχsupp h))
      have hdχ : fderiv ℝ χ z = 0 := by
        rw [Filter.EventuallyEq.fderiv_eq (tsupport_eventuallyEq_zero hzt)]
        simp
      rw [hdχ]; simp
  have hmeasB : AEStronglyMeasurable fB volume := by
    rw [hfB_V]
    exact (((measurable_fderiv ℝ χ).norm.pow_const 2).mul
      (hVcont.measurable.pow_const (2*k))).aestronglyMeasurable
  have hIntA : Integrable fA volume := by
    refine integrable_of_vanishes_off_compact (C := Lv^2) hmeasA (sq_nonneg Lv) hχcs.isCompact ?_ ?_
    · intro z hz
      have hχ0 : χ z = 0 := Function.notMem_support.mp fun h => hz (subset_closure h)
      show (χ z)^2 * ‖fderiv ℝ v z‖^2 = 0
      rw [hχ0]; simp
    · intro z
      show |(χ z)^2 * ‖fderiv ℝ v z‖^2| ≤ Lv^2
      rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
      by_cases hz : z ∈ Work.CR.Flat.polydisc 0 s
      · have h1 : (χ z)^2 ≤ 1 := by nlinarith [hχnn z, hχle1 z, sq_nonneg (χ z)]
        have h2 : ‖fderiv ℝ v z‖^2 ≤ Lv^2 := pow_le_pow_left₀ (norm_nonneg _) (hv_fd z hz) 2
        calc (χ z)^2 * ‖fderiv ℝ v z‖^2 ≤ 1 * Lv^2 :=
              mul_le_mul h1 h2 (by positivity) (by norm_num)
          _ = Lv^2 := by ring
      · have hχ0 : χ z = 0 := by
          by_contra hne
          exact hz (hχsupp (subset_closure (Function.mem_support.mpr hne)))
        rw [hχ0]; simp only [zero_pow (by norm_num : 2 ≠ 0), zero_mul]
        exact pow_nonneg hLv0 2
  have hIntB : Integrable fB volume := by
    refine integrable_of_vanishes_off_compact (C := M^(2*k) * L^2) hmeasB
      (mul_nonneg (pow_nonneg hMnn (2*k)) (sq_nonneg L)) hχcs.isCompact ?_ ?_
    · intro z hz
      have hχ0 : fderiv ℝ χ z = 0 := by
        rw [Filter.EventuallyEq.fderiv_eq (tsupport_eventuallyEq_zero (f := χ) (z := z) hz)]
        simp
      show ‖fderiv ℝ χ z‖^2 * (W z)^(2*k) = 0
      rw [hχ0]; simp
    · intro z
      show |‖fderiv ℝ χ z‖^2 * (W z)^(2*k)| ≤ M^(2*k) * L^2
      rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) (pow_nonneg (le_trans hΛ (hWle z)) (2*k)))]
      by_cases hz : z ∈ tsupport χ
      · have hzs : ∀ j, ‖z j‖ ≤ s j := fun j => le_of_lt (by simpa using hχsupp hz j)
        have hWz : (W z)^(2*k) ≤ M^(2*k) := by
          have h := hMW z hzs
          exact pow_le_pow_left₀ (le_trans hΛ (hWle z)) (abs_le.mp h).2 (2*k)
        have h1 : ‖fderiv ℝ χ z‖^2 ≤ L^2 := pow_le_pow_left₀ (norm_nonneg _) (hχL z) 2
        calc ‖fderiv ℝ χ z‖^2 * (W z)^(2*k) ≤ L^2 * M^(2*k) :=
              mul_le_mul h1 hWz (pow_nonneg (le_trans hΛ (hWle z)) (2*k)) (sq_nonneg L)
          _ = M^(2*k) * L^2 := by ring
      · have hχ0 : fderiv ℝ χ z = 0 := by
          rw [Filter.EventuallyEq.fderiv_eq (tsupport_eventuallyEq_zero (f := χ) (z := z) hz)]
          simp
        rw [hχ0]; simp only [norm_zero, zero_pow (by norm_num : 2 ≠ 0), zero_mul]
        exact mul_nonneg (pow_nonneg hMnn (2*k)) (sq_nonneg L)
  have hIntAB : Integrable (fun z => 2 * fA z + 2 * fB z) volume :=
    (hIntA.const_mul 2).add (hIntB.const_mul 2)
  have hmeasG2 : AEStronglyMeasurable (fun z => ‖fderiv ℝ G z‖^2) volume :=
    ((measurable_fderiv ℝ G).norm.pow_const 2).aestronglyMeasurable
  have hIntG : Integrable (fun z => ‖fderiv ℝ G z‖^2) volume :=
    Integrable.mono' hIntAB hmeasG2
      (hnormG_ae.mono fun z hz => by
        rwa [Real.norm_eq_abs, abs_of_nonneg (by positivity)])
  -- volume of `Pd s` is finite
  have hPds_fin : (volume : Measure (Work.NN.Core.Cn n)) (Work.CR.Flat.polydisc 0 s) < ⊤ := by
    refine lt_of_le_of_lt (measure_mono ?_) hcs_compact.measure_lt_top
    intro z hz j
    exact le_of_lt (by simpa using hz j)
  have hPds_nn : (volume : Measure (Work.NN.Core.Cn n)) (Work.CR.Flat.polydisc 0 s) ≠ ⊤ :=
    ne_of_lt hPds_fin
  -- `Av = ∫_{Pd s} W^{2k}`
  set Av : ℝ := ∫ z in Work.CR.Flat.polydisc 0 s, (W z)^(2*k) with hAv
  have hAvnn : 0 ≤ Av := by
    rw [hAv]; exact integral_nonneg fun z => pow_nonneg (le_trans hΛ (hWle z)) _
  set Dc : ℝ := 2 * (A * (k:ℝ)^2 + (A + 1) * L^2) with hDc
  have hSmeas : MeasurableSet (Work.CR.Flat.polydisc 0 s) :=
    (Work.CR.Flat.isOpen_polydisc 0 s).measurableSet
  have hIntWA : IntegrableOn (fun z => (W z)^(2*k)) (Work.CR.Flat.polydisc 0 s) volume := by
    refine MeasureTheory.IntegrableOn.of_bound hPds_fin ?_ (M^(2*k)) ?_
    · exact (((hLip.continuousOn.mono (Work.CR.Flat.polydisc_mono (fun j => (hsρ j).le))).pow
        (2*k))).aestronglyMeasurable hSmeas
    · filter_upwards [MeasureTheory.ae_restrict_mem hSmeas] with z hz
      have hzs : ∀ j, ‖z j‖ ≤ s j := fun j => le_of_lt (by simpa using hz j)
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (le_trans hΛ (hWle z)) _)]
      exact pow_le_pow_left₀ (le_trans hΛ (hWle z)) (abs_le.mp (hMW z hzs)).2 (2*k)
  have hfG_bound : ∫ z, ‖fderiv ℝ G z‖^2 ≤ Dc * Av := by
    have h1 : ∫ z, ‖fderiv ℝ G z‖^2 ≤ ∫ z, (2 * fA z + 2 * fB z) :=
      integral_mono_ae hIntG hIntAB hnormG_ae
    have h2 : ∫ z, (2 * fA z + 2 * fB z) = 2 * (∫ z, fA z) + 2 * (∫ z, fB z) := by
      rw [MeasureTheory.integral_add (hIntA.const_mul 2) (hIntB.const_mul 2)]
      rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    have hfA_zero : ∀ z ∉ Work.CR.Flat.polydisc 0 s, fA z = 0 := by
      intro z hz
      have hχ0 : χ z = 0 := Function.notMem_support.mp fun h => hz (hχsupp (subset_closure h))
      show (χ z)^2 * ‖fderiv ℝ v z‖^2 = 0
      rw [hχ0]; simp
    have hHχ := hH k hk χ hχcd hχcs
      (hχsupp.trans (Work.CR.Flat.polydisc_mono (fun j => (hsρ j).le))) hχnn
    have hRmeas : MeasurableSet (Work.CR.Flat.polydisc 0 ρ) :=
      (Work.CR.Flat.isOpen_polydisc 0 ρ).measurableSet
    -- bound of the source term
    have hb2 : Λ^2 * (∫ z in Work.CR.Flat.polydisc 0 ρ, (χ z)^2 * (W z)^(2*k-2)) ≤ Av := by
      rw [hAv]
      have hsupp : (∫ z in Work.CR.Flat.polydisc 0 ρ, (χ z)^2 * (W z)^(2*k-2))
          = ∫ z in Work.CR.Flat.polydisc 0 s, (χ z)^2 * (W z)^(2*k-2) :=
        MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hRmeas
          (Work.CR.Flat.polydisc_mono (fun j => (hsρ j).le))
          (fun z hz => by
            have hχ0 : χ z = 0 := Function.notMem_support.mp fun h => hz.2 (hχsupp (subset_closure h))
            rw [hχ0]; ring)
      rw [hsupp, ← MeasureTheory.integral_const_mul]
      have hC2 : 0 ≤ Λ^2 * M^(2*k-2) := mul_nonneg (sq_nonneg Λ) (pow_nonneg hMnn _)
      refine MeasureTheory.integral_mono ?_ hIntWA (fun z => ?_)
      · refine MeasureTheory.IntegrableOn.of_bound hPds_fin ?_ (Λ^2 * M^(2*k-2)) ?_
        · exact (((continuous_const.continuousOn).mul
            (((hχcd.continuous.pow 2).continuousOn).mul
              (((hLip.continuousOn.mono (Work.CR.Flat.polydisc_mono (fun j => (hsρ j).le))).pow
                (2*k-2)))))).aestronglyMeasurable hSmeas
        · filter_upwards [MeasureTheory.ae_restrict_mem hSmeas] with z hz
          have hzs : ∀ j, ‖z j‖ ≤ s j := fun j => le_of_lt (by simpa using hz j)
          have hχ2 : (χ z)^2 ≤ 1 := by nlinarith [hχnn z, hχle1 z, sq_nonneg (χ z)]
          have hWp : (W z)^(2*k-2) ≤ M^(2*k-2) :=
            pow_le_pow_left₀ (le_trans hΛ (hWle z)) (abs_le.mp (hMW z hzs)).2 (2*k-2)
          rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg Λ)
            (mul_nonneg (sq_nonneg _) (pow_nonneg (le_trans hΛ (hWle z)) _)))]
          calc Λ^2 * ((χ z)^2 * (W z)^(2*k-2)) ≤ Λ^2 * (1 * M^(2*k-2)) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul hχ2 hWp (pow_nonneg (le_trans hΛ (hWle z)) _) (by norm_num)) (sq_nonneg Λ)
            _ = Λ^2 * M^(2*k-2) := by ring
      · by_cases hz : z ∈ Work.CR.Flat.polydisc 0 s
        · have hχ2 : (χ z)^2 ≤ 1 := by nlinarith [hχnn z, hχle1 z, sq_nonneg (χ z)]
          have hL2 : Λ^2 ≤ (W z)^2 := pow_le_pow_left₀ hΛ (hWle z) 2
          have hLχ : Λ^2 * (χ z)^2 ≤ (W z)^2 * 1 := by
            nlinarith [hL2, hχ2, sq_nonneg Λ, sq_nonneg (χ z), hΛ]
          calc Λ^2 * ((χ z)^2 * (W z)^(2*k-2))
              = (Λ^2 * (χ z)^2) * (W z)^(2*k-2) := by ring
            _ ≤ ((W z)^2 * 1) * (W z)^(2*k-2) :=
                mul_le_mul_of_nonneg_right hLχ (pow_nonneg (le_trans hΛ (hWle z)) _)
            _ = (W z)^(2*k) := by
                rw [mul_one, ← pow_add]; congr 1; omega
        · have hχ0 : χ z = 0 := Function.notMem_support.mp fun h => hz (hχsupp (subset_closure h))
          rw [hχ0]
          simp only [zero_pow (by norm_num : 2 ≠ 0), zero_mul, mul_zero]
          exact pow_nonneg (le_trans hΛ (hWle z)) (2*k)
    -- bound of the second RHS term
    have hb3 : (∫ z in Work.CR.Flat.polydisc 0 ρ, ‖fderiv ℝ χ z‖^2 * (W z)^(2*k)) ≤ L^2 * Av := by
      have hsupp : (∫ z in Work.CR.Flat.polydisc 0 ρ, ‖fderiv ℝ χ z‖^2 * (W z)^(2*k))
          = ∫ z in Work.CR.Flat.polydisc 0 s, ‖fderiv ℝ χ z‖^2 * (W z)^(2*k) :=
        MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hRmeas
          (Work.CR.Flat.polydisc_mono (fun j => (hsρ j).le))
          (fun z hz => by
            have hχ0 : fderiv ℝ χ z = 0 := by
              rw [Filter.EventuallyEq.fderiv_eq
                (tsupport_eventuallyEq_zero (f := χ) (z := z) (fun h => hz.2 (hχsupp h)))]
              simp
            rw [hχ0]; simp)
      have hmid : (∫ z in Work.CR.Flat.polydisc 0 s, ‖fderiv ℝ χ z‖^2 * (W z)^(2*k))
          ≤ ∫ z in Work.CR.Flat.polydisc 0 s, L^2 * (W z)^(2*k) := by
        refine MeasureTheory.integral_mono ?_ (hIntWA.const_mul (L^2)) (fun z => ?_)
        · refine MeasureTheory.IntegrableOn.of_bound hPds_fin ?_ (L^2 * M^(2*k)) ?_
          · exact ((measurable_fderiv ℝ χ).norm.pow_const 2).aestronglyMeasurable.mul
              (((hLip.continuousOn.mono (Work.CR.Flat.polydisc_mono (fun j => (hsρ j).le))).pow
                (2*k)).aestronglyMeasurable hSmeas)
          · filter_upwards [MeasureTheory.ae_restrict_mem hSmeas] with z hz
            have hzs : ∀ j, ‖z j‖ ≤ s j := fun j => le_of_lt (by simpa using hz j)
            have hWz : (W z)^(2*k) ≤ M^(2*k) :=
              pow_le_pow_left₀ (le_trans hΛ (hWle z)) (abs_le.mp (hMW z hzs)).2 (2*k)
            rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _)
              (pow_nonneg (le_trans hΛ (hWle z)) _))]
            calc ‖fderiv ℝ χ z‖^2 * (W z)^(2*k) ≤ L^2 * M^(2*k) :=
                  mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hχL z) 2) hWz
                    (pow_nonneg (le_trans hΛ (hWle z)) _) (by positivity)
              _ = L^2 * M^(2*k) := rfl
        · exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hχL z) 2)
            (pow_nonneg (le_trans hΛ (hWle z)) _)
      calc (∫ z in Work.CR.Flat.polydisc 0 ρ, ‖fderiv ℝ χ z‖^2 * (W z)^(2*k))
          = ∫ z in Work.CR.Flat.polydisc 0 s, ‖fderiv ℝ χ z‖^2 * (W z)^(2*k) := hsupp
        _ ≤ ∫ z in Work.CR.Flat.polydisc 0 s, L^2 * (W z)^(2*k) := hmid
        _ = L^2 * (∫ z in Work.CR.Flat.polydisc 0 s, (W z)^(2*k)) := by
            rw [MeasureTheory.integral_const_mul]
        _ = L^2 * Av := by rw [hAv]

    have h3 : ∫ z, fA z ≤ A * ((k:ℝ)^2 * Av + L^2 * Av) := by
      have hA_eq : ∫ z, fA z = ∫ z in Work.CR.Flat.polydisc 0 ρ,
          (χ z)^2 * ‖fderiv ℝ (fun w => (W w)^k) z‖^2 := by
        rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (s := Work.CR.Flat.polydisc 0 ρ)
          (fun z hz => hfA_zero z (fun h => hz (Work.CR.Flat.polydisc_mono (fun j => (hsρ j).le) h)))]
      rw [hA_eq]
      calc (∫ z in Work.CR.Flat.polydisc 0 ρ, (χ z)^2 * ‖fderiv ℝ (fun w => (W w)^k) z‖^2)
          ≤ A * ((k:ℝ)^2 * Λ^2 * (∫ z in Work.CR.Flat.polydisc 0 ρ, (χ z)^2 * (W z)^(2*k-2))
              + ∫ z in Work.CR.Flat.polydisc 0 ρ, ‖fderiv ℝ χ z‖^2 * (W z)^(2*k)) := by
            simpa only [mul_assoc] using hHχ
        _ ≤ A * ((k:ℝ)^2 * Av + L^2 * Av) := by
            refine mul_le_mul_of_nonneg_left ?_ hA.le
            have e1 : (k:ℝ)^2 * Λ^2 * (∫ z in Work.CR.Flat.polydisc 0 ρ, (χ z)^2 * (W z)^(2*k-2))
                ≤ (k:ℝ)^2 * Av := by
              rw [mul_assoc]
              exact mul_le_mul_of_nonneg_left hb2 (by positivity)
            linarith [e1, hb3]
    have h4 : ∫ z, fB z ≤ L^2 * Av := by
      have hfB_eq : ∫ z, fB z = ∫ z in Work.CR.Flat.polydisc 0 ρ, fB z := by
        rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (s := Work.CR.Flat.polydisc 0 ρ)]
        intro z hz
        have hχ0 : fderiv ℝ χ z = 0 := by
          rw [Filter.EventuallyEq.fderiv_eq
            (tsupport_eventuallyEq_zero (f := χ) (z := z)
              (fun h => hz (Work.CR.Flat.polydisc_mono (fun j => (hsρ j).le) (hχsupp h))))]
          simp
        show ‖fderiv ℝ χ z‖^2 * (W z)^(2*k) = 0
        rw [hχ0]; simp
      rw [hfB_eq]
      exact hb3
    calc ∫ z, ‖fderiv ℝ G z‖^2 ≤ ∫ z, (2 * fA z + 2 * fB z) := h1
      _ = 2 * (∫ z, fA z) + 2 * (∫ z, fB z) := h2
      _ ≤ 2 * (A * ((k:ℝ)^2 * Av + L^2 * Av)) + 2 * (L^2 * Av) :=
          add_le_add (mul_le_mul_of_nonneg_left h3 (by norm_num)) (mul_le_mul_of_nonneg_left h4 (by norm_num))
      _ = Dc * Av := by rw [hDc]; ring
  -- ## Gagliardo--Nirenberg and the power conversion
  have hWnn : ∀ z, 0 ≤ W z := fun z => le_trans hΛ (hWle z)
  have hDc0 : 0 ≤ Dc := by rw [hDc]; positivity
  set qE : ENNReal := (2 : ENNReal) * ((NNReal.conjExponent (2 * n) : NNReal) : ENNReal) with hqEdef
  set A2 : ENNReal := MeasureTheory.eLpNorm v 2
    (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 s)) with hA2def
  set B : ENNReal := MeasureTheory.eLpNorm W (ENNReal.ofReal (2 * (k:ℝ)))
    (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 s)) with hBdef
  have hmeas_v : AEStronglyMeasurable v
      (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 s)) :=
    hv_lip.continuousOn.aestronglyMeasurable hSmeas
  have hA2sq : A2 ^ (2:ℝ)
      = ∫⁻ z in Work.CR.Flat.polydisc 0 s, ENNReal.ofReal ((W z)^(2*k)) := by
    rw [hA2def, Work.NN.Core.Value.eLpNorm_two_sq_eq_lintegral_ofReal hmeas_v]
    refine lintegral_congr fun z => ?_
    congr 1
    rw [hv, Real.norm_eq_abs, abs_pow,
      show |W z| = W z from abs_of_nonneg (hWnn z), ← pow_mul, Nat.mul_comm k 2]
  have hAvJ : ENNReal.ofReal Av = A2 ^ (2:ℝ) := by
    rw [hAv, hA2sq]
    exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hIntWA
      (Filter.Eventually.of_forall fun z => pow_nonneg (hWnn z) _)
  have hD2 : (MeasureTheory.eLpNorm (fderiv ℝ G) 2 volume) ^ (2:ℝ)
      ≤ ENNReal.ofReal Dc * A2 ^ (2:ℝ) := by
    rw [Work.NN.Core.Value.eLpNorm_two_sq_eq_lintegral_ofReal
      (measurable_fderiv ℝ G).aestronglyMeasurable, ← hAvJ]
    calc ∫⁻ z, ENNReal.ofReal (‖fderiv ℝ G z‖^2)
        = ENNReal.ofReal (∫ z, ‖fderiv ℝ G z‖^2) :=
          (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hIntG
            (Filter.Eventually.of_forall fun z => by positivity)).symm
      _ ≤ ENNReal.ofReal (Dc * Av) := ENNReal.ofReal_le_ofReal hfG_bound
      _ = ENNReal.ofReal Dc * ENNReal.ofReal Av := ENNReal.ofReal_mul hDc0
  have hDle : MeasureTheory.eLpNorm (fderiv ℝ G) 2 volume
      ≤ ENNReal.ofReal (Real.sqrt Dc) * A2 :=
    Work.NN.Core.Lev.sq_le_ofReal_mul_sq hDc0 hD2
  have hG2le : MeasureTheory.eLpNorm G 2 volume ≤ A2 := by
    have hsuppG : Function.support G ⊆ Work.CR.Flat.polydisc 0 s := by
      intro z hz
      by_contra hzS
      have hzt : z ∉ tsupport χ := fun h => hzS (hχsupp h)
      have hχ0 : χ z = 0 := Function.notMem_support.mp fun h => hzt (subset_closure h)
      exact hz (by rw [hG]; simp [hχ0])
    have hGV : G = fun z => χ z * (V z)^k := by
      funext z
      by_cases hz : z ∈ Work.CR.Flat.polydisc 0 ρ
      · rw [hG]
        show χ z * (W z)^k = χ z * (V z)^k
        rw [hVeq hz]
      · have hzt : z ∉ tsupport χ := fun h =>
          hz (Work.CR.Flat.polydisc_mono (fun j => (hsρ j).le) (hχsupp h))
        have hχ0 : χ z = 0 := Function.notMem_support.mp fun h => hzt (subset_closure h)
        rw [hG]
        show χ z * (W z)^k = χ z * (V z)^k
        rw [hχ0]; simp
    have hGmeas : AEStronglyMeasurable G volume := by
      rw [hGV]
      exact (hχcd.continuous.mul (hVcont.pow k)).aestronglyMeasurable
    rw [← MeasureTheory.eLpNorm_restrict_eq_of_support_subset hGmeas hsuppG]
    refine MeasureTheory.eLpNorm_mono_ae
      (hGmeas.mono_measure MeasureTheory.Measure.restrict_le_self) ?_
    filter_upwards with z
    show ‖G z‖ ≤ ‖v z‖
    rw [hG, norm_mul, Real.norm_of_nonneg (hχnn z)]
    calc χ z * ‖v z‖ ≤ 1 * ‖v z‖ := mul_le_mul_of_nonneg_right (hχle1 z) (norm_nonneg _)
      _ = ‖v z‖ := one_mul _
  have hGNapp := hGNS ⟨(k:ℝ) * M^(k-1) * (K:ℝ) + M^k * L, by positivity⟩ s G hG_lip htsupp_G
  have hsqGN : (MeasureTheory.eLpNorm G qE volume) ^ (2:ℝ)
      ≤ ENNReal.ofReal (Cgns * Real.sqrt Dc) * A2 ^ (2:ℝ) := by
    have h1 := hGNapp
    rw [← ENNReal.rpow_natCast] at h1
    refine h1.trans ?_
    calc ENNReal.ofReal Cgns * MeasureTheory.eLpNorm G 2 volume
            * MeasureTheory.eLpNorm (fderiv ℝ G) 2 volume
        ≤ ENNReal.ofReal Cgns * A2 * (ENNReal.ofReal (Real.sqrt Dc) * A2) :=
          mul_le_mul' (mul_le_mul' le_rfl hG2le) hDle
      _ = ENNReal.ofReal (Cgns * Real.sqrt Dc) * A2 ^ (2:ℝ) := by
          rw [ENNReal.rpow_two, pow_two,
            show ENNReal.ofReal Cgns * A2 * (ENNReal.ofReal (Real.sqrt Dc) * A2)
              = ENNReal.ofReal Cgns * ENNReal.ofReal (Real.sqrt Dc) * (A2 * A2) by ring,
            ← ENNReal.ofReal_mul hCgns.le]
  have hGfinal : MeasureTheory.eLpNorm G qE volume
      ≤ ENNReal.ofReal (Real.sqrt (Cgns * Real.sqrt Dc)) * A2 :=
    Work.NN.Core.Lev.sq_le_ofReal_mul_sq (by positivity) hsqGN
  have hvGN : MeasureTheory.eLpNorm v qE
        (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 r))
      ≤ ENNReal.ofReal (Real.sqrt (Cgns * Real.sqrt Dc)) * A2 := by
    have hae : v =ᵐ[MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 r)] G := by
      rw [Filter.EventuallyEq,
        MeasureTheory.ae_restrict_iff' (Work.CR.Flat.isOpen_polydisc 0 r).measurableSet]
      exact Filter.Eventually.of_forall fun z hz => by
        show v z = χ z * v z
        have hz1 : ∀ j, ‖z j‖ ≤ r j := fun j => le_of_lt (by simpa using hz j)
        rw [hχ1 z hz1, one_mul]
    exact ((le_of_eq (MeasureTheory.eLpNorm_congr_ae hae)).trans
      (MeasureTheory.eLpNorm_mono_measure G MeasureTheory.Measure.restrict_le_self)).trans hGfinal
  -- ## converting `v = W^k` back to `W`
  have hWR : AEStronglyMeasurable W
      (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 r)) :=
    ((hLip.mono (Work.CR.Flat.polydisc_mono (fun j => (hrs j).le.trans (hsρ j).le))).continuousOn)
      |>.aestronglyMeasurable (Work.CR.Flat.isOpen_polydisc 0 r).measurableSet
  have hWS : AEStronglyMeasurable W
      (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 s)) :=
    ((hLip.mono (Work.CR.Flat.polydisc_mono (fun j => (hsρ j).le))).continuousOn)
      |>.aestronglyMeasurable (Work.CR.Flat.isOpen_polydisc 0 s).measurableSet
  have hexp : ENNReal.ofReal (2 * ((k:ℝ) * Work.NN.Core.Lev.moserTheta n))
      = qE * ENNReal.ofReal (k:ℝ) := by
    rw [hqEdef, ← Work.NN.Core.Lev.ofReal_moserTheta n,
      show (2:ENNReal) = ENNReal.ofReal (2:ℝ) from (ENNReal.ofReal_ofNat 2).symm,
      ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
      ← ENNReal.ofReal_mul (by have h := Work.NN.Core.Lev.moserTheta_pos hn; positivity)]
    congr 1
    ring
  have hXeq : MeasureTheory.eLpNorm v qE
        (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 r))
      = (MeasureTheory.eLpNorm W
          (ENNReal.ofReal (2 * ((k:ℝ) * Work.NN.Core.Lev.moserTheta n)))
          (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 r)))^k := by
    rw [hqEdef]
    rw [show v = fun z => ‖W z‖ ^ (k:ℝ) by
      funext z
      show (W z)^k = ‖W z‖ ^ (k:ℝ)
      rw [Real.norm_eq_abs, abs_of_nonneg (hWnn z), Real.rpow_natCast]]
    rw [MeasureTheory.eLpNorm_norm_rpow _ hWR (by exact_mod_cast (by omega : 0 < k)),
      ENNReal.rpow_natCast, hexp]
  have hA2eq : A2 = B^k := by
    rw [hA2def, hBdef]
    rw [show v = fun z => ‖W z‖ ^ (k:ℝ) by
      funext z
      show (W z)^k = ‖W z‖ ^ (k:ℝ)
      rw [Real.norm_eq_abs, abs_of_nonneg (hWnn z), Real.rpow_natCast]]
    rw [MeasureTheory.eLpNorm_norm_rpow _ hWS (by exact_mod_cast (by omega : 0 < k)),
      ENNReal.rpow_natCast]
    exact congrArg
      (fun p => (MeasureTheory.eLpNorm W p
        (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 s)))^k)
      (by rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)])
  have hX1 : (MeasureTheory.eLpNorm W
        (ENNReal.ofReal (2 * ((k:ℝ) * Work.NN.Core.Lev.moserTheta n)))
        (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 r)))^k
      ≤ ENNReal.ofReal (Real.sqrt (Cgns * Real.sqrt Dc)) * B^k := by
    rw [hXeq, hA2eq] at hvGN
    exact hvGN
  -- ## the constant comparison
  have harith : Cgns * Real.sqrt Dc ≤ Cc * (1 + L) * (1 + (k:ℝ)) := by
    rw [hCcdef]
    have hA1 : (0:ℝ) < A + 1 := by linarith
    have hk0 : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
    have hk1 : (1:ℝ) ≤ (1 + (k:ℝ))^2 := by nlinarith
    have hL1 : (1:ℝ) ≤ (1 + L)^2 := by nlinarith
    have hX : A * (k:ℝ)^2 ≤ (A + 1) * (1 + (k:ℝ))^2 * (1 + L)^2 := by
      have h : A * (k:ℝ)^2 ≤ (A + 1) * (1 + (k:ℝ))^2 :=
        mul_le_mul (by linarith) (by nlinarith) (sq_nonneg _) hA1.le
      calc A * (k:ℝ)^2 ≤ (A + 1) * (1 + (k:ℝ))^2 := h
        _ ≤ (A + 1) * (1 + (k:ℝ))^2 * (1 + L)^2 :=
            le_mul_of_one_le_right (by positivity) hL1
    have hY : (A + 1) * L^2 ≤ (A + 1) * (1 + (k:ℝ))^2 * (1 + L)^2 := by
      calc (A + 1) * L^2 ≤ (A + 1) * (1 + L)^2 :=
            mul_le_mul_of_nonneg_left (by nlinarith [hL0]) hA1.le
        _ ≤ ((A + 1) * (1 + L)^2) * (1 + (k:ℝ))^2 :=
            le_mul_of_one_le_right (by positivity) hk1
        _ = (A + 1) * (1 + (k:ℝ))^2 * (1 + L)^2 := by ring
    have hZ : A * (k:ℝ)^2 + (A + 1) * L^2
        ≤ 2 * ((A + 1) * (1 + (k:ℝ))^2 * (1 + L)^2) := by linarith
    have hsq : Dc ≤ (2 * (A + 1) * (1 + (k:ℝ)) * (1 + L))^2 := by
      rw [hDc, show (2 * (A + 1) * (1 + (k:ℝ)) * (1 + L))^2
          = 4 * (A + 1)^2 * (1 + (k:ℝ))^2 * (1 + L)^2 by ring]
      nlinarith [hZ, hA1.le, sq_nonneg (1 + (k:ℝ)), sq_nonneg (1 + L),
        mul_nonneg hA1.le (mul_nonneg (sq_nonneg (1 + (k:ℝ))) (sq_nonneg (1 + L)))]
    have hsqrt : Real.sqrt Dc ≤ 2 * (A + 1) * (1 + (k:ℝ)) * (1 + L) := by
      rw [← Real.sqrt_sq (by positivity : (0:ℝ) ≤ 2 * (A + 1) * (1 + (k:ℝ)) * (1 + L))]
      exact Real.sqrt_le_sqrt hsq
    calc Cgns * Real.sqrt Dc ≤ Cgns * (2 * (A + 1) * (1 + (k:ℝ)) * (1 + L)) :=
          mul_le_mul_of_nonneg_left hsqrt hCgns.le
      _ ≤ (Cgns * (2 * (A + 1)) + 1) * (1 + L) * (1 + (k:ℝ)) := by
          have h1 : Cgns * (2 * (A + 1)) ≤ Cgns * (2 * (A + 1)) + 1 := by linarith
          have h2 : (0:ℝ) ≤ (1 + (k:ℝ)) * (1 + L) := by positivity
          calc Cgns * (2 * (A + 1) * (1 + (k:ℝ)) * (1 + L))
              = (Cgns * (2 * (A + 1))) * ((1 + (k:ℝ)) * (1 + L)) := by ring
            _ ≤ (Cgns * (2 * (A + 1)) + 1) * ((1 + (k:ℝ)) * (1 + L)) :=
                mul_le_mul_of_nonneg_right h1 h2
            _ = (Cgns * (2 * (A + 1)) + 1) * (1 + L) * (1 + (k:ℝ)) := by ring
  have hconst : (ENNReal.ofReal (Real.sqrt (Cgns * Real.sqrt Dc)))^(1/(k:ℝ))
      ≤ (ENNReal.ofReal (Cc * (1 + L) * (1 + (k:ℝ))))^(1/(2*(k:ℝ))) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg _) (by positivity : (0:ℝ) ≤ 1/(k:ℝ))]
    rw [ENNReal.ofReal_rpow_of_nonneg (mul_nonneg (mul_nonneg hCcpos.le (by linarith))
      (by positivity)) (by positivity : (0:ℝ) ≤ 1/(2*(k:ℝ)))]
    apply ENNReal.ofReal_le_ofReal
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity : (0:ℝ) ≤ Cgns * Real.sqrt Dc),
      show (1:ℝ)/2 * (1/(k:ℝ)) = 1/(2*(k:ℝ)) by ring]
    exact Real.rpow_le_rpow (by positivity) harith (by positivity)
  -- ## taking the `k`-th root
  have hkpos : (0:ℝ) < (k:ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hroot : MeasureTheory.eLpNorm W
        (ENNReal.ofReal (2 * ((k:ℝ) * Work.NN.Core.Lev.moserTheta n)))
        (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 r))
      = ((MeasureTheory.eLpNorm W
          (ENNReal.ofReal (2 * ((k:ℝ) * Work.NN.Core.Lev.moserTheta n)))
          (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 r)))^k)^(1/(k:ℝ)) := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
      show (k:ℝ) * (1/(k:ℝ)) = 1 by rw [mul_one_div, div_self (ne_of_gt hkpos)],
      ENNReal.rpow_one]
  rw [hroot]
  refine (ENNReal.rpow_le_rpow hX1 (by positivity : (0:ℝ) ≤ 1/(k:ℝ))).trans ?_
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : (0:ℝ) ≤ 1/(k:ℝ)),
    ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
    show (k:ℝ) * (1/(k:ℝ)) = 1 by rw [mul_one_div, div_self (ne_of_gt hkpos)],
    ENNReal.rpow_one, hBdef]
  exact mul_le_mul_of_nonneg_right hconst (by positivity)


end

end Work.NN.Core.Lev2
