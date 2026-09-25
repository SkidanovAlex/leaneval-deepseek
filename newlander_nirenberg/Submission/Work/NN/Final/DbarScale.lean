/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The rescaled perturbation is small (copy)

This is a copy of `Work.NN.Final.exists_rescale_vecHolder` (proved by a colleague in
`Submission/Work/NN/Final/exists_rescale_vecHolder.lean`), restated in a module that does not depend
on `Submission.Work.NN.Final.dbarSolvable_of_perturb`, so that the latter can import it.

The small-perturbation argument of the assembly chapter needs the perturbation of the *rescaled*
normalisation `Tsh T μ` (`x ↦ (μ:ℂ)⁻¹ • T x`) to be `C^{0,α}`-small on a fixed polydisc, for `μ`
small.  The perturbation of the rescaled normalisation is the perturbation of `T` evaluated at the
rescaled point, up to the cancelling scalar `(μ:ℂ)⁻¹ … (μ:ℂ)` (`Atr_Tsh_apply`):
`Atr J (Tsh T μ) z = (μ:ℂ)⁻¹ • (Atr J T (μ • z)).comp (μ • 1)`; hence its operator norm is bounded
by `‖Atr J T (μ • z)‖`, and `Atr J T` is Lipschitz near `0` (it is `C¹` at `0` because `J` is, and
`Atr J T 0 = 0`), which makes both the supremum and the Hölder seminorm on the *bounded* polydisc
`pd n (fun _ => 1) 4` tend to `0` with `μ`.
-/
import Mathlib
import Submission.Work.NN.Final.DbarSolvableAux
import Submission.Work.NN.Final.Transport
import Submission.Work.Core.Std

open LeanEval.Geometry.NewlanderNirenberg
open Submission
open Work.NN.Core
open Set
open scoped ContDiff NNReal

namespace Work.NN.Final

/-! ## Elementary bounds on the unit polydisc -/

/-- Every point of the polydisc `pd n (fun _ => 1) 4` is within distance `4` of the origin: the
membership condition bounds each of its `n` coordinates by `4`, and the norm on `ℂⁿ` is the
supremum of the coordinate norms. -/
lemma norm_le_four_of_mem_pd_four_c {n : ℕ} {z : Cn n} (hz : z ∈ pd n (fun _ => 1) 4) :
    ‖z‖ ≤ 4 := by
  have h : ∀ j : Fin n, ‖z j‖₊ ≤ (4 : ℝ≥0) := fun j => by
    have hj : ‖z j‖ < 4 := by
      have := (mem_pd.mp hz) j
      simpa using this
    exact_mod_cast le_of_lt hj
  rw [Pi.norm_def]
  exact_mod_cast (Finset.sup_le (fun j _ => h j))

/-- For `0 < α < 1` and `0 ≤ t ≤ 1` one has `t ≤ t ^ α`. -/
lemma rpow_self_le_of_le_one_c {α t : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t ≤ t ^ α := by
  rcases eq_or_lt_of_le ht0 with rfl | ht
  · rw [Real.zero_rpow hα0.ne']
  · calc t = t ^ (1 : ℝ) := (Real.rpow_one t).symm
      _ ≤ t ^ α := Real.rpow_le_rpow_of_exponent_ge ht ht1 (le_of_lt hα1)

/-! ## The rescaled perturbation -/

/-- **The operator norm of the rescaled perturbation.**  Writing `A_μ z := Atr J (Tsh T μ) z`, the
`(0,1)`-form `A_μ z` is obtained from `Atr J T (μ • z)` by conjugating with the multiplication
`μ • ·` on `ℂⁿ` and the inverse multiplication on the values; the two scalings cancel in the
operator norm, so `‖A_μ z‖ ≤ ‖Atr J T (μ • z)‖`. -/
lemma norm_Atr_Tsh_sub_le_c {n : ℕ} {J : EN n → EN n →L[ℝ] EN n} {T : EN n ≃L[ℝ] F n} {μ : ℝ}
    (hμpos : 0 < μ) (hμ' : μ ≠ 0) (z z' : Cn n) :
    ‖Atr J (Tsh T μ hμ') z - Atr J (Tsh T μ hμ') z'‖
      ≤ ‖Atr J T ((μ : ℂ) • z) - Atr J T ((μ : ℂ) • z')‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (fun w => ?_)
  have h1 : (Atr J (Tsh T μ hμ') z - Atr J (Tsh T μ hμ') z') w
      = ((μ : ℂ)⁻¹) •
          ((Atr J T ((μ : ℂ) • z) - Atr J T ((μ : ℂ) • z')) ((μ : ℂ) • w)) := by
    rw [sub_apply, Atr_Tsh_apply, Atr_Tsh_apply, ← smul_sub, sub_apply]
  rw [h1]
  have hc : ‖((μ : ℂ))‖ = μ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hμpos]
  have hci : ‖(((μ : ℂ))⁻¹)‖ = μ⁻¹ := by rw [norm_inv, hc]
  calc ‖((μ : ℂ)⁻¹) •
          ((Atr J T ((μ : ℂ) • z) - Atr J T ((μ : ℂ) • z')) ((μ : ℂ) • w))‖
      = ‖((μ : ℂ)⁻¹)‖ *
          ‖(Atr J T ((μ : ℂ) • z) - Atr J T ((μ : ℂ) • z')) ((μ : ℂ) • w)‖ :=
        norm_smul _ _
    _ ≤ ‖((μ : ℂ)⁻¹)‖ *
          (‖Atr J T ((μ : ℂ) • z) - Atr J T ((μ : ℂ) • z')‖ * ‖(μ : ℂ) • w‖) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        exact ContinuousLinearMap.le_opNorm _ _
    _ = ‖Atr J T ((μ : ℂ) • z) - Atr J T ((μ : ℂ) • z')‖ * ‖w‖ := by
        rw [hci, norm_smul, hc]
        field_simp

/-- The perturbation `Atr J T` is `C¹` at `0`, hence Lipschitz on a neighbourhood of `0`. -/
lemma contDiffAt_one_Atr_c {n : ℕ} {U : Set (EN n)} {J : EN n → EN n →L[ℝ] EN n}
    {T : EN n ≃L[ℝ] F n} (hU : IsOpen U) (h0U : (0 : EN n) ∈ U) (hJ : ContDiffOn ℝ 1 J U) :
    ContDiffAt ℝ 1 (fun z : Cn n => Atr J T z) 0 := by
  have hJ0 : ContDiffAt ℝ 1 J 0 := hJ.contDiffAt (hU.mem_nhds h0U)
  have hφ : ContDiffAt ℝ 1 (fun z : Cn n => tupleDerivInv T z) 0 :=
    (tupleDerivInv T).contDiff.contDiffAt
  have h1 : ContDiffAt ℝ 1 (fun z : Cn n => J (tupleDerivInv T z)) 0 :=
    ContDiffAt.comp (f := fun z : Cn n => tupleDerivInv T z) 0 (by simpa using hJ0) hφ
  have h2 : ContDiffAt ℝ 1 (fun z : Cn n => (J (tupleDerivInv T z)).comp (tupleDerivInv T)) 0 :=
    h1.clm_comp contDiff_const.contDiffAt
  have h3 : ContDiffAt ℝ 1 (fun z : Cn n => Jtr J T z) 0 :=
    contDiff_const.contDiffAt.clm_comp h2
  have h4 : ContDiffAt ℝ 1 (fun z : Cn n => JstdCn n z) 0 := by
    have hh : (fun z : Cn n => JstdCn n z)
        = fun _ : Cn n => Complex.I • (1 : Cn n →L[ℝ] Cn n) := rfl
    rw [hh]; exact contDiff_const.contDiffAt
  exact h3.sub h4

/-- **The rescaled perturbation is small.**  Let `J` be `C¹` on an open set `U ∋ 0` of `ℝ^{2n}` and
`T` normalise `J 0`.  Then for every `ε > 0` there is `μ > 0` such that the perturbation of the
*rescaled* normalisation `Tsh T μ` (which sends `x` to `(μ:ℂ)⁻¹ • T x`; the transported structure
`Jtr J (Tsh T μ)` is then the pullback of `Jtr J T` by `z ↦ μ • z`) is `C^{0,α}`-small with
constant `ε` on the unit polydisc `pd n (fun _ => 1) 4`:
`‖Atr J (Tsh T μ) z‖ ≤ ε` and `‖Atr J (Tsh T μ) z - Atr J (Tsh T μ) z'‖ ≤ ε ‖z - z'‖^α` there.

Uses `Work.NN.Final.Atr_Tsh_apply` (`Atr J (Tsh T μ) z` is `Atr J T` evaluated at `μ • z`, up to the
cancelling scalar `(μ:ℂ)⁻¹ … (μ:ℂ)`), `Work.NN.Final.Atr_zero` (`Atr J T 0 = 0`), the `C¹`-Lipschitz
bound for `Atr J T` near `0` coming from `hJ` (`tupleDerivInv T` maps a neighbourhood of `0` into
`U`), and `diam (pd n (fun _ => 1) 4) < ∞`, so that both bounds tend to `0` with `μ`. -/
theorem exists_rescale_vecHolder_c {n : ℕ} {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {U : Set (LeanEval.Geometry.NewlanderNirenberg.E n)}
    {J : LeanEval.Geometry.NewlanderNirenberg.E n → LeanEval.Geometry.NewlanderNirenberg.E n →L[ℝ] LeanEval.Geometry.NewlanderNirenberg.E n}
    {T : LeanEval.Geometry.NewlanderNirenberg.E n ≃L[ℝ] Submission.F n}
    (hU : IsOpen U) (h0U : (0 : LeanEval.Geometry.NewlanderNirenberg.E n) ∈ U)
    (hJ : ContDiffOn ℝ 1 J U)
    (hT : ∀ v, T (J 0 v) = Complex.I • T v) {ε : ℝ} (hε : 0 < ε) :
    ∃ μ : ℝ, ∃ hμ : 0 < μ,
      Work.NN.Final.VecHolder
        (fun z => Work.NN.Final.Atr J (Work.NN.Final.Tsh T μ (ne_of_gt hμ)) z) α ε
        (Work.NN.Final.pd n (fun _ => 1) 4) := by
  -- `Atr J T` is `C¹` at `0`, so it is Lipschitz on a ball around `0`.
  obtain ⟨K, t, ht, hLip⟩ :=
    (contDiffAt_one_Atr_c (n := n) hU h0U hJ).exists_lipschitzOnWith
  obtain ⟨ρ, hρpos, hρsub⟩ := Metric.mem_nhds_iff.mp ht
  have hLipρ : LipschitzOnWith K (fun z : Cn n => Atr J T z) (Metric.ball 0 ρ) :=
    hLip.mono hρsub
  -- The auxiliary constant `M = K + 1 > 0` and the scale `μ`, chosen so that `μ ≤ ρ/8` (to land in
  -- the Lipschitz ball) and `M * μ ≤ ε/9` (to make both bounds small).
  set M : ℝ := (K : ℝ) + 1 with hMdef
  have hMpos : 0 < M := by rw [hMdef]; positivity
  have hKle : (K : ℝ) ≤ M := by rw [hMdef]; linarith [K.coe_nonneg]
  set μ : ℝ := min (ρ / 8) (ε / (M * 9)) with hμdef
  have hμpos : 0 < μ := by
    rw [hμdef]; exact lt_min (by positivity) (div_pos hε (by positivity))
  have hμle1 : μ ≤ ρ / 8 := by rw [hμdef]; exact min_le_left _ _
  have hμle2 : M * μ ≤ ε / 9 := by
    have h2 : μ ≤ ε / (M * 9) := by rw [hμdef]; exact min_le_right _ _
    calc M * μ ≤ M * (ε / (M * 9)) := mul_le_mul_of_nonneg_left h2 (le_of_lt hMpos)
      _ = ε / 9 := by field_simp
  refine ⟨μ, hμpos, ?_⟩
  -- From here on the rescaled normalisation is `Tsh T μ (ne_of_gt hμpos)`.
  have hc : ‖((μ : ℂ))‖ = μ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hμpos]
  have hA0 : Atr J T 0 = 0 :=
    ContinuousLinearMap.ext (fun w => by simpa using Atr_zero J T hT w)
  have hAμ0 : Atr J (Tsh T μ (ne_of_gt hμpos)) 0 = 0 :=
    ContinuousLinearMap.ext (fun w => by
      simpa using
        Atr_zero J (Tsh T μ (ne_of_gt hμpos))
          (Tsh_intertwines J T μ (ne_of_gt hμpos) hT) w)
  have hzero : (0 : Cn n) ∈ Metric.ball 0 ρ := by simp [Metric.mem_ball, hρpos]
  have hμnn : (0 : ℝ) ≤ M * μ := le_of_lt (mul_pos hMpos hμpos)
  constructor
  · -- the supremum bound
    intro z hz
    have hz4 : ‖z‖ ≤ 4 := norm_le_four_of_mem_pd_four_c hz
    have hcz : ((μ : ℂ) • z) ∈ Metric.ball 0 ρ := by
      rw [Metric.mem_ball, dist_eq_norm, sub_zero, norm_smul, hc]
      nlinarith [hμle1, hz4, hρpos, hμpos, norm_nonneg z]
    have hL : ‖Atr J T ((μ : ℂ) • z)‖ ≤ (K : ℝ) * (μ * ‖z‖) := by
      have hdist := hLipρ.dist_le_mul ((μ : ℂ) • z) hcz 0 hzero
      simp only [dist_eq_norm] at hdist
      rw [hA0, sub_zero, sub_zero, norm_smul, hc] at hdist
      exact hdist
    calc ‖Atr J (Tsh T μ (ne_of_gt hμpos)) z‖
        = ‖Atr J (Tsh T μ (ne_of_gt hμpos)) z - Atr J (Tsh T μ (ne_of_gt hμpos)) 0‖ := by
          rw [hAμ0, sub_zero]
      _ ≤ ‖Atr J T ((μ : ℂ) • z) - Atr J T ((μ : ℂ) • 0)‖ :=
          norm_Atr_Tsh_sub_le_c hμpos (ne_of_gt hμpos) z 0
      _ = ‖Atr J T ((μ : ℂ) • z)‖ := by rw [smul_zero, hA0, sub_zero]
      _ ≤ (K : ℝ) * (μ * ‖z‖) := hL
      _ ≤ M * μ * 4 := by nlinarith [hKle, hz4, hμpos, norm_nonneg z]
      _ ≤ ε := by nlinarith [hμle2, hε]
  · -- the Hölder seminorm bound
    intro z hz z' hz'
    have ht0 : (0 : ℝ) ≤ ‖z - z'‖ := norm_nonneg _
    have hpow : (0 : ℝ) ≤ ‖z - z'‖ ^ α := Real.rpow_nonneg ht0 α
    have hz4 : ‖z‖ ≤ 4 := norm_le_four_of_mem_pd_four_c hz
    have hz4' : ‖z'‖ ≤ 4 := norm_le_four_of_mem_pd_four_c hz'
    have hcz : ((μ : ℂ) • z) ∈ Metric.ball 0 ρ := by
      rw [Metric.mem_ball, dist_eq_norm, sub_zero, norm_smul, hc]
      nlinarith [hμle1, hz4, hρpos, hμpos, norm_nonneg z]
    have hcz' : ((μ : ℂ) • z') ∈ Metric.ball 0 ρ := by
      rw [Metric.mem_ball, dist_eq_norm, sub_zero, norm_smul, hc]
      nlinarith [hμle1, hz4', hρpos, hμpos, norm_nonneg z']
    have hL : ‖Atr J T ((μ : ℂ) • z) - Atr J T ((μ : ℂ) • z')‖
        ≤ (K : ℝ) * (μ * ‖z - z'‖) := by
      have hdist := hLipρ.dist_le_mul ((μ : ℂ) • z) hcz ((μ : ℂ) • z') hcz'
      simp only [dist_eq_norm] at hdist
      have hsub : ‖(μ : ℂ) • z - (μ : ℂ) • z'‖ = μ * ‖z - z'‖ := by
        rw [← smul_sub, norm_smul, hc]
      rw [hsub] at hdist
      exact hdist
    have hmain : ‖Atr J (Tsh T μ (ne_of_gt hμpos)) z - Atr J (Tsh T μ (ne_of_gt hμpos)) z'‖
        ≤ (K : ℝ) * (μ * ‖z - z'‖) :=
      (norm_Atr_Tsh_sub_le_c hμpos (ne_of_gt hμpos) z z').trans hL
    rcases le_or_gt ‖z - z'‖ 1 with ht1 | ht1
    · -- small distances: `‖z - z'‖ ≤ ‖z - z'‖ ^ α`
      have hself : ‖z - z'‖ ≤ ‖z - z'‖ ^ α := rpow_self_le_of_le_one_c hα0 hα1 ht0 ht1
      calc ‖Atr J (Tsh T μ (ne_of_gt hμpos)) z - Atr J (Tsh T μ (ne_of_gt hμpos)) z'‖
          ≤ (K : ℝ) * (μ * ‖z - z'‖) := hmain
        _ ≤ M * μ * ‖z - z'‖ := by nlinarith [hKle, ht0, hμpos]
        _ ≤ M * μ * ‖z - z'‖ ^ α := mul_le_mul_of_nonneg_left hself hμnn
        _ ≤ (ε / 9) * ‖z - z'‖ ^ α := mul_le_mul_of_nonneg_right hμle2 hpow
        _ ≤ ε * ‖z - z'‖ ^ α := by
            apply mul_le_mul_of_nonneg_right _ hpow
            linarith [hε]
    · -- large distances: `1 ≤ ‖z - z'‖ ^ α` and `‖z - z'‖ ≤ 8`
      have hone : 1 ≤ ‖z - z'‖ ^ α := Real.one_le_rpow (le_of_lt ht1) (le_of_lt hα0)
      have ht8 : ‖z - z'‖ ≤ 8 := by
        calc ‖z - z'‖ ≤ ‖z‖ + ‖z'‖ := norm_sub_le _ _
          _ ≤ 8 := by linarith
      calc ‖Atr J (Tsh T μ (ne_of_gt hμpos)) z - Atr J (Tsh T μ (ne_of_gt hμpos)) z'‖
          ≤ (K : ℝ) * (μ * ‖z - z'‖) := hmain
        _ ≤ M * μ * ‖z - z'‖ := by nlinarith [hKle, ht0, hμpos]
        _ ≤ M * μ * 8 := mul_le_mul_of_nonneg_left ht8 hμnn
        _ ≤ (ε / 9) * 8 := mul_le_mul_of_nonneg_right hμle2 (by norm_num)
        _ ≤ ε := by linarith [hε]
        _ ≤ ε * ‖z - z'‖ ^ α := by nlinarith [hone, hε]

end Work.NN.Final
