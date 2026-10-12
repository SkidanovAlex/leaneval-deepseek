import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBogFS.W1funDecay_momentsAbs
import Submission.Work.BoseBoxFock.L1Tails.kernelTail
import Submission.Work.BoseBoxFock.PCFU.UnivFrames
import Submission.Work.BoseBoxFock.PCFU.kappaL_windowSum_le
import Submission.Work.BoseFixR.LatGreen.W1funPeriodSummable
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.taper_pairing_aux` — the vocabulary of the UV-taper pairing bound

Target (same directory): `Work.BoseBoxFock.PCFU.taper_pairing_le`, the bound

    ‖∫_w∫_y (KfrU(v,h,μ,fu,N)(w−y) − latPer3 ℓ (W1fun v h ℓ)(w−y))·H w y‖
      ≤ C √((1+R)⁶/Λ · ℓ⁹ · ∫∫ Σ_j ‖∂_{w_j}H‖²) ,

`ℓ = ellH v μ`, `Λ = uvRad ℓ N` (`= 2πN/(4ℓ)`, the UV cut-off radius of the truncation).

The intended proof is `Work.BoseBoxFock.L1Tails.kernelTail` (the truncation tail of the `χχ`
periodised kernel) fed by `Work.BoseBoxFock.PCFU.coulTail_W1fun` (its `hτ` input), after
identifying `KfrU` with the *truncated lattice Fourier sum*

    KfrU v h μ fu N z = Σ_{n ∈ taperS N} taperC fu ℓ N n · Ŵ₁(κ_n) · e^{i⟪κ_n,z⟫}

where

* `taperS N = univ.image (labVec N)` is the label cube `Lab N ≃ [−N,N]³` as a set of lattice
  vectors,
* `taperC fu ℓ N n = ((uvCut fu (uvRad ℓ N) (kappaL ℓ n) : ℝ) : ℂ)` is the UV taper,
* `κ_n = kappaL ℓ n` and `Ŵ₁ = kinFT (W1fun v h ℓ)`.

This module collects the vocabulary and the elementary lemmas about it; the target file contains
the assembly.

Everything here is `sorry`-free.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock.PCFU

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The label cube `Lab N ≃ [−N,N]³` as a finite set of lattice vectors. -/
def taperS (N : ℕ) : Finset (Fin 3 → ℤ) := Finset.univ.image (Work.BoseBoxFock.labVec N)

/-- The UV taper of the truncated lattice sum, at `Λ = uvRad ℓ N`. -/
def taperC (fu : Work.BoseBoxFix.LowCut) (ℓ : ℝ) (N : ℕ) (n : Fin 3 → ℤ) : ℂ :=
  ((Work.BoseBoxFock.uvCut fu (Work.BoseBoxFock.uvRad ℓ N) (Work.BoseBoxFock.kappaL ℓ n) : ℝ) : ℂ)

/-! ## 1. The label cube -/

/-- The least-absolute representative of an integer `j` with `|j| ≤ N` in `ZMod (2N+1)` is `j`
itself: `valMinAbs` is a bijection `ZMod (2N+1) → [−N,N]`. -/
lemma intCast_valMinAbs_of_abs_le (N : ℕ) {j : ℤ} (hj : |j| ≤ (N : ℤ)) :
    ((j : ZMod (2 * N + 1))).valMinAbs = j := by
  haveI : NeZero (2 * N + 1) := ⟨by omega⟩
  rw [ZMod.valMinAbs_spec]
  refine ⟨rfl, ?_⟩
  obtain ⟨h1, h2⟩ := abs_le.mp hj
  constructor <;> push_cast <;> omega

/-- `labVec N` is injective (the centred representative is unique). -/
lemma labVec_injective (N : ℕ) : Function.Injective (Work.BoseBoxFock.labVec N) := by
  intro a b h
  funext i
  exact ZMod.valMinAbs_inj.mp (congrFun h i)

/-- Every integer vector of the cube `[−N,N]³` is `labVec N` of a label. -/
lemma labVec_surjOn_cube (N : ℕ) {m : Fin 3 → ℤ} (hm : ∀ i, |m i| ≤ (N : ℤ)) :
    ∃ k : Work.BoseBoxFock.Lab N, Work.BoseBoxFock.labVec N k = m := by
  refine ⟨fun i => ((m i : ℤ) : ZMod (2 * N + 1)), funext fun i => ?_⟩
  exact intCast_valMinAbs_of_abs_le N (hm i)

/-- Membership in `taperS N` is testifying a label. -/
lemma mem_taperS {N : ℕ} {n : Fin 3 → ℤ} :
    n ∈ taperS N ↔ ∃ k : Work.BoseBoxFock.Lab N, Work.BoseBoxFock.labVec N k = n := by
  rw [taperS, Finset.mem_image]
  exact ⟨fun ⟨k, _, hk⟩ => ⟨k, hk⟩, fun ⟨k, hk⟩ => ⟨k, Finset.mem_univ k, hk⟩⟩

/-- The momentum of a label is the sampling lattice point of its centred integer vector. -/
lemma kmomLab_eq_kappaL (ℓ : ℝ) (N : ℕ) (k : Work.BoseBoxFock.Lab N) :
    Work.BoseBoxFock.kmomLab ℓ N k = Work.BoseBoxFock.kappaL ℓ (Work.BoseBoxFock.labVec N k) := rfl

/-! ## 2. The UV taper -/

/-- The cut-off radius is positive at `N ≥ 1`, `ℓ > 0`. -/
lemma uvRad_pos {ℓ : ℝ} {N : ℕ} (hℓ : 0 < ℓ) (hN : 1 ≤ N) :
    0 < Work.BoseBoxFock.uvRad ℓ N := by
  rw [Work.BoseBoxFock.uvRad]
  have h1 : (0 : ℝ) < 2 * Real.pi / ℓ := by positivity
  have h2 : (0 : ℝ) < (N : ℝ) / 4 := by
    have : (0 : ℝ) < (N : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hN
    positivity
  calc (0 : ℝ) < (2 * Real.pi / ℓ) * ((N : ℝ) / 4) := mul_pos h1 h2
    _ = 2 * Real.pi / ℓ * (N : ℝ) / 4 := by ring

/-- The taper is bounded by `1`. -/
lemma taperC_le_one (fu : Work.BoseBoxFix.LowCut) (ℓ : ℝ) (N : ℕ) (n : Fin 3 → ℤ) :
    ‖taperC fu ℓ N n‖ ≤ 1 := by
  simp only [taperC, Work.BoseBoxFock.uvCut]
  rw [Complex.norm_of_nonneg (Work.BoseBoxFix.LowCut.nonneg fu _)]
  exact Work.BoseBoxFix.LowCut.le_one fu _

/-- The taper is exactly `1` strictly below the cut-off. -/
lemma taperC_eq_one_of_lt {fu : Work.BoseBoxFix.LowCut} {ℓ : ℝ} {N : ℕ}
    (hΛ : 0 < Work.BoseBoxFock.uvRad ℓ N) {n : Fin 3 → ℤ}
    (hn : ‖Work.BoseBoxFock.kappaL ℓ n‖ < Work.BoseBoxFock.uvRad ℓ N) :
    taperC fu ℓ N n = 1 := by
  have ht : ‖Work.BoseBoxFock.kappaL ℓ n‖ / Work.BoseBoxFock.uvRad ℓ N ≤ 1 :=
    le_of_lt ((div_lt_one hΛ).mpr hn)
  have h1 : Work.BoseBoxFock.uvCut fu (Work.BoseBoxFock.uvRad ℓ N)
      (Work.BoseBoxFock.kappaL ℓ n)
      = fu.f (‖Work.BoseBoxFock.kappaL ℓ n‖ / Work.BoseBoxFock.uvRad ℓ N) := rfl
  rw [taperC, h1, Work.BoseBoxFix.LowCut.one fu _ ht]
  norm_num

/-- Every lattice vector strictly inside the cut-off ball is a label of the cube. -/
lemma mem_taperS_of_norm_lt {ℓ : ℝ} (hℓ : 0 < ℓ) {N : ℕ} (hN : 1 ≤ N) {n : Fin 3 → ℤ}
    (hn : ‖Work.BoseBoxFock.kappaL ℓ n‖ < Work.BoseBoxFock.uvRad ℓ N) : n ∈ taperS N := by
  rw [mem_taperS]
  have hfac : (0 : ℝ) < 2 * Real.pi / ℓ := by positivity
  have hnorm : ‖Work.BoseBoxFock.kappaL ℓ n‖
      = (2 * Real.pi / ℓ) * ‖Work.BoseBoxFock.latVec n‖ :=
    Work.BoseBoxFock.L1Tails.norm_kappaL_eq_latVec hℓ n
  rw [hnorm, Work.BoseBoxFock.uvRad] at hn
  have hlt : ‖Work.BoseBoxFock.latVec n‖ < (N : ℝ) / 4 := by
    have h2 : (2 * Real.pi / ℓ) * ‖Work.BoseBoxFock.latVec n‖
        < (2 * Real.pi / ℓ) * ((N : ℝ) / 4) := by
      have heq : 2 * Real.pi / ℓ * (N : ℝ) / 4 = (2 * Real.pi / ℓ) * ((N : ℝ) / 4) := by ring
      rwa [heq] at hn
    nlinarith [h2, hfac]
  have hNi : (0 : ℝ) ≤ (N : ℝ) := by positivity
  refine labVec_surjOn_cube N (fun i => ?_)
  have h1 : |(((n i : ℤ)) : ℝ)| ≤ ‖Work.BoseBoxFock.latVec n‖ := by
    have h2 := PiLp.norm_apply_le (Work.BoseBoxFock.latVec n) i
    rw [Work.BoseBoxFock.latVec_apply, Real.norm_eq_abs] at h2
    exact h2
  have h2 : |((n i : ℤ) : ℝ)| ≤ (N : ℝ) := by
    have h3 : ‖Work.BoseBoxFock.latVec n‖ ≤ (N : ℝ) / 4 := le_of_lt hlt
    have h4 : (N : ℝ) / 4 ≤ (N : ℝ) := by linarith
    linarith
  exact_mod_cast h2

/-! ## 3. Basic facts about the hypotheses of the target -/

/-- `ellH` is `sideAt` once the latter is positive. -/
lemma ellH_eq_sideAt_of_pos {v : E3 → ℝ} {μ : ℝ}
    (h : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) :
    Work.BoseBoxFock.ellH v μ = Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := by
  rw [Work.BoseBoxFock.ellH, if_pos h]

/-- `W₁` vanishes off the ball of radius `R` containing the support of `v`. -/
lemma W1fun_eq_zero_of_le_norm' {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {R ℓ : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) {y : E3} (hy : R ≤ ‖y‖) :
    Work.BoseFixR.W1fun v h ℓ y = 0 :=
  Work.BoseFixR.LatGreen.W1fun_eq_zero_of_le_norm h hv_supp hy

/-- A uniform bound for a smooth box-supported kernel. -/
lemma taper_exists_bound_H {ℓ : ℝ} {H : E3 → E3 → ℂ}
    (hH : Continuous (Function.uncurry H))
    (hHs : ∀ w y, H w y ≠ 0 →
      w ∈ Work.BoseK15.corpusBox.boxL ℓ ∧ y ∈ Work.BoseK15.corpusBox.boxL ℓ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ w y, ‖H w y‖ ≤ M :=
  Work.BoseBoxFock.L1Tails.latPair_exists_bound_H hH hHs

/-- For a box-supported smooth `H`, each slice `y ↦ H w y` is integrable. -/
lemma taper_integrable_H_slice {ℓ : ℝ} {H : E3 → E3 → ℂ}
    (hH : Continuous (Function.uncurry H))
    (hHs : ∀ w y, H w y ≠ 0 →
      w ∈ Work.BoseK15.corpusBox.boxL ℓ ∧ y ∈ Work.BoseK15.corpusBox.boxL ℓ)
    (w : E3) : Integrable (fun y : E3 => H w y) volume := by
  refine Continuous.integrable_of_hasCompactSupport ?_ ?_
  · exact hH.comp (continuous_const.prodMk continuous_id)
  · refine HasCompactSupport.of_support_subset_isCompact
      (Work.BoseBoxFock.L1Tails.latPair_boxL_isCompact ℓ) ?_
    intro y hy
    exact (hHs w y (Function.mem_support.mp hy)).2

/-- The full kernel `(w,y) ↦ H w y` is integrable. -/
lemma taper_integrable_H_prod {ℓ : ℝ} {H : E3 → E3 → ℂ}
    (hH : Continuous (Function.uncurry H))
    (hHs : ∀ w y, H w y ≠ 0 →
      w ∈ Work.BoseK15.corpusBox.boxL ℓ ∧ y ∈ Work.BoseK15.corpusBox.boxL ℓ) :
    Integrable (fun p : E3 × E3 => H p.1 p.2) (volume.prod volume) := by
  obtain ⟨M, hM0, hM⟩ := taper_exists_bound_H hH hHs
  have hind := Work.BoseBoxFock.L1Tails.latPair_integrable_indicator_boxL ℓ
  have hmaj : Integrable (fun p : E3 × E3 => (M *
      (Work.BoseK15.corpusBox.boxL ℓ).indicator (fun _ => (1 : ℝ)) p.1) *
      (Work.BoseK15.corpusBox.boxL ℓ).indicator (fun _ => (1 : ℝ)) p.2)
      (volume.prod volume) :=
    Integrable.mul_prod (hind.const_mul M) hind
  refine Integrable.mono' hmaj hH.aestronglyMeasurable ?_
  filter_upwards with p
  have hbound : ‖H p.1 p.2‖ ≤ M *
      (Work.BoseK15.corpusBox.boxL ℓ).indicator (fun _ => (1 : ℝ)) p.1 *
      (Work.BoseK15.corpusBox.boxL ℓ).indicator (fun _ => (1 : ℝ)) p.2 := by
    by_cases hp : p.1 ∈ Work.BoseK15.corpusBox.boxL ℓ
    · by_cases hq : p.2 ∈ Work.BoseK15.corpusBox.boxL ℓ
      · rw [Set.indicator_of_mem hp, Set.indicator_of_mem hq, mul_one, mul_one]
        exact hM p.1 p.2
      · have hz : H p.1 p.2 = 0 := by
          by_contra hne
          exact hq (hHs p.1 p.2 hne).2
        simp [Set.indicator_of_notMem hq, hz]
    · have hz : H p.1 p.2 = 0 := by
        by_contra hne
        exact hp (hHs p.1 p.2 hne).1
      simp [Set.indicator_of_notMem hp, hz]
  exact hbound

/-! ## 4. The `KfrU` side: continuity, boundedness, integrability -/

/-- The `univ` `k`-frame is a finite sum of plane waves, hence continuous. -/
lemma taper_continuous_KfrU (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (μ : ℝ)
    (fu : Work.BoseBoxFix.LowCut) (N : ℕ) : Continuous (KfrU v h μ fu N) := by
  rw [show KfrU v h μ fu N = (fun z : E3 => ∑ k : Work.BoseBoxFock.Lab N,
      ((Work.BoseBoxFock.W1h v h μ fu N k : ℝ) : ℂ)
        * Complex.exp (Complex.I * (inner ℝ
            (Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) N k) z : ℂ))) from by
    funext z; simp only [KfrU]]
  fun_prop

/-- Pointwise bound for the `univ` `k`-frame. -/
lemma taper_norm_KfrU_le_sum (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (μ : ℝ)
    (fu : Work.BoseBoxFix.LowCut) (N : ℕ) (z : E3) :
    ‖KfrU v h μ fu N z‖
      ≤ ∑ k : Work.BoseBoxFock.Lab N, ‖((Work.BoseBoxFock.W1h v h μ fu N k : ℝ) : ℂ)‖ := by
  rw [KfrU]
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun k _ => ?_))
  rw [norm_mul]
  have h1 : ‖Complex.exp (Complex.I * (inner ℝ
      (Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) N k) z : ℂ))‖ = 1 := by
    rw [show Complex.I * ((inner ℝ
          (Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) N k) z : ℝ) : ℂ)
        = ((inner ℝ (Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) N k) z : ℝ) : ℂ)
          * Complex.I by ring]
    exact Complex.norm_exp_ofReal_mul_I _
  rw [h1, mul_one]

/-- For a box-supported smooth `H`, the `KfrU`-pairing slice is integrable. -/
lemma taper_integrable_KfrU_inner {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {μ : ℝ} {N : ℕ}
    {fu : Work.BoseBoxFix.LowCut} {H : E3 → E3 → ℂ}
    (hH : Continuous (Function.uncurry H))
    (hHs : ∀ w y, H w y ≠ 0 →
      w ∈ Work.BoseK15.corpusBox.boxL (Work.BoseBoxFock.ellH v μ)
        ∧ y ∈ Work.BoseK15.corpusBox.boxL (Work.BoseBoxFock.ellH v μ))
    (w : E3) : Integrable (fun y : E3 => KfrU v h μ fu N (w - y) * H w y) volume := by
  refine Integrable.mono' ((taper_integrable_H_slice hH hHs w).norm.const_mul
      (∑ k : Work.BoseBoxFock.Lab N, ‖((Work.BoseBoxFock.W1h v h μ fu N k : ℝ) : ℂ)‖)) ?_ ?_
  · exact (((taper_continuous_KfrU v h μ fu N).comp
      (continuous_const.sub continuous_id)).mul (hH.comp
        (continuous_const.prodMk continuous_id))).aestronglyMeasurable
  · filter_upwards with y
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (taper_norm_KfrU_le_sum v h μ fu N _) (norm_nonneg _)

end Work.BoseBoxFock.PCFU
