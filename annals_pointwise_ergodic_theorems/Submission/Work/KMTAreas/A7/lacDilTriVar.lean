/-
# The triangular-smoothing (Fejér) lacunary variational estimate

This is the **martingale/Lépingle half** of the discrete `ℤ`-model lacunary bump-dilation
variational estimate `Work.KMTAreas.A7.lacunaryBumpDilationVar`: for a `2`-lacunary sequence of
integral scales `σ`, the `r`-variation (`2 < r`) of the family of triangular (Fejér) smoothings
`n ↦ triSmooth σ n f = triConv (lacLev σ n) f` is bounded on `ℓᵖ(ℤ)`, `1 < p < ∞`, by
`C ‖f‖_{ℓᵖ}`, with `C` depending only on `p` and `r`.

The proof is a martingale argument.  The triangular smoothing is the average of the *shifted
lattice conditional expectations* over a complete residue system of shifts,

  `triConv k g = (2^L)⁻¹ ∑_{τ < 2^L} latticeExp k τ g`   (`k ≤ L`),

and for fixed `τ` the family `k ↦ latticeExp k τ g` is a *reverse* martingale (the σ-algebras
`latticeSpan k τ` coarsen as `k` grows), for which Lépingle's variational inequality holds in `ℓᵖ`
(`Work.Analysis.Hilbert.latticeWalk_var_le`).  Since the variational norm is subadditive and
positively homogeneous, the variation of the average is bounded by the average of the variations,
which gives the claim with no loss in `L`; the index `n` of the family is clamped at `K` (so that
the horizon `lacLev σ K + 1` is finite) and the clamp is removed by monotone convergence
(`variationalNorm_eq_iSup_comp_min`, `eLpNorm_iSup_le_of_le`).

The `ℝ`-valued form of Lépingle applies to the real and imaginary parts of `f` separately; the
pointwise splitting `triConv k f = triConv k (re f) + i · triConv k (im f)` and the subadditivity
of the variational norm then give the complex case.
-/
import Mathlib
import ChallengeDeps
import Submission.Work.KMTAreas.A7.lacDilDefs
import Submission.Work.KMTAreas.A7.varPart_comp_le_varPathCL
import Submission.Work.KMTAreas.A7.varPathCL_latticeExpR_le
import Submission.Work.KMTAreas.A7.eLpNorm_latVarSupR_le
import Submission.Work.KMTAreas.A7.latVarSupR_le_of_integrable_case
import Submission.Work.KMTAreas.A7.memLp_re_im_memLp_integrable
import Submission.Port.Aesm

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7

open MeasureTheory Finset
open scoped ENNReal BigOperators

noncomputable section

/-! ## The `ℝ≥0∞`-valued `eLpNorm` toolbox on `ℤ` -/

/-- Every `ℝ≥0∞`-valued function on `ℤ` is measurable. -/
lemma measurable_ennreal_int (u : ℤ → ℝ≥0∞) : Measurable u := measurable_of_countable u

/-- Every `ℝ≥0∞`-valued function on `ℤ` is almost everywhere measurable. -/
lemma aemeasurable_ennreal_int {μ : Measure ℤ} (u : ℤ → ℝ≥0∞) : AEMeasurable u μ :=
  (measurable_of_countable u).aemeasurable

/-- Monotonicity of `eLpNorm` for `ℝ≥0∞`-valued functions. -/
lemma eLpNorm_mono_ennreal {u v : ℤ → ℝ≥0∞} (h : ∀ x, u x ≤ v x) {q : ℝ≥0∞}
    (hq0 : q ≠ 0) (hqt : q ≠ ∞) {μ : Measure ℤ} :
    eLpNorm u q μ ≤ eLpNorm v q μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) hq0 hqt,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) hq0 hqt]
  have hq : 0 < q.toReal := ENNReal.toReal_pos hq0 hqt
  refine ENNReal.rpow_le_rpow ?_ (by positivity)
  refine lintegral_mono fun x => ?_
  simp only [enorm_eq_self]
  exact ENNReal.rpow_le_rpow (h x) hq.le

/-- Subadditivity of `eLpNorm` for `ℝ≥0∞`-valued functions. -/
lemma eLpNorm_add_le_ennreal {u v : ℤ → ℝ≥0∞} {q : ℝ≥0∞} (hq : 1 ≤ q) (hqt : q ≠ ∞)
    {μ : Measure ℤ} :
    eLpNorm (u + v) q μ ≤ eLpNorm u q μ + eLpNorm v q μ := by
  have hq0 : q ≠ 0 := by rintro rfl; exact absurd hq (by simp)
  have hq1 : (1 : ℝ) ≤ q.toReal := by
    have h := ENNReal.toReal_mono (a := (1 : ℝ≥0∞)) (b := q) hqt hq
    simpa using h
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) hq0 hqt,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) hq0 hqt,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) hq0 hqt]
  have key := ENNReal.lintegral_Lp_add_le (μ := μ) (p := q.toReal)
    (f := fun x => u x) (g := fun x => v x)
    (aemeasurable_ennreal_int u) (aemeasurable_ennreal_int v) hq1
  simpa only [Pi.add_apply, enorm_eq_self] using key

/-- Finite subadditivity of `eLpNorm` for `ℝ≥0∞`-valued functions. -/
lemma eLpNorm_finset_sum_le_ennreal {ι : Type*} (s : Finset ι) (u : ι → ℤ → ℝ≥0∞)
    {q : ℝ≥0∞} (hq : 1 ≤ q) (hqt : q ≠ ∞) {μ : Measure ℤ} :
    eLpNorm (fun x => ∑ i ∈ s, u i x) q μ ≤ ∑ i ∈ s, eLpNorm (u i) q μ := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      have h1 : (fun x : ℤ => ∑ i ∈ insert a s, u i x)
          = u a + (fun x => ∑ i ∈ s, u i x) := by
        funext x; simp [Finset.sum_insert ha]
      rw [h1, Finset.sum_insert ha]
      exact (eLpNorm_add_le_ennreal hq hqt).trans (add_le_add le_rfl ih)

/-! ## TEMPORARY STUBS FOR THE DELEGATED PIECES (removed once the children's modules are imported) -/

/-! ## The finite-subadditivity of the variational norm -/

/-- The variational norm of a finite sum of sequences is at most the sum of the variational norms. -/
lemma variationalNorm_finset_sum_le {r : NNReal} (hr : 1 ≤ r) {ι : Type*} (s : Finset ι)
    (a : ι → ℕ → ℂ) :
    PointwiseErgodicTheorems.variationalNorm r (fun n => ∑ i ∈ s, a i n)
      ≤ ∑ i ∈ s, PointwiseErgodicTheorems.variationalNorm r (a i) := by
  classical
  induction s using Finset.induction with
  | empty =>
      have h0 : (fun n : ℕ => ∑ i ∈ (∅ : Finset ι), a i n) = 0 := by
        funext n; simp
      rw [h0, Finset.sum_empty]
      have hz : PointwiseErgodicTheorems.variationalNorm r (0 : ℕ → ℂ) = 0 := by
        have h := Submission.PointwiseErgodicTheorems.variationalNorm_smul (r := r) hr
          (0 : ℂ) (0 : ℕ → ℂ)
        simpa using h
      rw [hz]
  | insert i s hi ih =>
      have h1 : (fun n : ℕ => ∑ j ∈ insert i s, a j n)
          = a i + (fun n => ∑ j ∈ s, a j n) := by
        funext n; simp [Finset.sum_insert hi]
      rw [h1, Finset.sum_insert hi]
      exact (Submission.PointwiseErgodicTheorems.variationalNorm_add_le hr _ _).trans
        (add_le_add le_rfl ih)

/-! ## Calculus with `triConv`, `latticeExp` and `latticeExpR` -/

/-- **The averaging identity for the triangular smoothing**, in the `Finset.range` form used below. -/
lemma triConv_eq_avg_latticeExp {k L : ℕ} (h : k ≤ L) (g : ℤ → ℂ) (x : ℤ) :
    Work.Analysis.Hilbert.triConv k g x
      = ((2 : ℂ) ^ L)⁻¹ * ∑ τ ∈ Finset.range (2 ^ L),
          Work.Analysis.Hilbert.latticeExp k (τ : ℤ) g x := by
  have hcast : ((2 : ℤ) ^ L) = ((2 ^ L : ℕ) : ℤ) := by push_cast; ring
  have key := Work.Analysis.Hilbert.lattice_exp_average (k := k) (K := L) h g x
  rw [hcast, ← Work.Analysis.Hilbert.sum_range_eq_sum_Ico (2 ^ L)
    (fun j : ℤ => Work.Analysis.Hilbert.latticeExp k j g x)] at key
  have h3 : ((2 : ℂ) ^ L) ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [key, ← mul_assoc, inv_mul_cancel₀ h3, one_mul]

/-- `latticeExp` of a real-valued function is the complex coercion of `latticeExpR`. -/
lemma latticeExp_coe (k : ℕ) (τ : ℤ) (h : ℤ → ℝ) (x : ℤ) :
    Work.Analysis.Hilbert.latticeExp k τ (fun m => (h m : ℂ)) x
      = (Work.Analysis.Hilbert.latticeExpR k τ h x : ℂ) := by
  simp only [Work.Analysis.Hilbert.latticeExp, Work.Analysis.Hilbert.latticeExpR]
  push_cast
  rfl

/-- The level-`0` lattice average is the function itself. -/
lemma latticeExpR_zero (τ : ℤ) (h : ℤ → ℝ) (x : ℤ) :
    Work.Analysis.Hilbert.latticeExpR 0 τ h x = h x := by
  simp [Work.Analysis.Hilbert.latticeExpR, Work.Analysis.Hilbert.latticeBase_zero]

/-- The `L^p` seminorm of `x ↦ ‖f x‖ₑ` is the `L^p` seminorm of `f`, for `q ∉ {0, ∞}`. -/
lemma eLpNorm_enorm_eq (f : ℤ → ℂ) {q : ℝ≥0∞} (hq0 : q ≠ 0) (hqt : q ≠ ∞) :
    eLpNorm (fun x : ℤ => ‖f x‖ₑ) q (Measure.count : Measure ℤ)
      = eLpNorm f q (Measure.count : Measure ℤ) := by
  have h1 : (∫⁻ (x : ℤ), ‖‖f x‖ₑ‖ₑ ^ q.toReal ∂(Measure.count : Measure ℤ))
      = ∫⁻ (x : ℤ), ‖f x‖ₑ ^ q.toReal ∂(Measure.count : Measure ℤ) :=
    lintegral_congr fun x => by simp only [enorm_eq_self]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) hq0 hqt,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) hq0 hqt, h1]

/-- `triConv` of a complex-valued function splits into its real and imaginary parts. -/
lemma triConv_re_add_im (k : ℕ) (f : ℤ → ℂ) :
    Work.Analysis.Hilbert.triConv k f
      = (fun x => Work.Analysis.Hilbert.triConv k (fun m => ((f m).re : ℂ)) x)
        + (fun x => Complex.I * Work.Analysis.Hilbert.triConv k (fun m => ((f m).im : ℂ)) x) := by
  funext x
  simp only [Pi.add_apply, Work.Analysis.Hilbert.triConv, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  have h := Complex.re_add_im (f (x - d))
  calc (Work.Analysis.Hilbert.triKernel k d : ℂ) * f (x - d)
      = (Work.Analysis.Hilbert.triKernel k d : ℂ)
          * ((f (x - d)).re + (f (x - d)).im * Complex.I) := by
        conv_lhs => rw [← h]
    _ = (Work.Analysis.Hilbert.triKernel k d : ℂ) * (f (x - d)).re
          + Complex.I * ((Work.Analysis.Hilbert.triKernel k d : ℂ) * (f (x - d)).im) := by ring

/-! ## The single-step estimate -/

/-- **The pointwise single-step estimate.**  Each atom average `latticeExpR (lev n) τ h x` is
dominated by the *level-`0`* average `h x` plus one single chain sum of `latVarSupR r L τ h x`. -/
lemma iSup_enorm_latticeExpR_le (r : NNReal) (hr : 0 < (r : ℝ)) (L : ℕ) (τ : ℤ) (h : ℤ → ℝ)
    (lev : ℕ → ℕ) (hL : ∀ n, lev n < L) (x : ℤ) :
    (⨆ n : ℕ, ‖(Work.Analysis.Hilbert.latticeExpR (lev n) τ h x : ℂ)‖ₑ)
      ≤ ‖((h x : ℝ) : ℂ)‖ₑ + latVarSupR r L τ h x := by
  have hbase : ‖(Work.Analysis.Hilbert.latticeExpR 0 τ h x : ℂ)‖ₑ = ‖((h x : ℝ) : ℂ)‖ₑ := by
    rw [latticeExpR_zero]
  refine iSup_le fun n => ?_
  have hdiff : ‖(Work.Analysis.Hilbert.latticeExpR (lev n) τ h x : ℂ)
      - (Work.Analysis.Hilbert.latticeExpR 0 τ h x : ℂ)‖ₑ ≤ latVarSupR r L τ h x := by
    rcases eq_or_ne (lev n) 0 with h0 | h0
    · rw [h0, sub_self]
      have hz : ‖((0 : ℂ))‖ₑ = (0 : ℝ≥0∞) := by simp
      rw [hz]
      exact (bot_le : (0 : ℝ≥0∞) ≤ latVarSupR r L τ h x)
    · have hLn : 0 < L := lt_of_le_of_lt (Nat.zero_le (lev n)) (hL n)
      set u : ℕ → ℕ := fun j => if j = 0 then L - lev n else L + (j - 1) with hu
      have hu0 : u 0 = L - lev n := by simp [hu]
      have husucc : ∀ c : ℕ, u (c + 1) = L + c := by
        intro c
        have hne : c + 1 ≠ 0 := Nat.succ_ne_zero c
        simp only [hu, if_neg hne]
        ring_nf
        simp
      have humono : StrictMono u := by
        intro a b hab
        rcases Nat.eq_zero_or_pos a with ha | ha
        · obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : b ≠ 0)
          rw [ha, hu0, husucc d]
          have hlt : L - lev n < L := Nat.sub_lt hLn (Nat.pos_of_ne_zero h0)
          omega
        · obtain ⟨c, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp ha)
          obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : b ≠ 0)
          rw [husucc, husucc]
          exact Nat.add_lt_add_left (Nat.succ_lt_succ_iff.mp hab) _
      have hterm : (∑ j ∈ Finset.range 1,
            |Work.Analysis.Hilbert.latticeExpR (L - u (j + 1)) τ h x
              - Work.Analysis.Hilbert.latticeExpR (L - u j) τ h x| ^ (r : ℝ))
          = |Work.Analysis.Hilbert.latticeExpR 0 τ h x
              - Work.Analysis.Hilbert.latticeExpR (lev n) τ h x| ^ (r : ℝ) := by
        have h1 : L - u 0 = lev n := by
          rw [hu0]
          exact Nat.sub_sub_self (le_of_lt (hL n))
        have h2 : L - u 1 = 0 := by
          rw [show u 1 = L from by simpa using husucc 0]
          exact Nat.sub_self L
        simp [h1, h2]
      have hrne : (r : ℝ) ≠ 0 := ne_of_gt hr
      have hrpow : (|Work.Analysis.Hilbert.latticeExpR 0 τ h x
            - Work.Analysis.Hilbert.latticeExpR (lev n) τ h x| ^ (r : ℝ)) ^ (1 / (r : ℝ))
          = |Work.Analysis.Hilbert.latticeExpR 0 τ h x
            - Work.Analysis.Hilbert.latticeExpR (lev n) τ h x| := by
        rw [← Real.rpow_mul (abs_nonneg _), mul_one_div_cancel hrne, Real.rpow_one]
      have hkey : ENNReal.ofReal |Work.Analysis.Hilbert.latticeExpR 0 τ h x
            - Work.Analysis.Hilbert.latticeExpR (lev n) τ h x| ≤ latVarSupR r L τ h x := by
        have h1 : ENNReal.ofReal ((∑ j ∈ Finset.range 1,
              |Work.Analysis.Hilbert.latticeExpR (L - u (j + 1)) τ h x
                - Work.Analysis.Hilbert.latticeExpR (L - u j) τ h x| ^ (r : ℝ))
              ^ (1 / (r : ℝ))) ≤ latVarSupR r L τ h x :=
          le_iSup_of_le (⟨u, humono⟩ : {u : ℕ → ℕ // StrictMono u}) (le_iSup_of_le 1 le_rfl)
        rw [hterm, hrpow] at h1
        exact h1
      have hcnorm : ‖(Work.Analysis.Hilbert.latticeExpR (lev n) τ h x : ℂ)
            - (Work.Analysis.Hilbert.latticeExpR 0 τ h x : ℂ)‖ₑ
          = ENNReal.ofReal |Work.Analysis.Hilbert.latticeExpR 0 τ h x
            - Work.Analysis.Hilbert.latticeExpR (lev n) τ h x| := by
        rw [← ofReal_norm,
          show (Work.Analysis.Hilbert.latticeExpR (lev n) τ h x : ℂ)
              - (Work.Analysis.Hilbert.latticeExpR 0 τ h x : ℂ)
            = ((Work.Analysis.Hilbert.latticeExpR (lev n) τ h x
                - Work.Analysis.Hilbert.latticeExpR 0 τ h x : ℝ) : ℂ) from by push_cast; ring]
        exact (congrArg ENNReal.ofReal (RCLike.norm_ofReal (K := ℂ)
            (Work.Analysis.Hilbert.latticeExpR (lev n) τ h x
              - Work.Analysis.Hilbert.latticeExpR 0 τ h x))).trans (by rw [abs_sub_comm])
      rw [hcnorm]
      exact hkey
  calc ‖(Work.Analysis.Hilbert.latticeExpR (lev n) τ h x : ℂ)‖ₑ
      = ‖((Work.Analysis.Hilbert.latticeExpR (lev n) τ h x : ℂ)
          - (Work.Analysis.Hilbert.latticeExpR 0 τ h x : ℂ))
          + (Work.Analysis.Hilbert.latticeExpR 0 τ h x : ℂ)‖ₑ := by
        rw [sub_add_cancel]
    _ ≤ ‖(Work.Analysis.Hilbert.latticeExpR (lev n) τ h x : ℂ)
          - (Work.Analysis.Hilbert.latticeExpR 0 τ h x : ℂ)‖ₑ
        + ‖(Work.Analysis.Hilbert.latticeExpR 0 τ h x : ℂ)‖ₑ := enorm_add_le _ _
    _ = ‖(Work.Analysis.Hilbert.latticeExpR 0 τ h x : ℂ)‖ₑ
        + ‖(Work.Analysis.Hilbert.latticeExpR (lev n) τ h x : ℂ)
          - (Work.Analysis.Hilbert.latticeExpR 0 τ h x : ℂ)‖ₑ := add_comm _ _
    _ ≤ ‖((h x : ℝ) : ℂ)‖ₑ + latVarSupR r L τ h x := by
        rw [hbase]
        exact add_le_add le_rfl hdiff

/-! ## The fixed-shift martingale estimate -/

/-- **The `ℓᵖ` estimate for the family of shifted lattice averages.** -/
theorem triVar_latticeExpR_le (p : ℝ) (hp : 1 < p) (r : NNReal) (hr : 2 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ (h : ℤ → ℝ),
      MemLp h (ENNReal.ofReal p) (Measure.count : Measure ℤ) →
      ∀ (lev : ℕ → ℕ), Monotone lev → ∀ (L : ℕ), (∀ n, lev n < L) → ∀ τ : ℤ,
      eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => (Work.Analysis.Hilbert.latticeExpR (lev n) τ h x : ℂ)))
        (ENNReal.ofReal p) (Measure.count : Measure ℤ)
        ≤ ENNReal.ofReal C * eLpNorm h (ENNReal.ofReal p) (Measure.count : Measure ℤ) := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := eLpNorm_latVarSupR_le p hp r hr
  have hC₂ := latVarSupR_le_of_integrable_case p hp r hC₁
  have hr1 : (1 : NNReal) ≤ r := by
    have : (2 : NNReal) ≤ r := le_of_lt hr
    exact le_trans (by norm_num) this
  have hr1' : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
  have hr0 : (0 : ℝ) < (r : ℝ) := lt_of_lt_of_le one_pos hr1'
  have hp1 : (1 : ℝ) ≤ p := le_of_lt hp
  have hq0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr (lt_of_lt_of_le one_pos hp1)).ne'
  have hqt : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have hq1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp1
  refine ⟨1 + 2 * C₁, by linarith, ?_⟩
  intro h hh lev hlev L hL τ
  have hbase : eLpNorm (fun x : ℤ => ‖((h x : ℝ) : ℂ)‖ₑ) (ENNReal.ofReal p)
      (Measure.count : Measure ℤ)
      ≤ eLpNorm h (ENNReal.ofReal p) (Measure.count : Measure ℤ) := by
    rw [eLpNorm_enorm_eq (fun x : ℤ => ((h x : ℝ) : ℂ)) hq0 hqt]
    exact eLpNorm_mono (hf := by pw_aesm) (fun x => by simp)
  have hbdd : ∀ x : ℤ, PointwiseErgodicTheorems.variationalNorm r
      (fun n : ℕ => (Work.Analysis.Hilbert.latticeExpR (lev n) τ h x : ℂ))
      ≤ ‖((h x : ℝ) : ℂ)‖ₑ + 2 * latVarSupR r L τ h x := by
    intro x
    have hsup : (⨆ n : ℕ, ‖(Work.Analysis.Hilbert.latticeExpR (lev n) τ h x : ℂ)‖ₑ)
        ≤ ‖((h x : ℝ) : ℂ)‖ₑ + latVarSupR r L τ h x :=
      iSup_enorm_latticeExpR_le r hr0 L τ h lev hL x
    have hvar : Submission.PointwiseErgodicTheorems.varPart r
        (fun n : ℕ => (Work.Analysis.Hilbert.latticeExpR (lev n) τ h x : ℂ))
        ≤ latVarSupR r L τ h x :=
      (varPart_comp_le_varPathCL hr1
          (fun k : ℕ => (Work.Analysis.Hilbert.latticeExpR k τ h x : ℂ)) lev hlev L
          (fun n => le_of_lt (hL n))).trans
        (varPathCL_latticeExpR_le r L τ h x)
    rw [Submission.PointwiseErgodicTheorems.variationalNorm_eq_add]
    calc (⨆ n : ℕ, ‖(Work.Analysis.Hilbert.latticeExpR (lev n) τ h x : ℂ)‖ₑ)
          + Submission.PointwiseErgodicTheorems.varPart r
              (fun n : ℕ => (Work.Analysis.Hilbert.latticeExpR (lev n) τ h x : ℂ))
        ≤ (‖((h x : ℝ) : ℂ)‖ₑ + latVarSupR r L τ h x)
          + latVarSupR r L τ h x := add_le_add hsup hvar
      _ = ‖((h x : ℝ) : ℂ)‖ₑ + 2 * latVarSupR r L τ h x := by
          ring
  calc eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => (Work.Analysis.Hilbert.latticeExpR (lev n) τ h x : ℂ)))
        (ENNReal.ofReal p) (Measure.count : Measure ℤ)
      ≤ eLpNorm (fun x : ℤ => ‖((h x : ℝ) : ℂ)‖ₑ
          + 2 * latVarSupR r L τ h x) (ENNReal.ofReal p) (Measure.count : Measure ℤ) :=
        eLpNorm_mono_ennreal hbdd hq0 hqt
    _ ≤ eLpNorm (fun x : ℤ => ‖((h x : ℝ) : ℂ)‖ₑ)
          (ENNReal.ofReal p) (Measure.count : Measure ℤ)
        + eLpNorm (fun x : ℤ => 2 * latVarSupR r L τ h x) (ENNReal.ofReal p)
          (Measure.count : Measure ℤ) :=
        eLpNorm_add_le_ennreal hq1 hqt
    _ = eLpNorm (fun x : ℤ => ‖((h x : ℝ) : ℂ)‖ₑ)
          (ENNReal.ofReal p) (Measure.count : Measure ℤ)
        + 2 * eLpNorm (latVarSupR r L τ h) (ENNReal.ofReal p) (Measure.count : Measure ℤ) := by
        rw [Commons.MeasureTheory.Lp.eLpNorm_const_mul_ennreal (c := (2 : ℝ≥0∞))
          (by simp) hq0 hqt]
    _ ≤ eLpNorm h (ENNReal.ofReal p) (Measure.count : Measure ℤ)
        + 2 * (ENNReal.ofReal C₁ * eLpNorm h (ENNReal.ofReal p) (Measure.count : Measure ℤ)) :=
        add_le_add hbase (mul_le_mul_right (hC₂ h hh L τ) 2)
    _ = ENNReal.ofReal (1 + 2 * C₁) * eLpNorm h (ENNReal.ofReal p) (Measure.count : Measure ℤ) := by
        rw [ENNReal.ofReal_add (by norm_num) (by linarith),
          ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2), ENNReal.ofReal_one,
          ENNReal.ofReal_ofNat]
        ring

/-! ## The averaging step: from the lattice averages to the triangular smoothing -/

/-- **The `ℓᵖ` estimate for the triangular smoothings.** -/
theorem triVar_triConv_le (p : ℝ) (hp : 1 < p) (r : NNReal) (hr : 2 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ (h : ℤ → ℝ),
      MemLp h (ENNReal.ofReal p) (Measure.count : Measure ℤ) →
      ∀ (lev : ℕ → ℕ), Monotone lev → ∀ (L : ℕ), (∀ n, lev n < L) →
      eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Work.Analysis.Hilbert.triConv (lev n) (fun m => (h m : ℂ)) x))
        (ENNReal.ofReal p) (Measure.count : Measure ℤ)
        ≤ ENNReal.ofReal C * eLpNorm h (ENNReal.ofReal p) (Measure.count : Measure ℤ) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := triVar_latticeExpR_le p hp r hr
  have hp1 : (1 : ℝ) ≤ p := le_of_lt hp
  have hq0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr (lt_of_lt_of_le one_pos hp1)).ne'
  have hqt : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have hq1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp1
  have hr1 : (1 : NNReal) ≤ r := le_trans (by norm_num : (1:NNReal) ≤ 2) (le_of_lt hr)
  refine ⟨C₀, hC₀pos, ?_⟩
  intro h hh lev hlev L hL
  have hc : ‖((2 : ℂ) ^ L)⁻¹‖ₑ = ((2 : ℝ≥0∞) ^ L)⁻¹ := by
    rw [← ofReal_norm, norm_inv, norm_pow, show ‖(2 : ℂ)‖ = 2 by norm_num,
      ENNReal.ofReal_inv_of_pos (by positivity),
      ENNReal.ofReal_pow (show (0:ℝ) ≤ 2 by norm_num) L, ENNReal.ofReal_ofNat]
  have hpt : ∀ x : ℤ, PointwiseErgodicTheorems.variationalNorm r
      (fun n : ℕ => Work.Analysis.Hilbert.triConv (lev n) (fun m => (h m : ℂ)) x)
      ≤ ((2 : ℝ≥0∞) ^ L)⁻¹ * ∑ τ ∈ Finset.range (2 ^ L),
          PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => (Work.Analysis.Hilbert.latticeExpR (lev n) (τ : ℤ) h x : ℂ)) := by
    intro x
    have hfam : (fun n : ℕ => Work.Analysis.Hilbert.triConv (lev n) (fun m => (h m : ℂ)) x)
        = ((2 : ℂ) ^ L)⁻¹ • (fun n : ℕ => ∑ τ ∈ Finset.range (2 ^ L),
            Work.Analysis.Hilbert.latticeExp (lev n) (τ : ℤ) (fun m => (h m : ℂ)) x) := by
      funext n
      rw [Pi.smul_apply, smul_eq_mul, triConv_eq_avg_latticeExp (le_of_lt (hL n))]
    have hcoe : ∀ n : ℕ, (∑ τ ∈ Finset.range (2 ^ L),
          Work.Analysis.Hilbert.latticeExp (lev n) (τ : ℤ) (fun m => (h m : ℂ)) x)
        = ∑ τ ∈ Finset.range (2 ^ L),
            (Work.Analysis.Hilbert.latticeExpR (lev n) (τ : ℤ) h x : ℂ) := by
      intro n
      exact Finset.sum_congr rfl fun τ _ => latticeExp_coe (lev n) (τ : ℤ) h x
    have h2 : PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => ∑ τ ∈ Finset.range (2 ^ L),
          Work.Analysis.Hilbert.latticeExp (lev n) (τ : ℤ) (fun m => (h m : ℂ)) x)
        ≤ ∑ τ ∈ Finset.range (2 ^ L), PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => (Work.Analysis.Hilbert.latticeExpR (lev n) (τ : ℤ) h x : ℂ)) := by
      rw [show (fun n : ℕ => ∑ τ ∈ Finset.range (2 ^ L),
            Work.Analysis.Hilbert.latticeExp (lev n) (τ : ℤ) (fun m => (h m : ℂ)) x)
          = (fun n : ℕ => ∑ τ ∈ Finset.range (2 ^ L),
            (Work.Analysis.Hilbert.latticeExpR (lev n) (τ : ℤ) h x : ℂ)) from by
        funext n; exact hcoe n]
      exact variationalNorm_finset_sum_le hr1 (Finset.range (2 ^ L))
        (fun τ : ℕ => fun n : ℕ =>
          (Work.Analysis.Hilbert.latticeExpR (lev n) (τ : ℤ) h x : ℂ))
    rw [hfam, Submission.PointwiseErgodicTheorems.variationalNorm_smul hr1, hc]
    exact mul_le_mul_right h2 _
  calc eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => Work.Analysis.Hilbert.triConv (lev n) (fun m => (h m : ℂ)) x))
        (ENNReal.ofReal p) (Measure.count : Measure ℤ)
      ≤ eLpNorm (fun x : ℤ => ((2 : ℝ≥0∞) ^ L)⁻¹ * ∑ τ ∈ Finset.range (2 ^ L),
          PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => (Work.Analysis.Hilbert.latticeExpR (lev n) (τ : ℤ) h x : ℂ)))
          (ENNReal.ofReal p) (Measure.count : Measure ℤ) :=
        eLpNorm_mono_ennreal hpt hq0 hqt
    _ = ((2 : ℝ≥0∞) ^ L)⁻¹ * eLpNorm (fun x : ℤ => ∑ τ ∈ Finset.range (2 ^ L),
          PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => (Work.Analysis.Hilbert.latticeExpR (lev n) (τ : ℤ) h x : ℂ)))
          (ENNReal.ofReal p) (Measure.count : Measure ℤ) :=
        Commons.MeasureTheory.Lp.eLpNorm_const_mul_ennreal (c := ((2 : ℝ≥0∞) ^ L)⁻¹)
          (by simp) hq0 hqt
    _ ≤ ((2 : ℝ≥0∞) ^ L)⁻¹ * ∑ τ ∈ Finset.range (2 ^ L),
          eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => (Work.Analysis.Hilbert.latticeExpR (lev n) (τ : ℤ) h x : ℂ)))
            (ENNReal.ofReal p) (Measure.count : Measure ℤ) :=
        mul_le_mul_right (eLpNorm_finset_sum_le_ennreal (Finset.range (2 ^ L))
          (fun τ : ℕ => fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => (Work.Analysis.Hilbert.latticeExpR (lev n) (τ : ℤ) h x : ℂ)))
          hq1 hqt) _
    _ ≤ ((2 : ℝ≥0∞) ^ L)⁻¹ * ∑ τ ∈ Finset.range (2 ^ L),
          ENNReal.ofReal C₀ * eLpNorm h (ENNReal.ofReal p) (Measure.count : Measure ℤ) :=
        (by
          refine mul_le_mul_right ?_ _
          refine Finset.sum_le_sum ?_
          intro τ _
          exact hC₀ h hh lev hlev L hL (τ : ℤ))
    _ = ENNReal.ofReal C₀ * eLpNorm h (ENNReal.ofReal p) (Measure.count : Measure ℤ) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc,
          show ((2 : ℝ≥0∞) ^ L)⁻¹ * ((2 ^ L : ℕ) : ℝ≥0∞) = 1 from by
            rw [Nat.cast_pow, Nat.cast_ofNat,
              ENNReal.inv_mul_cancel (by positivity) (by simp)],
          one_mul]

/-! ## The main theorem -/

/-- **The lacunary variational estimate for the triangular (Fejér) smoothings** (the
martingale/Lépingle half of `Work.KMTAreas.A7.lacunaryBumpDilationVar`). -/
theorem lacDilTriVar (p : ℝ) (hp : 1 < p) (r : NNReal) (hr : 2 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ (σ : ℕ → ℕ), (∀ n, 1 ≤ σ n) → (∀ n, 2 * σ n ≤ σ (n + 1)) →
      ∀ f : ℤ → ℂ,
      MeasureTheory.eLpNorm
          (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => Work.KMTAreas.A7.triSmooth σ n f x))
          (ENNReal.ofReal p) (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
        ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm f (ENNReal.ofReal p)
            (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := triVar_triConv_le p hp r hr
  have hp1 : (1 : ℝ) ≤ p := le_of_lt hp
  have hq0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr (lt_of_lt_of_le one_pos hp1)).ne'
  have hqt : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have hq1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp1
  have hr1 : (1 : NNReal) ≤ r := le_trans (by norm_num : (1:NNReal) ≤ 2) (le_of_lt hr)
  refine ⟨2 * C₀, by linarith, ?_⟩
  intro σ hσ1 hσ2 f
  rcases eq_top_or_lt_top (eLpNorm f (ENNReal.ofReal p) (Measure.count : Measure ℤ)) with
    htop | hlt
  · rw [htop]
    have hmul : ENNReal.ofReal (2 * C₀) * (⊤ : ℝ≥0∞) = ⊤ :=
      ENNReal.mul_top (ENNReal.ofReal_pos.mpr (by linarith : (0:ℝ) < 2 * C₀)).ne'
    rw [hmul]
    exact le_top
  · have hae : AEStronglyMeasurable f (Measure.count : Measure ℤ) :=
      (measurable_of_countable f).aemeasurable.aestronglyMeasurable
    have hf : MemLp f (ENNReal.ofReal p) (Measure.count : Measure ℤ) := memLp_iff.mpr hlt
    obtain ⟨hre, him⟩ := memLp_re_im_memLp_integrable (lt_of_lt_of_le one_pos hp1) hf
    have hf_le : eLpNorm (fun x : ℤ => (f x).re) (ENNReal.ofReal p) (Measure.count : Measure ℤ)
        ≤ eLpNorm f (ENNReal.ofReal p) (Measure.count : Measure ℤ) :=
      eLpNorm_mono (hf := by pw_aesm) (fun x => by simpa using Complex.abs_re_le_norm (f x))
    have hf_le' : eLpNorm (fun x : ℤ => (f x).im) (ENNReal.ofReal p) (Measure.count : Measure ℤ)
        ≤ eLpNorm f (ENNReal.ofReal p) (Measure.count : Measure ℤ) :=
      eLpNorm_mono (hf := by pw_aesm) (fun x => by simpa using Complex.abs_im_le_norm (f x))
    have hbound : ∀ K : ℕ, eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => Work.KMTAreas.A7.triSmooth σ (min n K) f x))
        (ENNReal.ofReal p) (Measure.count : Measure ℤ)
        ≤ ENNReal.ofReal (2 * C₀) * eLpNorm f (ENNReal.ofReal p) (Measure.count : Measure ℤ) := by
      intro K
      set lev : ℕ → ℕ := fun n => lacLev σ (min n K) with hlevdef
      have hlev : Monotone lev := fun i j hij =>
        lacLev_mono hσ2 (min_le_min hij le_rfl)
      have hL : ∀ n : ℕ, lev n < lacLev σ K + 1 := by
        intro n
        have h : lev n ≤ lacLev σ K := lacLev_mono hσ2 (min_le_right n K)
        omega
      have hsplit : ∀ x : ℤ, PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Work.KMTAreas.A7.triSmooth σ (min n K) f x)
          ≤ PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => Work.Analysis.Hilbert.triConv (lev n) (fun m => ((f m).re : ℂ)) x)
            + PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => Work.Analysis.Hilbert.triConv (lev n) (fun m => ((f m).im : ℂ)) x) := by
        intro x
        have hfam : (fun n : ℕ => Work.KMTAreas.A7.triSmooth σ (min n K) f x)
            = (fun n : ℕ => Work.Analysis.Hilbert.triConv (lev n) (fun m => ((f m).re : ℂ)) x)
              + (Complex.I • (fun n : ℕ => Work.Analysis.Hilbert.triConv (lev n)
                  (fun m => ((f m).im : ℂ)) x)) := by
          funext n
          have h1 : Work.KMTAreas.A7.triSmooth σ (min n K) f x
              = Work.Analysis.Hilbert.triConv (lev n) f x := rfl
          rw [h1, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          exact congrFun (triConv_re_add_im (lev n) f) x
        have hI : ‖Complex.I‖ₑ = 1 := by
          rw [← ofReal_norm, show ‖Complex.I‖ = 1 from by norm_num, ENNReal.ofReal_one]
        have hsm : PointwiseErgodicTheorems.variationalNorm r
            (Complex.I • (fun n : ℕ => Work.Analysis.Hilbert.triConv (lev n)
                (fun m => ((f m).im : ℂ)) x))
            = PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => Work.Analysis.Hilbert.triConv (lev n)
                (fun m => ((f m).im : ℂ)) x) := by
          rw [Submission.PointwiseErgodicTheorems.variationalNorm_smul hr1, hI, one_mul]
        rw [hfam]
        calc PointwiseErgodicTheorems.variationalNorm r
              ((fun n : ℕ => Work.Analysis.Hilbert.triConv (lev n) (fun m => ((f m).re : ℂ)) x)
                + (Complex.I • (fun n : ℕ => Work.Analysis.Hilbert.triConv (lev n)
                    (fun m => ((f m).im : ℂ)) x)))
            ≤ PointwiseErgodicTheorems.variationalNorm r
                (fun n : ℕ => Work.Analysis.Hilbert.triConv (lev n) (fun m => ((f m).re : ℂ)) x)
              + PointwiseErgodicTheorems.variationalNorm r
                (Complex.I • (fun n : ℕ => Work.Analysis.Hilbert.triConv (lev n)
                    (fun m => ((f m).im : ℂ)) x)) :=
              Submission.PointwiseErgodicTheorems.variationalNorm_add_le hr1 _ _
          _ = _ := by rw [hsm]
      calc eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => Work.KMTAreas.A7.triSmooth σ (min n K) f x))
            (ENNReal.ofReal p) (Measure.count : Measure ℤ)
          ≤ eLpNorm (fun x : ℤ =>
              PointwiseErgodicTheorems.variationalNorm r
                (fun n : ℕ => Work.Analysis.Hilbert.triConv (lev n) (fun m => ((f m).re : ℂ)) x)
              + PointwiseErgodicTheorems.variationalNorm r
                (fun n : ℕ => Work.Analysis.Hilbert.triConv (lev n) (fun m => ((f m).im : ℂ)) x))
              (ENNReal.ofReal p) (Measure.count : Measure ℤ) :=
            eLpNorm_mono_ennreal hsplit hq0 hqt
        _ ≤ eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => Work.Analysis.Hilbert.triConv (lev n) (fun m => ((f m).re : ℂ)) x))
              (ENNReal.ofReal p) (Measure.count : Measure ℤ)
            + eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => Work.Analysis.Hilbert.triConv (lev n) (fun m => ((f m).im : ℂ)) x))
              (ENNReal.ofReal p) (Measure.count : Measure ℤ) :=
            eLpNorm_add_le_ennreal hq1 hqt
        _ ≤ ENNReal.ofReal C₀ * eLpNorm (fun x : ℤ => (f x).re) (ENNReal.ofReal p)
              (Measure.count : Measure ℤ)
            + ENNReal.ofReal C₀ * eLpNorm (fun x : ℤ => (f x).im) (ENNReal.ofReal p)
              (Measure.count : Measure ℤ) :=
            add_le_add (hC₀ (fun x => (f x).re) hre lev hlev (lacLev σ K + 1) hL)
              (hC₀ (fun x => (f x).im) him lev hlev (lacLev σ K + 1) hL)
        _ ≤ ENNReal.ofReal C₀ * eLpNorm f (ENNReal.ofReal p) (Measure.count : Measure ℤ)
            + ENNReal.ofReal C₀ * eLpNorm f (ENNReal.ofReal p) (Measure.count : Measure ℤ) :=
            add_le_add (mul_le_mul_right hf_le _) (mul_le_mul_right hf_le' _)
        _ = ENNReal.ofReal (2 * C₀) * eLpNorm f (ENNReal.ofReal p)
              (Measure.count : Measure ℤ) := by
            rw [← add_mul, ← ENNReal.ofReal_add (by linarith) (by linarith),
              show C₀ + C₀ = 2 * C₀ from by ring]
    have hmono : ∀ x : ℤ, Monotone fun K : ℕ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => Work.KMTAreas.A7.triSmooth σ (min n K) f x) := by
      intro x K K' hKK'
      exact Submission.PointwiseErgodicTheorems.variationalNorm_comp_min_mono r
        (fun n : ℕ => Work.KMTAreas.A7.triSmooth σ n f x) hKK'
    have hsup := Submission.PointwiseErgodicTheorems.eLpNorm_iSup_le_of_le hq0 hqt
      (fun K : ℕ => aemeasurable_ennreal_int (fun x : ℤ =>
        PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Work.KMTAreas.A7.triSmooth σ (min n K) f x))) hmono hbound
    rw [show (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Work.KMTAreas.A7.triSmooth σ n f x))
        = fun x : ℤ => ⨆ K : ℕ, PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Work.KMTAreas.A7.triSmooth σ (min n K) f x) from by
      funext x
      exact Submission.PointwiseErgodicTheorems.variationalNorm_eq_iSup_comp_min r
        (fun n : ℕ => Work.KMTAreas.A7.triSmooth σ n f x)]
    exact hsup

end

end Work.KMTAreas.A7
