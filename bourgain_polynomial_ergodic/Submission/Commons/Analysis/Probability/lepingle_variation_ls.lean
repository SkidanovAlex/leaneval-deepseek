import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.Probability.Martingale.OptionalSampling
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Commons.Probability.doob_lp_maximal
import Submission.Commons.Analysis.MeasureTheory.eLpNorm_rpow_toReal
import Submission.Commons.Analysis.Asymptotics.geom_finset_le
import Submission.Commons.Analysis.MeasureTheory.eLpNorm_iSup_of_monotone
import Submission.Commons.MeasureTheory.Lp.eLpNorm_finset_sum_le_ennreal
import Submission.Commons.MeasureTheory.Lp.eLpNorm_const_mul_ennreal

namespace Commons.Analysis.Probability

open _root_.MeasureTheory
open scoped BigOperators ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The martingale increment `d n = h (n+1) - h n`. -/
noncomputable def dinc (h : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ := h (n+1) - h n

/-- The prefix square function `∑_{n<N} d n²`. -/
noncomputable def preSq (h : ℕ → Ω → ℝ) (N : ℕ) : Ω → ℝ :=
  fun ω => ∑ n ∈ Finset.range N, (dinc h n ω)^2

/-- The square function `S² = ⨆_N preSq N`, as an `ℝ≥0∞`-valued function. -/
noncomputable def Ssq (h : ℕ → Ω → ℝ) : Ω → ℝ≥0∞ :=
  fun ω => ⨆ N : ℕ, ENNReal.ofReal (preSq h N ω)

/-- The maximal function `f* = ⨆_n |h n|`, as an `ℝ≥0∞`-valued function. -/
noncomputable def mstar (h : ℕ → Ω → ℝ) : Ω → ℝ≥0∞ :=
  fun ω => ⨆ n : ℕ, ENNReal.ofReal ‖h n ω‖

variable [IsProbabilityMeasure μ]

lemma measurable_dinc (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (h : ℕ → Ω → ℝ)
    (hmart : Martingale h ℱ μ) (n : ℕ) : Measurable (dinc h n) := by
  have h1 : Measurable (h (n+1)) :=
    (hmart.1 (n+1)).measurable.mono (ℱ.le' (n+1)) le_rfl
  have h2 : Measurable (h n) := (hmart.1 n).measurable.mono (ℱ.le' n) le_rfl
  simpa only [dinc] using h1.sub h2

/-- `preSq N` is `ℱ N`-measurable. -/
lemma measurable_preSq (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (h : ℕ → Ω → ℝ)
    (hmart : Martingale h ℱ μ) (N : ℕ) : Measurable[ℱ N] (preSq h N) := by
  have hsum : Measurable[ℱ N]
      (fun ω => ∑ n ∈ Finset.range N, (dinc h n ω)^2) :=
    Finset.measurable_sum _ (fun n hn => by
      have hnN : n + 1 ≤ N := by have := Finset.mem_range.mp hn; omega
      have h1 : Measurable[ℱ N] (h (n+1)) :=
        (hmart.1 (n+1)).measurable.mono (ℱ.mono hnN) le_rfl
      have h2 : Measurable[ℱ N] (h n) :=
        (hmart.1 n).measurable.mono (ℱ.mono (Nat.le_succ n |>.trans hnN)) le_rfl
      exact (h1.sub h2).pow_const 2)
  exact hsum

/-- The event `E_N = {preSq N ≤ λ < preSq (N+1)}`, which is `ℱ (N+1)`-measurable. -/
def Eset (h : ℕ → Ω → ℝ) (lam : ℝ) (N : ℕ) : Set Ω :=
  {ω | preSq h N ω ≤ lam ∧ lam < preSq h (N+1) ω}

lemma measurableSet_Eset (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (h : ℕ → Ω → ℝ)
    (hmart : Martingale h ℱ μ) (lam : ℝ) (N : ℕ) :
    MeasurableSet[ℱ (N+1)] (Eset h lam N) := by
  unfold Eset
  have h1 : Measurable[ℱ (N+1)] (preSq h N) :=
    (measurable_preSq ℱ h hmart N).mono (ℱ.mono (Nat.le_succ N)) le_rfl
  have h2 : Measurable[ℱ (N+1)] (preSq h (N+1)) := measurable_preSq ℱ h hmart (N+1)
  exact (measurableSet_le h1 measurable_const).inter
    (measurableSet_lt measurable_const h2)

/-- The increments have zero conditional expectation: `E[d n | ℱ n] = 0`. -/
lemma condExp_dinc (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (h : ℕ → Ω → ℝ)
    (hmart : Martingale h ℱ μ) (hint : ∀ n, MemLp (h n) 2 μ) (n : ℕ) :
    condExp (ℱ n) μ (dinc h n) =ᵐ[μ] 0 := by
  have hsub := condExp_sub ((hint (n+1)).integrable one_le_two) ((hint n).integrable one_le_two) (ℱ n)
  have h1 : condExp (ℱ n) μ (h (n+1)) =ᵐ[μ] h n := hmart.condExp_ae_eq (Nat.le_succ n)
  have h2 : condExp (ℱ n) μ (h n) =ᵐ[μ] h n := hmart.condExp_ae_eq le_rfl
  have key : condExp (ℱ n) μ (dinc h n) =ᵐ[μ]
      condExp (ℱ n) μ (h (n+1)) - condExp (ℱ n) μ (h n) := hsub
  filter_upwards [key, h1, h2] with ω hk h1ω h2ω
  simp only [Pi.sub_apply, Pi.zero_apply] at hk ⊢
  rw [hk, h1ω, h2ω, sub_self]

/-- Orthogonality of the martingale increments against `ℱ k`-measurable sets:
`∫_s h_k · d_k = 0` for `s ∈ ℱ k`. -/
lemma setIntegral_h_d (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (h : ℕ → Ω → ℝ)
    (hmart : Martingale h ℱ μ) (hint : ∀ n, MemLp (h n) 2 μ)
    (s : Set Ω) (k : ℕ) (hs : MeasurableSet[ℱ k] s) :
    ∫ ω in s, h k ω * dinc h k ω ∂μ = 0 := by
  haveI : SigmaFiniteFiltration μ ℱ := ⟨fun _ => inferInstance⟩
  have hik1 : Integrable (h (k+1)) μ := (hint (k+1)).integrable one_le_two
  have hik : Integrable (h k) μ := (hint k).integrable one_le_two
  have hikmul : Integrable (h k * h (k+1)) μ := MemLp.integrable_mul (hint k) (hint (k+1))
  have hkk : Integrable (h k * h k) μ := MemLp.integrable_mul (hint k) (hint k)
  have hpull : condExp (ℱ k) μ (h k * h (k+1)) =ᵐ[μ] h k * h k := by
    have h1 := condExp_mul_of_stronglyMeasurable_left (μ := μ) (m := ℱ k)
      (f := h k) (g := h (k+1)) (hmart.1 k) hikmul hik1
    have h2 := hmart.condExp_ae_eq (Nat.le_succ k)
    filter_upwards [h1, h2] with ω h1ω h2ω
    have : condExp (ℱ k) μ (h k * h (k+1)) ω
        = h k ω * condExp (ℱ k) μ (h (k+1)) ω := h1ω
    rw [this, h2ω]
    simp only [Pi.mul_apply]
  have hA : ∫ ω in s, (h k * h (k+1)) ω ∂μ = ∫ ω in s, (h k * h k) ω ∂μ := by
    rw [← setIntegral_condExp (m := ℱ k) (ℱ.le' k) hikmul hs]
    refine setIntegral_congr_ae (ℱ.le' k s hs) ?_
    filter_upwards [hpull] with ω hω _
    exact hω
  have hsub : ∫ ω in s, ((h k * h (k+1)) - (h k * h k)) ω ∂μ
      = ∫ ω in s, (h k * h (k+1)) ω ∂μ - ∫ ω in s, (h k * h k) ω ∂μ := by
    simp only [Pi.sub_apply]
    rw [integral_sub (μ := μ.restrict s) hikmul.integrableOn hkk.integrableOn]
  have hfinal : ∫ ω in s, ((h k * h (k+1)) - (h k * h k)) ω ∂μ = 0 := by
    rw [hsub, hA, sub_self]
  rw [dinc]
  convert hfinal using 2 with ω
  simp only [Pi.sub_apply, Pi.mul_apply]
  ring_nf

/-- Pointwise telescoping identity for the increments:
`∑_{k∈[N,M)} d_k² = d_N² + (h_M² − h_{N+1}²) − 2 ∑_{k∈[N+1,M)} h_k d_k`. -/
lemma pt_tele (h : ℕ → Ω → ℝ) (N M : ℕ) (hNM : N + 1 ≤ M) (ω : Ω) :
    ∑ k ∈ Finset.Ico N M, (dinc h k ω)^2
      = (dinc h N ω)^2
        + ((h M ω)^2 - (h (N+1) ω)^2)
        - 2 * ∑ k ∈ Finset.Ico (N+1) M, h k ω * dinc h k ω := by
  have htel : ∑ k ∈ Finset.Ico (N+1) M,
      ((h (k+1) ω)^2 - (h k ω)^2)
      = (h M ω)^2 - (h (N+1) ω)^2 :=
    Finset.sum_Ico_sub (fun k => (h k ω)^2) hNM
  have hdd : ∀ k : ℕ, (h (k+1) ω)^2 - (h k ω)^2
      = 2*(h k ω)*(dinc h k ω) + (dinc h k ω)^2 := by
    intro k; simp only [dinc, Pi.sub_apply]; ring
  have hsum : ∑ k ∈ Finset.Ico (N+1) M, (dinc h k ω)^2
      = ((h M ω)^2 - (h (N+1) ω)^2)
        - 2 * ∑ k ∈ Finset.Ico (N+1) M, h k ω * dinc h k ω := by
    have h2 : ∑ k ∈ Finset.Ico (N+1) M,
          ((h (k+1) ω)^2 - (h k ω)^2)
        = ∑ k ∈ Finset.Ico (N+1) M,
          (2*(h k ω)*(dinc h k ω)
            + (dinc h k ω)^2) :=
      Finset.sum_congr rfl (fun k _ => hdd k)
    rw [htel] at h2
    have h3 : ∑ k ∈ Finset.Ico (N+1) M,
          (2*(h k ω)*(dinc h k ω)
            + (dinc h k ω)^2)
        = 2 * (∑ k ∈ Finset.Ico (N+1) M, h k ω * dinc h k ω)
          + ∑ k ∈ Finset.Ico (N+1) M, (dinc h k ω)^2 := by
      rw [Finset.sum_add_distrib]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _; ring
    rw [h3] at h2
    linarith
  have hsplit : ∑ k ∈ Finset.Ico N M, (dinc h k ω)^2
      = (dinc h N ω)^2
        + ∑ k ∈ Finset.Ico (N+1) M, (dinc h k ω)^2 := by
    rw [show Finset.Ico N M = insert N (Finset.Ico (N+1) M) from by
      ext k; simp only [Finset.mem_Ico, Finset.mem_insert]; omega]
    rw [Finset.sum_insert (by simp [Finset.mem_Ico])]
  rw [hsplit, hsum]; ring

/-- The increments are in `L²`. -/
lemma memLp_dinc (h : ℕ → Ω → ℝ) (hint : ∀ n, MemLp (h n) 2 μ) (n : ℕ) :
    MemLp (dinc h n) 2 μ := by
  simp only [dinc]
  exact (hint (n+1)).sub (hint n)

/-- The squared increments are integrable. -/
lemma integrable_dinc_sq (h : ℕ → Ω → ℝ) (hint : ∀ n, MemLp (h n) 2 μ) (n : ℕ) :
    Integrable (fun ω => (dinc h n ω)^2) μ := by
  have h := memLp_dinc h hint n
  have := MemLp.integrable_mul h h
  convert this using 1
  ext ω; simp only [Pi.mul_apply]; ring

/-- The squared martingale values are integrable. -/
lemma integrable_h_sq (h : ℕ → Ω → ℝ) (hint : ∀ n, MemLp (h n) 2 μ) (n : ℕ) :
    Integrable (fun ω => (h n ω)^2) μ := by
  have h := hint n
  have := MemLp.integrable_mul h h
  convert this using 1
  ext ω; simp only [Pi.mul_apply]; ring

/-- The products `h_k · d_k` are integrable. -/
lemma integrable_h_mul_d (h : ℕ → Ω → ℝ) (hint : ∀ n, MemLp (h n) 2 μ) (n : ℕ) :
    Integrable (fun ω => h n ω * dinc h n ω) μ := by
  have h1 : MemLp (h n) 2 μ := hint n
  have h2 := memLp_dinc h hint n
  have := MemLp.integrable_mul h1 h2
  convert this using 1
  all_goals (ext ω; simp only [Pi.mul_apply])

/-- Integral form of the telescoping identity. -/
lemma setIntegral_tele (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (h : ℕ → Ω → ℝ)
    (hmart : Martingale h ℱ μ) (hint : ∀ n, MemLp (h n) 2 μ)
    (lam : ℝ) (N M : ℕ) (hNM : N + 1 ≤ M) :
    ∫ ω in Eset h lam N, (∑ k ∈ Finset.Ico N M, (dinc h k ω)^2) ∂μ
      = ∫ ω in Eset h lam N, (dinc h N ω)^2 ∂μ
        + ∫ ω in Eset h lam N,
            ((h M ω)^2 - (h (N+1) ω)^2) ∂μ := by
  set H := Eset h lam N with hHdef
  have hE : MeasurableSet[ℱ (N+1)] H := measurableSet_Eset ℱ h hmart lam N
  have hEamb : MeasurableSet H := (Filtration.le' ℱ (N+1)) H hE
  have hB : Integrable (fun ω => (dinc h N ω)^2) μ := integrable_dinc_sq h hint N
  have hC : Integrable (fun ω =>
      (h M ω)^2 - (h (N+1) ω)^2) μ :=
    (integrable_h_sq h hint M).sub (integrable_h_sq h hint (N+1))
  have hD : Integrable (fun ω => 2 * ∑ k ∈ Finset.Ico (N+1) M,
      h k ω * dinc h k ω) μ := by
    have hfun : (fun ω => 2 * ∑ k ∈ Finset.Ico (N+1) M,
        h k ω * dinc h k ω)
        = fun ω => ∑ k ∈ Finset.Ico (N+1) M,
            2 * (h k ω * dinc h k ω) := by
      ext ω; rw [Finset.mul_sum]
    rw [hfun]
    exact MeasureTheory.integrable_finsetSum _
      (fun k _ => (integrable_h_mul_d h hint k).const_mul 2)
  have hD0 : ∫ ω in H, (2 * ∑ k ∈ Finset.Ico (N+1) M,
      h k ω * dinc h k ω) ∂μ = 0 := by
    have hfun : (fun ω => 2 * ∑ k ∈ Finset.Ico (N+1) M,
        h k ω * dinc h k ω)
        = fun ω => ∑ k ∈ Finset.Ico (N+1) M,
            2 * (h k ω * dinc h k ω) := by
      ext ω; rw [Finset.mul_sum]
    rw [hfun, integral_finsetSum]
    · apply Finset.sum_eq_zero
      intro k hk
      have hk1 : N + 1 ≤ k := (Finset.mem_Ico.mp hk).1
      have hsk : MeasurableSet[ℱ k] H := (Filtration.mono ℱ hk1) H hE
      have h0 := setIntegral_h_d ℱ h hmart hint H k hsk
      calc ∫ ω in H, 2 * (h k ω * dinc h k ω) ∂μ
          = 2 * ∫ ω in H, h k ω * dinc h k ω ∂μ := by
            rw [integral_const_mul]
        _ = 2 * 0 := by rw [h0]
        _ = 0 := by ring
    · intro k _
      exact ((integrable_h_mul_d h hint k).const_mul 2).integrableOn
  have hpt : ∀ ω, (∑ k ∈ Finset.Ico N M, (dinc h k ω)^2)
      = (dinc h N ω)^2
        + ((h M ω)^2 - (h (N+1) ω)^2)
        - 2 * ∑ k ∈ Finset.Ico (N+1) M, h k ω * dinc h k ω :=
    fun ω => pt_tele h N M hNM ω
  rw [setIntegral_congr_fun hEamb (fun ω _ => hpt ω)]
  rw [show (∫ ω in H, ((dinc h N ω)^2
        + ((h M ω)^2 - (h (N+1) ω)^2)
        - 2 * ∑ k ∈ Finset.Ico (N+1) M, h k ω * dinc h k ω) ∂μ)
      = ∫ ω in H, ((dinc h N ω)^2
          + ((h M ω)^2 - (h (N+1) ω)^2)) ∂μ
        - ∫ ω in H, (2 * ∑ k ∈ Finset.Ico (N+1) M,
            h k ω * dinc h k ω) ∂μ from
    integral_sub (μ := μ.restrict H) (hB.add hC).integrableOn hD.integrableOn]
  rw [hD0, sub_zero]
  rw [show (∫ ω in H, ((dinc h N ω)^2
        + ((h M ω)^2 - (h (N+1) ω)^2)) ∂μ)
      = ∫ ω in H, (dinc h N ω)^2 ∂μ
        + ∫ ω in H, ((h M ω)^2 - (h (N+1) ω)^2) ∂μ from
    integral_add (μ := μ.restrict H) hB.integrableOn hC.integrableOn]

lemma pt_bound_h (h : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    ENNReal.ofReal ((h n ω)^2) ≤ (mstar h ω)^2 := by
  have h1 : ENNReal.ofReal ‖h n ω‖ ≤ mstar h ω := by
    show ENNReal.ofReal ‖h n ω‖ ≤ ⨆ m, ENNReal.ofReal ‖h m ω‖
    exact le_iSup (fun m => ENNReal.ofReal ‖h m ω‖) n
  have hsq : ((h n ω)^2) = ‖h n ω‖^2 := by
    rw [Real.norm_eq_abs, sq_abs]
  rw [hsq, ENNReal.ofReal_pow (norm_nonneg _)]
  exact pow_le_pow_left₀ (by positivity) h1 2

lemma pt_bound_d (h : ℕ → Ω → ℝ) (N : ℕ) (ω : Ω) :
    ENNReal.ofReal ((dinc h N ω)^2) ≤ 4 * (mstar h ω)^2 := by
  have h1 : ENNReal.ofReal ‖h (N+1) ω‖ ≤ mstar h ω := by
    show ENNReal.ofReal ‖h (N+1) ω‖ ≤ ⨆ m, ENNReal.ofReal ‖h m ω‖
    exact le_iSup (fun m => ENNReal.ofReal ‖h m ω‖) (N+1)
  have h2 : ENNReal.ofReal ‖h N ω‖ ≤ mstar h ω := by
    show ENNReal.ofReal ‖h N ω‖ ≤ ⨆ m, ENNReal.ofReal ‖h m ω‖
    exact le_iSup (fun m => ENNReal.ofReal ‖h m ω‖) N
  have hkey : ENNReal.ofReal ‖dinc h N ω‖ ≤ 2 * mstar h ω := by
    have hsub : ‖dinc h N ω‖ = ‖h (N+1) ω - h N ω‖ := by
      simp only [dinc, Pi.sub_apply]
    rw [hsub]
    calc ENNReal.ofReal ‖h (N+1) ω - h N ω‖
        ≤ ENNReal.ofReal (‖h (N+1) ω‖ + ‖h N ω‖) :=
          ENNReal.ofReal_le_ofReal (norm_sub_le _ _)
      _ = ENNReal.ofReal ‖h (N+1) ω‖
            + ENNReal.ofReal ‖h N ω‖ :=
          ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)
      _ ≤ mstar h ω + mstar h ω := add_le_add h1 h2
      _ = 2 * mstar h ω := by ring
  have hsq : ((dinc h N ω)^2) = ‖dinc h N ω‖^2 := by
    rw [Real.norm_eq_abs, sq_abs]
  rw [hsq, ENNReal.ofReal_pow (norm_nonneg _)]
  calc (ENNReal.ofReal ‖dinc h N ω‖)^2
      ≤ (2 * mstar h ω)^2 := pow_le_pow_left₀ (by positivity) hkey 2
    _ = 4 * (mstar h ω)^2 := by ring

lemma preSq_le_mstar (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (h : ℕ → Ω → ℝ)
    (hmart : Martingale h ℱ μ) (hint : ∀ n, MemLp (h n) 2 μ)
    (lam : ℝ) (N M : ℕ) (hNM : N + 1 ≤ M) :
    ∫⁻ ω in Eset h lam N,
        ENNReal.ofReal (∑ k ∈ Finset.Ico N M, (dinc h k ω)^2) ∂μ
      ≤ 5 * ∫⁻ ω in Eset h lam N, (mstar h ω)^2 ∂μ := by
  set H := Eset h lam N with hH
  have hE : MeasurableSet[ℱ (N+1)] H := measurableSet_Eset ℱ h hmart lam N
  have hA : Integrable (fun ω => ∑ k ∈ Finset.Ico N M, (dinc h k ω)^2) μ :=
    MeasureTheory.integrable_finsetSum _ (fun k _ => integrable_dinc_sq h hint k)
  have hB : Integrable (fun ω => (dinc h N ω)^2) μ := integrable_dinc_sq h hint N
  have hCsqM : Integrable (fun ω => (h M ω)^2) μ := integrable_h_sq h hint M
  have hC : Integrable (fun ω => (h M ω)^2 - (h (N+1) ω)^2) μ :=
    hCsqM.sub (integrable_h_sq h hint (N+1))
  have htel := setIntegral_tele ℱ h hmart hint lam N M hNM
  rw [show (∫⁻ ω in H, ENNReal.ofReal (∑ k ∈ Finset.Ico N M, (dinc h k ω)^2) ∂μ)
      = ENNReal.ofReal (∫ ω in H, (∑ k ∈ Finset.Ico N M, (dinc h k ω)^2) ∂μ) from
    (ofReal_integral_eq_lintegral_ofReal hA.integrableOn (Filter.Eventually.of_forall (fun ω => Finset.sum_nonneg (fun k _ => sq_nonneg _)))).symm]
  rw [htel]
  have h1 : ENNReal.ofReal (∫ ω in H, (dinc h N ω)^2 ∂μ)
      ≤ 4 * ∫⁻ ω in H, (mstar h ω)^2 ∂μ := by
    rw [ofReal_integral_eq_lintegral_ofReal hB.integrableOn (Filter.Eventually.of_forall (fun ω => sq_nonneg _))]
    calc ∫⁻ ω in H, ENNReal.ofReal ((dinc h N ω)^2) ∂μ
        ≤ ∫⁻ ω in H, 4 * (mstar h ω)^2 ∂μ :=
          lintegral_mono (fun ω => pt_bound_d h N ω)
      _ = 4 * ∫⁻ ω in H, (mstar h ω)^2 ∂μ :=
          lintegral_const_mul' 4 _ (by norm_num)
  have h2 : ENNReal.ofReal (∫ ω in H, ((h M ω)^2 - (h (N+1) ω)^2) ∂μ)
      ≤ ∫⁻ ω in H, (mstar h ω)^2 ∂μ := by
    calc ENNReal.ofReal (∫ ω in H, ((h M ω)^2 - (h (N+1) ω)^2) ∂μ)
        ≤ ENNReal.ofReal (∫ ω in H, (h M ω)^2 ∂μ) :=
          ENNReal.ofReal_le_ofReal (by
            apply integral_mono (μ := μ.restrict H) hC.integrableOn hCsqM.integrableOn
            intro ω; simp only [Pi.sub_apply]; nlinarith [sq_nonneg (h (N+1) ω)])
      _ = ∫⁻ ω in H, ENNReal.ofReal ((h M ω)^2) ∂μ :=
          ofReal_integral_eq_lintegral_ofReal hCsqM.integrableOn (Filter.Eventually.of_forall (fun ω => sq_nonneg _))
      _ ≤ ∫⁻ ω in H, (mstar h ω)^2 ∂μ :=
          lintegral_mono (fun ω => pt_bound_h h M ω)
  calc ENNReal.ofReal (∫ ω in H, (dinc h N ω)^2 ∂μ
          + ∫ ω in H, ((h M ω)^2 - (h (N+1) ω)^2) ∂μ)
      ≤ ENNReal.ofReal (∫ ω in H, (dinc h N ω)^2 ∂μ)
        + ENNReal.ofReal (∫ ω in H, ((h M ω)^2 - (h (N+1) ω)^2) ∂μ) :=
        ENNReal.ofReal_add_le
    _ ≤ 4 * ∫⁻ ω in H, (mstar h ω)^2 ∂μ + ∫⁻ ω in H, (mstar h ω)^2 ∂μ :=
        add_le_add h1 h2
    _ = 5 * ∫⁻ ω in H, (mstar h ω)^2 ∂μ := by ring

/-- The square function of the "rest" after time `N`. -/
noncomputable def restSq (h : ℕ → Ω → ℝ) (N : ℕ) : Ω → ℝ≥0∞ :=
  fun ω => ⨆ M : ℕ, ENNReal.ofReal (∑ k ∈ Finset.range M, (dinc h (N+k) ω)^2)

lemma integral_restSq_le (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (h : ℕ → Ω → ℝ)
    (hmart : Martingale h ℱ μ) (hint : ∀ n, MemLp (h n) 2 μ) (lam : ℝ) (N : ℕ) :
    ∫⁻ ω in Eset h lam N, restSq h N ω ∂μ
      ≤ 5 * ∫⁻ ω in Eset h lam N, (mstar h ω)^2 ∂μ := by
  simp only [restSq]
  rw [lintegral_iSup]
  swap
  · intro M
    exact ENNReal.measurable_ofReal.comp
      (Finset.measurable_sum _ (fun k _ => (measurable_dinc ℱ h hmart (N+k)).pow_const 2))
  swap
  · intro a b hab ω
    exact ENNReal.ofReal_le_ofReal (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_subset_range.mpr hab) (fun k _ _ => sq_nonneg _))
  apply iSup_le
  intro M
  rcases Nat.eq_zero_or_pos M with hM | hM
  · subst hM
    simp only [Finset.range_zero, Finset.sum_empty, ENNReal.ofReal_zero, lintegral_zero]
    exact bot_le
  · have hkey := preSq_le_mstar ℱ h hmart hint lam N (N+M) (by omega)
    have hfun : (fun ω => ENNReal.ofReal (∑ k ∈ Finset.range M, (dinc h (N+k) ω)^2))
        = fun ω => ENNReal.ofReal (∑ k ∈ Finset.Ico N (N+M), (dinc h k ω)^2) := by
      ext ω
      congr 1
      rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
    rw [hfun]
    exact hkey

lemma preSq_add (h : ℕ → Ω → ℝ) (N M : ℕ) (ω : Ω) :
    preSq h (N+M) ω = preSq h N ω + ∑ k ∈ Finset.range M, (dinc h (N+k) ω)^2 := by
  simp only [preSq]
  rw [Finset.sum_range_add]

lemma preSq_mono (h : ℕ → Ω → ℝ) {L N : ℕ} (hLN : L ≤ N) (ω : Ω) :
    preSq h L ω ≤ preSq h N ω :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hLN)
    (fun k _ _ => sq_nonneg _)

/-- The square function splits as the prefix part plus the rest. -/
lemma Ssq_eq_add (h : ℕ → Ω → ℝ) (N : ℕ) (ω : Ω) :
    Ssq h ω = ENNReal.ofReal (preSq h N ω) + restSq h N ω := by
  apply le_antisymm
  · apply iSup_le
    intro L
    by_cases hL : L ≤ N
    · exact le_add_right (ENNReal.ofReal_le_ofReal (preSq_mono h hL ω))
    · push_neg at hL
      have hLM : N + (L - N) = L := Nat.add_sub_of_le (le_of_lt hL)
      have h2 : preSq h L ω
          = preSq h N ω + ∑ k ∈ Finset.range (L - N), (dinc h (N+k) ω)^2 := by
        conv_lhs => rw [← hLM]
        exact preSq_add h N (L - N) ω
      rw [h2, ENNReal.ofReal_add (p := preSq h N ω)
        (q := ∑ k ∈ Finset.range (L - N), (dinc h (N+k) ω)^2)
        (Finset.sum_nonneg (fun k _ => sq_nonneg _)) (Finset.sum_nonneg (fun k _ => sq_nonneg _))]
      apply add_le_add_right
      simp only [restSq]
      exact le_iSup (fun M => ENNReal.ofReal
        (∑ k ∈ Finset.range M, (dinc h (N+k) ω)^2)) (L - N)
  · simp only [restSq]
    rw [ENNReal.add_iSup]
    apply iSup_le
    intro M
    rw [← ENNReal.ofReal_add
      (show 0 ≤ preSq h N ω from Finset.sum_nonneg (fun k _ => sq_nonneg _))
      (Finset.sum_nonneg (fun k _ => sq_nonneg _)), ← preSq_add]
    simp only [Ssq]
    exact le_iSup (fun L => ENNReal.ofReal (preSq h L ω)) (N + M)

/-- On `E_N ∩ {Ssq > ofReal (2 lam)}`, the rest square function exceeds `ofReal lam`. -/
lemma restSq_gt_of (h : ℕ → Ω → ℝ) (N : ℕ) {lam : ℝ}
    (hlam : 0 < lam) (ω : Ω) (hE : preSq h N ω ≤ lam)
    (hS : ENNReal.ofReal (2*lam) < Ssq h ω) :
    ENNReal.ofReal lam < restSq h N ω := by
  by_contra hcon
  push_neg at hcon
  have h2 : ENNReal.ofReal (preSq h N ω) + restSq h N ω
      ≤ ENNReal.ofReal lam + ENNReal.ofReal lam :=
    add_le_add (ENNReal.ofReal_le_ofReal hE) hcon
  rw [← ENNReal.ofReal_add hlam.le hlam.le] at h2
  rw [Ssq_eq_add h N ω, show (2:ℝ)*lam = lam + lam from by ring] at hS
  exact absurd (lt_of_lt_of_le hS h2) (lt_irrefl _)



section KeyIneq

lemma preSq_zero (h : ℕ → Ω → ℝ) (ω : Ω) : preSq h 0 ω = 0 := by
  simp [preSq]

/-- The events `Eset h lam N` are pairwise disjoint. -/
lemma disjoint_Eset {h : ℕ → Ω → ℝ} {lam : ℝ} {N M : ℕ} (hNM : N < M) :
    Disjoint (Eset h lam N) (Eset h lam M) := by
  rw [Set.disjoint_left]
  intro ω hN hM
  obtain ⟨hN1, hN2⟩ := hN
  obtain ⟨hM1, hM2⟩ := hM
  have hmono := preSq_mono h (show N+1 ≤ M by omega) ω
  linarith

/-- For `lam ≥ 0` the events `Eset h lam N`, `N < K`, partition `{lam < preSq h K}`. -/
lemma iUnion_Eset_eq {h : ℕ → Ω → ℝ} {lam : ℝ} (hlam : 0 ≤ lam) (K : ℕ) :
    (⋃ N ∈ Finset.range K, Eset h lam N) = {ω | lam < preSq h K ω} := by
  ext ω
  simp only [Set.mem_iUnion, Finset.mem_range, Set.mem_setOf_eq, Eset]
  constructor
  · rintro ⟨N, hNK, _, h2⟩
    exact lt_of_lt_of_le h2 (preSq_mono h (by omega) ω)
  · intro hK
    have hex : ∃ N, N ≤ K ∧ lam < preSq h N ω := ⟨K, le_rfl, hK⟩
    have hspec := Nat.find_spec hex
    have hN0pos : 0 < Nat.find hex := by
      by_contra hc
      push_neg at hc
      have h0 : Nat.find hex = 0 := Nat.eq_zero_of_le_zero hc
      rw [h0, preSq_zero] at hspec
      linarith [hspec.2, hlam]
    refine ⟨Nat.find hex - 1, by omega, ?_, ?_⟩
    · have hlt : Nat.find hex - 1 < Nat.find hex := Nat.sub_lt hN0pos Nat.one_pos
      have h1 := Nat.find_min hex hlt
      by_contra hcon
      push_neg at hcon
      exact h1 ⟨by omega, hcon⟩
    · have hsucc : Nat.find hex - 1 + 1 = Nat.find hex :=
        Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hN0pos.ne')
      rw [hsucc]
      exact hspec.2

/-- Key good-λ inequality for the BDG square function bound (prefix version). -/
lemma key_ineq (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (h : ℕ → Ω → ℝ)
    (hmart : Martingale h ℱ μ) (hint : ∀ n, MemLp (h n) 2 μ)
    {lam : ℝ} (hlam : 0 < lam) (K : ℕ) :
    μ {ω | 2*lam < preSq h K ω}
      ≤ 5 * ENNReal.ofReal lam⁻¹ *
          ∫⁻ ω in {ω | lam < preSq h K ω}, (mstar h ω)^2 ∂μ := by
  have hlam0 : 0 ≤ lam := hlam.le
  have hpreK : Measurable (preSq h K) := (measurable_preSq ℱ h hmart K).mono (ℱ.le' K) le_rfl
  have hEmeas : ∀ N, MeasurableSet (Eset h lam N) := fun N =>
    (Filtration.le' ℱ (N+1)) _ (measurableSet_Eset ℱ h hmart lam N)
  have hAmeas : MeasurableSet {ω : Ω | 2*lam < preSq h K ω} :=
    measurableSet_lt measurable_const hpreK
  have hsub : {ω : Ω | 2*lam < preSq h K ω} ⊆ ⋃ N ∈ Finset.range K, Eset h lam N := by
    rw [iUnion_Eset_eq hlam0 K]
    intro ω hω
    exact lt_trans (show lam < 2*lam by linarith) hω
  have hAeq : {ω : Ω | 2*lam < preSq h K ω}
      = ⋃ N ∈ Finset.range K, (Eset h lam N ∩ {ω : Ω | 2*lam < preSq h K ω}) := by
    refine Set.Subset.antisymm ?_ ?_
    · intro ω hω
      obtain ⟨N, hN, hE⟩ := Set.mem_iUnion₂.mp (hsub hω)
      exact Set.mem_iUnion₂.mpr ⟨N, hN, hE, hω⟩
    · intro ω hω
      obtain ⟨N, hN, hE, hA'⟩ := Set.mem_iUnion₂.mp hω
      exact hA'
  have hdisjA : Set.PairwiseDisjoint (↑(Finset.range K))
      (fun N => Eset h lam N ∩ {ω : Ω | 2*lam < preSq h K ω}) := by
    intro N _ M _ hNM
    rcases lt_or_gt_of_ne hNM with hmn | hmn
    · exact (disjoint_Eset hmn).mono Set.inter_subset_left Set.inter_subset_left
    · exact (disjoint_Eset hmn).symm.mono Set.inter_subset_left Set.inter_subset_left
  have hmeasA : ∀ N ∈ Finset.range K,
      MeasurableSet (Eset h lam N ∩ {ω : Ω | 2*lam < preSq h K ω}) :=
    fun N _ => (hEmeas N).inter hAmeas
  have hdisjE : Set.PairwiseDisjoint (↑(Finset.range K)) (fun N => Eset h lam N) := by
    intro N _ M _ hNM
    rcases lt_or_gt_of_ne hNM with hmn | hmn
    · exact disjoint_Eset hmn
    · exact (disjoint_Eset hmn).symm
  have hper : ∀ N ∈ Finset.range K,
      μ (Eset h lam N ∩ {ω : Ω | 2*lam < preSq h K ω})
        ≤ 5 * ENNReal.ofReal lam⁻¹ * ∫⁻ ω in Eset h lam N, (mstar h ω)^2 ∂μ := by
    intro N _
    set s := Eset h lam N ∩ {ω : Ω | 2*lam < preSq h K ω} with hs
    have hpt : ∀ ω ∈ s, ENNReal.ofReal lam < restSq h N ω := by
      rintro ω ⟨hE, hA'⟩
      refine restSq_gt_of h N hlam ω hE.1 ?_
      have hpos : 0 < preSq h K ω := lt_trans (mul_pos two_pos hlam) hA'
      have hlt : ENNReal.ofReal (2*lam) < ENNReal.ofReal (preSq h K ω) :=
        (ENNReal.ofReal_lt_ofReal_iff hpos).mpr hA'
      refine lt_of_lt_of_le hlt ?_
      show ENNReal.ofReal (preSq h K ω) ≤ Ssq h ω
      exact le_iSup (fun N => ENNReal.ofReal (preSq h N ω)) K
    have h1 : ENNReal.ofReal lam * μ s
        ≤ ∫⁻ ω in s, restSq h N ω ∂μ := by
      conv_lhs => rw [← Measure.restrict_apply_univ (μ := μ) (s := s), ← lintegral_const]
      exact lintegral_mono_ae (by
        rw [ae_restrict_iff' ((hEmeas N).inter hAmeas)]
        exact Filter.Eventually.of_forall (fun ω hω => (hpt ω hω).le))
    have h2 : ∫⁻ ω in s, restSq h N ω ∂μ
        ≤ ∫⁻ ω in Eset h lam N, restSq h N ω ∂μ :=
      lintegral_mono_set Set.inter_subset_left
    have h3 := integral_restSq_le ℱ h hmart hint lam N
    have hfac : ENNReal.ofReal lam⁻¹ * (ENNReal.ofReal lam * μ s) = μ s := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.mpr hlam0),
        inv_mul_cancel₀ hlam.ne', ENNReal.ofReal_one, one_mul]
    calc μ s
        ≤ ENNReal.ofReal lam⁻¹ * (ENNReal.ofReal lam * μ s) := le_of_eq hfac.symm
      _ ≤ ENNReal.ofReal lam⁻¹ * ∫⁻ ω in s, restSq h N ω ∂μ := mul_le_mul_right h1 _
      _ ≤ ENNReal.ofReal lam⁻¹ * ∫⁻ ω in Eset h lam N, restSq h N ω ∂μ := mul_le_mul_right h2 _
      _ ≤ ENNReal.ofReal lam⁻¹ * (5 * ∫⁻ ω in Eset h lam N, (mstar h ω)^2 ∂μ) :=
          mul_le_mul_right h3 _
      _ = 5 * ENNReal.ofReal lam⁻¹ * ∫⁻ ω in Eset h lam N, (mstar h ω)^2 ∂μ := by ring
  have h1 : μ {ω : Ω | 2*lam < preSq h K ω}
      ≤ ∑ N ∈ Finset.range K, μ (Eset h lam N ∩ {ω : Ω | 2*lam < preSq h K ω}) := by
    conv_lhs => rw [hAeq]
    exact le_of_eq (measure_biUnion_finset hdisjA hmeasA)
  calc μ {ω : Ω | 2*lam < preSq h K ω}
      ≤ ∑ N ∈ Finset.range K, μ (Eset h lam N ∩ {ω : Ω | 2*lam < preSq h K ω}) := h1
    _ ≤ ∑ N ∈ Finset.range K,
          5 * ENNReal.ofReal lam⁻¹ * ∫⁻ ω in Eset h lam N, (mstar h ω)^2 ∂μ :=
        Finset.sum_le_sum hper
    _ = 5 * ENNReal.ofReal lam⁻¹ *
          ∑ N ∈ Finset.range K, ∫⁻ ω in Eset h lam N, (mstar h ω)^2 ∂μ := by
        rw [Finset.mul_sum]
    _ = 5 * ENNReal.ofReal lam⁻¹ *
          ∫⁻ ω in {ω : Ω | lam < preSq h K ω}, (mstar h ω)^2 ∂μ := by
        congr 1
        rw [← iUnion_Eset_eq hlam0 K]
        exact (lintegral_biUnion_finset hdisjE (fun N _ => hEmeas N)
          (fun ω => (mstar h ω)^2)).symm

end KeyIneq

section BDG

/-- `∫⁻_{t ∈ (0,X)} ofReal (t^s) = ofReal (X^{s+1}/(s+1))` for `s > -1` and `X ≥ 0`. -/
lemma lintegral_Ioo_rpow (X s : ℝ) (hX : 0 ≤ X) (hs : -1 < s) :
    ∫⁻ t in Set.Ioo 0 X, ENNReal.ofReal (t ^ s) = ENNReal.ofReal (X ^ (s + 1) / (s + 1)) := by
  rw [Measure.restrict_congr_set (μ := volume) (MeasureTheory.Ioo_ae_eq_Ioc (a := 0) (b := X))]
  have hint : IntegrableOn (fun t : ℝ => t ^ s) (Set.Ioc 0 X) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hX).mp
      (intervalIntegral.intervalIntegrable_rpow' hs)
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioc 0 X)] (fun t : ℝ => t ^ s) := by
    filter_upwards [self_mem_ae_restrict (μ := (volume : Measure ℝ)) measurableSet_Ioc] with t ht
    exact Real.rpow_nonneg (le_of_lt ht.1) s
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
  congr 1
  rw [← intervalIntegral.integral_of_le hX, integral_rpow (Or.inl hs),
    Real.zero_rpow (by linarith : s + 1 ≠ 0)]
  ring

/-- Bootstrap lemma: `A ≤ c * D * A^(1-1/q)` with `0 < A < ∞` and `1 < q` gives `A^(1/q) ≤ c * D`. -/
lemma rpow_bootstrap {A c D : ℝ≥0∞} {q : ℝ}
    (hA0 : A ≠ 0) (hAtop : A ≠ ⊤) (h : A ≤ c * D * A ^ (1 - 1/q)) :
    A ^ (1/q) ≤ c * D := by
  have hsplit : A ^ (1/q) * A ^ (1 - 1/q) = A := by
    rw [← ENNReal.rpow_add (1/q) (1 - 1/q) hA0 hAtop,
      show 1/q + (1 - 1/q) = 1 by ring, ENNReal.rpow_one]
  have hne : A ^ (1 - 1/q) ≠ 0 := by
    intro h0
    rcases ENNReal.rpow_eq_zero_iff.mp h0 with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact hA0 h1
    · exact hAtop h1
  have hne' : A ^ (1 - 1/q) ≠ ⊤ := ENNReal.rpow_ne_top_of_ne_zero hA0 hAtop
  have h2 : A ^ (1/q) * A ^ (1 - 1/q) ≤ c * D * A ^ (1 - 1/q) := by
    rw [hsplit]; exact h
  exact (ENNReal.mul_le_mul_iff_left hne hne').mp h2

/-- `t ↦ t^s` is Borel measurable. -/
lemma real_measurable_rpow_const (s : ℝ) : Measurable fun t : ℝ => t ^ s := by
  have h : Measurable fun t : ℝ => Complex.re (Complex.exp ((s:ℂ) * Complex.log (t:ℂ))) :=
    Complex.measurable_re.comp (Complex.measurable_exp.comp
      (measurable_const.mul (Complex.measurable_log.comp Complex.measurable_ofReal)))
  have hfun : (fun t : ℝ => t ^ s)
      = fun t : ℝ => if t = 0 then (0:ℝ)^s else Complex.re (Complex.exp ((s:ℂ)*Complex.log (t:ℂ))) := by
    funext t
    by_cases ht : t = 0
    · simp [ht]
    · simp only [if_neg ht]
      rw [Real.rpow_def, Complex.cpow_def, if_neg (by simpa using ht), mul_comm]
  rw [hfun]
  exact Measurable.ite (measurableSet_singleton 0) measurable_const h

/-- `x ↦ x^s` is Borel measurable on `ℝ≥0∞`. -/
lemma ENNReal.measurable_rpow_const (s : ℝ) : Measurable fun x : ℝ≥0∞ => x ^ s := by
  have htr : Measurable fun x : ℝ≥0∞ => x.toReal := Measurable.ennreal_toReal measurable_id
  have hbase : Measurable fun x : ℝ≥0∞ => ENNReal.ofReal (x.toReal ^ s) := by
    have h1 : Measurable (fun x : ℝ≥0∞ => x.toReal ^ s) :=
      Measurable.comp (g := fun t : ℝ => t ^ s) (f := fun x : ℝ≥0∞ => x.toReal)
        (real_measurable_rpow_const s) htr
    exact Measurable.ennreal_ofReal h1
  have hfun : (fun x : ℝ≥0∞ => x ^ s)
      = fun x => if x = ⊤ then ⊤ ^ s else if x = 0 then (0:ℝ≥0∞)^s
          else ENNReal.ofReal (x.toReal ^ s) := by
    funext x
    by_cases h1 : x = ⊤
    · simp [h1]
    by_cases h2 : x = 0
    · simp [h2]
    · simp only [h1, h2, if_false]
      rw [← ENNReal.ofReal_toReal (ENNReal.rpow_ne_top_of_ne_zero h2 h1), ENNReal.toReal_rpow]
  rw [hfun]
  exact Measurable.ite (measurableSet_singleton ⊤) measurable_const
    (Measurable.ite (measurableSet_singleton 0) measurable_const hbase)

/-- `∫⁻_{t>0} (if t/2 < Z ω then t^s else 0) = (2 Z ω)^{s+1}/(s+1)` (for `Z ≥ 0`). -/
lemma inner_eval_rpow (Z : Ω → ℝ) (hZnn : ∀ ω, 0 ≤ Z ω) {s : ℝ} (hs : -1 < s) (ω : Ω) :
    (∫⁻ t in Set.Ioi (0:ℝ), (if t/2 < Z ω then ENNReal.ofReal (t ^ s) else 0))
      = ENNReal.ofReal ((2 * Z ω) ^ (s + 1) / (s + 1)) := by
  have hZω : 0 ≤ Z ω := hZnn ω
  rw [← lintegral_indicator (measurableSet_Ioi : MeasurableSet (Set.Ioi (0:ℝ)))]
  have hfun : (Set.Ioi (0:ℝ)).indicator
        (fun t => if t/2 < Z ω then ENNReal.ofReal (t ^ s) else 0)
      = (Set.Ioo 0 (2 * Z ω)).indicator (fun t => ENNReal.ofReal (t ^ s)) := by
    funext t
    by_cases ht : t ∈ Set.Ioo (0:ℝ) (2 * Z ω)
    · rw [Set.indicator_of_mem (s := Set.Ioi (0:ℝ)) ht.1,
        Set.indicator_of_mem (s := Set.Ioo 0 (2 * Z ω)) ht, if_pos (by linarith [ht.2])]
    · rw [Set.indicator_of_notMem (s := Set.Ioo 0 (2 * Z ω)) ht]
      by_cases ht0 : t ∈ Set.Ioi (0:ℝ)
      · rw [Set.indicator_of_mem (s := Set.Ioi (0:ℝ)) ht0,
          if_neg (fun h => ht ⟨ht0, by linarith⟩)]
      · rw [Set.indicator_of_notMem (s := Set.Ioi (0:ℝ)) ht0]
  rw [hfun, lintegral_indicator measurableSet_Ioo]
  exact lintegral_Ioo_rpow (2 * Z ω) s (by linarith) hs

/-- Tonelli step for the BDG bootstrap:
`∫⁻_{t>0} t^s ∫⁻_{ω : t/2 < Z ω} W = ∫⁻_ω W ω * (2 Z ω)^{s+1}/(s+1)`. -/
lemma tonelli_step (Z : Ω → ℝ) (W : Ω → ℝ≥0∞) (hZ : Measurable Z) (hW : Measurable W)
    (hZnn : ∀ ω, 0 ≤ Z ω) {s : ℝ} (hs : -1 < s) :
    (∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (t ^ s) * (∫⁻ ω in {ω | t/2 < Z ω}, W ω ∂μ))
      = ∫⁻ ω, W ω * ENNReal.ofReal ((2 * Z ω) ^ (s + 1) / (s + 1)) ∂μ := by
  classical
  have hGmeas : AEMeasurable
      (fun p : ℝ × Ω => ENNReal.ofReal (p.1 ^ s) * (if p.1/2 < Z p.2 then W p.2 else 0))
      ((volume.restrict (Set.Ioi 0)).prod μ) := by
    refine (Measurable.mul ?_ ?_).aemeasurable
    · exact (Measurable.ennreal_ofReal (real_measurable_rpow_const s)).comp measurable_fst
    · refine Measurable.ite ?_ ?_ ?_
      · exact measurableSet_lt (measurable_fst.div_const 2) (hZ.comp measurable_snd)
      · exact hW.comp measurable_snd
      · exact measurable_const
  have hstepA : (∫⁻ t in Set.Ioi (0:ℝ),
        ENNReal.ofReal (t ^ s) * (∫⁻ ω in {ω | t/2 < Z ω}, W ω ∂μ))
      = ∫⁻ t, ∫⁻ ω,
          ENNReal.ofReal (t ^ s) * (if t/2 < Z ω then W ω else 0) ∂μ
          ∂(volume.restrict (Set.Ioi 0)) := by
    refine lintegral_congr (fun t => ?_)
    have hsmeas : MeasurableSet {ω | t/2 < Z ω} :=
      measurableSet_lt (measurable_const (a := t/2)) hZ
    have hfun : (fun ω => ENNReal.ofReal (t ^ s) * (if t/2 < Z ω then W ω else 0))
        = fun ω => ENNReal.ofReal (t ^ s) * ({ω | t/2 < Z ω}).indicator W ω := by
      funext ω; rfl
    rw [hfun, lintegral_const_mul _ (hW.indicator hsmeas),
      lintegral_indicator hsmeas W]
  rw [hstepA, lintegral_lintegral_swap (μ := volume.restrict (Set.Ioi 0)) (ν := μ) hGmeas]
  have hinner : ∀ ω, (∫⁻ t in Set.Ioi (0:ℝ),
        ENNReal.ofReal (t ^ s) * (if t/2 < Z ω then W ω else 0))
      = W ω * ENNReal.ofReal ((2 * Z ω) ^ (s + 1) / (s + 1)) := by
    intro ω
    have hm : Measurable fun t : ℝ => if t/2 < Z ω then ENNReal.ofReal (t ^ s) else 0 :=
      Measurable.ite (measurableSet_lt (measurable_id.div_const 2) measurable_const)
        (Measurable.ennreal_ofReal (real_measurable_rpow_const s)) measurable_const
    have h1 : (∫⁻ t in Set.Ioi (0:ℝ),
          ENNReal.ofReal (t ^ s) * (if t/2 < Z ω then W ω else 0))
        = W ω * ∫⁻ t in Set.Ioi (0:ℝ),
            (if t/2 < Z ω then ENNReal.ofReal (t ^ s) else 0) := by
      rw [← lintegral_const_mul (W ω) hm]
      refine lintegral_congr (fun t => ?_)
      by_cases h : t/2 < Z ω <;> simp [h, mul_comm]
    rw [h1, inner_eval_rpow Z hZnn hs ω]
  exact lintegral_congr hinner

lemma bdg_preSq_le (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (h : ℕ → Ω → ℝ)
    (hmart : Martingale h ℱ μ) (hint : ∀ n, MemLp (h n) 2 μ)
    (p : ℝ) (hp : 2 < p)
    (hB : ∫⁻ ω, (mstar h ω)^p ∂μ ≠ ⊤) (K : ℕ) :
    ∫⁻ ω, (ENNReal.ofReal (preSq h K ω)) ^ (p/2) ∂μ
      ≤ ENNReal.ofReal ((p/2 * (10 * (2^(p/2-1) / (p/2-1))))^(p/2)) *
          ∫⁻ ω, (mstar h ω)^p ∂μ := by
  have hq0 : (0:ℝ) < p/2 := by linarith
  have hq1 : (1:ℝ) < p/2 := by linarith
  have hq1' : (0:ℝ) < p/2 - 1 := by linarith
  have hZ_meas : Measurable (preSq h K) :=
    (measurable_preSq ℱ h hmart K).mono (ℱ.le' K) le_rfl
  have hZnn : ∀ ω, 0 ≤ preSq h K ω := fun ω => Finset.sum_nonneg (fun n _ => sq_nonneg _)
  have hWmeas : Measurable (fun ω => (mstar h ω)^2) := by
    refine (Measurable.iSup ?_).pow_const 2
    intro n
    exact ENNReal.measurable_ofReal.comp
      ((hmart.1 n).measurable.mono (ℱ.le' n) le_rfl).norm
  have hWc_meas : Measurable (fun ω => ENNReal.ofReal 10 * (mstar h ω)^2) :=
    measurable_const.mul hWmeas
  set A := ∫⁻ ω, (ENNReal.ofReal (preSq h K ω)) ^ (p/2) ∂μ with hAdef
  -- Layer cake formula
  have hLC := lintegral_rpow_eq_lintegral_meas_lt_mul (μ := μ) (f := preSq h K)
    (Filter.Eventually.of_forall hZnn) hZ_meas.aemeasurable hq0
  have hA1 : A = ENNReal.ofReal (p/2) *
      ∫⁻ t in Set.Ioi (0:ℝ), μ {a | t < preSq h K a} * ENNReal.ofReal (t ^ (p/2 - 1)) := by
    rw [show A = ∫⁻ ω, ENNReal.ofReal ((preSq h K ω) ^ (p/2)) ∂μ from
      lintegral_congr (fun ω => ENNReal.ofReal_rpow_of_nonneg (hZnn ω) hq0.le)]
    exact hLC
  -- the good-lambda input
  have hkey : ∀ t ∈ Set.Ioi (0:ℝ),
      μ {a | t < preSq h K a}
        ≤ ENNReal.ofReal (10 * t⁻¹) *
            ∫⁻ ω in {ω | t/2 < preSq h K ω}, (mstar h ω)^2 ∂μ := by
    intro t ht
    have ht0 : 0 < t := ht
    have hh := key_ineq ℱ h hmart hint (lam := t/2) (by linarith) K
    rw [show (2:ℝ)*(t/2) = t by ring] at hh
    have hconst : ENNReal.ofReal (10 * t⁻¹) = 5 * ENNReal.ofReal ((t/2)⁻¹) := by
      rw [show (10:ℝ) * t⁻¹ = 5 * (t/2)⁻¹ by field_simp; ring,
        ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 5)]
      norm_num
    rw [← hconst] at hh
    exact hh
  have hstep3 : (∫⁻ t in Set.Ioi (0:ℝ),
        μ {a | t < preSq h K a} * ENNReal.ofReal (t ^ (p/2 - 1)))
      ≤ ∫⁻ t in Set.Ioi (0:ℝ),
          (ENNReal.ofReal (10 * t⁻¹) *
            ∫⁻ ω in {ω | t/2 < preSq h K ω}, (mstar h ω)^2 ∂μ)
          * ENNReal.ofReal (t ^ (p/2 - 1)) := by
    refine lintegral_mono_ae ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    exact Filter.Eventually.of_forall (fun t ht => mul_le_mul_left (hkey t ht) _)
  -- pointwise rewriting of the integrand
  have hstep4 : (∫⁻ t in Set.Ioi (0:ℝ),
          (ENNReal.ofReal (10 * t⁻¹) *
            ∫⁻ ω in {ω | t/2 < preSq h K ω}, (mstar h ω)^2 ∂μ)
          * ENNReal.ofReal (t ^ (p/2 - 1)))
      = ∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (t ^ (p/2 - 2)) *
          (∫⁻ ω in {ω | t/2 < preSq h K ω}, ENNReal.ofReal 10 * (mstar h ω)^2 ∂μ) := by
    refine setLIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    have ht0 : 0 < t := ht
    have harm : ENNReal.ofReal (10 * t⁻¹) * ENNReal.ofReal (t ^ (p/2 - 1))
        = ENNReal.ofReal 10 * ENNReal.ofReal (t ^ (p/2 - 2)) := by
      have h2 : t ^ (p/2 - 1) * t⁻¹ = t ^ (p/2 - 2) := by
        rw [← Real.rpow_neg_one t, ← Real.rpow_add ht0 (p/2-1) (-1),
          show p/2 - 1 + -1 = p/2 - 2 by ring]
      rw [← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 10 * t⁻¹),
        ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 10)]
      congr 1
      rw [show (10:ℝ) * t⁻¹ * t^(p/2-1) = 10 * (t^(p/2-1) * t⁻¹) by ring, h2]
    have hG' : ENNReal.ofReal 10 * (∫⁻ ω in {ω | t/2 < preSq h K ω}, (mstar h ω)^2 ∂μ)
        = ∫⁻ ω in {ω | t/2 < preSq h K ω}, ENNReal.ofReal 10 * (mstar h ω)^2 ∂μ :=
      (lintegral_const_mul (μ := μ.restrict {ω | t/2 < preSq h K ω})
        (ENNReal.ofReal 10) hWmeas).symm
    have key : (ENNReal.ofReal (10 * t⁻¹) *
            (∫⁻ ω in {ω | t/2 < preSq h K ω}, (mstar h ω)^2 ∂μ))
          * ENNReal.ofReal (t ^ (p/2 - 1))
        = ENNReal.ofReal (t ^ (p/2 - 2)) * (ENNReal.ofReal 10 *
            (∫⁻ ω in {ω | t/2 < preSq h K ω}, (mstar h ω)^2 ∂μ)) := by
      rw [show (ENNReal.ofReal (10 * t⁻¹) *
              (∫⁻ ω in {ω | t/2 < preSq h K ω}, (mstar h ω)^2 ∂μ))
            * ENNReal.ofReal (t ^ (p/2 - 1))
          = (∫⁻ ω in {ω | t/2 < preSq h K ω}, (mstar h ω)^2 ∂μ)
            * (ENNReal.ofReal (10 * t⁻¹) * ENNReal.ofReal (t ^ (p/2 - 1))) from by ring,
        harm]
      ring
    rw [key, hG']
  -- Tonelli
  have hstep5 : (∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (t ^ (p/2 - 2)) *
        (∫⁻ ω in {ω | t/2 < preSq h K ω}, ENNReal.ofReal 10 * (mstar h ω)^2 ∂μ))
      = ∫⁻ ω, (ENNReal.ofReal 10 * (mstar h ω)^2) *
          ENNReal.ofReal ((2 * preSq h K ω) ^ (p/2 - 1) / (p/2 - 1)) ∂μ :=
    (by
      have h := tonelli_step (μ := μ) (Z := preSq h K)
        (W := fun ω => ENNReal.ofReal 10 * (mstar h ω)^2)
        hZ_meas hWc_meas hZnn (s := p/2 - 2) (by linarith)
      simpa only [show p/2 - 2 + 1 = p/2 - 1 by ring] using h)
  have hWZ_meas : Measurable (fun ω => (mstar h ω)^2 *
      (ENNReal.ofReal (preSq h K ω)) ^ (p/2 - 1)) :=
    hWmeas.mul ((Measurable.ennreal_ofReal hZ_meas).pow_const _)
  have hconst2 : Measurable (fun ω => ENNReal.ofReal ((2 * preSq h K ω) ^ (p/2 - 1) / (p/2 - 1))) :=
    Measurable.ennreal_ofReal
      (((real_measurable_rpow_const (p/2 - 1)).comp (hZ_meas.const_mul 2)).div_const _)
  have hWZ2 : Measurable (fun ω => (mstar h ω)^2 *
      ENNReal.ofReal ((2 * preSq h K ω) ^ (p/2 - 1) / (p/2 - 1))) :=
    hWmeas.mul hconst2
  have hCeq : ∀ ω, ENNReal.ofReal ((2 * preSq h K ω)^(p/2-1)/(p/2-1))
      = ENNReal.ofReal (2^(p/2-1)/(p/2-1)) * (ENNReal.ofReal (preSq h K ω))^(p/2-1) := by
    intro ω
    have hZω := hZnn ω
    have h2Z : (0:ℝ) ≤ 2 * preSq h K ω := by positivity
    calc ENNReal.ofReal ((2 * preSq h K ω)^(p/2-1)/(p/2-1))
        = ENNReal.ofReal ((2 * preSq h K ω)^(p/2-1)) * ENNReal.ofReal ((p/2-1)⁻¹) :=
          ENNReal.ofReal_mul (Real.rpow_nonneg h2Z _)
      _ = (ENNReal.ofReal (2 * preSq h K ω))^(p/2-1) * (ENNReal.ofReal (p/2-1))⁻¹ := by
          rw [ENNReal.ofReal_rpow_of_nonneg h2Z (by linarith : (0:ℝ) ≤ p/2-1),
            ENNReal.ofReal_inv_of_pos hq1']
      _ = (ENNReal.ofReal 2 * ENNReal.ofReal (preSq h K ω))^(p/2-1)
            * (ENNReal.ofReal (p/2-1))⁻¹ := by
          rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
      _ = ((ENNReal.ofReal 2)^(p/2-1) * (ENNReal.ofReal (preSq h K ω))^(p/2-1))
            * (ENNReal.ofReal (p/2-1))⁻¹ := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by linarith : (0:ℝ) ≤ p/2-1)]
      _ = ENNReal.ofReal (2^(p/2-1)) * (ENNReal.ofReal (preSq h K ω))^(p/2-1)
            * (ENNReal.ofReal (p/2-1))⁻¹ := by
          rw [ENNReal.ofReal_rpow_of_nonneg (by norm_num : (0:ℝ) ≤ 2)
            (by linarith : (0:ℝ) ≤ p/2-1)]
      _ = ENNReal.ofReal (2^(p/2-1)/(p/2-1)) * (ENNReal.ofReal (preSq h K ω))^(p/2-1) := by
          rw [show ENNReal.ofReal (2^(p/2-1)) * (ENNReal.ofReal (preSq h K ω))^(p/2-1)
                * (ENNReal.ofReal (p/2-1))⁻¹
              = (ENNReal.ofReal (2^(p/2-1)) * (ENNReal.ofReal (p/2-1))⁻¹)
                * (ENNReal.ofReal (preSq h K ω))^(p/2-1) from by ring,
            ← ENNReal.ofReal_inv_of_pos hq1',
            ← ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) _)]
          rfl
  have hstepC : (∫⁻ ω, (mstar h ω)^2 *
        ENNReal.ofReal ((2 * preSq h K ω) ^ (p/2 - 1) / (p/2 - 1)) ∂μ)
      = ENNReal.ofReal (2^(p/2-1) / (p/2 - 1)) *
          ∫⁻ ω, (mstar h ω)^2 * (ENNReal.ofReal (preSq h K ω)) ^ (p/2 - 1) ∂μ := by
    rw [← lintegral_const_mul _ hWZ_meas]
    refine lintegral_congr (fun ω => ?_)
    rw [hCeq ω]
    ring
  have hstep6 : (∫⁻ ω, (ENNReal.ofReal 10 * (mstar h ω)^2) *
        ENNReal.ofReal ((2 * preSq h K ω) ^ (p/2 - 1) / (p/2 - 1)) ∂μ)
      = ENNReal.ofReal (10 * (2^(p/2-1) / (p/2 - 1))) *
          ∫⁻ ω, (mstar h ω)^2 * (ENNReal.ofReal (preSq h K ω)) ^ (p/2 - 1) ∂μ := by
    rw [show (∫⁻ ω, (ENNReal.ofReal 10 * (mstar h ω)^2) *
          ENNReal.ofReal ((2 * preSq h K ω) ^ (p/2 - 1) / (p/2 - 1)) ∂μ)
        = ∫⁻ ω, ENNReal.ofReal 10 * ((mstar h ω)^2 *
          ENNReal.ofReal ((2 * preSq h K ω) ^ (p/2 - 1) / (p/2 - 1))) ∂μ from
        lintegral_congr (fun ω => by ring)]
    rw [lintegral_const_mul _ hWZ2, hstepC,
      show ENNReal.ofReal 10 * (ENNReal.ofReal (2^(p/2-1) / (p/2-1)) *
          (∫⁻ ω, (mstar h ω)^2 * (ENNReal.ofReal (preSq h K ω))^(p/2-1) ∂μ))
        = (ENNReal.ofReal 10 * ENNReal.ofReal (2^(p/2-1) / (p/2-1))) *
          (∫⁻ ω, (mstar h ω)^2 * (ENNReal.ofReal (preSq h K ω))^(p/2-1) ∂μ) from by ring,
      ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 10)]
  -- H\"older
  have hholder : (∫⁻ ω, (mstar h ω)^2 * (ENNReal.ofReal (preSq h K ω)) ^ (p/2 - 1) ∂μ)
      ≤ (∫⁻ ω, (mstar h ω)^p ∂μ) ^ (2/p) * A ^ (1 - 2/p) := by
    have hpq : (p/2).HolderConjugate (p/2).conjExponent :=
      Real.HolderConjugate.conjExponent hq1
    have hZp : Measurable (fun ω => (ENNReal.ofReal (preSq h K ω)) ^ (p/2 - 1)) :=
      (ENNReal.measurable_rpow_const (p/2 - 1)).comp (Measurable.ennreal_ofReal hZ_meas)
    have h1 := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq hWmeas.aemeasurable hZp.aemeasurable
    have h2 : (∫⁻ ω, ((mstar h ω)^2) ^ (p/2) ∂μ) = ∫⁻ ω, (mstar h ω)^p ∂μ := by
      refine lintegral_congr (fun ω => ?_)
      rw [← ENNReal.rpow_natCast (mstar h ω) 2, ← ENNReal.rpow_mul,
        show (↑(2:ℕ) : ℝ) * (p/2) = p by push_cast; ring]
    have h3 : (∫⁻ ω, ((ENNReal.ofReal (preSq h K ω)) ^ (p/2 - 1)) ^ (p/2).conjExponent ∂μ)
        = A := by
      rw [hAdef]
      refine lintegral_congr (fun ω => ?_)
      have hexp : (p/2 - 1) * (p/2 / (p/2 - 1)) = p/2 :=
        mul_div_cancel₀ (p/2) (show p/2 - 1 ≠ 0 by linarith)
      rw [← ENNReal.rpow_mul, Real.conjExponent]
      try rw [hexp]
    have h4 : (1:ℝ) / (p/2) = 2/p := by field_simp; try ring
    have h5 : (1:ℝ) / (p/2).conjExponent = 1 - 2/p := by
      have hp2' : p - 2 ≠ 0 := by linarith
      have hq1'' : p/2 - 1 ≠ 0 := by linarith
      have hp0 : p ≠ 0 := by linarith
      have hce : (p/2).conjExponent = p/(p-2) := by
        rw [Real.conjExponent]
        field_simp
        try ring
      rw [hce, one_div, inv_div]
      field_simp
      try ring
    calc (∫⁻ ω, (mstar h ω)^2 * (ENNReal.ofReal (preSq h K ω)) ^ (p/2 - 1) ∂μ)
        ≤ (∫⁻ ω, ((mstar h ω)^2) ^ (p/2) ∂μ) ^ (1 / (p/2))
            * (∫⁻ ω, ((ENNReal.ofReal (preSq h K ω)) ^ (p/2 - 1)) ^ (p/2).conjExponent ∂μ)
                ^ (1 / (p/2).conjExponent) := h1
      _ = (∫⁻ ω, (mstar h ω)^p ∂μ) ^ (2/p) * A ^ (1 - 2/p) := by rw [h2, h3, h4, h5]
  -- combine
  have hmain : A ≤ ENNReal.ofReal (p/2) * ENNReal.ofReal (10 * (2^(p/2-1) / (p/2-1))) *
      (∫⁻ ω, (mstar h ω)^p ∂μ) ^ (2/p) * A ^ (1 - 2/p) := by
    conv_lhs => rw [hA1]
    calc ENNReal.ofReal (p/2) *
            ∫⁻ t in Set.Ioi (0:ℝ), μ {a | t < preSq h K a} * ENNReal.ofReal (t ^ (p/2 - 1))
        ≤ ENNReal.ofReal (p/2) * ∫⁻ t in Set.Ioi (0:ℝ),
            (ENNReal.ofReal (10 * t⁻¹) *
              ∫⁻ ω in {ω | t/2 < preSq h K ω}, (mstar h ω)^2 ∂μ)
            * ENNReal.ofReal (t ^ (p/2 - 1)) := mul_le_mul_right hstep3 _
      _ = ENNReal.ofReal (p/2) * (∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (t ^ (p/2 - 2)) *
              (∫⁻ ω in {ω | t/2 < preSq h K ω}, ENNReal.ofReal 10 * (mstar h ω)^2 ∂μ)) := by
            rw [hstep4]
      _ = ENNReal.ofReal (p/2) * (∫⁻ ω, (ENNReal.ofReal 10 * (mstar h ω)^2) *
              ENNReal.ofReal ((2 * preSq h K ω) ^ (p/2 - 1) / (p/2 - 1)) ∂μ) := by
            rw [hstep5]
      _ = ENNReal.ofReal (p/2) * (ENNReal.ofReal (10 * (2^(p/2-1) / (p/2 - 1))) *
              ∫⁻ ω, (mstar h ω)^2 * (ENNReal.ofReal (preSq h K ω)) ^ (p/2 - 1) ∂μ) := by
            rw [hstep6]
      _ ≤ ENNReal.ofReal (p/2) * (ENNReal.ofReal (10 * (2^(p/2-1) / (p/2 - 1))) *
              ((∫⁻ ω, (mstar h ω)^p ∂μ) ^ (2/p) * A ^ (1 - 2/p))) :=
            mul_le_mul_right (mul_le_mul_right hholder _) _
      _ = ENNReal.ofReal (p/2) * ENNReal.ofReal (10 * (2^(p/2-1) / (p/2-1))) *
              (∫⁻ ω, (mstar h ω)^p ∂μ) ^ (2/p) * A ^ (1 - 2/p) := by
            rw [show ENNReal.ofReal (p/2) * (ENNReal.ofReal (10 * (2^(p/2-1) / (p/2 - 1))) *
                  ((∫⁻ ω, (mstar h ω)^p ∂μ) ^ (2/p) * A ^ (1 - 2/p)))
                = ENNReal.ofReal (p/2) * ENNReal.ofReal (10 * (2^(p/2-1) / (p/2-1))) *
                  (∫⁻ ω, (mstar h ω)^p ∂μ) ^ (2/p) * A ^ (1 - 2/p) from by ring]
  -- bootstrap
  rcases eq_or_ne A 0 with hA0 | hA0
  · rw [hA0]
    exact bot_le
  · have hAtop : A ≠ ⊤ := by
      have hZbound : ∀ ω, ENNReal.ofReal (preSq h K ω) ≤ (4 * (K:ℝ≥0∞)) * (mstar h ω)^2 := by
        intro ω
        have hsum : ENNReal.ofReal (preSq h K ω)
            = ∑ n ∈ Finset.range K, ENNReal.ofReal ((dinc h n ω)^2) := by
          rw [preSq, ENNReal.ofReal_sum_of_nonneg (fun n _ => sq_nonneg _)]
        rw [hsum]
        calc ∑ n ∈ Finset.range K, ENNReal.ofReal ((dinc h n ω)^2)
            ≤ ∑ n ∈ Finset.range K, 4 * (mstar h ω)^2 :=
              Finset.sum_le_sum (fun n _ => pt_bound_d h n ω)
          _ = K * (4 * (mstar h ω)^2) := by rw [Finset.sum_const, Finset.card_range]; ring
          _ = (4 * (K:ℝ≥0∞)) * (mstar h ω)^2 := by ring
      have hbig : A ≤ (4 * (K:ℝ≥0∞)) ^ (p/2) * ∫⁻ ω, (mstar h ω)^p ∂μ := by
        rw [hAdef]
        calc ∫⁻ ω, (ENNReal.ofReal (preSq h K ω)) ^ (p/2) ∂μ
            ≤ ∫⁻ ω, ((4 * (K:ℝ≥0∞)) * (mstar h ω)^2) ^ (p/2) ∂μ :=
              lintegral_mono (fun ω => ENNReal.rpow_le_rpow (hZbound ω) hq0.le)
          _ = ∫⁻ ω, (4 * (K:ℝ≥0∞)) ^ (p/2) * ((mstar h ω)^2) ^ (p/2) ∂μ := by
              refine lintegral_congr (fun ω => ?_)
              rw [ENNReal.mul_rpow_of_nonneg _ _ hq0.le]
          _ = (4 * (K:ℝ≥0∞)) ^ (p/2) * ∫⁻ ω, ((mstar h ω)^2) ^ (p/2) ∂μ :=
              lintegral_const_mul _ (hWmeas.pow_const _)
          _ = (4 * (K:ℝ≥0∞)) ^ (p/2) * ∫⁻ ω, (mstar h ω)^p ∂μ := by
              congr 1
              refine lintegral_congr (fun ω => ?_)
              rw [← ENNReal.rpow_natCast (mstar h ω) 2, ← ENNReal.rpow_mul,
                show (↑(2:ℕ) : ℝ) * (p/2) = p by push_cast; ring]
      refine ne_top_of_le_ne_top ?_ hbig
      exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hq0.le
        (ENNReal.mul_ne_top (by norm_num) (by simp))) hB
    have hb := rpow_bootstrap (hA0 := hA0) (hAtop := hAtop) (q := p/2)
      (c := ENNReal.ofReal (p/2) * ENNReal.ofReal (10 * (2^(p/2-1) / (p/2-1))))
      (D := (∫⁻ ω, (mstar h ω)^p ∂μ) ^ (2/p)) (by
        rw [show (1:ℝ) - 1/(p/2) = 1 - 2/p by field_simp; try ring]
        exact hmain)
    have hb2 : A ^ (1 / (p/2)) = A ^ (2/p) := by
      rw [show (1:ℝ)/(p/2) = 2/p by field_simp; try ring]
    rw [hb2] at hb
    calc A = (A ^ (2/p)) ^ (p/2) := by
          rw [← ENNReal.rpow_mul,
            show (2/p * (p/2)) = 1 by field_simp; try ring, ENNReal.rpow_one]
      _ ≤ ((ENNReal.ofReal (p/2) * ENNReal.ofReal (10 * (2^(p/2-1) / (p/2-1)))) *
            (∫⁻ ω, (mstar h ω)^p ∂μ) ^ (2/p)) ^ (p/2) := ENNReal.rpow_le_rpow hb hq0.le
      _ = (ENNReal.ofReal (p/2) * ENNReal.ofReal (10 * (2^(p/2-1) / (p/2-1)))) ^ (p/2) *
            ((∫⁻ ω, (mstar h ω)^p ∂μ) ^ (2/p)) ^ (p/2) :=
          ENNReal.mul_rpow_of_nonneg _ _ hq0.le
      _ = (ENNReal.ofReal (p/2) * ENNReal.ofReal (10 * (2^(p/2-1) / (p/2-1)))) ^ (p/2) *
            ∫⁻ ω, (mstar h ω)^p ∂μ := by
          congr 1
          rw [← ENNReal.rpow_mul,
            show (2/p * (p/2)) = 1 by field_simp; try ring, ENNReal.rpow_one]
      _ = ENNReal.ofReal ((p/2 * (10 * (2^(p/2-1) / (p/2-1)))) ^ (p/2)) *
            ∫⁻ ω, (mstar h ω)^p ∂μ := by
          congr 1
          rw [← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ p/2),
            ENNReal.ofReal_rpow_of_nonneg (by positivity) hq0.le]

/-- `(⨆ i, f i)^s = ⨆ i, (f i)^s` for `s > 0` in `ℝ≥0∞`. -/
lemma ENNReal.iSup_rpow {ι : Sort*} (f : ι → ℝ≥0∞) (s : ℝ) (hs : 0 < s) :
    (⨆ i, f i) ^ s = ⨆ i, (f i) ^ s := by
  apply le_antisymm
  · have hX : (⨆ i, (f i) ^ s) = ((⨆ i, (f i) ^ s) ^ s⁻¹) ^ s :=
      (ENNReal.rpow_inv_rpow (x := ⨆ i, (f i) ^ s) hs.ne').symm
    rw [hX, ENNReal.rpow_le_rpow_iff hs]
    refine iSup_le (fun i => ?_)
    calc f i = (f i) ^ (s * s⁻¹) := by
          rw [show s * s⁻¹ = 1 by field_simp, ENNReal.rpow_one]
      _ = ((f i) ^ s) ^ s⁻¹ := ENNReal.rpow_mul _ _ _
      _ ≤ (⨆ j, (f j) ^ s) ^ s⁻¹ :=
          ENNReal.rpow_le_rpow (le_iSup (fun j => (f j) ^ s) i) (by positivity)
  · exact iSup_le (fun i => ENNReal.rpow_le_rpow (le_iSup f i) hs.le)

/-- BDG upper square-function bound for the full square function `Ssq`. -/
lemma bdg_Ssq_le (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (h : ℕ → Ω → ℝ)
    (hmart : Martingale h ℱ μ) (hint : ∀ n, MemLp (h n) 2 μ)
    (p : ℝ) (hp : 2 < p)
    (hB : ∫⁻ ω, (mstar h ω)^p ∂μ ≠ ⊤) :
    ∫⁻ ω, (Ssq h ω) ^ (p/2) ∂μ
      ≤ ENNReal.ofReal ((p/2 * (10 * (2^(p/2-1) / (p/2-1))))^(p/2)) *
          ∫⁻ ω, (mstar h ω)^p ∂μ := by
  have hq0 : (0:ℝ) < p/2 := by linarith
  have hZ_meas : ∀ K, Measurable (preSq h K) := fun K =>
    (measurable_preSq ℱ h hmart K).mono (ℱ.le' K) le_rfl
  have hmono : Monotone fun K : ℕ => fun ω => (ENNReal.ofReal (preSq h K ω)) ^ (p/2) := by
    intro a b hab ω
    exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal (preSq_mono h hab ω)) hq0.le
  have hmeas : ∀ K, Measurable fun ω => (ENNReal.ofReal (preSq h K ω)) ^ (p/2) := fun K =>
    (ENNReal.measurable_rpow_const (p/2)).comp (Measurable.ennreal_ofReal (hZ_meas K))
  rw [show (∫⁻ ω, (Ssq h ω) ^ (p/2) ∂μ)
      = ∫⁻ ω, (⨆ K : ℕ, (ENNReal.ofReal (preSq h K ω)) ^ (p/2)) ∂μ from
      lintegral_congr (fun ω =>
        ENNReal.iSup_rpow (fun K => ENNReal.ofReal (preSq h K ω)) (p/2) hq0)]
  rw [lintegral_iSup hmeas hmono]
  exact iSup_le (fun K => bdg_preSq_le ℱ h hmart hint p hp hB K)

/-- Doob's maximal inequality + the `L^p` contraction of conditional expectation:
the maximal function of the `condExp` martingale is controlled in `L^p`, `p > 1`. -/
lemma mstar_condExp_lp_le (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (f : Ω → ℝ)
    {p : ℝ} (hp : 1 < p) (hf : MemLp f (ENNReal.ofReal p) μ) :
    ∫⁻ ω, (mstar (fun n => condExp (ℱ n) μ f) ω)^p ∂μ
      ≤ (ENNReal.ofReal (p/(p-1)))^p * ∫⁻ ω, (ENNReal.ofReal ‖f ω‖)^p ∂μ := by
  haveI : SigmaFiniteFiltration μ ℱ := ⟨fun _ => inferInstance⟩
  have hp0 : 0 < p := by linarith
  have hgp : ∀ n, MemLp (condExp (ℱ n) μ f) (ENNReal.ofReal p) μ := fun n =>
    MemLp.condExp (m := ℱ n) (μ := μ) (ENNReal.one_le_ofReal.mpr hp.le) hf
  have hfp : Integrable (fun ω => ‖f ω‖ ^ p) μ := by
    have h := hf.integrable_norm_rpow'
    rwa [ENNReal.toReal_ofReal hp0.le] at h
  have hf_nn : 0 ≤ᵐ[μ] (fun ω => ‖f ω‖ ^ p) :=
    Filter.Eventually.of_forall (fun ω => Real.rpow_nonneg (norm_nonneg _) p)
  have hmart : Martingale (fun n => condExp (ℱ n) μ f) ℱ μ := martingale_condExp f ℱ μ
  -- the `L^p` contraction of conditional expectation
  have hcontr : ∀ n, ∫⁻ ω, (ENNReal.ofReal ‖condExp (ℱ n) μ f ω‖)^p ∂μ
      ≤ ∫⁻ ω, (ENNReal.ofReal ‖f ω‖)^p ∂μ := by
    intro n
    have hJ := Integrable.norm_condExp_rpow_le (μ := μ) (m := ℱ n) (f := f) hp.le hfp
    have hcn : 0 ≤ᵐ[μ] condExp (ℱ n) μ (fun ω => ‖f ω‖ ^ p) :=
      condExp_nonneg hf_nn
    have h1 : ∫⁻ ω, ENNReal.ofReal (‖condExp (ℱ n) μ f ω‖^p) ∂μ
        ≤ ∫⁻ ω, ENNReal.ofReal (condExp (ℱ n) μ (fun ω => ‖f ω‖ ^ p) ω) ∂μ := by
      refine lintegral_mono_ae ?_
      filter_upwards [hJ] with ω hω
      exact ENNReal.ofReal_le_ofReal hω
    have h2 : ∫⁻ ω, ENNReal.ofReal (condExp (ℱ n) μ (fun ω => ‖f ω‖ ^ p) ω) ∂μ
        = ∫⁻ ω, ENNReal.ofReal (‖f ω‖^p) ∂μ := by
      rw [← ofReal_integral_eq_lintegral_ofReal (integrable_condExp (m := ℱ n)) hcn,
        integral_condExp (ℱ.le' n), ofReal_integral_eq_lintegral_ofReal hfp hf_nn]
    calc ∫⁻ ω, (ENNReal.ofReal ‖condExp (ℱ n) μ f ω‖)^p ∂μ
        = ∫⁻ ω, ENNReal.ofReal (‖condExp (ℱ n) μ f ω‖^p) ∂μ :=
          lintegral_congr (fun ω => ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp0.le)
      _ ≤ ∫⁻ ω, ENNReal.ofReal (‖f ω‖^p) ∂μ := h1.trans_eq h2
      _ = ∫⁻ ω, (ENNReal.ofReal ‖f ω‖)^p ∂μ :=
          (lintegral_congr (fun ω =>
            ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp0.le)).symm
  -- `|g|` is a submartingale
  have hsub : Submartingale (fun n ω => ‖condExp (ℱ n) μ f ω‖) ℱ μ := by
    refine ⟨fun n => (stronglyMeasurable_condExp (m := ℱ n)).norm, ?_, ?_⟩
    · intro i j hij
      filter_upwards [norm_condExp_le (μ := μ) (m := ℱ i) (condExp (ℱ j) μ f),
        hmart.condExp_ae_eq hij] with ω h1 h2
      calc ‖condExp (ℱ i) μ f ω‖ = ‖condExp (ℱ i) μ (condExp (ℱ j) μ f) ω‖ := by rw [h2]
        _ ≤ condExp (ℱ i) μ (fun ω => ‖condExp (ℱ j) μ f ω‖) ω := h1
    · intro n
      exact (hgp n).norm.integrable (ENNReal.one_le_ofReal.mpr hp.le)
  have hdoob := Commons.Probability.doob_lp_maximal (μ := μ) (𝒢 := ℱ) hsub
    (fun n ω => norm_nonneg _) hp (fun n => (hgp n).norm)
  have hstep : (⨆ n, ∫⁻ ω, (ENNReal.ofReal ‖condExp (ℱ n) μ f ω‖)^p ∂μ)
      ≤ ∫⁻ ω, (ENNReal.ofReal ‖f ω‖)^p ∂μ := iSup_le hcontr
  calc ∫⁻ ω, (mstar (fun n => condExp (ℱ n) μ f) ω)^p ∂μ
      = ∫⁻ ω, (⨆ n, ENNReal.ofReal ‖condExp (ℱ n) μ f ω‖)^p ∂μ := rfl
    _ ≤ (ENNReal.ofReal (p/(p-1)))^p *
          (⨆ n, ∫⁻ ω, (ENNReal.ofReal ‖condExp (ℱ n) μ f ω‖)^p ∂μ) := by
        simpa only [Real.enorm_eq_ofReal_abs, norm_norm,
          abs_of_nonneg (norm_nonneg _)] using hdoob
    _ ≤ (ENNReal.ofReal (p/(p-1)))^p * ∫⁻ ω, (ENNReal.ofReal ‖f ω‖)^p ∂μ :=
        mul_le_mul_right hstep _

/-- BDG upper square-function bound for the `condExp` martingale of an `L^p` function,
`p > 2`. -/
lemma bdg_condExp_lp_le (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (f : Ω → ℝ)
    {p : ℝ} (hp : 2 < p) (hf : MemLp f (ENNReal.ofReal p) μ) :
    ∫⁻ ω, (Ssq (fun n => condExp (ℱ n) μ f) ω) ^ (p/2) ∂μ
      ≤ ENNReal.ofReal ((p/2 * (10 * (2^(p/2-1) / (p/2-1))))^(p/2)) *
          ((ENNReal.ofReal (p/(p-1)))^p * ∫⁻ ω, (ENNReal.ofReal ‖f ω‖)^p ∂μ) := by
  have hp2 : (2:ℝ) < p := hp
  have hp1 : (1:ℝ) < p := by linarith
  have hp0 : (0:ℝ) < p := by linarith
  have hf2 : MemLp f 2 μ :=
    hf.mono_exponent (by
      simpa using ENNReal.ofReal_le_ofReal (by linarith : (2:ℝ) ≤ p))
  have hgp : ∀ n, MemLp (condExp (ℱ n) μ f) 2 μ := fun n =>
    MemLp.condExp (m := ℱ n) (μ := μ) one_le_two hf2
  have hfp : Integrable (fun ω => ‖f ω‖ ^ p) μ := by
    have h := hf.integrable_norm_rpow'
    rwa [ENNReal.toReal_ofReal hp0.le] at h
  have hId : ∫⁻ ω, (ENNReal.ofReal ‖f ω‖) ^ p ∂μ
      = ∫⁻ ω, ENNReal.ofReal (‖f ω‖ ^ p) ∂μ :=
    lintegral_congr (fun ω => ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp0.le)
  have hB : ∫⁻ ω, (mstar (fun n => condExp (ℱ n) μ f) ω)^p ∂μ ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (mstar_condExp_lp_le ℱ f hp1 hf)
    refine ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_ne_zero (by positivity) ENNReal.ofReal_ne_top) ?_
    rw [hId]
    exact hfp.lintegral_lt_top.ne
  have hmart : Martingale (fun n => condExp (ℱ n) μ f) ℱ μ := martingale_condExp f ℱ μ
  calc ∫⁻ ω, (Ssq (fun n => condExp (ℱ n) μ f) ω) ^ (p/2) ∂μ
      ≤ ENNReal.ofReal ((p/2 * (10 * (2^(p/2-1) / (p/2-1))))^(p/2)) *
          ∫⁻ ω, (mstar (fun n => condExp (ℱ n) μ f) ω)^p ∂μ :=
        bdg_Ssq_le ℱ _ hmart hgp p hp hB
    _ ≤ ENNReal.ofReal ((p/2 * (10 * (2^(p/2-1) / (p/2-1))))^(p/2)) *
          ((ENNReal.ofReal (p/(p-1)))^p * ∫⁻ ω, (ENNReal.ofReal ‖f ω‖)^p ∂μ) :=
        mul_le_mul_right (mstar_condExp_lp_le ℱ f hp1 hf) _

end BDG

section Pathwise

variable (x : ℕ → ℝ)

/-- The diameter of the range `x 0, …, x t`. -/
noncomputable def rng (t : ℕ) : ℝ :=
  ((Finset.range (t+1)).product (Finset.range (t+1))).sup'
    ⟨(0, 0), Finset.mem_product.mpr ⟨Finset.mem_range.mpr (Nat.succ_pos t),
      Finset.mem_range.mpr (Nat.succ_pos t)⟩⟩ (fun p : ℕ × ℕ => |x p.1 - x p.2|)

lemma le_rng {s s' t : ℕ} (hs : s ≤ t) (hs' : s' ≤ t) : |x s - x s'| ≤ rng x t :=
  Finset.le_sup' (s := (Finset.range (t+1)).product (Finset.range (t+1)))
    (b := (s, s')) (fun p : ℕ × ℕ => |x p.1 - x p.2|)
    (Finset.mem_product.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hs),
      Finset.mem_range.mpr (Nat.lt_succ_of_le hs')⟩)

lemma rng_nonneg (t : ℕ) : 0 ≤ rng x t :=
  (abs_nonneg _).trans (le_rng x (Nat.zero_le t) (Nat.zero_le t))

lemma rng_mono : Monotone (rng x) := by
  intro a b hab
  refine Finset.sup'_le _ _ (fun p hp => ?_)
  have h1 : p.1 ≤ b := by
    have := (Finset.mem_product.mp hp).1; simp only [Finset.mem_range] at this; omega
  have h2 : p.2 ≤ b := by
    have := (Finset.mem_product.mp hp).2; simp only [Finset.mem_range] at this; omega
  exact le_rng x h1 h2

/-- One step of Osekowski's sampling at scale `m`, capped at `N+1`. -/
noncomputable def tauStep (N m : ℕ) (τ : ℕ) : ℕ := by
  classical
  exact if h : ∃ t : ℕ, τ < t ∧ t ≤ N+1 ∧
      (1/2 : ℝ)^m * rng x t ≤ |x t - x τ|
    then Nat.find h else N+1

/-- Osekowski's sampling times at scale `m`. -/
noncomputable def tau (N m : ℕ) : ℕ → ℕ := fun j => (tauStep x N m)^[j] 0

lemma tau_succ (N m j : ℕ) : tau x N m (j+1) = tauStep x N m (tau x N m j) :=
  Function.iterate_succ_apply' _ _ _

lemma tauStep_le (N m : ℕ) (τ : ℕ) : tauStep x N m τ ≤ N+1 := by
  classical
  unfold tauStep
  by_cases h : ∃ t : ℕ, τ < t ∧ t ≤ N+1 ∧ (1/2 : ℝ)^m * rng x t ≤ |x t - x τ|
  · rw [dif_pos h]; try exact (Nat.find_spec h).2.1
  · rw [dif_neg h]

lemma tau_le (N m j : ℕ) : tau x N m j ≤ N+1 := by
  induction j with
  | zero => exact Nat.zero_le _
  | succ j ih => rw [tau_succ]; exact tauStep_le x N m _

lemma tauStep_lt (N m : ℕ) (τ : ℕ) (h : τ < N+1) : τ < tauStep x N m τ := by
  classical
  unfold tauStep
  by_cases hh : ∃ t : ℕ, τ < t ∧ t ≤ N+1 ∧ (1/2 : ℝ)^m * rng x t ≤ |x t - x τ|
  · rw [dif_pos hh]; exact (Nat.find_spec hh).1
  · rw [dif_neg hh]; exact h

lemma tau_lt_succ (N m j : ℕ) (h : tau x N m j < N+1) : tau x N m j < tau x N m (j+1) := by
  rw [tau_succ]; exact tauStep_lt x N m _ h

lemma tau_good (N m j : ℕ) (h : tau x N m (j+1) ≠ N+1) :
    (1/2 : ℝ)^m * rng x (tau x N m (j+1)) ≤ |x (tau x N m (j+1)) - x (tau x N m j)| := by
  classical
  rw [tau_succ] at h ⊢
  unfold tauStep at h ⊢
  by_cases hh : ∃ t, tau x N m j < t ∧ t ≤ N+1 ∧
      (1/2 : ℝ)^m * rng x t ≤ |x t - x (tau x N m j)|
  · rw [dif_pos hh] at h ⊢
    exact (Nat.find_spec hh).2.2
  · rw [dif_neg hh] at h
    exact absurd rfl h

/-- Between two consecutive sampling times the path never reaches the threshold. -/
lemma tau_not_good (N m j t : ℕ) (h1 : tau x N m j < t) (h2 : t < tau x N m (j+1)) :
    |x t - x (tau x N m j)| < (1/2 : ℝ)^m * rng x t := by
  classical
  have htN : t ≤ N+1 := le_of_lt (lt_of_lt_of_le h2 (tau_le x N m (j+1)))
  rw [tau_succ] at h2
  unfold tauStep at h2
  by_cases hP : ∃ t' : ℕ, tau x N m j < t' ∧ t' ≤ N+1 ∧
      (1/2 : ℝ)^m * rng x t' ≤ |x t' - x (tau x N m j)|
  · rw [dif_pos hP] at h2
    exact not_le.mp (fun hc => Nat.find_min hP h2 ⟨h1, htN, hc⟩)
  · rw [dif_neg hP] at h2
    by_contra hcon
    exact hP ⟨t, h1, htN, not_lt.mp hcon⟩

/-- If the sampling has stopped at the cap `N+1` then no time in `(tau j, N]` is good; in
particular (taking `j` with `tau j` the last sample before the end) nothing after `tau j` is
good at all. -/
lemma tau_no_good (N m j : ℕ) (h : tau x N m (j+1) = N+1) :
    ¬ ∃ t : ℕ, tau x N m j < t ∧ t ≤ N ∧
      (1/2 : ℝ)^m * rng x t ≤ |x t - x (tau x N m j)| := by
  rintro ⟨t, ht, htN, hc⟩
  have hP : ∃ t' : ℕ, tau x N m j < t' ∧ t' ≤ N+1 ∧
      (1/2 : ℝ)^m * rng x t' ≤ |x t' - x (tau x N m j)| := ⟨t, ht, by omega, hc⟩
  classical
  rw [tau_succ] at h
  unfold tauStep at h
  rw [dif_pos hP] at h
  have hmin : Nat.find hP ≤ t := Nat.find_min' hP ⟨ht, by omega, hc⟩
  omega

lemma tauStep_of_eq (N m j : ℕ) (h : tau x N m j = N+1) : tau x N m (j+1) = N+1 := by
  rw [tau_succ, h]
  classical
  unfold tauStep
  rw [dif_neg]
  rintro ⟨t, ht, htN, _⟩
  omega

/-- The diameter up to `t` is bounded by the diameter up to `c ≤ t` plus the part beyond. -/
lemma rng_split {c t : ℕ} (hct : c ≤ t) :
    rng x t ≤ max (rng x c)
      (max (2 * (Finset.Icc c t).sup' ⟨c, Finset.mem_Icc.mpr ⟨le_rfl, hct⟩⟩
              (fun s => |x c - x s|))
           (rng x c + (Finset.Icc c t).sup' ⟨c, Finset.mem_Icc.mpr ⟨le_rfl, hct⟩⟩
              (fun s => |x c - x s|))) := by
  set R := (Finset.Icc c t).sup' ⟨c, Finset.mem_Icc.mpr ⟨le_rfl, hct⟩⟩ (fun s => |x c - x s|)
    with hRdef
  have hR : ∀ s ∈ Finset.Icc c t, |x c - x s| ≤ R := fun s hs =>
    Finset.le_sup' (fun s => |x c - x s|) hs
  have hR' : ∀ s ∈ Finset.Icc c t, |x s - x c| ≤ R := fun s hs => by
    rw [abs_sub_comm]; exact hR s hs
  simp only [rng]
  refine Finset.sup'_le _ _ (fun p hp => ?_)
  have hp1 : p.1 ≤ t := by
    have := (Finset.mem_product.mp hp).1; simp only [Finset.mem_range] at this; omega
  have hp2 : p.2 ≤ t := by
    have := (Finset.mem_product.mp hp).2; simp only [Finset.mem_range] at this; omega
  rcases le_or_gt p.1 c with h1 | h1
  · rcases le_or_gt p.2 c with h2 | h2
    · exact le_trans (le_rng x h1 h2) (le_max_left _ _)
    · refine le_trans (abs_sub_le (x p.1) (x c) (x p.2)) ?_
      have hA : |x p.1 - x c| ≤ rng x c := le_rng x h1 le_rfl
      have hB : |x c - x p.2| ≤ R := hR p.2 (Finset.mem_Icc.mpr ⟨le_of_lt h2, hp2⟩)
      have hm : rng x c + R ≤ max (rng x c) (max (2 * R) (rng x c + R)) :=
        le_trans (le_max_right (2 * R) (rng x c + R))
          (le_max_right (rng x c) (max (2 * R) (rng x c + R)))
      calc |x p.1 - x c| + |x c - x p.2| ≤ rng x c + R := add_le_add hA hB
        _ ≤ _ := hm
  · rcases le_or_gt p.2 c with h2 | h2
    · refine le_trans (abs_sub_le (x p.1) (x c) (x p.2)) ?_
      have hA : |x p.1 - x c| ≤ R := hR' p.1 (Finset.mem_Icc.mpr ⟨le_of_lt h1, hp1⟩)
      have hB : |x c - x p.2| ≤ rng x c := le_rng x le_rfl h2
      have hm : rng x c + R ≤ max (rng x c) (max (2 * R) (rng x c + R)) :=
        le_trans (le_max_right (2 * R) (rng x c + R))
          (le_max_right (rng x c) (max (2 * R) (rng x c + R)))
      calc |x p.1 - x c| + |x c - x p.2| ≤ R + rng x c := add_le_add hA hB
        _ = rng x c + R := by ring
        _ ≤ _ := hm
    · refine le_trans (abs_sub_le (x p.1) (x c) (x p.2)) ?_
      have hA : |x p.1 - x c| ≤ R := hR' p.1 (Finset.mem_Icc.mpr ⟨le_of_lt h1, hp1⟩)
      have hB : |x c - x p.2| ≤ R := hR p.2 (Finset.mem_Icc.mpr ⟨le_of_lt h2, hp2⟩)
      have hm : 2 * R ≤ max (rng x c) (max (2 * R) (rng x c + R)) :=
        le_trans (le_max_left (2 * R) (rng x c + R))
          (le_max_right (rng x c) (max (2 * R) (rng x c + R)))
      calc |x p.1 - x c| + |x c - x p.2| ≤ R + R := add_le_add hA hB
        _ = 2 * R := by ring
        _ ≤ _ := hm

/-- At a sampling time the running range is at least half of the range at the next one. -/
lemma rng_half (N m j t : ℕ) (hm : 1 ≤ m) (hjt : tau x N m j ≤ t)
    (h2 : t < tau x N m (j+1)) : rng x t / 2 ≤ rng x (tau x N m j) := by
  by_contra hcon
  have hlt : rng x (tau x N m j) < rng x t / 2 := not_le.mp hcon
  have hne : (Finset.Icc (tau x N m j) t).Nonempty :=
    ⟨tau x N m j, Finset.mem_Icc.mpr ⟨le_rfl, hjt⟩⟩
  set R := (Finset.Icc (tau x N m j) t).sup' hne (fun s => |x (tau x N m j) - x s|)
    with hRdef
  have hRge : rng x t / 2 ≤ R := by
    have hsp := rng_split x hjt
    rw [← hRdef] at hsp
    rcases le_max_iff.mp hsp with h1 | h1
    · linarith [rng_nonneg x t, hlt]
    · rcases le_max_iff.mp h1 with h2' | h2'
      · linarith
      · linarith
  obtain ⟨s, hs, hsr⟩ := Finset.exists_mem_eq_sup' hne (fun s => |x (tau x N m j) - x s|)
  have hsI := Finset.mem_Icc.mp hs
  have hRt : 0 < rng x t / 2 := by linarith [rng_nonneg x (tau x N m j)]
  have hsj : tau x N m j < s := by
    rcases lt_or_eq_of_le hsI.1 with h | h
    · exact h
    · exfalso
      have hthis : |x (tau x N m j) - x s| = 0 := by rw [h, sub_self, abs_zero]
      have h0 : 0 < R := lt_of_lt_of_le hRt hRge
      linarith
  have hstt : s < tau x N m (j+1) := lt_of_le_of_lt hsI.2 h2
  have hng := tau_not_good x N m j s hsj hstt
  have hhalf : (1/2 : ℝ)^m ≤ 1/2 := by
    conv_lhs => rw [show m = (m-1) + 1 by omega]
    rw [pow_succ]
    have h1 : (1/2 : ℝ)^(m-1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    linarith
  have hbound : (1/2 : ℝ)^m * rng x s ≤ rng x t / 2 := by
    have hmono := rng_mono x hsI.2
    nlinarith [rng_nonneg x s, hhalf, hmono]
  have hRs : R = |x (tau x N m j) - x s| := hsr
  have hfinal : (1/2 : ℝ)^m * rng x s ≤ |x s - x (tau x N m j)| :=
    calc (1/2 : ℝ)^m * rng x s ≤ rng x t / 2 := hbound
      _ ≤ R := hRge
      _ = |x s - x (tau x N m j)| := by rw [hRs, abs_sub_comm]
  linarith [hng, hfinal]

lemma tau_ge (N m : ℕ) : ∀ j ≤ N+1, j ≤ tau x N m j := by
  intro j
  induction j with
  | zero => intro _; exact Nat.zero_le _
  | succ j ih =>
      intro hj
      have ihj := ih (by omega : j ≤ N+1)
      rcases eq_or_lt_of_le (tau_le x N m j) with heq | hlt
      · rw [tauStep_of_eq x N m j heq]
        omega
      · have hlt' : tau x N m j < tau x N m (j+1) := tau_lt_succ x N m j hlt
        omega

lemma tau_reaches (N m : ℕ) : tau x N m (N+1) = N+1 :=
  le_antisymm (tau_le x N m _) (tau_ge x N m _ le_rfl)

/-- `j` index of the last sampling time `≤ t` (for `t ≤ N`). -/
lemma exists_tau_last (N m t : ℕ) (ht : t ≤ N) :
    ∃ j, tau x N m j ≤ t ∧ t < tau x N m (j+1) := by
  classical
  have hex : ∃ k, t < tau x N m k := ⟨N+1, by rw [tau_reaches]; omega⟩
  have hpos : 0 < Nat.find hex := by
    by_contra h0
    have h0' : Nat.find hex = 0 := by omega
    have hspec := Nat.find_spec hex
    rw [h0'] at hspec
    simp only [tau, Function.iterate_zero_apply] at hspec
    omega
  refine ⟨Nat.find hex - 1, ?_, ?_⟩
  · have hlt : Nat.find hex - 1 < Nat.find hex := by omega
    exact le_of_not_gt (Nat.find_min hex hlt)
  · have := Nat.find_spec hex
    rwa [Nat.sub_add_cancel (by omega : 1 ≤ Nat.find hex)]

lemma tau_mono (N m : ℕ) : Monotone (tau x N m) := by
  refine monotone_nat_of_le_succ (fun j => ?_)
  by_cases h : tau x N m j = N+1
  · rw [tauStep_of_eq x N m j h, h]
  · exact le_of_lt (tau_lt_succ x N m j (lt_of_le_of_ne (tau_le x N m j) h))

/-- The increment from the previous sampling time is at most the threshold. -/
lemma abs_sub_tau_le (N m j s : ℕ) (h1 : tau x N m j ≤ s) (h2 : s < tau x N m (j+1)) :
    |x s - x (tau x N m j)| ≤ (1/2 : ℝ)^m * rng x s := by
  rcases lt_or_eq_of_le h1 with h | h
  · exact le_of_lt (tau_not_good x N m j s h h2)
  · have hz : |x s - x (tau x N m j)| = 0 := by rw [← h, sub_self, abs_zero]
    rw [hz]
    exact mul_nonneg (by positivity) (rng_nonneg x s)

/-- **Osekowski's comparable-jump lemma** (arXiv:1908.05937, Lemma 2.3) for the discrete
capped sampling: a jump of size `≈ 2^{-m} rng x t` is matched by a sampled increment of at
least an eighth of its size. -/
theorem tau_comparable (N m : ℕ) (hm : 2 ≤ m) {t' t : ℕ} (ht't : t' < t) (htN : t ≤ N)
    (hlo : 2 * ((1/2 : ℝ)^m * rng x t) < |x t' - x t|)
    (hhi : |x t' - x t| ≤ 4 * ((1/2 : ℝ)^m * rng x t)) :
    ∃ j : ℕ, 1 ≤ j ∧ t' < tau x N m j ∧ tau x N m j ≤ t ∧
      |x t' - x t| ≤ 8 * |x (tau x N m (j-1)) - x (tau x N m j)| := by
  classical
  obtain ⟨j, hjle, hjlt⟩ := exists_tau_last x N m t htN
  have hne : tau x N m j ≠ N+1 := by
    have := tau_le x N m j; omega
  have hstep1 : t' < tau x N m j := by
    by_contra hc
    have hle : tau x N m j ≤ t' := not_lt.mp hc
    have h1 := abs_sub_tau_le x N m j t' hle (lt_trans ht't hjlt)
    have h2 := abs_sub_tau_le x N m j t hjle hjlt
    rw [abs_sub_comm] at h2
    have h3 : rng x t' ≤ rng x t := rng_mono x (le_of_lt ht't)
    have h4 : (1/2 : ℝ)^m * rng x t' ≤ (1/2 : ℝ)^m * rng x t :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    have habs : |x t' - x t| ≤ |x t' - x (tau x N m j)| + |x (tau x N m j) - x t| :=
      abs_sub_le (x t') (x (tau x N m j)) (x t)
    linarith
  have hj1 : 1 ≤ j := by
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · rw [h0] at hstep1
      simp only [tau, Function.iterate_zero_apply] at hstep1
      omega
    · exact hpos
  have hhalf := rng_half x N m j t (by omega) hjle hjlt
  have hgood := tau_good x N m (j-1) (by
    rw [Nat.sub_add_cancel hj1]
    exact hne)
  rw [Nat.sub_add_cancel hj1] at hgood
  refine ⟨j, hj1, hstep1, hjle, ?_⟩
  have h4 : |x (tau x N m (j-1)) - x (tau x N m j)|
      = |x (tau x N m j) - x (tau x N m (j-1))| := abs_sub_comm _ _
  have hthis : |x t' - x t| ≤ 8 * ((1/2 : ℝ)^m * rng x (tau x N m j)) := by
    calc |x t' - x t| ≤ 4 * ((1/2 : ℝ)^m * rng x t) := hhi
      _ = 8 * ((1/2 : ℝ)^m * (rng x t / 2)) := by ring
      _ ≤ 8 * ((1/2 : ℝ)^m * rng x (tau x N m j)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hhalf (by positivity))
            (by norm_num)
  calc |x t' - x t| ≤ 8 * ((1/2 : ℝ)^m * rng x (tau x N m j)) := hthis
    _ ≤ 8 * |x (tau x N m (j-1)) - x (tau x N m j)| := by
        rw [h4]
        exact mul_le_mul_of_nonneg_left hgood (by norm_num)

/-- Every positive `D ≤ B` sits at a dyadic scale `2^{-m}`: there is `m ≥ 1` with
`2 * ((1/2)^m * B) < D ≤ 4 * ((1/2)^m * B)`. -/
lemma exists_dyadic_scale {B D : ℝ} (hD : 0 < D) (hDB : D ≤ B) :
    ∃ m : ℕ, 1 ≤ m ∧ 2 * ((1/2 : ℝ)^m * B) < D ∧ D ≤ 4 * ((1/2 : ℝ)^m * B) := by
  have hB : 0 < B := lt_of_lt_of_le hD hDB
  obtain ⟨m0, hm0⟩ := exists_pow_lt_of_lt_one (show (0:ℝ) < D / (2 * B) by positivity)
    (by norm_num : (1/2:ℝ) < 1)
  have hex : ∃ m : ℕ, 2 * ((1/2 : ℝ)^m * B) < D := by
    refine ⟨m0, ?_⟩
    rw [lt_div_iff₀ (by positivity : (0:ℝ) < 2*B)] at hm0
    linarith
  set m := Nat.find hex with hmdef
  have hm : 2 * ((1/2 : ℝ)^m * B) < D := Nat.find_spec hex
  have hm1 : 1 ≤ m := by
    by_contra h
    have h0 : m = 0 := by omega
    rw [h0] at hm
    simp at hm
    linarith
  refine ⟨m, hm1, hm, ?_⟩
  have hmin : ¬ (2 * ((1/2:ℝ)^(m-1) * B) < D) := Nat.find_min hex (by omega)
  have hpow : (1/2:ℝ)^(m-1) = 2 * (1/2:ℝ)^m := by
    conv_rhs => rw [show m = (m-1)+1 by omega, pow_succ]
    ring
  rw [hpow] at hmin
  push_neg at hmin
  linarith

/-- Two disjoint sampling windows contain no common time. -/
lemma Ioc_tau_disjoint (u : ℕ → ℕ) (hu : StrictMono u) {l₁ l₂ : ℕ} (h : l₁ < l₂)
    {s : ℕ} (h₁ : u l₁ < s ∧ s ≤ u (l₁+1)) (h₂ : u l₂ < s ∧ s ≤ u (l₂+1)) : False := by
  have h3 : u (l₁+1) ≤ u l₂ := hu.monotone (by omega)
  omega

/-- Past the cap the sampling is constant. -/
lemma tau_eq_cap (N m j : ℕ) (h : N+1 ≤ j) : tau x N m j = N+1 :=
  le_antisymm (tau_le x N m j) (by
    rw [← tau_reaches x N m]
    exact tau_mono x N m h)

/-- **Osekowski's pathwise domination** (arXiv:1908.05937, Lemma 2.4): every jump of the path
is matched by a sampled increment at a dyadic scale, and distinct jumps give distinct pairs
`(scale, index)`. -/
theorem ptw_domination (N : ℕ) {ρ r : ℝ} (hρ : 0 < ρ) (hρr : ρ < r)
    (u : ℕ → ℕ) (hu : StrictMono u) (J : ℕ) (huN : u J ≤ N) :
    ENNReal.ofReal (∑ l ∈ Finset.range J, |x (u l) - x (u (l+1))|^r)
      ≤ ENNReal.ofReal (8^ρ * (rng x N)^(r-ρ)) *
          ⨆ M : ℕ, ENNReal.ofReal
            (∑ m ∈ Finset.Icc 2 M, (1/2 : ℝ)^((m-2)*(r-ρ)) *
              ∑ j ∈ Finset.range (N+2), |x (tau x N m j) - x (tau x N m (j+1))|^ρ) := by
  classical
  set S := (Finset.range J).filter (fun l => |x (u l) - x (u (l+1))| ≠ 0) with hS
  have key_old : ∀ l ∈ S, ∃ q : ℕ × ℕ, 2 ≤ q.1 ∧ 1 ≤ q.2 ∧ u l < tau x N q.1 q.2 ∧
      tau x N q.1 q.2 ≤ u (l+1) ∧
      |x (u l) - x (u (l+1))| ≤ 8 * |x (tau x N q.1 (q.2-1)) - x (tau x N q.1 q.2)| ∧
      |x (u l) - x (u (l+1))| ≤ 4 * ((1/2:ℝ)^q.1 * rng x N) := by
    intro l hl
    obtain ⟨hlJ, hne⟩ := Finset.mem_filter.mp hl
    have hlJ' : l < J := Finset.mem_range.mp hlJ
    have hD : 0 < |x (u l) - x (u (l+1))| := by
      rw [abs_pos]
      exact abs_ne_zero.mp hne
    have hDB : |x (u l) - x (u (l+1))| ≤ rng x (u (l+1)) :=
      le_rng x (hu.monotone (Nat.le_succ l)) le_rfl
    obtain ⟨m, hm1, hlo, hhi⟩ := exists_dyadic_scale hD hDB
    have hm2 : 2 ≤ m := by
      by_contra hcon
      have hm1' : m = 1 := by omega
      rw [hm1'] at hlo
      simp only [pow_one] at hlo
      linarith
    obtain ⟨j, hj1, hjgt, hjle, hconc⟩ := tau_comparable x N m hm2 (hu (Nat.lt_succ_self l))
      (le_trans (hu.monotone (by omega : l + 1 ≤ J)) huN) hlo hhi
    exact ⟨(m, j), hm2, hj1, hjgt, hjle, hconc, by
      refine le_trans hhi (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left ?_ (by positivity)) (by norm_num))
      exact rng_mono x (le_trans (hu.monotone (by omega : l + 1 ≤ J)) huN)⟩
  have hkey : ∀ l : ℕ, ∃ q : ℕ × ℕ, l ∈ S → (2 ≤ q.1 ∧ 1 ≤ q.2 ∧ u l < tau x N q.1 q.2 ∧
      tau x N q.1 q.2 ≤ u (l+1) ∧
      |x (u l) - x (u (l+1))| ≤ 8 * |x (tau x N q.1 (q.2-1)) - x (tau x N q.1 q.2)| ∧
      |x (u l) - x (u (l+1))| ≤ 4 * ((1/2:ℝ)^q.1 * rng x N)) := by
    intro l
    by_cases hl : l ∈ S
    · obtain ⟨qq, hqq⟩ := key_old l hl
      exact ⟨qq, fun _ => hqq⟩
    · exact ⟨(2, 1), fun hc => absurd hc hl⟩
  choose q hq using hkey
  set Mbar := S.sup (fun l => (q l).1) with hMbar
  set F : ℕ → ℕ → ℝ := fun m j =>
    (1/2 : ℝ)^((m-2)*(r-ρ)) * |x (tau x N m j) - x (tau x N m (j+1))|^ρ with hF
  have hterm : ∀ l ∈ S,
      |x (u l) - x (u (l+1))|^r ≤ 8^ρ * (rng x N)^(r-ρ) * F (q l).1 ((q l).2 - 1) := by
    intro l hl
    obtain ⟨hlJ, hne⟩ := Finset.mem_filter.mp hl
    obtain ⟨hm2, hj1, hjgt, hjle, hconc, hhi4⟩ := hq l hl
    set m := (q l).1 with hm
    set j := (q l).2 with hj
    have hD : 0 < |x (u l) - x (u (l+1))| := by
      rw [abs_pos]
      exact abs_ne_zero.mp hne
    have hjs : j - 1 + 1 = j := Nat.sub_add_cancel hj1
    have hrp : (0:ℝ) < r - ρ := by linarith
    have hpow : (4:ℝ) * (1/2:ℝ)^m = (1/2:ℝ)^(m-2) := by
      have h1 : (1/2:ℝ)^m = (1/2:ℝ)^(m-2) * (1/2:ℝ)^2 := by
        rw [← pow_add, show m - 2 + 2 = m by omega]
      rw [h1, show ((1/2:ℝ))^2 = 1/4 by norm_num]
      ring
    have hcomb : (4 * (1/2:ℝ)^m)^(r-ρ) = (1/2:ℝ)^((m-2)*(r-ρ)) := by
      rw [hpow, ← Real.rpow_natCast (1/2:ℝ) (m-2),
        ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ (1/2:ℝ))]
      congr 1
      rw [Nat.cast_sub hm2]
      norm_num
      try ring
    have hsplit : (4 * ((1/2:ℝ)^m * rng x N))^(r-ρ)
        = (1/2:ℝ)^((m-2)*(r-ρ)) * (rng x N)^(r-ρ) := by
      rw [show (4:ℝ) * ((1/2:ℝ)^m * rng x N) = (4 * (1/2:ℝ)^m) * rng x N by ring,
        Real.mul_rpow (by positivity : (0:ℝ) ≤ 4 * (1/2:ℝ)^m) (rng_nonneg x N), hcomb]
    calc |x (u l) - x (u (l+1))|^r
        = |x (u l) - x (u (l+1))|^ρ * |x (u l) - x (u (l+1))|^(r-ρ) := by
          rw [← Real.rpow_add hD]; ring_nf
      _ ≤ |x (u l) - x (u (l+1))|^ρ * (4 * ((1/2:ℝ)^m * rng x N))^(r-ρ) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (abs_nonneg _) hhi4 hrp.le)
            (Real.rpow_nonneg (abs_nonneg _) _)
      _ ≤ (8^ρ * |x (tau x N m (j-1)) - x (tau x N m j)|^ρ) *
            (4 * ((1/2:ℝ)^m * rng x N))^(r-ρ) := by
          refine mul_le_mul_of_nonneg_right ?_
            (Real.rpow_nonneg (mul_nonneg (by norm_num)
              (mul_nonneg (by positivity) (rng_nonneg x N))) _)
          rw [← Real.mul_rpow (by norm_num : (0:ℝ) ≤ 8) (abs_nonneg _)]
          exact Real.rpow_le_rpow (abs_nonneg _) hconc hρ.le
      _ = 8^ρ * (rng x N)^(r-ρ) * F m (j-1) := by
          have hFval : F m (j-1)
              = (1/2:ℝ)^((m-2)*(r-ρ)) * |x (tau x N m (j-1)) - x (tau x N m j)|^ρ := by
            simp only [hF, hjs]
          rw [hsplit, hFval]
          ring
  have hinj : Set.InjOn q ↑S := by
    intro l₁ h₁ l₂ h₂ heq
    by_contra hne'
    obtain ⟨_, _, hgt₁, hle₁, _, _⟩ := hq l₁ h₁
    obtain ⟨_, _, hgt₂, hle₂, _, _⟩ := hq l₂ h₂
    rw [← heq] at hgt₂ hle₂
    rcases lt_or_gt_of_ne hne' with h | h
    · exact Ioc_tau_disjoint u hu h ⟨hgt₁, hle₁⟩ ⟨hgt₂, hle₂⟩
    · exact Ioc_tau_disjoint u hu h ⟨hgt₂, hle₂⟩ ⟨hgt₁, hle₁⟩
  have hj1S : ∀ l ∈ S, 1 ≤ (q l).2 := fun l hl => (hq l hl).2.1
  have hinj' : Set.InjOn (fun l => ((q l).1, (q l).2 - 1)) ↑S := by
    intro l₁ h₁ l₂ h₂ heq
    have h1 : (q l₁).1 = (q l₂).1 := (Prod.ext_iff.mp heq).1
    have h2 : (q l₁).2 - 1 = (q l₂).2 - 1 := (Prod.ext_iff.mp heq).2
    have h3 : (q l₁).2 = (q l₂).2 := by
      have := hj1S l₁ h₁
      have := hj1S l₂ h₂
      omega
    have hqeq : q l₁ = q l₂ := by
      ext <;> omega
    exact hinj h₁ h₂ hqeq
  have himage' : S.image (fun l => ((q l).1, (q l).2 - 1))
      ⊆ Finset.Icc 2 Mbar ×ˢ Finset.range (N+2) := by
    intro p hp
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hm2, hj1, hgt, hle, _, _⟩ := hq l hl
    refine Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hm2, ?_⟩, Finset.mem_range.mpr ?_⟩
    · exact Finset.le_sup (s := S) (f := fun l => (q l).1) hl
    · obtain ⟨hlJ₀, _⟩ := Finset.mem_filter.mp hl
      have hlJ' : l < J := Finset.mem_range.mp hlJ₀
      have h1 : u (l + 1) ≤ N := le_trans (hu.monotone (by omega)) huN
      have hcap : (q l).2 ≤ N+1 := by
        by_contra hcon
        push_neg at hcon
        rw [tau_eq_cap x N (q l).1 (q l).2 (le_of_lt hcon)] at hle
        omega
      have h2 : (q l).2 ≤ tau x N (q l).1 (q l).2 := tau_ge x N (q l).1 (q l).2 hcap
      omega
  have hsumJ : (∑ l ∈ Finset.range J, |x (u l) - x (u (l+1))|^r)
      = ∑ l ∈ S, |x (u l) - x (u (l+1))|^r := by
    rw [hS, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun l hl => ?_)
    by_cases hc : |x (u l) - x (u (l+1))| ≠ 0
    · rw [if_pos hc]
    · have h0 : |x (u l) - x (u (l+1))| = 0 := not_not.mp hc
      rw [if_neg hc, h0, Real.zero_rpow (by linarith : (r:ℝ) ≠ 0)]
  have hsum : (∑ l ∈ S, |x (u l) - x (u (l+1))|^r)
      ≤ 8^ρ * (rng x N)^(r-ρ) *
          (∑ m ∈ Finset.Icc 2 Mbar, (1/2 : ℝ)^((m-2)*(r-ρ)) *
            ∑ j ∈ Finset.range (N+2), |x (tau x N m j) - x (tau x N m (j+1))|^ρ) := by
    have h1 : (∑ l ∈ S, |x (u l) - x (u (l+1))|^r)
        ≤ ∑ l ∈ S, 8^ρ * (rng x N)^(r-ρ) * F (q l).1 ((q l).2 - 1) :=
      Finset.sum_le_sum hterm
    have h2 : (∑ l ∈ S, 8^ρ * (rng x N)^(r-ρ) * F (q l).1 ((q l).2 - 1))
        = 8^ρ * (rng x N)^(r-ρ) * ∑ l ∈ S, F (q l).1 ((q l).2 - 1) := by
      rw [Finset.mul_sum]
    have himg_eq : (∑ l ∈ S, F (q l).1 ((q l).2 - 1))
        = ∑ p ∈ S.image (fun l => ((q l).1, (q l).2 - 1)), F p.1 p.2 :=
      (Finset.sum_image (g := fun l => ((q l).1, (q l).2 - 1))
        (f := fun p : ℕ × ℕ => F p.1 p.2) hinj').symm
    have h3 : (∑ l ∈ S, F (q l).1 ((q l).2 - 1))
        ≤ ∑ p ∈ Finset.Icc 2 Mbar ×ˢ Finset.range (N+2), F p.1 p.2 := by
      rw [himg_eq]
      refine Finset.sum_le_sum_of_subset_of_nonneg himage' (fun p _ _ => ?_)
      simp only [hF]
      exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg (abs_nonneg _) _)
    have h4 : (∑ p ∈ Finset.Icc 2 Mbar ×ˢ Finset.range (N+2), F p.1 p.2)
        = ∑ m ∈ Finset.Icc 2 Mbar, ∑ j ∈ Finset.range (N+2), F m j := by
      rw [Finset.sum_product]
    have h5 : (∑ m ∈ Finset.Icc 2 Mbar, ∑ j ∈ Finset.range (N+2), F m j)
        = ∑ m ∈ Finset.Icc 2 Mbar, (1/2 : ℝ)^((m-2)*(r-ρ)) *
            ∑ j ∈ Finset.range (N+2), |x (tau x N m j) - x (tau x N m (j+1))|^ρ := by
      refine Finset.sum_congr rfl (fun m hm => ?_)
      have hFm : F m = fun j => (1/2 : ℝ)^((m-2)*(r-ρ)) *
          |x (tau x N m j) - x (tau x N m (j+1))|^ρ := rfl
      rw [hFm, Finset.mul_sum]
    calc (∑ l ∈ S, |x (u l) - x (u (l+1))|^r)
        ≤ 8^ρ * (rng x N)^(r-ρ) * ∑ l ∈ S, F (q l).1 ((q l).2 - 1) := h1.trans_eq h2
      _ ≤ 8^ρ * (rng x N)^(r-ρ) *
            ∑ p ∈ Finset.Icc 2 Mbar ×ˢ Finset.range (N+2), F p.1 p.2 :=
          mul_le_mul_of_nonneg_left h3 (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
            (Real.rpow_nonneg (rng_nonneg x N) _))
      _ = 8^ρ * (rng x N)^(r-ρ) *
            ∑ m ∈ Finset.Icc 2 Mbar, (1/2 : ℝ)^((m-2)*(r-ρ)) *
              ∑ j ∈ Finset.range (N+2), |x (tau x N m j) - x (tau x N m (j+1))|^ρ := by
          rw [h4, h5]
  rw [hsumJ]
  calc ENNReal.ofReal (∑ l ∈ S, |x (u l) - x (u (l+1))|^r)
      ≤ ENNReal.ofReal (8^ρ * (rng x N)^(r-ρ) *
          (∑ m ∈ Finset.Icc 2 Mbar, (1/2 : ℝ)^((m-2)*(r-ρ)) *
            ∑ j ∈ Finset.range (N+2), |x (tau x N m j) - x (tau x N m (j+1))|^ρ)) :=
        ENNReal.ofReal_le_ofReal hsum
    _ = ENNReal.ofReal (8^ρ * (rng x N)^(r-ρ)) *
          ENNReal.ofReal (∑ m ∈ Finset.Icc 2 Mbar, (1/2 : ℝ)^((m-2)*(r-ρ)) *
            ∑ j ∈ Finset.range (N+2), |x (tau x N m j) - x (tau x N m (j+1))|^ρ) :=
        ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
          (Real.rpow_nonneg (rng_nonneg x N) _))
    _ ≤ ENNReal.ofReal (8^ρ * (rng x N)^(r-ρ)) *
          ⨆ M : ℕ, ENNReal.ofReal
            (∑ m ∈ Finset.Icc 2 M, (1/2 : ℝ)^((m-2)*(r-ρ)) *
              ∑ j ∈ Finset.range (N+2), |x (tau x N m j) - x (tau x N m (j+1))|^ρ) :=
        mul_le_mul_of_nonneg_left
          (le_iSup (f := fun M : ℕ => ENNReal.ofReal
            (∑ m ∈ Finset.Icc (2:ℕ) M, (1/2 : ℝ)^((m-2)*(r-ρ)) *
              ∑ j ∈ Finset.range (N+2), |x (tau x N m j) - x (tau x N m (j+1))|^ρ)) Mbar)
          zero_le

end Pathwise


section StoppingTimes

set_option backward.isDefEq.respectTransparency false in
lemma measurable_rng_path (m : MeasurableSpace Ω) (ℱ : Filtration ℕ m) (g : ℕ → Ω → ℝ)
    (hg : ∀ n, Measurable[ℱ n] (g n)) (t : ℕ) :
    Measurable[ℱ t] (fun ω => rng (fun n => g n ω) t) := by
  letI : MeasurableSpace Ω := ℱ t
  have key : (fun ω => rng (fun n => g n ω) t)
      = ((Finset.range (t+1)).product (Finset.range (t+1))).sup'
          ⟨(0,0), Finset.mem_product.mpr ⟨Finset.mem_range.mpr (Nat.succ_pos t), Finset.mem_range.mpr (Nat.succ_pos t)⟩⟩
          (fun p : ℕ × ℕ => fun ω => |g p.1 ω - g p.2 ω|) := by
    funext ω
    exact (Finset.sup'_apply _ (fun p : ℕ × ℕ => fun ω => |g p.1 ω - g p.2 ω|) ω).symm
  rw [key]
  refine Finset.measurable_sup' _ (fun p hp => ?_)
  have h1 : p.1 ≤ t := by
    have := (Finset.mem_product.mp hp).1; simp only [Finset.mem_range] at this; omega
  have h2 : p.2 ≤ t := by
    have := (Finset.mem_product.mp hp).2; simp only [Finset.mem_range] at this; omega
  have hA : Measurable (fun ω => g p.1 ω - g p.2 ω) :=
    ((hg p.1).mono (ℱ.mono h1) le_rfl).sub ((hg p.2).mono (ℱ.mono h2) le_rfl)
  exact hA.abs

lemma measurableSet_lt_of_stoppingTime (m : MeasurableSpace Ω) (ℱ : Filtration ℕ m) {T : Ω → ℕ}
    (hT : ∀ n, MeasurableSet[ℱ n] {ω | T ω ≤ n}) {t n : ℕ} (ht : t ≤ n) :
    MeasurableSet[ℱ n] {ω | T ω < t} := by
  rcases Nat.eq_zero_or_pos t with h0 | hpos
  · subst h0
    have hz : {ω | T ω < 0} = (∅ : Set Ω) := by ext ω; simp
    rw [hz]
    exact @MeasurableSet.empty Ω (ℱ n)
  · have h1 : {ω | T ω < t} = {ω | T ω ≤ t - 1} := by
      ext ω
      show T ω < t ↔ T ω ≤ t - 1
      omega
    rw [h1]
    exact (ℱ.mono (by omega : t - 1 ≤ n)) _ (hT (t - 1))

set_option backward.isDefEq.respectTransparency false in
lemma measurableSet_eq_of_stoppingTime (m : MeasurableSpace Ω) (ℱ : Filtration ℕ m) {T : Ω → ℕ}
    (hT : ∀ n, MeasurableSet[ℱ n] {ω | T ω ≤ n}) {t n : ℕ} (ht : t ≤ n) :
    MeasurableSet[ℱ n] {ω | T ω = t} := by
  have h1 : {ω | T ω = t} = {ω | T ω ≤ t} ∩ {ω | T ω < t}ᶜ := by
    ext ω
    show T ω = t ↔ T ω ≤ t ∧ ¬ (T ω < t)
    omega
  rw [h1]
  exact ((ℱ.mono ht) _ (hT t)).inter (measurableSet_lt_of_stoppingTime m ℱ hT ht).compl

lemma tauStep_le_iff (x : ℕ → ℝ) (N m τ n : ℕ) (hn : n < N+1) :
    tauStep x N m τ ≤ n ↔ ∃ t, t ≤ n ∧ τ < t ∧ (1/2:ℝ)^m * rng x t ≤ |x t - x τ| := by
  classical
  unfold tauStep
  by_cases h : ∃ t, τ < t ∧ t ≤ N+1 ∧ (1/2:ℝ)^m * rng x t ≤ |x t - x τ|
  · rw [dif_pos h]
    constructor
    · intro hle
      exact ⟨Nat.find h, hle, (Nat.find_spec h).1, (Nat.find_spec h).2.2⟩
    · rintro ⟨t, ht, h1, h2⟩
      exact le_trans (Nat.find_le ⟨h1, le_trans ht (le_of_lt hn), h2⟩) ht
  · rw [dif_neg h]
    constructor
    · intro hle; omega
    · rintro ⟨t, ht, h1, h2⟩
      exact absurd ⟨t, h1, le_trans ht (le_of_lt hn), h2⟩ h

set_option backward.isDefEq.respectTransparency false in
lemma measurableSet_tauStep_le (m : MeasurableSpace Ω) (ℱ : Filtration ℕ m) (g : ℕ → Ω → ℝ)
    (hg : ∀ n, Measurable[ℱ n] (g n)) (N mm : ℕ) {T : Ω → ℕ}
    (hT : ∀ n, MeasurableSet[ℱ n] {ω | T ω ≤ n}) (n : ℕ) :
    MeasurableSet[ℱ n] {ω | tauStep (fun k => g k ω) N mm (T ω) ≤ n} := by
  letI : MeasurableSpace Ω := ℱ n
  by_cases hn : N + 1 ≤ n
  · have hu : {ω | tauStep (fun k => g k ω) N mm (T ω) ≤ n} = Set.univ := by
      ext ω
      exact iff_of_true (le_trans (tauStep_le _ N mm (T ω)) hn) trivial
    rw [hu]
    exact MeasurableSet.univ
  · push Not at hn
    have hiff : ∀ ω, (tauStep (fun k => g k ω) N mm (T ω) ≤ n ↔
        ∃ t ≤ n, T ω < t ∧ (1/2:ℝ)^mm * rng (fun k => g k ω) t ≤ |g t ω - g (T ω) ω|) :=
      fun ω => tauStep_le_iff (fun k => g k ω) N mm (T ω) n hn
    have hset : {ω | tauStep (fun k => g k ω) N mm (T ω) ≤ n}
        = ⋃ t : Fin (n+1), ({ω | T ω < t.val} ∩
            {ω | (1/2:ℝ)^mm * rng (fun k => g k ω) t.val ≤ |g t.val ω - g (T ω) ω|}) := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
      constructor
      · intro h
        obtain ⟨t, ht, h1, h2⟩ := (hiff ω).mp h
        exact ⟨⟨t, Nat.lt_succ_of_le ht⟩, h1, h2⟩
      · rintro ⟨t, h1, h2⟩
        exact (hiff ω).mpr ⟨t.val, Nat.lt_succ_iff.mp t.isLt, h1, h2⟩
    rw [hset]
    refine MeasurableSet.iUnion (fun t => ?_)
    have htn : t.val ≤ n := Nat.lt_succ_iff.mp t.isLt
    set F : ℕ → Ω → ℝ := fun s ω => if T ω = s then g s ω else 0 with hFs
    have hFmeas : ∀ s : ℕ, s ≤ n → Measurable[ℱ n] (F s) := by
      intro s hs
      have hs' : MeasurableSet[ℱ n] {ω | T ω = s} := measurableSet_eq_of_stoppingTime m ℱ hT hs
      have hgs : Measurable[ℱ n] (g s) := (hg s).mono (ℱ.mono hs) le_rfl
      have h := hgs.indicator hs'
      convert h using 1
      ext ω
      simp only [F, Set.indicator_apply, Set.mem_ofPred_eq]
    have hPhi : ∀ ω, T ω < t.val → (∑ s ∈ Finset.range t.val, F s ω) = g (T ω) ω := by
      intro ω hω
      rw [Finset.sum_eq_single (T ω)]
      · rw [hFs]; simp
      · intro b hb hne
        rw [hFs]
        simp only [if_neg (fun h : T ω = b => hne h.symm)]
      · intro hmem
        exact absurd (Finset.mem_range.mpr hω) hmem
    have hEq : {ω | T ω < t.val} ∩ {ω | (1/2:ℝ)^mm * rng (fun k => g k ω) t.val ≤
          |g t.val ω - g (T ω) ω|}
        = {ω | T ω < t.val} ∩ {ω | (1/2:ℝ)^mm * rng (fun k => g k ω) t.val ≤
            |g t.val ω - ∑ s ∈ Finset.range t.val, F s ω|} := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, by rwa [← hPhi ω h1] at h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, by rwa [hPhi ω h1] at h2⟩
    rw [hEq]
    refine MeasurableSet.inter (measurableSet_lt_of_stoppingTime m ℱ hT htn) ?_
    refine measurableSet_le ?_ ?_
    · exact ((measurable_rng_path m ℱ g hg t.val).mono (ℱ.mono htn) le_rfl).const_mul _
    · refine (((hg t.val).mono (ℱ.mono htn) le_rfl).sub ?_).abs
      exact Finset.measurable_sum _ (fun s hs => hFmeas s (by
        have := Finset.mem_range.mp hs; omega))

set_option backward.isDefEq.respectTransparency false in
lemma isStoppingTime_tau (m : MeasurableSpace Ω) (ℱ : Filtration ℕ m) (g : ℕ → Ω → ℝ)
    (hg : ∀ n, Measurable[ℱ n] (g n)) (N mm : ℕ) :
    ∀ j, IsStoppingTime ℱ (fun ω => ((tau (fun n => g n ω) N mm j : ℕ) : ℕ∞)) := by
  intro j
  induction j with
  | zero =>
    have hz : (fun ω => ((tau (fun n => g n ω) N mm 0 : ℕ) : ℕ∞)) = fun _ : Ω => (0 : ℕ∞) := by
      funext ω
      rfl
    rw [hz]
    exact isStoppingTime_const ℱ 0
  | succ j ih =>
    have hT : ∀ n, MeasurableSet[ℱ n] {ω | tau (fun k => g k ω) N mm j ≤ n} := by
      intro n
      simpa [ENat.coe_le_coe] using ih n
    intro n
    convert measurableSet_tauStep_le m ℱ g hg N mm hT n using 1
    ext ω
    show ((tau (fun k => g k ω) N mm (j+1) : ℕ) : ℕ∞) ≤ ((n:ℕ) : ℕ∞) ↔
      tauStep (fun k => g k ω) N mm (tau (fun k => g k ω) N mm j) ≤ n
    rw [tau_succ (fun k => g k ω) N mm j, ENat.coe_le_coe]


end StoppingTimes


section Sampled

noncomputable def tauR (g : ℕ → Ω → ℝ) (N mm j : ℕ) : Ω → ℕ :=
  fun ω => tau (fun k => g k ω) N mm j

noncomputable def sm (g : ℕ → Ω → ℝ) (N mm j : ℕ) : Ω → ℝ :=
  fun ω => g (tau (fun k => g k ω) N mm j) ω

lemma sm_eq_stoppedValue (g : ℕ → Ω → ℝ) (N mm j : ℕ) :
    sm g N mm j = stoppedValue g (fun ω => (tauR g N mm j ω : ℕ∞)) := by
  funext ω
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma isStoppingTime_tauR (m : MeasurableSpace Ω) (ℱ : Filtration ℕ m) (g : ℕ → Ω → ℝ)
    (hg : ∀ n, Measurable[ℱ n] (g n)) (N mm : ℕ) (j : ℕ) :
    IsStoppingTime ℱ (fun ω => (tauR g N mm j ω : ℕ∞)) :=
  isStoppingTime_tau m ℱ g hg N mm j

noncomputable def filt (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (g : ℕ → Ω → ℝ)
    (hg : ∀ n, Measurable[ℱ n] (g n)) (N mm : ℕ) : Filtration ℕ ‹MeasurableSpace Ω› where
  seq j := (isStoppingTime_tauR ‹MeasurableSpace Ω› ℱ g hg N mm j).measurableSpace
  mono' := by
    intro i j hij
    refine (isStoppingTime_tauR ‹MeasurableSpace Ω› ℱ g hg N mm i).measurableSpace_mono
      (isStoppingTime_tauR ‹MeasurableSpace Ω› ℱ g hg N mm j) ?_
    intro ω
    exact ENat.natCast_le_natCast.mpr (tau_mono (fun k => g k ω) N mm hij)
  le' j := (isStoppingTime_tauR ‹MeasurableSpace Ω› ℱ g hg N mm j).measurableSpace_le

set_option backward.isDefEq.respectTransparency false in
theorem martingale_sm (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (g : ℕ → Ω → ℝ)
    (hg : ∀ n, Measurable[ℱ n] (g n)) (hmart : Martingale g ℱ μ)
    (N mm : ℕ) :
    Martingale (sm g N mm) (filt ℱ g hg N mm) μ := by
  haveI : SigmaFiniteFiltration μ ℱ := ⟨fun _ => inferInstance⟩
  have hSA : StronglyAdapted ℱ g := fun n => (hg n).stronglyMeasurable
  have hprog : IsStronglyProgressive ℱ g := hSA.isStronglyProgressive_of_discrete
  refine ⟨fun j => ?_, fun i j hij => ?_⟩
  · rw [sm_eq_stoppedValue]
    exact (measurable_stoppedValue hprog
      (isStoppingTime_tauR ‹MeasurableSpace Ω› ℱ g hg N mm j)).stronglyMeasurable
  · rw [sm_eq_stoppedValue, sm_eq_stoppedValue]
    have hle : (fun ω => (tauR g N mm i ω : ℕ∞)) ≤ (fun ω => (tauR g N mm j ω : ℕ∞)) := by
      intro ω
      exact ENat.natCast_le_natCast.mpr (tau_mono (fun k => g k ω) N mm hij)
    have hbdd : ∀ ω, (tauR g N mm j ω : ℕ∞) ≤ ((N+1 : ℕ) : ℕ∞) := by
      intro ω
      exact ENat.natCast_le_natCast.mpr (tau_le (fun k => g k ω) N mm j)
    have h := hmart.stoppedValue_ae_eq_condExp_of_le (μ := μ)
      (isStoppingTime_tauR ‹MeasurableSpace Ω› ℱ g hg N mm j)
      (isStoppingTime_tauR ‹MeasurableSpace Ω› ℱ g hg N mm i) hle hbdd
    exact h.symm


section SampledBDG

lemma memLp_sm (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (g : ℕ → Ω → ℝ) (hgm : ∀ n, Measurable[ℱ n] (g n))
    (hg : ∀ n, MemLp (g n) 2 μ) (N mm j : ℕ) : MemLp (sm g N mm j) 2 μ := by
  have hSA : StronglyAdapted ℱ g := fun n => (hgm n).stronglyMeasurable
  have hprog : IsStronglyProgressive ℱ g := hSA.isStronglyProgressive_of_discrete
  have hmeas : Measurable (sm g N mm j) := by
    rw [sm_eq_stoppedValue]
    exact (measurable_stoppedValue hprog
      (isStoppingTime_tauR ‹MeasurableSpace Ω› ℱ g hgm N mm j)).mono
      (isStoppingTime_tauR ‹MeasurableSpace Ω› ℱ g hgm N mm j).measurableSpace_le le_rfl
  refine MemLp.of_le (g := fun ω => ∑ n ∈ Finset.range (N+2), |g n ω|) ?_ ?_ ?_
  · exact memLp_finsetSum _ (fun n _ => (hg n).norm)
  · exact hmeas.aestronglyMeasurable
  · filter_upwards with ω
    have hmem : tau (fun k => g k ω) N mm j ∈ Finset.range (N+2) :=
      Finset.mem_range.mpr (Nat.lt_succ_of_le (tau_le (fun k => g k ω) N mm j))
    have hsum : 0 ≤ ∑ n ∈ Finset.range (N+2), |g n ω| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
    have h1 : |sm g N mm j ω| = |g (tau (fun k => g k ω) N mm j) ω| := rfl
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hsum, h1]
    exact Finset.single_le_sum (f := fun n => |g n ω|) (fun i _ => abs_nonneg _) hmem

lemma mstar_sm_le (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (g : ℕ → Ω → ℝ) (N mm : ℕ) :
    mstar (sm g N mm) ≤ mstar g := by
  intro ω
  refine iSup_le (fun j => ?_)
  exact le_iSup (fun n : ℕ => ENNReal.ofReal ‖g n ω‖) (tau (fun k => g k ω) N mm j)

lemma lintegral_mstar_sm_le (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (f : Ω → ℝ) (N mm : ℕ)
    {s : ℝ} (hs1 : 1 < s)
    (hf : MemLp f (ENNReal.ofReal s) μ) :
    ∫⁻ ω, (mstar (sm (fun n => condExp (ℱ n) μ f) N mm) ω)^s ∂μ
      ≤ (ENNReal.ofReal (s/(s-1)))^s * ∫⁻ ω, (ENNReal.ofReal ‖f ω‖)^s ∂μ := by
  have h1 : ∫⁻ ω, (mstar (sm (fun n => condExp (ℱ n) μ f) N mm) ω)^s ∂μ
      ≤ ∫⁻ ω, (mstar (fun n => condExp (ℱ n) μ f) ω)^s ∂μ :=
    lintegral_mono (fun ω => ENNReal.rpow_le_rpow (mstar_sm_le ℱ _ N mm ω) (by positivity))
  exact h1.trans (mstar_condExp_lp_le ℱ f hs1 hf)

lemma hB_sm (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (f : Ω → ℝ) (N mm : ℕ) {s : ℝ}
    (hs0 : 0 < s) (hs1 : 1 < s) (hf : MemLp f (ENNReal.ofReal s) μ) :
    ∫⁻ ω, (mstar (sm (fun n => condExp (ℱ n) μ f) N mm) ω)^s ∂μ ≠ ⊤ := by
  have hfp : Integrable (fun ω => ‖f ω‖ ^ s) μ := by
    have h := hf.integrable_norm_rpow'
    rwa [ENNReal.toReal_ofReal hs0.le] at h
  have hId : ∫⁻ ω, (ENNReal.ofReal ‖f ω‖) ^ s ∂μ
      = ∫⁻ ω, ENNReal.ofReal (‖f ω‖ ^ s) ∂μ :=
    lintegral_congr (fun ω => ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hs0.le)
  refine ne_top_of_le_ne_top ?_ (lintegral_mstar_sm_le ℱ f N mm hs1 hf)
  refine ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_ne_zero (by positivity) ENNReal.ofReal_ne_top) ?_
  rw [hId]
  exact hfp.lintegral_lt_top.ne

noncomputable def bdgA (s : ℝ) : ℝ := s/2 * (10 * (2^(s/2-1) / (s/2-1)))
noncomputable def bdgB (s : ℝ) : ℝ := s/(s-1)
noncomputable def bdgXY (s : ℝ) : ℝ := (bdgA s)^(s/2) * (bdgB s)^s
noncomputable def bdgZZ (s : ℝ) : ℝ := bdgA s * (bdgB s)^2

lemma bdgA_nonneg {s : ℝ} (hs : 2 < s) : 0 ≤ bdgA s := by
  have h1 : 0 < s/2 - 1 := by linarith
  have h2 : (0:ℝ) < 2^(s/2-1) := Real.rpow_pos_of_pos (by norm_num) _
  have h3 : 0 < s/2 := by linarith
  have h4 : 0 ≤ s/2 * (10 * (2^(s/2-1) / (s/2-1))) := by
    exact mul_nonneg h3.le (mul_nonneg (by norm_num) (div_nonneg h2.le h1.le))
  simpa [bdgA] using h4

lemma bdgB_nonneg {s : ℝ} (hs : 2 < s) : 0 ≤ bdgB s := by
  have h1 : 0 < s - 1 := by linarith
  have h2 : 0 < s := by linarith
  have h4 : 0 ≤ s/(s-1) := div_nonneg h2.le h1.le
  simpa [bdgB] using h4

lemma bdgXY_nonneg {s : ℝ} (hs : 2 < s) : 0 ≤ bdgXY s :=
  mul_nonneg (Real.rpow_nonneg (bdgA_nonneg hs) _) (Real.rpow_nonneg (bdgB_nonneg hs) _)

lemma bdgZZ_nonneg {s : ℝ} (hs : 2 < s) : 0 ≤ bdgZZ s :=
  mul_nonneg (bdgA_nonneg hs) (sq_nonneg _)


set_option backward.isDefEq.respectTransparency false in
lemma measurable_sm_aux (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (g : ℕ → Ω → ℝ)
    (hgm : ∀ n, Measurable[ℱ n] (g n)) (N mm j : ℕ) : Measurable (sm g N mm j) := by
  have hSA : StronglyAdapted ℱ g := fun n => (hgm n).stronglyMeasurable
  have hprog : IsStronglyProgressive ℱ g := hSA.isStronglyProgressive_of_discrete
  rw [sm_eq_stoppedValue]
  exact (measurable_stoppedValue hprog
    (isStoppingTime_tauR ‹MeasurableSpace Ω› ℱ g hgm N mm j)).mono
    (isStoppingTime_tauR ‹MeasurableSpace Ω› ℱ g hgm N mm j).measurableSpace_le le_rfl

lemma measurable_preSq_sm (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (g : ℕ → Ω → ℝ)
    (hgm : ∀ n, Measurable[ℱ n] (g n)) (N m K : ℕ) : Measurable (preSq (sm g N m) K) := by
  refine Finset.measurable_sum _ (fun n hn => ?_)
  exact ((measurable_sm_aux ℱ g hgm N m (n+1)).sub
    (measurable_sm_aux ℱ g hgm N m n)).pow_const 2

lemma measurable_Ssq_sm (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (g : ℕ → Ω → ℝ)
    (hgm : ∀ n, Measurable[ℱ n] (g n)) (N m : ℕ) : Measurable (Ssq (sm g N m)) := by
  refine Measurable.iSup (fun K => ?_)
  exact (measurable_preSq_sm ℱ g hgm N m K).ennreal_ofReal

set_option backward.isDefEq.respectTransparency false in
lemma bdg_sm_sq (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (f : Ω → ℝ) {s : ℝ}
    (hs0 : 0 < s) (hs1 : 1 < s) (hs2 : 2 < s)
    (hf : MemLp f (ENNReal.ofReal s) μ) (N mm : ℕ) :
    eLpNorm (Ssq (sm (fun n => condExp (ℱ n) μ f) N mm)) (ENNReal.ofReal (s/2)) μ
      ≤ ENNReal.ofReal (bdgZZ s) * (eLpNorm f (ENNReal.ofReal s) μ)^2 := by
  haveI : SigmaFiniteFiltration μ ℱ := ⟨fun _ => inferInstance⟩
  have hf2 : MemLp f 2 μ := hf.mono_exponent (by
    simpa using ENNReal.ofReal_le_ofReal hs2.le)
  have hgm : ∀ n, Measurable[ℱ n] (condExp (ℱ n) μ f) :=
    fun n => (stronglyMeasurable_condExp (m := ℱ n)).measurable
  have hg2 : ∀ n, MemLp (condExp (ℱ n) μ f) 2 μ :=
    fun n => MemLp.condExp (m := ℱ n) (μ := μ) one_le_two hf2
  have hmart : Martingale (sm (fun n => condExp (ℱ n) μ f) N mm)
      (filt ℱ (fun n => condExp (ℱ n) μ f) hgm N mm) μ :=
    martingale_sm ℱ _ hgm (martingale_condExp f ℱ μ) N mm
  have hint : ∀ j, MemLp (sm (fun n => condExp (ℱ n) μ f) N mm j) 2 μ :=
    fun j => memLp_sm ℱ _ hgm hg2 N mm j
  have hB := hB_sm ℱ f N mm hs0 hs1 hf
  have hbdg := bdg_Ssq_le (filt ℱ (fun n => condExp (ℱ n) μ f) hgm N mm)
    (sm (fun n => condExp (ℱ n) μ f) N mm) hmart hint s hs2 hB
  have hmstar := lintegral_mstar_sm_le ℱ f N mm hs1 hf
  have hBnn : 0 ≤ bdgB s := bdgB_nonneg hs2
  have hsnn : (0:ℝ) ≤ s := le_of_lt hs0
  have hInt : ∫⁻ ω, (Ssq (sm (fun n => condExp (ℱ n) μ f) N mm) ω)^(s/2) ∂μ
      ≤ ENNReal.ofReal (bdgXY s) * ∫⁻ ω, (ENNReal.ofReal ‖f ω‖)^s ∂μ := by
    have h1 : ENNReal.ofReal ((s / 2 * (10 * (2 ^ (s / 2 - 1) / (s / 2 - 1)))) ^ (s / 2))
        = ENNReal.ofReal ((bdgA s)^(s/2)) := by rw [bdgA]
    rw [h1] at hbdg
    refine hbdg.trans ?_
    refine (mul_le_mul_of_nonneg_left hmstar bot_le).trans (le_of_eq ?_)
    rw [bdgXY, bdgB, ENNReal.ofReal_rpow_of_nonneg
      (div_nonneg hsnn (by linarith : (0:ℝ) ≤ s - 1)) hsnn]
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg (bdgA_nonneg hs2) _), mul_assoc]
  have hp0 : ENNReal.ofReal (s/2) ≠ 0 := by
    rw [ENNReal.ofReal_ne_zero_iff]; linarith
  have hpT : ENNReal.ofReal (s/2) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hp0' : ENNReal.ofReal s ≠ 0 := by
    rw [ENNReal.ofReal_ne_zero_iff]; linarith
  have hpT' : ENNReal.ofReal s ≠ ⊤ := ENNReal.ofReal_ne_top
  have hA : (eLpNorm (Ssq (sm (fun n => condExp (ℱ n) μ f) N mm))
        (ENNReal.ofReal (s/2)) μ)^(s/2)
      = ∫⁻ ω, (Ssq (sm (fun n => condExp (ℱ n) μ f) N mm) ω)^(s/2) ∂μ := by
    have key := Commons.Analysis.MeasureTheory.eLpNorm_rpow_toReal (μ := μ)
      (p := ENNReal.ofReal (s/2))
      (f := Ssq (sm (fun n => condExp (ℱ n) μ f) N mm)) hp0 hpT
      (measurable_Ssq_sm ℱ _ hgm N mm).aestronglyMeasurable
    simpa [ENNReal.toReal_ofReal (by linarith : (0:ℝ) ≤ s/2)] using key
  have hF : (eLpNorm f (ENNReal.ofReal s) μ)^s
      = ∫⁻ ω, (ENNReal.ofReal ‖f ω‖)^s ∂μ := by
    have key := Commons.Analysis.MeasureTheory.eLpNorm_rpow_toReal (μ := μ)
      (p := ENNReal.ofReal s) (f := f) hp0' hpT' hf.aestronglyMeasurable
    simpa [ENNReal.toReal_ofReal hs0.le, Real.enorm_eq_ofReal_abs, Real.norm_eq_abs] using key
  have hkey : (eLpNorm (Ssq (sm (fun n => condExp (ℱ n) μ f) N mm))
        (ENNReal.ofReal (s/2)) μ)^(s/2)
      ≤ ENNReal.ofReal (bdgXY s) * (eLpNorm f (ENNReal.ofReal s) μ)^s := by
    simpa [hA, hF] using hInt
  have hsa : 0 < 2/s := by positivity
  calc eLpNorm (Ssq (sm (fun n => condExp (ℱ n) μ f) N mm)) (ENNReal.ofReal (s/2)) μ
      = ((eLpNorm (Ssq (sm (fun n => condExp (ℱ n) μ f) N mm))
          (ENNReal.ofReal (s/2)) μ)^(s/2))^(2/s) := by
        rw [← ENNReal.rpow_mul]
        rw [show (s/2) * (2/s) = 1 by field_simp]
        rw [ENNReal.rpow_one]
    _ ≤ (ENNReal.ofReal (bdgXY s) * (eLpNorm f (ENNReal.ofReal s) μ)^s)^(2/s) :=
        ENNReal.rpow_le_rpow hkey hsa.le
    _ = (ENNReal.ofReal (bdgXY s))^(2/s) * ((eLpNorm f (ENNReal.ofReal s) μ)^s)^(2/s) :=
        ENNReal.mul_rpow_of_nonneg _ _ (le_of_lt hsa)
    _ = ENNReal.ofReal (bdgZZ s) * (eLpNorm f (ENNReal.ofReal s) μ)^2 := by
        have h1 : (ENNReal.ofReal (bdgXY s))^(2/s) = ENNReal.ofReal (bdgZZ s) := by
          rw [ENNReal.ofReal_rpow_of_nonneg (bdgXY_nonneg hs2) (le_of_lt hsa)]
          congr 1
          rw [bdgZZ, bdgXY,
            Real.mul_rpow (Real.rpow_nonneg (bdgA_nonneg hs2) _)
              (Real.rpow_nonneg (bdgB_nonneg hs2) _)]
          rw [← Real.rpow_mul (bdgA_nonneg hs2), ← Real.rpow_mul (bdgB_nonneg hs2)]
          rw [show s/2 * (2/s) = 1 by field_simp,
            show s * (2/s) = 2 by field_simp]
          rw [Real.rpow_one, Real.rpow_two]
        have h2 : ((eLpNorm f (ENNReal.ofReal s) μ)^s)^(2/s)
            = (eLpNorm f (ENNReal.ofReal s) μ)^2 := by
          rw [← ENNReal.rpow_mul]
          rw [show s * (2/s) = 2 by field_simp]
          rw [ENNReal.rpow_ofNat]
        rw [h1, h2]


end SampledBDG

end Sampled


section Variation

/-- The variation of the path `g · ω` restricted to subsequences lying in `[0,N]`. -/
noncomputable def Vtr (g : ℕ → Ω → ℝ) (s : ℝ) (N : ℕ) : Ω → ℝ≥0∞ :=
  fun ω => ⨆ (u : {u : ℕ → ℕ // StrictMono u}) (J : ℕ),
    if u.1 J ≤ N then
      ENNReal.ofReal ((∑ j ∈ Finset.range J, |g (u.1 (j+1)) ω - g (u.1 j) ω|^s) ^ (1/s))
    else 0

/-- The sampled square-function sum of the `m`-scale process, `m ≤ M`, at horizon `N`. -/
noncomputable def Zterm (g : ℕ → Ω → ℝ) (s : ℝ) (N M : ℕ) (ω : Ω) : ℝ :=
  ∑ m ∈ Finset.Icc 2 M, (1/2:ℝ)^((m-2)*(s-2)) *
    ∑ j ∈ Finset.range (N+2),
      |g (tau (fun k => g k ω) N m j) ω - g (tau (fun k => g k ω) N m (j+1)) ω|^(2:ℝ)

/-- The sampled square-function sum at horizon `N`. -/
noncomputable def Ztr (g : ℕ → Ω → ℝ) (s : ℝ) (N : ℕ) : Ω → ℝ≥0∞ :=
  fun ω => ⨆ (M : ℕ), ENNReal.ofReal (Zterm g s N M ω)

/-- The chain with `u 0 = a`, `u j = b + (j-1)` for `j ≥ 1`. -/
def twoChain (a b : ℕ) : ℕ → ℕ := fun j => if j = 0 then a else b + (j - 1)

lemma twoChain_zero (a b : ℕ) : twoChain a b 0 = a := rfl
lemma twoChain_one (a b : ℕ) : twoChain a b 1 = b := by simp [twoChain]

lemma twoChain_strictMono {a b : ℕ} (hab : a < b) : StrictMono (twoChain a b) := by
  intro i j hij
  have hi : i = 0 ∨ 1 ≤ i := by omega
  rcases hi with rfl | hi
  · rw [twoChain_zero]
    have hj0 : j ≠ 0 := by omega
    rw [twoChain, if_neg hj0]
    omega
  · have hjn : j ≠ 0 := by omega
    have hin : i ≠ 0 := by omega
    rw [twoChain, if_neg hin, twoChain, if_neg hjn]
    omega

/-- `ofReal` commutes with a finite supremum of nonnegative values. -/
lemma ofReal_sup'_eq {ι : Type*} (S : Finset ι) (hS : S.Nonempty) (f : ι → ℝ)
    (hf : ∀ i ∈ S, 0 ≤ f i) :
    ENNReal.ofReal (S.sup' hS f) = S.sup' hS (fun i => ENNReal.ofReal (f i)) := by
  obtain ⟨i₀, hi₀, hmax⟩ := Finset.exists_mem_eq_sup' hS f
  refine le_antisymm ?_ ?_
  · rw [hmax]
    exact Finset.le_sup' (s := S) (b := i₀) (fun i => ENNReal.ofReal (f i)) hi₀
  · refine Finset.sup'_le _ _ (fun i hi => ?_)
    exact ENNReal.ofReal_le_ofReal (Finset.le_sup' (s := S) (b := i) f hi)

lemma ofReal_rng_le_Vtr (g : ℕ → Ω → ℝ) {s : ℝ} (hs : 0 < s) (N : ℕ) (ω : Ω) :
    ENNReal.ofReal (rng (fun k => g k ω) N) ≤ Vtr g s N ω := by
  classical
  set x : ℕ → ℝ := fun k => g k ω with hx
  set S := (Finset.range (N+1)).product (Finset.range (N+1)) with hS
  have hSne : S.Nonempty :=
    ⟨(0,0), Finset.mem_product.mpr ⟨Finset.mem_range.mpr (Nat.succ_pos N),
      Finset.mem_range.mpr (Nat.succ_pos N)⟩⟩
  have key : ∀ p ∈ S, ENNReal.ofReal |x p.1 - x p.2| ≤ Vtr g s N ω := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
    simp only [Finset.mem_range] at hp1 hp2
    have hp1' : p.1 ≤ N := Nat.lt_succ_iff.mp hp1
    have hp2' : p.2 ≤ N := Nat.lt_succ_iff.mp hp2
    rcases lt_trichotomy p.1 p.2 with hlt | heq | hgt
    · have hstr : StrictMono (twoChain p.1 p.2) := twoChain_strictMono hlt
      have huJ : twoChain p.1 p.2 1 ≤ N := by rw [twoChain_one]; exact hp2'
      have hterm : ENNReal.ofReal
          ((∑ j ∈ Finset.range 1, |x (twoChain p.1 p.2 (j+1)) - x (twoChain p.1 p.2 j)|^s) ^ (1/s))
          = ENNReal.ofReal |x p.2 - x p.1| := by
        rw [Finset.sum_range_one, twoChain_one, twoChain_zero]
        congr 1
        rw [← Real.rpow_mul (abs_nonneg _), mul_one_div, div_self hs.ne', Real.rpow_one]
      have hle := le_iSup (fun u : {u : ℕ → ℕ // StrictMono u} =>
          ⨆ J : ℕ, if u.1 J ≤ N then
            ENNReal.ofReal ((∑ j ∈ Finset.range J,
              |x (u.1 (j+1)) - x (u.1 j)|^s) ^ (1/s)) else 0)
        ⟨twoChain p.1 p.2, hstr⟩
      have hle2 := le_iSup (fun J : ℕ => if (twoChain p.1 p.2) J ≤ N then
            ENNReal.ofReal ((∑ j ∈ Finset.range J,
              |x (twoChain p.1 p.2 (j+1)) - x (twoChain p.1 p.2 j)|^s) ^ (1/s)) else 0) 1
      rw [if_pos huJ] at hle2
      have : ENNReal.ofReal |x p.1 - x p.2| ≤ Vtr g s N ω := by
        have heq2 : ENNReal.ofReal |x p.1 - x p.2| = ENNReal.ofReal
            ((∑ j ∈ Finset.range 1, |x (twoChain p.1 p.2 (j+1)) - x (twoChain p.1 p.2 j)|^s) ^ (1/s)) := by
          rw [abs_sub_comm]; exact hterm.symm
        exact le_trans (le_of_eq heq2) (le_trans hle2 hle)
      exact this
    · rw [heq, sub_self, abs_zero, ENNReal.ofReal_zero]; exact zero_le
    · have hstr : StrictMono (twoChain p.2 p.1) := twoChain_strictMono hgt
      have huJ : twoChain p.2 p.1 1 ≤ N := by rw [twoChain_one]; exact hp1'
      have hterm : ENNReal.ofReal
          ((∑ j ∈ Finset.range 1, |x (twoChain p.2 p.1 (j+1)) - x (twoChain p.2 p.1 j)|^s) ^ (1/s))
          = ENNReal.ofReal |x p.1 - x p.2| := by
        rw [Finset.sum_range_one, twoChain_one, twoChain_zero]
        congr 1
        rw [← Real.rpow_mul (abs_nonneg _), mul_one_div, div_self hs.ne', Real.rpow_one]
      have hle := le_iSup (fun u : {u : ℕ → ℕ // StrictMono u} =>
          ⨆ J : ℕ, if u.1 J ≤ N then
            ENNReal.ofReal ((∑ j ∈ Finset.range J,
              |x (u.1 (j+1)) - x (u.1 j)|^s) ^ (1/s)) else 0)
        ⟨twoChain p.2 p.1, hstr⟩
      have hle2 := le_iSup (fun J : ℕ => if (twoChain p.2 p.1) J ≤ N then
            ENNReal.ofReal ((∑ j ∈ Finset.range J,
              |x (twoChain p.2 p.1 (j+1)) - x (twoChain p.2 p.1 j)|^s) ^ (1/s)) else 0) 1
      rw [if_pos huJ] at hle2
      exact le_trans (le_of_eq hterm.symm) (le_trans hle2 hle)
  calc ENNReal.ofReal (rng (fun k => g k ω) N)
      = ENNReal.ofReal (S.sup' hSne (fun p => |x p.1 - x p.2|)) := rfl
    _ = S.sup' hSne (fun p => ENNReal.ofReal |x p.1 - x p.2|) :=
        ofReal_sup'_eq S hSne _ (fun i _ => abs_nonneg _)
    _ ≤ Vtr g s N ω := Finset.sup'_le _ _ key

lemma ofReal_Zterm_le_Ztr (g : ℕ → Ω → ℝ) (s : ℝ) (N M : ℕ) (ω : Ω) :
    ENNReal.ofReal (Zterm g s N M ω) ≤ Ztr g s N ω :=
  le_iSup (fun M' : ℕ => ENNReal.ofReal (Zterm g s N M' ω)) M

lemma ofReal_rpow_rng_le (g : ℕ → Ω → ℝ) {s : ℝ} (hs2 : 2 < s) (N : ℕ) (ω : Ω) :
    ENNReal.ofReal (8 ^ (2:ℝ) * rng (fun k => g k ω) N ^ (s - 2))
      ≤ 64 * (ENNReal.ofReal (rng (fun k => g k ω) N)) ^ (s - 2) := by
  have hr : 0 ≤ rng (fun k => g k ω) N := rng_nonneg _ N
  have h8 : (8:ℝ) ^ (2:ℝ) = 64 := by
    rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]; norm_num
  rw [h8, ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 64),
    ENNReal.ofReal_rpow_of_nonneg hr (by linarith : (0:ℝ) ≤ s - 2)]
  norm_num

lemma Vtr_rpow_le (g : ℕ → Ω → ℝ) {s : ℝ} (hs0 : 0 < s) (hs2 : 2 < s) (N : ℕ) (ω : Ω) :
    (Vtr g s N ω)^s ≤ 64 * (ENNReal.ofReal (rng (fun k => g k ω) N))^(s - 2) * Ztr g s N ω := by
  classical
  set x : ℕ → ℝ := fun k => g k ω with hx
  have hpow : (Vtr g s N ω)^s
      = ⨆ (u : {u : ℕ → ℕ // StrictMono u}) (J : ℕ),
          (if u.1 J ≤ N then
            ENNReal.ofReal ((∑ j ∈ Finset.range J, |x (u.1 (j+1)) - x (u.1 j)|^s) ^ (1/s))
          else 0)^s := by
    rw [Vtr]
    rw [ENNReal.iSup_rpow _ s hs0]
    congr 1
    ext u
    rw [ENNReal.iSup_rpow _ s hs0]
  rw [hpow]
  refine iSup_le (fun u => ?_)
  refine iSup_le (fun J => ?_)
  by_cases hN : u.1 J ≤ N
  · rw [if_pos hN]
    have hsum_nn : 0 ≤ ∑ j ∈ Finset.range J, |x (u.1 (j+1)) - x (u.1 j)|^s :=
      Finset.sum_nonneg (fun j _ => Real.rpow_nonneg (abs_nonneg _) s)
    have hX : (ENNReal.ofReal ((∑ j ∈ Finset.range J,
          |x (u.1 (j+1)) - x (u.1 j)|^s) ^ (1/s)))^s
        = ENNReal.ofReal (∑ j ∈ Finset.range J, |x (u.1 j) - x (u.1 (j+1))|^s) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hsum_nn _) hs0.le]
      congr 1
      rw [← Real.rpow_mul hsum_nn, one_div, inv_mul_cancel₀ hs0.ne', Real.rpow_one]
      exact Finset.sum_congr rfl (fun j _ => by rw [abs_sub_comm])
    rw [hX]
    have hptw := ptw_domination x N (ρ := 2) (r := s) (by norm_num) hs2 u u.2 J hN
    refine hptw.trans ?_
    have hZ : (⨆ M : ℕ, ENNReal.ofReal
        (∑ m ∈ Finset.Icc 2 M, (1/2:ℝ)^((m-2)*(s-2)) *
          ∑ j ∈ Finset.range (N+2),
            |x (tau x N m j) - x (tau x N m (j+1))|^(2:ℝ))) ≤ Ztr g s N ω := by
      refine iSup_le (fun M => ?_)
      refine le_trans (le_of_eq ?_) (ofReal_Zterm_le_Ztr g s N M ω)
      congr 1
    calc ENNReal.ofReal (8 ^ (2:ℝ) * rng x N ^ (s - 2)) *
          (⨆ M : ℕ, ENNReal.ofReal
            (∑ m ∈ Finset.Icc 2 M, (1/2:ℝ)^((m-2)*(s-2)) *
              ∑ j ∈ Finset.range (N+2), |x (tau x N m j) - x (tau x N m (j+1))|^2))
        ≤ (64 * (ENNReal.ofReal (rng x N))^(s-2)) * Ztr g s N ω :=
          mul_le_mul' (ofReal_rpow_rng_le g hs2 N ω) hZ
      _ = 64 * (ENNReal.ofReal (rng x N))^(s - 2) * Ztr g s N ω := by ring
  · rw [if_neg hN]
    rw [ENNReal.zero_rpow_of_pos hs0]
    exact zero_le

lemma ENNReal.sq_le_of_rpow_le {a b Z : ℝ≥0∞} {s : ℝ} (hs : 2 < s) (hb : b < ⊤) (hba : b ≤ a)
    (h : a^s ≤ 64 * b^(s-2) * Z) : a^(2:ℝ) ≤ 64 * Z := by
  have hs2 : (0:ℝ) < s - 2 := by linarith
  rcases eq_or_ne a 0 with ha0 | ha0
  · rw [ha0, ENNReal.zero_rpow_of_pos (by norm_num : (0:ℝ) < 2)]; exact zero_le
  rcases eq_or_ne a ⊤ with haT | haT
  · rw [haT] at h ⊢
    rw [ENNReal.top_rpow_of_pos (by linarith : (0:ℝ) < s)] at h
    rcases eq_or_ne b 0 with hb0 | hb0
    · rw [hb0, ENNReal.zero_rpow_of_pos hs2] at h
      rw [mul_zero, zero_mul] at h
      exact absurd h (not_le.mpr ENNReal.zero_lt_top)
    · have hbr : b ^ (s-2) < ⊤ :=
        lt_top_iff_ne_top.mpr (ENNReal.rpow_ne_top_of_ne_zero hb0 (lt_top_iff_ne_top.mp hb))
      have hZ : Z = ⊤ := by
        by_contra hZne
        exact absurd h (not_le.mpr (ENNReal.mul_lt_top
          (ENNReal.mul_lt_top (by norm_num) hbr) (lt_top_iff_ne_top.mpr hZne)))
      rw [hZ, ENNReal.mul_top (by norm_num : (64:ℝ≥0∞) ≠ 0),
        ENNReal.top_rpow_of_pos (by norm_num : (0:ℝ) < 2)]
  · have hac : a^s = a^(s-2) * a^(2:ℝ) := by
      conv_lhs => rw [show s = (s-2) + 2 by ring]
      rw [ENNReal.rpow_add (s-2) 2 ha0 haT]
    rw [hac] at h
    have hA0 : a ^ (s-2) ≠ 0 :=
      ne_of_gt (ENNReal.rpow_pos (lt_of_le_of_ne zero_le (Ne.symm ha0)) haT)
    have hAT : a ^ (s-2) ≠ ⊤ := ENNReal.rpow_ne_top_of_ne_zero ha0 haT
    have h1 : a^(2:ℝ) ≤ (a^(s-2))⁻¹ * (64 * b^(s-2) * Z) := by
      have h' := mul_le_mul_of_nonneg_left h (zero_le : (0:ℝ≥0∞) ≤ (a^(s-2))⁻¹)
      rw [← mul_assoc, ENNReal.inv_mul_cancel hA0 hAT, one_mul] at h'
      exact h'
    have hb2 : (b * a⁻¹)^(s-2) = b^(s-2) * (a^(s-2))⁻¹ := by
      rw [ENNReal.mul_rpow_of_nonneg b a⁻¹ (by positivity : (0:ℝ) ≤ s-2),
        ENNReal.inv_rpow]
    have h2 : (a^(s-2))⁻¹ * (64 * b^(s-2) * Z) = 64 * (b * a⁻¹)^(s-2) * Z := by
      rw [hb2]; ring
    rw [h2] at h1
    have hba1 : b * a⁻¹ ≤ 1 := by
      refine le_trans (mul_le_mul_of_nonneg_right hba zero_le) ?_
      rw [ENNReal.mul_inv_cancel ha0 haT]
    have h3 : (b * a⁻¹)^(s-2) ≤ 1 := ENNReal.rpow_le_one hba1 hs2.le
    calc a^(2:ℝ) ≤ 64 * (b * a⁻¹)^(s-2) * Z := h1
      _ ≤ 64 * 1 * Z := by gcongr
      _ = 64 * Z := by ring

lemma Vtr_sq_le (g : ℕ → Ω → ℝ) {s : ℝ} (hs0 : 0 < s) (hs2 : 2 < s) (N : ℕ) (ω : Ω) :
    (Vtr g s N ω)^(2:ℝ) ≤ 64 * Ztr g s N ω :=
  ENNReal.sq_le_of_rpow_le hs2 ENNReal.ofReal_lt_top (ofReal_rng_le_Vtr g hs0 N ω)
    (Vtr_rpow_le g hs0 hs2 N ω)

lemma rpow_two_abs_sub (a b : ℝ) : |a - b|^(2:ℝ) = (b - a)^2 := by
  rw [Real.rpow_ofNat, sq_abs]; ring

lemma sm_eq_cap (g : ℕ → Ω → ℝ) {N mm j : ℕ} (h : N+1 ≤ j) :
    sm g N mm j = sm g N mm (N+1) := by
  funext ω
  simp only [sm]
  rw [tau_eq_cap (fun k => g k ω) N mm j h,
    tau_eq_cap (fun k => g k ω) N mm (N+1) le_rfl]

lemma dinc_sm_eq_zero (g : ℕ → Ω → ℝ) {N mm j : ℕ} (h : N+1 ≤ j) :
    dinc (sm g N mm) j = 0 := by
  have h1 : sm g N mm (j+1) = sm g N mm (N+1) := sm_eq_cap g (by omega)
  have h2 : sm g N mm j = sm g N mm (N+1) := sm_eq_cap g h
  simp only [dinc, Pi.sub_apply, Pi.zero_apply]
  rw [h1, h2, sub_self]

lemma preSq_sm_stab (g : ℕ → Ω → ℝ) (N mm K : ℕ) (h : N+2 ≤ K) :
    preSq (sm g N mm) K = preSq (sm g N mm) (N+2) := by
  funext ω
  unfold preSq
  rw [← Finset.sum_range_add_sum_Ico (fun n => (dinc (sm g N mm) n ω)^2) h]
  have hzero : ∑ j ∈ Finset.Ico (N+2) K, (dinc (sm g N mm) j ω)^2 = 0 := by
    refine Finset.sum_eq_zero (fun j hj => ?_)
    rw [Finset.mem_Ico] at hj
    rw [dinc_sm_eq_zero g (j := j) (by omega)]
    simp
  rw [hzero, add_zero]

lemma Ssq_sm_eq (g : ℕ → Ω → ℝ) (N mm : ℕ) (ω : Ω) :
    Ssq (sm g N mm) ω = ENNReal.ofReal (preSq (sm g N mm) (N+2) ω) := by
  refine le_antisymm ?_ (le_iSup (fun K : ℕ => ENNReal.ofReal (preSq (sm g N mm) K ω)) (N+2))
  refine iSup_le (fun K => ?_)
  by_cases hK : K ≤ N+2
  · exact ENNReal.ofReal_le_ofReal (preSq_mono (sm g N mm) hK ω)
  · rw [preSq_sm_stab g N mm K (by omega)]

lemma Zterm_eq (g : ℕ → Ω → ℝ) (s : ℝ) (N M : ℕ) (ω : Ω) :
    Zterm g s N M ω
      = ∑ m ∈ Finset.Icc 2 M, (1/2:ℝ)^((m-2)*(s-2)) * preSq (sm g N m) (N+2) ω := by
  refine Finset.sum_congr rfl (fun m _ => ?_)
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp only [preSq, dinc, Pi.sub_apply, sm]
  rw [rpow_two_abs_sub]

lemma ofReal_Zterm_eq (g : ℕ → Ω → ℝ) (s : ℝ) (N M : ℕ) (ω : Ω) :
    ENNReal.ofReal (Zterm g s N M ω)
      = ∑ m ∈ Finset.Icc 2 M, ENNReal.ofReal ((1/2:ℝ)^((m-2)*(s-2))) * Ssq (sm g N m) ω := by
  rw [Zterm_eq]
  have hnn : ∀ m ∈ Finset.Icc 2 M,
      0 ≤ (1/2:ℝ)^((m-2)*(s-2)) * preSq (sm g N m) (N+2) ω :=
    fun m _ => mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (Finset.sum_nonneg (fun j _ => sq_nonneg _))
  rw [ENNReal.ofReal_sum_of_nonneg (s := Finset.Icc 2 M)
    (f := fun m => (1/2:ℝ)^((m-2)*(s-2)) * preSq (sm g N m) (N+2) ω) hnn]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  rw [ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _)]
  congr 1
  exact (Ssq_sm_eq g N m ω).symm


end Variation


section NormBound

set_option backward.isDefEq.respectTransparency false in
lemma measurable_Zterm (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (g : ℕ → Ω → ℝ)
    (hgm : ∀ n, Measurable[ℱ n] (g n)) (s : ℝ) (N M : ℕ) : Measurable (Zterm g s N M) := by
  refine Finset.measurable_sum _ (fun m hm => ?_)
  refine Measurable.const_mul ?_ _
  refine Finset.measurable_sum _ (fun j hj => ?_)
  have habs : Measurable (fun ω => |g (tau (fun k => g k ω) N m j) ω
      - g (tau (fun k => g k ω) N m (j+1)) ω|) :=
    (((measurable_sm_aux ℱ g hgm N m j).sub
      (measurable_sm_aux ℱ g hgm N m (j+1))).abs)
  have h2 := habs.pow_const 2
  convert h2 using 1
  ext a
  rw [Real.rpow_ofNat]

set_option backward.isDefEq.respectTransparency false in
lemma measurable_Ztr (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (g : ℕ → Ω → ℝ)
    (hgm : ∀ n, Measurable[ℱ n] (g n)) (s : ℝ) (N : ℕ) : Measurable (Ztr g s N) := by
  refine Measurable.iSup (fun M => ?_)
  exact (measurable_Zterm ℱ g hgm s N M).ennreal_ofReal

lemma one_sub_half_rpow_ge {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    x * Real.log 2 / 2 ≤ 1 - (1/2:ℝ)^x := by
  have h2pos : (0:ℝ) < 2 := by norm_num
  have h2x1 : 1 + x * Real.log 2 ≤ (2:ℝ)^x := by
    rw [Real.rpow_def_of_pos h2pos]
    have := Real.add_one_le_exp (Real.log 2 * x)
    linarith
  have h2x2 : (2:ℝ)^x ≤ 2 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hx1
    rwa [Real.rpow_one] at h
  have hpos : 0 < (2:ℝ)^x := Real.rpow_pos_of_pos h2pos x
  have hinv : (1:ℝ)/2 ≤ ((2:ℝ)^x)⁻¹ := by
    rw [one_div, inv_le_inv₀ (by norm_num) hpos]
    exact h2x2
  have hneg : (1/2:ℝ)^x = ((2:ℝ)^x)⁻¹ := by
    rw [show (1/2:ℝ) = (2:ℝ)⁻¹ by norm_num, Real.inv_rpow (by norm_num : (0:ℝ) ≤ 2)]
  rw [hneg]
  calc x * Real.log 2 / 2 = (x * Real.log 2) * (1/2) := by ring
    _ ≤ ((2:ℝ)^x - 1) * ((2:ℝ)^x)⁻¹ :=
        mul_le_mul (by linarith [mul_nonneg (le_of_lt hx0) (le_of_lt (Real.log_pos one_lt_two))]) hinv
          (by norm_num) (by linarith [mul_nonneg (le_of_lt hx0) (le_of_lt (Real.log_pos one_lt_two))])
    _ = 1 - ((2:ℝ)^x)⁻¹ := by
        rw [sub_mul, one_mul, mul_inv_cancel₀ (ne_of_gt hpos)]

lemma geom_bound {s : ℝ} (hs2 : 2 < s) (hs3 : s ≤ 3) (M : ℕ) :
    ∑ m ∈ Finset.Icc 2 M, (1/2:ℝ)^((m-2)*(s-2)) ≤ 2/((s-2)*Real.log 2) := by
  have hs0 : 0 < s - 2 := by linarith
  have hs1 : s - 2 ≤ 1 := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  set c : ℝ := (1/2:ℝ)^(s-2) with hc
  have hc0 : 0 ≤ c := Real.rpow_nonneg (by norm_num) _
  have hbase : (1 - c) ≥ (s-2) * Real.log 2 / 2 := by
    rw [hc]; exact one_sub_half_rpow_ge hs0 hs1
  have hlt : c < 1 := by
    have h2 : 0 < (s - 2) * Real.log 2 / 2 := by positivity
    linarith
  have hpow : ∀ m ∈ Finset.Icc 2 M, (1/2:ℝ)^((m-2)*(s-2)) = c^(m-2) := by
    intro m hm
    have hm2 : 2 ≤ m := (Finset.mem_Icc.mp hm).1
    rw [hc]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 1/2)]
    congr 1
    rw [Nat.cast_sub hm2]; ring
  calc ∑ m ∈ Finset.Icc 2 M, (1/2:ℝ)^((m-2)*(s-2))
      = ∑ m ∈ Finset.Icc 2 M, c^(m-2) := Finset.sum_congr rfl hpow
    _ = ∑ k ∈ (Finset.Icc 2 M).image (fun m => m-2), c^k :=
        (Finset.sum_image (f := fun k : ℕ => c^k) (g := fun m : ℕ => m - 2)
          (fun a ha b hb hab => by
            obtain ⟨ha1, -⟩ := Finset.mem_Icc.mp (by simpa using ha)
            obtain ⟨hb1, -⟩ := Finset.mem_Icc.mp (by simpa using hb)
            beta_reduce at hab
            omega)).symm
    _ ≤ ∑ k ∈ Finset.range (M+1), c^k := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => pow_nonneg hc0 i)
        intro k hk
        rw [Finset.mem_image] at hk
        obtain ⟨m, hm, rfl⟩ := hk
        rw [Finset.mem_Icc] at hm
        exact Finset.mem_range.mpr (by omega)
    _ ≤ 1/(1-c) := Commons.Analysis.Asymptotics.geom_finset_le hc0 hlt _
    _ ≤ 2/((s-2)*Real.log 2) := by
        rw [div_le_div_iff₀ (by linarith) (by positivity)]
        linarith

lemma Zterm_nonneg (g : ℕ → Ω → ℝ) (s : ℝ) (N M : ℕ) (ω : Ω) : 0 ≤ Zterm g s N M ω := by
  refine Finset.sum_nonneg (fun m _ => mul_nonneg (Real.rpow_nonneg (by norm_num) _)
    (Finset.sum_nonneg (fun j _ => Real.rpow_nonneg (abs_nonneg _) _)))

lemma Zterm_mono (g : ℕ → Ω → ℝ) (s : ℝ) (N : ℕ) : Monotone (Zterm g s N) := by
  intro a b hab ω
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => ?_)
  · intro x hx
    rw [Finset.mem_Icc] at hx ⊢
    exact ⟨hx.1, le_trans hx.2 hab⟩
  · refine mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (Finset.sum_nonneg (fun j _ => Real.rpow_nonneg (abs_nonneg _) _))

set_option maxHeartbeats 1000000 in
lemma eLpNorm_Ztr_le (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (f : Ω → ℝ) {s : ℝ}
    (hs0 : 0 < s) (hs1 : 1 < s) (hs2 : 2 < s) (hs3 : s ≤ 3)
    (hf : MemLp f (ENNReal.ofReal s) μ) (N : ℕ) :
    eLpNorm (Ztr (fun n => condExp (ℱ n) μ f) s N) (ENNReal.ofReal (s/2)) μ
      ≤ ENNReal.ofReal (2/((s-2)*Real.log 2)) * ENNReal.ofReal (bdgZZ s)
          * (eLpNorm f (ENNReal.ofReal s) μ)^2 := by
  haveI : SigmaFiniteFiltration μ ℱ := ⟨fun _ => inferInstance⟩
  have hgm : ∀ n, Measurable[ℱ n] (condExp (ℱ n) μ f) :=
    fun n => (stronglyMeasurable_condExp (m := ℱ n)).measurable
  have hp0 : ENNReal.ofReal (s/2) ≠ 0 := by rw [ENNReal.ofReal_ne_zero_iff]; linarith
  have hpT : ENNReal.ofReal (s/2) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hmono : Monotone (fun M : ℕ => fun ω =>
      ENNReal.ofReal (Zterm (fun n => condExp (ℱ n) μ f) s N M ω)) := by
    intro a b hab ω
    exact ENNReal.ofReal_le_ofReal (Zterm_mono (fun n => condExp (ℱ n) μ f) s N hab ω)
  have hkey : eLpNorm (fun ω => ⨆ M : ℕ,
        ENNReal.ofReal (Zterm (fun n => condExp (ℱ n) μ f) s N M ω)) (ENNReal.ofReal (s/2)) μ
      = ⨆ M : ℕ, eLpNorm (fun ω => ENNReal.ofReal
          (Zterm (fun n => condExp (ℱ n) μ f) s N M ω)) (ENNReal.ofReal (s/2)) μ :=
    Commons.Analysis.MeasureTheory.eLpNorm_iSup_of_monotone hp0 hpT
      (fun M => (measurable_Zterm ℱ _ hgm s N M).ennreal_ofReal) hmono
  rw [show Ztr (fun n => condExp (ℱ n) μ f) s N = fun ω => ⨆ M : ℕ,
      ENNReal.ofReal (Zterm (fun n => condExp (ℱ n) μ f) s N M ω) from rfl, hkey]
  refine iSup_le (fun M => ?_)
  have hsum : ∀ m ∈ Finset.Icc 2 M, AEMeasurable (fun ω =>
      ENNReal.ofReal ((1/2:ℝ)^((m-2)*(s-2))) * Ssq (sm (fun n => condExp (ℱ n) μ f) N m) ω) μ := by
    intro m hm
    exact ((measurable_Ssq_sm ℱ _ hgm N m).const_mul
      (ENNReal.ofReal ((1/2:ℝ)^((m-2)*(s-2))))).aemeasurable
  have h1p : (1:ℝ≥0∞) ≤ ENNReal.ofReal (s/2) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith : (1:ℝ) ≤ s/2)
  refine le_trans (le_of_eq ?_) (le_trans
    (Commons.MeasureTheory.Lp.eLpNorm_finset_sum_le_ennreal h1p hsum) ?_)
  · refine eLpNorm_congr_ae (Filter.Eventually.of_forall (fun ω => ?_))
    exact ofReal_Zterm_eq _ s N M ω
  · calc ∑ m ∈ Finset.Icc 2 M, eLpNorm (fun ω =>
          ENNReal.ofReal ((1/2:ℝ)^((m-2)*(s-2))) * Ssq (sm (fun n => condExp (ℱ n) μ f) N m) ω)
          (ENNReal.ofReal (s/2)) μ
        ≤ ∑ m ∈ Finset.Icc 2 M, ENNReal.ofReal ((1/2:ℝ)^((m-2)*(s-2))) *
            (ENNReal.ofReal (bdgZZ s) * (eLpNorm f (ENNReal.ofReal s) μ)^2) := by
          refine Finset.sum_le_sum (fun m hm => ?_)
          rw [Commons.MeasureTheory.Lp.eLpNorm_const_mul_ennreal
            (c := ENNReal.ofReal ((1/2:ℝ)^((m-2)*(s-2))))
            (V := Ssq (sm (fun n => condExp (ℱ n) μ f) N m)) ENNReal.ofReal_ne_top hp0 hpT]
          exact mul_le_mul_of_nonneg_left (bdg_sm_sq ℱ f hs0 hs1 hs2 hf N m) zero_le
      _ = (∑ m ∈ Finset.Icc 2 M, ENNReal.ofReal ((1/2:ℝ)^((m-2)*(s-2)))) *
            (ENNReal.ofReal (bdgZZ s) * (eLpNorm f (ENNReal.ofReal s) μ)^2) := by
          rw [Finset.sum_mul]
      _ = ENNReal.ofReal (∑ m ∈ Finset.Icc 2 M, (1/2:ℝ)^((m-2)*(s-2))) *
            (ENNReal.ofReal (bdgZZ s) * (eLpNorm f (ENNReal.ofReal s) μ)^2) := by
          rw [ENNReal.ofReal_sum_of_nonneg (fun m _ => Real.rpow_nonneg (by norm_num) _)]
      _ ≤ ENNReal.ofReal (2/((s-2)*Real.log 2)) *
            (ENNReal.ofReal (bdgZZ s) * (eLpNorm f (ENNReal.ofReal s) μ)^2) := by
          refine mul_le_mul_of_nonneg_right ?_ zero_le
          exact ENNReal.ofReal_le_ofReal (geom_bound hs2 hs3 M)
      _ = ENNReal.ofReal (2/((s-2)*Real.log 2)) * ENNReal.ofReal (bdgZZ s)
            * (eLpNorm f (ENNReal.ofReal s) μ)^2 := by ring


end NormBound


section Enorm

theorem enorm_iSup_le {ι : Type*} [Nonempty ι] (f : ι → ℝ) :
    ‖⨆ i, f i‖ₑ ≤ ⨆ i, ‖f i‖ₑ := by
  set Y : ℝ≥0∞ := ⨆ i, ‖f i‖ₑ with hYdef
  by_cases hY : Y = ⊤
  · rw [hY]; exact le_top
  have hfi : ∀ i, |f i| ≤ Y.toReal := by
    intro i
    have h1 : ‖f i‖ₑ ≤ Y := le_iSup (fun i => ‖f i‖ₑ) i
    have h2 : ‖f i‖ₑ ≠ ⊤ := ne_top_of_le_ne_top hY h1
    have := ENNReal.toReal_mono hY h1
    rwa [Real.enorm_eq_ofReal_abs, ENNReal.toReal_ofReal (abs_nonneg _)] at this
  have hbdd : BddAbove (Set.range f) := ⟨Y.toReal, by rintro x ⟨i, rfl⟩; exact le_trans (le_abs_self _) (hfi i)⟩
  have h2 : (⨆ i, f i) ≤ Y.toReal := ciSup_le (fun i => le_trans (le_abs_self _) (hfi i))
  have h3 : -Y.toReal ≤ (⨆ i, f i) :=
    le_ciSup_of_le hbdd (Classical.arbitrary ι) (by linarith [hfi (Classical.arbitrary ι), neg_abs_le (f (Classical.arbitrary ι))])
  rw [Real.enorm_eq_ofReal_abs]
  refine le_trans (ENNReal.ofReal_le_ofReal (abs_le.mpr ⟨h3, h2⟩)) ?_
  exact ENNReal.ofReal_toReal_le


end Enorm


section VtrF

/-- The finite-chain version of the truncated variation. -/
noncomputable def VtrF (g : ℕ → Ω → ℝ) (s : ℝ) (N : ℕ) : Ω → ℝ≥0∞ :=
  fun ω => ⨆ (q : Σ J : ℕ, (Fin (J+1) → ℕ)),
    if q.1 ≤ N ∧ StrictMono q.2 ∧ q.2 ⟨q.1, Nat.lt_succ_self q.1⟩ ≤ N then
      ENNReal.ofReal ((∑ j ∈ Finset.range q.1,
        |g (q.2 ⟨min (j+1) q.1, Nat.lt_succ_of_le (min_le_right _ _)⟩) ω
         - g (q.2 ⟨min j q.1, Nat.lt_succ_of_le (min_le_right _ _)⟩) ω|^s) ^ (1/s))
    else 0

/-- The extension of a finite chain to a strictly monotone map `ℕ → ℕ`. -/
noncomputable def chainExt {J : ℕ} (w : Fin (J+1) → ℕ) : ℕ → ℕ :=
  fun j => if hj : j ≤ J then w ⟨j, Nat.lt_succ_of_le hj⟩ else w ⟨J, Nat.lt_succ_self J⟩ + (j - J)

lemma chainExt_of_le {J : ℕ} (w : Fin (J+1) → ℕ) {j : ℕ} (hj : j ≤ J) :
    chainExt w j = w ⟨j, Nat.lt_succ_of_le hj⟩ := dif_pos hj

lemma chainExt_mono {J : ℕ} {w : Fin (J+1) → ℕ} (hw : StrictMono w) :
    StrictMono (chainExt w) := by
  intro a b hab
  rw [chainExt, chainExt]
  by_cases hb : b ≤ J
  · have ha : a ≤ J := by omega
    rw [dif_pos ha, dif_pos hb]
    exact hw (by rw [Fin.lt_def]; exact_mod_cast hab)
  · have hbJ : J < b := by omega
    by_cases ha : a ≤ J
    · rw [dif_pos ha, dif_neg hb]
      have h1 : w ⟨a, Nat.lt_succ_of_le ha⟩ ≤ w ⟨J, Nat.lt_succ_self J⟩ :=
        hw.monotone (by rw [Fin.le_def]; exact_mod_cast ha)
      omega
    · rw [dif_neg ha, dif_neg hb]
      omega

lemma VtrF_le_Vtr (g : ℕ → Ω → ℝ) (s : ℝ) (N : ℕ) : VtrF g s N ≤ Vtr g s N := by
  intro ω
  rw [VtrF, Vtr]
  refine iSup_le (fun q => ?_)
  rcases q with ⟨J, w⟩
  by_cases h : J ≤ N ∧ StrictMono w ∧ w ⟨J, Nat.lt_succ_self J⟩ ≤ N
  · rw [if_pos h]
    obtain ⟨hJ, hmono, hlast⟩ := h
    have hu_mono : StrictMono (chainExt w) := chainExt_mono hmono
    have huJ : chainExt w J = w ⟨J, Nat.lt_succ_self J⟩ := chainExt_of_le _ le_rfl
    have hsum : (∑ j ∈ Finset.range J,
          |g (w ⟨min (j+1) J, Nat.lt_succ_of_le (min_le_right _ _)⟩) ω
           - g (w ⟨min j J, Nat.lt_succ_of_le (min_le_right _ _)⟩) ω|^s)
        = ∑ j ∈ Finset.range J, |g (chainExt w (j+1)) ω - g (chainExt w j) ω|^s := by
      refine Finset.sum_congr rfl (fun j hj => ?_)
      rw [Finset.mem_range] at hj
      have hj1 : j + 1 ≤ J := by omega
      have hjJ : j ≤ J := by omega
      have e1 : w ⟨min (j+1) J, Nat.lt_succ_of_le (min_le_right _ _)⟩
          = w ⟨j+1, Nat.lt_succ_of_le hj1⟩ :=
        congrArg w (Fin.ext (min_eq_left hj1))
      have e2 : w ⟨min j J, Nat.lt_succ_of_le (min_le_right _ _)⟩
          = w ⟨j, Nat.lt_succ_of_le hjJ⟩ :=
        congrArg w (Fin.ext (min_eq_left hjJ))
      rw [e1, e2, chainExt_of_le _ hj1, chainExt_of_le _ hjJ]
    rw [hsum]
    have hinner := le_iSup (fun J' : ℕ => if chainExt w J' ≤ N then ENNReal.ofReal
        ((∑ j ∈ Finset.range J', |g (chainExt w (j+1)) ω - g (chainExt w j) ω|^s) ^ (1/s))
        else 0) J
    rw [if_pos (by rw [huJ]; exact hlast)] at hinner
    refine le_trans hinner ?_
    exact le_iSup (fun u : {u : ℕ → ℕ // StrictMono u} => ⨆ J' : ℕ,
        if u.1 J' ≤ N then ENNReal.ofReal ((∑ j ∈ Finset.range J',
          |g (u.1 (j+1)) ω - g (u.1 j) ω|^s) ^ (1/s)) else 0) ⟨chainExt w, hu_mono⟩
  · rw [if_neg h]
    exact zero_le

lemma Vtr_le_VtrF (g : ℕ → Ω → ℝ) (s : ℝ) (N : ℕ) : Vtr g s N ≤ VtrF g s N := by
  intro ω
  rw [Vtr, VtrF]
  refine iSup_le (fun u => iSup_le (fun J => ?_))
  by_cases hN : u.1 J ≤ N
  · rw [if_pos hN]
    have hJ : J ≤ N := le_trans (u.2.id_le J) hN
    have hmono : StrictMono (fun i : Fin (J+1) => u.1 i.val) := by
      intro a b hab
      simpa using u.2 (show (a : ℕ) < (b : ℕ) from hab)
    have hlast : (fun i : Fin (J+1) => u.1 i.val) ⟨J, Nat.lt_succ_self J⟩ ≤ N := hN
    have hsum : (∑ j ∈ Finset.range J, |g (u.1 (j+1)) ω - g (u.1 j) ω|^s)
        = ∑ j ∈ Finset.range J,
            |g ((fun i : Fin (J+1) => u.1 i.val)
                ⟨min (j+1) J, Nat.lt_succ_of_le (min_le_right _ _)⟩) ω
             - g ((fun i : Fin (J+1) => u.1 i.val)
                ⟨min j J, Nat.lt_succ_of_le (min_le_right _ _)⟩) ω|^s := by
      refine Finset.sum_congr rfl (fun j hj => ?_)
      rw [Finset.mem_range] at hj
      have hj1 : j + 1 ≤ J := by omega
      have hjJ : j ≤ J := by omega
      have e1 : (⟨min (j+1) J, Nat.lt_succ_of_le (min_le_right _ _)⟩ : Fin (J+1))
          = ⟨j+1, Nat.lt_succ_of_le hj1⟩ := Fin.ext (min_eq_left hj1)
      have e2 : (⟨min j J, Nat.lt_succ_of_le (min_le_right _ _)⟩ : Fin (J+1))
          = ⟨j, Nat.lt_succ_of_le hjJ⟩ := Fin.ext (min_eq_left hjJ)
      rw [e1, e2]
    rw [hsum]
    have hinner := le_iSup (fun q : Σ J' : ℕ, (Fin (J'+1) → ℕ) =>
        if q.1 ≤ N ∧ StrictMono q.2 ∧ q.2 ⟨q.1, Nat.lt_succ_self q.1⟩ ≤ N then
          ENNReal.ofReal ((∑ j ∈ Finset.range q.1,
            |g (q.2 ⟨min (j+1) q.1, Nat.lt_succ_of_le (min_le_right _ _)⟩) ω
             - g (q.2 ⟨min j q.1, Nat.lt_succ_of_le (min_le_right _ _)⟩) ω|^s) ^ (1/s))
        else 0) ⟨J, fun i => u.1 i.val⟩
    rw [if_pos ⟨hJ, hmono, hlast⟩] at hinner
    exact hinner
  · rw [if_neg hN]
    exact zero_le

lemma Vtr_eq_VtrF (g : ℕ → Ω → ℝ) (s : ℝ) (N : ℕ) : Vtr g s N = VtrF g s N :=
  le_antisymm (Vtr_le_VtrF g s N) (VtrF_le_Vtr g s N)

set_option maxHeartbeats 800000 in
lemma measurable_VtrF (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (g : ℕ → Ω → ℝ)
    (hgm : ∀ n, Measurable[ℱ n] (g n)) (s : ℝ) (N : ℕ) : Measurable (VtrF g s N) := by
  refine Measurable.iSup (fun q : Σ J : ℕ, (Fin (J+1) → ℕ) => ?_)
  by_cases h : q.1 ≤ N ∧ StrictMono q.2 ∧ q.2 ⟨q.1, Nat.lt_succ_self q.1⟩ ≤ N
  · simp only [if_pos h]
    refine Measurable.ennreal_ofReal ?_
    refine Measurable.pow_const ?_ _
    refine Finset.measurable_sum _ (fun j hj => ?_)
    refine ((Measurable.sub ?_ ?_).abs).pow_const s
    · exact (hgm (q.2 ⟨min (j+1) q.1, Nat.lt_succ_of_le (min_le_right _ _)⟩)).mono
        (ℱ.le _) le_rfl
    · exact (hgm (q.2 ⟨min j q.1, Nat.lt_succ_of_le (min_le_right _ _)⟩)).mono
        (ℱ.le _) le_rfl
  · simp only [if_neg h]
    exact measurable_const

set_option maxHeartbeats 800000 in
lemma measurable_Vtr (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (g : ℕ → Ω → ℝ)
    (hgm : ∀ n, Measurable[ℱ n] (g n)) (s : ℝ) (N : ℕ) : Measurable (Vtr g s N) := by
  rw [Vtr_eq_VtrF]
  exact measurable_VtrF ℱ g hgm s N


end VtrF


section VtrNorm

lemma Vtr_mono (g : ℕ → Ω → ℝ) (s : ℝ) : Monotone (Vtr g s) := by
  intro N N' hNN ω
  change (⨆ (u : {u : ℕ → ℕ // StrictMono u}) (J : ℕ),
      if u.1 J ≤ N then ENNReal.ofReal ((∑ j ∈ Finset.range J,
        |g (u.1 (j+1)) ω - g (u.1 j) ω|^s) ^ (1/s)) else 0)
    ≤ (⨆ (u : {u : ℕ → ℕ // StrictMono u}) (J : ℕ),
      if u.1 J ≤ N' then ENNReal.ofReal ((∑ j ∈ Finset.range J,
        |g (u.1 (j+1)) ω - g (u.1 j) ω|^s) ^ (1/s)) else 0)
  refine iSup_le (fun u => iSup_le (fun J => ?_))
  by_cases h : u.1 J ≤ N
  · have h' : u.1 J ≤ N' := le_trans h hNN
    rw [if_pos h]
    refine le_trans ?_ (le_iSup (fun u' : {u : ℕ → ℕ // StrictMono u} => ⨆ J' : ℕ,
        if u'.1 J' ≤ N' then ENNReal.ofReal ((∑ j ∈ Finset.range J',
          |g (u'.1 (j+1)) ω - g (u'.1 j) ω|^s) ^ (1/s)) else 0) u)
    refine le_trans (le_of_eq (if_pos h').symm)
      (le_iSup (fun J' : ℕ => if u.1 J' ≤ N' then ENNReal.ofReal ((∑ j ∈ Finset.range J',
        |g (u.1 (j+1)) ω - g (u.1 j) ω|^s) ^ (1/s)) else 0) J)
  · rw [if_neg h]
    exact zero_le

set_option maxHeartbeats 800000 in
lemma eLpNorm_Vtr_le (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (f : Ω → ℝ) {s : ℝ}
    (hs0 : 0 < s) (hs2 : 2 < s) (hs3 : s ≤ 3)
    (hf : MemLp f (ENNReal.ofReal s) μ) (N : ℕ) :
    eLpNorm (Vtr (fun n => condExp (ℱ n) μ f) s N) (ENNReal.ofReal s) μ
      ≤ 8 * ((ENNReal.ofReal (2/((s-2)*Real.log 2)) * ENNReal.ofReal (bdgZZ s))^(1/2 : ℝ)
          * eLpNorm f (ENNReal.ofReal s) μ) := by
  have hsa : (0:ℝ) < s/2 := by linarith
  have hgm : ∀ n, Measurable[ℱ n] (condExp (ℱ n) μ f) :=
    fun n => (stronglyMeasurable_condExp (m := ℱ n)).measurable
  have hle : ∀ ω, ((Vtr (fun n => condExp (ℱ n) μ f) s N ω)^(2:ℝ))^(s/2)
      ≤ (64 * Ztr (fun n => condExp (ℱ n) μ f) s N ω)^(s/2) :=
    fun ω => ENNReal.rpow_le_rpow
      (Vtr_sq_le (fun n => condExp (ℱ n) μ f) hs0 hs2 N ω) hsa.le
  have hpow : ∀ ω, ((Vtr (fun n => condExp (ℱ n) μ f) s N ω)^(2:ℝ))^(s/2)
      = (Vtr (fun n => condExp (ℱ n) μ f) s N ω)^s := by
    intro ω
    rw [← ENNReal.rpow_mul]
    congr 1; ring
  have hInt : ∫⁻ ω, (Vtr (fun n => condExp (ℱ n) μ f) s N ω)^s ∂μ
      ≤ (64:ℝ≥0∞)^(s/2) * ∫⁻ ω,
          (Ztr (fun n => condExp (ℱ n) μ f) s N ω)^(s/2) ∂μ := by
    calc ∫⁻ ω, (Vtr (fun n => condExp (ℱ n) μ f) s N ω)^s ∂μ
        = ∫⁻ ω, ((Vtr (fun n => condExp (ℱ n) μ f) s N ω)^(2:ℝ))^(s/2) ∂μ :=
          lintegral_congr (fun ω => (hpow ω).symm)
      _ ≤ ∫⁻ ω, (64 * Ztr (fun n => condExp (ℱ n) μ f) s N ω)^(s/2) ∂μ :=
          lintegral_mono hle
      _ = ∫⁻ ω, (64:ℝ≥0∞)^(s/2) * (Ztr (fun n => condExp (ℱ n) μ f) s N ω)^(s/2) ∂μ := by
          refine lintegral_congr (fun ω => ?_)
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : (0:ℝ) ≤ s/2)]
      _ = (64:ℝ≥0∞)^(s/2) * ∫⁻ ω, (Ztr (fun n => condExp (ℱ n) μ f) s N ω)^(s/2) ∂μ := by
          rw [lintegral_const_mul'' _
            ((measurable_Ztr ℱ _ hgm s N).pow_const _).aemeasurable]
  have hp0 : ENNReal.ofReal s ≠ 0 := by rw [ENNReal.ofReal_ne_zero_iff]; linarith
  have hpT : ENNReal.ofReal s ≠ ⊤ := ENNReal.ofReal_ne_top
  have hA : eLpNorm (Vtr (fun n => condExp (ℱ n) μ f) s N) (ENNReal.ofReal s) μ
      = (∫⁻ ω, (Vtr (fun n => condExp (ℱ n) μ f) s N ω)^s ∂μ) ^ (1/s) := by
    have key := Commons.Analysis.MeasureTheory.eLpNorm_rpow_toReal (μ := μ)
      (p := ENNReal.ofReal s) (f := Vtr (fun n => condExp (ℱ n) μ f) s N) hp0 hpT
      (measurable_Vtr ℱ _ hgm s N).aestronglyMeasurable
    rw [show (eLpNorm (Vtr (fun n => condExp (ℱ n) μ f) s N) (ENNReal.ofReal s) μ)
        = ((eLpNorm (Vtr (fun n => condExp (ℱ n) μ f) s N) (ENNReal.ofReal s) μ)^(s))^(1/s)
        from by rw [← ENNReal.rpow_mul, mul_one_div, div_self (ne_of_gt hs0), ENNReal.rpow_one]]
    congr 1
    rw [ENNReal.toReal_ofReal hs0.le] at key
    exact key
  rw [hA]
  have hp0z : ENNReal.ofReal (s/2) ≠ 0 := by rw [ENNReal.ofReal_ne_zero_iff]; linarith
  have hpTz : ENNReal.ofReal (s/2) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hZ2 : eLpNorm (Ztr (fun n => condExp (ℱ n) μ f) s N) (ENNReal.ofReal (s/2)) μ
      = (∫⁻ ω, (Ztr (fun n => condExp (ℱ n) μ f) s N ω)^(s/2) ∂μ)^(2/s) := by
    have key := Commons.Analysis.MeasureTheory.eLpNorm_rpow_toReal (μ := μ)
      (p := ENNReal.ofReal (s/2)) (f := Ztr (fun n => condExp (ℱ n) μ f) s N) hp0z hpTz
      (measurable_Ztr ℱ _ hgm s N).aestronglyMeasurable
    rw [ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ s/2)] at key
    simp only [enorm_eq_self] at key
    rw [show eLpNorm (Ztr (fun n => condExp (ℱ n) μ f) s N) (ENNReal.ofReal (s/2)) μ
        = ((eLpNorm (Ztr (fun n => condExp (ℱ n) μ f) s N) (ENNReal.ofReal (s/2)) μ)^(s/2))^(2/s)
        from by rw [← ENNReal.rpow_mul, show (s/2) * (2/s) = 1 by field_simp, ENNReal.rpow_one]]
    rw [key]
  have hB2 := eLpNorm_Ztr_le ℱ f hs0 (by linarith) hs2 hs3 hf N
  calc (∫⁻ ω, (Vtr (fun n => condExp (ℱ n) μ f) s N ω)^s ∂μ)^(1/s)
      ≤ ((64:ℝ≥0∞)^(s/2) * ∫⁻ ω, (Ztr (fun n => condExp (ℱ n) μ f) s N ω)^(s/2) ∂μ)^(1/s) :=
        ENNReal.rpow_le_rpow hInt (by positivity)
    _ = 8 * (∫⁻ ω, (Ztr (fun n => condExp (ℱ n) μ f) s N ω)^(s/2) ∂μ)^(1/s) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : (0:ℝ) ≤ 1/s)]
        congr 1
        have h64 : (64:ℝ≥0∞) = ((8:ℝ≥0∞))^(2:ℝ) := by
          rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast]; norm_num
        rw [h64, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
          show (2:ℝ) * (s/2 * (1/s)) = 1 by field_simp, ENNReal.rpow_one]
    _ = 8 * (eLpNorm (Ztr (fun n => condExp (ℱ n) μ f) s N) (ENNReal.ofReal (s/2)) μ)^(1/2 : ℝ) := by
        congr 1
        rw [hZ2]
        have he : ((∫⁻ ω, (Ztr (fun n => condExp (ℱ n) μ f) s N ω)^(s/2) ∂μ)^(2/s))^(1/2 : ℝ)
            = (∫⁻ ω, (Ztr (fun n => condExp (ℱ n) μ f) s N ω)^(s/2) ∂μ)^(1/s) := by
          rw [(ENNReal.rpow_mul _ (2/s) (1/2 : ℝ)).symm]
          congr 1
          field_simp
        exact he.symm
    _ ≤ 8 * ((ENNReal.ofReal (2/((s-2)*Real.log 2)) * ENNReal.ofReal (bdgZZ s))
          * (eLpNorm f (ENNReal.ofReal s) μ)^2)^(1/2 : ℝ) :=
        mul_le_mul_of_nonneg_left (ENNReal.rpow_le_rpow hB2 (by norm_num)) (by norm_num)
    _ = 8 * ((ENNReal.ofReal (2/((s-2)*Real.log 2)) * ENNReal.ofReal (bdgZZ s))^(1/2 : ℝ)
          * eLpNorm f (ENNReal.ofReal s) μ) := by
        congr 1
        have h2 : (eLpNorm f (ENNReal.ofReal s) μ)^2
            = (eLpNorm f (ENNReal.ofReal s) μ)^(2:ℝ) := by
          rw [ENNReal.rpow_ofNat]
        rw [h2]
        have he : ((ENNReal.ofReal (2/((s-2)*Real.log 2)) * ENNReal.ofReal (bdgZZ s))
              * (eLpNorm f (ENNReal.ofReal s) μ)^(2:ℝ))^(1/2 : ℝ)
            = (ENNReal.ofReal (2/((s-2)*Real.log 2)) * ENNReal.ofReal (bdgZZ s))^(1/2 : ℝ)
              * eLpNorm f (ENNReal.ofReal s) μ := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 1/2)]
          rw [(ENNReal.rpow_mul _ (2:ℝ) (1/2 : ℝ)).symm]
          norm_num
        exact he


end VtrNorm


section Final

lemma pointwise_bound (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (f : Ω → ℝ) (s : ℝ) (ω : Ω) :
    ‖(⨆ (u : {u : ℕ → ℕ // StrictMono u}) (J : ℕ),
        (∑ j ∈ Finset.range J,
          |(condExp (ℱ (u.1 (j+1))) μ f) ω - (condExp (ℱ (u.1 j)) μ f) ω| ^ s) ^ (1 / s))‖ₑ
      ≤ ⨆ N, Vtr (fun n => condExp (ℱ n) μ f) s N ω := by
  haveI : Nonempty {u : ℕ → ℕ // StrictMono u} := ⟨⟨fun n => n, strictMono_id⟩⟩
  set X : (ℕ → ℕ) → ℕ → ℝ := fun u J => (∑ j ∈ Finset.range J,
      |(condExp (ℱ (u (j+1))) μ f) ω - (condExp (ℱ (u j)) μ f) ω| ^ s) ^ (1 / s) with hX
  have hnn : ∀ u J, 0 ≤ X u J := fun u J =>
    Real.rpow_nonneg (Finset.sum_nonneg (fun j _ => Real.rpow_nonneg (abs_nonneg _) s)) _
  have h1 : ∀ u : {u : ℕ → ℕ // StrictMono u},
      ‖(⨆ J : ℕ, X u.1 J)‖ₑ ≤ ⨆ N, Vtr (fun n => condExp (ℱ n) μ f) s N ω := by
    intro u
    refine (enorm_iSup_le (fun J : ℕ => X u.1 J)).trans (iSup_le (fun J => ?_))
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (hnn u.1 J)]
    refine le_trans ?_ (le_iSup (fun N : ℕ => Vtr (fun n => condExp (ℱ n) μ f) s N ω) (u.1 J))
    rw [Vtr]
    refine le_trans ?_ (le_iSup (fun u' : {u : ℕ → ℕ // StrictMono u} => ⨆ J' : ℕ,
      if u'.1 J' ≤ u.1 J then ENNReal.ofReal (X u'.1 J') else 0) u)
    refine le_trans ?_ (le_iSup (fun J' : ℕ =>
      if u.1 J' ≤ u.1 J then ENNReal.ofReal (X u.1 J') else 0) J)
    rw [if_pos (le_refl (u.1 J))]
  calc ‖(⨆ (u : {u : ℕ → ℕ // StrictMono u}) (J : ℕ), X u.1 J)‖ₑ
      ≤ ⨆ u : {u : ℕ → ℕ // StrictMono u}, ‖(⨆ J : ℕ, X u.1 J)‖ₑ := enorm_iSup_le _
    _ ≤ ⨆ N, Vtr (fun n => condExp (ℱ n) μ f) s N ω := iSup_le h1

omit [MeasurableSpace Ω] in
/-- For a real sequence, the real-valued (`ciSup`) `s`-variation over all subsequences equals the
`toReal` of the `ℝ≥0∞`-valued one.  When the family of chain sums is bounded both are honest
suprema; when it is unbounded, the real supremum is `0` (either the outer family is unbounded, or
every row is unbounded — a bounded row could be spliced onto any long chain). -/
lemma variation_real_eq_toReal (x : ℕ → ℝ) {s : ℝ} (hs : 0 < s) :
    (⨆ (u : {u : ℕ → ℕ // StrictMono u}) (J : ℕ),
        (∑ j ∈ Finset.range J, |x (u.1 (j+1)) - x (u.1 j)| ^ s) ^ (1 / s))
      = (⨆ (u : {u : ℕ → ℕ // StrictMono u}) (J : ℕ),
        ENNReal.ofReal ((∑ j ∈ Finset.range J, |x (u.1 (j+1)) - x (u.1 j)| ^ s) ^ (1 / s))).toReal := by
  classical
  haveI : Nonempty {u : ℕ → ℕ // StrictMono u} := ⟨⟨fun n => n, strictMono_id⟩⟩
  set S : (ℕ → ℕ) → ℕ → ℝ := fun u J => ∑ j ∈ Finset.range J, |x (u (j+1)) - x (u j)| ^ s
    with hS
  set X : (ℕ → ℕ) → ℕ → ℝ := fun u J => (S u J) ^ (1 / s) with hX
  have hSnn : ∀ u J, 0 ≤ S u J := fun u J =>
    Finset.sum_nonneg (fun j _ => Real.rpow_nonneg (abs_nonneg _) s)
  have hnn : ∀ u J, 0 ≤ X u J := fun u J => Real.rpow_nonneg (hSnn u J) _
  have hXpow : ∀ u J, (X u J) ^ s = S u J := fun u J => by
    simp only [hX]
    rw [← Real.rpow_mul (hSnn u J), one_div, inv_mul_cancel₀ hs.ne', Real.rpow_one]
  change (⨆ (u : {u : ℕ → ℕ // StrictMono u}) (J : ℕ), X u.1 J)
    = (⨆ (u : {u : ℕ → ℕ // StrictMono u}) (J : ℕ), ENNReal.ofReal (X u.1 J)).toReal
  set E := ⨆ (u : {u : ℕ → ℕ // StrictMono u}) (J : ℕ), ENNReal.ofReal (X u.1 J) with hE
  have hle : ∀ (u : {u : ℕ → ℕ // StrictMono u}) (J : ℕ), ENNReal.ofReal (X u.1 J) ≤ E :=
    fun u J => le_iSup₂ (f := fun (u : {u : ℕ → ℕ // StrictMono u}) (J : ℕ) =>
      ENNReal.ofReal (X u.1 J)) u J
  rcases lt_or_eq_of_le (le_top : E ≤ ⊤) with hω | hω
  · have hleR : ∀ (u : {u : ℕ → ℕ // StrictMono u}) (J : ℕ), X u.1 J ≤ E.toReal := fun u J =>
      (ENNReal.ofReal_le_iff_le_toReal hω.ne).mp (hle u J)
    have hbddJ : ∀ u : {u : ℕ → ℕ // StrictMono u}, BddAbove (Set.range (fun J => X u.1 J)) :=
      fun u => ⟨_, by rintro _ ⟨J, rfl⟩; exact hleR u J⟩
    have hsupJ : ∀ u : {u : ℕ → ℕ // StrictMono u}, (⨆ J, X u.1 J) ≤ E.toReal :=
      fun u => ciSup_le (hleR u)
    have hbddU : BddAbove (Set.range (fun u : {u : ℕ → ℕ // StrictMono u} => ⨆ J, X u.1 J)) :=
      ⟨_, by rintro _ ⟨u, rfl⟩; exact hsupJ u⟩
    apply le_antisymm
    · exact ciSup_le (fun u => hsupJ u)
    · have hV0 : 0 ≤ ⨆ (u : {u : ℕ → ℕ // StrictMono u}) (J : ℕ), X u.1 J :=
        Real.iSup_nonneg (fun u => Real.iSup_nonneg (fun J => hnn u.1 J))
      refine ENNReal.toReal_le_of_le_ofReal hV0 ?_
      refine iSup₂_le (fun u J => ?_)
      exact ENNReal.ofReal_le_ofReal ((le_ciSup (hbddJ u) J).trans (le_ciSup hbddU u))
  · rw [hω, ENNReal.toReal_top]
    by_cases hall : ∀ u : {u : ℕ → ℕ // StrictMono u}, ¬ BddAbove (Set.range (fun J => X u.1 J))
    · have h0 : ∀ u : {u : ℕ → ℕ // StrictMono u}, (⨆ J, X u.1 J) = 0 := fun u =>
        Real.iSup_of_not_bddAbove (hall u)
      simp only [h0, ciSup_const]
    push_neg at hall
    obtain ⟨w, Cw, hCw⟩ := hall
    by_cases hb : BddAbove (Set.range (fun u : {u : ℕ → ℕ // StrictMono u} => ⨆ J, X u.1 J))
    swap
    · exact Real.iSup_of_not_bddAbove hb
    exfalso
    obtain ⟨C, hC⟩ := hb
    -- some chain sum exceeds `C`
    obtain ⟨u, J, huJ⟩ : ∃ (u : {u : ℕ → ℕ // StrictMono u}) (J : ℕ), C < X u.1 J := by
      by_contra hcon
      push_neg at hcon
      have : E ≤ ENNReal.ofReal C :=
        iSup₂_le (fun u J => ENNReal.ofReal_le_ofReal (hcon u J))
      rw [hω] at this
      exact ENNReal.ofReal_ne_top (top_le_iff.mp this)
    -- splice the bounded row `w` after `u` at time `J`
    let v : ℕ → ℕ := fun j => if j ≤ J then u.1 j else w.1 (j - J + u.1 J)
    have hvmono : StrictMono v := by
      intro i j hij
      simp only [v]
      by_cases hj : j ≤ J
      · have hi : i ≤ J := by omega
        rw [if_pos hi, if_pos hj]; exact u.2 hij
      · rw [if_neg hj]
        have hw1 : j - J + u.1 J ≤ w.1 (j - J + u.1 J) := w.2.id_le _
        by_cases hi : i ≤ J
        · rw [if_pos hi]
          have : u.1 i ≤ u.1 J := u.2.monotone hi
          omega
        · rw [if_neg hi]; exact w.2 (by omega)
    have hvJ : X v J = X u.1 J := by
      simp only [hX, hS]
      congr 1
      refine Finset.sum_congr rfl (fun j hj => ?_)
      have hj' := Finset.mem_range.mp hj
      simp only [v, if_pos (show j ≤ J by omega), if_pos (show j + 1 ≤ J by omega)]
    have hCw' : ∀ K, S w.1 K ≤ Cw ^ s := fun K => by
      rw [← hXpow]
      exact Real.rpow_le_rpow (hnn _ _) (hCw ⟨K, rfl⟩) hs.le
    set T : ℝ := |x (v (J+1)) - x (v J)| ^ s with hT
    have hrow : ∀ K, S v K ≤ S u.1 J + T + Cw ^ s := by
      intro K
      have hsub : S v K ≤ S v (J + 1 + K) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
          (fun j _ _ => Real.rpow_nonneg (abs_nonneg _) s)
      refine hsub.trans ?_
      have hsplit : S v (J + 1 + K) = (S v J + T) +
          ∑ i ∈ Finset.range K, |x (v (J + 1 + i + 1)) - x (v (J + 1 + i))| ^ s := by
        simp only [hS]
        rw [Finset.sum_range_add, Finset.sum_range_succ]
      have hvu : S v J = S u.1 J := by
        simp only [hS]
        refine Finset.sum_congr rfl (fun j hj => ?_)
        have hj' := Finset.mem_range.mp hj
        simp only [v, if_pos (show j ≤ J by omega), if_pos (show j + 1 ≤ J by omega)]
      have htail : ∑ i ∈ Finset.range K, |x (v (J + 1 + i + 1)) - x (v (J + 1 + i))| ^ s
          ≤ Cw ^ s := by
        have heq : ∀ i, v (J + 1 + i) = w.1 (u.1 J + 1 + i) := fun i => by
          simp only [v, if_neg (show ¬ (J + 1 + i ≤ J) by omega)]
          rw [show J + 1 + i - J + u.1 J = u.1 J + 1 + i by omega]
        have h1 : ∑ i ∈ Finset.range K, |x (v (J + 1 + i + 1)) - x (v (J + 1 + i))| ^ s
            = ∑ i ∈ Finset.range K,
                |x (w.1 (u.1 J + 1 + i + 1)) - x (w.1 (u.1 J + 1 + i))| ^ s := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [show J + 1 + i + 1 = J + 1 + (i + 1) by omega, heq, heq]
          rfl
        rw [h1]
        refine le_trans ?_ (hCw' (u.1 J + 1 + K))
        simp only [hS]
        rw [Finset.sum_range_add]
        exact le_add_of_nonneg_left (Finset.sum_nonneg (fun j _ => Real.rpow_nonneg (abs_nonneg _) s))
      rw [hsplit, hvu]
      linarith
    have hbddv : BddAbove (Set.range (fun K => X v K)) := by
      refine ⟨(S u.1 J + T + Cw ^ s) ^ (1 / s), ?_⟩
      rintro _ ⟨K, rfl⟩
      exact Real.rpow_le_rpow (hSnn _ _) (hrow K) (by positivity)
    have h1 : X u.1 J ≤ ⨆ K, X (⟨v, hvmono⟩ : {u : ℕ → ℕ // StrictMono u}).1 K := by
      rw [← hvJ]; exact le_ciSup hbddv J
    have h2 : (⨆ K, X (⟨v, hvmono⟩ : {u : ℕ → ℕ // StrictMono u}).1 K) ≤ C :=
      hC ⟨⟨v, hvmono⟩, rfl⟩
    linarith

omit [MeasurableSpace Ω] in
/-- The supremum over horizons of the truncated variations is the full `ℝ≥0∞`-variation. -/
lemma iSup_Vtr_eq (g : ℕ → Ω → ℝ) (s : ℝ) (ω : Ω) :
    ⨆ N, Vtr g s N ω = ⨆ (u : {u : ℕ → ℕ // StrictMono u}) (J : ℕ),
      ENNReal.ofReal ((∑ j ∈ Finset.range J, |g (u.1 (j+1)) ω - g (u.1 j) ω| ^ s) ^ (1 / s)) := by
  apply le_antisymm
  · refine iSup_le (fun N => ?_)
    rw [Vtr]
    refine iSup₂_le (fun u J => ?_)
    split_ifs
    · exact le_iSup₂ (f := fun (u : {u : ℕ → ℕ // StrictMono u}) (J : ℕ) =>
        ENNReal.ofReal ((∑ j ∈ Finset.range J, |g (u.1 (j+1)) ω - g (u.1 j) ω| ^ s) ^ (1 / s))) u J
    · exact zero_le
  · refine iSup₂_le (fun u J => ?_)
    refine le_trans ?_ (le_iSup (fun N => Vtr g s N ω) (u.1 J))
    rw [Vtr]
    refine le_trans ?_ (le_iSup₂ (f := fun (u' : {u : ℕ → ℕ // StrictMono u}) (J' : ℕ) =>
      if u'.1 J' ≤ u.1 J then ENNReal.ofReal ((∑ j ∈ Finset.range J',
        |g (u'.1 (j+1)) ω - g (u'.1 j) ω| ^ s) ^ (1 / s)) else 0) u J)
    rw [if_pos le_rfl]

/-- The real-valued variation over all subsequences is measurable as soon as the truncated
variations `Vtr g s N` are: it is `ω ↦ (⨆ N, Vtr g s N ω).toReal`. -/
lemma measurable_iSup_variation (g : ℕ → Ω → ℝ) {s : ℝ} (hs : 0 < s)
    (hV : ∀ N, Measurable (Vtr g s N)) :
    Measurable (fun ω => ⨆ (u : {u : ℕ → ℕ // StrictMono u}) (J : ℕ),
        (∑ j ∈ Finset.range J, |g (u.1 (j+1)) ω - g (u.1 j) ω| ^ s) ^ (1 / s)) := by
  have h : (fun ω => ⨆ (u : {u : ℕ → ℕ // StrictMono u}) (J : ℕ),
        (∑ j ∈ Finset.range J, |g (u.1 (j+1)) ω - g (u.1 j) ω| ^ s) ^ (1 / s))
      = fun ω => (⨆ N, Vtr g s N ω).toReal := by
    funext ω
    rw [iSup_Vtr_eq, variation_real_eq_toReal (fun n => g n ω) hs]
  rw [h]
  exact (Measurable.iSup hV).ennreal_toReal

set_option maxHeartbeats 800000 in
lemma eLpNorm_Vinf_le (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (f : Ω → ℝ) {s : ℝ}
    (hs0 : 0 < s) (hs2 : 2 < s) (hs3 : s ≤ 3)
    (hf : MemLp f (ENNReal.ofReal s) μ) :
    eLpNorm (fun ω => ⨆ N, Vtr (fun n => condExp (ℱ n) μ f) s N ω) (ENNReal.ofReal s) μ
      ≤ 8 * ((ENNReal.ofReal (2/((s-2)*Real.log 2)) * ENNReal.ofReal (bdgZZ s))^(1/2 : ℝ)
          * eLpNorm f (ENNReal.ofReal s) μ) := by
  have hgm : ∀ n, Measurable[ℱ n] (condExp (ℱ n) μ f) :=
    fun n => (stronglyMeasurable_condExp (m := ℱ n)).measurable
  have hp0 : ENNReal.ofReal s ≠ 0 := by rw [ENNReal.ofReal_ne_zero_iff]; linarith
  have hpT : ENNReal.ofReal s ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [Commons.Analysis.MeasureTheory.eLpNorm_iSup_of_monotone hp0 hpT
    (fun N => measurable_Vtr ℱ _ hgm s N) (Vtr_mono _ s)]
  refine iSup_le (fun N => ?_)
  exact eLpNorm_Vtr_le ℱ f hs0 hs2 hs3 hf N

set_option maxHeartbeats 800000 in
lemma statement_le (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (f : Ω → ℝ) {s : ℝ}
    (hs0 : 0 < s) (hf : MemLp f (ENNReal.ofReal s) μ) :
    eLpNorm (fun ω => ⨆ (u : {u : ℕ → ℕ // StrictMono u}) (J : ℕ),
        (∑ j ∈ Finset.range J,
          |(condExp (ℱ (u.1 (j+1))) μ f) ω - (condExp (ℱ (u.1 j)) μ f) ω| ^ s) ^ (1 / s))
      (ENNReal.ofReal s) μ
      ≤ eLpNorm (fun ω => ⨆ N, Vtr (fun n => condExp (ℱ n) μ f) s N ω)
          (ENNReal.ofReal s) μ := by
  have hp0 : ENNReal.ofReal s ≠ 0 := by rw [ENNReal.ofReal_ne_zero_iff]; linarith
  have hpT : ENNReal.ofReal s ≠ ⊤ := ENNReal.ofReal_ne_top
  have hgm : ∀ n, Measurable[ℱ n] (condExp (ℱ n) μ f) :=
    fun n => (stronglyMeasurable_condExp (m := ℱ n)).measurable
  have hGm : Measurable (fun ω => ⨆ N, Vtr (fun n => condExp (ℱ n) μ f) s N ω) :=
    Measurable.iSup (fun N => measurable_Vtr ℱ _ hgm s N)
  have hVm := (measurable_iSup_variation (fun n => condExp (ℱ n) μ f) hs0
    (fun N => measurable_Vtr ℱ _ hgm s N)).aestronglyMeasurable (μ := μ)
  have h1 : eLpNorm (fun ω => ⨆ (u : {u : ℕ → ℕ // StrictMono u}) (J : ℕ),
        (∑ j ∈ Finset.range J,
          |(condExp (ℱ (u.1 (j+1))) μ f) ω - (condExp (ℱ (u.1 j)) μ f) ω| ^ s) ^ (1 / s))
      (ENNReal.ofReal s) μ
      = (∫⁻ ω, ‖(⨆ (u : {u : ℕ → ℕ // StrictMono u}) (J : ℕ),
          (∑ j ∈ Finset.range J,
            |(condExp (ℱ (u.1 (j+1))) μ f) ω - (condExp (ℱ (u.1 j)) μ f) ω| ^ s) ^ (1 / s))‖ₑ^(s)
        ∂μ)^(1/s) := by
    have key := Commons.Analysis.MeasureTheory.eLpNorm_rpow_toReal (μ := μ)
      (p := ENNReal.ofReal s)
      (f := fun ω => ⨆ (u : {u : ℕ → ℕ // StrictMono u}) (J : ℕ),
        (∑ j ∈ Finset.range J,
          |(condExp (ℱ (u.1 (j+1))) μ f) ω - (condExp (ℱ (u.1 j)) μ f) ω| ^ s) ^ (1 / s))
      hp0 hpT hVm
    rw [show eLpNorm (fun ω => ⨆ (u : {u : ℕ → ℕ // StrictMono u}) (J : ℕ),
        (∑ j ∈ Finset.range J,
          |(condExp (ℱ (u.1 (j+1))) μ f) ω - (condExp (ℱ (u.1 j)) μ f) ω| ^ s) ^ (1 / s))
        (ENNReal.ofReal s) μ
        = ((eLpNorm (fun ω => ⨆ (u : {u : ℕ → ℕ // StrictMono u}) (J : ℕ),
          (∑ j ∈ Finset.range J,
            |(condExp (ℱ (u.1 (j+1))) μ f) ω - (condExp (ℱ (u.1 j)) μ f) ω| ^ s) ^ (1 / s))
          (ENNReal.ofReal s) μ)^(s))^(1/s) from by
      rw [← ENNReal.rpow_mul, mul_one_div, div_self (ne_of_gt hs0), ENNReal.rpow_one]]
    rw [ENNReal.toReal_ofReal hs0.le] at key
    rw [key]
  have h2 : eLpNorm (fun ω => ⨆ N, Vtr (fun n => condExp (ℱ n) μ f) s N ω)
      (ENNReal.ofReal s) μ
      = (∫⁻ ω, (⨆ N, Vtr (fun n => condExp (ℱ n) μ f) s N ω)^(s) ∂μ)^(1/s) := by
    have key := Commons.Analysis.MeasureTheory.eLpNorm_rpow_toReal (μ := μ)
      (p := ENNReal.ofReal s)
      (f := fun ω => ⨆ N, Vtr (fun n => condExp (ℱ n) μ f) s N ω) hp0 hpT
      hGm.aestronglyMeasurable
    rw [show eLpNorm (fun ω => ⨆ N, Vtr (fun n => condExp (ℱ n) μ f) s N ω)
        (ENNReal.ofReal s) μ
        = ((eLpNorm (fun ω => ⨆ N, Vtr (fun n => condExp (ℱ n) μ f) s N ω)
          (ENNReal.ofReal s) μ)^(s))^(1/s) from by
      rw [← ENNReal.rpow_mul, mul_one_div, div_self (ne_of_gt hs0), ENNReal.rpow_one]]
    rw [ENNReal.toReal_ofReal hs0.le] at key
    simp only [enorm_eq_self] at key
    rw [key]
  rw [h1, h2]
  refine ENNReal.rpow_le_rpow (lintegral_mono (fun ω =>
    ENNReal.rpow_le_rpow (pointwise_bound ℱ f s ω) (by positivity))) (by positivity)


end Final


section Assembly

lemma bdgZZ_bound {s : ℝ} (hs2 : 2 < s) (hs3 : s ≤ 3) : bdgZZ s ≤ 10^4/(s-2) := by
  have hpos : 0 < s - 2 := by linarith
  have h4 : s/2 - 1 = (s-2)/2 := by ring
  have hT : (0:ℝ) < (2:ℝ)^(s/2-1) := Real.rpow_pos_of_pos (by norm_num) _
  have h3 : (2:ℝ)^(s/2-1) ≤ 2 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
      (by linarith : s/2 - 1 ≤ 1)
    simpa using h
  have h1 : s/2 ≤ 2 := by linarith
  have hden : 0 < s/2 - 1 := by linarith
  have hkey : (2:ℝ)^(s/2-1) / (s/2-1) ≤ 2 / ((s-2)/2) := by
    rw [div_le_div_iff₀ hden (by linarith : (0:ℝ) < (s-2)/2)]
    have hc : (2:ℝ) * (s/2-1) = s - 2 := by rw [h4]; ring
    rw [hc]; nlinarith [h3, hT, hpos]
  have hA : bdgA s ≤ 80/(s-2) := by
    rw [bdgA]
    calc s/2 * (10 * ((2:ℝ)^(s/2-1) / (s/2-1))) ≤ 2 * (10 * (2 / ((s-2)/2))) := by
          refine mul_le_mul h1 (mul_le_mul_of_nonneg_left hkey (by norm_num))
            (by positivity) (by norm_num)
      _ ≤ 80/(s-2) := by
          have hc : 2/((s-2)/2) = 4/(s-2) := by
            have h : (s-2) ≠ 0 := ne_of_gt hpos
            field_simp
            ring
          rw [hc]
          have h2c : 2 * (10 * (4/(s-2))) = 80/(s-2) := by field_simp; ring
          rw [h2c]
  have h5 : s/(s-1) ≤ 3 := by
    rw [div_le_iff₀ (by linarith : (0:ℝ) < s-1)]; linarith
  have h0 : 0 ≤ s/(s-1) := div_nonneg (by linarith) (by linarith)
  have hB : (bdgB s)^2 ≤ 9 := by
    rw [bdgB]
    have h := mul_self_le_mul_self h0 h5
    calc (s/(s-1))^2 = s/(s-1) * (s/(s-1)) := by ring
      _ ≤ 3 * 3 := h
      _ = 9 := by norm_num
  rw [bdgZZ]
  calc bdgA s * (bdgB s)^2 ≤ (80/(s-2)) * 9 :=
        mul_le_mul hA hB (sq_nonneg _) (by positivity)
    _ ≤ 10^4/(s-2) := by
        rw [div_mul_eq_mul_div, div_le_div_iff₀ hpos hpos]
        linarith

lemma geomc_bound {s : ℝ} (hs2 : 2 < s) : 2/((s-2)*Real.log 2) ≤ 10^4/(s-2) := by
  have hpos : 0 < s - 2 := by linarith
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlog' : (0:ℝ) < Real.log 2 := hlog
  have h2 : (2:ℝ) ≤ 10^4 * Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  rw [div_le_div_iff₀ (by positivity) hpos]
  calc (2:ℝ) * (s-2) ≤ (10^4 * Real.log 2) * (s-2) :=
        mul_le_mul_of_nonneg_right h2 hpos.le
    _ = 10^4 * ((s-2) * Real.log 2) := by ring

set_option maxHeartbeats 800000 in
theorem lepingle_variation_ls :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type*} {m : MeasurableSpace Ω} (μ : Measure Ω)
      [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m) (s : ℝ) (hs : 2 < s) (hs3 : s ≤ 3)
      (f : Ω → ℝ), MemLp f (ENNReal.ofReal s) μ →
      eLpNorm (fun ω => ⨆ (u : {u : ℕ → ℕ // StrictMono u}) (J : ℕ),
        (Finset.sum (Finset.range J) (fun j =>
          |(condExp (ℱ (u.1 (j + 1))) μ f) ω - (condExp (ℱ (u.1 j)) μ f) ω| ^ s)) ^ (1 / s))
        (ENNReal.ofReal s) μ
        ≤ ENNReal.ofReal (C / (s - 2)) * eLpNorm f (ENNReal.ofReal s) μ := by
  refine ⟨10^6, by norm_num, ?_⟩
  intro Ω m μ _ ℱ s hs hs3 f hf
  have hs0 : 0 < s := by linarith
  have hpos : 0 < s - 2 := by linarith
  have ha : 0 ≤ 2/((s-2)*Real.log 2) := by
    apply div_nonneg (by norm_num)
    exact mul_nonneg hpos.le (Real.log_pos one_lt_two).le
  have hb : 0 ≤ bdgZZ s := bdgZZ_nonneg hs
  have hB1 : (ENNReal.ofReal (2/((s-2)*Real.log 2)) * ENNReal.ofReal (bdgZZ s))^(1/2 : ℝ)
      ≤ ENNReal.ofReal (10^4/(s-2)) := by
    have h1 : 2/((s-2)*Real.log 2) * bdgZZ s ≤ (10^4/(s-2))^2 := by
      refine le_trans (mul_le_mul (geomc_bound hs) (bdgZZ_bound hs hs3) hb (by positivity)) ?_
      rw [div_mul_div_comm]
      rw [show (10^4/(s-2))^2 = 10^4*10^4/((s-2)*(s-2)) by field_simp]
    calc (ENNReal.ofReal (2/((s-2)*Real.log 2)) * ENNReal.ofReal (bdgZZ s))^(1/2 : ℝ)
        = (ENNReal.ofReal (2/((s-2)*Real.log 2) * bdgZZ s))^(1/2 : ℝ) := by
          rw [ENNReal.ofReal_mul ha]
      _ = ENNReal.ofReal ((2/((s-2)*Real.log 2) * bdgZZ s)^(1/2 : ℝ)) :=
          ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)
      _ ≤ ENNReal.ofReal (10^4/(s-2)) := by
          refine ENNReal.ofReal_le_ofReal ?_
          calc (2/((s-2)*Real.log 2) * bdgZZ s)^(1/2 : ℝ)
              = Real.sqrt (2/((s-2)*Real.log 2) * bdgZZ s) := (Real.sqrt_eq_rpow _).symm
            _ ≤ Real.sqrt ((10^4/(s-2))^2) := Real.sqrt_le_sqrt h1
            _ = 10^4/(s-2) := Real.sqrt_sq (by positivity)
  have h8 : (8:ℝ≥0∞) * ENNReal.ofReal (10^4/(s-2)) ≤ ENNReal.ofReal (10^6/(s-2)) := by
    rw [show (8:ℝ≥0∞) = ENNReal.ofReal 8 by norm_num,
      ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 8)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [show (8:ℝ) * (10^4/(s-2)) = 8*10^4/(s-2) by ring]
    rw [div_le_div_iff₀ hpos hpos]
    linarith
  refine le_trans (statement_le ℱ f hs0 hf) ?_
  refine le_trans (eLpNorm_Vinf_le ℱ f hs0 hs hs3 hf) ?_
  calc 8 * ((ENNReal.ofReal (2/((s-2)*Real.log 2)) * ENNReal.ofReal (bdgZZ s))^(1/2 : ℝ)
        * eLpNorm f (ENNReal.ofReal s) μ)
      ≤ 8 * (ENNReal.ofReal (10^4/(s-2)) * eLpNorm f (ENNReal.ofReal s) μ) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hB1 zero_le) (by norm_num)
    _ = 8 * ENNReal.ofReal (10^4/(s-2)) * eLpNorm f (ENNReal.ofReal s) μ := by ring
    _ ≤ ENNReal.ofReal (10^6/(s-2)) * eLpNorm f (ENNReal.ofReal s) μ :=
        mul_le_mul_of_nonneg_right h8 zero_le


end Assembly

end Commons.Analysis.Probability