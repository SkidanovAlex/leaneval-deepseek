import Mathlib
import Submission.Work.FunctionalEquations.Gap
import Submission.Work.FunctionalEquations.CoefficientValuePattern
import Submission.Work.FunctionalEquations.GaussianRadialDeriv
import Submission.Work.FunctionalEquations.ReconstructionGaussianGen
import Submission.Work.FunctionalEquations.GenSummableMulExpNeg

namespace Work.FunctionalEquations

open LeanEval.Analysis.CKMRVInterpolation Work.Core Work.FE Filter Topology
open scoped FourierTransform SchwartzMap

noncomputable section

/-! ## Summability and bounds for a Dirichlet series with polynomially bounded coefficients -/

private lemma summable_nat_add_one_pow_mul_geometric' {N : ℕ} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    Summable fun n : ℕ => ((n : ℝ) + 1) ^ N * t ^ n := by
  have htabs : ‖t‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg ht0]; exact ht1
  have hgeom : Summable fun n : ℕ => (n : ℝ) ^ N * t ^ n :=
    summable_pow_mul_geometric_of_norm_lt_one N htabs
  have hgeom1 : Summable fun n : ℕ => t ^ n := summable_geometric_of_norm_lt_one htabs
  have hmain : Summable fun n : ℕ => (2 : ℝ) ^ N * (((n : ℝ) ^ N * t ^ n) + t ^ n) :=
    (hgeom.add hgeom1).mul_left _
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hmain
  have hb : ((n : ℝ) + 1) ^ N ≤ (2 : ℝ) ^ N * ((n : ℝ) ^ N + 1) := by
    have hmax : ((n : ℝ) + 1) ≤ 2 * max (n : ℝ) 1 := by
      rcases le_or_gt 1 (n : ℝ) with hh | hh
      · rw [max_eq_left hh]; linarith
      · rw [max_eq_right hh.le]; linarith
    have hstep : ((n : ℝ) + 1) ^ N ≤ (2 * max (n : ℝ) 1) ^ N :=
      pow_le_pow_left₀ (by positivity) hmax N
    have hmaxN : (max (n : ℝ) 1) ^ N ≤ (n : ℝ) ^ N + 1 := by
      rcases le_or_gt 1 (n : ℝ) with hh | hh
      · rw [max_eq_left hh]
        have : (0 : ℝ) ≤ (n : ℝ) ^ N := by positivity
        linarith
      · rw [max_eq_right hh.le]; simp
    calc ((n : ℝ) + 1) ^ N ≤ (2 * max (n : ℝ) 1) ^ N := hstep
      _ = (2 : ℝ) ^ N * (max (n : ℝ) 1) ^ N := by rw [mul_pow]
      _ ≤ (2 : ℝ) ^ N * ((n : ℝ) ^ N + 1) :=
          mul_le_mul_of_nonneg_left hmaxN (by positivity)
  calc ((n : ℝ) + 1) ^ N * t ^ n ≤ ((2 : ℝ) ^ N * ((n : ℝ) ^ N + 1)) * t ^ n :=
        mul_le_mul_of_nonneg_right hb (by positivity)
    _ = (2 : ℝ) ^ N * (((n : ℝ) ^ N * t ^ n) + t ^ n) := by ring

lemma summable_poly_exp_neg {k₀ : ℕ} (C : ℝ) (N : ℕ) {y : ℝ} (hy : 0 < y) :
    Summable fun m : Set.Ici k₀ =>
      C * ((m.1:ℝ)+1)^N * Real.exp (-(2 * Real.pi * y * (m.1:ℝ))) := by
  set t : ℝ := Real.exp (-(2*Real.pi*y)) with ht
  have ht0 : 0 < t := Real.exp_pos _
  have ht1 : t < 1 := by rw [ht, Real.exp_lt_one_iff]; nlinarith [Real.pi_pos, hy]
  have hw : Summable fun m : Set.Ici k₀ => ((m.1:ℝ)+1)^N * t^(m.1) :=
    (summable_nat_add_one_pow_mul_geometric' ht0.le ht1).subtype _
  refine (hw.mul_left C).congr fun m => ?_
  show C * (((m.1:ℝ)+1)^N * t^(m.1))
      = C * ((m.1:ℝ)+1)^N * Real.exp (-(2 * Real.pi * y * (m.1:ℝ)))
  rw [ht, ← Real.exp_nat_mul]
  ring_nf

/-- The function witnessing the decay `o(e^{-2π(k₀-1) Im τ})` of a Dirichlet series
indexed from `k₀` with polynomially bounded coefficients. -/
def dirichletDecayBound (k₀ : ℕ) (C : ℝ) (N : ℕ) (y : ℝ) : ℝ :=
  Real.exp (2 * Real.pi * ((k₀:ℝ) - 1) * y) *
    ∑' m : Set.Ici k₀, C * ((m.1:ℝ)+1)^N * Real.exp (-(2 * Real.pi * y * (m.1:ℝ)))

lemma dirichletWeight_sum_le {k₀ : ℕ} (C : ℝ) (N : ℕ) (hC : 0 ≤ C) {y : ℝ} (hy : 1 ≤ y) :
    (∑' m : Set.Ici k₀, C * ((m.1:ℝ)+1)^N * Real.exp (-(2*Real.pi*y*(m.1:ℝ))))
      ≤ Real.exp (-(2*Real.pi*(k₀:ℝ)*y)) *
        ∑' m : Set.Ici k₀, C * ((m.1:ℝ)+1)^N * Real.exp (-(2*Real.pi*((m.1:ℝ) - (k₀:ℝ)))) := by
  have hsum_f : Summable fun m : Set.Ici k₀ =>
      C * ((m.1:ℝ)+1)^N * Real.exp (-(2*Real.pi*y*(m.1:ℝ))) :=
    summable_poly_exp_neg C N (by linarith)
  have hsum_inner : Summable fun m : Set.Ici k₀ =>
      C * ((m.1:ℝ)+1)^N * Real.exp (-(2*Real.pi*((m.1:ℝ) - (k₀:ℝ)))) := by
    have h := summable_poly_exp_neg (C * Real.exp (2*Real.pi*(k₀:ℝ))) N (k₀ := k₀)
      (by norm_num : (0:ℝ) < 1)
    refine h.congr fun m => ?_
    have e1 : Real.exp (-(2*Real.pi*((m.1:ℝ) - (k₀:ℝ))))
        = Real.exp (2*Real.pi*(k₀:ℝ)) * Real.exp (-(2*Real.pi*1*(m.1:ℝ))) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [e1]; ring
  have hsum_g : Summable fun m : Set.Ici k₀ =>
      Real.exp (-(2*Real.pi*(k₀:ℝ)*y)) *
        (C * ((m.1:ℝ)+1)^N * Real.exp (-(2*Real.pi*((m.1:ℝ) - (k₀:ℝ))))) :=
    hsum_inner.mul_left _
  have hmain : (∑' m : Set.Ici k₀, C * ((m.1:ℝ)+1)^N * Real.exp (-(2*Real.pi*y*(m.1:ℝ))))
      ≤ ∑' m : Set.Ici k₀, Real.exp (-(2*Real.pi*(k₀:ℝ)*y)) *
        (C * ((m.1:ℝ)+1)^N * Real.exp (-(2*Real.pi*((m.1:ℝ) - (k₀:ℝ))))) := by
    refine Summable.tsum_le_tsum (fun m => ?_) hsum_f hsum_g
    have hexp : -(2*Real.pi*y*(m.1:ℝ))
        ≤ -(2*Real.pi*(k₀:ℝ)*y) + -(2*Real.pi*((m.1:ℝ) - (k₀:ℝ))) := by
      have hm : (k₀:ℝ) ≤ (m.1:ℝ) := by exact_mod_cast m.2
      nlinarith [Real.pi_pos, mul_nonneg (sub_nonneg.mpr hy) (sub_nonneg.mpr hm)]
    calc C * ((m.1:ℝ)+1)^N * Real.exp (-(2*Real.pi*y*(m.1:ℝ)))
        = (C * ((m.1:ℝ)+1)^N) * Real.exp (-(2*Real.pi*y*(m.1:ℝ))) := by ring
      _ ≤ (C * ((m.1:ℝ)+1)^N) *
            Real.exp (-(2*Real.pi*(k₀:ℝ)*y) + -(2*Real.pi*((m.1:ℝ) - (k₀:ℝ)))) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by positivity)
      _ = Real.exp (-(2*Real.pi*(k₀:ℝ)*y)) *
          (C * ((m.1:ℝ)+1)^N * Real.exp (-(2*Real.pi*((m.1:ℝ) - (k₀:ℝ))))) := by
          rw [Real.exp_add]; ring
  rwa [hsum_inner.tsum_mul_left] at hmain

lemma tendsto_exp_neg_lin (a : ℝ) (ha : 0 < a) :
    Tendsto (fun y : ℝ => Real.exp (-(a * y))) atTop (nhds 0) := by
  have h3 : Filter.Tendsto (fun y : ℝ => Real.exp (a*y)) Filter.atTop Filter.atTop :=
    Real.tendsto_exp_atTop.comp (Filter.Tendsto.const_mul_atTop ha Filter.tendsto_id)
  have h4 := h3.inv_tendsto_atTop
  refine h4.congr (fun y => ?_)
  rw [Pi.inv_apply, Real.exp_neg]

/-- **Decay of a Dirichlet series indexed from `k₀`.**  If `‖c m‖ ≤ C (m+1)^N` then the
series `∑_m c_m e^{2πi m τ}` is `o(e^{-2π(k₀-1) Im τ})` in the strip `-1 ≤ Re τ ≤ 1`. -/
theorem tendsToZeroInStrip_dirichlet {k₀ : ℕ} {c : Set.Ici k₀ → ℂ} {C : ℝ} {N : ℕ}
    (hC : 0 ≤ C) (h : ∀ m, ‖c m‖ ≤ C * ((m.1:ℝ)+1)^N) (n : ℕ) [NeZero n] :
    TendsToZeroInStrip n ((k₀:ℝ) - 1)
      (fun τ (_ : E n) => ∑' m : Set.Ici k₀, c m * dirichletTerm m.1 τ) := by
  intro x
  refine ⟨dirichletDecayBound k₀ C N, ?htend, ?hbound⟩
  · set T : ℝ := ∑' m : Set.Ici k₀,
      C * ((m.1:ℝ)+1)^N * Real.exp (-(2*Real.pi*((m.1:ℝ) - (k₀:ℝ)))) with hT
    have hlim : Tendsto (fun y : ℝ => T * Real.exp (-(2*Real.pi*y))) atTop (nhds 0) := by
      simpa using (tendsto_exp_neg_lin (2*Real.pi) (by positivity)).const_mul T
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
    · filter_upwards [eventually_ge_atTop (1:ℝ)] with y hy
      exact mul_nonneg (Real.exp_nonneg _) (tsum_nonneg (fun m => by positivity))
    · filter_upwards [eventually_ge_atTop (1:ℝ)] with y hy
      simp only [dirichletDecayBound]
      have hb := dirichletWeight_sum_le (k₀ := k₀) C N hC hy
      have hE : Real.exp (2 * Real.pi * ((k₀:ℝ)-1) * y) * Real.exp (-(2*Real.pi*(k₀:ℝ)*y))
          = Real.exp (-(2*Real.pi*y)) := by
        rw [← Real.exp_add]; congr 1; ring
      calc Real.exp (2 * Real.pi * ((k₀:ℝ)-1) * y) *
            (∑' m : Set.Ici k₀, C*((m.1:ℝ)+1)^N * Real.exp (-(2*Real.pi*y*(m.1:ℝ))))
          ≤ Real.exp (2 * Real.pi * ((k₀:ℝ)-1) * y) * (Real.exp (-(2*Real.pi*(k₀:ℝ)*y)) * T) :=
            mul_le_mul_of_nonneg_left hb (Real.exp_nonneg _)
        _ = (Real.exp (2 * Real.pi * ((k₀:ℝ)-1) * y) * Real.exp (-(2*Real.pi*(k₀:ℝ)*y))) * T :=
            (mul_assoc _ _ _).symm
        _ = Real.exp (-(2*Real.pi*y)) * T := by rw [hE]
        _ = T * Real.exp (-(2*Real.pi*y)) := mul_comm _ _
  · intro τ hτ _ _
    have hsumm : Summable fun m : Set.Ici k₀ => c m * dirichletTerm m.1 τ :=
      summable_mul_dirichletTerm_gen hC h τ hτ
    have hnorms : Summable fun m : Set.Ici k₀ => ‖c m * dirichletTerm m.1 τ‖ := hsumm.norm
    have hS : ‖∑' m : Set.Ici k₀, c m * dirichletTerm m.1 τ‖
        ≤ ∑' m : Set.Ici k₀, C * ((m.1:ℝ)+1)^N * Real.exp (-(2*Real.pi*τ.im*(m.1:ℝ))) := by
      have hnorm_eq : (fun m : Set.Ici k₀ => ‖c m * dirichletTerm m.1 τ‖)
          = fun m : Set.Ici k₀ => ‖c m‖ * Real.exp (-(2*Real.pi*τ.im*(m.1:ℝ))) := by
        funext m; rw [norm_mul, norm_dirichletTerm]
      have hsumm2 : Summable fun m : Set.Ici k₀ =>
          ‖c m‖ * Real.exp (-(2*Real.pi*τ.im*(m.1:ℝ))) :=
        hnorms.congr (fun m => by rw [norm_mul, norm_dirichletTerm])
      have hsumm3 : Summable fun m : Set.Ici k₀ =>
          C * ((m.1:ℝ)+1)^N * Real.exp (-(2*Real.pi*τ.im*(m.1:ℝ))) :=
        summable_poly_exp_neg C N hτ
      calc ‖∑' m : Set.Ici k₀, c m * dirichletTerm m.1 τ‖
          ≤ ∑' m : Set.Ici k₀, ‖c m * dirichletTerm m.1 τ‖ := norm_tsum_le_tsum_norm hnorms
        _ = ∑' m : Set.Ici k₀, ‖c m‖ * Real.exp (-(2*Real.pi*τ.im*(m.1:ℝ))) := by rw [hnorm_eq]
        _ ≤ ∑' m : Set.Ici k₀, C * ((m.1:ℝ)+1)^N * Real.exp (-(2*Real.pi*τ.im*(m.1:ℝ))) :=
            Summable.tsum_le_tsum (fun m => by
              exact mul_le_mul_of_nonneg_right (h m) (Real.exp_nonneg _)) hsumm2 hsumm3
    simp only [dirichletDecayBound]
    have hfac : Real.exp (2*Real.pi*((k₀:ℝ)-1)*τ.im) *
        Real.exp (-(2*Real.pi*((k₀:ℝ)-1)*τ.im)) = 1 := by
      rw [← Real.exp_add]; ring_nf; simp
    calc ‖∑' m : Set.Ici k₀, c m * dirichletTerm m.1 τ‖
        ≤ _ := hS
      _ = (Real.exp (2*Real.pi*((k₀:ℝ)-1)*τ.im) *
            (∑' m : Set.Ici k₀, C*((m.1:ℝ)+1)^N * Real.exp (-(2*Real.pi*τ.im*(m.1:ℝ))))) *
          Real.exp (-(2*Real.pi*((k₀:ℝ)-1)*τ.im)) := by
            rw [show (Real.exp (2*Real.pi*((k₀:ℝ)-1)*τ.im) *
                  (∑' m : Set.Ici k₀, C*((m.1:ℝ)+1)^N * Real.exp (-(2*Real.pi*τ.im*(m.1:ℝ))))) *
                Real.exp (-(2*Real.pi*((k₀:ℝ)-1)*τ.im))
              = (Real.exp (2*Real.pi*((k₀:ℝ)-1)*τ.im) *
                  Real.exp (-(2*Real.pi*((k₀:ℝ)-1)*τ.im))) *
                (∑' m : Set.Ici k₀, C*((m.1:ℝ)+1)^N * Real.exp (-(2*Real.pi*τ.im*(m.1:ℝ)))) from by ring]
            rw [hfac, one_mul]

/-! ## Closure properties of `TendsToZeroInStrip` -/

lemma TendsToZeroInStrip.add {n : ℕ} [NeZero n] {c : ℝ} {g g' : ℂ → E n → ℂ}
    (hg : TendsToZeroInStrip n c g) (hg' : TendsToZeroInStrip n c g') :
    TendsToZeroInStrip n c (fun τ x => g τ x + g' τ x) := by
  intro x
  obtain ⟨φ, hφ, hb⟩ := hg x
  obtain ⟨φ', hφ', hb'⟩ := hg' x
  refine ⟨fun y => φ y + φ' y, ?_, fun τ hτ h1 h2 => ?_⟩
  · simpa only [add_zero] using hφ.add hφ'
  · rw [add_mul]
    exact le_trans (norm_add_le _ _) (add_le_add (hb τ hτ h1 h2) (hb' τ hτ h1 h2))

lemma TendsToZeroInStrip.congr {n : ℕ} [NeZero n] {c : ℝ} {g g' : ℂ → E n → ℂ}
    (hg : TendsToZeroInStrip n c g) (h : ∀ τ x, 0 < τ.im → g τ x = g' τ x) :
    TendsToZeroInStrip n c g' := by
  intro x
  obtain ⟨φ, hφ, hb⟩ := hg x
  exact ⟨φ, hφ, fun τ hτ h1 h2 => by rw [← h τ x hτ]; exact hb τ hτ h1 h2⟩

/-! ## The decay lemma with a prefactor -/

lemma tendsto_one_add_pow_mul_exp_neg (d : ℕ) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun y : ℝ => (1+y)^d * Real.exp (-(a*y))) atTop (nhds 0) := by
  have hb : (0:ℝ) < a/2 := by linarith
  have hcomp : Tendsto (fun y : ℝ => ((a/2)*y)^d * Real.exp (-((a/2)*y))) atTop (nhds 0) :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero d).comp
      (Filter.Tendsto.const_mul_atTop hb Filter.tendsto_id)
  have hv0 : Tendsto (fun y : ℝ =>
      ((a/2)⁻¹)^d * (((a/2)*y)^d * Real.exp (-((a/2)*y)))) atTop (nhds 0) := by
    simpa only [mul_zero] using hcomp.const_mul (((a/2)⁻¹)^d)
  have hv : Tendsto (fun y : ℝ => y^d * Real.exp (-((a/2)*y))) atTop (nhds 0) := by
    refine hv0.congr (fun y => ?_)
    have h1 : (a/2)⁻¹ ^ d * (a/2)^d = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ (ne_of_gt hb), one_pow]
    rw [mul_pow]
    calc ((a/2)⁻¹)^d * (((a/2)^d * y^d) * Real.exp (-((a/2)*y)))
        = ((a/2)⁻¹^d * (a/2)^d) * (y^d * Real.exp (-((a/2)*y))) := by ring
      _ = y^d * Real.exp (-((a/2)*y)) := by rw [h1, one_mul]
  have hmain : Tendsto (fun y : ℝ => 2^d * (y^d * Real.exp (-((a/2)*y)))) atTop (nhds 0) := by
    simpa only [mul_zero] using hv.const_mul (2^d)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hmain ?_ ?_
  · filter_upwards [eventually_ge_atTop (0:ℝ)] with y hy
    exact mul_nonneg (pow_nonneg (by linarith) _) (Real.exp_nonneg _)
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with y hy
    have h1 : (1+y)^d ≤ 2^d * y^d := by
      have h2 : 1 + y ≤ 2*y := by linarith
      calc (1+y)^d ≤ (2*y)^d := pow_le_pow_left₀ (by positivity) h2 d
        _ = 2^d * y^d := by rw [mul_pow]
    have h3 : Real.exp (-(a*y)) ≤ Real.exp (-((a/2)*y)) := by
      rw [Real.exp_le_exp]; nlinarith
    calc (1+y)^d * Real.exp (-(a*y)) ≤ (2^d * y^d) * Real.exp (-((a/2)*y)) :=
          mul_le_mul h1 h3 (Real.exp_nonneg _) (by positivity)
      _ = 2^d * (y^d * Real.exp (-((a/2)*y))) := by ring

/-- **Decay of a Dirichlet series with a prefactor.**  If `‖c m‖ ≤ C (m+1)^N` and `P` is
bounded by `(1 + Im τ)^d` in the strip, then `P(τ) ∑_m c_m e^{2πi m τ}` is
`o(e^{-2π(k₀-1) Im τ})`. -/
theorem tendsToZeroInStrip_dirichlet_poly {k₀ : ℕ} {c : Set.Ici k₀ → ℂ} {C : ℝ} {N d : ℕ}
    (hC : 0 ≤ C) (h : ∀ m, ‖c m‖ ≤ C * ((m.1:ℝ)+1)^N) (P : ℂ → ℂ)
    (hP : ∀ τ : ℂ, 0 < τ.im → -1 ≤ τ.re → τ.re ≤ 1 → ‖P τ‖ ≤ (1 + τ.im)^d) (n : ℕ) [NeZero n] :
    TendsToZeroInStrip n ((k₀:ℝ) - 1)
      (fun τ (_ : E n) => P τ * ∑' m : Set.Ici k₀, c m * dirichletTerm m.1 τ) := by
  intro x
  refine ⟨fun y => (1+y)^d * dirichletDecayBound k₀ C N y, ?htend, ?hbound⟩
  · set T : ℝ := ∑' m : Set.Ici k₀,
      C * ((m.1:ℝ)+1)^N * Real.exp (-(2*Real.pi*((m.1:ℝ) - (k₀:ℝ)))) with hT
    have hlim : Tendsto (fun y : ℝ => T * ((1+y)^d * Real.exp (-(2*Real.pi*y))))
        atTop (nhds 0) := by
      simpa only [mul_zero] using
        (tendsto_one_add_pow_mul_exp_neg d (a := 2*Real.pi) (by positivity)).const_mul T
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
    · filter_upwards [eventually_ge_atTop (1:ℝ)] with y hy
      exact mul_nonneg (pow_nonneg (by linarith) _)
        (mul_nonneg (Real.exp_nonneg _) (tsum_nonneg (fun m => by positivity)))
    · filter_upwards [eventually_ge_atTop (1:ℝ)] with y hy
      simp only [dirichletDecayBound]
      have hb := dirichletWeight_sum_le (k₀ := k₀) C N hC hy
      have hE : Real.exp (2 * Real.pi * ((k₀:ℝ)-1) * y) * Real.exp (-(2*Real.pi*(k₀:ℝ)*y))
          = Real.exp (-(2*Real.pi*y)) := by
        rw [← Real.exp_add]; congr 1; ring
      calc (1+y)^d * (Real.exp (2 * Real.pi * ((k₀:ℝ)-1) * y) *
              (∑' m : Set.Ici k₀, C*((m.1:ℝ)+1)^N * Real.exp (-(2*Real.pi*y*(m.1:ℝ)))))
          ≤ (1+y)^d * (Real.exp (2 * Real.pi * ((k₀:ℝ)-1) * y) *
              (Real.exp (-(2*Real.pi*(k₀:ℝ)*y)) * T)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb (Real.exp_nonneg _))
              (pow_nonneg (by linarith) _)
        _ = ((1+y)^d * (Real.exp (2 * Real.pi * ((k₀:ℝ)-1) * y) *
              Real.exp (-(2*Real.pi*(k₀:ℝ)*y)))) * T := by ring
        _ = ((1+y)^d * Real.exp (-(2*Real.pi*y))) * T := by rw [hE]
        _ = T * ((1+y)^d * Real.exp (-(2*Real.pi*y))) := by ring
  · intro τ hτ hre1 hre2
    have hsumm : Summable fun m : Set.Ici k₀ => c m * dirichletTerm m.1 τ :=
      summable_mul_dirichletTerm_gen hC h τ hτ
    have hnorms : Summable fun m : Set.Ici k₀ => ‖c m * dirichletTerm m.1 τ‖ := hsumm.norm
    have hS : ‖∑' m : Set.Ici k₀, c m * dirichletTerm m.1 τ‖
        ≤ ∑' m : Set.Ici k₀, C * ((m.1:ℝ)+1)^N * Real.exp (-(2*Real.pi*τ.im*(m.1:ℝ))) := by
      have hnorm_eq : (fun m : Set.Ici k₀ => ‖c m * dirichletTerm m.1 τ‖)
          = fun m : Set.Ici k₀ => ‖c m‖ * Real.exp (-(2*Real.pi*τ.im*(m.1:ℝ))) := by
        funext m; rw [norm_mul, norm_dirichletTerm]
      have hsumm2 : Summable fun m : Set.Ici k₀ =>
          ‖c m‖ * Real.exp (-(2*Real.pi*τ.im*(m.1:ℝ))) :=
        hnorms.congr (fun m => by rw [norm_mul, norm_dirichletTerm])
      have hsumm3 : Summable fun m : Set.Ici k₀ =>
          C * ((m.1:ℝ)+1)^N * Real.exp (-(2*Real.pi*τ.im*(m.1:ℝ))) :=
        summable_poly_exp_neg C N hτ
      calc ‖∑' m : Set.Ici k₀, c m * dirichletTerm m.1 τ‖
          ≤ ∑' m : Set.Ici k₀, ‖c m * dirichletTerm m.1 τ‖ := norm_tsum_le_tsum_norm hnorms
        _ = ∑' m : Set.Ici k₀, ‖c m‖ * Real.exp (-(2*Real.pi*τ.im*(m.1:ℝ))) := by rw [hnorm_eq]
        _ ≤ ∑' m : Set.Ici k₀, C * ((m.1:ℝ)+1)^N * Real.exp (-(2*Real.pi*τ.im*(m.1:ℝ))) :=
            Summable.tsum_le_tsum (fun m => by
              exact mul_le_mul_of_nonneg_right (h m) (Real.exp_nonneg _)) hsumm2 hsumm3
    have hnorm_le : ‖P τ * ∑' m : Set.Ici k₀, c m * dirichletTerm m.1 τ‖
        ≤ (1 + τ.im)^d *
          (∑' m : Set.Ici k₀, C * ((m.1:ℝ)+1)^N * Real.exp (-(2*Real.pi*τ.im*(m.1:ℝ)))) := by
      rw [norm_mul]
      exact mul_le_mul (hP τ hτ hre1 hre2) hS (norm_nonneg _) (pow_nonneg (by linarith) _)
    simp only [dirichletDecayBound]
    have hfac : Real.exp (2*Real.pi*((k₀:ℝ)-1)*τ.im) *
        Real.exp (-(2*Real.pi*((k₀:ℝ)-1)*τ.im)) = 1 := by
      rw [← Real.exp_add]; ring_nf; simp
    calc ‖P τ * ∑' m : Set.Ici k₀, c m * dirichletTerm m.1 τ‖
        ≤ (1 + τ.im)^d *
          (∑' m : Set.Ici k₀, C*((m.1:ℝ)+1)^N * Real.exp (-(2*Real.pi*τ.im*(m.1:ℝ)))) := hnorm_le
      _ = ((1 + τ.im)^d * (Real.exp (2*Real.pi*((k₀:ℝ)-1)*τ.im) *
              (∑' m : Set.Ici k₀, C*((m.1:ℝ)+1)^N * Real.exp (-(2*Real.pi*τ.im*(m.1:ℝ)))))) *
            Real.exp (-(2*Real.pi*((k₀:ℝ)-1)*τ.im)) := by
            rw [show ((1 + τ.im)^d * (Real.exp (2*Real.pi*((k₀:ℝ)-1)*τ.im) * (∑' m : Set.Ici k₀, C*((m.1:ℝ)+1)^N * Real.exp (-(2*Real.pi*τ.im*(m.1:ℝ)))))) *
                  Real.exp (-(2*Real.pi*((k₀:ℝ)-1)*τ.im))
                = (1 + τ.im)^d * ((Real.exp (2*Real.pi*((k₀:ℝ)-1)*τ.im) *
                    Real.exp (-(2*Real.pi*((k₀:ℝ)-1)*τ.im))) * (∑' m : Set.Ici k₀, C*((m.1:ℝ)+1)^N * Real.exp (-(2*Real.pi*τ.im*(m.1:ℝ))))) from by ring]
            rw [hfac, one_mul]

/-! ## The Gaussian at a sample point -/

lemma gaussianFun_samplePoint {n : ℕ} [NeZero n] (τ : ℂ) (m : ℕ) :
    Work.Core.gaussianFun n τ (samplePoint (n := n) (m : ℝ)) = dirichletTerm m τ := by
  rw [Work.Core.gaussianFun]
  have hnorm : ‖samplePoint (n := n) (m : ℝ)‖ = Real.sqrt (2 * (m : ℝ)) := by
    rw [samplePoint, Work.Sampling.realIncl_norm, abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [hnorm, dirichletTerm]
  congr 1
  rw [Real.sq_sqrt (by positivity)]
  push_cast
  ring

private lemma hasDerivAt_gaussianProfile' (c : ℂ) (x : ℝ) :
    HasDerivAt (fun r : ℝ => Complex.exp (c * (r : ℂ) ^ 2))
      (Complex.exp (c * (x : ℂ) ^ 2) * (c * (2 * (x : ℂ)))) x := by
  have h1 : HasDerivAt (fun r : ℝ => (r : ℂ) ^ 2) ((2 : ℂ) * (x : ℂ)) x := by
    have h := (hasDerivAt_pow 2 x).ofReal_comp
    simpa using h
  have h2 : HasDerivAt (fun r : ℝ => c * (r : ℂ) ^ 2) (c * ((2 : ℂ) * (x : ℂ))) x :=
    h1.const_mul c
  simpa using h2.cexp

lemma radialDeriv_gaussianFun_samplePoint {n : ℕ} [NeZero n] (τ : ℂ) (m : ℕ) :
    radialDeriv 1 (Work.Core.gaussianFun n τ) (samplePoint (n := n) (m : ℝ))
      = (2 * (Real.pi : ℂ) * Complex.I * τ * (rate m : ℂ)) * dirichletTerm m τ := by
  have hnorm : ‖samplePoint (n := n) (m : ℝ)‖ = Real.sqrt (2 * (m : ℝ)) := by
    rw [samplePoint, Work.Sampling.realIncl_norm, abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [radialDeriv, iteratedDeriv_one, hnorm]
  have hfun : (fun r : ℝ => Work.Core.gaussianFun n τ (realIncl (n := n) r))
      = fun r : ℝ => Complex.exp ((Real.pi : ℂ) * Complex.I * τ * (r : ℂ) ^ 2) := by
    funext r
    rw [Work.Core.gaussianFun]
    congr 1
    rw [Work.Sampling.realIncl_norm, sq_abs]
    push_cast
    ring
  rw [hfun]
  rw [(hasDerivAt_gaussianProfile' ((Real.pi : ℂ) * Complex.I * τ)
        (Real.sqrt (2 * (m : ℝ)))).deriv]
  have hsq : ((Real.sqrt (2 * (m : ℝ)) : ℂ)) ^ 2 = ((2 * (m : ℝ) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]
  have hexp : Complex.exp ((Real.pi : ℂ) * Complex.I * τ *
        ((Real.sqrt (2 * (m : ℝ)) : ℂ)) ^ 2) = dirichletTerm m τ := by
    rw [hsq, dirichletTerm]
    congr 1
    push_cast
    ring
  rw [hexp, rate]
  ring

/-! ## Differentiability in `τ` -/

lemma differentiable_dirichletTerm (m : ℕ) :
    Differentiable ℂ (fun τ : ℂ => dirichletTerm m τ) := by
  unfold dirichletTerm
  fun_prop

lemma differentiableAt_profile {n : ℕ} [NeZero n] {f : E n → ℂ} (hf : ContDiff ℝ ⊤ f) (x : E n) :
    DifferentiableAt ℝ (fun r : ℝ => f (realIncl (n := n) r)) ‖x‖ := by
  have hd : DifferentiableAt ℝ f (realIncl (n := n) ‖x‖) :=
    (hf.differentiable (by simp)).differentiableAt
  exact hd.comp ‖x‖ (Work.Sampling.hasDerivAt_realIncl (n := n) ‖x‖).differentiableAt

/-! ## Linearity of the first radial derivative -/

lemma radialDeriv_one_add {n : ℕ} [NeZero n] {f g : E n → ℂ} {x : E n}
    (hf : DifferentiableAt ℝ (fun r : ℝ => f (realIncl (n := n) r)) ‖x‖)
    (hg : DifferentiableAt ℝ (fun r : ℝ => g (realIncl (n := n) r)) ‖x‖) :
    radialDeriv 1 (fun y => f y + g y) x = radialDeriv 1 f x + radialDeriv 1 g x := by
  simp only [radialDeriv, iteratedDeriv_one]
  rw [show (fun r : ℝ => (fun y => f y + g y) (realIncl (n := n) r))
      = (fun r : ℝ => f (realIncl (n := n) r)) + (fun r : ℝ => g (realIncl (n := n) r))
      from rfl, deriv_add hf hg]

lemma radialDeriv_one_const_mul {n : ℕ} [NeZero n] (c : ℂ) {f : E n → ℂ} {x : E n}
    (hf : DifferentiableAt ℝ (fun r : ℝ => f (realIncl (n := n) r)) ‖x‖) :
    radialDeriv 1 (fun y => c * f y) x = c * radialDeriv 1 f x := by
  simp only [radialDeriv, iteratedDeriv_one]
  rw [show (fun r : ℝ => (fun y => c * f y) (realIncl (n := n) r))
      = (fun r : ℝ => c * f (realIncl (n := n) r)) from rfl, deriv_const_mul c hf]

/-- If `A - 2 B + C` vanishes identically then the corresponding combination of first
radial derivatives vanishes. -/
lemma radialDeriv_one_combination_eq_zero {n : ℕ} [NeZero n] {A B C : E n → ℂ} {x : E n}
    (hA : DifferentiableAt ℝ (fun r : ℝ => A (realIncl (n := n) r)) ‖x‖)
    (hB : DifferentiableAt ℝ (fun r : ℝ => B (realIncl (n := n) r)) ‖x‖)
    (hC : DifferentiableAt ℝ (fun r : ℝ => C (realIncl (n := n) r)) ‖x‖)
    (hzero : ∀ y, A y - 2 * B y + C y = 0) :
    radialDeriv 1 A x - 2 * radialDeriv 1 B x + radialDeriv 1 C x = 0 := by
  have h2 : DifferentiableAt ℝ (fun r : ℝ => (2 : ℂ) * B (realIncl (n := n) r)) ‖x‖ :=
    hB.const_mul 2
  have h12 : DifferentiableAt ℝ
      ((fun r : ℝ => A (realIncl (n := n) r)) - (fun r : ℝ => 2 * B (realIncl (n := n) r)))
      ‖x‖ := hA.sub h2
  have hcomb : radialDeriv 1 A x - 2 * radialDeriv 1 B x + radialDeriv 1 C x
      = radialDeriv 1 (fun y => A y - 2 * B y + C y) x := by
    simp only [radialDeriv, iteratedDeriv_one]
    rw [show (fun r : ℝ => A (realIncl (n := n) r) - 2 * B (realIncl (n := n) r)
            + C (realIncl (n := n) r))
          = ((fun r : ℝ => A (realIncl (n := n) r))
              - (fun r : ℝ => 2 * B (realIncl (n := n) r)))
              + (fun r : ℝ => C (realIncl (n := n) r)) from rfl]
    rw [deriv_add h12 hC, deriv_sub hA h2, deriv_const_mul 2 hB]
  rw [hcomb, show (fun y : E n => A y - 2 * B y + C y) = fun _ => (0 : ℂ) from funext hzero]
  simp only [radialDeriv, iteratedDeriv_one]
  simp

/-! ## Differentiability of a Dirichlet series on the upper half plane -/

lemma differentiableOn_uHP_of {f : ℂ → ℂ}
    (h : ∀ y₀ : ℝ, 0 < y₀ → DifferentiableOn ℂ f {τ : ℂ | y₀ < τ.im}) :
    DifferentiableOn ℂ f {τ : ℂ | 0 < τ.im} := by
  intro τ hτ
  have hτ' : 0 < τ.im := hτ
  have hy : 0 < τ.im / 2 := by linarith
  have hmem : τ ∈ {z : ℂ | τ.im / 2 < z.im} := by
    simp only [Set.mem_setOf_eq]; linarith
  have hopen : IsOpen {z : ℂ | τ.im / 2 < z.im} :=
    isOpen_lt continuous_const Complex.continuous_im
  exact ((h (τ.im / 2) hy).differentiableAt (hopen.mem_nhds hmem)).differentiableWithinAt

theorem differentiableOn_dirichletSeries {k₀ : ℕ} {c : Set.Ici k₀ → ℂ} {C : ℝ} {N : ℕ}
    (hC : 0 ≤ C) (h : ∀ m, ‖c m‖ ≤ C * ((m.1 : ℝ) + 1) ^ N) :
    DifferentiableOn ℂ (fun τ : ℂ => ∑' m : Set.Ici k₀, c m * dirichletTerm m.1 τ)
      {τ : ℂ | 0 < τ.im} := by
  refine differentiableOn_uHP_of fun y₀ hy₀ => ?_
  refine Complex.differentiableOn_tsum_of_summable_norm
    (u := fun m : Set.Ici k₀ => C * ((m.1:ℝ)+1)^N * Real.exp (-(2*Real.pi*y₀*(m.1:ℝ))))
    (summable_poly_exp_neg C N hy₀) ?_ (isOpen_lt continuous_const Complex.continuous_im) ?_
  · intro m
    exact ((differentiable_dirichletTerm m.1).const_mul (c m)).differentiableOn
  · intro m w hw
    rw [norm_mul, norm_dirichletTerm]
    have hm0 : (0:ℝ) ≤ (m.1:ℝ) := Nat.cast_nonneg _
    have hw' : y₀ < w.im := hw
    have hexp : Real.exp (-(2*Real.pi*w.im*(m.1:ℝ))) ≤ Real.exp (-(2*Real.pi*y₀*(m.1:ℝ))) := by
      rw [Real.exp_le_exp]
      nlinarith [Real.pi_pos, mul_le_mul_of_nonneg_right (le_of_lt hw') hm0]
    calc ‖c m‖ * Real.exp (-(2*Real.pi*w.im*(m.1:ℝ)))
        ≤ (C * ((m.1:ℝ)+1)^N) * Real.exp (-(2*Real.pi*w.im*(m.1:ℝ))) :=
          mul_le_mul_of_nonneg_right (h m) (Real.exp_nonneg _)
      _ ≤ (C * ((m.1:ℝ)+1)^N) * Real.exp (-(2*Real.pi*y₀*(m.1:ℝ))) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)

/-- A Dirichlet series times the linear factor `2 π i τ` is differentiable on the upper
half plane. -/
theorem differentiableOn_tau_dirichletSeries {k₀ : ℕ} {c : Set.Ici k₀ → ℂ} {C : ℝ} {N : ℕ}
    (hC : 0 ≤ C) (h : ∀ m, ‖c m‖ ≤ C * ((m.1 : ℝ) + 1) ^ N) :
    DifferentiableOn ℂ
      (fun τ : ℂ => (2 * (Real.pi : ℂ) * Complex.I * τ) *
        ∑' m : Set.Ici k₀, c m * dirichletTerm m.1 τ) {τ : ℂ | 0 < τ.im} := by
  have hlin : DifferentiableOn ℂ (fun τ : ℂ => 2 * (Real.pi : ℂ) * Complex.I * τ)
      {τ : ℂ | 0 < τ.im} :=
    (differentiable_id.const_mul (2 * (Real.pi : ℂ) * Complex.I)).differentiableOn
  exact hlin.mul (differentiableOn_dirichletSeries hC h)

/-- The difference of two polynomially bounded families is polynomially bounded. -/
lemma polyBoundSubGen' {k₀ : ℕ} {c c' : Set.Ici k₀ → ℂ} {N N' : ℕ} {C C' : ℝ}
    (hC : 0 ≤ C) (hC' : 0 ≤ C')
    (h : ∀ m, ‖c m‖ ≤ C * ((m.1:ℝ)+1)^N) (h' : ∀ m, ‖c' m‖ ≤ C' * ((m.1:ℝ)+1)^N') :
    ∀ m, ‖c m - c' m‖ ≤ (C + C') * ((m.1:ℝ)+1)^(max N N') := by
  intro m
  have h1 : (1:ℝ) ≤ (m.1:ℝ) + 1 := by
    have : (0:ℝ) ≤ (m.1:ℝ) := Nat.cast_nonneg _
    linarith
  have hN : ((m.1:ℝ)+1)^N ≤ ((m.1:ℝ)+1)^(max N N') :=
    pow_le_pow_right₀ h1 (le_max_left _ _)
  have hN' : ((m.1:ℝ)+1)^N' ≤ ((m.1:ℝ)+1)^(max N N') :=
    pow_le_pow_right₀ h1 (le_max_right _ _)
  calc ‖c m - c' m‖ ≤ ‖c m‖ + ‖c' m‖ := norm_sub_le _ _
    _ ≤ C * ((m.1:ℝ)+1)^N + C' * ((m.1:ℝ)+1)^N' := add_le_add (h m) (h' m)
    _ ≤ C * ((m.1:ℝ)+1)^(max N N') + C' * ((m.1:ℝ)+1)^(max N N') :=
        add_le_add (mul_le_mul_of_nonneg_left hN hC) (mul_le_mul_of_nonneg_left hN' hC')
    _ = (C + C') * ((m.1:ℝ)+1)^(max N N') := by ring

/-- **Decay of a Dirichlet series.** -/

lemma tendsToZero_dirichletSeries {k₀ : ℕ} {c : Set.Ici k₀ → ℂ} {C : ℝ} {N : ℕ}
    (hC : 0 ≤ C) (h : ∀ m, ‖c m‖ ≤ C * ((m.1:ℝ)+1)^N) (n : ℕ) [NeZero n] :
    TendsToZeroInStrip n ((k₀:ℝ) - 1)
      (fun τ (_ : E n) => ∑' m : Set.Ici k₀, c m * dirichletTerm m.1 τ) := by
  have h := tendsToZeroInStrip_dirichlet_poly (k₀ := k₀) hC h (fun _ => (1:ℂ)) (d := 0) (n := n)
    (fun τ _ _ _ => by simp)
  simpa using h

/-- **Decay of a Dirichlet series with a Dirichlet series indexed from `k₀` minus a single
term.**  This is the form in which the normalisation `F(τ,√(2m)) = e^{2πimτ}` is proved. -/
lemma tendsToZero_dirichletSeries_sub_single {k₀ : ℕ} {c : Set.Ici k₀ → ℂ} {C : ℝ} {N : ℕ}
    (hC : 0 ≤ C) (h : ∀ m', ‖c m'‖ ≤ C * ((m'.1:ℝ)+1)^N) (m : Set.Ici k₀) (n : ℕ) [NeZero n] :
    TendsToZeroInStrip n ((k₀:ℝ) - 1)
      (fun τ (_ : E n) =>
        (∑' m' : Set.Ici k₀, c m' * dirichletTerm m'.1 τ) - dirichletTerm m.1 τ) := by
  set c' : Set.Ici k₀ → ℂ := fun m' => if m = m' then (1:ℂ) else 0 with hc'
  set c1 : Set.Ici k₀ → ℂ := fun m' => c m' - c' m' with hc1
  have hc'_bound : ∀ m', ‖c' m'‖ ≤ (1:ℝ) * ((m'.1:ℝ)+1)^(0:ℕ) := by
    intro m'
    simp only [hc', pow_zero, mul_one]
    by_cases hmm : m = m' <;> simp [hmm]
  have hc1_bound : ∀ m', ‖c1 m'‖ ≤ (C + 1) * ((m'.1:ℝ)+1)^(max N 0) := by
    intro m'
    have := polyBoundSubGen' (c := c) (c' := c') (N := N) (N' := 0) (C := C) (C' := 1)
      hC zero_le_one h hc'_bound m'
    simpa only [hc1] using this
  have hbase := tendsToZero_dirichletSeries (k₀ := k₀) (c := c1)
    (C := C + 1) (N := max N 0) (add_nonneg hC zero_le_one) hc1_bound n
  refine TendsToZeroInStrip.congr hbase (fun τ x hτ => ?_)
  have hsum1 : Summable fun m' : Set.Ici k₀ => c m' * dirichletTerm m'.1 τ :=
    summable_mul_dirichletTerm_gen hC h τ hτ
  have hsum' : Summable fun m' : Set.Ici k₀ => c' m' * dirichletTerm m'.1 τ := by
    refine summable_of_ne_finset_zero (s := ({m} : Finset (Set.Ici k₀))) ?_
    intro b hb
    simp only [Finset.mem_singleton] at hb
    rw [hc']
    simp only
    rw [if_neg (fun h => hb h.symm), zero_mul]
  have htsum' : (∑' m' : Set.Ici k₀, c' m' * dirichletTerm m'.1 τ) = dirichletTerm m.1 τ := by
    rw [tsum_eq_single m]
    · rw [hc']; simp
    · intro b hb; rw [hc']; simp only; rw [if_neg (fun h => hb h.symm), zero_mul]
  show (∑' m' : Set.Ici k₀, c1 m' * dirichletTerm m'.1 τ) = (∑' m' : Set.Ici k₀, c m' * dirichletTerm m'.1 τ) - dirichletTerm m.1 τ
  rw [show (fun m' : Set.Ici k₀ => c1 m' * dirichletTerm m'.1 τ)
      = (fun m' : Set.Ici k₀ => c m' * dirichletTerm m'.1 τ - c' m' * dirichletTerm m'.1 τ)
      from funext fun m' => by rw [hc1]; simp only; ring]
  rw [hsum1.tsum_sub hsum', htsum']

/-- **Decay of `τ` times a Dirichlet series.** -/
lemma tendsToZero_tau_dirichletSeries {k₀ : ℕ} {c : Set.Ici k₀ → ℂ} {C : ℝ} {N : ℕ}
    (hC : 0 ≤ C) (h : ∀ m, ‖c m‖ ≤ C * ((m.1:ℝ)+1)^N) (n : ℕ) [NeZero n] :
    TendsToZeroInStrip n ((k₀:ℝ) - 1)
      (fun τ (_ : E n) => τ * ∑' m : Set.Ici k₀, c m * dirichletTerm m.1 τ) := by
  refine tendsToZeroInStrip_dirichlet_poly (k₀ := k₀) hC h (fun τ => τ) (d := 1) (n := n) ?_
  intro τ hτ hr1 hr2
  rw [pow_one]
  have hsq : ‖τ‖^2 ≤ (1 + τ.im)^2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    nlinarith [hτ, hr1, hr2, sq_nonneg τ.im]
  have h1 : ‖τ‖ ≤ Real.sqrt ((1 + τ.im)^2) := by
    rw [← Real.sqrt_sq (norm_nonneg τ)]
    exact Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (by linarith [hτ] : (0:ℝ) ≤ 1 + τ.im)] at h1

/-- The difference of a Dirichlet series with one of its terms. -/
lemma tsum_sub_delta_single {k₀ : ℕ} (c : Set.Ici k₀ → ℂ) (a : ℂ) (m : Set.Ici k₀) (τ : ℂ)
    (h : Summable fun m' : Set.Ici k₀ => c m' * dirichletTerm m'.1 τ) :
    (∑' m' : Set.Ici k₀, (c m' - (if m = m' then a else 0)) * dirichletTerm m'.1 τ)
      = (∑' m' : Set.Ici k₀, c m' * dirichletTerm m'.1 τ) - a * dirichletTerm m.1 τ := by
  have h' : Summable fun m' : Set.Ici k₀ => (if m = m' then a else 0) * dirichletTerm m'.1 τ := by
    refine summable_of_ne_finset_zero (s := ({m} : Finset (Set.Ici k₀))) ?_
    intro b hb
    simp only [Finset.mem_singleton] at hb
    rw [if_neg (fun h => hb h.symm), zero_mul]
  have hts : (∑' m' : Set.Ici k₀, (if m = m' then a else 0) * dirichletTerm m'.1 τ)
      = a * dirichletTerm m.1 τ := by
    rw [tsum_eq_single m]
    · rw [if_pos rfl]
    · intro b hb; rw [if_neg (fun h => hb h.symm), zero_mul]
  rw [show (fun m' : Set.Ici k₀ => (c m' - (if m = m' then a else 0)) * dirichletTerm m'.1 τ)
      = (fun m' : Set.Ici k₀ =>
          c m' * dirichletTerm m'.1 τ - (if m = m' then a else 0) * dirichletTerm m'.1 τ)
      from funext fun m' => by ring]
  rw [h.tsum_sub h', hts]

/-! ## The value normalisations from rigidity -/

lemma value_data_at {n : ℕ} [NeZero n] {k₀ : ℕ} (hk : 1 ≤ k₀)
    (hR : HomogeneousRigidity n ((k₀ : ℝ) - 1)) (S : FunctionalEquationSolution n)
    (basis : SampleIdx k₀ → RSch n) (hExp : ExpansionDataGen n k₀ S basis)
    (m : Set.Ici k₀) :
    (∀ τ : ℂ, 0 < τ.im → S.F τ (samplePoint (n := n) (m.1 : ℝ)) = dirichletTerm m.1 τ) ∧
    (∀ τ : ℂ, 0 < τ.im → S.Ftilde τ (samplePoint (n := n) (m.1 : ℝ)) = 0) := by
  obtain ⟨hF, hFt, hDF, hDFt, hGrow⟩ := hExp
  set x₀ : E n := samplePoint (n := n) (m.1 : ℝ) with hx₀
  obtain ⟨C0, N0, hC0, hb0⟩ := hGrow 0 0
  have hval : ∀ (j : Fin 4) (m' : Set.Ici k₀),
      ‖(basis (m', j)).1 x₀‖ ≤ C0 * ((m'.1:ℝ)+1)^N0 := by
    intro j m'
    have h := hb0 m' j x₀
    rw [pow_zero, one_mul] at h
    have hx : realIncl (n := n) ‖x₀‖ = x₀ := by rw [hx₀]; exact realIncl_norm_samplePoint _
    rwa [radialDeriv_zero_apply (⇑(basis (m',j)).1) x₀ hx] at h
  have hdec_tau : ∀ (j : Fin 4), TendsToZeroInStrip n ((k₀:ℝ)-1)
      (fun τ (_ : E n) => τ * ∑' m' : Set.Ici k₀,
        ((2*(Real.pi:ℂ)*Complex.I) * ((rate m'.1 : ℂ) * (basis (m', j)).1 x₀))
          * dirichletTerm m'.1 τ) := by
    intro j
    refine tendsToZero_tau_dirichletSeries (k₀ := k₀) (C := 2*Real.pi*C0) (N := N0+1)
      (by positivity) (fun m' => ?_) n
    have hb := hval j m'
    have hr0 : 0 ≤ rate m'.1 := Real.sqrt_nonneg _
    have hrle : rate m'.1 ≤ (m'.1:ℝ) + 1 := rate_le_add_one m'.1
    have hpos : 0 ≤ ((m'.1:ℝ)+1) := by positivity
    have h2pi : ‖(2*(Real.pi:ℂ)*Complex.I)‖ = 2*Real.pi := by
      rw [show (2*(Real.pi:ℂ)*Complex.I) = ((2*Real.pi:ℝ):ℂ) * Complex.I by push_cast; ring,
        norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    rw [norm_mul, h2pi, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr0]
    calc 2*Real.pi * (rate m'.1 * ‖(basis (m',j)).1 x₀‖)
        ≤ 2*Real.pi * (((m'.1:ℝ)+1) * (C0*((m'.1:ℝ)+1)^N0)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hrle hb (norm_nonneg _) hpos) (by positivity)
      _ = (2*Real.pi*C0) * ((m'.1:ℝ)+1)^(N0+1) := by rw [pow_succ]; ring
  have hdecF : TendsToZeroInStrip n ((k₀:ℝ)-1)
      (fun τ (_ : E n) => S.F τ x₀ - dirichletTerm m.1 τ) := by
    have hbase := TendsToZeroInStrip.add
      (tendsToZero_dirichletSeries_sub_single (k₀ := k₀) hC0 (fun m' => hval 0 m') m n)
      (hdec_tau 2)
    refine TendsToZeroInStrip.congr hbase (fun τ x hτ => ?_)
    have hsm : Summable fun m' : Set.Ici k₀ =>
        (rate m'.1 : ℂ) * (basis (m',2)).1 x₀ * dirichletTerm m'.1 τ :=
      summable_rate_mul_dirichletTerm_gen hC0 (fun m' => hval 2 m') τ hτ
    have hsum2 : (∑' m' : Set.Ici k₀,
          ((2*(Real.pi:ℂ)*Complex.I) * ((rate m'.1 : ℂ) * (basis (m',2)).1 x₀))
            * dirichletTerm m'.1 τ)
        = (2*(Real.pi:ℂ)*Complex.I) *
          (∑' m' : Set.Ici k₀, (rate m'.1 : ℂ) * (basis (m',2)).1 x₀ * dirichletTerm m'.1 τ) := by
      have hshape : (fun m' : Set.Ici k₀ =>
            ((2*(Real.pi:ℂ)*Complex.I) * ((rate m'.1 : ℂ) * (basis (m',2)).1 x₀)) * dirichletTerm m'.1 τ)
          = fun m' : Set.Ici k₀ => (2*(Real.pi:ℂ)*Complex.I) *
              (((rate m'.1 : ℂ) * (basis (m',2)).1 x₀) * dirichletTerm m'.1 τ) :=
        funext fun m' => by ring
      rw [hshape, hsm.tsum_mul_left (2*(Real.pi:ℂ)*Complex.I)]
    rw [hF τ x₀ hτ, hsum2]
    ring
  have hdecFt : TendsToZeroInStrip n ((k₀:ℝ)-1) (fun τ (_ : E n) => S.Ftilde τ x₀) := by
    have hbase := TendsToZeroInStrip.add
      (tendsToZero_dirichletSeries (k₀ := k₀) hC0 (fun m' => hval 1 m') n) (hdec_tau 3)
    refine TendsToZeroInStrip.congr hbase (fun τ x hτ => ?_)
    have hsm : Summable fun m' : Set.Ici k₀ =>
        (rate m'.1 : ℂ) * (basis (m',3)).1 x₀ * dirichletTerm m'.1 τ :=
      summable_rate_mul_dirichletTerm_gen hC0 (fun m' => hval 3 m') τ hτ
    have hsum2 : (∑' m' : Set.Ici k₀,
          ((2*(Real.pi:ℂ)*Complex.I) * ((rate m'.1 : ℂ) * (basis (m',3)).1 x₀))
            * dirichletTerm m'.1 τ)
        = (2*(Real.pi:ℂ)*Complex.I) *
          (∑' m' : Set.Ici k₀, (rate m'.1 : ℂ) * (basis (m',3)).1 x₀ * dirichletTerm m'.1 τ) := by
      have hshape : (fun m' : Set.Ici k₀ =>
            ((2*(Real.pi:ℂ)*Complex.I) * ((rate m'.1 : ℂ) * (basis (m',3)).1 x₀)) * dirichletTerm m'.1 τ)
          = fun m' : Set.Ici k₀ => (2*(Real.pi:ℂ)*Complex.I) *
              (((rate m'.1 : ℂ) * (basis (m',3)).1 x₀) * dirichletTerm m'.1 τ) :=
        funext fun m' => by ring
      rw [hshape, hsm.tsum_mul_left (2*(Real.pi:ℂ)*Complex.I)]
    rw [hFt τ x₀ hτ, hsum2]
    ring
  have hd1 : ∀ x : E n, DifferentiableOn ℂ
      (fun τ : ℂ => (fun τ (_ : E n) => S.F τ x₀ - dirichletTerm m.1 τ) τ x)
      {τ : ℂ | 0 < τ.im} :=
    fun x => (S.holomorphic_F x₀).sub (differentiable_dirichletTerm m.1).differentiableOn
  have hd2 : ∀ x : E n, DifferentiableOn ℂ
      (fun τ : ℂ => (fun τ (_ : E n) => S.Ftilde τ x₀) τ x) {τ : ℂ | 0 < τ.im} :=
    fun x => S.holomorphic_Ftilde x₀
  have hrec1 : ∀ (τ : ℂ) (x : E n), 0 < τ.im →
      (fun τ (_ : E n) => S.F τ x₀ - dirichletTerm m.1 τ) (τ+2) x
        - 2 * (fun τ (_ : E n) => S.F τ x₀ - dirichletTerm m.1 τ) (τ+1) x
        + (fun τ (_ : E n) => S.F τ x₀ - dirichletTerm m.1 τ) τ x = 0 := by
    intro τ x hτ
    have hrec := S.recur_F τ x₀ hτ
    have d1 : dirichletTerm m.1 (τ+1) = dirichletTerm m.1 τ := dirichletTerm_add_one _ _
    have d2 : dirichletTerm m.1 (τ+2) = dirichletTerm m.1 τ := by
      rw [show τ+2 = (τ+1)+1 by ring, dirichletTerm_add_one, dirichletTerm_add_one]
    show (S.F (τ+2) x₀ - dirichletTerm m.1 (τ+2)) - 2 * (S.F (τ+1) x₀ - dirichletTerm m.1 (τ+1))
        + (S.F τ x₀ - dirichletTerm m.1 τ) = 0
    rw [d1, d2,
      show (S.F (τ+2) x₀ - dirichletTerm m.1 τ) - 2 * (S.F (τ+1) x₀ - dirichletTerm m.1 τ)
          + (S.F τ x₀ - dirichletTerm m.1 τ)
        = (S.F (τ+2) x₀ - 2 * S.F (τ+1) x₀ + S.F τ x₀) from by ring,
      hrec]
  have hrec2 : ∀ (τ : ℂ) (x : E n), 0 < τ.im →
      (fun τ (_ : E n) => S.Ftilde τ x₀) (τ+2) x
        - 2 * (fun τ (_ : E n) => S.Ftilde τ x₀) (τ+1) x
        + (fun τ (_ : E n) => S.Ftilde τ x₀) τ x = 0 := by
    intro τ x hτ
    show S.Ftilde (τ+2) x₀ - 2 * S.Ftilde (τ+1) x₀ + S.Ftilde τ x₀ = 0
    rw [S.recur_Ftilde τ x₀ hτ]
  have hslash : ∀ (τ : ℂ) (x : E n), 0 < τ.im →
      (fun τ (_ : E n) => S.F τ x₀ - dirichletTerm m.1 τ) τ x
        + slashFactor n τ * (fun τ (_ : E n) => S.Ftilde τ x₀) (-1/τ) x = 0 := by
    intro τ x hτ
    have hfe := S.functional_equation τ x₀ hτ
    have hg : Work.Core.gaussianFun n τ x₀ = dirichletTerm m.1 τ := by
      rw [hx₀]; exact gaussianFun_samplePoint τ m.1
    show (S.F τ x₀ - dirichletTerm m.1 τ) + slashFactor n τ * S.Ftilde (-1/τ) x₀ = 0
    rw [← hg, ← hfe]; ring
  have hres := hR (fun τ (_ : E n) => S.F τ x₀ - dirichletTerm m.1 τ)
      (fun τ (_ : E n) => S.Ftilde τ x₀) hd1 hd2 hrec1 hrec2 hslash hdecF hdecFt
  refine ⟨fun τ hτ => ?_, fun τ hτ => ?_⟩
  · exact sub_eq_zero.mp (hres τ 0 hτ).1
  · exact (hres τ 0 hτ).2

/-! ## The radial-derivative normalisations from rigidity -/

lemma deriv_data_at {n : ℕ} [NeZero n] {k₀ : ℕ} (hk : 1 ≤ k₀)
    (hR : HomogeneousRigidity n ((k₀ : ℝ) - 1)) (S : FunctionalEquationSolution n)
    (basis : SampleIdx k₀ → RSch n) (hExp : ExpansionDataGen n k₀ S basis)
    (m : Set.Ici k₀) :
    (∀ τ : ℂ, 0 < τ.im →
      radialDeriv 1 (S.F τ) (samplePoint (n := n) (m.1 : ℝ))
        = (2*(Real.pi:ℂ)*Complex.I*τ*(rate m.1 : ℂ)) * dirichletTerm m.1 τ) ∧
    (∀ τ : ℂ, 0 < τ.im →
      radialDeriv 1 (S.Ftilde τ) (samplePoint (n := n) (m.1 : ℝ)) = 0) := by
  obtain ⟨hF, hFt, hDF, hDFt, hGrow⟩ := hExp
  set x₀ : E n := samplePoint (n := n) (m.1 : ℝ) with hx₀
  obtain ⟨C1, N1, hC1, hb1⟩ := hGrow 0 1
  have hder : ∀ (j : Fin 4) (m' : Set.Ici k₀),
      ‖radialDeriv 1 (⇑(basis (m', j)).1) x₀‖ ≤ C1 * ((m'.1:ℝ)+1)^N1 := by
    intro j m'
    have h := hb1 m' j x₀
    rwa [pow_zero, one_mul] at h
  have h2pi : ‖(2*(Real.pi:ℂ)*Complex.I)‖ = 2*Real.pi := by
    rw [show (2*(Real.pi:ℂ)*Complex.I) = ((2*Real.pi:ℝ):ℂ) * Complex.I by push_cast; ring,
      norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hrate_der : ∀ (j : Fin 4) (m' : Set.Ici k₀),
      ‖(rate m'.1 : ℂ) * radialDeriv 1 (⇑(basis (m',j)).1) x₀‖ ≤ C1 * ((m'.1:ℝ)+1)^(N1+1) := by
    intro j m'
    have hr0 : 0 ≤ rate m'.1 := Real.sqrt_nonneg _
    have hrle : rate m'.1 ≤ (m'.1:ℝ) + 1 := rate_le_add_one m'.1
    have hpos : 0 ≤ ((m'.1:ℝ)+1) := by positivity
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr0]
    calc rate m'.1 * ‖radialDeriv 1 (⇑(basis (m',j)).1) x₀‖
        ≤ ((m'.1:ℝ)+1) * (C1*((m'.1:ℝ)+1)^N1) :=
          mul_le_mul hrle (hder j m') (norm_nonneg _) hpos
      _ = C1 * ((m'.1:ℝ)+1)^(N1+1) := by rw [pow_succ]; ring
  have htau_bound : ∀ (j : Fin 4) (m' : Set.Ici k₀),
      ‖(2*(Real.pi:ℂ)*Complex.I) * ((rate m'.1 : ℂ) * radialDeriv 1 (⇑(basis (m',j)).1) x₀)‖
        ≤ (2*Real.pi*C1) * ((m'.1:ℝ)+1)^(N1+1) := by
    intro j m'
    rw [norm_mul, h2pi]
    calc 2*Real.pi * ‖(rate m'.1 : ℂ) * radialDeriv 1 (⇑(basis (m',j)).1) x₀‖
        ≤ 2*Real.pi * (C1 * ((m'.1:ℝ)+1)^(N1+1)) :=
          mul_le_mul_of_nonneg_left (hrate_der j m') (by positivity)
      _ = (2*Real.pi*C1) * ((m'.1:ℝ)+1)^(N1+1) := by ring
  -- decay of the `a`-series and the `τ`-series of the derivative of `F`
  have hdecA : TendsToZeroInStrip n ((k₀:ℝ)-1)
      (fun τ (_ : E n) =>
        ∑' m' : Set.Ici k₀, radialDeriv 1 (⇑(basis (m',0)).1) x₀ * dirichletTerm m'.1 τ) :=
    tendsToZero_dirichletSeries (k₀ := k₀) hC1 (fun m' => hder 0 m') n
  have hdecCtau : TendsToZeroInStrip n ((k₀:ℝ)-1)
      (fun τ (_ : E n) => τ * ∑' m' : Set.Ici k₀,
        ((2*(Real.pi:ℂ)*Complex.I) * ((rate m'.1 : ℂ) * radialDeriv 1 (⇑(basis (m',2)).1) x₀)
          - (if m = m' then (2*(Real.pi:ℂ)*Complex.I) * (rate m.1 : ℂ) else 0))
          * dirichletTerm m'.1 τ) := by
    refine tendsToZero_tau_dirichletSeries (k₀ := k₀) (C := 2*Real.pi*C1 + 2*Real.pi*rate m.1)
      (N := max (N1+1) 0) ?_ (fun m' => ?_) n
    · have h1 : (0:ℝ) ≤ 2*Real.pi*C1 := mul_nonneg (by positivity) hC1
      have h2 : (0:ℝ) ≤ 2*Real.pi*rate m.1 := mul_nonneg (by positivity) (rate_nonneg m.1)
      exact add_nonneg h1 h2
    · have h1 : ∀ m' : Set.Ici k₀,
          ‖(2*(Real.pi:ℂ)*Complex.I) * ((rate m'.1 : ℂ) * radialDeriv 1 (⇑(basis (m',2)).1) x₀)‖
            ≤ (2*Real.pi*C1) * ((m'.1:ℝ)+1)^(N1+1) := fun m' => htau_bound 2 m'
      have h2 : ∀ m' : Set.Ici k₀,
          ‖(if m = m' then (2*(Real.pi:ℂ)*Complex.I) * (rate m.1 : ℂ) else 0)‖
            ≤ (2*Real.pi*rate m.1) * ((m'.1:ℝ)+1)^(0:ℕ) := by
        intro m'
        rw [pow_zero, mul_one]
        by_cases hmm : m = m'
        · rw [if_pos hmm, norm_mul, h2pi, Complex.norm_real, Real.norm_of_nonneg (rate_nonneg m.1)]
        · rw [if_neg hmm, norm_zero]
          have h1 : (0:ℝ) ≤ 2*Real.pi := by positivity
          have h2 : (0:ℝ) ≤ rate m.1 := rate_nonneg m.1
          exact mul_nonneg h1 h2
      have hC1' : (0:ℝ) ≤ 2*Real.pi*C1 := mul_nonneg (by positivity) hC1
      have hC2' : (0:ℝ) ≤ 2*Real.pi*rate m.1 := mul_nonneg (by positivity) (rate_nonneg m.1)
      exact polyBoundSubGen' hC1' hC2' h1 h2 m'
  have hdecD : TendsToZeroInStrip n ((k₀:ℝ)-1)
      (fun τ (_ : E n) => radialDeriv 1 (S.F τ) x₀
        - (2*(Real.pi:ℂ)*Complex.I*τ*(rate m.1 : ℂ)) * dirichletTerm m.1 τ) := by
    refine TendsToZeroInStrip.congr (TendsToZeroInStrip.add hdecA hdecCtau) (fun τ x hτ => ?_)
    have hsm : Summable fun m' : Set.Ici k₀ =>
        (rate m'.1 : ℂ) * radialDeriv 1 (⇑(basis (m',2)).1) x₀ * dirichletTerm m'.1 τ :=
      summable_rate_mul_dirichletTerm_gen hC1 (fun m' => hder 2 m') τ hτ
    have hsm' : Summable fun m' : Set.Ici k₀ =>
        ((2*(Real.pi:ℂ)*Complex.I) * ((rate m'.1 : ℂ) * radialDeriv 1 (⇑(basis (m',2)).1) x₀))
          * dirichletTerm m'.1 τ :=
      (hsm.mul_left (2*(Real.pi:ℂ)*Complex.I)).congr (fun m' => by ring)
    have hsum2 : (∑' m' : Set.Ici k₀,
          ((2*(Real.pi:ℂ)*Complex.I) * ((rate m'.1 : ℂ) * radialDeriv 1 (⇑(basis (m',2)).1) x₀))
            * dirichletTerm m'.1 τ)
        = (2*(Real.pi:ℂ)*Complex.I) *
          (∑' m' : Set.Ici k₀,
            (rate m'.1 : ℂ) * radialDeriv 1 (⇑(basis (m',2)).1) x₀ * dirichletTerm m'.1 τ) := by
      have hshape : (fun m' : Set.Ici k₀ =>
            ((2*(Real.pi:ℂ)*Complex.I) * ((rate m'.1 : ℂ) * radialDeriv 1 (⇑(basis (m',2)).1) x₀))
              * dirichletTerm m'.1 τ)
          = fun m' : Set.Ici k₀ => (2*(Real.pi:ℂ)*Complex.I) *
              (((rate m'.1 : ℂ) * radialDeriv 1 (⇑(basis (m',2)).1) x₀) * dirichletTerm m'.1 τ) :=
        funext fun m' => by ring
      rw [hshape, hsm.tsum_mul_left (2*(Real.pi:ℂ)*Complex.I)]
    have hsub := tsum_sub_delta_single
      (c := fun m' => (2*(Real.pi:ℂ)*Complex.I) * ((rate m'.1 : ℂ) * radialDeriv 1 (⇑(basis (m',2)).1) x₀))
      ((2*(Real.pi:ℂ)*Complex.I) * (rate m.1 : ℂ)) m τ hsm'
    rw [hDF 1 τ x₀ hτ, hsub, hsum2]
    ring
  have hdecDt : TendsToZeroInStrip n ((k₀:ℝ)-1)
      (fun τ (_ : E n) => radialDeriv 1 (S.Ftilde τ) x₀) := by
    have hbase := TendsToZeroInStrip.add
      (tendsToZero_dirichletSeries (k₀ := k₀) hC1 (fun m' => hder 1 m') n)
      (tendsToZero_tau_dirichletSeries (k₀ := k₀) (C := 2*Real.pi*C1) (N := N1+1)
        (by positivity) (fun m' => htau_bound 3 m') n)
    refine TendsToZeroInStrip.congr hbase (fun τ x hτ => ?_)
    have hsm : Summable fun m' : Set.Ici k₀ =>
        (rate m'.1 : ℂ) * radialDeriv 1 (⇑(basis (m',3)).1) x₀ * dirichletTerm m'.1 τ :=
      summable_rate_mul_dirichletTerm_gen hC1 (fun m' => hder 3 m') τ hτ
    have hsum2 : (∑' m' : Set.Ici k₀,
          ((2*(Real.pi:ℂ)*Complex.I) * ((rate m'.1 : ℂ) * radialDeriv 1 (⇑(basis (m',3)).1) x₀))
            * dirichletTerm m'.1 τ)
        = (2*(Real.pi:ℂ)*Complex.I) *
          (∑' m' : Set.Ici k₀,
            (rate m'.1 : ℂ) * radialDeriv 1 (⇑(basis (m',3)).1) x₀ * dirichletTerm m'.1 τ) := by
      have hshape : (fun m' : Set.Ici k₀ =>
            ((2*(Real.pi:ℂ)*Complex.I) * ((rate m'.1 : ℂ) * radialDeriv 1 (⇑(basis (m',3)).1) x₀))
              * dirichletTerm m'.1 τ)
          = fun m' : Set.Ici k₀ => (2*(Real.pi:ℂ)*Complex.I) *
              (((rate m'.1 : ℂ) * radialDeriv 1 (⇑(basis (m',3)).1) x₀) * dirichletTerm m'.1 τ) :=
        funext fun m' => by ring
      rw [hshape, hsm.tsum_mul_left (2*(Real.pi:ℂ)*Complex.I)]
    rw [hDFt 1 τ x₀ hτ, hsum2]
    ring
  -- differentiability in `τ`
  have hdd : ∀ x : E n, DifferentiableOn ℂ
      (fun τ : ℂ => (fun τ (_ : E n) => radialDeriv 1 (S.F τ) x₀
        - (2*(Real.pi:ℂ)*Complex.I*τ*(rate m.1 : ℂ)) * dirichletTerm m.1 τ) τ x)
      {τ : ℂ | 0 < τ.im} := by
    intro x
    have hA : DifferentiableOn ℂ (fun τ : ℂ =>
        ∑' m' : Set.Ici k₀, radialDeriv 1 (⇑(basis (m',0)).1) x₀ * dirichletTerm m'.1 τ)
        {τ : ℂ | 0 < τ.im} := differentiableOn_dirichletSeries hC1 (fun m' => hder 0 m')
    have hB : DifferentiableOn ℂ (fun τ : ℂ => (2*(Real.pi:ℂ)*Complex.I*τ) *
        ∑' m' : Set.Ici k₀,
          (rate m'.1 : ℂ) * radialDeriv 1 (⇑(basis (m',2)).1) x₀ * dirichletTerm m'.1 τ)
        {τ : ℂ | 0 < τ.im} :=
      differentiableOn_tau_dirichletSeries hC1 (fun m' => hrate_der 2 m')
    have hC : DifferentiableOn ℂ (fun τ : ℂ =>
        (2*(Real.pi:ℂ)*Complex.I*τ*(rate m.1 : ℂ)) * dirichletTerm m.1 τ)
        {τ : ℂ | 0 < τ.im} := by
      have h1 : Differentiable ℂ (fun τ : ℂ => τ * dirichletTerm m.1 τ) :=
        differentiable_id.mul (differentiable_dirichletTerm m.1)
      refine DifferentiableOn.congr
        ((h1.const_mul (2*(Real.pi:ℂ)*Complex.I*(rate m.1:ℂ))).differentiableOn)
        (fun τ _ => ?_)
      ring
    refine DifferentiableOn.congr ((hA.add hB).sub hC) (fun τ hτ => ?_)
    simp only [Pi.add_apply, Pi.sub_apply]
    beta_reduce
    rw [hDF 1 τ x₀ hτ]
  have hddt : ∀ x : E n, DifferentiableOn ℂ
      (fun τ : ℂ => (fun τ (_ : E n) => radialDeriv 1 (S.Ftilde τ) x₀) τ x)
      {τ : ℂ | 0 < τ.im} := by
    intro x
    have hA : DifferentiableOn ℂ (fun τ : ℂ =>
        ∑' m' : Set.Ici k₀, radialDeriv 1 (⇑(basis (m',1)).1) x₀ * dirichletTerm m'.1 τ)
        {τ : ℂ | 0 < τ.im} := differentiableOn_dirichletSeries hC1 (fun m' => hder 1 m')
    have hB : DifferentiableOn ℂ (fun τ : ℂ => (2*(Real.pi:ℂ)*Complex.I*τ) *
        ∑' m' : Set.Ici k₀,
          (rate m'.1 : ℂ) * radialDeriv 1 (⇑(basis (m',3)).1) x₀ * dirichletTerm m'.1 τ)
        {τ : ℂ | 0 < τ.im} :=
      differentiableOn_tau_dirichletSeries hC1 (fun m' => hrate_der 3 m')
    refine DifferentiableOn.congr (hA.add hB) (fun τ hτ => ?_)
    simp only [Pi.add_apply]
    beta_reduce
    rw [hDFt 1 τ x₀ hτ]
  -- the functional equations
  have hr1 : ∀ (τ : ℂ) (x : E n), 0 < τ.im →
      (fun τ (_ : E n) => radialDeriv 1 (S.F τ) x₀
        - (2*(Real.pi:ℂ)*Complex.I*τ*(rate m.1 : ℂ)) * dirichletTerm m.1 τ) (τ+2) x
        - 2 * (fun τ (_ : E n) => radialDeriv 1 (S.F τ) x₀
            - (2*(Real.pi:ℂ)*Complex.I*τ*(rate m.1 : ℂ)) * dirichletTerm m.1 τ) (τ+1) x
        + (fun τ (_ : E n) => radialDeriv 1 (S.F τ) x₀
            - (2*(Real.pi:ℂ)*Complex.I*τ*(rate m.1 : ℂ)) * dirichletTerm m.1 τ) τ x = 0 := by
    intro τ x hτ
    have hcomb := radialDeriv_one_combination_eq_zero (A := S.F (τ+2)) (B := S.F (τ+1))
      (C := S.F τ) (x := x₀)
      (differentiableAt_profile (S.smooth_F (τ+2)) x₀)
      (differentiableAt_profile (S.smooth_F (τ+1)) x₀)
      (differentiableAt_profile (S.smooth_F τ) x₀)
      (fun y => S.recur_F τ y hτ)
    have d1 : dirichletTerm m.1 (τ+1) = dirichletTerm m.1 τ := dirichletTerm_add_one _ _
    have d2 : dirichletTerm m.1 (τ+2) = dirichletTerm m.1 τ := by
      rw [show τ+2 = (τ+1)+1 by ring, dirichletTerm_add_one, dirichletTerm_add_one]
    show (radialDeriv 1 (S.F (τ+2)) x₀
          - (2*(Real.pi:ℂ)*Complex.I*(τ+2)*(rate m.1 : ℂ)) * dirichletTerm m.1 (τ+2))
        - 2 * (radialDeriv 1 (S.F (τ+1)) x₀
          - (2*(Real.pi:ℂ)*Complex.I*(τ+1)*(rate m.1 : ℂ)) * dirichletTerm m.1 (τ+1))
        + (radialDeriv 1 (S.F τ) x₀
          - (2*(Real.pi:ℂ)*Complex.I*τ*(rate m.1 : ℂ)) * dirichletTerm m.1 τ) = 0
    rw [d1, d2]
    rw [show (radialDeriv 1 (S.F (τ+2)) x₀
            - 2*(Real.pi:ℂ)*Complex.I*(τ+2)*(rate m.1 : ℂ)*dirichletTerm m.1 τ)
          - 2 * (radialDeriv 1 (S.F (τ+1)) x₀
            - 2*(Real.pi:ℂ)*Complex.I*(τ+1)*(rate m.1 : ℂ)*dirichletTerm m.1 τ)
          + (radialDeriv 1 (S.F τ) x₀
            - 2*(Real.pi:ℂ)*Complex.I*τ*(rate m.1 : ℂ)*dirichletTerm m.1 τ)
        = radialDeriv 1 (S.F (τ+2)) x₀ - 2 * radialDeriv 1 (S.F (τ+1)) x₀
          + radialDeriv 1 (S.F τ) x₀ from by ring,
      hcomb]
  have hr2 : ∀ (τ : ℂ) (x : E n), 0 < τ.im →
      (fun τ (_ : E n) => radialDeriv 1 (S.Ftilde τ) x₀) (τ+2) x
        - 2 * (fun τ (_ : E n) => radialDeriv 1 (S.Ftilde τ) x₀) (τ+1) x
        + (fun τ (_ : E n) => radialDeriv 1 (S.Ftilde τ) x₀) τ x = 0 := by
    intro τ x hτ
    have hcomb := radialDeriv_one_combination_eq_zero (A := S.Ftilde (τ+2)) (B := S.Ftilde (τ+1))
      (C := S.Ftilde τ) (x := x₀)
      (differentiableAt_profile (S.smooth_Ftilde (τ+2)) x₀)
      (differentiableAt_profile (S.smooth_Ftilde (τ+1)) x₀)
      (differentiableAt_profile (S.smooth_Ftilde τ) x₀)
      (fun y => S.recur_Ftilde τ y hτ)
    exact hcomb
  have hslash : ∀ (τ : ℂ) (x : E n), 0 < τ.im →
      (fun τ (_ : E n) => radialDeriv 1 (S.F τ) x₀
        - (2*(Real.pi:ℂ)*Complex.I*τ*(rate m.1 : ℂ)) * dirichletTerm m.1 τ) τ x
        + slashFactor n τ * (fun τ (_ : E n) => radialDeriv 1 (S.Ftilde τ) x₀) (-1/τ) x = 0 := by
    intro τ x hτ
    have hfe : (fun y : E n => S.F τ y + slashFactor n τ * S.Ftilde (-1/τ) y)
        = fun y => Work.Core.gaussianFun n τ y := by
      funext y; rw [S.functional_equation τ y hτ]
    have hdFt : DifferentiableAt ℝ (fun r : ℝ => S.Ftilde (-1/τ) (realIncl (n:=n) r)) ‖x₀‖ :=
      differentiableAt_profile (S.smooth_Ftilde (-1/τ)) x₀
    have hg : radialDeriv 1 (fun y : E n => slashFactor n τ * S.Ftilde (-1/τ) y) x₀
        = slashFactor n τ * radialDeriv 1 (S.Ftilde (-1/τ)) x₀ :=
      radialDeriv_one_const_mul (slashFactor n τ) hdFt
    have h1 : radialDeriv 1 (S.F τ) x₀ + slashFactor n τ * radialDeriv 1 (S.Ftilde (-1/τ)) x₀
        = (2*(Real.pi:ℂ)*Complex.I*τ*(rate m.1 : ℂ)) * dirichletTerm m.1 τ := by
      rw [← hg, ← radialDeriv_one_add (differentiableAt_profile (S.smooth_F τ) x₀)
        (hdFt.const_mul (slashFactor n τ)), hfe]
      exact radialDeriv_gaussianFun_samplePoint τ m.1
    show (radialDeriv 1 (S.F τ) x₀ - (2*(Real.pi:ℂ)*Complex.I*τ*(rate m.1 : ℂ)) * dirichletTerm m.1 τ)
      + slashFactor n τ * radialDeriv 1 (S.Ftilde (-1/τ)) x₀ = 0
    linear_combination h1
  have hres := hR (fun τ (_ : E n) => radialDeriv 1 (S.F τ) x₀
        - (2*(Real.pi:ℂ)*Complex.I*τ*(rate m.1 : ℂ)) * dirichletTerm m.1 τ)
      (fun τ (_ : E n) => radialDeriv 1 (S.Ftilde τ) x₀)
      hdd hddt hr1 hr2 hslash hdecD hdecDt
  refine ⟨fun τ hτ => ?_, fun τ hτ => ?_⟩
  · exact sub_eq_zero.mp (hres τ 0 hτ).1
  · exact (hres τ 0 hτ).2

/-- **The value normalisations of Section 8 from the uniqueness input.**  The pointwise
normalisations `F(τ,√(2m)) = e^{2πimτ}`, `F̃(τ,√(2m)) = 0` and their first radial
derivatives, for the sample radii `√(2m)`, `m ≥ k₀`. -/
theorem Section8ValueDataOfRigidity {n : ℕ} [NeZero n] {k₀ : ℕ} (hk : 1 ≤ k₀)
    (hR : HomogeneousRigidity n ((k₀ : ℝ) - 1)) (S : FunctionalEquationSolution n)
    (basis : SampleIdx k₀ → RSch n) (hExp : ExpansionDataGen n k₀ S basis) :
    Section8ValueDataGen n k₀ S basis := by
  refine ⟨fun m τ hτ => (value_data_at hk hR S basis hExp m).1 τ hτ,
    fun m τ hτ => (value_data_at hk hR S basis hExp m).2 τ hτ,
    fun m τ hτ => (deriv_data_at hk hR S basis hExp m).1 τ hτ,
    fun m τ hτ => (deriv_data_at hk hR S basis hExp m).2 τ hτ⟩

end

end Work.FunctionalEquations
