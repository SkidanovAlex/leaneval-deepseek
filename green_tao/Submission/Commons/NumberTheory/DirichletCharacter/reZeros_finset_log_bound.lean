import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_conj
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_norm_half_plane
import Submission.Commons.NumberTheory.DirichletCharacter.norm_LFunction_le_re_ge_one
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_re_lower_of_two_le_re
import Submission.Commons.Algebra.BigOperators.card_le_finsum_of_one_le

open Complex DirichletCharacter Metric
open scoped Real Topology BigOperators

set_option linter.unusedVariables false

namespace Commons.NumberTheory.DirichletCharacter

lemma conj_shift (σ T : ℝ) :
    (starRingEnd ℂ) ((σ : ℂ) + (T : ℂ) * Complex.I) = (σ : ℂ) - (T : ℂ) * Complex.I := by
  simp [Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im]

noncomputable def reZeroFun {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (T : ℝ) : ℂ → ℂ :=
  (fun z => χ.LFunction (z + (T : ℂ) * Complex.I)) +
    (fun z => (χ⁻¹).LFunction (z - (T : ℂ) * Complex.I))

lemma reZeroFun_apply {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (T : ℝ) (z : ℂ) :
    reZeroFun χ T z = χ.LFunction (z + (T : ℂ) * Complex.I) +
      (χ⁻¹).LFunction (z - (T : ℂ) * Complex.I) := rfl

lemma reZeroFun_apply_ofReal {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (T σ : ℝ) :
    reZeroFun χ T (σ : ℂ) = (((2 * (χ.LFunction ((σ : ℂ) + (T : ℂ) * Complex.I)).re) : ℝ) : ℂ) := by
  have hconj := LFunction_conj χ hχ ((σ : ℂ) + (T : ℂ) * Complex.I)
  rw [conj_shift σ T] at hconj
  rw [reZeroFun_apply, ← hconj]
  exact Complex.add_conj _

lemma chiInv_ne_one {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    χ⁻¹ ≠ 1 := by
  intro h
  apply hχ
  calc χ = (χ⁻¹)⁻¹ := by rw [inv_inv]
    _ = (1 : DirichletCharacter ℂ N)⁻¹ := by rw [h]
    _ = 1 := by simp

lemma reZeroFun_differentiable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (T : ℝ) : Differentiable ℂ (reZeroFun χ T) := by
  have h1 : Differentiable ℂ (fun z : ℂ => χ.LFunction (z + (T : ℂ) * Complex.I)) :=
    (DirichletCharacter.differentiable_LFunction hχ).comp (differentiable_id.add_const _)
  have h2 : Differentiable ℂ (fun z : ℂ => (χ⁻¹).LFunction (z - (T : ℂ) * Complex.I)) :=
    (DirichletCharacter.differentiable_LFunction (chiInv_ne_one hχ)).comp
      (differentiable_id.sub_const _)
  exact h1.add h2

lemma LFunction_bound_region {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    {s : ℂ} (hlo : 1/8 ≤ s.re) :
    ‖χ.LFunction s‖ ≤ 16 * (N:ℝ) * (1 + |s.im|) + Real.log (N:ℝ) + Real.log (2 + |s.im|) + 6 := by
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  by_cases h1 : s.re ≤ 1
  · have hpos : 0 < s.re := lt_of_lt_of_le (by norm_num) hlo
    have hb := LFunction_norm_half_plane χ hχ hpos
    have hsn : ‖s‖ ≤ 1 + |s.im| := by
      calc ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
        _ = s.re + |s.im| := by rw [abs_of_nonneg (le_of_lt hpos)]
        _ ≤ 1 + |s.im| := by linarith
    have hsinv : 1 / s.re ≤ 8 := by
      have h := one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 1/8) hlo
      norm_num at h
      simpa [one_div] using h
    have hdiv : ‖s‖ / s.re ≤ 8 * (1 + |s.im|) := by
      rw [div_eq_mul_inv]
      calc ‖s‖ * s.re⁻¹ ≤ (1 + |s.im|) * s.re⁻¹ :=
            mul_le_mul_of_nonneg_right hsn (by positivity)
        _ ≤ (1 + |s.im|) * 8 := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            simpa [one_div] using hsinv
        _ = 8 * (1 + |s.im|) := by ring
    have hmain : 2 * (N:ℝ) * ‖s‖ / s.re ≤ 16 * (N:ℝ) * (1 + |s.im|) := by
      calc 2 * (N:ℝ) * ‖s‖ / s.re = 2 * (N:ℝ) * (‖s‖ / s.re) := by ring
        _ ≤ 2 * (N:ℝ) * (8 * (1 + |s.im|)) := by
              exact mul_le_mul_of_nonneg_left hdiv (by positivity)
        _ = 16 * (N:ℝ) * (1 + |s.im|) := by ring
    calc ‖χ.LFunction s‖ ≤ 2 * (N:ℝ) * ‖s‖ / s.re := hb
      _ ≤ 16 * (N:ℝ) * (1 + |s.im|) := hmain
      _ ≤ 16 * (N:ℝ) * (1 + |s.im|) + Real.log (N:ℝ) + Real.log (2 + |s.im|) + 6 := by
          have hlogN : 0 ≤ Real.log (N:ℝ) := Real.log_nonneg hN1
          have hlog2 : 0 ≤ Real.log (2 + |s.im|) := Real.log_nonneg (by linarith [abs_nonneg s.im])
          linarith
  · have h1' : 1 ≤ s.re := le_of_lt (not_le.mp h1)
    have hb := norm_LFunction_le_re_ge_one χ hχ s h1'
    have hnn : (0:ℝ) ≤ 16 * (N:ℝ) * (1 + |s.im|) := by positivity
    linarith [hb, hnn]

lemma LFunction_bound_region' {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    {s : ℂ} {T : ℝ} (hlo : 1/8 ≤ s.re) (him : |s.im| ≤ T + 2) (hT : 2 ≤ T) :
    ‖χ.LFunction s‖ ≤ 26 * (N:ℝ) * (T + 3) := by
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hb := LFunction_bound_region χ hχ hlo
  have h1 : 16 * (N:ℝ) * (1 + |s.im|) ≤ 16 * (N:ℝ) * (T+3) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith
  have h2 : Real.log (N:ℝ) ≤ (N:ℝ) * (T+3) := by
    have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < (N:ℝ) by positivity)
    nlinarith [hN1, hT, h]
  have h3 : Real.log (2 + |s.im|) ≤ 3 * ((N:ℝ) * (T+3)) := by
    have hpos : 0 < 2 + |s.im| := by linarith [abs_nonneg s.im]
    have hl : Real.log (2 + |s.im|) ≤ 2 + |s.im| - 1 := Real.log_le_sub_one_of_pos hpos
    have hT3 : (0:ℝ) < T + 3 := by linarith
    have hNt : T + 3 ≤ (N:ℝ) * (T+3) := by nlinarith [hN1, hT3]
    nlinarith [hl, him, hNt]
  have h4 : (6:ℝ) ≤ 6 * ((N:ℝ) * (T+3)) := by
    have hp : 1 ≤ (N:ℝ) * (T+3) := by nlinarith [hN1, hT]
    linarith
  linarith [hb, h1, h2, h3, h4]

lemma reZeroFun_bound {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (T : ℝ) (hT : 2 ≤ T) {z : ℂ} (hz : z ∈ Metric.sphere (2:ℂ) (15/8)) :
    ‖reZeroFun χ T z‖ ≤ 52 * (N:ℝ) * (T + 3) := by
  have hdist : ‖z - 2‖ = 15/8 := by
    rw [Metric.mem_sphere, dist_eq_norm] at hz; exact hz
  have hre_lo : (1/8:ℝ) ≤ z.re := by
    have h := Complex.abs_re_le_norm (z - 2)
    rw [Complex.sub_re, hdist] at h
    have h2 : (2:ℂ).re = 2 := by norm_num
    rw [h2] at h
    have := (abs_le.mp h).1
    linarith
  have him : |z.im| ≤ 15/8 := by
    have h := Complex.abs_im_le_norm (z - 2)
    rw [Complex.sub_im, hdist] at h
    have h2 : (2:ℂ).im = 0 := by norm_num
    rw [h2, sub_zero] at h
    exact h
  have hre_lo1 : (1/8:ℝ) ≤ (z + (T:ℂ)*Complex.I).re := by
    rw [show (z + (T:ℂ)*Complex.I).re = z.re by simp]; exact hre_lo
  have him1 : |(z + (T:ℂ)*Complex.I).im| ≤ T + 2 := by
    rw [show (z + (T:ℂ)*Complex.I).im = z.im + T by simp]
    have hab := abs_le.mp him
    rw [abs_le]
    constructor <;> linarith [hab.1, hab.2, hT]
  have hre_lo2 : (1/8:ℝ) ≤ (z - (T:ℂ)*Complex.I).re := by
    rw [show (z - (T:ℂ)*Complex.I).re = z.re by simp]; exact hre_lo
  have him2 : |(z - (T:ℂ)*Complex.I).im| ≤ T + 2 := by
    rw [show (z - (T:ℂ)*Complex.I).im = z.im - T by simp]
    have hab := abs_le.mp him
    rw [abs_le]
    constructor <;> linarith [hab.1, hab.2, hT]
  have h1 : ‖χ.LFunction (z + (T:ℂ)*Complex.I)‖ ≤ 26 * (N:ℝ) * (T + 3) :=
    LFunction_bound_region' χ hχ hre_lo1 him1 hT
  have h2 : ‖(χ⁻¹).LFunction (z - (T:ℂ)*Complex.I)‖ ≤ 26 * (N:ℝ) * (T + 3) :=
    LFunction_bound_region' (χ⁻¹) (chiInv_ne_one hχ) hre_lo2 him2 hT
  rw [reZeroFun_apply]
  calc ‖χ.LFunction (z + (T:ℂ)*Complex.I) + (χ⁻¹).LFunction (z - (T:ℂ)*Complex.I)‖
      ≤ ‖χ.LFunction (z + (T:ℂ)*Complex.I)‖ + ‖(χ⁻¹).LFunction (z - (T:ℂ)*Complex.I)‖ :=
        norm_add_le _ _
    _ ≤ 26 * (N:ℝ) * (T + 3) + 26 * (N:ℝ) * (T + 3) := add_le_add h1 h2
    _ = 52 * (N:ℝ) * (T + 3) := by ring

private lemma divisor_ne_zero_of_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hne : f 2 ≠ 0)
    {u : ℂ} (hu : u ∈ Metric.closedBall (2:ℂ) (3/2)) (hfu : f u = 0) :
    MeromorphicOn.divisor f (Metric.closedBall (2:ℂ) (3/2)) u ≠ 0 := by
  have hAn : AnalyticOnNhd ℂ f (Metric.closedBall (2:ℂ) (3/2)) := fun z _ => hf.analyticAt z
  have horder : ∀ v : ↥(Metric.closedBall (2:ℂ) (3/2)), meromorphicOrderAt f v.1 ≠ ⊤ := by
    intro v hv
    rw [(hf.analyticAt v.1).meromorphicOrderAt_eq] at hv
    rw [ENat.map_eq_top_iff] at hv
    rw [analyticOrderAt_eq_top] at hv
    have hAnU : AnalyticOnNhd ℂ f Set.univ := fun z _ => hf.analyticAt z
    have hEq : Set.EqOn f 0 Set.univ :=
      hAnU.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ v.1) hv
    exact hne (hEq (Set.mem_univ 2))
  have hsupp := MeromorphicNFOn.zero_set_eq_divisor_support hAn.meromorphicNFOn horder
  have hmem : u ∈ Metric.closedBall (2:ℂ) (3/2) ∩ f ⁻¹' {0} := ⟨hu, by simpa using hfu⟩
  rw [hsupp] at hmem
  rwa [Function.mem_support] at hmem

private lemma divisor_cast_nonneg {f : ℂ → ℂ} {U : Set ℂ} (hf : AnalyticOnNhd ℂ f U) (u : ℂ) :
    (0 : ℝ) ≤ ((MeromorphicOn.divisor f U u : ℤ) : ℝ) := by
  have h := MeromorphicOn.AnalyticOnNhd.divisor_nonneg hf
  exact_mod_cast (h u)

private lemma divisor_cast_finiteSupport (f : ℂ → ℂ) (c : ℂ) (R : ℝ) :
    Function.HasFiniteSupport
      (fun u : ℂ => ((MeromorphicOn.divisor f (Metric.closedBall c R) u : ℤ) : ℝ)) := by
  have hfinZ : (Function.support
      (fun u : ℂ => (MeromorphicOn.divisor f (Metric.closedBall c R) u : ℤ))).Finite := by
    simpa [Function.HasFiniteSupport] using
      ((MeromorphicOn.divisor f (Metric.closedBall c R)).finiteSupport (isCompact_closedBall c R))
  refine hfinZ.subset ?_
  intro u hu
  rw [Function.mem_support] at hu ⊢
  exact fun hz => hu (by exact_mod_cast hz)

theorem reZeros_finset_log_bound {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∃ Z : Finset ℝ,
      (∀ z ∈ Z, z ∈ Set.Icc (1 / 2) 2) ∧
      (∀ σ : ℝ, σ ∈ Set.Icc (1 / 2) 2 →
        (DirichletCharacter.LFunction χ ((σ : ℂ) + (T : ℂ) * Complex.I)).re = 0 → σ ∈ Z) ∧
      (Z.card : ℝ) ≤ C * Real.log ((N : ℝ) * (T + 3)) := by
  classical
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  refine ⟨(1 + Real.log 104 / Real.log 5) / Real.log (5/4), ?_, ?_⟩
  · have h5 : 0 < Real.log 5 := Real.log_pos (by norm_num)
    have h54 : 0 < Real.log (5/4) := Real.log_pos (by norm_num)
    have hnum : 0 < 1 + Real.log 104 / Real.log 5 := by positivity
    exact div_pos hnum h54
  · intro T hT
    have hAnU : AnalyticOnNhd ℂ (reZeroFun χ T) Set.univ :=
      fun z _ => (reZeroFun_differentiable χ hχ T).analyticAt z
    have hAn32 : AnalyticOnNhd ℂ (reZeroFun χ T) (Metric.closedBall (2:ℂ) (3/2)) :=
      hAnU.mono (Set.subset_univ _)
    have hre2 : (1:ℝ)/4 ≤ (χ.LFunction (((2:ℝ):ℂ) + (T:ℂ) * Complex.I)).re :=
      LFunction_re_lower_of_two_le_re χ hχ (by simp)
    have h2ne : reZeroFun χ T 2 ≠ 0 := by
      change reZeroFun χ T ((2:ℝ):ℂ) ≠ 0
      rw [reZeroFun_apply_ofReal χ hχ T 2, ne_eq, Complex.ofReal_eq_zero]
      linarith
    have h2norm : ‖reZeroFun χ T 2‖ = 2 * (χ.LFunction (((2:ℝ):ℂ) + (T:ℂ) * Complex.I)).re := by
      change ‖reZeroFun χ T ((2:ℝ):ℂ)‖ = 2 * (χ.LFunction (((2:ℝ):ℂ) + (T:ℂ) * Complex.I)).re
      rw [reZeroFun_apply_ofReal χ hχ T 2, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by linarith)]
    have hM1 : (1:ℝ) ≤ 52 * (N:ℝ) * (T + 3) := by nlinarith [hN1, hT]
    have hRabs : |(15:ℝ)/8| = 15/8 := abs_of_nonneg (by norm_num)
    have hJ := AnalyticOnNhd.sum_divisor_le (c := (2:ℂ)) (r := (3/2:ℝ)) (R := (15/8:ℝ))
      (M := 52 * (N:ℝ) * (T + 3)) (f := reZeroFun χ T)
      (by norm_num) (by norm_num) hM1
      (hAnU.mono (Set.subset_univ _))
      h2ne
      (fun z hz => reZeroFun_bound χ hχ T hT (by rw [hRabs] at hz; exact hz))
    rw [show |(3:ℝ)/2| = (3:ℝ)/2 by norm_num] at hJ
    have hrr : (15:ℝ)/8 / (3/2) = 5/4 := by norm_num
    rw [hrr] at hJ
    have hquot : 52 * (N:ℝ) * (T+3) / ‖reZeroFun χ T 2‖ ≤ 104 * ((N:ℝ) * (T+3)) := by
      rw [h2norm]
      have hge : (1:ℝ)/2 ≤ 2 * (χ.LFunction (((2:ℝ):ℂ) + (T:ℂ)*Complex.I)).re := by linarith
      have hinv : (2 * (χ.LFunction (((2:ℝ):ℂ) + (T:ℂ)*Complex.I)).re)⁻¹ ≤ (1/2:ℝ)⁻¹ :=
        inv_anti₀ (by norm_num) hge
      calc 52 * (N:ℝ) * (T+3) / (2 * (χ.LFunction (((2:ℝ):ℂ)+(T:ℂ)*Complex.I)).re)
          = 52 * (N:ℝ) * (T+3) * (2 * (χ.LFunction (((2:ℝ):ℂ)+(T:ℂ)*Complex.I)).re)⁻¹ := by
              rw [div_eq_mul_inv]
        _ ≤ 52 * (N:ℝ) * (T+3) * (1/2:ℝ)⁻¹ :=
              mul_le_mul_of_nonneg_left hinv (by positivity)
        _ = 104 * ((N:ℝ) * (T+3)) := by norm_num; ring
    have hlogbound : Real.log (52 * (N:ℝ) * (T+3) / ‖reZeroFun χ T 2‖) ≤
        Real.log 104 + Real.log ((N:ℝ) * (T+3)) := by
      rw [← Real.log_mul (by norm_num) (by positivity)]
      exact Real.log_le_log (by positivity) hquot
    have hL : 0 < Real.log (5/4) := Real.log_pos (by norm_num)
    set D : ℂ → ℤ :=
      (fun u => MeromorphicOn.divisor (reZeroFun χ T) (Metric.closedBall (2:ℂ) (3/2)) u) with hDdef
    have hJ' : (↑(∑ᶠ u : ℂ, D u) : ℝ) ≤
        (Real.log 104 + Real.log ((N:ℝ) * (T+3))) / Real.log (5/4) := by
      refine le_trans hJ (div_le_div_of_nonneg_right hlogbound (le_of_lt hL))
    have hDnn : ∀ u, (0:ℝ) ≤ (D u : ℝ) := fun u => by
      simpa [hDdef] using divisor_cast_nonneg hAn32 u
    have hDfin : Function.HasFiniteSupport (fun u => (D u : ℝ)) := by
      simpa [hDdef] using divisor_cast_finiteSupport (reZeroFun χ T) (2:ℂ) (3/2)
    have hDfinZ : Function.HasFiniteSupport D := by
      rw [hDdef]
      simpa [Function.HasFiniteSupport] using (MeromorphicOn.divisor (reZeroFun χ T)
        (Metric.closedBall (2:ℂ) (3/2))).finiteSupport (isCompact_closedBall (2:ℂ) (3/2))
    set A : Finset ℂ := (hDfin.toFinset).filter (fun u => u.im = 0 ∧ 1/2 ≤ u.re ∧ u.re ≤ 2) with hAdef
    have hA1 : ∀ u ∈ A, (1:ℝ) ≤ (D u : ℝ) := by
      intro u hu
      have huF : u ∈ (hDfin.toFinset).filter (fun u => u.im = 0 ∧ 1/2 ≤ u.re ∧ u.re ≤ 2) := by
        rw [hAdef] at hu; exact hu
      obtain ⟨huS, _⟩ := Finset.mem_filter.mp huF
      have hmem : u ∈ Function.support (fun u => (D u : ℝ)) := hDfin.mem_toFinset.mp huS
      rw [Function.mem_support] at hmem
      have hint : (0:ℤ) ≤ D u := by
        simpa [hDdef] using MeromorphicOn.AnalyticOnNhd.divisor_nonneg hAn32 u
      have hne0 : D u ≠ 0 := fun h => hmem (by rw [h]; norm_num)
      have hge : (1:ℤ) ≤ D u := by omega
      exact_mod_cast hge
    have hcard := Commons.Algebra.BigOperators.card_le_finsum_of_one_le hDnn hDfin A hA1
    have hcast : (∑ᶠ u : ℂ, (D u : ℝ)) = (↑(∑ᶠ u : ℂ, D u) : ℝ) :=
      (map_finsum (Int.castRingHom ℝ) hDfinZ).symm
    have hcard' : (A.card : ℝ) ≤ (Real.log 104 + Real.log ((N:ℝ) * (T+3))) / Real.log (5/4) := by
      calc (A.card : ℝ) ≤ ∑ᶠ u : ℂ, (D u : ℝ) := hcard
        _ = (↑(∑ᶠ u : ℂ, D u) : ℝ) := hcast
        _ ≤ _ := hJ'
    set Z : Finset ℝ := A.image (fun u => u.re) with hZdef
    have hZcard : Z.card = A.card := by
      rw [hZdef]
      apply Finset.card_image_of_injOn
      intro u hu v hv huv
      have huF : u ∈ (hDfin.toFinset).filter (fun u => u.im = 0 ∧ 1/2 ≤ u.re ∧ u.re ≤ 2) := by
        rw [hAdef] at hu; exact hu
      have hvF : v ∈ (hDfin.toFinset).filter (fun u => u.im = 0 ∧ 1/2 ≤ u.re ∧ u.re ≤ 2) := by
        rw [hAdef] at hv; exact hv
      exact Complex.ext huv
        (by rw [(Finset.mem_filter.mp huF).2.1, (Finset.mem_filter.mp hvF).2.1])
    have hZle : (Z.card : ℝ) ≤ (Real.log 104 + Real.log ((N:ℝ) * (T+3))) / Real.log (5/4) := by
      rw [hZcard]; exact hcard'
    have hfinal : (Real.log 104 + Real.log ((N:ℝ) * (T+3))) / Real.log (5/4) ≤
        ((1 + Real.log 104 / Real.log 5) / Real.log (5/4)) * Real.log ((N:ℝ) * (T+3)) := by
      have h5 : 0 < Real.log 5 := Real.log_pos (by norm_num)
      have hu5 : (5:ℝ) ≤ (N:ℝ) * (T+3) := by nlinarith [hN1, hT]
      have hlogu : Real.log 5 ≤ Real.log ((N:ℝ) * (T+3)) := Real.log_le_log (by norm_num) hu5
      have h104 : 0 ≤ Real.log 104 := Real.log_nonneg (by norm_num)
      have key : Real.log 104 ≤ (Real.log 104 / Real.log 5) * Real.log ((N:ℝ) * (T+3)) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ h5]
        exact mul_le_mul_of_nonneg_left hlogu h104
      rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hL]
      rw [add_mul, one_mul]
      linarith [key]
    refine ⟨Z, ?_, ?_, ?_⟩
    · intro z hz
      have hz' : z ∈ A.image (fun u => u.re) := by rw [hZdef] at hz; exact hz
      obtain ⟨u, huA, rfl⟩ := Finset.mem_image.mp hz'
      have huF : u ∈ (hDfin.toFinset).filter (fun u => u.im = 0 ∧ 1/2 ≤ u.re ∧ u.re ≤ 2) := by
        rw [hAdef] at huA; exact huA
      exact (Finset.mem_filter.mp huF).2.2
    · intro σ hσ hσzero
      have hσh : reZeroFun χ T (σ:ℂ) = 0 := by
        rw [reZeroFun_apply_ofReal χ hχ T σ, hσzero]
        simp
      have hσball : (σ:ℂ) ∈ Metric.closedBall (2:ℂ) (3/2) := by
        rw [Metric.mem_closedBall, dist_eq_norm]
        have h : ‖(σ:ℂ) - 2‖ = |σ - 2| := by
          rw [show (σ:ℂ) - 2 = ((σ - 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
            Real.norm_eq_abs]
        rw [h, abs_le]
        constructor <;> linarith [hσ.1, hσ.2]
      have hDne : D (σ:ℂ) ≠ 0 := by
        have h := divisor_ne_zero_of_zero (reZeroFun_differentiable χ hχ T) h2ne hσball hσh
        simpa [hDdef] using h
      have hσsupp : (σ:ℂ) ∈ Function.support (fun u => (D u : ℝ)) := by
        rw [Function.mem_support]
        exact fun h => hDne (by exact_mod_cast h)
      have hσS : (σ:ℂ) ∈ hDfin.toFinset := hDfin.mem_toFinset.mpr hσsupp
      have hσA : (σ:ℂ) ∈ A := by
        rw [hAdef, Finset.mem_filter]
        exact ⟨hσS, by simp, by simpa using hσ.1, by simpa using hσ.2⟩
      have hz' : (σ:ℂ).re ∈ A.image (fun u => u.re) := Finset.mem_image.mpr ⟨(σ:ℂ), hσA, rfl⟩
      rw [hZdef]
      simpa using hz'
    · calc (Z.card : ℝ) ≤ (Real.log 104 + Real.log ((N:ℝ) * (T+3))) / Real.log (5/4) := hZle
        _ ≤ _ := hfinal

end Commons.NumberTheory.DirichletCharacter
