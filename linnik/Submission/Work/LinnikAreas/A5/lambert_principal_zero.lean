import Mathlib
import Submission.Commons.NumberTheory.Zeta.chebyshev_psi_sub_id_exp
import Submission.Work.LinnikAreas.A5.lambert_defs
import Submission.Work.LinnikAreas.A5.psi_sub_id_exp_bound
import Submission.Work.LinnikAreas.A5.psi_abel_integral
import Submission.Work.LinnikAreas.A5.integral_rpow_log_subst
import Submission.Work.LinnikAreas.A5.integral_exp_neg_sqrt_log_rpow_le
import Submission.Work.LinnikAreas.A5.lamWeight_calculus
import Submission.Work.LinnikAreas.A5.tsum_lamWeight_eq_sum
import Submission.Work.LinnikAreas.A5.integral_exp_neg_sqrt_rpow_le

open scoped BigOperators Interval
open MeasureTheory Set Finset

set_option maxHeartbeats 4000000

namespace Work.LinnikAreas.A5

noncomputable section

/-! ## Elementary calculus of the weight `t ↦ t^{-σ} f(log t / log q)` -/

/-- The weight `lamWeight q lam f` is continuous on `[1,∞)`. -/
lemma continuousOn_lamWeight {q lam : ℝ} (hq : 1 < q) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Ici 0)) :
    ContinuousOn (lamWeight q lam f) (Set.Ici 1) := by
  have hLpos : 0 < Real.log q := Real.log_pos hq
  have hrpow : ContinuousOn (fun t : ℝ => t ^ (-(1 - lam / Real.log q))) (Set.Ici (1:ℝ)) :=
    ContinuousOn.rpow_const continuous_id.continuousOn
      (fun t ht => Or.inl (ne_of_gt (lt_of_lt_of_le zero_lt_one ht)))
  have hlog : ContinuousOn (fun t : ℝ => Real.log t / Real.log q) (Set.Ici (1:ℝ)) :=
    (Real.continuousOn_log.mono (fun t ht => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact ne_of_gt (lt_of_lt_of_le zero_lt_one ht))).div_const (Real.log q)
  have hmem : MapsTo (fun t : ℝ => Real.log t / Real.log q) (Set.Ici (1:ℝ)) (Set.Ici (0:ℝ)) :=
    fun t ht => div_nonneg (Real.log_nonneg ht) hLpos.le
  have hcomp : ContinuousOn (fun t : ℝ => f (Real.log t / Real.log q)) (Set.Ici (1:ℝ)) :=
    hf.comp hlog hmem
  show ContinuousOn (fun t : ℝ => t ^ (-(1 - lam / Real.log q)) * f (Real.log t / Real.log q))
    (Set.Ici 1)
  exact hrpow.mul hcomp

/-- `deriv (lamWeight q lam f)` is interval-integrable on `[1,N]` when `N ≤ q^{x₀}`. -/
lemma intervalIntegrable_deriv_lamWeight {x₀ q lam M M' : ℝ} {f : ℝ → ℝ} {N : ℕ}
    (hx₀ : 0 < x₀) (hq : 1 < q) (hσ : 0 ≤ 1 - lam / Real.log q)
    (hM0 : 0 ≤ M) (hM'0 : 0 ≤ M') (hf : ContDiffOn ℝ 1 f (Set.Ioo 0 x₀))
    (hM : ∀ t : ℝ, ‖f t‖ ≤ M) (hM' : ∀ t ∈ Set.Icc (0:ℝ) x₀, ‖deriv f t‖ ≤ M')
    (hN1 : 1 ≤ N) (hNT : (N:ℝ) ≤ q ^ x₀) :
    IntervalIntegrable (deriv (lamWeight q lam f)) volume (1:ℝ) (N:ℝ) := by
  have hN1' : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN1
  have hb := (lamWeight_calculus (x₀ := x₀) (q := q) (lam := lam) (M := M) (M' := M')
    hx₀ hq hσ hM0 hM'0 hf hM hM').2
  have hmaj : IntervalIntegrable
      (fun t : ℝ => t ^ (-(1 - lam / Real.log q) - 1) * ((1 - lam / Real.log q) * M + M' / Real.log q))
      volume (1:ℝ) (N:ℝ) := by
    refine ContinuousOn.intervalIntegrable_of_Icc hN1' (ContinuousOn.mul ?_ continuousOn_const)
    refine ContinuousOn.rpow_const continuous_id.continuousOn (fun t ht => Or.inl ?_)
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one (Set.mem_Icc.mp ht).1)
  refine IntervalIntegrable.mono_fun' hmaj (measurable_deriv _).aestronglyMeasurable ?_
  rw [Set.uIoc_of_le hN1']
  simp only [Filter.EventuallyLE]
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
  filter_upwards [MeasureTheory.Measure.ae_ne volume (q ^ x₀)] with t htne htmem
  exact hb t ⟨htmem.1, lt_of_le_of_ne (le_trans htmem.2 hNT) htne⟩

/-- `ψ · deriv (lamWeight ...)` is interval-integrable on `[1,N]`. -/
lemma intervalIntegrable_psi_mul_deriv_lamWeight {x₀ q lam M M' : ℝ} {f : ℝ → ℝ} {N : ℕ}
    (hx₀ : 0 < x₀) (hq : 1 < q) (hσ : 0 ≤ 1 - lam / Real.log q)
    (hM0 : 0 ≤ M) (hM'0 : 0 ≤ M') (hf : ContDiffOn ℝ 1 f (Set.Ioo 0 x₀))
    (hM : ∀ t : ℝ, ‖f t‖ ≤ M) (hM' : ∀ t ∈ Set.Icc (0:ℝ) x₀, ‖deriv f t‖ ≤ M')
    (hN1 : 1 ≤ N) (hNT : (N:ℝ) ≤ q ^ x₀) :
    IntervalIntegrable
      (fun t : ℝ => Chebyshev.psi t * deriv (lamWeight q lam f) t) volume (1:ℝ) (N:ℝ) := by
  have hN1' : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN1
  have hb := (lamWeight_calculus (x₀ := x₀) (q := q) (lam := lam) (M := M) (M' := M')
    hx₀ hq hσ hM0 hM'0 hf hM hM').2
  have hmaj : IntervalIntegrable
      (fun t : ℝ => (Real.log 4 + 4) * (((1 - lam / Real.log q) * M + M' / Real.log q) *
        t ^ (-(1 - lam / Real.log q)))) volume (1:ℝ) (N:ℝ) := by
    refine ContinuousOn.intervalIntegrable_of_Icc hN1' (ContinuousOn.mul continuousOn_const ?_)
    refine ContinuousOn.mul continuousOn_const ?_
    refine ContinuousOn.rpow_const continuous_id.continuousOn (fun t ht => Or.inl ?_)
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one (Set.mem_Icc.mp ht).1)
  refine IntervalIntegrable.mono_fun' hmaj
    ((Chebyshev.psi_mono.measurable).mul (measurable_deriv _)).aestronglyMeasurable ?_
  rw [Set.uIoc_of_le hN1']
  simp only [Filter.EventuallyLE]
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
  filter_upwards [MeasureTheory.Measure.ae_ne volume (q ^ x₀)] with t htne htmem
  have htT : t < q ^ x₀ := lt_of_le_of_ne (le_trans htmem.2 hNT) htne
  have hbnd := hb t ⟨htmem.1, htT⟩
  have htp : 0 < t := lt_trans zero_lt_one htmem.1
  have hpsib : ‖Chebyshev.psi t‖ ≤ (Real.log 4 + 4) * t := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Chebyshev.psi_nonneg t)]
    exact Chebyshev.psi_le_const_mul_self (by linarith only [htp])
  have hrpow : t * t ^ (-(1 - lam / Real.log q) - 1) = t ^ (-(1 - lam / Real.log q)) := by
    calc t * t ^ (-(1 - lam / Real.log q) - 1)
        = t ^ (1:ℝ) * t ^ (-(1 - lam / Real.log q) - 1) := by rw [Real.rpow_one]
      _ = t ^ ((1:ℝ) + (-(1 - lam / Real.log q) - 1)) := by rw [Real.rpow_add htp]
      _ = t ^ (-(1 - lam / Real.log q)) := by congr 1; ring
  rw [norm_mul]
  calc ‖Chebyshev.psi t‖ * ‖deriv (lamWeight q lam f) t‖
      ≤ ((Real.log 4 + 4) * t) *
          (t ^ (-(1 - lam / Real.log q) - 1) * ((1 - lam / Real.log q) * M + M' / Real.log q)) :=
        mul_le_mul hpsib hbnd (norm_nonneg _) (by positivity)
    _ = (Real.log 4 + 4) * (((1 - lam / Real.log q) * M + M' / Real.log q) *
          t ^ (-(1 - lam / Real.log q))) := by
        rw [← hrpow]; ring

/-! ## The main theorem -/

/-
Same as `LinnikAreas/A5/lambert_principal_uniform` but with `0 ≤ lam` instead of `0 < lam`
(the λ = 0 endpoint is needed for the λ = 0 case of HB 13.3, where the weight is the "limit"
test function `g0 K t = (K-t)/K`).  For a continuous weight `f` supported in `[0,x₀]` with
`‖f‖ ≤ M`, `‖f'‖ ≤ M'`, and `σ = 1 - lam/log q`:

  (1/log q)·Σ_n Λ(n) n^{-σ} f(log n / log q) ≤ ∫₀^{x₀} e^{lam u} f(u) du + O((M+M')/log q),

uniformly in lam ∈ [0, R] and in f.
-/
theorem lambert_principal_zero (x₀ R : ℝ) (hx₀ : 0 < x₀) (hR : 0 < R) :
    ∃ C : ℝ, 0 < C ∧ ∃ q₀ : ℕ, ∀ {q : ℕ}, q₀ ≤ q →
    ∀ {f : ℝ → ℝ} {M M' : ℝ}, 0 ≤ M → 0 ≤ M' →
      ContinuousOn f (Set.Ici 0) → (∀ t : ℝ, x₀ ≤ t → f t = 0) →
      ContDiffOn ℝ 1 f (Set.Ioo 0 x₀) →
      (∀ t : ℝ, ‖f t‖ ≤ M) → (∀ t ∈ Set.Icc (0:ℝ) x₀, ‖deriv f t‖ ≤ M') →
      ∀ lam : ℝ, 0 ≤ lam → lam ≤ R →
        (Real.log q)⁻¹ * (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
            (n : ℝ) ^ (-(1 - lam / Real.log q)) * f (Real.log n / Real.log q))
          ≤ (∫ u in (0:ℝ)..x₀, Real.exp (lam * u) * f u) + C * (M + M') / Real.log q := by
  obtain ⟨K, c, hKpos, hcpos, hpsi⟩ := psi_sub_id_exp_bound
  set C₀ : ℝ := K * Real.exp (R * x₀) + 2 + K * (2 * Real.exp (R * x₀) / c ^ 2) * 2 with hC₀def
  have hC₀pos : 0 < C₀ := by
    rw [hC₀def]; positivity
  refine ⟨C₀, hC₀pos, max 3 (⌊Real.exp (2 * R)⌋₊ + 3), ?_⟩
  intro q hq f M M' hM0 hM'0 hcont hsupp hf2 hM hM' lam hlam0 hlamR
  -- ## numeric preliminaries
  have hq3 : 3 ≤ q := le_trans (le_max_left 3 _) hq
  have hq1 : (1:ℝ) < (q:ℝ) := by exact_mod_cast (by omega : 1 < q)
  have hq0 : (0:ℝ) < (q:ℝ) := lt_trans zero_lt_one hq1
  have hLpos : 0 < Real.log (q:ℝ) := Real.log_pos hq1
  have hL1 : 1 ≤ Real.log (q:ℝ) := by
    rw [Real.le_log_iff_exp_le hq0]
    have h3 : (3:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq3
    linarith only [Real.exp_one_lt_three, h3]
  have hL2R : 2 * R ≤ Real.log (q:ℝ) := by
    rw [Real.le_log_iff_exp_le hq0]
    have h3 : (⌊Real.exp (2 * R)⌋₊ : ℝ) + 3 ≤ (q:ℝ) := by
      exact_mod_cast (le_trans (le_max_right 3 (⌊Real.exp (2*R)⌋₊ + 3)) hq :
        ⌊Real.exp (2 * R)⌋₊ + 3 ≤ q)
    linarith only [Nat.lt_floor_add_one (Real.exp (2 * R)), h3]
  have hσ0 : 0 ≤ 1 - lam / Real.log (q:ℝ) := by
    rw [sub_nonneg, div_le_one hLpos]
    linarith only [hR, hlamR, hL2R]
  have hσhalf : (1:ℝ)/2 ≤ 1 - lam / Real.log (q:ℝ) := by
    have h : lam / Real.log (q:ℝ) ≤ 1/2 := by
      rw [div_le_iff₀ hLpos]; linarith only [hlamR, hL2R]
    linarith only [h]
  -- ## the cutoff `N` and the weight `G`
  set N : ℕ := ⌊(q:ℝ) ^ x₀⌋₊ with hNdef
  have hT1 : (1:ℝ) ≤ (q:ℝ) ^ x₀ := Real.one_le_rpow hq1.le hx₀.le
  have hTpos : (0:ℝ) < (q:ℝ) ^ x₀ := lt_of_lt_of_le zero_lt_one hT1
  have hN1 : 1 ≤ N := by
    rw [hNdef, Nat.one_le_floor_iff]; exact hT1
  have hN1' : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN1
  have hNpos : (0:ℝ) < (N:ℝ) := lt_of_lt_of_le zero_lt_one hN1'
  have hNT : (N:ℝ) ≤ (q:ℝ) ^ x₀ := by
    rw [hNdef]; exact Nat.floor_le hTpos.le
  have hTN : (q:ℝ) ^ x₀ - (N:ℝ) ≤ 1 := by
    have h := Nat.lt_floor_add_one ((q:ℝ) ^ x₀)
    rw [← hNdef] at h; linarith only [h]
  set G : ℝ → ℝ := lamWeight (q:ℝ) lam f with hGdef
  have hGcontT : ContinuousOn G (Set.Icc (1:ℝ) ((q:ℝ)^x₀)) := by
    rw [hGdef]
    exact (continuousOn_lamWeight hq1 hcont).mono (fun t ht => ht.1)
  have hGcontN : ContinuousOn G (Set.Icc (1:ℝ) (N:ℝ)) :=
    hGcontT.mono (Set.Icc_subset_Icc le_rfl hNT)
  have hGintT : IntervalIntegrable G volume (1:ℝ) ((q:ℝ)^x₀) :=
    ContinuousOn.intervalIntegrable_of_Icc hT1 hGcontT
  have hGintN : IntervalIntegrable G volume (1:ℝ) (N:ℝ) :=
    ContinuousOn.intervalIntegrable_of_Icc hN1' hGcontN
  have hGintNT : IntervalIntegrable G volume (N:ℝ) ((q:ℝ)^x₀) :=
    ContinuousOn.intervalIntegrable_of_Icc hNT (hGcontT.mono (Set.Icc_subset_Icc hN1' le_rfl))
  have hcal := lamWeight_calculus (x₀ := x₀) (q := (q:ℝ)) (lam := lam) (M := M) (M' := M')
    hx₀ hq1 hσ0 hM0 hM'0 hf2 hM hM'
  have hGderiv : ∀ t ∈ Set.Ioo (1:ℝ) (N:ℝ), HasDerivAt G (deriv G t) t := by
    intro t ht
    have htT : t ∈ Set.Ioo (1:ℝ) ((q:ℝ)^x₀) := ⟨ht.1, lt_of_lt_of_le ht.2 hNT⟩
    rw [hGdef]
    exact (hcal.1 t htT).differentiableAt.hasDerivAt
  have hgderiv : IntervalIntegrable (deriv G) volume (1:ℝ) (N:ℝ) := by
    rw [hGdef]
    exact intervalIntegrable_deriv_lamWeight hx₀ hq1 hσ0 hM0 hM'0 hf2 hM hM' hN1 hNT
  have hgpsi : IntervalIntegrable (fun t : ℝ => Chebyshev.psi t * deriv G t) volume (1:ℝ) (N:ℝ) := by
    rw [hGdef]
    exact intervalIntegrable_psi_mul_deriv_lamWeight hx₀ hq1 hσ0 hM0 hM'0 hf2 hM hM' hN1 hNT
  have hgid_raw : IntervalIntegrable (fun t : ℝ => deriv G t * t) volume (1:ℝ) (N:ℝ) :=
    hgderiv.mul_continuousOn continuous_id.continuousOn
  have hgid : IntervalIntegrable (fun t : ℝ => t * deriv G t) volume (1:ℝ) (N:ℝ) :=
    hgid_raw.congr (fun t _ => by ring)
  have hgR : IntervalIntegrable (fun t : ℝ => (Chebyshev.psi t - t) * deriv G t)
      volume (1:ℝ) (N:ℝ) :=
    (hgpsi.sub hgid).congr (fun t _ => by ring)
  -- ## Abel summation
  have habel := psi_abel_integral N G hN1 hGcontN
    (fun t ht => (hGderiv t ht).differentiableAt) hgpsi hgderiv
  -- ## integral splitting and integration by parts
  have hsplit : (∫ t in (1:ℝ)..(N:ℝ), Chebyshev.psi t * deriv G t)
      = (∫ t in (1:ℝ)..(N:ℝ), t * deriv G t)
        + (∫ t in (1:ℝ)..(N:ℝ), (Chebyshev.psi t - t) * deriv G t) := by
    rw [← intervalIntegral.integral_add hgid hgR]
    exact intervalIntegral.integral_congr (fun t _ => by ring)
  have hibp : (∫ t in (1:ℝ)..(N:ℝ), t * deriv G t)
      = (N:ℝ) * G (N:ℝ) - G 1 - (∫ t in (1:ℝ)..(N:ℝ), G t) := by
    have hminmax : Set.Ioo (min (1:ℝ) (N:ℝ)) (max (1:ℝ) (N:ℝ)) = Set.Ioo (1:ℝ) (N:ℝ) := by
      rw [min_eq_left hN1', max_eq_right hN1']
    have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
      (a := (1:ℝ)) (b := (N:ℝ)) (u := fun x : ℝ => x) (u' := fun _ : ℝ => (1:ℝ))
      (v := G) (v' := deriv G)
      (continuous_id.continuousOn) (by rw [Set.uIcc_of_le hN1']; exact hGcontN)
      (fun x hx => by rw [hminmax] at hx; exact hasDerivAt_id x)
      (fun x hx => by rw [hminmax] at hx; exact hGderiv x hx)
      intervalIntegrable_const hgderiv
    have h' : (∫ x in (1:ℝ)..(N:ℝ), x * deriv G x)
        = (N:ℝ) * G (N:ℝ) - (1:ℝ) * G 1 - ∫ x in (1:ℝ)..(N:ℝ), (1:ℝ) * G x := by
      simpa using h
    have h1 : (∫ x in (1:ℝ)..(N:ℝ), (1:ℝ) * G x) = ∫ x in (1:ℝ)..(N:ℝ), G x :=
      intervalIntegral.integral_congr (fun x _ => one_mul _)
    rw [h1] at h'
    simpa using h'
  -- ## the key identity
  have hkey : (∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.vonMangoldt n : ℝ) * G (n:ℝ))
      = G 1 + (∫ t in (1:ℝ)..(N:ℝ), G t)
        + (Chebyshev.psi (N:ℝ) - (N:ℝ)) * G (N:ℝ)
        - (∫ t in (1:ℝ)..(N:ℝ), (Chebyshev.psi t - t) * deriv G t) := by
    rw [habel]
    have hpsiN : Chebyshev.psi (N:ℝ) * G (N:ℝ)
        = (N:ℝ) * G (N:ℝ) + (Chebyshev.psi (N:ℝ) - (N:ℝ)) * G (N:ℝ) := by ring
    rw [hpsiN, hsplit, hibp]
    ring
  -- ## bound on the individual terms
  have hG1 : G 1 ≤ M := by
    have h1 : G 1 = f 0 := by
      rw [hGdef]
      show (1:ℝ) ^ (-(1 - lam / Real.log (q:ℝ))) * f (Real.log 1 / Real.log (q:ℝ)) = f 0
      rw [Real.log_one, zero_div, Real.one_rpow, one_mul]
    rw [h1]
    have h := hM 0
    rw [Real.norm_eq_abs] at h
    exact (abs_le.mp h).2
  have hNterm : |(Chebyshev.psi (N:ℝ) - (N:ℝ)) * G (N:ℝ)| ≤ K * Real.exp (R * x₀) * M := by
    have hpsN := hpsi (N:ℝ) hN1'
    have hGN : |G (N:ℝ)| ≤ (N:ℝ) ^ (-(1 - lam / Real.log (q:ℝ))) * M := by
      rw [hGdef]
      show |(N:ℝ) ^ (-(1 - lam / Real.log (q:ℝ))) * f (Real.log (N:ℝ) / Real.log (q:ℝ))|
        ≤ (N:ℝ) ^ (-(1 - lam / Real.log (q:ℝ))) * M
      rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hNpos.le _)]
      refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hNpos.le _)
      have h := hM (Real.log (N:ℝ) / Real.log (q:ℝ))
      rw [Real.norm_eq_abs] at h
      exact h
    have hlogN : Real.log (N:ℝ) ≤ x₀ * Real.log (q:ℝ) := by
      calc Real.log (N:ℝ) ≤ Real.log ((q:ℝ)^x₀) := Real.log_le_log hNpos hNT
        _ = x₀ * Real.log (q:ℝ) := Real.log_rpow hq0 x₀
    have hpow : (N:ℝ) * (N:ℝ) ^ (-(1 - lam / Real.log (q:ℝ)))
        = (N:ℝ) ^ (lam / Real.log (q:ℝ)) := by
      calc (N:ℝ) * (N:ℝ) ^ (-(1 - lam / Real.log (q:ℝ)))
          = (N:ℝ) ^ (1:ℝ) * (N:ℝ) ^ (-(1 - lam / Real.log (q:ℝ))) := by rw [Real.rpow_one]
        _ = (N:ℝ) ^ ((1:ℝ) + -(1 - lam / Real.log (q:ℝ))) := by rw [Real.rpow_add hNpos]
        _ = (N:ℝ) ^ (lam / Real.log (q:ℝ)) := by
            congr 1; ring
    have hexp_le : (N:ℝ) ^ (lam / Real.log (q:ℝ)) ≤ Real.exp (R * x₀) := by
      rw [Real.rpow_def_of_pos hNpos]
      refine Real.exp_le_exp.mpr ?_
      have h1 : lam / Real.log (q:ℝ) * Real.log (N:ℝ) ≤ R * x₀ := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hLpos]
        have ha : lam * Real.log (N:ℝ) ≤ lam * (x₀ * Real.log (q:ℝ)) :=
          mul_le_mul_of_nonneg_left hlogN hlam0
        have hb : lam * (x₀ * Real.log (q:ℝ)) ≤ R * (x₀ * Real.log (q:ℝ)) :=
          mul_le_mul_of_nonneg_right hlamR (by positivity)
        linarith only [ha, hb]
      linarith only [h1]
    have hexp1 : Real.exp (-c * Real.sqrt (Real.log (N:ℝ))) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith only [hcpos, Real.sqrt_nonneg (Real.log (N:ℝ))]
    calc |(Chebyshev.psi (N:ℝ) - (N:ℝ)) * G (N:ℝ)|
        = |Chebyshev.psi (N:ℝ) - (N:ℝ)| * |G (N:ℝ)| := abs_mul _ _
      _ ≤ (K * (N:ℝ) * Real.exp (-c * Real.sqrt (Real.log (N:ℝ)))) *
            ((N:ℝ) ^ (-(1 - lam / Real.log (q:ℝ))) * M) :=
          mul_le_mul hpsN hGN (abs_nonneg _) (by positivity)
      _ = K * M * ((N:ℝ) * (N:ℝ) ^ (-(1 - lam / Real.log (q:ℝ)))) *
            Real.exp (-c * Real.sqrt (Real.log (N:ℝ))) := by ring
      _ = K * M * (N:ℝ) ^ (lam / Real.log (q:ℝ)) *
            Real.exp (-c * Real.sqrt (Real.log (N:ℝ))) := by rw [hpow]
      _ ≤ K * M * Real.exp (R * x₀) * 1 := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hexp_le (by positivity)) hexp1
            (Real.exp_pos _).le (by positivity)
      _ = K * Real.exp (R * x₀) * M := by ring
  have hIntG : (∫ t in (1:ℝ)..(N:ℝ), G t)
      ≤ Real.log (q:ℝ) * (∫ u in (0:ℝ)..x₀, Real.exp (lam * u) * f u) + M := by
    have hmain : (∫ t in (1:ℝ)..((q:ℝ)^x₀), G t)
        = Real.log (q:ℝ) * (∫ u in (0:ℝ)..x₀, Real.exp (lam * u) * f u) := by
      rw [hGdef]
      exact integral_rpow_log_subst x₀ lam hx₀ hq1 (hcont.mono Set.Icc_subset_Ici_self)
    have hadj := intervalIntegral.integral_add_adjacent_intervals hGintN hGintNT
    rw [hmain] at hadj
    have htail : |(∫ t in (N:ℝ)..((q:ℝ)^x₀), G t)| ≤ M := by
      have hmaj : IntervalIntegrable (fun t : ℝ => M * t ^ (-(1 - lam / Real.log (q:ℝ))))
          volume (N:ℝ) ((q:ℝ)^x₀) := by
        refine ContinuousOn.intervalIntegrable_of_Icc hNT (ContinuousOn.mul continuousOn_const ?_)
        refine ContinuousOn.rpow_const continuous_id.continuousOn (fun t ht => Or.inl ?_)
        exact ne_of_gt (lt_of_lt_of_le hNpos (Set.mem_Icc.mp ht).1)
      have hae : ∀ᵐ t ∂volume, t ∈ Set.Ioc (N:ℝ) ((q:ℝ)^x₀) →
          ‖G t‖ ≤ M * t ^ (-(1 - lam / Real.log (q:ℝ))) := by
        filter_upwards with t ht
        have htpos : (0:ℝ) < t := lt_of_lt_of_le hNpos ht.1.le
        rw [hGdef]
        show ‖(t ^ (-(1 - lam / Real.log (q:ℝ)))) * f (Real.log t / Real.log (q:ℝ))‖
          ≤ M * t ^ (-(1 - lam / Real.log (q:ℝ)))
        rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg htpos.le _)]
        have h := hM (Real.log t / Real.log (q:ℝ))
        rw [Real.norm_eq_abs] at h
        calc t ^ (-(1 - lam / Real.log (q:ℝ))) * ‖f (Real.log t / Real.log (q:ℝ))‖
            = ‖f (Real.log t / Real.log (q:ℝ))‖ * t ^ (-(1 - lam / Real.log (q:ℝ))) := by ring
          _ ≤ M * t ^ (-(1 - lam / Real.log (q:ℝ))) :=
              mul_le_mul_of_nonneg_right h (Real.rpow_nonneg htpos.le _)
      have h1 := intervalIntegral.norm_integral_le_of_norm_le hNT hae hmaj
      refine le_trans h1 ?_
      have hInt2 : (∫ t in (N:ℝ)..((q:ℝ)^x₀), t ^ (-(1 - lam / Real.log (q:ℝ)))) ≤ 1 := by
        have hmono : (∫ t in (N:ℝ)..((q:ℝ)^x₀), t ^ (-(1 - lam / Real.log (q:ℝ))))
            ≤ ∫ t in (N:ℝ)..((q:ℝ)^x₀),
                (N:ℝ) ^ (-(1 - lam / Real.log (q:ℝ))) := by
          refine intervalIntegral.integral_mono_on hNT ?_ intervalIntegrable_const ?_
          · refine ContinuousOn.intervalIntegrable_of_Icc hNT ?_
            refine ContinuousOn.rpow_const continuous_id.continuousOn (fun t ht => Or.inl ?_)
            exact ne_of_gt (lt_of_lt_of_le hNpos (Set.mem_Icc.mp ht).1)
          · intro t ht
            exact Real.rpow_le_rpow_of_nonpos hNpos (Set.mem_Icc.mp ht).1 (by linarith only [hσhalf])
        rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
        have h3 : (N:ℝ) ^ (-(1 - lam / Real.log (q:ℝ))) ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos hN1' (by linarith only [hσhalf])
        calc (∫ t in (N:ℝ)..((q:ℝ)^x₀), t ^ (-(1 - lam / Real.log (q:ℝ))))
            ≤ ((q:ℝ)^x₀ - (N:ℝ)) * (N:ℝ) ^ (-(1 - lam / Real.log (q:ℝ))) := hmono
          _ ≤ 1 * 1 := mul_le_mul hTN h3 (by positivity) (by norm_num)
          _ = 1 := by ring
      calc (∫ t in (N:ℝ)..((q:ℝ)^x₀), M * t ^ (-(1 - lam / Real.log (q:ℝ))))
          = M * (∫ t in (N:ℝ)..((q:ℝ)^x₀), t ^ (-(1 - lam / Real.log (q:ℝ)))) :=
            intervalIntegral.integral_const_mul _ _
        _ ≤ M * 1 := mul_le_mul_of_nonneg_left hInt2 hM0
        _ = M := by ring
    rw [eq_sub_iff_add_eq.mpr hadj]
    linarith only [abs_le.mp htail, htail]
  have hIntR : |(∫ t in (1:ℝ)..(N:ℝ), (Chebyshev.psi t - t) * deriv G t)|
      ≤ K * (2 * Real.exp (R * x₀) / c ^ 2) *
        ((1 - lam / Real.log (q:ℝ)) * M + M' / Real.log (q:ℝ)) := by
    have hpt : ∀ t : ℝ, 1 < t → t < (q:ℝ)^x₀ →
        |(Chebyshev.psi t - t) * deriv G t|
          ≤ K * ((1 - lam / Real.log (q:ℝ)) * M + M' / Real.log (q:ℝ)) *
              (Real.exp (-c * Real.sqrt (Real.log t)) * t ^ (-(1 - lam / Real.log (q:ℝ)))) := by
      intro t ht1 htT
      have htp : 0 < t := lt_trans zero_lt_one ht1
      have h1 := hpsi t ht1.le
      have h2 : ‖deriv G t‖
          ≤ t ^ (-(1 - lam / Real.log (q:ℝ)) - 1) *
              ((1 - lam / Real.log (q:ℝ)) * M + M' / Real.log (q:ℝ)) := by
        rw [hGdef]
        exact hcal.2 t ⟨ht1, htT⟩
      have hrpow : t * t ^ (-(1 - lam / Real.log (q:ℝ)) - 1)
          = t ^ (-(1 - lam / Real.log (q:ℝ))) := by
        calc t * t ^ (-(1 - lam / Real.log (q:ℝ)) - 1)
            = t ^ (1:ℝ) * t ^ (-(1 - lam / Real.log (q:ℝ)) - 1) := by rw [Real.rpow_one]
          _ = t ^ ((1:ℝ) + (-(1 - lam / Real.log (q:ℝ)) - 1)) := by rw [Real.rpow_add htp]
          _ = t ^ (-(1 - lam / Real.log (q:ℝ))) := by congr 1; ring
      rw [abs_mul]
      calc |Chebyshev.psi t - t| * ‖deriv G t‖
          ≤ (K * t * Real.exp (-c * Real.sqrt (Real.log t))) *
              (t ^ (-(1 - lam / Real.log (q:ℝ)) - 1) *
                ((1 - lam / Real.log (q:ℝ)) * M + M' / Real.log (q:ℝ))) :=
            mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
        _ = K * ((1 - lam / Real.log (q:ℝ)) * M + M' / Real.log (q:ℝ)) *
              (Real.exp (-c * Real.sqrt (Real.log t)) * t ^ (-(1 - lam / Real.log (q:ℝ)))) := by
            rw [← hrpow]; ring
    have hmaj : IntervalIntegrable
        (fun t : ℝ => K * ((1 - lam / Real.log (q:ℝ)) * M + M' / Real.log (q:ℝ)) *
          (Real.exp (-c * Real.sqrt (Real.log t)) * t ^ (-(1 - lam / Real.log (q:ℝ)))))
        volume (1:ℝ) (N:ℝ) := by
      refine ContinuousOn.intervalIntegrable_of_Icc hN1' (ContinuousOn.mul continuousOn_const ?_)
      refine ContinuousOn.mul ?_ ?_
      · exact Real.continuous_exp.comp_continuousOn
          ((Real.continuous_sqrt.comp_continuousOn (Real.continuousOn_log.mono (fun t ht => by
            simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
            exact ne_of_gt (lt_of_lt_of_le zero_lt_one (Set.mem_Icc.mp ht).1)))).const_mul (-c))
      · refine ContinuousOn.rpow_const continuous_id.continuousOn (fun t ht => Or.inl ?_)
        exact ne_of_gt (lt_of_lt_of_le zero_lt_one (Set.mem_Icc.mp ht).1)
    have hae : ∀ᵐ t ∂volume, t ∈ Set.Ioc (1:ℝ) (N:ℝ) →
        ‖(Chebyshev.psi t - t) * deriv G t‖
          ≤ K * ((1 - lam / Real.log (q:ℝ)) * M + M' / Real.log (q:ℝ)) *
              (Real.exp (-c * Real.sqrt (Real.log t)) * t ^ (-(1 - lam / Real.log (q:ℝ)))) := by
      filter_upwards [MeasureTheory.Measure.ae_ne volume ((q:ℝ)^x₀)] with t htne htmem
      rw [Real.norm_eq_abs]
      exact hpt t htmem.1 (lt_of_le_of_ne (le_trans htmem.2 hNT) htne)
    have h1 := intervalIntegral.norm_integral_le_of_norm_le hN1' hae hmaj
    refine le_trans h1 ?_
    rw [intervalIntegral.integral_const_mul]
    have h2 : (∫ t in (1:ℝ)..(N:ℝ),
          Real.exp (-c * Real.sqrt (Real.log t)) * t ^ (-(1 - lam / Real.log (q:ℝ))))
        ≤ 2 * Real.exp (R * x₀) / c ^ 2 := by
      set fI : ℝ → ℝ := fun t => Real.exp (-c * Real.sqrt (Real.log t)) *
        t ^ (-(1 - lam / Real.log (q:ℝ))) with hfI
      have hfcont : ContinuousOn fI (Set.Icc (1:ℝ) ((q:ℝ)^x₀)) := by
        rw [hfI]
        refine ContinuousOn.mul ?_ ?_
        · refine Real.continuous_exp.comp_continuousOn ?_
          exact (Real.continuous_sqrt.comp_continuousOn (Real.continuousOn_log.mono (fun t ht => by
            simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
            exact ne_of_gt (lt_of_lt_of_le zero_lt_one ht.1)))).const_mul (-c)
        · refine ContinuousOn.rpow_const continuous_id.continuousOn (fun t ht => Or.inl ?_)
          exact ne_of_gt (lt_of_lt_of_le zero_lt_one ht.1)
      have hbig : IntervalIntegrable fI volume (1:ℝ) ((q:ℝ)^x₀) :=
        ContinuousOn.intervalIntegrable_of_Icc hT1 hfcont
      have hsmall : IntervalIntegrable fI volume (1:ℝ) (N:ℝ) :=
        ContinuousOn.intervalIntegrable_of_Icc hN1' (hfcont.mono (Set.Icc_subset_Icc le_rfl hNT))
      have hmid : IntervalIntegrable fI volume (N:ℝ) ((q:ℝ)^x₀) :=
        ContinuousOn.intervalIntegrable_of_Icc hNT (hfcont.mono (Set.Icc_subset_Icc hN1' le_rfl))
      have hnonneg : 0 ≤ ∫ t in (N:ℝ)..((q:ℝ)^x₀), fI t := by
        refine intervalIntegral.integral_nonneg hNT (fun t ht => ?_)
        rw [hfI]
        exact mul_nonneg (Real.exp_pos _).le
          (Real.rpow_nonneg (le_of_lt (lt_of_lt_of_le hNpos ht.1)) _)
      have hadj := intervalIntegral.integral_add_adjacent_intervals hsmall hmid
      have hbound : (∫ t in (1:ℝ)..((q:ℝ)^x₀), fI t) ≤ 2 * Real.exp (R * x₀) / c ^ 2 := by
        rw [hfI]
        exact integral_exp_neg_sqrt_rpow_le (x₀ := x₀) (R := R) (lam := lam) (c := c)
          hx₀ hcpos hlam0 hlamR hq1
      linarith only [hadj, hnonneg, hbound]

    calc K * ((1 - lam / Real.log (q:ℝ)) * M + M' / Real.log (q:ℝ)) *
          (∫ t in (1:ℝ)..(N:ℝ),
            Real.exp (-c * Real.sqrt (Real.log t)) * t ^ (-(1 - lam / Real.log (q:ℝ))))
        ≤ K * ((1 - lam / Real.log (q:ℝ)) * M + M' / Real.log (q:ℝ)) *
            (2 * Real.exp (R * x₀) / c ^ 2) :=
          mul_le_mul_of_nonneg_left h2 (by
            have h1 : 0 ≤ (1 - lam / Real.log (q:ℝ)) * M := mul_nonneg hσ0 hM0
            have h2 : 0 ≤ M' / Real.log (q:ℝ) := div_nonneg hM'0 hLpos.le
            have : 0 ≤ K := hKpos.le
            nlinarith only [hKpos, h1, h2])
      _ = K * (2 * Real.exp (R * x₀) / c ^ 2) *
            ((1 - lam / Real.log (q:ℝ)) * M + M' / Real.log (q:ℝ)) := by ring
  -- ## rewrite the `tsum` as a finite sum
  have htsum : (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
        (n : ℝ) ^ (-(1 - lam / Real.log (q:ℝ))) * f (Real.log n / Real.log (q:ℝ)))
      = ∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.vonMangoldt n : ℝ) *
          (n : ℝ) ^ (-(1 - lam / Real.log (q:ℝ))) * f (Real.log n / Real.log (q:ℝ)) := by
    have h := tsum_lamWeight_eq_sum (x₀ := x₀) (q := (q:ℝ)) (lam := lam) hx₀ hq1 hsupp
    rw [← hNdef] at h
    exact h
  have hsum_eq : (∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.vonMangoldt n : ℝ) *
        (n : ℝ) ^ (-(1 - lam / Real.log (q:ℝ))) * f (Real.log n / Real.log (q:ℝ)))
      = ∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.vonMangoldt n : ℝ) * G (n:ℝ) := by
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [hGdef]
    show (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 - lam / Real.log (q:ℝ))) *
        f (Real.log n / Real.log (q:ℝ))
      = (ArithmeticFunction.vonMangoldt n : ℝ) *
        ((n : ℝ) ^ (-(1 - lam / Real.log (q:ℝ))) * f (Real.log n / Real.log (q:ℝ)))
    ring
  -- ## the main estimate
  have hσle : (1 - lam / Real.log (q:ℝ)) ≤ 1 := by linarith only [div_nonneg hlam0 hLpos.le, hlam0, hLpos]
  have hML : M' / Real.log (q:ℝ) ≤ M' := by
    rw [div_le_iff₀ hLpos]; nlinarith only [hL1, hM'0]
  have hmain_le : (1 - lam / Real.log (q:ℝ)) * M + M' / Real.log (q:ℝ) ≤ M + M' := by
    linarith only [mul_le_mul_of_nonneg_right hσle hM0, hML, hσle, hM0]
  have hMain : (∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.vonMangoldt n : ℝ) * G (n:ℝ))
      ≤ Real.log (q:ℝ) * (∫ u in (0:ℝ)..x₀, Real.exp (lam * u) * f u) + C₀ * (M + M') := by
    rw [hkey]
    have h1 : G 1 + (∫ t in (1:ℝ)..(N:ℝ), G t)
        + (Chebyshev.psi (N:ℝ) - (N:ℝ)) * G (N:ℝ)
        - (∫ t in (1:ℝ)..(N:ℝ), (Chebyshev.psi t - t) * deriv G t)
        ≤ G 1 + (∫ t in (1:ℝ)..(N:ℝ), G t)
          + |(Chebyshev.psi (N:ℝ) - (N:ℝ)) * G (N:ℝ)|
          + |(∫ t in (1:ℝ)..(N:ℝ), (Chebyshev.psi t - t) * deriv G t)| := by
      linarith only [neg_le_abs (∫ t in (1:ℝ)..(N:ℝ), (Chebyshev.psi t - t) * deriv G t),
        le_abs_self ((Chebyshev.psi (N:ℝ) - (N:ℝ)) * G (N:ℝ))]
    refine le_trans h1 ?_
    have h2 : G 1 + (∫ t in (1:ℝ)..(N:ℝ), G t)
        + |(Chebyshev.psi (N:ℝ) - (N:ℝ)) * G (N:ℝ)|
        + |(∫ t in (1:ℝ)..(N:ℝ), (Chebyshev.psi t - t) * deriv G t)|
        ≤ M + (Real.log (q:ℝ) * (∫ u in (0:ℝ)..x₀, Real.exp (lam * u) * f u) + M)
          + K * Real.exp (R * x₀) * M
          + K * (2 * Real.exp (R * x₀) / c ^ 2) *
              ((1 - lam / Real.log (q:ℝ)) * M + M' / Real.log (q:ℝ)) := by
      linarith only [hG1, hIntG, hNterm, hIntR]
    refine le_trans h2 ?_
    rw [hC₀def]
    have hKe : 0 ≤ K * Real.exp (R * x₀) := mul_nonneg hKpos.le (Real.exp_pos _).le
    have hK2 : 0 ≤ K * (2 * Real.exp (R * x₀) / c ^ 2) := by
      have h : 0 < 2 * Real.exp (R * x₀) / c ^ 2 := by positivity
      exact mul_nonneg hKpos.le h.le
    have hMM : 0 ≤ M + M' := by linarith only [hM0, hM'0]
    -- core arithmetic: the four error terms are dominated by `(2 + Ke + 2K2) * (M + M')`
    have hcore : 2 * M + K * Real.exp (R * x₀) * M +
          K * (2 * Real.exp (R * x₀) / c ^ 2) * ((1 - lam / Real.log (q:ℝ)) * M + M' / Real.log (q:ℝ))
        ≤ (2 + K * Real.exp (R * x₀) + 2 * (K * (2 * Real.exp (R * x₀) / c ^ 2))) * (M + M') := by
      have h1 : 2 * M ≤ 2 * (M + M') := by linarith only [hM'0]
      have h2 : K * Real.exp (R * x₀) * M ≤ K * Real.exp (R * x₀) * (M + M') :=
        mul_le_mul_of_nonneg_left (by linarith only [hM'0]) hKe
      have h3 : K * (2 * Real.exp (R * x₀) / c ^ 2) *
            ((1 - lam / Real.log (q:ℝ)) * M + M' / Real.log (q:ℝ))
          ≤ 2 * (K * (2 * Real.exp (R * x₀) / c ^ 2)) * (M + M') := by
        have hA := mul_le_mul_of_nonneg_left hmain_le hK2
        have hX : 0 ≤ K * (2 * Real.exp (R * x₀) / c ^ 2) * (M + M') :=
          mul_nonneg hK2 hMM
        linarith only [hA, hX]
      have h4 : (2 + K * Real.exp (R * x₀) + 2 * (K * (2 * Real.exp (R * x₀) / c ^ 2))) * (M + M')
          = 2 * (M + M') + K * Real.exp (R * x₀) * (M + M')
            + 2 * (K * (2 * Real.exp (R * x₀) / c ^ 2) * (M + M')) := by ring
      linarith only [h1, h2, h3, h4, hM'0]
    have hCge : 2 + K * Real.exp (R * x₀) + 2 * (K * (2 * Real.exp (R * x₀) / c ^ 2)) ≤ C₀ := by
      rw [hC₀def]; linarith only []
    have hprod : (2 + K * Real.exp (R * x₀) + 2 * (K * (2 * Real.exp (R * x₀) / c ^ 2))) * (M + M')
        ≤ C₀ * (M + M') := mul_le_mul_of_nonneg_right hCge hMM
    linarith only [hcore, hprod]
  -- ## finish
  have hinv : 0 ≤ (Real.log (q:ℝ))⁻¹ := inv_nonneg.mpr hLpos.le
  calc (Real.log (q:ℝ))⁻¹ * (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
        (n : ℝ) ^ (-(1 - lam / Real.log (q:ℝ))) * f (Real.log n / Real.log (q:ℝ)))
      = (Real.log (q:ℝ))⁻¹ * (∑ n ∈ Finset.Icc 1 N,
          (ArithmeticFunction.vonMangoldt n : ℝ) * G (n:ℝ)) := by
        rw [htsum, hsum_eq]
    _ ≤ (Real.log (q:ℝ))⁻¹ *
          (Real.log (q:ℝ) * (∫ u in (0:ℝ)..x₀, Real.exp (lam * u) * f u) + C₀ * (M + M')) :=
        mul_le_mul_of_nonneg_left hMain hinv
    _ = (∫ u in (0:ℝ)..x₀, Real.exp (lam * u) * f u) + C₀ * (M + M') / Real.log (q:ℝ) := by
        rw [div_eq_inv_mul, mul_add, ← mul_assoc, inv_mul_cancel₀ hLpos.ne', one_mul]

end

end Work.LinnikAreas.A5
