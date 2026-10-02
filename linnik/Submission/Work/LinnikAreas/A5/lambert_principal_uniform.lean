import Mathlib
import Submission.Commons.NumberTheory.Zeta.chebyshev_psi_sub_id_exp
import Submission.Work.LinnikAreas.A5.psi_abel_integral
import Submission.Work.LinnikAreas.A5.integral_rpow_log_subst
import Submission.Work.LinnikAreas.A5.integral_exp_neg_sqrt_log_rpow_le
import Submission.Work.LinnikAreas.A5.psi_sub_id_exp_bound

open scoped BigOperators
open MeasureTheory Set Finset

namespace Work.LinnikAreas.A5

noncomputable section

set_option maxHeartbeats 4000000

/-
Uniform Chebyshev-ψ (principal character) term of HB §13.  For a weight f supported in [0,x₀]
with 0 ≤ M, 0 ≤ M', ‖f‖ ≤ M and ‖f'‖ ≤ M', and σ = 1 - lam/log q:

  (1/log q)·Σ_n Λ(n) n^{-σ} f(log n/log q) ≤ ∫₀^{x₀} e^{lam u} f(u) du + O((M+M')/log q),

uniformly in lam ∈ (0,R] and in f.  Proof: partial summation against ψ(t) = t + R(t) with
R(t) ≪ t exp(-c√(log t)) (available under Submission/Commons/NumberTheory/Zeta/, not in Mathlib);
the main term is ∫₁^{q^{x₀}} t^{-σ} f(log t/log q) dt = (log q)·∫₀^{x₀} e^{lam u} f(u) du.

Assembly (this file): `psi_sub_id_exp_bound` gives R(t) ≪ t e^{-c√log t} for t ≥ 1;
`psi_abel_integral` turns the von Mangoldt sum into ψ(N)G(N) - ∫₁^N ψ G';
`integral_rpow_log_subst` identifies ∫₁^{q^{x₀}} G with (log q)∫₀^{x₀} e^{lam u} f;
`integral_exp_neg_sqrt_log_rpow_le` bounds the de la Vallée Poussin error integral by
2e^{R x₀}/c², independently of q.  The remaining pieces (the weight `wgt` and its derivative,
integrability, the tail/boundary terms and the constant bookkeeping) are proved below.
-/

/-! ## The Mellin-type weight `t ↦ t^{-σ} f(log t / L)` and its derivative -/

private abbrev wgt (L σ : ℝ) (f : ℝ → ℝ) (t : ℝ) : ℝ := t ^ (-σ) * f (Real.log t / L)

private abbrev wgtD (L σ : ℝ) (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  -σ * t ^ (-σ - 1) * f (Real.log t / L)
    + t ^ (-σ) * (deriv f (Real.log t / L) * (t⁻¹ / L))

private lemma continuousOn_wgt {x₀ L σ B : ℝ} (hL : 0 < L) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Ici 0)) (hB : (1:ℝ) ≤ B) (hle : Real.log B / L ≤ x₀) :
    ContinuousOn (wgt L σ f) (Set.Icc (1:ℝ) B) := by
  have hBx : Real.log B ≤ x₀ * L := (div_le_iff₀ hL).mp hle
  have hlogc : ContinuousOn (fun t : ℝ => Real.log t / L) (Set.Icc (1:ℝ) B) :=
    (Real.continuousOn_log.mono (fun x hx => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact ne_of_gt (lt_of_lt_of_le zero_lt_one hx.1))).div_const L
  have hmap : MapsTo (fun t : ℝ => Real.log t / L) (Set.Icc (1:ℝ) B) (Set.Icc (0:ℝ) x₀) := by
    intro t ht
    have ht1 : (1:ℝ) ≤ t := ht.1
    have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht1
    refine ⟨div_nonneg (Real.log_nonneg ht1) hL.le, ?_⟩
    rw [div_le_iff₀ hL]
    have hlog : Real.log t ≤ Real.log B := Real.log_le_log htpos ht.2
    linarith only [hlog, hBx]
  have hcomp : ContinuousOn (fun t : ℝ => f (Real.log t / L)) (Set.Icc (1:ℝ) B) :=
    hf.comp hlogc (hmap.mono_right Set.Icc_subset_Ici_self)
  have hrp : ContinuousOn (fun t : ℝ => t ^ (-σ)) (Set.Icc (1:ℝ) B) :=
    ContinuousOn.rpow continuousOn_id continuousOn_const (fun x hx => Or.inl (by linarith only [hx.1, hx]))
  exact hrp.mul hcomp

/-- Interval integrability of the weight on `[1,B]`. -/
private lemma intervalIntegrable_wgt {x₀ L σ B : ℝ} (hL : 0 < L) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Ici 0)) (hB : (1:ℝ) ≤ B) (hle : Real.log B / L ≤ x₀) :
    IntervalIntegrable (wgt L σ f) volume (1:ℝ) B := by
  have h' : ContinuousOn (wgt L σ f) (Set.uIcc (1:ℝ) B) := by
    rw [Set.uIcc_of_le hB]
    exact continuousOn_wgt hL hf hB hle
  exact h'.intervalIntegrable

private lemma rpow_neg_sub_one_split {σ t : ℝ} (ht : 0 < t) :
    t ^ (-σ - 1) = t ^ (-σ) * t⁻¹ := by
  rw [show -σ - 1 = -σ + (-1:ℝ) by ring, Real.rpow_add ht, Real.rpow_neg_one]

private lemma hasDerivAt_wgt {x₀ L σ : ℝ} (hL : 0 < L) {f : ℝ → ℝ}
    (hf : DifferentiableOn ℝ f (Set.Ioo (0:ℝ) x₀)) {t : ℝ} (ht : 1 < t)
    (hu : Real.log t / L ∈ Set.Ioo (0:ℝ) x₀) :
    HasDerivAt (wgt L σ f) (wgtD L σ f t) t := by
  have htpos : 0 < t := by linarith only [ht]
  have h1 : HasDerivAt (fun t : ℝ => t ^ (-σ)) (-σ * t ^ (-σ - 1)) t :=
    Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt htpos))
  have h2 : HasDerivAt (fun t : ℝ => Real.log t / L) (t⁻¹ / L) t :=
    (Real.hasDerivAt_log (ne_of_gt htpos)).div_const L
  have h3 : HasDerivAt f (deriv f (Real.log t / L)) (Real.log t / L) :=
    (hf.differentiableAt (Ioo_mem_nhds hu.1 hu.2)).hasDerivAt
  have h4 : HasDerivAt (fun t : ℝ => f (Real.log t / L))
      (deriv f (Real.log t / L) * (t⁻¹ / L)) t := h3.comp t h2
  exact h1.mul h4

private lemma deriv_wgt {x₀ L σ : ℝ} (hL : 0 < L) {f : ℝ → ℝ}
    (hf : DifferentiableOn ℝ f (Set.Ioo (0:ℝ) x₀)) {t : ℝ} (ht : 1 < t)
    (hu : Real.log t / L ∈ Set.Ioo (0:ℝ) x₀) :
    deriv (wgt L σ f) t = wgtD L σ f t :=
  (hasDerivAt_wgt hL hf ht hu).deriv

private lemma wgtD_alt {L σ : ℝ} {f : ℝ → ℝ} {t : ℝ} (ht : 0 < t) :
    wgtD L σ f t
      = t ^ (-σ - 1) * (-σ * f (Real.log t / L) + deriv f (Real.log t / L) / L) := by
  rw [wgtD, rpow_neg_sub_one_split ht]
  ring

private lemma abs_wgtD_le {x₀ L σ A B : ℝ} (hL : 0 < L) (hσ : 0 ≤ σ) {f : ℝ → ℝ}
    (hfA : ∀ t : ℝ, ‖f t‖ ≤ A) (hfB : ∀ u ∈ Set.Icc (0:ℝ) x₀, ‖deriv f u‖ ≤ B)
    {t : ℝ} (ht : 1 ≤ t) (hu : Real.log t / L ∈ Set.Icc (0:ℝ) x₀) :
    |wgtD L σ f t| ≤ (σ * A + B / L) * t ^ (-σ - 1) := by
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hrp : 0 ≤ t ^ (-σ - 1) := Real.rpow_nonneg htpos.le _
  have hfu : |f (Real.log t / L)| ≤ A := by
    have h := hfA (Real.log t / L); rwa [Real.norm_eq_abs] at h
  have hfdu : |deriv f (Real.log t / L)| ≤ B := by
    have h := hfB _ hu; rwa [Real.norm_eq_abs] at h
  have h1 : |-σ * f (Real.log t / L) + deriv f (Real.log t / L) / L| ≤ σ * A + B / L := by
    refine le_trans (abs_add_le _ _) ?_
    have h2 : |-σ * f (Real.log t / L)| = σ * |f (Real.log t / L)| := by
      rw [abs_mul, abs_neg, abs_of_nonneg hσ]
    rw [h2, abs_div, abs_of_pos hL]
    exact add_le_add (mul_le_mul_of_nonneg_left hfu hσ) (div_le_div_of_nonneg_right hfdu hL.le)
  rw [wgtD_alt htpos, abs_mul, abs_of_nonneg hrp, mul_comm (t ^ (-σ - 1))]
  exact mul_le_mul_of_nonneg_right h1 hrp

private lemma rpow_neg_sub_one_le_one {σ t : ℝ} (hσ : 0 ≤ σ) (ht : 1 ≤ t) :
    t ^ (-σ - 1) ≤ 1 := by
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have h1 : t ^ (-σ - 1) = (t ^ (σ + 1))⁻¹ := by
    rw [show -σ - 1 = -(σ + 1) by ring, Real.rpow_neg htpos.le]
  rw [h1, inv_le_one₀ (Real.rpow_pos_of_pos htpos _)]
  exact Real.one_le_rpow ht (by linarith only [hσ])

private lemma rpow_neg_le_one {σ t : ℝ} (hσ : 0 ≤ σ) (ht : 1 ≤ t) : t ^ (-σ) ≤ 1 := by
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  rw [Real.rpow_neg htpos.le, inv_le_one₀ (Real.rpow_pos_of_pos htpos σ)]
  exact Real.one_le_rpow ht hσ

/-! ## Integrability of the derivative and of `ψ · derivative` -/

private lemma integrableOn_deriv_wgt {x₀ L σ A B : ℝ} {N : ℕ}
    (hx₀ : 0 < x₀) (hL : 0 < L) (hσ : 0 ≤ σ) (hN : 1 ≤ N)
    (hNe : (N:ℝ) ≤ Real.exp (L * x₀))
    {f : ℝ → ℝ} (hf : DifferentiableOn ℝ f (Set.Ioo (0:ℝ) x₀))
    (hfA : ∀ t : ℝ, ‖f t‖ ≤ A) (hfB : ∀ u ∈ Set.Icc (0:ℝ) x₀, ‖deriv f u‖ ≤ B) :
    IntegrableOn (deriv (wgt L σ f)) (Set.uIoc (1:ℝ) (N:ℝ)) volume := by
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hfin : volume (Set.uIoc (1:ℝ) (N:ℝ)) < ⊤ := by
    rw [Set.uIoc_of_le hN1, Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
  have hA0 : 0 ≤ A := le_trans (abs_nonneg _) (by
    have h := hfA 0; rwa [Real.norm_eq_abs] at h)
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (by
    have h := hfB (x₀/2) ⟨by linarith only [hx₀], by linarith only [hx₀]⟩
    rwa [Real.norm_eq_abs] at h)
  have hC0 : 0 ≤ σ * A + B / L := by positivity
  refine IntegrableOn.of_bound hfin (measurable_deriv (wgt L σ f)).aestronglyMeasurable
    (σ * A + B / L) ?_
  rw [ae_restrict_iff' measurableSet_uIoc, ae_iff]
  refine measure_mono_null (t := {x : ℝ | x = (N:ℝ)}) (fun x hx => ?_) (measure_singleton _)
  simp only [Set.mem_ofPred_eq, Classical.not_imp] at hx
  by_cases hxN : x = (N:ℝ)
  · simpa only [Set.mem_ofPred_eq, not_not] using hxN
  · exfalso
    rw [Set.uIoc_of_le hN1, Set.mem_Ioc] at hx
    have hx1 : (1:ℝ) < x := hx.1.1
    have hxNlt : x < (N:ℝ) := lt_of_le_of_ne hx.1.2 hxN
    have hxu : Real.log x / L ∈ Set.Ioo (0:ℝ) x₀ := by
      refine ⟨div_pos (Real.log_pos hx1) hL, ?_⟩
      rw [div_lt_iff₀ hL]
      have h1 : Real.log x < Real.log (N:ℝ) := Real.log_lt_log (by linarith only [hx]) hxNlt
      have h2 : Real.log (N:ℝ) ≤ L * x₀ := by
        have h3 : Real.log (N:ℝ) ≤ Real.log (Real.exp (L * x₀)) :=
          Real.log_le_log (by exact_mod_cast (by omega : 0 < N)) hNe
        rwa [Real.log_exp] at h3
      linarith only [h1, h2]
    have hd := deriv_wgt (σ := σ) hL hf hx1 hxu
    have hb := abs_wgtD_le hL hσ hfA hfB (le_of_lt hx1) ⟨le_of_lt hxu.1, le_of_lt hxu.2⟩
    have hle1 : x ^ (-σ - 1) ≤ 1 := rpow_neg_sub_one_le_one hσ (le_of_lt hx1)
    have hgoal : ‖deriv (wgt L σ f) x‖ ≤ σ * A + B / L := by
      rw [Real.norm_eq_abs, hd]
      calc |wgtD L σ f x| ≤ (σ * A + B / L) * x ^ (-σ - 1) := hb
        _ ≤ (σ * A + B / L) * 1 := mul_le_mul_of_nonneg_left hle1 hC0
        _ = σ * A + B / L := by ring
    exact hx.2 hgoal

private lemma intervalIntegrable_deriv_wgt {x₀ L σ A B : ℝ} {N : ℕ}
    (hx₀ : 0 < x₀) (hL : 0 < L) (hσ : 0 ≤ σ) (hN : 1 ≤ N)
    (hNe : (N:ℝ) ≤ Real.exp (L * x₀))
    {f : ℝ → ℝ} (hf : DifferentiableOn ℝ f (Set.Ioo (0:ℝ) x₀))
    (hfA : ∀ t : ℝ, ‖f t‖ ≤ A) (hfB : ∀ u ∈ Set.Icc (0:ℝ) x₀, ‖deriv f u‖ ≤ B) :
    IntervalIntegrable (deriv (wgt L σ f)) volume (1:ℝ) (N:ℝ) := by
  rw [intervalIntegrable_iff]
  exact integrableOn_deriv_wgt hx₀ hL hσ hN hNe hf hfA hfB

private lemma intervalIntegrable_psi_deriv_wgt {x₀ L σ A B : ℝ} {N : ℕ}
    (hx₀ : 0 < x₀) (hL : 0 < L) (hσ : 0 ≤ σ) (hN : 1 ≤ N)
    (hNe : (N:ℝ) ≤ Real.exp (L * x₀))
    {f : ℝ → ℝ} (hf : DifferentiableOn ℝ f (Set.Ioo (0:ℝ) x₀))
    (hfA : ∀ t : ℝ, ‖f t‖ ≤ A) (hfB : ∀ u ∈ Set.Icc (0:ℝ) x₀, ‖deriv f u‖ ≤ B) :
    IntervalIntegrable (fun t : ℝ => Chebyshev.psi t * deriv (wgt L σ f) t)
      volume (1:ℝ) (N:ℝ) := by
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hder := integrableOn_deriv_wgt hx₀ hL hσ hN hNe hf hfA hfB
  have hmeas : AEStronglyMeasurable (fun t : ℝ => Chebyshev.psi t)
      (volume.restrict (Set.uIoc (1:ℝ) (N:ℝ))) :=
    Chebyshev.psi_mono.measurable.aestronglyMeasurable
  have hbdd : ∀ᵐ t ∂(volume.restrict (Set.uIoc (1:ℝ) (N:ℝ))),
      ‖Chebyshev.psi t‖ ≤ (Real.log 4 + 4) * (N:ℝ) := by
    rw [ae_restrict_iff' measurableSet_uIoc]
    refine Filter.Eventually.of_forall (fun t ht => ?_)
    rw [Set.uIoc_of_le hN1, Set.mem_Ioc] at ht
    have ht1 : (1:ℝ) ≤ t := le_of_lt ht.1
    have h1 : Chebyshev.psi t ≤ (Real.log 4 + 4) * t :=
      Chebyshev.psi_le_const_mul_self (by linarith only [ht])
    have h2 : 0 ≤ Chebyshev.psi t := Chebyshev.psi_nonneg t
    rw [Real.norm_eq_abs, abs_of_nonneg h2]
    exact le_trans h1 (mul_le_mul_of_nonneg_left ht.2 (by positivity))
  have h := MeasureTheory.Integrable.mul_bdd (μ := volume.restrict (Set.uIoc (1:ℝ) (N:ℝ)))
    (f := deriv (wgt L σ f)) (g := fun t : ℝ => Chebyshev.psi t)
    (c := (Real.log 4 + 4) * (N:ℝ)) hder hmeas hbdd
  rw [intervalIntegrable_iff]
  exact h.congr (Filter.Eventually.of_forall (fun t => by ring))

/-! ## The principal-character estimate -/

private lemma continuousOn_decay (c L a b : ℝ) (ha : (0:ℝ) < a) (hab : a ≤ b) :
    ContinuousOn (fun t : ℝ => Real.exp (-c * Real.sqrt (Real.log t)) * t ^ (-L))
      (Set.uIcc a b) := by
  have hmem : ∀ x ∈ Set.uIcc a b, (0:ℝ) < x := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    linarith only [hx.1, ha, hx]
  have hlog : ContinuousOn (fun t : ℝ => Real.log t) (Set.uIcc a b) :=
    Real.continuousOn_log.mono (fun x hx => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact ne_of_gt (hmem x hx))
  have hsqrt : ContinuousOn (fun t : ℝ => Real.sqrt (Real.log t)) (Set.uIcc a b) :=
    Real.continuous_sqrt.comp_continuousOn hlog
  have hexp : ContinuousOn (fun t : ℝ => Real.exp (-c * Real.sqrt (Real.log t))) (Set.uIcc a b) :=
    Real.continuous_exp.comp_continuousOn (hsqrt.const_mul (-c))
  exact hexp.mul (ContinuousOn.rpow continuousOn_id continuousOn_const
    (fun x hx => Or.inl (ne_of_gt (hmem x hx))))

theorem lambert_principal_uniform (x₀ R : ℝ) (hx₀ : 0 < x₀) (hR : 0 < R) :
    ∃ C : ℝ, 0 < C ∧ ∃ q₀ : ℕ, ∀ {q : ℕ}, q₀ ≤ q →
    ∀ {f : ℝ → ℝ} {M M' : ℝ}, 0 ≤ M → 0 ≤ M' →
      ContinuousOn f (Set.Ici 0) → (∀ t : ℝ, x₀ ≤ t → f t = 0) →
      ContDiffOn ℝ 1 f (Set.Ioo 0 x₀) →
      (∀ t : ℝ, ‖f t‖ ≤ M) → (∀ t ∈ Set.Icc (0:ℝ) x₀, ‖deriv f t‖ ≤ M') →
      ∀ lam : ℝ, 0 < lam → lam ≤ R →
        (Real.log q)⁻¹ * (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
            (n : ℝ) ^ (-(1 - lam / Real.log q)) * f (Real.log n / Real.log q))
          ≤ (∫ u in (0:ℝ)..x₀, Real.exp (lam * u) * f u) + C * (M + M') / Real.log q := by
  obtain ⟨K, c, hKpos, hcpos, hpsi⟩ := psi_sub_id_exp_bound
  have hKnn : 0 ≤ K := hKpos.le
  have hc2 : 0 < c ^ 2 := by positivity
  let C₀ : ℝ := 2 + K * Real.exp (R * x₀) + 2 * K * Real.exp (R * x₀) / c ^ 2
  refine ⟨C₀, by rw [show C₀ = 2 + K * Real.exp (R * x₀) + 2 * K * Real.exp (R * x₀) / c ^ 2
      from rfl]; positivity, ⌈Real.exp (max 1 (max R (1 / x₀)))⌉₊, ?_⟩
  intro q hq f M M' hM hM' hfcont hfsupp hfcd hfA hfB lam hlam hlamR
  -- ### numerical facts about `q`
  have hexp_le : Real.exp (max 1 (max R (1 / x₀))) ≤ (q : ℝ) := by
    have h1 : Real.exp (max 1 (max R (1 / x₀))) ≤
        ((⌈Real.exp (max 1 (max R (1 / x₀)))⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    have h2 : ((⌈Real.exp (max 1 (max R (1 / x₀)))⌉₊ : ℕ) : ℝ) ≤ (q : ℝ) := by
      exact_mod_cast hq
    linarith only [h1, h2]
  have hqpos : (0 : ℝ) < (q : ℝ) := lt_of_lt_of_le (Real.exp_pos _) hexp_le
  have hq1 : (1 : ℝ) < (q : ℝ) := by
    have h1 : (1 : ℝ) < Real.exp (max 1 (max R (1 / x₀))) :=
      Real.one_lt_exp_iff.mpr (by positivity)
    linarith only [hexp_le, h1]
  let L : ℝ := Real.log q
  have hLval : L = Real.log q := rfl
  have hLpos : 0 < L := by rw [hLval]; exact Real.log_pos hq1
  have hmax : max 1 (max R (1 / x₀)) ≤ L := by
    have h := (Real.le_log_iff_exp_le hqpos).mpr hexp_le
    rw [hLval]; exact h
  have hL1 : 1 ≤ L := le_trans (le_max_left _ _) hmax
  have hLR : R ≤ L :=
    le_trans (le_max_left R (1 / x₀))
      (le_trans (le_max_right (1:ℝ) (max R (1 / x₀))) hmax)
  have h1x : 1 / x₀ ≤ L :=
    le_trans (le_max_right R (1 / x₀))
      (le_trans (le_max_right (1:ℝ) (max R (1 / x₀))) hmax)
  have hLx : 1 ≤ L * x₀ := by
    have h := (div_le_iff₀ hx₀).mp h1x
    linarith only [h]
  let σ : ℝ := 1 - lam / L
  have hσval : σ = 1 - lam / L := rfl
  have hσ0 : 0 ≤ σ := by
    have h1 : lam / L ≤ 1 := (div_le_one hLpos).mpr (le_trans hlamR hLR)
    rw [hσval]; linarith only [h1]
  have hσ1 : σ ≤ 1 := by
    have h1 : 0 ≤ lam / L := div_nonneg hlam.le hLpos.le
    rw [hσval]; linarith only [h1]
  set N : ℕ := ⌊(q : ℝ) ^ x₀⌋₊ with hNdef
  have hqpow : (q : ℝ) ^ x₀ = Real.exp (L * x₀) := by
    rw [Real.rpow_def_of_pos hqpos, hLval]
  have hqpow1 : (1 : ℝ) ≤ (q : ℝ) ^ x₀ := by
    rw [hqpow]
    calc (1 : ℝ) = Real.exp 0 := by rw [Real.exp_zero]
      _ ≤ Real.exp (L * x₀) := Real.exp_le_exp.mpr (by linarith only [hLx])
  have hN1 : 1 ≤ N := by
    have h2 : 1 ≤ ⌊(q : ℝ) ^ x₀⌋₊ := Nat.le_floor (by simpa using hqpow1)
    rwa [hNdef]
  have hNle : (N : ℝ) ≤ Real.exp (L * x₀) := by
    have h1 : (N : ℝ) ≤ (q : ℝ) ^ x₀ := by
      rw [hNdef]; exact Nat.floor_le (by positivity)
    rwa [hqpow] at h1
  have hNq : (N : ℝ) ≤ (q : ℝ) ^ x₀ := by rw [hqpow]; exact hNle
  have hN1' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith only [hN1']
  have hlogN : Real.log (N : ℝ) / L ≤ x₀ := by
    rw [div_le_iff₀ hLpos]
    have h1 : Real.log (N : ℝ) ≤ Real.log (Real.exp (L * x₀)) :=
      Real.log_le_log hNpos hNle
    rw [Real.log_exp] at h1
    linarith only [h1]
  have hlogNle : Real.log (N : ℝ) ≤ x₀ * L := (div_le_iff₀ hLpos).mp hlogN
  have hfdiff : DifferentiableOn ℝ f (Set.Ioo (0 : ℝ) x₀) :=
    hfcd.differentiableOn (by norm_num)
  -- ### the `tsum` is a finite sum
  let Ssum : ℝ := ∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.vonMangoldt n : ℝ) *
      (n : ℝ) ^ (-(1 - lam / Real.log q)) * f (Real.log n / Real.log q)
  have hSsumval : Ssum = ∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.vonMangoldt n : ℝ) *
      (n : ℝ) ^ (-(1 - lam / Real.log q)) * f (Real.log n / Real.log q) := rfl
  have htsum : (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
        (n : ℝ) ^ (-(1 - lam / Real.log q)) * f (Real.log n / Real.log q)) = Ssum := by
    rw [show Ssum = ∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.vonMangoldt n : ℝ) *
        (n : ℝ) ^ (-(1 - lam / Real.log q)) * f (Real.log n / Real.log q) from rfl]
    refine tsum_eq_sum (s := Finset.Icc 1 N) (fun b hb => ?_)
    by_cases hb0 : b = 0
    · subst hb0; simp
    · have hb1 : 1 ≤ b := Nat.one_le_iff_ne_zero.mpr hb0
      have hbN : N < b := by
        by_contra h
        push_neg at h
        exact hb (Finset.mem_Icc.mpr ⟨hb1, h⟩)
      have hbq : (q : ℝ) ^ x₀ < (b : ℝ) := by
        have h1 : (q : ℝ) ^ x₀ < ((N : ℕ) : ℝ) + 1 := by
          rw [hNdef]; exact Nat.lt_floor_add_one _
        have h2 : ((N : ℕ) : ℝ) + 1 ≤ (b : ℝ) := by
          exact_mod_cast (by omega : N + 1 ≤ b)
        linarith only [h1, h2]
      have hlog : x₀ ≤ Real.log b / L := by
        rw [le_div_iff₀ hLpos]
        have h3 : Real.log ((q : ℝ) ^ x₀) < Real.log b :=
          Real.log_lt_log (by positivity) hbq
        rw [Real.log_rpow hqpos] at h3
        rw [hLval]
        linarith only [h3]
      rw [hfsupp (Real.log b / L) hlog]
      simp
  -- ### Abel summation and integration by parts
  have hcontG : ContinuousOn (wgt L σ f) (Set.Icc (1:ℝ) (N:ℝ)) :=
    continuousOn_wgt hLpos hfcont hN1' hlogN
  have hcontGu : ContinuousOn (wgt L σ f) (Set.uIcc (1:ℝ) (N:ℝ)) := by
    rw [Set.uIcc_of_le hN1']; exact hcontG
  have hGdiff : ∀ t ∈ Set.Ioo (1:ℝ) (N:ℝ), DifferentiableAt ℝ (wgt L σ f) t := by
    intro t ht
    rw [Set.mem_Ioo] at ht
    have hu : Real.log t / L ∈ Set.Ioo (0:ℝ) x₀ := by
      refine ⟨div_pos (Real.log_pos ht.1) hLpos, ?_⟩
      rw [div_lt_iff₀ hLpos]
      have h1 : Real.log t < Real.log (N:ℝ) := Real.log_lt_log (by linarith only [ht.1, ht]) ht.2
      linarith only [hlogNle, h1]
    exact (hasDerivAt_wgt hLpos hfdiff ht.1 hu).differentiableAt
  have hIdG : IntervalIntegrable (deriv (wgt L σ f)) volume (1:ℝ) (N:ℝ) :=
    intervalIntegrable_deriv_wgt hx₀ hLpos hσ0 hN1 hNle hfdiff hfA hfB
  have hIpsiG : IntervalIntegrable (fun t : ℝ => Chebyshev.psi t * deriv (wgt L σ f) t)
      volume (1:ℝ) (N:ℝ) :=
    intervalIntegrable_psi_deriv_wgt hx₀ hLpos hσ0 hN1 hNle hfdiff hfA hfB
  have habel : (∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.vonMangoldt n : ℝ) * wgt L σ f (n:ℝ))
      = Chebyshev.psi (N:ℝ) * wgt L σ f (N:ℝ)
        - ∫ t in (1:ℝ)..(N:ℝ), Chebyshev.psi t * deriv (wgt L σ f) t :=
    psi_abel_integral N (wgt L σ f) hN1 hcontG hGdiff hIpsiG hIdG
  have habel' : (∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.vonMangoldt n : ℝ) *
        (n : ℝ) ^ (-(1 - lam / Real.log q)) * f (Real.log n / Real.log q))
      = Chebyshev.psi (N:ℝ) * wgt L σ f (N:ℝ)
        - ∫ t in (1:ℝ)..(N:ℝ), Chebyshev.psi t * deriv (wgt L σ f) t := by
    rw [← habel]
    exact Finset.sum_congr rfl (fun n _ => by ring)
  have hIt : IntervalIntegrable (fun t : ℝ => t * deriv (wgt L σ f) t) volume (1:ℝ) (N:ℝ) := by
    have h := hIdG.mul_continuousOn (continuous_id.continuousOn)
    exact h.congr (fun t _ => by simp [id_eq, mul_comm])
  have hIpsiSub : IntervalIntegrable
      (fun t : ℝ => (Chebyshev.psi t - t) * deriv (wgt L σ f) t) volume (1:ℝ) (N:ℝ) := by
    have h := hIpsiG.sub hIt
    exact h.congr (fun t _ => by ring_nf)
  have hibp : ∫ t in (1:ℝ)..(N:ℝ), t * deriv (wgt L σ f) t
      = (N:ℝ) * wgt L σ f (N:ℝ) - 1 * wgt L σ f 1
        - ∫ t in (1:ℝ)..(N:ℝ), wgt L σ f t := by
    have hder_u : ∀ x ∈ Set.Ioo (min (1:ℝ) (N:ℝ)) (max (1:ℝ) (N:ℝ)),
        HasDerivAt (fun t : ℝ => t) (1:ℝ) x := fun x _ => hasDerivAt_id x
    have hder_v : ∀ x ∈ Set.Ioo (min (1:ℝ) (N:ℝ)) (max (1:ℝ) (N:ℝ)),
        HasDerivAt (wgt L σ f) (deriv (wgt L σ f) x) x := by
      intro x hx
      rw [min_eq_left hN1', max_eq_right hN1'] at hx
      exact (hGdiff x hx).hasDerivAt
    have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
      (u := fun t : ℝ => t) (v := wgt L σ f) (u' := fun _ => (1:ℝ))
      (v' := deriv (wgt L σ f)) (a := (1:ℝ)) (b := (N:ℝ))
      continuousOn_id hcontGu hder_u hder_v intervalIntegrable_const hIdG
    simpa using h
  have hsplit : ∫ t in (1:ℝ)..(N:ℝ), Chebyshev.psi t * deriv (wgt L σ f) t
      = (∫ t in (1:ℝ)..(N:ℝ), t * deriv (wgt L σ f) t)
        + ∫ t in (1:ℝ)..(N:ℝ), (Chebyshev.psi t - t) * deriv (wgt L σ f) t := by
    rw [← intervalIntegral.integral_add hIt hIpsiSub]
    exact intervalIntegral.integral_congr (fun t _ => by ring)
  -- ### the main term
  let I : ℝ := ∫ u in (0:ℝ)..x₀, Real.exp (lam * u) * f u
  have hIval : I = ∫ u in (0:ℝ)..x₀, Real.exp (lam * u) * f u := rfl
  have hsubst : ∫ t in (1:ℝ)..((q:ℝ)^x₀), wgt L σ f t = L * I :=
    integral_rpow_log_subst x₀ lam hx₀ (q := (q:ℝ)) hq1 (hfcont.mono Set.Icc_subset_Ici_self)
  have hB1 : (1:ℝ) ≤ (q:ℝ)^x₀ := hqpow1
  have hItail : IntervalIntegrable (wgt L σ f) volume (N:ℝ) ((q:ℝ)^x₀) := by
    have hBe : Real.log ((q:ℝ)^x₀) / L ≤ x₀ := by
      have hne : Real.log (q:ℝ) ≠ 0 := ne_of_gt (Real.log_pos hq1)
      rw [Real.log_rpow hqpos, hLval, mul_div_assoc, div_self hne, mul_one]
    have h1 : IntervalIntegrable (wgt L σ f) volume (1:ℝ) ((q:ℝ)^x₀) :=
      intervalIntegrable_wgt hLpos hfcont hB1 hBe
    refine h1.mono_set ?_
    rw [Set.uIcc_of_le hNq, Set.uIcc_of_le hB1]
    exact Set.Icc_subset_Icc hN1' le_rfl
  have hIG : IntervalIntegrable (wgt L σ f) volume (1:ℝ) (N:ℝ) :=
    intervalIntegrable_wgt hLpos hfcont hN1' hlogN
  have hadj : (∫ t in (1:ℝ)..(N:ℝ), wgt L σ f t) + ∫ t in (N:ℝ)..((q:ℝ)^x₀), wgt L σ f t
      = ∫ t in (1:ℝ)..((q:ℝ)^x₀), wgt L σ f t :=
    intervalIntegral.integral_add_adjacent_intervals hIG hItail
  have htail : |∫ t in (N:ℝ)..((q:ℝ)^x₀), wgt L σ f t| ≤ M := by
    have hb : ∀ t ∈ Set.uIoc (N:ℝ) ((q:ℝ)^x₀), ‖wgt L σ f t‖ ≤ M := by
      intro t ht
      rw [Set.uIoc_of_le hNq, Set.mem_Ioc] at ht
      have ht1 : (1:ℝ) ≤ t := le_trans hN1' (le_of_lt ht.1)
      have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht1
      have hu : Real.log t / L ∈ Set.Icc (0:ℝ) x₀ := by
        refine ⟨div_nonneg (Real.log_nonneg ht1) hLpos.le, ?_⟩
        rw [div_le_iff₀ hLpos]
        have h1 : Real.log t ≤ Real.log ((q:ℝ)^x₀) := Real.log_le_log htpos ht.2
        rw [Real.log_rpow hqpos] at h1
        rw [hLval]
        exact h1
      rw [Real.norm_eq_abs, show wgt L σ f t = t ^ (-σ) * f (Real.log t / L) from rfl,
        abs_mul, abs_of_nonneg (Real.rpow_nonneg htpos.le _)]
      have hfr : |f (Real.log t / L)| ≤ M := by
        have h := hfA (Real.log t / L); rwa [Real.norm_eq_abs] at h
      calc t ^ (-σ) * |f (Real.log t / L)| ≤ 1 * M :=
            mul_le_mul (rpow_neg_le_one hσ0 ht1) hfr (abs_nonneg _) (by norm_num)
        _ = M := one_mul M
    have h1 := intervalIntegral.norm_integral_le_of_norm_le_const (a := (N:ℝ))
      (b := (q:ℝ)^x₀) hb
    have h2 : (q:ℝ)^x₀ - (N:ℝ) ≤ 1 := by
      have h3 : (q:ℝ)^x₀ < ((N : ℕ) : ℝ) + 1 := by
        rw [hNdef]; exact Nat.lt_floor_add_one _
      linarith only [h3]
    have h4 : (0:ℝ) ≤ (q:ℝ)^x₀ - (N:ℝ) := by linarith only [hqpow, hNle]
    rw [Real.norm_eq_abs] at h1
    calc |∫ t in (N:ℝ)..((q:ℝ)^x₀), wgt L σ f t| ≤ M * |(q:ℝ)^x₀ - (N:ℝ)| := h1
      _ = M * ((q:ℝ)^x₀ - (N:ℝ)) := by rw [abs_of_nonneg h4]
      _ ≤ M * 1 := mul_le_mul_of_nonneg_left h2 hM
      _ = M := by ring
  have hmain : (∫ t in (1:ℝ)..(N:ℝ), wgt L σ f t) ≤ L * I + M := by
    have h : (∫ t in (1:ℝ)..(N:ℝ), wgt L σ f t)
        = (∫ t in (1:ℝ)..((q:ℝ)^x₀), wgt L σ f t)
          - ∫ t in (N:ℝ)..((q:ℝ)^x₀), wgt L σ f t := by linarith only [hadj]
    rw [h, hsubst]
    linarith only [neg_le_abs (∫ t in (N:ℝ)..((q:ℝ)^x₀), wgt L σ f t), htail]
  -- ### boundary terms
  have hg1m : wgt L σ f 1 ≤ M := by
    have h : wgt L σ f 1 = f 0 := by
      rw [show wgt L σ f 1 = (1:ℝ) ^ (-σ) * f (Real.log 1 / L) from rfl,
        Real.one_rpow, Real.log_one, zero_div, one_mul]
    rw [h]
    have h2 : |f 0| ≤ M := by
      have h := hfA 0; rwa [Real.norm_eq_abs] at h
    exact le_trans (le_abs_self _) h2
  have hRNm : (Chebyshev.psi (N:ℝ) - N) * wgt L σ f (N:ℝ) ≤ K * Real.exp (R * x₀) * M := by
    have hp := hpsi (N:ℝ) hN1'
    have hw : |wgt L σ f (N:ℝ)| ≤ (N:ℝ) ^ (-σ) * M := by
      rw [show wgt L σ f (N:ℝ) = (N:ℝ) ^ (-σ) * f (Real.log (N:ℝ) / L) from rfl,
        abs_mul, abs_of_nonneg (Real.rpow_nonneg hNpos.le _)]
      have hfr : |f (Real.log (N:ℝ) / L)| ≤ M := by
        have h := hfA (Real.log (N:ℝ) / L); rwa [Real.norm_eq_abs] at h
      exact mul_le_mul_of_nonneg_left hfr (Real.rpow_nonneg hNpos.le _)
    have hNpow : (N:ℝ) ^ (1 - σ) ≤ Real.exp (R * x₀) := by
      rw [Real.rpow_def_of_pos hNpos]
      refine Real.exp_le_exp.mpr ?_
      have h1 : 1 - σ = lam / L := by rw [hσval]; ring
      rw [h1]
      have hlamL : 0 ≤ lam / L := by positivity
      calc Real.log (N:ℝ) * (lam / L) ≤ (x₀ * L) * (lam / L) :=
            mul_le_mul_of_nonneg_right hlogNle hlamL
        _ = lam * x₀ := by field_simp
        _ ≤ R * x₀ := by nlinarith only [hlamR, hx₀]
    have hneg : Real.exp (-c * Real.sqrt (Real.log (N:ℝ))) ≤ 1 := by
      rw [← Real.exp_zero]
      refine Real.exp_le_exp.mpr ?_
      have h1 : 0 ≤ Real.sqrt (Real.log (N:ℝ)) := Real.sqrt_nonneg _
      nlinarith only [hcpos, h1]
    have hkey : (N:ℝ) * (N:ℝ) ^ (-σ) = (N:ℝ) ^ (1 - σ) := by
      nth_rewrite 1 [show (N:ℝ) = (N:ℝ) ^ (1:ℝ) from (Real.rpow_one _).symm]
      rw [← Real.rpow_add hNpos]
      congr 1
    have hstep : (K * (N:ℝ) * Real.exp (-c * Real.sqrt (Real.log (N:ℝ)))) *
          ((N:ℝ) ^ (-σ) * M)
        = K * M * ((N:ℝ) ^ (1 - σ) * Real.exp (-c * Real.sqrt (Real.log (N:ℝ)))) := by
      have hr : (K * (N:ℝ) * Real.exp (-c * Real.sqrt (Real.log (N:ℝ)))) *
            ((N:ℝ) ^ (-σ) * M)
          = K * M * (Real.exp (-c * Real.sqrt (Real.log (N:ℝ))) *
              ((N:ℝ) * (N:ℝ) ^ (-σ))) := by ring
      rw [hr, hkey]
      ring
    have hp' := hpsi (N:ℝ) hN1'
    calc (Chebyshev.psi (N:ℝ) - N) * wgt L σ f (N:ℝ)
        ≤ |Chebyshev.psi (N:ℝ) - (N:ℝ)| * |wgt L σ f (N:ℝ)| := by
          rw [← abs_mul]; exact le_abs_self _
      _ ≤ (K * (N:ℝ) * Real.exp (-c * Real.sqrt (Real.log (N:ℝ)))) *
            ((N:ℝ) ^ (-σ) * M) :=
          mul_le_mul hp' hw (abs_nonneg _) (by positivity)
      _ = K * M * ((N:ℝ) ^ (1 - σ) * Real.exp (-c * Real.sqrt (Real.log (N:ℝ)))) := hstep
      _ ≤ K * M * (Real.exp (R * x₀) * 1) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul hNpow hneg (Real.exp_nonneg _) (Real.exp_pos _).le
      _ = K * Real.exp (R * x₀) * M := by ring
  -- ### the error integral
  have hErrm : -(∫ t in (1:ℝ)..(N:ℝ), (Chebyshev.psi t - t) * deriv (wgt L σ f) t)
      ≤ 2 * K * Real.exp (R * x₀) / c ^ 2 * (M + M') := by
    have hne : ∀ᵐ t ∂volume, t ≠ (N:ℝ) := by
      rw [MeasureTheory.ae_iff]
      have h0 : volume {t : ℝ | ¬ t ≠ (N:ℝ)} = 0 := by
        rw [show {t : ℝ | ¬ t ≠ (N:ℝ)} = {(N:ℝ)} from by ext t; simp]
        exact measure_singleton _
      exact h0
    have hpt : ∀ᵐ t ∂volume, t ∈ Set.Ioc (1:ℝ) (N:ℝ) →
        ‖(Chebyshev.psi t - t) * deriv (wgt L σ f) t‖
          ≤ K * (σ * M + M' / L) *
              (Real.exp (-c * Real.sqrt (Real.log t)) * t ^ (-σ)) := by
      refine hne.mono (fun t hte ht => ?_)
      rw [Set.mem_Ioc] at ht
      have ht1 : (1:ℝ) < t := ht.1
      have htpos : 0 < t := by linarith only [ht]
      have hu : Real.log t / L ∈ Set.Ioo (0:ℝ) x₀ := by
        refine ⟨div_pos (Real.log_pos ht1) hLpos, ?_⟩
        rw [div_lt_iff₀ hLpos]
        have h1 : Real.log t < Real.log (N:ℝ) :=
          Real.log_lt_log htpos (lt_of_le_of_ne ht.2 hte)
        linarith only [hlogNle, h1]
      have hd := deriv_wgt (σ := σ) hLpos hfdiff ht1 hu
      have hb := abs_wgtD_le hLpos hσ0 hfA hfB (le_of_lt ht1) ⟨le_of_lt hu.1, le_of_lt hu.2⟩
      have hp := hpsi t (le_of_lt ht1)
      rw [Real.norm_eq_abs, abs_mul, hd]
      have hkey : t * t ^ (-σ - 1) = t ^ (-σ) := by
        nth_rewrite 1 [show t = t ^ (1:ℝ) from (Real.rpow_one t).symm]
        rw [← Real.rpow_add htpos]
        congr 1
        ring
      calc |Chebyshev.psi t - t| * |wgtD L σ f t|
          ≤ (K * t * Real.exp (-c * Real.sqrt (Real.log t))) *
              ((σ * M + M' / L) * t ^ (-σ - 1)) :=
            mul_le_mul hp hb (abs_nonneg _) (by positivity)
        _ = K * (σ * M + M' / L) *
              (Real.exp (-c * Real.sqrt (Real.log t)) * (t * t ^ (-σ - 1))) := by ring
        _ = K * (σ * M + M' / L) *
              (Real.exp (-c * Real.sqrt (Real.log t)) * t ^ (-σ)) := by rw [hkey]
    have hcontg : ContinuousOn (fun t : ℝ => K * (σ * M + M' / L) *
        (Real.exp (-c * Real.sqrt (Real.log t)) * t ^ (-σ))) (Set.uIcc (1:ℝ) (N:ℝ)) :=
      (continuousOn_decay c σ (1:ℝ) (N:ℝ) zero_lt_one hN1').const_mul _
    have h1 := intervalIntegral.norm_integral_le_of_norm_le hN1' hpt hcontg.intervalIntegrable
    rw [Real.norm_eq_abs] at h1
    have h2 : (∫ t in (1:ℝ)..(N:ℝ), K * (σ * M + M' / L) *
        (Real.exp (-c * Real.sqrt (Real.log t)) * t ^ (-σ)))
        = K * (σ * M + M' / L) *
          ∫ t in (1:ℝ)..(N:ℝ), Real.exp (-c * Real.sqrt (Real.log t)) * t ^ (-σ) :=
      intervalIntegral.integral_const_mul _ _
    rw [h2] at h1
    have h3 : (∫ t in (1:ℝ)..(N:ℝ), Real.exp (-c * Real.sqrt (Real.log t)) * t ^ (-σ))
        ≤ 2 * Real.exp (R * x₀) / c ^ 2 := by
      have hmono : (∫ t in (1:ℝ)..(N:ℝ), Real.exp (-c * Real.sqrt (Real.log t)) * t ^ (-σ))
          ≤ ∫ t in (1:ℝ)..((q:ℝ)^x₀),
              Real.exp (-c * Real.sqrt (Real.log t)) * t ^ (-σ) := by
        refine intervalIntegral.integral_mono_interval le_rfl hN1' hNq ?_ ?_
        · filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with x hx
          rw [Set.mem_Ioc] at hx
          exact mul_nonneg (Real.exp_nonneg _) (Real.rpow_nonneg (by linarith only [hx.1, hx]) _)
        · exact (continuousOn_decay c σ (1:ℝ) ((q:ℝ)^x₀) zero_lt_one hB1).intervalIntegrable
      have hd := integral_exp_neg_sqrt_log_rpow_le x₀ R lam c hx₀ hcpos hlam hlamR
        (q := (q:ℝ)) hq1
      refine le_trans hmono ?_
      refine le_trans (le_of_eq ?_) hd
      exact intervalIntegral.integral_congr (fun t _ => by
        rw [show σ = 1 - lam / L from hσval, show L = Real.log q from hLval])
    have hcoef : 0 ≤ 2 * K * Real.exp (R * x₀) / c ^ 2 := by positivity
    have hinner : σ * M + M' / L ≤ M + M' := by
      have h1 : σ * M ≤ M := by
        calc σ * M ≤ 1 * M := mul_le_mul_of_nonneg_right hσ1 hM
          _ = M := one_mul M
      have h2 : M' / L ≤ M' := by
        rw [div_le_iff₀ hLpos]
        nlinarith only [hM', hL1]
      linarith only [h1, h2]
    have hcoef2 : 0 ≤ K * (σ * M + M' / L) := by positivity
    have h4 : K * (σ * M + M' / L) *
          (∫ t in (1:ℝ)..(N:ℝ), Real.exp (-c * Real.sqrt (Real.log t)) * t ^ (-σ))
        ≤ K * (σ * M + M' / L) * (2 * Real.exp (R * x₀) / c ^ 2) :=
      mul_le_mul_of_nonneg_left h3 hcoef2
    calc -(∫ t in (1:ℝ)..(N:ℝ), (Chebyshev.psi t - t) * deriv (wgt L σ f) t)
        ≤ |∫ t in (1:ℝ)..(N:ℝ), (Chebyshev.psi t - t) * deriv (wgt L σ f) t| :=
          neg_le_abs _
      _ ≤ K * (σ * M + M' / L) * (2 * Real.exp (R * x₀) / c ^ 2) := le_trans h1 h4
      _ = 2 * K * Real.exp (R * x₀) / c ^ 2 * (σ * M + M' / L) := by ring
      _ ≤ 2 * K * Real.exp (R * x₀) / c ^ 2 * (M + M') := mul_le_mul_of_nonneg_left hinner hcoef
  -- ### assembly
  have hS : Ssum = (Chebyshev.psi (N:ℝ) - (N:ℝ)) * wgt L σ f (N:ℝ) + wgt L σ f 1
      + (∫ t in (1:ℝ)..(N:ℝ), wgt L σ f t)
      - ∫ t in (1:ℝ)..(N:ℝ), (Chebyshev.psi t - t) * deriv (wgt L σ f) t := by
    rw [show Ssum = ∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.vonMangoldt n : ℝ) *
        (n : ℝ) ^ (-(1 - lam / Real.log q)) * f (Real.log n / Real.log q) from rfl, habel',
      hsplit, hibp]
    ring
  have hfin : Ssum ≤ L * I + C₀ * (M + M') := by
    have h1 : Ssum ≤ K * Real.exp (R * x₀) * M + M + (L * I + M)
        + 2 * K * Real.exp (R * x₀) / c ^ 2 * (M + M') := by
      rw [hS]
      linarith only [hRNm, hg1m, hmain, hErrm]
    have hCval : C₀ = 2 + K * Real.exp (R * x₀) + 2 * K * Real.exp (R * x₀) / c ^ 2 := rfl
    have hEpos : 0 < Real.exp (R * x₀) := Real.exp_pos _
    have hcoef : 0 ≤ K * Real.exp (R * x₀) + 2 := by positivity
    have hMsum : M ≤ M + M' := by linarith only [hM']
    have hkey : K * Real.exp (R * x₀) * M + M + (L * I + M)
        + 2 * K * Real.exp (R * x₀) / c ^ 2 * (M + M')
        ≤ L * I + C₀ * (M + M') := by
      rw [hCval]
      linarith only [hMsum, mul_le_mul_of_nonneg_left hMsum hcoef, hM, hM', hKnn, hEpos.le, hc2.le, hcoef]
    linarith only [h1, hkey, habel', hibp, hsplit, hmain, hg1m, hRNm, hErrm]
  -- ### conclusion
  rw [htsum]
  have hstep1 : (Real.log q)⁻¹ * Ssum ≤ (Real.log q)⁻¹ * (L * I + C₀ * (M + M')) :=
    mul_le_mul_of_nonneg_left hfin (by positivity)
  have hstep2 : (Real.log q)⁻¹ * (L * I + C₀ * (M + M')) = I + C₀ * (M + M') / Real.log q := by
    have hLne : Real.log q ≠ 0 := by rw [← hLval]; exact ne_of_gt hLpos
    rw [hLval]
    field_simp
  rw [hstep2] at hstep1
  exact hstep1

end

end Work.LinnikAreas.A5
