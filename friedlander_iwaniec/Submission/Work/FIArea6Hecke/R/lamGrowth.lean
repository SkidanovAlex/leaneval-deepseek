import Mathlib
import Submission.Work.FIArea6Hecke.R.logDerivCore
import Submission.Work.FIArea6Hecke.R.noCompletion_of_primaryTrivial
import Submission.Work.FIArea6Hecke.R.lamRightHalf_strict
import Submission.Work.FIArea6Hecke.R.HeckeCompletionAll
import Submission.Work.FIArea6Hecke.R.LamRightHalf.completion_growth
import Submission.Work.FIArea6Hecke.R.LamRightHalf.thetaHol_one_div_dual
import Submission.Work.FIArea6Hecke.R.LamRightHalf.thetaDualM_decay
import Submission.Work.FIArea6Hecke.R.heckeLambda_eq_LambdaHecke
import Submission.Work.FIArea6Hecke.R.mellin_thetaDualMG_growth
import Submission.Work.FIArea5.S16Hecke.heckeLSeries_conj
import Submission.Work.FIArea5.S16Hecke.twist_unitSum

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIArea6Hecke.R

open Complex

noncomputable section

/-! ## Uniqueness and reflection helpers

These two elementary facts about entire functions are used to move between the right half-plane
and the whole plane.  They are kept here for reuse; the final argument (below) already contains
its own copy of the reflection bookkeeping. -/

/-- **Uniqueness on a right half-plane.**  Two entire functions agreeing on `{T < Re s}` are
equal.  (The `T = 1` case is `ZFRDefs.eq_of_agrees_right`; here we need `T = 1 + |m|/2`.) -/
lemma eq_of_agrees_right' {G Lam : ℂ → ℂ} {T : ℝ}
    (hG : AnalyticOn ℂ G Set.univ) (hL : AnalyticOn ℂ Lam Set.univ)
    (h : ∀ s : ℂ, T < s.re → Lam s = G s) : Lam = G := by
  have hG' : AnalyticOnNhd ℂ G Set.univ := analyticOn_univ.mp hG
  have hL' : AnalyticOnNhd ℂ Lam Set.univ := analyticOn_univ.mp hL
  have hev : (fun s : ℂ => Lam s - G s) =ᶠ[nhds (((T + 1 : ℝ)) : ℂ)] 0 := by
    filter_upwards [Metric.ball_mem_nhds (((T + 1 : ℝ)) : ℂ) (by norm_num : (0 : ℝ) < 1)]
      with s hs
    have h1 : ‖s - (((T + 1 : ℝ)) : ℂ)‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hs
    have h2 : |s.re - (T + 1)| ≤ ‖s - (((T + 1 : ℝ)) : ℂ)‖ := by
      simpa using Complex.abs_re_le_norm (s - (((T + 1 : ℝ)) : ℂ))
    have h3 : T < s.re := by
      have h4 := lt_of_le_of_lt h2 h1
      rw [abs_lt] at h4
      linarith [h4.1]
    simp [h s h3]
  have hzero : (fun s : ℂ => Lam s - G s) = 0 :=
    AnalyticOnNhd.eq_of_eventuallyEq (hL'.sub hG') (fun z _ => analyticAt_const) hev
  funext s
  exact sub_eq_zero.mp (congrFun hzero s)

open Work.FIArea5.S16Hecke
open MeasureTheory Set

/-! ## Conjugation helpers -/

lemma psi_conj_neg (chi : GaussianInt → ℂ) (k : ℕ) (z : GaussianInt) :
    star (psi chi (-(k : ℤ)) z)
      = psi (fun z : GaussianInt => star (chi z)) (k : ℤ) z := by
  have h := psi_conj (fun z : GaussianInt => star (chi z)) k z
  rw [show (fun z : GaussianInt => star (star (chi z))) = chi from
    funext (fun z => star_star (chi z))] at h
  rw [h, star_star]

lemma heckeLSeries_conj_neg (chi : GaussianInt → ℂ) (k : ℕ) (s : ℂ) :
    star (heckeLSeries chi (-(k : ℤ)) (star s))
      = heckeLSeries (fun z : GaussianInt => star (chi z)) (k : ℤ) s := by
  have h := heckeLSeries_conj (fun z : GaussianInt => star (chi z)) k (star s)
  rw [show (fun z : GaussianInt => star (star (chi z))) = chi from
    funext (fun z => star_star (chi z)), star_star] at h
  rw [h, star_star]

/-- Vanishing of the first Fourier coefficient of the twist, from the non-triviality of `ψ_k`
on the primary units. -/
lemma gaussSum_zero_of_psi_ne_aux (d : ℕ) (hd : 1 ≤ d) (k : ℕ)
    {chi : GaussianInt → ℂ} (hchi : IsCharMod4dStrict d chi)
    (hne : ∃ z : GaussianInt, Work.FIPlan.IsPrimary z ∧ IsUnitMod4d d z ∧
      psi chi (k : ℤ) z ≠ 1) :
    k = 0 → gaussSum d (twist chi k) 0 = 0 := by
  intro hk0
  subst hk0
  obtain ⟨z, hz1, hz2, hz3⟩ := hne
  have hzchi : chi z ≠ 1 := by
    have h1 : psi chi (0 : ℤ) z = chi z := by simp [psi]
    simp only [Nat.cast_zero] at hz3
    rwa [h1] at hz3
  have hchi' : IsCharMod4dStrict d (twist chi 0) :=
    twist_isCharMod4dStrict d hd chi 0 hchi
  refine gaussSum_zero_of_nontrivial hd hchi' ⟨z, hz1, hz2, ?_⟩
  rw [twist_eq_of_isPrimary chi 0 hz1]
  exact hzchi

/-! ## Two elementary combinations of growth constants -/

/-- The combination of growth estimates used on the left half-plane. -/
lemma leftCombine {R c C₂ K₁ K₂ L M zr : ℝ}
    (hR : 1 ≤ R) (hc : 0 ≤ c) (hC₂ : 0 ≤ C₂) (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (hL : 0 ≤ L) (hM : 0 ≤ M) (hzr : zr ≤ R) :
    zr * L + M + C₂ * R * (Real.log (R + 2) + K₂)
      ≤ (max (5 * c) C₂ + L + M + 1) * R * (Real.log (R + 2) + (K₁ + K₂ + Real.log 3 + 1)) := by
  have hR0 : 0 ≤ R := by linarith
  have hlog2 : 0 ≤ Real.log (R + 2) := Real.log_nonneg (by linarith)
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hbr : 0 ≤ Real.log (R + 2) + (K₁ + K₂ + Real.log 3 + 1) := by linarith
  have hbr1 : 1 ≤ Real.log (R + 2) + (K₁ + K₂ + Real.log 3 + 1) := by linarith
  have hX0 : 0 ≤ R * (Real.log (R + 2) + (K₁ + K₂ + Real.log 3 + 1)) := mul_nonneg hR0 hbr
  have e1 : zr * L ≤ L * R * (Real.log (R + 2) + (K₁ + K₂ + Real.log 3 + 1)) := by
    have h1 : zr * L ≤ R * L := by nlinarith [hzr, hL]
    have h2 : R * L ≤ R * L * (Real.log (R + 2) + (K₁ + K₂ + Real.log 3 + 1)) := by
      nlinarith [mul_nonneg hR0 hL, hbr1]
    linarith [h1, h2]
  have e2 : M ≤ M * R * (Real.log (R + 2) + (K₁ + K₂ + Real.log 3 + 1)) := by
    have h1 : 1 ≤ R * (Real.log (R + 2) + (K₁ + K₂ + Real.log 3 + 1)) := by nlinarith
    have h2 := le_mul_of_one_le_left hM h1
    linarith [h2]
  have e3 : C₂ * R * (Real.log (R + 2) + K₂)
      ≤ max (5 * c) C₂ * (R * (Real.log (R + 2) + (K₁ + K₂ + Real.log 3 + 1))) := by
    have hle : Real.log (R + 2) + K₂ ≤ Real.log (R + 2) + (K₁ + K₂ + Real.log 3 + 1) := by
      linarith
    have h1 : C₂ * R * (Real.log (R + 2) + K₂)
        ≤ C₂ * R * (Real.log (R + 2) + (K₁ + K₂ + Real.log 3 + 1)) := by
      exact mul_le_mul_of_nonneg_left hle (mul_nonneg hC₂ hR0)
    have h2 : C₂ * R * (Real.log (R + 2) + (K₁ + K₂ + Real.log 3 + 1))
        ≤ max (5 * c) C₂ * (R * (Real.log (R + 2) + (K₁ + K₂ + Real.log 3 + 1))) := by
      have h0 : 0 ≤ R * (Real.log (R + 2) + (K₁ + K₂ + Real.log 3 + 1)) :=
        mul_nonneg hR0 hbr
      have h1 : C₂ ≤ max (5 * c) C₂ := le_max_right _ _
      nlinarith [h0, h1]
    linarith [h1, h2]
  have e4 : L * R * (Real.log (R + 2) + (K₁ + K₂ + Real.log 3 + 1))
      + M * R * (Real.log (R + 2) + (K₁ + K₂ + Real.log 3 + 1))
      + max (5 * c) C₂ * (R * (Real.log (R + 2) + (K₁ + K₂ + Real.log 3 + 1)))
      ≤ max (5 * c) C₂ * (R * (Real.log (R + 2) + (K₁ + K₂ + Real.log 3 + 1)))
      + L * R * (Real.log (R + 2) + (K₁ + K₂ + Real.log 3 + 1))
      + M * R * (Real.log (R + 2) + (K₁ + K₂ + Real.log 3 + 1))
      + R * (Real.log (R + 2) + (K₁ + K₂ + Real.log 3 + 1)) := by
    nlinarith [hX0]
  have e5 : max (5 * c) C₂ * (R * (Real.log (R + 2) + (K₁ + K₂ + Real.log 3 + 1)))
      + L * R * (Real.log (R + 2) + (K₁ + K₂ + Real.log 3 + 1))
      + M * R * (Real.log (R + 2) + (K₁ + K₂ + Real.log 3 + 1))
      + R * (Real.log (R + 2) + (K₁ + K₂ + Real.log 3 + 1))
      = (max (5 * c) C₂ + L + M + 1) * R * (Real.log (R + 2) + (K₁ + K₂ + Real.log 3 + 1)) := by
    ring
  linarith [e1, e2, e3, e4, e5.le, e5.ge]

/-- The combination of growth estimates used on the right half-plane. -/
lemma rightCombine {R c C₂ K₁ K₂ L M : ℝ}
    (hR : 1 ≤ R) (hc : 0 ≤ c) (hC₂ : 0 ≤ C₂) (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (hL : 0 ≤ L) (hM : 0 ≤ M) :
    c * (R + 3) * (Real.log (R + 5) + K₁)
      ≤ (max (5 * c) C₂ + L + M + 1) * R * (Real.log (R + 2) + (K₁ + K₂ + Real.log 3 + 1)) := by
  have hR0 : 0 ≤ R := by linarith
  have hlog2 : 0 ≤ Real.log (R + 2) := Real.log_nonneg (by linarith)
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlog5 : 0 ≤ Real.log (R + 5) := Real.log_nonneg (by linarith)
  have hR5 : Real.log (R + 5) ≤ Real.log (R + 2) + Real.log 3 := by
    have h := Real.log_le_log (by linarith : (0 : ℝ) < R + 5)
      (by linarith : R + 5 ≤ (R + 2) * 3)
    rw [Real.log_mul (by linarith : (R : ℝ) + 2 ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)] at h
    exact h
  have hbr : 0 ≤ Real.log (R + 2) + (K₁ + K₂ + Real.log 3 + 1) := by linarith
  have hstep : c * (R + 3) * (Real.log (R + 5) + K₁)
      ≤ 5 * c * (R * (Real.log (R + 2) + (K₁ + K₂ + Real.log 3 + 1))) := by
    have h0 : 0 ≤ Real.log (R + 5) + K₁ := by linarith
    have h1 : R + 3 ≤ 5 * R := by linarith
    have h2 : Real.log (R + 5) + K₁ ≤ Real.log (R + 2) + (K₁ + K₂ + Real.log 3 + 1) := by
      linarith
    have h3 : (R + 3) * (Real.log (R + 5) + K₁)
        ≤ (5 * R) * (Real.log (R + 2) + (K₁ + K₂ + Real.log 3 + 1)) :=
      mul_le_mul h1 h2 h0 (by linarith)
    calc c * (R + 3) * (Real.log (R + 5) + K₁)
        = c * ((R + 3) * (Real.log (R + 5) + K₁)) := by ring
      _ ≤ c * ((5 * R) * (Real.log (R + 2) + (K₁ + K₂ + Real.log 3 + 1))) :=
          mul_le_mul_of_nonneg_left h3 hc
      _ = 5 * c * (R * (Real.log (R + 2) + (K₁ + K₂ + Real.log 3 + 1))) := by ring
  have hfinal : 5 * c * (R * (Real.log (R + 2) + (K₁ + K₂ + Real.log 3 + 1)))
      ≤ (max (5 * c) C₂ + L + M + 1) * R * (Real.log (R + 2) + (K₁ + K₂ + Real.log 3 + 1)) := by
    have h0 : 0 ≤ R * (Real.log (R + 2) + (K₁ + K₂ + Real.log 3 + 1)) := mul_nonneg hR0 hbr
    have hmx : 5 * c ≤ max (5 * c) C₂ + L + M + 1 := by linarith [le_max_left (5 * c) C₂]
    nlinarith [h0, hmx]
  linarith [hstep, hfinal]

/-! ## The circle growth for non-negative weight -/

/-- **Circle growth of an admissible completion, weight `k ≥ 0`.**  Route: the completion is the
Mellin transform of the weight-`k` theta series, whose weak functional equation (Mathlib's
`WeakFEPair.functional_equation`) reflects the left half-plane `re ≤ 1/2` to the right half-plane
`re ≥ 1/2`, where `Work.FIArea6Hecke.R.lamRightHalf_strict` applies; the reflected factor is the
Mellin transform of the dual kernel, controlled by `mellin_thetaDualMG_growth`. -/
theorem growth_nat (d : ℕ) (hd : 1 ≤ d) (chi : GaussianInt → ℂ) (k : ℕ)
    (hchi : IsCharMod4dStrict d chi)
    (hne : ∃ z : GaussianInt, Work.FIPlan.IsPrimary z ∧ IsUnitMod4d d z ∧
      psi chi (k : ℤ) z ≠ 1)
    (Lam : ℂ → ℂ) (hAn : AnalyticOn ℂ Lam Set.univ)
    (hagr : ∀ s : ℂ, 1 + (k : ℝ) / 2 < s.re →
      Lam s = Work.FITop4.Bridge.heckeArch d (k : ℤ) s * heckeLSeries chi (k : ℤ) s) :
    ∃ C K : ℝ, 0 < C ∧ 0 ≤ K ∧ ∀ R : ℝ, 1 ≤ R → ∀ z : ℂ, ‖z‖ = R →
      Real.log ‖Lam z‖ ≤ C * R * (Real.log (R + 2) + K) := by
  have habsk : |(((k : ℤ)) : ℝ)| = (k : ℝ) := by
    rw [Int.cast_natCast]; exact abs_of_nonneg (by positivity)
  obtain ⟨c, K₁, hc0, hK₁, hHalf⟩ :=
    lamRightHalf_strict d chi (k : ℤ) Lam hd hchi hne hAn
      (fun s hs => hagr s (by rw [habsk] at hs; exact hs))
  have hchi' : IsCharMod4dStrict d (twist chi k) :=
    twist_isCharMod4dStrict d hd chi k hchi
  have hb' : ∀ z : GaussianInt, ‖twist chi k z‖ ≤ 1 := hchi'.1.2.2.1
  have hU' : unitSum (twist chi k) k ≠ 0 := by
    rw [twist_unitSum d hd chi k hchi.1]; norm_num
  have h0' := gaussSum_zero_of_psi_ne_aux d hd k hchi hne
  have hf_int : LocallyIntegrableOn (fun u : ℝ => thetaHol (twist chi k) k u) (Set.Ioi 0) :=
    (continuousOn_thetaHol_Ioi (m := k) hb').locallyIntegrableOn measurableSet_Ioi
  have hg_cont : ContinuousOn (thetaDualMG d (twist chi k) k) (Set.Ioi 0) := by
    refine ((thetaDualM_continuous d hb' k).comp
      (continuous_id.div_const _).continuousOn ?_).const_mul _
    intro x hx
    simp only [Set.mem_Ioi] at hx ⊢
    positivity
  have hg_int : LocallyIntegrableOn (thetaDualMG d (twist chi k) k) (Set.Ioi 0) :=
    hg_cont.locallyIntegrableOn measurableSet_Ioi
  obtain ⟨Cf, hCf0, hdecf⟩ := thetaHol_exp_decay d hd (twist chi k) k hb'
  have hf_dec : ∃ C u₀ : ℝ, 0 < u₀ ∧ ∀ u : ℝ, u₀ ≤ u →
      ‖thetaHol (twist chi k) k u‖ ≤ C * Real.exp (-Real.pi * u) := by
    refine ⟨Cf * Real.exp (Real.pi * thetaC d), thetaC d, thetaC_pos hd, fun u hu => ?_⟩
    refine (hdecf u hu).trans_eq ?_
    rw [show -Real.pi * (u - thetaC d) = -Real.pi * u + Real.pi * thetaC d by ring,
      Real.exp_add]
    ring
  obtain ⟨Cg, hdecg⟩ := thetaDualM_decay d hd hb' k h0'
  have hg_dec : ∃ C u₀ : ℝ, 0 < u₀ ∧ ∀ u : ℝ, u₀ ≤ u →
      ‖thetaDualMG d (twist chi k) k u‖
        ≤ C * Real.exp (-(Real.pi / (16 * (d : ℝ) ^ 2)) * u) := by
    refine ⟨‖dualConst d (twist chi k) k‖ * Cg, 16 * (d : ℝ) ^ 2, by positivity,
      fun u hu => ?_⟩
    have harg : (1 : ℝ) ≤ u / (16 * (d : ℝ) ^ 2) := by
      rw [le_div_iff₀ (by positivity)]
      linarith
    rw [thetaDualMG, norm_mul]
    calc ‖dualConst d (twist chi k) k‖ *
            ‖thetaDualM d (twist chi k) k (u / (16 * (d : ℝ) ^ 2))‖
        ≤ ‖dualConst d (twist chi k) k‖ *
            (Cg * Real.exp (-Real.pi * (u / (16 * (d : ℝ) ^ 2)))) :=
          mul_le_mul_of_nonneg_left (hdecg _ harg) (norm_nonneg _)
      _ = (‖dualConst d (twist chi k) k‖ * Cg) *
            Real.exp (-(Real.pi / (16 * (d : ℝ) ^ 2)) * u) := by
          rw [show -Real.pi * (u / (16 * (d : ℝ) ^ 2))
              = -(Real.pi / (16 * (d : ℝ) ^ 2)) * u by ring]
          ring
  let P : WeakFEPair ℂ :=
    { f := fun u : ℝ => thetaHol (twist chi k) k u
      g := thetaDualMG d (twist chi k) k
      k := ((k + 1 : ℕ) : ℝ)
      ε := 1
      f₀ := 0
      g₀ := 0
      hf_int := hf_int
      hg_int := hg_int
      hk := by positivity
      hε := one_ne_zero
      h_feq := fun x hx => thetaHol_one_div_dual d hd hchi' k hU' hx
      hf_top := fun r => by
        simpa only [sub_zero] using isBigO_rpow_of_exp_decay Real.pi_pos hf_dec r
      hg_top := fun r => by
        simpa only [sub_zero] using isBigO_rpow_of_exp_decay (by positivity) hg_dec r }
  have hstrong : IsStrongFEPair P := ⟨rfl, rfl⟩
  have hΛ : P.Λ = mellin (fun u : ℝ => thetaHol (twist chi k) k u) :=
    IsStrongFEPair.Λ_eq hstrong
  have hsymmΛ : P.symm.Λ = mellin (thetaDualMG d (twist chi k) k) :=
    IsStrongFEPair.Λ_eq (IsStrongFEPair.symm hstrong)
  set Λc : ℂ → ℂ := fun s => (((4 * d : ℕ) : ℂ)) ^ s *
      ((Real.pi : ℂ) ^ ((k : ℂ) / 2)) * P.Λ (s + (k : ℂ) / 2) with hΛcdef
  have h4dpos : (0 : ℝ) < 4 * (d : ℝ) := by
    have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have hΛ4d : (((4 * d : ℕ) : ℂ)) ≠ 0 := by
    rw [show (((4 * d : ℕ) : ℂ)) = (((4 * (d : ℝ)) : ℝ) : ℂ) by push_cast; ring]
    rw [Complex.ofReal_ne_zero]; exact ne_of_gt h4dpos
  have hΛcan : AnalyticOn ℂ Λc Set.univ := by
    refine DifferentiableOn.analyticOn ?_ isOpen_univ
    intro s _
    exact (((differentiableAt_id.const_cpow (Or.inl hΛ4d)).mul
      (differentiableAt_const (((Real.pi : ℂ) ^ ((k : ℂ) / 2))))).mul
      ((hstrong.differentiable_Λ.differentiableAt).comp s
        (differentiableAt_id.add_const _))).differentiableWithinAt
  have hΛcagr : ∀ s : ℂ, 1 + (k : ℝ) / 2 < s.re →
      Λc s = Work.FITop4.Bridge.heckeArch d (k : ℤ) s * heckeLSeries chi (k : ℤ) s := by
    intro s hs
    have hsub : s + (k : ℂ) / 2 - (k : ℂ) / 2 = s := by ring
    have hk2 : ((k : ℂ) / 2) = (((k : ℝ) / 2 : ℝ) : ℂ) := by push_cast; ring
    have hs' : 1 + (k : ℝ) / 2 < (s + (k : ℂ) / 2).re := by
      rw [Complex.add_re, hk2, Complex.ofReal_re]
      linarith [hs, (by positivity : (0 : ℝ) ≤ (k : ℝ) / 2)]
    have hmellin := mellin_thetaHol_eq (twist chi k) k hb' (s := s + (k : ℂ) / 2) hs'
    simp only [hΛcdef]
    calc (((4 * d : ℕ) : ℂ)) ^ s * ((Real.pi : ℂ) ^ ((k : ℂ) / 2)) *
            P.Λ (s + (k : ℂ) / 2)
        = (((4 * d : ℕ) : ℂ)) ^ s * ((Real.pi : ℂ) ^ ((k : ℂ) / 2)) *
            mellin (thetaHol (twist chi k) k) (s + (k : ℂ) / 2) := by rw [hΛ]
      _ = (((4 * d : ℕ) : ℂ)) ^ s * ((Real.pi : ℂ) ^ ((k : ℂ) / 2)) *
            (Complex.Gamma (s + (k : ℂ) / 2) * (Real.pi : ℂ) ^ (-(s + (k : ℂ) / 2)) *
              heckeLSeries (twist chi k) (k : ℤ) (s + (k : ℂ) / 2 - (k : ℂ) / 2)) := by
            rw [hmellin]
      _ = (((4 * d : ℕ) : ℂ)) ^ s * ((Real.pi : ℂ) ^ ((k : ℂ) / 2)) *
            (Complex.Gamma (s + (k : ℂ) / 2) * (Real.pi : ℂ) ^ (-(s + (k : ℂ) / 2)) *
              heckeLSeries chi (k : ℤ) s) := by
            rw [hsub, heckeLSeries_twist]
      _ = Work.FITop4.Bridge.heckeArch d (k : ℤ) s * heckeLSeries chi (k : ℤ) s := by
            rw [Work.FITop4.Bridge.heckeArch]
            have hgam : s + ((|(((k : ℤ)) : ℝ)| / 2 : ℝ) : ℂ) = s + (k : ℂ) / 2 := by
              congr 1
              rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (((k : ℤ)) : ℝ))]
              push_cast; ring
            rw [hgam]
            have hbas : (((4 * d : ℕ) : ℂ)) = (((4 * (d : ℝ)) : ℝ) : ℂ) := by
              push_cast; ring
            rw [hbas]
            have hfour : (((4 * (d : ℝ)) : ℝ) : ℂ) ^ s * ((Real.pi : ℂ) ^ ((k : ℂ) / 2)) *
                ((Real.pi : ℂ) ^ (-(s + (k : ℂ) / 2))) = (4 * ((d : ℝ) : ℂ) / (Real.pi : ℂ)) ^ s := by
              rw [show (((4 * (d : ℝ)) : ℝ) : ℂ) = (((4 * d : ℕ) : ℂ)) by push_cast; ring]
              rw [Work.FIArea5.S16Hecke.fourd_pow_pi_pow d hd k s]
              congr 1
              push_cast; ring
            rw [show (((4 * (d : ℝ)) : ℝ) : ℂ) ^ s * ((Real.pi : ℂ) ^ ((k : ℂ) / 2)) *
                    (Complex.Gamma (s + (k : ℂ) / 2) * (Real.pi : ℂ) ^ (-(s + (k : ℂ) / 2)) *
                      heckeLSeries chi (k : ℤ) s)
                  = (((4 * (d : ℝ)) : ℝ) : ℂ) ^ s * ((Real.pi : ℂ) ^ ((k : ℂ) / 2)) *
                      (Real.pi : ℂ) ^ (-(s + (k : ℂ) / 2)) *
                    (Complex.Gamma (s + (k : ℂ) / 2) * heckeLSeries chi (k : ℤ) s) from by ring]
            rw [hfour]
            ring
  have hEq : Lam = Λc :=
    eq_of_agrees_right (T := 1 + (k : ℝ) / 2) hΛcan hAn
      (fun s hs => by rw [hagr s hs, hΛcagr s hs])
  obtain ⟨C₂, K₂, hC₂, hK₂, hDbound⟩ := mellin_thetaDualMG_growth d hd hchi' k hU' h0'
  have hlog4d : 0 ≤ Real.log (4 * (d : ℝ)) := by
    refine Real.log_nonneg ?_
    have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have hlogpi : 0 < Real.log Real.pi := Real.log_pos (by linarith [Real.pi_gt_three])
  have hknn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hkn2 : (0 : ℝ) ≤ (k : ℝ) / 2 := by positivity
  have hM0 : 0 ≤ ((k : ℝ) / 2) * Real.log Real.pi := mul_nonneg hkn2 hlogpi.le
  have hCbig : 0 < max (5 * c) C₂ + Real.log (4 * (d : ℝ))
      + ((k : ℝ) / 2) * Real.log Real.pi + 1 := by
    linarith [le_max_left (5 * c) C₂, hc0, hlog4d, hM0]
  have hKbig : 0 ≤ K₁ + K₂ + Real.log 3 + 1 := by
    have h : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
    linarith
  refine ⟨max (5 * c) C₂ + Real.log (4 * (d : ℝ)) + ((k : ℝ) / 2) * Real.log Real.pi + 1,
    K₁ + K₂ + Real.log 3 + 1, hCbig, hKbig, ?_⟩
  intro R hR1 z hz
  have hR0 : (0 : ℝ) ≤ R := by linarith
  have hzre : z.re ≤ R := by
    have h := Complex.abs_re_le_norm z
    rw [hz] at h
    linarith [(abs_le.mp h).2]
  have hnzre : -(R : ℝ) ≤ z.re := by
    have h := Complex.abs_re_le_norm z
    rw [hz] at h
    linarith [(abs_le.mp h).1]
  by_cases hre : (1 / 2 : ℝ) ≤ z.re
  · have h1 := hHalf z hre
    rw [hz] at h1
    have h2 := rightCombine (R := R) (c := c) (C₂ := C₂) (K₁ := K₁) (K₂ := K₂)
      (L := Real.log (4 * (d : ℝ))) (M := ((k : ℝ) / 2) * Real.log Real.pi)
      hR1 hc0.le hC₂.le hK₁ hK₂ hlog4d hM0
    linarith [h1, h2]
  · push_neg at hre
    rw [hEq]
    set t : ℂ := (k : ℂ) / 2 + 1 - z with ht_def
    have hk2 : ((k : ℂ) / 2) = (((k : ℝ) / 2 : ℝ) : ℂ) := by push_cast; ring
    have ht_re : t.re = (k : ℝ) / 2 + 1 - z.re := by
      rw [ht_def]
      simp only [Complex.sub_re, Complex.add_re, Complex.one_re, hk2, Complex.ofReal_re]
    have ht_lo : (k : ℝ) / 2 + 1 / 2 ≤ t.re := by rw [ht_re]; linarith
    have ht_hi : t.re ≤ (k : ℝ) / 2 + R + 1 := by rw [ht_re]; linarith
    have hPΛ : P.Λ (z + (k : ℂ) / 2) = P.symm.Λ t := by
      have h := P.functional_equation t
      have hk : (P.k : ℂ) = (k : ℂ) + 1 := by
        show ((((k + 1 : ℕ) : ℝ)) : ℂ) = (k : ℂ) + 1
        push_cast; ring
      rw [show P.ε = (1 : ℂ) from rfl, hk] at h
      have harg : ((k : ℂ) + 1) - t = z + (k : ℂ) / 2 := by rw [ht_def]; ring
      rw [harg] at h
      simpa using h
    have hΛcz : Λc z = (((4 * d : ℕ) : ℂ)) ^ z * ((Real.pi : ℂ) ^ ((k : ℂ) / 2)) *
        mellin (thetaDualMG d (twist chi k) k) t := by
      simp only [hΛcdef]
      rw [hPΛ, hsymmΛ]
    have hpi : ‖((Real.pi : ℂ) ^ ((k : ℂ) / 2))‖ = Real.pi ^ ((k : ℝ) / 2) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos, hk2, Complex.ofReal_re]
    have hnormz : ‖Λc z‖ = (4 * (d : ℝ)) ^ (z.re) * Real.pi ^ ((k : ℝ) / 2) *
        ‖mellin (thetaDualMG d (twist chi k) k) t‖ := by
      rw [hΛcz, norm_mul, norm_mul]
      rw [show (((4 * d : ℕ) : ℂ)) = (((4 * (d : ℝ)) : ℝ) : ℂ) by push_cast; ring]
      rw [Complex.norm_cpow_eq_rpow_re_of_pos h4dpos, hpi]
    have hD := hDbound R hR1 t ht_lo ht_hi
    have hbr : 0 ≤ Real.log (R + 2) + (K₁ + K₂ + Real.log 3 + 1) := by
      have h : 0 ≤ Real.log (R + 2) := Real.log_nonneg (by linarith)
      linarith
    by_cases hX : ‖mellin (thetaDualMG d (twist chi k) k) t‖ = 0
    · rw [hnormz, hX, mul_zero, Real.log_zero]
      exact mul_nonneg (mul_nonneg hCbig.le hR0) hbr
    · have hXpos : 0 < ‖mellin (thetaDualMG d (twist chi k) k) t‖ :=
        lt_of_le_of_ne (norm_nonneg _) (Ne.symm hX)
      have hlogz : Real.log ‖Λc z‖ = z.re * Real.log (4 * (d : ℝ))
          + ((k : ℝ) / 2) * Real.log Real.pi
          + Real.log ‖mellin (thetaDualMG d (twist chi k) k) t‖ := by
        rw [hnormz]
        rw [Real.log_mul (mul_ne_zero
              (ne_of_gt (Real.rpow_pos_of_pos h4dpos _))
              (ne_of_gt (Real.rpow_pos_of_pos Real.pi_pos _))) (ne_of_gt hXpos),
          Real.log_mul (ne_of_gt (Real.rpow_pos_of_pos h4dpos _))
            (ne_of_gt (Real.rpow_pos_of_pos Real.pi_pos _)),
          Real.log_rpow h4dpos, Real.log_rpow Real.pi_pos]
      have hcomb := leftCombine (R := R) (c := c) (C₂ := C₂) (K₁ := K₁) (K₂ := K₂)
        (L := Real.log (4 * (d : ℝ))) (M := ((k : ℝ) / 2) * Real.log Real.pi) (zr := z.re)
        hR1 hc0.le hC₂.le hK₁ hK₂ hlog4d hM0 hzre
      linarith [hlogz, hD, hcomb]

/-! ## The circle growth of an admissible completion -/

/-- **The circle growth of an admissible completion** (replacement for the stalled stub `Work.FIArea6Hecke.R.lamGrowthStrict`; the statement is identical, but the missing strip-bound input is now a proved theorem, so the proof is within reach).

For every strict character `χ` mod `4d`, every `m : ℤ` and every entire completion `Λ` of `Λ(s,ψ) = heckeArch d m s · L(s,ψ_χ)` (`Work.FIArea6Hecke.R.IsCompleted`),

`log ‖Λ z‖ ≤ C·R·(log (R+2) + K)`  for `‖z‖ = R ≥ 1`,

with constants depending only on the datum.  This is the input of the Hadamard partial fraction `Work.FIArea6Hecke.R.lamPartialFraction`.

The completion is the Mellin transform of the weight-`m` theta series; its weak functional equation reflects the left half-plane `re ≤ 1/2` onto the right half-plane `re ≥ 1/2` (where `Work.FIArea6Hecke.R.lamRightHalf_strict` applies), the reflected factor being the Mellin transform of the dual theta kernel, which is exponentially small on that region. -/
theorem lamGrowth (d : ℕ) (chi : GaussianInt → ℂ) (m : ℤ) (Lam : ℂ → ℂ)
    (hadm : IsCompleted d chi m Lam) :
    ∃ C K : ℝ, 0 < C ∧ 0 ≤ K ∧ ∀ R : ℝ, 1 ≤ R → ∀ z : ℂ, ‖z‖ = R →
      Real.log ‖Lam z‖ ≤ C * R * (Real.log (R + 2) + K) := by
  obtain ⟨hd, hchi, hAn, hagr⟩ := hadm
  have hnt : ∃ z : GaussianInt, Work.FIPlan.IsPrimary z ∧
      IsUnitMod4d d z ∧ psi chi m z ≠ 1 := by
    by_contra h
    push_neg at h
    exact (noCompletion_of_primaryTrivial d chi m hd hchi h) ⟨Lam, hAn, hagr⟩
  by_cases hm : 0 ≤ m
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, m = (k : ℤ) := ⟨m.toNat, (Int.toNat_of_nonneg hm).symm⟩
    have habsk : |(((k : ℤ)) : ℝ)| = (k : ℝ) := by
      rw [Int.cast_natCast]; exact abs_of_nonneg (by positivity)
    exact growth_nat d hd chi k hchi hnt Lam hAn
      (fun s hs => hagr s (by rw [habsk]; exact hs))
  · push_neg at hm
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, m = -((k : ℤ)) := ⟨m.natAbs, by omega⟩
    have hchi_c : IsCharMod4dStrict d (fun z : GaussianInt => star (chi z)) :=
      isCharMod4dStrict_conj hchi
    have hne_c : ∃ z : GaussianInt, Work.FIPlan.IsPrimary z ∧ IsUnitMod4d d z ∧
        psi (fun z : GaussianInt => star (chi z)) (k : ℤ) z ≠ 1 := by
      obtain ⟨z, hz1, hz2, hz3⟩ := hnt
      refine ⟨z, hz1, hz2, ?_⟩
      intro hc
      apply hz3
      have h3 : star (psi chi (-(k : ℤ)) z) = (1 : ℂ) := by
        rw [psi_conj_neg chi k z]; exact hc
      have h4 := congrArg star h3
      simpa using h4
    have hAn_c : AnalyticOn ℂ (fun s : ℂ => star (Lam (star s))) Set.univ := by
      refine DifferentiableOn.analyticOn ?_ isOpen_univ
      intro z _
      have h1 : DifferentiableAt ℂ Lam (star z) :=
        (hAn.analyticAt Filter.univ_mem).differentiableAt
      have h3 := DifferentiableAt.conj_conj (f := Lam) (x := star z) h1
      have h3' : DifferentiableAt ℂ (fun s : ℂ => star (Lam (star s))) (star (star z)) := h3
      rw [star_star] at h3'
      exact h3'.differentiableWithinAt
    have hagr_c : ∀ s : ℂ, 1 + (k : ℝ) / 2 < s.re →
        star (Lam (star s)) = Work.FITop4.Bridge.heckeArch d (k : ℤ) s *
          heckeLSeries (fun z : GaussianInt => star (chi z)) (k : ℤ) s := by
      intro s hs
      have hs' : 1 + |((-(k : ℕ) : ℤ) : ℝ)| / 2 < (star s).re := by
        rw [Complex.star_def, Complex.conj_re]
        have habs : |((-(k : ℕ) : ℤ) : ℝ)| = (k : ℝ) := by
          rw [show ((-(k : ℕ) : ℤ) : ℝ) = -((k : ℤ) : ℝ) by push_cast; ring, abs_neg,
            abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((k : ℤ) : ℝ)), Int.cast_natCast]
        rw [habs]
        exact hs
      have hAconj : star (Work.FITop4.Bridge.heckeArch d (-(k : ℤ)) (star s))
          = Work.FITop4.Bridge.heckeArch d (k : ℤ) s := by
        have h := star_heckeArch d (-(k : ℤ)) s hd
        simpa using h
      rw [hagr (star s) hs', star_mul, hAconj, heckeLSeries_conj_neg chi k s]
      ring
    obtain ⟨C, K, hC, hK, hbound⟩ :=
      growth_nat d hd (fun z : GaussianInt => star (chi z)) k hchi_c hne_c
        (fun s : ℂ => star (Lam (star s))) hAn_c hagr_c
    refine ⟨C, K, hC, hK, fun R hR z hz => ?_⟩
    have h := hbound R hR (star z) (by rw [norm_star, hz])
    simpa using h


end

end Work.FIArea6Hecke.R
