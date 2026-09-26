import Mathlib
import Submission.Work.Asymptotics.HalfFunnel.lowBadDefs
import Submission.Work.HFN.HalfFunnel.lowBadAux
import Submission.Work.HFN.HalfFunnel.lowBad_Aexp_tail
import Submission.Work.Asymptotics.HalfFunnel.lowBad_PhiSpike_deriv
import Submission.Work.HFN.HalfFunnel.lowBad_kernel_spike_b
import Submission.Work.HFN.HalfFunnel.lowF2_eq_paperLayer
import Submission.Work.HFN.HalfFunnel.lowBad_Phi12_deriv
import Submission.Work.Asymptotics.HalfFunnel.spike_model_integral
import Submission.Work.Asymptotics.HalfFunnel.Kaxis_cusp_of_bounded
import Submission.Work.Asymptotics.DomainD
import Submission.Work.Asymptotics.exists_seminorm_bound_of_iteratedDeriv_bound
import Submission.Work.Asymptotics.Compact.local_agreement
import Submission.Work.HFN.Kaxis_local_tail
import Submission.Work.Asymptotics.kernelTransform_seminorm_of_layer
import Submission.Work.Asymptotics.highPart_seminorm_scaled
import Submission.Work.Asymptotics.paperLayer_smooth
import Submission.Work.Asymptotics.punctured_iteratedDeriv
import Submission.Work.HFN.kernelTransform_seminorm_on_compact

noncomputable section

open MeasureTheory Filter Topology UpperHalfPlane
open scoped Topology ContDiff

namespace Work.HFN.HalfFunnel
open Work.Asymptotics Work.Asymptotics.HalfFunnel  -- ck-hfn-fix: fork moved out of Work.Asymptotics

open Work.Kernels

/-! ## An elementary weighted bound

`r ↦ |r|^k (2|r|+2)^l (1+r^2)^{-N}` is bounded when `k + l ≤ 2N`. -/

lemma exists_bound_abs_pow_mul_pow_inv (k l N : ℕ) (hN : k + l ≤ 2 * N) :
    ∃ W : ℝ, 0 ≤ W ∧ ∀ r : ℝ,
      |r| ^ k * (2 * |r| + 2) ^ l * (1 + r ^ 2) ^ (-(N : ℝ)) ≤ W := by
  refine ⟨4 ^ l, by positivity, fun r => ?_⟩
  have h2 : (0:ℝ) < 1 + r ^ 2 := by positivity
  have hkey : (1 + r ^ 2) ^ (-(N:ℝ)) = ((1 + r^2)^N)⁻¹ := by
    rw [Real.rpow_neg h2.le, Real.rpow_natCast]
  rw [hkey]
  have hposN : (0:ℝ) < (1 + r^2)^N := by positivity
  rcases le_or_gt 1 |r| with hr | hr
  · have h2r : (2 * |r| + 2) ^ l ≤ (4 * |r|) ^ l := by
      apply pow_le_pow_left₀ (by positivity)
      linarith
    have hrN : |r| ^ (2*N) ≤ (1 + r^2)^N := by
      have h3 : |r|^2 ≤ 1 + r^2 := by
        rw [sq_abs]; linarith [sq_nonneg r]
      calc |r| ^ (2*N) = (|r|^2)^N := by rw [pow_mul]
        _ ≤ (1 + r^2)^N := pow_le_pow_left₀ (by positivity) h3 N
    have hinv : ((1 + r^2)^N)⁻¹ ≤ (|r| ^ (2*N))⁻¹ := inv_anti₀ (by positivity) hrN
    have h4 : (|r| ^ (2*N))⁻¹ * |r| ^ (k+l) ≤ 1 := by
      rw [inv_mul_eq_div, div_le_one (by positivity)]
      exact pow_le_pow_right₀ (by linarith) (by omega)
    calc |r| ^ k * (2 * |r| + 2) ^ l * ((1 + r ^ 2) ^ N)⁻¹
        ≤ |r|^k * (4*|r|)^l * ((1 + r^2)^N)⁻¹ := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left h2r (by positivity)
      _ = 4^l * (|r| ^ (k+l)) * ((1 + r^2)^N)⁻¹ := by
          rw [mul_pow, show |r|^k * (4^l * |r|^l) = 4^l * (|r|^k * |r|^l) by ring, ← pow_add]
      _ ≤ 4^l * (|r| ^ (k+l)) * (|r| ^ (2*N))⁻¹ :=
          mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = 4^l * ((|r| ^ (2*N))⁻¹ * |r| ^ (k+l)) := by ring
      _ ≤ 4^l * 1 := mul_le_mul_of_nonneg_left h4 (by positivity)
      _ = 4^l := by ring
  · have hr1 : |r| ≤ 1 := le_of_lt hr
    have hrk : |r|^k ≤ 1 := pow_le_one₀ (abs_nonneg r) hr1
    have h2r : (2*|r|+2)^l ≤ 4^l := by
      apply pow_le_pow_left₀ (by positivity)
      linarith
    have h1l : |r|^k * (2*|r|+2)^l ≤ 4^l := by
      calc |r|^k * (2*|r|+2)^l ≤ 1 * 4^l :=
            mul_le_mul hrk h2r (by positivity) (by norm_num)
        _ = 4^l := by ring
    have hN1 : ((1 + r^2)^N)⁻¹ ≤ 1 := by
      rw [inv_le_one₀ (by positivity)]
      exact one_le_pow₀ (by nlinarith [sq_nonneg r])
    calc |r|^k * (2*|r|+2)^l * ((1 + r^2)^N)⁻¹ ≤ 4^l * 1 :=
          mul_le_mul h1l hN1 (by positivity) (by positivity)
      _ = 4^l := by ring

/-! ## The polynomial version of the composition estimate -/

/-- **Composition estimate with polynomial decay.**  If `F` is `l` times differentiable on
`(-1,∞)` and its iterated derivatives satisfy `‖∂^m F x‖ ≤ K (1+x)^{-N}` for `x ≥ 0` (with
`k + l ≤ 2N`), then `|r|^k ∂_r^l ((2 - 2cos(πr²))·F(r²))` is bounded by a constant depending only
on `k` and `l`, times `K`. -/
theorem exists_seminorm_bound_of_iteratedDeriv_bound_poly (k l N : ℕ) (hN : k + l ≤ 2 * N) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (F : ℝ → ℂ) (K : ℝ), 0 ≤ K →
      ContDiffOn ℝ (l : WithTop ℕ∞) F (Set.Ioi (-1)) →
      (∀ m : ℕ, m ≤ l → ∀ x : ℝ, 0 ≤ x →
        ‖iteratedDeriv m F x‖ ≤ K * (1 + x) ^ (-(N : ℝ))) →
      ∀ r : ℝ, (|r| ^ k) * ‖iteratedDeriv l
        (fun s : ℝ => (2 - 2 * Real.cos (Real.pi * s ^ 2) : ℂ) * F (s ^ 2)) r‖ ≤ c * K := by
  obtain ⟨W, hW0, hW⟩ := exists_bound_abs_pow_mul_pow_inv k l N hN
  refine ⟨(l.factorial : ℝ) * (4 * (2 * Real.pi) ^ l) * W, by positivity, ?_⟩
  intro F K hK hFdiff hFbound r
  have hcont_cos : ContDiffOn ℝ (l : ℕ∞ω)
      (fun x : ℝ => (2 - 2 * Real.cos (Real.pi * x) : ℂ)) (Set.Ioi (-1)) := by
    have h1 : ContDiff ℝ (l : ℕ∞ω) (fun x : ℝ => (2 - 2 * Real.cos (Real.pi * x))) := by
      fun_prop
    have h2 := Complex.ofRealCLM.contDiff.comp h1
    refine h2.contDiffOn.congr (fun x _ => ?_)
    show (2 - 2 * (Real.cos (Real.pi * x) : ℂ)) = ((2 - 2 * Real.cos (Real.pi * x) : ℝ) : ℂ)
    push_cast
    ring
  have hfcont : ContDiffOn ℝ (l : ℕ∞ω) (fun r : ℝ => r ^ 2) Set.univ :=
    ((contDiff_id (𝕜 := ℝ)).pow 2).contDiffOn
  have hbnd : ∀ i ≤ l, ∀ x : ℝ, 0 ≤ x →
      ‖iteratedDeriv i (fun y : ℝ => (2 - 2 * Real.cos (Real.pi * y) : ℂ) * F y) x‖
        ≤ K * (1 + x) ^ (-(N : ℝ)) * (4 * (2 * Real.pi) ^ l) := by
    intro i hi x hx
    have hxmem : x ∈ Set.Ioi (-1) := by rw [Set.mem_Ioi]; linarith
    have hmul := norm_iteratedFDerivWithin_mul_le (𝕜 := ℝ) (s := Set.Ioi (-1))
      (f := fun y : ℝ => (2 - 2 * Real.cos (Real.pi * y) : ℂ)) (g := F) (N := (l : ℕ∞ω))
      hcont_cos hFdiff (uniqueDiffOn_Ioi (-1)) hxmem
      (show (i : ℕ∞ω) ≤ (l : ℕ∞ω) from by exact_mod_cast hi)
    have hL : ‖iteratedFDerivWithin ℝ i
          (fun y : ℝ => (2 - 2 * Real.cos (Real.pi * y) : ℂ) * F y) (Set.Ioi (-1)) x‖
        = ‖iteratedDeriv i (fun y : ℝ => (2 - 2 * Real.cos (Real.pi * y) : ℂ) * F y) x‖ :=
      norm_iteratedFDerivWithin_eq_of_isOpen isOpen_Ioi hxmem i _
    rw [hL] at hmul
    have hstep : ∀ j ∈ Finset.range (i + 1),
        (i.choose j : ℝ) *
          ‖iteratedFDerivWithin ℝ j (fun y : ℝ => (2 - 2 * Real.cos (Real.pi * y) : ℂ))
            (Set.Ioi (-1)) x‖ *
          ‖iteratedFDerivWithin ℝ (i - j) F (Set.Ioi (-1)) x‖
        ≤ (i.choose j : ℝ) * (4 * Real.pi ^ j) * (K * (1 + x) ^ (-(N : ℝ))) := by
      intro j hj
      have hc : ‖iteratedFDerivWithin ℝ j
            (fun y : ℝ => (2 - 2 * Real.cos (Real.pi * y) : ℂ)) (Set.Ioi (-1)) x‖
          ≤ 4 * Real.pi ^ j := by
        rw [norm_iteratedFDerivWithin_eq_of_isOpen isOpen_Ioi hxmem j]
        exact norm_iteratedDeriv_two_sub_two_cos j x
      have ht : ‖iteratedFDerivWithin ℝ (i - j) F (Set.Ioi (-1)) x‖
          ≤ K * (1 + x) ^ (-(N : ℝ)) := by
        rw [norm_iteratedFDerivWithin_eq_of_isOpen isOpen_Ioi hxmem (i - j)]
        exact hFbound (i - j) (le_trans (Nat.sub_le i j) hi) x hx
      exact mul_le_mul (mul_le_mul_of_nonneg_left hc (by positivity)) ht
        (by positivity) (by positivity)
    have hsum2 : (∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * (4 * Real.pi ^ j))
        ≤ 4 * (2 * Real.pi) ^ l := by
      have hbin : (∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ)) = 2 ^ i := by
        have hh := add_pow (1 : ℝ) 1 i
        rw [one_add_one_eq_two] at hh
        rw [hh]
        apply Finset.sum_congr rfl
        intro j hj
        rw [one_pow, one_pow]
        ring
      calc (∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * (4 * Real.pi ^ j))
          ≤ ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * (4 * Real.pi ^ l) := by
            refine Finset.sum_le_sum (fun j hj => ?_)
            have hjle : j ≤ l := le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) hi
            have hpi : Real.pi ^ j ≤ Real.pi ^ l :=
              pow_le_pow_right₀ (by linarith [Real.pi_gt_three] : (1 : ℝ) ≤ Real.pi) hjle
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpi (by norm_num))
              (by positivity)
        _ = (∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ)) * (4 * Real.pi ^ l) := by
            rw [Finset.sum_mul]
        _ = 2 ^ i * (4 * Real.pi ^ l) := by rw [hbin]
        _ ≤ 4 * (2 * Real.pi) ^ l := by
            have h2 : (2 : ℝ) ^ i ≤ 2 ^ l := pow_le_pow_right₀ (by norm_num) hi
            have h3 : (2 : ℝ) ^ i * (4 * Real.pi ^ l) ≤ 2 ^ l * (4 * Real.pi ^ l) :=
              mul_le_mul_of_nonneg_right h2 (by positivity)
            refine h3.trans_eq ?_
            rw [mul_pow]
            ring
    calc ‖iteratedDeriv i (fun y : ℝ => (2 - 2 * Real.cos (Real.pi * y) : ℂ) * F y) x‖
        ≤ ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) *
            ‖iteratedFDerivWithin ℝ j (fun y : ℝ => (2 - 2 * Real.cos (Real.pi * y) : ℂ))
              (Set.Ioi (-1)) x‖ *
            ‖iteratedFDerivWithin ℝ (i - j) F (Set.Ioi (-1)) x‖ := hmul
      _ ≤ ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * (4 * Real.pi ^ j) *
            (K * (1 + x) ^ (-(N : ℝ))) := Finset.sum_le_sum hstep
      _ = (K * (1 + x) ^ (-(N : ℝ))) *
            (∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * (4 * Real.pi ^ j)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j hj
            ring
      _ ≤ (K * (1 + x) ^ (-(N : ℝ))) * (4 * (2 * Real.pi) ^ l) :=
            mul_le_mul_of_nonneg_left hsum2 (by positivity)
      _ = K * (1 + x) ^ (-(N : ℝ)) * (4 * (2 * Real.pi) ^ l) := by ring
  have hCbound : ∀ i, i ≤ l → ‖iteratedFDerivWithin ℝ i
        (fun y : ℝ => (2 - 2 * Real.cos (Real.pi * y) : ℂ) * F y)
        (Set.Ioi (-1)) (r ^ 2)‖ ≤ K * (1 + r ^ 2) ^ (-(N : ℝ)) * (4 * (2 * Real.pi) ^ l) := by
    intro i hi
    have hr2 : r ^ 2 ∈ Set.Ioi (-1) := by rw [Set.mem_Ioi]; nlinarith [sq_nonneg r]
    rw [norm_iteratedFDerivWithin_eq_of_isOpen isOpen_Ioi hr2]
    exact hbnd i hi (r ^ 2) (sq_nonneg r)
  have hDbound : ∀ i, 1 ≤ i → i ≤ l →
      ‖iteratedFDerivWithin ℝ i (fun r : ℝ => r ^ 2) Set.univ r‖ ≤ (2 * |r| + 2) ^ i := by
    intro i hi _
    rw [iteratedFDerivWithin_univ, norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    exact norm_iteratedDeriv_sq_le hi r
  have hcomp := norm_iteratedFDerivWithin_comp_le (𝕜 := ℝ)
    (g := fun y : ℝ => (2 - 2 * Real.cos (Real.pi * y) : ℂ) * F y)
    (f := fun r : ℝ => r ^ 2) (n := l) (s := Set.univ) (t := Set.Ioi (-1))
    (x := r) (N := (l : ℕ∞ω)) (hcont_cos.mul hFdiff) hfcont le_rfl
    (uniqueDiffOn_Ioi (-1)) uniqueDiffOn_univ
    (by intro x _; rw [Set.mem_Ioi]; nlinarith [sq_nonneg x]) (Set.mem_univ r) hCbound hDbound
  have hcomp' : ‖iteratedDeriv l
        (fun s : ℝ => (2 - 2 * Real.cos (Real.pi * s ^ 2) : ℂ) * F (s ^ 2)) r‖
      ≤ (l.factorial : ℝ) * (K * (1 + r ^ 2) ^ (-(N : ℝ)) * (4 * (2 * Real.pi) ^ l))
        * (2 * |r| + 2) ^ l := by
    have heq : (fun s : ℝ => (2 - 2 * Real.cos (Real.pi * s ^ 2) : ℂ) * F (s ^ 2))
        = (fun y : ℝ => (2 - 2 * Real.cos (Real.pi * y) : ℂ) * F y)
          ∘ (fun r : ℝ => r ^ 2) := rfl
    rw [heq, ← norm_iteratedFDeriv_eq_norm_iteratedDeriv, ← iteratedFDerivWithin_univ]
    exact hcomp
  calc (|r| ^ k) * ‖iteratedDeriv l
        (fun s : ℝ => (2 - 2 * Real.cos (Real.pi * s ^ 2) : ℂ) * F (s ^ 2)) r‖
      ≤ |r| ^ k * ((l.factorial : ℝ) * (K * (1 + r ^ 2) ^ (-(N : ℝ))
          * (4 * (2 * Real.pi) ^ l)) * (2 * |r| + 2) ^ l) :=
        mul_le_mul_of_nonneg_left hcomp' (by positivity)
    _ = (l.factorial : ℝ) * (4 * (2 * Real.pi) ^ l) * K
          * (|r| ^ k * (2 * |r| + 2) ^ l * (1 + r ^ 2) ^ (-(N : ℝ))) := by ring
    _ ≤ (l.factorial : ℝ) * (4 * (2 * Real.pi) ^ l) * K * W := by
        have h1 : (0 : ℝ) ≤ (l.factorial : ℝ) * (4 * (2 * Real.pi) ^ l) * K := by positivity
        exact mul_le_mul_of_nonneg_left (hW r) h1
    _ = ((l.factorial : ℝ) * (4 * (2 * Real.pi) ^ l) * W) * K := by ring

open Work.Asymptotics

theorem contDiffOn_intervalIntegral_exp_ofReal
    {κ : ℝ → ℂ} {B : ℝ} (hB : 0 ≤ B)
    (hmeas : AEStronglyMeasurable κ (volume.restrict (Set.Ioc 0 1)))
    (hbound : ∀ᵐ t ∂(volume.restrict (Set.Ioc 0 1)), ‖κ t‖ ≤ B) :
    ContDiffOn ℝ ω (fun x : ℝ => ∫ t in (0:ℝ)..1, κ t * Complex.exp (-(Real.pi * (x : ℂ) * (t : ℂ)))) (Set.Ioi (-1)) := by
  have hconv : ∀ f : ℝ → ℂ, (∫ t in (0:ℝ)..1, f t) = ∫ t, f t ∂(volume.restrict (Set.Ioc (0:ℝ) 1)) := by
    intro f; rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  have hcont_exp : ∀ w : ℂ, AEStronglyMeasurable (fun t : ℝ => Complex.exp (-(Real.pi * w * (t:ℂ)))) (volume.restrict (Set.Ioc 0 1)) := by
    intro w
    exact (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal).neg).aestronglyMeasurable
  have hcont_lin : Continuous (fun t : ℝ => -(Real.pi * (t:ℂ))) :=
    (continuous_const.mul Complex.continuous_ofReal).neg
  have hnormpi : ‖(Real.pi : ℂ)‖ = Real.pi := by
    rw [show ‖(Real.pi:ℂ)‖ = |Real.pi| from by
      rw [Complex.norm_def, Complex.normSq_ofReal]; simpa [sq] using Real.sqrt_sq_eq_abs Real.pi]
    exact abs_of_pos Real.pi_pos
  have hdiff : Differentiable ℂ (fun z : ℂ => ∫ t in (0:ℝ)..1, κ t * Complex.exp (-(Real.pi * z * (t:ℂ)))) := by
    intro z
    have h_int : Integrable (fun t : ℝ => κ t * Complex.exp (-(Real.pi * z * (t:ℂ)))) (volume.restrict (Set.Ioc 0 1)) := by
      refine Integrable.mono' (integrable_const (B * Real.exp (Real.pi * |z.re|))) ?_ ?_
      · exact hmeas.mul (hcont_exp z)
      · filter_upwards [hbound, MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t hbnd ht
        rw [norm_mul, Complex.norm_exp]
        have hexp : (-(Real.pi * z * (t:ℂ))).re = -(Real.pi * z.re * t) := by
          simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
        rw [hexp]
        have h3 : - (z.re * t) ≤ |z.re| := by
          calc - (z.re * t) ≤ |z.re * t| := neg_le_abs _
            _ = |z.re| * |t| := abs_mul _ _
            _ ≤ |z.re| * 1 := mul_le_mul_of_nonneg_left (by rw [abs_of_pos ht.1]; exact ht.2) (abs_nonneg _)
            _ = |z.re| := mul_one _
        have h1 : -(Real.pi * z.re * t) ≤ Real.pi * |z.re| := by
          have : -(Real.pi * z.re * t) = Real.pi * (-(z.re * t)) := by ring
          rw [this]
          exact mul_le_mul_of_nonneg_left h3 (le_of_lt Real.pi_pos)
        exact mul_le_mul hbnd (Real.exp_le_exp.mpr h1) (Real.exp_nonneg _) hB
    have h_bound : ∀ᵐ t ∂(volume.restrict (Set.Ioc 0 1)), ∀ w ∈ Metric.ball z 1,
        ‖κ t * (-(Real.pi * (t:ℂ))) * Complex.exp (-(Real.pi * w * (t:ℂ)))‖
          ≤ B * Real.pi * Real.exp (Real.pi * (|z.re| + 1)) := by
      filter_upwards [hbound, MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t hbnd ht
      intro w hw
      rw [Metric.mem_ball, Complex.dist_eq] at hw
      have hre2 : |w.re| ≤ |z.re| + 1 := by
        have h1 := abs_sub_abs_le_abs_sub w.re z.re
        have h2 := Complex.abs_re_le_norm (w - z)
        rw [Complex.sub_re] at h2
        linarith
      rw [norm_mul, norm_mul, Complex.norm_exp, norm_neg]
      have hexp : (-(Real.pi * w * (t:ℂ))).re = -(Real.pi * w.re * t) := by
        simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
      rw [hexp]
      have htle : t ≤ 1 := ht.2
      have htpos : 0 < t := ht.1
      have hnpi : ‖(Real.pi : ℂ) * (t:ℂ)‖ = Real.pi * t := by
        rw [Complex.norm_mul, hnormpi]
        congr 1
        rw [show ‖(t:ℂ)‖ = |t| from by
          rw [Complex.norm_def, Complex.normSq_ofReal]; simpa [sq] using Real.sqrt_sq_eq_abs t]
        exact abs_of_pos htpos
      rw [hnpi]
      have hexple : Real.exp (-(Real.pi * w.re * t)) ≤ Real.exp (Real.pi * (|z.re| + 1)) := by
        apply Real.exp_le_exp.mpr
        have h4 : -(w.re * t) ≤ |w.re| * t := by
          calc -(w.re * t) ≤ |w.re * t| := neg_le_abs _
            _ = |w.re| * |t| := abs_mul _ _
            _ = |w.re| * t := by rw [abs_of_pos htpos]
        have h5 : |w.re| * t ≤ |w.re| * 1 := mul_le_mul_of_nonneg_left htle (abs_nonneg _)
        nlinarith [Real.pi_pos, hre2]
      calc ‖κ t‖ * (Real.pi * t) * Real.exp (-(Real.pi * w.re * t))
          ≤ B * (Real.pi * t) * Real.exp (Real.pi * (|z.re| + 1)) := by
            apply mul_le_mul
            · exact mul_le_mul hbnd (le_refl _) (by positivity) hB
            · exact hexple
            · positivity
            · positivity
          _ ≤ B * Real.pi * Real.exp (Real.pi * (|z.re| + 1)) := by
            apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
            have hpi : Real.pi * t ≤ Real.pi := by
              simpa using mul_le_mul_of_nonneg_left htle (le_of_lt Real.pi_pos)
            exact mul_le_mul_of_nonneg_left hpi hB
    have h_diff : ∀ᵐ t ∂(volume.restrict (Set.Ioc 0 1)), ∀ w ∈ Metric.ball z 1,
        HasDerivAt (fun w : ℂ => κ t * Complex.exp (-(Real.pi * w * (t:ℂ))))
          (κ t * (-(Real.pi * (t:ℂ))) * Complex.exp (-(Real.pi * w * (t:ℂ)))) w := by
      filter_upwards with t
      intro w _
      have hlin : HasDerivAt (fun w : ℂ => Real.pi * w * (t:ℂ)) (Real.pi * (t:ℂ)) w := by
        have h := (hasDerivAt_id w).const_mul (Real.pi : ℂ)
        simpa using h.mul_const (t:ℂ)
      have hneg : HasDerivAt (fun w : ℂ => -(Real.pi * w * (t:ℂ))) (-(Real.pi * (t:ℂ))) w := hlin.neg
      have hexp2 : HasDerivAt (fun w : ℂ => Complex.exp (-(Real.pi * w * (t:ℂ))))
          (Complex.exp (-(Real.pi * w * (t:ℂ))) * (-(Real.pi * (t:ℂ)))) w :=
        (Complex.hasDerivAt_exp (-(Real.pi * w * (t:ℂ)))).comp w hneg
      have h3 : HasDerivAt (fun w : ℂ => κ t * Complex.exp (-(Real.pi * w * (t:ℂ))))
          (κ t * (Complex.exp (-(Real.pi * w * (t:ℂ))) * (-(Real.pi * (t:ℂ))))) w :=
        hexp2.const_mul (κ t)
      have heq : κ t * (Complex.exp (-(Real.pi * w * (t:ℂ))) * (-(Real.pi * (t:ℂ))))
          = κ t * (-(Real.pi * (t:ℂ))) * Complex.exp (-(Real.pi * w * (t:ℂ))) := by ring
      rw [heq] at h3
      exact h3
    have hF'_meas : AEStronglyMeasurable (fun t : ℝ => κ t * (-(Real.pi * (t:ℂ))) * Complex.exp (-(Real.pi * z * (t:ℂ)))) (volume.restrict (Set.Ioc 0 1)) := by
      apply AEStronglyMeasurable.mul ?_ (hcont_exp z)
      exact AEStronglyMeasurable.mul hmeas hcont_lin.aestronglyMeasurable
    obtain ⟨-, hderiv⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume.restrict (Set.Ioc (0:ℝ) 1))
      (F := fun z t => κ t * Complex.exp (-(Real.pi * z * (t:ℂ))))
      (F' := fun z t => κ t * (-(Real.pi * (t:ℂ))) * Complex.exp (-(Real.pi * z * (t:ℂ))))
      (bound := fun _ => B * Real.pi * Real.exp (Real.pi * (|z.re| + 1)))
      (x₀ := z) (s := Metric.ball z 1)
      (Metric.ball_mem_nhds z one_pos)
      (Filter.Eventually.of_forall (fun w => hmeas.mul (hcont_exp w)))
      h_int hF'_meas h_bound (integrable_const _) h_diff
    have hfun : (fun n : ℂ => ∫ a, κ a * Complex.exp (-(Real.pi * n * (a:ℂ))) ∂(volume.restrict (Set.Ioc (0:ℝ) 1)))
        = fun n : ℂ => ∫ t in (0:ℝ)..1, κ t * Complex.exp (-(Real.pi * n * (t:ℂ))) := by
      funext n; exact (hconv _).symm
    rw [hfun] at hderiv
    exact hderiv.differentiableAt
  have hcdR : ContDiff ℝ ω (fun z : ℂ => ∫ t in (0:ℝ)..1, κ t * Complex.exp (-(Real.pi * z * (t:ℂ)))) :=
    ((hdiff.differentiableOn.analyticOnNhd isOpen_univ).contDiff).restrict_scalars ℝ
  exact (hcdR.comp_contDiffOn Complex.ofRealCLM.contDiff.contDiffOn).mono (Set.subset_univ _)

theorem contDiffOn_integral_Ici_exp_ofReal
    {ψ : ℝ → ℂ} {C M : ℝ} (hC : 0 < C) (hM : 0 ≤ M)
    (hmeas : AEStronglyMeasurable ψ (volume.restrict (Set.Ici 1)))
    (hbound : ∀ᵐ t ∂(volume.restrict (Set.Ici 1)), ‖ψ t‖ ≤ C * t^M * Real.exp (-(Real.pi * t))) :
    ContDiffOn ℝ ω (fun x : ℝ => ∫ t in Set.Ici 1, ψ t * Complex.exp (-(Real.pi * (x:ℂ) * (t:ℂ)))) (Set.Ioi (-1)) := by
  set U : Set ℂ := {z | -1 < z.re} with hUdef
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hcont : ∀ z : ℂ, AEStronglyMeasurable (fun t : ℝ => Complex.exp (-(Real.pi * z * (t:ℂ)))) (volume.restrict (Set.Ici 1)) :=
    fun z => (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal).neg).aestronglyMeasurable
  have hcont_lin : Continuous (fun t : ℝ => -(Real.pi * (t:ℂ))) :=
    (continuous_const.mul Complex.continuous_ofReal).neg
  have hint_base : ∀ η : ℝ, 0 < η → Integrable (fun t : ℝ => C * (t^M * Real.exp (-(Real.pi * η * t)))) (volume.restrict (Set.Ici 1)) := by
    intro η hη
    have h1 : IntegrableOn (fun t : ℝ => t^M * Real.exp ((-(Real.pi * η)) * t)) (Set.Ioi 0) := by
      simpa only [Real.rpow_one] using
        integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := M) (b := Real.pi * η) (by linarith) one_pos (by positivity)
    have heq : (fun t : ℝ => t^M * Real.exp ((-(Real.pi * η)) * t)) = (fun t : ℝ => t^M * Real.exp (-(Real.pi * η * t))) := by
      funext t; rw [neg_mul]
    rw [heq] at h1
    have h2 : IntegrableOn (fun t : ℝ => t^M * Real.exp (-(Real.pi * η * t))) (Set.Ici 1) :=
      h1.mono_set (Set.Ici_subset_Ioi.mpr (by norm_num))
    exact h2.const_mul C
  have hint_deriv : ∀ η : ℝ, 0 < η → Integrable (fun t : ℝ => (C * Real.pi) * (t^(M+1) * Real.exp (-(Real.pi * η * t)))) (volume.restrict (Set.Ici 1)) := by
    intro η hη
    have h1 : IntegrableOn (fun t : ℝ => t^(M+1) * Real.exp ((-(Real.pi * η)) * t)) (Set.Ioi 0) := by
      simpa only [Real.rpow_one] using
        integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := M+1) (b := Real.pi * η) (by linarith) one_pos (by positivity)
    have heq : (fun t : ℝ => t^(M+1) * Real.exp ((-(Real.pi * η)) * t)) = (fun t : ℝ => t^(M+1) * Real.exp (-(Real.pi * η * t))) := by
      funext t; rw [neg_mul]
    rw [heq] at h1
    have h2 : IntegrableOn (fun t : ℝ => t^(M+1) * Real.exp (-(Real.pi * η * t))) (Set.Ici 1) :=
      h1.mono_set (Set.Ici_subset_Ioi.mpr (by norm_num))
    exact h2.const_mul (C * Real.pi)
  have hΦ_diff : DifferentiableOn ℂ
      (fun z : ℂ => ∫ t in Set.Ici 1, ψ t * Complex.exp (-(Real.pi * z * (t:ℂ)))) U := by
    intro z₀ hz₀
    have hz₀' : -1 < z₀.re := hz₀
    set η : ℝ := (z₀.re + 1) / 2 with hηdef
    have hηpos : 0 < η := by rw [hηdef]; linarith
    have hz₀_eq : z₀.re = -1 + 2 * η := by rw [hηdef]; ring
    have hbase := hint_base η hηpos
    have hder := hint_deriv η hηpos
    have hbd_base : ∀ᵐ t ∂(volume.restrict (Set.Ici 1)),
        ‖ψ t * Complex.exp (-(Real.pi * z₀ * (t:ℂ)))‖ ≤ C * (t^M * Real.exp (-(Real.pi * η * t))) := by
      filter_upwards [hbound, MeasureTheory.ae_restrict_mem measurableSet_Ici] with t hbnd ht
      have ht1 : 1 ≤ t := ht
      have htpos : 0 < t := lt_of_lt_of_le one_pos ht1
      rw [norm_mul, Complex.norm_exp]
      have hexp : (-(Real.pi * z₀ * (t:ℂ))).re = -(Real.pi * z₀.re * t) := by
        simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
      rw [hexp]
      have hkey : Real.exp (-(Real.pi * t)) * Real.exp (-(Real.pi * z₀.re * t))
          ≤ Real.exp (-(Real.pi * η * t)) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have hEq : -(Real.pi * t) + -(Real.pi * z₀.re * t) = -(Real.pi * (1 + z₀.re) * t) := by ring
        rw [hEq]
        apply neg_le_neg
        apply mul_le_mul_of_nonneg_right _ htpos.le
        apply mul_le_mul_of_nonneg_left _ Real.pi_pos.le
        linarith
      calc ‖ψ t‖ * Real.exp (-(Real.pi * z₀.re * t))
          ≤ (C * t^M * Real.exp (-(Real.pi * t))) * Real.exp (-(Real.pi * z₀.re * t)) :=
            mul_le_mul_of_nonneg_right hbnd (Real.exp_nonneg _)
        _ = C * (t^M * (Real.exp (-(Real.pi * t)) * Real.exp (-(Real.pi * z₀.re * t)))) := by ring
        _ ≤ C * (t^M * Real.exp (-(Real.pi * η * t))) := by
            apply mul_le_mul_of_nonneg_left _ hC.le
            exact mul_le_mul_of_nonneg_left hkey (Real.rpow_nonneg (le_of_lt htpos) _)
    have hF_int : Integrable (fun t : ℝ => ψ t * Complex.exp (-(Real.pi * z₀ * (t:ℂ)))) (volume.restrict (Set.Ici 1)) :=
      hbase.mono' (hmeas.mul (hcont z₀)) hbd_base
    have hF'_meas : AEStronglyMeasurable (fun t : ℝ => ψ t * (-(Real.pi * (t:ℂ))) * Complex.exp (-(Real.pi * z₀ * (t:ℂ)))) (volume.restrict (Set.Ici 1)) := by
      apply AEStronglyMeasurable.mul ?_ (hcont z₀)
      exact AEStronglyMeasurable.mul hmeas hcont_lin.aestronglyMeasurable
    have h_bound : ∀ᵐ t ∂(volume.restrict (Set.Ici 1)), ∀ z ∈ Metric.ball z₀ η,
        ‖ψ t * (-(Real.pi * (t:ℂ))) * Complex.exp (-(Real.pi * z * (t:ℂ)))‖
          ≤ (C * Real.pi) * (t^(M+1) * Real.exp (-(Real.pi * η * t))) := by
      filter_upwards [hbound, MeasureTheory.ae_restrict_mem measurableSet_Ici] with t hbnd ht
      intro z hz
      have ht1 : 1 ≤ t := ht
      have htpos : 0 < t := lt_of_lt_of_le one_pos ht1
      rw [Metric.mem_ball, Complex.dist_eq] at hz
      have hzre : z.re > -1 + η := by
        have h1 := Complex.abs_re_le_norm (z - z₀)
        rw [Complex.sub_re] at h1
        have hlt : |z.re - z₀.re| < η := lt_of_le_of_lt h1 hz
        rw [abs_lt] at hlt
        rw [hz₀_eq] at hlt
        linarith [hlt.1]
      rw [norm_mul, norm_mul, Complex.norm_exp, norm_neg]
      have hexp : (-(Real.pi * z * (t:ℂ))).re = -(Real.pi * z.re * t) := by
        simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
      rw [hexp]
      have hnpi : ‖Real.pi * (t:ℂ)‖ = Real.pi * t := by
        rw [Complex.norm_mul]
        have h1 : ‖(Real.pi:ℂ)‖ = Real.pi := by
          rw [show ‖(Real.pi:ℂ)‖ = |Real.pi| from by
            rw [Complex.norm_def, Complex.normSq_ofReal]; simpa [sq] using Real.sqrt_sq_eq_abs Real.pi]
          exact abs_of_pos Real.pi_pos
        rw [h1, show ‖(t:ℂ)‖ = |t| from by
          rw [Complex.norm_def, Complex.normSq_ofReal]; simpa [sq] using Real.sqrt_sq_eq_abs t, abs_of_pos htpos]
      rw [hnpi]
      have hkey : Real.exp (-(Real.pi * t)) * Real.exp (-(Real.pi * z.re * t))
          ≤ Real.exp (-(Real.pi * η * t)) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have hEq : -(Real.pi * t) + -(Real.pi * z.re * t) = -(Real.pi * (1 + z.re) * t) := by ring
        rw [hEq]
        apply neg_le_neg
        apply mul_le_mul_of_nonneg_right _ htpos.le
        apply mul_le_mul_of_nonneg_left _ Real.pi_pos.le
        linarith
      have hrpow : t^(M+1) = t^M * t := by rw [Real.rpow_add htpos, Real.rpow_one]
      calc ‖ψ t‖ * (Real.pi * t) * Real.exp (-(Real.pi * z.re * t))
          ≤ (C * t^M * Real.exp (-(Real.pi * t))) * (Real.pi * t) * Real.exp (-(Real.pi * z.re * t)) := by
            apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact hbnd
        _ = (C * Real.pi) * (t^(M+1) * (Real.exp (-(Real.pi * t)) * Real.exp (-(Real.pi * z.re * t)))) := by
            rw [hrpow]; ring
        _ ≤ (C * Real.pi) * (t^(M+1) * Real.exp (-(Real.pi * η * t))) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact mul_le_mul_of_nonneg_left hkey (Real.rpow_nonneg (le_of_lt htpos) _)
    have h_diff : ∀ᵐ t ∂(volume.restrict (Set.Ici 1)), ∀ z ∈ Metric.ball z₀ η,
        HasDerivAt (fun z : ℂ => ψ t * Complex.exp (-(Real.pi * z * (t:ℂ))))
          (ψ t * (-(Real.pi * (t:ℂ))) * Complex.exp (-(Real.pi * z * (t:ℂ)))) z := by
      filter_upwards with t
      intro z _
      have hlin : HasDerivAt (fun z : ℂ => Real.pi * z * (t:ℂ)) (Real.pi * (t:ℂ)) z := by
        have h := (hasDerivAt_id z).const_mul (Real.pi : ℂ)
        simpa using h.mul_const (t:ℂ)
      have hneg : HasDerivAt (fun z : ℂ => -(Real.pi * z * (t:ℂ))) (-(Real.pi * (t:ℂ))) z := hlin.neg
      have hexp2 : HasDerivAt (fun z : ℂ => Complex.exp (-(Real.pi * z * (t:ℂ))))
          (Complex.exp (-(Real.pi * z * (t:ℂ))) * (-(Real.pi * (t:ℂ)))) z :=
        (Complex.hasDerivAt_exp (-(Real.pi * z * (t:ℂ)))).comp z hneg
      have h3 : HasDerivAt (fun z : ℂ => ψ t * Complex.exp (-(Real.pi * z * (t:ℂ))))
          (ψ t * (Complex.exp (-(Real.pi * z * (t:ℂ))) * (-(Real.pi * (t:ℂ))))) z :=
        hexp2.const_mul (ψ t)
      have heq : ψ t * (Complex.exp (-(Real.pi * z * (t:ℂ))) * (-(Real.pi * (t:ℂ))))
          = ψ t * (-(Real.pi * (t:ℂ))) * Complex.exp (-(Real.pi * z * (t:ℂ))) := by ring
      rw [heq] at h3
      exact h3
    obtain ⟨-, hderiv⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume.restrict (Set.Ici (1:ℝ)))
      (F := fun z t => ψ t * Complex.exp (-(Real.pi * z * (t:ℂ))))
      (F' := fun z t => ψ t * (-(Real.pi * (t:ℂ))) * Complex.exp (-(Real.pi * z * (t:ℂ))))
      (bound := fun t => (C * Real.pi) * (t^(M+1) * Real.exp (-(Real.pi * η * t))))
      (x₀ := z₀) (s := Metric.ball z₀ η)
      (Metric.ball_mem_nhds z₀ hηpos)
      (Filter.Eventually.of_forall (fun z => hmeas.mul (hcont z)))
      hF_int hF'_meas h_bound hder h_diff
    exact hderiv.differentiableAt.differentiableWithinAt
  have hΦ_ana : AnalyticOnNhd ℂ (fun z : ℂ => ∫ t in Set.Ici 1, ψ t * Complex.exp (-(Real.pi * z * (t:ℂ)))) U :=
    hΦ_diff.analyticOnNhd hUopen
  have hcd : ContDiffOn ℝ ω (fun z : ℂ => ∫ t in Set.Ici 1, ψ t * Complex.exp (-(Real.pi * z * (t:ℂ)))) U :=
    (hΦ_ana.contDiffOn_of_completeSpace).restrict_scalars ℝ
  have hsq : ContDiff ℝ ω (fun r : ℝ => ((r:ℂ))^2) := Complex.ofRealCLM.contDiff.pow 2
  have hmaps : ∀ r : ℝ, (fun r : ℝ => ((r:ℂ))^2) r ∈ U := by
    intro r
    simp only [U, Set.mem_ofPred_eq]
    have h : (((r:ℂ))^2).re = r^2 := by
      rw [sq, Complex.mul_re]; simp [Complex.ofReal_re, Complex.ofReal_im]; ring
    rw [h]; nlinarith [sq_nonneg r]
  exact hcd.comp (Complex.ofRealCLM.contDiff.contDiffOn) (fun x hx => by
    simp only [U, Set.mem_ofPred_eq]; exact hx)

open Work.Asymptotics

theorem contDiffOn_intervalIntegral_exp_ofReal_general
    {κ : ℝ → ℂ} {a b B : ℝ} (ha : 0 < a) (hab : a ≤ b) (hB : 0 ≤ B)
    (hmeas : AEStronglyMeasurable κ (volume.restrict (Set.Ioc a b)))
    (hbound : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), ‖κ t‖ ≤ B) :
    ContDiffOn ℝ ω (fun x : ℝ => ∫ t in a..b, κ t * Complex.exp (-(Real.pi * (x : ℂ) * (t : ℂ)))) (Set.Ioi (-1)) := by
  have hconv : ∀ f : ℝ → ℂ, (∫ t in a..b, f t) = ∫ t, f t ∂(volume.restrict (Set.Ioc a b)) := by
    intro f; rw [intervalIntegral.integral_of_le hab]
  have hcont_exp : ∀ w : ℂ, AEStronglyMeasurable (fun t : ℝ => Complex.exp (-(Real.pi * w * (t:ℂ)))) (volume.restrict (Set.Ioc a b)) := by
    intro w
    exact (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal).neg).aestronglyMeasurable
  have hcont_lin : Continuous (fun t : ℝ => -(Real.pi * (t:ℂ))) :=
    (continuous_const.mul Complex.continuous_ofReal).neg
  have hnormpi : ‖(Real.pi : ℂ)‖ = Real.pi := by
    rw [show ‖(Real.pi:ℂ)‖ = |Real.pi| from by
      rw [Complex.norm_def, Complex.normSq_ofReal]; simpa [sq] using Real.sqrt_sq_eq_abs Real.pi]
    exact abs_of_pos Real.pi_pos
  have hdiff : Differentiable ℂ (fun z : ℂ => ∫ t in a..b, κ t * Complex.exp (-(Real.pi * z * (t:ℂ)))) := by
    intro z
    have h_int : Integrable (fun t : ℝ => κ t * Complex.exp (-(Real.pi * z * (t:ℂ)))) (volume.restrict (Set.Ioc a b)) := by
      refine Integrable.mono' (integrable_const (B * Real.exp (Real.pi * (|z.re| * (|b| + 1))))) ?_ ?_
      · exact hmeas.mul (hcont_exp z)
      · filter_upwards [hbound, MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t hbnd ht
        rw [norm_mul, Complex.norm_exp]
        have hexp : (-(Real.pi * z * (t:ℂ))).re = -(Real.pi * z.re * t) := by
          simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
        rw [hexp]
        have ht0 : 0 < t := lt_trans ha ht.1
        have hb1 : t ≤ |b| + 1 := by
          have hbb : b ≤ |b| := le_abs_self b
          linarith [abs_nonneg b, ht.2]
        have h3 : - (z.re * t) ≤ |z.re| * (|b| + 1) := by
          calc - (z.re * t) ≤ |z.re * t| := neg_le_abs _
            _ = |z.re| * |t| := abs_mul _ _
            _ ≤ |z.re| * (|b| + 1) := mul_le_mul_of_nonneg_left (by rw [abs_of_pos ht0]; exact hb1) (abs_nonneg _)
        have h1 : -(Real.pi * z.re * t) ≤ Real.pi * (|z.re| * (|b| + 1)) := by
          have : -(Real.pi * z.re * t) = Real.pi * (-(z.re * t)) := by ring
          rw [this]
          exact mul_le_mul_of_nonneg_left h3 (le_of_lt Real.pi_pos)
        exact mul_le_mul hbnd (Real.exp_le_exp.mpr h1) (Real.exp_nonneg _) hB
    have h_bound : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), ∀ w ∈ Metric.ball z 1,
        ‖κ t * (-(Real.pi * (t:ℂ))) * Complex.exp (-(Real.pi * w * (t:ℂ)))‖
          ≤ B * Real.pi * (|b| + 1) * Real.exp (Real.pi * ((|z.re| + 1) * (|b| + 1))) := by
      filter_upwards [hbound, MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t hbnd ht
      intro w hw
      rw [Metric.mem_ball, Complex.dist_eq] at hw
      have hrel : |w.re| * (|b| + 1) ≤ (|z.re| + 1) * (|b| + 1) := by
        have hre2 : |w.re| ≤ |z.re| + 1 := by
          have h1 := abs_sub_abs_le_abs_sub w.re z.re
          have h2 := Complex.abs_re_le_norm (w - z)
          rw [Complex.sub_re] at h2
          linarith
        exact mul_le_mul_of_nonneg_right hre2 (by positivity)
      have hre2 : |w.re| ≤ |z.re| + 1 := by
        have h1 := abs_sub_abs_le_abs_sub w.re z.re
        have h2 := Complex.abs_re_le_norm (w - z)
        rw [Complex.sub_re] at h2
        linarith
      rw [norm_mul, norm_mul, Complex.norm_exp, norm_neg]
      have hexp : (-(Real.pi * w * (t:ℂ))).re = -(Real.pi * w.re * t) := by
        simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
      rw [hexp]
      have htle : t ≤ |b| + 1 := by
        have hbb : b ≤ |b| := le_abs_self b
        linarith [abs_nonneg b, ht.2]
      have htpos : 0 < t := lt_trans ha ht.1
      have hnpi : ‖(Real.pi : ℂ) * (t:ℂ)‖ = Real.pi * t := by
        rw [Complex.norm_mul, hnormpi]
        congr 1
        rw [show ‖(t:ℂ)‖ = |t| from by
          rw [Complex.norm_def, Complex.normSq_ofReal]; simpa [sq] using Real.sqrt_sq_eq_abs t]
        exact abs_of_pos htpos
      rw [hnpi]
      have hexple : Real.exp (-(Real.pi * w.re * t)) ≤ Real.exp (Real.pi * ((|z.re| + 1) * (|b| + 1))) := by
        apply Real.exp_le_exp.mpr
        have h4 : -(w.re * t) ≤ |w.re| * t := by
          calc -(w.re * t) ≤ |w.re * t| := neg_le_abs _
            _ = |w.re| * |t| := abs_mul _ _
            _ = |w.re| * t := by rw [abs_of_pos htpos]
        have h5 : |w.re| * t ≤ |w.re| * (|b| + 1) := mul_le_mul_of_nonneg_left htle (abs_nonneg _)
        nlinarith [Real.pi_pos, hre2]
      calc ‖κ t‖ * (Real.pi * t) * Real.exp (-(Real.pi * w.re * t))
          ≤ B * (Real.pi * t) * Real.exp (Real.pi * ((|z.re| + 1) * (|b| + 1))) := by
            apply mul_le_mul
            · exact mul_le_mul hbnd (le_refl _) (by positivity) hB
            · exact hexple
            · positivity
            · positivity
          _ ≤ B * Real.pi * (|b| + 1) * Real.exp (Real.pi * ((|z.re| + 1) * (|b| + 1))) := by
            apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
            have hpi : Real.pi * t ≤ Real.pi * (|b| + 1) := by
              simpa using mul_le_mul_of_nonneg_left htle (le_of_lt Real.pi_pos)
            have h2 := mul_le_mul_of_nonneg_left hpi hB
            linarith [h2]
    have h_diff : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), ∀ w ∈ Metric.ball z 1,
        HasDerivAt (fun w : ℂ => κ t * Complex.exp (-(Real.pi * w * (t:ℂ))))
          (κ t * (-(Real.pi * (t:ℂ))) * Complex.exp (-(Real.pi * w * (t:ℂ)))) w := by
      filter_upwards with t
      intro w _
      have hlin : HasDerivAt (fun w : ℂ => Real.pi * w * (t:ℂ)) (Real.pi * (t:ℂ)) w := by
        have h := (hasDerivAt_id w).const_mul (Real.pi : ℂ)
        simpa using h.mul_const (t:ℂ)
      have hneg : HasDerivAt (fun w : ℂ => -(Real.pi * w * (t:ℂ))) (-(Real.pi * (t:ℂ))) w := hlin.neg
      have hexp2 : HasDerivAt (fun w : ℂ => Complex.exp (-(Real.pi * w * (t:ℂ))))
          (Complex.exp (-(Real.pi * w * (t:ℂ))) * (-(Real.pi * (t:ℂ)))) w :=
        (Complex.hasDerivAt_exp (-(Real.pi * w * (t:ℂ)))).comp w hneg
      have h3 : HasDerivAt (fun w : ℂ => κ t * Complex.exp (-(Real.pi * w * (t:ℂ))))
          (κ t * (Complex.exp (-(Real.pi * w * (t:ℂ))) * (-(Real.pi * (t:ℂ))))) w :=
        hexp2.const_mul (κ t)
      have heq : κ t * (Complex.exp (-(Real.pi * w * (t:ℂ))) * (-(Real.pi * (t:ℂ))))
          = κ t * (-(Real.pi * (t:ℂ))) * Complex.exp (-(Real.pi * w * (t:ℂ))) := by ring
      rw [heq] at h3
      exact h3
    have hF'_meas : AEStronglyMeasurable (fun t : ℝ => κ t * (-(Real.pi * (t:ℂ))) * Complex.exp (-(Real.pi * z * (t:ℂ)))) (volume.restrict (Set.Ioc a b)) := by
      apply AEStronglyMeasurable.mul ?_ (hcont_exp z)
      exact AEStronglyMeasurable.mul hmeas hcont_lin.aestronglyMeasurable
    obtain ⟨-, hderiv⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume.restrict (Set.Ioc a b))
      (F := fun z t => κ t * Complex.exp (-(Real.pi * z * (t:ℂ))))
      (F' := fun z t => κ t * (-(Real.pi * (t:ℂ))) * Complex.exp (-(Real.pi * z * (t:ℂ))))
      (bound := fun _ => B * Real.pi * (|b| + 1) * Real.exp (Real.pi * ((|z.re| + 1) * (|b| + 1))))
      (x₀ := z) (s := Metric.ball z 1)
      (Metric.ball_mem_nhds z one_pos)
      (Filter.Eventually.of_forall (fun w => hmeas.mul (hcont_exp w)))
      h_int hF'_meas h_bound (integrable_const _) h_diff
    have hfun : (fun n : ℂ => ∫ a, κ a * Complex.exp (-(Real.pi * n * (a:ℂ))) ∂(volume.restrict (Set.Ioc a b)))
        = fun n : ℂ => ∫ t in a..b, κ t * Complex.exp (-(Real.pi * n * (t:ℂ))) := by
      funext n; exact (hconv _).symm
    rw [hfun] at hderiv
    exact hderiv.differentiableAt
  have hcdR : ContDiff ℝ ω (fun z : ℂ => ∫ t in a..b, κ t * Complex.exp (-(Real.pi * z * (t:ℂ)))) :=
    ((hdiff.differentiableOn.analyticOnNhd isOpen_univ).contDiff).restrict_scalars ℝ
  exact (hcdR.comp_contDiffOn Complex.ofRealCLM.contDiff.contDiffOn).mono (Set.subset_univ _)

/-! ## The scale is bounded on the bad-line region -/

/-! ## The `high` piece on the bad-line region -/

theorem lowBad_highPart_seminorm (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (k l : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ : ℍ) (r : ℝ), lowBadSet τ →
      (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => highPart (Gcusp ℓ d) τ s) r‖ ≤ C := by
  obtain ⟨c, N, hc, hb⟩ := highPart_seminorm_scaled (Gcusp ℓ d) (fun i j => Gcusp_moderate ℓ d i j) k l
  refine ⟨c * max (6 ^ N) 1, mul_nonneg hc (le_trans zero_le_one (le_max_right _ _)), ?_⟩
  intro τ r hτ
  have hs6 : scale τ ≤ 6 := lowBadSet_scale_le hτ
  have hs1 : (1:ℝ) ≤ scale τ := Work.Kernels.one_le_scale τ
  have hbound : (scale τ) ^ N ≤ max (6 ^ N) 1 := by
    rcases le_or_gt 0 N with hN | hN
    · exact le_trans (Real.rpow_le_rpow (le_trans zero_le_one hs1) hs6 hN) (le_max_left _ _)
    · have h2 : (scale τ) ^ N ≤ (1:ℝ) ^ N := Real.rpow_le_rpow_of_nonpos (by norm_num) hs1 (le_of_lt hN)
      rw [Real.one_rpow] at h2
      exact h2.trans (le_max_right _ _)
  calc (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => highPart (Gcusp ℓ d) τ s) r‖
      ≤ c * (scale τ) ^ N := hb τ r hτ.1
    _ ≤ c * max (6 ^ N) 1 := mul_le_mul_of_nonneg_left hbound hc

/-! ## The translate pole -/

/-! ## Smoothness of the spike piece -/

lemma contDiffOn_PhiSpike {τ : ℍ} (hτ : lowBadSet τ) :
    ContDiffOn ℝ ω (fun x : ℝ => PhiSpike τ x) (Set.Ioi (-1)) := by
  set a : ℝ := τ.im - lowRho with ha
  set b : ℝ := τ.im + lowRho with hb
  have hapos : 0 < a := by rw [ha, lowRho]; linarith [hτ.2.1]
  have hab : a ≤ b := by rw [ha, hb, lowRho]; linarith
  have hcnt : Continuous (fun t : ℝ => tpole τ t) := continuous_tpole hτ
  have hmeas : AEStronglyMeasurable (fun t : ℝ => tpole τ t)
      (volume.restrict (Set.Ioc a b)) := hcnt.aestronglyMeasurable
  have hbound : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)),
      ‖tpole τ t‖ ≤ 1 / (2 * Real.pi * |τ.re - tsign τ|) :=
    Filter.Eventually.of_forall (fun t => norm_tpole_le hτ t)
  have hkey := contDiffOn_intervalIntegral_exp_ofReal_general (κ := fun t => tpole τ t)
    hapos hab (by positivity) hmeas hbound
  have hid : ∀ x : ℝ, PhiSpike τ x
      = ∫ t in (a)..(b), tpole τ t * Complex.exp (-(Real.pi * (x:ℂ) * (t:ℂ))) := by
    intro x
    rw [PhiSpike, lowWin, ← ha, ← hb]
    rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le hab]
  exact hkey.congr (fun x _ => hid x)

/-! ## Boundedness of `Aexp` on the region -/

/-! ## Smoothness of the low and tail pieces -/

lemma contDiffOn_PhiOne (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) {C : ℝ} (hC : 0 ≤ C)
    (hdec1 : ∀ (τ : ℍ), lowBadSet τ → ∀ t : ℝ, 0 < t → t ≤ lowT →
      ‖Kaxis (Kfun ℓ d) τ t - tpole τ t‖ ≤ C)
    (hdec2 : ∀ (τ : ℍ), lowBadSet τ → ∀ t : ℝ, 0 < t → t ≤ lowT → lowRho ≤ |t - τ.im| →
      ‖Kaxis (Kfun ℓ d) τ t‖ ≤ C)
    {τ : ℍ} (hτ : lowBadSet τ) :
    ContDiffOn ℝ ω (fun x : ℝ => PhiOne ℓ d τ x) (Set.Ioi (-1)) := by
  have hLT : (1:ℝ) ≤ lowT := by rw [lowT]; norm_num
  have hmeas1 : AEStronglyMeasurable (fun t : ℝ => Kaxis (Kfun ℓ d) τ t)
      (volume.restrict (Set.Ioc 0 1)) := (measurable_Kaxis_Kfun ℓ d hd τ).aestronglyMeasurable
  have hmeas2 : AEStronglyMeasurable (fun t : ℝ => (lowWin τ).indicator (tpole τ) t)
      (volume.restrict (Set.Ioc 0 1)) :=
    ((continuous_tpole hτ).measurable.indicator measurableSet_Ioo).aestronglyMeasurable
  have hbound : ∀ᵐ t ∂(volume.restrict (Set.Ioc 0 1)),
      ‖Kaxis (Kfun ℓ d) τ t - (lowWin τ).indicator (tpole τ) t‖ ≤ C := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Set.mem_Ioc] at ht
    by_cases htw : t ∈ lowWin τ
    · rw [Set.indicator_of_mem htw]
      exact hdec1 τ hτ t ht.1 (le_trans ht.2 hLT)
    · rw [Set.indicator_of_notMem htw, sub_zero]
      exact hdec2 τ hτ t ht.1 (le_trans ht.2 hLT) (off_win_gives_sep htw)
  have hkey := contDiffOn_intervalIntegral_exp_ofReal (κ := fun t : ℝ =>
    Kaxis (Kfun ℓ d) τ t - (lowWin τ).indicator (tpole τ) t) hC (hmeas1.sub hmeas2) hbound
  have hid : ∀ x : ℝ, PhiOne ℓ d τ x
      = ∫ t in (0:ℝ)..1, (Kaxis (Kfun ℓ d) τ t - (lowWin τ).indicator (tpole τ) t)
          * Complex.exp (-(Real.pi * (x:ℂ) * (t:ℂ))) := by
    intro x
    rw [PhiOne, intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  exact hkey.congr (fun x _ => hid x)

lemma tpole_not_mem_win {τ : ℍ} (hτ : lowBadSet τ) {t : ℝ} (ht : lowT ≤ t) : t ∉ lowWin τ := by
  intro h
  rw [lowWin, Set.mem_Ioo] at h
  rw [lowT] at ht
  have h1 : τ.im + lowRho < 3 := by
    rw [lowRho]
    linarith [hτ.2.2.1]
  linarith [h.2, h1, ht]

lemma contDiffOn_PhiTwo (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) {C : ℝ} (hC : 0 ≤ C)
    (hdec1 : ∀ (τ : ℍ), lowBadSet τ → ∀ t : ℝ, 0 < t → t ≤ lowT →
      ‖Kaxis (Kfun ℓ d) τ t - tpole τ t‖ ≤ C)
    (hdec2 : ∀ (τ : ℍ), lowBadSet τ → ∀ t : ℝ, 0 < t → t ≤ lowT → lowRho ≤ |t - τ.im| →
      ‖Kaxis (Kfun ℓ d) τ t‖ ≤ C)
    (htail : ∃ Ct Mt : ℝ, 0 < Ct ∧ 0 ≤ Mt ∧ ∀ (τ : ℍ), lowBadSet τ → ∀ t : ℝ, lowT ≤ t →
      ‖Kaxis (Kfun ℓ d) τ t - Aexp (Gcusp ℓ d) τ t‖
        ≤ Ct * (1 + t) ^ Mt * Real.exp (-(Real.pi * t)))
    {τ : ℍ} (hτ : lowBadSet τ) :
    ContDiffOn ℝ ω (fun x : ℝ => PhiTwo ℓ d τ x) (Set.Ioi (-1)) := by
  obtain ⟨CB, hCB, hbC⟩ := lowBadSet_Aexp_le ℓ d hd
  obtain ⟨Ct, Mt, hCt, hMt, hbT⟩ := htail
  have hLT : (1:ℝ) ≤ lowT := by rw [lowT]; norm_num
  set D : ℝ := max ((C + CB + 1) * Real.exp (Real.pi * lowT)) (Ct * 2 ^ Mt) with hD
  set M : ℝ := max Mt 0 with hM
  have hDpos : 0 < D := by
    have h1 : (0:ℝ) < (C + CB + 1) * Real.exp (Real.pi * lowT) := by positivity
    exact lt_of_lt_of_le h1 (le_max_left _ _)
  have hMnn : 0 ≤ M := le_max_right _ _
  have hmeas : AEStronglyMeasurable (fun t : ℝ => Kaxis (Kfun ℓ d) τ t
      - Aexp (Gcusp ℓ d) τ t - (lowWin τ).indicator (tpole τ) t)
      (volume.restrict (Set.Ici 1)) :=
    (((measurable_Kaxis_Kfun ℓ d hd τ).aestronglyMeasurable).sub
      (by unfold Aexp; fun_prop)).sub
      (((continuous_tpole hτ).measurable.indicator measurableSet_Ioo).aestronglyMeasurable)
  have hbound : ∀ᵐ t ∂(volume.restrict (Set.Ici 1)),
      ‖Kaxis (Kfun ℓ d) τ t - Aexp (Gcusp ℓ d) τ t
        - (lowWin τ).indicator (tpole τ) t‖ ≤ D * t ^ M * Real.exp (-(Real.pi * t)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
    have ht1 : (1:ℝ) ≤ t := ht
    have ht0 : (0:ℝ) < t := lt_of_lt_of_le zero_lt_one ht1
    by_cases htT : t ≤ lowT
    · have h1 : ‖Kaxis (Kfun ℓ d) τ t - (lowWin τ).indicator (tpole τ) t‖ ≤ C := by
        by_cases hw : t ∈ lowWin τ
        · rw [Set.indicator_of_mem hw]
          exact hdec1 τ hτ t ht0 (le_trans htT (le_refl lowT))
        · rw [Set.indicator_of_notMem hw, sub_zero]
          exact hdec2 τ hτ t ht0 (le_trans htT (le_refl lowT)) (off_win_gives_sep hw)
      have h2 : ‖Aexp (Gcusp ℓ d) τ t‖ ≤ CB := hbC τ hτ t ht1 htT
      have h3 : ‖Kaxis (Kfun ℓ d) τ t - Aexp (Gcusp ℓ d) τ t
          - (lowWin τ).indicator (tpole τ) t‖
          ≤ C + CB + 1 := by
        have heq : Kaxis (Kfun ℓ d) τ t - Aexp (Gcusp ℓ d) τ t
            - (lowWin τ).indicator (tpole τ) t
            = (Kaxis (Kfun ℓ d) τ t - (lowWin τ).indicator (tpole τ) t)
              - Aexp (Gcusp ℓ d) τ t := by ring
        rw [heq]
        linarith [norm_sub_le (Kaxis (Kfun ℓ d) τ t - (lowWin τ).indicator (tpole τ) t)
          (Aexp (Gcusp ℓ d) τ t)]
      have h4 : t ^ M * Real.exp (-(Real.pi * t)) ≥ Real.exp (-(Real.pi * lowT)) := by
        have h5 : (1:ℝ) ≤ t ^ M := Real.one_le_rpow ht1 hMnn
        have h6 : Real.exp (-(Real.pi * lowT)) ≤ Real.exp (-(Real.pi * t)) :=
          Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, htT])
        calc Real.exp (-(Real.pi * lowT)) ≤ Real.exp (-(Real.pi * t)) := h6
          _ = 1 * Real.exp (-(Real.pi * t)) := (one_mul _).symm
          _ ≤ t ^ M * Real.exp (-(Real.pi * t)) :=
              mul_le_mul_of_nonneg_right h5 (Real.exp_nonneg _)
      have h7 : (C + CB + 1) ≤ D * Real.exp (-(Real.pi * lowT)) := by
        have h8 : (C + CB + 1) * Real.exp (Real.pi * lowT) ≤ D := le_max_left _ _
        have h9 : ((C + CB + 1) * Real.exp (Real.pi * lowT)) * Real.exp (-(Real.pi * lowT))
            = (C + CB + 1) := by
          rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
        have h10 := mul_le_mul_of_nonneg_right h8 (Real.exp_pos (-(Real.pi * lowT))).le
        rw [h9] at h10
        linarith [h10]
      calc ‖Kaxis (Kfun ℓ d) τ t - Aexp (Gcusp ℓ d) τ t
            - (lowWin τ).indicator (tpole τ) t‖
          ≤ C + CB + 1 := h3
        _ ≤ D * (t ^ M * Real.exp (-(Real.pi * t))) := by
            have h11 : D * Real.exp (-(Real.pi * lowT)) ≤ D * (t ^ M * Real.exp (-(Real.pi * t))) :=
              mul_le_mul_of_nonneg_left h4 hDpos.le
            linarith [h7, h11]
        _ = D * t ^ M * Real.exp (-(Real.pi * t)) := by ring
    · have htT' : lowT ≤ t := le_of_lt (not_le.mp htT)
      rw [Set.indicator_of_notMem (tpole_not_mem_win hτ htT'), sub_zero]
      have h1 : ‖Kaxis (Kfun ℓ d) τ t - Aexp (Gcusp ℓ d) τ t‖
          ≤ Ct * (1 + t) ^ Mt * Real.exp (-(Real.pi * t)) := hbT τ hτ t htT'
      have h2 : (1 + t) ^ Mt ≤ 2 ^ Mt * t ^ Mt := by
        have h3 : (1 + t) ≤ 2 * t := by linarith
        calc (1 + t) ^ Mt ≤ (2 * t) ^ Mt := Real.rpow_le_rpow (by linarith) h3 hMt
          _ = 2 ^ Mt * t ^ Mt := Real.mul_rpow (by norm_num) (by linarith)
      have h4 : t ^ Mt ≤ t ^ M := Real.rpow_le_rpow_of_exponent_le ht1 (le_max_left Mt 0)
      have h5 : Ct * 2 ^ Mt ≤ D := le_max_right _ _
      have h6 : Ct * (1 + t) ^ Mt ≤ D * t ^ M := by
        calc Ct * (1 + t) ^ Mt ≤ Ct * (2 ^ Mt * t ^ Mt) := mul_le_mul_of_nonneg_left h2 hCt.le
          _ = (Ct * 2 ^ Mt) * t ^ Mt := by ring
          _ ≤ D * t ^ Mt := mul_le_mul_of_nonneg_right h5 (Real.rpow_nonneg (by linarith) _)
          _ ≤ D * t ^ M := mul_le_mul_of_nonneg_left h4 (le_of_lt hDpos)
      calc ‖Kaxis (Kfun ℓ d) τ t - Aexp (Gcusp ℓ d) τ t‖
          ≤ Ct * (1 + t) ^ Mt * Real.exp (-(Real.pi * t)) := h1
        _ = (Ct * (1 + t) ^ Mt) * Real.exp (-(Real.pi * t)) := by ring
        _ ≤ (D * t ^ M) * Real.exp (-(Real.pi * t)) :=
            mul_le_mul_of_nonneg_right h6 (Real.exp_nonneg _)
        _ = D * t ^ M * Real.exp (-(Real.pi * t)) := by ring
  have hkey := contDiffOn_integral_Ici_exp_ofReal (ψ := fun t : ℝ => Kaxis (Kfun ℓ d) τ t
    - Aexp (Gcusp ℓ d) τ t - (lowWin τ).indicator (tpole τ) t) hDpos hMnn hmeas hbound
  have hid : ∀ x : ℝ, PhiTwo ℓ d τ x
      = ∫ t in Set.Ici 1, (Kaxis (Kfun ℓ d) τ t - Aexp (Gcusp ℓ d) τ t
          - (lowWin τ).indicator (tpole τ) t) * Complex.exp (-(Real.pi * (x:ℂ) * (t:ℂ))) := by
    intro x
    rw [PhiTwo]
  exact hkey.congr (fun x _ => hid x)

lemma contDiffOn_part (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) {C : ℝ} (hC : 0 ≤ C)
    (hdec1 : ∀ (τ : ℍ), lowBadSet τ → ∀ t : ℝ, 0 < t → t ≤ lowT →
      ‖Kaxis (Kfun ℓ d) τ t - tpole τ t‖ ≤ C)
    (hdec2 : ∀ (τ : ℍ), lowBadSet τ → ∀ t : ℝ, 0 < t → t ≤ lowT → lowRho ≤ |t - τ.im| →
      ‖Kaxis (Kfun ℓ d) τ t‖ ≤ C)
    (htail : ∃ Ct Mt : ℝ, 0 < Ct ∧ 0 ≤ Mt ∧ ∀ (τ : ℍ), lowBadSet τ → ∀ t : ℝ, lowT ≤ t →
      ‖Kaxis (Kfun ℓ d) τ t - Aexp (Gcusp ℓ d) τ t‖
        ≤ Ct * (1 + t) ^ Mt * Real.exp (-(Real.pi * t)))
    {τ : ℍ} (hτ : lowBadSet τ) :
    ContDiffOn ℝ ω (fun x : ℝ => PhiOne ℓ d τ x + PhiTwo ℓ d τ x + PhiSpike τ x)
      (Set.Ioi (-1)) :=
  ((contDiffOn_PhiOne ℓ d hd hC hdec1 hdec2 hτ).add
    (contDiffOn_PhiTwo ℓ d hd hC hdec1 hdec2 htail hτ)).add (contDiffOn_PhiSpike hτ)

/-! ## The `r`-seminorm bound for `lowF2` on the bad-line region -/

theorem lowBad_hsemi_of_bounds (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {Cdec : ℝ} (hCdec : 0 ≤ Cdec)
    (hdec1 : ∀ (τ : ℍ), lowBadSet τ → ∀ t : ℝ, 0 < t → t ≤ lowT →
      ‖Kaxis (Kfun ℓ d) τ t - tpole τ t‖ ≤ Cdec)
    (hdec2 : ∀ (τ : ℍ), lowBadSet τ → ∀ t : ℝ, 0 < t → t ≤ lowT → lowRho ≤ |t - τ.im| →
      ‖Kaxis (Kfun ℓ d) τ t‖ ≤ Cdec)
    (htail : ∃ Ct Mt : ℝ, 0 < Ct ∧ 0 ≤ Mt ∧ ∀ (τ : ℍ), lowBadSet τ → ∀ t : ℝ, lowT ≤ t →
      ‖Kaxis (Kfun ℓ d) τ t - Aexp (Gcusp ℓ d) τ t‖
        ≤ Ct * (1 + t) ^ Mt * Real.exp (-(Real.pi * t)))
    (hPhiSpike : ∀ m N : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ (τ : ℍ), lowBadSet τ → ∀ x : ℝ, 0 ≤ x →
      ‖iteratedDeriv m (fun x : ℝ => PhiSpike τ x) x‖ ≤ K * (1 + x) ^ (-(N : ℝ)))
    (hPhi12 : ∀ m N : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ (τ : ℍ), lowBadSet τ → ∀ x : ℝ, 0 ≤ x →
      ‖iteratedDeriv m (fun x : ℝ => PhiOne ℓ d τ x + PhiTwo ℓ d τ x) x‖
        ≤ K * (1 + x) ^ (-(N : ℝ)))
    (k l : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ : ℍ) (r : ℝ), lowBadSet τ →
      (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => lowF2 ℓ d τ s) r‖ ≤ C := by
  obtain ⟨Chp, hChp, hhpb⟩ := lowBad_highPart_seminorm ℓ d hd k l
  obtain ⟨c, hc, hcomp⟩ := exists_seminorm_bound_of_iteratedDeriv_bound_poly k l (k + l) (by omega)
  set N : ℝ := ((k + l : ℕ) : ℝ) with hN
  -- bounds for the derivatives of the sum, for each order `m ≤ l`
  have hmn : ∀ m : ℕ, ∃ K : ℝ, 0 ≤ K ∧ (m ≤ l →
      ∀ (τ : ℍ), lowBadSet τ → ∀ x : ℝ, 0 ≤ x →
        ‖iteratedDeriv m (fun x : ℝ => PhiOne ℓ d τ x + PhiTwo ℓ d τ x + PhiSpike τ x) x‖
          ≤ K * (1 + x) ^ (-N)) := by
    intro m
    by_cases hm : m ≤ l
    · obtain ⟨K1, hK1, hb1⟩ := hPhi12 m (k + l)
      obtain ⟨K2, hK2, hb2⟩ := hPhiSpike m (k + l)
      refine ⟨K1 + K2, by positivity, fun _ τ hτ x hx => ?_⟩
      have hxm : x ∈ Set.Ioi (-1) := by rw [Set.mem_Ioi]; linarith
      have hnhds : Set.Ioi (-1) ∈ 𝓝 x := IsOpen.mem_nhds isOpen_Ioi hxm
      have hd1 : ContDiffAt ℝ (m : ℕ∞) (fun x : ℝ => PhiOne ℓ d τ x + PhiTwo ℓ d τ x) x :=
        ((contDiffOn_PhiOne ℓ d hd hCdec hdec1 hdec2 hτ).add
          (contDiffOn_PhiTwo ℓ d hd hCdec hdec1 hdec2 htail hτ)).contDiffAt hnhds |>.of_le le_top
      have hd2 : ContDiffAt ℝ (m : ℕ∞) (fun x : ℝ => PhiSpike τ x) x :=
        (contDiffOn_PhiSpike hτ).contDiffAt hnhds |>.of_le le_top
      have hid : iteratedDeriv m (fun x : ℝ => PhiOne ℓ d τ x + PhiTwo ℓ d τ x + PhiSpike τ x) x
          = iteratedDeriv m (fun x : ℝ => PhiOne ℓ d τ x + PhiTwo ℓ d τ x) x
            + iteratedDeriv m (fun x : ℝ => PhiSpike τ x) x := by
        rw [show (fun x : ℝ => PhiOne ℓ d τ x + PhiTwo ℓ d τ x + PhiSpike τ x)
            = (fun x : ℝ => PhiOne ℓ d τ x + PhiTwo ℓ d τ x) + (fun x : ℝ => PhiSpike τ x)
            from rfl]
        exact iteratedDeriv_add hd1 hd2
      rw [hid, hN]
      calc ‖iteratedDeriv m (fun x : ℝ => PhiOne ℓ d τ x + PhiTwo ℓ d τ x) x
            + iteratedDeriv m (fun x : ℝ => PhiSpike τ x) x‖
          ≤ ‖iteratedDeriv m (fun x : ℝ => PhiOne ℓ d τ x + PhiTwo ℓ d τ x) x‖
            + ‖iteratedDeriv m (fun x : ℝ => PhiSpike τ x) x‖ := norm_add_le _ _
        _ ≤ K1 * (1 + x) ^ (-(((k + l : ℕ) : ℝ))) + K2 * (1 + x) ^ (-(((k + l : ℕ) : ℝ))) :=
            add_le_add (hb1 τ hτ x hx) (hb2 τ hτ x hx)
        _ = (K1 + K2) * (1 + x) ^ (-(((k + l : ℕ) : ℝ))) := by ring
    · exact ⟨0, le_rfl, fun h => absurd h hm⟩
  choose Kf hKf using hmn
  set Ktot : ℝ := ∑ m ∈ Finset.range (l + 1), Kf m with hKtot
  have hKf0 : ∀ m, 0 ≤ Kf m := fun m => (hKf m).1
  have hKtot0 : 0 ≤ Ktot := Finset.sum_nonneg (fun m _ => hKf0 m)
  have hKtotb : ∀ m : ℕ, m ≤ l → ∀ (τ : ℍ), lowBadSet τ → ∀ x : ℝ, 0 ≤ x →
      ‖iteratedDeriv m (fun x : ℝ => PhiOne ℓ d τ x + PhiTwo ℓ d τ x + PhiSpike τ x) x‖
        ≤ Ktot * (1 + x) ^ (-N) := by
    intro m hm τ hτ x hx
    have hmem : m ∈ Finset.range (l + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hm)
    have h := (hKf m).2 hm τ hτ x hx
    have hle : Kf m ≤ Ktot := Finset.single_le_sum (fun i _ => hKf0 i) hmem
    have hpow : 0 ≤ (1 + x) ^ (-N) := Real.rpow_nonneg (by linarith) _
    exact le_trans h (mul_le_mul_of_nonneg_right hle hpow)
  refine ⟨Chp + c * Ktot, by positivity, fun τ r hτ => ?_⟩
  have hFdiff : ContDiffOn ℝ (l : ℕ∞)
      (fun x : ℝ => PhiOne ℓ d τ x + PhiTwo ℓ d τ x + PhiSpike τ x) (Set.Ioi (-1)) :=
    (contDiffOn_part ℓ d hd hCdec hdec1 hdec2 htail hτ).of_le le_top
  have hb := hcomp (fun x : ℝ => PhiOne ℓ d τ x + PhiTwo ℓ d τ x + PhiSpike τ x) Ktot hKtot0
    hFdiff (fun m hm x hx => hKtotb m hm τ hτ x hx) r
  have hhs : iteratedDeriv l (fun s : ℝ => lowF2 ℓ d τ s) r
      = iteratedDeriv l (fun s : ℝ =>
            (2 - 2 * Real.cos (Real.pi * s ^ 2) : ℂ)
              * (PhiOne ℓ d τ (s ^ 2) + PhiTwo ℓ d τ (s ^ 2) + PhiSpike τ (s ^ 2))) r
        + iteratedDeriv l (fun s : ℝ => highPart (Gcusp ℓ d) τ s) r := by
    rw [show (fun s : ℝ => lowF2 ℓ d τ s)
        = (fun s : ℝ => (2 - 2 * Real.cos (Real.pi * s ^ 2) : ℂ)
              * (PhiOne ℓ d τ (s ^ 2) + PhiTwo ℓ d τ (s ^ 2) + PhiSpike τ (s ^ 2)))
          + (fun s : ℝ => highPart (Gcusp ℓ d) τ s) from rfl]
    refine iteratedDeriv_add ?_ ?_
    · have hFn : ContDiffAt ℝ ω
          (fun x : ℝ => PhiOne ℓ d τ x + PhiTwo ℓ d τ x + PhiSpike τ x) (r ^ 2) :=
        (contDiffOn_part ℓ d hd hCdec hdec1 hdec2 htail hτ).contDiffAt
          (IsOpen.mem_nhds isOpen_Ioi (by rw [Set.mem_Ioi]; nlinarith [sq_nonneg r]))
      have hcomp2 : ContDiffAt ℝ ω (fun s : ℝ =>
          PhiOne ℓ d τ (s ^ 2) + PhiTwo ℓ d τ (s ^ 2) + PhiSpike τ (s ^ 2)) r := by
        have hpow : ContDiffAt ℝ ω (fun s : ℝ => s ^ 2) r := by fun_prop
        have hc := ContDiffAt.comp (f := fun s : ℝ => s ^ 2)
          (g := fun x : ℝ => PhiOne ℓ d τ x + PhiTwo ℓ d τ x + PhiSpike τ x) r hFn hpow
        exact hc
      have hcos : ContDiffAt ℝ ω (fun s : ℝ => (2 - 2 * Real.cos (Real.pi * s ^ 2) : ℂ)) r := by
        have h1 : (fun s : ℝ => (2 - 2 * Real.cos (Real.pi * s ^ 2) : ℂ))
            = fun s : ℝ => sinSq s := by
          funext s
          rw [sinSq_eq_two_sub_two_cos]
          push_cast
          ring
        rw [h1]
        exact contDiff_omega_sinSq.contDiffAt
      exact (hcos.mul hcomp2).of_le le_top
    · exact ((contDiff_omega_highPart (Gcusp ℓ d) τ).contDiffAt).of_le le_top
  rw [hhs]
  have h2 : (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => highPart (Gcusp ℓ d) τ s) r‖ ≤ Chp :=
    hhpb τ r hτ
  calc (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ =>
          (2 - 2 * Real.cos (Real.pi * s ^ 2) : ℂ)
            * (PhiOne ℓ d τ (s ^ 2) + PhiTwo ℓ d τ (s ^ 2) + PhiSpike τ (s ^ 2))) r
        + iteratedDeriv l (fun s : ℝ => highPart (Gcusp ℓ d) τ s) r‖
      ≤ (|r| ^ k) * (‖iteratedDeriv l (fun s : ℝ =>
            (2 - 2 * Real.cos (Real.pi * s ^ 2) : ℂ)
              * (PhiOne ℓ d τ (s ^ 2) + PhiTwo ℓ d τ (s ^ 2) + PhiSpike τ (s ^ 2))) r‖
          + ‖iteratedDeriv l (fun s : ℝ => highPart (Gcusp ℓ d) τ s) r‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
    _ = (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ =>
            (2 - 2 * Real.cos (Real.pi * s ^ 2) : ℂ)
              * (PhiOne ℓ d τ (s ^ 2) + PhiTwo ℓ d τ (s ^ 2) + PhiSpike τ (s ^ 2))) r‖
          + (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => highPart (Gcusp ℓ d) τ s) r‖ := by ring
    _ ≤ c * Ktot + Chp := by linarith
    _ = Chp + c * Ktot := by ring

/-! ## An adapter: the spike decomposition from the pointwise kernel bound -/

/-- `lowBadSet τ` gives `|Re τ| < 1` and `3/4 < |Re τ|`. -/
lemma lowBadSet_abs_re {τ : ℍ} (hτ : lowBadSet τ) : |τ.re| < 1 ∧ 3 / 4 < |τ.re| := by
  have h1 : |τ.re| < 1 := abs_lt.mpr ⟨hτ.1.1, hτ.1.2.1⟩
  have h2 : (3 : ℝ) / 4 < |τ.re| := by
    rcases hτ.2.2.2 with h | h
    · rw [abs_of_pos (by linarith : (0 : ℝ) < τ.re)]; exact h
    · rw [abs_of_neg (by linarith : τ.re < 0)]; linarith
  exact ⟨h1, h2⟩

/-- `‖tpole τ t‖ ≤ 1/(2 π lowRho)` as soon as the contour point keeps distance `≥ lowRho`
from the pole height `Im τ`. -/
lemma norm_tpole_le_of_sep_low {τ : ℍ} {t : ℝ} (h : lowRho ≤ |t - τ.im|) :
    ‖tpole τ t‖ ≤ 1 / (2 * Real.pi * lowRho) := by
  have hnum : ‖((tsign τ : ℂ) / (2 * Real.pi))‖ = 1 / (2 * Real.pi) := by
    rw [norm_div]
    have h1 : ‖(tsign τ : ℂ)‖ = 1 := by unfold tsign; split <;> norm_num
    rw [h1, norm_mul, Complex.norm_ofNat, Complex.norm_of_nonneg Real.pi_pos.le]
  have hden : ((t : ℂ) * Complex.I - ((τ : ℂ) - (tsign τ : ℂ))).im = t - τ.im := by
    simp only [Complex.sub_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, UpperHalfPlane.coe_im]
    ring
  have hge : |t - τ.im| ≤ ‖(t : ℂ) * Complex.I - ((τ : ℂ) - (tsign τ : ℂ))‖ := by
    have h1 := Complex.abs_im_le_norm ((t : ℂ) * Complex.I - ((τ : ℂ) - (tsign τ : ℂ)))
    rwa [hden] at h1
  have hpos : 0 < lowRho := lowRho_pos
  rw [tpole, norm_div, hnum]
  have hd : (0 : ℝ) < ‖(t : ℂ) * Complex.I - ((τ : ℂ) - (tsign τ : ℂ))‖ :=
    lt_of_lt_of_le (lt_of_lt_of_le hpos h) hge
  calc (1 / (2 * Real.pi)) / ‖(t : ℂ) * Complex.I - ((τ : ℂ) - (tsign τ : ℂ))‖
      ≤ (1 / (2 * Real.pi)) / lowRho :=
        div_le_div_of_nonneg_left (by positivity) hpos (le_trans h hge)
    _ = 1 / (2 * Real.pi * lowRho) := by rw [div_div]

/-- **Adapter**: a uniform pointwise bound for `K - tpole` on the closed region
`{|Re τ| < 1, 1/2 ≤ Im τ ≤ 2, 3/4 < |Re τ|}` yields the two clauses of `lowBad_spike_decomp`
(the second one by the triangle inequality, since `tpole` is bounded off the spike window). -/
lemma lowBad_spike_b_adapter (ℓ : LogLambdaData) (d : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ (τ : UpperHalfPlane) (t : ℝ), |τ.re| < 1 → (1 : ℝ) / 2 ≤ τ.im → τ.im ≤ 2 →
      3 / 4 < |τ.re| → 0 < t → t ≤ lowT →
      ‖Kaxis (Kfun ℓ d) τ t - tpole τ t‖ ≤ C) :
    ∃ C' : ℝ, 0 ≤ C' ∧
      (∀ (τ : ℍ), lowBadSet τ → ∀ t : ℝ, 0 < t → t ≤ lowT →
        ‖Kaxis (Kfun ℓ d) τ t - tpole τ t‖ ≤ C') ∧
      (∀ (τ : ℍ), lowBadSet τ → ∀ t : ℝ, 0 < t → t ≤ lowT → lowRho ≤ |t - τ.im| →
        ‖Kaxis (Kfun ℓ d) τ t‖ ≤ C') := by
  have hextra : (0 : ℝ) ≤ 1 / (2 * Real.pi * lowRho) := by
    rw [lowRho]; positivity
  refine ⟨C + 1 / (2 * Real.pi * lowRho), by linarith, ?_, ?_⟩
  · intro τ hτ t ht htT
    obtain ⟨h1, h2⟩ := lowBadSet_abs_re hτ
    have := h τ t h1 hτ.2.1 hτ.2.2.1 h2 ht htT
    linarith
  · intro τ hτ t ht htT hsep
    obtain ⟨h1, h2⟩ := lowBadSet_abs_re hτ
    have hK : ‖Kaxis (Kfun ℓ d) τ t - tpole τ t‖ ≤ C := h τ t h1 hτ.2.1 hτ.2.2.1 h2 ht htT
    have htp := norm_tpole_le_of_sep_low (τ := τ) (t := t) hsep
    have hsplit : ‖Kaxis (Kfun ℓ d) τ t‖
        ≤ ‖Kaxis (Kfun ℓ d) τ t - tpole τ t‖ + ‖tpole τ t‖ := by
      have h3 := norm_add_le (Kaxis (Kfun ℓ d) τ t - tpole τ t) (tpole τ t)
      simpa using h3
    linarith

/-! ## Evenness and smoothness of `lowF2` in the radial variable -/

lemma lowF2_neg (ℓ : LogLambdaData) (d : ℕ) (τ : ℍ) (r : ℝ) :
    lowF2 ℓ d τ (-r) = lowF2 ℓ d τ r := by
  simp only [lowF2, neg_sq, highPart]

lemma contDiff_lowF2 (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) {C : ℝ} (hC : 0 ≤ C)
    (hdec1 : ∀ (τ : ℍ), lowBadSet τ → ∀ t : ℝ, 0 < t → t ≤ lowT →
      ‖Kaxis (Kfun ℓ d) τ t - tpole τ t‖ ≤ C)
    (hdec2 : ∀ (τ : ℍ), lowBadSet τ → ∀ t : ℝ, 0 < t → t ≤ lowT → lowRho ≤ |t - τ.im| →
      ‖Kaxis (Kfun ℓ d) τ t‖ ≤ C)
    (htail : ∃ Ct Mt : ℝ, 0 < Ct ∧ 0 ≤ Mt ∧ ∀ (τ : ℍ), lowBadSet τ → ∀ t : ℝ, lowT ≤ t →
      ‖Kaxis (Kfun ℓ d) τ t - Aexp (Gcusp ℓ d) τ t‖
        ≤ Ct * (1 + t) ^ Mt * Real.exp (-(Real.pi * t)))
    {τ : ℍ} (hτ : lowBadSet τ) :
    ContDiff ℝ ω (fun r : ℝ => lowF2 ℓ d τ r) := by
  have hpart := contDiffOn_part ℓ d hd hC hdec1 hdec2 htail hτ
  have hcomp : ContDiff ℝ ω (fun r : ℝ =>
      PhiOne ℓ d τ (r ^ 2) + PhiTwo ℓ d τ (r ^ 2) + PhiSpike τ (r ^ 2)) := by
    have h := hpart.comp_contDiff (n := ω) (f := fun r : ℝ => r ^ 2) (by fun_prop)
      (fun r => by rw [Set.mem_Ioi]; nlinarith [sq_nonneg r])
    simpa [Function.comp_def] using h
  have hcos : ContDiff ℝ ω (fun r : ℝ => (2 - 2 * Real.cos (Real.pi * r ^ 2) : ℂ)) := by
    have h1 : (fun r : ℝ => (2 - 2 * Real.cos (Real.pi * r ^ 2) : ℂ)) = fun r : ℝ => sinSq r := by
      funext r
      rw [sinSq_eq_two_sub_two_cos]
      push_cast
      ring
    rw [h1]
    exact contDiff_omega_sinSq
  have hhigh : ContDiff ℝ ω (fun r : ℝ => highPart (Gcusp ℓ d) τ r) :=
    contDiff_omega_highPart (Gcusp ℓ d) τ
  simpa [lowF2] using (hcos.mul hcomp).add hhigh

/-! ## The target -/

theorem lowRegion_badLine (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∀ k l : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ : UpperHalfPlane) (r : ℝ),
      τ ∈ Work.Asymptotics.DomainD → (1 : ℝ) / 2 ≤ τ.im → τ.im ≤ 2 →
      (3 / 4 < τ.re ∨ τ.re < -(3 / 4)) →
      (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ =>
        Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) τ s) r‖ ≤ C := by
  -- the two inputs of the spike decomposition
  obtain ⟨Cks, hCks, hks⟩ := lowBad_kernel_spike_b ℓ d hd
  obtain ⟨Cdec, hCdec, hdec1, hdec2⟩ := lowBad_spike_b_adapter ℓ d hCks hks
  -- the tail bound `K - Aexp = O((1+t)^M e^{-πt})` on the bad-line region
  obtain ⟨Ct, Mt, hCt, hMt, htail⟩ := lowBad_Aexp_tail ℓ d hd
  -- agreement of the explicit layer `lowF2` with the paper's layer
  have hid : ∀ (τ : ℍ) (r : ℝ), lowBadSet τ →
      lowF2 ℓ d τ r = paperLayer (Gcusp ℓ d) ℓ d τ r := by
    intro τ r hτ
    exact lowF2_eq_paperLayer ℓ d hd Cdec hCdec hdec1 hdec2 τ r hτ
  -- the `r`-seminorm bound for `lowF2`
  have hsemi0 : ∀ k l : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ : ℍ) (r : ℝ), lowBadSet τ →
      (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => lowF2 ℓ d τ s) r‖ ≤ C := by
    intro k l
    refine lowBad_hsemi_of_bounds ℓ d hd hCdec hdec1 hdec2 ⟨Ct, Mt, hCt, hMt, htail⟩ ?_ ?_ k l
    · intro m N
      exact lowBad_PhiSpike_deriv ℓ d hd m N
    · intro m N
      exact lowBad_Phi12_deriv ℓ d hd Cdec hCdec hdec1 m N
  -- transport through the puncture at `r = 0`
  have hsemi : ∀ k l : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ : ℍ) (r : ℝ), lowBadSet τ →
      (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => layer (Gcusp ℓ d) ℓ d τ s) r‖ ≤ C := by
    intro k l
    obtain ⟨C₀, hC₀, hb₀⟩ := hsemi0 k l
    refine ⟨C₀, hC₀, ?_⟩
    intro τ r hτ
    rcases eq_or_ne r 0 with hr | hr
    · subst hr
      rcases Nat.eq_zero_or_pos l with hl | hl
      · subst hl
        have hz : layer (Gcusp ℓ d) ℓ d τ 0 = 0 := by rw [layer]; simp
        simp only [iteratedDeriv_zero, hz, norm_zero, mul_zero]
        exact hC₀
      · have hfun : (fun s : ℝ => layer (Gcusp ℓ d) ℓ d τ s)
            = fun s : ℝ => (if s = 0 then 0 else lowF2 ℓ d τ s) := by
          funext s
          rcases eq_or_ne s 0 with hs | hs
          · subst hs; rw [layer]; simp
          · rw [layer, if_neg hs, if_neg hs]
            exact (hid τ s hτ).symm
        rw [hfun, punctured_iteratedDeriv (lowF2_neg ℓ d τ)
          ((contDiff_lowF2 ℓ d hd hCdec hdec1 hdec2 ⟨Ct, Mt, hCt, hMt, htail⟩ hτ).differentiable
            (by simp)) l hl]
        exact hb₀ τ 0 hτ
    · have heq : (fun s : ℝ => layer (Gcusp ℓ d) ℓ d τ s)
          =ᶠ[𝓝 r] (fun s : ℝ => lowF2 ℓ d τ s) := by
        filter_upwards [isOpen_ne.mem_nhds hr] with s hs
        rw [layer, if_neg hs]
        exact (hid τ s hτ).symm
      rw [iteratedDeriv_congr_of_eventuallyEq heq l]
      exact hb₀ τ r hτ
  -- transfer to the contour integral
  intro k l
  obtain ⟨C, hC, hb⟩ := kernelTransform_seminorm_of_layer_on_compact ℓ d
    (layer (Gcusp ℓ d) ℓ d)
    (by
      intro τ hτ
      have h1 : layer (Gcusp ℓ d) ℓ d τ 0 = 0 := by rw [layer]; simp
      have h2 : kernelTransform (Kfun ℓ d) τ 0 = 0 := by simp [kernelTransform]
      rw [h1, h2])
    (by
      intro τ hτ r hr hInt
      rw [layer, if_neg hr]
      have hsub : ({τ} : Set ℍ) ⊆ DomainD := by rintro x rfl; exact hτ.1
      have hcpt : IsCompact ({τ} : Set ℍ) := isCompact_singleton
      refine Work.Asymptotics.Compact.local_agreement (K := ({τ} : Set ℍ)) ℓ d hd
        (Gcusp ℓ d) (fun i j => Gcusp_moderate ℓ d i j) ?_
        (Work.Asymptotics.MFix.Kaxis_local_flat ℓ d hd hcpt hsub)
        (Work.HFN.cusp_expansion_of_kernel ℓ d hd hcpt hsub) τ r (by simp) hr hInt
      intro h8 j
      rw [Gcusp, if_pos h8]
      funext x
      fin_cases j <;> simp [Gcusp8])
    hsemi k l
  exact ⟨C, hC, fun τ r hD him1 him2 hre => hb τ r ⟨hD, him1, him2, hre⟩⟩

end Work.HFN.HalfFunnel
