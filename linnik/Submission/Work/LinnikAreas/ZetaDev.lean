import Mathlib
import Submission.Work.LinnikAreas.ZetaPrincipalDefs
import Submission.Work.LinnikAreas.Kernel
import Submission.Commons.NumberTheory.Zeta.xiE_partialFraction_eq
import Submission.Commons.NumberTheory.Zeta.xi_logDeriv_re_lower_general
import Submission.Commons.Analysis.Complex.exterior_jensen_multiplicity

open DirichletCharacter Complex Filter Metric
open scoped BigOperators Classical Topology
noncomputable section
set_option linter.style.haveILetI false

namespace Work.LinnikAreas

/-- Multiplicity of `u` as a non-trivial zero of the completed Riemann zeta `Λ`, computed through
the classical entire completion `Ξ(s) = 1/2 + (1/2) s (s-1) Λ₀(s)` (whose zeros are exactly the
non-trivial zeros of `ζ`, with the same multiplicities). -/
def zetaMult (u : ℂ) : ℕ := analyticOrderNatAt Commons.NumberTheory.Zeta.XiPF.xiF u

/-- The `zeroMult` of the trivial character is the analytic vanishing order of the completed
Riemann zeta function. -/
lemma zetaDev_zeroMult_one_eq (q : ℕ) [NeZero q] (ρ : ℂ) :
    Work.LinnikContract.zeroMult (1 : DirichletCharacter ℂ q) ρ =
      analyticOrderNatAt completedRiemannZeta ρ := by
  rw [Work.LinnikContract.zeroMult, DirichletCharacter.primitiveCharacter_one]
  congr 1
  haveI : NeZero (DirichletCharacter.conductor (1 : DirichletCharacter ℂ q)) :=
    ⟨(1 : DirichletCharacter ℂ q).conductor_ne_zero⟩
  have key : ∀ (N : ℕ) [NeZero N], N = 1 →
      completedLFunction (1 : DirichletCharacter ℂ N) = completedRiemannZeta := by
    intro N _ hN
    subst hN
    exact DirichletCharacter.completedLFunction_modOne_eq
  exact key _ (DirichletCharacter.conductor_one)

/-- The tent kernel at the origin is `K²`. -/
lemma tentK_zero (L K : ℝ) : Commons.NumberTheory.Linnik.tentK L K 0 = (K : ℂ) ^ 2 := by
  simp [Commons.NumberTheory.Linnik.tentK, Commons.NumberTheory.Linnik.tentH_zero]

/-- High-frequency (`‖u‖ ≥ 2`) part of the inverse-square kernel bound on the closed critical
strip `Re u ≤ 1`. -/
theorem norm_Hk_strip_high (q : ℕ) (hq : 2 ≤ q) {u : ℂ} (hu : u.re ≤ 1) (h2 : 2 ≤ ‖u‖) :
    ‖Work.LinnikContract.Hk (11/2) (3/10) ((1 - u) * (Real.log (q : ℝ) : ℂ))‖
      ≤ (20 / (Real.log (q : ℝ))^2) * (1 / (1 + ‖u‖^2)) := by
  have hL : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < q))
  have hK : (0:ℝ) < 3/10 := by norm_num
  set z : ℂ := (1 - u) * (Real.log (q : ℝ) : ℂ) with hzdef
  have hzre : 0 ≤ z.re := by
    rw [hzdef, Complex.mul_re]
    simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_im, mul_zero, sub_zero]
    exact mul_nonneg (by linarith) hL.le
  have hexp1 : Real.exp (-((11:ℝ)/2 - 2*(3/10)) * z.re) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith [hzre]
  have h1 := Work.LinnikAreas.norm_Hk_le_inv_sq (L := 11/2) (K := 3/10) hK hzre
  have hzfac : ‖z‖ = Real.log (q : ℝ) * ‖u - 1‖ := by
    rw [hzdef, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL, norm_sub_rev (1:ℂ) u]
    ring
  have htri : ‖u‖ ≤ ‖u - 1‖ + 1 := by
    have h := norm_add_le (u - 1) (1 : ℂ)
    rw [sub_add_cancel] at h; simpa using h
  have hstep : ‖Work.LinnikContract.Hk (11/2) (3/10) z‖ ≤ 4 / ‖z‖^2 := by
    calc ‖Work.LinnikContract.Hk (11/2) (3/10) z‖
        ≤ Real.exp (-((11:ℝ)/2 - 2*(3/10)) * z.re) * (4 / ‖z‖^2) := h1
      _ ≤ 1 * (4 / ‖z‖^2) := mul_le_mul_of_nonneg_right hexp1 (by positivity)
      _ = 4 / ‖z‖^2 := one_mul _
  have hun : ‖u‖ ≤ 2 * ‖u - 1‖ := by linarith
  have hs : (‖u‖/2)^2 ≤ ‖u-1‖^2 := by
    have h0 : (0:ℝ) ≤ ‖u‖/2 := by positivity
    have h1' : ‖u‖/2 ≤ ‖u-1‖ := by linarith
    exact pow_le_pow_left₀ h0 h1' 2
  have h4 : (4:ℝ) ≤ ‖u‖^2 := by nlinarith
  have hfin : 4 / ‖z‖^2 ≤ (20 / (Real.log (q : ℝ))^2) * (1 / (1 + ‖u‖^2)) := by
    have hz2 : ‖z‖^2 = (Real.log (q : ℝ))^2 * ‖u - 1‖^2 := by rw [hzfac, mul_pow]
    have hden : (Real.log (q : ℝ))^2 * (‖u‖/2)^2 ≤ (Real.log (q : ℝ))^2 * ‖u-1‖^2 :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    rw [hz2]
    refine (div_le_div_of_nonneg_left (by norm_num) (by positivity) hden).trans ?_
    have hsimp : 4 / ((Real.log (q : ℝ))^2 * (‖u‖/2)^2)
        = 16 / ((Real.log (q : ℝ))^2 * ‖u‖^2) := by
      field_simp; ring
    rw [hsimp]
    rw [div_le_iff₀ (by positivity)]
    have hsimp2 : (20 / (Real.log (q : ℝ))^2) * (1 / (1 + ‖u‖^2))
        * ((Real.log (q : ℝ))^2 * ‖u‖^2) = 20 * ‖u‖^2 / (1 + ‖u‖^2) := by
      field_simp
    rw [hsimp2, le_div_iff₀ (by positivity)]
    nlinarith [h4]
  rw [hzdef] at hstep
  linarith [hstep, hfin]

/-- Low-frequency (`‖u‖ ≤ 2`) part of the kernel bound on the closed critical strip. -/
theorem norm_Hk_strip_low (q : ℕ) (hq : 2 ≤ q) {u : ℂ} (hu : u.re ≤ 1) (h2 : ‖u‖ ≤ 2) :
    ‖Work.LinnikContract.Hk (11/2) (3/10) ((1 - u) * (Real.log (q : ℝ) : ℂ))‖
      ≤ (5 * ((3:ℝ)/10)^2) * (1 / (1 + ‖u‖^2)) := by
  have hL : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < q))
  have hK : (0:ℝ) < 3/10 := by norm_num
  set z : ℂ := (1 - u) * (Real.log (q : ℝ) : ℂ) with hzdef
  have hzre : 0 ≤ z.re := by
    rw [hzdef, Complex.mul_re]
    simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_im, mul_zero, sub_zero]
    exact mul_nonneg (by linarith) hL.le
  have hexp1 : Real.exp (-((11:ℝ)/2 - 2*(3/10)) * z.re) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith [hzre]
  have h1 := Work.LinnikAreas.norm_Hk_le_sq (L := 11/2) (K := 3/10) hK hzre
  have h2' : ‖Work.LinnikContract.Hk (11/2) (3/10) z‖ ≤ ((3:ℝ)/10)^2 := by
    calc ‖Work.LinnikContract.Hk (11/2) (3/10) z‖
        ≤ Real.exp (-((11:ℝ)/2 - 2*(3/10)) * z.re) * ((3:ℝ)/10)^2 := h1
      _ ≤ 1 * ((3:ℝ)/10)^2 := mul_le_mul_of_nonneg_right hexp1 (by norm_num)
      _ = ((3:ℝ)/10)^2 := one_mul _
  have hw : (1:ℝ) ≤ 5 * (1/(1+‖u‖^2)) := by
    have he : (5:ℝ) * (1/(1+‖u‖^2)) = 5/(1+‖u‖^2) := by ring
    rw [he, le_div_iff₀ (by positivity)]
    nlinarith [norm_nonneg u, h2]
  rw [hzdef] at h2'
  calc ‖Work.LinnikContract.Hk (11/2) (3/10) ((1 - u) * (Real.log (q : ℝ) : ℂ))‖
      ≤ ((3:ℝ)/10)^2 := h2'
    _ = ((3:ℝ)/10)^2 * 1 := by ring
    _ ≤ ((3:ℝ)/10)^2 * (5 * (1/(1+‖u‖^2))) := mul_le_mul_of_nonneg_left hw (by norm_num)
    _ = (5 * ((3:ℝ)/10)^2) * (1/(1+‖u‖^2)) := by ring

/-- Kernel bound on the closed critical strip `Re u ≤ 1`, in the form needed to dominate the
zero summands by the inverse-square weight. -/
theorem norm_Hk_strip_bound (q : ℕ) (hq : 2 ≤ q) {u : ℂ} (hu : u.re ≤ 1) :
    ‖Work.LinnikContract.Hk (11/2) (3/10) ((1 - u) * (Real.log (q : ℝ) : ℂ))‖
      ≤ max (5 * ((3:ℝ)/10)^2) (20 / (Real.log (q : ℝ))^2) * (1 / (1 + ‖u‖^2)) := by
  by_cases h2 : ‖u‖ ≤ 2
  · exact (norm_Hk_strip_low q hq hu h2).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  · push_neg at h2
    exact (norm_Hk_strip_high q hq hu (le_of_lt h2)).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))

/-- The kernel at the point `log q`: `‖Hk (11/2) (3/10) (log q)‖ ≤ 100 q^{-49/10}` for `q ≥ 2`. -/
theorem norm_Hk_logq_le (q : ℕ) (hq : 2 ≤ q) :
    ‖Work.LinnikContract.Hk (11/2) (3/10) ((Real.log (q : ℝ) : ℂ))‖
      ≤ 100 * (q : ℝ) ^ (-(49:ℝ)/10) := by
  have hq1 : (1:ℝ) < (q:ℝ) := by exact_mod_cast (by omega : 1 < q)
  have hL : 0 < Real.log (q:ℝ) := Real.log_pos hq1
  have hK : (0:ℝ) < 3/10 := by norm_num
  have hnorm : ‖((Real.log (q:ℝ) : ℂ))‖ = Real.log (q:ℝ) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL]
  rw [Work.LinnikContract.Hk, norm_mul]
  have hF2 : ‖Work.LinnikContract.F2 (3/10) ((Real.log (q:ℝ) : ℂ))‖ ≤ 4/(Real.log (q:ℝ))^2 := by
    have h := Work.LinnikAreas.norm_F2_le_inv_sq (K := 3/10) hK (z := ((Real.log (q:ℝ) : ℂ)))
      (by simp only [Complex.ofReal_re]; exact hL.le)
    rw [hnorm] at h
    exact h
  have hexp : ‖Complex.exp (-(((11:ℝ)/2 - 2*(3/10) : ℝ) : ℂ) * ((Real.log (q:ℝ) : ℂ)))‖
      = (q : ℝ) ^ (-(49:ℝ)/10) := by
    rw [Complex.norm_exp]
    have hre : (-(((11:ℝ)/2 - 2*(3/10) : ℝ) : ℂ) * ((Real.log (q:ℝ) : ℂ))).re
        = -((49:ℝ)/10) * Real.log (q:ℝ) := by
      rw [Complex.mul_re]
      simp only [Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      norm_num
    rw [hre, Real.rpow_def_of_pos (x := (q:ℝ)) (by exact_mod_cast (by omega : 0 < q)) (-(49:ℝ)/10)]
    congr 1
    ring
  have hfour : 4 / (Real.log (q:ℝ))^2 ≤ 100 := by
    have hlog2 : (1:ℝ)/2 ≤ Real.log (q : ℝ) :=
      le_trans (le_of_lt (lt_trans (by norm_num) Real.log_two_gt_d9))
        (Real.log_le_log (by norm_num) (by exact_mod_cast hq))
    rw [div_le_iff₀ (by positivity)]
    have hsq : (1:ℝ)/4 ≤ (Real.log (q : ℝ))^2 := by
      have hh := mul_le_mul hlog2 hlog2 (by norm_num) (by linarith)
      have h14 : (1:ℝ)/4 = (1/2)*(1/2) := by norm_num
      rw [h14, pow_two]
      exact hh
    nlinarith [hsq]
  calc ‖Complex.exp (-(((11:ℝ)/2 - 2*(3/10) : ℝ) : ℂ) * ((Real.log (q:ℝ) : ℂ)))‖
        * ‖Work.LinnikContract.F2 (3/10) ((Real.log (q:ℝ) : ℂ))‖
      ≤ (q : ℝ) ^ (-(49:ℝ)/10) * (4 / (Real.log (q:ℝ))^2) := by
        rw [hexp]; exact mul_le_mul_of_nonneg_left hF2 (by positivity)
    _ ≤ (q : ℝ) ^ (-(49:ℝ)/10) * 100 :=
        mul_le_mul_of_nonneg_left hfour (by positivity)
    _ = 100 * (q : ℝ) ^ (-(49:ℝ)/10) := by ring

end Work.LinnikAreas

namespace Work.LinnikAreas

/-- Heath-Brown's kernel `Hk (11/2) (3/10)` evaluated at `(1-u)·log q`. -/
abbrev zetaHk (q : ℕ) (u : ℂ) : ℂ :=
  Work.LinnikContract.Hk (11/2) (3/10) ((1 - u) * (Real.log (q : ℝ) : ℂ))

/-- Heath-Brown's tent kernel `tentK (11/2) (3/10)` evaluated at `(1-u)·log q`. -/
abbrev zetaTent (q : ℕ) (u : ℂ) : ℂ :=
  Commons.NumberTheory.Linnik.tentK (11/2) (3/10) ((1 - u) * (Real.log (q : ℝ) : ℂ))

end Work.LinnikAreas

namespace Work.LinnikAreas

/-- The completed Riemann zeta function is meromorphic on the whole plane. -/
lemma meromorphicOn_completedRiemannZeta : MeromorphicOn completedRiemannZeta Set.univ := by
  intro x _
  set C : ℂ → ℂ := fun s => completedRiemannZeta₀ s - s⁻¹ - (1 - s)⁻¹ with hC
  have h0 : MeromorphicAt completedRiemannZeta₀ x :=
    (differentiable_completedZeta₀.analyticAt x).meromorphicAt
  have h1 : MeromorphicAt (fun s : ℂ => s⁻¹) x := (MeromorphicAt.id x).inv
  have h2 : MeromorphicAt (fun s : ℂ => (1 - s)⁻¹) x :=
    ((MeromorphicAt.const (1:ℂ) x).sub (MeromorphicAt.id x)).inv
  have h3 : MeromorphicAt C x := by
    rw [hC]; exact (h0.sub h1).sub h2
  refine h3.congr ?_
  filter_upwards with s
  show completedRiemannZeta₀ s - s⁻¹ - (1 - s)⁻¹ = completedRiemannZeta s
  rw [completedRiemannZeta_eq, one_div, one_div]

/-- `completedRiemannZeta` has a simple pole at `0`. -/
lemma meromorphicOrderAt_completedRiemannZeta_zero :
    meromorphicOrderAt completedRiemannZeta 0 = (-1 : ℤ) := by
  have hf : MeromorphicAt completedRiemannZeta 0 :=
    meromorphicOn_completedRiemannZeta 0 (Set.mem_univ _)
  rw [meromorphicOrderAt_eq_int_iff hf]
  refine ⟨fun s => s * (completedRiemannZeta₀ s - (1 - s)⁻¹) - 1, ?_, ?_, ?_⟩
  · have hξ : AnalyticAt ℂ completedRiemannZeta₀ 0 := differentiable_completedZeta₀.analyticAt 0
    have hid : AnalyticAt ℂ (fun s : ℂ => s) 0 := analyticAt_id
    have hone : AnalyticAt ℂ (fun s : ℂ => 1 - s) 0 := analyticAt_const.sub hid
    have hinv : AnalyticAt ℂ (fun s : ℂ => (1 - s)⁻¹) 0 := hone.inv (by norm_num)
    have hc1 : AnalyticAt ℂ (fun _ : ℂ => (1:ℂ)) 0 := analyticAt_const
    have hprod : AnalyticAt ℂ (fun s : ℂ => s * (completedRiemannZeta₀ s - (1 - s)⁻¹)) 0 :=
      hid.mul (hξ.sub hinv)
    refine (analyticAt_congr ?_).mp (hprod.sub hc1)
    filter_upwards with s
    simp [Pi.sub_apply]
  · norm_num
  · filter_upwards [self_mem_nhdsWithin] with z hz
    have hz0 : z ≠ 0 := hz
    rw [sub_zero, zpow_neg_one, smul_eq_mul, completedRiemannZeta_eq, one_div, one_div]
    field_simp
    ring

/-- `completedRiemannZeta` has a simple pole at `1`. -/
lemma meromorphicOrderAt_completedRiemannZeta_one :
    meromorphicOrderAt completedRiemannZeta 1 = (-1 : ℤ) := by
  have hf : MeromorphicAt completedRiemannZeta 1 :=
    meromorphicOn_completedRiemannZeta 1 (Set.mem_univ _)
  rw [meromorphicOrderAt_eq_int_iff hf]
  refine ⟨fun s => (s - 1) * (completedRiemannZeta₀ s - s⁻¹) + 1, ?_, ?_, ?_⟩
  · have hξ : AnalyticAt ℂ completedRiemannZeta₀ 1 := differentiable_completedZeta₀.analyticAt 1
    have hid : AnalyticAt ℂ (fun s : ℂ => s) 1 := analyticAt_id
    have hinv : AnalyticAt ℂ (fun s : ℂ => s⁻¹) 1 := hid.inv (by norm_num)
    have hc1 : AnalyticAt ℂ (fun _ : ℂ => (1:ℂ)) 1 := analyticAt_const
    have hlin : AnalyticAt ℂ (fun s : ℂ => s - 1) 1 := hid.sub hc1
    have hprod : AnalyticAt ℂ (fun s : ℂ => (s - 1) * (completedRiemannZeta₀ s - s⁻¹)) 1 :=
      hlin.mul (hξ.sub hinv)
    refine (analyticAt_congr ?_).mp (hprod.add hc1)
    filter_upwards with s
    simp [Pi.add_apply]
  · norm_num
  · filter_upwards [self_mem_nhdsWithin] with z hz
    have hz1 : z - 1 ≠ 0 := sub_ne_zero.mpr hz
    rw [zpow_neg_one, smul_eq_mul, completedRiemannZeta_eq, one_div, one_div]
    have step : (z - 1)⁻¹ * ((z - 1) * (completedRiemannZeta₀ z - z⁻¹) + 1)
        = (completedRiemannZeta₀ z - z⁻¹) + (z - 1)⁻¹ := by
      rw [mul_add, mul_one, ← mul_assoc, inv_mul_cancel₀ hz1, one_mul]
    rw [step]
    have hneg : -(1 - z)⁻¹ = (z - 1)⁻¹ := by
      have : (1 - z) = -(z - 1) := by ring
      rw [this, inv_neg, neg_neg]
    rw [← hneg]
    ring

/-- The divisor of `completedRiemannZeta` on the whole plane at `0` is `-1`. -/
lemma divisor_univ_completedRiemannZeta_zero :
    MeromorphicOn.divisor completedRiemannZeta Set.univ 0 = (-1 : ℤ) := by
  rw [MeromorphicOn.divisor_apply meromorphicOn_completedRiemannZeta (Set.mem_univ 0),
    meromorphicOrderAt_completedRiemannZeta_zero]
  rfl

/-- The divisor of `completedRiemannZeta` on the whole plane at `1` is `-1`. -/
lemma divisor_univ_completedRiemannZeta_one :
    MeromorphicOn.divisor completedRiemannZeta Set.univ 1 = (-1 : ℤ) := by
  rw [MeromorphicOn.divisor_apply meromorphicOn_completedRiemannZeta (Set.mem_univ 1),
    meromorphicOrderAt_completedRiemannZeta_one]
  rfl

end Work.LinnikAreas

namespace Work.LinnikAreas

/-- The full divisor sum of the completed Riemann zeta function against Heath-Brown's tent
kernel, i.e. the integrand of `zetaBallSum` in the limit. -/
abbrev zetaA (q : ℕ) : ℂ → ℂ :=
  fun u => ((MeromorphicOn.divisor completedRiemannZeta Set.univ u : ℤ) : ℂ) * zetaTent q u

/-- The zero-multiplicity weighted sum against Heath-Brown's kernel `Hk`. -/
abbrev zetaB (q : ℕ) : ℂ → ℂ := fun u => (zetaMult u : ℂ) * zetaHk q u

end Work.LinnikAreas

namespace Work.LinnikAreas

@[simp] theorem zetaA_apply (q : ℕ) (u : ℂ) :
    zetaA q u = ((MeromorphicOn.divisor completedRiemannZeta Set.univ u : ℤ) : ℂ) * zetaTent q u := rfl

@[simp] theorem zetaB_apply (q : ℕ) (u : ℂ) :
    zetaB q u = (zetaMult u : ℂ) * zetaHk q u := rfl

end Work.LinnikAreas

namespace Work.LinnikAreas

@[simp] theorem zetaHk_apply (q : ℕ) (u : ℂ) :
    zetaHk q u = Work.LinnikContract.Hk (11/2) (3/10) ((1 - u) * (Real.log (q : ℝ) : ℂ)) := rfl

@[simp] theorem zetaTent_apply (q : ℕ) (u : ℂ) :
    zetaTent q u = Commons.NumberTheory.Linnik.tentK (11/2) (3/10) ((1 - u) * (Real.log (q : ℝ) : ℂ)) := rfl

end Work.LinnikAreas
