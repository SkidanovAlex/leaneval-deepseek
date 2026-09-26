/-
# The "pre-declash" form of the half-funnel kernel bounds

This file proves `Work.Asymptotics.HalfFunnel.funnelPreDeclash`: the pair of raw estimates on
the CKMRV kernel `Kaxis (Kfun ℓ d) τ t` that the half-funnel `r`-seminorm assembly needs,
namely

* the polynomial/exponential bound of `Work.Asymptotics.funnelKernelPre` in the window
  `1 ≤ t ≤ Im τ - 1` (below the pole), and
* the two-pole ("spike") decomposition of `Work.Asymptotics.funnelKernelSpike` in the window
  `Im τ - 1 ≤ t ≤ Im τ + 1`.

## Why the two estimates are not simply imported

`Work.Asymptotics.funnelKernelPre` rests on the compact bounds `KPlus_axis_compact` and
`KMinus_axis_compact`, whose modules import `Submission.Work.Asymptotics.KernelBoundAux`;
`Work.Asymptotics.funnelKernelSpike` rests on the `SpikeCircle`/`MiddleRange` machinery, whose
modules import `Submission.Work.Asymptotics.MiddleRange.Basic`.  Those two modules both declare
`Work.Asymptotics.continuous_scale`, so no Lean module can import both worlds, and the two
papers' estimates cannot be combined by importing them side by side.

The resolution taken here is to *reprove* the first estimate inside the second environment.
The only declarations of `KernelBoundAux` used by
`Submission/Work/Asymptotics/KPlus_axis_compact.lean` and
`Submission/Work/Asymptotics/KMinus_axis_compact.lean` are the two trivial facts
`(imagAxis t ht).im = t` and `scale (imagAxis t ht) = 1 + t⁻¹ + t`, which are reproved below as
`Work.Asymptotics.fpdImagAxis_im` and `Work.Asymptotics.fpdScale_imagAxis` (given that
distinctive names so that they cannot collide with a future shared helper).  Everything else of the
first estimate is copied from the four modules

* `Submission/Work/Asymptotics/KPlus_axis_compact.lean`,
* `Submission/Work/Asymptotics/KMinus_axis_compact.lean`,
* `Submission/Work/Residues/KMinus_axis_bound.lean`,
* `Submission/Work/Asymptotics/funnelKernelPre.lean`

verbatim (their proofs, which are complete), with only those two facts replaced.
-/

import Mathlib
import Submission.Work.Asymptotics.KPlusAxisAtoms
import Submission.Work.Asymptotics.DomainD
import Submission.Work.Kernels.Kernels
import Submission.Work.Kernels.KernelGrowth
import Submission.Work.Kernels.LogLambdaInstance
import Submission.Work.Kernels.ClearLink.KPlusClear_eq_smul
import Submission.Work.Asymptotics.KClear_mg2
import Submission.Work.Asymptotics.jInvariantFun_eq_smul_of_eq
import Submission.Work.Asymptotics.differentiableAt_Kfun_tau
import Submission.Work.Asymptotics.MiddleRange.Classify
import Submission.Work.Residues.KMinusCuspDefs
import Submission.Work.Kernels.ClearLink.KMinusClear_eq_smul
import Submission.Work.Asymptotics.DeltaFun_imagAxis_lower_sharp
import Submission.Work.Asymptotics.DeltaFun_upper_sharp
import Submission.Work.Asymptotics.E4Fun_upper_half
import Submission.Work.Residues.bracket8_axis_bound
import Submission.Work.Residues.bracket24_axis_bound
import Submission.Work.Residues.kpre_inv_axis_bound
import Submission.Work.Asymptotics.funnelTailBasic
import Submission.Work.Asymptotics.KPlusXiDefs
import Submission.Work.Asymptotics.Compact.kminus_bracket
import Submission.Work.Asymptotics.funnelTailQuant
import Submission.Work.Residues.ThetaDecay
import Submission.Work.Kernels.TildeFacts.KPlus_z_tildeA
import Submission.Work.Asymptotics.funnelKernelSpike
namespace Work.Asymptotics

/-! ## The two trivial facts of `KernelBoundAux` used by the compact bounds -/

/-- The imaginary part of the point `it` of the imaginary axis. -/
lemma fpdImagAxis_im (t : ℝ) (ht : 0 < t) : (Work.Kernels.imagAxis t ht).im = t := by
  show ((t : ℂ) * Complex.I).im = t
  simp

/-- `‖it‖ = t` for `t > 0`. -/
lemma fpdNorm_imagAxis (t : ℝ) (ht : 0 < t) :
    ‖((Work.Kernels.imagAxis t ht : UpperHalfPlane) : ℂ)‖ = t := by
  show ‖(t : ℂ) * Complex.I‖ = t
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]

/-- The scale of the point `it` of the imaginary axis is `1 + t⁻¹ + t`. -/
lemma fpdScale_imagAxis (t : ℝ) (ht : 0 < t) :
    Work.Kernels.scale (Work.Kernels.imagAxis t ht) = 1 + t⁻¹ + t := by
  have h1 : (Work.Kernels.imagAxis t ht).im = t := fpdImagAxis_im t ht
  have h2 : ‖((Work.Kernels.imagAxis t ht : UpperHalfPlane) : ℂ)‖ = t := fpdNorm_imagAxis t ht
  simp only [Work.Kernels.scale, h1, h2]

end Work.Asymptotics

/-! ### Copy of `Submission/Work/Asymptotics/KPlus_axis_compact.lean` -/

/-
# Boundedness of `K_+` on the axis over the compact funnel

`Work.Asymptotics.KPlus_axis_compact`: for `d ∈ {8,24}`, `τ ∈ 𝒟` with `2 ≤ Im τ ≤ H` and
`1 ≤ t ≤ Im τ - 1`, the kernel `K_+^{(d)}(τ, it)` is bounded by a constant depending only on
`d` and `H`.

The proof does not need any analysis of the explicit entries of the coefficient matrix `Υ_+`:
off the coincidence set `j(τ) = j(z)` the *cleared* kernel `K_+^{clear}` of Theorem 4.9(4) is
`growthPrefactor · K_+` (`Work.Kernels.ClearLink.KPlusClear_eq_smul`), and

* `K_+^{clear} = K^{clear} + K̂^{clear}` is polynomially bounded on `ℍ × ℍ`
  (`Work.Asymptotics.KClear_mg2`),
* the divisor `growthPrefactor d τ z = Δ(τ)Δ(z)^e (j(τ) - j(z))` is *bounded away from zero*
  on the compact box `{|Re τ| ≤ 1, 2 ≤ Im τ ≤ H, 1 ≤ Im z ≤ Im τ - 1, Re z = 0}`, because
  `Δ` never vanishes and `j(τ) ≠ j(z)` there: if `j(τ) = j(it)` then `τ` is `SL(2,ℤ)`-conjugate
  to `it`, and an explicit computation with `(γ • it).im = t / (d² + (ct)²)` (where `γ = (∗ ∗; c d)`)
  gives `Im τ ≤ t`, contradicting `t ≤ Im τ - 1`.
-/

set_option maxHeartbeats 1000000

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology

namespace Work.Asymptotics

open Work.Kernels

/-! ## The imaginary part of `γ • (it)` -/

/-- For `t ≥ 1` and `γ ∈ SL(2,ℤ)`, the point `γ • (it)` has imaginary part at most `t`.  Indeed
`(γ • (it)).im = t / (d² + (ct)²)` with `γ = (∗ ∗; c d)` and `ad - bc = 1`, and the denominator is
at least `1`. -/
private lemma im_smul_imagAxis_le (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) {t : ℝ}
    (ht0 : 0 < t) (ht : 1 ≤ t) : (γ • Work.Kernels.imagAxis t ht0).im ≤ t := by
  rw [ModularGroup.im_smul_eq_div_normSq]
  rw [show (Work.Kernels.imagAxis t ht0).im = t from Work.Asymptotics.fpdImagAxis_im t ht0]
  refine div_le_self (by linarith) ?_
  have hden : UpperHalfPlane.denom
      (SpecialLinearGroup.toGL ((SpecialLinearGroup.map (Int.castRingHom ℝ)) γ))
      ((Work.Kernels.imagAxis t ht0 : ℍ) : ℂ)
      = ((γ 1 1 : ℤ) : ℂ) + (((γ 1 0 : ℤ) : ℂ) * t) * Complex.I := by
    rw [ModularGroup.denom_apply,
      show ((Work.Kernels.imagAxis t ht0 : ℍ) : ℂ) = (t : ℂ) * Complex.I from rfl]
    ring
  have hns : Complex.normSq (((γ 1 1 : ℤ) : ℂ) + (((γ 1 0 : ℤ) : ℂ) * t) * Complex.I)
      = ((γ 1 1 : ℤ) : ℝ)^2 + (((γ 1 0 : ℤ) : ℝ) * t)^2 := by
    rw [Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.intCast_re,
      Complex.intCast_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  rw [hden, hns]
  have hdetZ : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have hh := γ.2; rw [Matrix.det_fin_two] at hh; exact hh
  rcases eq_or_ne (γ 1 0) 0 with hc0 | hc0
  · have h2' : (((γ 1 0 : ℤ) : ℝ) * t)^2 = 0 := by rw [hc0]; ring
    rw [h2', add_zero]
    have hd0 : γ 1 1 ≠ 0 := by
      intro h
      rw [hc0, h] at hdetZ
      norm_num at hdetZ
    have h1 : (1:ℤ) ≤ (γ 1 1)^2 := by
      have h2 : (1:ℤ) ≤ |γ 1 1| := Int.one_le_abs hd0
      have h3 : |γ 1 1|^2 = (γ 1 1)^2 := by rw [sq_abs]
      nlinarith [h2, sq_nonneg (|γ 1 1|)]
    exact_mod_cast h1
  · have h1 : (1:ℤ) ≤ (γ 1 0)^2 := by
      have h2 : (1:ℤ) ≤ |γ 1 0| := Int.one_le_abs hc0
      have h3 : |γ 1 0|^2 = (γ 1 0)^2 := by rw [sq_abs]
      nlinarith [h2, sq_nonneg (|γ 1 0|)]
    have h1' : (1:ℝ) ≤ ((γ 1 0 : ℤ) : ℝ)^2 := by exact_mod_cast h1
    have ht2 : (1:ℝ) ≤ t^2 := by nlinarith
    have hmul : (1:ℝ) ≤ (((γ 1 0 : ℤ) : ℝ)^2) * t^2 := by
      calc (1:ℝ) = 1 * 1 := by ring
        _ ≤ _ := mul_le_mul h1' ht2 (by norm_num) (by positivity)
    have heq : (((γ 1 0 : ℤ) : ℝ) * t)^2 = (((γ 1 0 : ℤ) : ℝ)^2) * t^2 := by ring
    have hd2 : (0:ℝ) ≤ ((γ 1 1 : ℤ) : ℝ)^2 := sq_nonneg _
    rw [heq]
    linarith

/-! ## The compact parameter box -/

/-- The compact box of parameters: `|Re τ| ≤ 1`, `2 ≤ Im τ ≤ H`, `1 ≤ Im z ≤ Im τ - 1` and
`Re z = 0`.  It contains the parameter set of `KMinus_axis_compact`. -/
private def Bx (H : ℝ) : Set (ℍ × ℍ) :=
  {p | |p.1.re| ≤ 1} ∩ {p | 2 ≤ p.1.im} ∩ {p | p.1.im ≤ H} ∩ {p | 1 ≤ p.2.im}
    ∩ {p | p.2.im ≤ p.1.im - 1} ∩ {p | ((p.2 : ℂ)).re = 0}

private lemma mem_Bx {H : ℝ} {p : ℍ × ℍ} :
    p ∈ Bx H ↔ |p.1.re| ≤ 1 ∧ 2 ≤ p.1.im ∧ p.1.im ≤ H ∧ 1 ≤ p.2.im ∧
      p.2.im ≤ p.1.im - 1 ∧ ((p.2 : ℂ)).re = 0 := by
  simp only [Bx, Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩, f⟩; exact ⟨a, b, c, d, e, f⟩
  · rintro ⟨a, b, c, d, e, f⟩; exact ⟨⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩, f⟩

private lemma isClosed_Bx (H : ℝ) : IsClosed (Bx H) := by
  have h1 : IsClosed {p : ℍ × ℍ | |p.1.re| ≤ 1} :=
    isClosed_le ((UpperHalfPlane.continuous_re.comp continuous_fst).abs) continuous_const
  have h2 : IsClosed {p : ℍ × ℍ | 2 ≤ p.1.im} :=
    isClosed_le continuous_const (UpperHalfPlane.continuous_im.comp continuous_fst)
  have h3 : IsClosed {p : ℍ × ℍ | p.1.im ≤ H} :=
    isClosed_le (UpperHalfPlane.continuous_im.comp continuous_fst) continuous_const
  have h4 : IsClosed {p : ℍ × ℍ | 1 ≤ p.2.im} :=
    isClosed_le continuous_const (UpperHalfPlane.continuous_im.comp continuous_snd)
  have h5 : IsClosed {p : ℍ × ℍ | p.2.im ≤ p.1.im - 1} :=
    isClosed_le (UpperHalfPlane.continuous_im.comp continuous_snd)
      ((UpperHalfPlane.continuous_im.comp continuous_fst).sub continuous_const)
  have h6 : IsClosed {p : ℍ × ℍ | ((p.2 : ℂ)).re = 0} :=
    isClosed_eq (Complex.continuous_re.comp (UpperHalfPlane.continuous_coe.comp continuous_snd))
      continuous_const
  unfold Bx
  exact ((((h1.inter h2).inter h3).inter h4).inter h5).inter h6

private lemma isCompact_Bx {H : ℝ} (hH : 2 ≤ H) : IsCompact (Bx H) := by
  have hH0 : (0:ℝ) < H := by linarith
  set τ₀ : ℍ := ⟨(H : ℂ) * Complex.I, by
    have h : ((H : ℂ) * Complex.I).im = H := by simp
    rw [h]; exact hH0⟩ with hτ₀def
  set z₀ : ℍ := ⟨((H / 2 : ℝ) : ℂ) * Complex.I, by
    have h : (((H / 2 : ℝ) : ℂ) * Complex.I).im = H / 2 := by simp
    rw [h]; linarith⟩ with hz₀def
  have hτ₀im : τ₀.im = H := by simp [τ₀]
  have hz₀im : z₀.im = H / 2 := by simp [z₀]
  have hτ₀coe : ((τ₀ : ℍ) : ℂ) = (H : ℂ) * Complex.I := rfl
  have hz₀coe : ((z₀ : ℍ) : ℂ) = ((H / 2 : ℝ) : ℂ) * Complex.I := rfl
  refine IsCompact.of_isClosed_subset
    ((isCompact_closedBall τ₀ (H + 1)).prod (isCompact_closedBall z₀ (H / 2 + 1)))
    (isClosed_Bx H) ?_
  rintro p hp
  rw [Set.mem_prod]
  rw [mem_Bx] at hp
  obtain ⟨hre, him2, himH, hz1, hle, hzre⟩ := hp
  have hzre0 : p.2.re = 0 := by rw [← UpperHalfPlane.coe_re]; exact hzre
  constructor
  · rw [Metric.mem_closedBall]
    have hsqrt : (1:ℝ) ≤ Real.sqrt (p.1.im * τ₀.im) := by
      rw [hτ₀im, Real.one_le_sqrt]; nlinarith
    refine le_trans (UpperHalfPlane.dist_le_dist_coe_div_sqrt p.1 τ₀) ?_
    refine le_trans (div_le_self (by positivity) hsqrt) ?_
    have hsq : dist (p.1 : ℂ) (τ₀ : ℂ) ^ 2 = p.1.re ^ 2 + (p.1.im - H) ^ 2 := by
      rw [dist_eq_norm, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hτ₀coe]
      simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
        sub_zero, add_zero, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
      ring
    have hre2 : p.1.re ^ 2 ≤ 1 := by
      have := abs_le.mp hre
      nlinarith [this.1, this.2]
    have habs : |p.1.im - H| ≤ H - 2 := by
      rw [abs_le]; exact ⟨by linarith, by linarith⟩
    have him2' : (p.1.im - H) ^ 2 ≤ (H - 2) ^ 2 := by
      nlinarith [sq_abs (p.1.im - H), abs_nonneg (p.1.im - H), habs]
    have hfin : dist (p.1 : ℂ) (τ₀ : ℂ) ^ 2 ≤ (H + 1) ^ 2 := by
      rw [hsq]; nlinarith
    have hnn := dist_nonneg (x := (p.1 : ℂ)) (y := (τ₀ : ℂ))
    nlinarith [sq_nonneg (H + 1)]
  · rw [Metric.mem_closedBall]
    have hsqrt : (1:ℝ) ≤ Real.sqrt (p.2.im * z₀.im) := by
      rw [hz₀im, Real.one_le_sqrt]; nlinarith
    refine le_trans (UpperHalfPlane.dist_le_dist_coe_div_sqrt p.2 z₀) ?_
    refine le_trans (div_le_self (by positivity) hsqrt) ?_
    have hsq : dist (p.2 : ℂ) (z₀ : ℂ) ^ 2 = p.2.re ^ 2 + (p.2.im - H/2) ^ 2 := by
      rw [dist_eq_norm, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hz₀coe]
      simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
        sub_zero, add_zero, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
      ring
    have habs : |p.2.im - H/2| ≤ H/2 := by
      rw [abs_le]; exact ⟨by linarith, by linarith⟩
    have hfin : dist (p.2 : ℂ) (z₀ : ℂ) ^ 2 ≤ (H/2 + 1) ^ 2 := by
      rw [hsq, hzre0]
      nlinarith [sq_abs (p.2.im - H/2), abs_nonneg (p.2.im - H/2), sq_nonneg (H/2), habs]
    have hnn := dist_nonneg (x := (p.2 : ℂ)) (y := (z₀ : ℂ))
    nlinarith [sq_nonneg (H/2 + 1)]

/-! ## No coincidence in the box -/

/-- On the box, `j(τ) ≠ j(z)`: if `j(τ) = j(it)` then `τ = γ • (it)`, whence
`Im τ ≤ t ≤ Im τ - 1`. -/
private lemma jInvariantFun_ne_of_mem_Bx {H : ℝ} {p : ℍ × ℍ} (hp : p ∈ Bx H) :
    Work.Kernels.jInvariantFun p.1 ≠ Work.Kernels.jInvariantFun p.2 := by
  rw [mem_Bx] at hp
  obtain ⟨hre, him2, himH, hz1, hle, hzre⟩ := hp
  intro h
  have hz : p.2 = Work.Kernels.imagAxis p.2.im p.2.im_pos :=
    eq_imagAxis_of_re_eq_zero hzre
  rw [hz] at h
  obtain ⟨γ, hγ⟩ := jInvariantFun_eq_smul_of_eq h
  have him := im_smul_imagAxis_le γ p.2.im_pos hz1
  rw [hγ] at him
  linarith

/-! ## The divisor is bounded away from zero on the box -/

/-- `p ↦ growthPrefactor d p.1 p.2` is continuous. -/
private lemma continuous_growthPrefactor_pair (d : ℕ) :
    Continuous (fun p : ℍ × ℍ => Work.Kernels.growthPrefactor d p.1 p.2) := by
  have hE4 : Continuous fun τ : ℍ => Work.Kernels.E4Fun τ :=
    Work.Kernels.ClassicalFacts.E4Fun_mem_InP.1.continuous
  have hD : Continuous fun τ : ℍ => Work.Kernels.DeltaFun τ :=
    Work.Kernels.ClassicalFacts.DeltaFun_mem_InP.1.continuous
  have hjf : Continuous fun τ : ℍ => Work.Kernels.jInvariantFun τ := by
    have h : (fun τ : ℍ => Work.Kernels.jInvariantFun τ) =
        fun τ => Work.Kernels.E4Fun τ ^ 3 / Work.Kernels.DeltaFun τ := rfl
    rw [h]
    exact (hE4.pow 3).div hD (fun τ => Work.Kernels.ClassicalFacts.DeltaFun_ne_zero τ)
  have h1 : Continuous fun p : ℍ × ℍ => Work.Kernels.DeltaFun p.1 := hD.comp continuous_fst
  have h2 : Continuous fun p : ℍ × ℍ => Work.Kernels.DeltaFun p.2 := hD.comp continuous_snd
  have h3 : Continuous fun p : ℍ × ℍ => Work.Kernels.jInvariantFun p.1 := hjf.comp continuous_fst
  have h4 : Continuous fun p : ℍ × ℍ => Work.Kernels.jInvariantFun p.2 := hjf.comp continuous_snd
  simp only [Work.Kernels.growthPrefactor]
  exact ((h1.mul (h2.pow _)).mul (h3.sub h4))

/-- The box is nonempty (for `H ≥ 2`): the pair `(2i, i)`. -/
private lemma nonempty_Bx {H : ℝ} (hH : 2 ≤ H) : (Bx H).Nonempty := by
  refine ⟨((⟨(2 : ℂ) * Complex.I, by simp⟩ : ℍ),
    Work.Kernels.imagAxis 1 (by norm_num)), ?_⟩
  rw [mem_Bx]
  have h1im : ((⟨(2 : ℂ) * Complex.I, by simp⟩ : ℍ)).im = 2 := by simp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp
  · rw [h1im]
  · rw [h1im]; linarith
  · rw [Work.Asymptotics.fpdImagAxis_im]
  · rw [Work.Asymptotics.fpdImagAxis_im, h1im]; norm_num
  · show ((1 : ℂ) * Complex.I).re = 0
    simp

/-- `growthPrefactor` is bounded below by a positive constant on the compact box. -/
private lemma exists_lower_growthPrefactor (d : ℕ) (H : ℝ) (hH : 2 ≤ H) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ p ∈ Bx H, δ ≤ ‖Work.Kernels.growthPrefactor d p.1 p.2‖ := by
  obtain ⟨p₀, hp₀mem, hp₀min⟩ := (isCompact_Bx hH).exists_isMinOn (nonempty_Bx hH)
    ((continuous_growthPrefactor_pair d).norm).continuousOn
  refine ⟨‖Work.Kernels.growthPrefactor d p₀.1 p₀.2‖,
    norm_pos_iff.mpr (growthPrefactor_ne_zero d (jInvariantFun_ne_of_mem_Bx hp₀mem)),
    fun p hp => hp₀min hp⟩

/-! ## Bounding the scale on the funnel and on the axis -/

private lemma scale_le_of_funnel {H : ℝ} {τ : ℍ} (hre : |τ.re| ≤ 1) (him2 : 2 ≤ τ.im)
    (himH : τ.im ≤ H) :
    Work.Kernels.scale τ ≤ 1 + (1 / 2 : ℝ) + Real.sqrt (1 + H ^ 2) := by
  have h1 : (τ.im)⁻¹ ≤ (1 / 2 : ℝ) := by
    have h := one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 2) him2
    simpa [one_div] using h
  have hsq : ‖(τ : ℂ)‖ ^ 2 ≤ 1 + H ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    have hre2 : τ.re ^ 2 ≤ 1 := by
      have := abs_le.mp hre; nlinarith [this.1, this.2]
    have him2' : τ.im ^ 2 ≤ H ^ 2 := by nlinarith [τ.im_pos]
    nlinarith
  have h2 : ‖(τ : ℂ)‖ ≤ Real.sqrt (1 + H ^ 2) := by
    calc ‖(τ : ℂ)‖ = Real.sqrt (‖(τ : ℂ)‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt (1 + H ^ 2) := Real.sqrt_le_sqrt hsq
  have hdef : Work.Kernels.scale τ = 1 + (τ.im)⁻¹ + ‖(τ : ℂ)‖ := rfl
  rw [hdef]; linarith
/-! ## The scale of the contour point on the axis -/

/-- For `1 ≤ t ≤ H - 1` the scale of the contour point `it` is at most `H + 1`. -/
private lemma scale_cti_le {H t : ℝ} (ht : 1 ≤ t) (htH : t ≤ H - 1) :
    Work.Kernels.scale (Work.Asymptotics.cti t) ≤ H + 1 := by
  have ht0 : 0 < t := by linarith
  rw [Work.Asymptotics.cti_eq_imagAxis ht0, Work.Asymptotics.fpdScale_imagAxis t ht0]
  have h : (t)⁻¹ ≤ 1 := by
    have h2 := one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 1) ht
    simpa [one_div] using h2
  linarith

/-! ## The main theorem -/

theorem KPlus_axis_compact (d : ℕ) (hd : d = 8 ∨ d = 24) (H : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (τ : UpperHalfPlane) (t : ℝ),
      τ ∈ Work.Asymptotics.DomainD → 2 ≤ τ.im → τ.im ≤ H → 1 ≤ t → t ≤ τ.im - 1 →
      ‖Work.Kernels.KPlus d τ (Work.Asymptotics.cti t)‖ ≤ C := by
  rcases lt_or_ge H 2 with hH | hH
  · -- the parameter set is empty
    refine ⟨1, one_pos, fun τ t hD him2 himH h1 h2 => ?_⟩
    exfalso
    linarith
  · obtain ⟨δ, hδpos, hδ⟩ := exists_lower_growthPrefactor d H hH
    obtain ⟨αf, Nf, Mf, hαf, hNf, hMf, hbf⟩ := (KClear_mg2 Work.Kernels.logLambda d hd).1
    obtain ⟨αh, Nh, Mh, hαh, hNh, hMh, hbh⟩ := (KClear_mg2 Work.Kernels.logLambda d hd).2
    refine ⟨max 1 ((αf * (1 + (1 / 2 : ℝ) + Real.sqrt (1 + H ^ 2)) ^ Nf * (H + 1) ^ Mf +
      αh * (1 + (1 / 2 : ℝ) + Real.sqrt (1 + H ^ 2)) ^ Nh * (H + 1) ^ Mh) / δ),
      lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
    intro τ t hD him2 himH h1 h2
    have ht0 : 0 < t := by linarith
    have hreτ : |τ.re| ≤ 1 := by
      have h := (mem_DomainD.mp hD)
      rw [abs_le]; exact ⟨by linarith [h.1], by linarith [h.2.1]⟩
    have hzre : ((Work.Asymptotics.cti t : ℍ) : ℂ).re = 0 := by
      rw [Work.Asymptotics.cti_coe ht0]; simp
    have hzim : (Work.Asymptotics.cti t).im = t := Work.Asymptotics.cti_im ht0
    have htH : t ≤ H - 1 := by linarith
    have hpmem : (τ, Work.Asymptotics.cti t) ∈ Bx H := by
      rw [mem_Bx]
      exact ⟨hreτ, him2, himH, by rw [hzim]; exact h1, by rw [hzim]; exact h2, hzre⟩
    have hJ := jInvariantFun_ne_of_mem_Bx hpmem
    have hgpne : Work.Kernels.growthPrefactor d τ (Work.Asymptotics.cti t) ≠ 0 :=
      growthPrefactor_ne_zero d hJ
    have hgpnorm : ‖Work.Kernels.growthPrefactor d τ (Work.Asymptotics.cti t)‖ ≠ 0 :=
      norm_ne_zero_iff.mpr hgpne
    -- the cleared kernel and its value
    have hclear : Work.Kernels.KPlusClear d τ (Work.Asymptotics.cti t)
        = Work.Kernels.growthPrefactor d τ (Work.Asymptotics.cti t)
          * Work.Kernels.KPlus d τ (Work.Asymptotics.cti t) :=
      Work.Kernels.ClearLink.KPlusClear_eq_smul d hd τ _ hJ
    have hsplit : Work.Kernels.KPlusClear d τ (Work.Asymptotics.cti t)
        = Work.Kernels.KfunClear Work.Kernels.logLambda d τ (Work.Asymptotics.cti t)
          + Work.Kernels.KhatClear Work.Kernels.logLambda d τ (Work.Asymptotics.cti t) := by
      simp only [Work.Kernels.KfunClear, Work.Kernels.KhatClear]
      ring
    -- the norm identity
    have hnorm : ‖Work.Kernels.KPlus d τ (Work.Asymptotics.cti t)‖
        = ‖Work.Kernels.KPlusClear d τ (Work.Asymptotics.cti t)‖
          / ‖Work.Kernels.growthPrefactor d τ (Work.Asymptotics.cti t)‖ := by
      have h1' : ‖Work.Kernels.KPlusClear d τ (Work.Asymptotics.cti t)‖
          = ‖Work.Kernels.growthPrefactor d τ (Work.Asymptotics.cti t)‖
            * ‖Work.Kernels.KPlus d τ (Work.Asymptotics.cti t)‖ := by
        rw [hclear, norm_mul]
      rw [h1', mul_div_cancel_left₀ _ hgpnorm]
    -- the scale bounds
    have hsτ : Work.Kernels.scale τ ≤ 1 + (1 / 2 : ℝ) + Real.sqrt (1 + H ^ 2) :=
      scale_le_of_funnel hreτ him2 himH
    have hsz : Work.Kernels.scale (Work.Asymptotics.cti t) ≤ H + 1 := scale_cti_le h1 htH
    have hsτ1 : (1:ℝ) ≤ Work.Kernels.scale τ := Work.Kernels.one_le_scale τ
    have hsz1 : (1:ℝ) ≤ Work.Kernels.scale (Work.Asymptotics.cti t) :=
      Work.Kernels.one_le_scale _
    have hpowτ : (Work.Kernels.scale τ) ^ Nf ≤ (1 + (1 / 2 : ℝ) + Real.sqrt (1 + H ^ 2)) ^ Nf :=
      Real.rpow_le_rpow (le_trans zero_le_one hsτ1) hsτ hNf
    have hpowz : (Work.Kernels.scale (Work.Asymptotics.cti t)) ^ Mf ≤ (H + 1) ^ Mf :=
      Real.rpow_le_rpow (le_trans zero_le_one hsz1) hsz hMf
    have hpowτ' : (Work.Kernels.scale τ) ^ Nh ≤ (1 + (1 / 2 : ℝ) + Real.sqrt (1 + H ^ 2)) ^ Nh :=
      Real.rpow_le_rpow (le_trans zero_le_one hsτ1) hsτ hNh
    have hpowz' : (Work.Kernels.scale (Work.Asymptotics.cti t)) ^ Mh ≤ (H + 1) ^ Mh :=
      Real.rpow_le_rpow (le_trans zero_le_one hsz1) hsz hMh
    have hbound_f : ‖Work.Kernels.KfunClear Work.Kernels.logLambda d τ (Work.Asymptotics.cti t)‖
        ≤ αf * (1 + (1 / 2 : ℝ) + Real.sqrt (1 + H ^ 2)) ^ Nf * (H + 1) ^ Mf := by
      refine le_trans (hbf τ _) ?_
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left hpowτ hαf) hpowz (Real.rpow_nonneg (by positivity) _)
        (by positivity)
    have hbound_h : ‖Work.Kernels.KhatClear Work.Kernels.logLambda d τ (Work.Asymptotics.cti t)‖
        ≤ αh * (1 + (1 / 2 : ℝ) + Real.sqrt (1 + H ^ 2)) ^ Nh * (H + 1) ^ Mh := by
      refine le_trans (hbh τ _) ?_
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left hpowτ' hαh) hpowz' (Real.rpow_nonneg (by positivity) _)
        (by positivity)
    have hbound : ‖Work.Kernels.KPlusClear d τ (Work.Asymptotics.cti t)‖
        ≤ αf * (1 + (1 / 2 : ℝ) + Real.sqrt (1 + H ^ 2)) ^ Nf * (H + 1) ^ Mf +
          αh * (1 + (1 / 2 : ℝ) + Real.sqrt (1 + H ^ 2)) ^ Nh * (H + 1) ^ Mh := by
      rw [hsplit]
      exact le_trans (norm_add_le _ _) (add_le_add hbound_f hbound_h)
    have hδ' : δ ≤ ‖Work.Kernels.growthPrefactor d τ (Work.Asymptotics.cti t)‖ :=
      hδ ⟨τ, Work.Asymptotics.cti t⟩ hpmem
    have hA_nonneg : 0 ≤ αf * (1 + (1 / 2 : ℝ) + Real.sqrt (1 + H ^ 2)) ^ Nf * (H + 1) ^ Mf +
        αh * (1 + (1 / 2 : ℝ) + Real.sqrt (1 + H ^ 2)) ^ Nh * (H + 1) ^ Mh := by
      refine add_nonneg (mul_nonneg (mul_nonneg hαf ?_)
        (Real.rpow_nonneg (by linarith) _)) (mul_nonneg (mul_nonneg hαh ?_)
        (Real.rpow_nonneg (by linarith) _)) <;> exact Real.rpow_nonneg (by positivity) _
    rw [hnorm]
    refine le_trans (le_trans (div_le_div_of_nonneg_right hbound (norm_nonneg _))
      (div_le_div_of_nonneg_left hA_nonneg hδpos hδ')) (le_max_right _ _)

end Work.Asymptotics

/-! ### Copy of `Submission/Work/Asymptotics/KMinus_axis_compact.lean` -/

/-
# Boundedness of `K_-` on the axis over the compact funnel

`Work.Asymptotics.KMinus_axis_compact`: for `d ∈ {8,24}`, `τ ∈ 𝒟` with `2 ≤ Im τ ≤ H` and
`1 ≤ t ≤ Im τ - 1`, the kernel `K_-^{(d)}(τ, it)` is bounded by a constant depending only on
`ℓ`, `d` and `H`.

The proof does not need any analysis of the explicit entries of the coefficient matrix `Υ_-`:
off the coincidence set `j(τ) = j(z)` the *cleared* kernel `K_-^{clear}` of Theorem 4.9(4) is
`growthPrefactor · K_-` (`Work.Kernels.ClearLink.KMinusClear_eq_smul`), and

* `K_-^{clear} = K^{clear} - K̂^{clear}` is polynomially bounded on `ℍ × ℍ`
  (`Work.Asymptotics.KClear_mg2`),
* the divisor `growthPrefactor d τ z = Δ(τ)Δ(z)^e (j(τ) - j(z))` is *bounded away from zero*
  on the compact box `{|Re τ| ≤ 1, 2 ≤ Im τ ≤ H, 1 ≤ Im z ≤ Im τ - 1, Re z = 0}`, because
  `Δ` never vanishes and `j(τ) ≠ j(z)` there: if `j(τ) = j(it)` then `τ` is `SL(2,ℤ)`-conjugate
  to `it`, and an explicit computation with `(γ • it).im = t / (d² + (ct)²)` (where `γ = (∗ ∗; c d)`)
  gives `Im τ ≤ t`, contradicting `t ≤ Im τ - 1`.
-/

set_option maxHeartbeats 1000000

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology

namespace Work.Asymptotics

open Work.Kernels

/-! ## The imaginary part of `γ • (it)` -/

/-- For `t ≥ 1` and `γ ∈ SL(2,ℤ)`, the point `γ • (it)` has imaginary part at most `t`.  Indeed
`(γ • (it)).im = t / (d² + (ct)²)` with `γ = (∗ ∗; c d)` and `ad - bc = 1`, and the denominator is
at least `1`. -/
private lemma im_smul_imagAxis_leM (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) {t : ℝ}
    (ht0 : 0 < t) (ht : 1 ≤ t) : (γ • Work.Kernels.imagAxis t ht0).im ≤ t := by
  rw [ModularGroup.im_smul_eq_div_normSq]
  rw [show (Work.Kernels.imagAxis t ht0).im = t from Work.Asymptotics.fpdImagAxis_im t ht0]
  refine div_le_self (by linarith) ?_
  have hden : UpperHalfPlane.denom
      (SpecialLinearGroup.toGL ((SpecialLinearGroup.map (Int.castRingHom ℝ)) γ))
      ((Work.Kernels.imagAxis t ht0 : ℍ) : ℂ)
      = ((γ 1 1 : ℤ) : ℂ) + (((γ 1 0 : ℤ) : ℂ) * t) * Complex.I := by
    rw [ModularGroup.denom_apply,
      show ((Work.Kernels.imagAxis t ht0 : ℍ) : ℂ) = (t : ℂ) * Complex.I from rfl]
    ring
  have hns : Complex.normSq (((γ 1 1 : ℤ) : ℂ) + (((γ 1 0 : ℤ) : ℂ) * t) * Complex.I)
      = ((γ 1 1 : ℤ) : ℝ)^2 + (((γ 1 0 : ℤ) : ℝ) * t)^2 := by
    rw [Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.intCast_re,
      Complex.intCast_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  rw [hden, hns]
  have hdetZ : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have hh := γ.2; rw [Matrix.det_fin_two] at hh; exact hh
  rcases eq_or_ne (γ 1 0) 0 with hc0 | hc0
  · have h2' : (((γ 1 0 : ℤ) : ℝ) * t)^2 = 0 := by rw [hc0]; ring
    rw [h2', add_zero]
    have hd0 : γ 1 1 ≠ 0 := by
      intro h
      rw [hc0, h] at hdetZ
      norm_num at hdetZ
    have h1 : (1:ℤ) ≤ (γ 1 1)^2 := by
      have h2 : (1:ℤ) ≤ |γ 1 1| := Int.one_le_abs hd0
      have h3 : |γ 1 1|^2 = (γ 1 1)^2 := by rw [sq_abs]
      nlinarith [h2, sq_nonneg (|γ 1 1|)]
    exact_mod_cast h1
  · have h1 : (1:ℤ) ≤ (γ 1 0)^2 := by
      have h2 : (1:ℤ) ≤ |γ 1 0| := Int.one_le_abs hc0
      have h3 : |γ 1 0|^2 = (γ 1 0)^2 := by rw [sq_abs]
      nlinarith [h2, sq_nonneg (|γ 1 0|)]
    have h1' : (1:ℝ) ≤ ((γ 1 0 : ℤ) : ℝ)^2 := by exact_mod_cast h1
    have ht2 : (1:ℝ) ≤ t^2 := by nlinarith
    have hmul : (1:ℝ) ≤ (((γ 1 0 : ℤ) : ℝ)^2) * t^2 := by
      calc (1:ℝ) = 1 * 1 := by ring
        _ ≤ _ := mul_le_mul h1' ht2 (by norm_num) (by positivity)
    have heq : (((γ 1 0 : ℤ) : ℝ) * t)^2 = (((γ 1 0 : ℤ) : ℝ)^2) * t^2 := by ring
    have hd2 : (0:ℝ) ≤ ((γ 1 1 : ℤ) : ℝ)^2 := sq_nonneg _
    rw [heq]
    linarith

/-! ## The compact parameter box -/

/-- The compact box of parameters: `|Re τ| ≤ 1`, `2 ≤ Im τ ≤ H`, `1 ≤ Im z ≤ Im τ - 1` and
`Re z = 0`.  It contains the parameter set of `KMinus_axis_compact`. -/
private def BxM (H : ℝ) : Set (ℍ × ℍ) :=
  {p | |p.1.re| ≤ 1} ∩ {p | 2 ≤ p.1.im} ∩ {p | p.1.im ≤ H} ∩ {p | 1 ≤ p.2.im}
    ∩ {p | p.2.im ≤ p.1.im - 1} ∩ {p | ((p.2 : ℂ)).re = 0}

private lemma mem_BxM {H : ℝ} {p : ℍ × ℍ} :
    p ∈ BxM H ↔ |p.1.re| ≤ 1 ∧ 2 ≤ p.1.im ∧ p.1.im ≤ H ∧ 1 ≤ p.2.im ∧
      p.2.im ≤ p.1.im - 1 ∧ ((p.2 : ℂ)).re = 0 := by
  simp only [BxM, Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩, f⟩; exact ⟨a, b, c, d, e, f⟩
  · rintro ⟨a, b, c, d, e, f⟩; exact ⟨⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩, f⟩

private lemma isClosed_BxM (H : ℝ) : IsClosed (BxM H) := by
  have h1 : IsClosed {p : ℍ × ℍ | |p.1.re| ≤ 1} :=
    isClosed_le ((UpperHalfPlane.continuous_re.comp continuous_fst).abs) continuous_const
  have h2 : IsClosed {p : ℍ × ℍ | 2 ≤ p.1.im} :=
    isClosed_le continuous_const (UpperHalfPlane.continuous_im.comp continuous_fst)
  have h3 : IsClosed {p : ℍ × ℍ | p.1.im ≤ H} :=
    isClosed_le (UpperHalfPlane.continuous_im.comp continuous_fst) continuous_const
  have h4 : IsClosed {p : ℍ × ℍ | 1 ≤ p.2.im} :=
    isClosed_le continuous_const (UpperHalfPlane.continuous_im.comp continuous_snd)
  have h5 : IsClosed {p : ℍ × ℍ | p.2.im ≤ p.1.im - 1} :=
    isClosed_le (UpperHalfPlane.continuous_im.comp continuous_snd)
      ((UpperHalfPlane.continuous_im.comp continuous_fst).sub continuous_const)
  have h6 : IsClosed {p : ℍ × ℍ | ((p.2 : ℂ)).re = 0} :=
    isClosed_eq (Complex.continuous_re.comp (UpperHalfPlane.continuous_coe.comp continuous_snd))
      continuous_const
  unfold BxM
  exact ((((h1.inter h2).inter h3).inter h4).inter h5).inter h6

private lemma isCompact_BxM {H : ℝ} (hH : 2 ≤ H) : IsCompact (BxM H) := by
  have hH0 : (0:ℝ) < H := by linarith
  set τ₀ : ℍ := ⟨(H : ℂ) * Complex.I, by
    have h : ((H : ℂ) * Complex.I).im = H := by simp
    rw [h]; exact hH0⟩ with hτ₀def
  set z₀ : ℍ := ⟨((H / 2 : ℝ) : ℂ) * Complex.I, by
    have h : (((H / 2 : ℝ) : ℂ) * Complex.I).im = H / 2 := by simp
    rw [h]; linarith⟩ with hz₀def
  have hτ₀im : τ₀.im = H := by simp [τ₀]
  have hz₀im : z₀.im = H / 2 := by simp [z₀]
  have hτ₀coe : ((τ₀ : ℍ) : ℂ) = (H : ℂ) * Complex.I := rfl
  have hz₀coe : ((z₀ : ℍ) : ℂ) = ((H / 2 : ℝ) : ℂ) * Complex.I := rfl
  refine IsCompact.of_isClosed_subset
    ((isCompact_closedBall τ₀ (H + 1)).prod (isCompact_closedBall z₀ (H / 2 + 1)))
    (isClosed_BxM H) ?_
  rintro p hp
  rw [Set.mem_prod]
  rw [mem_BxM] at hp
  obtain ⟨hre, him2, himH, hz1, hle, hzre⟩ := hp
  have hzre0 : p.2.re = 0 := by rw [← UpperHalfPlane.coe_re]; exact hzre
  constructor
  · rw [Metric.mem_closedBall]
    have hsqrt : (1:ℝ) ≤ Real.sqrt (p.1.im * τ₀.im) := by
      rw [hτ₀im, Real.one_le_sqrt]; nlinarith
    refine le_trans (UpperHalfPlane.dist_le_dist_coe_div_sqrt p.1 τ₀) ?_
    refine le_trans (div_le_self (by positivity) hsqrt) ?_
    have hsq : dist (p.1 : ℂ) (τ₀ : ℂ) ^ 2 = p.1.re ^ 2 + (p.1.im - H) ^ 2 := by
      rw [dist_eq_norm, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hτ₀coe]
      simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
        sub_zero, add_zero, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
      ring
    have hre2 : p.1.re ^ 2 ≤ 1 := by
      have := abs_le.mp hre
      nlinarith [this.1, this.2]
    have habs : |p.1.im - H| ≤ H - 2 := by
      rw [abs_le]; exact ⟨by linarith, by linarith⟩
    have him2' : (p.1.im - H) ^ 2 ≤ (H - 2) ^ 2 := by
      nlinarith [sq_abs (p.1.im - H), abs_nonneg (p.1.im - H), habs]
    have hfin : dist (p.1 : ℂ) (τ₀ : ℂ) ^ 2 ≤ (H + 1) ^ 2 := by
      rw [hsq]; nlinarith
    have hnn := dist_nonneg (x := (p.1 : ℂ)) (y := (τ₀ : ℂ))
    nlinarith [sq_nonneg (H + 1)]
  · rw [Metric.mem_closedBall]
    have hsqrt : (1:ℝ) ≤ Real.sqrt (p.2.im * z₀.im) := by
      rw [hz₀im, Real.one_le_sqrt]; nlinarith
    refine le_trans (UpperHalfPlane.dist_le_dist_coe_div_sqrt p.2 z₀) ?_
    refine le_trans (div_le_self (by positivity) hsqrt) ?_
    have hsq : dist (p.2 : ℂ) (z₀ : ℂ) ^ 2 = p.2.re ^ 2 + (p.2.im - H/2) ^ 2 := by
      rw [dist_eq_norm, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hz₀coe]
      simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
        sub_zero, add_zero, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
      ring
    have habs : |p.2.im - H/2| ≤ H/2 := by
      rw [abs_le]; exact ⟨by linarith, by linarith⟩
    have hfin : dist (p.2 : ℂ) (z₀ : ℂ) ^ 2 ≤ (H/2 + 1) ^ 2 := by
      rw [hsq, hzre0]
      nlinarith [sq_abs (p.2.im - H/2), abs_nonneg (p.2.im - H/2), sq_nonneg (H/2), habs]
    have hnn := dist_nonneg (x := (p.2 : ℂ)) (y := (z₀ : ℂ))
    nlinarith [sq_nonneg (H/2 + 1)]

/-! ## No coincidence in the box -/

/-- On the box, `j(τ) ≠ j(z)`: if `j(τ) = j(it)` then `τ = γ • (it)`, whence
`Im τ ≤ t ≤ Im τ - 1`. -/
private lemma jInvariantFun_ne_of_mem_BxM {H : ℝ} {p : ℍ × ℍ} (hp : p ∈ BxM H) :
    Work.Kernels.jInvariantFun p.1 ≠ Work.Kernels.jInvariantFun p.2 := by
  rw [mem_BxM] at hp
  obtain ⟨hre, him2, himH, hz1, hle, hzre⟩ := hp
  intro h
  have hz : p.2 = Work.Kernels.imagAxis p.2.im p.2.im_pos :=
    eq_imagAxis_of_re_eq_zero hzre
  rw [hz] at h
  obtain ⟨γ, hγ⟩ := jInvariantFun_eq_smul_of_eq h
  have him := im_smul_imagAxis_leM γ p.2.im_pos hz1
  rw [hγ] at him
  linarith

/-! ## The divisor is bounded away from zero on the box -/

/-- `p ↦ growthPrefactor d p.1 p.2` is continuous. -/
private lemma continuous_growthPrefactor_pairM (d : ℕ) :
    Continuous (fun p : ℍ × ℍ => Work.Kernels.growthPrefactor d p.1 p.2) := by
  have hE4 : Continuous fun τ : ℍ => Work.Kernels.E4Fun τ :=
    Work.Kernels.ClassicalFacts.E4Fun_mem_InP.1.continuous
  have hD : Continuous fun τ : ℍ => Work.Kernels.DeltaFun τ :=
    Work.Kernels.ClassicalFacts.DeltaFun_mem_InP.1.continuous
  have hjf : Continuous fun τ : ℍ => Work.Kernels.jInvariantFun τ := by
    have h : (fun τ : ℍ => Work.Kernels.jInvariantFun τ) =
        fun τ => Work.Kernels.E4Fun τ ^ 3 / Work.Kernels.DeltaFun τ := rfl
    rw [h]
    exact (hE4.pow 3).div hD (fun τ => Work.Kernels.ClassicalFacts.DeltaFun_ne_zero τ)
  have h1 : Continuous fun p : ℍ × ℍ => Work.Kernels.DeltaFun p.1 := hD.comp continuous_fst
  have h2 : Continuous fun p : ℍ × ℍ => Work.Kernels.DeltaFun p.2 := hD.comp continuous_snd
  have h3 : Continuous fun p : ℍ × ℍ => Work.Kernels.jInvariantFun p.1 := hjf.comp continuous_fst
  have h4 : Continuous fun p : ℍ × ℍ => Work.Kernels.jInvariantFun p.2 := hjf.comp continuous_snd
  simp only [Work.Kernels.growthPrefactor]
  exact ((h1.mul (h2.pow _)).mul (h3.sub h4))

/-- The box is nonempty (for `H ≥ 2`): the pair `(2i, i)`. -/
private lemma nonempty_BxM {H : ℝ} (hH : 2 ≤ H) : (BxM H).Nonempty := by
  refine ⟨((⟨(2 : ℂ) * Complex.I, by simp⟩ : ℍ),
    Work.Kernels.imagAxis 1 (by norm_num)), ?_⟩
  rw [mem_BxM]
  have h1im : ((⟨(2 : ℂ) * Complex.I, by simp⟩ : ℍ)).im = 2 := by simp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp
  · rw [h1im]
  · rw [h1im]; linarith
  · rw [Work.Asymptotics.fpdImagAxis_im]
  · rw [Work.Asymptotics.fpdImagAxis_im, h1im]; norm_num
  · show ((1 : ℂ) * Complex.I).re = 0
    simp

/-- `growthPrefactor` is bounded below by a positive constant on the compact box. -/
private lemma exists_lower_growthPrefactorM (d : ℕ) (H : ℝ) (hH : 2 ≤ H) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ p ∈ BxM H, δ ≤ ‖Work.Kernels.growthPrefactor d p.1 p.2‖ := by
  obtain ⟨p₀, hp₀mem, hp₀min⟩ := (isCompact_BxM hH).exists_isMinOn (nonempty_BxM hH)
    ((continuous_growthPrefactor_pairM d).norm).continuousOn
  refine ⟨‖Work.Kernels.growthPrefactor d p₀.1 p₀.2‖,
    norm_pos_iff.mpr (growthPrefactor_ne_zero d (jInvariantFun_ne_of_mem_BxM hp₀mem)),
    fun p hp => hp₀min hp⟩

/-! ## Bounding the scale on the funnel and on the axis -/

private lemma scale_le_of_funnelM {H : ℝ} {τ : ℍ} (hre : |τ.re| ≤ 1) (him2 : 2 ≤ τ.im)
    (himH : τ.im ≤ H) :
    Work.Kernels.scale τ ≤ 1 + (1 / 2 : ℝ) + Real.sqrt (1 + H ^ 2) := by
  have h1 : (τ.im)⁻¹ ≤ (1 / 2 : ℝ) := by
    have h := one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 2) him2
    simpa [one_div] using h
  have hsq : ‖(τ : ℂ)‖ ^ 2 ≤ 1 + H ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    have hre2 : τ.re ^ 2 ≤ 1 := by
      have := abs_le.mp hre; nlinarith [this.1, this.2]
    have him2' : τ.im ^ 2 ≤ H ^ 2 := by nlinarith [τ.im_pos]
    nlinarith
  have h2 : ‖(τ : ℂ)‖ ≤ Real.sqrt (1 + H ^ 2) := by
    calc ‖(τ : ℂ)‖ = Real.sqrt (‖(τ : ℂ)‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt (1 + H ^ 2) := Real.sqrt_le_sqrt hsq
  have hdef : Work.Kernels.scale τ = 1 + (τ.im)⁻¹ + ‖(τ : ℂ)‖ := rfl
  rw [hdef]; linarith

private lemma scale_imagAxis_le {H t : ℝ} (ht : 1 ≤ t) (htH : t ≤ H - 1) :
    Work.Kernels.scale (Work.Kernels.imagAxis t (by linarith : 0 < t)) ≤ H + 1 := by
  rw [fpdScale_imagAxis]
  have h : (t)⁻¹ ≤ 1 := by
    have := one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 1) ht
    simpa [one_div] using this
  linarith

/-! ## The main theorem -/

theorem KMinus_axis_compact (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (H : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (τ : UpperHalfPlane) (t : ℝ) (ht : 0 < t),
      τ ∈ Work.Asymptotics.DomainD → 2 ≤ τ.im → τ.im ≤ H → 1 ≤ t → t ≤ τ.im - 1 →
        ‖Work.Kernels.KMinus ℓ d τ (Work.Kernels.imagAxis t ht)‖ ≤ C := by
  rcases lt_or_ge H 2 with hH | hH
  · -- the parameter set is empty
    refine ⟨1, one_pos, fun τ t ht hD him2 himH h1 h2 => ?_⟩
    exfalso
    linarith
  · obtain ⟨δ, hδpos, hδ⟩ := exists_lower_growthPrefactorM d H hH
    obtain ⟨αf, Nf, Mf, hαf, hNf, hMf, hbf⟩ := (KClear_mg2 ℓ d hd).1
    obtain ⟨αh, Nh, Mh, hαh, hNh, hMh, hbh⟩ := (KClear_mg2 ℓ d hd).2
    refine ⟨max 1 ((αf * (1 + (1 / 2 : ℝ) + Real.sqrt (1 + H ^ 2)) ^ Nf * (H + 1) ^ Mf +
      αh * (1 + (1 / 2 : ℝ) + Real.sqrt (1 + H ^ 2)) ^ Nh * (H + 1) ^ Mh) / δ),
      lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
    intro τ t ht hD him2 himH h1 h2
    have hreτ : |τ.re| ≤ 1 := by
      have h := (mem_DomainD.mp hD)
      rw [abs_le]; exact ⟨by linarith [h.1], by linarith [h.2.1]⟩
    have hzre : ((Work.Kernels.imagAxis t ht : ℍ) : ℂ).re = 0 := by
      show ((t : ℂ) * Complex.I).re = 0
      simp
    have hzim : (Work.Kernels.imagAxis t ht).im = t := Work.Asymptotics.fpdImagAxis_im t ht
    have htH : t ≤ H - 1 := by linarith
    have hpmem : (τ, Work.Kernels.imagAxis t ht) ∈ BxM H := by
      rw [mem_BxM]
      refine ⟨hreτ, him2, himH, ?_, ?_, hzre⟩
      · rw [hzim]; exact h1
      · rw [hzim]; exact h2
    have hJ := jInvariantFun_ne_of_mem_BxM hpmem
    have hgpne : Work.Kernels.growthPrefactor d τ (Work.Kernels.imagAxis t ht) ≠ 0 :=
      growthPrefactor_ne_zero d hJ
    have hgpnorm : ‖Work.Kernels.growthPrefactor d τ (Work.Kernels.imagAxis t ht)‖ ≠ 0 :=
      norm_ne_zero_iff.mpr hgpne
    -- the cleared kernel and its value
    have hclear : Work.Kernels.KMinusClear ℓ d τ (Work.Kernels.imagAxis t ht)
        = Work.Kernels.growthPrefactor d τ (Work.Kernels.imagAxis t ht)
          * Work.Kernels.KMinus ℓ d τ (Work.Kernels.imagAxis t ht) :=
      Work.Kernels.ClearLink.KMinusClear_eq_smul ℓ d hd τ _ hJ
    have hsplit : Work.Kernels.KMinusClear ℓ d τ (Work.Kernels.imagAxis t ht)
        = Work.Kernels.KfunClear ℓ d τ (Work.Kernels.imagAxis t ht)
          - Work.Kernels.KhatClear ℓ d τ (Work.Kernels.imagAxis t ht) := by
      simp only [Work.Kernels.KMinusClear, Work.Kernels.KfunClear, Work.Kernels.KhatClear]
      ring
    -- the norm identity
    have hnorm : ‖Work.Kernels.KMinus ℓ d τ (Work.Kernels.imagAxis t ht)‖
        = ‖Work.Kernels.KMinusClear ℓ d τ (Work.Kernels.imagAxis t ht)‖
          / ‖Work.Kernels.growthPrefactor d τ (Work.Kernels.imagAxis t ht)‖ := by
      have h1' : ‖Work.Kernels.KMinusClear ℓ d τ (Work.Kernels.imagAxis t ht)‖
          = ‖Work.Kernels.growthPrefactor d τ (Work.Kernels.imagAxis t ht)‖
            * ‖Work.Kernels.KMinus ℓ d τ (Work.Kernels.imagAxis t ht)‖ := by
        rw [hclear, norm_mul]
      rw [h1', mul_div_cancel_left₀ _ hgpnorm]
    -- the scale bounds
    have hsτ : Work.Kernels.scale τ ≤ 1 + (1 / 2 : ℝ) + Real.sqrt (1 + H ^ 2) :=
      scale_le_of_funnelM hreτ him2 himH
    have hsz : Work.Kernels.scale (Work.Kernels.imagAxis t ht) ≤ H + 1 :=
      scale_imagAxis_le h1 htH
    have hsτ1 : (1:ℝ) ≤ Work.Kernels.scale τ := Work.Kernels.one_le_scale τ
    have hsz1 : (1:ℝ) ≤ Work.Kernels.scale (Work.Kernels.imagAxis t ht) :=
      Work.Kernels.one_le_scale _
    have hpowτ : (Work.Kernels.scale τ) ^ Nf ≤ (1 + (1 / 2 : ℝ) + Real.sqrt (1 + H ^ 2)) ^ Nf :=
      Real.rpow_le_rpow (le_trans zero_le_one hsτ1) hsτ hNf
    have hpowz : (Work.Kernels.scale (Work.Kernels.imagAxis t ht)) ^ Mf ≤ (H + 1) ^ Mf :=
      Real.rpow_le_rpow (le_trans zero_le_one hsz1) hsz hMf
    have hpowτ' : (Work.Kernels.scale τ) ^ Nh ≤ (1 + (1 / 2 : ℝ) + Real.sqrt (1 + H ^ 2)) ^ Nh :=
      Real.rpow_le_rpow (le_trans zero_le_one hsτ1) hsτ hNh
    have hpowz' : (Work.Kernels.scale (Work.Kernels.imagAxis t ht)) ^ Mh ≤ (H + 1) ^ Mh :=
      Real.rpow_le_rpow (le_trans zero_le_one hsz1) hsz hMh
    have hbound_f : ‖Work.Kernels.KfunClear ℓ d τ (Work.Kernels.imagAxis t ht)‖
        ≤ αf * (1 + (1 / 2 : ℝ) + Real.sqrt (1 + H ^ 2)) ^ Nf * (H + 1) ^ Mf := by
      refine le_trans (hbf τ _) ?_
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left hpowτ hαf) hpowz (Real.rpow_nonneg (by positivity) _)
        (by positivity)
    have hbound_h : ‖Work.Kernels.KhatClear ℓ d τ (Work.Kernels.imagAxis t ht)‖
        ≤ αh * (1 + (1 / 2 : ℝ) + Real.sqrt (1 + H ^ 2)) ^ Nh * (H + 1) ^ Mh := by
      refine le_trans (hbh τ _) ?_
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left hpowτ' hαh) hpowz' (Real.rpow_nonneg (by positivity) _)
        (by positivity)
    have hbound : ‖Work.Kernels.KMinusClear ℓ d τ (Work.Kernels.imagAxis t ht)‖
        ≤ αf * (1 + (1 / 2 : ℝ) + Real.sqrt (1 + H ^ 2)) ^ Nf * (H + 1) ^ Mf +
          αh * (1 + (1 / 2 : ℝ) + Real.sqrt (1 + H ^ 2)) ^ Nh * (H + 1) ^ Mh := by
      rw [hsplit]
      exact le_trans (norm_sub_le _ _) (add_le_add hbound_f hbound_h)
    have hδ' : δ ≤ ‖Work.Kernels.growthPrefactor d τ (Work.Kernels.imagAxis t ht)‖ :=
      hδ ⟨τ, Work.Kernels.imagAxis t ht⟩ hpmem
    have hA_nonneg : 0 ≤ αf * (1 + (1 / 2 : ℝ) + Real.sqrt (1 + H ^ 2)) ^ Nf * (H + 1) ^ Mf +
        αh * (1 + (1 / 2 : ℝ) + Real.sqrt (1 + H ^ 2)) ^ Nh * (H + 1) ^ Mh := by
      refine add_nonneg (mul_nonneg (mul_nonneg hαf ?_)
        (Real.rpow_nonneg (by linarith) _)) (mul_nonneg (mul_nonneg hαh ?_)
        (Real.rpow_nonneg (by linarith) _)) <;> exact Real.rpow_nonneg (by positivity) _
    rw [hnorm]
    refine le_trans (le_trans (div_le_div_of_nonneg_right hbound (norm_nonneg _))
      (div_le_div_of_nonneg_left hA_nonneg hδpos hδ')) (le_max_right _ _)

end Work.Asymptotics

/-! ### Copy of `Submission/Work/Residues/KMinus_axis_bound.lean` -/

namespace Work.Residues

open UpperHalfPlane Matrix
open scoped UpperHalfPlane MatrixGroups Manifold ModularForm

open Work.Kernels

/-! ## Decomposition of `K_-` on the contour -/

lemma KMinus_eq_kpre_mul_bracket8 (ℓ : LogLambdaData) (τ z : ℍ) :
    KMinus ℓ 8 τ z = (kpre z τ)⁻¹ * bracket8 ℓ z τ := by
  rw [Work.Asymptotics.Compact.KMinus8_eq ℓ τ z]
  congr 1
  rw [bracket8_eq]
  simp only [bracket8e, c1728]

lemma KMinus_eq_kpre_mul_bracket24 (ℓ : LogLambdaData) (τ z : ℍ) :
    KMinus ℓ 24 τ z = (kpre z τ)⁻¹ * bracket24 ℓ z τ := by
  rw [Work.Asymptotics.Compact.KMinus24_eq ℓ τ z]
  congr 1
  rw [bracket24_eq]
  simp only [bracket24e, c1728]

/-- `e^{a} * e^{-b} ≤ 1` when `a ≤ b`. -/
private lemma exp_mul_exp_neg_le_one {a b : ℝ} (h : a ≤ b) :
    Real.exp a * Real.exp (-b) ≤ 1 := by
  rw [← Real.exp_add, Real.exp_le_one_iff]
  linarith

/-- Assembly of the axis bound from the four pieces. -/
theorem KMinus_axis_bound_of_pieces (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (hb8 : ∃ H C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧ 0 ≤ H ∧
      ∀ (τ : ℍ) (t : ℝ) (ht : 0 < t), H ≤ τ.im → 1 ≤ t →
        ‖bracket8 ℓ (imagAxis t ht) τ‖ ≤ C * (scale τ) ^ N * (1 + t) ^ M)
    (hb24 : ∃ H C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧ 0 ≤ H ∧
      ∀ (τ : ℍ) (t : ℝ) (ht : 0 < t), H ≤ τ.im → 1 ≤ t → t ≤ τ.im - 1 →
        ‖bracket24 ℓ (imagAxis t ht) τ‖ ≤ C * (scale τ) ^ N * (1 + t) ^ M *
          Real.exp (2 * Real.pi * τ.im))
    (hkp : ∃ H K : ℝ, 0 < K ∧ 0 ≤ H ∧
      ∀ (τ : ℍ) (t : ℝ) (ht : 0 < t), H ≤ τ.im → 1 ≤ t → t ≤ τ.im - 1 →
        ‖(kpre (imagAxis t ht) τ)⁻¹‖ ≤ K * Real.exp (2 * Real.pi * t) *
          Real.exp (-(2 * Real.pi * τ.im)))
    (hcomp : ∀ H : ℝ, ∃ C : ℝ, 0 < C ∧
      ∀ (τ : ℍ) (t : ℝ) (ht : 0 < t), τ ∈ Work.Asymptotics.DomainD → 2 ≤ τ.im → τ.im ≤ H →
        1 ≤ t → t ≤ τ.im - 1 → ‖KMinus ℓ d τ (imagAxis t ht)‖ ≤ C) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ : ℍ) (t : ℝ) (ht : 0 < t), τ ∈ Work.Asymptotics.DomainD → 2 ≤ τ.im → 1 ≤ t →
        t ≤ τ.im - 1 →
        ‖KMinus ℓ d τ (imagAxis t ht)‖ ≤ C * (scale τ) ^ N * (1 + t) ^ M *
          (if d = 8 then 1 else Real.exp (2 * Real.pi * t)) := by
  rcases hd with rfl | rfl
  · obtain ⟨H8, C8, N8, M8, hC8, hN8, hM8, hH8, hb8'⟩ := hb8
    obtain ⟨Hk, K, hK, hHk, hkp'⟩ := hkp
    set H0 : ℝ := max (max H8 Hk) 2 with hH0def
    have hH8H0 : H8 ≤ H0 := le_trans (le_max_left _ _) (le_max_left _ _)
    have hHkH0 : Hk ≤ H0 := le_trans (le_max_right _ _) (le_max_left _ _)
    obtain ⟨Cc, hCc, hcomp'⟩ := hcomp H0
    have hmaxpos : (0 : ℝ) < max (K * C8) Cc :=
      lt_of_lt_of_le (mul_pos hK hC8) (le_max_left _ _)
    have hmaxnn : (0 : ℝ) ≤ max (K * C8) Cc := hmaxpos.le
    have key : ∀ (τ : ℍ) (t : ℝ) (ht : 0 < t), τ ∈ Work.Asymptotics.DomainD → 2 ≤ τ.im →
        1 ≤ t → t ≤ τ.im - 1 →
        ‖KMinus ℓ 8 τ (imagAxis t ht)‖ ≤ max (K * C8) Cc * (scale τ) ^ N8 * (1 + t) ^ M8 := by
      intro τ t ht hτD hτ2 ht1 htt
      have hS : (0 : ℝ) ≤ (scale τ) ^ N8 := Real.rpow_nonneg (le_of_lt (scale_pos τ)) N8
      have hT : (0 : ℝ) ≤ (1 + t) ^ M8 := Real.rpow_nonneg (by linarith) M8
      have hsc : (1 : ℝ) ≤ (scale τ) ^ N8 := Real.one_le_rpow (one_le_scale τ) hN8
      have h1t : (1 : ℝ) ≤ (1 + t) ^ M8 := Real.one_le_rpow (by linarith) hM8
      by_cases hbig : H0 ≤ τ.im
      · have hH8le : H8 ≤ τ.im := le_trans hH8H0 hbig
        have hHkle : Hk ≤ τ.im := le_trans hHkH0 hbig
        have hee : Real.exp (2 * Real.pi * t) * Real.exp (-(2 * Real.pi * τ.im)) ≤ 1 :=
          exp_mul_exp_neg_le_one (by nlinarith [Real.pi_pos])
        rw [KMinus_eq_kpre_mul_bracket8 ℓ τ (imagAxis t ht), norm_mul]
        have h1 := hkp' τ t ht hHkle ht1 htt
        have h2 := hb8' τ t ht hH8le ht1
        have hb : ‖(kpre (imagAxis t ht) τ)⁻¹‖ * ‖bracket8 ℓ (imagAxis t ht) τ‖
            ≤ (K * C8) * (scale τ) ^ N8 * (1 + t) ^ M8 := by
          calc ‖(kpre (imagAxis t ht) τ)⁻¹‖ * ‖bracket8 ℓ (imagAxis t ht) τ‖
              ≤ (K * Real.exp (2 * Real.pi * t) * Real.exp (-(2 * Real.pi * τ.im))) *
                  (C8 * (scale τ) ^ N8 * (1 + t) ^ M8) :=
                mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
            _ = (K * C8) * (scale τ) ^ N8 * (1 + t) ^ M8 *
                  (Real.exp (2 * Real.pi * t) * Real.exp (-(2 * Real.pi * τ.im))) := by ring
            _ ≤ (K * C8) * (scale τ) ^ N8 * (1 + t) ^ M8 * 1 :=
                mul_le_mul_of_nonneg_left hee (by positivity)
            _ = (K * C8) * (scale τ) ^ N8 * (1 + t) ^ M8 := by ring
        refine le_trans hb ?_
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hS) hT
      · have hle : τ.im ≤ H0 := le_of_lt (not_le.mp hbig)
        refine le_trans (hcomp' τ t ht hτD hτ2 hle ht1 htt) ?_
        have hstep1 : max (K * C8) Cc * 1 ≤ max (K * C8) Cc * (scale τ) ^ N8 :=
          mul_le_mul_of_nonneg_left hsc hmaxnn
        have hstep2 : max (K * C8) Cc * (scale τ) ^ N8 * 1
            ≤ max (K * C8) Cc * (scale τ) ^ N8 * (1 + t) ^ M8 :=
          mul_le_mul_of_nonneg_left h1t (mul_nonneg hmaxnn hS)
        calc Cc ≤ max (K * C8) Cc := le_max_right _ _
          _ = max (K * C8) Cc * 1 := by ring
          _ ≤ max (K * C8) Cc * (scale τ) ^ N8 := hstep1
          _ = max (K * C8) Cc * (scale τ) ^ N8 * 1 := by ring
          _ ≤ max (K * C8) Cc * (scale τ) ^ N8 * (1 + t) ^ M8 := hstep2
    refine ⟨max (K * C8) Cc, N8, M8, hmaxpos, hN8, hM8, ?_⟩
    intro τ t ht h1 h2 h3 h4
    simpa using key τ t ht h1 h2 h3 h4
  · obtain ⟨H24, C24, N24, M24, hC24, hN24, hM24, hH24, hb24'⟩ := hb24
    obtain ⟨Hk, K, hK, hHk, hkp'⟩ := hkp
    set H0 : ℝ := max (max H24 Hk) 2 with hH0def
    have hH24H0 : H24 ≤ H0 := le_trans (le_max_left _ _) (le_max_left _ _)
    have hHkH0 : Hk ≤ H0 := le_trans (le_max_right _ _) (le_max_left _ _)
    obtain ⟨Cc, hCc, hcomp'⟩ := hcomp H0
    have hmaxpos : (0 : ℝ) < max (K * C24) Cc :=
      lt_of_lt_of_le (mul_pos hK hC24) (le_max_left _ _)
    have hmaxnn : (0 : ℝ) ≤ max (K * C24) Cc := hmaxpos.le
    have key : ∀ (τ : ℍ) (t : ℝ) (ht : 0 < t), τ ∈ Work.Asymptotics.DomainD → 2 ≤ τ.im →
        1 ≤ t → t ≤ τ.im - 1 →
        ‖KMinus ℓ 24 τ (imagAxis t ht)‖ ≤
          max (K * C24) Cc * (scale τ) ^ N24 * (1 + t) ^ M24 * Real.exp (2 * Real.pi * t) := by
      intro τ t ht hτD hτ2 ht1 htt
      have hS : (0 : ℝ) ≤ (scale τ) ^ N24 := Real.rpow_nonneg (le_of_lt (scale_pos τ)) N24
      have hT : (0 : ℝ) ≤ (1 + t) ^ M24 := Real.rpow_nonneg (by linarith) M24
      have hsc : (1 : ℝ) ≤ (scale τ) ^ N24 := Real.one_le_rpow (one_le_scale τ) hN24
      have h1t : (1 : ℝ) ≤ (1 + t) ^ M24 := Real.one_le_rpow (by linarith) hM24
      have hE : (1 : ℝ) ≤ Real.exp (2 * Real.pi * t) := by
        rw [Real.one_le_exp_iff]; positivity
      by_cases hbig : H0 ≤ τ.im
      · have hH24le : H24 ≤ τ.im := le_trans hH24H0 hbig
        have hHkle : Hk ≤ τ.im := le_trans hHkH0 hbig
        have hee : Real.exp (-(2 * Real.pi * τ.im)) * Real.exp (2 * Real.pi * τ.im) = 1 := by
          rw [← Real.exp_add, Real.exp_eq_one_iff]
          ring
        rw [KMinus_eq_kpre_mul_bracket24 ℓ τ (imagAxis t ht), norm_mul]
        have h1 := hkp' τ t ht hHkle ht1 htt
        have h2 := hb24' τ t ht hH24le ht1 htt
        have hb : ‖(kpre (imagAxis t ht) τ)⁻¹‖ * ‖bracket24 ℓ (imagAxis t ht) τ‖
            ≤ (K * C24) * (scale τ) ^ N24 * (1 + t) ^ M24 * Real.exp (2 * Real.pi * t) := by
          calc ‖(kpre (imagAxis t ht) τ)⁻¹‖ * ‖bracket24 ℓ (imagAxis t ht) τ‖
              ≤ (K * Real.exp (2 * Real.pi * t) * Real.exp (-(2 * Real.pi * τ.im))) *
                  (C24 * (scale τ) ^ N24 * (1 + t) ^ M24 * Real.exp (2 * Real.pi * τ.im)) :=
                mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
            _ = (K * C24) * (scale τ) ^ N24 * (1 + t) ^ M24 *
                  (Real.exp (2 * Real.pi * t) *
                    (Real.exp (-(2 * Real.pi * τ.im)) * Real.exp (2 * Real.pi * τ.im))) := by ring
            _ = (K * C24) * (scale τ) ^ N24 * (1 + t) ^ M24 * Real.exp (2 * Real.pi * t) := by
                rw [hee]; ring
        refine le_trans hb ?_
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hS) hT)
          (Real.exp_nonneg _)
      · have hle : τ.im ≤ H0 := le_of_lt (not_le.mp hbig)
        refine le_trans (hcomp' τ t ht hτD hτ2 hle ht1 htt) ?_
        have hstep1 : max (K * C24) Cc * 1 ≤ max (K * C24) Cc * (scale τ) ^ N24 :=
          mul_le_mul_of_nonneg_left hsc hmaxnn
        have hstep2 : max (K * C24) Cc * (scale τ) ^ N24 * 1
            ≤ max (K * C24) Cc * (scale τ) ^ N24 * (1 + t) ^ M24 :=
          mul_le_mul_of_nonneg_left h1t (mul_nonneg hmaxnn hS)
        have hstep3 : max (K * C24) Cc * (scale τ) ^ N24 * (1 + t) ^ M24 * 1
            ≤ max (K * C24) Cc * (scale τ) ^ N24 * (1 + t) ^ M24 *
              Real.exp (2 * Real.pi * t) :=
          mul_le_mul_of_nonneg_left hE (mul_nonneg (mul_nonneg hmaxnn hS) hT)
        calc Cc ≤ max (K * C24) Cc := le_max_right _ _
          _ = max (K * C24) Cc * 1 := by ring
          _ ≤ max (K * C24) Cc * (scale τ) ^ N24 := hstep1
          _ = max (K * C24) Cc * (scale τ) ^ N24 * 1 := by ring
          _ ≤ max (K * C24) Cc * (scale τ) ^ N24 * (1 + t) ^ M24 := hstep2
          _ = max (K * C24) Cc * (scale τ) ^ N24 * (1 + t) ^ M24 * 1 := by ring
          _ ≤ max (K * C24) Cc * (scale τ) ^ N24 * (1 + t) ^ M24 * Real.exp (2 * Real.pi * t) :=
              hstep3
    refine ⟨max (K * C24) Cc, N24, M24, hmaxpos, hN24, hM24, ?_⟩
    intro τ t ht h1 h2 h3 h4
    simpa using key τ t ht h1 h2 h3 h4

/-- **The `K_-` bound on the contour below the diagonal.**  For `d ∈ {8,24}`, `τ ∈ 𝒟` with
`2 ≤ Im τ`, and `1 ≤ t ≤ Im τ - 1` (so that the contour point `it` lies strictly below the
diagonal), the kernel `K_-^{(d)}(τ,it)` grows at most polynomially in `τ` and in `t`, with the
single exponential factor `e^{2πt}` allowed in dimension 24. -/
theorem KMinus_axis_bound (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ : UpperHalfPlane) (t : ℝ) (ht : 0 < t), τ ∈ Work.Asymptotics.DomainD → 2 ≤ τ.im →
        1 ≤ t → t ≤ τ.im - 1 →
        ‖Work.Kernels.KMinus ℓ d τ (Work.Kernels.imagAxis t ht)‖
          ≤ C * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M *
              (if d = 8 then 1 else Real.exp (2 * Real.pi * t)) := by
  refine KMinus_axis_bound_of_pieces ℓ d hd (bracket8_axis_bound ℓ) (bracket24_axis_bound ℓ)
    ?_ (fun H => Work.Asymptotics.KMinus_axis_compact ℓ d hd H)
  refine kpre_inv_axis_bound (fun τ hτ => ?_) (fun t ht ht1 => ?_) (fun τ hτ => ?_)
  · exact Work.Asymptotics.DeltaFun_upper_sharp τ hτ
  · exact Work.Asymptotics.DeltaFun_imagAxis_lower_sharp t ht ht1
  · exact Work.Asymptotics.E4Fun_upper_half τ hτ

end Work.Residues

/-! ### Copy of `Submission/Work/Asymptotics/funnelKernelPre.lean` -/

namespace Work.Asymptotics

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped Topology

open Work.Kernels

/-! ## Explicit-constant decay bounds for the theta quartics

These are the `Work.Residues.UFun_decay` / `WFun_decay` / `VFun_decay` estimates with the
constants of their proofs made explicit; they are the numerical input of the control of the
divisor `Δ(τ)Δ(it)^e (j τ - j(it))` below the diagonal. -/

lemma VFun_decay_exp (τ : ℍ) (hτ : 1 ≤ τ.im) :
    ‖VFun τ‖ ≤ (Work.Modular.theta2BoundConst ^ 4 + 1) * Real.exp (-(Real.pi * τ.im)) := by
  have h := Work.Modular.norm_theta2_le_exp τ (by simpa using hτ)
  have hV : VFun τ = Work.Modular.theta2 τ ^ 4 := rfl
  rw [hV, norm_pow]
  have h1 : ‖Work.Modular.theta2 τ‖ ^ 4 ≤
      (Real.exp (-Real.pi * (τ : ℂ).im / 4) * Work.Modular.theta2BoundConst) ^ 4 :=
    pow_le_pow_left₀ (norm_nonneg _) h 4
  have h2 : (Real.exp (-Real.pi * (τ : ℂ).im / 4) * Work.Modular.theta2BoundConst) ^ 4
      = Work.Modular.theta2BoundConst ^ 4 * Real.exp (-(Real.pi * τ.im)) := by
    rw [mul_pow]
    have hexp : Real.exp (-Real.pi * (τ : ℂ).im / 4) ^ 4 = Real.exp (-(Real.pi * τ.im)) := by
      rw [← Real.exp_nat_mul]
      simp only [UpperHalfPlane.coe_im]
      congr 1; ring
    rw [hexp]; ring
  have h3 : Work.Modular.theta2BoundConst ^ 4 * Real.exp (-(Real.pi * τ.im))
      ≤ (Work.Modular.theta2BoundConst ^ 4 + 1) * Real.exp (-(Real.pi * τ.im)) := by
    have := Real.exp_pos (-(Real.pi * τ.im))
    nlinarith [sq_nonneg (Work.Modular.theta2BoundConst ^ 2)]
  linarith [h1, le_of_eq h2, h3]

lemma UFun_decay_exp (τ : ℍ) (hτ : 1 ≤ τ.im) :
    ‖UFun τ - 1‖ ≤ (15 * Work.Residues.thetaA + 1) * Real.exp (-(Real.pi * τ.im)) := by
  have hz : 1 ≤ ((τ : ℂ)).im := hτ
  have h1 := Work.Residues.norm_jacobiTheta_sub_one_bound (τ : ℂ) hz
  have h2 := Work.Residues.norm_jacobiTheta_le_two (τ : ℂ) hz
  have h3 := Work.Residues.norm_pow_four_sub_one_le (w := jacobiTheta (τ : ℂ))
    (A := Work.Residues.thetaA) (e := Real.exp (-(Real.pi * (τ : ℂ).im)))
    Work.Residues.thetaA_nonneg (Real.exp_nonneg _) h1 h2
  have hU : UFun τ = jacobiTheta (τ : ℂ) ^ 4 := rfl
  rw [hU]
  simp only [UpperHalfPlane.coe_im] at h3
  have h4 : (15 * Work.Residues.thetaA) * Real.exp (-(Real.pi * τ.im))
      ≤ (15 * Work.Residues.thetaA + 1) * Real.exp (-(Real.pi * τ.im)) := by
    have := Real.exp_pos (-(Real.pi * τ.im)); nlinarith
  linarith [h3, h4]

lemma WFun_decay_exp (τ : ℍ) (hτ : 1 ≤ τ.im) :
    ‖WFun τ - 1‖ ≤ (15 * Work.Residues.thetaA + 1) * Real.exp (-(Real.pi * τ.im)) := by
  set z : ℂ := ((ModularGroup.T • τ : ℍ) : ℂ) with hzdef
  have hcoe : z = (τ : ℂ) + 1 := by
    rw [hzdef, modular_T_smul, UpperHalfPlane.coe_vadd]; push_cast; ring
  have him : z.im = τ.im := by rw [hcoe]; simp
  have hz : 1 ≤ z.im := by rw [him]; exact hτ
  have h1 : ‖jacobiTheta z - 1‖ ≤ Work.Residues.thetaA * Real.exp (-(Real.pi * τ.im)) := by
    have hh := Work.Residues.norm_jacobiTheta_sub_one_bound z hz
    rwa [him] at hh
  have h2 := Work.Residues.norm_jacobiTheta_le_two z hz
  have h3 := Work.Residues.norm_pow_four_sub_one_le (w := jacobiTheta z) (A := Work.Residues.thetaA)
    (e := Real.exp (-(Real.pi * τ.im))) Work.Residues.thetaA_nonneg (Real.exp_nonneg _) h1 h2
  have hW : WFun τ = jacobiTheta z ^ 4 := by
    have h4 : Work.Modular.theta4 τ = jacobiTheta z := by
      rw [← Work.Modular.theta3_T_smul τ]
      rfl
    rw [show WFun τ = Work.Modular.theta4 τ ^ 4 from rfl, h4]
  rw [hW]
  have h5 : (15 * Work.Residues.thetaA) * Real.exp (-(Real.pi * τ.im))
      ≤ (15 * Work.Residues.thetaA + 1) * Real.exp (-(Real.pi * τ.im)) := by
    have := Real.exp_pos (-(Real.pi * τ.im)); nlinarith
  linarith [h3, h5]

/-- **Funnel `K_-` bound below the diagonal**, from the proved
`Work.Residues.KMinus_axis_bound`. -/
theorem KMinus_axis_bound_apply (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ : UpperHalfPlane) (t : ℝ) (ht : 0 < t), τ ∈ Work.Asymptotics.DomainD → 2 ≤ τ.im →
        1 ≤ t → t ≤ τ.im - 1 →
        ‖Work.Kernels.KMinus ℓ d τ (Work.Kernels.imagAxis t ht)‖
          ≤ C * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M *
              (if d = 8 then 1 else Real.exp (2 * Real.pi * t)) :=
  Work.Residues.KMinus_axis_bound ℓ d hd

/-! ## The `K_+` bound on the axis -/

/-- Raising the polynomial part and the constant of a bound of the form
`C S^N T^M X`. -/
lemma BddStep {C C' S T N N' M M' X : ℝ} (hC : C ≤ C') (hC'0 : 0 ≤ C')
    (hS : (1:ℝ) ≤ S) (hT : (1:ℝ) ≤ T) (hN : N ≤ N') (hM : M ≤ M') (hX : (1:ℝ) ≤ X) :
    C * S ^ N * T ^ M * X ≤ C' * S ^ N' * T ^ M' * X := by
  have hSN : S ^ N ≤ S ^ N' := Real.rpow_le_rpow_of_exponent_le hS hN
  have hTM : T ^ M ≤ T ^ M' := Real.rpow_le_rpow_of_exponent_le hT hM
  have hS0 : (0:ℝ) ≤ S ^ N := Real.rpow_nonneg (by linarith) _
  have hT0 : (0:ℝ) ≤ T ^ M := Real.rpow_nonneg (by linarith) _
  have h1 : C * S ^ N ≤ C' * S ^ N' := mul_le_mul hC hSN hS0 hC'0
  have h2 : C * S ^ N * T ^ M ≤ C' * S ^ N' * T ^ M' :=
    mul_le_mul h1 hTM hT0 (by positivity)
  exact mul_le_mul_of_nonneg_right h2 (by linarith)

/-- Absorbing a constant into the polynomial part of a bound. -/
lemma const_le_poly {C C' S T N M X : ℝ} (hC : C ≤ C') (hC'0 : 0 ≤ C')
    (hS : (1:ℝ) ≤ S) (hT : (1:ℝ) ≤ T) (hN : 0 ≤ N) (hM : 0 ≤ M) (hX : (1:ℝ) ≤ X) :
    C ≤ C' * S ^ N * T ^ M * X := by
  have hSN : (1:ℝ) ≤ S ^ N := Real.one_le_rpow hS hN
  have hTM : (1:ℝ) ≤ T ^ M := Real.one_le_rpow hT hM
  have hAB : (1:ℝ) ≤ S ^ N * T ^ M := by
    have h0 : (0:ℝ) ≤ S ^ N := Real.rpow_nonneg (by linarith) _
    simpa using mul_le_mul hSN hTM (by norm_num : (0:ℝ) ≤ 1) h0
  have hprod : (1:ℝ) ≤ S ^ N * T ^ M * X := by
    simpa using mul_le_mul hAB hX (by norm_num : (0:ℝ) ≤ 1)
      (le_trans (by norm_num : (0:ℝ) ≤ 1) hAB)
  have := mul_le_mul_of_nonneg_left hprod hC'0
  linarith

/-- **The `K_+` bound on the axis.**  Assembly of the asymptotic pieces `KPlus8_axis_big`,
`KPlus24_axis_big` (large `Im τ`) with the compact bound `KPlus_axis_compact`. -/
theorem KPlus_axis_bound (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ : UpperHalfPlane) (t : ℝ), τ ∈ Work.Asymptotics.DomainD → 2 ≤ τ.im →
        1 ≤ t → t ≤ τ.im - 1 →
        ‖Work.Kernels.KPlus d τ (Work.Asymptotics.cti t)‖
          ≤ C * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M *
              (if d = 8 then 1 else Real.exp (2 * Real.pi * t)) := by
  rcases hd with rfl | rfl
  · obtain ⟨H8, C8, N8, M8, hC8, hN8, hM8, _hH8, hb8⟩ := KPlus8_axis_big
    obtain ⟨Cc, hCc, hcomp⟩ := KPlus_axis_compact 8 (Or.inl rfl) H8
    refine ⟨max C8 Cc, N8, M8, lt_of_lt_of_le hC8 (le_max_left _ _), hN8, hM8, ?_⟩
    intro τ t hD h2 h1 hle
    have hS1 : (1:ℝ) ≤ Work.Kernels.scale τ := Work.Kernels.one_le_scale τ
    have hT1 : (1:ℝ) ≤ 1 + t := by linarith
    rw [if_pos rfl]
    by_cases hbig : H8 ≤ τ.im
    · refine le_trans (hb8 τ t ⟨hD, h2⟩ hbig h1 hle) ?_
      simpa using BddStep (C := C8) (C' := max C8 Cc) (le_max_left _ _)
        (lt_of_lt_of_le hC8 (le_max_left _ _)).le hS1 hT1 le_rfl le_rfl le_rfl
    · refine le_trans (hcomp τ t hD h2 (le_of_lt (not_le.mp hbig)) h1 hle) ?_
      exact const_le_poly (C := Cc) (C' := max C8 Cc) (le_max_right _ _)
        (lt_of_lt_of_le hC8 (le_max_left _ _)).le hS1 hT1 hN8 hM8 le_rfl
  · obtain ⟨H24, C24, N24, M24, hC24, hN24, hM24, _hH24, hb24⟩ := KPlus24_axis_big
    obtain ⟨Cc, hCc, hcomp⟩ := KPlus_axis_compact 24 (Or.inr rfl) H24
    refine ⟨max C24 Cc, N24, M24, lt_of_lt_of_le hC24 (le_max_left _ _), hN24, hM24, ?_⟩
    intro τ t hD h2 h1 hle
    have hS1 : (1:ℝ) ≤ Work.Kernels.scale τ := Work.Kernels.one_le_scale τ
    have hT1 : (1:ℝ) ≤ 1 + t := by linarith
    have hX1 : (1:ℝ) ≤ Real.exp (2 * Real.pi * t) := by
      rw [Real.one_le_exp_iff]; positivity
    rw [if_neg (by norm_num : ¬ ((24 : ℕ) = 8))]
    by_cases hbig : H24 ≤ τ.im
    · exact le_trans (hb24 τ t ⟨hD, h2⟩ hbig h1 hle)
        (BddStep (C := C24) (C' := max C24 Cc) (le_max_left _ _)
          (lt_of_lt_of_le hC24 (le_max_left _ _)).le hS1 hT1 le_rfl le_rfl hX1)
    · refine le_trans (hcomp τ t hD h2 (le_of_lt (not_le.mp hbig)) h1 hle) ?_
      exact const_le_poly (C := Cc) (C' := max C24 Cc) (le_max_right _ _)
        (lt_of_lt_of_le hC24 (le_max_left _ _)).le hS1 hT1 hN24 hM24 hX1

theorem funnelKernelPre (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ : UpperHalfPlane) (t : ℝ), τ ∈ Work.Asymptotics.DomainD → 2 ≤ τ.im →
        1 ≤ t → t ≤ τ.im - 1 →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖
          ≤ C * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M *
              Real.exp ((if d = 8 then 0 else 2 * Real.pi) * t) := by
  obtain ⟨Cp, Np, Mp, hCp, hNp, hMp, hKp⟩ := KPlus_axis_bound d hd
  obtain ⟨Cm, Nm, Mm, hCm, hNm, hMm, hKm⟩ := KMinus_axis_bound_apply ℓ d hd
  refine ⟨max Cp Cm, max Np Nm, max Mp Mm, lt_of_lt_of_le hCp (le_max_left _ _),
    le_max_of_le_left hNp, le_max_of_le_left hMp, ?_⟩
  intro τ t hD h2 h1 hle
  have ht0 : 0 < t := by linarith
  have hS : (1:ℝ) ≤ Work.Kernels.scale τ := Work.Kernels.one_le_scale τ
  have hT : (1:ℝ) ≤ 1 + t := by linarith
  have hX : Real.exp ((if d = 8 then 0 else 2 * Real.pi) * t)
      = (if d = 8 then 1 else Real.exp (2 * Real.pi * t)) := by
    by_cases h8 : d = 8
    · rw [if_pos h8, if_pos h8]; simp
    · rw [if_neg h8, if_neg h8]
  have hXge : (1:ℝ) ≤ (if d = 8 then 1 else Real.exp (2 * Real.pi * t)) := by
    by_cases h8 : d = 8
    · rw [if_pos h8]
    · rw [if_neg h8, Real.one_le_exp_iff]; positivity
  have hP : ‖Work.Kernels.KPlus d τ (Work.Kernels.imagAxis t ht0)‖
      ≤ Cp * (Work.Kernels.scale τ) ^ Np * (1 + t) ^ Mp *
          (if d = 8 then 1 else Real.exp (2 * Real.pi * t)) := by
    have h := hKp τ t hD h2 h1 hle
    rwa [Work.Asymptotics.cti_eq_imagAxis ht0] at h
  have hM : ‖Work.Kernels.KMinus ℓ d τ (Work.Kernels.imagAxis t ht0)‖
      ≤ Cm * (Work.Kernels.scale τ) ^ Nm * (1 + t) ^ Mm *
          (if d = 8 then 1 else Real.exp (2 * Real.pi * t)) := by
    exact hKm τ t ht0 hD h2 h1 hle
  have hP' : ‖Work.Kernels.KPlus d τ (Work.Kernels.imagAxis t ht0)‖
      ≤ max Cp Cm * (Work.Kernels.scale τ) ^ (max Np Nm) * (1 + t) ^ (max Mp Mm) *
          (if d = 8 then 1 else Real.exp (2 * Real.pi * t)) :=
    le_trans hP (BddStep (C := Cp) (C' := max Cp Cm) (le_max_left _ _)
      (lt_of_lt_of_le hCp (le_max_left _ _)).le hS hT (le_max_left _ _) (le_max_left _ _) hXge)
  have hM' : ‖Work.Kernels.KMinus ℓ d τ (Work.Kernels.imagAxis t ht0)‖
      ≤ max Cp Cm * (Work.Kernels.scale τ) ^ (max Np Nm) * (1 + t) ^ (max Mp Mm) *
          (if d = 8 then 1 else Real.exp (2 * Real.pi * t)) :=
    le_trans hM (BddStep (C := Cm) (C' := max Cp Cm) (le_max_right _ _)
      (lt_of_lt_of_le hCp (le_max_left _ _)).le hS hT (le_max_right _ _) (le_max_right _ _) hXge)
  have hsplit : ‖Work.Kernels.Kfun ℓ d τ (Work.Kernels.imagAxis t ht0)‖
      ≤ max (‖Work.Kernels.KPlus d τ (Work.Kernels.imagAxis t ht0)‖)
            (‖Work.Kernels.KMinus ℓ d τ (Work.Kernels.imagAxis t ht0)‖) := by
    have hsum := norm_add_le (Work.Kernels.KPlus d τ (Work.Kernels.imagAxis t ht0))
      (Work.Kernels.KMinus ℓ d τ (Work.Kernels.imagAxis t ht0))
    rw [Work.Kernels.Kfun, norm_div]
    have h2n : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [h2n]
    have hx : ‖Work.Kernels.KPlus d τ (Work.Kernels.imagAxis t ht0)‖
        ≤ max (‖Work.Kernels.KPlus d τ (Work.Kernels.imagAxis t ht0)‖)
            (‖Work.Kernels.KMinus ℓ d τ (Work.Kernels.imagAxis t ht0)‖) := le_max_left _ _
    have hy : ‖Work.Kernels.KMinus ℓ d τ (Work.Kernels.imagAxis t ht0)‖
        ≤ max (‖Work.Kernels.KPlus d τ (Work.Kernels.imagAxis t ht0)‖)
            (‖Work.Kernels.KMinus ℓ d τ (Work.Kernels.imagAxis t ht0)‖) := le_max_right _ _
    linarith
  rw [hX, Work.Kernels.Kaxis, dif_pos ht0]
  exact le_trans hsplit (max_le hP' hM')

end

end Work.Asymptotics


namespace Work.Asymptotics.HalfFunnel

/-- **Pre-declash form of the half-funnel kernel bounds.**  The two estimates
`Work.Asymptotics.funnelKernelPre` (window `1 ≤ t ≤ Im τ - 1`) and
`Work.Asymptotics.funnelKernelSpike` (window `|t - Im τ| ≤ 1`) for the CKMRV kernel on the
half funnel `{τ ∈ 𝒟 : 2 ≤ Im τ}`. -/
theorem funnelPreDeclash (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) : (∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧ ∀ (τ : UpperHalfPlane) (t : ℝ), τ ∈ Work.Asymptotics.DomainD → 2 ≤ τ.im → 1 ≤ t → t ≤ τ.im - 1 → ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖ ≤ C * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M * Real.exp ((if d = 8 then 0 else 2 * Real.pi) * t)) ∧ (∃ (c₁ c₂ : ℂ) (C N M : ℝ), 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧ ‖c₁‖ ≤ C ∧ ‖c₂‖ ≤ C ∧ ∀ (τ : UpperHalfPlane) (t : ℝ), τ ∈ Work.Asymptotics.DomainD → 2 ≤ τ.im → τ.im - 1 ≤ t → t ≤ τ.im + 1 → ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t - (c₁ / ((t : ℂ) * Complex.I - ((τ : ℂ) - 1)) + c₂ / ((t : ℂ) * Complex.I - ((τ : ℂ) + 1)))‖ ≤ C * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M) :=
  ⟨Work.Asymptotics.funnelKernelPre ℓ d hd, Work.Asymptotics.funnelKernelSpike ℓ d hd⟩

end Work.Asymptotics.HalfFunnel
