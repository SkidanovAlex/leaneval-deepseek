import Mathlib
import Submission.Work.GM.S3.Base
import Submission.Work.GM.S3.Defs
import Submission.Work.GM.S3.Statements
import Submission.Work.GM.S3.Rl4Aux
import Submission.Work.GM.S3.fourier_decay_explicit
import Submission.Work.GM.S3.RtildeSq_one_lower
import Submission.Work.GM.S3.bddAbove_range_RtildeSq
import Submission.Work.GM.S3.gSq_continuous
import Submission.Work.GM.S3.integral_gSq_le

/-!
# GM 8.4, proved in a module free of the `iteratedDeriv_ofReal_comp` clash

`Submission.Work.GM.S3.lemma84` proves `Work.GM.S3.Lemma84Statement`, but its module imports
`Submission.Work.GM.S3.integral_iteratedDeriv_scaled_le`, which declares
`Work.GM.S3.iteratedDeriv_ofReal_comp` -- a name that is *also* declared in
`Submission.Work.GM.S3.hhat_defs`.  Any module importing both fails to build
("environment already contains ..."), and the final assembly of `s3_of_affine` needs both
`Lemma84Statement` and `Work.GM.S3.Prop72Statement` (whose module closure contains `hhat_defs`).

This file repeats the two proofs with *every* auxiliary declaration placed in the fresh namespace
`Work.GM.S3.L84cf`, so that no name it introduces can collide with any other module of the
project: the module is jointly importable with `Submission.Work.GM.S3.hhat_defs` (and with
`Submission.Work.GM.S3.integral_iteratedDeriv_scaled_le`, for that matter).

* the `L¹`-bounds for iterated derivatives of a scaled bump product are copied from
  `Submission/Work/GM/S3/integral_iteratedDeriv_scaled_le.lean`;
* the Fourier decay of `ψ₁ · RtildeSq` and its consequences are copied from
  `Submission/Work/GM/S3/lemma84.lean`.

The public statement is re-exported below as `Work.GM.S3.lemma84_clashfree`.
-/

namespace Work.GM.S3

/- The private namespace holding every copied declaration: nothing declared here can clash with
another module of the project. -/
namespace L84cf


open MeasureTheory

/-- The scaled/shifted bump derivative: `(u ↦ ψ (Bs * (u - u')))^{(m)} = Bs^m · ψ^{(m)}(Bs * (u - u'))`. -/
lemma iteratedDeriv_comp_scaled_shift {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ) (Bs u' : ℝ) (m : ℕ) :
    iteratedDeriv m (fun u : ℝ => ψ (Bs * (u - u'))) =
      fun u => Bs ^ m * iteratedDeriv m ψ (Bs * (u - u')) := by
  have hg : ContDiff ℝ ((m : ℕ∞) : WithTop ℕ∞) ψ := hψ.of_le (by exact_mod_cast le_top)
  funext u
  rw [show iteratedDeriv m (fun u : ℝ => ψ (Bs * (u - u'))) u
        = iteratedDeriv m (fun v => ψ (Bs * v)) (u - u') from
        congrFun (iteratedDeriv_comp_sub_const m (fun v => ψ (Bs * v)) u') u]
  rw [iteratedDeriv_comp_const_mul hg Bs]

/-- The scaled bump derivative with the extra amplitude `Bs`:
`(u ↦ Bs · ψ (Bs * (u - u')))^{(m)} = Bs^(m+1) · ψ^{(m)}(Bs * (u - u'))`. -/
lemma iteratedDeriv_scaled_shift_mul {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ) (Bs u' : ℝ) (m : ℕ) :
    iteratedDeriv m (fun u : ℝ => Bs * ψ (Bs * (u - u'))) =
      fun u => Bs ^ (m + 1) * iteratedDeriv m ψ (Bs * (u - u')) := by
  have h1 := iteratedDeriv_comp_scaled_shift hψ Bs u' m
  funext u
  rw [show iteratedDeriv m (fun u : ℝ => Bs * ψ (Bs * (u - u'))) u
        = Bs * iteratedDeriv m (fun u => ψ (Bs * (u - u'))) u from
        iteratedDeriv_const_mul_field Bs (fun u => ψ (Bs * (u - u')))]
  rw [congrFun h1 u, pow_succ']
  ring

/-- The iterated derivative of a real-valued function, viewed as a complex-valued function,
is the complexification of the real iterated derivative. -/
lemma iteratedDeriv_ofReal_comp {F : ℝ → ℝ}
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) (j : ℕ) (u : ℝ) :
    iteratedDeriv j (fun u : ℝ => ((F u : ℝ) : ℂ)) u = ((iteratedDeriv j F u : ℝ) : ℂ) := by
  have hF' : ContDiffAt ℝ ((j : WithTop ℕ∞)) F u :=
    hF.contDiffAt.of_le (by exact_mod_cast le_top)
  have h := ContinuousLinearMap.iteratedFDeriv_comp_left (𝕜 := ℝ) Complex.ofRealCLM hF'
    (i := j) le_rfl
  have h2 : (iteratedFDeriv ℝ j (fun u : ℝ => ((F u : ℝ) : ℂ)) u) (fun _ => (1 : ℝ))
      = Complex.ofRealCLM ((iteratedFDeriv ℝ j F u) (fun _ => (1 : ℝ))) := by
    change (iteratedFDeriv ℝ j (Complex.ofRealCLM ∘ F) u) (fun _ => (1 : ℝ)) = _
    rw [h]; rfl
  simpa [iteratedDeriv] using h2

/-- Substitution rule: the `L¹` mass of `|ψ^{(m)}(Bs * (· - u'))|`. -/
lemma integral_abs_iteratedDeriv_scaled_shift (ψ : ℝ → ℝ) (Bs u' : ℝ) (m : ℕ) :
    ∫ u, |iteratedDeriv m ψ (Bs * (u - u'))| = |Bs⁻¹| * ∫ x, |iteratedDeriv m ψ x| := by
  have h1 : (∫ u, |iteratedDeriv m ψ (Bs * (u - u'))|)
      = ∫ z, |iteratedDeriv m ψ (Bs * z)| := by
    rw [show (fun u : ℝ => |iteratedDeriv m ψ (Bs * (u - u'))|)
          = (fun z : ℝ => |iteratedDeriv m ψ (Bs * z)|) ∘ (fun u => u - u') from rfl]
    exact integral_sub_right_eq_self (fun z => |iteratedDeriv m ψ (Bs * z)|) u'
  rw [h1, MeasureTheory.Measure.integral_comp_mul_left (fun y : ℝ => |iteratedDeriv m ψ y|) Bs,
    smul_eq_mul]

/-- **`L¹` bound for the derivatives of a scaled bump product** (real-valued version). -/
lemma integral_abs_iteratedDeriv_mul_scaled_le
    {ψ₁ ψ₃ : ℝ → ℝ} {c₁ : ℕ → ℝ} (hc₁ : ∀ i x, |iteratedDeriv i ψ₁ x| ≤ c₁ i)
    (h₁ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ₁) (_h₁cs : HasCompactSupport ψ₁)
    (h₃ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ₃) (h₃cs : HasCompactSupport ψ₃)
    {Bs : ℝ} (hBs : 1 ≤ Bs) (u' : ℝ) (j : ℕ) :
    ∫ u, |iteratedDeriv j (fun u : ℝ => ψ₁ u * (Bs * ψ₃ (Bs * (u - u')))) u| ≤
      (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * c₁ i * ∫ x, |iteratedDeriv (j - i) ψ₃ x|)
        * Bs ^ j := by
  have hBs0 : 0 < Bs := lt_of_lt_of_le zero_lt_one hBs
  have hBsne : Bs ≠ 0 := ne_of_gt hBs0
  set Φ : ℝ → ℝ := fun u => ψ₁ u * (Bs * ψ₃ (Bs * (u - u'))) with hΦ
  let G : ℝ → ℝ := fun v => Bs * ψ₃ (Bs * (v - u'))
  have hΦG : Φ = ψ₁ * G := by
    rw [hΦ]; funext u; simp only [Pi.mul_apply]; rfl
  have h1diff : ∀ u, ContDiffAt ℝ ((j : WithTop ℕ∞)) ψ₁ u := fun u =>
    h₁.contDiffAt.of_le (by exact_mod_cast le_top)
  have hGdiff : ∀ u, ContDiffAt ℝ ((j : WithTop ℕ∞)) G u := by
    intro u
    have hcd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun v : ℝ => Bs * ψ₃ (Bs * (v - u'))) := by
      fun_prop
    exact (hcd.contDiffAt (x := u)).of_le (by exact_mod_cast le_top)
  have hGderiv : ∀ m u, iteratedDeriv m G u
      = Bs ^ (m + 1) * iteratedDeriv m ψ₃ (Bs * (u - u')) := by
    intro m u
    have h := congrFun (iteratedDeriv_scaled_shift_mul h₃ Bs u' m) u
    simpa only [G] using h
  have hleib : ∀ u, iteratedDeriv j Φ u = ∑ i ∈ Finset.range (j + 1),
      (j.choose i : ℝ) * iteratedDeriv i ψ₁ u * iteratedDeriv (j - i) G u := by
    intro u
    rw [hΦG]
    exact iteratedDeriv_mul (h1diff u) (hGdiff u)
  have hbound : ∀ u, |iteratedDeriv j Φ u| ≤ ∑ i ∈ Finset.range (j + 1),
      (j.choose i : ℝ) * c₁ i * Bs ^ (j - i + 1) * |iteratedDeriv (j - i) ψ₃ (Bs * (u - u'))| := by
    intro u
    rw [hleib u]
    calc |∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * iteratedDeriv i ψ₁ u * iteratedDeriv (j - i) G u|
        ≤ ∑ i ∈ Finset.range (j + 1),
            |(j.choose i : ℝ) * iteratedDeriv i ψ₁ u * iteratedDeriv (j - i) G u| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range (j + 1),
            (j.choose i : ℝ) * c₁ i * Bs ^ (j - i + 1) * |iteratedDeriv (j - i) ψ₃ (Bs * (u - u'))| := by
          apply Finset.sum_le_sum
          intro i _
          have hA : 0 ≤ (j.choose i : ℝ) := Nat.cast_nonneg _
          have hWabs : |iteratedDeriv (j - i) G u|
              = Bs ^ (j - i + 1) * |iteratedDeriv (j - i) ψ₃ (Bs * (u - u'))| := by
            rw [hGderiv (j - i) u, abs_mul, abs_of_nonneg (pow_nonneg hBs0.le _)]
          calc |(j.choose i : ℝ) * iteratedDeriv i ψ₁ u * iteratedDeriv (j - i) G u|
              = (j.choose i : ℝ) * |iteratedDeriv i ψ₁ u| * |iteratedDeriv (j - i) G u| := by
                rw [abs_mul, abs_mul, abs_of_nonneg hA]
            _ = (j.choose i : ℝ) * |iteratedDeriv i ψ₁ u|
                  * (Bs ^ (j - i + 1) * |iteratedDeriv (j - i) ψ₃ (Bs * (u - u'))|) := by rw [hWabs]
            _ ≤ (j.choose i : ℝ) * c₁ i
                  * (Bs ^ (j - i + 1) * |iteratedDeriv (j - i) ψ₃ (Bs * (u - u'))|) := by
                gcongr
                exact hc₁ i u
            _ = (j.choose i : ℝ) * c₁ i * Bs ^ (j - i + 1)
                  * |iteratedDeriv (j - i) ψ₃ (Bs * (u - u'))| := by ring
  have hcs_iter : ∀ m, HasCompactSupport (iteratedDeriv m ψ₃) := by
    intro m
    induction m with
    | zero => simpa using h₃cs
    | succ n ih => rw [iteratedDeriv_succ]; exact ih.deriv
  have hbase_int : ∀ m, Integrable (fun x : ℝ => |iteratedDeriv m ψ₃ x|) := by
    intro m
    exact ((h₃.continuous_iteratedDeriv m (by exact_mod_cast le_top)).abs).integrable_of_hasCompactSupport
      (hcs_iter m).abs
  have hint : ∀ m, Integrable (fun u : ℝ => |iteratedDeriv m ψ₃ (Bs * (u - u'))|) := by
    intro m
    exact ((hbase_int m).comp_mul_left' hBsne).comp_sub_right u'
  have hKint : ∀ i, Integrable (fun u : ℝ =>
      (j.choose i : ℝ) * c₁ i * Bs ^ (j - i + 1) * |iteratedDeriv (j - i) ψ₃ (Bs * (u - u'))|) :=
    fun i => (hint (j - i)).const_mul ((j.choose i : ℝ) * c₁ i * Bs ^ (j - i + 1))
  have hGint : Integrable (fun u : ℝ => ∑ i ∈ Finset.range (j + 1),
      (j.choose i : ℝ) * c₁ i * Bs ^ (j - i + 1) * |iteratedDeriv (j - i) ψ₃ (Bs * (u - u'))|) :=
    MeasureTheory.integrable_finsetSum _ (fun i _ => hKint i)
  have hstep1 : ∫ u, |iteratedDeriv j Φ u| ≤ ∫ u, (∑ i ∈ Finset.range (j + 1),
      (j.choose i : ℝ) * c₁ i * Bs ^ (j - i + 1) * |iteratedDeriv (j - i) ψ₃ (Bs * (u - u'))|) :=
    integral_mono_of_nonneg (ae_of_all _ (fun u => abs_nonneg _)) hGint (ae_of_all _ hbound)
  have hstep2 : ∫ u, (∑ i ∈ Finset.range (j + 1),
        (j.choose i : ℝ) * c₁ i * Bs ^ (j - i + 1) * |iteratedDeriv (j - i) ψ₃ (Bs * (u - u'))|)
      = ∑ i ∈ Finset.range (j + 1),
          (j.choose i : ℝ) * c₁ i * Bs ^ (j - i) * ∫ x, |iteratedDeriv (j - i) ψ₃ x| := by
    rw [MeasureTheory.integral_finsetSum (Finset.range (j + 1)) (fun i _ => hKint i)]
    apply Finset.sum_congr rfl
    intro i _
    rw [MeasureTheory.integral_const_mul,
      integral_abs_iteratedDeriv_scaled_shift ψ₃ Bs u' (j - i),
      abs_of_pos (inv_pos.mpr hBs0)]
    have hpow : Bs ^ (j - i + 1) * Bs⁻¹ = Bs ^ (j - i) := by
      rw [pow_succ, mul_assoc, mul_inv_cancel₀ hBsne, mul_one]
    calc ((j.choose i : ℝ) * c₁ i * Bs ^ (j - i + 1)) * (Bs⁻¹ * ∫ x, |iteratedDeriv (j - i) ψ₃ x|)
        = ((j.choose i : ℝ) * c₁ i) * (Bs ^ (j - i + 1) * Bs⁻¹)
            * ∫ x, |iteratedDeriv (j - i) ψ₃ x| := by ring
      _ = (j.choose i : ℝ) * c₁ i * Bs ^ (j - i) * ∫ x, |iteratedDeriv (j - i) ψ₃ x| := by rw [hpow]
  have hstep3 : (∑ i ∈ Finset.range (j + 1),
        (j.choose i : ℝ) * c₁ i * Bs ^ (j - i) * ∫ x, |iteratedDeriv (j - i) ψ₃ x|)
      ≤ (∑ i ∈ Finset.range (j + 1),
          (j.choose i : ℝ) * c₁ i * ∫ x, |iteratedDeriv (j - i) ψ₃ x|) * Bs ^ j := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i _
    have hc : 0 ≤ c₁ i := le_trans (abs_nonneg _) (hc₁ i 0)
    have hI : 0 ≤ ∫ x, |iteratedDeriv (j - i) ψ₃ x| := integral_nonneg (fun x => abs_nonneg _)
    have hD : 0 ≤ (j.choose i : ℝ) * c₁ i * ∫ x, |iteratedDeriv (j - i) ψ₃ x| :=
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hc) hI
    have hle : Bs ^ (j - i) ≤ Bs ^ j := pow_le_pow_right₀ hBs (Nat.sub_le j i)
    calc (j.choose i : ℝ) * c₁ i * Bs ^ (j - i) * ∫ x, |iteratedDeriv (j - i) ψ₃ x|
        = ((j.choose i : ℝ) * c₁ i * ∫ x, |iteratedDeriv (j - i) ψ₃ x|) * Bs ^ (j - i) := by ring
      _ ≤ ((j.choose i : ℝ) * c₁ i * ∫ x, |iteratedDeriv (j - i) ψ₃ x|) * Bs ^ j :=
          mul_le_mul_of_nonneg_left hle hD
  exact le_trans hstep1 (le_trans (le_of_eq hstep2) hstep3)

/-- **`L¹` bound for the derivatives of a scaled bump product.** For `B_s ≥ 1`, the `j`-th
derivative of `u ↦ ψ₁ u · (B_s · ψ₃ (B_s · (u - u')))` has `L¹`-norm at most
`(Σ_{i ≤ j} C(j,i) c₁ i ∫|ψ₃^(j-i)|) · B_s^j`, where `c₁ i` bounds `|ψ₁^(i)|` and `ψ₁, ψ₃` are
`C^∞` with compact support.  The `B_s^j` is where the Fourier decay of the smoothing comes from:
differentiating the scaled bump costs `B_s`, while the scaling contributes `B_s^{-1}` to the `L¹`
norm.  Suggested route: `iteratedDeriv_mul` (Leibniz) + `iteratedDeriv_comp_sub_const` +
`iteratedDeriv_comp_const_mul`/`iteratedDeriv_const_mul_field` for
`(ψ₃(B_s ·))^(m) = B_s^m ψ₃^(m)(B_s ·)`, then `integral_mono` and
`Measure.integral_comp_mul_left` (`∫ u, g (B_s * u) = |B_s⁻¹| * ∫ g`). -/
theorem integral_iteratedDeriv_scaled_le
    {ψ₁ ψ₃ : ℝ → ℝ} {c₁ : ℕ → ℝ} (hc₁ : ∀ i x, |iteratedDeriv i ψ₁ x| ≤ c₁ i)
    (h₁ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ₁) (h₁cs : HasCompactSupport ψ₁)
    (h₃ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ₃) (h₃cs : HasCompactSupport ψ₃)
    {Bs : ℝ} (hBs : 1 ≤ Bs) (u' : ℝ) (j : ℕ) :
    ∫ u, ‖iteratedDeriv j (fun u : ℝ => ((ψ₁ u * (Bs * ψ₃ (Bs * (u - u'))) : ℝ) : ℂ)) u‖ ≤
      (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * c₁ i * ∫ x, |iteratedDeriv (j - i) ψ₃ x|)
        * Bs ^ j := by
  have hFcd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u : ℝ => ψ₁ u * (Bs * ψ₃ (Bs * (u - u')))) := by fun_prop
  have hkey : ∀ u, ‖iteratedDeriv j (fun u : ℝ =>
        ((ψ₁ u * (Bs * ψ₃ (Bs * (u - u'))) : ℝ) : ℂ)) u‖
      = |iteratedDeriv j (fun u : ℝ => ψ₁ u * (Bs * ψ₃ (Bs * (u - u')))) u| := by
    intro u
    rw [iteratedDeriv_ofReal_comp hFcd j u]
    simp
  rw [show (fun u : ℝ => ‖iteratedDeriv j (fun u : ℝ =>
          ((ψ₁ u * (Bs * ψ₃ (Bs * (u - u'))) : ℝ) : ℂ)) u‖)
        = (fun u : ℝ => |iteratedDeriv j (fun u : ℝ =>
            ψ₁ u * (Bs * ψ₃ (Bs * (u - u')))) u|) from funext hkey]
  exact integral_abs_iteratedDeriv_mul_scaled_le hc₁ h₁ h₁cs h₃ h₃cs hBs u' j


open Complex Finset MeasureTheory
open scoped BigOperators FourierTransform
open Submission.GM (Rfun energy Separated)

section Helpers

/-- If `IsBumpAtOne ψ C` then `ψ` vanishes off `[1/C, C]`. -/
theorem bumpAtOne_eq_zero_of_notMem {ψ : ℝ → ℝ} {C : ℝ} (h : IsBumpAtOne ψ C) {x : ℝ}
    (hx : x ∉ Set.Icc (1 / C) C) : ψ x = 0 :=
  by_contra fun hne => hx (h.2.2.1 x hne)

theorem bumpAtOne_hasCompactSupport {ψ : ℝ → ℝ} {C : ℝ} (h : IsBumpAtOne ψ C) :
    HasCompactSupport ψ :=
  HasCompactSupport.intro (K := Set.Icc (1 / C) C) isCompact_Icc fun x hx =>
    bumpAtOne_eq_zero_of_notMem h hx

theorem bumpAtZero_eq_zero_of_notMem {ψ : ℝ → ℝ} {C : ℝ} (h : IsBumpAtZero ψ C) {x : ℝ}
    (hx : x ∉ Set.Icc (-C) C) : ψ x = 0 := by
  refine by_contra fun hne => hx ?_
  have hx' := h.2.2.1 x hne
  rw [abs_le] at hx'
  exact ⟨hx'.1, hx'.2⟩

theorem bumpAtZero_hasCompactSupport {ψ : ℝ → ℝ} {C : ℝ} (h : IsBumpAtZero ψ C) :
    HasCompactSupport ψ :=
  HasCompactSupport.intro (K := Set.Icc (-C) C) isCompact_Icc fun x hx =>
    bumpAtZero_eq_zero_of_notMem h hx

end Helpers

section Master

/-- The Fourier character `𝓮(-ξu) = exp(-2πiξu)` as a complex number. -/
private noncomputable def chr (ξ : ℝ) (u : ℝ) : ℂ := (Real.fourierChar (-(ξ * u)) : ℂ)

/-- The smoothed bump `u ↦ ψ₁ u · (B_s · ψ₃ (B_s · (u - u')))`, as a complex-valued function. -/
private noncomputable def smFun (ψ₁ ψ₃ : ℝ → ℝ) (Bs u' : ℝ) : ℝ → ℂ :=
  fun u => ((ψ₁ u * (Bs * ψ₃ (Bs * (u - u'))) : ℝ) : ℂ)

/-- The weight `ψ₂ u · ‖Rfun W u‖²` as a complex-valued function. -/
private noncomputable def wtFun (W : Finset ℝ) (ψ₂ : ℝ → ℝ) : ℝ → ℂ :=
  fun u => ((ψ₂ u * ‖Rfun W u‖ ^ 2 : ℝ) : ℂ)

/-- The double integrand of `𝓕 (ψ₁ · RtildeSq)`. -/
private noncomputable def dblFun (ξ : ℝ) (W : Finset ℝ) (ψ₁ ψ₂ ψ₃ : ℝ → ℝ) (Bs : ℝ)
    (u u' : ℝ) : ℂ :=
  chr ξ u * (smFun ψ₁ ψ₃ Bs u' u * wtFun W ψ₂ u')

private theorem smFun_contDiff {ψ₁ ψ₃ : ℝ → ℝ}
    (h₁ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ₁)
    (h₃ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ₃) (Bs u' : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (smFun ψ₁ ψ₃ Bs u') := by
  have hprod : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u : ℝ => ψ₁ u * (Bs * ψ₃ (Bs * (u - u')))) := by
    refine h₁.mul (contDiff_const.mul ?_)
    exact h₃.comp (contDiff_const.mul (contDiff_id.sub contDiff_const))
  unfold smFun
  exact Complex.ofRealCLM.contDiff.comp hprod

private theorem smFun_hasCompactSupport {ψ₁ : ℝ → ℝ} {C₀ : ℝ} (h₁ : IsBumpAtOne ψ₁ C₀)
    (ψ₃ : ℝ → ℝ) (Bs u' : ℝ) :
    HasCompactSupport (smFun ψ₁ ψ₃ Bs u') := by
  refine HasCompactSupport.intro (K := Set.Icc (1 / C₀) C₀) isCompact_Icc fun u hu => ?_
  unfold smFun
  rw [bumpAtOne_eq_zero_of_notMem h₁ hu]
  simp

private theorem wtFun_continuous {ψ₂ : ℝ → ℝ} {C₀ : ℝ} (hC₀ : 1 ≤ C₀)
    (h₂ : IsBumpAtOne ψ₂ C₀) (W : Finset ℝ) : Continuous (wtFun W ψ₂) := by
  unfold wtFun
  exact Complex.continuous_ofReal.comp (gSq_continuous ψ₂ C₀ hC₀ h₂ W)

private theorem wtFun_hasCompactSupport {ψ₂ : ℝ → ℝ} {C₀ : ℝ} (h₂ : IsBumpAtOne ψ₂ C₀)
    (W : Finset ℝ) : HasCompactSupport (wtFun W ψ₂) := by
  refine HasCompactSupport.intro (K := Set.Icc (1 / C₀) C₀) isCompact_Icc fun u hu => ?_
  unfold wtFun
  rw [bumpAtOne_eq_zero_of_notMem h₂ hu]
  simp

private theorem dblFun_continuous {ψ₁ ψ₂ ψ₃ : ℝ → ℝ} {C₀ : ℝ} (hC₀ : 1 ≤ C₀)
    (h₁ : IsBumpAtOne ψ₁ C₀) (h₂ : IsBumpAtOne ψ₂ C₀) (h₃ : IsBumpAtZero ψ₃ C₀)
    (ξ : ℝ) (W : Finset ℝ) (Bs : ℝ) :
    Continuous (Function.uncurry (dblFun ξ W ψ₁ ψ₂ ψ₃ Bs)) := by
  have hch : Continuous fun p : ℝ × ℝ => (Real.fourierChar (-(ξ * p.1)) : ℂ) :=
    (continuous_subtype_val.comp
      (Real.continuous_fourierChar.comp ((continuous_const.mul continuous_id).neg))).comp
        continuous_fst
  have ha : Continuous fun p : ℝ × ℝ => ((ψ₁ p.1 : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (h₁.1.continuous.comp continuous_fst)
  have hb : Continuous fun p : ℝ × ℝ => ((Bs * ψ₃ (Bs * (p.1 - p.2)) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp <| (continuous_const.mul h₃.1.continuous).comp
      (by fun_prop : Continuous fun p : ℝ × ℝ => Bs * (p.1 - p.2))
  have hw' : Continuous fun p : ℝ × ℝ => wtFun W ψ₂ p.2 :=
    (wtFun_continuous hC₀ h₂ W).comp continuous_snd
  have hprod : Continuous fun p : ℝ × ℝ =>
      (Real.fourierChar (-(ξ * p.1)) : ℂ) * (((ψ₁ p.1 * (Bs * ψ₃ (Bs * (p.1 - p.2))) : ℝ)) : ℂ)
        * wtFun W ψ₂ p.2 := by
    refine ((hch.mul ?_).mul hw')
    exact (ha.mul hb).congr (fun p => by simp only [Pi.mul_apply]; push_cast; ring)
  refine hprod.congr ?_
  intro p
  simp only [Function.uncurry, dblFun, chr, smFun]
  push_cast
  ring

private theorem dblFun_hasCompactSupport {ψ₁ ψ₂ ψ₃ : ℝ → ℝ} {C₀ : ℝ} (hC₀ : 1 ≤ C₀)
    (h₁ : IsBumpAtOne ψ₁ C₀) (h₂ : IsBumpAtOne ψ₂ C₀) (ξ : ℝ) (W : Finset ℝ) (Bs : ℝ) :
    HasCompactSupport (Function.uncurry (dblFun ξ W ψ₁ ψ₂ ψ₃ Bs)) := by
  refine HasCompactSupport.intro
    (K := Set.Icc (1 / C₀ : ℝ) C₀ ×ˢ Set.Icc (1 / C₀ - C₀ : ℝ) (C₀ + C₀))
    (isCompact_Icc.prod isCompact_Icc) fun p hp => ?_
  obtain ⟨u, u'⟩ := p
  have hsub : Set.Icc (1 / C₀ : ℝ) C₀ ⊆ Set.Icc (1 / C₀ - C₀ : ℝ) (C₀ + C₀) := by
    intro x hx
    exact ⟨by linarith [hx.1, hC₀], by linarith [hx.2, hC₀]⟩
  have hp' : u ∉ Set.Icc (1 / C₀ : ℝ) C₀ ∨ u' ∉ Set.Icc (1 / C₀ - C₀ : ℝ) (C₀ + C₀) := by
    by_contra h
    rw [not_or, not_not, not_not] at h
    exact hp (by simp only [Set.mem_prod]; exact h)
  simp only [Function.uncurry, dblFun, chr, smFun, wtFun]
  rcases hp' with hu | hu
  · rw [bumpAtOne_eq_zero_of_notMem h₁ hu]
    simp
  · rw [show ψ₂ u' = 0 from bumpAtOne_eq_zero_of_notMem h₂ (fun hc => hu (hsub hc))]
    simp

/-- **The core Fourier decay bound for `ψ₁ · RtildeSq`.** For `B_s = N·B ≥ 1`, every `j` and every
`ξ ≠ 0`,
`‖𝓕 (ψ₁ · RtildeSq W N B ψ₃ ψ₂) ξ‖ ≤ (∫ ψ₂‖Rfun W‖²) · (S_j · B_s^j) / (2π|ξ|)^j`,
where `S_j = Σ_{i≤j} C(j,i) c₁ i ∫|ψ₃^(j-i)|` and `c₁ i` bounds `|ψ₁^(i)|`.

Proof: write `f = ψ₁ · RtildeSq` and `RtildeSq u = ∫ B_s ψ₃(B_s(u-u')) g(u') du'` with
`g = ψ₂|R|²`; Fubini turns `𝓕 f ξ` into `∫ g(u') · 𝓕(u ↦ ψ₁ u B_s ψ₃(B_s(u-u')))(ξ) du'`, and the
inner Fourier transform decays like `B_s^j/|ξ|^j` because the `j`-th derivative of
`u ↦ ψ₁ u B_s ψ₃(B_s(u-u'))` has `L¹`-norm `≤ S_j B_s^j`. -/
theorem fourier_decay_RtildeSq {C₀ : ℝ} {ψ₁ ψ₂ ψ₃ : ℝ → ℝ} (hC₀ : 1 ≤ C₀)
    (h₁ : IsBumpAtOne ψ₁ C₀) (h₂ : IsBumpAtOne ψ₂ C₀) (h₃ : IsBumpAtZero ψ₃ C₀)
    {c₁ : ℕ → ℝ} (hc₁ : ∀ i x, |iteratedDeriv i ψ₁ x| ≤ c₁ i)
    (W : Finset ℝ) (N : ℕ) (B : ℝ) (hB : 1 ≤ (N : ℝ) * B) (j : ℕ) :
    ∀ ξ : ℝ, ξ ≠ 0 →
      ‖FourierTransform.fourier (fun u => ((ψ₁ u * RtildeSq W N B ψ₃ ψ₂ u : ℝ) : ℂ)) ξ‖ ≤
        (∫ u, ψ₂ u * ‖Rfun W u‖ ^ 2) *
          ((∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * c₁ i *
              ∫ x, |iteratedDeriv (j - i) ψ₃ x|) * ((N : ℝ) * B) ^ j) /
          (2 * Real.pi * |ξ|) ^ j := by
  intro ξ hξ
  set Bs : ℝ := (N : ℝ) * B with hBsdef
  have hBs1 : 1 ≤ Bs := hB
  set S : ℝ := ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * c₁ i *
      ∫ x, |iteratedDeriv (j - i) ψ₃ x| with hSdef
  -- integrability of the double integrand and Fubini
  have hdblint : Integrable (Function.uncurry (dblFun ξ W ψ₁ ψ₂ ψ₃ Bs)) (volume.prod volume) :=
    (dblFun_continuous hC₀ h₁ h₂ h₃ ξ W Bs).integrable_of_hasCompactSupport
      (dblFun_hasCompactSupport hC₀ h₁ h₂ ξ W Bs)
  have hFubini : (∫ u, ∫ u', dblFun ξ W ψ₁ ψ₂ ψ₃ Bs u u')
      = ∫ u', ∫ u, dblFun ξ W ψ₁ ψ₂ ψ₃ Bs u u' :=
    integral_integral_swap hdblint
  -- unfolding of `RtildeSq`
  have hRtd : ∀ u : ℝ, RtildeSq W N B ψ₃ ψ₂ u =
      ∫ u', Bs * ψ₃ (Bs * (u - u')) * (ψ₂ u' * ‖Rfun W u'‖ ^ 2) := by
    intro u
    rw [RtildeSq]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u' => ?_)
    simp only [hBsdef]
    ring
  -- the Fourier transform as a double integral
  have hbridge : FourierTransform.fourier (fun u => ((ψ₁ u * RtildeSq W N B ψ₃ ψ₂ u : ℝ) : ℂ)) ξ
      = ∫ u, ∫ u', dblFun ξ W ψ₁ ψ₂ ψ₃ Bs u u' := by
    have h1 : FourierTransform.fourier (fun u => ((ψ₁ u * RtildeSq W N B ψ₃ ψ₂ u : ℝ) : ℂ)) ξ
        = ∫ u, chr ξ u * ((ψ₁ u * RtildeSq W N B ψ₃ ψ₂ u : ℝ) : ℂ) := by
      rw [Real.fourier_eq]
      refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
      dsimp only
      simp only [chr, show inner ℝ u ξ = ξ * u from by simp]
      rw [Circle.smul_def, smul_eq_mul]
    rw [h1]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    dsimp only
    have h2 : ((ψ₁ u * RtildeSq W N B ψ₃ ψ₂ u : ℝ) : ℂ)
        = (ψ₁ u : ℂ) * ((RtildeSq W N B ψ₃ ψ₂ u : ℝ) : ℂ) := by push_cast; ring
    rw [h2, hRtd u]
    rw [show ((∫ u', Bs * ψ₃ (Bs * (u - u')) * (ψ₂ u' * ‖Rfun W u'‖ ^ 2) : ℝ) : ℂ)
        = ∫ u', ((Bs * ψ₃ (Bs * (u - u')) * (ψ₂ u' * ‖Rfun W u'‖ ^ 2) : ℝ) : ℂ)
        from integral_ofReal.symm]
    rw [← MeasureTheory.integral_const_mul]
    rw [← MeasureTheory.integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u' => ?_)
    dsimp only
    simp only [dblFun, chr, smFun, wtFun]
    push_cast
    ring
  -- the inner integral is the Fourier transform of the smoothed bump
  have hinner : ∀ u' : ℝ, (∫ u, dblFun ξ W ψ₁ ψ₂ ψ₃ Bs u u')
      = FourierTransform.fourier (smFun ψ₁ ψ₃ Bs u') ξ * wtFun W ψ₂ u' := by
    intro u'
    have h0 : (∫ u, dblFun ξ W ψ₁ ψ₂ ψ₃ Bs u u')
        = ∫ u, chr ξ u * smFun ψ₁ ψ₃ Bs u' u * wtFun W ψ₂ u' := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
      dsimp only
      simp only [dblFun]
      ring
    have h2 : (∫ u, chr ξ u * smFun ψ₁ ψ₃ Bs u' u)
        = FourierTransform.fourier (smFun ψ₁ ψ₃ Bs u') ξ := by
      rw [Real.fourier_eq]
      refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
      dsimp only
      simp only [chr, show inner ℝ u ξ = ξ * u from by simp]
      rw [Circle.smul_def, smul_eq_mul]
    rw [h0, MeasureTheory.integral_mul_const, h2]
  -- the decay bound for the smoothed bump
  have hsmdecay : ∀ u' : ℝ,
      ‖FourierTransform.fourier (smFun ψ₁ ψ₃ Bs u') ξ‖ ≤ S * Bs ^ j / (2 * Real.pi * |ξ|) ^ j := by
    intro u'
    have hdec := fourier_decay_explicit j (smFun_contDiff h₁.1 h₃.1 Bs u')
      (smFun_hasCompactSupport h₁ ψ₃ Bs u') hξ
    have hL1 := integral_iteratedDeriv_scaled_le (ψ₁ := ψ₁) (ψ₃ := ψ₃) (c₁ := c₁) hc₁
      h₁.1 (bumpAtOne_hasCompactSupport h₁) h₃.1 (bumpAtZero_hasCompactSupport h₃) hBs1 u' j
    have hden : 0 < (2 * Real.pi * |ξ|) ^ j := by
      have : 0 < |ξ| := abs_pos.mpr hξ
      positivity
    refine hdec.trans ?_
    refine div_le_div_of_nonneg_right ?_ hden.le
    rw [hSdef]
    exact hL1
  -- integrability of the inner integral, as a function of `u'`
  have hFint : Integrable (fun u' => ∫ u, dblFun ξ W ψ₁ ψ₂ ψ₃ Bs u u') volume := by
    have h := hdblint.integral_prod_right
    simpa [Function.uncurry] using h
  -- conclude
  rw [hbridge, hFubini]
  have hstep1 : ‖∫ u', ∫ u, dblFun ξ W ψ₁ ψ₂ ψ₃ Bs u u'‖
      ≤ ∫ u', ‖∫ u, dblFun ξ W ψ₁ ψ₂ ψ₃ Bs u u'‖ := norm_integral_le_integral_norm _
  have hwtint : Integrable (fun u' => ‖wtFun W ψ₂ u'‖) volume :=
    ((wtFun_continuous hC₀ h₂ W).integrable_of_hasCompactSupport
      (wtFun_hasCompactSupport h₂ W)).norm
  have hstep2 : (∫ u', ‖∫ u, dblFun ξ W ψ₁ ψ₂ ψ₃ Bs u u'‖)
      ≤ ∫ u', (S * Bs ^ j / (2 * Real.pi * |ξ|) ^ j) * ‖wtFun W ψ₂ u'‖ := by
    refine integral_mono hFint.norm (hwtint.const_mul _) fun u' => ?_
    dsimp only
    rw [hinner u', norm_mul]
    exact mul_le_mul_of_nonneg_right (hsmdecay u') (norm_nonneg _)
  have hstep3 : (∫ u', (S * Bs ^ j / (2 * Real.pi * |ξ|) ^ j) * ‖wtFun W ψ₂ u'‖)
      = (S * Bs ^ j / (2 * Real.pi * |ξ|) ^ j) * ∫ u', ‖wtFun W ψ₂ u'‖ :=
    MeasureTheory.integral_const_mul _ _
  have hstep4 : (∫ u', ‖wtFun W ψ₂ u'‖) = ∫ u, ψ₂ u * ‖Rfun W u‖ ^ 2 := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    dsimp only
    have hnorm : ‖wtFun W ψ₂ u‖ = |ψ₂ u * ‖Rfun W u‖ ^ 2| := by
      unfold wtFun
      simp
    rw [hnorm, abs_of_nonneg (mul_nonneg (h₂.2.1 u) (sq_nonneg _))]
  calc ‖∫ u', ∫ u, dblFun ξ W ψ₁ ψ₂ ψ₃ Bs u u'‖
      ≤ ∫ u', ‖∫ u, dblFun ξ W ψ₁ ψ₂ ψ₃ Bs u u'‖ := hstep1
    _ ≤ (S * Bs ^ j / (2 * Real.pi * |ξ|) ^ j) * ∫ u', ‖wtFun W ψ₂ u'‖ :=
        hstep2.trans (le_of_eq hstep3)
    _ = (S * Bs ^ j / (2 * Real.pi * |ξ|) ^ j) * ∫ u, ψ₂ u * ‖Rfun W u‖ ^ 2 := by
        rw [hstep4]
    _ = (∫ u, ψ₂ u * ‖Rfun W u‖ ^ 2) * (S * Bs ^ j) / (2 * Real.pi * |ξ|) ^ j := by
        rw [hBsdef]; ring

end Master

section Assembly

/-- The smoothed `|R|²` is strongly measurable in `u` (its integral kernel is continuous). -/
private theorem RtildeSq_stronglyMeasurable {ψ₂ ψ₃ : ℝ → ℝ} {C₀ : ℝ} (hC₀ : 1 ≤ C₀)
    (h₂ : IsBumpAtOne ψ₂ C₀) (h₃ : IsBumpAtZero ψ₃ C₀) (W : Finset ℝ) (N : ℕ) (B : ℝ) :
    StronglyMeasurable (fun u : ℝ => RtildeSq W N B ψ₃ ψ₂ u) := by
  have hcont : Continuous (fun p : ℝ × ℝ =>
      (N : ℝ) * B * ψ₃ ((N : ℝ) * B * (p.1 - p.2)) * (ψ₂ p.2 * ‖Rfun W p.2‖ ^ 2)) := by
    have h1 : Continuous fun p : ℝ × ℝ =>
        (N : ℝ) * B * ψ₃ ((N : ℝ) * B * (p.1 - p.2)) :=
      (continuous_const : Continuous fun _ : ℝ × ℝ => (N : ℝ) * B).mul
        (h₃.1.continuous.comp (by fun_prop))
    exact h1.mul ((gSq_continuous ψ₂ C₀ hC₀ h₂ W).comp continuous_snd)
  have h := hcont.stronglyMeasurable.integral_prod_right' (ν := volume)
  simpa [RtildeSq, mul_assoc] using h

/-- **GM 8.4** (Fourier decay of smoothings of `|R|²`), in the form needed by Prop 10.1.

`∃ c` is placed *after* the bumps (so `c` may depend on the chosen bumps, as in the source, where the
implied constants depend on the fixed bumps), and the hypothesis on the smoothing parameter is
`1 ≤ N * B ≤ M N`: `RtildeSq` smooths at frequency `N * B`, so the source's `B_smoothing ⪅ T` reads
`N * B ≤ M N`.

For every `ε > 0` and every `C₀ ≥ 1`, every pair of bumps `ψ₁, ψ₂` supported on `u ∈ [1/C₀, C₀]` with
`ψ₁ 1 = ψ₂ 1 = 1` and every bump `ψ₃` supported on `|x| ≤ C₀` with `ψ₃ 0 = 1` (all smooth,
non-negative, with bounded derivatives: the predicates `IsBumpAtOne`/`IsBumpAtZero` in `Defs.lean`),
there is `c : ℕ → ℝ → ℝ` such that for every `N ≥ 1`, every `W ⊆ [0, M N]` that is
`(M N)^ε`-separated, every `B` with `1 ≤ N B` and `N B ≤ M N`, every `j`, `η > 0` and `ξ ≠ 0`:

`‖𝓕 (ψ₁ · RtildeSq W N B ψ₃ ψ₂) ξ‖ ≤ c j η · (M N)^η · (M N/|ξ|)^j · sup_u (ψ₁ u · RtildeSq W N B ψ₃ ψ₂ u)`

where `RtildeSq W N B ψ₃ ψ₂ u = ∫ (N B) ψ₃(N B (u-u')) ψ₂ u' ‖R(u')‖² du'` is GM (7.5) without the
square root (so `f = ψ₁ |R̃|²`), and the displayed inequality is exactly the decay hypothesis of
`AffineStatement` with `T = M N`.

Proof (paper): write `f = ψ₁ f₁` with `f₁ = (B_s ψ₃(B_s ·)) * (ψ₂ |R|²)`, `B_s = N B`.  Then
`f̂ = ψ̂₁ * (ψ̂₃(·/B_s) ĝ)` with `‖ĝ‖_∞ ≤ ∫ ψ₂ |R|² ≪ |W|²`; the derivative bounds on `ψ₃` give
`‖ψ̂₃(ξ/B_s)‖ ⪅_j (B_s/|ξ|)^j`, hence `‖f̂₁(ξ)‖ ⪅_j |W|² (B_s/|ξ|)^j`; convolving with the fixed
bump `ψ₁` preserves this (split `∫|ψ̂₁(ξ-y)| ‖f̂₁(y)‖ dy` at `|y| = |ξ|/2` and use `B_s ≥ 1`).
Finally `f(1) ⪆ |W|² B_s/T`: `ψ₂ ≫ 1` near `1`, `ψ₃ ≫ 1` near `0`, `ψ₁(1) = 1`, and
`‖R(u)‖ ≥ |W|/2` for `|log |u|| ≤ 1/(2T)` (`Defs.lean`, `Rfun_lower_near_one`), so
`|W|² B_s^j ≤ T^j sup f` because `B_s ≤ T = M N`. -/
theorem lemma84 :
    ∀ ε : ℝ, 0 < ε → ∀ C₀ : ℝ, 1 ≤ C₀ →
    ∀ (ψ₁ ψ₂ ψ₃ : ℝ → ℝ), Work.GM.S3.IsBumpAtOne ψ₁ C₀ →
      Work.GM.S3.IsBumpAtOne ψ₂ C₀ → Work.GM.S3.IsBumpAtZero ψ₃ C₀ →
    ∃ c : ℕ → ℝ → ℝ,
      ∀ N : ℕ, 1 ≤ N → ∀ W : Finset ℝ,
        (∀ t ∈ W, t ∈ Set.Icc 0 (Submission.LargeValues.M N)) →
        Submission.GM.Separated W ((Submission.LargeValues.M N) ^ ε) →
      ∀ B : ℝ, 1 ≤ (N : ℝ) * B → (N : ℝ) * B ≤ Submission.LargeValues.M N →
      ∀ (j : ℕ) (η : ℝ), 0 < η → ∀ ξ : ℝ, ξ ≠ 0 →
        ‖FourierTransform.fourier
            (fun u => ((ψ₁ u * Work.GM.S3.RtildeSq W N B ψ₃ ψ₂ u : ℝ) : ℂ)) ξ‖ ≤
          c j η * (Submission.LargeValues.M N) ^ η *
            (Submission.LargeValues.M N / |ξ|) ^ j *
            sSup (Set.range (fun u => ψ₁ u * Work.GM.S3.RtildeSq W N B ψ₃ ψ₂ u)) := by
  intro ε hε C₀ hC₀ ψ₁ ψ₂ ψ₃ h₁ h₂ h₃
  let c₁ : ℕ → ℝ := fun i => Classical.choose (h₁.2.2.2.2 i)
  have hc₁ : ∀ i x, |iteratedDeriv i ψ₁ x| ≤ c₁ i :=
    fun i x => (Classical.choose_spec (h₁.2.2.2.2 i)).2 x
  have hc₁nn : ∀ i, 0 ≤ c₁ i := fun i => (Classical.choose_spec (h₁.2.2.2.2 i)).1
  obtain ⟨Cint, hCintpos, hCint⟩ := integral_gSq_le ψ₂ C₀ hC₀ h₂
  obtain ⟨cL, hcLpos, hL⟩ := RtildeSq_one_lower ψ₂ ψ₃ C₀ hC₀ h₂ h₃
  let Sfun : ℕ → ℝ := fun j => ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * c₁ i *
      ∫ x, |iteratedDeriv (j - i) ψ₃ x|
  have hSfunnn : ∀ j, 0 ≤ Sfun j := by
    intro j
    refine Finset.sum_nonneg fun i hi => ?_
    exact mul_nonneg (mul_nonneg (by positivity) (hc₁nn i))
      (integral_nonneg fun x => abs_nonneg _)
  refine ⟨fun j _ => max 1 (Cint * Sfun j / (cL * (2 * Real.pi) ^ j) + C₀), ?_⟩
  intro N hN W hW hSep B hB hBT j η hη ξ hξ
  have hcfun : (fun j _ => max 1 (Cint * Sfun j / (cL * (2 * Real.pi) ^ j) + C₀)) j η
      = max 1 (Cint * Sfun j / (cL * (2 * Real.pi) ^ j) + C₀) := rfl
  rw [hcfun]
  set T : ℝ := Submission.LargeValues.M N with hTdef
  set Bs : ℝ := (N : ℝ) * B with hBsdef
  have hBs1 : 1 ≤ Bs := hB
  have hBspos : 0 < Bs := lt_of_lt_of_le one_pos hBs1
  have hBpos : 0 < B := by
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    nlinarith [hB]
  have hT1 : 1 ≤ T := by rw [hTdef]; exact Submission.LargeValues.M_ge_one hN
  have hTpos : 0 < T := lt_of_lt_of_le one_pos hT1
  have hBsT : Bs ≤ T := hBT
  set fR : ℝ → ℝ := fun u => ψ₁ u * RtildeSq W N B ψ₃ ψ₂ u with hfRdef
  set f : ℝ → ℂ := fun u => ((fR u : ℝ) : ℂ) with hfdef
  have hf_eq : f = fun u => ((ψ₁ u * RtildeSq W N B ψ₃ ψ₂ u : ℝ) : ℂ) := by
    funext u; simp only [hfdef, hfRdef]
  set sF : ℝ := sSup (Set.range fR) with hsFdef
  have hRnn : ∀ u, 0 ≤ RtildeSq W N B ψ₃ ψ₂ u := fun u =>
    RtildeSq_nonneg W N B ψ₃ ψ₂ u h₃.2.1 h₂.2.1 hBpos.le
  have hfRnn : ∀ u, 0 ≤ fR u := fun u => mul_nonneg (h₁.2.1 u) (hRnn u)
  have hbdd : BddAbove (Set.range fR) := by
    rw [hfRdef]
    exact bddAbove_range_RtildeSq ψ₁ ψ₂ ψ₃ C₀ h₁ h₂ h₃ W N B (le_trans zero_le_one hB)
  have hsup1 : fR 1 ≤ sF := by
    rw [hsFdef]; exact le_csSup hbdd (Set.mem_range_self 1)
  have hsupnn : 0 ≤ sF := le_trans (hfRnn 1) hsup1
  have hle : ∀ u, fR u ≤ sF := fun u => by
    rw [hsFdef]; exact le_csSup hbdd (Set.mem_range_self u)
  have hfRone : fR 1 = RtildeSq W N B ψ₃ ψ₂ 1 := by
    simp only [hfRdef, h₁.2.2.2.1, one_mul]
  have hccnn : 0 ≤ max 1 (Cint * Sfun j / (cL * (2 * Real.pi) ^ j) + C₀) :=
    le_trans zero_le_one (le_max_left _ _)
  have hWT : ∀ t ∈ W, |t| ≤ T := by
    intro t ht
    have h := hW t ht
    rw [Set.mem_Icc] at h
    rw [abs_le]
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  have hlow : cL * (W.card : ℝ) ^ 2 * Bs / T ≤ sF := by
    have h := hL W N T B hT1 hWT hB hBsT
    rw [← hfRone] at h
    exact h.trans hsup1
  by_cases hj0 : j = 0
  · subst hj0
    have hRsm : StronglyMeasurable (fun u : ℝ => RtildeSq W N B ψ₃ ψ₂ u) :=
      RtildeSq_stronglyMeasurable hC₀ h₂ h₃ W N B
    have hfRsm : StronglyMeasurable fR := by
      rw [hfRdef]
      exact h₁.1.continuous.stronglyMeasurable.mul hRsm
    have hvol : volume (Set.Icc (1 / C₀ : ℝ) C₀) ≠ ⊤ := by
      rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
    have hDint : Integrable (fun u : ℝ =>
        (Set.Icc (1 / C₀ : ℝ) C₀).indicator (fun _ => sF) u) volume := by
      rw [integrable_indicator_iff (s := Set.Icc (1 / C₀ : ℝ) C₀) measurableSet_Icc]
      exact integrableOn_const hvol (by simp)
    have hfRint : Integrable fR volume := by
      refine Integrable.mono' hDint hfRsm.aestronglyMeasurable ?_
      filter_upwards with u
      by_cases hu : u ∈ Set.Icc (1 / C₀ : ℝ) C₀
      · rw [Set.indicator_of_mem hu, Real.norm_eq_abs, abs_of_nonneg (hfRnn u)]
        exact hle u
      · rw [Set.indicator_of_notMem hu]
        have h0 : fR u = 0 := by
          simp only [hfRdef, bumpAtOne_eq_zero_of_notMem h₁ hu, zero_mul]
        rw [h0, norm_zero]
    have hbound : ∫ u, fR u ≤ (C₀ - 1 / C₀) * sF := by
      have hA : (0 : ℝ) ≤ C₀ - 1 / C₀ := by
        have h1 : 1 / C₀ ≤ 1 := by
          simpa using one_div_le_one_div_of_le (show (0 : ℝ) < 1 by norm_num) hC₀
        linarith
      have h := integral_mono hfRint hDint (fun u => ?_)
      · rw [MeasureTheory.integral_indicator_const (s := Set.Icc (1 / C₀ : ℝ) C₀) sF
            measurableSet_Icc, Real.volume_real_Icc, max_eq_left hA, smul_eq_mul] at h
        exact h
      · by_cases hu : u ∈ Set.Icc (1 / C₀ : ℝ) C₀
        · rw [Set.indicator_of_mem hu]; exact hle u
        · rw [Set.indicator_of_notMem hu]
          have h0 : fR u = 0 := by
            simp only [hfRdef, bumpAtOne_eq_zero_of_notMem h₁ hu, zero_mul]
          rw [h0]
    have hmain : ‖𝓕 f ξ‖ ≤ C₀ * sF := by
      rw [hf_eq]
      have hnorm : ‖𝓕 (fun u => ((ψ₁ u * RtildeSq W N B ψ₃ ψ₂ u : ℝ) : ℂ)) ξ‖
          ≤ ∫ u, ‖((ψ₁ u * RtildeSq W N B ψ₃ ψ₂ u : ℝ) : ℂ)‖ := by
        rw [Real.fourier_eq]
        refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
        refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
        dsimp only
        rw [Circle.norm_smul]
      refine hnorm.trans ?_
      calc ∫ u, ‖((ψ₁ u * RtildeSq W N B ψ₃ ψ₂ u : ℝ) : ℂ)‖
          = ∫ u, fR u := by
            refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
            dsimp only
            have h : ‖((ψ₁ u * RtildeSq W N B ψ₃ ψ₂ u : ℝ) : ℂ)‖ = fR u := by
              rw [hfRdef, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hfRnn u)]
            exact h
        _ ≤ C₀ * sF :=
            hbound.trans (mul_le_mul_of_nonneg_right (sub_le_self _ (by positivity)) hsupnn)
    have hKnn : 0 ≤ Cint * Sfun 0 / (cL * (2 * Real.pi) ^ 0) :=
      div_nonneg (mul_nonneg hCintpos.le (hSfunnn 0)) (by positivity)
    have hcc : C₀ ≤ max 1 (Cint * Sfun 0 / (cL * (2 * Real.pi) ^ 0) + C₀) :=
      le_trans (le_add_of_nonneg_left hKnn) (le_max_right _ _)
    have hTη : 1 ≤ T ^ η := Real.one_le_rpow hT1 hη.le
    calc ‖𝓕 f ξ‖ ≤ C₀ * sF := hmain
      _ ≤ max 1 (Cint * Sfun 0 / (cL * (2 * Real.pi) ^ 0) + C₀) * sF :=
          mul_le_mul_of_nonneg_right hcc hsupnn
      _ ≤ max 1 (Cint * Sfun 0 / (cL * (2 * Real.pi) ^ 0) + C₀) * T ^ η * sF := by
          have h1 : max 1 (Cint * Sfun 0 / (cL * (2 * Real.pi) ^ 0) + C₀) * 1 ≤
              max 1 (Cint * Sfun 0 / (cL * (2 * Real.pi) ^ 0) + C₀) * T ^ η :=
            mul_le_mul_of_nonneg_left hTη hccnn
          calc max 1 (Cint * Sfun 0 / (cL * (2 * Real.pi) ^ 0) + C₀) * sF
              = (max 1 (Cint * Sfun 0 / (cL * (2 * Real.pi) ^ 0) + C₀) * 1) * sF := by ring
            _ ≤ (max 1 (Cint * Sfun 0 / (cL * (2 * Real.pi) ^ 0) + C₀) * T ^ η) * sF :=
                mul_le_mul h1 le_rfl hsupnn (by positivity)
            _ = max 1 (Cint * Sfun 0 / (cL * (2 * Real.pi) ^ 0) + C₀) * T ^ η * sF := by ring
      _ = max 1 (Cint * Sfun 0 / (cL * (2 * Real.pi) ^ 0) + C₀) * T ^ η *
            (T / |ξ|) ^ 0 * sF := by rw [pow_zero]; ring
  · have hj1 : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj0
    refine (fourier_decay_RtildeSq hC₀ h₁ h₂ h₃ hc₁ W N B hB j ξ hξ).trans ?_
    have hA0 : ∫ u, ψ₂ u * ‖Rfun W u‖ ^ 2 ≤ Cint * (W.card : ℝ) ^ 2 := hCint W
    have hSnn : 0 ≤ Sfun j := hSfunnn j
    have hBspow : 0 < Bs ^ j := pow_pos hBspos j
    have hden : 0 < (2 * Real.pi * |ξ|) ^ j := by
      have hξpos : 0 < |ξ| := abs_pos.mpr hξ
      positivity
    have hWB : (W.card : ℝ) ^ 2 * Bs ^ j ≤ T ^ j * sF / cL := by
      have h1 : cL * (W.card : ℝ) ^ 2 * Bs ≤ T * sF := by
        have h := (div_le_iff₀ hTpos).mp hlow
        linarith [h]
      have h1b : (W.card : ℝ) ^ 2 * Bs ≤ T * sF / cL :=
        (le_div_iff₀ hcLpos).mpr (by linarith [h1])
      have hpow : Bs ^ (j - 1) ≤ T ^ (j - 1) := pow_le_pow_left₀ hBspos.le hBsT (j - 1)
      have hBsj : Bs ^ j = Bs * Bs ^ (j - 1) := by
        rw [← pow_succ']; congr 1; omega
      have hTj : T ^ j = T * T ^ (j - 1) := by
        rw [← pow_succ']; congr 1; omega
      calc (W.card : ℝ) ^ 2 * Bs ^ j = ((W.card : ℝ) ^ 2 * Bs) * Bs ^ (j - 1) := by
            rw [hBsj]; ring
        _ ≤ (T * sF / cL) * T ^ (j - 1) :=
            mul_le_mul h1b hpow (by positivity) (by positivity)
        _ = T ^ j * sF / cL := by rw [hTj]; ring
    calc (∫ u, ψ₂ u * ‖Rfun W u‖ ^ 2) * (Sfun j * Bs ^ j) / (2 * Real.pi * |ξ|) ^ j
        ≤ (Cint * (W.card : ℝ) ^ 2) * (Sfun j * Bs ^ j) / (2 * Real.pi * |ξ|) ^ j := by
          refine div_le_div_of_nonneg_right ?_ hden.le
          exact mul_le_mul_of_nonneg_right hA0 (mul_nonneg hSnn hBspow.le)
      _ = (Cint * Sfun j / (2 * Real.pi * |ξ|) ^ j) * ((W.card : ℝ) ^ 2 * Bs ^ j) := by
          rw [div_eq_mul_inv]; ring
      _ ≤ (Cint * Sfun j / (2 * Real.pi * |ξ|) ^ j) * (T ^ j * sF / cL) := by
          refine mul_le_mul_of_nonneg_left hWB ?_
          positivity
      _ = (Cint * Sfun j / (cL * (2 * Real.pi) ^ j)) * (T / |ξ|) ^ j * sF := by
          have h1 : (2 * Real.pi * |ξ|) ^ j = (2 * Real.pi) ^ j * |ξ| ^ j := by rw [mul_pow]
          rw [h1, div_eq_mul_inv, div_eq_mul_inv, div_pow, div_eq_mul_inv, mul_inv, mul_inv]
          ring_nf
      _ ≤ max 1 (Cint * Sfun j / (cL * (2 * Real.pi) ^ j) + C₀) * T ^ η * (T / |ξ|) ^ j * sF := by
          have hxnn : 0 ≤ (T / |ξ|) ^ j := by positivity
          have hK : Cint * Sfun j / (cL * (2 * Real.pi) ^ j) ≤
              max 1 (Cint * Sfun j / (cL * (2 * Real.pi) ^ j) + C₀) := by
            have h := le_max_right (1 : ℝ) (Cint * Sfun j / (cL * (2 * Real.pi) ^ j) + C₀)
            linarith
          have hTη : 1 ≤ T ^ η := Real.one_le_rpow hT1 hη.le
          calc Cint * Sfun j / (cL * (2 * Real.pi) ^ j) * (T / |ξ|) ^ j * sF
              ≤ max 1 (Cint * Sfun j / (cL * (2 * Real.pi) ^ j) + C₀) * (T / |ξ|) ^ j * sF :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK hxnn) hsupnn
            _ = max 1 (Cint * Sfun j / (cL * (2 * Real.pi) ^ j) + C₀) * 1 *
                  (T / |ξ|) ^ j * sF := by ring
            _ ≤ max 1 (Cint * Sfun j / (cL * (2 * Real.pi) ^ j) + C₀) * T ^ η *
                  (T / |ξ|) ^ j * sF := by
                have h1 : max 1 (Cint * Sfun j / (cL * (2 * Real.pi) ^ j) + C₀) * 1 ≤
                    max 1 (Cint * Sfun j / (cL * (2 * Real.pi) ^ j) + C₀) * T ^ η :=
                  mul_le_mul_of_nonneg_left hTη hccnn
                have h2 : (0:ℝ) ≤ (T / |ξ|) ^ j * sF := mul_nonneg hxnn hsupnn
                calc max 1 (Cint * Sfun j / (cL * (2 * Real.pi) ^ j) + C₀) * 1 *
                      (T / |ξ|) ^ j * sF
                    = (max 1 (Cint * Sfun j / (cL * (2 * Real.pi) ^ j) + C₀) * 1) *
                        ((T / |ξ|) ^ j * sF) := by ring
                  _ ≤ (max 1 (Cint * Sfun j / (cL * (2 * Real.pi) ^ j) + C₀) * T ^ η) *
                        ((T / |ξ|) ^ j * sF) :=
                      mul_le_mul h1 le_rfl h2 (by positivity)
                  _ = max 1 (Cint * Sfun j / (cL * (2 * Real.pi) ^ j) + C₀) * T ^ η *
                        (T / |ξ|) ^ j * sF := by ring

end Assembly

end L84cf

/-- **GM 8.4** (`Work.GM.S3.Lemma84Statement`), proved in a module free of the
`iteratedDeriv_ofReal_comp` clash.  All auxiliary declarations live in `Work.GM.S3.L84cf`, so this
module can be imported alongside `Submission.Work.GM.S3.hhat_defs`. -/
theorem lemma84_clashfree : Work.GM.S3.Lemma84Statement := L84cf.lemma84

end Work.GM.S3
