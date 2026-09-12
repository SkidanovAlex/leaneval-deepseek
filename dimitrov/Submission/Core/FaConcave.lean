import Mathlib
import Submission.Core.FaAnalytic
import Submission.Core.F1Norm
import Submission.Core.FaPolar
import Submission.Core.FullPeriod

/-!
# KL-F4: log-concavity (unimodality) of `‖f_a‖` on circle arcs

(F4 of Plan.md DESIGN NOTE 6.)  On each arc of the circle (an interval of
`σ` avoiding all jump points `σ ≡ θ_j + π (mod 2π)`), the modulus of
`f_a(E σ)` is log-concave in `σ`:

    log ‖f_a(E σ)‖ = log a + Σ_j p_j · log ‖1 + E(σ − θ_j)‖
                   = log a + Σ_j p_j·log 2 + Σ_j p_j · log|cos((σ−θ_j)/2)|,

and each `log|cos(u/2)|` has second derivative `-(1/4)·sec²(u/2) ≤ 0` on any
interval avoiding the zeros of `cos(u/2)`.  With `p_j ≥ 0` the sum is
concave.  (Log-concavity in the affine argument coordinate `t` follows by
composition with an increasing affine map.)

A separate abstract lemma turns log-concavity into the `UnimodalOn` shape
that `Submission.Core.D3.per_arc_bound` requires (`q := ‖f‖/2` unimodal on
the interval), for a continuous `q` positive in the interior.

Prove all theorems below; add helper lemmas as needed.  No placeholders may
remain; the module must build (`lake build Submission.Core.FaConcave`).
-/

noncomputable section

open scoped Real Complex BigOperators
open Complex

namespace Submission.Core

/-! ## Local plumbing for `E` (copied/derived for the core `E` of this file) -/

private lemma fcE_add (t s : ℝ) : E (t + s) = E t * E s := by
  dsimp [E]
  rw [← Complex.exp_add]
  congr 1
  rw [Complex.ofReal_add]
  ring

private lemma fcE_zero : E 0 = 1 := by
  dsimp [E]
  simp

private lemma fc_norm_E (t : ℝ) : ‖E t‖ = 1 := by
  dsimp [E]
  rw [Complex.norm_exp_ofReal_mul_I]

private lemma fcE_ne_zero (t : ℝ) : E t ≠ 0 := by
  have hnorm : ‖E t‖ ≠ 0 := by
    rw [fc_norm_E t]
    norm_num
  exact norm_ne_zero_iff.mp hnorm

private lemma fcE_neg_mul (t : ℝ) : E (-t) * E t = 1 := by
  have h := fcE_add (-t) t
  have hz : -t + t = 0 := by ring
  rw [hz] at h
  rw [fcE_zero] at h
  exact h.symm

private lemma fc_re_E (t : ℝ) : (E t).re = Real.cos t := by
  dsimp [E]
  rw [Complex.exp_mul_I]
  rw [Complex.add_re, Complex.mul_re]
  rw [Complex.cos_ofReal_re, Complex.sin_ofReal_re]
  simp [Complex.I_re, Complex.I_im]

private lemma fc_im_E (t : ℝ) : (E t).im = Real.sin t := by
  dsimp [E]
  rw [Complex.exp_mul_I]
  rw [Complex.add_im, Complex.mul_im]
  rw [Complex.cos_ofReal_im, Complex.sin_ofReal_re]
  simp [Complex.I_re, Complex.I_im]

private lemma fc_norm_one_add_E (t : ℝ) : ‖(1 : ℂ) + E t‖ = 2 * |Real.cos (t / 2)| := by
  have hsq : ‖(1 : ℂ) + E t‖ ^ 2 = 4 * (Real.cos (t / 2)) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    rw [Complex.normSq_apply]
    have hre' : ((1 : ℂ) + E t).re = 1 + Real.cos t := by
      rw [Complex.add_re, fc_re_E]
      simp
    have him' : ((1 : ℂ) + E t).im = Real.sin t := by
      rw [Complex.add_im, fc_im_E]
      simp
    rw [hre', him']
    have hsc : Real.sin t ^ 2 + Real.cos t ^ 2 = 1 := Real.sin_sq_add_cos_sq t
    have hcm : Real.cos t = 2 * (Real.cos (t / 2)) ^ 2 - 1 := by
      have h := Real.cos_two_mul (t / 2)
      convert h using 1 <;> ring
    nlinarith
  have hb : (2 * |Real.cos (t / 2)|) ^ 2 = 4 * (Real.cos (t / 2)) ^ 2 := by
    rw [mul_pow, sq_abs]
    ring
  have hposB : 0 ≤ 2 * |Real.cos (t / 2)| := by positivity
  apply le_antisymm
  · exact (sq_le_sq₀ (norm_nonneg _) hposB).mp (le_of_eq (by rw [hsq, hb]))
  · exact (sq_le_sq₀ hposB (norm_nonneg _)).mp (le_of_eq (by rw [hb, hsq]))

/-- `cos ((x - θ₀)/2) ≠ 0` whenever `1 + E(x-θ₀) ≠ 0`. -/
private lemma fc_cos_half_ne_zero (θ₀ : ℝ) {x : ℝ} (h : (1 : ℂ) + E (x - θ₀) ≠ 0) :
    Real.cos ((x - θ₀) / 2) ≠ 0 := by
  have hn : ‖(1 : ℂ) + E (x - θ₀)‖ ≠ 0 := norm_ne_zero_iff.mpr h
  have hEq := fc_norm_one_add_E (x - θ₀)
  intro hc
  have hzero : ‖(1 : ℂ) + E (x - θ₀)‖ = 0 := by
    rw [hEq, hc]
    simp
  exact hn hzero

/-- Pointwise: `log‖1+Eφ‖ = log 2 + log(cos(φ/2))` (log means log|·|). -/
private lemma fc_log_norm_eq_log_cos (θ₀ : ℝ) {x : ℝ} (h : (1 : ℂ) + E (x - θ₀) ≠ 0) :
    Real.log ‖(1 : ℂ) + E (x - θ₀)‖
      = Real.log 2 + Real.log (Real.cos ((x - θ₀) / 2)) := by
  have hc : Real.cos ((x - θ₀) / 2) ≠ 0 := fc_cos_half_ne_zero θ₀ h
  have hnorm : ‖(1 : ℂ) + E (x - θ₀)‖ = 2 * |Real.cos ((x - θ₀) / 2)| :=
    fc_norm_one_add_E (x - θ₀)
  calc
    Real.log ‖(1 : ℂ) + E (x - θ₀)‖
        = Real.log (2 * |Real.cos ((x - θ₀) / 2)|) := by rw [hnorm]
    _ = Real.log 2 + Real.log |Real.cos ((x - θ₀) / 2)| := by
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (abs_ne_zero.mpr hc)]
    _ = Real.log 2 + Real.log (Real.cos ((x - θ₀) / 2)) := by
        congr 1
        exact Real.log_abs (Real.cos ((x - θ₀) / 2))

/-- tan is strictly increasing on the interval between consecutive zeros of
`cos((·-θ₀)/2)`. -/
private lemma fc_strictMonoOn_tan_half (θ₀ : ℝ) {u v : ℝ}
    (hc : ∀ x ∈ Set.Ioo u v, Real.cos ((x - θ₀) / 2) ≠ 0) :
    StrictMonoOn Real.tan (Set.Ioo ((u - θ₀) / 2) ((v - θ₀) / 2)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioo _ _)
  · refine Real.continuousOn_tan.mono ?_
    intro z hzJ
    let x : ℝ := 2 * z + θ₀
    have hxθ : (x - θ₀) / 2 = z := by
      dsimp [x]
      ring
    have hx : x ∈ Set.Ioo u v := by
      constructor
      · have h1 : u - θ₀ < 2 * z := by
          simpa [mul_comm] using (div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)).mp hzJ.1
        dsimp [x]
        linarith
      · have h1 : 2 * z < v - θ₀ := by
          simpa [mul_comm] using (lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mp hzJ.2
        dsimp [x]
        linarith
    have hcosx : Real.cos ((x - θ₀) / 2) ≠ 0 := hc x hx
    rwa [hxθ] at hcosx
  · intro z hzint
    have hzJ : z ∈ Set.Ioo ((u - θ₀) / 2) ((v - θ₀) / 2) := by
      simpa [interior_Ioo] using hzint
    let x : ℝ := 2 * z + θ₀
    have hxθ : (x - θ₀) / 2 = z := by
      dsimp [x]
      ring
    have hx : x ∈ Set.Ioo u v := by
      constructor
      · have h1 : u - θ₀ < 2 * z := by
          simpa [mul_comm] using (div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)).mp hzJ.1
        dsimp [x]
        linarith
      · have h1 : 2 * z < v - θ₀ := by
          simpa [mul_comm] using (lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mp hzJ.2
        dsimp [x]
        linarith
    have hcosx : Real.cos ((x - θ₀) / 2) ≠ 0 := hc x hx
    have hcosz : Real.cos z ≠ 0 := by
      rwa [hxθ] at hcosx
    rw [Real.deriv_tan]
    exact div_pos zero_lt_one (sq_pos_of_ne_zero hcosz)

/-- `x ↦ -tan((x-θ₀)/2)/2` is antitone on an interval avoiding zeros of cos. -/
private lemma fc_antitoneOn_neg_tan_half (θ₀ : ℝ) {u v : ℝ}
    (hc : ∀ x ∈ Set.Ioo u v, Real.cos ((x - θ₀) / 2) ≠ 0) :
    AntitoneOn (fun x : ℝ => -Real.tan ((x - θ₀) / 2) / 2) (Set.Ioo u v) := by
  have hsm : StrictMonoOn Real.tan (Set.Ioo ((u - θ₀) / 2) ((v - θ₀) / 2)) :=
    fc_strictMonoOn_tan_half θ₀ hc
  intro x hx y hy hxy
  rcases lt_or_eq_of_le hxy with hlt | heq
  · have hx' : (x - θ₀) / 2 ∈ Set.Ioo ((u - θ₀) / 2) ((v - θ₀) / 2) := by
      constructor
      · have h1 : u - θ₀ < x - θ₀ := by linarith [hx.1]
        exact div_lt_div_of_pos_right h1 (by norm_num)
      · have h2 : x - θ₀ < v - θ₀ := by linarith [hx.2]
        exact div_lt_div_of_pos_right h2 (by norm_num)
    have hy' : (y - θ₀) / 2 ∈ Set.Ioo ((u - θ₀) / 2) ((v - θ₀) / 2) := by
      constructor
      · have h1 : u - θ₀ < y - θ₀ := by linarith [hy.1]
        exact div_lt_div_of_pos_right h1 (by norm_num)
      · have h2 : y - θ₀ < v - θ₀ := by linarith [hy.2]
        exact div_lt_div_of_pos_right h2 (by norm_num)
    have hxy' : (x - θ₀) / 2 < (y - θ₀) / 2 := by
      exact div_lt_div_of_pos_right (by linarith) (by norm_num)
    have ht : Real.tan ((x - θ₀) / 2) < Real.tan ((y - θ₀) / 2) :=
      hsm hx' hy' hxy'
    have hneg : -Real.tan ((y - θ₀) / 2) < -Real.tan ((x - θ₀) / 2) := neg_lt_neg ht
    have hdiv : -Real.tan ((y - θ₀) / 2) / 2 ≤ -Real.tan ((x - θ₀) / 2) / 2 :=
      div_le_div_of_nonneg_right (le_of_lt hneg) (by norm_num)
    exact hdiv
  · subst x
    rfl

/-- Pointwise derivative of `x ↦ log(cos((x-θ₀)/2))`. -/
private lemma fc_hasDerivAt_log_cos_half (θ₀ : ℝ) {x : ℝ}
    (hc : Real.cos ((x - θ₀) / 2) ≠ 0) :
    HasDerivAt (fun t : ℝ => Real.log (Real.cos ((t - θ₀) / 2)))
      (-Real.tan ((x - θ₀) / 2) / 2) x := by
  have hy : HasDerivAt (fun t : ℝ => (t - θ₀) / 2) (1 / 2) x := by
    have hsub : HasDerivAt (fun t : ℝ => t - θ₀) 1 x := (hasDerivAt_id x).sub_const θ₀
    have hdiv := hsub.div_const (2 : ℝ)
    convert hdiv using 1 <;> norm_num
  have hcos : HasDerivAt (fun t : ℝ => Real.cos ((t - θ₀) / 2))
      (-Real.sin ((x - θ₀) / 2) * (1 / 2)) x := by
    exact (Real.hasDerivAt_cos ((x - θ₀) / 2)).comp x hy
  have hlog := hcos.log hc
  convert hlog using 1
  rw [Real.tan_eq_sin_div_cos]
  field_simp [hc]

/-- `x ↦ log(cos((x-θ₀)/2))` is concave on an interval avoiding zeros of cos. -/
private lemma fc_log_cos_half_concaveOn (θ₀ : ℝ) {u v : ℝ}
    (hc : ∀ x ∈ Set.Ioo u v, Real.cos ((x - θ₀) / 2) ≠ 0) :
    ConcaveOn ℝ (Set.Ioo u v) (fun x : ℝ => Real.log (Real.cos ((x - θ₀) / 2))) := by
  let K : ℝ → ℝ := fun x => Real.log (Real.cos ((x - θ₀) / 2))
  have hderiv : ∀ x ∈ interior (Set.Ioo u v),
      HasDerivAt K (-Real.tan ((x - θ₀) / 2) / 2) x := by
    intro x hx
    have hx' : x ∈ Set.Ioo u v := by simpa [interior_Ioo] using hx
    exact fc_hasDerivAt_log_cos_half θ₀ (hc x hx')
  have hdiff : DifferentiableOn ℝ K (interior (Set.Ioo u v)) := by
    intro x hx
    exact (hderiv x hx).differentiableAt.differentiableWithinAt
  refine AntitoneOn.concaveOn_of_deriv (convex_Ioo u v) ?_ hdiff ?_
  · have hc' : ContinuousOn K (interior (Set.Ioo u v)) := hdiff.continuousOn
    simpa [K, interior_Ioo] using hc'
  · have hanti : AntitoneOn (fun x : ℝ => -Real.tan ((x - θ₀) / 2) / 2) (Set.Ioo u v) :=
      fc_antitoneOn_neg_tan_half θ₀ hc
    intro x hx y hy hxy
    rw [interior_Ioo] at hx hy
    have hxK : deriv K x = -Real.tan ((x - θ₀) / 2) / 2 :=
      (hderiv x (by simpa [interior_Ioo])).deriv
    have hyK : deriv K y = -Real.tan ((y - θ₀) / 2) / 2 :=
      (hderiv y (by simpa [interior_Ioo])).deriv
    rw [hxK, hyK]
    exact hanti (by simpa [interior_Ioo] using hx) (by simpa [interior_Ioo] using hy) hxy

/-! ## Concavity-preserving operations (built directly to control instances) -/

/-- Pointwise sum of concave functions is concave. -/
private lemma fc_concaveOn_add {s : Set ℝ} {f g : ℝ → ℝ} (hf : ConcaveOn ℝ s f)
    (hg : ConcaveOn ℝ s g) : ConcaveOn ℝ s (fun x => f x + g x) := by
  constructor
  · exact hf.1
  · intro x hx y hy a b ha hb hab
    have h1 := hf.2 hx hy ha hb hab
    have h2 := hg.2 hx hy ha hb hab
    change a * (f x + g x) + b * (f y + g y) ≤ f (a * x + b * y) + g (a * x + b * y)
    change a * f x + b * f y ≤ f (a * x + b * y) at h1
    change a * g x + b * g y ≤ g (a * x + b * y) at h2
    rw [mul_add, mul_add]
    nlinarith [h1, h2]

/-- A nonnegative multiple of a concave function is concave. -/
private lemma fc_concaveOn_smul {s : Set ℝ} {c : ℝ} (hc : 0 ≤ c) {f : ℝ → ℝ}
    (hf : ConcaveOn ℝ s f) : ConcaveOn ℝ s (fun x => c * f x) := by
  constructor
  · exact hf.1
  · intro x hx y hy a b ha hb hab
    have h1 := hf.2 hx hy ha hb hab
    change a * (c * f x) + b * (c * f y) ≤ c * f (a * x + b * y)
    change a * f x + b * f y ≤ f (a * x + b * y) at h1
    nlinarith [h1, hc]

/-- Constants are concave. -/
private lemma fc_concaveOn_const {s : Set ℝ} (hs : Convex ℝ s) (c : ℝ) :
    ConcaveOn ℝ s (fun _ : ℝ => c) := by
  constructor
  · exact hs
  · intro x hx y hy a b ha hb hab
    change a * c + b * c ≤ c
    rw [← add_mul, hab, one_mul]

/-- Finite sums of concave functions are concave. -/
private lemma fc_concaveOn_finset_sum {ι : Type*} (s : Finset ι) (t : Set ℝ)
    (ht : Convex ℝ t) {f : ι → ℝ → ℝ} (hf : ∀ i ∈ s, ConcaveOn ℝ t (f i)) :
    ConcaveOn ℝ t (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have h : (fun x : ℝ => ∑ i ∈ (∅ : Finset ι), f i x) = fun _ : ℝ => 0 := by
        funext x
        simp
      rw [h]
      exact fc_concaveOn_const ht 0
  | insert a s' has' ih =>
      have hsplit : (fun x : ℝ => ∑ i ∈ insert a s', f i x)
          = fun x : ℝ => f a x + ∑ i ∈ s', f i x := by
        funext x
        rw [Finset.sum_insert has']
      rw [hsplit]
      exact fc_concaveOn_add (hf a (Finset.mem_insert_self a s'))
        (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

/-- **Single summand log-concavity.**  On an open interval where
`1 + E(x−θ₀) ≠ 0` (i.e. `cos((x−θ₀)/2) ≠ 0`), `x ↦ log‖1+E(x−θ₀)‖` is
concave. -/
theorem log_norm_one_add_E_concaveOn (θ₀ : ℝ) {u v : ℝ} (huv : u < v)
    (hz : ∀ x ∈ Set.Ioo u v, (1 : ℂ) + E (x - θ₀) ≠ 0) :
    ConcaveOn ℝ (Set.Ioo u v) (fun x : ℝ => Real.log ‖(1 : ℂ) + E (x - θ₀)‖) := by
  have hcos : ∀ x ∈ Set.Ioo u v, Real.cos ((x - θ₀) / 2) ≠ 0 :=
    fun x hx => fc_cos_half_ne_zero θ₀ (hz x hx)
  have hkc : ConcaveOn ℝ (Set.Ioo u v)
      (fun x : ℝ => Real.log (Real.cos ((x - θ₀) / 2))) :=
    fc_log_cos_half_concaveOn θ₀ hcos
  have hconst : ConcaveOn ℝ (Set.Ioo u v) (fun _ : ℝ => Real.log 2) :=
    fc_concaveOn_const (convex_Ioo u v) (Real.log 2)
  have hsum : ConcaveOn ℝ (Set.Ioo u v)
      (fun x : ℝ => Real.log 2 + Real.log (Real.cos ((x - θ₀) / 2))) :=
    fc_concaveOn_add hconst hkc
  refine hsum.congr ?_
  intro x hx
  exact (fc_log_norm_eq_log_cos θ₀ (hz x hx)).symm

/-! ## Norm identity for `faE` and its logarithm -/

private lemma fc_one_add_E_sub_ne_zero_iff (σ θ : ℝ) :
    (1 : ℂ) + E (σ - θ) ≠ 0 ↔ E σ ≠ -E θ := by
  constructor
  · intro h hE
    have hsub : E (σ - θ) = E σ * E (-θ) := by
      have h' := fcE_add σ (-θ)
      simpa [sub_eq_add_neg] using h'
    have h1 : E (-θ) * E θ = 1 := fcE_neg_mul θ
    have this' : E (σ - θ) = -1 := by
      rw [hsub, hE]
      have hcomm : (-E θ) * E (-θ) = -(E θ * E (-θ)) := by ring
      rw [hcomm]
      have hswap : E θ * E (-θ) = E (-θ) * E θ := by ring
      rw [hswap, h1]
    have hzero : (1 : ℂ) + E (σ - θ) = 0 := by
      rw [this']
      ring
    exact h hzero
  · intro h h1
    have hsub : E (σ - θ) = E σ * E (-θ) := by
      have h' := fcE_add σ (-θ)
      simpa [sub_eq_add_neg] using h'
    have hE' : E (σ - θ) = -(1 : ℂ) := by
      apply eq_neg_of_add_eq_zero_left
      simpa [add_comm] using h1
    have hE : E (σ - θ) = -1 := by simpa using hE'
    have harg : E σ * E (-θ) = -1 := by rwa [hsub] at hE
    have hmul : (E σ * E (-θ)) * E θ = -E θ := by
      rw [harg]
      simp
    have hred : (E σ * E (-θ)) * E θ = E σ := by
      have h1' : E (-θ) * E θ = 1 := fcE_neg_mul θ
      calc
        (E σ * E (-θ)) * E θ = E σ * (E (-θ) * E θ) := by ring
        _ = E σ * 1 := by rw [h1']
        _ = E σ := by ring
    have hEσ : E σ = -E θ := by
      rw [hred] at hmul
      exact hmul
    exact h hEσ

/-- `‖Eσ + Eθ‖ = ‖1 + E(σ-θ)‖`. -/
private lemma fc_norm_E_add_E (σ θ : ℝ) : ‖E σ + E θ‖ = ‖(1 : ℂ) + E (σ - θ)‖ := by
  have hsub : E (σ - θ) = E σ * E (-θ) := by
    have h' := fcE_add σ (-θ)
    simpa [sub_eq_add_neg] using h'
  have hprod : E θ * (1 + E (σ - θ)) = E σ + E θ := by
    rw [hsub]
    have h1 : E θ * E (-θ) = 1 := by
      have hswap : E θ * E (-θ) = E (-θ) * E θ := by ring
      rw [hswap, fcE_neg_mul θ]
    calc
      E θ * (1 + E σ * E (-θ)) = E θ + E θ * (E σ * E (-θ)) := by ring
      _ = E θ + E σ * (E θ * E (-θ)) := by ring
      _ = E σ + E θ := by rw [h1]; ring
  calc
    ‖E σ + E θ‖ = ‖E θ * (1 + E (σ - θ))‖ := by rw [← hprod]
    _ = ‖E θ‖ * ‖1 + E (σ - θ)‖ := by rw [norm_mul]
    _ = ‖1 + E (σ - θ)‖ := by rw [fc_norm_E]; norm_num

/-- Norm identity for `faE` in terms of the jump factors. -/
private lemma fc_faE_norm (n : ℕ) (a : ℝ) (ha : 0 ≤ a) (θ : Fin n → ℝ) (p : Fin n → ℝ) {σ : ℝ}
    (hne : ∀ j : Fin n, (1 : ℂ) + E (σ - θ j) ≠ 0) :
    ‖faE n a θ p σ‖ = a * ∏ j ∈ (Finset.univ : Finset (Fin n)),
      ‖(1 : ℂ) + E (σ - θ j)‖ ^ p j := by
  unfold faE
  have hne' : ∀ j : Fin n, E σ ≠ -E (θ j) := fun j =>
    (fc_one_add_E_sub_ne_zero_iff σ (θ j)).mp (hne j)
  have hnorm := fa_norm_on_circle n a ha (z := fun j : Fin n => E (θ j)) p
    (hz := fun j => fc_norm_E (θ j)) (w := E σ) (hw := fc_norm_E σ) hne'
  rw [hnorm]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [fc_norm_E_add_E σ (θ j)]

/-- Log of the norm expands as the sum of jump-factor logs. -/
private lemma fc_log_faE_norm_eq (n : ℕ) (a : ℝ) (ha : 0 < a) (θ : Fin n → ℝ) (p : Fin n → ℝ)
    {σ : ℝ} (hne : ∀ j : Fin n, (1 : ℂ) + E (σ - θ j) ≠ 0) :
    Real.log ‖faE n a θ p σ‖ =
      Real.log a + ∑ j ∈ (Finset.univ : Finset (Fin n)),
        p j * Real.log ‖(1 : ℂ) + E (σ - θ j)‖ := by
  have hpos : ∀ j : Fin n, 0 < ‖(1 : ℂ) + E (σ - θ j)‖ := by
    intro j
    exact lt_of_le_of_ne (norm_nonneg _) (by
      intro hz
      exact hne j (norm_eq_zero.mp hz.symm))
  have hnorm := fc_faE_norm n a (le_of_lt ha) θ p hne
  have hprodpos : 0 < ∏ j ∈ (Finset.univ : Finset (Fin n)),
      ‖(1 : ℂ) + E (σ - θ j)‖ ^ p j := by
    exact Finset.prod_pos (by
      intro j hj
      exact Real.rpow_pos_of_pos (hpos j) (p j))
  calc
    Real.log ‖faE n a θ p σ‖
        = Real.log (a * ∏ j ∈ (Finset.univ : Finset (Fin n)),
            ‖(1 : ℂ) + E (σ - θ j)‖ ^ p j) := by rw [hnorm]
    _ = Real.log a + Real.log (∏ j ∈ (Finset.univ : Finset (Fin n)),
            ‖(1 : ℂ) + E (σ - θ j)‖ ^ p j) := by
          rw [Real.log_mul (ne_of_gt ha) (ne_of_gt hprodpos)]
    _ = Real.log a + ∑ j ∈ (Finset.univ : Finset (Fin n)),
          Real.log (‖(1 : ℂ) + E (σ - θ j)‖ ^ p j) := by
          congr 1
          rw [Real.log_prod]
          intro j hj
          exact ne_of_gt (Real.rpow_pos_of_pos (hpos j) (p j))
    _ = Real.log a + ∑ j ∈ (Finset.univ : Finset (Fin n)),
          p j * Real.log ‖(1 : ℂ) + E (σ - θ j)‖ := by
          congr 1
          apply Finset.sum_congr rfl
          intro j hj
          rw [Real.log_rpow (hpos j) (p j)]

/-- **Log-concavity of `‖f_a‖` on a jump-free arc.**  With `0 < a`,
`p_j ≥ 0`, on an open interval where no factor `1 + E(σ−θ_j)` vanishes,
`σ ↦ log‖faE n a θ p σ‖` is concave. -/
theorem log_faE_concaveOn (n : ℕ) (a : ℝ) (ha : 0 < a) (θ : Fin n → ℝ)
    (p : Fin n → ℝ) (hp : ∀ j : Fin n, 0 ≤ p j) {u v : ℝ} (huv : u < v)
    (hz : ∀ σ ∈ Set.Ioo u v, ∀ j : Fin n, (1 : ℂ) + E (σ - θ j) ≠ 0) :
    ConcaveOn ℝ (Set.Ioo u v) (fun σ : ℝ => Real.log ‖faE n a θ p σ‖) := by
  have hsingle : ∀ j : Fin n, ConcaveOn ℝ (Set.Ioo u v)
      (fun σ : ℝ => p j * Real.log ‖(1 : ℂ) + E (σ - θ j)‖) := by
    intro j
    have hc1 := log_norm_one_add_E_concaveOn (θ j) huv (fun x hx => hz x hx j)
    exact fc_concaveOn_smul (hp j) hc1
  have hsumconc : ConcaveOn ℝ (Set.Ioo u v)
      (fun σ : ℝ => ∑ j ∈ (Finset.univ : Finset (Fin n)),
        p j * Real.log ‖(1 : ℂ) + E (σ - θ j)‖) := by
    exact fc_concaveOn_finset_sum (Finset.univ : Finset (Fin n)) (Set.Ioo u v)
      (convex_Ioo u v) (fun i hi => hsingle i)
  have hconst : ConcaveOn ℝ (Set.Ioo u v) (fun _ : ℝ => Real.log a) :=
    fc_concaveOn_const (convex_Ioo u v) (Real.log a)
  have hsumall : ConcaveOn ℝ (Set.Ioo u v)
      (fun σ : ℝ => Real.log a + ∑ j ∈ (Finset.univ : Finset (Fin n)),
        p j * Real.log ‖(1 : ℂ) + E (σ - θ j)‖) := by
    simpa using fc_concaveOn_add hconst hsumconc
  refine hsumall.congr ?_
  intro σ hσ
  exact (fc_log_faE_norm_eq n a ha θ p (fun j => hz σ hσ j)).symm

/-! ## Unimodality from log-concavity (auxiliary analysis) -/

/-- A point in `(a, y)` where `q` exceeds `c`, from right-continuity at `a`. -/
private lemma fc_right_pull (q : ℝ → ℝ) {a c y : ℝ} (hay : a < y) (hqa : c < q a)
    (hcont : ContinuousWithinAt q (Set.Ioi a) a) :
    ∃ x, a < x ∧ x < y ∧ c < q x := by
  rcases Metric.continuousWithinAt_iff.mp hcont (q a - c) (sub_pos.mpr hqa) with ⟨δ, hδ0, hδ⟩
  let x0 : ℝ := a + min δ (y - a) / 2
  have hminpos : 0 < min δ (y - a) := lt_min hδ0 (sub_pos.mpr hay)
  refine ⟨x0, ?_, ?_, ?_⟩
  · dsimp [x0]
    nlinarith
  · dsimp [x0]
    have hle : min δ (y - a) ≤ y - a := min_le_right _ _
    have hlt2 : y - a < 2 * (y - a) := by nlinarith
    nlinarith
  · have hxa : a < x0 := by
      dsimp [x0]
      nlinarith [hminpos]
    have hdist : dist x0 a < δ := by
      rw [Real.dist_eq]
      have hxa' : 0 < x0 - a := by linarith
      rw [abs_of_pos hxa']
      dsimp [x0]
      have hminlt : min δ (y - a) < 2 * δ := by
        exact lt_of_le_of_lt (min_le_left _ _) (by nlinarith [hδ0])
      nlinarith
    have hq := hδ hxa hdist
    rw [Real.dist_eq] at hq
    have hq' : q a - q x0 < q a - c := (abs_sub_lt_iff.mp hq).2
    linarith

/-- A point in `(x, b)` where `q` exceeds `c`, from left-continuity at `b`. -/
private lemma fc_left_pull (q : ℝ → ℝ) {b c x : ℝ} (hxb : x < b) (hqb : c < q b)
    (hcont : ContinuousWithinAt q (Set.Iio b) b) :
    ∃ y, x < y ∧ y < b ∧ c < q y := by
  rcases Metric.continuousWithinAt_iff.mp hcont (q b - c) (sub_pos.mpr hqb) with ⟨δ, hδ0, hδ⟩
  let x0 : ℝ := b - min δ (b - x) / 2
  have hminpos : 0 < min δ (b - x) := lt_min hδ0 (sub_pos.mpr hxb)
  refine ⟨x0, ?_, ?_, ?_⟩
  · dsimp [x0]
    have hle : min δ (b - x) ≤ b - x := min_le_right _ _
    have hlt2 : b - x < 2 * (b - x) := by nlinarith
    nlinarith
  · dsimp [x0]
    nlinarith
  · have hxb0 : x0 < b := by
      dsimp [x0]
      nlinarith [hminpos]
    have hdist : dist x0 b < δ := by
      rw [Real.dist_eq]
      have hneg : x0 - b < 0 := by linarith
      rw [abs_of_neg hneg]
      dsimp [x0]
      have hminlt : min δ (b - x) < 2 * δ := by
        exact lt_of_le_of_lt (min_le_left _ _) (by nlinarith [hδ0])
      nlinarith
    have hq := hδ hxb0 hdist
    rw [Real.dist_eq] at hq
    have hq' : q b - q x0 < q b - c := (abs_sub_lt_iff.mp hq).2
    linarith

/-- Concavity of `L` forbids `L t < L x` and `L t < L z` when `x < t < z`. -/
private lemma fc_concave_not_gt_both {a b : ℝ} {L : ℝ → ℝ} (hL : ConcaveOn ℝ (Set.Ioo a b) L)
    {x t z : ℝ} (hx : x ∈ Set.Ioo a b) (ht : t ∈ Set.Ioo a b) (hz : z ∈ Set.Ioo a b)
    (hxt : x < t) (htz : t < z) (hxL : L t < L x) (hzL : L t < L z) : False := by
  let μ : ℝ := (z - t) / (z - x)
  have hzx : 0 < z - x := sub_pos.mpr (lt_trans hxt htz)
  have hzt : 0 < z - t := sub_pos.mpr htz
  have hμ0 : 0 < μ := by
    dsimp [μ]
    exact div_pos hzt hzx
  have hμ1 : μ < 1 := by
    have hmain : z - t < z - x := by linarith
    have hb : (z - t) / (z - x) < 1 := (div_lt_one hzx).2 hmain
    simpa [μ] using hb
  have hbnonneg : 0 ≤ 1 - μ := by linarith
  have hbadd : μ + (1 - μ) = 1 := by ring
  have hineq := hL.2 hx hz (le_of_lt hμ0) hbnonneg hbadd
  change μ * L x + (1 - μ) * L z ≤ L (μ * x + (1 - μ) * z) at hineq
  have hmid : μ * x + (1 - μ) * z = t := by
    dsimp [μ]
    have hzx0 : z - x ≠ 0 := ne_of_gt hzx
    field_simp [hzx0]
    ring
  rw [hmid] at hineq
  have hs1 : μ * L t < μ * L x := mul_lt_mul_of_pos_left hxL hμ0
  have hs2 : (1 - μ) * L t < (1 - μ) * L z := mul_lt_mul_of_pos_left hzL (by linarith)
  have hsum : μ * L t + (1 - μ) * L t < μ * L x + (1 - μ) * L z := add_lt_add hs1 hs2
  have hred : μ * L t + (1 - μ) * L t = L t := by ring
  nlinarith [hineq, hsum, hred]

/-- One-sided continuity from the right at the left endpoint. -/
private lemma fc_rightCont (q : ℝ → ℝ) {a b : ℝ} (hab : a < b)
    (hqcont : ContinuousOn q (Set.Icc a b)) :
    ContinuousWithinAt q (Set.Ioi a) a := by
  have hcontat : ContinuousWithinAt q (Set.Icc a b) a :=
    hqcont.continuousWithinAt (by constructor <;> linarith)
  have hna : Set.Icc a b ∈ nhdsWithin a (Set.Ioi a) := by
    rw [mem_nhdsWithin_iff_eventually]
    filter_upwards [isOpen_Iio.mem_nhds hab] with w hw
    intro hwIoi
    exact ⟨le_of_lt hwIoi, le_of_lt hw⟩
  exact hcontat.mono_of_mem_nhdsWithin hna

/-- One-sided continuity from the left at the right endpoint. -/
private lemma fc_leftCont (q : ℝ → ℝ) {a b : ℝ} (hab : a < b)
    (hqcont : ContinuousOn q (Set.Icc a b)) :
    ContinuousWithinAt q (Set.Iio b) b := by
  have hcontat : ContinuousWithinAt q (Set.Icc a b) b :=
    hqcont.continuousWithinAt (by constructor <;> linarith)
  have hnb : Set.Icc a b ∈ nhdsWithin b (Set.Iio b) := by
    rw [mem_nhdsWithin_iff_eventually]
    filter_upwards [isOpen_Ioi.mem_nhds hab] with w hw
    intro hwIio
    exact ⟨le_of_lt hw, le_of_lt hwIio⟩
  exact hcontat.mono_of_mem_nhdsWithin hnb

/-- `q` is monotone increasing on `[a,m]` when `m` is a maximizer. -/
private lemma fc_q_monotone_left {a b m : ℝ} (hab : a < b) (q : ℝ → ℝ)
    (hmem : m ∈ Set.Icc a b) (hmax : ∀ t ∈ Set.Icc a b, q t ≤ q m)
    (hqcont : ContinuousOn q (Set.Icc a b))
    (hqpos : ∀ t : ℝ, a < t → t < b → 0 < q t)
    (hlog : ConcaveOn ℝ (Set.Ioo a b) (fun t : ℝ => Real.log (q t))) :
    MonotoneOn q (Set.Icc a m) := by
  have hcwA : ContinuousWithinAt q (Set.Ioi a) a := fc_rightCont q hab hqcont
  have hcwB : ContinuousWithinAt q (Set.Iio b) b := fc_leftCont q hab hqcont
  intro x hx y hy hxy
  by_contra hnot
  have hylt : q y < q x := lt_of_not_ge hnot
  have hnexy : x ≠ y := by
    intro heq
    subst y
    exact (lt_irrefl (q x)) hylt
  have hxly : x < y := lt_of_le_of_ne hxy hnexy
  by_cases hym : y = m
  · subst y
    exact (not_le_of_gt hylt) (hmax x (by constructor <;> linarith [hx.1, hx.2, hmem.2]))
  have hylm : y < m := lt_of_le_of_ne hy.2 hym
  have hay : a < y := lt_of_le_of_lt hx.1 hxly
  have hyb : y < b := lt_of_lt_of_le hylm hmem.2
  have hqy : 0 < q y := hqpos y hay hyb
  have hz₂ : ∃ z, z ∈ Set.Ioo y b ∧ q y < q z := by
    by_cases hmb : m < b
    · refine ⟨m, ⟨hylm, hmb⟩, lt_of_lt_of_le hylt (hmax x (by constructor <;> linarith [hx.1, hx.2, hmem.2]))⟩
    · have hmb' : b ≤ m := le_of_not_gt hmb
      have hmbEq : m = b := le_antisymm hmem.2 hmb'
      subst m
      rcases fc_left_pull q hyb (lt_of_lt_of_le hylt (hmax x (by constructor <;> linarith [hx.1, hx.2]))) hcwB with ⟨w, hwy, hwb, hqw⟩
      exact ⟨w, ⟨hwy, hwb⟩, hqw⟩
  have hz₁ : ∃ z, z ∈ Set.Ioo a y ∧ q y < q z := by
    by_cases hax : a < x
    · refine ⟨x, ⟨hax, hxly⟩, hylt⟩
    · have hxa : x ≤ a := le_of_not_gt hax
      have hxaEq : x = a := le_antisymm hxa hx.1
      subst x
      rcases fc_right_pull q hay hylt hcwA with ⟨w, hwa, hwy, hqw⟩
      exact ⟨w, ⟨hwa, hwy⟩, hqw⟩
  rcases hz₁ with ⟨z₁, hz₁mem, hz₁gt⟩
  rcases hz₂ with ⟨z₂, hz₂mem, hz₂gt⟩
  have hz₁ab : z₁ ∈ Set.Ioo a b := ⟨hz₁mem.1, lt_trans hz₁mem.2 hyb⟩
  have hz₂ab : z₂ ∈ Set.Ioo a b := ⟨lt_trans hay hz₂mem.1, hz₂mem.2⟩
  have hyab : y ∈ Set.Ioo a b := ⟨hay, hyb⟩
  have hL1 : Real.log (q y) < Real.log (q z₁) := Real.log_lt_log hqy hz₁gt
  have hL2 : Real.log (q y) < Real.log (q z₂) := Real.log_lt_log hqy hz₂gt
  exact fc_concave_not_gt_both (L := fun t => Real.log (q t)) hlog hz₁ab hyab hz₂ab
    hz₁mem.2 hz₂mem.1 hL1 hL2

/-- `q` is monotone decreasing on `[m,b]` when `m` is a maximizer. -/
private lemma fc_q_antitone_right {a b m : ℝ} (hab : a < b) (q : ℝ → ℝ)
    (hmem : m ∈ Set.Icc a b) (hmax : ∀ t ∈ Set.Icc a b, q t ≤ q m)
    (hqcont : ContinuousOn q (Set.Icc a b))
    (hqpos : ∀ t : ℝ, a < t → t < b → 0 < q t)
    (hlog : ConcaveOn ℝ (Set.Ioo a b) (fun t : ℝ => Real.log (q t))) :
    AntitoneOn q (Set.Icc m b) := by
  have hcwA : ContinuousWithinAt q (Set.Ioi a) a := fc_rightCont q hab hqcont
  have hcwB : ContinuousWithinAt q (Set.Iio b) b := fc_leftCont q hab hqcont
  intro x hx y hy hxy
  by_contra hnot
  have hxlt : q x < q y := lt_of_not_ge hnot
  have hnexy : x ≠ y := by
    intro heq
    subst y
    exact (lt_irrefl (q x)) hxlt
  have hxly : x < y := lt_of_le_of_ne hxy hnexy
  by_cases hxm : x = m
  · subst x
    exact (not_le_of_gt hxlt) (hmax y (by constructor <;> linarith [hy.1, hy.2, hmem.1]))
  have hmx : m < x := lt_of_le_of_ne hx.1 (Ne.symm hxm)
  have hax : a < x := lt_of_le_of_lt hmem.1 hmx
  have hxb : x < b := lt_of_lt_of_le hxly hy.2
  have hqx : 0 < q x := hqpos x hax hxb
  have hz₁ : ∃ z, z ∈ Set.Ioo a x ∧ q x < q z := by
    by_cases ham : a < m
    · refine ⟨m, ⟨ham, hmx⟩, lt_of_lt_of_le hxlt (hmax y (by constructor <;> linarith [hy.1, hy.2, hmem.1]))⟩
    · have hma : m ≤ a := le_of_not_gt ham
      have hmaEq : m = a := le_antisymm hma hmem.1
      subst m
      rcases fc_right_pull q hax (lt_of_lt_of_le hxlt (hmax y (by constructor <;> linarith [hy.1, hy.2]))) hcwA with ⟨w, hwa, hwx, hqw⟩
      exact ⟨w, ⟨hwa, hwx⟩, hqw⟩
  have hz₂ : ∃ z, z ∈ Set.Ioo x b ∧ q x < q z := by
    by_cases hyb : y < b
    · refine ⟨y, ⟨hxly, hyb⟩, hxlt⟩
    · have hby : b ≤ y := le_of_not_gt hyb
      have hbyEq : y = b := le_antisymm hy.2 hby
      subst y
      rcases fc_left_pull q hxb hxlt hcwB with ⟨w, hwx, hwb, hqw⟩
      exact ⟨w, ⟨hwx, hwb⟩, hqw⟩
  rcases hz₁ with ⟨z₁, hz₁mem, hz₁gt⟩
  rcases hz₂ with ⟨z₂, hz₂mem, hz₂gt⟩
  have hz₁ab : z₁ ∈ Set.Ioo a b := ⟨hz₁mem.1, lt_trans hz₁mem.2 hxb⟩
  have hz₂ab : z₂ ∈ Set.Ioo a b := ⟨lt_trans hax hz₂mem.1, hz₂mem.2⟩
  have hxab : x ∈ Set.Ioo a b := ⟨hax, hxb⟩
  have hL1 : Real.log (q x) < Real.log (q z₁) := Real.log_lt_log hqx hz₁gt
  have hL2 : Real.log (q x) < Real.log (q z₂) := Real.log_lt_log hqx hz₂gt
  exact fc_concave_not_gt_both (L := fun t => Real.log (q t)) hlog hz₁ab hxab hz₂ab
    hz₁mem.2 hz₂mem.1 hL1 hL2

/-- **From log-concavity to unimodality.**  A continuous `q ≥ 0` on `[a,b]`
whose log is concave on the open interval is unimodal: there is `m` with
`UnimodalOn a b m q`. -/
theorem unimodal_of_log_concave {a b : ℝ} (hab : a ≤ b) (q : ℝ → ℝ)
    (hqcont : ContinuousOn q (Set.Icc a b))
    (hqpos : ∀ t : ℝ, a < t → t < b → 0 < q t)
    (hlog : ConcaveOn ℝ (Set.Ioo a b) (fun t : ℝ => Real.log (q t))) :
    ∃ m : ℝ, UnimodalOn a b m q := by
  by_cases hab' : a = b
  · subst b
    refine ⟨a, ?_⟩
    constructor
    · exact le_rfl
    constructor
    · exact le_rfl
    constructor
    · intro x hx y hy hxy
      have hxeq : x = a := le_antisymm hx.2 hx.1
      have hyeq : y = a := le_antisymm hy.2 hy.1
      rw [hxeq, hyeq]
    · intro x hx y hy hxy
      have hxeq : x = a := le_antisymm hx.2 hx.1
      have hyeq : y = a := le_antisymm hy.2 hy.1
      rw [hxeq, hyeq]
  · have hlt : a < b := lt_of_le_of_ne hab hab'
    rcases IsCompact.exists_isMaxOn isCompact_Icc (Set.nonempty_Icc.mpr hab) hqcont with ⟨m, hmem, hmax⟩
    refine ⟨m, ?_⟩
    constructor
    · exact hmem.1
    constructor
    · exact hmem.2
    constructor
    · exact fc_q_monotone_left hlt q hmem (fun t ht => isMaxOn_iff.mp hmax t ht) hqcont hqpos hlog
    · exact fc_q_antitone_right hlt q hmem (fun t ht => isMaxOn_iff.mp hmax t ht) hqcont hqpos hlog

/-- Concavity is preserved under increasing affine reparametrization. -/
theorem concaveOn_comp_affine {u v r c : ℝ} (hr : 0 < r) {f : ℝ → ℝ}
    (hf : ConcaveOn ℝ (Set.Ioo u v) f) :
    ConcaveOn ℝ (Set.Ioo (r * u + c) (r * v + c)) (fun t : ℝ => f ((t - c) / r)) := by
  constructor
  · exact convex_Ioo _ _
  · intro x hx y hy a b ha hb hab
    have hx' : (x - c) / r ∈ Set.Ioo u v := by
      constructor
      · have h1 : r * u < x - c := by nlinarith [hx.1]
        exact (lt_div_iff₀ hr).2 (by simpa [mul_comm] using h1)
      · have h2 : x - c < r * v := by nlinarith [hx.2]
        exact (div_lt_iff₀ hr).2 (by simpa [mul_comm] using h2)
    have hy' : (y - c) / r ∈ Set.Ioo u v := by
      constructor
      · have h1 : r * u < y - c := by nlinarith [hy.1]
        exact (lt_div_iff₀ hr).2 (by simpa [mul_comm] using h1)
      · have h2 : y - c < r * v := by nlinarith [hy.2]
        exact (div_lt_iff₀ hr).2 (by simpa [mul_comm] using h2)
    change a • f ((x - c) / r) + b • f ((y - c) / r) ≤
      f ((a • x + b • y - c) / r)
    have hmain := hf.2 hx' hy' ha hb hab
    have harg : a • ((x - c) / r) + b • ((y - c) / r) = (a • x + b • y - c) / r := by
      simp only [smul_eq_mul]
      have hc : c * (a + b) = c := by rw [hab]; ring
      calc
        a * ((x - c) / r) + b * ((y - c) / r)
            = (a * (x - c)) / r + (b * (y - c)) / r := by
                congr 1 <;> rw [← mul_div_assoc]
        _ = (a * (x - c) + b * (y - c)) / r := by rw [add_div]
        _ = (a * x + b * y - c) / r := by
            congr 1
            ring_nf
            nlinarith [hab, hc]
    rw [← harg]
    exact hmain

/-- Unimodality is preserved under increasing affine reparametrization. -/
theorem unimodalOn_comp_affine {a b m r c : ℝ} (hr : 0 < r) (q : ℝ → ℝ)
    (hq : UnimodalOn a b m q) :
    UnimodalOn (r * a + c) (r * b + c) (r * m + c) (fun t : ℝ => q ((t - c) / r)) := by
  constructor
  · nlinarith [hq.1]
  constructor
  · nlinarith [hq.2.1]
  constructor
  · intro x hx y hy hxy
    have hx' : (x - c) / r ∈ Set.Icc a m := by
      constructor
      · have h1 : r * a ≤ x - c := by nlinarith [hx.1]
        exact (le_div_iff₀ hr).2 (by simpa [mul_comm] using h1)
      · have h2 : x - c ≤ r * m := by nlinarith [hx.2]
        exact (div_le_iff₀ hr).2 (by simpa [mul_comm] using h2)
    have hy' : (y - c) / r ∈ Set.Icc a m := by
      constructor
      · have h1 : r * a ≤ y - c := by nlinarith [hy.1]
        exact (le_div_iff₀ hr).2 (by simpa [mul_comm] using h1)
      · have h2 : y - c ≤ r * m := by nlinarith [hy.2]
        exact (div_le_iff₀ hr).2 (by simpa [mul_comm] using h2)
    have hle' : (x - c) / r ≤ (y - c) / r :=
      div_le_div_of_nonneg_right (by linarith) (le_of_lt hr)
    exact hq.2.2.1 hx' hy' hle'
  · intro x hx y hy hxy
    have hx' : (x - c) / r ∈ Set.Icc m b := by
      constructor
      · have h1 : r * m ≤ x - c := by nlinarith [hx.1]
        exact (le_div_iff₀ hr).2 (by simpa [mul_comm] using h1)
      · have h2 : x - c ≤ r * b := by nlinarith [hx.2]
        exact (div_le_iff₀ hr).2 (by simpa [mul_comm] using h2)
    have hy' : (y - c) / r ∈ Set.Icc m b := by
      constructor
      · have h1 : r * m ≤ y - c := by nlinarith [hy.1]
        exact (le_div_iff₀ hr).2 (by simpa [mul_comm] using h1)
      · have h2 : y - c ≤ r * b := by nlinarith [hy.2]
        exact (div_le_iff₀ hr).2 (by simpa [mul_comm] using h2)
    have hle' : (x - c) / r ≤ (y - c) / r :=
      div_le_div_of_nonneg_right (by linarith) (le_of_lt hr)
    exact hq.2.2.2 hx' hy' hle'

end Submission.Core

end
