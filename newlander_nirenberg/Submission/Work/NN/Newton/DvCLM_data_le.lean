import Mathlib
import Submission.Work.NN.Newton.pushforward_setup
import Submission.Work.NN.Newton.holderNorm_one_fderiv_coeff_le
import Submission.Work.NN.Newton.holderNorm_two_deriv_bounds
import Submission.Work.NN.Newton.contDiffOn_DvCLM
import Submission.Work.NN.Newton.fderiv_DvCLM_apply

namespace Work.NN.Newton

open scoped NNReal ENNReal ContDiff
open Set

-- `0 < R` is part of the interface of `DvCLM_data_le` but is not needed by the argument.
set_option linter.unusedVariables false

/-! ## Auxiliary lemmas about `ContinuousLinearMap.pi` -/

section PiNorm

variable {ι : Type*} [Fintype ι]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {Y : ι → Type*} [∀ i, NormedAddCommGroup (Y i)] [∀ i, NormedSpace ℝ (Y i)]

/-- If all the components of a family of continuous linear maps are bounded by `B`, then so is
the operator norm of the `pi`-combination. -/
lemma opNorm_pi_le_of_le {f : ∀ i, X →L[ℝ] Y i} {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ i, ‖f i‖ ≤ B) : ‖ContinuousLinearMap.pi f‖ ≤ B := by
  refine ContinuousLinearMap.opNorm_le_bound _ hB fun v => ?_
  rw [pi_norm_le_iff_of_nonneg (mul_nonneg hB (norm_nonneg v))]
  intro i
  rw [ContinuousLinearMap.pi_apply]
  calc ‖f i v‖ ≤ ‖f i‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ B * ‖v‖ := mul_le_mul_of_nonneg_right (h i) (norm_nonneg v)

end PiNorm

section PiSub

variable {ι : Type*} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {Y : ι → Type*} [∀ i, NormedAddCommGroup (Y i)] [∀ i, NormedSpace ℝ (Y i)]

/-- `ContinuousLinearMap.pi` is additive (the general API has no `sub` lemma). -/
lemma pi_sub_pi (f g : ∀ i, X →L[ℝ] Y i) :
    ContinuousLinearMap.pi f - ContinuousLinearMap.pi g
      = ContinuousLinearMap.pi (fun i => f i - g i) := by
  ext v i
  simp [ContinuousLinearMap.pi_apply]

end PiSub

/-- The `holderNorm 2` bound controls the Hölder seminorm of the first derivative. -/
lemma norm_fderiv_sub_le_of_holderNorm_two {n : ℕ} {α b R : ℝ} (hα0 : 0 < α)
    {u : Work.NN.Core.Cn n → ℂ} (hb0 : 0 ≤ b)
    (hb : Work.CR.Flat.holderNorm 2 α u (Pd n R) ≤ ENNReal.ofReal b) :
    ∀ x ∈ Pd n R, ∀ y ∈ Pd n R, ‖fderiv ℝ u x - fderiv ℝ u y‖ ≤ b * ‖x - y‖ ^ α := by
  intro x hx y hy
  have hPopen : IsOpen (Pd n R) := isOpen_Pd n R
  have h := norm_sub_iteratedFDerivWithin_le_of_holderNorm_le
    (X := Work.NN.Core.Cn n) hα0 hb0 hb (i := 1) (by norm_num) hx hy
  rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (s := Pd n R) (f := u) 1 hPopen hx,
    iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (s := Pd n R) (f := u) 1 hPopen hy,
    norm_iteratedFDeriv_one_sub_eq_gen'] at h
  exact h

/-- From a `C^{2,α}` bound on the components `v l` on the polydisc `Pd n R`, the coefficient
map `z ↦ DvCLM v z = ContinuousLinearMap.pi (fun l => fderiv ℝ (v l) z)` is `C¹` on `Pd n R`,
and it, its derivative, and their differences are all bounded by `b`.

(The hypothesis `0 < R` is part of the interface; the argument only uses that `Pd n R` is open
and that the `C^{2,α}` norms are finite, both of which hold for every `R`.) -/
theorem DvCLM_data_le {n : ℕ} {α : ℝ} (hα0 : 0 < α) {R : ℝ} (hR : 0 < R)
    {v : Fin n → Work.NN.Core.Cn n → ℂ}
    (hv : ∀ l, ∀ m : ℕ, ContDiffOn ℝ m (v l) (Work.NN.Newton.Pd n R))
    {b : ℝ} (hb0 : 0 ≤ b)
    (hb : ∀ l, Work.CR.Flat.holderNorm 2 α (v l) (Work.NN.Newton.Pd n R) ≤ ENNReal.ofReal b) :
    ContDiffOn ℝ 1 (Work.NN.Newton.DvCLM v) (Work.NN.Newton.Pd n R) ∧
    (∀ z ∈ Work.NN.Newton.Pd n R, ‖Work.NN.Newton.DvCLM v z‖ ≤ b) ∧
    (∀ z ∈ Work.NN.Newton.Pd n R, ‖fderiv ℝ (Work.NN.Newton.DvCLM v) z‖ ≤ b) ∧
    (∀ x ∈ Work.NN.Newton.Pd n R, ∀ y ∈ Work.NN.Newton.Pd n R,
      ‖Work.NN.Newton.DvCLM v x - Work.NN.Newton.DvCLM v y‖ ≤ b * ‖x - y‖ ^ α) ∧
    (∀ x ∈ Work.NN.Newton.Pd n R, ∀ y ∈ Work.NN.Newton.Pd n R,
      ‖fderiv ℝ (Work.NN.Newton.DvCLM v) x - fderiv ℝ (Work.NN.Newton.DvCLM v) y‖
        ≤ b * ‖x - y‖ ^ α) := by
  have hPopen : IsOpen (Pd n R) := isOpen_Pd n R
  -- the scalar bounds read off the `C^{2,α}` hypothesis
  have h10 : ∀ l : Fin n, ∀ z ∈ Pd n R, ‖fderiv ℝ (v l) z‖ ≤ b :=
    fun l => (holderNorm_two_deriv_bounds hα0 hb0 (hb l)).1
  have h1H : ∀ l : Fin n, ∀ x ∈ Pd n R, ∀ y ∈ Pd n R,
      ‖fderiv ℝ (v l) x - fderiv ℝ (v l) y‖ ≤ b * ‖x - y‖ ^ α :=
    fun l => norm_fderiv_sub_le_of_holderNorm_two hα0 hb0 (hb l)
  have h20 : ∀ l : Fin n, ∀ z ∈ Pd n R,
      ‖fderiv ℝ (fun z => fderiv ℝ (v l) z) z‖ ≤ b :=
    fun l => (holderNorm_two_deriv_bounds hα0 hb0 (hb l)).2.1
  have h2H : ∀ l : Fin n, ∀ x ∈ Pd n R, ∀ y ∈ Pd n R,
      ‖fderiv ℝ (fun z => fderiv ℝ (v l) z) x
        - fderiv ℝ (fun z => fderiv ℝ (v l) z) y‖ ≤ b * ‖x - y‖ ^ α :=
    fun l => (holderNorm_two_deriv_bounds hα0 hb0 (hb l)).2.2
  -- `fderiv ℝ (v l)` is differentiable on the polydisc, since `v l` is `C³` there
  have hd : ∀ (l : Fin n) (x : Work.NN.Core.Cn n), x ∈ Pd n R →
      DifferentiableAt ℝ (fun z => fderiv ℝ (v l) z) x := by
    intro l x hx
    have h2 : ContDiffOn ℝ 2 (fun z => fderiv ℝ (v l) z) (Pd n R) :=
      (hv l 3).fderiv_of_isOpen hPopen (by norm_num)
    exact (h2.differentiableOn (by norm_num)).differentiableAt (hPopen.mem_nhds hx)
  -- the derivative of `DvCLM v` is the `pi` of the second derivatives of the components
  have hfd : ∀ (x : Work.NN.Core.Cn n), x ∈ Pd n R → ∀ h : Work.NN.Core.Cn n,
      fderiv ℝ (DvCLM v) x h
        = ContinuousLinearMap.pi (fun l : Fin n => fderiv ℝ (fun z => fderiv ℝ (v l) z) x h) :=
    fun x hx h => fderiv_DvCLM_apply (fun l => hd l x hx) h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact contDiffOn_DvCLM (fun l => hv l 2)
  · intro z hz
    have hD : DvCLM v z = ContinuousLinearMap.pi (fun l : Fin n => fderiv ℝ (v l) z) := rfl
    rw [hD]
    exact opNorm_pi_le_of_le hb0 fun l => h10 l z hz
  · intro z hz
    refine ContinuousLinearMap.opNorm_le_bound _ hb0 fun h => ?_
    rw [hfd z hz h]
    exact opNorm_pi_le_of_le (mul_nonneg hb0 (norm_nonneg h)) fun l => by
      calc ‖fderiv ℝ (fun z => fderiv ℝ (v l) z) z h‖
          ≤ ‖fderiv ℝ (fun z => fderiv ℝ (v l) z) z‖ * ‖h‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ b * ‖h‖ := mul_le_mul_of_nonneg_right (h20 l z hz) (norm_nonneg h)
  · intro x hx y hy
    have hxy : DvCLM v x - DvCLM v y
        = ContinuousLinearMap.pi (fun l : Fin n => fderiv ℝ (v l) x - fderiv ℝ (v l) y) := by
      simpa only [DvCLM] using
        (pi_sub_pi (fun l : Fin n => fderiv ℝ (v l) x) (fun l : Fin n => fderiv ℝ (v l) y))
    rw [hxy]
    exact opNorm_pi_le_of_le (mul_nonneg hb0 (Real.rpow_nonneg (norm_nonneg _) α))
      fun l => h1H l x hx y hy
  · intro x hx y hy
    refine ContinuousLinearMap.opNorm_le_bound _
      (mul_nonneg hb0 (Real.rpow_nonneg (norm_nonneg _) α)) fun h => ?_
    rw [sub_apply, hfd x hx h, hfd y hy h, pi_sub_pi]
    refine opNorm_pi_le_of_le (mul_nonneg (mul_nonneg hb0 (Real.rpow_nonneg (norm_nonneg _) α))
      (norm_nonneg h)) fun l => ?_
    calc ‖fderiv ℝ (fun z => fderiv ℝ (v l) z) x h - fderiv ℝ (fun z => fderiv ℝ (v l) z) y h‖
        = ‖(fderiv ℝ (fun z => fderiv ℝ (v l) z) x
            - fderiv ℝ (fun z => fderiv ℝ (v l) z) y) h‖ := congrArg norm (sub_apply _ _ _).symm
      _ ≤ ‖fderiv ℝ (fun z => fderiv ℝ (v l) z) x
            - fderiv ℝ (fun z => fderiv ℝ (v l) z) y‖ * ‖h‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (b * ‖x - y‖ ^ α) * ‖h‖ :=
          mul_le_mul_of_nonneg_right (h2H l x hx y hy) (norm_nonneg h)

end Work.NN.Newton
