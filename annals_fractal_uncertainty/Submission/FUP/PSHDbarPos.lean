import Submission.FUP.Hormander

open FractalUncertainty MeasureTheory FourierTransform Metric
open scoped ENNReal BigOperators ContDiff

set_option autoImplicit false
variable {d : ℕ}
local notation "ℂᵈ" => (Fin d → ℂ)

/-!
# Transferring `∂∂̄φ ≥ κ` from smooth plurisubharmonic weights to arbitrary PSH weights

`DbarDbarPos φ κ` (Hörmander's distributional positivity condition, `Dbar.lean`) is proved in two
steps:

* for a *smooth* `φ` it reduces, by two integrations by parts, to the pointwise inequality
  `κ z * ‖w‖² ≤ (D²φ z)![w,w] + (D²φ z)![I•w, I•w]`, which says that the real Hessian of `φ`
  restricted to the complex plane spanned by `w` is `≥ κ` — this is `dbarDbarPos_of_hessian`;
* an arbitrary `IsPSH` weight is approximated by its convolution with a smooth kernel: the
  convolution is smooth and still PSH (the sub-mean-value property is preserved by averaging),
  dominates the original (`u_ε ≥ u`) and converges to it, so the positivity passes to the limit.

This module contains the elementary bookkeeping (integrability, continuity and compact support of
the test integrands, additivity and scaling of `DbarDbarPos`).
-/

namespace Submission.FUP

section Basic

/-- A real function on `ℂᵈ` which is bounded on every ball. -/
def BoundedOnCompact (φ : ℂᵈ → ℝ) : Prop :=
  ∀ R : ℝ, ∃ M : ℝ, ∀ z : ℂᵈ, ‖z‖ ≤ R → |φ z| ≤ M

lemma BoundedOnCompact.const_mul {φ : ℂᵈ → ℝ} (hφ : BoundedOnCompact φ) (c : ℝ) :
    BoundedOnCompact (fun z => c * φ z) := by
  intro R
  obtain ⟨M, hM⟩ := hφ R
  exact ⟨|c| * M, fun z hz => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hM z hz) (abs_nonneg c)⟩

lemma BoundedOnCompact.add {φ ψ : ℂᵈ → ℝ} (hφ : BoundedOnCompact φ) (hψ : BoundedOnCompact ψ) :
    BoundedOnCompact (fun z => φ z + ψ z) := by
  intro R
  obtain ⟨M, hM⟩ := hφ R
  obtain ⟨N, hN⟩ := hψ R
  refine ⟨max M 0 + max N 0, fun z hz => ?_⟩
  have h1 : |φ z| ≤ max M 0 := le_trans (hM z hz) (le_max_left _ _)
  have h2 : |ψ z| ≤ max N 0 := le_trans (hN z hz) (le_max_left _ _)
  calc |φ z + ψ z| ≤ |φ z| + |ψ z| := abs_add_le _ _
    _ ≤ max M 0 + max N 0 := add_le_add h1 h2

end Basic

section Test

lemma hasCompactSupport_finset_sum {ι : Type*} [Fintype ι] {F : ι → ℂᵈ → ℝ}
    (hF : ∀ i, HasCompactSupport (F i)) :
    HasCompactSupport (fun z => ∑ i, F i z) := by
  have hsum : HasCompactSupport (∑ i : ι, F i) :=
    HasCompactSupport.finset_sum (s := Finset.univ) (f := F) (fun i _ => hF i)
  have heq : (fun z : ℂᵈ => ∑ i, F i z) = (∑ i : ι, F i) := by
    funext z
    exact (Finset.sum_apply z Finset.univ F).symm
  rw [heq]
  exact hsum

lemma contDiff_formTest {n : WithTop ℕ∞} {α : ℂᵈ → (Fin d → ℂ)} (hα : ContDiff ℝ n α)
    (j k : Fin d) : ContDiff ℝ n (formTest α j k) := by
  have h1 : ContDiff ℝ n (fun z => α z j) :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℂ) j).contDiff.comp hα
  have h2 : ContDiff ℝ n (fun z => star (α z k)) :=
    Complex.conjCLE.contDiff.comp
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℂ) k).contDiff.comp hα)
  exact Complex.reCLM.contDiff.comp (h1.mul h2)

lemma continuous_formTest {α : ℂᵈ → (Fin d → ℂ)} (hα : Continuous α) (j k : Fin d) :
    Continuous (formTest α j k) := by
  have h1 : Continuous (fun z => α z j) := (continuous_apply j).comp hα
  have h2 : Continuous (fun z => star (α z k)) :=
    Complex.continuous_conj.comp ((continuous_apply k).comp hα)
  exact Complex.continuous_re.comp (h1.mul h2)

lemma contDiff_formImag {n : WithTop ℕ∞} {α : ℂᵈ → (Fin d → ℂ)} (hα : ContDiff ℝ n α)
    (j k : Fin d) : ContDiff ℝ n (formImag α j k) := by
  have h1 : ContDiff ℝ n (fun z => α z j) :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℂ) j).contDiff.comp hα
  have h2 : ContDiff ℝ n (fun z => star (α z k)) :=
    Complex.conjCLE.contDiff.comp
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℂ) k).contDiff.comp hα)
  exact Complex.imCLM.contDiff.comp (h1.mul h2)

lemma continuous_formImag {α : ℂᵈ → (Fin d → ℂ)} (hα : Continuous α) (j k : Fin d) :
    Continuous (formImag α j k) := by
  have h1 : Continuous (fun z => α z j) := (continuous_apply j).comp hα
  have h2 : Continuous (fun z => star (α z k)) :=
    Complex.continuous_conj.comp ((continuous_apply k).comp hα)
  exact Complex.continuous_im.comp (h1.mul h2)

lemma hasCompactSupport_formImag {α : ℂᵈ → (Fin d → ℂ)} (hα : HasCompactSupport α)
    (j k : Fin d) : HasCompactSupport (formImag α j k) := by
  have h1 : HasCompactSupport (fun z : ℂᵈ => α z j) :=
    hα.comp_left (g := fun v : Fin d → ℂ => v j) (by simp)
  have h2 : HasCompactSupport (fun z : ℂᵈ => star (α z k)) :=
    (hα.comp_left (g := fun v : Fin d → ℂ => v k) (by simp)).comp_left
      (g := star) (by simp)
  have h3 : HasCompactSupport (fun z : ℂᵈ => α z j * star (α z k)) :=
    h1.mul_right (f' := fun z : ℂᵈ => star (α z k))
  exact h3.comp_left (g := Complex.im) (by simp)

lemma hasCompactSupport_formTest {α : ℂᵈ → (Fin d → ℂ)} (hα : HasCompactSupport α)
    (j k : Fin d) : HasCompactSupport (formTest α j k) := by
  have h1 : HasCompactSupport (fun z : ℂᵈ => α z j) :=
    hα.comp_left (g := fun v : Fin d → ℂ => v j) (by simp)
  have h2 : HasCompactSupport (fun z : ℂᵈ => star (α z k)) :=
    (hα.comp_left (g := fun v : Fin d → ℂ => v k) (by simp)).comp_left
      (g := star) (by simp)
  have h3 : HasCompactSupport (fun z : ℂᵈ => α z j * star (α z k)) :=
    h1.mul_right (f' := fun z : ℂᵈ => star (α z k))
  exact h3.comp_left (g := Complex.re) (by simp)

lemma continuous_dxx {χ : ℂᵈ → ℝ} (hχ : ContDiff ℝ ∞ χ) (j k : Fin d) :
    Continuous (fun z => dxx j k χ z) :=
  ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => ℂᵈ) ℝ
      ![Pi.single j (1:ℂ), Pi.single k (1:ℂ)]).continuous.comp
    (hχ.continuous_iteratedFDeriv (m := 2) (WithTop.coe_le_coe.mpr le_top)))

lemma continuous_dyy {χ : ℂᵈ → ℝ} (hχ : ContDiff ℝ ∞ χ) (j k : Fin d) :
    Continuous (fun z => dyy j k χ z) :=
  ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => ℂᵈ) ℝ
      ![Pi.single j Complex.I, Pi.single k Complex.I]).continuous.comp
    (hχ.continuous_iteratedFDeriv (m := 2) (WithTop.coe_le_coe.mpr le_top)))

lemma hasCompactSupport_dxx {χ : ℂᵈ → ℝ} (hχ : HasCompactSupport χ) (j k : Fin d) :
    HasCompactSupport (fun z => dxx j k χ z) :=
  (hχ.iteratedFDeriv 2).comp_left
    (g := fun L : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => ℂᵈ) ℝ =>
      L ![Pi.single j (1:ℂ), Pi.single k (1:ℂ)]) (by simp)

lemma hasCompactSupport_dyy {χ : ℂᵈ → ℝ} (hχ : HasCompactSupport χ) (j k : Fin d) :
    HasCompactSupport (fun z => dyy j k χ z) :=
  (hχ.iteratedFDeriv 2).comp_left
    (g := fun L : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => ℂᵈ) ℝ =>
      L ![Pi.single j Complex.I, Pi.single k Complex.I]) (by simp)

lemma continuous_dxy {χ : ℂᵈ → ℝ} (hχ : ContDiff ℝ ∞ χ) (j k : Fin d) :
    Continuous (fun z => dxy j k χ z) :=
  ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => ℂᵈ) ℝ
      ![Pi.single j (1:ℂ), Pi.single k Complex.I]).continuous.comp
    (hχ.continuous_iteratedFDeriv (m := 2) (WithTop.coe_le_coe.mpr le_top)))

lemma continuous_dyx {χ : ℂᵈ → ℝ} (hχ : ContDiff ℝ ∞ χ) (j k : Fin d) :
    Continuous (fun z => dyx j k χ z) :=
  ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => ℂᵈ) ℝ
      ![Pi.single j Complex.I, Pi.single k (1:ℂ)]).continuous.comp
    (hχ.continuous_iteratedFDeriv (m := 2) (WithTop.coe_le_coe.mpr le_top)))

lemma hasCompactSupport_dxy {χ : ℂᵈ → ℝ} (hχ : HasCompactSupport χ) (j k : Fin d) :
    HasCompactSupport (fun z => dxy j k χ z) :=
  (hχ.iteratedFDeriv 2).comp_left
    (g := fun L : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => ℂᵈ) ℝ =>
      L ![Pi.single j (1:ℂ), Pi.single k Complex.I]) (by simp)

lemma hasCompactSupport_dyx {χ : ℂᵈ → ℝ} (hχ : HasCompactSupport χ) (j k : Fin d) :
    HasCompactSupport (fun z => dyx j k χ z) :=
  (hχ.iteratedFDeriv 2).comp_left
    (g := fun L : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => ℂᵈ) ℝ =>
      L ![Pi.single j Complex.I, Pi.single k (1:ℂ)]) (by simp)

lemma continuous_dbarDbarTest {α : ℂᵈ → (Fin d → ℂ)} (hα : ContDiff ℝ ∞ α) :
    Continuous (dbarDbarTest α) := by
  change Continuous (fun z : ℂᵈ => (1/4 : ℝ) * ∑ j : Fin d, ∑ k : Fin d,
    ((dxx j k (formTest α j k) z + dyy j k (formTest α j k) z)
      - dxy j k (formImag α j k) z + dyx j k (formImag α j k) z))
  refine continuous_const.mul ?_
  refine continuous_finsetSum (s := Finset.univ)
    (f := fun j : Fin d => fun z => ∑ k : Fin d,
      ((dxx j k (formTest α j k) z + dyy j k (formTest α j k) z)
        - dxy j k (formImag α j k) z + dyx j k (formImag α j k) z)) (fun j _ => ?_)
  refine continuous_finsetSum (s := Finset.univ)
    (f := fun k : Fin d => fun z =>
      ((dxx j k (formTest α j k) z + dyy j k (formTest α j k) z)
        - dxy j k (formImag α j k) z + dyx j k (formImag α j k) z)) (fun k _ => ?_)
  exact (((continuous_dxx (contDiff_formTest hα j k) j k).add
      (continuous_dyy (contDiff_formTest hα j k) j k)).sub
      (continuous_dxy (contDiff_formImag hα j k) j k)).add
      (continuous_dyx (contDiff_formImag hα j k) j k)

lemma hasCompactSupport_dbarDbarTest {α : ℂᵈ → (Fin d → ℂ)} (hα : HasCompactSupport α) :
    HasCompactSupport (dbarDbarTest α) := by
  change HasCompactSupport (fun z : ℂᵈ => (1/4 : ℝ) * ∑ j : Fin d, ∑ k : Fin d,
    ((dxx j k (formTest α j k) z + dyy j k (formTest α j k) z)
      - dxy j k (formImag α j k) z + dyx j k (formImag α j k) z))
  have hF : HasCompactSupport
      (fun z => ∑ j : Fin d, ∑ k : Fin d,
        ((dxx j k (formTest α j k) z + dyy j k (formTest α j k) z)
          - dxy j k (formImag α j k) z + dyx j k (formImag α j k) z)) :=
    hasCompactSupport_finset_sum (fun j => hasCompactSupport_finset_sum (fun k =>
      (((hasCompactSupport_dxx (hasCompactSupport_formTest hα j k) j k).add
        (hasCompactSupport_dyy (hasCompactSupport_formTest hα j k) j k)).sub
        (hasCompactSupport_dxy (hasCompactSupport_formImag hα j k) j k)).add
        (hasCompactSupport_dyx (hasCompactSupport_formImag hα j k) j k)))
  exact HasCompactSupport.mul_left (f := fun _ : ℂᵈ => (1/4 : ℝ)) hF

lemma continuous_formNormSq {α : ℂᵈ → (Fin d → ℂ)} (hα : Continuous α) :
    Continuous (formNormSq α) := by
  change Continuous (fun z : ℂᵈ => ∑ j : Fin d, ‖α z j‖ ^ 2)
  exact continuous_finsetSum (s := Finset.univ)
    (f := fun j : Fin d => fun z => ‖α z j‖ ^ 2)
    (fun j _ => (((continuous_apply j).comp hα).norm).pow 2)

lemma hasCompactSupport_formNormSq {α : ℂᵈ → (Fin d → ℂ)} (hα : HasCompactSupport α) :
    HasCompactSupport (formNormSq α) := by
  change HasCompactSupport (fun z : ℂᵈ => ∑ j : Fin d, ‖α z j‖ ^ 2)
  exact hα.comp_left (g := fun v : Fin d → ℂ => ∑ j : Fin d, ‖v j‖ ^ 2) (by simp)

/-- A function which is bounded on balls, multiplied by a compactly supported continuous function,
is integrable. -/
lemma integrable_mul_of_boundedOnCompact {φ : ℂᵈ → ℝ} (hφm : Measurable φ)
    (hφ : BoundedOnCompact φ) {g : ℂᵈ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g) :
    Integrable (fun z => φ z * g z) := by
  classical
  obtain ⟨R, hRpos, hR⟩ := hgc.isBounded.exists_pos_norm_le
  have hsupp : Function.support (fun z => φ z * g z) ⊆ Metric.closedBall 0 R := by
    intro z hz
    have hgz : g z ≠ 0 := by
      intro h0; simp [h0] at hz
    have hmem : z ∈ Function.support g := by simpa [Function.mem_support] using hgz
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hR z (subset_tsupport g hmem)
  rw [← integrableOn_iff_integrable_of_support_subset hsupp]
  obtain ⟨M, hM⟩ := hφ R
  obtain ⟨C, hC⟩ := hgc.isCompact.exists_bound_of_continuousOn hg.continuousOn
  refine IntegrableOn.of_bound (isCompact_closedBall (0 : ℂᵈ) R).measure_lt_top
    (hφm.mul hg.measurable).aestronglyMeasurable (max M 0 * max C 0) ?_
  filter_upwards [ae_restrict_mem measurableSet_closedBall] with z hz
  rw [Metric.mem_closedBall, dist_zero_right] at hz
  by_cases hz' : z ∈ tsupport g
  · have h1 : |φ z| ≤ max M 0 := le_trans (hM z hz) (le_max_left _ _)
    have h2 : ‖g z‖ ≤ max C 0 := le_trans (hC z hz') (le_max_left _ _)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul h1 h2 (abs_nonneg _) (le_trans (abs_nonneg _) h1)
  · have h0 : g z = 0 := image_eq_zero_of_notMem_tsupport hz'
    rw [h0, mul_zero, Real.norm_eq_abs, abs_zero]
    positivity

end Test

section Closure

theorem DbarDbarPos.zero : DbarDbarPos (fun _ : ℂᵈ => (0 : ℝ)) (fun _ : ℂᵈ => (0 : ℝ)) := by
  intro α hα hs
  refine ⟨?_, ?_, ?_⟩
  · simp only [zero_mul]; exact integrable_zero _ _ _
  · simp only [zero_mul]; exact integrable_zero _ _ _
  · simp only [zero_mul, integral_zero]
    exact le_refl 0

theorem DbarDbarPos.add {φ ψ : ℂᵈ → ℝ} {k l : ℂᵈ → ℝ}
    (h1 : DbarDbarPos φ k) (h2 : DbarDbarPos ψ l) :
    DbarDbarPos (fun z => φ z + ψ z) (fun z => k z + l z) := by
  intro α hα hs
  obtain ⟨hκ, hφ, hineq⟩ := h1 α hα hs
  obtain ⟨hl, hψ, hineq2⟩ := h2 α hα hs
  have hκ' : Integrable (fun z => (k z + l z) * formNormSq α z) := by
    have h1 := hκ.add hl
    rw [show ((fun z : ℂᵈ => k z * formNormSq α z) + fun z => l z * formNormSq α z)
        = fun z => (k z + l z) * formNormSq α z from by
      funext z; simp only [Pi.add_apply, add_mul]] at h1
    exact h1
  have hφ' : Integrable (fun z => (φ z + ψ z) * dbarDbarTest α z) := by
    have h1 := hφ.add hψ
    rw [show ((fun z : ℂᵈ => φ z * dbarDbarTest α z) + fun z => ψ z * dbarDbarTest α z)
        = fun z => (φ z + ψ z) * dbarDbarTest α z from by
      funext z; simp only [Pi.add_apply, add_mul]] at h1
    exact h1
  refine ⟨hκ', hφ', ?_⟩
  have e1 : (fun z => (k z + l z) * formNormSq α z)
      = fun z => k z * formNormSq α z + l z * formNormSq α z := by
    funext z; simp only [add_mul]
  have e2 : (fun z => (φ z + ψ z) * dbarDbarTest α z)
      = fun z => φ z * dbarDbarTest α z + ψ z * dbarDbarTest α z := by
    funext z; simp only [add_mul]
  have h1' : ∫ z, (k z + l z) * formNormSq α z
      = (∫ z, k z * formNormSq α z) + ∫ z, l z * formNormSq α z := by
    rw [e1]; exact integral_add hκ hl
  have h2' : ∫ z, (φ z + ψ z) * dbarDbarTest α z
      = (∫ z, φ z * dbarDbarTest α z) + ∫ z, ψ z * dbarDbarTest α z := by
    rw [e2]; exact integral_add hφ hψ
  rw [h1', h2']; linarith

theorem DbarDbarPos.const_mul {φ : ℂᵈ → ℝ} {k : ℂᵈ → ℝ} (h : DbarDbarPos φ k)
    {c : ℝ} (hc : 0 ≤ c) : DbarDbarPos (fun z => c * φ z) (fun z => c * k z) := by
  intro α hα hs
  obtain ⟨hκ, hφ, hineq⟩ := h α hα hs
  have hκ' : Integrable (fun z => (c * k z) * formNormSq α z) := by
    have h1 := hκ.const_mul c
    rw [show (fun z : ℂᵈ => c * (k z * formNormSq α z))
        = fun z => (c * k z) * formNormSq α z from by
      funext z; simp only [mul_assoc]] at h1
    exact h1
  have hφ' : Integrable (fun z => (c * φ z) * dbarDbarTest α z) := by
    have h1 := hφ.const_mul c
    rw [show (fun z : ℂᵈ => c * (φ z * dbarDbarTest α z))
        = fun z => (c * φ z) * dbarDbarTest α z from by
      funext z; simp only [mul_assoc]] at h1
    exact h1
  refine ⟨hκ', hφ', ?_⟩
  have h1' : ∫ z, (c * k z) * formNormSq α z = c * ∫ z, k z * formNormSq α z := by
    simp only [mul_assoc]; exact integral_const_mul c _
  have h2' : ∫ z, (c * φ z) * dbarDbarTest α z = c * ∫ z, φ z * dbarDbarTest α z := by
    simp only [mul_assoc]; exact integral_const_mul c _
  rw [h1', h2']
  exact mul_le_mul_of_nonneg_left hineq hc

end Closure

end Submission.FUP
