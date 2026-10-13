import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.Spaces.Gamma_WlInf

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Nblock6.Auxiliary

open scoped Real Topology
open Filter

set_option autoImplicit false

/-- Right-hand side of the `m`-fold Leibniz expansion of `dthU` (the angular derivation
`φ ↦ sin(2θ)·φ'`). -/
noncomputable def dthLf (m : ℕ) (f g : ℝ → ℝ) : ℝ → ℝ :=
  fun θ => ∑ i ∈ Finset.range (m + 1),
    (m.choose i : ℝ) * (Work.Spaces.dthU^[i] f θ * Work.Spaces.dthU^[m - i] g θ)

lemma dthLf_apply (m : ℕ) (f g : ℝ → ℝ) (θ : ℝ) :
    dthLf m f g θ = ∑ i ∈ Finset.range (m + 1),
      (m.choose i : ℝ) * (Work.Spaces.dthU^[i] f θ * Work.Spaces.dthU^[m - i] g θ) := rfl

/-- The defining relation of `dthU`: `sin (2θ) · (dthU^i φ)' = dthU^{i+1} φ`.  Note that this is
unconditional: it is a definitional unfolding of `dthU`. -/
lemma sin_mul_deriv_dthU (i : ℕ) (φ : ℝ → ℝ) (θ : ℝ) :
    Real.sin (2 * θ) * deriv (Work.Spaces.dthU^[i] φ) θ = Work.Spaces.dthU^[i + 1] φ θ := by
  rw [← Work.Spaces.dthU_iter_succ_apply i φ]
  rfl

/-- The pointwise derivative of the Leibniz sum, assuming only that the individual iterates of
`f` and `g` (up to `m`) are differentiable at `θ`. -/
lemma deriv_dthLf (m : ℕ) (f g : ℝ → ℝ) (θ : ℝ)
    (hf : ∀ i ≤ m, DifferentiableAt ℝ (Work.Spaces.dthU^[i] f) θ)
    (hg : ∀ i ≤ m, DifferentiableAt ℝ (Work.Spaces.dthU^[i] g) θ) :
    deriv (dthLf m f g) θ =
      ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
        (deriv (Work.Spaces.dthU^[i] f) θ * Work.Spaces.dthU^[m - i] g θ
          + Work.Spaces.dthU^[i] f θ * deriv (Work.Spaces.dthU^[m - i] g) θ) := by
  have hterm : ∀ i ∈ Finset.range (m + 1),
      DifferentiableAt ℝ (fun y => (m.choose i : ℝ) *
        (Work.Spaces.dthU^[i] f y * Work.Spaces.dthU^[m - i] g y)) θ := by
    intro i hi
    rw [Finset.mem_range] at hi
    exact ((hf i (by omega)).mul (hg (m - i) (by omega))).const_mul _
  unfold dthLf
  rw [deriv_fun_sum hterm]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  have him : i ≤ m := by omega
  have hmi : m - i ≤ m := by omega
  rw [Work.Spaces.deriv_const_mul']
  rw [show deriv (fun y => Work.Spaces.dthU^[i] f y * Work.Spaces.dthU^[m - i] g y) θ
      = deriv (Work.Spaces.dthU^[i] f) θ * Work.Spaces.dthU^[m - i] g θ
        + Work.Spaces.dthU^[i] f θ * deriv (Work.Spaces.dthU^[m - i] g) θ
      from deriv_mul (hf i him) (hg (m - i) hmi)]

/-- The iterated Leibniz rule for `dthU` on the open interval, with only differentiability of the
individual iterates as hypothesis. -/
lemma dthU_iter_mul_Ioo_aux :
    ∀ (m : ℕ) (f g : ℝ → ℝ),
      (∀ i ≤ m, DifferentiableOn ℝ (Work.Spaces.dthU^[i] f) (Set.Ioo 0 (Real.pi / 2))) →
      (∀ i ≤ m, DifferentiableOn ℝ (Work.Spaces.dthU^[i] g) (Set.Ioo 0 (Real.pi / 2))) →
      Set.EqOn (Work.Spaces.dthU^[m] (f * g)) (dthLf m f g) (Set.Ioo 0 (Real.pi / 2)) := by
  intro m
  induction m with
  | zero =>
      intro f g hf hg θ hθ
      simp [dthLf]
  | succ m ih =>
      intro f g hf hg θ hθ
      have hmem : Set.Ioo (0 : ℝ) (Real.pi / 2) ∈ 𝓝 θ := IsOpen.mem_nhds isOpen_Ioo hθ
      have hfm : ∀ i ≤ m,
          DifferentiableOn ℝ (Work.Spaces.dthU^[i] f) (Set.Ioo 0 (Real.pi / 2)) :=
        fun i hi => hf i (by omega)
      have hgm : ∀ i ≤ m,
          DifferentiableOn ℝ (Work.Spaces.dthU^[i] g) (Set.Ioo 0 (Real.pi / 2)) :=
        fun i hi => hg i (by omega)
      have hAt : ∀ i ≤ m, DifferentiableAt ℝ (Work.Spaces.dthU^[i] f) θ :=
        fun i hi => (hfm i hi).differentiableAt hmem
      have hAtg : ∀ i ≤ m, DifferentiableAt ℝ (Work.Spaces.dthU^[i] g) θ :=
        fun i hi => (hgm i hi).differentiableAt hmem
      have hev : Filter.EventuallyEq (𝓝 θ) (Work.Spaces.dthU^[m] (f * g)) (dthLf m f g) :=
        (ih f g hfm hgm).eventuallyEq_of_mem hmem
      rw [← Work.Spaces.dthU_iter_succ_apply m (f * g), Work.Spaces.dthU_apply, hev.deriv_eq,
        deriv_dthLf m f g θ hAt hAtg, Finset.mul_sum]
      have h1 : ∀ i ∈ Finset.range (m + 1),
          Real.sin (2 * θ) * ((m.choose i : ℝ) *
              (deriv (Work.Spaces.dthU^[i] f) θ * Work.Spaces.dthU^[m - i] g θ
                + Work.Spaces.dthU^[i] f θ * deriv (Work.Spaces.dthU^[m - i] g) θ))
            = (m.choose i : ℝ) *
                (Work.Spaces.dthU^[i] f θ * Work.Spaces.dthU^[m + 1 - i] g θ)
              + (m.choose i : ℝ) *
                (Work.Spaces.dthU^[i + 1] f θ * Work.Spaces.dthU^[m - i] g θ) := by
        intro i hi
        rw [Finset.mem_range] at hi
        have him : i ≤ m := by omega
        rw [show Real.sin (2 * θ) * ((m.choose i : ℝ) *
              (deriv (Work.Spaces.dthU^[i] f) θ * Work.Spaces.dthU^[m - i] g θ
                + Work.Spaces.dthU^[i] f θ * deriv (Work.Spaces.dthU^[m - i] g) θ))
            = (m.choose i : ℝ) *
                ((Real.sin (2 * θ) * deriv (Work.Spaces.dthU^[i] f) θ)
                  * Work.Spaces.dthU^[m - i] g θ)
              + (m.choose i : ℝ) *
                (Work.Spaces.dthU^[i] f θ
                  * (Real.sin (2 * θ) * deriv (Work.Spaces.dthU^[m - i] g) θ))
            from by ring]
        rw [sin_mul_deriv_dthU i f θ, sin_mul_deriv_dthU (m - i) g θ,
          show m - i + 1 = m + 1 - i from by omega]
        ring
      trans ∑ i ∈ Finset.range (m + 1),
          ((m.choose i : ℝ) * (Work.Spaces.dthU^[i] f θ * Work.Spaces.dthU^[m + 1 - i] g θ)
            + (m.choose i : ℝ) *
                (Work.Spaces.dthU^[i + 1] f θ * Work.Spaces.dthU^[m - i] g θ))
      · exact Finset.sum_congr rfl h1
      · rw [Finset.sum_add_distrib, dthLf_apply]
        have hS : (∑ i ∈ Finset.range (m + 2),
              ((m + 1).choose i : ℝ) *
                (Work.Spaces.dthU^[i] f θ * Work.Spaces.dthU^[m + 1 - i] g θ))
            = (∑ i ∈ Finset.range (m + 1),
                  (m.choose i : ℝ) *
                    (Work.Spaces.dthU^[i] f θ * Work.Spaces.dthU^[m + 1 - i] g θ))
              + ∑ i ∈ Finset.range (m + 1),
                  (m.choose i : ℝ) *
                    (Work.Spaces.dthU^[i + 1] f θ * Work.Spaces.dthU^[m - i] g θ) := by
          rw [show (m + 1) + 1 = m + 2 from rfl]
          exact Finset.sum_choose_succ_mul
            (fun a b => Work.Spaces.dthU^[a] f θ * Work.Spaces.dthU^[b] g θ) m
        rw [hS]

theorem dthU_iter_mul_Ioo (m : ℕ) (f g : ℝ → ℝ)
    (hf : ∀ i ≤ m, DifferentiableOn ℝ (Work.Spaces.dthU^[i] f) (Set.Ioo 0 (Real.pi / 2)))
    (hg : ∀ i ≤ m, DifferentiableOn ℝ (Work.Spaces.dthU^[i] g) (Set.Ioo 0 (Real.pi / 2))) :
    Set.EqOn (Work.Spaces.dthU^[m] (f * g))
      (fun θ => ∑ i ∈ Finset.range (m + 1),
        (m.choose i : ℝ) * (Work.Spaces.dthU^[i] f θ * Work.Spaces.dthU^[m - i] g θ))
      (Set.Ioo 0 (Real.pi / 2)) := by
  intro θ hθ
  have h := dthU_iter_mul_Ioo_aux m f g hf hg hθ
  simp only [dthLf] at h
  exact h

end Work.FTS.StrongEps.E4R3.Nblock6.Auxiliary
