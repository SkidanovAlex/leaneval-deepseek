/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# Linearity of the telescoping solution operator `G.recU`, continuity version

The companion result `Work.NN.Ratio.recU_linear` proves that `G.recU` is affine in its
datum under `C^1` hypotheses.  The argument actually only ever uses *continuity* of the
datum (which is what makes the Cauchy-type transform `dbarTransform` well defined and
additive through its integral representation).  Here we record the corresponding
statement with mere continuity hypotheses, which is the form in which the
Newlander–Nirenberg contraction argument consumes it.
-/
import Mathlib
import Submission.Work.NN.Ratio.Defs
import Submission.Work.NN.Ratio.recU_linear

noncomputable section

open scoped NNReal ENNReal ContDiff
open Set MeasureTheory

namespace Work.NN.Ratio

variable {n : ℕ}

/-- The transform radius strictly exceeds the outer cutoff threshold. -/
private lemma b_lt_r (G : Geom n) : G.b < G.r := by linarith [G.hr, G.ha, G.hab]

/-! ## Linearity of the one-coordinate Cauchy-type transform -/

/-- `dbarTransform` is additive in its datum, for continuous data. -/
private lemma dbarT_add (j : Fin n) {ρ : ℝ} {g g' : (Fin n → ℂ) → ℂ}
    (hg : Continuous g) (hg' : Continuous g') (z : Fin n → ℂ) :
    Work.CR.Flat.Cauchy.dbarTransform ρ j (fun y => g y + g' y) z
      = Work.CR.Flat.Cauchy.dbarTransform ρ j g z
        + Work.CR.Flat.Cauchy.dbarTransform ρ j g' z := by
  have h1 : IntegrableOn (fun w : ℂ => g (z + Function.update (0 : Fin n → ℂ) j w) / w)
      (Metric.ball (0 : ℂ) ρ) :=
    Work.CR.Flat.Cauchy.integrableOn_dbarTransform_integrand j hg z
  have h2 : IntegrableOn (fun w : ℂ => g' (z + Function.update (0 : Fin n → ℂ) j w) / w)
      (Metric.ball (0 : ℂ) ρ) :=
    Work.CR.Flat.Cauchy.integrableOn_dbarTransform_integrand j hg' z
  have hsplit : (∫ w in Metric.ball (0 : ℂ) ρ,
        (g (z + Function.update (0 : Fin n → ℂ) j w)
          + g' (z + Function.update (0 : Fin n → ℂ) j w)) / w)
      = (∫ w in Metric.ball (0 : ℂ) ρ, g (z + Function.update (0 : Fin n → ℂ) j w) / w)
        + (∫ w in Metric.ball (0 : ℂ) ρ, g' (z + Function.update (0 : Fin n → ℂ) j w) / w) := by
    rw [← integral_add h1 h2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    ring
  simp only [Work.CR.Flat.Cauchy.dbarTransform]
  rw [hsplit]
  ring

/-- `dbarTransform` is real-homogeneous in its datum, for continuous data. -/
private lemma dbarT_smul (j : Fin n) {ρ : ℝ} (c : ℝ) {g : (Fin n → ℂ) → ℂ}
    (hg : Continuous g) (z : Fin n → ℂ) :
    Work.CR.Flat.Cauchy.dbarTransform ρ j (fun y => c • g y) z
      = c • Work.CR.Flat.Cauchy.dbarTransform ρ j g z := by
  have h1 : IntegrableOn (fun w : ℂ => g (z + Function.update (0 : Fin n → ℂ) j w) / w)
      (Metric.ball (0 : ℂ) ρ) :=
    Work.CR.Flat.Cauchy.integrableOn_dbarTransform_integrand j hg z
  have hsplit : (∫ w in Metric.ball (0 : ℂ) ρ,
        (c • g (z + Function.update (0 : Fin n → ℂ) j w)) / w)
      = c • (∫ w in Metric.ball (0 : ℂ) ρ,
          g (z + Function.update (0 : Fin n → ℂ) j w) / w) := by
    rw [← MeasureTheory.integral_smul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only [Complex.real_smul]
    ring
  simp only [Work.CR.Flat.Cauchy.dbarTransform]
  rw [hsplit]
  simp only [Complex.real_smul]
  ring

/-- `dbarTransform` is affine in its datum, for continuous data. -/
private lemma dbarT_affine (j : Fin n) {ρ : ℝ} (c : ℝ) {g g' : (Fin n → ℂ) → ℂ}
    (hg : Continuous g) (hg' : Continuous g') (z : Fin n → ℂ) :
    Work.CR.Flat.Cauchy.dbarTransform ρ j (fun y => c • g y + g' y) z
      = c • Work.CR.Flat.Cauchy.dbarTransform ρ j g z
        + Work.CR.Flat.Cauchy.dbarTransform ρ j g' z := by
  have h1 := dbarT_add j (ρ := ρ) (g := fun y => c • g y) (g' := g') (hg.const_smul c) hg' z
  have h2 := dbarT_smul j (ρ := ρ) c hg z
  calc Work.CR.Flat.Cauchy.dbarTransform ρ j (fun y => c • g y + g' y) z
      = Work.CR.Flat.Cauchy.dbarTransform ρ j (fun y => c • g y) z
        + Work.CR.Flat.Cauchy.dbarTransform ρ j g' z := h1
    _ = c • Work.CR.Flat.Cauchy.dbarTransform ρ j g z
        + Work.CR.Flat.Cauchy.dbarTransform ρ j g' z := by
        rw [show Work.CR.Flat.Cauchy.dbarTransform ρ j (fun y => c • g y) z
              = c • Work.CR.Flat.Cauchy.dbarTransform ρ j g z from h2]

/-! ## Linearity of the recursion `G.recF` -/

/-- The intermediate data of the recursion are continuous when the datum is. -/
private lemma recF_continuous (G : Geom n) {f : Fin n → (Fin n → ℂ) → ℂ}
    (hf : ∀ j, Continuous (f j)) : ∀ s ≤ n, ∀ k, Continuous (G.recF f s k) := by
  intro s
  induction s with
  | zero => intro _ k; simpa using hf k
  | succ s ihs =>
      intro hs k
      have ih1 : ∀ i, Continuous (G.recF f s i) := ihs (by omega)
      by_cases hlt : s < n
      · have hrec : G.recF f (s + 1) = G.stepData ⟨s, hlt⟩ (G.recF f s) :=
          G.recF_succ_of_lt hlt
        rw [hrec]
        simp only [Geom.stepData]
        have hcont : Continuous (fun y => G.cutFbar ⟨s, hlt⟩ y * G.recF f s k y) :=
          (G.contDiff_cutFbar ⟨s, hlt⟩).continuous.mul (ih1 k)
        exact (Work.CR.Flat.Cauchy.contDiff_dbarTransform (b := G.b) (b_lt_r G) ⟨s, hlt⟩ 0
          (contDiff_zero.mpr hcont)
          (fun y hy => by rw [G.cutFbar_eq_zero_of_ge hy, zero_mul])).continuous
      · have hrec : G.recF f (s + 1) = G.recF f s := by rw [G.recF_succ]; simp [hlt]
        rw [hrec]
        exact ih1 k

/-- The intermediate data of the recursion are affine in the datum. -/
private lemma recF_affine (G : Geom n) (c : ℝ) {f g : Fin n → (Fin n → ℂ) → ℂ}
    (hf : ∀ j, Continuous (f j)) (hg : ∀ j, Continuous (g j)) :
    ∀ s ≤ n, ∀ k, (fun z => G.recF (fun j => fun y => c • f j y + g j y) s k z)
      = fun z => c • G.recF f s k z + G.recF g s k z := by
  intro s
  induction s with
  | zero => intro _ k; rfl
  | succ s ihs =>
      intro hs k
      have ih : ∀ k, (fun z => G.recF (fun j => fun y => c • f j y + g j y) s k z)
          = fun z => c • G.recF f s k z + G.recF g s k z := fun k => ihs (by omega) k
      by_cases hlt : s < n
      · funext z
        rw [G.recF_succ_of_lt (f := fun j => fun y => c • f j y + g j y) hlt,
          G.recF_succ_of_lt (f := f) hlt, G.recF_succ_of_lt (f := g) hlt]
        simp only [Geom.stepData]
        have h1 : Continuous (fun y => G.cutFbar ⟨s, hlt⟩ y * G.recF f s k y) :=
          (G.contDiff_cutFbar ⟨s, hlt⟩).continuous.mul (recF_continuous G hf s (by omega) k)
        have h2 : Continuous (fun y => G.cutFbar ⟨s, hlt⟩ y * G.recF g s k y) :=
          (G.contDiff_cutFbar ⟨s, hlt⟩).continuous.mul (recF_continuous G hg s (by omega) k)
        rw [show (fun y => G.cutFbar ⟨s, hlt⟩ y
              * G.recF (fun j => fun y => c • f j y + g j y) s k y)
            = fun y => c • (G.cutFbar ⟨s, hlt⟩ y * G.recF f s k y)
                + (G.cutFbar ⟨s, hlt⟩ y * G.recF g s k y) from by
          funext y
          rw [show G.recF (fun j => fun y => c • f j y + g j y) s k y
              = c • G.recF f s k y + G.recF g s k y from congrFun (ih k) y]
          simp only [Complex.real_smul]
          ring]
        exact dbarT_affine ⟨s, hlt⟩ (ρ := G.r) c h1 h2 z
      · have hrec : ∀ h : Fin n → (Fin n → ℂ) → ℂ, G.recF h (s + 1) = G.recF h s := by
          intro h; rw [G.recF_succ]; simp [hlt]
        funext z
        rw [hrec, hrec, hrec]
        exact congrFun (ih k) z

/-! ## Linearity of the solution `G.recU` -/

/-- The explicit solution is affine in its datum, for continuous data. -/
private lemma recU_affine (G : Geom n) (c : ℝ) {f g : Fin n → (Fin n → ℂ) → ℂ}
    (hf : ∀ j, Continuous (f j)) (hg : ∀ j, Continuous (g j)) :
    (fun z => G.recU (fun j => fun y => c • f j y + g j y) z)
      = fun z => c • G.recU f z + G.recU g z := by
  funext z
  rw [show G.recU (fun j => fun y => c • f j y + g j y) z = ∑ j : Fin n,
        Work.CR.Flat.Cauchy.dbarTransform G.r j
          (fun y => G.cutF j y * G.recF (fun j => fun y => c • f j y + g j y) (j : ℕ) j y) z
        from rfl,
    show G.recU f z = ∑ j : Fin n, Work.CR.Flat.Cauchy.dbarTransform G.r j
          (fun y => G.cutF j y * G.recF f (j : ℕ) j y) z from rfl,
    show G.recU g z = ∑ j : Fin n, Work.CR.Flat.Cauchy.dbarTransform G.r j
          (fun y => G.cutF j y * G.recF g (j : ℕ) j y) z from rfl,
    Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h1 : Continuous (fun y => G.cutF j y * G.recF f (j : ℕ) j y) :=
    (G.contDiff_cutF j).continuous.mul (recF_continuous G hf (j : ℕ) (le_of_lt j.isLt) j)
  have h2 : Continuous (fun y => G.cutF j y * G.recF g (j : ℕ) j y) :=
    (G.contDiff_cutF j).continuous.mul (recF_continuous G hg (j : ℕ) (le_of_lt j.isLt) j)
  rw [show (fun y => G.cutF j y * G.recF (fun j => fun y => c • f j y + g j y) (j : ℕ) j y)
      = fun y => c • (G.cutF j y * G.recF f (j : ℕ) j y)
          + (G.cutF j y * G.recF g (j : ℕ) j y) from by
    funext y
    rw [show G.recF (fun j => fun y => c • f j y + g j y) (j : ℕ) j y
        = c • G.recF f (j : ℕ) j y + G.recF g (j : ℕ) j y from
      congrFun (recF_affine G c hf hg (j : ℕ) (le_of_lt j.isLt) j) y]
    simp only [Complex.real_smul]
    ring]
  exact dbarT_affine j (ρ := G.r) c h1 h2 z

theorem recULinearCont {n : ℕ} (G : Work.NN.Ratio.Geom n) :
    ∀ (c : ℝ) (f g : Fin n → (Fin n → ℂ) → ℂ),
      (∀ j, Continuous (f j)) → (∀ j, Continuous (g j)) → ∀ z : Fin n → ℂ,
        G.recU (fun j => fun y => c • f j y + g j y) z = c • G.recU f z + G.recU g z := by
  intro c f g hf hg z
  exact congrFun (recU_affine G c hf hg) z

end Work.NN.Ratio
