import Mathlib.Tactic.Have
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BSKinetic.windowedMul_integrable
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BSKinetic.windowedMul_dirichlet_eq`

The windowed Dirichlet (integration-by-parts) identity for the product `χ · F` of a smooth
compactly supported cutoff `χ` and an arbitrary smooth `F`:

    `∫_x Σ_k (∂_k(χ·F))²  =  ∫_x Σ_k (∂_kχ)²·F²  −  ∫_x Σ_k χ²·F·(∂_k²F)`.

The proof is the standard two-factor integration by parts `∫ ∂_k(χ²·F·∂_kF) = 0`
(`Submission.BoseGases.integral_fderiv_eq_zero`, applied to the smooth compactly supported
function `χ²F∂_kF`), together with the Leibniz rule for `∂_k(χ·F)` and the second-order
Leibniz rule for `∂_k(χ²·F·∂_kF)`.
-/

noncomputable section

open MeasureTheory Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BSKinetic

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

/-! ## 1. The two Leibniz rules -/

/-- **The Leibniz rule for the windowed product.**  `∂_k(χ·F) = (∂_kχ)·F + χ·(∂_kF)`. -/
lemma fderiv_mul_apply_basis {χ F : ℝ³ → ℝ} (hχ : ContDiff ℝ (⊤ : ENat) χ)
    (hF : ContDiff ℝ (⊤ : ENat) F) (x : ℝ³) (k : Fin 3) :
    fderiv ℝ (fun y : ℝ³ => χ y * F y) x (Submission.BoseGases.kcStdBasis k)
      = fderiv ℝ χ x (Submission.BoseGases.kcStdBasis k) * F x
        + χ x * fderiv ℝ F x (Submission.BoseGases.kcStdBasis k) := by
  have h1 : DifferentiableAt ℝ χ x := hχ.differentiable (by norm_num) x
  have h2 : DifferentiableAt ℝ F x := hF.differentiable (by norm_num) x
  rw [show (fun y : ℝ³ => χ y * F y) = χ * F from rfl, fderiv_mul h1 h2]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

/-- **The second-order Leibniz rule.**  For `g = χ²·F·∂_kF`,

    `∂_k g = 2·(∂_kχ)·χ·F·(∂_kF) + χ²·(∂_kF)² + χ²·F·(∂_k∂_kF)`. -/
lemma fderiv_window2_apply {χ F : ℝ³ → ℝ} (hχ : ContDiff ℝ (⊤ : ENat) χ)
    (hF : ContDiff ℝ (⊤ : ENat) F) (x : ℝ³) (k : Fin 3) :
    fderiv ℝ (fun y : ℝ³ =>
        χ y ^ 2 * F y * fderiv ℝ F y (Submission.BoseGases.kcStdBasis k)) x
        (Submission.BoseGases.kcStdBasis k)
      = 2 * (fderiv ℝ χ x (Submission.BoseGases.kcStdBasis k)) * χ x * F x
          * (fderiv ℝ F x (Submission.BoseGases.kcStdBasis k))
        + (χ x) ^ 2 * (fderiv ℝ F x (Submission.BoseGases.kcStdBasis k)) ^ 2
        + (χ x) ^ 2 * F x
            * (fderiv ℝ (fun y : ℝ³ =>
                fderiv ℝ F y (Submission.BoseGases.kcStdBasis k)) x
                (Submission.BoseGases.kcStdBasis k)) := by
  set e := Submission.BoseGases.kcStdBasis k with he
  have hχd : DifferentiableAt ℝ χ x := hχ.differentiable (by norm_num) x
  have hFd : DifferentiableAt ℝ F x := hF.differentiable (by norm_num) x
  have hB : ContDiff ℝ (⊤ : ENat) (fun y : ℝ³ => fderiv ℝ F y e) := by
    have hmain : ContDiff ℝ (↑(⊤ : ENat) : WithTop ℕ∞)
        (fun p : ℝ³ × ℝ³ => (fderiv ℝ F p.1) p.2) :=
      ContDiff.contDiff_fderiv_apply (𝕜 := ℝ) hF (by simp)
    have hpair : ContDiff ℝ (↑(⊤ : ENat) : WithTop ℕ∞) (fun y : ℝ³ => (y, e)) :=
      contDiff_id.prodMk contDiff_const
    exact hmain.comp hpair
  have hBd : DifferentiableAt ℝ (fun y : ℝ³ => fderiv ℝ F y e) x :=
    hB.differentiable (by norm_num) x
  have hPd : DifferentiableAt ℝ (χ ^ 2 * F) x := (hχd.pow 2).mul hFd
  have hχ2 : fderiv ℝ (fun y : ℝ³ => χ y ^ 2) x = (2 * χ x) • fderiv ℝ χ x := by
    have h := fderiv_fun_pow (𝕜 := ℝ) (f := χ) 2 hχd
    simpa using h
  have hP : fderiv ℝ (χ ^ 2 * F) x = F x • fderiv ℝ (χ ^ 2) x + (χ x) ^ 2 • fderiv ℝ F x := by
    rw [fderiv_mul (hχd.pow 2) hFd]
    simp only [Pi.pow_apply]
    rw [add_comm]
  change fderiv ℝ ((χ ^ 2 * F) * (fun y : ℝ³ => fderiv ℝ F y e)) x e = _
  rw [fderiv_mul hPd hBd, hP, show (χ ^ 2 : ℝ³ → ℝ) = (fun y : ℝ³ => χ y ^ 2) from rfl, hχ2]
  simp only [Pi.mul_apply, add_apply, smul_apply, smul_eq_mul]
  ring

/-! ## 2. The integration by parts `∫ ∂_k(χ²·F·∂_kF) = 0` -/

/-- **Integration by parts.**  Since `χ²·F·∂_kF` is smooth and compactly supported, the integral
of its `k`-th partial derivative vanishes. -/
lemma integral_fderiv_window2_eq_zero {χ F : ℝ³ → ℝ} (hχ : ContDiff ℝ (⊤ : ENat) χ)
    (hcs : HasCompactSupport χ) (hF : ContDiff ℝ (⊤ : ENat) F) (k : Fin 3) :
    (∫ x : ℝ³,
        fderiv ℝ (fun y : ℝ³ =>
          χ y ^ 2 * F y * fderiv ℝ F y (Submission.BoseGases.kcStdBasis k)) x
          (Submission.BoseGases.kcStdBasis k)) = 0 := by
  set e := Submission.BoseGases.kcStdBasis k with he
  have hB : ContDiff ℝ (⊤ : ENat) (fun y : ℝ³ => fderiv ℝ F y e) := by
    have hmain : ContDiff ℝ (↑(⊤ : ENat) : WithTop ℕ∞)
        (fun p : ℝ³ × ℝ³ => (fderiv ℝ F p.1) p.2) :=
      ContDiff.contDiff_fderiv_apply (𝕜 := ℝ) hF (by simp)
    have hpair : ContDiff ℝ (↑(⊤ : ENat) : WithTop ℕ∞) (fun y : ℝ³ => (y, e)) :=
      contDiff_id.prodMk contDiff_const
    exact hmain.comp hpair
  have hg : ContDiff ℝ (⊤ : ENat)
      (fun y : ℝ³ => χ y ^ 2 * F y * fderiv ℝ F y e) := ((hχ.pow 2).mul hF).mul hB
  have hcs2 : HasCompactSupport (fun y : ℝ³ => χ y ^ 2) :=
    hcs.comp_left (g := fun t : ℝ => t ^ 2) (by simp)
  have hcg : HasCompactSupport (fun y : ℝ³ => χ y ^ 2 * F y * fderiv ℝ F y e) :=
    (hcs2.mul_right (f' := F)).mul_right
  exact Submission.BoseGases.integral_fderiv_eq_zero hg hcg e

/-! ## 3. The identity in a single basis direction -/

/-- **The identity in one direction `k`.**  The square of `∂_k(χ·F)` integrates to the sum of the
`(∂_kχ)²F²` term and minus the `χ²F∂_k²F` term. -/
lemma windowedMul_perK {χ F : ℝ³ → ℝ} (hχ : ContDiff ℝ (⊤ : ENat) χ)
    (hcs : HasCompactSupport χ) (hF : ContDiff ℝ (⊤ : ENat) F) (k : Fin 3) :
    (∫ x : ℝ³, (fderiv ℝ (fun y : ℝ³ => χ y * F y) x (Submission.BoseGases.kcStdBasis k)) ^ 2)
      = (∫ x : ℝ³,
          (fderiv ℝ χ x (Submission.BoseGases.kcStdBasis k)) ^ 2 * (F x) ^ 2)
        - (∫ x : ℝ³, (χ x) ^ 2 * F x *
            (fderiv ℝ (fun y : ℝ³ =>
                fderiv ℝ F y (Submission.BoseGases.kcStdBasis k)) x
              (Submission.BoseGases.kcStdBasis k))) := by
  have hB := integral_fderiv_window2_eq_zero hχ hcs hF k
  obtain ⟨hI1, hI2, hI3, hI4, _⟩ := windowedMul_integrable hχ hcs hF k
  let P1 : ℝ³ → ℝ :=
    fun x => (fderiv ℝ χ x (Submission.BoseGases.kcStdBasis k)) ^ 2 * (F x) ^ 2
  let P2 : ℝ³ → ℝ :=
    fun x => 2 * (fderiv ℝ χ x (Submission.BoseGases.kcStdBasis k)) * χ x * F x
      * (fderiv ℝ F x (Submission.BoseGases.kcStdBasis k))
  let P3 : ℝ³ → ℝ :=
    fun x => (χ x) ^ 2 * (fderiv ℝ F x (Submission.BoseGases.kcStdBasis k)) ^ 2
  let P4 : ℝ³ → ℝ :=
    fun x => (χ x) ^ 2 * F x *
      (fderiv ℝ (fun y : ℝ³ => fderiv ℝ F y (Submission.BoseGases.kcStdBasis k)) x
        (Submission.BoseGases.kcStdBasis k))
  have hI1' : Integrable P1 := hI1
  have hI2' : Integrable P2 := hI2
  have hI3' : Integrable P3 := hI3
  have hI4' : Integrable P4 := hI4
  have hL : ∀ x, (fderiv ℝ (fun y : ℝ³ => χ y * F y) x
        (Submission.BoseGases.kcStdBasis k)) ^ 2 = P1 x + P2 x + P3 x := by
    intro x
    rw [fderiv_mul_apply_basis hχ hF x k]
    simp only [P1, P2, P3]
    ring
  have h0 : ∀ x, fderiv ℝ (fun y : ℝ³ =>
          χ y ^ 2 * F y * fderiv ℝ F y (Submission.BoseGases.kcStdBasis k)) x
          (Submission.BoseGases.kcStdBasis k) = P2 x + P3 x + P4 x := by
    intro x
    simpa only [P2, P3, P4] using fderiv_window2_apply hχ hF x k
  have hInt1 : (∫ x, P1 x + P2 x + P3 x) = (∫ x, P1 x) + (∫ x, P2 x) + (∫ x, P3 x) := by
    rw [integral_add (f := fun x => P1 x + P2 x) (g := P3) (hI1'.add hI2') hI3',
        integral_add (f := P1) (g := P2) hI1' hI2']
  have hInt0 : (∫ x, P2 x + P3 x + P4 x) = (∫ x, P2 x) + (∫ x, P3 x) + (∫ x, P4 x) := by
    rw [integral_add (f := fun x => P2 x + P3 x) (g := P4) (hI2'.add hI3') hI4',
        integral_add (f := P2) (g := P3) hI2' hI3']
  have hzero : (∫ x, P2 x + P3 x + P4 x) = 0 := by
    rw [show (∫ x, P2 x + P3 x + P4 x)
          = (∫ x, fderiv ℝ (fun y : ℝ³ =>
              χ y ^ 2 * F y * fderiv ℝ F y (Submission.BoseGases.kcStdBasis k)) x
              (Submission.BoseGases.kcStdBasis k))
        from integral_congr_ae (Eventually.of_forall (fun x => (h0 x).symm)), hB]
  have hsplit2 : (∫ x, P2 x) + (∫ x, P3 x) = -(∫ x, P4 x) := by
    have hh := hInt0
    rw [hzero] at hh
    linarith
  calc (∫ x, (fderiv ℝ (fun y : ℝ³ => χ y * F y) x
        (Submission.BoseGases.kcStdBasis k)) ^ 2)
      = ∫ x, P1 x + P2 x + P3 x := integral_congr_ae (Eventually.of_forall hL)
    _ = (∫ x, P1 x) + (∫ x, P2 x) + (∫ x, P3 x) := hInt1
    _ = (∫ x, P1 x) - (∫ x, P4 x) := by linarith [hsplit2]
    _ = (∫ x, (fderiv ℝ χ x (Submission.BoseGases.kcStdBasis k)) ^ 2 * (F x) ^ 2)
        - (∫ x, (χ x) ^ 2 * F x *
            (fderiv ℝ (fun y : ℝ³ =>
                fderiv ℝ F y (Submission.BoseGases.kcStdBasis k)) x
              (Submission.BoseGases.kcStdBasis k))) := by
        simp only [P1, P4]

/-! ## 4. The target identity -/

theorem windowedMul_dirichlet_eq {χ F : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hχ : ContDiff ℝ (⊤ : ENat) χ) (hcs : HasCompactSupport χ)
    (hF : ContDiff ℝ (⊤ : ENat) F) :
    (∫ x : EuclideanSpace ℝ (Fin 3), ∑ k : Fin 3,
        (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 3) => χ y * F y) x
          (Submission.BoseGases.kcStdBasis k)) ^ 2)
      = (∫ x : EuclideanSpace ℝ (Fin 3), ∑ k : Fin 3,
          (fderiv ℝ χ x (Submission.BoseGases.kcStdBasis k)) ^ 2 * (F x) ^ 2)
        - (∫ x : EuclideanSpace ℝ (Fin 3), ∑ k : Fin 3, (χ x) ^ 2 * F x *
            (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 3) =>
                fderiv ℝ F y (Submission.BoseGases.kcStdBasis k)) x
              (Submission.BoseGases.kcStdBasis k))) := by
  let Q : Fin 3 → ℝ³ → ℝ := fun k x =>
    (fderiv ℝ (fun y : ℝ³ => χ y * F y) x (Submission.BoseGases.kcStdBasis k)) ^ 2
  let P1 : Fin 3 → ℝ³ → ℝ := fun k x =>
    (fderiv ℝ χ x (Submission.BoseGases.kcStdBasis k)) ^ 2 * (F x) ^ 2
  let P4 : Fin 3 → ℝ³ → ℝ := fun k x => (χ x) ^ 2 * F x *
    (fderiv ℝ (fun y : ℝ³ => fderiv ℝ F y (Submission.BoseGases.kcStdBasis k)) x
      (Submission.BoseGases.kcStdBasis k))
  have hQ : ∀ k : Fin 3, Integrable (Q k) := fun k => (windowedMul_integrable hχ hcs hF k).2.2.2.2
  have hI1 : ∀ k : Fin 3, Integrable (P1 k) := fun k => (windowedMul_integrable hχ hcs hF k).1
  have hI4 : ∀ k : Fin 3, Integrable (P4 k) := fun k => (windowedMul_integrable hχ hcs hF k).2.2.2.1
  have hper : ∀ k : Fin 3, (∫ x, Q k x) = (∫ x, P1 k x) - (∫ x, P4 k x) :=
    fun k => windowedMul_perK hχ hcs hF k
  have h1 : (∫ x, ∑ k : Fin 3, Q k x) = ∑ k : Fin 3, ∫ x, Q k x := by
    simpa using integral_finsetSum (Finset.univ) (f := fun k x => Q k x) (fun k _ => hQ k)
  have h2 : (∫ x, ∑ k : Fin 3, P1 k x) = ∑ k : Fin 3, ∫ x, P1 k x := by
    simpa using integral_finsetSum (Finset.univ) (f := fun k x => P1 k x) (fun k _ => hI1 k)
  have h3 : (∫ x, ∑ k : Fin 3, P4 k x) = ∑ k : Fin 3, ∫ x, P4 k x := by
    simpa using integral_finsetSum (Finset.univ) (f := fun k x => P4 k x) (fun k _ => hI4 k)
  have hper' : ∀ k : Fin 3, (∫ x, Q k x) = (∫ x, P1 k x) - (∫ x, P4 k x) := hper
  calc (∫ x : ℝ³, ∑ k : Fin 3, (fderiv ℝ (fun y : ℝ³ => χ y * F y) x
          (Submission.BoseGases.kcStdBasis k)) ^ 2)
      = ∫ x, ∑ k : Fin 3, Q k x := by simp only [Q]
    _ = ∑ k : Fin 3, ∫ x, Q k x := h1
    _ = ∑ k : Fin 3, ((∫ x, P1 k x) - (∫ x, P4 k x)) :=
        Finset.sum_congr rfl (fun k _ => hper' k)
    _ = (∑ k : Fin 3, ∫ x, P1 k x) - (∑ k : Fin 3, ∫ x, P4 k x) :=
        Finset.sum_sub_distrib (f := fun k => ∫ x, P1 k x) (g := fun k => ∫ x, P4 k x)
    _ = (∫ x, ∑ k : Fin 3, P1 k x) - (∫ x, ∑ k : Fin 3, P4 k x) := by rw [← h2, ← h3]
    _ = (∫ x : ℝ³, ∑ k : Fin 3,
          (fderiv ℝ χ x (Submission.BoseGases.kcStdBasis k)) ^ 2 * (F x) ^ 2)
        - (∫ x : ℝ³, ∑ k : Fin 3, (χ x) ^ 2 * F x *
            (fderiv ℝ (fun y : ℝ³ =>
                fderiv ℝ F y (Submission.BoseGases.kcStdBasis k)) x
              (Submission.BoseGases.kcStdBasis k))) := by
        simp only [P1, P4]

end Work.BSKinetic
