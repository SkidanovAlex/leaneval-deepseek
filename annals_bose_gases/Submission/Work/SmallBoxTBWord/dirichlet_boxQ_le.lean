import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SmallBoxTBWord.fderiv_boxQ_kcDir
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Dirichlet-form bound on the windowed `Q_B`-projected derivative

For the box mean-free projection `boxQ volA A i` (the mean over the compact set
`A` in slot `i`), a smooth window `χ`, and a smooth `Ψ : X (n+1) → ℝ`, this file
proves

    Σ_i ∫_{abox (n+1) a} Σ_k (∂_{ik}(χ(x_i)·(Q_{B,i}Ψ)))²
      ≤ 2·Cχ²·kinWord (n+1) a Ψ + 2·winErrBox a A volA χ Ψ .

The argument is the position-space half of the kinetic bridge, at the general
per-box geometry `(A, volA, χ)`: the Leibniz rule in the `i`-th slot turns
`∂_{ik}(χ(x_i)·u)` into `χ(x_i)·(∂_{ik}u) + u·(∂_kχ)(x_i)`; the box projection is
free for the `i`-th derivative (`fderiv_boxQ_kcDir`), and the window factor is
bounded by `Cχ` (`hsup`).
-/

noncomputable section

open MeasureTheory Metric
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.SmallBoxTBWord

open Submission.BoseGases
open _root_.BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option linter.unusedVariables false

/-! ## Elementary calculus helpers -/

/-- **Leibniz + `(a+b)² ≤ 2a²+2b²` in an arbitrary direction.** -/
lemma mul_dir_sq_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {χ u : E → ℝ} {x v : E} (hχ : DifferentiableAt ℝ χ x) (hu : DifferentiableAt ℝ u x) :
    (fderiv ℝ (fun y : E => χ y * u y) x v) ^ 2
      ≤ 2 * (χ x) ^ 2 * (fderiv ℝ u x v) ^ 2
        + 2 * (fderiv ℝ χ x v) ^ 2 * (u x) ^ 2 := by
  have hd : fderiv ℝ (fun y : E => χ y * u y) x v
      = χ x * fderiv ℝ u x v + u x * fderiv ℝ χ x v := by
    have h1 : fderiv ℝ (fun y : E => χ y * u y) x = fderiv ℝ (χ * u) x := rfl
    rw [h1, fderiv_mul hχ hu, add_apply, smul_apply, smul_apply, smul_eq_mul, smul_eq_mul]
  rw [hd]
  nlinarith [sq_nonneg (χ x * fderiv ℝ u x v - u x * fderiv ℝ χ x v)]

/-! ## Smoothness of `boxQ` and the coordinate derivative of the window -/

/-- The box mean `boxP volA A i Φ` is smooth (`Φ` smooth and `A` compact). -/
lemma boxP_contDiff_boxQ {N : ℕ} {A : Set ℝ³} (hA : IsCompact A) (volA : ℝ) (i : Fin N)
    {Φ : X N → ℝ} (hΦ : ContDiff ℝ (⊤ : ENat) Φ) :
    ContDiff ℝ (⊤ : ENat) (boxP volA A i Φ) := by
  have hU : ContDiff ℝ (⊤ : ENat) (fun q : X N × ℝ³ => Function.update q.1 i q.2) :=
    contDiff_update_pair i
  have hF : ContDiff ℝ (⊤ : ENat)
      (Function.uncurry (fun (p : X N) (z : ℝ³) => Φ (Function.update p i z))) :=
    hΦ.comp hU
  have hmain : ContDiff ℝ (⊤ : ENat)
      (fun p : X N => ∫ z in A, Φ (Function.update p i z)) :=
    Commons.Analysis.Calculus.contDiff_setIntegral_isCompact (k := A) hA hF
  have hmain2 : ContDiff ℝ (⊤ : ENat)
      (fun p : X N => (1 / volA) * ∫ z in A, Φ (Function.update p i z)) :=
    (contDiff_const (c := (1 / volA))).mul hmain
  unfold boxP
  exact hmain2

/-- The box mean-free projection `boxQ volA A i Φ = Φ − boxP volA A i Φ` is smooth. -/
lemma boxQ_contDiff {N : ℕ} {A : Set ℝ³} (hA : IsCompact A) (volA : ℝ) (i : Fin N)
    {Φ : X N → ℝ} (hΦ : ContDiff ℝ (⊤ : ENat) Φ) :
    ContDiff ℝ (⊤ : ENat) (boxQ volA A i Φ) := by
  unfold boxQ
  exact hΦ.sub (boxP_contDiff_boxQ hA volA i hΦ)

/-- `y ↦ χ (y i)` is smooth. -/
lemma contDiff_chi_apply {N : ℕ} {χ : ℝ³ → ℝ} (hχ : ContDiff ℝ (⊤ : ENat) χ) (i : Fin N) :
    ContDiff ℝ (⊤ : ENat) (fun y : X N => χ (y i)) :=
  hχ.comp (by fun_prop)

/-- **The `i`-th coordinate derivative of the window `χ (z i)`** in the direction
`kcDir N i k` is the `k`-th coordinate derivative of `χ` at `x i`. -/
lemma fderiv_chi_apply_kcDir {N : ℕ} {χ : ℝ³ → ℝ} (hχ : ContDiff ℝ (⊤ : ENat) χ) (i : Fin N)
    (x : X N) (k : Fin 3) :
    fderiv ℝ (fun z : X N => χ (z i)) x (kcDir N i k)
      = fderiv ℝ χ (x i) (kcStdBasis k) := by
  have hχd : DifferentiableAt ℝ χ (x i) := hχ.differentiable (by simp) (x i)
  have hf : DifferentiableAt ℝ (fun z : X N => z i) x :=
    (ContinuousLinearMap.proj (φ := fun _ : Fin N => ℝ³) i).differentiableAt
  have hcomp := fderiv_comp (x := x) (g := χ) (f := fun z : X N => z i) hχd hf
  have hfun : (fun z : X N => χ (z i)) = χ ∘ (fun z : X N => z i) := rfl
  rw [hfun, hcomp, ContinuousLinearMap.comp_apply]
  have hproj : fderiv ℝ (fun z : X N => z i) x
      = ContinuousLinearMap.proj (φ := fun _ : Fin N => ℝ³) i :=
    ContinuousLinearMap.fderiv (ContinuousLinearMap.proj (φ := fun _ : Fin N => ℝ³) i)
  rw [hproj]
  simp [ContinuousLinearMap.proj, kcDir]

/-! ## Pointwise bounds -/

/-- **Pointwise bound for one pair `(i,k)`.** -/
lemma boxQ_term_le {Cχ : ℝ} {A : Set ℝ³} {volA : ℝ} {χ : ℝ³ → ℝ} {n : ℕ}
    (hχ : ContDiff ℝ (⊤ : ENat) χ) (hA : IsCompact A) (hsup : ∀ x, |χ x| ≤ Cχ)
    {Ψ : X (n + 1) → ℝ} (hΨ : ContDiff ℝ (⊤ : ENat) Ψ)
    (i : Fin (n + 1)) (x : X (n + 1)) (k : Fin 3) :
    (fderiv ℝ (fun y : X (n + 1) => χ (y i) * boxQ volA A i Ψ y) x
        (kcDir (n + 1) i k)) ^ 2
      ≤ 2 * Cχ ^ 2 * (fderiv ℝ Ψ x (kcDir (n + 1) i k)) ^ 2
        + 2 * ((fderiv ℝ χ (x i) (kcStdBasis k)) ^ 2 * (boxQ volA A i Ψ x) ^ 2) := by
  have hχ' : DifferentiableAt ℝ (fun z : X (n + 1) => χ (z i)) x :=
    (contDiff_chi_apply hχ i).differentiable (by simp) x
  have hu : DifferentiableAt ℝ (boxQ volA A i Ψ) x :=
    (boxQ_contDiff hA volA i hΨ).differentiable (by simp) x
  have h1 := mul_dir_sq_le (χ := fun z : X (n + 1) => χ (z i)) (u := boxQ volA A i Ψ)
      (x := x) (v := kcDir (n + 1) i k) hχ' hu
  have h2 : fderiv ℝ (boxQ volA A i Ψ) x (kcDir (n + 1) i k)
      = fderiv ℝ Ψ x (kcDir (n + 1) i k) := fderiv_boxQ_kcDir hA volA i hΨ x k
  have h3 : fderiv ℝ (fun z : X (n + 1) => χ (z i)) x (kcDir (n + 1) i k)
      = fderiv ℝ χ (x i) (kcStdBasis k) := fderiv_chi_apply_kcDir hχ i x k
  have h4 : (χ (x i)) ^ 2 ≤ Cχ ^ 2 := by
    rw [← sq_abs (χ (x i))]
    exact pow_le_pow_left₀ (abs_nonneg _) (hsup (x i)) 2
  rw [h2, h3] at h1
  nlinarith [h1, h4, sq_nonneg Cχ,
    sq_nonneg (fderiv ℝ Ψ x (kcDir (n + 1) i k)), sq_nonneg (boxQ volA A i Ψ x)]

/-- **Pointwise bound summed over the three coordinate directions.** -/
lemma boxQ_sum_le {Cχ : ℝ} {A : Set ℝ³} {volA : ℝ} {χ : ℝ³ → ℝ} {n : ℕ}
    (hχ : ContDiff ℝ (⊤ : ENat) χ) (hA : IsCompact A) (hsup : ∀ x, |χ x| ≤ Cχ)
    {Ψ : X (n + 1) → ℝ} (hΨ : ContDiff ℝ (⊤ : ENat) Ψ)
    (i : Fin (n + 1)) (x : X (n + 1)) :
    (∑ k : Fin 3, (fderiv ℝ (fun y : X (n + 1) => χ (y i) * boxQ volA A i Ψ y) x
        (kcDir (n + 1) i k)) ^ 2)
      ≤ 2 * Cχ ^ 2 * (∑ k : Fin 3, (fderiv ℝ Ψ x (kcDir (n + 1) i k)) ^ 2)
        + 2 * ((∑ k : Fin 3, (fderiv ℝ χ (x i) (kcStdBasis k)) ^ 2)
            * (boxQ volA A i Ψ x) ^ 2) := by
  calc
    (∑ k : Fin 3, (fderiv ℝ (fun y : X (n + 1) => χ (y i) * boxQ volA A i Ψ y) x
        (kcDir (n + 1) i k)) ^ 2)
        ≤ ∑ k : Fin 3,
            (2 * Cχ ^ 2 * (fderiv ℝ Ψ x (kcDir (n + 1) i k)) ^ 2
              + 2 * ((fderiv ℝ χ (x i) (kcStdBasis k)) ^ 2
                  * (boxQ volA A i Ψ x) ^ 2)) :=
          Finset.sum_le_sum (fun k _ => boxQ_term_le hχ hA hsup hΨ i x k)
    _ = 2 * Cχ ^ 2 * (∑ k : Fin 3, (fderiv ℝ Ψ x (kcDir (n + 1) i k)) ^ 2)
          + 2 * ((∑ k : Fin 3, (fderiv ℝ χ (x i) (kcStdBasis k)) ^ 2)
              * (boxQ volA A i Ψ x) ^ 2) := by
          rw [Finset.sum_add_distrib]
          congr 1
          · rw [Finset.mul_sum]
          · rw [Finset.sum_mul, Finset.mul_sum]

/-! ## Integrability of the three integrands -/

/-- Continuity of the windowed derivative integrand. -/
lemma boxQ_continuous_left {A : Set ℝ³} {volA : ℝ} {χ : ℝ³ → ℝ} {n : ℕ}
    (hχ : ContDiff ℝ (⊤ : ENat) χ) (hA : IsCompact A)
    {Ψ : X (n + 1) → ℝ} (hΨ : ContDiff ℝ (⊤ : ENat) Ψ) (i : Fin (n + 1)) :
    Continuous (fun x : X (n + 1) => ∑ k : Fin 3,
      (fderiv ℝ (fun y : X (n + 1) => χ (y i) * boxQ volA A i Ψ y) x
        (kcDir (n + 1) i k)) ^ 2) := by
  have hf : ContDiff ℝ (⊤ : ENat)
      (fun y : X (n + 1) => χ (y i) * boxQ volA A i Ψ y) :=
    (contDiff_chi_apply hχ i).mul (boxQ_contDiff hA volA i hΨ)
  refine continuous_finsetSum _ (fun k _ => ?_)
  exact ((firstDir_contDiff hf (kcDir (n + 1) i k)).continuous).pow 2

/-- Continuity of the `kinWord` integrand. -/
lemma boxQ_continuous_kin {n : ℕ}
    {Ψ : X (n + 1) → ℝ} (hΨ : ContDiff ℝ (⊤ : ENat) Ψ) (i : Fin (n + 1)) :
    Continuous (fun x : X (n + 1) =>
      ∑ k : Fin 3, (fderiv ℝ Ψ x (kcDir (n + 1) i k)) ^ 2) := by
  refine continuous_finsetSum _ (fun k _ => ?_)
  exact ((firstDir_contDiff hΨ (kcDir (n + 1) i k)).continuous).pow 2

/-- Continuity of the window-error integrand. -/
lemma boxQ_continuous_win {A : Set ℝ³} {volA : ℝ} {χ : ℝ³ → ℝ} {n : ℕ}
    (hχ : ContDiff ℝ (⊤ : ENat) χ) (hA : IsCompact A)
    {Ψ : X (n + 1) → ℝ} (hΨ : ContDiff ℝ (⊤ : ENat) Ψ) (i : Fin (n + 1)) :
    Continuous (fun x : X (n + 1) =>
      (∑ k : Fin 3, (fderiv ℝ χ (x i) (kcStdBasis k)) ^ 2)
        * (boxQ volA A i Ψ x) ^ 2) := by
  have hgrad : Continuous (fun x : X (n + 1) =>
      ∑ k : Fin 3, (fderiv ℝ χ (x i) (kcStdBasis k)) ^ 2) := by
    have hχc : Continuous (fun x : X (n + 1) => fderiv ℝ χ (x i)) :=
      (hχ.continuous_fderiv (by decide)).comp (continuous_apply i)
    refine continuous_finsetSum _ (fun k _ => ?_)
    exact ((hχc.clm_apply continuous_const)).pow 2
  exact hgrad.mul (((boxQ_contDiff hA volA i hΨ).continuous).pow 2)

/-! ## The integral step -/

/-- **The integral bound for a single slot**, obtained from the pointwise bound by
monotonicity and additivity of the integral. -/
lemma boxQ_int_step {a Cχ : ℝ} {A : Set ℝ³} {volA : ℝ} {χ : ℝ³ → ℝ} {n : ℕ}
    (ha : 0 < a) (hχ : ContDiff ℝ (⊤ : ENat) χ) (hA : IsCompact A)
    (hsup : ∀ x, |χ x| ≤ Cχ)
    {Ψ : X (n + 1) → ℝ} (hΨ : ContDiff ℝ (⊤ : ENat) Ψ) (i : Fin (n + 1)) :
    (∫ x in abox (n + 1) a, ∑ k : Fin 3,
        (fderiv ℝ (fun y : X (n + 1) => χ (y i) * boxQ volA A i Ψ y) x
          (kcDir (n + 1) i k)) ^ 2)
      ≤ 2 * Cχ ^ 2
          * (∫ x in abox (n + 1) a,
              ∑ k : Fin 3, (fderiv ℝ Ψ x (kcDir (n + 1) i k)) ^ 2)
        + 2 * (∫ x in abox (n + 1) a,
              (∑ k : Fin 3, (fderiv ℝ χ (x i) (kcStdBasis k)) ^ 2)
                * (boxQ volA A i Ψ x) ^ 2) := by
  have h1 : IntegrableOn (fun x : X (n + 1) => ∑ k : Fin 3,
      (fderiv ℝ (fun y : X (n + 1) => χ (y i) * boxQ volA A i Ψ y) x
        (kcDir (n + 1) i k)) ^ 2) (abox (n + 1) a) volume :=
    integrableOn_abox_of_continuous ha (boxQ_continuous_left hχ hA hΨ i)
  have h2 : IntegrableOn (fun x : X (n + 1) =>
      ∑ k : Fin 3, (fderiv ℝ Ψ x (kcDir (n + 1) i k)) ^ 2) (abox (n + 1) a) volume :=
    integrableOn_abox_of_continuous ha (boxQ_continuous_kin hΨ i)
  have h3 : IntegrableOn (fun x : X (n + 1) =>
      (∑ k : Fin 3, (fderiv ℝ χ (x i) (kcStdBasis k)) ^ 2)
        * (boxQ volA A i Ψ x) ^ 2) (abox (n + 1) a) volume :=
    integrableOn_abox_of_continuous ha (boxQ_continuous_win hχ hA hΨ i)
  have hg : IntegrableOn (fun x : X (n + 1) =>
      2 * Cχ ^ 2 * (∑ k : Fin 3, (fderiv ℝ Ψ x (kcDir (n + 1) i k)) ^ 2)
        + 2 * ((∑ k : Fin 3, (fderiv ℝ χ (x i) (kcStdBasis k)) ^ 2)
            * (boxQ volA A i Ψ x) ^ 2)) (abox (n + 1) a) volume := by
    refine integrableOn_abox_of_continuous ha (Continuous.add ?_ ?_)
    · exact continuous_const.mul (boxQ_continuous_kin hΨ i)
    · exact continuous_const.mul (boxQ_continuous_win hχ hA hΨ i)
  have hmono : (∫ x in abox (n + 1) a, ∑ k : Fin 3,
        (fderiv ℝ (fun y : X (n + 1) => χ (y i) * boxQ volA A i Ψ y) x
          (kcDir (n + 1) i k)) ^ 2)
      ≤ ∫ x in abox (n + 1) a,
          (2 * Cχ ^ 2 * (∑ k : Fin 3, (fderiv ℝ Ψ x (kcDir (n + 1) i k)) ^ 2)
            + 2 * ((∑ k : Fin 3, (fderiv ℝ χ (x i) (kcStdBasis k)) ^ 2)
                * (boxQ volA A i Ψ x) ^ 2)) :=
    integral_mono h1 hg (fun x => boxQ_sum_le hχ hA hsup hΨ i x)
  have hsplit : (∫ x in abox (n + 1) a,
        (2 * Cχ ^ 2 * (∑ k : Fin 3, (fderiv ℝ Ψ x (kcDir (n + 1) i k)) ^ 2)
          + 2 * ((∑ k : Fin 3, (fderiv ℝ χ (x i) (kcStdBasis k)) ^ 2)
              * (boxQ volA A i Ψ x) ^ 2)))
      = 2 * Cχ ^ 2
          * (∫ x in abox (n + 1) a,
              ∑ k : Fin 3, (fderiv ℝ Ψ x (kcDir (n + 1) i k)) ^ 2)
        + 2 * (∫ x in abox (n + 1) a,
              (∑ k : Fin 3, (fderiv ℝ χ (x i) (kcStdBasis k)) ^ 2)
                * (boxQ volA A i Ψ x) ^ 2) := by
    rw [integral_add
      (f := fun x : X (n + 1) =>
        2 * Cχ ^ 2 * (∑ k : Fin 3, (fderiv ℝ Ψ x (kcDir (n + 1) i k)) ^ 2))
      (g := fun x : X (n + 1) =>
        2 * ((∑ k : Fin 3, (fderiv ℝ χ (x i) (kcStdBasis k)) ^ 2)
            * (boxQ volA A i Ψ x) ^ 2))
      (h2.const_mul _) (h3.const_mul _)]
    rw [integral_const_mul, integral_const_mul]
  exact hmono.trans_eq hsplit

/-! ## The theorem -/

theorem dirichlet_boxQ_le {a Cχ : ℝ} {A : Set (EuclideanSpace ℝ (Fin 3))} {volA : ℝ} {χ : EuclideanSpace ℝ (Fin 3) → ℝ} {n : ℕ} (ha : 0 < a) (hCχ : 0 ≤ Cχ) (hχ : ContDiff ℝ (⊤ : ENat) χ) (hA : IsCompact A) (hsup : ∀ x, |χ x| ≤ Cχ) {Ψ : Submission.BoseGases.X (n + 1) → ℝ} (hΨ : ContDiff ℝ (⊤ : ENat) Ψ) : (∑ i : Fin (n + 1), ∫ x in Submission.BoseGases.abox (n + 1) a, ∑ k : Fin 3, (fderiv ℝ (fun y : Submission.BoseGases.X (n + 1) => χ (y i) * Work.SmallBoxTBWord.boxQ volA A i Ψ y) x (Submission.BoseGases.kcDir (n + 1) i k)) ^ 2) ≤ 2 * Cχ ^ 2 * Submission.BoseGases.kinWord (n + 1) a Ψ + 2 * Work.SmallBoxTBWord.winErrBox a A volA χ Ψ := by
  have hKW : (∑ i : Fin (n + 1), ∫ x in abox (n + 1) a,
        ∑ k : Fin 3, (fderiv ℝ Ψ x (kcDir (n + 1) i k)) ^ 2) = kinWord (n + 1) a Ψ := by
    rw [kinSum_sum_integral ha Ψ hΨ]
    rfl
  have hWQ : (∑ i : Fin (n + 1), ∫ x in abox (n + 1) a,
        (∑ k : Fin 3, (fderiv ℝ χ (x i) (kcStdBasis k)) ^ 2)
          * (boxQ volA A i Ψ x) ^ 2) = winErrBox a A volA χ Ψ := rfl
  calc
    (∑ i : Fin (n + 1), ∫ x in abox (n + 1) a, ∑ k : Fin 3,
        (fderiv ℝ (fun y : X (n + 1) => χ (y i) * boxQ volA A i Ψ y) x
          (kcDir (n + 1) i k)) ^ 2)
        ≤ ∑ i : Fin (n + 1),
            (2 * Cχ ^ 2
                * (∫ x in abox (n + 1) a,
                    ∑ k : Fin 3, (fderiv ℝ Ψ x (kcDir (n + 1) i k)) ^ 2)
              + 2 * (∫ x in abox (n + 1) a,
                    (∑ k : Fin 3, (fderiv ℝ χ (x i) (kcStdBasis k)) ^ 2)
                      * (boxQ volA A i Ψ x) ^ 2)) :=
          Finset.sum_le_sum (fun i _ => boxQ_int_step ha hχ hA hsup hΨ i)
    _ = 2 * Cχ ^ 2
          * (∑ i : Fin (n + 1), ∫ x in abox (n + 1) a,
              ∑ k : Fin 3, (fderiv ℝ Ψ x (kcDir (n + 1) i k)) ^ 2)
        + 2 * (∑ i : Fin (n + 1), ∫ x in abox (n + 1) a,
              (∑ k : Fin 3, (fderiv ℝ χ (x i) (kcStdBasis k)) ^ 2)
                * (boxQ volA A i Ψ x) ^ 2) := by
          rw [Finset.sum_add_distrib]
          congr 1
          · rw [Finset.mul_sum]
          · rw [Finset.mul_sum]
    _ = 2 * Cχ ^ 2 * kinWord (n + 1) a Ψ + 2 * winErrBox a A volA χ Ψ := by rw [hKW, hWQ]

end Work.SmallBoxTBWord
