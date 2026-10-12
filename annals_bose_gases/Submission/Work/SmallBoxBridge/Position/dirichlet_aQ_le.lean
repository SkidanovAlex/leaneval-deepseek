import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SmallBoxBridge.Defs
import Submission.Work.SmallBoxKinBridge
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Dirichlet-form bound on the windowed `Q`-projected derivative

For a smooth `Ψ` this file proves the pointwise-derivative bound

    Σ_i ∫_{abox (n+1) s} Σ_k (∂_{ik}(χ_s(x_i)·(Q_iΨ)))²
      ≤ 2·chiSup²·kinWord (n+1) s Ψ + 2·winErrorQ s Ψ ,

the position-space half of the kinetic bridge (`Definitions.lean`'s `winErrorQ`):
the Leibniz rule in the `i`-th slot turns `∂_{ik}(χ(x_i)·u)` into
`χ(x_i)·(∂_{ik}u) + u·(∂_kχ)(x_i)`; the `Q_i`-projection is free for the `i`-th
derivative (`fderiv_aQ_kcDir`), and the window factor is bounded by `chiSup`.
-/

noncomputable section

open MeasureTheory Metric
open scoped ContDiff Topology Real BigOperators

namespace Work.SmallBoxBridge.Position

open Submission.BoseGases
open _root_.BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## Elementary calculus helpers -/

/-- **Leibniz + `(a+b)² ≤ 2a²+2b²` in an arbitrary direction.** -/
lemma dirichlet_mul_dir_sq_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
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

/-- **The `i`-th coordinate derivative of the window `χ_s(z i)`** in the direction
`kcDir N i k` is the `k`-th coordinate derivative of `χ_s` at `x i`. -/
lemma dirichlet_fderiv_chiScale_coord {N : ℕ} {s : ℝ} (hs : 0 < s) (i : Fin N)
    (x : X N) (k : Fin 3) :
    fderiv ℝ (fun z : X N => chiScale s (z i)) x (kcDir N i k)
      = fderiv ℝ (chiScale s) (x i) (kcStdBasis k) := by
  have hχ : DifferentiableAt ℝ (chiScale s) (x i) :=
    (chiScale_contDiff hs.ne').differentiable (by norm_num) (x i)
  have hf : DifferentiableAt ℝ (fun z : X N => z i) x :=
    (ContinuousLinearMap.proj (φ := fun _ : Fin N => ℝ³) i).differentiableAt
  have hcomp := fderiv_comp (x := x) (g := chiScale s) (f := fun z : X N => z i) hχ hf
  have hfun : (fun z : X N => chiScale s (z i)) = (chiScale s) ∘ (fun z : X N => z i) := rfl
  rw [hfun, hcomp, ContinuousLinearMap.comp_apply]
  have hproj : fderiv ℝ (fun z : X N => z i) x
      = ContinuousLinearMap.proj (φ := fun _ : Fin N => ℝ³) i :=
    ContinuousLinearMap.fderiv (ContinuousLinearMap.proj (φ := fun _ : Fin N => ℝ³) i)
  rw [hproj]
  simp [ContinuousLinearMap.proj, kcDir]

/-- Smoothness of the mean-free part `Q_i Φ`. -/
lemma dirichlet_contDiff_aQ {N : ℕ} {s : ℝ} (hs : 0 < s) (i : Fin N) {Φ : X N → ℝ}
    (hΦ : ContDiff ℝ ∞ Φ) : ContDiff ℝ ∞ (aQ s i Φ) := by
  unfold aQ
  exact hΦ.sub (contDiff_aP hs i hΦ)

/-! ## Pointwise bounds -/

/-- **Pointwise bound for one pair `(i,k)`.** -/
lemma dirichlet_aQ_term_le {n : ℕ} {s : ℝ} (hs : 0 < s)
    {Ψ : X (n + 1) → ℝ} (hΨ : ContDiff ℝ (⊤ : ENat) Ψ)
    (i : Fin (n + 1)) (x : X (n + 1)) (k : Fin 3) :
    (fderiv ℝ (fun z : X (n + 1) => chiScale s (z i) * aQ s i Ψ z) x
        (kcDir (n + 1) i k)) ^ 2
      ≤ 2 * chiSup ^ 2 * (fderiv ℝ Ψ x (kcDir (n + 1) i k)) ^ 2
        + 2 * ((fderiv ℝ (chiScale s) (x i) (kcStdBasis k)) ^ 2 * (aQ s i Ψ x) ^ 2) := by
  have hχ : DifferentiableAt ℝ (fun z : X (n + 1) => chiScale s (z i)) x :=
    ((chiScale_contDiff hs.ne').comp (by fun_prop : ContDiff ℝ ∞ (fun z : X (n + 1) => z i))).differentiable
      (by norm_num) x
  have hu : DifferentiableAt ℝ (aQ s i Ψ) x :=
    (dirichlet_contDiff_aQ hs i hΨ).differentiable (by norm_num) x
  have h1 := dirichlet_mul_dir_sq_le (χ := fun z : X (n + 1) => chiScale s (z i))
    (u := aQ s i Ψ) (x := x) (v := kcDir (n + 1) i k) hχ hu
  have h2 : fderiv ℝ (aQ s i Ψ) x (kcDir (n + 1) i k)
      = fderiv ℝ Ψ x (kcDir (n + 1) i k) := fderiv_aQ_kcDir hs i hΨ x k
  have h3 : fderiv ℝ (fun z : X (n + 1) => chiScale s (z i)) x (kcDir (n + 1) i k)
      = fderiv ℝ (chiScale s) (x i) (kcStdBasis k) := dirichlet_fderiv_chiScale_coord hs i x k
  have h4 : (chiScale s (x i)) ^ 2 ≤ chiSup ^ 2 := by
    rw [← sq_abs (chiScale s (x i))]
    exact pow_le_pow_left₀ (abs_nonneg _) (abs_chiScale_le_chiSup s (x i)) 2
  rw [h2, h3] at h1
  nlinarith [h1, h4, sq_nonneg chiSup,
    sq_nonneg (fderiv ℝ Ψ x (kcDir (n + 1) i k)), sq_nonneg (aQ s i Ψ x)]

/-- **Pointwise bound summed over the three coordinate directions.** -/
lemma dirichlet_aQ_sum_le {n : ℕ} {s : ℝ} (hs : 0 < s)
    {Ψ : X (n + 1) → ℝ} (hΨ : ContDiff ℝ (⊤ : ENat) Ψ)
    (i : Fin (n + 1)) (x : X (n + 1)) :
    (∑ k : Fin 3, (fderiv ℝ (fun z : X (n + 1) => chiScale s (z i) * aQ s i Ψ z) x
        (kcDir (n + 1) i k)) ^ 2)
      ≤ 2 * chiSup ^ 2 * (∑ k : Fin 3, (fderiv ℝ Ψ x (kcDir (n + 1) i k)) ^ 2)
        + 2 * ((∑ k : Fin 3, (fderiv ℝ (chiScale s) (x i) (kcStdBasis k)) ^ 2)
            * (aQ s i Ψ x) ^ 2) := by
  calc
    (∑ k : Fin 3, (fderiv ℝ (fun z : X (n + 1) => chiScale s (z i) * aQ s i Ψ z) x
        (kcDir (n + 1) i k)) ^ 2)
        ≤ ∑ k : Fin 3,
            (2 * chiSup ^ 2 * (fderiv ℝ Ψ x (kcDir (n + 1) i k)) ^ 2
              + 2 * ((fderiv ℝ (chiScale s) (x i) (kcStdBasis k)) ^ 2
                  * (aQ s i Ψ x) ^ 2)) :=
          Finset.sum_le_sum (fun k _ => dirichlet_aQ_term_le hs hΨ i x k)
    _ = 2 * chiSup ^ 2 * (∑ k : Fin 3, (fderiv ℝ Ψ x (kcDir (n + 1) i k)) ^ 2)
          + 2 * ((∑ k : Fin 3, (fderiv ℝ (chiScale s) (x i) (kcStdBasis k)) ^ 2)
              * (aQ s i Ψ x) ^ 2) := by
          rw [Finset.sum_add_distrib]
          congr 1
          · rw [Finset.mul_sum]
          · rw [Finset.sum_mul, Finset.mul_sum]

/-! ## Integrability of the three integrands -/

/-- Continuity of the windowed derivative integrand. -/
lemma dirichlet_continuous_left {n : ℕ} {s : ℝ} (hs : 0 < s)
    {Ψ : X (n + 1) → ℝ} (hΨ : ContDiff ℝ (⊤ : ENat) Ψ) (i : Fin (n + 1)) :
    Continuous (fun x : X (n + 1) => ∑ k : Fin 3,
      (fderiv ℝ (fun z : X (n + 1) => chiScale s (z i) * aQ s i Ψ z) x
        (kcDir (n + 1) i k)) ^ 2) := by
  have hχ : ContDiff ℝ ∞ (fun z : X (n + 1) => chiScale s (z i)) :=
    (chiScale_contDiff hs.ne').comp (by fun_prop : ContDiff ℝ ∞ (fun z : X (n + 1) => z i))
  have hf : ContDiff ℝ ∞ (fun z : X (n + 1) => chiScale s (z i) * aQ s i Ψ z) :=
    hχ.mul (dirichlet_contDiff_aQ hs i hΨ)
  refine continuous_finsetSum _ (fun k _ => ?_)
  exact (((hf.continuous_fderiv (by decide)).clm_apply continuous_const)).pow 2

/-- Continuity of the `kinWord` integrand. -/
lemma dirichlet_continuous_kin {n : ℕ}
    {Ψ : X (n + 1) → ℝ} (hΨ : ContDiff ℝ (⊤ : ENat) Ψ) (i : Fin (n + 1)) :
    Continuous (fun x : X (n + 1) =>
      ∑ k : Fin 3, (fderiv ℝ Ψ x (kcDir (n + 1) i k)) ^ 2) := by
  refine continuous_finsetSum _ (fun k _ => ?_)
  exact (((hΨ.continuous_fderiv (by decide)).clm_apply continuous_const)).pow 2

/-- Continuity of the window-error integrand. -/
lemma dirichlet_continuous_win {n : ℕ} {s : ℝ} (hs : 0 < s)
    {Ψ : X (n + 1) → ℝ} (hΨ : ContDiff ℝ (⊤ : ENat) Ψ) (i : Fin (n + 1)) :
    Continuous (fun x : X (n + 1) =>
      (∑ k : Fin 3, (fderiv ℝ (chiScale s) (x i) (kcStdBasis k)) ^ 2)
        * (aQ s i Ψ x) ^ 2) := by
  have hgrad : Continuous (fun x : X (n + 1) =>
      ∑ k : Fin 3, (fderiv ℝ (chiScale s) (x i) (kcStdBasis k)) ^ 2) := by
    have hχ : Continuous (fun x : X (n + 1) =>
        fderiv ℝ (chiScale s) (x i)) :=
      ((chiScale_contDiff hs.ne').continuous_fderiv (by decide)).comp (continuous_apply i)
    refine continuous_finsetSum _ (fun k _ => ?_)
    exact ((hχ.clm_apply continuous_const)).pow 2
  exact hgrad.mul (((dirichlet_contDiff_aQ hs i hΨ).continuous).pow 2)

/-! ## The integral step -/

/-- **The integral bound for a single slot**, obtained from the pointwise bound by
monotonicity and additivity of the integral. -/
lemma dirichlet_int_step {n : ℕ} {s : ℝ} (hs : 0 < s)
    {Ψ : X (n + 1) → ℝ} (hΨ : ContDiff ℝ (⊤ : ENat) Ψ) (i : Fin (n + 1)) :
    (∫ x in abox (n + 1) s, ∑ k : Fin 3,
        (fderiv ℝ (fun z : X (n + 1) => chiScale s (z i) * aQ s i Ψ z) x
          (kcDir (n + 1) i k)) ^ 2)
      ≤ 2 * chiSup ^ 2
          * (∫ x in abox (n + 1) s,
              ∑ k : Fin 3, (fderiv ℝ Ψ x (kcDir (n + 1) i k)) ^ 2)
        + 2 * (∫ x in abox (n + 1) s,
              (∑ k : Fin 3, (fderiv ℝ (chiScale s) (x i) (kcStdBasis k)) ^ 2)
                * (aQ s i Ψ x) ^ 2) := by
  have h1 : IntegrableOn (fun x : X (n + 1) => ∑ k : Fin 3,
      (fderiv ℝ (fun z : X (n + 1) => chiScale s (z i) * aQ s i Ψ z) x
        (kcDir (n + 1) i k)) ^ 2) (abox (n + 1) s) volume :=
    integrableOn_abox_of_continuous hs (dirichlet_continuous_left hs hΨ i)
  have h2 : IntegrableOn (fun x : X (n + 1) =>
      ∑ k : Fin 3, (fderiv ℝ Ψ x (kcDir (n + 1) i k)) ^ 2) (abox (n + 1) s) volume :=
    integrableOn_abox_of_continuous hs (dirichlet_continuous_kin hΨ i)
  have h3 : IntegrableOn (fun x : X (n + 1) =>
      (∑ k : Fin 3, (fderiv ℝ (chiScale s) (x i) (kcStdBasis k)) ^ 2)
        * (aQ s i Ψ x) ^ 2) (abox (n + 1) s) volume :=
    integrableOn_abox_of_continuous hs (dirichlet_continuous_win hs hΨ i)
  have hg : IntegrableOn (fun x : X (n + 1) =>
      2 * chiSup ^ 2 * (∑ k : Fin 3, (fderiv ℝ Ψ x (kcDir (n + 1) i k)) ^ 2)
        + 2 * ((∑ k : Fin 3, (fderiv ℝ (chiScale s) (x i) (kcStdBasis k)) ^ 2)
            * (aQ s i Ψ x) ^ 2)) (abox (n + 1) s) volume := by
    refine integrableOn_abox_of_continuous hs (Continuous.add ?_ ?_)
    · exact continuous_const.mul (dirichlet_continuous_kin hΨ i)
    · exact continuous_const.mul (dirichlet_continuous_win hs hΨ i)
  have hmono : (∫ x in abox (n + 1) s, ∑ k : Fin 3,
        (fderiv ℝ (fun z : X (n + 1) => chiScale s (z i) * aQ s i Ψ z) x
          (kcDir (n + 1) i k)) ^ 2)
      ≤ ∫ x in abox (n + 1) s,
          (2 * chiSup ^ 2 * (∑ k : Fin 3, (fderiv ℝ Ψ x (kcDir (n + 1) i k)) ^ 2)
            + 2 * ((∑ k : Fin 3, (fderiv ℝ (chiScale s) (x i) (kcStdBasis k)) ^ 2)
                * (aQ s i Ψ x) ^ 2)) :=
    integral_mono h1 hg (fun x => dirichlet_aQ_sum_le hs hΨ i x)
  have hsplit : (∫ x in abox (n + 1) s,
        (2 * chiSup ^ 2 * (∑ k : Fin 3, (fderiv ℝ Ψ x (kcDir (n + 1) i k)) ^ 2)
          + 2 * ((∑ k : Fin 3, (fderiv ℝ (chiScale s) (x i) (kcStdBasis k)) ^ 2)
              * (aQ s i Ψ x) ^ 2)))
      = 2 * chiSup ^ 2
          * (∫ x in abox (n + 1) s,
              ∑ k : Fin 3, (fderiv ℝ Ψ x (kcDir (n + 1) i k)) ^ 2)
        + 2 * (∫ x in abox (n + 1) s,
              (∑ k : Fin 3, (fderiv ℝ (chiScale s) (x i) (kcStdBasis k)) ^ 2)
                * (aQ s i Ψ x) ^ 2) := by
    rw [integral_add
      (f := fun x : X (n + 1) =>
        2 * chiSup ^ 2 * (∑ k : Fin 3, (fderiv ℝ Ψ x (kcDir (n + 1) i k)) ^ 2))
      (g := fun x : X (n + 1) =>
        2 * ((∑ k : Fin 3, (fderiv ℝ (chiScale s) (x i) (kcStdBasis k)) ^ 2)
            * (aQ s i Ψ x) ^ 2))
      (h2.const_mul _) (h3.const_mul _)]
    rw [integral_const_mul, integral_const_mul]
  exact hmono.trans_eq hsplit

/-! ## The theorem -/

theorem dirichlet_aQ_le {n : ℕ} {s : ℝ} (hs : 0 < s)
    {Ψ : (Fin (n + 1) → EuclideanSpace ℝ (Fin 3)) → ℝ} (hΨ : ContDiff ℝ (⊤ : ENat) Ψ) :
    (∑ i : Fin (n + 1), ∫ x in Submission.BoseGases.abox (n + 1) s, ∑ k : Fin 3,
        (fderiv ℝ (fun z : Fin (n + 1) → EuclideanSpace ℝ (Fin 3) =>
            Submission.BoseGases.chiScale s (z i) * Submission.BoseGases.aQ s i Ψ z) x
          (Submission.BoseGases.kcDir (n + 1) i k)) ^ 2)
      ≤ 2 * Submission.BoseGases.chiSup ^ 2 * Submission.BoseGases.kinWord (n + 1) s Ψ
        + 2 * Submission.BoseGases.winErrorQ s Ψ := by
  have hKW : (∑ i : Fin (n + 1), ∫ x in abox (n + 1) s,
        ∑ k : Fin 3, (fderiv ℝ Ψ x (kcDir (n + 1) i k)) ^ 2) = kinWord (n + 1) s Ψ := by
    rw [kinSum_sum_integral hs Ψ hΨ]
    rfl
  have hWQ : (∑ i : Fin (n + 1), ∫ x in abox (n + 1) s,
        (∑ k : Fin 3, (fderiv ℝ (chiScale s) (x i) (kcStdBasis k)) ^ 2)
          * (aQ s i Ψ x) ^ 2) = winErrorQ s Ψ := rfl
  calc
    (∑ i : Fin (n + 1), ∫ x in abox (n + 1) s, ∑ k : Fin 3,
        (fderiv ℝ (fun z : X (n + 1) => chiScale s (z i) * aQ s i Ψ z) x
          (kcDir (n + 1) i k)) ^ 2)
        ≤ ∑ i : Fin (n + 1),
            (2 * chiSup ^ 2
                * (∫ x in abox (n + 1) s,
                    ∑ k : Fin 3, (fderiv ℝ Ψ x (kcDir (n + 1) i k)) ^ 2)
              + 2 * (∫ x in abox (n + 1) s,
                    (∑ k : Fin 3, (fderiv ℝ (chiScale s) (x i) (kcStdBasis k)) ^ 2)
                      * (aQ s i Ψ x) ^ 2)) :=
          Finset.sum_le_sum (fun i _ => dirichlet_int_step hs hΨ i)
    _ = 2 * chiSup ^ 2
          * (∑ i : Fin (n + 1), ∫ x in abox (n + 1) s,
              ∑ k : Fin 3, (fderiv ℝ Ψ x (kcDir (n + 1) i k)) ^ 2)
        + 2 * (∑ i : Fin (n + 1), ∫ x in abox (n + 1) s,
              (∑ k : Fin 3, (fderiv ℝ (chiScale s) (x i) (kcStdBasis k)) ^ 2)
                * (aQ s i Ψ x) ^ 2) := by
          rw [Finset.sum_add_distrib]
          congr 1
          · rw [Finset.mul_sum]
          · rw [Finset.mul_sum]
    _ = 2 * chiSup ^ 2 * kinWord (n + 1) s Ψ + 2 * winErrorQ s Ψ := by rw [hKW, hWQ]

end Work.SmallBoxBridge.Position
