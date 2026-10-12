import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Submission.Work.BoseBoxFock.PCFU.SlotPieceDefs
import Submission.Work.BoseBoxFock.exists_fderiv_chiScale_bound_inv
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.windowedDirichlet_le`

The **windowed Dirichlet product rule**: for a smooth state `Φ` on the `n`-particle box, the
Dirichlet form of the windowed fibre function `z ↦ χ_ℓ(z)·Φ(x[i ↦ z])` is bounded by twice the
`χ_ℓ(x_i)²`-weighted **fibre** Dirichlet form of `Φ` plus the price `2·(M/ℓ)²·∫_{box} Φ²` of the
window, where `M/ℓ` is the operator-norm bound on `fderiv χ_ℓ` supplied as a hypothesis.

## Proof

Everything is pointwise inside the box.

* The fibrewise derivative is the master derivative along the insertion direction:
  `fderiv ℝ (fun z => Φ (update x i z)) (x i) = (fderiv ℝ Φ x).comp π` with
  `π = ContinuousLinearMap.pi (Pi.single i (ContinuousLinearMap.id ℝ E3))` (`fderiv_update` +
  chain rule); evaluating at the basis vector `single k 1` gives the "`kcDir`" direction
  `Function.update 0 i (single k 1)`.
* Leibniz (`fderiv_fun_mul`) splits the derivative of the windowed product into
  `χ_ℓ(x i)·(∂_k Φ)_fib + Φ(x)·∂_k χ_ℓ`, and `(a+b)² ≤ 2a² + 2b²` separates the two terms.
* The single non-elementary input is that the sum of the squares of the coordinates of a
  *continuous linear functional* against the standard orthonormal basis is bounded by the square
  of its operator norm: `∑ k, (L (single k 1))² ≤ ‖L‖²`
  (`sumSq_single_le_opNorm`, proved by evaluating `L` on its gradient vector
  `g = ∑ k, L (single k 1) • single k 1` and using `L g = ‖g‖²`).
* Integrability of both sides over the compact box `abox n ℓ` follows from continuity of the
  integrands (`abox_compact` + `ContinuousOn.integrableOn_compact`); note that `Φ` need not have
  compact support — the box is what makes everything finite.
-/

namespace Work.BoseBoxFock.PCFU

noncomputable section

open MeasureTheory
open scoped ContDiff Topology Real BigOperators

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1000000

/-- **A real continuous linear functional on `ℝ³` is Hilbert–Schmidt.**

For `L : ℝ³ →L[ℝ] ℝ`, the sum of the squares of the values of `L` on the standard orthonormal
basis is bounded by `‖L‖²`.  (In fact the two are equal: the Euclidean gradient `g` of `L` is
`∑ k, L (single k 1) • single k 1`, and `∑ k, (L (single k 1))² = ‖g‖² = L g ≤ ‖L‖·‖g‖`.) -/
theorem sumSq_single_le_opNorm (L : E3 →L[ℝ] ℝ) :
    ∑ k : Fin 3, (L (EuclideanSpace.single k (1 : ℝ))) ^ 2 ≤ ‖L‖ ^ 2 := by
  have hv : Orthonormal ℝ (fun k : Fin 3 => EuclideanSpace.single k (1 : ℝ)) :=
    EuclideanSpace.orthonormal_single
  set c : Fin 3 → ℝ := fun k => L (EuclideanSpace.single k (1 : ℝ))
  set g : E3 := ∑ k : Fin 3, c k • EuclideanSpace.single k (1 : ℝ)
  have hg : g = ∑ k : Fin 3, c k • EuclideanSpace.single k (1 : ℝ) := rfl
  have hinner : inner ℝ g g = ∑ k : Fin 3, c k * c k := by
    rw [hg]
    have h := Orthonormal.inner_sum hv c c Finset.univ
    simpa using h
  have hgg : inner ℝ g g = ‖g‖ ^ 2 := real_inner_self_eq_norm_sq g
  have hLg : L g = ∑ k : Fin 3, c k * c k := by
    rw [hg, map_sum]
    exact Finset.sum_congr rfl fun k _ => by simp [c]
  have hle : ‖g‖ ^ 2 ≤ ‖L‖ * ‖g‖ := by
    calc ‖g‖ ^ 2 = L g := by rw [← hgg, hLg, hinner]
      _ ≤ ‖L g‖ := Real.le_norm_self _
      _ ≤ ‖L‖ * ‖g‖ := ContinuousLinearMap.le_opNorm L g
  have h1 : ‖g‖ ≤ ‖L‖ := by
    rw [pow_two] at hle
    by_cases h0 : ‖g‖ = 0
    · rw [h0]; exact norm_nonneg L
    · exact le_of_mul_le_mul_right hle (lt_of_le_of_ne (norm_nonneg g) (Ne.symm h0))
  calc ∑ k : Fin 3, (c k) ^ 2 = ∑ k : Fin 3, c k * c k := by simp [pow_two]
    _ = ‖g‖ ^ 2 := by rw [← hinner, hgg]
    _ ≤ ‖L‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg g) h1 2

variable {n : ℕ}

/-- **The fibrewise derivative of a smooth state.**  Changing the slot `i` of `x` is the affine
map `z ↦ Function.update x i z`, whose derivative is the insertion functional
`π = ContinuousLinearMap.pi (Pi.single i (ContinuousLinearMap.id ℝ E3))`; hence, by the chain rule,
`fderiv ℝ (fun z => Φ (Function.update x i z)) (x i) = (fderiv ℝ Φ x).comp π`. -/
theorem fderiv_update_comp {Φ : Submission.BoseGases.X n → ℝ}
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (i : Fin n) (x : Submission.BoseGases.X n) :
    fderiv ℝ (fun z : E3 => Φ (Function.update x i z)) (x i)
      = (fderiv ℝ Φ x).comp
          (ContinuousLinearMap.pi (Pi.single i (ContinuousLinearMap.id ℝ E3))) := by
  have hg : HasFDerivAt Φ (fderiv ℝ Φ (Function.update x i (x i)))
      (Function.update x i (x i)) :=
    (hΦ.differentiable (by simp) _).hasFDerivAt
  have hcomp := hg.comp (x i) (hasFDerivAt_update x (x i))
  simpa [Function.comp_def, Function.update_self] using hcomp.fderiv

/-- Evaluation of the insertion functional: `π (single k 1) = Function.update 0 i (single k 1)`. -/
theorem pi_single_apply (i : Fin n) (k : Fin 3) :
    (ContinuousLinearMap.pi (Pi.single i (ContinuousLinearMap.id ℝ E3)))
        (EuclideanSpace.single k (1 : ℝ))
      = Function.update (0 : Submission.BoseGases.X n) i (EuclideanSpace.single k (1 : ℝ)) := by
  funext j
  by_cases h : j = i
  · subst h; simp [ContinuousLinearMap.pi_apply]
  · simp [ContinuousLinearMap.pi_apply, h]

/-- **Evaluated fibrewise derivative.**  The partial derivative of `Φ` in the `k`-th coordinate of
the `i`-th slot is the master derivative along the insertion direction. -/
theorem fderiv_update_comp_apply {Φ : Submission.BoseGases.X n → ℝ}
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (i : Fin n) (x : Submission.BoseGases.X n) (k : Fin 3) :
    fderiv ℝ (fun z : E3 => Φ (Function.update x i z)) (x i) (EuclideanSpace.single k (1 : ℝ))
      = fderiv ℝ Φ x (Function.update 0 i (EuclideanSpace.single k (1 : ℝ))) := by
  rw [fderiv_update_comp hΦ i x, ContinuousLinearMap.comp_apply, pi_single_apply i k]

/-- **Leibniz for the windowed fibre.**  Splitting the product `χ_ℓ(z)·Φ(x[i ↦ z])` gives
`∂_k (χ_ℓ·Φ∘update) = χ_ℓ(x i)·(∂_k Φ∘update) + Φ(x)·∂_k χ_ℓ` at `z = x i`. -/
theorem fderiv_windowed_update {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : Submission.BoseGases.X n → ℝ}
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (i : Fin n) (x : Submission.BoseGases.X n) (k : Fin 3) :
    fderiv ℝ (fun z : E3 =>
        Submission.BoseGases.chiScale ℓ z * Φ (Function.update x i z)) (x i)
        (EuclideanSpace.single k (1 : ℝ))
      = Submission.BoseGases.chiScale ℓ (x i) *
          (fderiv ℝ Φ x (Function.update 0 i (EuclideanSpace.single k (1 : ℝ))))
        + Φ x *
          (fderiv ℝ (Submission.BoseGases.chiScale ℓ) (x i) (EuclideanSpace.single k (1 : ℝ))) := by
  have hχd : DifferentiableAt ℝ (Submission.BoseGases.chiScale ℓ) (x i) :=
    (Submission.BoseGases.chiScale_contDiff (ne_of_gt hℓ)).differentiable (by simp) _
  have hΦd : DifferentiableAt ℝ (fun z : E3 => Φ (Function.update x i z)) (x i) :=
    (hΦ.comp (contDiff_update ∞ x i)).differentiable (by simp) _
  rw [fderiv_fun_mul hχd hΦd]
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [fderiv_update_comp_apply hΦ i x k, Function.update_eq_self]

theorem windowedDirichlet_le {n : ℕ} (i : Fin n) {ℓ M : ℝ} (hℓ : 0 < ℓ) (hM0 : 0 ≤ M)
    (hM : ∀ (x w : EuclideanSpace ℝ (Fin 3)),
      |fderiv ℝ (Submission.BoseGases.chiScale ℓ) x w| ≤ (M / ℓ) * ‖w‖)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    ∫ x in Submission.BoseGases.abox n ℓ,
        (∑ k : Fin 3, ‖fderiv ℝ (fun z : EuclideanSpace ℝ (Fin 3) =>
          Submission.BoseGases.chiScale ℓ z *
            Φ (Function.update x i z)) (x i) (EuclideanSpace.single k (1 : ℝ))‖ ^ 2)
      ≤ 2 * (∫ x in Submission.BoseGases.abox n ℓ,
            (Submission.BoseGases.chiScale ℓ (x i)) ^ 2 *
              (∑ k : Fin 3, ‖fderiv ℝ (fun z : EuclideanSpace ℝ (Fin 3) =>
                Φ (Function.update x i z)) (x i) (EuclideanSpace.single k (1 : ℝ))‖ ^ 2))
        + 2 * (M / ℓ) ^ 2 * ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 := by
  classical
  have hℓne : ℓ ≠ 0 := ne_of_gt hℓ
  have hMdiv : 0 ≤ M / ℓ := div_nonneg hM0 hℓ.le
  let F : Submission.BoseGases.X n → ℝ := fun x => ∑ k : Fin 3, ‖fderiv ℝ (fun z : E3 =>
    Submission.BoseGases.chiScale ℓ z * Φ (Function.update x i z)) (x i)
    (EuclideanSpace.single k (1 : ℝ))‖ ^ 2
  let G : Submission.BoseGases.X n → ℝ := fun x => (Submission.BoseGases.chiScale ℓ (x i)) ^ 2 *
    (∑ k : Fin 3, ‖fderiv ℝ (fun z : E3 => Φ (Function.update x i z)) (x i)
      (EuclideanSpace.single k (1 : ℝ))‖ ^ 2)
  let H : Submission.BoseGases.X n → ℝ := fun x => (Φ x) ^ 2
  change ∫ x in Submission.BoseGases.abox n ℓ, F x
      ≤ 2 * (∫ x in Submission.BoseGases.abox n ℓ, G x)
        + 2 * (M / ℓ) ^ 2 * ∫ x in Submission.BoseGases.abox n ℓ, H x
  -- ## the sum bound for the derivative of the window
  have hsumA : ∀ x : Submission.BoseGases.X n,
      ∑ k : Fin 3, ‖fderiv ℝ (Submission.BoseGases.chiScale ℓ) (x i)
        (EuclideanSpace.single k (1 : ℝ))‖ ^ 2 ≤ (M / ℓ) ^ 2 := by
    intro x
    have hLn : ‖fderiv ℝ (Submission.BoseGases.chiScale ℓ) (x i)‖ ≤ M / ℓ := by
      refine ContinuousLinearMap.opNorm_le_bound _ hMdiv (fun w => ?_)
      rw [Real.norm_eq_abs]
      exact hM (x i) w
    calc ∑ k : Fin 3, ‖fderiv ℝ (Submission.BoseGases.chiScale ℓ) (x i)
            (EuclideanSpace.single k (1 : ℝ))‖ ^ 2
        = ∑ k : Fin 3, (fderiv ℝ (Submission.BoseGases.chiScale ℓ) (x i)
            (EuclideanSpace.single k (1 : ℝ))) ^ 2 :=
          Finset.sum_congr rfl fun k _ => sq_abs _
      _ ≤ ‖fderiv ℝ (Submission.BoseGases.chiScale ℓ) (x i)‖ ^ 2 :=
          sumSq_single_le_opNorm _
      _ ≤ (M / ℓ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hLn 2
  have hGx : ∀ x : Submission.BoseGases.X n,
      G x = (Submission.BoseGases.chiScale ℓ (x i)) ^ 2 *
        (∑ k : Fin 3, ‖fderiv ℝ Φ x (Function.update 0 i
          (EuclideanSpace.single k (1 : ℝ)))‖ ^ 2) := by
    intro x
    dsimp only [G]
    congr 1
    exact Finset.sum_congr rfl fun k _ => by rw [fderiv_update_comp_apply hΦ i x k]
  -- ## the pointwise product-rule bound
  have hpt : ∀ x : Submission.BoseGases.X n, F x ≤ 2 * G x + 2 * (M / ℓ) ^ 2 * H x := by
    intro x
    have hstep : ∀ k : Fin 3,
        ‖fderiv ℝ (fun z : E3 => Submission.BoseGases.chiScale ℓ z *
            Φ (Function.update x i z)) (x i) (EuclideanSpace.single k (1 : ℝ))‖ ^ 2
          ≤ 2 * (Submission.BoseGases.chiScale ℓ (x i)) ^ 2 *
              ‖fderiv ℝ Φ x (Function.update 0 i (EuclideanSpace.single k (1 : ℝ)))‖ ^ 2
            + 2 * (Φ x) ^ 2 *
              ‖fderiv ℝ (Submission.BoseGases.chiScale ℓ) (x i)
                (EuclideanSpace.single k (1 : ℝ))‖ ^ 2 := by
      intro k
      rw [fderiv_windowed_update hℓ hΦ i x k]
      simp only [Real.norm_eq_abs, sq_abs]
      nlinarith [sq_nonneg (Submission.BoseGases.chiScale ℓ (x i) * (fderiv ℝ Φ x)
          (Function.update 0 i (EuclideanSpace.single k (1 : ℝ)))
        - Φ x * (fderiv ℝ (Submission.BoseGases.chiScale ℓ) (x i))
          (EuclideanSpace.single k (1 : ℝ)))]
    calc F x = ∑ k : Fin 3, ‖fderiv ℝ (fun z : E3 => Submission.BoseGases.chiScale ℓ z *
        Φ (Function.update x i z)) (x i) (EuclideanSpace.single k (1 : ℝ))‖ ^ 2 := rfl
      _ ≤ ∑ k : Fin 3,
            (2 * (Submission.BoseGases.chiScale ℓ (x i)) ^ 2 *
                ‖fderiv ℝ Φ x (Function.update 0 i (EuclideanSpace.single k (1 : ℝ)))‖ ^ 2
              + 2 * (Φ x) ^ 2 *
                ‖fderiv ℝ (Submission.BoseGases.chiScale ℓ) (x i)
                  (EuclideanSpace.single k (1 : ℝ))‖ ^ 2) :=
          Finset.sum_le_sum fun k _ => hstep k
      _ = 2 * (Submission.BoseGases.chiScale ℓ (x i)) ^ 2 *
            (∑ k : Fin 3, ‖fderiv ℝ Φ x
              (Function.update 0 i (EuclideanSpace.single k (1 : ℝ)))‖ ^ 2)
          + 2 * (Φ x) ^ 2 *
            (∑ k : Fin 3, ‖fderiv ℝ (Submission.BoseGases.chiScale ℓ) (x i)
              (EuclideanSpace.single k (1 : ℝ))‖ ^ 2) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ 2 * (Submission.BoseGases.chiScale ℓ (x i)) ^ 2 *
            (∑ k : Fin 3, ‖fderiv ℝ Φ x
              (Function.update 0 i (EuclideanSpace.single k (1 : ℝ)))‖ ^ 2)
          + 2 * (Φ x) ^ 2 * (M / ℓ) ^ 2 :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left (hsumA x) (by positivity))
      _ = 2 * G x + 2 * (M / ℓ) ^ 2 * H x := by
          rw [hGx x]; dsimp only [H]; ring
  -- ## continuity of the integrands
  have hcontχ : Continuous
      (fun x : Submission.BoseGases.X n => Submission.BoseGases.chiScale ℓ (x i)) :=
    (Submission.BoseGases.chiScale_contDiff hℓne).continuous.comp (continuous_apply i)
  have hcontB : ∀ k : Fin 3, Continuous (fun x : Submission.BoseGases.X n =>
      fderiv ℝ Φ x (Function.update 0 i (EuclideanSpace.single k (1 : ℝ)))) :=
    fun k => (hΦ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcontA : ∀ k : Fin 3, Continuous (fun x : Submission.BoseGases.X n =>
      fderiv ℝ (Submission.BoseGases.chiScale ℓ) (x i)
        (EuclideanSpace.single k (1 : ℝ))) := fun k =>
    (((Submission.BoseGases.chiScale_contDiff hℓne).continuous_fderiv (by simp)).comp
      (continuous_apply i)).clm_apply continuous_const
  have hGcont : Continuous G := by
    have h1 : Continuous (fun x : Submission.BoseGases.X n => ∑ k : Fin 3, ‖fderiv ℝ Φ x
        (Function.update 0 i (EuclideanSpace.single k (1 : ℝ)))‖ ^ 2) :=
      continuous_finsetSum Finset.univ (fun k _ => (hcontB k).norm.pow 2)
    have h2 : G = fun x => (Submission.BoseGases.chiScale ℓ (x i)) ^ 2 *
        (∑ k : Fin 3, ‖fderiv ℝ Φ x
          (Function.update 0 i (EuclideanSpace.single k (1 : ℝ)))‖ ^ 2) := by
      funext x
      dsimp only [G]
      congr 1
      exact Finset.sum_congr rfl fun k _ => by rw [fderiv_update_comp_apply hΦ i x k]
    rw [h2]
    exact (hcontχ.pow 2).mul h1
  have hHcont : Continuous H := by
    dsimp only [H]
    exact hΦ.continuous.pow 2
  have hFcont : Continuous F := by
    have h1 : Continuous (fun x : Submission.BoseGases.X n => ∑ k : Fin 3,
        (Submission.BoseGases.chiScale ℓ (x i) * (fderiv ℝ Φ x
            (Function.update 0 i (EuclideanSpace.single k (1 : ℝ))))
          + Φ x * (fderiv ℝ (Submission.BoseGases.chiScale ℓ) (x i)
            (EuclideanSpace.single k (1 : ℝ)))) ^ 2) :=
      continuous_finsetSum Finset.univ
        (fun k _ => ((hcontχ.mul (hcontB k)).add (hΦ.continuous.mul (hcontA k))).pow 2)
    refine h1.congr ?_
    intro x
    dsimp only [F]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [fderiv_windowed_update hℓ hΦ i x k]
    simp only [Real.norm_eq_abs, sq_abs]
  -- ## integrability and the integral comparison
  have hFint : Integrable F
      ((volume : Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ)) :=
    ContinuousOn.integrableOn_compact (Submission.BoseGases.abox_compact n hℓ)
      hFcont.continuousOn
  have hGint : Integrable G
      ((volume : Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ)) :=
    ContinuousOn.integrableOn_compact (Submission.BoseGases.abox_compact n hℓ)
      hGcont.continuousOn
  have hHint : Integrable H
      ((volume : Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ)) :=
    ContinuousOn.integrableOn_compact (Submission.BoseGases.abox_compact n hℓ)
      hHcont.continuousOn
  have hmono : ∫ x in Submission.BoseGases.abox n ℓ, F x
      ≤ ∫ x in Submission.BoseGases.abox n ℓ, (2 * G x + 2 * (M / ℓ) ^ 2 * H x) :=
    integral_mono_ae hFint (hGint.const_mul 2 |>.add (hHint.const_mul (2 * (M / ℓ) ^ 2)))
      (Filter.Eventually.of_forall hpt)
  calc ∫ x in Submission.BoseGases.abox n ℓ, F x
      ≤ ∫ x in Submission.BoseGases.abox n ℓ, (2 * G x + 2 * (M / ℓ) ^ 2 * H x) := hmono
    _ = 2 * (∫ x in Submission.BoseGases.abox n ℓ, G x)
        + 2 * (M / ℓ) ^ 2 * (∫ x in Submission.BoseGases.abox n ℓ, H x) := by
        rw [integral_add (hGint.const_mul 2) (hHint.const_mul (2 * (M / ℓ) ^ 2)),
          integral_const_mul, integral_const_mul]

end

end Work.BoseBoxFock.PCFU
