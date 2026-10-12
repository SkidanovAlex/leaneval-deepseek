import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SmallBoxTBWord.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `rhs_slot_peel` — peeling the `i`-th slot out of the `(n+1)`-particle box

FS `eq:appTB`'s right-hand side is the `𝒯_B` word written with the `i`-th slot of the
many-particle configuration frozen: the whole `(n+1)`-particle derivative-difference
integral over `abox (n+1) a` is an iterated integral over the peeled slot
`y ∈ acube a` and the remaining configuration `r ∈ abox n a`.

The only mathematics is the `kcInsN`-dictionary between the two pictures:

* `kcInsN n i (y, r)` inserts `y` in the `i`-th slot, and perturbing that slot by
  `t • kcStdBasis k` is perturbing the configuration by `t • kcDir (n+1) i k`
  (`Work.SmallBoxBridge.Fourier.kcInsN_add_smul`), so along the two curves the
  many-particle function `z ↦ W (z i)·Φ z` and the fibre function
  `w ↦ W w·Φ (kcInsN n i (w,r))` agree (`fderiv_slot_eq_fibre_W`);
* the box integral is carried to the product integral by the measure-preserving
  `kcInsN` (`Submission.BoseGases.abox_integral_peel`).

Integrability on the compact box comes from `ContDiff`ness of the integrand.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.SmallBoxTBWord

open Submission.BoseGases
open _root_.BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## 1  The slot derivative is the fibre derivative

The `kcDir (n+1) i k`-directional derivative of `z ↦ W (z i)·Φ z` at `kcInsN n i (y,r)`
equals the `kcStdBasis k`-directional derivative of the one-variable fibre
`w ↦ W w·Φ (kcInsN n i (w,r))` at `y`.  This is `T0Form_slot_eq_dirichlet`'s
`fderiv_slot_eq_fibre` with the window `chiScale s` replaced by a general smooth `W`. -/

theorem fderiv_slot_eq_fibre_W {n : ℕ} {W : ℝ³ → ℝ} (hW : ContDiff ℝ ∞ W)
    {Φ : X (n + 1) → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (i : Fin (n + 1)) (r : X n) (y : ℝ³)
    (k : Fin 3) :
    fderiv ℝ (fun z : X (n + 1) => W (z i) * Φ z)
      (kcInsN n i (y, r)) (kcDir (n + 1) i k)
      = fderiv ℝ (fun w : ℝ³ => W w * Φ (kcInsN n i (w, r)))
        y (kcStdBasis k) := by
  set A : X (n + 1) → ℝ := fun z => W (z i) * Φ z with hA
  set B : ℝ³ → ℝ := fun w => W w * Φ (kcInsN n i (w, r)) with hB
  have hWi : ContDiff ℝ ∞ (fun z : X (n + 1) => W (z i)) := hW.comp (by fun_prop)
  have hA_diff : DifferentiableAt ℝ A (kcInsN n i (y, r)) :=
    (hWi.mul hΦ).differentiable (by norm_num) _
  have hB_diff : DifferentiableAt ℝ B y :=
    ((hW.mul (hΦ.comp (Work.SmallBoxBridge.Fourier.contDiff_kcInsN_right i r)))).differentiable
      (by norm_num) _
  have hc : HasDerivAt (fun t : ℝ => kcInsN n i (y, r) + t • kcDir (n + 1) i k)
      (kcDir (n + 1) i k) 0 := by
    have h : HasDerivAt (fun t : ℝ => t • kcDir (n + 1) i k) (kcDir (n + 1) i k) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const (kcDir (n + 1) i k)
    simpa using h.const_add (kcInsN n i (y, r))
  have hd : HasDerivAt (fun t : ℝ => y + t • kcStdBasis k) (kcStdBasis k) 0 := by
    have h : HasDerivAt (fun t : ℝ => t • kcStdBasis k) (kcStdBasis k) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const (kcStdBasis k)
    simpa using h.const_add y
  have hA2 : HasFDerivAt A (fderiv ℝ A (kcInsN n i (y, r)))
      (kcInsN n i (y, r) + (0 : ℝ) • kcDir (n + 1) i k) := by
    simpa using hA_diff.hasFDerivAt
  have hB2 : HasFDerivAt B (fderiv ℝ B y) (y + (0 : ℝ) • kcStdBasis k) := by
    simpa using hB_diff.hasFDerivAt
  have h1 : HasDerivAt (A ∘ fun t : ℝ => kcInsN n i (y, r) + t • kcDir (n + 1) i k)
      ((fderiv ℝ A (kcInsN n i (y, r))) (kcDir (n + 1) i k)) 0 :=
    hA2.comp_hasDerivAt 0 hc
  have h2 : HasDerivAt (B ∘ fun t : ℝ => y + t • kcStdBasis k)
      ((fderiv ℝ B y) (kcStdBasis k)) 0 := hB2.comp_hasDerivAt 0 hd
  have hfun : (A ∘ fun t : ℝ => kcInsN n i (y, r) + t • kcDir (n + 1) i k)
      = (B ∘ fun t : ℝ => y + t • kcStdBasis k) := by
    funext t
    simp only [Function.comp_apply, hA, hB]
    rw [Work.SmallBoxBridge.Fourier.kcInsN_add_smul, kc_insN_apply_same]
  rw [hfun] at h1
  exact h1.unique h2

/-! ## 2  The peel -/

theorem rhs_slot_peel {n : ℕ} {a : ℝ} (ha : 0 < a) {W : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hW : ContDiff ℝ (⊤ : ENat) W) {Φ : Submission.BoseGases.X (n + 1) → ℝ} (hΦ : ContDiff ℝ (⊤ : ENat) Φ)
    (i : Fin (n + 1)) :
    ∫ x in Submission.BoseGases.abox (n + 1) a, ∑ k : Fin 3,
        (fderiv ℝ (fun z : Submission.BoseGases.X (n + 1) => W (z i) * Φ z) x
          (Submission.BoseGases.kcDir (n + 1) i k)) ^ 2
      = ∫ r in Submission.BoseGases.abox n a,
          ∫ y in Submission.BoseGases.acube a, ∑ k : Fin 3,
            (fderiv ℝ (fun w : EuclideanSpace ℝ (Fin 3) => W w * Φ (Submission.BoseGases.kcInsN n i (w, r)))
              y (Submission.BoseGases.kcStdBasis k)) ^ 2 := by
  have hWi : ContDiff ℝ ∞ (fun z : X (n + 1) => W (z i)) := hW.comp (by fun_prop)
  have hA : ContDiff ℝ ∞ (fun z : X (n + 1) => W (z i) * Φ z) := hWi.mul hΦ
  have hfd : Continuous (fun x : X (n + 1) => fderiv ℝ (fun z : X (n + 1) => W (z i) * Φ z) x) :=
    hA.continuous_fderiv (by simp)
  have hInt : IntegrableOn (fun x : X (n + 1) => ∑ k : Fin 3,
      (fderiv ℝ (fun z : X (n + 1) => W (z i) * Φ z) x (kcDir (n + 1) i k)) ^ 2)
      (abox (n + 1) a) volume :=
    ContinuousOn.integrableOn_compact (abox_compact (n + 1) ha)
      (continuous_finsetSum _ (fun k _ => ((hfd.clm_apply continuous_const).pow 2))).continuousOn
  rw [abox_integral_peel (n := n) (ℓ := a) i _ hInt]
  refine integral_congr_ae (Eventually.of_forall (fun r => ?_))
  refine integral_congr_ae (Eventually.of_forall (fun y => ?_))
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [fderiv_slot_eq_fibre_W hW hΦ i r y k]

end Work.SmallBoxTBWord
