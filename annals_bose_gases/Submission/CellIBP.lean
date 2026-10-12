import ChallengeDeps
import Submission.FiberSlice
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Operator-to-gradient conversion of the per-cell energy (whole-space IBP)

The bracket compares `BracketSum.cellOpEnergy` (operator form: `φ·(−Δᵢφ)`
integrals) with the gradient-form energies that the slice machinery produces.
For smooth compactly supported `φ`, the whole-space integration by parts
(`KineticChild.kc_ws_dir2_eq` + the coordinate decomposition
`kc_partialLaplacian_eq`) converts the operator form into the gradient form:

  * `cellKinetic_eq_grad` — `∑_{i ∈ occSet a j} ∫ φ·(−Δᵢφ) =
    ∫ ∑_{i ∈ occSet a j} ∑_k (∂ᵢₖφ)²`;
  * `cellOpEnergy_eq_cellGradEnergy` — the per-cell operator energy equals the
    gradient-form per-cell energy (`cellIntra` and the interaction part of
    `cellGradEnergy` are the same integral by definition).

With this, L1 closes by integrating `SliceEnergy.sliceWsE_ge_eNeu` over the
frozen background (FiberSlice.cellGradEnergy_integral).
-/

namespace Submission

open _root_.BoseGases
open _root_.BoseGases.CInfty0Box
set_option autoImplicit false

namespace BoseGases

open Filter Metric MeasureTheory
open scoped ContDiff Topology Real

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- Whole-space integration by parts, one particle at a time:
`∫ φ·(−Δᵢφ) = ∑ₖ ∫ (∂ᵢₖφ)²` for a smooth compactly supported `φ`. -/
lemma kinetic_term_eq_grad {N : ℕ} {φ : X N → ℝ} (hφ : ContDiff ℝ ∞ φ) (hcs : HasCompactSupport φ)
    (i : Fin N) :
    (∫ x : X N, φ x * (-(partialLaplacian i φ) x)) =
      ∑ k : Fin 3, ∫ x : X N, (fderiv ℝ φ x (kcDir N i k)) ^ 2 := by
  let F : Fin 3 → X N → ℝ := fun k x =>
    φ x * (-(fderiv ℝ (fun z : X N => (fderiv ℝ φ z) (kcDir N i k)) x) (kcDir N i k))
  have hF : ∀ k : Fin 3, Integrable (F k) volume := by
    intro k
    dsimp [F]
    have hS : Continuous (fun x : X N =>
        (fderiv ℝ (fun z : X N => (fderiv ℝ φ z) (kcDir N i k)) x) (kcDir N i k)) :=
      (secondDir_contDiff_u hφ (kcDir N i k)).continuous
    exact Continuous.integrable_of_hasCompactSupport
      (hφ.continuous.mul hS.neg) hcs.mul_right
  have hpoint : (fun x : X N => φ x * (-(partialLaplacian i φ) x)) =
      fun x : X N => ∑ k : Fin 3, F k x := by
    funext x
    have hbr := kc_partialLaplacian_eq i (f := φ)
      (hφ.of_le (WithTop.coe_le_coe.mpr le_top : (2 : ℕ∞ω) ≤ ∞))
    have hbrx : partialLaplacian i φ x =
        ∑ k : Fin 3, (fderiv ℝ (fun z : X N => (fderiv ℝ φ z) (kcDir N i k)) x) (kcDir N i k) := by
      simpa using congrFun hbr x
    dsimp [F]
    rw [hbrx]
    rw [← Finset.sum_neg_distrib]
    rw [Finset.mul_sum]
  calc
    (∫ x : X N, φ x * (-(partialLaplacian i φ) x))
        = ∫ x : X N, ∑ k : Fin 3, F k x := by
          rw [hpoint]
    _ = ∑ k : Fin 3, ∫ x : X N, F k x := by
          exact integral_finsetSum (s := (Finset.univ : Finset (Fin 3))) (μ := volume) (f := F)
            (fun k hk => hF k)
    _ = ∑ k : Fin 3, ∫ x : X N, (fderiv ℝ φ x (kcDir N i k)) ^ 2 := by
          apply Finset.sum_congr rfl
          intro k hk
          dsimp [F]
          exact kc_ws_dir2_eq (f := φ) (u := kcDir N i k) hφ hcs

/-- Each squared directional derivative `x ↦ (∂ᵢₖφ x)²` is integrable over the
whole space (continuous and compactly supported). -/
lemma kinetic_dirSq_integrable {N : ℕ} {φ : X N → ℝ} (hφ : ContDiff ℝ ∞ φ) (hcs : HasCompactSupport φ)
    (i : Fin N) (k : Fin 3) :
    Integrable (fun x : X N => (fderiv ℝ φ x (kcDir N i k)) ^ 2) volume := by
  have hcont : Continuous (fun x : X N => (fderiv ℝ φ x (kcDir N i k)) ^ 2) :=
    (firstDir_contDiff hφ (kcDir N i k)).continuous.pow 2
  have hcsDir : HasCompactSupport (fun x : X N => fderiv ℝ φ x (kcDir N i k)) := by
    refine IsCompact.of_isClosed_subset hcs (isClosed_tsupport _) ?_
    simpa using (tsupport_firstDir_subset (f := φ) (kcDir N i k))
  have hcsSq : HasCompactSupport (fun x : X N => (fderiv ℝ φ x (kcDir N i k)) ^ 2) := by
    refine IsCompact.of_isClosed_subset hcsDir (isClosed_tsupport _) ?_
    simpa [pow_two] using
      (tsupport_mul_subset_left (f := (fun x : X N => fderiv ℝ φ x (kcDir N i k)))
        (g := (fun x : X N => fderiv ℝ φ x (kcDir N i k))))
  exact Continuous.integrable_of_hasCompactSupport hcont hcsSq

/-- The per-cell operator kinetic energy equals the gradient form (whole-space
integration by parts, per occupied particle). -/
lemma cellKinetic_eq_grad {m N : ℕ} (a : Assign m N) (j : CellIdx m)
    {φ : X N → ℝ} (hφ : ContDiff ℝ ∞ φ) (hcs : HasCompactSupport φ) :
    cellKinetic a j (φ := φ) =
      ∫ x : X N, ∑ i ∈ occSet a j, ∑ k : Fin 3, (fderiv ℝ φ x (kcDir N i k)) ^ 2 := by
  have hDirSq : ∀ i : Fin N, ∀ k : Fin 3,
      Integrable (fun x : X N => (fderiv ℝ φ x (kcDir N i k)) ^ 2) volume := by
    intro i k
    exact kinetic_dirSq_integrable hφ hcs i k
  have hH : ∀ i ∈ occSet a j, Integrable (fun x : X N =>
      ∑ k : Fin 3, (fderiv ℝ φ x (kcDir N i k)) ^ 2) volume := by
    intro i hi
    exact integrable_finsetSum (s := (Finset.univ : Finset (Fin 3))) (μ := volume)
      (f := fun k x => (fderiv ℝ φ x (kcDir N i k)) ^ 2) (fun k hk => hDirSq i k)
  calc
    cellKinetic a j (φ := φ)
        = ∑ i ∈ occSet a j, ∫ x : X N, φ x * (-(partialLaplacian i φ) x) := by
          rw [cellKinetic]
    _ = ∑ i ∈ occSet a j, (∑ k : Fin 3, ∫ x : X N, (fderiv ℝ φ x (kcDir N i k)) ^ 2) := by
          refine Finset.sum_congr rfl (fun i hi => kinetic_term_eq_grad hφ hcs i)
    _ = ∑ i ∈ occSet a j, ∫ x : X N, (∑ k : Fin 3, (fderiv ℝ φ x (kcDir N i k)) ^ 2) := by
          refine Finset.sum_congr rfl (fun i hi => ?_)
          exact (integral_finsetSum (s := (Finset.univ : Finset (Fin 3))) (μ := volume)
            (f := fun k x => (fderiv ℝ φ x (kcDir N i k)) ^ 2) (fun k hk => hDirSq i k)).symm
    _ = ∫ x : X N, ∑ i ∈ occSet a j, ∑ k : Fin 3, (fderiv ℝ φ x (kcDir N i k)) ^ 2 := by
          exact (integral_finsetSum (s := occSet a j) (μ := volume)
            (f := fun i x => ∑ k : Fin 3, (fderiv ℝ φ x (kcDir N i k)) ^ 2) hH).symm

/-- **The per-cell operator energy equals the gradient-form per-cell energy**
(whole-space IBP for the kinetic part; the interaction parts coincide by
definition). -/
lemma cellOpEnergy_eq_cellGradEnergy {m N : ℕ} (a : Assign m N) (j : CellIdx m)
    (v : ℝ³ → ℝ) {φ : X N → ℝ} (hφ : ContDiff ℝ ∞ φ) (hcs : HasCompactSupport φ) :
    cellOpEnergy a j v (φ := φ) = cellGradEnergy a j v (φ := φ) := by
  rw [cellOpEnergy, cellGradEnergy, cellKinetic_eq_grad a j (φ := φ) hφ hcs]
  simp [cellIntra]

end BoseGases

end Submission
