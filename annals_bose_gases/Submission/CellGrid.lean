import Mathlib.Tactic.Have
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import ChallengeDeps
import Submission.CellCutoffs
import Submission.Profile
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The 3D cell partition of unity with quantified error density

This module instantiates the abstract `Submission.CellCutoffs` construction with
the concrete profile `rhoProfile` of `Submission.Profile`, and builds the
three-dimensional cell family over the cube `[0, m·ℓ]³`: a cell is a triple of
axis cells `c = (a,b,d) : CellIdx m`, with cutoff

    χ_c(y) := ξ_a(y₀)·ξ_b(y₁)·ξ_d(y₂),      ξ_j(t) := rhoProfile (t/ℓ + 1 − j),

one factor per coordinate.  Results (all pointwise on the cube, i.e. for `y`
with `0 ≤ y_k ≤ mℓ`):

  * `cellCut_contDiff` — each cell cutoff is smooth;
  * `cellCut_pu` — `Σ_c χ_c(y)² = 1` (exact partition of unity on the cube);
  * `cell_partial_axis_sum_le` — for each coordinate direction `k`,
    `Σ_c (∂_k χ_c(y))² ≤ 2A²/ℓ²`, where `|ρ′| ≤ A` (at most two axis cells
    overlap, and the two other axes sum to `1`);
  * `cell_partial_sq_sum_le` — summing over the three directions:
    `Σ_c Σ_k (∂_k χ_c(y))² ≤ 6A²/ℓ²`.

This is the `C`-term of `ManyBodyIMS.ims_pieces_le_whole_err`: localizing a
state with these cell cutoffs costs kinetic energy at most
`(6A²/ℓ²)·‖f‖²` per localised particle, with the error density bounded by the
explicit constant `6A²/ℓ²` (independent of `m`, since at most two axis cells
overlap any point).
-/

namespace Submission

open _root_.BoseGases
open _root_.BoseGases.CInfty0Box
set_option autoImplicit false

namespace BoseGases

open Filter Metric MeasureTheory
open scoped ContDiff Topology Real

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- A 3D cell: three axis cells, one per coordinate direction. -/
abbrev CellIdx (m : ℕ) := (Fin (m + 2)) × (Fin (m + 2)) × (Fin (m + 2))

/-- The cutoff of the cell `c`, a product of the three axis profiles evaluated
at the three coordinates of `y`. -/
noncomputable def cellCut (ℓ : ℝ) (m : ℕ) (c : CellIdx m) (y : ℝ³) : ℝ :=
  axisFam rhoProfile ℓ m c.1 (y 0) * axisFam rhoProfile ℓ m c.2.1 (y 1) *
    axisFam rhoProfile ℓ m c.2.2 (y 2)

lemma axisFam_contDiff (ℓ : ℝ) (m : ℕ) (j : Fin (m + 2)) :
    ContDiff ℝ ∞ (fun t : ℝ => axisFam rhoProfile ℓ m j t) := by
  unfold axisFam
  have hlin : ContDiff ℝ ∞ (fun t : ℝ => t / ℓ + 1 - (j.val : ℝ)) := by fun_prop
  exact profile_contDiff.comp hlin

attribute [fun_prop] axisFam_contDiff

/-- The cell cutoff is smooth. -/
lemma cellCut_contDiff (ℓ : ℝ) (m : ℕ) (c : CellIdx m) :
    ContDiff ℝ ∞ (cellCut ℓ m c) := by
  unfold cellCut
  fun_prop

/-- the coordinate-curve derivative formula for a shifted axis factor -/
lemma axis_deriv_shift (ℓ : ℝ) (m : ℕ) (j : Fin (m + 2)) (c0 : ℝ) :
    deriv (fun t : ℝ => axisFam rhoProfile ℓ m j (c0 + t)) 0 =
      deriv (fun u : ℝ => axisFam rhoProfile ℓ m j u) c0 := by
  have h1 : (fun t : ℝ => axisFam rhoProfile ℓ m j (c0 + t)) =
      (fun u : ℝ => axisFam rhoProfile ℓ m j (1 * u + c0)) := by
    funext t
    congr 1
    ring
  rw [h1]
  have hA0 := deriv_comp_affine (ρ := fun u : ℝ => axisFam rhoProfile ℓ m j u)
    (a := 1) (b := c0) (x := 0) (by norm_num : (1 : ℝ) ≠ 0)
  simpa using hA0

/-- derivative of an axis function along a shifted curve -/
lemma axis_diff_shift (ℓ : ℝ) (m : ℕ) (j : Fin (m + 2)) (c0 : ℝ) :
    DifferentiableAt ℝ (fun t : ℝ => axisFam rhoProfile ℓ m j (c0 + t)) 0 := by
  have hc : ContDiff ℝ ∞ (fun t : ℝ => axisFam rhoProfile ℓ m j (c0 + t)) := by
    exact (axisFam_contDiff ℓ m j).comp (by fun_prop : ContDiff ℝ ∞ (fun t : ℝ => c0 + t))
  exact hc.differentiable (by norm_num : (∞ : ℕ∞ω) ≠ 0) 0



/-- A triple nested sum of a separated function factors into a product of sums. -/
lemma sum3_sep {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (f : A → ℝ) (g : B → ℝ) (h : C → ℝ) :
    (∑ a : A, ∑ b : B, ∑ c : C, f a * g b * h c) =
      (∑ a : A, f a) * (∑ b : B, g b) * (∑ c : C, h c) := by
  let S : ℝ := ∑ c : C, h c
  let G : ℝ := ∑ b : B, g b
  calc
    (∑ a : A, ∑ b : B, ∑ c : C, f a * g b * h c)
        = ∑ a : A, ∑ b : B, (f a * g b) * S := by
          apply Finset.sum_congr rfl
          intro a ha
          apply Finset.sum_congr rfl
          intro b hb
          rw [← Finset.mul_sum]
    _ = ∑ a : A, (f a * G) * S := by
          apply Finset.sum_congr rfl
          intro a ha
          calc
            (∑ b : B, (f a * g b) * S) = ∑ b : B, f a * (g b * S) := by
              apply Finset.sum_congr rfl
              intro b hb
              ring
            _ = f a * (∑ b : B, g b * S) := by
              rw [← Finset.mul_sum]
            _ = f a * (G * S) := by
              dsimp [G]
              rw [← Finset.sum_mul]
            _ = (f a * G) * S := by
              ring
    _ = (∑ a : A, f a) * G * S := by
          calc
            (∑ a : A, (f a * G) * S) = ∑ a : A, f a * (G * S) := by
              apply Finset.sum_congr rfl
              intro a ha
              ring
            _ = (∑ a : A, f a) * (G * S) := by
              rw [← Finset.sum_mul]
            _ = ((∑ a : A, f a) * G) * S := by
              ring
    _ = (∑ a : A, f a) * (∑ b : B, g b) * (∑ c : C, h c) := by
          dsimp [G, S]

lemma cellDir0 (ℓ : ℝ) (m : ℕ) (y : ℝ³) (a b d : Fin (m + 2)) :
    fderiv ℝ (cellCut ℓ m (a, (b, d))) y (kcStdBasis 0) =
      deriv (fun u : ℝ => axisFam rhoProfile ℓ m a u) (y 0) *
        axisFam rhoProfile ℓ m b (y 1) * axisFam rhoProfile ℓ m d (y 2) := by
  let C : ℝ := axisFam rhoProfile ℓ m b (y 1) * axisFam rhoProfile ℓ m d (y 2)
  have hcd : ContDiff ℝ ∞ (cellCut ℓ m (a, (b, d))) := by
    exact cellCut_contDiff ℓ m (a, (b, d))
  have hdiff : DifferentiableAt ℝ (cellCut ℓ m (a, (b, d))) y := by
    exact hcd.differentiable (by norm_num : (∞ : ℕ∞ω) ≠ 0) y
  have hconst_diff : DifferentiableAt ℝ (fun _ : ℝ => C) 0 := by
    exact (hasDerivAt_const (0 : ℝ) C).differentiableAt
  have hder_prod : deriv (fun t : ℝ => axisFam rhoProfile ℓ m a (y 0 + t) * C) 0 =
      deriv (fun t : ℝ => axisFam rhoProfile ℓ m a (y 0 + t)) 0 * C := by
    have hm := deriv_mul (axis_diff_shift ℓ m a (y 0)) hconst_diff
    simpa [deriv_const] using hm
  calc
    fderiv ℝ (cellCut ℓ m (a, (b, d))) y (kcStdBasis 0)
        = lineDeriv ℝ (cellCut ℓ m (a, (b, d))) y (kcStdBasis 0) := by
          rw [← DifferentiableAt.lineDeriv_eq_fderiv hdiff]
    _ = deriv (fun t : ℝ => cellCut ℓ m (a, (b, d)) (y + t • (kcStdBasis 0))) 0 := by
          rfl
    _ = deriv (fun t : ℝ => axisFam rhoProfile ℓ m a (y 0 + t) * C) 0 := by
          congr 1
          funext t
          dsimp [C, cellCut]
          simp [kcStdBasis]
          ring
    _ = deriv (fun u : ℝ => axisFam rhoProfile ℓ m a u) (y 0) * C := by
          rw [hder_prod, axis_deriv_shift]
    _ = deriv (fun u : ℝ => axisFam rhoProfile ℓ m a u) (y 0) *
          axisFam rhoProfile ℓ m b (y 1) * axisFam rhoProfile ℓ m d (y 2) := by
          dsimp [C]
          ring

lemma cellDir1 (ℓ : ℝ) (m : ℕ) (y : ℝ³) (a b d : Fin (m + 2)) :
    fderiv ℝ (cellCut ℓ m (a, (b, d))) y (kcStdBasis 1) =
      axisFam rhoProfile ℓ m a (y 0) *
        deriv (fun u : ℝ => axisFam rhoProfile ℓ m b u) (y 1) *
        axisFam rhoProfile ℓ m d (y 2) := by
  let C : ℝ := axisFam rhoProfile ℓ m a (y 0) * axisFam rhoProfile ℓ m d (y 2)
  have hcd : ContDiff ℝ ∞ (cellCut ℓ m (a, (b, d))) := by
    exact cellCut_contDiff ℓ m (a, (b, d))
  have hdiff : DifferentiableAt ℝ (cellCut ℓ m (a, (b, d))) y := by
    exact hcd.differentiable (by norm_num : (∞ : ℕ∞ω) ≠ 0) y
  have hconst_diff : DifferentiableAt ℝ (fun _ : ℝ => C) 0 := by
    exact (hasDerivAt_const (0 : ℝ) C).differentiableAt
  have hder_prod : deriv (fun t : ℝ => C * axisFam rhoProfile ℓ m b (y 1 + t)) 0 =
      C * deriv (fun t : ℝ => axisFam rhoProfile ℓ m b (y 1 + t)) 0 := by
    have hm := deriv_mul hconst_diff (axis_diff_shift ℓ m b (y 1))
    simpa [deriv_const] using hm
  calc
    fderiv ℝ (cellCut ℓ m (a, (b, d))) y (kcStdBasis 1)
        = lineDeriv ℝ (cellCut ℓ m (a, (b, d))) y (kcStdBasis 1) := by
          rw [← DifferentiableAt.lineDeriv_eq_fderiv hdiff]
    _ = deriv (fun t : ℝ => cellCut ℓ m (a, (b, d)) (y + t • (kcStdBasis 1))) 0 := by
          rfl
    _ = deriv (fun t : ℝ => C * axisFam rhoProfile ℓ m b (y 1 + t)) 0 := by
          congr 1
          funext t
          dsimp [C, cellCut]
          simp [kcStdBasis]
          ring
    _ = C * deriv (fun u : ℝ => axisFam rhoProfile ℓ m b u) (y 1) := by
          rw [hder_prod, axis_deriv_shift]
    _ = axisFam rhoProfile ℓ m a (y 0) *
          deriv (fun u : ℝ => axisFam rhoProfile ℓ m b u) (y 1) *
          axisFam rhoProfile ℓ m d (y 2) := by
          dsimp [C]
          ring

lemma cellDir2 (ℓ : ℝ) (m : ℕ) (y : ℝ³) (a b d : Fin (m + 2)) :
    fderiv ℝ (cellCut ℓ m (a, (b, d))) y (kcStdBasis 2) =
      axisFam rhoProfile ℓ m a (y 0) *
        axisFam rhoProfile ℓ m b (y 1) *
        deriv (fun u : ℝ => axisFam rhoProfile ℓ m d u) (y 2) := by
  let C : ℝ := axisFam rhoProfile ℓ m a (y 0) * axisFam rhoProfile ℓ m b (y 1)
  have hcd : ContDiff ℝ ∞ (cellCut ℓ m (a, (b, d))) := by
    exact cellCut_contDiff ℓ m (a, (b, d))
  have hdiff : DifferentiableAt ℝ (cellCut ℓ m (a, (b, d))) y := by
    exact hcd.differentiable (by norm_num : (∞ : ℕ∞ω) ≠ 0) y
  have hconst_diff : DifferentiableAt ℝ (fun _ : ℝ => C) 0 := by
    exact (hasDerivAt_const (0 : ℝ) C).differentiableAt
  have hder_prod : deriv (fun t : ℝ => C * axisFam rhoProfile ℓ m d (y 2 + t)) 0 =
      C * deriv (fun t : ℝ => axisFam rhoProfile ℓ m d (y 2 + t)) 0 := by
    have hm := deriv_mul hconst_diff (axis_diff_shift ℓ m d (y 2))
    simpa [deriv_const] using hm
  calc
    fderiv ℝ (cellCut ℓ m (a, (b, d))) y (kcStdBasis 2)
        = lineDeriv ℝ (cellCut ℓ m (a, (b, d))) y (kcStdBasis 2) := by
          rw [← DifferentiableAt.lineDeriv_eq_fderiv hdiff]
    _ = deriv (fun t : ℝ => cellCut ℓ m (a, (b, d)) (y + t • (kcStdBasis 2))) 0 := by
          rfl
    _ = deriv (fun t : ℝ => C * axisFam rhoProfile ℓ m d (y 2 + t)) 0 := by
          congr 1
          funext t
          dsimp [C, cellCut]
          simp [kcStdBasis]
    _ = C * deriv (fun u : ℝ => axisFam rhoProfile ℓ m d u) (y 2) := by
          rw [hder_prod, axis_deriv_shift]
    _ = axisFam rhoProfile ℓ m a (y 0) *
          axisFam rhoProfile ℓ m b (y 1) *
          deriv (fun u : ℝ => axisFam rhoProfile ℓ m d u) (y 2) := by
          dsimp [C]


/-- Exact partition of unity on the cube: `Σ_c χ_c(y)² = 1` for
`0 ≤ y_k ≤ m·ℓ`. -/
lemma cellCut_pu {ℓ : ℝ} (hℓ : 0 < ℓ) (m : ℕ) {y : ℝ³}
    (hy : ∀ k : Fin 3, 0 ≤ y k ∧ y k ≤ (m : ℝ) * ℓ) :
    (∑ c : CellIdx m, (cellCut ℓ m c y) ^ 2) = 1 := by
  have h0 : (∑ j : Fin (m + 2), (axisFam rhoProfile ℓ m j (y 0)) ^ 2) = 1 := by
    exact axis_pu profile_supp profile_pu hℓ (hy 0).1 (hy 0).2
  have h1 : (∑ j : Fin (m + 2), (axisFam rhoProfile ℓ m j (y 1)) ^ 2) = 1 := by
    exact axis_pu profile_supp profile_pu hℓ (hy 1).1 (hy 1).2
  have h2 : (∑ j : Fin (m + 2), (axisFam rhoProfile ℓ m j (y 2)) ^ 2) = 1 := by
    exact axis_pu profile_supp profile_pu hℓ (hy 2).1 (hy 2).2
  calc
    (∑ c : CellIdx m, (cellCut ℓ m c y) ^ 2)
        = ∑ a : Fin (m + 2), ∑ b : Fin (m + 2), ∑ d : Fin (m + 2),
            (cellCut ℓ m (a, (b, d)) y) ^ 2 := by
          rw [Fintype.sum_prod_type]
          apply Finset.sum_congr rfl
          intro a ha
          exact Fintype.sum_prod_type (f := fun bc : (Fin (m + 2) × Fin (m + 2)) =>
            (cellCut ℓ m (a, bc) y) ^ 2)
    _ = ∑ a : Fin (m + 2), ∑ b : Fin (m + 2), ∑ d : Fin (m + 2),
            (axisFam rhoProfile ℓ m a (y 0)) ^ 2 * (axisFam rhoProfile ℓ m b (y 1)) ^ 2 *
              (axisFam rhoProfile ℓ m d (y 2)) ^ 2 := by
          apply Finset.sum_congr rfl
          intro a ha
          apply Finset.sum_congr rfl
          intro b hb
          apply Finset.sum_congr rfl
          intro d hd
          unfold cellCut
          ring
    _ = 1 := by
      rw [sum3_sep]
      rw [h0, h1, h2]
      ring

/-- Per-coordinate error density: for direction `k`, `Σ_c (∂_k χ_c(y))² ≤ 2A²/ℓ²`. -/
lemma cell_partial_axis_sum_le {ℓ A : ℝ} (hℓ : 0 < ℓ) (hA0 : 0 ≤ A)
    (hA : ∀ t : ℝ, |deriv rhoProfile t| ≤ A) (m : ℕ) {y : ℝ³} (k : Fin 3)
    (hy : ∀ k : Fin 3, 0 ≤ y k ∧ y k ≤ (m : ℝ) * ℓ) :
    (∑ c : CellIdx m, (fderiv ℝ (cellCut ℓ m c) y (kcStdBasis k)) ^ 2) ≤
      (2 * A ^ 2) / ℓ ^ 2 := by
  have hpu0 : (∑ j : Fin (m + 2), (axisFam rhoProfile ℓ m j (y 0)) ^ 2) = 1 := by
    exact axis_pu profile_supp profile_pu hℓ (hy 0).1 (hy 0).2
  have hpu1 : (∑ j : Fin (m + 2), (axisFam rhoProfile ℓ m j (y 1)) ^ 2) = 1 := by
    exact axis_pu profile_supp profile_pu hℓ (hy 1).1 (hy 1).2
  have hpu2 : (∑ j : Fin (m + 2), (axisFam rhoProfile ℓ m j (y 2)) ^ 2) = 1 := by
    exact axis_pu profile_supp profile_pu hℓ (hy 2).1 (hy 2).2
  fin_cases k
  · calc
    (∑ c : CellIdx m, (fderiv ℝ (cellCut ℓ m c) y (kcStdBasis 0)) ^ 2)
        = ∑ a : Fin (m + 2), ∑ b : Fin (m + 2), ∑ q : Fin (m + 2),
            (fderiv ℝ (cellCut ℓ m (a, (b, q))) y (kcStdBasis 0)) ^ 2 := by
          rw [Fintype.sum_prod_type]
          apply Finset.sum_congr rfl
          intro a ha
          exact Fintype.sum_prod_type (f := fun p : Fin (m + 2) × Fin (m + 2) =>
            (fderiv ℝ (cellCut ℓ m (a, p)) y (kcStdBasis 0)) ^ 2)
    _ = ∑ a : Fin (m + 2), ∑ b : Fin (m + 2), ∑ q : Fin (m + 2),
            (deriv (fun u : ℝ => axisFam rhoProfile ℓ m a u) (y 0)) ^ 2 *
            (axisFam rhoProfile ℓ m b (y 1)) ^ 2 *
            (axisFam rhoProfile ℓ m q (y 2)) ^ 2 := by
          apply Finset.sum_congr rfl
          intro a ha
          apply Finset.sum_congr rfl
          intro b hb
          apply Finset.sum_congr rfl
          intro q hq
          rw [cellDir0]
          ring
    _ = (∑ a : Fin (m + 2), (deriv (fun u : ℝ => axisFam rhoProfile ℓ m a u) (y 0)) ^ 2) *
          (∑ b : Fin (m + 2), (axisFam rhoProfile ℓ m b (y 1)) ^ 2) *
          (∑ q : Fin (m + 2), (axisFam rhoProfile ℓ m q (y 2)) ^ 2) := by
          rw [sum3_sep]
    _ = ∑ a : Fin (m + 2), (deriv (fun u : ℝ => axisFam rhoProfile ℓ m a u) (y 0)) ^ 2 := by
          rw [hpu1, hpu2]
          ring
    _ ≤ (2 * A ^ 2) / ℓ ^ 2 := by
          exact axis_grad_sum_le profile_deriv_supp hA0 hA hℓ m (hy 0).1 (hy 0).2

  · calc
    (∑ c : CellIdx m, (fderiv ℝ (cellCut ℓ m c) y (kcStdBasis 1)) ^ 2)
        = ∑ a : Fin (m + 2), ∑ b : Fin (m + 2), ∑ q : Fin (m + 2),
            (fderiv ℝ (cellCut ℓ m (a, (b, q))) y (kcStdBasis 1)) ^ 2 := by
          rw [Fintype.sum_prod_type]
          apply Finset.sum_congr rfl
          intro a ha
          exact Fintype.sum_prod_type (f := fun p : Fin (m + 2) × Fin (m + 2) =>
            (fderiv ℝ (cellCut ℓ m (a, p)) y (kcStdBasis 1)) ^ 2)
    _ = ∑ a : Fin (m + 2), ∑ b : Fin (m + 2), ∑ q : Fin (m + 2),
            (axisFam rhoProfile ℓ m a (y 0)) ^ 2 *
            (deriv (fun u : ℝ => axisFam rhoProfile ℓ m b u) (y 1)) ^ 2 *
            (axisFam rhoProfile ℓ m q (y 2)) ^ 2 := by
          apply Finset.sum_congr rfl
          intro a ha
          apply Finset.sum_congr rfl
          intro b hb
          apply Finset.sum_congr rfl
          intro q hq
          rw [cellDir1]
          ring
    _ = (∑ a : Fin (m + 2), (axisFam rhoProfile ℓ m a (y 0)) ^ 2) *
          (∑ b : Fin (m + 2), (deriv (fun u : ℝ => axisFam rhoProfile ℓ m b u) (y 1)) ^ 2) *
          (∑ q : Fin (m + 2), (axisFam rhoProfile ℓ m q (y 2)) ^ 2) := by
          rw [sum3_sep]
    _ = ∑ b : Fin (m + 2), (deriv (fun u : ℝ => axisFam rhoProfile ℓ m b u) (y 1)) ^ 2 := by
          rw [hpu0, hpu2]
          ring
    _ ≤ (2 * A ^ 2) / ℓ ^ 2 := by
          exact axis_grad_sum_le profile_deriv_supp hA0 hA hℓ m (hy 1).1 (hy 1).2

  · calc
    (∑ c : CellIdx m, (fderiv ℝ (cellCut ℓ m c) y (kcStdBasis 2)) ^ 2)
        = ∑ a : Fin (m + 2), ∑ b : Fin (m + 2), ∑ q : Fin (m + 2),
            (fderiv ℝ (cellCut ℓ m (a, (b, q))) y (kcStdBasis 2)) ^ 2 := by
          rw [Fintype.sum_prod_type]
          apply Finset.sum_congr rfl
          intro a ha
          exact Fintype.sum_prod_type (f := fun p : Fin (m + 2) × Fin (m + 2) =>
            (fderiv ℝ (cellCut ℓ m (a, p)) y (kcStdBasis 2)) ^ 2)
    _ = ∑ a : Fin (m + 2), ∑ b : Fin (m + 2), ∑ q : Fin (m + 2),
            (axisFam rhoProfile ℓ m a (y 0)) ^ 2 *
            (axisFam rhoProfile ℓ m b (y 1)) ^ 2 *
            (deriv (fun u : ℝ => axisFam rhoProfile ℓ m q u) (y 2)) ^ 2 := by
          apply Finset.sum_congr rfl
          intro a ha
          apply Finset.sum_congr rfl
          intro b hb
          apply Finset.sum_congr rfl
          intro q hq
          rw [cellDir2]
          ring
    _ = (∑ a : Fin (m + 2), (axisFam rhoProfile ℓ m a (y 0)) ^ 2) *
          (∑ b : Fin (m + 2), (axisFam rhoProfile ℓ m b (y 1)) ^ 2) *
          (∑ q : Fin (m + 2), (deriv (fun u : ℝ => axisFam rhoProfile ℓ m q u) (y 2)) ^ 2) := by
          rw [sum3_sep]
    _ = ∑ q : Fin (m + 2), (deriv (fun u : ℝ => axisFam rhoProfile ℓ m q u) (y 2)) ^ 2 := by
          rw [hpu0, hpu1]
          ring
    _ ≤ (2 * A ^ 2) / ℓ ^ 2 := by
          exact axis_grad_sum_le profile_deriv_supp hA0 hA hℓ m (hy 2).1 (hy 2).2

/-- The total error density over the three directions:
`Σ_c Σ_k (∂_k χ_c(y))² ≤ 6A²/ℓ²`. -/
lemma cell_partial_sq_sum_le {ℓ A : ℝ} (hℓ : 0 < ℓ) (hA0 : 0 ≤ A)
    (hA : ∀ t : ℝ, |deriv rhoProfile t| ≤ A) (m : ℕ) {y : ℝ³}
    (hy : ∀ k : Fin 3, 0 ≤ y k ∧ y k ≤ (m : ℝ) * ℓ) :
    (∑ c : CellIdx m, ∑ k : Fin 3, (fderiv ℝ (cellCut ℓ m c) y (kcStdBasis k)) ^ 2) ≤
      (6 * A ^ 2) / ℓ ^ 2 := by
  calc
    (∑ c : CellIdx m, ∑ k : Fin 3, (fderiv ℝ (cellCut ℓ m c) y (kcStdBasis k)) ^ 2)
        = ∑ k : Fin 3, ∑ c : CellIdx m, (fderiv ℝ (cellCut ℓ m c) y (kcStdBasis k)) ^ 2 := by
          rw [Finset.sum_comm]
    _ ≤ ∑ k : Fin 3, (2 * A ^ 2) / ℓ ^ 2 := by
          exact Finset.sum_le_sum (fun k hk =>
            cell_partial_axis_sum_le (hℓ := hℓ) (hA0 := hA0) (hA := hA) (m := m) (k := k) hy)
    _ = (6 * A ^ 2) / ℓ ^ 2 := by
          simp
          ring


end BoseGases

end Submission
