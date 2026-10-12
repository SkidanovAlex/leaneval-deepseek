import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Submission.Work.BoseKinLoc.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.chiSqAux` — the pointwise product rule behind `chiSq_dirichlet_le_fsT`

The target `Work.BoseBoxFock.chiSq_dirichlet_le_fsT` bounds the *windowed Dirichlet word* of an
arbitrary smooth one-body state `ψ` by the localised word `fsT ℓ d s εT b 0 ψ` plus a mass term.

The one elementary input is the product rule for the windowed mean-free state.  Write
`χ := chiScale ℓ` (the corpus bump, `bsWin ℓ 0` up to definitional unfolding) and let
`m : ℝ` be any constant; then for every coordinate `j`,

    `χ(z)·∂_jψ(z) = ∂_j(χ·(ψ − m))(z) − ∂_jχ(z)·(ψ(z) − m)`,

because `∂_j(χ·(ψ−m)) = ∂_jχ·(ψ−m) + χ·∂_jψ`.  Squaring and using `(a−b)² ≤ 2a² + 2b²` gives
the pointwise inequality

    `χ(z)²·(∂_jψ(z))² ≤ 2(∂_j(χ·(ψ−m))(z))² + 2(∂_jχ(z))²(ψ(z) − m)²`,

and summing over `j = 0,1,2`:

    `χ(z)²·Σ_j(∂_jψ(z))² ≤ 2·Σ_j(∂_j(χ·(ψ−m))(z))² + 2·(Σ_j(∂_jχ(z))²)·(ψ(z) − m)²`.

The right-hand side is integrated against the *unrestricted* volume in the consumer: the first sum
is exactly the Dirichlet form `bsOneBody ℓ (·)² 0 ψ` of `bsOneBody_eq_dirichlet`, and the second is
controlled by the mass of the state on the box.

`m` is kept as a free real: the application takes `m = bsMean ℓ 0 ψ` (the box mean), but the
identity itself never uses that.
-/

noncomputable section

open MeasureTheory
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseBoxFock

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The anchored big-box window is the corpus bump: `bsWin ℓ 0 = chiScale ℓ`. -/
theorem bsWin_zero_eq_chiScale (ℓ : ℝ) :
    Work.BSKinetic.bsWin ℓ 0 = Submission.BoseGases.chiScale ℓ := by
  funext x
  simp [Work.BSKinetic.bsWin]

/-- **The product rule, rearranged.**  For smooth `ψ`, every constant `m`, every coordinate `j`
and every point `z`,

    `χ(z)·∂_jψ(z) = ∂_j(χ·(ψ − m))(z) − ∂_jχ(z)·(ψ(z) − m)`.

This is `∂_j(χ(ψ−m)) = ∂_jχ·(ψ−m) + χ·∂_jψ` solved for `χ·∂_jψ`. -/
theorem chiScale_mul_fderiv_eq_sub {ℓ m : ℝ} (hℓ : 0 < ℓ) {ψ : ℝ³ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (j : Fin 3) (z : ℝ³) :
    Submission.BoseGases.chiScale ℓ z * (fderiv ℝ ψ z (EuclideanSpace.single j (1 : ℝ)))
      = (fderiv ℝ (fun y : ℝ³ => Submission.BoseGases.chiScale ℓ y * (ψ y - m)) z
            (EuclideanSpace.single j (1 : ℝ)))
        - (fderiv ℝ (Submission.BoseGases.chiScale ℓ) z (EuclideanSpace.single j (1 : ℝ)))
            * (ψ z - m) := by
  have hχd : DifferentiableAt ℝ (Submission.BoseGases.chiScale ℓ) z :=
    (Submission.BoseGases.chiScale_contDiff (ne_of_gt hℓ)).contDiffAt.differentiableAt (by simp)
  have hQd : DifferentiableAt ℝ (fun y : ℝ³ => ψ y - m) z :=
    ((hψ.contDiffAt).differentiableAt (by simp)).sub_const _
  have hmul := fderiv_mul hχd hQd
  have hfun : (Submission.BoseGases.chiScale ℓ * fun y : ℝ³ => ψ y - m)
      = fun y : ℝ³ => Submission.BoseGases.chiScale ℓ y * (ψ y - m) := by
    funext y; rfl
  rw [hfun] at hmul
  have happ := congrArg (fun (L : ℝ³ →L[ℝ] ℝ) => L (EuclideanSpace.single j (1 : ℝ))) hmul
  simp only [add_apply, smul_apply, smul_eq_mul] at happ
  rw [fderiv_sub_const] at happ
  rw [happ]
  ring

/-- **The pointwise square inequality, one coordinate.**  For smooth `ψ`,

    `χ(z)²·(∂_jψ(z))² ≤ 2·(∂_j(χ·(ψ − m))(z))² + 2·(∂_jχ(z))²·(ψ(z) − m)²`. -/
theorem chiScale_sq_mul_fderiv_sq_le {ℓ m : ℝ} (hℓ : 0 < ℓ) {ψ : ℝ³ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (j : Fin 3) (z : ℝ³) :
    (Submission.BoseGases.chiScale ℓ z) ^ 2 * (fderiv ℝ ψ z (EuclideanSpace.single j (1 : ℝ))) ^ 2
      ≤ 2 * (fderiv ℝ (fun y : ℝ³ => Submission.BoseGases.chiScale ℓ y * (ψ y - m)) z
              (EuclideanSpace.single j (1 : ℝ))) ^ 2
        + 2 * (fderiv ℝ (Submission.BoseGases.chiScale ℓ) z (EuclideanSpace.single j (1 : ℝ))) ^ 2
            * (ψ z - m) ^ 2 := by
  have hkey := chiScale_mul_fderiv_eq_sub (m := m) hℓ hψ j z
  set a := (fderiv ℝ (fun y : ℝ³ => Submission.BoseGases.chiScale ℓ y * (ψ y - m)) z)
    (EuclideanSpace.single j (1 : ℝ)) with ha
  set b := (fderiv ℝ (Submission.BoseGases.chiScale ℓ) z (EuclideanSpace.single j (1 : ℝ)))
    * (ψ z - m) with hb
  have hgoal : (Submission.BoseGases.chiScale ℓ z
        * (fderiv ℝ ψ z (EuclideanSpace.single j (1 : ℝ)))) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
    rw [hkey]
    nlinarith [sq_nonneg (a + b)]
  calc (Submission.BoseGases.chiScale ℓ z) ^ 2
        * (fderiv ℝ ψ z (EuclideanSpace.single j (1 : ℝ))) ^ 2
      = (Submission.BoseGases.chiScale ℓ z
          * (fderiv ℝ ψ z (EuclideanSpace.single j (1 : ℝ)))) ^ 2 := by ring
    _ ≤ 2 * a ^ 2 + 2 * b ^ 2 := hgoal
    _ = 2 * (fderiv ℝ (fun y : ℝ³ => Submission.BoseGases.chiScale ℓ y * (ψ y - m)) z
              (EuclideanSpace.single j (1 : ℝ))) ^ 2
        + 2 * (fderiv ℝ (Submission.BoseGases.chiScale ℓ) z (EuclideanSpace.single j (1 : ℝ))) ^ 2
            * (ψ z - m) ^ 2 := by rw [ha, hb]; ring

/-- **The pointwise square inequality, summed over the three coordinates.** -/
theorem chiScale_sq_mul_sum_fderiv_le {ℓ m : ℝ} (hℓ : 0 < ℓ) {ψ : ℝ³ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (z : ℝ³) :
    (Submission.BoseGases.chiScale ℓ z) ^ 2
        * (∑ j : Fin 3, (fderiv ℝ ψ z (EuclideanSpace.single j (1 : ℝ))) ^ 2)
      ≤ 2 * (∑ j : Fin 3, (fderiv ℝ (fun y : ℝ³ =>
                Submission.BoseGases.chiScale ℓ y * (ψ y - m)) z
              (EuclideanSpace.single j (1 : ℝ))) ^ 2)
        + 2 * ((∑ j : Fin 3, (fderiv ℝ (Submission.BoseGases.chiScale ℓ) z
              (EuclideanSpace.single j (1 : ℝ))) ^ 2) * (ψ z - m) ^ 2) := by
  have hpt : ∀ j : Fin 3,
      (Submission.BoseGases.chiScale ℓ z) ^ 2
          * (fderiv ℝ ψ z (EuclideanSpace.single j (1 : ℝ))) ^ 2
        ≤ 2 * (fderiv ℝ (fun y : ℝ³ => Submission.BoseGases.chiScale ℓ y * (ψ y - m)) z
                (EuclideanSpace.single j (1 : ℝ))) ^ 2
          + 2 * (fderiv ℝ (Submission.BoseGases.chiScale ℓ) z
                (EuclideanSpace.single j (1 : ℝ))) ^ 2 * (ψ z - m) ^ 2 :=
    fun j => chiScale_sq_mul_fderiv_sq_le hℓ hψ j z
  calc (Submission.BoseGases.chiScale ℓ z) ^ 2
        * (∑ j : Fin 3, (fderiv ℝ ψ z (EuclideanSpace.single j (1 : ℝ))) ^ 2)
      = ∑ j : Fin 3, (Submission.BoseGases.chiScale ℓ z) ^ 2
          * (fderiv ℝ ψ z (EuclideanSpace.single j (1 : ℝ))) ^ 2 := by
        rw [Finset.mul_sum]
    _ ≤ ∑ j : Fin 3, (2 * (fderiv ℝ (fun y : ℝ³ =>
                Submission.BoseGases.chiScale ℓ y * (ψ y - m)) z
                (EuclideanSpace.single j (1 : ℝ))) ^ 2
          + 2 * (fderiv ℝ (Submission.BoseGases.chiScale ℓ) z
                (EuclideanSpace.single j (1 : ℝ))) ^ 2 * (ψ z - m) ^ 2) :=
        Finset.sum_le_sum (fun j _ => hpt j)
    _ = 2 * (∑ j : Fin 3, (fderiv ℝ (fun y : ℝ³ =>
                Submission.BoseGases.chiScale ℓ y * (ψ y - m)) z
                (EuclideanSpace.single j (1 : ℝ))) ^ 2)
        + 2 * ((∑ j : Fin 3, (fderiv ℝ (Submission.BoseGases.chiScale ℓ) z
                (EuclideanSpace.single j (1 : ℝ))) ^ 2) * (ψ z - m) ^ 2) := by
        rw [Finset.sum_add_distrib]
        congr 1
        · rw [Finset.mul_sum]
        · rw [← Finset.sum_mul, ← Finset.mul_sum]
          ring

end Work.BoseBoxFock
