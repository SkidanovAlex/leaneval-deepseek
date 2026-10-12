import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseFixGlue.Residuals
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixGlue.Pot.abs_potWordU_le` — the pointwise bound for `potWordU`

`potWordU N v (g₀ v h) ℓ μ u x` is the *multiplicative* part of FS `eq:Def_HB`,
`−μ·Σ_i ∫_y w_{1,u}(x_i,y)dy + Σ_{i<j} w_u(x_i,x_j)`, and this module isolates the
elementary pointwise bound needed for its `u`-integrability and domination arguments:

`|potWordU …| ≤ |μ|·(N·(2·chiSup²·∫|g₀|)) + chiSup²·Σ_{i<j} 2|v(x_i−x_j)|`.

The two per-term inputs are proved in `Work.BoseBox.abs_potBracketG_le` (the same bound
for the *un-summed* bracket `potBracketG`, which uses the `pairSet` Finset spelling of the
pair sum):

* `Work.BoseBox.abs_potBr_le` — `|∫_y w_{1,u}(a,y)dy| ≤ 2·chiSup²·∫|g₀|`, from the
  pointwise factorisation of `wLoc` into two window factors `|χ_u| ≤ chiSup` and the
  quotient bound `|wScaled ℓ g| ≤ 2|g|` (FS's regime `0 < ℓ`, `R ≤ ℓ·r₀`, `(χ⋆χ) ≥ 1/2`
  on `‖z‖ ≤ r₀`, plus the support of the numerator), followed by
  `abs_integral_le_integral_abs`, `integral_mono` and translation invariance;
* `Work.BoseBox.abs_wLoc_pair_le` — `|wLoc ℓ v u a b| ≤ chiSup²·(2|v(a−b)|)`, the same
  pointwise factorisation with numerator `v`.

The only thing this module adds is the *sum* over the corpus's index spelling for the
pairs, `{ij : Fin N × Fin N // ij.1 < ij.2}` (a subtype, not the `pairSet` Finset),
together with `Finset.abs_sum_le_sum_abs`, `Finset.sum_le_sum`, `Finset.mul_sum` and
`abs_add_le` for the assembly.
-/

noncomputable section

open scoped Real BigOperators

namespace Work.BoseFixGlue.Pot

open Work.BoseBox

set_option autoImplicit false

theorem abs_potWordU_le {N : ℕ} {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {R r₀ ℓ μ : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hC : ∀ z : EuclideanSpace ℝ (Fin 3), ‖z‖ ≤ r₀ →
      1 / 2 ≤ Submission.BoseGases.conv3 Submission.BoseGases.chi Submission.BoseGases.chi z)
    (hℓ : 0 < ℓ) (hRℓ : R ≤ ℓ * r₀) (u : EuclideanSpace ℝ (Fin 3))
    (x : Submission.BoseGases.X N) :
    |Work.BoseKinLoc.potWordU N v (Submission.BoseGases.g0 v h) ℓ μ u x| ≤
      |μ| * ((N : ℝ) * (2 * Work.BoseBox.chiSup ^ 2 * Work.BoseBox.g0mass v h))
        + Work.BoseBox.chiSup ^ 2 *
            ∑ ij : {ij : Fin N × Fin N // ij.1 < ij.2}, (2 * |v (x ij.1.1 - x ij.1.2)|) := by
  -- per-particle fibre bound
  have hBr : ∀ i : Fin N,
      |potBr ℓ (Submission.BoseGases.g0 v h) u (x i)| ≤ 2 * chiSup ^ 2 * g0mass v h :=
    fun i => abs_potBr_le hR hv_supp hC hℓ hRℓ u (x i)
  have hSum1 : |∑ i : Fin N, potBr ℓ (Submission.BoseGases.g0 v h) u (x i)|
      ≤ (N : ℝ) * (2 * chiSup ^ 2 * g0mass v h) := by
    calc |∑ i : Fin N, potBr ℓ (Submission.BoseGases.g0 v h) u (x i)|
        ≤ ∑ i : Fin N, |potBr ℓ (Submission.BoseGases.g0 v h) u (x i)| :=
          Finset.abs_sum_le_sum_abs
            (fun i : Fin N => potBr ℓ (Submission.BoseGases.g0 v h) u (x i)) Finset.univ
      _ ≤ ∑ _i : Fin N, (2 * chiSup ^ 2 * g0mass v h) :=
          Finset.sum_le_sum (fun i _ => hBr i)
      _ = (N : ℝ) * (2 * chiSup ^ 2 * g0mass v h) := by
          simp [Finset.sum_const, nsmul_eq_mul]
  -- per-pair bound, summed over the subtype spelling of the pairs
  have hPair :
      |∑ ij : {ij : Fin N × Fin N // ij.1 < ij.2},
          Submission.BoseGases.wLoc ℓ v u (x ij.1.1) (x ij.1.2)|
        ≤ chiSup ^ 2 *
            ∑ ij : {ij : Fin N × Fin N // ij.1 < ij.2},
              (2 * |v (x ij.1.1 - x ij.1.2)|) := by
    calc |∑ ij : {ij : Fin N × Fin N // ij.1 < ij.2},
            Submission.BoseGases.wLoc ℓ v u (x ij.1.1) (x ij.1.2)|
        ≤ ∑ ij : {ij : Fin N × Fin N // ij.1 < ij.2},
            |Submission.BoseGases.wLoc ℓ v u (x ij.1.1) (x ij.1.2)| :=
          Finset.abs_sum_le_sum_abs
            (fun ij : {ij : Fin N × Fin N // ij.1 < ij.2} =>
              Submission.BoseGases.wLoc ℓ v u (x ij.1.1) (x ij.1.2)) Finset.univ
      _ ≤ ∑ ij : {ij : Fin N × Fin N // ij.1 < ij.2},
            chiSup ^ 2 * (2 * |v (x ij.1.1 - x ij.1.2)|) :=
          Finset.sum_le_sum
            (fun ij _ => abs_wLoc_pair_le hv_supp hC hℓ hRℓ u (x ij.1.1) (x ij.1.2))
      _ = chiSup ^ 2 *
            ∑ ij : {ij : Fin N × Fin N // ij.1 < ij.2},
              (2 * |v (x ij.1.1 - x ij.1.2)|) := by
          rw [Finset.mul_sum]
  -- unfold `potWordU`
  have hbrk : Work.BoseKinLoc.potWordU N v (Submission.BoseGases.g0 v h) ℓ μ u x
      = -μ * (∑ i : Fin N, potBr ℓ (Submission.BoseGases.g0 v h) u (x i))
        + ∑ ij : {ij : Fin N × Fin N // ij.1 < ij.2},
            Submission.BoseGases.wLoc ℓ v u (x ij.1.1) (x ij.1.2) := rfl
  rw [hbrk]
  calc |(-μ) * (∑ i : Fin N, potBr ℓ (Submission.BoseGases.g0 v h) u (x i))
          + ∑ ij : {ij : Fin N × Fin N // ij.1 < ij.2},
              Submission.BoseGases.wLoc ℓ v u (x ij.1.1) (x ij.1.2)|
      ≤ |(-μ) * (∑ i : Fin N, potBr ℓ (Submission.BoseGases.g0 v h) u (x i))|
          + |∑ ij : {ij : Fin N × Fin N // ij.1 < ij.2},
              Submission.BoseGases.wLoc ℓ v u (x ij.1.1) (x ij.1.2)| := abs_add_le _ _
    _ = |μ| * |∑ i : Fin N, potBr ℓ (Submission.BoseGases.g0 v h) u (x i)|
          + |∑ ij : {ij : Fin N × Fin N // ij.1 < ij.2},
              Submission.BoseGases.wLoc ℓ v u (x ij.1.1) (x ij.1.2)| := by
          rw [abs_mul, abs_neg]
    _ ≤ |μ| * ((N : ℝ) * (2 * chiSup ^ 2 * g0mass v h))
          + chiSup ^ 2 *
              ∑ ij : {ij : Fin N × Fin N // ij.1 < ij.2},
                (2 * |v (x ij.1.1 - x ij.1.2)|) :=
          add_le_add (mul_le_mul_of_nonneg_left hSum1 (abs_nonneg μ)) hPair

end Work.BoseFixGlue.Pot
