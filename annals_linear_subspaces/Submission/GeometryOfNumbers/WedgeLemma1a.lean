import Mathlib
import Submission.Bridge.ONGraphLower
import Submission.GeometryOfNumbers.WedgeGeneralE1
import Submission.Commons.LinearAlgebra.Alternating.iMulti_proportional_of_span_eq
import Submission.Commons.LinearAlgebra.ExteriorPower.iMulti_linearIndependent_of_ne_zero

/-!
# Lemma 1(a), converse direction, for general pure tensors (coordinate model)

For a `k`-plane `V = span (range u)` (`u` independent) with `V ⊓ x₀ᗮ = ⊥`
(`x₀ = modelX ℓ`), let `w = ιMulti u` with block norms `X = ‖w₀‖`, `Y = ‖w₁‖` and
`δ = planeResidual V x₀` the operator-norm distance.  Then, for planes close to `x₀`
(`δ ≤ 1/2`), the graph offsets (from the orthonormal graph representation `u = λ(e + coff)`
of `exists_graph_rep`) are controlled by `δ`: each `‖coff i‖ ≤ 2δ` (`ONGraphLower`), hence
`Y/X = ‖ιMulti(e+coff)₁‖ ≤ 2√k · δ`:

`pureTensor_blockRatio_le_planeResidual`:  `‖w₁‖/‖w₀‖ ≤ 2√k · δ` when `δ ≤ 1/2`.

This is the pure-tensor form of the paper's Lemma 1(a) (converse: the block ratio is at most
a constant times the distance); together with `WedgeHigherBlocks.pureTensor_flow_le` it turns
distance-smallness of a rational plane into the cone hypothesis `b·‖w₁‖ ≤ a·‖w₀‖` needed by
the flow.
-/

noncomputable section

open Module exteriorPower InnerProductGeometry Real
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false

open Submission.ExteriorCoordinates
open Submission.DiagonalFlow

namespace Submission.WedgeLemma1a

variable {d : ℕ}

/-- **Lemma 1(a), converse (pure tensor form)**: for an independent family `u : Fin k → ℝᵈ`
spanning a plane transverse to `x₀ᗮ`, with distance `δ = planeResidual V x₀ ≤ 1/2`, the block
ratio of the pure tensor `w = ιMulti u` is at most `2√k · δ`. -/
theorem pureTensor_blockRatio_le_planeResidual {d k : ℕ} (ℓ : ℕ) (hk : 0 < k)
    (u : Fin k → RD d) (hu : LinearIndependent ℝ u)
    (hbot : (Submodule.span ℝ (Set.range u)) ⊓ (Submission.WedgeBlocks.modelX ℓ)ᗮ = ⊥)
    (hδ12 : Submission.ProjectionDistance.planeResidual (Submodule.span ℝ (Set.range u))
        (Submission.WedgeBlocks.modelX ℓ) ≤ 1 / 2) :
    ‖blockElem (d := d) (k := k) (ℓ := ℓ) (exteriorPower.ιMulti ℝ k u) 1‖ /
      ‖blockElem (d := d) (k := k) (ℓ := ℓ) (exteriorPower.ιMulti ℝ k u) 0‖ ≤
      (2 : ℝ) * Real.sqrt (k : ℝ) *
        Submission.ProjectionDistance.planeResidual (Submodule.span ℝ (Set.range u))
          (Submission.WedgeBlocks.modelX ℓ) := by
  classical
  let V : Submodule ℝ (RD d) := Submodule.span ℝ (Set.range u)
  let w : WK d k := exteriorPower.ιMulti ℝ k u
  let δ : ℝ := Submission.ProjectionDistance.planeResidual V (Submission.WedgeBlocks.modelX ℓ)
  rcases Submission.WedgeGeneralE1.exists_graph_rep (d := d) (k := k) ℓ hk u hu hbot with
    ⟨e, coff, he_ON, he_x0, coff_orth, hspan⟩
  let g : Fin k → RD d := fun j => e j + coff j
  let w' : WK d k := exteriorPower.ιMulti ℝ k g
  have hδ12' : δ ≤ 1 / 2 := by simpa [δ, V] using hδ12
  -- V = ONGraph.graphSubspace e coff
  have hVgraph : V = Submission.Bridge.ONGraph.graphSubspace e coff := by
    dsimp [V, Submission.Bridge.ONGraph.graphSubspace]
    rw [← hspan]
    rfl
  have hδgraph : δ = Submission.ProjectionDistance.planeResidual
      (Submission.Bridge.ONGraph.graphSubspace e coff) (Submission.WedgeBlocks.modelX ℓ) := by
    dsimp [δ]
    rw [hVgraph]
  -- w' ≠ 0 (block-0 = ιMulti e is a unit vector), hence g is linearly independent
  have hw'0 : blockElem (d := d) (k := k) (ℓ := ℓ) w' 0 = exteriorPower.ιMulti ℝ k e := by
    dsimp [w', g]
    exact Submission.WedgeBlocks.blockElem_zero_of_graph (d := d) (k := k) ℓ e coff he_x0 coff_orth
  have hw'ne : w' ≠ 0 := by
    intro hz
    have h0 : blockElem (d := d) (k := k) (ℓ := ℓ) w' 0 = 0 := by rw [hz]; simp
    rw [hw'0] at h0
    have hn : ‖exteriorPower.ιMulti ℝ k e‖ ≠ 0 := by
      rw [Commons.Analysis.InnerProductSpace.norm_iMulti_orthonormal e he_ON hk]
      norm_num
    exact hn (by simp [h0])
  have hgLI : LinearIndependent ℝ g :=
    Commons.LinearAlgebra.ExteriorPower.iMulti_linearIndependent_of_ne_zero g hw'ne
  have hspan' : Submodule.span ℝ (Set.range u) = Submodule.span ℝ (Set.range g) := by
    simpa [g] using hspan.symm
  rcases Commons.LinearAlgebra.Alternating.iMulti_proportional_of_span_eq
      (𝕜 := ℝ) (M := RD d) u g hu hgLI hspan' with ⟨lam, hlam0, hprop⟩
  have hprop_j : ∀ j : ℕ, blockElem (d := d) (k := k) (ℓ := ℓ) w j =
      lam • blockElem (d := d) (k := k) (ℓ := ℓ) w' j := by
    intro j
    have hc := congrArg (fun z : WK d k => blockElem (d := d) (k := k) (ℓ := ℓ) z j) hprop
    simpa [w, w', blockElem_smul] using hc
  have hn (j : ℕ) : ‖blockElem (d := d) (k := k) (ℓ := ℓ) w j‖ =
      |lam| * ‖blockElem (d := d) (k := k) (ℓ := ℓ) w' j‖ := by
    calc
      ‖blockElem (d := d) (k := k) (ℓ := ℓ) w j‖
          = ‖lam • blockElem (d := d) (k := k) (ℓ := ℓ) w' j‖ := by rw [hprop_j j]
      _ = |lam| * ‖blockElem (d := d) (k := k) (ℓ := ℓ) w' j‖ := by
            rw [norm_smul, Real.norm_eq_abs]
  -- offsets are small: ‖coff j‖ ≤ 2δ
  have hcoff : ∀ j : Fin k, ‖coff j‖ ≤ 2 * δ := by
    intro j
    have hg := Submission.Bridge.ONGraph.graph_residual_le_two_planeResidual
      (E := RD d) (x := Submission.WedgeBlocks.modelX ℓ) (k := k) hk e coff he_ON he_x0 coff_orth j
      (by simpa [hδgraph] using hδ12')
    simpa [hδgraph] using hg
  have hd0 : 0 ≤ δ := by
    have hpos : 0 < ‖Submission.Bridge.ONGraph.graphVec e coff ⟨0, hk⟩‖ := by
      exact norm_pos_iff.mpr (Submission.Bridge.ONGraph.graphVec_ne_zero (x := Submission.WedgeBlocks.modelX ℓ)
        e coff he_ON he_x0 coff_orth ⟨0, hk⟩)
    have hdiv0 : 0 ≤ ‖coff ⟨0, hk⟩‖ / ‖Submission.Bridge.ONGraph.graphVec e coff ⟨0, hk⟩‖ :=
      div_nonneg (norm_nonneg (coff ⟨0, hk⟩)) (le_of_lt hpos)
    have hdivle : ‖coff ⟨0, hk⟩‖ / ‖Submission.Bridge.ONGraph.graphVec e coff ⟨0, hk⟩‖ ≤ δ := by
      have hg := Submission.Bridge.ONGraph.planeResidual_ge_unit_graphVec
        (E := RD d) (x := Submission.WedgeBlocks.modelX ℓ) (k := k) e coff he_ON he_x0 coff_orth ⟨0, hk⟩
      rw [hδgraph]
      simpa using hg
    exact le_trans hdiv0 hdivle
  -- ‖w'₁‖² = Σ‖coff‖² ≤ 4kδ²
  have hb1sq' : ‖blockElem (d := d) (k := k) (ℓ := ℓ) w' 1‖ ^ 2 =
      (Finset.univ : Finset (Fin k)).sum (fun j => ‖coff j‖ ^ 2) := by
    have hsq := Submission.WedgeBlocks.blockElem_one_of_graph_normSq (d := d) (k := k) ℓ e coff
      he_ON he_x0 coff_orth
    simpa [w', g] using hsq
  have hsum : (Finset.univ : Finset (Fin k)).sum (fun j => ‖coff j‖ ^ 2) ≤
      4 * (k : ℝ) * δ ^ 2 := by
    calc
      (Finset.univ : Finset (Fin k)).sum (fun j => ‖coff j‖ ^ 2)
          ≤ (Finset.univ : Finset (Fin k)).sum (fun _ : Fin k => (2 * δ) ^ 2) := by
              apply Finset.sum_le_sum
              intro j hj
              have hc0 : 0 ≤ ‖coff j‖ := norm_nonneg _
              have h2d0 : 0 ≤ 2 * δ := by positivity
              exact (sq_le_sq₀ hc0 h2d0).mpr (hcoff j)
      _ = (k : ℝ) * (2 * δ) ^ 2 := by
            simp [Finset.sum_const, nsmul_eq_mul]
      _ = 4 * (k : ℝ) * δ ^ 2 := by ring
  have hw1sq : ‖blockElem (d := d) (k := k) (ℓ := ℓ) w' 1‖ ^ 2 ≤ 4 * (k : ℝ) * δ ^ 2 := by
    rw [hb1sq']
    exact hsum
  have hw1le : ‖blockElem (d := d) (k := k) (ℓ := ℓ) w' 1‖ ≤ 2 * Real.sqrt (k : ℝ) * δ := by
    have hsq2 : ‖blockElem (d := d) (k := k) (ℓ := ℓ) w' 1‖ ^ 2 ≤
        (2 * Real.sqrt (k : ℝ) * δ) ^ 2 := by
      calc
        ‖blockElem (d := d) (k := k) (ℓ := ℓ) w' 1‖ ^ 2 ≤ 4 * (k : ℝ) * δ ^ 2 := hw1sq
        _ = (2 * Real.sqrt (k : ℝ) * δ) ^ 2 := by
              rw [mul_pow, mul_pow]
              have hsqrt : (Real.sqrt (k : ℝ)) ^ 2 = (k : ℝ) := by
                rw [Real.sq_sqrt]
                positivity
              rw [hsqrt]
              ring
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hsq2
  -- ratio ‖w₁‖/‖w₀‖ = ‖w'₁‖
  have hw0'1 : ‖blockElem (d := d) (k := k) (ℓ := ℓ) w' 0‖ = 1 := by
    rw [hw'0]
    exact Commons.Analysis.InnerProductSpace.norm_iMulti_orthonormal e he_ON hk
  have hratio : ‖blockElem (d := d) (k := k) (ℓ := ℓ) w 1‖ /
      ‖blockElem (d := d) (k := k) (ℓ := ℓ) w 0‖ = ‖blockElem (d := d) (k := k) (ℓ := ℓ) w' 1‖ := by
    have habs0 : |lam| ≠ 0 := abs_ne_zero.mpr hlam0
    calc
      ‖blockElem (d := d) (k := k) (ℓ := ℓ) w 1‖ /
          ‖blockElem (d := d) (k := k) (ℓ := ℓ) w 0‖
          = (|lam| * ‖blockElem (d := d) (k := k) (ℓ := ℓ) w' 1‖) /
              (|lam| * ‖blockElem (d := d) (k := k) (ℓ := ℓ) w' 0‖) := by rw [hn 1, hn 0]
      _ = (|lam| * ‖blockElem (d := d) (k := k) (ℓ := ℓ) w' 1‖) / (|lam| * 1) := by rw [hw0'1]
      _ = ‖blockElem (d := d) (k := k) (ℓ := ℓ) w' 1‖ := by
            field_simp [habs0]
  calc
    ‖blockElem (d := d) (k := k) (ℓ := ℓ) (exteriorPower.ιMulti ℝ k u) 1‖ /
      ‖blockElem (d := d) (k := k) (ℓ := ℓ) (exteriorPower.ιMulti ℝ k u) 0‖
        = ‖blockElem (d := d) (k := k) (ℓ := ℓ) w 1‖ /
            ‖blockElem (d := d) (k := k) (ℓ := ℓ) w 0‖ := by
            simp [w]
    _ = ‖blockElem (d := d) (k := k) (ℓ := ℓ) w' 1‖ := hratio
    _ ≤ 2 * Real.sqrt (k : ℝ) * δ := hw1le
    _ = 2 * Real.sqrt (k : ℝ) *
          Submission.ProjectionDistance.planeResidual (Submodule.span ℝ (Set.range u))
            (Submission.WedgeBlocks.modelX ℓ) := by
            simp [δ, V]


/-- **Transversality ⇒ block-0 nonzero**: for an independent `u` spanning a plane transverse
to `x₀ᗮ`, the block-0 component of the pure tensor `w = ιMulti u` is nonzero (equivalently
`‖block₀ w‖ > 0`). -/
lemma blockElem_zero_ne_zero_of_transverse {d k : ℕ} (ℓ : ℕ) (hk : 0 < k)
    (u : Fin k → RD d) (hu : LinearIndependent ℝ u)
    (hbot : (Submodule.span ℝ (Set.range u)) ⊓ (Submission.WedgeBlocks.modelX ℓ)ᗮ = ⊥) :
    0 < ‖blockElem (d := d) (k := k) (ℓ := ℓ) (exteriorPower.ιMulti ℝ k u) 0‖ := by
  classical
  rcases Submission.WedgeGeneralE1.exists_graph_rep (d := d) (k := k) ℓ hk u hu hbot with
    ⟨e, coff, he_ON, he_x0, coff_orth, hspan⟩
  let g : Fin k → RD d := fun j => e j + coff j
  let w' : WK d k := exteriorPower.ιMulti ℝ k g
  have hw'0 : blockElem (d := d) (k := k) (ℓ := ℓ) w' 0 = exteriorPower.ιMulti ℝ k e := by
    dsimp [w', g]
    exact Submission.WedgeBlocks.blockElem_zero_of_graph (d := d) (k := k) ℓ e coff he_x0 coff_orth
  have hw'ne : w' ≠ 0 := by
    intro hz
    have h0 : blockElem (d := d) (k := k) (ℓ := ℓ) w' 0 = 0 := by rw [hz]; simp
    rw [hw'0] at h0
    have hn : ‖exteriorPower.ιMulti ℝ k e‖ ≠ 0 := by
      rw [Commons.Analysis.InnerProductSpace.norm_iMulti_orthonormal e he_ON hk]
      norm_num
    exact hn (by simp [h0])
  have hgLI : LinearIndependent ℝ g :=
    Commons.LinearAlgebra.ExteriorPower.iMulti_linearIndependent_of_ne_zero g hw'ne
  have hspan' : Submodule.span ℝ (Set.range u) = Submodule.span ℝ (Set.range g) := by
    simpa [g] using hspan.symm
  rcases Commons.LinearAlgebra.Alternating.iMulti_proportional_of_span_eq
      (𝕜 := ℝ) (M := RD d) u g hu hgLI hspan' with ⟨lam, hlam0, hprop⟩
  have hw'0norm : ‖blockElem (d := d) (k := k) (ℓ := ℓ) w' 0‖ = 1 := by
    rw [hw'0]
    exact Commons.Analysis.InnerProductSpace.norm_iMulti_orthonormal e he_ON hk
  have hw0lam : ‖blockElem (d := d) (k := k) (ℓ := ℓ)
      (exteriorPower.ιMulti ℝ k u) 0‖ = |lam| := by
    calc
      ‖blockElem (d := d) (k := k) (ℓ := ℓ) (exteriorPower.ιMulti ℝ k u) 0‖
          = ‖lam • blockElem (d := d) (k := k) (ℓ := ℓ) w' 0‖ := by
              have hc : blockElem (d := d) (k := k) (ℓ := ℓ) (exteriorPower.ιMulti ℝ k u) 0 =
                  lam • blockElem (d := d) (k := k) (ℓ := ℓ) w' 0 := by
                have hc0 := congrArg (fun z : WK d k =>
                  blockElem (d := d) (k := k) (ℓ := ℓ) z 0) hprop
                simpa [w', g, blockElem_smul] using hc0
              rw [hc]
      _ = |lam| * ‖blockElem (d := d) (k := k) (ℓ := ℓ) w' 0‖ := by
            rw [norm_smul, Real.norm_eq_abs]
      _ = |lam| := by rw [hw'0norm, mul_one]
  rw [hw0lam]
  exact abs_pos.mpr hlam0

/-- **Lemma 1(a), converse (product form)**: under the hypotheses of
`pureTensor_blockRatio_le_planeResidual`, `‖w₁‖ ≤ 2√k · δ · ‖w₀‖`. -/
lemma block1_le_mul_planeResidual {d k : ℕ} (ℓ : ℕ) (hk : 0 < k)
    (u : Fin k → RD d) (hu : LinearIndependent ℝ u)
    (hbot : (Submodule.span ℝ (Set.range u)) ⊓ (Submission.WedgeBlocks.modelX ℓ)ᗮ = ⊥)
    (hδ12 : Submission.ProjectionDistance.planeResidual (Submodule.span ℝ (Set.range u))
        (Submission.WedgeBlocks.modelX ℓ) ≤ 1 / 2) :
    ‖blockElem (d := d) (k := k) (ℓ := ℓ) (exteriorPower.ιMulti ℝ k u) 1‖ ≤
      (2 : ℝ) * Real.sqrt (k : ℝ) *
        Submission.ProjectionDistance.planeResidual (Submodule.span ℝ (Set.range u))
          (Submission.WedgeBlocks.modelX ℓ) *
        ‖blockElem (d := d) (k := k) (ℓ := ℓ) (exteriorPower.ιMulti ℝ k u) 0‖ := by
  have hratio := pureTensor_blockRatio_le_planeResidual (d := d) (k := k) ℓ hk u hu hbot hδ12
  have hXpos : 0 < ‖blockElem (d := d) (k := k) (ℓ := ℓ) (exteriorPower.ιMulti ℝ k u) 0‖ :=
    blockElem_zero_ne_zero_of_transverse (d := d) (k := k) ℓ hk u hu hbot
  have hle : ‖blockElem (d := d) (k := k) (ℓ := ℓ) (exteriorPower.ιMulti ℝ k u) 1‖ ≤
      (2 : ℝ) * Real.sqrt (k : ℝ) *
        Submission.ProjectionDistance.planeResidual (Submodule.span ℝ (Set.range u))
          (Submission.WedgeBlocks.modelX ℓ) *
        ‖blockElem (d := d) (k := k) (ℓ := ℓ) (exteriorPower.ιMulti ℝ k u) 0‖ := by
    exact (div_le_iff₀ hXpos).mp hratio
  exact hle


end Submission.WedgeLemma1a
