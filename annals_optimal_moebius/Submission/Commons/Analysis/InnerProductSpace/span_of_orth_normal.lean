import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Dual frame lemma: orthogonal to the normal means in the tangent span

In `EuclideanSpace ℝ (Fin 3)`, let `t₀, t₁, N` be an orthonormal triple
(unit, pairwise orthogonal).  Any vector `w` orthogonal to `N` lies in the
span of `t₀` and `t₁`:

`w ∈ Submodule.span ℝ ({t₀, t₁} : Set (EuclideanSpace ℝ (Fin 3)))`.

This is the companion of
`Commons.Analysis.InnerProductSpace.orthonormal_frame_decomp` (which says
"orthogonal to `t₀` and `t₁` ⟹ a multiple of `N`"); together they let one
decompose vectors of `ℝ³` in the moving frame `(t₀, t₁, N)` of a surface
whose unit normal is `N`.  Proof idea: an orthonormal triple spans `ℝ³`, so
expand `w` in it; the `N`-coefficient is `⟪w, N⟫ = 0`, leaving only the
`t₀, t₁` terms.
-/

noncomputable section
namespace Commons.Analysis.InnerProductSpace

open scoped BigOperators

/-- A vector orthogonal to the normal `N` of an orthonormal frame
`(t₀, t₁, N)` of `ℝ³` lies in the span of `t₀` and `t₁`. -/
theorem span_of_orth_normal {t₀ t₁ Nx w : EuclideanSpace ℝ (Fin 3)}
    (ht₀ : ‖t₀‖ = 1) (ht₁ : ‖t₁‖ = 1) (hN : ‖Nx‖ = 1)
    (h₀₁ : inner ℝ t₀ t₁ = 0) (h₀N : inner ℝ t₀ Nx = 0) (h₁N : inner ℝ t₁ Nx = 0)
    (hw : inner ℝ w Nx = 0) :
    w ∈ Submodule.span ℝ ({t₀, t₁} : Set (EuclideanSpace ℝ (Fin 3))) := by
  classical
  -- inner products of ℝ³ are symmetric, so record the mirrored hypotheses
  have h₁₀ : inner ℝ t₁ t₀ = 0 := by simpa [real_inner_comm] using h₀₁
  have hN₀ : inner ℝ Nx t₀ = 0 := by simpa [real_inner_comm] using h₀N
  have hN₁ : inner ℝ Nx t₁ = 0 := by simpa [real_inner_comm] using h₁N
  have hwN : inner ℝ Nx w = 0 := by simpa [real_inner_comm] using hw
  -- v is the orthonormal frame (t₀, t₁, Nx), indexed by Fin 3
  let v : Fin 3 → EuclideanSpace ℝ (Fin 3) := ![t₀, t₁, Nx]
  have hv : Orthonormal ℝ v := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j <;> simp [v, ht₀, ht₁, hN, h₀₁, h₁₀, h₀N, hN₀, h₁N, hN₁]
  -- an orthonormal family of the right cardinality is a basis
  have hcard : Fintype.card (Fin 3) = Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) := by simp
  let B := basisOfOrthonormalOfCardEqFinrank hv hcard
  have hvB : Orthonormal ℝ (B : Fin 3 → EuclideanSpace ℝ (Fin 3)) := by
    simpa [B, basisOfOrthonormalOfCardEqFinrank] using hv
  let b : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3)) := B.toOrthonormalBasis hvB
  have hb0 : b 0 = t₀ := by
    simp [b, B, basisOfOrthonormalOfCardEqFinrank, Module.Basis.coe_toOrthonormalBasis, v]
  have hb1 : b 1 = t₁ := by
    simp [b, B, basisOfOrthonormalOfCardEqFinrank, Module.Basis.coe_toOrthonormalBasis, v]
  have hb2 : b 2 = Nx := by
    simp [b, B, basisOfOrthonormalOfCardEqFinrank, Module.Basis.coe_toOrthonormalBasis, v]
  -- expand w in the frame; the Nx-component is ⟪w, Nx⟫ = 0
  have hw3 : w = (inner ℝ t₀ w) • t₀ + (inner ℝ t₁ w) • t₁ := by
    calc
      w = ∑ i : Fin 3, inner ℝ (b i) w • b i := by
        simpa using (b.sum_repr' w).symm
      _ = inner ℝ (b 0) w • b 0 + inner ℝ (b 1) w • b 1 + inner ℝ (b 2) w • b 2 := by
        rw [Fin.sum_univ_three]
      _ = inner ℝ t₀ w • t₀ + inner ℝ t₁ w • t₁ + inner ℝ Nx w • Nx := by
        rw [hb0, hb1, hb2]
      _ = (inner ℝ t₀ w) • t₀ + (inner ℝ t₁ w) • t₁ := by
        simp [hwN]
  -- ... hence w is an ℝ-linear combination of the generators t₀ and t₁
  let S : Submodule ℝ (EuclideanSpace ℝ (Fin 3)) :=
    Submodule.span ℝ ({t₀, t₁} : Set (EuclideanSpace ℝ (Fin 3)))
  have ht₀S : t₀ ∈ S := by
    exact Submodule.mem_span_of_mem (s := ({t₀, t₁} : Set (EuclideanSpace ℝ (Fin 3)))) (by simp)
  have ht₁S : t₁ ∈ S := by
    exact Submodule.mem_span_of_mem (s := ({t₀, t₁} : Set (EuclideanSpace ℝ (Fin 3)))) (by simp)
  rw [hw3]
  change (inner ℝ t₀ w) • t₀ + (inner ℝ t₁ w) • t₁ ∈ S
  exact Submodule.add_mem S (Submodule.smul_mem S (inner ℝ t₀ w) ht₀S)
    (Submodule.smul_mem S (inner ℝ t₁ w) ht₁S)

end Commons.Analysis.InnerProductSpace