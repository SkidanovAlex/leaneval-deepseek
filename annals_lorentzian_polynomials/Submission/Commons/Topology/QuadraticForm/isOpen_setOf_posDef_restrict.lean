import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.LinearAlgebra.QuadraticForm.Basic

open Matrix Set Topology

namespace Commons.Topology.QuadraticForm

lemma matrix_toQuadraticForm'_restrict_apply_eq_sum {n : ℕ}
    (V : Submodule ℝ (Fin n → ℝ)) (B : Matrix (Fin n) (Fin n) ℝ) (v : V) :
    (B.toQuadraticForm'.restrict V) v =
      ∑ i : Fin n, ∑ j : Fin n, (v : Fin n → ℝ) i * B i j * (v : Fin n → ℝ) j := by
  rw [QuadraticMap.restrict_apply]
  simp [Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
    Matrix.toLinearMap₂'_apply', dotProduct, Matrix.mulVec, Finset.mul_sum,
    mul_assoc, mul_left_comm, mul_comm]

lemma continuous_matrix_toQuadraticForm'_restrict {n : ℕ}
    (V : Submodule ℝ (Fin n → ℝ)) :
    Continuous (fun p : Matrix (Fin n) (Fin n) ℝ × V =>
      (p.1.toQuadraticForm'.restrict V) p.2) := by
  have hsum : Continuous (fun p : Matrix (Fin n) (Fin n) ℝ × V =>
      ∑ i : Fin n, ∑ j : Fin n, (p.2 : Fin n → ℝ) i * p.1 i j * (p.2 : Fin n → ℝ) j) := by
    refine continuous_finsetSum Finset.univ ?_
    intro i hi
    refine continuous_finsetSum Finset.univ ?_
    intro j hj
    have hvi : Continuous (fun p : Matrix (Fin n) (Fin n) ℝ × V => (p.2 : Fin n → ℝ) i) :=
      (continuous_apply i).comp (continuous_subtype_val.comp continuous_snd)
    have hvj : Continuous (fun p : Matrix (Fin n) (Fin n) ℝ × V => (p.2 : Fin n → ℝ) j) :=
      (continuous_apply j).comp (continuous_subtype_val.comp continuous_snd)
    have hBij : Continuous (fun p : Matrix (Fin n) (Fin n) ℝ × V => p.1 i j) :=
      (continuous_apply j).comp ((continuous_apply i).comp continuous_fst)
    exact (hvi.mul hBij).mul hvj
  exact hsum.congr (fun p => (matrix_toQuadraticForm'_restrict_apply_eq_sum V p.1 p.2).symm)

lemma exists_nhds_forall_pos_of_compact
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {s : Set Y} (hs : IsCompact s)
    (f : X × Y → ℝ) (hf : Continuous f)
    {x : X} (h : ∀ y ∈ s, 0 < f (x, y)) :
    ∃ U ∈ 𝓝 x, ∀ x' ∈ U, ∀ y ∈ s, 0 < f (x', y) := by
  classical
  let pos : Set (X × Y) := {p | 0 < f p}
  have hpos_mem : ∀ y ∈ s, pos ∈ 𝓝 (x, y) := by
    intro y hy
    have hpre : f ⁻¹' (Ioi (0 : ℝ)) ∈ 𝓝 (x, y) :=
      (hf.continuousAt).preimage_mem_nhds (Ioi_mem_nhds (h y hy))
    exact hpre
  have h1 : ∀ y, y ∈ s → ∃ u : Set X, u ∈ 𝓝 x ∧ ∃ v : Set Y, v ∈ 𝓝 y ∧ u ×ˢ v ⊆ pos := by
    intro y hy
    simpa [pos] using mem_nhds_prod_iff.mp (hpos_mem y hy)
  choose! U hU_rest using h1
  have hU : ∀ y ∈ s, U y ∈ 𝓝 x := fun y hy => (hU_rest y hy).1
  have h2 : ∀ y, y ∈ s → ∃ v : Set Y, v ∈ 𝓝 y ∧ U y ×ˢ v ⊆ pos := by
    intro y hy
    exact (hU_rest y hy).2
  choose! W hW_rest using h2
  have hW : ∀ y ∈ s, W y ∈ 𝓝 y := fun y hy => (hW_rest y hy).1
  have hUW : ∀ y ∈ s, U y ×ˢ W y ⊆ pos := fun y hy => (hW_rest y hy).2
  rcases hs.elim_nhds_subcover W hW with ⟨t, hts, hcover⟩
  let U0 : Set X := ⋂ y ∈ t, U y
  have hU0 : U0 ∈ 𝓝 x := by
    simpa [U0] using (Filter.biInter_finset_mem t).2 (fun y hy => hU y (hts y hy))
  refine ⟨U0, hU0, ?_⟩
  intro x' hx' y hy
  have hycover : y ∈ ⋃ y0 ∈ t, W y0 := hcover hy
  rcases (Set.mem_iUnion₂.mp hycover) with ⟨y0, hy0t, hyW⟩
  have hxU : x' ∈ U y0 := by
    have : x' ∈ ⋂ y ∈ t, U y := by simpa [U0] using hx'
    exact Set.biInter_subset_of_mem hy0t this
  have hp : (x', y) ∈ U y0 ×ˢ W y0 := Set.mem_prod.mpr ⟨hxU, hyW⟩
  have hp' : (x', y) ∈ pos := hUW y0 (hts y0 hy0t) hp
  simpa [pos] using hp'

theorem isOpen_setOf_posDef_restrict {n : ℕ} (V : Submodule ℝ (Fin n → ℝ)) :
    IsOpen {B : Matrix (Fin n) (Fin n) ℝ |
      (B.toQuadraticForm'.restrict V).PosDef} := by
  classical
  refine isOpen_iff_mem_nhds.mpr ?_
  intro B0 hB0
  let X := Matrix (Fin n) (Fin n) ℝ
  let T : Set V := Metric.sphere (0 : V) 1
  have hT_compact : IsCompact T := by
    simpa [T] using isCompact_sphere (0 : V) (1 : ℝ)
  let g : X × V → ℝ := fun p => (p.1.toQuadraticForm'.restrict V) p.2
  have hg_cont : Continuous g := by
    simpa [g] using continuous_matrix_toQuadraticForm'_restrict V
  have hg_pos : ∀ v ∈ T, 0 < g (B0, v) := by
    intro v hv
    have hv_norm : ‖v‖ = 1 := by
      simpa [T, Metric.mem_sphere, dist_eq_norm] using hv
    have hv_ne : v ≠ 0 := by
      exact norm_ne_zero_iff.mp (by rw [hv_norm]; norm_num)
    change 0 < (B0.toQuadraticForm'.restrict V) v
    exact hB0 v hv_ne
  rcases exists_nhds_forall_pos_of_compact hT_compact g hg_cont hg_pos with ⟨U, hU, hUpos⟩
  have hUsub : U ⊆ {B : Matrix (Fin n) (Fin n) ℝ | (B.toQuadraticForm'.restrict V).PosDef} := by
    intro B hB
    change (B.toQuadraticForm'.restrict V).PosDef
    intro v hv_ne
    let r : ℝ := (‖v‖)⁻¹
    have hnorm_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv_ne
    have hr_pos : 0 < r := inv_pos.mpr hnorm_pos
    have hr_nonneg : 0 ≤ r := le_of_lt hr_pos
    have hw_norm : ‖r • v‖ = 1 := by
      rw [norm_smul_of_nonneg hr_nonneg v]
      exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv_ne)
    have hwT : r • v ∈ T := by
      have : dist (r • v) (0 : V) = 1 := by
        simpa [dist_eq_norm] using hw_norm
      simpa [T, Metric.mem_sphere] using this
    have hw_pos : 0 < g (B, r • v) := hUpos B hB (r • v) hwT
    have hw_pos_restrict : 0 < (B.toQuadraticForm'.restrict V) (r • v) := by
      simpa [g] using hw_pos
    have hq_w : (B.toQuadraticForm'.restrict V) (r • v) =
        (r * r) * B.toQuadraticForm' (v : Fin n → ℝ) := by
      simp [QuadraticMap.restrict_apply, QuadraticMap.map_smul, smul_eq_mul, mul_assoc]
    have hq_w' : 0 < (r * r) * B.toQuadraticForm' (v : Fin n → ℝ) := by
      simpa [hq_w] using hw_pos_restrict
    have hr2_pos : 0 < r * r := mul_pos hr_pos hr_pos
    have hq_v' : 0 < B.toQuadraticForm' (v : Fin n → ℝ) :=
      (mul_pos_iff_of_pos_left hr2_pos).mp hq_w'
    simpa [QuadraticMap.restrict_apply] using hq_v'
  exact Filter.mem_of_superset hU hUsub

end Commons.Topology.QuadraticForm