import Mathlib
import Submission.Work.EKLComp.EucDefs

/-!
# Minkowski: a determinant-one `3 × 3` matrix has a short integer vector

For `M : Matrix (Fin 3) (Fin 3) ℝ` with `M.det = 1`, the ℤ-lattice `M ℤ³ ⊆ ℝ³` has covolume `1`,
so by Minkowski's convex body theorem every symmetric convex body of volume `> 8` contains a
nonzero lattice point.  The open cube `(-2,2)³` has volume `64 > 8`, whence a nonzero
`m : Fin 3 → ℤ` with every coordinate of `M *ᵥ m` strictly between `-2` and `2`, and hence
Euclidean norm at most `2√3`.
-/

set_option linter.style.haveILetI false

namespace Work.EKLComp

open MeasureTheory Module Matrix

noncomputable section

/-- The ℤ-lattice `M ℤ³ ⊆ ℝ³` (with `M.det = 1`, so covolume `1`) has a nonzero vector of
Euclidean norm at most `2√3`.  Proof plan: Minkowski's convex body theorem
(`MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure`) applied to the open
cube `s = Set.pi Set.univ (fun _ : Fin 3 => Set.Ioo (-2 : ℝ) 2)` (convex, symmetric, volume
`4^3 = 64 > 8 = volume (fundamentalDomain b) * 2 ^ finrank ℝ (Fin 3 → ℝ)`): the lattice is
`L = (Submodule.span ℤ (Set.range b)).toAddSubgroup` where `b := (Pi.basisFun ℝ (Fin 3)).map
(Matrix.toLinearEquiv' M h)` with `h : Invertible M` obtained from `hM`, so that `b i = M.col i` and
`Matrix.of b = Mᵀ`, whence `ZSpan.volume_fundamentalDomain` gives fundamental-domain volume
`|det M| = 1` (`ZSpan.isAddFundamentalDomain'`).  NOTE: in this Mathlib version
`Matrix.of f i j = f i j` (no transpose).  A lattice point `x ∈ L` is
`∑ i, c i • b i = M *ᵥ (fun i => (c i : ℝ))` with `c : Fin 3 → ℤ`
(`Submodule.mem_span_range_iff_exists_fun`); `x ≠ 0` gives `c ≠ 0` (apply `M.adjugate`, using
`Matrix.adjugate_mul` and `hM`).  Finally `x ∈ s` means `|x i| < 2` for all `i`, so
`enorm3 x = sqrt (∑ i, (x i)^2) < sqrt 12 = 2 * Real.sqrt 3`. -/
theorem short_vector_of_det_one (M : Matrix (Fin 3) (Fin 3) ℝ) (hM : M.det = 1) :
    ∃ m : Fin 3 → ℤ, m ≠ 0 ∧
      Work.EKLComp.enorm3 (Matrix.mulVec M (fun i => (m i : ℝ))) ≤ 2 * Real.sqrt 3 := by
  classical
  -- `M` is invertible, so its columns form a basis of `ℝ³`, whose ℤ-span is `M ℤ³`.
  have hunit : IsUnit M.det := by rw [hM]; exact isUnit_one
  let h : Invertible M := Matrix.invertibleOfIsUnitDet M hunit
  let e : (Fin 3 → ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ) := Matrix.toLinearEquiv' M h
  have he : ∀ v : Fin 3 → ℝ, e v = M *ᵥ v := fun v =>
    DFunLike.congr_fun (Matrix.toLinearEquiv'_apply M h) v
  let b : Basis (Fin 3) ℝ (Fin 3 → ℝ) := (Pi.basisFun ℝ (Fin 3)).map e
  have hb : ∀ i, b i = M.col i := by
    intro i
    rw [Basis.map_apply, Pi.basisFun_apply, he, Matrix.mulVec_single_one]
  have hofb : (Matrix.of b) = Mᵀ := by
    ext i j
    rw [Matrix.of_apply, hb i, Matrix.col_apply, Matrix.transpose_apply]
  have hdetb : (Matrix.of b).det = 1 := by
    rw [hofb, Matrix.det_transpose, hM]
  -- The lattice `M ℤ³` is countable.
  let L : AddSubgroup (Fin 3 → ℝ) := (Submodule.span ℤ (Set.range b)).toAddSubgroup
  haveI hcount : Countable L := by
    refine Set.Countable.to_subtype (Set.Countable.mono ?_
      (Set.countable_range (fun c : Fin 3 → ℤ => ∑ i, c i • b i)))
    intro x hx
    rw [Set.mem_range]
    exact (Submodule.mem_span_range_iff_exists_fun ℤ).1 hx
  -- The open cube `(-2,2)³`.
  set s : Set (Fin 3 → ℝ) := Set.pi Set.univ (fun _ : Fin 3 => Set.Ioo (-2 : ℝ) 2) with hs
  have hF : volume (ZSpan.fundamentalDomain b) = 1 := by
    rw [ZSpan.volume_fundamentalDomain, hdetb]; norm_num
  have hvols : volume s = 64 := by
    rw [hs, volume_pi, Measure.pi_pi]; simp [Real.volume_Ioo]; norm_num
  have hconv : Convex ℝ s := by
    rw [hs]; exact convex_pi (fun i _ => convex_Ioo _ _)
  have hsymm : ∀ x ∈ s, -x ∈ s := by
    intro x hx
    rw [hs] at hx ⊢
    intro i hi
    have h1 := hx i hi
    simp only [Set.mem_Ioo, Pi.neg_apply] at h1 ⊢
    constructor <;> linarith [h1.1, h1.2]
  have hfr : finrank ℝ (Fin 3 → ℝ) = 3 := Module.finrank_fin_fun ℝ
  -- Minkowski's convex body theorem.
  obtain ⟨x, hxne, hxmem⟩ :=
    MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
      (L := L) (F := ZSpan.fundamentalDomain b) (μ := volume) (s := s)
      (ZSpan.isAddFundamentalDomain' b (volume : Measure (Fin 3 → ℝ))) hsymm hconv (by
        rw [hF, hvols, hfr]; norm_num)
  -- Write the lattice point as `M *ᵥ m` for an integer vector `m`, which is nonzero.
  have hxL : (x : Fin 3 → ℝ) ∈ Submodule.span ℤ (Set.range b) := x.2
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hxL
  have hx_eq : (x : Fin 3 → ℝ) = M *ᵥ (fun i => (c i : ℝ)) := by
    rw [← hc]
    funext j
    rw [Matrix.mulVec_apply_eq_sum]
    simp only [Finset.sum_apply, hb, zsmul_eq_mul]
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  have hcne : c ≠ 0 := by
    intro hc0
    apply hxne
    apply Subtype.ext
    rw [← hc, hc0]
    simp
  have hcoord : ∀ i, (x : Fin 3 → ℝ) i ∈ Set.Ioo (-2 : ℝ) 2 := by
    intro i
    have h1 := hxmem
    rw [hs] at h1
    exact h1 i (Set.mem_univ i)
  refine ⟨c, hcne, ?_⟩
  rw [← hx_eq]
  -- Every coordinate of `x` is `< 2` in absolute value, so `enorm3 x ≤ √12 = 2√3`.
  have hsq : ∑ i, (x : Fin 3 → ℝ) i * (x : Fin 3 → ℝ) i ≤ 12 := by
    have h4 : ∀ i, (x : Fin 3 → ℝ) i * (x : Fin 3 → ℝ) i ≤ 4 := by
      intro i
      have h1 := hcoord i
      simp only [Set.mem_Ioo] at h1
      nlinarith [h1.1, h1.2]
    calc ∑ i, (x : Fin 3 → ℝ) i * (x : Fin 3 → ℝ) i ≤ ∑ _i : Fin 3, (4 : ℝ) :=
          Finset.sum_le_sum (fun i _ => h4 i)
      _ = 12 := by rw [Fin.sum_univ_three]; norm_num
  calc Work.EKLComp.enorm3 (x : Fin 3 → ℝ)
      = Real.sqrt (∑ i, (x : Fin 3 → ℝ) i * (x : Fin 3 → ℝ) i) := by
        rw [Work.EKLComp.enorm3, Work.EKLComp.dot3]
    _ ≤ Real.sqrt 12 := Real.sqrt_le_sqrt hsq
    _ = 2 * Real.sqrt 3 := by
        rw [show (12 : ℝ) = 4 * 3 by norm_num, Real.sqrt_mul (by norm_num),
          show Real.sqrt 4 = 2 by
            rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]

end

end Work.EKLComp
