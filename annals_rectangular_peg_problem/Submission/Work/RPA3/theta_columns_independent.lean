import Mathlib
import Submission.Work.RPA3.theta_columns_defs
import Submission.Work.RPA3.theta_columns_zero
import Submission.Work.RPA3.continuous_thCol
import Submission.Work.RPA3.thCol_add_two_pi

/-!
# RPA3, D2: invertibility of the derivative of the tubular map

The tubular parametrisation `θ(τ,x,t,ξ) = ℓ τ (x,t) + J(ξ₁ ∂_xℓ + ξ₂ ∂_tℓ)` has a derivative
`Z ↦ θ(τ,Z)` whose four columns `∂_xθ, ∂_tθ, ∂_{ξ₁}θ, ∂_{ξ₂}θ` are linearly independent, uniformly
for `ξ` in a small ball and `(τ,x,t)` in the compact parameter region `τ ∈ [-1,2]`,
`|x| ≤ X₀+1`, `t ∈ ℝ` (the angle `t` is periodic).

The proof is the one described in the statement: the four columns depend continuously on
`w = (τ,((x,t),ξ))` (`continuous_thCol`), so their `4 × 4` matrix in the coordinates of `PS`
(`thColMat`) is continuous and its determinant is a continuous real function `D`; at `ξ = 0` the
four columns are `∂_xℓ, ∂_tℓ, J∂_xℓ, J∂_tℓ`, a basis by `imm` and `lag` (`theta_columns_zero`), so
`D ≠ 0` there.  On the compact set
`C = [-1,2] × [-X₀-1,X₀+1] × [0,2π] × {‖ξ‖ ≤ 1}` the set `{D = 0}` is compact and stays away from
the slice `ξ = 0`, so the minimum of `‖ξ‖` on it is a positive `ε` uniform in `(τ,x,t)`; this gives
the statement for `t ∈ [0,2π]`, and the general `t` follows from the `2π`-periodicity of the four
columns in `t` (`thCol_add_two_pi`).
-/

open scoped ContDiff Matrix

set_option autoImplicit false
noncomputable section

namespace Work.RPA3

/-- The four columns of the tubular map are periodic in the angle `t` with period `2π`; iterated,
this gives periodicity by any integer multiple of `2π`. -/
theorem thCol_periodic_int (L : LagFamilyAll) (j : Fin 4) (τ x t : ℝ) (ξ : ℝ × ℝ) (k : ℤ) :
    thCol L j (τ, ((x, t + (k : ℝ) * (2 * Real.pi)), ξ)) = thCol L j (τ, ((x, t), ξ)) := by
  have hper : Function.Periodic (fun t : ℝ => thCol L j (τ, ((x, t), ξ))) (2 * Real.pi) :=
    fun t => thCol_add_two_pi L j τ x t ξ
  exact hper.int_mul k t

/-- Every real `t` is `t' + k·2π` for some `t' ∈ [0,2π]` and some integer `k`. -/
theorem exists_shift_two_pi (t : ℝ) :
    ∃ t' ∈ Set.Icc (0 : ℝ) (2 * Real.pi), ∃ k : ℤ, t = t' + (k : ℝ) * (2 * Real.pi) := by
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  refine ⟨t - ((⌊t / (2 * Real.pi)⌋ : ℤ) : ℝ) * (2 * Real.pi), ?_, ⌊t / (2 * Real.pi)⌋, by ring⟩
  have hfloor : ((⌊t / (2 * Real.pi)⌋ : ℤ) : ℝ) ≤ t / (2 * Real.pi) := Int.floor_le _
  have hfloor' : t / (2 * Real.pi) < ((⌊t / (2 * Real.pi)⌋ : ℤ) : ℝ) + 1 :=
    Int.lt_floor_add_one _
  have hle : ((⌊t / (2 * Real.pi)⌋ : ℤ) : ℝ) * (2 * Real.pi) ≤ t := by
    have := mul_le_mul_of_nonneg_right hfloor (le_of_lt h2pi)
    rwa [div_mul_cancel₀ _ (ne_of_gt h2pi)] at this
  have hlt : t < (((⌊t / (2 * Real.pi)⌋ : ℤ) : ℝ) + 1) * (2 * Real.pi) := by
    have := mul_lt_mul_of_pos_right hfloor' h2pi
    rwa [div_mul_cancel₀ _ (ne_of_gt h2pi)] at this
  constructor
  · show (0 : ℝ) ≤ t - ((⌊t / (2 * Real.pi)⌋ : ℤ) : ℝ) * (2 * Real.pi)
    linarith
  · show t - ((⌊t / (2 * Real.pi)⌋ : ℤ) : ℝ) * (2 * Real.pi) ≤ 2 * Real.pi
    linarith

/-- **D2, invertibility of the derivative of the tubular map.**  There is a uniform `ε > 0` such
that on the compact parameter region `τ ∈ [-1,2]`, `|x| ≤ X₀+1` and `‖ξ‖ < ε`, the four columns
`∂_xθ, ∂_tθ, ∂_{ξ₁}θ, ∂_{ξ₂}θ` of the derivative of `Z ↦ θ(τ,Z)` are linearly independent
(`ColumnsIndependent`).

Proof: at `ξ = 0` the four columns are `∂_xℓ, ∂_tℓ, J∂_xℓ, J∂_tℓ`, a basis by `L.imm` and `L.lag`
(`lagrangian_independent` in `Submission.Work.RPA3.Symp`).  For `ξ ≠ 0` the columns are obtained
from these by adding terms of order `‖ξ‖`, bounded on the compact region, so for small `‖ξ‖` the
matrix stays invertible; uniformity in `(τ,x,t)` follows by compactness of
`[-1,2] × [-X₀-1, X₀+1] × (ℝ/2πℤ)` (contradiction with a convergent sequence), and in the standard
region `|x| ≥ X₀` the four columns are the explicit constant basis vectors of `theta_std`. -/
theorem theta_columns_independent (L : Work.RPA3.LagFamilyAll) :
    ∃ ε > 0, ∀ τ ∈ Set.Icc (-1 : ℝ) 2, ∀ x t, |x| ≤ L.X0 + 1 → ∀ ξ : ℝ × ℝ, ‖ξ‖ < ε →
      Work.RPA3.ColumnsIndependent L τ x t ξ := by
  -- the determinant of the matrix of the four columns, as a function of `w = (τ,((x,t),ξ))`
  have hdet_cont : Continuous (fun w : ℝ × PS => (thColMat L w).det) :=
    (continuous_thColMat L (continuous_thCol L)).matrix_det
  -- at `ξ = 0` the four columns form a basis, so the determinant does not vanish
  have hzero : ∀ (τ x t : ℝ), (thColMat L (τ, ((x, t), (0 : ℝ × ℝ)))).det ≠ 0 :=
    fun τ x t => det_ne_zero_of_columnsIndependent L τ x t 0 (theta_columns_zero L τ x t)
  -- the compact parameter region, with `t` reduced to one period
  set C : Set (ℝ × PS) :=
    (Set.Icc (-1 : ℝ) 2) ×ˢ (((Set.Icc (-(L.X0 + 1)) (L.X0 + 1)) ×ˢ
      (Set.Icc (0 : ℝ) (2 * Real.pi))) ×ˢ (Metric.closedBall (0 : ℝ × ℝ) 1)) with hCdef
  have hCmem : ∀ w : ℝ × PS, w ∈ C ↔
      (w.1 ∈ Set.Icc (-1 : ℝ) 2 ∧ w.2.1.1 ∈ Set.Icc (-(L.X0 + 1)) (L.X0 + 1) ∧
        w.2.1.2 ∈ Set.Icc (0 : ℝ) (2 * Real.pi) ∧
        w.2.2 ∈ Metric.closedBall (0 : ℝ × ℝ) 1) := by
    intro w
    rw [hCdef, Set.mem_prod, Set.mem_prod, Set.mem_prod]
    tauto
  have hCcomp : IsCompact C := by
    rw [hCdef]
    exact isCompact_Icc.prod ((isCompact_Icc.prod isCompact_Icc).prod
      (isCompact_closedBall (0 : ℝ × ℝ) 1))
  have hCbound : ∀ w ∈ C, ‖w.2.2‖ ≤ 1 := by
    intro w hw
    have h := ((hCmem w).mp hw).2.2.2
    rwa [Metric.mem_closedBall, dist_zero_right] at h
  -- uniformity in `(τ,x,t)`: the minimum of `‖ξ‖` on the compact set `C ∩ {det = 0}`
  obtain ⟨ε, hεpos, hε1, hε⟩ : ∃ ε > 0, ε ≤ 1 ∧ ∀ w ∈ C, ‖w.2.2‖ < ε →
      (thColMat L w).det ≠ 0 := by
    by_cases hA : ∃ w ∈ C, (thColMat L w).det = 0
    · obtain ⟨w₀, hw₀C, hw₀D⟩ := hA
      have hAcomp : IsCompact {w : ℝ × PS | w ∈ C ∧ (thColMat L w).det = 0} :=
        hCcomp.inter_right (isClosed_eq hdet_cont continuous_const)
      obtain ⟨w₁, hw₁, hw₁min⟩ :=
        hAcomp.exists_isMinOn ⟨w₀, hw₀C, hw₀D⟩
          (f := fun w : ℝ × PS => ‖w.2.2‖) (by fun_prop)
      have hw₁C : w₁ ∈ C := hw₁.1
      have hw₁D : (thColMat L w₁).det = 0 := hw₁.2
      have hw₁ne : w₁.2.2 ≠ 0 := by
        intro h0
        have h1 := hzero w₁.1 w₁.2.1.1 w₁.2.1.2
        have heta : w₁ = (w₁.1, (w₁.2.1, w₁.2.2)) := rfl
        rw [heta] at hw₁D
        rw [h0] at hw₁D
        exact h1 hw₁D
      refine ⟨‖w₁.2.2‖, norm_pos_iff.mpr hw₁ne, hCbound w₁ hw₁C, ?_⟩
      intro w hwC hwξ hwD
      have hwmem : w ∈ {w : ℝ × PS | w ∈ C ∧ (thColMat L w).det = 0} := ⟨hwC, hwD⟩
      have hle : ‖w₁.2.2‖ ≤ ‖w.2.2‖ := (isMinOn_iff.mp hw₁min) w hwmem
      linarith
    · have hA' : ∀ w ∈ C, (thColMat L w).det ≠ 0 := by
        intro w hwC hwD
        exact hA ⟨w, hwC, hwD⟩
      exact ⟨1, one_pos, le_refl 1, fun w hwC _ => hA' w hwC⟩
  refine ⟨ε, hεpos, ?_⟩
  intro τ hτ x t hx ξ hξ
  -- reduce an arbitrary angle `t` to the fundamental period `[0,2π]`
  obtain ⟨t', ht'mem, k, htk⟩ := exists_shift_two_pi t
  have hmat : thColMat L (τ, ((x, t), ξ)) = thColMat L (τ, ((x, t'), ξ)) := by
    ext i j
    simp only [thColMat_apply]
    congr 1
    have hper := thCol_periodic_int L j τ x t' ξ k
    rw [← htk] at hper
    exact hper
  have hmem : (τ, ((x, t'), ξ)) ∈ C := by
    rw [hCmem]
    refine ⟨hτ, ?_, ht'mem, ?_⟩
    · rw [Set.mem_Icc]
      exact abs_le.mp hx
    · rw [Metric.mem_closedBall, dist_zero_right]
      exact le_of_lt (lt_of_lt_of_le hξ hε1)
  have hDne : (thColMat L (τ, ((x, t), ξ))).det ≠ 0 := by
    rw [hmat]
    exact hε _ hmem hξ
  exact columnsIndependent_of_det_ne_zero L τ x t ξ hDne

end Work.RPA3
