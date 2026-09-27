import Mathlib
import Submission.Work.EKLContract.Defs
import Submission.Work.EKLContract.Diag
import Submission.Work.EKLContract.Lemmas.Gamma3Facts

/-!
# Uniform injectivity on the thick set

EKL, §2.1 / Pisa Thm 6.3 (uniform injectivity of the orbit map).  The stabiliser of the
lattice `s Γ₃ ∈ X₃` is `s Γ₃ s⁻¹`; over the compact (Mahler) set of `ρ`-thick lattices these
stabilisers are *uniformly* discrete.

The statement below is the quantitative form used in the EKL development: given the
"short basis" hypothesis `hb` — for every `ρ`-thick `g ∈ SL₃(ℝ)` there is a non-singular
integral matrix `M` whose `g M`-columns are bounded by `C` — there is a uniform `δ > 0`
such that no conjugate `s γ s⁻¹` of a non-trivial element of `Γ₃` by a `ρ`-thick `s` lies in
the `δ`-neighbourhood `V δ` of the identity.

The proof is elementary and uses `hb` only once.  Fix `s` (`ρ`-thick) and `γ ∈ Γ₃`, `γ ≠ 1`,
and let `M` be the integral matrix supplied by `hb`, so that the columns of `S M`
(`S = toMat s`) have sup-norm `≤ C`.  Since `M` is invertible the integral matrix
`Z = (G-1) M` (`G` the integral matrix of `γ`) is nonzero, so some column `Z · j` is a nonzero
integer vector.  The thickness of `s` applied to that vector gives
`ρ ≤ ‖S · (Z · j)‖`, while `S · (Z · j) = (s γ s⁻¹ - 1) · (S · (M · j))`
and the second factor has norm `≤ C`; if `s γ s⁻¹ ∈ V δ` then each row of `s γ s⁻¹ - 1`
has entries `< δ`, whence `‖S · (Z · j)‖ ≤ 3 δ C`.  Choosing `δ = ρ/(6C)` makes this `≤ ρ/2`,
the required contradiction.
-/

open Work.EKLContract
open scoped Matrix

set_option linter.unusedVariables false

namespace Work.EKLComp

/-- Entrywise closeness of `A` to `1` and a norm bound on `v` give a bound on `(A-1) v`.
The `3` is the dimension. -/
lemma norm_sub_mulVec_le {δ B : ℝ} (hδ : 0 ≤ δ) (hB : 0 ≤ B)
    {A : Matrix (Fin 3) (Fin 3) ℝ}
    (hA : ∀ i j, |A i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ δ)
    {v : Fin 3 → ℝ} (hv : ‖v‖ ≤ B) :
    ‖(A - 1) *ᵥ v‖ ≤ 3 * δ * B := by
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro i
  calc ‖((A - 1) *ᵥ v) i‖ = |∑ k, (A - 1) i k * v k| := by
        rw [Real.norm_eq_abs, Matrix.mulVec_apply_eq_sum]
    _ ≤ ∑ k, |(A - 1) i k * v k| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k, |(A - 1) i k| * |v k| := by simp [abs_mul]
    _ ≤ ∑ k, δ * B := by
        apply Finset.sum_le_sum
        intro k _
        have hk : |(A - 1) i k| ≤ δ := by
          simpa only [Matrix.sub_apply] using hA i k
        have hvk : |v k| ≤ B := by
          rw [← Real.norm_eq_abs]
          exact le_trans (norm_le_pi_norm v k) hv
        calc |(A - 1) i k| * |v k| ≤ δ * |v k| := mul_le_mul_of_nonneg_right hk (abs_nonneg _)
          _ ≤ δ * B := mul_le_mul_of_nonneg_left hvk hδ
    _ = 3 * δ * B := by rw [Fin.sum_univ_three]; ring

/-- Casting an integral matrix–vector product to `ℝ`. -/
lemma map_mulVec_int (A : Matrix (Fin 3) (Fin 3) ℤ) (v : Fin 3 → ℤ) :
    (A.map (Int.castRingHom ℝ)) *ᵥ (fun j => ((v j : ℤ) : ℝ)) =
      fun i => (((A *ᵥ v) i : ℤ) : ℝ) := by
  ext i
  rw [Matrix.mulVec_apply_eq_sum, Matrix.mulVec_apply_eq_sum]
  push_cast
  rfl

/-- Casting a column of an integral matrix product to `ℝ`. -/
lemma map_mulVec_col_int (A B : Matrix (Fin 3) (Fin 3) ℤ) (j : Fin 3) :
    (A.map (Int.castRingHom ℝ)) *ᵥ (fun k => ((B k j : ℤ) : ℝ)) =
      fun i => (((A * B) i j : ℤ) : ℝ) := by
  rw [map_mulVec_int]
  ext i
  rw [Matrix.mulVec_apply_eq_sum, Matrix.mul_apply]

/-- An integral matrix with nonzero determinant is cancellable on the left. -/
lemma eq_zero_of_mul_eq_zero_of_det_ne_zero {A B : Matrix (Fin 3) (Fin 3) ℤ}
    (hB : B.det ≠ 0) (h : A * B = 0) : A = 0 := by
  have h1 : A * B * B.adjugate = 0 := by rw [h, Matrix.zero_mul]
  rw [Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one] at h1
  rcases smul_eq_zero.mp h1 with h2 | h2
  · exact absurd h2 hB
  · exact h2

/-- The real matrix of `G - 1` from the real matrix of `G`. -/
lemma map_sub_one (G : Matrix (Fin 3) (Fin 3) ℤ) :
    (G - 1).map (Int.castRingHom ℝ) = G.map (Int.castRingHom ℝ) - 1 := by
  ext i l
  simp only [Matrix.sub_apply, Matrix.map_apply, Matrix.one_apply]
  by_cases h : i = l <;> simp [h, Int.cast_sub]

theorem thick_inj_given_short (ρ : ℝ) (hρ : 0 < ρ) (C : ℝ) (hC : 0 < C)
    (hb : ∀ g : Matrix (Fin 3) (Fin 3) ℝ, g.det = 1 →
      (∀ m : Fin 3 → ℤ, m ≠ 0 → ρ ≤ ‖Matrix.mulVec g (fun j => (m j : ℝ))‖) →
      ∃ M : Matrix (Fin 3) (Fin 3) ℤ, M.det ≠ 0 ∧
        ∀ j : Fin 3, ‖Matrix.mulVec g (fun k => ((M k j : ℤ) : ℝ))‖ ≤ C) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : Work.EKLContract.SL3,
      (∀ m : Fin 3 → ℤ, m ≠ 0 → ρ ≤ ‖Matrix.mulVec (Work.EKLContract.toMat s) (fun j => (m j : ℝ))‖) →
      ∀ γ : Work.EKLContract.SL3, γ ∈ Work.EKLContract.Γ3 → γ ≠ 1 →
        ¬ (s * γ * s⁻¹ ∈ Work.EKLContract.V δ) := by
  refine ⟨ρ / (6 * C), by positivity, ?_⟩
  intro s hs γ hγmem hγne hV
  change ∀ i j, |toMat (s * γ * s⁻¹) i j -
    (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| < ρ / (6 * C) at hV
  -- the short basis of `s` supplied by `hb`
  obtain ⟨M, hMdet, hMcol⟩ := hb (toMat s) (Matrix.SpecialLinearGroup.det_coe s) hs
  -- the integral model `G` of `γ`
  obtain ⟨G₀, hG₀⟩ := MonoidHom.mem_range.mp hγmem
  set G : Matrix (Fin 3) (Fin 3) ℤ := (G₀ : Matrix (Fin 3) (Fin 3) ℤ) with hGdef
  have hGr : toMat γ = G.map (Int.castRingHom ℝ) := by
    rw [← hG₀]
    exact Matrix.SpecialLinearGroup.coe_matrix_coe G₀
  have hGrne : toMat γ ≠ 1 := fun h => hγne (toMat_injective (by rw [h, toMat_one]))
  have hGne : G ≠ 1 := by
    intro h
    refine hγne (toMat_injective ?_)
    rw [toMat_one, hGr, h]
    ext i l
    simp only [Matrix.map_apply, Matrix.one_apply]
    by_cases h' : i = l <;> simp [h']
  -- the nonzero integral matrix whose column is the vector fed to the thickness of `s`
  set Z : Matrix (Fin 3) (Fin 3) ℤ := (G - 1) * M with hZdef
  have hZne : Z ≠ 0 := by
    rw [hZdef]
    intro h
    exact hGne (sub_eq_zero.mp (eq_zero_of_mul_eq_zero_of_det_ne_zero hMdet h))
  obtain ⟨k₀, j, hkj⟩ : ∃ k j, Z k j ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hZne (by ext k j; exact h k j)
  have hcolne : (fun k => Z k j) ≠ 0 := fun h => hkj (by simpa using congrFun h k₀)
  have hthick : ρ ≤ ‖Matrix.mulVec (toMat s) (fun k => ((Z k j : ℤ) : ℝ))‖ :=
    hs (fun k => Z k j) hcolne
  -- `(s γ s⁻¹) * s = s * γ` at the level of matrices
  have hAS : toMat (s * γ * s⁻¹) * toMat s = toMat s * toMat γ := by
    rw [← toMat_mul, ← toMat_mul]
    congr 1
    group
  -- express `S · (Z · j)` as `(s γ s⁻¹ - 1) · (S · (M · j))`
  have hcol : (fun k => ((Z k j : ℤ) : ℝ)) =
      (toMat γ - 1) *ᵥ (fun k => ((M k j : ℤ) : ℝ)) := by
    have h1 : toMat γ - 1 = (G - 1).map (Int.castRingHom ℝ) := by
      rw [hGr]
      exact (map_sub_one G).symm
    rw [hZdef, h1, map_mulVec_col_int]
  have hkey : Matrix.mulVec (toMat s) (fun k => ((Z k j : ℤ) : ℝ)) =
      (toMat (s * γ * s⁻¹) - 1) *ᵥ
        (Matrix.mulVec (toMat s) (fun k => ((M k j : ℤ) : ℝ))) := by
    calc Matrix.mulVec (toMat s) (fun k => ((Z k j : ℤ) : ℝ))
        = Matrix.mulVec (toMat s) ((toMat γ - 1) *ᵥ (fun k => ((M k j : ℤ) : ℝ))) := by
          rw [hcol]
      _ = (toMat s * (toMat γ - 1)) *ᵥ (fun k => ((M k j : ℤ) : ℝ)) := by
          rw [Matrix.mulVec_mulVec]
      _ = (toMat s * toMat γ - toMat s * 1) *ᵥ (fun k => ((M k j : ℤ) : ℝ)) := by
          rw [Matrix.mul_sub]
      _ = (toMat s * toMat γ - toMat s) *ᵥ (fun k => ((M k j : ℤ) : ℝ)) := by
          rw [Matrix.mul_one]
      _ = (toMat (s * γ * s⁻¹) * toMat s - toMat s) *ᵥ (fun k => ((M k j : ℤ) : ℝ)) := by
          rw [hAS]
      _ = (toMat (s * γ * s⁻¹) - 1) *ᵥ
            (Matrix.mulVec (toMat s) (fun k => ((M k j : ℤ) : ℝ))) := by
          rw [Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.mulVec_mulVec, Matrix.one_mulVec]
  have hbound : ‖(toMat (s * γ * s⁻¹) - 1) *ᵥ
        (Matrix.mulVec (toMat s) (fun k => ((M k j : ℤ) : ℝ)))‖ ≤ ρ / 2 := by
    have hv : ‖Matrix.mulVec (toMat s) (fun k => ((M k j : ℤ) : ℝ))‖ ≤ C := hMcol j
    have hA : ∀ i l, |toMat (s * γ * s⁻¹) i l - (1 : Matrix (Fin 3) (Fin 3) ℝ) i l| ≤
        ρ / (6 * C) := fun i l => le_of_lt (hV i l)
    calc ‖(toMat (s * γ * s⁻¹) - 1) *ᵥ
          (Matrix.mulVec (toMat s) (fun k => ((M k j : ℤ) : ℝ)))‖
        ≤ 3 * (ρ / (6 * C)) * C :=
          norm_sub_mulVec_le (by positivity) (le_trans (norm_nonneg _) hv) hA hv
      _ = ρ / 2 := by
          rw [mul_assoc]
          field_simp
          ring
  rw [hkey] at hthick
  linarith

end Work.EKLComp
