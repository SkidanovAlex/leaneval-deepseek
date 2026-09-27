import Mathlib
import Submission.Work.EKLContract.Defs
import Submission.Work.EKLContract.Diag

/-!
# `HasShortVec (mkX 1) 2` holds, `HasShortVec (mkX 1) 1` fails

The identity coset `mkX 1 = Γ₃ ∈ X₃ = SL₃(ℝ)/SL₃(ℤ)` is the lattice `ℤ³`.  Every nonzero vector
of `ℤ³` has sup-norm `≥ 1`, so `λ₁(ℤ³) = 1`: the coset has a lattice vector of norm `< 2`
(namely `e₁`), but none of norm `< 1`.

The proof of the second half needs the observation that a representative of `mkX 1` lies in
`Γ₃ = SL₃(ℤ)`, hence has *integer* entries; the lattice vectors it produces are therefore
nonzero integer vectors, and a nonzero integer vector has a coordinate of absolute value `≥ 1`.
-/

namespace Work.EKLContract.Lemmas

open Work.EKLContract

/-- A cast integer whose real absolute value is `< 1` is `0`. -/
lemma int_eq_zero_of_abs_cast_lt_one {z : ℤ} (h : |(z : ℝ)| < 1) : z = 0 := by
  have h1 : (-1 : ℝ) < (z : ℝ) ∧ (z : ℝ) < 1 := by rwa [abs_lt] at h
  have h2 : (-1 : ℤ) < z := by exact_mod_cast h1.1
  have h3 : z < (1 : ℤ) := by exact_mod_cast h1.2
  omega

/-- A representative of the coset `mkX 1` lies in `Γ₃ = SL₃(ℤ)`. -/
lemma mem_Γ3_of_mkX_eq_one {g : SL3} (h : mkX g = mkX 1) : g ∈ Γ3 := by
  have h1 : g⁻¹ * 1 ∈ Γ3 := QuotientGroup.eq.mp h
  have h2 : g⁻¹ ∈ Γ3 := by simpa using h1
  simpa using (Subgroup.inv_mem_iff Γ3).mp h2

/-- Every element of `Γ₃` is the coercion of an integral matrix in `SL₃(ℤ)`. -/
lemma exists_intSL3_of_mem_Γ3 {g : SL3} (hg : g ∈ Γ3) :
    ∃ A : Matrix.SpecialLinearGroup (Fin 3) ℤ, (A : SL3) = g := by
  obtain ⟨A, hA⟩ := MonoidHom.mem_range.mp hg
  exact ⟨A, hA⟩

/-- With `A : SL₃(ℤ)` viewed in `SL₃(ℝ)`, the `i`-th coordinate of `A` applied to the image in
`ℝ³` of an integral vector `m` is the image of the corresponding integral coordinate. -/
lemma mulVec_coe_int (A : Matrix.SpecialLinearGroup (Fin 3) ℤ) (m : Fin 3 → ℤ) (i : Fin 3) :
    Matrix.mulVec ((A : SL3) : Matrix (Fin 3) (Fin 3) ℝ) (fun j => (m j : ℝ)) i
      = ((Matrix.mulVec (A : Matrix (Fin 3) (Fin 3) ℤ) m) i : ℝ) := by
  rw [Matrix.SpecialLinearGroup.coe_matrix_coe]
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
  push_cast
  simp

/-- An integral matrix of determinant `1` sends no nonzero integral vector to `0`. -/
lemma mulVec_int_ne_zero (A : Matrix.SpecialLinearGroup (Fin 3) ℤ) {m : Fin 3 → ℤ} (hm : m ≠ 0) :
    Matrix.mulVec (A : Matrix (Fin 3) (Fin 3) ℤ) m ≠ 0 := by
  intro h
  apply hm
  by_contra hm0
  have := (Matrix.exists_mulVec_eq_zero_iff (M := (A : Matrix (Fin 3) (Fin 3) ℤ))).mp
    ⟨m, hm0, h⟩
  rw [A.prop] at this
  exact one_ne_zero this

/-- `mkX 1 = ℤ³` has a lattice vector of norm `< 2` but none of norm `< 1`, i.e. `λ₁(ℤ³) = 1`. -/
theorem mkX_one_short : Work.EKLContract.HasShortVec (Work.EKLContract.mkX 1) 2 ∧
    ¬ Work.EKLContract.HasShortVec (Work.EKLContract.mkX 1) 1 := by
  constructor
  · -- `e₁ ∈ ℤ³` is a lattice vector of norm `1 < 2`
    refine ⟨1, rfl, ![1, 0, 0], ?_, ?_⟩
    · decide
    · intro i
      fin_cases i <;> norm_num [Matrix.one_mulVec]
  · -- every lattice vector of `ℤ³` has a coordinate `≥ 1` in absolute value
    rintro ⟨g, hg, m, hm, hshort⟩
    obtain ⟨A, hA⟩ := exists_intSL3_of_mem_Γ3 (mem_Γ3_of_mkX_eq_one hg)
    have hshort' : ∀ i, |Matrix.mulVec ((A : SL3) : Matrix (Fin 3) (Fin 3) ℝ)
        (fun j => (m j : ℝ)) i| < 1 := by
      intro i; rw [hA]; exact hshort i
    have hzero : Matrix.mulVec (A : Matrix (Fin 3) (Fin 3) ℤ) m = 0 := by
      funext i
      apply int_eq_zero_of_abs_cast_lt_one
      rw [← mulVec_coe_int A m i]
      exact hshort' i
    exact mulVec_int_ne_zero A hm hzero

end Work.EKLContract.Lemmas
