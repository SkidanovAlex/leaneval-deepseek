import Mathlib
import Submission.Commons.Analysis.Fourier.gaussian_shift_psf_matrix_le_correct

namespace Commons.Lattice.PoissonSummation

set_option autoImplicit false
open scoped BigOperators
open Module
open scoped RealInnerProductSpace InnerProductSpace

noncomputable section

/-! ## Coordinate machinery for a lattice with a `ℤ`-basis of coordinate matrix `A`

Throughout this section:
`E n = EuclideanSpace ℝ (Fin n)`, `ℒ ≤ E n` is a full-rank `ℤ`-lattice,
`b : Basis (Fin n) ℤ ℒ` is a `ℤ`-basis and `A` is its canonical coordinate matrix
(`hAcoords : (((b j : ℒ) : E n) i) = A i j`).
We express each lattice point `b.equivFun.symm k` in canonical coordinates through the
matrix `A`, and reindex lattice sums by the bijection `b.equivFun.symm`. -/

abbrev lmassE (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The `i`-th canonical coordinate functional on `E n`. -/
noncomputable def lmassCoordFun (n : ℕ) (i : Fin n) : lmassE n →ₗ[ℝ] ℝ :=
  (LinearMap.proj i).comp ((WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).toLinearMap)

lemma lmassCoordFun_apply {n : ℕ} (v : lmassE n) (i : Fin n) :
    lmassCoordFun n i v = v i := rfl

/-- Canonical coordinates of a `ℤ`-combination of basis vectors are given by `A.mulVec`. -/
lemma lmass_coord_of_basis {n : ℕ} (ℒ : Submodule ℤ (lmassE n)) [DiscreteTopology ℒ] [IsZLattice ℝ ℒ]
    (b : Basis (Fin n) ℤ ℒ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hAcoords : ∀ i j : Fin n, (((b j : ℒ) : lmassE n) i) = A i j)
    (k : Fin n → ℤ) (i : Fin n) :
    (((b.equivFun.symm k : ℒ) : lmassE n)) i = (A.mulVec (fun j : Fin n => (k j : ℝ))) i := by
  have hsum : (b.equivFun.symm k : ℒ) = ∑ j : Fin n, (k j : ℤ) • (b j) := by
    rw [Basis.equivFun_symm_apply]
  rw [hsum]
  change (lmassCoordFun n i) (ℒ.subtype (∑ j : Fin n, (k j : ℤ) • (b j : ℒ))) =
    (A.mulVec (fun j : Fin n => (k j : ℝ))) i
  have hsub : ℒ.subtype (∑ j : Fin n, (k j : ℤ) • (b j : ℒ)) =
      (∑ j : Fin n, (k j : ℤ) • (ℒ.subtype (b j))) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j hj
    simp [Submodule.subtype_apply]
  rw [hsub]
  rw [map_sum]
  calc
    (∑ j : Fin n, lmassCoordFun n i ((k j : ℤ) • ((b j : ℒ) : lmassE n)))
        = ∑ j : Fin n, A i j * (k j : ℝ) := by
            apply Finset.sum_congr rfl
            intro j hj
            calc
              lmassCoordFun n i ((k j : ℤ) • ((b j : ℒ) : lmassE n))
                  = (k j : ℝ) * (lmassCoordFun n i ((b j : ℒ) : lmassE n)) := by
                    rw [← Int.cast_smul_eq_zsmul ℝ (k j) ((b j : ℒ) : lmassE n)]
                    rw [map_smul]
                    simp [lmassCoordFun_apply]
              _ = (k j : ℝ) * (A i j) := by
                    rw [← hAcoords i j]
                    rfl
              _ = A i j * (k j : ℝ) := by ring
    _ = (A.mulVec (fun j : Fin n => (k j : ℝ))) i := by rfl

/-- Squared norm on `E n` is the sum of squares of canonical coordinates. -/
lemma lmass_norm_sq_sum_sq {n : ℕ} (v : lmassE n) : ‖v‖ ^ 2 = ∑ i : Fin n, (v i) ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2 (fun _ : Fin n => ℝ)]
  simp

/-- The squared norm of a shifted lattice point expressed through the coordinate matrix. -/
lemma lmass_norm_sq_shift {n : ℕ} (ℒ : Submodule ℤ (lmassE n)) [DiscreteTopology ℒ] [IsZLattice ℝ ℒ]
    (b : Basis (Fin n) ℤ ℒ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hAcoords : ∀ i j : Fin n, (((b j : ℒ) : lmassE n) i) = A i j)
    (k : Fin n → ℤ) (u : lmassE n) :
    ‖((b.equivFun.symm k : ℒ) : lmassE n) - u‖ ^ 2 =
      ∑ i : Fin n, (((A.mulVec (fun j : Fin n => (k j : ℝ))) i) - u i) ^ 2 := by
  rw [lmass_norm_sq_sum_sq]
  apply Finset.sum_congr rfl
  intro i hi
  change ((((b.equivFun.symm k : ℒ) : lmassE n) - u) i) ^ 2 =
      (((A.mulVec (fun j : Fin n => (k j : ℝ))) i) - u i) ^ 2
  congr 1
  rw [WithLp.ofLp_sub]
  rw [Pi.sub_apply]
  rw [lmass_coord_of_basis ℒ b A hAcoords k i]

/-- The squared norm of a lattice point expressed through the coordinate matrix. -/
lemma lmass_norm_sq {n : ℕ} (ℒ : Submodule ℤ (lmassE n)) [DiscreteTopology ℒ] [IsZLattice ℝ ℒ]
    (b : Basis (Fin n) ℤ ℒ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hAcoords : ∀ i j : Fin n, (((b j : ℒ) : lmassE n) i) = A i j)
    (k : Fin n → ℤ) :
    ‖((b.equivFun.symm k : ℒ) : lmassE n)‖ ^ 2 =
      ∑ i : Fin n, (((A.mulVec (fun j : Fin n => (k j : ℝ))) i) ^ 2) := by
  rw [lmass_norm_sq_sum_sq]
  apply Finset.sum_congr rfl
  intro i hi
  change (((b.equivFun.symm k : ℒ) : lmassE n) i) ^ 2 =
      (((A.mulVec (fun j : Fin n => (k j : ℝ))) i) ^ 2)
  congr 1
  rw [lmass_coord_of_basis ℒ b A hAcoords k i]

/-- Reindexing the unshifted lattice Gaussian sum by the `ℤ`-basis. -/
lemma lmass_tsum_reindex_unshifted {n : ℕ} (ℒ : Submodule ℤ (lmassE n)) [DiscreteTopology ℒ] [IsZLattice ℝ ℒ]
    (b : Basis (Fin n) ℤ ℒ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hAcoords : ∀ i j : Fin n, (((b j : ℒ) : lmassE n) i) = A i j)
    (s : ℝ) :
    (∑' y : ℒ, Real.exp (-Real.pi * ‖(y : lmassE n)‖ ^ 2 / s ^ 2)) =
      (∑' k : Fin n → ℤ, Real.exp (-Real.pi * (∑ i, (((A.mulVec (fun j : Fin n => (k j : ℝ))) i) ^ 2)) / s ^ 2)) := by
  let e : (Fin n → ℤ) ≃ ℒ := (b.equivFun.symm).toEquiv
  rw [← Equiv.tsum_eq (e := e)
    (f := fun y : ℒ => Real.exp (-Real.pi * ‖(y : lmassE n)‖ ^ 2 / s ^ 2))]
  apply tsum_congr
  intro k
  change Real.exp (-Real.pi * ‖((b.equivFun.symm k : ℒ) : lmassE n)‖ ^ 2 / s ^ 2) =
      Real.exp (-Real.pi * (∑ i, (((A.mulVec (fun j : Fin n => (k j : ℝ))) i) ^ 2)) / s ^ 2)
  congr 1
  rw [lmass_norm_sq ℒ b A hAcoords k]

/-- Reindexing the shifted lattice Gaussian sum by the `ℤ`-basis. -/
lemma lmass_tsum_reindex_shifted {n : ℕ} (ℒ : Submodule ℤ (lmassE n)) [DiscreteTopology ℒ] [IsZLattice ℝ ℒ]
    (b : Basis (Fin n) ℤ ℒ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hAcoords : ∀ i j : Fin n, (((b j : ℒ) : lmassE n) i) = A i j)
    (s : ℝ) (u : lmassE n) :
    (∑' y : ℒ, Real.exp (-Real.pi * ‖(y : lmassE n) - u‖ ^ 2 / s ^ 2)) =
      (∑' k : Fin n → ℤ, Real.exp (-Real.pi * (∑ i, (((A.mulVec (fun j : Fin n => (k j : ℝ))) i) - u i) ^ 2) / s ^ 2)) := by
  let e : (Fin n → ℤ) ≃ ℒ := (b.equivFun.symm).toEquiv
  rw [← Equiv.tsum_eq (e := e)
    (f := fun y : ℒ => Real.exp (-Real.pi * ‖(y : lmassE n) - u‖ ^ 2 / s ^ 2))]
  apply tsum_congr
  intro k
  change Real.exp (-Real.pi * ‖((b.equivFun.symm k : ℒ) : lmassE n) - u‖ ^ 2 / s ^ 2) =
      Real.exp (-Real.pi * (∑ i, (((A.mulVec (fun j : Fin n => (k j : ℝ))) i) - u i) ^ 2) / s ^ 2)
  congr 1
  rw [lmass_norm_sq_shift ℒ b A hAcoords k u]

/-- **Shifted Gaussian mass of a lattice is maximized at zero shift (Banaszczyk).**

Let `ℒ ≤ E = EuclideanSpace ℝ (Fin n)` be a full-rank `ℤ`-lattice with `ℤ`-basis
`b : Basis (Fin n) ℤ ℒ` of canonical coordinate matrix `A` (hypothesis `hAcoords`), with
`A.det ≠ 0`.  Then for every `s > 0` and every shift vector `u : E`,

    ∑' y : ℒ, exp(-π·‖(y : E) - u‖²/s²)  ≤  ∑' y : ℒ, exp(-π·‖(y : E)‖²/s²).

Standard proof (Poisson summation with a shift):  writing `ℒ = {A·k : k ∈ ℤⁿ}` through the
basis, the shifted theta identity is
`∑' k : ℤⁿ, exp(-π·‖A·k - u‖²/s²) = (sⁿ/|det A|) · ∑' m : ℤⁿ,
exp(-π·s²·‖(A⁻¹)ᵀ·m‖²) · cos(2π·⟨(A⁻¹)ᵀ·m, u⟩)`
(each side of the unshifted Poisson identity applied to `x ↦ exp(-π‖Ax-u‖²/s²)`, whose
Fourier transform is `(sⁿ/|det A|)·exp(-πs²‖(A⁻¹)ᵀξ‖²)·exp(-2πi·⟨ξ,A⁻¹u⟩)`), and since
`cos ≤ 1` and all weights are positive, the right side is `≤ (sⁿ/|det A|)·∑' m,
exp(-πs²‖(A⁻¹)ᵀm‖²)`, which by (unshifted) Poisson summation equals the unshifted lattice
sum.  Helpful existing Commons lemmas: `Commons.Analysis.Fourier.gaussian_psf_matrix`
(the unshifted identity over ℤⁿ) and possibly `Commons.Lattice.PoissonSummation.lattice_psf`
(its lattice form, may not exist yet when you start - restate/prove what you need, or prove
this statement directly from `gaussian_psf_matrix` and the real-parts argument). -/
theorem lattice_shifted_mass_le {n : ℕ} (ℒ : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    [DiscreteTopology ℒ] [IsZLattice ℝ ℒ]
    (b : Basis (Fin n) ℤ ℒ) (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.det ≠ 0)
    (hAcoords : ∀ i j : Fin n, (((b j : ℒ) : EuclideanSpace ℝ (Fin n)) i) = A i j)
    (s : ℝ) (hs : 0 < s) (u : EuclideanSpace ℝ (Fin n)) :
    (∑' y : ℒ, Real.exp (-Real.pi * ‖(y : EuclideanSpace ℝ (Fin n)) - u‖ ^ 2 / s ^ 2)) ≤
      (∑' y : ℒ, Real.exp (-Real.pi * ‖(y : EuclideanSpace ℝ (Fin n))‖ ^ 2 / s ^ 2)) := by
  rw [lmass_tsum_reindex_shifted ℒ b A hAcoords s u]
  rw [lmass_tsum_reindex_unshifted ℒ b A hAcoords s]
  exact Commons.Analysis.Fourier.gaussian_shift_psf_matrix_le_correct A hA s hs u

end

end Commons.Lattice.PoissonSummation
