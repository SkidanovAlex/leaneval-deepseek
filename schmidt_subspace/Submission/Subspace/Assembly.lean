import Mathlib
import Submission.Subspace.UBounds
import Submission.Subspace.ElimBlock
import Submission.Subspace.PderivDiv

/-!
# Interface lemmas for the maximal-rank assembly

Two small bridges needed to feed the output of the Siegel step (`exists_flat_poly`) and of the
grid refinement (`nonvanish_grid`) into the `A`-bounds (`A_bounds`):

* `isBlockHom_map_intCast_rat`: block-homogeneity of an integral polynomial transfers to its
  image in `ℚ`;
* `aeval_pderivIter_intCast_ne_zero_iff`: non-vanishing of an iterated derivative at an
  integral point is the same over `ℚ` and over `ℂ`.
-/

open scoped BigOperators

namespace Submission.Subspace

variable {m N : ℕ}

/-- Block-homogeneity transfers to the image in `ℚ`. -/
lemma isBlockHom_map_intCast_rat {F : MvPolynomial (Fin m × Fin N) ℤ} {d : Fin m → ℕ}
    (h : ∀ u ∈ F.support, ∀ h' : Fin m, ∑ i : Fin N, u (h', i) = d h') :
    IsBlockHom d (F.map (Int.castRingHom ℚ)) := by
  intro u hu h'
  rw [MvPolynomial.support_map_of_injective _ Int.cast_injective] at hu
  exact h u hu h'

/-- Non-vanishing of an iterated derivative of an integral polynomial at an integral point is a
`ℚ`-statement: it is equivalent over `ℚ` and over `ℂ`. -/
lemma aeval_pderivIter_intCast_ne_zero_iff (F : MvPolynomial (Fin m × Fin N) ℤ)
    (e : (Fin m × Fin N) →₀ ℕ) (x : Fin m × Fin N → ℤ) :
    MvPolynomial.aeval (fun q => (Int.castRingHom ℂ) (x q))
        (Commons.Algebra.MvPolynomial.pderivIter e (F.map (Int.castRingHom ℂ))) ≠ 0 ↔
    MvPolynomial.aeval (fun q => (Int.castRingHom ℚ) (x q))
        (Commons.Algebra.MvPolynomial.pderivIter e (F.map (Int.castRingHom ℚ))) ≠ 0 := by
  have hQexp : Commons.Algebra.MvPolynomial.pderivIter e (F.map (Int.castRingHom ℚ))
      = (Commons.Algebra.MvPolynomial.pderivIter e F).map (algebraMap ℤ ℚ) :=
    Commons.Algebra.MvPolynomial.pderivIter_map _ _ _
  have hmap : Commons.Algebra.MvPolynomial.pderivIter e (F.map (Int.castRingHom ℂ))
      = (Commons.Algebra.MvPolynomial.pderivIter e (F.map (Int.castRingHom ℚ))).map
          (algebraMap ℚ ℂ) := by
    rw [Commons.Algebra.MvPolynomial.pderivIter_map,
      Commons.Algebra.MvPolynomial.pderivIter_map, MvPolynomial.map_map]
    rw [show (algebraMap ℚ ℂ).comp (Int.castRingHom ℚ) = (Int.castRingHom ℂ) from by
      ext n; simp]
  have hval : MvPolynomial.aeval (fun q => (Int.castRingHom ℂ) (x q))
        (((Commons.Algebra.MvPolynomial.pderivIter e F).map (algebraMap ℤ ℚ)).map
          (algebraMap ℚ ℂ))
      = algebraMap ℚ ℂ (MvPolynomial.aeval (fun q => (Int.castRingHom ℚ) (x q))
          ((Commons.Algebra.MvPolynomial.pderivIter e F).map (algebraMap ℤ ℚ))) := by
    rw [MvPolynomial.map_map,
      show (algebraMap ℚ ℂ).comp (algebraMap ℤ ℚ) = (algebraMap ℤ ℂ) from by ext n; simp,
      MvPolynomial.aeval_map_algebraMap ℂ, MvPolynomial.aeval_map_algebraMap ℚ]
    have h1 := MvPolynomial.map_aeval (R := ℤ) (σ := Fin m × Fin N)
      (g := fun q => (Int.castRingHom ℚ) (x q)) (φ := algebraMap ℚ ℂ)
      (p := Commons.Algebra.MvPolynomial.pderivIter e F)
    rw [show (algebraMap ℚ ℂ).comp (algebraMap ℤ ℚ) = (Int.castRingHom ℂ) from by ext n; simp,
      show (fun i => (algebraMap ℚ ℂ) ((Int.castRingHom ℚ) (x i)))
          = (fun i => (Int.castRingHom ℂ) (x i)) from by funext i; simp] at h1
    rw [h1, MvPolynomial.aeval_eq_eval₂Hom]
    exact congrArg (fun f : ℤ →+* ℂ => MvPolynomial.eval₂Hom f
      (fun q => (Int.castRingHom ℂ) (x q)) (Commons.Algebra.MvPolynomial.pderivIter e F))
      (show (algebraMap ℤ ℂ) = (Int.castRingHom ℂ) from rfl)
  rw [hmap, hQexp, hval]
  constructor
  · intro hh h0
    exact hh (by rw [h0, map_zero])
  · intro hh h0
    exact hh ((algebraMap ℚ ℂ).injective (by rw [h0, map_zero]))

/-- Over a field, the divided derivative has nonzero value at a point iff the plain iterated
derivative does. -/
lemma aeval_pderivIterDiv_ne_zero_iff_plain {K : Type*} [Field K] [CharZero K]
    (e : (Fin m × Fin N) →₀ ℕ) (F : MvPolynomial (Fin m × Fin N) K)
    (u : Fin m × Fin N → K) :
    MvPolynomial.aeval u (pderivIterDiv e F) ≠ 0 ↔
      MvPolynomial.aeval u (Commons.Algebra.MvPolynomial.pderivIter e F) ≠ 0 := by
  have hfac : 0 < facOf e := by
    rw [facOf]; exact Finset.prod_pos fun i _ => Nat.factorial_pos _
  have hne : (((facOf e : ℕ) : K))⁻¹ ≠ 0 := by
    refine inv_ne_zero ?_
    exact_mod_cast (Nat.pos_iff_ne_zero.mp hfac)
  rw [pderivIterDiv_eq_inv_mul, map_mul, MvPolynomial.aeval_C, mul_ne_zero_iff]
  exact ⟨fun h => h.2, fun h => ⟨hne, h⟩⟩

/-- Non-vanishing of the *divided* derivative of an integral polynomial at an integral point:
equivalent whether computed over `ℂ` or over `ℚ`, with the plain derivative on the `ℚ` side. -/
lemma aeval_pderivIterDiv_intCast_ne_zero_iff (F : MvPolynomial (Fin m × Fin N) ℤ)
    (e : (Fin m × Fin N) →₀ ℕ) (x : Fin m × Fin N → ℤ) :
    MvPolynomial.aeval (fun q => (Int.castRingHom ℂ) (x q))
        (pderivIterDiv e (F.map (Int.castRingHom ℂ))) ≠ 0 ↔
    MvPolynomial.aeval (fun q => (Int.castRingHom ℚ) (x q))
        (Commons.Algebra.MvPolynomial.pderivIter e (F.map (Int.castRingHom ℚ))) ≠ 0 := by
  rw [aeval_pderivIterDiv_ne_zero_iff_plain]
  exact aeval_pderivIter_intCast_ne_zero_iff F e x

end Submission.Subspace
