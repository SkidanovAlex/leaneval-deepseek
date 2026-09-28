import Mathlib
import Submission.Work.Q44Geom.ReducDefs

/-!
# Integrality of the cofactor of a primitive linear form

If a primitive integral linear form `ℓ` divides an integral quartic form `c` (as an identity of
rational polynomials), then the cofactor `H` of degree `3` has integral coefficients.

This is Gauss's lemma, transported along the injective univariate substitution
`X_i ↦ T ^ (5 ^ i)` of `Work.Q44Geom.ReducDefs`: the substitution of `ℓ` is a primitive
univariate integer polynomial, and the substitution of `c` is (the image of) an integer
polynomial; hence so is the substitution of `H`, and the coefficients of `H` are read off at
the weights `wtMon m`.
-/

set_option autoImplicit false

open MvPolynomial Finset

noncomputable section

namespace Work.Q44Geom

open Work.HP

/-- The univariate substitution of an integral polynomial is the image, along `ℤ → ℚ`, of the
substitution of the integral polynomial. -/
lemma substQ_polyOfR_intCast {d : ℕ} (A : Mon d 4 → ℤ) :
    substQ (polyOfR (fun m => (A m : ℚ))) = (substZ (polyOfR A)).map (Int.castRingHom ℚ) := by
  rw [← polyOfR_map_intCast A, substQ_map_intCast]

theorem integral_cofactor_deg1 (c : Work.HP.Mon 4 4 → ℤ) (H : MvPolynomial (Fin 5) ℚ)
    (ℓ : Work.HP.Mon 1 4 → ℤ) (hℓ : Work.HP.IsPrim ℓ) (hH : H.IsHomogeneous 3)
    (hF : Work.HP.formOf 4 4 c = Work.Q44Geom.polyOfR (fun m => (ℓ m : ℚ)) * H) :
    ∃ h : Work.HP.Mon 3 4 → ℤ, H = Work.Q44Geom.polyOfR (fun m => (h m : ℚ)) := by
  classical
  -- Restate the hypothesis with both sides written as coefficient vectors over `ℤ`.
  have hF' : polyOfR (fun m : Mon 4 4 => (c m : ℚ))
      = polyOfR (fun m : Mon 1 4 => (ℓ m : ℚ)) * H := by
    rw [← formOf_eq_polyOfR c]
    exact hF
  -- The substituted identity: `ℓ̂ * Ĥ = ĉ` with `ℓ̂, ĉ` substitutions of integer polynomials.
  have hFsym : substQ (polyOfR (fun m : Mon 1 4 => (ℓ m : ℚ)) * H)
      = (substZ (polyOfR c)).map (Int.castRingHom ℚ) := by
    rw [← hF']
    exact substQ_polyOfR_intCast c
  have h2 : (substZ (polyOfR ℓ)).map (Int.castRingHom ℚ) * substQ H
      = (substZ (polyOfR c)).map (Int.castRingHom ℚ) := by
    rw [← substQ_polyOfR_intCast ℓ, ← map_mul, hFsym]
  have h3 : (substZ (polyOfR ℓ)).map (Int.castRingHom ℚ) * substQ H
      ∈ Polynomial.lifts (Int.castRingHom ℚ) := by
    rw [h2]
    exact (Polynomial.mem_lifts ((substZ (polyOfR c)).map (Int.castRingHom ℚ))).mpr
      ⟨substZ (polyOfR c), rfl⟩
  -- Gauss's lemma: a primitive factor of a polynomial in the image of `ℤ[X]` stays in it.
  have hkey : substQ H ∈ Polynomial.lifts (Int.castRingHom ℚ) :=
    (isPrimitive_substZ_polyOfR hℓ).map_mul_mem_lifts_iff.mp h3
  obtain ⟨G, hG⟩ := (Polynomial.mem_lifts (substQ H)).mp hkey
  -- Read off the coefficients of `H` at the weights of the degree-three monomials.
  have hcoeff : ∀ m : Mon 3 4, H.coeff m.toFinsupp = (G.coeff (wtMon m) : ℚ) := by
    intro m
    have h4 : (substQ H).coeff (wtMon m) = H.coeff m.toFinsupp := by
      have h5 := coeff_substQ_polyOfR (d := 3) (by norm_num)
        (fun m : Mon 3 4 => H.coeff m.toFinsupp) m
      rwa [polyOfR_ofHomog hH] at h5
    rw [← h4, ← hG, Polynomial.coeff_map]
    simp
  refine ⟨fun m => G.coeff (wtMon m), ?_⟩
  exact polyOfR_inj_of_homog hH
    (isHomogeneous_polyOfR (d := 3) (fun m : Mon 3 4 => (G.coeff (wtMon m) : ℚ)))
    (fun m => by rw [coeff_polyOfR]; simpa using hcoeff m)

end Work.Q44Geom
