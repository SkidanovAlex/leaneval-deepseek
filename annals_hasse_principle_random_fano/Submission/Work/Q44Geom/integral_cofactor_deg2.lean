import Mathlib
import Submission.Work.Q44Geom.ReducDefs

/-!
# Integrality of the quadratic cofactor of a quartic form with a primitive linear factor

If a quartic form `F` in `5` variables with integer coefficients factors as
`F = L · H` where `L` is a *primitive* integer linear form (degree `1`) and `H` is a
homogeneous rational quadratic form, then `H` already has integer coefficients
(Gauss's lemma).  The proof uses the univariate substitution `X_i ↦ T ^ (5 ^ i)` of
`Work.Q44Geom.ReducDefs`, which turns the identity into a product of polynomials in
`T`: the image of `L` is primitive, and `Polynomial.IsPrimitive.map_mul_mem_lifts_iff`
then forces the image of `H` to have integer coefficients.  Injectivity of the weight
map in degree `≤ 4` recovers the coefficients of `H` itself.
-/

namespace Work.Q44Geom

open MvPolynomial Finset Polynomial
open Work.HP

/-- The `5 ^ i`-substitution of a primitive degree-`d` form (`d ≤ 4`) with integer
coefficients is a primitive polynomial: its coefficients are exactly the `q m`, at the
pairwise distinct weights `wtMon m`. -/
lemma isPrimitive_substZ_polyOfR' {d : ℕ} (hd : d ≤ 4) {q : Mon d 4 → ℤ}
    (hq : IsPrim q) : (substZ (polyOfR q)).IsPrimitive := by
  rw [Polynomial.isPrimitive_iff_isUnit_of_C_dvd]
  intro r hr
  rw [Polynomial.C_dvd_iff_dvd_coeff] at hr
  have h1 : r ∣ Finset.univ.gcd q :=
    Finset.dvd_gcd fun m _ => by
      have h2 := hr (wtMon m)
      rw [coeff_substZ_polyOfR hd q m] at h2
      exact h2
  rw [show Finset.univ.gcd q = 1 from hq] at h1
  exact isUnit_of_dvd_one h1

theorem integral_cofactor_deg2 (c : Work.HP.Mon 4 4 → ℤ) (H : MvPolynomial (Fin 5) ℚ)
    (q : Work.HP.Mon 2 4 → ℤ) (hq : Work.HP.IsPrim q) (hH : H.IsHomogeneous 2)
    (hF : Work.HP.formOf 4 4 c = Work.Q44Geom.polyOfR (fun m => (q m : ℚ)) * H) :
    ∃ h : Work.HP.Mon 2 4 → ℤ, H = Work.Q44Geom.polyOfR (fun m => (h m : ℚ)) := by
  have hAprim : (substZ (polyOfR q)).IsPrimitive :=
    isPrimitive_substZ_polyOfR' (by norm_num) hq
  -- The substitution of the two factors, over `ℤ` and over `ℚ`.
  have hqeq : substQ (polyOfR (fun m : Mon 2 4 => (q m : ℚ)))
      = Polynomial.map (algebraMap ℤ ℚ) (substZ (polyOfR q)) := by
    rw [← polyOfR_map_intCast q]
    exact substQ_map_intCast (polyOfR q)
  have hceq : substQ (Work.HP.formOf 4 4 c)
      = Polynomial.map (algebraMap ℤ ℚ) (substZ (polyOfR c)) := by
    rw [formOf_eq_polyOfR, ← polyOfR_map_intCast c]
    exact substQ_map_intCast (polyOfR c)
  have hkey : Polynomial.map (algebraMap ℤ ℚ) (substZ (polyOfR q)) * substQ H
      = substQ (Work.HP.formOf 4 4 c) := by
    calc Polynomial.map (algebraMap ℤ ℚ) (substZ (polyOfR q)) * substQ H
        = substQ (polyOfR (fun m : Mon 2 4 => (q m : ℚ))) * substQ H := by rw [hqeq]
      _ = substQ (polyOfR (fun m : Mon 2 4 => (q m : ℚ)) * H) := by rw [substQ.map_mul]
      _ = substQ (Work.HP.formOf 4 4 c) := by rw [hF]
  have hmem : Polynomial.map (algebraMap ℤ ℚ) (substZ (polyOfR q)) * substQ H
      ∈ Polynomial.lifts (algebraMap ℤ ℚ) := by
    rw [hkey, Polynomial.mem_lifts]
    exact ⟨substZ (polyOfR c), hceq.symm⟩
  -- Gauss's lemma: `substQ H` has integer coefficients.
  obtain ⟨H', hH'⟩ := hAprim.map_mul_mem_lifts_iff.mp hmem
  have hH'' : Polynomial.map (algebraMap ℤ ℚ) H' = substQ H := by
    simpa only [Polynomial.coe_mapRingHom] using hH'
  refine ⟨fun m => H'.coeff (wtMon m), ?_⟩
  apply polyOfR_inj_of_homog hH (isHomogeneous_polyOfR _)
  intro m
  rw [coeff_polyOfR]
  have h2 : (substQ H).coeff (wtMon m) = H.coeff m.toFinsupp := by
    have hh := coeff_substQ_polyOfR (d := 2) (by norm_num)
      (fun m : Mon 2 4 => H.coeff m.toFinsupp) m
    rwa [polyOfR_ofHomog hH] at hh
  have h1 : algebraMap ℤ ℚ (H'.coeff (wtMon m)) = (substQ H).coeff (wtMon m) := by
    rw [← Polynomial.coeff_map (algebraMap ℤ ℚ) (wtMon m), hH'']
  exact (h1.trans h2).symm

end Work.Q44Geom
