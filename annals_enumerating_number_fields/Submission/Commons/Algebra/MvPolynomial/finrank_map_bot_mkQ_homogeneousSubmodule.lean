import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Submission.Commons.Algebra.MvPolynomial.finrank_homogeneousSubmodule_eq_choose

namespace Commons.Algebra.MvPolynomial

/-- The `t`-th graded piece of a polynomial ring in `m` variables has dimension
`(m + t - 1).choose t`, and its image under the quotient by the zero ideal (which
is an isomorphism onto the ring itself) has the same dimension. -/
theorem finrank_map_bot_mkQ_homogeneousSubmodule {k : Type} [Field k] {m : ℕ} (t : ℕ) :
    Module.finrank k (Submodule.map ((⊥ : Ideal (MvPolynomial (Fin m) k)).mkQ.restrictScalars k)
      (MvPolynomial.homogeneousSubmodule (Fin m) k t)) = (m + t - 1).choose t := by
  -- The quotient map by the zero ideal is a bijective `k`-linear map, hence a linear
  -- equivalence; mapping along it preserves the dimension.
  let f : MvPolynomial (Fin m) k →ₗ[k]
      MvPolynomial (Fin m) k ⧸ (⊥ : Submodule (MvPolynomial (Fin m) k) (MvPolynomial (Fin m) k)) :=
    (⊥ : Ideal (MvPolynomial (Fin m) k)).mkQ.restrictScalars k
  have hfinj : Function.Injective f := by
    intro a b hab
    have h : (Submodule.Quotient.mk a : MvPolynomial (Fin m) k ⧸
        (⊥ : Submodule (MvPolynomial (Fin m) k) (MvPolynomial (Fin m) k))) =
        Submodule.Quotient.mk b := hab
    rw [Submodule.Quotient.eq] at h
    exact sub_eq_zero.mp (by simpa using h)
  have hfsurj : Function.Surjective f := by
    intro y
    obtain ⟨x, hx⟩ := Submodule.mkQ_surjective
      (⊥ : Submodule (MvPolynomial (Fin m) k) (MvPolynomial (Fin m) k)) y
    exact ⟨x, hx⟩
  let e : MvPolynomial (Fin m) k ≃ₗ[k]
      MvPolynomial (Fin m) k ⧸ (⊥ : Submodule (MvPolynomial (Fin m) k) (MvPolynomial (Fin m) k)) :=
    LinearEquiv.ofBijective f ⟨hfinj, hfsurj⟩
  have he : (e : MvPolynomial (Fin m) k →ₗ[k]
      MvPolynomial (Fin m) k ⧸ (⊥ : Submodule (MvPolynomial (Fin m) k) (MvPolynomial (Fin m) k))) = f :=
    rfl
  rw [← finrank_homogeneousSubmodule_eq_choose (k := k) m t]
  rw [show ((⊥ : Ideal (MvPolynomial (Fin m) k)).mkQ.restrictScalars k) = f from rfl, ← he]
  rw [LinearEquiv.finrank_map_eq e]

end Commons.Algebra.MvPolynomial