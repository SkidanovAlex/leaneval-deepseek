/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ORVonNeumann area (N5 of the one-relator coherence project)

# The `*`-structure on a group algebra

Mathlib has no `StarRing` instance on `MonoidAlgebra R G`.  For the analytic core of the
one-relator coherence project we need the group algebra `ℂ[G]` as a `*`-subring of the
group von Neumann algebra `N(G)` and of `U(G)`, with the involution
`(∑ r_g · g)⋆ = ∑ (r_g)⋆ · g⁻¹`.

We define it here (for any group `G` and any `*`-ring `R`) together with its basic API:
`star_single`, `star_coeff`, `star_add`, `star_mul`, `star_star` and the `StarRing` instance.
-/
import Mathlib
import Submission.Work.ORVonNeumann.Basic

set_option autoImplicit false

universe u v

namespace Work.ORVonNeumann

open MonoidAlgebra

variable {R : Type*} {G : Type*}

/-- The involution of a group algebra: `(∑ r_g · g)⋆ = ∑ (r_g)⋆ · g⁻¹`. -/
noncomputable def GroupAlgebraStar.starF [Semiring R] [StarRing R] [Group G]
    (f : MonoidAlgebra R G) : MonoidAlgebra R G :=
  MonoidAlgebra.ofCoeff (Finsupp.domCongr (Equiv.inv G) (Finsupp.mapRange star (by simp) f.coeff))

namespace GroupAlgebraStar

variable [Semiring R] [StarRing R] [Group G]

theorem starF_coeff (f : MonoidAlgebra R G) :
    (starF f).coeff = Finsupp.domCongr (Equiv.inv G) (Finsupp.mapRange star (by simp) f.coeff) :=
  rfl

theorem starF_apply (f : MonoidAlgebra R G) (g : G) :
    (starF f).coeff g = star (f.coeff g⁻¹) := by
  rw [starF_coeff, Finsupp.domCongr_apply, Finsupp.equivMapDomain_apply, Finsupp.mapRange_apply]
  simp

theorem starF_add (f g : MonoidAlgebra R G) : starF (f + g) = starF f + starF g := by
  classical
  apply MonoidAlgebra.ext
  ext x
  rw [starF_apply, MonoidAlgebra.coeff_add, Finsupp.add_apply, star_add, MonoidAlgebra.coeff_add,
    Finsupp.add_apply, starF_apply, starF_apply]

theorem starF_zero : starF (0 : MonoidAlgebra R G) = 0 := by
  classical
  apply MonoidAlgebra.ext
  ext x
  rw [starF_apply, MonoidAlgebra.coeff_zero, Finsupp.zero_apply, star_zero]
  rfl

theorem starF_starF (f : MonoidAlgebra R G) : starF (starF f) = f := by
  classical
  apply MonoidAlgebra.ext
  ext g
  rw [starF_apply, starF_apply, inv_inv, star_star]

@[simp]
theorem starF_single (g : G) (r : R) :
    starF (single g r : MonoidAlgebra R G) = single g⁻¹ (star r) := by
  classical
  apply MonoidAlgebra.ext
  ext x
  rw [starF_apply, MonoidAlgebra.coeff_single, Finsupp.single_apply, apply_ite star, star_zero,
    MonoidAlgebra.coeff_single, Finsupp.single_apply]
  by_cases h : x = g⁻¹
  · subst h; rw [inv_inv, if_pos rfl, if_pos rfl]
  · have h' : x⁻¹ ≠ g := fun hc => h (inv_eq_iff_eq_inv.mp hc)
    rw [if_neg (Ne.symm h'), if_neg (Ne.symm h)]

theorem starF_ofCoeff_add (c₁ c₂ : G →₀ R) :
    MonoidAlgebra.ofCoeff (c₁ + c₂) = MonoidAlgebra.ofCoeff c₁ + MonoidAlgebra.ofCoeff c₂ := by
  apply MonoidAlgebra.ext
  rw [MonoidAlgebra.coeff_add]

theorem starF_ofCoeff_zero : MonoidAlgebra.ofCoeff (0 : G →₀ R) = 0 := by
  apply MonoidAlgebra.ext
  rw [MonoidAlgebra.coeff_zero]

@[simp]
theorem starF_one : starF (1 : MonoidAlgebra R G) = 1 := by
  have h1 : (1 : MonoidAlgebra R G) = single 1 1 := (MonoidAlgebra.one_def).symm
  rw [h1, starF_single, inv_one, star_one]

theorem ofCoeff_single_eq (a : G) (b : R) :
    MonoidAlgebra.ofCoeff (Finsupp.single a b) = MonoidAlgebra.single a b := rfl

theorem starF_mul_single (c : G →₀ R) (g : G) (r : R) :
    starF (MonoidAlgebra.ofCoeff c * single g r) =
      starF (single g r) * starF (MonoidAlgebra.ofCoeff c) := by
  induction c using Finsupp.induction_linear with
  | zero => rw [starF_ofCoeff_zero, zero_mul, starF_zero, mul_zero]
  | add c₁ c₂ h₁ h₂ =>
    rw [starF_ofCoeff_add, add_mul, starF_add, h₁, h₂, starF_add, mul_add]
  | single a b =>
    rw [ofCoeff_single_eq, MonoidAlgebra.single_mul_single, starF_single, starF_single,
      starF_single, MonoidAlgebra.single_mul_single, mul_inv_rev, star_mul]

theorem starF_mul_single_right (f : MonoidAlgebra R G) (g : G) (r : R) :
    starF (f * single g r) = starF (single g r) * starF f :=
  starF_mul_single f.coeff g r

theorem starF_mul_ofCoeff (f : MonoidAlgebra R G) (c : G →₀ R) :
    starF (f * MonoidAlgebra.ofCoeff c) = starF (MonoidAlgebra.ofCoeff c) * starF f := by
  induction c using Finsupp.induction_linear with
  | zero => rw [starF_ofCoeff_zero, mul_zero, starF_zero, zero_mul]
  | add c₁ c₂ h₁ h₂ =>
    rw [starF_ofCoeff_add, mul_add, starF_add, h₁, h₂, starF_add, add_mul]
  | single a b =>
    rw [ofCoeff_single_eq]
    exact starF_mul_single_right f a b

theorem starF_mul (f g : MonoidAlgebra R G) : starF (f * g) = starF g * starF f :=
  starF_mul_ofCoeff f g.coeff

end GroupAlgebraStar

/-! ### The `StarRing` instance -/

noncomputable instance instStarMonoidAlgebra [Semiring R] [StarRing R] [Group G] :
    Star (MonoidAlgebra R G) :=
  ⟨GroupAlgebraStar.starF⟩

noncomputable instance instInvolutiveStarMonoidAlgebra [Semiring R] [StarRing R] [Group G] :
    InvolutiveStar (MonoidAlgebra R G) :=
  ⟨GroupAlgebraStar.starF_starF⟩

noncomputable instance instStarMulMonoidAlgebra [Semiring R] [StarRing R] [Group G] :
    StarMul (MonoidAlgebra R G) :=
  ⟨GroupAlgebraStar.starF_mul⟩

noncomputable instance instStarRingMonoidAlgebra [Semiring R] [StarRing R] [Group G] :
    StarRing (MonoidAlgebra R G) :=
  ⟨GroupAlgebraStar.starF_add⟩

@[simp]
theorem MonoidAlgebra.star_single [Semiring R] [StarRing R] [Group G] (g : G) (r : R) :
    star (single g r : MonoidAlgebra R G) = single g⁻¹ (star r) :=
  GroupAlgebraStar.starF_single g r

/-- The group-algebra involution is conjugate-linear in the scalars: `ℂ[G]` is a
`*`-algebra over `ℂ`. -/
theorem MonoidAlgebra.star_smul [CommSemiring R] [StarRing R] [Group G] (c : R)
    (f : MonoidAlgebra R G) : star (c • f) = star c • star f := by
  have halg : ∀ d : R, algebraMap R (MonoidAlgebra R G) d = MonoidAlgebra.single (1 : G) d := by
    intro d
    simpa using congr_fun (MonoidAlgebra.coe_algebraMap (R := R) (A := R) (M := G)) d
  rw [Algebra.smul_def, star_mul, halg, Algebra.smul_def, halg, MonoidAlgebra.star_single, inv_one,
    ← halg (star c)]
  exact (Algebra.commutes (star c) (star f)).symm

theorem MonoidAlgebra.star_coeff [Semiring R] [StarRing R] [Group G]
    (f : MonoidAlgebra R G) (g : G) : (star f).coeff g = star (f.coeff g⁻¹) :=
  GroupAlgebraStar.starF_apply f g

end Work.ORVonNeumann
