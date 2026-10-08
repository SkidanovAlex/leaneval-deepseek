import Mathlib
import Submission.Work.NormalComplement.AppVII.TildeEAux

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# A central element of `ℂ[A]` acts on each simple submodule by a scalar

For a finite group `A`, a central element `u` of the group algebra `ℂ[A]` and a simple
submodule `N` of the regular module `ℂ[A]`, left multiplication by `u` restricts to a
`ℂ[A]`-linear endomorphism of `N`, hence (Schur's lemma over the algebraically closed field
`ℂ`) is multiplication by a scalar; the scalar is determined by its trace:

`u * x = ((∑ g, u.coeff g * ν g) / finrank ℂ N) • x` for `x ∈ N`,

where `ν` is the character of `N`.  This is the technical input for the identities satisfied by
the central primitive idempotents of `ℂ[A]`, and for `zC_pairing`, the first orthogonality
relation in the normalisation used downstream.
-/

noncomputable section

open Classical

open scoped BigOperators MonoidAlgebra

namespace Work.NormalComplement.AppVII

variable {A : Type*} [Group A] [Fintype A]

/-- The first orthogonality relation for the class sums `zℂ χ = ∑_g χ(g⁻¹) • single g 1`:
pairing `zℂ χ` against an irreducible character `ν` gives `|A| δ_{χν}`. -/
theorem zC_pairing (χ : A → ℂ) (hχ : χ ∈ Work.CharCore.Irr A) (ν : A → ℂ)
    (hν : ν ∈ Work.CharCore.Irr A) :
    (∑ g : A, (zℂ χ).coeff g * ν g) = (Nat.card A : ℂ) * (if χ = ν then 1 else 0) := by
  classical
  have h1 : (∑ g : A, (zℂ χ).coeff g * ν g) = ∑ g : A, χ (g⁻¹) * ν g :=
    Finset.sum_congr rfl fun g _ => by rw [coeff_zℂ]
  have h2 : (∑ g : A, χ (g⁻¹) * ν g) = ∑ g : A, χ g * ν (g⁻¹) := by
    have := Equiv.sum_comp (Equiv.inv A) (fun h : A => χ h * ν h⁻¹)
    simpa using this
  have h3 : (∑ g : A, χ g * ν (g⁻¹)) = ∑ g : A, χ g * starRingEnd ℂ (ν g) :=
    Finset.sum_congr rfl fun g _ => by rw [Work.CharCore.star_Irr ν hν g]
  have h5 : (∑ g : A, χ g * starRingEnd ℂ (ν g)) =
      (Fintype.card A : ℂ) * Work.CharCore.cfInner χ ν := by
    rw [Work.CharCore.cfInner]
    have hcard : (Fintype.card A : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    field_simp
  rw [h1, h2, h3, h5, Work.CharCore.irr_orthonormal χ ν hχ hν, Fintype.card_eq_nat_card]

/-- A central element `u` of `ℂ[A]` acts on a simple submodule `N` of the regular module by
the scalar `(∑ g, u.coeff g * ν g) / finrank ℂ N`, where `ν` is the character of `N`. -/
theorem central_acts_scalar (u : MonoidAlgebra ℂ A)
    (hu : ∀ a : MonoidAlgebra ℂ A, u * a = a * u)
    (N : Submodule (MonoidAlgebra ℂ A) (MonoidAlgebra ℂ A))
    (hN : N ∈ Work.CharCore.irrSubmodules A)
    {x : MonoidAlgebra ℂ A} (hx : x ∈ N) :
    u * x = ((∑ g : A, u.coeff g * (Work.CharCore.submoduleRep N).character g) /
      (Module.finrank ℂ N : ℂ)) • x := by
  classical
  haveI hS : IsSimpleModule (MonoidAlgebra ℂ A) N :=
    Work.CharCore.isSimpleModule_of_mem_irrSubmodules N hN
  haveI hnt : Nontrivial N := IsSimpleModule.nontrivial (MonoidAlgebra ℂ A) N
  -- left multiplication by `u` is `ℂ[A]`-linear on `N` because `u` is central
  let T : N →ₗ[MonoidAlgebra ℂ A] N :=
    { toFun := fun y => ⟨u • (y : MonoidAlgebra ℂ A), N.smul_mem u y.2⟩
      map_add' := by
        intro y z
        apply Subtype.ext
        change u • ((y : MonoidAlgebra ℂ A) + (z : MonoidAlgebra ℂ A)) =
          u • (y : MonoidAlgebra ℂ A) + u • (z : MonoidAlgebra ℂ A)
        rw [smul_add]
      map_smul' := by
        intro a y
        apply Subtype.ext
        change u * (a * (y : MonoidAlgebra ℂ A)) =
          a * (u * (y : MonoidAlgebra ℂ A))
        rw [← mul_assoc, ← mul_assoc, hu a] }
  -- Schur: a `ℂ[A]`-linear endomorphism of the simple module `N` is a scalar
  obtain ⟨c, hc⟩ :=
    (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed (A := MonoidAlgebra ℂ A)
      (V := N) ℂ).2 T
  -- its trace, computed from the scalar form
  have htr1 : (LinearMap.trace ℂ N) (T.restrictScalars ℂ) =
      c * (Module.finrank ℂ N : ℂ) := by
    have hT : (T.restrictScalars ℂ : N →ₗ[ℂ] N) = c • (1 : N →ₗ[ℂ] N) := by
      ext y
      have h1 : (T.restrictScalars ℂ) y = T y := rfl
      rw [h1, ← hc, Module.algebraMap_end_apply]
      rfl
    rw [hT, map_smul, show (1 : N →ₗ[ℂ] N) = LinearMap.id from rfl, LinearMap.trace_id]
    rfl
  -- the decomposition of `u` into the `single g 1`
  have hdecomp : u = ∑ g : A, u.coeff g • MonoidAlgebra.single g (1 : ℂ) := by
    ext h
    rw [coeff_sum_smul_single]
  -- `T` equals the action of `u`, and that action is `∑ g, u.coeff g • ρ g`
  have hTas : (T.restrictScalars ℂ) =
      (Representation.asAlgebraHom (Work.CharCore.submoduleRep N)) u := by
    apply LinearMap.ext
    intro y
    apply Subtype.ext
    simp only [Work.CharCore.submoduleRep]
    rw [Work.Clifford.asAlgebraHom_ofModule'_apply]
    rfl
  have hsum : (Representation.asAlgebraHom (Work.CharCore.submoduleRep N)) u =
      ∑ g : A, u.coeff g • (Work.CharCore.submoduleRep N) g := by
    conv_lhs => rw [hdecomp]
    rw [map_sum]
    exact Finset.sum_congr rfl fun g _ => by
      rw [map_smul, Representation.asAlgebraHom_single_one]
  -- its trace, computed from the decomposition
  have htr2 : (LinearMap.trace ℂ N) (T.restrictScalars ℂ) =
      ∑ g : A, u.coeff g * (Work.CharCore.submoduleRep N).character g := by
    rw [hTas, hsum, map_sum]
    exact Finset.sum_congr rfl fun g _ => by
      rw [map_smul, smul_eq_mul]
      rfl
  -- conclude `c` and the scalar action
  have hfin : (Module.finrank ℂ N : ℂ) ≠ 0 := by
    have hpos : 0 < Module.finrank ℂ N := Module.finrank_pos_iff.mpr hnt
    exact_mod_cast hpos.ne'
  have hcf : c = (∑ g : A, u.coeff g * (Work.CharCore.submoduleRep N).character g) /
      (Module.finrank ℂ N : ℂ) := by
    rw [eq_div_iff hfin, ← htr1, htr2]
  rw [← hcf]
  have hkey : T ⟨x, hx⟩ = c • (⟨x, hx⟩ : N) := by
    rw [← hc, Module.algebraMap_end_apply]
  have hcoe : (T ⟨x, hx⟩ : MonoidAlgebra ℂ A) = c • x := by
    rw [hkey]
    rfl
  have hval : (T ⟨x, hx⟩ : MonoidAlgebra ℂ A) = u * x := by
    show u • (x : MonoidAlgebra ℂ A) = u * x
    exact smul_eq_mul u x
  rw [← hcoe, ← hval]

end Work.NormalComplement.AppVII
