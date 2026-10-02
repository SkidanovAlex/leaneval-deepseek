import Mathlib
import Submission.Work.LerayHirsch.FibreZeta
import Submission.Work.LerayHirsch.lhMap_comap

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# The restriction of the powers of `ζ` to a fibre

`Work.LerayHirsch.CohMap_fibreIncl_zeta` identifies the restriction of `ζ = c₁(ℓ(E))` to a fibre
with the hyperplane class `ζ(ℂP^{m-1}) = Work.LerayHirsch.zetaP m` of that fibre.  This module
upgrades the identification to **all powers**:

`(fibreIncl)^*(ζ^i) = (projUniv ∘ projClassFibre)^*(ζ_{ε^m}^i)`,

i.e. the classes `1, ζ, …, ζ^{m-1}` restrict to the powers of the fibre's hyperplane class.  This is
the second half of the Leray–Hirsch statement of
`Submission/Work/LerayHirsch/README.md` §0.3: together with `LerayHirschFull (trivCore m)` (the
trivial-bundle case, i.e. Künneth for `ℂP^{m-1}`, subproject KUNNETH) it says that the restrictions
of `1, ζ, …, ζ^{m-1}` to a fibre form a basis of `H^*(ℂP^{m-1};ℤ)`.

The key auxiliary results are

* `Work.LerayHirsch.bijective_CohMap_of_homeomorph` — a homeomorphism induces a bijection on
  singular cohomology (the tool that transports statements between `P(ε^m)` and `ℂP^{m-1}`);
* `Work.LerayHirsch.zeta_trivCore_comap_projUniv` — `ζ(ℂP^{m-1}) = (projUniv)^*ζ(ε^m)`;
* `Work.LerayHirsch.CohMap_comp_fibreIncl_zeta` — the `i = 1` case of the composite statement;
* `Work.LerayHirsch.CohMap_fibreIncl_zetaPow` — the statement for all `i`, by induction using the
  naturality of the graded product `Work.Whitney.cupChern`.
-/

namespace Work.LerayHirsch

open Work.TangentClasses Work.Thom

open scoped LinearAlgebra.Projectivization

noncomputable section

variable {B : Type} [TopologicalSpace B] {ι : Type} {m : ℕ}

/-- **A homeomorphism induces a bijection on singular cohomology** (in every degree), with the
inverse given by the pullback along the inverse homeomorphism. -/
theorem bijective_CohMap_of_homeomorph {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (n : ℕ) : Function.Bijective (CohMap (e : C(X, Y)) ℤ n).hom := by
  have hcomp₁ : (e.symm : C(Y, X)).comp (e : C(X, Y)) = ContinuousMap.id X := by
    ext x; exact e.symm_apply_apply x
  have hcomp₂ : (e : C(X, Y)).comp (e.symm : C(Y, X)) = ContinuousMap.id Y := by
    ext y; exact e.apply_symm_apply y
  have h1 : (CohMap (e.symm : C(Y, X)) ℤ n).hom.comp (CohMap (e : C(X, Y)) ℤ n).hom
      = LinearMap.id := by
    ext x
    rw [LinearMap.comp_apply, LinearMap.id_apply,
      Work.Thom.CohMap_comp_apply (e.symm : C(Y, X)) (e : C(X, Y)) ℤ n x, hcomp₂, CohMap_id]
    simp only [ModuleCat.hom_id, LinearMap.id_apply]
  have h2 : (CohMap (e : C(X, Y)) ℤ n).hom.comp (CohMap (e.symm : C(Y, X)) ℤ n).hom
      = LinearMap.id := by
    ext y
    rw [LinearMap.comp_apply, LinearMap.id_apply,
      Work.Thom.CohMap_comp_apply (e : C(X, Y)) (e.symm : C(Y, X)) ℤ n y, hcomp₁, CohMap_id]
    simp only [ModuleCat.hom_id, LinearMap.id_apply]
  constructor
  · intro x y hxy
    have hx := LinearMap.congr_fun h1 x
    have hy := LinearMap.congr_fun h1 y
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at hx hy
    rw [← hx, hxy, hy]
  · intro y
    refine ⟨(CohMap (e.symm : C(Y, X)) ℤ n).hom y, ?_⟩
    have hy := LinearMap.congr_fun h2 y
    simpa only [LinearMap.comp_apply, LinearMap.id_apply] using hy

/-- **The hyperplane class of `ℂP^{m-1}` is the pullback of the hyperplane class of `P(ε^m)`** along
the canonical identification `projUniv m`. -/
theorem zeta_trivCore_comap_projUniv (m : ℕ) :
    (CohMap (projUniv m) ℤ 2).hom (zeta (trivCore m)) = zetaP m := by
  rw [zeta_comap (trivCore m) (projUniv m), zetaP]
  simp only [tautLineP]

/-- **The `i = 1` case of the restriction of the powers of `ζ`**, in the composite form
`projUniv ∘ projClassFibre`. -/
theorem CohMap_comp_fibreIncl_zeta (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    [Fintype ι] (b : B) :
    (CohMap ((projUniv m).comp (projClassFibre Z b)) ℤ 2).hom (zeta (trivCore m))
      = (CohMap (fibreIncl Z b) ℤ 2).hom (zeta Z) := by
  have h : (CohMap ((projUniv m).comp (projClassFibre Z b)) ℤ 2).hom (zeta (trivCore m))
      = (CohMap (projClassFibre Z b) ℤ 2).hom
          ((CohMap (projUniv m) ℤ 2).hom (zeta (trivCore m))) :=
    (Work.Thom.CohMap_comp_apply (projClassFibre Z b) (projUniv m) ℤ 2 (zeta (trivCore m))).symm
  rw [h, zeta_trivCore_comap_projUniv, ← CohMap_fibreIncl_zeta Z b]

/-- **The restriction of the powers of `ζ` to a fibre**: for every `i`, the pullback of `ζ^i` along
the inclusion of a fibre is the pullback of `ζ(ℂP^{m-1})^i` along the identification
`projUniv ∘ projClassFibre` of the fibre with `P(ε^m)`. -/
theorem CohMap_fibreIncl_zetaPow (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    [Fintype ι] (b : B) (i : ℕ) :
    (CohMap (fibreIncl Z b) ℤ (2 * i)).hom (zetaPow Z i)
      = (CohMap ((projUniv m).comp (projClassFibre Z b)) ℤ (2 * i)).hom
          (zetaPow (trivCore m) i) := by
  induction i with
  | zero =>
    rw [zetaPow_zero, zetaPow_zero, Work.Whitney.cohTransport_CohMap, Work.Whitney.cohTransport_CohMap,
      CohMap_oneH, CohMap_oneH]
  | succ i ih =>
    rw [zetaPow_succ, zetaPow_succ, Work.Whitney.cupChern_CohMap, Work.Whitney.cupChern_CohMap, ih,
      CohMap_comp_fibreIncl_zeta Z b]

end

end Work.LerayHirsch
