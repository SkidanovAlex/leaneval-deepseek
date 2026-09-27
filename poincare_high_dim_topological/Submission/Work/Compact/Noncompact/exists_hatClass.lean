import Mathlib
import Submission.Work.Compact.Noncompact.Good
import Submission.Work.Compact.Noncompact.exists_sub_bdry_of_hatClass_eq_zero

/-!
# Every class in `H_{k+1}(X, X∖S)` is the class of a relative cycle on the nose

`Work.Compact.Noncompact.hatClass S k z hz` is the class in `H_{k+1}(X, X∖S) = H_{k+1}(RC X S)` of a
chain `z ∈ C_{k+1}(X)` whose boundary is supported in `S`.  This file proves the converse: the map

`z ↦ hatClass S k z` is surjective, i.e. every class in `H_{k+1}(RC X S)` is represented by an
*actual chain* of `X` (not merely by a chain of the quotient complex `C_*(X)/C_*(S)`).

The argument is elementary.  The projection `C_{k+1}(X) ⟶ (RC X S).X (k+1)` is surjective; a class
`u ∈ H_{k+1}(RC X S)` is the class of a cycle `y` of `RC X S`; lifting the chain underlying `y` to a
chain `z ∈ C_{k+1}(X)` and using the compatibility of `∂` with the projection shows that `∂z` is
killed by the projection, hence is supported in `S`; and the class of `z` is, by construction, the
class of `y`, i.e. `u`.
-/

namespace Work.Compact.Noncompact

set_option maxHeartbeats 800000

noncomputable section

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

variable {X : TopCat}

/-- **A chain is supported in `S` exactly when its image in `C_n(X)/C_n(S)` vanishes** (general
form, in arbitrary degree `n`, of `Work.Compact.Noncompact.hatQ_eq_zero_iff_mem_suppS`). -/
lemma f_π_eq_zero_iff_mem_suppS (S : Set X) (n : ℕ) (x : Ch X n) :
    x ∈ suppS X S n ↔ ((cokernel.π (Work.Cohomology.inclChains X S)).f n) x = 0 := by
  have hc := isColimitCoforkMapOfIsColimit'
    (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) n)
    (cokernel.condition (Work.Cohomology.inclChains X S))
    (cokernelIsCokernel (Work.Cohomology.inclChains X S))
  have hc' : (Work.Cohomology.inclChains X S).f n ≫
      (cokernel.π (Work.Cohomology.inclChains X S)).f n = 0 := by
    rw [← HomologicalComplex.comp_f, cokernel.condition, HomologicalComplex.zero_f]
  exact (cokernelπ_eq_zero_iff_range hc' hc x).symm

theorem exists_hatClass (X : TopCat) (S : Set X) (k : ℕ) (u : (RC X S).homology (k + 1)) :
    ∃ (z : Ch X (k + 1)) (hz : bdry X k z ∈ suppS X S k), hatClass S k z hz = u := by
  -- Lift `u` to a cycle of the relative complex.
  obtain ⟨y, hy⟩ : ∃ y : (RC X S).cycles (k + 1),
      ((RC X S).homologyπ (k + 1)).hom y = u := by
    have hsurj : Function.Surjective (ModuleCat.Hom.hom ((RC X S).homologyπ (k + 1))) :=
      (ModuleCat.epi_iff_surjective _).mp inferInstance
    obtain ⟨y, hy⟩ := hsurj u
    exact ⟨y, hy⟩
  -- Lift the chain underlying that cycle to a genuine chain of `X`.
  obtain ⟨z, hzπ⟩ : ∃ z : Ch X (k + 1),
      ((cokernel.π (Work.Cohomology.inclChains X S)).f (k + 1)) z
        = ((RC X S).iCycles (k + 1)).hom y := by
    have hsurj : Function.Surjective
        (ModuleCat.Hom.hom ((cokernel.π (Work.Cohomology.inclChains X S)).f (k + 1))) :=
      (ModuleCat.epi_iff_surjective _).mp inferInstance
    obtain ⟨z, hz⟩ := hsurj (((RC X S).iCycles (k + 1)).hom y)
    exact ⟨z, hz⟩
  -- Its boundary is supported in `S`.
  have hz : bdry X k z ∈ suppS X S k := by
    rw [f_π_eq_zero_iff_mem_suppS]
    have hcomm := HomologicalComplex.Hom.comm
      (cokernel.π (Work.Cohomology.inclChains X S)) (k + 1) k
    have hh := congrArg
      (fun (φ : Ch X (k + 1) ⟶ (RC X S).X k) => φ.hom z) hcomm
    rw [ModuleCat.comp_apply, ModuleCat.comp_apply] at hh
    rw [← hh, hzπ]
    have h2 := HomologicalComplex.iCycles_d (RC X S) (k + 1) k
    have h3 := congrArg
      (fun (φ : (RC X S).cycles (k + 1) ⟶ (RC X S).X k) => φ.hom y) h2
    rw [ModuleCat.comp_apply] at h3
    exact h3
  refine ⟨z, hz, ?_⟩
  -- The cycle attached to `z` is `y`, hence its class is `u`.
  have hA : ((RC X S).iCycles (k + 1)).hom ((hatCycHom S k z hz).hom 1) = hatQ S k z := by
    have h := iCycles_hatCycHom S k z hz
    have h2 := congrArg
      (fun (f : ModuleCat.of ℤ ℤ ⟶ (RC X S).X (k + 1)) => f.hom 1) h
    rw [ModuleCat.comp_apply] at h2
    rw [h2]
    exact ofHom_toSpanSingleton_one' (hatQ S k z)
  have hyc : (hatCycHom S k z hz).hom 1 = y := by
    have hinj : Function.Injective ((RC X S).iCycles (k + 1)).hom :=
      (ModuleCat.mono_iff_injective _).mp inferInstance
    exact hinj (hA.trans hzπ)
  show hatClass S k z hz = u
  rw [hatClass, hatClassHom, ModuleCat.comp_apply, hyc, hy]

end

end Work.Compact.Noncompact
