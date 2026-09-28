import Mathlib
import Submission.Work.Kunneth.kunneth_cohomology_cpn
import Submission.Work.Kunneth.kunneth_h4_cp2cp2
import Submission.Work.Projective.cpn_cohomology

/-!
# `H^n(X × ℂP^m)` is free over `H^*(X)` on `1, ζ, …, ζ^m`

`Work.Kunneth.kunneth_cohomology_cpn` computes `H^n(X × ℂP^m; ℤ)` as
`⨁_{p+q=n} H^p(X;ℤ) ⊗ H^q(ℂP^m;ℤ)` with no hypotheses on `X`.  Since the cohomology of `ℂP^m` is
`ℤ` in the even degrees `≤ 2m` and `0` in the others (`Work.Projective.cpn_cohomology`), the
tensor factors collapse and `H^n(X × ℂP^m;ℤ)` becomes the product of the `H^p(X;ℤ)` over the
bidegrees `(p,q)` with `p+q = n` and `q` even, `q ≤ 2m`:

`H^n(X × ℂP^m;ℤ) ≅ ∏_{j=0}^{⌊n/2⌋} H^{n-2j}(X;ℤ)`  (with `2j ≤ 2m`).

This is the **Leray–Hirsch base case** requested by the WHITNEY subproject: `H^*(B × ℂP^{m-1})` is
free over `H^*(B)` on `1, ζ, …, ζ^{m-1}`.

## Main results

* `Work.Kunneth.cohomSummand_cpn_model` — the `(p,q)` Künneth summand is `H^p(X)` for `q` even
  `≤ 2m` and `0` otherwise;
* `Work.Kunneth.kunneth_cohomology_cpn_free` — the resulting product decomposition of
  `H^n(X × ℂP^m;ℤ)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct

namespace Work.Kunneth

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

/-- `ℂP^m` as a simplicial set. -/
abbrev cpnSSet (m : ℕ) : SSet := TopCat.toSSet.obj (Work.Projective.CPSpace m)

/-- The `(p,q)`-summand of the Künneth decomposition of `H^n(X × ℂP^m)`: it is `H^p(X)` when `q`
is even and `≤ 2m` (where `H^q(ℂP^m) = ℤ`) and `0` otherwise. -/
abbrev cpnSummand (X : SSet) (m : ℕ) (pq : ℕ × ℕ) : ModuleCat ℤ :=
  if Even pq.2 ∧ pq.2 ≤ 2 * m then (Work.Cohomology.cochainC ℤ X).homology pq.1
    else ModuleCat.of ℤ (Fin 0 → ℤ)

/-- **The `(p,q)` Künneth summand with a projective space**: `H^p(X) ⊗ H^q(ℂP^m)` is `H^p(X)` if
`q` is even and `≤ 2m`, and `0` otherwise. -/
theorem cohomSummand_cpn_model (X : SSet) (m : ℕ) (pq : ℕ × ℕ) :
    Nonempty (Work.Kunneth.cohomSummand X (cpnSSet m) pq.1 pq.2 ≃ₗ[ℤ] ↥(cpnSummand X m pq)) := by
  by_cases h : Even pq.2 ∧ pq.2 ≤ 2 * m
  · -- `H^q(ℂP^m) = ℤ`, so the summand is `H^p(X) ⊗ ℤ ≅ H^p(X)`
    obtain ⟨e⟩ := (Work.Projective.cpn_cohomology m pq.2 :
      Nonempty ((Work.Cohomology.cochainC ℤ (cpnSSet m)).homology pq.2 ≅
        Work.Projective.cpnModel m pq.2))
    obtain ⟨ei⟩ := Work.Projective.cpnModel_iso_int h
    have hiso : ((Work.Cohomology.cochainC ℤ X).homology pq.1
          ⊗ (Work.Cohomology.cochainC ℤ (cpnSSet m)).homology pq.2)
        ≅ ((Work.Cohomology.cochainC ℤ X).homology pq.1) :=
      (TensorProduct.congr
        (LinearEquiv.refl ℤ ↥((Work.Cohomology.cochainC ℤ X).homology pq.1))
        (e ≪≫ ei).toLinearEquiv).toModuleIso
      ≪≫ (TensorProduct.rid ℤ ↥((Work.Cohomology.cochainC ℤ X).homology pq.1)).toModuleIso
    rw [cpnSummand, if_pos h]
    exact ⟨hiso.toLinearEquiv⟩
  · -- `H^q(ℂP^m) = 0`, so the summand is `H^p(X) ⊗ 0 = 0`
    obtain ⟨e⟩ := (Work.Projective.cpn_cohomology m pq.2 :
      Nonempty ((Work.Cohomology.cochainC ℤ (cpnSSet m)).homology pq.2 ≅
        Work.Projective.cpnModel m pq.2))
    have hz : IsZero ((Work.Cohomology.cochainC ℤ (cpnSSet m)).homology pq.2) :=
      isZero_of_iso (Work.Projective.isZero_cpnModel h) e.symm
    have hz2 : IsZero (((Work.Cohomology.cochainC ℤ X).homology pq.1
        ⊗ (Work.Cohomology.cochainC ℤ (cpnSSet m)).homology pq.2)) :=
      isZero_tensor_of_isZero_right hz
    have hz3 : IsZero (ModuleCat.of ℤ (Fin 0 → ℤ)) := ModuleCat.isZero_of_subsingleton _
    rw [cpnSummand, if_neg h]
    obtain ⟨hIso⟩ := nonempty_iso_of_isZero hz2 hz3
    exact ⟨hIso.toLinearEquiv⟩

/-- **Leray–Hirsch base case.**  `H^n(X × ℂP^m; ℤ)` is the product of the `H^p(X; ℤ)` over the
bidegrees `(p,q)` with `p + q = n`, `q` even and `q ≤ 2m` — i.e. `H^*(X × ℂP^m)` is free over
`H^*(X)` on the classes `1, ζ, …, ζ^m`. -/
theorem kunneth_cohomology_cpn_free (X : SSet) (m n : ℕ) :
    Nonempty (CategoryTheory.Iso
      ((Work.Cohomology.cochainC ℤ (sProd X (cpnSSet m))).homology n)
      (ModuleCat.of ℤ (∀ pq : tpIdx n, ↥(cpnSummand X m pq.1)))) := by
  obtain ⟨e⟩ := kunneth_cohomology_cpn X m n
  exact ⟨e ≪≫ (LinearEquiv.piCongrRight (fun pq : tpIdx n =>
    Classical.choice (cohomSummand_cpn_model X m pq.1))).toModuleIso⟩

end

end Work.Kunneth
