import Mathlib
import Submission.Work.Cohomology.HomologyPairSequence
import Submission.Work.Cohomology.homologyContractible
import Submission.Work.RatHurewicz.torsion_of_subsingleton_ratHomology

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The relative integral homology of a point is a torsion group

This file proves `Work.RatHurewicz.nat_smul_eq_zero_relChains_rangeModel`: for a topological space
`Z`, a point `z₀ ∈ Z` and a degree `j ≥ 2`, if the *rational* singular homology `H_j(Z;ℚ)` vanishes
then every element of the *integral* relative homology `H_j(Z, {z₀};ℤ)` has finite order.

## The mathematics

The long exact sequence of the pair `(Z, {z₀})` with `ℤ` coefficients reads

`H_j({z₀}) → H_j(Z) → H_j(Z,{z₀}) → H_{j-1}({z₀}) → H_{j-1}(Z)`.

For `j ≥ 2` the two outer groups involving the point vanish (`j ≥ 1` and `j - 1 ≥ 1` are positive
degrees, and a point is contractible, `Work.Cohomology.homologyContractible`).  Hence exactness at
`H_j(Z,{z₀})` says that the map `H_j(Z) ⟶ H_j(Z,{z₀})` is surjective.  Since `H_j(Z;ℚ) = 0` implies
that `H_j(Z;ℤ)` is a torsion group (`Work.RatHurewicz.torsion_of_subsingleton_ratHomology`, the
change-of-coefficients step `H_*(Z;ℚ) ≅ H_*(Z;ℤ) ⊗ ℚ` together with flatness of `ℚ` over `ℤ`), every
relative class is the image of a torsion class, so it is a torsion class itself.

No relative change-of-coefficients statement is needed: the *integral* LES of the pair together with
the absolute torsion statement suffices, which is why this route is short.

## Formalisation notes

* The long exact sequence of the pair is `Work.Cohomology.hPair_exact₃`, exactness at `H_{n+1}(X,A)`
  of the complex `H_{n+1}(X) → H_{n+1}(X,A) → H_n(A)`; with `n = k` and `j = k + 1` the indices line
  up syntactically, which is why the proof first replaces `j` by `k + 1` (`obtain ⟨k, rfl⟩`).
* `set_option backward.isDefEq.respectTransparency false` is needed because the same module can be
  reached through the abbreviation `Work.Cohomology.relChains X A` and through
  `cokernel (Work.Cohomology.inclChains X A)`, and the resulting `ModuleCat ℤ` instances only agree
  up to a (defeq) instance of `Ring ℤ`.
* The final transfer of torsion is done for a bare `AddMonoidHom` (no module structure, hence no
  ring instances), which keeps it free of the instance mismatch above.
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open CategoryTheory Limits

namespace Work.RatHurewicz

noncomputable section

/-- The first arrow of a short exact sequence of `ℤ`-modules with vanishing target is an
epimorphism: the image of `f` is the kernel of the zero map. -/
private lemma epi_of_exact_of_isZero_tgt {S : ShortComplex (ModuleCat ℤ)} (h : S.Exact)
    (h3 : IsZero S.X₃) : Epi S.f :=
  (ShortComplex.exact_iff_epi S (h3.eq_of_tgt S.g 0)).mp h

/-- A surjective additive homomorphism whose source is a torsion group has torsion target. -/
private lemma exists_nat_smul_eq_zero_of_surjective_addHom
    {A B : Type*} [AddCommMonoid A] [AddCommMonoid B]
    (f : A →+ B) (hf : Function.Surjective f)
    (htor : ∀ a : A, ∃ N : ℕ, 0 < N ∧ N • a = 0) :
    ∀ b : B, ∃ N : ℕ, 0 < N ∧ N • b = 0 := by
  intro b
  obtain ⟨a, rfl⟩ := hf b
  obtain ⟨n, hn, ha⟩ := htor a
  exact ⟨n, hn, by rw [← map_nsmul, ha, map_zero]⟩

theorem nat_smul_eq_zero_relChains_rangeModel {Z : Type} [TopologicalSpace Z] (z₀ : Z) (j : ℕ)
    (hj : 2 ≤ j)
    (hQ : Subsingleton ↥((Work.Cohomology.singularChains ℚ (TopCat.of Z)).homology j)) :
    ∀ b : ↥((Work.Cohomology.relChains (TopCat.of Z) ({z₀} : Set Z)).homology j),
      ∃ N : ℕ, 0 < N ∧ N • b = 0 := by
  -- write `j = k + 1` so that the degree of `hPair_exact₃` matches the goal syntactically
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 :=
    ⟨j - 1, (Nat.sub_add_cancel (by omega : 1 ≤ j)).symm⟩
  -- the absolute integral homology is a torsion group
  have htor := Work.RatHurewicz.torsion_of_subsingleton_ratHomology (X := Z) (k + 1) hQ
  -- the homology of the point (a contractible space) vanishes in the positive degree `k ≥ 1`
  have hA : IsZero ((Work.Cohomology.singularChains ℤ
      (TopCat.of ↥({z₀} : Set Z))).homology k) :=
    Work.Cohomology.homologyContractible (X := TopCat.of ↥({z₀} : Set Z)) k (by omega)
  -- so the map `H_{k+1}(Z) ⟶ H_{k+1}(Z,{z₀})` of the long exact sequence of the pair is onto
  haveI hepi : Epi (HomologicalComplex.homologyMap
      (cokernel.π (Work.Cohomology.inclChains (TopCat.of Z) ({z₀} : Set Z))) (k + 1)) :=
    epi_of_exact_of_isZero_tgt
      (Work.Cohomology.hPair_exact₃ (TopCat.of Z) ({z₀} : Set Z) k) hA
  have hsurj : Function.Surjective ⇑(ModuleCat.Hom.hom
      (HomologicalComplex.homologyMap
        (cokernel.π (Work.Cohomology.inclChains (TopCat.of Z) ({z₀} : Set Z))) (k + 1))) :=
    fun y => (ModuleCat.epi_iff_surjective _).mp hepi y
  exact exists_nat_smul_eq_zero_of_surjective_addHom
    (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (cokernel.π (Work.Cohomology.inclChains (TopCat.of Z) ({z₀} : Set Z))) (k + 1))).toAddMonoidHom
    hsurj htor

end

end Work.RatHurewicz
