import Mathlib
import Submission.Work.ClassFieldTower.ProTwoGeneratorRank
import Submission.Work.ClassFieldTower.ProTwoGenus
import Submission.Work.ProPDeficiency.Basic
import Submission.Work.ProPDeficiency.Specialisations

namespace Work.ClassFieldTower

set_option linter.style.haveILetI false

/-- **Any generating set of `G_∅ = Gal(Kc_∅/Kc)` modulo all finite `2`-quotients has at least
five elements.**

`M` is a maximal unramified pro-`2` extension of `Kc = ℚ(√-30030)` and `S` is a finite subset of
`G_∅ = galoisGroup M` whose image generates `G_∅ ⧸ N` for every normal `N` with `G_∅ ⧸ N` a
finite `2`-group.

The genus-theoretic input `exists_surjective_galoisGroup_zmodTwo_five_witness` provides, for this
`M`, a surjection `φ : G_∅ ↠ (𝔽₂)^5`.  Applying the hypothesis to the kernel `N = ker φ` shows
that the image of `S` in `G_∅ ⧸ ker φ ≅ (𝔽₂)^5` generates: pushing the generating set forward
along `φ` we get a generating finset of the elementary abelian `2`-group `(𝔽₂)^5` of cardinality
at most `#S`.  Since `dGens (𝔽₂)^5 = 5` and `dGens ≤` the cardinality of any generating finset,
`5 ≤ #S`. -/
theorem five_le_card_of_generates_in_finite_quotients
    (M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Work.ClassFieldTower.Kc 2)
    (S : Finset (Work.ClassFieldTower.galoisGroup M))
    (hS : ∀ (N : Subgroup (Work.ClassFieldTower.galoisGroup M)) [N.Normal],
        Finite (Work.ClassFieldTower.galoisGroup M ⧸ N) →
        IsPGroup 2 (Work.ClassFieldTower.galoisGroup M ⧸ N) →
        Subgroup.closure (Set.image (QuotientGroup.mk' N) (S : Set (Work.ClassFieldTower.galoisGroup M))) = ⊤) :
    5 ≤ S.card := by
  classical
  -- five independent unramified quadratic extensions of `Kc`: `G_∅ ↠ (𝔽₂)^5`
  obtain ⟨φ, hφ⟩ := exists_surjective_galoisGroup_zmodTwo_five_witness M
  haveI : φ.ker.Normal := MonoidHom.normal_ker φ
  -- the quotient `G_∅ ⧸ ker φ` is the finite `2`-group `(𝔽₂)^5`
  have hfin : Finite (Work.ClassFieldTower.galoisGroup M ⧸ φ.ker) :=
    Finite.of_equiv (Fin 5 → Multiplicative (ZMod 2))
      (QuotientGroup.quotientKerEquivOfSurjective φ hφ).symm.toEquiv
  have hA : IsPGroup 2 (Fin 5 → Multiplicative (ZMod 2)) := by
    rw [IsPGroup.iff_card]
    exact ⟨5, by simp⟩
  have hpg : IsPGroup 2 (Work.ClassFieldTower.galoisGroup M ⧸ φ.ker) :=
    IsPGroup.of_injective hA
      (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toMonoidHom
      (QuotientGroup.quotientKerEquivOfSurjective φ hφ).injective
  -- the hypothesis: the image of `S` generates the quotient `(𝔽₂)^5`
  have h := hS φ.ker hfin hpg
  have h1 := Work.ProPDeficiency.closure_image_eq_top_of_surjective
      (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toMonoidHom
      (QuotientGroup.quotientKerEquivOfSurjective φ hφ).surjective h
  -- push the generating set forward along `φ`
  set f : Work.ClassFieldTower.galoisGroup M →* (Fin 5 → Multiplicative (ZMod 2)) :=
    (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toMonoidHom.comp (QuotientGroup.mk' φ.ker)
    with hf
  have hgen : Work.ProPDeficiency.IsGeneratingSet (S.image f) := by
    rw [Work.ProPDeficiency.isGeneratingSet_iff, Finset.coe_image]
    rw [show (f '' (S : Set (Work.ClassFieldTower.galoisGroup M)))
      = (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toMonoidHom ''
        ((⇑(QuotientGroup.mk' φ.ker)) '' (S : Set (Work.ClassFieldTower.galoisGroup M))) from by
      rw [hf, MonoidHom.coe_comp, Set.image_comp]]
    exact h1
  -- `dGens (𝔽₂)^5 = 5` and a generating finset has at least `dGens` elements
  calc 5 = Work.ProPDeficiency.dGens (Fin 5 → Multiplicative (ZMod 2)) :=
        (Work.ProPDeficiency.dGens_zmod_two_pow 5).symm
    _ ≤ (S.image f).card := Work.ProPDeficiency.dGens_le_card hgen
    _ ≤ S.card := Finset.card_image_le

end Work.ClassFieldTower
