import Mathlib
import Submission.Work.ShafarevichKoch.RelationBound
import Submission.Work.ShafarevichKoch.Kc
import Submission.Work.ShafarevichKoch.exists_quotient_of_finite_unramified
import Submission.Work.ShafarevichKoch.residuallyFiniteTwoGroup_presented
import Submission.Work.ShafarevichKoch.infiniteProTwoExtension_of_hasProTwoPresentation
import Submission.Work.ClassFieldTower.ProTwoGenus
import Submission.Work.ClassFieldTower.hasGenusLevel_witness

/-!
# `Work.ShafarevichKoch.proTwoShafarevichKochInput_Kc_of_presentation_and_quotients`

This file closes the gap between the *presentation form* of the Shafarevich--Koch crux for
`Kc = ℚ(√-30030)` (`Work.ShafarevichKoch.HasProTwoPresentation Kc 5 r`, plus the realization of
the finite `2`-quotients of the presented abstract group `G = presentedGroup 5 6 w`) and the
*sound interface* `Work.ClassFieldTower.ProTwoShafarevichKochInput Kc` of
`Work/ClassFieldTower/ProTwoGenus.lean`.

## What is proved

The general form `proTwoShafarevichKochInput_of_genusLevel_presentation_quotients` takes an
arbitrary number field `F` with a genus level (`HasGenusLevel F`), a maximal unramified pro-`2`
extension `M` of `F`, a topological generating set `g : Fin 5 → G_∅` with `w : Fin 6 → FreeGroup
(Fin 5)` whose normal closure is `ker (FreeGroup.lift g)` (`(P1)`), the density of the `g_i` in
`G_∅` (`(P2)`) and the realization of the finite `2`-quotients of the presented group `G` by
finite unramified extensions of `F` (which is the only arithmetic content beyond the presentation
data), and produces `ProTwoShafarevichKochInput F`.  The instance for `F = Kc` is the target
`proTwoShafarevichKochInput_Kc_of_presentation_and_quotients`, using the genus level
`Work.ClassFieldTower.hasGenusLevel_witness` of `Kc`.

## Where each clause comes from

Writing `rel := Finset.univ.image w` (so that `G = FreeGroup (Fin 5) ⧸ normalClosure rel` and
`G ≃* presentedGroup 5 6 w` by `QuotientGroup.quotientMulEquivOfEq`, the two normal closures
coinciding because `Set.range w = ↑rel`), the four clauses of `ProTwoShafarevichKochInput` are:

* the deficiency bound `rel.card ≤ 5 + 1 = 6`: `rel` is the image of the six-element `Fin 6`;
* minimality of the generating set: the genus level of `F` gives, through
  `Work.ShafarevichKoch.exists_quotient_of_finite_unramified`, a **surjection** `G ↠ (𝔽₂)^5`
  (the genus level is an unramified exponent-`2` extension of degree `2^5`); the image of a
  generating finset of `G` generates `(𝔽₂)^5`, which needs `5` elements
  (`Work.ProPDeficiency.dGens_le_card`, `Work.ProPDeficiency.dGens_zmod_two_pow`);
* residual `2`-finiteness: `Work.ShafarevichKoch.residuallyFiniteTwoGroup_presented` and
  invariance under isomorphism (`Work.ClassFieldTower.residuallyFiniteTwoGroup_of_mulEquiv`);
* the description of `G_∅`:
  - *every finite `2`-quotient of `G` is realized by an unramified extension* is the hypothesis
    `hreal`, transported along `G ≃* presentedGroup 5 6 w` by
    `Work.ClassFieldTower.realizedByUnramifiedExtensions_of_mulEquiv`;
  - *every finite unramified `2`-extension of `F` is a quotient of `G`* is
    `Work.ShafarevichKoch.exists_quotient_of_finite_unramified` (which uses the density `(P2)`),
    transported back along the same isomorphism (via `QuotientGroup.congr`).
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

open scoped Classical
open scoped NumberField
open Work.ClassFieldTower

noncomputable section

namespace Work.ShafarevichKoch

/-- **The presentation form of the crux, plus realization of finite `2`-quotients, gives the
sound Shafarevich--Koch interface, for any number field with a genus level.**

Let `F` be a number field with a genus level `HasGenusLevel F` (an unramified exponent-`2` Galois
extension of degree `2 ^ 5`), `M` a maximal unramified pro-`2` extension of `F`,
`g : Fin 5 → Gal(M/F)` a topological generating set, and `w : Fin 6 → FreeGroup (Fin 5)` words
whose normal closure is the kernel of `FreeGroup.lift g` (so that the presented abstract group
`G = presentedGroup 5 6 w` embeds in `Gal(M/F)` with dense image).  Assume that every finite
`2`-quotient of `G` is the Galois group of a finite extension of `F` with trivial relative
different.  Then `ProTwoShafarevichKochInput F` holds, with the presentation `5` generators,
`rel := Finset.univ.image w` relators.

This is the general form of `proTwoShafarevichKochInput_Kc_of_presentation_and_quotients`; the
genus level is used exactly once, to produce a surjection `G ↠ (𝔽₂)^5` and hence the minimality
of the generating set. -/
theorem proTwoShafarevichKochInput_of_genusLevel_presentation_quotients
    (F : Type) [Field F] [NumberField F] (hgenus : HasGenusLevel F)
    (M : MaximalUnramifiedProP.{0} F 2) (g : Fin 5 → galoisGroup M)
    (w : Fin 6 → FreeGroup (Fin 5))
    (hker : MonoidHom.ker (FreeGroup.lift g) = Subgroup.normalClosure (Set.range w))
    (hdense : (Subgroup.closure (Set.range g)).topologicalClosure = ⊤)
    (hreal : ∀ (N : Subgroup (presentedGroup 5 6 w)) [N.Normal],
      Finite (presentedGroup 5 6 w ⧸ N) →
      IsPGroup 2 (presentedGroup 5 6 w ⧸ N) →
      ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra F L)
        (_ : FiniteDimensional F L) (_ : IsGalois F L),
        differentIdeal (𝓞 F) (𝓞 L) = ⊤ ∧
        Nonempty ((L ≃ₐ[F] L) ≃* (presentedGroup 5 6 w ⧸ N))) :
    ProTwoShafarevichKochInput F := by
  classical
  -- the relator finset and the abstract group it presents
  let rel : Finset (FreeGroup (Fin 5)) := Finset.univ.image w
  let G := FreeGroup (Fin 5) ⧸ Subgroup.normalClosure (rel : Set (FreeGroup (Fin 5)))
  have hrelcoe : (rel : Set (FreeGroup (Fin 5))) = Set.range w := by
    ext y; simp [rel, Set.mem_range]
  have hnc : Subgroup.normalClosure (rel : Set (FreeGroup (Fin 5)))
      = Subgroup.normalClosure (Set.range w) := congrArg _ hrelcoe
  -- `G` is `presentedGroup 5 6 w`
  let ePG : G ≃* presentedGroup 5 6 w := QuotientGroup.quotientMulEquivOfEq hnc
  -- clause 3: residual `2`-finiteness
  have hres : ResiduallyFiniteTwoGroup G :=
    residuallyFiniteTwoGroup_of_mulEquiv ePG
      (residuallyFiniteTwoGroup_presented F 5 6 M g w hker hdense)
  -- the genus level of `F`: an unramified exponent-`2` extension of degree `2 ^ 5`
  obtain ⟨L₀, iL, iNL, iAL, hfdL, hgalL, hdiffL, hexpL, hcardL⟩ := hgenus
  letI : Field L₀ := iL
  letI : NumberField L₀ := iNL
  letI : Algebra F L₀ := iAL
  letI : FiniteDimensional F L₀ := hfdL
  letI : IsGalois F L₀ := hgalL
  have hpgL : IsPGroup 2 (L₀ ≃ₐ[F] L₀) := by
    rw [isPGroup_iff_pow_pow_eq_one]
    intro σ
    exact ⟨1, by rw [pow_one]; exact hexpL σ⟩
  -- it is a quotient of `G`
  obtain ⟨N₀, hN₀, ⟨eN₀⟩⟩ :=
    exists_quotient_of_finite_unramified F 5 6 M g w hker hdense L₀ hdiffL hpgL
  haveI : N₀.Normal := hN₀
  haveI : IsMulCommutative (L₀ ≃ₐ[F] L₀) :=
    IsMulCommutative.of_comm (commute_of_sq_eq_one hexpL)
  obtain ⟨e5⟩ :=
    Commons.GroupTheory.SpecificGroups.ZModProd.exists_mulEquiv_multiplicative_fin_zmod_two_of_fintype_commutative_pow_two_eq_one_card
      (G := L₀ ≃ₐ[F] L₀) hexpL hcardL
  -- the surjection `G ↠ (𝔽₂)^5`
  let ψ : G →* (Fin 5 → Multiplicative (ZMod 2)) :=
    (e5.toMonoidHom.comp (eN₀.toMonoidHom.comp (QuotientGroup.mk' N₀))).comp ePG.toMonoidHom
  have hψ : Function.Surjective ψ :=
    (e5.surjective.comp (eN₀.surjective.comp (QuotientGroup.mk'_surjective N₀))).comp
      ePG.surjective
  -- clause 2: minimality of the generating set
  have hmin : ∀ S : Finset G, Subgroup.closure (S : Set G) = ⊤ → 5 ≤ S.card := by
    intro S hS
    have hgen : Work.ProPDeficiency.IsGeneratingSet (S.image ψ) := by
      rw [Work.ProPDeficiency.isGeneratingSet_iff, Finset.coe_image,
        ← MonoidHom.map_closure ψ (S : Set G), hS, Subgroup.map_top_of_surjective ψ hψ]
    calc 5 = Work.ProPDeficiency.dGens (Fin 5 → Multiplicative (ZMod 2)) :=
          (Work.ProPDeficiency.dGens_zmod_two_pow 5).symm
      _ ≤ (S.image ψ).card := Work.ProPDeficiency.dGens_le_card hgen
      _ ≤ S.card := Finset.card_image_le
  -- clause 4a: realization of the finite `2`-quotients of `G`, transported along `G ≃* G`
  have hdesc1 : RealizedByUnramifiedExtensions F G :=
    realizedByUnramifiedExtensions_of_mulEquiv ePG hreal
  -- clause 4b: every finite unramified `2`-extension is a quotient of `G`
  have hdesc2 : ∀ (L : Type) [Field L] [NumberField L] [Algebra F L] [FiniteDimensional F L]
      [IsGalois F L], differentIdeal (𝓞 F) (𝓞 L) = ⊤ → IsPGroup 2 (L ≃ₐ[F] L) →
      ∃ (N : Subgroup G) (_ : N.Normal), Finite (G ⧸ N) ∧ IsPGroup 2 (G ⧸ N) ∧
        Nonempty ((G ⧸ N) ≃* (L ≃ₐ[F] L)) := by
    intro L hFi hNu hAl hFd hGa hunr hpg
    obtain ⟨N, hN, ⟨eN⟩⟩ :=
      exists_quotient_of_finite_unramified F 5 6 M g w hker hdense L hunr hpg
    haveI : N.Normal := hN
    -- transport the normal subgroup `N ≤ presentedGroup 5 6 w` back to `G`
    let eH : G →* presentedGroup 5 6 w := ePG.toMonoidHom
    let N' : Subgroup G := N.comap eH
    have hN' : N'.Normal := hN.comap eH
    haveI : N'.Normal := hN'
    have hmap : Subgroup.map eH N' = N :=
      Subgroup.map_comap_eq_self_of_surjective (f := eH) ePG.surjective N
    let φ : G ⧸ N' ≃* presentedGroup 5 6 w ⧸ N := QuotientGroup.congr N' N ePG hmap
    haveI : Fintype (L ≃ₐ[F] L) := AlgEquiv.fintype F L
    exact ⟨N', hN', Finite.of_equiv (L ≃ₐ[F] L) (φ.trans eN).symm.toEquiv,
      hpg.of_equiv (φ.trans eN).symm, ⟨φ.trans eN⟩⟩
  -- assembly
  refine ⟨Fin 5, inferInstance, inferInstance, rel, ?_⟩
  refine ⟨?_, hmin, hres, hdesc1, hdesc2⟩
  -- clause 1: the deficiency bound
  have hrelcard : rel.card ≤ 6 := by
    have h : (Finset.univ.image w).card ≤ 6 := by
      calc (Finset.univ.image w).card ≤ (Finset.univ : Finset (Fin 6)).card :=
            Finset.card_image_le
        _ = 6 := by simp
    exact h
  rw [Fintype.card_fin]
  omega

/-- **The presentation form of the crux, plus realization of finite `2`-quotients, gives the sound
Shafarevich--Koch interface for `Kc`.**  Let `M` be a maximal unramified pro-`2` extension of
`Kc = ℚ(√-30030)`, let `g : Fin 5 → Gal(M/Kc)` be a topological generating set, and let
`w : Fin 6 → FreeGroup (Fin 5)` be words whose normal closure is the kernel of the corresponding
map `FreeGroup (Fin 5) → Gal(M/Kc)`, so that the abstract group `G = presentedGroup 5 6 w` embeds
in `Gal(M/Kc)` with dense image (`HasProTwoPresentation Kc 5 6`).  Assume moreover that every
finite `2`-quotient of `G` is the Galois group of a finite extension of `Kc` with trivial relative
different (the "realization of finite `2`-quotients" clause).  Then the sound interface
`Work.ClassFieldTower.ProTwoShafarevichKochInput Kc` holds: `G` arises from five generators and at
most six relators, its generating sets are minimal (five elements, by the genus level of `Kc`),
it is residually a finite `2`-group, and its finite `2`-quotients are exactly the Galois groups of
the finite unramified `2`-extensions of `Kc`.

Both directions of the "finite `2`-quotients" description are needed here and are available: the
realization of quotients of `G` is the hypothesis, and the converse (every finite unramified
`2`-extension of `Kc` is a quotient of `G`) is proved by density from
`Work.ShafarevichKoch.exists_quotient_of_finite_unramified`.  Minimality comes from the genus level
`Work.ClassFieldTower.hasGenusLevel_witness` together with the elementary fact that a generating
finset of `(𝔽₂)^5` has at least five elements, and residual `2`-finiteness from
`Work.ShafarevichKoch.residuallyFiniteTwoGroup_presented`.

Suggested route.  Unpack `ProTwoShafarevichKochInput Kc` (`Submission/Work/ClassFieldTower/ProTwoGenus.lean`)
with `α := Fin 5` and `rel := Finset.univ.image w`, and use `Work.ClassFieldTower.ProTwoGenus`'s
`DescribesMaximalProTwo`, `ResiduallyFiniteTwoGroup`; the quotient `FreeGroup (Fin 5) ⧸
Subgroup.normalClosure ((Finset.univ.image w : Finset (FreeGroup (Fin 5))) : Set _)` is
`Work.ShafarevichKoch.presentedGroup 5 6 w` (`normalClosure` of `Set.range w` equals that of the
finset image), so transporting `hreal` and the clause-2 output of
`exists_quotient_of_finite_unramified` along that isomorphism gives both conjuncts of
`DescribesMaximalProTwo`.  The minimality argument is the one already carried out inside
`Work.ShafarevichKoch.infiniteProTwoExtension_of_hasProTwoPresentation` (a generating finset of `G`
maps onto a generating finset of `(𝔽₂)^5` via a surjection `G ↠ (𝔽₂)^5` obtained from the genus
level and `exists_quotient_of_finite_unramified`); note the auxiliary
`card_le_of_closure_eq_top_multiplicative` there is `private`, so it has to be redone (or the
argument re-run) in the new file. -/
theorem proTwoShafarevichKochInput_Kc_of_presentation_and_quotients
    (M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Work.ClassFieldTower.Kc 2)
    (g : Fin 5 → Work.ClassFieldTower.galoisGroup M) (w : Fin 6 → FreeGroup (Fin 5))
    (hker : MonoidHom.ker (FreeGroup.lift g) = Subgroup.normalClosure (Set.range w))
    (hdense : (Subgroup.closure (Set.range g)).topologicalClosure = ⊤)
    (hreal : ∀ (N : Subgroup (Work.ShafarevichKoch.presentedGroup 5 6 w)) [N.Normal],
      Finite (Work.ShafarevichKoch.presentedGroup 5 6 w ⧸ N) →
      IsPGroup 2 (Work.ShafarevichKoch.presentedGroup 5 6 w ⧸ N) →
      ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra Work.ClassFieldTower.Kc L)
        (_ : FiniteDimensional Work.ClassFieldTower.Kc L) (_ : IsGalois Work.ClassFieldTower.Kc L),
        differentIdeal (NumberField.RingOfIntegers Work.ClassFieldTower.Kc)
          (NumberField.RingOfIntegers L) = ⊤ ∧
        Nonempty ((L ≃ₐ[Work.ClassFieldTower.Kc] L) ≃* (Work.ShafarevichKoch.presentedGroup 5 6 w ⧸ N))) :
    Work.ClassFieldTower.ProTwoShafarevichKochInput Work.ClassFieldTower.Kc :=
  proTwoShafarevichKochInput_of_genusLevel_presentation_quotients
    Work.ClassFieldTower.Kc Work.ClassFieldTower.hasGenusLevel_witness M g w hker hdense hreal

end Work.ShafarevichKoch
