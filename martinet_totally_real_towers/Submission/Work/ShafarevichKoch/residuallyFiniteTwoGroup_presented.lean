import Mathlib
import Submission.Work.ShafarevichKoch.RelationBound

/-!
# `Work.ShafarevichKoch.residuallyFiniteTwoGroup_presented`

The abstract group `presentedGroup d r w = FreeGroup (Fin d) ⧸ ⟪w⟫` presented by a pro-`2`
presentation `(P1)` of the maximal unramified pro-`2` group `G_∅ = Gal(F_∅/F)` is again
*residually a finite `2`-group* (`Work.ClassFieldTower.ResiduallyFiniteTwoGroup`).

This is the "residual" half of the Shafarevich--Koch interface: the presentation map
`FreeGroup (Fin d) →* G_∅`, `x_i ↦ g_i` has kernel exactly the normal closure of the words `w_j`,
so it descends to an **injective** homomorphism `presentedGroup d r w →* G_∅`.  Since `G_∅` is
residually a finite `2`-group (`Work.ClassFieldTower.residuallyFiniteTwoGroup_galoisGroup`), and
that property passes to subgroups and to quotients by an equal normal subgroup, the presented
group inherits it.

Note that the density hypothesis `hdense` is *not* needed here: only injectivity of the lifted
map matters, and the lift is injective as soon as `(P1)` holds.  (Density is what makes the
presented group's finite `2`-quotients the *arithmetically realized* ones, cf.
`exists_quotient_of_finite_unramified`.)

## Main results

* `residuallyFiniteTwoGroup_of_injective` -- the property is inherited along injective
  homomorphisms (a subgroup of a residually finite `2`-group is residually a finite
  `2`-group);
* `residuallyFiniteTwoGroup_galoisGroup_univ` -- the universe-general form of
  `Work.ClassFieldTower.residuallyFiniteTwoGroup_galoisGroup` (that lemma is stated for
  `F : Type` only, while the statement proved here is universe-polymorphic);
* `residuallyFiniteTwoGroup_presented` -- the target.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open scoped Classical
open scoped NumberField

noncomputable section

namespace Work.ShafarevichKoch

open Work.ClassFieldTower

/-- **`ResiduallyFiniteTwoGroup` is inherited along injective homomorphisms.**

If `f : G →* H` is injective and `H` is residually a finite `2`-group, so is `G`: given
`g ≠ 1`, separate `f g` from `1` by a normal `N ◁ H` with `H ⧸ N` a finite `2`-group, and pull
`N` back along `f`.  The pullback `K := N.comap f` has `G ⧸ K` a subgroup of `H ⧸ N`
(via `(mk' N).comp f`, whose kernel is `N.comap f`), hence finite and a `2`-group, and it does
not contain `g`. -/
theorem residuallyFiniteTwoGroup_of_injective {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Injective f)
    (hH : ResiduallyFiniteTwoGroup H) : ResiduallyFiniteTwoGroup G := by
  intro g hg
  have hfg : f g ≠ 1 := fun h1 => hg (hf (by rw [h1, map_one]))
  obtain ⟨N, hN, hfin, hpg, hmk⟩ := hH (f g) hfg
  haveI : N.Normal := hN
  -- the pullback of the separating quotient along `f`
  let φ : G →* H ⧸ N := (QuotientGroup.mk' N).comp f
  have hkerφ : MonoidHom.ker φ = N.comap f := by
    ext x
    simp only [MonoidHom.mem_ker, φ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_comap]
  let K : Subgroup G := MonoidHom.ker φ
  have hK : K.Normal := MonoidHom.normal_ker φ
  haveI : K.Normal := hK
  have hfinrange : Finite ↥φ.range :=
    Finite.of_injective (Subgroup.subtype φ.range) Subtype.coe_injective
  refine ⟨K, hK, ?_, ?_, ?_⟩
  · -- `G ⧸ K ≃* φ.range` is a subgroup of the finite group `H ⧸ N`
    exact Finite.of_equiv φ.range (QuotientGroup.quotientKerEquivRange φ).symm.toEquiv
  · -- a subgroup of a finite `2`-group is a `2`-group
    exact (hpg.of_injective (Subgroup.subtype φ.range) Subtype.coe_injective).of_equiv
      (QuotientGroup.quotientKerEquivRange φ).symm
  · intro h1
    simp only [QuotientGroup.mk'_apply] at h1
    have hmem : g ∈ K := (QuotientGroup.eq_one_iff (N := K) g).mp h1
    have hφ : φ g = 1 := MonoidHom.mem_ker.mp hmem
    exact hmk (by simpa [φ] using hφ)

/-- **`G_∅` is residually a finite `2`-group**, in the universe generality of the target
statement (`F : Type*` rather than `F : Type`).

The argument is that of `Work.ClassFieldTower.residuallyFiniteTwoGroup_galoisGroup`: for
`σ ≠ 1` pick `x` with `σ x ≠ x`; the normal closure `L` of `F⟮x⟯` inside `F_∅` is finite
dimensional and Galois over `F`, so `Gal(L/F)` is a finite `2`-group (`M.proP`), the restriction
map `G_∅ →* Gal(L/F)` is surjective and does not kill `σ`. -/
theorem residuallyFiniteTwoGroup_galoisGroup_univ {F : Type*} [Field F] [NumberField F]
    (M : MaximalUnramifiedProP.{0} F 2) : ResiduallyFiniteTwoGroup (galoisGroup M) := by
  classical
  intro σ hσ
  have hne : ∃ x : M.K, σ x ≠ x := by
    by_contra h
    exact hσ (AlgEquiv.ext (fun x => by by_contra hx; exact h ⟨x, hx⟩))
  obtain ⟨x, hx⟩ := hne
  -- the field `F⟮x⟯` is finite dimensional over `F`, since `F_∅/F` is algebraic
  let E : IntermediateField F M.K := IntermediateField.adjoin F ({x} : Set M.K)
  haveI hfdE : FiniteDimensional F E :=
    IntermediateField.finiteDimensional_adjoin
      (fun z _ => IsAlgebraic.isIntegral (Algebra.IsAlgebraic.isAlgebraic z))
  -- the normal closure of `F⟮x⟯` inside `F_∅` is finite dimensional and Galois over `F`
  let L : IntermediateField F M.K := IntermediateField.normalClosure F E M.K
  haveI hfdL : FiniteDimensional F L := normalClosure.is_finiteDimensional F E M.K
  haveI hgalL : IsGalois F L := IsGalois.normalClosure F E M.K
  haveI hnormL : Normal F L := inferInstance
  let φ : galoisGroup M →* (↥L ≃ₐ[F] ↥L) :=
    AlgEquiv.restrictNormalHom (F := F) (K₁ := M.K) ↥L
  -- `σ` does not act trivially on `L`
  have hφσ : φ σ ≠ 1 := by
    intro h
    have hxmem : x ∈ L :=
      (IntermediateField.subset_adjoin F ({x} : Set M.K)).trans
        (IntermediateField.le_normalClosure E) (by simp)
    have h1 : (φ σ) ⟨x, hxmem⟩ = (1 : ↥L ≃ₐ[F] ↥L) ⟨x, hxmem⟩ := by rw [h]
    have h2 : (↑((φ σ) ⟨x, hxmem⟩) : M.K) = (↑(⟨x, hxmem⟩ : ↥L) : M.K) := by rw [h1]; rfl
    rw [AlgEquiv.restrictNormalHom_apply L σ ⟨x, hxmem⟩] at h2
    exact hx h2
  have hpgL : IsPGroup 2 (↥L ≃ₐ[F] ↥L) := M.proP L hfdL hgalL
  let N : Subgroup (galoisGroup M) := φ.ker
  have hN : N.Normal := MonoidHom.normal_ker φ
  haveI : N.Normal := hN
  refine ⟨N, hN, ?_, ?_, ?_⟩
  · haveI : Finite (↥L ≃ₐ[F] ↥L) := Finite.of_fintype _
    exact Finite.of_equiv (↥φ.range) (QuotientGroup.quotientKerEquivRange φ).symm.toEquiv
  · have hpgrange : IsPGroup 2 ↥(φ.range) :=
      hpgL.of_injective (Subgroup.subtype φ.range) Subtype.coe_injective
    exact hpgrange.of_equiv (QuotientGroup.quotientKerEquivRange φ).symm
  · intro h
    have hmem : σ ∈ N :=
      (QuotientGroup.eq_one_iff (N := N) σ).mp (by simpa [QuotientGroup.mk'_apply] using h)
    exact hφσ hmem

/-- **The group presented by a pro-`2` presentation `(P1)` of `G_∅` is residually a finite
`2`-group.**

The presentation map `FreeGroup.lift g : FreeGroup (Fin d) →* G_∅` has kernel the normal closure
of the words `w` (`hker`), so it factors through an injective homomorphism
`presentedGroup d r w →* G_∅`.  Since `G_∅` is residually a finite `2`-group
(`residuallyFiniteTwoGroup_galoisGroup_univ`), so are its subgroups, and hence -- transporting
along the identification of the two quotients of the free group -- so is `presentedGroup d r w`. -/
theorem residuallyFiniteTwoGroup_presented (F : Type*) [Field F] [NumberField F] (d r : ℕ)
    (M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} F 2)
    (g : Fin d → Work.ClassFieldTower.galoisGroup M) (w : Fin r → FreeGroup (Fin d))
    (hker : MonoidHom.ker (FreeGroup.lift g) = Subgroup.normalClosure (Set.range w))
    (hdense : (Subgroup.closure (Set.range g)).topologicalClosure = ⊤) :
    Work.ClassFieldTower.ResiduallyFiniteTwoGroup
      (Work.ShafarevichKoch.presentedGroup d r w) := by
  -- `G_∅` is residually a finite `2`-group, hence so is every subgroup of it
  have hres : Work.ClassFieldTower.ResiduallyFiniteTwoGroup
      (Work.ClassFieldTower.galoisGroup M) := residuallyFiniteTwoGroup_galoisGroup_univ M
  have hsub : Work.ClassFieldTower.ResiduallyFiniteTwoGroup ↥(FreeGroup.lift g).range :=
    residuallyFiniteTwoGroup_of_injective (Subgroup.subtype (FreeGroup.lift g).range)
      Subtype.coe_injective hres
  -- `FreeGroup (Fin d) ⧸ ker (lift g) ≃* (lift g).range`
  have hq : Work.ClassFieldTower.ResiduallyFiniteTwoGroup
      (FreeGroup (Fin d) ⧸ MonoidHom.ker (FreeGroup.lift g)) :=
    Work.ClassFieldTower.residuallyFiniteTwoGroup_of_mulEquiv
      (QuotientGroup.quotientKerEquivRange (FreeGroup.lift g)) hsub
  -- `ker (lift g) = ⟪w⟫` identifies the two quotients of the free group
  have hmap : Subgroup.map (MulEquiv.refl (FreeGroup (Fin d)))
      (MonoidHom.ker (FreeGroup.lift g)) = Subgroup.normalClosure (Set.range w) := by
    simpa using hker
  have e : (FreeGroup (Fin d) ⧸ MonoidHom.ker (FreeGroup.lift g)) ≃*
      (FreeGroup (Fin d) ⧸ Subgroup.normalClosure (Set.range w)) :=
    QuotientGroup.congr _ _ (MulEquiv.refl _) hmap
  exact Work.ClassFieldTower.residuallyFiniteTwoGroup_of_mulEquiv e.symm hq

end Work.ShafarevichKoch
