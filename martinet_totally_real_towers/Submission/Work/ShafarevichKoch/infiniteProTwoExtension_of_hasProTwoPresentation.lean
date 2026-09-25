import Mathlib
import Submission.Work.ShafarevichKoch.RelationBound
import Submission.Work.ShafarevichKoch.exists_quotient_of_finite_unramified
import Submission.Work.ShafarevichKoch.residuallyFiniteTwoGroup_presented

/-!
# `Work.ShafarevichKoch.infiniteProTwoExtension_of_hasProTwoPresentation`

A pro-`2` presentation `HasProTwoPresentation F 5 r` of the maximal unramified pro-`2` extension
`F_∅` of a number field `F` (five generators, `r ≤ 6` relations, the `g_i` generating `G_∅`
topologically) together with a genus level of `F` (`HasGenusLevel F`: an unramified exponent-`2`
Galois extension of degree `2^5`) forces the maximal unramified pro-`2` extension of `F` to be
**infinite**.

## The argument

Let `G = presentedGroup 5 r w = FreeGroup (Fin 5) ⧸ ⟪w⟫` be the abstract group presented by the
pro-`2` presentation.  By construction `G` is isomorphic to the dense subgroup
`H = range (FreeGroup.lift g) ≤ G_∅` of `G_∅`, so `Infinite G` implies `Infinite G_∅`; it
therefore suffices to prove `G` infinite.  This is Golod--Shafarevich:

* the relator set `rel = w '' univ` satisfies `rel.card ≤ r ≤ 6`, hence the Golod--Shafarevich
  inequality `4 · rel.card ≤ 5 · 5`;
* `G` is residually a finite `2`-group
  (`Work.ShafarevichKoch.residuallyFiniteTwoGroup_presented`), so if `G` were finite it would be a
  finite `2`-group (`Work.ClassFieldTower.isPGroup_two_of_residuallyFiniteTwo_of_finite`), and the
  finite `2`-group Golod--Shafarevich inequality
  (`Commons.GroupTheory.ProPGroup.golod_shafarevich_presentation_card_lt`) gives the contradiction
  `5 · 5 < 4 · rel.card`;
* the remaining hypothesis of that inequality is **minimality** of the chosen generating set:
  no generating finset of `G` has fewer than `5` elements.  This is where the genus level is used:
  the degree-`2^5` unramified exponent-`2` level of `F` gives, via
  `Work.ShafarevichKoch.exists_quotient_of_finite_unramified`, a **surjection** `G ↠ (𝔽₂)^5`; the
  image of a generating finset of `G` generates `(𝔽₂)^5`, which needs `5` elements.

This derivation uses the presentation direction of the Shafarevich--Koch interface only; the
reverse (realization) direction is not needed for the infinitude conclusion.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Classical

noncomputable section

namespace Work.ShafarevichKoch

/-- **A generating finset of `(ℤ/2)^n` (written multiplicatively) has at least `n` elements.**
Transporting along the (additive) identification `Multiplicative (Fin n → ZMod 2) ≃ (𝔽₂)^n`, a
generating subgroup is an `𝔽₂`-subspace and a generating finset spans it, so its card is at least
the `𝔽₂`-dimension `n`. -/
private theorem card_le_of_closure_eq_top_multiplicative {n : ℕ}
    (A : Finset (Multiplicative (Fin n → ZMod 2)))
    (hA : Subgroup.closure (A : Set (Multiplicative (Fin n → ZMod 2))) = ⊤) :
    n ≤ A.card := by
  classical
  have htop : Subgroup.toAddSubgroup' (⊤ : Subgroup (Multiplicative (Fin n → ZMod 2))) = ⊤ :=
    OrderIso.map_top _
  have hclos : AddSubgroup.closure
      (Multiplicative.ofAdd ⁻¹' (A : Set (Multiplicative (Fin n → ZMod 2)))) = ⊤ := by
    rw [← Subgroup.toAddSubgroup'_closure (S := (A : Set (Multiplicative (Fin n → ZMod 2)))),
      hA, htop]
  set B : Finset (Fin n → ZMod 2) := A.image Multiplicative.toAdd with hBdef
  have hBcoe : (Multiplicative.ofAdd ⁻¹' (A : Set (Multiplicative (Fin n → ZMod 2))))
      = (B : Set (Fin n → ZMod 2)) := by
    ext y
    simp only [Set.mem_preimage, Finset.mem_coe, hBdef, Finset.mem_image]
    exact ⟨fun hy => ⟨Multiplicative.ofAdd y, hy, rfl⟩,
      by rintro ⟨a, ha, rfl⟩; simpa using ha⟩
  have hspan : Submodule.span (ZMod 2) (B : Set (Fin n → ZMod 2)) = ⊤ := by
    refine eq_top_iff.mpr fun x _ => ?_
    have hx : x ∈ AddSubgroup.closure (B : Set (Fin n → ZMod 2)) := by
      rw [← hBcoe, hclos]; trivial
    have hle : AddSubgroup.closure (B : Set (Fin n → ZMod 2))
        ≤ (Submodule.span (ZMod 2) (B : Set (Fin n → ZMod 2))).toAddSubgroup :=
      (AddSubgroup.closure_le _).mpr (fun y hy => Submodule.subset_span hy)
    exact hle hx
  have hfr : Module.finrank (ZMod 2) (Fin n → ZMod 2) ≤ B.card := by
    have h := finrank_span_le_card (R := ZMod 2) (M := Fin n → ZMod 2)
      (s := (B : Set (Fin n → ZMod 2)))
    rw [hspan, finrank_top, Finset.toFinset_coe] at h
    exact h
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hfr
  exact hfr.trans (by rw [hBdef]; exact Finset.card_image_le)

/-- **A pro-`2` presentation with five generators and at most six relators, plus a genus level,
gives an infinite maximal unramified pro-`2` extension.** -/
theorem infiniteProTwoExtension_of_hasProTwoPresentation (F : Type*) [Field F] [NumberField F]
    {r : ℕ} (hgenus : Work.ClassFieldTower.HasGenusLevel F)
    (h : Work.ShafarevichKoch.HasProTwoPresentation F 5 r) (hr : r ≤ 6) :
    Work.ClassFieldTower.InfiniteProTwoExtension F := by
  classical
  -- the pro-`2` presentation of `G_∅`
  obtain ⟨M, g, w, hker, hdense⟩ := h
  -- the abstract group presented by it, and the relator finset
  let G := presentedGroup 5 r w
  let rel : Finset (FreeGroup (Fin 5)) := Finset.image w Finset.univ
  have hrelcoe : (rel : Set (FreeGroup (Fin 5))) = Set.range w := by
    simp [rel, Set.range]
  -- `G` is residually a finite `2`-group
  have hres : Work.ClassFieldTower.ResiduallyFiniteTwoGroup G :=
    residuallyFiniteTwoGroup_presented F 5 r M g w hker hdense
  -- the genus level of `F` and the resulting surjection `G ↠ (𝔽₂)^5`
  obtain ⟨L, iL, iNL, iAL, hfd, hgal, hdiff, hexp, hcard⟩ := hgenus
  letI : Field L := iL
  letI : NumberField L := iNL
  letI : Algebra F L := iAL
  letI : FiniteDimensional F L := hfd
  letI : IsGalois F L := hgal
  have hpgL : IsPGroup 2 (L ≃ₐ[F] L) := fun σ => ⟨1, by rw [pow_one]; exact hexp σ⟩
  obtain ⟨N, hN, ⟨eN⟩⟩ :=
    exists_quotient_of_finite_unramified F 5 r M g w hker hdense L hdiff hpgL
  haveI : N.Normal := hN
  haveI : IsMulCommutative (L ≃ₐ[F] L) :=
    ⟨Std.Commutative.mk (Work.ClassFieldTower.mul_comm_of_sq_eq_one hexp)⟩
  obtain ⟨e5⟩ :=
    Commons.GroupTheory.SpecificGroups.ZModProd.exists_mulEquiv_multiplicative_fin_zmod_two_of_fintype_commutative_pow_two_eq_one_card
      (G := L ≃ₐ[F] L) hexp hcard
  let ψ : G →* Multiplicative (Fin 5 → ZMod 2) :=
    e5.toMonoidHom.comp (eN.toMonoidHom.comp (QuotientGroup.mk' N))
  have hψ : Function.Surjective ψ :=
    e5.surjective.comp (eN.surjective.comp (QuotientGroup.mk'_surjective N))
  -- minimality of the generating set of `G`
  have hmin : ∀ S : Finset G, Subgroup.closure (S : Set G) = ⊤ → 5 ≤ S.card := by
    intro S hS
    have hImg : Subgroup.closure ((S.image ψ : Finset (Multiplicative (Fin 5 → ZMod 2))) :
        Set (Multiplicative (Fin 5 → ZMod 2))) = ⊤ := by
      rw [Finset.coe_image, ← MonoidHom.map_closure ψ (S : Set G), hS,
        Subgroup.map_top_of_surjective _ hψ]
    calc 5 ≤ (S.image ψ).card := card_le_of_closure_eq_top_multiplicative _ hImg
      _ ≤ S.card := Finset.card_image_le
  -- the numerical Golod--Shafarevich inequality
  have hrelcard : rel.card ≤ 6 := by
    show (Finset.image w Finset.univ).card ≤ 6
    calc (Finset.image w Finset.univ).card ≤ (Finset.univ : Finset (Fin r)).card :=
          Finset.card_image_le
      _ = r := by simp
      _ ≤ 6 := hr
  have hineq : 4 * rel.card ≤ 5 * 5 := by omega
  -- the presentation of `G` by the relator finset `rel`
  have hpres : Nonempty (G ≃*
      FreeGroup (Fin 5) ⧸ Subgroup.normalClosure (rel : Set (FreeGroup (Fin 5)))) := by
    have h : Subgroup.normalClosure (Set.range w) = Subgroup.normalClosure
        (rel : Set (FreeGroup (Fin 5))) := congrArg Subgroup.normalClosure hrelcoe.symm
    exact ⟨QuotientGroup.congr _ _ (MulEquiv.refl (FreeGroup (Fin 5))) (by simp [h])⟩
  -- `G` is infinite, by Golod--Shafarevich
  have hGinf : Infinite G := by
    by_contra hfin
    haveI : Finite G := not_infinite_iff_finite.mp hfin
    haveI : Fintype G := Fintype.ofFinite G
    have hpgG : IsPGroup 2 G :=
      Work.ClassFieldTower.isPGroup_two_of_residuallyFiniteTwo_of_finite hres inferInstance
    haveI : Nontrivial G := by
      rw [← not_subsingleton_iff_nontrivial]
      intro hss
      haveI := hss
      have hcl : Subgroup.closure ((∅ : Finset G) : Set G) = ⊤ := by
        refine eq_top_iff.mpr fun x _ => ?_
        rw [Subsingleton.elim x 1]
        exact Subgroup.one_mem _
      have hh := hmin ∅ hcl
      simp only [Finset.card_empty] at hh
      omega
    have hkey :=
      Commons.GroupTheory.ProPGroup.golod_shafarevich_presentation_card_lt 2 hpgG rel hpres hmin
    rw [Fintype.card_fin] at hkey
    omega
  -- `G ≅ range (FreeGroup.lift g)`, a subgroup of `G_∅`
  have hisoH : G ≃* ↥(FreeGroup.lift g).range :=
    (QuotientGroup.congr (Subgroup.normalClosure (Set.range w)) (FreeGroup.lift g).ker
      (MulEquiv.refl (FreeGroup (Fin 5))) (by rw [hker]; simp)).trans
      (QuotientGroup.quotientKerEquivRange (FreeGroup.lift g))
  haveI : Infinite G := hGinf
  haveI : Infinite ↥(FreeGroup.lift g).range :=
    Infinite.of_injective (β := G) (α := ↥(FreeGroup.lift g).range) ⇑hisoH hisoH.injective
  exact ⟨M, Infinite.of_injective (Subgroup.subtype (FreeGroup.lift g).range)
    Subtype.coe_injective⟩

end Work.ShafarevichKoch
