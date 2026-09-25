import Mathlib
import Submission.Work.ClassFieldTower.ProTwoDefs

namespace Work.ClassFieldTower

/-- **`RealizedByUnramifiedExtensions` is invariant under group isomorphisms**: if every finite
`2`-quotient of `H` is the Galois group of a finite unramified Galois extension of `F`, the same
holds for `G`, via any isomorphism `e : G ≃* H`.

Proof strategy: for `N : Subgroup G` normal with `G ⧸ N` a finite `2`-group, use the normal
subgroup `N.map e` of `H` and the isomorphism `QuotientGroup.congr e N (N.map e) : G ⧸ N ≃* H ⧸ N.map e`
(together with `Subgroup.Normal.map`/`QuotientGroup.quotientMulEquivOfEq` as needed). -/
theorem realizedByUnramifiedExtensions_of_mulEquiv {F : Type} [Field F] [NumberField F]
    {G H : Type} [Group G] [Group H] (e : G ≃* H) (h : RealizedByUnramifiedExtensions F H) :
    RealizedByUnramifiedExtensions F G := by
  intro N hN hfin hp
  have hN' : (N.map (e : G →* H)).Normal := hN.map (e : G →* H) e.surjective
  -- the induced isomorphism of quotients
  let φ : G ⧸ N ≃* H ⧸ N.map (e : G →* H) :=
    QuotientGroup.congr N (N.map (e : G →* H)) e rfl
  have hfH : Finite (H ⧸ N.map (e : G →* H)) :=
    Finite.of_equiv (G ⧸ N) (h := hfin) φ.toEquiv
  have hp' : IsPGroup 2 (H ⧸ N.map (e : G →* H)) := hp.of_equiv φ
  obtain ⟨L, fld, nf, alg, fd, gal, hdiff, ⟨ψ⟩⟩ := h (N.map (e : G →* H)) hfH hp'
  exact ⟨L, fld, nf, alg, fd, gal, hdiff, ⟨ψ.trans φ.symm⟩⟩

end Work.ClassFieldTower
