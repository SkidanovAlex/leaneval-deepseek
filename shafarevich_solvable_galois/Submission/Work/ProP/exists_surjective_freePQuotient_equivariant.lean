import Mathlib
import Submission.Work.ProP.Defs
import Submission.Work.ProP.exists_pCentralSeries_le_ker
import Submission.Work.Shrinking.PCentralQuotient
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.ProP

open Work.Shrinking

/-- **The generic kernel corollary, `G`-equivariantly.**  Let `G` act on `F^(n)` by
automorphisms (`ρ`), and let `P` be a finite `G`-operator `p`-group
(`[MulDistribMulAction G P]`, so that `MulDistribMulAction.toMulAut G P g` is the automorphism
induced by `g`).  If `φ : F^(n) →* P` is a `G`-equivariant surjection, then `P` is a
`G`-equivariant quotient of one of the finite `G`-operator groups `F^(n)/F^(n)(ν)`: there are
`ν`, an action `Φ` of `G` on `FreePQuotient p n ν` compatible with the projection, and a
surjective `f` with `f (Φ g y) = (MulDistribMulAction.toMulAut G P g) (f y)`.

Proof: take `ν` with `F^(n)(ν) ≤ φ.ker` (cofinality of the filtration, available as
`Work.ProP.exists_pCentralSeries_le_ker`).  The descended action `Φ` is constructed as in
`Work.ProP.exists_freePQuotientAction`: `F^(n)(ν)` is characteristic, so
`QuotientGroup.congr` provides the induced automorphism
`Φ g (mk x) = mk (ρ g x)` (see `Work.Shrinking.quotAut`, `Work.Shrinking.quotAut_mk`); check that
`g ↦ Φ g` is a homomorphism using `MulEquiv.ext` and `QuotientGroup.mk'_surjective`.  The
factorization `f` of `φ` through `QuotientGroup.lift` is equivariant: `f ∘ Φ g` and
`toMulAut g ∘ f` are group homomorphisms agreeing on the classes of the free generators, because
`φ` is equivariant and `F^(n)(ν)` is `G`-stable. -/
theorem exists_surjective_freePQuotient_equivariant {G : Type*} [Group G] {p n : ℕ}
    [Fact p.Prime] {P : Type*} [Group P] [Finite P] [MulDistribMulAction G P]
    (hP : IsPGroup p P) (ρ : G →* MulAut (FreeGroup (Fin n))) (φ : FreeGroup (Fin n) →* P)
    (hφ : Function.Surjective φ)
    (heq : ∀ (g : G) (x : FreeGroup (Fin n)),
      φ (ρ g x) = (MulDistribMulAction.toMulAut G P g) (φ x)) :
    ∃ (ν : ℕ) (Φ : G →* MulAut (FreePQuotient p n ν)) (f : FreePQuotient p n ν →* P),
      Function.Surjective f ∧
      (∀ (g : G) (x : FreeGroup (Fin n)),
        Φ g (freePQuotientMk p n ν x) = freePQuotientMk p n ν (ρ g x)) ∧
      (∀ (g : G) (y : FreePQuotient p n ν),
        f (Φ g y) = (MulDistribMulAction.toMulAut G P g) (f y)) := by
  -- cofinality of the filtration: some term is killed by `φ`
  obtain ⟨ν, hν⟩ := exists_pCentralSeries_le_ker (p := p) n hP φ
  let N : Subgroup (FreeGroup (Fin n)) := Work.Shrinking.pCentralSeries p (FreeGroup (Fin n)) ν
  -- `N` is characteristic, hence invariant under the action `ρ`
  have hNm : ∀ g : G, Subgroup.map ((ρ g : MulAut (FreeGroup (Fin n))) :
      FreeGroup (Fin n) →* FreeGroup (Fin n)) N = N := fun g =>
    Work.Shrinking.map_pCentralSeries_eq p (ρ g) ν
  -- the descended action of `G` on `F^(n)/N`
  let Φ : G →* MulAut (FreePQuotient p n ν) :=
  { toFun := fun g => QuotientGroup.congr N N (ρ g) (hNm g)
    map_one' := by
      refine MulEquiv.ext fun y => ?_
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N y
      show QuotientGroup.congr N N (ρ 1) (hNm 1) (QuotientGroup.mk' N x)
        = (1 : MulAut (FreePQuotient p n ν)) (QuotientGroup.mk' N x)
      rw [QuotientGroup.congr_mk', MulAut.one_apply]
      simp
    map_mul' g h := by
      refine MulEquiv.ext fun y => ?_
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N y
      show QuotientGroup.mk' N ((ρ (g * h)) x)
        = (QuotientGroup.congr N N (ρ g) (hNm g)
            * QuotientGroup.congr N N (ρ h) (hNm h)) (QuotientGroup.mk' N x)
      rw [MulAut.mul_apply, QuotientGroup.congr_mk', QuotientGroup.congr_mk']
      simp only [map_mul, MulAut.mul_apply] }
  -- the compatibility of `Φ` with the projection
  have hΦ : ∀ (g : G) (x : FreeGroup (Fin n)),
      Φ g (freePQuotientMk p n ν x) = freePQuotientMk p n ν (ρ g x) :=
    fun g x => QuotientGroup.congr_mk' N N (ρ g) (hNm g) x
  -- the factorization of `φ` through the quotient
  have hNker : N ≤ φ.ker := hν
  let f : FreePQuotient p n ν →* P := QuotientGroup.lift N φ hNker
  have hf_mk : ∀ x : FreeGroup (Fin n), f (QuotientGroup.mk' N x) = φ x :=
    fun x => QuotientGroup.lift_mk' N hNker x
  have hf : Function.Surjective f :=
    QuotientGroup.lift_surjective_of_surjective N φ hφ hNker
  have hΦ' : ∀ (g : G) (x : FreeGroup (Fin n)),
      Φ g (QuotientGroup.mk' N x) = QuotientGroup.mk' N (ρ g x) :=
    fun g x => QuotientGroup.congr_mk' N N (ρ g) (hNm g) x
  -- equivariance of the factorization
  have hfeq : ∀ (g : G) (y : FreePQuotient p n ν),
      f (Φ g y) = (MulDistribMulAction.toMulAut G P g) (f y) := by
    intro g y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N y
    rw [hΦ' g x, hf_mk, hf_mk]
    exact heq g x
  exact ⟨ν, Φ, f, hf, hΦ, hfeq⟩

end Work.ProP
