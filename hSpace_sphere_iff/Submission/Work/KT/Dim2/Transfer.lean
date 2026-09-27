import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.diskQuot

/-!
# `Work.KT.D2.Transfer` — the quotient map `D² → S²` as an algebra isomorphism

A self-contained copy of `Work.KT.diskQuotAlgEquiv` (which lives in `SphereAux`, whose
`Work.KT.K0.map_cls` clashes with `Psi.Basic`), placed in the namespace `Work.KT.D2` so that it
can be imported alongside `psi_rank_one`.
-/

open Classical

namespace Work.KT.D2

noncomputable section

open Work.KT

open Classical in
/-- The algebra isomorphism `C(S^d, ℂ) ≅ Kpair ℝ^d` induced by a quotient map `q : D^d → S^d`
collapsing the boundary of the disc to the north pole.  Evaluation at the north pole corresponds
to evaluation at any boundary point. -/
def diskQuotAlgEquiv (d : ℕ) (q : C(Ball (Euc d), Sph (ModelSphere d)))
    (hq : Topology.IsQuotientMap q)
    (hfib : ∀ x x' : Ball (Euc d), q x = q x' →
      x = x' ∨ (x ∈ bdry (Euc d) ∧ x' ∈ bdry (Euc d)))
    (hnp : ∀ x ∈ bdry (Euc d), q x = sphKT_northPole d) :
    C(Sph (ModelSphere d), ℂ) ≃ₐ[ℂ] Kpair (Euc d) := by
  have hfac : ∀ g : Kpair (Euc d), Function.FactorsThrough (g : C(Ball (Euc d), ℂ)) q := by
    intro g a a' h
    rcases hfib a a' h with rfl | ⟨ha, ha'⟩
    · rfl
    · exact g.2 a ha a' ha'
  have hmem : ∀ h : C(Sph (ModelSphere d), ℂ), pullAlg q h ∈ Kpair (Euc d) := by
    intro h a ha a' ha'
    rw [show (pullAlg q h) a = h (q a) from rfl, show (pullAlg q h) a' = h (q a') from rfl,
      hnp a ha, hnp a' ha']
  have hinj : Function.Injective (pullAlg q) := by
    intro f g h
    ext y
    obtain ⟨x, rfl⟩ := hq.surjective y
    simpa using ContinuousMap.ext_iff.mp h x
  refine AlgEquiv.ofBijective ((pullAlg q).codRestrict (Kpair (Euc d)) hmem) ⟨?_, ?_⟩
  · exact (AlgHom.injective_codRestrict _ _ _).mpr hinj
  · intro g
    refine ⟨hq.lift (g : C(Ball (Euc d), ℂ)) (hfac g), ?_⟩
    apply Subtype.ext
    rw [AlgHom.coe_codRestrict]
    show pullAlg q (hq.lift (g : C(Ball (Euc d), ℂ)) (hfac g)) = (g : C(Ball (Euc d), ℂ))
    exact hq.lift_comp _ _

/-- The augmentation compatibility of `diskQuotAlgEquiv`. -/
lemma diskQuotAlgEquiv_aug (d : ℕ) (q : C(Ball (Euc d), Sph (ModelSphere d)))
    (hq : Topology.IsQuotientMap q)
    (hfib : ∀ x x' : Ball (Euc d), q x = q x' →
      x = x' ∨ (x ∈ bdry (Euc d) ∧ x' ∈ bdry (Euc d)))
    (hnp : ∀ x ∈ bdry (Euc d), q x = sphKT_northPole d)
    (y0 : Ball (Euc d)) (hy0 : y0 ∈ bdry (Euc d)) (h : C(Sph (ModelSphere d), ℂ)) :
    augPair (Euc d) y0 (diskQuotAlgEquiv d q hq hfib hnp h) = evalC (sphKT_northPole d) h := by
  have h1 : ((diskQuotAlgEquiv d q hq hfib hnp h : Kpair (Euc d)) : C(Ball (Euc d), ℂ)) y0
      = h (q y0) := rfl
  rw [show augPair (Euc d) y0 (diskQuotAlgEquiv d q hq hfib hnp h)
      = ((diskQuotAlgEquiv d q hq hfib hnp h : Kpair (Euc d)) : C(Ball (Euc d), ℂ)) y0
        from rfl, h1, hnp y0 hy0]
  rfl

end

end Work.KT.D2
