import Mathlib
import Submission.Work.ORLyndon.powDefs
import Submission.Work.ORLyndon.sigma_zeta_eq_one

namespace Work.ORLyndon

theorem levelOf_support_mapDomainRingHom_zeta {α : Type*} [DecidableEq α] {K : Type*} [Field K]
    (t : α) (r u : FreeGroup α) (l : ℕ) (hpow : r = u ^ l)
    (hσ : Work.OROneRel.sigma t u = 1)
    (c : MonoidAlgebra K (FreeGroup ({a : α // a ≠ t} × ℤ))) :
    ∀ g ∈ ((MonoidAlgebra.mapDomainRingHom K
        ((Work.ORLyndon.presentRho r).comp (Work.OROneRel.zeta t))) c).coeff.support,
      Work.ORLyndon.levelOf t r u l hpow hσ g = 1 := by
  classical
  intro g hg
  rw [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.coeff_mapDomain] at hg
  -- The support of the image is contained in the image of the support.
  have hsub := Finsupp.mapDomain_support
    (f := ⇑((Work.ORLyndon.presentRho r).comp (Work.OROneRel.zeta t))) (s := c.coeff)
  obtain ⟨x, _hx, hgx⟩ := Finset.mem_image.mp (hsub hg)
  rw [← hgx]
  simp only [MonoidHom.comp_apply, Work.ORLyndon.levelOf_presentRho]
  exact Work.ORLyndon.sigma_zeta_eq_one t x

end Work.ORLyndon
