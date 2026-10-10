import Mathlib.Algebra.Group.End
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.QuotientGroup.Defs
import Submission.Work.ProP.Defs
import Submission.Work.Shrinking.PCentralQuotient
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.ProP

open Work.Shrinking

/-- **The generic kernel quotients carry the induced `G`-action.**  If `G` acts on the free
group `F^(n)` by automorphisms (`ρ : G →* MulAut (FreeGroup (Fin n))`), then each term of the
`p`-central filtration is `G`-stable — it is characteristic, so
`(pCentralSeries p F ν).map (ρ g).toMonoidHom = pCentralSeries p F ν` — and hence the quotient
`F^(n)/F^(n)(ν)` inherits an action of `G`, compatible with the projection: the action sends the
class of `x` to the class of `ρ g x`.

This is the first half of the `G`-operator refinement of item 2 of the assignment (the paper's
`F^(n)` is a free pro-`p` `G`-operator group): it is what lets one say that
`F^(n)/F^(n)(ν)` is a `G`-operator group and that the acting group can be transported through
the factorization.

Proof: for each `g`, `QuotientGroup.congr` applied to `ρ g` and the stability of the kernel
gives an automorphism of the quotient (`Work.Shrinking.map_pCentralSeries_eq` is exactly the
stability, and `QuotientGroup.congr_mk` computes it on classes); then check `1` and multiplication
using `MulEquiv.ext` and `QuotientGroup.mk'_surjective`, giving a homomorphism
`G →* MulAut (FreePQuotient p n ν)`.  The analogous construction for subquotients, together with
the class-level computation, is `Work.Shrinking.quotAut` and `Work.Shrinking.quotAut_mk` in
`Submission/Work/Shrinking/PCentralQuotient.lean`. -/
theorem exists_freePQuotientAction {G : Type*} [Group G] (p n ν : ℕ)
    (ρ : G →* MulAut (FreeGroup (Fin n))) :
    ∃ Φ : G →* MulAut (FreePQuotient p n ν),
      ∀ (g : G) (x : FreeGroup (Fin n)),
        Φ g (freePQuotientMk p n ν x) = freePQuotientMk p n ν (ρ g x) := by
  have key : ∀ g : G,
      (pCentralSeries p (FreeGroup (Fin n)) ν).map (↑(ρ g))
        = pCentralSeries p (FreeGroup (Fin n)) ν := by
    intro g
    rw [← MulEquiv.toMonoidHom_eq_coe]
    exact map_pCentralSeries_eq p (ρ g) ν
  refine ⟨{ toFun := fun g => QuotientGroup.congr _ _ (ρ g) (key g),
            map_one' := ?_, map_mul' := ?_ }, ?_⟩
  · refine MulEquiv.ext fun x => ?_
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective
      (pCentralSeries p (FreeGroup (Fin n)) ν) x
    show QuotientGroup.mk' (pCentralSeries p (FreeGroup (Fin n)) ν) ((ρ 1) y)
      = QuotientGroup.mk' (pCentralSeries p (FreeGroup (Fin n)) ν) y
    rw [MonoidHom.map_one]
    rfl
  · intro g h
    refine MulEquiv.ext fun x => ?_
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective
      (pCentralSeries p (FreeGroup (Fin n)) ν) x
    show QuotientGroup.mk' (pCentralSeries p (FreeGroup (Fin n)) ν) ((ρ (g * h)) y)
      = QuotientGroup.mk' (pCentralSeries p (FreeGroup (Fin n)) ν) ((ρ g) ((ρ h) y))
    rw [MonoidHom.map_mul]
    rfl
  · intro g x
    exact QuotientGroup.congr_mk' _ _ (ρ g) (key g) x

end Work.ProP
