import Mathlib
import Submission.Work.Fitting.Defs
import Submission.Work.Fitting.pCoreSeries_two

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Fitting.pCoreSeries_three`

The third term of the upper `p`-series of a finite group `G` is

`pCoreSeries p G 3 = (O_{p'}(G/O_{p',p}(G))).comap (mk' O_{p',p}(G))`.

Indeed `pCoreSeries p G 3 = O_{p'}(G/pCoreSeries p G 2).comap (mk' (pCoreSeries p G 2))`
by definition (`pCoreSeries_succ`), and `pCoreSeries p G 2 = O_{p',p}(G)` (`pCoreSeries_two`),
so the left-hand side is the pullback of `O_{p'}` along the quotient by `O_{p',p}(G)`.
The two quotients `G/pCoreSeries p G 2` and `G/O_{p',p}(G)` are identified by
`QuotientGroup.quotientMulEquivOfEq`, and `O_π` is invariant under such isomorphisms
(`piCore_comap_of_bijective`).
-/

noncomputable section

open Classical

namespace Work.Fitting

theorem pCoreSeries_three (p : ℕ) (G : Type*) [Group G] [Finite G] :
    Work.Fitting.pCoreSeries p G 3 =
      (Work.Fitting.pPrimeCore p (G ⧸ Work.Fitting.pPrimePCore p G)).comap
        (QuotientGroup.mk' (Work.Fitting.pPrimePCore p G)) := by
  have hif : (fun q : ℕ => (if Even 2 then q ≠ p else q = p)) = (fun q => q ≠ p) := by
    funext q; simp
  rw [show (3 : ℕ) = 2 + 1 from rfl, pCoreSeries_succ, hif]
  have h2 : pCoreSeries p G 2 = pPrimePCore p G := pCoreSeries_two p G
  let e : G ⧸ pCoreSeries p G 2 ≃* G ⧸ pPrimePCore p G := QuotientGroup.quotientMulEquivOfEq h2
  have hcomp : e.toMonoidHom.comp (QuotientGroup.mk' (pCoreSeries p G 2)) =
      QuotientGroup.mk' (pPrimePCore p G) := by
    ext x
    exact QuotientGroup.quotientMulEquivOfEq_mk h2 x
  have hfin1 : Finite (G ⧸ pPrimePCore p G) :=
    Finite.of_surjective (QuotientGroup.mk' (pPrimePCore p G))
      (QuotientGroup.mk'_surjective (pPrimePCore p G))
  have hfin2 : Finite (G ⧸ pCoreSeries p G 2) :=
    Finite.of_surjective (QuotientGroup.mk' (pCoreSeries p G 2))
      (QuotientGroup.mk'_surjective (pCoreSeries p G 2))
  have hcomap : (piCore (fun q => q ≠ p) (G ⧸ pPrimePCore p G)).comap e.toMonoidHom =
      piCore (fun q => q ≠ p) (G ⧸ pCoreSeries p G 2) :=
    piCore_comap_of_bijective e.toMonoidHom e.injective e.surjective
  rw [← hcomap, Subgroup.comap_comap, hcomp]
  rfl

end Work.Fitting
