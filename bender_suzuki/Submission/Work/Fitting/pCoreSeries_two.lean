import Mathlib
import Submission.Work.Fitting.Defs
import Submission.Work.Fitting.pCoreSeries_one

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Fitting.pCoreSeries_two`

The second term of the upper `p`-series of a finite group `G` is `O_{p',p}(G)`.

Indeed `pCoreSeries p G 2 = O_p(G/O_{p'}(G)).comap (mk' O_{p'}(G))` by definition
(`pCoreSeries_succ`), and `pCoreSeries p G 1 = O_{p'}(G)` (`pCoreSeries_one`), so the
left-hand side is `pPrimePCore p G`.
-/

noncomputable section

open Classical

namespace Work.Fitting

theorem pCoreSeries_two (p : ℕ) (G : Type*) [Group G] [Finite G] :
    Work.Fitting.pCoreSeries p G 2 = Work.Fitting.pPrimePCore p G := by
  have hif : (fun q : ℕ => (if Even 1 then q ≠ p else q = p)) = (fun q => q = p) := by
    funext q; simp
  rw [show (2:ℕ) = 1 + 1 from rfl, pCoreSeries_succ, hif, pPrimePCore]
  have hcomp : (QuotientGroup.quotientMulEquivOfEq (pCoreSeries_one p G)).toMonoidHom.comp
        (QuotientGroup.mk' (pCoreSeries p G 1)) = QuotientGroup.mk' (pPrimeCore p G) := by
    ext x
    simp [QuotientGroup.quotientMulEquivOfEq_mk]
  have hcomap : (piCore (fun q => q = p) (G ⧸ pPrimeCore p G)).comap
        (QuotientGroup.quotientMulEquivOfEq (pCoreSeries_one p G)).toMonoidHom =
      piCore (fun q => q = p) (G ⧸ pCoreSeries p G 1) :=
    piCore_comap_of_bijective
      (QuotientGroup.quotientMulEquivOfEq (pCoreSeries_one p G)).toMonoidHom
      (QuotientGroup.quotientMulEquivOfEq (pCoreSeries_one p G)).injective
      (QuotientGroup.quotientMulEquivOfEq (pCoreSeries_one p G)).surjective
  rw [← hcomap, Subgroup.comap_comap, hcomp]

end Work.Fitting
