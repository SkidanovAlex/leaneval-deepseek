import Mathlib
import Submission.Work.RatHurewicz.product_ratH_vanishing_rat
import Submission.Work.Stems.fin_prod_ratH_vanishing

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.RatHurewicz

open CategoryTheory CategoryTheory.Limits

set_option linter.style.haveILetI false

noncomputable section

/-- **The `ℤ^r` (free) case of `EMVan`, without the integral Serre exact range hypothesis.**

Let `k ≥ 2` and let `Z` be `(k-1)`-connected with vanishing rational reduced homology in the
range `k < j ≤ 2k-1`.  Then the `r`-fold product `Fin r → Z` (the empty product for `r = 0`, i.e.
`PUnit`) has the same vanishing property.

This is `Work.Stems.fin_prod_ratH_vanishing` with the hypothesis
`Work.Serre.SerreExactRangeCorrected` removed: the induction step uses the *rational* product step
`Work.RatHurewicz.product_ratH_vanishing_rat` (Künneth in the vanishing range, proved from the
rational pair comparison `Work.Serre.ratSerrePairComparison`) instead of the integral Serre exact
sequence.  Everything else — the homeomorphism `(Fin (r+1) → Z) ≅ (Fin r → Z) × Z` splitting off
the last coordinate, `(k-1)`-connectivity of products, and homotopy invariance of rational
homology — is transport of the induction hypothesis. -/
theorem fin_prod_ratH_vanishing_rat (k : ℕ) (hk : 2 ≤ k) (r : ℕ) {Z : Type} [TopologicalSpace Z]
    (z₀ : Z) (hZc : Work.Serre.Conn Z z₀ k)
    (hZ : ∀ j : ℕ, k < j → j ≤ 2 * k - 1 →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of Z) j)) :
    ∀ j : ℕ, k < j → j ≤ 2 * k - 1 →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Fin r → Z)) j) := by
  induction r with
  | zero =>
    intro j hj1 _
    haveI : Nonempty (Fin 0 → Z) := ⟨fun i => i.elim0⟩
    haveI : Subsingleton (Fin 0 → Z) := ⟨fun f g => funext fun i => i.elim0⟩
    exact (Work.Serre.ratAcyclic_of_contractible (Fin 0 → Z)).isZero_ratH (by omega)
  | succ r ih =>
    intro j hj1 hj2
    refine Work.Stems.isZero_ratH_of_homeomorph (Work.Stems.homeoFinSucc Z r) j ?_
    exact Work.RatHurewicz.product_ratH_vanishing_rat k hk (fun _ => z₀) z₀
      (Work.Stems.conn_fin_prod k r z₀ hZc) hZc ih hZ j hj1 hj2

end

end Work.RatHurewicz
