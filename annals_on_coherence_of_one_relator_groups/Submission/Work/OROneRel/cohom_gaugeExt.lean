import Mathlib
import Submission.Work.OROneRel.globalGauge
import Submission.Work.OROneRel.cohom_mk
import Submission.Work.OROneRel.lsig_gPosL
import Submission.Work.OROneRel.lsig_gNegL

/-!
# The global gauge has the prescribed weights

`Work.OROneRel.gaugeExt p q hq Wt` (`Submission/Work/OROneRel/globalGauge.lean`) extends a gauge
`Wt` of the band `[0, pq]` of the two-letter level graph (`c = tlW p q`, `a ↦ q`, `b ↦ -p`) to a
gauge of all of `ℤ` by the two `a`-chains `gPosL` (above the band) and `gNegL` (below it).

Here we prove the *weight identity* of the extension: if the given `Wt` has the prescribed weights
`cohom (tlW p q) (Wt i) = ofAdd i`, then so does the extension `gaugeExt p q hq Wt`.  This is one of
the two inputs of the global gauge besides `htree` (the other one, `htree`, is the tree condition on
the band and is transported by `gaugeExt_hwalk`); this file is the counterpart of
`gaugeExt_hwalk` for the weights.

The argument is the weight count along the chains: the `lsig`-weight of a word is additive
(`lsig_append`), the appended letter of the upper chain is `a` and contributes `tlW p q 0 = q`, the
appended letter of the lower chain is `a⁻¹` and contributes `-q`, and the band word at the level `t`
contributes `t` by the hypothesis (via `cohom_mk` and injectivity of `ofAdd`).  The two inductions
along the chains are `lsig_gPosL` and `lsig_gNegL`; the transfer from `lsig` to `cohom` is
`cohom_mk`.

Note that nothing here uses `1 ≤ p` or `htree`: only the *weights* of the gauge words are involved.
-/

namespace Work.OROneRel

noncomputable section

/-- **The global gauge has the prescribed weights.**  If a band gauge `Wt` satisfies
`cohom (tlW p q) (Wt i) = ofAdd i` for every `i`, then the global gauge `gaugeExt p q hq Wt` built
from it by the two `a`-chains satisfies the same identity at every level `i : ℤ`. -/
theorem cohom_gaugeExt {p q : ℕ} (hq : 1 ≤ q) {Wt : ℤ → FreeGroup (Fin 2)}
    (hcoh : ∀ i : ℤ, Work.OROneRel.cohom (Work.OROneRel.tlW p q) (Wt i) = Multiplicative.ofAdd i) :
    ∀ i : ℤ, Work.OROneRel.cohom (Work.OROneRel.tlW p q) (Work.OROneRel.gaugeExt p q hq Wt i)
      = Multiplicative.ofAdd i := by
  -- the band words have weight the level: `cohom_mk` turns the hypothesis into an `lsig` statement
  have hl : ∀ t : ℤ, lsig (tlW p q) (wordOf (Wt t)) = t := by
    intro t
    have h1 := cohom_mk (tlW p q) (wordOf (Wt t))
    rw [mk_wordOf, hcoh t] at h1
    exact Multiplicative.ofAdd.injective h1.symm
  intro i
  rw [gaugeExt, gaugeExtL]
  by_cases h : 0 ≤ i ∧ i ≤ npq p q
  · -- inside the band the global gauge *is* the band gauge
    rw [dif_pos h, mk_wordOf]
    exact hcoh i
  · rw [dif_neg h]
    by_cases h2 : i < 0
    · -- below the band: the word is the lower chain, whose weight is the level
      rw [dif_pos h2, cohom_mk, lsig_gNegL hl i h2]
    · -- above the band: the word is the upper chain, whose weight is the level
      rw [dif_neg h2, cohom_mk, lsig_gPosL hl i (by omega)]

end

end Work.OROneRel
