import Mathlib
import Submission.Work.CFT.Kummer.Defs
import Submission.Work.CFT.Kummer.Hypotheses
import Submission.Work.CFT.Kummer.Estimate
import Submission.Work.CFT.Kummer.units_rank_eq_two_of_totallyReal_cubic
import Submission.Work.CFT.Kummer.deltaK_eq_zero_of_totallyReal

/-!
# Shafarevich's estimate for a totally real cubic field and `p = 3`

The numerical inputs `r₁ + r₂ - 1 = 2` and `δ_{K,3} = 0` of Shafarevich's relation-rank estimate are
discharged here for a totally real field `K` of degree `3` (`NumberField.Units.rank K = 2` by
Dirichlet, and `δ_{K,3} = 0` since a totally real field contains no primitive cube root of unity),
giving the estimate in the form used by the class-field tower:

`dim_{𝔽₃} H²(G, 𝔽₃) ≤ dim_{𝔽₃} H¹(G, 𝔽₃) + 2`,

for `G = Gal(K_∅(3)/K)` the maximal everywhere-unramified pro-`3` group (represented by the
hypothesis bundle `Work.CFT.Kummer.UnramifiedShafarevich K 3 G`), and the finite-quotient
(Ch. 11 / Koch transfer) form used for a finite level of the tower.

## Main results

* `Work.CFT.Kummer.finrank_H2Fp_le_H1Fp_add_two`.
* `Work.CFT.Kummer.finrank_H2Fp_quotient_le_two` — the finite-quotient form
  `dim H²(G ⧸ N, 𝔽₃) ≤ dim H¹(G ⧸ N, 𝔽₃) + 2 + k` for `N` the normal closure of `k` elements
  which do not change the generator rank (Frattini elements).
* `Work.CFT.Kummer.finrank_H2Fp_quotient_le_two_of_frattini` — the same with the Frattini
  hypothesis discharged by `Work.CFT.Kummer.finrank_H1Fp_quotient_frattini`.
-/

open scoped nonZeroDivisors
open NumberField

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Work.CFT.Kummer

/-- **Shafarevich's relation-rank estimate for a totally real cubic field and `p = 3`**:
`dim_{𝔽₃} H²(G, 𝔽₃) ≤ dim_{𝔽₃} H¹(G, 𝔽₃) + 2` for the maximal everywhere-unramified pro-`3`
Galois group `G = Gal(K_∅(3)/K)`. -/
theorem finrank_H2Fp_le_H1Fp_add_two (K : Type*) [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (hdeg : Module.finrank ℚ K = 3)
    (G : Type) [Group G] [h : UnramifiedShafarevich K 3 G] :
    Module.finrank (ZMod 3) (H2Fp 3 G) ≤ Module.finrank (ZMod 3) (H1Fp 3 G) + 2 :=
  finrank_H2Fp_le_H1Fp_add_two_of_rank_delta K G
    (units_rank_eq_two_of_totallyReal_cubic K hdeg)
    (deltaK_eq_zero_of_totallyReal K 3 (by norm_num) (by norm_num))

/-- **The finite-quotient form** for a totally real cubic field and `p = 3`: for `N` the normal
closure of `k` elements of the maximal unramified pro-`3` group `G`, whose killing does not change
the generator rank,
`dim_{𝔽₃} H²(G ⧸ N, 𝔽₃) ≤ dim_{𝔽₃} H¹(G ⧸ N, 𝔽₃) + 2 + k`. -/
theorem finrank_H2Fp_quotient_le_two (K : Type*) [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (hdeg : Module.finrank ℚ K = 3)
    (G : Type) [Group G] [h : UnramifiedShafarevich K 3 G] (hk : KochTransfer 3 G)
    (k : ℕ) (g : Fin k → G)
    (hgen : Module.finrank (ZMod 3) (H1Fp 3 (G ⧸ Subgroup.normalClosure (Set.range g))) =
      Module.finrank (ZMod 3) (H1Fp 3 G)) :
    Module.finrank (ZMod 3) (H2Fp 3 (G ⧸ Subgroup.normalClosure (Set.range g))) ≤
      Module.finrank (ZMod 3) (H1Fp 3 (G ⧸ Subgroup.normalClosure (Set.range g))) + 2 + k :=
  finrank_H2Fp_quotient_le_two_of_rank_delta K G hk k g hgen
    (units_rank_eq_two_of_totallyReal_cubic K hdeg)
    (deltaK_eq_zero_of_totallyReal K 3 (by norm_num) (by norm_num))

/-- The finite-quotient form of Shafarevich's estimate, with the Frattini (tower-cutting)
hypothesis discharged: for a finite `3`-group `G` and elements `g i ∈ Φ(G)`,
`dim_{𝔽₃} H²(G ⧸ N, 𝔽₃) ≤ dim_{𝔽₃} H¹(G ⧸ N, 𝔽₃) + 2 + k`. -/
theorem finrank_H2Fp_quotient_le_two_of_frattini (K : Type*) [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (hdeg : Module.finrank ℚ K = 3)
    (G : Type) [Group G] [Finite G] [h : UnramifiedShafarevich K 3 G] (hk : KochTransfer 3 G)
    (hG : IsPGroup 3 G) (k : ℕ) (g : Fin k → G) (hg : ∀ i, g i ∈ frattini G) :
    Module.finrank (ZMod 3) (H2Fp 3 (G ⧸ Subgroup.normalClosure (Set.range g))) ≤
      Module.finrank (ZMod 3) (H1Fp 3 (G ⧸ Subgroup.normalClosure (Set.range g))) + 2 + k :=
  finrank_H2Fp_quotient_le_two K hdeg G hk k g
    (finrank_H1Fp_quotient_frattini hG k g hg)

end Work.CFT.Kummer
