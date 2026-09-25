import Mathlib
import Submission.Work.CFT.ShafarevichCore.Defs
import Submission.Work.CFT.Kummer.All

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

set_option warn.classDefReducibility false

/-!
# The reduction of Shafarevich's estimate to the two core facts

This file proves, sorry-free, everything between Koch's two arithmetic facts
(`Work.CFT.ShafarevichCore.ShafarevichInjection`, `...ClassRankFormula`) and the relation-rank
estimate `dim H²(G,𝔽_p) ≤ dim H¹(G,𝔽_p) + (r₁+r₂-1) + δ_{F,p}` for the maximal
everywhere-unramified pro-`p` group `G` of `F`.

The only arithmetic input is the *proved* Kummer computation
`Work.CFT.Kummer.finrank_kummerDual_empty`,
`dim 𝓒_∅ = dim Cl_F[p] + (r₁+r₂-1) + δ_{F,p}`; from it, fact (a) bounds `dim H²` by `dim 𝓒_∅` and
fact (b′) turns `dim Cl_F[p]` into `dim H¹`.

## Main results

* `Work.CFT.ShafarevichCore.finrank_H2Fp_le_kummerDual` — fact (a) alone:
  `dim H²(G,𝔽_p) ≤ dim 𝓒_∅`.
* `Work.CFT.ShafarevichCore.classRank_iff_kummerRank` — **(b) ⟺ (b′)**: Koch's H¹ rank formula (b)
  is *equivalent* to the class-group rank formula (b′), given the Kummer computation.  Hence the
  rank formula is not an extra input.
* `Work.CFT.ShafarevichCore.finrank_H2Fp_le_H1Fp_add` — **Shafarevich's estimate** from the two
  core facts.
* `Work.CFT.ShafarevichCore.unramifiedShafarevich_of_coreFacts` and
  `..._of_unramifiedShafarevich` — the equivalence of `CoreFacts` with the Kummer area's class
  `Work.CFT.Kummer.UnramifiedShafarevichClassGroup` / `UnramifiedShafarevich`.
-/

open NumberField
open scoped Classical nonZeroDivisors

noncomputable section

set_option warn.classDefReducibility false in
attribute [local instance] Classical.propDecidable

namespace Work.CFT.ShafarevichCore

variable (F : Type*) [Field F] [NumberField F] (p : ℕ) [Fact p.Prime] (G : Type) [Group G]

/-- `CoreFacts` is the conjunction of the two isolated facts. -/
theorem coreFacts_iff :
    CoreFacts F p G ↔ ShafarevichInjection F p G ∧ ClassRankFormula F p G := Iff.rfl

/-- **Fact (a) alone**: the Shafarevich injection bounds the second cohomology by the Kummer
character group, `dim_{𝔽_p} H²(G,𝔽_p) ≤ dim_{𝔽_p} 𝓒_∅`. -/
theorem finrank_H2Fp_le_kummerDual (h : ShafarevichInjection F p G) :
    Module.finrank (ZMod p) (H2Fp p G) ≤ Module.finrank (ZMod p) (kummerDual F p ∅) := by
  obtain ⟨sha, hsha⟩ := h
  haveI := Work.CFT.Kummer.finite_kummerDual F p ∅
  exact LinearMap.finrank_le_finrank_of_injective hsha

/-- **Koch's H¹ rank formula (b) is equivalent to the class-group rank formula (b′).**  From the
*proved* Kummer computation `dim 𝓒_∅ = dim Cl_F[p] + (r₁+r₂-1) + δ_{F,p}`
(`Work.CFT.Kummer.finrank_kummerDual_empty`), the equality `dim 𝓒_∅ = dim H¹ + (r₁+r₂-1) + δ`
is equivalent to `dim H¹ = dim Cl_F[p]`.  Thus the Kummer area's H¹ rank formula is not an
independent arithmetic input beyond (b′). -/
theorem classRank_iff_kummerRank :
    ClassRankFormula F p G ↔ KummerRankFormula F p G := by
  have hK : Module.finrank (ZMod p) (kummerDual F p ∅) =
      Module.finrank (ZMod p) (classGroupTorsion F p) + NumberField.Units.rank F +
        Work.CFT.Kummer.deltaK F p := Work.CFT.Kummer.finrank_kummerDual_empty F p
  unfold ClassRankFormula KummerRankFormula
  constructor <;> intro h <;> omega

/-- The Kummer rank formula (b) is exactly the `rank_formula` field of the Kummer area's class
`Work.CFT.Kummer.UnramifiedShafarevich`. -/
theorem kummerRank_iff_unramifiedShafarevichRank
    [h : Work.CFT.Kummer.UnramifiedShafarevich F p G] :
    KummerRankFormula F p G := h.rank_formula

/-- **Shafarevich's relation-rank estimate** from the two core facts: for the maximal
everywhere-unramified pro-`p` group `G` of `F`,

`dim_{𝔽_p} H²(G,𝔽_p) ≤ dim_{𝔽_p} H¹(G,𝔽_p) + (r₁+r₂-1) + δ_{F,p}`. -/
theorem finrank_H2Fp_le_H1Fp_add (h : CoreFacts F p G) :
    Module.finrank (ZMod p) (H2Fp p G) ≤
      Module.finrank (ZMod p) (H1Fp p G) + NumberField.Units.rank F +
        Work.CFT.Kummer.deltaK F p := by
  have ha : Module.finrank (ZMod p) (H2Fp p G) ≤
      Module.finrank (ZMod p) (Work.CFT.Kummer.kummerDual F p ∅) :=
    finrank_H2Fp_le_kummerDual F p G h.injection
  have hb : Module.finrank (ZMod p) (H1Fp p G) =
      Module.finrank (ZMod p) (Work.CFT.Kummer.classGroupTorsion F p) := h.classRank
  have hK := Work.CFT.Kummer.finrank_kummerDual_empty F p
  omega

/-- **`CoreFacts` implies the Kummer area's class `UnramifiedShafarevichClassGroup`** (the class
whose two fields are exactly (a) and (b′)), given the finiteness of `H²(G,𝔽_p)`. -/
noncomputable def unramifiedShafarevichClassGroup_of_coreFacts (h : CoreFacts F p G)
    (hfin : Module.Finite (ZMod p) (H2Fp p G)) :
    Work.CFT.Kummer.UnramifiedShafarevichClassGroup F p G where
  finite_H2 := hfin
  finite_dual := Work.CFT.Kummer.finite_kummerDual F p ∅
  sha := Classical.choose h.injection
  sha_injective := Classical.choose_spec h.injection
  h1_eq_classGroupRank := h.classRank

/-- **The Kummer area's `UnramifiedShafarevichClassGroup` implies `CoreFacts`**: the vocabulary of
this area is exactly the (a) + (b′) factorization of that class. -/
theorem coreFacts_of_unramifiedShafarevichClassGroup
    [h : Work.CFT.Kummer.UnramifiedShafarevichClassGroup F p G] : CoreFacts F p G :=
  ⟨⟨h.sha, h.sha_injective⟩, h.h1_eq_classGroupRank⟩

/-- **`CoreFacts` implies the Kummer area's `UnramifiedShafarevich`** (facts (a) and (b)), given
the finiteness of `H²(G,𝔽_p)`. -/
noncomputable def unramifiedShafarevich_of_coreFacts (h : CoreFacts F p G)
    (hfin : Module.Finite (ZMod p) (H2Fp p G)) :
    Work.CFT.Kummer.UnramifiedShafarevich F p G where
  finite_H2 := hfin
  finite_dual := Work.CFT.Kummer.finite_kummerDual F p ∅
  sha := Classical.choose h.injection
  sha_injective := Classical.choose_spec h.injection
  rank_formula := (classRank_iff_kummerRank F p G).mp h.classRank

/-- **The Kummer area's `UnramifiedShafarevich` implies `CoreFacts`** — using the (proved) Kummer
computation to recover (b′) from the H¹ rank formula (b). -/
theorem coreFacts_of_unramifiedShafarevich [h : Work.CFT.Kummer.UnramifiedShafarevich F p G] :
    CoreFacts F p G :=
  ⟨⟨h.sha, h.sha_injective⟩, (classRank_iff_kummerRank F p G).mpr h.rank_formula⟩

/-- **The estimate in the shape used by the tower** for a totally real cubic field and `p = 3`:
`dim_{𝔽₃} H²(G,𝔽₃) ≤ dim_{𝔽₃} H¹(G,𝔽₃) + 2`. -/
theorem finrank_H2Fp_le_H1Fp_add_two_of_coreFacts [NumberField.IsTotallyReal F]
    (hdeg : Module.finrank ℚ F = 3) (h : CoreFacts F 3 G) :
    Module.finrank (ZMod 3) (H2Fp 3 G) ≤ Module.finrank (ZMod 3) (H1Fp 3 G) + 2 := by
  have h1 := finrank_H2Fp_le_H1Fp_add F 3 G h
  rw [Work.CFT.Kummer.units_rank_eq_two_of_totallyReal_cubic F hdeg,
    Work.CFT.Kummer.deltaK_eq_zero_of_totallyReal F 3 (by norm_num) (by norm_num)] at h1
  simpa using h1

end Work.CFT.ShafarevichCore
