import Mathlib
import Submission.Work.WingbergH3.Defs
import Submission.Work.WingbergH3.genRankTwo_eq_of_card
import Submission.Work.WingbergH3.relRankTwo_eq_of_card

/-!
# `Work.WingbergH3.Deficiency` -- the deficiency form of the wall

The literature states the relation count in the *deficiency* form used by
Hajir--Maire--Ramakrishna (arXiv:2103.09508, Notations: `df(Γ) = d₂(Γ) − d₁(Γ)`):

```
df(G_∅) = d₂(G_∅) − d₁(G_∅) ≤ d₂(O_F^×) ,
```

equivalently Shafarevich's `d₂(G_∅) ≤ d₁(G_∅) + d₂(O_F^×)`
(`Work.WingbergRoute.ShafarevichBound`), the two shapes coinciding because
`(r₁ + r₂ − 1) + 1 = r₁ + r₂ = d₂(O_F^×)` (`Work.WingbergRoute.unitTwoRank_eq_unitsRank_add_one`).

This module records the deficiency form with the two ranks of `Defs.lean`, so that a caller can use
either normalisation of the wall.

## Main declarations

* `Work.WingbergH3.deficiencyTwo_eq_sub_of_card`;
* `Work.WingbergH3.deficiencyTwo_le_iff_card`;
* `Work.WingbergH3.deficiency_le_unitTwoRank_iff_shafarevichBound`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open scoped Classical

noncomputable section

namespace Work.WingbergH3

open Work.ConCohomology Work.ClassFieldTower

/-- **The deficiency in terms of the two exponents**: if `#H²(Γ,𝔽₂) = 2 ^ k` and
`#H¹(Γ,𝔽₂) = 2 ^ d` then `df(Γ) = k − d`. -/
theorem deficiencyTwo_eq_sub_of_card {Γ : Type*} [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] {k d : ℕ}
    (hk : Nat.card (Work.RelatorRank.contH2 Γ) = 2 ^ k)
    (hd : Nat.card (H1 Γ (ZMod 2)) = 2 ^ d) :
    deficiencyTwo Γ = (k : ℤ) - (d : ℤ) := by
  rw [deficiencyTwo, relRankTwo_eq_of_card hk, genRankTwo_eq_of_card hd]

/-- **The deficiency bound in the exponent form**: `df(Γ) ≤ u` is exactly `k ≤ d + u` for the
exponents of `#H²` and `#H¹`. -/
theorem deficiencyTwo_le_iff_card {Γ : Type*} [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] {k d u : ℕ}
    (hk : Nat.card (Work.RelatorRank.contH2 Γ) = 2 ^ k)
    (hd : Nat.card (H1 Γ (ZMod 2)) = 2 ^ d) :
    deficiencyTwo Γ ≤ (u : ℤ) ↔ k ≤ d + u := by
  rw [deficiencyTwo_eq_sub_of_card hk hd]
  omega

/-- **The wall in its two normalisations.**  For a maximal unramified pro-`2` extension `M` of `F`
whose generator and relation ranks are exhibited as powers of two, the deficiency form
`df(G_∅) ≤ d₂(O_F^×)` is *the same inequality* as
`Work.WingbergRoute.ShafarevichBound F M`, i.e. `dim H² ≤ dim H¹ + d₂(O_F^×)`. -/
theorem deficiency_le_unitTwoRank_iff_shafarevichBound (F : Type) [Field F] [NumberField F]
    (M : MaximalUnramifiedProP.{0} F 2) {k d : ℕ}
    (hk : Nat.card (Work.RelatorRank.contH2 (galoisGroup M)) = 2 ^ k)
    (hd : Nat.card (H1 (galoisGroup M) (ZMod 2)) = 2 ^ d) :
    deficiencyTwo (galoisGroup M) ≤ (unitTwoRank F : ℤ) ↔ k ≤ d + unitTwoRank F :=
  deficiencyTwo_le_iff_card hk hd

end Work.WingbergH3
