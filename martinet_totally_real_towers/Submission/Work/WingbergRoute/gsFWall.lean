import Mathlib
import Submission.Work.WingbergRoute.TotallyReal
import Submission.Work.WingbergRoute.natCard_H2Z_quot_two_le_card_H1_zmodTwo_gsF
import Submission.Work.WingbergRoute.gsFWingbergWall_of_deficiencyInput

/-!
# `Work.WingbergRoute.gsFWall` -- the totally real wall in the classical *deficiency* form

For the benchmark-reaching base `gsF = ℚ(√2576450045)` this module records the area's input in the
form in which the literature states it: the deficiency `df = r − d` of the maximal unramified pro-`2`
group is bounded by the `2`-rank of the units,

```
df(G_∅) = dim_{𝔽₂} H³(G_∅,ℤ)[2]  ≤  d₂(O_gsF^×) = r₁ + r₂ = 2       (Wingberg),
```

i.e. `#H³(G_∅,ℤ)[2] ≤ 2^{unitTwoRank gsF}`.  Wingberg's theorem gives `df ≤ 1` (the roots of unity
are universal norms), so the input below has a factor of two of slack.

The *elementary* half of the count is **proved** in this area: the coefficient-sequence identity

```
#H²(G_∅,𝔽₂) = #(H²(G_∅,ℤ)/2H²(G_∅,ℤ)) · #H³(G_∅,ℤ)[2]      (Work.ShafarevichKoch.CountZ)
```

together with the unconditional bound

```
#(H²(G_∅,ℤ)/2H²(G_∅,ℤ)) ≤ #H¹(G_∅,𝔽₂)   (natCard_H2Z_quot_two_le_card_H1_zmodTwo_gsF, this area)
```

(which needs no class field theory: it is `H²(G,ℤ) ≅ H¹(G,ℚ/ℤ)`, the pure algebra
`#(A/2A) ≤ #A[2]` for `2`-primary torsion and the Bockstein surjection `H¹(G,𝔽₂) ↠ H²(G,ℤ)[2]`).
So only the `H³`-half -- Wingberg's duality in degree `0` -- remains, exactly as for `Kc`.

## Main declarations

* `Work.WingbergRoute.gsFDeficiencyWall` (the input, in the deficiency form);
* `Work.WingbergRoute.gsFWingbergWall_of_gsFDeficiencyWall`;
* `Work.WingbergRoute.exists_hasProP2Presentation_gsF_of_gsFDeficiencyWall` (the presentation step,
  given Gaschütz's value theorem).
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

open scoped Classical

noncomputable section

namespace Work.WingbergRoute

open Work.ConCohomology Work.ShafarevichKoch Work.ClassFieldTower

/-- **The wall for `gsF` in the classical deficiency form**: for some maximal unramified pro-`2`
extension `M` of `gsF`, the groups `H²(G_∅,ℤ)`, `H³(G_∅,ℤ)` are finite, the generator rank
`#H¹(G_∅,𝔽₂) = 2^d` is finite, and the deficiency is at most the `2`-rank of the units:
`#H³(G_∅,ℤ)[2] ≤ 2 ^ unitTwoRank gsF = 4`.  By Wingberg's duality the true bound is `≤ 2`. -/
def gsFDeficiencyWall : Prop :=
  ∃ M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} gsF 2,
    Finite (Work.ConCohomology.H2 (Work.ClassFieldTower.galoisGroup M) ℤ) ∧
      Finite (Work.ShafarevichKoch.H3 (Work.ClassFieldTower.galoisGroup M) ℤ) ∧
        (∃ d : ℕ,
          Nat.card (Work.ConCohomology.H1 (Work.ClassFieldTower.galoisGroup M) (ZMod 2)) = 2 ^ d) ∧
          Nat.card (Work.ShafarevichKoch.twoTorsionH3 (Work.ClassFieldTower.galoisGroup M)) ≤
            2 ^ Work.ClassFieldTower.unitTwoRank gsF

/-- **The deficiency wall gives `gsFWingbergWall`** (item (2) of the deliverable in the literature's
own shape). -/
theorem gsFWingbergWall_of_gsFDeficiencyWall (h : gsFDeficiencyWall) : gsFWingbergWall :=
  gsFWingbergWall_of_deficiencyInput h

/-- **The presentation step at `gsF` from the deficiency wall**: with Gaschütz's value theorem, some
maximal unramified pro-`2` extension of `gsF` has a pro-`2` presentation on `GeneratorRank`
generators and `d + 2` relators, where `#H¹(G_∅,𝔽₂) = 2^d`. -/
theorem exists_hasProP2Presentation_gsF_of_gsFDeficiencyWall
    (hdict : ∀ M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} gsF 2,
      Work.RelatorRank.GaschutzCohomologicalValue (Work.ClassFieldTower.galoisGroup M))
    (h : gsFDeficiencyWall) :
    ∃ M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} gsF 2, ∃ d : ℕ,
      Nat.card (Work.ConCohomology.H1 (Work.ClassFieldTower.galoisGroup M) (ZMod 2)) = 2 ^ d ∧
        Work.RelatorRank.HasProP2Presentation (Work.ClassFieldTower.galoisGroup M)
          (Work.RelatorRank.GeneratorRank (Work.ClassFieldTower.galoisGroup M)) (d + 2) := by
  obtain ⟨M, hM⟩ := gsFWingbergWall_of_gsFDeficiencyWall h
  exact ⟨M, hasProP2Presentation_gsF_of_wall M (hdict M) hM⟩

end Work.WingbergRoute
