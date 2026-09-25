import Mathlib
import Submission.Work.WingbergRoute.Main
import Submission.NumberField.GolodShafarevichArithmetic
import Submission.Work.WingbergRoute.six_le_card_of_surjective_elementaryAbelian

/-!
# `Work.WingbergRoute.TotallyReal` -- the totally real instance: the benchmark itself

This module is the part of the unramified (Wingberg) route that reaches
`Submission.exists_totallyReal_discr_le` **unconditionally** (given the classical arithmetic
input).  The base field is the **totally real** quadratic field
`F = gsF = ℚ(√2576450045)`, `2576450045 = 5·13·17·29·37·41·53`, of
`Submission/Work/QuadraticFields/`, whose multiquadratic extension

```
gsM = ℚ(√5, √13, √17, √29, √37, √41, √53)
```

is unramified over `gsF` of degree `2^6 = 64`
(`Work.QuadraticFields.gs_certificate`, `...gs_unramified_at_infinite_places`).

**Why this instance is the one that works.**  Over a *totally real* base an extension which is
unramified at the finite primes **and at the infinite places** has all its levels totally real
(`Commons.NumberTheory.NumberField.isTotallyReal_of_isUnramifiedAtInfinitePlaces`), and every level
`L` has `rootDiscr L = rootDiscr F`.  So the Golod--Shafarevich theorem produces Martinet's family
of totally real fields with bounded root discriminant — this is
`Submission.NumberField.exists_totallyReal_discr_le_of_unbounded_unramified_pro2`.  Over the
*imaginary* quadratic `Kc` the same input produces only the weak wall
`Submission.NumberField.BoundedRdTowerWall`, because the levels of the tower over `Kc` are not
totally real (`Submission/Work/HilbertTowerCM/`, §3--§5).

**The numbers.**  With `d = d(G_∅) ≥ 6` (the degree-`2^6` unramified multiquadratic extension
exhibits six independent unramified quadratics) and Wingberg's / Shafarevich's relation-rank bound
`r(G_∅) ≤ d + d₂(O_gsF^×) = d + 2` we get `r ≤ d + 2` and hence

```
4 r ≤ 4 (d + 2) ≤ d²  for d ≥ 6 ,
```

which is the hypothesis of the finite `p`-group Golod--Shafarevich inequality — with the strict
inequality `4r > d²` for finite `2`-groups this forces `G_∅` to be infinite.

## Main declarations

* `Work.WingbergRoute.unitTwoRank_gsF` : `d₂(O_gsF^×) = 2`;
* `Work.WingbergRoute.four_mul_le_sq_of_le_add_two`;
* `Work.WingbergRoute.gsFArithmeticInput_of_data` : the two numerical clauses (`6 ≤ #α` and
  `#rel ≤ #α + 2`) and the structural clauses give `gsFArithmeticInput`;
* `Work.WingbergRoute.golodShafarevichArithmeticInput_of_gsF` : `gsFArithmeticInput` implies the
  workspace's `Submission.NumberField.GolodShafarevichArithmeticInput`;
* **`Work.WingbergRoute.exists_totallyReal_discr_le_of_gsFArithmeticInput`** -- the benchmark;
* `Work.WingbergRoute.contH2DimLe_of_gsFWingbergWall` : the Wall gives the cohomological relation
  bound `dim H² ≤ d + 2`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open scoped Classical
open scoped NumberField
open NumberField
open Work.ConCohomology

noncomputable section

namespace Work.WingbergRoute

/-! ## The numbers at `gsF` -/

/-- **`d₂(O_gsF^×) = 2`**: `gsF = ℚ(√2576450045)` is a real quadratic field, so it has two real
places and no complex ones, and `d₂(O_F^×) = r₁ + r₂ = 2`. -/
theorem unitTwoRank_gsF : Work.ClassFieldTower.unitTwoRank gsF = 2 := by
  haveI : NumberField.IsTotallyReal gsF := Work.QuadraticFields.gsF_isTotallyReal
  have hnr : NumberField.InfinitePlace.nrRealPlaces gsF = Module.finrank ℚ gsF :=
    (NumberField.IsTotallyReal.finrank gsF).symm
  rw [Work.ClassFieldTower.unitTwoRank_eq_card_infinitePlace,
    NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    NumberField.IsTotallyReal.nrComplexPlaces_eq_zero, add_zero, hnr,
    Work.QuadraticFields.gsF_finrank]

/-- **The Golod--Shafarevich numerical bookkeeping**: `r ≤ d + 2` and `d ≥ 6` give `4r ≤ d²`. -/
theorem four_mul_le_sq_of_le_add_two {d r : ℕ} (hd : 6 ≤ d) (hr : r ≤ d + 2) :
    4 * r ≤ d * d := by
  have h1 : 4 * (d + 2) ≤ d * d := by
    nlinarith [sq_nonneg ((d : ℤ) - 6)]
  calc 4 * r ≤ 4 * (d + 2) := Nat.mul_le_mul_left 4 hr
    _ ≤ d * d := h1

/-- The same bookkeeping stated with `unitTwoRank gsF = 2`. -/
theorem four_mul_le_sq_of_le_add_unitTwoRank {d r : ℕ} (hd : 6 ≤ d)
    (hr : r ≤ d + Work.ClassFieldTower.unitTwoRank gsF) : 4 * r ≤ d * d := by
  have := unitTwoRank_gsF
  exact four_mul_le_sq_of_le_add_two hd (by omega)

/-! ## The arithmetic input -/

/-- **`gsFArithmeticInput` implies the workspace's `GolodShafarevichArithmeticInput`.**  The
passage adds the two clauses the workspace's global input derives internally: `4r ≤ d²` (from
`d ≥ 6` and `r ≤ d + 2`) and `0 < d`.  The generator-rank clause `6 ≤ #α` is the genus-theoretic
input: its provenance is `Work.WingbergRoute.Certificate`. -/
theorem golodShafarevichArithmeticInput_of_gsF (h : gsFArithmeticInput) :
    Submission.NumberField.GolodShafarevichArithmeticInput := by
  classical
  unfold gsFArithmeticInput at h
  obtain ⟨α, iα, iD, rel, h6, hrel, hmin, hres, hquot2, hreal⟩ := h
  refine ⟨gsF, inferInstance, inferInstance, Work.QuadraticFields.gsF_isTotallyReal,
    α, iα, iD, rel, ?_, ?_, hmin, hres, hquot2, hreal⟩
  · exact Nat.lt_of_lt_of_le (by norm_num) h6
  · exact four_mul_le_sq_of_le_add_unitTwoRank h6 hrel

/-- **THE BENCHMARK from the totally real unramified input at `gsF`.** -/
theorem exists_totallyReal_discr_le_of_gsFArithmeticInput (h : gsFArithmeticInput) :
    Work.CMRealSubfield.Benchmark :=
  Submission.NumberField.exists_totallyReal_discr_le_of_golodShafarevichArithmetic
    (Submission.GroupTheory.finitePGroupGolodShafarevich_of_commons 2)
    (golodShafarevichArithmeticInput_of_gsF h)

/-! ## The Wall in the totally real instance -/

/-- **The Wall gives the cohomological relation bound for the totally real base.**  From
`ShafarevichBound gsF M` (`dim H² ≤ dim H¹ + d₂(O_gsF^×) = d + 2`) the relation rank of `G_∅` is
at most `d + 2`. -/
theorem contH2DimLe_of_shafarevichBound_gsF
    (M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} gsF 2)
    (h : ShafarevichBound gsF M) :
    ∃ d : ℕ, Nat.card (H1 (Work.ClassFieldTower.galoisGroup M) (ZMod 2)) = 2 ^ d ∧
      Work.RelatorRank.ContH2DimLe (Work.ClassFieldTower.galoisGroup M) (d + 2) := by
  obtain ⟨k, d, hk, hd, hbd⟩ := h
  have hu : Work.ClassFieldTower.unitTwoRank gsF = 2 := unitTwoRank_gsF
  exact ⟨d, hd, ⟨k, by omega, hk⟩⟩

/-- **The benchmark (in the target's own spelling) from the totally real unramified input.** -/
theorem exists_totallyReal_discr_le_spelled_of_gsFArithmeticInput
    (h : gsFArithmeticInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∃ d : ℕ, N ≤ d ∧
      ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : NumberField.IsTotallyReal K),
        Module.finrank ℚ K = d ∧ |(NumberField.discr K : ℝ)| ≤ C ^ d :=
  exists_totallyReal_discr_le_of_gsFArithmeticInput h

/-- **The totally real Wall in the deficiency form**: `dim H² ≤ dim H¹ + 2`. -/
theorem gsFWingbergWall_iff :
    gsFWingbergWall ↔
      ∃ M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} gsF 2, ∃ d : ℕ,
        Nat.card (H1 (Work.ClassFieldTower.galoisGroup M) (ZMod 2)) = 2 ^ d ∧
        Work.RelatorRank.ContH2DimLe (Work.ClassFieldTower.galoisGroup M) (d + 2) := by
  constructor
  · rintro ⟨M, hM⟩
    obtain ⟨d, hd, hcont⟩ := (shafarevichBound_iff gsF M).mp hM
    have hu : Work.ClassFieldTower.unitTwoRank gsF = 2 := unitTwoRank_gsF
    exact ⟨M, d, hd, hcont.mono (by omega)⟩
  · rintro ⟨M, d, hd, hcont⟩
    refine ⟨M, (shafarevichBound_iff gsF M).mpr ⟨d, hd, ?_⟩⟩
    have hu : Work.ClassFieldTower.unitTwoRank gsF = 2 := unitTwoRank_gsF
    exact hcont.mono (by omega)

/-- **The presentation step at `gsF`**: the totally real Wall and Gaschütz give a pro-`2`
presentation of `G_∅` with `d` generators and `d + 2` relators, where `#H¹(G_∅,𝔽₂) = 2^d`. -/
theorem hasProP2Presentation_gsF_of_wall
    (M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} gsF 2)
    (hdict : Work.RelatorRank.GaschutzCohomologicalValue (Work.ClassFieldTower.galoisGroup M))
    (h : ShafarevichBound gsF M) :
    ∃ d : ℕ, Nat.card (H1 (Work.ClassFieldTower.galoisGroup M) (ZMod 2)) = 2 ^ d ∧
      Work.RelatorRank.HasProP2Presentation (Work.ClassFieldTower.galoisGroup M)
        (Work.RelatorRank.GeneratorRank (Work.ClassFieldTower.galoisGroup M)) (d + 2) := by
  obtain ⟨d, hd, hpres⟩ := hasProP2Presentation_of_shafarevichBound gsF M hdict h
  have hu : Work.ClassFieldTower.unitTwoRank gsF = 2 := unitTwoRank_gsF
  rw [hu] at hpres
  exact ⟨d, hd, hpres⟩

/-- **The Golod--Shafarevich inequality from the totally real Wall**: with the genus certificate
`6 ≤ d` and the relation count `r ≤ d + 2`, one has `4r ≤ d²`. -/
theorem four_mul_rel_le_sq_of_wall
    {d r : ℕ} (hd : 6 ≤ d) (hr : r ≤ d + Work.ClassFieldTower.unitTwoRank gsF) :
    4 * r ≤ d * d :=
  four_mul_le_sq_of_le_add_unitTwoRank hd hr

end Work.WingbergRoute
