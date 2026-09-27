import Mathlib
import Submission.Work.Drive.cutDichotomy
import Submission.Work.Drive.rotSweepEquivariance
import Submission.Work.Drive.bottomBdryMeet_clampedSweep_count

/-!
# The side value of a rotation, and the `top₀` clause of the multiplicativity

`Work.Drive.Capping.odd_ncard_topBdryMeet_zero_iff_nonempty_of_dichotomy`
(`Submission/Work/Drive/cutDichotomy.lean`) computes the `0`-th top count of the triple of radial
sweeps of three plane presentations:

> `Odd n_{P_0} ↔` the cut of the chart `Q` by the first sweep is non-empty `∧` the cut by the second
> sweep is non-empty.

The side function of the order route is, by definition, the *non-emptiness of the cut*

> `e u = 1 ⟺ the cut of the base plane `P₀` by the sweep of the rotated plane `u·P₀` is non-empty`,

and the `top₀` clause of `Work.Drive.ChainFunctional` reads `Odd n_{P_0} ↔ e a · e (a+c) = 1`.

This file does that wiring, and — this is the point — shows that the side value is a function of the
**angle** and not of the block: the design truncates the three sweeps of one triple at *pairwise
distinct* levels (`c 0 > c 1 > c 2`, `Submission/Work/Drive/END_LEVEL_OBSTRUCTION.md` §1), so a
definition of `e u` at a *single* block would be meaningless unless the cut is independent of the
truncation.  It is:

> **`Work.Drive.diskCut_clampedSweep_irrel`** — the cut of a clamped sweep does not depend on the
> truncation level, nor on the cutoff, provided both floors are below the levels of the chart on the
> disk and of the swept plane on its box.

All declarations are sorry-free and rest only on `propext`, `Classical.choice` and `Quot.sound`.
-/

namespace Work.Drive

open scoped Topology Manifold ContDiff
open Set

noncomputable section

/-- **The cut of a clamped sweep is independent of its truncation level and of its cutoff.**  The
exact image description `Work.Drive.diskCut_clampedSweep_eq` writes the cut as

> `{x : ‖x‖ ≤ 1 and the class of `Q x` is the class of some box point `y` of `P` and
>   `c ≤ levelOf (Q x) ≤ levelOf (P y)`}`,

so once the truncation floor `c` is below the chart's levels on the disk, the lower bound is vacuous
and only the *upper* bound (the swept plane's profile) remains — which is independent of both `c` and
the cutoff `ψ` (the cutoff only changes the parametrisation of the sweep, not its image). -/
theorem diskCut_clampedSweep_irrel (Q : ℂ → CappingSpace) (c c' : ℝ) (hc : 0 < c) (hc' : 0 < c')
    (ψ ψ' : ℝ → ℝ)
    (hψ0 : ψ 0 = 1) (hψ1 : ψ 1 = 0)
    (hψ01 : ∀ t ∈ Set.Icc (0 : ℝ) 1, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hcont : ContinuousOn ψ (Set.Icc (0 : ℝ) 1))
    (hψ0' : ψ' 0 = 1) (hψ1' : ψ' 1 = 0)
    (hψ01' : ∀ t ∈ Set.Icc (0 : ℝ) 1, ψ' t ∈ Set.Icc (0 : ℝ) 1)
    (hcont' : ContinuousOn ψ' (Set.Icc (0 : ℝ) 1))
    (P : EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (hr : ∀ y ∈ Submission.Drive.unitBox 1, c ≤ levelOf (P y))
    (hr' : ∀ y ∈ Submission.Drive.unitBox 1, c' ≤ levelOf (P y))
    (hclow : ∀ x : EuclideanSpace ℝ (Fin 2), ‖cplxOf x‖ ≤ 1 → c ≤ levelOf (Q (cplxOf x)))
    (hclow' : ∀ x : EuclideanSpace ℝ (Fin 2), ‖cplxOf x‖ ≤ 1 → c' ≤ levelOf (Q (cplxOf x))) :
    diskCut Q (clampedSweep c ψ P) = diskCut Q (clampedSweep c' ψ' P) := by
  rw [diskCut_clampedSweep_eq Q c hc ψ hψ0 hψ1 hψ01 hcont P hr,
    diskCut_clampedSweep_eq Q c' hc' ψ' hψ0' hψ1' hψ01' hcont' P hr']
  ext x
  constructor
  · rintro ⟨h1, y, hy, hcls, -, hle⟩
    exact ⟨h1, y, hy, hcls, hclow' x h1, hle⟩
  · rintro ⟨h1, y, hy, hcls, -, hle⟩
    exact ⟨h1, y, hy, hcls, hclow x h1, hle⟩

/-- **The `ZMod 2` side value of a set**: `1` when it is non-empty, `0` when it is empty.  Applied to
the cut of a plane by a sweep, this is the side function of the order route. -/
noncomputable def side (S : Set (EuclideanSpace ℝ (Fin 2))) : ZMod 2 :=
  if S = ∅ then 0 else 1

theorem side_eq_one_iff {S : Set (EuclideanSpace ℝ (Fin 2))} : side S = 1 ↔ S ≠ ∅ := by
  rw [side]
  by_cases h : S = ∅
  · rw [if_pos h]
    exact ⟨fun h1 => absurd h1 zero_ne_one, fun h2 => absurd h h2⟩
  · rw [if_neg h]
    exact ⟨fun _ => h, fun _ => rfl⟩

theorem side_eq_zero_iff {S : Set (EuclideanSpace ℝ (Fin 2))} : side S = 0 ↔ S = ∅ := by
  rw [side]
  by_cases h : S = ∅
  · rw [if_pos h]
    exact ⟨fun _ => h, fun _ => rfl⟩
  · rw [if_neg h]
    exact ⟨fun h1 => absurd h1 one_ne_zero, fun h2 => absurd h2 h⟩

private lemma zmod2_cases' (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- In `ZMod 2` a product is `1` exactly when both factors are `1` (there are no other units). -/
theorem zmod2_mul_eq_one_iff {a b : ZMod 2} : a * b = 1 ↔ a = 1 ∧ b = 1 := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩ <;> by_contra hc
    · rcases zmod2_cases' a with h0 | h1
      · rw [h0, zero_mul] at h; exact zero_ne_one h
      · exact absurd h1 hc
    · rcases zmod2_cases' b with h0 | h1
      · rw [h0, mul_zero] at h; exact zero_ne_one h
      · exact absurd h1 hc
  · rintro ⟨rfl, rfl⟩
    norm_num

/-- **THE `top₀` CLAUSE OF THE MULTIPLICATIVITY, in `ZMod 2` form.**  The `0`-th top count of the
triple of radial sweeps of three plane presentations whose first plane is the chart `Q` is odd exactly
when the product of the two *side values* is `1`, i.e. exactly when both cuts are non-empty.  This is
the shape of `Work.Drive.ChainFunctional.top₀`
(`Odd (topBdryMeet Y (D a c hac) 0).ncard ↔ e a * e ⟨a + c, hac⟩ = 1`). -/
theorem Capping.odd_ncard_topBdryMeet_zero_eq_side_mul
    (Q : ℂ → CappingSpace) (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (hQ : P 0 = diskPlane Q)
    (c : Fin 3 → ℝ) (ψ : ℝ → ℝ) (hψ : ψ 1 = 0)
    (hfibV : ∀ u ∈ cutBaseBox (P 0) (clampedSweep (c 1) ψ (P 1)) (clampedSweep (c 2) ψ (P 2)),
      (cutFibreBox (P 0) (clampedSweep (c 1) ψ (P 1)) u).ncard = 1)
    (hfibW : ∀ u ∈ cutBaseBox (P 0) (clampedSweep (c 1) ψ (P 1)) (clampedSweep (c 2) ψ (P 2)),
      (cutFibreBox (P 0) (clampedSweep (c 2) ψ (P 2)) u).ncard = 1)
    (A B : Fin 1 → ℝ → EuclideanSpace ℝ (Fin 2))
    (hV : diskCut Q (clampedSweep (c 1) ψ (P 1)) = arcCycle A ∨
      diskCut Q (clampedSweep (c 1) ψ (P 1)) = ∅)
    (hW : diskCut Q (clampedSweep (c 2) ψ (P 2)) = arcCycle B ∨
      diskCut Q (clampedSweep (c 2) ψ (P 2)) = ∅)
    (hchordA : ∀ i, IsChord (A i)) (hchordB : ∀ j, IsChord (B j))
    (hAinj : ∀ i, Set.InjOn (A i) (Set.Icc (0 : ℝ) 1))
    (hBinj : ∀ j, Set.InjOn (B j) (Set.Icc (0 : ℝ) 1))
    (hAdisj : ∀ i i' : Fin 1, i ≠ i' →
      Disjoint (A i '' Set.Icc (0 : ℝ) 1) (A i' '' Set.Icc (0 : ℝ) 1))
    (hBdisj : ∀ j j' : Fin 1, j ≠ j' →
      Disjoint (B j '' Set.Icc (0 : ℝ) 1) (B j' '' Set.Icc (0 : ℝ) 1))
    (hint : ∀ (i : Fin 1) (j : Fin 1) (t s : ℝ), t ∈ Set.Icc (0 : ℝ) 1 → s ∈ Set.Icc (0 : ℝ) 1 →
      A i t = B j s → t ∈ Set.Ioo (0 : ℝ) 1 ∧ s ∈ Set.Ioo (0 : ℝ) 1 ∧ ‖A i t‖ < 1)
    (hendsA : ∀ i k : Fin 1, A i 0 = A k 0 ∨ A i 0 = antipode (A k 0) → i = k)
    (hendsB : ∀ j l : Fin 1, B j 0 = B l 0 ∨ B j 0 = antipode (B l 0) → j = l)
    (htrans : ∀ (i : Fin 1) (j : Fin 1) (t s : ℝ), t ∈ Set.Ioo (0 : ℝ) 1 → s ∈ Set.Ioo (0 : ℝ) 1 →
      A i t = B j s → det2 (deriv (A i) t) (deriv (B j) s) ≠ 0) :
    Odd (topBdryMeet CappingSpace (fun k => clampedSweep (c k) ψ (P k)) 0).ncard ↔
      side (diskCut Q (clampedSweep (c 1) ψ (P 1))) *
        side (diskCut Q (clampedSweep (c 2) ψ (P 2))) = 1 := by
  rw [Capping.odd_ncard_topBdryMeet_zero_iff_nonempty_of_dichotomy Q P hQ c ψ hψ hfibV hfibW A B
    hV hW hchordA hchordB hAinj hBinj hAdisj hBdisj hint hendsA hendsB htrans,
    zmod2_mul_eq_one_iff, side_eq_one_iff, side_eq_one_iff]

/-- **The side value attached to a rotation**, from the design's angle-indexed family of plane
presentations: the non-emptiness of the cut of the base chart `Q` by the sweep of the plane presented
at the angle `u`, truncated at the level `c u` with the cutoff `ψ`.

By `Work.Drive.diskCut_clampedSweep_irrel` this value does not depend on the level `c u` (as long as it
lies below the levels of the chart on the disk and of the swept plane on its box), nor on `ψ` — which is
what makes it a function of the *angle* alone, as the order function of the route must be. -/
noncomputable def sideAt (Q : ℂ → CappingSpace)
    (P : UnitAddCircle → EuclideanSpace ℝ (Fin 2) → CappingSpace) (c : UnitAddCircle → ℝ)
    (ψ : ℝ → ℝ) (u : UnitAddCircle) : ZMod 2 :=
  side (diskCut Q (clampedSweep (c u) ψ (P u)))

theorem sideAt_apply (Q : ℂ → CappingSpace)
    (P : UnitAddCircle → EuclideanSpace ℝ (Fin 2) → CappingSpace) (c : UnitAddCircle → ℝ)
    (ψ : ℝ → ℝ) (u : UnitAddCircle) :
    sideAt Q P c ψ u = side (diskCut Q (clampedSweep (c u) ψ (P u))) := rfl

theorem sideAt_eq_one_iff {Q : ℂ → CappingSpace}
    {P : UnitAddCircle → EuclideanSpace ℝ (Fin 2) → CappingSpace} {c : UnitAddCircle → ℝ}
    {ψ : ℝ → ℝ} {u : UnitAddCircle} :
    sideAt Q P c ψ u = 1 ↔ diskCut Q (clampedSweep (c u) ψ (P u)) ≠ ∅ := by
  rw [sideAt_apply, side_eq_one_iff]

/-- **The `top₀` clause in the design's own angle-indexed form.**  The three chains of the block are
the sweeps of the planes presented at the three angles `u 0, u 1, u 2` (with `u 0 = 0`, i.e. the chart's
own plane — so `P (u 0) = diskPlane Q`), and the conclusion is `Odd n_{P_0} ↔ e (u 1) · e (u 2) = 1`
with `e := sideAt …`. -/
theorem Capping.odd_ncard_topBdryMeet_zero_eq_sideAt_mul
    (Q : ℂ → CappingSpace)
    (P : UnitAddCircle → EuclideanSpace ℝ (Fin 2) → CappingSpace) (c : UnitAddCircle → ℝ)
    (ψ : ℝ → ℝ) (hψ : ψ 1 = 0) (u : Fin 3 → UnitAddCircle)
    (hP0 : P (u 0) = diskPlane Q)
    (hfibV : ∀ y ∈ cutBaseBox (P (u 0)) (clampedSweep (c (u 1)) ψ (P (u 1)))
        (clampedSweep (c (u 2)) ψ (P (u 2))),
      (cutFibreBox (P (u 0)) (clampedSweep (c (u 1)) ψ (P (u 1))) y).ncard = 1)
    (hfibW : ∀ y ∈ cutBaseBox (P (u 0)) (clampedSweep (c (u 1)) ψ (P (u 1)))
        (clampedSweep (c (u 2)) ψ (P (u 2))),
      (cutFibreBox (P (u 0)) (clampedSweep (c (u 2)) ψ (P (u 2))) y).ncard = 1)
    (A B : Fin 1 → ℝ → EuclideanSpace ℝ (Fin 2))
    (hV : diskCut Q (clampedSweep (c (u 1)) ψ (P (u 1))) = arcCycle A ∨
      diskCut Q (clampedSweep (c (u 1)) ψ (P (u 1))) = ∅)
    (hW : diskCut Q (clampedSweep (c (u 2)) ψ (P (u 2))) = arcCycle B ∨
      diskCut Q (clampedSweep (c (u 2)) ψ (P (u 2))) = ∅)
    (hchordA : ∀ i, IsChord (A i)) (hchordB : ∀ j, IsChord (B j))
    (hAinj : ∀ i, Set.InjOn (A i) (Set.Icc (0 : ℝ) 1))
    (hBinj : ∀ j, Set.InjOn (B j) (Set.Icc (0 : ℝ) 1))
    (hAdisj : ∀ i i' : Fin 1, i ≠ i' →
      Disjoint (A i '' Set.Icc (0 : ℝ) 1) (A i' '' Set.Icc (0 : ℝ) 1))
    (hBdisj : ∀ j j' : Fin 1, j ≠ j' →
      Disjoint (B j '' Set.Icc (0 : ℝ) 1) (B j' '' Set.Icc (0 : ℝ) 1))
    (hint : ∀ (i : Fin 1) (j : Fin 1) (t s : ℝ), t ∈ Set.Icc (0 : ℝ) 1 → s ∈ Set.Icc (0 : ℝ) 1 →
      A i t = B j s → t ∈ Set.Ioo (0 : ℝ) 1 ∧ s ∈ Set.Ioo (0 : ℝ) 1 ∧ ‖A i t‖ < 1)
    (hendsA : ∀ i k : Fin 1, A i 0 = A k 0 ∨ A i 0 = antipode (A k 0) → i = k)
    (hendsB : ∀ j l : Fin 1, B j 0 = B l 0 ∨ B j 0 = antipode (B l 0) → j = l)
    (htrans : ∀ (i : Fin 1) (j : Fin 1) (t s : ℝ), t ∈ Set.Ioo (0 : ℝ) 1 → s ∈ Set.Ioo (0 : ℝ) 1 →
      A i t = B j s → det2 (deriv (A i) t) (deriv (B j) s) ≠ 0) :
    Odd (topBdryMeet CappingSpace (fun k => clampedSweep (c (u k)) ψ (P (u k))) 0).ncard ↔
      sideAt Q P c ψ (u 1) * sideAt Q P c ψ (u 2) = 1 := by
  rw [sideAt_apply, sideAt_apply]
  exact Capping.odd_ncard_topBdryMeet_zero_eq_side_mul Q (fun k => P (u k)) hP0
    (fun k => c (u k)) ψ hψ hfibV hfibW A B hV hW hchordA hchordB hAinj hBinj
    hAdisj hBdisj hint hendsA hendsB htrans

/-- **The block form of the `top₀` clause.**  The design truncates the three sweeps of one triple at
*pairwise distinct* levels (`c 0 > c 1 > c 2`), so the block count uses the floor `cblk`; the side
values are nevertheless the canonical ones `sideAt … u`, by
`Work.Drive.diskCut_clampedSweep_irrel`.  The two hypotheses `hlev1`, `hlev2` are exactly the instances
of that independence lemma. -/
theorem Capping.odd_ncard_topBdryMeet_zero_eq_sideAt_mul_of_block
    (Q : ℂ → CappingSpace)
    (P : UnitAddCircle → EuclideanSpace ℝ (Fin 2) → CappingSpace) (c : UnitAddCircle → ℝ)
    (cblk : Fin 3 → ℝ) (ψ : ℝ → ℝ) (hψ : ψ 1 = 0) (u : Fin 3 → UnitAddCircle)
    (hP0 : P (u 0) = diskPlane Q)
    (hlev1 : diskCut Q (clampedSweep (cblk 1) ψ (P (u 1))) =
      diskCut Q (clampedSweep (c (u 1)) ψ (P (u 1))))
    (hlev2 : diskCut Q (clampedSweep (cblk 2) ψ (P (u 2))) =
      diskCut Q (clampedSweep (c (u 2)) ψ (P (u 2))))
    (hfibV : ∀ y ∈ cutBaseBox (P (u 0)) (clampedSweep (cblk 1) ψ (P (u 1)))
        (clampedSweep (cblk 2) ψ (P (u 2))),
      (cutFibreBox (P (u 0)) (clampedSweep (cblk 1) ψ (P (u 1))) y).ncard = 1)
    (hfibW : ∀ y ∈ cutBaseBox (P (u 0)) (clampedSweep (cblk 1) ψ (P (u 1)))
        (clampedSweep (cblk 2) ψ (P (u 2))),
      (cutFibreBox (P (u 0)) (clampedSweep (cblk 2) ψ (P (u 2))) y).ncard = 1)
    (A B : Fin 1 → ℝ → EuclideanSpace ℝ (Fin 2))
    (hV : diskCut Q (clampedSweep (cblk 1) ψ (P (u 1))) = arcCycle A ∨
      diskCut Q (clampedSweep (cblk 1) ψ (P (u 1))) = ∅)
    (hW : diskCut Q (clampedSweep (cblk 2) ψ (P (u 2))) = arcCycle B ∨
      diskCut Q (clampedSweep (cblk 2) ψ (P (u 2))) = ∅)
    (hchordA : ∀ i, IsChord (A i)) (hchordB : ∀ j, IsChord (B j))
    (hAinj : ∀ i, Set.InjOn (A i) (Set.Icc (0 : ℝ) 1))
    (hBinj : ∀ j, Set.InjOn (B j) (Set.Icc (0 : ℝ) 1))
    (hAdisj : ∀ i i' : Fin 1, i ≠ i' →
      Disjoint (A i '' Set.Icc (0 : ℝ) 1) (A i' '' Set.Icc (0 : ℝ) 1))
    (hBdisj : ∀ j j' : Fin 1, j ≠ j' →
      Disjoint (B j '' Set.Icc (0 : ℝ) 1) (B j' '' Set.Icc (0 : ℝ) 1))
    (hint : ∀ (i : Fin 1) (j : Fin 1) (t s : ℝ), t ∈ Set.Icc (0 : ℝ) 1 → s ∈ Set.Icc (0 : ℝ) 1 →
      A i t = B j s → t ∈ Set.Ioo (0 : ℝ) 1 ∧ s ∈ Set.Ioo (0 : ℝ) 1 ∧ ‖A i t‖ < 1)
    (hendsA : ∀ i k : Fin 1, A i 0 = A k 0 ∨ A i 0 = antipode (A k 0) → i = k)
    (hendsB : ∀ j l : Fin 1, B j 0 = B l 0 ∨ B j 0 = antipode (B l 0) → j = l)
    (htrans : ∀ (i : Fin 1) (j : Fin 1) (t s : ℝ), t ∈ Set.Ioo (0 : ℝ) 1 → s ∈ Set.Ioo (0 : ℝ) 1 →
      A i t = B j s → det2 (deriv (A i) t) (deriv (B j) s) ≠ 0) :
    Odd (topBdryMeet CappingSpace
        (fun k => clampedSweep (cblk k) ψ (P (u k))) 0).ncard ↔
      sideAt Q P c ψ (u 1) * sideAt Q P c ψ (u 2) = 1 := by
  rw [Capping.odd_ncard_topBdryMeet_zero_eq_side_mul Q (fun k => P (u k)) hP0 cblk ψ hψ
    hfibV hfibW A B hV hW hchordA hchordB hAinj hBinj hAdisj hBdisj hint hendsA hendsB htrans,
    hlev1, hlev2, sideAt_apply, sideAt_apply]

/-- **The presentation of the rotated plane**: the rotation of the chart `Q` by the angle `w`, read as
a box presentation.  This is the family the counting route sweeps, and the family the side function of
the order is indexed by. -/
noncomputable def rotPresentation (Q : ℂ → CappingSpace) (w : UnitAddCircle) :
    EuclideanSpace ℝ (Fin 2) → CappingSpace :=
  diskPlane fun z => rotCapping w (Q z)

/-- **THE SIDE FUNCTION OF THE ROUTE.**  For the chart `Q` of the reference plane, a truncation family
`c` (any family of admissible levels, i.e. below the levels of the chart on the disk and of each swept
plane on its box) and a cutoff `ψ`:

> `sideOf Q c ψ w = 1  ⟺  the cut of `Q` by the sweep of the rotated plane `w·P₀` is non-empty`,

i.e. the side function `b` of Hugelmeyer's order on the non-collision angles.  By
`Work.Drive.diskCut_clampedSweep_irrel` its value does not depend on the choice of `c` or `ψ`. -/
noncomputable def sideOf (Q : ℂ → CappingSpace) (c : UnitAddCircle → ℝ) (ψ : ℝ → ℝ)
    (w : UnitAddCircle) : ZMod 2 :=
  sideAt Q (rotPresentation Q) c ψ w

theorem sideOf_eq_one_iff {Q : ℂ → CappingSpace} {c : UnitAddCircle → ℝ} {ψ : ℝ → ℝ}
    {w : UnitAddCircle} :
    sideOf Q c ψ w = 1 ↔
      diskCut Q (clampedSweep (c w) ψ (rotPresentation Q w)) ≠ ∅ := by
  rw [sideOf, sideAt_eq_one_iff]

/-- **The cut transport under a rotation of the whole configuration.**  Rotating the chart and every
chain by `v` does not change the cut: both the chart and the sweep are transported by the same
homeomorphism `rotCapping v`. -/
theorem diskCut_rotCapping (Q : ℂ → CappingSpace)
    (V : EuclideanSpace ℝ (Fin 3) → CappingSpace) (v : UnitAddCircle) :
    diskCut (fun z => rotCapping v (Q z)) (fun x => rotCapping v (V x)) = diskCut Q V := by
  ext x
  simp only [diskCut, Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · rintro ⟨h1, y, hy, hxy⟩
    exact ⟨h1, y, hy, rotCapping_injective' v hxy⟩
  · rintro ⟨h1, y, hy, hxy⟩
    exact ⟨h1, y, hy, by rw [hxy]⟩

/-- **The cut of a rotated sweep of a rotated plane is the cut of the sweep of the plane.**  Combining
the rotation of the chart with `Work.Drive.clampedSweep_rotCapping`, this identifies the cuts of the
three blocks of a triple with the cuts computed in the reference chart — which is what makes the three
clauses `top₀/top₁/top₂` talk about *one* side function. -/
theorem diskCut_clampedSweep_rotCapping (Q : ℂ → CappingSpace) (c : ℝ) (ψ : ℝ → ℝ)
    (P : EuclideanSpace ℝ (Fin 2) → CappingSpace) (v : UnitAddCircle) :
    diskCut (fun z => rotCapping v (Q z))
        (clampedSweep c ψ (fun y => rotCapping v (P y)))
      = diskCut Q (clampedSweep c ψ P) := by
  have hfun : clampedSweep c ψ (fun y' => rotCapping v (P y'))
      = fun y => rotCapping v (clampedSweep c ψ P y) := by
    funext y
    exact clampedSweep_rotCapping v c ψ P y
  rw [hfun]
  exact diskCut_rotCapping Q (clampedSweep c ψ P) v

/-- **The rotated presentation of a rotated angle is the presentation of the sum.**  The group law of
the rotation (`Work.Drive.rotCapping_add`) read on the box presentations. -/
theorem rotPresentation_add (Q : ℂ → CappingSpace) (v w : UnitAddCircle) :
    (fun y : EuclideanSpace ℝ (Fin 2) => rotCapping v (rotPresentation Q w y))
      = rotPresentation Q (v + w) := by
  funext y
  show rotCapping v (diskPlane (fun z => rotCapping w (Q z)) y)
      = diskPlane (fun z => rotCapping (v + w) (Q z)) y
  simp only [diskPlane_apply]
  rw [show rotCapping (v + w) = rotCapping v ∘ rotCapping w from rotCapping_add v w]
  rfl

/-- **THE CUT OF A BLOCK, READ IN THE BASE CHART.**  For the rotation family, the cut of the plane of
the block `k` by the sweep of the plane of the block `j` is the base cut of the plane of the block
`j − k`: rotating the whole configuration by `−u k` transports both the chart and the sweep
(`Work.Drive.diskCut_clampedSweep_rotCapping`) and turns the presentation `rotPresentation Q (u j)`
into `rotPresentation Q (u j − u k)` (`Work.Drive.rotPresentation_add`).  This is the identification
that makes the three clauses `top₀/top₁/top₂` speak about *one* side function. -/
theorem diskCut_block_eq_base (Q : ℂ → CappingSpace) (u : Fin 3 → UnitAddCircle)
    (c : ℝ) (ψ : ℝ → ℝ) (j k : Fin 3) :
    diskCut (fun z : ℂ => rotCapping (u k) (Q z))
        (clampedSweep c ψ (rotPresentation Q (u j)))
      = diskCut Q (clampedSweep c ψ (rotPresentation Q (u j - u k))) := by
  have hfun : (fun y : EuclideanSpace ℝ (Fin 2) =>
        rotCapping (u k) (rotPresentation Q (u j - u k) y))
      = rotPresentation Q (u j) := by
    have h := rotPresentation_add Q (u k) (u j - u k)
    rw [show u k + (u j - u k) = u j from by abel] at h
    exact h
  rw [← hfun]
  exact diskCut_clampedSweep_rotCapping Q c ψ (rotPresentation Q (u j - u k)) (u k)

/-- **THE `ends_odd` CLAUSE OF THE MULTIPLICATIVITY, from the end contribution.**  The sum of the three
bottom (end) counts of the triple of radial sweeps is `1`
(`Work.Drive.sum_bottomBdryMeet_clampedSweep_eq_one_local`, proved in
`Submission/Work/Drive/bottomBdryMeet_clampedSweep_count.lean`), hence **odd** — which is the third
clause `ends_odd` of `Work.Drive.ChainFunctional` and, together with the `top` clauses, the input of
`Work.Drive.e_add_of_triple`. -/
theorem Capping.odd_sum_bottomBdryMeet_clampedSweeps
    (c : Fin 3 → ℝ) (hc : ∀ k, 0 < c k) (hc1 : c 1 < c 0) (hc2 : c 2 < c 0)
    (ψ : ℝ → ℝ) (hψ0 : ψ 0 = 1) (hψ1 : ψ 1 = 0)
    (hψ01 : ∀ t ∈ Set.Icc (0 : ℝ) 1, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hcont : ContinuousOn ψ (Set.Icc (0 : ℝ) 1)) (hanti : StrictAntiOn ψ (Set.Icc (0 : ℝ) 1))
    (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (hlev : ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)), c 0 < levelOf (P k y))
    (q : Projectivization ℝ (Eucl 3))
    (hy : ∀ k, ∃! y : EuclideanSpace ℝ (Fin 2), y ∈ Submission.Drive.unitBox 1 ∧
      (cappingSpaceHomeoProj (P k y)).2 = q)
    (huniq : ∀ q' : Projectivization ℝ (Eucl 3),
      (∀ k, ∃ y ∈ Submission.Drive.unitBox 1, (cappingSpaceHomeoProj (P k y)).2 = q') → q' = q) :
    Odd ((bottomBdryMeet CappingSpace (fun k => clampedSweep (c k) ψ (P k)) 0).ncard
      + (bottomBdryMeet CappingSpace (fun k => clampedSweep (c k) ψ (P k)) 1).ncard
      + (bottomBdryMeet CappingSpace (fun k => clampedSweep (c k) ψ (P k)) 2).ncard) := by
  have h := sum_bottomBdryMeet_clampedSweep_eq_one_local c hc hc1 hc2 ψ hψ0 hψ1 hψ01 hcont hanti
    P hlev q hy huniq
  rw [h]
  exact ⟨0, by norm_num⟩

end

end Work.Drive
