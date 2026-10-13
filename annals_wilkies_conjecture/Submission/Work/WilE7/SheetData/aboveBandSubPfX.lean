import Mathlib
import Submission.Work.WilE7.SheetData.DefsX
import Submission.Work.WilE7.SheetData._incl_dev
import Submission.Work.WilE7.SheetData.NonstrictLevelFibre
import Submission.Work.WilE7.AboveAux.aboveLevel_subPf
import Submission.Work.WilE7.fiberProduct_semiPf
import Submission.Work.WilE7.SemiPfInter
import Submission.Work.WilE7.subPf_algebra
import Submission.Work.WilE7.SheetData.graphCellSubPfX
import Submission.Work.WilE7.SheetData.aboveRegionSubPf

namespace Work.WilE7.SheetData

open WilkiesDesign WilkiesDesign.E

/-- **The fibre over the base is the set of sheet values.**  The hypotheses `hsub` (each sheet
value lies in `X.set` over `C`), `hcov` (nothing else does) say that for `x ∈ C` the fibre of
`X.set` over `x` is exactly the range of the sheet map `j ↦ s j x`. -/
theorem fiber_eq_range_of_sheets {p m : ℕ} {X : SemiPf (p + (m + 1))} {C : Set (Fin p → ℝ)}
    {k : ℕ} {s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ)}
    (hsub : ∀ j : Fin k, ∀ x ∈ C, Fin.append x (s j x) ∈ X.set)
    (hcov : ∀ z ∈ X.set, projFirst p (m + 1) z ∈ C →
      ∃ j : Fin k, s j (projFirst p (m + 1) z) = projSnd p (m + 1) z) :
    ∀ x ∈ C, fiber X.set x = Set.range (fun j : Fin k => s j x) := by
  intro x hx
  ext u
  constructor
  · -- a fibre point is a sheet value: `hcov` produces the index
    intro hu
    obtain ⟨j, hj⟩ := hcov (Fin.append x u) hu (by rw [Work.WilE7.projFirst_append]; exact hx)
    rw [Work.WilE7.projFirst_append] at hj
    rw [Work.WilE7.projSnd_append] at hj
    exact ⟨j, hj⟩
  · -- a sheet value is a fibre point: `hsub`
    rintro ⟨j, rfl⟩
    exact hsub j x hx

/-- **The `k` sheet values are exactly an enumeration of the fibre.**  In particular, for `x ∈ C`
the fibre of `X.set` over `x` has exactly `k` points: the sheets are injective (`hinj`) and
exhaust it (`hsub` + `hcov`).  This is the (otherwise unstated) cardinality hypothesis of the
graph-cell lemma `Work.WilE7.SheetData.graphCellSubPfX`. -/
theorem fiber_ncard_eq_of_sheets {p m : ℕ} {X : SemiPf (p + (m + 1))} {C : Set (Fin p → ℝ)}
    {k : ℕ} {s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ)}
    (hinj : ∀ x ∈ C, Function.Injective fun j : Fin k => s j x)
    (hsub : ∀ j : Fin k, ∀ x ∈ C, Fin.append x (s j x) ∈ X.set)
    (hcov : ∀ z ∈ X.set, projFirst p (m + 1) z ∈ C →
      ∃ j : Fin k, s j (projFirst p (m + 1) z) = projSnd p (m + 1) z) :
    ∀ x ∈ C, (fiber X.set x).ncard = k := by
  intro x hx
  rw [fiber_eq_range_of_sheets hsub hcov x hx,
    Set.ncard_range_of_injective (hinj x hx), Nat.card_fin]

/-- **The open band above the `i`-th sheet is sub-Pfaffian.**

The set `{y | Fin.init y ∈ C ∧ (s i (Fin.init y)) (Fin.last m) < y (Fin.last p) < 1}` is

* the region above the *graph* of the level function `x ↦ (s i x) (Fin.last m)` over `C`, and
* that graph is sub-Pfaffian by `Work.WilE7.SheetData.graphCellSubPfX` (the non-strict
  level-fibre construction identifies it with `lfY3`, which needs only `Monotone`, not `StrictMono`);
* the region above a sub-Pfaffian subset of `ℝ^{p+1}`, cut by `y.last < 1`, is sub-Pfaffian by
  `Work.WilE7.SheetData.aboveRegionSubPf` (one extra coordinate, two polynomial atoms, project).

The cardinality hypothesis of the graph-cell lemma is supplied by `fiber_ncard_eq_of_sheets`:
`hsub`/`hcov` make the fibre over `x ∈ C` exactly the `k`-element set of sheet values. -/
theorem aboveBandSubPfX (p m : ℕ) (X : WilkiesDesign.E.SemiPf (p + (m + 1)))
    (C : Set (Fin p → ℝ)) (hCpf : WilkiesDesign.E.SubPf p C)
    (k : ℕ) (s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ))
    (hinj : ∀ x ∈ C, Function.Injective fun j : Fin k => s j x)
    (hsub : ∀ j : Fin k, ∀ x ∈ C, Fin.append x (s j x) ∈ X.set)
    (hcov : ∀ z ∈ X.set, WilkiesDesign.E.projFirst p (m + 1) z ∈ C →
      ∃ j : Fin k, s j (WilkiesDesign.E.projFirst p (m + 1) z) = WilkiesDesign.E.projSnd p (m + 1) z)
    (hmono : ∀ x ∈ C, Monotone fun j : Fin k => (s j x) (Fin.last m))
    (i : Fin k) :
    WilkiesDesign.E.SubPf (p + 1)
      {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧
        (s i (Fin.init y)) (Fin.last m) < y (Fin.last p) ∧ y (Fin.last p) < 1} := by
  -- the fibre over `x ∈ C` is the `k`-element set of sheet values
  have hcard : ∀ x ∈ C, (WilkiesDesign.E.fiber X.set x).ncard = k :=
    fiber_ncard_eq_of_sheets hinj hsub hcov
  -- the graph of the `i`-th sheet over `C` is sub-Pfaffian
  have hgraph : WilkiesDesign.E.SubPf (p + 1)
      {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧
        y (Fin.last p) = (s i (Fin.init y)) (Fin.last m)} :=
    graphCellSubPfX X C hCpf k s hinj hsub hcov hcard hmono i
  -- hence so is the band above it
  have habove := aboveRegionSubPf (n := p) hgraph
  -- the band above the graph is the target band
  have hset : {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧
        (s i (Fin.init y)) (Fin.last m) < y (Fin.last p) ∧ y (Fin.last p) < 1}
      = {y : Fin (p + 1) → ℝ | y (Fin.last p) < 1 ∧
        ∃ t : ℝ, Fin.snoc (Fin.init y) t ∈
          {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧
            y (Fin.last p) = (s i (Fin.init y)) (Fin.last m)} ∧ t < y (Fin.last p)} := by
    ext y
    simp only [Set.mem_ofPred_eq, Fin.init_snoc, Fin.snoc_last]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h3, (s i (Fin.init y)) (Fin.last m), ⟨h1, rfl⟩, h2⟩
    · rintro ⟨h3, t, ⟨h1, ht⟩, h2⟩
      exact ⟨h1, ht ▸ h2, h3⟩
  rw [hset]
  exact habove

end Work.WilE7.SheetData
