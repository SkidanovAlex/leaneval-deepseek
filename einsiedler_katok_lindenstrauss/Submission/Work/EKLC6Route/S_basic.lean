import Mathlib
import Submission.Work.EKLC6Route.Defs
import Submission.Work.EKLC6Route.chartSet_measurable
import Submission.Work.EKLC6Route.measure_dU_zero
import Submission.Work.EKLC6Route.piece_partition
import Submission.Work.EKLC6Route.piece_measurable
import Submission.Work.EKLC6Route.atom_pastSigSet_eq
import Submission.Work.EKLC6Core.firstReturn_partition
import Submission.Work.EKLC6Core.neverReturnSet_null
import Submission.Work.EKLC6Core.atom_iSup_comap_iterate_eq
import Submission.Work.EKLC6Core.countableGenEntropy
import Submission.Work.EKLC6Core.cutHelpers

/-!
# `Work.EKLC6Route.S_basic` — basic properties of the coding partition `S`

The `Window` of `Work.EKLC6Route.Defs` codes a coding partition of `X₃` by the countable family
`w.S : ℕ → Set X₃`, obtained by enumerating the pieces
`(w.W ∪ w.N0)ᶜ`, `w.N0` and `w.D i J c` (first-return time `i`, `θ`-level `J`, grid class `c`)
through an `Encodable` structure on the index type `PIdx = Option (Option (ℕ × Option ℕ × (Fin 3 → Fin 3 → ℤ)))`.
This module assembles the basic facts needed by the rest of the route:

* `w.S` is a countable measurable partition of `X₃`;
* `w.N0 = neverReturnSet t w.W ∪ {z | w.dU z = 0}` is `μ`-null (Poincaré recurrence + `Chart.thin`);
* `w.W` is Borel and `w.dU` is measurable;
* the atom of the past σ-algebra `w.A = pastSigSet t w.S` at `x` is exactly the set of points whose
  whole `Tm t`-orbit shadows that of `x` across the partition `w.S`.
-/

namespace Work.EKLC6Route

open MeasureTheory Filter Topology
open scoped ENNReal
open Work.EKLContract
open Classical

variable {μ : MeasureTheory.Measure X3} {t : Fin 3 → ℝ}

/-- Reading off the `PIdx`-encoding: the enumeration `w.S` used inside `Window.S` is driven by
`Encodable.decode₂ PIdx` for the instance `Encodable.ofCountable PIdx` that `Window.S` installs
locally, so that `w.S n = w.piece p` exactly when that `decode₂` returns `some p`. -/
private lemma Window.S_unfold (w : Window μ t) (n : ℕ) :
    w.S n = (match @Encodable.decode₂ Window.PIdx (Encodable.ofCountable Window.PIdx) n with
      | some p => w.piece p
      | none => ∅) := rfl

/-- `w.S` is measurable as soon as the pieces `w.piece p` are. -/
private lemma Window.S_measurable (w : Window μ t)
    (hp : ∀ p : Window.PIdx, MeasurableSet (w.piece p)) : ∀ n, MeasurableSet (w.S n) := by
  intro n
  rw [Window.S_unfold w n]
  cases h : @Encodable.decode₂ Window.PIdx (Encodable.ofCountable Window.PIdx) n with
  | none => exact MeasurableSet.empty
  | some p => exact hp p

/-- Distinct members of the enumeration `w.S` are disjoint, because they are (or are contained in)
distinct pieces `w.piece p` and `Encodable.encode` is injective. -/
private lemma Window.S_pairwiseDisjoint (w : Window μ t)
    (hpd : ∀ p q : Window.PIdx, p ≠ q → Disjoint (w.piece p) (w.piece q)) :
    ∀ m n, m ≠ n → Disjoint (w.S m) (w.S n) := by
  intro m n hmn
  rw [Window.S_unfold w m, Window.S_unfold w n]
  cases hm : @Encodable.decode₂ Window.PIdx (Encodable.ofCountable Window.PIdx) m with
  | none =>
    cases hn : @Encodable.decode₂ Window.PIdx (Encodable.ofCountable Window.PIdx) n with
    | none => exact disjoint_bot_left
    | some q => exact disjoint_bot_left
  | some p =>
    cases hn : @Encodable.decode₂ Window.PIdx (Encodable.ofCountable Window.PIdx) n with
    | none => exact disjoint_bot_right
    | some q =>
      refine hpd p q ?_
      intro hpq
      have hp1 : @Encodable.encode Window.PIdx (Encodable.ofCountable Window.PIdx) p = m :=
        (@Encodable.decode₂_eq_some Window.PIdx (Encodable.ofCountable Window.PIdx) m p).mp hm
      have hq1 : @Encodable.encode Window.PIdx (Encodable.ofCountable Window.PIdx) q = n :=
        (@Encodable.decode₂_eq_some Window.PIdx (Encodable.ofCountable Window.PIdx) n q).mp hn
      exact hmn (by rw [← hp1, ← hq1, hpq])

/-- The enumeration `w.S` covers `X₃` as soon as the pieces do: every piece `w.piece p` occurs as
`w.S (Encodable.encode p)`. -/
private lemma Window.S_iUnion (w : Window μ t)
    (hpc : (⋃ p : Window.PIdx, w.piece p) = Set.univ) : (⋃ n, w.S n) = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro x
  rw [Set.mem_iUnion]
  have hx : x ∈ ⋃ p : Window.PIdx, w.piece p := by rw [hpc]; trivial
  rw [Set.mem_iUnion] at hx
  obtain ⟨p, hp⟩ := hx
  refine ⟨@Encodable.encode Window.PIdx (Encodable.ofCountable Window.PIdx) p, ?_⟩
  have henc : @Encodable.decode₂ Window.PIdx (Encodable.ofCountable Window.PIdx)
      (@Encodable.encode Window.PIdx (Encodable.ofCountable Window.PIdx) p) = some p :=
    @Encodable.decode₂_encode Window.PIdx (Encodable.ofCountable Window.PIdx) p
  rw [Window.S_unfold w _, henc]
  exact hp

theorem S_basic {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ] {t : Fin 3 → ℝ} (w : Work.EKLC6Route.Window μ t)
    (hmp : MeasureTheory.MeasurePreserving (Work.EKLC6Route.Tm t) μ μ) :
    (∀ n, MeasurableSet (w.S n)) ∧ (∀ m n, m ≠ n → Disjoint (w.S m) (w.S n)) ∧
    (⋃ n, w.S n) = Set.univ ∧ μ w.N0 = 0 ∧ MeasurableSet w.W ∧ Measurable w.dU ∧
    (∀ x, Work.EKLContract.atom w.A x =
      {y | ∀ n, ∀ m, (Work.EKLC6Route.Tm t)^[n] x ∈ w.S m → (Work.EKLC6Route.Tm t)^[n] y ∈ w.S m}) := by
  obtain ⟨hW, hdU, -, hp⟩ := Work.EKLC6Route.piece_measurable w
  obtain ⟨hpd, hpc⟩ := Work.EKLC6Route.piece_partition w hW
  have hdisj := Window.S_pairwiseDisjoint w hpd
  have hcover := Window.S_iUnion w hpc
  have hN0 : μ w.N0 = 0 := by
    rw [show w.N0 = Work.EKLC6Core.neverReturnSet t w.W ∪ {z : X3 | w.dU z = 0} from rfl]
    exact measure_union_null (Work.EKLC6Core.neverReturnSet_null hmp hW)
      (Work.EKLC6Route.measure_dU_zero w)
  refine ⟨Window.S_measurable w hp, hdisj, hcover, hN0, hW, hdU, ?_⟩
  intro x
  exact Work.EKLC6Route.atom_pastSigSet_eq (t := t) w.S x hdisj hcover

end Work.EKLC6Route
