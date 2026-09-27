import Mathlib
import Submission.Work.Drive.cutTranslate
import Submission.Work.Drive.ncard_tripleMeet_cut
import Submission.Work.Drive.even_ncard_tripleCart_add_ncard_cutBase_of_odd_fibres

/-!
# The box-restricted cut bookkeeping: parameter triples and base points

`Work.Drive.ncard_topBdryMeet_zero_eq_ncard_cutTriples` (`cutTranslate.lean`) identifies the counting
engine's `top` count of the first chain with the number of *cut triples*
`cutTriples P V W` (a plane parameter `u ∈ unitBox 1` and two sweep parameters `y, z ∈ unitBox 2` with
`P u = V y` and `P u = W z`).  What the chain route of
`Submission/Work/Drive/CONCRETE_CHAINS_STATUS.md` §3 item 2 still needs is the passage from those triples
to the *base*: the plane parameters `u` at which **both** cuts are met,
`cutBaseBox P V W` (the finite, `0`-dimensional set which is the mod-2 intersection of the two cut
cycles inside the plane, and which the mod-2 intersection form of `ℝP²` evaluates).

This file supplies exactly that, in the two forms the status note asks for:

* `ncard_cutTriples_eq_ncard_cutBaseBox` — the **generic (singleton fibre) case**: if over every point
  of the base the box-fibre of each of the two cuts is a singleton (the transversality of the cut), the
  projection `(u,y,z) ↦ u` is a bijection, so the two counts are equal;
* `even_ncard_cutTriples_add_ncard_cutBaseBox_of_odd_fibres` — the **odd-multiplicity case** (what the
  radial sweep produces): if over every point of the base both box-fibres have odd cardinality, the two
  counts have the same parity
  (`Work.Drive.even_ncard_tripleCart_add_ncard_cutBase_of_odd_fibres`, transported to the boxes).

Both are pure bookkeeping: the geometry enters only through the finiteness of the fibres (supplied here
as hypotheses, since the cut cycles themselves are one-dimensional and hence infinite).
-/

namespace Work.Drive

open scoped Manifold ContDiff
open Manifold

noncomputable section

variable {Y : Type*} [TopologicalSpace Y]

/-- **The cut relation restricted to the parameter boxes**: the pairs `(u,y)` with `u` a plane
parameter in `unitBox 1`, `y` a sweep parameter in `unitBox 2` and `P u = V y`.  Its boxes make the
`Set`-level bookkeeping of `ncard_tripleMeet_cut.lean` applicable to the concrete cuts of
`cutTranslate.lean`. -/
def cutRelBox (P : EuclideanSpace ℝ (Fin 2) → Y) (V : EuclideanSpace ℝ (Fin 3) → Y) :
    Set (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 3)) :=
  {p | p.1 ∈ Submission.Drive.unitBox 1 ∧ p.2 ∈ Submission.Drive.unitBox 2 ∧
    (p.1, p.2) ∈ cutRel P V}

/-- The cut triples of `cutTranslate.lean` are the parameter triples of the two box-restricted cuts. -/
theorem cutTriples_eq_tripleCart (P : EuclideanSpace ℝ (Fin 2) → Y)
    (V W : EuclideanSpace ℝ (Fin 3) → Y) :
    cutTriples P V W = tripleCart (cutRelBox P V) (cutRelBox P W) := by
  ext p
  simp only [cutTriples, tripleCart, cutRelBox, Set.mem_setOf_eq, Set.mem_ofPred_eq]
  tauto

/-- The box-restricted base of `cutTranslate.lean` is the base of the two box-restricted cuts. -/
theorem cutBaseBox_eq_cutBase (P : EuclideanSpace ℝ (Fin 2) → Y)
    (V W : EuclideanSpace ℝ (Fin 3) → Y) :
    cutBaseBox P V W = cutBase (cutRelBox P V) (cutRelBox P W) := by
  ext u
  simp only [cutBaseBox, cutBase, cutRelBox, Set.mem_setOf_eq, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hu, ⟨y, hy, huy⟩, z, hz, huz⟩
    exact ⟨⟨y, hu, hy, huy⟩, ⟨z, hu, hz, huz⟩⟩
  · rintro ⟨⟨y, hu, hy, huy⟩, ⟨z, _, hz, huz⟩⟩
    exact ⟨hu, ⟨y, hy, huy⟩, z, hz, huz⟩

/-- The `A`-fibre of the box-restricted cut is the box-fibre of `cutTranslate.lean`. -/
theorem fibreA_cutRelBox (P : EuclideanSpace ℝ (Fin 2) → Y)
    (V : EuclideanSpace ℝ (Fin 3) → Y) {u : EuclideanSpace ℝ (Fin 2)}
    (hu : u ∈ Submission.Drive.unitBox 1) :
    fibreA (cutRelBox P V) u = cutFibreBox P V u := by
  ext y
  simp only [fibreA, cutRelBox, cutFibreBox, Set.mem_setOf_eq, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨-, hy, huy⟩
    exact ⟨hy, huy⟩
  · rintro ⟨hy, huy⟩
    exact ⟨hu, hy, huy⟩

/-- The `B`-fibre of the box-restricted cut is the box-fibre of `cutTranslate.lean`. -/
theorem fibreB_cutRelBox (P : EuclideanSpace ℝ (Fin 2) → Y)
    (V : EuclideanSpace ℝ (Fin 3) → Y) {u : EuclideanSpace ℝ (Fin 2)}
    (hu : u ∈ Submission.Drive.unitBox 1) :
    fibreB (cutRelBox P V) u = cutFibreBox P V u := by
  ext y
  simp only [fibreB, fibreA, cutRelBox, cutFibreBox, Set.mem_setOf_eq, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨-, hy, huy⟩
    exact ⟨hy, huy⟩
  · rintro ⟨hy, huy⟩
    exact ⟨hu, hy, huy⟩

/-- **The box-restricted cut bookkeeping, generic case.**  If over every point of the base the box-fibre
of each of the two cuts is a singleton, then the cut triples are in bijection with the base points, and
the two counts agree.  (Both sides are finite in the geometric situation — the cut triples are
`0`-dimensional by transversality — but the proof needs no finiteness: it uses that an injective map
preserves `ncard` unconditionally, `Set.InjOn.ncard_image`, with the infinite case being `0 = 0` on
both sides.) -/
theorem ncard_cutTriples_eq_ncard_cutBaseBox (P : EuclideanSpace ℝ (Fin 2) → Y)
    (V W : EuclideanSpace ℝ (Fin 3) → Y)
    (hfibV : ∀ u ∈ cutBaseBox P V W, (cutFibreBox P V u).ncard = 1)
    (hfibW : ∀ u ∈ cutBaseBox P V W, (cutFibreBox P W u).ncard = 1) :
    (cutTriples P V W).ncard = (cutBaseBox P V W).ncard := by
  set A := cutRelBox P V with hA
  set B := cutRelBox P W with hB
  have htri : cutTriples P V W = tripleCart A B := by rw [hA, hB, cutTriples_eq_tripleCart]
  have hbase : cutBaseBox P V W = cutBase A B := by rw [hA, hB, cutBaseBox_eq_cutBase]
  have hmem : ∀ u ∈ cutBase A B, u ∈ Submission.Drive.unitBox 1 := by
    rintro u ⟨⟨y, hy, -⟩, -⟩
    exact hy
  have hfibA : ∀ u ∈ cutBase A B, (fibreA A u).ncard = 1 := by
    intro u hu
    rw [hA, fibreA_cutRelBox P V (hmem u hu)]
    exact hfibV u (by rw [hbase]; exact hu)
  have hfibB : ∀ u ∈ cutBase A B, (fibreB B u).ncard = 1 := by
    intro u hu
    rw [hB, fibreB_cutRelBox P W (hmem u hu)]
    exact hfibW u (by rw [hbase]; exact hu)
  have hinj : Set.InjOn Prod.fst (tripleCart A B) := by
    intro p hp q hq hpq
    have hpbase : p.1 ∈ cutBase A B := ⟨⟨p.2.1, hp.1⟩, ⟨p.2.2, hp.2⟩⟩
    have hq1 : q.1 = p.1 := hpq.symm
    have hy : p.2.1 = q.2.1 := by
      obtain ⟨a, ha⟩ := Set.ncard_eq_one.mp (hfibA p.1 hpbase)
      have h1 : p.2.1 ∈ fibreA A p.1 := hp.1
      have h2 : q.2.1 ∈ fibreA A p.1 := by
        have hq' : (q.1, q.2.1) ∈ A := hq.1
        rwa [hq1] at hq'
      rw [ha] at h1 h2
      simp only [Set.mem_singleton_iff] at h1 h2
      exact h1.trans h2.symm
    have hz : p.2.2 = q.2.2 := by
      obtain ⟨b, hb⟩ := Set.ncard_eq_one.mp (hfibB p.1 hpbase)
      have h1 : p.2.2 ∈ fibreB B p.1 := hp.2
      have h2 : q.2.2 ∈ fibreB B p.1 := by
        have hq' : (q.1, q.2.2) ∈ B := hq.2
        rwa [hq1] at hq'
      rw [hb] at h1 h2
      simp only [Set.mem_singleton_iff] at h1 h2
      exact h1.trans h2.symm
    rw [show p = (p.1, p.2.1, p.2.2) from rfl, show q = (q.1, q.2.1, q.2.2) from rfl,
      hpq, hy, hz]
  rw [htri, hbase, ← fst_image_tripleCart A B, hinj.ncard_image]

/-- **The box-restricted cut bookkeeping, odd-multiplicity case.**  If over every point of the base both
box-fibres have *odd* cardinality — the situation for the radial sweeps — then the number of cut triples
and the number of base points have the same parity.  This is
`Work.Drive.even_ncard_tripleCart_add_ncard_cutBase_of_odd_fibres` transported to the boxes; the
finiteness of the cut relations in the boxes is supplied as a hypothesis (in the geometric situation it
holds by transversality: the cut is `1`-dimensional inside a compact parameter box and the fibres are
finite). -/
theorem even_ncard_cutTriples_add_ncard_cutBaseBox_of_odd_fibres
    (P : EuclideanSpace ℝ (Fin 2) → Y) (V W : EuclideanSpace ℝ (Fin 3) → Y) (hA : (cutRelBox P V).Finite)
    (hB : (cutRelBox P W).Finite)
    (hfibV : ∀ u ∈ cutBaseBox P V W, Odd (cutFibreBox P V u).ncard)
    (hfibW : ∀ u ∈ cutBaseBox P V W, Odd (cutFibreBox P W u).ncard) :
    Even ((cutTriples P V W).ncard + (cutBaseBox P V W).ncard) := by
  have htri : cutTriples P V W = tripleCart (cutRelBox P V) (cutRelBox P W) :=
    cutTriples_eq_tripleCart P V W
  have hbase : cutBaseBox P V W = cutBase (cutRelBox P V) (cutRelBox P W) :=
    cutBaseBox_eq_cutBase P V W
  have hmem : ∀ u ∈ cutBase (cutRelBox P V) (cutRelBox P W), u ∈ Submission.Drive.unitBox 1 := by
    rintro u ⟨⟨y, hy, -⟩, -⟩
    exact hy
  have hfibV' : ∀ u ∈ cutBase (cutRelBox P V) (cutRelBox P W),
      Odd (fibreA (cutRelBox P V) u).ncard := by
    intro u hu
    rw [fibreA_cutRelBox P V (hmem u hu)]
    exact hfibV u (by rw [hbase]; exact hu)
  have hfibW' : ∀ u ∈ cutBase (cutRelBox P V) (cutRelBox P W),
      Odd (fibreB (cutRelBox P W) u).ncard := by
    intro u hu
    rw [fibreB_cutRelBox P W (hmem u hu)]
    exact hfibW u (by rw [hbase]; exact hu)
  have h := even_ncard_tripleCart_add_ncard_cutBase_of_odd_fibres (cutRelBox P V) (cutRelBox P W)
    hA hB hfibV' hfibW'
  rw [htri, hbase]
  exact h

namespace Capping

/-- **The engine's top count for the first chain is the number of plane parameters on both cuts.**

Composing `ncard_topBdryMeet_zero_eq_ncard_cutTriples` (the engine's top count *is* the cut-triple
count) with the box-restricted bookkeeping, this is the exact form in which
`CONCRETE_CHAINS_STATUS.md` §3 item 2 asks for: the `top_0` count of the radial-sweep triple is the
number of plane parameters `u ∈ unitBox 1` at which *both* cuts are met — the finite, `0`-dimensional
quantity which the mod-2 intersection form of `ℝP²` (`Work.Drive.surf_intersection_form_chords`)
evaluates as `ε_1 · ε_2`.  The hypothesis is the transversality of the two cuts (every box-fibre over
the base a singleton); the odd-multiplicity (radial) version is
`even_ncard_cutTriples_add_ncard_cutBaseBox_of_odd_fibres`. -/
theorem ncard_topBdryMeet_zero_eq_ncard_cutBaseBox
    (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace) (c : Fin 3 → ℝ) (ψ : ℝ → ℝ)
    (hψ : ψ 1 = 0)
    (hfibV : ∀ u ∈ cutBaseBox (P 0) (clampedSweep (c 1) ψ (P 1)) (clampedSweep (c 2) ψ (P 2)),
      (cutFibreBox (P 0) (clampedSweep (c 1) ψ (P 1)) u).ncard = 1)
    (hfibW : ∀ u ∈ cutBaseBox (P 0) (clampedSweep (c 1) ψ (P 1)) (clampedSweep (c 2) ψ (P 2)),
      (cutFibreBox (P 0) (clampedSweep (c 2) ψ (P 2)) u).ncard = 1) :
    (topBdryMeet CappingSpace (fun k => clampedSweep (c k) ψ (P k)) 0).ncard
      = (cutBaseBox (P 0) (clampedSweep (c 1) ψ (P 1)) (clampedSweep (c 2) ψ (P 2))).ncard := by
  rw [ncard_topBdryMeet_zero_eq_ncard_cutTriples P c ψ hψ]
  exact ncard_cutTriples_eq_ncard_cutBaseBox _ _ _ hfibV hfibW

end Capping

end

end Work.Drive
