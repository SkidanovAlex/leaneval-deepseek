import Mathlib
import Submission.Work.Drive.cutBaseBox
import Submission.Work.Drive.cutDictionary
import Submission.Work.Drive.sqDisk_foldBox_existsUnique
import Submission.Work.Drive.hcCartesian
import Submission.Work.Drive.ncard_bdryMeet_perm

/-!
# The transport of `(SURF)` to the engine's cut counts

The counting engine (`Work.Drive.manifold_triple_inter_boundary_parity`,
`Work.Drive.even_sum_topBdryMeet_add_bottomBdryMeet`) counts *parameter triples*, and for the radial
sweeps of a plane presentation `P` its `top` count has been identified with the number of **plane
parameters lying on both cuts** (`Work.Drive.ncard_topBdryMeet_zero_eq_ncard_cutBaseBox`):

> `n_P = #(cutBaseBox P V W) = #{u ∈ □ : P u ∈ range V ∧ P u ∈ range W}`.

Hugelmeyer's Lemma 2 (the multiplicativity of the mod-2 intersection form of `ℝP²`) says that this
number is `ε_V · ε_W`, where `ε_U` is the number of **arcs** of the cut `A_U = P ∩ U` — the paper's
`ε_U = #(C_0 ⋔ A_U)`, with `C_0 ⊂ P` the essential loop.

The mod-2 intersection form of `ℝP²` in exactly this form is **proved** in the workspace
(`Work.Drive.surf_arcCycle`, `cutDictionary.lean` / `Surf/ChainForm.lean`): for two systems of chords
`A`, `B` of the disk model of `ℝP²` in general position,

> `Odd #(A ⋔ B) ↔ Odd (chainMeetsLine A) ∧ Odd (chainMeetsLine B)`,
> `chainMeetsLine A = ` the number of chords of `A` (`Work.Drive.ncard_chainMeetsLine`).

What was missing is the **dictionary** between the two languages: the engine's count `cutBaseBox P V W`
is taken over the *parameter square* of the plane presentation, while `(SURF)` is stated on the *disk
model* `D̄/∼`.  This file supplies that dictionary:

* `Work.Drive.diskCut Q V` — the lift of the cut of a *disk-presented* plane
  (`Work.Drive.diskPlane Q = Q ∘ sqDisk ∘ foldBox`) to the disk model: the points of the closed disk
  whose plane point lies on the chain `V`;
* **`Work.Drive.ncard_cutBaseBox_eq_diskCut`** — the square-to-disk parametrisation
  `Work.Drive.sqDisk_foldBox_existsUnique` (`sqDisk ∘ foldBox` is a bijection of the unit square onto
  the closed disk) identifies the two parameter counts:
  `#(cutBaseBox (diskPlane Q) V W) = #(diskCut Q V ∩ diskCut Q W)`.  This is the step that turns the
  engine's *parameter* count into a count of *points* of the disk model, i.e. into the input of
  `(SURF)`;
* **`Work.Drive.odd_ncard_cutBaseBox_iff_arcParity`** — the transport: if the two cuts of the disk
  presentation are systems of chords `A`, `B`, then the engine's count splits multiplicatively,
  `Odd #(cutBaseBox) ↔ Odd (chainMeetsLine A) ∧ Odd (chainMeetsLine B)`.

So the whole geometric content of the multiplicativity `n_P ≡ ε_Q ε_R` is isolated in the two
hypotheses `diskCut Q V = arcCycle A`, `diskCut Q W = arcCycle B` — the statement that the cut of the
plane by the sweep, lifted to the disk model, is a system of chords, with the endpoints defining the
arcs.  Everything else is bookkeeping plus the proved `(SURF)`.

**Notation.**  `Eucl n` abbreviates `EuclideanSpace ℝ (Fin (n + 1))`
(`ProjectiveTopology.lean`), so the plane parameter is `Eucl 1 = ℝ²` and the sweep parameter
`Eucl 2 = ℝ³`.
-/

namespace Work.Drive

open scoped Topology Manifold ContDiff
open Set

noncomputable section

/-- **The cut of a disk-presented plane, lifted to the disk model.**  For a disk presentation
`Q : ℂ → CappingSpace` of the plane and a chain `V` of the capping space, this is the set of points of
the closed disk — read in the parameter plane through `Work.Drive.cplxOf` — whose plane point lies on
the chain `V` (more precisely on the restriction of `V` to the parameter cube `unitBox 2`, which is
what the engine's `Work.Drive.cutBaseBox` counts).

For `V = clampedSweep c ψ P_u` this is the *cut* `A_u = P ∩ V_u` of the transport chapter
(`CUT_TRANSPORT_DESIGN.md`), a `1`-cycle of `ℝP²` when the intersection is transverse. -/
def diskCut (Q : ℂ → CappingSpace) (V : EuclideanSpace ℝ (Fin 3) → CappingSpace) :
    Set (EuclideanSpace ℝ (Fin 2)) :=
  {x | ‖cplxOf x‖ ≤ 1 ∧ Q (cplxOf x) ∈ V '' Submission.Drive.unitBox 2}

/-- **The descent of the parameter square to the disk**: the map inverse to
`Work.Drive.sqDisk ∘ Work.Drive.foldBox` (`Work.Drive.sqDisk_foldBox_existsUnique`), read in the
parameter plane through `Work.Drive.cplxOfInv`. -/
def diskPtFun (y : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  cplxOfInv (sqDisk (foldBox y))

@[simp] lemma diskPtFun_apply (y : EuclideanSpace ℝ (Fin 2)) :
    diskPtFun y = cplxOfInv (sqDisk (foldBox y)) := rfl

/-- **The cut is compact** (and hence closed) for a continuous presentation and a continuous chain:
it is closed, being the preimage of the compact set `V '' unitBox 2` under the continuous map
`x ↦ Q (cplxOf x)`, and it is contained in the compact disc.  This is step 1 of the recipe for the
geometric input (G) in `CUT_TRANSPORT_STATUS.md` §5. -/
theorem isCompact_diskCut (Q : ℂ → CappingSpace) (hQ : Continuous Q)
    (V : EuclideanSpace ℝ (Fin 3) → CappingSpace) (hV : Continuous V) :
    IsCompact (diskCut Q V) := by
  haveI : T2Space CappingSpace := Work.Drive.t2Space_cappingSpace
  have hcplx : Continuous fun x : EuclideanSpace ℝ (Fin 2) => cplxOf x := by
    have h : (fun x : EuclideanSpace ℝ (Fin 2) => cplxOf x) = ⇑Work.Drive.LinChart.cplxOfLIE :=
      funext fun x => (Work.Drive.LinChart.cplxOfLIE_apply x).symm
    rw [h]
    exact Work.Drive.LinChart.cplxOfLIE.continuous
  have hcont : Continuous fun x : EuclideanSpace ℝ (Fin 2) => Q (cplxOf x) := hQ.comp hcplx
  have hK : IsCompact (V '' Submission.Drive.unitBox 2) := (isCompact_unitBox 2).image hV
  have hclosed : IsClosed (diskCut Q V) :=
    (isClosed_le (continuous_norm.comp hcplx) continuous_const).inter (hK.isClosed.preimage hcont)
  refine (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1).of_isClosed_subset hclosed ?_
  intro x hx
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, ← norm_cplxOf x]
  exact hx.1

/-- The plane point of a parameter is the disk presentation of its descent:
`diskPlane Q y = Q (cplxOf (diskPtFun y))`. -/
lemma diskPlane_eq_Q_cplxOf_diskPtFun (Q : ℂ → CappingSpace)
    (y : EuclideanSpace ℝ (Fin 2)) :
    diskPlane Q y = Q (cplxOf (diskPtFun y)) := by
  rw [diskPlane_apply, diskPtFun_apply, cplxOf_cplxOfInv]

/-- **The descent is injective on the unit square.**  This is the uniqueness half of
`Work.Drive.sqDisk_foldBox_existsUnique`. -/
theorem diskPtFun_injOn_unitBox :
    Set.InjOn diskPtFun (Submission.Drive.unitBox 1) := by
  intro u hu v hv huv
  have h1 : sqDisk (foldBox u) = sqDisk (foldBox v) := by
    have h := congrArg cplxOf huv
    rwa [diskPtFun_apply, diskPtFun_apply, cplxOf_cplxOfInv, cplxOf_cplxOfInv] at h
  exact (sqDisk_foldBox_existsUnique (sqDisk (foldBox u))
    (norm_sqDisk_le_one _ (foldBox_mem_unitBox u))).unique ⟨hu, rfl⟩ ⟨hv, h1.symm⟩

/-- **The engine's parameter count is a point count of the disk model.**  The image of the plane's
parameter box `cutBaseBox (diskPlane Q) V W` under the square-to-disk descent is exactly the set of
points of the disk model lying on both cuts, i.e. `diskCut Q V ∩ diskCut Q W`. -/
theorem image_diskPtFun_cutBaseBox (Q : ℂ → CappingSpace)
    (V W : EuclideanSpace ℝ (Fin 3) → CappingSpace) :
    diskPtFun '' cutBaseBox (diskPlane Q) V W = diskCut Q V ∩ diskCut Q W := by
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨hu1, ⟨y, hy, huy⟩, ⟨z, hz, huz⟩⟩ := hu
    simp only [cutRel, Set.mem_ofPred_eq] at huy huz
    refine ⟨⟨?_, y, hy, ?_⟩, ⟨?_, z, hz, ?_⟩⟩
    · rw [diskPtFun_apply, cplxOf_cplxOfInv]
      exact norm_sqDisk_le_one _ (foldBox_mem_unitBox u)
    · rw [← diskPlane_eq_Q_cplxOf_diskPtFun Q u]
      exact huy.symm
    · rw [diskPtFun_apply, cplxOf_cplxOfInv]
      exact norm_sqDisk_le_one _ (foldBox_mem_unitBox u)
    · rw [← diskPlane_eq_Q_cplxOf_diskPtFun Q u]
      exact huz.symm
  · rintro ⟨⟨hx1, hxV⟩, ⟨-, hxW⟩⟩
    obtain ⟨y, hybox, hyeq⟩ := hxV
    obtain ⟨z, hzbox, hzeq⟩ := hxW
    obtain ⟨u, ⟨hu1, hu2⟩, -⟩ := sqDisk_foldBox_existsUnique (cplxOf x) hx1
    have hux : diskPtFun u = x := by
      rw [diskPtFun_apply, hu2, cplxOfInv_cplxOf]
    refine ⟨u, ⟨hu1, ⟨y, hybox, ?_⟩, ⟨z, hzbox, ?_⟩⟩, hux⟩
    · show diskPlane Q u = V y
      rw [diskPlane_apply, hu2, ← hyeq]
    · show diskPlane Q u = W z
      rw [diskPlane_apply, hu2, ← hzeq]

/-- **The engine's count of plane parameters on both cuts *is* the mod-2 intersection number of the
two cuts inside the disk model.**  The square-to-disk parametrisation is a bijection of the parameter
box onto the closed disk (`Work.Drive.sqDisk_foldBox_existsUnique`), hence preserves cardinalities. -/
theorem ncard_cutBaseBox_eq_diskCut (Q : ℂ → CappingSpace)
    (V W : EuclideanSpace ℝ (Fin 3) → CappingSpace) :
    (cutBaseBox (diskPlane Q) V W).ncard = (diskCut Q V ∩ diskCut Q W).ncard := by
  have hinj : Set.InjOn diskPtFun (cutBaseBox (diskPlane Q) V W) :=
    diskPtFun_injOn_unitBox.mono (fun u hu => hu.1)
  rw [← image_diskPtFun_cutBaseBox Q V W]
  exact hinj.ncard_image.symm

/-- **THE TRANSPORT: the multiplicativity `n_P ≡ ε_Q ε_R` of Hugelmeyer's Lemma 2**, in the exact
vocabulary of the counting engine.

If the two cuts of the disk presentation `Q` are systems of chords `A`, `B` of the disk model
(`diskCut Q V = arcCycle A`, `diskCut Q W = arcCycle B`, i.e. the cuts *are* the arc systems — this is
the single geometric input, the "dictionary" of the transport chapter), and the two systems are in
general position in the sense of `(SURF)` (`Work.Drive.surf_arcCycle`), then the engine's count of
plane parameters on both cuts has the parity of the product of the two **arc counts**
`Work.Drive.chainMeetsLine A`, `Work.Drive.chainMeetsLine B` — i.e. of `ε_V` and `ε_W`, the paper's
`#(C_0 ⋔ A_U)`. -/
theorem odd_ncard_cutBaseBox_iff_arcParity {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Q : ℂ → CappingSpace)
    (V W : EuclideanSpace ℝ (Fin 3) → CappingSpace)
    (A : ι → ℝ → EuclideanSpace ℝ (Fin 2)) (B : κ → ℝ → EuclideanSpace ℝ (Fin 2))
    (hVcut : diskCut Q V = arcCycle A) (hWcut : diskCut Q W = arcCycle B)
    (hAinj : ∀ i, Set.InjOn (A i) (Set.Icc (0 : ℝ) 1))
    (hBinj : ∀ j, Set.InjOn (B j) (Set.Icc (0 : ℝ) 1))
    (hAdisj : ∀ i i' : ι, i ≠ i' →
      Disjoint (A i '' Set.Icc (0 : ℝ) 1) (A i' '' Set.Icc (0 : ℝ) 1))
    (hBdisj : ∀ j j' : κ, j ≠ j' →
      Disjoint (B j '' Set.Icc (0 : ℝ) 1) (B j' '' Set.Icc (0 : ℝ) 1))
    (hint : ∀ (i : ι) (j : κ) (t s : ℝ), t ∈ Set.Icc (0 : ℝ) 1 → s ∈ Set.Icc (0 : ℝ) 1 →
      A i t = B j s → t ∈ Set.Ioo (0 : ℝ) 1 ∧ s ∈ Set.Ioo (0 : ℝ) 1)
    (hendsA : ∀ i k : ι, A i 0 = A k 0 ∨ A i 0 = antipode (A k 0) → i = k)
    (hendsB : ∀ j l : κ, B j 0 = B l 0 ∨ B j 0 = antipode (B l 0) → j = l)
    (hcross : ∀ i j, Odd (chordMeet (A i) (B j)).ncard) :
    Odd (cutBaseBox (diskPlane Q) V W).ncard ↔
      (Odd (chainMeetsLine A).ncard ∧ Odd (chainMeetsLine B).ncard) := by
  rw [ncard_cutBaseBox_eq_diskCut, hVcut, hWcut]
  exact surf_arcCycle A B hAinj hBinj hAdisj hBdisj hint hendsA hendsB hcross

/-- **The parameter-level dictionary**: the engine's count of plane parameters on both cuts is the
number of crossing *parameter pairs* of the two arc systems (`Work.Drive.chordMeetAll`) — the count
`(SURF)` is stated for.  Bookkeeping (`Work.Drive.ncard_arcCycle_inter`) plus the cut identification. -/
theorem ncard_cutBaseBox_eq_chordMeetAll {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Q : ℂ → CappingSpace)
    (V W : EuclideanSpace ℝ (Fin 3) → CappingSpace)
    (A : ι → ℝ → EuclideanSpace ℝ (Fin 2)) (B : κ → ℝ → EuclideanSpace ℝ (Fin 2))
    (hVcut : diskCut Q V = arcCycle A) (hWcut : diskCut Q W = arcCycle B)
    (hAinj : ∀ i, Set.InjOn (A i) (Set.Icc (0 : ℝ) 1))
    (hBinj : ∀ j, Set.InjOn (B j) (Set.Icc (0 : ℝ) 1))
    (hAdisj : ∀ i i' : ι, i ≠ i' →
      Disjoint (A i '' Set.Icc (0 : ℝ) 1) (A i' '' Set.Icc (0 : ℝ) 1))
    (hBdisj : ∀ j j' : κ, j ≠ j' →
      Disjoint (B j '' Set.Icc (0 : ℝ) 1) (B j' '' Set.Icc (0 : ℝ) 1))
    (hint : ∀ (i : ι) (j : κ) (t s : ℝ), t ∈ Set.Icc (0 : ℝ) 1 → s ∈ Set.Icc (0 : ℝ) 1 →
      A i t = B j s → t ∈ Set.Ioo (0 : ℝ) 1 ∧ s ∈ Set.Ioo (0 : ℝ) 1) :
    (cutBaseBox (diskPlane Q) V W).ncard = (chordMeetAll A B).ncard := by
  rw [ncard_cutBaseBox_eq_diskCut, hVcut, hWcut]
  exact ncard_arcCycle_inter A B hAinj hBinj hAdisj hBdisj hint

/-- **The transport in the form closest to the geometry**: the two cuts are systems of chords *in
general position* (`Work.Drive.ChordPair`, i.e. both are `C^∞` chords whose crossings are strictly
interior and whose straightening family is transverse), the arcs are embedded and pairwise disjoint
within each system, and the endpoints are distinct modulo the antipodal map.  Then the engine's count
has the parity of the product of the two arc counts, with the odd crossing parity of every pair
supplied by the proved `Work.Surf.chord_parity` (`Work.Drive.odd_ncard_chordMeet_of_pair`). -/
theorem odd_ncard_cutBaseBox_iff_arcParity_of_chordPair {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Q : ℂ → CappingSpace)
    (V W : EuclideanSpace ℝ (Fin 3) → CappingSpace)
    (A : ι → ℝ → EuclideanSpace ℝ (Fin 2)) (B : κ → ℝ → EuclideanSpace ℝ (Fin 2))
    (hVcut : diskCut Q V = arcCycle A) (hWcut : diskCut Q W = arcCycle B)
    (hAinj : ∀ i, Set.InjOn (A i) (Set.Icc (0 : ℝ) 1))
    (hBinj : ∀ j, Set.InjOn (B j) (Set.Icc (0 : ℝ) 1))
    (hAdisj : ∀ i i' : ι, i ≠ i' →
      Disjoint (A i '' Set.Icc (0 : ℝ) 1) (A i' '' Set.Icc (0 : ℝ) 1))
    (hBdisj : ∀ j j' : κ, j ≠ j' →
      Disjoint (B j '' Set.Icc (0 : ℝ) 1) (B j' '' Set.Icc (0 : ℝ) 1))
    (hendsA : ∀ i k : ι, A i 0 = A k 0 ∨ A i 0 = antipode (A k 0) → i = k)
    (hendsB : ∀ j l : κ, B j 0 = B l 0 ∨ B j 0 = antipode (B l 0) → j = l)
    (hpair : ∀ i j, ChordPair (A i) (B j)) :
    Odd (cutBaseBox (diskPlane Q) V W).ncard ↔
      (Odd (chainMeetsLine A).ncard ∧ Odd (chainMeetsLine B).ncard) := by
  refine odd_ncard_cutBaseBox_iff_arcParity Q V W A B hVcut hWcut hAinj hBinj hAdisj hBdisj
    (fun i j t s ht hs h => (hpair i j).2.2.2.2.1 t s ht hs h) hendsA hendsB
    (fun i j => odd_ncard_chordMeet_of_pair (hpair i j))

/-- **The `ε` dictionary: the arc count of a cut is the number of chords of the system**, i.e. the
engine's pairing `#(C_0 ⋔ A_V)` of the cut with the essential loop `C_0` (the projective line of the
disk model).  This is `Work.Drive.ncard_chainMeetsLine`, recorded here in the route's `ε` notation. -/
theorem ncard_chainMeetsLine_eq_card {ι : Type*} [Fintype ι]
    (A : ι → ℝ → EuclideanSpace ℝ (Fin 2))
    (hends : ∀ i k : ι, A i 0 = A k 0 ∨ A i 0 = antipode (A k 0) → i = k) :
    (chainMeetsLine A).ncard = Fintype.card ι :=
  ncard_chainMeetsLine A hends

/-- **The multiplicativity in the `Odd`-product form**: the engine's count is odd exactly when the
product of the two arc counts is odd.  (`Odd (m * n) ↔ Odd m ∧ Odd n`.) -/
theorem odd_ncard_cutBaseBox_iff_mul {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Q : ℂ → CappingSpace)
    (V W : EuclideanSpace ℝ (Fin 3) → CappingSpace)
    (A : ι → ℝ → EuclideanSpace ℝ (Fin 2)) (B : κ → ℝ → EuclideanSpace ℝ (Fin 2))
    (hVcut : diskCut Q V = arcCycle A) (hWcut : diskCut Q W = arcCycle B)
    (hAinj : ∀ i, Set.InjOn (A i) (Set.Icc (0 : ℝ) 1))
    (hBinj : ∀ j, Set.InjOn (B j) (Set.Icc (0 : ℝ) 1))
    (hAdisj : ∀ i i' : ι, i ≠ i' →
      Disjoint (A i '' Set.Icc (0 : ℝ) 1) (A i' '' Set.Icc (0 : ℝ) 1))
    (hBdisj : ∀ j j' : κ, j ≠ j' →
      Disjoint (B j '' Set.Icc (0 : ℝ) 1) (B j' '' Set.Icc (0 : ℝ) 1))
    (hint : ∀ (i : ι) (j : κ) (t s : ℝ), t ∈ Set.Icc (0 : ℝ) 1 → s ∈ Set.Icc (0 : ℝ) 1 →
      A i t = B j s → t ∈ Set.Ioo (0 : ℝ) 1 ∧ s ∈ Set.Ioo (0 : ℝ) 1)
    (hendsA : ∀ i k : ι, A i 0 = A k 0 ∨ A i 0 = antipode (A k 0) → i = k)
    (hendsB : ∀ j l : κ, B j 0 = B l 0 ∨ B j 0 = antipode (B l 0) → j = l)
    (hcross : ∀ i j, Odd (chordMeet (A i) (B j)).ncard) :
    Odd (cutBaseBox (diskPlane Q) V W).ncard ↔
      Odd ((chainMeetsLine A).ncard * (chainMeetsLine B).ncard) := by
  rw [odd_ncard_cutBaseBox_iff_arcParity Q V W A B hVcut hWcut hAinj hBinj hAdisj hBdisj hint
    hendsA hendsB hcross, Nat.odd_mul]

/-- **THE TRANSPORT, END TO END, IN THE ENGINE'S OWN COUNT.**  For the three radial sweeps of a
plane presentation `P` whose first plane is the disk-presented plane `diskPlane Q`
(`Work.Drive.ncard_topBdryMeet_zero_eq_ncard_cutBaseBox`, so the transversality of the two cuts over
the base and the cutoff normalisation `ψ 1 = 0` are the hypotheses), if the two cuts of `Q` are systems
of chords in general position, then the engine's `top` count of the first block — the paper's `n_P` —
has the parity of the product of the two arc counts:

> `Odd n_P ↔ Odd ε_Q ∧ Odd ε_R`.

This is Hugelmeyer's Lemma 2 (the multiplicativity `n_P ≡ ε_Q · ε_R`) in the exact form in which the
counting half consumes it (`COUNT_ASSEMBLY_STATUS.md` §4). -/
theorem Capping.odd_ncard_topBdryMeet_zero_iff_arcParity
    (Q : ℂ → CappingSpace) (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (hQ : P 0 = diskPlane Q)
    (c : Fin 3 → ℝ) (ψ : ℝ → ℝ) (hψ : ψ 1 = 0)
    (hfibV : ∀ u ∈ cutBaseBox (P 0) (clampedSweep (c 1) ψ (P 1)) (clampedSweep (c 2) ψ (P 2)),
      (cutFibreBox (P 0) (clampedSweep (c 1) ψ (P 1)) u).ncard = 1)
    (hfibW : ∀ u ∈ cutBaseBox (P 0) (clampedSweep (c 1) ψ (P 1)) (clampedSweep (c 2) ψ (P 2)),
      (cutFibreBox (P 0) (clampedSweep (c 2) ψ (P 2)) u).ncard = 1)
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : ι → ℝ → EuclideanSpace ℝ (Fin 2)) (B : κ → ℝ → EuclideanSpace ℝ (Fin 2))
    (hVcut : diskCut Q (clampedSweep (c 1) ψ (P 1)) = arcCycle A)
    (hWcut : diskCut Q (clampedSweep (c 2) ψ (P 2)) = arcCycle B)
    (hAinj : ∀ i, Set.InjOn (A i) (Set.Icc (0 : ℝ) 1))
    (hBinj : ∀ j, Set.InjOn (B j) (Set.Icc (0 : ℝ) 1))
    (hAdisj : ∀ i i' : ι, i ≠ i' →
      Disjoint (A i '' Set.Icc (0 : ℝ) 1) (A i' '' Set.Icc (0 : ℝ) 1))
    (hBdisj : ∀ j j' : κ, j ≠ j' →
      Disjoint (B j '' Set.Icc (0 : ℝ) 1) (B j' '' Set.Icc (0 : ℝ) 1))
    (hendsA : ∀ i k : ι, A i 0 = A k 0 ∨ A i 0 = antipode (A k 0) → i = k)
    (hendsB : ∀ j l : κ, B j 0 = B l 0 ∨ B j 0 = antipode (B l 0) → j = l)
    (hpair : ∀ i j, ChordPair (A i) (B j)) :
    Odd (topBdryMeet CappingSpace (fun k => clampedSweep (c k) ψ (P k)) 0).ncard ↔
      (Odd (chainMeetsLine A).ncard ∧ Odd (chainMeetsLine B).ncard) := by
  rw [Capping.ncard_topBdryMeet_zero_eq_ncard_cutBaseBox P c ψ hψ hfibV hfibW, hQ]
  exact odd_ncard_cutBaseBox_iff_arcParity_of_chordPair Q _ _ A B hVcut hWcut hAinj hBinj hAdisj
    hBdisj hendsA hendsB hpair

/-- **THE TRANSPORT FOR THE RADIAL SWEEPS** (the odd-multiplicity case, which is the geometric one):
the fibres of the two cuts over the base have *odd* cardinality (the multiplicity of the radial sweep
in `Work.Drive.even_ncard_cutTriples_add_ncard_cutBaseBox_of_odd_fibres`), so the engine's `top` count
of the first block has the same parity as the number of base points, and the transport applies:

> `Odd n_P ↔ Odd ε_Q ∧ Odd ε_R`.

This is Hugelmeyer's Lemma 2 in the exact form the counting half consumes
(`COUNTING_HALF_REMAINING.md` §2, `COUNT_ASSEMBLY_STATUS.md` §4). -/
theorem Capping.odd_ncard_topBdryMeet_zero_iff_arcParity_of_odd_fibres
    (Q : ℂ → CappingSpace) (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (hQ : P 0 = diskPlane Q)
    (c : Fin 3 → ℝ) (ψ : ℝ → ℝ) (hψ : ψ 1 = 0)
    (hfinV : (cutRelBox (P 0) (clampedSweep (c 1) ψ (P 1))).Finite)
    (hfinW : (cutRelBox (P 0) (clampedSweep (c 2) ψ (P 2))).Finite)
    (hfibV : ∀ u ∈ cutBaseBox (P 0) (clampedSweep (c 1) ψ (P 1)) (clampedSweep (c 2) ψ (P 2)),
      Odd (cutFibreBox (P 0) (clampedSweep (c 1) ψ (P 1)) u).ncard)
    (hfibW : ∀ u ∈ cutBaseBox (P 0) (clampedSweep (c 1) ψ (P 1)) (clampedSweep (c 2) ψ (P 2)),
      Odd (cutFibreBox (P 0) (clampedSweep (c 2) ψ (P 2)) u).ncard)
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : ι → ℝ → EuclideanSpace ℝ (Fin 2)) (B : κ → ℝ → EuclideanSpace ℝ (Fin 2))
    (hVcut : diskCut Q (clampedSweep (c 1) ψ (P 1)) = arcCycle A)
    (hWcut : diskCut Q (clampedSweep (c 2) ψ (P 2)) = arcCycle B)
    (hAinj : ∀ i, Set.InjOn (A i) (Set.Icc (0 : ℝ) 1))
    (hBinj : ∀ j, Set.InjOn (B j) (Set.Icc (0 : ℝ) 1))
    (hAdisj : ∀ i i' : ι, i ≠ i' →
      Disjoint (A i '' Set.Icc (0 : ℝ) 1) (A i' '' Set.Icc (0 : ℝ) 1))
    (hBdisj : ∀ j j' : κ, j ≠ j' →
      Disjoint (B j '' Set.Icc (0 : ℝ) 1) (B j' '' Set.Icc (0 : ℝ) 1))
    (hendsA : ∀ i k : ι, A i 0 = A k 0 ∨ A i 0 = antipode (A k 0) → i = k)
    (hendsB : ∀ j l : κ, B j 0 = B l 0 ∨ B j 0 = antipode (B l 0) → j = l)
    (hpair : ∀ i j, ChordPair (A i) (B j)) :
    Odd (topBdryMeet CappingSpace (fun k => clampedSweep (c k) ψ (P k)) 0).ncard ↔
      (Odd (chainMeetsLine A).ncard ∧ Odd (chainMeetsLine B).ncard) := by
  have hbase : Odd (cutBaseBox (P 0) (clampedSweep (c 1) ψ (P 1))
        (clampedSweep (c 2) ψ (P 2))).ncard ↔
      (Odd (chainMeetsLine A).ncard ∧ Odd (chainMeetsLine B).ncard) := by
    rw [hQ]
    exact odd_ncard_cutBaseBox_iff_arcParity_of_chordPair Q _ _ A B hVcut hWcut hAinj hBinj hAdisj
      hBdisj hendsA hendsB hpair
  have hev := even_ncard_cutTriples_add_ncard_cutBaseBox_of_odd_fibres (P 0)
    (clampedSweep (c 1) ψ (P 1)) (clampedSweep (c 2) ψ (P 2)) hfinV hfinW hfibV hfibW
  rw [Nat.even_add] at hev
  have hiff : Odd (cutTriples (P 0) (clampedSweep (c 1) ψ (P 1))
        (clampedSweep (c 2) ψ (P 2))).ncard ↔
      Odd (cutBaseBox (P 0) (clampedSweep (c 1) ψ (P 1))
        (clampedSweep (c 2) ψ (P 2))).ncard := by
    have hmod : (cutTriples (P 0) (clampedSweep (c 1) ψ (P 1))
          (clampedSweep (c 2) ψ (P 2))).ncard % 2
        = (cutBaseBox (P 0) (clampedSweep (c 1) ψ (P 1))
          (clampedSweep (c 2) ψ (P 2))).ncard % 2 := by
      have h1 : (cutTriples (P 0) (clampedSweep (c 1) ψ (P 1))
            (clampedSweep (c 2) ψ (P 2))).ncard % 2 = 0 ↔
          (cutBaseBox (P 0) (clampedSweep (c 1) ψ (P 1))
            (clampedSweep (c 2) ψ (P 2))).ncard % 2 = 0 := by
        simpa [Nat.even_iff] using hev
      omega
    rw [Nat.odd_iff, Nat.odd_iff, hmod]
  rw [ncard_topBdryMeet_zero_eq_ncard_cutTriples P c ψ hψ]
  exact hiff.trans hbase

/-- **The multiplicativity for any block of the triple, by permuting the chains.**  The `k`-th top
boundary count of a triple of chains is the `0`-th top boundary count of the triple with the chains
permuted so that the `k`-th one comes first (`Work.Drive.ncard_bdryMeet_perm`); so the transport
`Work.Drive.Capping.odd_ncard_topBdryMeet_zero_iff_arcParity_of_odd_fibres`, stated for the `0`-th
block, applies to the plane of every block. -/
theorem ncard_topBdryMeet_eq_perm {M : Type*} [TopologicalSpace M]
    (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M) (σ : Equiv.Perm (Fin 3)) :
    (topBdryMeet M (fun i => D (σ i)) 0).ncard = (topBdryMeet M D (σ 0)).ncard := by
  have h := ncard_bdryMeet_perm M D
    (fun z : EuclideanSpace ℝ (Fin 3) => z ∈ Submission.Drive.unitBoxBdry 2 ∧ z 2 = 1) σ
  simpa only [topBdryMeet, tripleBdryMeet, Set.mem_ofPred_eq, and_assoc] using h

/-- The same for the bottom (end) count of the `k`-th block. -/
theorem ncard_bottomBdryMeet_eq_perm {M : Type*} [TopologicalSpace M]
    (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M) (σ : Equiv.Perm (Fin 3)) :
    (bottomBdryMeet M (fun i => D (σ i)) 0).ncard = (bottomBdryMeet M D (σ 0)).ncard := by
  have h := ncard_bdryMeet_perm M D
    (fun z : EuclideanSpace ℝ (Fin 3) => z ∈ Submission.Drive.unitBoxBdry 2 ∧ z 2 = 0) σ
  simpa only [bottomBdryMeet, tripleBdryMeet, Set.mem_ofPred_eq, and_assoc] using h

end

end Work.Drive
