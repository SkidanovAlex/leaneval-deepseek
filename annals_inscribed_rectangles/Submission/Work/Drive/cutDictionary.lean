import Mathlib
import Submission.Work.Drive.arc_defs
import Submission.Work.Drive.Surf.ChainForm

/-!
# The cut ↔ chord-system dictionary: the counting half

The chain route to Hugelmeyer's order theory counts, on a capped plane `P ≅ ℝP²`, the intersections of
`1`-cycles (`SWEEP_TRANSPORT_NOTES.md` §3, `SURF_STATUS.md`):

* `n_P = #(P ⋔ V_Q ⋔ V_R) = #(A_Q ⋔ A_R)` where `A_V = P ∩ V` is the **cut** of the plane by the
  sweep `V` — the count produced by the engine is `Work.Drive.cutBaseBox`
  (`Work.Drive.ncard_topBdryMeet_zero_eq_ncard_cutBaseBox`), i.e. the number of plane parameters lying
  on both cuts;
* `ε_V = #(C_0 ⋔ V) = #(C_0 ⋔ A_V)` for the essential loop `C_0 ⊂ P`, whose chain-level value is the
  *pairing with the projective line*.

The mod-2 intersection form of `ℝP²` (`Work.Drive.surf_intersection_form_line`) is *proved*, and it is
stated for **systems of chords of the disk model** — `A : ι → ℝ → ℝ²`, with the counts `chordMeetAll`
(crossing *parameter pairs*) and `chainMeetsLine` (the endpoints, i.e. the projective line).

The present file supplies the missing **dictionary** between the two languages, in the form the counts
actually appear:

* `Work.Drive.arcCycle A` — the `1`-cycle of the disk model carried by a system of arcs: the union of
  the arcs' images.  For the route this is the **cut** `A_V ⊆ D̄` (the cut is a `1`-cycle of the plane,
  so its lift to the disk model is a union of arcs whose endpoints are antipodally paired).
* `Work.Drive.ncard_arcCycle_inter` — **the crossings of two systems of arcs are the points of the
  intersection of their cycles**: `#(arcCycle A ∩ arcCycle B) = #(chordMeetAll A B)`; this is the
  identification that turns the engine's *parameter* count (`cutBaseBox`) into the chord count that
  `(SURF)` consumes.
* `Work.Drive.surf_arcCycle` — **`(SURF)` in the language of cycles of the disk model**:
  `Odd #(arcCycle A ∩ arcCycle B) ↔ Odd #(chainMeetsLine A) ∧ Odd #(chainMeetsLine B)`, i.e. the
  mod-2 intersection form of `ℝP²` is `(1)`, in the exact form the route consumes (`n_P ≡ ε_Q ε_R`).
* `Work.Drive.arcCycle_inter_unitCircle_subset` — the boundary points of a cycle are its arc
  endpoints, so `chainMeetsLine` is exactly the set of points of the cycle on the projective line.
* `Work.Drive.isCompact_arcCycle` — the cycle of a finite system of continuous arcs is compact (the
  finiteness input of the counts).

What remains on the *geometric* side (not in this file) is the identification of the concrete cuts
`A_V = P ∩ V` with such arc systems, i.e. the parametrisation of the cut by chords; everything the
counts do with it is here.
-/

namespace Work.Drive

open scoped Topology
open Set

noncomputable section

variable {ι κ : Type*}

/-- **The `1`-cycle carried by a system of arcs** of the disk model `D̄/{z ~ -z} = ℝP²`: the union of
the arcs' images.  This is the subset of the closed disk whose image under `Work.Drive.projDisk` is the
`1`-cycle; the arc endpoints are its crossings with the projective line `L = ∂D̄/∼`. -/
def arcCycle (A : ι → ℝ → EuclideanSpace ℝ (Fin 2)) : Set (EuclideanSpace ℝ (Fin 2)) :=
  ⋃ i, A i '' Set.Icc (0 : ℝ) 1

lemma mem_arcCycle {A : ι → ℝ → EuclideanSpace ℝ (Fin 2)}
    {x : EuclideanSpace ℝ (Fin 2)} :
    x ∈ arcCycle A ↔ ∃ (i : ι) (t : ℝ), t ∈ Set.Icc (0 : ℝ) 1 ∧ A i t = x := by
  simp [arcCycle]

/-- The membership form used in the proofs below. -/
lemma mem_arcCycle_of_eq {A : ι → ℝ → EuclideanSpace ℝ (Fin 2)} {i : ι} {t : ℝ}
    {x : EuclideanSpace ℝ (Fin 2)} (ht : t ∈ Set.Icc (0 : ℝ) 1) (h : A i t = x) :
    x ∈ arcCycle A :=
  (mem_arcCycle (A := A) (x := x)).mpr ⟨i, t, ht, h⟩

/-- The **endpoints** of a system of arcs: the points of the arcs on the unit circle.  For the disk
model these are exactly the crossings of the cycle with the projective line. -/
def arcEnds (A : ι → ℝ → EuclideanSpace ℝ (Fin 2)) : Set (EuclideanSpace ℝ (Fin 2)) :=
  {x | x ∈ unitCircle ∧ ∃ i, x = A i 0 ∨ x = A i 1}

/-- **The boundary points of a cycle are the arc endpoints.**  If the interior of every arc lies
strictly inside the disk (the condition that the cycle is transverse to the projective line), then the
only points of the cycle on the circle are the arc endpoints. -/
lemma arcCycle_inter_unitCircle_subset (A : ι → ℝ → EuclideanSpace ℝ (Fin 2))
    (hstrict : ∀ (i : ι) (t : ℝ), t ∈ Set.Ioo (0 : ℝ) 1 → ‖A i t‖ < 1) :
    arcCycle A ∩ unitCircle ⊆ arcEnds A := by
  rintro x ⟨hx, hxc⟩
  obtain ⟨i, t, ht, hxt⟩ := mem_arcCycle.mp hx
  subst hxt
  refine ⟨hxc, i, ?_⟩
  rcases eq_or_lt_of_le ht.1 with h0 | h0
  · exact Or.inl (by rw [h0])
  rcases eq_or_lt_of_le ht.2 with h1 | h1
  · exact Or.inr (by rw [h1])
  · exact absurd (hstrict i t ⟨h0, h1⟩)
      (by rw [show ‖A i t‖ = 1 from by simpa [unitCircle] using hxc]; exact lt_irrefl 1)

/-- **The cycle of a finite system of continuous arcs is compact** — the finiteness input of every
count below. -/
lemma isCompact_arcCycle [Finite ι] (A : ι → ℝ → EuclideanSpace ℝ (Fin 2))
    (hcont : ∀ i, Continuous (A i)) : IsCompact (arcCycle A) :=
  isCompact_iUnion fun i => isCompact_Icc.image (hcont i)

/-- **The crossings are the points of the intersection of the cycles.**  For two systems of arcs of the
disk model whose arcs are embedded, pairwise disjoint, and meet only in their interiors, the number of
crossing *parameter pairs* (`Work.Drive.chordMeetAll`, the count `(SURF)` is stated for) equals the
number of *points* of `D̄` lying on both cycles — which is what the engine's `cutBaseBox` counts. -/
theorem ncard_arcCycle_inter (A : ι → ℝ → EuclideanSpace ℝ (Fin 2))
    (B : κ → ℝ → EuclideanSpace ℝ (Fin 2))
    (hAinj : ∀ i, Set.InjOn (A i) (Set.Icc (0 : ℝ) 1))
    (hBinj : ∀ j, Set.InjOn (B j) (Set.Icc (0 : ℝ) 1))
    (hAdisj : ∀ i i' : ι, i ≠ i' →
      Disjoint (A i '' Set.Icc (0 : ℝ) 1) (A i' '' Set.Icc (0 : ℝ) 1))
    (hBdisj : ∀ j j' : κ, j ≠ j' →
      Disjoint (B j '' Set.Icc (0 : ℝ) 1) (B j' '' Set.Icc (0 : ℝ) 1))
    (hint : ∀ (i : ι) (j : κ) (t s : ℝ), t ∈ Set.Icc (0 : ℝ) 1 → s ∈ Set.Icc (0 : ℝ) 1 →
      A i t = B j s → t ∈ Set.Ioo (0 : ℝ) 1 ∧ s ∈ Set.Ioo (0 : ℝ) 1) :
    (arcCycle A ∩ arcCycle B).ncard = (chordMeetAll A B).ncard := by
  have himage : (fun p : (ι × ℝ) × (κ × ℝ) => A p.1.1 p.1.2) '' chordMeetAll A B
      = arcCycle A ∩ arcCycle B := by
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      obtain ⟨hp1, hp2, hpx⟩ := hp
      refine ⟨mem_arcCycle_of_eq (⟨le_of_lt hp1.1, le_of_lt hp1.2⟩ : p.1.2 ∈ Set.Icc (0:ℝ) 1) rfl, ?_⟩
      exact mem_arcCycle_of_eq (⟨le_of_lt hp2.1, le_of_lt hp2.2⟩ : p.2.2 ∈ Set.Icc (0:ℝ) 1) hpx.symm
    · rintro ⟨hxA, hxB⟩
      obtain ⟨i, t, ht, hxt⟩ := (mem_arcCycle (A := A) (x := x)).mp hxA
      obtain ⟨j, s, hs, hxs⟩ := (mem_arcCycle (A := B) (x := x)).mp hxB
      have hts := hint i j t s ht hs (hxt.trans hxs.symm)
      exact ⟨((i, t), (j, s)), ⟨hts.1, hts.2, hxt.trans hxs.symm⟩, hxt⟩
  have hinj : Set.InjOn (fun p : (ι × ℝ) × (κ × ℝ) => A p.1.1 p.1.2) (chordMeetAll A B) := by
    rintro ⟨⟨i, t⟩, ⟨j, s⟩⟩ hp ⟨⟨i', t'⟩, ⟨j', s'⟩⟩ hq heq
    obtain ⟨hp1, hp2, hpx⟩ := hp
    obtain ⟨hq1, hq2, hqx⟩ := hq
    have hBs : B j s = B j' s' := hpx.symm.trans (heq.trans hqx)
    have hii : i = i' := by
      by_contra hne
      exact Set.disjoint_left.mp (hAdisj i i' hne)
        ⟨t, ⟨le_of_lt hp1.1, le_of_lt hp1.2⟩, rfl⟩
        ⟨t', ⟨le_of_lt hq1.1, le_of_lt hq1.2⟩, heq.symm⟩
    have htt : t = t' := by
      have h2 := heq
      rw [hii] at h2
      exact hAinj i' ⟨le_of_lt hp1.1, le_of_lt hp1.2⟩ ⟨le_of_lt hq1.1, le_of_lt hq1.2⟩ h2
    have hjj : j = j' := by
      by_contra hne
      exact Set.disjoint_left.mp (hBdisj j j' hne)
        ⟨s, ⟨le_of_lt hp2.1, le_of_lt hp2.2⟩, rfl⟩
        ⟨s', ⟨le_of_lt hq2.1, le_of_lt hq2.2⟩, hBs.symm⟩
    have hss : s = s' := by
      have h2 := hBs
      rw [hjj] at h2
      exact hBinj j' ⟨le_of_lt hp2.1, le_of_lt hp2.2⟩ ⟨le_of_lt hq2.1, le_of_lt hq2.2⟩ h2
    rw [hii, htt, hjj, hss]
  rw [← himage, hinj.ncard_image]


/-- **The endpoints double-count the projective line.**  For a system of chords with distinct endpoints
modulo the antipodal map, the endpoint set is the disjoint union of the two ranges `i ↦ A i 0` and
`i ↦ -A i 0`, so it has exactly twice as many elements as the set of points of the projective line met
by the system (`Work.Drive.chainMeetsLine`, i.e. the pairing `ε_V`).  The engine's seam bookkeeping
counts *boundary parameters*, hence their number is `2 ε_V`. -/
theorem ncard_arcEnds_eq_two_mul_chainMeetsLine [Fintype ι]
    (A : ι → ℝ → EuclideanSpace ℝ (Fin 2))
    (hchord : ∀ i, A i 1 = antipode (A i 0))
    (hstart : ∀ i, A i 0 ∈ unitCircle)
    (hdist : ∀ i k : ι, A i 0 = A k 0 ∨ A i 0 = antipode (A k 0) → i = k) :
    (arcEnds A).ncard = 2 * (chainMeetsLine A).ncard := by
  have hpair : ∀ i k : ι, A i 0 = A k 1 ↔ A i 0 = antipode (A k 0) := fun i k => by
    rw [hchord k]
  have hrange : Set.range (Sum.elim (fun i => A i 0) (fun i => A i 1)) = arcEnds A := by
    ext x
    constructor
    · rintro ⟨i | i, rfl⟩
      · simp only [Sum.elim_inl]
        exact ⟨hstart i, i, Or.inl rfl⟩
      · simp only [Sum.elim_inr]
        refine ⟨?_, i, Or.inr rfl⟩
        rw [hchord i]
        exact antipode_mem_circle (hstart i)
    · rintro ⟨-, i, h | h⟩
      · exact ⟨Sum.inl i, h.symm⟩
      · exact ⟨Sum.inr i, h.symm⟩
  have hzero : ∀ i : ι, ¬ (A i 0 = 0) := by
    intro i h0
    have h2 : ‖A i 0‖ = 1 := by simpa [unitCircle] using hstart i
    rw [h0, norm_zero] at h2
    exact one_ne_zero h2.symm
  have hself : ∀ i : ι, ¬ (A i 0 = antipode (A i 0)) := by
    intro i h0
    exact hzero i ((antipode_eq_self_iff (A i 0)).mp h0.symm)
  have hinj : Function.Injective (Sum.elim (fun i => A i 0) (fun i => A i 1)) := by
    intro a b h
    rcases a with i | i <;> rcases b with k | k
    · simp only [Sum.elim_inl] at h
      exact congrArg Sum.inl (hdist i k (Or.inl h))
    · simp only [Sum.elim_inl, Sum.elim_inr] at h
      have h' : A i 0 = antipode (A k 0) := (hpair i k).mp h
      have hik : i = k := hdist i k (Or.inr h')
      subst hik
      exact absurd (hself i h') (by simp)
    · simp only [Sum.elim_inl, Sum.elim_inr] at h
      have h1 : antipode (A i 0) = A k 0 := by rw [← hchord i]; exact h
      have h' : A i 0 = antipode (A k 0) := by
        have := congrArg antipode h1
        rwa [antipode_involutive (A i 0)] at this
      have hik : i = k := hdist i k (Or.inr h')
      subst hik
      exact absurd (hself i h') (by simp)
    · simp only [Sum.elim_inr] at h
      have h1 : antipode (A i 0) = antipode (A k 0) := by
        rw [← hchord i, ← hchord k]; exact h
      exact congrArg Sum.inr (hdist i k (Or.inl (antipode_injective h1)))
  rw [← hrange, Set.ncard_range_of_injective hinj, Nat.card_eq_fintype_card, Fintype.card_sum,
    ncard_chainMeetsLine A hdist]
  ring

/-- **`(SURF)` in the language of cycles of the disk model**: the mod-2 intersection form of `ℝP²` is
`(1)`.  For two systems of chords of the disk model with distinct endpoints modulo the antipodal map
and crossing oddly, the parity of the number of points lying on both cycles is the product of the two
parities of the pairings with the projective line (`Work.Drive.chainMeetsLine`).

This is `Work.Drive.surf_intersection_form_line` with its count identified by
`Work.Drive.ncard_arcCycle_inter`; it is the exact form the chain route consumes (`n_P ≡ ε_Q ε_R`). -/
theorem surf_arcCycle [Fintype ι] [Fintype κ]
    (A : ι → ℝ → EuclideanSpace ℝ (Fin 2)) (B : κ → ℝ → EuclideanSpace ℝ (Fin 2))
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
    Odd (arcCycle A ∩ arcCycle B).ncard ↔
      (Odd (chainMeetsLine A).ncard ∧ Odd (chainMeetsLine B).ncard) := by
  rw [ncard_arcCycle_inter A B hAinj hBinj hAdisj hBdisj hint]
  exact surf_intersection_form_line A B hendsA hendsB hcross


/-- **`(SURF)` in `Set.ncard` form, with the base case discharged** — the form the chain route can
actually use.

`Work.Drive.surf_intersection_form_chords` (in `Submission/Work/Drive/Surf/ChainFormChords.lean`) is the
same statement with the *unconditional* base case, but its import closure contains
`Work.Drive.winding_eq_crossing_sum` and therefore **cannot be imported together with the counting
engine** (the three declarations of `Work.Drive.toC`, see `TO_C_CLASH.md`).  This version uses
`Work.Drive.surf_intersection_form_line_family`, whose per-pair hypothesis `Work.Drive.ChordPair`
(`Submission/Work/Drive/Surf/ChainForm.lean`) is clash-free, and whose closure is contained in this
file's: it is the form the multiplicativity `n_P ≡ ε_Q ε_R` should be assembled from. -/
theorem surf_arcCycle_chords [Fintype ι] [Fintype κ]
    (A : ι → ℝ → EuclideanSpace ℝ (Fin 2)) (B : κ → ℝ → EuclideanSpace ℝ (Fin 2))
    (hpair : ∀ i j, ChordPair (A i) (B j))
    (hAinj : ∀ i, Set.InjOn (A i) (Set.Icc (0 : ℝ) 1))
    (hBinj : ∀ j, Set.InjOn (B j) (Set.Icc (0 : ℝ) 1))
    (hAdisj : ∀ i i' : ι, i ≠ i' →
      Disjoint (A i '' Set.Icc (0 : ℝ) 1) (A i' '' Set.Icc (0 : ℝ) 1))
    (hBdisj : ∀ j j' : κ, j ≠ j' →
      Disjoint (B j '' Set.Icc (0 : ℝ) 1) (B j' '' Set.Icc (0 : ℝ) 1))
    (hint : ∀ (i : ι) (j : κ) (t s : ℝ), t ∈ Set.Icc (0 : ℝ) 1 → s ∈ Set.Icc (0 : ℝ) 1 →
      A i t = B j s → t ∈ Set.Ioo (0 : ℝ) 1 ∧ s ∈ Set.Ioo (0 : ℝ) 1)
    (hendsA : ∀ i k : ι, A i 0 = A k 0 ∨ A i 0 = antipode (A k 0) → i = k)
    (hendsB : ∀ j l : κ, B j 0 = B l 0 ∨ B j 0 = antipode (B l 0) → j = l) :
    Odd (arcCycle A ∩ arcCycle B).ncard ↔
      (Odd (chainMeetsLine A).ncard ∧ Odd (chainMeetsLine B).ncard) := by
  rw [ncard_arcCycle_inter A B hAinj hBinj hAdisj hBdisj hint]
  exact surf_intersection_form_line_family A B hpair hendsA hendsB

end

end Work.Drive
