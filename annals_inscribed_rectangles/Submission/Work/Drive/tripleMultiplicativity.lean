import Mathlib
import Submission.Work.Drive.collapseTransport
import Submission.Work.Drive.transportAssembly
import Submission.Work.Drive.collapseT5
import Submission.Work.Drive.t5FaceAvoid
import Submission.Work.Drive.cutBaseBox
import Submission.Work.Drive.rotSideCount

/-!
# The multiplicativity per block of a triple of plane presentations (Hugelmeyer's Lemma 2)

`CHAINPARITY_REDUCTION.md` §4 records that `hdense` — Hugelmeyer's Lemma 4 on a dense set of parameter
triples — is proved by the *triple engine* `Work.Drive.odd_sum_topBdryMeet_clampedSweeps_of_planes`
(which gives `Odd (T 0 + T 1 + T 2)` for the three top counts of the triple of radial sweeps) plus the
**multiplicativity** `T k ≡ ε_j · ε_l` of each block.  The multiplicativity is the radial-collapse
transport, which is on disk in `Submission/Work/Drive/transportAssembly.lean` and
`Submission/Work/Drive/collapseChartBridge.lean`; this file states it in the shape the triple consumes.

The three planes of the design's triple are the rotations `P k = rotPresentation Q (u k)` of one chart,
but each of them *is* a disk plane of a rotated chart (`rotPresentation Q v = diskPlane (rotCapping v ∘
Q)`), so the multiplicativity applies **per block**: take the `k`-th plane as the chart's own plane and
the other two as the two sweeps.  This file does the block `0` of that reduction, where the chart is `Q`
itself and the triple is `(diskPlane Q, P₁, P₂)`:

> `Odd (T 0) ↔ Odd (coreSideCount Q (c 1) P₁) ∧ Odd (coreSideCount Q (c 2) P₂)`,

with two *distinct* levels `c 1 > c 2` (the corrected design's truncation levels,
`END_LEVEL_OBSTRUCTION.md` §3).  Blocks `1` and `2` are obtained from it by the rotation identities
`Work.Drive.coreSideCount_rotCapping` / `coreSideCount_rotPresentation`
(`Submission/Work/Drive/rotSideCount.lean`), which is why the statement is written with the chart's
own plane singled out.

The inputs are exactly the ones the transport consumes: the two endpoint identifications
(`colCount 0 = T 0` — `colCount_zero_eq_topBdryMeet_levels` below, the level-general form of the
proved `colCount_zero_eq_topBdryMeet`; and `colCount 1 = #fibreMeet` —
`colMeet_one_ncard_eq_fibreMeet`), the fibre decomposition (`fibreMeet_ncard_eq_sum_diamMeet`, with its
finiteness and basepoint hypotheses), the box parity `Even (K 0 + K 1)` (T1/T3 through the chart bridge,
`even_ncard_colCount_zero_add_one`) and T5 uniformly in the angle.
-/

set_option autoImplicit false

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace

noncomputable section

/-! ## 1. The `s = 0` collapsed count with three distinct levels

`Work.Drive.colCount_zero_eq_topBdryMeet` identifies `K 0` with the top count `T 0` of the triple
`(diskPlane Q, P₁, P₂)` **with the same level `c` and the same cutoff `ψ`** for the two sweeps.  The
design's triple has three *distinct* levels (`c 0 > c 1 > c 2`), so the identification is needed in the
level-general form; that is what the lemma below supplies (the proof is the same, with the level vector
`c : Fin 3 → ℝ` instead of `![c₀, c, c]`). -/

/-- **`K 0` is the top count of the triple, with distinct levels.** -/
theorem colCount_zero_eq_topBdryMeet_levels (β : ℝ → ℝ) (Q : ℂ → CappingSpace)
    (c : Fin 3 → ℝ) (ψ : ℝ → ℝ) (hψ : ψ 1 = 0)
    (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace) (hP0 : P 0 = diskPlane Q)
    (hfibV : ∀ u ∈ cutBaseBox (P 0) (clampedSweep (c 1) ψ (P 1)) (clampedSweep (c 2) ψ (P 2)),
      (cutFibreBox (P 0) (clampedSweep (c 1) ψ (P 1)) u).ncard = 1)
    (hfibW : ∀ u ∈ cutBaseBox (P 0) (clampedSweep (c 1) ψ (P 1)) (clampedSweep (c 2) ψ (P 2)),
      (cutFibreBox (P 0) (clampedSweep (c 2) ψ (P 2)) u).ncard = 1) :
    colCount β Q (clampedSweep (c 1) ψ (P 1)) (clampedSweep (c 2) ψ (P 2)) 0
      = (topBdryMeet CappingSpace (fun k => clampedSweep (c k) ψ (P k)) 0).ncard := by
  have h1 := Work.Drive.Capping.ncard_topBdryMeet_zero_eq_ncard_cutBaseBox P c ψ hψ hfibV hfibW
  have h2 := ncard_cutTriples_eq_ncard_cutBaseBox (P 0) (clampedSweep (c 1) ψ (P 1))
    (clampedSweep (c 2) ψ (P 2)) hfibV hfibW
  rw [colCount, colMeet_zero_eq_cutTriples]
  rw [show diskPlane Q = P 0 from hP0.symm]
  rw [h2, ← h1]

/-! ## 2. The multiplicativity of the block `0` of the design's triple -/

/-- **The multiplicativity of the block `0`.**  For the triple of radial sweeps
`(clampedSweep (c 0) ψ (diskPlane Q), clampedSweep (c 1) ψ P₁, clampedSweep (c 2) ψ P₂)` the top count
of the first block has the parity of the product of the two side values:

> `Odd (T 0) ↔ Odd (coreSideCount Q (c 1) P₁) ∧ Odd (coreSideCount Q (c 2) P₂)`.

The cutoff is the clamp `ψ = (1 - ·)` (the shape in which `coreMeet` and `fibreMeet` are defined); the
levels `c 0, c 1, c 2` are *distinct* (only `c 1` and `c 2` enter the conclusion, and `c 0` only through
the top count). -/
theorem odd_topBdryMeet_zero_iff_coreSideCounts {β : ℝ → ℝ} {Q : ℂ → CappingSpace}
    {P₁ P₂ : EuclideanSpace ℝ (Fin 2) → CappingSpace} {c₀ c₁ c₂ : ℝ}
    (hfibV : ∀ u ∈ cutBaseBox (diskPlane Q) (clampedSweep c₁ (fun t => 1 - t) P₁)
        (clampedSweep c₂ (fun t => 1 - t) P₂),
      (cutFibreBox (diskPlane Q) (clampedSweep c₁ (fun t => 1 - t) P₁) u).ncard = 1)
    (hfibW : ∀ u ∈ cutBaseBox (diskPlane Q) (clampedSweep c₁ (fun t => 1 - t) P₁)
        (clampedSweep c₂ (fun t => 1 - t) P₂),
      (cutFibreBox (diskPlane Q) (clampedSweep c₂ (fun t => 1 - t) P₂) u).ncard = 1)
    (h1 : colCount β Q (clampedSweep c₁ (fun t => 1 - t) P₁)
        (clampedSweep c₂ (fun t => 1 - t) P₂) 1
      = (fibreMeet Q (clampedSweep c₁ (fun t => 1 - t) P₁)
          (clampedSweep c₂ (fun t => 1 - t) P₂)).ncard)
    (hfin : (coreMeet Q c₁ P₁).Finite)
    (hfind : ∀ q ∈ coreMeet Q c₁ P₁, (diamMeet Q q.1 (clampedSweep c₂ (fun t => 1 - t) P₂)).Finite)
    (hbase : ∀ y ∈ Submission.Drive.unitBox 2,
      coreLoop Q 1 ≠ clampedSweep c₁ (fun t => 1 - t) P₁ y)
    (hheven : Even (colCount β Q (clampedSweep c₁ (fun t => 1 - t) P₁)
          (clampedSweep c₂ (fun t => 1 - t) P₂) 0
        + colCount β Q (clampedSweep c₁ (fun t => 1 - t) P₁)
          (clampedSweep c₂ (fun t => 1 - t) P₂) 1))
    (hpar : ∀ t : ℝ, Odd (diamMeet Q t (clampedSweep c₂ (fun t => 1 - t) P₂)).ncard
      ↔ Odd (coreSideCount Q c₂ P₂)) :
    Odd ((topBdryMeet CappingSpace
        (fun k => clampedSweep (![c₀, c₁, c₂] k) (fun s => 1 - s)
          (![diskPlane Q, P₁, P₂] k)) 0).ncard)
      ↔ Odd (coreSideCount Q c₁ P₁) ∧ Odd (coreSideCount Q c₂ P₂) := by
  have hK0 := colCount_zero_eq_topBdryMeet_levels β Q ![c₀, c₁, c₂] (fun s => 1 - s) (by norm_num)
    ![diskPlane Q, P₁, P₂] (by simp) hfibV hfibW
  rw [← hK0]
  exact odd_ncard_of_even_colCount (clampedSweep c₂ (fun t => 1 - t) P₂)
    (N := colCount β Q (clampedSweep c₁ (fun t => 1 - t) P₁)
      (clampedSweep c₂ (fun t => 1 - t) P₂) 0) rfl h1 hfin hfind hbase hheven hpar

/-! ## 3. Reindexing the triple: the count of a block under a permutation of the chains -/

/-- **Reindexing `topBdryMeet` by a permutation of the three chains.**  Composing the triple `D` with a
permutation `τ` relabels the chains *and* the parameter coordinates, so the `k`-th block count of the
reindexed triple is the `(τ k)`-th block count of the original.  (This is what moves a designated
disk plane `P k` into the `0`-slot, so that §2 applies to the block `k` of the design's triple.) -/
lemma ncard_topBdryMeet_comp {M : Type*} [TopologicalSpace M]
    (τ : Equiv.Perm (Fin 3)) (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M) (k : Fin 3) :
    (topBdryMeet M (fun j => D (τ j)) k).ncard = (topBdryMeet M D (τ k)).ncard := by
  refine Set.ncard_congr (fun x _ => fun i => x (τ.symm i)) ?_ ?_ ?_
  · -- the reindexed point is a triple point of the original triple
    intro x hx
    obtain ⟨⟨hbox, h01, h02, hbd⟩, htop⟩ := hx
    have hgen : ∀ j : Fin 3, D (τ j) (x j) = D (τ 0) (x 0) := by
      intro j
      fin_cases j
      · rfl
      · simpa using h01.symm
      · simpa using h02.symm
    have hτk : (fun i : Fin 3 => x (τ.symm i)) (τ k) = x k := by
      simp
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · intro j
      exact hbox (τ.symm j)
    · have h0 := hgen (τ.symm 0)
      rw [Equiv.apply_symm_apply] at h0
      have h1 := hgen (τ.symm 1)
      rw [Equiv.apply_symm_apply] at h1
      show D 0 (x (τ.symm 0)) = D 1 (x (τ.symm 1))
      rw [h0, h1]
    · have h0 := hgen (τ.symm 0)
      rw [Equiv.apply_symm_apply] at h0
      have h2 := hgen (τ.symm 2)
      rw [Equiv.apply_symm_apply] at h2
      show D 0 (x (τ.symm 0)) = D 2 (x (τ.symm 2))
      rw [h0, h2]
    · rw [hτk]
      exact hbd
    · rw [hτk]
      exact htop
  · -- injectivity
    intro x₁ _ x₂ _ h
    funext j
    have := congrFun h (τ j)
    simpa using this
  · -- surjectivity
    intro y hy
    refine ⟨fun i => y (τ i), ?_, ?_⟩
    · obtain ⟨⟨hbox, h01, h02, hbd⟩, htop⟩ := hy
      have hgen : ∀ j : Fin 3, D j (y j) = D 0 (y 0) := by
        intro j
        fin_cases j
        · rfl
        · show D 1 (y 1) = D 0 (y 0)
          exact h01.symm
        · show D 2 (y 2) = D 0 (y 0)
          exact h02.symm
      refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
      · intro j
        exact hbox (τ j)
      · have h0 := hgen (τ 0)
        have h1 := hgen (τ 1)
        show D (τ 0) (y (τ 0)) = D (τ 1) (y (τ 1))
        rw [h0, h1]
      · have h0 := hgen (τ 0)
        have h2 := hgen (τ 2)
        show D (τ 0) (y (τ 0)) = D (τ 2) (y (τ 2))
        rw [h0, h2]
      · show (fun i : Fin 3 => y (τ i)) k ∈ Submission.Drive.unitBoxBdry 2
        rw [show (fun i : Fin 3 => y (τ i)) k = y (τ k) from rfl]
        exact hbd
      · show (fun i : Fin 3 => y (τ i)) k 2 = 1
        rw [show (fun i : Fin 3 => y (τ i)) k = y (τ k) from rfl]
        exact htop
    · funext i
      simp

/-! ## 4. The multiplicativity of an arbitrary block of a triple of plane presentations -/

/-- **The multiplicativity of the block `k` of a triple of plane presentations.**  Let `P : Fin 3 → ℝ² →
CappingSpace` be three plane presentations, `c : Fin 3 → ℝ` their truncation levels, and suppose that the
block `τ 0` of the permutation `τ` is a *disk plane* of a chart `Q` (`P (τ 0) = diskPlane Q`).  Then the
top count of that block of the triple of radial sweeps has the parity of the product of the two other
side values:

> `Odd (T (τ 0)) ↔ Odd (coreSideCount Q (c (τ 1)) (P (τ 1)))
>                    ∧ Odd (coreSideCount Q (c (τ 2)) (P (τ 2)))`.

For the design's triple `P k = rotPresentation Q (u k)` every `P k` *is* a disk plane
(`rotPresentation Q v = diskPlane (rotCapping v ∘ Q)`), so this covers all three blocks; the transport it
consumes is §2 above (`odd_topBdryMeet_zero_iff_coreSideCounts`, the block `0` case), and the passage
from block `0` to block `τ 0` is the reindexing `ncard_topBdryMeet_comp` of §3. -/
theorem odd_topBdryMeet_iff_coreSideCounts {β : ℝ → ℝ} {Q : ℂ → CappingSpace}
    {P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace} {c : Fin 3 → ℝ}
    {τ : Equiv.Perm (Fin 3)} (hPτ : P (τ 0) = diskPlane Q)
    (hfibV : ∀ u ∈ cutBaseBox (diskPlane Q) (clampedSweep (c (τ 1)) (fun t => 1 - t) (P (τ 1)))
        (clampedSweep (c (τ 2)) (fun t => 1 - t) (P (τ 2))),
      (cutFibreBox (diskPlane Q) (clampedSweep (c (τ 1)) (fun t => 1 - t) (P (τ 1))) u).ncard = 1)
    (hfibW : ∀ u ∈ cutBaseBox (diskPlane Q) (clampedSweep (c (τ 1)) (fun t => 1 - t) (P (τ 1)))
        (clampedSweep (c (τ 2)) (fun t => 1 - t) (P (τ 2))),
      (cutFibreBox (diskPlane Q) (clampedSweep (c (τ 2)) (fun t => 1 - t) (P (τ 2))) u).ncard = 1)
    (h1 : colCount β Q (clampedSweep (c (τ 1)) (fun t => 1 - t) (P (τ 1)))
        (clampedSweep (c (τ 2)) (fun t => 1 - t) (P (τ 2))) 1
      = (fibreMeet Q (clampedSweep (c (τ 1)) (fun t => 1 - t) (P (τ 1)))
          (clampedSweep (c (τ 2)) (fun t => 1 - t) (P (τ 2)))).ncard)
    (hfin : (coreMeet Q (c (τ 1)) (P (τ 1))).Finite)
    (hfind : ∀ q ∈ coreMeet Q (c (τ 1)) (P (τ 1)),
      (diamMeet Q q.1 (clampedSweep (c (τ 2)) (fun t => 1 - t) (P (τ 2)))).Finite)
    (hbase : ∀ y ∈ Submission.Drive.unitBox 2,
      coreLoop Q 1 ≠ clampedSweep (c (τ 1)) (fun t => 1 - t) (P (τ 1)) y)
    (hheven : Even (colCount β Q (clampedSweep (c (τ 1)) (fun t => 1 - t) (P (τ 1)))
          (clampedSweep (c (τ 2)) (fun t => 1 - t) (P (τ 2))) 0
        + colCount β Q (clampedSweep (c (τ 1)) (fun t => 1 - t) (P (τ 1)))
          (clampedSweep (c (τ 2)) (fun t => 1 - t) (P (τ 2))) 1))
    (hpar : ∀ t : ℝ, Odd (diamMeet Q t (clampedSweep (c (τ 2)) (fun t => 1 - t) (P (τ 2)))).ncard
      ↔ Odd (coreSideCount Q (c (τ 2)) (P (τ 2)))) :
    Odd ((topBdryMeet CappingSpace
        (fun j => clampedSweep (c j) (fun s => 1 - s) (P j)) (τ 0)).ncard)
      ↔ Odd (coreSideCount Q (c (τ 1)) (P (τ 1)))
        ∧ Odd (coreSideCount Q (c (τ 2)) (P (τ 2))) := by
  have hc_eq : ![c (τ 0), c (τ 1), c (τ 2)] = (fun j => c (τ j)) := by
    funext j
    fin_cases j <;> rfl
  have hP_eq : ![diskPlane Q, P (τ 1), P (τ 2)] = (fun j => P (τ j)) := by
    funext j
    fin_cases j
    · simpa using hPτ.symm
    · rfl
    · rfl
  have h := odd_topBdryMeet_zero_iff_coreSideCounts (β := β) (Q := Q) (P₁ := P (τ 1))
    (P₂ := P (τ 2)) (c₀ := c (τ 0)) (c₁ := c (τ 1)) (c₂ := c (τ 2))
    hfibV hfibW h1 hfin hfind hbase hheven hpar
  rw [hc_eq, hP_eq] at h
  rw [ncard_topBdryMeet_comp τ (fun j => clampedSweep (c j) (fun s => 1 - s) (P j)) 0] at h
  exact h

/-! ## 5. The side values of the rotated blocks, in terms of one chart

The design's triple is `P k = rotPresentation Q (u k)`, i.e. `P k = diskPlane (rotCapping (u k) ∘ Q)`: the
chart of the block `k` is the *rotated* chart `rotCapping (u k) ∘ Q`.  The identification
`Work.Drive.coreSideCount_rotCapping` (rotating the whole configuration preserves the count) turns the
block-`k` side values into side values of the single chart `Q`:

> `coreSideCount Q c (rotPresentation Q (b - a)) = coreSideCount (rotCapping a ∘ Q) c (rotPresentation Q b)`,

so the product of §4 for the block `k` reads, in the design's notation,
`T k ≡ e (u j - u k) · e (u l - u k)` with `e v := Odd (coreSideCount Q c (rotPresentation Q v))`
— the `hdense`/`hn2` correspondence of `CHAINPARITY_REDUCTION.md` §4. -/

/-- **The side value of a rotated block, in terms of the base chart.**  Rotating the chart `Q` by `a` and
the plane presentation by `b` gives the same count as the base chart `Q` with the plane rotated by
`b - a`. -/
theorem coreSideCount_rotPresentation_sub (Q : ℂ → CappingSpace) (c : ℝ)
    (a b : UnitAddCircle) :
    coreSideCount Q c (rotPresentation Q (b - a))
      = coreSideCount (fun z => rotCapping a (Q z)) c (rotPresentation Q b) := by
  rw [coreSideCount_rotCapping Q c (rotPresentation Q (b - a)) a]
  congr 1
  funext y
  show rotCapping a (rotCapping (b - a) (Q (sqDisk (foldBox y))))
    = rotCapping b (Q (sqDisk (foldBox y)))
  have h := congrFun (rotCapping_add a (b - a)) (Q (sqDisk (foldBox y)))
  rw [add_sub_cancel] at h
  exact h.symm

/-! ## 6. The `ZMod 2` form of the multiplicativity (the input of the triple bookkeeping)

`Submission/Work/Drive/orderFromTripleCount.lean` already contains the *algebraic* bookkeeping of
Hugelmeyer's Lemmas 3–4: from the triple identity `n P Q R + n Q R P + n R P Q = 1` (the engine's
output `Work.Drive.odd_sum_topBdryMeet_clampedSweeps_of_planes`, read in `ZMod 2`) and the three
**multiplicativities** `n P Q R = κ P Q · κ P R` it derives antisymmetry and transitivity of `κ`.  This
section supplies those multiplicativities in `ZMod 2` form from §4: the side value is

> `sideVal Q c P := if Odd (coreSideCount Q c P) then 1 else 0`,

and §4 says `Odd (T (τ 0)) ↔ Odd ε₁ ∧ Odd ε₂`, whence `(T (τ 0) : ZMod 2) = sideVal Q (c (τ 1)) (P (τ 1)) *
sideVal Q (c (τ 2)) (P (τ 2))`. -/

/-- In `ZMod 2` the value of a natural number is determined by its residue mod `2`. -/
lemma zmod2_natCast_eq_mod (n : ℕ) : ((n : ZMod 2)) = ((n % 2 : ℕ) : ZMod 2) := by
  nth_rewrite 1 [← Nat.div_add_mod n 2]
  push_cast
  have h2 : (2 : ZMod 2) = 0 := by decide
  rw [h2, zero_mul, zero_add]

/-- In `ZMod 2` a natural number is `1` exactly when it is odd. -/
lemma zmod2_natCast_eq_one_iff_odd (n : ℕ) : ((n : ZMod 2) = 1) ↔ Odd n := by
  rw [zmod2_natCast_eq_mod]
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · rw [h]
    simp [Nat.odd_iff, h]
  · rw [h]
    simp [Nat.odd_iff, h]

/-- The `ZMod 2` value of a natural number is its parity indicator. -/
lemma zmod2_natCast_eq_ite_odd (n : ℕ) : ((n : ZMod 2)) = if Odd n then (1 : ZMod 2) else 0 := by
  by_cases h : Odd n
  · rw [if_pos h]
    exact (zmod2_natCast_eq_one_iff_odd n).mpr h
  · rw [if_neg h, zmod2_natCast_eq_mod, Nat.even_iff.mp (Nat.not_odd_iff_even.mp h)]
    rfl

/-- **The side value** of a plane presentation against a chart: the parity of the loop-vs-sweep count,
as an element of `ZMod 2`. -/
def sideVal (Q : ℂ → CappingSpace) (c : ℝ)
    (P : EuclideanSpace ℝ (Fin 2) → CappingSpace) : ZMod 2 :=
  if Odd (coreSideCount Q c P) then 1 else 0

@[simp] lemma sideVal_eq_ite (Q : ℂ → CappingSpace) (c : ℝ)
    (P : EuclideanSpace ℝ (Fin 2) → CappingSpace) :
    sideVal Q c P = if Odd (coreSideCount Q c P) then 1 else 0 := rfl

/-- **The multiplicativity of the block `τ 0` in the `ZMod 2` form** consumed by the triple
bookkeeping `Work.Drive.orderFromTripleCount`: the top count of the block is the product of the two
side values. -/
theorem topBdryMeet_zmod2_eq_mul {β : ℝ → ℝ} {Q : ℂ → CappingSpace}
    {P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace} {c : Fin 3 → ℝ}
    {τ : Equiv.Perm (Fin 3)} (hPτ : P (τ 0) = diskPlane Q)
    (hfibV : ∀ u ∈ cutBaseBox (diskPlane Q) (clampedSweep (c (τ 1)) (fun t => 1 - t) (P (τ 1)))
        (clampedSweep (c (τ 2)) (fun t => 1 - t) (P (τ 2))),
      (cutFibreBox (diskPlane Q) (clampedSweep (c (τ 1)) (fun t => 1 - t) (P (τ 1))) u).ncard = 1)
    (hfibW : ∀ u ∈ cutBaseBox (diskPlane Q) (clampedSweep (c (τ 1)) (fun t => 1 - t) (P (τ 1)))
        (clampedSweep (c (τ 2)) (fun t => 1 - t) (P (τ 2))),
      (cutFibreBox (diskPlane Q) (clampedSweep (c (τ 2)) (fun t => 1 - t) (P (τ 2))) u).ncard = 1)
    (h1 : colCount β Q (clampedSweep (c (τ 1)) (fun t => 1 - t) (P (τ 1)))
        (clampedSweep (c (τ 2)) (fun t => 1 - t) (P (τ 2))) 1
      = (fibreMeet Q (clampedSweep (c (τ 1)) (fun t => 1 - t) (P (τ 1)))
          (clampedSweep (c (τ 2)) (fun t => 1 - t) (P (τ 2)))).ncard)
    (hfin : (coreMeet Q (c (τ 1)) (P (τ 1))).Finite)
    (hfind : ∀ q ∈ coreMeet Q (c (τ 1)) (P (τ 1)),
      (diamMeet Q q.1 (clampedSweep (c (τ 2)) (fun t => 1 - t) (P (τ 2)))).Finite)
    (hbase : ∀ y ∈ Submission.Drive.unitBox 2,
      coreLoop Q 1 ≠ clampedSweep (c (τ 1)) (fun t => 1 - t) (P (τ 1)) y)
    (hheven : Even (colCount β Q (clampedSweep (c (τ 1)) (fun t => 1 - t) (P (τ 1)))
          (clampedSweep (c (τ 2)) (fun t => 1 - t) (P (τ 2))) 0
        + colCount β Q (clampedSweep (c (τ 1)) (fun t => 1 - t) (P (τ 1)))
          (clampedSweep (c (τ 2)) (fun t => 1 - t) (P (τ 2))) 1))
    (hpar : ∀ t : ℝ, Odd (diamMeet Q t (clampedSweep (c (τ 2)) (fun t => 1 - t) (P (τ 2)))).ncard
      ↔ Odd (coreSideCount Q (c (τ 2)) (P (τ 2)))) :
    (((topBdryMeet CappingSpace
        (fun j => clampedSweep (c j) (fun s => 1 - s) (P j)) (τ 0)).ncard : ℕ) : ZMod 2)
      = sideVal Q (c (τ 1)) (P (τ 1)) * sideVal Q (c (τ 2)) (P (τ 2)) := by
  have hparity := odd_topBdryMeet_iff_coreSideCounts hPτ hfibV hfibW h1 hfin hfind hbase hheven hpar
  rw [zmod2_natCast_eq_ite_odd, sideVal_eq_ite, sideVal_eq_ite]
  by_cases h1' : Odd (coreSideCount Q (c (τ 1)) (P (τ 1)))
  · by_cases h2' : Odd (coreSideCount Q (c (τ 2)) (P (τ 2)))
    · rw [if_pos h1', if_pos h2', if_pos (hparity.mpr ⟨h1', h2'⟩), mul_one]
    · rw [if_pos h1', if_neg h2', if_neg (fun hh => h2' (hparity.mp hh).2), mul_zero]
  · by_cases h2' : Odd (coreSideCount Q (c (τ 2)) (P (τ 2)))
    · rw [if_neg h1', if_pos h2', if_neg (fun hh => h1' (hparity.mp hh).1), zero_mul]
    · rw [if_neg h1', if_neg h2', if_neg (fun hh => h1' (hparity.mp hh).1), zero_mul]

end

end Work.Drive
