import Mathlib
import Submission.Work.Drive.orderTripleParity
import Submission.Work.Drive.transportBlock

/-!
# The design's functional identity from the block multiplicativities (step 3 of §6)

`SWEEP_TRIPLE_GENERIC_STATUS.md` §6 records the chain from the triple genericity to the design's
`hdense`/`hn2`.  Its three mathematical inputs are

1. **the engine + the ends clause** `⟹ Odd (Σ_k top_k)` — `orderTripleParity.lean`;
2. **the multiplicativity T6** per block — `Work.Drive.odd_coreSideCount_mul_of_block`
   (`transportBlock.lean`), which computes the `k`-th top count as a product of *two* side counts at
   the two truncation levels `cblk (k+1)`, `cblk (k+2)` of the two swept planes;
3. **the level transfer** — `Work.Drive.odd_coreSideCount_eq_of_lt_level` (`germLevelBridge.lean`),
   which identifies those two side counts with the design's *single* side function
   `e x = sideVal Q c (rotPresentation Q x)` at the fixed level `c` (all truncation levels lie below
   the levels of the chart, so the count does not see them).

This file performs the assembly: from `Odd (Σ_k top_k)`, the three block multiplicativities and the
level transfer, it derives the design's functional identity

> `e (u 1 - u 0) · e (u 2 - u 0) + e (u 0 - u 1) · e (u 2 - u 1) + e (u 0 - u 2) · e (u 1 - u 2) = 1`

for the triple of angles `u : Fin 3 → UnitAddCircle` — i.e. Hugelmeyer's Lemma 4 in the shape in which
`Work.Drive.parityCore_of_sideGerm`/`Work.Drive.parityCore_of_designCount` state `hdense`, once the two
remaining bridges (`Work.Drive.sideGerm_eq_sideVal_of_good` for the germ version, and the rotation
invariance `Work.Drive.coreSideCount_rotPresentation_sub` for the angle differences) are applied by the
caller.

The statement is deliberately *modular*: the three heavy geometric inputs (the engine's `Meet3Hyp`, the
ends clause, and the transport's T6 data) enter only through the two hypotheses `htop` and `hT6`, so the
file is independent of the design's genericity lane and of the germ lane.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff Topology

noncomputable section

/-- **The `ZMod 2` product from the multiplicativity's `Odd`-form.**  If the oddness of `n` is
equivalent to the oddness of both `a` and `b`, then the `ZMod 2` value of `n` is the product of those of
`a` and `b`. -/
theorem zmod2_natCast_eq_mul_of_odd_iff {n a b : ℕ} (h : Odd n ↔ (Odd a ∧ Odd b)) :
    ((n : ℕ) : ZMod 2) = ((a : ℕ) : ZMod 2) * ((b : ℕ) : ZMod 2) := by
  rw [zmod2_natCast_eq_ite_odd, zmod2_natCast_eq_ite_odd, zmod2_natCast_eq_ite_odd]
  by_cases ha : Odd a
  · by_cases hb : Odd b
    · rw [if_pos ha, if_pos hb, if_pos (h.mpr ⟨ha, hb⟩), mul_one]
    · rw [if_pos ha, if_neg hb, if_neg (fun hh => hb (h.mp hh).2), mul_zero]
  · by_cases hb : Odd b
    · rw [if_neg ha, if_pos hb, if_neg (fun hh => ha (h.mp hh).1), zero_mul]
    · rw [if_neg ha, if_neg hb, if_neg (fun hh => ha (h.mp hh).1), zero_mul]

/-- **The design's functional identity, from the oddness of the total top count and the block
multiplicativities.**

* `htop`: the total top count of the design's triple (the three radial sweeps of the rotated planes at
  the angles `u j`, truncated at the levels `cblk j`) is odd — the output of the engine plus the ends
  clause (`Work.Drive.odd_sum_topBdryMeet_of_classTriple`);
* `hT6`: the block multiplicativity, in the form of the transport's
  `Work.Drive.odd_coreSideCount_mul_of_block`: the `k`-th top count is odd exactly when the two base
  side counts at the levels `cblk (k+1)`, `cblk (k+2)` and the angle differences
  `u (k+1) - u k`, `u (k+2) - u k` are odd;
* `hlevind`: the level transfer: the side count at each truncation level `cblk j` has the same parity
  as the side count at the design's fixed level `c`
  (`Work.Drive.odd_coreSideCount_eq_of_lt_level`).

The conclusion is Hugelmeyer's Lemma 4 at the triple `(0, u 1, u 2)` in the shape consumed by
`Work.Drive.hdense_sideGerm_of_good_identity` (after the germ bridge) and by
`Work.Drive.parityCore_of_designCount`. -/
theorem sum_sideVal_mul_eq_one_of_odd_top
    (Q : ℂ → CappingSpace) (u : Fin 3 → UnitAddCircle) (cblk : Fin 3 → ℝ) (c : ℝ)
    (htop : Odd ((topBdryMeet CappingSpace (fun j =>
          clampedSweep (cblk j) (fun t => 1 - t) (rotPresentation Q (u j))) 0).ncard
      + (topBdryMeet CappingSpace (fun j =>
          clampedSweep (cblk j) (fun t => 1 - t) (rotPresentation Q (u j))) 1).ncard
      + (topBdryMeet CappingSpace (fun j =>
          clampedSweep (cblk j) (fun t => 1 - t) (rotPresentation Q (u j))) 2).ncard))
    (hT6 : ∀ k : Fin 3, Odd ((topBdryMeet CappingSpace (fun j =>
          clampedSweep (cblk j) (fun t => 1 - t) (rotPresentation Q (u j))) k).ncard) ↔
      (Odd (coreSideCount Q (cblk (k + 1)) (rotPresentation Q (u (k + 1) - u k)))
        ∧ Odd (coreSideCount Q (cblk (k + 2)) (rotPresentation Q (u (k + 2) - u k)))))
    (hlevind : ∀ (j : Fin 3) (x : UnitAddCircle),
      Odd (coreSideCount Q (cblk j) (rotPresentation Q x))
        ↔ Odd (coreSideCount Q c (rotPresentation Q x))) :
    sideVal Q c (rotPresentation Q (u (0 + 1) - u 0))
        * sideVal Q c (rotPresentation Q (u (0 + 2) - u 0))
      + sideVal Q c (rotPresentation Q (u (1 + 1) - u 1))
        * sideVal Q c (rotPresentation Q (u (1 + 2) - u 1))
      + sideVal Q c (rotPresentation Q (u (2 + 1) - u 2))
        * sideVal Q c (rotPresentation Q (u (2 + 2) - u 2)) = 1 := by
  -- the block multiplicativity in `ZMod 2` form, at the design's fixed level `c`
  have hblock : ∀ k : Fin 3,
      (((topBdryMeet CappingSpace (fun j =>
        clampedSweep (cblk j) (fun t => 1 - t) (rotPresentation Q (u j))) k).ncard : ℕ) : ZMod 2)
        = sideVal Q c (rotPresentation Q (u (k + 1) - u k))
          * sideVal Q c (rotPresentation Q (u (k + 2) - u k)) := by
    intro k
    have h2 := zmod2_natCast_eq_mul_of_odd_iff (hT6 k)
    rw [h2, zmod2_natCast_eq_ite_odd, zmod2_natCast_eq_ite_odd, sideVal_eq_ite, sideVal_eq_ite]
    by_cases h1 : Odd (coreSideCount Q (cblk (k + 1)) (rotPresentation Q (u (k + 1) - u k)))
    · by_cases h1' : Odd (coreSideCount Q (cblk (k + 2)) (rotPresentation Q (u (k + 2) - u k)))
      · rw [if_pos h1, if_pos h1', if_pos ((hlevind (k + 1) _).mp h1),
          if_pos ((hlevind (k + 2) _).mp h1')]
      · rw [if_pos h1, if_neg h1', if_pos ((hlevind (k + 1) _).mp h1),
          if_neg (fun hh => h1' ((hlevind (k + 2) _).mpr hh))]
    · by_cases h1' : Odd (coreSideCount Q (cblk (k + 2)) (rotPresentation Q (u (k + 2) - u k)))
      · rw [if_neg h1, if_pos h1', if_neg (fun hh => h1 ((hlevind (k + 1) _).mpr hh)),
          if_pos ((hlevind (k + 2) _).mp h1')]
      · rw [if_neg h1, if_neg h1', if_neg (fun hh => h1 ((hlevind (k + 1) _).mpr hh)),
          if_neg (fun hh => h1' ((hlevind (k + 2) _).mpr hh))]
  have hsum : (((topBdryMeet CappingSpace (fun j =>
        clampedSweep (cblk j) (fun t => 1 - t) (rotPresentation Q (u j))) 0).ncard : ℕ) : ZMod 2)
      + (((topBdryMeet CappingSpace (fun j =>
        clampedSweep (cblk j) (fun t => 1 - t) (rotPresentation Q (u j))) 1).ncard : ℕ) : ZMod 2)
      + (((topBdryMeet CappingSpace (fun j =>
        clampedSweep (cblk j) (fun t => 1 - t) (rotPresentation Q (u j))) 2).ncard : ℕ) : ZMod 2)
      = 1 :=
    zmod2_sum_three_eq_one_of_odd
      (fun k : Fin 3 => (topBdryMeet CappingSpace (fun j =>
        clampedSweep (cblk j) (fun t => 1 - t) (rotPresentation Q (u j))) k).ncard)
      (by simpa using htop)
  rw [hblock 0, hblock 1, hblock 2] at hsum
  exact hsum

/-- **The design's functional identity at the triple of angles `(0, a, a + c')`** — the exact shape of
the `hdense` identity of `Work.Drive.parityCore_of_sideGerm`, with the side function
`e x = sideVal Q c (rotPresentation Q x)`.

The hypotheses are those of `sum_sideVal_mul_eq_one_of_odd_top` at the angles `u`, together with
`u 0 = 0`, `u 1 = a`, `u 2 = a + c'` (in the design, `u = ![0, a, a + c']`); the proof only rewrites the
six angle differences. -/
theorem sum_sideVal_mul_eq_one_of_odd_top_design
    (Q : ℂ → CappingSpace) (u : Fin 3 → UnitAddCircle) (a c' : UnitAddCircle)
    (hu0 : u 0 = 0) (hu1 : u 1 = a) (hu2 : u 2 = a + c')
    (cblk : Fin 3 → ℝ) (c : ℝ)
    (htop : Odd ((topBdryMeet CappingSpace (fun j =>
          clampedSweep (cblk j) (fun t => 1 - t) (rotPresentation Q (u j))) 0).ncard
      + (topBdryMeet CappingSpace (fun j =>
          clampedSweep (cblk j) (fun t => 1 - t) (rotPresentation Q (u j))) 1).ncard
      + (topBdryMeet CappingSpace (fun j =>
          clampedSweep (cblk j) (fun t => 1 - t) (rotPresentation Q (u j))) 2).ncard))
    (hT6 : ∀ k : Fin 3, Odd ((topBdryMeet CappingSpace (fun j =>
          clampedSweep (cblk j) (fun t => 1 - t) (rotPresentation Q (u j))) k).ncard) ↔
      (Odd (coreSideCount Q (cblk (k + 1)) (rotPresentation Q (u (k + 1) - u k)))
        ∧ Odd (coreSideCount Q (cblk (k + 2)) (rotPresentation Q (u (k + 2) - u k)))))
    (hlevind : ∀ (j : Fin 3) (x : UnitAddCircle),
      Odd (coreSideCount Q (cblk j) (rotPresentation Q x))
        ↔ Odd (coreSideCount Q c (rotPresentation Q x))) :
    sideVal Q c (rotPresentation Q a) * sideVal Q c (rotPresentation Q (a + c'))
      + sideVal Q c (rotPresentation Q (-a)) * sideVal Q c (rotPresentation Q c')
      + sideVal Q c (rotPresentation Q (-(a + c'))) * sideVal Q c (rotPresentation Q (-c')) = 1 := by
  have h := sum_sideVal_mul_eq_one_of_odd_top Q u cblk c htop hT6 hlevind
  have e01 : u (0 + 1) - u 0 = a := by
    rw [show (0 + 1 : Fin 3) = 1 from by decide, hu1, hu0]; abel
  have e02 : u (0 + 2) - u 0 = a + c' := by
    rw [show (0 + 2 : Fin 3) = 2 from by decide, hu2, hu0]; abel
  have e11 : u (1 + 1) - u 1 = c' := by
    rw [show (1 + 1 : Fin 3) = 2 from by decide, hu2, hu1]; abel
  have e12 : u (1 + 2) - u 1 = -a := by
    rw [show (1 + 2 : Fin 3) = 0 from by decide, hu0, hu1]; abel
  have e21 : u (2 + 1) - u 2 = -(a + c') := by
    rw [show (2 + 1 : Fin 3) = 0 from by decide, hu0, hu2]; abel
  have e22 : u (2 + 2) - u 2 = -c' := by
    rw [show (2 + 2 : Fin 3) = 1 from by decide, hu1, hu2]; abel
  rw [e01, e02, e11, e12, e21, e22] at h
  rw [← mul_comm (sideVal Q c (rotPresentation Q (-a))) (sideVal Q c (rotPresentation Q c'))] at h
  exact h

/-! ## 3. The per-block multiplicativity in the design's own vocabulary -/

/-- **The block multiplicativity `hT6` of `sum_sideVal_mul_eq_one_of_odd_top` from the transport's
per-block input.**

The hypothesis `hblock k` is the conclusion of the transport's block-`0` multiplicativity
`Work.Drive.odd_topBdryMeet_zero_iff_coreSideCounts`
(`tripleMultiplicativity.lean`) at the chart `rotCapping (u k) ∘ Q` of the block `k`, with the two
swept planes `rotPresentation Q (u (k+1))`, `rotPresentation Q (u (k+2))` and the two truncation levels
`cblk (k+1)`, `cblk (k+2)` — i.e. the `0`-th block statement for the triple relabelled so that the
block `k` comes first.  (Note that `diskPlane (fun z => rotCapping (u k) (Q z))` is
`rotPresentation Q (u k)` by definition, so the T6 instance can be passed verbatim.)

The conclusion is the `hT6` shape consumed by `sum_sideVal_mul_eq_one_of_odd_top`: the same statement
for the design's triple, in the base chart `Q` and at the *angle differences* `u (k+1) - u k`,
`u (k+2) - u k` (`Work.Drive.odd_coreSideCount_mul_of_block`). -/
theorem hT6_design_of_blockT6
    (Q : ℂ → CappingSpace) (u : Fin 3 → UnitAddCircle) (cblk : Fin 3 → ℝ)
    (hblock : ∀ k : Fin 3,
      Odd (topBdryMeet CappingSpace (fun i => clampedSweep
            (![cblk k, cblk (k + 1), cblk (k + 2)] i) (fun t => 1 - t)
            (![rotPresentation Q (u k), rotPresentation Q (u (k + 1)),
              rotPresentation Q (u (k + 2))] i)) 0).ncard ↔
        (Odd (coreSideCount (fun z => rotCapping (u k) (Q z)) (cblk (k + 1))
            (rotPresentation Q (u (k + 1))))
          ∧ Odd (coreSideCount (fun z => rotCapping (u k) (Q z)) (cblk (k + 2))
            (rotPresentation Q (u (k + 2)))))) :
    ∀ k : Fin 3, Odd (topBdryMeet CappingSpace (fun j => clampedSweep (cblk j) (fun t => 1 - t)
          (rotPresentation Q (u j))) k).ncard ↔
      (Odd (coreSideCount Q (cblk (k + 1)) (rotPresentation Q (u (k + 1) - u k)))
        ∧ Odd (coreSideCount Q (cblk (k + 2)) (rotPresentation Q (u (k + 2) - u k)))) := by
  intro k
  have h := hblock k
  have hfun : (fun i : Fin 3 => clampedSweep
        (![cblk k, cblk (k + 1), cblk (k + 2)] i) (fun t => 1 - t)
        (![rotPresentation Q (u k), rotPresentation Q (u (k + 1)),
          rotPresentation Q (u (k + 2))] i))
      = fun i : Fin 3 => clampedSweep (cblk (k + i)) (fun t => 1 - t)
          (rotPresentation Q (u (k + i))) := by
    funext i
    fin_cases i <;> simp
  rw [hfun] at h
  exact odd_coreSideCount_mul_of_block Q u cblk k h

/-! ## 4. The end-to-end form: the design's identity from the engine/ends clause and the transport -/

/-- **The design's functional identity, end to end.**  From

* `htop`: the oddness of the total top count of the design's triple (the engine plus the ends clause,
  `Work.Drive.odd_sum_topBdryMeet_of_classTriple`);
* `hblock`: the transport's per-block multiplicativity of the block `k` in the chart `rotCapping (u k)`
  (`Work.Drive.odd_topBdryMeet_zero_iff_coreSideCounts`);
* `hlevind`: the level transfer (`Work.Drive.odd_coreSideCount_eq_of_lt_level`) to the design's fixed
  level `c`;

the design's side function `e x = sideVal Q c (rotPresentation Q x)` satisfies Hugelmeyer's functional
identity `e (u 1 - u 0) · e (u 2 - u 0) + e (u 0 - u 1) · e (u 2 - u 1) + e (u 0 - u 2) · e (u 1 - u 2) = 1`. -/
theorem sum_sideVal_mul_eq_one_of_blockT6
    (Q : ℂ → CappingSpace) (u : Fin 3 → UnitAddCircle) (cblk : Fin 3 → ℝ) (c : ℝ)
    (htop : Odd ((topBdryMeet CappingSpace (fun j =>
          clampedSweep (cblk j) (fun t => 1 - t) (rotPresentation Q (u j))) 0).ncard
      + (topBdryMeet CappingSpace (fun j =>
          clampedSweep (cblk j) (fun t => 1 - t) (rotPresentation Q (u j))) 1).ncard
      + (topBdryMeet CappingSpace (fun j =>
          clampedSweep (cblk j) (fun t => 1 - t) (rotPresentation Q (u j))) 2).ncard))
    (hblock : ∀ k : Fin 3,
      Odd (topBdryMeet CappingSpace (fun i => clampedSweep
            (![cblk k, cblk (k + 1), cblk (k + 2)] i) (fun t => 1 - t)
            (![rotPresentation Q (u k), rotPresentation Q (u (k + 1)),
              rotPresentation Q (u (k + 2))] i)) 0).ncard ↔
        (Odd (coreSideCount (fun z => rotCapping (u k) (Q z)) (cblk (k + 1))
            (rotPresentation Q (u (k + 1))))
          ∧ Odd (coreSideCount (fun z => rotCapping (u k) (Q z)) (cblk (k + 2))
            (rotPresentation Q (u (k + 2))))))
    (hlevind : ∀ (j : Fin 3) (x : UnitAddCircle),
      Odd (coreSideCount Q (cblk j) (rotPresentation Q x))
        ↔ Odd (coreSideCount Q c (rotPresentation Q x))) :
    sideVal Q c (rotPresentation Q (u (0 + 1) - u 0))
        * sideVal Q c (rotPresentation Q (u (0 + 2) - u 0))
      + sideVal Q c (rotPresentation Q (u (1 + 1) - u 1))
        * sideVal Q c (rotPresentation Q (u (1 + 2) - u 1))
      + sideVal Q c (rotPresentation Q (u (2 + 1) - u 2))
        * sideVal Q c (rotPresentation Q (u (2 + 2) - u 2)) = 1 :=
  sum_sideVal_mul_eq_one_of_odd_top Q u cblk c htop
    (hT6_design_of_blockT6 Q u cblk hblock) hlevind

/-- **The design's identity at the triple `(0, a, a + c')`, end to end** — the literal `hdense` shape
(with `sideVal` in place of `sideGerm`; the germ bridge is
`Work.Drive.sideGerm_eq_sideVal_of_good`). -/
theorem sum_sideVal_mul_eq_one_of_blockT6_design
    (Q : ℂ → CappingSpace) (u : Fin 3 → UnitAddCircle) (a c' : UnitAddCircle)
    (hu0 : u 0 = 0) (hu1 : u 1 = a) (hu2 : u 2 = a + c')
    (cblk : Fin 3 → ℝ) (c : ℝ)
    (htop : Odd ((topBdryMeet CappingSpace (fun j =>
          clampedSweep (cblk j) (fun t => 1 - t) (rotPresentation Q (u j))) 0).ncard
      + (topBdryMeet CappingSpace (fun j =>
          clampedSweep (cblk j) (fun t => 1 - t) (rotPresentation Q (u j))) 1).ncard
      + (topBdryMeet CappingSpace (fun j =>
          clampedSweep (cblk j) (fun t => 1 - t) (rotPresentation Q (u j))) 2).ncard))
    (hblock : ∀ k : Fin 3,
      Odd (topBdryMeet CappingSpace (fun i => clampedSweep
            (![cblk k, cblk (k + 1), cblk (k + 2)] i) (fun t => 1 - t)
            (![rotPresentation Q (u k), rotPresentation Q (u (k + 1)),
              rotPresentation Q (u (k + 2))] i)) 0).ncard ↔
        (Odd (coreSideCount (fun z => rotCapping (u k) (Q z)) (cblk (k + 1))
            (rotPresentation Q (u (k + 1))))
          ∧ Odd (coreSideCount (fun z => rotCapping (u k) (Q z)) (cblk (k + 2))
            (rotPresentation Q (u (k + 2))))))
    (hlevind : ∀ (j : Fin 3) (x : UnitAddCircle),
      Odd (coreSideCount Q (cblk j) (rotPresentation Q x))
        ↔ Odd (coreSideCount Q c (rotPresentation Q x))) :
    sideVal Q c (rotPresentation Q a) * sideVal Q c (rotPresentation Q (a + c'))
      + sideVal Q c (rotPresentation Q (-a)) * sideVal Q c (rotPresentation Q c')
      + sideVal Q c (rotPresentation Q (-(a + c'))) * sideVal Q c (rotPresentation Q (-c')) = 1 :=
  sum_sideVal_mul_eq_one_of_odd_top_design Q u a c' hu0 hu1 hu2 cblk c htop
    (hT6_design_of_blockT6 Q u cblk hblock) hlevind

end

end Work.Drive
