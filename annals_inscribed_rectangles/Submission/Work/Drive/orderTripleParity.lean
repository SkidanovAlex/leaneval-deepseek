import Mathlib
import Submission.Work.Drive.even_sum_topBdryMeet_add_bottomBdryMeet
import Submission.Work.Drive.classTripleRegular
import Submission.Work.Drive.odd_sum_bottomBdryMeet_of_classTriple
import Submission.Work.Drive.tripleMultiplicativity

/-!
# The top counts of the design's triple are odd (the settlement of §6bis)

`SWEEP_TRIPLE_GENERIC_STATUS.md` §6bis left one bookkeeping question open: the engine's output for the
design's triple reads `Even (Σ_k (top_k + bottom_k))` and the face avoidance
(`Work.Drive.tripleBdryMeet_subset_seamBdryMeet`) shows that only `bottom_0` can be nonzero, so
`Odd (Σ_k top_k) ↔ Odd (bottom_0)` — but *identifying* `bottom_0` with a product of side counts (as the
transport does for the tops) would make the identity vacuous (`2 · Σ products ≡ 0`).

**The settlement**: `bottom_0` is NOT identified by the transport at all.  It is the *end contribution*
`n_{-λ}` of Hugelmeyer's four-face count, and its parity is supplied by the **ends clause**
`Work.Drive.odd_sum_bottomBdryMeet_of_classTriple`
(resp. `Work.Drive.odd_sum_bottomBdryMeet_of_hasClassLinearization`), which computes
`Odd (Σ_k bottom_k)` from the oddness of the class-triple count.  With the engine this gives

> `Odd (Σ_k top_k)`,

and then the transport's multiplicativity T6 (`Work.Drive.topBdryMeet_zmod2_eq_mul`) converts it into
the design's functional identity `Σ_k ε_j ε_l = 1` — Hugelmeyer's Lemma 4 in the design's shape (the
`hdense`/`hn2` input of `Work.Drive.parityCore_of_sideGerm` / `Work.Drive.parityCore_of_designCount`).

This file contains the parity step itself (`odd_of_even_add_odd` + the two assembly lemmas) and its
`ZMod 2` form; it is the "step 3" of `SWEEP_TRIPLE_GENERIC_STATUS.md` §6 whose missing half was exactly
the question of §6bis.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace

noncomputable section

/-! ## 1. The parity step -/

/-- **The parity step of §6bis**: `Even (a + b)` and `Odd b` give `Odd a`.  (The mirror of
`Work.Drive.odd_of_odd_add_even`, which is the direction `Even (a+b) → Odd a → Odd b`.) -/
theorem odd_of_even_add_odd {a b : ℕ} (h : Even (a + b)) (hb : Odd b) : Odd a := by
  obtain ⟨k, hk⟩ := h
  obtain ⟨l, hl⟩ := hb
  exact ⟨k - l - 1, by omega⟩

/-- **The engine plus the ends clause give the oddness of the total top count.**  For any triple of
`3`-chains `D` of a smooth `4`-manifold satisfying the engine's hypotheses (`Meet3Hyp` and the
seam/slice separation `hdisj`), if the total *end* contribution `Σ_k bottom_k` is odd — which is the
ends clause `Work.Drive.odd_sum_bottomBdryMeet_of_classTriple` — then the total *top* count
`Σ_k top_k` is odd.

This is the parity form of Hugelmeyer's Lemma 4 at the chain level: the only input beyond the engine is
the parity of the end contribution, and the end contribution is a single level-face count. -/
theorem odd_sum_topBdryMeet_of_ends {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M) (h : Work.Drive.Meet3Hyp M D)
    (hdisj : ∀ (k : Fin 3) (x : Fin 3 → EuclideanSpace ℝ (Fin 3)),
      x ∈ Work.Drive.tripleBdryMeet M D k →
      ¬ (Work.Drive.onSeam (x k) ∧ (x k 2 = 0 ∨ x k 2 = 1)))
    (hbot : Odd ((Work.Drive.bottomBdryMeet M D 0).ncard
      + (Work.Drive.bottomBdryMeet M D 1).ncard + (Work.Drive.bottomBdryMeet M D 2).ncard)) :
    Odd ((Work.Drive.topBdryMeet M D 0).ncard
      + (Work.Drive.topBdryMeet M D 1).ncard + (Work.Drive.topBdryMeet M D 2).ncard) := by
  have hengine := Work.Drive.even_sum_topBdryMeet_add_bottomBdryMeet M D h hdisj
  -- rearrange the engine's sum into `(Σ top) + (Σ bottom)`
  have hrearr : ((Work.Drive.topBdryMeet M D 0).ncard
        + (Work.Drive.bottomBdryMeet M D 0).ncard
        + ((Work.Drive.topBdryMeet M D 1).ncard
          + (Work.Drive.bottomBdryMeet M D 1).ncard)
        + ((Work.Drive.topBdryMeet M D 2).ncard
          + (Work.Drive.bottomBdryMeet M D 2).ncard))
      = ((Work.Drive.topBdryMeet M D 0).ncard + (Work.Drive.topBdryMeet M D 1).ncard
          + (Work.Drive.topBdryMeet M D 2).ncard)
        + ((Work.Drive.bottomBdryMeet M D 0).ncard + (Work.Drive.bottomBdryMeet M D 1).ncard
          + (Work.Drive.bottomBdryMeet M D 2).ncard) := by
    ring
  rw [hrearr] at hengine
  exact odd_of_even_add_odd hengine hbot

/-! ## 2. The design's triple: `ClassTripleRegular` + design data + the ends clause -/

/-- **The top counts of the design's triple are odd.**  For `ClassTripleRegular` plane presentations
`P`, the cutoff data `ψ` of the design, the truncation levels `c` (positive, `≤ c 0`), the level bound
`c 0 < levelOf (P k y)`, the face condition, and the ends clause (the oddness of `Σ_k bottom_k`, which
`Work.Drive.odd_sum_bottomBdryMeet_of_classTriple` derives from the odd class-triple count), the total
top count of the three radial sweeps is odd.

The hypotheses are exactly those of `Work.Drive.meet3Hyp_and_separation_of_classTripleRegular` (the
engine's `Meet3Hyp` and `hdisj`) together with the ends clause. -/
theorem odd_sum_topBdryMeet_of_classTriple
    (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace) (c : Fin 3 → ℝ) (ψ : ℝ → ℝ)
    (hreg : ClassTripleRegular P)
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (hψ' : ∀ t ∈ Set.Icc (0 : ℝ) 1, deriv ψ t ≠ 0)
    (hcpos : ∀ k : Fin 3, 0 < c k) (hck : ∀ k : Fin 3, c k ≤ c 0)
    (hlev : ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)), c 0 < levelOf (P k y))
    (hface : FaceCondition P c ψ)
    (hbot : Odd ((bottomBdryMeet CappingSpace
            (fun k => clampedSweep (c k) ψ (P k)) 0).ncard
      + (bottomBdryMeet CappingSpace
            (fun k => clampedSweep (c k) ψ (P k)) 1).ncard
      + (bottomBdryMeet CappingSpace
            (fun k => clampedSweep (c k) ψ (P k)) 2).ncard)) :
    Odd ((topBdryMeet CappingSpace
            (fun k => clampedSweep (c k) ψ (P k)) 0).ncard
      + (topBdryMeet CappingSpace
            (fun k => clampedSweep (c k) ψ (P k)) 1).ncard
      + (topBdryMeet CappingSpace
            (fun k => clampedSweep (c k) ψ (P k)) 2).ncard) := by
  obtain ⟨hhyp, hdisj⟩ := meet3Hyp_and_separation_of_classTripleRegular P c ψ hreg hψ hψ' hcpos hck
    hlev hface
  exact odd_sum_topBdryMeet_of_ends _ hhyp hdisj hbot

/-! ## 3. The `ZMod 2` form: the input of the multiplicativity T6 -/

/-- **The parity of a sum of three naturals, in `ZMod 2`.** -/
theorem zmod2_sum_three_eq_one_of_odd (f : Fin 3 → ℕ) (h : Odd (f 0 + f 1 + f 2)) :
    ((f 0 : ℕ) : ZMod 2) + ((f 1 : ℕ) : ZMod 2) + ((f 2 : ℕ) : ZMod 2) = 1 := by
  have h2 : (((f 0 + f 1 + f 2 : ℕ)) : ZMod 2) = 1 :=
    zmod2_natCast_eq_one_iff_odd (f 0 + f 1 + f 2) |>.mpr h
  push_cast at h2 ⊢
  linear_combination h2

/-- **The design's functional identity's left-hand side is `1` in `ZMod 2`**: the top counts of the
three blocks of the design's triple sum to `1` mod `2`.  With the multiplicativity
`Work.Drive.topBdryMeet_zmod2_eq_mul` (one instance per block), this is Hugelmeyer's Lemma 4 in the
form the design's `hdense` consumes:

> `Σ_k ε (P_j; chart P_k) · ε (P_l; chart P_k) = 1`. -/
theorem sum_topBdryMeet_zmod2_eq_one_of_classTriple
    (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace) (c : Fin 3 → ℝ) (ψ : ℝ → ℝ)
    (hreg : ClassTripleRegular P)
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (hψ' : ∀ t ∈ Set.Icc (0 : ℝ) 1, deriv ψ t ≠ 0)
    (hcpos : ∀ k : Fin 3, 0 < c k) (hck : ∀ k : Fin 3, c k ≤ c 0)
    (hlev : ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)), c 0 < levelOf (P k y))
    (hface : FaceCondition P c ψ)
    (hbot : Odd ((bottomBdryMeet CappingSpace
            (fun k => clampedSweep (c k) ψ (P k)) 0).ncard
      + (bottomBdryMeet CappingSpace
            (fun k => clampedSweep (c k) ψ (P k)) 1).ncard
      + (bottomBdryMeet CappingSpace
            (fun k => clampedSweep (c k) ψ (P k)) 2).ncard)) :
    ((topBdryMeet CappingSpace (fun k => clampedSweep (c k) ψ (P k)) 0).ncard : ZMod 2)
      + ((topBdryMeet CappingSpace (fun k => clampedSweep (c k) ψ (P k)) 1).ncard : ZMod 2)
      + ((topBdryMeet CappingSpace (fun k => clampedSweep (c k) ψ (P k)) 2).ncard : ZMod 2) = 1 :=
  zmod2_sum_three_eq_one_of_odd
    (fun k => (topBdryMeet CappingSpace (fun j => clampedSweep (c j) ψ (P j)) k).ncard)
    (odd_sum_topBdryMeet_of_classTriple P c ψ hreg hψ hψ' hcpos hck hlev hface hbot)

end

end Work.Drive
