import Mathlib
import Submission.Work.OROneRel.twoLetterTlDefs
import Submission.Work.OROneRel.winBasisDefs
import Submission.Work.OROneRel.decor_tlU_tlW_at
import Submission.Work.OROneRel.coedgeBase
import Submission.Work.OROneRel.coverCoedgeDev

/-!
# The global gauge of the two-letter level graph

For `c = tlW p q` (`a ↦ q`, `b ↦ -p`) and a *band* gauge `Wt` (`Wt 0 = 1`, `cohom c (Wt i) = ofAdd i`
for all `i`, and `htree`: the walk of `Wt i` for `i ∈ [0, pq]` runs through edges of the band whose
loop class vanishes), we extend `Wt` to a gauge on *all* of `ℤ` by two `a`-chains:

* above the band (`i > pq`), climb the `a`-edges: `level(i) = level(i - q) * a`, anchored at the band
  (the recursion stops at the last level `≤ pq`, which lies in `(pq - q, pq]`);
* below the band (`i < 0`), descend: `level(i) = level(i + q) * a⁻¹`, anchored at the first level
  `≥ 0`, which lies in `[0, q)`.

Every edge traversed by the chains is an `a`-edge `(0,i)` with `i < 0` or `i > pq - q`, and by
construction those edges have trivial loop class (`gaugeExt_aedge`): this is what lets the window
chain of `Submission/Work/OROneRel/levelChain.lean` run with the *actual* tree of the gauge instead
of a prescribed one (see `Submission/Work/OROneRel/NOTES_twoLetter_freiheitssatz_chain.md`).

The last section records the two *last-letter* facts about the band gauge that make the chains
reduced: for `w ∈ (pq - q, pq]` the last letter of `wordOf (Wt w)` is not `a⁻¹`, and for `w < q` it
is not `a`.  Both follow from `htree`, because the last step of the walk of a band gauge word
traverses a *band* edge.
-/

namespace Work.OROneRel

noncomputable section

/-- The right end of the band: `pq`. -/
abbrev npq (p q : ℕ) : ℤ := (p : ℤ) * (q : ℤ)

/-! ## The two chains -/

/-- **The gauge word above the band**: at every level `i > pq`, climb the `a`-edges from the band.
The recursion stops as soon as the level has come back into the band, i.e. at the last level
`≤ pq`, which lies in `(pq - q, pq]`. -/
def gPosL (p q : ℕ) (hq : 1 ≤ q) (Wt : ℤ → FreeGroup (Fin 2)) : ℤ → List (Fin 2 × Bool)
  | i => (if i - (q : ℤ) ≤ npq p q then wordOf (Wt (i - (q : ℤ)))
          else gPosL p q hq Wt (i - (q : ℤ))) ++ [((0 : Fin 2), true)]
termination_by i => (i - npq p q).toNat
decreasing_by
  have h : npq p q < i - (q : ℤ) := by omega
  have h0 : 0 < i - npq p q := by omega
  exact (Int.toNat_lt_toNat h0).mpr (by omega)

/-- **The gauge word below the band**: at every level `i < 0`, descend the `a`-edges to the band.
The recursion stops as soon as the level has come back to `≥ 0`, i.e. at the first level
`≥ 0`, which lies in `[0, q)`. -/
def gNegL (p q : ℕ) (hq : 1 ≤ q) (Wt : ℤ → FreeGroup (Fin 2)) : ℤ → List (Fin 2 × Bool)
  | i => (if 0 ≤ i + (q : ℤ) then wordOf (Wt (i + (q : ℤ)))
          else gNegL p q hq Wt (i + (q : ℤ))) ++ [((0 : Fin 2), false)]
termination_by i => (-i).toNat
decreasing_by
  have h : i + (q : ℤ) < 0 := by omega
  have h0 : 0 < -i := by omega
  exact (Int.toNat_lt_toNat h0).mpr (by omega)

/-- **The global gauge word** at the level `i`: the given band word for `0 ≤ i ≤ pq`, the `a`-chain
above the band for `i > pq`, the `a`-chain below the band for `i < 0`. -/
def gaugeExtL (p q : ℕ) (hq : 1 ≤ q) (Wt : ℤ → FreeGroup (Fin 2)) (i : ℤ) : List (Fin 2 × Bool) :=
  if h : 0 ≤ i ∧ i ≤ npq p q then wordOf (Wt i)
  else if h2 : i < 0 then gNegL p q hq Wt i
  else gPosL p q hq Wt i

/-- **The global gauge**: the element of `F 2` spelled by `gaugeExtL`. -/
def gaugeExt (p q : ℕ) (hq : 1 ≤ q) (Wt : ℤ → FreeGroup (Fin 2)) (i : ℤ) : FreeGroup (Fin 2) :=
  FreeGroup.mk (gaugeExtL p q hq Wt i)

/-! ## Elementary level bounds -/

theorem q_le_npq {p q : ℕ} (hp : 1 ≤ p) : (q : ℤ) ≤ npq p q := by
  have hp1 : (1 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp
  have hq0 : (0 : ℤ) ≤ (q : ℤ) := by positivity
  have h := mul_le_mul_of_nonneg_right hp1 hq0
  simpa [npq] using h

theorem npq_nonneg {p q : ℕ} : 0 ≤ npq p q := by
  have hp0 : (0 : ℤ) ≤ (p : ℤ) := by positivity
  have hq0 : (0 : ℤ) ≤ (q : ℤ) := by positivity
  simpa [npq] using mul_nonneg hp0 hq0

theorem npq_sub_q_nonneg {p q : ℕ} (hp : 1 ≤ p) : 0 ≤ npq p q - (q : ℤ) := by
  have := q_le_npq (p := p) (q := q) hp
  linarith

/-! ## Agreement with the band -/

@[simp] theorem gaugeExtL_of_band {p q : ℕ} {hq : 1 ≤ q} {Wt : ℤ → FreeGroup (Fin 2)} {i : ℤ}
    (h1 : 0 ≤ i) (h2 : i ≤ npq p q) :
    gaugeExtL p q hq Wt i = wordOf (Wt i) := by
  rw [gaugeExtL, dif_pos ⟨h1, h2⟩]

theorem gaugeExt_of_band {p q : ℕ} {hq : 1 ≤ q} {Wt : ℤ → FreeGroup (Fin 2)} {i : ℤ}
    (h1 : 0 ≤ i) (h2 : i ≤ npq p q) :
    gaugeExt p q hq Wt i = Wt i := by
  rw [gaugeExt, gaugeExtL_of_band h1 h2, mk_wordOf]

theorem gaugeExt_zero {p q : ℕ} {hq : 1 ≤ q} {Wt : ℤ → FreeGroup (Fin 2)} (h : Wt 0 = 1) :
    gaugeExt p q hq Wt 0 = 1 := by
  rw [gaugeExt_of_band le_rfl (npq_nonneg (p := p) (q := q)), h]

/-! ## The recursion equations of the two chains -/

theorem gPosL_eq {p q : ℕ} {hq : 1 ≤ q} {Wt : ℤ → FreeGroup (Fin 2)} (i : ℤ) :
    gPosL p q hq Wt i =
      (if i - (q : ℤ) ≤ npq p q then wordOf (Wt (i - (q : ℤ)))
       else gPosL p q hq Wt (i - (q : ℤ))) ++ [((0 : Fin 2), true)] := by
  rw [gPosL]

theorem gNegL_eq {p q : ℕ} {hq : 1 ≤ q} {Wt : ℤ → FreeGroup (Fin 2)} (i : ℤ) :
    gNegL p q hq Wt i =
      (if 0 ≤ i + (q : ℤ) then wordOf (Wt (i + (q : ℤ)))
       else gNegL p q hq Wt (i + (q : ℤ))) ++ [((0 : Fin 2), false)] := by
  rw [gNegL]

/-- The recursion step of the upper chain at a level above the band. -/
theorem gPosL_above {p q : ℕ} {hq : 1 ≤ q} {Wt : ℤ → FreeGroup (Fin 2)} {i : ℤ}
    (hi : npq p q + (q : ℤ) < i) :
    gPosL p q hq Wt i = gPosL p q hq Wt (i - (q : ℤ)) ++ [((0 : Fin 2), true)] := by
  rw [gPosL_eq, if_neg (by omega : ¬ (i - (q : ℤ) ≤ npq p q))]

/-- The base of the upper chain: at a level `i + q` with `i ≤ pq` (and `i > pq - q`), the chain has
come back into the band. -/
theorem gPosL_base {p q : ℕ} {hq : 1 ≤ q} {Wt : ℤ → FreeGroup (Fin 2)} {i : ℤ}
    (h2 : i ≤ npq p q) :
    gPosL p q hq Wt (i + (q : ℤ)) = wordOf (Wt i) ++ [((0 : Fin 2), true)] := by
  rw [gPosL_eq, if_pos (by rw [add_sub_cancel_right]; exact h2),
    show i + (q : ℤ) - (q : ℤ) = i from add_sub_cancel_right i (q : ℤ)]

/-- The recursion step of the lower chain at a level below the band. -/
theorem gNegL_below {p q : ℕ} {hq : 1 ≤ q} {Wt : ℤ → FreeGroup (Fin 2)} {i : ℤ}
    (hi : i + (q : ℤ) < 0) :
    gNegL p q hq Wt i = gNegL p q hq Wt (i + (q : ℤ)) ++ [((0 : Fin 2), false)] := by
  rw [gNegL_eq, if_neg (by omega : ¬ (0 ≤ i + (q : ℤ)))]

/-- The base of the lower chain: at a level `i < 0` with `i + q ≥ 0`, the chain has come back into
the band. -/
theorem gNegL_base {p q : ℕ} {hq : 1 ≤ q} {Wt : ℤ → FreeGroup (Fin 2)} {i : ℤ}
    (h : 0 ≤ i + (q : ℤ)) :
    gNegL p q hq Wt i = wordOf (Wt (i + (q : ℤ))) ++ [((0 : Fin 2), false)] := by
  rw [gNegL_eq, if_pos h]

/-! ## The element-level recursion steps of the global gauge -/

/-- **Above the band, the global gauge climbs by `a`**: for `i > pq - q` the gauge at the level
`i + q` is the gauge at the level `i` times `a`. -/
theorem gaugeExt_pos_step {p q : ℕ} (hp : 1 ≤ p) {hq : 1 ≤ q} {Wt : ℤ → FreeGroup (Fin 2)}
    {i : ℤ} (hi : npq p q - (q : ℤ) < i) :
    gaugeExt p q hq Wt (i + (q : ℤ)) = gaugeExt p q hq Wt i * FreeGroup.of (0 : Fin 2) := by
  have hq0 : (0 : ℤ) < (q : ℤ) := by exact_mod_cast hq
  have hsub : 0 ≤ npq p q - (q : ℤ) := npq_sub_q_nonneg (p := p) (q := q) hp
  have hni : ¬ (i + (q : ℤ) < 0) := by omega
  have hnotband : ¬ (0 ≤ i + (q : ℤ) ∧ i + (q : ℤ) ≤ npq p q) := by
    rintro ⟨-, h2⟩; omega
  rw [gaugeExt, gaugeExt, gaugeExtL, dif_neg hnotband, dif_neg hni]
  have hcase : gPosL p q hq Wt (i + (q : ℤ)) =
      (if i ≤ npq p q then wordOf (Wt i) else gPosL p q hq Wt i) ++ [((0 : Fin 2), true)] := by
    rw [gPosL_eq, show i + (q : ℤ) - (q : ℤ) = i from add_sub_cancel_right i (q : ℤ)]
  rw [hcase]
  by_cases hb : i ≤ npq p q
  · have hmem : 0 ≤ i ∧ i ≤ npq p q := ⟨by omega, hb⟩
    rw [if_pos hb, gaugeExtL, dif_pos hmem, mk_append, mk_singleton_true]
  · have hmem : ¬ (0 ≤ i ∧ i ≤ npq p q) := by
      rintro ⟨-, h2⟩; exact hb h2
    have hpos : ¬ (i < 0) := by omega
    rw [if_neg hb, gaugeExtL, dif_neg hmem, dif_neg hpos, mk_append, mk_singleton_true]

/-- **Below the band, the global gauge descends by `a⁻¹`**: for `i < 0` the gauge at the level `i`
is the gauge at the level `i + q` times `a⁻¹`. -/
theorem gaugeExt_neg_step {p q : ℕ} (hp : 1 ≤ p) {hq : 1 ≤ q} {Wt : ℤ → FreeGroup (Fin 2)}
    {i : ℤ} (hi : i < 0) :
    gaugeExt p q hq Wt i = gaugeExt p q hq Wt (i + (q : ℤ)) * (FreeGroup.of (0 : Fin 2))⁻¹ := by
  have hq0 : (0 : ℤ) < (q : ℤ) := by exact_mod_cast hq
  have hsub : 0 ≤ npq p q - (q : ℤ) := npq_sub_q_nonneg (p := p) (q := q) hp
  have hnil : ¬ (0 ≤ i ∧ i ≤ npq p q) := by
    rintro ⟨h1, -⟩; omega
  rw [gaugeExt, gaugeExt, gaugeExtL, dif_neg hnil, dif_pos hi]
  by_cases hle : i + (q : ℤ) < 0
  · rw [gaugeExtL, dif_neg (by rintro ⟨h1, -⟩; omega : ¬ (0 ≤ i + (q : ℤ) ∧ i + (q : ℤ) ≤ npq p q)),
      dif_pos hle, gNegL_below hle, mk_append, mk_singleton_false]
  · have hmem : 0 ≤ i + (q : ℤ) ∧ i + (q : ℤ) ≤ npq p q := by
      refine ⟨by omega, ?_⟩
      by_contra hc
      have : npq p q < i + (q : ℤ) := by omega
      have := q_le_npq (p := p) (q := q) hp
      omega
    rw [gaugeExtL, dif_pos hmem, gNegL_base (by omega : 0 ≤ i + (q : ℤ)),
      mk_append, mk_singleton_false]

/-! ## The `a`-edges of the two chains are trivial -/

/-- **The `a`-edge `(0,i)` is trivial above the band**, for `i > pq - q`: the gauge at the level
`i + q` is the gauge at the level `i` times `a`, so the loop class of the edge `(0,i)` is `1`. -/
theorem coverClassAt_aedge_pos {p q : ℕ} (hp : 1 ≤ p) {hq : 1 ≤ q} {Wt : ℤ → FreeGroup (Fin 2)}
    {i : ℤ} (hi : npq p q - (q : ℤ) < i) :
    coverClassAt (gaugeExt p q hq Wt) (tlW p q) ((0 : Fin 2), i) = 1 := by
  rw [coverClassAt, gaugeMap_of]
  have h : (i + tlW p q (0 : Fin 2)) = i + (q : ℤ) := by simp [tlW]
  rw [h, gaugeExt_pos_step (p := p) (q := q) hp hi]
  group

/-- **The `a`-edge `(0,i)` is trivial below the band**, for `i < 0`. -/
theorem coverClassAt_aedge_neg {p q : ℕ} (hp : 1 ≤ p) {hq : 1 ≤ q} {Wt : ℤ → FreeGroup (Fin 2)}
    {i : ℤ} (hi : i < 0) :
    coverClassAt (gaugeExt p q hq Wt) (tlW p q) ((0 : Fin 2), i) = 1 := by
  rw [coverClassAt, gaugeMap_of]
  have h : (i + tlW p q (0 : Fin 2)) = i + (q : ℤ) := by simp [tlW]
  rw [h, gaugeExt_neg_step (p := p) (q := q) hp hi]
  group

end

end Work.OROneRel
/-!
## Notes for the properties of `gaugeExt` (to be proved in separate files)

The definitions above are chosen so that the following are provable by elementary list/level
manipulations.  They are recorded here because they are the intended interface.

* `gaugeExtL_pos_step`-style facts are already proved above (`gaugeExt_pos_step`,
  `gaugeExt_neg_step`), giving `coverClassAt_aedge_pos` and `coverClassAt_aedge_neg`: **the `a`-edges
  of the two chains are trivial**.

* *Reducedness*: the chain words are reduced.  The two inputs are the "last letter" facts about the
  band gauge, both consequences of `htree` (the walk of a band gauge word traverses only edges of
  `winE 0 pq`):
  - if `pq - q < w ≤ pq` then the last letter of `wordOf (Wt w)` is not `(0,false)` (i.e. not `a⁻¹`);
    otherwise the last decorated letter would be `((0,w),false)`, and the edge `(0,w)` is not an edge
    of the band because `w + q > pq`;
  - if `w < q` then the last letter of `wordOf (Wt w)` is not `(0,true)` (i.e. not `a`); otherwise
    the last decorated letter would be `((0,w-q),true)` with `w - q < 0`.

* *`hwalk`*: every gauge word `gaugeExt j` runs through edges of trivial class.  For `0 ≤ j ≤ pq`
  this is `htree`; for the chains it follows by induction on the recursion, the new step being an
  `a`-edge of the chain, which is trivial by `coverClassAt_aedge_pos` / `coverClassAt_aedge_neg`.

* *`b`-edges*: the `b`-edges with `j > pq` and with `j ≤ p - 1` have non-trivial class.  If
  `coverClassAt (gaugeExt) (tlW p q) (1,j) = 1` then `gaugeExt (j - p) = gaugeExt j * b`; reducing
  along the chains, the left hand side ends with `a⁻¹` (for `j > pq`: the right hand side ends with
  `b`, while `wordOf (gaugeExt (j-p))` ends with `a` if `j - p > pq` and cannot end with `b` if
  `j - p ≤ pq`, since the edge `(1,j)` is not in the band).  For `j ≤ p - 1` the left hand side is a
  `gNegL` word ending with `(0,false)` (i.e. `a⁻¹`) while the right hand side ends with `b`, and the
  word of `gaugeExt j = Wt j` does not end with `b⁻¹` (the edge `(1,j)` is not in the band).
-/
