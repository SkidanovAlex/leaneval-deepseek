import Submission.Work.PTGeometric.SourceFamily

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# PTGEOMETRIC: the block reparametrisation of an iterated concatenation

`Work.PTGeometric.genLoopListConcat i l` is the iterated concatenation of a list of cube loops `l`
along the coordinate `i`.  On the `k`-th dyadic block of the coordinate `i` the concatenation reads
the element `l[k]` of the list at a *reparametrised* cube point: the coordinate `i` is sent to
`2 ^ (k+1) * (t i) - 1` and the other coordinates are unchanged.  This file fixes that
reparametrisation, `Work.PTGeometric.blockPt`, together with the clipping map
`Work.PTGeometric.ptProj` of the unit interval which makes it a *total* function of the cube point
(so that it can be composed continuously, and so that on the interior of a dyadic block the clipping
is inactive and the reparametrisation is an affine — hence smooth — function of `t i`).

## Main definitions

* `Work.PTGeometric.ptProj` — the clipping of `ℝ` onto `[0,1]`;
* `Work.PTGeometric.blockPt` — the block reparametrisation of the `k`-th block along the coordinate
  `i`.

## Main results

* `Work.PTGeometric.ptProj_coe`, `Work.PTGeometric.ptProj_of_mem`
* `Work.PTGeometric.blockPt_apply_coe` — the explicit formula for the components.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped Topology unitInterval
open Function Set

namespace Work.PTGeometric

noncomputable section

variable {N : Type*} [DecidableEq N]

/-- **The clipping of the real line onto the unit interval**, as a function `ℝ → I`.  It is
continuous and it is the identity on `[0,1]`, which is where the block reparametrisation lands when
the cube point is in the interior of a dyadic block. -/
def ptProj (v : ℝ) : Set.Icc (0 : ℝ) 1 := Set.projIcc 0 1 (by norm_num) v

/-- The value of the clipping, as a real number. -/
theorem ptProj_coe (v : ℝ) : ((ptProj v : Set.Icc (0 : ℝ) 1) : ℝ) = max 0 (min 1 v) :=
  Set.coe_projIcc 0 1 (by norm_num) v

/-- On the unit interval the clipping is the identity. -/
theorem ptProj_of_mem {v : ℝ} (hv : v ∈ Set.Icc (0 : ℝ) 1) : ptProj v = ⟨v, hv⟩ :=
  Set.projIcc_of_mem (by norm_num) hv

/-- The clipping is the identity iff the argument reads back as the value, for arguments in the
unit interval. -/
theorem ptProj_eq_iff {v : ℝ} {u : Set.Icc (0 : ℝ) 1} (h : v ∈ Set.Icc (0 : ℝ) 1) :
    ptProj v = u ↔ (u : ℝ) = v := by
  rw [ptProj_of_mem h]
  exact ⟨fun hh => by rw [← hh], fun hh => Subtype.ext hh.symm⟩

/-- The clipping is continuous. -/
theorem continuous_ptProj : Continuous ptProj :=
  continuous_projIcc (a := (0 : ℝ)) (b := 1) (h := by norm_num)

/-- **The block reparametrisation of the `k`-th block** along the coordinate `i`: the coordinate `i`
is sent to `2 ^ (k+1) * (t i) - 1` (clipped to the unit interval) and the other coordinates are
unchanged.

The two hypotheses describe the interior of the `k`-th dyadic block, `2 ^ (k+1) * (t i) > 1` and
`2 ^ k * (t i) < 1`; they are what makes the clipped value an element of the open unit interval, so
that the clipping in the definition is inactive. -/
def blockPt (i : N) (k : ℕ) (t : N → Set.Icc (0 : ℝ) 1)
    (hlo : 1 < (2 : ℝ) ^ (k + 1) * (t i : ℝ)) (hhi : (2 : ℝ) ^ k * (t i : ℝ) < 1) :
    N → Set.Icc (0 : ℝ) 1 :=
  Function.update t i (ptProj ((2 : ℝ) ^ (k + 1) * (t i : ℝ) - 1))

/-- The defining equation of the block reparametrisation. -/
theorem blockPt_eq (i : N) (k : ℕ) (t : N → Set.Icc (0 : ℝ) 1)
    (hlo : 1 < (2 : ℝ) ^ (k + 1) * (t i : ℝ)) (hhi : (2 : ℝ) ^ k * (t i : ℝ) < 1) :
    blockPt i k t hlo hhi
      = Function.update t i (ptProj ((2 : ℝ) ^ (k + 1) * (t i : ℝ) - 1)) := rfl

/-- **The components of the block reparametrisation**: on the `i`-th coordinate the affine
expression `2 ^ (k+1) * (t i) - 1` (the clipping being inactive under the two hypotheses), and
elsewhere the coordinate of `t` itself. -/
theorem blockPt_apply_coe (i : N) (k : ℕ) (t : N → Set.Icc (0 : ℝ) 1)
    (hlo : 1 < (2 : ℝ) ^ (k + 1) * (t i : ℝ)) (hhi : (2 : ℝ) ^ k * (t i : ℝ) < 1) (m : N) :
    ((blockPt i k t hlo hhi m : Set.Icc (0 : ℝ) 1) : ℝ)
      = if m = i then (2 : ℝ) ^ (k + 1) * (t i : ℝ) - 1 else (t m : ℝ) := by
  have hmem : (2 : ℝ) ^ (k + 1) * (t i : ℝ) - 1 ∈ Set.Icc (0 : ℝ) 1 := by
    have hp : (2 : ℝ) ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
    refine ⟨by linarith, ?_⟩
    rw [hp]; nlinarith [hhi]
  rw [blockPt, Function.update_apply]
  split
  · rw [ptProj_of_mem hmem]
  · rfl

/-- The block reparametrisation does not change the value of the coordinates away from `i`. -/
theorem blockPt_apply_of_ne (i : N) (k : ℕ) (t : N → Set.Icc (0 : ℝ) 1)
    (hlo : 1 < (2 : ℝ) ^ (k + 1) * (t i : ℝ)) (hhi : (2 : ℝ) ^ k * (t i : ℝ) < 1)
    {m : N} (hm : m ≠ i) :
    ((blockPt i k t hlo hhi m : Set.Icc (0 : ℝ) 1) : ℝ) = (t m : ℝ) := by
  rw [blockPt_apply_coe, if_neg hm]

end

end Work.PTGeometric
