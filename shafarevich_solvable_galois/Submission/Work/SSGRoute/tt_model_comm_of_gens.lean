import Mathlib
import Submission.Work.SSGRoute.TwoTwoModelDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The commutator of two generalised generators of the "two-two" detector group

`TTModel ι = (ι → ℤ/4) × ((ι × ι) → ℤ/2)` with `(a, κ) * (a', κ') = (a + a', κ + κ' + coc a a')`.
The `fst`-part is an abelian group and the `snd`-part is central of exponent `2`, so the group is
nilpotent of class `2`; the commutator of two elements depends only on their `a`-parts:

  `⁅(a, κ), (a', κ')⁆ = (0, coc a a' + coc a' a)`.

For the generalised generators `of i = (e_i, 0)` this gives, since `coc e_i e_j = E_{ij}` with
`E_{ij}` the matrix unit, the identity `⁅of i, of j⁆ = pairElt i j`, i.e. the basic commutator of
the generators of the free group is detected by the matrix `E_{ij} + E_{ji}`.  This is the
separating property of the detector `ttDetector`.
-/

namespace Work.SSGRoute

open scoped commutatorElement

namespace TTModel

variable {ι : Type*}

/-- The `fst`-part of the commutator vanishes: the `fst`-part is abelian. -/
theorem commutator_fst (x y : TTModel ι) : ⁅x, y⁆.fst = 0 := by
  rw [commutatorElement_def]
  funext k
  simp only [fst_mul, fst_inv, Pi.add_apply, Pi.neg_apply, Pi.zero_apply]
  abel

/-- The `snd`-part of the commutator of `(a, κ)` and `(a', κ')` is `coc a a' + coc a' a`; in
particular it depends only on the `fst`-parts. -/
theorem commutator_snd (x y : TTModel ι) :
    ⁅x, y⁆.snd = coc x.fst y.fst + coc y.fst x.fst := by
  rw [commutatorElement_def]
  simp only [snd_mul, fst_mul, fst_inv, snd_inv, coc_add_left, coc_neg, coc_neg_right]
  funext p
  simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, CharTwo.neg_eq]
  ring_nf
  simp [show (2 : ZMod 2) = 0 from by decide, show (3 : ZMod 2) = 1 from by decide]

/-- `coc` evaluated on two matrix units: `coc e_i e_j = E_{ij}`. -/
theorem coc_single_single [DecidableEq ι] (i j : ι) :
    coc (Pi.single i (1 : ZMod 4)) (Pi.single j (1 : ZMod 4)) =
      Pi.single (i, j) (1 : ZMod 2) := by
  funext p
  obtain ⟨p1, p2⟩ := p
  by_cases h1 : p1 = i <;> by_cases h2 : p2 = j <;>
    simp [coc, h1, h2]

end TTModel

/-- The basic commutator `⁅of i, of j⁆` of the generalised generators is the "matrix"
`E_{ij} + E_{ji}`. -/
theorem tt_model_comm_of_gens {ι : Type*} [DecidableEq ι] (i j : ι) :
    ⁅Work.SSGRoute.TTModel.of i, Work.SSGRoute.TTModel.of j⁆ =
      Work.SSGRoute.TTModel.pairElt i j := by
  refine TTModel.ext' ?_ ?_
  · intro k
    rw [TTModel.commutator_fst]
    simp [TTModel.pairElt]
  · intro p
    rw [TTModel.commutator_snd, TTModel.of_fst, TTModel.of_fst, TTModel.coc_single_single,
      TTModel.coc_single_single, TTModel.pairElt_snd]

end Work.SSGRoute
