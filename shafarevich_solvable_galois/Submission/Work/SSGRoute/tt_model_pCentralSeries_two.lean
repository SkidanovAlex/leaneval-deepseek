import Mathlib
import Submission.Work.SSGRoute.TwoTwoModelDefs
import Submission.Work.SSGRoute.pCentralSeries_two_eq_bot_of_exponent_four
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The third term of the `2`-central series of the "two-two" detector group vanishes

The detector group `TTModel ι` of `Submission.Work.SSGRoute.TwoTwoModelDefs` has exponent `4`
and its commutator subgroup is central of exponent `2`.  Hence the second term
`P₂ = (TTModel ι)² [TTModel ι, TTModel ι]` of the descending `2`-central series is central of
exponent `2`, and the third term `P₃ = (P₂)² [P₂, TTModel ι]` is trivial.

* `TTModel.tt_commutator_fst`, `TTModel.tt_ker_fst_commute`, `TTModel.tt_ker_fst_sq` : the
  kernel of `fst` is central of exponent `2`, and commutators lie in it;
* `TTModel.tt_pow_four` : every element has order dividing `4`.

The final theorem is then the general group-theoretic lemma
`pCentralSeries_two_eq_bot_of_exponent_four`.
-/

open scoped commutatorElement

namespace Work.SSGRoute

namespace TTModel

variable {ι : Type*}

/-! ## Elementary `ZMod` arithmetic -/

lemma zmod4_two_two (a : ZMod 4) : (a + a) + (a + a) = 0 := by
  revert a; decide

lemma zmod2_add_self (u : ZMod 2) : u + u = 0 := by
  revert u; decide

lemma ttChi_add_self (a : ZMod 4) : ttChi (a + a) = 0 := by
  revert a; decide

/-! ## Coordinates of squares -/

theorem tt_sq_fst (x : TTModel ι) (i : ι) : (x ^ 2).fst i = x.fst i + x.fst i := by
  rw [pow_two, TTModel.fst_mul_apply]

theorem tt_sq_fst_fun (x : TTModel ι) : (x ^ 2).fst = x.fst + x.fst := by
  rw [pow_two]; rfl

theorem tt_sq_snd (x : TTModel ι) (p : ι × ι) :
    (x ^ 2).snd p = x.snd p + x.snd p + coc x.fst x.fst p := by
  obtain ⟨i, j⟩ := p
  rw [pow_two, TTModel.snd_mul_apply]
  rfl

/-! ## The kernel of `fst` is central of exponent `2` -/

theorem tt_ker_fst_commute (x y : TTModel ι) (hx : x.fst = 0) : x * y = y * x := by
  refine TTModel.ext' (fun i => ?_) (fun p => ?_)
  · show (x * y).fst i = (y * x).fst i
    rw [TTModel.fst_mul_apply, TTModel.fst_mul_apply, hx]
    simp
  · obtain ⟨i, j⟩ := p
    show (x * y).snd (i, j) = (y * x).snd (i, j)
    rw [TTModel.snd_mul_apply, TTModel.snd_mul_apply, hx]
    simp only [Pi.zero_apply, map_zero, zero_mul, mul_zero, add_zero, zero_add]
    ring

theorem tt_ker_fst_sq (x : TTModel ι) (hx : x.fst = 0) : x ^ 2 = 1 := by
  refine TTModel.ext' (fun i => ?_) (fun p => ?_)
  · show (x ^ 2).fst i = (1 : TTModel ι).fst i
    rw [tt_sq_fst, hx]
    simp
  · obtain ⟨i, j⟩ := p
    show (x ^ 2).snd (i, j) = (1 : TTModel ι).snd (i, j)
    rw [tt_sq_snd, hx, coc_zero_left]
    simp only [TTModel.snd_one, Pi.zero_apply, add_zero, zero_add]
    exact zmod2_add_self (x.snd (i, j))

/-! ## Commutators -/

theorem tt_commutator_fst (x y : TTModel ι) : (⁅x, y⁆).fst = 0 := by
  rw [commutatorElement_def]
  funext i
  simp only [TTModel.fst_mul, TTModel.fst_inv, Pi.add_apply, Pi.neg_apply, Pi.zero_apply]
  abel

theorem tt_commutator_sq (x y : TTModel ι) : ⁅x, y⁆ ^ 2 = 1 :=
  tt_ker_fst_sq ⁅x, y⁆ (tt_commutator_fst x y)

theorem tt_commutator_commutator (x y z : TTModel ι) : ⁅⁅x, y⁆, z⁆ = 1 :=
  commutatorElement_eq_one_iff_commute.mpr
    (tt_ker_fst_commute ⁅x, y⁆ z (tt_commutator_fst x y))

/-! ## Exponent `4` -/

theorem tt_pow_four (x : TTModel ι) : x ^ 4 = 1 := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul]
  refine TTModel.ext' (fun i => ?_) (fun p => ?_)
  · show ((x ^ 2) ^ 2).fst i = (0 : ι → ZMod 4) i
    rw [pow_two, TTModel.fst_mul_apply, tt_sq_fst]
    simp only [Pi.zero_apply]
    exact zmod4_two_two (x.fst i)
  · obtain ⟨i, j⟩ := p
    show ((x ^ 2) ^ 2).snd (i, j) = (0 : ι × ι → ZMod 2) (i, j)
    rw [pow_two, TTModel.snd_mul_apply, tt_sq_snd, tt_sq_fst_fun]
    simp only [Pi.add_apply, ttChi_add_self, mul_zero, Pi.zero_apply, add_zero]
    exact zmod2_add_self (x.snd (i, j) + x.snd (i, j) + coc x.fst x.fst (i, j))

end TTModel

/-- The third term of the descending `2`-central series of the detector group `TTModel ι` is
trivial: `TTModel ι` has exponent `4` and its commutator subgroup is central of exponent `2`. -/
theorem tt_model_pCentralSeries_two (ι : Type*) :
    Work.Shrinking.pCentralSeries 2 (Work.SSGRoute.TTModel ι) 2 = ⊥ :=
  pCentralSeries_two_eq_bot_of_exponent_four
    (fun x => TTModel.tt_pow_four x)
    (fun x y z => TTModel.tt_commutator_commutator x y z)
    (fun x y => TTModel.tt_commutator_sq x y)

end Work.SSGRoute
