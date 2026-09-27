import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.FanDefs
import Submission.Work.EQ.fan_base
import Submission.Work.EQ.germCHelpers
import Submission.Work.EQ.germC_facts
import Submission.Work.EQ.charValDefs
import Submission.Work.EQ.charVal_aux
import Submission.Work.EQ.walk_bounds
import Submission.Work.EQ.walk_count
import Submission.Work.EQ.charVal_main
import Submission.Work.EQ.charVal_props
import Submission.Work.EQ.fan_step_deriv
import Submission.Work.EQ.SqrtNearOne
import Submission.Work.EQ.FanSep.Defs
import Submission.Work.EQ.FanSep.axis_walk
import Submission.Work.EQ.FanSep.centre_numbers
import Submission.Work.EQ.FanSep.germ_lip
import Submission.Work.EQ.FanSep.step_x
import Submission.Work.EQ.FanSep.step_w

namespace Work.EQ

open Complex Filter _root_.Topology
open scoped BigOperators

noncomputable section

/-- The state of level `j` of the word `ε` (level `j` is the suffix `ε.drop j`). -/
def fLvl (ε : List Bool) (j : ℕ) : ℕ := stAux (ε.drop j).reverse 0

/-- Number of levels `k < |ε|` whose centre is not `A₁`, i.e. whose walk state is nonzero. -/
def fVis (ε : List Bool) : ℕ := ((Finset.range ε.length).filter (fun k => fLvl ε k ≠ 0)).card

@[simp] lemma fLvl_self (ε : List Bool) : fLvl ε ε.length = 0 := by
  rw [fLvl, List.drop_length]; rfl

lemma fLvl_zero (ε : List Bool) : fLvl ε 0 = stAux ε.reverse 0 := rfl

/-- **The fan centre is the walk centre.** -/
theorem fan_centre_walk {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) (ε : List Bool) :
    fan a h ε 0 = (((stCtr (stAux ε.reverse 0) : ℝ) : ℂ), (0 : ℂ)) := by
  obtain ⟨hstp, -, hne, -, -, -, -, -, -, -, -, -, -, -, -⟩ := walk_bounds (a := a) ha0 ha1
  induction ε with
  | nil =>
      rw [fan, germC_value ha0 ha1 hh]
      simp [stCtr, stIdx]
  | cons s ε ih =>
      rw [fan]
      rw [mul_zero, ih]
      rw [FanSep.invBranch_axis a s (hne (stAux ε.reverse 0))]
      have happ : stAux (s :: ε).reverse 0 = stp s (stAux ε.reverse 0) := by
        rw [List.reverse_cons, stAux_append]; rfl
      rw [happ, hstp]
      refine Prod.ext ?_ ?_
      · apply congrArg (fun t : ℝ => (t : ℂ))
        rw [axStep]
        have h1 : sgnB s = if s then (1 : ℝ) else -1 := by cases s <;> rfl
        have h2 : sgnR (stCtr (stAux ε.reverse 0) + a / 2)
            = (stCtr (stAux ε.reverse 0) + a / 2) / |stCtr (stAux ε.reverse 0) + a / 2| :=
          (div_abs_self (hne (stAux ε.reverse 0))).symm
        rw [h1, h2]
        ring
      · simp


/-- `nonA1Count` counts exactly the levels whose walk state is nonzero. -/
lemma nonA1Count_eq_fVis {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) (ε : List Bool) :
    nonA1Count a h ε = fVis ε := by
  unfold nonA1Count fVis
  have hfin : ({k : ℕ | k < ε.length ∧
      fan a h (ε.drop k) 0 ≠ ((-1 / 2 : ℂ), (0 : ℂ))} : Set ℕ).Finite :=
    (Set.finite_Iio ε.length).subset (fun k hk => hk.1)
  rw [Set.ncard_eq_toFinset_card _ hfin]
  rw [show hfin.toFinset = (Finset.range ε.length).filter (fun k => fLvl ε k ≠ 0) from by
    ext k
    rw [Set.Finite.mem_toFinset hfin]
    simp only [Set.mem_setOf_eq, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hk, hfa⟩
      refine ⟨hk, fun hz => hfa ?_⟩
      rw [fan_centre_walk ha0 ha1 hh]
      have hz0 : stAux (ε.drop k).reverse 0 = 0 := hz
      rw [hz0]
      simp [stCtr, stIdx]
    · rintro ⟨hk, hz⟩
      refine ⟨hk, ?_⟩
      rw [fan_centre_walk ha0 ha1 hh]
      intro hcontra
      exact hz (stCtr_eq_iff.mp (by
        have h1 : (stCtr (stAux (ε.drop k).reverse 0) : ℂ) = ((-1 / 2 : ℝ) : ℂ) := by
          have := congrArg Prod.fst hcontra
          simpa using this
        exact Complex.ofReal_inj.mp h1))]

/-- **The extreme property, strict form.** For a centre `c = -1/2 + 2k` with `k ≠ 0`, the
quantity `λ‖c - a/2‖/‖c + a/2‖` is bounded by `fanTh a < 1`. -/
theorem centre_ratio_le_fanTh {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {k : ℤ} (hk : k ≠ 0) :
    eqLam a * |(-1 / 2 + 2 * (k : ℝ)) - a / 2| / |(-1 / 2 + 2 * (k : ℝ)) + a / 2| ≤
      fanTh a := by
  set m : ℝ := (k : ℝ) with hm
  have hA : |(-1 / 2 + 2 * m) - a / 2| = |2 * m - (1 + a) / 2| := by congr 1; ring
  have hB : |(-1 / 2 + 2 * m) + a / 2| = |2 * m - (1 - a) / 2| := by congr 1; ring
  rw [hA, hB, eqLam, fanTh]
  have hcpos : (0 : ℝ) < (1 - a) / 2 := by linarith
  have hdpos : (0 : ℝ) < (1 + a) / 2 := by linarith
  have h5 : (0 : ℝ) < 5 - a := by linarith
  have h5' : (0 : ℝ) < 5 + a := by linarith
  have hden : (0 : ℝ) < |2 * m - (1 - a) / 2| := abs_pos.mpr (by
    intro hc; have : (1 - a) / 2 = 2 * m := by linarith
    rcases lt_or_gt_of_ne hk with hk0 | hk0
    · have hm1 : m ≤ -1 := by
        have hk' : k ≤ (-1 : ℤ) := by omega
        have : (k : ℝ) ≤ ((-1 : ℤ) : ℝ) := by exact_mod_cast hk'
        simpa [hm] using this
      linarith
    · have hm1 : 1 ≤ m := by
        have hk' : (1 : ℤ) ≤ k := by omega
        have : ((1 : ℤ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk'
        simpa [hm] using this
      linarith)
  have key : |2 * m - (1 + a) / 2| * (5 - a) ≤ |2 * m - (1 - a) / 2| * (5 + a) := by
    rcases lt_or_gt_of_ne hk with hk0 | hk0
    · have hm1 : m ≤ -1 := by
        have hk' : k ≤ (-1 : ℤ) := by omega
        have : (k : ℝ) ≤ ((-1 : ℤ) : ℝ) := by exact_mod_cast hk'
        simpa [hm] using this
      have h1 : |2 * m - (1 + a) / 2| = (1 + a) / 2 - 2 * m := by
        rw [abs_of_neg (by linarith : 2 * m - (1 + a) / 2 < 0)]
        ring
      have h2 : |2 * m - (1 - a) / 2| = (1 - a) / 2 - 2 * m := by
        rw [abs_of_neg (by linarith : 2 * m - (1 - a) / 2 < 0)]
        ring
      rw [h1, h2]; nlinarith [ha0, hm1]
    · have hm1 : 1 ≤ m := by
        have hk' : (1 : ℤ) ≤ k := by omega
        have : ((1 : ℤ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk'
        simpa [hm] using this
      have h1 : |2 * m - (1 + a) / 2| = 2 * m - (1 + a) / 2 := by
        rw [abs_of_pos (by linarith : 0 < 2 * m - (1 + a) / 2)]
      have h2 : |2 * m - (1 - a) / 2| = 2 * m - (1 - a) / 2 := by
        rw [abs_of_pos (by linarith : 0 < 2 * m - (1 - a) / 2)]
      rw [h1, h2]; nlinarith [ha0, hm1]
  have key2 : |2 * m - (1 + a) / 2| / |2 * m - (1 - a) / 2| ≤ (5 + a) / (5 - a) := by
    rw [div_le_div_iff₀ hden h5]
    linarith [key]
  calc ((1 - a) / (1 + a)) * |2 * m - (1 + a) / 2| / |2 * m - (1 - a) / 2|
      = ((1 - a) / (1 + a)) * (|2 * m - (1 + a) / 2| / |2 * m - (1 - a) / 2|) := by ring
    _ ≤ ((1 - a) / (1 + a)) * ((5 + a) / (5 - a)) :=
        mul_le_mul_of_nonneg_left key2 (by positivity)
    _ = (1 - a) * (5 + a) / ((1 + a) * (5 - a)) := by field_simp

/-- The extreme property at `A₁`: the quantity is exactly `1`. -/
theorem centre_ratio_zero (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    eqLam a * |(-1 / 2 + 2 * ((0 : ℤ) : ℝ)) - a / 2| / |(-1 / 2 + 2 * ((0 : ℤ) : ℝ)) + a / 2|
      = 1 := by
  rw [eqLam]
  simp only [Int.cast_zero, mul_zero, add_zero]
  rw [show (-1 / 2 - a / 2 : ℝ) = -((1 + a) / 2) by ring,
    show (-1 / 2 + a / 2 : ℝ) = -((1 - a) / 2) by ring, abs_neg, abs_neg,
    abs_of_pos (by linarith : (0 : ℝ) < (1 + a) / 2),
    abs_of_pos (by linarith : (0 : ℝ) < (1 - a) / 2)]
  have hne1 : (1 + a : ℝ) ≠ 0 := by linarith
  have hne2 : (1 - a : ℝ) ≠ 0 := by linarith
  field_simp

end

end Work.EQ

namespace Work.EQ

open Complex Filter _root_.Topology

theorem fanTh_pos {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : 0 < fanTh a := by
  rw [fanTh]
  have h1 : 0 < 1 - a := by linarith
  have h2 : 0 < 5 + a := by linarith
  have h3 : 0 < 1 + a := by linarith
  have h4 : 0 < 5 - a := by linarith
  exact div_pos (mul_pos h1 h2) (mul_pos h3 h4)

theorem fanTh_lt_one {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : fanTh a < 1 := by
  have hpos : (0:ℝ) < (1 + a) * (5 - a) := by nlinarith
  rw [fanTh, div_lt_one hpos]
  nlinarith

end Work.EQ
