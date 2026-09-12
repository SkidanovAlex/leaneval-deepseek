/-
Assembly for theorem_1_3: the family packings famPacking t are pairwise
distinct (min-value theorem), every square (12s+6)² is a missing curvature of
every family packing, and the number of such squares below N is Ω(√N).

-/
import Submission.Apollo.FamMin
import Submission.Apollo.FamBridge
import Submission.Apollo.PackDistinct
import Mathlib.Tactic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Function
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Order.Filter.AtTopBot.Basic
set_option autoImplicit false
open scoped Pointwise
open scoped NumberTheorySymbols
open LocalGlobalApollonianCirclePackings

namespace Apollo

/-! ## distinctness of the family packings -/

/-- every curvature of the packing of famQuad t is ≥ famA t. -/
lemma famPacking_min (t : ℕ) : ∀ x ∈ curvatureSet (famPacking t), famA t ≤ x := by
  intro x hx
  rw [fam_curvatureSet_eq t] at hx
  rcases hx with ⟨v, hv, j, hj⟩
  rw [← hj]
  exact fam_orbit_min_ge t v hv j

/-- the positive value famD t = famC t + 4 is a curvature of the packing. -/
lemma famPacking_has_d (t : ℕ) : famD t ∈ curvatureSet (famPacking t) := by
  rw [curvatureSet]
  rw [Set.mem_iUnion₂]
  refine ⟨(⟨famQuad t, famQuad_mem t⟩ : integralPrimitiveDescartesQuadruple), ?_, ?_⟩
  · exact (MulAction.orbitRel.Quotient.mem_orbit).2 (by rfl)
  · refine ⟨(3 : Fin 4), ?_⟩
    simp [famQuad]

/-- the family packings are pairwise distinct. -/
theorem famPacking_injective : Function.Injective famPacking := by
  intro t s hts
  have hmem : famA s ∈ curvatureSet (famPacking t) := by
    rw [hts]
    exact famPacking_has_a s
  have hge : famA t ≤ famA s := famPacking_min t (famA s) hmem
  have hmem' : famA t ∈ curvatureSet (famPacking s) := by
    rw [← hts]
    exact famPacking_has_a t
  have hge' : famA s ≤ famA t := famPacking_min s (famA t) hmem'
  unfold famA at hge hge'
  omega

/-! ## the missing squares -/

/-- (12s+6)² ≡ 12 (mod 24). -/
lemma sq_twelve_mod24 (s : ℕ) : ((12 * (s : ℤ) + 6) ^ 2) % 24 = 12 := by
  have hq : (12 * (s : ℤ) + 6) ^ 2 = 24 * (6 * (s : ℤ) ^ 2 + 6 * (s : ℤ) + 1) + 12 := by ring
  rw [hq]
  omega

/-- every (12s+6)² is a positive square (for the counting, > 0). -/
lemma sq_twelve_pos (s : ℕ) : 0 < (12 * (s : ℤ) + 6) ^ 2 := by
  have hz : 0 ≤ (s : ℤ) := by exact_mod_cast Nat.zero_le s
  have h6 : 0 < 12 * (s : ℤ) + 6 := by nlinarith
  exact sq_pos_of_pos h6

/-- every (12s+6)² is a missing curvature of the family packing. -/
theorem famPacking_missing_square (t s : ℕ) :
    ((12 * (s : ℤ) + 6) ^ 2) ∈ missingCurvatureSet (famPacking t) := by
  rw [missingCurvatureSet]
  constructor
  · exact sq_twelve_pos s
  · constructor
    · exact fam_no_square_curvature t (12 * (s : ℤ) + 6)
    · -- residue class present: famD t ≡ 12 ≡ (12s+6)² (mod 24)
      refine ⟨famD t, ?_, ?_⟩
      · exact famPacking_has_d t
      · have h1 : ((famD t : ℤ) : ZMod 24) = (12 : ZMod 24) :=
          zmod24_of_emod (famD t) 12 (famD_mod24 t)
        have h2 : (((12 * (s : ℤ) + 6) ^ 2 : ℤ) : ZMod 24) = (12 : ZMod 24) :=
          zmod24_of_emod ((12 * (s : ℤ) + 6) ^ 2) 12 (sq_twelve_mod24 s)
        have hz : ((famD t : ℤ) : ZMod 24) = (((12 * (s : ℤ) + 6) ^ 2 : ℤ) : ZMod 24) := by
          rw [h1, h2]
        exact (ZMod.intCast_eq_intCast_iff (famD t) ((12 * (s : ℤ) + 6) ^ 2) 24).1 hz

/-- the missing-square map is injective. -/
lemma sq_missing_inj : Function.Injective (fun s : ℕ => (12 * (s : ℤ) + 6) ^ 2) := by
  intro s t h
  have hpos1 : 0 < 12 * (s : ℤ) + 6 := by
    have hz : 0 ≤ (s : ℤ) := by exact_mod_cast Nat.zero_le s
    nlinarith
  have hpos2 : 0 < 12 * (t : ℤ) + 6 := by
    have hz : 0 ≤ (t : ℤ) := by exact_mod_cast Nat.zero_le t
    nlinarith
  have hlt : (12 * (s : ℤ) + 6) = 12 * (t : ℤ) + 6 := by
    rcases (sq_eq_sq_iff_eq_or_eq_neg.mp h) with h' | h'
    · exact h'
    · exfalso
      omega
  have hc : (s : ℤ) = (t : ℤ) := by omega
  exact_mod_cast hc


/-! ## counting the missing squares below N -/

/-- the square used for the count. -/
def famSquare (s : ℕ) : ℤ := (12 * (s : ℤ) + 6) ^ 2

/-- the square map is injective. -/
lemma famSquare_inj : Function.Injective famSquare := by
  intro s t hst
  unfold famSquare at hst
  exact sq_missing_inj hst

/-- positive integers bounded above by a real are finite. -/
lemma int_bounded_finite (x : ℝ) : {z : ℤ | 0 < z ∧ (z : ℝ) ≤ x}.Finite := by
  refine Set.Finite.subset (Finset.finite_toSet (Finset.Icc (1 : ℤ) (Int.ceil x))) ?_
  intro z hz
  rcases hz with ⟨hp, hle⟩
  rw [Finset.mem_coe]
  rw [Finset.mem_Icc]
  constructor
  · omega
  · exact_mod_cast (le_trans hle (Int.le_ceil x))

/-- the missing set below N is finite. -/
lemma missSet_finite (A : PrimitiveApollonianCirclePacking) (x : ℝ) :
    (missingCurvatureSet A ∩ {z : ℤ | (z : ℝ) ≤ x}).Finite := by
  refine Set.Finite.subset (int_bounded_finite x) ?_
  intro z hz
  rcases hz with ⟨hm, hle⟩
  rcases hm with ⟨hp, _, _⟩
  exact ⟨hp, hle⟩

/-- the squares (12s+6)² for s < ⌊√x/48⌋ lie below x (for x ≥ 9216). -/
lemma famSquare_below (s : ℕ) (x : ℝ) (hx : 9216 ≤ x)
    (hs : s < Nat.floor (Real.sqrt x / 48)) :
    ((famSquare s : ℤ) : ℝ) ≤ x := by
  have hx0 : 0 ≤ x := by nlinarith
  have hsqrt0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have ha0 : 0 ≤ Real.sqrt x / 48 := by nlinarith
  have hslt : (s : ℝ) < Real.sqrt x / 48 := by
    have hn1 : (s : ℝ) + 1 ≤ (Nat.floor (Real.sqrt x / 48) : ℝ) := by
      exact_mod_cast (Nat.succ_le_of_lt hs)
    have hfl : (Nat.floor (Real.sqrt x / 48) : ℝ) ≤ Real.sqrt x / 48 := Nat.floor_le ha0
    nlinarith
  have hbig : (8 : ℝ) ≤ Real.sqrt x := by
    have h1 : (8 : ℝ) ^ 2 ≤ x := by nlinarith
    have h2 : (8 : ℝ) ^ 2 ≤ (Real.sqrt x) ^ 2 := by
      rw [Real.sq_sqrt hx0]
      exact h1
    have h3 := (sq_le_sq.mp h2)
    rw [abs_of_nonneg (by norm_num : 0 ≤ (8 : ℝ)), abs_of_nonneg hsqrt0] at h3
    exact h3
  have h126 : (12 * (s : ℝ) + 6) ≤ Real.sqrt x := by
    nlinarith
  have hpos : 0 ≤ 12 * (s : ℝ) + 6 := by
    have hz : 0 ≤ (s : ℝ) := by exact_mod_cast Nat.zero_le s
    nlinarith
  have hb : (12 * (s : ℝ) + 6) ^ 2 ≤ (Real.sqrt x) ^ 2 := by
    exact (sq_le_sq.mpr (by
      rw [abs_of_nonneg hpos, abs_of_nonneg hsqrt0]
      exact h126))
  have hb2 : (12 * (s : ℝ) + 6) ^ 2 ≤ x := by
    rwa [Real.sq_sqrt hx0] at hb
  have hcast : (((12 * (s : ℤ) + 6) ^ 2 : ℤ) : ℝ) = (12 * (s : ℝ) + 6) ^ 2 := by
    norm_num
  rw [show (famSquare s : ℤ) = (12 * (s : ℤ) + 6) ^ 2 by rfl]
  rw [hcast]
  exact hb2

/-- the number of missing curvatures of the family packing up to x is at least
√x / 96, for all x ≥ 9216. -/
theorem famPacking_missing_count (t : ℕ) (x : ℝ) (hx : 9216 ≤ x) :
    Real.sqrt x / 96 ≤ missingCurvatures (famPacking t) x := by
  let B : ℕ := Nat.floor (Real.sqrt x / 48)
  have hf_inj : Function.Injective famSquare := famSquare_inj
  -- all squares for s < B are missing and ≤ x:
  have hsub : famSquare '' {s : ℕ | s < B} ⊆
      (missingCurvatureSet (famPacking t) ∩ {z : ℤ | (z : ℝ) ≤ x}) := by
    intro y hy
    rcases hy with ⟨s, hs, rfl⟩
    constructor
    · unfold famSquare
      exact famPacking_missing_square t s
    · exact famSquare_below s x hx hs
  -- cardinality of the image is B:
  have himg : (famSquare '' {s : ℕ | s < B}).ncard = B := by
    have hn : (famSquare '' {s : ℕ | s < B}).ncard = ({s : ℕ | s < B}).ncard :=
      Set.ncard_image_of_injective (s := {s : ℕ | s < B}) (f := famSquare) hf_inj
    rw [hn]
    rw [show ({s : ℕ | s < B} : Set ℕ) = ((Finset.range B : Finset ℕ) : Set ℕ) by
      ext s
      simp]
    rw [Set.ncard_coe_finset]
    simp
  -- the containing (finite) set has ncard ≥ B:
  have hBle : B ≤ (missingCurvatureSet (famPacking t) ∩ {z : ℤ | (z : ℝ) ≤ x}).ncard := by
    have h1 : (famSquare '' {s : ℕ | s < B}).ncard ≤
        (missingCurvatureSet (famPacking t) ∩ {z : ℤ | (z : ℝ) ≤ x}).ncard :=
      Set.ncard_le_ncard hsub (missSet_finite (famPacking t) x)
    rwa [himg] at h1
  -- transfer to the ℝ-valued missingCurvatures:
  have hcount : (B : ℝ) ≤ missingCurvatures (famPacking t) x := by
    unfold missingCurvatures
    exact_mod_cast hBle
  -- B ≥ √x/96:
  have hB96 : Real.sqrt x / 96 ≤ (B : ℝ) := by
    have hlt : Real.sqrt x / 48 < (B : ℝ) + 1 := by
      exact_mod_cast Nat.lt_floor_add_one (Real.sqrt x / 48)
    have hbig : (96 : ℝ) ≤ Real.sqrt x := by
      have h1 : (96 : ℝ) ^ 2 ≤ x := by nlinarith
      have hsqrt0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
      have h2 : (96 : ℝ) ^ 2 ≤ (Real.sqrt x) ^ 2 := by
        rw [Real.sq_sqrt (by nlinarith : 0 ≤ x)]
        exact h1
      have h3 := (sq_le_sq.mp h2)
      rw [abs_of_nonneg (by norm_num : 0 ≤ (96 : ℝ)), abs_of_nonneg hsqrt0] at h3
      exact h3
    nlinarith
  exact le_trans hB96 hcount

/-- the family packing has Ω(√N) missing curvatures: √x =O missingCurvatures. -/
theorem famPacking_bigO_sqrt (t : ℕ) :
    Real.sqrt =O[Filter.atTop] missingCurvatures (famPacking t) := by
  have hev : ∀ᶠ x : ℝ in Filter.atTop, ‖Real.sqrt x‖ ≤ 96 * ‖missingCurvatures (famPacking t) x‖ := by
    rw [Filter.eventually_atTop]
    refine ⟨9216, ?_⟩
    intro x hx
    have hsqrt : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
    have hmiss0 : 0 ≤ missingCurvatures (famPacking t) x := by
      unfold missingCurvatures
      exact_mod_cast Nat.zero_le _
    have hc := famPacking_missing_count t x hx
    have hnorm1 : ‖Real.sqrt x‖ = Real.sqrt x := by
      rw [Real.norm_eq_abs, abs_of_nonneg hsqrt]
    have hnorm2 : ‖missingCurvatures (famPacking t) x‖ = missingCurvatures (famPacking t) x := by
      rw [Real.norm_eq_abs, abs_of_nonneg hmiss0]
    rw [hnorm1, hnorm2]
    nlinarith [hc]
  exact Asymptotics.IsBigO.of_bound 96 hev

end Apollo
