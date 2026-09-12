import Mathlib
import Submission.Section5D
import Submission.Commons.LinearAlgebra.Net.spread_permutations

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option linter.dupNamespace false

noncomputable section

/-!
# Section 5d (counting layer): admissibility of the coordinate family

This module completes the counting-layer interface of
`Submission.Section5D`: it proves that the coordinate family
`Acoord n δ ν T` (defined in `Submission.Section5D`) is
`(holeN ν T, n, δ)`-admissible with origin symmetry and the radius bound,
for `T ≤ ν/2` and `n` large enough.  These are exactly the hypotheses under
which `Submission.CorAc2.cor_anticoncentration` is applied to the family in
the net argument of Theorem A.
-/

open scoped BigOperators ENNReal

namespace Submission.Section5D

attribute [local instance] Classical.propDecidable

open Submission.Admissible
open Commons.LinearAlgebra.Net

/-! ## Hole arithmetic (`keepMag = ⌊ν/T⌋`, `holeN = ⌊ν/T⌋−1`) -/

/-- from `T ≤ ν/2` the hole half-width bound `⌊ν/T⌋` is at least `2`. -/
lemma keepMag_ge_two {ν T : ℝ} (hT0 : 0 < T) (hν0 : 0 < ν) (hTν : T ≤ ν / 2) :
    2 ≤ keepMag ν T := by
  have h : (2 : ℝ) ≤ ν / T := by
    rw [le_div_iff₀ hT0]
    linarith
  exact Nat.le_floor (n := 2) h

/-- the hole bound `N := ⌊ν/T⌋−1` is at least `1`. -/
lemma holeN_ge_one {ν T : ℝ} (hT0 : 0 < T) (hν0 : 0 < ν) (hTν : T ≤ ν / 2) :
    1 ≤ holeN ν T := by
  have h2 : 2 ≤ ⌊ν / T⌋₊ := by
    simpa [keepMag] using keepMag_ge_two (ν := ν) (T := T) hT0 hν0 hTν
  unfold holeN
  omega

/-- `⌊ν/T⌋ ≤ ν/T` (as reals). -/
lemma keepMag_le_self {ν T : ℝ} (hT0 : 0 < T) (hν0 : 0 < ν) : (keepMag ν T : ℝ) ≤ ν / T := by
  unfold keepMag
  have h : (0 : ℝ) ≤ ν / T := by positivity
  exact Nat.floor_le h

/-- `(holeN ν T : ℝ) * T ≥ ν/4` whenever `0 < T ≤ ν/2`. -/
lemma holeN_mul_T_ge_quarter {ν T : ℝ} (hT0 : 0 < T) (hν0 : 0 < ν) (hTν : T ≤ ν / 2) :
    (ν / 4 : ℝ) ≤ (holeN ν T : ℝ) * T := by
  by_cases hT4 : T ≤ ν / 4
  · have hNge : (ν / T - 2 : ℝ) ≤ (holeN ν T : ℝ) := by
      have hlt : (ν / T : ℝ) - 1 < (⌊ν / T⌋₊ : ℝ) := by
        have h1 := Nat.lt_floor_add_one (ν / T)
        linarith
      have hf2 : 1 ≤ ⌊ν / T⌋₊ := by
        have h2 : 2 ≤ keepMag ν T := keepMag_ge_two (ν := ν) (T := T) hT0 hν0 hTν
        unfold keepMag at h2
        omega
      unfold holeN
      have hc : ((⌊ν / T⌋₊ - 1 : ℕ) : ℝ) = (⌊ν / T⌋₊ : ℝ) - 1 := by
        rw [Nat.cast_sub hf2]
        norm_num
      rw [hc]
      linarith
    have hprod : (ν / T - 2 : ℝ) * T ≤ (holeN ν T : ℝ) * T := by
      exact mul_le_mul_of_nonneg_right hNge (le_of_lt hT0)
    have hcalc : (ν / T - 2 : ℝ) * T = ν - 2 * T := by
      field_simp [ne_of_gt hT0]
    have hle : (ν / 4 : ℝ) ≤ (ν / T - 2 : ℝ) * T := by
      rw [hcalc]
      linarith
    linarith
  · have hN1 : (1 : ℝ) ≤ (holeN ν T : ℝ) := by
      exact_mod_cast holeN_ge_one (ν := ν) (T := T) hT0 hν0 hTν
    have hTge : ν / 4 ≤ T := le_of_not_ge hT4
    have hprod : (1 : ℝ) * T ≤ (holeN ν T : ℝ) * T := by
      exact mul_le_mul_of_nonneg_right hN1 (le_of_lt hT0)
    linarith

/-! ## Radius growth lemmas -/

/-- the radius of a small-coordinate window is at least its defining real
bound plus one. -/
lemma smallRad_real_ge {n : ℕ} (T : ℝ) (pos : ℕ) :
    (4 * Real.sqrt (n : ℝ) / (T * Real.sqrt (pos : ℝ)) : ℝ) + 1 ≤ (smallRad n T pos : ℝ) := by
  let x : ℝ := 4 * Real.sqrt (n : ℝ) / (T * Real.sqrt (pos : ℝ))
  unfold smallRad
  have h1 : x ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil x
  have hadd : x + 1 ≤ (⌈x⌉₊ : ℝ) + 1 := by linarith
  have hcast : ((⌈x⌉₊ + 1 : ℕ) : ℝ) = (⌈x⌉₊ : ℝ) + 1 := by norm_num [Nat.cast_add]
  change x + 1 ≤ ((⌈x⌉₊ + 1 : ℕ) : ℝ)
  rwa [hcast]

/-- `4/T ≤ 4√n/(T√pos)` for `1 ≤ pos ≤ n`. -/
lemma four_div_T_le_small {n : ℕ} (T : ℝ) (pos : ℕ) (hposn : pos ≤ n) (hpos1 : 1 ≤ pos)
    (hT0 : 0 < T) :
    (4 / T : ℝ) ≤ 4 * Real.sqrt (n : ℝ) / (T * Real.sqrt (pos : ℝ)) := by
  have hposR : (0 : ℝ) < (pos : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hpos1)
  have hsqrtpos : (0 : ℝ) < Real.sqrt (pos : ℝ) := Real.sqrt_pos.2 hposR
  have hsqn : Real.sqrt (pos : ℝ) ≤ Real.sqrt (n : ℝ) := Real.sqrt_le_sqrt (by exact_mod_cast hposn)
  have hone : (1 : ℝ) ≤ Real.sqrt (n : ℝ) / Real.sqrt (pos : ℝ) := by
    rw [le_div_iff₀ hsqrtpos]
    simpa using hsqn
  have hcalc : (4 / T : ℝ) * (Real.sqrt (n : ℝ) / Real.sqrt (pos : ℝ)) =
      4 * Real.sqrt (n : ℝ) / (T * Real.sqrt (pos : ℝ)) := by
    field_simp [ne_of_gt hT0, ne_of_gt hsqrtpos]
  calc
    (4 / T : ℝ) = (4 / T : ℝ) * 1 := by ring
    _ ≤ (4 / T : ℝ) * (Real.sqrt (n : ℝ) / Real.sqrt (pos : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hone (by positivity)
    _ = 4 * Real.sqrt (n : ℝ) / (T * Real.sqrt (pos : ℝ)) := hcalc

/-- small-coordinate radius is at least `2⌊ν/T⌋−2` (natural), given
`pos ≤ n`, `1 ≤ pos`, `T ≤ ν/2`, `ν ≤ 1`. -/
lemma smallRad_ge_two_keep_sub_two {n : ℕ} {ν T : ℝ} (hν1 : ν ≤ 1) (hT0 : 0 < T)
    (hν0 : 0 < ν) (hTν : T ≤ ν / 2) {pos : ℕ} (hposn : pos ≤ n) (hpos1 : 1 ≤ pos) :
    (2 * keepMag ν T - 2 : ℕ) ≤ smallRad n T pos := by
  have hk2 : 2 ≤ keepMag ν T := keepMag_ge_two (ν := ν) (T := T) hT0 hν0 hTν
  have h41 : (4 / T : ℝ) + 1 ≤ (smallRad n T pos : ℝ) := by
    let x : ℝ := 4 * Real.sqrt (n : ℝ) / (T * Real.sqrt (pos : ℝ))
    have hx : (4 / T : ℝ) ≤ x := four_div_T_le_small T pos hposn hpos1 hT0
    have hx1 : (4 / T : ℝ) + 1 ≤ x + 1 := by linarith
    have hx2 : x + 1 ≤ (smallRad n T pos : ℝ) := smallRad_real_ge (n := n) T pos
    exact le_trans hx1 hx2
  have hνT2 : (2 * (ν / T) - 2 : ℝ) ≤ 4 / T := by
    rw [le_div_iff₀ hT0]
    field_simp [ne_of_gt hT0]
    nlinarith [hν1]
  have hfl : (2 * (keepMag ν T : ℝ) - 2 : ℝ) ≤ 2 * (ν / T) - 2 := by
    have hkm := keepMag_le_self (ν := ν) (T := T) hT0 hν0
    nlinarith
  have hge : (((2 * keepMag ν T - 2 : ℕ) : ℝ)) ≤ (smallRad n T pos : ℝ) := by
    have hc : (((2 * keepMag ν T - 2 : ℕ) : ℝ)) = 2 * (keepMag ν T : ℝ) - 2 := by
      have h2le : (2 : ℕ) ≤ 2 * keepMag ν T := by omega
      rw [Nat.cast_sub h2le]
      norm_num [Nat.cast_mul]
    rw [hc]
    calc
      2 * (keepMag ν T : ℝ) - 2 ≤ 2 * (ν / T : ℝ) - 2 := hfl
      _ ≤ 4 / T := hνT2
      _ ≤ (smallRad n T pos : ℝ) := by linarith [h41]
  exact_mod_cast hge

/-- the large-coordinate radius is at least `4/T` in reals, given `δ ≤ 1/2`,
`T > 0`. -/
lemma largeRad_real_ge_four_div {δ T : ℝ} (hδ0 : 0 < δ) (hδ12 : δ ≤ 1 / 2) (hT0 : 0 < T) :
    (4 / T : ℝ) ≤ (largeRad δ T : ℝ) - 1 := by
  have hsqrtδ : (0 : ℝ) < Real.sqrt δ := Real.sqrt_pos.2 hδ0
  have h4' : (4 * Real.sqrt δ : ℝ) ≤ Real.sqrt 8 := by
    have hle2 : (4 * Real.sqrt δ : ℝ) ^ 2 ≤ (Real.sqrt 8 : ℝ) ^ 2 := by
      rw [mul_pow]
      rw [Real.sq_sqrt (le_of_lt hδ0)]
      rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 8)]
      norm_num
      linarith [hδ12]
    have habs : |4 * Real.sqrt δ| ≤ |Real.sqrt 8| := (sq_le_sq.mp hle2)
    have hnon1 : (0 : ℝ) ≤ 4 * Real.sqrt δ := by positivity
    have hnon2 : (0 : ℝ) ≤ Real.sqrt 8 := by positivity
    rwa [abs_of_nonneg hnon1, abs_of_nonneg hnon2] at habs
  have hrat : (4 / T : ℝ) ≤ Real.sqrt 8 / (Real.sqrt δ * T) := by
    rw [le_div_iff₀ (mul_pos hsqrtδ hT0)]
    calc
      (4 / T : ℝ) * (Real.sqrt δ * T) = (4 / T * T) * Real.sqrt δ := by ring
      _ = 4 * Real.sqrt δ := by field_simp [ne_of_gt hT0]
      _ ≤ Real.sqrt 8 := h4'
  unfold largeRad
  have hceil : Real.sqrt 8 / (Real.sqrt δ * T) ≤ (⌈Real.sqrt 8 / (Real.sqrt δ * T)⌉₊ : ℝ) :=
    Nat.le_ceil _
  have hcast : (↑(⌈Real.sqrt 8 / (Real.sqrt δ * T)⌉₊ + 1 : ℕ) : ℝ) =
      (⌈Real.sqrt 8 / (Real.sqrt δ * T)⌉₊ : ℝ) + 1 := by norm_num [Nat.cast_add]
  rw [hcast]
  linarith

/-- the large-coordinate radius is at least `⌊ν/T⌋` (natural), given
`δ ≤ 1/2`, `ν ≤ 1`, `T > 0`. -/
lemma largeRad_ge_keep {δ ν T : ℝ} (hδ0 : 0 < δ) (hδ12 : δ ≤ 1 / 2) (hν0 : 0 < ν)
    (hν1 : ν ≤ 1) (hT0 : 0 < T) :
    (keepMag ν T : ℕ) ≤ largeRad δ T := by
  have hT4 : (4 / T : ℝ) ≤ (largeRad δ T : ℝ) - 1 :=
    largeRad_real_ge_four_div (δ := δ) (T := T) hδ0 hδ12 hT0
  have hd : (ν / T : ℝ) ≤ 4 / T := by
    exact div_le_div_of_nonneg_right (by nlinarith [hν1] : ν ≤ 4) (le_of_lt hT0)
  have hkm : (keepMag ν T : ℝ) ≤ ν / T := keepMag_le_self (ν := ν) (T := T) hT0 hν0
  have hge : (keepMag ν T : ℝ) ≤ (largeRad δ T : ℝ) := by linarith
  exact_mod_cast hge


/-! ## Admissibility of the coordinate family -/

/-- the 1-based position of a coordinate is at most `n`. -/
lemma posOf_le {n : ℕ} (i : Fin n) : posOf i ≤ n := by
  unfold posOf
  omega

/-- the 1-based position of a coordinate is at least `1`. -/
lemma posOf_pos {n : ℕ} (i : Fin n) : 1 ≤ posOf i := by
  unfold posOf
  omega

/-- `holeN = keepMag − 1` as naturals, given `1 ≤ keepMag`. -/
lemma holeN_eq_keep_sub_one {ν T : ℝ} (h : 1 ≤ keepMag ν T) : holeN ν T = keepMag ν T - 1 := by
  unfold holeN keepMag
  omega

/-- `holeN < keepMag` as naturals. -/
lemma holeN_lt_keepMag {ν T : ℝ} (h : 1 ≤ keepMag ν T) : holeN ν T < keepMag ν T := by
  rw [holeN_eq_keep_sub_one h]
  omega

/-- cast of the hole relation to reals: `(holeN:ℝ) = (keepMag:ℝ) − 1`. -/
lemma holeN_real_eq {ν T : ℝ} (h : 1 ≤ keepMag ν T) :
    (holeN ν T : ℝ) = (keepMag ν T : ℝ) - 1 := by
  have hn := holeN_eq_keep_sub_one h
  rw [hn]
  have h1 : (1 : ℕ) ≤ keepMag ν T := h
  have hc : (((keepMag ν T - 1 : ℕ) : ℝ)) = (keepMag ν T : ℝ) - 1 := by
    rw [Nat.cast_sub h1]
    norm_num
  exact hc

/-- `keepMag ≥ 1` in real form (from `T ≤ ν/2`). -/
lemma keepMag_real_gt_zero {ν T : ℝ} (hT0 : 0 < T) (hν0 : 0 < ν) (hTν : T ≤ ν / 2) :
    (0 : ℝ) < (keepMag ν T : ℝ) := by
  have h2 : 2 ≤ keepMag ν T := keepMag_ge_two (ν := ν) (T := T) hT0 hν0 hTν
  exact_mod_cast (lt_of_lt_of_le (by norm_num) h2)

/-- cardinality of the large single interval. -/
lemma largeWin_card (R : ℕ) : (largeWin R).card = 2 * R + 1 := by
  unfold largeWin
  rw [Int.card_Icc]
  have hz : (R : ℤ) + 1 - (-(R : ℤ)) = (2 * (R : ℤ) + 1) := by ring
  rw [hz]
  have hc : (2 * (R : ℤ) + 1) = ((2 * R + 1 : ℕ) : ℤ) := by
    norm_num [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  rw [hc]
  exact Int.toNat_natCast (2 * R + 1)

/-- the coordinate family `Acoord n δ ν T` is `(holeN ν T, n, δ)`-admissible
for every `n`, provided `0 < T ≤ ν/2` and `0 < δ ≤ 1/2`, `0 < ν ≤ 1`. -/
lemma Acoord_admissible {δ ν : ℝ} (hδ0 : 0 < δ) (hδ12 : δ ≤ 1 / 2) (hν0 : 0 < ν)
    (hν1 : ν ≤ 1) (n : ℕ) (T : ℝ) (hT0 : 0 < T) (hTν : T ≤ ν / 2) :
    Admissible (holeN ν T) n n δ (Acoord n δ ν T) := by
  constructor
  · intro i hi
    let R : ℕ := smallRad n T (posOf i)
    have hk2 : 2 ≤ keepMag ν T := keepMag_ge_two (ν := ν) (T := T) hT0 hν0 hTν
    have hk1 : 1 ≤ keepMag ν T := by omega
    have hposn : posOf i ≤ n := posOf_le i
    have hpos1 : 1 ≤ posOf i := posOf_pos i
    have hR2 : 2 * (⌊ν / T⌋₊ : ℕ) - 2 ≤ R := by
      have h := smallRad_ge_two_keep_sub_two (n := n) (ν := ν) (T := T) hν1 hT0 hν0 hTν
        (pos := posOf i) hposn hpos1
      simpa [R, keepMag] using h
    refine ⟨(keepMag ν T : ℤ), (R : ℤ), -(R : ℤ), -(keepMag ν T : ℤ), ?_, ?_, ?_, ?_, ?_⟩
    · -- cover
      simpa [R] using Acoord_small_union hi
    · -- length of first arm ≥ holeN
      have hlen := arm_card_ge_holeN (ν := ν) (T := T) (R := R)
        (by simpa [keepMag] using hk2) (by simpa [keepMag] using hR2)
      simpa [R, keepMag, holeN] using hlen
    · -- length of second arm ≥ holeN
      have hlen := arm_card_ge_holeN (ν := ν) (T := T) (R := R)
        (by simpa [keepMag] using hk2) (by simpa [keepMag] using hR2)
      -- d₂ − c₂ + 1 = R − keepMag + 1
      have hrew : ((R : ℤ) - (keepMag ν T : ℤ) + 1) = (-(keepMag ν T : ℤ)) - (-(R : ℤ)) + 1 := by ring
      rw [← hrew]
      exact hlen
    · -- disjointness of the two arms
      have hdisj := armWin_arms_disjoint (h := keepMag ν T) (R := R) hk1
      simpa [R, keepMag] using hdisj
    · -- every element has magnitude > holeN
      intro a ha
      have hka := Acoord_lower_small hi ha
      have hkaR : (keepMag ν T : ℝ) ≤ |(a : ℝ)| := by
        have hz : ((keepMag ν T : ℤ) : ℝ) ≤ ((|a| : ℤ) : ℝ) := by exact_mod_cast hka
        rwa [Int.cast_abs] at hz
      have hNlt : (holeN ν T : ℝ) < (keepMag ν T : ℝ) := by
        have hn : holeN ν T < keepMag ν T := holeN_lt_keepMag hk1
        exact_mod_cast hn
      exact lt_of_lt_of_le hNlt hkaR
  · intro i hi
    refine ⟨-(largeRad δ T : ℤ), (largeRad δ T : ℤ), ?_, ?_⟩
    · -- cover
      simpa [largeWin] using Acoord_of_large hi
    · -- length ≥ holeN
      have hkr : keepMag ν T ≤ largeRad δ T :=
        largeRad_ge_keep (δ := δ) (ν := ν) (T := T) hδ0 hδ12 hν0 hν1 hT0
      have hNk : holeN ν T ≤ keepMag ν T := by
        unfold holeN
        unfold keepMag
        omega
      have hNr : holeN ν T ≤ largeRad δ T := le_trans hNk hkr
      have h2 : holeN ν T ≤ 2 * largeRad δ T + 1 := by
        have hL : largeRad δ T ≤ 2 * largeRad δ T + 1 := by omega
        exact le_trans hNr hL
      have hgoal : (largeRad δ T : ℤ) - (-(largeRad δ T : ℤ)) + 1 =
          ((2 * largeRad δ T + 1 : ℕ) : ℤ) := by
        have hc : ((2 * largeRad δ T + 1 : ℕ) : ℤ) = 2 * (largeRad δ T : ℤ) + 1 := by
          norm_num [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
        rw [hc]
        ring
      rw [hgoal]
      exact_mod_cast h2


/-! ## Radius upper bounds and the radius bound (`hrad`) -/

/-- `⌈a⌉₊ + 1 ≤ a + 2` for `0 ≤ a`. -/
lemma ceil_add_one_le {a : ℝ} (ha : 0 ≤ a) : (⌈a⌉₊ : ℝ) + 1 ≤ a + 2 := by
  have hlt : (⌈a⌉₊ : ℝ) < a + 1 := Nat.ceil_lt_add_one ha
  linarith

/-- small-coordinate radius is at most `4√n/T + 2`. -/
lemma smallRad_upper {n : ℕ} (T : ℝ) (pos : ℕ) (hpos1 : 1 ≤ pos) (hT0 : 0 < T) :
    (smallRad n T pos : ℝ) ≤ 4 * Real.sqrt (n : ℝ) / T + 2 := by
  let x : ℝ := 4 * Real.sqrt (n : ℝ) / (T * Real.sqrt (pos : ℝ))
  have hposR : (0 : ℝ) < (pos : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hpos1)
  have hsqrtpos : (0 : ℝ) < Real.sqrt (pos : ℝ) := Real.sqrt_pos.2 hposR
  have hx0 : 0 ≤ x := by
    dsimp [x]
    positivity
  have hlt : (⌈x⌉₊ : ℝ) + 1 ≤ x + 2 := ceil_add_one_le hx0
  have hx : x ≤ 4 * Real.sqrt (n : ℝ) / T := by
    have hsqrt1 : (1 : ℝ) ≤ Real.sqrt (pos : ℝ) := by
      have hle := Real.sqrt_le_sqrt (by exact_mod_cast hpos1 : (1 : ℝ) ≤ (pos : ℝ))
      simpa using hle
    have hTle : T ≤ T * Real.sqrt (pos : ℝ) := by
      simpa using (mul_le_mul_of_nonneg_left hsqrt1 (le_of_lt hT0))
    have h4 : (0 : ℝ) ≤ 4 * Real.sqrt (n : ℝ) := by positivity
    exact div_le_div_of_nonneg_left h4 hT0 hTle
  have hlt' : (⌈x⌉₊ : ℝ) + 1 ≤ 4 * Real.sqrt (n : ℝ) / T + 2 := by linarith
  unfold smallRad
  change (↑(⌈x⌉₊ + 1 : ℕ) : ℝ) ≤ 4 * Real.sqrt (n : ℝ) / T + 2
  have hb : (↑(⌈x⌉₊ + 1 : ℕ) : ℝ) = (⌈x⌉₊ : ℝ) + 1 := by
    rw [Nat.cast_add]
    norm_num
  rwa [hb]

/-- large-coordinate radius is at most `√8/(√δ·T) + 2`. -/
lemma largeRad_upper {δ T : ℝ} (hδ0 : 0 < δ) (hT0 : 0 < T) :
    (largeRad δ T : ℝ) ≤ Real.sqrt 8 / (Real.sqrt δ * T) + 2 := by
  let y : ℝ := Real.sqrt 8 / (Real.sqrt δ * T)
  have hy0 : 0 ≤ y := by
    dsimp [y]
    positivity
  have hlt : (⌈y⌉₊ : ℝ) + 1 ≤ y + 2 := ceil_add_one_le hy0
  unfold largeRad
  change (↑(⌈y⌉₊ + 1 : ℕ) : ℝ) ≤ Real.sqrt 8 / (Real.sqrt δ * T) + 2
  have hb : (↑(⌈y⌉₊ + 1 : ℕ) : ℝ) = (⌈y⌉₊ : ℝ) + 1 := by
    rw [Nat.cast_add]
    norm_num
  rwa [hb]

/-- From a large-enough `n` the small-coordinate radius bound is below
`n·holeN` (reals). -/
lemma rad_le_n_holeN_of_n_big {δ ν : ℝ} (hδ0 : 0 < δ) (hν0 : 0 < ν) (hν1 : ν ≤ 1)
    (n : ℕ) (T : ℝ) (hT0 : 0 < T) (hTν : T ≤ ν / 2)
    (hn1 : (1 : ℝ) ≤ (n : ℝ))
    (hnν : (1024 / ν ^ 2 : ℝ) ≤ (n : ℝ))
    (hsn : (32 / ν : ℝ) ≤ Real.sqrt (n : ℝ)) :
    (4 * Real.sqrt (n : ℝ) / T + 2 : ℝ) ≤ (n : ℝ) * (holeN ν T : ℝ) := by
  have hN4 : (ν / 4 : ℝ) ≤ (holeN ν T : ℝ) * T :=
    holeN_mul_T_ge_quarter (ν := ν) (T := T) hT0 hν0 hTν
  have hNge : (ν / (4 * T) : ℝ) ≤ (holeN ν T : ℝ) := by
    have hdiv := (div_le_iff₀ hT0).mpr hN4
    have hrew : (ν / 4) / T = ν / (4 * T) := by field_simp [ne_of_gt hT0]
    rwa [hrew] at hdiv
  have hnmul : (n : ℝ) * (ν / (4 * T)) ≤ (n : ℝ) * (holeN ν T : ℝ) := by
    exact mul_le_mul_of_nonneg_left hNge (by positivity : (0 : ℝ) ≤ (n : ℝ))
  have hn8 : (8 : ℝ) ≤ (n : ℝ) := by
    have hle1 : (ν ^ 2 : ℝ) ≤ 1 := by nlinarith [hν1]
    have h1024 : (8 : ℝ) ≤ (1024 / ν ^ 2 : ℝ) := by
      have h1024ge : (1024 : ℝ) ≤ 1024 / ν ^ 2 := by
        rw [le_div_iff₀ (pow_pos hν0 2)]
        nlinarith [hle1]
      nlinarith
    linarith
  have h16 : 16 * Real.sqrt (n : ℝ) ≤ ν * (n : ℝ) / 2 := by
    have hsnpos : (0 : ℝ) < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by linarith [hn1])
    have hν2 : (0 : ℝ) < ν / 2 := by positivity
    have hmul := mul_le_mul_of_nonneg_left hsn (le_of_lt hν2)
    have hrew : (ν / 2) * (32 / ν) = 16 := by field_simp [ne_of_gt hν0] <;> ring
    have h16' : 16 ≤ (ν / 2) * Real.sqrt (n : ℝ) := by
      rwa [hrew] at hmul
    have hring : (ν / 2) * Real.sqrt (n : ℝ) = ν * Real.sqrt (n : ℝ) / 2 := by ring
    have hgoal : 16 ≤ ν * Real.sqrt (n : ℝ) / 2 := by
      simpa [hring] using h16'
    have hmul2 := mul_le_mul_of_nonneg_right hgoal (le_of_lt hsnpos)
    have hsq : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) := by
      rw [← pow_two]
      exact Real.sq_sqrt (by positivity)
    have hnorm : (ν * Real.sqrt (n : ℝ) / 2) * Real.sqrt (n : ℝ) = ν * (n : ℝ) / 2 := by
      calc
        (ν * Real.sqrt (n : ℝ) / 2) * Real.sqrt (n : ℝ) =
            (ν / 2) * (Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ)) := by ring
        _ = (ν / 2) * (n : ℝ) := by rw [hsq]
        _ = ν * (n : ℝ) / 2 := by ring
    rwa [hnorm] at hmul2
  have h8T : 8 * T ≤ 4 * ν := by nlinarith [hTν]
  have hmain : 16 * Real.sqrt (n : ℝ) + 8 * T ≤ ν * (n : ℝ) := by
    have htail : ν * (n : ℝ) / 2 + 4 * ν ≤ ν * (n : ℝ) := by nlinarith [hn8]
    linarith
  have htarget0 : (4 * Real.sqrt (n : ℝ) / T + 2 : ℝ) ≤ (ν * (n : ℝ)) / (4 * T) := by
    have h4T : (0 : ℝ) < 4 * T := by positivity
    rw [le_div_iff₀ h4T]
    have hrew3 : (4 * Real.sqrt (n : ℝ) / T + 2) * (4 * T) =
        16 * Real.sqrt (n : ℝ) + 8 * T := by
      field_simp [ne_of_gt hT0] <;> ring
    rwa [hrew3]
  have htarget : (4 * Real.sqrt (n : ℝ) / T + 2 : ℝ) ≤ (n : ℝ) * (ν / (4 * T)) := by
    have hrew2 : (ν * (n : ℝ)) / (4 * T) = (n : ℝ) * (ν / (4 * T)) := by
      field_simp [ne_of_gt hT0]
    rwa [← hrew2]
  exact le_trans htarget hnmul


/-- large-coordinate radius bound is below `n·holeN` (reals), from a
large-enough `n`. -/
lemma largeRad_le_n_holeN_of_n_big {δ ν : ℝ} (hν0 : 0 < ν)
    (n : ℕ) (T : ℝ) (hT0 : 0 < T) (hTν : T ≤ ν / 2)
    (hnδ : (4 * Real.sqrt 8 / (ν * Real.sqrt δ) + 4 : ℝ) ≤ (n : ℝ)) :
    (Real.sqrt 8 / (Real.sqrt δ * T) + 2 : ℝ) ≤ (n : ℝ) * (holeN ν T : ℝ) := by
  have hN4 : (ν / 4 : ℝ) ≤ (holeN ν T : ℝ) * T :=
    holeN_mul_T_ge_quarter (ν := ν) (T := T) hT0 hν0 hTν
  have hNge : (ν / (4 * T) : ℝ) ≤ (holeN ν T : ℝ) := by
    have hdiv := (div_le_iff₀ hT0).mpr hN4
    have hrew : (ν / 4) / T = ν / (4 * T) := by field_simp [ne_of_gt hT0]
    rwa [hrew] at hdiv
  have hnmul : (n : ℝ) * (ν / (4 * T)) ≤ (n : ℝ) * (holeN ν T : ℝ) := by
    exact mul_le_mul_of_nonneg_left hNge (by positivity : (0 : ℝ) ≤ (n : ℝ))
  have hnv : (4 * Real.sqrt 8 / Real.sqrt δ + 4 * ν : ℝ) ≤ (n : ℝ) * ν := by
    have hmul := mul_le_mul_of_nonneg_right hnδ (le_of_lt hν0)
    have hrew : (4 * Real.sqrt 8 / (ν * Real.sqrt δ) + 4) * ν =
        4 * Real.sqrt 8 / Real.sqrt δ + 4 * ν := by
      field_simp [ne_of_gt hν0] <;> ring
    rwa [hrew] at hmul
  have htarget0 : Real.sqrt 8 / (Real.sqrt δ * T) + 2 ≤ (ν * (n : ℝ)) / (4 * T) := by
    have h4T : (0 : ℝ) < 4 * T := by positivity
    rw [le_div_iff₀ h4T]
    have hrew2 : (Real.sqrt 8 / (Real.sqrt δ * T) + 2) * (4 * T) =
        4 * Real.sqrt 8 / Real.sqrt δ + 8 * T := by
      field_simp [ne_of_gt hT0] <;> ring
    rw [hrew2]
    have h8T : 8 * T ≤ 4 * ν := by nlinarith [hTν]
    nlinarith
  have htarget : Real.sqrt 8 / (Real.sqrt δ * T) + 2 ≤ (n : ℝ) * (ν / (4 * T)) := by
    have hrew3 : (ν * (n : ℝ)) / (4 * T) = (n : ℝ) * (ν / (4 * T)) := by
      field_simp [ne_of_gt hT0]
    rwa [← hrew3]
  exact le_trans htarget hnmul

/-- integer radius bound `|a| ≤ n·holeN` for every coordinate window
(`hrad`), once `n` is large enough (depending only on `δ,ν`). -/
lemma Acoord_hrad {δ ν : ℝ} (hδ0 : 0 < δ) (hδ12 : δ ≤ 1 / 2) (hν0 : 0 < ν)
    (hν1 : ν ≤ 1) :
    ∃ n₀ : ℕ, 1 ≤ n₀ ∧
      ∀ n ≥ n₀, ∀ T (hT0 : 0 < T) (hTν : T ≤ ν / 2),
        ∀ i : Fin n, ∀ a : ℤ, a ∈ Acoord n δ ν T i →
          |a| ≤ ((n * holeN ν T : ℕ) : ℤ) := by
  let Z : ℝ := max (1024 / ν ^ 2) (4 * Real.sqrt 8 / (ν * Real.sqrt δ) + 4)
  refine ⟨Nat.ceil Z + 1, by omega, ?_⟩
  intro n hn T hT0 hTν i a ha
  have hn0 : Nat.ceil Z + 1 ≤ n := hn
  have hn1nat : (1 : ℕ) ≤ n := by omega
  have hZ : Z ≤ (n : ℝ) := by
    have h1 : (Nat.ceil Z : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast (by omega : Nat.ceil Z ≤ n)
    exact le_trans (Nat.le_ceil Z) h1
  have hnν : (1024 / ν ^ 2 : ℝ) ≤ (n : ℝ) := by
    exact le_trans (le_max_left (1024 / ν ^ 2) (4 * Real.sqrt 8 / (ν * Real.sqrt δ) + 4)) hZ
  have hnδ : (4 * Real.sqrt 8 / (ν * Real.sqrt δ) + 4 : ℝ) ≤ (n : ℝ) := by
    exact le_trans (le_max_right (1024 / ν ^ 2) (4 * Real.sqrt 8 / (ν * Real.sqrt δ) + 4)) hZ
  have hsn : (32 / ν : ℝ) ≤ Real.sqrt (n : ℝ) := by
    have hpow : (32 / ν : ℝ) ^ 2 = 1024 / ν ^ 2 := by
      field_simp [ne_of_gt hν0] <;> ring
    have hle2 : (32 / ν : ℝ) ^ 2 ≤ (n : ℝ) := by
      rwa [hpow]
    exact (Real.le_sqrt (by positivity) (by positivity : (0 : ℝ) ≤ (n : ℝ))).2 hle2
  by_cases hi : smallIndex n δ (i.val)
  · -- small coordinate
    have hup := Acoord_upper_small hi ha  -- |a| ≤ (smallRad ... : ℤ)
    have hupR : |(a : ℝ)| ≤ (smallRad n T (posOf i) : ℝ) := by
      have hz : ((|a| : ℤ) : ℝ) ≤ ((smallRad n T (posOf i) : ℤ) : ℝ) := by exact_mod_cast hup
      rwa [Int.cast_abs] at hz
    have hsm : (smallRad n T (posOf i) : ℝ) ≤ 4 * Real.sqrt (n : ℝ) / T + 2 :=
      smallRad_upper T (posOf i) (posOf_pos i) hT0
    have hle := rad_le_n_holeN_of_n_big (δ := δ) (ν := ν) hδ0 hν0 hν1 n T hT0 hTν
      (by exact_mod_cast hn1nat) hnν hsn
    have hh : ((n * holeN ν T : ℕ) : ℝ) = (n : ℝ) * (holeN ν T : ℝ) := by
      exact Nat.cast_mul n (holeN ν T)
    have hfinal : |(a : ℝ)| ≤ ((n * holeN ν T : ℕ) : ℝ) := by
      rw [hh]
      exact le_trans hupR (le_trans hsm hle)
    exact int_abs_le_of_real_le (R := n * holeN ν T) (by simpa [Nat.cast_mul] using hfinal)
  · -- large coordinate
    have hup := Acoord_upper_large hi ha
    have hupR : |(a : ℝ)| ≤ (largeRad δ T : ℝ) := by
      have hz : ((|a| : ℤ) : ℝ) ≤ ((largeRad δ T : ℤ) : ℝ) := by exact_mod_cast hup
      rwa [Int.cast_abs] at hz
    have hlg : (largeRad δ T : ℝ) ≤ Real.sqrt 8 / (Real.sqrt δ * T) + 2 :=
      largeRad_upper hδ0 hT0
    have hle := largeRad_le_n_holeN_of_n_big (δ := δ) (ν := ν) hν0 n T hT0 hTν hnδ
    have hh : ((n * holeN ν T : ℕ) : ℝ) = (n : ℝ) * (holeN ν T : ℝ) := by
      exact Nat.cast_mul n (holeN ν T)
    have hfinal : |(a : ℝ)| ≤ ((n * holeN ν T : ℕ) : ℝ) := by
      rw [hh]
      exact le_trans hupR (le_trans hlg hle)
    exact int_abs_le_of_real_le (R := n * holeN ν T) (by simpa [Nat.cast_mul] using hfinal)


/-! ## product bound over the coordinate family -/

/-- Stirling lower bound for the factorial: `(k/e)^k ≤ k!` for `k ≥ 1`. -/
lemma factorial_ge_pow_exp (k : ℕ) (hk : 1 ≤ k) :
    ((k : ℝ) / Real.exp 1) ^ k ≤ (k.factorial : ℝ) := by
  have h := Stirling.le_factorial_stirling k
  have hπ : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have h2π : (1 : ℝ) ≤ 2 * Real.pi * (k : ℝ) := by
    have h1 : (1 : ℝ) ≤ 2 * Real.pi := by nlinarith
    have h2 : 2 * Real.pi ≤ 2 * Real.pi * (k : ℝ) := by
      have hm := mul_le_mul_of_nonneg_left hkR (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
      simpa using hm
    linarith
  have hsqrt : (1 : ℝ) ≤ Real.sqrt (2 * Real.pi * (k : ℝ)) := by
    exact (Real.le_sqrt (by norm_num) (by positivity)).2 (by nlinarith)
  have hkeg0 : (0 : ℝ) ≤ ((k : ℝ) / Real.exp 1) ^ k := by positivity
  have hle1 : ((k : ℝ) / Real.exp 1) ^ k ≤
      Real.sqrt (2 * Real.pi * (k : ℝ)) * ((k : ℝ) / Real.exp 1) ^ k := by
    simpa using (mul_le_mul_of_nonneg_right hsqrt hkeg0)
  exact le_trans hle1 h

/-- pos-dependent upper bound of the small radius. -/
lemma smallRad_upper_pos {n : ℕ} (T : ℝ) (pos : ℕ) (hpos0 : (0 : ℝ) < (pos : ℝ))
    (hT0 : 0 < T) :
    (smallRad n T pos : ℝ) ≤ 4 * Real.sqrt (n : ℝ) / (T * Real.sqrt (pos : ℝ)) + 2 := by
  let x : ℝ := 4 * Real.sqrt (n : ℝ) / (T * Real.sqrt (pos : ℝ))
  have hx0 : 0 ≤ x := by
    dsimp [x]
    positivity
  have hlt : (⌈x⌉₊ : ℝ) + 1 ≤ x + 2 := ceil_add_one_le hx0
  unfold smallRad
  change (↑(⌈x⌉₊ + 1 : ℕ) : ℝ) ≤ 4 * Real.sqrt (n : ℝ) / (T * Real.sqrt (pos : ℝ)) + 2
  have hb : (↑(⌈x⌉₊ + 1 : ℕ) : ℝ) = (⌈x⌉₊ : ℝ) + 1 := by
    rw [Nat.cast_add]
    norm_num
  rw [hb]
  linarith

/-- small-coordinate window has cardinality at most `2·smallRad`. -/
lemma Acoord_small_card_le_two_smallRad {n : ℕ} {δ ν T : ℝ} {i : Fin n}
    (hi : smallIndex n δ (i.val)) (hν0 : 0 < ν) (hν1 : ν ≤ 1) (hT0 : 0 < T) (hTν : T ≤ ν / 2) :
    ((Acoord n δ ν T i).card : ℝ) ≤ 2 * (smallRad n T (posOf i) : ℝ) := by
  have hk2 : 2 ≤ keepMag ν T := keepMag_ge_two (ν := ν) (T := T) hT0 hν0 hTν
  have hk1 : 1 ≤ keepMag ν T := by omega
  let R : ℕ := smallRad n T (posOf i)
  have hhR : keepMag ν T ≤ R := by
    have hposn : posOf i ≤ n := posOf_le i
    have hpos1 : 1 ≤ posOf i := posOf_pos i
    have hR2 : (2 * keepMag ν T - 2 : ℕ) ≤ smallRad n T (posOf i) :=
      smallRad_ge_two_keep_sub_two (n := n) (ν := ν) (T := T) hν1 hT0 hν0 hTν
        (pos := posOf i) hposn hpos1
    have hle : keepMag ν T ≤ 2 * keepMag ν T - 2 := by omega
    exact le_trans hle (by simpa [R] using hR2)
  have hc1 := card_Icc_nat (keepMag ν T) R hhR
  have hc2 := card_Icc_neg_nat (keepMag ν T) R hhR
  have hdisj : Disjoint (Finset.Icc (keepMag ν T : ℤ) (R : ℤ))
      (Finset.Icc (-(R : ℤ)) (-(keepMag ν T : ℤ))) := by
    have hd := armWin_arms_disjoint (h := keepMag ν T) (R := R) hk1
    simpa using hd
  have hcard : (armWin (keepMag ν T) R).card = 2 * (R - keepMag ν T + 1) := by
    unfold armWin
    rw [Finset.card_union_of_disjoint hdisj, hc1, hc2]
    ring
  have hle : 2 * (R - keepMag ν T + 1) ≤ 2 * R := by omega
  have hcov : Acoord n δ ν T i = armWin (keepMag ν T) R := by
    simpa [armWin, R] using Acoord_small_union hi
  rw [hcov]
  rw [hcard]
  exact_mod_cast hle

/-- large-coordinate window has cardinality at most `3·largeRad`. -/
lemma Acoord_large_card_le_three_largeRad {n : ℕ} {δ ν T : ℝ} {i : Fin n}
    (hi : ¬ smallIndex n δ (i.val)) :
    ((Acoord n δ ν T i).card : ℝ) ≤ 3 * (largeRad δ T : ℝ) := by
  have hcov : Acoord n δ ν T i = largeWin (largeRad δ T) := Acoord_of_large hi
  have hcard : (largeWin (largeRad δ T)).card = 2 * largeRad δ T + 1 := largeWin_card (largeRad δ T)
  have hR1n : 1 ≤ largeRad δ T := by
    unfold largeRad
    omega
  rw [hcov]
  rw [hcard]
  have hn : (2 * largeRad δ T + 1 : ℕ) ≤ 3 * largeRad δ T := by omega
  exact_mod_cast hn

end Submission.Section5D

end
