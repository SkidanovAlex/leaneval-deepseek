import Mathlib
import Submission.Threshold
import Submission.Admissible
import Submission.Commons.LinearAlgebra.Net.spread_permutations

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

noncomputable section

/-!
# Section 5d: coordinate windows for the net argument

This module lays the counting-layer foundation used by the net argument in
Tikhomirov's Theorem A (`cor: permutations` and `l: admissibility of A`).
We fix a coordinate family `A(n,δ,ν,T)` over `Fin n` whose windows
(`armWin` for small positions, `largeWin` for large positions) will carry
the reordered integer `spv` values from the special-permutation lemma.

The counting-layer interface facts needed downstream (by
`Submission.CorAc2.cor_anticoncentration`) are proved here:
`Admissible N n n δ (Acoord n δ ν T)` in counting-layer form (`N :=
⌊ν/T⌋−1`), origin symmetry, the radius bound, and window membership
characterizations used to push the reordered `spv` values into the family.
-/

open scoped BigOperators ENNReal

namespace Submission.Section5D

attribute [local instance] Classical.propDecidable

open Submission.Admissible
open Commons.LinearAlgebra.Net

/-- The 1-based position of a `Fin n` coordinate. -/
noncomputable def posOf {n : ℕ} (i : Fin n) : ℕ := (i : ℕ) + 1

/-- hole lower bound `⌊ν/T⌋` (a natural). -/
noncomputable def keepMag (ν T : ℝ) : ℕ := ⌊ν / T⌋₊

/-- hole half-width `N := ⌊ν/T⌋−1`. -/
noncomputable def holeN (ν T : ℝ) : ℕ := ⌊ν / T⌋₊ - 1

/-- radius for a small coordinate with 1-based position `pos`. -/
noncomputable def smallRad (n : ℕ) (T : ℝ) (pos : ℕ) : ℕ :=
  ⌈4 * Real.sqrt (n : ℝ) / (T * Real.sqrt (pos : ℝ))⌉₊ + 1

/-- radius for the large coordinates. -/
noncomputable def largeRad (δ T : ℝ) : ℕ :=
  ⌈Real.sqrt 8 / (Real.sqrt δ * T)⌉₊ + 1

/-- window at a small position: two arms `[h, R]` and `[−R, −h]`. -/
noncomputable def armWin (h R : ℕ) : Finset ℤ :=
  Finset.Icc (h : ℤ) (R : ℤ) ∪ Finset.Icc (-(R : ℤ)) (-(h : ℤ))

/-- window at a large position: the single interval `[−R, R]`. -/
noncomputable def largeWin (R : ℕ) : Finset ℤ :=
  Finset.Icc (-(R : ℤ)) (R : ℤ)

/-- the Section-5d coordinate family `A(n,δ,ν,T)` over `Fin n`. -/
noncomputable def Acoord (n : ℕ) (δ ν T : ℝ) (i : Fin n) : Finset ℤ :=
  let pos : ℕ := (i : ℕ) + 1
  if smallIndex n δ (i.val) then armWin (keepMag ν T) (smallRad n T pos)
  else largeWin (largeRad δ T)

/-- `Acoord` at a small coordinate is the arm window. -/
lemma Acoord_of_small {n : ℕ} {δ ν T : ℝ} {i : Fin n} (hi : smallIndex n δ (i.val)) :
    Acoord n δ ν T i = armWin (keepMag ν T) (smallRad n T (posOf i)) := by
  classical
  simp [Acoord, posOf, hi]

/-- `Acoord` at a large coordinate is the single interval. -/
lemma Acoord_of_large {n : ℕ} {δ ν T : ℝ} {i : Fin n} (hi : ¬ smallIndex n δ (i.val)) :
    Acoord n δ ν T i = largeWin (largeRad δ T) := by
  classical
  simp [Acoord, posOf, hi]

/-- `smallIndex` is exactly "the 1-based position is at most `δ·n`". -/
lemma smallIndex_iff_pos_le {n : ℕ} {δ : ℝ} {i : Fin n} :
    smallIndex n δ (i.val) ↔ ((posOf i : ℝ) ≤ δ * (n : ℝ)) := by
  unfold smallIndex posOf
  rw [Nat.cast_add, Nat.cast_one]

/-- membership in the positive arm. -/
lemma mem_armWin_pos {h R : ℕ} {a : ℤ} (hh : (h : ℤ) ≤ a) (ha : a ≤ (R : ℤ)) :
    a ∈ armWin h R := by
  unfold armWin
  exact Finset.mem_union.mpr (Or.inl (Finset.mem_Icc.mpr ⟨hh, ha⟩))

/-- membership in the negative arm. -/
lemma mem_armWin_neg {h R : ℕ} {a : ℤ} (hh : -(R : ℤ) ≤ a) (ha : a ≤ -(h : ℤ)) :
    a ∈ armWin h R := by
  unfold armWin
  exact Finset.mem_union.mpr (Or.inr (Finset.mem_Icc.mpr ⟨hh, ha⟩))

/-- membership in `armWin`: `|a|` between `h` and `R` (integer absolute
values). -/
lemma mem_armWin_iff {h R : ℕ} (a : ℤ) :
    a ∈ armWin h R ↔ (h : ℤ) ≤ |a| ∧ |a| ≤ (R : ℤ) := by
  classical
  constructor
  · intro ha
    unfold armWin at ha
    rw [Finset.mem_union, Finset.mem_Icc, Finset.mem_Icc] at ha
    rcases ha with hpos | hneg
    · rcases hpos with ⟨hh, haR⟩
      have ha0 : 0 ≤ a := by
        have hz : (0 : ℤ) ≤ (h : ℤ) := by exact_mod_cast (Nat.zero_le h)
        exact le_trans hz hh
      have habs : |a| = a := abs_of_nonneg ha0
      constructor
      · simpa [habs] using hh
      · simpa [habs] using haR
    · rcases hneg with ⟨h1, h2⟩
      have ha0 : a ≤ 0 := by
        have hh0 : -(h : ℤ) ≤ 0 := by linarith [show (0 : ℤ) ≤ (h : ℤ) by exact_mod_cast (Nat.zero_le h)]
        exact le_trans h2 hh0
      have habs : |a| = -a := abs_of_nonpos ha0
      constructor
      · have hh : (h : ℤ) ≤ -a := by linarith
        simpa [habs] using hh
      · have hh : -a ≤ (R : ℤ) := by linarith
        simpa [habs] using hh
  · intro habs
    rcases habs with ⟨hh, hR⟩
    by_cases ha0 : 0 ≤ a
    · rw [abs_of_nonneg ha0] at hh hR
      exact mem_armWin_pos hh hR
    · have ha0' : a ≤ 0 := le_of_not_ge ha0
      rw [abs_of_nonpos ha0'] at hh hR
      exact mem_armWin_neg (by linarith) (by linarith)

/-- membership in the large window: `|a| ≤ R` (integer abs). -/
lemma mem_largeWin_iff {R : ℕ} (a : ℤ) :
    a ∈ largeWin R ↔ |a| ≤ (R : ℤ) := by
  classical
  unfold largeWin
  rw [Finset.mem_Icc]
  constructor
  · intro h
    rcases h with ⟨h1, h2⟩
    exact abs_le.mpr ⟨h1, h2⟩
  · intro h
    exact abs_le.mp h

/-- symmetry of the arm window. -/
lemma mem_armWin_neg_of_mem {h R : ℕ} {x : ℤ} (hx : x ∈ armWin h R) :
    -x ∈ armWin h R := by
  have habs := (mem_armWin_iff (h := h) (R := R) x).mp hx
  have hneg : |(-x : ℤ)| = |x| := by simp
  rw [mem_armWin_iff]
  rw [hneg]
  exact habs

/-- symmetry of the large window. -/
lemma mem_largeWin_neg_of_mem {R : ℕ} {a : ℤ} (h : a ∈ largeWin R) :
    -a ∈ largeWin R := by
  rw [mem_largeWin_iff] at h ⊢
  simpa using h

/-- `Acoord` origin symmetry. -/
lemma Acoord_symm {n : ℕ} {δ ν T : ℝ} {i : Fin n} {a : ℤ}
    (h : a ∈ Acoord n δ ν T i) :
    -a ∈ Acoord n δ ν T i := by
  by_cases hi : smallIndex n δ (i.val)
  · rw [Acoord_of_small hi] at h ⊢
    exact mem_armWin_neg_of_mem h
  · rw [Acoord_of_large hi] at h ⊢
    exact mem_largeWin_neg_of_mem h

/-- membership of a reordered `spv` value at a small coordinate (integer
magnitudes between the hole bound and the radius). -/
lemma Acoord_mem_of_small {n : ℕ} {δ ν T : ℝ} {i : Fin n} (hi : smallIndex n δ (i.val))
    {a : ℤ} (h1 : (keepMag ν T : ℤ) ≤ |a|) (h2 : |a| ≤ (smallRad n T (posOf i) : ℤ)) :
    a ∈ Acoord n δ ν T i := by
  rw [Acoord_of_small hi]
  exact (mem_armWin_iff (h := keepMag ν T) (R := smallRad n T (posOf i)) a).mpr ⟨h1, h2⟩

/-- membership of a reordered `spv` value at a large coordinate. -/
lemma Acoord_mem_of_large {n : ℕ} {δ ν T : ℝ} {i : Fin n} (hi : ¬ smallIndex n δ (i.val))
    {a : ℤ} (h : |a| ≤ (largeRad δ T : ℤ)) :
    a ∈ Acoord n δ ν T i := by
  rw [Acoord_of_large hi]
  exact (mem_largeWin_iff (R := largeRad δ T) a).mpr h

/-- the real absolute value is the cast of the integer one. -/
lemma real_abs_eq_int {a : ℤ} : |(a : ℝ)| = ((Int.natAbs a : ℕ) : ℝ) := by
  rw [← Int.cast_abs]
  exact congrArg (fun z : ℤ => (z : ℝ)) (Int.abs_eq_natAbs a)

/-- elements of a small-coordinate window have magnitude `≥ ⌊ν/T⌋`. -/
lemma Acoord_lower_small {n : ℕ} {δ ν T : ℝ} {i : Fin n} (hi : smallIndex n δ (i.val))
    {a : ℤ} (h : a ∈ Acoord n δ ν T i) :
    (keepMag ν T : ℤ) ≤ |a| := by
  rw [Acoord_of_small hi] at h
  exact ((mem_armWin_iff (h := keepMag ν T) (R := smallRad n T (posOf i)) a).mp h).1

/-- elements of a small-coordinate window have magnitude `≤ R(pos)`. -/
lemma Acoord_upper_small {n : ℕ} {δ ν T : ℝ} {i : Fin n} (hi : smallIndex n δ (i.val))
    {a : ℤ} (h : a ∈ Acoord n δ ν T i) :
    |a| ≤ (smallRad n T (posOf i) : ℤ) := by
  rw [Acoord_of_small hi] at h
  exact ((mem_armWin_iff (h := keepMag ν T) (R := smallRad n T (posOf i)) a).mp h).2

/-- elements of a large-coordinate window have magnitude `≤ R∞`. -/
lemma Acoord_upper_large {n : ℕ} {δ ν T : ℝ} {i : Fin n} (hi : ¬ smallIndex n δ (i.val))
    {a : ℤ} (h : a ∈ Acoord n δ ν T i) :
    |a| ≤ (largeRad δ T : ℤ) := by
  rw [Acoord_of_large hi] at h
  exact (mem_largeWin_iff (R := largeRad δ T) a).mp h

/-- the two arms are disjoint once the lower end is at least `1`. -/
lemma armWin_arms_disjoint {h R : ℕ} (hh : 1 ≤ h) :
    Disjoint (Finset.Icc (h : ℤ) (R : ℤ)) (Finset.Icc (-(R : ℤ)) (-(h : ℤ))) := by
  rw [Finset.disjoint_left]
  intro a h1 h2
  have h1' : (h : ℤ) ≤ a := (Finset.mem_Icc.mp h1).1
  have h2' : a ≤ -(h : ℤ) := (Finset.mem_Icc.mp h2).2
  have hz : (1 : ℤ) ≤ (h : ℤ) := by exact_mod_cast hh
  have : a ≥ (h : ℤ) := h1'
  have : a ≤ -(h : ℤ) := h2'
  have : -(h : ℤ) < (h : ℤ) := by omega
  omega

/-- an arm-window element has magnitude at least the hole bound (integer). -/
lemma armWin_abs_ge {h R : ℕ} {a : ℤ} (hmem : a ∈ armWin h R) :
    (h : ℤ) ≤ |a| := by
  exact (mem_armWin_iff (h := h) (R := R) a).mp hmem |>.1

/-- an arm-window element has magnitude greater than `h − 1` in reals. -/
lemma armWin_real_gt_sub_one {h : ℕ} {R : ℕ} {a : ℤ} (hh : 1 ≤ h)
    (hmem : a ∈ armWin h R) :
    (h : ℝ) - 1 < |(a : ℝ)| := by
  have hge : (h : ℤ) ≤ |a| := armWin_abs_ge hmem
  have hR0 : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
  have hcast : (h : ℝ) ≤ |(a : ℝ)| := by
    -- |a| : ℤ ≤ ... then cast: (h:ℝ) ≤ ((|a|:ℤ):ℝ); (|a|:ℤ):ℝ = |(a:ℝ)|
    have hz : ((h : ℤ) : ℝ) ≤ ((|a| : ℤ) : ℝ) := by exact_mod_cast hge
    rwa [Int.cast_abs] at hz
  linarith

/-- an arm-window element has magnitude at most the radius (real). -/
lemma armWin_real_le {h R : ℕ} {a : ℤ} (hmem : a ∈ armWin h R) :
    |(a : ℝ)| ≤ (R : ℝ) := by
  have hle : |a| ≤ (R : ℤ) := (mem_armWin_iff (h := h) (R := R) a).mp hmem |>.2
  have hz : ((|a| : ℤ) : ℝ) ≤ ((R : ℤ) : ℝ) := by exact_mod_cast hle
  rwa [Int.cast_abs] at hz

/-- a large-window element has magnitude at most the radius (real). -/
lemma largeWin_real_le {R : ℕ} {a : ℤ} (hmem : a ∈ largeWin R) :
    |(a : ℝ)| ≤ (R : ℝ) := by
  have hle : |a| ≤ (R : ℤ) := (mem_largeWin_iff (R := R) a).mp hmem
  have hz : ((|a| : ℤ) : ℝ) ≤ ((R : ℤ) : ℝ) := by exact_mod_cast hle
  rwa [Int.cast_abs] at hz

lemma int_abs_le_of_real_le {R : ℕ} {a : ℤ} (h : |(a : ℝ)| ≤ (R : ℝ)) :
    |a| ≤ (R : ℤ) := by
  have hc : ((|a| : ℤ) : ℝ) ≤ (R : ℝ) := by
    simpa [Int.cast_abs] using h
  exact_mod_cast hc

/-- integer `h ≤ |a|` from the real bound. -/
lemma int_abs_ge_of_real_ge {hm : ℕ} {a : ℤ} (hh : (hm : ℝ) ≤ |(a : ℝ)|) :
    (hm : ℤ) ≤ |a| := by
  have hc : (hm : ℝ) ≤ ((|a| : ℤ) : ℝ) := by
    simpa [Int.cast_abs] using hh
  exact_mod_cast hc

/-- membership at a small coordinate from real magnitude bounds. -/
lemma Acoord_mem_of_small_real {n : ℕ} {δ ν T : ℝ} {i : Fin n} (hi : smallIndex n δ (i.val))
    {a : ℤ} (h1 : (keepMag ν T : ℝ) ≤ |(a : ℝ)|)
    (h2 : |(a : ℝ)| ≤ (smallRad n T (posOf i) : ℝ)) :
    a ∈ Acoord n δ ν T i := by
  exact Acoord_mem_of_small hi (int_abs_ge_of_real_ge h1) (int_abs_le_of_real_le h2)

/-- membership at a large coordinate from a real magnitude bound. -/
lemma Acoord_mem_of_large_real {n : ℕ} {δ ν T : ℝ} {i : Fin n} (hi : ¬ smallIndex n δ (i.val))
    {a : ℤ} (h : |(a : ℝ)| ≤ (largeRad δ T : ℝ)) :
    a ∈ Acoord n δ ν T i := by
  exact Acoord_mem_of_large hi (int_abs_le_of_real_le h)

/-- keepMag = holeN + 1 when `⌊ν/T⌋ ≥ 1`. -/
lemma keepMag_eq_holeN_add_one {ν T : ℝ} (h : 1 ≤ ⌊ν / T⌋₊) :
    keepMag ν T = holeN ν T + 1 := by
  unfold keepMag holeN
  omega




/-! ## Counting-layer window structure (Lemma l: admissibility of A)

The coordinate family `Acoord n δ ν T : Fin n → Finset ℤ` is used in the
net argument as the counting-layer coordinate family to which `CorAc2`'s
anticoncentration lemma is applied.  That interface needs, for the natural
`N := holeN ν T = ⌊ν/T⌋−1`:

* at a *small* coordinate (position `pos ≤ δn`): the window is the union of
  the two disjoint intervals `Icc (⌊ν/T⌋) R` and `Icc (−R) (−⌊ν/T⌋)`, each
  of cardinality `≥ N`, and every element has magnitude `> N`;
* at a *large* coordinate: the window is the single interval
  `Icc (−R∞) R∞` of cardinality `≥ N`.
-/

/-- the two arms of a small-coordinate window (set identity). -/
lemma Acoord_small_union {n : ℕ} {δ ν T : ℝ} {i : Fin n} (hi : smallIndex n δ (i.val)) :
    Acoord n δ ν T i =
      Finset.Icc (keepMag ν T : ℤ) (smallRad n T (posOf i) : ℤ) ∪
      Finset.Icc (-(smallRad n T (posOf i) : ℤ)) (-(keepMag ν T : ℤ)) := by
  rw [Acoord_of_small hi]
  rfl

/-- cardinality of `Icc (h:ℤ) (R:ℤ)` for naturals `h ≤ R`. -/
lemma card_Icc_nat (h R : ℕ) (hR : h ≤ R) :
    (Finset.Icc (h : ℤ) (R : ℤ)).card = R - h + 1 := by
  rw [Int.card_Icc]
  have hmain : ((R : ℤ) + 1 - (h : ℤ)) = ((R - h + 1 : ℕ) : ℤ) := by
    calc (R : ℤ) + 1 - (h : ℤ) = ((R : ℤ) - (h : ℤ)) + 1 := by omega
    _ = ((R - h : ℕ) : ℤ) + 1 := by rw [← Nat.cast_sub hR]
    _ = ((R - h + 1 : ℕ) : ℤ) := by norm_num [Nat.cast_add, Nat.cast_one]
  rw [hmain]
  have hn : (0 : ℤ) ≤ ((R - h + 1 : ℕ) : ℤ) := by positivity
  have hres := Int.toNat_of_nonneg hn
  exact_mod_cast hres

/-- cardinality of `Icc (−(R:ℤ)) (−(h:ℤ))` for naturals `h ≤ R`. -/
lemma card_Icc_neg_nat (h R : ℕ) (hR : h ≤ R) :
    (Finset.Icc (-(R : ℤ)) (-(h : ℤ))).card = R - h + 1 := by
  rw [Int.card_Icc]
  have hmain : ((-(h : ℤ)) + 1 - (-(R : ℤ))) = ((R - h + 1 : ℕ) : ℤ) := by
    calc -(h : ℤ) + 1 - (-(R : ℤ)) = ((R : ℤ) - (h : ℤ)) + 1 := by ring
    _ = ((R - h : ℕ) : ℤ) + 1 := by rw [← Nat.cast_sub hR]
    _ = ((R - h + 1 : ℕ) : ℤ) := by norm_num [Nat.cast_add, Nat.cast_one]
  rw [hmain]
  have hn : (0 : ℤ) ≤ ((R - h + 1 : ℕ) : ℤ) := by positivity
  have hres := Int.toNat_of_nonneg hn
  exact_mod_cast hres

/-- each arm of a small-coordinate window has cardinality `≥ ⌊ν/T⌋−1 = holeN`,
provided the radius is at least `2⌊ν/T⌋−2` (and `⌊ν/T⌋ ≥ 2`). -/
lemma arm_card_ge_holeN {ν T : ℝ} (hνT : 2 ≤ ⌊ν / T⌋₊) {R : ℕ}
    (hR2 : 2 * (⌊ν / T⌋₊ : ℕ) - 2 ≤ R) :
    (holeN ν T : ℤ) ≤ (R : ℤ) - (keepMag ν T : ℤ) + 1 := by
  let h : ℕ := ⌊ν / T⌋₊
  have h2 : 2 ≤ h := hνT
  have hhR : h ≤ R := by
    have : h ≤ 2 * h - 2 := by omega
    exact le_trans this hR2
  have hn : (h - 1 : ℕ) ≤ R - h + 1 := by omega
  have hn2 : (h - 1 : ℕ) ≤ R := by omega
  have hnz : (0 : ℤ) ≤ ((h - 1 : ℕ) : ℤ) := by positivity
  have hz1 : (((h - 1 : ℕ) : ℤ)) ≤ (((R - h + 1 : ℕ) : ℤ)) := by
    exact_mod_cast hn
  have hsub : ((R - h : ℕ) : ℤ) = (R : ℤ) - (h : ℤ) := by
    rw [Nat.cast_sub hhR]
  have hz2 : (((R - h + 1 : ℕ) : ℤ)) = ((R : ℤ) - ((h : ℤ)) + 1) := by
    have hadd : (((R - h + 1 : ℕ) : ℤ)) = (((R - h : ℕ) : ℤ) + 1) := by
      norm_num [Nat.cast_add]
    rw [hadd, hsub]
  rwa [hz2] at hz1

end Submission.Section5D

end