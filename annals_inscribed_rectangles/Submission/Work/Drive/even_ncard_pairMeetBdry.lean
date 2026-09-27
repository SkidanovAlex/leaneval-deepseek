import Mathlib
import Submission.Work.Drive.pairMeetDefs
import Submission.Work.Drive.boxParity
import Submission.Work.Drive.SeamMeetDefs
import Submission.Work.Drive.SeamSweep
import Submission.Work.Drive.bdry_label_parity

/-!
# The parity of the pair-meet counts at the two ends of the collapse family

`Work.Drive.even_ncard_pairMeetBdry` is the box-level form of the bordism invariance of the pair-meet
count of the radial-collapse transport (`Submission/Work/Drive/pairMeetDefs.lean`): the two end
counts `K 0 = #pairMeetSet E E' V W 0` and `K 1 = #pairMeetSet E E' V W 1` have the same parity.

The difference map `F = pairDiff E E' V W : ℝ⁹ → ℝ⁸` is smooth, and on the `9`-box
`Submission.Drive.ParityProp` (`Work.Drive.boxParity`) applies: the number of *boundary* zeros of `F`
is even.  Grouping the `9` faces of the box by the block of coordinates they belong to (`label9`) and
using the seam invariance of the four chains `E, E', V, W` and the absence of zeros on the two
*level* faces (`havY`, `havZ`):

* the family-parameter faces `x 0 ∈ {0,1}` carry exactly the pair-meet counts `K 0` and `K 1`
  (`endFace`, the bijection `ncard_endFace`);
* the plane-seam faces `x 1, x 2 ∈ {0,1}` are paired by the antipodal involution `seamInv2` of the
  plane parameter square (`hseamU`, `hseamU'`);
* the sweep-seam faces `x 3, x 4 ∈ {0,1}` (resp. `x 6, x 7 ∈ {0,1}`) are paired by the antipodal
  involution `seamInv` of the sweep parameter cube (`hseamV`, resp. `hseamW`);
* the level faces `x 5 ∈ {0,1}` and `x 8 ∈ {0,1}` carry no boundary zero at all (`havY`, `havZ`).

Hence `K 0 + K 1 ≡ 0 (mod 2)`.
-/

set_option autoImplicit false

namespace Work.Drive

open Submission.Drive
open scoped ContDiff Topology

noncomputable section

namespace PMB

/-! ## 1. The coordinate dictionary of the `9`-box -/

/-- The point of the `9`-box with family parameter `s`, plane parameter `u` and sweep parameters `y`
and `z`: coordinates `0, 1, 2` are `s, u 0, u 1`, coordinates `3, 4, 5` are `y`, and coordinates
`6, 7, 8` are `z`. -/
def mk9 (s : ℝ) (u : EuclideanSpace ℝ (Fin 2)) (y z : EuclideanSpace ℝ (Fin 3)) : Amb 8 :=
  WithLp.toLp 2 (fun i : Fin 9 => ![s, u 0, u 1, y 0, y 1, y 2, z 0, z 1, z 2] i)

@[simp] lemma mk9_apply_zero (s : ℝ) (u : EuclideanSpace ℝ (Fin 2))
    (y z : EuclideanSpace ℝ (Fin 3)) : mk9 s u y z 0 = s := by simp [mk9]

@[simp] lemma mk9_apply_one (s : ℝ) (u : EuclideanSpace ℝ (Fin 2))
    (y z : EuclideanSpace ℝ (Fin 3)) : mk9 s u y z 1 = u 0 := by simp [mk9]

@[simp] lemma mk9_apply_two (s : ℝ) (u : EuclideanSpace ℝ (Fin 2))
    (y z : EuclideanSpace ℝ (Fin 3)) : mk9 s u y z 2 = u 1 := by simp [mk9]

@[simp] lemma mk9_apply_three (s : ℝ) (u : EuclideanSpace ℝ (Fin 2))
    (y z : EuclideanSpace ℝ (Fin 3)) : mk9 s u y z 3 = y 0 := by simp [mk9]

@[simp] lemma mk9_apply_four (s : ℝ) (u : EuclideanSpace ℝ (Fin 2))
    (y z : EuclideanSpace ℝ (Fin 3)) : mk9 s u y z 4 = y 1 := by simp [mk9]

@[simp] lemma mk9_apply_five (s : ℝ) (u : EuclideanSpace ℝ (Fin 2))
    (y z : EuclideanSpace ℝ (Fin 3)) : mk9 s u y z 5 = y 2 := by simp [mk9]

@[simp] lemma mk9_apply_six (s : ℝ) (u : EuclideanSpace ℝ (Fin 2))
    (y z : EuclideanSpace ℝ (Fin 3)) : mk9 s u y z 6 = z 0 := by simp [mk9]

@[simp] lemma mk9_apply_seven (s : ℝ) (u : EuclideanSpace ℝ (Fin 2))
    (y z : EuclideanSpace ℝ (Fin 3)) : mk9 s u y z 7 = z 1 := by simp [mk9]

@[simp] lemma mk9_apply_eight (s : ℝ) (u : EuclideanSpace ℝ (Fin 2))
    (y z : EuclideanSpace ℝ (Fin 3)) : mk9 s u y z 8 = z 2 := by simp [mk9]

@[simp] lemma ftS_mk9 (s : ℝ) (u : EuclideanSpace ℝ (Fin 2)) (y z : EuclideanSpace ℝ (Fin 3)) :
    ftS (mk9 s u y z) = s := by simp [mk9, ftS]

@[simp] lemma ftU_mk9 (s : ℝ) (u : EuclideanSpace ℝ (Fin 2)) (y z : EuclideanSpace ℝ (Fin 3)) :
    ftU (mk9 s u y z) = u := by
  ext i
  fin_cases i <;> simp [mk9, ftU, WithLp.ofLp_toLp]

@[simp] lemma ftY_mk9 (s : ℝ) (u : EuclideanSpace ℝ (Fin 2)) (y z : EuclideanSpace ℝ (Fin 3)) :
    ftY (mk9 s u y z) = y := by
  ext i
  fin_cases i <;> simp [mk9, ftY, WithLp.ofLp_toLp]

@[simp] lemma ftZ_mk9 (s : ℝ) (u : EuclideanSpace ℝ (Fin 2)) (y z : EuclideanSpace ℝ (Fin 3)) :
    ftZ (mk9 s u y z) = z := by
  ext i
  fin_cases i <;> simp [mk9, ftZ, WithLp.ofLp_toLp]

lemma ftU_apply (x : Amb 8) (i : Fin 2) : ftU x i = x ⟨1 + i.val, by omega⟩ := by
  simp [ftU, WithLp.ofLp_toLp]

lemma ftY_apply (x : Amb 8) (i : Fin 3) : ftY x i = x ⟨3 + i.val, by omega⟩ := by
  simp [ftY, WithLp.ofLp_toLp]

lemma ftZ_apply (x : Amb 8) (i : Fin 3) : ftZ x i = x ⟨6 + i.val, by omega⟩ := by
  simp [ftZ, WithLp.ofLp_toLp]

lemma ftU_zero (x : Amb 8) : ftU x 0 = x 1 := by simp [ftU, WithLp.ofLp_toLp]

lemma ftU_one (x : Amb 8) : ftU x 1 = x 2 := by simp [ftU, WithLp.ofLp_toLp]

lemma ftY_zero (x : Amb 8) : ftY x 0 = x 3 := by simp [ftY, WithLp.ofLp_toLp]

lemma ftY_one (x : Amb 8) : ftY x 1 = x 4 := by simp [ftY, WithLp.ofLp_toLp]

lemma ftZ_zero (x : Amb 8) : ftZ x 0 = x 6 := by simp [ftZ, WithLp.ofLp_toLp]

lemma ftZ_one (x : Amb 8) : ftZ x 1 = x 7 := by simp [ftZ, WithLp.ofLp_toLp]

lemma ftY2_eq_coord (x : Amb 8) : ftY2 x = x 5 := by simp [ftY2]

lemma ftZ2_eq_coord (x : Amb 8) : ftZ2 x = x 8 := by simp [ftZ2]

/-- **The coordinate dictionary in the other direction**: every point of the `9`-box is recovered from
its family parameter, its plane parameter and its two sweep parameters. -/
lemma mk9_ft (x : Amb 8) : mk9 (ftS x) (ftU x) (ftY x) (ftZ x) = x := by
  ext i
  fin_cases i <;> simp [mk9, ftS, ftU, ftY, ftZ, WithLp.ofLp_toLp]

/-- The value of the pair difference map on the point `mk9 s u y z`. -/
lemma pairDiff_mk9 (E : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (E' : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (V W : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    (s : ℝ) (u : EuclideanSpace ℝ (Fin 2)) (y z : EuclideanSpace ℝ (Fin 3)) :
    pairDiff E E' V W (mk9 s u y z) = pair44 (E s u - V y) (E' u - W z) := by
  simp only [pairDiff, ftS_mk9, ftU_mk9, ftY_mk9, ftZ_mk9]

lemma pair44_zero : pair44 (0 : EuclideanSpace ℝ (Fin 4)) 0 = 0 := by
  ext i
  fin_cases i <;> simp [pair44]

/-- **Box membership of `mk9`.** -/
lemma mk9_mem_unitBox {s : ℝ} {u : EuclideanSpace ℝ (Fin 2)} {y z : EuclideanSpace ℝ (Fin 3)}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (hu : u ∈ Submission.Drive.unitBox 1)
    (hy : y ∈ Submission.Drive.unitBox 2) (hz : z ∈ Submission.Drive.unitBox 2) :
    mk9 s u y z ∈ Submission.Drive.unitBox 8 := by
  intro i
  fin_cases i
  · simpa [mk9] using hs
  · simpa [mk9] using hu 0
  · simpa [mk9] using hu 1
  · simpa [mk9] using hy 0
  · simpa [mk9] using hy 1
  · simpa [mk9] using hy 2
  · simpa [mk9] using hz 0
  · simpa [mk9] using hz 1
  · simpa [mk9] using hz 2

/-- **Boundary membership of `mk9`** for a family parameter on the boundary of `[0,1]`. -/
lemma mk9_mem_unitBoxBdry {s : ℝ} {u : EuclideanSpace ℝ (Fin 2)} {y z : EuclideanSpace ℝ (Fin 3)}
    (hs : s = 0 ∨ s = 1) (hbox : mk9 s u y z ∈ Submission.Drive.unitBox 8) :
    mk9 s u y z ∈ Submission.Drive.unitBoxBdry 8 := by
  rw [Submission.Drive.unitBoxBdry, Set.mem_ofPred_eq]
  refine ⟨hbox, 0, ?_⟩
  rcases hs with h | h <;> simp [mk9, h]

/-! ## 2. The labelling of the nine faces of the box

The nine coordinates of the box split into the blocks `0` (the family parameter), `1, 2` (the plane
parameter), `3, 4` (the first sweep parameter), `6, 7` (the second sweep parameter) and the two
*level* coordinates `5` and `8`.  `label9` records the block of each coordinate: two coordinates of
the same block are the two faces of one seam identification. -/

/-- The block of each of the nine coordinates. -/
def label9 : Fin 9 → Fin 5 := ![0, 1, 1, 2, 2, 4, 3, 3, 4]

lemma label9_zero {i : Fin 9} : label9 i = 0 ↔ i = 0 := by fin_cases i <;> decide

lemma label9_one {i : Fin 9} : label9 i = 1 ↔ (i = 1 ∨ i = 2) := by fin_cases i <;> decide

lemma label9_two {i : Fin 9} : label9 i = 2 ↔ (i = 3 ∨ i = 4) := by fin_cases i <;> decide

lemma label9_three {i : Fin 9} : label9 i = 3 ↔ (i = 6 ∨ i = 7) := by fin_cases i <;> decide

lemma label9_four {i : Fin 9} : label9 i = 4 ↔ (i = 5 ∨ i = 8) := by fin_cases i <;> decide

/-! ## 3. The five groups of boundary faces -/

/-- The family-parameter faces `x 0 = s` of the box. -/
abbrev endFace (F : Amb 8 → Tgt 8) (s : ℝ) : Set (Amb 8) := {x | x ∈ bdyZeros F ∧ ftS x = s}

/-- The plane-seam faces `x 1 ∈ {0,1}`, `x 2 ∈ {0,1}`. -/
abbrev uPart (F : Amb 8 → Tgt 8) : Set (Amb 8) := labelMeet F label9 1

/-- The first sweep-seam faces `x 3 ∈ {0,1}`, `x 4 ∈ {0,1}`. -/
abbrev yPart (F : Amb 8 → Tgt 8) : Set (Amb 8) := labelMeet F label9 2

/-- The second sweep-seam faces `x 6 ∈ {0,1}`, `x 7 ∈ {0,1}`. -/
abbrev zPart (F : Amb 8 → Tgt 8) : Set (Amb 8) := labelMeet F label9 3

/-- The two *level* faces `x 5 ∈ {0,1}`, `x 8 ∈ {0,1}` (the top and bottom faces of the sweeps). -/
abbrev lvlPart (F : Amb 8 → Tgt 8) : Set (Amb 8) := labelMeet F label9 4

lemma mem_endFace {F : Amb 8 → Tgt 8} {s : ℝ} {x : Amb 8} :
    x ∈ endFace F s ↔ x ∈ bdyZeros F ∧ ftS x = s := Iff.rfl

lemma mem_uPart {F : Amb 8 → Tgt 8} {x : Amb 8} :
    x ∈ uPart F ↔ x ∈ bdyZeros F ∧ ((x 1 = 0 ∨ x 1 = 1) ∨ (x 2 = 0 ∨ x 2 = 1)) := by
  rw [uPart, labelMeet, Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hx, i, hi, hxi⟩
    refine ⟨hx, ?_⟩
    rcases label9_one.mp hi with rfl | rfl
    · exact Or.inl hxi
    · exact Or.inr hxi
  · rintro ⟨hx, h | h⟩
    · exact ⟨hx, 1, label9_one.mpr (Or.inl rfl), h⟩
    · exact ⟨hx, 2, label9_one.mpr (Or.inr rfl), h⟩

lemma mem_yPart {F : Amb 8 → Tgt 8} {x : Amb 8} :
    x ∈ yPart F ↔ x ∈ bdyZeros F ∧ ((x 3 = 0 ∨ x 3 = 1) ∨ (x 4 = 0 ∨ x 4 = 1)) := by
  rw [yPart, labelMeet, Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hx, i, hi, hxi⟩
    refine ⟨hx, ?_⟩
    rcases label9_two.mp hi with rfl | rfl
    · exact Or.inl hxi
    · exact Or.inr hxi
  · rintro ⟨hx, h | h⟩
    · exact ⟨hx, 3, label9_two.mpr (Or.inl rfl), h⟩
    · exact ⟨hx, 4, label9_two.mpr (Or.inr rfl), h⟩

lemma mem_zPart {F : Amb 8 → Tgt 8} {x : Amb 8} :
    x ∈ zPart F ↔ x ∈ bdyZeros F ∧ ((x 6 = 0 ∨ x 6 = 1) ∨ (x 7 = 0 ∨ x 7 = 1)) := by
  rw [zPart, labelMeet, Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hx, i, hi, hxi⟩
    refine ⟨hx, ?_⟩
    rcases label9_three.mp hi with rfl | rfl
    · exact Or.inl hxi
    · exact Or.inr hxi
  · rintro ⟨hx, h | h⟩
    · exact ⟨hx, 6, label9_three.mpr (Or.inl rfl), h⟩
    · exact ⟨hx, 7, label9_three.mpr (Or.inr rfl), h⟩

lemma mem_lvlPart {F : Amb 8 → Tgt 8} {x : Amb 8} :
    x ∈ lvlPart F ↔ x ∈ bdyZeros F ∧ ((x 5 = 0 ∨ x 5 = 1) ∨ (x 8 = 0 ∨ x 8 = 1)) := by
  rw [lvlPart, labelMeet, Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hx, i, hi, hxi⟩
    refine ⟨hx, ?_⟩
    rcases label9_four.mp hi with rfl | rfl
    · exact Or.inl hxi
    · exact Or.inr hxi
  · rintro ⟨hx, h | h⟩
    · exact ⟨hx, 5, label9_four.mpr (Or.inl rfl), h⟩
    · exact ⟨hx, 8, label9_four.mpr (Or.inr rfl), h⟩

/-- **The family-parameter group is the union of the two end faces.** -/
lemma labelMeet_zero_eq (F : Amb 8 → Tgt 8) :
    labelMeet F label9 0 = endFace F 0 ∪ endFace F 1 := by
  ext x
  constructor
  · intro hx
    rw [labelMeet, Set.mem_inter_iff, Set.mem_ofPred_eq] at hx
    obtain ⟨hbz, i, hi, hxi⟩ := hx
    rw [label9_zero] at hi
    subst hi
    rcases hxi with h | h
    · exact Or.inl ⟨hbz, by simpa [ftS] using h⟩
    · exact Or.inr ⟨hbz, by simpa [ftS] using h⟩
  · rintro (⟨hbz, h⟩ | ⟨hbz, h⟩)
    · exact ⟨hbz, 0, label9_zero.mpr rfl, Or.inl (by simpa [ftS] using h)⟩
    · exact ⟨hbz, 0, label9_zero.mpr rfl, Or.inr (by simpa [ftS] using h)⟩

lemma disjoint_endFace (F : Amb 8 → Tgt 8) : Disjoint (endFace F 0) (endFace F 1) := by
  rw [Set.disjoint_left]
  rintro x ⟨-, h0⟩ ⟨-, h1⟩
  rw [h0] at h1
  exact absurd h1 (by norm_num)

/-! ## 4. The two end faces are the pair-meet sets -/

/-- **The family-parameter face `x 0 = s` is the pair-meet set at the family parameter `s`**: the map
`x ↦ (ftU x, ftY x, ftZ x)` is a bijection onto the closed parameter box
`unitBox 1 × unitBox 2 × unitBox 2`. -/
lemma ncard_endFace (E : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (E' : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (V W : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    {s : ℝ} (hs : s = 0 ∨ s = 1) :
    (endFace (pairDiff E E' V W) s).ncard = (pairMeetSet E E' V W s).ncard := by
  have hs01 : s ∈ Set.Icc (0 : ℝ) 1 := by
    rcases hs with h | h <;> rw [h] <;> norm_num
  refine Set.ncard_congr (fun x _ => (ftU x, ftY x, ftZ x)) ?_ ?_ ?_
  · intro x hx
    obtain ⟨hbz, hsx⟩ := hx
    rw [mem_bdyZeros] at hbz
    obtain ⟨⟨hbox, -⟩, hzero⟩ := hbz
    have hd := (pairDiff_eq_zero_iff E E' V W x).mp hzero
    rw [pairMeetSet, Set.mem_ofPred_eq]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · show ∀ i : Fin 2, ftU x i ∈ Set.Icc (0 : ℝ) 1
      intro i
      rw [ftU_apply]
      exact hbox _
    · show ∀ i : Fin 3, ftY x i ∈ Set.Icc (0 : ℝ) 1
      intro i
      rw [ftY_apply]
      exact hbox _
    · show ∀ i : Fin 3, ftZ x i ∈ Set.Icc (0 : ℝ) 1
      intro i
      rw [ftZ_apply]
      exact hbox _
    · show E s (ftU x) = V (ftY x)
      rw [← hsx]
      exact hd.1
    · show E' (ftU x) = W (ftZ x)
      exact hd.2
  · intro x x' hx hx' h
    have h1 : ftU x = ftU x' := congrArg (fun p : EuclideanSpace ℝ (Fin 2) ×
      EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) => p.1) h
    have h2 : ftY x = ftY x' := congrArg (fun p : EuclideanSpace ℝ (Fin 2) ×
      EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) => p.2.1) h
    have h3 : ftZ x = ftZ x' := congrArg (fun p : EuclideanSpace ℝ (Fin 2) ×
      EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) => p.2.2) h
    rw [← mk9_ft x, ← mk9_ft x', h1, h2, h3, hx.2, hx'.2]
  · intro p hp
    rw [pairMeetSet, Set.mem_ofPred_eq] at hp
    obtain ⟨hu, hy, hz, h1, h2⟩ := hp
    refine ⟨mk9 s p.1 p.2.1 p.2.2, ?_, ?_⟩
    · refine ⟨?_, ftS_mk9 s p.1 p.2.1 p.2.2⟩
      rw [mem_bdyZeros, Submission.Drive.unitBoxBdry, Set.mem_ofPred_eq]
      refine ⟨⟨mk9_mem_unitBox hs01 hu hy hz, ?_⟩, ?_⟩
      · exact ⟨0, by rcases hs with h | h <;> simp [mk9, h]⟩
      · rw [pairDiff_mk9, h1, h2, sub_self, sub_self]
        exact pair44_zero
    · rw [ftU_mk9, ftY_mk9, ftZ_mk9]

/-! ## 5. The three seam involutions -/

/-- The antipodal involution of the plane parameter square, lifted to the `9`-box. -/
abbrev uInv (x : Amb 8) : Amb 8 := mk9 (ftS x) (seamInv2 (ftU x)) (ftY x) (ftZ x)

/-- The antipodal involution of the first sweep parameter, lifted to the `9`-box. -/
abbrev yInv (x : Amb 8) : Amb 8 := mk9 (ftS x) (ftU x) (seamInv (ftY x)) (ftZ x)

/-- The antipodal involution of the second sweep parameter, lifted to the `9`-box. -/
abbrev zInv (x : Amb 8) : Amb 8 := mk9 (ftS x) (ftU x) (ftY x) (seamInv (ftZ x))

@[simp] lemma ftS_uInv (x : Amb 8) : ftS (uInv x) = ftS x := by simp only [uInv, ftS_mk9]

@[simp] lemma ftU_uInv (x : Amb 8) : ftU (uInv x) = seamInv2 (ftU x) := by
  simp only [uInv, ftU_mk9]

@[simp] lemma ftY_uInv (x : Amb 8) : ftY (uInv x) = ftY x := by simp only [uInv, ftY_mk9]

@[simp] lemma ftZ_uInv (x : Amb 8) : ftZ (uInv x) = ftZ x := by simp only [uInv, ftZ_mk9]

@[simp] lemma ftS_yInv (x : Amb 8) : ftS (yInv x) = ftS x := by simp only [yInv, ftS_mk9]

@[simp] lemma ftU_yInv (x : Amb 8) : ftU (yInv x) = ftU x := by simp only [yInv, ftU_mk9]

@[simp] lemma ftY_yInv (x : Amb 8) : ftY (yInv x) = seamInv (ftY x) := by
  simp only [yInv, ftY_mk9]

@[simp] lemma ftZ_yInv (x : Amb 8) : ftZ (yInv x) = ftZ x := by simp only [yInv, ftZ_mk9]

@[simp] lemma ftS_zInv (x : Amb 8) : ftS (zInv x) = ftS x := by simp only [zInv, ftS_mk9]

@[simp] lemma ftU_zInv (x : Amb 8) : ftU (zInv x) = ftU x := by simp only [zInv, ftU_mk9]

@[simp] lemma ftY_zInv (x : Amb 8) : ftY (zInv x) = ftY x := by simp only [zInv, ftY_mk9]

@[simp] lemma ftZ_zInv (x : Amb 8) : ftZ (zInv x) = seamInv (ftZ x) := by
  simp only [zInv, ftZ_mk9]

lemma uInv_apply_one (x : Amb 8) : uInv x 1 = 1 - x 1 := by
  simp [uInv, mk9, ftU, WithLp.ofLp_toLp]

lemma uInv_apply_two (x : Amb 8) : uInv x 2 = 1 - x 2 := by
  simp [uInv, mk9, ftU, WithLp.ofLp_toLp]

lemma yInv_apply_three (x : Amb 8) : yInv x 3 = 1 - x 3 := by
  simp [yInv, mk9, ftY, WithLp.ofLp_toLp]

lemma yInv_apply_four (x : Amb 8) : yInv x 4 = 1 - x 4 := by
  simp [yInv, mk9, ftY, WithLp.ofLp_toLp]

lemma zInv_apply_six (x : Amb 8) : zInv x 6 = 1 - x 6 := by
  simp [zInv, mk9, ftZ, WithLp.ofLp_toLp]

lemma zInv_apply_seven (x : Amb 8) : zInv x 7 = 1 - x 7 := by
  simp [zInv, mk9, ftZ, WithLp.ofLp_toLp]

lemma seamInv2_invol (y : EuclideanSpace ℝ (Fin 2)) : seamInv2 (seamInv2 y) = y := by
  ext i
  fin_cases i <;> simp [seamInv2_apply_zero, seamInv2_apply_one]

lemma seamInv_invol (y : EuclideanSpace ℝ (Fin 3)) : seamInv (seamInv y) = y := by
  ext i
  fin_cases i <;> simp [seamInv]

lemma one_sub_mem_Icc (c : ℝ) : 1 - c ∈ Set.Icc (0 : ℝ) 1 ↔ c ∈ Set.Icc (0 : ℝ) 1 := by
  constructor <;> intro h <;> exact ⟨by linarith [h.1, h.2], by linarith [h.1, h.2]⟩

/-- The coordinate form of the plane seam involution. -/
lemma seamInv2_apply' (y : EuclideanSpace ℝ (Fin 2)) (i : Fin 2) : seamInv2 y i = 1 - y i := by
  fin_cases i <;> simp [seamInv2]

/-- The coordinate form of the sweep seam involution: the *level* coordinate `2` is fixed. -/
lemma seamInv_apply' (y : EuclideanSpace ℝ (Fin 3)) (i : Fin 3) :
    seamInv y i = if i = 2 then y 2 else 1 - y i := by
  fin_cases i <;> simp [seamInv]

lemma seamInv2_mem_unitBox_iff (y : EuclideanSpace ℝ (Fin 2)) :
    seamInv2 y ∈ Submission.Drive.unitBox 1 ↔ y ∈ Submission.Drive.unitBox 1 := by
  constructor
  · intro h i
    have hi := h i
    rw [seamInv2_apply'] at hi
    exact (one_sub_mem_Icc (y i)).mp hi
  · intro h i
    rw [seamInv2_apply']
    exact (one_sub_mem_Icc (y i)).mpr (h i)

lemma seamInv_mem_unitBox_iff (y : EuclideanSpace ℝ (Fin 3)) :
    seamInv y ∈ Submission.Drive.unitBox 2 ↔ y ∈ Submission.Drive.unitBox 2 := by
  constructor
  · intro h i
    have hi := h i
    rw [seamInv_apply'] at hi
    by_cases h2 : i = 2
    · rw [if_pos h2] at hi
      rwa [h2]
    · rw [if_neg h2] at hi
      exact (one_sub_mem_Icc (y i)).mp hi
  · intro h i
    rw [seamInv_apply']
    by_cases h2 : i = 2
    · rw [if_pos h2, h2]
      exact h 2
    · rw [if_neg h2]
      exact (one_sub_mem_Icc (y i)).mpr (h i)

lemma uInv_mem_unitBox {x : Amb 8} (hx : x ∈ Submission.Drive.unitBox 8) :
    uInv x ∈ Submission.Drive.unitBox 8 := by
  refine mk9_mem_unitBox ?_ ?_ ?_ ?_
  · simpa [ftS] using hx 0
  · exact (seamInv2_mem_unitBox_iff (ftU x)).mpr (fun i => by rw [ftU_apply]; exact hx _)
  · exact fun i => by rw [ftY_apply]; exact hx _
  · exact fun i => by rw [ftZ_apply]; exact hx _

lemma yInv_mem_unitBox {x : Amb 8} (hx : x ∈ Submission.Drive.unitBox 8) :
    yInv x ∈ Submission.Drive.unitBox 8 := by
  refine mk9_mem_unitBox ?_ ?_ ?_ ?_
  · simpa [ftS] using hx 0
  · exact fun i => by rw [ftU_apply]; exact hx _
  · exact (seamInv_mem_unitBox_iff (ftY x)).mpr (fun i => by rw [ftY_apply]; exact hx _)
  · exact fun i => by rw [ftZ_apply]; exact hx _

lemma zInv_mem_unitBox {x : Amb 8} (hx : x ∈ Submission.Drive.unitBox 8) :
    zInv x ∈ Submission.Drive.unitBox 8 := by
  refine mk9_mem_unitBox ?_ ?_ ?_ ?_
  · simpa [ftS] using hx 0
  · exact fun i => by rw [ftU_apply]; exact hx _
  · exact fun i => by rw [ftY_apply]; exact hx _
  · exact (seamInv_mem_unitBox_iff (ftZ x)).mpr (fun i => by rw [ftZ_apply]; exact hx _)

/-- **The pair difference map is invariant under the plane involution at a seam point.** -/
lemma pairDiff_uInv_mk (E : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (E' : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (V W : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    (hseamU : ∀ (s : ℝ) (u : EuclideanSpace ℝ (Fin 2)),
      onSeam2 u → E s (seamInv2 u) = E s u)
    (hseamU' : ∀ u : EuclideanSpace ℝ (Fin 2), onSeam2 u → E' (seamInv2 u) = E' u)
    (s : ℝ) (u : EuclideanSpace ℝ (Fin 2)) (y z : EuclideanSpace ℝ (Fin 3))
    (h : onSeam2 u) :
    pairDiff E E' V W (mk9 s (seamInv2 u) y z) = pairDiff E E' V W (mk9 s u y z) := by
  simp only [pairDiff_mk9, hseamU s u h, hseamU' u h]

lemma pairDiff_uInv (E : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (E' : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (V W : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    (hseamU : ∀ (s : ℝ) (u : EuclideanSpace ℝ (Fin 2)),
      onSeam2 u → E s (seamInv2 u) = E s u)
    (hseamU' : ∀ u : EuclideanSpace ℝ (Fin 2), onSeam2 u → E' (seamInv2 u) = E' u)
    (x : Amb 8) (h : onSeam2 (ftU x)) :
    pairDiff E E' V W (uInv x) = pairDiff E E' V W x := by
  rw [show uInv x = mk9 (ftS x) (seamInv2 (ftU x)) (ftY x) (ftZ x) from rfl]
  rw [pairDiff_uInv_mk E E' V W hseamU hseamU' (ftS x) (ftU x) (ftY x) (ftZ x) h,
    mk9_ft x]

/-- **The pair difference map is invariant under the first sweep involution at a seam point.** -/
lemma pairDiff_yInv_mk (E : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (E' : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (V W : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    (hseamV : ∀ y : EuclideanSpace ℝ (Fin 3), onSeam y → V (seamInv y) = V y)
    (s : ℝ) (u : EuclideanSpace ℝ (Fin 2)) (y z : EuclideanSpace ℝ (Fin 3))
    (h : onSeam y) :
    pairDiff E E' V W (mk9 s u (seamInv y) z) = pairDiff E E' V W (mk9 s u y z) := by
  simp only [pairDiff_mk9, hseamV y h]

lemma pairDiff_yInv (E : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (E' : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (V W : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    (hseamV : ∀ y : EuclideanSpace ℝ (Fin 3), onSeam y → V (seamInv y) = V y)
    (x : Amb 8) (h : onSeam (ftY x)) :
    pairDiff E E' V W (yInv x) = pairDiff E E' V W x := by
  rw [show yInv x = mk9 (ftS x) (ftU x) (seamInv (ftY x)) (ftZ x) from rfl]
  rw [pairDiff_yInv_mk E E' V W hseamV (ftS x) (ftU x) (ftY x) (ftZ x) h, mk9_ft x]

/-- **The pair difference map is invariant under the second sweep involution at a seam point.** -/
lemma pairDiff_zInv_mk (E : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (E' : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (V W : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    (hseamW : ∀ z : EuclideanSpace ℝ (Fin 3), onSeam z → W (seamInv z) = W z)
    (s : ℝ) (u : EuclideanSpace ℝ (Fin 2)) (y z : EuclideanSpace ℝ (Fin 3))
    (h : onSeam z) :
    pairDiff E E' V W (mk9 s u y (seamInv z)) = pairDiff E E' V W (mk9 s u y z) := by
  simp only [pairDiff_mk9, hseamW z h]

lemma pairDiff_zInv (E : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (E' : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (V W : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    (hseamW : ∀ z : EuclideanSpace ℝ (Fin 3), onSeam z → W (seamInv z) = W z)
    (x : Amb 8) (h : onSeam (ftZ x)) :
    pairDiff E E' V W (zInv x) = pairDiff E E' V W x := by
  rw [show zInv x = mk9 (ftS x) (ftU x) (ftY x) (seamInv (ftZ x)) from rfl]
  rw [pairDiff_zInv_mk E E' V W hseamW (ftS x) (ftU x) (ftY x) (ftZ x) h, mk9_ft x]

/-! ## 6. The seam groups carry an even number of boundary zeros -/

lemma onSeam2_ftU_of (x : Amb 8)
    (h : (x 1 = 0 ∨ x 1 = 1) ∨ (x 2 = 0 ∨ x 2 = 1)) : onSeam2 (ftU x) := by
  rcases h with (h | h) | (h | h)
  · exact Or.inl (by rw [ftU_zero, h])
  · exact Or.inr (Or.inl (by rw [ftU_zero, h]))
  · exact Or.inr (Or.inr (Or.inl (by rw [ftU_one, h])))
  · exact Or.inr (Or.inr (Or.inr (by rw [ftU_one, h])))

lemma onSeam_ftY_of (x : Amb 8)
    (h : (x 3 = 0 ∨ x 3 = 1) ∨ (x 4 = 0 ∨ x 4 = 1)) : onSeam (ftY x) := by
  rcases h with (h | h) | (h | h)
  · exact Or.inl (by rw [ftY_zero, h])
  · exact Or.inr (Or.inl (by rw [ftY_zero, h]))
  · exact Or.inr (Or.inr (Or.inl (by rw [ftY_one, h])))
  · exact Or.inr (Or.inr (Or.inr (by rw [ftY_one, h])))

lemma onSeam_ftZ_of (x : Amb 8)
    (h : (x 6 = 0 ∨ x 6 = 1) ∨ (x 7 = 0 ∨ x 7 = 1)) : onSeam (ftZ x) := by
  rcases h with (h | h) | (h | h)
  · exact Or.inl (by rw [ftZ_zero, h])
  · exact Or.inr (Or.inl (by rw [ftZ_zero, h]))
  · exact Or.inr (Or.inr (Or.inl (by rw [ftZ_one, h])))
  · exact Or.inr (Or.inr (Or.inr (by rw [ftZ_one, h])))

lemma uInv_mem (E : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (E' : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (V W : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    (hseamU : ∀ (s : ℝ) (u : EuclideanSpace ℝ (Fin 2)),
      onSeam2 u → E s (seamInv2 u) = E s u)
    (hseamU' : ∀ u : EuclideanSpace ℝ (Fin 2), onSeam2 u → E' (seamInv2 u) = E' u)
    {x : Amb 8} (hx : x ∈ uPart (pairDiff E E' V W)) :
    uInv x ∈ uPart (pairDiff E E' V W) := by
  rw [mem_uPart] at hx
  obtain ⟨hbz, hco⟩ := hx
  rw [mem_bdyZeros] at hbz
  obtain ⟨⟨hbox, -⟩, hzero⟩ := hbz
  have hsU := onSeam2_ftU_of x hco
  rw [mem_uPart]
  refine ⟨?_, ?_⟩
  · rw [mem_bdyZeros, Submission.Drive.unitBoxBdry, Set.mem_ofPred_eq]
    refine ⟨⟨uInv_mem_unitBox hbox, ?_⟩, ?_⟩
    · rcases hco with (h | h) | (h | h)
      · exact ⟨1, Or.inr (by rw [uInv_apply_one, h]; norm_num)⟩
      · exact ⟨1, Or.inl (by rw [uInv_apply_one, h]; norm_num)⟩
      · exact ⟨2, Or.inr (by rw [uInv_apply_two, h]; norm_num)⟩
      · exact ⟨2, Or.inl (by rw [uInv_apply_two, h]; norm_num)⟩
    · rw [pairDiff_uInv E E' V W hseamU hseamU' x hsU]
      exact hzero
  · rcases hco with (h | h) | (h | h)
    · exact Or.inl (Or.inr (by rw [uInv_apply_one, h]; norm_num))
    · exact Or.inl (Or.inl (by rw [uInv_apply_one, h]; norm_num))
    · exact Or.inr (Or.inr (by rw [uInv_apply_two, h]; norm_num))
    · exact Or.inr (Or.inl (by rw [uInv_apply_two, h]; norm_num))

lemma yInv_mem (E : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (E' : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (V W : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    (hseamV : ∀ y : EuclideanSpace ℝ (Fin 3), onSeam y → V (seamInv y) = V y)
    {x : Amb 8} (hx : x ∈ yPart (pairDiff E E' V W)) :
    yInv x ∈ yPart (pairDiff E E' V W) := by
  rw [mem_yPart] at hx
  obtain ⟨hbz, hco⟩ := hx
  rw [mem_bdyZeros] at hbz
  obtain ⟨⟨hbox, -⟩, hzero⟩ := hbz
  have hsV := onSeam_ftY_of x hco
  rw [mem_yPart]
  refine ⟨?_, ?_⟩
  · rw [mem_bdyZeros, Submission.Drive.unitBoxBdry, Set.mem_ofPred_eq]
    refine ⟨⟨yInv_mem_unitBox hbox, ?_⟩, ?_⟩
    · rcases hco with (h | h) | (h | h)
      · exact ⟨3, Or.inr (by rw [yInv_apply_three, h]; norm_num)⟩
      · exact ⟨3, Or.inl (by rw [yInv_apply_three, h]; norm_num)⟩
      · exact ⟨4, Or.inr (by rw [yInv_apply_four, h]; norm_num)⟩
      · exact ⟨4, Or.inl (by rw [yInv_apply_four, h]; norm_num)⟩
    · rw [pairDiff_yInv E E' V W hseamV x hsV]
      exact hzero
  · rcases hco with (h | h) | (h | h)
    · exact Or.inl (Or.inr (by rw [yInv_apply_three, h]; norm_num))
    · exact Or.inl (Or.inl (by rw [yInv_apply_three, h]; norm_num))
    · exact Or.inr (Or.inr (by rw [yInv_apply_four, h]; norm_num))
    · exact Or.inr (Or.inl (by rw [yInv_apply_four, h]; norm_num))

lemma zInv_mem (E : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (E' : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (V W : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    (hseamW : ∀ z : EuclideanSpace ℝ (Fin 3), onSeam z → W (seamInv z) = W z)
    {x : Amb 8} (hx : x ∈ zPart (pairDiff E E' V W)) :
    zInv x ∈ zPart (pairDiff E E' V W) := by
  rw [mem_zPart] at hx
  obtain ⟨hbz, hco⟩ := hx
  rw [mem_bdyZeros] at hbz
  obtain ⟨⟨hbox, -⟩, hzero⟩ := hbz
  have hsW := onSeam_ftZ_of x hco
  rw [mem_zPart]
  refine ⟨?_, ?_⟩
  · rw [mem_bdyZeros, Submission.Drive.unitBoxBdry, Set.mem_ofPred_eq]
    refine ⟨⟨zInv_mem_unitBox hbox, ?_⟩, ?_⟩
    · rcases hco with (h | h) | (h | h)
      · exact ⟨6, Or.inr (by rw [zInv_apply_six, h]; norm_num)⟩
      · exact ⟨6, Or.inl (by rw [zInv_apply_six, h]; norm_num)⟩
      · exact ⟨7, Or.inr (by rw [zInv_apply_seven, h]; norm_num)⟩
      · exact ⟨7, Or.inl (by rw [zInv_apply_seven, h]; norm_num)⟩
    · rw [pairDiff_zInv E E' V W hseamW x hsW]
      exact hzero
  · rcases hco with (h | h) | (h | h)
    · exact Or.inl (Or.inr (by rw [zInv_apply_six, h]; norm_num))
    · exact Or.inl (Or.inl (by rw [zInv_apply_six, h]; norm_num))
    · exact Or.inr (Or.inr (by rw [zInv_apply_seven, h]; norm_num))
    · exact Or.inr (Or.inl (by rw [zInv_apply_seven, h]; norm_num))

lemma uInv_invol (x : Amb 8) : uInv (uInv x) = x := by
  rw [show uInv (uInv x) = mk9 (ftS x) (seamInv2 (seamInv2 (ftU x))) (ftY x) (ftZ x) from by
        simp only [uInv, ftS_mk9, ftU_mk9, ftY_mk9, ftZ_mk9],
    seamInv2_invol, mk9_ft x]

lemma yInv_invol (x : Amb 8) : yInv (yInv x) = x := by
  rw [show yInv (yInv x) = mk9 (ftS x) (ftU x) (seamInv (seamInv (ftY x))) (ftZ x) from by
        simp only [yInv, ftS_mk9, ftU_mk9, ftY_mk9, ftZ_mk9],
    seamInv_invol, mk9_ft x]

lemma zInv_invol (x : Amb 8) : zInv (zInv x) = x := by
  rw [show zInv (zInv x) = mk9 (ftS x) (ftU x) (ftY x) (seamInv (seamInv (ftZ x))) from by
        simp only [zInv, ftS_mk9, ftU_mk9, ftY_mk9, ftZ_mk9],
    seamInv_invol, mk9_ft x]

lemma uInv_ne {x : Amb 8} (h : (x 1 = 0 ∨ x 1 = 1) ∨ (x 2 = 0 ∨ x 2 = 1)) : uInv x ≠ x := by
  intro heq
  rcases h with (h | h) | (h | h)
  · have hc := congrArg (fun z : Amb 8 => z 1) heq
    rw [uInv_apply_one, h] at hc
    norm_num at hc
  · have hc := congrArg (fun z : Amb 8 => z 1) heq
    rw [uInv_apply_one, h] at hc
    norm_num at hc
  · have hc := congrArg (fun z : Amb 8 => z 2) heq
    rw [uInv_apply_two, h] at hc
    norm_num at hc
  · have hc := congrArg (fun z : Amb 8 => z 2) heq
    rw [uInv_apply_two, h] at hc
    norm_num at hc

lemma yInv_ne {x : Amb 8} (h : (x 3 = 0 ∨ x 3 = 1) ∨ (x 4 = 0 ∨ x 4 = 1)) : yInv x ≠ x := by
  intro heq
  rcases h with (h | h) | (h | h)
  · have hc := congrArg (fun z : Amb 8 => z 3) heq
    rw [yInv_apply_three, h] at hc
    norm_num at hc
  · have hc := congrArg (fun z : Amb 8 => z 3) heq
    rw [yInv_apply_three, h] at hc
    norm_num at hc
  · have hc := congrArg (fun z : Amb 8 => z 4) heq
    rw [yInv_apply_four, h] at hc
    norm_num at hc
  · have hc := congrArg (fun z : Amb 8 => z 4) heq
    rw [yInv_apply_four, h] at hc
    norm_num at hc

lemma zInv_ne {x : Amb 8} (h : (x 6 = 0 ∨ x 6 = 1) ∨ (x 7 = 0 ∨ x 7 = 1)) : zInv x ≠ x := by
  intro heq
  rcases h with (h | h) | (h | h)
  · have hc := congrArg (fun z : Amb 8 => z 6) heq
    rw [zInv_apply_six, h] at hc
    norm_num at hc
  · have hc := congrArg (fun z : Amb 8 => z 6) heq
    rw [zInv_apply_six, h] at hc
    norm_num at hc
  · have hc := congrArg (fun z : Amb 8 => z 7) heq
    rw [zInv_apply_seven, h] at hc
    norm_num at hc
  · have hc := congrArg (fun z : Amb 8 => z 7) heq
    rw [zInv_apply_seven, h] at hc
    norm_num at hc

lemma even_ncard_uPart (E : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (E' : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (V W : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    (hseamU : ∀ (s : ℝ) (u : EuclideanSpace ℝ (Fin 2)),
      onSeam2 u → E s (seamInv2 u) = E s u)
    (hseamU' : ∀ u : EuclideanSpace ℝ (Fin 2), onSeam2 u → E' (seamInv2 u) = E' u)
    (hfin : (uPart (pairDiff E E' V W)).Finite) :
    Even (uPart (pairDiff E E' V W)).ncard :=
  even_ncard_of_involution hfin uInv (fun _ hx => uInv_mem E E' V W hseamU hseamU' hx)
    (fun x _ => uInv_invol x) (fun _ hx => uInv_ne (mem_uPart.mp hx).2)

lemma even_ncard_yPart (E : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (E' : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (V W : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    (hseamV : ∀ y : EuclideanSpace ℝ (Fin 3), onSeam y → V (seamInv y) = V y)
    (hfin : (yPart (pairDiff E E' V W)).Finite) :
    Even (yPart (pairDiff E E' V W)).ncard :=
  even_ncard_of_involution hfin yInv (fun _ hx => yInv_mem E E' V W hseamV hx)
    (fun x _ => yInv_invol x) (fun _ hx => yInv_ne (mem_yPart.mp hx).2)

lemma even_ncard_zPart (E : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (E' : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (V W : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    (hseamW : ∀ z : EuclideanSpace ℝ (Fin 3), onSeam z → W (seamInv z) = W z)
    (hfin : (zPart (pairDiff E E' V W)).Finite) :
    Even (zPart (pairDiff E E' V W)).ncard :=
  even_ncard_of_involution hfin zInv (fun _ hx => zInv_mem E E' V W hseamW hx)
    (fun x _ => zInv_invol x) (fun _ hx => zInv_ne (mem_zPart.mp hx).2)

/-! ## 7. The level faces are free -/

lemma lvlPart_eq_empty (E : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (E' : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (V W : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    (havY : ∀ x ∈ Submission.Drive.unitBox 8, pairDiff E E' V W x = 0 →
      ftY2 x ≠ 0 ∧ ftY2 x ≠ 1)
    (havZ : ∀ x ∈ Submission.Drive.unitBox 8, pairDiff E E' V W x = 0 →
      ftZ2 x ≠ 0 ∧ ftZ2 x ≠ 1) :
    lvlPart (pairDiff E E' V W) = ∅ := by
  ext x
  constructor
  · intro hx
    rw [mem_lvlPart] at hx
    obtain ⟨hbz, hco⟩ := hx
    rw [mem_bdyZeros] at hbz
    obtain ⟨⟨hbox, -⟩, hzero⟩ := hbz
    obtain ⟨hy1, hy2⟩ := havY x hbox hzero
    obtain ⟨hz1, hz2⟩ := havZ x hbox hzero
    rcases hco with (h | h) | (h | h)
    · exact hy1 (by rw [ftY2_eq_coord]; exact h)
    · exact hy2 (by rw [ftY2_eq_coord]; exact h)
    · exact hz1 (by rw [ftZ2_eq_coord]; exact h)
    · exact hz2 (by rw [ftZ2_eq_coord]; exact h)
  · intro hx
    exact hx.elim

/-- The elementary arithmetic of the last step: from the parity of `a + b + c + d + e` with
`b, c, d, e` even, the parity of `a`. -/
lemma even_of_even_add_four {a b c d e : ℕ} (h : Even (a + b + c + d + e))
    (hb : Even b) (hc : Even c) (hd : Even d) (he : Even e) : Even a := by
  have h' : Even (a + (b + (c + (d + e)))) := by
    rwa [show a + b + c + d + e = a + (b + (c + (d + e))) from by ring] at h
  exact (Nat.even_add.mp h').mpr (hb.add (hc.add (hd.add he)))

/-! ## 8. Smoothness of the pair difference map -/

lemma pair44_apply_lt (a b : EuclideanSpace ℝ (Fin 4)) {i : Fin 8} (h : i.val < 4) :
    pair44 a b i = a ⟨i.val, h⟩ := by
  simp only [pair44, WithLp.ofLp_toLp]
  rw [dif_pos h]

lemma pair44_apply_ge (a b : EuclideanSpace ℝ (Fin 4)) {i : Fin 8} (h : ¬ i.val < 4) :
    pair44 a b i = b ⟨i.val - 4, by omega⟩ := by
  simp only [pair44, WithLp.ofLp_toLp]
  rw [dif_neg h]

lemma fin_sub_four_lt (i : Fin 8) (h : ¬ i.val < 4) : i.val - 4 < 4 := by omega

lemma contDiff_pair44 {α : Type*} [NormedAddCommGroup α] [NormedSpace ℝ α]
    {u v : α → EuclideanSpace ℝ (Fin 4)} (hu : ContDiff ℝ Ctop u) (hv : ContDiff ℝ Ctop v) :
    ContDiff ℝ Ctop (fun x => pair44 (u x) (v x)) := by
  rw [contDiff_piLp]
  intro i
  by_cases hi : i.val < 4
  · have h : (fun x => pair44 (u x) (v x) i) = fun x => u x ⟨i.val, hi⟩ := by
      funext x; exact pair44_apply_lt (u x) (v x) hi
    rw [h]
    exact (by fun_prop : ContDiff ℝ Ctop
      (fun f : EuclideanSpace ℝ (Fin 4) => f ⟨i.val, hi⟩)).comp hu
  · have h : (fun x => pair44 (u x) (v x) i) = fun x => v x ⟨i.val - 4, fin_sub_four_lt i hi⟩ := by
      funext x; exact pair44_apply_ge (u x) (v x) hi
    rw [h]
    exact (by fun_prop : ContDiff ℝ Ctop
      (fun f : EuclideanSpace ℝ (Fin 4) => f ⟨i.val - 4, fin_sub_four_lt i hi⟩)).comp hv

theorem contDiff_pairDiff (E : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (E' : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (V W : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    (hE : ContDiff ℝ Ctop (Function.uncurry E)) (hE' : ContDiff ℝ Ctop E')
    (hV : ContDiff ℝ Ctop V) (hW : ContDiff ℝ Ctop W) :
    ContDiff ℝ Ctop (pairDiff E E' V W) := by
  have hSU : ContDiff ℝ Ctop (fun x : Amb 8 => (ftS x, ftU x)) := by
    refine ContDiff.prodMk ?_ ?_
    · show ContDiff ℝ Ctop (fun x : Amb 8 => x 0)
      fun_prop
    · show ContDiff ℝ Ctop
        (fun x : Amb 8 => WithLp.toLp 2 (fun i : Fin 2 => x ⟨1 + i.val, by omega⟩))
      fun_prop
  have hU : ContDiff ℝ Ctop (fun x : Amb 8 => ftU x) := by
    show ContDiff ℝ Ctop
      (fun x : Amb 8 => WithLp.toLp 2 (fun i : Fin 2 => x ⟨1 + i.val, by omega⟩))
    fun_prop
  have hY : ContDiff ℝ Ctop (fun x : Amb 8 => ftY x) := by
    show ContDiff ℝ Ctop
      (fun x : Amb 8 => WithLp.toLp 2 (fun i : Fin 3 => x ⟨3 + i.val, by omega⟩))
    fun_prop
  have hZ : ContDiff ℝ Ctop (fun x : Amb 8 => ftZ x) := by
    show ContDiff ℝ Ctop
      (fun x : Amb 8 => WithLp.toLp 2 (fun i : Fin 3 => x ⟨6 + i.val, by omega⟩))
    fun_prop
  have h1 : ContDiff ℝ Ctop (fun x : Amb 8 => E (ftS x) (ftU x)) := hE.comp hSU
  have h2 : ContDiff ℝ Ctop (fun x : Amb 8 => E' (ftU x)) := hE'.comp hU
  have h3 : ContDiff ℝ Ctop (fun x : Amb 8 => V (ftY x)) := hV.comp hY
  have h4 : ContDiff ℝ Ctop (fun x : Amb 8 => W (ftZ x)) := hW.comp hZ
  exact contDiff_pair44 (h1.sub h3) (h2.sub h4)

end PMB

open PMB

theorem even_ncard_pairMeetBdry
    (E : ℝ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (E' : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (V W : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 4))
    (hE : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry E))
    (hE' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) E')
    (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W)
    (hreg : ∀ x ∈ Submission.Drive.unitBox 8, Work.Drive.pairDiff E E' V W x = 0 →
      Function.Surjective (fderiv ℝ (Work.Drive.pairDiff E E' V W) x))
    (hface : ∀ x ∈ Submission.Drive.unitBoxBdry 8, Work.Drive.pairDiff E E' V W x = 0 →
      ∃ i : Fin 9, (x i = 0 ∨ x i = 1) ∧ (∀ j : Fin 9, j ≠ i → x j ∈ Set.Ioo (0 : ℝ) 1) ∧
        Function.Surjective (fun v : {v : EuclideanSpace ℝ (Fin 9) // v i = 0} =>
          fderiv ℝ (Work.Drive.pairDiff E E' V W) x v.1))
    (hseamU : ∀ (s : ℝ) (u : EuclideanSpace ℝ (Fin 2)), Work.Drive.onSeam2 u → E s (Work.Drive.seamInv2 u) = E s u)
    (hseamU' : ∀ u : EuclideanSpace ℝ (Fin 2), Work.Drive.onSeam2 u → E' (Work.Drive.seamInv2 u) = E' u)
    (hseamV : ∀ y : EuclideanSpace ℝ (Fin 3), Work.Drive.onSeam y → V (Work.Drive.seamInv y) = V y)
    (hseamW : ∀ z : EuclideanSpace ℝ (Fin 3), Work.Drive.onSeam z → W (Work.Drive.seamInv z) = W z)
    (havY : ∀ x ∈ Submission.Drive.unitBox 8, Work.Drive.pairDiff E E' V W x = 0 →
      Work.Drive.ftY2 x ≠ 0 ∧ Work.Drive.ftY2 x ≠ 1)
    (havZ : ∀ x ∈ Submission.Drive.unitBox 8, Work.Drive.pairDiff E E' V W x = 0 →
      Work.Drive.ftZ2 x ≠ 0 ∧ Work.Drive.ftZ2 x ≠ 1) :
    Even ((Work.Drive.pairMeetSet E E' V W 0).ncard + (Work.Drive.pairMeetSet E E' V W 1).ncard) := by
  have hFd : ContDiff ℝ Ctop (pairDiff E E' V W) := contDiff_pairDiff E E' V W hE hE' hV hW
  have hsum := even_sum_ncard_labelMeet (pairDiff E E' V W) hFd hreg hface label9
  rw [Fin.sum_univ_five] at hsum
  have hfin : (bdyZeros (pairDiff E E' V W)).Finite :=
    (boxParity 8 (pairDiff E E' V W) hFd hreg hface).1
  have hfinU : (uPart (pairDiff E E' V W)).Finite :=
    hfin.subset (fun x hx => (mem_uPart.mp hx).1)
  have hfinY : (yPart (pairDiff E E' V W)).Finite :=
    hfin.subset (fun x hx => (mem_yPart.mp hx).1)
  have hfinZ : (zPart (pairDiff E E' V W)).Finite :=
    hfin.subset (fun x hx => (mem_zPart.mp hx).1)
  have hU : Even (uPart (pairDiff E E' V W)).ncard :=
    even_ncard_uPart E E' V W hseamU hseamU' hfinU
  have hY : Even (yPart (pairDiff E E' V W)).ncard :=
    even_ncard_yPart E E' V W hseamV hfinY
  have hZ : Even (zPart (pairDiff E E' V W)).ncard :=
    even_ncard_zPart E E' V W hseamW hfinZ
  have h1 : Even (labelMeet (pairDiff E E' V W) label9 1).ncard := hU
  have h2 : Even (labelMeet (pairDiff E E' V W) label9 2).ncard := hY
  have h3 : Even (labelMeet (pairDiff E E' V W) label9 3).ncard := hZ
  have h4 : (labelMeet (pairDiff E E' V W) label9 4).ncard = 0 := by
    change (lvlPart (pairDiff E E' V W)).ncard = 0
    rw [lvlPart_eq_empty E E' V W havY havZ, Set.ncard_empty]
  have h4e : Even (labelMeet (pairDiff E E' V W) label9 4).ncard := by
    rw [h4]
    exact ⟨0, rfl⟩
  have hfin0 : (endFace (pairDiff E E' V W) 0).Finite :=
    hfin.subset (fun x hx => hx.1)
  have hfin1 : (endFace (pairDiff E E' V W) 1).Finite :=
    hfin.subset (fun x hx => hx.1)
  have h0 : (labelMeet (pairDiff E E' V W) label9 0).ncard
      = (pairMeetSet E E' V W 0).ncard + (pairMeetSet E E' V W 1).ncard := by
    rw [labelMeet_zero_eq (pairDiff E E' V W)]
    rw [Set.ncard_union_eq (disjoint_endFace (pairDiff E E' V W)) hfin0 hfin1]
    rw [ncard_endFace E E' V W (show (0 : ℝ) = 0 ∨ (0 : ℝ) = 1 from Or.inl rfl),
      ncard_endFace E E' V W (show (1 : ℝ) = 0 ∨ (1 : ℝ) = 1 from Or.inr rfl)]
  have ha : Even (labelMeet (pairDiff E E' V W) label9 0).ncard :=
    even_of_even_add_four hsum h1 h2 h3 h4e
  rwa [h0] at ha

end

end Work.Drive
