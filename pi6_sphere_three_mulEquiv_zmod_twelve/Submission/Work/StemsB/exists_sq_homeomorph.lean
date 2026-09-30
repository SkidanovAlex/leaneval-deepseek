import Mathlib

/-!
# `Work.StemsB.exists_sq_homeomorph`

There is a self-homeomorphism `Φ` of the square `[0,1]²` whose second coordinate vanishes
exactly on the union of the left, right and bottom edges.

We build `Φ` as the "cone" over a self-homeomorphism `h` of the boundary circle of the square:
`Φ p = c + ρ(p) • (h (u p) - c)`, where `c` is the centre, `ρ` the `L∞` radius and `u` the radial
projection to the boundary.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Work.StemsB

noncomputable section

open Set Filter
open scoped Topology

abbrev Sq : Type := unitInterval × unitInterval

/-- The square as a subset of `ℝ × ℝ`. -/
def sq : Set (ℝ × ℝ) := {q | 0 ≤ q.1 ∧ q.1 ≤ 1 ∧ 0 ≤ q.2 ∧ q.2 ≤ 1}

theorem mem_sq_iff (q : ℝ × ℝ) :
    q ∈ sq ↔ 0 ≤ q.1 ∧ q.1 ≤ 1 ∧ 0 ≤ q.2 ∧ q.2 ≤ 1 := Iff.rfl

/-- The coordinates of a point of the square, as a point of `ℝ × ℝ`. -/
def toR (p : Sq) : ℝ × ℝ := ((p.1 : ℝ), (p.2 : ℝ))

theorem toR_mem (p : Sq) : toR p ∈ sq := ⟨p.1.2.1, p.1.2.2, p.2.2.1, p.2.2.2⟩

/-- Package a point of the square as a point of `unitInterval × unitInterval`. -/
def ofR (x : ℝ × ℝ) (hx : x ∈ sq) : Sq :=
  (⟨x.1, hx.1, hx.2.1⟩, ⟨x.2, hx.2.2.1, hx.2.2.2⟩)

theorem ofR_toR (p : Sq) : ofR (toR p) (toR_mem p) = p := by
  apply Prod.ext <;> apply Subtype.ext <;> rfl

/-- The centre of the square. -/
def ctr : Sq := (⟨1/2, by norm_num⟩, ⟨1/2, by norm_num⟩)

/-- The four edges of the square (as subsets of `ℝ × ℝ`). -/
def Eb : Set (ℝ × ℝ) := {q | q.2 = 0}
def Er : Set (ℝ × ℝ) := {q | q.1 = 1}
def Et : Set (ℝ × ℝ) := {q | q.2 = 1}
def El : Set (ℝ × ℝ) := {q | q.1 = 0}

/-- The boundary of the square. -/
def bndR : Set (ℝ × ℝ) := Eb ∪ Er ∪ (Et ∪ El)

/-- The union of the left, right and bottom edges (the "U"). -/
def UUR : Set (ℝ × ℝ) := {q | q.1 = 0 ∨ q.1 = 1 ∨ q.2 = 0}

theorem mem_bndR_iff (q : ℝ × ℝ) : q ∈ bndR ↔ q.2 = 0 ∨ q.1 = 1 ∨ q.2 = 1 ∨ q.1 = 0 := by
  simp only [bndR, Eb, Er, Et, El, Set.mem_union, Set.mem_ofPred_eq]
  tauto

/-! ### The boundary self-map -/

/-- The boundary self map in coordinates. -/
def Gbd (x y : ℝ) : ℝ × ℝ :=
  if y = 0 then ((x + 1) / 3, 0)
  else if x = 1 then ((y + 2) / 3, 0)
  else if y = 1 then
    (if x ≤ 1/3 then (0, 3 * x)
     else if x ≤ 2/3 then (3 * x - 1, 1)
     else (1, 3 - 3 * x))
  else ((1 - y) / 3, 0)

/-- The inverse of `Gbd` on the boundary, in coordinates. -/
def Gi (x y : ℝ) : ℝ × ℝ :=
  if y = 0 then
    (if x ≤ 1/3 then (0, 1 - 3 * x)
     else if x ≤ 2/3 then (3 * x - 1, 0)
     else (1, 3 * x - 2))
  else if x = 0 then (y / 3, 1)
  else if x = 1 then ((3 - y) / 3, 1)
  else ((x + 1) / 3, 1)

/-- The boundary self-map on `ℝ × ℝ`. -/
def Hbd (q : ℝ × ℝ) : ℝ × ℝ := Gbd q.1 q.2

/-- The inverse of `Hbd` on the boundary. -/
def Hi (q : ℝ × ℝ) : ℝ × ℝ := Gi q.1 q.2

theorem Gbd_bot (x : ℝ) : Gbd x 0 = ((x + 1) / 3, 0) := by rw [Gbd, if_pos rfl]

theorem Gbd_right (x y : ℝ) (h : y ≠ 0) (hx : x = 1) : Gbd x y = ((y + 2) / 3, 0) := by
  rw [Gbd, if_neg h, if_pos hx]

theorem Gbd_top (x y : ℝ) (h : y ≠ 0) (hx : x ≠ 1) (hy : y = 1) :
    Gbd x y = (if x ≤ 1 / 3 then (0, 3 * x)
      else if x ≤ 2 / 3 then (3 * x - 1, 1) else (1, 3 - 3 * x)) := by
  rw [Gbd, if_neg h, if_neg hx, if_pos hy]

theorem Gbd_left (x y : ℝ) (h : y ≠ 0) (hx : x ≠ 1) (hy : y ≠ 1) :
    Gbd x y = ((1 - y) / 3, 0) := by
  rw [Gbd, if_neg h, if_neg hx, if_neg hy]

theorem Gi_zero (x : ℝ) :
    Gi x 0 = (if x ≤ 1 / 3 then (0, 1 - 3 * x)
      else if x ≤ 2 / 3 then (3 * x - 1, 0) else (1, 3 * x - 2)) := by
  rw [Gi, if_pos rfl]

theorem Gi_fst_zero (x y : ℝ) (h : y ≠ 0) (hx : x = 0) : Gi x y = (y / 3, 1) := by
  rw [Gi, if_neg h, if_pos hx]

theorem Gi_fst_one (x y : ℝ) (h : y ≠ 0) (hx0 : x ≠ 0) (hx : x = 1) :
    Gi x y = ((3 - y) / 3, 1) := by
  rw [Gi, if_neg h, if_neg hx0, if_pos hx]

theorem Gi_top (x y : ℝ) (h : y ≠ 0) (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    Gi x y = ((x + 1) / 3, 1) := by
  rw [Gi, if_neg h, if_neg hx0, if_neg hx1]



theorem Gi_Gbd (x y : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hb : y = 0 ∨ x = 1 ∨ y = 1 ∨ x = 0) : Gi (Gbd x y).1 (Gbd x y).2 = (x, y) := by
  rcases hb with h0 | h1 | h2 | h3
  · subst h0
    rw [Gbd_bot]; simp only [Prod.fst, Prod.snd]; rw [Gi_zero]
    split_ifs with g1 g2
    · ext <;> linarith
    · ext <;> linarith
    · exfalso; linarith
  · rcases eq_or_ne y 0 with hy | hy
    · subst hy
      rw [Gbd_bot]; simp only [Prod.fst, Prod.snd]; rw [Gi_zero]
      split_ifs <;> ext <;> linarith
    · have hypos : 0 < y := lt_of_le_of_ne hy0 (Ne.symm hy)
      rw [Gbd_right x y hy h1]; simp only [Prod.fst, Prod.snd]; rw [Gi_zero]
      split_ifs with g1 g2
      · exfalso; linarith
      · exfalso; linarith
      · ext <;> linarith
  · have hyn : y ≠ 0 := by rw [h2]; norm_num
    rcases eq_or_ne x 1 with hx | hx
    · rw [Gbd_right x y hyn hx]; simp only [Prod.fst, Prod.snd]; rw [Gi_zero]
      split_ifs with g1 g2
      · exfalso; linarith
      · exfalso; linarith
      · ext <;> linarith
    · rw [Gbd_top x y hyn hx h2]
      by_cases gg1 : x ≤ 1/3
      · rw [if_pos gg1]; simp only [Prod.fst, Prod.snd]
        rcases eq_or_ne x 0 with hx0' | hx0'
        · subst hx0'
          simp only [mul_zero]
          rw [Gi_zero, if_pos (by norm_num : (0:ℝ) ≤ 1/3)]
          ext <;> linarith
        · have h3 : 3 * x ≠ 0 := by intro hh; exact hx0' (by linarith)
          rw [Gi_fst_zero 0 (3 * x) h3 rfl]; ext <;> linarith
      · rw [if_neg gg1]
        by_cases gg2 : x ≤ 2/3
        · rw [if_pos gg2]; simp only [Prod.fst, Prod.snd]
          rcases eq_or_ne (3 * x - 1) 1 with h1' | h1'
          · rw [Gi_fst_one (3 * x - 1) 1 one_ne_zero (by intro hh; linarith) h1']
            ext <;> linarith
          · have hne0 : 3 * x - 1 ≠ 0 := by intro hh; have := not_le.mp gg1; linarith
            rw [Gi_top (3 * x - 1) 1 one_ne_zero hne0 h1']; ext <;> linarith
        · rw [if_neg gg2]; simp only [Prod.fst, Prod.snd]
          rcases eq_or_ne (3 - 3 * x) 0 with h0' | h0'
          · rw [h0', Gi_zero]
            rw [if_neg (by norm_num : ¬ ((1:ℝ) ≤ 1/3)), if_neg (by norm_num : ¬ ((1:ℝ) ≤ 2/3))]
            ext <;> linarith
          · rw [Gi_fst_one 1 (3 - 3 * x) h0' one_ne_zero rfl]; ext <;> linarith
  · subst h3
    rcases eq_or_ne y 0 with hy | hy
    · subst hy
      rw [Gbd_bot]; simp only [Prod.fst, Prod.snd]; rw [Gi_zero]
      split_ifs <;> ext <;> linarith
    · rcases eq_or_ne y 1 with hy1' | hy1'
      · subst hy1'
        rw [Gbd_top 0 1 hy (by norm_num) rfl, if_pos (by norm_num : (0:ℝ) ≤ 1/3)]
        simp only [Prod.fst, Prod.snd, mul_zero]
        rw [Gi_zero, if_pos (by norm_num : (0:ℝ) ≤ 1/3)]
        ext <;> linarith
      · rw [Gbd_left 0 y hy (by norm_num) hy1']; simp only [Prod.fst, Prod.snd]; rw [Gi_zero]
        split_ifs with g1 g2
        · ext <;> linarith
        · ext <;> linarith
        · exfalso; linarith

theorem Gbd_Gi (x y : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hb : y = 0 ∨ x = 1 ∨ y = 1 ∨ x = 0) : Gbd (Gi x y).1 (Gi x y).2 = (x, y) := by
  rcases eq_or_ne y 0 with hy | hy
  · subst hy
    rw [Gi_zero]
    split_ifs with g1 g2
    · simp only [Prod.fst, Prod.snd]
      rcases eq_or_ne (1 - 3 * x) 0 with hz | hz
      · rw [hz, Gbd_bot]; ext <;> linarith
      · have hzpos : 0 < 1 - 3 * x := lt_of_le_of_ne (by linarith) (Ne.symm hz)
        rcases eq_or_ne x 0 with hx | hx
        · subst hx
          simp only [mul_zero, sub_zero]
          rw [Gbd_top 0 1 (by norm_num) (by norm_num) rfl, if_pos (by norm_num : (0:ℝ) ≤ 1/3)]
          ext <;> linarith
        · have hz1 : 1 - 3 * x ≠ 1 := by intro hh; exact hx (by linarith)
          rw [Gbd_left 0 (1 - 3 * x) (ne_of_gt hzpos) (by norm_num) hz1]
          ext <;> linarith
    · simp only [Prod.fst, Prod.snd]
      rw [Gbd_bot]; ext <;> linarith
    · simp only [Prod.fst, Prod.snd]
      have hne : 3 * x - 2 ≠ 0 := by intro hh; have := not_le.mp g2; linarith
      rw [Gbd_right 1 (3 * x - 2) hne rfl]; ext <;> linarith
  · rcases hb with h0 | h1 | h2 | h3
    · exact absurd h0 hy
    · subst h1
      rw [Gi_fst_one 1 y hy (by norm_num) rfl]; simp only [Prod.fst, Prod.snd]
      rw [Gbd_top ((3 - y) / 3) 1 one_ne_zero (by intro hh; exact hy (by linarith)) rfl]
      rw [if_neg (by intro hh; linarith)]
      rcases eq_or_ne y 1 with hy1b | hy1b
      · rw [if_pos (by rw [hy1b]; norm_num)]
        ext <;> linarith
      · have hgt : ¬ ((3 - y) / 3 ≤ 2 / 3) := by
          intro hh
          have h1 : 1 ≤ y := by linarith
          exact hy1b (le_antisymm hy1 h1)
        rw [if_neg hgt]
        ext <;> linarith
    · subst h2
      rcases eq_or_ne x 0 with hx | hx
      · subst hx
        rw [Gi_fst_zero 0 1 (by norm_num) rfl]; simp only [Prod.fst, Prod.snd]
        rw [Gbd_top (1/3) 1 one_ne_zero (by norm_num) rfl, if_pos (by norm_num : (1:ℝ)/3 ≤ 1/3)]
        ext <;> linarith
      · rcases eq_or_ne x 1 with hx1 | hx1
        · subst hx1
          rw [Gi_fst_one 1 1 (by norm_num) (by norm_num) rfl]; simp only [Prod.fst, Prod.snd]
          rw [Gbd_top ((3 - 1) / 3) 1 one_ne_zero (by norm_num) rfl,
              if_neg (by norm_num : ¬ ((3:ℝ) - 1) / 3 ≤ 1/3),
              if_pos (by norm_num : ((3:ℝ) - 1) / 3 ≤ 2/3)]
          ext <;> linarith
        · rw [Gi_top x 1 (by norm_num) hx hx1]; simp only [Prod.fst, Prod.snd]
          have hgt : ¬ ((x + 1) / 3 ≤ 1 / 3) := by
            intro hh
            have h0 : x ≤ 0 := by linarith
            exact hx (le_antisymm h0 hx0)
          rw [Gbd_top ((x + 1) / 3) 1 one_ne_zero (by intro hh; exact hx1 (by linarith)) rfl,
              if_neg hgt, if_pos (by linarith)]
          ext <;> linarith
    · subst h3
      rw [Gi_fst_zero 0 y hy rfl]; simp only [Prod.fst, Prod.snd]
      rw [Gbd_top (y / 3) 1 one_ne_zero (by intro hh; exact hy (by linarith)) rfl,
          if_pos (by linarith : y / 3 ≤ 1/3)]
      ext <;> linarith



theorem Hi_Hbd (q : ℝ × ℝ) (hq : q ∈ sq) (hb : q ∈ bndR) : Hi (Hbd q) = q :=
  Gi_Gbd q.1 q.2 hq.1 hq.2.1 hq.2.2.1 hq.2.2.2 ((mem_bndR_iff q).mp hb)

theorem Hbd_Hi (q : ℝ × ℝ) (hq : q ∈ sq) (hb : q ∈ bndR) : Hbd (Hi q) = q :=
  Gbd_Gi q.1 q.2 hq.1 hq.2.1 hq.2.2.1 hq.2.2.2 ((mem_bndR_iff q).mp hb)

theorem Hbd_mem_sq (q : ℝ × ℝ) (hq : q ∈ sq) : Hbd q ∈ sq := by
  obtain ⟨h1, h2, h3, h4⟩ := hq
  rw [Hbd, Gbd]
  split_ifs <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

theorem Hi_mem_sq (q : ℝ × ℝ) (hq : q ∈ sq) : Hi q ∈ sq := by
  obtain ⟨h1, h2, h3, h4⟩ := hq
  rw [Hi, Gi]
  split_ifs <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

theorem Hbd_mem_bnd (q : ℝ × ℝ) : Hbd q ∈ bndR := by
  rw [Hbd, Gbd]
  split_ifs <;>
    (simp only [bndR, Eb, Er, Et, El, Set.mem_union, Set.mem_ofPred_eq]
     try tauto)

theorem Hbd_on_Eb (q : ℝ × ℝ) (h : q.2 = 0) : Hbd q = ((q.1 + 1) / 3, 0) := by
  rw [Hbd, Gbd, if_pos h]

theorem Hbd_on_Er (q : ℝ × ℝ) (h : q.1 = 1) : Hbd q = ((q.2 + 2) / 3, 0) := by
  rw [Hbd, Gbd]
  by_cases h0 : q.2 = 0
  · rw [if_pos h0, h, h0]; norm_num
  · rw [if_neg h0, if_pos h]

theorem Hbd_on_El (q : ℝ × ℝ) (h : q.1 = 0) : Hbd q = ((1 - q.2) / 3, 0) := by
  rw [Hbd, Gbd]
  split_ifs <;> ext <;> linarith

theorem Hbd_on_Et (q : ℝ × ℝ) (h : q.2 = 1) :
    Hbd q = (if q.1 ≤ 1 / 3 then (0, 3 * q.1)
      else if q.1 ≤ 2 / 3 then (3 * q.1 - 1, 1) else (1, 3 - 3 * q.1)) := by
  rw [Hbd, Gbd, h, if_neg (by norm_num : ¬ ((1:ℝ) = 0))]
  by_cases h1 : q.1 = 1
  · rw [if_pos h1, h1]
    rw [if_neg (by norm_num : ¬ ((1:ℝ) ≤ 1/3)), if_neg (by norm_num : ¬ ((1:ℝ) ≤ 2/3))]
    norm_num
  · rw [if_neg h1, if_pos rfl]

theorem isClosed_Eb : IsClosed Eb :=
  isClosed_singleton.preimage continuous_snd

theorem isClosed_Er : IsClosed Er :=
  isClosed_singleton.preimage continuous_fst

theorem isClosed_Et : IsClosed Et :=
  isClosed_singleton.preimage continuous_snd

theorem isClosed_El : IsClosed El :=
  isClosed_singleton.preimage continuous_fst

theorem continuousOn_Hbd_Eb : ContinuousOn Hbd Eb := by
  have hc : Continuous (fun q : ℝ × ℝ => ((q.1 + 1) / 3, (0:ℝ))) := by fun_prop
  exact hc.continuousOn.congr (fun q hq => Hbd_on_Eb q hq)

theorem continuousOn_Hbd_Er : ContinuousOn Hbd Er := by
  have hc : Continuous (fun q : ℝ × ℝ => ((q.2 + 2) / 3, (0:ℝ))) := by fun_prop
  exact hc.continuousOn.congr (fun q hq => Hbd_on_Er q hq)

theorem continuousOn_Hbd_El : ContinuousOn Hbd El := by
  have hc : Continuous (fun q : ℝ × ℝ => ((1 - q.2) / 3, (0:ℝ))) := by fun_prop
  exact hc.continuousOn.congr (fun q hq => Hbd_on_El q hq)

theorem continuousOn_Hbd_Et : ContinuousOn Hbd Et := by
  have hA : ContinuousOn Hbd (Et ∩ {q : ℝ × ℝ | q.1 ≤ 1/3}) := by
    have hc : Continuous (fun q : ℝ × ℝ => ((0:ℝ), 3 * q.1)) := by fun_prop
    refine hc.continuousOn.congr (fun q hq => ?_)
    have hle : q.1 ≤ 1/3 := hq.2
    rw [Hbd_on_Et q hq.1, if_pos hle]
  have hB : ContinuousOn Hbd (Et ∩ {q : ℝ × ℝ | 1/3 ≤ q.1 ∧ q.1 ≤ 2/3}) := by
    have hc : Continuous (fun q : ℝ × ℝ => (3 * q.1 - 1, (1:ℝ))) := by fun_prop
    refine hc.continuousOn.congr (fun q hq => ?_)
    have hq2 : 1/3 ≤ q.1 ∧ q.1 ≤ 2/3 := hq.2
    rw [Hbd_on_Et q hq.1]
    by_cases h1 : q.1 ≤ 1/3
    · rw [if_pos h1]; ext <;> linarith
    · rw [if_neg h1, if_pos hq2.2]
  have hC : ContinuousOn Hbd (Et ∩ {q : ℝ × ℝ | 2/3 ≤ q.1}) := by
    have hc : Continuous (fun q : ℝ × ℝ => ((1:ℝ), 3 - 3 * q.1)) := by fun_prop
    refine hc.continuousOn.congr (fun q hq => ?_)
    have hq2 : 2/3 ≤ q.1 := hq.2
    rw [Hbd_on_Et q hq.1]
    by_cases h1 : q.1 ≤ 1/3
    · rw [if_pos h1]; ext <;> linarith
    · rw [if_neg h1]
      by_cases h2 : q.1 ≤ 2/3
      · rw [if_pos h2]; ext <;> linarith
      · rw [if_neg h2]
  have hclA : IsClosed (Et ∩ {q : ℝ × ℝ | q.1 ≤ 1/3}) :=
    isClosed_Et.inter (isClosed_le continuous_fst continuous_const)
  have hclB : IsClosed (Et ∩ {q : ℝ × ℝ | 1/3 ≤ q.1 ∧ q.1 ≤ 2/3}) :=
    isClosed_Et.inter ((isClosed_le continuous_const continuous_fst).inter
      (isClosed_le continuous_fst continuous_const))
  have hclC : IsClosed (Et ∩ {q : ℝ × ℝ | 2/3 ≤ q.1}) :=
    isClosed_Et.inter (isClosed_le continuous_const continuous_fst)
  have hAB : ContinuousOn Hbd (Et ∩ {q : ℝ × ℝ | q.1 ≤ 1/3} ∪
      (Et ∩ {q : ℝ × ℝ | 1/3 ≤ q.1 ∧ q.1 ≤ 2/3})) :=
    hA.union_of_isClosed hB hclA hclB
  have hunion : Et ∩ {q : ℝ × ℝ | q.1 ≤ 1/3} ∪
      (Et ∩ {q : ℝ × ℝ | 1/3 ≤ q.1 ∧ q.1 ≤ 2/3}) ∪ (Et ∩ {q : ℝ × ℝ | 2/3 ≤ q.1}) = Et := by
    ext q; constructor
    · rintro ((⟨hq, -⟩ | ⟨hq, -, -⟩) | ⟨hq, -⟩) <;> exact hq
    · intro hq
      rcases le_total q.1 (1/3) with h | h
      · exact Or.inl (Or.inl ⟨hq, h⟩)
      · rcases le_total q.1 (2/3) with h' | h'
        · exact Or.inl (Or.inr ⟨hq, h, h'⟩)
        · exact Or.inr ⟨hq, h'⟩
  have key := hAB.union_of_isClosed hC (hclA.union hclB) hclC
  rwa [hunion] at key

theorem continuousOn_Hbd_bndR : ContinuousOn Hbd bndR := by
  have hAB : ContinuousOn Hbd (Eb ∪ Er) :=
    continuousOn_Hbd_Eb.union_of_isClosed continuousOn_Hbd_Er isClosed_Eb isClosed_Er
  have hCD : ContinuousOn Hbd (Et ∪ El) :=
    continuousOn_Hbd_Et.union_of_isClosed continuousOn_Hbd_El isClosed_Et isClosed_El
  have key := hAB.union_of_isClosed hCD (isClosed_Eb.union isClosed_Er)
    (isClosed_Et.union isClosed_El)
  simpa only [bndR] using key

/-! ### The coning construction -/

theorem mem_UUR_iff (q : ℝ × ℝ) : q ∈ UUR ↔ q.1 = 0 ∨ q.1 = 1 ∨ q.2 = 0 := Iff.rfl

theorem Hi_mem_bnd (q : ℝ × ℝ) : Hi q ∈ bndR := by
  rw [Hi, Gi]
  split_ifs <;>
    (simp only [bndR, Eb, Er, Et, El, Set.mem_union, Set.mem_ofPred_eq]
     try tauto)

theorem Hbd_second_zero (q : ℝ × ℝ) (hq : q ∈ sq) (hb : q ∈ bndR) :
    (Hbd q).2 = 0 ↔ q ∈ UUR := by
  rw [mem_bndR_iff] at hb
  rcases hb with h0 | h1 | h2 | h3
  · rw [Hbd_on_Eb q h0, mem_UUR_iff]; simp [h0]
  · rw [Hbd_on_Er q h1, mem_UUR_iff]; simp [h1]
  · rw [Hbd_on_Et q h2, mem_UUR_iff, h2]
    by_cases g1 : q.1 ≤ 1/3
    · rw [if_pos g1]
      constructor
      · intro h; simp only [Prod.snd] at h; left; linarith
      · intro h; simp only [Prod.snd]; rcases h with h | h | h <;> linarith
    · rw [if_neg g1]
      by_cases g2 : q.1 ≤ 2/3
      · rw [if_pos g2]
        constructor
        · intro h; simp only [Prod.snd] at h; exact absurd h (by norm_num)
        · intro h; simp only [Prod.snd]; rcases h with h | h | h <;> linarith
      · rw [if_neg g2]
        constructor
        · intro h; simp only [Prod.snd] at h; right; left; linarith
        · intro h; simp only [Prod.snd]; rcases h with h | h | h <;> linarith
  · rw [Hbd_on_El q h3, mem_UUR_iff]; simp [h3]

/-- The centre as a point of `ℝ × ℝ`. -/
def c0 : ℝ × ℝ := (1/2, 1/2)

theorem c0_mem_sq : c0 ∈ sq :=
  ⟨by norm_num [c0], by norm_num [c0], by norm_num [c0], by norm_num [c0]⟩

/-- The `L∞` norm about the centre. -/
def nrm (v : ℝ × ℝ) : ℝ := 2 * max |v.1| |v.2|

theorem nrm_nonneg (v : ℝ × ℝ) : 0 ≤ nrm v := by unfold nrm; positivity

theorem nrm_smul (t : ℝ) (ht : 0 ≤ t) (v : ℝ × ℝ) : nrm (t • v) = t * nrm v := by
  have e1 : (t • v).1 = t * v.1 := rfl
  have e2 : (t • v).2 = t * v.2 := rfl
  simp only [nrm, e1, e2, abs_mul, abs_of_nonneg ht]
  rw [show t * (2 * max |v.1| |v.2|) = 2 * max (t * |v.1|) (t * |v.2|) from by
    rw [show t * (2 * max |v.1| |v.2|) = 2 * (t * max |v.1| |v.2|) by ring,
        mul_max_of_nonneg |v.1| |v.2| ht]]

/-- The `L∞` radius of `q` about the centre. -/
def radR (q : ℝ × ℝ) : ℝ := nrm (q - c0)

theorem radR_eq (q : ℝ × ℝ) : radR q = 2 * max |q.1 - 1/2| |q.2 - 1/2| := rfl

theorem radR_nonneg (q : ℝ × ℝ) : 0 ≤ radR q := nrm_nonneg _

theorem radR_c0 : radR c0 = 0 := by simp [radR, nrm, c0]

theorem radR_le_one (q : ℝ × ℝ) (hq : q ∈ sq) : radR q ≤ 1 := by
  rw [radR_eq]
  have h1 : |q.1 - 1/2| ≤ 1/2 := abs_sub_le_iff.mpr ⟨by linarith [hq.2.1], by linarith [hq.1]⟩
  have h2 : |q.2 - 1/2| ≤ 1/2 :=
    abs_sub_le_iff.mpr ⟨by linarith [hq.2.2.2], by linarith [hq.2.2.1]⟩
  linarith [max_le h1 h2]

theorem radR_eq_zero_iff (q : ℝ × ℝ) : radR q = 0 ↔ q = c0 := by
  constructor
  · intro h
    rw [radR_eq] at h
    have hm : max |q.1 - 1/2| |q.2 - 1/2| = 0 := by linarith
    have e1 : |q.1 - 1/2| = 0 := le_antisymm (by rw [← hm]; exact le_max_left _ _) (abs_nonneg _)
    have e2 : |q.2 - 1/2| = 0 := le_antisymm (by rw [← hm]; exact le_max_right _ _) (abs_nonneg _)
    have h1 : q.1 = 1/2 := by have := abs_eq_zero.mp e1; linarith
    have h2 : q.2 = 1/2 := by have := abs_eq_zero.mp e2; linarith
    exact Prod.ext h1 h2
  · rintro rfl; exact radR_c0

theorem radR_of_bnd (q : ℝ × ℝ) (hq : q ∈ sq) (hb : q ∈ bndR) : radR q = 1 := by
  rw [radR_eq]
  have h1 : |q.1 - 1/2| ≤ 1/2 := abs_sub_le_iff.mpr ⟨by linarith [hq.2.1], by linarith [hq.1]⟩
  have h2 : |q.2 - 1/2| ≤ 1/2 :=
    abs_sub_le_iff.mpr ⟨by linarith [hq.2.2.2], by linarith [hq.2.2.1]⟩
  have hm : max |q.1 - 1/2| |q.2 - 1/2| = 1/2 := by
    rw [mem_bndR_iff] at hb
    rcases hb with h | h | h | h
    · rw [h, show |(0:ℝ) - 1/2| = 1/2 by norm_num, max_eq_right h1]
    · rw [h, show |(1:ℝ) - 1/2| = 1/2 by norm_num, max_eq_left h2]
    · rw [h, show |(1:ℝ) - 1/2| = 1/2 by norm_num, max_eq_right h1]
    · rw [h, show |(0:ℝ) - 1/2| = 1/2 by norm_num, max_eq_left h2]
  linarith

/-- The radial projection to the boundary. -/
def bptR (q : ℝ × ℝ) : ℝ × ℝ :=
  if radR q = 0 then c0 else c0 + (radR q)⁻¹ • (q - c0)

theorem bptR_eq (q : ℝ × ℝ) (h : radR q ≠ 0) : bptR q = c0 + (radR q)⁻¹ • (q - c0) := by
  rw [bptR, if_neg h]

theorem bptR_c0 : bptR c0 = c0 := by rw [bptR, if_pos radR_c0]

theorem bptR_fst (q : ℝ × ℝ) (h : radR q ≠ 0) :
    (bptR q).1 = 1/2 + (radR q)⁻¹ * (q.1 - 1/2) := by
  rw [bptR_eq q h]; rfl

theorem bptR_snd (q : ℝ × ℝ) (h : radR q ≠ 0) :
    (bptR q).2 = 1/2 + (radR q)⁻¹ * (q.2 - 1/2) := by
  rw [bptR_eq q h]; rfl

theorem bptR_mem_sq (q : ℝ × ℝ) : bptR q ∈ sq := by
  by_cases h : radR q = 0
  · rw [bptR, if_pos h]; exact c0_mem_sq
  · have hpos : 0 < radR q := lt_of_le_of_ne (radR_nonneg q) (Ne.symm h)
    have hb1 : |q.1 - 1/2| ≤ radR q / 2 := by
      rw [radR_eq]; have := le_max_left |q.1 - 1/2| |q.2 - 1/2|; linarith
    have hb2 : |q.2 - 1/2| ≤ radR q / 2 := by
      rw [radR_eq]; have := le_max_right |q.1 - 1/2| |q.2 - 1/2|; linarith
    have hc : (radR q)⁻¹ * (radR q / 2) = 1/2 := by
      rw [div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ h, one_mul]
      norm_num
    have i1 : |(bptR q).1 - 1/2| ≤ 1/2 := by
      rw [bptR_fst q h,
        show 1/2 + (radR q)⁻¹ * (q.1 - 1/2) - 1/2 = (radR q)⁻¹ * (q.1 - 1/2) by ring]
      rw [abs_mul, abs_of_nonneg (le_of_lt (inv_pos.mpr hpos))]
      calc (radR q)⁻¹ * |q.1 - 1/2| ≤ (radR q)⁻¹ * (radR q / 2) :=
            mul_le_mul_of_nonneg_left hb1 (le_of_lt (inv_pos.mpr hpos))
        _ = 1/2 := hc
    have i2 : |(bptR q).2 - 1/2| ≤ 1/2 := by
      rw [bptR_snd q h,
        show 1/2 + (radR q)⁻¹ * (q.2 - 1/2) - 1/2 = (radR q)⁻¹ * (q.2 - 1/2) by ring]
      rw [abs_mul, abs_of_nonneg (le_of_lt (inv_pos.mpr hpos))]
      calc (radR q)⁻¹ * |q.2 - 1/2| ≤ (radR q)⁻¹ * (radR q / 2) :=
            mul_le_mul_of_nonneg_left hb2 (le_of_lt (inv_pos.mpr hpos))
        _ = 1/2 := hc
    rw [mem_sq_iff]
    exact ⟨by linarith [neg_le.mp (abs_le.mp i1).1], by linarith [(abs_le.mp i1).2],
           by linarith [neg_le.mp (abs_le.mp i2).1], by linarith [(abs_le.mp i2).2]⟩

theorem bptR_mem_bnd (q : ℝ × ℝ) (h : radR q ≠ 0) : bptR q ∈ bndR := by
  have hpos : 0 < radR q := lt_of_le_of_ne (radR_nonneg q) (Ne.symm h)
  have hm : max |q.1 - 1/2| |q.2 - 1/2| = radR q / 2 := by rw [radR_eq]; linarith
  rw [mem_bndR_iff]
  rcases max_cases |q.1 - 1/2| |q.2 - 1/2| with ⟨he, _⟩ | ⟨he, _⟩
  · have hb : |q.1 - 1/2| = radR q / 2 := by rw [← hm, he]
    have hval : |(bptR q).1 - 1/2| = 1/2 := by
      rw [bptR_fst q h,
        show 1/2 + (radR q)⁻¹ * (q.1 - 1/2) - 1/2 = (radR q)⁻¹ * (q.1 - 1/2) by ring,
        abs_mul, abs_of_nonneg (le_of_lt (inv_pos.mpr hpos)), hb,
        div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hpos), one_mul]
      norm_num
    rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1/2)).mp hval with hh | hh
    · right; left; linarith
    · right; right; right; linarith
  · have hb : |q.2 - 1/2| = radR q / 2 := by rw [← hm, he]
    have hval : |(bptR q).2 - 1/2| = 1/2 := by
      rw [bptR_snd q h,
        show 1/2 + (radR q)⁻¹ * (q.2 - 1/2) - 1/2 = (radR q)⁻¹ * (q.2 - 1/2) by ring,
        abs_mul, abs_of_nonneg (le_of_lt (inv_pos.mpr hpos)), hb,
        div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hpos), one_mul]
      norm_num
    rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1/2)).mp hval with hh | hh
    · right; right; left; linarith
    · left; linarith

theorem radR_shift (u : ℝ × ℝ) (t : ℝ) (ht : 0 ≤ t) :
    radR (c0 + t • (u - c0)) = t * radR u := by
  have hsub : c0 + t • (u - c0) - c0 = t • (u - c0) := by abel
  rw [radR, hsub, nrm_smul t ht]
  rfl

theorem bptR_shift (u : ℝ × ℝ) (hu : u ∈ sq) (hb : u ∈ bndR) (t : ℝ) (ht : 0 < t) :
    bptR (c0 + t • (u - c0)) = u := by
  have hrad : radR (c0 + t • (u - c0)) = t := by
    rw [radR_shift u t (le_of_lt ht), radR_of_bnd u hu hb, mul_one]
  have hne : radR (c0 + t • (u - c0)) ≠ 0 := by rw [hrad]; exact ne_of_gt ht
  have hsub : c0 + t • (u - c0) - c0 = t • (u - c0) := by abel
  rw [bptR_eq _ hne, hrad, hsub, smul_smul, inv_mul_cancel₀ (ne_of_gt ht), one_smul]
  abel

/-- The "cone" map over `Hbd`. -/
def PhiR (q : ℝ × ℝ) : ℝ × ℝ := c0 + radR q • (Hbd (bptR q) - c0)

/-- The inverse cone map. -/
def PsiR (q : ℝ × ℝ) : ℝ × ℝ := c0 + radR q • (Hi (bptR q) - c0)

theorem PhiR_fst (q : ℝ × ℝ) :
    (PhiR q).1 = 1/2 + radR q * ((Hbd (bptR q)).1 - 1/2) := by rw [PhiR]; rfl

theorem PhiR_snd (q : ℝ × ℝ) :
    (PhiR q).2 = 1/2 + radR q * ((Hbd (bptR q)).2 - 1/2) := by rw [PhiR]; rfl

theorem PhiR_sub (q : ℝ × ℝ) : PhiR q - c0 = radR q • (Hbd (bptR q) - c0) := by
  rw [PhiR]; abel

theorem PsiR_sub (q : ℝ × ℝ) : PsiR q - c0 = radR q • (Hi (bptR q) - c0) := by
  rw [PsiR]; abel

theorem PhiR_c0 : PhiR c0 = c0 := by rw [PhiR, radR_c0, zero_smul, add_zero]

theorem PhiR_fst' (q : ℝ × ℝ) :
    (PhiR q).1 = (1 - radR q) / 2 + radR q * (Hbd (bptR q)).1 := by
  rw [PhiR_fst]; ring

theorem PhiR_snd' (q : ℝ × ℝ) :
    (PhiR q).2 = (1 - radR q) / 2 + radR q * (Hbd (bptR q)).2 := by
  rw [PhiR_snd]; ring

theorem PsiR_fst (q : ℝ × ℝ) :
    (PsiR q).1 = 1/2 + radR q * ((Hi (bptR q)).1 - 1/2) := by rw [PsiR]; rfl

theorem PsiR_snd (q : ℝ × ℝ) :
    (PsiR q).2 = 1/2 + radR q * ((Hi (bptR q)).2 - 1/2) := by rw [PsiR]; rfl

theorem PsiR_fst' (q : ℝ × ℝ) :
    (PsiR q).1 = (1 - radR q) / 2 + radR q * (Hi (bptR q)).1 := by
  rw [PsiR_fst]; ring

theorem PsiR_snd' (q : ℝ × ℝ) :
    (PsiR q).2 = (1 - radR q) / 2 + radR q * (Hi (bptR q)).2 := by
  rw [PsiR_snd]; ring

theorem PhiR_mem_sq (q : ℝ × ℝ) (hq : q ∈ sq) : PhiR q ∈ sq := by
  by_cases h : radR q = 0
  · rw [PhiR, h, zero_smul, add_zero]; exact c0_mem_sq
  · have hu := Hbd_mem_sq (bptR q) (bptR_mem_sq q)
    have ht0 := radR_nonneg q
    have ht1 := radR_le_one q hq
    rw [mem_sq_iff, PhiR_fst', PhiR_snd']
    exact ⟨by nlinarith [hu.1, ht0, ht1], by nlinarith [hu.2.1, ht0, ht1],
           by nlinarith [hu.2.2.1, ht0, ht1], by nlinarith [hu.2.2.2, ht0, ht1]⟩

theorem PsiR_mem_sq (q : ℝ × ℝ) (hq : q ∈ sq) : PsiR q ∈ sq := by
  by_cases h : radR q = 0
  · rw [PsiR, h, zero_smul, add_zero]; exact c0_mem_sq
  · have hu := Hi_mem_sq (bptR q) (bptR_mem_sq q)
    have ht0 := radR_nonneg q
    have ht1 := radR_le_one q hq
    rw [mem_sq_iff, PsiR_fst', PsiR_snd']
    exact ⟨by nlinarith [hu.1, ht0, ht1], by nlinarith [hu.2.1, ht0, ht1],
           by nlinarith [hu.2.2.1, ht0, ht1], by nlinarith [hu.2.2.2, ht0, ht1]⟩

theorem radR_PhiR (q : ℝ × ℝ) (hq : q ∈ sq) : radR (PhiR q) = radR q := by
  have hu := Hbd_mem_sq (bptR q) (bptR_mem_sq q)
  rw [radR, PhiR_sub, nrm_smul _ (radR_nonneg q)]
  show radR q * radR (Hbd (bptR q)) = radR q
  rw [radR_of_bnd _ hu (Hbd_mem_bnd _), mul_one]

theorem radR_PsiR (q : ℝ × ℝ) (hq : q ∈ sq) : radR (PsiR q) = radR q := by
  have hu := Hi_mem_sq (bptR q) (bptR_mem_sq q)
  rw [radR, PsiR_sub, nrm_smul _ (radR_nonneg q)]
  show radR q * radR (Hi (bptR q)) = radR q
  rw [radR_of_bnd _ hu (Hi_mem_bnd _), mul_one]

theorem bptR_PhiR (q : ℝ × ℝ) (hq : q ∈ sq) (h : radR q ≠ 0) :
    bptR (PhiR q) = Hbd (bptR q) := by
  have hpos : 0 < radR q := lt_of_le_of_ne (radR_nonneg q) (Ne.symm h)
  rw [PhiR]
  exact bptR_shift _ (Hbd_mem_sq _ (bptR_mem_sq q)) (Hbd_mem_bnd _) _ hpos

theorem bptR_PsiR (q : ℝ × ℝ) (hq : q ∈ sq) (h : radR q ≠ 0) :
    bptR (PsiR q) = Hi (bptR q) := by
  have hpos : 0 < radR q := lt_of_le_of_ne (radR_nonneg q) (Ne.symm h)
  rw [PsiR]
  exact bptR_shift _ (Hi_mem_sq _ (bptR_mem_sq q)) (Hi_mem_bnd _) _ hpos

theorem PsiR_PhiR (q : ℝ × ℝ) (hq : q ∈ sq) : PsiR (PhiR q) = q := by
  by_cases h : radR q = 0
  · have hq0 : q = c0 := (radR_eq_zero_iff q).mp h
    rw [hq0, PhiR, radR_c0, zero_smul, add_zero, PsiR, radR_c0, zero_smul, add_zero]
  · rw [PsiR, radR_PhiR q hq, bptR_PhiR q hq h,
        Hi_Hbd (bptR q) (bptR_mem_sq q) (bptR_mem_bnd q h), bptR_eq q h,
        show c0 + (radR q)⁻¹ • (q - c0) - c0 = (radR q)⁻¹ • (q - c0) by abel,
        smul_smul, mul_inv_cancel₀ h, one_smul]
    abel

theorem PhiR_PsiR (q : ℝ × ℝ) (hq : q ∈ sq) : PhiR (PsiR q) = q := by
  by_cases h : radR q = 0
  · have hq0 : q = c0 := (radR_eq_zero_iff q).mp h
    rw [hq0, PsiR, radR_c0, zero_smul, add_zero, PhiR, radR_c0, zero_smul, add_zero]
  · rw [PhiR, radR_PsiR q hq, bptR_PsiR q hq h,
        Hbd_Hi (bptR q) (bptR_mem_sq q) (bptR_mem_bnd q h), bptR_eq q h,
        show c0 + (radR q)⁻¹ • (q - c0) - c0 = (radR q)⁻¹ • (q - c0) by abel,
        smul_smul, mul_inv_cancel₀ h, one_smul]
    abel

theorem PhiR_snd_eq_zero (q : ℝ × ℝ) (hq : q ∈ sq) :
    (PhiR q).2 = 0 ↔ radR q = 1 ∧ (Hbd q).2 = 0 := by
  have hu := Hbd_mem_sq (bptR q) (bptR_mem_sq q)
  have ht0 := radR_nonneg q
  have ht1 := radR_le_one q hq
  have hu2 : 0 ≤ (Hbd (bptR q)).2 := hu.2.2.1
  have hval := PhiR_snd' q
  rw [hval]
  have hbpt_eq : radR q = 1 → bptR q = q := by
    intro h1
    rw [bptR_eq q (by rw [h1]; norm_num), h1, inv_one, one_smul]; abel
  constructor
  · intro h0
    have h1 : radR q = 1 := by nlinarith [mul_nonneg ht0 hu2, ht1]
    have h2 : (Hbd (bptR q)).2 = 0 := by nlinarith [mul_nonneg ht0 hu2, ht1]
    exact ⟨h1, by rwa [hbpt_eq h1] at h2⟩
  · rintro ⟨h1, h2⟩
    rw [hbpt_eq h1, h1, h2]; ring

/-! ### The map on the square -/

/-- The coning homeomorphism, as a map of the square. -/
def PhiC (p : Sq) : Sq := ofR (PhiR (toR p)) (PhiR_mem_sq (toR p) (toR_mem p))

/-- Its inverse. -/
def PsiC (p : Sq) : Sq := ofR (PsiR (toR p)) (PsiR_mem_sq (toR p) (toR_mem p))

theorem toR_inj {x y : Sq} (h : toR x = toR y) : x = y := by
  apply Prod.ext
  · apply Subtype.ext
    have := congrArg Prod.fst h
    simpa [toR] using this
  · apply Subtype.ext
    have := congrArg Prod.snd h
    simpa [toR] using this

theorem PsiC_PhiC (p : Sq) : PsiC (PhiC p) = p :=
  toR_inj (by
    show PsiR (PhiR (toR p)) = toR p
    exact PsiR_PhiR (toR p) (toR_mem p))

theorem PhiC_PsiC (p : Sq) : PhiC (PsiC p) = p :=
  toR_inj (by
    show PhiR (PsiR (toR p)) = toR p
    exact PhiR_PsiR (toR p) (toR_mem p))

theorem continuous_toR : Continuous toR := by
  rw [show toR = fun p : Sq => ((p.1 : ℝ), (p.2 : ℝ)) from rfl]
  exact Continuous.prodMk (continuous_subtype_val.comp continuous_fst)
    (continuous_subtype_val.comp continuous_snd)

theorem continuous_radR : Continuous radR := by
  rw [show radR = fun q : ℝ × ℝ => 2 * max |q.1 - 1/2| |q.2 - 1/2| from rfl]
  exact continuous_const.mul ((continuous_fst.sub continuous_const).abs.max
    (continuous_snd.sub continuous_const).abs)

theorem continuousOn_bptR : ContinuousOn bptR {q : ℝ × ℝ | q ≠ c0} := by
  have hne : ∀ q, q ≠ c0 → radR q ≠ 0 := fun q hq h => hq ((radR_eq_zero_iff q).mp h)
  have hbasic : ContinuousOn (fun q : ℝ × ℝ => c0 + (radR q)⁻¹ • (q - c0))
      {q : ℝ × ℝ | q ≠ c0} :=
    continuousOn_const.add (ContinuousOn.smul
      ((continuous_radR.continuousOn).inv₀ hne)
      (continuous_id.continuousOn.sub continuousOn_const))
  exact hbasic.congr (fun q hq => bptR_eq q (hne q hq))

theorem continuous_PhiR : Continuous PhiR := by
  have hne : ∀ q, q ≠ c0 → radR q ≠ 0 := fun q hq h => hq ((radR_eq_zero_iff q).mp h)
  have hmt : MapsTo bptR {q : ℝ × ℝ | q ≠ c0} bndR := fun q hq => bptR_mem_bnd q (hne q hq)
  have hcomp : ContinuousOn (fun q => Hbd (bptR q)) {q : ℝ × ℝ | q ≠ c0} :=
    ContinuousOn.comp continuousOn_Hbd_bndR continuousOn_bptR hmt
  have hbase : ContinuousOn PhiR {q : ℝ × ℝ | q ≠ c0} :=
    continuousOn_const.add (ContinuousOn.smul (continuous_radR.continuousOn)
      (hcomp.sub continuousOn_const))
  have hrad_lim : Tendsto (fun q : ℝ × ℝ => radR q) (𝓝 c0) (𝓝 0) := by
    have := continuous_radR.tendsto c0
    rwa [radR_c0] at this
  have hbound : ∀ q : ℝ × ℝ, ‖PhiR q - c0‖ ≤ radR q := by
    intro q
    rw [PhiR_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg (radR_nonneg q)]
    have h2 : ‖Hbd (bptR q) - c0‖ ≤ 1 := by
      have hu := Hbd_mem_sq (bptR q) (bptR_mem_sq q)
      have ha : (Hbd (bptR q) - c0).1 = (Hbd (bptR q)).1 - 1/2 := rfl
      have hb : (Hbd (bptR q) - c0).2 = (Hbd (bptR q)).2 - 1/2 := rfl
      rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs, ha, hb, max_le_iff]
      exact ⟨abs_le.mpr ⟨by linarith [hu.1], by linarith [hu.2.1]⟩,
             abs_le.mpr ⟨by linarith [hu.2.2.1], by linarith [hu.2.2.2]⟩⟩
    calc radR q * ‖Hbd (bptR q) - c0‖ ≤ radR q * 1 :=
          mul_le_mul_of_nonneg_left h2 (radR_nonneg q)
      _ = radR q := by ring
  have hnorm : Tendsto (fun q => ‖PhiR q - c0‖) (𝓝 c0) (𝓝 0) :=
    squeeze_zero (fun q => norm_nonneg _) hbound hrad_lim
  have hlim : Tendsto (fun q => PhiR q - c0) (𝓝 c0) (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
  have hc0 : ContinuousAt PhiR c0 := by
    have h := hlim.add_const c0
    change Tendsto PhiR (𝓝 c0) (𝓝 (PhiR c0))
    rw [PhiR_c0]
    simpa using h
  rw [continuous_iff_continuousAt]
  intro q
  by_cases h : q = c0
  · subst h; exact hc0
  · exact hbase.continuousAt (isOpen_compl_singleton.mem_nhds (by simpa using h))

theorem continuous_PhiC : Continuous PhiC := by
  have hf : Continuous (fun p : Sq => PhiR (toR p)) := continuous_PhiR.comp continuous_toR
  have hmem : ∀ p : Sq, PhiR (toR p) ∈ sq := fun p => PhiR_mem_sq (toR p) (toR_mem p)
  rw [show PhiC = fun p : Sq => (⟨(PhiR (toR p)).1, (hmem p).1, (hmem p).2.1⟩,
      ⟨(PhiR (toR p)).2, (hmem p).2.2.1, (hmem p).2.2.2⟩) from rfl]
  exact Continuous.prodMk
    (Continuous.subtype_mk hf.fst (fun p => ⟨(hmem p).1, (hmem p).2.1⟩))
    (Continuous.subtype_mk hf.snd (fun p => ⟨(hmem p).2.2.1, (hmem p).2.2.2⟩))

theorem UUR_subset_bndR : UUR ⊆ bndR := by
  intro q hq
  have hq' : q.1 = 0 ∨ q.1 = 1 ∨ q.2 = 0 := hq
  rw [mem_bndR_iff]
  tauto

theorem radR_eq_one_iff (q : ℝ × ℝ) (hq : q ∈ sq) : radR q = 1 ↔ q ∈ bndR := by
  constructor
  · intro h
    have hmax : max |q.1 - 1/2| |q.2 - 1/2| = 1/2 := by rw [radR_eq] at h; linarith
    rw [mem_bndR_iff]
    rcases max_cases |q.1 - 1/2| |q.2 - 1/2| with ⟨he, _⟩ | ⟨he, _⟩
    · have hh1 : |q.1 - 1/2| = 1/2 := by rw [he] at hmax; exact hmax
      rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1/2)).mp hh1 with hh | hh
      · right; left; linarith
      · right; right; right; linarith
    · have hh2 : |q.2 - 1/2| = 1/2 := by rw [he] at hmax; exact hmax
      rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1/2)).mp hh2 with hh | hh
      · right; right; left; linarith
      · left; linarith
  · intro hb
    exact radR_of_bnd q hq hb

theorem PhiC_snd_eq_zero (p : Sq) :
    (PhiC p).2 = 0 ↔ p.1 = 0 ∨ p.1 = 1 ∨ p.2 = 0 := by
  have hq := toR_mem p
  rw [Subtype.ext_iff, Subtype.ext_iff, Subtype.ext_iff, Subtype.ext_iff]
  show (PhiR (toR p)).2 = 0 ↔ (p.1 : ℝ) = 0 ∨ (p.1 : ℝ) = 1 ∨ (p.2 : ℝ) = 0
  rw [PhiR_snd_eq_zero (toR p) hq]
  constructor
  · rintro ⟨h1, h2⟩
    exact (Hbd_second_zero (toR p) hq ((radR_eq_one_iff (toR p) hq).mp h1)).mp h2
  · intro hU
    have hb : toR p ∈ bndR := UUR_subset_bndR hU
    exact ⟨(radR_eq_one_iff (toR p) hq).mpr hb,
           (Hbd_second_zero (toR p) hq hb).mpr hU⟩

/-- **Main lemma.** There is a self-homeomorphism of the square whose second coordinate vanishes
exactly on the left, right and bottom edges. -/
theorem exists_sq_homeomorph :
    ∃ Φ : unitInterval × unitInterval ≃ₜ unitInterval × unitInterval,
      ∀ p : unitInterval × unitInterval, (Φ p).2 = 0 ↔ p.1 = 0 ∨ p.1 = 1 ∨ p.2 = 0 := by
  refine ⟨(isHomeomorph_iff_continuous_bijective.mpr ⟨continuous_PhiC, ?_⟩).homeomorph PhiC, ?_⟩
  · exact ⟨fun a b hab => by
        have := congrArg PsiC hab
        rwa [PsiC_PhiC a, PsiC_PhiC b] at this,
      fun b => ⟨PsiC b, PhiC_PsiC b⟩⟩
  · exact PhiC_snd_eq_zero

end

end Work.StemsB
