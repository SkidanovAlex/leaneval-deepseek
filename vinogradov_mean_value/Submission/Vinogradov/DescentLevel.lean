/-
Copyright: the formalization team of the Vinogradov mean value theorem project.
-/
import Submission.Vinogradov.OneStep
import Submission.Commons.Combinatorics.LevelBlocks.div_mul_div_eq
import Submission.Commons.Combinatorics.LevelBlocks.blkIdx_basic
import Submission.Commons.Combinatorics.LevelBlocks.div_center_le

/-!
# The level structure of the scale descent (GLYZ §3.3, Lemma 3.6)

GLYZ prove Lemma 3.6 by a *scale descent*: the interval `[0,1]` is partitioned into `n` blocks for
a tower of levels `1 = n 0 | n 1 | ... | n K` (here `|` means "divides"), and at each step the
`ℓ²`-norm of the block sums at level `n j` is compared with the `ℓ²`-norm of the block sums at level
`n (j+1)` using the model decoupling theorem at the *number of sub-blocks* `M j := n (j+1) / n j`.

This module sets up the combinatorics of the levels: the block index of a fine piece, the
sub-block index, the level sums, and the `ℓ²`-functional `lvl2`.
-/

noncomputable section
open MeasureTheory Complex Classical Filter
open scoped Real BigOperators Topology RealInnerProductSpace ENNReal NNReal

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.style.emptyLine false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Submission.Vinogradov

/-! ## 1. Blocks and sub-blocks -/

/-- **The level-`n` block of the `i`-th fine piece.**  The centre of the `i`-th fine piece of the
`m`-fold partition of `[0,1]` lies in exactly one of the `n` intervals `[I/n, (I+1)/n)`; its index
is `floor (n * (2i+1) / (2m))`. -/
def blkIdx (m n : ℕ) (i : Fin m) : ℕ := (n * (2 * i.val + 1)) / (2 * m)

lemma blkIdx_lt {m n : ℕ} (hn : 0 < n) (i : Fin m) : blkIdx m n i < n := by
  rw [blkIdx]
  exact (Commons.Combinatorics.LevelBlocks.blkIdx_basic (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)
    hn i.isLt).1

lemma blkIdx_self {m : ℕ} (i : Fin m) : blkIdx m m i = i.val := by
  rw [blkIdx]
  exact (Commons.Combinatorics.LevelBlocks.blkIdx_basic
    (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)
    (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt) i.isLt).2

/-- The level-`n` block index, as an element of `Fin n`. -/
def blkOf (m n : ℕ) (hn : 0 < n) (i : Fin m) : Fin n :=
  ⟨blkIdx m n i, blkIdx_lt hn i⟩

/-- The index of the sub-block of the level-`n` block of `i` that contains the piece `i`, when each
level-`n` block is divided into `M` equal sub-blocks (so that the next level is `n * M`). -/
def lvlSubBlkIdx (m n M : ℕ) (i : Fin m) : ℕ := blkIdx m (n * M) i % M

/-- The sub-block index as an element of `Fin M`. -/
def lvlSubBlk (m n M : ℕ) (hM : 0 < M) (i : Fin m) : Fin M :=
  ⟨lvlSubBlkIdx m n M i, Nat.mod_lt _ hM⟩

@[simp] lemma lvlSubBlk_val {m n M : ℕ} (hM : 0 < M) (i : Fin m) :
    (lvlSubBlk m n M hM i).val = lvlSubBlkIdx m n M i := rfl

/-- **The refinement of the levels.**  The level-`(n*M)` block of `i` sits inside the level-`n`
block of `i`. -/
lemma blkIdx_div {m n M : ℕ} (hM : 0 < M) (i : Fin m) :
    blkIdx m (n * M) i / M = blkIdx m n i := by
  rw [blkIdx, blkIdx]
  exact Commons.Combinatorics.LevelBlocks.div_mul_div_eq hM

/-- The level-`(n*M)` block index of `i` is the level-`n` index times `M` plus the sub-block
index. -/
lemma blkIdx_eq_subBlkIdx {m n M : ℕ} (hM : 0 < M) (i : Fin m) :
    blkIdx m (n * M) i = M * blkIdx m n i + lvlSubBlkIdx m n M i := by
  have hdiv : blkIdx m (n * M) i / M = blkIdx m n i := blkIdx_div hM i
  have h := Nat.div_add_mod (blkIdx m (n * M) i) M
  rw [hdiv] at h
  exact h.symm

/-! ## 2. The geometry of the levels: the centres lie in the blocks -/

lemma pieceCenter_eq_half (m : ℕ) (j : Fin m) :
    pieceCenter m j = ((2 * j.val + 1 : ℕ) : ℝ) / (2 * m) := by
  rw [pieceCenter]
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simp
  · have hm0 : (m : ℝ) ≠ 0 := by positivity
    field_simp
    push_cast
    ring

/-- **The centre of the `i`-th fine piece lies in the `blkIdx`-th block** of the level-`n`
partition. -/
lemma abs_pieceCenter_sub_blkIdx_le {m n : ℕ} (hn : 0 < n) (i : Fin m) :
    |pieceCenter m i - (blkIdx m n i : ℝ) / (n : ℝ)| ≤ 1 / (n : ℝ) := by
  have hm : 0 < m := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  set J : ℕ := blkIdx m n i with hJ
  have h1 : J * (2 * m) ≤ n * (2 * i.val + 1) := by
    rw [hJ, blkIdx]
    exact Nat.div_mul_le_self _ _
  have h2 : n * (2 * i.val + 1) < (J + 1) * (2 * m) := by
    rw [hJ, blkIdx]
    have h := Nat.div_add_mod (n * (2 * i.val + 1)) (2 * m)
    have hmod := Nat.mod_lt (n * (2 * i.val + 1)) (by positivity : 0 < 2 * m)
    calc n * (2 * i.val + 1)
        = (2 * m) * ((n * (2 * i.val + 1)) / (2 * m)) + (n * (2 * i.val + 1)) % (2 * m) := h.symm
      _ = (n * (2 * i.val + 1)) % (2 * m) + (2 * m) * ((n * (2 * i.val + 1)) / (2 * m)) := by ring
      _ < (2 * m) + (2 * m) * ((n * (2 * i.val + 1)) / (2 * m)) := add_lt_add_left hmod _
      _ = ((n * (2 * i.val + 1)) / (2 * m) + 1) * (2 * m) := by ring
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hm0 : (0 : ℝ) < 2 * m := by positivity
  have h1' : J * (2 * m) ≤ (2 * i.val + 1) * n := by
    calc J * (2 * m) ≤ n * (2 * i.val + 1) := h1
      _ = (2 * i.val + 1) * n := Nat.mul_comm n _
  have hlow : (J : ℝ) / (n : ℝ) ≤ ((2 * i.val + 1 : ℕ) : ℝ) / (2 * m) := by
    rw [div_le_div_iff₀ hn0 hm0]
    exact_mod_cast h1'
  have hhigh : ((2 * i.val + 1 : ℕ) : ℝ) / (2 * m) < ((J : ℝ) + 1) / (n : ℝ) := by
    rw [div_lt_div_iff₀ hm0 hn0]
    have h2r : ((n * (2 * i.val + 1) : ℕ) : ℝ) < ((J + 1) * (2 * m) : ℕ) := by exact_mod_cast h2
    push_cast at h2r ⊢
    linarith
  have he : ((J : ℝ) + 1) / (n : ℝ) = (J : ℝ) / (n : ℝ) + 1 / (n : ℝ) := by rw [add_div]
  rw [pieceCenter_eq_half m i, abs_le]
  constructor
  · linarith
  · rw [he] at hhigh
    linarith

/-- **The sub-block centre in global coordinates.**  Extending the level-`n` blocks by the factor
`M` (so that the next level is `n * M`), the centre of the sub-block containing the piece `i` is
the centre of the corresponding level-`(n*M)` block. -/
lemma subBlk_center {m n M : ℕ} (hn : 0 < n) (hM : 0 < M) (i : Fin m) :
    (blkIdx m n i : ℝ) / (n : ℝ) + (1 / (n : ℝ)) * pieceCenter M (lvlSubBlk m n M hM i)
      = ((blkIdx m (n * M) i : ℝ) + 1 / 2) / ((n * M : ℕ) : ℝ) := by
  have hJ : (blkIdx m (n * M) i : ℝ)
      = (M : ℝ) * (blkIdx m n i : ℝ) + (lvlSubBlkIdx m n M i : ℝ) := by
    rw [blkIdx_eq_subBlkIdx hM i]
    push_cast
    ring
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hcoe : (lvlSubBlkIdx m n M i : ℝ) = (blkIdx m (n * M) i : ℝ) - (M : ℝ) * (blkIdx m n i : ℝ) := by
    rw [hJ]; ring
  rw [pieceCenter]
  simp only [lvlSubBlk]
  rw [hcoe]
  field_simp
  push_cast
  ring

/-- **The proximity of a fine centre to its sub-block centre.** -/
lemma abs_pieceCenter_sub_subBlkIdx_le {m n M : ℕ} (hn : 0 < n) (hM : 0 < M) (i : Fin m) :
    |pieceCenter m i - ((blkIdx m n i : ℝ) / (n : ℝ)
        + (1 / (n : ℝ)) * pieceCenter M (lvlSubBlk m n M hM i))|
      ≤ 1 / (2 * ((n * M : ℕ) : ℝ)) := by
  rw [subBlk_center hn hM i, pieceCenter_eq_half m i]
  have hdiv : ((blkIdx m (n * M) i : ℝ) + 1 / 2) / ((n * M : ℕ) : ℝ)
      = (blkIdx m (n * M) i : ℝ) / ((n * M : ℕ) : ℝ) + 1 / (2 * ((n * M : ℕ) : ℝ)) := by
    rw [add_div]
    ring
  rw [hdiv]
  have hrw : ((2 * i.val + 1 : ℕ) : ℝ) / (2 * m)
      - ((blkIdx m (n * M) i : ℝ) / ((n * M : ℕ) : ℝ) + 1 / (2 * ((n * M : ℕ) : ℝ)))
      = ((2 * i.val + 1 : ℕ) : ℝ) / (2 * m) - (blkIdx m (n * M) i : ℝ) / ((n * M : ℕ) : ℝ)
        - 1 / (2 * ((n * M : ℕ) : ℝ)) := by ring
  rw [hrw]
  exact Commons.Combinatorics.LevelBlocks.div_center_le (m := m) (n := n * M)
    (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt) (Nat.mul_pos hn hM) i.val


/-! ## 3. The numerical condition of the tube lemma at level `n` -/

/-- **The numerical condition of the tube lemma in level form.**  If the Taylor constant of the
curve is dominated by the gain `ε` of the tube lemma (`ha`, a condition on the FIXED constants
only) and the number of sub-blocks satisfies `M^l ≤ (Ctube l)^l n` (`hb`, the same as
`M ≤ Ctube l * n^{1/l}`, i.e. GLYZ's `κ^{(l+1)/l}` scale), then the numerical hypothesis of
`curvePlate_subset_taylorPlate` holds at the level-`n` block. -/
lemma tube_num_condition {l : ℕ} (hl : 1 ≤ l) {A cT R ε δ x : ℝ} {n M : ℕ}
    (hM : 1 ≤ M) (hn : 1 ≤ n) (hε : 0 < ε) (hcT : 0 < cT) (hA : 1 ≤ A) (hR : 0 ≤ R)
    (hx : max δ |x| ≤ 1 / (n : ℝ))
    (ha : 2 * (2 ^ (l + 1) * R * ((l : ℝ) + 1)) ≤ ε * tubeCG l A cT)
    (hb : (M : ℝ) ^ l ≤ (Ctube l) ^ l * (n : ℝ)) :
    2 * (R * ((l : ℝ) + 1) * (max δ |x|) ^ (l + 1))
      < ε * tubeRho l A cT (1 / (2 * ((n * M : ℕ) : ℝ))) := by
  set σ : ℝ := 1 / (2 * ((n * M : ℕ) : ℝ)) with hσ
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hs0 : 0 < σ := by rw [hσ]; positivity
  have hCG0 : 0 < tubeCG l A cT := tubeCG_pos hl hA hcT
  have hCt1 : (1 : ℝ) ≤ Ctube l := one_le_Ctube l
  have hCt0 : 0 < Ctube l := Ctube_pos l
  have hMl0 : (0 : ℝ) ≤ (M : ℝ) ^ l := by positivity
  -- the condition (b) implies the sub-block constraint
  have h3 : (2 : ℝ) ^ (l + 1) * R * ((l : ℝ) + 1) * (M : ℝ) ^ l
      < ε * tubeCG l A cT * (Ctube l) ^ l * (n : ℝ) := by
    have hPpos : (0 : ℝ) < ε * tubeCG l A cT * (Ctube l) ^ l * (n : ℝ) := by positivity
    have hmul1 : (2 * (2 ^ (l + 1) * R * ((l : ℝ) + 1))) * (M : ℝ) ^ l
        ≤ (ε * tubeCG l A cT) * (M : ℝ) ^ l := mul_le_mul_of_nonneg_right ha hMl0
    have hmul2 : (ε * tubeCG l A cT) * (M : ℝ) ^ l
        ≤ (ε * tubeCG l A cT) * ((Ctube l) ^ l * (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    have h := le_trans hmul1 hmul2
    nlinarith [h, hPpos, hMl0]
  -- the two cases of the minimum in `tubeRho_ge`
  have hCtsig : (Ctube l * σ) ^ l = (Ctube l) ^ l / ((2 : ℝ) ^ l * (n : ℝ) ^ l * (M : ℝ) ^ l) := by
    rw [hσ, mul_pow, div_pow, one_pow, mul_pow]
    push_cast
    rw [mul_pow]
    ring
  have hx0 : 0 ≤ max δ |x| := le_trans (abs_nonneg x) (le_max_right _ _)
  have hL : 2 * (R * ((l : ℝ) + 1) * (max δ |x|) ^ (l + 1))
      ≤ 2 * (R * ((l : ℝ) + 1)) / (n : ℝ) ^ (l + 1) := by
    have h1 : (max δ |x|) ^ (l + 1) ≤ (1 / (n : ℝ)) ^ (l + 1) :=
      pow_le_pow_left₀ hx0 hx _
    have h2 : (1 / (n : ℝ)) ^ (l + 1) = 1 / (n : ℝ) ^ (l + 1) := by rw [div_pow, one_pow]
    rw [h2] at h1
    have h3' : R * ((l : ℝ) + 1) * (max δ |x|) ^ (l + 1)
        ≤ R * ((l : ℝ) + 1) * (1 / (n : ℝ) ^ (l + 1)) :=
      mul_le_mul_of_nonneg_left h1 (mul_nonneg hR (by positivity))
    have h4 : R * ((l : ℝ) + 1) * (1 / (n : ℝ) ^ (l + 1))
        = (R * ((l : ℝ) + 1)) / (n : ℝ) ^ (l + 1) := by ring
    rw [h4] at h3'
    have h6 : (2 : ℝ) * (R * ((l : ℝ) + 1) / (n : ℝ) ^ (l + 1))
        = 2 * (R * ((l : ℝ) + 1)) / (n : ℝ) ^ (l + 1) := by ring
    rw [← h6]
    exact mul_le_mul_of_nonneg_left h3' (by norm_num)
  have hY : (2 : ℝ) ^ (l + 1) * R * ((l : ℝ) + 1) * (M : ℝ) ^ l * (n : ℝ) ^ l
      < ε * tubeCG l A cT * (Ctube l) ^ l * (n : ℝ) ^ (l + 1) := by
    have h := mul_lt_mul_of_pos_right h3 (by positivity : (0 : ℝ) < (n : ℝ) ^ l)
    have hp : (n : ℝ) * (n : ℝ) ^ l = (n : ℝ) ^ (l + 1) := by rw [pow_succ']
    have he : ε * tubeCG l A cT * (Ctube l) ^ l * (n : ℝ) * (n : ℝ) ^ l
        = ε * tubeCG l A cT * (Ctube l) ^ l * (n : ℝ) ^ (l + 1) := by
      rw [show ε * tubeCG l A cT * (Ctube l) ^ l * (n : ℝ) * (n : ℝ) ^ l
        = ε * tubeCG l A cT * (Ctube l) ^ l * ((n : ℝ) * (n : ℝ) ^ l) by ring, hp]
    rwa [he] at h
  rcases le_total (Ctube l * σ) 1 with hcase | hcase
  · have hmin : min (Ctube l * σ) 1 = Ctube l * σ := min_eq_left hcase
    have hρ : tubeCG l A cT * (Ctube l * σ) ^ l ≤ tubeRho l A cT σ := by
      have h := tubeRho_ge l A cT σ
      rwa [hmin] at h
    have hgoal : 2 * (R * ((l : ℝ) + 1)) / (n : ℝ) ^ (l + 1)
        < ε * (tubeCG l A cT * ((Ctube l) ^ l
            / ((2 : ℝ) ^ l * (n : ℝ) ^ l * (M : ℝ) ^ l))) := by
      rw [mul_div_assoc', mul_div_assoc', div_lt_div_iff₀ (by positivity) (by positivity)]
      have hring : 2 * (R * ((l : ℝ) + 1)) * ((2 : ℝ) ^ l * (n : ℝ) ^ l * (M : ℝ) ^ l)
          = (2 : ℝ) ^ (l + 1) * R * ((l : ℝ) + 1) * (M : ℝ) ^ l * (n : ℝ) ^ l := by
        rw [pow_succ]; ring
      have hring2 : ε * (tubeCG l A cT * (Ctube l) ^ l) * (n : ℝ) ^ (l + 1)
          = ε * tubeCG l A cT * (Ctube l) ^ l * (n : ℝ) ^ (l + 1) := by ring
      rw [hring, hring2]
      exact hY
    calc 2 * (R * ((l : ℝ) + 1) * (max δ |x|) ^ (l + 1))
        ≤ 2 * (R * ((l : ℝ) + 1)) / (n : ℝ) ^ (l + 1) := hL
      _ < ε * (tubeCG l A cT * ((Ctube l) ^ l
            / ((2 : ℝ) ^ l * (n : ℝ) ^ l * (M : ℝ) ^ l))) := hgoal
      _ = ε * (tubeCG l A cT * (Ctube l * σ) ^ l) := by rw [hCtsig]
      _ ≤ ε * tubeRho l A cT σ := mul_le_mul_of_nonneg_left hρ hε.le
  · have hmin : min (Ctube l * σ) 1 = 1 := min_eq_right hcase
    have hρ : tubeCG l A cT * (1 : ℝ) ^ l ≤ tubeRho l A cT σ := by
      have h := tubeRho_ge l A cT σ
      rwa [hmin] at h
    have ha' : 4 * (R * ((l : ℝ) + 1)) ≤ ε * tubeCG l A cT := by
      have h1 : (4 : ℝ) ≤ 2 * (2 : ℝ) ^ (l + 1) := by
        have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : 1 ≤ l + 1)
        linarith
      have hRl : (0 : ℝ) ≤ R * ((l : ℝ) + 1) := mul_nonneg hR (by positivity)
      have key : 4 * (R * ((l : ℝ) + 1)) ≤ (2 * (2 : ℝ) ^ (l + 1)) * (R * ((l : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_right h1 hRl
      have key2 : 4 * (R * ((l : ℝ) + 1)) ≤ 2 * ((2 : ℝ) ^ (l + 1) * R * ((l : ℝ) + 1)) := by
        calc 4 * (R * ((l : ℝ) + 1)) ≤ (2 * (2 : ℝ) ^ (l + 1)) * (R * ((l : ℝ) + 1)) := key
          _ = 2 * ((2 : ℝ) ^ (l + 1) * R * ((l : ℝ) + 1)) := by ring
      exact le_trans key2 ha
    have hx1 : (max δ |x|) ^ (l + 1) ≤ 1 := by
      have h1 : max δ |x| ≤ 1 := by
        have h2 : 1 / (n : ℝ) ≤ 1 := by
          rw [div_le_one hn0]
          exact_mod_cast hn
        linarith [hx]
      exact pow_le_one₀ hx0 h1
    have hone : (1 : ℝ) ^ l = 1 := one_pow l
    rw [hone, mul_one] at hρ
    have hεC : 0 < ε * tubeCG l A cT := by positivity
    have hlt : 2 * (R * ((l : ℝ) + 1) * (max δ |x|) ^ (l + 1)) < ε * tubeCG l A cT := by
      have h1 : R * ((l : ℝ) + 1) * (max δ |x|) ^ (l + 1) ≤ R * ((l : ℝ) + 1) :=
        mul_le_of_le_one_right (mul_nonneg hR (by positivity)) hx1
      have h2 : 2 * (R * ((l : ℝ) + 1) * (max δ |x|) ^ (l + 1)) ≤ 2 * (R * ((l : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left h1 (by norm_num)
      have h3 : 2 * (R * ((l : ℝ) + 1)) < ε * tubeCG l A cT := by
        have hRl : (0 : ℝ) ≤ R * ((l : ℝ) + 1) := mul_nonneg hR (by positivity)
        linarith [ha', hRl, hεC]
      exact lt_of_le_of_lt h2 h3
    calc 2 * (R * ((l : ℝ) + 1) * (max δ |x|) ^ (l + 1))
        < ε * tubeCG l A cT := hlt
      _ ≤ ε * tubeRho l A cT σ := mul_le_mul_of_nonneg_left hρ hε.le




/-- **The numerical condition of the descent, with the plate enlargement `Λ`.**  The fine plate
may be `Λ` times as large as the sub-block separation; this is the constant enlargement `C` of
GLYZ Lemma 3.6 (see `ROADMAP.lean`, session 53). -/
lemma tube_num_condition_Λ {l : ℕ} (hl : 1 ≤ l) {A cT R ε δ x Λ : ℝ} {n M : ℕ}
    (hM : 1 ≤ M) (hn : 1 ≤ n) (hε : 0 < ε) (hcT : 0 < cT) (hA : 1 ≤ A) (hR : 0 ≤ R)
    (hΛ : 1 ≤ Λ)
    (hx : max δ |x| ≤ Λ / (n : ℝ))
    (ha : 2 * (2 ^ (l + 1) * R * ((l : ℝ) + 1) * Λ ^ (l + 1)) ≤ ε * tubeCG l A cT)
    (hb : (M : ℝ) ^ l ≤ (Ctube l) ^ l * (n : ℝ)) :
    2 * (R * ((l : ℝ) + 1) * (max δ |x|) ^ (l + 1))
      < ε * tubeRho l A cT (Λ / (2 * ((n * M : ℕ) : ℝ))) := by
  set σ : ℝ := Λ / (2 * ((n * M : ℕ) : ℝ)) with hσ
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hs0 : 0 < σ := by rw [hσ]; positivity
  have hCG0 : 0 < tubeCG l A cT := tubeCG_pos hl hA hcT
  have hCt1 : (1 : ℝ) ≤ Ctube l := one_le_Ctube l
  have hCt0 : 0 < Ctube l := Ctube_pos l
  have hMl0 : (0 : ℝ) ≤ (M : ℝ) ^ l := by positivity
  have hΛ0 : (0 : ℝ) < Λ := lt_of_lt_of_le zero_lt_one hΛ
  have hΛl : (1 : ℝ) ≤ Λ ^ l := one_le_pow₀ hΛ
  -- the condition (b) implies the scaled sub-block constraint
  have h3 : (2 : ℝ) ^ (l + 1) * R * ((l : ℝ) + 1) * Λ ^ (l + 1) * (M : ℝ) ^ l
      < ε * tubeCG l A cT * (Ctube l) ^ l * (n : ℝ) * Λ ^ l := by
    have hmul1 : (2 * (2 ^ (l + 1) * R * ((l : ℝ) + 1) * Λ ^ (l + 1))) * (M : ℝ) ^ l
        ≤ (ε * tubeCG l A cT) * (M : ℝ) ^ l := mul_le_mul_of_nonneg_right ha hMl0
    have hmul2 : (ε * tubeCG l A cT) * (M : ℝ) ^ l
        ≤ (ε * tubeCG l A cT) * ((Ctube l) ^ l * (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    have h := le_trans hmul1 hmul2
    have h4 : ε * tubeCG l A cT * (Ctube l) ^ l * (n : ℝ)
        ≤ ε * tubeCG l A cT * (Ctube l) ^ l * (n : ℝ) * Λ ^ l := by
      have h2 : (0 : ℝ) ≤ ε * tubeCG l A cT * (Ctube l) ^ l * (n : ℝ) := by positivity
      nlinarith [h2, hΛl]
    have h5 : (2 * (2 ^ (l + 1) * R * ((l : ℝ) + 1) * Λ ^ (l + 1))) * (M : ℝ) ^ l
        = 2 * ((2 : ℝ) ^ (l + 1) * R * ((l : ℝ) + 1) * Λ ^ (l + 1) * (M : ℝ) ^ l) := by
      ring
    rw [h5] at h
    have hP : (0 : ℝ) < ε * tubeCG l A cT * (Ctube l) ^ l * (n : ℝ) := by positivity
    linarith [h, h4, hP]
  have hx0 : 0 ≤ max δ |x| := le_trans (abs_nonneg x) (le_max_right _ _)
  have hL : 2 * (R * ((l : ℝ) + 1) * (max δ |x|) ^ (l + 1))
      ≤ 2 * (R * ((l : ℝ) + 1)) * Λ ^ (l + 1) / (n : ℝ) ^ (l + 1) := by
    have h1 : (max δ |x|) ^ (l + 1) ≤ (Λ / (n : ℝ)) ^ (l + 1) :=
      pow_le_pow_left₀ hx0 hx _
    rw [div_pow] at h1
    have h2 : R * ((l : ℝ) + 1) * (max δ |x|) ^ (l + 1)
        ≤ R * ((l : ℝ) + 1) * (Λ ^ (l + 1) / (n : ℝ) ^ (l + 1)) :=
      mul_le_mul_of_nonneg_left h1 (mul_nonneg hR (by positivity))
    calc 2 * (R * ((l : ℝ) + 1) * (max δ |x|) ^ (l + 1))
        = 2 * (R * ((l : ℝ) + 1) * (max δ |x|) ^ (l + 1)) := rfl
      _ ≤ 2 * (R * ((l : ℝ) + 1) * (Λ ^ (l + 1) / (n : ℝ) ^ (l + 1))) :=
          mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ = 2 * (R * ((l : ℝ) + 1)) * Λ ^ (l + 1) / (n : ℝ) ^ (l + 1) := by ring
  have hCtsig : (Ctube l * σ) ^ l
      = (Ctube l) ^ l * Λ ^ l / ((2 : ℝ) ^ l * (n : ℝ) ^ l * (M : ℝ) ^ l) := by
    rw [hσ]
    have h : Ctube l * (Λ / (2 * ((n * M : ℕ) : ℝ))) = Ctube l * Λ / (2 * ((n * M : ℕ) : ℝ)) := by
      ring
    rw [h]
    rw [div_pow, mul_pow]
    push_cast
    ring
  have hY : (2 : ℝ) ^ (l + 1) * R * ((l : ℝ) + 1) * Λ ^ (l + 1) * (M : ℝ) ^ l * (n : ℝ) ^ l
      < ε * tubeCG l A cT * (Ctube l) ^ l * Λ ^ l * (n : ℝ) ^ (l + 1) := by
    have h := mul_lt_mul_of_pos_right h3 (by positivity : (0 : ℝ) < (n : ℝ) ^ l)
    have hp : (n : ℝ) * (n : ℝ) ^ l = (n : ℝ) ^ (l + 1) := by rw [pow_succ']
    have he : ε * tubeCG l A cT * (Ctube l) ^ l * (n : ℝ) * Λ ^ l * (n : ℝ) ^ l
        = ε * tubeCG l A cT * (Ctube l) ^ l * Λ ^ l * (n : ℝ) ^ (l + 1) := by
      rw [show ε * tubeCG l A cT * (Ctube l) ^ l * (n : ℝ) * Λ ^ l * (n : ℝ) ^ l
        = ε * tubeCG l A cT * (Ctube l) ^ l * Λ ^ l * ((n : ℝ) * (n : ℝ) ^ l) by ring, hp]
    rwa [he] at h
  rcases le_total (Ctube l * σ) 1 with hcase | hcase
  · have hmin : min (Ctube l * σ) 1 = Ctube l * σ := min_eq_left hcase
    have hρ : tubeCG l A cT * (Ctube l * σ) ^ l ≤ tubeRho l A cT σ := by
      have h := tubeRho_ge l A cT σ
      rwa [hmin] at h
    have hgoal : 2 * (R * ((l : ℝ) + 1)) * Λ ^ (l + 1) / (n : ℝ) ^ (l + 1)
        < ε * (tubeCG l A cT * ((Ctube l) ^ l * Λ ^ l
            / ((2 : ℝ) ^ l * (n : ℝ) ^ l * (M : ℝ) ^ l))) := by
      have hD : (0 : ℝ) < (2 : ℝ) ^ l * (n : ℝ) ^ l * (M : ℝ) ^ l := by positivity
      rw [show ε * (tubeCG l A cT * ((Ctube l) ^ l * Λ ^ l
            / ((2 : ℝ) ^ l * (n : ℝ) ^ l * (M : ℝ) ^ l)))
          = ε * (tubeCG l A cT * ((Ctube l) ^ l * Λ ^ l))
            / ((2 : ℝ) ^ l * (n : ℝ) ^ l * (M : ℝ) ^ l) from by ring]
      rw [div_lt_div_iff₀ (by positivity) hD]
      have hring : (2 * (R * ((l : ℝ) + 1)) * Λ ^ (l + 1))
            * ((2 : ℝ) ^ l * (n : ℝ) ^ l * (M : ℝ) ^ l)
          = (2 : ℝ) ^ (l + 1) * R * ((l : ℝ) + 1) * Λ ^ (l + 1) * (M : ℝ) ^ l
              * (n : ℝ) ^ l := by
        rw [pow_succ]
        ring
      have hring2 : ε * (tubeCG l A cT * ((Ctube l) ^ l * Λ ^ l)) * (n : ℝ) ^ (l + 1)
          = ε * tubeCG l A cT * (Ctube l) ^ l * Λ ^ l * (n : ℝ) ^ (l + 1) := by ring
      rw [hring, hring2]
      exact hY
    calc 2 * (R * ((l : ℝ) + 1) * (max δ |x|) ^ (l + 1))
        ≤ 2 * (R * ((l : ℝ) + 1)) * Λ ^ (l + 1) / (n : ℝ) ^ (l + 1) := hL
      _ < ε * (tubeCG l A cT * ((Ctube l) ^ l * Λ ^ l
            / ((2 : ℝ) ^ l * (n : ℝ) ^ l * (M : ℝ) ^ l))) := hgoal
      _ = ε * (tubeCG l A cT * (Ctube l * σ) ^ l) := by rw [hCtsig]
      _ ≤ ε * tubeRho l A cT σ := mul_le_mul_of_nonneg_left hρ hε.le
  · have hmin : min (Ctube l * σ) 1 = 1 := min_eq_right hcase
    have hρ : tubeCG l A cT * (1 : ℝ) ^ l ≤ tubeRho l A cT σ := by
      have h := tubeRho_ge l A cT σ
      rwa [hmin] at h
    have ha' : 4 * (R * ((l : ℝ) + 1) * Λ ^ (l + 1)) ≤ ε * tubeCG l A cT := by
      have h1 : (4 : ℝ) ≤ 2 * (2 : ℝ) ^ (l + 1) := by
        have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : 1 ≤ l + 1)
        linarith
      have hRl : (0 : ℝ) ≤ R * ((l : ℝ) + 1) * Λ ^ (l + 1) := by positivity
      have key : 4 * (R * ((l : ℝ) + 1) * Λ ^ (l + 1))
          ≤ (2 * (2 : ℝ) ^ (l + 1)) * (R * ((l : ℝ) + 1) * Λ ^ (l + 1)) :=
        mul_le_mul_of_nonneg_right h1 hRl
      have key2 : 4 * (R * ((l : ℝ) + 1) * Λ ^ (l + 1))
          ≤ 2 * ((2 : ℝ) ^ (l + 1) * R * ((l : ℝ) + 1) * Λ ^ (l + 1)) := by
        calc 4 * (R * ((l : ℝ) + 1) * Λ ^ (l + 1))
            ≤ (2 * (2 : ℝ) ^ (l + 1)) * (R * ((l : ℝ) + 1) * Λ ^ (l + 1)) := key
          _ = 2 * ((2 : ℝ) ^ (l + 1) * R * ((l : ℝ) + 1) * Λ ^ (l + 1)) := by ring
      exact le_trans key2 ha
    have hx1 : (max δ |x|) ^ (l + 1) ≤ Λ ^ (l + 1) := by
      have h1 : max δ |x| ≤ Λ := by
        have h2 : Λ / (n : ℝ) ≤ Λ := by
          rw [div_le_iff₀ hn0]
          have h3 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
          nlinarith [hΛ, h3]
        linarith [hx]
      exact pow_le_pow_left₀ hx0 h1 _
    have hone : (1 : ℝ) ^ l = 1 := one_pow l
    rw [hone, mul_one] at hρ
    have hεC : 0 < ε * tubeCG l A cT := by positivity
    have hlt : 2 * (R * ((l : ℝ) + 1) * (max δ |x|) ^ (l + 1)) < ε * tubeCG l A cT := by
      have h1 : R * ((l : ℝ) + 1) * (max δ |x|) ^ (l + 1)
          ≤ R * ((l : ℝ) + 1) * Λ ^ (l + 1) :=
        mul_le_mul_of_nonneg_left hx1 (mul_nonneg hR (by positivity))
      have h2 : 2 * (R * ((l : ℝ) + 1) * (max δ |x|) ^ (l + 1))
          ≤ 2 * (R * ((l : ℝ) + 1) * Λ ^ (l + 1)) :=
        mul_le_mul_of_nonneg_left h1 (by norm_num)
      have h3 : 2 * (R * ((l : ℝ) + 1) * Λ ^ (l + 1)) < ε * tubeCG l A cT := by
        have hRl : (0 : ℝ) ≤ R * ((l : ℝ) + 1) * Λ ^ (l + 1) := by positivity
        linarith [ha', hRl, hεC]
      exact lt_of_le_of_lt h2 h3
    calc 2 * (R * ((l : ℝ) + 1) * (max δ |x|) ^ (l + 1))
        < ε * tubeCG l A cT := hlt
      _ ≤ ε * tubeRho l A cT σ := mul_le_mul_of_nonneg_left hρ hε.le

/-! ## 4. The level sums, and the one-step of the tower -/

/-- The sum of the fine pieces attached to the `r`-th block of the level-`n` partition. -/
def blkSum (l m n : ℕ) (f : Fin m → E l → ℂ) (r : Fin n) : E l → ℂ :=
  fun x => ∑ i ∈ (Finset.univ.filter (fun i : Fin m => blkIdx m n i = r.val)), f i x

/-- **The `ℓ²`-norm of the level-`n` block sums.**  This is the quantity which the scale descent
propagates: at the level `1` there is a single block, so `lvl2 l m 1 f = ‖Σ f‖`, while at the level
`m` the blocks are the individual fine pieces, so `lvl2 l m m f = ‖(‖f i‖)‖_{ℓ²}`. -/
def lvl2 (l m n : ℕ) (f : Fin m → E l → ℂ) : ℝ≥0∞ :=
  l2Norm (fun r : Fin n => lpNorm l (pE l) (blkSum l m n f r))

lemma l2Norm_rpow_two {ι : Type*} [Fintype ι] (a : ι → ℝ≥0∞) :
    (l2Norm a) ^ (2 : ℝ) = ∑ i, a i ^ (2 : ℝ) := by
  rw [l2Norm, ← ENNReal.rpow_mul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one]

lemma blkIdx_one {m : ℕ} (i : Fin m) : blkIdx m 1 i = 0 := by
  rw [blkIdx, one_mul]
  exact Nat.div_eq_of_lt (by omega)

lemma lvl2_one {l m : ℕ} (f : Fin m → E l → ℂ) :
    lvl2 l m 1 f = lpNorm l (pE l) (fun x => ∑ i, f i x) := by
  have hblk : blkSum l m 1 f 0 = fun x => ∑ i, f i x := by
    funext x
    simp only [blkSum]
    have hfilt : (Finset.univ.filter (fun i : Fin m => blkIdx m 1 i = (0 : Fin 1).val))
        = Finset.univ := by
      apply Finset.filter_true_of_mem
      intro i _
      rw [blkIdx_one]
      rfl
    rw [hfilt]
  rw [lvl2, l2Norm, Fin.sum_univ_one, hblk, ← ENNReal.rpow_mul]
  rw [show (2 : ℝ) * (1 / 2) = 1 by norm_num, ENNReal.rpow_one]

lemma lvl2_self {l m : ℕ} (f : Fin m → E l → ℂ) :
    lvl2 l m m f = l2Norm (fun i : Fin m => lpNorm l (pE l) (f i)) := by
  have hblk : ∀ r : Fin m, blkSum l m m f r = f r := by
    intro r
    funext x
    simp only [blkSum]
    have hfilt : (Finset.univ.filter (fun i : Fin m => blkIdx m m i = r.val)) = {r} := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      rw [blkIdx_self]
      exact ⟨fun h => Fin.ext h, fun h => by rw [h]⟩
    rw [hfilt, Finset.sum_singleton]
  simp only [lvl2, hblk]

/-! ## 5. The refinement of the levels -/

/-- The index of the sub-block `r` of the `I`-th block, viewed as a block of the finer level
`n * M`. -/
def finIdx {n M : ℕ} (I : Fin n) (r : Fin M) : Fin (n * M) :=
  ⟨I.val * M + r.val, by
    have h1 : I.val * M + r.val < I.val * M + M := by
      have := r.isLt
      omega
    have h2 : I.val * M + M = (I.val + 1) * M := by ring
    have h3 : (I.val + 1) * M ≤ n * M :=
      Nat.mul_le_mul_right M (Nat.succ_le_of_lt I.isLt)
    omega⟩

@[simp] lemma finIdx_val {n M : ℕ} (I : Fin n) (r : Fin M) :
    (finIdx I r).val = I.val * M + r.val := rfl

lemma finIdx_injective {n M : ℕ} :
    Function.Injective (fun p : Fin n × Fin M => finIdx p.1 p.2) := by
  rintro ⟨I, r⟩ ⟨I', r'⟩ h
  have hval : I.val * M + r.val = I'.val * M + r'.val := by
    simpa [finIdx] using congrArg Fin.val h
  have hr : r.val = r'.val := by
    have h1 : (r.val + I.val * M) % M = (r'.val + I'.val * M) % M := by
      rw [add_comm r.val, add_comm r'.val, hval]
    rw [Nat.add_mul_mod_self_right, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt r.isLt,
      Nat.mod_eq_of_lt r'.isLt] at h1
    exact h1
  have hI : I.val = I'.val := by
    rw [hr] at hval
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero (by rintro rfl; omega))
      (Nat.add_right_cancel hval)
  exact Prod.ext (Fin.ext hI) (Fin.ext hr)

lemma finIdx_surjective {n M : ℕ} : Function.Surjective (fun p : Fin n × Fin M => finIdx p.1 p.2) := by
  rintro ⟨R, hR⟩
  rcases Nat.eq_zero_or_pos M with hM | hM
  · exact absurd hR (by simp [hM])
  · refine ⟨(⟨R / M, ?_⟩, ⟨R % M, Nat.mod_lt _ hM⟩), ?_⟩
    · rw [Nat.div_lt_iff_lt_mul hM]
      exact hR
    · refine Fin.ext ?_
      simp only [finIdx_val]
      rw [Nat.mul_comm]
      exact Nat.div_add_mod R M

/-- The level-`(n*M)` blocks are exactly the sub-blocks of the level-`n` blocks. -/
def finIdxEquiv (n M : ℕ) : Fin n × Fin M ≃ Fin (n * M) :=
  Equiv.ofBijective _ ⟨finIdx_injective, finIdx_surjective⟩

lemma sum_finIdx {n M : ℕ} {β : Type*} [AddCommMonoid β] (g : Fin (n * M) → β) :
    (∑ I : Fin n, ∑ r : Fin M, g (finIdx I r)) = ∑ R : Fin (n * M), g R := by
  have h1 : (∑ I : Fin n, ∑ r : Fin M, g (finIdx I r))
      = ∑ p : Fin n × Fin M, g (finIdx p.1 p.2) :=
        (Fintype.sum_prod_type (f := fun p : Fin n × Fin M => g (finIdx p.1 p.2))).symm
  rw [h1]
  exact Equiv.sum_comp (finIdxEquiv n M) g

/-- **The blocks of a finer level are the sub-blocks of the coarser level.** -/
lemma filter_subBlk_eq {m n M : ℕ} (hM : 0 < M) (I : Fin n) (r : Fin M) :
    ((Finset.univ.filter (fun i : Fin m => blkIdx m n i = I.val)).filter
        (fun i => lvlSubBlkIdx m n M i = r.val))
      = Finset.univ.filter (fun i : Fin m => blkIdx m (n * M) i = (finIdx I r).val) := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [finIdx_val]
  have hdiv : (I.val * M + r.val) / M = I.val := by
    have h := Nat.add_mul_div_left r.val I.val hM
    rw [Nat.div_eq_of_lt r.isLt, zero_add, Nat.mul_comm M I.val] at h
    rw [add_comm (I.val * M) r.val, h]
  have hmod : (I.val * M + r.val) % M = r.val := by
    have h := Nat.add_mul_mod_self_right r.val I.val M
    rw [Nat.mod_eq_of_lt r.isLt] at h
    rw [add_comm (I.val * M) r.val, h]
  constructor
  · rintro ⟨h1, h2⟩
    have hJ := blkIdx_eq_subBlkIdx (n := n) hM i
    rw [h1, h2] at hJ
    rw [hJ]
    ring
  · intro h
    have hJ := blkIdx_eq_subBlkIdx (n := n) hM i
    rw [h] at hJ
    constructor
    · have h2 : blkIdx m (n * M) i / M = blkIdx m n i := blkIdx_div hM i
      rw [h, hdiv] at h2
      exact h2.symm
    · have h2 : blkIdx m (n * M) i % M = lvlSubBlkIdx m n M i := rfl
      rw [h, hmod] at h2
      exact h2.symm


/-! ## 6. The one-step of the tower -/

/-- **The one-step of the scale descent.**  If the model decoupling theorem is available at the
number of sub-blocks `M` and the level-`n` blocks of the fine pieces are refined into `M`
sub-blocks each (so that the next level is `n * M`), then the `ℓ²`-norm of the level-`n` block sums
is bounded by the `ℓ²`-norm of the level-`(n*M)` block sums, with the constant of the model
theorem.  The hypotheses `ha`, `hb` are the FIXED numerical conditions of the tube lemma
(`tube_num_condition`). -/
theorem lvl2_step {l : ℕ} (hl : 1 ≤ l) (D : ℕ → ℝ → E l)
    {A cT R : ℝ} (hbd : CurveBounded l D A) (hA : 1 ≤ A) (htor : CurveTorsion l D cT)
    (hcT : 0 < cT) (htay : CurveTaylor l D R) (hR : 0 ≤ R)
    {m n M : ℕ} (hm : 0 < m) (hn : 0 < n) (hM : 0 < M)
    {Λ : ℝ} (hΛ : 1 ≤ Λ)
    {Λ₁ ε : ℝ} (hε : 0 < ε) (hΛ₁ : Λ * (1 + ε) * Ctube l ≤ Λ₁)
    {C₁ : ℝ≥0∞} (hdec : DecLinScale l M Λ₁ C₁)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hδΛ : δ ≤ Λ / (2 * ((n * M : ℕ) : ℝ)))
    (ha : 2 * (2 ^ (l + 1) * R * ((l : ℝ) + 1) * Λ ^ (l + 1)) ≤ ε * tubeCG l A cT)
    (hb : (M : ℝ) ^ l ≤ (Ctube l) ^ l * (n : ℝ))
    {f : Fin m → E l → ℂ}
    (hf : ∀ i, IsFourierRep l (curvePlate l D δ (pieceCenter m i)) (f i)) :
    lvl2 l m n f ≤ C₁ * lvl2 l m (n * M) f := by
  classical
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hM1 : 1 ≤ M := hM
  -- the per-block one-step
  have hper : ∀ I : Fin n,
      lpNorm l (pE l) (blkSum l m n f I)
        ≤ C₁ * l2Norm (fun r : Fin M =>
            lpNorm l (pE l) (blkSum l m (n * M) f (finIdx I r))) := by
    intro I
    set s : Finset (Fin m) := Finset.univ.filter (fun i => blkIdx m n i = I.val) with hs
    have hsmem : ∀ i : Fin m, i ∈ s ↔ blkIdx m n i = I.val := by
      intro i
      rw [hs]
      simp
    have hcI : ((I.val : ℝ) / (n : ℝ)) ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · positivity
      · rw [div_le_one hnR]
        exact_mod_cast I.isLt.le
    have hcIk : (I.val : ℝ) / (n : ℝ) + 1 / (n : ℝ) ≤ 1 := by
      rw [← add_div, div_le_one hnR]
      exact_mod_cast I.isLt
    have hκ0 : (0 : ℝ) < 1 / (n : ℝ) := by positivity
    have hκ1 : 1 / (n : ℝ) ≤ 1 := by
      rw [div_le_one hnR]
      exact_mod_cast hn
    have huc : ∀ i ∈ s, |pieceCenter m i - (I.val : ℝ) / (n : ℝ)| ≤ 1 / (n : ℝ) := by
      intro i hi
      have h := abs_pieceCenter_sub_blkIdx_le hn i
      rw [(hsmem i).mp hi] at h
      exact h
    have hui : ∀ i ∈ s, pieceCenter m i ∈ Set.Icc (0 : ℝ) 1 := by
      intro i _
      rw [pieceCenter]
      constructor
      · positivity
      · rw [div_le_one (by exact_mod_cast hm)]
        have h : (i.val : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast i.isLt
        linarith
    have hblksub : ∀ i ∈ s, |pieceCenter m i - ((I.val : ℝ) / (n : ℝ)
        + (1 / (n : ℝ)) * pieceCenter M (lvlSubBlk m n M hM i))|
        ≤ (1 / (n : ℝ)) / (2 * (M : ℝ)) := by
      intro i hi
      have h := abs_pieceCenter_sub_subBlkIdx_le hn hM i
      rw [(hsmem i).mp hi] at h
      have he : (1 : ℝ) / (2 * ((n * M : ℕ) : ℝ)) = (1 / (n : ℝ)) / (2 * (M : ℝ)) := by
        push_cast
        ring
      rwa [he] at h
    have hnum : ∀ i ∈ s, 2 * (R * ((l : ℝ) + 1)
        * (max δ |pieceCenter m i - (I.val : ℝ) / (n : ℝ)|) ^ (l + 1))
        < ε * tubeRho l A cT (Λ * ((1 / (n : ℝ)) / (2 * (M : ℝ)))) := by
      intro i hi
      have hx : max δ |pieceCenter m i - (I.val : ℝ) / (n : ℝ)| ≤ Λ / (n : ℝ) := by
        refine max_le ?_ ?_
        · have hle : Λ / (2 * ((n * M : ℕ) : ℝ)) ≤ Λ / (n : ℝ) := by
            rw [div_le_div_iff₀ (by positivity) hnR]
            push_cast
            have hM1' : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
            have h2 : (1 : ℝ) ≤ 2 * (M : ℝ) := by linarith
            have h3 : (n : ℝ) ≤ 2 * ((n : ℝ) * (M : ℝ)) := by
              calc (n : ℝ) = (n : ℝ) * 1 := by ring
                _ ≤ (n : ℝ) * (2 * (M : ℝ)) := mul_le_mul_of_nonneg_left h2 hnR.le
                _ = 2 * ((n : ℝ) * (M : ℝ)) := by ring
            exact mul_le_mul_of_nonneg_left h3 (by linarith)
          exact le_trans hδΛ hle
        · have hle : 1 / (n : ℝ) ≤ Λ / (n : ℝ) := by
            rw [div_le_div_iff₀ hnR hnR]
            have h3 : (n : ℝ) ≤ Λ * (n : ℝ) := by
              calc (n : ℝ) = 1 * (n : ℝ) := by ring
                _ ≤ Λ * (n : ℝ) := mul_le_mul_of_nonneg_right hΛ hnR.le
            linarith
          exact le_trans (huc i hi) hle
      have h := tube_num_condition_Λ (l := l) hl hM1 hn hε hcT hA hR hΛ hx ha hb
      have he : Λ / (2 * ((n * M : ℕ) : ℝ)) = Λ * ((1 / (n : ℝ)) / (2 * (M : ℝ))) := by
        push_cast
        ring
      rwa [he] at h
    have hδκ : δ ≤ Λ * ((1 / (n : ℝ)) / (2 * (M : ℝ))) := by
      have he : Λ / (2 * ((n * M : ℕ) : ℝ)) = Λ * ((1 / (n : ℝ)) / (2 * (M : ℝ))) := by
        push_cast
        ring
      rw [← he]
      exact hδΛ
    have hmain := descentStep (l := l) hl D hbd hA htor hcT htay hR
      (c_I := (I.val : ℝ) / (n : ℝ)) (κ := 1 / (n : ℝ)) (M := M)
      (Λ := Λ) (Λ₁ := Λ₁) (ε := ε) (C₁ := C₁) (s := s) (δ := δ)
      (u := fun i : Fin m => pieceCenter m i)
      (blk := fun i : Fin m => lvlSubBlk m n M hM i) (f := f)
      hcI hcIk hκ0 hκ1 hM1 hΛ hε hΛ₁ hdec hδ0 hδ1 hδκ huc hui hblksub hnum
      (fun i _ => hf i)
    have hL : blkSum l m n f I = fun x => ∑ i ∈ s, f i x := by
      funext x
      simp only [blkSum]
      rw [hs]
    have hR : ∀ r : Fin M,
        (fun x => ∑ i ∈ s.filter (fun i => lvlSubBlk m n M hM i = r), f i x)
          = blkSum l m (n * M) f (finIdx I r) := by
      intro r
      funext x
      simp only [blkSum]
      congr 1
      rw [hs]
      have hfil : (Finset.univ.filter (fun i : Fin m => blkIdx m n i = I.val)).filter
            (fun i => lvlSubBlk m n M hM i = r)
          = (Finset.univ.filter (fun i : Fin m => blkIdx m n i = I.val)).filter
            (fun i => lvlSubBlkIdx m n M i = r.val) := by
        apply Finset.filter_congr
        intro i _
        simp only [Fin.ext_iff, lvlSubBlk_val]
      rw [hfil, filter_subBlk_eq (m := m) hM I r]
    have hRfun : (fun r : Fin M => lpNorm l (pE l)
          (fun x => ∑ i ∈ s.filter (fun i => lvlSubBlk m n M hM i = r), f i x))
        = fun r : Fin M => lpNorm l (pE l) (blkSum l m (n * M) f (finIdx I r)) := by
      funext r
      rw [hR r]
    rw [hL, ← hRfun]
    exact hmain
  -- square and sum
  have hsum : (∑ I : Fin n, (lpNorm l (pE l) (blkSum l m n f I)) ^ (2 : ℝ))
      ≤ C₁ ^ (2 : ℝ)
        * ∑ R : Fin (n * M), (lpNorm l (pE l) (blkSum l m (n * M) f R)) ^ (2 : ℝ) := by
    calc (∑ I : Fin n, (lpNorm l (pE l) (blkSum l m n f I)) ^ (2 : ℝ))
        ≤ ∑ I : Fin n, (C₁ ^ (2 : ℝ) * ∑ r : Fin M,
            (lpNorm l (pE l) (blkSum l m (n * M) f (finIdx I r))) ^ (2 : ℝ)) := by
          refine Finset.sum_le_sum fun I _ => ?_
          have h := ENNReal.rpow_le_rpow (hper I) (by norm_num : (0 : ℝ) ≤ 2)
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2), l2Norm_rpow_two] at h
          exact h
      _ = C₁ ^ (2 : ℝ) * ∑ I : Fin n, ∑ r : Fin M,
            (lpNorm l (pE l) (blkSum l m (n * M) f (finIdx I r))) ^ (2 : ℝ) := by
          rw [Finset.mul_sum]
      _ = C₁ ^ (2 : ℝ)
            * ∑ R : Fin (n * M), (lpNorm l (pE l) (blkSum l m (n * M) f R)) ^ (2 : ℝ) := by
          congr 1
          exact sum_finIdx (g := fun R : Fin (n * M) =>
            (lpNorm l (pE l) (blkSum l m (n * M) f R)) ^ (2 : ℝ))
  rw [lvl2, lvl2, l2Norm, l2Norm]
  have hC1 : (C₁ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) = C₁ := by
    rw [← ENNReal.rpow_mul, show (2 : ℝ) * (1 / 2) = 1 by norm_num, ENNReal.rpow_one]
  have h2 := ENNReal.rpow_le_rpow hsum (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2), hC1] at h2
  exact h2

end Submission.Vinogradov
