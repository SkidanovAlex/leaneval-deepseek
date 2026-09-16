import Submission.CertJTabsSpec2

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000000

open scoped BigOperators
open Finset

/-!
# The accumulation lemmas for the `J`-side regrouping

The `J`-form of the certificate is a double sum over the flat list `cJTrips` of `(β, ã, W)`
entries, and the table evaluation of `Submission/CertJEval` uses, for each signature group, the
*accumulated* weights `gPosL`/`gNegL` (the sums of the `W` over the terms with a common `ã`,
split into positive and negative parts).

Here we prove the algebraic identity that makes this legitimate: for a list of weighted parts
`L : List (ℕ × ℤ)` and any function `f` of the part,

  `∑_{p ∈ L} p.2 · f p.1  =  ∑_{q ∈ accPosOf L} |q.2| · f q.1  −  ∑_{q ∈ accNegOf L} |q.2| · f q.1`,

where `accPosOf`/`accNegOf` accumulate the weights with a common key and split by sign, and then
the two-group version (the four-block sign expansion).
-/

namespace Commons.NumberTheory.MaynardSieve

/-! ## The weighted sum over an accumulated list -/

/-- **Inserting a weighted part into an accumulated list preserves the weighted sum.** -/
theorem sum_accumAux (l : List (ℕ × ℤ)) (p : ℕ × ℤ) (f : ℕ → ℤ) :
    ((accumAux l p).map (fun q => q.2 * f q.1)).sum
      = (l.map (fun q => q.2 * f q.1)).sum + p.2 * f p.1 := by
  induction l with
  | nil => simp [accumAux]
  | cons q t ih =>
    rw [accumAux]
    by_cases h : q.1 = p.1
    · rw [if_pos h]
      simp only [List.map_cons, List.sum_cons]
      rw [h]; ring
    · rw [if_neg h]
      simp only [List.map_cons, List.sum_cons]
      rw [ih]; ring

/-- The left fold of the accumulation preserves the weighted sum. -/
theorem sum_foldl_accumAux (l z : List (ℕ × ℤ)) (f : ℕ → ℤ) :
    ((l.foldl accumAux z).map (fun q => q.2 * f q.1)).sum
      = (z.map (fun q => q.2 * f q.1)).sum + (l.map (fun q => q.2 * f q.1)).sum := by
  induction l generalizing z with
  | nil => simp
  | cons a t ih =>
    rw [List.foldl_cons, ih, sum_accumAux]
    simp only [List.map_cons, List.sum_cons]
    ring

/-- **Accumulating a list preserves the weighted sum.** -/
theorem sum_accum (l : List (ℕ × ℤ)) (f : ℕ → ℤ) :
    ((accum l).map (fun q => q.2 * f q.1)).sum = (l.map (fun q => q.2 * f q.1)).sum := by
  rw [accum, sum_foldl_accumAux]
  simp

/-- Dropping the zero weights does not change the weighted sum. -/
theorem sum_filter_ne_zero (l : List (ℕ × ℤ)) (f : ℕ → ℤ) :
    ((l.filter (fun q => decide (q.2 ≠ 0))).map (fun q => q.2 * f q.1)).sum
      = (l.map (fun q => q.2 * f q.1)).sum := by
  induction l with
  | nil => simp
  | cons q t ih =>
    by_cases h : q.2 = 0
    · rw [List.filter_cons_of_neg (by simp [h])]
      simp only [List.map_cons, List.sum_cons, h]
      rw [ih]; ring
    · rw [List.filter_cons_of_pos (by simp [h])]
      simp only [List.map_cons, List.sum_cons]
      rw [ih]

/-- The weighted sum is invariant under the key sorting. -/
theorem sum_insertionSort (l : List (ℕ × ℤ)) (f : ℕ → ℤ) :
    ((List.insertionSort (fun a b : ℕ × ℤ => a.1 ≤ b.1) l).map (fun q => q.2 * f q.1)).sum
      = (l.map (fun q => q.2 * f q.1)).sum :=
  List.Perm.sum_eq ((List.perm_insertionSort (fun a b : ℕ × ℤ => a.1 ≤ b.1) l).map _)

/-- The weighted sum splits along the sign of the weight. -/
theorem sum_pos_add_neg (l : List (ℕ × ℤ)) (f : ℕ → ℤ) :
    (l.map (fun q => q.2 * f q.1)).sum
      = ((l.filter (fun q => decide (0 < q.2))).map (fun q => q.2 * f q.1)).sum
        + ((l.filter (fun q => decide (q.2 < 0))).map (fun q => q.2 * f q.1)).sum := by
  induction l with
  | nil => simp
  | cons q t ih =>
    rcases lt_trichotomy q.2 0 with h | h | h
    · rw [List.filter_cons_of_neg (by simp; omega), List.filter_cons_of_pos (by simp [h])]
      simp only [List.map_cons, List.sum_cons]
      rw [ih]; ring
    · rw [List.filter_cons_of_neg (by simp; omega), List.filter_cons_of_neg (by simp; omega)]
      simp only [List.map_cons, List.sum_cons, h]
      rw [ih]; ring
    · rw [List.filter_cons_of_pos (by simp [h]), List.filter_cons_of_neg (by simp; omega)]
      simp only [List.map_cons, List.sum_cons]
      rw [ih]; ring

/-- For an all-negative list the weighted sum is the negative of the absolute-value sum. -/
theorem sum_neg_eq_natAbs (l : List (ℕ × ℤ)) (f : ℕ → ℤ) (h : ∀ q ∈ l, q.2 < 0) :
    ((l.map (fun q => q.2 * f q.1)).sum)
      = - ((l.map (fun q => ((q.2.natAbs : ℕ) : ℤ) * f q.1)).sum) := by
  induction l with
  | nil => simp
  | cons q t ih =>
    have hq : q.2 < 0 := h q (by simp)
    have ht : ∀ p ∈ t, p.2 < 0 := fun p hp => h p (by simp [hp])
    have hterm : q.2 * f q.1 = - (((q.2.natAbs : ℕ) : ℤ) * f q.1) := by
      have h1 : q.2 = -(((q.2.natAbs : ℕ) : ℤ)) := Int.eq_neg_natAbs_of_nonpos (le_of_lt hq)
      conv_lhs => rw [h1]
      ring
    rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, ih ht, hterm]
    ring

/-- **Changing the `C`-variable of the `(E)`-kernel, the exact form needed.** -/
theorem sum_pos_eq_natAbs (l : List (ℕ × ℤ)) (f : ℕ → ℤ) (h : ∀ q ∈ l, 0 < q.2) :
    ((l.map (fun q => q.2 * f q.1)).sum)
      = ((l.map (fun q => ((q.2.natAbs : ℕ) : ℤ) * f q.1)).sum) := by
  induction l with
  | nil => simp
  | cons q t ih =>
    have hq : 0 < q.2 := h q (by simp)
    have ht : ∀ p ∈ t, 0 < p.2 := fun p hp => h p (by simp [hp])
    have hterm : q.2 * f q.1 = (((q.2.natAbs : ℕ) : ℤ)) * f q.1 := by
      conv_rhs => rw [Int.natAbs_of_nonneg (le_of_lt hq)]
    rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, ih ht, hterm]


end Commons.NumberTheory.MaynardSieve

/-! ## The accumulation as a function of the weighted list -/

namespace Commons.NumberTheory.MaynardSieve

/-- The accumulation of a list of weighted parts, with the zero weights dropped and the keys
sorted. -/
def accSignedOf (L : List (ℕ × ℤ)) : List (ℕ × ℤ) :=
  List.insertionSort (fun a b : ℕ × ℤ => a.1 ≤ b.1)
    ((accum L).filter (fun q => decide (q.2 ≠ 0)))

/-- The positive accumulated weights (as absolute values). -/
def accPosOf (L : List (ℕ × ℤ)) : List (ℕ × ℕ) :=
  ((accSignedOf L).filter (fun q => decide (0 < q.2))).map (fun q => (q.1, q.2.natAbs))

/-- The negative accumulated weights (as absolute values). -/
def accNegOf (L : List (ℕ × ℤ)) : List (ℕ × ℕ) :=
  ((accSignedOf L).filter (fun q => decide (q.2 < 0))).map (fun q => (q.1, q.2.natAbs))

theorem accPos_eq_accPosOf (T : List (ℕ × ℕ × ℤ)) (i : ℕ) :
    accPos T i = accPosOf ((T.filter (fun t => decide (t.1 = i))).map (fun t => (t.2.1, t.2.2))) :=
  rfl

theorem accNeg_eq_accNegOf (T : List (ℕ × ℕ × ℤ)) (i : ℕ) :
    accNeg T i = accNegOf ((T.filter (fun t => decide (t.1 = i))).map (fun t => (t.2.1, t.2.2))) :=
  rfl

/-- **The weighted sum of a list of weighted parts equals the accumulated sign-split sum.** -/
theorem sum_eq_accPosOf_sub_accNegOf (L : List (ℕ × ℤ)) (f : ℕ → ℤ) :
    (L.map (fun p => p.2 * f p.1)).sum
      = ((accPosOf L).map (fun q => (q.2 : ℤ) * f q.1)).sum
        - ((accNegOf L).map (fun q => (q.2 : ℤ) * f q.1)).sum := by
  have hpermp : ((List.insertionSort (fun a b : ℕ × ℤ => a.1 ≤ b.1)
      ((accum L).filter (fun q => decide (q.2 ≠ 0)))).filter (fun q => decide (0 < q.2))).Perm
      (((accum L).filter (fun q => decide (q.2 ≠ 0))).filter (fun q => decide (0 < q.2))) :=
    (List.perm_insertionSort (fun a b : ℕ × ℤ => a.1 ≤ b.1) _).filter _
  have hpermn : ((List.insertionSort (fun a b : ℕ × ℤ => a.1 ≤ b.1)
      ((accum L).filter (fun q => decide (q.2 ≠ 0)))).filter (fun q => decide (q.2 < 0))).Perm
      (((accum L).filter (fun q => decide (q.2 ≠ 0))).filter (fun q => decide (q.2 < 0))) :=
    (List.perm_insertionSort (fun a b : ℕ × ℤ => a.1 ≤ b.1) _).filter _
  have hpos : ((accPosOf L).map (fun q => (q.2 : ℤ) * f q.1)).sum
      = (((((accum L).filter (fun q => decide (q.2 ≠ 0))).filter (fun q => decide (0 < q.2))).map
          (fun q => ((q.2.natAbs : ℕ) : ℤ) * f q.1)).sum) := by
    rw [accPosOf, accSignedOf, List.map_map]
    rw [List.Perm.sum_eq (hpermp.map _)]
    rfl
  have hneg : ((accNegOf L).map (fun q => (q.2 : ℤ) * f q.1)).sum
      = (((((accum L).filter (fun q => decide (q.2 ≠ 0))).filter (fun q => decide (q.2 < 0))).map
          (fun q => ((q.2.natAbs : ℕ) : ℤ) * f q.1)).sum) := by
    rw [accNegOf, accSignedOf, List.map_map]
    rw [List.Perm.sum_eq (hpermn.map _)]
    rfl
  rw [hpos, hneg, ← sum_accum L f, ← sum_filter_ne_zero ((accum L)) f,
    sum_pos_add_neg, sum_pos_eq_natAbs _ _ (fun q hq => of_decide_eq_true (List.mem_filter.mp hq).2),
    sum_neg_eq_natAbs _ _ (fun q hq => of_decide_eq_true (List.mem_filter.mp hq).2)]
  ring

/-! ## The two-group four-block identity -/

/-- The weighted sum of a signed accumulated group against a shifted kernel. -/
def WblkZ (g : List (ℕ × ℤ)) (K : ℕ → ℕ → ℤ) (m : ℕ) : ℤ :=
  ((g.map (fun b => b.2 * K m b.1)).sum)

/-- The weighted sum of an (absolutely weighted) accumulated group against a shifted kernel. -/
def Wblk (g : List (ℕ × ℕ)) (K : ℕ → ℕ → ℤ) (m : ℕ) : ℤ :=
  ((g.map (fun b => (b.2 : ℤ) * K m b.1)).sum)

/-- The two-group contraction of signed weighted lists. -/
def BLKZ (g h : List (ℕ × ℤ)) (K : ℕ → ℕ → ℤ) : ℤ :=
  ((g.map (fun a => (h.map (fun b => a.2 * b.2 * K a.1 b.1)).sum)).sum)

/-- The four-block contraction of two absolutely weighted groups. -/
def BLK (g h : List (ℕ × ℕ)) (K : ℕ → ℕ → ℤ) : ℤ :=
  ((g.map (fun a => (h.map (fun b => (a.2 : ℤ) * (b.2 : ℤ) * K a.1 b.1)).sum)).sum)

theorem BLKZ_eq_sum_WblkZ (g h : List (ℕ × ℤ)) (K : ℕ → ℕ → ℤ) :
    BLKZ g h K = (g.map (fun a => a.2 * WblkZ h K a.1)).sum := by
  unfold BLKZ WblkZ
  refine congrArg List.sum (List.map_congr_left (fun a _ => ?_))
  trans (h.map (fun b => a.2 * (b.2 * K a.1 b.1))).sum
  · exact congrArg List.sum (List.map_congr_left (fun b _ => by ring))
  · rw [List.sum_map_mul_left]

theorem BLK_eq_sum_Wblk (g h : List (ℕ × ℕ)) (K : ℕ → ℕ → ℤ) :
    BLK g h K = (g.map (fun a => (a.2 : ℤ) * Wblk h K a.1)).sum := by
  unfold BLK Wblk
  refine congrArg List.sum (List.map_congr_left (fun a _ => ?_))
  trans (h.map (fun b => (a.2 : ℤ) * ((b.2 : ℤ) * K a.1 b.1))).sum
  · exact congrArg List.sum (List.map_congr_left (fun b _ => by ring))
  · rw [List.sum_map_mul_left]

/-- **The two-group contraction in terms of the accumulated sign groups.** -/
theorem sum_pair_blocks (L M : List (ℕ × ℤ)) (K : ℕ → ℕ → ℤ) :
    BLKZ L M K
      = BLK (accPosOf L) (accPosOf M) K + BLK (accNegOf L) (accNegOf M) K
        - BLK (accPosOf L) (accNegOf M) K - BLK (accNegOf L) (accPosOf M) K := by
  have hinner : ∀ m : ℕ, WblkZ M K m = Wblk (accPosOf M) K m - Wblk (accNegOf M) K m := by
    intro m
    unfold WblkZ Wblk
    exact sum_eq_accPosOf_sub_accNegOf M (fun n => K m n)
  rw [BLKZ_eq_sum_WblkZ]
  have h1 : (L.map (fun a => a.2 * WblkZ M K a.1))
      = (L.map (fun a => a.2 * Wblk (accPosOf M) K a.1 + -(a.2 * Wblk (accNegOf M) K a.1))) :=
    List.map_congr_left (fun a _ => by rw [hinner a.1]; ring)
  rw [h1, List.sum_map_add]
  have h2 : (L.map (fun a => -(a.2 * Wblk (accNegOf M) K a.1))).sum
      = - ((L.map (fun a => a.2 * Wblk (accNegOf M) K a.1)).sum) := by
    rw [List.sum_neg, List.map_map]
    rfl
  rw [h2,
    sum_eq_accPosOf_sub_accNegOf L (fun m => Wblk (accPosOf M) K m),
    sum_eq_accPosOf_sub_accNegOf L (fun m => Wblk (accNegOf M) K m),
    ← BLK_eq_sum_Wblk (accPosOf L) (accPosOf M) K,
    ← BLK_eq_sum_Wblk (accNegOf L) (accPosOf M) K,
    ← BLK_eq_sum_Wblk (accPosOf L) (accNegOf M) K,
    ← BLK_eq_sum_Wblk (accNegOf L) (accNegOf M) K]
  ring

end Commons.NumberTheory.MaynardSieve
