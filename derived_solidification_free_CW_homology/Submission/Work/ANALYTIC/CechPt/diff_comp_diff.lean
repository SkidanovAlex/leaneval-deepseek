import Mathlib
import Submission.Work.ANALYTIC.CechPt.LevelDefs

/-!
# `diff ≫ diff = 0` for the level-`n` dyadic nerve of the interval

We prove that the alternating sum of the pullbacks along the face maps of `Level.lev M •`
squares to zero, i.e. that

`∑ i, (-1)^i (∑ j, (-1)^j F (face j (face i x))) = 0`

for every `F : lev M p → ℤ` and every `x : lev M (p+2)`.

The proof is the standard one: the face maps satisfy the semi-simplicial identity

`face j (face i x) = face (j.predAbove i) (face (i.succAbove j) x)`

(the two possible orders of deleting two coordinates agree, cf.
`Fin.succAbove_succAbove_succAbove_predAbove`) and the map

`φ : (i,j) ↦ (i.succAbove j, j.predAbove i)`

is a fixed-point-free involution of `Fin (p+3) × Fin (p+2)` which flips the parity of `i + j`
(`Fin.succAbove_succAbove_predAbove`, `Fin.predAbove_predAbove_succAbove`).  Hence the double
sum is equal to its own negative, so it vanishes in `ℤ`.
-/

namespace Work.ANALYTIC.CechPt

namespace Level

/-- The two possible orders of deleting two coordinates of an element of `lev M (p+2)` agree:
deleting first the `i`-th and then the `j`-th coordinate is the same as deleting first the
`i.succAbove j`-th and then the `j.predAbove i`-th one.  This is the semi-simplicial identity
`d_j d_i = d_{j.predAbove i} d_{i.succAbove j}` for the face maps of `lev M •`. -/
lemma diffSq_face_face {M p : ℕ} (x : lev M (p + 2)) (i : Fin (p + 3)) (j : Fin (p + 2)) :
    face j (face i x) = face (j.predAbove i) (face (i.succAbove j) x) := by
  refine Subtype.ext ?_
  funext k
  simp only [face]
  rw [← Fin.succAbove_succAbove_succAbove_predAbove]

/-- The value of `(i.succAbove j, j.predAbove i)` differs from `(i, j)` by `± 1` in total:
either the first coordinate is shifted up by one and the second is kept, or the first is kept and
the second is shifted down by one.  In particular the parity of the sum of the two coordinates is
flipped. -/
lemma diffSq_parity {p : ℕ} (i : Fin (p+3)) (j : Fin (p+2)) :
    ((i.succAbove j : Fin (p+3)) : ℕ) + ((j.predAbove i : Fin (p+2)) : ℕ) = (i:ℕ) + (j:ℕ) + 1
    ∨ (i:ℕ) + (j:ℕ) = ((i.succAbove j : Fin (p+3)) : ℕ) + ((j.predAbove i : Fin (p+2)) : ℕ) + 1 := by
  by_cases h : (Fin.castSucc j : Fin (p+3)) < i
  · have h' : (j:ℕ) < (i:ℕ) := by simpa only [Fin.lt_def, Fin.val_castSucc] using h
    right
    rw [Fin.succAbove_of_castSucc_lt i j h, Fin.predAbove_of_castSucc_lt j i h]
    simp only [Fin.val_castSucc, Fin.val_pred]
    omega
  · left
    rw [Fin.succAbove_of_le_castSucc i j (le_of_not_gt h),
      Fin.predAbove_of_le_castSucc j i (le_of_not_gt h)]
    simp only [Fin.val_succ, Fin.coe_castPred]
    omega

/-- The alternating sign attached to `(i.succAbove j, j.predAbove i)` is the negative of the one
attached to `(i, j)`. -/
lemma diffSq_neg_one_pow {p : ℕ} (i : Fin (p+3)) (j : Fin (p+2)) :
    (-1 : ℤ) ^ (((i.succAbove j : Fin (p+3)) : ℕ) + ((j.predAbove i : Fin (p+2)) : ℕ))
      = - (-1 : ℤ) ^ ((i : ℕ) + (j : ℕ)) := by
  rcases diffSq_parity i j with h | h
  · rw [h, pow_succ]; ring
  · rw [h, pow_succ]; ring

/-- The involution `(i, j) ↦ (i.succAbove j, j.predAbove i)` of `Fin (p+3) × Fin (p+2)` used to
cancel the double sum defining `diff (diff F)`. -/
def diffSqSwap {p : ℕ} (q : Fin (p+3) × Fin (p+2)) : Fin (p+3) × Fin (p+2) :=
  (q.1.succAbove q.2, q.2.predAbove q.1)

/-- `diffSqSwap` is an involution (in particular a fixed-point-free bijection). -/
lemma diffSqSwap_involutive {p : ℕ} : Function.Involutive (@diffSqSwap p) := by
  rintro ⟨i, j⟩
  simp only [diffSqSwap, Fin.succAbove_succAbove_predAbove, Fin.predAbove_predAbove_succAbove]

end Level

/-- The cohomological differential `diff` of the level-`n` dyadic nerve of the interval
(`Level.lev M p = ` `(p+1)`-tuples of vertices of `{0,…,M-1}` of diameter `≤ 1`, `Level.face i` deletes
the `i`-th coordinate, `Level.diff f x = ∑ i, (-1)^i * f (face i x)`) squares to zero.  Hint: `face`
is the alternating face map of a simplicial structure on `lev M •`; either build that structure and
use the alternating-face-map-complex construction, or prove the simplicial identity
`face j (face i x) = face (i.castPred _) (face (Fin.succ j) x)` for `i ≤ Fin.castSucc j` and
`face j (face i x) = face (i.pred _) (face (Fin.castSucc j) x)` for `Fin.castSucc j < i`, and cancel
the double sum by the fixed-point-free involution
`(i,j) ↦ (Fin.succ j, i.castPred _)` / `(Fin.castSucc j, i.pred _)` of `Fin (p+3) × Fin (p+2)`,
which flips the parity of `i + j`. -/
theorem diff_comp_diff {M p : ℕ} (F : Work.ANALYTIC.CechPt.Level.lev M p → ℤ) :
    Work.ANALYTIC.CechPt.Level.diff (Work.ANALYTIC.CechPt.Level.diff F) = 0 := by
  funext x
  let G : Fin (p+3) × Fin (p+2) → ℤ :=
    fun q => (-1 : ℤ) ^ ((q.1 : ℕ) + (q.2 : ℕ))
      * F (Level.face q.2 (Level.face q.1 x))
  have hsplit : Work.ANALYTIC.CechPt.Level.diff (Work.ANALYTIC.CechPt.Level.diff F) x
      = ∑ q : Fin (p+3) × Fin (p+2), G q := by
    simp only [Work.ANALYTIC.CechPt.Level.diff, Finset.mul_sum]
    calc ∑ i : Fin (p+3), ∑ j : Fin (p+2),
            (-1 : ℤ) ^ (i : ℕ) * ((-1 : ℤ) ^ (j : ℕ) * F (Level.face j (Level.face i x)))
        = ∑ i : Fin (p+3), ∑ j : Fin (p+2),
            (-1 : ℤ) ^ ((i : ℕ) + (j : ℕ)) * F (Level.face j (Level.face i x)) :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
            rw [← mul_assoc, ← pow_add]
      _ = ∑ q : Fin (p+3) × Fin (p+2), G q :=
          (Fintype.sum_prod_type (fun q : Fin (p+3) × Fin (p+2) =>
            (-1 : ℤ) ^ ((q.1 : ℕ) + (q.2 : ℕ))
              * F (Level.face q.2 (Level.face q.1 x)))).symm
  rw [hsplit]
  let e : Fin (p+3) × Fin (p+2) ≃ Fin (p+3) × Fin (p+2) := Level.diffSqSwap_involutive.toPerm
  have hneg : ∀ q, G (e q) = - G q := by
    rintro ⟨i, j⟩
    show G (Level.diffSqSwap (i, j)) = - G (i, j)
    simp only [Level.diffSqSwap, G]
    rw [← Level.diffSq_face_face x i j, Level.diffSq_neg_one_pow i j]
    ring
  have hfin : (∑ q, G q) = 0 := by
    have h1 : (∑ q, G q) = - (∑ q, G q) :=
      calc (∑ q, G q) = ∑ q, G (e q) := (Equiv.sum_comp e G).symm
        _ = ∑ q, - G q := Finset.sum_congr rfl fun q _ => hneg q
        _ = - (∑ q, G q) := Finset.sum_neg_distrib G
    linarith
  exact hfin

end Work.ANALYTIC.CechPt
