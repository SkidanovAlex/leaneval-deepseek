/-
  annals_wilkies_conjecture, area C4aL (`C4a_lift`): goodness of the pieces.

  Every piece `piece cc σ' P` of the lift is a *good* `LiftPiece`:
  * the two data families `F` and `g` are entire, being polynomial/analytic expressions
    in the coordinates (`analyticAt_pieceF`, `analyticAt_pieceG` from `Basic`);
  * the piece is bounded: the `x`-coordinate (`z 0 = t`) satisfies `0 < t < 1`, the
    `one`-coordinates satisfy `z j ^ 2 = 1` by the clearing equation, and all remaining
    coordinates satisfy `|z j| < 1` by the strict inequalities;
  * the `x`-coordinate is positive on the piece;
  * when the `y`-coordinate is inverted (`σ' 0 = VC.big`) it does not vanish, since the
    inequality `0 < z 1 ^ 2` holds there.
-/
import Mathlib
import Submission.Work.WilC4aL.Basic

set_option autoImplicit false
noncomputable section
open Classical Topology Filter
namespace Work.WilC4aL
open WilkiesDesign WilkiesDesign.CG.C4a

/-! ## 1. The case assignment of a piece -/

/-- The case assignment of the piece `piece cc σ' P`: the `x`-coordinate is `big`
(inverted, piece coordinate `t = 1/x`) and the remaining coordinates follow `σ'`. -/
def sigmaCons {m : ℕ} (σ' : Fin (m + 1) → VC) : Fin (m + 2) → VC := Fin.cons VC.big σ'

/-! ## 2. Evaluating `pieceG` at the distinguished coordinates -/

/-- `pieceG` at the `x`-coordinate with the `q = 0` slot. -/
theorem pieceG_zero_zero {m : ℕ} (σ : Fin (m + 2) → VC) (z : Fin (m + 2) → ℝ) :
    pieceG σ 0 0 z = z 0 := by simp [pieceG]

/-- `pieceG` at a nonzero coordinate, `q = 0` slot, when the coordinate is `big`. -/
theorem pieceG_succ_zero_of_big {m : ℕ} (σ : Fin (m + 2) → VC) (j : Fin (m + 1))
    (z : Fin (m + 2) → ℝ) (h : σ (Fin.succ j) = VC.big) :
    pieceG σ (Fin.succ j) 0 z = (z (Fin.succ j)) ^ 2 := by
  rw [show pieceG σ (Fin.succ j) 0 z =
      (if σ (Fin.succ j) = VC.small then 1 - (z (Fin.succ j)) ^ 2
       else if σ (Fin.succ j) = VC.one then 1 else (z (Fin.succ j)) ^ 2)
      from by simp [pieceG]]
  rw [if_neg (by rw [h]; decide), if_neg (by rw [h]; decide)]

/-! ## 3. The piece is bounded -/

/-- For every point of the piece and every coordinate, `|z j| ≤ 1`.  The `x`-coordinate
lies in `(0,1)`; a `one`-coordinate satisfies `z j ^ 2 = 1` by the clearing equation
`pieceF = 0`; the other coordinates satisfy `|z j| < 1` by the strict inequalities. -/
theorem abs_le_one_of_mem_piece {k m : ℕ} (cc : Fin k → ℝ) (σ' : Fin (m + 1) → VC)
    (P : MvPolynomial (Fin (k + 2 + m) ⊕ Fin (k + 2 + m)) ℝ)
    {z : Fin (m + 2) → ℝ} (hz : z ∈ (piece cc σ' P).set) (j : Fin (m + 2)) :
    |z j| ≤ 1 := by
  have hgq : ∀ (i : Fin (m + 2)) (q : Fin 2), 0 < pieceG (sigmaCons σ') i q z := by
    intro i q
    have h := hz.2 (finProdFinEquiv (i, q))
    simpa only [piece, sigmaCons, Equiv.symm_apply_apply, Prod.fst, Prod.snd] using h
  have hF : pieceF cc (sigmaCons σ') P.totalDegree P z = 0 := by
    have h := hz.1; simpa only [piece, sigmaCons] using h
  -- every `one`-coordinate satisfies `z j ^ 2 = 1`, because `pieceF` is a sum of squares
  have hterm : ∀ i : Fin (m + 2),
      (if (sigmaCons σ') i = VC.one then (z i ^ 2 - 1) ^ 2 else 0) = 0 := by
    have hnn : ∀ i ∈ (Finset.univ : Finset (Fin (m + 2))),
        0 ≤ (if (sigmaCons σ') i = VC.one then (z i ^ 2 - 1) ^ 2 else 0) := by
      intro i _
      split_ifs with h
      · exact sq_nonneg _
      · exact le_refl 0
    have hS : (∑ i : Fin (m + 2),
        (if (sigmaCons σ') i = VC.one then (z i ^ 2 - 1) ^ 2 else 0)) = 0 := by
      have hA : 0 ≤ (Ppart cc (sigmaCons σ') P.totalDegree P z) ^ 2 := sq_nonneg _
      have hB : 0 ≤ ∑ i : Fin (m + 2),
        (if (sigmaCons σ') i = VC.one then (z i ^ 2 - 1) ^ 2 else 0) :=
        Finset.sum_nonneg hnn
      rw [pieceF] at hF
      linarith
    exact fun i => (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hS i (Finset.mem_univ i)
  rcases Fin.eq_zero_or_eq_succ j with hj0 | ⟨j', hj'⟩
  · -- the `x`-coordinate: `0 < z 0` and `0 < 1 - z 0`
    subst hj0
    have h0 : 0 < z 0 := by
      have h := hgq 0 0; rw [pieceG_zero_zero] at h; exact h
    have h1 : z 0 < 1 := by
      have h := hgq 0 1
      rw [show pieceG (sigmaCons σ') 0 1 z = 1 - z 0 from by simp [pieceG]] at h
      linarith
    rw [abs_of_pos h0]; linarith
  · subst hj'
    have hσj : (sigmaCons σ') (Fin.succ j') = σ' j' := by
      simp only [sigmaCons, Fin.cons_succ]
    rcases hv : σ' j' with hs | ho | hb
    · -- `small`: `0 < 1 - z j ^ 2`
      have hσv : (sigmaCons σ') (Fin.succ j') = VC.small := by rw [hσj, hv]
      have h := hgq (Fin.succ j') 0
      rw [show pieceG (sigmaCons σ') (Fin.succ j') 0 z =
          (if (sigmaCons σ') (Fin.succ j') = VC.small then 1 - (z (Fin.succ j')) ^ 2
           else if (sigmaCons σ') (Fin.succ j') = VC.one then 1
           else (z (Fin.succ j')) ^ 2) from by simp [pieceG]] at h
      rw [if_pos hσv] at h
      rw [← sq_le_one_iff_abs_le_one]; nlinarith
    · -- `one`: `z j ^ 2 = 1`
      have h := hterm (Fin.succ j')
      rw [hσj, hv] at h
      rw [if_pos rfl] at h
      have h2 : z (Fin.succ j') ^ 2 = 1 := by
        have h3 := sq_eq_zero_iff.mp h; linarith
      rw [← sq_le_one_iff_abs_le_one]; linarith
    · -- `big`: `0 < 1 - z j ^ 2`
      have hσv : (sigmaCons σ') (Fin.succ j') = VC.big := by rw [hσj, hv]
      have h := hgq (Fin.succ j') 1
      rw [show pieceG (sigmaCons σ') (Fin.succ j') 1 z =
          (if (sigmaCons σ') (Fin.succ j') = VC.small then 1
           else if (sigmaCons σ') (Fin.succ j') = VC.one then 1
           else 1 - (z (Fin.succ j')) ^ 2) from by simp [pieceG]] at h
      rw [if_neg (by rw [hσv]; decide), if_neg (by rw [hσv]; decide)] at h
      rw [← sq_le_one_iff_abs_le_one]; nlinarith

/-! ## 4. The target statement -/

theorem piece_good {k m : ℕ} (cc : Fin k → ℝ) (σ' : Fin (m + 1) → VC)
    (P : MvPolynomial (Fin (k + 2 + m) ⊕ Fin (k + 2 + m)) ℝ) :
    (piece cc σ' P).Good := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro z
    exact analyticAt_pieceF cc (sigmaCons σ') P.totalDegree P z
  · intro j z
    exact analyticAt_pieceG (sigmaCons σ') (finProdFinEquiv.symm j).1
      (finProdFinEquiv.symm j).2 z
  · -- bounded: any two points of the piece are at distance at most `2`
    refine Metric.isBounded_iff.mpr ⟨2, ?_⟩
    intro x hx y hy
    rw [dist_pi_le_iff (by norm_num)]
    intro i
    rw [Real.dist_eq]
    have hx1 := abs_le_one_of_mem_piece cc σ' P hx i
    have hy1 := abs_le_one_of_mem_piece cc σ' P hy i
    calc |x i - y i| ≤ |x i| + |y i| := abs_sub _ _
      _ ≤ 1 + 1 := by linarith
      _ = 2 := by norm_num
  · -- the `x`-coordinate is positive
    intro z hz
    have h := hz.2 (finProdFinEquiv ((0 : Fin (m + 2)), (0 : Fin 2)))
    have h' : 0 < pieceG (Fin.cons VC.big σ') 0 0 z := by simpa [piece] using h
    have h2 : pieceG (Fin.cons VC.big σ') 0 0 z = z 0 := by
      simp only [pieceG]
      split_ifs <;> first | rfl | omega | simp_all
    rwa [h2] at h'
  · -- when `y` is inverted, it does not vanish
    change (piece cc σ' P).inv = true →
      ∀ z : Fin (m + 2) → ℝ, z ∈ (piece cc σ' P).set → z 1 ≠ 0
    intro hinv z hz
    have hσ'0 : σ' 0 = VC.big := by
      have h : (piece cc σ' P).inv = true := hinv
      simp only [piece] at h
      exact decide_eq_true_eq.mp h
    have hσv : ((Fin.cons VC.big σ' : Fin (m + 2) → VC)) (Fin.succ (0 : Fin (m + 1)))
        = VC.big := by
      rw [Fin.cons_succ]; exact hσ'0
    have hh := hz.2 (finProdFinEquiv ((Fin.succ (0 : Fin (m + 1))), (0 : Fin 2)))
    simp only [piece, Equiv.symm_apply_apply] at hh
    rw [pieceG_succ_zero_of_big
      (σ := (Fin.cons VC.big σ' : Fin (m + 2) → VC)) (j := 0) (z := z) hσv] at hh
    exact sq_pos_iff.mp hh

end Work.WilC4aL
