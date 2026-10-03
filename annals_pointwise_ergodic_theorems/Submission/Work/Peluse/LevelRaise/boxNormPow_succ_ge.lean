import Mathlib
import Submission.Work.Peluse.BoxNorm.WinDefs
import Submission.Work.Peluse.BoxNorm.boxSumPow_eq_boxNormPow

set_option autoImplicit false
set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Work.Peluse.LevelRaise

open Work.Peluse.BoxNorm

noncomputable section

/-- The `k`-tuples of shifts over the tail `(Q 1, …, Q k)` of `Q`. -/
abbrev Tup {k : ℕ} (Q : Fin (k+1) → Finset ℤ) : Type := Tuple k (fun i : Fin k => Q i.succ)

/-!
# Raising the level of the Gowers box norm

The Gowers box norm is increasing in the degree: if the shift set `Q 0` of the extra direction is
nonempty, then, writing `boxNormPow t Q S f` for the `2^t`-th power `‖f‖^{2^t}_{□^t_{Q}(S)}`,

`boxNormPow k (Q ∘ succ) S f ^ 2 ≤ |Q 0| · boxNormPow (k+1) Q S f`.

The proof is the standard Gowers–Cauchy–Schwarz step, organised through the "sum of squares" form
of the box sum developed in `Submission/Work/Peluse/BoxNorm/boxSumPow_eq_boxNormPow.lean`:

* slicing the level-`(k+1)` cube along its first coordinate factorises the cube term into
  `Φ(x+a')·conj (Φ(x+a))` where `Φ = redCube Q hs hs' f` is the level-`k` cube term, so the
  level-`(k+1)` box sum is `boxScaling · ∑_{hs,hs'} ∑_x ‖∑_{a ∈ Q_0} Φ(x+a)‖²`
  (`normSqSum`);
* the level-`k` box sum is, up to the factor `|Q_0|` and modulo the shift invariance of the
  window sum, the sum of the *same* `Φ`'s over the *same* window;
* Cauchy–Schwarz over the joint index `(hs,hs',x)`, together with the elementary counting bound
  `#{(hs,hs',x) : ∑_a Φ(x+a) ≠ 0} ≤ |Q_0|·|S|·(∏_{i<k}|Q_{i+1}|)²` (a nonvanishing `Φ` exhibits a
  point of `S` at distance `a ∈ Q_0` from `x + total hs'`), gives
  `|Q_0| ‖rawSum_k‖² ≤ |S| (∏_{i<k}|Q_{i+1}|)² · normSqSum`;
* the two normalising constants `boxScaling` of the levels `k` and `k+1` are related by
  `c_k² · |S| · (∏_{i<k}|Q_{i+1}|)² = |Q_0|² · c_{k+1}`, which converts the previous display into
  the theorem.
-/

/-! ## Elementary window facts -/

/-- Membership in the window `ball`. -/
lemma mem_ball_iff {t : ℕ} (P : Fin t → Finset ℤ) (N : ℕ) (x : ℤ) :
    x ∈ ball t P N ↔ x.natAbs ≤ rad t P N := by
  rw [ball, Finset.mem_Icc]
  omega

/-- The radius of the `(k+1)`-window is the radius of the `k`-window plus the `Q 0`-mass. -/
lemma rad_succ (k : ℕ) (Q : Fin (k+1) → Finset ℤ) (N : ℕ) :
    rad (k+1) Q N = rad k (fun i : Fin k => Q i.succ) N + (Q 0).sum (fun z => z.natAbs) := by
  simp only [rad]
  rw [Fin.sum_univ_succ]
  ring

/-- The `Q 0`-shifts fit in the slack between the two windows. -/
lemma natAbs_add_rad_le {k : ℕ} (Q : Fin (k+1) → Finset ℤ) (N : ℕ) {a : ℤ} (ha : a ∈ Q 0) :
    a.natAbs + rad k (fun i : Fin k => Q i.succ) N ≤ rad (k+1) Q N := by
  rw [rad_succ]
  have h : a.natAbs ≤ (Q 0).sum (fun z => z.natAbs) :=
    Finset.single_le_sum (fun z _ => Nat.zero_le _) ha
  omega

/-- `Tuple.total` of a tuple is bounded by the sum of the sizes of its coordinate sets. -/
lemma total_natAbs_le {k : ℕ} (P : Fin k → Finset ℤ) (hs : Tuple k P) :
    (Tuple.total hs).natAbs ≤ ∑ i, (P i).sum (fun z => z.natAbs) := by
  rw [Tuple.total]
  refine le_trans (natAbs_sum_le Finset.univ (fun i => (hs i).1)) ?_
  refine Finset.sum_le_sum fun i _ => ?_
  exact Finset.single_le_sum (fun z _ => Nat.zero_le _) (hs i).2

/-! ## The level-`k` box sum over the level-`(k+1)` window -/

/-- The norm of a real number viewed in `ℂ`. -/
lemma norm_ofReal_complex (r : ℝ) : ‖(r : ℂ)‖ = |r| := by
  have h : ‖(r : ℂ)‖ ^ 2 = r ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]
    ring
  nlinarith [norm_nonneg (r : ℂ), abs_nonneg r, sq_abs r]

/-! ## The Cauchy–Schwarz step -/

/-- The counting bound: the Minkowski-type set `⋃_{a ∈ Q_0} (S - a)` has cardinality at most
`|Q_0|·|S|`. -/
lemma card_biUnion_image_sub_le {k : ℕ} (Q : Fin (k+1) → Finset ℤ) (S : Finset ℤ) :
    ((Q 0).biUnion (fun a : ℤ => S.image (fun s : ℤ => s - a))).card
      ≤ (Q 0).card * S.card := by
  refine le_trans Finset.card_biUnion_le ?_
  refine le_trans (Finset.sum_le_sum (fun a _ => Finset.card_image_le)) ?_
  rw [Finset.sum_const, nsmul_eq_mul, Nat.cast_id]

/-! ## From the raw box sums to the normalised ones -/

/-- The `2^t`-th power of the box norm is the normalising constant times the modulus of the raw
box sum. -/
lemma boxNormPow_eq_scaling_mul_norm (t : ℕ) (P : Fin t → Finset ℤ) (S : Finset ℤ) (f : ℤ → ℂ) :
    boxNormPow t P S f = boxScaling t P S * ‖rawSum t P f‖ := by
  rw [boxNormPow, boxSumPow_eq_scaling, norm_mul, norm_ofReal_complex,
    abs_of_nonneg (boxScaling_nonneg t P S)]

/-- The level-`(k+1)` box norm power is the normalising constant times `normSqSum`. -/
lemma boxNormPow_succ_eq_scaling_mul_normSq {k : ℕ} (Q : Fin (k+1) → Finset ℤ) (S : Finset ℤ)
    (f : ℤ → ℂ) {N : ℕ} (hN : Work.Peluse.SupportIn f N) :
    boxNormPow (k+1) Q S f = boxScaling (k+1) Q S * normSqSum Q f N := by
  rw [boxNormPow, boxSumPow_eq_scaling, rawSum_eq_cubeNormSqSum Q f hN, norm_mul,
    norm_ofReal_complex, norm_ofReal_complex, abs_of_nonneg (boxScaling_nonneg (k+1) Q S),
    abs_of_nonneg (normSqSum_nonneg Q f N)]

/-- `Fintype.card` of the shift tuples is the product of the cardinalities. -/
lemma fintype_card_tuple (k : ℕ) (Q : Fin (k+1) → Finset ℤ) :
    Fintype.card (Tup Q) = ∏ i : Fin k, (Q i.succ).card := by
  rw [Fintype.card_pi]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Fintype.card_coe]

/-! ## The main theorem -/

end

end Work.Peluse.LevelRaise
