import Mathlib
import Submission.Work.ZeroEst.one_var_defs
import Submission.Work.ZeroEst.lang24_degree
import Submission.Work.ZeroEst.lam_cramer

namespace Work.ZeroEst

open Polynomial Matrix

/-- The polynomial determinant of the `r × r` submatrix of a family `Q : Fin r → Fin m → ℚ[X]`
selected by `W : Fin r → Fin m`. -/
private noncomputable def pdet {m r : ℕ} (Q : Fin r → Fin m → Polynomial ℚ) (W : Fin r → Fin m) :
    Polynomial ℚ := (Matrix.of (fun a b : Fin r => Q a (W b))).det

private lemma coee_pdet {m r : ℕ} (Q : Fin r → Fin m → Polynomial ℚ) (W : Fin r → Fin m) :
    (Matrix.of (fun a b : Fin r => ((Q a (W b) : Polynomial ℚ) : RatFunc ℚ))).det
      = ((pdet Q W : Polynomial ℚ) : RatFunc ℚ) := by
  rw [pdet]
  exact (RingHom.map_det (algebraMap (Polynomial ℚ) (RatFunc ℚ))
    (Matrix.of (fun a b : Fin r => Q a (W b)))).symm

/-- If the `W`-minor of `Q` does not vanish, then `W` is injective; in particular `r ≤ m`. -/
private lemma injective_of_pdet_ne_zero {m r : ℕ} (Q : Fin r → Fin m → Polynomial ℚ)
    (W : Fin r → Fin m) (h : pdet Q W ≠ 0) : Function.Injective W := by
  intro a b hab
  by_contra hne
  have hcol : ∀ i : Fin r, Q i (W a) = Q i (W b) := fun i => by rw [hab]
  have hz : (Matrix.of (fun a b : Fin r => Q a (W b))).det = 0 := by
    rw [← Matrix.det_transpose (M := Matrix.of (fun a b : Fin r => Q a (W b)))]
    refine Matrix.det_zero_of_row_eq hne ?_
    funext k
    simp only [Matrix.transpose_apply, Matrix.of_apply]
    exact hcol k
  exact h (by rw [pdet]; exact hz)

theorem lamdeg (m : ℕ) (q : Polynomial ℚ) (A : Fin m → Fin m → Polynomial ℚ) (hq : q ≠ 0) :
    ∃ N : ℕ, ∀ (P : Fin m → Polynomial ℚ) (r : ℕ) (V k0 : Fin r → Fin m)
      (lam : Fin r → Fin m → RatFunc ℚ),
      (Matrix.of (fun a b : Fin r => orbit q A P (k0 a) (V b))).det ≠ 0 →
      (∀ k, k < m → ∀ j, ((orbit q A P k j : Polynomial ℚ) : RatFunc ℚ)
          = ∑ l, lam l j * ((orbit q A P k (V l) : Polynomial ℚ) : RatFunc ℚ)) →
      ∀ l j, (lam l j).num.degree ≤ (N : WithBot ℕ) ∧ (lam l j).denom.degree ≤ (N : WithBot ℕ) := by
  obtain ⟨N₀, hN₀⟩ := lam_cramer m q A hq
  refine ⟨m * N₀, ?_⟩
  intro P r V k0 lam hdet hrel l j
  obtain ⟨Q, hQdeg, hQdet, hQcramer⟩ := hN₀ P r V k0 lam hdet hrel
  set p1 : Polynomial ℚ := pdet Q (fun b => if b = l then j else V b) with hp1
  set p0 : Polynomial ℚ := pdet Q V with hp0
  have hp0ne : p0 ≠ 0 := by
    intro h0
    apply hQdet
    have h1 : ((p0 : Polynomial ℚ) : RatFunc ℚ) = 0 := by rw [h0]; simp
    rw [hp0] at h1
    rw [← coee_pdet Q V] at h1
    exact h1
  have hrm : r ≤ m := by
    simpa using Fintype.card_le_of_injective V (injective_of_pdet_ne_zero Q V hp0ne)
  have hmain : ((p0 : Polynomial ℚ) : RatFunc ℚ) * lam l j = ((p1 : Polynomial ℚ) : RatFunc ℚ) := by
    have h := hQcramer l j
    rwa [show (Matrix.of (fun a b : Fin r => ((Q a (V b) : Polynomial ℚ) : RatFunc ℚ))).det
          = ((pdet Q V : Polynomial ℚ) : RatFunc ℚ) from coee_pdet Q V,
        show (Matrix.of (fun a b : Fin r => ((Q a (if b = l then j else V b) : Polynomial ℚ) : RatFunc ℚ))).det
          = ((pdet Q (fun b => if b = l then j else V b) : Polynomial ℚ) : RatFunc ℚ) from
            coee_pdet Q (fun b => if b = l then j else V b)] at h
  have hp0k : ((p0 : Polynomial ℚ) : RatFunc ℚ) ≠ 0 := by
    rw [hp0, ← coee_pdet Q V]
    exact hQdet
  have hlam : lam l j = ((p1 : Polynomial ℚ) : RatFunc ℚ) / ((p0 : Polynomial ℚ) : RatFunc ℚ) := by
    rw [eq_div_iff hp0k, mul_comm]; exact hmain
  have hdeg1 : p1.natDegree ≤ m * N₀ := by
    rw [hp1, pdet]
    exact le_trans (lang24_det_natDegree_le _ N₀ (fun a b => hQdeg a _)) (Nat.mul_le_mul_right N₀ hrm)
  have hdeg0 : p0.natDegree ≤ m * N₀ := by
    rw [hp0, pdet]
    exact le_trans (lang24_det_natDegree_le _ N₀ (fun a b => hQdeg a _)) (Nat.mul_le_mul_right N₀ hrm)
  have hb1 : p1.degree ≤ ((m * N₀ : ℕ) : WithBot ℕ) := by
    refine le_trans (Polynomial.degree_le_natDegree) ?_
    exact_mod_cast hdeg1
  have hb0 : p0.degree ≤ ((m * N₀ : ℕ) : WithBot ℕ) := by
    refine le_trans (Polynomial.degree_le_natDegree) ?_
    exact_mod_cast hdeg0
  constructor
  · by_cases h1 : p1 = 0
    · have hl0 : lam l j = 0 := by rw [hlam, h1]; simp
      rw [hl0, RatFunc.num_zero]; exact bot_le
    · have hdvd : (lam l j).num ∣ p1 := (RatFunc.num_dvd h1).mpr ⟨p0, hp0ne, hlam⟩
      exact le_trans (Polynomial.degree_le_of_dvd hdvd h1) hb1
  · have hdvd : (lam l j).denom ∣ p0 := (RatFunc.denom_dvd hp0ne).mpr ⟨p1, hlam⟩
    exact le_trans (Polynomial.degree_le_of_dvd hdvd hp0ne) hb0

end Work.ZeroEst
