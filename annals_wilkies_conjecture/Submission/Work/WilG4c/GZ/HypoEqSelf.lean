/-
  WilG4c / `CritFixOmega` — self-contained proof of the sup-ball / Euclidean-ball bridge
  `HypoRaw = HypoRawE` (the fallback, independent of the delegated version).
-/
import Mathlib
import Submission.Work.WilG4c.CritAux.HypoDefs
import Submission.Work.WilG4c.CritAux

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilkG4c.GZ

open WilkiesDesign

/-- The cube block of `fibPt u y` is `y`. -/
theorem cubePt_fibPt_self {p n : ℕ} (u : Fin (p + (n + 1)) → ℝ) (y : Fin (n + 1) → ℝ) :
    Work.WilkG4c.cubePt (Work.WilkG4c.fibPt u y) = y := by
  funext j
  simp [Work.WilkG4c.fibPt, Work.WilkG4c.cubePt, Fin.append_right]

/-- The parameter block of `fibPt u y` is `parPt u`. -/
theorem parPt_fibPt_self {p n : ℕ} (u : Fin (p + (n + 1)) → ℝ) (y : Fin (n + 1) → ℝ) :
    Work.WilkG4c.parPt (Work.WilkG4c.fibPt u y) = Work.WilkG4c.parPt u := by
  funext i
  simp [Work.WilkG4c.fibPt, Work.WilkG4c.parPt, Fin.append_left]

/-- The sup-ball and the Euclidean-ball condensations agree. -/
theorem hypoRaw_eq_hypoRawE_self (p n : ℕ) (X : Set (Fin (p + (n + 1)) → ℝ)) :
    Work.WilkG4c.HypoRaw p n X = Work.WilkG4c.HypoRawE p n X := by
  ext u
  constructor
  · rintro ⟨ρ, hρ, h⟩
    refine ⟨ρ, hρ, ?_⟩
    intro y hy
    have hcube : Work.WilkG4c.cubePt (Work.WilkG4c.fibPt u y) = y := cubePt_fibPt_self u y
    have hpar : Work.WilkG4c.parPt (Work.WilkG4c.fibPt u y) = Work.WilkG4c.parPt u :=
      parPt_fibPt_self u y
    have hcoord : ∀ j : Fin (n + 1),
        dist (y j) (Work.WilkG4c.cubePt u j) < ρ := by
      intro j
      have hle : (y j - Work.WilkG4c.cubePt u j) ^ 2 ≤
          ∑ k : Fin (n + 1), (y k - Work.WilkG4c.cubePt u k) ^ 2 :=
        Finset.single_le_sum (f := fun k : Fin (n + 1) =>
            (y k - Work.WilkG4c.cubePt u k) ^ 2)
          (fun i _ => sq_nonneg _) (Finset.mem_univ j)
      have hlt : (y j - Work.WilkG4c.cubePt u j) ^ 2 < ρ ^ 2 := lt_of_le_of_lt hle hy
      rw [Real.dist_eq]
      exact (sq_lt_sq.mp hlt).trans_eq (abs_of_pos hρ)
    have hd : dist (Work.WilkG4c.cubePt (Work.WilkG4c.fibPt u y))
        (Work.WilkG4c.cubePt u) < ρ := by
      rw [hcube]
      exact (dist_pi_lt_iff hρ).mpr hcoord
    have := h (Work.WilkG4c.fibPt u y) hpar hd
    simpa only [Work.WilkG4c.fibPt] using this
  · rintro ⟨r, hr, h⟩
    refine ⟨r / ((n : ℝ) + 2), by positivity, ?_⟩
    intro w' hpar hd
    have hρ : (0 : ℝ) < r / ((n : ℝ) + 2) := by positivity
    have hcoord : ∀ j : Fin (n + 1),
        |Work.WilkG4c.cubePt w' j - Work.WilkG4c.cubePt u j| < r / ((n : ℝ) + 2) := by
      intro j
      have hx := (dist_pi_lt_iff hρ).mp hd
      simpa [Real.dist_eq] using hx j
    have hterm : ∀ j : Fin (n + 1),
        (Work.WilkG4c.cubePt w' j - Work.WilkG4c.cubePt u j) ^ 2 <
          (r / ((n : ℝ) + 2)) ^ 2 := by
      intro j
      exact sq_lt_sq.mpr (by rw [abs_of_pos hρ]; exact hcoord j)
    have hbound : ((n : ℝ) + 1) * (r / ((n : ℝ) + 2)) ^ 2 ≤ r ^ 2 := by
      have ha : (0 : ℝ) < (n : ℝ) + 2 := by positivity
      have hlt : ((n : ℝ) + 1) < ((n : ℝ) + 2) ^ 2 := by
        nlinarith [show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n]
      have key2 : ((n : ℝ) + 2) ^ 2 * (r / ((n : ℝ) + 2)) ^ 2 = r ^ 2 := by
        field_simp
        try ring
      calc ((n : ℝ) + 1) * (r / ((n : ℝ) + 2)) ^ 2
          ≤ ((n : ℝ) + 2) ^ 2 * (r / ((n : ℝ) + 2)) ^ 2 :=
            mul_le_mul_of_nonneg_right hlt.le (sq_nonneg _)
        _ = r ^ 2 := key2
    have hsum : ∑ j : Fin (n + 1),
        (Work.WilkG4c.cubePt w' j - Work.WilkG4c.cubePt u j) ^ 2 < r ^ 2 := by
      calc ∑ j : Fin (n + 1), (Work.WilkG4c.cubePt w' j - Work.WilkG4c.cubePt u j) ^ 2
          < ∑ _j : Fin (n + 1), (r / ((n : ℝ) + 2)) ^ 2 :=
            Finset.sum_lt_sum (fun j _ => le_of_lt (hterm j))
              ⟨0, Finset.mem_univ _, hterm 0⟩
        _ = ((n : ℝ) + 1) * (r / ((n : ℝ) + 2)) ^ 2 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            push_cast
            ring
        _ ≤ r ^ 2 := hbound
    have hmem : Work.WilkG4c.fibPt u (Work.WilkG4c.cubePt w') ∈ X := by
      have := h (Work.WilkG4c.cubePt w') hsum
      simpa only [Work.WilkG4c.fibPt] using this
    have hw' : w' = Work.WilkG4c.fibPt u (Work.WilkG4c.cubePt w') := by
      conv_lhs => rw [← Work.WilkG4c.fibPt_cubePt w']
      simp only [Work.WilkG4c.fibPt]
      rw [hpar]
    exact hw' ▸ hmem

end Work.WilkG4c.GZ
