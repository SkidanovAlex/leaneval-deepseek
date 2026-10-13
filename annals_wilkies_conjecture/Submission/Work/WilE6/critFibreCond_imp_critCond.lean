import Mathlib
import Submission.Work.WilE6.Closure

namespace Work.WilE6

/-!
  WilE6: from the fibre conditions of a `DNF` piece of `critSA` to the plain
  Taylor-criterion predicate `critCond`.

  The fibre point of `critSA` carries, besides the point `(u, (z, h))`, the witnesses
  `t, wm, w0, wb, we`.  The conditions `critFibreCond` say that `t` is an attained
  sup-norm distance of `u` and that the polynomial values are bounded by the corresponding
  powers of `t`.  Here we show that these conditions imply `critCond`, i.e. the same
  statements with `t` replaced by the actual distance `dist u 0` and the evaluations taken
  along `idxPhi` rather than the coordinate functions of the ambient space.

  The proof factors into four elementary lemmas:

  * `abs_le_of_sq_shift`: two signed square witnesses `a² + x = t`, `b² - x = t` force
    `|x| ≤ t`;
  * `dist_eq_of_witness`: the sup-norm witnesses (`u_i² - t² + w_i² = 0`, an attained
    index or `t = 0`, and `t = w₀²`) force `t = dist u 0` (via `norm_witness_iff`);
  * `eval_idxPhi_eq`: the evaluation along `idxPhi` agrees with the evaluation along
    `Sum.elim u (Fin.append z h)`;
  * `abs_le_of_wb`: the two signed witnesses for each coordinate give the coordinate bound.
-/

/-- Two signed square witnesses force an absolute value bound: if `a² + x - t = 0` and
`b² - x - t = 0` for some `a`, `b`, then `|x| ≤ t`. -/
lemma abs_le_of_sq_shift {x t : ℝ} (h0 : ∃ a : ℝ, a ^ 2 + x - t = 0)
    (h1 : ∃ b : ℝ, b ^ 2 - x - t = 0) : |x| ≤ t := by
  obtain ⟨a, ha⟩ := h0; obtain ⟨b, hb⟩ := h1
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg a, sq_nonneg b]

/-- The sup-norm witnesses force `t = dist u 0`: if `u_i² - t² + w_i² = 0` for all `i`, the
bound `t²` is attained at some coordinate (or `t = 0`), and `t = w₀²`, then `t = dist u 0`. -/
lemma dist_eq_of_witness {k : ℕ} (u : Fin k → ℝ) (t : ℝ) (w : Fin k → ℝ) (w₀ : ℝ)
    (hw : ∀ i, u i ^ 2 - t ^ 2 + w i ^ 2 = 0)
    (hj : (∃ j : Fin k, u j ^ 2 = t ^ 2) ∨ t = 0)
    (ht : t = w₀ ^ 2) : t = dist u 0 := by
  rcases hj with ⟨j, hj⟩ | ht0
  · exact (norm_witness_iff k j.pos u t).mp ⟨w, w₀, hw, ⟨j, hj⟩, ht⟩
  · subst ht0
    have hu : u = 0 := by
      funext i
      have h := hw i
      have h2 : u i ^ 2 = 0 := by nlinarith [sq_nonneg (w i), sq_nonneg (u i)]
      exact sq_eq_zero_iff.mp h2
    rw [hu]; simp

/-- Evaluating a polynomial in the `(u, (z,h))`-variables along the coordinate functions of
the ambient space agrees with evaluating it along `idxPhi`, provided the `h`-coordinates of
the fibre point are the given chain values. -/
lemma eval_idxPhi_eq {k r p : ℕ} (pnt : Fin (BP k r + FQ k p) → ℝ) (h : Fin r → ℝ)
    (hh : ∀ j : Fin r, pnt (idxH k r p j) = h j) (Q : MvPolynomial (Fin k ⊕ Fin (k + r)) ℝ) :
    MvPolynomial.eval (Sum.elim (fun i => pnt (idxU k r p i))
        (Fin.append (fun i => pnt (idxZ k r p i)) h)) Q
      = MvPolynomial.eval (fun i => pnt (idxPhi k r p i)) Q := by
  have hfun : Sum.elim (fun i => pnt (idxU k r p i)) (Fin.append (fun i => pnt (idxZ k r p i)) h)
      = fun i => pnt (idxPhi k r p i) := by
    funext x
    cases x with
    | inl i => simp [idxPhi]
    | inr y =>
      exact Fin.addCases
        (motive := fun y => Sum.elim (fun i => pnt (idxU k r p i))
            (Fin.append (fun i => pnt (idxZ k r p i)) h) (Sum.inr y)
          = pnt (idxPhi k r p (Sum.inr y)))
        (fun i => by simp [Fin.append_left])
        (fun j => by simp [Fin.append_right, hh])
        y
  rw [hfun]

/-- The two signed witnesses for the `i`-th coordinate bound (`|u_i| ≤ t`) give the bound. -/
lemma abs_le_of_wb {k p : ℕ} (hp : p ≤ k) (u : Fin k → ℝ) (wb : Fin (2*p) → ℝ) (t : ℝ)
    (h : ∀ b : Fin (2*p), wb b ^ 2 + (if (b.1 % 2 == 0) then u ⟨b.1/2, div2_lt hp b⟩
      else -u ⟨b.1/2, div2_lt hp b⟩) - t = 0)
    (i : Fin p) : |u ⟨i.1, lt_of_lt_of_le i.2 hp⟩| ≤ t := by
  have hfin0 : ((⟨(⟨2*i.1, by omega⟩ : Fin (2*p)).1 / 2, div2_lt hp ⟨2*i.1, by omega⟩⟩ : Fin k))
      = ⟨i.1, lt_of_lt_of_le i.2 hp⟩ := by apply Fin.ext; dsimp only; omega
  have hfin1 : ((⟨(⟨2*i.1+1, by omega⟩ : Fin (2*p)).1 / 2, div2_lt hp ⟨2*i.1+1, by omega⟩⟩ : Fin k))
      = ⟨i.1, lt_of_lt_of_le i.2 hp⟩ := by apply Fin.ext; dsimp only; omega
  refine abs_le_of_sq_shift ⟨wb ⟨2*i.1, by omega⟩, ?_⟩ ⟨wb ⟨2*i.1+1, by omega⟩, ?_⟩
  · have hb := h ⟨2*i.1, by omega⟩
    simp only [Nat.mul_mod_right] at hb
    rw [hfin0] at hb
    exact hb
  · have hb := h ⟨2*i.1+1, by omega⟩
    have hmod : (⟨2*i.1+1, by omega⟩ : Fin (2*p)).1 % 2 = 1 := by dsimp only; omega
    rw [hmod] at hb
    rw [if_neg (by decide : ¬(((1:ℕ) == 0) = true))] at hb
    rw [hfin1] at hb
    exact hb

theorem critFibreCond_imp_critCond {k r p : ℕ} (hp : p ≤ k) (κ : ℕ) (hκ : 1 ≤ κ) (P : MvPolynomial (Fin k ⊕ Fin (k + r)) ℝ) (Gs : List (MvPolynomial (Fin k ⊕ Fin (k + r)) ℝ)) (h : Fin r → ℝ) (pnt : Fin (Work.WilE6.BP k r + Work.WilE6.FQ k p) → ℝ) (hh : ∀ j : Fin r, pnt (Work.WilE6.idxH k r p j) = h j) (j : Fin (k + 1)) (hj : Work.WilE6.critFibreCond (k := k) (r := r) (p := p) hp κ P Gs j pnt) : Work.WilE6.critCond (k := k) (r := r) (p := p) hp κ P Gs (fun i => pnt (Work.WilE6.idxZ k r p i)) h (fun i => pnt (Work.WilE6.idxU k r p i)) := by
  simp only [critFibreCond] at hj
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hj
  -- §1. The `t`-coordinate is the sup-norm distance of `u`.
  have ht : pnt (idxT k r p) = dist (fun i => pnt (idxU k r p i)) 0 := by
    by_cases hjk : (j : ℕ) < k
    · have h2' := h2
      rw [dif_pos hjk] at h2'
      refine dist_eq_of_witness (fun i => pnt (idxU k r p i)) (pnt (idxT k r p))
        (fun i => pnt (idxWm k r p i)) (pnt (idxW0 k r p)) ?_ ?_ ?_
      · intro i; exact h1 i
      · left; exact ⟨⟨j, hjk⟩, by linarith [h2']⟩
      · linarith [h3]
    · have h2' := h2
      rw [dif_neg hjk] at h2'
      refine dist_eq_of_witness (fun i => pnt (idxU k r p i)) (pnt (idxT k r p))
        (fun i => pnt (idxWm k r p i)) (pnt (idxW0 k r p)) ?_ ?_ ?_
      · intro i; exact h1 i
      · right; exact h2'
      · linarith [h3]
  -- §2. The two equation witnesses bound `|P|` by `t^{κ²}`.
  have h5_0 : pnt (idxWe k r p 0) ^ 2
      + MvPolynomial.eval (fun i => pnt (idxPhi k r p i)) P - pnt (idxT k r p) ^ (κ ^ 2) = 0 := by
    have := h5 0; simpa using this
  have h5_1 : pnt (idxWe k r p 1) ^ 2
      + (-(MvPolynomial.eval (fun i => pnt (idxPhi k r p i)) P)) - pnt (idxT k r p) ^ (κ ^ 2) = 0 := by
    have := h5 1; simpa using this
  have hPabs : |MvPolynomial.eval (fun i => pnt (idxPhi k r p i)) P| ≤ pnt (idxT k r p) ^ (κ ^ 2) := by
    rw [abs_le]
    constructor
    · nlinarith [sq_nonneg (pnt (idxWe k r p 1))]
    · nlinarith [sq_nonneg (pnt (idxWe k r p 0))]
  simp only [critCond]
  refine ⟨?_, ?_, ?_⟩
  · rw [eval_idxPhi_eq pnt h hh P, ← ht]
    exact hPabs
  · intro i
    rw [← ht]
    exact abs_le_of_wb hp (fun i => pnt (idxU k r p i)) (fun b => pnt (idxWb k r p b)) _ h4 i
  · intro G hG
    rw [eval_idxPhi_eq pnt h hh G, ← ht]
    exact h6 G hG

end Work.WilE6
