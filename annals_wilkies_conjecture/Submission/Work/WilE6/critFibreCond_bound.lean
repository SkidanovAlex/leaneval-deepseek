import Mathlib
import Submission.Work.WilE6.Block
import Submission.Work.WilE6.CritSA
import Submission.Work.WilE6.Base
import Submission.Work.WilE6.norm_witness_iff
import Submission.Work.WilE6.critFibreCond_imp_critCond

namespace Work.WilE6

/-!
  `Work.WilE6.critFibreCond_bound`

  A point `v` of the fibre of `critSA` (coordinates `u, t, wm, w0, wb, we`) whose
  `critFibreCond` holds is not far from the fibre origin: every fibre coordinate is
  bounded by `√(2·t)` where `t = dist (projU v) 0` is the sup-norm distance of the
  `u`-block, provided `t ≤ 1`.

  The individual estimates are

  * `u_i`, `t`  : bounded by `t ≤ √(2t)`;
  * `wm_i`      : `wm_i^2 = t^2 - u_i^2 ≤ t^2`;
  * `w0`        : `w0^2 = t`;
  * `wb_b`      : `wb_b^2 = t^(κ²) ± u_{b/2} ≤ t^(κ²) + t ≤ 2t` (as `κ ≥ 1`, `t ≤ 1`);
  * `we_e`      : adding the two equations (`e = 0, 1`) kills the equation value and gives
                  `we_0^2 + we_1^2 = 2 t^(κ²)`, hence `we_e^2 ≤ 2 t^(κ²) ≤ 2t`.

  The blocks `wm`, `w0`, `wb`, `we` are also available as standalone sibling lemmas
  (`critFibreCond_wm_w0_bound`, `critFibreCond_wb_bound`, `critFibreCond_we_bound`); we
  give the proof inline so that this file is self-contained apart from
  `dist_eq_of_witness` (the identification of the `t`-coordinate with the sup-norm
  distance, proved in `critFibreCond_imp_critCond`).
-/

/-- The `t`-coordinate of a fibre point satisfying `critFibreCond` is the sup-norm distance
of its `u`-block from the origin.  (`dist_eq_of_witness` in `critFibreCond_imp_critCond`.) -/
theorem critFibreCond_bound_t {k r p : ℕ} (hp : p ≤ k) (κ : ℕ)
    (P : MvPolynomial (Fin k ⊕ Fin (k + r)) ℝ)
    (Gs : List (MvPolynomial (Fin k ⊕ Fin (k + r)) ℝ))
    (c : WilkiesDesign.E.EAChain k r) (z : Fin k → ℝ) (v : Fin (FQ k p) → ℝ)
    (j : Fin (k + 1))
    (h : critFibreCond (p := p) hp κ P Gs j (Fin.append (graphPt c z) v)) :
    v (fT k p) = dist (projU k p v) 0 := by
  have hc := h
  simp only [BP, critFibreCond] at hc
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hc
  show v (fT k p) = dist (fun i => v (fU k p i)) 0
  refine dist_eq_of_witness (fun i => v (fU k p i)) (v (fT k p))
    (fun i => v (fWm k p i)) (v (fW0 k p)) ?_ ?_ ?_
  · intro i
    simpa only [append_gp_idxU, append_gp_idxT, append_gp_idxWm] using h1 i
  · by_cases hj : (j : ℕ) < k
    · left
      refine ⟨⟨(j : ℕ), hj⟩, ?_⟩
      have hh := h2
      rw [dite_eq_left hj] at hh
      have hh2 : v (fU k p ⟨(j : ℕ), hj⟩) ^ 2 - v (fT k p) ^ 2 = 0 := by
        simpa only [append_gp_idxU, append_gp_idxT] using hh
      linarith
    · right
      have hh := h2
      rw [dite_eq_right hj] at hh
      simpa only [append_gp_idxT] using hh
  · have hh := h3
    have hh2 : v (fT k p) - v (fW0 k p) ^ 2 = 0 := by
      simpa only [append_gp_idxT, append_gp_idxW0] using hh
    linarith

theorem critFibreCond_bound {k r p : ℕ} (hp : p ≤ k) (κ : ℕ) (hκ : 1 ≤ κ) (P : MvPolynomial (Fin k ⊕ Fin (k + r)) ℝ) (Gs : List (MvPolynomial (Fin k ⊕ Fin (k + r)) ℝ)) (c : WilkiesDesign.E.EAChain k r) (z : Fin k → ℝ) (v : Fin (Work.WilE6.FQ k p) → ℝ) (j : Fin (k + 1)) (h : Work.WilE6.critFibreCond (p := p) hp κ P Gs j (Fin.append (Work.WilE6.graphPt c z) v)) (hbd : dist (Work.WilE6.projU k p v) 0 ≤ 1) : dist v 0 ≤ Real.sqrt (2 * dist (Work.WilE6.projU k p v) 0) := by
  have hc := h
  simp only [BP, critFibreCond] at hc
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hc
  set T : ℝ := dist (projU k p v) 0 with hT
  have hT0 : 0 ≤ T := dist_nonneg
  have hT1 : T ≤ 1 := hbd
  have hsT : T ≤ Real.sqrt (2 * T) := by
    rw [Real.le_sqrt hT0 (by linarith)]
    nlinarith
  have ht : v (fT k p) = T := by
    rw [hT]
    exact critFibreCond_bound_t hp κ P Gs c z v j h
  have hk2 : 1 ≤ κ ^ 2 := Nat.one_le_pow 2 κ (by omega)
  have hpowT : v (fT k p) ^ (κ ^ 2) ≤ T := by
    rw [ht]
    simpa using pow_le_pow_of_le_one hT0 hT1 hk2
  have hwm : ∀ i, |v (fWm k p i)| ≤ Real.sqrt (2 * T) := by
    intro i
    have h1i : v (fU k p i) ^ 2 - v (fT k p) ^ 2 + v (fWm k p i) ^ 2 = 0 := by
      simpa only [append_gp_idxU, append_gp_idxT, append_gp_idxWm] using h1 i
    have hsq : v (fWm k p i) ^ 2 ≤ T ^ 2 := by
      rw [ht] at h1i
      nlinarith [sq_nonneg (v (fU k p i))]
    calc |v (fWm k p i)| = Real.sqrt (v (fWm k p i) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt (T ^ 2) := Real.sqrt_le_sqrt hsq
      _ = T := Real.sqrt_sq hT0
      _ ≤ Real.sqrt (2 * T) := hsT
  have hw0 : |v (fW0 k p)| ≤ Real.sqrt (2 * T) := by
    have hh := h3
    have h3' : v (fT k p) - v (fW0 k p) ^ 2 = 0 := by
      simpa only [append_gp_idxT, append_gp_idxW0] using hh
    have hsq : v (fW0 k p) ^ 2 = T := by rw [ht] at h3'; linarith
    calc |v (fW0 k p)| = Real.sqrt (v (fW0 k p) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ = Real.sqrt T := by rw [hsq]
      _ ≤ Real.sqrt (2 * T) := Real.sqrt_le_sqrt (by linarith)
  have hwb : ∀ b, |v (fWb k p b)| ≤ Real.sqrt (2 * T) := by
    intro b
    have hb : v (fWb k p b) ^ 2
        + (if (b.1 % 2 == 0) then v (fU k p ⟨b.1 / 2, div2_lt hp b⟩)
          else -v (fU k p ⟨b.1 / 2, div2_lt hp b⟩)) - v (fT k p) ^ (κ ^ 2) = 0 := by
      simpa only [append_gp_idxWb, append_gp_idxU, append_gp_idxT] using h4 b
    have hneg : -(if (b.1 % 2 == 0) then v (fU k p ⟨b.1 / 2, div2_lt hp b⟩)
          else -v (fU k p ⟨b.1 / 2, div2_lt hp b⟩)) ≤ T := by
      have hub : |v (fU k p ⟨b.1 / 2, div2_lt hp b⟩)| ≤ T := by
        have h' := dist_le_pi_dist (projU k p v) (0 : Fin k → ℝ) ⟨b.1 / 2, div2_lt hp b⟩
        rw [hT]
        simpa only [projU, Real.dist_eq, Pi.zero_apply, sub_zero] using h'
      by_cases hbb : (b.1 % 2 == 0) = true
      · rw [ite_eq_left hbb]
        linarith [neg_le_abs (v (fU k p ⟨b.1 / 2, div2_lt hp b⟩))]
      · rw [ite_eq_right hbb]
        linarith [le_abs_self (v (fU k p ⟨b.1 / 2, div2_lt hp b⟩))]
    have hsq : v (fWb k p b) ^ 2 ≤ 2 * T := by nlinarith [hpowT, hneg]
    calc |v (fWb k p b)| = Real.sqrt (v (fWb k p b) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt (2 * T) := Real.sqrt_le_sqrt hsq
  have hwe : ∀ e, |v (fWe k p e)| ≤ Real.sqrt (2 * T) := by
    have h0 : v (fWe k p 0) ^ 2
        + (MvPolynomial.eval (fun i => Fin.append (graphPt c z) v (idxPhi k r p i)) P)
        - v (fT k p) ^ (κ ^ 2) = 0 := by
      have hh := h5 0
      rw [append_gp_idxWe c z v 0, append_gp_idxT c z v] at hh
      simpa using hh
    have h1' : v (fWe k p 1) ^ 2
        + (-(MvPolynomial.eval (fun i => Fin.append (graphPt c z) v (idxPhi k r p i)) P))
        - v (fT k p) ^ (κ ^ 2) = 0 := by
      have hh := h5 1
      rw [append_gp_idxWe c z v 1, append_gp_idxT c z v] at hh
      simpa using hh
    have hsum : v (fWe k p 0) ^ 2 + v (fWe k p 1) ^ 2 = 2 * v (fT k p) ^ (κ ^ 2) := by linarith
    intro e
    have hs : v (fWe k p e) ^ 2 ≤ 2 * T := by
      have he : e = 0 ∨ e = 1 := by omega
      rcases he with rfl | rfl
      · have hle : v (fWe k p 0) ^ 2 ≤ v (fWe k p 0) ^ 2 + v (fWe k p 1) ^ 2 := by
          nlinarith [sq_nonneg (v (fWe k p 1))]
        rw [hsum] at hle
        nlinarith [hpowT]
      · have hle : v (fWe k p 1) ^ 2 ≤ v (fWe k p 0) ^ 2 + v (fWe k p 1) ^ 2 := by
          nlinarith [sq_nonneg (v (fWe k p 0))]
        rw [hsum] at hle
        nlinarith [hpowT]
    calc |v (fWe k p e)| = Real.sqrt (v (fWe k p e) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt (2 * T) := Real.sqrt_le_sqrt hs
  have hs2 : 0 ≤ Real.sqrt (2 * T) := Real.sqrt_nonneg _
  rw [dist_pi_le_iff hs2]
  intro x
  simp only [Pi.zero_apply, Real.dist_eq, sub_zero]
  rcases FQ_cover (k := k) (p := p) x with ⟨i, rfl⟩ | rfl | ⟨i, rfl⟩ | rfl | ⟨b, rfl⟩ | ⟨e, rfl⟩
  · have hle : |v (fU k p i)| ≤ T := by
      have h' := dist_le_pi_dist (projU k p v) (0 : Fin k → ℝ) i
      rw [hT]
      simpa only [projU, Real.dist_eq, Pi.zero_apply, sub_zero] using h'
    exact hle.trans hsT
  · rw [ht, abs_of_nonneg hT0]; exact hsT
  · exact hwm i
  · exact hw0
  · exact hwb b
  · exact hwe e

end Work.WilE6
