import Mathlib
import Submission.Work.WilE6.Closure

set_option autoImplicit false
noncomputable section
open Classical Topology

namespace Work.WilE6
open WilkiesConjecture WilkiesDesign WilkiesDesign.E

variable {k r p : ℕ}

/-! ## §1. Numeric and metric helpers -/

/-- `(√(T - v))² + v - T = 0` whenever `|v| ≤ T`: the square-root identity behind all the
polynomial witnesses of the Taylor criterion. -/
theorem sq_sqrt_sub {v T : ℝ} (h : |v| ≤ T) : (Real.sqrt (T - v)) ^ 2 + v - T = 0 := by
  have h1 : 0 ≤ T - v := by linarith [le_abs_self v, h]
  rw [Real.sq_sqrt h1]
  ring

/-- The coordinates of a point of `Fin k → ℝ` are bounded by its distance from the origin
(in the sup metric). -/
theorem abs_le_dist_zero (u : Fin k → ℝ) (i : Fin k) : |u i| ≤ dist u 0 := by
  have h := dist_le_pi_dist u 0 i
  rw [show dist (u i) ((0 : Fin k → ℝ) i) = |u i| from by simp] at h
  exact h

/-! ## §2. The canonical witness point -/

theorem canonBase_bound (n : ℕ) (hn : n < BP k r) (hnk : ¬ n < k) : n - k < r := by
  have hBP : BP k r = k + r := rfl
  omega

theorem canonPt_bound (n : ℕ) (hn : n < BP k r + FQ k p) (hnk : ¬ n < BP k r) :
    n - BP k r < FQ k p := by
  have hBP : BP k r = k + r := rfl
  have hFQ : FQ k p = 2 * k + 2 * p + 4 := rfl
  omega

theorem canonFib_bound_wm (n : ℕ) (h1 : ¬ n < k + 1) (h2 : n < k + 1 + k) :
    n - (k + 1) < k := by omega

theorem canonFib_bound_wb (n : ℕ) (h1 : ¬ n < k + 1 + k + 1) (h2 : n < k + 1 + k + 1 + 2 * p) :
    n - (k + 1 + k + 1) < 2 * p := by omega

theorem canonFib_bound_we (n : ℕ) (h1 : ¬ n < k + 1 + k + 1 + 2 * p) (h2 : n < FQ k p) :
    n - (k + 1 + k + 1 + 2 * p) < 2 := by
  have hFQ : FQ k p = 2 * k + 2 * p + 4 := rfl
  omega

/-- The base coordinates `(z, h)` of the canonical point, as a function of the first
`BP k r = k + r` coordinates of the ambient space of `critSA`. -/
def canonBase (k r : ℕ) (z : Fin k → ℝ) (h : Fin r → ℝ) : Fin (BP k r) → ℝ :=
  fun i => if hi : (i : ℕ) < k then z ⟨(i : ℕ), hi⟩
    else h ⟨(i : ℕ) - k, canonBase_bound (k := k) (r := r) (i : ℕ) i.2 hi⟩

/-- The fibre coordinates of the canonical witness point, as a function of the last
`FQ k p` coordinates of the ambient space: `u`, `t = dist u 0`, and the witnesses
`wm`, `w0`, `wb`, `we`. -/
def canonFib (hp : p ≤ k) (κ : ℕ) (P : MvPolynomial (Fin k ⊕ Fin (k + r)) ℝ)
    (z : Fin k → ℝ) (h : Fin r → ℝ) (u : Fin k → ℝ) : Fin (FQ k p) → ℝ :=
  fun i =>
    if h₁ : (i : ℕ) < k then u ⟨(i : ℕ), h₁⟩
    else if h₂ : (i : ℕ) < k + 1 then canonT k u
    else if h₃ : (i : ℕ) < k + 1 + k then
      canonWm k u ⟨(i : ℕ) - (k + 1), canonFib_bound_wm (k := k) (i : ℕ) h₂ h₃⟩
    else if h₄ : (i : ℕ) < k + 1 + k + 1 then canonW0 k u
    else if h₅ : (i : ℕ) < k + 1 + k + 1 + 2 * p then
      canonWb k p hp κ u ⟨(i : ℕ) - (k + 1 + k + 1),
        canonFib_bound_wb (k := k) (p := p) (i : ℕ) h₄ h₅⟩
    else canonWe k r κ P z h u ⟨(i : ℕ) - (k + 1 + k + 1 + 2 * p),
      canonFib_bound_we (k := k) (p := p) (i : ℕ) h₅ i.2⟩

/-- The canonical witness point of the criterion set: base `(z,h)` and fibre the canonical
witnesses `(u, t = dist u 0, wm, w0, wb, we)`. -/
def canonPt (hp : p ≤ k) (κ : ℕ) (P : MvPolynomial (Fin k ⊕ Fin (k + r)) ℝ)
    (z : Fin k → ℝ) (h : Fin r → ℝ) (u : Fin k → ℝ) : Fin (BP k r + FQ k p) → ℝ :=
  Fin.addCases (canonBase k r z h) (canonFib hp κ P z h u)

/-! ## §3. The values of the canonical point -/

theorem canonBase_lt (z : Fin k → ℝ) (h : Fin r → ℝ) (n : ℕ) (hn : n < BP k r)
    (hnk : n < k) : canonBase k r z h (⟨n, hn⟩ : Fin (BP k r)) = z ⟨n, hnk⟩ := by
  simp only [canonBase, dite_eq_left hnk]

theorem canonBase_ge (z : Fin k → ℝ) (h : Fin r → ℝ) (n : ℕ) (hn : n < BP k r)
    (hnk : ¬ n < k) :
    canonBase k r z h (⟨n, hn⟩ : Fin (BP k r)) =
      h ⟨n - k, canonBase_bound (k := k) (r := r) n hn hnk⟩ := by
  simp only [canonBase, dite_eq_right hnk]

theorem canonPt_castAdd (hp : p ≤ k) (κ : ℕ) (P : MvPolynomial (Fin k ⊕ Fin (k + r)) ℝ)
    (z : Fin k → ℝ) (h : Fin r → ℝ) (u : Fin k → ℝ) (y : Fin (BP k r)) :
    canonPt hp κ P z h u (Fin.castAdd (FQ k p) y) = canonBase k r z h y := by
  simp only [canonPt, Fin.addCases_left]

theorem canonPt_natAdd (hp : p ≤ k) (κ : ℕ) (P : MvPolynomial (Fin k ⊕ Fin (k + r)) ℝ)
    (z : Fin k → ℝ) (h : Fin r → ℝ) (u : Fin k → ℝ) (x : Fin (FQ k p)) :
    canonPt hp κ P z h u (Fin.natAdd (BP k r) x) = canonFib hp κ P z h u x := by
  simp only [canonPt, Fin.addCases_right]

theorem canonFib_of_lt (hp : p ≤ k) (κ : ℕ) (P : MvPolynomial (Fin k ⊕ Fin (k + r)) ℝ)
    (z : Fin k → ℝ) (h : Fin r → ℝ) (u : Fin k → ℝ) (n : ℕ) (hn : n < FQ k p)
    (hx : n < k) : canonFib hp κ P z h u (⟨n, hn⟩ : Fin (FQ k p)) = u ⟨n, hx⟩ := by
  simp only [canonFib, dite_eq_left hx]

theorem canonFib_of_t (hp : p ≤ k) (κ : ℕ) (P : MvPolynomial (Fin k ⊕ Fin (k + r)) ℝ)
    (z : Fin k → ℝ) (h : Fin r → ℝ) (u : Fin k → ℝ) (n : ℕ) (hn : n < FQ k p)
    (h1 : ¬ n < k) (h2 : n < k + 1) :
    canonFib hp κ P z h u (⟨n, hn⟩ : Fin (FQ k p)) = canonT k u := by
  simp only [canonFib, dite_eq_right h1, dite_eq_left h2]

theorem canonFib_of_wm (hp : p ≤ k) (κ : ℕ) (P : MvPolynomial (Fin k ⊕ Fin (k + r)) ℝ)
    (z : Fin k → ℝ) (h : Fin r → ℝ) (u : Fin k → ℝ) (n : ℕ) (hn : n < FQ k p)
    (h1 : ¬ n < k) (h2 : ¬ n < k + 1) (h3 : n < k + 1 + k) :
    canonFib hp κ P z h u (⟨n, hn⟩ : Fin (FQ k p)) =
      canonWm k u ⟨n - (k + 1), canonFib_bound_wm (k := k) n h2 h3⟩ := by
  simp only [canonFib, dite_eq_right h1, dite_eq_right h2, dite_eq_left h3]

theorem canonFib_of_w0 (hp : p ≤ k) (κ : ℕ) (P : MvPolynomial (Fin k ⊕ Fin (k + r)) ℝ)
    (z : Fin k → ℝ) (h : Fin r → ℝ) (u : Fin k → ℝ) (n : ℕ) (hn : n < FQ k p)
    (h1 : ¬ n < k) (h2 : ¬ n < k + 1) (h3 : ¬ n < k + 1 + k) (h4 : n < k + 1 + k + 1) :
    canonFib hp κ P z h u (⟨n, hn⟩ : Fin (FQ k p)) = canonW0 k u := by
  simp only [canonFib, dite_eq_right h1, dite_eq_right h2, dite_eq_right h3, dite_eq_left h4]

theorem canonFib_of_wb (hp : p ≤ k) (κ : ℕ) (P : MvPolynomial (Fin k ⊕ Fin (k + r)) ℝ)
    (z : Fin k → ℝ) (h : Fin r → ℝ) (u : Fin k → ℝ) (n : ℕ) (hn : n < FQ k p)
    (h1 : ¬ n < k) (h2 : ¬ n < k + 1) (h3 : ¬ n < k + 1 + k) (h4 : ¬ n < k + 1 + k + 1)
    (h5 : n < k + 1 + k + 1 + 2 * p) :
    canonFib hp κ P z h u (⟨n, hn⟩ : Fin (FQ k p)) =
      canonWb k p hp κ u ⟨n - (k + 1 + k + 1), canonFib_bound_wb (k := k) (p := p) n h4 h5⟩ := by
  simp only [canonFib, dite_eq_right h1, dite_eq_right h2, dite_eq_right h3, dite_eq_right h4,
    dite_eq_left h5]

theorem canonFib_of_we (hp : p ≤ k) (κ : ℕ) (P : MvPolynomial (Fin k ⊕ Fin (k + r)) ℝ)
    (z : Fin k → ℝ) (h : Fin r → ℝ) (u : Fin k → ℝ) (n : ℕ) (hn : n < FQ k p)
    (h1 : ¬ n < k) (h2 : ¬ n < k + 1) (h3 : ¬ n < k + 1 + k) (h4 : ¬ n < k + 1 + k + 1)
    (h5 : ¬ n < k + 1 + k + 1 + 2 * p) :
    canonFib hp κ P z h u (⟨n, hn⟩ : Fin (FQ k p)) =
      canonWe k r κ P z h u ⟨n - (k + 1 + k + 1 + 2 * p),
        canonFib_bound_we (k := k) (p := p) n h5 hn⟩ := by
  simp only [canonFib, dite_eq_right h1, dite_eq_right h2, dite_eq_right h3, dite_eq_right h4,
    dite_eq_right h5]

theorem canonPt_idxZ {hp : p ≤ k} {κ : ℕ} {P : MvPolynomial (Fin k ⊕ Fin (k + r)) ℝ}
    {z : Fin k → ℝ} {h : Fin r → ℝ} {u : Fin k → ℝ} (i : Fin k) :
    canonPt hp κ P z h u (idxZ k r p i) = z i := by
  have hBP : BP k r = k + r := rfl
  have hb : (i : ℕ) < BP k r := by omega
  have hidx : idxZ k r p i = Fin.castAdd (FQ k p) (⟨(i : ℕ), hb⟩ : Fin (BP k r)) := by
    apply Fin.ext
    simp only [idxZ, Fin.val_castAdd]
  rw [hidx, canonPt_castAdd]
  exact canonBase_lt z h (i : ℕ) hb i.2

theorem canonPt_idxH {hp : p ≤ k} {κ : ℕ} {P : MvPolynomial (Fin k ⊕ Fin (k + r)) ℝ}
    {z : Fin k → ℝ} {h : Fin r → ℝ} {u : Fin k → ℝ} (j : Fin r) :
    canonPt hp κ P z h u (idxH k r p j) = h j := by
  have hBP : BP k r = k + r := rfl
  have hb : k + (j : ℕ) < BP k r := by omega
  have hnk : ¬ k + (j : ℕ) < k := by omega
  have hidx : idxH k r p j = Fin.castAdd (FQ k p) (⟨k + (j : ℕ), hb⟩ : Fin (BP k r)) := by
    apply Fin.ext
    simp only [idxH, Fin.val_castAdd]
  rw [hidx, canonPt_castAdd]
  rw [canonBase_ge z h (k + (j : ℕ)) hb hnk]
  apply congrArg h
  apply Fin.ext
  change k + (j : ℕ) - k = (j : ℕ)
  omega

theorem canonPt_idxU {hp : p ≤ k} {κ : ℕ} {P : MvPolynomial (Fin k ⊕ Fin (k + r)) ℝ}
    {z : Fin k → ℝ} {h : Fin r → ℝ} {u : Fin k → ℝ} (i : Fin k) :
    canonPt hp κ P z h u (idxU k r p i) = u i := by
  have hFQ : FQ k p = 2 * k + 2 * p + 4 := rfl
  have hi : (i : ℕ) < FQ k p := by omega
  have hidx : idxU k r p i = Fin.natAdd (BP k r) (⟨(i : ℕ), hi⟩ : Fin (FQ k p)) := by
    apply Fin.ext
    simp only [idxU, Fin.natAdd]
  rw [hidx, canonPt_natAdd]
  exact canonFib_of_lt hp κ P z h u (i : ℕ) hi i.2

theorem canonPt_idxT {hp : p ≤ k} {κ : ℕ} {P : MvPolynomial (Fin k ⊕ Fin (k + r)) ℝ}
    {z : Fin k → ℝ} {h : Fin r → ℝ} {u : Fin k → ℝ} :
    canonPt hp κ P z h u (idxT k r p) = canonT k u := by
  have hFQ : FQ k p = 2 * k + 2 * p + 4 := rfl
  have hi : k < FQ k p := by omega
  have hidx : idxT k r p = Fin.natAdd (BP k r) (⟨k, hi⟩ : Fin (FQ k p)) := by
    apply Fin.ext
    simp only [idxT, Fin.natAdd]
  rw [hidx, canonPt_natAdd]
  exact canonFib_of_t hp κ P z h u k hi (by omega) (by omega)

theorem canonPt_idxWm {hp : p ≤ k} {κ : ℕ} {P : MvPolynomial (Fin k ⊕ Fin (k + r)) ℝ}
    {z : Fin k → ℝ} {h : Fin r → ℝ} {u : Fin k → ℝ} (i : Fin k) :
    canonPt hp κ P z h u (idxWm k r p i) = canonWm k u i := by
  have hFQ : FQ k p = 2 * k + 2 * p + 4 := rfl
  have hi : k + 1 + (i : ℕ) < FQ k p := by omega
  have hidx : idxWm k r p i = Fin.natAdd (BP k r) (⟨k + 1 + (i : ℕ), hi⟩ : Fin (FQ k p)) := by
    apply Fin.ext
    simp only [idxWm, Fin.natAdd]
    omega
  rw [hidx, canonPt_natAdd]
  rw [canonFib_of_wm hp κ P z h u (k + 1 + (i : ℕ)) hi (by omega) (by omega) (by omega)]
  apply congrArg (canonWm k u)
  apply Fin.ext
  change k + 1 + (i : ℕ) - (k + 1) = (i : ℕ)
  omega

theorem canonPt_idxW0 {hp : p ≤ k} {κ : ℕ} {P : MvPolynomial (Fin k ⊕ Fin (k + r)) ℝ}
    {z : Fin k → ℝ} {h : Fin r → ℝ} {u : Fin k → ℝ} :
    canonPt hp κ P z h u (idxW0 k r p) = canonW0 k u := by
  have hFQ : FQ k p = 2 * k + 2 * p + 4 := rfl
  have hi : k + 1 + k < FQ k p := by omega
  have hidx : idxW0 k r p = Fin.natAdd (BP k r) (⟨k + 1 + k, hi⟩ : Fin (FQ k p)) := by
    apply Fin.ext
    simp only [idxW0, Fin.natAdd]
    omega
  rw [hidx, canonPt_natAdd]
  exact canonFib_of_w0 hp κ P z h u (k + 1 + k) hi (by omega) (by omega) (by omega) (by omega)

theorem canonPt_idxWb {hp : p ≤ k} {κ : ℕ} {P : MvPolynomial (Fin k ⊕ Fin (k + r)) ℝ}
    {z : Fin k → ℝ} {h : Fin r → ℝ} {u : Fin k → ℝ} (b : Fin (2 * p)) :
    canonPt hp κ P z h u (idxWb k r p b) = canonWb k p hp κ u b := by
  have hFQ : FQ k p = 2 * k + 2 * p + 4 := rfl
  have hi : k + 1 + k + 1 + (b : ℕ) < FQ k p := by omega
  have hidx : idxWb k r p b =
      Fin.natAdd (BP k r) (⟨k + 1 + k + 1 + (b : ℕ), hi⟩ : Fin (FQ k p)) := by
    apply Fin.ext
    simp only [idxWb, Fin.natAdd]
    omega
  rw [hidx, canonPt_natAdd]
  rw [canonFib_of_wb hp κ P z h u (k + 1 + k + 1 + (b : ℕ)) hi (by omega) (by omega)
    (by omega) (by omega) (by omega)]
  apply congrArg (canonWb k p hp κ u)
  apply Fin.ext
  change k + 1 + k + 1 + (b : ℕ) - (k + 1 + k + 1) = (b : ℕ)
  omega

theorem canonPt_idxWe {hp : p ≤ k} {κ : ℕ} {P : MvPolynomial (Fin k ⊕ Fin (k + r)) ℝ}
    {z : Fin k → ℝ} {h : Fin r → ℝ} {u : Fin k → ℝ} (e : Fin 2) :
    canonPt hp κ P z h u (idxWe k r p e) = canonWe k r κ P z h u e := by
  have hFQ : FQ k p = 2 * k + 2 * p + 4 := rfl
  have hi : k + 1 + k + 1 + 2 * p + (e : ℕ) < FQ k p := by omega
  have hidx : idxWe k r p e =
      Fin.natAdd (BP k r) (⟨k + 1 + k + 1 + 2 * p + (e : ℕ), hi⟩ : Fin (FQ k p)) := by
    apply Fin.ext
    simp only [idxWe, Fin.natAdd]
    omega
  rw [hidx, canonPt_natAdd]
  rw [canonFib_of_we hp κ P z h u (k + 1 + k + 1 + 2 * p + (e : ℕ)) hi (by omega)
    (by omega) (by omega) (by omega) (by omega)]
  apply congrArg (canonWe k r κ P z h u)
  apply Fin.ext
  change k + 1 + k + 1 + 2 * p + (e : ℕ) - (k + 1 + k + 1 + 2 * p) = (e : ℕ)
  omega

theorem canonPt_comp_idxPhi (hp : p ≤ k) (κ : ℕ) (P : MvPolynomial (Fin k ⊕ Fin (k + r)) ℝ)
    (z : Fin k → ℝ) (h : Fin r → ℝ) (u : Fin k → ℝ) :
    (fun x : Fin k ⊕ Fin (k + r) => canonPt hp κ P z h u (idxPhi k r p x)) =
      Sum.elim u (Fin.append z h) := by
  funext x
  rcases x with i | y
  · exact canonPt_idxU i
  · simp only [Sum.elim_inr]
    refine Fin.addCases (motive := fun y : Fin (k + r) =>
      canonPt hp κ P z h u (idxPhi k r p (Sum.inr y)) = Fin.append z h y) (fun i => ?_)
      (fun j => ?_) y
    · simp only [idxPhi_inr_castAdd, canonPt_idxZ, Fin.append_left]
    · simp only [idxPhi_inr_natAdd, canonPt_idxH, Fin.append_right]

theorem canonPt_eval_idxPhi {hp : p ≤ k} {κ : ℕ}
    {P : MvPolynomial (Fin k ⊕ Fin (k + r)) ℝ} {z : Fin k → ℝ} {h : Fin r → ℝ}
    {u : Fin k → ℝ} (Q : MvPolynomial (Fin k ⊕ Fin (k + r)) ℝ) :
    MvPolynomial.eval (fun i => canonPt hp κ P z h u (idxPhi k r p i)) Q =
      MvPolynomial.eval (Sum.elim u (Fin.append z h)) Q := by
  rw [canonPt_comp_idxPhi]

/-! ## §4. The fibre conditions at the canonical point -/

/-- The canonical point satisfies the fibre conditions of the criterion, for an attained
index `j` (or the degenerate index when `dist u 0 = 0`). -/
theorem critFibreCond_canonPt (hp : p ≤ k) (κ : ℕ)
    (P : MvPolynomial (Fin k ⊕ Fin (k + r)) ℝ)
    (Gs : List (MvPolynomial (Fin k ⊕ Fin (k + r)) ℝ)) (z : Fin k → ℝ) (h : Fin r → ℝ)
    (u : Fin k → ℝ)
    (hP : |MvPolynomial.eval (Sum.elim u (Fin.append z h)) P| ≤ dist u 0 ^ (κ ^ 2))
    (hbase : ∀ i : Fin p, |u ⟨i.1, lt_of_lt_of_le i.2 hp⟩| ≤ dist u 0 ^ (κ ^ 2))
    (hGs : ∀ G ∈ Gs, dist u 0 ^ κ < MvPolynomial.eval (Sum.elim u (Fin.append z h)) G)
    (j : Fin (k + 1))
    (hj : (if hj' : (j : ℕ) < k then u ⟨(j : ℕ), hj'⟩ ^ 2 - dist u 0 ^ 2 = 0
      else dist u 0 = 0)) :
    critFibreCond (k := k) (r := r) (p := p) hp κ P Gs j (canonPt hp κ P z h u) := by
  simp only [critFibreCond, canonPt_idxU, canonPt_idxT, canonPt_idxWm, canonPt_idxW0,
    canonPt_idxWb, canonPt_idxWe, canonPt_eval_idxPhi, canonT, canonWm, canonW0, canonWb,
    canonWe]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    have habs : |u i| ≤ dist u 0 := abs_le_dist_zero u i
    have hsq : u i ^ 2 ≤ dist u 0 ^ 2 := by
      have h1 : |u i| ^ 2 ≤ (dist u 0) ^ 2 := by
        have h2 := mul_self_le_mul_self (abs_nonneg (u i)) habs
        simpa [sq] using h2
      calc u i ^ 2 = |u i| ^ 2 := by rw [sq_abs]
        _ ≤ (dist u 0) ^ 2 := h1
    have hkey : (Real.sqrt (dist u 0 ^ 2 - u i ^ 2)) ^ 2 + u i ^ 2 - dist u 0 ^ 2 = 0 :=
      sq_sqrt_sub (by rw [abs_of_nonneg (sq_nonneg (u i))]; exact hsq)
    linarith
  · exact hj
  · rw [Real.sq_sqrt dist_nonneg]
    ring
  · intro b
    have hbp : b.1 / 2 < p := by
      rw [Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2)]
      have hb2 := b.2
      omega
    have hb : |u ⟨b.1 / 2, div2_lt hp b⟩| ≤ dist u 0 ^ (κ ^ 2) :=
      hbase ⟨b.1 / 2, hbp⟩
    by_cases hpar : ((b : ℕ) % 2 == 0) = true
    · rw [ite_eq_left hpar]
      have hkey : (Real.sqrt (dist u 0 ^ (κ ^ 2) - u ⟨b.1 / 2, div2_lt hp b⟩)) ^ 2
          + u ⟨b.1 / 2, div2_lt hp b⟩ - dist u 0 ^ (κ ^ 2) = 0 := sq_sqrt_sub hb
      linarith
    · rw [ite_eq_right hpar]
      have hneg : |-(u ⟨b.1 / 2, div2_lt hp b⟩)| ≤ dist u 0 ^ (κ ^ 2) := by
        rwa [abs_neg]
      have hkey : (Real.sqrt (dist u 0 ^ (κ ^ 2) - -(u ⟨b.1 / 2, div2_lt hp b⟩))) ^ 2
          + -(u ⟨b.1 / 2, div2_lt hp b⟩) - dist u 0 ^ (κ ^ 2) = 0 := sq_sqrt_sub hneg
      linarith
  · intro e
    by_cases he : e = 0
    · rw [ite_eq_left he]
      have hkey : (Real.sqrt (dist u 0 ^ (κ ^ 2)
          - MvPolynomial.eval (Sum.elim u (Fin.append z h)) P)) ^ 2
          + MvPolynomial.eval (Sum.elim u (Fin.append z h)) P - dist u 0 ^ (κ ^ 2) = 0 :=
        sq_sqrt_sub hP
      linarith
    · rw [ite_eq_right he]
      have hneg : |-(MvPolynomial.eval (Sum.elim u (Fin.append z h)) P)| ≤
          dist u 0 ^ (κ ^ 2) := by rwa [abs_neg]
      have hkey : (Real.sqrt (dist u 0 ^ (κ ^ 2)
          - -(MvPolynomial.eval (Sum.elim u (Fin.append z h)) P))) ^ 2
          + -(MvPolynomial.eval (Sum.elim u (Fin.append z h)) P) - dist u 0 ^ (κ ^ 2) = 0 :=
        sq_sqrt_sub hneg
      linarith
  · intro G hG
    exact hGs G hG

/-! ## §5. The main theorem -/

theorem critCond_imp_exists_witness {k r p : ℕ} (hp : p ≤ k) (κ : ℕ) (hκ : 1 ≤ κ) (P : MvPolynomial (Fin k ⊕ Fin (k + r)) ℝ) (Gs : List (MvPolynomial (Fin k ⊕ Fin (k + r)) ℝ)) (z : Fin k → ℝ) (h : Fin r → ℝ) (u : Fin k → ℝ) (hcond : Work.WilE6.critCond (k := k) (r := r) (p := p) hp κ P Gs z h u) : ∃ j : Fin (k + 1), ∃ pnt : Fin (Work.WilE6.BP k r + Work.WilE6.FQ k p) → ℝ, (∀ i : Fin k, pnt (Work.WilE6.idxZ k r p i) = z i) ∧ (∀ j' : Fin r, pnt (Work.WilE6.idxH k r p j') = h j') ∧ (∀ i : Fin k, pnt (Work.WilE6.idxU k r p i) = u i) ∧ Work.WilE6.critFibreCond (k := k) (r := r) (p := p) hp κ P Gs j pnt ∧ pnt (Work.WilE6.idxT k r p) = Work.WilE6.canonT k u ∧ (∀ i : Fin k, pnt (Work.WilE6.idxWm k r p i) = Work.WilE6.canonWm k u i) ∧ pnt (Work.WilE6.idxW0 k r p) = Work.WilE6.canonW0 k u ∧ (∀ b : Fin (2 * p), pnt (Work.WilE6.idxWb k r p b) = Work.WilE6.canonWb k p hp κ u b) ∧ (∀ e : Fin 2, pnt (Work.WilE6.idxWe k r p e) = Work.WilE6.canonWe k r κ P z h u e) := by
  obtain ⟨hP, hbase, hGs⟩ := hcond
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0
    have hd0 : dist u 0 = 0 := by
      have hle : dist u 0 ≤ 0 := by
        rw [dist_pi_le_iff le_rfl]
        intro b
        exact b.elim0
      exact le_antisymm hle dist_nonneg
    refine ⟨⟨0, by omega⟩, canonPt hp κ P z h u, canonPt_idxZ, canonPt_idxH, canonPt_idxU, ?_,
      canonPt_idxT, canonPt_idxWm, canonPt_idxW0, canonPt_idxWb, canonPt_idxWe⟩
    have hnot : ¬ (((⟨0, by omega⟩ : Fin (0 + 1)) : ℕ) < 0) := by omega
    refine critFibreCond_canonPt hp κ P Gs z h u hP hbase hGs ⟨0, by omega⟩ ?_
    rw [dite_eq_right hnot]
    exact hd0
  · obtain ⟨_, _, _, ⟨j0, hj0⟩, _⟩ := (norm_witness_iff k hkpos u (dist u 0)).mpr rfl
    have hj0' : u j0 ^ 2 = dist u 0 ^ 2 := hj0
    refine ⟨⟨(j0 : ℕ), by omega⟩, canonPt hp κ P z h u, canonPt_idxZ, canonPt_idxH,
      canonPt_idxU, ?_, canonPt_idxT, canonPt_idxWm, canonPt_idxW0, canonPt_idxWb,
      canonPt_idxWe⟩
    refine critFibreCond_canonPt hp κ P Gs z h u hP hbase hGs ⟨(j0 : ℕ), by omega⟩ ?_
    rw [dite_eq_left (by omega : (j0 : ℕ) < k)]
    show u j0 ^ 2 - dist u 0 ^ 2 = 0
    rw [hj0']
    ring

end Work.WilE6
