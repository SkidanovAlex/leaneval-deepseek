/-
  WilE10 / RexpSub — the *strict* inequalities of the branch construction.

  For a point `mkPt n m x ε z` of the branch construction (see `RexpSubDefs`), every element of
  `posOf n m ε` evaluates strictly positively. There are three shapes of atom, and each is positive
  exactly on the branch it belongs to:

  * `posS n m i` (`1 - sᵢ² > 0`) and `sNZ n m i` (`sᵢ² > 0`) on the *large* branch `ε i = false`,
    where the `s`-coordinate is `zᵢ⁻¹`. There `|zᵢ| > 1`, hence `|zᵢ⁻¹| < 1` (so `1 - sᵢ² > 0`) and
    `zᵢ ≠ 0` (so `sᵢ² > 0`);
  * `posSign n m i` (`uᵢ sᵢ > 0`) in the large branch of the `i`-th projected coordinate, where
    `uᵢ = psi (xᵢ)` and `sᵢ = zᵢ⁻¹ = xᵢ⁻¹`. Since `psi` has the sign of its argument, the product
    equals `1/√(1+xᵢ²) > 0`.

  This is the companion of `eqs_of_eqsOf_eq_zero` (the vanishing atoms): together they say that
  `mkPt n m x ε z` satisfies the basic set `basicOf n m P ε` of its branch, which is the content of
  `mkPt_mem_W`.
-/
import Mathlib
import Submission.Work.WilE10.RexpSubDefs

namespace Work.WilE10.RexpSub

open Work.WilE10 WilkiesDesign WilkiesDesign.E

/-! ## Reading off the members of `posOf` -/

/-- The members of `posOf n m ε`: the large branch of a coordinate `i` contributes the two
inequalities `posS`, `sNZ`, and the large branch of a projected coordinate `i` contributes
`posSign`. -/
theorem posOf_mem (n m : ℕ) (ε : Fin (n + m) → Bool) (f : EAPoly (Kdim n m) (n + m))
    (hf : f ∈ posOf n m ε) :
    (∃ i : Fin (n + m), ε i = false ∧ (f = posS n m i ∨ f = sNZ n m i)) ∨
      (∃ i : Fin n, ε (Fin.castAdd m i) = false ∧ f = posSign n m i) := by
  rw [posOf] at hf
  rcases List.mem_append.mp hf with h | h
  · rcases List.mem_flatMap.mp h with ⟨i, -, hi⟩
    split_ifs at hi with he
    · exact absurd hi (List.not_mem_nil)
    · exact Or.inl ⟨i, by simpa using he, by simpa using hi⟩
  · rcases List.mem_flatMap.mp h with ⟨i, -, hi⟩
    split_ifs at hi with he
    · exact absurd hi (List.not_mem_nil)
    · exact Or.inr ⟨i, by simpa using he, by simpa using hi⟩

/-! ## Evaluating the atoms -/

/-- The atoms of `posOf` are built from the `Sum.inl` variables only, so their evaluation only
involves the coordinates of the point itself (no exponentials). -/
theorem posOf_eval_posS (n m : ℕ) (p : Fin (Kdim n m) → ℝ) (i : Fin (n + m)) :
    eaEval (chain n m) (posS n m i) p = 1 - p (us n m i) ^ 2 := by
  simp [posS, Xa, eaEval]

theorem posOf_eval_sNZ (n m : ℕ) (p : Fin (Kdim n m) → ℝ) (i : Fin (n + m)) :
    eaEval (chain n m) (sNZ n m i) p = p (us n m i) ^ 2 := by
  simp [sNZ, Xa, eaEval]

theorem posOf_eval_posSign (n m : ℕ) (p : Fin (Kdim n m) → ℝ) (i : Fin n) :
    eaEval (chain n m) (posSign n m i) p = p (uu n m i) * p (us n m (Fin.castAdd m i)) := by
  simp [posSign, Xa, eaEval]

/-! ## The elementary inequalities -/

/-- On the large branch `|z| > 1` the reciprocal satisfies `1 - z⁻¹² > 0`. -/
theorem one_sub_sq_inv_pos {z : ℝ} (hz : 1 < |z|) : 0 < 1 - z⁻¹ ^ 2 := by
  have h2 : z⁻¹ ^ 2 = 1 / |z| ^ 2 := by
    rw [inv_pow, inv_eq_one_div, sq_abs]
  have h3 : z⁻¹ ^ 2 < 1 := by
    rw [h2, div_lt_one (by positivity)]
    nlinarith [hz, abs_nonneg z]
  linarith

/-- On the large branch `|z| > 1` the reciprocal is nonzero, so its square is positive. -/
theorem sq_inv_pos {z : ℝ} (hz : 1 < |z|) : 0 < z⁻¹ ^ 2 :=
  sq_pos_of_ne_zero (inv_ne_zero (by intro h0; rw [h0] at hz; norm_num at hz))

/-- `psi` has the sign of its argument: `psi x * x⁻¹ = 1/√(1+x²) > 0`. -/
theorem psi_mul_inv_pos {x : ℝ} (hx : x ≠ 0) : 0 < psi x * x⁻¹ := by
  have h : psi x * x⁻¹ = 1 / Real.sqrt (1 + x ^ 2) := by
    rw [psi]; field_simp
  rw [h]
  exact div_pos one_pos (Real.sqrt_pos.mpr (by positivity))

/-! ## The statement -/

theorem pos_of_posOf_pos (n m : ℕ) (x : Fin n → ℝ) (ε : Fin (n + m) → Bool)
    (z : Fin (n + m) → ℝ) (hzx : ∀ i : Fin n, z (Fin.castAdd m i) = x i)
    (hε : ∀ i : Fin (n + m), ε i = true ↔ |z i| ≤ 1) :
    ∀ f ∈ Work.WilE10.posOf n m ε,
      0 < WilkiesDesign.E.eaEval (Work.WilE10.chain n m) f (Work.WilE10.mkPt n m x ε z) := by
  intro f hf
  rcases posOf_mem n m ε f hf with ⟨i, hi, hfi⟩ | ⟨i, hi, hfi⟩
  · -- `ε i = false`: the coordinate `i` is in the large branch, so `|z i| > 1`.
    have hnot : ¬ (|z i| ≤ 1) := by
      intro hle
      have h1 : ε i = true := (hε i).mpr hle
      rw [hi] at h1
      exact Bool.false_ne_true h1
    have hbig : 1 < |z i| := lt_of_not_ge hnot
    rcases hfi with rfl | rfl
    · rw [posOf_eval_posS, mkPt_us, hi]
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact one_sub_sq_inv_pos hbig
    · rw [posOf_eval_sNZ, mkPt_us, hi]
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact sq_inv_pos hbig
  · -- `ε (castAdd m i) = false`: both `psi (x i)` and `x i⁻¹` are nonzero with the same sign.
    have hnot : ¬ (|z (Fin.castAdd m i)| ≤ 1) := by
      intro hle
      have h1 : ε (Fin.castAdd m i) = true := (hε _).mpr hle
      rw [hi] at h1
      exact Bool.false_ne_true h1
    have hbig : 1 < |x i| := by
      have h2 : 1 < |z (Fin.castAdd m i)| := lt_of_not_ge hnot
      rwa [hzx i] at h2
    have hx0 : x i ≠ 0 := by
      intro h0; rw [h0] at hbig; norm_num at hbig
    rw [hfi, posOf_eval_posSign, mkPt_uu, mkPt_us, hi, hzx i]
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact psi_mul_inv_pos hx0

end Work.WilE10.RexpSub
