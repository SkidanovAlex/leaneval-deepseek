/-
  WilE10 / RexpSub — `mkPt_mem_cube`.

  The point `mkPt n m x ε z` built in `RexpSubDefs` lies in the closed cube
  `[-1,1]^(Kdim n m)`: each coordinate has modulus at most `1`.  The five blocks are

  * `uᵢ = psi (x i)`                          — `|psi| ≤ 1`;
  * `tᵢ = if ε i then z i else 0`             — `hε` says `ε i` is the sign of `|z i| ≤ 1`;
  * `sᵢ = if ε i then 0 else (z i)⁻¹`         — likewise, locally the reciprocal of a
                                                number of modulus `> 1`;
  * `qᵢ = if ε i then sqrt (1 - zᵢ²) else 0`  — `sqrt (1 - t²) ≤ 1` for every `t`;
  * `wᵢ = if ε (castAdd m i) then sqrt (psi (x i) * x i) else 0` — here `ε (castAdd m i) = true`
    forces `|z (castAdd m i)| = |x i| ≤ 1` by `hzx`, and `psi t * t = t²/√(1+t²) ≤ 1` for
    `|t| ≤ 1`.
-/
import Mathlib
import Submission.Work.WilE10.RexpSubDefs

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilE10.RexpSub

open WilkiesDesign WilkiesDesign.E

/-! ## The coordinate bounds -/

/-- The reciprocal of a number of modulus at least `1` lies in the cube. -/
theorem cube_abs_inv_le_one {t : ℝ} (h : 1 ≤ |t|) : |t⁻¹| ≤ 1 := by
  rw [abs_inv, inv_eq_one_div, div_le_iff₀ (lt_of_lt_of_le one_pos h), one_mul]
  exact h

/-- `sqrt (1 - t ^ 2)` lies in the cube, for every `t` (the small-branch tag `q`). -/
theorem cube_abs_sqrt_one_sub_sq_le_one (t : ℝ) : |Real.sqrt (1 - t ^ 2)| ≤ 1 := by
  rw [abs_of_nonneg (Real.sqrt_nonneg _)]
  calc Real.sqrt (1 - t ^ 2) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg t])
    _ = 1 := Real.sqrt_one

/-- `psi t * t ≤ 1` for `|t| ≤ 1`: the tag `w` of the small branch. -/
theorem cube_psi_mul_self_le_one {t : ℝ} (h : |t| ≤ 1) : psi t * t ≤ 1 := by
  have hpos : 0 < Real.sqrt (1 + t ^ 2) := Real.sqrt_pos.mpr (by nlinarith [sq_nonneg t])
  have h1 : 1 ≤ Real.sqrt (1 + t ^ 2) := by
    have h' : Real.sqrt 1 ≤ Real.sqrt (1 + t ^ 2) :=
      Real.sqrt_le_sqrt (by nlinarith [sq_nonneg t])
    rwa [Real.sqrt_one] at h'
  have ht2 : t ^ 2 ≤ 1 := by
    have h' := abs_nonneg t
    nlinarith [sq_abs t]
  have hpt : psi t * t = t ^ 2 / Real.sqrt (1 + t ^ 2) := by
    rw [psi]; field_simp
  rw [hpt, div_le_iff₀ hpos, one_mul]
  linarith

/-- `sqrt (psi t * t)` lies in the cube for `|t| ≤ 1`: the tag `w` of the small branch. -/
theorem cube_abs_sqrt_psi_mul_le_one {t : ℝ} (h : |t| ≤ 1) : |Real.sqrt (psi t * t)| ≤ 1 := by
  rw [abs_of_nonneg (Real.sqrt_nonneg _)]
  calc Real.sqrt (psi t * t) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt (cube_psi_mul_self_le_one h)
    _ = 1 := Real.sqrt_one

/-! ## The point -/

theorem mkPt_mem_cube (n m : ℕ) (x : Fin n → ℝ) (ε : Fin (n + m) → Bool) (z : Fin (n + m) → ℝ)
    (hzx : ∀ i : Fin n, z (Fin.castAdd m i) = x i)
    (hε : ∀ i : Fin (n + m), ε i = true ↔ |z i| ≤ 1) :
    Work.WilE10.mkPt n m x ε z ∈ WilkiesDesign.E.cubeC (Work.WilE10.Kdim n m) := by
  rw [WilkiesDesign.E.cubeC]
  intro k
  have hsurj : ∃ a : Idx n m, eA n m a = k := ⟨(eA n m).symm k, (eA n m).apply_symm_apply k⟩
  obtain ⟨idx, rfl⟩ := hsurj
  simp only [mkPt, Equiv.symm_apply_apply]
  rcases idx with iu | j
  · simp only [mkPoint]
    exact psi_abs_le_one (x iu)
  · rcases j with it | j
    · simp only [mkPoint]
      by_cases hb : ε it = true
      · rw [ite_eq_left hb]
        exact (hε it).1 hb
      · rw [ite_eq_right hb]
        simp
    · rcases j with is' | j
      · simp only [mkPoint]
        by_cases hb : ε is' = true
        · rw [ite_eq_left hb]
          simp
        · rw [ite_eq_right hb]
          refine cube_abs_inv_le_one ?_
          exact le_of_lt (not_le.mp (fun hc => hb ((hε is').2 hc)))
      · rcases j with iq | iw
        · simp only [mkPoint]
          by_cases hb : ε iq = true
          · rw [ite_eq_left hb]
            exact cube_abs_sqrt_one_sub_sq_le_one (z iq)
          · rw [ite_eq_right hb]
            simp
        · simp only [mkPoint]
          by_cases hb : ε (Fin.castAdd m iw) = true
          · rw [ite_eq_left hb]
            refine cube_abs_sqrt_psi_mul_le_one ?_
            have hz : |z (Fin.castAdd m iw)| ≤ 1 := (hε (Fin.castAdd m iw)).1 hb
            rwa [hzx iw] at hz
          · rw [ite_eq_right hb]
            simp

end Work.WilE10.RexpSub
