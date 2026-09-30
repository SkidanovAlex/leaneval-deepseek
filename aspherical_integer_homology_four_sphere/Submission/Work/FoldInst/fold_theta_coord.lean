import Mathlib
import Submission.Work.FoldInst.FoldPiece
import Submission.Work.FoldInst.CertFold

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FoldInst

open Matrix
open scoped Matrix

/-! ## Auxiliary computations for the fold chart `θ`

The fold chart of the class `i` and the sign index `r` is
`foldTheta i r = coordPerm i ∘ mobiusKlein (N_F D_r)` (see `FoldPiece.lean`).  The coordinate
identity `fold_theta_coord` below computes, for every point `y` of the Klein ball, the `t`-th
coordinate of the chart value in terms of the wall slack at `y` and the height of the point
`N_F · (act k_r y)` in the upper half space model.

The proof is a chain of elementary coordinate computations; the only non-trivial input is the fold
identity `fold_identity` (the certificate `N_F D_r k_r = R_{ε_r} N_F`). -/

/-- The coordinates `0,1,2` of `uhsOfHyp P` are the corresponding entries of `P` rescaled by the
height `(P₄ − P₃)⁻¹`. -/
theorem uhsOfHyp_coord_f3to5 (P : HypModel.V5) (w : Fin 3) :
    HypModel.uhsOfHyp P (f3to4 w) = P (f3to5 w) * (P 4 - P 3)⁻¹ := by
  fin_cases w <;> simp [HypModel.uhsOfHyp, f3to4, f3to5]

/-- The general form of the previous computation, for an abstract index `j` with `j < 3`. -/
theorem uhsOfHyp_coord (P : HypModel.V5) (j : Fin 4) (hj : (j : ℕ) < 3) :
    HypModel.uhsOfHyp P j = P ⟨j.val, by omega⟩ * (P 4 - P 3)⁻¹ := by
  obtain ⟨k, hk⟩ := j
  interval_cases k <;> simp_all [HypModel.uhsOfHyp]

/-- `uhsOfHyp` is invariant under rescaling of its argument *on the first three coordinates*: the
height coordinate changes, but `uhsOfHyp P 0, 1, 2` do not. -/
theorem uhsOfHyp_smul_horiz (c : ℝ) (P : HypModel.V5) (j : Fin 4) (hj : (j : ℕ) < 3)
    (hc : c ≠ 0) : HypModel.uhsOfHyp (c • P) j = HypModel.uhsOfHyp P j := by
  rw [uhsOfHyp_coord _ _ hj, uhsOfHyp_coord _ _ hj]
  have he : (c • P) ⟨j.val, by omega⟩ = c * P ⟨j.val, by omega⟩ := by simp
  have hd : (c • P) 4 - (c • P) 3 = c * (P 4 - P 3) := by simp; ring
  rw [he, hd, mul_inv]
  rw [show c * P ⟨j.val, by omega⟩ * (c⁻¹ * (P 4 - P 3)⁻¹)
      = (c * c⁻¹) * (P ⟨j.val, by omega⟩ * (P 4 - P 3)⁻¹) from by ring, mul_inv_cancel₀ hc,
    one_mul]

/-- The sign matrix `reflEr e = diag(e₀,e₁,e₂,1,1)` acts diagonally. -/
theorem reflEr_mulVec_apply (e : Fin 3 → ℤ) (P : HypModel.V5) (j : Fin 5) :
    (reflEr e *ᵥ P) j =
      (if h : (j : ℕ) < 3 then (e ⟨j, h⟩ : ℝ) else 1) * P j := by
  have h : reflEr e = Matrix.diagonal (fun i : Fin 5 =>
      if h : (i : ℕ) < 3 then (e ⟨i, h⟩ : ℝ) else 1) := by
    ext a b
    simp only [reflEr, reflE, Matrix.map_apply, Matrix.diagonal_apply, Int.coe_castRingHom]
    by_cases hab : a = b
    · subst hab
      by_cases h3 : (a : ℕ) < 3 <;> simp [h3]
    · simp [hab]
  rw [h, Matrix.mulVec_diagonal]

/-- The first three coordinates of `reflEr e *ᵥ P` are the sign-changed coordinates of `P`. -/
theorem reflEr_mulVec_f3to5 (e : Fin 3 → ℤ) (P : HypModel.V5) (w : Fin 3) :
    (reflEr e *ᵥ P) (f3to5 w) = (e w : ℝ) * P (f3to5 w) := by
  rw [reflEr_mulVec_apply]
  have h3 : ((f3to5 w : Fin 5) : ℕ) < 3 := w.isLt
  rw [dite_eq_left h3]
  congr 2

/-- The last two coordinates of `reflEr e *ᵥ P` are those of `P`. -/
theorem reflEr_mulVec_four (e : Fin 3 → ℤ) (P : HypModel.V5) :
    (reflEr e *ᵥ P) 4 = P 4 := by
  rw [reflEr_mulVec_apply]; norm_num

/-- The last two coordinates of `reflEr e *ᵥ P` are those of `P`. -/
theorem reflEr_mulVec_three (e : Fin 3 → ℤ) (P : HypModel.V5) :
    (reflEr e *ᵥ P) 3 = P 3 := by
  rw [reflEr_mulVec_apply]; norm_num

/-- **The fold identity, over `ℝ`.**  The fold identity `N_F D_r k_r = R_{ε_r} N_F` of the
certificate, transported to the real normalisation `N_F = ½ (2 N_F)` used by the chart. -/
theorem foldNr_mul_D_mul_K (i : Fin 98) (r : Fin (foldCodim i) → Bool) :
    foldNr i * foldDrR i r * foldKrR i r = reflEr (foldEr i r) * foldNr i := by
  have hid := fold_identity i (foldRepOf i r) (isReal_repOf i r)
  simp only [foldNr, matR, foldDrR, foldDr, foldKrR, foldKr, reflEr, foldEr]
  rw [smul_mul_assoc, smul_mul_assoc, ← Matrix.map_mul, ← Matrix.map_mul, hid, Matrix.map_mul,
    mul_smul_comm]

/-- The Klein diagonal `k_r` of a representative acts on the null ray of `act k_r y` by bringing it
back to the ray of `y`: `k_r · (act k_r y, 1) = (y, 1)`. -/
theorem foldKrR_mulVec_ray_act (i : Fin 98) (r : Fin (foldCodim i) → Bool) (y : E4) :
    foldKrR i r *ᵥ HypModel.ray (act (toG (foldKr i r)) y) = HypModel.ray y := by
  have hK : ∀ j : Fin 4, signVec (toG (foldKr i r)) j = foldKr i r j :=
    fun j => by
      have hp := foldRepK_pm i (foldRepOf i r) j
      simp only [foldKr] at hp ⊢
      rcases hp with h | h <;> simp [signVec, toG, h]
  have hK2 : ∀ j : Fin 4, (foldKr i r j : ℝ) * (foldKr i r j : ℝ) = 1 := fun j => by
    have hp := foldRepK_pm i (foldRepOf i r) j
    simp only [foldKr] at hp ⊢
    rcases hp with h | h <;> simp [h]
  have hdiag : foldKrR i r = Matrix.diagonal (fun j : Fin 5 =>
      if h : (j : ℕ) < 4 then ((foldKr i r) ⟨j, h⟩ : ℝ) else 1) := by
    ext a b
    simp only [foldKrR, diagK, Matrix.map_apply, Matrix.diagonal_apply, Int.coe_castRingHom]
    by_cases hab : a = b
    · subst hab; by_cases h4 : (a : ℕ) < 4 <;> simp [h4]
    · simp [hab]
  ext j
  rw [hdiag, Matrix.mulVec_diagonal]
  fin_cases j <;> simp [HypModel.ray, act_apply_apply, hK]
  all_goals rw [← mul_assoc, hK2 _]
  all_goals simp

/-- The rows `0,1,2` of the normalisation `N_F`: the `w`-th row is minus the normal of the `w`-th
side of the triple, completed by `1` in the last place. -/
theorem foldNr_mulVec_ray_row (i : Fin 98) (w : Fin 3) (z : E4) :
    (foldNr i *ᵥ HypModel.ray z) (f3to5 w) = sideSlack (foldTriple i w) z := by
  simp only [Matrix.mulVec, dotProduct, sideSlack]
  have hsplit : ∀ f : Fin 5 → ℝ, (∑ j, f j) = (∑ t4 : Fin 4, f (f4to5 t4)) + f 4 := by
    intro f; rw [Fin.sum_univ_five, Fin.sum_univ_four]; norm_num [f4to5]
  rw [hsplit (fun j => foldNr i (f3to5 w) j * HypModel.ray z j)]
  have h1 : ∀ t4 : Fin 4, foldNr i (f3to5 w) (f4to5 t4) * HypModel.ray z (f4to5 t4) =
      - (sideNormal (foldTriple i w) t4 : ℝ) * z t4 := by
    intro t4
    have hf : foldNr i (f3to5 w) (f4to5 t4) = - (sideNormal (foldTriple i w) t4 : ℝ) := by
      simp only [foldNr, matR, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
      rw [foldN2_row, Int.coe_castRingHom]; push_cast; ring
    rw [hf]
    congr 1
    fin_cases t4 <;> rfl
  have hf4 : foldNr i (f3to5 w) 4 = 1 := by
    simp only [foldNr, matR, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    rw [foldN2_row_last]; norm_num
  have h2 : HypModel.ray z 4 = 1 := rfl
  simp only [h1, hf4, h2, mul_one]
  simp only [neg_mul, Finset.sum_neg_distrib]
  ring

/-- The sign change `act g` preserves the quantity `1 - ‖·‖²`. -/
theorem one_sub_norm_sq_act (g : Fin 4 → ZMod 2) (y : E4) :
    (1 : ℝ) - ‖act g y‖ ^ 2 = 1 - ‖y‖ ^ 2 := by
  have hε : ∀ i : Fin 4, ((signVec g i : ℤ) : ℝ) ^ 2 = 1 := fun i => by
    have := signVec_sq g i
    rw [sq]; exact_mod_cast this
  have h := HypModel.one_sub_norm_sq_rot4_diagonal (fun i => (signVec g i : ℝ)) hε y
  simpa only [act] using h

/-- **The height of the chart output.**  The third coordinate (the height in the upper half space
model) of `mobiusKlein N_F (act k_r y)` is `√(1-‖y‖²) Δ⁻¹`, where `Δ` is the height difference of
the vector `N_F · (act k_r y, 1)`. -/
theorem mobiusKlein_height (i : Fin 98) (r : Fin (foldCodim i) → Bool) (y : E4) :
    (HypModel.mobiusKlein (foldNr i) (act (toG (foldKr i r)) y)) 3
      = Real.sqrt (1 - ‖y‖ ^ 2) *
        (((foldNr i *ᵥ HypModel.ray (act (toG (foldKr i r)) y)) 4
          - (foldNr i *ᵥ HypModel.ray (act (toG (foldKr i r)) y)) 3)⁻¹) := by
  have hnorm := one_sub_norm_sq_act (toG (foldKr i r)) y
  have hsqrt : Real.sqrt (1 - ‖act (toG (foldKr i r)) y‖ ^ 2) = Real.sqrt (1 - ‖y‖ ^ 2) := by
    rw [hnorm]
  have h4 : (((Real.sqrt (1 - ‖act (toG (foldKr i r)) y‖ ^ 2))⁻¹) •
        (foldNr i *ᵥ HypModel.ray (act (toG (foldKr i r)) y))) 4
      = (Real.sqrt (1 - ‖y‖ ^ 2))⁻¹ * (foldNr i *ᵥ HypModel.ray (act (toG (foldKr i r)) y)) 4 := by
    simp [hsqrt]
  have h3 : (((Real.sqrt (1 - ‖act (toG (foldKr i r)) y‖ ^ 2))⁻¹) •
        (foldNr i *ᵥ HypModel.ray (act (toG (foldKr i r)) y))) 3
      = (Real.sqrt (1 - ‖y‖ ^ 2))⁻¹ * (foldNr i *ᵥ HypModel.ray (act (toG (foldKr i r)) y)) 3 := by
    simp [hsqrt]
  simp only [HypModel.mobiusKlein, HypModel.hypOfKlein, Matrix.mulVec_smul]
  rw [HypModel.uhsOfHyp_apply_three, h4, h3]
  rw [show (Real.sqrt (1 - ‖y‖ ^ 2))⁻¹ * (foldNr i *ᵥ HypModel.ray (act (toG (foldKr i r)) y)) 4
        - (Real.sqrt (1 - ‖y‖ ^ 2))⁻¹ * (foldNr i *ᵥ HypModel.ray (act (toG (foldKr i r)) y)) 3
      = (Real.sqrt (1 - ‖y‖ ^ 2))⁻¹ *
        ((foldNr i *ᵥ HypModel.ray (act (toG (foldKr i r)) y)) 4
          - (foldNr i *ᵥ HypModel.ray (act (toG (foldKr i r)) y)) 3) from by ring]
  rw [mul_inv, inv_inv]

/-- The walls of the representative `(i,r)` are the images of the triple sides of the class under
the Klein diagonal `k_r`. -/
theorem foldWalls_eq (i : Fin 98) (r : Fin (foldCodim i) → Bool) (s : Fin 3)
    (hs : (s : ℕ) < foldCodim i) :
    foldWalls i r ⟨s.val, hs⟩ =
      sidePerm (toG (foldKr i r)) (foldTriple i (foldWallPos i s)) := by
  rw [foldWalls, foldTriple_wallPos i s hs]
  congr 1

/-- The sign `ε_r` at the wall position of `s` is the sign indexed by `s`. -/
theorem foldEr_wallPos (i : Fin 98) (r : Fin (foldCodim i) → Bool) (s : Fin 3)
    (hs : (s : ℕ) < foldCodim i) :
    foldEr i r (foldWallPos i s) = if r ⟨s.val, hs⟩ then -1 else 1 := by
  have h1 : foldPosIsWall i (foldWallPos i s) = 1 :=
    (foldPosIsWall_iff i (foldWallPos i s)).mpr ⟨s, hs, rfl⟩
  have h2 : (foldPosToWall i (foldWallPos i s) : ℕ) < foldCodim i := by
    rw [foldPosToWall_spec i s hs]; exact hs
  have harg : (⟨foldPosToWall i (foldWallPos i s), h2⟩ : Fin (foldCodim i)) = ⟨s.val, hs⟩ :=
    Fin.ext (congrArg (fun x : Fin 3 => (x : ℕ)) (foldPosToWall_spec i s hs))
  rw [foldEr, foldRepEps_pattern]
  simp only [foldPattern, h1, h2, and_self, ↓reduceDIte, harg]

/-- The real form of the previous sign identity. -/
theorem foldEr_wallPos_real (i : Fin 98) (r : Fin (foldCodim i) → Bool) (s : Fin 3)
    (hs : (s : ℕ) < foldCodim i) :
    (foldEr i r (foldWallPos i s) : ℝ) = if r ⟨s.val, hs⟩ then -1 else 1 := by
  rw [foldEr_wallPos i r s hs]
  split <;> norm_num

/-- **The coordinate computation for the fold chart.**  The `s`-th chart coordinate of the fold
chart of `(i,r)` at the Klein point `y` is the sign `ε_r` at the wall position of `s`, times the
row of the normalisation, times the inverse height of `N_F · (act k_r y, 1)`. -/
theorem foldTheta_coord_apply (i : Fin 98) (r : Fin (foldCodim i) → Bool) (y : E4)
    (hy : y ∈ Work.HypModel.ball) (s : Fin 3) (hs : (s : ℕ) < foldCodim i) :
    (foldTheta i r y) (f3to4 s) =
      (foldEr i r (foldWallPos i s) : ℝ) *
        (foldNr i *ᵥ HypModel.ray (act (toG (foldKr i r)) y)) (f3to5 (foldWallPos i s)) *
        (((foldNr i *ᵥ HypModel.ray (act (toG (foldKr i r)) y)) 4
          - (foldNr i *ᵥ HypModel.ray (act (toG (foldKr i r)) y)) 3)⁻¹) := by
  have hpos : (0 : ℝ) < 1 - ‖y‖ ^ 2 := by
    have hlt : ‖y‖ < 1 := hy
    nlinarith [norm_nonneg y]
  have hc : (Real.sqrt (1 - ‖y‖ ^ 2))⁻¹ ≠ 0 :=
    inv_ne_zero (ne_of_gt (Real.sqrt_pos.mpr hpos))
  rw [show (foldTheta i r y) (f3to4 s) =
        (HypModel.uhsOfHyp ((foldNr i * foldDrR i r) *ᵥ HypModel.hypOfKlein y))
          (f3to4 (foldWallPos i s)) from by
      simp only [foldTheta, HypModel.mobiusKlein]
      rw [coordPerm_apply, coordPerm_invFun_wall i s hs]]
  rw [show (foldNr i * foldDrR i r) *ᵥ HypModel.hypOfKlein y
        = (Real.sqrt (1 - ‖y‖ ^ 2))⁻¹ • ((foldNr i * foldDrR i r) *ᵥ HypModel.ray y) from by
      simp only [HypModel.hypOfKlein, Matrix.mulVec_smul]]
  rw [uhsOfHyp_smul_horiz ((Real.sqrt (1 - ‖y‖ ^ 2))⁻¹)
        ((foldNr i * foldDrR i r) *ᵥ HypModel.ray y) (f3to4 (foldWallPos i s))
        (by simp [f3to4]) hc]
  rw [uhsOfHyp_coord_f3to5]
  have hV : (foldNr i * foldDrR i r) *ᵥ HypModel.ray y
      = reflEr (foldEr i r) *ᵥ (foldNr i *ᵥ HypModel.ray (act (toG (foldKr i r)) y)) := by
    rw [← foldKrR_mulVec_ray_act i r y, Matrix.mulVec_mulVec, foldNr_mul_D_mul_K i r,
      ← Matrix.mulVec_mulVec]
  rw [hV, reflEr_mulVec_f3to5, reflEr_mulVec_four, reflEr_mulVec_three]

theorem fold_theta_coord (i : Fin 98) (r : Fin (foldCodim i) → Bool) (y : E4) (hy : y ∈ Work.HypModel.ball) (t : Fin (foldCodim i)) : Real.sqrt (1 - ‖y‖ ^ 2) * (foldTheta i r y) ⟨t, by have := t.isLt; have := foldCodim_le i; omega⟩ = (if r t then -1 else 1) * sideSlack (foldWalls i r t) y * (HypModel.mobiusKlein (foldNr i) (act (toG (foldKr i r)) y)) 3 := by
  have hc3 : (t : ℕ) < 3 := by have := foldCodim_le i; omega
  set s : Fin 3 := ⟨t.val, hc3⟩ with hs_def
  have hs : (s : ℕ) < foldCodim i := by rw [hs_def]; exact t.isLt
  have hidx : (⟨t, by have := t.isLt; have := foldCodim_le i; omega⟩ : Fin 4) = f3to4 s := by
    apply Fin.ext
    simp [f3to4, hs_def]
  have hts : t = (⟨s.val, hs⟩ : Fin (foldCodim i)) := by
    apply Fin.ext
    simp [hs_def]
  rw [hidx, hts, foldTheta_coord_apply i r y hy s hs, mobiusKlein_height i r y,
    foldEr_wallPos_real i r s hs, foldWalls_eq i r s hs,
    ← sideSlack_act (toG (foldKr i r)) (foldTriple i (foldWallPos i s)) y,
    ← foldNr_mulVec_ray_row i (foldWallPos i s) (act (toG (foldKr i r)) y)]
  by_cases hr : r ⟨s.val, hs⟩ <;> simp [hr] <;> ring

end Work.FoldInst
