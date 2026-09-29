import Mathlib
import Submission.Work.Cert.Spec
import Submission.Work.Cert.ACore.drift_le

/-!
# Grid drift of the conjunct-2 (1024-grid) certificate

Copy-edit of `Submission/Work/Cert/ACore/drift_le.lean` (the proved 4096-grid drift lemma) to the
coarser `NARC2 = 1024` grid of certificate v4.

With `z_j = cx (E j).1 (E j).2`, `u_j = (Rk k/S)·rot (j/NARC2)`, `W = cx WR2 WI2` and
`ρ = rot (1/NARC2)` the one-step identity

  `z_{j+1} − u_{j+1} = (z_{j+1} − z_j·W) + z_j·(W − ρ) + (z_j − u_j)·ρ`

gives `δ_{j+1} ≤ g_j + (Rk k/S + δ_j)·(2/S) + δ_j` with the step term `g_j ≤ 27/(2S)`, hence
`δ_j ≤ 16j/S ≤ 16·1024/S = 16384/S ≤ 65536/S`.

The geometric helper lemmas (`rot_zero`, `rot_add`, `norm_rot`, `cx_eq_div`, `cx_step_eq`,
`norm_int_le`, `drift_step`, `step_arith`) are grid-independent and are reused from
`Submission.Work.Cert.ACore.drift_le`; only the one-step bound (for `gridStep2`/`WR2`/`WI2`) and the
arithmetic of `1/NARC2` are redone here.  Note the step bound `√181/S` is independent of the
constants `WR2`, `WI2`: only `GTOL = 8` and the division remainders enter.
-/

namespace Work.Cert

open Submission.CDTPlan

/-- `(NARC2 : ℝ) = 1024`. -/
lemma drift2_NARC2_cast : ((NARC2 : ℝ)) = 1024 := by norm_num [NARC2]

/-- The scale `NARC2` is nonzero in `ℝ`. -/
lemma drift2_NARC2_ne : (NARC2 : ℝ) ≠ 0 := by
  rw [drift2_NARC2_cast]; norm_num

/-! ## The one-step bound on the 1024-grid

`gridStep2 ex ey nx ny` (tolerance `GTOL = 8`) implies
`‖cx nx ny − cx ex ey · cx WR2 WI2‖ ≤ 27/(2S)`; the proof is that of `gridStep_norm_le` with an
arbitrary pair `(wr, wi)` of constants, since the bound never uses their values. -/

theorem drift2_gridStep_norm_le_aux (wr wi ex ey nx ny : ℤ)
    (h : (decide (iabs (nx - cmr ex ey wr wi) ≤ GTOL) &&
          decide (iabs (ny - cmi ex ey wr wi) ≤ GTOL)) = true) :
    ‖cx nx ny - cx ex ey * cx wr wi‖ ≤ 27 / (2 * (S : ℝ)) := by
  have hS : (0 : ℝ) < (S : ℝ) := ACore.S_pos_real
  have hSpos : (0 : ℤ) < S := by norm_num [S]
  have hmem := h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hmem
  have hd1 : |nx - cmr ex ey wr wi| ≤ 8 := by
    rw [← ACore.iabs_eq]; exact hmem.1
  have hd2 : |ny - cmi ex ey wr wi| ≤ 8 := by
    rw [← ACore.iabs_eq]; exact hmem.2
  have h1 : S * md ex wr + (ex * wr) % S = ex * wr := by
    simp only [md, fdiv]
    exact Int.mul_ediv_add_emod (ex * wr) S
  have h2 : S * md ey wi + (ey * wi) % S = ey * wi := by
    simp only [md, fdiv]
    exact Int.mul_ediv_add_emod (ey * wi) S
  have h3 : S * md ex wi + (ex * wi) % S = ex * wi := by
    simp only [md, fdiv]
    exact Int.mul_ediv_add_emod (ex * wi) S
  have h4 : S * md ey wr + (ey * wr) % S = ey * wr := by
    simp only [md, fdiv]
    exact Int.mul_ediv_add_emod (ey * wr) S
  have e1 : nx * S - (ex * wr - ey * wi)
      = S * (nx - cmr ex ey wr wi)
        - (ex * wr) % S + (ey * wi) % S := by
    simp only [cmr]
    linarith
  have e2 : ny * S - (ex * wi + ey * wr)
      = S * (ny - cmi ex ey wr wi)
        - (ex * wi) % S - (ey * wr) % S := by
    simp only [cmi]
    linarith
  have b1 : |S * (nx - cmr ex ey wr wi)| ≤ 8 * S := by
    rw [abs_mul, abs_of_nonneg (le_of_lt hSpos)]
    exact mul_le_mul_of_nonneg_left hd1 (le_of_lt hSpos)
  have b2 : |-((ex * wr) % S) + (ey * wi) % S| ≤ S - 1 := by
    rw [abs_le]
    constructor
    · have ha := Int.emod_nonneg (ey * wi) (by norm_num [S] : S ≠ 0)
      have hb := Int.emod_lt_of_pos (ex * wr) hSpos
      linarith
    · have ha := Int.emod_nonneg (ex * wr) (by norm_num [S] : S ≠ 0)
      have hb := Int.emod_lt_of_pos (ey * wi) hSpos
      linarith
  have b3 : |S * (ny - cmi ex ey wr wi)| ≤ 8 * S := by
    rw [abs_mul, abs_of_nonneg (le_of_lt hSpos)]
    exact mul_le_mul_of_nonneg_left hd2 (le_of_lt hSpos)
  have b4 : |-((ex * wi) % S) - ((ey * wr) % S)| ≤ 2 * S - 2 := by
    rw [abs_le]
    constructor
    · have hb1 := Int.emod_lt_of_pos (ex * wi) hSpos
      have hb2 := Int.emod_lt_of_pos (ey * wr) hSpos
      linarith
    · have ha1 := Int.emod_nonneg (ex * wi) (by norm_num [S] : S ≠ 0)
      have ha2 := Int.emod_nonneg (ey * wr) (by norm_num [S] : S ≠ 0)
      linarith
  have hA : |nx * S - (ex * wr - ey * wi)| ≤ 9 * S := by
    rw [e1, show S * (nx - cmr ex ey wr wi)
          - (ex * wr) % S + (ey * wi) % S
        = S * (nx - cmr ex ey wr wi)
          + (-((ex * wr) % S) + (ey * wi) % S) by ring]
    have hh := abs_add_le (S * (nx - cmr ex ey wr wi))
      (-((ex * wr) % S) + (ey * wi) % S)
    linarith
  have hB : |ny * S - (ex * wi + ey * wr)| ≤ 10 * S := by
    rw [e2, show S * (ny - cmi ex ey wr wi)
          - (ex * wi) % S - (ey * wr) % S
        = S * (ny - cmi ex ey wr wi)
          + (-((ex * wi) % S) - (ey * wr) % S) by ring]
    have hh := abs_add_le (S * (ny - cmi ex ey wr wi))
      (-((ex * wi) % S) - (ey * wr) % S)
    linarith
  rw [ACore.cx_step_eq ex ey wr wi nx ny, norm_div]
  have hden : ‖(S : ℂ) ^ 2‖ = (S : ℝ) ^ 2 := by
    rw [norm_pow, Complex.norm_intCast, abs_of_pos hS]
  rw [hden]
  have hnum := ACore.norm_int_le _ _ hA hB
  calc ‖((nx * S - (ex * wr - ey * wi) : ℤ) : ℂ) +
          (((ny * S - (ex * wi + ey * wr) : ℤ)) : ℂ) * Complex.I‖
          / (S : ℝ) ^ 2
      ≤ ((27 / 2) * (S : ℝ)) / (S : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right hnum (by positivity)
    _ = 27 / (2 * (S : ℝ)) := by field_simp

/-- `gridStep2` (tolerance `GTOL = 8`) implies `‖cx nx ny − cx ex ey · cx WR2 WI2‖ ≤ 27/(2S)`. -/
theorem drift2_gridStep_norm_le (ex ey nx ny : ℤ) (h : gridStep2 ex ey nx ny = true) :
    ‖cx nx ny - cx ex ey * cx WR2 WI2‖ ≤ 27 / (2 * (S : ℝ)) :=
  drift2_gridStep_norm_le_aux WR2 WI2 ex ey nx ny h

/-- `(Rk k/S)·rot ((n+1)/NARC2) = ((Rk k/S)·rot (n/NARC2))·rot (1/NARC2)`. -/
theorem drift2_rot_step (k n : ℕ) :
    ((Rk k : ℝ) / (S : ℝ)) * rot (((n + 1 : ℕ) : ℝ) / (NARC2 : ℝ))
      = (((Rk k : ℝ) / (S : ℝ)) * rot ((n : ℝ) / (NARC2 : ℝ)))
          * rot (1 / (NARC2 : ℝ)) := by
  rw [show (((n + 1 : ℕ) : ℝ)) / (NARC2 : ℝ)
        = (n : ℝ) / (NARC2 : ℝ) + 1 / (NARC2 : ℝ) by push_cast; ring]
  rw [ACore.rot_add]
  ring

open Submission.CDTPlan in
/-- **Grid drift on the 1024-grid.**  The certificate's grid points `E j` satisfy the exact circle
points `(Rk k / S) · rot (j/NARC2)` to within `65536/S`, by induction on `j` from the integer step
`gridStep2` and the rotation tolerance `‖cx WR2 WI2 − rot(1/NARC2)‖ ≤ 2/S`. -/
theorem drift_le2 (hW : RotConsts2) (k : ℕ) (hk : k ≤ 2) (E : ℕ → ℤ × ℤ) (h0 : E 0 = (Rk k, 0))
    (hstep : ∀ j, j < NARC2 → gridStep2 (E j).1 (E j).2 (E (j + 1)).1 (E (j + 1)).2 = true)
    (j : ℕ) (hj : j ≤ NARC2) :
    ‖cx (E j).1 (E j).2 - ((Rk k : ℝ) / (S : ℝ)) * rot ((j : ℝ) / NARC2)‖ ≤ 65536 / (S : ℝ) := by
  have hS : (0 : ℝ) < (S : ℝ) := ACore.S_pos_real
  have hk0 : (0 : ℝ) ≤ (Rk k : ℝ) := by exact_mod_cast (ACore.Rk_facts k hk).1
  have hkS : (Rk k : ℝ) ≤ (S : ℝ) := (ACore.Rk_facts k hk).2
  have hR1 : (Rk k : ℝ) / (S : ℝ) ≤ 1 := by
    rw [div_le_one hS]
    exact hkS
  have hW' : ‖cx WR2 WI2 - rot (1 / (NARC2 : ℝ))‖ ≤ 2 / (S : ℝ) := hW
  have key : ∀ m : ℕ, m ≤ NARC2 →
      ‖cx (E m).1 (E m).2 - ((Rk k : ℝ) / (S : ℝ))
          * rot ((m : ℝ) / NARC2)‖ ≤ 16 * (m : ℝ) / (S : ℝ) := by
    intro m
    induction m with
    | zero =>
        intro _
        have hz : cx (E 0).1 (E 0).2
            - ((Rk k : ℝ) / (S : ℝ)) * rot (((0 : ℕ) : ℝ) / NARC2) = 0 := by
          rw [h0]
          simp [cx, rot]
        rw [hz]
        norm_num
    | succ n ih =>
        intro hn
        have hnlt : n < NARC2 := by omega
        have ihn : ‖cx (E n).1 (E n).2
            - ((Rk k : ℝ) / (S : ℝ)) * rot ((n : ℝ) / NARC2)‖
              ≤ 16 * (n : ℝ) / (S : ℝ) := ih (by omega)
        have hstepn := hstep n hnlt
        have hg : ‖cx (E (n + 1)).1 (E (n + 1)).2
            - cx (E n).1 (E n).2 * cx WR2 WI2‖
              ≤ 27 / (2 * (S : ℝ)) := drift2_gridStep_norm_le _ _ _ _ hstepn
        have hz_le : ‖cx (E n).1 (E n).2‖
            ≤ (Rk k : ℝ) / (S : ℝ)
              + ‖cx (E n).1 (E n).2
                  - ((Rk k : ℝ) / (S : ℝ)) * rot ((n : ℝ) / NARC2)‖ := by
          have h := norm_add_le
            (cx (E n).1 (E n).2
              - ((Rk k : ℝ) / (S : ℝ)) * rot ((n : ℝ) / NARC2))
            (((Rk k : ℝ) / (S : ℝ)) * rot ((n : ℝ) / NARC2))
          have he : cx (E n).1 (E n).2
                - ((Rk k : ℝ) / (S : ℝ)) * rot ((n : ℝ) / NARC2)
              + (((Rk k : ℝ) / (S : ℝ)) * rot ((n : ℝ) / NARC2))
              = cx (E n).1 (E n).2 := by ring
          rw [he] at h
          have hu : ‖((Rk k : ℝ) / (S : ℝ)) * rot ((n : ℝ) / NARC2)‖
              = (Rk k : ℝ) / (S : ℝ) := by
            rw [norm_mul, ACore.norm_rot, mul_one, ← Complex.ofReal_div]
            exact ACore.norm_ofReal_of_nonneg (div_nonneg hk0 hS.le)
          rw [hu] at h
          linarith [h]
        have hdr := ACore.drift_step (W := cx WR2 WI2)
          (ρ := rot (1 / (NARC2 : ℝ))) (z := cx (E n).1 (E n).2)
          (z' := cx (E (n + 1)).1 (E (n + 1)).2)
          (u := ((Rk k : ℝ) / (S : ℝ)) * rot ((n : ℝ) / NARC2))
          (g := 27 / (2 * (S : ℝ))) (c := 2 / (S : ℝ))
          (Rz := (Rk k : ℝ) / (S : ℝ)
            + ‖cx (E n).1 (E n).2
                - ((Rk k : ℝ) / (S : ℝ)) * rot ((n : ℝ) / NARC2)‖)
          (dd := ‖cx (E n).1 (E n).2
                - ((Rk k : ℝ) / (S : ℝ)) * rot ((n : ℝ) / NARC2)‖)
          hg hW' (ACore.norm_rot _) hz_le (le_refl _)
        have harith := ACore.step_arith n ((Rk k : ℝ) / (S : ℝ))
          ‖cx (E n).1 (E n).2
            - ((Rk k : ℝ) / (S : ℝ)) * rot ((n : ℝ) / NARC2)‖
          (by have hn1024 : n < 1024 := hnlt; omega) hR1 ihn
        rw [drift2_rot_step]
        have hfin := hdr.trans harith
        simpa using hfin
  have hmain := key j hj
  have hfin : 16 * (j : ℝ) / (S : ℝ) ≤ 65536 / (S : ℝ) := by
    apply div_le_div_of_nonneg_right _ hS.le
    have hj1024 : j ≤ 1024 := hj
    have hj' : (j : ℝ) ≤ 4096 := by exact_mod_cast (by omega : j ≤ 4096)
    linarith
  linarith

end Work.Cert
