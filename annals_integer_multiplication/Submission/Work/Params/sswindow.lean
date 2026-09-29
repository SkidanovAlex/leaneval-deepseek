import Mathlib
import Submission.Work.Params.tsfacts
import Submission.Work.Params.uparfacts
import Submission.Work.Params.basic
import Submission.Work.Params.defs

/-!
# The window condition `(1-2η)tᵢ < sᵢ ≤ (1-η)tᵢ` for the explicit parameters `tsPar`, `ssPar`

The paper §5.1 needs, for each `i < d`, the window condition of `ParamOK` for the concrete lists
`tsPar n` (`d'` copies of `r/2` followed by `d-d'` copies of `r`) and `ssPar n`
(`u₀ + F(k+1)` resp. `2u₀ - 1 + 2F(k-d'+1)`).

The hypotheses are exactly the size conditions that make the windows nonempty:
`8d(FQ + Fd + 1) ≤ r` for the `r/2`-branch and `4d(1 + 2FQ + 2Fd) ≤ r` for the `r`-branch,
where `F = Ffac`, `Q = Qall`, `r = rpar n`.
-/

set_option autoImplicit false

namespace Work.Params

open HvdH

/-- Integer-quotient bound: `m/n < ⌊m/n⌋ + 1` in `ℝ`. -/
theorem nat_div_lt_succ (m n : ℕ) : (m : ℝ) / n < ((m / n : ℕ) : ℝ) + 1 := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  have h1 : (m : ℝ) = (n : ℝ) * ((m / n : ℕ) : ℝ) + ((m % n : ℕ) : ℝ) := by
    have := congrArg (fun k : ℕ => (k : ℝ)) (Nat.div_add_mod m n)
    push_cast at this
    linarith [this]
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hmod : ((m % n : ℕ) : ℝ) < (n : ℝ) := by exact_mod_cast Nat.mod_lt m hn
  rw [h1, div_lt_iff₀ hnpos]
  nlinarith

/-- `getD` evaluation for `tsPar`. -/
theorem tsPar_getD_sswindow (n i : ℕ) (hi : i < HvdH.D) :
    (tsPar n).getD i 0 = (if i < dpar n then rpar n / 2 else rpar n) := by
  unfold tsPar
  rw [List.getD_eq_getElem _ _ (by rw [List.length_map, List.length_range]; exact hi)]
  rw [List.getElem_map, List.getElem_range]

/-- `getD` evaluation for `ssPar`. -/
theorem ssPar_getD_sswindow (n i : ℕ) (hi : i < HvdH.D) :
    (ssPar n).getD i 0 = (if i < dpar n then upar n + Ffac * (i + 1)
      else 2 * upar n - 1 + 2 * Ffac * (i - dpar n + 1)) := by
  unfold ssPar
  rw [List.getD_eq_getElem _ _ (by rw [List.length_map, List.length_range]; exact hi)]
  rw [List.getElem_map, List.getElem_range]

/-- `1 ≤ upar n`: `upar n ≥ Lpar n = _ + 1`. -/
theorem upar_one_le (n : ℕ) : 1 ≤ upar n := by
  have h := (uparfacts n).1
  unfold Lpar at h
  exact le_trans (Nat.le_add_left 1 (rpar n * (2*HvdH.D-1) / (4*HvdH.D))) h

/-- Real window, `r/2`-branch: `u₀` and `F(k+1)` fit in `((1-2η)r/2, (1-η)r/2]`. -/
theorem sswindow_lo (R L U F Q x : ℝ) (hF : 0 < F) (hx : 0 ≤ x) (hxD : x ≤ (HvdH.D:ℝ))
    (hxL : R * (2 * (HvdH.D:ℝ) - 1) / (4 * (HvdH.D:ℝ)) < L) (hLu : L ≤ U)
    (hLx : L ≤ R * (2 * (HvdH.D:ℝ) - 1) / (4 * (HvdH.D:ℝ)) + 1)
    (huQ : U < L + F * Q) (h1 : 8 * (HvdH.D:ℝ) * (F * Q + F * (HvdH.D:ℝ) + 1) ≤ R) :
    (1 - 2 / (4 * (HvdH.D:ℝ))) * (R / 2) < U + F * x ∧
      U + F * x ≤ (1 - 1 / (4 * (HvdH.D:ℝ))) * (R / 2) := by
  simp only [HvdH.D, Nat.cast_ofNat] at *
  norm_num at *
  constructor <;> nlinarith [mul_nonneg hF.le hx]

/-- Real window, `r`-branch: `2u₀-1` and `2F(k-d'+1)` fit in `((1-2η)r, (1-η)r]`. -/
theorem sswindow_hi (R L U F Q y : ℝ) (hF : 1 ≤ F) (hy : 1 ≤ y) (hyD : y ≤ (HvdH.D:ℝ))
    (hxL : R * (2 * (HvdH.D:ℝ) - 1) / (4 * (HvdH.D:ℝ)) < L) (hLu : L ≤ U)
    (hLx : L ≤ R * (2 * (HvdH.D:ℝ) - 1) / (4 * (HvdH.D:ℝ)) + 1)
    (huQ : U < L + F * Q) (h2 : 4 * (HvdH.D:ℝ) * (1 + 2 * F * Q + 2 * F * (HvdH.D:ℝ)) ≤ R) :
    (1 - 2 / (4 * (HvdH.D:ℝ))) * R < 2 * U - 1 + 2 * F * y ∧
      2 * U - 1 + 2 * F * y ≤ (1 - 1 / (4 * (HvdH.D:ℝ))) * R := by
  simp only [HvdH.D, Nat.cast_ofNat] at *
  norm_num at *
  constructor <;> nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ F) (by linarith : (0:ℝ) ≤ y)]

theorem sswindow (n : ℕ)
    (h1 : 8 * HvdH.D * (Work.Params.Ffac * Work.Params.Qall + Work.Params.Ffac * HvdH.D + 1) ≤ HvdH.rpar n)
    (h2 : 4 * HvdH.D * (1 + 2 * Work.Params.Ffac * Work.Params.Qall + 2 * Work.Params.Ffac * HvdH.D) ≤ HvdH.rpar n) :
    ∀ i < HvdH.D, (1 - 2 / (4 * HvdH.D : ℝ)) * ((Work.Params.tsPar n).getD i 0 : ℝ) < ((Work.Params.ssPar n).getD i 0 : ℝ) ∧
      ((Work.Params.ssPar n).getD i 0 : ℝ) ≤ (1 - 1 / (4 * HvdH.D : ℝ)) * ((Work.Params.tsPar n).getD i 0 : ℝ) := by
  intro i hi
  have hts := tsPar_getD_sswindow n i hi
  have hss := ssPar_getD_sswindow n i hi
  have hk : 1 ≤ krpar n := by
    have hFQ1 : 1 ≤ Ffac * Qall :=
      Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero Ffac_ne_zero (Nat.pos_iff_ne_zero.mp Qall_pos))
    have hbracket : 2 ≤ Ffac * Qall + Ffac * HvdH.D + 1 := by omega
    have h8D : 1 ≤ 8 * HvdH.D := by decide
    have hbig : 2 ≤ 8 * HvdH.D * (Ffac * Qall + Ffac * HvdH.D + 1) := by
      have := Nat.mul_le_mul h8D hbracket
      simpa using this
    have hR2 : 2 ≤ rpar n := le_trans hbig h1
    by_contra hkk
    have h0 : krpar n = 0 := by omega
    simp only [ts_rpar_eq, h0, pow_zero] at hR2
    omega
  have hRhalf : ((rpar n / 2 : ℕ) : ℝ) = (rpar n : ℝ) / 2 := by
    have hnat : 2 * (rpar n / 2) = rpar n := ts_two_mul_rpar_div_two n hk
    have hc : 2 * ((rpar n / 2 : ℕ) : ℝ) = (rpar n : ℝ) := by
      have := congrArg (fun m : ℕ => (m : ℝ)) hnat
      push_cast at this
      exact this
    linarith
  have hu1 : (Lpar n : ℝ) ≤ (upar n : ℝ) := by
    have := (uparfacts n).1
    exact_mod_cast this
  have hu2 : (upar n : ℝ) < (Lpar n : ℝ) + (Ffac : ℝ) * (Qall : ℝ) := by
    have h := (uparfacts n).2.1
    have h' : (upar n : ℝ) < ((Lpar n + Ffac * Qall : ℕ) : ℝ) := by exact_mod_cast h
    rw [Nat.cast_add, Nat.cast_mul] at h'
    exact h'
  have hLp_cast : (Lpar n : ℝ) = (((rpar n * (2*HvdH.D - 1)) / (4*HvdH.D) : ℕ) : ℝ) + 1 := by
    unfold Lpar; push_cast; ring
  have hxD_lt : ((2*HvdH.D-1 : ℕ) : ℝ) = 2*(HvdH.D:ℝ) - 1 := by
    rw [Nat.cast_sub (by decide : 1 ≤ 2*HvdH.D)]; push_cast; ring
  have he : ∀ m : ℕ, ((m * (2*HvdH.D-1) : ℕ) : ℝ) / ((4*HvdH.D : ℕ) : ℝ)
      = (m : ℝ) * (2*(HvdH.D:ℝ) - 1) / (4*(HvdH.D:ℝ)) := by
    intro m
    simp only [Nat.cast_mul, Nat.cast_ofNat, hxD_lt]
  have hxL : (rpar n : ℝ) * (2 * (HvdH.D:ℝ) - 1) / (4 * (HvdH.D:ℝ)) < (Lpar n : ℝ) := by
    have h := nat_div_lt_succ (rpar n * (2*HvdH.D - 1)) (4*HvdH.D)
    rw [hLp_cast]
    rw [he (rpar n)] at h
    exact h
  have hLx : (Lpar n : ℝ) ≤ (rpar n : ℝ) * (2 * (HvdH.D:ℝ) - 1) / (4 * (HvdH.D:ℝ)) + 1 := by
    have h := Nat.cast_div_le (α := ℝ) (m := rpar n * (2*HvdH.D-1)) (n := 4*HvdH.D)
    rw [hLp_cast]
    rw [he (rpar n)] at h
    linarith
  have h1r : 8 * (HvdH.D:ℝ) * ((Ffac:ℝ)*(Qall:ℝ) + (Ffac:ℝ)*(HvdH.D:ℝ) + 1) ≤ (rpar n:ℝ) := by
    exact_mod_cast h1
  have h2r : 4 * (HvdH.D:ℝ) * (1 + 2 * (Ffac:ℝ)*(Qall:ℝ) + 2 * (Ffac:ℝ)*(HvdH.D:ℝ)) ≤ (rpar n:ℝ) := by
    exact_mod_cast h2
  rcases Nat.lt_or_ge i (dpar n) with hlt | hge
  · simp only [hts, hss, hlt, ite_true]
    rw [hRhalf, Nat.cast_add, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    have hF : (0:ℝ) < (Ffac:ℝ) := Nat.cast_pos.mpr Ffac_pos
    have hx : (0:ℝ) ≤ (i:ℝ) + 1 := by
      have : (0:ℝ) ≤ (i:ℝ) := Nat.cast_nonneg i
      linarith
    have hxD : (i:ℝ) + 1 ≤ (HvdH.D:ℝ) := by
      have hle : i + 1 ≤ HvdH.D := Nat.succ_le_of_lt hi
      have hc : ((i+1 : ℕ):ℝ) ≤ (HvdH.D:ℝ) := Nat.cast_le.mpr hle
      rwa [Nat.cast_add, Nat.cast_one] at hc
    exact sswindow_lo (rpar n : ℝ) (Lpar n : ℝ) (upar n : ℝ) (Ffac:ℝ) (Qall:ℝ) ((i:ℝ)+1)
      hF hx hxD hxL hu1 hLx hu2 h1r
  · have hup1 : 1 ≤ upar n := upar_one_le n
    have hcast1 : ((2 * upar n - 1 : ℕ) : ℝ) = 2*(upar n:ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ 2 * upar n)]; push_cast; ring
    have hcast2 : ((i - dpar n + 1 : ℕ) : ℝ) = (i:ℝ) - (dpar n:ℝ) + 1 := by
      rw [Nat.cast_add, Nat.cast_sub hge, Nat.cast_one]
    have hcast3 : ((2 * upar n - 1 + 2 * Ffac * (i - dpar n + 1) : ℕ) : ℝ)
        = 2*(upar n:ℝ) - 1 + 2*(Ffac:ℝ)*((i:ℝ) - (dpar n:ℝ) + 1) := by
      rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul, hcast1, hcast2, Nat.cast_ofNat]
      try ring
    simp only [hts, hss, Nat.not_lt.mpr hge, ite_false]
    rw [hcast3]
    have hF : (1:ℝ) ≤ (Ffac:ℝ) := by exact_mod_cast Ffac_one_le
    have hy : (1:ℝ) ≤ (i:ℝ) - (dpar n:ℝ) + 1 := by
      have : (dpar n:ℝ) ≤ (i:ℝ) := by exact_mod_cast hge
      linarith
    have hyD : (i:ℝ) - (dpar n:ℝ) + 1 ≤ (HvdH.D:ℝ) := by
      have hleq : i - dpar n ≤ i := Nat.sub_le i (dpar n)
      have hc : ((i - dpar n : ℕ):ℝ) ≤ (i:ℝ) := by exact_mod_cast hleq
      rw [Nat.cast_sub hge] at hc
      have hle2 : i + 1 ≤ HvdH.D := Nat.succ_le_of_lt hi
      have hc2 : (i:ℝ) + 1 ≤ (HvdH.D:ℝ) := by
        have hc3 : ((i+1 : ℕ):ℝ) ≤ (HvdH.D:ℝ) := Nat.cast_le.mpr hle2
        rwa [Nat.cast_add, Nat.cast_one] at hc3
      linarith
    exact sswindow_hi (rpar n : ℝ) (Lpar n : ℝ) (upar n : ℝ) (Ffac:ℝ) (Qall:ℝ)
      ((i:ℝ) - (dpar n:ℝ) + 1) hF hy hyD hxL hu1 hLx hu2 h2r

end Work.Params
