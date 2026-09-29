import Mathlib
import Submission.Work.Cert.WLDefs
import Submission.Work.Cert.LeafChain
import Submission.Work.ANum3.Z2.floor_cmp
import Submission.Work.ANum3.Z2.cx_div_reim

/-! # The rounding error of the integer division `a/b` at scale `S`

For integers `ar ai br bi` with `gb20 br bi = ⌊(br²+bi²)/S⌋ > 0`, the mantissa pair
`(gxr0, gxi0)` (the floored parts of `(a·conj b)/gb20`) approximates `a/b` to within
`(2·⌊(|xr|+|xi|+2)/N⌋ + 4 + ETOL)/S`.  This is the third summand of `grx`
(`Submission/Work/Cert/WL/Defs.lean`) and is consumed by `wind_leaf_sound_impl`.

The proof: write `D = br²+bi² = S·N + u`, `Pr = ar·br+ai·bi = N·xr + ρ`,
`Pi = ai·br−ar·bi = N·xi + σ` with `0 ≤ u < S`, `0 ≤ ρ,σ < N`.  Then
`z.re = (S·ρ − xr·u)/(S·D)` and `z.im = (S·σ − xi·u)/(S·D)`, and
`|S·ρ − xr·u| ≤ S·(N + |xr|)`,
so `S·‖z‖ ≤ 2 + (|xr|+|xi|)/N ≤ 2·⌊(|xr|+|xi|+2)/N⌋ + 4 + ETOL` (the last step is
`floor_cmp`). -/

set_option maxHeartbeats 4000000

namespace Work.ANum3.Z2

open Work.Cert

theorem ratio_floor {ar ai br bi : ℤ} (hb2 : 0 < Work.Cert.WL.gb20 br bi) :
    ‖Work.Cert.cx ar ai / Work.Cert.cx br bi
        - Work.Cert.cx (Work.Cert.WL.gxr0 ar ai br bi) (Work.Cert.WL.gxi0 ar ai br bi)‖
      ≤ ((2 * Work.Cert.fdiv
            (Work.Cert.iabs (Work.Cert.WL.gxr0 ar ai br bi)
              + Work.Cert.iabs (Work.Cert.WL.gxi0 ar ai br bi) + 2)
            (Work.Cert.WL.gb20 br bi) + 4 + Work.Cert.ETOL : ℤ) : ℝ) / (Work.Cert.S : ℝ) := by
  set B2 : ℤ := br * br + bi * bi with hB2
  set N : ℤ := WL.gb20 br bi with hN
  set Pr : ℤ := ar * br + ai * bi with hPr
  set Pi : ℤ := ai * br - ar * bi with hPi
  set xr : ℤ := WL.gxr0 ar ai br bi with hxr
  set xi : ℤ := WL.gxi0 ar ai br bi with hxi
  have hNpos : 0 < N := hb2
  have hN_eq : N = B2 / S := by rw [hN, WL.gb20, ← hB2]; rfl
  have hxrN : xr = Pr / N := by rw [hxr, WL.gxr0, ← hPr, ← hN]; rfl
  have hxiN : xi = Pi / N := by rw [hxi, WL.gxi0, ← hPi, ← hN]; rfl
  have hB2pos : 0 < B2 := by
    have h := Int.ediv_mul_le B2 (b := S) S_ne
    rw [← hN_eq] at h
    have h1N : (1 : ℤ) ≤ N := by omega
    have h2 : (1 : ℤ) * S ≤ N * S := mul_le_mul_of_nonneg_right h1N (le_of_lt S_pos)
    linarith [h, h2, S_pos]
  have hB2pos' : 0 < br * br + bi * bi := by rw [← hB2]; exact hB2pos
  have hreim := cx_div_reim ar ai br bi hB2pos'
  have hre' : (cx ar ai / cx br bi).re = (Pr : ℝ) / (B2 : ℝ) := by
    have h := hreim.1
    rw [← hPr, ← hB2] at h
    exact h
  have him' : (cx ar ai / cx br bi).im = (Pi : ℝ) / (B2 : ℝ) := by
    have h := hreim.2
    rw [← hPi, ← hB2] at h
    exact h
  have hu : B2 = S * N + B2 % S := by
    have h := Int.mul_ediv_add_emod B2 S
    rw [← hN_eq] at h
    exact h.symm
  have hp_eq : Pr = N * xr + Pr % N := by
    have h := Int.mul_ediv_add_emod Pr N
    rw [← hxrN] at h
    exact h.symm
  have hi_eq : Pi = N * xi + Pi % N := by
    have h := Int.mul_ediv_add_emod Pi N
    rw [← hxiN] at h
    exact h.symm
  have hkeyr : S * Pr - xr * B2 = S * (Pr % N) - xr * (B2 % S) := by
    have h1 : S * Pr = S * (N * xr) + S * (Pr % N) := by
      conv_lhs => rw [hp_eq]
      ring
    have h2 : xr * B2 = xr * (S * N) + xr * (B2 % S) := by
      conv_lhs => rw [hu]
      ring
    rw [h1, h2]; ring
  have hkeyi : S * Pi - xi * B2 = S * (Pi % N) - xi * (B2 % S) := by
    have h1 : S * Pi = S * (N * xi) + S * (Pi % N) := by
      conv_lhs => rw [hi_eq]
      ring
    have h2 : xi * B2 = xi * (S * N) + xi * (B2 % S) := by
      conv_lhs => rw [hu]
      ring
    rw [h1, h2]; ring
  have hB2R : (0 : ℝ) < (B2 : ℝ) := by exact_mod_cast hB2pos
  have hNposR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
  have hSne : (S : ℝ) ≠ 0 := ne_of_gt S_posR
  have hB2ne : (B2 : ℝ) ≠ 0 := ne_of_gt hB2R
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNposR
  have hkeyR : (S : ℝ) * (Pr : ℝ) - (xr : ℝ) * (B2 : ℝ)
      = ((S * (Pr % N) - xr * (B2 % S) : ℤ) : ℝ) := by
    have h1 : (S : ℝ) * (Pr : ℝ) - (xr : ℝ) * (B2 : ℝ) = ((S * Pr - xr * B2 : ℤ) : ℝ) := by
      push_cast; ring
    have h2 : ((S * Pr - xr * B2 : ℤ) : ℝ) = ((S * (Pr % N) - xr * (B2 % S) : ℤ) : ℝ) := by
      exact_mod_cast hkeyr
    exact h1.trans h2
  have hkeyI : (S : ℝ) * (Pi : ℝ) - (xi : ℝ) * (B2 : ℝ)
      = ((S * (Pi % N) - xi * (B2 % S) : ℤ) : ℝ) := by
    have h1 : (S : ℝ) * (Pi : ℝ) - (xi : ℝ) * (B2 : ℝ) = ((S * Pi - xi * B2 : ℤ) : ℝ) := by
      push_cast; ring
    have h2 : ((S * Pi - xi * B2 : ℤ) : ℝ) = ((S * (Pi % N) - xi * (B2 % S) : ℤ) : ℝ) := by
      exact_mod_cast hkeyi
    exact h1.trans h2
  have hzre : (cx ar ai / cx br bi - cx xr xi).re
      = ((S * (Pr % N) - xr * (B2 % S) : ℤ) : ℝ) / ((S : ℝ) * (B2 : ℝ)) := by
    rw [Complex.sub_re, hre', cx_re, ← hkeyR]
    rw [div_sub_div (Pr : ℝ) (xr : ℝ) hB2ne hSne]
    ring
  have hzim : (cx ar ai / cx br bi - cx xr xi).im
      = ((S * (Pi % N) - xi * (B2 % S) : ℤ) : ℝ) / ((S : ℝ) * (B2 : ℝ)) := by
    rw [Complex.sub_im, him', cx_im, ← hkeyI]
    rw [div_sub_div (Pi : ℝ) (xi : ℝ) hB2ne hSne]
    ring
  have hnumr : |((S * (Pr % N) - xr * (B2 % S) : ℤ) : ℝ)| ≤ (S : ℝ) * ((N : ℝ) + |(xr : ℝ)|) := by
    have he : ((S * (Pr % N) - xr * (B2 % S) : ℤ) : ℝ)
        = (S : ℝ) * ((Pr % N : ℤ) : ℝ) - (xr : ℝ) * ((B2 % S : ℤ) : ℝ) := by
      push_cast; ring
    rw [he]
    have hs : |((Pr % N : ℤ) : ℝ)| ≤ (N : ℝ) := by
      rw [abs_of_nonneg (by exact_mod_cast Int.emod_nonneg Pr (ne_of_gt hNpos))]
      exact_mod_cast le_of_lt (Int.emod_lt_of_pos Pr hNpos)
    have hut : |((B2 % S : ℤ) : ℝ)| ≤ (S : ℝ) := by
      rw [abs_of_nonneg (by exact_mod_cast Int.emod_nonneg B2 S_ne)]
      exact_mod_cast le_of_lt (Int.emod_lt_of_pos B2 S_pos)
    have htri : |(S : ℝ) * ((Pr % N : ℤ) : ℝ) - (xr : ℝ) * ((B2 % S : ℤ) : ℝ)|
        ≤ |(S : ℝ) * ((Pr % N : ℤ) : ℝ)| + |(xr : ℝ) * ((B2 % S : ℤ) : ℝ)| := by
      simpa using abs_sub_le ((S : ℝ) * ((Pr % N : ℤ) : ℝ)) 0 ((xr : ℝ) * ((B2 % S : ℤ) : ℝ))
    calc |(S : ℝ) * ((Pr % N : ℤ) : ℝ) - (xr : ℝ) * ((B2 % S : ℤ) : ℝ)|
        ≤ |(S : ℝ) * ((Pr % N : ℤ) : ℝ)| + |(xr : ℝ) * ((B2 % S : ℤ) : ℝ)| := htri
      _ = (S : ℝ) * |((Pr % N : ℤ) : ℝ)| + |(xr : ℝ)| * |((B2 % S : ℤ) : ℝ)| := by
          rw [abs_mul, abs_mul, abs_of_pos S_posR]
      _ ≤ (S : ℝ) * (N : ℝ) + |(xr : ℝ)| * (S : ℝ) :=
          add_le_add (mul_le_mul_of_nonneg_left hs (le_of_lt S_posR))
            (mul_le_mul_of_nonneg_left hut (abs_nonneg _))
      _ = (S : ℝ) * ((N : ℝ) + |(xr : ℝ)|) := by ring
  have hnumi : |((S * (Pi % N) - xi * (B2 % S) : ℤ) : ℝ)| ≤ (S : ℝ) * ((N : ℝ) + |(xi : ℝ)|) := by
    have he : ((S * (Pi % N) - xi * (B2 % S) : ℤ) : ℝ)
        = (S : ℝ) * ((Pi % N : ℤ) : ℝ) - (xi : ℝ) * ((B2 % S : ℤ) : ℝ) := by
      push_cast; ring
    rw [he]
    have hs : |((Pi % N : ℤ) : ℝ)| ≤ (N : ℝ) := by
      rw [abs_of_nonneg (by exact_mod_cast Int.emod_nonneg Pi (ne_of_gt hNpos))]
      exact_mod_cast le_of_lt (Int.emod_lt_of_pos Pi hNpos)
    have hut : |((B2 % S : ℤ) : ℝ)| ≤ (S : ℝ) := by
      rw [abs_of_nonneg (by exact_mod_cast Int.emod_nonneg B2 S_ne)]
      exact_mod_cast le_of_lt (Int.emod_lt_of_pos B2 S_pos)
    have htri : |(S : ℝ) * ((Pi % N : ℤ) : ℝ) - (xi : ℝ) * ((B2 % S : ℤ) : ℝ)|
        ≤ |(S : ℝ) * ((Pi % N : ℤ) : ℝ)| + |(xi : ℝ) * ((B2 % S : ℤ) : ℝ)| := by
      simpa using abs_sub_le ((S : ℝ) * ((Pi % N : ℤ) : ℝ)) 0 ((xi : ℝ) * ((B2 % S : ℤ) : ℝ))
    calc |(S : ℝ) * ((Pi % N : ℤ) : ℝ) - (xi : ℝ) * ((B2 % S : ℤ) : ℝ)|
        ≤ |(S : ℝ) * ((Pi % N : ℤ) : ℝ)| + |(xi : ℝ) * ((B2 % S : ℤ) : ℝ)| := htri
      _ = (S : ℝ) * |((Pi % N : ℤ) : ℝ)| + |(xi : ℝ)| * |((B2 % S : ℤ) : ℝ)| := by
          rw [abs_mul, abs_mul, abs_of_pos S_posR]
      _ ≤ (S : ℝ) * (N : ℝ) + |(xi : ℝ)| * (S : ℝ) :=
          add_le_add (mul_le_mul_of_nonneg_left hs (le_of_lt S_posR))
            (mul_le_mul_of_nonneg_left hut (abs_nonneg _))
      _ = (S : ℝ) * ((N : ℝ) + |(xi : ℝ)|) := by ring
  have hNS : (N : ℝ) * (S : ℝ) ≤ (B2 : ℝ) := by
    have h := congrArg (fun z : ℤ => (z : ℝ)) hu
    push_cast at h
    have hnn : (0 : ℝ) ≤ ((B2 % S : ℤ) : ℝ) := by exact_mod_cast Int.emod_nonneg B2 S_ne
    linarith
  have hzre_bound : |(cx ar ai / cx br bi - cx xr xi).re| ≤ (1 + |(xr : ℝ)| / (N : ℝ)) / (S : ℝ) := by
    have h1 : |(cx ar ai / cx br bi - cx xr xi).re|
        = |((S * (Pr % N) - xr * (B2 % S) : ℤ) : ℝ)| / ((S : ℝ) * (B2 : ℝ)) := by
      rw [hzre, abs_div, abs_of_pos (mul_pos S_posR hB2R)]
    rw [h1]
    calc |((S * (Pr % N) - xr * (B2 % S) : ℤ) : ℝ)| / ((S : ℝ) * (B2 : ℝ))
        ≤ (S : ℝ) * ((N : ℝ) + |(xr : ℝ)|) / ((S : ℝ) * (B2 : ℝ)) :=
          div_le_div_of_nonneg_right hnumr (le_of_lt (mul_pos S_posR hB2R))
      _ = ((N : ℝ) + |(xr : ℝ)|) / (B2 : ℝ) := by
          rw [div_eq_div_iff (mul_ne_zero hSne hB2ne) hB2ne]; ring
      _ ≤ ((N : ℝ) + |(xr : ℝ)|) / ((N : ℝ) * (S : ℝ)) :=
          div_le_div_of_nonneg_left (add_nonneg (le_of_lt hNposR) (abs_nonneg _))
            (mul_pos hNposR S_posR) hNS
      _ = (1 + |(xr : ℝ)| / (N : ℝ)) / (S : ℝ) := by
          rw [div_eq_div_iff (mul_ne_zero hNne hSne) hSne]
          field_simp
  have hzim_bound : |(cx ar ai / cx br bi - cx xr xi).im| ≤ (1 + |(xi : ℝ)| / (N : ℝ)) / (S : ℝ) := by
    have h1 : |(cx ar ai / cx br bi - cx xr xi).im|
        = |((S * (Pi % N) - xi * (B2 % S) : ℤ) : ℝ)| / ((S : ℝ) * (B2 : ℝ)) := by
      rw [hzim, abs_div, abs_of_pos (mul_pos S_posR hB2R)]
    rw [h1]
    calc |((S * (Pi % N) - xi * (B2 % S) : ℤ) : ℝ)| / ((S : ℝ) * (B2 : ℝ))
        ≤ (S : ℝ) * ((N : ℝ) + |(xi : ℝ)|) / ((S : ℝ) * (B2 : ℝ)) :=
          div_le_div_of_nonneg_right hnumi (le_of_lt (mul_pos S_posR hB2R))
      _ = ((N : ℝ) + |(xi : ℝ)|) / (B2 : ℝ) := by
          rw [div_eq_div_iff (mul_ne_zero hSne hB2ne) hB2ne]; ring
      _ ≤ ((N : ℝ) + |(xi : ℝ)|) / ((N : ℝ) * (S : ℝ)) :=
          div_le_div_of_nonneg_left (add_nonneg (le_of_lt hNposR) (abs_nonneg _))
            (mul_pos hNposR S_posR) hNS
      _ = (1 + |(xi : ℝ)| / (N : ℝ)) / (S : ℝ) := by
          rw [div_eq_div_iff (mul_ne_zero hNne hSne) hSne]
          field_simp
  have hz : ‖cx ar ai / cx br bi - cx xr xi‖
      ≤ (2 + ((|(xr : ℝ)| + |(xi : ℝ)|) / (N : ℝ))) / (S : ℝ) := by
    have h1 := Complex.norm_le_abs_re_add_abs_im (cx ar ai / cx br bi - cx xr xi)
    have h2 := add_le_add hzre_bound hzim_bound
    refine le_trans h1 (le_trans h2 ?_)
    rw [← add_div]
    apply div_le_div_of_nonneg_right _ (le_of_lt S_posR)
    rw [add_div]
    linarith
  have hS' : (S : ℝ) * ‖cx ar ai / cx br bi - cx xr xi‖
      ≤ 2 + ((|(xr : ℝ)| + |(xi : ℝ)|) / (N : ℝ)) := by
    have h := mul_le_mul_of_nonneg_left hz (le_of_lt S_posR)
    rwa [mul_div_cancel₀ _ (ne_of_gt S_posR)] at h
  have hfl : 2 + ((|(xr : ℝ)| + |(xi : ℝ)|) / (N : ℝ))
      ≤ 2 * ((fdiv (iabs xr + iabs xi + 2) N : ℤ) : ℝ) + 4 + (ETOL : ℝ) := by
    have h := floor_cmp xr xi N hNpos
    rwa [show ((iabs xr + iabs xi : ℤ) : ℝ) = |(xr : ℝ)| + |(xi : ℝ)| by
      push_cast; rw [iabs_abs, iabs_abs]] at h
  have hfin : (S : ℝ) * ‖cx ar ai / cx br bi - cx xr xi‖
      ≤ ((2 * fdiv (iabs xr + iabs xi + 2) N + 4 + ETOL : ℤ) : ℝ) := by
    have hc : ((2 * fdiv (iabs xr + iabs xi + 2) N + 4 + ETOL : ℤ) : ℝ)
        = 2 * ((fdiv (iabs xr + iabs xi + 2) N : ℤ) : ℝ) + 4 + (ETOL : ℝ) := by
      push_cast; ring
    rw [hc]; linarith
  rw [le_div_iff₀ S_posR]
  linarith [hfin]


end Work.ANum3.Z2
