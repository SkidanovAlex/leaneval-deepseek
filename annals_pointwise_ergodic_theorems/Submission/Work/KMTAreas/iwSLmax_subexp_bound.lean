import Mathlib
import Submission.Work.KMTAreas.iwSL
import Submission.Work.KMTAreas.logb_iwQ0_le

/-!
# The sub-exponential bound for the Tao denominator bound `iwSLmax`

`iwSLmax ρ l = max Q_0^{(l)} (2^{l D_ρ})` is the sharp upper bound for the elements of the Tao
denominator set `S_l` of Appendix A of Krause–Mirek–Tao (see `Submission/Work/KMTAreas/iwSL.lean`).
The present lemma is the **numeric input consumed by the IW multiplier theorem**: it shows

  `iwSLmax ρ l ≤ 2^{D_ρ (2+ρ)(l+1) 2^{ρl/2}}`,

i.e. `log₂ (iwSLmax ρ l) ≲_ρ l · 2^{ρl/2}` — *sub-exponential* in `2^l` (the competing, weaker
bound of `iwQ0_le` gives the exponent `O(2^{ρl})`, which is useless for quantifying over the good
major arcs `k ≤ -C_ρ 2^{ρl}`).

Both branches of the `max` are handled:

* the power branch `2^{l D_ρ}` is immediate, since `l ≤ (2+ρ)(l+1) 2^{ρl/2}`;
* the factorial branch is `logb 2 (Q_0^{(l)}) ≤ D_ρ (2+ρ)(l+1) 2^{ρl/2}`, proved in
  `Submission/Work/KMTAreas/logb_iwQ0_le.lean` from `N_0^{(l)} ≤ 2·2^{ρl/2}` and `log N ≤ N - 1`.

The conversion from the logarithmic bound to the exponential one is the elementary equivalence
`Real.logb_le_iff_le_rpow` for the base `2 > 1`.
-/

set_option autoImplicit false

namespace Work.KMTAreas

open Work.Analysis.IonescuWainger

theorem iwSLmax_subexp_bound (ρ : ℝ) (hρ : 0 < ρ) (l : ℕ) :
    ((Work.KMTAreas.iwSLmax ρ l : ℕ) : ℝ) ≤
      (2 : ℝ) ^ (((Work.Analysis.IonescuWainger.iwD ρ : ℕ) : ℝ) * (2 + ρ) *
        ((l : ℝ) + 1) * (2 : ℝ) ^ (ρ * (l : ℝ) / 2)) := by
  set E : ℝ := ((iwD ρ : ℕ) : ℝ) * (2 + ρ) * ((l : ℝ) + 1) *
        (2 : ℝ) ^ (ρ * (l : ℝ) / 2) with hEdef
  set s : ℝ := (2 : ℝ) ^ (ρ * (l : ℝ) / 2) with hsdef
  -- `s = 2^{ρl/2} ≥ 1`
  have hs1 : (1 : ℝ) ≤ s := by
    rw [hsdef]
    exact Real.one_le_rpow (by norm_num) (by positivity)
  have hspos : 0 < s := by linarith
  -- the factorial branch `Q_0^{(l)} ≤ 2^E`
  have hQ0pos : 0 < ((iwQ0 ρ l : ℕ) : ℝ) := by
    have : 0 < iwQ0 ρ l := by rw [iwQ0]; exact pow_pos (Nat.factorial_pos _) _
    exact_mod_cast this
  have hQ : ((iwQ0 ρ l : ℕ) : ℝ) ≤ (2 : ℝ) ^ E := by
    have h := logb_iwQ0_le ρ hρ l
    rw [hEdef]
    exact (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) hQ0pos).mp h
  -- the power branch `2^{l D_ρ} ≤ 2^E`, via `l ≤ (2+ρ)(l+1) s`
  have hbase : (2 : ℝ) ≤ (2 + ρ) * s := by
    have h2 : (0 : ℝ) ≤ 2 + ρ := by linarith
    have h3 : 2 + ρ ≤ (2 + ρ) * s := by
      have := mul_le_mul_of_nonneg_left hs1 h2
      simpa using this
    linarith [h3, hρ]
  have hmain : (l : ℝ) ≤ (2 + ρ) * ((l : ℝ) + 1) * s := by
    have h1 : (2 : ℝ) * ((l : ℝ) + 1) ≤ ((2 + ρ) * s) * ((l : ℝ) + 1) :=
      mul_le_mul hbase le_rfl (by positivity) (by positivity)
    have h2 : ((2 + ρ) * s) * ((l : ℝ) + 1) = (2 + ρ) * ((l : ℝ) + 1) * s := by ring
    rw [h2] at h1
    linarith [h1, Nat.cast_nonneg (α := ℝ) l]
  have hDnn : (0 : ℝ) ≤ (iwD ρ : ℝ) := by positivity
  have hkey : (l : ℝ) * (iwD ρ : ℝ) ≤ E := by
    have h3 := mul_le_mul_of_nonneg_left hmain hDnn
    rw [hEdef]
    calc (l : ℝ) * (iwD ρ : ℝ) = (iwD ρ : ℝ) * (l : ℝ) := by ring
      _ ≤ (iwD ρ : ℝ) * ((2 + ρ) * ((l : ℝ) + 1) * s) := h3
      _ = (iwD ρ : ℝ) * (2 + ρ) * ((l : ℝ) + 1) * s := by ring
  have hP : ((2 ^ (l * iwD ρ) : ℕ) : ℝ) ≤ (2 : ℝ) ^ E := by
    have hcast : ((2 ^ (l * iwD ρ) : ℕ) : ℝ) = (2 : ℝ) ^ (((l * iwD ρ : ℕ)) : ℝ) := by
      simp only [Nat.cast_pow, Nat.cast_ofNat, Real.rpow_natCast]
    rw [hcast]
    refine (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mpr ?_
    rw [Nat.cast_mul]
    exact hkey
  -- assemble the maximum
  have hmaxcast : ((iwSLmax ρ l : ℕ) : ℝ) =
      max ((iwQ0 ρ l : ℕ) : ℝ) (((2 ^ (l * iwD ρ) : ℕ)) : ℝ) := by
    rw [iwSLmax, Nat.cast_max]
  rw [hmaxcast]
  exact max_le hQ hP

end Work.KMTAreas
