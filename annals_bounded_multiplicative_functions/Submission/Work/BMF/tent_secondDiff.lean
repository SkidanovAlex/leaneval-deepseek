import Mathlib
import Submission.Work.BMF.tent_fourier_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The tent function is the discrete second difference of `phiR`

For `0 < B ≤ 1/2` the tent (hat) function `tent B x = max (1 - nint x / B) 0` can be written as

`tent B x = B + (1 / (2 * B)) * (2 * phiR x - phiR (x + B) - phiR (x - B))`,

where `phiR t = {t}^2 - {t} + 1/6` is the (`1`-periodic) Bernoulli polynomial of degree two.

This is the exact finite-difference identity behind the Fourier expansion of the tent, and it is
the reason the second derivative of `phiR` (a `1`-periodic "sawtooth" distribution) reproduces the
tent kernel.
-/

namespace Work.BMF

/-- `Int.fract t = t` on `[0, 1)`. -/
lemma tent_secondDiff_fract_self {t : ℝ} (h0 : 0 ≤ t) (h1 : t < 1) : Int.fract t = t :=
  Int.fract_eq_self.mpr ⟨h0, h1⟩

/-- `Int.fract t = t - 1` on `[1, 2)`. -/
lemma tent_secondDiff_fract_sub_one {t : ℝ} (h0 : 1 ≤ t) (h1 : t < 2) :
    Int.fract t = t - 1 := by
  have h : Int.fract (t - 1) = t - 1 := tent_secondDiff_fract_self (by linarith) (by linarith)
  have h2 := Int.fract_sub_intCast t 1
  simp only [Int.cast_one] at h2
  rw [← h2]
  exact h

/-- `Int.fract t = t + 1` on `(-1, 0)`. -/
lemma tent_secondDiff_fract_add_one {t : ℝ} (h0 : -1 < t) (h1 : t < 0) :
    Int.fract t = t + 1 := by
  have h : Int.fract (t + 1) = t + 1 := tent_secondDiff_fract_self (by linarith) (by linarith)
  have h2 := Int.fract_add_intCast t 1
  simp only [Int.cast_one] at h2
  rw [← h2]
  exact h

/-- On `[0, 1)`, `phiR t = t^2 - t + 1/6`. -/
lemma tent_secondDiff_phiR_mem {t : ℝ} (h0 : 0 ≤ t) (h1 : t < 1) :
    phiR t = t ^ 2 - t + 1 / 6 := by
  unfold phiR; rw [tent_secondDiff_fract_self h0 h1]

/-- On `[1, 2)`, `phiR t = (t - 1)^2 - (t - 1) + 1/6`. -/
lemma tent_secondDiff_phiR_sub_one {t : ℝ} (h0 : 1 ≤ t) (h1 : t < 2) :
    phiR t = (t - 1) ^ 2 - (t - 1) + 1 / 6 := by
  unfold phiR; rw [tent_secondDiff_fract_sub_one h0 h1]

/-- On `(-1, 0)`, `phiR t = (t + 1)^2 - (t + 1) + 1/6`. -/
lemma tent_secondDiff_phiR_add_one {t : ℝ} (h0 : -1 < t) (h1 : t < 0) :
    phiR t = (t + 1) ^ 2 - (t + 1) + 1 / 6 := by
  unfold phiR; rw [tent_secondDiff_fract_add_one h0 h1]

/-- `phiR` is `1`-periodic, hence invariant under addition of integers. -/
lemma tent_secondDiff_phiR_add_intCast (t : ℝ) (n : ℤ) : phiR (t + n) = phiR t := by
  unfold phiR; rw [Int.fract_add_intCast]

/-- For `0 < B ≤ 1/2` the tent of width `B` is the centred second difference of `phiR`:
`tent B x = B + (1/(2B)) · (2 φ(x) - φ(x+B) - φ(x-B))`. -/
theorem tent_secondDiff (B x : ℝ) (hB : 0 < B) (hB2 : B ≤ 1 / 2) :
    tent B x = B + (1 / (2 * B)) * (2 * phiR x - phiR (x + B) - phiR (x - B)) := by
  -- Reduce everything to `a = Int.fract x ∈ [0,1)` using the periodicity of `phiR`.
  set a : ℝ := Int.fract x with ha
  have ha0 : 0 ≤ a := by rw [ha]; exact Int.fract_nonneg x
  have ha1 : a < 1 := by rw [ha]; exact Int.fract_lt_one x
  have hx1 : x = a + (⌊x⌋ : ℝ) := by
    rw [ha]; exact (Int.fract_add_floor x).symm
  have hfx : phiR x = phiR a := by rw [hx1, tent_secondDiff_phiR_add_intCast]
  have hfxB : phiR (x + B) = phiR (a + B) := by
    have hh : x + B = (a + B) + (⌊x⌋ : ℝ) := by linarith [hx1]
    rw [hh, tent_secondDiff_phiR_add_intCast]
  have hfxmB : phiR (x - B) = phiR (a - B) := by
    have hh : x - B = (a - B) + (⌊x⌋ : ℝ) := by linarith [hx1]
    rw [hh, tent_secondDiff_phiR_add_intCast]
  have h1 : nint x = min a (1 - a) := by rw [nint_eq_min_fract, ← ha]
  have htent : tent B x = max (1 - min a (1 - a) / B) 0 := by
    unfold tent; rw [h1]
  rw [htent, hfx, hfxB, hfxmB]
  -- Three regimes: `a < B`, `B ≤ a ≤ 1-B`, and `a ≥ 1-B`.
  rcases lt_or_ge (a + B) 1 with hAB | hAB
  · have hU : phiR (a + B) = (a + B) ^ 2 - (a + B) + 1 / 6 :=
      tent_secondDiff_phiR_mem (by linarith) hAB
    rcases lt_or_ge a B with hlt | hge
    · -- `a < B` (and `a + B < 1`): the tent is `1 - a/B`.
      have hD : phiR (a - B) = (a - B + 1) ^ 2 - (a - B + 1) + 1 / 6 :=
        tent_secondDiff_phiR_add_one (by linarith [ha0, hB2]) (by linarith)
      have hmin : min a (1 - a) = a := min_eq_left (by linarith [hlt, hB2])
      have hmax : max (1 - a / B) 0 = 1 - a / B :=
        max_eq_left (by rw [sub_nonneg, div_le_one hB]; linarith)
      rw [hmin, hmax, tent_secondDiff_phiR_mem ha0 ha1, hU, hD]
      field_simp
      ring
    · -- `B ≤ a` and `a + B < 1`: the tent vanishes.
      have hD : phiR (a - B) = (a - B) ^ 2 - (a - B) + 1 / 6 :=
        tent_secondDiff_phiR_mem (by linarith) (by linarith)
      have hmax : max (1 - min a (1 - a) / B) 0 = 0 := by
        rw [max_eq_right]
        rw [sub_nonpos, one_le_div hB]
        exact le_min hge (by linarith)
      rw [hmax, tent_secondDiff_phiR_mem ha0 ha1, hU, hD]
      field_simp
      ring
  · -- `1 ≤ a + B`, i.e. `a ≥ 1 - B`: the tent is `1 - (1-a)/B`.
    have hU : phiR (a + B) = (a + B - 1) ^ 2 - (a + B - 1) + 1 / 6 :=
      tent_secondDiff_phiR_sub_one hAB (by linarith)
    have hD : phiR (a - B) = (a - B) ^ 2 - (a - B) + 1 / 6 :=
      tent_secondDiff_phiR_mem (by linarith) (by linarith)
    have hmin : min a (1 - a) = 1 - a := min_eq_right (by linarith [hAB, hB2])
    have hmax : max (1 - (1 - a) / B) 0 = 1 - (1 - a) / B :=
      max_eq_left (by rw [sub_nonneg, div_le_one hB]; linarith)
    rw [hmin, hmax, tent_secondDiff_phiR_mem ha0 ha1, hU, hD]
    field_simp
    ring

end Work.BMF
