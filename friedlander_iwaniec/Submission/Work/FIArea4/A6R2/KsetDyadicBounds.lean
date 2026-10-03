import Mathlib
import Submission.Work.S15crux.prelude
import Submission.Work.FIArea4.S15cutDefs

namespace Work.FIArea4.A6R2

/-- **The dyadic window of the stratum scales.**  Every scale `k ∈ kset Pa X j e` (i.e.
`k = dk d'` for some `d'` with `1 ≤ d' ≤ Y/e` and `X < e d'`, `Y = S15Y Pa X j`) satisfies

* `2^k < 4Y/e` (the scales do not exceed the stratum length),
* `2^k ≥ 2X/e` (the filter `X < e d'` forces a lower bound), and
* `k ≤ log₂(4Y)` (the scales lie in the range summed by `ksetBracketSum_le`).

This is the elementary input to the geometric summation of the Proposition 14.1 bracket over the
dyadic scales occurring in the stratum. -/
theorem KsetDyadicBounds (Pa : Work.FITop.Params) (X j e : ℕ) (hX : 1 ≤ X) (he : 1 ≤ e)
    {k : ℕ} (hk : k ∈ Work.S15crux.kset Pa X j e) :
    (2:ℝ)^k < 4 * ((Work.FIArea4.S15Y Pa X j : ℝ) / (e : ℝ))
      ∧ 2 * ((X : ℝ) / (e : ℝ)) ≤ (2:ℝ)^k
      ∧ k ≤ Nat.log 2 (4 * Work.FIArea4.S15Y Pa X j) := by
  -- unfold the membership in the image `kset = dset.image dk`
  rw [Work.S15crux.kset, Finset.mem_image] at hk
  obtain ⟨d', hd', hkd⟩ := hk
  -- unfold the membership in the filtered interval `dset`
  rw [Work.S15crux.dset, Finset.mem_filter, Finset.mem_Icc] at hd'
  obtain ⟨⟨hd1, hdY⟩, hdX⟩ := hd'
  rw [← hkd]
  obtain ⟨hlo, hhi⟩ := Work.S15crux.dk_spec hd1
  have he0 : 0 < e := by omega
  have heR : (0:ℝ) < (e:ℝ) := by exact_mod_cast he0
  -- `e * d' ≤ Y` and hence `d' ≤ Y`
  have hedY : e * d' ≤ Work.FIArea4.S15Y Pa X j :=
    le_trans (Nat.mul_le_mul_left e hdY) (Nat.mul_div_le _ _)
  have hdY' : d' ≤ Work.FIArea4.S15Y Pa X j := by
    refine le_trans ?_ hedY
    calc d' = 1 * d' := by ring
      _ ≤ e * d' := Nat.mul_le_mul_right d' he
  refine ⟨?_, ?_, ?_⟩
  · -- `2^k < 4 d' ≤ 4 Y / e`
    have hloR : ((2 ^ Work.S15crux.dk d' : ℕ) : ℝ) < ((4 * d' : ℕ) : ℝ) := by
      exact_mod_cast hlo
    have hstep : ((4 * d' : ℕ) : ℝ) ≤ 4 * ((Work.FIArea4.S15Y Pa X j : ℝ) / (e:ℝ)) := by
      have hd'R : (d' : ℝ) ≤ (Work.FIArea4.S15Y Pa X j : ℝ) / (e:ℝ) := by
        rw [le_div_iff₀ heR]
        have hR : (e:ℝ) * (d':ℝ) ≤ (Work.FIArea4.S15Y Pa X j : ℝ) := by exact_mod_cast hedY
        nlinarith [hR]
      have hcast : ((4 * d' : ℕ) : ℝ) = 4 * (d' : ℝ) := by push_cast; ring
      rw [hcast]
      linarith
    calc (2:ℝ) ^ Work.S15crux.dk d' = ((2 ^ Work.S15crux.dk d' : ℕ) : ℝ) := by push_cast; ring
      _ < ((4 * d' : ℕ) : ℝ) := hloR
      _ ≤ 4 * ((Work.FIArea4.S15Y Pa X j : ℝ) / (e:ℝ)) := hstep
  · -- `2^k ≥ 2 d' ≥ 2 X / e`
    have hnat : 2 * d' ≤ 2 ^ Work.S15crux.dk d' := by
      rw [Nat.pow_succ] at hhi
      omega
    have hkey : 2 * X ≤ e * (2 ^ Work.S15crux.dk d') := by
      have hXe : X ≤ e * d' := by omega
      calc 2 * X ≤ 2 * (e * d') := Nat.mul_le_mul_left 2 hXe
        _ = e * (2 * d') := by ring
        _ ≤ e * (2 ^ Work.S15crux.dk d') := Nat.mul_le_mul_left e hnat
    have hkeyR : (2:ℝ) * (X:ℝ) ≤ (e:ℝ) * (2:ℝ) ^ Work.S15crux.dk d' := by
      exact_mod_cast hkey
    have h2 : 2 * ((X:ℝ)/(e:ℝ)) = (2*(X:ℝ))/(e:ℝ) := by ring
    rw [h2, div_le_iff₀ heR]
    nlinarith [hkeyR]
  · -- `k ≤ log₂ (4 Y)`
    apply Nat.log_mono_right
    omega

end Work.FIArea4.A6R2
