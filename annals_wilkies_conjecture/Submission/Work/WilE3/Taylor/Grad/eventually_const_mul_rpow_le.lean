import Mathlib

namespace Work.WilE3.Taylor.Grad

theorem eventually_const_mul_rpow_le {G g : ℝ → ℝ} {κ c : ℝ} {m : ℕ}
    (hg : ContinuousAt g 0) (hg0 : g 0 ≠ 0)
    (hGg : G =ᶠ[nhds (0:ℝ)] fun t => t ^ m * g t) (hc : 0 < c) (hκ : 0 ≤ κ) :
    ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      c * (|g 0| / 2) ^ κ * (t ^ m) ^ κ ≤ c * |G t| ^ κ := by
  have hgpos : 0 < |g 0| := abs_pos.mpr hg0
  have hhalf : 0 < |g 0| / 2 := by linarith
  -- continuity of `g` at `0` gives an eventual lower bound `|g 0| / 2 ≤ |g t|`.
  have htend : Filter.Tendsto (fun t : ℝ => |g t|) (nhds 0) (nhds (|g 0|)) := by
    simpa [Function.comp_def] using (continuous_abs.continuousAt.comp hg).tendsto
  have hev_g : ∀ᶠ t in nhds (0:ℝ), |g 0| / 2 ≤ |g t| := by
    have hU : Set.Ioi (|g 0| / 2) ∈ nhds (|g 0|) :=
      IsOpen.mem_nhds isOpen_Ioi (by simp only [Set.mem_Ioi]; linarith)
    have hlt : ∀ᶠ t in nhds (0:ℝ), |g 0| / 2 < |g t| := htend.eventually hU
    exact hlt.mono (fun t h => le_of_lt h)
  -- and `G` agrees with `t ^ m * g t` near `0`.
  have hev_eq : ∀ᶠ t in nhds (0:ℝ), G t = t ^ m * g t := hGg
  have hev : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0),
      |g 0| / 2 ≤ |g t| ∧ G t = t ^ m * g t :=
    (hev_g.and hev_eq).filter_mono nhdsWithin_le_nhds
  refine (hev.and self_mem_nhdsWithin).mono ?_
  rintro t ⟨⟨hgt, hGt⟩, htpos⟩
  have ht0 : (0:ℝ) < t := htpos
  have hpow_t : (0:ℝ) ≤ t ^ m := pow_nonneg (le_of_lt ht0) m
  have hhalf_nonneg : 0 ≤ |g 0| / 2 := le_of_lt hhalf
  -- `|G t| = t ^ m * |g t|` for `t > 0`.
  have hGr : |G t| = t ^ m * |g t| := by
    rw [hGt, abs_mul, abs_of_nonneg hpow_t]
  have hkG : |G t| ^ κ = (t ^ m) ^ κ * |g t| ^ κ := by
    rw [hGr, Real.mul_rpow hpow_t (abs_nonneg _)]
  -- monotonicity of `· ^ κ` for `κ ≥ 0`.
  have h1 : (|g 0| / 2) ^ κ ≤ |g t| ^ κ := Real.rpow_le_rpow hhalf_nonneg hgt hκ
  have h2 : (t ^ m) ^ κ * (|g 0| / 2) ^ κ ≤ (t ^ m) ^ κ * |g t| ^ κ :=
    mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hpow_t κ)
  rw [hkG]
  calc c * (|g 0| / 2) ^ κ * (t ^ m) ^ κ
      = c * ((t ^ m) ^ κ * (|g 0| / 2) ^ κ) := by ring
    _ ≤ c * ((t ^ m) ^ κ * |g t| ^ κ) := mul_le_mul_of_nonneg_left h2 (le_of_lt hc)

end Work.WilE3.Taylor.Grad
