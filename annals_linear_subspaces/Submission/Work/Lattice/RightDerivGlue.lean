import Mathlib
import Submission.Work.Lattice.GoodTime

/-!
# Glue between the good-time predicate and one-sided derivatives

`Submission.GoodTime.HasLocalSlopeGe E t c` is the differentiability-free form of "the right slope
of `E` at `t` is at least `−c`".  When the right derivative *does* exist (for the §3 energy
`E(t) = ∑ᵢ Λᵢ(t)²` this comes from the local affine structure of the Grayson data along the flow),
the two are equivalent and the derivative value is exactly the quantity `⟨ċ_t, c_t⟩` of Lemma 4:

* `le_of_hasLocalSlopeGe_of_hasDerivWithinAt`: from `HasLocalSlopeGe E t c` and
  `HasDerivWithinAt E D (Ici t) t` conclude `−c ≤ D`.

Module `Submission.Work.Lattice.RightDerivGlue`, namespace `Submission.GoodTime`.
-/

noncomputable section

open Set Filter
open scoped Topology
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Submission.GoodTime

/-- **The good-time predicate bounds the right derivative.**  If `E` does not decrease faster than
slope `c` to the right of `t`, and its right derivative at `t` exists with value `D`, then
`−c ≤ D`. -/
theorem le_of_hasLocalSlopeGe_of_hasDerivWithinAt {E : ℝ → ℝ} {t c D : ℝ}
    (h : HasLocalSlopeGe E t c) (hd : HasDerivWithinAt E D (Set.Ici t) t) : -c ≤ D := by
  obtain ⟨ε, hε, hloc⟩ := h
  have hset : Set.Ici t \ {t} = Set.Ioi t := by
    ext s
    simp only [Set.mem_sdiff, Set.mem_Ici, Set.mem_singleton_iff, Set.mem_Ioi]
    exact ⟨fun h => lt_of_le_of_ne h.1 (Ne.symm h.2), fun h => ⟨le_of_lt h, ne_of_gt h⟩⟩
  have hslope : Tendsto (slope E t) (𝓝[>] t) (𝓝 D) := by
    have h1 : Tendsto (slope E t) (𝓝[Set.Ici t \ {t}] t) (𝓝 D) :=
      (hasDerivWithinAt_iff_tendsto_slope).mp hd
    rwa [hset] at h1
  have hmap : Tendsto (fun s : ℝ => t + s) (𝓝[>] (0 : ℝ)) (𝓝[>] t) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨tendsto_nhdsWithin_of_tendsto_nhds ?_, ?_⟩
    · simpa using (tendsto_const_nhds.add tendsto_id :
        Tendsto (fun s : ℝ => t + s) (𝓝 0) (𝓝 (t + 0)))
    · filter_upwards [self_mem_nhdsWithin] with s hs
      simpa using hs
  have hquot : Tendsto (fun s : ℝ => (E (t + s) - E t) / s) (𝓝[>] (0 : ℝ)) (𝓝 D) := by
    have h1 : Tendsto (fun s : ℝ => slope E t (t + s)) (𝓝[>] (0 : ℝ)) (𝓝 D) := by
      simpa only [Function.comp_def] using hslope.comp hmap
    simpa [slope, vsub_eq_sub, smul_eq_mul, div_eq_inv_mul, mul_comm] using h1
  have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), -c ≤ (E (t + s) - E t) / s := by
    have h1 : ∀ᶠ s in 𝓝[>] (0 : ℝ), s < ε :=
      (eventually_lt_nhds hε).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, h1] with s hs0 hsε
    have hs0' : (0 : ℝ) < s := hs0
    have hts : t + s ∈ Set.Icc t (t + ε) := ⟨by linarith, by linarith⟩
    have h2 := hloc (t + s) hts
    have h3 : (-c * s) / s ≤ (E (t + s) - E t) / s := by
      apply div_le_div_of_nonneg_right _ hs0'.le
      linarith
    rwa [mul_div_cancel_right₀ (-c) (ne_of_gt hs0')] at h3
  exact ge_of_tendsto hquot hev

end Submission.GoodTime
