/-
Copyright: work module for the Elgindi finite-time singularity project.

# The pointwise factor bound `|(z+1)^m ∂_z^m D_θ^i f| ≤ |f|_𝒲 · Φ_i(θ)`

Elgindi's 𝒲^{4,∞}-estimates repeatedly need to move the radial weight `(z+1)^m`
across a `D_θ`-iterate: after extracting the unweighted bound
`|∂_z^m D_θ^i f| ≤ |f|_𝒲 (1+z)^{-m} Φ_i(θ)` the factor `(1+z)^m` cancels exactly.

This file records the combined statement, in the two cases:

* `i = 0`: the pure `∂_z^m` bound, which is `WlInf_z_bound`;
* `i ≥ 1`: the mixed bound, `(z+1)^m` times `pz_Dth_sup_bound`, where
  `hi : 1 ≤ i → m + i ≤ 4` supplies the hypothesis `k + j ≤ l` of the latter.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.WlInf_terms

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Spaces

set_option autoImplicit false

/-- The `(z+1)^m`-weighted bound for `∂_z^m D_θ^i f`, `m + i ≤ 4`:

`|(z+1)^m ∂_z^m D_θ^i f| ≤ |f|_𝒲 · (1 if i = 0, else (α+sin 2θ) sin(2θ)^{α/5})`.

For `i = 0` this is `WlInf_z_bound`; for `i ≥ 1` it is `(z+1)^m` times
`pz_Dth_sup_bound`, the factor `(1+z)^{-m}` cancelling. -/
theorem factor_bound (α : ℝ) (hα : 0 < α) (h : ℝ → ℝ → ℝ) (hmem : Work.Spaces.WlInfMem α 4 h)
    (m i : ℕ) (hm : m ≤ 4) (hi : 1 ≤ i → m + i ≤ 4) (z θ : ℝ)
    (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ) :
    |(z + 1) ^ m * Work.Spaces.pzIter m (Work.Spaces.DthIter i h) z θ| ≤
      Work.Spaces.WlInf α 4 h *
        (if i = 0 then 1 else (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by
  rcases eq_or_ne i 0 with hi0 | hi0
  · -- `i = 0`: this is the radial bound `WlInf_z_bound`.
    subst hi0
    simpa using WlInf_z_bound α 4 h hmem m hm z θ hz hθ
  · -- `i ≥ 1`: multiply the unweighted angular bound by `(z+1)^m`.
    have hz0 : (0 : ℝ) ≤ z := hz
    have hz1 : (0 : ℝ) < z + 1 := by linarith
    have hzpow : (0 : ℝ) < (z + 1) ^ m := pow_pos hz1 m
    have hne : (z + 1) ^ m ≠ 0 := ne_of_gt hzpow
    have hi1 : 1 ≤ i := by omega
    have hle : m + i ≤ 4 := hi hi1
    have hb := pz_Dth_sup_bound α hα 4 h hmem i m hi1 hle z θ hz hθ
    rw [if_neg hi0]
    calc |(z + 1) ^ m * pzIter m (DthIter i h) z θ|
        = (z + 1) ^ m * |pzIter m (DthIter i h) z θ| := by
          rw [abs_mul, abs_of_pos hzpow]
      _ ≤ (z + 1) ^ m * (WlInf α 4 h / (z + 1) ^ m
            * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) :=
          mul_le_mul_of_nonneg_left hb (le_of_lt hzpow)
      _ = WlInf α 4 h * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by
          rw [← mul_assoc, mul_div_cancel₀ _ hne]

end Work.Spaces
