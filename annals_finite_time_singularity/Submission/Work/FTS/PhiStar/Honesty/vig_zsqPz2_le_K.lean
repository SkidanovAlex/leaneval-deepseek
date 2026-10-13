/-
Copyright: work module for the Elgindi finite-time singularity project.

# `vig_zsqPz2_le_K` — the level-`K` vanishing-weight slot of the smoothing family `z²∂_z²Ψ`

This is the level-`K` analogue of `Work.FTS.ClassC.vig_zsqPz2_le` (the level-`7` statement):
for every vanishing-weight slot `vig α (z²∂_z²Ψ) r j` with `1 ≤ r` and `r + j ≤ K`, the
pointwise domination

```
vig α (z²∂_z²Ψ) r j z θ ≤ 4 * vanGridK α Ψ K z θ      (z > 0, θ ∈ (0,π/2))
```

holds, where `vanGridK` is the level-`K` grid majorant of
`Submission.Work.FTS.PhiStar.Honesty.VanGridK`.

The proof is the level-`7` proof verbatim, with the two membership lemmas of the grid replaced
by their level-`K` counterparts `vig_slot_le_vanGridK` / `hkIntegrand_le_vanGridK`
(proved in `VanGridK.lean`):

* the operator identity `vig_DzIter_pthIter_eq` (`D_z^j∂_θ^r(z²∂_z²Ψ) = D_z^{j+2}(∂_θ^rΨ) −
  D_z^{j+1}(∂_θ^rΨ)`, Clairaut + `z²∂_z² = D_z² − D_z`) is *level-independent* and reused as is;
* the elementary AM–GM `(x−y)²c² ≤ 2(xc)² + 2(yc)²` (`seven_sq_sub_mul_sq_le`) is reused;
* the two shifted slots have radial order `j + 1, j + 2 ≤ K + 2` and angular order `r ≤ K + 2`,
  so each is a summand of `vanGridK`.

Everything here is `sorry`-free.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.PhiStar.Honesty.VanGridK
import Submission.Work.FTS.ClassC.vig_zsqPz2_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem vig_zsqPz2_le_K {α : ℝ} {K : ℕ} (hγ : Work.Spaces.gam α ≤ 3 / 2)
    {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    ∀ j r : ℕ, 1 ≤ r → r + j ≤ K → ∀ z : ℝ, 0 < z →
      ∀ θ : ℝ, θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      Work.FTS.ClassC.vig α (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) r j z θ
        ≤ 4 * Work.FTS.PhiStar.Honesty.vanGridK α Ψ K z θ := by
  intro j r hr hrj z hz θ hθ
  have hrK : r ≤ K + 2 := by omega
  have hj2 : j + 2 ≤ K + 2 := by omega
  have hj1 : j + 1 ≤ K + 2 := by omega
  have hid := Work.FTS.ClassC.vig_DzIter_pthIter_eq hΨ r j z θ hz hθ
  have hsq := Work.FTS.ClassC.seven_sq_sub_mul_sq_le
    (Work.Spaces.DzIter (j + 2) (Work.Spaces.pthIter r Ψ) z θ)
    (Work.Spaces.DzIter (j + 1) (Work.Spaces.pthIter r Ψ) z θ) (Work.Spaces.w z)
  have hsnn : 0 ≤ (Real.sin (2 * θ)) ^ (2 * (r : ℝ) - Work.Spaces.gam α) :=
    Real.rpow_nonneg (le_of_lt (Work.FTS.ClassC.sin_two_pos_of_mem_Ioo hθ)) _
  have hA := vig_slot_le_vanGridK hγ Ψ K r (j + 2) hr hrK hj2 z θ hθ
  have hB := vig_slot_le_vanGridK hγ Ψ K r (j + 1) hr hrK hj1 z θ hθ
  rw [Work.FTS.ClassC.vig, hid]
  calc ((Work.Spaces.DzIter (j + 2) (Work.Spaces.pthIter r Ψ) z θ
          - Work.Spaces.DzIter (j + 1) (Work.Spaces.pthIter r Ψ) z θ)
        * Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (2 * (r : ℝ) - Work.Spaces.gam α)
      ≤ (2 * (Work.Spaces.DzIter (j + 2) (Work.Spaces.pthIter r Ψ) z θ
              * Work.Spaces.w z) ^ 2
          + 2 * (Work.Spaces.DzIter (j + 1) (Work.Spaces.pthIter r Ψ) z θ
              * Work.Spaces.w z) ^ 2)
          * (Real.sin (2 * θ)) ^ (2 * (r : ℝ) - Work.Spaces.gam α) :=
        mul_le_mul_of_nonneg_right hsq hsnn
    _ = 2 * ((Work.Spaces.DzIter (j + 2) (Work.Spaces.pthIter r Ψ) z θ
              * Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ)) ^ (2 * (r : ℝ) - Work.Spaces.gam α))
          + 2 * ((Work.Spaces.DzIter (j + 1) (Work.Spaces.pthIter r Ψ) z θ
              * Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ)) ^ (2 * (r : ℝ) - Work.Spaces.gam α)) := by ring
    _ ≤ 4 * Work.FTS.PhiStar.Honesty.vanGridK α Ψ K z θ := by linarith

end Work.FTS.PhiStar.Honesty
