import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Elliptic.WtoHAux
import Submission.Work.Elliptic.radial_arith

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Elliptic

open Work.Spaces

/-! ## A helper: expansion of `∂_z^m f` through `f = z² · divZ2 f`

For `SmoothNbhd f`, `z > 0` and `m ≤ 4`, the `m`-th plain `z`-derivative of `f` is obtained
from `f = z² · (f/z²)` (valid near `z ≠ 0`) and Leibniz; only `z²`, `2z`, `2` contribute. -/
theorem pzIter_divZ2_expansion_aux {f : ℝ → ℝ → ℝ} (hsm : SmoothNbhd f) {m : ℕ}
    (hm : m ≤ 4) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Iθ) :
    pzIter m f z θ = z ^ 2 * pzIter m (divZ2 f) z θ
      + (2 * (m : ℝ)) * z * pzIter (m - 1) (divZ2 f) z θ
      + ((m : ℝ) * ((m : ℝ) - 1)) * pzIter (m - 2) (divZ2 f) z θ := by
  have hκ : ContDiffAt ℝ ⊤ (fun z' => divZ2 f z' θ) z :=
    contDiffAt_divZ2_zslice hsm θ hθ z hz
  have hcongr : pzIter m f z θ = pzIter m (fun z θ => z ^ 2 * divZ2 f z θ) z θ := by
    refine pzIter_congr_nhds m ?_
    filter_upwards [IsOpen.mem_nhds isOpen_Ioi hz] with z' hz'
    exact divZ2_eq_mul (ne_of_gt hz')
  rw [hcongr, pzIter_sq_mul m hm hκ]

/-- The radial pointwise estimate underlying Proposition `WtoH`: if
`(z+1)³/z² · f ∈ 𝒲^{4,∞}` then for every `m ≤ 4` and `z > 0`, `θ ∈ Iθ`,
`|(1+z) w(z) z^m ∂_z^m f(z,θ)| ≤ 200000 · |(z+1)³/z² f|_{𝒲^{4,∞}}`. -/
theorem WtoH_Radial {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hsm : Work.Spaces.SmoothNbhd f)
    (hmem : Work.Spaces.WlInfMem α 4 (fun z θ => (z + 1) ^ 3 / z ^ 2 * f z θ)) :
    ∀ (m : ℕ), m ≤ 4 → ∀ (z : ℝ), 0 < z → ∀ (θ : ℝ), θ ∈ Work.Spaces.Iθ →
      |(1 + z) * Work.Spaces.w z * z ^ m * Work.Spaces.pzIter m f z θ|
        ≤ 200000 * Work.Spaces.WlInf α 4 (fun z θ => (z + 1) ^ 3 / z ^ 2 * f z θ) := by
  intro m hm z hz θ hθ
  let G : ℝ → ℝ → ℝ := fun z θ => (z + 1) ^ 3 / z ^ 2 * f z θ
  have hmemG : Work.Spaces.WlInfMem α 4 G := hmem
  have hΛ : 0 ≤ Work.Spaces.WlInf α 4 G := by
    rw [Work.Spaces.WlInf]
    exact add_nonneg (Work.Spaces.wlZSum_nonneg α 4 G hmemG)
      (Work.Spaces.wlThSum_nonneg α 4 G hmemG)
  have hG : G = fun z θ => (z + 1) ^ 3 * divZ2 f z θ := g_divZ2_eq f
  have hκ : ContDiffAt ℝ ⊤ (fun z' => divZ2 f z' θ) z :=
    contDiffAt_divZ2_zslice hsm θ hθ z hz
  have htri : ∀ j ≤ m,
      |(1 + z) ^ (j + 3) * pzIter j (divZ2 f) z θ| ≤ 6000 * Work.Spaces.WlInf α 4 G := by
    have h := tri_bound (G := G) (κ := divZ2 f) hG hm hz hκ (fun j hj =>
      Work.Spaces.WlInf_z_bound α 4 G hmemG j (by omega) z θ (le_of_lt hz) hθ)
    intro j hj
    have h' := h j hj
    rw [show (1 : ℝ) + z = z + 1 by ring]
    exact h'
  have hA := pzIter_divZ2_expansion_aux hsm hm hz hθ
  rw [hA]
  exact radial_arith (Λ := Work.Spaces.WlInf α 4 G) hm hz hΛ
    (fun j => pzIter j (divZ2 f) z θ) htri

end Work.Elliptic
