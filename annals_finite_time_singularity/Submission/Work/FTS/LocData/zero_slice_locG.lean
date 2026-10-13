/-
# `zero_slice_locG` — the localised datum vanishes to *second* order at the axis `z = 0`

The perturbation `g = locG α L β h = -zfar L F_* + β h` of the localised-data chapter
(`Submission/Work/FTS/LocData/Defs.lean`) satisfies the two axis conditions of the admissible
class `DataAdm`,

  `g 0 θ = 0`  and  `∂_z g 0 θ = 0`   for `0 ≤ θ ≤ π/2`,

as soon as the bump `h` vanishes for `z ≤ 3/4` (this is the case for the concrete bump `hLoc`,
whose `z`-support is `(3/4, 7/4)`) and `L ≥ 1`.

Both are *local* statements at `z = 0`, and that is the whole content of the proof:

* at `z = 0` the far part `zfar L F_* z θ = (1 - χ(z/L))·F_*(z,θ)` vanishes because
  `χ(0/L) = χ 0 = 1` (`chi_zero`), and `h 0 θ = 0` by hypothesis;
* the two functions vanish on a whole *neighbourhood* of `z = 0`: for `|z| ≤ 1 ≤ L` one has
  `|z/L| ≤ 1`, hence `χ(z/L) = 1` (`chi_eq_one`) and `zfar L F_* z θ = 0`, while `h z θ = 0` for
  `z ≤ 3/4`.  So `z ↦ locG α L β h z θ` agrees with `0` on the open interval `(-1, 3/4) ∋ 0`
  and therefore has derivative `0` at `0`.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Order.Lattice
import Submission.Work.FTS.LocData.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.LocData

open Filter
open scoped Topology

theorem zero_slice_locG (α L β : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {h : ℝ → ℝ → ℝ}
    (hh : ∀ z θ, z ≤ 3 / 4 → h z θ = 0) (hL : 1 ≤ L) :
    ∀ θ ∈ Work.Spaces.Iθ, locG α L β h 0 θ = 0 ∧ Work.Spaces.pz (locG α L β h) 0 θ = 0 := by
  intro θ hθ
  have hLpos : (0 : ℝ) < L := lt_of_lt_of_le zero_lt_one hL
  have hchi0 : Work.Stability.chi (0 / L) = 1 := by rw [zero_div, Work.Stability.chi_zero]
  have hh0 : h 0 θ = 0 := hh 0 θ (by norm_num)
  constructor
  · -- the value at `z = 0`: the far part vanishes because `χ 0 = 1`, and so does the bump
    rw [locG_eq_zfar, Work.Stability.zfar_apply, hchi0, hh0]
    ring
  · -- the `z`-derivative at `0`: the slice is zero on the neighbourhood `(-1, 3/4)` of `0`
    rw [Work.Spaces.pz]
    have hev : (fun z => locG α L β h z θ) =ᶠ[𝓝 (0 : ℝ)] (fun _ => (0 : ℝ)) := by
      filter_upwards [isOpen_Ioo.mem_nhds (show (0 : ℝ) ∈ Set.Ioo (-1) (3 / 4) by norm_num)]
        with z hz
      have hz1 : |z| < 1 := abs_lt.mpr ⟨hz.1, by linarith [hz.2]⟩
      have hzL : |z / L| ≤ 1 := by
        rw [abs_div, abs_of_pos hLpos, div_le_one hLpos]
        exact le_trans (le_of_lt hz1) hL
      have hchiz : Work.Stability.chi (z / L) = 1 := Work.Stability.chi_eq_one hzL
      have hhz : h z θ = 0 := hh z θ (le_of_lt hz.2)
      rw [locG_eq_zfar, Work.Stability.zfar_apply, hchiz, hhz]
      ring
    rw [hev.deriv_eq, deriv_const]

end Work.FTS.LocData
