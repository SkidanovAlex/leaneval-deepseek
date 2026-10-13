import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Submission.Work.FTS.Nonlinear.Pieces.Rows
import Submission.Work.FTS.Nonlinear.Defs
import Submission.Work.Spaces.WlInf_terms

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.Pieces.rl1Tools

set_option autoImplicit false

/-- The zeroth (radial) summand of `𝒲^{l,∞}` is the honest sup of `f` over the domain, so a
`WlInfMem`-bound bounds `f` pointwise.  This is the `k = 0`, `pzIter 0` instance of
`Work.Spaces.WlInf_z_bound`. -/
theorem abs_le_WlInf_of_mem {α B : ℝ} {l : ℕ} {f : ℝ → ℝ → ℝ}
    (hmem : Work.Spaces.WlInfMem α l f) (h : Work.Spaces.WlInf α l f ≤ B)
    {z θ : ℝ} (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ) :
    |f z θ| ≤ B := by
  have hb := Work.Spaces.WlInf_z_bound α l f hmem 0 (Nat.zero_le l) z θ hz hθ
  simpa using le_trans hb h

/-- `starPt`: the `Φ̃_*`-coefficients `ℛ(Φ̃_*), 𝒱(Φ̃_*)` and `∂_θ 𝒰(Φ̃_*)` of the nonlinear
terms are bounded by `max Cs 0 · α`.

This is an immediate consequence of the `𝒲^{l,∞}`-bounds recorded in `StarPkg`: each of the
three quantities is kept in `WlInf`, the `(z+1)/z`-weight between the two is `≥ 1` on `z > 0`,
and `Cs ≤ max Cs 0` with `α > 0`. -/
theorem starPt {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn} (hα : 0 < α)
    (hs : Work.FTS.Nonlin.StarPkg α Cs Φs) :
    (∀ z, 0 < z → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ| ≤ max Cs 0 * α) ∧
    (∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z θ| ≤ max Cs 0 * α) ∧
    (∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.pth (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs)) z θ|
        ≤ max Cs 0 * α) := by
  have hle : Cs * α ≤ max Cs 0 * α :=
    mul_le_mul_of_nonneg_right (le_max_left Cs 0) hα.le
  have hRmem : Work.Spaces.WlInfMem α 4 (fun z θ => (z + 1) / z
      * Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs)
        z θ) := hs.R.1
  have hRbnd : Work.Spaces.WlInf α 4 (fun z θ => (z + 1) / z
      * Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs)
        z θ) ≤ max Cs 0 * α := le_trans hs.R.2 hle
  refine ⟨?_, ?_, ?_⟩
  · intro z hz θ hθ
    have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz
    have hb : |(z + 1) / z * Work.Construction.Rop α
        (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ|
        ≤ max Cs 0 * α := abs_le_WlInf_of_mem hRmem hRbnd hzI hθ
    have hge1 : (1 : ℝ) ≤ (z + 1) / z := by
      rw [le_div_iff₀ hz]; linarith
    have hpos : 0 < (z + 1) / z := lt_of_lt_of_le zero_lt_one hge1
    have h1 : |Work.Construction.Rop α (Work.Construction.PhiTil α
        (Work.Construction.Fstar α) Φs) z θ|
        ≤ |(z + 1) / z * Work.Construction.Rop α
          (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ| := by
      rw [abs_mul, abs_of_pos hpos]
      calc |Work.Construction.Rop α (Work.Construction.PhiTil α
              (Work.Construction.Fstar α) Φs) z θ|
          = 1 * |Work.Construction.Rop α (Work.Construction.PhiTil α
              (Work.Construction.Fstar α) Φs) z θ| := (one_mul _).symm
        _ ≤ (z + 1) / z * |Work.Construction.Rop α (Work.Construction.PhiTil α
              (Work.Construction.Fstar α) Φs) z θ| :=
            mul_le_mul_of_nonneg_right hge1 (abs_nonneg _)
    exact le_trans h1 hb
  · intro z hz θ hθ
    exact abs_le_WlInf_of_mem hs.V.1 (le_trans hs.V.2 hle) hz hθ
  · intro z hz θ hθ
    exact abs_le_WlInf_of_mem hs.dU.1 (le_trans hs.dU.2 hle) hz hθ

end Work.FTS.Nonlinear.Pieces.rl1Tools
