import Mathlib
import Submission.Work.PointlessTwist.Constants
import Submission.Work.PointlessTwist.FunctionField
import Submission.Work.PointlessTwist.Constants.hasGoodAut_of_j_ne

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option linter.style.haveILetI false

namespace Work.PointlessTwist.Constants

open WeierstrassCurve WeierstrassCurve.Affine

/-- **`j ≠ 1728` from the characteristic-free form `c₄ ^ 3 ≠ 1728 · Δ`.**  Since `j = Δ⁻¹c₄³`,
`j = 1728` is equivalent to `c₄³ = 1728 · Δ` once `Δ ≠ 0`. -/
private theorem j_ne_1728_of_c4_cube_ne {K : Type} [Field K] (W : WeierstrassCurve K)
    [W.IsElliptic] (hΔ : W.Δ ≠ 0) (h : W.c₄ ^ 3 ≠ 1728 * W.Δ) : W.j ≠ 1728 := by
  intro hj
  apply h
  have h2 := congrArg (fun t => W.Δ * t) hj
  rw [WeierstrassCurve.j_eq] at h2
  rw [← mul_assoc, mul_inv_cancel₀ hΔ, one_mul, mul_comm W.Δ 1728] at h2
  exact h2

/-- **The constant Tate curve over a tower.**  Let `c ∈ 𝔽` be a parameter whose Tate normal form
`E(c) : y² + (1-c)xy - cy = x³ - cx²` is nonsingular and has `j ≠ 1728` (in the characteristic-free
form `c₄³ ≠ 1728·Δ`), and let `𝔽 → 𝕜` be a field extension.  Then there is a `FiveTorsionCurve 𝕜`
whose curve is `(Tate.tateCurve c).baseChange 𝕜` and whose marked point is the base change of
`(0,0)` — in particular the curve is **constant** with a constant point of order `5`.  This is the
concrete data of the function-field classes (b), (c), (d).

Route: reproduce the last part of `Work.PointlessIndexFive.nonempty_fiveTorsionCurve` with the
*prescribed* `c` (no `exists_tate_param`, no `Infinite 𝔽`):
* `(Tate.tateCurve c).Δ = c^5(c^2-11c-1) ≠ 0` gives `IsElliptic` (`WeierstrassCurve.isElliptic_iff`,
  `isUnit_iff_ne_zero`), hence `c ≠ 0`;
* transport the invariants to `𝕜` using the equality of curves
  `(Tate.tateCurve c).baseChange 𝕜 = Tate.tateCurve (algebraMap 𝔽 𝕜 c)` (prove by `ext <;> simp`),
  the formulas `Work.TorsorExistence.Tate.tateCurve_Δ` / `tateCurve_c₄` over `𝕜`, and injectivity of
  `algebraMap 𝔽 𝕜`; this gives `Δ ≠ 0` and `j ≠ 1728` over `𝕜`;
* `HasGoodAut` (Silverman A.1.2) for the base-changed Tate model over `𝕜` is the same case split as
  in `nonempty_fiveTorsionCurve`: characteristic `2` via `Work.PointlessIndexFive.hasGoodAut_char_two`
  (with `j ≠ 0 = 1728`), characteristic `3` via `hasGoodAut_char_three`, the rest by putting the
  model in short form (`Work.PointlessIndexFive.exists_short_variableChange`) and
  `hasGoodAut_short` / `Work.Arithmetic.Aut_orderOf_dvd_of_short`;
* `five_smul` is `Tate.tate_five_smul` transported by `Point.baseChange` (`map_nsmul`, `map_zero`,
  `nonsingular` base change), and `P_ne_zero` is `Point.some_ne_zero`.
Take `C₅.P := Point.baseChange 𝔽 𝕜 (Point.some 0 0 _)` and `E_eq := rfl`, `P_eq := rfl`. -/
theorem nonempty_constantTateData {𝔽 : Type} [Field 𝔽] [DecidableEq 𝔽] {𝕜 : Type} [Field 𝕜]
    [DecidableEq 𝕜] [Algebra 𝔽 𝕜] (c : 𝔽)
    (hΔ : (Work.TorsorExistence.Tate.tateCurve c).Δ ≠ 0)
    (hj : (Work.TorsorExistence.Tate.tateCurve c).c₄ ^ 3
      ≠ 1728 * (Work.TorsorExistence.Tate.tateCurve c).Δ) :
    Nonempty (Work.PointlessTwist.ConstantTateData 𝔽 𝕜 c) := by
  classical
  -- the Tate model over `𝔽` is elliptic, and `c ≠ 0`
  have hEll : (Work.TorsorExistence.Tate.tateCurve c).IsElliptic := by
    rw [WeierstrassCurve.isElliptic_iff]
    exact isUnit_iff_ne_zero.mpr hΔ
  haveI := hEll
  have hc0 : c ≠ 0 := fun hc =>
    hΔ (by rw [Work.TorsorExistence.Tate.tateCurve_Δ, hc]; ring)
  have hns00 : Nonsingular (Work.TorsorExistence.Tate.tateCurve c) 0 0 :=
    (equation_iff_nonsingular (W := Work.TorsorExistence.Tate.tateCurve c)).mp
      (Work.TorsorExistence.Tate.tateCurve_equation_zero c)
  -- the invariants of the base change
  have hΔ𝕜 : ((Work.TorsorExistence.Tate.tateCurve c).baseChange 𝕜).Δ ≠ 0 := by
    rw [WeierstrassCurve.baseChange, WeierstrassCurve.map_Δ]
    exact fun h => hΔ ((algebraMap 𝔽 𝕜).injective (by simpa using h))
  have hc4𝕜 : ((Work.TorsorExistence.Tate.tateCurve c).baseChange 𝕜).c₄ ^ 3
      ≠ 1728 * ((Work.TorsorExistence.Tate.tateCurve c).baseChange 𝕜).Δ := by
    rw [WeierstrassCurve.baseChange, WeierstrassCurve.map_c₄, WeierstrassCurve.map_Δ]
    refine fun h => hj ?_
    have h2 : (algebraMap 𝔽 𝕜) ((Work.TorsorExistence.Tate.tateCurve c).c₄ ^ 3)
        = (algebraMap 𝔽 𝕜) (1728 * (Work.TorsorExistence.Tate.tateCurve c).Δ) := by
      rw [map_pow, map_mul, map_ofNat]
      exact h
    exact (algebraMap 𝔽 𝕜).injective h2
  have hEll𝕜 : ((Work.TorsorExistence.Tate.tateCurve c).baseChange 𝕜).IsElliptic := by
    rw [WeierstrassCurve.baseChange]
    infer_instance
  haveI : ((Work.TorsorExistence.Tate.tateCurve c).baseChange 𝕜).IsElliptic := hEll𝕜
  have hj𝕜 : ((Work.TorsorExistence.Tate.tateCurve c).baseChange 𝕜).j ≠ 1728 :=
    j_ne_1728_of_c4_cube_ne _ hΔ𝕜 hc4𝕜
  -- Silverman A.1.2 for the base-changed model
  have hgood : Work.PointlessIndexFive.HasGoodAut
      ((Work.TorsorExistence.Tate.tateCurve c).baseChange 𝕜) :=
    hasGoodAut_of_j_ne _ hj𝕜
  -- the marked point `(0,0)` of the Tate model
  set T : Point ((Work.TorsorExistence.Tate.tateCurve c)⁄𝔽) := Point.some 0 0 hns00 with hT
  have h5T : (5 : ℕ) • T = 0 := Work.TorsorExistence.Tate.tate_five_smul c hc0 hns00
  have hPne : T ≠ 0 := Point.some_ne_zero hns00
  have hPne' : Point.map (W' := Work.TorsorExistence.Tate.tateCurve c)
      (Algebra.ofId 𝔽 𝕜) T ≠ 0 := by
    intro h
    exact hPne (Point.map_injective (W' := Work.TorsorExistence.Tate.tateCurve c)
      (f := Algebra.ofId 𝔽 𝕜) (by simpa using h))
  exact ⟨{
    C₅ := {
      E := (Work.TorsorExistence.Tate.tateCurve c).baseChange 𝕜
      isElliptic := hEll𝕜
      j_ne := hj𝕜
      P := Point.map (W' := Work.TorsorExistence.Tate.tateCurve c) (Algebra.ofId 𝔽 𝕜) T
      P_ne_zero := hPne'
      five_smul := by
        have hh := map_nsmul (Point.map (W' := Work.TorsorExistence.Tate.tateCurve c)
          (Algebra.ofId 𝔽 𝕜)) 5 T
        rw [← hh, h5T, Point.map_zero]
      order_aut := hgood }
    E_eq := rfl
    P := T
    five_smul := h5T
    P_ne_zero := hPne
    P_eq := rfl }⟩

end Work.PointlessTwist.Constants
