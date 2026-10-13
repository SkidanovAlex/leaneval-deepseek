import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS_FinalLeaves.classC_sup_le_proved

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_FinalLeaves.Sup5` — the (5′) producer, proved

`sup5'_proved` is the frozen producer `Work.FTS.FinalV2.sup5'` of
`Submission/Work/FTS/FinalV2/Producers.lean` (conjunct (5′) of `Inputs'`), with its statement
copied verbatim: the uniform sup bound

  `|extG g z θ τ| ≤ 10/√(γ(α)-1) · C₀α²`   for `τ ≥ 0`, `z ∈ Iz = [0,∞)`, `θ ∈ Iθ = [0,π/2]`,

for a family `g` satisfying `DynOK' α C₀ Φs E g`.

## Route

`DynOK' = DynOK ∧ LimApprox`.  The three regions of `Iz × Iθ`:

* `z ≤ 0` (i.e. `z = 0`): `extG g 0 θ τ = 0`;
* `z > 0`, `θ ∈ {0, π/2}`: `extG g = g` there and `RegPkgMin.vanish` (a field of `DynOK`) gives
  `g z 0 τ = g z (π/2) τ = 0`;
* `z > 0`, `0 < θ < π/2`: `g` is the limit of the class-C approximating slices `slice (gn n) τ`
  of the `LimApprox` clause, on which the class-C `L^∞`–`ℋ⁴` trade-off
  (`classC_sup_le_proved`, Elgindi's `SecondDerivativesBounded`) gives the bound, with the
  uniform `ℋ⁴`-bound `Xn α (slice (gn n) τ) ≤ C₀α²` making the constant uniform in `n`; the
  limit is then taken with `le_of_tendsto`.
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter

namespace Work.FTS_FinalLeaves

set_option autoImplicit false

/-- **(5′) producer**: the uniform sup bound of the extension `extG g` on `Iz × Iθ`, at the
dynamic amplitude bound `C₀α²` of `DynOK'`. -/
theorem sup5'_proved {α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hα1 : α ≤ 1) {g : Work.FTS.Galerkin.Fam}
    (hOK : Work.FTS.FinalV2.DynOK' α C₀ Φs E g) :
    ∀ τ : ℝ, 0 ≤ τ → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |Work.FTS.RegPkgGal.extG g z θ τ| ≤
        10 / Real.sqrt (Work.Spaces.gam α - 1) * (C₀ * α ^ 2) := by
  have hγ1 : 0 < Work.Spaces.gam α - 1 := by
    rw [Work.Spaces.gam_sub_one]; linarith
  have hCnn : 0 ≤ 10 / Real.sqrt (Work.Spaces.gam α - 1) :=
    div_nonneg (by norm_num) (Real.sqrt_nonneg _)
  intro τ hτ z hz θ hθ
  -- `C₀α² ≥ 0`, from the uniform `ℋ⁴`-bound of `DynOK`
  have hC0 : 0 ≤ C₀ * α ^ 2 :=
    le_trans (Work.Spaces.HkNorm_nonneg α 4 (Work.FTS.Galerkin.slice g τ)) (hOK.1.2 τ hτ)
  rcases le_or_gt z 0 with hz0 | hz0
  · rw [Work.FTS.RegPkgGal.extG_of_nonpos hz0, abs_zero]
    exact mul_nonneg hCnn hC0
  · rcases eq_or_lt_of_le hθ.1 with hθ0 | hθ0
    · rw [← hθ0, Work.FTS.RegPkgGal.extG_of_pos hz0 hτ,
        (hOK.1.1.vanish τ hτ z hz).1, abs_zero]
      exact mul_nonneg hCnn hC0
    · rcases eq_or_lt_of_le hθ.2 with hθp | hθp
      · rw [hθp, Work.FTS.RegPkgGal.extG_of_pos hz0 hτ,
          (hOK.1.1.vanish τ hτ z hz).2, abs_zero]
        exact mul_nonneg hCnn hC0
      · -- the interior: the class-C bound at the approximating slices, then the limit
        have hzθ : (z, θ) ∈ Work.Construction.Qd := ⟨hz0, hθ0, hθp⟩
        obtain ⟨gn, _B, _L, h1, _h2, h3, _h4⟩ := hOK.2 (τ + 1) (by linarith)
        have hτT : τ ∈ Set.Icc (0 : ℝ) (τ + 1) := ⟨hτ, by linarith⟩
        have hconv : Filter.Tendsto (fun n => Work.FTS.Galerkin.slice (gn n) τ z θ)
            Filter.atTop (𝓝 (Work.FTS.Galerkin.slice g τ z θ)) :=
          h3 τ hτT 0 0 (by norm_num) z θ hzθ
        have hbound : ∀ n : ℕ, |Work.FTS.Galerkin.slice (gn n) τ z θ| ≤
            10 / Real.sqrt (Work.Spaces.gam α - 1) * (C₀ * α ^ 2) := by
          intro n
          have hC := classC_sup_le_proved hα hα1 (Work.FTS.Galerkin.slice (gn n) τ)
            (h1 n τ hτT).1 z θ hzθ
          exact le_trans hC (mul_le_mul_of_nonneg_left (h1 n τ hτT).2.1 hCnn)
        have hlim := le_of_tendsto hconv.abs (Filter.Eventually.of_forall hbound)
        rwa [Work.FTS.RegPkgGal.extG_of_pos hz0 hτ]

end Work.FTS_FinalLeaves
