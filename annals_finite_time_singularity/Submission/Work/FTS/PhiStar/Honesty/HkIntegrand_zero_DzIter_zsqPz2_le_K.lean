/-
Copyright: work module for the Elgindi finite-time singularity project.

# The level-`0` radial slot of the smoothing family `z²∂_z²Ψ` against the grid majorant

For a datum `Ψ` which is `C^∞` on the **open** quadrant and an angular exponent
`γ = 1 + α/10 ≤ 3/2`, every iterated radial slot of the smoothing family
`z²∂_z²Ψ` is dominated by the level-`K` grid majorant `vanGridK α Ψ K`:

```
HkIntegrand α 0 (D_z^j (z²∂_z²Ψ)) z θ ≤ 4 * vanGridK α Ψ K z θ     (j ≤ K, z > 0, θ ∈ (0,π/2)).
```

The mathematics is three lines.

* At level `0` the `ℋ⁰`-integrand is a *single* weighted square,
  `HkIntegrand α 0 f = (f · w/ sin(2θ)^{η/2})²` (`HkIntegrand_zero_eq`);
* the operator identity `D_z^j (z²∂_z²Ψ) = D_z^{j+2}Ψ − D_z^{j+1}Ψ` on the open quadrant
  (`DzIter_zsqPzIter2_eq`: `z²∂_z² = D_z² − D_z` is a polynomial in `D_z` commuting with
  `D_z^j` by Clairaut — `zsqPz2_DzIter_eqOn` — and `z²∂_z²h = D_z²h − D_zh` is
  `seven_zsq_pzIter_two_eq`);
* the elementary AM–GM `((x − y)c)² ≤ 2(xc)² + 2(yc)²` (`seven_sq_sub_mul_sq_le`), and the two
  slots `D_z^{j+1}Ψ`, `D_z^{j+2}Ψ` are summands of the grid because `j + 2 ≤ K + 2`
  (`hkDze_zero_DzIter_le_vanGridK`).  The constant `4 = 2·2` is exactly the AM–GM loss.

The hypothesis `γ ≤ 3/2` is not needed for this slot; it is kept because the statement is
consumed together with the vanishing-weight siblings `vig_zsqPz2_le_K` and
`HkIntegrand_K_le_of_bounds`, which do use it.

Everything here is `sorry`-free.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.PhiStar.Honesty.VanGridK
import Submission.Work.FTS.ClassC.HkMem_seven_slots_of_plain_family

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## Two elementary bookkeeping lemmas -/

/-- At level `0` the `ℋ⁰`-integrand is the single weighted square
`(f z θ · w z / sin(2θ)^{η/2})²`: the first sum of `HkIntegrand` has the single term `i = 0`
and the second (mixed) sum is empty, its index condition `1 ≤ i` being false. -/
theorem HkIntegrand_zero_eq (α : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 f z θ
      = (f z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  rw [Work.Spaces.HkIntegrand, Finset.sum_range_one, Finset.sum_range_one, Finset.sum_range_one,
    Work.Spaces.DzIter_zero]
  norm_num

/-- **The operator identity.**  On the open quadrant, `D_z^j` commutes with `z²∂_z²`, and
`z²∂_z² = D_z² − D_z` there (both `z²∂_z²` and `D_z` are `z`-only operators, so the commutation
is Clairaut for the `z`-variable):
`D_z^j (z²∂_z²Ψ) = D_z^{j+2}Ψ − D_z^{j+1}Ψ`. -/
theorem DzIter_zsqPzIter2_eq {Ψ : ℝ → ℝ → ℝ}
    (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) (j : ℕ) :
    ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      Work.Spaces.DzIter j (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
        = Work.Spaces.DzIter (j + 2) Ψ z θ - Work.Spaces.DzIter (j + 1) Ψ z θ := by
  intro z θ hz hθ
  have hθ0 : 0 < θ := hθ.1
  have hπ : θ < Real.pi / 2 := hθ.2
  have hD : Work.Spaces.DzIter j (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
      = z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter j Ψ) z θ :=
    Work.FTS.ClassC.NormPiecesAux.zsqPz2_DzIter_eqOn Ψ hΨ j z θ hz hθ0 hπ
  have hE : z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter j Ψ) z θ
      = Work.Spaces.DzIter 2 (Work.Spaces.DzIter j Ψ) z θ
        - Work.Spaces.DzIter 1 (Work.Spaces.DzIter j Ψ) z θ :=
    Work.FTS.ClassC.seven_zsq_pzIter_two_eq (Work.Spaces.DzIter j Ψ) (hΨ.DzIter j)
      z θ hz hθ0 hπ
  have e2 : Work.Spaces.DzIter 2 (Work.Spaces.DzIter j Ψ)
      = Work.Spaces.DzIter (j + 2) Ψ := by
    rw [← Work.FTS.ClassC.seven_DzIter_add 2 j Ψ]
    exact congrArg (fun n => Work.Spaces.DzIter n Ψ) (by omega)
  have e1 : Work.Spaces.DzIter 1 (Work.Spaces.DzIter j Ψ)
      = Work.Spaces.DzIter (j + 1) Ψ := by
    rw [← Work.FTS.ClassC.seven_DzIter_add 1 j Ψ]
    exact congrArg (fun n => Work.Spaces.DzIter n Ψ) (by omega)
  rw [hD, hE, e2, e1]

/-! ## The target -/

theorem HkIntegrand_zero_DzIter_zsqPz2_le_K {α : ℝ} {K : ℕ}
    (hγ : Work.Spaces.gam α ≤ 3 / 2) {Ψ : ℝ → ℝ → ℝ}
    (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    ∀ j : ℕ, j ≤ K → ∀ z : ℝ, 0 < z → ∀ θ : ℝ, θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      Work.Spaces.HkIntegrand α 0
          (Work.Spaces.DzIter j (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z θ
        ≤ 4 * Work.FTS.PhiStar.Honesty.vanGridK α Ψ K z θ := by
  intro j hj z hz θ hθ
  -- the AM–GM kernel and the two dominating grid slots
  have hAM := Work.FTS.ClassC.seven_sq_sub_mul_sq_le
    (Work.Spaces.DzIter (j + 2) Ψ z θ) (Work.Spaces.DzIter (j + 1) Ψ z θ)
    (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
  have hA : Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter (j + 2) Ψ) z θ
      ≤ vanGridK α Ψ K z θ :=
    hkDze_zero_DzIter_le_vanGridK (α := α) (Ψ := Ψ) (K := K) (l := j + 2) (by omega) z θ hθ
  have hB : Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter (j + 1) Ψ) z θ
      ≤ vanGridK α Ψ K z θ :=
    hkDze_zero_DzIter_le_vanGridK (α := α) (Ψ := Ψ) (K := K) (l := j + 1) (by omega) z θ hθ
  rw [HkIntegrand_zero_eq α _ z θ, DzIter_zsqPzIter2_eq hΨ j z θ hz hθ]
  calc ((Work.Spaces.DzIter (j + 2) Ψ z θ - Work.Spaces.DzIter (j + 1) Ψ z θ)
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      ≤ 2 * (Work.Spaces.DzIter (j + 2) Ψ z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        + 2 * (Work.Spaces.DzIter (j + 1) Ψ z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := hAM
    _ ≤ 4 * vanGridK α Ψ K z θ := by
        rw [← HkIntegrand_zero_eq α (Work.Spaces.DzIter (j + 2) Ψ) z θ,
          ← HkIntegrand_zero_eq α (Work.Spaces.DzIter (j + 1) Ψ) z θ]
        linarith

end Work.FTS.PhiStar.Honesty
