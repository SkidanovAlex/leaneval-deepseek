import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.IntervalCases
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.StabilityFar.Profile.exists_Fstar_add_ge

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The mixed `𝒲^{4,∞}`-bound for the explicit function `c2m(θ)·2α/(1+z)`

This is the second of the two pointwise inputs of `Work.FTS.Nonlinear.FstarPkg.c2m_L12Fstar_W`:
the *mixed* weighted derivative

  `(z+1)^k ∂_z^k D_θ^j (c2m(θ)·2α/(1+z)) · sin(2θ)^{-α/5}/(α+sin 2θ)`

is `≤ C α`, uniformly for `0 < α ≤ 1`, `z ≥ 0`, `θ ∈ Iθ`, `1 ≤ j ≤ 4`, `k ≤ 4`.

## Mathematics

The function factors as `c2m(θ) · B(z)`, `B(z) = 2α/(1+z)`.  Since `D_θ` and `∂_z` act on the
two variables separately (`Work.Spaces.DthIter_decomp`, `Work.Spaces.pzIter_decomp`),

  `∂_z^k D_θ^j (c2m·B)(z,θ) = (dthU^[j] c2m)(θ) · (deriv^[k] B)(z)`

(`Work.Spaces.dthU` is the one-dimensional shadow `sin(2θ)·d/dθ` of `D_θ`).  The three
elementary estimates

* `|(z+1)^k deriv^[k] B z| ≤ 2α·k!` (radial, `c2mInv_radial`),
* `|(dthU^[j] c2m)(θ)| ≤ 1000·sin(2θ)²` for `1 ≤ j ≤ 4` (`dthU_c2m_bound`),
* `sin(2θ)²·sin(2θ)^{-α/5}/(α+sin 2θ) ≤ 1` on `θ ∈ Iθ`, `0 < α ≤ 1` (`sinWeight_le_one`)

then give, on the domain,

  `|⋯| ≤ 1000 sin(2θ)² · 2α k! · sin(2θ)^{-α/5}/(α+sin 2θ) ≤ 2000 α k! ≤ 48000 α ≤ 100000 α`.

Note `j ≥ 1` is what makes the angular estimate available: `dthU` carries a factor `sin 2θ`,
so `dthU^[j] c2m` vanishes like `sin(2θ)²` at the two angular endpoints, which is exactly the
decay needed to absorb the singular weight `sin(2θ)^{-α/5}/(α+sin 2θ)`.
-/
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.FstarPkg

set_option autoImplicit false

theorem c2mInv_mixed :
    ∃ C : ℝ, 0 < C ∧ ∀ (α z θ : ℝ), 0 < α → α ≤ 1 → 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      ∀ (j k : ℕ), 1 ≤ j → j ≤ 4 → k ≤ 4 →
      |(z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter j
          (fun z θ => Work.Construction.c2m θ * (2 * α / (1 + z)))) z θ
        * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))| ≤ C * α := by
  refine ⟨100000, by norm_num, ?_⟩
  intro α z θ hα hα1 hz hθ j k hj1 hj4 hk
  set s : ℝ := Real.sin (2 * θ) with hs
  set B : ℝ → ℝ := fun z => 2 * α / (1 + z) with hB
  set g : ℝ → ℝ := (Work.Spaces.dthU^[j] Work.Construction.c2m) with hg
  -- factor the mixed derivative into an angular and a radial part
  have hDth : Work.Spaces.DthIter j (fun z θ => Work.Construction.c2m θ * (2 * α / (1 + z)))
      = fun z θ => g θ * B z := by
    funext z θ
    exact Work.Spaces.DthIter_decomp j Work.Construction.c2m B z θ
  rw [hDth]
  rw [Work.Spaces.pzIter_decomp k g B z θ]
  have hs0 : 0 ≤ s := by
    rw [hs]
    exact Real.sin_nonneg_of_mem_Icc
      ⟨by linarith [(Set.mem_Icc.mp hθ).1], by linarith [(Set.mem_Icc.mp hθ).2, Real.pi_pos]⟩
  have hs1 : s ≤ 1 := by rw [hs]; exact Real.sin_le_one _
  have hA : |g θ| ≤ 1000 * s ^ 2 := by
    rw [hg]
    exact dthU_c2m_bound j hj1 hj4 θ
  have hBnd : |(z + 1) ^ k * deriv^[k] B z| ≤ 2 * α * (k.factorial : ℝ) := by
    rw [hB]
    exact c2mInv_radial α hα k z hz
  have hXnn : 0 ≤ s ^ (-(α / 5)) / (α + s) :=
    div_nonneg (Real.rpow_nonneg hs0 _) (by linarith)
  have hW : s ^ 2 * (s ^ (-(α / 5)) / (α + s)) ≤ 1 := by
    have := sinWeight_le_one α s hα hα1 hs0 hs1
    rwa [mul_div_assoc] at this
  have hfact : (k.factorial : ℝ) ≤ 24 := by
    interval_cases k <;> norm_num
  rw [mul_div_assoc]
  rw [show (z + 1) ^ k * (g θ * deriv^[k] B z)
      = g θ * ((z + 1) ^ k * deriv^[k] B z) by ring]
  rw [abs_mul, abs_mul, abs_of_nonneg hXnn]
  have h1 : |g θ| * |(z + 1) ^ k * deriv^[k] B z| * (s ^ (-(α / 5)) / (α + s))
      ≤ (1000 * s ^ 2) * (2 * α * (k.factorial : ℝ)) * (s ^ (-(α / 5)) / (α + s)) := by
    apply mul_le_mul_of_nonneg_right _ hXnn
    exact mul_le_mul hA hBnd (abs_nonneg _) (by positivity)
  refine le_trans h1 ?_
  have h2 : (1000 * s ^ 2) * (2 * α * (k.factorial : ℝ)) * (s ^ (-(α / 5)) / (α + s))
      = 2000 * α * (k.factorial : ℝ) * (s ^ 2 * (s ^ (-(α / 5)) / (α + s))) := by ring
  rw [h2]
  have h3 : 2000 * α * (k.factorial : ℝ) * (s ^ 2 * (s ^ (-(α / 5)) / (α + s)))
      ≤ 2000 * α * (k.factorial : ℝ) * 1 := by
    apply mul_le_mul_of_nonneg_left hW
    positivity
  have h4 : 2000 * α * (k.factorial : ℝ) * 1 ≤ 2000 * α * 24 := by
    nlinarith [hα.le, hfact]
  have h5 : 2000 * α * 24 ≤ 100000 * α := by nlinarith [hα.le]
  linarith [h3, h4, h5]

end Work.FTS.Nonlinear.FstarPkg
