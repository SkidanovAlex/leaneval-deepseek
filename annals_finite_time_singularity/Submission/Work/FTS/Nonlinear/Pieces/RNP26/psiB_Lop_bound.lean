import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.Spaces.DthIter_mul
import Submission.Work.Spaces.Gam_bounds
import Submission.Work.Construction.GLop_Aux
import Submission.Work.Construction.H4N_GammaTerm_Lop_bound
import Submission.Work.FTS.Nonlinear.Pieces.RNP26.BangDefs
import Submission.Work.FTS.Nonlinear.Pieces.RNP26.Bang_bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.Pieces.RNP26

/-- **The angular core for row 26**: the `Lop`-iterates of `θ ↦ sin²θ · Γ(θ)` are bounded by
`D·Γ(θ)·(sin²(2θ) + α)`, uniformly in `0 < α ≤ 1` and `1 ≤ i ≤ 4`.

Recipe (verbatim analogue of `Work.Construction.H4N_GammaTerm_Lop_bound`, whose angular
factor is `ψ = c2m·Γ` instead; the machinery `glop_Gam_deriv`, `glop_comp_cos_sq`, `glop_step`
and the tools `deriv_mono5`, `abs_mono5_le` are all in the tree): on `θ ∈ (0,π/2)` put
`x = cos²θ`.  Then `sin²θ = 1 - x`, `4x(1-x) = sin²(2θ)`, and for smooth `g`
`Lop (Γ·(g ∘ cos²)) = Γ·((-4x(1-x))·g' + (2α/3)(3x-2)·g) ∘ cos²` (uses
`D_θΓ = (α/3)(6cos²θ-4)Γ`).  Hence with the polynomials `B₀ = 1-x`,
`B_{i+1} = -4x(1-x)B_i' + (2α/3)(3x-2)B_i` one has
`Lop^[i] (sin²θ Γ) = Γ(θ)·B_i(cos²θ, α)` for `i ≤ 4`, and the explicit `B_i`
(`i = 1..4`, in the split form `4x(1-x)·V_i + ∑_{k≥1}(α/3)^k P_{i,k}`) are
```
B₁ = 4x(1-x)·(1)                              + (α/3)·(-4 + 10x - 6x²)
B₂ = 4x(1-x)·(-4 + 8x)                        + (α/3)·(-56x + 128x² - 72x³)
                                              + (α/3)²·(16 - 64x + 84x² - 36x³)
B₃ = 4x(1-x)·(16 - 96x + 96x²)                + (α/3)·(288x - 1536x² + 2304x³ - 1056x⁴)
                                              + (α/3)²·(480x - 1776x² + 2160x³ - 864x⁴)
                                              + (α/3)³·(-64 + 352x - 720x² + 648x³ - 216x⁴)
B₄ = 4x(1-x)·(-64 + 896x - 2304x² + 1536x³)   + (α/3)·(-1408x + 15616x² - 45696x³ + 50688x⁴ - 19200x⁵)
                                              + (α/3)²·(-3072x + 24000x² - 58560x³ + 57792x⁴ - 20160x⁵)
                                              + (α/3)³·(-3328x + 17152x² - 32832x³ + 27648x⁴ - 8640x⁵)
                                              + (α/3)⁴·(256 - 1792x + 4992x² - 6912x³ + 4752x⁴ - 1296x⁵)
```
(`B₁` is also `= 4x(1-x) + (2α/3)(3x-2)(1-x)`, the direct computation).  Then
`|B_i(x,α)| ≤ 4x(1-x)·(coefficient sum of V_i) + α·∑_{k≥1}3^{-k}(coefficient sum of P_{i,k})`
(for `0 ≤ x ≤ 1`, `0 < α ≤ 1`, using `(α/3)^k ≤ α/3^k`), and the coefficient sums are
`≤ 4800` and `≤ 76000`, so `D = 10⁵` works. -/
theorem psiB_Lop_bound :
    ∃ D : ℝ, 0 < D ∧ ∀ α : ℝ, 0 < α → α ≤ 1 → ∀ i : ℕ, 1 ≤ i → i ≤ 4 →
      ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        |(Work.Spaces.Lop^[i] (fun θ : ℝ => Real.sin θ ^ 2 * Work.Spaces.Gam α θ)) θ|
          ≤ D * Work.Spaces.Gam α θ * (Real.sin (2 * θ) ^ 2 + α) := by
  refine ⟨10 ^ 6, by norm_num, ?_⟩
  intro α hα hα1 i hi1 hi4 θ hθ
  -- `Γ` is nonnegative, so it factors out of the absolute value
  have hGam0 : 0 ≤ Work.Spaces.Gam α θ :=
    (Work.Spaces.Gam_bounds α θ hα (Set.Ioo_subset_Icc_self hθ)).1
  -- the substitution `x = cos²θ` lies in `[0,1]`
  have hxc : Real.cos θ ^ 2 ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨sq_nonneg _, by linarith [Real.cos_sq_le_one θ]⟩
  -- `4x(1-x) = sin²(2θ)`
  have hsin2 : 4 * Real.cos θ ^ 2 * (1 - Real.cos θ ^ 2) = Real.sin (2 * θ) ^ 2 := by
    rw [Real.sin_two_mul]
    ring_nf
    rw [Real.sin_sq]
    ring
  have hb := Bang_bound i hi1 hi4 (Real.cos θ ^ 2) α hxc hα hα1
  rw [bang_iter α hα i hi4 θ hθ]
  calc |Work.Spaces.Gam α θ * Bang i (Real.cos θ ^ 2) α|
      = Work.Spaces.Gam α θ * |Bang i (Real.cos θ ^ 2) α| := by
        rw [abs_mul, abs_of_nonneg hGam0]
    _ ≤ Work.Spaces.Gam α θ
          * (10 ^ 6 * (α + 4 * Real.cos θ ^ 2 * (1 - Real.cos θ ^ 2))) :=
        mul_le_mul_of_nonneg_left hb hGam0
    _ = 10 ^ 6 * Work.Spaces.Gam α θ * (Real.sin (2 * θ) ^ 2 + α) := by
        rw [hsin2]
        ring

end Work.FTS.Nonlinear.Pieces.RNP26
