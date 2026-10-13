import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.Nonlinear.Pieces.Rows
import Submission.Work.FTS.Nonlinear.Pieces.Basic
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row19.Split
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row19.HkSqZero
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row19.HkSq_VsW_mul_Gs_le
import Submission.Work.FTS.EllipticEst.HkSq_congr_open

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Row 19 of the `N4` table: the `V(Φ̃_*)·D_zF_*` piece

The piece is `N₃^{**} = -2α · V(Φ̃_*) · D_zF_*` (`Work.FTS.Nonlin.N3ss`,
`Work.FTS.Nonlinear.Pieces.RNP.Vs = Vop (PhiTs α Φs)`, `...Gs = Dz (Fstar α)`), and the claim is
`|N₃^{**}|_{ℋ⁴} ≤ K α³`.

The design's `𝒲^{4,∞}`-route (`WtoHQ` + the weighted product rule) is one order short of what
`StarPkg` provides (see `RNP/NOTES_row19.md`).  The proof below instead uses the *split*

  `V = V₀ + W`,   `V₀(θ) := V(0,θ)`,  `W := V - V₀`,

together with the two halves of the row that are available in the workspace:

* `RNP/row19/HkSq_VsW_mul_Gs_le` — the honest estimate for the part `W·D_zF_*` that vanishes at
  `z = 0`: `HkSq α 4 (W·D_zF_*) ≤ K₁ (max Cs 0)² α⁴` (from the `𝒲^{4,∞}`-fields of `StarPkg`
  and the Lipschitz bound `|W| ≤ M z`);
* `RNP/row19/HkSqZero` — the degenerate case: if `V(0,·)` does not vanish identically then the
  `ℋ⁴`-integrand of `V·D_zF_*` has a `z^{-2}` singularity, so the (Bochner) integral `HkSq` is
  `0` (`integral_undef`).

The two cases are glued by `HkSq_congr_open` (which sees only the open quadrant, where
`V = W` when `V₀ ≡ 0`), and the result is converted into the `ℋ⁴`-norm through
`Xn α (N₃^{**}) = 2α · Xn α (V·D_zF_*)` and `HkNorm = √HkSq`. -/
namespace Work.FTS.Nonlinear.Pieces.RNPV2

open Work.FTS.Nonlinear.Pieces.RNP (Vs Gs)

theorem row19 {α₂ Ci Ct Ce Cs : ℝ} (hN : Work.FTS.Nonlin.N4Norm Ci α₂) : ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn}, Work.FTS.Nonlin.GalClass α g → Work.FTS.Nonlin.StarPkg α Cs Φs → Work.FTS.Nonlin.EllPkgG α Ce g Φg → 0 < α → α ≤ 1 → α ≤ α₂ → Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N3ss α Φs) ≤ K * α ^ 3 := by
  obtain ⟨K₁, hK₁, hVsW⟩ := Work.FTS.Nonlinear.Pieces.RNP.row19.HkSq_VsW_mul_Gs_le
  refine ⟨2 * Real.sqrt K₁ * (max Cs 0 + 1), ?_, ?_⟩
  · have h1 : 0 < Real.sqrt K₁ := Real.sqrt_pos_of_pos hK₁
    have h2 : 0 < max Cs 0 + 1 := by
      have := le_max_right Cs (0 : ℝ); linarith
    exact mul_pos (mul_pos (by norm_num) h1) h2
  · intro α g Φs Φg _hGal hStar _hEll hα hα1 _hαα₂
    -- the `ℋ⁴`-square of `V(Φ̃_*)·D_zF_*`
    have hsq : Work.Spaces.HkSq α 4 (fun z θ => Vs α Φs z θ * Gs α z θ)
        ≤ K₁ * (max Cs 0) ^ 2 * α ^ 4 := by
      by_cases h0 : ∃ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), Vs α Φs 0 θ ≠ 0
      · -- `V(0,·) ≢ 0`: the integrand has a `z^{-2}` singularity, so `HkSq` is the junk value `0`
        rw [Work.FTS.Nonlinear.Pieces.RNP.row19.HkSqZero hα hStar h0]
        positivity
      · have h0' : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), Vs α Φs 0 θ = 0 := by
          intro θ hθ
          by_contra hne
          exact h0 ⟨θ, hθ, hne⟩
        -- `V = V₀ + W` with `V₀ ≡ 0` on the open quadrant, so `V·D_zF_* = W·D_zF_*` there
        rw [Work.FTS.EllipticEst.HkSq_congr_open α 4
          (f := fun z θ => Vs α Φs z θ * Gs α z θ)
          (g := fun z θ => Work.FTS.Nonlinear.Pieces.RNP.row19.VsW α Φs z θ * Gs α z θ)
          (fun z θ _ hθ1 hθ2 => by
            have hz0 : Vs α Φs 0 θ = 0 := h0' θ ⟨hθ1, hθ2⟩
            rw [Work.FTS.Nonlinear.Pieces.RNP.row19.VsW_apply]
            change Vs α Φs z θ * Gs α z θ
              = (Vs α Φs z θ - Vs α Φs 0 θ) * Gs α z θ
            rw [hz0, sub_zero])]
        exact hVsW hStar hα hα1
    -- pass to the norm
    have hnorm : Work.FTS.Nonlin.Xn α (fun z θ => Vs α Φs z θ * Gs α z θ)
        ≤ Real.sqrt K₁ * max Cs 0 * α ^ 2 := by
      rw [Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm]
      refine (Real.sqrt_le_sqrt hsq).trans (le_of_eq ?_)
      have harg : K₁ * (max Cs 0) ^ 2 * α ^ 4
          = (Real.sqrt K₁ * max Cs 0 * α ^ 2) ^ 2 := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hK₁.le]
        ring
      rw [harg, Real.sqrt_sq (mul_nonneg (mul_nonneg (Real.sqrt_nonneg K₁)
        (le_max_right Cs 0)) (sq_nonneg α))]
    calc Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N3ss α Φs)
        = 2 * α * Work.FTS.Nonlin.Xn α (fun z θ => Vs α Φs z θ * Gs α z θ) :=
          Work.FTS.Nonlinear.Pieces.RNP.xn_N3ss_of_nonneg hα.le Φs
      _ ≤ 2 * α * (Real.sqrt K₁ * max Cs 0 * α ^ 2) :=
          mul_le_mul_of_nonneg_left hnorm (by linarith)
      _ = 2 * Real.sqrt K₁ * max Cs 0 * α ^ 3 := by ring
      _ ≤ 2 * Real.sqrt K₁ * (max Cs 0 + 1) * α ^ 3 := by
          have hmax : max Cs 0 ≤ max Cs 0 + 1 := by linarith [le_max_right Cs (0 : ℝ)]
          have h2 : (0 : ℝ) ≤ 2 * Real.sqrt K₁ := by positivity
          have h3 : (0 : ℝ) ≤ α ^ 3 := by positivity
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmax h2) h3

end Work.FTS.Nonlinear.Pieces.RNPV2
