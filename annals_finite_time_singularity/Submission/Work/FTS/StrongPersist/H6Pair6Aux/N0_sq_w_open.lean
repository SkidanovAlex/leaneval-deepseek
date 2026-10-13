/-
# `H6Pair6Aux/N0_sq_w_open` — the pointwise weighted bound for `N₀` in the open class

This is the `SmoothOpen`-analogue of the pointwise estimate proved inside
`Work.FTS.Nonlinear.Pieces.rl0_bound` (the level-four row `rl0` of the §8 table).  The class
hypothesis of that proof, `Work.FTS.LocData.SmoothQuad g` (`C^∞` on the half strip `z > -1`), is
replaced here by `Work.FTS.EllipticEst.SmoothOpen g` (`C^∞` on the open quadrant) together with
the *assumed* bound `|L₁₂(g)| ≤ 3 |g|_{ℋ⁴}` (which in `rl0_bound` was derived from the class).

The only place where the smoothness class enters is the additivity of `∂_θ`, `∂_z` and `D_z` on
the total profile `F = F_* + g`; it is now supplied by
`Work.FTS.NonlinRows.Rl1.openSlice_pth_add` / `openSlice_pz_add` (the open-quadrant versions of
`pth_add_of_smoothQuad` / `pz_add_of_smoothQuad`).  Everything else — the collapse
`N₀₁ + N₀₂ = 8 α² c₂(θ) z² Γ/(c (1+z)⁴)` (`Work.Construction.N0_first_two_eq'`), the explicit
shape of `F_*` (`Work.FTS.Nonlinear.Pieces.Fstar_shape`) and the slotwise domination of `g`,
`D_θg`, `D_zg` by the `ℋ⁴`-integrand — is unconditional.

The two coefficients `A₀`, `B₀` are the ones exposed in
`Submission/Work/FTS/StrongPersist/H6Pair6Aux/Rl0Defs.lean`.
-/
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.Rl0Defs
import Submission.Work.FTS.Nonlinear.Pieces.rowsAux
import Submission.Work.FTS.NonlinRows.Rl1.splitOpen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-! ## Two bookkeeping lemmas about the Hardy weight `w`

(`private` copies of the identically named lemmas of `Work.FTS.Nonlinear.Pieces.rowsAux`,
which are not exported.) -/

/-- The exact cancellation `(r/(1+r)²)²·w r = (1/(1+r))²`. -/
private lemma n0sw_sq_div_shape_eq {c r : ℝ} (hr : 0 < r) :
    c ^ 2 * (r / (1 + r) ^ 2) ^ 2 * Work.Spaces.w r = c ^ 2 * (1 / (1 + r)) ^ 2 := by
  rw [Work.Spaces.w]
  field_simp

/-- The bound `(r²/(1+r)⁴)²·w r ≤ (1/(1+r))²`. -/
private lemma n0sw_sq_div_shape_le {c r : ℝ} (hr : 0 < r) :
    c ^ 2 * (r ^ 2 / (1 + r) ^ 4) ^ 2 * Work.Spaces.w r ≤ c ^ 2 * (1 / (1 + r)) ^ 2 := by
  rw [Work.Spaces.w]
  have h1r : 0 < 1 + r := by linarith
  have h4 : r ^ 2 ≤ (1 + r) ^ 4 := by
    nlinarith [sq_nonneg r, sq_nonneg (1 + r), hr.le, sq_nonneg ((1 + r) ^ 2 - r)]
  have hgoal : r ^ 2 / (1 + r) ^ 6 ≤ (1 / (1 + r)) ^ 2 := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (1 + r) ^ 6)]
    have hsimp : (1 / (1 + r)) ^ 2 * (1 + r) ^ 6 = (1 + r) ^ 4 := by field_simp
    rw [hsimp]
    exact h4
  calc c ^ 2 * (r ^ 2 / (1 + r) ^ 4) ^ 2 * ((1 + r) ^ 2 / r ^ 2)
      = c ^ 2 * (r ^ 2 / (1 + r) ^ 6) := by field_simp
    _ ≤ c ^ 2 * (1 / (1 + r)) ^ 2 := mul_le_mul_of_nonneg_left hgoal (sq_nonneg _)

/-! ## The pointwise bound -/

theorem N0_sq_w_open {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {g : Work.FTS.Galerkin.Fn}
    (hso : Work.FTS.EllipticEst.SmoothOpen g)
    (hL12g : ∀ z : ℝ, 0 ≤ z → |Work.Construction.L12 g z| ≤ 3 * Work.FTS.Nonlin.Xn α g) :
    ∀ r ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (Work.Construction.N0 α (Work.Construction.Ftot α g) g r θ) ^ 2 * Work.Spaces.w r
        ≤ 7 * (Work.FTS.StrongPersist.H6Pair6Aux.A₀ α (Work.FTS.Nonlin.Xn α g)
                * Work.Spaces.HkIntegrand α 4 g r θ
              + Work.FTS.StrongPersist.H6Pair6Aux.B₀ α (Work.FTS.Nonlin.Xn α g)
                * (1 / (1 + r)) ^ 2) := by
  -- two global facts about the data
  obtain ⟨hc1, hc2⟩ := Work.Spaces.c_bounds α hα hα1
  have hc0 : 0 < Work.Spaces.c α := by linarith
  have hFstar : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar α) :=
    Work.FTS.OpenPkg.smoothOpen_of_smoothQuad (Work.FTS.LocData.SmoothQuad_Fstar α)
  -- the explicit shape of `F_*` and its first derivatives
  have hDthF : ∀ z : ℝ, 0 ≤ z → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.Dth (Work.Construction.Fstar α) z θ| ≤ 40 * α ^ 2 * (z / (1 + z) ^ 2) :=
    (Work.FTS.Nonlinear.Pieces.Fstar_shape hα hα1).2.1
  have hDzF : ∀ z : ℝ, 0 ≤ z → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.Dz (Work.Construction.Fstar α) z θ| ≤ 40 * α * (z / (1 + z) ^ 2) :=
    (Work.FTS.Nonlinear.Pieces.Fstar_shape hα hα1).2.2
  have hc2m : ∀ θ : ℝ, |Work.Construction.c2m θ| ≤ 2 := fun θ => by
    have hs1 : Real.sin θ ^ 2 ≤ 1 := by
      nlinarith [Real.sin_le_one θ, Real.neg_one_le_sin θ, sq_nonneg (Real.sin θ)]
    rw [Work.Construction.c2m, abs_le]
    constructor
    · nlinarith [Real.neg_one_le_cos (2 * θ), hs1]
    · nlinarith [Real.cos_le_one (2 * θ), sq_nonneg (Real.sin θ)]
  -- the collapse of the two `F_*`-only terms of `N₀`
  have hN0bd : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |(3 / (2 * α)) * Work.Construction.s2 θ
          * Work.Construction.L12 (Work.Construction.Fstar α) z
          * Work.Spaces.pth (Work.Construction.Fstar α) z θ
        - Work.Construction.c2m θ * Work.Construction.L12 (Work.Construction.Fstar α) z
          * Work.Spaces.Dz (Work.Construction.Fstar α) z θ|
        ≤ 160 * α ^ 2 * (z ^ 2 / (1 + z) ^ 4) := by
    intro z hz θ hθ
    have hz0 : 0 ≤ z := le_of_lt hz
    have h1z : 0 < 1 + z := by linarith
    have hden : 0 < Work.Spaces.c α * (1 + z) ^ 4 := mul_pos hc0 (pow_pos h1z 4)
    obtain ⟨hG0, hG1⟩ := Work.Spaces.Gam_bounds α θ hα ⟨hθ.1.le, hθ.2.le⟩
    have hnum : |8 * α ^ 2 * Work.Construction.c2m θ * z ^ 2 * Work.Spaces.Gam α θ|
        ≤ 16 * α ^ 2 * z ^ 2 := by
      have hΓ : |Work.Spaces.Gam α θ| ≤ 1 := by rw [abs_of_nonneg hG0]; exact hG1
      calc |8 * α ^ 2 * Work.Construction.c2m θ * z ^ 2 * Work.Spaces.Gam α θ|
          = 8 * α ^ 2 * |Work.Construction.c2m θ| * z ^ 2 * |Work.Spaces.Gam α θ| := by
            rw [show 8 * α ^ 2 * Work.Construction.c2m θ * z ^ 2 * Work.Spaces.Gam α θ
                = (8 * α ^ 2) * Work.Construction.c2m θ * z ^ 2 * Work.Spaces.Gam α θ
                  from by ring]
            simp only [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 8 * α ^ 2),
              abs_of_nonneg (sq_nonneg z)]
            try ring
        _ ≤ 8 * α ^ 2 * 2 * z ^ 2 * 1 := by
            calc 8 * α ^ 2 * |Work.Construction.c2m θ| * z ^ 2 * |Work.Spaces.Gam α θ|
                ≤ 8 * α ^ 2 * 2 * z ^ 2 * |Work.Spaces.Gam α θ| :=
                  mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_left (hc2m θ) (by positivity)) (sq_nonneg z))
                    (abs_nonneg _)
              _ ≤ 8 * α ^ 2 * 2 * z ^ 2 * 1 := mul_le_mul_of_nonneg_left hΓ (by positivity)
        _ = 16 * α ^ 2 * z ^ 2 := by ring
    have hfin : 160 * α ^ 2 * (z ^ 2 / (1 + z) ^ 4) * (Work.Spaces.c α * (1 + z) ^ 4)
        = 160 * α ^ 2 * z ^ 2 * Work.Spaces.c α := by
      field_simp
      try ring
    rw [Work.Construction.N0_first_two_eq' (α := α) (z := z) (θ := θ) hα hα1 hz0
        ⟨hθ.1.le, hθ.2.le⟩,
      abs_div, abs_of_pos hden, div_le_iff₀ hden]
    rw [hfin]
    have hnn : (0 : ℝ) ≤ α ^ 2 * z ^ 2 := by positivity
    nlinarith [hnum, hc1, hnn, sq_nonneg α, sq_nonneg z, hα.le]
  intro r hr θ hθ
  have hr0 : 0 ≤ r := le_of_lt hr
  have h1r : 0 < 1 + r := by linarith
  have hw1 : 1 ≤ Work.Spaces.w r := by
    have hr' : (0 : ℝ) < r := hr
    rw [Work.Spaces.w, one_le_div (sq_pos_of_pos hr')]
    nlinarith
  -- the two additivity identities on the open quadrant
  have hpth : Work.Spaces.pth (Work.Construction.Ftot α g) r θ
      = Work.Spaces.pth (Work.Construction.Fstar α) r θ + Work.Spaces.pth g r θ :=
    Work.FTS.NonlinRows.Rl1.openSlice_pth_add hFstar hso hr hθ
  have hI2 : Work.Spaces.Dz (Work.Construction.Ftot α g) r θ
      = Work.Spaces.Dz (Work.Construction.Fstar α) r θ + Work.Spaces.Dz g r θ :=
    Work.FTS.Nonlinear.Pieces.Dz_add_of_diff
      (Work.FTS.NonlinRows.Rl1.openSlice_pz_add hFstar hso hr hθ)
  have hL12F : Work.Construction.L12 (Work.Construction.Fstar α) r = 2 * α / (1 + r) :=
    Work.Construction.L12_Fstar_eq hα hα1 hr0
  -- the numerical size of `|g|_{ℋ⁴}`
  set X : ℝ := Work.FTS.Nonlin.Xn α g with hX
  have hL12gX : |Work.Construction.L12 g r| ≤ 3 * X := by
    rw [hX]
    exact hL12g r hr0
  -- ## the decomposition and the seven termwise bounds
  set W : ℝ := Work.Spaces.w r with hWdef
  have hW1 : 1 ≤ W := by rw [hWdef]; exact hw1
  have hW0 : 0 ≤ W := le_trans zero_le_one hW1
  set Hk : ℝ := Work.Spaces.HkIntegrand α 4 g r θ with hHkdef
  set T0 : ℝ := (3 / (2 * α)) * Work.Construction.s2 θ
        * Work.Construction.L12 (Work.Construction.Fstar α) r
        * Work.Spaces.pth (Work.Construction.Fstar α) r θ
      - Work.Construction.c2m θ * Work.Construction.L12 (Work.Construction.Fstar α) r
        * Work.Spaces.Dz (Work.Construction.Fstar α) r θ with hT0def
  set T1 : ℝ := (1 / α) * Work.Construction.L12 g r * g r θ with hT1def
  set T2 : ℝ := (3 / (2 * α)) * Work.Construction.s2 θ * Work.Construction.L12 g r
        * Work.Spaces.pth (Work.Construction.Fstar α) r θ with hT2def
  set T3 : ℝ := (3 / (2 * α)) * Work.Construction.s2 θ * Work.Construction.L12 g r
        * Work.Spaces.pth g r θ with hT3def
  set T4 : ℝ := -(Work.Construction.c2m θ) * Work.Construction.L12 g r
        * Work.Spaces.Dz (Work.Construction.Fstar α) r θ with hT4def
  set T5 : ℝ := -(Work.Construction.c2m θ) * Work.Construction.L12 g r
        * Work.Spaces.Dz g r θ with hT5def
  set T6 : ℝ := -(Work.Construction.c2m θ)
        * Work.Construction.L12 (Work.Construction.Fstar α) r
        * Work.Spaces.Dz g r θ with hT6def
  have hexp : Work.Construction.N0 α (Work.Construction.Ftot α g) g r θ
      = T0 + T1 + T2 + T3 + T4 + T5 + T6 := by
    rw [hT0def, hT1def, hT2def, hT3def, hT4def, hT5def, hT6def]
    simp only [Work.Construction.N0]
    rw [hpth, hI2]
    ring
  have h3L : (Work.Construction.L12 g r) ^ 2 ≤ (3 * X) ^ 2 := by
    nlinarith [hL12gX, abs_nonneg (Work.Construction.L12 g r),
      sq_abs (Work.Construction.L12 g r)]
  have hc2sq : (Work.Construction.c2m θ) ^ 2 ≤ (2 : ℝ) ^ 2 := by
    nlinarith [hc2m θ, abs_nonneg (Work.Construction.c2m θ),
      sq_abs (Work.Construction.c2m θ)]
  have hb0 : T0 ^ 2 * W ≤ (160 * α ^ 2) ^ 2 * (1 / (1 + r)) ^ 2 := by
    have h := hN0bd r hr θ hθ
    rw [← hT0def] at h
    have h2 : T0 ^ 2 ≤ (160 * α ^ 2 * (r ^ 2 / (1 + r) ^ 4)) ^ 2 := by
      nlinarith [h, abs_nonneg T0, sq_abs T0]
    calc T0 ^ 2 * W ≤ (160 * α ^ 2 * (r ^ 2 / (1 + r) ^ 4)) ^ 2 * W :=
          mul_le_mul_of_nonneg_right h2 hW0
      _ = (160 * α ^ 2) ^ 2 * (r ^ 2 / (1 + r) ^ 4) ^ 2 * W := by ring
      _ ≤ (160 * α ^ 2) ^ 2 * (1 / (1 + r)) ^ 2 := by
          rw [hWdef]
          exact n0sw_sq_div_shape_le hr
  have hb1 : T1 ^ 2 * W ≤ (9 * X ^ 2 / α ^ 2) * Hk := by
    rw [hT1def]
    have hg2 : (g r θ) ^ 2 * W ≤ Hk := by
      have h := Work.FTS.Nonlinear.Pieces.g_sq_mul_w_sq_le_HkIntegrand α g hr hθ
      rw [← hWdef, ← hHkdef] at h
      have hWsq : W ≤ W ^ 2 := by nlinarith [hW1]
      have hstep : (g r θ) ^ 2 * W ≤ (g r θ) ^ 2 * W ^ 2 :=
        mul_le_mul_of_nonneg_left hWsq (sq_nonneg (g r θ))
      linarith [h, hstep]
    have hkey : ((1 / α) * Work.Construction.L12 g r * g r θ) ^ 2 * W
        = (1 / α) ^ 2 * (Work.Construction.L12 g r) ^ 2 * ((g r θ) ^ 2 * W) := by ring
    rw [hkey]
    calc (1 / α) ^ 2 * (Work.Construction.L12 g r) ^ 2 * ((g r θ) ^ 2 * W)
        ≤ (1 / α) ^ 2 * (3 * X) ^ 2 * Hk := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left h3L (sq_nonneg _)) hg2
            (mul_nonneg (sq_nonneg _) hW0)
            (mul_nonneg (sq_nonneg (1 / α)) (sq_nonneg (3 * X)))
      _ = (9 * X ^ 2 / α ^ 2) * Hk := by ring_nf
  have hb2 : T2 ^ 2 * W ≤ (180 * α * X) ^ 2 * (1 / (1 + r)) ^ 2 := by
    have hw : (Work.Spaces.Dth (Work.Construction.Fstar α) r θ) ^ 2 * W
        ≤ (40 * α ^ 2) ^ 2 * (1 / (1 + r)) ^ 2 := by
      have h := hDthF r hr0 θ ⟨hθ.1.le, hθ.2.le⟩
      have h5 : (Work.Spaces.Dth (Work.Construction.Fstar α) r θ) ^ 2
          ≤ (40 * α ^ 2 * (r / (1 + r) ^ 2)) ^ 2 := by
        nlinarith [h, abs_nonneg (Work.Spaces.Dth (Work.Construction.Fstar α) r θ),
          sq_abs (Work.Spaces.Dth (Work.Construction.Fstar α) r θ)]
      calc (Work.Spaces.Dth (Work.Construction.Fstar α) r θ) ^ 2 * W
          ≤ (40 * α ^ 2 * (r / (1 + r) ^ 2)) ^ 2 * W :=
            mul_le_mul_of_nonneg_right h5 hW0
        _ = (40 * α ^ 2) ^ 2 * (r / (1 + r) ^ 2) ^ 2 * W := by ring
        _ ≤ (40 * α ^ 2) ^ 2 * (1 / (1 + r)) ^ 2 := by
            rw [hWdef]
            exact le_of_eq (n0sw_sq_div_shape_eq (c := 40 * α ^ 2) hr)
    have hkey : T2 ^ 2 * W = (3 / (2 * α)) ^ 2 * (Work.Construction.L12 g r) ^ 2
          * ((Work.Spaces.Dth (Work.Construction.Fstar α) r θ) ^ 2 * W) := by
      rw [hT2def]
      simp only [Work.Spaces.Dth, Work.Construction.s2]
      ring
    rw [hkey]
    calc (3 / (2 * α)) ^ 2 * (Work.Construction.L12 g r) ^ 2
            * ((Work.Spaces.Dth (Work.Construction.Fstar α) r θ) ^ 2 * W)
        ≤ (3 / (2 * α)) ^ 2 * (3 * X) ^ 2 * ((40 * α ^ 2) ^ 2 * (1 / (1 + r)) ^ 2) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left h3L (sq_nonneg _)) hw
            (mul_nonneg (sq_nonneg _) hW0)
            (mul_nonneg (sq_nonneg (3 / (2 * α))) (sq_nonneg (3 * X)))
      _ = (180 * α * X) ^ 2 * (1 / (1 + r)) ^ 2 := by
          have hαne : α ≠ 0 := ne_of_gt hα
          field_simp
          ring
  have hb3 : T3 ^ 2 * W ≤ (81 * X ^ 2 / (4 * α ^ 2)) * Hk := by
    have hw : (Work.Spaces.Dth g r θ) ^ 2 * W ≤ Hk := by
      have h := Work.FTS.Nonlinear.Pieces.dth_sq_mul_w_le_HkIntegrand α g hα hr hθ
      rw [← hWdef, ← hHkdef] at h
      exact h
    have hkey : T3 ^ 2 * W = (3 / (2 * α)) ^ 2 * (Work.Construction.L12 g r) ^ 2
          * ((Work.Spaces.Dth g r θ) ^ 2 * W) := by
      rw [hT3def]
      simp only [Work.Spaces.Dth, Work.Construction.s2]
      ring
    rw [hkey]
    calc (3 / (2 * α)) ^ 2 * (Work.Construction.L12 g r) ^ 2
            * ((Work.Spaces.Dth g r θ) ^ 2 * W)
        ≤ (3 / (2 * α)) ^ 2 * (3 * X) ^ 2 * Hk := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left h3L (sq_nonneg _)) hw
            (mul_nonneg (sq_nonneg _) hW0)
            (mul_nonneg (sq_nonneg (3 / (2 * α))) (sq_nonneg (3 * X)))
      _ = (81 * X ^ 2 / (4 * α ^ 2)) * Hk := by ring_nf
  have hb4 : T4 ^ 2 * W ≤ (240 * α * X) ^ 2 * (1 / (1 + r)) ^ 2 := by
    have hw : (Work.Spaces.Dz (Work.Construction.Fstar α) r θ) ^ 2 * W
        ≤ (40 * α) ^ 2 * (1 / (1 + r)) ^ 2 := by
      have h := hDzF r hr0 θ ⟨hθ.1.le, hθ.2.le⟩
      have h5 : (Work.Spaces.Dz (Work.Construction.Fstar α) r θ) ^ 2
          ≤ (40 * α * (r / (1 + r) ^ 2)) ^ 2 := by
        nlinarith [h, abs_nonneg (Work.Spaces.Dz (Work.Construction.Fstar α) r θ),
          sq_abs (Work.Spaces.Dz (Work.Construction.Fstar α) r θ)]
      calc (Work.Spaces.Dz (Work.Construction.Fstar α) r θ) ^ 2 * W
          ≤ (40 * α * (r / (1 + r) ^ 2)) ^ 2 * W :=
            mul_le_mul_of_nonneg_right h5 hW0
        _ = (40 * α) ^ 2 * (r / (1 + r) ^ 2) ^ 2 * W := by ring
        _ ≤ (40 * α) ^ 2 * (1 / (1 + r)) ^ 2 := by
            rw [hWdef]
            exact le_of_eq (n0sw_sq_div_shape_eq (c := 40 * α) hr)
    have hkey : T4 ^ 2 * W = (Work.Construction.c2m θ) ^ 2
          * (Work.Construction.L12 g r) ^ 2
          * ((Work.Spaces.Dz (Work.Construction.Fstar α) r θ) ^ 2 * W) := by
      rw [hT4def]
      ring
    rw [hkey]
    calc (Work.Construction.c2m θ) ^ 2 * (Work.Construction.L12 g r) ^ 2
            * ((Work.Spaces.Dz (Work.Construction.Fstar α) r θ) ^ 2 * W)
        ≤ (2 : ℝ) ^ 2 * (3 * X) ^ 2 * ((40 * α) ^ 2 * (1 / (1 + r)) ^ 2) := by
          refine mul_le_mul (mul_le_mul hc2sq h3L (sq_nonneg _) (by norm_num)) hw
            (mul_nonneg (sq_nonneg _) hW0)
            (mul_nonneg (sq_nonneg (2 : ℝ)) (sq_nonneg (3 * X)))
      _ = (240 * α * X) ^ 2 * (1 / (1 + r)) ^ 2 := by ring_nf
  have hb5 : T5 ^ 2 * W ≤ (36 * X ^ 2) * Hk := by
    have hw : (Work.Spaces.Dz g r θ) ^ 2 * W ≤ Hk := by
      have h := Work.FTS.Nonlinear.Pieces.dz_sq_mul_w_le_HkIntegrand α g hr hθ
      rw [← hWdef, ← hHkdef] at h
      exact h
    have hkey : T5 ^ 2 * W = (Work.Construction.c2m θ) ^ 2
          * (Work.Construction.L12 g r) ^ 2
          * ((Work.Spaces.Dz g r θ) ^ 2 * W) := by
      rw [hT5def]
      ring
    rw [hkey]
    calc (Work.Construction.c2m θ) ^ 2 * (Work.Construction.L12 g r) ^ 2
            * ((Work.Spaces.Dz g r θ) ^ 2 * W)
        ≤ (2 : ℝ) ^ 2 * (3 * X) ^ 2 * Hk := by
          refine mul_le_mul (mul_le_mul hc2sq h3L (sq_nonneg _) (by norm_num)) hw
            (mul_nonneg (sq_nonneg _) hW0)
            (mul_nonneg (sq_nonneg (2 : ℝ)) (sq_nonneg (3 * X)))
      _ = (36 * X ^ 2) * Hk := by ring
  have hb6 : T6 ^ 2 * W ≤ (16 * α ^ 2) * Hk := by
    have hw : (Work.Spaces.Dz g r θ) ^ 2 * W ≤ Hk := by
      have h := Work.FTS.Nonlinear.Pieces.dz_sq_mul_w_le_HkIntegrand α g hr hθ
      rw [← hWdef, ← hHkdef] at h
      exact h
    have h2a : (2 * α / (1 + r)) ^ 2 ≤ (2 * α) ^ 2 := by
      have h0 : 0 ≤ 1 / (1 + r) := div_nonneg zero_le_one h1r.le
      have hle : 1 / (1 + r) ≤ 1 := by rw [div_le_one h1r]; linarith
      have hsq : (1 / (1 + r)) ^ 2 ≤ 1 := by nlinarith [h0, hle]
      calc (2 * α / (1 + r)) ^ 2 = (2 * α) ^ 2 * (1 / (1 + r)) ^ 2 := by ring_nf
        _ ≤ (2 * α) ^ 2 * 1 := mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
        _ = (2 * α) ^ 2 := by ring
    have hkey : T6 ^ 2 * W = (Work.Construction.c2m θ) ^ 2 * (2 * α / (1 + r)) ^ 2
          * ((Work.Spaces.Dz g r θ) ^ 2 * W) := by
      rw [hT6def, hL12F]
      ring
    rw [hkey]
    calc (Work.Construction.c2m θ) ^ 2 * (2 * α / (1 + r)) ^ 2
            * ((Work.Spaces.Dz g r θ) ^ 2 * W)
        ≤ (2 : ℝ) ^ 2 * (2 * α) ^ 2 * Hk := by
          refine mul_le_mul (mul_le_mul hc2sq h2a (sq_nonneg _) (by norm_num)) hw
            (mul_nonneg (sq_nonneg _) hW0)
            (mul_nonneg (sq_nonneg (2 : ℝ)) (sq_nonneg (2 * α)))
      _ = (16 * α ^ 2) * Hk := by ring
  -- ## the sum of seven squares
  have hcs7 : (T0 + T1 + T2 + T3 + T4 + T5 + T6) ^ 2
      ≤ 7 * (T0 ^ 2 + T1 ^ 2 + T2 ^ 2 + T3 ^ 2 + T4 ^ 2 + T5 ^ 2 + T6 ^ 2) := by
    have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
      (f := fun i : Fin 7 => ![T0, T1, T2, T3, T4, T5, T6] i)
    simpa [Fin.sum_univ_seven, Matrix.cons_val_zero, Matrix.cons_val_succ] using h
  -- ## the final assembly
  have hmain : (Work.Construction.N0 α (Work.Construction.Ftot α g) g r θ) ^ 2 * W
      ≤ 7 * (A₀ α X * Hk + B₀ α X * (1 / (1 + r)) ^ 2) := by
    calc (Work.Construction.N0 α (Work.Construction.Ftot α g) g r θ) ^ 2 * W
        = (T0 + T1 + T2 + T3 + T4 + T5 + T6) ^ 2 * W := by rw [hexp]
      _ ≤ 7 * ((T0 ^ 2 + T1 ^ 2 + T2 ^ 2 + T3 ^ 2 + T4 ^ 2 + T5 ^ 2 + T6 ^ 2) * W) := by
          calc (T0 + T1 + T2 + T3 + T4 + T5 + T6) ^ 2 * W
              ≤ (7 * (T0 ^ 2 + T1 ^ 2 + T2 ^ 2 + T3 ^ 2 + T4 ^ 2 + T5 ^ 2 + T6 ^ 2)) * W :=
                mul_le_mul_of_nonneg_right hcs7 hW0
            _ = 7 * ((T0 ^ 2 + T1 ^ 2 + T2 ^ 2 + T3 ^ 2 + T4 ^ 2 + T5 ^ 2 + T6 ^ 2) * W) := by
                ring
      _ ≤ 7 * (A₀ α X * Hk + B₀ α X * (1 / (1 + r)) ^ 2) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          rw [A₀, B₀]
          nlinarith [hb0, hb1, hb2, hb3, hb4, hb5, hb6]
  exact hmain

end Work.FTS.StrongPersist.H6Pair6Aux
