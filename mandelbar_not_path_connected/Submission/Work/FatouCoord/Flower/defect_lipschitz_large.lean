import Mathlib
import Submission.Work.FatouCoord.Setup
import Submission.Work.FatouCoord.Petal.repelling_defs
import Submission.Work.FatouCoord.Flower.LambdaBounds
import Submission.Work.FatouCoord.Repelling.defect_lipschitz

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Lipschitz continuity of the defect `ζ ↦ defect f a y ζ` on `{Re y < -1}`, `ζ = O(√‖y‖)`

`Repelling.defect_lipschitz` proves that `ζ ↦ defect f a w ζ` is `O(1/‖w‖²)`-Lipschitz on the
*unit* disc, for `w` in a far left half-plane `{Re w < -R}` with `R > 1/r`.

The flower construction needs the same estimate on the much larger discs
`{‖ζ‖ ≤ C √‖y‖}`, and only on the half-plane `{Re y < -1}` — the chart points occurring there
have large modulus but are not confined to a far left half-plane.

The proof is the mean value argument of `Repelling.defect_lipschitz`: the defect depends on `ζ`
only through `Φ (y + corr a y + ζ)` with `Φ z = wMap f z - z`, so its `ζ`-Lipschitz constant is
that of `Φ` on the segment joining the two points `y + corr a y + ζ`, `y + corr a y + ζ'`.  For
`‖y‖ ≥ N` large, `‖corr a y‖ = ‖(1 - a) Λ y‖ ≤ ‖y‖/4` (logarithmic growth of `Λ`) and
`C √‖y‖ ≤ ‖y‖/4`, so every point of such a segment has modulus `≥ ‖y‖/2 ≥ max (1/r) 4`; the
bound `‖deriv Φ‖ ≤ Kderiv A' / ‖z‖²` of `Estimate.deriv_wMap_bound_aux` therefore gives the
constant `4 Kderiv A' / ‖y‖²`.  (The hypothesis `Re y < -1` is not needed by this argument, it
only ensures that `y` lies on the side of the chart where `Λ` is defined and small.)
-/

open scoped Topology
open Set Filter Metric Function

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace Work.FatouCoord.Flower

open Work.FatouCoord

noncomputable section

/-- **The defect is Lipschitz in `ζ` on discs of radius `C √‖y‖`.**  For a parabolic germ
`f z = z + z ^ 2 * h z` with `ParabolicBounds f h a r A A'` and every `C ≥ 0` there are
`K > 0` and `N > 0` such that for all `y` with `Re y < -1` and `‖y‖ ≥ N` the map
`ζ ↦ defect f a y ζ` is `K / ‖y‖²`-Lipschitz on the disc `{‖ζ‖ ≤ C √‖y‖}`.  (One may take
`K = 4 Kderiv A'`, and `N` any threshold dominating the logarithmic growth threshold of `Λ`,
`16 C²`, `2/r + 1` and `9`.) -/
theorem defect_lipschitz_large {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ} (hb : Work.FatouCoord.ParabolicBounds f h a r A A') {C : ℝ} (hC : 0 ≤ C) : ∃ K N : ℝ, 0 < K ∧ 0 < N ∧ ∀ y ζ ζ' : ℂ, y.re < -1 → N ≤ ‖y‖ → ‖ζ‖ ≤ C * Real.sqrt ‖y‖ → ‖ζ'‖ ≤ C * Real.sqrt ‖y‖ → ‖Work.FatouCoord.Petal.defect f a y ζ - Work.FatouCoord.Petal.defect f a y ζ'‖ ≤ K * ‖ζ - ζ'‖ / ‖y‖ ^ 2 := by
  -- threshold beyond which `Λ` is dominated by `‖y‖/4`
  obtain ⟨T, hT⟩ := LambdaBounds.exists_lambda_growth (M := ‖(1 : ℂ) - a‖) (norm_nonneg _)
  -- the modulus threshold
  set N : ℝ := max (max T (16 * C ^ 2)) (max (1 + 2 * (1 / r)) 9) + 1 with hNdef
  have hT_le : T ≤ N := by
    rw [hNdef]
    have h1 : T ≤ max (max T (16 * C ^ 2)) (max (1 + 2 * (1 / r)) 9) :=
      le_trans (le_max_left _ _) (le_max_left _ _)
    linarith
  have h16_le : 16 * C ^ 2 ≤ N := by
    rw [hNdef]
    have h1 : 16 * C ^ 2 ≤ max (max T (16 * C ^ 2)) (max (1 + 2 * (1 / r)) 9) :=
      le_trans (le_max_right _ _) (le_max_left _ _)
    linarith
  have hr_le : 1 + 2 * (1 / r) ≤ N := by
    rw [hNdef]
    have h1 : (1 + 2 * (1 / r)) ≤ max (max T (16 * C ^ 2)) (max (1 + 2 * (1 / r)) 9) :=
      le_trans (le_max_left _ _) (le_max_right _ _)
    linarith
  have h9_le : (9 : ℝ) ≤ N := by
    rw [hNdef]
    have h1 : (9 : ℝ) ≤ max (max T (16 * C ^ 2)) (max (1 + 2 * (1 / r)) 9) :=
      le_trans (le_max_right _ _) (le_max_right _ _)
    linarith
  refine ⟨4 * Estimate.Kderiv A', N, ?_, ?_, ?_⟩
  · have hK : 0 < Estimate.Kderiv A' := by rw [Estimate.Kderiv]; nlinarith [hb.hA']
    linarith
  · linarith
  · intro y ζ ζ' _ hNy hζ hζ'
    have hKnn : 0 ≤ Estimate.Kderiv A' := Estimate.Kderiv_nonneg hb.hA'
    have hyn1 : 1 ≤ ‖y‖ := by linarith
    have hTy : T ≤ ‖y‖ := le_trans hT_le hNy
    have h16y : 16 * C ^ 2 ≤ ‖y‖ := le_trans h16_le hNy
    have hyn : 0 ≤ ‖y‖ := norm_nonneg y
    -- the correction `corr a y` is at most a quarter of `y`
    have hcorr : ‖Petal.corr a y‖ ≤ ‖y‖ / 4 := by
      rw [Petal.corr_apply, norm_mul]
      calc ‖(1 : ℂ) - a‖ * ‖Petal.Lambda y‖ ≤ ‖(1 : ℂ) - a‖ * (Real.log ‖y‖ + 2 * Real.pi) :=
            mul_le_mul_of_nonneg_left (LambdaBounds.norm_Lambda_le_log hyn1) (norm_nonneg _)
        _ ≤ ‖y‖ / 4 := hT ‖y‖ hTy
    -- and so is the allowed size of `ζ`
    have hCsqrt : C * Real.sqrt ‖y‖ ≤ ‖y‖ / 4 := by
      have hs : 0 ≤ Real.sqrt ‖y‖ := Real.sqrt_nonneg _
      have hsq : Real.sqrt ‖y‖ * Real.sqrt ‖y‖ = ‖y‖ := Real.mul_self_sqrt hyn
      have h4C : 4 * C ≤ Real.sqrt ‖y‖ := by
        have h := Real.sqrt_le_sqrt h16y
        have h4Cnn : 0 ≤ 4 * C := by linarith
        have he : Real.sqrt (16 * C ^ 2) = 4 * C := by
          rw [show (16 : ℝ) * C ^ 2 = (4 * C) * (4 * C) by ring, Real.sqrt_mul_self h4Cnn]
        rwa [he] at h
      nlinarith [h4C, hs, hsq]
    set x : ℂ := y + Petal.corr a y + ζ with hxdef
    set x' : ℂ := y + Petal.corr a y + ζ' with hx'def
    -- every point of the segment `[x,x']` is at distance `≥ ‖y‖/2` from the origin
    have hseg : ∀ z ∈ segment ℝ x x', ‖y‖ / 2 ≤ ‖z‖ := by
      intro z hz
      rw [segment_eq_image] at hz
      obtain ⟨θ, hθ, rfl⟩ := hz
      change ‖y‖ / 2 ≤ ‖(1 - θ) • x + θ • x'‖
      have hsm : (1 - θ) • x + θ • x' = (y + Petal.corr a y) + ((1 - θ) • ζ + θ • ζ') := by
        rw [hxdef, hx'def, Repelling.smul_segment_add_eq]
      rw [hsm]
      have hs1 : ‖(1 - θ) • ζ + θ • ζ'‖ ≤ C * Real.sqrt ‖y‖ := by
        have h1 : ‖(1 - θ) • ζ + θ • ζ'‖ ≤ ‖(1 - θ) • ζ‖ + ‖θ • ζ'‖ := norm_add_le _ _
        have h2 : ‖(1 - θ) • ζ‖ = (1 - θ) * ‖ζ‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith [hθ.2])]
        have h3 : ‖θ • ζ'‖ = θ * ‖ζ'‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hθ.1]
        have h4 : (1 - θ) * ‖ζ‖ ≤ (1 - θ) * (C * Real.sqrt ‖y‖) :=
          mul_le_mul_of_nonneg_left hζ (by linarith [hθ.2])
        have h5 : θ * ‖ζ'‖ ≤ θ * (C * Real.sqrt ‖y‖) :=
          mul_le_mul_of_nonneg_left hζ' hθ.1
        have h6 : (1 - θ) * (C * Real.sqrt ‖y‖) + θ * (C * Real.sqrt ‖y‖)
            = C * Real.sqrt ‖y‖ := by ring
        rw [h2, h3] at h1
        linarith
      have h1 : ‖y + Petal.corr a y‖ ≥ ‖y‖ - ‖Petal.corr a y‖ := by
        have h := norm_sub_le (y + Petal.corr a y) (Petal.corr a y)
        have h2 : (y + Petal.corr a y) - Petal.corr a y = y := by ring
        rw [h2] at h
        linarith
      have h3 : ‖(y + Petal.corr a y) + ((1 - θ) • ζ + θ • ζ')‖
          ≥ ‖y + Petal.corr a y‖ - ‖(1 - θ) • ζ + θ • ζ'‖ := by
        have h := norm_sub_le ((y + Petal.corr a y) + ((1 - θ) • ζ + θ • ζ'))
          ((1 - θ) • ζ + θ • ζ')
        have h2 : ((y + Petal.corr a y) + ((1 - θ) • ζ + θ • ζ'))
            - ((1 - θ) • ζ + θ • ζ') = y + Petal.corr a y := by ring
        rw [h2] at h
        linarith
      linarith
    have h4y2 : 4 ≤ ‖y‖ / 2 := by linarith
    have hry : 1 / r < ‖y‖ / 2 := by linarith
    have hdiff : ∀ z ∈ segment ℝ x x', DifferentiableAt ℂ (fun z => wMap f z - z) z := by
      intro z hz
      exact (Estimate.differentiableAt_wMap hb (lt_of_lt_of_le hry (hseg z hz))
        (le_trans h4y2 (hseg z hz))).sub differentiableAt_id
    have hbnd : ∀ z ∈ segment ℝ x x',
        ‖deriv (fun z => wMap f z - z) z‖ ≤ 4 * Estimate.Kderiv A' / ‖y‖ ^ 2 := by
      intro z hz
      have hzn : ‖y‖ / 2 ≤ ‖z‖ := hseg z hz
      have hz4 : 4 ≤ ‖z‖ := le_trans h4y2 hzn
      have hzr : 1 / r < ‖z‖ := lt_of_lt_of_le hry hzn
      have hsub : deriv (fun z => wMap f z - z) z = deriv (wMap f) z - 1 :=
        Repelling.deriv_sub_id (Estimate.differentiableAt_wMap hb hzr hz4)
      rw [hsub]
      have hb' := Estimate.deriv_wMap_bound_aux hb hzr hz4
      have hsq2 : (‖y‖ / 2) ^ 2 ≤ ‖z‖ ^ 2 := by nlinarith [hzn]
      calc ‖deriv (wMap f) z - 1‖ ≤ Estimate.Kderiv A' / ‖z‖ ^ 2 := hb'
        _ ≤ Estimate.Kderiv A' / (‖y‖ / 2) ^ 2 :=
              div_le_div_of_nonneg_left hKnn (by positivity) hsq2
        _ = 4 * Estimate.Kderiv A' / ‖y‖ ^ 2 := by
              rw [div_pow]; field_simp; ring
    -- the mean value inequality on the segment
    have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℂ)
      (f := fun z => wMap f z - z) (s := segment ℝ x x') (x := x) (y := x')
      (C := 4 * Estimate.Kderiv A' / ‖y‖ ^ 2) hdiff hbnd (convex_segment x x')
      (left_mem_segment ℝ x x') (right_mem_segment ℝ x x')
    -- the defect depends on `ζ` only through `wMap f (y + corr a y + ζ) - (y + corr a y + ζ)`
    have hdefect : Petal.defect f a y ζ - Petal.defect f a y ζ'
        = (wMap f x - x) - (wMap f x' - x') := by
      rw [Petal.defect_apply, Petal.defect_apply, ← hxdef, ← hx'def]
      ring
    have hxx : x' - x = ζ' - ζ := by rw [hx'def, hxdef]; ring
    calc ‖Petal.defect f a y ζ - Petal.defect f a y ζ'‖
        = ‖(wMap f x - x) - (wMap f x' - x')‖ := by rw [hdefect]
      _ = ‖(wMap f x' - x') - (wMap f x - x)‖ := norm_sub_rev _ _
      _ ≤ (4 * Estimate.Kderiv A' / ‖y‖ ^ 2) * ‖x' - x‖ := hmvt
      _ = 4 * Estimate.Kderiv A' / ‖y‖ ^ 2 * ‖ζ - ζ'‖ := by rw [hxx, norm_sub_rev]
      _ = 4 * Estimate.Kderiv A' * ‖ζ - ζ'‖ / ‖y‖ ^ 2 := by ring

end

end Work.FatouCoord.Flower
