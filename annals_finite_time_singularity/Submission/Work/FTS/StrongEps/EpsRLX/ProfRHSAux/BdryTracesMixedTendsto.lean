import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.H2.STBasic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsRLX.ProfRHSAux

open scoped Real Topology
open Filter

/-! ## The endpoint limits of a mixed derivative, from the boundary traces

The angular clause of `Work.FTS.Nonlin.BdryTraces α k f` says, for the slot `(a,b)` with
`a + b ≤ k`, that at both endpoints `θ = 0⁺` and `θ = (π/2)⁻` one has

  `sin(2θ)^{1-γ}·(D_z^b D_θ^a f (z,θ))² ⟶ 0`,   `γ = Work.Spaces.gam α`.

Since `γ = 1 + α/10 > 1` when `α > 0`, the weight `sin(2θ)^{1-γ}` *diverges* at the endpoints
(`sin(2θ) → 0` there), so the square of the slot has to vanish faster than `sin(2θ)^{γ-1}`:
multiplying the trace by the (bounded, in fact `≤ 1` near the endpoints) factor
`sin(2θ)^{γ-1}` exhibits the square of the slot as tending to `0`.  Taking square roots gives the
slot itself.

These two one-sided `θ`-facts are the content of this file, together with the target lemma, which
reads them off from the two angular conjuncts of `BdryTraces`. -/

/-- **A diverging weight kills the function (right endpoint).**  If `γ > 1` and
`sin (2θ) ^ (1 - γ) · X θ ^ 2 → 0` as `θ → 0⁺`, then `X θ → 0` as `θ → 0⁺`.

On the neighbourhood `(0, π/4)` of `0⁺` the two weights multiply to `1`
(`Real.rpow_add`, both bases positive), so `sin(2θ)^{γ-1}·(sin(2θ)^{1-γ}·X θ ^ 2) = X θ ^ 2`;
the left-hand side tends to `0·0 = 0` because `sin(2θ)^{γ-1} → 0` there
(`Work.FTS.H2.tendsto_sin_rpow_zero_right`).  Finally `X ↦ |X| = √(X²)` and
`tendsto_zero_iff_norm_tendsto_zero`. -/
theorem tendsto_zero_of_sin_rpow_mul_sq_right {γ : ℝ} (hγ : 1 < γ) {X : ℝ → ℝ}
    (h : Filter.Tendsto (fun θ : ℝ => Real.sin (2 * θ) ^ (1 - γ) * X θ ^ 2)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)) :
    Filter.Tendsto X (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  have hpos : 0 < γ - 1 := by linarith
  have hmul : Filter.Tendsto (fun θ : ℝ => Real.sin (2 * θ) ^ (γ - 1)
      * (Real.sin (2 * θ) ^ (1 - γ) * X θ ^ 2))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    simpa using (Work.FTS.H2.tendsto_sin_rpow_zero_right (γ - 1) hpos).mul h
  -- On a right neighbourhood of `0` the two weights multiply to `1`.
  have hsplit : (fun θ : ℝ => Real.sin (2 * θ) ^ (γ - 1)
      * (Real.sin (2 * θ) ^ (1 - γ) * X θ ^ 2))
      =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)] (fun θ : ℝ => X θ ^ 2) := by
    filter_upwards [self_mem_nhdsWithin,
      Ioo_mem_nhdsGT (show (0 : ℝ) < π / 4 by positivity)] with θ hθ hlt
    have hs : 0 < Real.sin (2 * θ) :=
      Work.FTS.H2.sin_two_pos_of_Ioo ⟨hθ, by linarith [hlt.2, Real.pi_pos]⟩
    rw [← mul_assoc, ← Real.rpow_add hs (γ - 1) (1 - γ),
      show γ - 1 + (1 - γ) = 0 by ring, Real.rpow_zero, one_mul]
  have hsq : Filter.Tendsto (fun θ : ℝ => X θ ^ 2)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := hmul.congr' hsplit
  -- The square root of the square is `|X|`.
  have hsqrt : Filter.Tendsto (fun θ : ℝ => Real.sqrt (X θ ^ 2))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    simpa [Function.comp_def] using (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hsq
  have habs : Filter.Tendsto (fun θ : ℝ => |X θ|)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    simpa [Real.sqrt_sq_eq_abs] using hsqrt
  exact tendsto_zero_iff_norm_tendsto_zero.2 (by simpa [Real.norm_eq_abs] using habs)

/-- **A diverging weight kills the function (left endpoint).**  If `γ > 1` and
`sin (2θ) ^ (1 - γ) · X θ ^ 2 → 0` as `θ → (π/2)⁻`, then `X θ → 0` as `θ → (π/2)⁻`.

The same proof as the right-endpoint version: `sin(2θ) → 0` at `π/2` is
`Work.FTS.H2.tendsto_sin_rpow_zero_left`, and the neighbourhood `(π/4, π/2)` of `π/2` in which
`sin(2θ) > 0` (so that the `rpow` exponents may be added) is `Ioo_mem_nhdsLT`. -/
theorem tendsto_zero_of_sin_rpow_mul_sq_left {γ : ℝ} (hγ : 1 < γ) {X : ℝ → ℝ}
    (h : Filter.Tendsto (fun θ : ℝ => Real.sin (2 * θ) ^ (1 - γ) * X θ ^ 2)
      (nhdsWithin (π / 2) (Set.Iio (π / 2))) (nhds 0)) :
    Filter.Tendsto X (nhdsWithin (π / 2) (Set.Iio (π / 2))) (nhds 0) := by
  have hpos : 0 < γ - 1 := by linarith
  have hmul : Filter.Tendsto (fun θ : ℝ => Real.sin (2 * θ) ^ (γ - 1)
      * (Real.sin (2 * θ) ^ (1 - γ) * X θ ^ 2))
      (nhdsWithin (π / 2) (Set.Iio (π / 2))) (nhds 0) := by
    simpa using (Work.FTS.H2.tendsto_sin_rpow_zero_left (γ - 1) hpos).mul h
  have hsplit : (fun θ : ℝ => Real.sin (2 * θ) ^ (γ - 1)
      * (Real.sin (2 * θ) ^ (1 - γ) * X θ ^ 2))
      =ᶠ[nhdsWithin (π / 2) (Set.Iio (π / 2))] (fun θ : ℝ => X θ ^ 2) := by
    filter_upwards [self_mem_nhdsWithin,
      Ioo_mem_nhdsLT (show π / 4 < π / 2 by linarith [Real.pi_pos])] with θ hθ hlt
    have hs : 0 < Real.sin (2 * θ) :=
      Work.FTS.H2.sin_two_pos_of_Ioo ⟨by linarith [hlt.1, Real.pi_pos], hlt.2⟩
    rw [← mul_assoc, ← Real.rpow_add hs (γ - 1) (1 - γ),
      show γ - 1 + (1 - γ) = 0 by ring, Real.rpow_zero, one_mul]
  have hsq : Filter.Tendsto (fun θ : ℝ => X θ ^ 2)
      (nhdsWithin (π / 2) (Set.Iio (π / 2))) (nhds 0) := hmul.congr' hsplit
  have hsqrt : Filter.Tendsto (fun θ : ℝ => Real.sqrt (X θ ^ 2))
      (nhdsWithin (π / 2) (Set.Iio (π / 2))) (nhds 0) := by
    simpa [Function.comp_def] using (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hsq
  have habs : Filter.Tendsto (fun θ : ℝ => |X θ|)
      (nhdsWithin (π / 2) (Set.Iio (π / 2))) (nhds 0) := by
    simpa [Real.sqrt_sq_eq_abs] using hsqrt
  exact tendsto_zero_iff_norm_tendsto_zero.2 (by simpa [Real.norm_eq_abs] using habs)

/-- **The endpoint limits of a mixed derivative, from the boundary traces.**  For `z > 0`, the
mixed derivative `D_z^b D_θ^a f` of a profile whose boundary traces vanish (`BdryTraces α k f`,
which supplies the slot `(a,b)` as soon as `a + b ≤ k`) tends to `0` as `θ → 0⁺` and as
`θ → (π/2)⁻`. -/
theorem BdryTracesMixedTendsto {α : ℝ} (hα : 0 < α) {k : ℕ} {f : Work.FTS.Galerkin.Fn}
    (htr : Work.FTS.Nonlin.BdryTraces α k f) {a b : ℕ} (hab : a + b ≤ k) {z : ℝ} (hz : 0 < z) :
    Filter.Tendsto (fun θ : ℝ => Work.Spaces.mixed b a f z θ) (𝓝[>] 0) (𝓝 0) ∧
    Filter.Tendsto (fun θ : ℝ => Work.Spaces.mixed b a f z θ) (𝓝[<] (Real.pi / 2)) (𝓝 0) := by
  have hγ : 1 < Work.Spaces.gam α := by
    simp only [Work.Spaces.gam]; linarith
  obtain ⟨h0, hπ⟩ := (htr a b hab).2 z hz
  exact ⟨tendsto_zero_of_sin_rpow_mul_sq_right hγ h0,
    tendsto_zero_of_sin_rpow_mul_sq_left hγ hπ⟩

end Work.FTS.StrongEps.EpsRLX.ProfRHSAux
