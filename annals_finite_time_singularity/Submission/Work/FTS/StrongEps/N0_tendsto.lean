import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Complex.Trigonometric
import Submission.Work.FTS.Galerkin.Defs
import Submission.Work.Construction.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FM.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps

/-- **Pointwise convergence of `N₀`.**  If every slot `D_z^jD_θ^i` of order `j + i ≤ 1` of the
family `F n` converges at `(z,θ)` to the corresponding slot of `Flim`, the same holds for the
family `w n` with limit `wlim`, and additionally `L₁₂(w n)(z') → L₁₂(wlim)(z')` for every
`z' ∈ Iz` (in particular at `z` itself), then `N₀ α (F n) (w n) z θ` converges to
`N₀ α Flim wlim z θ`.

`N₀` is a fixed algebraic combination of the constant profile `F_*` and of the quantities
`L₁₂(g)(z)`, `g(z,θ)`, `D_zF(z,θ)`, `D_zg(z,θ)` and `∂_θF(z,θ)` (with `F` the first and `g` the
second argument), so the statement is a limit computation.  The only subtlety is `∂_θF`: the
hypotheses control `mixed 0 1 (F n) z θ = D_θ(F n) z θ = sin(2θ)·∂_θ(F n) z θ`, i.e. `∂_θF` only
after multiplication by `sin(2θ)`; but in `N₀` the factor `∂_θF` also carries the coefficient
`(3/(2α))·sin(2θ)·L₁₂(g)(z)`, and grouping the product as
`((3/(2α))·L₁₂(g)(z))·(sin(2θ)·∂_θF)` (a pure ring identity) makes the convergent quantity
`sin(2θ)·∂_θF` the second factor.  No hypothesis on `θ` (or on the smoothness of `Flim`, `wlim`)
is needed beyond the convergence data. -/
theorem N0_tendsto {α : ℝ} {F : ℕ → Work.FTS.Galerkin.Fn} {Flim : Work.FTS.Galerkin.Fn}
    {w : ℕ → Work.FTS.Galerkin.Fn} {wlim : Work.FTS.Galerkin.Fn} {z θ : ℝ}
    (hz : z ∈ Work.Spaces.Iz)
    (hF : ∀ j i : ℕ, j + i ≤ 1 →
      Filter.Tendsto (fun n : ℕ => Work.Spaces.mixed j i (F n) z θ) Filter.atTop
        (nhds (Work.Spaces.mixed j i Flim z θ)))
    (hw : ∀ j i : ℕ, j + i ≤ 1 →
      Filter.Tendsto (fun n : ℕ => Work.Spaces.mixed j i (w n) z θ) Filter.atTop
        (nhds (Work.Spaces.mixed j i wlim z θ)))
    (hlw : ∀ z' ∈ Work.Spaces.Iz, Filter.Tendsto (fun n : ℕ => Work.Construction.L12 (w n) z')
      Filter.atTop (nhds (Work.Construction.L12 wlim z'))) :
    Filter.Tendsto (fun n : ℕ => Work.Construction.N0 α (F n) (w n) z θ) Filter.atTop
      (nhds (Work.Construction.N0 α Flim wlim z θ)) := by
  -- The slots of order `≤ 1`.
  have hL : Filter.Tendsto (fun n : ℕ => Work.Construction.L12 (w n) z) Filter.atTop
      (nhds (Work.Construction.L12 wlim z)) := hlw z hz
  have hg : Filter.Tendsto (fun n : ℕ => w n z θ) Filter.atTop (nhds (wlim z θ)) := by
    simpa only [Work.Spaces.mixed, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_zero] using
      hw 0 0 (by norm_num)
  have hZg : Filter.Tendsto (fun n : ℕ => Work.Spaces.Dz (w n) z θ) Filter.atTop
      (nhds (Work.Spaces.Dz wlim z θ)) := by
    simpa only [Work.Spaces.mixed, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero,
      Work.Spaces.DthIter_zero] using hw 1 0 (by norm_num)
  have hZF : Filter.Tendsto (fun n : ℕ => Work.Spaces.Dz (F n) z θ) Filter.atTop
      (nhds (Work.Spaces.Dz Flim z θ)) := by
    simpa only [Work.Spaces.mixed, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero,
      Work.Spaces.DthIter_zero] using hF 1 0 (by norm_num)
  -- `∂_θF` is only controlled after multiplication by `sin(2θ)`.
  have hDth : Filter.Tendsto
      (fun n : ℕ => Real.sin (2 * θ) * Work.Spaces.pth (F n) z θ) Filter.atTop
      (nhds (Real.sin (2 * θ) * Work.Spaces.pth Flim z θ)) := by
    simpa only [Work.Spaces.mixed, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_succ,
      Work.Spaces.DthIter_zero, Work.Spaces.Dth] using hF 0 1 (by norm_num)
  -- The `n`-independent part (`F_*`-terms of `N₀`).
  have hA : Filter.Tendsto (fun _ : ℕ =>
        (3 / (2 * α)) * Real.sin (2 * θ) * Work.Construction.L12 (Work.Construction.Fstar α) z
            * Work.Spaces.pth (Work.Construction.Fstar α) z θ
          - (Real.cos (2 * θ) - Real.sin θ ^ 2)
            * Work.Construction.L12 (Work.Construction.Fstar α) z
            * Work.Spaces.Dz (Work.Construction.Fstar α) z θ)
      Filter.atTop (nhds _) := tendsto_const_nhds
  have hB : Filter.Tendsto (fun n : ℕ =>
        (1 / α) * Work.Construction.L12 (w n) z * (w n z θ))
      Filter.atTop (nhds ((1 / α) * Work.Construction.L12 wlim z * (wlim z θ))) :=
    (hL.const_mul (1 / α)).mul hg
  have hC : Filter.Tendsto (fun n : ℕ =>
        (3 / (2 * α)) * Work.Construction.L12 (w n) z
          * (Real.sin (2 * θ) * Work.Spaces.pth (F n) z θ))
      Filter.atTop (nhds ((3 / (2 * α)) * Work.Construction.L12 wlim z
          * (Real.sin (2 * θ) * Work.Spaces.pth Flim z θ))) :=
    (hL.const_mul (3 / (2 * α))).mul hDth
  have hD : Filter.Tendsto (fun n : ℕ =>
        (Real.cos (2 * θ) - Real.sin θ ^ 2) * Work.Construction.L12 (w n) z
          * Work.Spaces.Dz (F n) z θ)
      Filter.atTop (nhds ((Real.cos (2 * θ) - Real.sin θ ^ 2) * Work.Construction.L12 wlim z
          * Work.Spaces.Dz Flim z θ)) :=
    (tendsto_const_nhds.mul hL).mul hZF
  have hE : Filter.Tendsto (fun n : ℕ =>
        (Real.cos (2 * θ) - Real.sin θ ^ 2) * Work.Construction.L12 (Work.Construction.Fstar α) z
          * Work.Spaces.Dz (w n) z θ)
      Filter.atTop (nhds ((Real.cos (2 * θ) - Real.sin θ ^ 2)
          * Work.Construction.L12 (Work.Construction.Fstar α) z
          * Work.Spaces.Dz wlim z θ)) :=
    hZg.const_mul ((Real.cos (2 * θ) - Real.sin θ ^ 2)
      * Work.Construction.L12 (Work.Construction.Fstar α) z)
  have hmain := (((hA.add hB).add hC).sub hD).sub hE
  -- `N₀` is the same expression, only the term carrying `∂_θF` is regrouped.
  convert hmain using 1
  · funext n
    simp only [Work.Construction.N0, Work.Construction.s2, Work.Construction.c2m]
    ring
  · congr 1
    simp only [Work.Construction.N0, Work.Construction.s2, Work.Construction.c2m]
    ring

end Work.FTS.StrongEps
