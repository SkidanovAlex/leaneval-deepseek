import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.Construction.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.Galerkin.Defs
import Submission.Work.FTS.StrongEps.gRHSBound.abs_N0_le
import Submission.Work.FTS.StrongEps.gRHSBound.abs_N_le
import Submission.Work.FTS.StrongEps.gRHSBound.abs_Nstar_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option maxHeartbeats 1000000

namespace Work.FTS.StrongEps

/-- **A sup bound for the right hand side `gRHS` of the `g`-equation on a compact set.**

`gRHS = -μ̄·AK + N₀ + N + N_*` is a finite sum of products, each of whose factors is one of
the eleven quantities bounded by `B` in the hypothesis `hbnd`, or one of
`L₁₂(F_*)`, `L₁₂(g)`, `FK F`, `μ̄` — bounded by `B` in the remaining hypotheses.  Hence on
`K ⊆ Q₀` (which enters only through `z > 0`, i.e. `z ∈ Iz`, so that the `L₁₂`- and
`FK`-bounds apply) the whole right hand side is bounded by an explicit constant depending
only on `α` and `B`.

The three summands are estimated in the helper modules
`Work.FTS.StrongEps.gRHSBound.{abs_N0_le, abs_N_le, abs_Nstar_le}`; the assembly below
combines them with the `μ̄·AK`-term.  Two auxiliary constants absorb the parameters:
`M ≥ max 1 (4/α)` the `α`-coefficients and `E = B² + B + 1` the powers of `B` (this makes
the product bounds uniform in `B`, in particular works for `B < 1`). -/
theorem gRHS_abs_le_on_compact {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {μ lam : ℝ}
    (hμ : |μ| ≤ 1 / 2) (hlam : |lam| ≤ 1)
    {F Φ g : Work.FTS.Galerkin.Fn} {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hKQ : K ⊆ Work.FTS.EllipticEst.Q0)
    {B : ℝ} (hB : 0 ≤ B)
    (hbnd : ∀ z θ : ℝ, (z, θ) ∈ K →
      |F z θ| + |Work.Spaces.pth F z θ| + |Work.Spaces.Dz F z θ| + |g z θ|
        + |Work.Spaces.Dz g z θ| + |Work.Spaces.pth (Work.Construction.Fstar α) z θ|
        + |Work.Spaces.Dz (Work.Construction.Fstar α) z θ|
        + |Work.Construction.Rop α (Work.Construction.PhiTil α F Φ) z θ|
        + |Work.Construction.Uop α (Work.Construction.PhiTil α F Φ) z θ|
        + |Work.Construction.Vop (Work.Construction.PhiTil α F Φ) z θ|
        + |Work.Construction.AK α z θ| ≤ B)
    (hL12Fstar : ∀ z ∈ Work.Spaces.Iz,
      |Work.Construction.L12 (Work.Construction.Fstar α) z| ≤ B)
    (hL12g : ∀ z ∈ Work.Spaces.Iz, |Work.Construction.L12 g z| ≤ B)
    (hmubar : |Work.Construction.mubar (Work.Construction.N0 α F g)
        (Work.Construction.N α F Φ)| ≤ B)
    (hFK : ∀ z ∈ Work.Spaces.Iz, |Work.Construction.FK F z| ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ z θ : ℝ, (z, θ) ∈ K →
      |Work.Construction.gRHS α μ lam F Φ g z θ| ≤ C := by
  -- the two auxiliary constants: `M` absorbs the `α`-coefficients, `E` the powers of `B`
  obtain ⟨M, hM1, hD4⟩ : ∃ M : ℝ, 1 ≤ M ∧ 4 / α ≤ M :=
    ⟨max 1 (4 / α), le_max_left 1 (4 / α), le_max_right 1 (4 / α)⟩
  obtain ⟨E, hEpos, hB2E, hBE⟩ : ∃ E : ℝ, 0 < E ∧ B ^ 2 ≤ E ∧ B ≤ E :=
    ⟨B ^ 2 + B + 1, by nlinarith [sq_nonneg B, hB], by linarith [hB],
      by nlinarith [sq_nonneg B]⟩
  have hMpos : 0 < M := lt_of_lt_of_le one_pos hM1
  have hMEpos : 0 < M * E := mul_pos hMpos hEpos
  have hME : E ≤ M * E := by nlinarith [hM1, hEpos]
  have hBBE : B * B ≤ E := by nlinarith [hB2E]
  refine ⟨100 * M * E, by nlinarith [hMpos, hEpos], ?_⟩
  intro z θ hzθ
  -- `K ⊆ Q₀` gives `z > 0`, hence `z ∈ Iz` for the three global bounds
  have hQ : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := hKQ hzθ
  obtain ⟨hzpos, -, -⟩ := Work.FTS.EllipticEst.mem_Q0.mp hQ
  have hzIz : z ∈ Work.Spaces.Iz := by simpa [Work.Spaces.Iz] using le_of_lt hzpos
  -- split the eleven-term sum bound into its eleven summands
  have hb := hbnd z θ hzθ
  have hn0 : (0 : ℝ) ≤ |F z θ| := abs_nonneg _
  have hn1 : (0 : ℝ) ≤ |Work.Spaces.pth F z θ| := abs_nonneg _
  have hn2 : (0 : ℝ) ≤ |Work.Spaces.Dz F z θ| := abs_nonneg _
  have hn3 : (0 : ℝ) ≤ |g z θ| := abs_nonneg _
  have hn4 : (0 : ℝ) ≤ |Work.Spaces.Dz g z θ| := abs_nonneg _
  have hn5 : (0 : ℝ) ≤ |Work.Spaces.pth (Work.Construction.Fstar α) z θ| := abs_nonneg _
  have hn6 : (0 : ℝ) ≤ |Work.Spaces.Dz (Work.Construction.Fstar α) z θ| := abs_nonneg _
  have hn7 : (0 : ℝ) ≤ |Work.Construction.Rop α (Work.Construction.PhiTil α F Φ) z θ| :=
    abs_nonneg _
  have hn8 : (0 : ℝ) ≤ |Work.Construction.Uop α (Work.Construction.PhiTil α F Φ) z θ| :=
    abs_nonneg _
  have hn9 : (0 : ℝ) ≤ |Work.Construction.Vop (Work.Construction.PhiTil α F Φ) z θ| :=
    abs_nonneg _
  have hn10 : (0 : ℝ) ≤ |Work.Construction.AK α z θ| := abs_nonneg _
  have hFb : |F z θ| ≤ B := by linarith [hb, hn1, hn2, hn3, hn4, hn5, hn6, hn7, hn8, hn9, hn10]
  have hpFb : |Work.Spaces.pth F z θ| ≤ B := by
    linarith [hb, hn0, hn2, hn3, hn4, hn5, hn6, hn7, hn8, hn9, hn10]
  have hDzFb : |Work.Spaces.Dz F z θ| ≤ B := by
    linarith [hb, hn0, hn1, hn3, hn4, hn5, hn6, hn7, hn8, hn9, hn10]
  have hgb : |g z θ| ≤ B := by
    linarith [hb, hn0, hn1, hn2, hn4, hn5, hn6, hn7, hn8, hn9, hn10]
  have hDzgb : |Work.Spaces.Dz g z θ| ≤ B := by
    linarith [hb, hn0, hn1, hn2, hn3, hn5, hn6, hn7, hn8, hn9, hn10]
  have hpFstb : |Work.Spaces.pth (Work.Construction.Fstar α) z θ| ≤ B := by
    linarith [hb, hn0, hn1, hn2, hn3, hn4, hn6, hn7, hn8, hn9, hn10]
  have hDzFstb : |Work.Spaces.Dz (Work.Construction.Fstar α) z θ| ≤ B := by
    linarith [hb, hn0, hn1, hn2, hn3, hn4, hn5, hn7, hn8, hn9, hn10]
  have hRopb : |Work.Construction.Rop α (Work.Construction.PhiTil α F Φ) z θ| ≤ B := by
    linarith [hb, hn0, hn1, hn2, hn3, hn4, hn5, hn6, hn8, hn9, hn10]
  have hUopb : |Work.Construction.Uop α (Work.Construction.PhiTil α F Φ) z θ| ≤ B := by
    linarith [hb, hn0, hn1, hn2, hn3, hn4, hn5, hn6, hn7, hn9, hn10]
  have hVopb : |Work.Construction.Vop (Work.Construction.PhiTil α F Φ) z θ| ≤ B := by
    linarith [hb, hn0, hn1, hn2, hn3, hn4, hn5, hn6, hn7, hn8, hn10]
  have hAKb : |Work.Construction.AK α z θ| ≤ B := by
    linarith [hb, hn0, hn1, hn2, hn3, hn4, hn5, hn6, hn7, hn8, hn9]
  have hL1Fst : |Work.Construction.L12 (Work.Construction.Fstar α) z| ≤ B := hL12Fstar z hzIz
  have hL1g : |Work.Construction.L12 g z| ≤ B := hL12g z hzIz
  have hFKb : |Work.Construction.FK F z| ≤ B := hFK z hzIz
  -- the four summands of `gRHS = -μ̄·AK + N₀ + N + N_*`
  have hAKpart : |(-(Work.Construction.mubar (Work.Construction.N0 α F g)
      (Work.Construction.N α F Φ))) * Work.Construction.AK α z θ| ≤ B * B := by
    rw [abs_mul, abs_neg]
    exact mul_le_mul hmubar hAKb (abs_nonneg _) hB
  have hpart1 : |Work.Construction.N0 α F g z θ| ≤ (4 / α + 6) * B ^ 2 :=
    Work.FTS.StrongEps.gRHSBound.abs_N0_le hα hB hL1Fst hL1g hFb hpFb hDzFb hgb hDzgb
      hpFstb hDzFstb
  have hpart2 : |Work.Construction.N α F Φ z θ| ≤ 8 * B ^ 2 :=
    Work.FTS.StrongEps.gRHSBound.abs_N_le hα hα1 hB hFb hpFb hDzFb hRopb hUopb hVopb hFKb
  have hpart3 : |Work.Construction.Nstar μ lam g z θ| ≤ 3 * B :=
    Work.FTS.StrongEps.gRHSBound.abs_Nstar_le hB hμ hlam hgb hDzgb
  have htot : |Work.Construction.gRHS α μ lam F Φ g z θ| ≤
      B * B + (4 / α + 6) * B ^ 2 + 8 * B ^ 2 + 3 * B := by
    simp only [Work.Construction.gRHS]
    obtain ⟨hXl, hXu⟩ := abs_le.mp hAKpart
    obtain ⟨hYl, hYu⟩ := abs_le.mp hpart1
    obtain ⟨hZl, hZu⟩ := abs_le.mp hpart2
    obtain ⟨hWl, hWu⟩ := abs_le.mp hpart3
    refine abs_le.mpr ⟨?_, ?_⟩ <;> linarith [hXl, hXu, hYl, hYu, hZl, hZu, hWl, hWu]
  -- absorb the explicit bound into `100 * M * E`
  have h1 : (4 / α + 6) * B ^ 2 ≤ 7 * (M * E) := by
    have hcoef : 4 / α + 6 ≤ 7 * M := by linarith [hD4, hM1]
    have h := mul_le_mul hcoef hB2E (sq_nonneg B) (by linarith [hMpos] : (0 : ℝ) ≤ 7 * M)
    linarith [h]
  have h2 : 8 * B ^ 2 ≤ 8 * (M * E) := by
    have hcoef : (8 : ℝ) ≤ 8 * M := by linarith [hM1]
    have h := mul_le_mul hcoef hB2E (sq_nonneg B) (by linarith [hMpos] : (0 : ℝ) ≤ 8 * M)
    linarith [h]
  have h3 : 3 * B ≤ 3 * (M * E) := by
    have h := mul_le_mul_of_nonneg_left hBE (by norm_num : (0 : ℝ) ≤ 3)
    have h' : 3 * E ≤ 3 * (M * E) :=
      mul_le_mul_of_nonneg_left hME (by norm_num : (0 : ℝ) ≤ 3)
    linarith [h, h']
  have h4 : B * B ≤ M * E := by
    have h := mul_le_mul_of_nonneg_left hBBE (le_of_lt hMpos)
    linarith [h]
  have hsum : B * B + (4 / α + 6) * B ^ 2 + 8 * B ^ 2 + 3 * B ≤ 100 * M * E := by
    linarith [h1, h2, h3, h4, hMEpos]
  exact le_trans htot hsum

end Work.FTS.StrongEps
