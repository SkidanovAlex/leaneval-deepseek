import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.RegExportIface.RXT.Leaves
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS.StrongEps.classC_mixed_sup_le_four

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.loc_sup4` — the local `C⁴` sup bound of the strong solution (S1)

For a family `g` satisfying `DynOK' (pExp α) C₀ Φs E g` and any box `[a,b] × [c,d]` with
`0 < a`, `0 < c`, `d < π/2` inside the open quadrant, the mixed derivatives
`D_z^jD_θ^i (slice g τ)` of order `j + i ≤ 4` are uniformly bounded on `[0,T] × [a,b] × [c,d]`.

The proof is the plan of `sources/ftsV2/fts_rxt_leafplans.md` (S1):

* `DynOK'` gives `DynOK` and `LimApprox`; evaluating the latter at the horizon `T + 1` produces the
  class-C approximants `gn`, the uniform `ℋ⁶`-bound `Xn6 α (slice (gn n) τ) ≤ B` and the
  convergence of every jet of order `≤ 4` on `Qd`;
* a class-`C` slice is `SmoothOpen` and `HkMem` at level `6`, so the interior `L^∞`–`ℋ⁶` trade-off
  `StrongEps.classC_mixed_sup_le_four` bounds each mixed slot of order `≤ 4` at a point of `Qd` by
  a constant (depending only on the box and on `γ - 1`) times `Xn6`;
* the box lies in `Qd`, so the limit is taken with `le_of_tendsto`.

Note the constant may depend on the box (the `L^∞`–`ℋ⁶` constant does), which is exactly what the
statement allows.
-/

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_RegExport.RXT

theorem loc_sup4 {α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3) {g : Work.FTS.Galerkin.Fam}
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (T : ℝ) (hT : 0 < T) {a b c d : ℝ} (ha : 0 < a) (hab : a ≤ b) (hc : 0 < c) (hcd : c ≤ d)
    (hd : d < π / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ ∈ Set.Icc (0:ℝ) T, ∀ j i : ℕ, j + i ≤ 4 →
      ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d,
      |Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g τ) z θ| ≤ C := by
  -- the exponent `β = pExp α = 3α` is a positive exponent `≤ 1`
  have hβ : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hβ1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  -- the class-`C` interior `L^∞`–`ℋ⁶` trade-off
  obtain ⟨C₁, hC₁pos, hC₁⟩ := Work.FTS.StrongEps.classC_mixed_sup_le_four
  have hC₁nn : 0 ≤ C₁ / Real.sqrt (Work.Spaces.gam (Work.FTS.Regularity.pExp α) - 1) :=
    div_nonneg hC₁pos.le (Real.sqrt_nonneg _)
  -- the approximating class-C families, the uniform `ℋ⁶`-bound `B`, and the jet convergence
  obtain ⟨gn, B, _L, h1, _h2, h3, _h4⟩ := hOK.2 (T + 1) (by linarith)
  have hBnn : 0 ≤ B := by
    have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (T + 1) := ⟨le_rfl, by linarith⟩
    have hx : 0 ≤ Work.FTS.StrongGlobal.Xn6 (Work.FTS.Regularity.pExp α)
        (Work.FTS.Galerkin.slice (gn 0) 0) := Work.Spaces.HkNorm_nonneg _ 6 _
    linarith [(h1 0 0 h0).2.2]
  refine ⟨C₁ / Real.sqrt (Work.Spaces.gam (Work.FTS.Regularity.pExp α) - 1) * B,
    mul_nonneg hC₁nn hBnn, ?_⟩
  intro τ hτ j i hji z hz θ hθ
  -- the box sits inside the open quadrant, and `τ` inside the horizon `T + 1`
  have hzpos : 0 < z := lt_of_lt_of_le ha hz.1
  have hθpos : 0 < θ := lt_of_lt_of_le hc hθ.1
  have hθlt : θ < π / 2 := lt_of_le_of_lt hθ.2 hd
  have hzθ : (z, θ) ∈ Work.Construction.Qd := ⟨hzpos, hθpos, hθlt⟩
  have hτT : τ ∈ Set.Icc (0 : ℝ) (T + 1) := ⟨hτ.1, by linarith [hτ.2]⟩
  -- every approximant satisfies the class-C bound at `(z,θ)`
  have hbound : ∀ n : ℕ,
      |Work.Spaces.mixed j i (Work.FTS.Galerkin.slice (gn n) τ) z θ|
        ≤ C₁ / Real.sqrt (Work.Spaces.gam (Work.FTS.Regularity.pExp α) - 1) * B := by
    intro n
    have hcn : Work.FTS.ClassC.ClassC (Work.FTS.Regularity.pExp α)
        (Work.FTS.Galerkin.slice (gn n) τ) := (h1 n τ hτT).1
    have hx6 : Work.FTS.StrongGlobal.Xn6 (Work.FTS.Regularity.pExp α)
        (Work.FTS.Galerkin.slice (gn n) τ) ≤ B := (h1 n τ hτT).2.2
    have hb := hC₁ (Work.FTS.Regularity.pExp α) ⟨hβ, hβ1⟩ hcn j i (by omega) hzθ
    calc |Work.Spaces.mixed j i (Work.FTS.Galerkin.slice (gn n) τ) z θ|
        ≤ C₁ / Real.sqrt (Work.Spaces.gam (Work.FTS.Regularity.pExp α) - 1)
            * Work.FTS.StrongGlobal.Xn6 (Work.FTS.Regularity.pExp α)
              (Work.FTS.Galerkin.slice (gn n) τ) := hb
      _ ≤ C₁ / Real.sqrt (Work.Spaces.gam (Work.FTS.Regularity.pExp α) - 1) * B :=
          mul_le_mul_of_nonneg_left hx6 hC₁nn
  -- pass to the limit along the jets of order `≤ 4`
  exact le_of_tendsto (h3 τ hτT j i hji z θ hzθ).abs (Filter.Eventually.of_forall hbound)

end Work.FTS_RegExport.RXT
