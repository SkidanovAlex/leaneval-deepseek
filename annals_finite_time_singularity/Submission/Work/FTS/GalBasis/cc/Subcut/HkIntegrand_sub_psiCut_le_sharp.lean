import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.GalBasis.cc.Subcut.Defs
import Submission.Work.FTS.GalBasis.cc.CutSpec
import Submission.Work.FTS.GalBasis.cc.SlotDefs
import Submission.Work.FTS.GalBasis.cc.chi_facts
import Submission.Work.FTS.GalBasis.cc.CutEst
import Submission.Work.FTS.GalBasis.cc.HkIntegrand_mul_le_slots
import Submission.Work.FTS.GalBasis.cc.Subcut.SharpLocalized
import Submission.Work.FTS.GalBasis.cc.Subcut.SharpMulSlots
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.GalBasis.cc.Subcut

open scoped Real Topology
open MeasureTheory Set Filter

attribute [local instance] Classical.propDecidable
set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- The **sharp** pointwise product bound for `χ_N f = f - ψ N · f`: on the open quadrant the
`ℋ⁴`-integrand of `f - ψ N · f` is bounded by a constant (chosen uniformly in `N`) times the sum of the
`ℋ⁴`-mass of `f` localised to `UN N` and the wrong-weight slots `zslotW α b f = D_z^b f · w · sin(2θ)^{-γ/2}`
for `b < 4` (not `b < 5`) localised to the two angular layers `LN N`.

The sharp range matters: this is fed into a layer estimate available only for `b ≤ 3` (its domination step uses
`mixed b 1 f`, of order `b + 1 ≤ 4`).  In `mulSlotRHS` the only occurrence of `zslotW` is in the mixed block's
`else` branch, guarded by `1 ≤ i ∧ i + j ≤ 4 ∧ a ≤ i ∧ b ≤ j` with `a = i`, and the slot index is `j - b`;
since `i ≥ 1` and `i + j ≤ 4` we have `j ≤ 3`, hence `j - b ≤ 3`.  So the membership fed to
`Finset.single_le_sum` sharpens from `Finset.mem_range.mpr (by omega)` to `Finset.range 4`, and the rest of the
proof of the sibling `HkIntegrand_sub_psiCut_le` (the pure `D_z` block, the multiplier bounds
`hmulU`/`hmulL` from `chi_facts`, the `650 = 25 + 625` counting, and the final `ring`) is unchanged, giving a
constant of the same shape `C₀ · 650 (K'^2 + 1)`.

Recommendation: prove a version of `CutEst.mulSlotRHS_le_localized` parameterised by the upper bound of the
localising sum (`Finset.range 4` instead of `Finset.range 5`), or copy its proof and sharpen the single
membership. -/
theorem HkIntegrand_sub_psiCut_le_sharp {α : ℝ} {f : Work.FTS.Galerkin.Fn}
    {ψ : ℕ → Work.FTS.Galerkin.Fn} {K : ℝ} (hs : CutSpec ψ K)
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.HkIntegrand α 4 (fun z θ => f z θ - ψ N z θ * f z θ) z θ ≤
        C * ((Work.FTS.GalBasis.cc.UN N).indicator (fun _ => (1 : ℝ)) (z, θ) *
              Work.Spaces.HkIntegrand α 4 f z θ
            + (Work.FTS.GalBasis.cc.LN N).indicator (fun _ => (1 : ℝ)) θ *
              ∑ b ∈ Finset.range 4, (Work.FTS.GalBasis.cc.zslotW α b f z θ) ^ 2) := by
  obtain ⟨K', hK'pos, hchi⟩ := chi_facts hs
  -- smoothness of the complement `χ_N = 1 - ψ N`
  have hχsm : ∀ N : ℕ,
      Work.FTS.EllipticEst.SmoothOpen (fun z θ => 1 - ψ N z θ) := by
    intro N
    have hψ : Work.FTS.EllipticEst.SmoothOpen (ψ N) := (hs.smooth N).contDiffOn
    change ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (fun z θ : ℝ => 1 - ψ N z θ)) Work.FTS.EllipticEst.Q0
    rw [show Function.uncurry (fun z θ : ℝ => 1 - ψ N z θ)
        = fun p : ℝ × ℝ => (1 : ℝ) - (fun p : ℝ × ℝ => ψ N p.1 p.2) p from rfl]
    exact (contDiffOn_const (c := (1 : ℝ))).sub hψ
  refine ⟨1024032001 * (650 * (K' ^ 2 + 1)), by positivity, ?_⟩
  intro N z θ hz hθ hθ2
  have hU : ∀ j i : ℕ, j + i ≤ 4 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.mixed j i (fun z θ => 1 - ψ N z θ) z θ ≠ 0 →
        (z, θ) ∈ Work.FTS.GalBasis.cc.UN N := by
    intro j i hji z θ hz hθ hθ2 hne
    rcases (hchi N).2.1 j i hji z θ hz hθ hθ2 hne with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hL : ∀ j i : ℕ, 1 ≤ i → j + i ≤ 4 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.mixed j i (fun z θ => 1 - ψ N z θ) z θ ≠ 0 →
        θ ∈ Work.FTS.GalBasis.cc.LN N :=
    fun j i hi hji z θ hz hθ hθ2 hne => (hchi N).2.2 j i hi hji z θ hz hθ hθ2 hne
  have hloc := mulSlotRHS_le_localized_sharp (α := α) (χ := fun z θ => 1 - ψ N z θ)
    (f := f) (K := K') (U := Work.FTS.GalBasis.cc.UN N) (L := Work.FTS.GalBasis.cc.LN N)
    (le_of_lt hK'pos) hU hL (hchi N).1 hz hθ hθ2
  have hloc' : mulSlotRHS α (fun z θ => 1 - ψ N z θ) f z θ ≤
      650 * (K' ^ 2 + 1) *
        ((Work.FTS.GalBasis.cc.UN N).indicator (fun _ => (1 : ℝ)) (z, θ)
            * Work.Spaces.HkIntegrand α 4 f z θ
          + (Work.FTS.GalBasis.cc.LN N).indicator (fun _ => (1 : ℝ)) θ *
            ∑ b ∈ Finset.range 4, (zslotW α b f z θ) ^ 2) := by
    rw [Set.indicator_apply, Set.indicator_apply]
    exact hloc
  have hprod := HkIntegrand_mul_le_slots_explicit (α := α) (χ := fun z θ => 1 - ψ N z θ)
    (f := f) (hχsm N) hsm z θ hz hθ hθ2
  have hfun : (fun z θ : ℝ => f z θ - ψ N z θ * f z θ)
      = fun z θ : ℝ => (1 - ψ N z θ) * f z θ := by
    funext z θ; ring
  rw [hfun]
  calc Work.Spaces.HkIntegrand α 4 (fun z θ => (1 - ψ N z θ) * f z θ) z θ
      ≤ 1024032001 * mulSlotRHS α (fun z θ => 1 - ψ N z θ) f z θ := hprod
    _ ≤ 1024032001 * (650 * (K' ^ 2 + 1) *
          ((Work.FTS.GalBasis.cc.UN N).indicator (fun _ => (1 : ℝ)) (z, θ)
              * Work.Spaces.HkIntegrand α 4 f z θ
            + (Work.FTS.GalBasis.cc.LN N).indicator (fun _ => (1 : ℝ)) θ *
              ∑ b ∈ Finset.range 4, (zslotW α b f z θ) ^ 2)) :=
        mul_le_mul_of_nonneg_left hloc' (by norm_num)
    _ = (1024032001 * (650 * (K' ^ 2 + 1))) *
          ((Work.FTS.GalBasis.cc.UN N).indicator (fun _ => (1 : ℝ)) (z, θ)
              * Work.Spaces.HkIntegrand α 4 f z θ
            + (Work.FTS.GalBasis.cc.LN N).indicator (fun _ => (1 : ℝ)) θ *
              ∑ b ∈ Finset.range 4, (zslotW α b f z θ) ^ 2) := by ring

end Work.FTS.GalBasis.cc.Subcut
