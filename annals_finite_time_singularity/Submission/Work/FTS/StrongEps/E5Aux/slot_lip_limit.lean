import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Order.Lattice
import Submission.Work.FTS.StrongEps.EpsConv

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5Aux

/-- **The slot Lipschitz bound passes to the locally uniform limit.**

If every slot `D_z^j D_θ^i` (`j + i ≤ 1`) of the profile family `τ ↦ slice (G n) τ` is
Lipschitz in `τ` with a constant `C` that is uniform in `n` on each compact subset `K` of the
quadrant `Q0`, and if for every `τ ∈ [0,T]` the slots of order `≤ 4` of `slice (G n) τ` converge
to those of `F τ` locally uniformly (the `ConvLocUnifH6` package), then the same slots of the
limit family `F` are Lipschitz in `τ` on `K` with the same constant.

The proof is the standard one: fix the two times `τ, τ'` and the point `p`, apply the uniform
bound to the `n`-th member and pass to the limit `n → ∞` using `le_of_tendsto_of_tendsto'`,
the pointwise convergence at `p` being `TendstoUniformlyOn.tendsto_at` (at the two times
separately). -/
theorem slot_lip_limit {G : ℕ → Work.FTS.Galerkin.Fam} {F : ℝ → Work.FTS.Galerkin.Fn}
    {α B T : ℝ}
    (hconv : ∀ τ ∈ Set.Icc 0 T,
      Work.FTS.StrongEps.ConvLocUnifH6 α B (fun n => Work.FTS.Galerkin.slice (G n) τ) (F τ))
    (hlip : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ (j i : ℕ), j + i ≤ 1 → ∀ p ∈ K,
        ∀ τ ∈ Set.Icc 0 T, ∀ τ' ∈ Set.Icc 0 T,
          |Work.Spaces.mixed j i (Work.FTS.Galerkin.slice (G n) τ) p.1 p.2
            - Work.Spaces.mixed j i (Work.FTS.Galerkin.slice (G n) τ') p.1 p.2|
            ≤ C * |τ - τ'|) :
    ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (j i : ℕ), j + i ≤ 1 → ∀ p ∈ K,
        ∀ τ ∈ Set.Icc 0 T, ∀ τ' ∈ Set.Icc 0 T,
          |Work.Spaces.mixed j i (F τ) p.1 p.2
            - Work.Spaces.mixed j i (F τ') p.1 p.2| ≤ C * |τ - τ'| := by
  intro K hK hKQ0
  obtain ⟨C, hC0, hClip⟩ := hlip K hK hKQ0
  refine ⟨C, hC0, ?_⟩
  intro j i hji p hp τ hτ τ' hτ'
  -- the slots of order `≤ 1` are among the slots of order `≤ 4` covered by `hconv`
  have hji4 : j + i ≤ 4 := by omega
  have huτ := Work.FTS.StrongEps.ConvLocUnifH6.conv (hconv τ hτ) K hK hKQ0 j i hji4
  have huτ' := Work.FTS.StrongEps.ConvLocUnifH6.conv (hconv τ' hτ') K hK hKQ0 j i hji4
  -- pointwise convergence of the two slots at the fixed point `p`
  have h1 := huτ.tendsto_at hp
  have h2 := huτ'.tendsto_at hp
  -- pass to the limit in the modulus of the increment
  have h3 : Filter.Tendsto
      (fun n : ℕ => |Work.Spaces.mixed j i (Work.FTS.Galerkin.slice (G n) τ) p.1 p.2
          - Work.Spaces.mixed j i (Work.FTS.Galerkin.slice (G n) τ') p.1 p.2|)
      Filter.atTop
      (nhds |Work.Spaces.mixed j i (F τ) p.1 p.2
          - Work.Spaces.mixed j i (F τ') p.1 p.2|) := (h1.sub h2).abs
  exact le_of_tendsto_of_tendsto' h3 tendsto_const_nhds
    (fun n => hClip n j i hji p hp τ hτ τ' hτ')

end Work.FTS.StrongEps.E5Aux
