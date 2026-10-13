import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.Nonlinear.FstarPkg.Fstar_W

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The `F_*`-package at order `6`: `Fstar_W6`

The profile `F_*(z,θ) = α (Γ(θ)/c) · 2z/(1+z)²` of `Work.Construction.Fstar` satisfies

  `F_* ∈ 𝒲^{6,∞}`  and  `|F_*|_{𝒲^{6,∞}} ≤ C α`,  `C` universal, for every `0 < α ≤ 1`.

The level-`4` version of this statement is `Work.FTS.Nonlinear.FstarPkg.Fstar_W`.  Nothing in
that proof used the bound `4`: the two pointwise estimates

* `Fstar_z_bound`     : `|(1+z)^k ∂_z^k F_*| ≤ 20 α · k!(k+1)`,
* `Fstar_mixed_bound` : `|(1+z)^k ∂_z^kD_θ^j F_* · sin(2θ)^{-α/5}/(α+sin 2θ)| ≤ 20 α · (tBound (j-1) 0) · k!(k+1)`

are proved for *arbitrary* `k : ℕ` and `j ≥ 1` (the only constraint is `1 ≤ j`), and the
`z`-factor `h = z/(1+z)²` as well as the angular factor `Γ` are both smooth for all orders.
So the whole `𝒲^{6,∞}`-bound follows by re-running the assembly with `4 ↦ 6` and the universal
constant `KB6` in place of `KB`.

The structure of the file is therefore:

* `KB6` and `KB6_nonneg` — the universal constant multiplying `20 α`;
* `WlInf_Fstar_le6` — the norm bound `|F_*|_{𝒲^{6,∞}} ≤ 20 α · KB6`;
* `WlInfMem_Fstar6` — membership, every `SupFinite` predicate witnessed by the same bounds;
* `Fstar_W6` — the requested statement.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist

set_option autoImplicit false

/-! ## The universal constant -/

/-- The universal constant `KB6` multiplying `20 α`: the sum of all the (α-independent)
pointwise bounds of the summands of `𝒲^{6,∞}(F_*)`.  Same shape as `FstarPkg.KB`, with
`range 5 ↦ range 7` and `k + j ≤ 4 ↦ k + j ≤ 6`. -/
noncomputable def KB6 : ℝ :=
  (∑ k ∈ Finset.range 7, (k.factorial : ℝ) * (k + 1))
    + ∑ j ∈ Finset.range 7, ∑ k ∈ Finset.range 7,
        (if 1 ≤ j ∧ k + j ≤ 6 then
          Work.Spaces.tBound (j - 1) 0 * ((k.factorial : ℝ) * (k + 1)) else 0)

lemma KB6_nonneg : 0 ≤ KB6 := by
  rw [KB6]
  refine add_nonneg (Finset.sum_nonneg fun k _ => by positivity) ?_
  refine Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => ?_
  split_ifs with h
  · exact mul_nonneg (Work.Spaces.tBound_nonneg _ _) (by positivity)
  · norm_num

/-! ## The `𝒲^{6,∞}`-norm bound -/

/-- The `𝒲^{6,∞}`-norm of `F_*` is at most `20 α · KB6`. -/
lemma WlInf_Fstar_le6 (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    Work.Spaces.WlInf α 6 (Work.Construction.Fstar α) ≤ 20 * α * KB6 := by
  have hKB : 20 * α * KB6 =
      (∑ k ∈ Finset.range 7, 20 * α * ((k.factorial : ℝ) * (k + 1)))
        + ∑ j ∈ Finset.range 7, ∑ k ∈ Finset.range 7,
            (20 * α * (if 1 ≤ j ∧ k + j ≤ 6 then
              Work.Spaces.tBound (j - 1) 0 * ((k.factorial : ℝ) * (k + 1)) else 0)) := by
    rw [KB6, mul_add]
    congr 1
    · rw [Finset.mul_sum]
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mul_sum]
  rw [Work.Spaces.WlInf, hKB]
  apply add_le_add
  · refine Finset.sum_le_sum fun k hk => ?_
    refine Work.Spaces.supAbs_le fun z hz θ hθ => ?_
    exact Work.FTS.Nonlinear.FstarPkg.Fstar_z_bound α hα hα1 k z θ hz hθ
  · apply Finset.sum_le_sum
    intro j hj
    apply Finset.sum_le_sum
    intro k hk
    split_ifs with hcond
    · refine Work.Spaces.supAbs_le fun z hz θ hθ => ?_
      exact Work.FTS.Nonlinear.FstarPkg.Fstar_mixed_bound α hα hα1 j k hcond.1 z θ hz hθ
    · simp

/-! ## Membership in `𝒲^{6,∞}` -/

/-- `F_* ∈ 𝒲^{6,∞}` for `0 < α ≤ 1`.  Every `SupFinite` predicate is witnessed by the explicit
bound of `Fstar_z_bound` / `Fstar_mixed_bound`. -/
lemma WlInfMem_Fstar6 (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    Work.Spaces.WlInfMem α 6 (Work.Construction.Fstar α) := by
  constructor
  · intro k hk
    refine ⟨20 * α * ((k.factorial : ℝ) * (k + 1)), fun y hy => ?_⟩
    rcases hy with ⟨z, hz, θ, hθ, rfl⟩
    exact Work.FTS.Nonlinear.FstarPkg.Fstar_z_bound α hα hα1 k z θ hz hθ
  · intro j hj k hk hj1 hjk
    refine ⟨20 * α * (Work.Spaces.tBound (j - 1) 0 * ((k.factorial : ℝ) * (k + 1))),
      fun y hy => ?_⟩
    rcases hy with ⟨z, hz, θ, hθ, rfl⟩
    exact Work.FTS.Nonlinear.FstarPkg.Fstar_mixed_bound α hα hα1 j k hj1 z θ hz hθ

/-! ## The requested statement -/

theorem Fstar_W6 : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 →
    Work.Spaces.WlInfMem α 6 (Work.Construction.Fstar α) ∧
    Work.Spaces.WlInf α 6 (Work.Construction.Fstar α) ≤ C * α := by
  refine ⟨20 * KB6 + 1, by linarith [KB6_nonneg], fun α hα hα1 =>
    ⟨WlInfMem_Fstar6 α hα hα1, ?_⟩⟩
  refine le_trans (WlInf_Fstar_le6 α hα hα1) ?_
  nlinarith [KB6_nonneg, hα]

end Work.FTS.StrongPersist
