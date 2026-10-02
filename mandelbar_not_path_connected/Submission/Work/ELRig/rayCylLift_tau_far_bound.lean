import Mathlib
import Submission.Work.ELRig.SideFlipChart
import Submission.Work.ELRig.CylLift

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter Set
open scoped Topology

namespace Work.ELRig

/-- **The level map `τ` of a `RayCylLift` separates the lift.**

If the level `L.τ s` is at distance at least `ε > 0` from the level `L.τ s₀`, then the lift point
`L.γ₁ s` is at distance at least some `c' > 0` from `L.γ₁ s₀`.

The proof is purely about continuity: the level `τ s` is the modulus of the Böttcher value of the
lift point `γ₁ s`, i.e.
`L.τ s = ‖dynPhi c d.φ (fl.Ψ (L.γ₁ s))‖`
(since `fl.Ψ (L.γ₁ s) = rayPt α₁ (L.τ s)` and `‖dynPhi (rayPt α₁ t)‖ = t`), and the right-hand
side is a continuous function of `s`.  Hence a sequence `γ₁ (s n) → γ₁ s₀` forces
`τ (s n) → τ s₀`; so points with `‖γ₁ s - γ₁ s₀‖` arbitrarily small cannot keep the level `ε`-far
from `τ s₀`. -/
theorem rayCylLift_tau_far_bound {c : ℂ} (d : Work.EL.RootParabolic c)
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) d.z₁)
    (L : Work.ELRig.RayCylLift d fl) {s₀ : ℝ} {ε : ℝ} (hε : 0 < ε) :
    ∃ c' > 0, ∀ s : ℝ, ε ≤ |L.τ s - L.τ s₀| → c' ≤ ‖L.γ₁ s - L.γ₁ s₀‖ := by
  -- `τ` is the modulus of the Böttcher value of the lift point.
  have hτ_eq : ∀ s : ℝ,
      L.τ s = ‖Work.EL.dynPhi c d.φ (fl.Ψ (L.γ₁ s))‖ := by
    intro s
    rw [L.hΨ₁ s, Work.Top.NakaneData.Phi_rayPt d.hN (L.hτ1 s),
      Work.Top.NakaneData.norm_rayPoint, abs_of_pos (lt_trans zero_lt_one (L.hτ1 s))]
  -- that expression is continuous at `γ₁ s₀`.
  have hcont : ContinuousAt (fun w : ℂ => ‖Work.EL.dynPhi c d.φ (fl.Ψ w)‖) (L.γ₁ s₀) := by
    have hq : fl.Ψ (L.γ₁ s₀) ∉ Work.EL.K c := by
      rw [L.hΨ₁ s₀]; exact Work.EL.rayPt_notMem_K d.hN (L.hτ1 s₀)
    have hdyn : ContinuousAt (Work.EL.dynPhi c d.φ) (fl.Ψ (L.γ₁ s₀)) :=
      (continuousOn_dynPhi (c := c) (d := d)).continuousAt
        ((Work.ParamRays.isClosed_filledJulia c).isOpen_compl.mem_nhds hq)
    exact (hdyn.comp (fl.Ψ_diff.continuous.continuousAt)).norm
  by_contra hcon
  push_neg at hcon
  -- a sequence `s n` with `ε ≤ |τ (s n) - τ s₀|` but `γ₁ (s n) → γ₁ s₀`
  have hseq : ∀ n : ℕ, ∃ s : ℝ,
      ε ≤ |L.τ s - L.τ s₀| ∧ ‖L.γ₁ s - L.γ₁ s₀‖ < 1 / ((n : ℝ) + 1) := by
    intro n
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    obtain ⟨s, hs1, hs2⟩ := hcon (1 / ((n : ℝ) + 1)) hpos
    exact ⟨s, hs1, hs2⟩
  choose s hs using hseq
  have hs1 : ∀ n : ℕ, ε ≤ |L.τ (s n) - L.τ s₀| := fun n => (hs n).1
  have hs2 : ∀ n : ℕ, ‖L.γ₁ (s n) - L.γ₁ s₀‖ < 1 / ((n : ℝ) + 1) := fun n => (hs n).2
  have htend_γ : Tendsto (fun n : ℕ => L.γ₁ (s n)) atTop (𝓝 (L.γ₁ s₀)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => le_of_lt (hs2 n)) ?_
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have htend_τ : Tendsto (fun n : ℕ => L.τ (s n)) atTop (𝓝 (L.τ s₀)) := by
    have h := hcont.tendsto.comp htend_γ
    simpa only [Function.comp_def, ← hτ_eq] using h
  have hu : Tendsto (fun n : ℕ => L.τ (s n) - L.τ s₀) atTop (𝓝 0) := by
    simpa using htend_τ.sub_const (L.τ s₀)
  have hnorm : Tendsto (fun n : ℕ => |L.τ (s n) - L.τ s₀|) atTop (𝓝 0) := by
    simpa using hu.norm
  have hle : ε ≤ 0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hnorm (Filter.Eventually.of_forall hs1)
  linarith

end Work.ELRig
