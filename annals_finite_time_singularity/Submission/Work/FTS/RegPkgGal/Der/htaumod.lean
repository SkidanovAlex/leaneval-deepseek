import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.RegPkgGal.Defs
import Submission.Work.FTS.RegPkgGal.R1
import Submission.Work.FTS.RegPkgGal.R1b.extG_cont
import Submission.Work.FTS.Regularity.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.RegPkgGal.Der.htaumod` — the fake-time Hölder modulus of the extension `g̃`

**Statement.**  Under the joint `C¹`-regularity `hcont` of `(z,τ) ↦ g̃ z θ τ` on the open strip
`(-1,∞) × (-1,S+1)` (one angle `θ ∈ Iθ` at a time) and the `Jet α S Nd` bound `hdt` on the
fake-time derivative `∂_τg̃` on the closed domain `z ≥ 0`, `θ ∈ Iθ`, `τ ∈ [0,S]`, the function
`τ ↦ g̃ z θ τ` is `α`-Hölder on `[0,S]`, uniformly in `(z,θ)` in that domain.

**Proof.**  For fixed `z ≥ 0`, `θ ∈ Iθ` the slice `t ↦ g̃ z θ t` is differentiable at every
`t ∈ [0,S]`: this is the chain rule along the affine curve `t ↦ (z,t)` applied to the joint
`C¹`-function, whose domain `z > -1` contains `z ≥ 0` (`differentiableAt_extG_slice`).  The
mean value theorem on the convex segment `[0,S]` (`norm_image_sub_le_of_norm_deriv_le`) then
bounds the increment by `Nd · |τ - τ'|`, using that *the* derivative
`deriv (fun s => g̃ z θ s) t` is the function whose `Jet` is `hdt`.  Finally `|τ - τ'| ≤ S`, so
`|τ - τ'| = |τ - τ'|^α · |τ - τ'|^{1-α} ≤ S^{1-α} · |τ - τ'|^α` (`Real.rpow_add'` plus
monotonicity of `x ↦ x^{1-α}`, `1 - α ≥ 0`), giving the constant `Lt = Nd · S^{1-α}`.

Note that no case distinction at `z = 0` (nor the boundedness data `hsup`) is needed: the
extension is `C¹` on the whole half-strip `z > -1` and the derivative jet already covers the
closed domain `z ≥ 0`. -/

namespace Work.FTS.RegPkgGal.Der

open Set

/-- **The `τ`-slice of the extension is differentiable.**

If the uncurried family `(z,τ) ↦ g̃ z θ τ` is jointly `C¹` on the open strip
`(-1,∞) × (-1,S+1)` at a fixed angle, then the one-variable slice `t ↦ g̃ z θ t` is
differentiable at every interior point `c` of the strip.  This is the chain rule along the
affine curve `t ↦ (z,t)`, whose derivative is the second basis vector `(0,1)`. -/
theorem differentiableAt_extG_slice {S : ℝ} {g : Work.FTS.RegPkgGal.Fam} {θ z c : ℝ}
    (h : ContDiffOn ℝ 1 (fun q : ℝ × ℝ => Work.FTS.RegPkgGal.extG g q.1 θ q.2)
      (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (S + 1)))
    (hz : z ∈ Set.Ioi (-1)) (hc : c ∈ Set.Ioo (-1) (S + 1)) :
    DifferentiableAt ℝ (fun s => Work.FTS.RegPkgGal.extG g z θ s) c := by
  have hopen : IsOpen (Set.Ioi (-1 : ℝ) ×ˢ Set.Ioo (-1 : ℝ) (S + 1)) :=
    isOpen_Ioi.prod isOpen_Ioo
  have hmem : (z, c) ∈ Set.Ioi (-1 : ℝ) ×ˢ Set.Ioo (-1 : ℝ) (S + 1) := ⟨hz, hc⟩
  have hnb : (Set.Ioi (-1 : ℝ) ×ˢ Set.Ioo (-1 : ℝ) (S + 1)) ∈ nhds (z, c) :=
    hopen.mem_nhds hmem
  have hca : ContDiffAt ℝ 1 (fun q : ℝ × ℝ => Work.FTS.RegPkgGal.extG g q.1 θ q.2) (z, c) :=
    h.contDiffAt hnb
  have hder : HasDerivAt (fun s : ℝ => (z, s)) ((0 : ℝ), (1 : ℝ)) c := by
    have h0 := (hasDerivAt_const (c := z) (x := c)).prodMk (hasDerivAt_id c)
    simpa using h0
  have hcomp := (hca.differentiableAt one_ne_zero).hasFDerivAt.comp_hasDerivAt c hder
  have h2 : DifferentiableAt ℝ
      ((fun q : ℝ × ℝ => Work.FTS.RegPkgGal.extG g q.1 θ q.2) ∘ fun s : ℝ => (z, s)) c :=
    hcomp.differentiableAt
  convert h2 using 1
  ext s
  rfl

theorem htaumod {α S : ℝ} {g : Work.FTS.RegPkgGal.Fam} (hα : 0 < α) (hα1 : α ≤ 1) (hS : 0 < S)
    (hcont : ∀ θ ∈ Work.Spaces.Iθ,
      ContDiffOn ℝ 1 (fun q : ℝ × ℝ => Work.FTS.RegPkgGal.extG g q.1 θ q.2)
        (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (S + 1)))
    (hdt : ∃ Nd : ℝ, Work.FTS.Regularity.Jet α S Nd
      (fun z θ τ => deriv (fun s => Work.FTS.RegPkgGal.extG g z θ s) τ))
    (hsup : ∃ M : ℝ, 0 ≤ M ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |Work.FTS.RegPkgGal.extG g z θ τ| ≤ M
        ∧ |Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ) z θ| ≤ M) :
    ∃ Lt : ℝ, 0 ≤ Lt ∧ ∀ τ ∈ Set.Icc 0 S, ∀ τ' ∈ Set.Icc 0 S, ∀ z : ℝ, 0 ≤ z →
      ∀ θ ∈ Work.Spaces.Iθ,
        |Work.FTS.RegPkgGal.extG g z θ τ - Work.FTS.RegPkgGal.extG g z θ τ'|
          ≤ Lt * |τ - τ'| ^ α := by
  obtain ⟨Nd, hNd⟩ := hdt
  have hLt0 : 0 ≤ Nd * S ^ (1 - α) :=
    mul_nonneg hNd.1 (Real.rpow_nonneg hS.le (1 - α))
  refine ⟨Nd * S ^ (1 - α), hLt0, ?_⟩
  intro τ hτ τ' hτ' z hz θ hθ
  -- the fake-time slice is differentiable on the closed strip, with derivative bounded by `Nd`
  have hdiff : ∀ c ∈ Set.Icc 0 S,
      DifferentiableAt ℝ (fun t : ℝ => Work.FTS.RegPkgGal.extG g z θ t) c := by
    intro c hc
    exact differentiableAt_extG_slice (θ := θ) (z := z) (c := c) (S := S)
      (hcont θ hθ) (Set.mem_Ioi.mpr (by linarith))
        (Set.mem_Ioo.mpr ⟨by linarith [hc.1], by linarith [hc.2, hS]⟩)
  have hbound : ∀ c ∈ Set.Icc 0 S,
      ‖deriv (fun t : ℝ => Work.FTS.RegPkgGal.extG g z θ t) c‖ ≤ Nd := by
    intro c hc
    rw [Real.norm_eq_abs]
    exact hNd.abs_le hz hθ hc
  -- the mean value theorem on the segment `[0,S]`
  have hmvt : |Work.FTS.RegPkgGal.extG g z θ τ - Work.FTS.RegPkgGal.extG g z θ τ'|
      ≤ Nd * |τ - τ'| := by
    simpa only [Real.norm_eq_abs]
      using Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound (convex_Icc 0 S) hτ' hτ
  -- the two `τ`-values lie in `[0,S]`, so `|τ - τ'| ≤ S`
  have hseg : |τ - τ'| ≤ S := by
    rw [abs_sub_le_iff]
    exact ⟨by linarith [hτ.2, hτ'.1], by linarith [hτ'.2, hτ.1]⟩
  -- `|τ - τ'| = |τ - τ'|^α · |τ - τ'|^{1-α}`, and the second factor is `≤ S^{1-α}`
  have hsplit : |τ - τ'| = |τ - τ'| ^ α * |τ - τ'| ^ (1 - α) := by
    have hsum : α + (1 - α) = 1 := by ring
    calc |τ - τ'| = |τ - τ'| ^ (α + (1 - α)) := by simp [hsum]
      _ = |τ - τ'| ^ α * |τ - τ'| ^ (1 - α) :=
            Real.rpow_add' (abs_nonneg _) (by rw [hsum]; norm_num)
  have hpow : |τ - τ'| ^ (1 - α) ≤ S ^ (1 - α) :=
    Real.rpow_le_rpow (abs_nonneg _) hseg (by linarith)
  calc |Work.FTS.RegPkgGal.extG g z θ τ - Work.FTS.RegPkgGal.extG g z θ τ'|
      ≤ Nd * |τ - τ'| := hmvt
    _ = Nd * (|τ - τ'| ^ α * |τ - τ'| ^ (1 - α)) := congrArg (fun u => Nd * u) hsplit
    _ ≤ Nd * (|τ - τ'| ^ α * S ^ (1 - α)) := by
          refine mul_le_mul_of_nonneg_left ?_ hNd.1
          exact mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg (abs_nonneg _) α)
    _ = (Nd * S ^ (1 - α)) * |τ - τ'| ^ α := by ring

end Work.FTS.RegPkgGal.Der
