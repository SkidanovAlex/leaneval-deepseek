/-
# `Work.FTS.MeridianDyn.Smooth.profFamOdd_contDiffAt`

The odd-extended profile family `profFamOdd α g` of the dynamic meridian bridge is `C¹` at every
point `(Z,Θ,τ)` of the **open** slab `Z > 0`, `0 < Θ < π/2`, `τ > -1` (for a regular family `g`,
`RegPkg α g`).

The point of the statement is the *odd extension*: `profFamOdd` is built from
`ConstructionInstance.profile`, which is
`θ ↦ if 0 ≤ θ then F_*(z,θ) + g z θ else -(F_*(z,-θ) + g z (-θ))`.  At a point with `Θ > 0` the
`if`-branch is the `0 ≤ θ` one, so *near* the point the odd extension is just `F_* + g`; the
regularity therefore reduces to the regularity of `F_*` (an explicit elementary function) and the
joint regularity of `g` supplied by `RegPkg.smooth`.

This is the reason the statement is stated at an *interior* point with `Θ > 0`: on the plane
`θ = 0` the odd extension is not differentiable in general (the two branches meet with opposite
signs), and the file's consumers only ever use interior points.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Submission.Work.FTS.MeridianDyn.Defs
import Submission.Work.FTS.Galerkin.Defs
import Submission.Work.FTS.Regularity.Defs
import Submission.Work.ConstructionInstance.Defs
import Submission.Work.Stability.Cutoff
import Submission.Work.Construction.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.MeridianDyn.Smooth

open Filter Set
open scoped Topology

/-! ## Smoothness of the two factors of the profile `F_*` -/

/-- `Γ(θ) = (sinθ·cos²θ)^{α/3}` is `C¹` at every interior angle `Θ ∈ (0, π/2)`.

The base `sinθ·cos²θ` is strictly positive there, so the (total) real power is `C¹` by
`Real.contDiffAt_rpow_const`. -/
lemma contDiffAt_Gam (α : ℝ) {Θ : ℝ} (hΘ : 0 < Θ) (hΘ1 : Θ < Real.pi / 2) :
    ContDiffAt ℝ 1 (fun θ : ℝ => Work.Spaces.Gam α θ) Θ := by
  have hbase : ContDiffAt ℝ 1 (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2) Θ := by fun_prop
  have hne : Real.sin Θ * Real.cos Θ ^ 2 ≠ 0 := by
    have h1 : 0 < Real.sin Θ := Real.sin_pos_of_pos_of_lt_pi hΘ (by linarith [hΘ1, Real.pi_pos])
    have h2 : 0 < Real.cos Θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [hΘ, Real.pi_pos], hΘ1⟩
    positivity
  have hrpow := Real.contDiffAt_rpow_const (x := Real.sin Θ * Real.cos Θ ^ 2) (p := α / 3)
    (n := 1) (Or.inl hne)
  have hmain : ContDiffAt ℝ 1
      ((fun x : ℝ => x ^ (α / 3)) ∘ (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2)) Θ :=
    hrpow.comp Θ hbase
  exact hmain

/-- The singular profile
`F_*(z,θ) = α·(Γ(θ)/c(α))·(2z/(1+z)²)` is `C¹` at every point with `z > 0` and
`0 < θ < π/2`: it is a product of a `C¹` function of `θ` (`Γ/c`, `c` constant) and the rational
function `z ↦ 2z/(1+z)²`, which is `C¹` at `Z > 0` (its pole sits at `z = -1`). -/
lemma contDiffAt_Fstar (α τ : ℝ) {Z Θ : ℝ} (hZ : 0 < Z) (hΘ : 0 < Θ)
    (hΘ1 : Θ < Real.pi / 2) :
    ContDiffAt ℝ 1 (fun p : ℝ × ℝ × ℝ => Work.Construction.Fstar α p.1 p.2.1) (Z, Θ, τ) := by
  have hsnd2 : ContDiffAt ℝ 1 (fun p : ℝ × ℝ × ℝ => p.2.1) (Z, Θ, τ) := by fun_prop
  have hfst : ContDiffAt ℝ 1 (fun p : ℝ × ℝ × ℝ => p.1) (Z, Θ, τ) := by fun_prop
  have hG' : ContDiffAt ℝ 1 ((Work.Spaces.Gam α) ∘ (fun p : ℝ × ℝ × ℝ => p.2.1)) (Z, Θ, τ) :=
    (contDiffAt_Gam α hΘ hΘ1).comp (Z, Θ, τ) hsnd2
  have hG : ContDiffAt ℝ 1 (fun p : ℝ × ℝ × ℝ => Work.Spaces.Gam α p.2.1) (Z, Θ, τ) := hG'
  have hG2 : ContDiffAt ℝ 1
      (fun p : ℝ × ℝ × ℝ => α * (Work.Spaces.Gam α p.2.1 / Work.Spaces.c α)) (Z, Θ, τ) :=
    (contDiffAt_const (c := α)).mul (hG.div_const (Work.Spaces.c α))
  have hF : ContDiffAt ℝ 1 (fun p : ℝ × ℝ × ℝ => Work.FM.Fstar p.1) (Z, Θ, τ) := by
    have hz : ContDiffAt ℝ 1 (fun z : ℝ => Work.FM.Fstar z) Z := by
      change ContDiffAt ℝ 1 (fun z : ℝ => 2 * z / (1 + z) ^ 2) Z
      fun_prop (disch := positivity)
    have hF' : ContDiffAt ℝ 1 ((fun z : ℝ => Work.FM.Fstar z) ∘ (fun p : ℝ × ℝ × ℝ => p.1))
        (Z, Θ, τ) := hz.comp (Z, Θ, τ) hfst
    exact hF'
  exact hG2.mul hF

/-! ## The target -/

theorem profFamOdd_contDiffAt {α : ℝ} (hα : 0 < α) {g : Work.FTS.MeridianDyn.Fam}
    (hreg : Work.FTS.Galerkin.RegPkg α g) {Z Θ τ : ℝ}
    (hZ : 0 < Z) (hΘ : 0 < Θ) (hΘ1 : Θ < Real.pi / 2) (hτ : -1 < τ) :
    ContDiffAt ℝ 1 (fun p : ℝ × ℝ × ℝ => Work.FTS.MeridianDyn.profFamOdd α g p.1 p.2.1 p.2.2)
      (Z, Θ, τ) := by
  -- the open slab of `RegPkg.smooth` contains the point
  have hmem : (Z, Θ, τ) ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)
      ×ˢ Set.Ioi (-1 : ℝ) := ⟨hZ, ⟨hΘ, hΘ1⟩, hτ⟩
  have hU : Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2) ×ˢ Set.Ioi (-1 : ℝ)
      ∈ 𝓝 (Z, Θ, τ) :=
    (isOpen_Ioi.prod (isOpen_Ioo.prod isOpen_Ioi)).mem_nhds hmem
  have hle : (1 : WithTop ℕ∞) ≤ Work.Stability.smoothOrder := by
    simp [Work.Stability.smoothOrder]
  -- the joint regularity of `g` at the point
  have hg : ContDiffAt ℝ 1 (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2) (Z, Θ, τ) :=
    (hreg.smooth.contDiffAt hU).of_le hle
  -- the profile `F_*` is `C¹` at the point
  have hF := contDiffAt_Fstar α τ hZ hΘ hΘ1
  have hsum : ContDiffAt ℝ 1
      (fun p : ℝ × ℝ × ℝ => Work.Construction.Fstar α p.1 p.2.1 + g p.1 p.2.1 p.2.2)
      (Z, Θ, τ) :=
    hF.add hg
  -- near the point `θ > 0`, so the odd extension is the `0 ≤ θ` branch `F_* + g`
  refine hsum.congr_of_eventuallyEq ?_
  have hpos : {p : ℝ × ℝ × ℝ | 0 < p.2.1} ∈ 𝓝 (Z, Θ, τ) :=
    (isOpen_lt continuous_const (continuous_fst.comp continuous_snd)).mem_nhds hΘ
  filter_upwards [hpos] with p hp
  rw [Work.FTS.MeridianDyn.profFamOdd_apply,
    Work.ConstructionInstance.profile_of_nonneg (le_of_lt hp)]
  rfl

end Work.FTS.MeridianDyn.Smooth
