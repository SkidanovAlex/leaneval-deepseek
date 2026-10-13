/-
# `Work.R1G.GTest` — the **visible test perturbation** `g = ε·z²e^{-z}·sin(2θ)`

A concrete, analytic, exponentially decaying perturbation of the self-similar profile which is
*nonzero at a prescribed visible point* `(z, θ) = (1, π/4)` of the open quadrant.  It is the witness
for `Work.R1G.exists_profileData_g_visible`.

Why this shape:

* `z²e^{-z}` vanishes to *second* order at `z = 0`, which is what `ProfileData.hquad0` (the value)
  and `ProfileData.hquad` (the `z`-derivative) require — and, unlike a compactly supported bump, it
  is *analytic on all of `ℝ²`*, which is what `Work.Spaces.SmoothNbhd` (an `≥ ω`-order condition,
  see `Work.Stability.Cutoff`) requires;
* `sin(2θ)` vanishes at the two angular boundaries `θ = 0`, `θ = π/2` (`VanishTheta`), and it is
  dominated by the angular vanishing factor `Γ(α,θ) = (sinθcos²θ)^α` of the profile
  (`|sin2θ| ≤ 2Γ(α,θ)` for `θ ∈ Iθ`, `0 < α ≤ 1`), which gives the `hvan` field;
* both factors are entire, so every field of `ProfileData` that is a *regularity* statement is
  immediate, and the exponentially decaying factor makes every weighted `H²` integral converge.

The module records the definitions, the explicit `z`- and `θ`-derivatives (both the plain
`∂_z^j ∂_θ^i` family and the weighted `D_z^j D_θ^i` family used by `Work.Spaces.HkIntegrand`), the
vanishing at the origin and at the angular boundary, and the non-vanishing at the visible point.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.ConstructionInstance.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

namespace Work.R1G

/-! ## The perturbation and its two factors -/

/-- The radial factor `z ↦ z²e^{-z}`: vanishing to second order at `z = 0`, exponentially decaying
at `+∞`, entire. -/
def gPhi (z : ℝ) : ℝ := z ^ 2 * Real.exp (-z)

/-- The angular factor `θ ↦ sin(2θ)`: vanishing at `θ = 0` and `θ = π/2`, entire. -/
def gPsi (θ : ℝ) : ℝ := Real.sin (2 * θ)

/-- **The visible test perturbation**: `g(z,θ) = ε·z²e^{-z}·sin(2θ)`. -/
def gTest (ε : ℝ) : ℝ → ℝ → ℝ := fun z θ => ε * gPhi z * gPsi θ

theorem gTest_apply (ε z θ : ℝ) : gTest ε z θ = ε * gPhi z * gPsi θ := rfl

/-! ## The explicit derivatives -/

/-- `∂_z gPhi`. -/
def gPhi1 (z : ℝ) : ℝ := (2 * z - z ^ 2) * Real.exp (-z)

/-- `∂_z² gPhi`. -/
def gPhi2 (z : ℝ) : ℝ := (2 - 4 * z + z ^ 2) * Real.exp (-z)

/-- `D_z gPhi = z ∂_z gPhi`. -/
def gPhiD1 (z : ℝ) : ℝ := (2 * z ^ 2 - z ^ 3) * Real.exp (-z)

/-- `∂_z (D_z gPhi)`: the plain `z`-derivative of `gPhiD1`. -/
def gPhiD1' (z : ℝ) : ℝ := (4 * z - 5 * z ^ 2 + z ^ 3) * Real.exp (-z)

/-- `D_z² gPhi`. -/
def gPhiD2 (z : ℝ) : ℝ := (4 * z ^ 2 - 5 * z ^ 3 + z ^ 4) * Real.exp (-z)

/-- `∂_θ gPsi`. -/
def gPsi1 (θ : ℝ) : ℝ := 2 * Real.cos (2 * θ)

/-- `∂_θ² gPsi`. -/
def gPsi2 (θ : ℝ) : ℝ := -4 * Real.sin (2 * θ)

/-- `D_θ gPsi = sin(2θ) ∂_θ gPsi = sin(4θ)`. -/
def gPsiD1 (θ : ℝ) : ℝ := Real.sin (4 * θ)

/-- `D_θ² gPsi = 4 sin(2θ) cos(4θ)`. -/
def gPsiD2 (θ : ℝ) : ℝ := 4 * Real.sin (2 * θ) * Real.cos (4 * θ)

/-! ## The elementary derivative computations -/

theorem hasDerivAt_gPhi (z : ℝ) : HasDerivAt gPhi (gPhi1 z) z := by
  have h1 : HasDerivAt (fun z : ℝ => z ^ 2) (2 * z ^ (2 - 1)) z := hasDerivAt_pow 2 z
  have h2 : HasDerivAt (fun z : ℝ => Real.exp (-z)) (Real.exp (-z) * (-1)) z := by
    have h := (hasDerivAt_id z).neg.exp
    simpa using h
  have hm := h1.mul h2
  unfold gPhi gPhi1
  convert hm using 1
  ring

theorem hasDerivAt_gPhi1 (z : ℝ) : HasDerivAt gPhi1 (gPhi2 z) z := by
  have h1 : HasDerivAt (fun z : ℝ => 2 * z - z ^ 2) (2 - 2 * z) z := by
    have ha : HasDerivAt (fun z : ℝ => 2 * z) 2 z := by
      simpa using (hasDerivAt_id z).const_mul 2
    have hb : HasDerivAt (fun z : ℝ => z ^ 2) (2 * z) z := by
      simpa using hasDerivAt_pow 2 (𝕜 := ℝ) z
    exact ha.sub hb
  have h2 : HasDerivAt (fun z : ℝ => Real.exp (-z)) (Real.exp (-z) * (-1)) z := by
    have h := (hasDerivAt_id z).neg.exp
    simpa using h
  have hm := h1.mul h2
  unfold gPhi1 gPhi2
  convert hm using 1
  ring

theorem hasDerivAt_gPsi (θ : ℝ) : HasDerivAt gPsi (gPsi1 θ) θ := by
  have h1 : HasDerivAt (fun θ : ℝ => 2 * θ) 2 θ := by
    simpa using (hasDerivAt_id θ).const_mul 2
  have h := h1.sin
  unfold gPsi gPsi1
  convert h using 1
  ring

theorem hasDerivAt_gPsi1 (θ : ℝ) : HasDerivAt gPsi1 (gPsi2 θ) θ := by
  have h1 : HasDerivAt (fun θ : ℝ => 2 * θ) 2 θ := by
    simpa using (hasDerivAt_id θ).const_mul 2
  have h := (h1.cos).const_mul 2
  unfold gPsi1 gPsi2
  convert h using 1 <;> ring

/-- `∂_θ (sin(4θ)) = 4cos(4θ)`. -/
theorem hasDerivAt_gPsiD1 (θ : ℝ) :
    HasDerivAt gPsiD1 (4 * Real.cos (4 * θ)) θ := by
  have h1 : HasDerivAt (fun θ : ℝ => 4 * θ) 4 θ := by
    simpa using (hasDerivAt_id θ).const_mul 4
  have h := h1.sin
  unfold gPsiD1
  convert h using 1
  ring

/-- `sin(4θ) = 2 sin(2θ)cos(2θ)`. -/
theorem gPsiD1_eq (θ : ℝ) : gPsiD1 θ = 2 * Real.sin (2 * θ) * Real.cos (2 * θ) := by
  have h2 := Real.sin_two_mul (2 * θ)
  rw [show (2:ℝ) * (2 * θ) = 4 * θ by ring] at h2
  rw [gPsiD1, h2]

/-- `HasDerivAt gPhiD1 (gPhiD1' z) z`. -/
theorem hasDerivAt_gPhiD1 (z : ℝ) : HasDerivAt gPhiD1 (gPhiD1' z) z := by
  have h1 : HasDerivAt (fun z : ℝ => 2 * z ^ 2 - z ^ 3) (4 * z - 3 * z ^ 2) z := by
    have ha : HasDerivAt (fun z : ℝ => 2 * z ^ 2) (2 * (2 * z ^ (2 - 1))) z :=
      (hasDerivAt_pow 2 z).const_mul 2
    have hb : HasDerivAt (fun z : ℝ => z ^ 3) (3 * z ^ (3 - 1)) z := hasDerivAt_pow 3 z
    have hs := ha.sub hb
    convert hs using 1 <;> ring
  have h2 : HasDerivAt (fun z : ℝ => Real.exp (-z)) (Real.exp (-z) * (-1)) z := by
    have h := (hasDerivAt_id z).neg.exp
    simpa using h
  have hm := h1.mul h2
  unfold gPhiD1 gPhiD1'
  convert hm using 1 <;> ring

/-- `z · ∂_z(D_z gPhi) = D_z² gPhi`. -/
theorem z_mul_gPhiD1' (z : ℝ) : z * gPhiD1' z = gPhiD2 z := by
  unfold gPhiD1' gPhiD2
  ring

/-! ## `∂_z` and `∂_θ` of the perturbation -/

theorem pz_gTest (ε : ℝ) :
    Work.Spaces.pz (gTest ε) = fun z θ => ε * gPhi1 z * gPsi θ := by
  funext z θ
  have h : HasDerivAt (fun z : ℝ => ε * gPhi z) (ε * gPhi1 z) z :=
    (hasDerivAt_gPhi z).const_mul ε
  have hfun : (fun z' : ℝ => gTest ε z' θ) = fun z' => (ε * gPhi z') * gPsi θ := by
    funext z'; rw [gTest_apply]
  simp only [Work.Spaces.pz]
  rw [hfun, deriv_mul_const h.differentiableAt (gPsi θ), h.deriv] <;> ring

theorem pzIter_two_gTest (ε : ℝ) :
    Work.Spaces.pzIter 2 (gTest ε) = fun z θ => ε * gPhi2 z * gPsi θ := by
  have hinner := pz_gTest ε
  funext z θ
  have h : HasDerivAt (fun z : ℝ => ε * gPhi1 z) (ε * gPhi2 z) z :=
    (hasDerivAt_gPhi1 z).const_mul ε
  have hfun : (fun z' : ℝ => (fun z θ => ε * gPhi1 z * gPsi θ) z' θ)
      = fun z' => (ε * gPhi1 z') * gPsi θ := by
    funext z'; rfl
  simp only [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero]
  rw [hinner]
  simp only [Work.Spaces.pz]
  rw [hfun, deriv_mul_const h.differentiableAt (gPsi θ), h.deriv] <;> ring

theorem pth_gTest (ε : ℝ) :
    Work.Spaces.pth (gTest ε) = fun z θ => ε * gPhi z * gPsi1 θ := by
  funext z θ
  have hG : HasDerivAt gPsi (gPsi1 θ) θ := hasDerivAt_gPsi θ
  have hfun : (fun θ' : ℝ => gTest ε z θ') = fun θ' => (ε * gPhi z) * gPsi θ' := by
    funext θ'; rw [gTest_apply]
  simp only [Work.Spaces.pth]
  rw [hfun, deriv_const_mul (ε * gPhi z) hG.differentiableAt, hG.deriv] <;> ring

theorem pthIter_two_gTest (ε : ℝ) :
    Work.Spaces.pthIter 2 (gTest ε) = fun z θ => ε * gPhi z * gPsi2 θ := by
  have hinner := pth_gTest ε
  funext z θ
  have hG : HasDerivAt gPsi1 (gPsi2 θ) θ := hasDerivAt_gPsi1 θ
  have hfun : (fun θ' : ℝ => (fun z θ => ε * gPhi z * gPsi1 θ) z θ')
      = fun θ' => (ε * gPhi z) * gPsi1 θ' := by
    funext θ'; rfl
  simp only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero]
  rw [hinner]
  simp only [Work.Spaces.pth]
  rw [hfun, deriv_const_mul (ε * gPhi z) hG.differentiableAt, hG.deriv] <;> ring

theorem pz_pth_gTest (ε : ℝ) :
    Work.Spaces.pz (Work.Spaces.pth (gTest ε)) = fun z θ => ε * gPhi1 z * gPsi1 θ := by
  have hinner := pth_gTest ε
  funext z θ
  have h : HasDerivAt (fun z : ℝ => ε * gPhi z) (ε * gPhi1 z) z :=
    (hasDerivAt_gPhi z).const_mul ε
  have hfun : (fun z' : ℝ => (fun z θ => ε * gPhi z * gPsi1 θ) z' θ)
      = fun z' => (ε * gPhi z') * gPsi1 θ := by
    funext z'; rfl
  rw [hinner]
  simp only [Work.Spaces.pz]
  rw [hfun, deriv_mul_const h.differentiableAt (gPsi1 θ), h.deriv] <;> ring

/-! ## `D_z` and `D_θ` of the perturbation -/

theorem DzIter_one_gTest (ε : ℝ) :
    Work.Spaces.DzIter 1 (gTest ε) = fun z θ => ε * gPhiD1 z * gPsi θ := by
  funext z θ
  change z * Work.Spaces.pz (gTest ε) z θ = ε * gPhiD1 z * gPsi θ
  rw [show Work.Spaces.pz (gTest ε) z θ = ε * gPhi1 z * gPsi θ by rw [pz_gTest]]
  unfold gPhiD1 gPhi1
  ring

theorem DzIter_two_gTest (ε : ℝ) :
    Work.Spaces.DzIter 2 (gTest ε) = fun z θ => ε * gPhiD2 z * gPsi θ := by
  have hD1 := DzIter_one_gTest ε
  funext z θ
  have h : HasDerivAt gPhiD1 (gPhiD1' z) z := hasDerivAt_gPhiD1 z
  have hfun : (fun z' : ℝ => (fun z θ => ε * gPhiD1 z * gPsi θ) z' θ)
      = fun z' => (ε * gPhiD1 z') * gPsi θ := by
    funext z'; rfl
  change z * Work.Spaces.pz (Work.Spaces.DzIter 1 (gTest ε)) z θ = ε * gPhiD2 z * gPsi θ
  rw [hD1]
  simp only [Work.Spaces.pz]
  rw [hfun, deriv_mul_const (h.differentiableAt.const_mul ε) (gPsi θ), (h.const_mul ε).deriv]
  rw [← z_mul_gPhiD1' z]
  ring

theorem DthIter_one_gTest (ε : ℝ) :
    Work.Spaces.DthIter 1 (gTest ε) = fun z θ => ε * gPhi z * gPsiD1 θ := by
  funext z θ
  change Real.sin (2 * θ) * Work.Spaces.pth (gTest ε) z θ = ε * gPhi z * gPsiD1 θ
  rw [show Work.Spaces.pth (gTest ε) z θ = ε * gPhi z * gPsi1 θ by rw [pth_gTest]]
  rw [gPsiD1_eq]
  unfold gPsi1
  ring

theorem DthIter_two_gTest (ε : ℝ) :
    Work.Spaces.DthIter 2 (gTest ε) = fun z θ => ε * gPhi z * gPsiD2 θ := by
  have hD1 := DthIter_one_gTest ε
  funext z θ
  have hfun : (fun θ' : ℝ => (fun z θ => ε * gPhi z * gPsiD1 θ) z θ')
      = fun θ' => (ε * gPhi z) * gPsiD1 θ' := by
    funext θ'; rfl
  change Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.DthIter 1 (gTest ε)) z θ
      = ε * gPhi z * gPsiD2 θ
  rw [hD1]
  simp only [Work.Spaces.pth]
  rw [hfun, deriv_const_mul (ε * gPhi z) (hasDerivAt_gPsiD1 θ).differentiableAt,
    (hasDerivAt_gPsiD1 θ).deriv]
  unfold gPsiD2
  ring

/-! ## The mixed derivatives needed by `HkIntegrand` -/

theorem mixed_zero_one_gTest (ε : ℝ) :
    Work.Spaces.mixed 0 1 (gTest ε) = fun z θ => ε * gPhi z * gPsiD1 θ := by
  rw [Work.Spaces.mixed, Work.Spaces.DzIter_zero]
  exact DthIter_one_gTest ε

theorem mixed_zero_two_gTest (ε : ℝ) :
    Work.Spaces.mixed 0 2 (gTest ε) = fun z θ => ε * gPhi z * gPsiD2 θ := by
  rw [Work.Spaces.mixed, Work.Spaces.DzIter_zero]
  exact DthIter_two_gTest ε

theorem mixed_one_one_gTest (ε : ℝ) :
    Work.Spaces.mixed 1 1 (gTest ε) = fun z θ => ε * gPhiD1 z * gPsiD1 θ := by
  have hD1 := DthIter_one_gTest ε
  funext z θ
  have h : HasDerivAt (fun z : ℝ => ε * gPhi z) (ε * gPhi1 z) z :=
    (hasDerivAt_gPhi z).const_mul ε
  have hfun : (fun z' : ℝ => (fun z θ => ε * gPhi z * gPsiD1 θ) z' θ)
      = fun z' => (ε * gPhi z') * gPsiD1 θ := by
    funext z'; rfl
  change z * Work.Spaces.pz (Work.Spaces.DthIter 1 (gTest ε)) z θ
      = ε * gPhiD1 z * gPsiD1 θ
  rw [hD1]
  simp only [Work.Spaces.pz]
  rw [hfun, deriv_mul_const h.differentiableAt (gPsiD1 θ), h.deriv]
  unfold gPhiD1 gPhi1
  ring

/-! ## Vanishing and the visible point -/

theorem gPhi_zero : gPhi 0 = 0 := by simp [gPhi]

theorem gPsi_zero : gPsi 0 = 0 := by simp [gPsi]

theorem gPsi_pi_half : gPsi (Real.pi / 2) = 0 := by
  have h : 2 * (Real.pi / 2) = Real.pi := by ring
  rw [gPsi, h, Real.sin_pi]

theorem gPhi1_zero : gPhi1 0 = 0 := by simp [gPhi1]

theorem gTest_vanish_theta (ε : ℝ) : Work.Spaces.VanishTheta (gTest ε) := by
  refine ⟨fun z => ?_, fun z => ?_⟩
  · rw [gTest_apply, gPsi_zero, mul_zero]
  · rw [gTest_apply, gPsi_pi_half, mul_zero]

theorem gTest_zero_z (ε θ : ℝ) : gTest ε 0 θ = 0 := by
  rw [gTest_apply, gPhi_zero, mul_zero, zero_mul]

theorem pz_gTest_zero_z (ε θ : ℝ) : Work.Spaces.pz (gTest ε) 0 θ = 0 := by
  rw [pz_gTest]
  simp [gPhi1_zero]

/-- **The perturbation is entire**: `SmoothNbhd` (analyticity on a neighbourhood of the closed
quadrant) holds for every amplitude. -/
theorem gTest_smoothNbhd (ε : ℝ) : Work.Spaces.SmoothNbhd (gTest ε) := by
  unfold Work.Spaces.SmoothNbhd gTest gPhi gPsi
  fun_prop

/-- **The visible non-vanishing**: `gTest ε` is nonzero at `(z,θ) = (1, π/4)` whenever `ε ≠ 0`. -/
theorem gTest_visible {ε : ℝ} (hε : ε ≠ 0) : gTest ε 1 (Real.pi / 4) ≠ 0 := by
  have hsin : Real.sin (2 * (Real.pi / 4)) = 1 := by
    have : 2 * (Real.pi / 4) = Real.pi / 2 := by ring
    rw [this, Real.sin_pi_div_two]
  have hexp : Real.exp (-1) ≠ 0 := Real.exp_ne_zero _
  have hval : gTest ε 1 (Real.pi / 4) = ε * Real.exp (-1) := by
    simp only [gTest_apply, gPhi, gPsi, hsin]
    norm_num
  rw [hval]
  exact mul_ne_zero hε hexp

end Work.R1G
