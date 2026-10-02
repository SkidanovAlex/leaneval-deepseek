/-
# The `α₁`-branch data of the second return map, from a root-parabolic parameter

This file *proves* the lemma `Work.GATE.Gate.branchData_alpha1_of_rootParabolic`: from the
root-parabolic input `Work.EL.RootParabolic c` it produces the `α₁`-branch data
`Work.GATE.BranchData d.φ α₁` of the second return map `F c = (T_c)^{10} = (Tsq c)^[5]`, whose
tube `S` contains *all* the dynamical ray points of the `α₁`-window:

    ∀ θ t, 1 < t → α₁ - 1/8 < θ → θ < α₁ + 1/8 → rayPt d.hN θ t ∈ bd.S.

The tube is therefore completely explicit: it is the set `rayTube d.hN` of the ray points whose
angle lies in the open window `I = (α₁ - 1/8, α₁ + 1/8)` and whose level is `> 1`.  On it the
inverse branch `Λ` of `F` is the *Böttcher inverse branch of direction `α₁`*: since
`1024 α₁ = α₁ + 371`, the branch acts on the angle and the level by

    Λ (rayPt θ t) = rayPt ((θ + 371)/1024) (t ^ (1/1024)),

which is exactly the lift `ϑ ↦ (ϑ + 371)/1024` of the `1024`-th root that fixes the direction
`α₁` (`(α₁ + 371)/1024 = α₁`).  The window `I` is invariant under this map, `Λ` is a right
inverse of `F` on the tube (`Work.ELRig.rayPt_iterate` plus `T^[10] ((θ + 371)/1024) = θ`), and
the `α₁`-relative deviation of the Böttcher argument is divided by `1024`
(`deviation φ α₁ (Λ z) = deviation φ α₁ z / 1024`).

The helper lemmas below isolate the three ingredients:

* `bAngle_rayPt`, `liftAngle_rayPt`, `deviation_rayPt` — the Böttcher argument of a ray point:
  `bAngle φ (rayPt θ t) = θ + k` for an integer `k` (`Complex.arg_mul_cos_add_sin_mul_I_sub`),
  whence the `α`-relative lift of a ray point of angle `θ ∈ (α - 1/2, α + 1/2]` is `θ` itself and
  its deviation from `α` is `θ - α`;
* `T_iterate_ten_window` — the angle arithmetic `T^[10]((θ + 371)/1024) = θ` for `θ` in the
  window (`Work.ELNest.T_iterate_ten` plus `1023 α₁ = 371`);
* the assembly: `rayTube`, `exists_rayTube_preimage`, `branchDataAlpha1`.
-/
import Mathlib
import Submission.Work.GATE.Gate.Defs
import Submission.Work.ELRig.rayPt_iterate
import Submission.Work.ELTop.rayPt_inj
import Submission.Work.ELTop.rayPt_add_int
import Submission.Work.ELNest.T_iterate_bAng

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace Work.GATE.Gate

/-! ## The arithmetic of the root angle `α₁ = 371/1023` -/

/-- The root angle `α₁` is strictly above the half-width `1/8` of the window. -/
theorem alpha1_low : (1 / 8 : ℝ) < Work.EL.alpha1 := by
  rw [Work.EL.alpha1]; norm_num

/-- The root angle `α₁` is strictly below `1 - 1/8`, so the whole window lies in `(0, 1)`. -/
theorem alpha1_high : Work.EL.alpha1 < 1 - 1 / 8 := by
  rw [Work.EL.alpha1]; norm_num

/-- `1023 α₁ = 371`: the integer by which the `α₁`-window is shifted by the branch
`ϑ ↦ (ϑ + 371)/1024`. -/
theorem alpha1_arith : (1023 : ℝ) * Work.EL.alpha1 = 371 := by
  rw [Work.EL.alpha1]; norm_num

/-! ## The Böttcher argument of a dynamical ray point -/

/-- The Böttcher coordinate of a dynamical ray point: `φ (rayPt θ t) = t·e^{2πiθ}`. -/
theorem phi_rayPt {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) {θ t : ℝ} (ht : 1 < t) :
    φ (Work.EL.rayPt hN θ t) = Work.Top.NakaneData.rayPoint θ t := by
  rw [← Work.EL.dynPhi_of_notMem (c := c) (φ := φ) (hN.rayPt_notMem ht), hN.Phi_rayPt ht]

/-- **The Böttcher argument of a ray point**: `bAngle φ (rayPt θ t) = θ + ⌊(π - 2πθ)/(2π)⌋`, so
in particular it is `θ` up to an integer.  This is the `arg` of the exterior point
`t·(cos 2πθ + i sin 2πθ)`. -/
theorem bAngle_rayPt {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) {θ t : ℝ} (ht : 1 < t) :
    Work.GATE.bAngle φ (Work.EL.rayPt hN θ t) =
      θ + ⌊(Real.pi - 2 * Real.pi * θ) / (2 * Real.pi)⌋ := by
  rw [Work.GATE.bAngle, phi_rayPt hN ht]
  have hpt : Work.Top.NakaneData.rayPoint θ t
      = (t : ℂ) * (Complex.cos ((2 * Real.pi * θ : ℝ) : ℂ)
          + Complex.sin ((2 * Real.pi * θ : ℝ) : ℂ) * Complex.I) := by
    rw [Work.Top.NakaneData.rayPoint]
    have h' : 2 * (Real.pi : ℂ) * (θ : ℂ) * Complex.I
        = ((2 * Real.pi * θ : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [h', Complex.exp_mul_I]
  rw [hpt]
  have h := Complex.arg_mul_cos_add_sin_mul_I_sub (show (0 : ℝ) < t by linarith) (2 * Real.pi * θ)
  have key : (↑t * (Complex.cos ↑(2 * Real.pi * θ)
        + Complex.sin ↑(2 * Real.pi * θ) * Complex.I)).arg
      = 2 * Real.pi * (θ + ↑⌊(Real.pi - 2 * Real.pi * θ) / (2 * Real.pi)⌋) := by
    linarith [h]
  rw [key]
  field_simp

/-- **The `α`-relative lift of a ray point of angle in `(α - 1/2, α + 1/2]` is the angle
itself.** -/
theorem liftAngle_rayPt {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) {α θ t : ℝ} (ht : 1 < t)
    (hlo : α - 1 / 2 < θ) (hhi : θ ≤ α + 1 / 2) :
    Work.GATE.liftAngle φ α (Work.EL.rayPt hN θ t) = θ := by
  obtain ⟨k, hk⟩ : ∃ k : ℤ, Work.GATE.bAngle φ (Work.EL.rayPt hN θ t) = θ + k :=
    ⟨_, bAngle_rayPt hN ht⟩
  rw [Work.GATE.liftAngle, hk]
  have hfl : ⌊α - (θ + (k : ℝ)) + 1 / 2⌋ = ⌊α - θ + 1 / 2⌋ - k := by
    rw [show α - (θ + (k : ℝ)) + 1 / 2 = (α - θ + 1 / 2) - (k : ℝ) by ring]
    exact Int.floor_sub_intCast _ _
  have h0 : ⌊α - θ + 1 / 2⌋ = 0 := by
    rw [Int.floor_eq_zero_iff]
    exact ⟨by linarith, by linarith⟩
  rw [hfl, h0]
  push_cast
  ring

/-- **The `α`-deviation of a ray point of angle in `(α - 1/2, α + 1/2]` is `θ - α`.** -/
theorem deviation_rayPt {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) {α θ t : ℝ} (ht : 1 < t)
    (hlo : α - 1 / 2 < θ) (hhi : θ ≤ α + 1 / 2) :
    Work.GATE.deviation φ α (Work.EL.rayPt hN θ t) = θ - α := by
  rw [Work.GATE.deviation, liftAngle_rayPt hN ht hlo hhi]

/-! ## The angle arithmetic of the branch `ϑ ↦ (ϑ + 371)/1024` -/

/-- **The tenth iterate of the angle-doubling map undoes the branch on the `α₁`-window**:
`T^[10]((θ + 371)/1024) = θ` for `θ ∈ (α₁ - 1/8, α₁ + 1/8)`.  The tenth iterate of `T` is the
fractional part of `1024 θ` (`Work.ELNest.T_iterate_ten`), and `1024·(θ + 371)/1024 = θ + 371`
with `0 < θ < 1` in the window. -/
theorem T_iterate_ten_window (θ : ℝ) (h1 : Work.EL.alpha1 - 1 / 8 < θ)
    (h2 : θ < Work.EL.alpha1 + 1 / 8) : Work.EL.T^[10] ((θ + 371) / 1024) = θ := by
  rw [Work.ELNest.T_iterate_ten]
  have hmul : (1024 : ℝ) * ((θ + 371) / 1024) = θ + 371 := by field_simp
  rw [hmul]
  have hcast : (371 : ℝ) = ((371 : ℤ) : ℝ) := by norm_num
  rw [hcast, Int.fract_add_intCast]
  exact Int.fract_eq_self.mpr ⟨by linarith [alpha1_low], by linarith [alpha1_high]⟩

/-! ## The `α₁`-tube and the inverse branch -/

/-- **The `α₁`-tube of the dynamical plane**: the dynamical ray points whose angle lies in the
open window `(α₁ - 1/8, α₁ + 1/8)` and whose level is `> 1`.  This is the tube `S` of the branch
data: on it the inverse branch of `F = (T_c)^{10}` of direction `α₁` is a genuine inverse branch
of the Böttcher coordinate `t·e^{2πiθ} ↦ t^{1/1024}·e^{2πi(θ+371)/1024}`. -/
def rayTube {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) : Set ℂ :=
  {z | ∃ θ t : ℝ, Work.EL.alpha1 - 1 / 8 < θ ∧ θ < Work.EL.alpha1 + 1 / 8 ∧ 1 < t ∧
    z = Work.EL.rayPt hN θ t}

/-- **The inverse branch of the Böttcher coordinate on the tube.**  Every point `z` of the tube
has a preimage `w` under `F = (T_c)^{10}` which again lies in the tube, and the `α₁`-deviation of
its Böttcher argument is that of `z` divided by `1024`: with `z = rayPt θ t` one takes
`w = rayPt ((θ + 371)/1024) (t^{1/1024})`. -/
theorem exists_rayTube_preimage {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (hB : Work.ParamRays.IsDynBottcher c φ) {z : ℂ} (hz : z ∈ rayTube hN) :
    ∃ w : ℂ, Work.EL.F c w = z ∧ w ∈ rayTube hN ∧
      Work.GATE.deviation φ Work.EL.alpha1 w = Work.GATE.deviation φ Work.EL.alpha1 z / 1024 := by
  obtain ⟨θ, t, hθ1, hθ2, ht, rfl⟩ := hz
  set θ' : ℝ := (θ + 371) / 1024 with hθ'def
  set t' : ℝ := t ^ ((1024 : ℝ)⁻¹) with ht'def
  have ht' : 1 < t' := by
    rw [ht'def]; exact Real.one_lt_rpow ht (by norm_num)
  have hshift : (θ + 371) / 1024 - Work.EL.alpha1 = (θ - Work.EL.alpha1) / 1024 := by
    have h := alpha1_arith
    field_simp
    linarith
  have hθ'lo : Work.EL.alpha1 - 1 / 8 < θ' := by
    rw [hθ'def]
    have h3 : -1 / 8 < (θ - Work.EL.alpha1) / 1024 := by linarith
    linarith [hshift]
  have hθ'hi : θ' < Work.EL.alpha1 + 1 / 8 := by
    rw [hθ'def]
    have h3 : (θ - Work.EL.alpha1) / 1024 < 1 / 8 := by linarith
    linarith [hshift]
  have hF : Work.EL.F c (Work.EL.rayPt hN θ' t') = Work.EL.rayPt hN θ t := by
    rw [Work.ELRig.rayPt_iterate hN hB ht']
    have hT : Work.EL.T^[10] θ' = θ := by
      rw [hθ'def]; exact T_iterate_ten_window θ hθ1 hθ2
    have htpow : t' ^ (1024 : ℕ) = t := by
      rw [ht'def]; exact Real.rpow_inv_natCast_pow (by linarith) (by norm_num)
    rw [hT, htpow]
  refine ⟨Work.EL.rayPt hN θ' t', hF, ⟨θ', t', hθ'lo, hθ'hi, ht', rfl⟩, ?_⟩
  rw [deviation_rayPt hN ht' (by linarith [hθ'lo]) (by linarith [hθ'hi]),
      deviation_rayPt hN ht (by linarith [hθ1]) (by linarith [hθ2])]
  rw [hθ'def]
  have h := alpha1_arith
  field_simp
  linarith

/-- **The `α₁`-branch data of the second return map `F c = (T_c)^{10}` at a root-parabolic
parameter.**  The tube is `rayTube hN`, and the branch `Λ` is the Böttcher inverse branch of
direction `α₁` (`exists_rayTube_preimage`), chosen classically on the tube. -/
noncomputable def branchDataAlpha1 {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (hB : Work.ParamRays.IsDynBottcher c φ) : Work.GATE.BranchData φ Work.EL.alpha1 where
  F := Work.EL.F c
  Λ := fun z => if h : z ∈ rayTube hN then (exists_rayTube_preimage hN hB h).choose else 0
  S := rayTube hN
  hright := by
    intro z hz
    rw [dite_eq_left hz]
    exact (exists_rayTube_preimage hN hB hz).choose_spec.1
  hmem := by
    intro z hz
    rw [dite_eq_left hz]
    exact (exists_rayTube_preimage hN hB hz).choose_spec.2.1
  hS_dev := by
    intro z hz
    obtain ⟨θ, t, hθ1, hθ2, ht, rfl⟩ := hz
    rw [deviation_rayPt hN ht (by linarith [hθ1]) (by linarith [hθ2])]
    rw [abs_le]
    exact ⟨by linarith [hθ1], by linarith [hθ2]⟩
  hdev := by
    intro z hz
    rw [dite_eq_left hz]
    exact (exists_rayTube_preimage hN hB hz).choose_spec.2.2

/-- **The `α₁`-branch data of `Work.EL.RootParabolic`.**  A root-parabolic parameter carries the
`α₁`-Böttcher branch data of its second return map, with the whole `α₁`-window of ray points in
the tube of the branch. -/
theorem branchData_alpha1_of_rootParabolic {c : ℂ} (d : Work.EL.RootParabolic c) :
    ∃ bd : Work.GATE.BranchData d.φ Work.EL.alpha1, bd.F = Work.EL.F c ∧
      ∀ (θ t : ℝ), 1 < t → Work.EL.alpha1 - 1/8 < θ → θ < Work.EL.alpha1 + 1/8 →
        Work.EL.rayPt d.hN θ t ∈ bd.S := by
  refine ⟨branchDataAlpha1 d.hN d.bottcher, rfl, ?_⟩
  intro θ t ht h1 h2
  exact ⟨θ, t, h1, h2, ht, rfl⟩

end Work.GATE.Gate
