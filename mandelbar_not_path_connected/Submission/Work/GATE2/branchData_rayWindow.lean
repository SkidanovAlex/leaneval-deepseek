/-
# `Work.GATE2.branchData_rayWindow`: the `α`-branch data for the whole ray window

This file proves the residual requested by the TRANSPORT step of the GATE2 design
(`Submission/Work/GATE2/Defs.lean`): for **any** parameter `c` carrying the dynamical Böttcher
data `hN : Work.EL.DynB c φ` and a genuine Böttcher coordinate `hB : IsDynBottcher c φ`, and for
any angle `α` in the open middle range `(1/8, 1 - 1/8)` whose `1024`-fold image is `α` up to an
integer

    `1024 α = α + m`,   `m : ℤ`   (equivalently `1023 α = m`),

the second return map `F = (T_c)^{10} = Work.EL.F c` has an inverse branch on the tube of **all**
dynamical ray points of the window `(α - 1/8, α + 1/8)`, normalised at the direction `α`.

This is the generalisation of `Work.GATE.Gate.branchData_alpha1_of_rootParabolic` (the case
`α = α₁ = 371/1023`, `m = 371`) from the single root angle to an arbitrary lattice angle of the
`1023`-th lattice.  Nothing in that argument is special to `371`: the branch acts on the Böttcher
coordinate by

    `Λ (rayPt θ t) = rayPt ((θ + m)/1024) (t ^ (1/1024))`,

which fixes the direction `α` because `(α + m)/1024 = α` (this is `1024 α = α + m`), and the
window is invariant because `|(θ + m)/1024 - α| = |θ - α|/1024`.

The three ingredients are exactly those of the `α₁`-case, all of them already general in `α`:

* `Work.GATE.Gate.deviation_rayPt` (with `Work.GATE.Gate.liftAngle_rayPt`,
  `Work.GATE.Gate.bAngle_rayPt`): the `α`-relative deviation of a ray point of angle in the
  window is `θ - α`;
* `Work.ELNest.T_iterate_ten` + `Int.fract_add_intCast`: `T^[10] ((θ + m)/1024) = θ` on the
  window (here `m = 371` is replaced by the general integer, `T` is the angle-doubling map);
* `Work.ELRig.rayPt_iterate`: `F (rayPt θ t) = rayPt (T^[10] θ) (t ^ 1024)`.

The tube is then defined *by* the window (`rayTube`), and the branch is selected classically on
it, exactly as in the `α₁`-construction.
-/
import Mathlib
import Submission.Work.GATE2.Inputs

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

namespace Work.GATE2

/-! ## The angle arithmetic of the branch `ϑ ↦ (ϑ + m)/1024` -/

/-- **The tenth iterate of the angle-doubling map undoes the branch on the window.**  If
`θ ∈ (0, 1)` then `T^[10] ((θ + m)/1024) = θ`: the tenth iterate of `T` is the fractional part of
`1024 θ` (`Work.ELNest.T_iterate_ten`), and `1024·((θ + m)/1024) = θ + m` with `θ ∈ [0, 1)`, so
the fractional part is `θ` (`Int.fract_add_intCast`).  In the application `θ` lies in the window
`(α - 1/8, α + 1/8)` of an `α ∈ (1/8, 1 - 1/8)`, whence `0 < θ < 1`. -/
theorem T_iterate_ten_window (m : ℤ) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) :
    Work.EL.T^[10] ((θ + (m : ℝ)) / 1024) = θ := by
  rw [Work.ELNest.T_iterate_ten]
  have hmul : (1024 : ℝ) * ((θ + (m : ℝ)) / 1024) = θ + (m : ℝ) := by field_simp
  rw [hmul, Int.fract_add_intCast]
  exact Int.fract_eq_self.mpr ⟨h0, h1⟩

/-- The branch `ϑ ↦ (ϑ + m)/1024` fixes the direction `α` when `1024 α = α + m`: the arithmetic
identity `(θ + m)/1024 - α = (θ - α)/1024` behind both the invariance of the window and the
division of the deviation by `1024`. -/
theorem branch_shift {α : ℝ} {m : ℤ} (hm : 1024 * α = α + (m : ℝ)) (θ : ℝ) :
    (θ + (m : ℝ)) / 1024 - α = (θ - α) / 1024 := by
  field_simp
  linarith

/-! ## The `α`-tube of the dynamical plane -/

/-- **The `α`-tube**: the dynamical ray points whose angle lies in the open window
`(α - 1/8, α + 1/8)` and whose level is `> 1`.  This is the tube `S` of the branch data of
direction `α`: it is exactly the set of points that
`Work.GATE2.branchData_rayWindow` must produce as the tube. -/
def rayTube {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) (α : ℝ) : Set ℂ :=
  {z | ∃ θ t : ℝ, α - 1 / 8 < θ ∧ θ < α + 1 / 8 ∧ 1 < t ∧ z = Work.EL.rayPt hN θ t}

theorem mem_rayTube {c : ℂ} {φ : ℂ → ℂ} {hN : Work.EL.DynB c φ} {α : ℝ} {θ t : ℝ}
    (h1 : α - 1 / 8 < θ) (h2 : θ < α + 1 / 8) (ht : 1 < t) :
    Work.EL.rayPt hN θ t ∈ rayTube hN α :=
  ⟨θ, t, h1, h2, ht, rfl⟩

/-! ## The inverse branch on the tube -/

/-- **The inverse branch of the Böttcher coordinate on the `α`-tube.**  Every point of the tube
has a preimage under `F = (T_c)^{10}` which again lies in the tube, and whose `α`-relative
Böttcher deviation is that of the point divided by `1024`: with `z = rayPt θ t` one takes

    `w = rayPt ((θ + m)/1024) (t ^ (1/1024))`,

the level being taken to the `1024`-th root and the angle being pushed through the branch of the
`1024`-th root that fixes the direction `α`.  Then `F w = z` by
`Work.ELRig.rayPt_iterate` + `T_iterate_ten_window`, the window is preserved by `branch_shift`,
and the deviation is divided by `1024` by `Work.GATE.Gate.deviation_rayPt`. -/
theorem exists_rayTube_preimage {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (hB : Work.ParamRays.IsDynBottcher c φ) {α : ℝ} {m : ℤ}
    (hm : 1024 * α = α + (m : ℝ)) (hα0 : 1 / 8 < α) (hα1 : α < 1 - 1 / 8) {z : ℂ}
    (hz : z ∈ rayTube hN α) :
    ∃ w : ℂ, Work.EL.F c w = z ∧ w ∈ rayTube hN α ∧
      Work.GATE.deviation φ α w = Work.GATE.deviation φ α z / 1024 := by
  obtain ⟨θ, t, hθ1, hθ2, ht, rfl⟩ := hz
  set θ' : ℝ := (θ + (m : ℝ)) / 1024 with hθ'def
  set t' : ℝ := t ^ ((1024 : ℝ)⁻¹) with ht'def
  have ht' : 1 < t' := by
    rw [ht'def]; exact Real.one_lt_rpow ht (by norm_num)
  have hθ'lo : α - 1 / 8 < θ' := by
    rw [hθ'def]
    have h3 : -1 / 8 < (θ - α) / 1024 := by linarith
    linarith [branch_shift hm θ]
  have hθ'hi : θ' < α + 1 / 8 := by
    rw [hθ'def]
    have h3 : (θ - α) / 1024 < 1 / 8 := by linarith
    linarith [branch_shift hm θ]
  have hF : Work.EL.F c (Work.EL.rayPt hN θ' t') = Work.EL.rayPt hN θ t := by
    rw [Work.ELRig.rayPt_iterate hN hB ht']
    have hT : Work.EL.T^[10] θ' = θ := by
      rw [hθ'def]
      exact T_iterate_ten_window m (by linarith) (by linarith)
    have htpow : t' ^ (1024 : ℕ) = t := by
      rw [ht'def]; exact Real.rpow_inv_natCast_pow (by linarith) (by norm_num)
    rw [hT, htpow]
  have hdev : Work.GATE.deviation φ α (Work.EL.rayPt hN θ' t') =
      Work.GATE.deviation φ α (Work.EL.rayPt hN θ t) / 1024 := by
    rw [Work.GATE.Gate.deviation_rayPt hN ht' (by linarith) (by linarith),
      Work.GATE.Gate.deviation_rayPt hN ht (by linarith) (by linarith)]
    rw [hθ'def]
    exact branch_shift hm θ
  exact ⟨Work.EL.rayPt hN θ' t', hF, mem_rayTube hθ'lo hθ'hi ht', hdev⟩

/-! ## The branch data -/

/-- **The `α`-branch data of the second return map `F c = (T_c)^{10}`, with the whole ray window
in the tube.**  The tube is `rayTube hN α` and the branch `Λ` is the Böttcher inverse branch of
direction `α` (`exists_rayTube_preimage`), chosen classically on the tube: on a tube point
`z = rayPt θ t` it is `rayPt ((θ + m)/1024) (t ^ (1/1024))`. -/
noncomputable def branchDataOfWindow {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (hB : Work.ParamRays.IsDynBottcher c φ) (α : ℝ) (m : ℤ)
    (hm : 1024 * α = α + (m : ℝ)) (hα0 : 1 / 8 < α) (hα1 : α < 1 - 1 / 8) :
    Work.GATE.BranchData φ α where
  F := Work.EL.F c
  Λ := fun z => if h : z ∈ rayTube hN α then
      (exists_rayTube_preimage hN hB hm hα0 hα1 h).choose else 0
  S := rayTube hN α
  hright := by
    intro z hz
    rw [dite_eq_left hz]
    exact (exists_rayTube_preimage hN hB hm hα0 hα1 hz).choose_spec.1
  hmem := by
    intro z hz
    rw [dite_eq_left hz]
    exact (exists_rayTube_preimage hN hB hm hα0 hα1 hz).choose_spec.2.1
  hS_dev := by
    intro z hz
    obtain ⟨θ, t, hθ1, hθ2, ht, rfl⟩ := hz
    rw [Work.GATE.Gate.deviation_rayPt hN ht (by linarith) (by linarith)]
    rw [abs_le]
    exact ⟨by linarith, by linarith⟩
  hdev := by
    intro z hz
    rw [dite_eq_left hz]
    exact (exists_rayTube_preimage hN hB hm hα0 hα1 hz).choose_spec.2.2

/-! ## The requested lemma -/

/-- **The `α`-ray-window branch data of the second return map**: for any parameter carrying the
dynamical Böttcher data and any angle `α ∈ (1/8, 1 - 1/8)` with `1024 α = α + m` (`m : ℤ`) there
is `α`-branch data for `F = Work.EL.F c` whose tube contains *all* the dynamical ray points of
the window `(α - 1/8, α + 1/8)`. -/
theorem branchData_rayWindow {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (hB : Work.ParamRays.IsDynBottcher c φ) (α : ℝ) (m : ℤ)
    (hm : 1024 * α = α + (m : ℝ)) (hα0 : 1 / 8 < α) (hα1 : α < 1 - 1 / 8) :
    ∃ bd : Work.GATE.BranchData φ α, bd.F = Work.EL.F c ∧
      ∀ (θ t : ℝ), 1 < t → α - 1 / 8 < θ → θ < α + 1 / 8 →
        Work.EL.rayPt hN θ t ∈ bd.S := by
  refine ⟨branchDataOfWindow hN hB α m hm hα0 hα1, rfl, ?_⟩
  intro θ t ht h1 h2
  exact mem_rayTube h1 h2 ht

end Work.GATE2
