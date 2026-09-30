import Mathlib
import Submission.Work.Thom.Continuous
import Submission.Work.Thom.Pair

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

/-!
# Geometry of the trivial real line bundle

This module collects the geometric input needed for the Thom isomorphism of the trivial real line
bundle `B × ℝ → B` (equivalently: the suspension isomorphism, or the Thom isomorphism for a real
line bundle): the maps into the total space that express the two ends of the fibre, and the
homotopies between them and the identity.

* `Work.Thom.continuous_add_section` — the **fibrewise sum** of two continuous maps into the total
  space over the same base point is continuous — the counterpart of
  `Work.Thom.continuous_smul_section` for addition;
* `Work.Thom.continuous_affine_section` — an affine combination `a • v + (1-a) • σ` of a constant
  family and a section is continuous;
* `Work.Thom.secConst` — the constant section `x ↦ ⟨x,c⟩` of the trivial line bundle;
* `Work.Thom.affineHom` — the affine homotopy `(t,p) ↦ ⟨p.1, (1-t)·c + t·p.2⟩`.
-/

open Work.TangentClasses

namespace Work.Thom

open Bundle Filter

open scoped Topology

noncomputable section

variable {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {ι : Type}

/-! ## The fibrewise sum of two sections -/

/-- **The fibrewise sum of two continuous maps into the total space over the same base point is
continuous.**  This is the counterpart of `Work.Thom.continuous_smul_section` for addition. -/
theorem continuous_add_section {Y : Type} [TopologicalSpace Y] (Z : RealBundle B F ι)
    (σ : C(Y, Z.TotalSpace)) (τ : C(Y, Z.TotalSpace)) (h : ∀ y, (σ y).1 = (τ y).1) :
    Continuous (fun y =>
      (⟨(σ y).1, (show F from (σ y).2) + (show F from (τ y).2)⟩ : Z.TotalSpace)) := by
  rw [continuous_iff_continuousAt]
  intro y₀
  set i := Z.indexAt (σ y₀).1 with hi
  have hy0 : (σ y₀).1 ∈ Z.baseSet i := by rw [hi]; exact Z.mem_baseSet_at (σ y₀).1
  have hσ : ContinuousAt (fun y => ((Z.localTriv i) (σ y)).2) y₀ :=
    continuousAt_localTrivAt_snd Z σ y₀
  have hτ : ContinuousAt (fun y => ((Z.localTriv i) (τ y)).2) y₀ := by
    have h1 := continuousAt_localTrivAt_snd Z τ y₀
    rw [show (τ y₀).1 = (σ y₀).1 from (h y₀).symm] at h1
    exact h1
  have hpair : ContinuousAt (fun y => ((σ y).1,
      (show F from ((Z.localTriv i) (σ y)).2) + (show F from ((Z.localTriv i) (τ y)).2))) y₀ :=
    (Z.continuous_proj.continuousAt.comp σ.continuous.continuousAt).prodMk (hσ.add hτ)
  have heq : (fun y => (Z.localTriv i)
        (⟨(σ y).1, (show F from (σ y).2) + (show F from (τ y).2)⟩ : Z.TotalSpace)) =
      fun y => ((σ y).1,
        (show F from ((Z.localTriv i) (σ y)).2) + (show F from ((Z.localTriv i) (τ y)).2)) := by
    funext y
    simp only [VectorBundleCore.localTriv_apply]
    rw [h y, map_add]
  refine (Z.localTriv i).continuousAt_of_comp_left ?_ hy0 ?_
  · show ContinuousAt (fun y => Z.proj
        (⟨(σ y).1, (show F from (σ y).2) + (show F from (τ y).2)⟩ : Z.TotalSpace)) y₀
    rw [show (fun y => Z.proj
        (⟨(σ y).1, (show F from (σ y).2) + (show F from (τ y).2)⟩ : Z.TotalSpace))
        = fun y => (σ y).1 from by funext y; rfl]
    exact Z.continuous_proj.continuousAt.comp σ.continuous.continuousAt
  · show ContinuousAt (fun y => (Z.localTriv i)
        (⟨(σ y).1, (show F from (σ y).2) + (show F from (τ y).2)⟩ : Z.TotalSpace)) y₀
    rw [heq]
    exact hpair

/-- **An affine combination of a constant family and a section is continuous.**  If `v : F` is a
vector fixed by the transition functions over the base points of `σ`, and `a : Y → ℝ` is
continuous, then `y ↦ ⟨(σ y).1, (1 - a y) • v + a y • (σ y).2⟩` is continuous. -/
theorem continuous_affine_section {Y : Type} [TopologicalSpace Y] (Z : RealBundle B F ι)
    (σ : C(Y, Z.TotalSpace)) (v : F) (a : C(Y, ℝ))
    (hv : ∀ y i j, (σ y).1 ∈ Z.baseSet i ∩ Z.baseSet j → Z.coordChange i j (σ y).1 v = v) :
    Continuous (fun y => (⟨(σ y).1,
      (show F from (1 - a y) • v + a y • (show F from (σ y).2))⟩ : Z.TotalSpace)) := by
  have h₁ : Continuous (fun y => (⟨(σ y).1, (1 - a y) • v⟩ : Z.TotalSpace)) :=
    continuous_section_mk Z ⟨fun y => (σ y).1, by exact Z.continuous_proj.comp σ.continuous⟩
      ⟨fun y => (1 - a y) • v, (continuous_const.sub a.continuous).smul continuous_const⟩
      (by intro y i j hy
          show Z.coordChange i j (σ y).1 ((1 - a y) • v) = (1 - a y) • v
          rw [map_smul, hv y i j hy])
  have h₂ : Continuous (fun y => (⟨(σ y).1, a y • (show F from (σ y).2)⟩ : Z.TotalSpace)) :=
    continuous_smul_section Z σ a
  exact (continuous_add_section Z
    ⟨fun y => (⟨(σ y).1, (1 - a y) • v⟩ : Z.TotalSpace), h₁⟩
    ⟨fun y => (⟨(σ y).1, a y • (show F from (σ y).2)⟩ : Z.TotalSpace), h₂⟩
    (fun y => rfl)).congr (by intro y; rfl)

/-! ## The trivial line bundle -/

section Triv

variable {ι₀ : Type} [Inhabited ι₀]

/-- A vector of the model fibre `ℝ` is fixed by every transition function of the trivial bundle. -/
theorem trivial_coordChange_apply (c : ℝ) (p : (RealBundle.trivial B ℝ ι₀).TotalSpace) (i j : ι₀) :
    (RealBundle.trivial B ℝ ι₀).coordChange i j p.1 c = c := rfl

/-- **The constant section** `x ↦ ⟨x,c⟩` of the trivial line bundle, as a map into its total
space. -/
def secConst (c : ℝ) : C((RealBundle.trivial B ℝ ι₀).TotalSpace,
    (RealBundle.trivial B ℝ ι₀).TotalSpace) :=
  ⟨fun p : (RealBundle.trivial B ℝ ι₀).TotalSpace =>
      (⟨p.1, (show (RealBundle.trivial B ℝ ι₀).Fiber p.1 from c)⟩ :
        (RealBundle.trivial B ℝ ι₀).TotalSpace),
    by
      refine continuous_section_mk (X := (RealBundle.trivial B ℝ ι₀).TotalSpace)
        (RealBundle.trivial B ℝ ι₀)
        ⟨fun p : (RealBundle.trivial B ℝ ι₀).TotalSpace => p.1,
          by exact (RealBundle.trivial B ℝ ι₀).continuous_proj⟩
        ⟨fun _ => c, continuous_const⟩ ?_
      intro y i j hy
      exact trivial_coordChange_apply c y i j⟩

@[simp] theorem secConst_apply (c : ℝ) (p : (RealBundle.trivial B ℝ ι₀).TotalSpace) :
    secConst (B := B) (ι₀ := ι₀) c p =
      (⟨p.1, (show (RealBundle.trivial B ℝ ι₀).Fiber p.1 from c)⟩ :
        (RealBundle.trivial B ℝ ι₀).TotalSpace) := rfl

/-- **The affine homotopy** `(t,p) ↦ ⟨p.1, (1-t)·c + t·p.2⟩` from the constant section `x ↦ ⟨x,c⟩`
to the identity of the total space of the trivial line bundle. -/
def affineHom (c : ℝ) :
    C(unitInterval × (RealBundle.trivial B ℝ ι₀).TotalSpace,
      (RealBundle.trivial B ℝ ι₀).TotalSpace) :=
  ⟨fun sp : unitInterval × (RealBundle.trivial B ℝ ι₀).TotalSpace =>
      (⟨(sp.2).1, ((1 - (sp.1 : unitInterval)) : ℝ) • (show ℝ from c) +
        (sp.1 : ℝ) • (show ℝ from (sp.2).2)⟩ : (RealBundle.trivial B ℝ ι₀).TotalSpace),
    continuous_affine_section (RealBundle.trivial B ℝ ι₀)
      ((ContinuousMap.id ((RealBundle.trivial B ℝ ι₀).TotalSpace)).comp
        ⟨Prod.snd, continuous_snd⟩) c
      ⟨fun sp : unitInterval × (RealBundle.trivial B ℝ ι₀).TotalSpace => (sp.1 : ℝ),
        continuous_subtype_val.comp continuous_fst⟩
      (by intro y i j hy; exact trivial_coordChange_apply c y.2 i j)⟩

@[simp] theorem affineHom_apply (c : ℝ)
    (sp : unitInterval × (RealBundle.trivial B ℝ ι₀).TotalSpace) :
    affineHom (B := B) (ι₀ := ι₀) c sp =
      (⟨(sp.2).1, ((1 - (sp.1 : unitInterval)) : ℝ) • (show ℝ from c) +
        (sp.1 : ℝ) • (show ℝ from (sp.2).2)⟩ : (RealBundle.trivial B ℝ ι₀).TotalSpace) := rfl

/-- The affine homotopy at time `0` is the constant section. -/
theorem affineHom_zero (c : ℝ) (p : (RealBundle.trivial B ℝ ι₀).TotalSpace) :
    affineHom (B := B) (ι₀ := ι₀) c (0, p) = secConst (B := B) (ι₀ := ι₀) c p := by
  rw [affineHom_apply, secConst_apply]
  norm_num

/-- The affine homotopy at time `1` is the identity. -/
theorem affineHom_one (c : ℝ) (p : (RealBundle.trivial B ℝ ι₀).TotalSpace) :
    affineHom (B := B) (ι₀ := ι₀) c (1, p) = p := by
  rw [affineHom_apply]
  norm_num

end Triv

end

end Work.Thom
