import Mathlib
import Submission.Work.Thom.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-!
# Continuity of sections of a real vector bundle, and of fibrewise rescalings

The Euler class of a bundle is the pullback of the Thom class of the pair `(E,E∖0)` along the zero
section, and the classical fact that *a bundle with a nowhere-zero section has vanishing Euler
class* is proved by exhibiting a homotopy between the zero section and the nowhere-zero section,
namely the fibrewise rescaling `(x,t) ↦ ⟨x, t • σ x⟩`.

To make that argument run in the workspace's model — gluing data `VectorBundleCore ℝ B F ι` — we
need the continuity of two kinds of maps into the total space:

* `Work.Thom.continuous_section_mk` — a *constant-family* section: if `b : X → B` and `g : X → F`
  are continuous and the fibre vector `g x` is fixed by every transition function over `b x`, then
  `x ↦ ⟨b x, g x⟩` is continuous.  (This is the "invariant vector" situation; it gives in particular
  the nowhere-zero section `x ↦ ⟨x,(0,1)⟩` of `E ⊕ ε¹`.)
* `Work.Thom.continuous_smul_section` — fibrewise rescaling: if `σ : X → E` is continuous and
  `c : X → ℝ` is continuous, then `x ↦ ⟨(σ x).1, c x • (σ x).2⟩` is continuous.  This is the
  homotopy of the vanishing theorem.

Both are proved by checking continuity in the *fixed* trivialisation at the base point,
`(Z.localTriv (Z.indexAt b₀))` (`Bundle.Trivialization.continuousAt_of_comp_left`); the transition
functions enter only through `FiberBundle.continuousAt_totalSpace`, i.e. through the continuity of
the given section.  (The preferred trivialisation `localTrivAt` at a base point is *not* a
continuous function of the base point, which is why the argument must go through `continuousAt` at
each point rather than through a single global trivialisation.)
-/

open Work.TangentClasses

namespace Work.Thom

open Bundle Filter

open scoped Topology

noncomputable section

variable {B : Type*} [TopologicalSpace B] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {ι : Type*}

/-- The coordinate of a continuous map into the total space of a bundle, read in the preferred
trivialisation at its base point `σ x₀`, is continuous at `x₀`.  This is
`FiberBundle.continuousAt_totalSpace` with the identification
`trivializationAt F Z.Fiber b = Z.localTrivAt b`. -/
theorem continuousAt_localTrivAt_snd {X : Type} [TopologicalSpace X] (Z : RealBundle B F ι)
    (σ : C(X, Z.TotalSpace)) (x₀ : X) :
    ContinuousAt (fun x => ((Z.localTrivAt (σ x₀).1) (σ x)).2) x₀ := by
  have h := ((FiberBundle.continuousAt_totalSpace F σ (x₀ := x₀)).1
    σ.continuous.continuousAt).2
  simpa only [VectorBundleCore.trivializationAt, VectorBundleCore.proj] using h

/-- **The continuity of a constant-family section.**  If `b : X → B` is continuous and `g : X → F`
takes values in the subspace of `F` fixed by every transition function over `b x`, then
`x ↦ ⟨b x, g x⟩` is a continuous section of the bundle. -/
theorem continuous_section_mk {X : Type} [TopologicalSpace X] (Z : RealBundle B F ι)
    (b : C(X, B)) (g : C(X, F))
    (h : ∀ x i j, b x ∈ Z.baseSet i ∩ Z.baseSet j → Z.coordChange i j (b x) (g x) = g x) :
    Continuous (fun x => (⟨b x, g x⟩ : Z.TotalSpace)) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  set i := Z.indexAt (b x₀) with hi
  have hx0 : b x₀ ∈ Z.baseSet i := by rw [hi]; exact Z.mem_baseSet_at (b x₀)
  have hU : ∀ᶠ x in 𝓝 x₀, b x ∈ Z.baseSet i :=
    b.continuous.continuousAt.preimage_mem_nhds ((Z.isOpen_baseSet i).mem_nhds hx0)
  have hθ : ContinuousAt (fun x => (b x, g x)) x₀ :=
    b.continuous.continuousAt.prodMk g.continuous.continuousAt
  have hev : (fun x => (Z.localTriv i) (⟨b x, g x⟩ : Z.TotalSpace)) =ᶠ[𝓝 x₀]
      (fun x => (b x, g x)) := by
    filter_upwards [hU] with x hx
    rw [VectorBundleCore.localTriv_apply]
    exact Prod.ext rfl (h x (Z.indexAt (b x)) i ⟨Z.mem_baseSet_at (b x), hx⟩)
  refine (Z.localTriv i).continuousAt_of_comp_left ?_ hx0 ?_
  · show ContinuousAt (fun x => Z.proj (⟨b x, g x⟩ : Z.TotalSpace)) x₀
    rw [show (fun x => Z.proj (⟨b x, g x⟩ : Z.TotalSpace)) = fun x => b x from by funext x; rfl]
    exact b.continuous.continuousAt
  · show ContinuousAt (fun x => (Z.localTriv i) (⟨b x, g x⟩ : Z.TotalSpace)) x₀
    exact hθ.congr hev.symm

/-- **Fibrewise rescaling of a continuous map into the total space.**  If `σ : X → E` is continuous
and `c : X → ℝ` is continuous, then `x ↦ ⟨(σ x).1, c x • (σ x).2⟩` is continuous.  Applying this to
a *constant* family in the second variable gives the homotopy between the zero section and a
nowhere-zero section (`Submission/Work/Thom/Euler.lean`). -/
theorem continuous_smul_section {X : Type} [TopologicalSpace X] (Z : RealBundle B F ι)
    (σ : C(X, Z.TotalSpace)) (c : C(X, ℝ)) :
    Continuous (fun x => (⟨(σ x).1, c x • (σ x).2⟩ : Z.TotalSpace)) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  set i := Z.indexAt (σ x₀).1 with hi
  have hx0 : (σ x₀).1 ∈ Z.baseSet i := by rw [hi]; exact Z.mem_baseSet_at (σ x₀).1
  have hσ : ContinuousAt (fun x => ((Z.localTriv i) (σ x)).2) x₀ :=
    continuousAt_localTrivAt_snd Z σ x₀
  have hpair : ContinuousAt (fun x => ((σ x).1, c x • ((Z.localTriv i) (σ x)).2)) x₀ :=
    (Z.continuous_proj.continuousAt.comp σ.continuous.continuousAt).prodMk
      (c.continuous.continuousAt.smul hσ)
  have heq : (fun x => (Z.localTriv i) (⟨(σ x).1, c x • (σ x).2⟩ : Z.TotalSpace)) =
      fun x => ((σ x).1, c x • ((Z.localTriv i) (σ x)).2) := by
    funext x
    rw [VectorBundleCore.localTriv_apply, ContinuousLinearMap.map_smul,
      VectorBundleCore.localTriv_apply]
  refine (Z.localTriv i).continuousAt_of_comp_left ?_ hx0 ?_
  · show ContinuousAt (fun x => Z.proj (⟨(σ x).1, c x • (σ x).2⟩ : Z.TotalSpace)) x₀
    rw [show (fun x => Z.proj (⟨(σ x).1, c x • (σ x).2⟩ : Z.TotalSpace)) = fun x => (σ x).1
      from by funext x; rfl]
    exact Z.continuous_proj.continuousAt.comp σ.continuous.continuousAt
  · show ContinuousAt (fun x => (Z.localTriv i) (⟨(σ x).1, c x • (σ x).2⟩ : Z.TotalSpace)) x₀
    rw [heq]
    exact hpair

end

end Work.Thom
