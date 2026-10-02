import Mathlib
import Submission.Work.PTGeometric.SourceRegionSetupBasic
import Submission.Work.PTGeometric.WeakRegion.Setup

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter ModelWithCorners

namespace Work.PTGeometric

noncomputable section

/-!
# The straightening chart of a region: basic model-space lemmas

This file collects the model-space (`Mod k`) analysis used to build the straightening chart
`w ↦ strAux ψ (φ w.1).1` of the region `{Φ ≤ 0}` of a weak region setup.

* `strAux_eq`, `unstrAux_eq`: the straightening maps are the explicit affine maps
  `z ↦ z ∓ ψ (tail z) • e 0`;
* `satSet V`: the `eZero`-saturation of `V` (the union of the translates `V - s • e 0`);
* `contDiffAt_psi_tailVec_of_mem`, `contDiffAt_psi_tailVec_of_satSet`: `z ↦ ψ (tail z)` is
  smooth at `tailVec z` for `z ∈ V`, and at every point of `satSet V`.
-/

variable {k : ℕ}

theorem strAux_eq (ψ : Mod k → ℝ) (z : Mod k) : strAux ψ z = z - ψ (tailVec z) • eZero := by
  show consVec (z.ofLp 0 - ψ (tailVec z)) (tailVec z) = z - ψ (tailVec z) • eZero
  rw [consVec, tailVec]
  module

theorem unstrAux_eq (ψ : Mod k → ℝ) (z : Mod k) : unstrAux ψ z = z + ψ (tailVec z) • eZero := by
  show consVec (z.ofLp 0 + ψ (tailVec z)) (tailVec z) = z + ψ (tailVec z) • eZero
  rw [consVec, tailVec]
  module

/-- The `eZero`-saturation of a set `V` of the model space. -/
def satSet (V : Set (Mod k)) : Set (Mod k) := ⋃ s : ℝ, (fun z : Mod k => z - s • eZero) '' V

theorem tailVec_self (z : Mod k) : tailVec (tailVec z) = tailVec z := by
  rw [tailVec, tailVec_apply_zero, zero_smul, sub_zero]

theorem sub_tailVec (z : Mod k) : z - tailVec z = z.ofLp 0 • eZero := by
  show z - (z - z.ofLp 0 • eZero) = z.ofLp 0 • eZero
  abel

theorem tailVec_smul_eZero (c : ℝ) : tailVec (c • eZero : Mod k) = 0 := by
  rw [tailVec, PiLp.smul_apply, eZero_apply, smul_eq_mul, mul_one, sub_self]

theorem tailVec_add_smul_eZero (v : Mod k) (c : ℝ) : tailVec (v + c • eZero) = tailVec v := by
  rw [tailVec_add, tailVec_smul_eZero, add_zero]

theorem mem_satSet_iff {V : Set (Mod k)} {w : Mod k} :
    w ∈ satSet V ↔ ∃ z ∈ V, tailVec z = tailVec w := by
  rw [satSet, mem_iUnion]
  constructor
  · rintro ⟨s, z, hz, rfl⟩
    exact ⟨z, hz, by rw [tailVec_sub_smul_eZero]⟩
  · rintro ⟨z, hz, hzw⟩
    refine ⟨z.ofLp 0 - w.ofLp 0, z, hz, ?_⟩
    have h1 : z - z.ofLp 0 • eZero = w - w.ofLp 0 • eZero := hzw
    have key : z - (z.ofLp 0 - w.ofLp 0) • eZero
        = (z - z.ofLp 0 • eZero) + w.ofLp 0 • eZero := by module
    show z - (z.ofLp 0 - w.ofLp 0) • eZero = w
    rw [key, h1]
    abel

theorem subset_satSet (V : Set (Mod k)) : V ⊆ satSet V := by
  intro w hw
  rw [mem_satSet_iff]
  exact ⟨w, hw, rfl⟩

theorem isOpen_satSet {V : Set (Mod k)} (hV : IsOpen V) : IsOpen (satSet V) := by
  rw [satSet]
  refine isOpen_iUnion fun s => ?_
  have h : (fun z : Mod k => z - s • eZero) '' V = (fun z : Mod k => z + s • eZero) ⁻¹' V := by
    ext w
    simp only [mem_image, mem_preimage]
    constructor
    · rintro ⟨z, hz, rfl⟩
      rwa [sub_add_cancel]
    · intro hw
      exact ⟨w + s • eZero, hw, by abel⟩
  rw [h]
  exact hV.preimage (by fun_prop)

/-- `z ↦ ψ (tailVec z)` is smooth at `tailVec z` for `z ∈ V`, when it is smooth on the open `V`. -/
theorem contDiffAt_psi_tailVec_of_mem {ψ : Mod k → ℝ} {V : Set (Mod k)} (hV : IsOpen V)
    (hψ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : Mod k => ψ (tailVec z)) V)
    {z : Mod k} (hz : z ∈ V) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u : Mod k => ψ (tailVec u)) (tailVec z) := by
  set F : Mod k → Mod k := fun v => v + (z - tailVec z) with hF
  have hFz : F (tailVec z) = z := by
    show tailVec z + (z - tailVec z) = z
    abel
  have hFsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F (F ⁻¹' V) := by
    show ContDiffOn ℝ _ (fun v : Mod k => v + (z - tailVec z)) (F ⁻¹' V)
    exact (contDiff_id.add contDiff_const).contDiffOn
  have hcomp : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun v : Mod k => ψ (tailVec (F v))) (F ⁻¹' V) := by
    have := hψ.comp hFsm (fun v hv => hv)
    exact this
  have hFopen : IsOpen (F ⁻¹' V) := hV.preimage (by rw [hF]; fun_prop)
  have hFmem : tailVec z ∈ F ⁻¹' V := by
    rw [mem_preimage, hFz]; exact hz
  have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun v : Mod k => ψ (tailVec (F v))) (tailVec z) :=
    hcomp.contDiffAt (hFopen.mem_nhds hFmem)
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards with v
  show ψ (tailVec v) = ψ (tailVec (F v))
  rw [hF, sub_tailVec, tailVec_add_smul_eZero]

theorem contDiffAt_psi_tailVec_of_satSet {ψ : Mod k → ℝ} {V : Set (Mod k)} (hV : IsOpen V)
    (hψ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : Mod k => ψ (tailVec z)) V)
    {u : Mod k} (hu : u ∈ satSet V) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : Mod k => ψ (tailVec z)) u := by
  obtain ⟨z, hz, hzu⟩ := mem_satSet_iff.1 hu
  set H : Mod k → Mod k := fun v => v - u.ofLp 0 • eZero with hH
  have hHu : H u = tailVec z := by
    have h1 : H u = tailVec u := rfl
    rw [h1, hzu]
  have hbase : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun v : Mod k => ψ (tailVec v)) (H u) := by
    rw [hHu]
    exact contDiffAt_psi_tailVec_of_mem hV hψ hz
  have hHsm : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) H u := by
    show ContDiffAt ℝ _ (fun v : Mod k => v - u.ofLp 0 • eZero) u
    fun_prop
  have hcomp := ContDiffAt.comp (u : Mod k) hbase hHsm
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards with v
  rw [Function.comp_apply]
  show ψ (tailVec v) = ψ (tailVec (H v))
  rw [hH, tailVec_sub_smul_eZero]

theorem contDiffOn_psi_tailVec_satSet {ψ : Mod k → ℝ} {V : Set (Mod k)} (hV : IsOpen V)
    (hψ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : Mod k => ψ (tailVec z)) V) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : Mod k => ψ (tailVec z)) (satSet V) :=
  fun u hu => (contDiffAt_psi_tailVec_of_satSet hV hψ hu).contDiffWithinAt

theorem contDiffOn_strAux_satSet {ψ : Mod k → ℝ} {V : Set (Mod k)} (hV : IsOpen V)
    (hψ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : Mod k => ψ (tailVec z)) V) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : Mod k => strAux ψ z) (satSet V) := by
  have h1 := contDiffOn_psi_tailVec_satSet hV hψ
  have h2 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : Mod k => ψ (tailVec z) • (eZero : Mod k)) (satSet V) :=
    h1.smul_const _
  refine (contDiffOn_id.sub h2).congr fun z _ => ?_
  rw [strAux_eq]
  rfl

theorem contDiffOn_unstrAux_satSet {ψ : Mod k → ℝ} {V : Set (Mod k)} (hV : IsOpen V)
    (hψ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : Mod k => ψ (tailVec z)) V) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : Mod k => unstrAux ψ z) (satSet V) := by
  have h1 := contDiffOn_psi_tailVec_satSet hV hψ
  have h2 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : Mod k => ψ (tailVec z) • (eZero : Mod k)) (satSet V) :=
    h1.smul_const _
  refine (contDiffOn_id.add h2).congr fun z _ => ?_
  rw [unstrAux_eq]
  rfl

end

end Work.PTGeometric
