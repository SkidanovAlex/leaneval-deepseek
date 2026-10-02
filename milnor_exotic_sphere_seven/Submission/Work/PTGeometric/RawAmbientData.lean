import Mathlib
import Submission.Work.PTGeometric.ContinuousDataOfRaw

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# PTGEOMETRIC: the raw ambient data of the source construction, as one structure

`Work.PTGeometric.continuousAmbientData_of_rawData` produces the `ContinuousAmbientData` of the last
mile from the *raw* ambient data of the source construction.  This file bundles those raw data as a
single structure so that the geometric producer can be stated (and delegated) as

  `[the defining function of the source region] + [the region-charting theorem] ⟹ RawAmbientData`.

The wrapper `Work.PTGeometric.continuousAmbientData_of_rawAmbientData` then feeds it to
`continuousAmbientData_of_rawData`.

## Main definitions and results

* `Work.PTGeometric.RawAmbientData`
* `Work.PTGeometric.continuousAmbientData_of_rawAmbientData`
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter

namespace Work.PTGeometric

noncomputable section

open Work.ThomBordism

variable {n k : ℕ} {ι : Type} [Fintype ι] {Fam : ι → Man8}

/-- **The raw ambient data of the source construction**: the compact source `M` with the ambient
coordinates `(P, v)` of the null-homotopy, the flat homotopy being `C^∞` only on a collar `V` of the
collapse end, and the prescribed boundary charts at the pieces. -/
structure RawAmbientData (n k : ℕ) (ι : Type) [Fintype ι] (Fam : ι → Man8) where
  M : Type
  [topologicalSpace : TopologicalSpace M]
  [chartedSpace : ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) M]
  [isManifold : IsManifold (𝓡∂ ((8 + k) + 1)) ∞ M]
  [compactSpace : CompactSpace M]
  [t2Space : T2Space M]
  [nonempty : Nonempty M]
  P : M → EndOp n
  v : M → Amb n
  hPc : Continuous P
  hvc : Continuous v
  hProj : ∀ x : M, P x ∈ Gr n k
  hMem : ∀ x : M, P x (v x) = v x
  V : Set M
  hVopen : IsOpen V
  S0 : Set M
  hS0cl : IsClosed S0
  hS0V : S0 ⊆ V
  hPsmV : ContMDiffOn (𝓡∂ ((8 + k) + 1)) (𝓘(ℝ, EndOp n)) ∞ P V
  hvsmV : ContMDiffOn (𝓡∂ ((8 + k) + 1)) (𝓘(ℝ, Amb n)) ∞ v V
  S : Set M
  hScl : IsClosed S
  hSsub : S ⊆ (𝓡∂ ((8 + k) + 1)).boundary M
  hSS0 : S ⊆ S0
  hend : ↥(S ∩ {x : M | v x = 0}) ≃ₜ (Σ i : ι, (Fam i).pt)
  hzero_sub : ∀ x ∈ (𝓡∂ ((8 + k) + 1)).boundary M, v x = 0 → x ∈ S
  δ : ℝ
  hδpos : 0 < δ
  hδ : ∀ x ∈ (𝓡∂ ((8 + k) + 1)).boundary M, x ∉ S0 → δ ≤ ‖v x‖
  mE : ℕ
  ellE : Fin mE → Amb n →L[ℝ] Amb k
  UE : Fin mE → Set M
  isOpen_UE : ∀ j, IsOpen (UE j)
  UE_int : ∀ j, UE j ⊆ interior S0
  ellE_inj : ∀ j y, y ∈ UE j → ∀ z : Amb n, P y z = z → ellE j z = 0 → z = 0
  ellE_inj_cl : ∀ j, closure (UE j) ⊆
    {y : M | ∀ z : Amb n, P y z = z → ellE j z = 0 → z = 0}
  bndZero_cov : ∀ x ∈ (𝓡∂ ((8 + k) + 1)).boundary M, v x = 0 → ∃ j, x ∈ UE j
  bndZero_trans : ∀ j, ∀ x ∈ UE j, ∀ (hx : x ∈ (𝓡∂ ((8 + k) + 1)).boundary M), v x = 0 →
    IsSubmersionAt (𝓡∂ ((8 + k) + 1)) (𝓡 k) ∞ (fun y : M => ellE j (v y)) x ∧
    IsSubmersionAt (𝓡 (8 + k)) (𝓡 k) ∞
      (fun y : ↥((𝓡∂ ((8 + k) + 1)).boundary M) => ellE j (v y)) ⟨x, hx⟩

attribute [instance] RawAmbientData.topologicalSpace RawAmbientData.chartedSpace
  RawAmbientData.isManifold RawAmbientData.compactSpace RawAmbientData.t2Space
  RawAmbientData.nonempty

/-- **The raw ambient data give the `ContinuousAmbientData` of the last mile**, as a `def`: the
`M`-field of the result is *definitionally* `D.M` (and similarly for the other fields), so that
statements about the produced ambient data can name its components (`NOTE_OMEGA.md` §7, §9). -/
noncomputable def continuousAmbientDataOf (hk : k ≤ n) (hk0 : 0 < k)
    (D : RawAmbientData n k ι Fam) : ContinuousAmbientData n k ι Fam :=
  continuousAmbientData_of_rawData D.M D.P D.v D.hPc D.hvc D.hProj D.hMem D.V D.hVopen
    D.S0 D.hS0cl D.hS0V D.hPsmV D.hvsmV D.S D.hScl D.hSsub D.hSS0 D.hend D.hzero_sub
    D.δ D.hδpos D.hδ D.mE D.ellE D.UE D.isOpen_UE D.UE_int
    D.ellE_inj D.ellE_inj_cl D.bndZero_cov D.bndZero_trans hk hk0

/-- **The raw ambient data give the `ContinuousAmbientData` of the last mile** (the `Nonempty` form,
kept for the existing consumers). -/
theorem continuousAmbientData_of_rawAmbientData (hk : k ≤ n) (hk0 : 0 < k)
    (D : RawAmbientData n k ι Fam) :
    Nonempty (ContinuousAmbientData n k ι Fam) :=
  ⟨continuousAmbientDataOf hk hk0 D⟩

end

end Work.PTGeometric
