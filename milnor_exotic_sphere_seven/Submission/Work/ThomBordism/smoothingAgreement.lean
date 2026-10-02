import Submission.Work.PTGeometric.RawAmbientData
import Submission.Work.ThomBordism.ambientPerturbBoundary

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

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

/-- **The smoothing step of the source construction does not change the field on the collar `S0`.**

`Work.PTGeometric.continuousAmbientDataOf` replaces the raw field `D.v` by its `C^∞` smoothing
`Work.PTGeometric.smoothMap_into_tautTotal_eqOn_close`, which is constructed to agree with `D.v` on the
closed collar `D.S0` of the raw data.  The boundary part of the level set `{v = 0}` lies in
`D.S0` (it is the collapse end `{x | x.1.1 0 = 0}`), which is why this agreement is what makes the
level set of the produced data identifiable with the raw one near its boundary. -/
theorem continuousAmbientDataOf_v_eqOn_S0 {n k : ℕ} {ι : Type} [Fintype ι] {Fam : ι → Man8}
    (hk : k ≤ n) (hk0 : 0 < k) (D : RawAmbientData n k ι Fam) :
    ∀ x ∈ D.S0, (continuousAmbientDataOf hk hk0 D).v x = D.v x := by
  classical
  haveI : NeZero (8 + k + 1) := ⟨by omega⟩
  let L : NNReal := Classical.choose (exists_Rmap_lipschitz n k hk)
  have hL : ∀ A Q : EndOp n, Q ∈ Gr n k →
      ‖A - Q‖ ≤ 1 / 8 → ‖Rmap A - Q‖ ≤ (L : ℝ) * ‖A - Q‖ :=
    Classical.choose_spec (exists_Rmap_lipschitz n k hk)
  set ε : ℝ := D.δ / 2 with hεdef
  have hε : 0 < ε := by rw [hεdef]; linarith [D.hδpos]
  let hex := smoothMap_into_tautTotal_eqOn_close n k hk hk0 D.M D.P D.v D.hPc D.hvc D.S0 D.hS0cl
    D.V D.hVopen D.hS0V D.hPsmV D.hvsmV D.hProj D.hMem L hL ε hε
  have keq := (Classical.choose_spec (Classical.choose_spec hex)).2.2.2.1
  intro x hx
  change (Classical.choose (Classical.choose_spec hex)) x = D.v x
  exact (keq x hx).2

/-- The collar field of the produced continuous data is `Set.univ` (definitionally): the first
smoothing is done on the *raw* collar `D.S0` and the resulting data carry no further collar. -/
theorem continuousAmbientDataOf_Sh {n k : ℕ} {ι : Type} [Fintype ι] {Fam : ι → Man8}
    (hk : k ≤ n) (hk0 : 0 < k) (D : RawAmbientData n k ι Fam) :
    (continuousAmbientDataOf hk hk0 D).Sh = Set.univ := rfl

end

end Work.PTGeometric
