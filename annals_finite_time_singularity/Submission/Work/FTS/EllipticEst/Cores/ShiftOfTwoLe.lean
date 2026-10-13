/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Cores.ShiftOfTwoLe`: the *radially differentiated* weak class, one level down

Elgindi's Proposition `prop:Hk` is proved by induction on the order `k`, and the induction step
is applied not to the datum `(F, Ψ)` itself but to its radial derivative
`(D_z F, D_z Ψ) = (z ∂_z F, z ∂_z Ψ)`, at level `k - 1`.  This module records that passage:

  if `(F, Ψ)` is of the weak class `EllWeakPos α k F Ψ` at order `k ≥ 2`, then
  `(D_z F, D_z Ψ)` is of the weak class at order `k - 1`.

Every one of the ten fields of the bundle is preserved, for its own reason:

* *the equation*: `bslOp α = -α²D_z² - 5αD_z + Lzero` and `Lzero` is `z`-independent, so `D_z`
  commutes with `bslOp` (`TT.bslOp_DzIter_eq`);
* *the Dirichlet data*: `D_z` annihilates a function that is identically zero in `z` on the
  line `θ = 0` (resp. `θ = π/2`) (`TT.DzIter_zero_at_zero`, `TT.DzIter_zero_at_pi_half`);
* *the two moment conditions*: these are the only genuinely analytic fields; they are the
  siblings `remov.Fstar_DzIter_one_F_ge_two` (the source half; note the hypothesis `2 ≤ k`,
  which is where the `k ≥ 2` in the statement comes from) and `remov.Fstar_DzIter_one_Psi`
  (the solution half, a first-order difference-quotient argument);
* *smoothness on the open quadrant*: preserved by `D_z` (`TT.EllWeakPos.smoothOpen_DzIter`);
* *the four honesty fields* `HkMem α (k-1)` of `D_z F`, `z²∂_zz(D_z Ψ)`, `∂_θθ(D_z Ψ)` and
  `z ∂_z∂_θθ(D_z Ψ)`: the pointwise domination "every slot of `HkIntegrand α (k-1) (D_z g)` is
  a slot of `HkIntegrand α k g`" (`AeMom.Repair.HkMem_Dz_shift`, the buildable repair copy of
  `remov.HkMem_Dz_shift`), transported across the two commutation identities
  `z²∂_zz(D_z Ψ) = D_z(z²∂_zzΨ)` (`DzAmgm.ZsqPz2Comm`) and
  `∂_θθ(D_z Ψ) = D_z(∂_θθΨ)` (`AeMom.Repair.Dz_pthIter_two_comm`), and the fact that the
  source `F` of the weak class is `C^∞` on the open quadrant because there it coincides with
  `bslOp α Ψ` (`AeMom.Repair.SmoothOpen_of_bslOp_eq`).

The statement is exactly `Work.FTS.EllipticEst.Cores.ShiftOfTwoLe`; the helper below is only the
assembly, split out so that the `refine` structure stays readable.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.TT.bslOp_DzIter_eq
import Submission.Work.FTS.EllipticEst.TT.SliceDatum
import Submission.Work.FTS.EllipticEst.TT.HkMem_descend_open
import Submission.Work.FTS.EllipticEst.remov.Fstar_DzIter_one_F_ge_two
import Submission.Work.FTS.EllipticEst.remov.Fstar_DzIter_one_Psi
import Submission.Work.FTS.EllipticEst.HkSq_congr_open
import Submission.Work.FTS.EllipticEst.remov.Dz_slice_identities
import Submission.Work.FTS.LocData.HkMem_of_majorant
import Submission.Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0
import Submission.Work.FTS.EllipticEst.DzAmgm.ZsqPz2Comm
import Submission.Work.FTS.EllipticEst.DzAmgm.DthIterDzCommOpen
import Submission.Work.Spaces.mixed_comm
import Submission.Work.FTS.EllipticEst.AeMom.Repair.ShiftAeRepair

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cores

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- **The assembly of the shift, given the two moment conditions.**

This is `ShiftOfTwoLe` with the two analytic inputs (`F_*(D_z F) = 0` and `F_*(D_z Ψ) = 0`)
supplied as explicit hypotheses; the target `ShiftOfTwoLe` below instantiates them with the
sibling modules.  The `k ≥ 1` version suffices here. -/
theorem shiftOfTwoLe_of_moments {α : ℝ} {k : ℕ} (hk : 1 ≤ k) {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ)
    (hmomF : ∀ z, 0 < z → Work.Elliptic.Fstar (Work.Spaces.DzIter 1 F) z = 0)
    (hmomΨ : ∀ z, 0 < z → Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) z = 0) :
    Work.FTS.EllipticEst.TT.EllWeakPos α (k - 1)
      (Work.Spaces.DzIter 1 F) (Work.Spaces.DzIter 1 Ψ) := by
  have hSΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.TT.EllWeakPos.smoothOpen h
  -- the source coincides with `bslOp α Ψ` on the open quadrant, hence is smooth there
  have hSF : Work.FTS.EllipticEst.SmoothOpen F :=
    Work.FTS.EllipticEst.AeMom.Repair.SmoothOpen_of_bslOp_eq hSΨ
      (fun z θ hz hθ hlt => h.1 z hz θ hθ hlt)
  -- `∂_θ²Ψ` is smooth on the open quadrant as well
  have hSpth2 : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 Ψ) := by
    have h1 : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pth Ψ) :=
      Work.FTS.EllipticEst.SmoothOpen.pth hSΨ
    have h2 : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pth (Work.Spaces.pth Ψ)) :=
      Work.FTS.EllipticEst.SmoothOpen.pth h1
    simpa only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero] using h2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the equation: `bslOp` commutes with `D_z`
    exact Work.FTS.EllipticEst.TT.bslOp_DzIter_eq α F Ψ 1 h.smooth h.1
  · -- the Dirichlet datum at `θ = 0`
    exact Work.FTS.EllipticEst.TT.DzIter_zero_at_zero Ψ 1 h.zero
  · -- the Dirichlet datum at `θ = π/2`
    exact Work.FTS.EllipticEst.TT.DzIter_zero_at_pi_half Ψ 1 h.pi_half
  · -- the source moment condition
    exact hmomF
  · -- the solution moment condition
    exact hmomΨ
  · -- smoothness on the open quadrant is preserved by `D_z`
    intro n
    exact (Work.FTS.EllipticEst.smoothOpen_iff_forall (Work.Spaces.DzIter 1 Ψ)).mp
      (Work.FTS.EllipticEst.TT.EllWeakPos.smoothOpen_DzIter h 1) n
  · -- `D_z F ∈ ℋ^{k-1}`
    have hmem : Work.Spaces.HkMem α (k - 1) (Work.Spaces.Dz F) :=
      Work.FTS.EllipticEst.AeMom.Repair.HkMem_Dz_shift hk hSF h.memF
    simpa only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero] using hmem
  · -- `z² ∂_zz(D_z Ψ) ∈ ℋ^{k-1}`
    have hG : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
      Work.FTS.EllipticEst.AeMom.Repair.SmoothOpen.zsq_mul
        (Work.FTS.EllipticEst.SmoothOpen.pzIter hSΨ 2)
    have hmem : Work.Spaces.HkMem α (k - 1)
        (Work.Spaces.Dz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) :=
      Work.FTS.EllipticEst.AeMom.Repair.HkMem_Dz_shift hk hG h.memA
    refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α (k - 1) hmem ?_
    intro z hz θ hθ
    exact (Work.FTS.EllipticEst.DzAmgm.ZsqPz2Comm Ψ hSΨ 1 0
      (show ((z, θ) : ℝ × ℝ) ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)
        from ⟨hz, hθ⟩)).symm
  · -- `∂_θθ(D_z Ψ) ∈ ℋ^{k-1}`
    have hmem : Work.Spaces.HkMem α (k - 1)
        (Work.Spaces.Dz (Work.Spaces.pthIter 2 Ψ)) :=
      Work.FTS.EllipticEst.AeMom.Repair.HkMem_Dz_shift hk hSpth2 h.memB
    refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α (k - 1) hmem ?_
    intro z hz θ hθ
    exact Work.FTS.EllipticEst.AeMom.Repair.Dz_pthIter_two_comm hSΨ z θ hz hθ.1 hθ.2
  · -- `z ∂_z ∂_θθ(D_z Ψ) ∈ ℋ^{k-1}`
    have hGs : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ) :=
      Work.FTS.EllipticEst.SmoothOpen.Dz hSpth2
    have hmem : Work.Spaces.HkMem α (k - 1)
        (Work.Spaces.Dz (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ)) :=
      Work.FTS.EllipticEst.AeMom.Repair.HkMem_Dz_shift hk hGs h.memZPth2
    refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α (k - 1) hmem ?_
    intro z hz θ hθ
    have hEqOn : Set.EqOn (Function.uncurry (Work.Spaces.Dz (Work.Spaces.pthIter 2 Ψ)))
        (Function.uncurry (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ)))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
      rintro ⟨z', θ'⟩ ⟨hz', hθ'⟩
      exact Work.FTS.EllipticEst.AeMom.Repair.Dz_pthIter_two_comm hSΨ z' θ' hz' hθ'.1 hθ'.2
    have hpe : Work.Spaces.pz (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ)) z θ
        = Work.Spaces.pz (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) z θ :=
      Work.Spaces.pz_congr_of_isOpen (isOpen_Ioi.prod isOpen_Ioo) hEqOn.symm ⟨hz, hθ⟩
    rw [hpe]
    rfl

/-- **The radially differentiated data are again of the weak class, one level down** (Elgindi,
the induction step of `prop:Hk`). -/
theorem ShiftOfTwoLe {α : ℝ} {k : ℕ} (hk : 2 ≤ k) {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) :
    Work.FTS.EllipticEst.TT.EllWeakPos α (k - 1)
      (Work.Spaces.DzIter 1 F) (Work.Spaces.DzIter 1 Ψ) :=
  shiftOfTwoLe_of_moments (by omega) h
    (Work.FTS.EllipticEst.remov.Fstar_DzIter_one_F_ge_two hk h)
    (Work.FTS.EllipticEst.remov.Fstar_DzIter_one_Psi (by omega) h)

end Work.FTS.EllipticEst.Cores
