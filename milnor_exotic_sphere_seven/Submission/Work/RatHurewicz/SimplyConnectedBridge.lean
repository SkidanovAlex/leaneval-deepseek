import Mathlib
import Submission.Work.RatHurewicz.ConnectivityBridge

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Cube-based simple connectivity versus Mathlib's `SimplyConnectedSpace`

Area **RATHUREWICZ** (`Submission/Work/RatHurewicz/`).  `ConnectivityBridge.lean` gives the `π₀`
half of the vocabulary bridge between the cube-based connectivity hypotheses of this area's contract
and Mathlib's `PathConnectedSpace`/`SimplyConnectedSpace`.  This module adds the `π₁` half:

* `Work.RatHurewicz.simplyConnectedSpace_of_subsingleton` — cube-based `π₀`- and `π₁`-triviality at
  a point imply `SimplyConnectedSpace X`.

With this bridge, the crux statements of the *other* areas (`Work.StemsB.RatHurewiczGeneral`,
`Work.Stems.RatHurewiczTheorem`, the degree-two Hurewicz statements) — all phrased with Mathlib's
`SimplyConnectedSpace`/`PathConnectedSpace` — can be fed from the cube-based connectivity hypotheses
of `Work.Drive.RationalHurewiczStable`, so that whichever of them is established first yields the
contract.

The proof uses the groupoid laws of `Path.Homotopic.Quotient` (`trans_assoc`, `symm_trans`,
`trans_symm`, `refl_trans`, `trans_refl`) to cancel a path on the left and on the right.
-/

open scoped Topology

namespace Work.RatHurewicz

noncomputable section

/-- **Cube-based simple connectivity implies `SimplyConnectedSpace`.**  If the cube-based `π₀` and
`π₁` of `X` at `x₀` are trivial, then `X` is simply connected in Mathlib's sense: there is a unique
path-homotopy class between any two points of `X`. -/
theorem simplyConnectedSpace_of_subsingleton {X : Type} [TopologicalSpace X] (x₀ : X)
    (h0 : Subsingleton (HomotopyGroup (Fin 0) X x₀))
    (h1 : Subsingleton (HomotopyGroup (Fin 1) X x₀)) : SimplyConnectedSpace X := by
  haveI hpc : PathConnectedSpace X := pathConnectedSpace_of_subsingleton_pi_zero x₀ h0
  have hq : Subsingleton (Path.Homotopic.Quotient x₀ x₀) := by
    haveI := h1
    exact (HomotopyGroup.pi1EquivFundamentalGroup (X := X) (x := x₀)).surjective.subsingleton
  rw [simply_connected_iff_paths_homotopic]
  refine ⟨hpc, fun x y => ?_⟩
  have key : ∀ (p : Path x₀ x) (r : Path y x₀) (ζ : Path x y),
      Path.Homotopic.Quotient.mk ζ =
        (Path.Homotopic.Quotient.mk p).symm.trans
          ((Path.Homotopic.Quotient.mk (p.trans (ζ.trans r))).trans
            (Path.Homotopic.Quotient.mk r).symm) := by
    intro p r ζ
    rw [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_trans]
    simp only [Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.symm_trans,
      Path.Homotopic.Quotient.trans_symm, Path.Homotopic.Quotient.refl_trans,
      Path.Homotopic.Quotient.trans_refl]
    rw [← Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.symm_trans,
      Path.Homotopic.Quotient.refl_trans]
  refine ⟨fun a b => ?_⟩
  induction a using Quotient.inductionOn with
  | h γ =>
    induction b using Quotient.inductionOn with
    | h δ =>
      change Path.Homotopic.Quotient.mk γ = Path.Homotopic.Quotient.mk δ
      rw [key (PathConnectedSpace.somePath x₀ x) (PathConnectedSpace.somePath y x₀) γ,
        key (PathConnectedSpace.somePath x₀ x) (PathConnectedSpace.somePath y x₀) δ]
      have hmid : Path.Homotopic.Quotient.mk
          ((PathConnectedSpace.somePath x₀ x).trans
            (γ.trans (PathConnectedSpace.somePath y x₀)))
          = Path.Homotopic.Quotient.mk
            ((PathConnectedSpace.somePath x₀ x).trans
              (δ.trans (PathConnectedSpace.somePath y x₀))) := hq.elim _ _
      rw [hmid]

end

end Work.RatHurewicz
