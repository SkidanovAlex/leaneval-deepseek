import Mathlib
import Submission.Work.PiS.Interfaces

namespace Work.SSS

open scoped Topology unitInterval

/-- **In a path connected, simply connected space any two paths with the same endpoints are
homotopic.**  More precisely, if `B` is path connected and `π₁(B, b₀)` is trivial (`Work.PiS.SimplyConn`
gives both, the path connectedness through the triviality of `π₀`), then for any two points
`b b' : B` and any two paths `γ γ' : Path b b'` between them, `γ` and `γ'` are homotopic relative to
the endpoints.  (Given a path `μ` from `b₀` to `b`, the loop `μ * (γ * γ'⁻¹) * μ⁻¹` based at `b₀`
is null homotopic since `π₁(B,b₀)` is trivial, and conjugating this homotopy back along `μ` gives
the required homotopy.) -/
theorem pathsHomotopicOfSimplyConn {B : Type} [TopologicalSpace B] (b₀ : B)
    (hc : Work.PiS.SimplyConn B b₀) :
    ∀ {b b' : B} (γ γ' : Path b b'), Path.Homotopic γ γ' := by
  intro b b' γ γ'
  -- `π₀(B, b₀)` trivial: every point of `B` is joined to `b₀` by a path.
  have hsub0 : Subsingleton (ZerothHomotopy B) :=
    (Equiv.subsingleton_congr (HomotopyGroup.pi0EquivZerothHomotopy (X := B) (x := b₀))).mp hc.1
  have hjoined : Joined b₀ b :=
    Quotient.exact (hsub0.allEq (ZerothHomotopy.mk b₀) (ZerothHomotopy.mk b))
  obtain ⟨μ⟩ := hjoined
  -- `π₁(B, b₀)` trivial.
  have hsub1 : Subsingleton (FundamentalGroup B b₀) :=
    (Equiv.subsingleton_congr
      (HomotopyGroup.pi1MulEquivFundamentalGroup (X := B) (x := b₀)).toEquiv).mp hc.2
  -- Conjugate the triviality along `μ` to get `π₁(B, b)` trivial, i.e. all loops at `b` are
  -- null homotopic relative to the endpoints.
  have hsubb : Subsingleton (Path.Homotopic.Quotient b b) :=
    (Equiv.subsingleton_congr
      (FundamentalGroup.fundamentalGroupMulEquivOfPath (X := B) μ).toEquiv).mp hsub1
  have hL : Path.Homotopic.Quotient.trans (Path.Homotopic.Quotient.mk γ)
      (Path.Homotopic.Quotient.symm (Path.Homotopic.Quotient.mk γ'))
      = Path.Homotopic.Quotient.refl b := hsubb.allEq _ _
  -- Cancel `γ'` on the right using the groupoid identities for `Path.Homotopic.Quotient`.
  have hmain : Path.Homotopic.Quotient.mk γ = Path.Homotopic.Quotient.mk γ' := by
    calc Path.Homotopic.Quotient.mk γ
        = Path.Homotopic.Quotient.trans (Path.Homotopic.Quotient.mk γ)
            (Path.Homotopic.Quotient.refl b') := by
          rw [Path.Homotopic.Quotient.trans_refl]
      _ = Path.Homotopic.Quotient.trans (Path.Homotopic.Quotient.mk γ)
            (Path.Homotopic.Quotient.trans (Path.Homotopic.Quotient.symm (Path.Homotopic.Quotient.mk γ'))
              (Path.Homotopic.Quotient.mk γ')) := by
          rw [Path.Homotopic.Quotient.symm_trans]
      _ = Path.Homotopic.Quotient.trans
            (Path.Homotopic.Quotient.trans (Path.Homotopic.Quotient.mk γ)
              (Path.Homotopic.Quotient.symm (Path.Homotopic.Quotient.mk γ')))
            (Path.Homotopic.Quotient.mk γ') := by
          rw [Path.Homotopic.Quotient.trans_assoc]
      _ = Path.Homotopic.Quotient.trans (Path.Homotopic.Quotient.refl b)
            (Path.Homotopic.Quotient.mk γ') := by
          rw [hL]
      _ = Path.Homotopic.Quotient.mk γ' := by
          rw [Path.Homotopic.Quotient.refl_trans]
  exact Path.Homotopic.Quotient.eq.mp hmain

end Work.SSS
