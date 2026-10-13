import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS_EllLimOK.FatouG
import Submission.Work.FTS_EllLimOK.UniqFatou
import Submission.Work.FTS_EllLimOK.Locality
import Submission.Work.FTS_EllLimOK.HkMem_zero_diff

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.UniqG

theorem smallUniq3G_fts : ∃ α₁ : ℝ, 0 < α₁ ∧ ∀ α : ℝ, 0 < α → α ≤ α₁ →
    ∀ (E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn) (fn : ℕ → Work.FTS.Galerkin.Fn)
      (f : Work.FTS.Galerkin.Fn), Work.FTS_EllLimOK.LimSeq4 α fn f →
    ∀ Ψ Ψ' : Work.FTS.Galerkin.Fn,
      Work.FTS_EllLimOK.IsJetLimit3G α E fn f Ψ →
      Work.FTS_EllLimOK.IsJetLimit3G α E fn f Ψ' →
      ∀ j i : ℕ, j + i ≤ 3 → ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
        Work.Spaces.mixed j i Ψ z θ = Work.Spaces.mixed j i Ψ' z θ := by
  -- The open quadrant is an open set.
  have hQd : IsOpen Work.Construction.Qd := by
    rw [Work.Construction.Qd]
    exact isOpen_Ioi.prod isOpen_Ioo
  refine ⟨1, one_pos, fun α hα _ E fn f _ Ψ Ψ' hΨ hΨ' j i _ z θ hzθ => ?_⟩
  -- Both limits carry the Fatou package; in particular they solve the same elliptic law.
  have hFΨ : Work.FTS_EllLimOK.FatouPkgG α f Ψ := hΨ.1
  have hFΨ' : Work.FTS_EllLimOK.FatouPkgG α f Ψ' := hΨ'.1
  -- Their difference is in `ℋ⁰` (level `0` memberships + closed-box regularity).
  have hδ : Work.Spaces.HkMem α 0 (Work.FTS_EllLimOK.diff Ψ Ψ') :=
    Work.FTS_EllLimOK.HkMem_zero_diff hFΨ.mem hFΨ'.mem hFΨ.box hFΨ'.box
  -- Hence the uniqueness of the homogeneous elliptic problem gives pointwise equality on `Qd`.
  have heq : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → Ψ z θ = Ψ' z θ :=
    Work.FTS_EllLimOK.eqOn_of_same_law hα hFΨ.sol hFΨ'.sol hFΨ.box hFΨ'.box
      hFΨ.mem hFΨ.memCos hFΨ'.mem hFΨ'.memCos hδ
  -- `mixed` is local, so equality on the open quadrant implies equality of the jets there.
  exact Work.FTS_EllLimOK.mixed_congr_of_eqOn_isOpen hQd
    (fun p hp => heq p.1 p.2 hp) hzθ j i

end Work.FTS_EllLimOK.UniqG
