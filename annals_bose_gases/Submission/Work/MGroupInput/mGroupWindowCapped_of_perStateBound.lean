import ChallengeDeps
import Submission.Work.MGroupInput.mGroupWindow_of_perStateBound
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.MGroupInput

/-- **`MGroupWindowCapped` from the per-state bound.**

This is the capped-window sibling of `mGroupWindow_of_perStateBound`.  The only
difference between the two targets is the extra hypothesis
`(P : ℝ) ≤ Cn' * μ * s ^ 3` carried by `MGroupWindowCapped`, which is simply
threaded through the `∀ P` in the conclusion and never used by the infimum
assembly.

The proof is literally the uncapped one: `diagWeBAt P … = diagKinPeBAt P … =
slotEB … P` is the infimum of the `blockE`-quotients over `CSBox P s`, `blockE`
is homogeneous of degree two in the state (`blockE_diagSlotWord_mul`), so a
bound holding at every normalised smooth state (`hp`) bounds the infimum
(`le_slotEB_of_forall_normalized`). -/
theorem mGroupWindowCapped_of_perStateBound {Cn Cn' s μ : ℝ} {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ,
      BoseGases.IsRadial w ∧ BoseGases.IsScatteringSolution w v) (c₀ cgap : ℝ)
    (hs : 0 < s)
    (hp : ∀ (P : ℕ), 1 ≤ P → Cn * μ * s ^ 3 ≤ (P : ℝ) → (P : ℝ) ≤ Cn' * μ * s ^ 3 →
      ∀ (Φ : Submission.BoseGases.X P → ℝ), ContDiff ℝ (⊤ : ℕ∞) Φ →
        (∫ x in Submission.BoseGases.abox P s, (Φ x) ^ 2) = 1 →
        (1 / 9) * (μ - (P : ℝ) / s ^ 3) ^ 2 * (8 * Real.pi * (BoseGases.a v) * s ^ 3)
          ≤ Work.KinPSuperadd.blockE s μ (Submission.BoseGases.wPairC s v)
              (Submission.BoseGases.wPairC s (Submission.BoseGases.g0 v h))
              (Work.KinPSuperadd.diagSlotWord s c₀ cgap) P Φ) :
    Work.MGroupInput.MGroupWindowCapped Cn Cn' s μ v h c₀ cgap := by
  intro P hP1 hP2 hP3
  refine le_slotEB_of_forall_normalized (N := P)
    (c := (1 / 9) * (μ - (P : ℝ) / s ^ 3) ^ 2 * (8 * Real.pi * (BoseGases.a v) * s ^ 3))
    (w := Submission.BoseGases.wPairC s v)
    (w1 := Submission.BoseGases.wPairC s (Submission.BoseGases.g0 v h))
    (K := Work.KinPSuperadd.diagSlotWord s c₀ cgap) ?_ ?_ hs
  · intro d Φ
    exact blockE_diagSlotWord_mul (s := s) (μ := μ) (c₀ := c₀) (cgap := cgap)
      (w := Submission.BoseGases.wPairC s v)
      (w1 := Submission.BoseGases.wPairC s (Submission.BoseGases.g0 v h)) P d Φ
  · intro Φ hΦc hΦn
    exact hp P hP1 hP2 hP3 Φ hΦc hΦn

end Work.MGroupInput
