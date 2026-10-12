import ChallengeDeps
import Submission.Work.SlotWord.dlThreshold_eq_delivered_shape
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SlotWord

/-- **The DL threshold in the `dlThreshold` shape bounded by the delivered faithful
per-box ground energy.**  This is `Submission.BoseGases.smallbox_dl_energy_bound_at_count`
(the delivered FS `thm:smallbox` at the faithful word, in its density-coefficient shape),
re-expressed through the definitional identity `dlThreshold_eq_delivered_shape`: the
algebraic left-hand side of the delivered bound is *by definition* the DL threshold at the
box `χ`-mass `V = s³` and the symbol `Γ = (R/s)² + dlGamma K_B μ (a v)`.  The constants
`c, C` are those of the delivered theorem, so the bound is uniform over the data and the
count, exactly as the sliding-word residual needs it. -/
theorem dlThreshold_le_diagWeBAt_of_smallbox :
    ∃ c : ℝ, 0 < c ∧ c < 1 / 2 ∧
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ (D : Submission.BoseGases.DLBoxData) (P : ℕ), 1 ≤ P → (P : ℝ) / D.s ^ 3 ≤ 9 * D.μ →
          Work.FockBridge.dlThreshold c C D.μ (BoseGases.a D.v) (D.s ^ 3)
              ((D.R / D.s) ^ 2 + Work.FockBridge.dlGamma D.K_B D.μ (BoseGases.a D.v))
              (P : ℝ)
            ≤ Work.BlockBound4.diagWeBAt P D.s D.μ D.v D.h D.c₀ D.cgap := by
  obtain ⟨c, hc0, hc1, C, hC0, hbound⟩ :=
    Submission.BoseGases.smallbox_dl_energy_bound_at_count
  refine ⟨c, hc0, hc1, C, hC0, ?_⟩
  intro D P hP hwin
  have h := hbound D P hP hwin
  rw [← Work.SlotWord.dlThreshold_eq_delivered_shape c C D.μ (BoseGases.a D.v) D.R D.s
        (Work.FockBridge.dlGamma D.K_B D.μ (BoseGases.a D.v)) (P : ℝ)]
  simpa only [Work.FockBridge.dlGamma] using h

end Work.SlotWord
