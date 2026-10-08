import Mathlib
import Submission.Work.CORE4.Defs10
import Submission.Work.CORE4.API
import Submission.Work.CORE4.EightIdxDefs
import Submission.Work.CORE4.EightULeP
import Submission.Work.CORE4.Case2EightQfacts

namespace Work.CORE4

/-- Bender 1981, §4 (8), case 2 of the trichotomy on `Q := Qsub p B = Ω₁(Z₂(O_p(U)))`: with
`Z(Q) < A < Q` and `A.relIndex Q = p`, the orbit number `u = |U : N_U(A)|` is at most `p`.

This is a copy of the sorry-backed `Work.CORE4.Case2EightN9U`; it is a short assembly from the
proved `Case2EightQfacts` (`Q ≤ F(U)`, `U ≤ N_G(Q)`, `x^p = 1` on `Q`) and the proved counting
lemma `Work.CORE4.eightU_le_p_of_case2` (`CORE4/EightULeP.lean`), plus `p` odd from
`p ∣ |F| ∣ |U|` and `B.U_odd`.  Must be sorry-free:
`#print axioms Work.CORE4.EightN9U` = `[propext, Classical.choice, Quot.sound]`. -/
theorem EightN9U (I : Work.GW2.C4Inputs) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G → ∀ B : Work.GW2.BenderSetup G,
      Work.GW2.Case2 B → ∀ C : Work.GW2.Case2Ctx6 B, Work.GW2.Case2PrePlus B C.D →
        Work.GW2.Case2SevenFacts B C.D →
        ∀ (p : ℕ) (P A : Subgroup G), p.Prime → P ≤ C.D.F → Nat.card P = p →
          Work.GW2.Case2EightObj C.D p P A →
          A ≤ Work.CORE4.Qsub p B → Work.CORE4.centerIn (Work.CORE4.Qsub p B) < A →
            A < Work.CORE4.Qsub p B → A.relIndex (Work.CORE4.Qsub p B) = p →
            Work.GW2.Case2EightU B A ≤ p := by
  intro G _ _ hbc B h2 C hplus h7 p P A hp hPF hPcard hobj hAQ hZlt _hAlt hidx
  -- Bender §4 (8): the four facts about `Q = Qsub p B`
  have hfacts := Case2EightQfacts I G hbc B h2 C hplus h7 p P A hp hPF hPcard hobj
  obtain ⟨_hQF, hQN, hQexp, _hQnc⟩ := hfacts
  -- `p` is odd, since `p ∣ |F|` and `|F| ∣ |U|` with `|U|` odd
  have hpodd : Odd p := by
    have h1 : p ∣ Nat.card ↥C.D.F := by
      rw [← hPcard]
      exact Subgroup.card_dvd_of_le hPF
    have h2 : Nat.card ↥C.D.F ∣ Nat.card ↥B.U :=
      Subgroup.card_dvd_of_le (Work.GW2.Case2Data.F_le_U B C.D)
    exact Odd.of_dvd_nat B.U_odd (h1.trans h2)
  -- the counting lemma of `CORE4/EightULeP.lean`
  exact eightU_le_p_of_case2 B hp hpodd hQN hAQ hZlt hobj.2.2.2.2.1 hidx hQexp

end Work.CORE4
