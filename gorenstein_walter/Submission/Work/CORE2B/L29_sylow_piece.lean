import Mathlib
import Submission.Work.CORE2B.L27_step1

namespace Work.CORE2B

/-- **The Sylow piece of the `D₁₆` case (iv) of Bender 1981 Lemma 2.9.**  Let `A ◁ N` be a
normal subgroup of a finite group `N` whose order is divisible by `4`, and let `V ≤ N` be a Klein
four-group of order `4`.  Then some `2`-subgroup `T ≤ N` contains `V` and meets `A` in a subgroup
of order at least `4`.

Proof: `V` is a `2`-group (of order `4`), so it lies in a Sylow `2`-subgroup `Q` of `N`; the
proved lemma `Work.CORE2B.sylow_inf_dvd` (`Submission/Work/CORE2B/L27_step1.lean`), applied to the
normal subgroup `A` of order divisible by `4`, gives `4 ∣ |Q ⊓ A|`, hence `4 ≤ |Q ⊓ A|`.  Take
`T := Q`. -/
theorem L29_sylow_piece {N : Type} [Group N] [Finite N] (A V : Subgroup N) [A.Normal]
    (h4A : 4 ∣ Nat.card A) (hV4 : Nat.card V = 4) :
    ∃ T : Subgroup N, IsPGroup 2 T ∧ V ≤ T ∧ 4 ≤ Nat.card ↥(T ⊓ A) := by
  have hVpg : IsPGroup 2 V := IsPGroup.of_card (n := 2) (by rw [hV4]; norm_num)
  obtain ⟨Q, hVQ⟩ := IsPGroup.exists_le_sylow (p := 2) hVpg
  refine ⟨(Q : Subgroup N), Q.isPGroup', hVQ, ?_⟩
  exact Nat.le_of_dvd Nat.card_pos (sylow_inf_dvd A h4A Q)

end Work.CORE2B
