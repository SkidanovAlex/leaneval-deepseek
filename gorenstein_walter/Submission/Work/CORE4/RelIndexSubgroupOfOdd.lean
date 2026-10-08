import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.Case2CountSetup

namespace Work.CORE4

/-- If `P ≤ M` has odd index in `M` (so `P` is a Sylow `2`-subgroup of `M`), `E ≤ M`, and `P`
normalizes `E`, then `P ⊓ E` has odd index in `E`, i.e. `2 ∤ [E : P ⊓ E]`.

Route.  `E ⊔ P ≤ M` and `P ≤ normalizer E`, so the Noether isomorphism in index form
(`Work.CORE4.relIndex_eq_relIndex_inf_of_normal_sup_eq E P (E ⊔ P)`, available in
`Submission.Work.CORE4.Case2CountSetup`) gives `P.relIndex (E ⊔ P) = (E ⊓ P).relIndex E`; on the
other hand `Subgroup.relIndex_mul_relIndex` shows `P.relIndex (E ⊔ P) ∣ P.relIndex M`, which is
odd.  Finally `Subgroup.relIndex_top_right : H.relIndex ⊤ = H.index` identifies
`((P ⊓ E).subgroupOf E).relIndex ⊤` with `(E ⊓ P).relIndex E` (note `P ⊓ E = E ⊓ P` by
`inf_comm`). -/
theorem RelIndexSubgroupOfOdd {G : Type} [Group G] [Finite G]
    (E P M : Subgroup G) (hE : E ≤ M) (hPE : P ≤ Subgroup.normalizer (E : Set G)) (hP : P ≤ M)
    (hrel : ¬ 2 ∣ P.relIndex M) : ¬ 2 ∣ ((P ⊓ E).subgroupOf E).relIndex ⊤ := by
  -- `E ⊔ P ≤ M` because both `E` and `P` are contained in `M`.
  have hsupM : E ⊔ P ≤ M := sup_le hE hP
  -- `E` is normal in `E ⊔ P`, since `E ⊔ P ≤ normalizer E` (`E ≤ normalizer E` and `P` does).
  have hnorm : (E.subgroupOf (E ⊔ P)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff le_sup_left]
    intro h k hh hk
    have hsupN : E ⊔ P ≤ Subgroup.normalizer (E : Set G) :=
      sup_le Subgroup.le_normalizer hPE
    have hkE : k ∈ Subgroup.normalizer (E : Set G) := hsupN hk
    exact ((Subgroup.mem_normalizer_iff).mp hkE h).mp hh
  -- Noether isomorphism, index form: `|E ⊔ P : P| = |E : E ⊓ P|`.
  have hmain : P.relIndex (E ⊔ P) = (E ⊓ P).relIndex E :=
    Work.CORE4.relIndex_eq_relIndex_inf_of_normal_sup_eq E P (E ⊔ P)
      le_sup_left le_sup_right rfl hnorm
  -- `P.relIndex (E ⊔ P)` divides `P.relIndex M`, which is odd.
  have hdvd : P.relIndex (E ⊔ P) ∣ P.relIndex M :=
    ⟨(E ⊔ P).relIndex M,
      (Subgroup.relIndex_mul_relIndex P (E ⊔ P) M le_sup_right hsupM).symm⟩
  have hodd : Odd (P.relIndex M) :=
    Nat.not_even_iff_odd.mp (fun he => hrel (even_iff_two_dvd.mp he))
  have hodd' : Odd (P.relIndex (E ⊔ P)) := hodd.of_dvd_nat hdvd
  have hoddE : Odd ((E ⊓ P).relIndex E) := hmain ▸ hodd'
  -- `((P ⊓ E).subgroupOf E).relIndex ⊤ = (E ⊓ P).relIndex E`.
  have hgoal : ((P ⊓ E).subgroupOf E).relIndex ⊤ = (E ⊓ P).relIndex E := by
    rw [Subgroup.relIndex_top_right, inf_comm P E]
    rfl
  rw [hgoal]
  exact fun h2 => (Nat.not_even_iff_odd.mpr hoddE) (even_iff_two_dvd.mpr h2)

end Work.CORE4
