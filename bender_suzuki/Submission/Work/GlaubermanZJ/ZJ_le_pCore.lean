import Mathlib
import Submission.Work.GlaubermanZJ.Basic
import Submission.Work.GlaubermanZJ.hasAbelianSylowTwo_iff
import Submission.Work.GlaubermanZJ.isAbelianSubgroup_ZJ
import Submission.Work.GlaubermanZJ.ZJ_le
import Submission.Work.GlaubermanZJ.ZJ_eq
import Submission.Work.LocalPrelim.ft7_9
import Submission.Work.PGroup.All

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.GlaubermanZJ

/-- `Z(J(S))` is normalized by `S`: it is characteristic in `S` because `J(S)` is, and the
normalizer of a subgroup is contained in the normalizer of its Thompson subgroup. -/
theorem sylow_le_normalizer_ZJ {X : Type*} [Group X] [Finite X] {p : ℕ} (S : Sylow p X) :
    (S : Subgroup X) ≤ Subgroup.normalizer (Submission.Blueprint.ZJ (S : Subgroup X) : Set X) := by
  refine le_trans Subgroup.le_normalizer ?_
  intro g hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  rw [ZJ_eq (S : Subgroup X)]
  have hchar := Work.PGroup.ZJ_characteristic (S : Subgroup X) g hg
  rwa [Work.PGroup.conjBy, Subgroup.pointwise_smul_def] at hchar

-- `Z(J(S)) ⊆ O_p(X)` when `X` is finite p-solvable with abelian Sylow 2-subgroups (or `5 ≤ p`)
-- and `O_{p'}(X) = ⊥`: this is the first half of the proof of Theorem A (p. 1114), obtained here
-- from the delivered quadratic Hall–Higman result (`Work.LocalPrelim.ft7_2_cond3_pstable_core`)
-- via the fact that `Z(J(S))` is abelian and normal in `S`, so `[S, Z(J(S)), Z(J(S))] = 1`.
theorem ZJ_le_pCore {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : p.Prime) (hpne : p ≠ 2)
    (hps : Work.HallHigman.IsPSolvable p X)
    (h2 : 5 ≤ p ∨ Work.GlaubermanZJ.HasAbelianSylowTwo X)
    (hcore : Work.Fitting.pPrimeCore p X = ⊥) (S : Sylow p X) :
    Submission.Blueprint.ZJ (S : Subgroup X) ≤ Work.Fitting.pCore p X := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h2' : 5 ≤ p ∨ ∀ Q : Sylow 2 X, IsMulCommutative ↥(Q : Subgroup X) := by
    rcases h2 with h | h
    · exact Or.inl h
    · exact Or.inr ((hasAbelianSylowTwo_iff (G := X)).mp h)
  -- `ZJ S` is abelian
  have hAab : Submission.Blueprint.IsAbelianSubgroup
      (Submission.Blueprint.ZJ (S : Subgroup X)) := isAbelianSubgroup_ZJ _
  -- so `[ZJ S, ZJ S] = 1`
  have hAA : ⁅Submission.Blueprint.ZJ (S : Subgroup X),
      Submission.Blueprint.ZJ (S : Subgroup X)⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact hAab b hb a ha
  -- `ZJ S` is normal in `S`, so `[S, ZJ S] ≤ ZJ S`
  have hSA : ⁅(S : Subgroup X), Submission.Blueprint.ZJ (S : Subgroup X)⁆
      ≤ Submission.Blueprint.ZJ (S : Subgroup X) := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp (sylow_le_normalizer_ZJ S)
  -- hence `[[S, ZJ S], ZJ S] ≤ [ZJ S, ZJ S] = 1`
  have hcomm : ⁅⁅(S : Subgroup X), Submission.Blueprint.ZJ (S : Subgroup X)⁆,
      Submission.Blueprint.ZJ (S : Subgroup X)⁆ = ⊥ := by
    refine le_bot_iff.mp ?_
    calc ⁅⁅(S : Subgroup X), Submission.Blueprint.ZJ (S : Subgroup X)⁆,
            Submission.Blueprint.ZJ (S : Subgroup X)⁆
        ≤ ⁅Submission.Blueprint.ZJ (S : Subgroup X),
            Submission.Blueprint.ZJ (S : Subgroup X)⁆ := Subgroup.commutator_mono_left hSA
      _ = ⊥ := hAA
  exact Work.LocalPrelim.ft7_2_cond3_pstable_core hp (hp.odd_of_ne_two hpne) hps h2' hcore
    ((Sylow.isPGroup' S).to_le (ZJ_le (S : Subgroup X))) hcomm

end Work.GlaubermanZJ
