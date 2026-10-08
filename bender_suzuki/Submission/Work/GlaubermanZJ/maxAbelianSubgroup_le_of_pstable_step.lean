import Mathlib
import Submission.Work.GlaubermanZJ.theorem3_2_defs
import Submission.Work.GlaubermanZJ.lemma3_5_a
import Submission.Work.GlaubermanZJ.cor3_1

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Glauberman 1968, Theorem 3.2, the final paragraph of the proof

This is the argument of the last paragraph of the proof of Glauberman's Theorem 3.2
(p. 1110).  Let `S` be a Sylow `p`-subgroup of the finite group `X` (`p` odd), `L ⊴ X`,
`V ⊴ X` a normal abelian `p`-subgroup of `X` with `V ≤ Z(J(L ∩ S))`, and suppose that
`hstep` holds: for every normal `p`-subgroup `C₁ ⊴ X` containing `C` and every `p`-subgroup
`A ≤ S` with `[C₁,A,A] = 1`, one has `A ≤ L` (this is step (3.5) of the source,
`Work.GlaubermanZJ.pstable_step`).  Then no abelian subgroup of `S` of maximal order avoids
`L`.

Suppose `A ∈ 𝒜(S)` with `A ⊄ L`.  By `hstep` with `C₁ = V` (which contains `C`), one has
`[V,A,A] ≠ 1` — display (3.9).  Thompson's replacement theorem produces `A* ∈ 𝒜(S)` with
`A ∩ V ⊊ A* ∩ V` and `[A*,A,A] = 1`; maximality of `A ∩ V` among the abelian subgroups of
maximal order of `S` not contained in `L` forces `A* ≤ L`, so `A*` is an abelian subgroup of
maximal order of `L ∩ S` and Lemma 3.5(a) gives `Z(J(L ∩ S)) ≤ A*`.  Since `V ≤ Z(J(L ∩ S))`,
`[V,A,A] ≤ [A*,A,A] = 1`, contradicting (3.9).  The descent is well founded because
`|A ∩ V|` strictly increases.
-/

set_option autoImplicit false

open scoped Classical Pointwise

namespace Work.GlaubermanZJ

theorem maxAbelianSubgroup_le_of_pstable_step {X : Type*} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) (hpne : p ≠ 2) (S : Sylow p X) (C V L : Subgroup X)
    (hLnorm : L.Normal) (hVnorm : V.Normal) (hVp : IsPGroup p V)
    (hVab : Submission.Blueprint.IsAbelianSubgroup V)
    (hVZ : V ≤ Submission.Blueprint.ZJ (L ⊓ (S : Subgroup X) : Subgroup X))
    (hCV : C ≤ V)
    (hstep : ∀ (C₁ : Subgroup X), C₁.Normal → IsPGroup p C₁ → C ≤ C₁ →
      ∀ (A : Subgroup X), A ≤ (S : Subgroup X) → IsPGroup p A → ⁅⁅C₁, A⁆, A⁆ = ⊥ → A ≤ L) :
    ∀ A : Subgroup X, Work.GlaubermanZJ.IsMaxAbelianSubgroup (S : Subgroup X) A → A ≤ L := by
  haveI : L.Normal := hLnorm
  haveI : V.Normal := hVnorm
  have hS : IsPGroup p (S : Subgroup X) := S.isPGroup'
  have hVS : V ≤ (S : Subgroup X) :=
    hVZ.trans (((blueprint_ZJ_le_thompsonJ (L ⊓ (S : Subgroup X))).trans
      (blueprint_thompsonJ_le (L ⊓ (S : Subgroup X)))).trans inf_le_right)
  have key : ∀ n : ℕ, ∀ A : Subgroup X, IsMaxAbelianSubgroup (S : Subgroup X) A →
      Nat.card ↥V + 1 - Nat.card ↥(A ⊓ V) = n → A ≤ L := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih A hA heqn
    by_cases hAL : A ≤ L
    · exact hAL
    exfalso
    have hAcard : Nat.card A = Work.PGroup.maxAbelianOrder (S : Subgroup X) :=
      ((isMaxAbelianSubgroup_iff (S : Subgroup X) A).mp hA).2.2
    obtain ⟨hAS, hAab, hAmax⟩ := hA
    have hAp : IsPGroup p A := hS.to_le hAS
    -- display (3.9): `[V,A,A] ≠ 1`
    have hcomm_ne : ⁅⁅V, A⁆, A⁆ ≠ ⊥ := fun h0 => hAL (hstep V hVnorm hVp hCV A hAS hAp h0)
    -- Thompson's replacement theorem
    have hAcom : IsMulCommutative A := (isAbelianSubgroup_iff_isMulCommutative A).mp hAab
    have hVcom : IsMulCommutative V := (isAbelianSubgroup_iff_isMulCommutative V).mp hVab
    have hAV : A ≤ Subgroup.normalizer (V : Set X) := by
      rw [Subgroup.normalizer_eq_top V]
      exact le_top
    have hVNA : ¬ V ≤ Subgroup.normalizer (A : Set X) := fun h =>
      hcomm_ne (commutator_commutator_eq_bot hAab h)
    obtain ⟨A', hA'S, hA'com, hA'card, -, hA'N, hA'lt⟩ :=
      Work.PGroup.thompson_replacement hp hpne (S : Subgroup X) A V hS hAS hAcom hAcard hVS hVcom
        hAV hVNA
    have hA'max : IsMaxAbelianSubgroup (S : Subgroup X) A' :=
      (isMaxAbelianSubgroup_iff (S : Subgroup X) A').mpr
        ⟨hA'S, (isAbelianSubgroup_iff_isMulCommutative A').mpr hA'com, hA'card⟩
    have hA'comm : ⁅⁅A', A⁆, A⁆ = ⊥ := commutator_commutator_eq_bot hAab hA'N
    have hcardlt : Nat.card ↥(A ⊓ V) < Nat.card ↥(A' ⊓ V) := by
      have hle : Nat.card ↥(A ⊓ V) ≤ Nat.card ↥(A' ⊓ V) := Subgroup.card_le_of_le hA'lt.le
      refine lt_of_le_of_ne hle ?_
      intro heq
      exact hA'lt.ne (Subgroup.eq_of_le_of_card_ge hA'lt.le heq.symm.le)
    have hdecr : Nat.card ↥V + 1 - Nat.card ↥(A' ⊓ V) < n := by
      rw [← heqn]
      exact Nat.sub_lt_sub_left
        (lt_of_le_of_lt (Subgroup.card_le_of_le (inf_le_right : A ⊓ V ≤ V))
          (Nat.lt_succ_self _)) hcardlt
    by_cases hA'L : A' ≤ L
    · -- `A' ≤ L`: contradicted by the replacement conclusion
      have hA'T : A' ≤ L ⊓ (S : Subgroup X) := le_inf hA'L hA'S
      have hA'Tmax : IsMaxAbelianSubgroup (L ⊓ (S : Subgroup X)) A' :=
        isMaxAbelianSubgroup_of_le hA'max hA'T inf_le_right
      have hZT_le : Submission.Blueprint.ZJ (L ⊓ (S : Subgroup X)) ≤ A' :=
        (lemma3_5_a (L ⊓ (S : Subgroup X)) (L ⊓ (S : Subgroup X)) A' hA'Tmax hA'T le_rfl).1
      have hle : ⁅⁅V, A⁆, A⁆ ≤ ⁅⁅A', A⁆, A⁆ :=
        Subgroup.commutator_mono (Subgroup.commutator_mono (hVZ.trans hZT_le) le_rfl) le_rfl
      rw [hA'comm] at hle
      exact hcomm_ne (le_bot_iff.mp hle)
    · exact hA'L (ih _ hdecr A' hA'max rfl)
  intro A hA
  exact key _ A hA rfl

end Work.GlaubermanZJ
