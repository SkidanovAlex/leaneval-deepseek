import Mathlib
import Submission.Work.Models.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped Pointwise

namespace Work.ZassenhausSuzuki.Odd

/-- The `g`-conjugate `A.map (MulAut.conj g)` is the image of `A` under the conjugation
action of `ConjAct G`. -/
lemma conj_eq_conjAct_smul {G : Type} [Group G] {A : Subgroup G} (g : G) :
    Submission.Blueprint.conj g A = ConjAct.toConjAct g • A := by
  rw [Subgroup.pointwise_smul_def, Submission.Blueprint.conj]
  congr 1

/-- The set of conjugates of `A` is the orbit of `A` under the conjugation action of
`ConjAct G`. -/
lemma range_conj_eq_orbit {G : Type} [Group G] {A : Subgroup G} :
    Set.range (fun g : G => Submission.Blueprint.conj g A) =
      MulAction.orbit (ConjAct G) A := by
  have hsmul : ∀ g : G, Submission.Blueprint.conj g A = ConjAct.toConjAct g • A :=
    fun g => conj_eq_conjAct_smul g
  have hsmul' : ∀ c : ConjAct G,
      Submission.Blueprint.conj (ConjAct.ofConjAct c) A = c • A := by
    intro c
    rw [hsmul, ConjAct.toConjAct_ofConjAct]
  ext x
  constructor
  · rintro ⟨g, hg⟩
    change Submission.Blueprint.conj g A = x at hg
    rw [← hg, hsmul]
    exact MulAction.mem_orbit _ _
  · intro hx
    rw [MulAction.mem_orbit_iff] at hx
    obtain ⟨c, hc⟩ := hx
    refine ⟨ConjAct.ofConjAct c, ?_⟩
    show Submission.Blueprint.conj (ConjAct.ofConjAct c) A = x
    rw [hsmul', hc]

/-- The stabiliser of `A` under the conjugation action is the normaliser of `A`. -/
lemma stabilizer_conjAct_eq_comap_normalizer {G : Type} [Group G] {A : Subgroup G} :
    MulAction.stabilizer (ConjAct G) A =
      (Subgroup.normalizer (A : Set G)).comap
        ((ConjAct.ofConjAct : ConjAct G ≃* G).toMonoidHom) := by
  ext c
  rw [MulAction.mem_stabilizer_iff, Subgroup.mem_comap]
  change c • A = A ↔ ConjAct.ofConjAct c ∈ Subgroup.normalizer (A : Set G)
  nth_rewrite 1 [← ConjAct.toConjAct_ofConjAct c]
  rw [Subgroup.conjAct_pointwise_smul_iff]

theorem card_range_conj_eq_index_normalizer {G : Type} [Group G] {A : Subgroup G} :
    Nat.card (Set.range (fun g : G => Submission.Blueprint.conj g A)) =
      (Subgroup.normalizer (A : Set G)).index := by
  rw [range_conj_eq_orbit, Nat.card_coe_set_eq, ← MulAction.index_stabilizer (ConjAct G) A,
    stabilizer_conjAct_eq_comap_normalizer,
    Subgroup.index_comap_of_surjective _ (ConjAct.ofConjAct : ConjAct G ≃* G).surjective]

end Work.ZassenhausSuzuki.Odd
