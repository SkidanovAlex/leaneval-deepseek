import Mathlib
import Submission.Work.Reductions.Defs
import Submission.Work.Reductions.stronglyEmbedded_centralizer_le

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Reductions

/-! ## Conjugation calculus for `Submission.Blueprint.conj`

`conj g H = g H g⁻¹ = H.map (MulAut.conj g)` is the conjugate of `H` used by
`IsStronglyEmbedded`.  We collect the elementary identities needed to see that strong
embeddedness and the "centralizer of an involution stays inside" property are invariant
under conjugation. -/

section ConjCalculus

variable {G : Type} [Group G]

/-- Conjugating by `b` and then by `a` is conjugating by `a * b`. -/
private theorem conj_map_mul (a b : G) (H : Subgroup G) :
    Submission.Blueprint.conj a (Submission.Blueprint.conj b H) =
      Submission.Blueprint.conj (a * b) H := by
  rw [Submission.Blueprint.conj, Submission.Blueprint.conj, Submission.Blueprint.conj,
    Subgroup.map_map]
  congr 1
  ext y
  simp [MulAut.conj_apply, mul_assoc]

/-- Conjugation distributes over intersections. -/
private theorem conj_map_inf (g : G) (H K : Subgroup G) :
    Submission.Blueprint.conj g (H ⊓ K) =
      Submission.Blueprint.conj g H ⊓ Submission.Blueprint.conj g K := by
  rw [Submission.Blueprint.conj, Submission.Blueprint.conj, Submission.Blueprint.conj,
    Subgroup.map_inf _ _ _ (MulAut.conj g).injective]

/-- Conjugation preserves cardinalities. -/
private theorem card_conj_map (g : G) (H : Subgroup G) :
    Nat.card (Submission.Blueprint.conj g H) = Nat.card H := by
  rw [Submission.Blueprint.conj]
  exact Subgroup.card_map_of_injective (MulAut.conj g).injective

/-- Membership in a conjugate, unwound: `x ∈ g H g⁻¹ ↔ g⁻¹ x g ∈ H`. -/
private theorem mem_conj_map_iff (g x : G) (H : Subgroup G) :
    x ∈ Submission.Blueprint.conj g H ↔ g⁻¹ * x * g ∈ H := by
  rw [Submission.Blueprint.conj, Subgroup.mem_map]
  constructor
  · rintro ⟨h, hh, hhx⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hhx
    have : g⁻¹ * x * g = h := by rw [← hhx]; group
    rw [this]; exact hh
  · intro hx
    refine ⟨g⁻¹ * x * g, hx, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group

end ConjCalculus

/-- Strong embeddedness is invariant under conjugation, and an involution inside a conjugate
of a strongly embedded subgroup has its centralizer inside that conjugate. -/
theorem stronglyEmbedded_conj {G : Type} [Group G] {H : Subgroup G} (g : G)
    (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) :
    LeanEval.GroupTheory.Defs.IsStronglyEmbedded (Submission.Blueprint.conj g H) ∧
      (∀ t : G, t ∈ Submission.Blueprint.conj g H → orderOf t = 2 →
        Subgroup.centralizer ({t} : Set G) ≤ Submission.Blueprint.conj g H) := by
  obtain ⟨hne, heven, hodd⟩ := hH
  have hconj : LeanEval.GroupTheory.Defs.IsStronglyEmbedded (Submission.Blueprint.conj g H) := by
    refine ⟨?_, ?_, ?_⟩
    · -- properness: conjugating back gives `H = ⊤`
      intro htop
      apply hne
      rw [eq_top_iff]
      intro h _
      have h2 : g * h * g⁻¹ ∈ Submission.Blueprint.conj g H := by rw [htop]; trivial
      rw [mem_conj_map_iff] at h2
      have h3 : g⁻¹ * (g * h * g⁻¹) * g = h := by group
      rwa [h3] at h2
    · -- even order is preserved
      rw [card_conj_map]; exact heven
    · -- the odd-order intersection condition transports across conjugation
      intro x hx
      have hx' : g⁻¹ * x * g ∉ H := fun h => hx ((mem_conj_map_iff g x H).mpr h)
      have hodd' := hodd (g⁻¹ * x * g) hx'
      have heq : Submission.Blueprint.conj g H ⊓ Submission.Blueprint.conj x
            (Submission.Blueprint.conj g H) =
          Submission.Blueprint.conj g
            (H ⊓ Submission.Blueprint.conj (g⁻¹ * x * g) H) := by
        have h1 : Submission.Blueprint.conj x (Submission.Blueprint.conj g H) =
            Submission.Blueprint.conj g (Submission.Blueprint.conj (g⁻¹ * x * g) H) := by
          rw [conj_map_mul x g, conj_map_mul g (g⁻¹ * x * g)]
          congr 1
          group
        rw [h1, ← conj_map_inf g H (Submission.Blueprint.conj (g⁻¹ * x * g) H)]
      rw [heq, card_conj_map]
      exact hodd'
  refine ⟨hconj, ?_⟩
  intro t ht h2
  exact stronglyEmbedded_centralizer_le hconj ht h2

end Work.Reductions
