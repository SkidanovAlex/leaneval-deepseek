import Mathlib
import Submission.Work.ZassenhausTwoGroup.Defs
import Submission.Work.Fitting.piCore_inf_eq_bot_of_coprime

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `twoPart_commute_oddPart`

For a finite group `Q` the `2`-core `O_2(Q)` and the `2'`-core `O_{2'}(Q)` commute elementwise;
applied to a subgroup `Q ≤ G` this says that the elements of

  `twoPart Q = O_2(Q)`   (the Sylow `2`-subgroup of `Q` when `Q` is nilpotent)

commute with those of

  `oddPart Q = O_{2'}(Q)`.

The mathematical content is one line: `O_π(G)` and `O_σ(G)` are normal in `G` for *any* two
predicates `π`, `σ`, so the commutator `⁅a, b⁆` of `a ∈ O_π(G)`, `b ∈ O_σ(G)` lies in both cores,
hence in `O_π(G) ⊓ O_σ(G)`; and that intersection is trivial as soon as `π` and `σ` are disjoint
(`Work.Fitting.piCore_inf_eq_bot_of_coprime`), because then no prime can divide both `|O_π(G)|`
and `|O_σ(G)|`.  So `⁅a, b⁆ = 1`.

In particular the argument never uses nilpotency of `Q` (nor primality of `2`): the hypothesis
`h : Group.IsNilpotent Q` in the statement below is simply carried along.  Nilpotency *is* what
makes `twoPart Q` and `oddPart Q` the two direct factors of `Q`
(`twoPart_sup_oddPart`), which is the shape in which the decomposition is used elsewhere in this
area.
-/

open scoped commutatorElement

namespace Work.ZassenhausTwoGroup

open Work.Fitting

/-- Two normal subgroups of a group with trivial intersection commute elementwise: the commutator
of `a ∈ H` and `b ∈ K` lies in `⁅H, K⁆ ≤ H ⊓ K = ⊥`. -/
theorem commute_of_inf_eq_bot {G : Type} [Group G] {H K : Subgroup G} [H.Normal] [K.Normal]
    (h : H ⊓ K = ⊥) : ∀ a ∈ H, ∀ b ∈ K, a * b = b * a := by
  intro a ha b hb
  have hmem : ⁅a, b⁆ ∈ H ⊓ K :=
    ⟨Subgroup.commutator_le_left H K (Subgroup.commutator_mem_commutator ha hb),
     Subgroup.commutator_le_right H K (Subgroup.commutator_mem_commutator ha hb)⟩
  exact commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp (h ▸ hmem))

/-- Elements of `O_π(G)` and `O_σ(G)` commute when `π` and `σ` are disjoint (in particular for
`π = (· = p)`, `σ = (· ≠ p)`: the `p`-core and the `p'`-core of a finite group commute). -/
theorem commute_of_mem_piCore_of_disjoint {G : Type} [Group G] [Finite G] (π σ : ℕ → Prop)
    (hdisj : ∀ p, π p → σ p → False) :
    ∀ a ∈ piCore π G, ∀ b ∈ piCore σ G, a * b = b * a :=
  commute_of_inf_eq_bot (H := piCore π G) (K := piCore σ G)
    (piCore_inf_eq_bot_of_coprime π σ G hdisj)

theorem twoPart_commute_oddPart {G : Type} [Group G] [Finite G] {Q : Subgroup G}
    (h : Group.IsNilpotent Q) :
    ∀ a ∈ Work.ZassenhausTwoGroup.twoPart Q, ∀ b ∈ Work.ZassenhausTwoGroup.oddPart Q,
      a * b = b * a := by
  intro a ha b hb
  -- `a` and `b` are the images in `G` of elements of the two cores of the group `Q`.
  rw [twoPart, Subgroup.mem_map] at ha
  obtain ⟨a', ha', rfl⟩ := ha
  rw [oddPart, Subgroup.mem_map] at hb
  obtain ⟨b', hb', rfl⟩ := hb
  -- Inside `Q`, the `2`-core and the `2'`-core commute, and `Q.subtype` is multiplicative.
  exact congrArg (fun z : ↥Q => (z : G))
    (commute_of_mem_piCore_of_disjoint (fun q => q = 2) (fun q => q ≠ 2)
      (fun _ hp hp' => hp' hp) a' ha' b' hb')

end Work.ZassenhausTwoGroup
