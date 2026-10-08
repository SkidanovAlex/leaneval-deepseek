import Mathlib
import Submission.Work.Models.Port.BenderPairModels
import Submission.Work.PSU3.BenderST

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.PSU3.BST.card_twoPoint_of_twoTransitive`

For a finite group `G` acting `2`-transitively on the cosets of `B`, the two-point
stabiliser `D = B ⊓ B^w` of the pair `(B, wB)` satisfies `|D| · |U| = |B|`, where `U` is any
group with `|U| = [G : B] - 1`.

This is orbit–stabiliser for the action of `G` on ordered pairs of distinct cosets: the number of
such pairs is `n (n - 1)` with `n = [G : B] = |G ⧸ B|`, the action is transitive on them
(`h2`), so `|G| = n (n - 1) · |D|`; on the other hand `|G| = n · |B|`.  Cancelling `n` and using
`n - 1 = |U|` (which is `hind` read through `Subgroup.index_eq_card`) gives the claim.

The two elementary ingredients (the number of ordered pairs of distinct points of a finite type,
and the description of the stabiliser of a pair of distinct points as the intersection of the two
point stabilisers) are proved first.
-/

namespace Work.PSU3.BST

/-- **Orbit–stabiliser**, in `Nat.card` form: for a group `G` acting on a type `X` and a point
`x : X`, the product of the cardinalities of the orbit and of the stabiliser of `x` is `|G|`. -/
theorem natCard_orbit_mul_natCard_stabilizer {G X : Type*} [Group G] [MulAction G X] (x : X) :
    Nat.card (MulAction.orbit G x) * Nat.card (MulAction.stabilizer G x) = Nat.card G := by
  rw [← Nat.card_prod]
  exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup G x)

/-- The number of ordered pairs of distinct points of a finite type `α` is
`|α| (|α| - 1)`. -/
theorem card_embedding_fin_two {α : Type*} [Finite α] :
    Nat.card (Fin 2 ↪ α) = Nat.card α * (Nat.card α - 1) := by
  have : Fintype α := Fintype.ofFinite α
  rw [Nat.card_eq_fintype_card, Fintype.card_embedding_eq, Fintype.card_fin]
  rw [← Nat.card_eq_fintype_card]
  rw [Nat.descFactorial_succ, Nat.descFactorial_one]
  ring

/-- The stabiliser of a pair of distinct points is the intersection of the two point
stabilisers: an element fixes the pair `(a, b)` iff it fixes `a` and fixes `b`. -/
theorem stabilizer_embFinTwo_eq_inf {G α : Type*} [Group G] [MulAction G α] {a b : α}
    (hab : a ≠ b) :
    MulAction.stabilizer G (Function.Embedding.embFinTwo hab) =
      MulAction.stabilizer G a ⊓ MulAction.stabilizer G b := by
  ext g
  rw [Subgroup.mem_inf, MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff,
    MulAction.mem_stabilizer_iff]
  constructor
  · intro h
    exact ⟨by simpa [Function.Embedding.embFinTwo_apply_zero]
        using congrArg (fun f : Fin 2 ↪ α => f 0) h,
      by simpa [Function.Embedding.embFinTwo_apply_one]
        using congrArg (fun f : Fin 2 ↪ α => f 1) h⟩
  · rintro ⟨h0, h1⟩
    ext i
    fin_cases i
    · simpa [Function.Embedding.embFinTwo_apply_zero] using h0
    · simpa [Function.Embedding.embFinTwo_apply_one] using h1

/-- **Two-point orbit–stabiliser count.**  If a finite group `G` acts `2`-transitively on the
cosets of `B`, then the two-point stabiliser `D = B ⊓ B^w` of the pair `(B, wB)` (with `w ∉ B`)
satisfies `|D| · |U| = |B|` for any group `U` with `|U| = [G : B] - 1`. -/
theorem card_twoPoint_of_twoTransitive {G : Type} [Group G] [Finite G] (B U : Subgroup G) (w : G)
    (h2 : MulAction.IsMultiplyPretransitive G (G ⧸ B) 2)
    (hind : B.index = Nat.card ↥U + 1) (hw : w ∉ B) :
    Nat.card ↥(Submission.Blueprint.twoPoint B w) * Nat.card ↥U = Nat.card ↥B := by
  classical
  -- The base point of the coset space, whose stabiliser is `B`.
  let pt : G ⧸ B := ((1 : G) : G ⧸ B)
  have hstab_pt : MulAction.stabilizer G pt = B := MulAction.stabilizer_quotient B
  -- `w ∉ B` means that `w` moves the base point.
  have hnew : pt ≠ w • pt := by
    intro h
    refine hw ?_
    have hmem : w ∈ MulAction.stabilizer G pt := by
      rw [MulAction.mem_stabilizer_iff]
      exact h.symm
    rwa [hstab_pt] at hmem
  -- The pair `(pt, w • pt)` as an embedding `Fin 2 ↪ G ⧸ B`.
  let e : Fin 2 ↪ (G ⧸ B) := Function.Embedding.embFinTwo hnew
  -- Orbit–stabiliser for the action of `G` on the pairs.
  have hcard_os : Nat.card (MulAction.orbit G e) * Nat.card (MulAction.stabilizer G e) =
      Nat.card G := natCard_orbit_mul_natCard_stabilizer e
  -- `G` is transitive on ordered pairs of distinct points, so the orbit is everything.
  have horbit : MulAction.orbit G e = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro x
    rw [MulAction.mem_orbit_iff]
    exact h2.exists_smul_eq e x
  -- Hence the orbit has `n (n - 1)` elements, `n = |G ⧸ B|`.
  have hcard_orb : Nat.card (MulAction.orbit G e) =
      Nat.card (G ⧸ B) * (Nat.card (G ⧸ B) - 1) := by
    rw [horbit, Nat.card_congr (Equiv.Set.univ (Fin 2 ↪ (G ⧸ B)))]
    exact card_embedding_fin_two
  -- The stabiliser of the pair `(pt, w • pt)` is the two-point stabiliser `B ⊓ B^w`.
  have hstab_e : MulAction.stabilizer G e = Submission.Blueprint.twoPoint B w := by
    rw [show e = Function.Embedding.embFinTwo hnew from rfl, stabilizer_embFinTwo_eq_inf hnew,
      hstab_pt, MulAction.stabilizer_smul_eq_stabilizer_map_conj, hstab_pt]
  -- `|G| = |G ⧸ B| · |B|`.
  have hG : Nat.card G = Nat.card (G ⧸ B) * Nat.card ↥B := by
    rw [← Subgroup.card_mul_index B, Subgroup.index_eq_card, Nat.mul_comm]
  -- Combining the two orbit–stabiliser computations: `n (n - 1) |D| = n |B|`.
  have key : (Nat.card (G ⧸ B) * (Nat.card (G ⧸ B) - 1)) *
      Nat.card ↥(Submission.Blueprint.twoPoint B w) = Nat.card (G ⧸ B) * Nat.card ↥B := by
    rw [← hcard_orb, ← hstab_e, hcard_os]
    exact hG
  -- Cancel `n = |G ⧸ B| > 0`.
  have hnpos : 0 < Nat.card (G ⧸ B) := Nat.card_pos
  have hcancel : (Nat.card (G ⧸ B) - 1) * Nat.card ↥(Submission.Blueprint.twoPoint B w) =
      Nat.card ↥B := by
    refine Nat.mul_left_cancel hnpos ?_
    rw [← mul_assoc]
    exact key
  -- `n - 1 = |U|` is exactly `hind`.
  have hU : Nat.card (G ⧸ B) - 1 = Nat.card ↥U := by
    rw [← Subgroup.index_eq_card B, hind, Nat.add_sub_cancel]
  rw [← hU, mul_comm (Nat.card ↥(Submission.Blueprint.twoPoint B w)) (Nat.card (G ⧸ B) - 1)]
  exact hcancel

end Work.PSU3.BST
