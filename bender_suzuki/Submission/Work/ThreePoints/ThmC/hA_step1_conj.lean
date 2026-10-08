import Mathlib
import Submission.Work.ThreePoints.ThmC.Defs
import Submission.Work.ThreePoints.ThmC.pPrimeCoreSub_conj
import Submission.Work.ThreePoints.Omega

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThreePoints.ThmC

open Submission.Blueprint

/-- Conjugation does not change the order of a `p'`-core: if `Y = X^g` then
`O_{p'}(Y)` is the conjugate `O_{p'}(X)^g` of `O_{p'}(X)` (`pPrimeCoreSub_conj`), and
conjugation is injective on `G`. -/
theorem natCard_pPrimeCoreSub_conj {G : Type} [Group G] [Finite G] (p : ℕ) (hp : p.Prime)
    (X : Subgroup G) (g : G) :
    Nat.card (Work.ThreePoints.ThmC.pPrimeCoreSub p (Submission.Blueprint.conj g X)) =
      Nat.card (Work.ThreePoints.ThmC.pPrimeCoreSub p X) := by
  rw [Work.ThreePoints.ThmC.pPrimeCoreSub_conj p hp X g,
    Subgroup.card_map_of_injective (MulAut.conj g).injective]

/-- **Peterfalvi I Ch. II §3, Step 1: the conjugation bookkeeping.**

Let `G` act `2`-transitively on `Ω = G ⧸ H`, let `t ∉ H`, and let `u` be such that the
conjugates `H^t` and `H^{ut}` are distinct — equivalently the points `tH` and `utH` of `Ω` are
distinct.  Then the two-point stabiliser `H^t ⊓ H^{ut}` of the pair `{tH, utH}` is conjugate to
the two-point stabiliser `twoPoint H t = H ⊓ H^t` of the pair `{H, tH}`: `2`-transitivity moves
one ordered pair of distinct points to the other, and conjugating a stabiliser by the group
element produced gives the stabiliser of the image point.  Since the order of `O_{p'}(X)` is a
conjugation invariant (`natCard_pPrimeCoreSub_conj`), the two `p'`-cores have the same order. -/
theorem hA_step1_conj {G : Type} [Group G] [Finite G] {H : Subgroup G}
    (h2t : Submission.Blueprint.IsTwoTransitiveOn H)
    {t u : G} (htH : t ∉ H)
    (hne : Submission.Blueprint.conj t H ≠ Submission.Blueprint.conj (u * t) H)
    {p : ℕ} (hp : p.Prime) :
    Nat.card (Work.ThreePoints.ThmC.pPrimeCoreSub p
        (Submission.Blueprint.conj t H ⊓ Submission.Blueprint.conj (u * t) H)) =
      Nat.card (Work.ThreePoints.ThmC.pPrimeCoreSub p (Submission.Blueprint.twoPoint H t)) := by
  classical
  -- `tH` and `utH` are distinct points of `Ω`, since their stabilisers differ
  have hne_pt : (t : G ⧸ H) ≠ ((u * t : G) : G ⧸ H) := by
    intro h
    exact hne (by
      rw [← Work.ThreePoints.stabilizer_mk H t,
        ← Work.ThreePoints.stabilizer_mk H (u * t), h])
  -- the base point `H` and `tH` are distinct points of `Ω`, since `t ∉ H`
  have hne_base : ((1 : G) : G ⧸ H) ≠ (t : G ⧸ H) := by
    intro h
    have ht : t ∈ MulAction.stabilizer G ((1 : G) : G ⧸ H) := by
      rw [MulAction.mem_stabilizer_iff, Work.ThreePoints.smul_mk, mul_one]
      exact h.symm
    rw [Work.ThreePoints.stabilizer_mk, Work.ThreePoints.conj_one] at ht
    exact htH ht
  -- `2`-transitivity moves the ordered pair `(tH, utH)` to `(H, tH)`
  obtain ⟨g, hgt, hgut⟩ :=
    (MulAction.is_two_pretransitive_iff.mp h2t) hne_pt hne_base
  -- conjugation by `g` turns the stabiliser of `g • ω` into the stabiliser of `ω`
  have h1 : MulAction.stabilizer G (g • (t : G ⧸ H)) =
      Submission.Blueprint.conj g (Submission.Blueprint.conj t H) := by
    rw [← Work.ThreePoints.stabilizer_mk H t]
    exact MulAction.stabilizer_smul_eq_stabilizer_map_conj g (t : G ⧸ H)
  have h2 : MulAction.stabilizer G (g • ((u * t : G) : G ⧸ H)) =
      Submission.Blueprint.conj g (Submission.Blueprint.conj (u * t) H) := by
    rw [← Work.ThreePoints.stabilizer_mk H (u * t)]
    exact MulAction.stabilizer_smul_eq_stabilizer_map_conj g ((u * t : G) : G ⧸ H)
  -- hence `(H^t ⊓ H^{ut})^g = H ⊓ H^t`
  have hconj : Submission.Blueprint.conj g
      (Submission.Blueprint.conj t H ⊓ Submission.Blueprint.conj (u * t) H) =
      Submission.Blueprint.twoPoint H t := by
    rw [Work.ThreePoints.conj_inf, ← h1, ← h2, hgt, hgut,
      Work.ThreePoints.stabilizer_mk H t, Work.ThreePoints.stabilizer_mk H (1 : G),
      Work.ThreePoints.conj_one]
  have hkey : Submission.Blueprint.conj t H ⊓ Submission.Blueprint.conj (u * t) H =
      Submission.Blueprint.conj g⁻¹ (Submission.Blueprint.twoPoint H t) := by
    rw [← hconj, Work.DoubleTransitivity.conj_inv_conj]
  rw [hkey]
  exact natCard_pPrimeCoreSub_conj p hp (Submission.Blueprint.twoPoint H t) g⁻¹

end Work.ThreePoints.ThmC
