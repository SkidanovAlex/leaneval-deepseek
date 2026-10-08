import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Hering.AppVII

/-- If `Q` is a normal subgroup of a finite group `H` and `P` is a complement of `Q`
(with `P ⊓ Q = ⊥` and `P ⊔ Q = ⊤`) of prime order `p`, then `H ⧸ Q` is cyclic of order `p`.

Indeed `P` and `Q` are complementary subgroups, so `H ⧸ Q ≃* P`; the quotient therefore
has order `|P| = p`, and a group of prime order is cyclic. -/
theorem part2_quotient_cyclic {H : Type*} [Group H] [Fintype H] {p : ℕ} (Q P : Subgroup H)
    (hQn : Q.Normal) (hinf : P ⊓ Q = ⊥) (hsup : P ⊔ Q = ⊤) (hp : p.Prime)
    (hPcard : Nat.card ↥P = p) : IsCyclic (H ⧸ Q) ∧ Nat.card (H ⧸ Q) = p := by
  have hQn' : Q.Normal := hQn
  -- `P` and `Q` are complementary: they meet trivially and their product is everything.
  have hcomp : P.IsComplement' Q := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · rw [disjoint_iff_inf_le, hinf]
    · -- Since `Q` is normal, `↑(P ⊔ Q) = ↑P * ↑Q`, and `P ⊔ Q = ⊤`.
      rw [← Subgroup.mul_normal P Q, hsup]
      rfl
  -- The quotient `H ⧸ Q` is (multiplicatively) isomorphic to `P`.
  have e := hcomp.QuotientMulEquiv
  have hcard : Nat.card (H ⧸ Q) = p := by
    rw [← hPcard]
    exact Nat.card_congr e.toEquiv
  refine ⟨?_, hcard⟩
  have : Fact p.Prime := ⟨hp⟩
  exact isCyclic_of_prime_card hcard

end Work.Hering.AppVII
