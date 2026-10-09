import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Torsor.Defs
import Mathlib.GroupTheory.Sylow
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.GroupTheory

/-- For a finite commutative group `G` and a prime `p`, there is a subgroup `H ≤ G` whose quotient is a `p`-group of order the `p`-part `p ^ (Nat.card G).factorization p` of `#G`; namely `H` is the range of the endomorphism `g ↦ g ^ (p ^ v)` where `p ^ v` is the `p`-part of `#G`. -/
theorem exists_subgroup_card_quotient_eq_pow_factorization {G : Type*} [CommGroup G] [Fintype G]
    {p : ℕ} [Fact p.Prime] :
    ∃ H : Subgroup G, Nat.card (G ⧸ H) = p ^ (Nat.card G).factorization p := by
  classical
  set v : ℕ := (Nat.card G).factorization p with hv
  let f : G →* G := powMonoidHom (p ^ v)
  refine ⟨f.range, ?_⟩
  -- The quotient by the range has the same cardinality as the kernel of the power map.
  have hquo : Nat.card (G ⧸ f.range) = Nat.card f.ker := by
    have e1 : Nat.card G = Nat.card (G ⧸ f.range) * Nat.card f.range :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup f.range
    have e2 : Nat.card f.ker * Nat.card f.range = Nat.card G := by
      rw [← Subgroup.index_ker f]
      exact Subgroup.card_mul_index f.ker
    have hpos : Nat.card f.range ≠ 0 := (Nat.card_pos (α := f.range)).ne'
    rw [← e2] at e1
    exact (mul_right_cancel₀ hpos e1).symm
  rw [hquo]
  -- It remains to show the kernel has cardinality `p ^ v`.
  have hpg : IsPGroup p f.ker := by
    intro x
    refine ⟨v, ?_⟩
    apply Subtype.ext
    have hx : f ↑x = 1 := MonoidHom.mem_ker.mp x.2
    simp only [Subgroup.coe_pow, OneMemClass.coe_one]
    simpa [f, powMonoidHom_apply] using hx
  have hker : Nat.card f.ker = p ^ v := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hpg
    -- Upper bound: `k ≤ v`.
    have hkle : k ≤ v := by
      have hdvd : p ^ k ∣ Nat.card G := by
        rw [← hk]
        exact Subgroup.card_subgroup_dvd_card f.ker
      have hfac : (p ^ k).factorization ≤ (Nat.card G).factorization :=
        (Nat.factorization_le_iff_dvd (pow_ne_zero k (Fact.out : p.Prime).ne_zero)
          (Nat.card_pos (α := G)).ne').mpr hdvd
      have := hfac p
      rwa [Nat.factorization_pow_self (Fact.out : p.Prime), ← hv] at this
    -- Lower bound: `p ^ v ≤ p ^ k`.
    have hlow : p ^ v ≤ p ^ k := by
      let P : Sylow p G := Classical.arbitrary (Sylow p G)
      have hPcard : Nat.card (P : Subgroup G) = p ^ v := by
        have h := Sylow.card_eq_multiplicity P
        rw [← hv] at h
        simpa using h
      have hPle : (P : Subgroup G) ≤ f.ker := by
        intro x hx
        rw [MonoidHom.mem_ker]
        have hxdvd : orderOf x ∣ p ^ v := by
          rw [← hPcard]
          exact Subgroup.orderOf_dvd_natCard (P : Subgroup G) hx
        have hxpow : x ^ (p ^ v) = 1 := orderOf_dvd_iff_pow_eq_one.mp hxdvd
        simpa [f, powMonoidHom_apply] using hxpow
      have hle := Subgroup.card_le_of_le hPle
      rw [hPcard, hk] at hle
      exact hle
    have hvk : v ≤ k := (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp hlow
    rw [hk, le_antisymm hkle hvk]
  exact hker

end Commons.GroupTheory