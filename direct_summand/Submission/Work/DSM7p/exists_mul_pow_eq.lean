import Mathlib
import Submission.Work.DSM7p.Basic
import Submission.Work.DSM7p.pow_pow_eq_of_root
import Submission.Work.DSM7p.three_mul_le_two_mul_pow

namespace Work.DSM7p

universe a

/-- **The exponent computation of the Krull step.**  `B` is an `A`-algebra, `Q : PerfectoidData p B` (so `Q.ϖ` has compatible `p`-power roots and `(Q.ϖ 0)^p = p · v` for a unit `v : Bˣ`), and `gr : ℕ → B` is a compatible system of `p`-power roots of `g : A` (`gr 0 = algebraMap A B g`, `(gr (k+1))^p = gr k`).  If `2 * K ≤ p ^ K`, then the `K`-th power of the almost-element `(Q.ϖ K)^3 * (gr K)^2` divides `algebraMap A B (p^2 * g)`, up to a unit.

The explicit witness is `c = (Q.ϖ K)^(2 * p^(K+1) - 3*K) * (gr K)^(p^K - 2*K) * (↑v⁻¹)^2`: its exponents are nonnegative because `2*K ≤ p^K` gives `3*K ≤ 2*p^K ≤ 2*p^(K+1)` and `2*K ≤ p^K`; and the product is `(Q.ϖ K)^(2*p^(K+1)) * (gr K)^(p^K) * v^{-2} = (Q.ϖ 0)^(2p) * algebraMap g * v^{-2} = (p * v)^2 * algebraMap g * v^{-2} = algebraMap (p^2 * g)` using `(Q.ϖ K)^(p^K) = Q.ϖ 0`, `(gr K)^(p^K) = gr 0`, `2*p^(K+1) = 2*p*p^K` and `v * v^{-1} = 1`. -/
theorem exists_mul_pow_eq {A B : Type a} [CommRing A] [CommRing B] [Algebra A B]
    (p : ℕ) [Fact p.Prime] (Q : DSMap.PerfectoidData p B) (g : A) (gr : ℕ → B)
    (hgr0 : gr 0 = algebraMap A B g) (hgr : ∀ k, gr (k + 1) ^ p = gr k)
    (K : ℕ) (hK : 2 * K ≤ p ^ K) :
    ∃ c : B, ((Q.ϖ K) ^ 3 * (gr K) ^ 2) ^ K * c = algebraMap A B ((p : A) ^ 2 * g) := by
  obtain ⟨v, hv⟩ := Q.unit
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  -- the `p ^ K`-th powers of the two compatible root systems return to level `0`
  have hϖ : (Q.ϖ K) ^ (p ^ K) = Q.ϖ 0 := pow_pow_eq_of_root _ Q.root K
  have hg : (gr K) ^ (p ^ K) = gr 0 := pow_pow_eq_of_root _ hgr K
  -- the exponent inequality making the witness's exponents nonnegative
  have h1 : 3 * K ≤ 2 * p ^ (K + 1) := three_mul_le_two_mul_pow p K hp2 hK
  -- `2 * p ^ (K+1) = p ^ K * (2 * p)` collects the `p ^ K`-th powers
  have h2p : 2 * p ^ (K + 1) = p ^ K * (2 * p) := by rw [pow_succ]; ring
  -- the unit contributes `1`
  have hvu : ((v : B)) ^ 2 * ((↑(v⁻¹) : B)) ^ 2 = 1 := by
    rw [← mul_pow, Units.mul_inv, one_pow]
  -- unfolding the `K`-th power of the almost element
  have hL : ((Q.ϖ K) ^ 3 * (gr K) ^ 2) ^ K = (Q.ϖ K) ^ (3 * K) * (gr K) ^ (2 * K) := by
    rw [mul_pow, ← pow_mul, ← pow_mul]
  have hR : algebraMap A B ((p : A) ^ 2 * g) = (p : B) ^ 2 * algebraMap A B g := by
    rw [map_mul, map_pow, map_natCast]
  refine ⟨(Q.ϖ K) ^ (2 * p ^ (K + 1) - 3 * K) * (gr K) ^ (p ^ K - 2 * K) *
    ((↑(v⁻¹) : B)) ^ 2, ?_⟩
  rw [hL, hR]
  calc (Q.ϖ K) ^ (3 * K) * (gr K) ^ (2 * K) *
        ((Q.ϖ K) ^ (2 * p ^ (K + 1) - 3 * K) * (gr K) ^ (p ^ K - 2 * K) * ((↑(v⁻¹) : B)) ^ 2)
      = (Q.ϖ K) ^ (3 * K) * (Q.ϖ K) ^ (2 * p ^ (K + 1) - 3 * K) *
          ((gr K) ^ (2 * K) * (gr K) ^ (p ^ K - 2 * K)) * ((↑(v⁻¹) : B)) ^ 2 := by ring
    _ = (Q.ϖ K) ^ (3 * K + (2 * p ^ (K + 1) - 3 * K)) *
          (gr K) ^ (2 * K + (p ^ K - 2 * K)) * ((↑(v⁻¹) : B)) ^ 2 := by
          rw [← pow_add, ← pow_add]
    _ = (Q.ϖ K) ^ (2 * p ^ (K + 1)) * (gr K) ^ (p ^ K) * ((↑(v⁻¹) : B)) ^ 2 := by
          rw [Nat.add_sub_of_le h1, Nat.add_sub_of_le hK]
    _ = (p : B) ^ 2 * ((v : B)) ^ 2 * (gr K) ^ (p ^ K) * ((↑(v⁻¹) : B)) ^ 2 := by
          rw [h2p, pow_mul, hϖ, pow_mul', hv, mul_pow]
    _ = (p : B) ^ 2 * (gr K) ^ (p ^ K) * (((v : B)) ^ 2 * ((↑(v⁻¹) : B)) ^ 2) := by ring
    _ = (p : B) ^ 2 * (gr K) ^ (p ^ K) * 1 := by rw [hvu]
    _ = (p : B) ^ 2 * algebraMap A B g := by rw [hg, hgr0]; ring

end Work.DSM7p
