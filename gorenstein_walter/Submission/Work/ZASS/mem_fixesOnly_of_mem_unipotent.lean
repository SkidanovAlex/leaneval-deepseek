import Mathlib
import Submission.Work.ZASS.Defs
import Submission.Work.Zassenhaus.Basic
import Submission.Work.Zassenhaus.zass_coprime_pow_half

namespace Work.ZASS

open Work.Zassenhaus

/-- `p ^ k` and `(p ^ k - 1) / 2` are coprime for odd `p`, with no condition on `k`.

For `k = 0` both statements degenerate (`p ^ 0 = 1` and `(1 - 1) / 2 = 0`), and `1` is coprime
to everything; for `1 ≤ k` this is `Work.Zassenhaus.zass_coprime_pow_half`. -/
private theorem coprime_pow_half_of_odd {p k : ℕ} (hp : Nat.Prime p) (hpodd : Odd p) :
    Nat.Coprime (p ^ k) ((p ^ k - 1) / 2) := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    simp
  · exact Work.Zassenhaus.zass_coprime_pow_half hp hpodd hk

/-- **Z2 (blueprint §ZASS).** Every nonidentity element of a subgroup `U ≤ B` of order
`p ^ k` fixes only `∞` (REVISED after review: the order of the two-point stabilizer must be
known at every point, not just one).  If `u • y = y` for some `y ≠ ∞`, then `u` lies in the
two-point stabilizer `G_{∞y}`, of order `(q-1)/2`, so `orderOf u` divides both `p^k` and
`(q-1)/2`, which are coprime (`Work.Zassenhaus.zass_coprime_pow_half`); hence `u = 1`. -/
theorem mem_fixesOnly_of_mem_unipotent {G X : Type} [Group G] [Finite G] [MulAction G X]
    {p k : ℕ} [Fact p.Prime] (hp : Odd p) {q : ℕ} (hq : q = p ^ k) {inf : X}
    {U : Subgroup G} (hUB : U ≤ Work.Zassenhaus.borel G inf) (hcardU : Nat.card U = p ^ k)
    (hcardH : ∀ y : X, y ≠ inf →
      Nat.card (Work.Zassenhaus.pairStab G inf y) = (q - 1) / 2)
    {u : G} (hu : u ∈ U) (hu1 : u ≠ 1) : u ∈ Work.Zassenhaus.fixesOnly G inf := by
  rw [Work.Zassenhaus.mem_fixesOnly_iff]
  refine ⟨hUB hu, ?_⟩
  intro y hy hyu
  -- `u` lies in the two-point stabilizer `G_{∞y}`
  have hyStab : u ∈ Work.Zassenhaus.pairStab G inf y := by
    rw [Work.Zassenhaus.mem_pairStab_iff]
    exact ⟨hyu, Work.Zassenhaus.mem_borel_iff.mp (hUB hu)⟩
  -- `orderOf u` divides `|U| = p ^ k`
  have hdvdU : orderOf u ∣ p ^ k := by
    rw [← hcardU]
    exact Subgroup.orderOf_dvd_natCard U hu
  -- `orderOf u` divides `|G_{∞y}| = (p ^ k - 1) / 2`
  have hq' : (q - 1) / 2 = (p ^ k - 1) / 2 := by rw [hq]
  have hdvdH : orderOf u ∣ (p ^ k - 1) / 2 := by
    rw [← hq', ← hcardH y hy]
    exact Subgroup.orderOf_dvd_natCard _ hyStab
  -- the two orders are coprime, so `orderOf u = 1`
  have hcop : Nat.Coprime (p ^ k) ((p ^ k - 1) / 2) :=
    coprime_pow_half_of_odd Fact.out hp
  exact hu1 (orderOf_eq_one_iff.mp ((Nat.Coprime.coprime_dvd_left hdvdU hcop).eq_one_of_dvd hdvdH))

end Work.ZASS
