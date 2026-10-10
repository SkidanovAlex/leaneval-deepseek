import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Algebra.Order.Ring.Star
import Submission.Work.SSGRoute.Interfaces
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# An involution acts trivially on `H¹`

Let `Γ` act on the `𝔽_p`-module `M` through a homomorphism `act : Γ →* G`, with `p` an odd prime.
For any `1`-cocycle `x : Γ → M` and any involution `c ∈ Γ` (`c ^ 2 = 1`), the restriction of `x`
to the cyclic subgroup `⟨c⟩` is a coboundary.

Mathematically: the cocycle condition at `(c, c)` gives `(1 + σ) x c = 0`, where `σ = act c`; since
`2` is invertible in `𝔽_p` (`p` odd), `σ - 1` is surjective onto `ker (1 + σ)`, so
`m := -(2⁻¹) • x c` satisfies `σ • m - m = x c`.  On `⟨c⟩ = {1, c}` this is exactly the coboundary
condition.
-/

namespace Work.SSGRoute

theorem odd_involution_coboundary (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    {Γ G M : Type} [Group Γ] [Group G] [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction G M] [SMulCommClass G (ZMod p) M]
    (act : Γ →* G) (x : Γ → M) (hx : SSGRoute.IsCocycleOn act ⊤ x)
    (c : Γ) (hc : c ^ 2 = 1) :
    SSGRoute.IsCoboundaryOn act (Subgroup.zpowers c) x := by
  -- `2` is invertible in `ZMod p` because `p ≠ 2`.
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp h
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    have hge : 2 ≤ p := (Fact.out : p.Prime).two_le
    exact hp (le_antisymm hle hge)
  -- `x 1 = 0`.
  have hx1 : x 1 = 0 := by
    have h := hx 1 (Subgroup.mem_top 1) 1 (Subgroup.mem_top 1)
    simp only [mul_one, map_one, one_smul] at h
    have h' : 0 = x 1 := add_left_cancel (a := x 1) (by rw [add_zero]; exact h)
    exact h'.symm
  -- The cocycle condition at `(c, c)`: `(1 + σ) x c = 0`, i.e. `σ • x c = -x c`.
  have hσxc : act c • x c = -x c := by
    have h := hx c (Subgroup.mem_top c) c (Subgroup.mem_top c)
    rw [← pow_two, hc, hx1] at h
    have h'' : act c • x c + x c = 0 := by rw [add_comm]; exact h.symm
    exact add_eq_zero_iff_eq_neg.mp h''
  refine ⟨-((2 : ZMod p)⁻¹ • x c), ?_⟩
  intro g hg
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hg
  rw [← hn]
  -- `c ^ (2 : ℤ) = 1`, hence every even power of `c` is `1`.
  have hcz : c ^ (2 : ℤ) = 1 := by rw [zpow_ofNat]; exact hc
  have hpow2 : ∀ k : ℤ, c ^ (2 * k) = 1 := by
    intro k
    rw [zpow_mul, hcz, one_zpow]
  rcases Int.even_or_odd n with he | ho
  · -- `n = 2k`: `c ^ n = 1`, and the coboundary relation at `1` is `0 = 0`.
    obtain ⟨k, hk⟩ := he
    have hnk : n = 2 * k := by rw [two_mul]; exact hk
    rw [hnk, hpow2 k, hx1, map_one, one_smul, sub_self]
  · -- `n = 2k + 1`: `c ^ n = c`, and the relation at `c` holds by construction.
    obtain ⟨k, hk⟩ := ho
    have hodd : c ^ (2 * k + 1) = c := by rw [zpow_add, hpow2 k, one_mul, zpow_one]
    rw [hk, hodd]
    have hm : act c • (-((2 : ZMod p)⁻¹ • x c)) - (-((2 : ZMod p)⁻¹ • x c)) = x c := by
      rw [smul_neg, smul_comm (act c) ((2 : ZMod p)⁻¹) (x c), hσxc, smul_neg, neg_neg,
        sub_eq_add_neg, neg_neg, ← add_smul, ← two_mul, mul_inv_cancel₀ h2, one_smul]
    exact hm.symm

end Work.SSGRoute
