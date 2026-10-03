import Mathlib
import Submission.Commons.NumberTheory.FriedlanderIwaniec.X2Y4_pair_roots_mod_prime_pow_card_mod_four_one

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.NumberTheory.FriedlanderIwaniec

open Finset

/-- Cardinality of a valuation stratum `{y | X2Y4_valZ p e y = a}` for `a < e`. -/
lemma X2Y4_card_valZ_stratum_of_lt {p e a m : ℕ} (hp : p.Prime) (ha : a < m) (hm : m ≤ e) :
    ({y : ZMod (p ^ e) | X2Y4_valZ p e y = a}).ncard = p ^ (e - a - 1) * (p - 1) := by
  have hae : a < e := lt_of_lt_of_le ha hm
  rw [X2Y4_card_valZ_stratum hp (le_of_lt hae), if_pos hae]

/-- Sum of `p ^ (2 * X2Y4_valZ p e y)` over the valuation stratum `a`, below the cutoff `m`. -/
lemma X2Y4_stratum_sum_pow_sq {p e m a : ℕ} (hp : p.Prime) (ha : a < m) (hm : m ≤ e)
    [NeZero (p ^ e)] :
    (∑ y ∈ (Finset.univ.filter (fun y : ZMod (p ^ e) => X2Y4_valZ p e y < m)).filter
        (fun y => X2Y4_valZ p e y = a), p ^ (2 * X2Y4_valZ p e y))
      = p ^ (e - a - 1) * (p - 1) * p ^ (2 * a) := by
  have hfilter : (Finset.univ.filter (fun y : ZMod (p ^ e) => X2Y4_valZ p e y < m)).filter
        (fun y => X2Y4_valZ p e y = a)
      = Finset.univ.filter (fun y : ZMod (p ^ e) => X2Y4_valZ p e y = a) := by
    rw [Finset.filter_filter]
    apply Finset.filter_congr
    intro y _
    constructor
    · rintro ⟨-, h2⟩; exact h2
    · intro h2; exact ⟨by rw [h2]; exact ha, h2⟩
  rw [hfilter]
  have hconst : ∀ y ∈ Finset.univ.filter (fun y : ZMod (p ^ e) => X2Y4_valZ p e y = a),
      p ^ (2 * X2Y4_valZ p e y) = p ^ (2 * a) := fun y hy => by
    rw [(Finset.mem_filter.mp hy).2]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul]
  rw [← Fintype.card_subtype (fun y : ZMod (p ^ e) => X2Y4_valZ p e y = a)]
  rw [show Fintype.card {y : ZMod (p ^ e) // X2Y4_valZ p e y = a}
      = Fintype.card (↥{y : ZMod (p ^ e) | X2Y4_valZ p e y = a}) from rfl,
    Set.fintypeCard_eq_ncard]
  rw [X2Y4_card_valZ_stratum_of_lt hp ha hm]

/-- Evaluation of the geometric-type sum over valuations below `(e + 3) / 4`. -/
lemma X2Y4_sum_range_pow_geom {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e) :
    (∑ a ∈ Finset.range ((e + 3) / 4), p ^ (e - a - 1) * (p - 1) * p ^ (2 * a))
      = p ^ (e - 1) * (p ^ ((e + 3) / 4) - 1) := by
  have hp1 : 1 ≤ p := hp.one_lt.le
  have hme : (e + 3) / 4 ≤ e := by omega
  have hterm : ∀ a ∈ Finset.range ((e + 3) / 4),
      p ^ (e - a - 1) * (p - 1) * p ^ (2 * a) = (p - 1) * p ^ (e - 1) * p ^ a := by
    intro a ha
    rw [Finset.mem_range] at ha
    have hae : a < e := lt_of_lt_of_le ha hme
    rw [show p ^ (e - a - 1) * (p - 1) * p ^ (2 * a)
          = (p - 1) * (p ^ (e - a - 1) * p ^ (2 * a)) by ring]
    rw [← pow_add, show e - a - 1 + 2 * a = e + a - 1 by omega,
        show e + a - 1 = (e - 1) + a by omega, pow_add]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum,
      show (p - 1) * p ^ (e - 1) * (∑ a ∈ Finset.range ((e + 3) / 4), p ^ a)
          = p ^ (e - 1) * ((p - 1) * (∑ a ∈ Finset.range ((e + 3) / 4), p ^ a)) by ring,
      X2Y4_mul_geom_sum p ((e + 3) / 4) hp1]

theorem X2Y4_sum_pow_sq_valZ_lt {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e) [NeZero (p ^ e)] :
    (∑ y ∈ (Finset.univ : Finset (ZMod (p ^ e))).filter
        (fun y => X2Y4_valZ p e y < (e + 3) / 4),
      p ^ (2 * X2Y4_valZ p e y))
      = p ^ (e - 1) * (p ^ ((e + 3) / 4) - 1) := by
  have hme : (e + 3) / 4 ≤ e := by omega
  have hmaps : ∀ x ∈ (Finset.univ : Finset (ZMod (p ^ e))).filter
        (fun y => X2Y4_valZ p e y < (e + 3) / 4),
      X2Y4_valZ p e x ∈ Finset.range ((e + 3) / 4) := by
    intro x hx
    rw [Finset.mem_range]
    exact (Finset.mem_filter.mp hx).2
  rw [← Finset.sum_fiberwise_of_maps_to
        (s := (Finset.univ : Finset (ZMod (p ^ e))).filter
          (fun y => X2Y4_valZ p e y < (e + 3) / 4))
        (t := Finset.range ((e + 3) / 4))
        (g := fun y => X2Y4_valZ p e y) (f := fun y => p ^ (2 * X2Y4_valZ p e y)) hmaps]
  have hstep : (∑ a ∈ Finset.range ((e + 3) / 4),
        ∑ x ∈ ((Finset.univ : Finset (ZMod (p ^ e))).filter
            (fun y => X2Y4_valZ p e y < (e + 3) / 4)).filter
            (fun y => X2Y4_valZ p e y = a), p ^ (2 * X2Y4_valZ p e x))
      = ∑ a ∈ Finset.range ((e + 3) / 4), p ^ (e - a - 1) * (p - 1) * p ^ (2 * a) :=
    Finset.sum_congr rfl (fun a ha => X2Y4_stratum_sum_pow_sq hp (Finset.mem_range.mp ha) hme)
  rw [hstep]
  exact X2Y4_sum_range_pow_geom hp he

end Commons.NumberTheory.FriedlanderIwaniec
