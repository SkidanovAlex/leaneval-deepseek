import Mathlib
import Submission.Work.ZASS.Defs
import Submission.Work.Zassenhaus.Basic

namespace Work.ZASS

/-- **Z2 (blueprint §ZASS).** `|G| = (q+1) * q * (q-1)/2`.  Either from
`MulAction.index_stabilizer` (`|G : B| = |X| = q+1`) together with `ZASS/card_borel`, or
from `MulAction.IsMultiplyPretransitive.index_of_fixingSubgroup_mul` with `k = 2` and the
2-element set `{inf, zero}` (which gives `(q+1)q` for the index of the two-point stabilizer).
(Hypothesis amended to `Work.GW2.ZassHyps2`, design pass 2.) -/
theorem card_G {G X : Type} [Group G] [Finite G] [MulAction G X] [Finite X]
    {q : ℕ} (h : Work.GW2.ZassHyps2 G X q) {inf zero : X} (hne : inf ≠ zero) :
    Nat.card G = (q + 1) * q * ((q - 1) / 2) := by
  obtain ⟨-, hXcard, hpretrans, -, hstab⟩ := h
  -- the two-point stabilizer of `{inf, zero}` is a two-point fixing subgroup
  have hnc : ({inf, zero} : Set X).ncard = 2 := Set.ncard_pair hne
  have hfix : fixingSubgroup G ({inf, zero} : Set X)
      = MulAction.stabilizer G inf ⊓ MulAction.stabilizer G zero := by
    ext g
    simp [mem_fixingSubgroup_iff, MulAction.mem_stabilizer_iff, Subgroup.mem_inf]
  -- its order: `(q - 1)/2`, straight from the hypothesis
  have hcardH : Nat.card ↥(MulAction.stabilizer G inf ⊓ MulAction.stabilizer G zero)
      = (q - 1) / 2 := by
    have h2 := hstab inf zero hne
    rw [← h2]
    exact (Nat.mul_div_cancel_left _ (by norm_num : (0 : ℕ) < 2)).symm
  -- its index: the number of ordered pairs of distinct points, `(q + 1) * q`
  have hidx : (MulAction.stabilizer G inf ⊓ MulAction.stabilizer G zero).index = (q + 1) * q := by
    have h0 := MulAction.IsMultiplyPretransitive.index_of_fixingSubgroup_eq (G := G) (α := X)
        ({inf, zero} : Set X) (by rw [hnc]; exact hpretrans)
    rw [hfix, hXcard, hnc] at h0
    rw [h0]
    have hdvd : 2 ∣ (q + 1) * q := by
      rcases Nat.even_or_odd q with hq | hq
      · have hh : 2 ∣ q * (q + 1) := hq.two_dvd.mul_right (q + 1)
        rwa [mul_comm] at hh
      · obtain ⟨k, hk⟩ := hq
        refine ⟨(k + 1) * q, ?_⟩
        rw [hk]; ring
    rw [Nat.factorial, Nat.factorial, Nat.choose_two_right, Nat.add_sub_cancel]
    exact Nat.div_mul_cancel hdvd
  -- orbit–stabilizer, in the index form `|H| * |G : H| = |G|`
  calc Nat.card G
      = (MulAction.stabilizer G inf ⊓ MulAction.stabilizer G zero).index *
        Nat.card ↥(MulAction.stabilizer G inf ⊓ MulAction.stabilizer G zero) :=
        (Subgroup.index_mul_card _).symm
    _ = (q + 1) * q * ((q - 1) / 2) := by rw [hidx, hcardH]

end Work.ZASS
