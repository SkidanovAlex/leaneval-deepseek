import Mathlib
import Submission.Work.ZJB.Step1.Defs

namespace Work.ZJB2.Step1

open Subgroup

/-!
# F3: the normalizer condition for Sylow subgroups

We prove the leaf `Work.ZJB.SylowOfNormalizerProp`: if `T ≤ G` is a `p`-subgroup whose
normalizer has no larger `p`-part than `T` itself --- `p ^ ν_p(|N_G(T)|) ≤ |T|` --- then `T`
is a Sylow `p`-subgroup of `G`.

The mathematics (standard): always `|T| ∣ |N_G(T)|`, so `|T| = p ^ n` forces the `p`-part of
`|N_G(T)|` to be at least `p ^ n`. If it were strictly larger, i.e. `p ^ (n+1) ∣ |N_G(T)|`,
then in particular `p ^ (n+1) ∣ |G|`, and the classical Sylow-counting statement
`Sylow.prime_pow_dvd_card_normalizer` (the `p`-part of `|N_G(H)|` exceeds `|H|` whenever `H`
of order `p ^ n` sits inside a group whose order is divisible by `p ^ (n+1)`) gives the
contradiction. Hence `(Nat.card G).factorization p = n`, i.e. `T` has the full `p`-part of `|G|`,
and `Sylow.ofCard` turns it into a Sylow `p`-subgroup with the same underlying subgroup.

Equivalently one may argue through the normalizer condition for `p`-groups; the counting
argument above avoids that machinery.
-/

theorem sylowOfNormalizerProp {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] :
    Work.ZJB.SylowOfNormalizerProp p G := by
  intro T hT hle
  have hp : Nat.Prime p := Fact.out
  -- `T` is a `p`-group, so `|T| = p ^ n` for some `n`.
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hT
  -- `ν_p(|N_G(T)|) = p`-exponent of `|N_G(T)|` is at most `n`.
  have hN : (Nat.card ↥(normalizer (T : Set G))).factorization p ≤ n := by
    have hle' : p ^ Work.ZJB.nuP p (normalizer (T : Set G)) ≤ p ^ n := by
      rw [hn] at hle
      exact hle
    have := (Nat.pow_le_pow_iff_right hp.one_lt).mp hle'
    simpa only [Work.ZJB.nuP] using this
  -- `p ^ n = |T|` divides `|G|`, so `n ≤ ν_p(|G|)`.
  have hn_le : n ≤ (Nat.card G).factorization p := by
    have hdvdT : p ^ n ∣ Nat.card G := by
      rw [← hn]
      exact Subgroup.card_subgroup_dvd_card T
    exact (hp.pow_dvd_iff_le_factorization (Nat.card_pos (α := G)).ne').mp hdvdT
  -- Conversely `ν_p(|G|) ≤ n`: otherwise `p ^ (n+1) ∣ |G|` and hence `p ^ (n+1) ∣ |N_G(T)|`,
  -- contradicting `hN`.
  have hn_ge : (Nat.card G).factorization p ≤ n := by
    by_contra hcon
    have hlt : n + 1 ≤ (Nat.card G).factorization p := by omega
    have hdvdG : p ^ (n + 1) ∣ Nat.card G :=
      (hp.pow_dvd_iff_le_factorization (Nat.card_pos (α := G)).ne').mpr hlt
    have hdivN : p ^ (n + 1) ∣ Nat.card ↥(normalizer (T : Set G)) :=
      Sylow.prime_pow_dvd_card_normalizer hdvdG hn
    have hfacN : n + 1 ≤ (Nat.card ↥(normalizer (T : Set G))).factorization p :=
      (hp.pow_dvd_iff_le_factorization
        (Nat.card_pos (α := ↥(normalizer (T : Set G)))).ne').mp hdivN
    omega
  have hfac : (Nat.card G).factorization p = n := le_antisymm hn_ge hn_le
  -- So `|T|` is exactly the `p`-part of `|G|`, and `Sylow.ofCard` finishes.
  have hcard : Nat.card ↥T = p ^ (Nat.card G).factorization p := by
    rw [hn, hfac]
  exact ⟨Sylow.ofCard T hcard, Sylow.coe_ofCard T hcard⟩

end Work.ZJB2.Step1
