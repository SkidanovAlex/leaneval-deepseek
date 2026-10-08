import Mathlib
import Submission.Work.BG.ThmABCDefs
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.GLUE.Defs
import Submission.Work.BG.thmCSmallShape
import Submission.Work.BG.relIndexCentT1
import Submission.Work.BG.relIndexCentT2
import Submission.Work.BG.cardKdvdRelIndexUB1
import Submission.Work.BG.cardKdvdRelIndexUB2
import Submission.Work.BG.nCases

/-!
# `2 * |K₁ ⊓ K₂| ∣ k` (Bender–Glauberman 1981, p. 211)

Bender–Glauberman use on p. 211 ("As `2|K|` divides `k` and is prime to `|G : H|` …") that,
under the hypotheses of their Theorem C, `2 * |K|` divides `k = k₁ + k₂`, where `K = K₁ ⊓ K₂`
and `kᵢ = |H : C_H(tᵢ)|`.

The two arithmetic ingredients of the paper's notation (BG p. 201)

  `kᵢ = (1/2)·|S₀|·|U : Bᵢ|`          (`Work.BG.relIndexCentT1`, `Work.BG.relIndexCentT2`)

combine with the structural consequence of the Theorem C hypotheses

  `|K₁ ⊓ K₂| ∣ |U : Bᵢ|` (`i = 1, 2`) (`Work.BG.cardKdvdRelIndexUB1`, `cardKdvdRelIndexUB2`)

to give `k = (n/2)·|K|·(d₁ + d₂)`, which is divisible by `2·|K|` as soon as `4 ∣ n`; for
`|S| ≥ 8` (`4 ≤ n`, with `n` a power of two) that is automatic, and the remaining case
`|S| = 4` is the already-proved `Work.BG.thmCSmallShape` (`k = 2|K|` exactly).
-/

namespace Work.BG

/-- Arithmetic: if `4 ∣ n` and `rᵢ = kc * dᵢ`, then `(n/2)·r₁ + (n/2)·r₂` is divisible by `2 * kc`
(the factor `n/2` is even). -/
private lemma c3Kdiv_arith (n kc r1 r2 d1 d2 : ℕ) (h4 : 4 ∣ n)
    (h1 : r1 = kc * d1) (h2 : r2 = kc * d2) :
    (2 * kc) ∣ (n / 2) * r1 + (n / 2) * r2 := by
  obtain ⟨s, hs⟩ := h4
  have hhalf : n / 2 = 2 * s := by omega
  rw [h1, h2, hhalf]
  refine ⟨s * d1 + s * d2, ?_⟩
  ring

/-- For the Bender–Glauberman data, `4 ≤ D.n` forces `4 ∣ D.n`: `D.n = |S₀|` is a power of two
(`S₀` is a subgroup of the `2`-group `S`), and a power of two that is at least `4` is divisible
by `4`. -/
private lemma c3Kdiv_four_dvd_n {G : Type} [Group G] [Finite G] (D : Work.GW2.BGData G)
    (h4 : 4 ≤ D.n) : 4 ∣ D.n := by
  obtain ⟨e0⟩ := D.dih
  have hcardS : Nat.card (D.S : Subgroup G) = 2 * D.n := by
    rw [Nat.card_congr e0.toEquiv, DihedralGroup.nat_card]
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp D.S.isPGroup'
  have hj1 : 1 ≤ j := by
    by_contra h
    have h0 : j = 0 := by omega
    have h2n : 2 * D.n = 1 := by rw [← hcardS, hj, h0]; norm_num
    have := D.two_le
    omega
  have hn_pow : D.n = 2 ^ (j - 1) := by
    have h2n : 2 ^ j = 2 * D.n := by rw [← hj, hcardS]
    have h2 : 2 ^ j = 2 * 2 ^ (j - 1) := by
      calc 2 ^ j = 2 ^ ((j - 1) + 1) := by rw [show (j - 1) + 1 = j by omega]
        _ = 2 * 2 ^ (j - 1) := by rw [pow_succ']
    rw [h2] at h2n
    exact (Nat.mul_left_cancel (by norm_num) h2n).symm
  rw [hn_pow, show (4 : ℕ) = 2 ^ 2 from by norm_num]
  refine pow_dvd_pow 2 ?_
  have hle : 2 ^ 2 ≤ 2 ^ (j - 1) := by rw [← hn_pow]; simpa using h4
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hle

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
/-- **Bender–Glauberman 1981, p. 211**: under the hypotheses of Theorem C, `2 * |K₁ ⊓ K₂|`
divides `k = k₁ + k₂`.

With `rᵢ := |U : Bᵢ|` one has `kᵢ = (n/2)·rᵢ` (`Work.BG.relIndexCentT1`,
`Work.BG.relIndexCentT2`), and `|K₁ ⊓ K₂| ∣ rᵢ` (`Work.BG.cardKdvdRelIndexUB1`,
`Work.BG.cardKdvdRelIndexUB2`), so `k = (n/2)·|K₁ ⊓ K₂|·(d₁ + d₂)` with `d₁ + d₂ ≥ 1`.  For
`|S| = 2n ≥ 8` one has `4 ∣ n`, hence `n/2` is even and `2·|K₁ ⊓ K₂|` divides `k`; for
`|S| = 4` the case `n = 2` is `Work.BG.thmCSmallShape` (`k = 2·|K₁ ⊓ K₂|` exactly). -/
theorem c3Kdiv {G : Type} [Group G] [Finite G]
    (D : Work.GW2.BGData G) (K1 K2 : Subgroup G)
    (hHyps : Work.GW2.C16.ThmCHyps D K1 K2) :
    (2 * Nat.card (K1 ⊓ K2 : Subgroup G)) ∣ D.k := by
  rcases (nCases G D).1 with hn2 | hn4
  · -- `|S| = 4`: `U = B K` and `k = 2|K|` exactly (`Work.GW2.C16.ThmCSmallShapeProp`)
    obtain ⟨-, hk⟩ := thmCSmallShape G D K1 K2 hn2 hHyps.1 hHyps.2.1 hHyps.2.2.1
    rw [hk]
  · -- `|S| ≥ 8`: `k = (n/2)(r₁ + r₂)` with `|K|` dividing both `rᵢ` and `4 ∣ n`
    obtain ⟨d1, hd1⟩ := cardKdvdRelIndexUB1 D K1 K2 hHyps
    obtain ⟨d2, hd2⟩ := cardKdvdRelIndexUB2 D K1 K2 hHyps
    have h1 := relIndexCentT1 D
    have h2 := relIndexCentT2 D
    show (2 * Nat.card (K1 ⊓ K2 : Subgroup G)) ∣
      (Subgroup.centralizer ({D.t1} : Set G)).relIndex D.H +
        (Subgroup.centralizer ({D.t2} : Set G)).relIndex D.H
    rw [h1, h2]
    exact c3Kdiv_arith D.n _ _ _ d1 d2 (c3Kdiv_four_dvd_n D hn4) hd1 hd2

end Work.BG
