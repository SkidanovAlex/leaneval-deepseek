import Mathlib
import Submission.Work.ThmF.ChV3.Step16Defs
import Submission.Work.ThmF.ChV3.Chain17
import Submission.Work.ThmF.Prove.step1
import Submission.Work.ThmF.ChV3.Prove.CH_card_chainfree
import Submission.Work.ThmF.ChV3.Prove.S1_CG_card_orbit
import Submission.Work.ThmF.ChV3.step6aux_count

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.ChV3.Prove.CG_pPart_101`

The `p`-part of `|C_G(P)|` in case (10-1) of Peterfalvi II Ch. V §3:

  `|C_G(P)|_{|P|} = |P| ^ (m+1)`

where `P ≤ V = C_D(t)` has prime order `p = |P| = orderOf (s * t)`, `m ≥ 1` is the exponent of
the chain (`|C_Q(P)| + 1 = p^m`), and case (10-1) says `p ∤ |Σ|` (with `|G|_p = p^{m+2}`).

The proof combines the three cardinalities that are already available from the standing context
`CtxF` alone, all with `p = |P| = orderOf (s * t)`:

* `S1_CG_card_orbit` — `C_G(P)` is transitive on the `P`-fixed points of `Ω = G ⧸ H`
  (`ChV12.centralizer_transitive_fixedPts`), with point stabiliser `C_H(P)`, so
  `|C_G(P)| = |Ω_P| · |C_H(P)|`;
* `step6aux_count` (`|Ω_P| = |C_Q(P)| + 1`) together with `hcq` — `|Ω_P| = p^m`;
* `CH_card_chainfree` (step (1)) — `|C_H(P)| = |C_Q(P)| · |Σ| · |P|`.

Hence `|C_G(P)| = p^m · (p^m − 1) · |Σ| · p`, and since `p` divides neither `p^m − 1` (which is
`≡ −1 (mod p)`, this is where `1 ≤ m` enters) nor `|Σ|` (the first conjunct of `Case101`), the
`p`-part is exactly `p^(m+1)`.

Note that this is the `p`-part statement that the source's step (11) consumes: in the design's
`centralizerP_eq` one has `|C_G(P)| = |R| · |C_Q(P)| · |Σ|` with `|R| = |P| · |P|^m = p^{m+1}`,
which is the same identity.
-/

namespace Work.ThmF.ChV3.Prove

/-- `pPart p (p ^ k * n) = p ^ k` for `p` prime and `p ∤ n`. -/
private lemma pPart_mul_not_dvd {p k n : ℕ} (hp : p.Prime) (h : ¬ p ∣ n) :
    Work.ThmF.ChV3.pPart p (p ^ k * n) = p ^ k := by
  have hn : n ≠ 0 := fun h0 => h (h0 ▸ dvd_zero p)
  have hpk : p ^ k ≠ 0 := pow_ne_zero _ hp.ne_zero
  unfold Work.ThmF.ChV3.pPart
  rw [Nat.factorization_mul hpk hn, Finsupp.add_apply, Nat.factorization_pow, Finsupp.smul_apply,
    Nat.Prime.factorization_self hp, Nat.factorization_eq_zero_of_not_dvd h]
  simp

theorem CG_pPart_101 {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G} {P : Subgroup G}
    {m : ℕ}
    (hFT : Submission.Blueprint.FeitThompsonProp) (hC4 : Submission.Blueprint.ChIIFourProp)
    (c : Work.ThmF.ChV3.CtxF H Q t s r P) (hpf : Nat.card P = orderOf (s * t)) (hm : 1 ≤ m)
    (hcq : Nat.card ↥(Work.ThmF.ChV3.CQ Q P) + 1 = orderOf (s * t) ^ m)
    (h101 : Work.ThmF.ChV3.Case101 H t P m) :
    Work.ThmF.ChV3.pPart (Nat.card P) (Nat.card ↥(Work.ThmF.ChV3.CG P)) = Nat.card P ^ (m+1) := by
  classical
  have hp : (Nat.card P).Prime := c.P_prime
  -- `|C_G(P)| = |Ω_P| · |C_H(P)| = p^m · (|C_Q(P)| · |Σ| · p)`
  have hCS : Nat.card ↥(Work.ThmF.ChV3.CG P) =
      orderOf (s * t) ^ m * (Nat.card ↥(Work.ThmF.ChV3.CQ Q P) *
        Nat.card ↥(Work.ThmF.ChV3.Sig H t P) * Nat.card P) := by
    rw [S1_CG_card_orbit c, ← Work.ThmF.ChV3.step6aux_count hC4 c, hcq,
      CH_card_chainfree hFT hC4 c]
  rw [hCS]
  have he : orderOf (s * t) = Nat.card P := hpf.symm
  rw [he]
  -- `|C_Q(P)| = p^m - 1`
  have ha : Nat.card ↥(Work.ThmF.ChV3.CQ Q P) = Nat.card P ^ m - 1 := by
    have h := hcq; rw [he] at h; omega
  -- `p ∣ p^m`
  have hpm_dvd : Nat.card P ∣ Nat.card P ^ m := by
    have hpow : Nat.card P ^ m = Nat.card P * Nat.card P ^ (m - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel hm]
    exact ⟨Nat.card P ^ (m - 1), hpow⟩
  -- `p ∤ p^m - 1` (this is where `1 ≤ m` is used)
  have hnotdvd_pm1 : ¬ Nat.card P ∣ Nat.card P ^ m - 1 := by
    intro hd
    have h1 : Nat.card P ∣ Nat.card P ^ m - (Nat.card P ^ m - 1) := Nat.dvd_sub hpm_dvd hd
    have h2 : Nat.card P ^ m - (Nat.card P ^ m - 1) = 1 := by
      have : 1 ≤ Nat.card P ^ m := Nat.one_le_pow m (Nat.card P) hp.pos
      omega
    rw [h2] at h1
    exact hp.not_dvd_one h1
  -- `p ∤ (p^m - 1) · |Σ|` (the second factor because case (10-1))
  have hnotdvd : ¬ Nat.card P ∣ (Nat.card P ^ m - 1) * Nat.card ↥(Work.ThmF.ChV3.Sig H t P) := by
    intro hc
    rcases hp.dvd_mul.mp hc with h1 | h1
    · exact hnotdvd_pm1 h1
    · exact h101.1 h1
  have hsplit : Nat.card P ^ m * (Nat.card ↥(Work.ThmF.ChV3.CQ Q P) *
        Nat.card ↥(Work.ThmF.ChV3.Sig H t P) * Nat.card P)
      = Nat.card P ^ (m + 1) * ((Nat.card P ^ m - 1) * Nat.card ↥(Work.ThmF.ChV3.Sig H t P)) := by
    rw [ha]; ring
  rw [hsplit]
  exact pPart_mul_not_dvd hp hnotdvd

end Work.ThmF.ChV3.Prove
