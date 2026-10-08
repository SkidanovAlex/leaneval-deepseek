import Mathlib
import Submission.Work.ThmF.ChV3.Ctx
import Submission.Work.ThmF.Prove.Step10Wrap.lteFactorization
import Submission.Work.ThmF.Prove.Step10Wrap.twoPowSubOne_factorization
import Submission.Work.ThmF.Prove.Step10Wrap.case2Factorizations

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.Prove.step10Wrapper` — step (10) of Peterfalvi II Ch. V §3, wrapper form

Step (10) (Peterfalvi II Ch. V §3, p. 252) says: if `|F| = f^m` then `p = f` and either (10-1)
`p ∤ |Σ|` and the `p`-part of `|G|` is `p^{m+2}`, or (10-2) `p = 3`, `f = 8` (so `q = f^p = 512`,
`q + 1 = 513 = 3^3 · 19`), `|Σ| = 3` and `|W| ∈ {3, 9}`, in which case the `3`-part of `|G|` is
`3^4 · |W|`.

The source's proof of the arithmetic half reads:

* `|Q| + 1 = (−1 + p^m)^p + 1 ≡ p^{m+1} (mod p^{m+2})`, hence `(|Q|+1)_p = p^{m+1}` (LTE); this
  needs `p` odd, which is *available here* because `|D| = (2^p−1)·|W|·p` is odd (strong
  embeddedness) and `(2^p−1)·|W|·p` is even when `p = 2`;
* `p ∤ |Q|` (as `|Q| = (p^m−1)^p`), `p ∤ 2^p − 1` (Fermat), `p ∤ |W|` in case (10-1) (by
  hypothesis `hSigW`);
* `|G| = (|Q|+1)·|H| = (|Q|+1)·|Q|·|D| = (|Q|+1)·|Q|·(2^p−1)·|W|·p`.

So the whole content of the wrapper is: the oddness of `D` forces `p` odd, and then the `p`-part of
a product of five explicit factors is computed by summing `p`-adic valuations.

The two number-theoretic leaves are proved in the sibling files
`Step10Wrap/lteFactorization` and `Step10Wrap/twoPowSubOne_factorization`; the case (10-2)
numerics are in `Step10Wrap/case2Factorizations`.
-/

namespace Work.ThmF.Prove

/-- **Case (10-1) arithmetic.**  For an odd prime `p`, with `f + 1 = p^m` (`m ≥ 1`), `q = f^p`,
`p ∤ w`, and `g = (q+1) · q · ((2^p − 1) · w · p)`, the `p`-adic valuation of `g` is `m + 2`:
the factors `q`, `2^p − 1` and `w` contribute nothing, `q + 1 = (p^m−1)^p + 1` contributes
`m + 1` (LTE, `p` odd) and the final factor `p` contributes `1`. -/
theorem factorization_of_data {p f q w g m : ℕ} (hp : p.Prime) (hodd : Odd p) (hm : 1 ≤ m)
    (hf : f + 1 = p ^ m) (hq : q = f ^ p) (hw : ¬ p ∣ w)
    (hg : g = (q + 1) * q * ((2 ^ p - 1) * w * p)) :
    g.factorization p = m + 2 := by
  have hLTE : (f ^ p + 1).factorization p = m + 1 :=
    Step10Wrap.lteFactorization hp hodd hm hf
  have hF : (2 ^ p - 1).factorization p = 0 := Step10Wrap.twoPowSubOne_factorization hp
  have hf0 : f ≠ 0 := by
    have h1 : 1 < p ^ m := Nat.one_lt_pow (by omega) hp.one_lt
    omega
  have hq0 : q ≠ 0 := by rw [hq]; exact pow_ne_zero _ hf0
  have hw0 : w ≠ 0 := by rintro rfl; exact hw (dvd_zero p)
  have hpf : ¬ p ∣ f := by
    intro h
    have hp2 : p ∣ f + 1 := by rw [hf]; exact dvd_pow_self p (by omega)
    have hp1 : p ∣ 1 := by
      have h3 : p ∣ (f + 1) - f := Nat.dvd_sub hp2 h
      simpa using h3
    exact hp.not_dvd_one hp1
  have hq1 : (q + 1).factorization p = m + 1 := by rw [hq, hLTE]
  have hqf : q.factorization p = 0 := by
    rw [hq, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
      Nat.factorization_eq_zero_of_not_dvd hpf, mul_zero]
  have hwfac : w.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hw
  have h2p : (2 ^ p - 1) ≠ 0 := by
    have h2 : 1 < 2 ^ p := Nat.one_lt_pow hp.ne_zero (by norm_num)
    omega
  have hA : (q + 1) * q ≠ 0 := mul_ne_zero (by omega) hq0
  have hB : (2 ^ p - 1) * w * p ≠ 0 := mul_ne_zero (mul_ne_zero h2p hw0) hp.ne_zero
  have hsplit4 : ((q + 1) * q * (((2 ^ p - 1) * w) * p)).factorization
      = ((q + 1) * q).factorization + (((2 ^ p - 1) * w) * p).factorization :=
    Nat.factorization_mul hA hB
  have hsplit3 : (((2 ^ p - 1) * w) * p).factorization
      = ((2 ^ p - 1) * w).factorization + p.factorization :=
    Nat.factorization_mul (mul_ne_zero h2p hw0) hp.ne_zero
  have hsplit2 : ((2 ^ p - 1) * w).factorization
      = (2 ^ p - 1).factorization + w.factorization :=
    Nat.factorization_mul h2p hw0
  have hsplit1 : ((q + 1) * q).factorization = (q + 1).factorization + q.factorization :=
    Nat.factorization_mul (by omega) hq0
  rw [hg, hsplit4, Finsupp.add_apply, hsplit1, Finsupp.add_apply, hsplit3,
    Finsupp.add_apply, hsplit2, Finsupp.add_apply, hq1, hqf, hF, hwfac,
    hp.factorization_self]
  omega

theorem step10Wrapper {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G} {P : Subgroup G} {m : ℕ}
    (c : Work.ThmF.ChV3.CtxF H Q t s r P)
    (hWD : Nat.card ↥(Submission.Blueprint.twoPoint H t) =
      (2 ^ Nat.card P - 1) * Nat.card ↥(Work.ThmF.W H t) * Nat.card P)
    (hGH : Nat.card G = (Nat.card Q + 1) * Nat.card ↥H)
    (hQD : Nat.card ↥H = Nat.card Q * Nat.card ↥(Submission.Blueprint.twoPoint H t))
    (hm : 1 ≤ m) (hcq : Nat.card ↥(Work.ThmF.ChV3.CQ Q P) + 1 = Nat.card P ^ m)
    (h4 : Nat.card Q = Nat.card ↥(Work.ThmF.ChV3.CQ Q P) ^ Nat.card P)
    (hSigW : ¬ Nat.card P ∣ Nat.card ↥(Work.ThmF.ChV3.Sig H t P) →
      ¬ Nat.card P ∣ Nat.card ↥(Work.ThmF.W H t))
    (hcase2 : Nat.card P ∣ Nat.card ↥(Work.ThmF.ChV3.Sig H t P) →
      Nat.card P = 3 ∧ Nat.card ↥(Work.ThmF.ChV3.CQ Q P) = 8 ∧
      Nat.card ↥(Work.ThmF.ChV3.Sig H t P) = 3 ∧
      (Nat.card ↥(Work.ThmF.W H t) = 3 ∨ Nat.card ↥(Work.ThmF.W H t) = 9)) :
    (¬ Nat.card P ∣ Nat.card ↥(Work.ThmF.ChV3.Sig H t P) ∧
        Work.ThmF.ChV3.pPart (Nat.card P) (Nat.card G) = Nat.card P ^ (m + 2)) ∨
     (Nat.card P = 3 ∧ Nat.card ↥(Work.ThmF.ChV3.Sig H t P) = 3 ∧
        Nat.card ↥(Work.ThmF.ChV3.CQ Q P) = 8 ∧
        (Nat.card ↥(Work.ThmF.W H t) = 3 ∨ Nat.card ↥(Work.ThmF.W H t) = 9) ∧
        Work.ThmF.ChV3.pPart 3 (Nat.card G) = 3 ^ 4 * Nat.card ↥(Work.ThmF.W H t)) := by
  -- `D = H ∩ H^t` has odd order (strong embeddedness), and `|D| = (2^p - 1) · |W| · p`
  -- forces `p ≠ 2`: if `p = 2` the right-hand side is even.
  have hdOdd : Odd (Nat.card ↥(Submission.Blueprint.twoPoint H t)) :=
    Work.ThmF.split_odd_card_twoPoint c.split
  have hpOdd : Odd (Nat.card P) := by
    rcases eq_or_ne (Nat.card P) 2 with h2 | h2
    · exfalso
      obtain ⟨k, hk⟩ := hdOdd
      rw [hWD, h2] at hk
      have h3 : (2 : ℕ) ^ 2 - 1 = 3 := by norm_num
      rw [h3] at hk
      omega
    · exact c.P_prime.odd_of_ne_two h2
  have hg : Nat.card G = (Nat.card Q + 1) * Nat.card Q *
      ((2 ^ Nat.card P - 1) * Nat.card ↥(Work.ThmF.W H t) * Nat.card P) := by
    rw [hGH, hQD, hWD]
    ring
  by_cases hσ : Nat.card P ∣ Nat.card ↥(Work.ThmF.ChV3.Sig H t P)
  · -- Case (10-2): `p = 3`, `f = 8`, `|Σ| = 3`, `|W| ∈ {3, 9}`.
    obtain ⟨hp3, hf8, hσ3, hw39⟩ := hcase2 hσ
    refine Or.inr ⟨hp3, hσ3, hf8, hw39, ?_⟩
    have key := Step10Wrap.case2Factorizations (p := Nat.card P)
      (f := Nat.card ↥(Work.ThmF.ChV3.CQ Q P)) (q := Nat.card Q)
      (w := Nat.card ↥(Work.ThmF.W H t)) (g := Nat.card G) hp3 hf8 h4 hg hw39
    rw [Work.ThmF.ChV3.pPart, key.1]
    exact key.2
  · -- Case (10-1): `p ∤ |Σ|`, so `p ∤ |W|`; the `p`-part of `|G|` is `p^{m+2}`.
    refine Or.inl ⟨hσ, ?_⟩
    have hw : ¬ Nat.card P ∣ Nat.card ↥(Work.ThmF.W H t) := hSigW hσ
    have key := factorization_of_data (p := Nat.card P)
      (f := Nat.card ↥(Work.ThmF.ChV3.CQ Q P)) (q := Nat.card Q)
      (w := Nat.card ↥(Work.ThmF.W H t)) (g := Nat.card G) (m := m)
      c.P_prime hpOdd hm hcq h4 hw hg
    rw [Work.ThmF.ChV3.pPart, key]

end Work.ThmF.Prove
