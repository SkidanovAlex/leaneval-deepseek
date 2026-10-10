import Mathlib
import Submission.Work.MotV.H1Data
import Submission.Work.MotV.Machinery
import Submission.Work.MotV.fifthPowerValued_of_pow
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotV

/-! ## Elementary lemmas used by the assembly

`ordP`, `Place` and `H1Data` are the vocabulary of `Submission/Work/MotV/H1Data.lean`
(`Work.MotV`).  The first two of the following four lemmas are one-line restatements of the
corresponding fields of `H1Data`, the power formula follows by induction, and the last two are the
arithmetic inputs of the Frobenius descent. -/

/-- In characteristic `p`, `(s - 1) ^ (p ^ n) = s ^ (p ^ n) - 1` (Freshman's dream). -/
lemma sub_one_pow_char_pow {L : Type*} [Field L] (p : ℕ) [Fact p.Prime] [CharP L p]
    {F : Type*} [Field F] [Algebra L F] (s : F) (n : ℕ) :
    (s - 1) ^ (p ^ n) = s ^ (p ^ n) - 1 := by
  haveI : CharP F p := charP_of_injective_algebraMap (algebraMap L F).injective p
  rw [sub_pow_char_pow, one_pow]

/-- A non-zero integer is not divisible by `p ^ n` for every `n` (`p ≥ 2`). -/
lemma not_dvd_pow_of_ne_zero {p : ℕ} (hp : 1 < p) {m : ℤ} (hm : m ≠ 0) :
    ¬ (∀ n : ℕ, ((p ^ n : ℕ) : ℤ) ∣ m) := by
  intro h
  have h1 := h (m.natAbs + 1)
  have h2 : p ^ (m.natAbs + 1) ∣ m.natAbs := by
    simpa using (Int.natAbs_dvd_natAbs (a := ((p ^ (m.natAbs + 1) : ℕ) : ℤ)) (b := m)).mpr h1
  have h3 : p ^ (m.natAbs + 1) ≤ m.natAbs := Nat.le_of_dvd (Int.natAbs_pos.mpr hm) h2
  have h4 : m.natAbs + 1 < p ^ (m.natAbs + 1) := Nat.lt_pow_self (n := m.natAbs + 1) (a := p) hp
  omega

variable {N : Type*} [Field N]

/-- The order of `1` at a rational place is `0`. -/
lemma ordP_one (E : WeierstrassCurve N) [E.IsElliptic] (H : H1Data N E) (Q : Place N E) :
    ordP E Q (1 : MotC2.Func E) = 0 := by
  have h := H.ord_mul Q.1 Q.2 1 1 one_ne_zero one_ne_zero
  rw [mul_one] at h
  show ordOfPlace E Q.1 Q.2 (1 : MotC2.Func E) = 0
  omega

/-- Multiplicativity of the order at a rational place. -/
lemma ordP_mul (E : WeierstrassCurve N) [E.IsElliptic] (H : H1Data N E) (Q : Place N E)
    {f g : MotC2.Func E} (hf : f ≠ 0) (hg : g ≠ 0) :
    ordP E Q (f * g) = ordP E Q f + ordP E Q g :=
  H.ord_mul Q.1 Q.2 f g hf hg

/-- The order of a `k`-th power. -/
lemma ordP_pow (E : WeierstrassCurve N) [E.IsElliptic] (H : H1Data N E) (Q : Place N E)
    {f : MotC2.Func E} (hf : f ≠ 0) (k : ℕ) :
    ordP E Q (f ^ k) = (k : ℤ) * ordP E Q f := by
  induction k with
  | zero => simpa using ordP_one E H Q
  | succ k ih =>
    rw [pow_succ, ordP_mul E H Q (pow_ne_zero _ hf) hf, ih]
    push_cast
    first | refl_ring1 | ring

/-- **The assembly `derivAll`.**  Over an algebraically closed field `N` with `ringChar N ≠ 5` and
an elliptic curve `E/N`, an element `r` of the function field `N(E)` whose value `r * (r - 1)` is a
fifth power at every `ℤᵐ⁰`-valued valuation trivial on `N` is constant.

The hypotheses are the decomposed inputs of the Hurwitz-lite argument for the invariant derivation
`D` of `N(E)`:

* `hmain` — the counting step (`Work.MotV.derivMain`, `Work.MotV.derivCount`): an `f` with
  `D f ≠ 0` and `FifthPowerValued N (f * (f - 1))` is constant;
* `hkerP` — in characteristic `p ≠ 5` the kernel of `D` consists of `p`-th powers;
* `hker0` — in characteristic zero the kernel of `D` consists of constants;
* `hterm` — a non-constant element has non-zero order at some rational place.

Proof.  If `D r ≠ 0`, apply `hmain`.  If `D r = 0`, then in characteristic zero `hker0` gives the
result, while in characteristic `p ≠ 5` one iterates `hkerP`: either one reaches at some stage an
element `s` with `D s ≠ 0`, which `hmain` shows to be constant — contradicting the non-constancy of
`r = s ^ (p ^ n)` — or `r` is a `p ^ n`-th power of a non-constant element of `ker D` for every `n`,
whence `p ^ n ∣ ord_Q r` at a place `Q` with `ord_Q r ≠ 0` for every `n`, which is impossible.  The
hypothesis `FifthPowerValued N (r * (r - 1))` descends through the `p ^ n`-th root because
`r * (r - 1) = (s * (s - 1)) ^ (p ^ n)` in characteristic `p` and `p ^ n` is coprime to `5`
(`Work.MotV.fifthPowerValued_of_pow`). -/
theorem derivAll {N : Type*} [Field N] [IsAlgClosed N] (E : WeierstrassCurve N) [E.IsElliptic]
    (H : Work.MotV.H1Data N E)
    (D : Derivation N (Work.MotC2.Func E) (Work.MotC2.Func E))
    (hmain : ∀ f : Work.MotC2.Func E, D f ≠ 0 → Work.MotV.FifthPowerValued N (f * (f - 1)) →
      ∃ c : N, algebraMap N (Work.MotC2.Func E) c = f)
    (hkerP : ∀ (p : ℕ) [Fact p.Prime] [CharP N p], p ≠ 5 → ∀ f : Work.MotC2.Func E,
      D f = 0 → ∃ s : Work.MotC2.Func E, s ^ p = f)
    (hker0 : CharZero N → ∀ f : Work.MotC2.Func E, D f = 0 →
      ∃ c : N, algebraMap N (Work.MotC2.Func E) c = f)
    (hterm : ∀ f : Work.MotC2.Func E, (∀ c : N, algebraMap N (Work.MotC2.Func E) c ≠ f) →
      ∃ Q : Work.MotV.Place N E, Work.MotV.ordP E Q f ≠ 0)
    (hN5 : ringChar N ≠ 5)
    (r : Work.MotC2.Func E) (hr : Work.MotV.FifthPowerValued N (r * (r - 1))) :
    ∃ c : N, algebraMap N (Work.MotC2.Func E) c = r := by
  classical
  by_cases hDr : D r = 0
  · -- `r` lies in the kernel of `D`
    by_cases hcz : CharZero N
    · -- characteristic zero: the kernel consists of constants
      exact hker0 hcz r hDr
    · -- characteristic `p ≠ 5`: descend along `p`-th roots
      have hp : Nat.Prime (ringChar N) := by
        rcases CharP.char_is_prime_or_zero N (ringChar N) with h | h
        · exact h
        · exact absurd ((CharP.charP_zero_iff_charZero N).mp (ringChar.eq_iff.mp h)) hcz
      haveI : Fact (Nat.Prime (ringChar N)) := ⟨hp⟩
      haveI : CharP N (ringChar N) := ringChar.charP N
      -- suppose `r` is not constant
      by_contra hcon
      have hnc : ∀ c : N, algebraMap N (MotC2.Func E) c ≠ r := fun c h => hcon ⟨c, h⟩
      obtain ⟨Q, hQ⟩ := hterm r hnc
      -- `key n`: `r` is the `(ringChar N) ^ n`-th power of a non-constant element of `ker D`
      have key : ∀ n : ℕ, ∃ f : MotC2.Func E,
          f ^ ((ringChar N) ^ n) = r ∧ D f = 0 ∧
            ∀ c : N, algebraMap N (MotC2.Func E) c ≠ f := by
        intro n
        induction n with
        | zero => exact ⟨r, by simp, hDr, hnc⟩
        | succ n ih =>
          obtain ⟨f, hfpow, hDf, hfnonc⟩ := ih
          -- `f` is a `p`-th power
          obtain ⟨s, hs⟩ := hkerP (ringChar N) hN5 f hDf
          have hs1 : s ^ ((ringChar N) ^ (n + 1)) = r := by
            rw [pow_succ', pow_mul, hs, hfpow]
          have hsnonc : ∀ c : N, algebraMap N (MotC2.Func E) c ≠ s := by
            intro c hc
            exact hfnonc (c ^ ringChar N) (by rw [← hs, ← hc, ← map_pow])
          -- the hypothesis survives the extraction of the `p`-th root
          have hfac : r * (r - 1) = (s * (s - 1)) ^ ((ringChar N) ^ (n + 1)) := by
            rw [← hs1, mul_pow, sub_one_pow_char_pow (L := N) (ringChar N) s (n + 1)]
          have hk5 : ¬ (5 : ℕ) ∣ (ringChar N) ^ (n + 1) := by
            intro hd
            have h5p : (5 : ℕ) ∣ ringChar N := Nat.Prime.dvd_of_dvd_pow (by norm_num) hd
            exact hN5 ((hp.dvd_iff_eq (a := 5) (by norm_num)).mp h5p)
          have hs5 : FifthPowerValued N (s * (s - 1)) :=
            fifthPowerValued_of_pow hk5 (hfac ▸ hr)
          refine ⟨s, hs1, ?_, hsnonc⟩
          by_cases hDs : D s = 0
          · exact hDs
          · -- `D s ≠ 0`: the counting hypothesis makes `s` constant
            exfalso
            obtain ⟨c, hc⟩ := hmain s hDs hs5
            exact hsnonc c hc
      -- every place divides `ord_Q r` by arbitrary powers of `p`
      have hdvdall : ∀ n : ℕ, (((ringChar N) ^ n : ℕ) : ℤ) ∣ ordP E Q r := by
        intro n
        obtain ⟨f, hfpow, hDf, hfnonc⟩ := key n
        refine ⟨ordP E Q f, ?_⟩
        rw [← hfpow, ordP_pow E H Q (fun h => hfnonc 0 (by rw [h, map_zero]))]
      exact not_dvd_pow_of_ne_zero (p := ringChar N) (by have := hp.two_le; omega) hQ hdvdall
  · -- `D r ≠ 0`: the counting hypothesis applies directly to `r`
    exact hmain r hDr hr

end Work.MotV
