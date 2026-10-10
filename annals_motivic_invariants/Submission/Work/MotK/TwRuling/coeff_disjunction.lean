import Mathlib
import Submission.Work.MotK.TwRuling.KleinJDefs
import Submission.Work.MotK.TwRuling.good_bFive_ne_charFive
import Submission.Work.MotK.TwRuling.good_ne_charTwo_v2
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotK.TwRuling

/-- If `(p : K) = 0` for a prime `p` in a field `K`, then `ringChar K = p`. -/
lemma ringChar_eq_of_prime_cast_eq_zero {K : Type} [Field K] {p : ℕ} (hp : p.Prime)
    (h : (p : K) = 0) : ringChar K = p := by
  have hdvd : ringChar K ∣ p := (ringChar.spec K p).mp h
  rcases hp.eq_one_or_self_of_dvd (ringChar K) hdvd with h1 | hp'
  · exact absurd h1 (CharP.ringChar_ne_one (R := K))
  · exact hp'

/-- **Characteristic `2`.**  From the identity `c₄³ · D⁵ = (kleinC4)³ · Δ` between the
invariants of `D.E` and Fisher's invariants of the Klein quintic `C_{a,b}`, a `Good` datum in
characteristic `2` cannot have `a⁵ = b⁵`: in char `2`, `kleinC4 a b = (a⁵ + b⁵)⁴` vanishes and
`kleinDisc a b = -11·a⁶b⁶` is nonzero, so `c₄³ = 0`, i.e. `j(D.E) = 0`, contradicting `j_ne_zero`. -/
lemma charTwo_ab_ne_of_j (K : Type) [Field K] (D : Work.MotV.KleinData K) (hD : D.Good)
    (h2 : ringChar K = 2)
    (hJ : D.E.c₄ ^ 3 * kleinDisc D.a D.b ^ 5 = kleinC4 D.a D.b ^ 3 * D.E.Δ) :
    D.a ^ 5 ≠ D.b ^ 5 := by
  haveI : CharP K 2 := ringChar.eq_iff.mp h2
  have h2K : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have h11 : (11 : K) ≠ 0 := by
    intro h
    have hd : 2 ∣ 11 := (CharP.cast_eq_zero_iff K 2 11).mp h
    norm_num at hd
  have hDa : D.a ≠ 0 := (mul_ne_zero_iff.mp hD.ab_ne).1
  have hDb : D.b ≠ 0 := (mul_ne_zero_iff.mp hD.ab_ne).2
  intro habs
  -- `kleinC4 a b = (a⁵ + b⁵)⁴ = 0`
  have hc4 : kleinC4 D.a D.b = 0 := by
    unfold kleinC4
    have hkey : D.a ^ 20 + 228 * D.a ^ 15 * D.b ^ 5 + 494 * D.a ^ 10 * D.b ^ 10
        - 228 * D.a ^ 5 * D.b ^ 15 + D.b ^ 20 = (D.a ^ 5 + D.b ^ 5) ^ 4 := by
      linear_combination (norm := first | refl_ring1 | ring1) (112 * D.a ^ 15 * D.b ^ 5 + 244 * D.a ^ 10 * D.b ^ 10
        - 116 * D.a ^ 5 * D.b ^ 15) * h2K
    have hsum : D.a ^ 5 + D.b ^ 5 = 0 := by
      rw [habs]
      have htwo : D.b ^ 5 + D.b ^ 5 = (2 : K) * D.b ^ 5 := by ring
      rw [htwo, h2K, zero_mul]
    rw [hkey, hsum]
    simp
  -- `kleinDisc a b = -11 * a⁶ * b⁶ ≠ 0`
  have hdisc : kleinDisc D.a D.b ≠ 0 := by
    have h10 : D.a ^ 10 = D.a ^ 5 * D.b ^ 5 := by
      rw [show (10 : ℕ) = 5 + 5 by norm_num, pow_add, habs]
    have hb10 : D.b ^ 10 = D.a ^ 5 * D.b ^ 5 := by
      rw [show (10 : ℕ) = 5 + 5 by norm_num, pow_add, ← habs]
    have hsimp : D.a * D.b * (D.a ^ 10 - 11 * D.a ^ 5 * D.b ^ 5 - D.b ^ 10)
        = -11 * (D.a ^ 6 * D.b ^ 6) := by rw [h10, hb10]; ring
    unfold kleinDisc
    rw [hsimp]
    exact mul_ne_zero (neg_ne_zero.mpr h11)
      (mul_ne_zero (pow_ne_zero 6 hDa) (pow_ne_zero 6 hDb))
  -- hence `c₄³ = 0`
  have hc4cubed : D.E.c₄ ^ 3 = 0 := by
    have h := hJ
    rw [hc4] at h
    have h0 : (0 : K) ^ 3 * D.E.Δ = 0 := by
      rw [zero_pow (by norm_num : (3 : ℕ) ≠ 0), zero_mul]
    rw [h0] at h
    exact (mul_eq_zero.mp h).resolve_right (pow_ne_zero 5 hdisc)
  haveI := hD.elliptic
  exact hD.j_ne_zero (D.E.j_eq_zero
    ((pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp hc4cubed))

/-- Over `KbG K`, at least one of `27a⁵ - 11b⁵`, `57a⁵ - b⁵` is nonzero for `a,b` the images of
`D.a, D.b` (`D.Good`).

Route (both reviewers).  Suppose both vanish.  Eliminating `b⁵` (`b⁵ = 57a⁵`) gives
`(27 - 627) a⁵ = -600 a⁵ = 0`; `a ≠ 0` (from `hD.ab_ne`), so `(600 : K) = 0`, i.e. the characteristic
is `2`, `3` or `5` (`600 = 2³·3·5²`; derive this by factoring `600 = (2:K)^3 * (3:K) * (5:K)^2 = 0`
and using `ringChar.spec` + `Nat.dvd_prime` for the primes `2,3,5`).

* characteristic `2`: both forms reduce to `a⁵ - b⁵`, and `good_ne_charTwo` gives `a⁵ ≠ b⁵`;
* characteristic `3`: both forms reduce to `±b⁵ ≠ 0`;
* characteristic `5`: both reduce to `2a⁵ - b⁵`, and `good_bFive_ne_charFive` gives `b⁵ ≠ 2a⁵`.

In each case a contradiction, so both cannot vanish. -/
theorem coeff_disjunction (K : Type) [Field K] (D : Work.MotV.KleinData K) (hD : D.Good) :
    (27 * (algebraMap K (Work.MotK.KbG K) D.a) ^ 5
        - 11 * (algebraMap K (Work.MotK.KbG K) D.b) ^ 5 ≠ 0)
    ∨ (57 * (algebraMap K (Work.MotK.KbG K) D.a) ^ 5
        - (algebraMap K (Work.MotK.KbG K) D.b) ^ 5 ≠ 0) := by
  set A : Work.MotK.KbG K := algebraMap K (Work.MotK.KbG K) D.a with hA
  set B : Work.MotK.KbG K := algebraMap K (Work.MotK.KbG K) D.b with hB
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2⟩ := hcon
  -- `a` and `b` are nonzero
  have hDa : D.a ≠ 0 := (mul_ne_zero_iff.mp hD.ab_ne).1
  have hDb : D.b ≠ 0 := (mul_ne_zero_iff.mp hD.ab_ne).2
  have hA0 : A ≠ 0 := by
    rw [hA]
    exact fun h => hDa ((algebraMap K (Work.MotK.KbG K)).injective (by rw [h, map_zero]))
  have hB0 : B ≠ 0 := by
    rw [hB]
    exact fun h => hDb ((algebraMap K (Work.MotK.KbG K)).injective (by rw [h, map_zero]))
  -- eliminating `b⁵` gives `600 · a⁵ = 0`, hence `(600 : K) = 0`
  have h600R : (600 : Work.MotK.KbG K) = 0 := by
    have h : (600 : Work.MotK.KbG K) * A ^ 5 = 0 := by
      linear_combination (norm := first | refl_ring1 | ring1) -h1 + 11 * h2
    exact (mul_eq_zero.mp h).resolve_right (pow_ne_zero 5 hA0)
  have h600K : (600 : K) = 0 := by
    have hm : algebraMap K (Work.MotK.KbG K) (600 : K) = (600 : Work.MotK.KbG K) :=
      map_ofNat (algebraMap K (Work.MotK.KbG K)) 600
    refine (algebraMap K (Work.MotK.KbG K)).injective ?_
    rw [hm, map_zero]
    exact h600R
  -- factor `600 = 2³ · 3 · 5²`
  have hfac : (2 : K) ^ 3 * (3 : K) * (5 : K) ^ 2 = 0 := by
    rw [← h600K]; norm_num
  rcases mul_eq_zero.mp hfac with h23 | h5sq
  · rcases mul_eq_zero.mp h23 with h2c | h3c
    · -- characteristic `2`: the two forms both become `a⁵ - b⁵`
      have h2K : (2 : K) = 0 := (pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp h2c
      have h2R : (2 : Work.MotK.KbG K) = 0 := by
        have hm : algebraMap K (Work.MotK.KbG K) (2 : K) = (2 : Work.MotK.KbG K) :=
          map_ofNat (algebraMap K (Work.MotK.KbG K)) 2
        rw [← hm, h2K, map_zero]
      have hne : D.a ^ 5 ≠ D.b ^ 5 :=
        good_ne_charTwo_v2 K D hD (ringChar_eq_of_prime_cast_eq_zero (p := 2) (by norm_num) h2K)
      have hAB : A ^ 5 - B ^ 5 = 0 := by
        linear_combination (norm := first | refl_ring1 | ring1) h1 - (13 * A ^ 5 - 5 * B ^ 5) * h2R
      have heq : A ^ 5 = B ^ 5 := sub_eq_zero.mp hAB
      rw [hA, hB] at heq
      exact hne ((algebraMap K (Work.MotK.KbG K)).injective
        (by simpa only [map_pow] using heq))
    · -- characteristic `3`: the second form becomes `-b⁵`
      have h3K : (3 : K) = 0 := h3c
      have h3R : (3 : Work.MotK.KbG K) = 0 := by
        have hm : algebraMap K (Work.MotK.KbG K) (3 : K) = (3 : Work.MotK.KbG K) :=
          map_ofNat (algebraMap K (Work.MotK.KbG K)) 3
        rw [← hm, h3K, map_zero]
      have hB5 : B ^ 5 = 0 := by
        have hneg : -(B ^ 5) = 0 := by
          linear_combination (norm := first | refl_ring1 | ring1) h2 - (19 * A ^ 5) * h3R
        exact neg_eq_zero.mp hneg
      exact hB0 ((pow_eq_zero_iff (by norm_num : (5 : ℕ) ≠ 0)).mp hB5)
  · -- characteristic `5`: both forms become `2a⁵ - b⁵`
    have h5K : (5 : K) = 0 := (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp h5sq
    have h5R : (5 : Work.MotK.KbG K) = 0 := by
      have hm : algebraMap K (Work.MotK.KbG K) (5 : K) = (5 : Work.MotK.KbG K) :=
        map_ofNat (algebraMap K (Work.MotK.KbG K)) 5
      rw [← hm, h5K, map_zero]
    have hne : D.b ^ 5 ≠ 2 * D.a ^ 5 :=
      good_bFive_ne_charFive K D hD (ringChar_eq_of_prime_cast_eq_zero (p := 5) (by norm_num) h5K)
    have hAB : 2 * A ^ 5 - B ^ 5 = 0 := by
      linear_combination (norm := first | refl_ring1 | ring1) h1 - (5 * A ^ 5 - 2 * B ^ 5) * h5R
    have heq : B ^ 5 = 2 * A ^ 5 := (sub_eq_zero.mp hAB).symm
    rw [hA, hB] at heq
    exact hne ((algebraMap K (Work.MotK.KbG K)).injective
      (by simpa only [map_pow, map_mul, map_ofNat] using heq))

#print axioms Work.MotK.TwRuling.coeff_disjunction

end Work.MotK.TwRuling
