import Mathlib
import Submission.Work.LinnikBurgess.cftValAddLt
import Submission.Work.LinnikBurgess.cftValOneLe
import Submission.Work.LinnikBurgess.cftValPowMul
import Submission.Work.LinnikBurgess.cftTaylorSq
import Submission.Work.LinnikBurgess.cftCountDvd
import Submission.Work.LinnikBurgess.cftCountVal
import Submission.Work.LinnikBurgess.cftCountClass
import Submission.Work.LinnikBurgess.cftCoeffCompMulX
import Submission.Work.LinnikBurgess.cftDerivSubCoeffOne
import Submission.Work.LinnikBurgess.cftDvdEvalCoeff
import Submission.Work.LinnikBurgess.cftEvalDivX
import Submission.Work.LinnikBurgess.cftSimpleRoots

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The "fiber at level `ν`" cap-content bound for a quartic

For a prime `p ≥ 5`, a polynomial `Q ∈ ℤ[X]` of degree at most `4` and integers `ν ≥ 1`, the set of
`y < p ^ M` with `p ∣ Q'(y)`, `v_p (Q'(y)) = ν` and `p ∤ Q''(y)` has at most `3 * p ^ (M - ν)`
elements.

The mathematical content is a Hensel-type counting argument, organised here as follows.

* `cftValEvalStep`/`cftStepTrich`: at a multiple of `p`, the valuation of `G` is governed by the
  minimum of `v_p (G 0)` and `1 + v_p (t)` (sharp non-archimedean property, `cftValAddLt`).
* `cftLift`/`cftBase`/`pLinearCount`: a polynomial whose reduction modulo `p` is an affine
  function with unit slope has at most `p ^ (N - ν)` points `x < p ^ N` of valuation exactly `ν`
  (one root class modulo `p ^ k` for every `k`, built by Hensel lifting).
* `pMultipleCount`: consequently a polynomial `G` with `p ∣ G(0)` and `p ∤ G'(0)` has at most
  `p ^ (N + 1 - ν)` points `t < p ^ N` with `v_p (G (p t)) = ν`.
* `cftMemR`, `cftFiberBound`, `cftMainAux`: the elements of `S` are split according to the residue
  class of `y` modulo `p`; each of the at most `3` admissible classes contributes at most
  `p ^ (M - ν)`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

open Polynomial

namespace Work.LinnikBurgess

/-! ## My own elementary helpers -/

/-- The other half of non-archimedeanness: the valuation of a sum is at least the minimum. -/
lemma cftValAddGeMin {p : ℕ} [Fact p.Prime] {x y : ℤ} (hxy : x + y ≠ 0) :
    min (padicValInt p x) (padicValInt p y) ≤ padicValInt p (x + y) := by
  have hxy' : ((x : ℚ)) + ((y : ℚ)) = (((x + y : ℤ)) : ℚ) := by push_cast; ring
  have hz : ((x : ℚ)) + ((y : ℚ)) ≠ 0 := by rw [hxy']; exact_mod_cast hxy
  have key := padicValRat.min_le_padicValRat_add (p := p) (q := ((x : ℚ))) (r := ((y : ℚ))) hz
  rw [padicValRat.of_int, padicValRat.of_int, hxy', padicValRat.of_int, ← Nat.cast_min] at key
  exact_mod_cast key

/-- The difference between the value of a polynomial and its value at a point is divisible by
the difference of the points (Mathlib's `Polynomial.sub_dvd_eval_sub`, restated). -/
lemma cftDvdEvalSub' (G : Polynomial ℤ) (x y : ℤ) : (x - y) ∣ (G.eval x - G.eval y) :=
  Polynomial.sub_dvd_eval_sub x y G

/-- The value of `divX G` at a multiple `p * t` is congruent to its value at `0` modulo `p`. -/
lemma cftDivX_congr {p : ℕ} (G : Polynomial ℤ) (t : ℤ) :
    (p : ℤ) ∣ (G.divX.eval ((p : ℤ) * t) - G.divX.eval 0) := by
  have h := Polynomial.sub_dvd_eval_sub ((p : ℤ) * t) 0 G.divX
  have : (((p : ℤ) * t) - 0) = (p : ℤ) * t := by ring
  rw [this] at h
  exact dvd_trans (dvd_mul_right _ _) h

/-! ## Lemma A: counting a linear-mod-`p` polynomial by exact valuation -/

/-- Lifting step: given a root class `c` modulo `p ^ k` of `F` (with `F` linear modulo `p` with
unit slope), there is a unique lifting to a root class modulo `p ^ (k+1)`. -/
lemma cftTaylorCongr {p : ℕ} [Fact p.Prime] {G : Polynomial ℤ} {k : ℕ} (hk : 1 ≤ k) (c t : ℤ) :
    ((p : ℤ) ^ (k + 1)) ∣ (G.eval (c + (p : ℤ) ^ k * t) - G.eval c
      - (p : ℤ) ^ k * t * G.derivative.eval c) := by
  have h := cftTaylorSq G (c + (p : ℤ) ^ k * t) c
  have hdiff : (c + (p : ℤ) ^ k * t) - c = (p : ℤ) ^ k * t := by ring
  rw [hdiff] at h
  have h1 : ((p : ℤ) ^ (k + 1)) ∣ ((p : ℤ) ^ k * t) ^ 2 := by
    have he : ((p : ℤ) ^ k * t) ^ 2 = ((p : ℤ) ^ (2 * k)) * t ^ 2 := by
      rw [mul_pow, ← pow_mul, Nat.mul_comm]
    rw [he]
    exact dvd_mul_of_dvd_left (pow_dvd_pow ((p : ℤ)) (show k + 1 ≤ 2 * k by omega)) _
  exact dvd_trans h1 h




/-! ## Linearisation -/

/-- If all coefficients of `F` of degree `≥ 2` are divisible by `p`, then `F` is affine modulo
`p`. -/
lemma cftLinear {p : ℕ} [Fact p.Prime] {F : Polynomial ℤ}
    (h2 : ∀ i, 2 ≤ i → (p : ℤ) ∣ F.coeff i) (x : ℤ) :
    (p : ℤ) ∣ F.eval x - (F.coeff 0 + F.coeff 1 * x) := by
  have hG : ∀ i, (p : ℤ) ∣ (F - C (F.coeff 0) - C (F.coeff 1) * X).coeff i := by
    intro i
    have hco : (F - C (F.coeff 0) - C (F.coeff 1) * X).coeff i
        = F.coeff i - (if i = 0 then F.coeff 0 else 0) - (if 1 = i then F.coeff 1 else 0) := by
      rw [Polynomial.coeff_sub, Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_C,
        Polynomial.coeff_X]
      split_ifs <;> ring
    rcases lt_or_ge i 2 with hi | hi
    · interval_cases i
      · rw [hco]; simp
      · rw [hco]; simp
    · rw [hco]
      have h0 : (if i = 0 then F.coeff 0 else 0) = 0 := if_neg (by omega)
      have h1' : (if 1 = i then F.coeff 1 else 0) = 0 := if_neg (by omega)
      rw [h0, h1']
      simpa using h2 i hi
  have h := cftDvdEvalCoeff (p := p) (F - C (F.coeff 0) - C (F.coeff 1) * X) hG x
  have he : (F - C (F.coeff 0) - C (F.coeff 1) * X).eval x
      = F.eval x - (F.coeff 0 + F.coeff 1 * x) := by
    simp [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    ring
  rwa [he] at h

/-- `x ≡ y (mod p)` gives `F x ≡ F y (mod p)`. -/
lemma cftEvalCongr {p : ℕ} (F : Polynomial ℤ) {x y : ℤ} (h : (p : ℤ) ∣ x - y) :
    (p : ℤ) ∣ F.eval x - F.eval y :=
  dvd_trans h (cftDvdEvalSub' F x y)

/-- Positional bound used by the lifting step. -/
lemma cftLiftBound {p k : ℕ} (hppos : 0 < p) {c t : ℕ} (hc : c < p ^ k) (ht : t < p) :
    c + p ^ k * t < p ^ (k + 1) := by
  have hwle : t ≤ p - 1 := by omega
  have h1 : c + p ^ k * t < p ^ k + p ^ k * t := Nat.add_lt_add_right hc _
  have h2 : p ^ k + p ^ k * t ≤ p ^ k + p ^ k * (p - 1) :=
    Nat.add_le_add_left (Nat.mul_le_mul_left _ hwle) _
  have h3 : p ^ k + p ^ k * (p - 1) = p ^ (k + 1) := by
    have hp1 : p - 1 + 1 = p := Nat.sub_add_cancel (by omega : 1 ≤ p)
    calc p ^ k + p ^ k * (p - 1) = p ^ k * (p - 1) + p ^ k * 1 := by ring
      _ = p ^ k * ((p - 1) + 1) := by rw [Nat.mul_add]
      _ = p ^ k * p := by rw [hp1]
      _ = p ^ (k + 1) := by rw [pow_succ]
  omega

/-! ## The Hensel lifting step -/

/-- Lifting step for a polynomial that is affine modulo `p` with unit slope: a root class of `F`
modulo `p ^ k` lifts to a unique root class modulo `p ^ (k + 1)`. -/
lemma cftLift {p : ℕ} [Fact p.Prime] {F : Polynomial ℤ}
    (h2 : ∀ i, 2 ≤ i → (p : ℤ) ∣ F.coeff i) (h1 : ¬ (p : ℤ) ∣ F.coeff 1)
    {k : ℕ} (hk : 1 ≤ k) {c : ℕ} (hc : c < p ^ k)
    (hdvd : ((p : ℤ) ^ k) ∣ F.eval (c : ℤ))
    (huniq : ∀ x : ℕ, ((p : ℤ) ^ k) ∣ F.eval (x : ℤ) → x % p ^ k = c) :
    ∃ c' : ℕ, c' < p ^ (k + 1) ∧ ((p : ℤ) ^ (k + 1)) ∣ F.eval (c' : ℤ) ∧
      ∀ x : ℕ, ((p : ℤ) ^ (k + 1)) ∣ F.eval (x : ℤ) → x % p ^ (k + 1) = c' := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hppos : 0 < p := (Fact.out : p.Prime).pos
  obtain ⟨A, hA⟩ : ∃ A : ℤ, F.eval (c : ℤ) = (p : ℤ) ^ k * A :=
    ⟨F.eval (c : ℤ) / (p : ℤ) ^ k, (Int.mul_ediv_cancel' hdvd).symm⟩
  have hder : ¬ (p : ℤ) ∣ F.derivative.eval (c : ℤ) := by
    intro h
    have hsub := cftDerivSubCoeffOne (p := p) F h2 (c : ℤ)
    have hdiff : (p : ℤ) ∣ F.derivative.eval (c : ℤ)
        - (F.derivative.eval (c : ℤ) - F.coeff 1) := dvd_sub h hsub
    have he : F.derivative.eval (c : ℤ) - (F.derivative.eval (c : ℤ) - F.coeff 1) = F.coeff 1 := by
      ring
    rw [he] at hdiff
    exact h1 hdiff
  have hder_ne : (((F.derivative.eval (c : ℤ) : ℤ)) : ZMod p) ≠ 0 := fun h =>
    hder ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h)
  set w : ZMod p := -((A : ZMod p)) / ((F.derivative.eval (c : ℤ) : ℤ) : ZMod p) with hw
  have hwroot : (A : ZMod p) + w * ((F.derivative.eval (c : ℤ) : ℤ) : ZMod p) = 0 := by
    rw [hw]; field_simp; ring
  have hwval : ((w.val : ℕ) : ZMod p) = w := ZMod.natCast_zmod_val w
  have hclt : c + p ^ k * w.val < p ^ (k + 1) := cftLiftBound hppos hc (ZMod.val_lt w)
  refine ⟨c + p ^ k * w.val, hclt, ?_, ?_⟩
  · -- divisibility at `c'`
    have hkey : (p : ℤ) ∣ A + ((w.val : ℤ)) * F.derivative.eval (c : ℤ) := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, hwval]
      exact hwroot
    have hmul : ((p : ℤ) ^ (k + 1)) ∣
        (p : ℤ) ^ k * (A + ((w.val : ℤ)) * F.derivative.eval (c : ℤ)) := by
      rw [pow_succ]
      exact mul_dvd_mul_left _ hkey
    have hT := cftTaylorCongr (p := p) (G := F) hk (c : ℤ) ((w.val : ℤ))
    have hsum := dvd_add hT hmul
    rw [hA] at hsum
    have hgoal : F.eval (((c + p ^ k * w.val : ℕ)) : ℤ)
        = (F.eval ((c : ℤ) + (p : ℤ) ^ k * ((w.val : ℤ)))
            - (p : ℤ) ^ k * A - (p : ℤ) ^ k * ((w.val : ℤ)) * F.derivative.eval (c : ℤ))
          + ((p : ℤ) ^ k * (A + ((w.val : ℤ)) * F.derivative.eval (c : ℤ))) := by
      have hcast : ((c + p ^ k * w.val : ℕ) : ℤ) = (c : ℤ) + (p : ℤ) ^ k * ((w.val : ℤ)) := by
        push_cast; ring
      rw [hcast]; ring
    rw [hgoal]
    exact hsum
  · -- uniqueness
    intro x hx
    have hk_dvd : ((p : ℤ) ^ k) ∣ F.eval (x : ℤ) := dvd_trans (pow_dvd_pow _ (by omega)) hx
    have hxc : x % p ^ k = c := huniq x hk_dvd
    set t : ℕ := x / p ^ k with ht
    have hx_eq : x = c + p ^ k * t := by
      have h := Nat.div_add_mod x (p ^ k)
      rw [hxc, ← ht] at h
      omega
    have hcong : (p : ℤ) ∣ A + (t : ℤ) * F.derivative.eval (c : ℤ) := by
      have hT := cftTaylorCongr (p := p) (G := F) hk (c : ℤ) (t : ℤ)
      have hxe : ((x : ℤ)) = (c : ℤ) + (p : ℤ) ^ k * (t : ℤ) := by
        rw [hx_eq]; push_cast; ring
      rw [← hxe] at hT
      have h1' : ((p : ℤ) ^ (k + 1)) ∣
          F.eval (c : ℤ) + (p : ℤ) ^ k * (t : ℤ) * F.derivative.eval (c : ℤ) := by
        have hsub := dvd_sub hx hT
        have he : (F.eval (↑x) - (F.eval (↑x) - F.eval (↑c)
            - ↑p ^ k * (↑t) * F.derivative.eval (↑c)))
            = F.eval (↑c) + ↑p ^ k * (↑t) * F.derivative.eval (↑c) := by ring
        rwa [he] at hsub
      rw [hA] at h1'
      have hfac : (p : ℤ) ^ k * (A + (t : ℤ) * F.derivative.eval (c : ℤ))
          = (p : ℤ) ^ k * A + (p : ℤ) ^ k * (t : ℤ) * F.derivative.eval (c : ℤ) := by ring
      rw [← hfac] at h1'
      rw [pow_succ] at h1'
      have hpne : ((p : ℤ) ^ k) ≠ 0 := pow_ne_zero _ (by positivity)
      exact (mul_dvd_mul_iff_left hpne).mp h1'
    have htZ : (t : ZMod p) = w := by
      have hc0 : ((A + (t : ℤ) * F.derivative.eval (c : ℤ) : ℤ) : ZMod p) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hcong
      push_cast at hc0
      have hmul : (t : ZMod p) * ((F.derivative.eval (c : ℤ) : ℤ) : ZMod p)
          = w * ((F.derivative.eval (c : ℤ) : ℤ) : ZMod p) := by
        have h1 : (t : ZMod p) * ((F.derivative.eval (c : ℤ) : ℤ) : ZMod p)
            = -((A : ZMod p)) := by linear_combination hc0
        have h2 : w * ((F.derivative.eval (c : ℤ) : ℤ) : ZMod p) = -((A : ZMod p)) := by
          linear_combination hwroot
        rw [h1, h2]
      exact mul_right_cancel₀ hder_ne hmul
    have htmod : t % p = w.val := by
      have hcast : ((t % p : ℕ) : ZMod p) = ((w.val : ℕ) : ZMod p) := by
        rw [ZMod.natCast_mod, htZ, ZMod.natCast_zmod_val]
      have := congrArg ZMod.val hcast
      rwa [ZMod.val_natCast_of_lt (Nat.mod_lt _ hppos),
        ZMod.val_natCast_of_lt (ZMod.val_lt w)] at this
    have hm1 : p ^ k * t ≡ p ^ k * w.val [MOD p ^ (k + 1)] := by
      have ht' : t ≡ w.val [MOD p] := by
        rw [Nat.ModEq, htmod, Nat.mod_eq_of_lt (ZMod.val_lt w)]
      rw [pow_succ]
      exact Nat.ModEq.mul_left' (p ^ k) ht'
    have hmod : x ≡ c + p ^ k * w.val [MOD p ^ (k + 1)] := by
      rw [hx_eq]
      exact Nat.ModEq.add_left _ hm1
    rw [Nat.ModEq] at hmod
    rw [hmod, Nat.mod_eq_of_lt hclt]


/-! ## Base case and main counting lemma for affine-modulo-`p` polynomials -/

/-- Base case: modulo `p` an affine polynomial with unit slope has exactly one root class. -/
lemma cftBase {p : ℕ} [Fact p.Prime] {F : Polynomial ℤ}
    (h2 : ∀ i, 2 ≤ i → (p : ℤ) ∣ F.coeff i) (h1 : ¬ (p : ℤ) ∣ F.coeff 1) :
    ∃ c : ℕ, c < p ^ 1 ∧ ((p : ℤ) ^ 1) ∣ F.eval (c : ℤ) ∧
      ∀ x : ℕ, ((p : ℤ) ^ 1) ∣ F.eval (x : ℤ) → x % p ^ 1 = c := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hppos : 0 < p := (Fact.out : p.Prime).pos
  have hf1 : ((F.coeff 1 : ℤ) : ZMod p) ≠ 0 := fun h =>
    h1 ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h)
  set z : ZMod p := -((F.coeff 0 : ℤ) : ZMod p) / ((F.coeff 1 : ℤ) : ZMod p) with hz
  have hzroot : ((F.coeff 0 : ℤ) : ZMod p) + ((F.coeff 1 : ℤ) : ZMod p) * z = 0 := by
    rw [hz]; field_simp; ring
  have hzcast : (z : ZMod p) = ((z.val : ℕ) : ZMod p) := (ZMod.natCast_zmod_val z).symm
  refine ⟨z.val, by simpa using ZMod.val_lt z, ?_, ?_⟩
  · have hbracket : (p : ℤ) ∣ F.coeff 0 + F.coeff 1 * ((z.val : ℕ) : ℤ) := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [← hzcast]
      exact hzroot
    have hlin := cftLinear (p := p) h2 ((z.val : ℕ) : ℤ)
    have hthis := dvd_add hlin hbracket
    rw [sub_add_cancel] at hthis
    simpa using hthis
  · intro x hx
    rw [pow_one] at hx
    have hxroot : ((F.coeff 0 : ℤ) : ZMod p) + ((F.coeff 1 : ℤ) : ZMod p) * (x : ZMod p) = 0 := by
      have hlin := cftLinear (p := p) h2 (x : ℤ)
      have hb : (p : ℤ) ∣ F.coeff 0 + F.coeff 1 * (x : ℤ) := by
        have hbb := dvd_sub hx hlin
        have he : F.eval (x : ℤ) - (F.eval (x : ℤ) - (F.coeff 0 + F.coeff 1 * (x : ℤ)))
            = F.coeff 0 + F.coeff 1 * (x : ℤ) := by ring
        rwa [he] at hbb
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hb
      simpa using this
    have hxz : (x : ZMod p) = z := by
      have hmul : (x : ZMod p) * ((F.coeff 1 : ℤ) : ZMod p)
          = z * ((F.coeff 1 : ℤ) : ZMod p) := by
        have h1' : (x : ZMod p) * ((F.coeff 1 : ℤ) : ZMod p) = -((F.coeff 0 : ℤ) : ZMod p) := by
          linear_combination hxroot
        have h2' : z * ((F.coeff 1 : ℤ) : ZMod p) = -((F.coeff 0 : ℤ) : ZMod p) := by
          linear_combination hzroot
        rw [h1', h2']
      exact mul_right_cancel₀ hf1 hmul
    rw [pow_one]
    have hcast : ((x % p : ℕ) : ZMod p) = ((z.val : ℕ) : ZMod p) := by
      rw [ZMod.natCast_mod, hxz, ZMod.natCast_zmod_val]
    have := congrArg ZMod.val hcast
    rwa [ZMod.val_natCast_of_lt (Nat.mod_lt _ hppos), ZMod.val_natCast_of_lt (ZMod.val_lt z)] at this

/-- **Counting lemma for affine-modulo-`p` polynomials.**  If all coefficients of `F` of degree
`≥ 2` vanish modulo `p` and the linear coefficient is a unit modulo `p`, then the number of
`x < p ^ N` with `v_p(F(x)) = ν` is at most `p ^ (N - ν)`. -/
lemma pLinearCount {p : ℕ} [Fact p.Prime] {F : Polynomial ℤ}
    (h2 : ∀ i, 2 ≤ i → (p : ℤ) ∣ F.coeff i) (h1 : ¬ (p : ℤ) ∣ F.coeff 1)
    (ν : ℕ) (hν : 1 ≤ ν) (N : ℕ) :
    ((Finset.range (p ^ N)).filter (fun x : ℕ => padicValInt p (F.eval (x : ℤ)) = ν)).card
      ≤ p ^ (N - ν) := by
  classical
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have star : ∀ k : ℕ, 1 ≤ k → ∃ c : ℕ, c < p ^ k ∧ ((p : ℤ) ^ k) ∣ F.eval (c : ℤ) ∧
      ∀ x : ℕ, ((p : ℤ) ^ k) ∣ F.eval (x : ℤ) → x % p ^ k = c := by
    intro k
    induction k with
    | zero => intro hk; exact absurd hk (by omega)
    | succ k ih =>
      intro hk
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · subst hk0
        exact cftBase h2 h1
      · obtain ⟨c, hclt, hcdvd, hcuni⟩ := ih hkpos
        exact cftLift h2 h1 hkpos hclt hcdvd hcuni
  obtain ⟨c, hclt, hcdvd, hcuni⟩ := star ν hν
  refine le_trans (Finset.card_le_card ?_) (cftCountClass hp2 hclt)
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢
  exact ⟨hx.1, hcuni x ((padicValInt_dvd_iff ν (F.eval (x : ℤ))).mpr
    (Or.inr (le_of_eq hx.2.symm)))⟩


/-! ## Lemma B: the `p`-multiple form -/

/-- Value of `G` at a multiple of `p`, compared with `min (v_p (G 0)) (1 + v_p t)`. -/
lemma cftValEvalStep {p : ℕ} [Fact p.Prime] {G : Polynomial ℤ}
    (hU : ∀ t : ℕ, ¬ (p : ℤ) ∣ G.divX.eval ((p : ℤ) * (t : ℤ)))
    {t : ℕ} (ht : t ≠ 0) (ha : G.eval 0 ≠ 0)
    (hne : G.eval ((p : ℤ) * (t : ℤ)) ≠ 0) :
    min (padicValInt p (G.eval 0)) (1 + padicValNat p t)
        ≤ padicValInt p (G.eval ((p : ℤ) * (t : ℤ)))
      ∧ (1 + padicValNat p t ≠ padicValInt p (G.eval 0) →
          padicValInt p (G.eval ((p : ℤ) * (t : ℤ)))
            = min (padicValInt p (G.eval 0)) (1 + padicValNat p t)) := by
  have hpZ : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have htZ : (t : ℤ) ≠ 0 := by exact_mod_cast ht
  have hpt : ((p : ℤ) * (t : ℤ)) ≠ 0 := mul_ne_zero hpZ htZ
  have hUne : G.divX.eval ((p : ℤ) * (t : ℤ)) ≠ 0 := fun h => hU t (by rw [h]; exact dvd_zero _)
  have hprod : padicValInt p ((p : ℤ) * (t : ℤ) * G.divX.eval ((p : ℤ) * (t : ℤ)))
      = 1 + padicValNat p t := by
    rw [padicValInt.mul hpt hUne]
    have h1 : padicValInt p ((p : ℤ) * (t : ℤ)) = 1 + padicValInt p (t : ℤ) := by
      have h := cftValPowMul (p := p) 1 (z := (t : ℤ)) htZ
      simpa using h
    rw [h1, padicValInt.of_nat, padicValInt.eq_zero_of_not_dvd (hU t)]
    ring
  have heval := (cftEvalDivX G ((p : ℤ) * (t : ℤ))).1
  set a := G.eval 0 with hadef
  set b := (p : ℤ) * (t : ℤ) * G.divX.eval ((p : ℤ) * (t : ℤ)) with hbdef
  have hbne : b ≠ 0 := by rw [hbdef]; exact mul_ne_zero hpt hUne
  have hane : a ≠ 0 := by rw [hadef]; exact ha
  have hsum : a + b = G.eval ((p : ℤ) * (t : ℤ)) := by
    rw [hadef, hbdef, heval]
  have hbval : padicValInt p b = 1 + padicValNat p t := by rw [hbdef]; exact hprod
  constructor
  · have hge := cftValAddGeMin (p := p) (x := a) (y := b) (by rw [hsum]; exact hne)
    rw [hbval, hsum] at hge
    exact hge
  · intro hne2
    rcases lt_trichotomy (1 + padicValNat p t) (padicValInt p a) with hlt | heq | hgt
    · have hb_lt : padicValInt p b < padicValInt p a := by rw [hbval]; exact hlt
      have hstep := cftValAddLt (p := p) hbne hane hb_lt
      rw [hbval, add_comm b a, hsum] at hstep
      rw [hstep, min_eq_right (le_of_lt hlt)]
    · exact absurd heq hne2
    · have hb_gt : padicValInt p a < padicValInt p b := by rw [hbval]; exact hgt
      have hstep := cftValAddLt (p := p) hane hbne hb_gt
      rw [hsum] at hstep
      rw [hstep, min_eq_left (le_of_lt hgt)]

/-- Trichotomy for the value of `G` at a multiple of `p`. -/
lemma cftStepTrich {p : ℕ} [Fact p.Prime] {G : Polynomial ℤ}
    (hU : ∀ t : ℕ, ¬ (p : ℤ) ∣ G.divX.eval ((p : ℤ) * (t : ℤ)))
    (ha : G.eval 0 ≠ 0) {t : ℕ} (ht : t ≠ 0) {ν : ℕ} (hν : 1 ≤ ν)
    (hval : padicValInt p (G.eval ((p : ℤ) * (t : ℤ))) = ν) :
    (1 + padicValNat p t < padicValInt p (G.eval 0)
        ∧ ν = 1 + padicValNat p t)
      ∨ (1 + padicValNat p t = padicValInt p (G.eval 0)
        ∧ padicValInt p (G.eval 0) ≤ ν)
      ∨ (padicValInt p (G.eval 0) < 1 + padicValNat p t
        ∧ ν = padicValInt p (G.eval 0)) := by
  have hne : G.eval ((p : ℤ) * (t : ℤ)) ≠ 0 := by
    intro h; rw [h, padicValInt.zero] at hval; omega
  obtain ⟨hmin, heqmin⟩ := cftValEvalStep hU ht ha hne
  rcases lt_trichotomy (1 + padicValNat p t) (padicValInt p (G.eval 0)) with h1 | h2 | h3
  · left
    have := heqmin (by omega)
    rw [min_eq_right (le_of_lt h1)] at this
    exact ⟨h1, hval.symm.trans this⟩
  · right; left
    refine ⟨h2, ?_⟩
    have := hmin
    rw [h2, min_self] at this
    omega
  · right; right
    have := heqmin (by omega)
    rw [min_eq_left (le_of_lt h3)] at this
    exact ⟨h3, hval.symm.trans this⟩

/-- **Counting lemma, `p`-multiple form.**  For `G` with `p ∣ G(0)` and `p ∤ G'(0)`, the number
of `t < p ^ N` with `v_p (G (p t)) = ν` is at most `p ^ (N + 1 - ν)`. -/
lemma pMultipleCount {p : ℕ} [Fact p.Prime] {G : Polynomial ℤ}
    (h0 : (p : ℤ) ∣ G.eval 0) (h1 : ¬ (p : ℤ) ∣ G.derivative.eval 0)
    (ν : ℕ) (hν : 1 ≤ ν) (N : ℕ) :
    ((Finset.range (p ^ N)).filter
        (fun t : ℕ => padicValInt p (G.eval ((p : ℤ) * (t : ℤ))) = ν)).card
      ≤ p ^ (N + 1 - ν) := by
  classical
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hpZ : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hU0 : G.divX.eval 0 = G.derivative.eval 0 := (cftEvalDivX G 0).2
  have hUunit : ∀ t : ℕ, ¬ (p : ℤ) ∣ G.divX.eval ((p : ℤ) * (t : ℤ)) := by
    intro t hdvd
    apply h1
    rw [← hU0]
    have hcong := cftDivX_congr (p := p) G (t : ℤ)
    have hthis := dvd_sub hdvd hcong
    have he : G.divX.eval ((p : ℤ) * (t : ℤ))
        - (G.divX.eval ((p : ℤ) * (t : ℤ)) - G.divX.eval 0) = G.divX.eval 0 := by ring
    rwa [he] at hthis
  by_cases ha0 : G.eval 0 = 0
  · have hsub0 : ((Finset.range (p ^ N)).filter
          (fun t : ℕ => padicValInt p (G.eval ((p : ℤ) * (t : ℤ))) = ν))
        ⊆ ((Finset.range (p ^ N)).filter (fun t : ℕ => padicValNat p t = ν - 1)) := by
      intro t ht
      simp only [Finset.mem_filter, Finset.mem_range] at ht ⊢
      refine ⟨ht.1, ?_⟩
      have htne : t ≠ 0 := by
        rintro rfl
        rw [Nat.cast_zero, mul_zero, ha0, padicValInt.zero] at ht
        omega
      have hUne : G.divX.eval ((p : ℤ) * (t : ℤ)) ≠ 0 :=
        fun h => hUunit t (by rw [h]; exact dvd_zero _)
      have htZ : (t : ℤ) ≠ 0 := by exact_mod_cast htne
      have hprod : padicValInt p ((p : ℤ) * (t : ℤ) * G.divX.eval ((p : ℤ) * (t : ℤ)))
          = 1 + padicValNat p t := by
        rw [padicValInt.mul (mul_ne_zero hpZ htZ) hUne]
        have h1' : padicValInt p ((p : ℤ) * (t : ℤ)) = 1 + padicValInt p (t : ℤ) := by
          have h := cftValPowMul (p := p) 1 (z := (t : ℤ)) htZ
          simpa using h
        rw [h1', padicValInt.of_nat, padicValInt.eq_zero_of_not_dvd (hUunit t)]
        ring
      have heval := (cftEvalDivX G ((p : ℤ) * (t : ℤ))).1
      rw [ha0, zero_add] at heval
      rw [heval, hprod] at ht
      omega
    calc ((Finset.range (p ^ N)).filter
          (fun t : ℕ => padicValInt p (G.eval ((p : ℤ) * (t : ℤ))) = ν)).card
        ≤ ((Finset.range (p ^ N)).filter (fun t : ℕ => padicValNat p t = ν - 1)).card :=
          Finset.card_le_card hsub0
      _ ≤ p ^ (N - (ν - 1)) := cftCountVal hp2
      _ = p ^ (N + 1 - ν) := by
          rw [show N - (ν - 1) = N + 1 - ν by omega]
  · have ha1 : 1 ≤ padicValInt p (G.eval 0) := (cftValOneLe ha0).mpr h0
    set c := padicValInt p (G.eval 0) with hcdef
    rcases lt_trichotomy ν c with hlt | heq | hgt
    · -- ν < c : every solution has v_p(t) = ν - 1
      have hsub : ((Finset.range (p ^ N)).filter
            (fun t : ℕ => padicValInt p (G.eval ((p : ℤ) * (t : ℤ))) = ν))
          ⊆ ((Finset.range (p ^ N)).filter (fun t : ℕ => padicValNat p t = ν - 1)) := by
        intro t ht
        simp only [Finset.mem_filter, Finset.mem_range] at ht ⊢
        refine ⟨ht.1, ?_⟩
        have htne : t ≠ 0 := by
          rintro rfl
          rw [Nat.cast_zero, mul_zero] at ht
          rw [← hcdef] at ht
          omega
        rcases cftStepTrich hUunit ha0 htne hν ht.2 with ⟨-, hνeq⟩ | ⟨heqc, hcle⟩ | ⟨hgt', hνeq⟩
        · omega
        · omega
        · omega
      calc ((Finset.range (p ^ N)).filter
            (fun t : ℕ => padicValInt p (G.eval ((p : ℤ) * (t : ℤ))) = ν)).card
          ≤ ((Finset.range (p ^ N)).filter (fun t : ℕ => padicValNat p t = ν - 1)).card :=
            Finset.card_le_card hsub
        _ ≤ p ^ (N - (ν - 1)) := cftCountVal hp2
        _ = p ^ (N + 1 - ν) := by
            rw [show N - (ν - 1) = N + 1 - ν by omega]
    · -- ν = c : every solution lies in the residue class 0 mod p^(c-1)
      have hsub : ((Finset.range (p ^ N)).filter
            (fun t : ℕ => padicValInt p (G.eval ((p : ℤ) * (t : ℤ))) = ν))
          ⊆ ((Finset.range (p ^ N)).filter (fun t : ℕ => p ^ (c - 1) ∣ t)) := by
        intro t ht
        simp only [Finset.mem_filter, Finset.mem_range] at ht ⊢
        refine ⟨ht.1, ?_⟩
        by_cases ht0 : t = 0
        · rw [ht0]; exact dvd_zero _
        · rcases cftStepTrich hUunit ha0 ht0 hν ht.2 with ⟨hlt', hνeq⟩ | ⟨heqc, -⟩ | ⟨hgt', hνeq⟩
          · omega
          · exact (Nat.pow_dvd_iff_le_padicValNat (by omega : p ≠ 1) ht0).mpr (by omega)
          · exact (Nat.pow_dvd_iff_le_padicValNat (by omega : p ≠ 1) ht0).mpr (by omega)
      calc ((Finset.range (p ^ N)).filter
            (fun t : ℕ => padicValInt p (G.eval ((p : ℤ) * (t : ℤ))) = ν)).card
          ≤ ((Finset.range (p ^ N)).filter (fun t : ℕ => p ^ (c - 1) ∣ t)).card :=
            Finset.card_le_card hsub
        _ ≤ p ^ (N - (c - 1)) := cftCountDvd hp2
        _ = p ^ (N + 1 - ν) := by
            rw [show N - (c - 1) = N + 1 - ν by omega]
    · -- ν > c : reduce to the affine case by substituting t = p^(c-1) * s
      obtain ⟨A, hA⟩ : ∃ A : ℤ, G.eval 0 = (p : ℤ) ^ c * A :=
        ⟨G.eval 0 / (p : ℤ) ^ c, (Int.mul_ediv_cancel' (by
          have h := padicValInt_dvd (p := p) (G.eval 0)
          rw [← hcdef] at h
          exact h)).symm⟩
      set Ê : Polynomial ℤ := C A + (G.divX.comp (C ((p : ℤ) ^ c) * X)) * X with hEdef
      have hcpos : 1 ≤ c := ha1
      have hEeval : ∀ s : ℤ, Ê.eval s = A + s * G.divX.eval ((p : ℤ) ^ c * s) := by
        intro s
        rw [hEdef]
        simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
          Polynomial.eval_comp]
        ring
      have hEcoeff2 : ∀ i, 2 ≤ i → (p : ℤ) ∣ Ê.coeff i := by
        intro i hi
        rw [hEdef]
        have hco : (C A + (G.divX.comp (C ((p : ℤ) ^ c) * X)) * X).coeff i
            = (G.divX.comp (C ((p : ℤ) ^ c) * X)).coeff (i - 1) := by
          rw [Polynomial.coeff_add, Polynomial.coeff_C, if_neg (by omega), zero_add]
          rcases i with _ | j
          · omega
          · rw [Polynomial.coeff_mul_X]
            simp
        rw [hco, cftCoeffCompMulX, ← pow_mul]
        have hci : 1 ≤ c * (i - 1) :=
          Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
        simpa using dvd_mul_of_dvd_right (pow_dvd_pow ((p : ℤ)) hci) (G.divX.coeff (i - 1))
      have hEcoeff1 : ¬ (p : ℤ) ∣ Ê.coeff 1 := by
        rw [hEdef]
        have hco : (C A + (G.divX.comp (C ((p : ℤ) ^ c) * X)) * X).coeff 1 = G.divX.eval 0 := by
          rw [Polynomial.coeff_add, Polynomial.coeff_C, if_neg (by norm_num), zero_add,
            Polynomial.coeff_mul_X, cftCoeffCompMulX]
          simp only [pow_zero, mul_one, Polynomial.coeff_zero_eq_eval_zero]
        rw [hco, hU0]
        exact h1
      have key : ∀ t : ℕ, t ∈ (Finset.range (p ^ N)).filter
            (fun t : ℕ => padicValInt p (G.eval ((p : ℤ) * (t : ℤ))) = ν) →
          (1 + padicValNat p t = c ∧ p ^ (c - 1) ∣ t
            ∧ t = p ^ (c - 1) * (t / p ^ (c - 1))) := by
        intro t ht
        simp only [Finset.mem_filter, Finset.mem_range] at ht
        have htne : t ≠ 0 := by
          rintro rfl
          rw [Nat.cast_zero, mul_zero] at ht
          rw [← hcdef] at ht
          omega
        have hceq : 1 + padicValNat p t = c := by
          rcases cftStepTrich hUunit ha0 htne hν ht.2 with ⟨hlt', hνeq⟩ | ⟨heqc, -⟩ | ⟨hgt', hνeq⟩
          · omega
          · omega
          · omega
        have hdvd : p ^ (c - 1) ∣ t :=
          (Nat.pow_dvd_iff_le_padicValNat (by omega : p ≠ 1) htne).mpr (by omega)
        exact ⟨hceq, hdvd, (Nat.mul_div_cancel' hdvd).symm⟩
      have hcount : ((Finset.range (p ^ (N - (c - 1)))).filter
          (fun s : ℕ => padicValInt p (Ê.eval (s : ℤ)) = ν - c)).card ≤ p ^ (N + 1 - ν) := by
        have hpc := pLinearCount hEcoeff2 hEcoeff1 (ν - c) (by omega) (N - (c - 1))
        rwa [show (N - (c - 1)) - (ν - c) = N + 1 - ν by omega] at hpc
      have key' : ∀ t : ℕ, t ∈ (Finset.range (p ^ N)).filter
            (fun t : ℕ => padicValInt p (G.eval ((p : ℤ) * (t : ℤ))) = ν) →
          (1 + padicValNat p t = c ∧ p ^ (c - 1) ∣ t
            ∧ t = p ^ (c - 1) * (t / p ^ (c - 1))) := key
      have hinj : Set.InjOn (fun t : ℕ => t / p ^ (c - 1))
          ↑((Finset.range (p ^ N)).filter
            (fun t : ℕ => padicValInt p (G.eval ((p : ℤ) * (t : ℤ))) = ν)) := by
        intro a1 ha1mem a2 ha2mem heq
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at ha1mem ha2mem
        obtain ⟨-, hd1, -⟩ := key a1 (by
          simp only [Finset.mem_filter, Finset.mem_range]; exact ⟨ha1mem.1, ha1mem.2⟩)
        obtain ⟨-, hd2, -⟩ := key a2 (by
          simp only [Finset.mem_filter, Finset.mem_range]; exact ⟨ha2mem.1, ha2mem.2⟩)
        have hm1 : p ^ (c - 1) * (a1 / p ^ (c - 1)) = a1 := Nat.mul_div_cancel' hd1
        have hm2 : p ^ (c - 1) * (a2 / p ^ (c - 1)) = a2 := Nat.mul_div_cancel' hd2
        calc a1 = p ^ (c - 1) * (a1 / p ^ (c - 1)) := hm1.symm
          _ = p ^ (c - 1) * (a2 / p ^ (c - 1)) := congrArg (fun z => p ^ (c - 1) * z) heq
          _ = a2 := hm2
      have hmaps : Set.MapsTo (fun t : ℕ => t / p ^ (c - 1))
          ↑((Finset.range (p ^ N)).filter
            (fun t : ℕ => padicValInt p (G.eval ((p : ℤ) * (t : ℤ))) = ν))
          ↑((Finset.range (p ^ (N - (c - 1)))).filter
            (fun s : ℕ => padicValInt p (Ê.eval (s : ℤ)) = ν - c)) := by
        intro t ht
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at ht ⊢
        obtain ⟨hceq, hdvd, -⟩ := key t (by
          simp only [Finset.mem_filter, Finset.mem_range]; exact ⟨ht.1, ht.2⟩)
        refine ⟨?_, ?_⟩
        · rcases le_or_gt (c - 1) N with hcle | hcgt
          · by_contra hcon
            have hle : p ^ (N - (c - 1)) ≤ t / p ^ (c - 1) := not_lt.mp hcon
            have hmul : p ^ (N - (c - 1)) * p ^ (c - 1) ≤ t := by
              have := Nat.mul_le_mul_right (p ^ (c - 1)) hle
              rwa [Nat.div_mul_cancel hdvd] at this
            have hpp : p ^ (N - (c - 1)) * p ^ (c - 1) = p ^ N := by
              rw [← pow_add, Nat.sub_add_cancel hcle]
            rw [hpp] at hmul
            omega
          · have htlt : t < p ^ (c - 1) := by
              have : p ^ N ≤ p ^ (c - 1) := Nat.pow_le_pow_right (by omega) (by omega)
              omega
            rw [Nat.div_eq_of_lt htlt]
            exact pow_pos (by omega) _
        · have hs : (p : ℤ) ^ (c - 1) * ((t / p ^ (c - 1) : ℕ) : ℤ) = (t : ℤ) := by
            exact_mod_cast (Nat.mul_div_cancel' hdvd)
          have hpow : (p : ℤ) * (p : ℤ) ^ (c - 1) = (p : ℤ) ^ c := by
            rw [← pow_succ']
            congr 1
            omega
          have hpt_eq : (p : ℤ) * (t : ℤ) = (p : ℤ) ^ c * ((t / p ^ (c - 1) : ℕ) : ℤ) := by
            rw [← hs, ← mul_assoc, hpow]
          have hGdecomp : G.eval ((p : ℤ) ^ c * ((t / p ^ (c - 1) : ℕ) : ℤ))
              = (p : ℤ) ^ c * Ê.eval ((t / p ^ (c - 1) : ℕ) : ℤ) := by
            rw [(cftEvalDivX G ((p : ℤ) ^ c * ((t / p ^ (c - 1) : ℕ) : ℤ))).1, hA, hEeval]
            ring
          have htval := ht.2
          rw [hpt_eq, hGdecomp] at htval
          have hEne : Ê.eval ((t / p ^ (c - 1) : ℕ) : ℤ) ≠ 0 := by
            intro h
            rw [h, mul_zero, padicValInt.zero] at htval
            omega
          rw [cftValPowMul c hEne] at htval
          omega
      exact le_trans (Finset.card_le_card_of_injOn _ hmaps hinj) hcount


/-! ## Assembly -/

/-- The `p % p ∈ R` bookkeeping: every `y` in `S` has its residue in the set of simple roots. -/
lemma cftMemR {p : ℕ} [Fact p.Prime] (Q : Polynomial ℤ)
    {ν M : ℕ} (hν : 1 ≤ ν) {S : Finset ℕ}
    (hS : ∀ y ∈ S, padicValNat p ((Polynomial.derivative Q).eval (y : ℤ)).natAbs = ν
        ∧ ¬ ((p : ℤ) ∣ (Polynomial.derivative (Polynomial.derivative Q)).eval (y : ℤ))
        ∧ y < p ^ M)
    {y : ℕ} (hy : y ∈ S) :
    y % p ∈ (Finset.range p).filter (fun r : ℕ =>
        (p : ℤ) ∣ (Polynomial.derivative Q).eval (r : ℤ)
        ∧ ¬ (p : ℤ) ∣ (Polynomial.derivative (Polynomial.derivative Q)).eval (r : ℤ)) := by
  classical
  obtain ⟨hval, h2nd, -⟩ := hS y hy
  have hval' : padicValInt p ((Polynomial.derivative Q).eval (y : ℤ)) = ν := hval
  have hne : (Polynomial.derivative Q).eval (y : ℤ) ≠ 0 := by
    intro h0
    rw [h0] at hval'
    simp [padicValInt.zero] at hval'
    omega
  have hpdiv : (p : ℤ) ∣ (Polynomial.derivative Q).eval (y : ℤ) :=
    (cftValOneLe hne).mp (hν.trans (le_of_eq hval'.symm))
  have hmod : (p : ℤ) ∣ (y : ℤ) - (((y % p : ℕ)) : ℤ) := by
    have hcast : (y : ℤ) = (p : ℤ) * (((y / p : ℕ)) : ℤ) + (((y % p : ℕ)) : ℤ) := by
      have hy' : y = p * (y / p) + y % p := (Nat.div_add_mod y p).symm
      calc (y : ℤ) = ((p * (y / p) + y % p : ℕ) : ℤ) := congrArg (fun z : ℕ => (z : ℤ)) hy'
        _ = ((p * (y / p) : ℕ) : ℤ) + (((y % p : ℕ)) : ℤ) := by rw [Nat.cast_add]
        _ = (p : ℤ) * (((y / p : ℕ)) : ℤ) + (((y % p : ℕ)) : ℤ) := by rw [Nat.cast_mul]
    refine ⟨(((y / p : ℕ)) : ℤ), ?_⟩
    rw [hcast]
    ring
  have hsub1 : (p : ℤ) ∣ (Polynomial.derivative Q).eval (y : ℤ)
      - (Polynomial.derivative Q).eval (((y % p : ℕ)) : ℤ) :=
    dvd_trans hmod (Polynomial.sub_dvd_eval_sub (y : ℤ) (((y % p : ℕ)) : ℤ) (Polynomial.derivative Q))
  have hsub2 : (p : ℤ) ∣ (Polynomial.derivative (Polynomial.derivative Q)).eval (y : ℤ)
      - (Polynomial.derivative (Polynomial.derivative Q)).eval (((y % p : ℕ)) : ℤ) :=
    dvd_trans hmod (Polynomial.sub_dvd_eval_sub (y : ℤ) (((y % p : ℕ)) : ℤ)
      (Polynomial.derivative (Polynomial.derivative Q)))
  refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt _ (Fact.out : p.Prime).pos), ?_, ?_⟩
  · have h3 := dvd_sub hpdiv hsub1
    have he : (Polynomial.derivative Q).eval (y : ℤ)
        - ((Polynomial.derivative Q).eval (y : ℤ)
          - (Polynomial.derivative Q).eval (((y % p : ℕ)) : ℤ))
        = (Polynomial.derivative Q).eval (((y % p : ℕ)) : ℤ) := by ring
    rwa [he] at h3
  · intro hbad
    exact h2nd (by
      have h3 := dvd_add hbad hsub2
      have he : (Polynomial.derivative (Polynomial.derivative Q)).eval (((y % p : ℕ)) : ℤ)
          + ((Polynomial.derivative (Polynomial.derivative Q)).eval (y : ℤ)
            - (Polynomial.derivative (Polynomial.derivative Q)).eval (((y % p : ℕ)) : ℤ))
          = (Polynomial.derivative (Polynomial.derivative Q)).eval (y : ℤ) := by ring
      rwa [he] at h3)

/-- One residue class contributes at most `p ^ (M - ν)`. -/
lemma cftFiberBound {p : ℕ} [Fact p.Prime] (Q : Polynomial ℤ) {ν M : ℕ} (hν : 1 ≤ ν)
    {S : Finset ℕ}
    (hS : ∀ y ∈ S, padicValNat p ((Polynomial.derivative Q).eval (y : ℤ)).natAbs = ν
        ∧ ¬ ((p : ℤ) ∣ (Polynomial.derivative (Polynomial.derivative Q)).eval (y : ℤ))
        ∧ y < p ^ M)
    {r : ℕ} (hr : r ∈ (Finset.range p).filter (fun r : ℕ =>
        (p : ℤ) ∣ (Polynomial.derivative Q).eval (r : ℤ)
        ∧ ¬ (p : ℤ) ∣ (Polynomial.derivative (Polynomial.derivative Q)).eval (r : ℤ))) :
    (S.filter (fun y : ℕ => y % p = r)).card ≤ p ^ (M - ν) := by
  classical
  obtain ⟨hrlt, hrdiv, hrnd⟩ := Finset.mem_filter.mp hr
  set Gr : Polynomial ℤ := (Polynomial.derivative Q).comp (Polynomial.X + Polynomial.C (r : ℤ))
    with hGrdef
  have hGr0 : Gr.eval 0 = (Polynomial.derivative Q).eval (r : ℤ) := by
    rw [hGrdef]
    simp only [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C,
      zero_add]
  have hGr1 : Gr.derivative.eval 0 = (Polynomial.derivative (Polynomial.derivative Q)).eval (r : ℤ) := by
    rw [hGrdef]
    simp only [Polynomial.derivative_comp, Polynomial.derivative_add, Polynomial.derivative_X,
      Polynomial.derivative_C, add_zero, Polynomial.eval_mul, Polynomial.eval_one,
      Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C,
      zero_add, one_mul]
  have hinj : Set.InjOn (fun y : ℕ => y / p) ↑(S.filter (fun y : ℕ => y % p = r)) := by
    intro a1 ha1 a2 ha2 heq
    simp only [Finset.mem_coe, Finset.mem_filter] at ha1 ha2
    have h1 : a1 = p * (a1 / p) + a1 % p := (Nat.div_add_mod a1 p).symm
    have h2 : a2 = p * (a2 / p) + a2 % p := (Nat.div_add_mod a2 p).symm
    rw [h1, h2, ha1.2, ha2.2]
    exact congrArg (fun z => p * z + r) heq
  have hmaps : Set.MapsTo (fun y : ℕ => y / p) ↑(S.filter (fun y : ℕ => y % p = r))
      ↑((Finset.range (p ^ (M - 1))).filter
        (fun t : ℕ => padicValInt p (Gr.eval ((p : ℤ) * (t : ℤ))) = ν)) := by
    intro y hy
    simp only [Finset.mem_coe, Finset.mem_filter] at hy ⊢
    obtain ⟨hyS, hymod⟩ := hy
    obtain ⟨hval, -, hyM⟩ := hS y hyS
    have hval' : padicValInt p ((Polynomial.derivative Q).eval (y : ℤ)) = ν := hval
    refine ⟨?_, ?_⟩
    · rw [Finset.mem_range]
      rcases Nat.eq_zero_or_pos M with hM0 | hMpos
      · subst hM0
        have hy0 : y = 0 := by
          have : y < 1 := hyM
          omega
        rw [hy0, Nat.zero_div]
        exact pow_pos (Nat.Prime.pos Fact.out) _
      · have hM1 : M - 1 + 1 = M := Nat.sub_add_cancel hMpos
        have hlt : y < p ^ (M - 1) * p := by
          rw [← pow_succ, hM1]
          exact hyM
        exact (Nat.div_lt_iff_lt_mul (Nat.Prime.pos Fact.out)).mpr hlt
    · have hev : Gr.eval ((p : ℤ) * (((y / p : ℕ)) : ℤ)) = (Polynomial.derivative Q).eval (y : ℤ) := by
        rw [hGrdef]
        simp only [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C,
          Polynomial.eval_mul]
        congr 1
        have hcast : (y : ℤ) = (p : ℤ) * (((y / p : ℕ)) : ℤ) + (((y % p : ℕ)) : ℤ) := by
          have hy' : y = p * (y / p) + y % p := (Nat.div_add_mod y p).symm
          calc (y : ℤ) = ((p * (y / p) + y % p : ℕ) : ℤ) := congrArg (fun z : ℕ => (z : ℤ)) hy'
            _ = ((p * (y / p) : ℕ) : ℤ) + (((y % p : ℕ)) : ℤ) := by rw [Nat.cast_add]
            _ = (p : ℤ) * (((y / p : ℕ)) : ℤ) + (((y % p : ℕ)) : ℤ) := by rw [Nat.cast_mul]
        rw [hcast, hymod]
      rw [hev]
      exact hval'
  have hcount := pMultipleCount (p := p) (G := Gr) (by rw [hGr0]; exact hrdiv)
    (by rw [hGr1]; exact hrnd) ν hν (M - 1)
  refine le_trans (Finset.card_le_card_of_injOn (fun y : ℕ => y / p) hmaps hinj) ?_
  rwa [show (M - 1) + 1 - ν = M - ν by omega] at hcount

/-- **Target lemma, auxiliary form** (with the divisibility hypothesis dropped, since it is not
needed). -/
theorem cftMainAux {p : ℕ} [Fact p.Prime] (Q : Polynomial ℤ) (hdeg : Q.natDegree ≤ 4)
    {ν M : ℕ} (hν : 1 ≤ ν) (S : Finset ℕ)
    (hS : ∀ y ∈ S, padicValNat p ((Polynomial.derivative Q).eval (y : ℤ)).natAbs = ν
        ∧ ¬ ((p : ℤ) ∣ (Polynomial.derivative (Polynomial.derivative Q)).eval (y : ℤ))
        ∧ y < p ^ M) :
    S.card ≤ 3 * p ^ (M - min ν M) := by
  classical
  have hMeq : M - min ν M = M - ν := by
    rcases le_total ν M with h | h
    · rw [min_eq_left h]
    · rw [min_eq_right h]
      omega
  rw [hMeq]
  set R : Finset ℕ := (Finset.range p).filter (fun r : ℕ =>
      (p : ℤ) ∣ (Polynomial.derivative Q).eval (r : ℤ)
      ∧ ¬ (p : ℤ) ∣ (Polynomial.derivative (Polynomial.derivative Q)).eval (r : ℤ)) with hRdef
  have hRcard : R.card ≤ 3 := by
    rw [hRdef]
    exact cftSimpleRoots Q hdeg
  have hmemR : ∀ y ∈ S, y % p ∈ R := fun y hy => by
    rw [hRdef]
    exact cftMemR Q hν (fun z hz => (hS z hz)) hy
  have hfiber : S.card ≤ ∑ r ∈ R, (S.filter (fun y : ℕ => y % p = r)).card :=
    le_of_eq (Finset.card_eq_sum_card_fiberwise (f := fun y : ℕ => y % p) hmemR)
  have hbnd : ∀ r ∈ R, (S.filter (fun y : ℕ => y % p = r)).card ≤ p ^ (M - ν) := by
    intro r hr
    rw [hRdef] at hr
    exact cftFiberBound Q hν (fun z hz => (hS z hz)) hr
  calc S.card ≤ ∑ r ∈ R, (S.filter (fun y : ℕ => y % p = r)).card := hfiber
    _ ≤ ∑ _r ∈ R, p ^ (M - ν) := Finset.sum_le_sum hbnd
    _ = R.card * p ^ (M - ν) := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ 3 * p ^ (M - ν) := Nat.mul_le_mul_right _ hRcard

/-- **The fiber bound.**  For a prime `p ≥ 5`, a polynomial `Q` of degree at most `4` and `ν ≥ 1`,
the number of `y < p ^ M` with `p ^ A ∣ Q(y)`, `v_p (Q'(y)) = ν` and `p ∤ Q''(y)` is at most
`3 * p ^ (M - min ν M)`. -/
theorem capContent_fiber_three {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p) (Q : Polynomial ℤ)
    (hdeg : Q.natDegree ≤ 4) (hQ : Q.map (Int.castRingHom (ZMod p)) ≠ 0)
    {A ν M : ℕ} (hν : 1 ≤ ν) (S : Finset ℕ)
    (hS : ∀ y ∈ S, ((p ^ A : ℕ) : ℤ) ∣ Q.eval (y : ℤ)
        ∧ padicValNat p ((Polynomial.derivative Q).eval (y : ℤ)).natAbs = ν
        ∧ ¬ ((p : ℤ) ∣ (Polynomial.derivative (Polynomial.derivative Q)).eval (y : ℤ))
        ∧ y < p ^ M) :
    S.card ≤ 3 * p ^ (M - min ν M) :=
  cftMainAux Q hdeg hν S (fun y hy => by
    obtain ⟨-, h1, h2, h3⟩ := hS y hy
    exact ⟨h1, h2, h3⟩)

end Work.LinnikBurgess
