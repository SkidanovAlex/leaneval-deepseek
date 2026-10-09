/-
# A relation between the Legendre symbols of the two terms of a partition of unity

If `a + b = 1` in `ℚ` and `v_p(a) = v_p(b) < 0`, then `(a/p)(b/p) = (-1/p)`, where `(·/p)` is
the Legendre symbol of the `p`-adic unit part.  This is the local input behind the fact that the
Hilbert symbol `(a,b)_p` is trivial when `a + b = 1`.
-/
import Mathlib
import Submission.Work.HilbertSymbol.Basic
import Submission.Work.HilbertSymbol.SmallLemmas
import Submission.Work.HilbertSymbol.legendreOf_intUnit
import Submission.Work.HilbertSymbol.intUnit_num_den_mul_sq
import Submission.Work.HilbertSymbol.padicVal_eq_zero_iff
import Submission.Work.HilbertSymbol.hilbertSymbolOdd_primeUnit_self
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

namespace Work.HilbertSymbol

/-! ## `legendreOf` as a multiplicative character -/

/-- `legendreOf p` as a monoid homomorphism `ℚˣ →* ℤˣ`. -/
private def legendreOfHom (p : ℕ) [Fact p.Prime] : ℚˣ →* ℤˣ where
  toFun := legendreOf p
  map_one' := legendreOf_one p
  map_mul' := legendreOf_mul p

private theorem legendreOf_zpow (p : ℕ) [Fact p.Prime] (a : ℚˣ) (k : ℤ) :
    legendreOf p (a ^ k) = legendreOf p a ^ k :=
  (legendreOfHom p).map_zpow a k

private theorem intUnitOf_mul_self (n : ℤ) : intUnitOf n * intUnitOf n = 1 := by
  rcases eq_or_ne n (-1) with h | h
  · rw [intUnitOf_eq_neg_one_iff.mpr h]
    ext
    simp
  · rw [intUnitOf_eq_one_iff.mpr h]
    simp

private theorem legendreOf_sq (p : ℕ) [Fact p.Prime] (a : ℚˣ) : legendreOf p (a ^ 2) = 1 := by
  have h : legendreOf p a * legendreOf p a = 1 := by
    unfold legendreOf legendreUnit quadCharUnit
    exact intUnitOf_mul_self _
  rw [sq, legendreOf_mul, h]

private theorem legendreOf_primeUnit_zpow (p : ℕ) [Fact p.Prime] (k : ℤ) :
    legendreOf p ((primeUnit p) ^ k) = 1 := by
  rw [legendreOf_zpow, legendreOf_primeUnit, one_zpow]

private theorem legendreOf_mul_primeUnit_zpow (p : ℕ) [Fact p.Prime] (a : ℚˣ) (k : ℤ) :
    legendreOf p (a * (primeUnit p) ^ k) = legendreOf p a := by
  rw [legendreOf_mul, legendreOf_primeUnit_zpow, mul_one]

/-! ## `legendreOf` of a rational number of `p`-adic valuation `0` -/

private theorem not_dvd_num_mul_den {p : ℕ} [Fact p.Prime] {c : ℚˣ}
    (hc : padicVal p c = 0) : ¬ (p : ℤ) ∣ (c : ℚ).num * ((c : ℚ).den : ℤ) := by
  obtain ⟨hn, hd⟩ := (padicVal_eq_zero_iff c).mp hc
  intro h
  rcases (Prime.dvd_mul (Nat.prime_iff_prime_int.mp (Fact.out : p.Prime))).mp h with h' | h'
  · exact hn h'
  · exact hd (by exact_mod_cast h')

/-- For a rational number `c` with `v_p(c) = 0`, the Legendre symbol of its `p`-adic unit part is
the Legendre symbol of the product of its numerator and denominator. -/
private theorem legendreOf_eq_intUnitOf_legendreSym_num_mul_den {p : ℕ} [Fact p.Prime] {c : ℚˣ}
    (hc : padicVal p c = 0) :
    legendreOf p c = intUnitOf (legendreSym p ((c : ℚ).num * ((c : ℚ).den : ℤ))) := by
  have hm : (c : ℚ).num ≠ 0 := Rat.num_ne_zero.mpr c.ne_zero
  have hq : (c : ℚ).den ≠ 0 := Rat.den_nz _
  have hmul : (c : ℚ).num * ((c : ℚ).den : ℤ) ≠ 0 :=
    mul_ne_zero hm (by exact_mod_cast hq)
  have key := congrArg (legendreOf p) (intUnit_num_den_mul_sq c)
  rw [legendreOf_mul, legendreOf_sq, mul_one] at key
  rw [key, legendreOf_intUnit hmul (not_dvd_num_mul_den hc)]

private theorem legendreOf_neg_one_eq_intUnitOf_legendreSym_neg_one (p : ℕ) [Fact p.Prime] :
    legendreOf p (-1) = intUnitOf (legendreSym p (-1)) := by
  have h := legendreOf_eq_intUnitOf_legendreSym_num_mul_den (p := p) (c := -1)
    (by rw [padicVal_neg, padicVal_one])
  simpa using h

/-! ## Two Legendre symbols of integers summing to `0` modulo `p` -/

private theorem legendreSym_mul_eq_neg_one_of_dvd_add {p : ℕ} [Fact p.Prime] {x y : ℤ}
    (hy : ¬ (p : ℤ) ∣ y) (h : (p : ℤ) ∣ x + y) :
    legendreSym p x * legendreSym p y = legendreSym p (-1) := by
  have hy0 : (y : ZMod p) ≠ 0 := by rwa [ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hxy : (x : ZMod p) = -(y : ZMod p) := by
    have h0 : ((x + y : ℤ) : ZMod p) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact h
    push_cast at h0
    exact eq_neg_of_add_eq_zero_left h0
  have hx' : (x : ZMod p) = (((-1 : ℤ)) : ZMod p) * (y : ZMod p) := by
    rw [hxy]
    push_cast
    ring
  have key : legendreSym p x = legendreSym p (-1) * legendreSym p y := by
    calc legendreSym p x = quadraticChar (ZMod p) (x : ZMod p) := rfl
      _ = quadraticChar (ZMod p) ((((-1 : ℤ)) : ZMod p) * (y : ZMod p)) := by rw [hx']
      _ = quadraticChar (ZMod p) (((-1 : ℤ)) : ZMod p) * quadraticChar (ZMod p) (y : ZMod p) :=
            map_mul _ _ _
      _ = legendreSym p (-1) * legendreSym p y := rfl
  have hy2 : legendreSym p y * legendreSym p y = 1 := by
    rw [← legendreSym.mul p y y, ← sq]
    exact legendreSym.sq_one' p hy0
  rw [key, mul_assoc, hy2, mul_one]

/-! ## Divisibility of the cross-multiplied numerator -/

private theorem dvd_num_den_add_of_pos {p : ℕ} [Fact p.Prime] {c d : ℚˣ}
    (h : 0 < padicValRat p ((c : ℚ) + (d : ℚ))) :
    (p : ℤ) ∣ (c : ℚ).num * ((d : ℚ).den : ℤ) + (d : ℚ).num * ((c : ℚ).den : ℤ) := by
  set s : ℚ := (c : ℚ) + (d : ℚ) with hs
  set nc : ℤ := (c : ℚ).num with hnc
  set qc : ℤ := ((c : ℚ).den : ℤ) with hqc
  set nd : ℤ := (d : ℚ).num with hnd
  set qd : ℤ := ((d : ℚ).den : ℤ) with hqd
  set S : ℤ := nc * qd + nd * qc with hS
  have hs0 : s ≠ 0 := by
    intro h0
    rw [h0, padicValRat.zero] at h
    exact lt_irrefl 0 h
  have hqc0 : (qc : ℚ) ≠ 0 := by
    rw [hqc]
    exact_mod_cast Rat.den_nz (c : ℚ)
  have hqd0 : (qd : ℚ) ≠ 0 := by
    rw [hqd]
    exact_mod_cast Rat.den_nz (d : ℚ)
  have hSval : ((S : ℤ) : ℚ) = s * (qc : ℚ) * (qd : ℚ) := by
    have h1 : (c : ℚ) = (nc : ℚ) / (qc : ℚ) := by
      rw [hnc, hqc]
      exact (Rat.num_div_den (c : ℚ)).symm
    have h2 : (d : ℚ) = (nd : ℚ) / (qd : ℚ) := by
      rw [hnd, hqd]
      exact (Rat.num_div_den (d : ℚ)).symm
    rw [hS, hs]
    push_cast
    rw [h1, h2]
    field_simp
  have hval : (0 : ℤ) < padicValRat p ((S : ℤ) : ℚ) := by
    rw [hSval, padicValRat.mul (mul_ne_zero hs0 hqc0) hqd0, padicValRat.mul hs0 hqc0]
    have h1 : (0 : ℤ) ≤ padicValRat p ((qc : ℤ) : ℚ) := by
      rw [hqc]
      simp
    have h2 : (0 : ℤ) ≤ padicValRat p ((qd : ℤ) : ℚ) := by
      rw [hqd]
      simp
    linarith
  rw [padicValRat.of_int] at hval
  by_contra hndvd
  have h0 : padicValInt p S = 0 := padicValInt.eq_zero_of_not_dvd hndvd
  rw [h0] at hval
  norm_num at hval

/-! ## The core computation -/

private theorem legendreOf_mul_eq_neg_one_of_padicVal_eq_zero {p : ℕ} [Fact p.Prime] {c d : ℚˣ}
    (hc : padicVal p c = 0) (hd : padicVal p d = 0)
    (hsum : 0 < padicValRat p ((c : ℚ) + (d : ℚ))) :
    legendreOf p c * legendreOf p d = legendreOf p (-1) := by
  have hdiv := dvd_num_den_add_of_pos (p := p) hsum
  have hnc : ¬ (p : ℤ) ∣ (c : ℚ).num := ((padicVal_eq_zero_iff c).mp hc).1
  have hnd : ¬ (p : ℤ) ∣ (d : ℚ).num := ((padicVal_eq_zero_iff d).mp hd).1
  have hqc : ¬ p ∣ (c : ℚ).den := ((padicVal_eq_zero_iff c).mp hc).2
  have hqd : ¬ p ∣ (d : ℚ).den := ((padicVal_eq_zero_iff d).mp hd).2
  have hpq : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp (Fact.out : p.Prime)
  have hcc : ¬ (p : ℤ) ∣ (c : ℚ).num * ((c : ℚ).den : ℤ) := fun h => by
    rcases (Prime.dvd_mul hpq).mp h with h | h
    · exact hnc h
    · exact hqc (by exact_mod_cast h)
  have hdd : ¬ (p : ℤ) ∣ (d : ℚ).num * ((d : ℚ).den : ℤ) := fun h => by
    rcases (Prime.dvd_mul hpq).mp h with h | h
    · exact hnd h
    · exact hqd (by exact_mod_cast h)
  have hncd : ¬ (p : ℤ) ∣ (c : ℚ).num * ((d : ℚ).den : ℤ) := fun h => by
    rcases (Prime.dvd_mul hpq).mp h with h | h
    · exact hnc h
    · exact hqd (by exact_mod_cast h)
  have hndc : ¬ (p : ℤ) ∣ (d : ℚ).num * ((c : ℚ).den : ℤ) := fun h => by
    rcases (Prime.dvd_mul hpq).mp h with h | h
    · exact hnd h
    · exact hqc (by exact_mod_cast h)
  have key := legendreSym_mul_eq_neg_one_of_dvd_add (p := p)
    (x := (c : ℚ).num * ((d : ℚ).den : ℤ)) (y := (d : ℚ).num * ((c : ℚ).den : ℤ)) hndc hdiv
  rw [legendreOf_eq_intUnitOf_legendreSym_num_mul_den hc,
    legendreOf_eq_intUnitOf_legendreSym_num_mul_den hd,
    legendreOf_neg_one_eq_intUnitOf_legendreSym_neg_one p]
  rw [← intUnitOf_mul (legendreSym_eq_one_or_neg_one' hcc)
    (legendreSym_eq_one_or_neg_one' hdd)]
  congr 1
  rw [← legendreSym.mul p ((c : ℚ).num * ((c : ℚ).den : ℤ))
    ((d : ℚ).num * ((d : ℚ).den : ℤ))]
  rw [show (c : ℚ).num * ((c : ℚ).den : ℤ) * ((d : ℚ).num * ((d : ℚ).den : ℤ))
      = (c : ℚ).num * ((d : ℚ).den : ℤ) * ((d : ℚ).num * ((c : ℚ).den : ℤ)) from by ring]
  rw [legendreSym.mul p ((c : ℚ).num * ((d : ℚ).den : ℤ))
    ((d : ℚ).num * ((c : ℚ).den : ℤ))]
  exact key

/-! ## The main statement -/

theorem legendreOf_mul_eq_legendreOf_neg_one_of_add_eq_one {p : ℕ} [Fact p.Prime] {a b : ℚˣ}
    (h : (a : ℚ) + (b : ℚ) = 1) (hab : padicVal p a = padicVal p b) (hlt : padicVal p a < 0) :
    legendreOf p a * legendreOf p b = legendreOf p (-1) := by
  set k : ℤ := -padicVal p a with hk
  have hkpos : 0 < k := by omega
  have hck : padicVal p (a * (primeUnit p) ^ k) = 0 := by
    rw [padicVal_mul p a ((primeUnit p) ^ k), padicVal_zpow p (primeUnit p) k,
      padicVal_primeUnit, mul_one]
    omega
  have hdk : padicVal p (b * (primeUnit p) ^ k) = 0 := by
    rw [padicVal_mul p b ((primeUnit p) ^ k), padicVal_zpow p (primeUnit p) k,
      padicVal_primeUnit, mul_one]
    omega
  have hsum : 0 < padicValRat p (((a * (primeUnit p) ^ k : ℚˣ) : ℚ)
      + ((b * (primeUnit p) ^ k : ℚˣ) : ℚ)) := by
    have hcd : (((a * (primeUnit p) ^ k : ℚˣ) : ℚ) + ((b * (primeUnit p) ^ k : ℚˣ) : ℚ))
        = (p : ℚ) ^ k := by
      simp only [Units.val_mul, Units.val_zpow_eq_zpow_val, primeUnit_coe]
      rw [← add_mul, h, one_mul]
    rw [hcd, padicValRat.zpow, padicValRat.self (Fact.out : p.Prime).one_lt, mul_one]
    exact hkpos
  rw [← legendreOf_mul_primeUnit_zpow p a k, ← legendreOf_mul_primeUnit_zpow p b k]
  exact legendreOf_mul_eq_neg_one_of_padicVal_eq_zero hck hdk hsum

end Work.HilbertSymbol
