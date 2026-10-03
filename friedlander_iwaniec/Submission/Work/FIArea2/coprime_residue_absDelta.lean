import Mathlib
import Submission.Work.FIPlan.Interface

namespace Work.FIArea2

/-- **The side condition `(a,q) = 1` of Corollary 8.3 is automatic**: if `a` is a residue of `z₂/z₁` modulo `|Δ|` (i.e. `a·|z₁|² ≡ Re(z̄₁z₂) (mod |Δ|)`) and `(Re(z̄₁z₂), |Δ|) = 1`, then `(a,|Δ|) = 1`.  Together with `coprime_re_absDelta` this supplies the hypothesis `(a,|Δ|) = 1` of `Nsol_eq_two_sum_jacobi` (the corrected (8.16)).

Sketch: `d = (a,|Δ|)` divides `a` and `|Δ|`; `d | a` gives `d | a|z₁|²`, and the congruence gives `|Δ| | a|z₁|² − Re(z̄₁z₂)`, so `d | Re(z̄₁z₂)`; hence `d | (Re(z̄₁z₂),|Δ|) = 1`.  (No coprimality of `|z₁|²` with `|Δ|` is needed.) -/
theorem coprime_residue_absDelta {z1 z2 : GaussianInt} {a : ℕ}
    (ha : (a : ℤ) * (Work.FIPlan.gnorm z1 : ℤ)
        ≡ (star z1 * z2).re [ZMOD (Work.FIPlan.absDelta z1 z2 : ℤ)])
    (h0 : Nat.Coprime ((star z1 * z2).re).natAbs (Work.FIPlan.absDelta z1 z2)) :
    Nat.Coprime a (Work.FIPlan.absDelta z1 z2) := by
  rw [Nat.coprime_iff_gcd_eq_one] at h0 ⊢
  have hda : Nat.gcd a (Work.FIPlan.absDelta z1 z2) ∣ a := Nat.gcd_dvd_left a _
  have hdD : Nat.gcd a (Work.FIPlan.absDelta z1 z2) ∣ Work.FIPlan.absDelta z1 z2 :=
    Nat.gcd_dvd_right a _
  -- integral divisibilities
  have hdZ : ((Nat.gcd a (Work.FIPlan.absDelta z1 z2) : ℕ) : ℤ) ∣ (a : ℤ) := by
    exact_mod_cast hda
  have hDZ : ((Nat.gcd a (Work.FIPlan.absDelta z1 z2) : ℕ) : ℤ) ∣
      (Work.FIPlan.absDelta z1 z2 : ℤ) := by
    exact_mod_cast hdD
  have hmod : (Work.FIPlan.absDelta z1 z2 : ℤ) ∣
      (star z1 * z2).re - (a : ℤ) * (Work.FIPlan.gnorm z1 : ℤ) :=
    Int.ModEq.dvd ha
  have hdsub : ((Nat.gcd a (Work.FIPlan.absDelta z1 z2) : ℕ) : ℤ) ∣
      (star z1 * z2).re - (a : ℤ) * (Work.FIPlan.gnorm z1 : ℤ) := hDZ.trans hmod
  have hdmul : ((Nat.gcd a (Work.FIPlan.absDelta z1 z2) : ℕ) : ℤ) ∣
      (a : ℤ) * (Work.FIPlan.gnorm z1 : ℤ) := dvd_mul_of_dvd_left hdZ _
  have hdRe : ((Nat.gcd a (Work.FIPlan.absDelta z1 z2) : ℕ) : ℤ) ∣ (star z1 * z2).re := by
    have h := dvd_add hdsub hdmul
    simpa using h
  -- back to `ℕ`
  have hdReNat : Nat.gcd a (Work.FIPlan.absDelta z1 z2) ∣ ((star z1 * z2).re).natAbs := by
    rw [← Int.natAbs_natCast (Nat.gcd a (Work.FIPlan.absDelta z1 z2))]
    exact Int.natAbs_dvd_natAbs.mpr hdRe
  have hdiv : Nat.gcd a (Work.FIPlan.absDelta z1 z2) ∣
      ((star z1 * z2).re).natAbs.gcd (Work.FIPlan.absDelta z1 z2) :=
    Nat.dvd_gcd hdReNat hdD
  have hone : Nat.gcd a (Work.FIPlan.absDelta z1 z2) ∣ 1 := by
    rwa [h0] at hdiv
  exact Nat.dvd_one.mp hone

end Work.FIArea2
