import Mathlib
import Submission.Work.FIArea2.G8Defs
import Submission.Work.FIArea2.TsumDefs

namespace Work.FIArea2

/-! ## Auxiliary facts about the Gaussian gcd `(Λ,Δ)` of (9.5)

Throughout, `ℤ[i] = GaussianInt = Zsqrtd (-1)` and `gnorm z = |z|²` is the (rational) norm of the
Gaussian integer `z` (so `(gnorm z : ℤ[i]) = z * star z`).  The main ingredient is the cancellation
of a factor whose norm is coprime to the modulus, which turns the congruence
`z₂ ≡ a z₁ (mod |Δ|)` into a congruence of the components, and then transports the divisibility
lattice `{d : d ∣ |Δ|}` to the rational gcd `(|Δ|, h₁² - a h₂²)`. -/

/-- `z̄z = |z|²` as an identity in `ℤ[i]`. -/
lemma gcdDelta_aux_star_mul_self (z : GaussianInt) :
    star z * z = ((Work.FIPlan.gnorm z : ℤ) : GaussianInt) := by
  rw [mul_comm, Work.FIPlan.gnorm, GaussianInt.abs_natCast_norm, ← Zsqrtd.norm_eq_mul_conj]

/-- `|z̄|² = |z|²`. -/
lemma gcdDelta_aux_gnorm_star (z : GaussianInt) :
    Work.FIPlan.gnorm (star z) = Work.FIPlan.gnorm z := by
  simp [Work.FIPlan.gnorm, Zsqrtd.norm_conj]

/-- **Cancellation modulo `d` in `ℤ[i]`.**  If `(gnorm z, d) = 1` and `d ∣ z X` in `ℤ[i]`, then
`d ∣ X`.  Indeed `z̄z = |z|²` is invertible modulo `d` by Bézout, so `z̄` is too. -/
lemma gcdDelta_aux_cancel {d : ℕ} {z X : GaussianInt}
    (hcop : Nat.Coprime (Work.FIPlan.gnorm z) d) (h : (d : GaussianInt) ∣ z * X) :
    (d : GaussianInt) ∣ X := by
  have hcop' : IsCoprime (d : GaussianInt) z := by
    have hbez : (1 : ℤ) = (Work.FIPlan.gnorm z : ℤ) * (Nat.gcdA (Work.FIPlan.gnorm z) d)
        + (d : ℤ) * (Nat.gcdB (Work.FIPlan.gnorm z) d) := by
      simpa [hcop.gcd_eq_one] using Nat.gcd_eq_gcd_ab (Work.FIPlan.gnorm z) d
    refine ⟨((Nat.gcdB (Work.FIPlan.gnorm z) d : ℤ) : GaussianInt),
      ((Nat.gcdA (Work.FIPlan.gnorm z) d : ℤ) : GaussianInt) * star z, ?_⟩
    have h2 : ((1 : ℤ) : GaussianInt) = ((Work.FIPlan.gnorm z : ℤ) : GaussianInt)
        * ((Nat.gcdA (Work.FIPlan.gnorm z) d : ℤ) : GaussianInt)
        + ((d : ℤ) : GaussianInt) * ((Nat.gcdB (Work.FIPlan.gnorm z) d : ℤ) : GaussianInt) := by
      exact_mod_cast hbez
    change ((Nat.gcdB (Work.FIPlan.gnorm z) d : ℤ) : GaussianInt) * ((d : ℤ) : GaussianInt)
        + ((Nat.gcdA (Work.FIPlan.gnorm z) d : ℤ) : GaussianInt) * star z * z
        = ((1 : ℤ) : GaussianInt)
    rw [h2, ← gcdDelta_aux_star_mul_self z]
    ring
  exact hcop'.dvd_of_dvd_mul_left h

/-- `z̄₁(z₂ - a z₁) = z̄₁z₂ - a|z₁|²` in `ℤ[i]`. -/
lemma gcdDelta_aux_z2_sub (z1 z2 : GaussianInt) (a : ℤ) :
    star z1 * (z2 - (a : GaussianInt) * z1)
      = star z1 * z2 - ((a * (Work.FIPlan.gnorm z1 : ℤ) : ℤ) : GaussianInt) := by
  calc star z1 * (z2 - (a : GaussianInt) * z1)
      = star z1 * z2 - (a : GaussianInt) * (star z1 * z1) := by rw [mul_sub, mul_left_comm]
    _ = star z1 * z2 - ((a * (Work.FIPlan.gnorm z1 : ℤ) : ℤ) : GaussianInt) := by
          rw [gcdDelta_aux_star_mul_self z1]; push_cast; rfl

/-- **The congruence `z₂ ≡ a z₁ (mod |Δ|)` in `ℤ[i]`.**  If `a` is the residue of `z₂/z₁` modulo
`|Δ|` (i.e. `a|z₁|² ≡ Re(z̄₁z₂) (mod |Δ|)`) and `(|z₁|², |Δ|) = 1`, then `|Δ| ∣ z₂ - a z₁`. -/
lemma gcdDelta_aux_dvd_z2_sub_a_z1 (z1 z2 : GaussianInt) (a : ℤ)
    (hni : Nat.Coprime (Work.FIPlan.gnorm z1) (Work.FIPlan.absDelta z1 z2))
    (ha : (a : ℤ) * (Work.FIPlan.gnorm z1 : ℤ)
        ≡ (star z1 * z2).re [ZMOD (Work.FIPlan.absDelta z1 z2 : ℤ)]) :
    ((Work.FIPlan.absDelta z1 z2 : ℕ) : GaussianInt) ∣ (z2 - (a : GaussianInt) * z1) := by
  have hkey : ((Work.FIPlan.absDelta z1 z2 : ℕ) : GaussianInt)
      ∣ star z1 * (z2 - (a : GaussianInt) * z1) := by
    change ((Work.FIPlan.absDelta z1 z2 : ℤ) : GaussianInt)
      ∣ star z1 * (z2 - (a : GaussianInt) * z1)
    rw [Zsqrtd.intCast_dvd]
    constructor
    · rw [gcdDelta_aux_z2_sub, Zsqrtd.re_sub, Zsqrtd.re_intCast]
      exact Int.ModEq.dvd ha
    · rw [gcdDelta_aux_z2_sub, Zsqrtd.im_sub, Zsqrtd.im_intCast, sub_zero]
      simp [Work.FIPlan.absDelta, Work.FIPlan.Delta]
  exact gcdDelta_aux_cancel (by rwa [gcdDelta_aux_gnorm_star]) hkey

/-- **The divisor-lattice step.**  If `(gnorm z, n) = 1` and `n ∣ X` in `ℤ[i]`, then for
`Y = z m - t X ≡ z m (mod n)` the largest divisor of `n` dividing both components of `Y` is
`(n, |m|)`.  Multiplicities of primes not dividing `n` are irrelevant, and a divisor `d ∣ n` is
absorbed by the unit `z` of `ℤ[i]/d`. -/
lemma gcdDelta_aux_gcd (z X : GaussianInt) (m t : ℤ) (n : ℕ)
    (hcop : Nat.Coprime (Work.FIPlan.gnorm z) n) (hX : (n : GaussianInt) ∣ X) :
    Nat.gcd (Nat.gcd ((z * (m : GaussianInt) - (t : GaussianInt) * X).re.natAbs)
      ((z * (m : GaussianInt) - (t : GaussianInt) * X).im.natAbs)) n
      = Nat.gcd n m.natAbs := by
  set Y := z * (m : GaussianInt) - (t : GaussianInt) * X with hYdef
  have hYX : Y + (t : GaussianInt) * X = z * (m : GaussianInt) := by rw [hYdef]; ring
  apply Nat.dvd_antisymm
  · -- the left hand side divides `(n, |m|)`
    set d := Nat.gcd (Nat.gcd Y.re.natAbs Y.im.natAbs) n with hddef
    have hdn : d ∣ n := by rw [hddef]; exact Nat.gcd_dvd_right _ _
    have hdg : d ∣ Nat.gcd Y.re.natAbs Y.im.natAbs := by
      rw [hddef]; exact Nat.gcd_dvd_left _ _
    have hdre : (d : ℤ) ∣ Y.re := Int.natCast_dvd.mpr (hdg.trans (Nat.gcd_dvd_left _ _))
    have hdim : (d : ℤ) ∣ Y.im := Int.natCast_dvd.mpr (hdg.trans (Nat.gcd_dvd_right _ _))
    have hdY : (d : GaussianInt) ∣ Y := by
      change ((d : ℤ) : GaussianInt) ∣ Y
      rw [Zsqrtd.intCast_dvd]; exact ⟨hdre, hdim⟩
    have hdnG : (d : GaussianInt) ∣ (n : GaussianInt) := by
      have h : (d : ℤ) ∣ (n : ℤ) := by exact_mod_cast hdn
      simpa using (Zsqrtd.intCast_dvd_intCast (d : ℤ) (n : ℤ)).mpr h
    have hdX : (d : GaussianInt) ∣ X := hdnG.trans hX
    have hzm : (d : GaussianInt) ∣ z * (m : GaussianInt) := by
      rw [← hYX]; exact dvd_add hdY (dvd_mul_of_dvd_right hdX _)
    have hcopd : Nat.Coprime (Work.FIPlan.gnorm z) d := hcop.coprime_dvd_right hdn
    have hdmG : (d : GaussianInt) ∣ (m : GaussianInt) := gcdDelta_aux_cancel hcopd hzm
    have hdm : (d : ℤ) ∣ m := by
      simpa using (Zsqrtd.intCast_dvd_intCast (d : ℤ) m).mp hdmG
    exact Nat.dvd_gcd hdn (Int.natCast_dvd.mp hdm)
  · -- and `(n, |m|)` divides the left hand side
    set g := Nat.gcd n m.natAbs with hgdef
    have hgn : g ∣ n := by rw [hgdef]; exact Nat.gcd_dvd_left _ _
    have hgm : g ∣ m.natAbs := by rw [hgdef]; exact Nat.gcd_dvd_right _ _
    have hgmZ : (g : ℤ) ∣ m := Int.natCast_dvd.mpr hgm
    have hgmG : (g : GaussianInt) ∣ (m : GaussianInt) := by
      simpa using (Zsqrtd.intCast_dvd_intCast (g : ℤ) m).mpr hgmZ
    have hgnG : (g : GaussianInt) ∣ (n : GaussianInt) := by
      have h : (g : ℤ) ∣ (n : ℤ) := by exact_mod_cast hgn
      simpa using (Zsqrtd.intCast_dvd_intCast (g : ℤ) (n : ℤ)).mpr h
    have hgX : (g : GaussianInt) ∣ X := hgnG.trans hX
    have hgz : (g : GaussianInt) ∣ z * (m : GaussianInt) := dvd_mul_of_dvd_right hgmG z
    have hgY : (g : GaussianInt) ∣ Y := by
      rw [hYdef]; exact dvd_sub hgz (dvd_mul_of_dvd_right hgX t)
    have hgYG : ((g : ℤ) : GaussianInt) ∣ Y := by simpa using hgY
    have hgre : (g : ℤ) ∣ Y.re := ((Zsqrtd.intCast_dvd (g : ℤ) Y).mp hgYG).1
    have hgim : (g : ℤ) ∣ Y.im := ((Zsqrtd.intCast_dvd (g : ℤ) Y).mp hgYG).2
    exact Nat.dvd_gcd (Nat.dvd_gcd (Int.natCast_dvd.mp hgre) (Int.natCast_dvd.mp hgim)) hgn

/-- **The Gaussian gcd `(Λ,Δ)` of (9.5) equals the rational gcd `(h₁²-a h₂², |Δ|)`.**  Under the
same hypotheses as the reduction of `Gsum` (`a` a residue of `z₂/z₁` modulo `|Δ|`, and
`(|z₁|²,|Δ|) = 1`),

  `gcdDelta z₁ z₂ h₁ h₂ = Nat.gcd |Δ| ((h₁² - a h₂²).natAbs)`,

where `Λ = z₁h₁² - z₂h₂²` (9.4) and `gcdDelta` is the largest `d ∣ |Δ|` dividing both components of
`Λ`.

Route: from `ha`, `(z̄₁z₂).im = Δ ≡ 0 (mod |Δ|)` and `z₁z̄₁ = |z₁|²` one gets
`z̄₁z₂ ≡ a z₁ z̄₁ (mod |Δ|)` in `ℤ[i]`; since `|z₁|²` is a unit modulo `|Δ|`, so is `z̄₁`, and
dividing gives `z₂ ≡ a z₁ (mod |Δ|)`.  Hence `Λ ≡ z₁(h₁² - a h₂²) (mod |Δ|)`.  Finally, for `d ∣ |Δ|`,
`d` divides both components of `X : ℤ[i]` iff `d ∣ X` in `ℤ[i]`, and multiplication by the unit `z₁`
of `ℤ[i]/|Δ|` induces a bijection of the divisors-of-`|Δ|` divisibility lattice (a unit modulo `|Δ|`
is a unit modulo every `d ∣ |Δ|`), so the largest such `d` for `Λ` equals that for `h₁² - a h₂²`,
i.e. `Nat.gcd |Δ| ((h₁²-a h₂²).natAbs)`. -/
theorem gcdDelta_eq_gcd (z1 z2 : GaussianInt) (a : ℤ) (h1 h2 : ℤ)
    (hD : Work.FIPlan.absDelta z1 z2 ≠ 0)
    (hni : Nat.Coprime (Work.FIPlan.gnorm z1) (Work.FIPlan.absDelta z1 z2))
    (ha : (a : ℤ) * (Work.FIPlan.gnorm z1 : ℤ)
        ≡ (star z1 * z2).re [ZMOD (Work.FIPlan.absDelta z1 z2 : ℤ)]) :
    Work.FIArea2.gcdDelta z1 z2 h1 h2
      = Nat.gcd (Work.FIPlan.absDelta z1 z2) ((h1 ^ 2 - a * h2 ^ 2).natAbs) := by
  have hX : ((Work.FIPlan.absDelta z1 z2 : ℕ) : GaussianInt)
      ∣ (z2 - (a : GaussianInt) * z1) := gcdDelta_aux_dvd_z2_sub_a_z1 z1 z2 a hni ha
  have hΛ : Lam z1 z2 h1 h2
      = z1 * ((h1 ^ 2 - a * h2 ^ 2 : ℤ) : GaussianInt)
        - ((h2 ^ 2 : ℤ) : GaussianInt) * (z2 - (a : GaussianInt) * z1) := by
    simp only [Lam]
    push_cast
    ring
  rw [gcdDelta, hΛ]
  exact gcdDelta_aux_gcd z1 (z2 - (a : GaussianInt) * z1) (h1 ^ 2 - a * h2 ^ 2) (h2 ^ 2)
    (Work.FIPlan.absDelta z1 z2) hni hX

end Work.FIArea2
