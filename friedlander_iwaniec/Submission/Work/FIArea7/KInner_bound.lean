/-
# `Submission.Work.FIArea7.KInner_bound` — the fibre bound for *FI* Proposition 22.1

For fixed real part `r`, the fibre `KInner Rz w k chi r` of the linear form `K(N)` is a sum over
`s` of the Jacobi–Kubota symbols `[w (r+is)]`.  This file rewrites that summand, using

* the multiplier rule in its primary form (`Work.FIArea7.jksym_mul_rule_primary`),
* the `ω`-representation of the Dirichlet symbol (`Work.FIArea7.dirichletSym_eq_jacobiSym_omega`)
  and its shift (`Work.FIArea7.jacobiSym_omega_shift`),

into the shape in which Pólya–Vinogradov applies: a constant times a sum, over the primary
`z = r + i s`, of the *sector weight* times the product of the two Jacobi characters
`(s | |r|)` and `(s - ω r | |w|²)`.
-/
import Mathlib
import Submission.Work.FIArea7.KSDefs
import Submission.Work.FIArea7.omega_rep
import Submission.Work.FIArea7.jksym_mul_rule_primary
import Submission.Work.FIArea7.twoChar_pv_dilated

set_option autoImplicit false

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The unit vector `z/|z|` attached to `z : ℤ[i]` (as a complex number). -/
def gunitC (z : GaussianInt) : ℂ := (z : ℂ) / ((‖(z : ℂ)‖ : ℝ) : ℂ)

lemma grossenChar_eq (chi : GaussianInt → ℂ) (k : ℤ) (z : GaussianInt) :
    grossenChar chi k z = chi z * gunitC z ^ k := rfl

/-- **The summand of the fibre, in the form used by Pólya–Vinogradov.**  For primary `w` (primitive)
and primary `z = r + i s`, and for `ω` with `ω·w.re ≡ -w.im` and `ω² + 1 ≡ 0 (mod |w|²)`,

  `ψ(z)[w z] = C·(χ(z)·(z/|z|)^k·ε(w,z)·(s | |r|)·(s - ω r | |w|²))`,

where `C = [w]·i^((r-1)/2)·(ω | |w|²)` is independent of `s`. -/
theorem term_eq (w : GaussianInt) (k : ℤ) (chi : GaussianInt → ℂ) (r s ω : ℤ)
    (hw : Work.FIPlan.IsPrimary w) (hcop : IsCoprime w.re w.im)
    (hz : Work.FIPlan.IsPrimary (⟨r, s⟩ : GaussianInt))
    (hω : ω * w.re ≡ -w.im [ZMOD ((Work.FIPlan.gnorm w : ℕ) : ℤ)])
    (hω2 : (ω ^ 2 + 1) ≡ 0 [ZMOD ((Work.FIPlan.gnorm w : ℕ) : ℤ)]) :
    grossenChar chi k (⟨r, s⟩ : GaussianInt) * JKSym (w * (⟨r, s⟩ : GaussianInt))
      = (JKSym w * Complex.I ^ ((r - 1) / 2) * (jacobiSym ω (Work.FIPlan.gnorm w) : ℂ))
        * (chi (⟨r, s⟩ : GaussianInt) * gunitC (⟨r, s⟩ : GaussianInt) ^ k
            * (MultEps w (⟨r, s⟩ : GaussianInt) : ℂ)
            * (jacobiSym s r.natAbs : ℂ)
            * (jacobiSym (s - ω * r) (Work.FIPlan.gnorm w) : ℂ)) := by
  have h1 : Work.FIArea7.DirichletSym w (⟨r, s⟩ : GaussianInt)
      = (jacobiSym ω (Work.FIPlan.gnorm w) : ℂ)
        * (jacobiSym (s - ω * r) (Work.FIPlan.gnorm w) : ℂ) := by
    rw [← Work.FIArea7.dirichletSym_eq_jacobiSym_omega hw hcop hω]
    dsimp only
    rw [Work.FIArea7.jacobiSym_omega_shift hω2 r s]
    push_cast
    ring
  rw [grossenChar, Work.FIArea7.jksym_mul_rule_primary hw hcop hz, h1]
  simp only [JKSym, JKCoeff, gunitC, Zsqrtd.re_mul, Zsqrtd.im_mul]
  push_cast
  ring

/-- The fibre `KInner` is a constant (`[w]·i^((r-1)/2)·(ω||w|²)`) times the sum of the sector weight
against the two Jacobi characters. -/
theorem KInner_eq_sum (Rz : ℤ) (w : GaussianInt) (k : ℤ) (chi : GaussianInt → ℂ) (r ω : ℤ)
    (hw : Work.FIPlan.IsPrimary w) (hcop : IsCoprime w.re w.im)
    (hω : ω * w.re ≡ -w.im [ZMOD ((Work.FIPlan.gnorm w : ℕ) : ℤ)])
    (hω2 : (ω ^ 2 + 1) ≡ 0 [ZMOD ((Work.FIPlan.gnorm w : ℕ) : ℤ)]) :
    KInner Rz w k chi r
      = (JKSym w * Complex.I ^ ((r - 1) / 2) * (jacobiSym ω (Work.FIPlan.gnorm w) : ℂ))
        * ∑ s ∈ Finset.Icc (-Rz) Rz,
            (if Work.FIPlan.IsPrimary (⟨r, s⟩ : GaussianInt) then
              chi (⟨r, s⟩ : GaussianInt) * gunitC (⟨r, s⟩ : GaussianInt) ^ k
                * (MultEps w (⟨r, s⟩ : GaussianInt) : ℂ)
                * (jacobiSym s r.natAbs : ℂ)
                * (jacobiSym (s - ω * r) (Work.FIPlan.gnorm w) : ℂ)
             else 0) := by
  rw [KInner, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hz : Work.FIPlan.IsPrimary (⟨r, s⟩ : GaussianInt)
  · rw [if_pos hz, if_pos hz, term_eq w k chi r s ω hw hcop hz hω hω2]
  · rw [if_neg hz, if_neg hz, mul_zero]

/-! ## The primary condition and the character are constant on residue classes mod `4d` -/

/-- `Even (b + 4 d v) ↔ Even b`. -/
lemma even_add_four_mul (b d v : ℤ) : Even (b + 4 * d * v) ↔ Even b := by
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t - 2 * d * v, by linear_combination ht⟩
  · rintro ⟨t, ht⟩
    exact ⟨t + 2 * d * v, by linear_combination ht⟩

/-- `(b + 4 d v) ≡ r - 1 [ZMOD 4] ↔ b ≡ r - 1 [ZMOD 4]`. -/
lemma modEq_four_add_four_mul (b d v r : ℤ) :
    (b + 4 * d * v ≡ r - 1 [ZMOD 4]) ↔ (b ≡ r - 1 [ZMOD 4]) := by
  rw [Int.modEq_iff_dvd, Int.modEq_iff_dvd]
  have h1 : r - 1 - (b + 4 * d * v) = (r - 1 - b) - 4 * d * v := by ring
  rw [h1]
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t + d * v, by linear_combination ht⟩
  · rintro ⟨t, ht⟩
    exact ⟨t - d * v, by linear_combination ht⟩

/-- For odd `r`, the primary condition on `⟨r, b + 4 d v⟩` depends only on `b`. -/
lemma isPrimary_mk_iff (r b d v : ℤ) (hr : Odd r) :
    Work.FIPlan.IsPrimary (⟨r, b + 4 * d * v⟩ : GaussianInt) ↔
      (Even b ∧ b ≡ r - 1 [ZMOD 4]) := by
  rw [Work.FIPlan.IsPrimary]
  dsimp only
  rw [even_add_four_mul, modEq_four_add_four_mul]
  exact ⟨fun h => ⟨h.2.1, h.2.2⟩, fun h => ⟨hr, h.1, h.2⟩⟩

/-- The `4d`-periodic character `χ` is constant along a residue class mod `4d`. -/
lemma chi_period (chi : GaussianInt → ℂ) (d : ℕ)
    (hper : ∀ a b : ℤ, chi (⟨a, b + 4 * (d : ℤ)⟩ : GaussianInt) = chi (⟨a, b⟩ : GaussianInt))
    (a b : ℤ) (v : ℤ) :
    chi (⟨a, b + 4 * (d : ℤ) * v⟩ : GaussianInt) = chi (⟨a, b⟩ : GaussianInt) := by
  induction v using Int.induction_on with
  | zero => simp
  | succ n ih =>
      rw [show b + 4 * (d : ℤ) * ((n : ℤ) + 1) = (b + 4 * (d : ℤ) * (n : ℤ)) + 4 * (d : ℤ) by ring,
        hper, ih]
  | pred n ih =>
      rw [show b + 4 * (d : ℤ) * (-(n : ℤ) - 1) = (b + 4 * (d : ℤ) * (-(n : ℤ))) - 4 * (d : ℤ)
            by ring]
      have h := hper a (b + 4 * (d : ℤ) * (-(n : ℤ)) - 4 * (d : ℤ))
      rw [show b + 4 * (d : ℤ) * (-(n : ℤ)) - 4 * (d : ℤ) + 4 * (d : ℤ)
            = b + 4 * (d : ℤ) * (-(n : ℤ)) by ring] at h
      rw [← h, ih]


/-- **The complex-weighted form of `Work.FIArea7.twoChar_pv_dilated`** for coprime odd moduli
`m₁` (with non-square odd part) and `m₂`, obtained by applying the real form to the real and
imaginary parts of the weight.  This is the shape in which the Pólya–Vinogradov estimate is fed
into the fibre bound: the weight is the sector character `(z/|z|)^k` times locally constant
factors. -/
theorem twoChar_complex_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (m₁ m₂ : ℕ) (hm₁ : Odd m₁) (hm₂ : Odd m₂) (hcop : Nat.Coprime m₁ m₂)
      (hgood : ∃ p : ℕ, p.Prime ∧ Odd (m₁.factorization p))
      (c₁ c₂ X Y : ℤ) (φ : ℤ → ℂ) (M D : ℝ),
      (∀ u : ℤ, ‖φ u‖ ≤ M) → (∀ u : ℤ, ‖φ (u + 1) - φ u‖ ≤ D) →
      ‖∑ u ∈ Finset.Icc X Y, (jacobiSym (u + c₁) m₁ : ℂ) * (jacobiSym (u + c₂) m₂ : ℂ) * φ u‖
        ≤ C * (M + ((Y - X).toNat : ℝ) * D) * Real.sqrt ((m₁ : ℝ) * (m₂ : ℝ))
            * (Real.log (2 + (m₁ : ℝ) * (m₂ : ℝ)) + 1) := by
  obtain ⟨C₀, hC₀pos, hPV⟩ := Work.FIArea7.twoChar_pv_dilated
  refine ⟨3 * C₀, by positivity, ?_⟩
  intro m₁ m₂ hm₁ hm₂ hcop hgood c₁ c₂ X Y φ M D hM hD
  have hshared : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ (m₁ : ℤ) → (p : ℤ) ∣ (m₂ : ℤ) →
      (p : ℤ) ∣ (1 : ℤ) := by
    intro p hp h1 h2
    exfalso
    have h1' : p ∣ m₁ := by exact_mod_cast h1
    have h2' : p ∣ m₂ := by exact_mod_cast h2
    have hgcd : p ∣ Nat.gcd m₁ m₂ := Nat.dvd_gcd h1' h2'
    rw [Nat.Coprime] at hcop
    rw [hcop] at hgcd
    have hle : p ≤ 1 := Nat.le_of_dvd (by norm_num) hgcd
    have h2p := hp.two_le
    omega
  have hgood' : ∃ p : ℕ, p.Prime ∧ ¬ (p : ℤ) ∣ (1 : ℤ) ∧ Odd (m₁.factorization p) := by
    obtain ⟨p, hp, hodd⟩ := hgood
    refine ⟨p, hp, ?_, hodd⟩
    intro hcon
    have hdv : p ∣ 1 := by exact_mod_cast hcon
    have hle : p ≤ 1 := Nat.le_of_dvd (by norm_num) hdv
    have h2p := hp.two_le
    omega
  have hre : ‖∑ u ∈ Finset.Icc X Y,
        (jacobiSym (u + c₁) m₁ : ℝ) * (jacobiSym (u + c₂) m₂ : ℝ) * (φ u).re‖
      ≤ C₀ * (M + ((Y - X).toNat : ℝ) * D) * Real.sqrt ((m₁ : ℝ) * (m₂ : ℝ))
          * (Real.log (2 + (m₁ : ℝ) * (m₂ : ℝ)) + 1) := by
    have h := hPV m₁ m₂ (1 : ℤ) c₁ c₂ X Y (fun u => (φ u).re) M D hm₁ hm₂ hshared hgood'
      (fun u => (Complex.abs_re_le_norm (φ u)).trans (hM u))
      (fun u => by
        have h' := (Complex.abs_re_le_norm (φ (u + 1) - φ u)).trans (hD u)
        rwa [Complex.sub_re] at h')
    simpa only [one_mul, Real.norm_eq_abs] using h
  have him : ‖∑ u ∈ Finset.Icc X Y,
        (jacobiSym (u + c₁) m₁ : ℝ) * (jacobiSym (u + c₂) m₂ : ℝ) * (φ u).im‖
      ≤ C₀ * (M + ((Y - X).toNat : ℝ) * D) * Real.sqrt ((m₁ : ℝ) * (m₂ : ℝ))
          * (Real.log (2 + (m₁ : ℝ) * (m₂ : ℝ)) + 1) := by
    have h := hPV m₁ m₂ (1 : ℤ) c₁ c₂ X Y (fun u => (φ u).im) M D hm₁ hm₂ hshared hgood'
      (fun u => (Complex.abs_im_le_norm (φ u)).trans (hM u))
      (fun u => by
        have h' := (Complex.abs_im_le_norm (φ (u + 1) - φ u)).trans (hD u)
        rwa [Complex.sub_im] at h')
    simpa only [one_mul, Real.norm_eq_abs] using h
  have hBnn : 0 ≤ C₀ * (M + ((Y - X).toNat : ℝ) * D) * Real.sqrt ((m₁ : ℝ) * (m₂ : ℝ))
      * (Real.log (2 + (m₁ : ℝ) * (m₂ : ℝ)) + 1) := by
    have hM0 : 0 ≤ M := le_trans (norm_nonneg (φ 0)) (hM 0)
    have hD0 : 0 ≤ D := le_trans (norm_nonneg _) (hD 0)
    have harg : (1 : ℝ) ≤ 2 + (m₁ : ℝ) * (m₂ : ℝ) := by
      have := Nat.cast_nonneg (α := ℝ) m₁
      have := Nat.cast_nonneg (α := ℝ) m₂
      nlinarith [mul_nonneg this this]
    have hlognn : 0 ≤ Real.log (2 + (m₁ : ℝ) * (m₂ : ℝ)) := Real.log_nonneg harg
    have h1 : 0 ≤ M + ((Y - X).toNat : ℝ) * D := by positivity
    have h2 : 0 ≤ Real.sqrt ((m₁ : ℝ) * (m₂ : ℝ)) := Real.sqrt_nonneg _
    have h3 : 0 ≤ Real.log (2 + (m₁ : ℝ) * (m₂ : ℝ)) + 1 := by linarith
    exact mul_nonneg (mul_nonneg (mul_nonneg hC₀pos.le h1) h2) h3
  have hdecomp :
      (∑ u ∈ Finset.Icc X Y, (jacobiSym (u + c₁) m₁ : ℂ) * (jacobiSym (u + c₂) m₂ : ℂ) * φ u)
        = ((∑ u ∈ Finset.Icc X Y,
              (jacobiSym (u + c₁) m₁ : ℝ) * (jacobiSym (u + c₂) m₂ : ℝ) * (φ u).re : ℝ) : ℂ)
          + Complex.I * ((∑ u ∈ Finset.Icc X Y,
              (jacobiSym (u + c₁) m₁ : ℝ) * (jacobiSym (u + c₂) m₂ : ℝ) * (φ u).im : ℝ) : ℂ) := by
    apply Complex.ext
    · rw [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
        Complex.I_im, Complex.re_sum, Complex.ofReal_sum]
      simp only [mul_zero, sub_zero, zero_mul, add_zero, zero_add, one_mul]
      apply Finset.sum_congr rfl
      intro u _
      simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.intCast_re, Complex.intCast_im, mul_zero, sub_zero, zero_mul]
      ring
    · rw [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
        Complex.I_im, Complex.im_sum, Complex.ofReal_sum]
      simp only [mul_zero, sub_zero, zero_mul, add_zero, zero_add, one_mul]
      apply Finset.sum_congr rfl
      intro u _
      simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.intCast_re, Complex.intCast_im, mul_zero, add_zero, zero_mul]
      ring
  calc ‖∑ u ∈ Finset.Icc X Y, (jacobiSym (u + c₁) m₁ : ℂ) * (jacobiSym (u + c₂) m₂ : ℂ) * φ u‖
      = ‖((∑ u ∈ Finset.Icc X Y,
              (jacobiSym (u + c₁) m₁ : ℝ) * (jacobiSym (u + c₂) m₂ : ℝ) * (φ u).re : ℝ) : ℂ)
          + Complex.I * ((∑ u ∈ Finset.Icc X Y,
              (jacobiSym (u + c₁) m₁ : ℝ) * (jacobiSym (u + c₂) m₂ : ℝ) * (φ u).im : ℝ) : ℂ)‖ := by
        rw [hdecomp]
    _ ≤ ‖((∑ u ∈ Finset.Icc X Y,
              (jacobiSym (u + c₁) m₁ : ℝ) * (jacobiSym (u + c₂) m₂ : ℝ) * (φ u).re : ℝ) : ℂ)‖
          + ‖Complex.I * ((∑ u ∈ Finset.Icc X Y,
              (jacobiSym (u + c₁) m₁ : ℝ) * (jacobiSym (u + c₂) m₂ : ℝ) * (φ u).im : ℝ) : ℂ)‖ :=
        norm_add_le _ _
    _ = ‖∑ u ∈ Finset.Icc X Y,
            (jacobiSym (u + c₁) m₁ : ℝ) * (jacobiSym (u + c₂) m₂ : ℝ) * (φ u).re‖
          + ‖∑ u ∈ Finset.Icc X Y,
            (jacobiSym (u + c₁) m₁ : ℝ) * (jacobiSym (u + c₂) m₂ : ℝ) * (φ u).im‖ := by
        rw [Complex.norm_real, norm_mul, Complex.norm_I, one_mul, Complex.norm_real]
    _ ≤ 2 * (C₀ * (M + ((Y - X).toNat : ℝ) * D) * Real.sqrt ((m₁ : ℝ) * (m₂ : ℝ))
            * (Real.log (2 + (m₁ : ℝ) * (m₂ : ℝ)) + 1)) := by
        linarith [hre, him]
    _ ≤ 3 * C₀ * (M + ((Y - X).toNat : ℝ) * D) * Real.sqrt ((m₁ : ℝ) * (m₂ : ℝ))
          * (Real.log (2 + (m₁ : ℝ) * (m₂ : ℝ)) + 1) := by
        nlinarith [hBnn, hC₀pos]

end

end Work.FIArea7
