import Mathlib
import Submission.Work.FIPlan.Interface
import Submission.Work.FIArea7.TwoCharPV.Basic
import Submission.Work.FIArea7.TwoCharPV.aFree_coprime
import Submission.Work.FIArea7.TwoCharPV.aFree_nonsquare
import Submission.Work.FIArea7.TwoCharPV.nonsquare_mul_of_coprime
import Submission.Work.FIArea7.TwoCharPV.pv_shifted_char
import Submission.Work.FIArea7.TwoCharPV.sum_Icc_int_reindex

set_option autoImplicit false

namespace Work.FIArea7

open scoped BigOperators

/-- For odd `q`, `oddPart q = q`. -/
lemma oddPart_eq_self_of_odd (q : ℕ) (hq : Odd q) : Work.FIPlan.oddPart q = q := by
  have h2 : ¬ 2 ∣ q := by
    intro h
    obtain ⟨k, hk⟩ := h
    obtain ⟨m, hm⟩ := hq
    omega
  rw [Work.FIPlan.oddPart, Nat.factorization_eq_zero_of_not_dvd h2, pow_zero, Nat.div_one]

/-- `p ∣ A.natAbs ↔ (p : ℤ) ∣ A`. -/
lemma nat_dvd_natAbs_iff {p : ℕ} {A : ℤ} : p ∣ A.natAbs ↔ (p : ℤ) ∣ A := by
  have h := Int.natAbs_dvd_natAbs (a := (p : ℤ)) (b := A)
  rw [Int.natAbs_natCast] at h
  exact h

/-- The Jacobi symbol has absolute value at most one. -/
lemma abs_jacobiSym_cast_le_one (a : ℤ) (b : ℕ) : |(jacobiSym a b : ℝ)| ≤ 1 := by
  rcases jacobiSym.trichotomy a b with h | h | h <;> rw [h] <;> norm_num

set_option maxHeartbeats 800000 in
/-- **The reduction of the product of two Jacobi-symbol characters to a single one.**
Writing `mⱼ = aCore A' mⱼ * aFree A' mⱼ` (with `A' = A.natAbs`), the `aCore` part contributes the
constant `J(cⱼ|aCore A' mⱼ)` (every prime of `aCore A' mⱼ` divides `A`), and the `aFree` part is a
dilated character `J(A|aFree A' mⱼ)·J(n + dⱼ|aFree A' mⱼ)`.  Because the two `aFree` parts are
coprime, the CRT combines these two into a single Jacobi symbol of modulus `aFree A' m₁ * aFree A' m₂`. -/
lemma twoChar_reduce (m₁ m₂ : ℕ) (A c₁ c₂ : ℤ) (hm₁ : Odd m₁) (hm₂ : Odd m₂)
    (hcommon : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ (m₁ : ℤ) → (p : ℤ) ∣ (m₂ : ℤ) → (p : ℤ) ∣ A)
    (hp : ∃ p : ℕ, p.Prime ∧ ¬ (p : ℤ) ∣ A ∧ Odd (m₁.factorization p)) :
    ∃ (Q : ℕ) (d K : ℤ), 1 ≤ Q ∧ Q ∣ m₁ * m₂ ∧
      (∀ k : ℕ, Work.FIPlan.oddPart Q ≠ k ^ 2) ∧ |(K : ℝ)| ≤ 1 ∧ ∀ n : ℤ,
        jacobiSym (A * n + c₁) m₁ * jacobiSym (A * n + c₂) m₂ = K * jacobiSym (n + d) Q := by
  have hm₁0 : 0 < m₁ := Nat.pos_of_ne_zero (fun h => by simp [h] at hm₁)
  have hm₂0 : 0 < m₂ := Nat.pos_of_ne_zero (fun h => by simp [h] at hm₂)
  set A' : ℕ := A.natAbs with hA'def
  set w₁ : ℕ := aFree A' m₁ with hw₁def
  set w₂ : ℕ := aFree A' m₂ with hw₂def
  set u₁ : ℕ := aCore A' m₁ with hu₁def
  set u₂ : ℕ := aCore A' m₂ with hu₂def
  have hw₁0 : w₁ ≠ 0 := (aFree_pos (A := A') hm₁0).ne'
  have hw₂0 : w₂ ≠ 0 := (aFree_pos (A := A') hm₂0).ne'
  have hu₁0 : u₁ ≠ 0 := (aCore_pos (A := A') hm₁0).ne'
  have hu₂0 : u₂ ≠ 0 := (aCore_pos (A := A') hm₂0).ne'
  have hw₁dvd : w₁ ∣ m₁ := aFree_dvd A' m₁
  have hw₂dvd : w₂ ∣ m₂ := aFree_dvd A' m₂
  have hsplit₁ : u₁ * w₁ = m₁ := aCore_mul_aFree A' m₁
  have hsplit₂ : u₂ * w₂ = m₂ := aCore_mul_aFree A' m₂
  -- coprimality of `wⱼ` with `A`
  have hcop₁ : Nat.Coprime w₁ A' := TwoCharPV.aFree_coprime A' m₁ hm₁0
  have hcop₂ : Nat.Coprime w₂ A' := TwoCharPV.aFree_coprime A' m₂ hm₂0
  have hiscop₁ : IsCoprime A (w₁ : ℤ) := by
    rw [Int.isCoprime_iff_nat_coprime, Int.natAbs_natCast]
    exact hcop₁.symm
  have hiscop₂ : IsCoprime A (w₂ : ℤ) := by
    rw [Int.isCoprime_iff_nat_coprime, Int.natAbs_natCast]
    exact hcop₂.symm
  -- the dilation parameters
  obtain ⟨d₁, hd₁⟩ := exists_dvd_mul_sub (w := w₁) (A := A) (c := c₁) hiscop₁
  obtain ⟨d₂, hd₂⟩ := exists_dvd_mul_sub (w := w₂) (A := A) (c := c₂) hiscop₂
  -- the two reduced moduli are coprime
  have hgcd : Nat.Coprime w₁ w₂ := by
    by_contra hcon
    obtain ⟨p, hpp, hpw₁, hpw₂⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcon
    have hpA : (p : ℤ) ∣ A :=
      hcommon p hpp (by exact_mod_cast hpw₁.trans hw₁dvd)
        (by exact_mod_cast hpw₂.trans hw₂dvd)
    have hpA' : p ∣ A' := by
      have : p ∣ A.natAbs := Int.natAbs_dvd_natAbs.mpr hpA
      simpa [A'] using this
    exact (Nat.Prime.not_coprime_iff_dvd.mpr ⟨p, hpp, hpw₁, hpA'⟩) hcop₁
  -- the CRT parameter
  obtain ⟨d, hdc, hdc'⟩ := exists_crt_int (u := w₁) (v := w₂) hgcd d₁ d₂
  refine ⟨w₁ * w₂, d,
    jacobiSym c₁ u₁ * jacobiSym c₂ u₂ * jacobiSym A w₁ * jacobiSym A w₂, ?_, ?_, ?_, ?_, ?_⟩
  · exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_pos (aFree_pos (A := A') hm₁0)
      (aFree_pos (A := A') hm₂0)).ne'
  · exact Nat.mul_dvd_mul hw₁dvd hw₂dvd
  · -- `oddPart (w₁ * w₂)` is not a square
    have hQodd : Odd (w₁ * w₂) := (hm₁.of_dvd_nat hw₁dvd).mul (hm₂.of_dvd_nat hw₂dvd)
    have hw₁nsq : ∀ k : ℕ, w₁ ≠ k ^ 2 := by
      refine TwoCharPV.aFree_nonsquare A' m₁ hm₁0 ?_
      obtain ⟨p, hpp, hpA, hpodd⟩ := hp
      exact ⟨p, hpp, fun hdiv => hpA (Int.natAbs_dvd_natAbs.mp (by simpa [A'] using hdiv)), hpodd⟩
    have hQnsq : ∀ k : ℕ, w₁ * w₂ ≠ k ^ 2 :=
      TwoCharPV.nonsquare_mul_of_coprime hgcd hw₁nsq
    intro k hk
    rw [oddPart_eq_self_of_odd _ hQodd] at hk
    exact hQnsq k hk
  · -- the constant has absolute value at most one
    have h₁ := abs_jacobiSym_cast_le_one c₁ u₁
    have h₂ := abs_jacobiSym_cast_le_one c₂ u₂
    have h₃ := abs_jacobiSym_cast_le_one A w₁
    have h₄ := abs_jacobiSym_cast_le_one A w₂
    push_cast
    rw [abs_mul, abs_mul, abs_mul]
    calc |(jacobiSym c₁ u₁ : ℝ)| * |(jacobiSym c₂ u₂ : ℝ)| * |(jacobiSym A w₁ : ℝ)|
            * |(jacobiSym A w₂ : ℝ)|
        ≤ 1 * 1 * 1 * 1 := by gcongr
      _ = 1 := by norm_num
  · -- the pointwise identity
    intro n
    have h₁ : jacobiSym (A * n + c₁) m₁
        = jacobiSym c₁ u₁ * (jacobiSym A w₁ * jacobiSym (n + d₁) w₁) := by
      rw [← hsplit₁, jacobiSym.mul_right' _ hu₁0 hw₁0,
        jacobiSym_const_of_prime_dvd (u := u₁) (A := A) ?_ c₁ n, jacobiSym_dilate hd₁ n]
      intro p hpp hpu
      rw [hu₁def] at hpu
      exact nat_dvd_natAbs_iff.mp (by simpa [A'] using aCore_prime_dvd hpp hpu)
    have h₂ : jacobiSym (A * n + c₂) m₂
        = jacobiSym c₂ u₂ * (jacobiSym A w₂ * jacobiSym (n + d₂) w₂) := by
      rw [← hsplit₂, jacobiSym.mul_right' _ hu₂0 hw₂0,
        jacobiSym_const_of_prime_dvd (u := u₂) (A := A) ?_ c₂ n, jacobiSym_dilate hd₂ n]
      intro p hpp hpu
      rw [hu₂def] at hpu
      exact nat_dvd_natAbs_iff.mp (by simpa [A'] using aCore_prime_dvd hpp hpu)
    have h₃ : jacobiSym (n + d₁) w₁ * jacobiSym (n + d₂) w₂ = jacobiSym (n + d) (w₁ * w₂) :=
      jacobiSym_crt_mul w₁ w₂ hw₁0 hw₂0 hdc hdc' n
    rw [h₁, h₂, ← h₃]
    ring

/-- **Pólya–Vinogradov for a product of two Jacobi-symbol characters, in arithmetic progressions.**

This is the analytic core of *FI* Proposition 22.1: the sum over an interval of the product of two
Jacobi symbols `(A n + c₁ | m₁)` and `(A n + c₂ | m₂)`, where the two moduli `m₁, m₂` share only
primes dividing the common "step" `A`, and where the part of `m₁` coprime to `A` is not a square
(so the corresponding Jacobi character is a *non-principal* Dirichlet character after the dilation
is removed).  The weight `φ` is bounded by `M` with first differences bounded by `D`, which gives
the loss `M + (length)·D` of summation by parts.

The intended proof: remove the `A`-primes from both moduli (the dilation reduction
`(A n + c|m) = (c | m^{>A})·(A | m')·(n + c A⁻¹ | m')` with `m'` the `A`-coprime part of `m`; when
`gcd(c, m^{>A}) > 1` the factor `(c | m^{>A})` is simply `0` and the identity still holds), so that
the two reduced moduli are coprime and the first one has non-square odd part; both factors are then
(up to constants) Jacobi symbols with coprime odd moduli, the first non-principal.  Reduce each
Jacobi symbol to its squarefree kernel (a primitive quadratic character,
`Work.FIArea4.jacobiSym_sqfreeKernel_of_coprime`, `Work.FIArea4.jacobiChar_isPrimitive`) times the
Möbius coprimality indicator `∑_{e | rad m} μ(e)[e | (A n + c)]`; the terms with `e` sharing a
prime with the squarefree kernel vanish identically, so only `e | rad(m/m')` survive (at most
`2√(m₁/m₁')·2√(m₂/m₂')` surviving pairs).  For each surviving pair the sum becomes a *primitive*
two-character sum over an arithmetic progression, bounded by the double DFT expansion
(`Work.FIArea4.pv_primitive`, `DirichletCharacter.IsPrimitive.fourierTransform_eq_inv_mul_gaussSum`,
`Commons.NumberTheory.DirichletCharacter.gaussSum_norm_sq_of_isPrimitive`) with
`‖gaussSum χ stdAddChar‖ = √m`: the frequencies `a/m₁' + b/m₂'` run over the `m₁'m₂'` grid, each
exponential sum being `≪ min(length, 1/‖θ‖)`, so that `∑ min(length, 1/‖θ‖) ≪ m₁'m₂'(1+log(m₁'m₂'))`
(harmonic bound).  Finally `2√(m₁/m₁')·2√(m₂/m₂')·√(m₁'m₂') = 4√(m₁m₂)`. -/
theorem twoChar_pv_dilated :
    ∃ C : ℝ, 0 < C ∧ ∀ (m₁ m₂ : ℕ) (A c₁ c₂ X Y : ℤ) (φ : ℤ → ℝ) (M D : ℝ),
      Odd m₁ → Odd m₂ →
      (∀ p : ℕ, p.Prime → (p : ℤ) ∣ (m₁ : ℤ) → (p : ℤ) ∣ (m₂ : ℤ) → (p : ℤ) ∣ A) →
      (∃ p : ℕ, p.Prime ∧ ¬ (p : ℤ) ∣ A ∧ Odd (m₁.factorization p)) →
      (∀ n : ℤ, |φ n| ≤ M) → (∀ n : ℤ, |φ (n + 1) - φ n| ≤ D) →
      |∑ n ∈ Finset.Icc X Y,
          (jacobiSym (A * n + c₁) m₁ : ℝ) * (jacobiSym (A * n + c₂) m₂ : ℝ) * φ n|
        ≤ C * (M + (((Y - X).toNat : ℝ)) * D) * Real.sqrt ((m₁ : ℝ) * (m₂ : ℝ))
            * (Real.log (2 + (m₁ : ℝ) * (m₂ : ℝ)) + 1) := by
  obtain ⟨C₀, hC₀pos, hpv⟩ := TwoCharPV.pv_shifted_char
  refine ⟨C₀, hC₀pos, fun m₁ m₂ A c₁ c₂ X Y φ M D hm₁ hm₂ hcommon hp hφ hd => ?_⟩
  have hM : 0 ≤ M := le_trans (abs_nonneg (φ 0)) (hφ 0)
  have hD : 0 ≤ D := le_trans (abs_nonneg (φ 1 - φ 0)) (hd 0)
  by_cases hXY : X ≤ Y
  · -- the interval is non-empty: reduce to a single Jacobi character and apply Pólya–Vinogradov
    have hm₁0 : 0 < m₁ := Nat.pos_of_ne_zero (fun h => by simp [h] at hm₁)
    have hm₂0 : 0 < m₂ := Nat.pos_of_ne_zero (fun h => by simp [h] at hm₂)
    obtain ⟨Q, d, K, hQ1, hQdvd, hQns, hKb, hpoint⟩ :=
      twoChar_reduce m₁ m₂ A c₁ c₂ hm₁ hm₂ hcommon hp
    have hsum : ∑ n ∈ Finset.Icc X Y,
          (jacobiSym (A * n + c₁) m₁ : ℝ) * (jacobiSym (A * n + c₂) m₂ : ℝ) * φ n
        = (K : ℝ) * ∑ n ∈ Finset.Icc X Y, (jacobiSym (n + d) Q : ℝ) * φ n := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun n _ => ?_)
      rw [← Int.cast_mul, hpoint n]
      push_cast
      ring
    have hshift : ∑ n ∈ Finset.Icc X Y, (jacobiSym (n + d) Q : ℝ) * φ n
        = ∑ t ∈ Finset.Icc 0 (Y - X).toNat,
            (jacobiSym ((t : ℤ) + (X + d)) Q : ℝ) * φ (X + (t : ℤ)) := by
      rw [TwoCharPV.sum_Icc_int_reindex X Y hXY
        (fun n => (jacobiSym (n + d) Q : ℝ) * φ n)]
      refine Finset.sum_congr rfl (fun t _ => ?_)
      rw [show X + (t : ℤ) + d = (t : ℤ) + (X + d) by ring]
    rw [hsum, abs_mul, hshift]
    -- the Pólya–Vinogradov bound
    have hpvb := hpv Q (X + d) (Y - X).toNat (fun t => φ (X + (t : ℤ))) M D hQ1 hQns
      (fun t => hφ _) (fun t => by
        have h : ((t + 1 : ℕ) : ℤ) = (t : ℤ) + 1 := by push_cast; ring
        rw [h, show X + ((t : ℤ) + 1) = X + (t : ℤ) + 1 by ring]
        exact hd _)
    -- size comparisons for the modulus
    have hQle : Q ≤ m₁ * m₂ := Nat.le_of_dvd (Nat.mul_pos hm₁0 hm₂0) hQdvd
    have hsqrt : Real.sqrt (Q : ℝ)
        ≤ Real.sqrt ((m₁ : ℝ) * (m₂ : ℝ)) := by
      rw [← Nat.cast_mul]
      exact Real.sqrt_le_sqrt (by exact_mod_cast hQle)
    have hlog : Real.log (Q : ℝ) + 1
        ≤ Real.log (2 + (m₁ : ℝ) * (m₂ : ℝ)) + 1 := by
      have hQ0 : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast (show 0 < Q by omega)
      have hle2 : (Q : ℝ) ≤ 2 + (m₁ : ℝ) * (m₂ : ℝ) := by
        have hcast : (Q : ℝ) ≤ ((m₁ * m₂ : ℕ) : ℝ) := by exact_mod_cast hQle
        push_cast at hcast ⊢
        linarith
      linarith [Real.log_le_log hQ0 hle2]
    have hL1 : 0 ≤ Real.log (Q : ℝ) + 1 := by
      have := Real.log_nonneg (show (1 : ℝ) ≤ (Q : ℝ) by exact_mod_cast hQ1)
      linarith
    have hL2 : 0 ≤ Real.log (2 + (m₁ : ℝ) * (m₂ : ℝ)) + 1 := by
      have h2 : (1 : ℝ) ≤ 2 + (m₁ : ℝ) * (m₂ : ℝ) := by
        have h3 : 0 ≤ (m₁ : ℝ) * (m₂ : ℝ) := by positivity
        linarith
      linarith [Real.log_nonneg h2]
    have ha : 0 ≤ C₀ * (M + (((Y - X).toNat : ℝ)) * D) := by
      have h1 : 0 ≤ (((Y - X).toNat : ℝ)) * D := mul_nonneg (by positivity) hD
      have h2 : 0 ≤ M + (((Y - X).toNat : ℝ)) * D := by linarith
      exact mul_nonneg (le_of_lt hC₀pos) h2
    calc |(K : ℝ)| * |∑ t ∈ Finset.Icc 0 (Y - X).toNat,
            (jacobiSym ((t : ℤ) + (X + d)) Q : ℝ) * φ (X + (t : ℤ))|
        ≤ 1 * (C₀ * (M + (((Y - X).toNat : ℝ)) * D) * Real.sqrt (Q : ℝ)
            * (Real.log (Q : ℝ) + 1)) :=
          mul_le_mul hKb hpvb (abs_nonneg _) (by norm_num)
      _ = C₀ * (M + (((Y - X).toNat : ℝ)) * D) * Real.sqrt (Q : ℝ)
            * (Real.log (Q : ℝ) + 1) := by ring
      _ ≤ C₀ * (M + (((Y - X).toNat : ℝ)) * D) * Real.sqrt ((m₁ : ℝ) * (m₂ : ℝ))
            * (Real.log (2 + (m₁ : ℝ) * (m₂ : ℝ)) + 1) := by
          have h1 : C₀ * (M + (((Y - X).toNat : ℝ)) * D) * Real.sqrt (Q : ℝ)
                * (Real.log (Q : ℝ) + 1)
              ≤ C₀ * (M + (((Y - X).toNat : ℝ)) * D) * Real.sqrt ((m₁ : ℝ) * (m₂ : ℝ))
                * (Real.log (Q : ℝ) + 1) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsqrt ha) hL1
          have h2 : C₀ * (M + (((Y - X).toNat : ℝ)) * D) * Real.sqrt ((m₁ : ℝ) * (m₂ : ℝ))
                * (Real.log (Q : ℝ) + 1)
              ≤ C₀ * (M + (((Y - X).toNat : ℝ)) * D) * Real.sqrt ((m₁ : ℝ) * (m₂ : ℝ))
                * (Real.log (2 + (m₁ : ℝ) * (m₂ : ℝ)) + 1) :=
            mul_le_mul_of_nonneg_left hlog (mul_nonneg ha (Real.sqrt_nonneg _))
          exact le_trans h1 h2
  · -- the interval is empty
    have hempty : Finset.Icc X Y = ∅ := Finset.Icc_eq_empty_iff.mpr hXY
    have hN0 : (Y - X).toNat = 0 := Int.toNat_of_nonpos (by omega)
    rw [hempty, Finset.sum_empty, abs_zero, hN0]
    simp only [Nat.cast_zero, mul_zero, add_zero]
    have hlog : 0 ≤ Real.log (2 + (m₁ : ℝ) * (m₂ : ℝ)) + 1 := by
      have h1 : (1 : ℝ) ≤ 2 + (m₁ : ℝ) * (m₂ : ℝ) := by
        have h2 : 0 ≤ (m₁ : ℝ) * (m₂ : ℝ) := by positivity
        linarith
      linarith [Real.log_nonneg h1]
    have hM' : (0 : ℝ) ≤ M + 0 * D := by rw [zero_mul, add_zero]; exact hM
    exact mul_nonneg (mul_nonneg (mul_nonneg (le_of_lt hC₀pos) hM')
      (Real.sqrt_nonneg _)) hlog

end Work.FIArea7
