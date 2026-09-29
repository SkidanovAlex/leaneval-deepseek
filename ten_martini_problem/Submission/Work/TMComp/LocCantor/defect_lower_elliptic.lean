/-
Avila–Jitomirskaya, *The Ten Martini Problem*: the elliptic lower bound for the
defect of a `SL₂(ℝ)` cocycle step.

For `A ∈ SL₂(ℝ)` with `|tr A| ≤ 2` the Frobenius norms of `A^m` and `A^{2m}` are
compared.  Writing `s` for the sum of the squares of the entries of `A`,
`X = s - 2` and `Y = 2 - (tr A)²/2`, one has

* `frob(A^k)² = 2 + X · α_k²`  where `α₀ = 0`, `α₁ = 1`, `α_{k+2} = tr A · α_{k+1} - α_k`
  (the sequence `α_k = U_{k-1}(tr A / 2)` of Chebyshev polynomials of the second kind);
* `(1 - (tr A)²/4) · α_k² ≤ 1`, which for `X ≥ 0` gives `Y · S_m ≤ (Y + X) · S_{2m}`
  with `S_k = frob(A^k)²`, hence the logarithmic bound.

In the degenerate case `Y = 0` one has `tr A = ±2`, so `α_k² = k²` and `S_m ≤ S_{2m}`
directly.
-/
import Mathlib
import Submission.Work.TMC7Core.Cocycle
import Submission.Work.TMC7Core.Scale.frob_map_ofReal_sq
import Submission.Work.TMComp.LocCantor.Auxiliary.matrix_pow_alpha

namespace Work.TMComp.LocCantor

/-! ## The sequence `α` attached to a real number `t` -/

/-- `alpha t` is the sequence with `alpha t 0 = 0`, `alpha t 1 = 1` and
`alpha t (k+2) = t * alpha t (k+1) - alpha t k`.  It is `U_{k-1}(t/2)`. -/
def alpha (t : ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => 1
  | k + 2 => t * alpha t (k + 1) - alpha t k

@[simp] lemma alpha_zero (t : ℝ) : alpha t 0 = 0 := rfl

@[simp] lemma alpha_one (t : ℝ) : alpha t 1 = 1 := rfl

lemma alpha_add_two (t : ℝ) (k : ℕ) : alpha t (k + 2) = t * alpha t (k + 1) - alpha t k := rfl

/-- Invariant quadratic form: `α_k² - t α_k α_{k+1} + α_{k+1}² = 1`. -/
lemma alpha_quad (t : ℝ) (k : ℕ) :
    alpha t k ^ 2 - t * alpha t k * alpha t (k + 1) + alpha t (k + 1) ^ 2 = 1 := by
  induction k with
  | zero => simp [alpha]
  | succ k ih =>
      have hstep : alpha t (k + 1) ^ 2 - t * alpha t (k + 1) * alpha t (k + 2)
            + alpha t (k + 2) ^ 2
          = alpha t k ^ 2 - t * alpha t k * alpha t (k + 1) + alpha t (k + 1) ^ 2 := by
        rw [alpha_add_two t k]; ring
      rw [hstep, ih]

/-- Catalan (Casorati) identity: `α_{k+2} α_k - α_{k+1}² = -1`. -/
lemma alpha_catalan (t : ℝ) (k : ℕ) : alpha t (k + 2) * alpha t k - alpha t (k + 1) ^ 2 = -1 := by
  have hq := alpha_quad t k
  rw [alpha_add_two t k]
  nlinarith [hq]

/-- Consequence of `alpha_quad`: `(1 - (t/2)²) α_k² ≤ 1` for every `k`. -/
lemma alpha_sq_mul_le (t : ℝ) (k : ℕ) : (1 - (t / 2) ^ 2) * alpha t k ^ 2 ≤ 1 := by
  cases k with
  | zero => simp [alpha]
  | succ j =>
      have hQ := alpha_quad t j
      have hdecomp : (alpha t j - (t / 2) * alpha t (j + 1)) ^ 2
            + (1 - (t / 2) ^ 2) * alpha t (j + 1) ^ 2 = 1 := by
        nlinarith [hQ]
      nlinarith [sq_nonneg (alpha t j - (t / 2) * alpha t (j + 1))]

/-- If `t² = 4` then `α_k² = k²`. -/
lemma alpha_sq_eq_sq_of_sq_eq_four (α : ℕ → ℝ) (h0 : α 0 = 0) (h1 : α 1 = 1)
    (t : ℝ) (ht : t ^ 2 = 4) (hrec : ∀ k, α (k + 2) = t * α (k + 1) - α k) (k : ℕ) :
    α k ^ 2 = (k : ℝ) ^ 2 := by
  set ε := t / 2 with hε
  have hε2 : ε ^ 2 = 1 := by rw [hε]; nlinarith [ht]
  have hrec' : ∀ j, α (j + 2) = 2 * ε * α (j + 1) - α j := by
    intro j; rw [hrec j, hε]; ring
  -- `β j = ε^j α j` satisfies the `ε = 1` recursion, whose solutions are affine
  set β : ℕ → ℝ := fun j => ε ^ j * α j with hβ
  have hβrec : ∀ j, β (j + 2) = 2 * β (j + 1) - β j := by
    intro j
    have e : ε ^ (j + 2) = ε ^ j := by rw [pow_add, hε2, mul_one]
    have e2 : ε ^ (j + 1) = ε ^ j * ε := pow_succ ε j
    simp only [hβ, e, e2, hrec' j]
    ring
  have haffine : ∀ j, β j = β 0 + (j : ℝ) * (β 1 - β 0) := by
    intro j
    induction j using Nat.twoStepInduction with
    | zero => ring
    | one => ring
    | more n ih1 ih2 =>
        rw [hβrec n, ih1, ih2]
        push_cast
        ring
  have hβ0 : β 0 = 0 := by simp [hβ, h0]
  have hβ1 : β 1 = ε := by simp [hβ, h1]
  have hbk : ε ^ k * α k = (k : ℝ) * ε := by
    have h : β k = (k : ℝ) * ε := by
      rw [haffine k, hβ0, hβ1]
      ring
    rwa [hβ] at h
  have hεkk : ε ^ k * ε ^ k = 1 := by
    rw [← pow_add, show k + k = 2 * k by ring, pow_mul, hε2, one_pow]
  have hαk : α k = ε ^ k * ((k : ℝ) * ε) := by
    calc α k = ε ^ k * ε ^ k * α k := by rw [hεkk, one_mul]
      _ = ε ^ k * (ε ^ k * α k) := by ring
      _ = ε ^ k * ((k : ℝ) * ε) := by rw [hbk]
  rw [hαk]
  have hpow : (ε ^ k) ^ 2 = 1 := by
    rw [← pow_mul, show k * 2 = 2 * k by ring, pow_mul, hε2, one_pow]
  rw [mul_pow, mul_pow, hpow, hε2]
  ring

/-! ## Sum of the squares of the entries -/

/-- Sum of the squares of the entries of a `2 × 2` real matrix. -/
def esq (M : Matrix (Fin 2) (Fin 2) ℝ) : ℝ := M 0 0 ^ 2 + M 0 1 ^ 2 + M 1 0 ^ 2 + M 1 1 ^ 2

lemma esq_smul_sub_one (A : Matrix (Fin 2) (Fin 2) ℝ) (x y : ℝ) :
    esq (x • A - y • (1 : Matrix (Fin 2) (Fin 2) ℝ))
      = x ^ 2 * esq A - 2 * x * y * (A 0 0 + A 1 1) + 2 * y ^ 2 := by
  simp only [esq, Matrix.sub_apply, Matrix.smul_apply]
  simp
  ring

/-! ## The Frobenius norm of the powers -/

lemma frob_map_ofRealHom_sq (B : Matrix (Fin 2) (Fin 2) ℝ) :
    (Work.TMC7Core.frob (B.map Complex.ofRealHom)) ^ 2 = esq B := by
  have hfun : B.map Complex.ofRealHom = B.map (fun x => (x : ℂ)) := rfl
  rw [hfun, Work.TMC7Core.Scale.frob_map_ofReal_sq]
  rfl

/-- `frob(A^k)² = 2 + (s - 2) α_k²` for `k ≥ 1`, where `s` is the sum of the squares
of the entries of `A`. -/
lemma frob_pow_sq (A : Matrix (Fin 2) (Fin 2) ℝ) (hdet : A.det = 1) (k : ℕ) (hk : 1 ≤ k) :
    (Work.TMC7Core.frob ((A.map Complex.ofRealHom) ^ k)) ^ 2
      = 2 + (esq A - 2) * (alpha A.trace k) ^ 2 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have h0 : alpha A.trace 0 = 0 := rfl
  have h1 : alpha A.trace 1 = 1 := rfl
  have hrec : ∀ n, alpha A.trace (n + 2) = A.trace * alpha A.trace (n + 1) - alpha A.trace n :=
    fun n => rfl
  have hp := Aux.matrix_pow_alpha A hdet (alpha A.trace) h0 h1 hrec j
  rw [← Matrix.map_pow, frob_map_ofRealHom_sq, hp, esq_smul_sub_one]
  have hlin : A.trace * alpha A.trace (j + 1) = alpha A.trace (j + 2) + alpha A.trace j := by
    rw [alpha_add_two A.trace j]; ring
  have hcat : alpha A.trace (j + 2) * alpha A.trace j - alpha A.trace (j + 1) ^ 2 = -1 :=
    alpha_catalan A.trace j
  have htr : A 0 0 + A 1 1 = A.trace := (Matrix.trace_fin_two A).symm
  rw [htr]
  linear_combination (-2 * alpha A.trace j) * hlin + (-2) * hcat

/-! ## The main bound -/

theorem defect_lower_elliptic (A : Matrix (Fin 2) (Fin 2) ℝ) (hdet : A.det = 1) (m : ℕ) (hm : 1 ≤ m)
    (hτ : |A.trace| ≤ 2) :
    0.5 * Real.log ((2 - A.trace ^ 2 / 2) /
        (2 - A.trace ^ 2 / 2 + (A 0 0 ^ 2 + A 0 1 ^ 2 + A 1 0 ^ 2 + A 1 1 ^ 2 - 2)))
      ≤ Real.log (Work.TMC7Core.frob ((A.map Complex.ofRealHom) ^ (2 * m)))
        - Real.log (Work.TMC7Core.frob ((A.map Complex.ofRealHom) ^ m)) := by
  set t := A.trace with ht
  set S := A 0 0 ^ 2 + A 0 1 ^ 2 + A 1 0 ^ 2 + A 1 1 ^ 2 with hS
  set X := S - 2 with hX
  set Y := 2 - t ^ 2 / 2 with hY
  have ht' : A.trace = t := ht.symm
  have hSe : esq A = S := by rw [hS]; rfl
  have hm2 : 1 ≤ 2 * m := by omega
  -- the Frobenius norms of the powers
  have hfrob : ∀ k, 1 ≤ k → (Work.TMC7Core.frob ((A.map Complex.ofRealHom) ^ k)) ^ 2
      = 2 + X * (alpha t k) ^ 2 := by
    intro k hk
    have h := frob_pow_sq A hdet k hk
    rw [hSe, ht'] at h
    rw [h]
  have hlogfrob : ∀ k, 1 ≤ k → Real.log (Work.TMC7Core.frob ((A.map Complex.ofRealHom) ^ k))
      = 0.5 * Real.log (2 + X * (alpha t k) ^ 2) := by
    intro k hk
    have h := hfrob k hk
    rw [← Real.sqrt_sq (Work.TMC7Core.frob_nonneg ((A.map Complex.ofRealHom) ^ k))]
    rw [Real.log_sqrt (by positivity)]
    rw [h]
    ring
  have hXnn : 0 ≤ X := by
    rw [hX, hS]
    have h := hdet
    rw [Matrix.det_fin_two] at h
    nlinarith [sq_nonneg (A 0 0 - A 1 1), sq_nonneg (A 0 1 + A 1 0)]
  have hYnn : 0 ≤ Y := by
    rw [hY, ht]
    have h := hτ
    rw [abs_le] at h
    nlinarith [h.1, h.2]
  rcases lt_or_eq_of_le hYnn with hYpos | hYzero
  · -- nondegenerate case `Y > 0`
    have hb : (1 - (t / 2) ^ 2) * (alpha t m) ^ 2 ≤ 1 := alpha_sq_mul_le t m
    have hYeq : Y = 2 * (1 - (t / 2) ^ 2) := by rw [hY]; ring
    have hSm : 0 < 2 + X * (alpha t m) ^ 2 := by
      nlinarith [mul_nonneg hXnn (sq_nonneg (alpha t m))]
    have hS2m : 0 < 2 + X * (alpha t (2 * m)) ^ 2 := by
      nlinarith [mul_nonneg hXnn (sq_nonneg (alpha t (2 * m)))]
    have hkey : Y * (2 + X * (alpha t m) ^ 2)
        ≤ (Y + X) * (2 + X * (alpha t (2 * m)) ^ 2) := by
      have h1 : Y * (alpha t m) ^ 2 ≤ 2 := by
        rw [hYeq]; nlinarith [hb]
      have h2 : X * (Y * (alpha t m) ^ 2) ≤ X * 2 := mul_le_mul_of_nonneg_left h1 hXnn
      have h3 : 0 ≤ (Y + X) * (X * (alpha t (2 * m)) ^ 2) :=
        mul_nonneg (by linarith) (mul_nonneg hXnn (sq_nonneg _))
      nlinarith [h2, h3]
    have hquot : Y / (Y + X)
        ≤ (2 + X * (alpha t (2 * m)) ^ 2) / (2 + X * (alpha t m) ^ 2) := by
      rw [div_le_div_iff₀ (by linarith) hSm]
      linarith [hkey]
    have hl := Real.log_le_log (div_pos hYpos (by linarith)) hquot
    rw [Real.log_div (ne_of_gt hS2m) (ne_of_gt hSm)] at hl
    rw [hlogfrob (2 * m) hm2, hlogfrob m hm]
    linarith
  · -- degenerate case `Y = 0`
    have hYz : Y = 0 := hYzero.symm
    have hL : 0.5 * Real.log (Y / (Y + X)) = 0 := by
      rw [hYz, zero_div, Real.log_zero, mul_zero]
    have ht2 : t ^ 2 = 4 := by
      have h := hY
      rw [hYz] at h
      linarith
    have halpha : ∀ k, (alpha t k) ^ 2 = (k : ℝ) ^ 2 := by
      intro k
      have hrec : ∀ j, alpha t (j + 2) = t * alpha t (j + 1) - alpha t j :=
        fun j => alpha_add_two t j
      exact alpha_sq_eq_sq_of_sq_eq_four (alpha t) rfl rfl t ht2 hrec k
    have hkey : 2 + X * (alpha t m) ^ 2 ≤ 2 + X * (alpha t (2 * m)) ^ 2 := by
      rw [halpha m, halpha (2 * m)]
      have hmle : (m : ℝ) ^ 2 ≤ ((2 * m : ℕ) : ℝ) ^ 2 := by
        push_cast
        nlinarith [show (0 : ℝ) ≤ (m : ℝ) by positivity]
      nlinarith [hXnn]
    have hl := Real.log_le_log
      (by nlinarith [mul_nonneg hXnn (sq_nonneg (alpha t m))]) hkey
    rw [hlogfrob (2 * m) hm2, hlogfrob m hm, hL]
    linarith

end Work.TMComp.LocCantor
