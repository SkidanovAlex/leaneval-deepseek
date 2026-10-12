import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Submission.Work.BoseBoxFock.KafzSym
import Submission.Work.BoseBoxFock.kafzFockBounds
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.chiRow_bound` — the `r¹` (`χ̂`) row of the symbol discrepancy

The `r¹`-row of `D1F` (`KafzSym`) is

    `−(2 ℓ⁻³ Ŵ₁(0)) • (BchiC univ hatChi 1 f + BchiA univ hatChi 1 f)`,

whose quadratic form at `w` is controlled by the Bessel/Cauchy–Schwarz estimate

    `|⟪w, Σ_k ĉ_k (a(f_k) + a(f_k)†) w⟫| ≤ 2 √(Σ_k ĉ_k²) √(⟪w, n₊^χ w⟫) ‖w‖`.

This file proves exactly that estimate (`chiRow_bound`), with `⟪w, n₊^χ w⟫ = Σ_k ‖a(f_k) w‖²`
(an *identity*, no orthonormality of the `f k` needed).

## Proof

Write `A = Σ_k ĉ_k a(f_k)` and `C = Σ_k ĉ_k a(f_k)†` (both `ℂ`-linear maps on
`cfock (Excited m)`), so that the row word is `T = A + C`.  Since `C` is the adjoint of `A`
(the weights `ĉ_k` are real), `⟪w, C w⟫ = ⟪A w, w⟫ = conj ⟪w, A w⟫`, hence

    `(⟪w, T w⟫).re = 2 (⟪w, A w⟫).re`.

Then Cauchy–Schwarz twice gives

    `|(⟪w, A w⟫).re| ≤ ‖⟪w, A w⟫‖ ≤ ‖w‖ ‖A w‖`,

and, with `b_k := ‖a(f_k) w‖`,

    `‖A w‖ ≤ Σ_k |ĉ_k| b_k ≤ √(Σ_k ĉ_k²) √(Σ_k b_k²)`
      `≤ √(Σ_k ĉ_k²) √(⟪w, n₊^χ w⟫)`.

The final ingredient `Σ_k ‖a(f_k) w‖² = (⟪w, n₊^χ w⟫).re` is `chiRow_nPlusChi_re`, a direct
consequence of `nOpC φ = a(φ)† a(φ)` being positive (`chiRow_inner_nOpC`).
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseBoxFock

open Work.BoseB4

set_option autoImplicit false
set_option linter.unusedVariables false

variable {m : ℕ} [NeZero m]

/-! ## 1. The quadratic form of `nOpC` is the squared norm of the annihilation -/

/-- `nOpC φ = a(φ)† a(φ)`, so `⟪w, nOpC φ w⟫ = ‖a(φ) w‖²` (as a complex number). -/
lemma chiRow_inner_nOpC (φ : Fin m → ℝ) (w : cfock (Excited m)) :
    inner ℂ w (nOpC φ w) = ((‖annOfE φ w‖ ^ 2 : ℝ) : ℂ) := by
  rw [kfb_nOpC_apply, ← kfb_inner_annOfE_creOfE φ w (annOfE φ w), kfb_inner_self_re]

/-- The real part of the quadratic form of `nOpC`. -/
lemma chiRow_nOpC_re (φ : Fin m → ℝ) (w : cfock (Excited m)) :
    (inner ℂ w (nOpC φ w)).re = ‖annOfE φ w‖ ^ 2 := by
  rw [chiRow_inner_nOpC, Complex.ofReal_re]

/-- **The quadratic form of `nPlusChi` is the sum of the squared norms.**  No orthonormality
of the modes `φ k` is needed: this is an identity. -/
lemma chiRow_nPlusChi_re {X : Type*} [AddCommGroup X] [Fintype X]
    (φ : X → Fin m → ℝ) (w : cfock (Excited m)) :
    (inner ℂ w (nPlusChi (m := m) φ w)).re = ∑ k : X, ‖annOfE (φ k) w‖ ^ 2 := by
  have h : inner ℂ w (nPlusChi (m := m) φ w)
      = ((∑ k : X, ‖annOfE (φ k) w‖ ^ 2 : ℝ) : ℂ) := by
    simp only [nPlusChi, LinearMap.sum_apply]
    rw [inner_sum, Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun k _ => chiRow_inner_nOpC (φ k) w
  rw [h, Complex.ofReal_re]

/-! ## 2. Adjointness of the weighted annihilation/creation sums, and the split `T = A + C` -/

/-- The weighted sums `A = Σ_k c_k a(φ_k)` and `C = Σ_k c_k a(φ_k)†` are adjoint: the
coefficients `c k` are real, so complex conjugation leaves them alone. -/
lemma chiRow_inner_ann_cre {X : Type*} [Fintype X] (c : X → ℝ) (φ : X → Fin m → ℝ)
    (u v : cfock (Excited m)) :
    inner ℂ ((∑ k : X, ((c k : ℝ) : ℂ) • annOfE (φ k)) u) v
      = inner ℂ u ((∑ k : X, ((c k : ℝ) : ℂ) • creOfE (φ k)) v) := by
  rw [LinearMap.sum_apply, LinearMap.sum_apply]
  simp only [LinearMap.smul_apply]
  rw [kfb_inner_sumL, kfb_inner_sumR]
  exact Finset.sum_congr rfl fun k _ => by
    rw [kfb_inner_smulL, kfb_inner_smulR, kfb_inner_annOfE_creOfE, Complex.conj_ofReal]

/-- Distributing the summand: `Σ_k c_k (a_k + a_k†) = Σ_k c_k a_k + Σ_k c_k a_k†`. -/
lemma chiRow_T_split {X : Type*} [Fintype X] (c : X → ℝ) (φ : X → Fin m → ℝ) :
    (∑ k : X, ((c k : ℝ) : ℂ) • (annOfE (φ k) + creOfE (φ k)))
      = (∑ k : X, ((c k : ℝ) : ℂ) • annOfE (φ k))
        + ∑ k : X, ((c k : ℝ) : ℂ) • creOfE (φ k) := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by rw [smul_add]

/-- **The row word has twice the real part of its annihilation half**: the creation half
contributes the conjugate, hence the same real part. -/
lemma chiRow_re_T {X : Type*} [Fintype X] (c : X → ℝ) (φ : X → Fin m → ℝ)
    (w : cfock (Excited m)) :
    (inner ℂ w ((∑ k : X, ((c k : ℝ) : ℂ) •
          (annOfE (φ k) + creOfE (φ k))) w)).re
      = 2 * (inner ℂ w ((∑ k : X, ((c k : ℝ) : ℂ) • annOfE (φ k)) w)).re := by
  have h : inner ℂ w ((∑ k : X, ((c k : ℝ) : ℂ) • creOfE (φ k)) w)
      = inner ℂ ((∑ k : X, ((c k : ℝ) : ℂ) • annOfE (φ k)) w) w :=
    (chiRow_inner_ann_cre c φ w w).symm
  have hconj : inner ℂ ((∑ k : X, ((c k : ℝ) : ℂ) • annOfE (φ k)) w) w
      = (starRingEnd ℂ) (inner ℂ w ((∑ k : X, ((c k : ℝ) : ℂ) • annOfE (φ k)) w)) :=
    (inner_conj_symm (x := (∑ k : X, ((c k : ℝ) : ℂ) • annOfE (φ k)) w) (y := w)).symm
  rw [chiRow_T_split c φ, LinearMap.add_apply, inner_add_right, h, hconj]
  simp only [Complex.add_re, Complex.conj_re]
  ring

/-! ## 3. The Cauchy–Schwarz bound on the annihilation half -/

/-- `‖Σ_k c_k a(φ_k) w‖ ≤ √(Σ_k c_k²) √(Σ_k ‖a(φ_k) w‖²)` — Cauchy–Schwarz for the
weighted sum of the vectors `a(φ_k) w`. -/
lemma chiRow_ann_norm_le {X : Type*} [Fintype X] (c : X → ℝ) (φ : X → Fin m → ℝ)
    (w : cfock (Excited m)) :
    ‖(∑ k : X, ((c k : ℝ) : ℂ) • annOfE (φ k)) w‖
      ≤ Real.sqrt (∑ k : X, c k ^ 2)
        * Real.sqrt (∑ k : X, ‖annOfE (φ k) w‖ ^ 2) := by
  have h1 : ‖(∑ k : X, ((c k : ℝ) : ℂ) • annOfE (φ k)) w‖
      ≤ ∑ k : X, |c k| * ‖annOfE (φ k) w‖ := by
    rw [LinearMap.sum_apply]
    simp only [LinearMap.smul_apply]
    refine (norm_sum_le Finset.univ _).trans ?_
    exact Finset.sum_le_sum fun k _ => by
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right
        (le_of_eq (RCLike.norm_ofReal (K := ℂ) (c k))) (norm_nonneg _)
  have h2 : (∑ k : X, |c k| * ‖annOfE (φ k) w‖) ^ 2
      ≤ (∑ k : X, |c k| ^ 2) * ∑ k : X, ‖annOfE (φ k) w‖ ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _
  have h3 : (∑ k : X, |c k| ^ 2) = ∑ k : X, c k ^ 2 :=
    Finset.sum_congr rfl fun k _ => sq_abs (c k)
  have h4 : ‖(∑ k : X, ((c k : ℝ) : ℂ) • annOfE (φ k)) w‖ ^ 2
      ≤ (∑ k : X, c k ^ 2) * ∑ k : X, ‖annOfE (φ k) w‖ ^ 2 := by
    rw [h3] at h2
    exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2
  have h5 : 0 ≤ ∑ k : X, c k ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
  have h6 : 0 ≤ ∑ k : X, ‖annOfE (φ k) w‖ ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
  calc ‖(∑ k : X, ((c k : ℝ) : ℂ) • annOfE (φ k)) w‖
      ≤ Real.sqrt ((∑ k : X, c k ^ 2) * ∑ k : X, ‖annOfE (φ k) w‖ ^ 2) :=
        (Real.le_sqrt (norm_nonneg _) (mul_nonneg h5 h6)).mpr h4
    _ = Real.sqrt (∑ k : X, c k ^ 2) * Real.sqrt (∑ k : X, ‖annOfE (φ k) w‖ ^ 2) :=
        Real.sqrt_mul h5 _

/-! ## 4. The row bound -/

theorem chiRow_bound {m : ℕ} [NeZero m] {X : Type*} [AddCommGroup X] [Fintype X]
    [DecidableEq X]
    (c : X → ℝ) (φ : X → Fin m → ℝ) (w : Work.BoseB4.cfock (Work.BoseB4.Excited m)) :
    |(inner ℂ w ((∑ k : X, ((c k : ℝ) : ℂ) •
          (Work.BoseBoxFock.annOfE (φ k) + Work.BoseBoxFock.creOfE (φ k))) w)).re|
      ≤ 2 * Real.sqrt (∑ k : X, c k ^ 2)
          * Real.sqrt ((inner ℂ w (Work.BoseBoxFock.nPlusChi (m := m) φ w)).re) * ‖w‖ := by
  rw [chiRow_re_T c φ w, chiRow_nPlusChi_re φ w]
  have hA := chiRow_ann_norm_le c φ w
  have hq : |(inner ℂ w ((∑ k : X, ((c k : ℝ) : ℂ) • annOfE (φ k)) w)).re|
      ≤ ‖w‖ * (Real.sqrt (∑ k : X, c k ^ 2)
          * Real.sqrt (∑ k : X, ‖annOfE (φ k) w‖ ^ 2)) := by
    refine (Complex.abs_re_le_norm _).trans ?_
    refine (norm_inner_le_norm w ((∑ k : X, ((c k : ℝ) : ℂ) • annOfE (φ k)) w)).trans ?_
    exact mul_le_mul_of_nonneg_left hA (norm_nonneg w)
  calc |2 * (inner ℂ w ((∑ k : X, ((c k : ℝ) : ℂ) • annOfE (φ k)) w)).re|
      = 2 * |(inner ℂ w ((∑ k : X, ((c k : ℝ) : ℂ) • annOfE (φ k)) w)).re| := by
        rw [abs_mul]
        norm_num
    _ ≤ 2 * (‖w‖ * (Real.sqrt (∑ k : X, c k ^ 2)
          * Real.sqrt (∑ k : X, ‖annOfE (φ k) w‖ ^ 2))) :=
        mul_le_mul_of_nonneg_left hq (by norm_num)
    _ = 2 * Real.sqrt (∑ k : X, c k ^ 2)
          * Real.sqrt (∑ k : X, ‖annOfE (φ k) w‖ ^ 2) * ‖w‖ := by ring

end Work.BoseBoxFock
