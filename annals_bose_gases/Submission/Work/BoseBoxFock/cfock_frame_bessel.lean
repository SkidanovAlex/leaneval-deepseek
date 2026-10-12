import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Submission.Work.BoseBoxFock.Frame.frame_diff_form
import Submission.Work.BoseBoxFock.Frame.frame_quadForm_nonneg
import Submission.Work.BoseBoxFock.Frame.psd_form_re_nonneg
import Submission.Work.BoseBoxFock.bessel_honest
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.cfock_frame_bessel` — the Bessel (frame) bound for the spectator
number operators `nOpC`

For a family `f : Mode → Fin m → ℝ` of one-particle coordinate vectors whose **frame
operator** is dominated by `C · 1` in the quadratic-form sense,

    `Σ_k ⟪f k, w⟫² ≤ C ‖w‖²`   for every `w : Fin m → ℝ`   (`⟪f k, w⟫ = gram (f k) w`),

the sum of the spectator number operators `Σ_k nOpC (f k) = Σ_k a(f k)† a(f k)` is
dominated by `C · n₊` in the sense of quadratic forms on the spectator Fock space
`cfock (Excited m)`:

    `(⟪x, (Σ_k nOpC (f k)) x⟫).re ≤ C · (⟪x, n₊ x⟫).re`.

This generalises `Work.BoseBoxFock.sum_annOfE_normSq_le_nPlusC` (the orthonormal case
`C = 1`) from a frame that is an *orthonormal family* to an arbitrary Bessel sequence;
unlike the orthonormal case (`Work.BoseB4.bessel_gram_factor`), the complementary matrix
`C·1 − S` is not a projection here, so it is factored as a product `B Bᵀ` of real
matrices via the C*-algebraic characterisation of positive semidefinite matrices.

## The argument

Write `u_l := annC l x` for the excited coordinate annihilations of the state `x`, so
`annOfE φ x = Σ_l φ_l u_l` and, using `creOfE = (annOfE)†`,
`(⟪x, nOpC φ x⟫).re = ‖annOfE φ x‖²`.

Let `A l l' := C δ_{ll'} − Σ_k f k l · f k l'` on the *excited* indices `l : Excited m`;
`hS` (restricted by extending `v : Excited m → ℝ` by `0` at the condensate coordinate)
says that `A` is positive semidefinite as a real quadratic form, and Bessel's inequality
is the two evaluations of the Hermitian form of `A` at `u`:

* `0 ≤ Σ_{l,l'} A l l' (⟪u_l, u_{l'}⟫).re` — the positivity of the form of a PSD
  matrix on the Gram matrix of a family of vectors in a complex Hilbert space
  (`Work.BoseBoxFock.Frame.psd_form_re_nonneg`);
* `Σ_{l,l'} A l l' (⟪u_l, u_{l'}⟫).re = C Σ_l ‖u_l‖² − Σ_k ‖annOfE (f k) x‖²` — the
  expansion of the difference of the two sides
  (`Work.BoseBoxFock.Frame.frame_diff_form`);

together with `(⟪x, n₊ x⟫).re = Σ_l ‖u_l‖²` (`Work.BoseBoxFock.kfb_re_inner_nPlusC_self`).
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseBoxFock

open Work.BoseB4

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

variable {m : ℕ} [NeZero m]

/-! ## The quadratic forms of `nOpC` and of the sum `Σ_k nOpC (f k)` -/

/-- `nOpC φ = a(φ)† a(φ)`, so its quadratic form is the squared norm of the annihilation:
`⟪w, nOpC φ w⟫ = ‖a(φ) w‖²` (as a complex number). -/
lemma cfb_inner_nOpC (φ : Fin m → ℝ) (w : cfock (Excited m)) :
    inner ℂ w (nOpC φ w) = ((‖annOfE φ w‖ ^ 2 : ℝ) : ℂ) := by
  rw [kfb_nOpC_apply, ← kfb_inner_annOfE_creOfE φ w (annOfE φ w), kfb_inner_self_re]

/-- **The quadratic form of `Σ_k nOpC (f k)` is the sum of the squared norms.**  No
assumption on the modes `f k` (no orthonormality, no frame bound) is needed: this is an
identity. -/
lemma cfb_sum_nOpC_re {Mode : Type*} [Fintype Mode] (φ : Mode → Fin m → ℝ)
    (w : cfock (Excited m)) :
    (inner ℂ w ((∑ k : Mode, nOpC (m := m) (φ k)) w)).re
      = ∑ k : Mode, ‖annOfE (φ k) w‖ ^ 2 := by
  have h : inner ℂ w ((∑ k : Mode, nOpC (m := m) (φ k)) w)
      = ((∑ k : Mode, ‖annOfE (φ k) w‖ ^ 2 : ℝ) : ℂ) := by
    rw [LinearMap.sum_apply, inner_sum, Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun k _ => cfb_inner_nOpC (φ k) w
  rw [h, Complex.ofReal_re]

/-! ## The Bessel bound -/

theorem cfock_frame_bessel {Mode : Type*} [Fintype Mode] [DecidableEq Mode] {m : ℕ} [NeZero m]
    (f : Mode → Fin m → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hS : ∀ w : Fin m → ℝ,
      ∑ k : Mode, (Work.BoseB4.gram (f k) w) ^ 2 ≤ C * ∑ l : Fin m, (w l) ^ 2)
    (x : Work.BoseB4.cfock (Work.BoseB4.Excited m)) :
    (inner ℂ x
        ((∑ k : Mode, Work.BoseBoxFock.nOpC (m := m) (f k)) x)).re
      ≤ C * (inner ℂ x (Work.BoseBoxFock.nPlusC (m := m) x)).re := by
  classical
  -- the compressed frame matrix `A = C·1 − Σ_k |f k⟩⟨f k|` on the excited modes
  set A : Excited m → Excited m → ℝ :=
    fun l l' => C * (if l = l' then (1 : ℝ) else 0) - ∑ k : Mode, f k l.1 * f k l'.1 with hA
  have hsym : ∀ l l', A l l' = A l' l := by
    intro l l'
    simp only [hA]
    have h1 : (if l = l' then (1 : ℝ) else 0) = (if l' = l then (1 : ℝ) else 0) := by
      by_cases h : l = l'
      · rw [if_pos h, if_pos h.symm]
      · rw [if_neg h, if_neg (Ne.symm h)]
    have h2 : (∑ k : Mode, f k l.1 * f k l'.1) = ∑ k : Mode, f k l'.1 * f k l.1 :=
      Finset.sum_congr rfl fun k _ => mul_comm _ _
    rw [h1, h2]
  -- `A` is positive semidefinite, by the frame hypothesis restricted to the excited modes
  have hquad : ∀ v : Excited m → ℝ, 0 ≤ ∑ l, ∑ l', v l * A l l' * v l' := by
    intro v
    simp only [hA]
    exact Work.BoseBoxFock.Frame.frame_quadForm_nonneg f C hS v
  -- the two evaluations of the Hermitian form of `A` at `u l = annC l x`
  have hnn : 0 ≤ ∑ l : Excited m, ∑ l' : Excited m,
      A l l' * (inner ℂ (annC (Excited m) l x) (annC (Excited m) l' x)).re :=
    Work.BoseBoxFock.Frame.psd_form_re_nonneg (A := A) hsym hquad
      (fun l : Excited m => annC (Excited m) l x)
  have hid : (∑ l : Excited m, ∑ l' : Excited m,
        A l l' * (inner ℂ (annC (Excited m) l x) (annC (Excited m) l' x)).re)
      = C * ∑ l : Excited m, ‖annC (Excited m) l x‖ ^ 2
        - ∑ k : Mode, ‖∑ l : Excited m, (((f k l.1 : ℝ)) : ℂ) • annC (Excited m) l x‖ ^ 2 := by
    simp only [hA]
    exact Work.BoseBoxFock.Frame.frame_diff_form
      (f := fun k (l : Excited m) => f k l.1) (C := C)
      (u := fun l : Excited m => annC (Excited m) l x)
  rw [hid] at hnn
  -- identify the explicit sums of norms with the two quadratic forms of the statement
  have hnorm : ∀ k : Mode,
      ‖annOfE (f k) x‖
        = ‖∑ l : Excited m, (((f k l.1 : ℝ)) : ℂ) • annC (Excited m) l x‖ := by
    intro k
    rw [kfb_annOfE_apply]
  have hsum : (∑ k : Mode, ‖annOfE (f k) x‖ ^ 2)
      = ∑ k : Mode, ‖∑ l : Excited m, (((f k l.1 : ℝ)) : ℂ) • annC (Excited m) l x‖ ^ 2 :=
    Finset.sum_congr rfl fun k _ => by rw [hnorm k]
  rw [cfb_sum_nOpC_re f x, kfb_re_inner_nPlusC_self, hsum]
  linarith

end Work.BoseBoxFock
