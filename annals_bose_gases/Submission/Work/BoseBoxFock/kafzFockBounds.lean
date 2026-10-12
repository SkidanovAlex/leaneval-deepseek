import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Submission.Work.BoseBoxFock.KzOpC
import Submission.Work.BoseBoxFock.creC_sum_norm_sq
import Submission.Work.BoseBoxFock.inner_annC_creC
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `kafzFockBounds` — the Fock-space bounds for the `KzOpC` rows

The spectator number-type operators of `KzOpC` satisfy the bounds FS use to turn
the anti-Wick corrections of `eq:subst-z` into `‖v‖²`-errors:

* `nPlusC = ∑_l a_l† a_l` (the excited number operator) is positive semi-definite
  and self-adjoint;
* the superposed annihilator and creator satisfy the Bessel-type bounds
  `‖a(φ) w‖² ≤ (∑_l φ_l²) ⟪w, n₊ w⟫` and
  `‖a(φ)† w‖² ≤ (∑_l φ_l²) (⟪w, n₊ w⟫ + ‖w‖²)`;
* the superposed number operator `nOpC φ = a(φ)†a(φ)` obeys the same Bessel bound.

All five are elementary consequences of the adjointness of the ladder operators
(`Work.BoseB4.inner_annC_creC`), the canonical commutation relations
(`Work.BoseB4.annC_creC_ccr`), Cauchy–Schwarz for a finite sum, and the exact
identity `‖a(φ)†w‖² = ‖a(φ)w‖² + (∑_l φ_l²)‖w‖²`
(`Work.BoseBoxFock.creC_sum_norm_sq`).  Note that the second bound has the *sharp*
correction `(∑_l φ_l²)‖w‖²` — the naive Bessel inequality would only give
`(∑_l φ_l²)(⟪w, n₊w⟫ + |Excited m| ‖w‖²)`.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseBoxFock

open Work.BoseB4

set_option linter.unusedVariables false

variable {m : ℕ} [NeZero m]

/-! ## Inner-product toolbox for `cfock`

The `Submodule` instance diamonds of `lp` make the generic Mathlib sesquilinearity
lemmas (`inner_smul_left`, …) fail to `rw`-match on `cfock`; these local restatements
(elaborated in the same environment as the goals below) rewrite reliably. -/

section Toolbox
variable {X : Type*} [DecidableEq X]

lemma kfb_inner_smulL (c : ℂ) (u v : cfock X) :
    inner ℂ (c • u) v = (starRingEnd ℂ) c * inner ℂ u v := inner_smul_left u v c

lemma kfb_inner_smulR (c : ℂ) (u v : cfock X) :
    inner ℂ u (c • v) = c * inner ℂ u v := inner_smul_right u v c

lemma kfb_inner_addL (u v w : cfock X) :
    inner ℂ (u + v) w = inner ℂ u w + inner ℂ v w := inner_add_left u v w

lemma kfb_inner_addR (u v w : cfock X) :
    inner ℂ u (v + w) = inner ℂ u v + inner ℂ u w := inner_add_right u v w

lemma kfb_inner_sumL {ι : Type*} (s : Finset ι) (f : ι → cfock X) (x : cfock X) :
    inner ℂ (∑ i ∈ s, f i) x = ∑ i ∈ s, inner ℂ (f i) x := sum_inner s f x

lemma kfb_inner_sumR {ι : Type*} (s : Finset ι) (x : cfock X) (f : ι → cfock X) :
    inner ℂ x (∑ i ∈ s, f i) = ∑ i ∈ s, inner ℂ x (f i) := inner_sum s f x

lemma kfb_inner_self_re (w : cfock X) : inner ℂ w w = ((‖w‖ ^ 2 : ℝ) : ℂ) :=
  (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) w).trans (Complex.ofReal_pow ‖w‖ 2).symm

lemma kfb_ofReal_sum_re {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ((∑ i ∈ s, ((f i : ℝ) : ℂ))).re = ∑ i ∈ s, f i := by
  rw [← Complex.ofReal_sum]
  simp

lemma kfb_norm_ofReal (c : ℝ) : ‖((c : ℝ) : ℂ)‖ = |c| := RCLike.norm_ofReal c

lemma kfb_norm_smul (c : ℂ) (w : cfock X) : ‖c • w‖ = ‖c‖ * ‖w‖ := norm_smul c w

end Toolbox

/-! ## Adjointness bookkeeping -/

/-- The creator is the left adjoint of the annihilator. -/
lemma kfb_inner_creC_annC {X : Type*} [DecidableEq X] (i : X) (u v : cfock X) :
    inner ℂ (creC X i u) v = inner ℂ u (annC X i v) :=
  (inner_conj_symm (creC X i u) v).symm.trans
    (((congrArg (starRingEnd ℂ)) (inner_annC_creC i v u)).symm.trans
      (inner_conj_symm u (annC X i v)))

lemma kfb_annOfE_apply (φ : Fin m → ℝ) (w : cfock (Excited m)) :
    annOfE φ w = ∑ l : Excited m, ((φ l.1 : ℝ) : ℂ) • annC (Excited m) l w := by
  simp only [annOfE, LinearMap.sum_apply, LinearMap.smul_apply]

lemma kfb_creOfE_apply (φ : Fin m → ℝ) (w : cfock (Excited m)) :
    creOfE φ w = ∑ l : Excited m, ((φ l.1 : ℝ) : ℂ) • creC (Excited m) l w := by
  simp only [creOfE, LinearMap.sum_apply, LinearMap.smul_apply]

lemma kfb_nPlusC_apply (w : cfock (Excited m)) :
    nPlusC w = ∑ l : Excited m, creC (Excited m) l (annC (Excited m) l w) := by
  simp only [nPlusC, LinearMap.sum_apply, LinearMap.comp_apply, one_smul]

lemma kfb_nOpC_apply (φ : Fin m → ℝ) (w : cfock (Excited m)) :
    nOpC φ w = creOfE φ (annOfE φ w) := by
  simp only [nOpC, LinearMap.comp_apply]

/-- Adjointness of the superposed annihilator: `annOfE φ` and `creOfE φ` are adjoint. -/
lemma kfb_inner_annOfE_creOfE (φ : Fin m → ℝ) (u v : cfock (Excited m)) :
    inner ℂ (annOfE φ u) v = inner ℂ u (creOfE φ v) := by
  rw [kfb_annOfE_apply, kfb_creOfE_apply, kfb_inner_sumL, kfb_inner_sumR]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [kfb_inner_smulL, kfb_inner_smulR, inner_annC_creC, Complex.conj_ofReal]

/-! ## The number operator `nPlusC` -/

lemma kfb_inner_nPlusC_self (w : cfock (Excited m)) :
    inner ℂ w (nPlusC w)
      = ∑ l : Excited m, ((‖annC (Excited m) l w‖ ^ 2 : ℝ) : ℂ) := by
  rw [kfb_nPlusC_apply, kfb_inner_sumR]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← inner_annC_creC l w (annC (Excited m) l w), kfb_inner_self_re]

lemma kfb_re_inner_nPlusC_self (w : cfock (Excited m)) :
    (inner ℂ w (nPlusC w)).re = ∑ l : Excited m, ‖annC (Excited m) l w‖ ^ 2 := by
  rw [kfb_inner_nPlusC_self]
  exact kfb_ofReal_sum_re Finset.univ _

lemma kfb_nPlusC_re_nonneg (w : cfock (Excited m)) : 0 ≤ (inner ℂ w (nPlusC w)).re := by
  rw [kfb_re_inner_nPlusC_self]
  exact Finset.sum_nonneg fun l _ => sq_nonneg _

lemma kfb_inner_nPlusC_symm (u v : cfock (Excited m)) :
    inner ℂ (nPlusC u) v = inner ℂ u (nPlusC v) := by
  rw [kfb_nPlusC_apply, kfb_nPlusC_apply, kfb_inner_sumL, kfb_inner_sumR]
  exact Finset.sum_congr rfl fun l _ => by
    rw [kfb_inner_creC_annC, inner_annC_creC]

/-! ## The annihilation bound -/

lemma kfb_annOfE_norm_le (φ : Fin m → ℝ) (w : cfock (Excited m)) :
    ‖annOfE φ w‖ ≤ ∑ l : Excited m, |φ l.1| * ‖annC (Excited m) l w‖ := by
  rw [kfb_annOfE_apply]
  refine (norm_sum_le _ _).trans_eq ?_
  refine Finset.sum_congr rfl fun l _ => ?_
  exact (kfb_norm_smul _ _).trans (by rw [kfb_norm_ofReal])

lemma kfb_annOfE_norm_sq_le (φ : Fin m → ℝ) (w : cfock (Excited m)) :
    ‖annOfE φ w‖ ^ 2
      ≤ (∑ l : Excited m, φ l.1 ^ 2) * (inner ℂ w (nPlusC w)).re := by
  have h1 := kfb_annOfE_norm_le φ w
  have h2 : (∑ l : Excited m, |φ l.1| * ‖annC (Excited m) l w‖) ^ 2
      ≤ (∑ l : Excited m, |φ l.1| ^ 2)
        * (∑ l : Excited m, ‖annC (Excited m) l w‖ ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _
  have h3 : ‖annOfE φ w‖ ^ 2
      ≤ (∑ l : Excited m, |φ l.1| * ‖annC (Excited m) l w‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h4 : (∑ l : Excited m, |φ l.1| ^ 2) = ∑ l : Excited m, φ l.1 ^ 2 :=
    Finset.sum_congr rfl fun l _ => by rw [sq_abs]
  rw [kfb_re_inner_nPlusC_self]
  calc ‖annOfE φ w‖ ^ 2
      ≤ (∑ l : Excited m, |φ l.1| * ‖annC (Excited m) l w‖) ^ 2 := h3
    _ ≤ (∑ l : Excited m, |φ l.1| ^ 2)
          * (∑ l : Excited m, ‖annC (Excited m) l w‖ ^ 2) := h2
    _ = (∑ l : Excited m, φ l.1 ^ 2)
          * (∑ l : Excited m, ‖annC (Excited m) l w‖ ^ 2) := by rw [h4]

/-! ## The creation bound -/

/-- The exact identity `‖a(φ)†w‖² = ‖a(φ)w‖² + (∑_l φ_l²)‖w‖²`. -/
lemma kfb_creOfE_norm_sq (φ : Fin m → ℝ) (w : cfock (Excited m)) :
    ‖creOfE φ w‖ ^ 2
      = ‖annOfE φ w‖ ^ 2 + (∑ l : Excited m, φ l.1 ^ 2) * ‖w‖ ^ 2 := by
  have h := creC_sum_norm_sq (fun l : Excited m => annC (Excited m) l)
      (fun l : Excited m => creC (Excited m) l) (fun l : Excited m => φ l.1) w
      (fun i u v => inner_annC_creC i u v) (fun i j => annC_creC_ccr i j)
  rw [kfb_creOfE_apply φ w, kfb_annOfE_apply φ w]
  exact h

lemma kfb_creOfE_norm_sq_le (φ : Fin m → ℝ) (w : cfock (Excited m)) :
    ‖creOfE φ w‖ ^ 2
      ≤ (∑ l : Excited m, φ l.1 ^ 2)
          * ((inner ℂ w (nPlusC w)).re + ‖w‖ ^ 2) := by
  have h3 := kfb_annOfE_norm_sq_le φ w
  rw [kfb_creOfE_norm_sq]
  have expand : (∑ l : Excited m, φ l.1 ^ 2)
        * ((inner ℂ w (nPlusC w)).re + ‖w‖ ^ 2)
      = (∑ l : Excited m, φ l.1 ^ 2) * (inner ℂ w (nPlusC w)).re
        + (∑ l : Excited m, φ l.1 ^ 2) * ‖w‖ ^ 2 := by ring
  rw [expand]
  linarith [h3]

/-! ## The `nOpC` bound -/

lemma kfb_nOpC_re_le (φ : Fin m → ℝ) (w : cfock (Excited m)) :
    (inner ℂ w (nOpC φ w)).re
      ≤ (∑ l : Excited m, φ l.1 ^ 2) * (inner ℂ w (nPlusC w)).re := by
  have h : inner ℂ w (nOpC φ w) = ((‖annOfE φ w‖ ^ 2 : ℝ) : ℂ) := by
    rw [kfb_nOpC_apply, ← kfb_inner_annOfE_creOfE φ w (annOfE φ w), kfb_inner_self_re]
  rw [h, Complex.ofReal_re]
  exact kfb_annOfE_norm_sq_le φ w

/-! ## The bounds -/

theorem kafzFockBounds {m : ℕ} [NeZero m] :
    (∀ w : Work.BoseB4.cfock (Work.BoseB4.Excited m),
        0 ≤ (inner ℂ w (Work.BoseBoxFock.nPlusC (m := m) w)).re)
    ∧ (∀ u v : Work.BoseB4.cfock (Work.BoseB4.Excited m),
        inner ℂ (Work.BoseBoxFock.nPlusC (m := m) u) v
          = inner ℂ u (Work.BoseBoxFock.nPlusC (m := m) v))
    ∧ (∀ (φ : Fin m → ℝ) (w : Work.BoseB4.cfock (Work.BoseB4.Excited m)),
        ‖Work.BoseBoxFock.annOfE φ w‖ ^ 2
          ≤ (∑ l : Work.BoseB4.Excited m, φ l.1 ^ 2)
            * (inner ℂ w (Work.BoseBoxFock.nPlusC (m := m) w)).re)
    ∧ (∀ (φ : Fin m → ℝ) (w : Work.BoseB4.cfock (Work.BoseB4.Excited m)),
        ‖Work.BoseBoxFock.creOfE φ w‖ ^ 2
          ≤ (∑ l : Work.BoseB4.Excited m, φ l.1 ^ 2)
            * ((inner ℂ w (Work.BoseBoxFock.nPlusC (m := m) w)).re + ‖w‖ ^ 2))
    ∧ (∀ (φ : Fin m → ℝ) (w : Work.BoseB4.cfock (Work.BoseB4.Excited m)),
        (inner ℂ w (Work.BoseBoxFock.nOpC (m := m) φ w)).re
          ≤ (∑ l : Work.BoseB4.Excited m, φ l.1 ^ 2)
            * (inner ℂ w (Work.BoseBoxFock.nPlusC (m := m) w)).re) := by
  exact ⟨fun w => kfb_nPlusC_re_nonneg w, fun u v => kfb_inner_nPlusC_symm u v,
    fun φ w => kfb_annOfE_norm_sq_le φ w, fun φ w => kfb_creOfE_norm_sq_le φ w,
    fun φ w => kfb_nOpC_re_le φ w⟩

end Work.BoseBoxFock
