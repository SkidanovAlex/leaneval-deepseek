import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseK15.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseK15.tauFun_lipschitz`

FS `def:tau`'s kinetic symbol

`τ(k) = (1 − ε_T) [‖k‖ − (2sℓ)⁻¹]₊² + ε_T [‖k‖ − (2dsℓ)⁻¹]₊²`

is **locally Lipschitz with a linear growth factor**: writing

`a := (2sℓ)⁻¹`, `b := (2dsℓ)⁻¹`, `M := max |a| |b|`,

one has

`|τ(p) − τ(q)| ≤ 4 (1 + M) (1 + |ε_T|) (1 + ‖p‖ + ‖q‖) ‖p − q‖`.

The proof is the one-variable fact that `t ↦ (max (t − a) 0)²` is Lipschitz on
`[0,∞)` with the *growth-dependent* constant `2 (1 + M) (1 + t + u)`: for
`t, u ≥ 0`,

`|(t−a)₊² − (u−a)₊²| = |(t−a)₊ − (u−a)₊| · ((t−a)₊ + (u−a)₊)
                       ≤ |t − u| (|t − a| + |u − a|)
                       ≤ |t − u| (t + u + 2M)`,

using `|x₊ − y₊| ≤ |x − y|` (`abs_max_sub_max_le_abs`), and `|‖p‖ − ‖q‖| ≤
‖p − q‖` (`abs_norm_sub_norm_le`) for the passage to vectors.

**The constant must depend on `s, d, ℓ`** — and it may, since the statement's
`∃ C` is innermost, after all four scalars.  No bound with a constant uniform in
`ℓ` holds: for `ε_T = 0` and `a = (2sℓ)⁻¹ → ∞` (i.e. `ℓ → 0⁺`) one has
`τ(0) = a²` while `τ(q) = 0` for `‖q‖ = 1`, and `a²` is not `≤ C · 2`.  So the
`ℓ`-dependence of `C` here is not an artefact of the formalisation.
-/

noncomputable section

-- `hs`, `hd` are part of the requested statement but are not needed for the
-- bound (it only uses `|a| ≤ M`); silence the unused-variable linter for them.
set_option linter.unusedVariables false

open scoped BigOperators

namespace Work.BoseK15

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- **The one-variable core.**  On `[0,∞)`, `t ↦ (max (t − a) 0)²` is Lipschitz
with the growth-dependent constant `|t − a| + |u − a| ≤ t + u + 2|a|`. -/
lemma sq_max_sub_zero_le (a t u : ℝ) :
    |(max (t - a) 0) ^ 2 - (max (u - a) 0) ^ 2| ≤ (|t - a| + |u - a|) * |t - u| := by
  have hfac : (max (t - a) 0) ^ 2 - (max (u - a) 0) ^ 2
      = (max (t - a) 0 - max (u - a) 0) * (max (t - a) 0 + max (u - a) 0) := by ring
  rw [hfac, abs_mul,
    abs_of_nonneg (by linarith [le_max_right (t - a) (0:ℝ), le_max_right (u - a) (0:ℝ)] :
      (0:ℝ) ≤ max (t - a) 0 + max (u - a) 0)]
  have h1 : |max (t - a) 0 - max (u - a) 0| ≤ |t - u| := by
    simpa using abs_max_sub_max_le_abs (t - a) (u - a) (0:ℝ)
  have h2 : max (t - a) 0 + max (u - a) 0 ≤ |t - a| + |u - a| :=
    add_le_add (max_le (le_abs_self _) (abs_nonneg _)) (max_le (le_abs_self _) (abs_nonneg _))
  calc |max (t - a) 0 - max (u - a) 0| * (max (t - a) 0 + max (u - a) 0)
      ≤ |t - u| * (|t - a| + |u - a|) := mul_le_mul h1 h2 (by positivity) (abs_nonneg _)
    _ = (|t - a| + |u - a|) * |t - u| := by ring

/-- The same bound for one kinetic row, in the vector form used by `tauFun`:
if `|a| ≤ M` then the difference of `(max (‖·‖ − a) 0)²` at `p` and `q` is at most
`2 (1 + M) (1 + ‖p‖ + ‖q‖) ‖p − q‖`. -/
lemma tau_row_lip (a M : ℝ) (ha : |a| ≤ M) (p q : ℝ³) :
    |(max (‖p‖ - a) 0) ^ 2 - (max (‖q‖ - a) 0) ^ 2|
      ≤ 2 * (1 + M) * (1 + ‖p‖ + ‖q‖) * ‖p - q‖ := by
  have hM : 0 ≤ M := le_trans (abs_nonneg a) ha
  have hpa : |‖p‖ - a| ≤ ‖p‖ + M := by
    rw [abs_le]
    have h := abs_le.mp ha
    constructor <;> linarith [norm_nonneg p, h.1, h.2]
  have hqa : |‖q‖ - a| ≤ ‖q‖ + M := by
    rw [abs_le]
    have h := abs_le.mp ha
    constructor <;> linarith [norm_nonneg q, h.1, h.2]
  have h1 := sq_max_sub_zero_le a ‖p‖ ‖q‖
  have hn : |‖p‖ - ‖q‖| ≤ ‖p - q‖ := abs_norm_sub_norm_le p q
  have hsum : |‖p‖ - a| + |‖q‖ - a| ≤ 2 * (1 + M) * (1 + ‖p‖ + ‖q‖) := by
    nlinarith [hpa, hqa, hM, norm_nonneg p, norm_nonneg q,
      mul_nonneg hM (norm_nonneg p), mul_nonneg hM (norm_nonneg q)]
  calc |(max (‖p‖ - a) 0) ^ 2 - (max (‖q‖ - a) 0) ^ 2|
      ≤ (|‖p‖ - a| + |‖q‖ - a|) * |‖p‖ - ‖q‖| := h1
    _ ≤ (2 * (1 + M) * (1 + ‖p‖ + ‖q‖)) * ‖p - q‖ :=
        mul_le_mul hsum hn (abs_nonneg _)
          (mul_nonneg (mul_nonneg (by norm_num) (by linarith))
            (by nlinarith [norm_nonneg p, norm_nonneg q]))
    _ = 2 * (1 + M) * (1 + ‖p‖ + ‖q‖) * ‖p - q‖ := by ring

/-- **The two-row bound**: `τ` with the two offsets `A`, `B` both bounded by `M`. -/
lemma tauFun_lip_of (eT A B M : ℝ) (hA : |A| ≤ M) (hB : |B| ≤ M) (p q : ℝ³) :
    |(1 - eT) * (max (‖p‖ - A) 0) ^ 2 + eT * (max (‖p‖ - B) 0) ^ 2
      - ((1 - eT) * (max (‖q‖ - A) 0) ^ 2 + eT * (max (‖q‖ - B) 0) ^ 2)|
    ≤ 4 * (1 + M) * (1 + |eT|) * (1 + ‖p‖ + ‖q‖) * ‖p - q‖ := by
  have hM : 0 ≤ M := le_trans (abs_nonneg A) hA
  have hA' := tau_row_lip A M hA p q
  have hB' := tau_row_lip B M hB p q
  have key : (1 - eT) * (max (‖p‖ - A) 0) ^ 2 + eT * (max (‖p‖ - B) 0) ^ 2
      - ((1 - eT) * (max (‖q‖ - A) 0) ^ 2 + eT * (max (‖q‖ - B) 0) ^ 2)
      = (1 - eT) * ((max (‖p‖ - A) 0) ^ 2 - (max (‖q‖ - A) 0) ^ 2)
        + eT * ((max (‖p‖ - B) 0) ^ 2 - (max (‖q‖ - B) 0) ^ 2) := by ring
  rw [key]
  have hT0 : 0 ≤ 2 * (1 + M) * (1 + ‖p‖ + ‖q‖) * ‖p - q‖ :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by linarith))
      (by nlinarith [norm_nonneg p, norm_nonneg q])) (norm_nonneg _)
  have h1e : |1 - eT| ≤ 1 + |eT| := by
    rw [abs_le]
    constructor <;> linarith [le_abs_self eT, neg_abs_le eT]
  calc |(1 - eT) * ((max (‖p‖ - A) 0) ^ 2 - (max (‖q‖ - A) 0) ^ 2)
        + eT * ((max (‖p‖ - B) 0) ^ 2 - (max (‖q‖ - B) 0) ^ 2)|
      ≤ |(1 - eT) * ((max (‖p‖ - A) 0) ^ 2 - (max (‖q‖ - A) 0) ^ 2)|
        + |eT * ((max (‖p‖ - B) 0) ^ 2 - (max (‖q‖ - B) 0) ^ 2)| := abs_add_le _ _
    _ = |1 - eT| * |(max (‖p‖ - A) 0) ^ 2 - (max (‖q‖ - A) 0) ^ 2|
        + |eT| * |(max (‖p‖ - B) 0) ^ 2 - (max (‖q‖ - B) 0) ^ 2| := by rw [abs_mul, abs_mul]
    _ ≤ |1 - eT| * (2 * (1 + M) * (1 + ‖p‖ + ‖q‖) * ‖p - q‖)
        + |eT| * (2 * (1 + M) * (1 + ‖p‖ + ‖q‖) * ‖p - q‖) :=
        add_le_add (mul_le_mul_of_nonneg_left hA' (abs_nonneg _))
          (mul_le_mul_of_nonneg_left hB' (abs_nonneg _))
    _ = (|1 - eT| + |eT|) * (2 * (1 + M) * (1 + ‖p‖ + ‖q‖) * ‖p - q‖) := by ring
    _ ≤ (2 * (1 + |eT|)) * (2 * (1 + M) * (1 + ‖p‖ + ‖q‖) * ‖p - q‖) :=
        mul_le_mul_of_nonneg_right (by linarith) hT0
    _ = 4 * (1 + M) * (1 + |eT|) * (1 + ‖p‖ + ‖q‖) * ‖p - q‖ := by ring

/-- FS `def:tau`'s symbol is Lipschitz with linear growth; the constant depends
on `ε_T, s, d, ℓ` through `max |(2sℓ)⁻¹| |(2dsℓ)⁻¹|`. -/
theorem tauFun_lipschitz (eT s d ℓ : ℝ) (hs : 0 < s) (hd : 0 < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p q : EuclideanSpace ℝ (Fin 3),
      |Work.BoseB4.tauFun eT s d ℓ p - Work.BoseB4.tauFun eT s d ℓ q|
        ≤ C * (1 + |eT|) * (1 + ‖p‖ + ‖q‖) * ‖p - q‖ := by
  refine ⟨4 * (1 + max |(2 * s * ℓ)⁻¹| |(2 * d * s * ℓ)⁻¹|), ?_, ?_⟩
  · have h0 : (0:ℝ) ≤ max |(2 * s * ℓ)⁻¹| |(2 * d * s * ℓ)⁻¹| :=
      le_trans (abs_nonneg _) (le_max_left _ _)
    linarith
  · intro p q
    simp only [Work.BoseB4.tauFun]
    exact tauFun_lip_of eT _ _ _ (le_max_left _ _) (le_max_right _ _) p q

end Work.BoseK15
