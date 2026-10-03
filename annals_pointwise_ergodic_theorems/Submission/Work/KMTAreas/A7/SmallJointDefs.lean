/-
# The twisted bilinear multiplier with a *joint* continuous symbol (A7, §6--§7)

`Work.KMTAreas.A7.smallBtwist` is the §6/§7 twisted bilinear multiplier at exact arithmetic
heights with a *product* symbol `m₁ ⊗ m₂`:

  `smallBtwist ρ P l₁ l₂ m₁ m₂ h k x = ∑' j₁, ∑' j₂, K(j₁,j₂) h(x-j₁) k(x-j₂)`,
  `K(j₁,j₂) = smallArithKernel ρ P q l₁ l₂ j₁ j₂ · cw m₁ j₁ · cw m₂ j₂`,  `q = arithQ ρ (max l₁ l₂)`.

The paper's §6 estimates (Proposition `mod-approx`, Lemma `crude-mult`(ii)) compare this operator
with the halved average `Ã_N = bilinOp (khalf N P)` through a symbol that is *not* a product: the
oscillatory integral `m̃_{N,ℝ}(ξ₁,ξ₂) = ∫_{1/2}^1 e(ξ₁Nt + ξ₂P(Nt))dt` (`ModelApproxDefs.mTilde`).
The carrier of that comparison is the twisted multiplier with a general (joint) continuous symbol
`M : ℝ × ℝ → ℂ`,

  `B^{l₁,l₂,m_Ẑ}_M(h,k)(x) = ∑' j₁, ∑' j₂, (∑_{α₁∈A₁, α₂∈A₂} m_Ẑ(α₁,α₂) e(-j₁α₁-j₂α₂))
      · (coefficient kernel of M)(j₁,j₂) · h(x-j₁) · k(x-j₂)`,

which is what this module introduces (`cw2J`, `smallJointK`, `smallBtwistJ`), together with

* `smallBtwistJ_prod` — the agreement with the product-symbol operator `smallBtwist`;
* `norm_mZ_le_one`, `norm_smallArithKernel_le` — the trivial arithmetic bounds `‖m_Ẑ‖ ≤ 1` and
  `‖smallArithKernel‖ ≤ #A₁·#A₂`;
* `tsum_norm_smallJointK_le` — the `ℓ¹(ℤ²)`-mass bound `∑ ‖smallJointK‖ ≤ #A₁·#A₂·∑‖cw2J M‖`;
* `eLpNorm_smallBtwistJ_le` / `eLpNorm_smallBtwistJ_le_of_cw2_mass` — the resulting
  `ℓ^{p₁} × ℓ^{p₂} → ℓ^p` operator bound (Young, via `Work.KMTAreas.A7.BilinOpLp`).

The analytic input (the paper's Lemma `crude-mult`(ii)) is the *summability bound*
`∑' p, ‖cw2 M p‖ ≤ C·B` for a symbol supported in a narrow band with derivative bounds `B`; it is
the target `Work.KMTAreas.A7.tsum_cw2_le_of_banded_deriv` (whose one-dimensional versions, e.g.
`A7/CwTsumLe.lean`, are already in the tree).  With it, `eLpNorm_smallBtwistJ_le_of_cw2_mass` turns
*symbol* estimates into *operator* estimates — the missing "symbol ⇒ operator" step of §6.

`cw2J` is the local copy of `Work.KMTAreas.A7.cw2` of `A7/Cw2Defs.lean` (the two definitions are
syntactically identical, so the estimates about `cw2` apply to `cw2J` by unfolding).
-/
import Mathlib
import Submission.Work.KMTAreas.A7.SmallDefs
import Submission.Work.KMTAreas.A7.BilinOpLp

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset
open scoped ENNReal NNReal BigOperators

open Work.Analysis.IonescuWainger

/-! ## The character `ee` -/

private theorem ee_add' (a b : ℝ) : ee (a + b) = ee a * ee b := by
  rw [ee, ee, ee, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-! ## The two-dimensional coefficient kernel -/

/-- **The two-dimensional coefficient kernel** of a symbol `M : ℝ → ℝ → ℂ` at the lattice point
`p : ℤ × ℤ`.  (Identical to `Work.KMTAreas.A7.cw2` of `A7/Cw2Defs.lean`.) -/
def cw2J (M : ℝ → ℝ → ℂ) (p : ℤ × ℤ) : ℂ :=
  ∫ x, ∫ y, M x y * ee (-((p.1 : ℝ) * x + (p.2 : ℝ) * y))

@[simp] theorem cw2J_apply (M : ℝ → ℝ → ℂ) (p : ℤ × ℤ) :
    cw2J M p = ∫ x, ∫ y, M x y * ee (-((p.1 : ℝ) * x + (p.2 : ℝ) * y)) := rfl

/-! ## The arithmetic symbol is bounded by one -/

/-- **The arithmetic symbol `m_Ẑ` is bounded by one.**  It is the average of `q` unimodular
characters. -/
theorem norm_mZ_le_one (P : Polynomial ℤ) (q : ℕ) (hq : 0 < q)
    (α₁ α₂ : Work.Analysis.IonescuWainger.Circle) : ‖mZ P q α₁ α₂‖ ≤ 1 := by
  have hq' : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hterm : ∀ n ∈ Finset.range q,
      ‖fourier (T := 1) (n : ℤ) α₁ * fourier (T := 1) (P.eval (n : ℤ)) α₂‖ = 1 := by
    intro n _
    rw [norm_mul, fourier_apply, fourier_apply, Circle.norm_coe, Circle.norm_coe, one_mul]
  calc ‖mZ P q α₁ α₂‖ = ‖(q : ℂ)⁻¹‖ * ‖∑ n ∈ Finset.range q,
        fourier (T := 1) (n : ℤ) α₁ * fourier (T := 1) (P.eval (n : ℤ)) α₂‖ := by
        rw [mZ, norm_mul]
    _ ≤ ‖(q : ℂ)⁻¹‖ * ∑ n ∈ Finset.range q,
        ‖fourier (T := 1) (n : ℤ) α₁ * fourier (T := 1) (P.eval (n : ℤ)) α₂‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)
    _ = ‖(q : ℂ)⁻¹‖ * q := by rw [Finset.sum_congr rfl hterm, Finset.sum_const,
        Finset.card_range, nsmul_eq_mul, mul_one]
    _ = 1 := by
        rw [norm_inv, Complex.norm_natCast, inv_mul_cancel₀ hq'.ne']

/-- **The trivial bound for the exact-height arithmetic kernel**:
`‖smallArithKernel ρ P q l₁ l₂ j₁ j₂‖ ≤ #(A₁)·#(A₂)`, the cardinalities of the two exact-height
frequency sets. -/
theorem norm_smallArithKernel_le (ρ : ℝ) (P : Polynomial ℤ) (q : ℕ) (l₁ l₂ : ℕ) (j₁ j₂ : ℤ) :
    ‖smallArithKernel ρ P q l₁ l₂ j₁ j₂‖
      ≤ (((diffFreqs ρ l₁).card : ℝ) * ((diffFreqs ρ l₂).card : ℝ)) := by
  have hterm : ∀ α₁ ∈ diffFreqs ρ l₁, ∀ α₂ ∈ diffFreqs ρ l₂,
      ‖mZ P q α₁ α₂ * fourier (T := 1) (-j₁) α₁ * fourier (T := 1) (-j₂) α₂‖ ≤ 1 := by
    intro α₁ _ α₂ _
    have hf : ∀ (y : ℤ) (α : Work.Analysis.IonescuWainger.Circle),
        ‖fourier (T := 1) y α‖ = 1 := by
      intro y α; rw [fourier_apply]; exact Circle.norm_coe _
    rw [norm_mul, norm_mul, hf, hf, mul_one, mul_one]
    by_cases hq : q = 0
    · subst hq; simp [mZ]
    · exact norm_mZ_le_one P q (Nat.pos_of_ne_zero hq) α₁ α₂
  calc ‖smallArithKernel ρ P q l₁ l₂ j₁ j₂‖
      = ‖∑ α₁ ∈ diffFreqs ρ l₁, ∑ α₂ ∈ diffFreqs ρ l₂,
          mZ P q α₁ α₂ * fourier (T := 1) (-j₁) α₁ * fourier (T := 1) (-j₂) α₂‖ := rfl
    _ ≤ ∑ α₁ ∈ diffFreqs ρ l₁, ‖∑ α₂ ∈ diffFreqs ρ l₂,
          mZ P q α₁ α₂ * fourier (T := 1) (-j₁) α₁ * fourier (T := 1) (-j₂) α₂‖ :=
        norm_sum_le _ _
    _ ≤ ∑ α₁ ∈ diffFreqs ρ l₁, ∑ α₂ ∈ diffFreqs ρ l₂, (1 : ℝ) :=
        Finset.sum_le_sum (fun α₁ h₁ =>
          (norm_sum_le _ _).trans (Finset.sum_le_sum (fun α₂ h₂ => hterm α₁ h₁ α₂ h₂)))
    _ = (((diffFreqs ρ l₁).card : ℝ) * ((diffFreqs ρ l₂).card : ℝ)) := by
        simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm]

/-! ## The twisted multiplier with a joint symbol -/

/-- **The kernel of the twisted bilinear multiplier with a joint continuous symbol** `M`:
the product of the exact-height arithmetic kernel and the two-dimensional coefficient kernel
`cw2J M` of `M`. -/
noncomputable def smallJointK (ρ : ℝ) (P : Polynomial ℤ) (q : ℕ) (l₁ l₂ : ℕ)
    (M : ℝ → ℝ → ℂ) (j₁ j₂ : ℤ) : ℂ :=
  smallArithKernel ρ P q l₁ l₂ j₁ j₂ * cw2J M (j₁, j₂)

/-- **The twisted bilinear multiplier `B^{l₁,l₂,m_Ẑ}_M` with a joint continuous symbol.**  For a
product symbol `M = m₁ ⊗ m₂` it agrees with `Work.KMTAreas.A7.smallBtwist` (`smallBtwistJ_prod`). -/
noncomputable def smallBtwistJ (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ : ℕ) (M : ℝ → ℝ → ℂ)
    (h k : ℤ → ℂ) : ℤ → ℂ :=
  bilinOp (smallJointK ρ P (arithQ ρ (max l₁ l₂)) l₁ l₂ M) h k

/-- `smallBtwist` is the bilinear convolution with the kernel
`smallArithKernel · cw m₁ · cw m₂` (definitional). -/
theorem smallBtwist_eq_bilinOp (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ : ℕ) (m₁ m₂ : ℝ → ℂ)
    (h k : ℤ → ℂ) :
    smallBtwist ρ P l₁ l₂ m₁ m₂ h k
      = bilinOp (fun j₁ j₂ => smallArithKernel ρ P (arithQ ρ (max l₁ l₂)) l₁ l₂ j₁ j₂
          * cw m₁ j₁ * cw m₂ j₂) h k := rfl

/-- **The two-dimensional coefficient kernel of a product symbol is the product of the
one-dimensional ones**: `cw2J (m₁ ⊗ m₂) (j₁,j₂) = cw m₁ j₁ * cw m₂ j₂`. -/
theorem cw2J_prod (m₁ m₂ : ℝ → ℂ) (j₁ j₂ : ℤ) :
    cw2J (fun x y => m₁ x * m₂ y) (j₁, j₂) = cw m₁ j₁ * cw m₂ j₂ := by
  have key : ∀ x y : ℝ, ee (-((j₁ : ℝ) * x + (j₂ : ℝ) * y))
      = ee (-(j₁ : ℝ) * x) * ee (-(j₂ : ℝ) * y) := by
    intro x y
    rw [show -((j₁ : ℝ) * x + (j₂ : ℝ) * y)
          = -(j₁ : ℝ) * x + -(j₂ : ℝ) * y by ring, ee_add']
  have h1 : (∫ x, ∫ y, (m₁ x * ee (-(j₁ : ℝ) * x)) * (m₂ y * ee (-(j₂ : ℝ) * y)))
      = ∫ x, (m₁ x * ee (-(j₁ : ℝ) * x)) * (∫ y, m₂ y * ee (-(j₂ : ℝ) * y)) := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    exact integral_const_mul _ _
  calc cw2J (fun x y => m₁ x * m₂ y) (j₁, j₂)
      = ∫ x, ∫ y, m₁ x * m₂ y * ee (-((j₁ : ℝ) * x + (j₂ : ℝ) * y)) := cw2J_apply _ _
    _ = ∫ x, ∫ y, (m₁ x * ee (-(j₁ : ℝ) * x)) * (m₂ y * ee (-(j₂ : ℝ) * y)) := by
        refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
        refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
        show m₁ x * m₂ y * ee (-((j₁ : ℝ) * x + (j₂ : ℝ) * y))
          = m₁ x * ee (-(j₁ : ℝ) * x) * (m₂ y * ee (-(j₂ : ℝ) * y))
        rw [key x y]; ring
    _ = ∫ x, (m₁ x * ee (-(j₁ : ℝ) * x)) * (∫ y, m₂ y * ee (-(j₂ : ℝ) * y)) := h1
    _ = (∫ x, m₁ x * ee (-(j₁ : ℝ) * x)) * (∫ y, m₂ y * ee (-(j₂ : ℝ) * y)) :=
        integral_mul_const _ _
    _ = cw m₁ j₁ * cw m₂ j₂ := rfl

/-- **`smallBtwistJ` with a product symbol is `smallBtwist`.** -/
theorem smallBtwistJ_prod (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ : ℕ) (m₁ m₂ : ℝ → ℂ)
    (h k : ℤ → ℂ) :
    smallBtwistJ ρ P l₁ l₂ (fun x y => m₁ x * m₂ y) h k
      = smallBtwist ρ P l₁ l₂ m₁ m₂ h k := by
  rw [smallBtwist_eq_bilinOp]
  refine congrArg (fun K => bilinOp K h k) ?_
  funext j₁ j₂
  rw [smallJointK, cw2J_prod]
  ring

/-! ## The mass bound -/

/-- **The pointwise bound for the kernel of the joint-symbol twisted multiplier.** -/
theorem norm_smallJointK_le (ρ : ℝ) (P : Polynomial ℤ) (q : ℕ) (l₁ l₂ : ℕ) (M : ℝ → ℝ → ℂ)
    (j₁ j₂ : ℤ) :
    ‖smallJointK ρ P q l₁ l₂ M j₁ j₂‖
      ≤ (((diffFreqs ρ l₁).card : ℝ) * ((diffFreqs ρ l₂).card : ℝ)) * ‖cw2J M (j₁, j₂)‖ := by
  rw [smallJointK, norm_mul]
  exact mul_le_mul_of_nonneg_right (norm_smallArithKernel_le ρ P q l₁ l₂ j₁ j₂) (norm_nonneg _)

/-- **The `ℓ¹(ℤ²)` mass of the joint-symbol kernel** is bounded by the product of the two
exact-height cardinalities times the mass of the coefficient kernel of the symbol. -/
theorem tsum_norm_smallJointK_le (ρ : ℝ) (P : Polynomial ℤ) (q : ℕ) (l₁ l₂ : ℕ)
    (M : ℝ → ℝ → ℂ) (hM : Summable (fun p : ℤ × ℤ => ‖cw2J M p‖)) :
    (∑' p : ℤ × ℤ, ‖smallJointK ρ P q l₁ l₂ M p.1 p.2‖)
      ≤ (((diffFreqs ρ l₁).card : ℝ) * ((diffFreqs ρ l₂).card : ℝ))
          * (∑' p : ℤ × ℤ, ‖cw2J M p‖) := by
  have hC : (0 : ℝ) ≤ ((diffFreqs ρ l₁).card : ℝ) * ((diffFreqs ρ l₂).card : ℝ) :=
    mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hsum : Summable (fun p : ℤ × ℤ => ‖smallJointK ρ P q l₁ l₂ M p.1 p.2‖) :=
    Summable.of_nonneg_of_le (fun p => norm_nonneg _)
      (fun p => norm_smallJointK_le ρ P q l₁ l₂ M p.1 p.2) (hM.mul_left _)
  rw [← tsum_mul_left]
  exact Summable.tsum_le_tsum (fun p => norm_smallJointK_le ρ P q l₁ l₂ M p.1 p.2) hsum
    (hM.mul_left _)

/-- **The `ℓ^{p₁} × ℓ^{p₂} → ℓ^p` bound for the joint-symbol twisted multiplier**, by Young's
inequality on the kernel (`Work.KMTAreas.A7.BilinOpLp`). -/
theorem eLpNorm_smallBtwistJ_le (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ : ℕ) (M : ℝ → ℝ → ℂ)
    {p p₁ p₂ : ENNReal} (hp : p₁⁻¹ + p₂⁻¹ = p⁻¹) (hp1 : 1 ≤ p)
    (hM : Summable (fun p : ℤ × ℤ => ‖cw2J M p‖)) (h k : ℤ → ℂ) :
    eLpNorm (fun x : ℤ => smallBtwistJ ρ P l₁ l₂ M h k x) p Measure.count
      ≤ ENNReal.ofReal (∑' p : ℤ × ℤ,
          ‖smallJointK ρ P (arithQ ρ (max l₁ l₂)) l₁ l₂ M p.1 p.2‖)
        * eLpNorm h p₁ Measure.count * eLpNorm k p₂ Measure.count := by
  have hsum : Summable (fun p : ℤ × ℤ =>
      ‖smallJointK ρ P (arithQ ρ (max l₁ l₂)) l₁ l₂ M p.1 p.2‖) :=
    Summable.of_nonneg_of_le (fun p => norm_nonneg _)
      (fun p => norm_smallJointK_le ρ P (arithQ ρ (max l₁ l₂)) l₁ l₂ M p.1 p.2) (hM.mul_left _)
  exact BilinOpLp hp hp1 hsum h k

/-- **The operator bound with the coefficient-mass bound as input** — the form in which the
`crude-mult`(ii) estimates (`Work.KMTAreas.A7.tsum_cw2_le_of_banded_deriv`, `A7/CwTsumLe.lean`)
are consumed. -/
theorem eLpNorm_smallBtwistJ_le_of_cw2_mass (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ : ℕ)
    (M : ℝ → ℝ → ℂ) {p p₁ p₂ : ENNReal} (hp : p₁⁻¹ + p₂⁻¹ = p⁻¹) (hp1 : 1 ≤ p)
    {B : ℝ} (hM : Summable (fun p : ℤ × ℤ => ‖cw2J M p‖))
    (hmass : (∑' p : ℤ × ℤ, ‖cw2J M p‖) ≤ B) (h k : ℤ → ℂ) :
    eLpNorm (fun x : ℤ => smallBtwistJ ρ P l₁ l₂ M h k x) p Measure.count
      ≤ ENNReal.ofReal (((diffFreqs ρ l₁).card : ℝ) * ((diffFreqs ρ l₂).card : ℝ) * B)
        * eLpNorm h p₁ Measure.count * eLpNorm k p₂ Measure.count := by
  have hC : (0 : ℝ) ≤ ((diffFreqs ρ l₁).card : ℝ) * ((diffFreqs ρ l₂).card : ℝ) :=
    mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  refine (eLpNorm_smallBtwistJ_le ρ P l₁ l₂ M hp hp1 hM h k).trans ?_
  refine mul_le_mul' (mul_le_mul' ?_ le_rfl) le_rfl
  refine ENNReal.ofReal_le_ofReal ?_
  calc (∑' p : ℤ × ℤ, ‖smallJointK ρ P (arithQ ρ (max l₁ l₂)) l₁ l₂ M p.1 p.2‖)
      ≤ (((diffFreqs ρ l₁).card : ℝ) * ((diffFreqs ρ l₂).card : ℝ))
          * (∑' p : ℤ × ℤ, ‖cw2J M p‖) := tsum_norm_smallJointK_le ρ P _ l₁ l₂ M hM
    _ ≤ (((diffFreqs ρ l₁).card : ℝ) * ((diffFreqs ρ l₂).card : ℝ)) * B :=
        mul_le_mul_of_nonneg_left hmass hC

end

end Work.KMTAreas.A7
