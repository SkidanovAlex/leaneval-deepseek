/-
# Area 7 — the λ-weighted box sum `WBox`

The assembly of AREA 7 needs a finer per-character quantity than `boxAbs`: the χ₁-term of HB §15
uses that the zero ρ₁ of χ₁ is weighted by `e^{-aλ₁}` while the *other* zeros of χ₁ are weighted
by at most `e^{-aλ₀}` (`λ₀` = the second-zero bound).  We therefore introduce

  `WBox q K R χ = Σ'_ρ (mult χ ρ) · e^{-a λ(ρ)} · ‖F₂((1-ρ)𝓛)‖   (ρ in HB's box)`

with `a = L - 2K = 49/10`.  It dominates `‖boxSum q L K R χ‖`, and it is dominated by
`e^{-aλ}·boxAbs` when `λ` is a lower bound for the zero parameters of all box zeros of `χ`.
-/
import Mathlib
import Submission.Work.LinnikAreas.A7.Defs
import Submission.Work.A7.Integrands
import Submission.Work.LinnikContract.API.Hk_norm
import Submission.Work.LinnikContract.API.F2_norm_le_re
import Submission.Work.LinnikContract.API.box_api
import Submission.Commons.Algebra.BigOperators.norm_finsum_le_of_norm_le

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.LinnikAreas.A7

open Work.LinnikContract
open Work.A7

lemma ac_pos : (0:ℝ) < ac := by norm_num [ac]

/-- `Σ'_ρ (mult χ ρ) e^{-aλ(ρ)}‖F₂((1-ρ)𝓛)‖` over the zeros of `χ` in HB's box, `a = 49/10`. -/
def WBox (q : ℕ) [NeZero q] (K R : ℝ) (χ : DirichletCharacter ℂ q) : ℝ :=
  ∑ᶠ ρ : ℂ, if InBox q R ρ then
    (zeroMult χ ρ : ℝ) * Real.exp (-(ac * lamOf q ρ)) * ‖F2 K ((1 - ρ) * Real.log q)‖ else 0

/-- The reference integrand of `WBox`. -/
noncomputable def wfun (q : ℕ) [NeZero q] (K R : ℝ) (χ : DirichletCharacter ℂ q) : ℂ → ℝ :=
  fun ρ => if InBox q R ρ then
    (zeroMult χ ρ : ℝ) * Real.exp (-(ac * lamOf q ρ)) * ‖F2 K ((1 - ρ) * Real.log q)‖ else 0

lemma WBox_eq_finsum (q : ℕ) [NeZero q] (K R : ℝ) (χ : DirichletCharacter ℂ q) :
    WBox q K R χ = ∑ᶠ ρ : ℂ, wfun q K R χ ρ := rfl

/-- The real part of `(1-ρ)𝓛` is `λ(ρ)`. -/
lemma re_one_sub_mul_log {q : ℕ} (ρ : ℂ) :
    ((1 - ρ) * (Real.log q : ℂ)).re = lamOf q ρ := by
  rw [lamOf]
  simp only [Complex.mul_re, Complex.sub_re, Complex.one_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.sub_im, mul_zero, sub_zero]

lemma WBox_nonneg (q : ℕ) [NeZero q] (K R : ℝ) (χ : DirichletCharacter ℂ q) :
    0 ≤ WBox q K R χ := by
  rw [WBox_eq_finsum]
  refine finsum_nonneg (fun ρ => ?_)
  simp only [wfun]
  split_ifs with h
  · positivity
  · exact le_refl 0

/-! ## Supports -/

/-- The `WBox` integrand and the `boxSum` integrand vanish simultaneously. -/
theorem support_wfun_eq_cfun {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (L K R : ℝ) :
    Function.support (wfun q K R χ) = Function.support (cfun q L K R χ) := by
  ext ρ
  rw [Function.mem_support, Function.mem_support]
  by_cases h : InBox q R ρ
  · simp only [wfun, cfun, h, if_true]
    simp only [Hk, mul_ne_zero_iff, Complex.exp_ne_zero, norm_ne_zero_iff, Nat.cast_ne_zero,
      Real.exp_ne_zero, ne_eq, mul_eq_zero, not_or]
    tauto
  · simp [wfun, cfun, h]

/-- The `WBox` integrand and the `boxAbs` integrand vanish simultaneously. -/
theorem support_wfun_eq_bfun {q : ℕ} [NeZero q] (K R : ℝ) (χ : DirichletCharacter ℂ q) :
    Function.support (wfun q K R χ) = Function.support (Work.A7.bfun q K R χ) := by
  ext ρ
  rw [Function.mem_support, Function.mem_support]
  by_cases h : InBox q R ρ
  · simp only [wfun, Work.A7.bfun, h, if_true]
    simp only [mul_ne_zero_iff, norm_ne_zero_iff, Nat.cast_ne_zero, Real.exp_ne_zero, ne_eq,
      mul_eq_zero, not_or]
    tauto
  · simp [wfun, Work.A7.bfun, h]

/-! ## The comparison lemmas -/

/-- Triangle inequality for `finsum` against a real majorant whose support contains that of `f`. -/
theorem norm_finsum_le_of_norm_le_support {α : Type*} {E : Type*} [SeminormedAddCommGroup E]
    {f : α → E} {g : α → ℝ}
    (hsub : Function.support g ⊆ Function.support f) (h : ∀ i, ‖f i‖ ≤ g i) :
    ‖∑ᶠ i, f i‖ ≤ ∑ᶠ i, g i := by
  by_cases hg : Function.HasFiniteSupport g
  · exact Commons.Algebra.BigOperators.norm_finsum_le_of_norm_le hg h
  · have hf : ¬ Function.HasFiniteSupport f := fun hf => hg (hf.subset hsub)
    rw [finsum_of_not_hasFiniteSupport hf, norm_zero, finsum_of_not_hasFiniteSupport hg]

/-- The `WBox` integrand dominates the `boxSum` integrand in norm. -/
lemma norm_cfun_le_wfun {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {L K R : ℝ}
    (hLK : L - 2*K = ac) (ρ : ℂ) :
    ‖cfun q L K R χ ρ‖ ≤ wfun q K R χ ρ := by
  simp only [cfun, wfun]
  by_cases hbox : InBox q R ρ
  · rw [if_pos hbox, if_pos hbox]
    have hnorm : ‖Hk L K ((1 - ρ) * (Real.log q : ℂ))‖ =
        Real.exp (-(L - 2*K) * lamOf q ρ) * ‖F2 K ((1 - ρ) * (Real.log q : ℂ))‖ := by
      rw [Work.LinnikContract.API.Hk_norm, re_one_sub_mul_log]
    have hexp : Real.exp (-(L - 2*K) * lamOf q ρ) = Real.exp (-(ac * lamOf q ρ)) := by
      rw [hLK, neg_mul]
    rw [norm_mul, hnorm, hexp, Complex.norm_natCast]
    exact le_of_eq (by ring)
  · rw [if_neg hbox, if_neg hbox, norm_zero]

/-- The `WBox` integrand is non-negative. -/
lemma wfun_nonneg {q : ℕ} [NeZero q] (K R : ℝ) (χ : DirichletCharacter ℂ q) (ρ : ℂ) :
    0 ≤ wfun q K R χ ρ := by
  simp only [wfun]
  split_ifs with h
  · positivity
  · exact le_refl 0

/-- Pointwise domination of the `WBox` integrand by `e^{-aλ}·bfun`. -/
lemma wfun_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (K R : ℝ) {lam : ℝ}
    (hlam : ∀ ρ : ℂ, InBox q R ρ → zeroMult χ ρ ≠ 0 → lam ≤ lamOf q ρ) (ρ : ℂ) :
    wfun q K R χ ρ ≤ Real.exp (-(ac * lam)) * Work.A7.bfun q K R χ ρ := by
  simp only [wfun, Work.A7.bfun]
  by_cases hbox : InBox q R ρ
  · rw [if_pos hbox, if_pos hbox]
    by_cases hm : zeroMult χ ρ = 0
    · rw [hm]; simp
    · have hle : Real.exp (-(ac * lamOf q ρ)) ≤ Real.exp (-(ac * lam)) := by
        rw [Real.exp_le_exp]
        nlinarith [ac_pos, hlam ρ hbox hm]
      have hz : (0:ℝ) ≤ (zeroMult χ ρ : ℝ) := Nat.cast_nonneg _
      have hF : (0:ℝ) ≤ ‖F2 K ((1 - ρ) * (Real.log q : ℂ))‖ := norm_nonneg _
      have h1 : (zeroMult χ ρ : ℝ) * Real.exp (-(ac * lamOf q ρ)) ≤
          (zeroMult χ ρ : ℝ) * Real.exp (-(ac * lam)) := mul_le_mul_of_nonneg_left hle hz
      calc (zeroMult χ ρ : ℝ) * Real.exp (-(ac * lamOf q ρ)) * ‖F2 K ((1 - ρ) * Real.log q)‖
          ≤ (zeroMult χ ρ : ℝ) * Real.exp (-(ac * lam)) * ‖F2 K ((1 - ρ) * Real.log q)‖ :=
            mul_le_mul_of_nonneg_right h1 hF
        _ = Real.exp (-(ac * lam)) * ((zeroMult χ ρ : ℝ) * ‖F2 K ((1 - ρ) * Real.log q)‖) := by
            ring
  · rw [if_neg hbox, if_neg hbox, mul_zero]

/-- The integrand of `WBox` vanishes exactly when the integrand of `boxAbs` does. -/
lemma wfun_ne_zero_iff {q : ℕ} [NeZero q] (K R : ℝ) (χ : DirichletCharacter ℂ q) (ρ : ℂ) :
    wfun q K R χ ρ ≠ 0 ↔ Work.A7.bfun q K R χ ρ ≠ 0 := by
  have h2 := congrArg (fun s : Set ℂ => (ρ ∈ s)) (support_wfun_eq_bfun K R χ)
  simpa [Function.mem_support] using h2

/-- `‖boxSum‖` is bounded by the λ-weighted box sum. -/
theorem norm_boxSum_le_WBox {q : ℕ} [NeZero q] {L K R : ℝ} (hLK : L - 2*K = ac)
    (χ : DirichletCharacter ℂ q) : ‖boxSum q L K R χ‖ ≤ WBox q K R χ := by
  have hsum : boxSum q L K R χ = ∑ᶠ ρ : ℂ, cfun q L K R χ ρ := rfl
  rw [hsum, WBox_eq_finsum]
  exact norm_finsum_le_of_norm_le_support
    (f := cfun q L K R χ) (g := wfun q K R χ)
    (le_of_eq (support_wfun_eq_cfun χ L K R)) (fun ρ => norm_cfun_le_wfun χ hLK ρ)

/-- `WBox` is dominated by `e^{-aλ}·boxAbs` once `λ` is a lower bound for the zero parameters of
all box zeros of `χ`. -/
theorem WBox_le_exp_mul_boxAbs {q : ℕ} [NeZero q] (K R : ℝ)
    (χ : DirichletCharacter ℂ q) {lam : ℝ}
    (hlam : ∀ ρ : ℂ, InBox q R ρ → zeroMult χ ρ ≠ 0 → lam ≤ lamOf q ρ) :
    WBox q K R χ ≤ Real.exp (-(ac * lam)) * boxAbs q K R χ := by
  rw [WBox_eq_finsum]
  have hb : boxAbs q K R χ = ∑ᶠ ρ : ℂ, Work.A7.bfun q K R χ ρ := rfl
  rw [hb, mul_finsum]
  have hmain : ‖∑ᶠ ρ : ℂ, wfun q K R χ ρ‖ ≤
      ∑ᶠ ρ : ℂ, Real.exp (-(ac * lam)) * Work.A7.bfun q K R χ ρ := by
    refine norm_finsum_le_of_norm_le_support (f := wfun q K R χ)
      (g := fun ρ : ℂ => Real.exp (-(ac * lam)) * Work.A7.bfun q K R χ ρ) ?_ ?_
    · intro ρ hρ
      rw [Function.mem_support] at hρ ⊢
      have hb0 : Work.A7.bfun q K R χ ρ ≠ 0 := by
        intro h0; exact hρ (by rw [h0, mul_zero])
      exact (wfun_ne_zero_iff K R χ ρ).mpr hb0
    · intro ρ
      rw [Real.norm_eq_abs, abs_of_nonneg (wfun_nonneg K R χ ρ)]
      exact wfun_le χ K R hlam ρ
  rwa [Real.norm_eq_abs, abs_of_nonneg (finsum_nonneg (fun ρ => wfun_nonneg K R χ ρ))] at hmain

end Work.LinnikAreas.A7
