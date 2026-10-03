/-
# The window-parametrised model symbols of the mixed case (`l₁ = 0`, `l₂ ≥ 1`)

The §6 model operator of the mixed case is the window-smoothed twisted bilinear multiplier

  `loMixedOp ρ P N l₂ k₁ k₂ = ∫_{1/2}^1 B^{0,l₂,m_Ẑ}_{m_*}(T^0_{φ_{N,t}}·, T^{l₂}_{φ̃_{N,t}}·) dt`

with the *repaired* window `u = loMixedU ρ P.natDegree l₂ k₁ k₂ = max (uScale ρ L) (d·l₂+3)`
(`L = max l₂ k₁ k₂`, `d = P.natDegree`), which separates the arithmetic fibres of
`diffFreqs ρ l₂` (the paper's free constant `C₂`).

This module exposes the model in *symbol* form with the window parameter `u` left free, so that

* the frozen-window symbols of area A6 (`arithKerM`, `symM`) are the instance
  `u = uScale ρ (lcL l₁ l₂ k₁ k₂)`,
* the repaired-window symbols of the mixed case are the instance
  `u = loMixedU ρ P.natDegree l₂ k₁ k₂`,

and every statement about the collapse of the §6 model symbol can be proved *once*, uniformly in
`u`, once the two arc facts (`periodize (mStarF u) = 1` on `ℝ_{≤-(2u+1)}`, supported in
`ℝ_{≤-2u}`, and the same for `mStargF`) and the non-aliasing of the arithmetic frequencies at the
radius `2^{-2u}` are available at that `u`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.LoMixedDefs
import Submission.Work.KMTAreas.A7.LoErrAux
import Submission.Work.KMTAreas.A7.ModelApproxHiKernels
import Submission.Work.KMTPlan.A6.symC_sub_symM_eq_symD
import Submission.Work.KMTPlan.A6.bilinOp_intervalIntegral
import Submission.Work.KMTPlan.A6.coeff2_sub_symC_symM

set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems

/-- **The arithmetic kernel of the §6 twisted bilinear multiplier at exact arithmetic heights
`(l₁,l₂)`, with window parameter `u`**: the double Fourier coefficient family of
`(1_{(ℚ/ℤ)_{l₁}} ⊗ 1_{(ℚ/ℤ)_{l₂}}) m_Ẑ` times the two `ℓ¹` window kernels `cw (m_* u)`. -/
noncomputable def arithKerMWin (ρ : ℝ) (P : ℤ[X]) (u l₁ l₂ : ℕ) : ℤ → ℤ → ℂ :=
  fun a b =>
    Work.KMTPlan.A6.arithKernelEx ρ P (arithQ ρ (max l₁ l₂)) l₁ l₂ a b
      * cw (mStarF u) a * cw (mStargF P.natDegree u) b

/-- The frozen-window arithmetic kernel of area A6 is the instance `u = uScale ρ (lcL …)`. -/
theorem arithKerM_eq_win (ρ : ℝ) (P : ℤ[X]) (l₁ l₂ k₁ k₂ : ℕ) :
    Work.KMTPlan.A6.arithKerM ρ P l₁ l₂ k₁ k₂
      = arithKerMWin ρ P (uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂)) l₁ l₂ := rfl

/-- **The §6 model symbol with window parameter `u`**: the `t`-integral of the symbol of the
twisted bilinear multiplier times the symbols of the two modulated exact-height multipliers. -/
noncomputable def symMWin (ρ : ℝ) (P : ℤ[X]) (u N l₁ l₂ k₁ k₂ : ℕ) : ℝ → ℝ → ℂ :=
  fun x y =>
    ∫ t in (1 / 2 : ℝ)..1,
      Work.KMTPlan.A6.symSeq2 (arithKerMWin ρ P u l₁ l₂) x y
        * Work.KMTPlan.A6.symSeq (Work.KMTPlan.A6.tmKer ρ l₁ (varphiNt N k₁ t)) x
        * Work.KMTPlan.A6.symSeq
            (Work.KMTPlan.A6.tmKer ρ l₂ (varphitildeNt P P.natDegree N k₂ t)) y

/-- The frozen-window model symbol of area A6 is the instance `u = uScale ρ (lcL …)`. -/
theorem symM_eq_win (ρ : ℝ) (P : ℤ[X]) (N l₁ l₂ k₁ k₂ : ℕ) :
    Work.KMTPlan.A6.symM ρ P N l₁ l₂ k₁ k₂
      = symMWin ρ P (uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂)) N l₁ l₂ k₁ k₂ := rfl

/-- The window of the mixed model, as the single parameter `u` of `symMWin`. -/
theorem loMixedU_eq (ρ : ℝ) (P : ℤ[X]) (l₂ k₁ k₂ : ℕ) :
    loMixedU ρ P.natDegree l₂ k₁ k₂
      = max (uScale ρ (Work.KMTPlan.A6.lcL 0 l₂ k₁ k₂)) (P.natDegree * l₂ + 3) := rfl

/-- **The model operator in kernel form**: `smallBtwist` is `bilinOp` with the kernel
`arithKerMWin`, so that `loMixedOp` is the `t`-integral of `bilinOp (arithKerMWin u 0 l₂)`
applied to the two modulated pieces. -/
theorem loMixedOp_eq_integral_bilinOp (ρ : ℝ) (P : ℤ[X]) (N l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ)
    (x : ℤ) :
    loMixedOp ρ P N l₂ k₁ k₂ f g x
      = ∫ t in (1 / 2 : ℝ)..1,
          bilinOp (arithKerMWin ρ P (loMixedU ρ P.natDegree l₂ k₁ k₂) 0 l₂)
            (Tm ρ 0 (varphiNt N k₁ t) f)
            (Tm ρ l₂ (varphitildeNt P P.natDegree N k₂ t) g) x := rfl

end

end Work.KMTAreas.A7

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger

/-! ## The concrete column in kernel form on the guard, and the first fibre is a singleton -/

/-- On the guard (large scales, main regime), the concrete column at the arithmetic heights
`(0,l₂)` is the bilinear convolution with the coefficient kernel of `symC`. -/
theorem loMainPart_eq_bilinOp_symC (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (P : ℤ[X])
    (C₀ : ℕ) (a : ℕ → NNReal) (f g : ℤ → ℂ) (l₂ k₁ k₂ n : ℕ) (x : ℤ)
    (hf : Work.KMTAreas.A5.BoundedZ f) (hg : Work.KMTAreas.A5.BoundedZ g)
    (h : loGuard ρ C₀ a 0 l₂ k₁ k₂ n) :
    mainPartTuple ρ P C₀ a f g 0 l₂ k₁ k₂ n x
      = bilinOp (fun u v => Work.KMTPlan.A6.coeff2
          (Work.KMTPlan.A6.symC ρ P (Nat.floor (a n)) 0 l₂ k₁ k₂) u v) f g x := by
  rw [mainPartTuple_apply, if_pos h,
    varpPiece_eq_bilinOp_hiKconc ρ P a 0 l₂ k₁ k₂ n hf hg x]
  congr 1
  funext u v
  have hk : hiKconc ρ P a 0 l₂ k₁ k₂ n
      = kernComp (khalf (Nat.floor (a n)) P)
          (Work.KMTPlan.A6.tmKer ρ 0 (varphiN (Nat.floor (a n)) k₁))
          (Work.KMTPlan.A6.tmKer ρ l₂
            (varphitildeN P.natDegree (Nat.floor (a n)) k₂)) := by
    rw [hiKconc_eq ρ hρ hρ1 P a 0 l₂ k₁ k₂ n]
    show hiKconcN ρ P (Nat.floor (a n)) 0 l₂ k₁ k₂ = _
    unfold hiKconcN
    simp only [Work.KMTPlan.A6.tmKer]
    rfl
  rw [hk]
  exact congrFun (congrFun (Work.KMTPlan.A6.cesb_kernComp_eq_coeff2_symC ρ hρ hρ1 P 0 l₂ k₁ k₂
    (Nat.floor (a n))) u) v

/-- The first arithmetic fibre set of the mixed case is the singleton `{0}`, hence non-aliasing
at every radius of the form `-(2u)`, `u ≥ 1`. -/
theorem loNonAliasingDiffFreqsZero (ρ : ℝ) {u : ℕ} (hu : 1 ≤ u) :
    NonAliasing (-(2 * (u : ℤ))) (diffFreqs ρ 0) := by
  have h0 : diffFreqs ρ 0 = iwArithFreqs ρ 0 := by
    rw [diffFreqs, if_pos rfl]
  rw [h0]
  exact Work.KMTPlan.A6.symp_NonAliasing_subset
    (nonAliasing_iwArithFreqs_zero ρ hu)
    (fun x hx => Finset.mem_union_left _ hx)

/-- The model tuple of the mixed range, unfolded at its guard. -/
theorem loMixedTuple_apply (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → NNReal) (f g : ℤ → ℂ)
    (l₂ k₁ k₂ n : ℕ) (x : ℤ) :
    loMixedTuple ρ P C₀ a f g l₂ k₁ k₂ n x =
      (if loGuard ρ C₀ a 0 l₂ k₁ k₂ n then
        loMixedOp ρ P (Nat.floor (a n)) l₂ k₁ k₂ f g x else 0) := rfl

end


end Work.KMTAreas.A7
namespace Work.KMTPlan.A6

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger
open Work.KMTAreas.A7

/-- **Poisson summation for the window-parametrised §6 arithmetic kernel**: the `ℤ²`-symbol of
`arithKerMWin ρ P u l₁ l₂` is the finite arithmetic sum over the exact-height frequencies of `m_Ẑ`
against the two periodisations of the tensor windows `m_* = η_{≤-2u}`, `m̃_* = η_{≤-2du}`.
This is `symp_symSeq2_arithKerM_eq` with the window parameter `u` left free. -/
theorem arithKerMWinSymSeq2 (ρ : ℝ) (P : Polynomial ℤ) (u l₁ l₂ : ℕ) (x y : ℝ) :
    symSeq2 (arithKerMWin ρ P u l₁ l₂) x y
      = ∑ α₁ ∈ diffFreqs ρ l₁, ∑ α₂ ∈ diffFreqs ρ l₂,
          mZ P (arithQ ρ (max l₁ l₂)) α₁ α₂
            * periodize (mStarF u) ((x : ℝ) - α₁)
            * periodize (mStargF P.natDegree u) ((y : ℝ) - α₂) := by
  -- the one-dimensional Poisson identities, with the character spliced in
  have hQ1 : ∀ α₁ : Circ, (∑' a : ℤ, cw (mStarF u) a * fourier (T := 1) (-a) α₁
        * eeC ((a : ℝ) * x)) = periodize (mStarF u) (((x : ℝ) : Circ) - α₁) := by
    intro α₁
    rw [← symp_cw_tsum_fourier (symp_contDiff_mStarF u) (symp_hasCompactSupport_mStarF u)
      (((x : ℝ) : Circ) - α₁)]
    refine tsum_congr fun a => ?_
    rw [← fourier_coe_one' a x, mul_assoc, fourier_splice a α₁ x]
  have hQ2 : ∀ α₂ : Circ, (∑' b : ℤ, cw (mStargF P.natDegree u) b * fourier (T := 1) (-b) α₂
        * eeC ((b : ℝ) * y)) = periodize (mStargF P.natDegree u) (((y : ℝ) : Circ) - α₂) := by
    intro α₂
    rw [← symp_cw_tsum_fourier (symp_contDiff_mStargF P.natDegree u)
      (symp_hasCompactSupport_mStargF P.natDegree u) (((y : ℝ) : Circ) - α₂)]
    refine tsum_congr fun b => ?_
    rw [← fourier_coe_one' b y, mul_assoc, fourier_splice b α₂ y]
  -- the product majorant
  have hprod : Summable fun p : ℤ × ℤ =>
      ‖cw (mStarF u) p.1‖ * ‖cw (mStargF P.natDegree u) p.2‖ := by
    simpa [norm_mul] using (symp_summable_cw_mStarF u).mul_norm
      (f := fun a : ℤ => cw (mStarF u) a) (g := fun b : ℤ => cw (mStargF P.natDegree u) b)
      (symp_summable_cw_mStargF P.natDegree u)
  -- the bound on the arithmetic kernel
  have hbound : ∀ p : ℤ × ℤ, ‖arithKerMWin ρ P u l₁ l₂ p.1 p.2‖
      ≤ ((diffFreqs ρ l₁).card : ℝ) * ((diffFreqs ρ l₂).card : ℝ)
        * (‖cw (mStarF u) p.1‖ * ‖cw (mStargF P.natDegree u) p.2‖) := by
    intro p
    have hker : ‖arithKernelEx ρ P (arithQ ρ (max l₁ l₂)) l₁ l₂ p.1 p.2‖
        ≤ ((diffFreqs ρ l₁).card : ℝ) * ((diffFreqs ρ l₂).card : ℝ) := by
      rw [arithKernelEx]
      calc ‖∑ α₁ ∈ diffFreqs ρ l₁, ∑ α₂ ∈ diffFreqs ρ l₂,
              mZ P (arithQ ρ (max l₁ l₂)) α₁ α₂
                * fourier (T := 1) (-p.1) α₁ * fourier (T := 1) (-p.2) α₂‖
          ≤ ∑ α₁ ∈ diffFreqs ρ l₁, ‖∑ α₂ ∈ diffFreqs ρ l₂,
              mZ P (arithQ ρ (max l₁ l₂)) α₁ α₂
                * fourier (T := 1) (-p.1) α₁ * fourier (T := 1) (-p.2) α₂‖ := norm_sum_le _ _
        _ ≤ ∑ _α₁ ∈ diffFreqs ρ l₁, ((diffFreqs ρ l₂).card : ℝ) := by
            refine Finset.sum_le_sum fun α₁ _ => ?_
            calc ‖∑ α₂ ∈ diffFreqs ρ l₂, mZ P (arithQ ρ (max l₁ l₂)) α₁ α₂
                    * fourier (T := 1) (-p.1) α₁ * fourier (T := 1) (-p.2) α₂‖
                ≤ ∑ α₂ ∈ diffFreqs ρ l₂, ‖mZ P (arithQ ρ (max l₁ l₂)) α₁ α₂
                    * fourier (T := 1) (-p.1) α₁ * fourier (T := 1) (-p.2) α₂‖ := norm_sum_le _ _
              _ ≤ ∑ _α₂ ∈ diffFreqs ρ l₂, (1 : ℝ) := by
                  refine Finset.sum_le_sum fun α₂ _ => ?_
                  rw [norm_mul, norm_mul, norm_fourier_one, norm_fourier_one, mul_one, mul_one]
                  exact symp_norm_mZ_le_one P (arithQ ρ (max l₁ l₂)) α₁ α₂
              _ = ((diffFreqs ρ l₂).card : ℝ) := by simp
        _ = ((diffFreqs ρ l₁).card : ℝ) * ((diffFreqs ρ l₂).card : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul]
    rw [arithKerMWin, norm_mul, norm_mul]
    calc ‖arithKernelEx ρ P (arithQ ρ (max l₁ l₂)) l₁ l₂ p.1 p.2‖
          * ‖cw (mStarF u) p.1‖ * ‖cw (mStargF P.natDegree u) p.2‖
        ≤ (((diffFreqs ρ l₁).card : ℝ) * ((diffFreqs ρ l₂).card : ℝ))
            * ‖cw (mStarF u) p.1‖ * ‖cw (mStargF P.natDegree u) p.2‖ := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hker (norm_nonneg _))
            (norm_nonneg _)
      _ = ((diffFreqs ρ l₁).card : ℝ) * ((diffFreqs ρ l₂).card : ℝ)
            * (‖cw (mStarF u) p.1‖ * ‖cw (mStargF P.natDegree u) p.2‖) := by ring
  -- absolute convergence of the two-dimensional symbol series
  have hsummand : Summable fun p : ℤ × ℤ =>
      arithKerMWin ρ P u l₁ l₂ p.1 p.2 * eeC (p.1 * x + p.2 * y) := by
    refine Summable.of_norm_bounded (g := fun p : ℤ × ℤ =>
      ((diffFreqs ρ l₁).card : ℝ) * ((diffFreqs ρ l₂).card : ℝ)
        * (‖cw (mStarF u) p.1‖ * ‖cw (mStargF P.natDegree u) p.2‖)) (hprod.mul_left _)
      (fun p => ?_)
    rw [norm_mul, symp_norm_eeC, mul_one]
    exact hbound p
  rw [symSeq2, ← Summable.tsum_prod hsummand]
  -- unfold the kernel into the finite sum over the exact-height frequencies
  have hswap : ∀ p : ℤ × ℤ, arithKerMWin ρ P u l₁ l₂ p.1 p.2 * eeC (p.1 * x + p.2 * y)
      = ∑ z ∈ (diffFreqs ρ l₁).product (diffFreqs ρ l₂),
          mZ P (arithQ ρ (max l₁ l₂)) z.1 z.2
            * fourier (T := 1) (-p.1) z.1 * fourier (T := 1) (-p.2) z.2
            * cw (mStarF u) p.1 * cw (mStargF P.natDegree u) p.2 * eeC (p.1 * x + p.2 * y) := by
    intro p
    rw [arithKerMWin, arithKernelEx]
    rw [show (∑ α₁ ∈ diffFreqs ρ l₁, ∑ α₂ ∈ diffFreqs ρ l₂,
          mZ P (arithQ ρ (max l₁ l₂)) α₁ α₂ * fourier (T := 1) (-p.1) α₁
            * fourier (T := 1) (-p.2) α₂)
        = ∑ z ∈ (diffFreqs ρ l₁).product (diffFreqs ρ l₂),
          mZ P (arithQ ρ (max l₁ l₂)) z.1 z.2 * fourier (T := 1) (-p.1) z.1
            * fourier (T := 1) (-p.2) z.2 from
      (Finset.sum_product (diffFreqs ρ l₁) (diffFreqs ρ l₂) (fun z : Circ × Circ =>
        mZ P (arithQ ρ (max l₁ l₂)) z.1 z.2 * fourier (T := 1) (-p.1) z.1
          * fourier (T := 1) (-p.2) z.2)).symm]
    simp only [Finset.sum_mul]
  rw [tsum_congr hswap]
  -- the fibre double sum factorises
  have hinner : ∀ α₁ α₂ : Circ,
      (∑' p : ℤ × ℤ, mZ P (arithQ ρ (max l₁ l₂)) α₁ α₂ * fourier (T := 1) (-p.1) α₁
          * fourier (T := 1) (-p.2) α₂ * cw (mStarF u) p.1 * cw (mStargF P.natDegree u) p.2
          * eeC (p.1 * x + p.2 * y))
        = mZ P (arithQ ρ (max l₁ l₂)) α₁ α₂
          * periodize (mStarF u) (((x : ℝ) : Circ) - α₁)
          * periodize (mStargF P.natDegree u) (((y : ℝ) : Circ) - α₂) := by
    intro α₁ α₂
    have hf : Summable fun a : ℤ =>
        ‖cw (mStarF u) a * fourier (T := 1) (-a) α₁ * eeC ((a : ℝ) * x)‖ := by
      refine (symp_summable_cw_mStarF u).congr (fun a => ?_)
      simp only [norm_mul, norm_fourier_one, symp_norm_eeC, mul_one]
    have hg : Summable fun b : ℤ =>
        ‖cw (mStargF P.natDegree u) b * fourier (T := 1) (-b) α₂ * eeC ((b : ℝ) * y)‖ := by
      refine (symp_summable_cw_mStargF P.natDegree u).congr (fun b => ?_)
      simp only [norm_mul, norm_fourier_one, symp_norm_eeC, mul_one]
    have hp_eq : ∀ p : ℤ × ℤ,
        mZ P (arithQ ρ (max l₁ l₂)) α₁ α₂ * fourier (T := 1) (-p.1) α₁
          * fourier (T := 1) (-p.2) α₂ * cw (mStarF u) p.1 * cw (mStargF P.natDegree u) p.2
          * eeC (p.1 * x + p.2 * y)
        = mZ P (arithQ ρ (max l₁ l₂)) α₁ α₂
          * ((cw (mStarF u) p.1 * fourier (T := 1) (-p.1) α₁ * eeC ((p.1 : ℝ) * x))
            * (cw (mStargF P.natDegree u) p.2 * fourier (T := 1) (-p.2) α₂
              * eeC ((p.2 : ℝ) * y))) := by
      intro p
      rw [symp_eeC_add]
      ring
    rw [tsum_congr hp_eq]
    rw [tsum_mul_left]
    rw [← tsum_mul_tsum_of_summable_norm
      (f := fun a : ℤ => cw (mStarF u) a * fourier (T := 1) (-a) α₁ * eeC ((a : ℝ) * x))
      (g := fun b : ℤ => cw (mStargF P.natDegree u) b * fourier (T := 1) (-b) α₂
        * eeC ((b : ℝ) * y)) hf hg]
    rw [hQ1 α₁, hQ2 α₂]
    ring
  -- exchange the finite arithmetic sums with the double `tsum`
  rw [Summable.tsum_finsetSum (s := (diffFreqs ρ l₁).product (diffFreqs ρ l₂))
    (f := fun (z : Circ × Circ) (p : ℤ × ℤ) => mZ P (arithQ ρ (max l₁ l₂)) z.1 z.2
        * fourier (T := 1) (-p.1) z.1 * fourier (T := 1) (-p.2) z.2
        * cw (mStarF u) p.1 * cw (mStargF P.natDegree u) p.2 * eeC (p.1 * x + p.2 * y))]
  · refine (Finset.sum_congr rfl fun z _ => hinner z.1 z.2).trans ?_
    exact Finset.sum_product (diffFreqs ρ l₁) (diffFreqs ρ l₂) (fun z : Circ × Circ =>
      mZ P (arithQ ρ (max l₁ l₂)) z.1 z.2
        * periodize (mStarF u) (((x : ℝ) : Circ) - z.1)
        * periodize (mStargF P.natDegree u) (((y : ℝ) : Circ) - z.2))
  · intro z _
    refine Summable.of_norm_bounded (g := fun p : ℤ × ℤ =>
      ‖mZ P (arithQ ρ (max l₁ l₂)) z.1 z.2‖
        * (‖cw (mStarF u) p.1‖ * ‖cw (mStargF P.natDegree u) p.2‖)) (hprod.mul_left _)
      (fun p => ?_)
    rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_fourier_one, norm_fourier_one,
      symp_norm_eeC]
    exact le_of_eq (by ring)

/-- **The collapse of the §6 model symbol at a general window `u`**: the product of the symbol of
the window-parametrised twisted bilinear multiplier with the symbols of the two modulated
exact-height multipliers collapses onto the single-fibre sum of `m_Ẑ` (the paper's `mod-approx`
alignment), provided the bumps sit inside the window arcs and the arithmetic frequencies are
non-aliasing at the window radii. -/
theorem symMWin_collapse (ρ : ℝ) (P : Polynomial ℤ) (u N l₁ l₂ k₁ k₂ : ℕ) (x y : ℝ)
    (hu : 1 ≤ u) (hd : 1 ≤ P.natDegree)
    (hC2 : max k₁ k₂ + 2 * u + 1 ≤ (Work.Analysis.EndVar.logN N).toNat)
    (hNA₁ : NonAliasing (-(2 * (u : ℤ))) (diffFreqs ρ l₁))
    (hNA₂ : NonAliasing (-((P.natDegree : ℤ) * 2 * (u : ℤ))) (diffFreqs ρ l₂)) (t : ℝ) :
    symSeq2 (arithKerMWin ρ P u l₁ l₂) x y
        * symSeq (tmKer ρ l₁ (varphiNt N k₁ t)) x
        * symSeq (tmKer ρ l₂ (varphitildeNt P P.natDegree N k₂ t)) y
      = ∑ β₁ ∈ diffFreqs ρ l₁, ∑ β₂ ∈ diffFreqs ρ l₂,
          mZ P (arithQ ρ (max l₁ l₂)) β₁ β₂
            * periodize (varphiNt N k₁ t) ((x : ℝ) - β₁)
            * periodize (varphitildeNt P P.natDegree N k₂ t) ((y : ℝ) - β₂) := by
  have hk₁ : k₁ + 2 * u + 1 ≤ (Work.Analysis.EndVar.logN N).toNat := by
    have h := hC2
    have h2 : k₁ ≤ max k₁ k₂ := Nat.le_max_left k₁ k₂
    omega
  have hk₂ : k₂ + 2 * u + 1 ≤ (Work.Analysis.EndVar.logN N).toNat := by
    have h := hC2
    have h2 : k₂ ≤ max k₁ k₂ := Nat.le_max_right k₁ k₂
    omega
  rw [arithKerMWinSymSeq2 ρ P u l₁ l₂ x y,
    symp_symSeq_tmKer_eq ρ l₁ (varphiNt N k₁ t) (integrable_varphiNt N k₁ t)
      (continuous_periodize_of_hasCompactSupport _
        (contDiff_varphiNt N k₁ t).continuous (hasCompactSupport_varphiNt N k₁ t))
      (symp_summable_cw_varphiNt N k₁ t) x,
    symp_symSeq_tmKer_eq ρ l₂ (varphitildeNt P P.natDegree N k₂ t)
      (symp_integrable_varphitildeNt P P.natDegree N k₂ t)
      (continuous_periodize_of_hasCompactSupport _
        (symp_contDiff_varphitildeNt P P.natDegree N k₂ t).continuous
        (symp_hasCompactSupport_varphitildeNt P P.natDegree N k₂ t))
      (symp_summable_cw_varphitildeNt P P.natDegree N k₂ t) y]
  refine symp_sum_collapse (diffFreqs ρ l₁) (diffFreqs ρ l₂)
    (fun a b => mZ P (arithQ ρ (max l₁ l₂)) a b)
    (periodize (mStarF u)) (periodize (varphiNt N k₁ t))
    (periodize (mStargF P.natDegree u)) (periodize (varphitildeNt P P.natDegree N k₂ t))
    (((x : ℝ) : Circ)) (((y : ℝ) : Circ)) ?_ ?_
  · intro α hα β hβ
    exact symp_collapse_pointwise (kΦ := -(2 * (u : ℤ) + 1)) (kΨ := -(2 * (u : ℤ)))
      (k := -(2 * (u : ℤ))) (by omega) le_rfl hNA₁
      (symp_supportedInArc_periodize_varphiNt N k₁ u hu hk₁ t)
      (symp_supportedInArc_periodize (symp_zpow_two_lt_half hu) (symp_mStarF_support' u) le_rfl)
      (fun θ hθ => symp_periodize_mStarF_eq_one u hu hθ) hα hβ (((x : ℝ) : Circ))
  · intro α hα β hβ
    exact symp_collapse_pointwise (kΦ := -((P.natDegree : ℤ) * 2 * (u : ℤ) + 1))
      (kΨ := -((P.natDegree : ℤ) * 2 * (u : ℤ)))
      (k := -((P.natDegree : ℤ) * 2 * (u : ℤ))) (by omega) le_rfl hNA₂
      (symp_supportedInArc_periodize_varphitildeNt P P.natDegree N k₂ u hd hu hk₂ t)
      (symp_supportedInArc_periodize (symp_zpow_two_d_lt_half hd hu)
        (symp_mStargF_support' P.natDegree u) le_rfl)
      (fun θ hθ => symp_periodize_mStargF_eq_one P.natDegree u hd hu hθ)
      hα hβ (((y : ℝ) : Circ))

end Work.KMTPlan.A6

namespace Work.KMTPlan.A6

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger
open Work.KMTAreas.A7
open Work.KMTContract

theorem summable_arithKerMWin (rho : Real) (P : Polynomial Int) (u l1 l2 : Nat) :
    Summable (fun p : Int × Int => ‖Work.KMTAreas.A7.arithKerMWin rho P u l1 l2 p.1 p.2‖) := by
  obtain ⟨C1, _hC1, hdec1⟩ := cw_etaCut_decay (-(2 * (u : Int)))
  obtain ⟨C2, _hC2, hdec2⟩ :=
    cw_etaCut_decay (-((P.natDegree : Int) * 2 * (u : Int)))
  have hdec1' : ∀ j : Int, ‖cw (mStarF u) j‖
      ≤ C1 / (1 + |(j : Real)|) ^ 2 := fun j => by simpa only [mStarF] using hdec1 j
  have hdec2' : ∀ j : Int, ‖cw (mStargF P.natDegree u) j‖
      ≤ C2 / (1 + |(j : Real)|) ^ 2 := fun j => by simpa only [mStargF] using hdec2 j
  have h1 : Summable (fun j : Int => ‖cw (mStarF u) j‖) :=
    kernel_l1_of_decay hdec1'
  have h2 : Summable (fun j : Int => ‖cw (mStargF P.natDegree u) j‖) :=
    kernel_l1_of_decay hdec2'
  have hprod : Summable (fun p : Int × Int =>
      ‖cw (mStarF u) p.1‖
        * ‖cw (mStargF P.natDegree u) p.2‖) :=
    Summable.mul_of_nonneg h1 h2 (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  refine Summable.of_nonneg_of_le (fun p => norm_nonneg _) (fun p => ?_)
    (hprod.mul_left (((diffFreqs rho l1).card : Real) * ((diffFreqs rho l2).card : Real)))
  have hkb := arithKernelEx_norm_le' rho P (arithQ rho (max l1 l2)) l1 l2 p.1 p.2
  rw [Work.KMTAreas.A7.arithKerMWin, norm_mul, norm_mul]
  calc ‖arithKernelEx rho P (arithQ rho (max l1 l2)) l1 l2 p.1 p.2‖
        * ‖cw (mStarF u) p.1‖
        * ‖cw (mStargF P.natDegree u) p.2‖
      ≤ (((diffFreqs rho l1).card : Real) * ((diffFreqs rho l2).card : Real))
        * ‖cw (mStarF u) p.1‖
        * ‖cw (mStargF P.natDegree u) p.2‖ := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hkb (norm_nonneg _))
          (norm_nonneg _)
    _ = (((diffFreqs rho l1).card : Real) * ((diffFreqs rho l2).card : Real))
        * (‖cw (mStarF u) p.1‖
          * ‖cw (mStargF P.natDegree u) p.2‖) := by ring

/-! ## §2.  Fubini: the `coeff2` of a `t`-integral is the `t`-integral of the `coeff2` -/

lemma coeff2IntegralSwapSym (sigma : Real → Real → Real → Complex)
    (hsigma_m : Measurable (fun p : Real × Real × Real => sigma p.1 p.2.1 p.2.2))
    {C : Real} (hsigma_b : ∀ t, t ∈ Set.Icc (1/2 : Real) 1 → ∀ x y : Real, ‖sigma t x y‖ ≤ C)
    (a b : Int) :
    coeff2 (fun x y => ∫ t in (1/2 : Real)..1, sigma t x y) a b
      = ∫ t in (1/2 : Real)..1, coeff2 (sigma t) a b := by
  have hE : ∀ z : Real, ‖eeC z‖ = 1 := fun z => by
    rw [eeC]; simp [Complex.norm_exp]
  unfold coeff2
  simp only [intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_of_le (by norm_num : (1/2:Real) ≤ 1)]
  set mx : Measure Real := volume.restrict (Set.Ioc (0:Real) 1) with hmx
  set mt : Measure Real := volume.restrict (Set.Ioc (1/2:Real) 1) with hmt
  have hrealx : mx.real Set.univ = 1 := by
    show (((volume : Measure Real).restrict (Set.Ioc (0:Real) 1)) Set.univ).toReal = 1
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Ioc]
    simp
  have step1 : ∀ x y : Real, (∫ t, sigma t x y ∂mt) * eeC (-(a : Real) * x - (b : Real) * y)
      = ∫ t, sigma t x y * eeC (-(a : Real) * x - (b : Real) * y) ∂mt :=
    fun x y => (MeasureTheory.integral_mul_const _ _).symm
  simp_rw [step1]
  have hInt1 : ∀ x : Real, Integrable (fun z : Real × Real =>
      sigma z.1 x z.2 * eeC (-(a : Real) * x - (b : Real) * z.2)) (mt.prod mx) := by
    intro x
    refine MeasureTheory.Integrable.of_bound ?_ C ?_
    · have h1 : Measurable (fun z : Real × Real => sigma z.1 x z.2) :=
        hsigma_m.comp (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))
      have h2 : Measurable (fun z : Real × Real =>
          eeC (-(a : Real) * x - (b : Real) * z.2)) := by
        have hc : Continuous (fun z : Real × Real =>
            eeC (-(a : Real) * x - (b : Real) * z.2)) := by
          unfold eeC; fun_prop
        exact hc.measurable
      exact (h1.mul h2).aestronglyMeasurable
    · have hbox : mt.prod mx = (volume.prod volume).restrict
          (Set.Ioc (1/2 : Real) 1 ×ˢ Set.Ioc (0 : Real) 1) := by
        rw [hmt, hmx, Measure.prod_restrict]
      rw [hbox]
      filter_upwards [MeasureTheory.ae_restrict_mem
        (measurableSet_Ioc.prod measurableSet_Ioc)] with z hz
      have ht : z.1 ∈ Set.Icc (1/2 : Real) 1 := ⟨le_of_lt hz.1.1, hz.1.2⟩
      rw [norm_mul, hE]
      simpa using hsigma_b z.1 ht x z.2
  have step2 : ∀ x : Real, (∫ y, ∫ t, sigma t x y * eeC (-(a : Real) * x - (b : Real) * y)
        ∂mt ∂mx)
      = ∫ t, ∫ y, sigma t x y * eeC (-(a : Real) * x - (b : Real) * y) ∂mx ∂mt := by
    intro x
    exact (MeasureTheory.integral_integral_swap 
      (f := fun t y => sigma t x y * eeC (-(a : Real) * x - (b : Real) * y))
      (hInt1 x)).symm
  simp_rw [step2]
  refine MeasureTheory.integral_integral_swap 
    (f := fun x t => ∫ y, sigma t x y * eeC (-(a : Real) * x - (b : Real) * y) ∂mx) ?_
  refine MeasureTheory.Integrable.of_bound ?_ C ?_
  · have hf : Measurable (fun w : (Real × Real) × Real =>
        sigma w.1.2 w.1.1 w.2 * eeC (-(a : Real) * w.1.1 - (b : Real) * w.2)) := by
      have h1 : Measurable (fun w : (Real × Real) × Real => sigma w.1.2 w.1.1 w.2) :=
        hsigma_m.comp ((measurable_snd.comp measurable_fst).prodMk
          ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
      have h2 : Measurable (fun w : (Real × Real) × Real =>
          eeC (-(a : Real) * w.1.1 - (b : Real) * w.2)) := by
        have hc : Continuous (fun w : (Real × Real) × Real =>
            eeC (-(a : Real) * w.1.1 - (b : Real) * w.2)) := by
          unfold eeC; fun_prop
        exact hc.measurable
      exact h1.mul h2
    exact MeasureTheory.AEStronglyMeasurable.integral_prod_right' hf.aestronglyMeasurable
  · have hbox : mx.prod mt = (volume.prod volume).restrict
        (Set.Ioc (0 : Real) 1 ×ˢ Set.Ioc (1/2 : Real) 1) := by
      rw [hmx, hmt, Measure.prod_restrict]
    rw [hbox]
    filter_upwards [MeasureTheory.ae_restrict_mem
      (measurableSet_Ioc.prod measurableSet_Ioc)] with z hz
    have ht : z.2 ∈ Set.Icc (1/2 : Real) 1 := ⟨le_of_lt hz.2.1, hz.2.2⟩
    have hbound : ∀ᵐ y ∂mx, ‖sigma z.2 z.1 y * eeC (-(a : Real) * z.1 - (b : Real) * y)‖ ≤ C := by
      refine Filter.Eventually.of_forall (fun y => ?_)
      rw [norm_mul, hE]
      simpa using hsigma_b z.2 ht z.1 y
    calc ‖∫ y, sigma z.2 z.1 y * eeC (-(a : Real) * z.1 - (b : Real) * y) ∂mx‖
        ≤ C * mx.real Set.univ := MeasureTheory.norm_integral_le_of_norm_le_const hbound
      _ = C := by rw [hrealx, mul_one]

/-- **The coefficient identity for the window-parametrised model symbol**: the `(a,b)`-Fourier
coefficient of the `t`-integral of the product symbol is the `t`-integral of the composed kernel. -/
theorem coeff2_symMWin_eq_integral_kernComp (ρ : ℝ) (P : ℤ[X]) (u N l₁ l₂ k₁ k₂ : ℕ)
    {κ₁ κ₂ : ℝ → ℤ → ℂ}
    (hκ₁ : ∀ t : ℝ, κ₁ t = tmKer ρ l₁ (varphiNt N k₁ t))
    (hκ₂ : ∀ t : ℝ, κ₂ t = tmKer ρ l₂ (varphitildeNt P P.natDegree N k₂ t))
    (hKsum : Summable fun p : ℤ × ℤ =>
      ‖Work.KMTAreas.A7.arithKerMWin ρ P u l₁ l₂ p.1 p.2‖)
    (hκ₁s : ∀ t ∈ Set.Icc (1/2 : ℝ) 1, Summable fun j : ℤ => ‖κ₁ t j‖)
    (hκ₂s : ∀ t ∈ Set.Icc (1/2 : ℝ) 1, Summable fun j : ℤ => ‖κ₂ t j‖)
    (hσm : Measurable (fun q : ℝ × ℝ × ℝ =>
      symSeq2 (Work.KMTAreas.A7.arithKerMWin ρ P u l₁ l₂) q.2.1 q.2.2
        * symSeq (κ₁ q.1) q.2.1 * symSeq (κ₂ q.1) q.2.2))
    {S : ℝ} (hσb : ∀ t, t ∈ Set.Icc (1/2 : ℝ) 1 → ∀ x y : ℝ,
      ‖symSeq2 (Work.KMTAreas.A7.arithKerMWin ρ P u l₁ l₂) x y
        * symSeq (κ₁ t) x * symSeq (κ₂ t) y‖ ≤ S) :
    coeff2 (fun x y : ℝ => ∫ t in (1/2 : ℝ)..1,
        symSeq2 (Work.KMTAreas.A7.arithKerMWin ρ P u l₁ l₂) x y
          * symSeq (κ₁ t) x * symSeq (κ₂ t) y)
      = fun a b : ℤ => ∫ t in (1/2 : ℝ)..1,
          kernComp (Work.KMTAreas.A7.arithKerMWin ρ P u l₁ l₂) (κ₁ t) (κ₂ t) a b := by
  funext a b
  rw [coeff2IntegralSwapSym (fun t x y =>
    symSeq2 (Work.KMTAreas.A7.arithKerMWin ρ P u l₁ l₂) x y
      * symSeq (κ₁ t) x * symSeq (κ₂ t) y) hσm hσb a b]
  refine intervalIntegral.integral_congr (fun t ht => ?_)
  rw [Set.uIcc_of_le (by norm_num : (1/2 : ℝ) ≤ 1)] at ht
  exact SymSeq2_kernComp_coeff _ (κ₁ t) (κ₂ t) hKsum (hκ₁s t ht).of_norm
    (hκ₂s t ht).of_norm a b

end Work.KMTPlan.A6
