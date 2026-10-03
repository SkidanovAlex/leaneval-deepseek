/-
# The operator-level integration-by-parts identity (i) of §6 (area A6): `k₂ = 0`

This module proves `Work.KMTPlan.A6.MdlDecayHighLow`, the *operator-level* form of the
integration-by-parts identity (i) of Krause--Mirek--Tao §6 at the pair `(k₁, 0)` (the `f`-side
scale `k₁` is free, the `g`-side scale is `k₂ = 0`), i.e. the `k`-decay used in Case B
(`max k > max l`) of the assembly `Submission/Work/KMTPlan/A6/LowModelGainEstimate.lean`:

  `mdlPartJ ρ P C₀ a f g l₁ l₂ k₁ 0 0 0
     = (mdlScaleF k₁) mdlIota (sliceW(j₁=-1,j₂=0, w=1, t=1) − sliceW(..., t=1/2))
       − mdlScaleFG P k₁ 0 · WInt(j₁=-1, j₂=1, w = mdlW3)`

where `mdlPartJ` is the `t`-integral of the model tuple with the modulated bumps
`(φ_{N,t}, φ̃_{N,t})` and `mdlSliceW`, `mdlWInt` are the frozen slices / weighted `t`-integrals
with the modified bumps.  The mathematical content is the *bump-level* identity
`Work.KMTPlan.A6.MdlBumpIntegIdentI` transported through the twisted bilinear multiplier
`Btwist`, whose kernel form is the functional-calculus identity
`Work.A7.ModelApproxCore_kernelComp`:
`Tle ρ l ψ` is the convolution with the kernel `i ↦ arithChar ρ l (-i) cw ψ i`
(`Work.KMTKernelArithChar`), so the composite `Btwist(m₁,m₂,Tle ψ ·, Tle χ ·)` is the bilinear
operator with kernel `kernComp (mdlBtwK) κ κ'`, whose `t`-integral against the bumps is the
`(p,z)`-sum of the pointwise products `κ_t z₁ κ̃_t z₂` against the fixed kernel
`mdlBtwK (p₁-z₁) (p₂-z₂) F(x-p₁) G(x-p₂)` (this is `mdlNF` below).  The identity then follows
from the pointwise (in the convolution indices `(z₁,z₂)`) `t`-integral identity of the bumps.

## The auxiliary objects of the proof

* `mdlBtwK` is the kernel of `Btwist` (as a named function, so that `kernComp` can be formed);
* `mdlIWKer ρ l ψ = iwKer ρ l (periodize ψ)` is the convolution kernel of `Tle ρ l ψ`;
* `mdlNF K κ κ' F G x` is the normal form
  `∑'_p ∑'_z (κ z₁ κ' z₂) · K (p₁-z₁) (p₂-z₂) F(x-p₁) G(x-p₂)`
  in which both sides of the identity are written (`mdlNF_static` converts
  `bilinOp (kernComp K κ κ') F G` into it).
-/
import Mathlib
import Submission.Work.A7.ModelApproxCore_Fpiece_convOp
import Submission.Work.KMTAreas.A7.SmallKernMassBasics
import Submission.Work.KMTPlan.A6.MdlNFIntegral
import Submission.Work.KMTPlan.A6.MdlKerVarphiNt
import Submission.Work.KMTPlan.A6.MdlKerVarphiNtj
import Submission.Work.KMTPlan.A6.MdlKerVarphitildeNt
import Submission.Work.KMTPlan.A6.MdlKerVarphitildeNtj
import Submission.Work.KMTPlan.A6.MdlKerIdentHighLow

set_option maxHeartbeats 4000000

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators Interval
open Work.KMTAreas.A7
open Work.Analysis.IonescuWainger

/-! ## Elementary bounds on the inputs of the model tuple -/

/-- `‖z‖ ≤ 1` from `Complex.normSq z ≤ 1`. -/
theorem mdl_norm_le_one_of_normSq_le_one {z : ℂ} (h : Complex.normSq z ≤ 1) : ‖z‖ ≤ 1 := by
  have h2 : ‖z‖ ^ 2 ≤ 1 := by rw [← Complex.normSq_eq_norm_sq]; exact h
  nlinarith [norm_nonneg z]

/-- The kernel `exactKer` of the exact-height projection is in `ℓ¹(ℤ)` (it is a difference of
`kmtKern`s, `Work.KMTKernL1Uniform`). -/
theorem mdl_summable_exactKer_norm (ρ : ℝ) (l : ℕ) (k : ℤ) :
    Summable (fun j : ℤ => ‖exactKer ρ l k j‖) := by
  rcases eq_or_ne l 0 with hl | hl
  · subst hl
    rw [Work.A7.exactKer_zero]
    exact Work.KMTAreas.A5.summable_kmtKern_norm ρ 0 k
  · have hfun : (fun j : ℤ => ‖exactKer ρ l k j‖)
        = fun j : ℤ => ‖Work.KMTAreas.A5.kmtKern ρ l k j
            - Work.KMTAreas.A5.kmtKern ρ (l - 1) k j‖ := by
      funext j
      rw [Work.A7.exactKer_of_ne ρ hl, Pi.sub_apply]
    rw [hfun]
    exact Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => norm_sub_le _ _)
      ((Work.KMTAreas.A5.summable_kmtKern_norm ρ l k).add
        (Work.KMTAreas.A5.summable_kmtKern_norm ρ (l - 1) k))

/-- The exact-height projection of a bounded sequence is bounded. -/
theorem mdl_F_bounded (ρ : ℝ) (u l : ℕ) {f : ℤ → ℂ}
    (hf : ∀ x : ℤ, Complex.normSq (f x) ≤ 1) : ∃ C : ℝ, ∀ y : ℤ, ‖mdlF ρ u l f y‖ ≤ C := by
  have hf1 : ∀ x : ℤ, ‖f x‖ ≤ 1 := fun x => mdl_norm_le_one_of_normSq_le_one (hf x)
  refine ⟨(∑' j : ℤ, ‖exactKer ρ l (-(u : ℤ)) j‖) * max 1 0, fun y => ?_⟩
  have hb : Work.KMTAreas.A5.BoundedZ f := ⟨1, hf1⟩
  rw [mdlF, Work.A7.piExact_eq_convOp ρ l (-(u : ℤ)) hb]
  exact Work.A7.ModelApproxCore_aux.norm_convOp_le (mdl_summable_exactKer_norm ρ l _) hf1 y

/-- The exact-height projection of a bounded sequence is bounded (the `g`-side twist). -/
theorem mdl_G_bounded (ρ : ℝ) (P : Polynomial ℤ) (u l : ℕ) {g : ℤ → ℂ}
    (hg : ∀ x : ℤ, Complex.normSq (g x) ≤ 1) : ∃ C : ℝ, ∀ y : ℤ, ‖mdlG ρ P u l g y‖ ≤ C := by
  have hg1 : ∀ x : ℤ, ‖g x‖ ≤ 1 := fun x => mdl_norm_le_one_of_normSq_le_one (hg x)
  refine ⟨(∑' j : ℤ, ‖exactKer ρ l (-((P.natDegree : ℤ) * (u : ℤ))) j‖) * max 1 0,
    fun y => ?_⟩
  have hb : Work.KMTAreas.A5.BoundedZ g := ⟨1, hg1⟩
  rw [mdlG, Work.A7.piExact_eq_convOp ρ l (-((P.natDegree : ℤ) * (u : ℤ))) hb]
  exact Work.A7.ModelApproxCore_aux.norm_convOp_le (mdl_summable_exactKer_norm ρ l _) hg1 y

/-- The weight `mdlW3 P N t = P'(Nt)/N^{d-1}` of the integration-by-parts identity (i) is
continuous in `t`. -/
theorem mdl_W3_continuous (P : Polynomial ℤ) (N : ℕ) :
    Continuous fun t : ℝ => mdlW3 P N t := by
  unfold mdlW3
  exact Complex.continuous_ofReal.comp
    ((continuous_PderivR_comp P (N : ℝ)).div_const _)

/-- The weight `mdlW3 P N t` is bounded on `[1/2,1]` (it is continuous there and the interval is
compact). -/
theorem mdl_W3_bound (P : Polynomial ℤ) (N : ℕ) :
    ∃ Cw : ℝ, 0 ≤ Cw ∧ ∀ t ∈ Set.Icc (1/2 : ℝ) 1, ‖mdlW3 P N t‖ ≤ Cw := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (1/2 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    (mdl_W3_continuous P N).continuousOn
  exact ⟨max C 0, le_max_right _ _, fun t ht => le_trans (hC t ht) (le_max_left _ _)⟩

/-- The arithmetic symbol `m_Ẑ` is an average of `q` complex numbers of modulus one, hence has
modulus at most one. -/
private lemma mdl_mZ_norm_le_one (P : Polynomial ℤ) (q : ℕ) (hq : 0 < q)
    (α₁ α₂ : Work.Analysis.IonescuWainger.Circle) : ‖mZ P q α₁ α₂‖ ≤ 1 := by
  rw [mZ, norm_mul, norm_inv, Complex.norm_natCast]
  have hsum : ‖∑ n ∈ Finset.range q,
      fourier (T := 1) (n : ℤ) α₁ * fourier (T := 1) (P.eval (n : ℤ)) α₂‖ ≤ (q : ℝ) := by
    calc ‖∑ n ∈ Finset.range q,
          fourier (T := 1) (n : ℤ) α₁ * fourier (T := 1) (P.eval (n : ℤ)) α₂‖
        ≤ ∑ n ∈ Finset.range q,
            ‖fourier (T := 1) (n : ℤ) α₁ * fourier (T := 1) (P.eval (n : ℤ)) α₂‖ :=
          norm_sum_le _ _
      _ = ∑ _n ∈ Finset.range q, (1 : ℝ) := by
          refine Finset.sum_congr rfl (fun n _ => ?_)
          rw [norm_mul, fourier_apply, fourier_apply, Circle.norm_coe, Circle.norm_coe, mul_one]
      _ = (q : ℝ) := by simp
  calc ((q : ℝ))⁻¹ * ‖∑ n ∈ Finset.range q,
        fourier (T := 1) (n : ℤ) α₁ * fourier (T := 1) (P.eval (n : ℤ)) α₂‖
      ≤ ((q : ℝ))⁻¹ * (q : ℝ) :=
        mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr (Nat.cast_nonneg q))
    _ = 1 := by rw [inv_mul_cancel₀ (by exact_mod_cast hq.ne')]

/-- The arithmetic kernel of `Btwist` is bounded by the product of the cardinalities of the two
arithmetic frequency sets. -/
theorem mdl_arithKernel_norm_le (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ : ℕ) (j₁ j₂ : ℤ) :
    ‖arithKernel ρ P (arithQ ρ (max l₁ l₂)) l₁ l₂ j₁ j₂‖
      ≤ ((iwArithFreqs ρ l₁).card : ℝ) * ((iwArithFreqs ρ l₂).card : ℝ) := by
  unfold arithKernel
  calc ‖∑ α₁ ∈ iwArithFreqs ρ l₁, ∑ α₂ ∈ iwArithFreqs ρ l₂,
        mZ P (arithQ ρ (max l₁ l₂)) α₁ α₂ * fourier (T := 1) (-j₁) α₁
          * fourier (T := 1) (-j₂) α₂‖
      ≤ ∑ α₁ ∈ iwArithFreqs ρ l₁, ‖∑ α₂ ∈ iwArithFreqs ρ l₂,
          mZ P (arithQ ρ (max l₁ l₂)) α₁ α₂ * fourier (T := 1) (-j₁) α₁
            * fourier (T := 1) (-j₂) α₂‖ :=
        norm_sum_le _ _
    _ ≤ ∑ α₁ ∈ iwArithFreqs ρ l₁, ∑ α₂ ∈ iwArithFreqs ρ l₂,
          ‖mZ P (arithQ ρ (max l₁ l₂)) α₁ α₂ * fourier (T := 1) (-j₁) α₁
            * fourier (T := 1) (-j₂) α₂‖ :=
        Finset.sum_le_sum (fun _ _ => norm_sum_le _ _)
    _ ≤ ∑ _α₁ ∈ iwArithFreqs ρ l₁, ∑ _α₂ ∈ iwArithFreqs ρ l₂, (1 : ℝ) := by
        refine Finset.sum_le_sum (fun α₁ _ => Finset.sum_le_sum (fun α₂ _ => ?_))
        rw [norm_mul, norm_mul, fourier_apply, fourier_apply, Circle.norm_coe, Circle.norm_coe,
          mul_one, mul_one]
        exact mdl_mZ_norm_le_one P (arithQ ρ (max l₁ l₂)) (arithQ_pos ρ _) α₁ α₂
    _ = ((iwArithFreqs ρ l₁).card : ℝ) * ((iwArithFreqs ρ l₂).card : ℝ) := by
        simp [Finset.sum_const, nsmul_eq_mul]

/-- The kernel of `Btwist` is in `ℓ¹(ℤ²)` as soon as the two symbols have summable `cw`
coefficients. -/
theorem mdl_summable_mdlBtwK (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ : ℕ) (m₁ m₂ : ℝ → ℂ)
    (h₁ : Summable fun j : ℤ => ‖cw m₁ j‖) (h₂ : Summable fun j : ℤ => ‖cw m₂ j‖) :
    Summable fun p : ℤ × ℤ => ‖mdlBtwK ρ P l₁ l₂ m₁ m₂ p.1 p.2‖ := by
  have hbound : ∀ p : ℤ × ℤ,
      ‖mdlBtwK ρ P l₁ l₂ m₁ m₂ p.1 p.2‖
        ≤ ((iwArithFreqs ρ l₁).card : ℝ) * ((iwArithFreqs ρ l₂).card : ℝ)
            * ‖cw m₁ p.1‖ * ‖cw m₂ p.2‖ := by
    intro p
    rw [mdlBtwK, twKer, norm_mul, norm_mul]
    exact mul_le_mul (mul_le_mul (mdl_arithKernel_norm_le ρ P l₁ l₂ p.1 p.2) le_rfl
      (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))) le_rfl
      (norm_nonneg _) (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
        (norm_nonneg _))
  refine Summable.of_nonneg_of_le (fun p => norm_nonneg _) hbound ?_
  have h₂' : Summable fun p : ℤ × ℤ => ‖cw m₁ p.1‖ * ‖cw m₂ p.2‖ :=
    Summable.mul_of_nonneg h₁ h₂ (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  exact (h₂'.mul_left (((iwArithFreqs ρ l₁).card : ℝ) * ((iwArithFreqs ρ l₂).card : ℝ))).congr
    (fun p => by ring)

/-- Linearity of a flat series against a fixed family `D`, when the coefficients are related by
`L z = c₁ A z - c₁ B z - c₂ C z`. -/
theorem mdl_tsum_linear (D : (ℤ × ℤ) × (ℤ × ℤ) → ℂ) (A B C L : ℤ × ℤ → ℂ) (c₁ c₂ : ℂ)
    (hA : Summable fun q : (ℤ × ℤ) × (ℤ × ℤ) => A q.2 * D q)
    (hB : Summable fun q : (ℤ × ℤ) × (ℤ × ℤ) => B q.2 * D q)
    (hC : Summable fun q : (ℤ × ℤ) × (ℤ × ℤ) => C q.2 * D q)
    (hL : Summable fun q : (ℤ × ℤ) × (ℤ × ℤ) => L q.2 * D q)
    (hcoef : ∀ z : ℤ × ℤ, L z = c₁ * A z - c₁ * B z - c₂ * C z) :
    (∑' q : (ℤ × ℤ) × (ℤ × ℤ), L q.2 * D q)
      = c₁ * ((∑' q, A q.2 * D q) - (∑' q, B q.2 * D q)) - c₂ * (∑' q, C q.2 * D q) := by
  have h1 : (∑' q : (ℤ × ℤ) × (ℤ × ℤ), L q.2 * D q)
      = ∑' q, ((c₁ * (A q.2 * D q) - c₁ * (B q.2 * D q)) - c₂ * (C q.2 * D q)) := by
    refine tsum_congr (fun q => ?_)
    rw [hcoef q.2]
    ring
  have h2 : (∑' q : (ℤ × ℤ) × (ℤ × ℤ),
        ((c₁ * (A q.2 * D q) - c₁ * (B q.2 * D q)) - c₂ * (C q.2 * D q)))
      = (∑' q, (c₁ * (A q.2 * D q) - c₁ * (B q.2 * D q))) - ∑' q, c₂ * (C q.2 * D q) :=
    Summable.tsum_sub ((hA.mul_left c₁).sub (hB.mul_left c₁)) (hC.mul_left c₂)
  have h3 : (∑' q : (ℤ × ℤ) × (ℤ × ℤ), (c₁ * (A q.2 * D q) - c₁ * (B q.2 * D q)))
      = c₁ * (∑' q, A q.2 * D q) - c₁ * (∑' q, B q.2 * D q) := by
    rw [Summable.tsum_sub (hA.mul_left c₁) (hB.mul_left c₁),
      Summable.tsum_mul_left c₁ hA, Summable.tsum_mul_left c₁ hB]
  have h4 : (∑' q : (ℤ × ℤ) × (ℤ × ℤ), c₂ * (C q.2 * D q)) = c₂ * ∑' q, C q.2 * D q :=
    Summable.tsum_mul_left c₂ hC
  calc (∑' q : (ℤ × ℤ) × (ℤ × ℤ), L q.2 * D q)
      = ∑' q, ((c₁ * (A q.2 * D q) - c₁ * (B q.2 * D q)) - c₂ * (C q.2 * D q)) := h1
    _ = (∑' q, (c₁ * (A q.2 * D q) - c₁ * (B q.2 * D q))) - ∑' q, c₂ * (C q.2 * D q) := h2
    _ = (c₁ * (∑' q, A q.2 * D q) - c₁ * (∑' q, B q.2 * D q))
          - c₂ * (∑' q, C q.2 * D q) := by rw [h3, h4]
    _ = c₁ * ((∑' q, A q.2 * D q) - (∑' q, B q.2 * D q)) - c₂ * (∑' q, C q.2 * D q) := by
        ring

/-! ## The core identity (the main argument) -/

open scoped Classical in
/-- **The operator-level integration-by-parts identity (i) in the `Btwist` vocabulary.**  This is
the core of `MdlDecayHighLow`: the `t`-integral of the model tuple with the modulated bumps
`(φ_{N,t}, φ̃_{N,t})` equals the boundary terms of the modified bumps minus the weighted `t`-integral
of the modified pair.  The four majorants `a₁, …, a₄` and the weight bound `Cw` are the inputs that
make every series and integral in sight absolutely convergent. -/
theorem mdlDecayHighLow_core
    (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ N k₁ : ℕ) (hk₁ : 1 ≤ k₁) (hN : 1 ≤ N) (u : ℕ) (F G : ℤ → ℂ)
    (CF CG Cw : ℝ) (hF : ∀ y : ℤ, ‖F y‖ ≤ CF) (hG : ∀ y : ℤ, ‖G y‖ ≤ CG)
    (hCw0 : 0 ≤ Cw) (hw : ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, ‖mdlW3 P N t‖ ≤ Cw)
    (hwm : AEStronglyMeasurable (fun t : ℝ => mdlW3 P N t) (volume : MeasureTheory.Measure ℝ))
    (hK : Summable fun p : ℤ × ℤ =>
      ‖mdlBtwK ρ P l₁ l₂ (mStarF u) (mStargF P.natDegree u) p.1 p.2‖)
    (a₁ a₂ a₃ a₄ : ℤ → ℝ) (ha₁ : Summable a₁) (ha₂ : Summable a₂) (ha₃ : Summable a₃)
    (ha₄ : Summable a₄)
    (hb₁ : ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, ∀ i : ℤ, ‖mdlIWKer ρ l₁ (varphiNt N k₁ t) i‖ ≤ a₁ i)
    (hb₂ : ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, ∀ i : ℤ,
      ‖mdlIWKer ρ l₂ (varphitildeNt P P.natDegree N 0 t) i‖ ≤ a₂ i)
    (hb₃ : ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, ∀ i : ℤ,
      ‖mdlIWKer ρ l₁ (varphiNtj N k₁ (-1) t) i‖ ≤ a₃ i)
    (hb₄ : ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, ∀ i : ℤ,
      ‖mdlIWKer ρ l₂ (varphitildeNtj P N 0 1 t) i‖ ≤ a₄ i)
    (hm₁ : ∀ i : ℤ, AEStronglyMeasurable (fun t : ℝ => mdlIWKer ρ l₁ (varphiNt N k₁ t) i) volume)
    (hm₂ : ∀ i : ℤ, AEStronglyMeasurable
      (fun t : ℝ => mdlIWKer ρ l₂ (varphitildeNt P P.natDegree N 0 t) i) volume)
    (hm₃ : ∀ i : ℤ, AEStronglyMeasurable
      (fun t : ℝ => mdlIWKer ρ l₁ (varphiNtj N k₁ (-1) t) i) volume)
    (hm₄ : ∀ i : ℤ, AEStronglyMeasurable
      (fun t : ℝ => mdlIWKer ρ l₂ (varphitildeNtj P N 0 1 t) i) volume)
    (x : ℤ) :
    (∫ t in (1 / 2 : ℝ)..1,
        Btwist ρ P l₁ l₂ (mStarF u) (mStargF P.natDegree u)
          (Tle ρ l₁ (varphiNt N k₁ t) F) (Tle ρ l₂ (varphitildeNt P P.natDegree N 0 t) G) x)
      = (mdlScaleF k₁ : ℂ) * mdlIota
          * (Btwist ρ P l₁ l₂ (mStarF u) (mStargF P.natDegree u)
                (Tle ρ l₁ (varphiNtj N k₁ (-1) 1) F)
                (Tle ρ l₂ (varphitildeNtj P N 0 0 1) G) x
              - Btwist ρ P l₁ l₂ (mStarF u) (mStargF P.natDegree u)
                (Tle ρ l₁ (varphiNtj N k₁ (-1) (1 / 2)) F)
                (Tle ρ l₂ (varphitildeNtj P N 0 0 (1 / 2)) G) x)
        - (mdlScaleFG P k₁ 0 : ℂ)
            * (∫ t in (1 / 2 : ℝ)..1, mdlW3 P N t
                * Btwist ρ P l₁ l₂ (mStarF u) (mStargF P.natDegree u)
                    (Tle ρ l₁ (varphiNtj N k₁ (-1) t) F)
                    (Tle ρ l₂ (varphitildeNtj P N 0 1 t) G) x) := by
  classical
  -- nonnegativity of the four majorants
  have ha₁0 : ∀ i : ℤ, 0 ≤ a₁ i := fun i => le_trans (norm_nonneg _) (hb₁ 1 (by norm_num) i)
  have ha₂0 : ∀ i : ℤ, 0 ≤ a₂ i := fun i => le_trans (norm_nonneg _) (hb₂ 1 (by norm_num) i)
  have ha₃0 : ∀ i : ℤ, 0 ≤ a₃ i := fun i => le_trans (norm_nonneg _) (hb₃ 1 (by norm_num) i)
  have ha₄0 : ∀ i : ℤ, 0 ≤ a₄ i := fun i => le_trans (norm_nonneg _) (hb₄ 1 (by norm_num) i)
  -- (1) the pointwise normal form of the integrand
  have hpoint : ∀ t ∈ Set.Icc (1/2:ℝ) 1,
      Btwist ρ P l₁ l₂ (mStarF u) (mStargF P.natDegree u)
        (Tle ρ l₁ (varphiNt N k₁ t) F) (Tle ρ l₂ (varphitildeNt P P.natDegree N 0 t) G) x
      = mdlNF (mdlBtwK ρ P l₁ l₂ (mStarF u) (mStargF P.natDegree u))
          (fun i => mdlIWKer ρ l₁ (varphiNt N k₁ t) i)
          (fun i => mdlIWKer ρ l₂ (varphitildeNt P P.natDegree N 0 t) i) F G x := by
    intro t ht
    have hs : Summable fun i : ℤ => ‖mdlIWKer ρ l₁ (varphiNt N k₁ t) i‖ :=
      Summable.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => hb₁ t ht i) ha₁
    have hs' : Summable fun i : ℤ => ‖mdlIWKer ρ l₂ (varphitildeNt P P.natDegree N 0 t) i‖ :=
      Summable.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => hb₂ t ht i) ha₂
    rw [Btwist_eq_bilinOp, Tle_eq_convOp, Tle_eq_convOp,
      ← Work.A7.ModelApproxCore_kernelComp
        (K := mdlBtwK ρ P l₁ l₂ (mStarF u) (mStargF P.natDegree u))
        (κ := fun i => mdlIWKer ρ l₁ (varphiNt N k₁ t) i)
        (κ' := fun i => mdlIWKer ρ l₂ (varphitildeNt P P.natDegree N 0 t) i) hK hs hs' hF hG]
    exact bilinOp_kernComp_eq_mdlNF hK hs hs' hF hG x
  -- (2) the Fubini swap of the `t`-integral with the two series
  have hFub := MdlNFIntegral (K := mdlBtwK ρ P l₁ l₂ (mStarF u) (mStargF P.natDegree u))
      (F := F) (G := G) hF hG hK (w := fun _ => (1:ℂ)) (Cw := 1) (by intro t ht; simp)
      measurable_const.aestronglyMeasurable
      (fun t => fun i => mdlIWKer ρ l₁ (varphiNt N k₁ t) i)
      (fun t => fun i => mdlIWKer ρ l₂ (varphitildeNt P P.natDegree N 0 t) i) a₁ a₂ ha₁ ha₂
      hb₁ hb₂ hm₁ hm₂ x
  have hBtw : (∫ t in (1/2:ℝ)..1,
        Btwist ρ P l₁ l₂ (mStarF u) (mStargF P.natDegree u)
          (Tle ρ l₁ (varphiNt N k₁ t) F) (Tle ρ l₂ (varphitildeNt P P.natDegree N 0 t) G) x)
      = ∫ t in (1/2:ℝ)..1, (fun _ => (1:ℂ)) t
          * mdlNF (mdlBtwK ρ P l₁ l₂ (mStarF u) (mStargF P.natDegree u))
              (fun i => mdlIWKer ρ l₁ (varphiNt N k₁ t) i)
              (fun i => mdlIWKer ρ l₂ (varphitildeNt P P.natDegree N 0 t) i) F G x := by
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    rw [Set.uIcc_of_le (by norm_num : (1/2:ℝ) ≤ 1)] at ht
    rw [hpoint t ht, one_mul]
  have hstep2 : (∫ t in (1/2:ℝ)..1,
        Btwist ρ P l₁ l₂ (mStarF u) (mStargF P.natDegree u)
          (Tle ρ l₁ (varphiNt N k₁ t) F) (Tle ρ l₂ (varphitildeNt P P.natDegree N 0 t) G) x)
      = ∑' p : ℤ × ℤ, ∑' z : ℤ × ℤ,
          mdlCoeff (fun _ => (1:ℂ)) (fun t => fun i => mdlIWKer ρ l₁ (varphiNt N k₁ t) i)
            (fun t => fun i => mdlIWKer ρ l₂ (varphitildeNt P P.natDegree N 0 t) i) z
            * mdlKFG (mdlBtwK ρ P l₁ l₂ (mStarF u) (mStargF P.natDegree u)) F G x p z := by
    rw [hBtw]
    exact hFub
  -- (3) the coefficient identity, from the bump-level identity (i)
  have hcoef : ∀ z : ℤ × ℤ,
      mdlCoeff (fun _ => (1:ℂ)) (fun t => fun i => mdlIWKer ρ l₁ (varphiNt N k₁ t) i)
          (fun t => fun i => mdlIWKer ρ l₂ (varphitildeNt P P.natDegree N 0 t) i) z
        = (mdlScaleF k₁ : ℂ) * mdlIota
            * ((mdlIWKer ρ l₁ (varphiNtj N k₁ (-1) 1) z.1
                  * mdlIWKer ρ l₂ (varphitildeNtj P N 0 0 1) z.2)
                - (mdlIWKer ρ l₁ (varphiNtj N k₁ (-1) (1/2)) z.1
                  * mdlIWKer ρ l₂ (varphitildeNtj P N 0 0 (1/2)) z.2))
          - (mdlScaleFG P k₁ 0 : ℂ)
              * mdlCoeff (fun t => mdlW3 P N t)
                  (fun t => fun i => mdlIWKer ρ l₁ (varphiNtj N k₁ (-1) t) i)
                  (fun t => fun i => mdlIWKer ρ l₂ (varphitildeNtj P N 0 1 t) i) z := by
    intro z
    have h := MdlKerIdentHighLow ρ P l₁ l₂ N k₁ hk₁ hN z.1 z.2
    simpa only [mdlIWKer_eq_TleKer, mdlCoeff, one_mul] using h
  -- (4) the coefficient families and the summability of the four `(p,z)`-families
  set K : ℤ → ℤ → ℂ := mdlBtwK ρ P l₁ l₂ (mStarF u) (mStargF P.natDegree u) with hKdef
  set D : (ℤ × ℤ) × (ℤ × ℤ) → ℂ := fun q => mdlKFG K F G x q.1 q.2 with hD
  set cA : ℤ × ℤ → ℂ := fun z => mdlIWKer ρ l₁ (varphiNtj N k₁ (-1) 1) z.1
      * mdlIWKer ρ l₂ (varphitildeNtj P N 0 0 1) z.2 with hcA
  set cB : ℤ × ℤ → ℂ := fun z => mdlIWKer ρ l₁ (varphiNtj N k₁ (-1) (1/2)) z.1
      * mdlIWKer ρ l₂ (varphitildeNtj P N 0 0 (1/2)) z.2 with hcB
  set cC : ℤ × ℤ → ℂ := mdlCoeff (fun t => mdlW3 P N t)
      (fun t => fun i => mdlIWKer ρ l₁ (varphiNtj N k₁ (-1) t) i)
      (fun t => fun i => mdlIWKer ρ l₂ (varphitildeNtj P N 0 1 t) i) with hcC
  set cL : ℤ × ℤ → ℂ := mdlCoeff (fun _ => (1:ℂ))
      (fun t => fun i => mdlIWKer ρ l₁ (varphiNt N k₁ t) i)
      (fun t => fun i => mdlIWKer ρ l₂ (varphitildeNt P P.natDegree N 0 t) i) with hcL
  have hK' : Summable fun p : ℤ × ℤ => ‖K p.1 p.2‖ := by rw [hKdef]; exact hK
  have hsA : Summable fun q : (ℤ × ℤ) × (ℤ × ℤ) => cA q.2 * D q := by
    refine Summable.of_norm_bounded (mdl_conv_majorant_summable hK' ha₃ ha₂ ha₃0 ha₂0 CF CG)
      (fun q => ?_)
    have h1 := mdl_summand_norm_le (K := K) (F := F) (G := G) hF hG
      (κ := fun i => mdlIWKer ρ l₁ (varphiNtj N k₁ (-1) 1) i)
      (κ' := fun i => mdlIWKer ρ l₂ (varphitildeNtj P N 0 0 1) i)
      (a := a₃) (a' := a₂) ha₃0 ha₂0
      (fun i => hb₃ 1 (by norm_num) i)
      (fun i => by simpa only [varphitildeNtj_zero P N 0 1] using hb₂ 1 (by norm_num) i)
      x q.1 q.2
    simpa only [hcA, hD] using h1
  have hsB : Summable fun q : (ℤ × ℤ) × (ℤ × ℤ) => cB q.2 * D q := by
    refine Summable.of_norm_bounded (mdl_conv_majorant_summable hK' ha₃ ha₂ ha₃0 ha₂0 CF CG)
      (fun q => ?_)
    have h1 := mdl_summand_norm_le (K := K) (F := F) (G := G) hF hG
      (κ := fun i => mdlIWKer ρ l₁ (varphiNtj N k₁ (-1) (1/2)) i)
      (κ' := fun i => mdlIWKer ρ l₂ (varphitildeNtj P N 0 0 (1/2)) i)
      (a := a₃) (a' := a₂) ha₃0 ha₂0
      (fun i => hb₃ (1/2) (by norm_num) i)
      (fun i => by simpa only [varphitildeNtj_zero P N 0 (1/2)] using hb₂ (1/2) (by norm_num) i)
      x q.1 q.2
    simpa only [hcB, hD] using h1
  have hsC : Summable fun q : (ℤ × ℤ) × (ℤ × ℤ) => cC q.2 * D q := by
    refine Summable.of_norm_bounded
      (mdl_conv_majorant_summable hK' (ha₃.mul_left Cw) ha₄
        (fun i => mul_nonneg hCw0 (ha₃0 i)) ha₄0 CF CG) (fun q => ?_)
    have h1 := mdl_coeff_intervalIntegral_bound (w := fun t => mdlW3 P N t) (Cw := Cw) hw hCw0
      ha₃0 ha₄0 hb₃ hb₄ q.2
    have h2 : ‖mdlKFG K F G x q.1 q.2‖
        ≤ ‖K (q.1.1 - q.2.1) (q.1.2 - q.2.2)‖ * CF * CG := by
      rw [mdlKFG, norm_mul, norm_mul]
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hF _) (norm_nonneg _)) (hG _)
        (norm_nonneg _) (mul_nonneg (norm_nonneg _) (le_trans (norm_nonneg _) (hF 0)))
    rw [hcC, hD, norm_mul]
    calc ‖mdlCoeff (fun t => mdlW3 P N t)
            (fun t => fun i => mdlIWKer ρ l₁ (varphiNtj N k₁ (-1) t) i)
            (fun t => fun i => mdlIWKer ρ l₂ (varphitildeNtj P N 0 1 t) i) q.2‖
          * ‖mdlKFG K F G x q.1 q.2‖
        ≤ (Cw * (a₃ q.2.1 * a₄ q.2.2))
            * (‖K (q.1.1 - q.2.1) (q.1.2 - q.2.2)‖ * CF * CG) :=
          mul_le_mul h1 h2 (norm_nonneg _) (mul_nonneg hCw0 (mul_nonneg (ha₃0 _) (ha₄0 _)))
      _ = mdlMajorant (fun i => Cw * a₃ i) a₄ K CF CG q := by
          rw [mdlMajorant]; ring
  have hsL : Summable fun q : (ℤ × ℤ) × (ℤ × ℤ) => cL q.2 * D q := by
    refine Summable.of_norm_bounded (mdl_conv_majorant_summable hK' ha₁ ha₂ ha₁0 ha₂0 CF CG)
      (fun q => ?_)
    have h1 := mdl_coeff_intervalIntegral_bound (w := fun _ => (1:ℂ)) (Cw := 1) (by intro t ht; simp)
      zero_le_one ha₁0 ha₂0 hb₁ hb₂ q.2
    have h2 : ‖mdlKFG K F G x q.1 q.2‖
        ≤ ‖K (q.1.1 - q.2.1) (q.1.2 - q.2.2)‖ * CF * CG := by
      rw [mdlKFG, norm_mul, norm_mul]
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hF _) (norm_nonneg _)) (hG _)
        (norm_nonneg _) (mul_nonneg (norm_nonneg _) (le_trans (norm_nonneg _) (hF 0)))
    rw [hcL, hD, norm_mul]
    calc ‖mdlCoeff (fun _ => (1:ℂ))
            (fun t => fun i => mdlIWKer ρ l₁ (varphiNt N k₁ t) i)
            (fun t => fun i => mdlIWKer ρ l₂ (varphitildeNt P P.natDegree N 0 t) i) q.2‖
          * ‖mdlKFG K F G x q.1 q.2‖
        ≤ (1 * (a₁ q.2.1 * a₂ q.2.2))
            * (‖K (q.1.1 - q.2.1) (q.1.2 - q.2.2)‖ * CF * CG) :=
          mul_le_mul h1 h2 (norm_nonneg _) (mul_nonneg zero_le_one (mul_nonneg (ha₁0 _) (ha₂0 _)))
      _ = mdlMajorant a₁ a₂ K CF CG q := by
          rw [mdlMajorant]; ring
  -- (5) both sides in the flat `(p,z)`-sum form
  have hLflat : (∫ t in (1/2:ℝ)..1,
        Btwist ρ P l₁ l₂ (mStarF u) (mStargF P.natDegree u)
          (Tle ρ l₁ (varphiNt N k₁ t) F) (Tle ρ l₂ (varphitildeNt P P.natDegree N 0 t) G) x)
      = ∑' q : (ℤ × ℤ) × (ℤ × ℤ), cL q.2 * D q := by
    rw [hstep2, hcL, hD]
    exact (hsL.tsum_prod).symm
  have hslice1 : Btwist ρ P l₁ l₂ (mStarF u) (mStargF P.natDegree u)
        (Tle ρ l₁ (varphiNtj N k₁ (-1) 1) F) (Tle ρ l₂ (varphitildeNtj P N 0 0 1) G) x
      = ∑' q : (ℤ × ℤ) × (ℤ × ℤ), cA q.2 * D q := by
    have hs1 : Summable fun i : ℤ => ‖mdlIWKer ρ l₁ (varphiNtj N k₁ (-1) 1) i‖ :=
      Summable.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => hb₃ 1 (by norm_num) i) ha₃
    have hs2 : Summable fun i : ℤ => ‖mdlIWKer ρ l₂ (varphitildeNtj P N 0 0 1) i‖ := by
      refine Summable.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => ?_) ha₂
      simpa only [varphitildeNtj_zero P N 0 1] using hb₂ 1 (by norm_num) i
    have h1 : Btwist ρ P l₁ l₂ (mStarF u) (mStargF P.natDegree u)
        (Tle ρ l₁ (varphiNtj N k₁ (-1) 1) F) (Tle ρ l₂ (varphitildeNtj P N 0 0 1) G) x
        = mdlNF K (fun i => mdlIWKer ρ l₁ (varphiNtj N k₁ (-1) 1) i)
            (fun i => mdlIWKer ρ l₂ (varphitildeNtj P N 0 0 1) i) F G x := by
      rw [hKdef, Btwist_eq_bilinOp, Tle_eq_convOp, Tle_eq_convOp,
        ← Work.A7.ModelApproxCore_kernelComp (K := K)
          (κ := fun i => mdlIWKer ρ l₁ (varphiNtj N k₁ (-1) 1) i)
          (κ' := fun i => mdlIWKer ρ l₂ (varphitildeNtj P N 0 0 1) i) hK' hs1 hs2 hF hG]
      exact bilinOp_kernComp_eq_mdlNF hK' hs1 hs2 hF hG x
    rw [h1, mdlNF_eq_tsum_prod hF hG hK' hs1 hs2 x, hcA, hD]
  have hslice2 : Btwist ρ P l₁ l₂ (mStarF u) (mStargF P.natDegree u)
        (Tle ρ l₁ (varphiNtj N k₁ (-1) (1/2)) F) (Tle ρ l₂ (varphitildeNtj P N 0 0 (1/2)) G) x
      = ∑' q : (ℤ × ℤ) × (ℤ × ℤ), cB q.2 * D q := by
    have hs1 : Summable fun i : ℤ => ‖mdlIWKer ρ l₁ (varphiNtj N k₁ (-1) (1/2)) i‖ :=
      Summable.of_nonneg_of_le (fun i => norm_nonneg _)
        (fun i => hb₃ (1/2) (by norm_num) i) ha₃
    have hs2 : Summable fun i : ℤ => ‖mdlIWKer ρ l₂ (varphitildeNtj P N 0 0 (1/2)) i‖ := by
      refine Summable.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => ?_) ha₂
      simpa only [varphitildeNtj_zero P N 0 (1/2)] using hb₂ (1/2) (by norm_num) i
    have h1 : Btwist ρ P l₁ l₂ (mStarF u) (mStargF P.natDegree u)
        (Tle ρ l₁ (varphiNtj N k₁ (-1) (1/2)) F) (Tle ρ l₂ (varphitildeNtj P N 0 0 (1/2)) G) x
        = mdlNF K (fun i => mdlIWKer ρ l₁ (varphiNtj N k₁ (-1) (1/2)) i)
            (fun i => mdlIWKer ρ l₂ (varphitildeNtj P N 0 0 (1/2)) i) F G x := by
      rw [hKdef, Btwist_eq_bilinOp, Tle_eq_convOp, Tle_eq_convOp,
        ← Work.A7.ModelApproxCore_kernelComp (K := K)
          (κ := fun i => mdlIWKer ρ l₁ (varphiNtj N k₁ (-1) (1/2)) i)
          (κ' := fun i => mdlIWKer ρ l₂ (varphitildeNtj P N 0 0 (1/2)) i) hK' hs1 hs2 hF hG]
      exact bilinOp_kernComp_eq_mdlNF hK' hs1 hs2 hF hG x
    rw [h1, mdlNF_eq_tsum_prod hF hG hK' hs1 hs2 x, hcB, hD]
  have hmid : (∫ t in (1/2:ℝ)..1, mdlW3 P N t
        * Btwist ρ P l₁ l₂ (mStarF u) (mStargF P.natDegree u)
            (Tle ρ l₁ (varphiNtj N k₁ (-1) t) F) (Tle ρ l₂ (varphitildeNtj P N 0 1 t) G) x)
      = ∑' q : (ℤ × ℤ) × (ℤ × ℤ), cC q.2 * D q := by
    have hFub2 := MdlNFIntegral (K := K) (F := F) (G := G) hF hG hK'
      (w := fun t => mdlW3 P N t) (Cw := Cw) hw hwm
      (fun t => fun i => mdlIWKer ρ l₁ (varphiNtj N k₁ (-1) t) i)
      (fun t => fun i => mdlIWKer ρ l₂ (varphitildeNtj P N 0 1 t) i) a₃ a₄ ha₃ ha₄
      hb₃ hb₄ hm₃ hm₄ x
    have h1 : ∀ t ∈ Set.Icc (1/2:ℝ) 1,
        Btwist ρ P l₁ l₂ (mStarF u) (mStargF P.natDegree u)
          (Tle ρ l₁ (varphiNtj N k₁ (-1) t) F) (Tle ρ l₂ (varphitildeNtj P N 0 1 t) G) x
        = mdlNF K (fun i => mdlIWKer ρ l₁ (varphiNtj N k₁ (-1) t) i)
            (fun i => mdlIWKer ρ l₂ (varphitildeNtj P N 0 1 t) i) F G x := by
      intro t ht
      have hs1 : Summable fun i : ℤ => ‖mdlIWKer ρ l₁ (varphiNtj N k₁ (-1) t) i‖ :=
        Summable.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => hb₃ t ht i) ha₃
      have hs2 : Summable fun i : ℤ => ‖mdlIWKer ρ l₂ (varphitildeNtj P N 0 1 t) i‖ :=
        Summable.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => hb₄ t ht i) ha₄
      rw [Btwist_eq_bilinOp, Tle_eq_convOp, Tle_eq_convOp,
        ← Work.A7.ModelApproxCore_kernelComp (K := K)
          (κ := fun i => mdlIWKer ρ l₁ (varphiNtj N k₁ (-1) t) i)
          (κ' := fun i => mdlIWKer ρ l₂ (varphitildeNtj P N 0 1 t) i) hK' hs1 hs2 hF hG]
      exact bilinOp_kernComp_eq_mdlNF hK' hs1 hs2 hF hG x
    have hcongr : (∫ t in (1/2:ℝ)..1, mdlW3 P N t
          * Btwist ρ P l₁ l₂ (mStarF u) (mStargF P.natDegree u)
              (Tle ρ l₁ (varphiNtj N k₁ (-1) t) F) (Tle ρ l₂ (varphitildeNtj P N 0 1 t) G) x)
        = ∫ t in (1/2:ℝ)..1, mdlW3 P N t
            * mdlNF K (fun i => mdlIWKer ρ l₁ (varphiNtj N k₁ (-1) t) i)
                (fun i => mdlIWKer ρ l₂ (varphitildeNtj P N 0 1 t) i) F G x := by
      refine intervalIntegral.integral_congr (fun t ht => ?_)
      rw [Set.uIcc_of_le (by norm_num : (1/2:ℝ) ≤ 1)] at ht
      rw [h1 t ht]
    rw [hcongr, hFub2, hcC, hD]
    exact (hsC.tsum_prod).symm
  -- (6) the endgame: rewrite the coefficients and use the linearity of the series
  rw [hLflat, hslice1, hslice2, hmid]
  exact mdl_tsum_linear D cA cB cC cL ((mdlScaleF k₁ : ℂ) * mdlIota) (mdlScaleFG P k₁ 0 : ℂ)
    hsA hsB hsC hsL (fun z => by rw [hcoef z]; ring)

theorem MdlDecayHighLow (ρ : ℝ) (P : Polynomial ℤ) (C₀ : ℕ) (a : ℕ → NNReal) (f g : ℤ → ℂ)
    (l₁ l₂ k₁ : ℕ) (hk₁ : 1 ≤ k₁) (hf : ∀ x : ℤ, Complex.normSq (f x) ≤ 1)
    (hg : ∀ x : ℤ, Complex.normSq (g x) ≤ 1)
    (hN : ∀ n : ℕ, 1 ≤ Nat.floor (a n)) :
    Work.KMTPlan.A6.mdlPartJ ρ P C₀ a f g l₁ l₂ k₁ 0 0 0
      = fun n x => (Work.KMTPlan.A6.mdlScaleF k₁ : ℂ) * Work.KMTPlan.A6.mdlIota
            * (Work.KMTPlan.A6.mdlSliceW ρ P C₀ a f g l₁ l₂ k₁ 0 (-1) 0
                  (fun _ _ => (1 : ℂ)) 1 n x
              - Work.KMTPlan.A6.mdlSliceW ρ P C₀ a f g l₁ l₂ k₁ 0 (-1) 0
                  (fun _ _ => (1 : ℂ)) (1 / 2) n x)
        - (Work.KMTPlan.A6.mdlScaleFG P k₁ 0 : ℂ)
            * Work.KMTPlan.A6.mdlWInt ρ P C₀ a f g l₁ l₂ k₁ 0 (-1) 1
                (fun n t => Work.KMTPlan.A6.mdlW3 P (Nat.floor (a n)) t) n x := by
  funext n x
  by_cases hcore : mdlCore ρ C₀ a l₁ l₂ k₁ 0 n
  · obtain ⟨CF, hCF⟩ := mdl_F_bounded ρ (uScale ρ (max (max l₁ l₂) (max k₁ 0))) l₁ hf
    obtain ⟨CG, hCG⟩ := mdl_G_bounded ρ P (uScale ρ (max (max l₁ l₂) (max k₁ 0))) l₂ hg
    obtain ⟨Cw, hCw0, hw⟩ := mdl_W3_bound P (Nat.floor (a n))
    have hwm : AEStronglyMeasurable (fun t : ℝ => mdlW3 P (Nat.floor (a n)) t)
        (volume : MeasureTheory.Measure ℝ) :=
      (mdl_W3_continuous P _).measurable.aestronglyMeasurable
    have hK : Summable fun p : ℤ × ℤ =>
        ‖mdlBtwK ρ P l₁ l₂ (mStarF (uScale ρ (max (max l₁ l₂) (max k₁ 0))))
          (mStargF P.natDegree (uScale ρ (max (max l₁ l₂) (max k₁ 0)))) p.1 p.2‖ :=
      mdl_summable_mdlBtwK ρ P l₁ l₂ _ _
        (summable_cw_mStarF (uScale ρ (max (max l₁ l₂) (max k₁ 0))))
        (summable_cw_mStargF P.natDegree (uScale ρ (max (max l₁ l₂) (max k₁ 0))))
    obtain ⟨a₁, ha₁, hb₁, hm₁⟩ := MdlKerVarphiNt ρ l₁ (Nat.floor (a n)) k₁
    obtain ⟨a₂, ha₂, hb₂, hm₂⟩ := MdlKerVarphitildeNt ρ l₂ P.natDegree (Nat.floor (a n)) 0 P
    obtain ⟨_, a₃, ha₃, hb₃, hm₃⟩ := MdlKerVarphiNtj ρ l₁ (Nat.floor (a n)) k₁ hk₁
    obtain ⟨_, a₄, ha₄, hb₄, hm₄⟩ := MdlKerVarphitildeNtj ρ l₂ P (Nat.floor (a n))
    rw [mdlPartJ_zero_zero, mdlPart_eq, if_pos hcore]
    simp only [mdlSliceW, mdlWInt, if_pos hcore, one_mul]
    exact mdlDecayHighLow_core ρ P l₁ l₂ (Nat.floor (a n)) k₁ hk₁ (hN n)
      (uScale ρ (max (max l₁ l₂) (max k₁ 0)))
      (mdlF ρ (uScale ρ (max (max l₁ l₂) (max k₁ 0))) l₁ f)
      (mdlG ρ P (uScale ρ (max (max l₁ l₂) (max k₁ 0))) l₂ g)
      CF CG Cw hCF hCG hCw0 hw hwm hK a₁ a₂ a₃ a₄ ha₁ ha₂ ha₃ ha₄ hb₁ hb₂ hb₃ hb₄
      (fun i => (hm₁ i).aestronglyMeasurable) (fun i => (hm₂ i).aestronglyMeasurable)
      (fun i => (hm₃ i).aestronglyMeasurable) (fun i => (hm₄ i).aestronglyMeasurable) x
  · rw [mdlPartJ_eq_zero_of_not_core ρ P C₀ a f g l₁ l₂ k₁ 0 0 0 n x hcore]
    simp [mdlSliceW, mdlWInt, hcore]

end

end Work.KMTPlan.A6
