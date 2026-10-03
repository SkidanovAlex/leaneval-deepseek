/-
# The `§8` model bound of the mixed range at bounded height

`Work.KMTPlan.A6.BoundedHMain.modelBound`: for `0 < ρ ≤ 1`, `2 < r` and a height bound `B`, the
`ℓ¹`-norm of the `r`-variation of the mixed §8 model tuple `loMixedTuple ρ P C₀ a f g l₂ k₁ k₂` is
bounded by `K(Λ)‖f‖₂‖g‖₂`.

The model operator factorises at arithmetic height `0` into the product of two one-variable
convolutions (`Work.KMTAreas.A7.btwistZero_factor`): the `f`-side factor is the fixed-kernel
convolution of the height-`0` piece `Tle ρ 0 (φ_{N,t}) f` with the window kernel `cw (m_* u)`, and
the `g`-side factor is the fixed-kernel convolution of the exact-height piece
`Tm ρ l₂ (φ̃_{N,t}) g` with the arithmetic kernel `loMixedGKer`.  The `t`-integral is handled by
`Work.KMTAreas.A7.variationalNorm_integral_le` (pointwise) and
`Work.KMTAreas.A7.eLpNorm_lintegral_le` (`ℓ¹`), the product by
`Work.KMTAreas.A7.variationalNorm_mul_le` and Hölder.  The two linear inputs are the *level-`0`*
estimate `plainVarF_lev0` and the bounded-height `g`-side estimate `gsideBoundedHeight`; both
fixed kernels are absorbed by Young's inequality (`variationalNorm_tsum_conv`).  No `AreaA1` is
used.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.MixedGSideAux
import Submission.Work.KMTPlan.A6.LowModApproxBoundedH.plainVarF_lev0
import Submission.Work.KMTPlan.A6.BoundedHMain.HZ.Gside
import Submission.Port.Aesm

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.KMTPlan.A6.BoundedHMain

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.KMTAreas.A7 Work.KMTContract
open Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier

local notation "Circ" => Work.Analysis.IonescuWainger.Circle

noncomputable section

/-! ## Elementary auxiliary facts -/

/-- The `loGuard` clip is the `core` clip with the heights in their original order. -/
theorem loGuard_eq_core_zero (ρ : ℝ) (C₀ : ℕ) (a : ℕ → NNReal) (l₂ k₁ k₂ n : ℕ) :
    (Work.KMTAreas.A7.loGuard ρ C₀ a 0 l₂ k₁ k₂ n)
      = (Work.KMTAreas.A7.core ρ C₀ 0 l₂ k₁ k₂ a n) := rfl

/-- The interval integral of `if c then X t else 0` is `if c then` the integral of `X`. -/
theorem intervalIntegral_ite_const_local (a b : ℝ) (c : Prop) [Decidable c] (X : ℝ → ℂ) :
    (∫ t in a..b, (if c then X t else 0)) = if c then ∫ t in a..b, X t else 0 := by
  by_cases h : c
  · rw [if_pos h]
    exact intervalIntegral.integral_congr (fun t _ => by rw [if_pos h])
  · rw [if_neg h]
    refine (intervalIntegral.integral_congr (fun t _ => by rw [if_neg h])).trans ?_
    simp

/-- The mixed model operator is the `t`-integral of the product of its two factors: this is
`btwistZero_factor` applied to the integrand of `loMixedOp`. -/
theorem loMixedOp_eq_integral_product (ρ : ℝ) (P : ℤ[X]) (N l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ)
    (x : ℤ) :
    Work.KMTAreas.A7.loMixedOp ρ P N l₂ k₁ k₂ f g x
      = ∫ t in (1/2 : ℝ)..1,
          (convOp (cw (Work.KMTAreas.A7.mStarF (Work.KMTAreas.A7.loMixedU ρ P.natDegree
              l₂ k₁ k₂)))
            (Work.KMTAreas.A7.Tm ρ 0 (Work.KMTAreas.A7.varphiNt N k₁ t) f) x)
          * (convOp (Work.KMTAreas.A7.loMixedGKer ρ P l₂
              (Work.KMTAreas.A7.mStargF P.natDegree (Work.KMTAreas.A7.loMixedU ρ P.natDegree
                l₂ k₁ k₂)))
            (Work.KMTAreas.A7.Tm ρ l₂ (Work.KMTAreas.A7.varphitildeNt P P.natDegree N k₂ t) g)
            x) := by
  rw [Work.KMTAreas.A7.loMixedOp]
  refine intervalIntegral.integral_congr (fun t _ => ?_)
  simp only [convOp]
  exact Work.KMTAreas.A7.btwistZero_factor ρ P l₂ _ _ _ _ x

/-- **The mixed model tuple as an interval integral of the product of its two factors**, with the
guard clip pushed inside the integrand. -/
theorem loMixedTuple_eq_integral (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → NNReal) (f g : ℤ → ℂ)
    (l₂ k₁ k₂ n : ℕ) (x : ℤ) :
    Work.KMTAreas.A7.loMixedTuple ρ P C₀ a f g l₂ k₁ k₂ n x
      = ∫ t in (1/2 : ℝ)..1,
          (if Work.KMTAreas.A7.loGuard ρ C₀ a 0 l₂ k₁ k₂ n then
              convOp (cw (Work.KMTAreas.A7.mStarF (Work.KMTAreas.A7.loMixedU ρ P.natDegree
                  l₂ k₁ k₂)))
                (Work.KMTAreas.A7.Tm ρ 0 (Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) k₁ t) f) x
            else 0)
          * (if Work.KMTAreas.A7.loGuard ρ C₀ a 0 l₂ k₁ k₂ n then
              convOp (Work.KMTAreas.A7.loMixedGKer ρ P l₂
                  (Work.KMTAreas.A7.mStargF P.natDegree (Work.KMTAreas.A7.loMixedU ρ P.natDegree
                    l₂ k₁ k₂)))
                (Work.KMTAreas.A7.Tm ρ l₂
                  (Work.KMTAreas.A7.varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g) x
            else 0) := by
  rw [Work.KMTAreas.A7.loMixedTuple]
  by_cases h : Work.KMTAreas.A7.loGuard ρ C₀ a 0 l₂ k₁ k₂ n
  · simp only [if_pos h]
    exact loMixedOp_eq_integral_product ρ P _ l₂ k₁ k₂ f g x
  · simp only [if_neg h]
    simp

/-! ## Measurability in `t` -/

theorem measurable_Tm_zero_varphiNt' (ρ : ℝ) (N k : ℕ) (f : ℤ → ℂ) (y : ℤ) :
    Measurable (fun t : ℝ => Work.KMTAreas.A7.Tm ρ 0
      (Work.KMTAreas.A7.varphiNt N k t) f y) := by
  have h := measurable_iwConv_varphiNt (Work.KMTAreas.A7.diffFreqs ρ 0) N k f y
  simpa only [Work.KMTAreas.A7.Tm] using h

theorem measurable_Tm_varphitildeNt' (ρ : ℝ) (P : Polynomial ℤ) (l N k : ℕ) (g : ℤ → ℂ)
    (y : ℤ) :
    Measurable (fun t : ℝ => Work.KMTAreas.A7.Tm ρ l
      (Work.KMTAreas.A7.varphitildeNt P P.natDegree N k t) g y) := by
  have hfun : (fun t : ℝ => Work.KMTAreas.A7.Tm ρ l
        (Work.KMTAreas.A7.varphitildeNt P P.natDegree N k t) g y)
      = fun t : ℝ => ∑' j : ℤ, iwKernel (iwSymbolSet (Work.KMTAreas.A7.diffFreqs ρ l)
          (periodize (Work.KMTAreas.A7.varphitildeNt P P.natDegree N k t))) j * g (y - j) := by
    funext t
    rw [Work.KMTAreas.A7.Tm, Work.KMTAreas.A7.iwConv_eq_tsum_mul]
  rw [hfun]
  exact Measurable.tsum (fun j : ℤ =>
    (Work.KMTAreas.A7.measurable_fourierCoeff_iwSymbolSet (Work.KMTAreas.A7.diffFreqs ρ l) j
      (Work.KMTAreas.A7.measurable_varphitildeNt_uncurry P N k)).mul_const _)

theorem measurable_convOp_Tm_zero_varphiNt' (ρ : ℝ) (m : ℝ → ℂ) (N k : ℕ) (f : ℤ → ℂ) (x : ℤ) :
    Measurable (fun t : ℝ => convOp (cw m) (Work.KMTAreas.A7.Tm ρ 0
      (Work.KMTAreas.A7.varphiNt N k t) f) x) := by
  have hfun : (fun t : ℝ => convOp (cw m) (Work.KMTAreas.A7.Tm ρ 0
        (Work.KMTAreas.A7.varphiNt N k t) f) x)
      = fun t : ℝ => ∑' j : ℤ, cw m j * Work.KMTAreas.A7.Tm ρ 0
          (Work.KMTAreas.A7.varphiNt N k t) f (x - j) := by
    funext t; rw [convOp]
  rw [hfun]
  exact Measurable.tsum (fun j : ℤ =>
    measurable_const.mul (measurable_Tm_zero_varphiNt' ρ N k f (x - j)))

theorem measurable_convOp_GKer_Tm_varphitildeNt' (ρ : ℝ) (P : Polynomial ℤ) (l₂ N k : ℕ)
    (m₂ : ℝ → ℂ) (g : ℤ → ℂ) (x : ℤ) :
    Measurable (fun t : ℝ => convOp (Work.KMTAreas.A7.loMixedGKer ρ P l₂ m₂)
      (Work.KMTAreas.A7.Tm ρ l₂ (Work.KMTAreas.A7.varphitildeNt P P.natDegree N k t) g) x) := by
  have hfun : (fun t : ℝ => convOp (Work.KMTAreas.A7.loMixedGKer ρ P l₂ m₂)
        (Work.KMTAreas.A7.Tm ρ l₂ (Work.KMTAreas.A7.varphitildeNt P P.natDegree N k t) g) x)
      = fun t : ℝ => ∑' j : ℤ, Work.KMTAreas.A7.loMixedGKer ρ P l₂ m₂ j
          * Work.KMTAreas.A7.Tm ρ l₂ (Work.KMTAreas.A7.varphitildeNt P P.natDegree N k t) g
              (x - j) := by
    funext t; rw [convOp]
  rw [hfun]
  exact Measurable.tsum (fun j : ℤ =>
    measurable_const.mul (measurable_Tm_varphitildeNt' ρ P l₂ N k g (x - j)))

/-! ## The mass of the arithmetic kernel `loMixedGKer` -/

/-- **The pointwise bound on the arithmetic kernel `loMixedGKer`**: its modulus is at most the
cardinality of the exact-height frequency set times `‖cw m₂ j‖`. -/
theorem norm_loMixedGKer_le (ρ : ℝ) (P : Polynomial ℤ) (l₂ : ℕ) (m₂ : ℝ → ℂ) (j : ℤ) :
    ‖Work.KMTAreas.A7.loMixedGKer ρ P l₂ m₂ j‖
      ≤ ((Work.KMTAreas.A7.diffFreqs ρ l₂).card : ℝ) * ‖cw m₂ j‖ := by
  classical
  set D : ℝ := ((Work.KMTAreas.A7.diffFreqs ρ l₂).card : ℝ) with hD
  have hD0 : 0 ≤ D := by rw [hD]; positivity
  have hθ : ‖∑ α₂ ∈ Work.KMTAreas.A7.diffFreqs ρ l₂,
      Work.KMTAreas.A7.mZ P (Work.KMTAreas.A7.arithQ ρ l₂) 0 α₂
        * fourier (T := 1) (-j) α₂‖ ≤ D := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ α₂ ∈ Work.KMTAreas.A7.diffFreqs ρ l₂,
          ‖Work.KMTAreas.A7.mZ P (Work.KMTAreas.A7.arithQ ρ l₂) 0 α₂
            * fourier (T := 1) (-j) α₂‖
        ≤ ∑ _α₂ ∈ Work.KMTAreas.A7.diffFreqs ρ l₂, (1 : ℝ) := by
          refine Finset.sum_le_sum (fun α₂ _ => ?_)
          rw [norm_mul]
          have h1 : ‖fourier (T := 1) (-j) α₂‖ = 1 := by
            rw [fourier_apply]
            exact _root_.Circle.norm_coe _
          rw [h1, mul_one]
          exact Work.KMTPlan.A6.symp_norm_mZ_le_one P _ _ _
      _ = D := by rw [hD, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [Work.KMTAreas.A7.loMixedGKer, norm_mul]
  exact mul_le_mul hθ le_rfl (norm_nonneg _) hD0

/-- **The `ℓ¹`-mass of the arithmetic kernel `loMixedGKer`** is at most the cardinality of the
exact-height frequency set times the mass of `cw m₂`. -/
theorem tsum_loMixedGKer_le_mass (ρ : ℝ) (P : Polynomial ℤ) (l₂ : ℕ) (m₂ : ℝ → ℂ)
    (hsum : Summable fun j : ℤ => ‖cw m₂ j‖) :
    (∑' j : ℤ, ‖Work.KMTAreas.A7.loMixedGKer ρ P l₂ m₂ j‖)
      ≤ ((Work.KMTAreas.A7.diffFreqs ρ l₂).card : ℝ) * (∑' j : ℤ, ‖cw m₂ j‖) := by
  classical
  have hsum1 : Summable fun j : ℤ => ‖Work.KMTAreas.A7.loMixedGKer ρ P l₂ m₂ j‖ :=
    Summable.of_nonneg_of_le (fun j => norm_nonneg _)
      (fun j => norm_loMixedGKer_le ρ P l₂ m₂ j) (hsum.mul_left _)
  refine (hsum1.tsum_le_tsum (fun j => norm_loMixedGKer_le ρ P l₂ m₂ j)
    (hsum.mul_left _)).trans (le_of_eq ?_)
  rw [tsum_mul_left]

/-! ## The two factor bounds -/

/-- **The `f`-side factor bound of the mixed model.**  For every `t ∈ [1/2,1]`, the `ℓ²`-norm of
the `r`-variation of the clipped family `1_{loGuard}·convOp (cw m_*) (Tle ρ 0 (φ_{N,t}) f)` is
bounded by `K(Λ)‖f‖₂`, uniformly in `t` and in the heights `l₂`, `k₁ ≤ B`. -/
theorem fsideKernelBound (P : Polynomial ℤ) (r : NNReal) (hr : 2 < r) (C₀ : ℕ) (hC₀ : 1 ≤ C₀)
    (ρ : ℝ) (hρ : 0 < ρ) (B : ℕ) :
    ∃ K : NNReal → NNReal,
      ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₂ k₁ k₂ : ℕ) (t : ℝ) (f : ℤ → ℂ),
        1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) → k₁ ≤ B →
        t ∈ Set.Icc (1/2 : ℝ) 1 →
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ =>
              if Work.KMTAreas.A7.loGuard ρ C₀ a 0 l₂ k₁ k₂ n then
                convOp (cw (Work.KMTAreas.A7.mStarF
                    (Work.KMTAreas.A7.loMixedU ρ P.natDegree l₂ k₁ k₂)))
                  (Work.KMTAreas.A7.Tle ρ 0
                    (Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) k₁ t) f) x
              else 0)) 2 MeasureTheory.Measure.count
          ≤ (K Λ : ENNReal) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
  classical
  obtain ⟨C, hC⟩ :=
    Work.KMTPlan.A6.LowModApproxBoundedH.plainVarF_lev0 r hr C₀ hC₀ ρ hρ B
  obtain ⟨Ck, hCkpos, hCk⟩ := Work.KMTPlan.A6.vpc_exists_cw_mStarF_tsum_le
  refine ⟨fun Λ => Real.toNNReal (Ck * (C Λ : ℝ)), ?_⟩
  intro a Λ l₂ k₁ k₂ t f hΛ ha ha1 hk₁B ht
  set w : ℕ → ℤ → ℂ := fun n x =>
    if Work.KMTAreas.A7.core ρ C₀ 0 l₂ k₁ k₂ a n then
      Work.KMTAreas.A7.Tle ρ 0 (Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) k₁ t) f x
    else 0 with hw
  have hbase : MeasureTheory.eLpNorm (fun x : ℤ =>
      PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => w n x)) 2
      MeasureTheory.Measure.count ≤ (C Λ : ENNReal) * MeasureTheory.eLpNorm f 2
        MeasureTheory.Measure.count := hC a Λ l₂ k₁ k₂ t f hΛ ha ha1 hk₁B ht
  have hfam : (fun n : ℕ => (fun x : ℤ =>
        if Work.KMTAreas.A7.loGuard ρ C₀ a 0 l₂ k₁ k₂ n then
          convOp (cw (Work.KMTAreas.A7.mStarF (Work.KMTAreas.A7.loMixedU ρ P.natDegree
            l₂ k₁ k₂)))
            (Work.KMTAreas.A7.Tle ρ 0 (Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) k₁ t) f) x
        else 0))
      = fun n : ℕ => fun x : ℤ => convOp
          (cw (Work.KMTAreas.A7.mStarF (Work.KMTAreas.A7.loMixedU ρ P.natDegree l₂ k₁ k₂)))
          (w n) x := by
    funext n x
    by_cases h : Work.KMTAreas.A7.loGuard ρ C₀ a 0 l₂ k₁ k₂ n
    · have h' : Work.KMTAreas.A7.core ρ C₀ 0 l₂ k₁ k₂ a n := by
        rw [← loGuard_eq_core_zero]; exact h
      have hw1 : w n = fun y : ℤ =>
          Work.KMTAreas.A7.Tle ρ 0 (Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) k₁ t) f y := by
        funext y
        simp only [hw, if_pos h']
      simp only [if_pos h, hw1]
    · have h' : ¬ Work.KMTAreas.A7.core ρ C₀ 0 l₂ k₁ k₂ a n := by
        rw [← loGuard_eq_core_zero]; exact h
      have hw0 : w n = 0 := by
        funext y
        simp only [hw, if_neg h']
        rfl
      simp only [if_neg h, hw0]
      simp [convOp]
  have hrew : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
        (if Work.KMTAreas.A7.loGuard ρ C₀ a 0 l₂ k₁ k₂ n then
          convOp (cw (Work.KMTAreas.A7.mStarF (Work.KMTAreas.A7.loMixedU ρ P.natDegree
            l₂ k₁ k₂)))
            (Work.KMTAreas.A7.Tle ρ 0 (Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) k₁ t) f) x
        else 0)))
      = fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => convOp
          (cw (Work.KMTAreas.A7.mStarF (Work.KMTAreas.A7.loMixedU ρ P.natDegree l₂ k₁ k₂)))
          (w n) x) := by
    funext x
    congr 1
    funext n
    exact congrFun (congrFun hfam n) x
  rw [hrew]
  set κ : ℤ → ℂ := cw (Work.KMTAreas.A7.mStarF
    (Work.KMTAreas.A7.loMixedU ρ P.natDegree l₂ k₁ k₂)) with hκ
  have hκsum : Summable fun j : ℤ => ‖κ j‖ := (hCk _).1
  have hκle : (∑' j : ℤ, ‖κ j‖) ≤ Ck := (hCk _).2
  have hr1 : (1 : NNReal) ≤ r := le_of_lt (lt_trans (by norm_num) hr)
  have hpt : ∀ x : ℤ, PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
        convOp κ (w n) x)
      ≤ ∑' j : ℤ, ENNReal.ofReal ‖κ j‖
          * PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => w n (x - j)) := by
    intro x
    have h := Work.KMTAreas.A7.variationalNorm_tsum_conv (r := r) hr1 κ hκsum w x
    simpa only [hκ, convOp] using h
  refine (MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm)
    (f := fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
      convOp κ (w n) x))
    (g := fun x : ℤ => ∑' j : ℤ, ENNReal.ofReal ‖κ j‖
      * PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => w n (x - j)))
    (fun x => by rw [enorm_eq_self, enorm_eq_self]; exact hpt x)).trans ?_
  have hmink := Commons.MeasureTheory.Lp.eLpNorm_tsum_le_tsum_eLpNorm
    (μ := MeasureTheory.Measure.count) (p := 2) (by norm_num)
    (f := fun j : ℤ => fun x : ℤ => ENNReal.ofReal ‖κ j‖
      * PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => w n (x - j)))
    (fun j => (measurable_of_countable _).aemeasurable)
  have hterm : ∀ j : ℤ, MeasureTheory.eLpNorm (fun x : ℤ =>
        ENNReal.ofReal ‖κ j‖ * PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => w n (x - j))) 2 MeasureTheory.Measure.count
      = ENNReal.ofReal ‖κ j‖ * MeasureTheory.eLpNorm (fun x : ℤ =>
          PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => w n x)) 2
          MeasureTheory.Measure.count := by
    intro j
    have h2 : (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) := by rw [ENNReal.ofReal_ofNat]
    rw [h2]
    rw [Commons.Analysis.Convolution.eLpNorm_sub_right_ennreal (fun y : ℤ =>
      ENNReal.ofReal ‖κ j‖ * PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => w n y))
      j (by norm_num)]
    exact Commons.Analysis.Convolution.eLpNorm_const_mul_ennreal_of_pos
      (f := fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => w n x))
      (measurable_of_countable _).aemeasurable _ (by norm_num)
  have hmass : (∑' j : ℤ, ENNReal.ofReal ‖κ j‖) ≤ ENNReal.ofReal Ck := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => norm_nonneg _) hκsum]
    exact ENNReal.ofReal_le_ofReal hκle
  refine hmink.trans ?_
  rw [tsum_congr hterm, ENNReal.tsum_mul_right]
  refine (mul_le_mul' hmass hbase).trans (le_of_eq ?_)
  rw [ENNReal.ofNNReal_toNNReal, ENNReal.ofReal_mul (le_of_lt hCkpos),
    ENNReal.ofReal_coe_nnreal]
  ring

/-- **The `g`-side factor bound of the mixed model.**  For every `t ∈ [1/2,1]`, the `ℓ²`-norm of
the `r`-variation of the clipped family `1_{loGuard}·convOp (loMixedGKer) (Tm ρ l₂ (φ̃_{N,t}) g)`
is bounded by `K(Λ)‖g‖₂`, uniformly in `t` and in the heights `l₂ ≤ B`, `k₂ ≤ B`. -/
theorem gsideKernelBound (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (r : NNReal) (hr : 2 < r)
    (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (B : ℕ) :
    ∃ K : NNReal → NNReal,
      ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₂ k₁ k₂ : ℕ) (t : ℝ) (g : ℤ → ℂ) (Cg : ℝ),
        1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ m, 1 ≤ a m) → l₂ ≤ B → k₂ ≤ B →
        t ∈ Set.Icc (1/2 : ℝ) 1 → (∀ y : ℤ, ‖g y‖ ≤ Cg) →
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ =>
              if Work.KMTAreas.A7.loGuard ρ C₀ a 0 l₂ k₁ k₂ n then
                convOp (Work.KMTAreas.A7.loMixedGKer ρ P l₂
                    (Work.KMTAreas.A7.mStargF P.natDegree
                      (Work.KMTAreas.A7.loMixedU ρ P.natDegree l₂ k₁ k₂)))
                  (Work.KMTAreas.A7.Tm ρ l₂
                    (Work.KMTAreas.A7.varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g) x
              else 0)) 2 MeasureTheory.Measure.count
          ≤ (K Λ : ENNReal) * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
  classical
  obtain ⟨K', hK'⟩ := gsideBoundedHeight P hd r hr C₀ hC₀ ρ hρ hρ1 B
  obtain ⟨Ck, hCkpos, hCk⟩ := Work.KMTPlan.A6.vpc_exists_cw_mStarF_tsum_le
  refine ⟨fun Λ => Real.toNNReal ((↑((iwArithFreqs ρ B).card) : ℝ) * (Ck * (K' Λ : ℝ))), ?_⟩
  intro a Λ l₂ k₁ k₂ t g Cg hΛ ha ha1 hl₂B hk₂B ht hg
  set w : ℕ → ℤ → ℂ := fun n x =>
    if Work.KMTAreas.A7.loGuard ρ C₀ a 0 l₂ k₁ k₂ n then
      Work.KMTAreas.A7.Tm ρ l₂
        (Work.KMTAreas.A7.varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g x
    else 0 with hw
  have hbase : MeasureTheory.eLpNorm (fun x : ℤ =>
      PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => w n x)) 2
      MeasureTheory.Measure.count ≤ (K' Λ : ENNReal) * MeasureTheory.eLpNorm g 2
        MeasureTheory.Measure.count := hK' a Λ l₂ k₁ k₂ t g Cg hΛ ha ha1 hl₂B hk₂B ht hg
  have hfam : (fun n : ℕ => (fun x : ℤ =>
        if Work.KMTAreas.A7.loGuard ρ C₀ a 0 l₂ k₁ k₂ n then
          convOp (Work.KMTAreas.A7.loMixedGKer ρ P l₂
              (Work.KMTAreas.A7.mStargF P.natDegree
                (Work.KMTAreas.A7.loMixedU ρ P.natDegree l₂ k₁ k₂)))
            (Work.KMTAreas.A7.Tm ρ l₂ (Work.KMTAreas.A7.varphitildeNt P P.natDegree
              (Nat.floor (a n)) k₂ t) g) x
        else 0))
      = fun n : ℕ => fun x : ℤ => convOp (Work.KMTAreas.A7.loMixedGKer ρ P l₂
          (Work.KMTAreas.A7.mStargF P.natDegree
            (Work.KMTAreas.A7.loMixedU ρ P.natDegree l₂ k₁ k₂))) (w n) x := by
    funext n x
    by_cases h : Work.KMTAreas.A7.loGuard ρ C₀ a 0 l₂ k₁ k₂ n
    · have hw1 : w n = fun y : ℤ => Work.KMTAreas.A7.Tm ρ l₂
          (Work.KMTAreas.A7.varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g y := by
        funext y
        simp only [hw, if_pos h]
      simp only [if_pos h, hw1]
    · have hw0 : w n = 0 := by
        funext y
        simp only [hw, if_neg h]
        rfl
      simp only [if_neg h, hw0]
      simp [convOp]
  have hrew : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
        (if Work.KMTAreas.A7.loGuard ρ C₀ a 0 l₂ k₁ k₂ n then
          convOp (Work.KMTAreas.A7.loMixedGKer ρ P l₂
              (Work.KMTAreas.A7.mStargF P.natDegree
                (Work.KMTAreas.A7.loMixedU ρ P.natDegree l₂ k₁ k₂)))
            (Work.KMTAreas.A7.Tm ρ l₂ (Work.KMTAreas.A7.varphitildeNt P P.natDegree
              (Nat.floor (a n)) k₂ t) g) x
        else 0)))
      = fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => convOp
          (Work.KMTAreas.A7.loMixedGKer ρ P l₂ (Work.KMTAreas.A7.mStargF P.natDegree
            (Work.KMTAreas.A7.loMixedU ρ P.natDegree l₂ k₁ k₂))) (w n) x) := by
    funext x
    congr 1
    funext n
    exact congrFun (congrFun hfam n) x
  rw [hrew]
  set κ : ℤ → ℂ := Work.KMTAreas.A7.loMixedGKer ρ P l₂
    (Work.KMTAreas.A7.mStargF P.natDegree
      (Work.KMTAreas.A7.loMixedU ρ P.natDegree l₂ k₁ k₂)) with hκ
  -- the two inputs of the mass bound
  have hcw : Summable fun j : ℤ => ‖cw (Work.KMTAreas.A7.mStargF P.natDegree
      (Work.KMTAreas.A7.loMixedU ρ P.natDegree l₂ k₁ k₂)) j‖ := by
    have h := (hCk (P.natDegree * Work.KMTAreas.A7.loMixedU ρ P.natDegree l₂ k₁ k₂)).1
    rwa [← Work.KMTAreas.A7.mStargF_eq_mStarF P _] at h
  have hcwle : (∑' j : ℤ, ‖cw (Work.KMTAreas.A7.mStargF P.natDegree
      (Work.KMTAreas.A7.loMixedU ρ P.natDegree l₂ k₁ k₂)) j‖) ≤ Ck := by
    have h := (hCk (P.natDegree * Work.KMTAreas.A7.loMixedU ρ P.natDegree l₂ k₁ k₂)).2
    rwa [← Work.KMTAreas.A7.mStargF_eq_mStarF P _] at h
  have hcard : ((Work.KMTAreas.A7.diffFreqs ρ l₂).card : ℝ)
      ≤ ((iwArithFreqs ρ B).card : ℝ) := by
    have h1 : (Work.KMTAreas.A7.diffFreqs ρ l₂).card ≤ (iwArithFreqs ρ B).card :=
      Finset.card_le_card fun α hα =>
        iwArithFreqs_mono hρ hρ1 hl₂B (lp_diffFreqs_subset ρ l₂ hα)
    exact_mod_cast h1
  have hmass' : (∑' j : ℤ, ‖κ j‖) ≤ ((iwArithFreqs ρ B).card : ℝ) * Ck := by
    rw [hκ]
    refine (tsum_loMixedGKer_le_mass ρ P l₂ _ hcw).trans ?_
    exact mul_le_mul hcard hcwle (by positivity) (by positivity)
  have hκsum : Summable fun j : ℤ => ‖κ j‖ := by
    rw [hκ]
    refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_)
      (hcw.mul_left (((iwArithFreqs ρ B).card : ℝ)))
    exact (norm_loMixedGKer_le ρ P l₂ _ j).trans
      (mul_le_mul_of_nonneg_right hcard (norm_nonneg _))
  have hr1 : (1 : NNReal) ≤ r := le_of_lt (lt_trans (by norm_num) hr)
  have hpt : ∀ x : ℤ, PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
        convOp κ (w n) x)
      ≤ ∑' j : ℤ, ENNReal.ofReal ‖κ j‖
          * PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => w n (x - j)) := by
    intro x
    have h := Work.KMTAreas.A7.variationalNorm_tsum_conv (r := r) hr1 κ hκsum w x
    simpa only [hκ, convOp] using h
  refine (MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm)
    (f := fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
      convOp κ (w n) x))
    (g := fun x : ℤ => ∑' j : ℤ, ENNReal.ofReal ‖κ j‖
      * PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => w n (x - j)))
    (fun x => by rw [enorm_eq_self, enorm_eq_self]; exact hpt x)).trans ?_
  have hmink := Commons.MeasureTheory.Lp.eLpNorm_tsum_le_tsum_eLpNorm
    (μ := MeasureTheory.Measure.count) (p := 2) (by norm_num)
    (f := fun j : ℤ => fun x : ℤ => ENNReal.ofReal ‖κ j‖
      * PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => w n (x - j)))
    (fun j => (measurable_of_countable _).aemeasurable)
  have hterm : ∀ j : ℤ, MeasureTheory.eLpNorm (fun x : ℤ =>
        ENNReal.ofReal ‖κ j‖ * PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => w n (x - j))) 2 MeasureTheory.Measure.count
      = ENNReal.ofReal ‖κ j‖ * MeasureTheory.eLpNorm (fun x : ℤ =>
          PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => w n x)) 2
          MeasureTheory.Measure.count := by
    intro j
    have h2 : (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) := by rw [ENNReal.ofReal_ofNat]
    rw [h2]
    rw [Commons.Analysis.Convolution.eLpNorm_sub_right_ennreal (fun y : ℤ =>
      ENNReal.ofReal ‖κ j‖ * PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => w n y))
      j (by norm_num)]
    exact Commons.Analysis.Convolution.eLpNorm_const_mul_ennreal_of_pos
      (f := fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => w n x))
      (measurable_of_countable _).aemeasurable _ (by norm_num)
  have hmass : (∑' j : ℤ, ENNReal.ofReal ‖κ j‖)
      ≤ ENNReal.ofReal (((iwArithFreqs ρ B).card : ℝ) * Ck) := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => norm_nonneg _) hκsum]
    exact ENNReal.ofReal_le_ofReal hmass'
  have hsplit2 : ENNReal.ofReal (Ck * (K' Λ : ℝ))
      = ENNReal.ofReal Ck * (K' Λ : ENNReal) := by
    rw [ENNReal.ofReal_mul (le_of_lt hCkpos), ENNReal.ofReal_coe_nnreal]
  have hEq : ENNReal.ofReal ((↑((iwArithFreqs ρ B).card) : ℝ) * (Ck * (K' Λ : ℝ)))
      = ENNReal.ofReal ((↑((iwArithFreqs ρ B).card) : ℝ)) * ENNReal.ofReal Ck
        * (K' Λ : ENNReal) := by
    rw [show ENNReal.ofReal ((↑((iwArithFreqs ρ B).card) : ℝ) * (Ck * (K' Λ : ℝ)))
        = ENNReal.ofReal ((↑((iwArithFreqs ρ B).card) : ℝ))
          * ENNReal.ofReal (Ck * (K' Λ : ℝ)) from
      ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ ((iwArithFreqs ρ B).card : ℝ))]
    rw [hsplit2]
    ring
  refine hmink.trans ?_
  rw [tsum_congr hterm, ENNReal.tsum_mul_right]
  refine (mul_le_mul' hmass hbase).trans (le_of_eq ?_)
  rw [ENNReal.ofNNReal_toNNReal, hEq,
    show ENNReal.ofReal ((↑((iwArithFreqs ρ B).card) : ℝ) * Ck)
        = ENNReal.ofReal ((↑((iwArithFreqs ρ B).card) : ℝ)) * ENNReal.ofReal Ck from
      ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ ((iwArithFreqs ρ B).card : ℝ))]
  ring

/-! ## The vanishing cases and the height-`0` identification -/

/-- At arithmetic height `0` the exact-height multiplier is the cumulative one. -/
theorem Tm_zero_eq_Tle (ρ : ℝ) (ψ : ℝ → ℂ) (u : ℤ → ℂ) :
    Work.KMTAreas.A7.Tm ρ 0 ψ u = Work.KMTAreas.A7.Tle ρ 0 ψ u := by
  funext x
  simp only [Work.KMTAreas.A7.Tm, Work.KMTAreas.A7.Tle, Work.KMTAreas.A7.diffFreqs]
  congr 3

/-- The exact-height multiplier kills the zero sequence. -/
@[simp] theorem Tm_zero_fn (ρ : ℝ) (l : ℕ) (ψ : ℝ → ℂ) :
    Work.KMTAreas.A7.Tm ρ l ψ (0 : ℤ → ℂ) = 0 := by
  funext x
  simp [Work.KMTAreas.A7.Tm, iwConv]

/-- The mixed model tuple vanishes when `f = 0` (pointwise). -/
theorem loMixedTuple_zero_left_pt (ρ : ℝ) (P : Polynomial ℤ) (C₀ : ℕ) (a : ℕ → NNReal)
    (g : ℤ → ℂ) (l₂ k₁ k₂ n : ℕ) (x : ℤ) :
    Work.KMTAreas.A7.loMixedTuple ρ P C₀ a (0 : ℤ → ℂ) g l₂ k₁ k₂ n x = 0 := by
  rw [Work.KMTAreas.A7.loMixedTuple]
  by_cases h : Work.KMTAreas.A7.loGuard ρ C₀ a 0 l₂ k₁ k₂ n
  · rw [if_pos h]
    rw [loMixedOp_eq_integral_product ρ P (Nat.floor (a n)) l₂ k₁ k₂ (0 : ℤ → ℂ) g x]
    simp [convOp]
  · rw [if_neg h]

/-- The mixed model tuple vanishes when `g = 0` (pointwise). -/
theorem loMixedTuple_zero_right_pt (ρ : ℝ) (P : Polynomial ℤ) (C₀ : ℕ) (a : ℕ → NNReal)
    (f : ℤ → ℂ) (l₂ k₁ k₂ n : ℕ) (x : ℤ) :
    Work.KMTAreas.A7.loMixedTuple ρ P C₀ a f (0 : ℤ → ℂ) l₂ k₁ k₂ n x = 0 := by
  rw [Work.KMTAreas.A7.loMixedTuple]
  by_cases h : Work.KMTAreas.A7.loGuard ρ C₀ a 0 l₂ k₁ k₂ n
  · rw [if_pos h]
    rw [loMixedOp_eq_integral_product ρ P (Nat.floor (a n)) l₂ k₁ k₂ f (0 : ℤ → ℂ) x]
    simp [convOp]
  · rw [if_neg h]

/-! ## The model bound -/

/-- **The `§8` model bound of the mixed range at bounded height.**  For `0 < ρ ≤ 1`, `2 < r` and a
height bound `B` there is `K : ℝ≥0 → ℝ≥0` such that for every `Λ`-lunacary scale sequence `a ≥ 1`,
every quadruple with `lcL 0 l₂ k₁ k₂ ≤ B` and `1 ≤ l₂`, every bounded `g` and every `f`,

  `‖ V^r_n (loMixedTuple ρ P C₀ a f g l₂ k₁ k₂ n ·) ‖_{ℓ¹(ℤ)} ≤ K(Λ) ‖f‖₂ ‖g‖₂`. -/
theorem modelBoundLoMixed (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (r : NNReal) (hr : 2 < r)
    (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (B : ℕ) :
    ∃ K : NNReal → NNReal,
      ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ) (Cg : ℝ),
        1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ m, 1 ≤ a m) →
        Work.KMTPlan.A6.lcL 0 l₂ k₁ k₂ ≤ B → 1 ≤ l₂ → (∀ y : ℤ, ‖g y‖ ≤ Cg) →
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => Work.KMTAreas.A7.loMixedTuple ρ P C₀ a f g l₂ k₁ k₂ n x))
          1 MeasureTheory.Measure.count
          ≤ (K Λ : ENNReal) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
              * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
  classical
  obtain ⟨K₁, hK₁⟩ := fsideKernelBound P r hr C₀ hC₀ ρ hρ B
  obtain ⟨K₂, hK₂⟩ := gsideKernelBound P hd r hr C₀ hC₀ ρ hρ hρ1 B
  refine ⟨fun Λ => max 1 (K₁ Λ * K₂ Λ), ?_⟩
  intro a Λ l₂ k₁ k₂ f g Cg hΛ ha ha1 hlB hl₂ hgb
  have hr1 : (1 : NNReal) ≤ r := le_of_lt (lt_trans (by norm_num) hr)
  -- the height bounds
  have hl₂B : l₂ ≤ B := by
    have h := hlB
    rw [Work.KMTPlan.A6.lcL] at h
    exact le_trans (le_trans (le_max_right 0 l₂) (le_max_left _ _)) h
  have hk₁B : k₁ ≤ B := by
    have h := hlB
    rw [Work.KMTPlan.A6.lcL] at h
    exact le_trans (le_trans (le_max_left k₁ k₂) (le_max_right _ _)) h
  have hk₂B : k₂ ≤ B := by
    have h := hlB
    rw [Work.KMTPlan.A6.lcL] at h
    exact le_trans (le_trans (le_max_right k₁ k₂) (le_max_right _ _)) h
  -- the degenerate cases
  by_cases hf0 : MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count = 0
  · have hz : f = 0 := by
      have h := (MeasureTheory.eLpNorm_eq_zero_iff (p := (2 : ENNReal)) (by norm_num)).mp hf0
      funext x
      simpa using MeasureTheory.Measure.ae_count_iff.mp h x
    have hfun : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => Work.KMTAreas.A7.loMixedTuple ρ P C₀ a f g l₂ k₁ k₂ n x)) = 0 := by
      funext x
      have h0 : (fun n : ℕ => Work.KMTAreas.A7.loMixedTuple ρ P C₀ a f g l₂ k₁ k₂ n x)
          = fun _ : ℕ => (0 : ℂ) := by
        funext n
        rw [hz]
        exact loMixedTuple_zero_left_pt ρ P C₀ a g l₂ k₁ k₂ n x
      rw [h0]
      exact Work.KMTAreas.A7.variationalNorm_zero r hr1
    rw [hfun, MeasureTheory.eLpNorm_zero]
    simp
  by_cases hg0 : MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count = 0
  · have hz : g = 0 := by
      have h := (MeasureTheory.eLpNorm_eq_zero_iff (p := (2 : ENNReal)) (by norm_num)).mp hg0
      funext x
      simpa using MeasureTheory.Measure.ae_count_iff.mp h x
    have hfun : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => Work.KMTAreas.A7.loMixedTuple ρ P C₀ a f g l₂ k₁ k₂ n x)) = 0 := by
      funext x
      have h0 : (fun n : ℕ => Work.KMTAreas.A7.loMixedTuple ρ P C₀ a f g l₂ k₁ k₂ n x)
          = fun _ : ℕ => (0 : ℂ) := by
        funext n
        rw [hz]
        exact loMixedTuple_zero_right_pt ρ P C₀ a f l₂ k₁ k₂ n x
      rw [h0]
      exact Work.KMTAreas.A7.variationalNorm_zero r hr1
    rw [hfun, MeasureTheory.eLpNorm_zero]
    simp
  by_cases hfT : MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count = ⊤
  · have hK0 : ((max 1 (K₁ Λ * K₂ Λ) : NNReal) : ENNReal) ≠ 0 := by
      rw [Ne, ENNReal.coe_eq_zero]
      exact ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
    have hKt : ((max 1 (K₁ Λ * K₂ Λ) : NNReal) : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
    rw [hfT, ENNReal.mul_top hK0, ENNReal.top_mul hg0]
    exact le_top
  by_cases hgT : MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count = ⊤
  · have hK0 : ((max 1 (K₁ Λ * K₂ Λ) : NNReal) : ENNReal) ≠ 0 := by
      rw [Ne, ENNReal.coe_eq_zero]
      exact ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
    have hKt : ((max 1 (K₁ Λ * K₂ Λ) : NNReal) : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
    rw [hgT, ENNReal.mul_top (mul_ne_zero hK0 hf0)]
    exact le_top
  -- the main case
  have hfin : ((K₁ Λ : ENNReal) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top hfT
  have hgin : ((K₂ Λ : ENNReal) * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top hgT
  -- the two clipped families
  set A : ℝ → ℕ → ℤ → ℂ := fun t n x =>
    if Work.KMTAreas.A7.loGuard ρ C₀ a 0 l₂ k₁ k₂ n then
      convOp (cw (Work.KMTAreas.A7.mStarF (Work.KMTAreas.A7.loMixedU ρ P.natDegree l₂ k₁ k₂)))
        (Work.KMTAreas.A7.Tm ρ 0 (Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) k₁ t) f) x
    else 0 with hAdef
  set Bd : ℝ → ℕ → ℤ → ℂ := fun t n x =>
    if Work.KMTAreas.A7.loGuard ρ C₀ a 0 l₂ k₁ k₂ n then
      convOp (Work.KMTAreas.A7.loMixedGKer ρ P l₂
          (Work.KMTAreas.A7.mStargF P.natDegree
            (Work.KMTAreas.A7.loMixedU ρ P.natDegree l₂ k₁ k₂)))
        (Work.KMTAreas.A7.Tm ρ l₂
          (Work.KMTAreas.A7.varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g) x
    else 0 with hBdef
  -- the per-`t` factor bounds
  have hAle : ∀ t ∈ Set.Icc (1/2 : ℝ) 1, MeasureTheory.eLpNorm (fun x : ℤ =>
      PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => A t n x)) 2
      MeasureTheory.Measure.count ≤ (K₁ Λ : ENNReal) * MeasureTheory.eLpNorm f 2
        MeasureTheory.Measure.count := by
    intro t ht
    have h := hK₁ a Λ l₂ k₁ k₂ t f hΛ ha ha1 hk₁B ht
    have hfam : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => A t n x))
        = fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
            (if Work.KMTAreas.A7.loGuard ρ C₀ a 0 l₂ k₁ k₂ n then
              convOp (cw (Work.KMTAreas.A7.mStarF
                  (Work.KMTAreas.A7.loMixedU ρ P.natDegree l₂ k₁ k₂)))
                (Work.KMTAreas.A7.Tle ρ 0
                  (Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) k₁ t) f) x
            else 0)) := by
      funext x
      refine congrArg (fun F : ℕ → ℂ => PointwiseErgodicTheorems.variationalNorm r F) ?_
      funext n
      by_cases hg : Work.KMTAreas.A7.loGuard ρ C₀ a 0 l₂ k₁ k₂ n
      · rw [hAdef]
        simp only [if_pos hg]
        rw [show Work.KMTAreas.A7.Tm ρ 0
              (Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) k₁ t) f
            = Work.KMTAreas.A7.Tle ρ 0
              (Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) k₁ t) f from
          Tm_zero_eq_Tle ρ _ f]
      · rw [hAdef]
        simp only [if_neg hg]
    rw [hfam]
    exact h
  have hBle : ∀ t ∈ Set.Icc (1/2 : ℝ) 1, MeasureTheory.eLpNorm (fun x : ℤ =>
      PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => Bd t n x)) 2
      MeasureTheory.Measure.count ≤ (K₂ Λ : ENNReal) * MeasureTheory.eLpNorm g 2
        MeasureTheory.Measure.count := by
    intro t ht
    have h := hK₂ a Λ l₂ k₁ k₂ t g Cg hΛ ha ha1 hl₂B hk₂B ht hgb
    have hfam : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => Bd t n x))
        = fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
            (if Work.KMTAreas.A7.loGuard ρ C₀ a 0 l₂ k₁ k₂ n then
              convOp (Work.KMTAreas.A7.loMixedGKer ρ P l₂
                  (Work.KMTAreas.A7.mStargF P.natDegree
                    (Work.KMTAreas.A7.loMixedU ρ P.natDegree l₂ k₁ k₂)))
                (Work.KMTAreas.A7.Tm ρ l₂ (Work.KMTAreas.A7.varphitildeNt P P.natDegree
                  (Nat.floor (a n)) k₂ t) g) x
            else 0)) := by
      funext x
      refine congrArg (fun F : ℕ → ℂ => PointwiseErgodicTheorems.variationalNorm r F) ?_
      funext n
      rw [hBdef]
    rw [hfam]
    exact h
  -- the pointwise real bounds on the two families
  have hAreal : ∀ t ∈ Set.Icc (1/2 : ℝ) 1, ∀ n : ℕ, ∀ x : ℤ,
      ‖A t n x‖ ≤ ((K₁ Λ : ENNReal) * MeasureTheory.eLpNorm f 2
        MeasureTheory.Measure.count).toReal := by
    intro t ht n x
    have h1 : ‖A t n x‖ₑ ≤ PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => A t n x) :=
      Work.KMTAreas.A7.enorm_apply_le_variationalNorm (r := r) (fun n : ℕ => A t n x) n
    have h2 : PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => A t n x)
        ≤ (K₁ Λ : ENNReal) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count :=
      Work.KMTAreas.A7.le_of_eLpNorm_count_le (q := 2) (by norm_num) (hAle t ht) x
    have h3 : ‖A t n x‖ₑ ≤ ENNReal.ofReal (((K₁ Λ : ENNReal)
        * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count).toReal) := by
      rw [ENNReal.ofReal_toReal hfin]
      exact h1.trans h2
    rw [← ofReal_norm] at h3
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h3
  have hBreal : ∀ t ∈ Set.Icc (1/2 : ℝ) 1, ∀ n : ℕ, ∀ x : ℤ,
      ‖Bd t n x‖ ≤ ((K₂ Λ : ENNReal) * MeasureTheory.eLpNorm g 2
        MeasureTheory.Measure.count).toReal := by
    intro t ht n x
    have h1 : ‖Bd t n x‖ₑ ≤ PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => Bd t n x) :=
      Work.KMTAreas.A7.enorm_apply_le_variationalNorm (r := r) (fun n : ℕ => Bd t n x) n
    have h2 : PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => Bd t n x)
        ≤ (K₂ Λ : ENNReal) * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count :=
      Work.KMTAreas.A7.le_of_eLpNorm_count_le (q := 2) (by norm_num) (hBle t ht) x
    have h3 : ‖Bd t n x‖ₑ ≤ ENNReal.ofReal (((K₂ Λ : ENNReal)
        * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count).toReal) := by
      rw [ENNReal.ofReal_toReal hgin]
      exact h1.trans h2
    rw [← ofReal_norm] at h3
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h3
  -- measurability in `t`
  have hAmeas : ∀ n : ℕ, ∀ x : ℤ, Measurable (fun t : ℝ => A t n x) := by
    intro n x
    by_cases hg : Work.KMTAreas.A7.loGuard ρ C₀ a 0 l₂ k₁ k₂ n
    · rw [show (fun t : ℝ => A t n x) = fun t : ℝ =>
          convOp (cw (Work.KMTAreas.A7.mStarF
              (Work.KMTAreas.A7.loMixedU ρ P.natDegree l₂ k₁ k₂)))
            (Work.KMTAreas.A7.Tm ρ 0
              (Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) k₁ t) f) x from by
        funext t
        rw [hAdef]
        simp only [if_pos hg]]
      exact measurable_convOp_Tm_zero_varphiNt' ρ _ _ _ f x
    · rw [show (fun t : ℝ => A t n x) = fun _ : ℝ => (0 : ℂ) from by
        funext t
        rw [hAdef]
        simp only [if_neg hg]]
      exact measurable_const
  have hBmeas : ∀ n : ℕ, ∀ x : ℤ, Measurable (fun t : ℝ => Bd t n x) := by
    intro n x
    by_cases hg : Work.KMTAreas.A7.loGuard ρ C₀ a 0 l₂ k₁ k₂ n
    · rw [show (fun t : ℝ => Bd t n x) = fun t : ℝ =>
          convOp (Work.KMTAreas.A7.loMixedGKer ρ P l₂
              (Work.KMTAreas.A7.mStargF P.natDegree
                (Work.KMTAreas.A7.loMixedU ρ P.natDegree l₂ k₁ k₂)))
            (Work.KMTAreas.A7.Tm ρ l₂
              (Work.KMTAreas.A7.varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g) x from by
        funext t
        rw [hBdef]
        simp only [if_pos hg]]
      exact measurable_convOp_GKer_Tm_varphitildeNt' ρ P l₂ _ _ _ g x
    · rw [show (fun t : ℝ => Bd t n x) = fun _ : ℝ => (0 : ℂ) from by
        funext t
        rw [hBdef]
        simp only [if_neg hg]]
      exact measurable_const
  -- the pointwise bound by the `t`-integral of the product
  have hInt : ∀ x : ℤ, PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => Work.KMTAreas.A7.loMixedTuple ρ P C₀ a f g l₂ k₁ k₂ n x)
      ≤ ∫⁻ t in Set.Ioc (1/2 : ℝ) 1,
          PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => A t n x)
            * PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => Bd t n x) := by
    intro x
    have hrepr : (fun n : ℕ => Work.KMTAreas.A7.loMixedTuple ρ P C₀ a f g l₂ k₁ k₂ n x)
        = fun n : ℕ => ∫ t in (1/2 : ℝ)..1, A t n x * Bd t n x := by
      funext n
      rw [loMixedTuple_eq_integral ρ P C₀ a f g l₂ k₁ k₂ n x, hAdef, hBdef]
    rw [hrepr]
    have hconv : (fun n : ℕ => (∫ t in (1/2 : ℝ)..1, A t n x * Bd t n x))
        = fun n : ℕ => ∫ t, A t n x * Bd t n x
            ∂(MeasureTheory.volume.restrict (Set.Ioc (1/2 : ℝ) 1)) := by
      funext n
      rw [intervalIntegral.integral_of_le (by norm_num : (1/2 : ℝ) ≤ 1)]
    rw [hconv]
    refine (Work.KMTAreas.A7.variationalNorm_integral_le (r := r) hr1
      (ν := MeasureTheory.volume.restrict (Set.Ioc (1/2 : ℝ) 1))
      (g := fun t n => A t n x * Bd t n x) ?_).trans ?_
    · -- integrability of every slice
      intro n
      refine MeasureTheory.Integrable.of_bound ?_
        ((((K₁ Λ : ENNReal) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count).toReal)
          * (((K₂ Λ : ENNReal) * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count).toReal))
        ?_
      · exact ((hAmeas n x).mul (hBmeas n x)).aestronglyMeasurable
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t htI
        have htI' : t ∈ Set.Icc (1/2 : ℝ) 1 := Set.Ioc_subset_Icc_self htI
        rw [norm_mul]
        exact mul_le_mul (hAreal t htI' n x) (hBreal t htI' n x) (norm_nonneg _)
          (by positivity)
    · -- the product bound
      refine MeasureTheory.lintegral_mono (fun t => ?_)
      exact Work.KMTAreas.A7.variationalNorm_mul_le_one r hr1 _ _
  refine (MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm) (f := fun x : ℤ =>
      PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => Work.KMTAreas.A7.loMixedTuple ρ P C₀ a f g l₂ k₁ k₂ n x))
    (g := fun x : ℤ => ∫⁻ t in Set.Ioc (1/2 : ℝ) 1,
      PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => A t n x)
        * PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => Bd t n x))
    (fun x => by rw [enorm_eq_self, enorm_eq_self]; exact hInt x)).trans ?_
  refine (Work.KMTAreas.A7.eLpNorm_lintegral_le 1 le_rfl
    (fun t x => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => A t n x)
      * PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => Bd t n x))
    ((K₁ Λ : ENNReal) * (K₂ Λ : ENNReal) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
      * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count) ?_).trans ?_
  · -- the per-`t` `ℓ¹` bound
    intro t ht
    have htI' : t ∈ Set.Icc (1/2 : ℝ) 1 := Set.Ioc_subset_Icc_self ht
    refine (MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm) (f := fun x : ℤ =>
        PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => A t n x)
          * PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => Bd t n x))
      (g := fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => A t n x)
          * PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => Bd t n x))
      (fun x => le_rfl)).trans ?_
    refine (Commons.MeasureTheory.Function.eLpNorm_mul_le_eLpNorm_mul_eLpNorm
      (μ := MeasureTheory.Measure.count) (p := 1) (q := 2) (r := 2)
      (by rw [inv_one, ENNReal.inv_two_add_inv_two])
      (measurable_of_countable _).aemeasurable (measurable_of_countable _).aemeasurable).trans ?_
    refine (mul_le_mul' (hAle t htI') (hBle t htI')).trans (le_of_eq ?_)
    ring
  · -- the final arithmetic
    have hle : ((K₁ Λ : ENNReal) * (K₂ Λ : ENNReal) * MeasureTheory.eLpNorm f 2
          MeasureTheory.Measure.count * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count)
        ≤ ((max 1 (K₁ Λ * K₂ Λ) : NNReal) : ENNReal) * MeasureTheory.eLpNorm f 2
          MeasureTheory.Measure.count * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
      refine mul_le_mul' (mul_le_mul' ?_ le_rfl) le_rfl
      rw [← ENNReal.coe_mul]
      exact ENNReal.coe_le_coe.mpr (le_max_right _ _)
    exact hle

end

end Work.KMTPlan.A6.BoundedHMain
