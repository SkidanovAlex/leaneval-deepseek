/-
# `cmode_bessel` — Bessel's inequality for the mode coefficients of the source

For every `z` and every `N`, the sum of the squared mode coefficients `cmode m F z`, weighted
by the `L²(Iθ, cos θ dθ)` norms of the Dirichlet eigenfunctions `eFam m`, is bounded by the
weighted `L²`-norm of the slice `θ ↦ F z θ`:

  `∑_{m ≤ N} ‖eFam m‖² · (cmode m F z)² ≤ ∫⁻_θ ofReal (F z θ² · cos θ)`.

This is the classical Bessel inequality for the orthogonal system `eFam m`
(orthogonality `eFam_orthogonal`, norms `eFam_norm_fts`): putting
`K θ = √(cos θ) · F z θ` and `eLp m = (‖eFam m‖)⁻¹ · √(cos ·) · eFam m`, the family `eLp` is
an orthonormal system of `L²(volume.restrict Iθ)` and
`eNorm m * (cmode m F z)² = ⟪eLp m, K⟫²`, so Mathlib's Bessel inequality
`Orthonormal.sum_inner_products_le` gives the claim.

When the slice is not a.e. strongly measurable, every `cmode m F z` vanishes by the
convention of the Bochner integral (`integral_non_aestronglyMeasurable`); the required
non-a.e.-measurability of the integrand is inherited from `θ ↦ F z θ` because each mode
weight `θ ↦ eFam m θ · cos θ` vanishes only on a finite set (`eFam_zeroSet_finite`).
-/
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.PhiStar.Series.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.gC_ode
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_orthogonal
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_norm_fts
import Submission.Work.Spaces.Defs
import Submission.Work.EllipticEst.ModalSolution.eFamBasisFts_FALSE

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.EllipticEst.ModalSolution

set_option autoImplicit false

lemma measurableSet_Iθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc

/-! ## The zeros of the mode weights -/

/-- `pG n` is the polynomial realising the Gegenbauer polynomial `gC n`
(`gC n x = (pG n).eval x`); it obeys the same three-term recurrence as `gC n`. -/
def pG : ℕ → Polynomial ℝ
  | 0 => 1
  | 1 => Polynomial.C 3 * Polynomial.X
  | (n + 2) => Polynomial.C (((n : ℝ) + 2)⁻¹) *
      (Polynomial.C (2 * ((n : ℝ) + 5 / 2)) * (Polynomial.X * pG (n + 1))
        - Polynomial.C ((n : ℝ) + 3) * pG n)

/-- The value of `gC n` at `1` is the binomial coefficient `(n+1)(n+2)/2`
(`C_n^{(3/2)}(1) = (n+1)(n+2)/2`); in particular `gC n` is not the zero function. -/
lemma gC_one (n : ℕ) :
    Work.FTS.PhiStar.Gegenbauer.gC n 1 = ((n : ℝ) + 1) * ((n : ℝ) + 2) / 2 := by
  induction n using Nat.twoStepInduction with
  | zero =>
    rw [show Work.FTS.PhiStar.Gegenbauer.gC 0 = (fun _ : ℝ => (1 : ℝ)) from rfl]
    norm_num
  | one =>
    rw [show Work.FTS.PhiStar.Gegenbauer.gC 1 = (fun x : ℝ => 3 * x) from rfl]
    norm_num
  | more k ihk ihk1 =>
    rw [show Work.FTS.PhiStar.Gegenbauer.gC (k + 2) 1
        = (2 * ((k : ℝ) + 5 / 2) * 1 * Work.FTS.PhiStar.Gegenbauer.gC (k + 1) 1
            - ((k : ℝ) + 3) * Work.FTS.PhiStar.Gegenbauer.gC k 1) / ((k : ℝ) + 2)
        from rfl]
    rw [ihk1, ihk]
    push_cast
    have hne : ((k : ℝ) + 2) ≠ 0 := by positivity
    field_simp
    ring

/-- `pG n` evaluates to `gC n`. -/
lemma pG_eval : ∀ n : ℕ, ∀ x : ℝ,
    (pG n).eval x = Work.FTS.PhiStar.Gegenbauer.gC n x := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero =>
    intro x
    rw [show pG 0 = (1 : Polynomial ℝ) from rfl,
      show Work.FTS.PhiStar.Gegenbauer.gC 0 = (fun _ : ℝ => (1 : ℝ)) from rfl]
    simp
  | one =>
    intro x
    rw [show pG 1 = Polynomial.C 3 * Polynomial.X from rfl,
      show Work.FTS.PhiStar.Gegenbauer.gC 1 = (fun x : ℝ => 3 * x) from rfl]
    simp
  | more k ihk ihk1 =>
    intro x
    rw [show pG (k + 2) = Polynomial.C (((k : ℝ) + 2)⁻¹) *
        (Polynomial.C (2 * ((k : ℝ) + 5 / 2)) * (Polynomial.X * pG (k + 1))
          - Polynomial.C ((k : ℝ) + 3) * pG k) from rfl]
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_X,
      ihk x, ihk1 x]
    rw [show Work.FTS.PhiStar.Gegenbauer.gC (k + 2) x
        = (2 * ((k : ℝ) + 5 / 2) * x * Work.FTS.PhiStar.Gegenbauer.gC (k + 1) x
            - ((k : ℝ) + 3) * Work.FTS.PhiStar.Gegenbauer.gC k x) / ((k : ℝ) + 2) from rfl]
    rw [div_eq_inv_mul]
    ring

lemma pG_ne_zero (n : ℕ) : pG n ≠ 0 := by
  intro h
  have h1 : Work.FTS.PhiStar.Gegenbauer.gC n 1 = 0 := by
    rw [← pG_eval n 1, h]
    simp
  rw [gC_one n] at h1
  have hpos : (0 : ℝ) < ((n : ℝ) + 1) * ((n : ℝ) + 2) / 2 := by positivity
  linarith

/-- A nonzero polynomial has finitely many real roots, so `gC (2m+1)` has finitely many
zeros. -/
lemma gC_roots_finite (m : ℕ) :
    {x : ℝ | Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) x = 0}.Finite := by
  have h := Polynomial.finite_setOfPred_isRoot (pG_ne_zero (2 * m + 1))
  simpa only [Set.mem_setOf_eq, Polynomial.IsRoot, pG_eval] using h

/-- The mode weight `θ ↦ eFam m θ · cos θ` vanishes only on a finite subset of `Iθ`. -/
lemma eFam_zeroSet_finite (m : ℕ) :
    {θ ∈ Work.Spaces.Iθ |
      Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ = 0}.Finite := by
  have hsub : {θ ∈ Work.Spaces.Iθ |
        Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ = 0} ⊆
      ({θ ∈ Work.Spaces.Iθ | Real.cos θ = 0} ∪
        {θ ∈ Work.Spaces.Iθ |
          Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin θ) = 0}) := by
    rintro θ ⟨hθ, h0⟩
    rw [Work.FTS.PhiStar.Gegenbauer.eFam] at h0
    simp only [mul_eq_zero] at h0
    rcases h0 with (h | h) | h
    · left; exact ⟨hθ, h⟩
    · right; exact ⟨hθ, h⟩
    · left; exact ⟨hθ, h⟩
  refine Set.Finite.subset (Set.Finite.union ?_ ?_) hsub
  · refine Set.Finite.subset (Set.finite_singleton (Real.pi / 2)) ?_
    rintro θ ⟨hθ, h0⟩
    exact Real.strictAntiOn_cos.injOn
      ⟨hθ.1, le_trans hθ.2 (by linarith [Real.pi_pos])⟩
      ⟨by positivity, by linarith [Real.pi_pos]⟩
      (by rw [h0, Real.cos_pi_div_two])
  · refine Set.Finite.subset ((gC_roots_finite m).image Real.arcsin) ?_
    rintro θ ⟨hθ, h0⟩
    exact ⟨Real.sin θ, h0, Real.arcsin_sin (by linarith [hθ.1, Real.pi_pos]) hθ.2⟩

/-- The mode weights vanish only on a null set. -/
lemma eFam_mul_cos_ae_ne_zero (m : ℕ) :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ ≠ 0 := by
  rw [MeasureTheory.ae_iff]
  have hmeas : MeasurableSet {θ : ℝ |
      Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ = 0} :=
    (isClosed_eq (continuous_eFam_mul_cos m) continuous_const).measurableSet
  rw [show {θ : ℝ |
        ¬ Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ ≠ 0}
      = {θ : ℝ | Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ = 0} from by
    ext θ; simp only [Set.mem_setOf_eq, ne_eq, not_not]]
  rw [MeasureTheory.Measure.restrict_apply hmeas]
  rw [show {θ : ℝ | Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ = 0}
        ∩ Work.Spaces.Iθ
      = {θ ∈ Work.Spaces.Iθ |
          Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ = 0} from by
    ext θ
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
    exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩]
  exact (eFam_zeroSet_finite m).measure_zero MeasureTheory.volume

/-! ## The modes as an orthonormal system of `L²(Iθ)` -/

lemma isFiniteMeasure_Iθ :
    MeasureTheory.IsFiniteMeasure (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (Real.pi / 2) from rfl,
    MeasureTheory.isFiniteMeasure_restrict, Real.volume_Icc]
  exact ENNReal.ofReal_ne_top

/-- The squared `L²(Iθ, cos θ dθ)`-norm of the `m`-th Dirichlet mode. -/
def eNorm (m : ℕ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ

lemma eNorm_pos (m : ℕ) : 0 < eNorm m := by
  rw [eNorm, Work.FTS.PhiStar.Gegenbauer.eFam_norm_fts m]
  positivity

lemma continuous_eFam (m : ℕ) :
    Continuous (fun θ : ℝ => Work.FTS.PhiStar.Gegenbauer.eFam m θ) := by
  rw [show Work.FTS.PhiStar.Gegenbauer.eFam m
      = fun θ : ℝ => Real.cos θ
          * Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin θ) from rfl]
  exact Real.continuous_cos.mul
    ((Work.FTS.PhiStar.Gegenbauer.contDiff_gC (2 * m + 1)).continuous.comp
      Real.continuous_sin)

/-- The normalised representative `(‖eFam m‖)⁻¹ · √(cos ·) · eFam m` of the `m`-th mode in
`L²(Iθ)`. -/
def eFun (m : ℕ) : ℝ → ℝ :=
  fun θ => (Real.sqrt (eNorm m))⁻¹ *
    (Real.sqrt (Real.cos θ) * Work.FTS.PhiStar.Gegenbauer.eFam m θ)

lemma continuous_eFun (m : ℕ) : Continuous (eFun m) := by
  refine continuous_const.mul ?_
  exact (Real.continuous_sqrt.comp Real.continuous_cos).mul (continuous_eFam m)

lemma eFun_memLp (m : ℕ) :
    MeasureTheory.MemLp (eFun m) 2 (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  haveI := isFiniteMeasure_Iθ
  obtain ⟨C, hC⟩ := IsCompact.exists_bound_of_continuousOn (s := Work.Spaces.Iθ)
    isCompact_Icc (continuous_eFun m).continuousOn
  refine MeasureTheory.MemLp.of_bound (continuous_eFun m).aestronglyMeasurable C ?_
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Iθ]
  filter_upwards with θ hθ
  exact hC θ hθ

/-- The normalised modes, as elements of `L²(Iθ)`. -/
def eLp (m : ℕ) : MeasureTheory.Lp ℝ 2 (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
  MeasureTheory.MemLp.toLp (eFun m) (eFun_memLp m)

lemma eLp_coe (m : ℕ) :
    (eLp m : ℝ → ℝ) =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ] eFun m :=
  MeasureTheory.MemLp.coeFn_toLp (eFun_memLp m)

/-- The normalised Dirichlet modes are orthonormal in `L²(Iθ)`. -/
lemma eLp_orthonormal : Orthonormal ℝ eLp := by
  rw [orthonormal_iff_ite]
  intro n m
  rw [MeasureTheory.L2.inner_def]
  have hone : (fun a => inner ℝ ((eLp n : ℝ → ℝ) a) ((eLp m : ℝ → ℝ) a))
      =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
        (fun a => eFun n a * eFun m a) := by
    filter_upwards [eLp_coe n, eLp_coe m] with a ha hb
    rw [ha, hb, Real.inner_apply]
  rw [MeasureTheory.integral_congr_ae hone]
  have hsplit : (∫ a, eFun n a * eFun m a
        ∂MeasureTheory.volume.restrict Work.Spaces.Iθ)
      = (Real.sqrt (eNorm n))⁻¹ * ((Real.sqrt (eNorm m))⁻¹ *
          ∫ a, (Real.sqrt (Real.cos a) * Work.FTS.PhiStar.Gegenbauer.eFam n a)
              * (Real.sqrt (Real.cos a) * Work.FTS.PhiStar.Gegenbauer.eFam m a)
            ∂MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    have hpt : (fun a => eFun n a * eFun m a)
        = fun a => (Real.sqrt (eNorm n))⁻¹ * ((Real.sqrt (eNorm m))⁻¹ *
            ((Real.sqrt (Real.cos a) * Work.FTS.PhiStar.Gegenbauer.eFam n a)
              * (Real.sqrt (Real.cos a) * Work.FTS.PhiStar.Gegenbauer.eFam m a))) := by
      funext a
      simp only [eFun]
      ring
    rw [hpt, MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  rw [hsplit]
  have hII : (∫ a, (Real.sqrt (Real.cos a) * Work.FTS.PhiStar.Gegenbauer.eFam n a)
        * (Real.sqrt (Real.cos a) * Work.FTS.PhiStar.Gegenbauer.eFam m a)
        ∂MeasureTheory.volume.restrict Work.Spaces.Iθ)
      = ∫ a in Work.Spaces.Iθ,
          Work.FTS.PhiStar.Gegenbauer.eFam n a
            * Work.FTS.PhiStar.Gegenbauer.eFam m a * Real.cos a := by
    refine MeasureTheory.integral_congr_ae ?_
    show ∀ᵐ a ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      (Real.sqrt (Real.cos a) * Work.FTS.PhiStar.Gegenbauer.eFam n a)
        * (Real.sqrt (Real.cos a) * Work.FTS.PhiStar.Gegenbauer.eFam m a)
        = Work.FTS.PhiStar.Gegenbauer.eFam n a
            * Work.FTS.PhiStar.Gegenbauer.eFam m a * Real.cos a
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Iθ]
    filter_upwards with a ha
    have hc : 0 ≤ Real.cos a :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [ha.1, Real.pi_pos], ha.2⟩
    conv_rhs => rw [← Real.sq_sqrt hc]
    ring
  rw [hII]
  by_cases hnm : n = m
  · rw [if_pos hnm, hnm]
    have hdiag : (∫ a in Work.Spaces.Iθ,
          Work.FTS.PhiStar.Gegenbauer.eFam m a
            * Work.FTS.PhiStar.Gegenbauer.eFam m a * Real.cos a) = eNorm m := by
      rw [eNorm]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Iθ (fun a _ => ?_)
      ring
    rw [hdiag]
    have hsq : Real.sqrt (eNorm m) * Real.sqrt (eNorm m) = eNorm m := by
      rw [← sq, Real.sq_sqrt (le_of_lt (eNorm_pos m))]
    have hN : eNorm m ≠ 0 := ne_of_gt (eNorm_pos m)
    calc (Real.sqrt (eNorm m))⁻¹ * ((Real.sqrt (eNorm m))⁻¹ * eNorm m)
        = ((Real.sqrt (eNorm m))⁻¹ * (Real.sqrt (eNorm m))⁻¹) * eNorm m := by ring
      _ = (Real.sqrt (eNorm m) * Real.sqrt (eNorm m))⁻¹ * eNorm m := by rw [mul_inv]
      _ = (eNorm m)⁻¹ * eNorm m := by rw [hsq]
      _ = 1 := inv_mul_cancel₀ hN
  · rw [if_neg hnm, eFam_orthogonal_Iθ n m hnm]
    ring

/-- The inner product of the `m`-th normalised mode with the `L²`-class of an arbitrary
function `f`. -/
lemma inner_eLp (m : ℕ) {f : ℝ → ℝ}
    (hf : MeasureTheory.MemLp f 2 (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :
    inner ℝ (eLp m) (hf.toLp f)
      = (Real.sqrt (eNorm m))⁻¹ *
        (∫ θ in Work.Spaces.Iθ,
          (Real.sqrt (Real.cos θ) * Work.FTS.PhiStar.Gegenbauer.eFam m θ) * f θ) := by
  rw [MeasureTheory.L2.inner_def]
  have hone : (fun a => inner ℝ ((eLp m : ℝ → ℝ) a) ((hf.toLp f : ℝ → ℝ) a))
      =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
        (fun a => (Real.sqrt (eNorm m))⁻¹ *
          ((Real.sqrt (Real.cos a) * Work.FTS.PhiStar.Gegenbauer.eFam m a) * f a)) := by
    filter_upwards [eLp_coe m, MeasureTheory.MemLp.coeFn_toLp hf] with a ha hb
    rw [ha, hb, Real.inner_apply]
    simp only [eFun]
    ring
  rw [MeasureTheory.integral_congr_ae hone, MeasureTheory.integral_const_mul]

/-! ## The mode coefficients -/

/-- The interval integral over `(0, π/2)` equals the set integral over `Iθ`. -/
lemma intervalIntegral_eq_setIntegral (g : ℝ → ℝ) :
    (∫ θ in (0 : ℝ)..(Real.pi / 2), g θ) = ∫ θ in Work.Spaces.Iθ, g θ := by
  rw [intervalIntegral.integral_of_le
    (by linarith [Real.pi_pos] : (0 : ℝ) ≤ Real.pi / 2)]
  rw [Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc]

/-- The numerator of `cmode m F z`, written in the `√(cos ·)`-form matching the `L²` inner
product. -/
def bInt (m : ℕ) (F : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ,
    (Real.sqrt (Real.cos θ) * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
      * (Real.sqrt (Real.cos θ) * F z θ)

/-- `cmode m F z` is the quotient `bInt m F z / eNorm m`. -/
lemma cmode_eq (m : ℕ) (F : ℝ → ℝ → ℝ) (z : ℝ) :
    Work.FTS.PhiStar.Series.cmode m F z = bInt m F z / eNorm m := by
  rw [Work.FTS.PhiStar.Series.cmode, bInt, eNorm]
  congr 1
  · rw [intervalIntegral_eq_setIntegral
      (fun θ => F z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ)]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Iθ (fun θ hθ => ?_)
    have hc : 0 ≤ Real.cos θ :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    conv_lhs => rw [← Real.sq_sqrt hc]
    ring
  · rw [intervalIntegral_eq_setIntegral
      (fun θ => Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ)]

/-! ## Bessel's inequality -/

theorem cmode_bessel (F : ℝ → ℝ → ℝ) (z : ℝ) (N : ℕ) :
    ENNReal.ofReal (∑ m ∈ Finset.range (N + 1),
        (∫ θ in Work.Spaces.Iθ, Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ)
          * (Work.FTS.PhiStar.Series.cmode m F z) ^ 2)
      ≤ ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (F z θ ^ 2 * Real.cos θ) := by
  set A : ENNReal :=
    ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (F z θ ^ 2 * Real.cos θ) with hA
  set K : ℝ → ℝ := fun θ => Real.sqrt (Real.cos θ) * F z θ with hK
  change ENNReal.ofReal (∑ m ∈ Finset.range (N + 1),
      eNorm m * (Work.FTS.PhiStar.Series.cmode m F z) ^ 2) ≤ A
  -- the pointwise identity `K θ ^ 2 = F z θ ^ 2 * cos θ` on `Iθ`
  have hKsq_pt : ∀ θ ∈ Work.Spaces.Iθ, K θ ^ 2 = F z θ ^ 2 * Real.cos θ := by
    intro θ hθ
    have hc : 0 ≤ Real.cos θ :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    rw [hK]
    rw [show (Real.sqrt (Real.cos θ) * F z θ) ^ 2 = Real.cos θ * F z θ ^ 2 by
      rw [mul_pow, Real.sq_sqrt hc]]
    ring
  by_cases hAtop : A = ⊤
  · rw [hAtop]
    exact le_top
  · have hAlt : A < ⊤ := lt_top_iff_ne_top.mpr hAtop
    by_cases hKsm : MeasureTheory.AEStronglyMeasurable K
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)
    · -- the `L²` case: Bessel's inequality
      have hKsq : (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (K θ ^ 2)) = A := by
        rw [hA]
        refine MeasureTheory.lintegral_congr_ae ?_
        show ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
          ENNReal.ofReal (K θ ^ 2) = ENNReal.ofReal (F z θ ^ 2 * Real.cos θ)
        rw [MeasureTheory.ae_restrict_iff' measurableSet_Iθ]
        filter_upwards with θ hθ
        rw [hKsq_pt θ hθ]
      have hKfin : (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (K θ ^ 2)) < ⊤ := by
        rw [hKsq]; exact hAlt
      have hKmem : MeasureTheory.MemLp K 2
          (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
        rw [MeasureTheory.memLp_two_iff_integrable_sq hKsm]
        refine ⟨hKsm.pow 2, ?_⟩
        rw [MeasureTheory.hasFiniteIntegral_iff_norm]
        have heq : (∫⁻ a, ENNReal.ofReal ‖K a ^ 2‖
              ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
            = ∫⁻ a, ENNReal.ofReal (K a ^ 2)
                ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
          refine MeasureTheory.lintegral_congr_ae
            (Filter.Eventually.of_forall (fun a => ?_))
          show ENNReal.ofReal ‖K a ^ 2‖ = ENNReal.ofReal (K a ^ 2)
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (K a))]
        rw [heq]; exact hKfin
      have hbessel : (∑ m ∈ Finset.range (N + 1),
            ‖inner ℝ (eLp m) (hKmem.toLp K)‖ ^ 2) ≤ ‖hKmem.toLp K‖ ^ 2 :=
        Orthonormal.sum_inner_products_le (hKmem.toLp K) (v := eLp)
          (s := Finset.range (N + 1)) eLp_orthonormal
      have hnorm : ‖hKmem.toLp K‖ ^ 2
          = ∫ θ in Work.Spaces.Iθ, F z θ ^ 2 * Real.cos θ := by
        rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
        have h1 : (∫ a, inner ℝ ((hKmem.toLp K : ℝ → ℝ) a)
              ((hKmem.toLp K : ℝ → ℝ) a)
              ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
            = ∫ a, K a ^ 2 ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards [MeasureTheory.MemLp.coeFn_toLp hKmem] with a ha
          rw [ha, Real.inner_apply, sq]
        rw [h1]
        refine MeasureTheory.integral_congr_ae ?_
        show ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
          K θ ^ 2 = F z θ ^ 2 * Real.cos θ
        rw [MeasureTheory.ae_restrict_iff' measurableSet_Iθ]
        filter_upwards with θ hθ
        rw [hKsq_pt θ hθ]
      have hsummand : ∀ m : ℕ, eNorm m * (Work.FTS.PhiStar.Series.cmode m F z) ^ 2
          = ‖inner ℝ (eLp m) (hKmem.toLp K)‖ ^ 2 := by
        intro m
        rw [cmode_eq m F z, inner_eLp m hKmem, Real.norm_eq_abs, sq_abs]
        rw [show (∫ θ in Work.Spaces.Iθ,
              (Real.sqrt (Real.cos θ) * Work.FTS.PhiStar.Gegenbauer.eFam m θ) * K θ)
            = bInt m F z from by rw [bInt, hK]]
        have hN : eNorm m ≠ 0 := ne_of_gt (eNorm_pos m)
        have hs : Real.sqrt (eNorm m) ≠ 0 :=
          ne_of_gt (Real.sqrt_pos.2 (eNorm_pos m))
        field_simp
        rw [Real.sq_sqrt (le_of_lt (eNorm_pos m))]
        ring
      have hmain : (∑ m ∈ Finset.range (N + 1),
            eNorm m * (Work.FTS.PhiStar.Series.cmode m F z) ^ 2)
          ≤ ∫ θ in Work.Spaces.Iθ, F z θ ^ 2 * Real.cos θ := by
        calc (∑ m ∈ Finset.range (N + 1),
              eNorm m * (Work.FTS.PhiStar.Series.cmode m F z) ^ 2)
            = ∑ m ∈ Finset.range (N + 1),
                ‖inner ℝ (eLp m) (hKmem.toLp K)‖ ^ 2 :=
              Finset.sum_congr rfl (fun m _ => hsummand m)
          _ ≤ ‖hKmem.toLp K‖ ^ 2 := hbessel
          _ = ∫ θ in Work.Spaces.Iθ, F z θ ^ 2 * Real.cos θ := hnorm
      have hint : MeasureTheory.Integrable (fun θ => F z θ ^ 2 * Real.cos θ)
          (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
        refine hKmem.integrable_sq.congr ?_
        show ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
          K θ ^ 2 = F z θ ^ 2 * Real.cos θ
        rw [MeasureTheory.ae_restrict_iff' measurableSet_Iθ]
        filter_upwards with θ hθ
        exact hKsq_pt θ hθ
      have hnonneg : 0 ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
          (fun θ => F z θ ^ 2 * Real.cos θ) := by
        show ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
          0 ≤ F z θ ^ 2 * Real.cos θ
        rw [MeasureTheory.ae_restrict_iff' measurableSet_Iθ]
        filter_upwards with θ hθ
        exact mul_nonneg (sq_nonneg _)
          (Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)
      rw [hA, ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
        (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
        (f := fun θ => F z θ ^ 2 * Real.cos θ) hint hnonneg]
      exact ENNReal.ofReal_le_ofReal hmain
    · -- the degenerate case: every mode coefficient vanishes
      have hKnm : ¬ MeasureTheory.AEStronglyMeasurable (fun θ : ℝ => F z θ)
          (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
        intro h
        apply hKsm
        rw [hK]
        have hcont : Continuous (fun θ : ℝ => Real.sqrt (Real.cos θ)) :=
          Real.continuous_sqrt.comp Real.continuous_cos
        exact hcont.aestronglyMeasurable.mul h
      have hbzero : ∀ m : ℕ, bInt m F z = 0 := by
        intro m
        have hne := not_aestronglyMeasurable_mul_eFam hKnm eFam_mul_cos_ae_ne_zero m
        have hzero : (∫ θ in Work.Spaces.Iθ,
            F z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) = 0 :=
          MeasureTheory.integral_non_aestronglyMeasurable hne
        have hbridge : (∫ θ in Work.Spaces.Iθ,
              (Real.sqrt (Real.cos θ) * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
                * (Real.sqrt (Real.cos θ) * F z θ))
            = ∫ θ in Work.Spaces.Iθ,
                F z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ := by
          refine MeasureTheory.setIntegral_congr_fun measurableSet_Iθ (fun θ hθ => ?_)
          have hc : 0 ≤ Real.cos θ :=
            Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
          conv_rhs => rw [← Real.sq_sqrt hc]
          ring
        rw [bInt, hbridge]
        exact hzero
      have hsum0 : (∑ m ∈ Finset.range (N + 1),
          eNorm m * (Work.FTS.PhiStar.Series.cmode m F z) ^ 2) = 0 := by
        refine Finset.sum_eq_zero (fun m _ => ?_)
        rw [cmode_eq m F z, hbzero m, zero_div]
        simp
      rw [hsum0, ENNReal.ofReal_zero]
      exact bot_le

end Work.EllipticEst.ModalSolution
