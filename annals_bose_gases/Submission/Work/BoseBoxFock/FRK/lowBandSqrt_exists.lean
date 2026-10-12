import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Submission.Work.BoseBoxFock.FRK.gramOrthFrame
import Submission.Work.BoseBoxFock.FRK.honestChiFrame
import Submission.Work.BoseBoxFock.FRK.lowBandSqrtDefs
import Submission.Work.BoseBoxFock.PotCubicLowBandAux.bigMAdmGeOne
import Submission.Work.BoseBoxFock.PotCubicLowBandAux.lowBandChiSumAux
import Submission.Work.BoseBoxFock.PotCubicLowBandAux.lowBandCondSumAux
import Submission.Work.BoseBoxFock.PotCubicLowBandAux.lowBandRowSplitAux
import Submission.Work.BoseBoxFock.PotCubicLowBandAux.windowCGAux
import Submission.Work.BoseBoxFock.cIPn_potCubic_eq_pairSet_gen
import Submission.Work.BoseBoxFock.chiRow_muEvalAux
import Submission.Work.BoseBoxFock.envFacts_uniform
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.FRK.lowBandSqrt_exists` — the √-currency bound of the cubic low band

The assembly of the LB1√ leaf: with `ℓ = sideAt μ (a v)`, `Θ = boxRestrictC ℓ Φ`,
`𝓜 = bigM (paramsAt μ (a v)) (a v) μ`, the low-band row

    Row = (∫ star Θ · potCubic(P_H) Θ).re − (∫ star Θ · potCubic(excited) Θ).re

is controlled by the four leaves `lowBandRowSplitAux`, `lowBandChiSumAux`, `lowBandCondSumAux`,
`windowCGAux`, together with the two environment facts `|W1 k| ≤ C·a`, `|fL s| ≤ 1`, the two
frame bounds (`honestChiFrame` for χ, `honestGFrame` for θ), the bridge `⟪Θ,SΘ⟫ ≤ cnPlusC ℓ Θ`
and the explicit arithmetic `(𝓜+1)·n ≤ 4μℓ³𝓜`.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock.FRK

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 3200000

/-! ## 0. Small general facts -/

/-- The `Finset.univ` form of `Finset.sum_le_sum_of_subset_of_nonneg`. -/
lemma sum_le_univ_of_nonneg {α M : Type*} [Fintype α] [AddCommMonoid M] [PartialOrder M]
    [IsOrderedAddMonoid M]
    (s : Finset α) (f : α → M) (h : ∀ x ∈ Finset.univ, x ∉ s → 0 ≤ f x) :
    ∑ x ∈ s, f x ≤ ∑ x ∈ (Finset.univ : Finset α), f x :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s) h

/-- The `pairSet` of a configuration space of at most one particle is empty. -/
lemma pairSet_eq_empty_of_le_one {n : ℕ} (hn : n ≤ 1) : Submission.BoseGases.pairSet n = ∅ := by
  haveI : Subsingleton (Fin n) :=
    ⟨fun a b => Fin.ext (by have ha := a.isLt; have hb := b.isLt; omega)⟩
  rw [Finset.eq_empty_iff_forall_notMem]
  intro p hp
  rw [Submission.BoseGases.pairSet, Finset.mem_filter] at hp
  exact hp.2 (Subsingleton.elim p.1 p.2)

/-- `boxPow` is the corpus's `abox` for positive side. -/
lemma boxPow_eq_abox (n : ℕ) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    Work.MB.boxPow n ℓ = Submission.BoseGases.abox n ℓ := by
  rw [Work.MB.boxPow, Submission.BoseGases.abox_eq_pi_acube]
  exact Set.pi_congr rfl fun i _ => boxL_eq_acube hℓ

/-- The box is invariant under a relabelling of the particles. -/
lemma mem_abox_comp_perm {n : ℕ} {ℓ : ℝ} (σ : Equiv.Perm (Fin n)) (x : Submission.BoseGases.X n) :
    (x ∘ σ) ∈ Submission.BoseGases.abox n ℓ ↔ x ∈ Submission.BoseGases.abox n ℓ := by
  simp only [Submission.BoseGases.mem_abox_iff, Function.comp_apply]
  constructor
  · intro h i; simpa using h (σ.symm i)
  · intro h i; simpa using h (σ i)

/-- `boxRestrictC` of a permutation invariant state is permutation invariant (in the shape the
low-band statements use). -/
lemma boxRestrictC_symm {n : ℕ} (ℓ : ℝ) (Φ : Submission.BoseGases.X n → ℝ)
    (hΦ : Submission.BoseGases.PermInvariant n Φ) :
    ∀ (σ : Equiv.Perm (Fin n)) (x : Submission.BoseGases.X n),
      boxRestrictC ℓ Φ (x ∘ σ) = boxRestrictC ℓ Φ x := by
  classical
  intro σ x
  have key : Φ (x ∘ σ)
        * (Submission.BoseGases.abox n ℓ).indicator (fun _ => (1 : ℝ)) (x ∘ σ)
      = Φ x * (Submission.BoseGases.abox n ℓ).indicator (fun _ => (1 : ℝ)) x := by
    by_cases hx : x ∈ Submission.BoseGases.abox n ℓ
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem ((mem_abox_comp_perm σ x).mpr hx),
        mul_one, mul_one]
      exact hΦ σ x
    · rw [Set.indicator_of_notMem hx,
        Set.indicator_of_notMem (fun hh => hx ((mem_abox_comp_perm σ x).mp hh)),
        mul_zero, mul_zero]
  have hC : boxRestrictC ℓ Φ (x ∘ σ)
      = ((Φ (x ∘ σ)
          * (Submission.BoseGases.abox n ℓ).indicator (fun _ => (1 : ℝ)) (x ∘ σ) : ℝ) : ℂ) := by
    rw [show boxRestrictC ℓ Φ (x ∘ σ) = ((Φ (x ∘ σ) : ℝ) : ℂ)
        * (((Submission.BoseGases.abox n ℓ).indicator (fun _ => (1 : ℝ)) (x ∘ σ) : ℝ) : ℂ)
        from rfl, Complex.ofReal_mul]
  have hC' : boxRestrictC ℓ Φ x
      = ((Φ x * (Submission.BoseGases.abox n ℓ).indicator (fun _ => (1 : ℝ)) x : ℝ) : ℂ) := by
    rw [show boxRestrictC ℓ Φ x = ((Φ x : ℝ) : ℂ)
        * (((Submission.BoseGases.abox n ℓ).indicator (fun _ => (1 : ℝ)) x : ℝ) : ℂ)
        from rfl, Complex.ofReal_mul]
  rw [hC, hC', key]

/-- `f_L` is bounded by `1` in absolute value (it is a `LowCut` of the rescaled momentum). -/
lemma fLFS_abs_le_one (fc : Work.BoseBoxFix.LowCut) (KL μ a : ℝ) (k : ℝ³) :
    |Work.BoseFixR.fLFS fc KL μ a k| ≤ 1 := by
  rw [Work.BoseFixR.fLFS, abs_le]
  exact ⟨by linarith [fc.nonneg (‖k‖ / (KL * Real.sqrt (μ * a)))],
    fc.le_one (‖k‖ / (KL * Real.sqrt (μ * a)))⟩

/-- `√x·√y = √(xy)` for nonnegative `x`. -/
lemma sqrt_mul_sqrt {x y : ℝ} (hx : 0 ≤ x) : Real.sqrt x * Real.sqrt y = Real.sqrt (x * y) :=
  (Real.sqrt_mul hx y).symm

/-- `√2·√2 = 2`. -/
lemma sqrt_two_mul_sqrt_two : Real.sqrt 2 * Real.sqrt 2 = (2 : ℝ) := by
  rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

/-- **The square-root product of the two sum bounds.** -/
lemma sqrt_prod_le {A B C Z₁ Z₂ V SX SY : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hZ₁ : 0 ≤ Z₁) (hZ₂ : 0 ≤ Z₂) (hV : 0 ≤ V)
    (h1 : SX ≤ A * (B ^ 2 * Z₁ * V)) (h2 : SY ≤ A * (C * Z₂ * V)) :
    Real.sqrt SX * Real.sqrt SY ≤ A * B * Real.sqrt C * Real.sqrt (Z₁ * Z₂) * V := by
  have hAnn : 0 ≤ A * (B ^ 2 * Z₁ * V) :=
    mul_nonneg hA (mul_nonneg (mul_nonneg (pow_nonneg hB 2) hZ₁) hV)
  have hBnn : 0 ≤ A * (C * Z₂ * V) := mul_nonneg hA (mul_nonneg (mul_nonneg hC hZ₂) hV)
  have hRnn : 0 ≤ A * B * Real.sqrt C * Real.sqrt (Z₁ * Z₂) * V := by positivity
  rcases le_or_gt 0 SX with hSX0 | hSX0
  · rcases le_or_gt 0 SY with hSY0 | hSY0
    · have hL2 : (Real.sqrt SX * Real.sqrt SY) ^ 2 = SX * SY := by
        rw [mul_pow, Real.sq_sqrt hSX0, Real.sq_sqrt hSY0]
      have hR2 : (A * B * Real.sqrt C * Real.sqrt (Z₁ * Z₂) * V) ^ 2
          = A ^ 2 * (B ^ 2) * C * (Z₁ * Z₂) * V ^ 2 := by
        rw [mul_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt hC,
          Real.sq_sqrt (mul_nonneg hZ₁ hZ₂)]
      have hLnn : 0 ≤ Real.sqrt SX * Real.sqrt SY :=
        mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      have hsq : (Real.sqrt SX * Real.sqrt SY) ^ 2
          ≤ (A * B * Real.sqrt C * Real.sqrt (Z₁ * Z₂) * V) ^ 2 := by
        rw [hL2, hR2]
        have h3 : SX * SY ≤ (A * (B ^ 2 * Z₁ * V)) * (A * (C * Z₂ * V)) :=
          mul_le_mul h1 h2 hSY0 hAnn
        have hexp : (A * (B ^ 2 * Z₁ * V)) * (A * (C * Z₂ * V))
            = A ^ 2 * (B ^ 2) * C * (Z₁ * Z₂) * V ^ 2 := by ring
        rw [hexp] at h3
        exact h3
      have := (sq_le_sq.mp hsq)
      simpa only [abs_of_nonneg hLnn, abs_of_nonneg hRnn] using this
    · rw [Real.sqrt_eq_zero_of_nonpos hSY0.le, mul_zero]
      exact hRnn
  · rw [Real.sqrt_eq_zero_of_nonpos hSX0.le, zero_mul]
    exact hRnn

/-- `cIPn` of a vector with itself has nonnegative real part. -/
lemma cIPn_self_re_nonneg {n : ℕ} (X : Work.BoseDict.Xn n → ℂ) :
    0 ≤ (Work.BoseDict.cIPn n X X).re := by
  rw [cIPn_self_re]
  exact MeasureTheory.integral_nonneg fun y => by positivity

/-- The `excited`-finset sum is the sum over the subtype of excited labels. -/
lemma sum_excited_eq_sum_subtype {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode] (F : Mode → ℝ) :
    ∑ s ∈ Work.BoseB7.excited Mode, F s
      = ∑ s : {s : Mode // s ∈ Work.BoseB7.excited Mode}, F s.1 :=
  Finset.sum_subtype (Work.BoseB7.excited Mode) (fun x => Iff.rfl) F

/-- Membership in `excited` is exactly being different from the zero label. -/
lemma mem_excited_iff {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (s : Mode) : s ∈ Work.BoseB7.excited Mode ↔ s ≠ 0 := by
  simp [Work.BoseB7.excited]

/-- The sum over the excited labels, shifted by `k`, is bounded by the full lattice sum. -/
lemma sum_shift_le_univ {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (k : G) (g : G → ℝ) (hgnn : ∀ j, 0 ≤ g j) :
    ∑ s ∈ Work.BoseB7.excited G, g (s - k) ≤ ∑ j : G, g j := by
  have hinj : Set.InjOn (fun s : G => s - k) (Work.BoseB7.excited G) := by
    intro x _ y _ h
    exact add_right_cancel (by simpa only [sub_eq_add_neg] using h :
      x + (-k) = y + (-k))
  rw [← Finset.sum_image (f := g) (g := fun s : G => s - k) hinj]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun x _ _ => hgnn x)

/-! ## 1. The `cIPn` ↔ box-integral bridge -/

/-- `cIPn` against a box-supported state is the box integral of the real part. -/
theorem cIPn_boxT0_re_eq_setIntegral {m n : ℕ} [NeZero m] {ℓ : ℝ} (hℓ : 0 < ℓ)
    {e : Fin m → Ω → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    {Θ : Work.BoseDict.Xn n → ℂ} (hΘm : Measurable Θ)
    (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C)
    (hΘsupp : Function.support Θ ⊆ Submission.BoseGases.abox n ℓ) :
    (Work.BoseDict.cIPn n Θ
        (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m) Θ)).re
      = ∫ x in Submission.BoseGases.abox n ℓ,
          (star (Θ x) * Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m) Θ x).re := by
  classical
  set S : Work.BoseDict.Xn n → ℂ :=
    Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m) Θ with hSdef
  obtain ⟨Cθ, hCθ⟩ := hΘb
  obtain ⟨hSmeas, ⟨CS, _hCS0, hCS⟩, _hSsupp⟩ :=
    (Work.MB.boxSlotSum_bdd (d := n) hmeas hbdd hsupp
      (Work.BoseBoxFock.boxT0 m)).2 Θ hΘm ⟨Cθ, hCθ⟩
  have hzero : ∀ x, x ∉ Submission.BoseGases.abox n ℓ →
      (starRingEnd ℂ) (Θ x) * S x = 0 := by
    intro x hx
    have h0 : Θ x = 0 := by
      by_contra h
      exact hx (hΘsupp (Function.mem_support.mpr h))
    rw [h0, map_zero, zero_mul]
  have hbox : (∫ x, (starRingEnd ℂ) (Θ x) * S x)
      = ∫ x in Submission.BoseGases.abox n ℓ, (starRingEnd ℂ) (Θ x) * S x :=
    (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      (s := Submission.BoseGases.abox n ℓ)
      (f := fun x => (starRingEnd ℂ) (Θ x) * S x) hzero).symm
  -- integrability of the integrand on the (finite measure) box
  haveI hfin : IsFiniteMeasure
      ((volume : Measure (Work.BoseDict.Xn n)).restrict (Submission.BoseGases.abox n ℓ)) := by
    rw [isFiniteMeasure_restrict]
    exact (Submission.BoseGases.abox_lt_top n ℓ hℓ.le).ne
  have hInt : Integrable (fun x => (starRingEnd ℂ) (Θ x) * S x)
      ((volume : Measure (Work.BoseDict.Xn n)).restrict (Submission.BoseGases.abox n ℓ)) :=
    Integrable.of_bound
      ((Complex.continuous_conj.measurable.comp hΘm).mul hSmeas).aestronglyMeasurable
      (max Cθ 0 * max CS 0)
      (Filter.Eventually.of_forall fun x => by
        rw [norm_mul, starRingEnd_apply, norm_star]
        exact mul_le_mul (hCθ x |>.trans (le_max_left _ _)) (hCS x |>.trans (le_max_left _ _))
          (norm_nonneg _) (le_trans (norm_nonneg _) (hCθ x |>.trans (le_max_left _ _))))
  rw [Work.BoseDict.cIPn, hbox]
  have hre := ContinuousLinearMap.integral_comp_comm Complex.reCLM hInt
  simp only [Complex.reCLM_apply] at hre
  rw [← hre]
  rfl

/-! ## 2. The χ-sum bound -/

/-- **The weighted χ-sum.** -/
lemma chiSumBound {m d : ℕ} [NeZero m] {ℓ 𝓜 V : ℝ} (hℓ : 0 < ℓ) (h𝓜 : 0 ≤ 𝓜)
    {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    {e : Fin m → Ω → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (horth : ∀ l l', (∫ z : Ω, star (e l z) * e l' z) = (if l = l' then (1 : ℂ) else 0))
    (f : Mode → Fin m → ℝ) (PHs : Finset Mode) (E : Work.BoseB7.Q3Env Mode)
    (C_B : ℝ) (hC_B : 0 ≤ C_B)
    (hframe : ∀ w : Fin m → ℝ,
      ∑ k : Mode, (Work.BoseB4.gram (f k) w) ^ 2 ≤ C_B * ∑ l : Fin m, (w l) ^ 2)
    (hf0 : ∀ k : Mode, f k 0 = 0)
    (Ca : ℝ) (hCa : 0 ≤ Ca) (hfL : ∀ s : Mode, |E.fL s| ≤ 1)
    (hW1 : ∀ k : Mode, |E.W1 k| ≤ Ca)
    {Θ : Work.BoseDict.Xn (d + 2) → ℂ} (hΘm : Measurable Θ)
    (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C)
    (hΘsupp : Function.support Θ ⊆ Work.MB.boxPow (d + 2) ℓ)
    (hΘsym : ∀ (σ : Equiv.Perm (Fin (d + 2))) (x : Work.BoseDict.Xn (d + 2)),
      Θ (x ∘ σ) = Θ x)
    (hVnn : 0 ≤ V)
    (hS : (Work.BoseDict.cIPn (d + 2) Θ
        (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m) Θ)).re ≤ V)
    (hS2 : (Work.BoseDict.cIPn (d + 2) Θ
        (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m)
          (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m) Θ))).re ≤ 𝓜 * V) :
    (∑ s ∈ Work.BoseB7.excited Mode, ∑ k ∈ Work.BoseB7.excited Mode \ PHs,
        |E.fL s| * |E.W1 k| *
          (Work.BoseDict.cIPn d
            (Work.BoseDict.boxAnnOf e (f (s - k)) d
              (Work.BoseDict.boxAnnOf e (f k) (d + 1) Θ))
            (Work.BoseDict.boxAnnOf e (f (s - k)) d
              (Work.BoseDict.boxAnnOf e (f k) (d + 1) Θ))).re)
      ≤ Ca * (C_B ^ 2 * (𝓜 + 1) * V) := by
  classical
  have hchi := Work.BoseBoxFock.PotCubicLowBandAux.lowBandChiSumAux (n := d) (ℓ := ℓ) (𝓜 := 𝓜)
    (V := V) hℓ h𝓜 hmeas hbdd hsupp horth f C_B hC_B hframe hf0 hΘm hΘb hΘsupp hΘsym hVnn hS hS2
  have hstep1 : (∑ s ∈ Work.BoseB7.excited Mode, ∑ k ∈ Work.BoseB7.excited Mode \ PHs,
        |E.fL s| * |E.W1 k| *
          (Work.BoseDict.cIPn d
            (Work.BoseDict.boxAnnOf e (f (s - k)) d
              (Work.BoseDict.boxAnnOf e (f k) (d + 1) Θ))
            (Work.BoseDict.boxAnnOf e (f (s - k)) d
              (Work.BoseDict.boxAnnOf e (f k) (d + 1) Θ))).re)
      ≤ Ca * (∑ s ∈ Work.BoseB7.excited Mode, ∑ k ∈ Work.BoseB7.excited Mode \ PHs,
          (Work.BoseDict.cIPn d
            (Work.BoseDict.boxAnnOf e (f (s - k)) d
              (Work.BoseDict.boxAnnOf e (f k) (d + 1) Θ))
            (Work.BoseDict.boxAnnOf e (f (s - k)) d
              (Work.BoseDict.boxAnnOf e (f k) (d + 1) Θ))).re) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun s _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    have h1 : |E.fL s| ≤ 1 := hfL s
    have h2 : |E.W1 k| ≤ Ca := hW1 k
    have h3 : 0 ≤ (Work.BoseDict.cIPn d
        (Work.BoseDict.boxAnnOf e (f (s - k)) d
          (Work.BoseDict.boxAnnOf e (f k) (d + 1) Θ))
        (Work.BoseDict.boxAnnOf e (f (s - k)) d
          (Work.BoseDict.boxAnnOf e (f k) (d + 1) Θ))).re := cIPn_self_re_nonneg _
    calc |E.fL s| * |E.W1 k| * (Work.BoseDict.cIPn d
          (Work.BoseDict.boxAnnOf e (f (s - k)) d
            (Work.BoseDict.boxAnnOf e (f k) (d + 1) Θ))
          (Work.BoseDict.boxAnnOf e (f (s - k)) d
            (Work.BoseDict.boxAnnOf e (f k) (d + 1) Θ))).re
        ≤ 1 * Ca * (Work.BoseDict.cIPn d
            (Work.BoseDict.boxAnnOf e (f (s - k)) d
              (Work.BoseDict.boxAnnOf e (f k) (d + 1) Θ))
            (Work.BoseDict.boxAnnOf e (f (s - k)) d
              (Work.BoseDict.boxAnnOf e (f k) (d + 1) Θ))).re := by
          refine mul_le_mul (mul_le_mul h1 h2 (abs_nonneg _) ?_) le_rfl h3 (by positivity)
          linarith [abs_nonneg (E.fL s)]
      _ = Ca * (Work.BoseDict.cIPn d
            (Work.BoseDict.boxAnnOf e (f (s - k)) d
              (Work.BoseDict.boxAnnOf e (f k) (d + 1) Θ))
            (Work.BoseDict.boxAnnOf e (f (s - k)) d
              (Work.BoseDict.boxAnnOf e (f k) (d + 1) Θ))).re := by ring
  have hstep2 : (∑ s ∈ Work.BoseB7.excited Mode, ∑ k ∈ Work.BoseB7.excited Mode \ PHs,
        (Work.BoseDict.cIPn d
          (Work.BoseDict.boxAnnOf e (f (s - k)) d
            (Work.BoseDict.boxAnnOf e (f k) (d + 1) Θ))
          (Work.BoseDict.boxAnnOf e (f (s - k)) d
            (Work.BoseDict.boxAnnOf e (f k) (d + 1) Θ))).re)
      ≤ ∑ k : Mode, ∑ k' : Mode,
        (Work.BoseDict.cIPn d
          (Work.BoseDict.boxAnnOf e (f k') d
            (Work.BoseDict.boxAnnOf e (f k) (d + 1) Θ))
          (Work.BoseDict.boxAnnOf e (f k') d
            (Work.BoseDict.boxAnnOf e (f k) (d + 1) Θ))).re := by
    rw [Finset.sum_comm]
    refine le_trans (sum_le_univ_of_nonneg _ _
      (fun k _ _ => Finset.sum_nonneg fun s _ => cIPn_self_re_nonneg _)) ?_
    refine Finset.sum_le_sum fun k _ => ?_
    exact sum_shift_le_univ k (fun j => (Work.BoseDict.cIPn d
      (Work.BoseDict.boxAnnOf e (f j) d (Work.BoseDict.boxAnnOf e (f k) (d + 1) Θ))
      (Work.BoseDict.boxAnnOf e (f j) d
        (Work.BoseDict.boxAnnOf e (f k) (d + 1) Θ))).re)
      (fun j => cIPn_self_re_nonneg _)
  calc (∑ s ∈ Work.BoseB7.excited Mode, ∑ k ∈ Work.BoseB7.excited Mode \ PHs,
        |E.fL s| * |E.W1 k| *
          (Work.BoseDict.cIPn d
            (Work.BoseDict.boxAnnOf e (f (s - k)) d
              (Work.BoseDict.boxAnnOf e (f k) (d + 1) Θ))
            (Work.BoseDict.boxAnnOf e (f (s - k)) d
              (Work.BoseDict.boxAnnOf e (f k) (d + 1) Θ))).re)
      ≤ Ca * (∑ s ∈ Work.BoseB7.excited Mode, ∑ k ∈ Work.BoseB7.excited Mode \ PHs,
          (Work.BoseDict.cIPn d
            (Work.BoseDict.boxAnnOf e (f (s - k)) d
              (Work.BoseDict.boxAnnOf e (f k) (d + 1) Θ))
            (Work.BoseDict.boxAnnOf e (f (s - k)) d
              (Work.BoseDict.boxAnnOf e (f k) (d + 1) Θ))).re) := hstep1
    _ ≤ Ca * (∑ k : Mode, ∑ k' : Mode,
        (Work.BoseDict.cIPn d
          (Work.BoseDict.boxAnnOf e (f k') d
            (Work.BoseDict.boxAnnOf e (f k) (d + 1) Θ))
          (Work.BoseDict.boxAnnOf e (f k') d
            (Work.BoseDict.boxAnnOf e (f k) (d + 1) Θ))).re) :=
        mul_le_mul_of_nonneg_left hstep2 hCa
    _ ≤ Ca * (C_B ^ 2 * (𝓜 + 1) * V) := mul_le_mul_of_nonneg_left hchi hCa

/-- The honest family's `f_L` is bounded by `1`. -/
lemma honestFam_fL_abs_le_one {v : ℝ³ → ℝ} (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ)
    (s : Lab (HM μ).N) :
    |(HonestBoxFam v h fc fu HM μ).E.fL s| ≤ 1 :=
  fLFS_abs_le_one fc
    (((Work.BoseBox.paramsAt μ (BoseGases.a v)).Kl * (Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2)
      ^ (-(1 : ℝ))) μ (BoseGases.a v) _

/-- The degenerate case: the row vanishes for at most one particle. -/
lemma lowBandRowDegLeOne {m n : ℕ} [NeZero m] {ℓ : ℝ}
    {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    {e : Fin m → Ω → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (horth : ∀ l l', (∫ z : Ω, star (e l z) * e l' z) = (if l = l' then (1 : ℂ) else 0))
    (f g : Mode → Fin m → ℝ) (PHs : Finset Mode) (E : Work.BoseB7.Q3Env Mode)
    {Θ : Work.BoseDict.Xn n → ℂ} (hΘm : Measurable Θ)
    (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C) (hn : n ≤ 1) :
    (∫ x : Work.BoseDict.Xn n, star (Θ x) *
        Work.BoseBoxFock.potCubic (fun T => Work.BoseDict.boxSlotSum e T) f g PHs E Θ x).re
      - (∫ x : Work.BoseDict.Xn n, star (Θ x) *
        Work.BoseBoxFock.potCubic (fun T => Work.BoseDict.boxSlotSum e T) f g
          (Work.BoseB7.excited Mode) E Θ x).re = 0 := by
  have key : ∀ (PHs : Finset Mode),
      (∫ x : Work.BoseDict.Xn n, star (Θ x) *
        Work.BoseBoxFock.potCubic (fun T => Work.BoseDict.boxSlotSum e T) f g PHs E Θ x) = 0 := by
    intro PHs
    have h := cIPn_potCubic_eq_pairSet_gen (n := n) e hmeas hbdd hsupp horth f g PHs E Θ hΘm hΘb
    rw [Work.BoseDict.cIPn] at h
    rw [pairSet_eq_empty_of_le_one hn] at h
    simp [Work.BoseDict.cIPn] at h
    exact h
  rw [key PHs, key (Work.BoseB7.excited Mode)]
  simp

/-- **The weighted θ-sum**, from the condensate-sum leaf and the weight bounds. -/
lemma thetaSumBound {m d : ℕ} [NeZero m] {ℓ 𝓜 V : ℝ} (hℓ : 0 < ℓ) (h𝓜 : 0 ≤ 𝓜)
    {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    {e : Fin m → Ω → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (horth : ∀ l l', (∫ z : Ω, star (e l z) * e l' z) = (if l = l' then (1 : ℂ) else 0))
    {Θ : Work.BoseDict.Xn (d + 2) → ℂ} (hΘm : Measurable Θ)
    (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C)
    (hΘsupp : Function.support Θ ⊆ Work.MB.boxPow (d + 2) ℓ)
    (hΘsym : ∀ (σ : Equiv.Perm (Fin (d + 2))) (x : Work.BoseDict.Xn (d + 2)),
      Θ (x ∘ σ) = Θ x)
    (g : Mode → Fin m → ℝ) (PHs : Finset Mode) (E : Work.BoseB7.Q3Env Mode)
    (Ca : ℝ) (hCa : 0 ≤ Ca) (hfL : ∀ s : Mode, |E.fL s| ≤ 1)
    (hW1 : ∀ k : Mode, |E.W1 k| ≤ Ca) (hVnn : 0 ≤ V)
    (hS : (Work.BoseDict.cIPn (d + 2) Θ
        (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m) Θ)).re ≤ V)
    (hθsum : (∑ s ∈ Work.BoseB7.excited Mode,
        (Work.BoseDict.cIPn d
          (Work.BoseDict.boxAnnOf e (g s) d
            (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m 0) (d + 1) Θ))
          (Work.BoseDict.boxAnnOf e (g s) d
            (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m 0) (d + 1) Θ))).re)
      ≤ ((d : ℝ) + 2) * V) :
    (∑ s ∈ Work.BoseB7.excited Mode, ∑ k ∈ Work.BoseB7.excited Mode \ PHs,
        |E.fL s| * |E.W1 k| *
          (Work.BoseDict.cIPn d
            (Work.BoseDict.boxAnnOf e (g s) d
              (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m 0) (d + 1) Θ))
            (Work.BoseDict.boxAnnOf e (g s) d
              (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m 0) (d + 1) Θ))).re)
      ≤ Ca * (1 * (((d : ℝ) + 2) * ((Work.BoseB7.excited Mode \ PHs).card : ℝ)) * V) := by
  classical
  set cLB : ℝ := ((Work.BoseB7.excited Mode \ PHs).card : ℝ) with hcLB
  have hcLBnn : 0 ≤ cLB := by rw [hcLB]; exact Nat.cast_nonneg _
  have hkey : (∑ s ∈ Work.BoseB7.excited Mode, ∑ k ∈ Work.BoseB7.excited Mode \ PHs,
        |E.fL s| * |E.W1 k| *
          (Work.BoseDict.cIPn d
            (Work.BoseDict.boxAnnOf e (g s) d
              (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m 0) (d + 1) Θ))
            (Work.BoseDict.boxAnnOf e (g s) d
              (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m 0) (d + 1) Θ))).re)
      ≤ Ca * (cLB * (∑ s ∈ Work.BoseB7.excited Mode,
          (Work.BoseDict.cIPn d
            (Work.BoseDict.boxAnnOf e (g s) d
              (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m 0) (d + 1) Θ))
            (Work.BoseDict.boxAnnOf e (g s) d
              (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m 0) (d + 1) Θ))).re)) := by
    calc (∑ s ∈ Work.BoseB7.excited Mode, ∑ k ∈ Work.BoseB7.excited Mode \ PHs,
          |E.fL s| * |E.W1 k| *
            (Work.BoseDict.cIPn d
              (Work.BoseDict.boxAnnOf e (g s) d
                (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m 0) (d + 1) Θ))
              (Work.BoseDict.boxAnnOf e (g s) d
                (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m 0) (d + 1) Θ))).re)
        ≤ ∑ s ∈ Work.BoseB7.excited Mode, ∑ _k ∈ Work.BoseB7.excited Mode \ PHs,
            Ca * (Work.BoseDict.cIPn d
              (Work.BoseDict.boxAnnOf e (g s) d
                (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m 0) (d + 1) Θ))
              (Work.BoseDict.boxAnnOf e (g s) d
                (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m 0) (d + 1) Θ))).re := by
          refine Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun k _ => ?_
          have h3 : 0 ≤ (Work.BoseDict.cIPn d
              (Work.BoseDict.boxAnnOf e (g s) d
                (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m 0) (d + 1) Θ))
              (Work.BoseDict.boxAnnOf e (g s) d
                (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m 0) (d + 1) Θ))).re :=
            cIPn_self_re_nonneg _
          calc |E.fL s| * |E.W1 k| * (Work.BoseDict.cIPn d
                (Work.BoseDict.boxAnnOf e (g s) d
                  (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m 0) (d + 1) Θ))
                (Work.BoseDict.boxAnnOf e (g s) d
                  (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m 0) (d + 1) Θ))).re
              ≤ 1 * Ca * (Work.BoseDict.cIPn d
                  (Work.BoseDict.boxAnnOf e (g s) d
                    (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m 0) (d + 1) Θ))
                  (Work.BoseDict.boxAnnOf e (g s) d
                    (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m 0) (d + 1) Θ))).re := by
                refine mul_le_mul (mul_le_mul (hfL s) (hW1 k) (abs_nonneg _) ?_) le_rfl h3
                  (by positivity)
                linarith [abs_nonneg (E.fL s)]
            _ = Ca * (Work.BoseDict.cIPn d
                  (Work.BoseDict.boxAnnOf e (g s) d
                    (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m 0) (d + 1) Θ))
                  (Work.BoseDict.boxAnnOf e (g s) d
                    (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m 0) (d + 1) Θ))).re := by
                ring
      _ = ∑ s ∈ Work.BoseB7.excited Mode, cLB * (Ca * (Work.BoseDict.cIPn d
              (Work.BoseDict.boxAnnOf e (g s) d
                (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m 0) (d + 1) Θ))
              (Work.BoseDict.boxAnnOf e (g s) d
                (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m 0) (d + 1) Θ))).re) := by
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [Finset.sum_const, nsmul_eq_mul, hcLB]
      _ = Ca * (cLB * ∑ s ∈ Work.BoseB7.excited Mode, (Work.BoseDict.cIPn d
              (Work.BoseDict.boxAnnOf e (g s) d
                (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m 0) (d + 1) Θ))
              (Work.BoseDict.boxAnnOf e (g s) d
                (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m 0) (d + 1) Θ))).re) := by
          rw [← Finset.mul_sum, ← Finset.mul_sum]
          ring
  calc (∑ s ∈ Work.BoseB7.excited Mode, ∑ k ∈ Work.BoseB7.excited Mode \ PHs,
        |E.fL s| * |E.W1 k| *
          (Work.BoseDict.cIPn d
            (Work.BoseDict.boxAnnOf e (g s) d
              (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m 0) (d + 1) Θ))
            (Work.BoseDict.boxAnnOf e (g s) d
              (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m 0) (d + 1) Θ))).re)
      ≤ Ca * (cLB * (∑ s ∈ Work.BoseB7.excited Mode, (Work.BoseDict.cIPn d
            (Work.BoseDict.boxAnnOf e (g s) d
              (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m 0) (d + 1) Θ))
            (Work.BoseDict.boxAnnOf e (g s) d
              (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m 0) (d + 1) Θ))).re)) := hkey
    _ ≤ Ca * (cLB * (((d : ℝ) + 2) * V)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hθsum hcLBnn) hCa
    _ = Ca * (1 * (((d : ℝ) + 2) * cLB) * V) := by ring
    _ = Ca * (1 * (((d : ℝ) + 2) * ((Work.BoseB7.excited Mode \ PHs).card : ℝ)) * V) := by
        rw [hcLB]

/-! ## 3. The θ-frame bound on the excited labels -/

/-- The honest θ-modes are orthonormal away from the condensate label, hence their frame operator
is dominated by the identity on the excited labels. -/
lemma honestGFrame {v : ℝ³ → ℝ} (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ) :
    ∀ w : Fin (HM μ).m → ℝ,
      (∑ s : {s : Lab (HM μ).N // s ∈ Work.BoseB7.excited (Lab (HM μ).N)},
        (Work.BoseB4.gram ((HM μ).g s.1) w) ^ 2) ≤ 1 * ∑ l : Fin (HM μ).m, (w l) ^ 2 := by
  intro w
  have horth : ∀ s t : {s : Lab (HM μ).N // s ∈ Work.BoseB7.excited (Lab (HM μ).N)},
      Work.BoseB4.gram ((HM μ).g s.1) ((HM μ).g t.1) = if s = t then (1 : ℝ) else 0 := by
    intro s t
    have hs : s.1 ≠ 0 := (mem_excited_iff s.1).mp s.2
    have ht : t.1 ≠ 0 := (mem_excited_iff t.1).mp t.2
    rw [(HM μ).hg s.1 t.1 hs ht]
    by_cases hst : s.1 = t.1
    · rw [if_pos hst, if_pos (Subtype.ext hst)]
    · rw [if_neg hst, if_neg (fun hh => hst (congrArg Subtype.val hh))]
  have h := gramOrthFrame
    (fun s : {s : Lab (HM μ).N // s ∈ Work.BoseB7.excited (Lab (HM μ).N)} => (HM μ).g s.1)
    horth w
  rw [one_mul]
  exact h

/-- **The condensate sum of the low band**, from `lowBandCondSumAux` at the excited labels. -/
lemma honestGSum {m d : ℕ} [NeZero m] {ℓ V : ℝ} (hℓ : 0 < ℓ)
    {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    {e : Fin m → Ω → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (horth : ∀ l l', (∫ z : Ω, star (e l z) * e l' z) = (if l = l' then (1 : ℂ) else 0))
    (g : Mode → Fin m → ℝ)
    (hframe : ∀ w : Fin m → ℝ,
      (∑ s : {s : Mode // s ∈ Work.BoseB7.excited Mode},
        (Work.BoseB4.gram (g s.1) w) ^ 2) ≤ 1 * ∑ l : Fin m, (w l) ^ 2)
    (h0 : ∀ s : Mode, s ≠ 0 → g s 0 = 0)
    {Θ : Work.BoseDict.Xn (d + 2) → ℂ} (hΘm : Measurable Θ)
    (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C)
    (hΘsupp : Function.support Θ ⊆ Work.MB.boxPow (d + 2) ℓ)
    (hΘsym : ∀ (σ : Equiv.Perm (Fin (d + 2))) (x : Work.BoseDict.Xn (d + 2)),
      Θ (x ∘ σ) = Θ x)
    (hS : (Work.BoseDict.cIPn (d + 2) Θ
        (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m) Θ)).re ≤ V) :
    (∑ s ∈ Work.BoseB7.excited Mode,
        (Work.BoseDict.cIPn d
          (Work.BoseDict.boxAnnOf e (g s) d
            (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m 0) (d + 1) Θ))
          (Work.BoseDict.boxAnnOf e (g s) d
            (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m 0) (d + 1) Θ))).re)
      ≤ ((d : ℝ) + 2) * V := by
  classical
  have hcs := Work.BoseBoxFock.PotCubicLowBandAux.lowBandCondSumAux (m := m) (n := d) (ℓ := ℓ)
    (e := e) hℓ hmeas hbdd hsupp horth
    (ι := {s : Mode // s ∈ Work.BoseB7.excited Mode})
    (g := fun s => g s.1) (C_θ := 1) (hC_θ := zero_le_one) (hframe := hframe)
    (h0 := fun s => h0 s.1 ((mem_excited_iff s.1).mp s.2))
    (hΘm := hΘm) (hΘb := hΘb) (hΘsupp := hΘsupp) (hΘsym := hΘsym)
  rw [sum_excited_eq_sum_subtype (F := fun s => (Work.BoseDict.cIPn d
      (Work.BoseDict.boxAnnOf e (g s) d
        (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m 0) (d + 1) Θ))
      (Work.BoseDict.boxAnnOf e (g s) d
        (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m 0) (d + 1) Θ))).re)]
  calc (∑ s : {s : Mode // s ∈ Work.BoseB7.excited Mode},
        (Work.BoseDict.cIPn d
          (Work.BoseDict.boxAnnOf e (g s.1) d
            (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m 0) (d + 1) Θ))
          (Work.BoseDict.boxAnnOf e (g s.1) d
            (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m 0) (d + 1) Θ))).re)
      ≤ 1 * ((d : ℝ) + 2) * (Work.BoseDict.cIPn (d + 2) Θ
          (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m) Θ)).re := hcs
    _ = ((d : ℝ) + 2) * (Work.BoseDict.cIPn (d + 2) Θ
          (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m) Θ)).re := by ring
    _ ≤ ((d : ℝ) + 2) * V := mul_le_mul_of_nonneg_left hS (by positivity)

/-! ## 4. The final assembly -/

/-- **The final assembly**: the row split, the two sum bounds, the square-root product and the
arithmetic. -/
lemma lowBandRowBound {m d : ℕ} [NeZero m] {ℓ a Ca C_B μ 𝓜 γ V : ℝ} (SX SY K : ℝ)
    {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    {e : Fin m → Ω → ℂ} {f g : Mode → Fin m → ℝ} (PHs : Finset Mode) (E : Work.BoseB7.Q3Env Mode)
    {Θ : Work.BoseDict.Xn (d + 2) → ℂ}
    (hℓ : 0 < ℓ) (ha : 0 < a) (hCa : 0 ≤ Ca) (hC_B : 0 ≤ C_B)
    (hμ : 0 < μ) (h𝓜1 : 1 ≤ 𝓜) (hγ : 0 ≤ γ) (hVnn : 0 ≤ V)
    (hnR : (d : ℝ) + 2 ≤ 2 * μ * ℓ ^ 3)
    (hK : 2 * Real.sqrt 2 * Ca * C_B ≤ K * a)
    (hrow : (∫ x : Work.BoseDict.Xn (d + 2), star (Θ x) *
        Work.BoseBoxFock.potCubic (fun T => Work.BoseDict.boxSlotSum e T) f g PHs E Θ x).re
      - (∫ x : Work.BoseDict.Xn (d + 2), star (Θ x) *
        Work.BoseBoxFock.potCubic (fun T => Work.BoseDict.boxSlotSum e T) f g
          (Work.BoseB7.excited Mode) E Θ x).re
      ≤ 2 * ℓ ^ (-(3 : ℝ)) * Real.sqrt SX * Real.sqrt SY)
    (hSX : SX ≤ Ca * (C_B ^ 2 * (𝓜 + 1) * V))
    (hSY : SY ≤ Ca * (1 * (((d : ℝ) + 2) * γ) * V)) :
    (∫ x : Work.BoseDict.Xn (d + 2), star (Θ x) *
        Work.BoseBoxFock.potCubic (fun T => Work.BoseDict.boxSlotSum e T) f g PHs E Θ x).re
      - (∫ x : Work.BoseDict.Xn (d + 2), star (Θ x) *
        Work.BoseBoxFock.potCubic (fun T => Work.BoseDict.boxSlotSum e T) f g
          (Work.BoseB7.excited Mode) E Θ x).re
      ≤ K * (a * (ℓ ^ 3)⁻¹ * Real.sqrt (2 * μ * ℓ ^ 3 * 𝓜 * γ)) * V := by
  have h𝓜nn : 0 ≤ 𝓜 := le_trans zero_le_one h𝓜1
  have hXnn : 0 ≤ μ * ℓ ^ 3 * 𝓜 * γ := by positivity
  have hprod : Real.sqrt SX * Real.sqrt SY
      ≤ Ca * C_B * Real.sqrt (1 : ℝ) * Real.sqrt ((𝓜 + 1) * (((d : ℝ) + 2) * γ)) * V :=
    sqrt_prod_le (A := Ca) (B := C_B) (C := 1) (Z₁ := 𝓜 + 1) (Z₂ := ((d : ℝ) + 2) * γ)
      (V := V) hCa hC_B zero_le_one (by linarith) (mul_nonneg (by positivity) hγ) hVnn hSX hSY
  have hZ : Real.sqrt ((𝓜 + 1) * (((d : ℝ) + 2) * γ)) ≤ 2 * Real.sqrt (μ * ℓ ^ 3 * 𝓜 * γ) := by
    have h4 : (𝓜 + 1) * (((d : ℝ) + 2) * γ) ≤ 4 * (μ * ℓ ^ 3 * 𝓜 * γ) := by
      have h1 : 𝓜 + 1 ≤ 2 * 𝓜 := by linarith
      have h2 : (d : ℝ) + 2 ≤ 2 * μ * ℓ ^ 3 := hnR
      have h3 : 0 ≤ 2 * μ * ℓ ^ 3 := by positivity
      nlinarith [h1, h2, hγ, h𝓜nn, h3, mul_nonneg h3 h𝓜nn, mul_nonneg (mul_nonneg h3 h𝓜nn) hγ,
        mul_le_mul h1 h2 (by linarith : (0:ℝ) ≤ (d:ℝ) + 2) (by linarith : (0:ℝ) ≤ 2 * 𝓜)]
    rw [show (2 : ℝ) * Real.sqrt (μ * ℓ ^ 3 * 𝓜 * γ) = Real.sqrt (4 * (μ * ℓ ^ 3 * 𝓜 * γ)) from by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4),
        show Real.sqrt (4 : ℝ) = 2 from by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]]
    exact Real.sqrt_le_sqrt h4
  have hpow : ℓ ^ (-(3 : ℝ)) = (ℓ ^ 3)⁻¹ := by
    rw [Real.rpow_neg hℓ.le 3]
    simp
  have hK2 : 4 * Ca * C_B ≤ K * a * Real.sqrt 2 := by
    have h1 := mul_le_mul_of_nonneg_right hK (Real.sqrt_nonneg 2)
    have h2 : (2 * Real.sqrt 2 * Ca * C_B) * Real.sqrt 2 = 4 * Ca * C_B := by
      rw [show (2 * Real.sqrt 2 * Ca * C_B) * Real.sqrt 2
          = 2 * (Real.sqrt 2 * Real.sqrt 2) * Ca * C_B by ring, sqrt_two_mul_sqrt_two]
      ring
    rwa [h2] at h1
  have hsqrt1 : Real.sqrt (1 : ℝ) = 1 := Real.sqrt_one
  have h2X : Real.sqrt (2 * μ * ℓ ^ 3 * 𝓜 * γ)
      = Real.sqrt 2 * Real.sqrt (μ * ℓ ^ 3 * 𝓜 * γ) := by
    rw [show 2 * μ * ℓ ^ 3 * 𝓜 * γ = 2 * (μ * ℓ ^ 3 * 𝓜 * γ) by ring,
      Real.sqrt_mul (by norm_num)]
  have hP1 : 2 * ℓ ^ (-(3 : ℝ)) * Real.sqrt SX * Real.sqrt SY
      ≤ 2 * ℓ ^ (-(3 : ℝ)) *
        (Ca * C_B * Real.sqrt (1 : ℝ) * Real.sqrt ((𝓜 + 1) * (((d : ℝ) + 2) * γ)) * V) := by
    rw [show 2 * ℓ ^ (-(3 : ℝ)) * Real.sqrt SX * Real.sqrt SY
        = 2 * ℓ ^ (-(3 : ℝ)) * (Real.sqrt SX * Real.sqrt SY) by ring]
    exact mul_le_mul_of_nonneg_left hprod (by positivity : (0 : ℝ) ≤ 2 * ℓ ^ (-(3 : ℝ)))
  have hP2 : 2 * ℓ ^ (-(3 : ℝ)) *
        (Ca * C_B * Real.sqrt (1 : ℝ) * Real.sqrt ((𝓜 + 1) * (((d : ℝ) + 2) * γ)) * V)
      ≤ 2 * ℓ ^ (-(3 : ℝ)) *
        (Ca * C_B * Real.sqrt (1 : ℝ) * (2 * Real.sqrt (μ * ℓ ^ 3 * 𝓜 * γ)) * V) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity : (0 : ℝ) ≤ 2 * ℓ ^ (-(3 : ℝ)))
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hZ (by positivity : (0:ℝ) ≤ Ca * C_B * Real.sqrt (1:ℝ))) hVnn
  have hP3 : 2 * ℓ ^ (-(3 : ℝ)) *
        (Ca * C_B * Real.sqrt (1 : ℝ) * (2 * Real.sqrt (μ * ℓ ^ 3 * 𝓜 * γ)) * V)
      ≤ K * (a * (ℓ ^ 3)⁻¹ * Real.sqrt (2 * μ * ℓ ^ 3 * 𝓜 * γ)) * V := by
    rw [hpow, hsqrt1, h2X]
    have hstep := mul_le_mul_of_nonneg_right hK2 (Real.sqrt_nonneg (μ * ℓ ^ 3 * 𝓜 * γ))
    have e1 : 2 * (ℓ ^ 3)⁻¹ * (Ca * C_B * 1 * (2 * Real.sqrt (μ * ℓ ^ 3 * 𝓜 * γ)) * V)
        = ((ℓ ^ 3)⁻¹ * V) * (4 * Ca * C_B * Real.sqrt (μ * ℓ ^ 3 * 𝓜 * γ)) := by ring
    have e2 : K * (a * (ℓ ^ 3)⁻¹ * (Real.sqrt 2 * Real.sqrt (μ * ℓ ^ 3 * 𝓜 * γ))) * V
        = ((ℓ ^ 3)⁻¹ * V) * (K * a * Real.sqrt 2 * Real.sqrt (μ * ℓ ^ 3 * 𝓜 * γ)) := by ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_left hstep (by positivity : (0:ℝ) ≤ (ℓ ^ 3)⁻¹ * V)
  exact le_trans hrow (le_trans hP1 (le_trans hP2 hP3))

/-- **The target.** -/
theorem lowBandSqrt_exists (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R) (hav : 0 < BoseGases.a v)
    (fc fu : Work.BoseBoxFix.LowCut) (J : ℝ) (hB3 : Work.BoseBoxFix.NodeB3B v h R fc)
    (Nmin : ℝ → ℕ) :
    ∃ (ε₀ K : ℝ), 0 < ε₀ ∧ Work.BoseBoxFock.FRK.LowBandSqrt v h fc fu J Nmin ε₀ K := by
  obtain ⟨ε₁, C, hε₁, hCnn, hEnv⟩ := envFacts_uniform v h hv hv1 hvrad hR hv_supp hav fc fu
  refine ⟨min ε₁ 1, 2 * Real.sqrt 2 * C * (48 / Real.pi), lt_min hε₁ one_pos, ?_⟩
  intro HM hNmin μ hAdm hJ n Φ hn hpos hlow hspec e hmeas hbdd hsupp horth hint hmem hpin
    hqvec htheta h0pin T_NH hTNH
  have hμ : 0 < μ := hAdm.1
  have hεadm : μ * (BoseGases.a v) ^ 3 ≤ ε₁ := le_trans hAdm.2.1 (min_le_left _ _)
  have ht1 : μ * (BoseGases.a v) ^ 3 ≤ 1 := le_trans hAdm.2.1 (min_le_right _ _)
  obtain ⟨hellpos, hell_eq, _hmu_eq, _hμℓ3, _hellinv, _hbigMle, hW1b, _hW1wb, _hW1w0,
    _hW1w0le, _hW1w0eq, _hcHCF, _hW1par, _hW1wpar, _htaupar, _hchipar⟩ :=
    hEnv HM μ ⟨hμ, hεadm, hAdm.2.2⟩
  have hℓpos : 0 < Work.BoseBox.sideAt μ (BoseGases.a v) := by
    rw [← hell_eq]; exact hellpos
  have hMcge1 : 1 ≤ Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v))
      (BoseGases.a v) μ :=
    Work.BoseBoxFock.PotCubicLowBandAux.bigMAdmGeOne hav hμ ht1
  have hMcnn : 0 ≤ Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v))
      (BoseGases.a v) μ := le_trans zero_le_one hMcge1
  have hVnn : 0 ≤ Submission.BoseGases.cnPlus (Work.BoseBox.sideAt μ (BoseGases.a v))
      (Φ : Submission.BoseGases.X n → ℝ) := cnPlus_nonneg' _ _
  have hsub : (HonestBoxFam v h fc fu HM μ).F.PHset (HonestBoxFam v h fc fu HM μ).E
      ⊆ Work.BoseB7.excited (Lab (HM μ).N) := by
    intro k hk
    rw [Work.BoseB7.FockData.PHset, Finset.mem_filter] at hk
    exact hk.1
  rcases le_or_gt n 1 with hn1 | hn2
  · -- ## the degenerate case `n ≤ 1`
    refine le_trans (b := 0) (le_of_eq ?_) ?_
    · refine lowBandRowDegLeOne (m := (HM μ).m) (ℓ := Work.BoseBox.sideAt μ (BoseGases.a v))
        (Mode := Lab (HM μ).N) (e := e) (f := (HM μ).f) (g := (HM μ).g)
        (PHs := (HonestBoxFam v h fc fu HM μ).F.PHset (HonestBoxFam v h fc fu HM μ).E)
        (E := (HonestBoxFam v h fc fu HM μ).E)
        (Θ := boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v))
          (Φ : Submission.BoseGases.X n → ℝ)) hmeas hbdd hsupp horth ?_ ?_ hn1
      · exact boxRestrictC_measurable _ Φ.contDiff.continuous
      · exact (boxRestrictC_norm_bound hℓpos Φ.contDiff.continuous).imp fun C hC => hC.2
    · apply mul_nonneg
      · apply mul_nonneg
        · positivity
        · exact mul_nonneg (mul_nonneg hav.le (inv_nonneg.mpr (by positivity)))
            (Real.sqrt_nonneg _)
      · exact hVnn
  · -- ## the main case `2 ≤ n`
    obtain ⟨d, hd⟩ : ∃ d, n = d + 2 := ⟨n - 2, by omega⟩
    subst hd
    have hnR : ((d : ℝ) + 2) ≤ 2 * μ * (Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 3 := by
      have h2 := hn; push_cast at h2; linarith
    have hΦc : Continuous (Φ : Submission.BoseGases.X (d + 2) → ℝ) := Φ.contDiff.continuous
    have hΘm : Measurable (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v))
        (Φ : Submission.BoseGases.X (d + 2) → ℝ)) := boxRestrictC_measurable _ hΦc
    have hΘb : ∃ C : ℝ, ∀ x, ‖boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v))
        (Φ : Submission.BoseGases.X (d + 2) → ℝ) x‖ ≤ C :=
      (boxRestrictC_norm_bound hℓpos hΦc).imp fun C hC => hC.2
    have hΘsupp : Function.support (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v))
        (Φ : Submission.BoseGases.X (d + 2) → ℝ)) ⊆ Submission.BoseGases.abox (d + 2)
          (Work.BoseBox.sideAt μ (BoseGases.a v)) :=
      boxRestrictC_support_subset _ _
    have hΘsuppPow : Function.support (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v))
        (Φ : Submission.BoseGases.X (d + 2) → ℝ)) ⊆ Work.MB.boxPow (d + 2)
          (Work.BoseBox.sideAt μ (BoseGases.a v)) := by
      rw [boxPow_eq_abox (d + 2) hℓpos]; exact hΘsupp
    have hΘsym : ∀ (σ : Equiv.Perm (Fin (d + 2))) (x : Submission.BoseGases.X (d + 2)),
        boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v))
          (Φ : Submission.BoseGases.X (d + 2) → ℝ) (x ∘ σ)
          = boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v))
            (Φ : Submission.BoseGases.X (d + 2) → ℝ) x :=
      boxRestrictC_symm _ _ Φ.symm
    have hS : (Work.BoseDict.cIPn (d + 2) (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v))
          (Φ : Submission.BoseGases.X (d + 2) → ℝ))
        (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 (HM μ).m)
          (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v))
            (Φ : Submission.BoseGases.X (d + 2) → ℝ)))).re
        ≤ Submission.BoseGases.cnPlus (Work.BoseBox.sideAt μ (BoseGases.a v))
          (Φ : Submission.BoseGases.X (d + 2) → ℝ) := by
      rw [cIPn_boxT0_re_eq_setIntegral (m := (HM μ).m) (n := d + 2)
        (ℓ := Work.BoseBox.sideAt μ (BoseGases.a v)) (e := e)
        (Θ := boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v))
          (Φ : Submission.BoseGases.X (d + 2) → ℝ)) hℓpos hmeas hbdd hsupp hΘm hΘb hΘsupp]
      have h2 := re_boxSlotSum_boxT0_le_cnPlusC (m := (HM μ).m) (n := d + 2) hℓpos hmeas hbdd
        hsupp horth hint hpin hΘm hΘb hΘsupp
      rwa [cnPlusC_boxRestrictC_eq_cnPlus hℓpos (Φ : Submission.BoseGases.X (d + 2) → ℝ)] at h2
    have hS2 : (Work.BoseDict.cIPn (d + 2) (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v))
          (Φ : Submission.BoseGases.X (d + 2) → ℝ))
        (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 (HM μ).m)
          (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 (HM μ).m)
            (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v))
              (Φ : Submission.BoseGases.X (d + 2) → ℝ))))).re
        ≤ Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ *
          Submission.BoseGases.cnPlus (Work.BoseBox.sideAt μ (BoseGases.a v))
            (Φ : Submission.BoseGases.X (d + 2) → ℝ) := by
      refine le_trans (Work.BoseBoxFock.PotCubicLowBandAux.windowCGAux (m := (HM μ).m) (n := d + 2)
        (ℓ := Work.BoseBox.sideAt μ (BoseGases.a v))
        (𝓜 := Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ)
        hℓpos hMcnn hmeas hbdd hsupp horth hmem hpin Φ.contDiff hspec) ?_
      rw [cnPlusC_boxRestrictC_eq_cnPlus hℓpos (Φ : Submission.BoseGases.X (d + 2) → ℝ)]
    -- the χ-sum bound
    have hSXb := chiSumBound (m := (HM μ).m) (d := d)
        (ℓ := Work.BoseBox.sideAt μ (BoseGases.a v))
        (𝓜 := Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ)
        (V := Submission.BoseGases.cnPlus (Work.BoseBox.sideAt μ (BoseGases.a v))
          (Φ : Submission.BoseGases.X (d + 2) → ℝ))
        (Mode := Lab (HM μ).N) (e := e) (f := (HM μ).f)
        (PHs := (HonestBoxFam v h fc fu HM μ).F.PHset (HonestBoxFam v h fc fu HM μ).E)
        (E := (HonestBoxFam v h fc fu HM μ).E)
        (Θ := boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v))
          (Φ : Submission.BoseGases.X (d + 2) → ℝ))
        (C_B := 48 / Real.pi) (Ca := C * BoseGases.a v)
        (hℓ := hℓpos) (h𝓜 := hMcnn) (hmeas := hmeas) (hbdd := hbdd) (hsupp := hsupp)
        (horth := horth) (hC_B := by positivity) (hframe := honestChiFrame h fc fu HM μ)
        (hf0 := (HM μ).hf0) (hCa := mul_nonneg hCnn hav.le)
        (hfL := fun s => honestFam_fL_abs_le_one (v := v) h fc fu HM μ s) (hW1 := fun k => hW1b k)
        (hΘm := hΘm) (hΘb := hΘb) (hΘsupp := hΘsuppPow) (hΘsym := hΘsym)
        (hVnn := hVnn) (hS := hS) (hS2 := hS2)
    -- the θ-sum bound
    have hθsum := honestGSum (m := (HM μ).m) (d := d)
        (ℓ := Work.BoseBox.sideAt μ (BoseGases.a v))
        (V := Submission.BoseGases.cnPlus (Work.BoseBox.sideAt μ (BoseGases.a v))
          (Φ : Submission.BoseGases.X (d + 2) → ℝ))
        (Mode := Lab (HM μ).N) (e := e) (g := (HM μ).g)
        (Θ := boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v))
          (Φ : Submission.BoseGases.X (d + 2) → ℝ))
        (hℓ := hℓpos) (hmeas := hmeas) (hbdd := hbdd) (hsupp := hsupp) (horth := horth)
        (hframe := honestGFrame HM μ) (h0 := (HM μ).hg0)
        (hΘm := hΘm) (hΘb := hΘb) (hΘsupp := hΘsuppPow) (hΘsym := hΘsym) (hS := hS)
    have hSYb := thetaSumBound (m := (HM μ).m) (d := d)
        (ℓ := Work.BoseBox.sideAt μ (BoseGases.a v))
        (𝓜 := Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ)
        (V := Submission.BoseGases.cnPlus (Work.BoseBox.sideAt μ (BoseGases.a v))
          (Φ : Submission.BoseGases.X (d + 2) → ℝ))
        (Mode := Lab (HM μ).N) (e := e) (g := (HM μ).g)
        (PHs := (HonestBoxFam v h fc fu HM μ).F.PHset (HonestBoxFam v h fc fu HM μ).E)
        (E := (HonestBoxFam v h fc fu HM μ).E)
        (Θ := boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v))
          (Φ : Submission.BoseGases.X (d + 2) → ℝ))
        (Ca := C * BoseGases.a v)
        (hℓ := hℓpos) (h𝓜 := hMcnn) (hmeas := hmeas) (hbdd := hbdd) (hsupp := hsupp)
        (horth := horth) (hCa := mul_nonneg hCnn hav.le)
        (hfL := fun s => honestFam_fL_abs_le_one (v := v) h fc fu HM μ s) (hW1 := fun k => hW1b k)
        (hΘm := hΘm) (hΘb := hΘb) (hΘsupp := hΘsuppPow) (hΘsym := hΘsym)
        (hVnn := hVnn) (hS := hS) (hθsum := hθsum)
    -- the row split
    have hrowb := Work.BoseBoxFock.PotCubicLowBandAux.lowBandRowSplitAux (m := (HM μ).m) (d := d)
        (ℓ := Work.BoseBox.sideAt μ (BoseGases.a v))
        (Mode := Lab (HM μ).N) (e := e) (f := (HM μ).f) (g := (HM μ).g)
        (PHs := (HonestBoxFam v h fc fu HM μ).F.PHset (HonestBoxFam v h fc fu HM μ).E)
        (E := (HonestBoxFam v h fc fu HM μ).E)
        (Θ := boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v))
          (Φ : Submission.BoseGases.X (d + 2) → ℝ))
        hmeas hbdd hsupp horth hmem hsub hellpos hΘm hΘb hΘsuppPow hΘsym
    rw [hell_eq] at hrowb
    exact lowBandRowBound
      (SX := ∑ s ∈ Work.BoseB7.excited (Lab (HM μ).N),
          ∑ k ∈ Work.BoseB7.excited (Lab (HM μ).N) \
            (HonestBoxFam v h fc fu HM μ).F.PHset (HonestBoxFam v h fc fu HM μ).E,
            |(HonestBoxFam v h fc fu HM μ).E.fL s| * |(HonestBoxFam v h fc fu HM μ).E.W1 k| *
              (Work.BoseDict.cIPn d
                (Work.BoseDict.boxAnnOf e ((HM μ).f (s - k)) d
                  (Work.BoseDict.boxAnnOf e ((HM μ).f k) (d + 1)
                    (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v))
                      (Φ : Submission.BoseGases.X (d + 2) → ℝ))))
                (Work.BoseDict.boxAnnOf e ((HM μ).f (s - k)) d
                  (Work.BoseDict.boxAnnOf e ((HM μ).f k) (d + 1)
                    (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v))
                      (Φ : Submission.BoseGases.X (d + 2) → ℝ))))).re)
      (SY := ∑ s ∈ Work.BoseB7.excited (Lab (HM μ).N),
          ∑ k ∈ Work.BoseB7.excited (Lab (HM μ).N) \
            (HonestBoxFam v h fc fu HM μ).F.PHset (HonestBoxFam v h fc fu HM μ).E,
            |(HonestBoxFam v h fc fu HM μ).E.fL s| * |(HonestBoxFam v h fc fu HM μ).E.W1 k| *
              (Work.BoseDict.cIPn d
                (Work.BoseDict.boxAnnOf e ((HM μ).g s) d
                  (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec (HM μ).m 0) (d + 1)
                    (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v))
                      (Φ : Submission.BoseGases.X (d + 2) → ℝ))))
                (Work.BoseDict.boxAnnOf e ((HM μ).g s) d
                  (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec (HM μ).m 0) (d + 1)
                    (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v))
                      (Φ : Submission.BoseGases.X (d + 2) → ℝ))))).re)
      (K := 2 * Real.sqrt 2 * C * (48 / Real.pi))
      (Mode := Lab (HM μ).N) (e := e) (f := (HM μ).f) (g := (HM μ).g)
      (PHs := (HonestBoxFam v h fc fu HM μ).F.PHset (HonestBoxFam v h fc fu HM μ).E)
      (E := (HonestBoxFam v h fc fu HM μ).E)
      (Θ := boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v))
        (Φ : Submission.BoseGases.X (d + 2) → ℝ))
      (Ca := C * BoseGases.a v) (C_B := 48 / Real.pi) (a := BoseGases.a v)
      (ℓ := Work.BoseBox.sideAt μ (BoseGases.a v)) (μ := μ)
      (γ := ((Work.BoseB7.excited (Lab (HM μ).N) \
        (HonestBoxFam v h fc fu HM μ).F.PHset (HonestBoxFam v h fc fu HM μ).E).card : ℝ))
      (V := Submission.BoseGases.cnPlus (Work.BoseBox.sideAt μ (BoseGases.a v))
        (Φ : Submission.BoseGases.X (d + 2) → ℝ))
      (𝓜 := Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ)
      (hℓ := hℓpos) (ha := hav) (hCa := mul_nonneg hCnn hav.le) (hC_B := by positivity)
      (hμ := hμ) (h𝓜1 := hMcge1) (hγ := Nat.cast_nonneg _) (hVnn := hVnn) (hnR := hnR)
      (hK := le_of_eq (by ring))
      (hrow := hrowb) (hSX := hSXb) (hSY := hSYb)
end Work.BoseBoxFock.FRK
