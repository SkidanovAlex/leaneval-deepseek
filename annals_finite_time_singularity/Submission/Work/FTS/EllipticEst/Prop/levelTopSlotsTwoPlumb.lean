/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Prop.levelTopSlotsTwoPlumb`: reusable plumbing for `Prop.levelTopSlotsTwo`

Two groups of elementary lemmas used by the term-by-term bounds of
`Prop.levelTopSlotsTwo`:

* the level-`0` integrand `HkIntegrand α 0 f` in explicit form, its nonnegativity, and the
  transfer of the membership `HkMem α 0 f` from a pointwise domination by an `ℋ^k`-integrand;
* the "a.e. slice inequality ⇒ inequality of the integrals" shape (`HkSq`- and `Tk`-versions),
  which is what the angular estimates (Agmon/Poincaré) produce.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.EllipticEst.DzAmgm.ZsqPz2Comm
import Submission.Work.FTS.EllipticEst.remov.EllEstUnifStepAux
import Submission.Work.FTS.EllipticEst.Prop.levelTopSlotsTwoAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Prop

set_option autoImplicit false
set_option maxHeartbeats 3200000

/-! ## Elementary facts -/

/-- `z > 0` almost everywhere on `Iz = [0,∞)`. -/
theorem ae_restrict_Iz_pos :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), (0 : ℝ) < z := by
  rw [Work.Spaces.Iz, MeasureTheory.ae_restrict_iff' measurableSet_Ici, MeasureTheory.ae_iff]
  refine MeasureTheory.measure_mono_null (t := ({0} : Set ℝ)) ?_
    (MeasureTheory.measure_singleton 0)
  intro x hx
  simp only [Set.mem_ofPred_eq, Set.mem_Ici] at hx
  push Not at hx
  exact le_antisymm hx.2 hx.1

/-- The level-`0` integrand is the square of the weighted function. -/
theorem HkIntegrand_zero_apply (α : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 f z θ
      = (f z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  simp [Work.Spaces.HkIntegrand]

/-- The level-`0` integrand against the `sEta`-weight, on `Iθ`. -/
theorem HkIntegrand_zero_eq_mul (α : ℝ) (f : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α 0 f z θ
      = (f z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta) := by
  rw [HkIntegrand_zero_apply, mul_pow, div_rpow_half_sq_Iθ hθ]
  ring

/-- The level-`0` integrand vanishes when `sin (2θ) = 0`. -/
theorem HkIntegrand_zero_eq_zero_of_sin_eq_zero (α : ℝ) (f : ℝ → ℝ → ℝ) {z θ : ℝ}
    (h : Real.sin (2 * θ) = 0) : Work.Spaces.HkIntegrand α 0 f z θ = 0 := by
  rw [HkIntegrand_zero_apply, h,
    Real.zero_rpow (by norm_num [Work.Spaces.eta] : Work.Spaces.eta / 2 ≠ 0), div_zero,
    mul_zero, sq]
  ring

/-- The level-`0` integrand vanishes when the radial weight vanishes. -/
theorem HkIntegrand_zero_eq_zero_of_w_eq_zero (α : ℝ) (f : ℝ → ℝ → ℝ) {z : ℝ}
    (h : Work.Spaces.w z = 0) (θ : ℝ) : Work.Spaces.HkIntegrand α 0 f z θ = 0 := by
  rw [HkIntegrand_zero_apply, h, zero_div, mul_zero, sq]
  ring

theorem w_zero : Work.Spaces.w 0 = 0 := by
  simp [Work.Spaces.w]

theorem sin_two_zero_at_zero_aux : Real.sin (2 * (0 : ℝ)) = 0 := by
  rw [show 2 * (0 : ℝ) = 0 by ring, Real.sin_zero]

theorem sin_two_zero_at_pi_half_aux : Real.sin (2 * (Real.pi / 2)) = 0 := by
  rw [show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]

/-- **Membership transfer.**  If the level-`0` integrand of `f` is pointwise dominated (on the
open quadrant) by the level-`k` integrand of an `ℋ^k`-function `g`, and `f` is smooth on the
open quadrant, then `f ∈ ℋ⁰`. -/
theorem HkMem_zero_of_pointwise {α : ℝ} {k : ℕ} {f g : ℝ → ℝ → ℝ} {c : ℝ}
    (hc : 0 ≤ c) (hf : SmoothOpen f) (hg : Work.Spaces.HkMem α k g)
    (h : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.HkIntegrand α 0 f z θ ≤ c * Work.Spaces.HkIntegrand α k g z θ) :
    Work.Spaces.HkMem α 0 f := by
  have hpoint : ∀ z θ : ℝ, z ∈ Work.Spaces.Iz → θ ∈ Work.Spaces.Iθ →
      Work.Spaces.HkIntegrand α 0 f z θ ≤ c * Work.Spaces.HkIntegrand α k g z θ := by
    intro z θ hz hθ
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
    · rw [← hz0, HkIntegrand_zero_eq_zero_of_w_eq_zero α f w_zero θ]
      exact mul_nonneg hc (Work.Spaces.HkIntegrand_nonneg α k g 0 θ)
    · rcases eq_or_lt_of_le hθ.1 with h0 | h0
      · rw [← h0, HkIntegrand_zero_eq_zero_of_sin_eq_zero α f sin_two_zero_at_zero_aux]
        exact mul_nonneg hc (Work.Spaces.HkIntegrand_nonneg α k g z 0)
      · rcases eq_or_lt_of_le hθ.2 with h1 | h1
        · rw [h1, HkIntegrand_zero_eq_zero_of_sin_eq_zero α f sin_two_zero_at_pi_half_aux]
          exact mul_nonneg hc (Work.Spaces.HkIntegrand_nonneg α k g z (Real.pi / 2))
        · exact h z θ hzpos h0 h1
  constructor
  · intro z hz
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
    · have hzero : (fun θ : ℝ => Work.Spaces.HkIntegrand α 0 f z θ) = fun _ => (0 : ℝ) :=
        funext fun θ => HkIntegrand_zero_eq_zero_of_w_eq_zero α f (by rw [← hz0]; exact w_zero) θ
      rw [hzero]
      exact integrableOn_zero
    · refine Integrable.mono' ((hg.1 z hz).const_mul c)
        (Work.Spaces.aesm_slice_of_continuousOn_Qd _
          (hf.continuousOn_HkIntegrand α 0) hzpos) ?_
      exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ => by
        rw [Real.norm_of_nonneg (Work.Spaces.HkIntegrand_nonneg α 0 f z θ)]
        exact hpoint z θ hz hθ
  · refine (hg.2.const_mul c).mono' ?_ ?_
    · have hjoint : MeasureTheory.AEStronglyMeasurable
          (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 0 f p.1 p.2)
          ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
        Work.Spaces.aesm_of_continuousOn_Qd _ (hf.continuousOn_HkIntegrand α 0)
      have := hjoint.integral_prod_right'
        (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
        (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
      simpa only using this
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => ?_
      rw [Real.norm_of_nonneg (MeasureTheory.integral_nonneg fun θ =>
        Work.Spaces.HkIntegrand_nonneg α 0 f z θ)]
      rw [← MeasureTheory.integral_const_mul]
      exact MeasureTheory.integral_mono_of_nonneg
        (Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 0 f z θ)
        ((hg.1 z hz).const_mul c)
        (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
          (fun θ hθ => hpoint z θ hz hθ))

/-! ## A.e. slice inequalities imply inequalities of the integrals -/

/-- **`HkSq`-version, two dominating terms.** -/
theorem HkSq_zero_le_of_ae_slice_le_sum {α C : ℝ} (hC : 0 ≤ C) {g u v : ℝ → ℝ → ℝ}
    (huO : MeasureTheory.IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 0 u z θ) Work.Spaces.Iz)
    (hvO : MeasureTheory.IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 0 v z θ) Work.Spaces.Iz)
    (hae : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g z θ)
        ≤ C * ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 u z θ)
            + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 v z θ))) :
    Work.Spaces.HkSq α 0 g ≤ C * (Work.Spaces.HkSq α 0 u + Work.Spaces.HkSq α 0 v) := by
  have hsplit : (∫ z in Work.Spaces.Iz,
        ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 u z θ)
          + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 v z θ)))
      = (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 u z θ)
        + (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 v z θ) :=
    MeasureTheory.integral_add huO hvO
  have hInt : MeasureTheory.Integrable (fun z : ℝ => C * ((∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 0 u z θ) + (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 0 v z θ))) (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    (huO.add hvO).const_mul C
  rw [Work.Spaces.HkSq, Work.Spaces.HkSq, Work.Spaces.HkSq]
  by_cases hG : MeasureTheory.Integrable
      (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iz)
  · have hmono := MeasureTheory.integral_mono_ae hG hInt hae
    rw [MeasureTheory.integral_const_mul] at hmono
    rw [hsplit] at hmono
    linarith
  · rw [MeasureTheory.integral_undef hG]
    exact mul_nonneg hC (add_nonneg (Work.Spaces.HkSq_nonneg α 0 u)
      (Work.Spaces.HkSq_nonneg α 0 v))

/-- **`Tk`-version, two dominating terms.** -/
theorem Tk_le_of_ae_slice_le_sum {α C : ℝ} (hC : 0 ≤ C) {A u v : ℝ → ℝ → ℝ}
    (huO : MeasureTheory.IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 0 u z θ) Work.Spaces.Iz)
    (hvO : MeasureTheory.IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 0 v z θ) Work.Spaces.Iz)
    (hae : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.mixed 0 1 A z θ * Work.Spaces.Wt α z θ) ^ 2)
        ≤ C * ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 u z θ)
            + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 v z θ))) :
    Work.FTS.EllipticEst.remov.Step.Tk α 1 A
      ≤ C * (Work.Spaces.HkSq α 0 u + Work.Spaces.HkSq α 0 v) := by
  have hsplit : (∫ z in Work.Spaces.Iz,
        ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 u z θ)
          + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 v z θ)))
      = (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 u z θ)
        + (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 v z θ) :=
    MeasureTheory.integral_add huO hvO
  have hInt : MeasureTheory.Integrable (fun z : ℝ => C * ((∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 0 u z θ) + (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 0 v z θ))) (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    (huO.add hvO).const_mul C
  rw [Work.FTS.EllipticEst.remov.Step.Tk, Work.Spaces.HkSq, Work.Spaces.HkSq]
  by_cases hG : MeasureTheory.Integrable
      (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.mixed 0 1 A z θ * Work.Spaces.Wt α z θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iz)
  · have hmono := MeasureTheory.integral_mono_ae hG hInt hae
    rw [MeasureTheory.integral_const_mul] at hmono
    rw [hsplit] at hmono
    linarith
  · rw [MeasureTheory.integral_undef hG]
    exact mul_nonneg hC (add_nonneg (Work.Spaces.HkSq_nonneg α 0 u)
      (Work.Spaces.HkSq_nonneg α 0 v))

/-- **`Tk`-version, three dominating terms.** -/
theorem Tk_le_of_ae_slice_le_sum3 {α C : ℝ} (hC : 0 ≤ C) {A u v w : ℝ → ℝ → ℝ}
    (huO : MeasureTheory.IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 0 u z θ) Work.Spaces.Iz)
    (hvO : MeasureTheory.IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 0 v z θ) Work.Spaces.Iz)
    (hwO : MeasureTheory.IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 0 w z θ) Work.Spaces.Iz)
    (hae : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.mixed 0 1 A z θ * Work.Spaces.Wt α z θ) ^ 2)
        ≤ C * (((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 u z θ)
            + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 v z θ))
          + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 w z θ))) :
    Work.FTS.EllipticEst.remov.Step.Tk α 1 A
      ≤ C * ((Work.Spaces.HkSq α 0 u + Work.Spaces.HkSq α 0 v) + Work.Spaces.HkSq α 0 w) := by
  have hsplit : (∫ z in Work.Spaces.Iz,
        (((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 u z θ)
          + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 v z θ))
          + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 w z θ)))
      = ((∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 u z θ)
          + (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 v z θ))
        + (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 w z θ) := by
    have h1 : (∫ z in Work.Spaces.Iz,
          (((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 u z θ)
            + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 v z θ))
            + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 w z θ)))
        = (∫ z in Work.Spaces.Iz, ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 u z θ)
            + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 v z θ)))
          + (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
              Work.Spaces.HkIntegrand α 0 w z θ) :=
      MeasureTheory.integral_add
        (μ := MeasureTheory.volume.restrict Work.Spaces.Iz) (huO.add hvO) hwO
    have h2 : (∫ z in Work.Spaces.Iz, ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 u z θ)
          + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 v z θ)))
        = (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 u z θ)
          + (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
              Work.Spaces.HkIntegrand α 0 v z θ) :=
      MeasureTheory.integral_add
        (μ := MeasureTheory.volume.restrict Work.Spaces.Iz) huO hvO
    rw [h1, h2]
  have hInt : MeasureTheory.Integrable (fun z : ℝ => C * (((∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 0 u z θ) + (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 0 v z θ)) + (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 0 w z θ))) (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    ((huO.add hvO).add hwO).const_mul C
  rw [Work.FTS.EllipticEst.remov.Step.Tk, Work.Spaces.HkSq, Work.Spaces.HkSq, Work.Spaces.HkSq]
  by_cases hG : MeasureTheory.Integrable
      (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.mixed 0 1 A z θ * Work.Spaces.Wt α z θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iz)
  · have hmono := MeasureTheory.integral_mono_ae hG hInt hae
    rw [MeasureTheory.integral_const_mul] at hmono
    rw [hsplit] at hmono
    linarith
  · rw [MeasureTheory.integral_undef hG]
    refine mul_nonneg hC (add_nonneg (add_nonneg (Work.Spaces.HkSq_nonneg α 0 u)
      (Work.Spaces.HkSq_nonneg α 0 v)) (Work.Spaces.HkSq_nonneg α 0 w))


/-- **The `θ`-integral agrees off the endpoints.** -/
theorem integral_Iθ_congr_of_Ioo {h k : ℝ → ℝ}
    (h' : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), h θ = k θ) :
    (∫ θ in Work.Spaces.Iθ, h θ) = ∫ θ in Work.Spaces.Iθ, k θ := by
  refine MeasureTheory.integral_congr_ae ?_
  show ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), h θ = k θ
  rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iθ) measurableSet_Icc]
  rw [MeasureTheory.ae_iff]
  refine MeasureTheory.measure_mono_null (t := ({0} : Set ℝ) ∪ {Real.pi / 2}) ?_ ?_
  · intro θ hθ
    simp only [Set.mem_ofPred_eq, not_imp, Set.mem_Icc, Work.Spaces.Iθ, Set.mem_union,
      Set.mem_singleton_iff] at hθ ⊢
    obtain ⟨⟨h0, h1⟩, hne⟩ := hθ
    rcases eq_or_lt_of_le h0 with h0' | h0'
    · exact Or.inl h0'.symm
    · refine Or.inr ?_
      by_contra hpi
      exact hne (h' θ ⟨h0', lt_of_le_of_ne h1 hpi⟩)
  · exact MeasureTheory.measure_union_null (MeasureTheory.measure_singleton 0)
      (MeasureTheory.measure_singleton (Real.pi / 2))

/-- **`L2Sq` is insensitive to the values off the open quadrant.** -/
theorem L2Sq_congr_open {f g : ℝ → ℝ → ℝ}
    (h : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → f z θ = g z θ) :
    Work.Spaces.L2Sq f = Work.Spaces.L2Sq g := by
  rw [Work.Spaces.L2Sq, Work.Spaces.L2Sq]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [ae_restrict_Iz_pos] with z hz
  exact integral_Iθ_congr_of_Ioo (fun θ hθ => by rw [h z θ hz hθ.1 hθ.2])

/-- **`Tk` is insensitive to a pointwise rewriting on the open quadrant.** -/
theorem Tk_congr_open {α : ℝ} (k : ℕ) {f g : ℝ → ℝ → ℝ}
    (h : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → f z θ = g z θ) :
    Work.FTS.EllipticEst.remov.Step.Tk α k f
      = Work.FTS.EllipticEst.remov.Step.Tk α k g := by
  have h' := Work.FTS.EllipticEst.AgreeOnQ.DthIter h k
  rw [Work.FTS.EllipticEst.remov.Step.Tk, Work.FTS.EllipticEst.remov.Step.Tk]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [ae_restrict_Iz_pos] with z hz
  exact integral_Iθ_congr_of_Ioo
    (fun θ hθ => by
      simp only [Work.Spaces.mixed_zero_left]
      rw [h' z θ hz hθ.1 hθ.2])

/-! ## The weight identity of the top angular slot -/

/-- On `Iθ` the square of the top angular slot is exactly `(∂_θf)² w² σ^{2-γ}`. -/
theorem Dth_mul_Wt_sq_eq_Iθ {α : ℝ} (hα : Work.Spaces.gam α < 2) (f : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.Dth f z θ * Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.pth f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) := by
  rcases eq_or_lt_of_le hθ.1 with h0 | h0
  · rw [← h0, Work.Spaces.Dth, sin_two_zero_at_zero_aux, zero_mul,
      Real.zero_rpow (by linarith : 2 - Work.Spaces.gam α ≠ 0)]
    ring
  · rcases eq_or_lt_of_le hθ.2 with h1 | h1
    · rw [h1, Work.Spaces.Dth, sin_two_zero_at_pi_half_aux, zero_mul,
        Real.zero_rpow (by linarith : 2 - Work.Spaces.gam α ≠ 0)]
      ring
    · rw [Work.Spaces.Dth, Work.Spaces.Wt, Work.Spaces.wTheta]
      rw [show (Real.sin (2 * θ) * Work.Spaces.pth f z θ
            * (Work.Spaces.w z * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α / 2)))) ^ 2
          = (Work.Spaces.pth f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ) * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α / 2))) ^ 2
          from by ring]
      rw [sq_sin_mul_rpow ⟨h0, h1⟩]

/-! ## The angular weight algebra of the Agmon estimate -/

/-- `(σ·g)²·σ^{-γ} = g²·σ^{2-γ}` on `Iθ` (both sides vanish at the endpoints). -/
theorem sq_sin_mul_rpow_Iθ {γ g θ : ℝ} (hγ : γ ≠ 0) (hγ2 : 2 - γ ≠ 0)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    (Real.sin (2 * θ) * g) ^ 2 * (Real.sin (2 * θ)) ^ (-γ)
      = g ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ) := by
  rcases eq_or_lt_of_le hθ.1 with h0 | h0
  · rw [← h0, sin_two_zero_at_zero_aux, zero_mul, Real.zero_rpow (neg_ne_zero.mpr hγ),
      Real.zero_rpow hγ2]
    ring
  · rcases eq_or_lt_of_le hθ.2 with h1 | h1
    · rw [h1, sin_two_zero_at_pi_half_aux, zero_mul, Real.zero_rpow (neg_ne_zero.mpr hγ),
        Real.zero_rpow hγ2]
      ring
    · have hs : 0 < Real.sin (2 * θ) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [h1, Real.pi_pos])
      rw [show (Real.sin (2 * θ) * g) ^ 2 * (Real.sin (2 * θ)) ^ (-γ)
          = g ^ 2 * ((Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-γ)) from by ring]
      rw [(Real.rpow_natCast (Real.sin (2 * θ)) 2).symm, ← Real.rpow_add hs,
        show (((2 : ℕ)) : ℝ) + (-γ) = 2 - γ from by push_cast; ring]

/-- `(D_θg)² · sGam α = (g')² · σ^{2-γ}` on `Iθ`. -/
theorem sq_Dth1Iter_one_sGam_eq {α : ℝ} (hγ : Work.Spaces.gam α ≠ 0)
    (hγ2 : 2 - Work.Spaces.gam α ≠ 0) (g : ℝ → ℝ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Elliptic.Dth1Iter 1 g θ) ^ 2 * Work.FTS.EllipticEst.sGam α θ
      = (deriv g θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) := by
  rw [Work.Elliptic.Dth1Iter_succ, Work.Elliptic.Dth1Iter_zero, Work.Elliptic.Dth1]
  simp only [Work.FTS.EllipticEst.sGam]
  exact sq_sin_mul_rpow_Iθ hγ hγ2 hθ


/-- **The top angular slot as a weighted integral of `∂_θf`.** -/
theorem Tk_one_eq_int {α : ℝ} (hα : Work.Spaces.gam α < 2) (f : ℝ → ℝ → ℝ) :
    Work.FTS.EllipticEst.remov.Step.Tk α 1 f
      = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth f z θ) ^ 2
          * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) := by
  rw [Work.FTS.EllipticEst.remov.Step.Tk]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with θ hθ
  simp only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero]
  rw [Dth_mul_Wt_sq_eq_Iθ hα f hθ]

/-- **A double integral is insensitive to the values off the open quadrant.** -/
theorem integral_prod_congr_open {F G : ℝ → ℝ → ℝ}
    (h : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → F z θ = G z θ) :
    (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, F z θ)
      = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, G z θ := by
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [ae_restrict_Iz_pos] with z hz
  exact integral_Iθ_congr_of_Ioo (fun θ hθ => h z θ hz hθ.1 hθ.2)


end Work.FTS.EllipticEst.Prop
