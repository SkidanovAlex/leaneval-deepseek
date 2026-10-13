/-
Work module for `annals_finite_time_singularity`: the transport of the (real) weak formulation of
`bslOp α Ψ = F` on the quadrant `Q0` to the half-strip `stripRR` in the `(σ,θ)`-coordinates.

This module collects the real-variable ingredients: the locality of `kopDr`, the integrability of
the transported integrand, the two change-of-variables identities and the real transport lemma,
plus the analysis of the "non-degenerate" / "degenerate" cases used in `transportWeakRR`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Elliptic.bslOp_add
import Submission.Work.EllipticEst.InteriorRegularity.Q0.RRBasic
import Submission.Work.EllipticEst.InteriorRegularity.Q0.exists_cutoff
import Submission.Work.EllipticEst.InteriorRegularity.Q0.bslOp_congr_of_isOpen
import Submission.Work.EllipticEst.InteriorRegularity.Q0.integrableOn_Q0_iff_strip
import Submission.Work.EllipticEst.InteriorRegularity.Q0.continuousOn_kopDr
import Submission.Work.EllipticEst.InteriorRegularity.Q0.barPsi_compact
import Submission.Work.EllipticEst.InteriorRegularity.IR.integralQ0eqStrip

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.EllipticEst.InteriorRegularity.Q0

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- The open quadrant, in the product form used by the change-of-variables lemmas. -/
theorem Q0_eq_prod : Work.FTS.EllipticEst.Q0 = Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) := rfl

/-- The half-strip, in the product form used by the change-of-variables lemmas. -/
theorem stripRR_eq_prod : stripRR = (Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2) := rfl

/-! ## The real change of variables `Q0 → stripRR` for integrals -/

/-- The real-valued version of `IR.integralQ0eqStrip`. -/
theorem integral_Q0_eq_strip_real {α : ℝ} (hα : 0 < α) {f : ℝ × ℝ → ℝ}
    (hf : MeasureTheory.IntegrableOn f Work.FTS.EllipticEst.Q0) :
    (∫ p in Work.FTS.EllipticEst.Q0, f p)
      = ∫ q in stripRR, f (Real.exp (α * q.1), q.2) * (α * Real.exp (α * q.1)) := by
  rw [Q0_eq_prod] at hf
  have hmain := Work.EllipticEst.InteriorRegularity.IR.integralQ0eqStrip (α := α) hα
    (X := fun p : ℝ × ℝ => ((f p : ℝ) : ℂ)) hf.ofReal
  have hcast : (∫ q in (Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2),
        ((f (Real.exp (α * q.1), q.2) * (α * Real.exp (α * q.1)) : ℝ) : ℂ))
      = ((∫ q in (Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2),
          f (Real.exp (α * q.1), q.2) * (α * Real.exp (α * q.1)) : ℝ) : ℂ) :=
    integral_complex_ofReal
  have hL : (∫ p in Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2), ((f p : ℝ) : ℂ))
      = ((∫ p in Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2), f p : ℝ) : ℂ) :=
    integral_complex_ofReal
  have hmid : (∫ p in Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2), ((f p : ℝ) : ℂ))
      = (∫ q in (Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2),
          ((f (Real.exp (α * q.1), q.2) * (α * Real.exp (α * q.1)) : ℝ) : ℂ)) := by
    rw [hmain]
    refine setIntegral_congr_fun (MeasurableSet.univ.prod measurableSet_Ioo) (fun q _ => ?_)
    push_cast
    ring
  have hstep : ((∫ p in Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2), f p : ℝ) : ℂ)
      = ((∫ q in (Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2),
          f (Real.exp (α * q.1), q.2) * (α * Real.exp (α * q.1)) : ℝ) : ℂ) := by
    rw [← hL, hmid, hcast]
  exact Complex.ofReal_injective hstep

/-! ## The two change-of-variable identities (the "chains") -/

/-- The `Q0`-side integrand of the weak formulation. -/
def qint (α : ℝ) (F : ℝ → ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun p => F p.1 p.2 * (p.1 ^ ((5 - α) / α) * Real.cos p.2)

theorem qint_apply (α : ℝ) (F : ℝ → ℝ → ℝ) (p : ℝ × ℝ) :
    qint α F p = F p.1 p.2 * (p.1 ^ ((5 - α) / α) * Real.cos p.2) := rfl

/-- Pulling `qint α F` back along `(σ,θ) ↦ (exp (ασ), θ)` gives `GRR α F · ψ`. -/
theorem qint_pullback_GRR {α : ℝ} (hα : 0 < α) {F : ℝ → ℝ → ℝ} {ψ : ℝ → ℝ → ℝ}
    {φ : ℝ → ℝ → ℝ} (hφval : ∀ z θ : ℝ, 0 < z → φ z θ = ψ ((1 / α) * Real.log z) θ)
    (hφQ : tsupport (Function.uncurry φ) ⊆ Work.FTS.EllipticEst.Q0) :
    ∀ q : ℝ × ℝ, (α * Real.exp (α * q.1))
        * (F (Real.exp (α * q.1)) q.2 * φ (Real.exp (α * q.1)) q.2
            * ((Real.exp (α * q.1)) ^ ((5 - α) / α) * Real.cos q.2))
      = GRR α F q.1 q.2 * ψ q.1 q.2 := by
  intro q
  by_cases hq : q.2 ∈ Set.Ioo 0 (π / 2)
  · have he : 0 < Real.exp (α * q.1) := Real.exp_pos _
    have hlog : (1 / α) * Real.log (Real.exp (α * q.1)) = q.1 := by
      rw [Real.log_exp]; field_simp
    rw [hφval _ _ he, hlog, exp_mul_rpow hα.ne']
    simp only [GRR, hq, if_true, wtRR]
    rw [show (5 - α) * q.1 = 5 * q.1 + -(α * q.1) from by ring, Real.exp_add, Real.exp_neg]
    field_simp
    try ring
  · have h0 : φ (Real.exp (α * q.1)) q.2 = 0 := by
      by_contra hne
      have hmem : (Real.exp (α * q.1), q.2) ∈ tsupport (Function.uncurry φ) :=
        subset_tsupport _ (Function.mem_support.mpr hne)
      exact hq (hφQ hmem).2
    simp only [GRR, hq, if_false, h0, mul_zero]
    ring

/-- Pulling back the `bslOp α φ`-integrand along `(σ,θ) ↦ (exp (ασ), θ)` gives
`VRR α Ψ · kopDr ψ`. -/
theorem bsl_pullback_VRR {α : ℝ} (hα : 0 < α) {Ψ : ℝ → ℝ → ℝ} {ψ : ℝ → ℝ → ℝ}
    {φ : ℝ → ℝ → ℝ} (hφQ : tsupport (Function.uncurry φ) ⊆ Work.FTS.EllipticEst.Q0)
    (hφbsl : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      Work.Elliptic.bslOp α φ z θ = kopDr ψ ((1 / α) * Real.log z) θ) :
    ∀ q : ℝ × ℝ, (α * Real.exp (α * q.1))
        * (Ψ (Real.exp (α * q.1)) q.2 * (Work.Elliptic.bslOp α φ (Real.exp (α * q.1)) q.2)
            * ((Real.exp (α * q.1)) ^ ((5 - α) / α) * Real.cos q.2))
      = VRR α Ψ q.1 q.2 * kopDr ψ q.1 q.2 := by
  intro q
  by_cases hq : q.2 ∈ Set.Ioo 0 (π / 2)
  · have he : 0 < Real.exp (α * q.1) := Real.exp_pos _
    have hlog : (1 / α) * Real.log (Real.exp (α * q.1)) = q.1 := by
      rw [Real.log_exp]; field_simp
    rw [hφbsl _ _ he hq, hlog, exp_mul_rpow hα.ne']
    simp only [VRR, hq, if_true, wtRR]
    rw [show (5 - α) * q.1 = 5 * q.1 + -(α * q.1) from by ring, Real.exp_add, Real.exp_neg]
    field_simp
    try ring
  · have h0 : Work.Elliptic.bslOp α φ (Real.exp (α * q.1)) q.2 = 0 := by
      refine bslOp_eq_zero_of_notMem_tsupport ?_
      intro hmem
      exact hq (hφQ hmem).2
    simp only [VRR, hq, if_false, h0, mul_zero]
    ring

/-! ## Integrability of the transported integrand -/

theorem integrable_VRR_kopDr {α : ℝ} (hα : 0 < α) {Ψ : ℝ → ℝ → ℝ}
    (hΨ : MeasureTheory.LocallyIntegrableOn (Function.uncurry Ψ) Work.FTS.EllipticEst.Q0)
    {ψ : ℝ → ℝ → ℝ} (hψ : ∀ n : ℕ, ContDiff ℝ n (Function.uncurry ψ))
    (hψc : HasCompactSupport (Function.uncurry ψ))
    (hψs : tsupport (Function.uncurry ψ) ⊆ stripRR) :
    MeasureTheory.Integrable (fun q : ℝ × ℝ => VRR α Ψ q.1 q.2 * kopDr ψ q.1 q.2) := by
  set K : Set (ℝ × ℝ) := tsupport (Function.uncurry ψ) with hK
  have hKc : IsCompact K := hψc
  have hcont : ContinuousOn (fun q : ℝ × ℝ => wtRR α q.1 q.2 * kopDr ψ q.1 q.2) K :=
    ((continuous_wtRR α).continuousOn).mul ((continuousOn_kopDr hψ).mono hψs)
  have hΦ : MeasureTheory.IntegrableOn
      (fun q : ℝ × ℝ => if q.2 ∈ Set.Ioo 0 (π / 2) then Ψ (Real.exp (α * q.1)) q.2 else 0)
      K :=
    integrableOn_barPsi_compact hα hΨ hKc hψs
  have hprod : MeasureTheory.IntegrableOn
      (fun q : ℝ × ℝ =>
        (if q.2 ∈ Set.Ioo 0 (π / 2) then Ψ (Real.exp (α * q.1)) q.2 else 0)
          * (wtRR α q.1 q.2 * kopDr ψ q.1 q.2)) K :=
    hΦ.mul_continuousOn hcont hKc
  have hEq : Set.EqOn (fun q : ℝ × ℝ =>
        (if q.2 ∈ Set.Ioo 0 (π / 2) then Ψ (Real.exp (α * q.1)) q.2 else 0)
          * (wtRR α q.1 q.2 * kopDr ψ q.1 q.2))
      (fun q : ℝ × ℝ => VRR α Ψ q.1 q.2 * kopDr ψ q.1 q.2) K := by
    intro q _
    by_cases hq : q.2 ∈ Set.Ioo 0 (π / 2)
    · simp only [hq, if_true, VRR]
      ring
    · simp only [hq, if_false, VRR]
      ring
  have hOn : MeasureTheory.IntegrableOn (fun q : ℝ × ℝ => VRR α Ψ q.1 q.2 * kopDr ψ q.1 q.2) K :=
    (integrableOn_congr_fun hEq hKc.measurableSet).mp hprod
  have hsupp : Function.support (fun q : ℝ × ℝ => VRR α Ψ q.1 q.2 * kopDr ψ q.1 q.2) ⊆ K := by
    intro q hq
    by_contra hcon
    have h1 : kopDr ψ q.1 q.2 = 0 := kopDr_eq_zero_of_notMem_tsupport hcon
    exact (Function.mem_support.mp hq) (by rw [h1, mul_zero])
  have hind : K.indicator (fun q : ℝ × ℝ => VRR α Ψ q.1 q.2 * kopDr ψ q.1 q.2)
      = (fun q : ℝ × ℝ => VRR α Ψ q.1 q.2 * kopDr ψ q.1 q.2) := by
    funext q
    by_cases hq : q ∈ K
    · rw [Set.indicator_of_mem hq]
    · rw [Set.indicator_of_notMem hq]
      by_contra hne
      exact hq (hsupp (Function.mem_support.mpr (fun h => hne h.symm)))
  rw [← hind, integrable_indicator_iff hKc.measurableSet]
  exact hOn

/-- The integrand on the `Q0`-side of the weak formulation is integrable. -/
theorem integrableOn_qint_of_pullback {α : ℝ} (hα : 0 < α) {f g : ℝ × ℝ → ℝ}
    (hf : MeasureTheory.Integrable (g))
    (heq : ∀ q : ℝ × ℝ, g q = (α * Real.exp (α * q.1)) * f (Real.exp (α * q.1), q.2)) :
    MeasureTheory.IntegrableOn f Work.FTS.EllipticEst.Q0 := by
  rw [integrableOn_Q0_iff_strip hα f]
  exact (hf.congr (by filter_upwards with q; rw [smul_eq_mul]; exact heq q)).integrableOn

/-! ## The chains -/

theorem LHS_chain {α : ℝ} (hα : 0 < α) {Ψ : ℝ → ℝ → ℝ}
    (hΨ : MeasureTheory.LocallyIntegrableOn (Function.uncurry Ψ) Work.FTS.EllipticEst.Q0)
    {ψ : ℝ → ℝ → ℝ} (hψ : ∀ n : ℕ, ContDiff ℝ n (Function.uncurry ψ))
    (hψc : HasCompactSupport (Function.uncurry ψ))
    (hψs : tsupport (Function.uncurry ψ) ⊆ stripRR)
    {φ : ℝ → ℝ → ℝ}
    (hφQ : tsupport (Function.uncurry φ) ⊆ Work.FTS.EllipticEst.Q0)
    (hφbsl : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      Work.Elliptic.bslOp α φ z θ = kopDr ψ ((1 / α) * Real.log z) θ) :
    (∫ q : ℝ × ℝ, VRR α Ψ q.1 q.2 * kopDr ψ q.1 q.2)
      = ∫ p in Work.FTS.EllipticEst.Q0,
          Ψ p.1 p.2 * (Work.Elliptic.bslOp α φ p.1 p.2)
            * (p.1 ^ ((5 - α) / α) * Real.cos p.2) := by
  set X : ℝ × ℝ → ℝ := fun p => Ψ p.1 p.2 * (Work.Elliptic.bslOp α φ p.1 p.2)
      * (p.1 ^ ((5 - α) / α) * Real.cos p.2) with hX
  have hInt : MeasureTheory.Integrable (fun q : ℝ × ℝ => VRR α Ψ q.1 q.2 * kopDr ψ q.1 q.2) :=
    integrable_VRR_kopDr hα hΨ hψ hψc hψs
  have hpb := bsl_pullback_VRR hα (Ψ := Ψ) (ψ := ψ) hφQ hφbsl
  have hIntOn : MeasureTheory.IntegrableOn X Work.FTS.EllipticEst.Q0 :=
    integrableOn_qint_of_pullback hα hInt (fun q => (hpb q).symm)
  have hOff : ∀ q : ℝ × ℝ, q ∉ stripRR → VRR α Ψ q.1 q.2 * kopDr ψ q.1 q.2 = 0 := by
    intro q hq
    have hq2 : ¬ (q.2 ∈ Set.Ioo 0 (π / 2)) := fun h => hq ⟨trivial, h⟩
    simp only [VRR, hq2, if_false, zero_mul]
  have h1 : (∫ q in stripRR, VRR α Ψ q.1 q.2 * kopDr ψ q.1 q.2)
      = ∫ q : ℝ × ℝ, VRR α Ψ q.1 q.2 * kopDr ψ q.1 q.2 :=
    setIntegral_eq_integral_of_forall_compl_eq_zero hOff
  have h2 : (∫ q in stripRR, VRR α Ψ q.1 q.2 * kopDr ψ q.1 q.2)
      = ∫ q in stripRR, (α * Real.exp (α * q.1)) * X (Real.exp (α * q.1), q.2) :=
    setIntegral_congr_fun (MeasurableSet.univ.prod measurableSet_Ioo)
      (fun q _ => (hpb q).symm)
  have h3 := integral_Q0_eq_strip_real hα hIntOn
  calc ∫ q : ℝ × ℝ, VRR α Ψ q.1 q.2 * kopDr ψ q.1 q.2
      = ∫ q in stripRR, VRR α Ψ q.1 q.2 * kopDr ψ q.1 q.2 := h1.symm
    _ = ∫ q in stripRR, (α * Real.exp (α * q.1)) * X (Real.exp (α * q.1), q.2) := h2
    _ = ∫ q in stripRR, X (Real.exp (α * q.1), q.2) * (α * Real.exp (α * q.1)) := by
        refine setIntegral_congr_fun (MeasurableSet.univ.prod measurableSet_Ioo)
          (fun q _ => by ring)
    _ = ∫ p in Work.FTS.EllipticEst.Q0, X p := h3.symm

theorem RHS_chain {α : ℝ} (hα : 0 < α) {F : ℝ → ℝ → ℝ} {ψ φ : ℝ → ℝ → ℝ}
    (hφval : ∀ z θ : ℝ, 0 < z → φ z θ = ψ ((1 / α) * Real.log z) θ)
    (hφQ : tsupport (Function.uncurry φ) ⊆ Work.FTS.EllipticEst.Q0)
    (hint : MeasureTheory.Integrable (fun q : ℝ × ℝ => GRR α F q.1 q.2 * ψ q.1 q.2)) :
    (∫ q : ℝ × ℝ, GRR α F q.1 q.2 * ψ q.1 q.2)
      = ∫ p in Work.FTS.EllipticEst.Q0,
          F p.1 p.2 * φ p.1 p.2 * (p.1 ^ ((5 - α) / α) * Real.cos p.2) := by
  set Y : ℝ × ℝ → ℝ := fun p =>
    F p.1 p.2 * φ p.1 p.2 * (p.1 ^ ((5 - α) / α) * Real.cos p.2) with hY
  have hpb := qint_pullback_GRR hα (F := F) (ψ := ψ) hφval hφQ
  have hIntOn : MeasureTheory.IntegrableOn Y Work.FTS.EllipticEst.Q0 :=
    integrableOn_qint_of_pullback hα hint (fun q => (hpb q).symm)
  have hOff : ∀ q : ℝ × ℝ, q ∉ stripRR → GRR α F q.1 q.2 * ψ q.1 q.2 = 0 := by
    intro q hq
    have hq2 : ¬ (q.2 ∈ Set.Ioo 0 (π / 2)) := fun h => hq ⟨trivial, h⟩
    simp only [GRR, hq2, if_false, zero_mul]
  have h1 : (∫ q in stripRR, GRR α F q.1 q.2 * ψ q.1 q.2)
      = ∫ q : ℝ × ℝ, GRR α F q.1 q.2 * ψ q.1 q.2 :=
    setIntegral_eq_integral_of_forall_compl_eq_zero hOff
  have h2 : (∫ q in stripRR, GRR α F q.1 q.2 * ψ q.1 q.2)
      = ∫ q in stripRR, (α * Real.exp (α * q.1)) * Y (Real.exp (α * q.1), q.2) :=
    setIntegral_congr_fun (MeasurableSet.univ.prod measurableSet_Ioo)
      (fun q _ => (hpb q).symm)
  have h3 := integral_Q0_eq_strip_real hα hIntOn
  calc ∫ q : ℝ × ℝ, GRR α F q.1 q.2 * ψ q.1 q.2
      = ∫ q in stripRR, GRR α F q.1 q.2 * ψ q.1 q.2 := h1.symm
    _ = ∫ q in stripRR, (α * Real.exp (α * q.1)) * Y (Real.exp (α * q.1), q.2) := h2
    _ = ∫ q in stripRR, Y (Real.exp (α * q.1), q.2) * (α * Real.exp (α * q.1)) := by
        refine setIntegral_congr_fun (MeasurableSet.univ.prod measurableSet_Ioo)
          (fun q _ => by ring)
    _ = ∫ p in Work.FTS.EllipticEst.Q0, Y p := h3.symm

/-! ## The functionals `Lam` and `Gint` and the non-degeneracy -/

/-- The `Q0`-side integrand of the weak formulation tested against `f`. -/
def Gint (α : ℝ) (F : ℝ → ℝ → ℝ) (φ : ℝ → ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun p => F p.1 p.2 * φ p.1 p.2 * (p.1 ^ ((5 - α) / α) * Real.cos p.2)

/-- The left-hand side integrand of the weak formulation. -/
def Lint (α : ℝ) (Ψ : ℝ → ℝ → ℝ) (φ : ℝ → ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun p => Ψ p.1 p.2 * (Work.Elliptic.bslOp α φ p.1 p.2) * (p.1 ^ ((5 - α) / α) * Real.cos p.2)

/-- The left-hand side functional of the weak formulation. -/
def Lam (α : ℝ) (Ψ : ℝ → ℝ → ℝ) (φ : ℝ → ℝ → ℝ) : ℝ := ∫ p in Work.FTS.EllipticEst.Q0, Lint α Ψ φ p

/-- Non-degeneracy of `Ψ`: there is a `Q0`-test function on which the left-hand side functional
of the weak formulation does not vanish. -/
def Nondeg (α : ℝ) (Ψ : ℝ → ℝ → ℝ) : Prop :=
  ∃ η : ℝ → ℝ → ℝ, (∀ n : ℕ, ContDiff ℝ n (Function.uncurry η)) ∧
    HasCompactSupport (Function.uncurry η) ∧
    tsupport (Function.uncurry η) ⊆ Work.FTS.EllipticEst.Q0 ∧ Lam α Ψ η ≠ 0

theorem Gint_apply (α : ℝ) (F φ : ℝ → ℝ → ℝ) (p : ℝ × ℝ) :
    Gint α F φ p = F p.1 p.2 * φ p.1 p.2 * (p.1 ^ ((5 - α) / α) * Real.cos p.2) := rfl

theorem Lam_apply (α : ℝ) (Ψ φ : ℝ → ℝ → ℝ) :
    Lam α Ψ φ = ∫ p in Work.FTS.EllipticEst.Q0, Lint α Ψ φ p := rfl

/-! ## Linear combinations of the transported test functions -/

/-- `bslOp` is additive for a natural multiple of the second argument. -/
theorem bslOp_nsmul_add (α : ℝ) {f g : ℝ → ℝ → ℝ} (n : ℕ) {z θ : ℝ} (hθ : Real.cos θ ≠ 0)
    (hf : ContDiffAt ℝ 2 (Function.uncurry f) (z, θ))
    (hg : ContDiffAt ℝ 2 (Function.uncurry g) (z, θ)) :
    Work.Elliptic.bslOp α (fun z θ : ℝ => f z θ + n * g z θ) z θ
      = Work.Elliptic.bslOp α f z θ + n * Work.Elliptic.bslOp α g z θ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hsplit : (fun z θ : ℝ => f z θ + (↑(n + 1) : ℝ) * g z θ)
        = (fun z θ : ℝ => (f z θ + ↑n * g z θ) + g z θ) := by
      funext z θ; push_cast; ring
    rw [hsplit]
    have hcmb : ContDiffAt ℝ 2 (Function.uncurry (fun z θ : ℝ => f z θ + ↑n * g z θ)) (z, θ) := by
      have hfun : Function.uncurry (fun z θ : ℝ => f z θ + ↑n * g z θ)
          = fun p : ℝ × ℝ => Function.uncurry f p + ↑n * Function.uncurry g p := by
        funext p; rfl
      rw [hfun]
      exact hf.add ((contDiffAt_const (c := (↑n : ℝ))).mul hg)
    rw [Work.Elliptic.bslOp_add α _ g z θ hθ hcmb hg, ih]
    push_cast
    ring

/-- The left-hand integrand is additive in the natural-multiple sense. -/
theorem Lint_nsmul_add (α : ℝ) {Ψ f g : ℝ → ℝ → ℝ} (n : ℕ)
    (hfc : ∀ z θ : ℝ, Real.cos θ ≠ 0 → ContDiffAt ℝ 2 (Function.uncurry f) (z, θ))
    (hgc : ∀ z θ : ℝ, Real.cos θ ≠ 0 → ContDiffAt ℝ 2 (Function.uncurry g) (z, θ)) :
    Set.EqOn (Lint α Ψ (fun z θ : ℝ => f z θ + n * g z θ))
      (fun p : ℝ × ℝ => Lint α Ψ f p + n * Lint α Ψ g p)
      (Work.FTS.EllipticEst.Q0) := by
  intro p hp
  have hθ : Real.cos p.2 ≠ 0 := by
    obtain ⟨-, h1, h2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], h2⟩)
  simp only [Lint]
  rw [bslOp_nsmul_add α n hθ (hfc p.1 p.2 hθ) (hgc p.1 p.2 hθ)]
  ring

/-! ## Integrability transfer for the source side -/

theorem integrableOn_strip_iff {f : ℝ × ℝ → ℝ}
    (h : ∀ q : ℝ × ℝ, q ∉ (Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2) → f q = 0) :
    MeasureTheory.IntegrableOn f ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2))
      ↔ MeasureTheory.Integrable f := by
  constructor
  · intro hf
    have hind : ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)).indicator f = f := by
      funext q
      by_cases hq : q ∈ (Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)
      · rw [Set.indicator_of_mem hq]
      · rw [Set.indicator_of_notMem hq]
        exact (h q hq).symm
    have h2 : MeasureTheory.Integrable
        (((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)).indicator f) := by
      rw [MeasureTheory.integrable_indicator_iff (MeasurableSet.univ.prod measurableSet_Ioo)]
      exact hf
    rwa [hind] at h2
  · intro hf; exact hf.integrableOn

theorem Gint_eq_qint_mul (α : ℝ) (F φ : ℝ → ℝ → ℝ) :
    Gint α F φ = fun p : ℝ × ℝ => qint α F p * φ p.1 p.2 := by
  funext p; simp only [Gint, qint]; ring

theorem integrable_GRR_iff {α : ℝ} (hα : 0 < α) {F ψ φ : ℝ → ℝ → ℝ}
    (hφval : ∀ z θ : ℝ, 0 < z → φ z θ = ψ ((1 / α) * Real.log z) θ)
    (hφQ : tsupport (Function.uncurry φ) ⊆ Work.FTS.EllipticEst.Q0) :
    MeasureTheory.Integrable (fun q : ℝ × ℝ => GRR α F q.1 q.2 * ψ q.1 q.2)
      ↔ MeasureTheory.IntegrableOn (Gint α F φ) Work.FTS.EllipticEst.Q0 := by
  have hpb := qint_pullback_GRR hα (F := F) (ψ := ψ) hφval hφQ
  rw [Gint_eq_qint_mul α F φ,
    integrableOn_Q0_iff_strip hα (fun p : ℝ × ℝ => qint α F p * φ p.1 p.2)]
  have hsupp : ∀ q : ℝ × ℝ,
      q ∉ (Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2) →
        (α * Real.exp (α * q.1)) • (qint α F (Real.exp (α * q.1), q.2)
          * φ (Real.exp (α * q.1)) q.2) = 0 := by
    intro q hq
    have hq2 : ¬ (q.2 ∈ Set.Ioo 0 (π / 2)) := fun h => hq ⟨trivial, h⟩
    have h0 : φ (Real.exp (α * q.1)) q.2 = 0 := by
      by_contra hne
      have hmem : (Real.exp (α * q.1), q.2) ∈ tsupport (Function.uncurry φ) :=
        subset_tsupport _ (Function.mem_support.mpr hne)
      exact hq2 (hφQ hmem).2
    rw [h0, mul_zero, smul_zero]
  rw [integrableOn_strip_iff hsupp]
  constructor
  · intro hf
    refine hf.congr (Filter.Eventually.of_forall fun q => ?_)
    show GRR α F q.1 q.2 * ψ q.1 q.2
        = (α * Real.exp (α * q.1)) • (qint α F (Real.exp (α * q.1), q.2) * φ (Real.exp (α * q.1)) q.2)
    rw [smul_eq_mul,
      show (α * Real.exp (α * q.1)) * (qint α F (Real.exp (α * q.1), q.2) * φ (Real.exp (α * q.1)) q.2)
          = (α * Real.exp (α * q.1)) * (F (Real.exp (α * q.1)) q.2 * φ (Real.exp (α * q.1)) q.2
              * ((Real.exp (α * q.1)) ^ ((5 - α) / α) * Real.cos q.2)) from by
            simp only [qint]; ring]
    exact (hpb q).symm
  · intro hg
    refine hg.congr (Filter.Eventually.of_forall fun q => ?_)
    show (α * Real.exp (α * q.1)) • (qint α F (Real.exp (α * q.1), q.2) * φ (Real.exp (α * q.1)) q.2)
        = GRR α F q.1 q.2 * ψ q.1 q.2
    rw [smul_eq_mul,
      show (α * Real.exp (α * q.1)) * (qint α F (Real.exp (α * q.1), q.2) * φ (Real.exp (α * q.1)) q.2)
          = (α * Real.exp (α * q.1)) * (F (Real.exp (α * q.1)) q.2 * φ (Real.exp (α * q.1)) q.2
              * ((Real.exp (α * q.1)) ^ ((5 - α) / α) * Real.cos q.2)) from by
            simp only [qint]; ring]
    exact hpb q



end Work.EllipticEst.InteriorRegularity.Q0
