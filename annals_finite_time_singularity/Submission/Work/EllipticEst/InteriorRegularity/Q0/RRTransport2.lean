/-
Work module for `annals_finite_time_singularity`: the two-point ("non-degeneracy") argument
which shows that the source-side integrand of the transported weak formulation is integrable as
soon as some `Q0`-test function has non-vanishing left-hand side functional, together with the
real transport lemma `transport_real`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Elliptic.bslOp_add
import Submission.Work.EllipticEst.InteriorRegularity.Q0.RRTransport

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

/-! ## Test functions obtained as natural multiples -/

theorem tsupport_nsmul_add_subset {f g : ℝ → ℝ → ℝ} (n : ℕ) :
    tsupport (Function.uncurry (fun z θ : ℝ => f z θ + n * g z θ))
      ⊆ tsupport (Function.uncurry f) ∪ tsupport (Function.uncurry g) := by
  have hfun : Function.uncurry (fun z θ : ℝ => f z θ + n * g z θ)
      = fun p : ℝ × ℝ => Function.uncurry f p + n * Function.uncurry g p := by
    funext p; rfl
  have hs : Function.support (fun p : ℝ × ℝ =>
        Function.uncurry f p + (n : ℝ) * Function.uncurry g p)
      ⊆ Function.support (Function.uncurry f) ∪ Function.support (Function.uncurry g) := by
    intro p hp
    rw [Function.mem_support] at hp
    by_contra hcon
    have h1 : Function.uncurry f p = 0 := by
      by_contra h
      exact hcon (Or.inl (by rwa [Function.mem_support]))
    have h2 : Function.uncurry g p = 0 := by
      by_contra h
      exact hcon (Or.inr (by rwa [Function.mem_support]))
    exact hp (by rw [h1, h2, mul_zero, add_zero])
  rw [hfun]
  exact subset_trans (closure_mono hs) (le_of_eq closure_union)

/-- The `C^∞`, compactly supported combination `f + n * g` of two test functions on `Q0`. -/
theorem test_nsmul_add {f g : ℝ → ℝ → ℝ} (n : ℕ)
    (hfsm : ∀ m : ℕ, ContDiff ℝ m (Function.uncurry f))
    (hfc : HasCompactSupport (Function.uncurry f))
    (hfQ : tsupport (Function.uncurry f) ⊆ Work.FTS.EllipticEst.Q0)
    (hgsm : ∀ m : ℕ, ContDiff ℝ m (Function.uncurry g))
    (hgc : HasCompactSupport (Function.uncurry g))
    (hgQ : tsupport (Function.uncurry g) ⊆ Work.FTS.EllipticEst.Q0) :
    (∀ m : ℕ, ContDiff ℝ m (Function.uncurry (fun z θ : ℝ => f z θ + n * g z θ))) ∧
    HasCompactSupport (Function.uncurry (fun z θ : ℝ => f z θ + n * g z θ)) ∧
    tsupport (Function.uncurry (fun z θ : ℝ => f z θ + n * g z θ))
      ⊆ Work.FTS.EllipticEst.Q0 := by
  have hfun : Function.uncurry (fun z θ : ℝ => f z θ + n * g z θ)
      = fun p : ℝ × ℝ => Function.uncurry f p + n * Function.uncurry g p := by
    funext p; rfl
  refine ⟨?_, ?_, ?_⟩
  · intro m
    rw [hfun]
    exact (hfsm m).add ((contDiff_const (c := (n : ℝ))).mul (hgsm m))
  · rw [hfun]
    exact hfc.add (hgc.mul_left (f := fun _ : ℝ × ℝ => ((n : ℕ) : ℝ)))
  · exact subset_trans (tsupport_nsmul_add_subset n) (union_subset hfQ hgQ)

/-! ## The two-point trick -/

/-- The weak identity tested against the combination `f + n * g`. -/
theorem hweak_nsmul {α : ℝ} {Ψ F : ℝ → ℝ → ℝ}
    (hweak : ∀ φ : ℝ → ℝ → ℝ, (∀ n : ℕ, ContDiff ℝ n (Function.uncurry φ)) →
      HasCompactSupport (Function.uncurry φ) →
      tsupport (Function.uncurry φ) ⊆ Work.FTS.EllipticEst.Q0 →
      (∫ p in Work.FTS.EllipticEst.Q0, Lint α Ψ φ p)
        = ∫ p in Work.FTS.EllipticEst.Q0, Gint α F φ p)
    {f g : ℝ → ℝ → ℝ} (n : ℕ)
    (hfsm : ∀ m : ℕ, ContDiff ℝ m (Function.uncurry f))
    (hfc : HasCompactSupport (Function.uncurry f))
    (hfQ : tsupport (Function.uncurry f) ⊆ Work.FTS.EllipticEst.Q0)
    (hgsm : ∀ m : ℕ, ContDiff ℝ m (Function.uncurry g))
    (hgc : HasCompactSupport (Function.uncurry g))
    (hgQ : tsupport (Function.uncurry g) ⊆ Work.FTS.EllipticEst.Q0)
    (hfI : MeasureTheory.IntegrableOn (Lint α Ψ f) Work.FTS.EllipticEst.Q0)
    (hgI : MeasureTheory.IntegrableOn (Lint α Ψ g) Work.FTS.EllipticEst.Q0) :
    (∫ p in Work.FTS.EllipticEst.Q0, Gint α F (fun z θ : ℝ => f z θ + n * g z θ) p)
      = Lam α Ψ f + n * Lam α Ψ g := by
  obtain ⟨hνsm, hνc, hνQ⟩ := test_nsmul_add n hfsm hfc hfQ hgsm hgc hgQ
  have hhw := hweak (fun z θ : ℝ => f z θ + n * g z θ) hνsm hνc hνQ
  rw [← hhw]
  have hpoint : Set.EqOn (Lint α Ψ (fun z θ : ℝ => f z θ + n * g z θ))
      (fun p : ℝ × ℝ => Lint α Ψ f p + n * Lint α Ψ g p) Work.FTS.EllipticEst.Q0 :=
    Lint_nsmul_add α n (fun z θ _ => (hfsm 2).contDiffAt) (fun z θ _ => (hgsm 2).contDiffAt)
  have hQ0m : MeasurableSet Work.FTS.EllipticEst.Q0 := by
    rw [Q0_eq_prod]
    exact MeasurableSet.prod measurableSet_Ioi measurableSet_Ioo
  have hae : ∀ᵐ p ∂(MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)),
      p ∈ Work.FTS.EllipticEst.Q0 →
        Lint α Ψ (fun z θ : ℝ => f z θ + n * g z θ) p
          = Lint α Ψ f p + n * Lint α Ψ g p :=
    Filter.Eventually.of_forall (fun p hp => hpoint hp)
  rw [MeasureTheory.setIntegral_congr_ae hQ0m hae,
    MeasureTheory.integral_add hfI (hgI.const_mul n),
    MeasureTheory.integral_const_mul ((n : ℕ) : ℝ) (Lint α Ψ g), Lam_apply α Ψ f,
    Lam_apply α Ψ g]

/-- If `Ψ` is non-degenerate, then the source-side integrand is integrable. -/
theorem integrableOn_Gint_of_nondeg {α : ℝ} (hα : 0 < α) {F Ψ : ℝ → ℝ → ℝ}
    (hΨ : MeasureTheory.LocallyIntegrableOn (Function.uncurry Ψ) Work.FTS.EllipticEst.Q0)
    (hweak : ∀ φ : ℝ → ℝ → ℝ, (∀ n : ℕ, ContDiff ℝ n (Function.uncurry φ)) →
      HasCompactSupport (Function.uncurry φ) →
      tsupport (Function.uncurry φ) ⊆ Work.FTS.EllipticEst.Q0 →
      (∫ p in Work.FTS.EllipticEst.Q0, Lint α Ψ φ p)
        = ∫ p in Work.FTS.EllipticEst.Q0, Gint α F φ p)
    (hnd : Nondeg α Ψ)
    {ψ φ : ℝ → ℝ → ℝ} (hψ : ∀ n : ℕ, ContDiff ℝ n (Function.uncurry ψ))
    (hψc : HasCompactSupport (Function.uncurry ψ))
    (hψs : tsupport (Function.uncurry ψ) ⊆ stripRR)
    (hφsm : ∀ n : ℕ, ContDiff ℝ n (Function.uncurry φ))
    (hφc : HasCompactSupport (Function.uncurry φ))
    (hφQ : tsupport (Function.uncurry φ) ⊆ Work.FTS.EllipticEst.Q0)
    (hφval : ∀ z θ : ℝ, 0 < z → φ z θ = ψ ((1 / α) * Real.log z) θ)
    (hφbsl : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      Work.Elliptic.bslOp α φ z θ = kopDr ψ ((1 / α) * Real.log z) θ) :
    MeasureTheory.IntegrableOn (Gint α F φ) Work.FTS.EllipticEst.Q0 := by
  obtain ⟨η, hηsm, hηc, hηQ, hηne⟩ := hnd
  have hIntψ : MeasureTheory.Integrable (fun q : ℝ × ℝ => VRR α Ψ q.1 q.2 * kopDr ψ q.1 q.2) :=
    integrable_VRR_kopDr hα hΨ hψ hψc hψs
  have hφI : MeasureTheory.IntegrableOn (Lint α Ψ φ) Work.FTS.EllipticEst.Q0 :=
    integrableOn_qint_of_pullback hα hIntψ
      (fun q => (bsl_pullback_VRR hα hφQ hφbsl q).symm)
  have hηI : MeasureTheory.IntegrableOn (Lint α Ψ η) Work.FTS.EllipticEst.Q0 := by
    refine MeasureTheory.Integrable.of_integral_ne_zero ?_
    rwa [Lam_apply α Ψ η] at hηne
  by_cases h0 : Lam α Ψ φ = 0
  · -- use the multiples `1` and `2`
    have h1 : (∫ p in Work.FTS.EllipticEst.Q0,
          Gint α F (fun z θ : ℝ => φ z θ + ((1 : ℕ) : ℝ) * η z θ) p)
        = Lam α Ψ φ + ((1 : ℕ) : ℝ) * Lam α Ψ η :=
      hweak_nsmul hweak 1 hφsm hφc hφQ hηsm hηc hηQ hφI hηI
    have h2 : (∫ p in Work.FTS.EllipticEst.Q0,
          Gint α F (fun z θ : ℝ => φ z θ + ((2 : ℕ) : ℝ) * η z θ) p)
        = Lam α Ψ φ + ((2 : ℕ) : ℝ) * Lam α Ψ η :=
      hweak_nsmul hweak 2 hφsm hφc hφQ hηsm hηc hηQ hφI hηI
    have hI1 : MeasureTheory.IntegrableOn
        (Gint α F (fun z θ : ℝ => φ z θ + ((1 : ℕ) : ℝ) * η z θ))
        Work.FTS.EllipticEst.Q0 := by
      refine MeasureTheory.Integrable.of_integral_ne_zero ?_
      rw [h1, h0]
      simpa using hηne
    have hI2 : MeasureTheory.IntegrableOn
        (Gint α F (fun z θ : ℝ => φ z θ + ((2 : ℕ) : ℝ) * η z θ))
        Work.FTS.EllipticEst.Q0 := by
      refine MeasureTheory.Integrable.of_integral_ne_zero ?_
      rw [h2, h0]
      intro hcon
      have hcon' : (2 : ℝ) * Lam α Ψ η = 0 := by simpa using hcon
      exact hηne ((mul_eq_zero.mp hcon').resolve_left (by norm_num))
    have hsub : (fun p : ℝ × ℝ => Gint α F (fun z θ : ℝ => φ z θ + ((2 : ℕ) : ℝ) * η z θ) p
          - Gint α F (fun z θ : ℝ => φ z θ + ((1 : ℕ) : ℝ) * η z θ) p)
        = Gint α F η := by
      funext p
      simp only [Gint]
      push_cast
      ring
    have hηG : MeasureTheory.IntegrableOn (Gint α F η) Work.FTS.EllipticEst.Q0 := by
      rw [← hsub]
      exact hI2.sub hI1
    have hφG : (fun p : ℝ × ℝ => Gint α F (fun z θ : ℝ => φ z θ + ((1 : ℕ) : ℝ) * η z θ) p
          - Gint α F η p) = Gint α F φ := by
      funext p
      simp only [Gint]
      push_cast
      ring
    rw [← hφG]
    exact hI1.sub hηG
  · -- the functional does not vanish on `φ` itself
    have hG0 : (∫ p in Work.FTS.EllipticEst.Q0, Gint α F φ p) ≠ 0 := by
      rw [← hweak φ hφsm hφc hφQ]
      rwa [Lam_apply α Ψ φ] at h0
    exact MeasureTheory.Integrable.of_integral_ne_zero hG0

/-- The (real) transport of the weak formulation to the half-strip. -/
theorem transport_real {α : ℝ} (hα : 0 < α) {F Ψ : ℝ → ℝ → ℝ}
    (hΨ : MeasureTheory.LocallyIntegrableOn (Function.uncurry Ψ) Work.FTS.EllipticEst.Q0)
    (hweak : ∀ φ : ℝ → ℝ → ℝ, (∀ n : ℕ, ContDiff ℝ n (Function.uncurry φ)) →
      HasCompactSupport (Function.uncurry φ) →
      tsupport (Function.uncurry φ) ⊆ Work.FTS.EllipticEst.Q0 →
      (∫ p in Work.FTS.EllipticEst.Q0, Lint α Ψ φ p)
        = ∫ p in Work.FTS.EllipticEst.Q0, Gint α F φ p)
    {τ : ℝ → ℝ → ℝ} (hτ : ∀ n : ℕ, ContDiff ℝ n (Function.uncurry τ))
    (hτc : HasCompactSupport (Function.uncurry τ))
    (hτs : tsupport (Function.uncurry τ) ⊆ stripRR)
    {φ : ℝ → ℝ → ℝ} (hφsm : ∀ n : ℕ, ContDiff ℝ n (Function.uncurry φ))
    (hφc : HasCompactSupport (Function.uncurry φ))
    (hφQ : tsupport (Function.uncurry φ) ⊆ Work.FTS.EllipticEst.Q0)
    (hφval : ∀ z θ : ℝ, 0 < z → φ z θ = τ ((1 / α) * Real.log z) θ)
    (hφbsl : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      Work.Elliptic.bslOp α φ z θ = kopDr τ ((1 / α) * Real.log z) θ) :
    (∫ q : ℝ × ℝ, VRR α Ψ q.1 q.2 * kopDr τ q.1 q.2)
      = ∫ q : ℝ × ℝ, GRR α F q.1 q.2 * τ q.1 q.2 := by
  have hchain := LHS_chain hα hΨ hτ hτc hτs hφQ hφbsl
  have hhweak : (∫ p in Work.FTS.EllipticEst.Q0,
        Ψ p.1 p.2 * (Work.Elliptic.bslOp α φ p.1 p.2)
          * (p.1 ^ ((5 - α) / α) * Real.cos p.2))
      = ∫ p in Work.FTS.EllipticEst.Q0, Gint α F φ p :=
    hweak φ hφsm hφc hφQ
  by_cases hint : MeasureTheory.Integrable (fun q : ℝ × ℝ => GRR α F q.1 q.2 * τ q.1 q.2)
  · have hright : (∫ q : ℝ × ℝ, GRR α F q.1 q.2 * τ q.1 q.2)
        = ∫ p in Work.FTS.EllipticEst.Q0, Gint α F φ p :=
      RHS_chain hα hφval hφQ hint
    rw [hchain, hhweak, hright]
  · have hG : ¬ MeasureTheory.IntegrableOn (Gint α F φ) Work.FTS.EllipticEst.Q0 :=
      fun hcon => hint ((integrable_GRR_iff hα hφval hφQ).mpr hcon)
    have hL0 : (∫ p in Work.FTS.EllipticEst.Q0,
          Ψ p.1 p.2 * (Work.Elliptic.bslOp α φ p.1 p.2)
            * (p.1 ^ ((5 - α) / α) * Real.cos p.2)) = 0 :=
      hhweak.trans (MeasureTheory.integral_undef hG)
    rw [hchain, hL0, MeasureTheory.integral_undef hint]

/-- In the degenerate case, the left-hand side functional vanishes identically. -/
theorem VRR_kopDr_eq_zero_of_not_nondeg {α : ℝ} (hα : 0 < α) {Ψ : ℝ → ℝ → ℝ}
    (hΨ : MeasureTheory.LocallyIntegrableOn (Function.uncurry Ψ) Work.FTS.EllipticEst.Q0)
    (hnd : ¬ Nondeg α Ψ) {τ : ℝ → ℝ → ℝ} (hτ : ∀ n : ℕ, ContDiff ℝ n (Function.uncurry τ))
    (hτc : HasCompactSupport (Function.uncurry τ))
    (hτs : tsupport (Function.uncurry τ) ⊆ stripRR)
    {φ : ℝ → ℝ → ℝ} (hφsm : ∀ n : ℕ, ContDiff ℝ n (Function.uncurry φ))
    (hφc : HasCompactSupport (Function.uncurry φ))
    (hφQ : tsupport (Function.uncurry φ) ⊆ Work.FTS.EllipticEst.Q0)
    (hφval : ∀ z θ : ℝ, 0 < z → φ z θ = τ ((1 / α) * Real.log z) θ)
    (hφbsl : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      Work.Elliptic.bslOp α φ z θ = kopDr τ ((1 / α) * Real.log z) θ) :
    (∫ q : ℝ × ℝ, VRR α Ψ q.1 q.2 * kopDr τ q.1 q.2) = 0 := by
  rw [LHS_chain hα hΨ hτ hτc hτs hφQ hφbsl]
  have h : Lam α Ψ φ = 0 := by
    by_contra hne
    exact hnd ⟨φ, hφsm, hφc, hφQ, hne⟩
  exact h

end Work.EllipticEst.InteriorRegularity.Q0
