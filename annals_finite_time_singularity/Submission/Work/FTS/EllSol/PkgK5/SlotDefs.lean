import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.DivSinDefs
import Submission.Work.FTS.H2.DivQ.sliceBoundEta

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.PkgK5

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## The data functionals -/

/-- The `η`-weighted data `∫ (h')² sin(2θ)^{-η}`. -/
def pEta (h : ℝ → ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, (deriv h θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))

/-- The `γ`-weighted data `∫ (D_θ^m h')² sin(2θ)^{-γ}`. -/
def pGam (α : ℝ) (m : ℕ) (h : ℝ → ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ,
    (Work.Elliptic.Dth1Iter m (deriv h) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))

/-- The left-hand side `∫ (D_θ^i (h/sin 2θ))² sin(2θ)^{-γ}`. -/
def pLhs (α : ℝ) (i : ℕ) (h : ℝ → ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ,
    (Work.Elliptic.Dth1Iter i (Work.Elliptic.SinQ h) θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))

/-- The `η`-weighted integrand of the slice. -/
def etaInt (h : ℝ → ℝ) : ℝ → ℝ :=
  fun θ => (deriv h θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))

/-- The `γ`-weighted integrand of the `m`-th derivative of the slice. -/
def gamInt (α : ℝ) (m : ℕ) (h : ℝ → ℝ) : ℝ → ℝ :=
  fun θ => (Work.Elliptic.Dth1Iter m (deriv h) θ) ^ 2
    * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))

/-- The `γ`-weighted integrand of the `i`-th quotient iterate. -/
def lhsInt (α : ℝ) (i : ℕ) (h : ℝ → ℝ) : ℝ → ℝ :=
  fun θ => (Work.Elliptic.Dth1Iter i (Work.Elliptic.SinQ h) θ) ^ 2
    * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))

/-- The angular cut-off coefficient `2 cos 2θ` (an `abbrev`, so that it is definitionally
reducible to the explicit lambda). -/
abbrev cfun : ℝ → ℝ := fun θ => 2 * Real.cos (2 * θ)

/-! ## Elementary facts -/

theorem sin_two_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

theorem sin_two_pos_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

theorem gam_pos {α : ℝ} (hα : 0 < α) : 0 < Work.Spaces.gam α :=
  lt_trans zero_lt_one (Work.Spaces.one_lt_gam hα)

theorem eta_le_gam {α : ℝ} (hα : 0 < α) : Work.Spaces.eta ≤ Work.Spaces.gam α := by
  have h1 : Work.Spaces.eta < 1 := Work.Spaces.eta_lt_one
  have h2 : 1 < Work.Spaces.gam α := Work.Spaces.one_lt_gam hα
  linarith

theorem eta_le_four_sub_gam {α : ℝ} (hα1 : α ≤ 1) :
    -(Work.Spaces.eta) ≤ 4 - Work.Spaces.gam α := by
  have h1 : Work.Spaces.gam α ≤ 11 / 10 := by rw [Work.Spaces.gam]; linarith
  have h2 : 0 ≤ Work.Spaces.eta := Work.Spaces.eta_nonneg
  linarith

/-- `sin(2θ)^{-η} ≤ sin(2θ)^{-γ}` on `Iθ` (the `γ`-weight is the *larger* one). -/
theorem rpow_neg_eta_le_neg_gam {α : ℝ} (hα : 0 < α) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
  have hs0 := sin_two_nonneg_Iθ hθ
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  rcases eq_or_lt_of_le hs0 with h | h
  · rw [← h, Real.zero_rpow (ne_of_lt (neg_lt_zero.mpr (Work.Spaces.eta_pos))),
      Real.zero_rpow (ne_of_lt (neg_lt_zero.mpr (gam_pos hα)))]
  · exact Real.rpow_le_rpow_of_exponent_ge h hs1 (by linarith [eta_le_gam hα])

theorem pEta_nonneg (h : ℝ → ℝ) : 0 ≤ pEta h := by
  rw [pEta]
  exact MeasureTheory.setIntegral_nonneg measurableSet_Icc
    (fun θ hθ => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _))

theorem pGam_nonneg (α : ℝ) (m : ℕ) (h : ℝ → ℝ) : 0 ≤ pGam α m h := by
  rw [pGam]
  exact MeasureTheory.setIntegral_nonneg measurableSet_Icc
    (fun θ hθ => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _))

/-- Almost-everywhere statements on `Iθ` may be checked on the open interval. -/
theorem restrict_Iθ_eq_Ioo :
    MeasureTheory.volume.restrict Work.Spaces.Iθ
      = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  rw [Work.Spaces.Iθ]
  exact MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
      (b := Real.pi / 2)).symm

theorem ae_Iθ_of_forall_Ioo {p : ℝ → Prop}
    (h : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), p θ) :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), p θ := by
  rw [restrict_Iθ_eq_Ioo]
  exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo h

/-- `sin(2θ)^4 * (h/sin 2θ)² sin(2θ)^{-γ} ≤ (h/sin 2θ)² sin(2θ)^{-η}` on the open interval. -/
theorem sin_four_mul_le {α : ℝ} (hα1 : α ≤ 1) {h : ℝ → ℝ} {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    (Real.sin (2 * θ)) ^ 4 * (Work.Elliptic.SinQ h θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      ≤ (Work.Elliptic.SinQ h θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
  have hs := sin_two_pos_Ioo hθ
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hgam : Work.Spaces.gam α ≤ 11 / 10 := by rw [Work.Spaces.gam]; linarith
  have hη : 0 ≤ Work.Spaces.eta := Work.Spaces.eta_nonneg
  have hkey : (Real.sin (2 * θ)) ^ 4
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
    have h4 : (Real.sin (2 * θ)) ^ 4 = (Real.sin (2 * θ)) ^ (4 : ℝ) :=
      (Real.rpow_natCast (Real.sin (2 * θ)) 4).symm
    rw [h4]
    have hadd : (Real.sin (2 * θ)) ^ (4 : ℝ) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        = (Real.sin (2 * θ)) ^ ((4 : ℝ) + -(Work.Spaces.gam α)) :=
      (Real.rpow_add hs (4 : ℝ) (-(Work.Spaces.gam α))).symm
    rw [hadd, show (4 : ℝ) + -(Work.Spaces.gam α) = 4 - Work.Spaces.gam α by ring]
    exact Real.rpow_le_rpow_of_exponent_ge hs hs1 (by linarith)
  have hQ : 0 ≤ (Work.Elliptic.SinQ h θ) ^ 2 := sq_nonneg _
  calc (Real.sin (2 * θ)) ^ 4 * (Work.Elliptic.SinQ h θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      = ((Real.sin (2 * θ)) ^ 4
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) * (Work.Elliptic.SinQ h θ) ^ 2 := by
        ring
    _ ≤ ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) * (Work.Elliptic.SinQ h θ) ^ 2 :=
        mul_le_mul_of_nonneg_right hkey hQ
    _ = (Work.Elliptic.SinQ h θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by ring

/-! ## The level-zero term via the sharp weighted Hardy inequality -/

/-- The constant of the sharp weighted Hardy inequality `Work.FTS.H2.DivQ.sliceBoundEta`. -/
noncomputable def Ceta : ℝ := Classical.choose (Work.FTS.H2.DivQ.sliceBoundEta)

theorem Ceta_pos : 0 < Ceta := (Classical.choose_spec (Work.FTS.H2.DivQ.sliceBoundEta)).1

/-- The level-zero term `(h/sin 2θ)² sin(2θ)^{-η}` is integrable and controlled by the
`η`-weighted data (`Work.FTS.H2.DivQ.sliceBoundEta`). -/
theorem levelZeroData {h : ℝ → ℝ} (hsm : ContDiffOn ℝ (↑(⊤ : ℕ∞)) h (Set.Ioo 0 (Real.pi / 2)))
    (h0 : Tendsto h (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hπ : Tendsto h (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0))
    (hD : MeasureTheory.IntegrableOn (etaInt h) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn
        (fun θ => (Work.Elliptic.SinQ h θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ,
          (Work.Elliptic.SinQ h θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        ≤ Ceta * pEta h := by
  have hmain := (Classical.choose_spec (Work.FTS.H2.DivQ.sliceBoundEta)).2 h hsm h0 hπ hD
  have hEq : (fun θ => (Work.Elliptic.SinQ h θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      = fun θ => (h θ / Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := rfl
  refine ⟨?_, ?_⟩
  · simpa only [hEq] using hmain.1
  · rw [pEta, Ceta]
    simpa only [hEq] using hmain.2

/-! ## Smoothness of the quotient iterates on the open interval -/

theorem contDiffOn_SinQ {h : ℝ → ℝ}
    (hsm : ContDiffOn ℝ (↑(⊤ : ℕ∞)) h (Set.Ioo 0 (Real.pi / 2))) :
    ContDiffOn ℝ (↑(⊤ : ℕ∞)) (Work.Elliptic.SinQ h) (Set.Ioo 0 (Real.pi / 2)) := by
  have hsin : ContDiffOn ℝ (↑(⊤ : ℕ∞)) (fun θ : ℝ => Real.sin (2 * θ))
      (Set.Ioo 0 (Real.pi / 2)) := by fun_prop
  exact hsm.div hsin (fun θ hθ => ne_of_gt (sin_two_pos_Ioo hθ))

theorem contDiffOn_Dth1Iter_SinQ {h : ℝ → ℝ}
    (hsm : ContDiffOn ℝ (↑(⊤ : ℕ∞)) h (Set.Ioo 0 (Real.pi / 2))) (l : ℕ) :
    ContDiffOn ℝ (↑(⊤ : ℕ∞)) (Work.Elliptic.Dth1Iter l (Work.Elliptic.SinQ h))
      (Set.Ioo 0 (Real.pi / 2)) := by
  induction l with
  | zero => simpa using contDiffOn_SinQ hsm
  | succ l ih =>
      rw [Work.Elliptic.Dth1Iter_succ]
      show ContDiffOn ℝ (↑(⊤ : ℕ∞))
        (fun θ => Real.sin (2 * θ) * deriv (Work.Elliptic.Dth1Iter l (Work.Elliptic.SinQ h)) θ)
        (Set.Ioo 0 (Real.pi / 2))
      have hs : ContDiffOn ℝ (↑(⊤ : ℕ∞)) (fun θ : ℝ => Real.sin (2 * θ))
          (Set.Ioo 0 (Real.pi / 2)) := by fun_prop
      exact hs.mul (ih.deriv_of_isOpen isOpen_Ioo (by simp))

theorem continuousOn_lhsInt {α : ℝ} {i : ℕ} {h : ℝ → ℝ}
    (hsm : ContDiffOn ℝ (↑(⊤ : ℕ∞)) h (Set.Ioo 0 (Real.pi / 2))) :
    ContinuousOn (lhsInt α i h) (Set.Ioo 0 (Real.pi / 2)) := by
  have h1 := (contDiffOn_Dth1Iter_SinQ hsm i).continuousOn
  have h2 : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      (Set.Ioo 0 (Real.pi / 2)) := by
    refine ContinuousOn.rpow_const ?_ (fun θ hθ => Or.inl (ne_of_gt (sin_two_pos_Ioo hθ)))
    fun_prop
  exact (h1.pow 2).mul h2

theorem aesm_lhsInt {α : ℝ} {i : ℕ} {h : ℝ → ℝ}
    (hsm : ContDiffOn ℝ (↑(⊤ : ℕ∞)) h (Set.Ioo 0 (Real.pi / 2))) :
    AEStronglyMeasurable (lhsInt α i h) (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  have h := (continuousOn_lhsInt (α := α) (i := i) hsm).aestronglyMeasurable
    (μ := MeasureTheory.volume) measurableSet_Ioo
  rwa [restrict_Iθ_eq_Ioo]


end Work.FTS.EllSol.PkgK5
