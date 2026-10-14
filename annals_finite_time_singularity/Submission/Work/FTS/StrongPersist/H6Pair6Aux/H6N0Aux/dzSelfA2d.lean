import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.H2.STBasic
import Submission.Work.FTS.H2.STEasyDefs
import Submission.Work.FTS.H2.STEasyId
import Submission.Work.FTS.H2.T1HardSlice
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.dzSelf2d
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.thetaHardyLeft
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.thetaHardyRight
import Submission.Work.FTS_EllLimOK.BoxDataH.BoxUniform
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.one_le_mul_w
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.EllSol.PkgK5.SlotDefs =====
section

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
end
end
-- ===== merged: Submission.Work.FTS.H2.EMB.EM_gside =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2.EMB


end Work.FTS.H2.EMB
end
-- ===== merged: Submission.Work.FTS.H2.EMB.EM_term_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2.EMB


end Work.FTS.H2.EMB
end
-- ===== merged: Submission.Work.FTS.H2.HardIntegrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Elementary exponent identities on `Iθ`

All of them are instances of `Real.rpow_add'` (which, unlike `Real.rpow_add`, does not require
a *positive* base, only that the sum of the exponents be non-zero — this is what makes them
valid also at the two endpoints of `Iθ`, where `sin(2θ) = 0`). -/




/-! ## Small numerical lemmas -/



/-! ## Slices of `SmoothNbhd` functions and their box bounds -/


/-! ## The pointwise bound of `HardF` -/



/-! ## A.e. strong measurability of the slice -/


/-! ## The main statement -/


end Work.FTS.H2
end
end
-- ===== merged: Submission.Work.FTS.H2.STEasyBnd =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2

set_option autoImplicit false
set_option maxHeartbeats 8000000




end Work.FTS.H2
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux.dzSelfA2d =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux

/-!
## The weighted radial self-pairing with a coefficient `A(z,θ)`

With `w z = (1+z)²/z²`, `ρ = w²`, `s z = z ρ z = (1+z)⁴/z³` and `D = z ∂_z`, the exact
identity

`s' Y² + 2 ρ (DY) Y = (s Y²)'`

integrated against a coefficient `ψ` with `|ψ| ≤ A`, `|z ψ'| ≤ B` on `(0,∞)` gives (FTC on
`[ε,M]`, the boundary terms being killed along the dyadic minimiser sequences of `H = w²Y²`,
see `T5bAux.dzSelf1dW`)

`|∫_0^∞ w² ψ (zY') Y| ≤ (3A + B) ∫_0^∞ w² Y²`,

and with `A = B = K` the constant is `4K ≤ 5K`, which is `dzSelfA1d` below.

Applying this slicewise in `θ` with the coefficient `ψ = A(·,θ)` (hypotheses `hAbd`, `hAdz`
at fixed `θ ∈ (0,π/2)`), multiplying by `σ θ > 0` and integrating over `θ` against the
angular weight `σ` (Fubini, using the product-integrability hypotheses `hF`, `hD2`, `hcross`)
gives `dzSelfA2d`.
-/

noncomputable section

/-- **The one-dimensional slice bound.**  For a coefficient `ψ` with `|ψ| ≤ K` and
`|z ψ'| ≤ K` on `(0,∞)` and a radial profile `Y`,

`|∫_0^∞ w² ψ (z Y') Y| ≤ 5 K ∫_0^∞ w² Y²`.

This is `T5bAux.dzSelf1dW` with `A = B = K` (which gives the constant `3K + K = 4K ≤ 5K`). -/
theorem dzSelfA1d {K : ℝ} {ψ Y : ℝ → ℝ}
    (hK0 : 0 ≤ K)
    (hψsm : ContDiffOn ℝ 1 ψ (Set.Ioi 0))
    (hψA : ∀ z ∈ Set.Ioi (0 : ℝ), |ψ z| ≤ K)
    (hψB : ∀ z ∈ Set.Ioi (0 : ℝ), |z * deriv ψ z| ≤ K)
    (hY : ContDiffOn ℝ 1 Y (Set.Ioi 0))
    (hF : MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * (Y z) ^ 2)
      (Set.Ioi 0))
    (hD : MeasureTheory.IntegrableOn
      (fun z => (Work.Spaces.w z) ^ 2 * (z * deriv Y z) ^ 2) (Set.Ioi 0)) :
    |∫ z in Set.Ioi (0 : ℝ),
        (Work.Spaces.w z) ^ 2 * (ψ z * ((z * deriv Y z) * Y z))|
      ≤ 5 * K * ∫ z in Set.Ioi (0 : ℝ), (Work.Spaces.w z) ^ 2 * (Y z) ^ 2 := by
  have h1 := T5bAux.dzSelf1dW (ψ := ψ) (Y := Y) (A := K) (B := K)
    hK0 hK0 hψsm hψA hψB hY hF hD
  have hI0 : 0 ≤ ∫ z in Set.Ioi (0 : ℝ), (Work.Spaces.w z) ^ 2 * (Y z) ^ 2 :=
    setIntegral_nonneg measurableSet_Ioi (fun z _ => by positivity)
  have hIeq : (∫ z in Set.Ioi (0 : ℝ),
        (Work.Spaces.w z) ^ 2 * (ψ z * ((z * deriv Y z) * Y z)))
      = ∫ z in Set.Ioi (0 : ℝ),
        (Work.Spaces.w z) ^ 2 * ψ z * ((z * deriv Y z) * Y z) :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => by ring)
  calc |∫ z in Set.Ioi (0 : ℝ),
        (Work.Spaces.w z) ^ 2 * (ψ z * ((z * deriv Y z) * Y z))|
      = |∫ z in Set.Ioi (0 : ℝ),
          (Work.Spaces.w z) ^ 2 * ψ z * ((z * deriv Y z) * Y z)| := by rw [hIeq]
    _ ≤ (3 * K + K) * ∫ z in Set.Ioi (0 : ℝ), (Work.Spaces.w z) ^ 2 * (Y z) ^ 2 := h1
    _ = 4 * K * ∫ z in Set.Ioi (0 : ℝ), (Work.Spaces.w z) ^ 2 * (Y z) ^ 2 := by ring
    _ ≤ 5 * K * ∫ z in Set.Ioi (0 : ℝ), (Work.Spaces.w z) ^ 2 * (Y z) ^ 2 := by
        have hcoef : 4 * K ≤ 5 * K := by linarith
        calc 4 * K * ∫ z in Set.Ioi (0 : ℝ), (Work.Spaces.w z) ^ 2 * (Y z) ^ 2
            = (4 * K) * (∫ z in Set.Ioi (0 : ℝ), (Work.Spaces.w z) ^ 2 * (Y z) ^ 2) := by
              ring
          _ ≤ (5 * K) * (∫ z in Set.Ioi (0 : ℝ), (Work.Spaces.w z) ^ 2 * (Y z) ^ 2) :=
              mul_le_mul_of_nonneg_right hcoef hI0
          _ = 5 * K * ∫ z in Set.Ioi (0 : ℝ), (Work.Spaces.w z) ^ 2 * (Y z) ^ 2 := by ring

theorem dzSelfA2d {σ : ℝ → ℝ} {A V : ℝ → ℝ → ℝ} {K : ℝ}
    (hK0 : 0 ≤ K)
    (hσm : AEMeasurable σ (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hσpos : ∀ θ ∈ Set.Ioo 0 (π / 2), 0 < σ θ)
    (hA : ∀ θ ∈ Set.Ioo 0 (π / 2), ContDiffOn ℝ 1 (fun z => A z θ) (Set.Ioi 0))
    (hAbd : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 → |A z θ| ≤ K)
    (hAdz : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |z * deriv (fun z' => A z' θ) z| ≤ K)
    (hV : ∀ θ ∈ Set.Ioo 0 (π / 2), ContDiffOn ℝ 1 (fun z => V z θ) (Set.Ioi 0))
    (hVae : AEMeasurable (Function.uncurry V)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
    (hF : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * σ p.2 * (V p.1 p.2) ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
    (hD2 : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * σ p.2
        * (p.1 * Work.Spaces.pz V p.1 p.2) ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
    (hcross : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * σ p.2
        * (A p.1 p.2 * ((p.1 * Work.Spaces.pz V p.1 p.2) * V p.1 p.2)))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ))) :
    |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.w z) ^ 2 * σ θ * (A z θ * ((z * Work.Spaces.pz V z θ) * V z θ))|
      ≤ 5 * K * ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.w z) ^ 2 * σ θ * (V z θ) ^ 2 := by
  have hΛz : MeasureTheory.volume.restrict Work.Spaces.Iz
      = MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) :=
    Measure.restrict_congr_set dzSelf2d_Iz_ae
  have hΛθ : MeasureTheory.volume.restrict Work.Spaces.Iθ
      = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) :=
    Measure.restrict_congr_set dzSelf2d_Ith_ae
  have haeθ : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      θ ∈ Set.Ioo (0 : ℝ) (π / 2) := by
    have h := MeasureTheory.ae_restrict_mem (μ := (MeasureTheory.volume : Measure ℝ))
      (s := Set.Ioo (0 : ℝ) (π / 2)) measurableSet_Ioo
    rwa [← hΛθ] at h
  have hσae : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), 0 < σ θ :=
    haeθ.mono (fun θ hmem => hσpos θ hmem)
  -- slice integrability of `w²V²` for a.e. `θ` (divide by `σ θ > 0`)
  have hsliceF : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * (V z θ) ^ 2)
        (Set.Ioi 0) := by
    have h1 : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        MeasureTheory.Integrable
          (fun z => (Work.Spaces.w z) ^ 2 * σ θ * (V z θ) ^ 2)
          (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
      MeasureTheory.Integrable.prod_left_ae hF
    filter_upwards [h1, hσae] with θ hθ hpos
    have h2 : MeasureTheory.Integrable
        (fun z => σ θ * ((Work.Spaces.w z) ^ 2 * (V z θ) ^ 2))
        (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
      simpa only [mul_comm, mul_left_comm, mul_assoc] using hθ
    have h3 : MeasureTheory.Integrable
        (fun z => (Work.Spaces.w z) ^ 2 * (V z θ) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
      (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr (ne_of_gt hpos))
        (fun z => (Work.Spaces.w z) ^ 2 * (V z θ) ^ 2)).mp h2
    rw [hΛz] at h3
    exact h3
  -- slice integrability of `w²(z∂_zV)²` for a.e. `θ`
  have hsliceD : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      MeasureTheory.IntegrableOn
        (fun z => (Work.Spaces.w z) ^ 2 * (z * Work.Spaces.pz V z θ) ^ 2)
        (Set.Ioi 0) := by
    have h1 : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        MeasureTheory.Integrable
          (fun z => (Work.Spaces.w z) ^ 2 * σ θ * (z * Work.Spaces.pz V z θ) ^ 2)
          (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
      MeasureTheory.Integrable.prod_left_ae hD2
    filter_upwards [h1, hσae] with θ hθ hpos
    have h2 : MeasureTheory.Integrable
        (fun z => σ θ * ((Work.Spaces.w z) ^ 2 * (z * Work.Spaces.pz V z θ) ^ 2))
        (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
      simpa only [mul_comm, mul_left_comm, mul_assoc] using hθ
    have h3 : MeasureTheory.Integrable
        (fun z => (Work.Spaces.w z) ^ 2 * (z * Work.Spaces.pz V z θ) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
      (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr (ne_of_gt hpos))
        (fun z => (Work.Spaces.w z) ^ 2 * (z * Work.Spaces.pz V z θ) ^ 2)).mp h2
    rw [hΛz] at h3
    exact h3
  -- the a.e.-`θ` slicewise 1-D bound with coefficient `A(·,θ)`
  have hkey : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      |∫ z in Work.Spaces.Iz,
          (Work.Spaces.w z) ^ 2 * σ θ * (A z θ * ((z * Work.Spaces.pz V z θ) * V z θ))|
        ≤ 5 * K * (σ θ * ∫ z in Set.Ioi (0 : ℝ),
            (Work.Spaces.w z) ^ 2 * (V z θ) ^ 2) := by
    filter_upwards [haeθ, hσae, hsliceF, hsliceD] with θ hmem hpos hsf hsd
    have h1 : |∫ z in Set.Ioi (0 : ℝ),
          (Work.Spaces.w z) ^ 2
            * (A z θ * ((z * deriv (fun z' => V z' θ) z) * V z θ))|
        ≤ 5 * K * ∫ z in Set.Ioi (0 : ℝ), (Work.Spaces.w z) ^ 2 * (V z θ) ^ 2 :=
      dzSelfA1d (K := K) hK0 (hA θ hmem)
        (fun z hz => hAbd z θ hz hmem.1 hmem.2)
        (fun z hz => hAdz z θ hz hmem.1 hmem.2) (hV θ hmem) hsf hsd
    have hfun : (fun z => (Work.Spaces.w z) ^ 2 * σ θ
          * (A z θ * ((z * Work.Spaces.pz V z θ) * V z θ)))
        = fun z => σ θ * ((Work.Spaces.w z) ^ 2
          * (A z θ * ((z * deriv (fun z' => V z' θ) z) * V z θ))) := by
      funext z
      simp only [Work.Spaces.pz]
      ring
    have hL : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * σ θ
          * (A z θ * ((z * Work.Spaces.pz V z θ) * V z θ)))
        = σ θ * ∫ z in Set.Ioi (0 : ℝ), (Work.Spaces.w z) ^ 2
            * (A z θ * ((z * deriv (fun z' => V z' θ) z) * V z θ)) := by
      rw [hfun, setIntegral_congr_set dzSelf2d_Iz_ae]
      rw [MeasureTheory.integral_const_mul]
    rw [hL, abs_mul, abs_of_pos hpos]
    calc σ θ * |∫ z in Set.Ioi (0 : ℝ), (Work.Spaces.w z) ^ 2
            * (A z θ * ((z * deriv (fun z' => V z' θ) z) * V z θ))|
        ≤ σ θ * (5 * K * ∫ z in Set.Ioi (0 : ℝ),
            (Work.Spaces.w z) ^ 2 * (V z θ) ^ 2) :=
          mul_le_mul_of_nonneg_left h1 hpos.le
      _ = 5 * K * (σ θ * ∫ z in Set.Ioi (0 : ℝ),
            (Work.Spaces.w z) ^ 2 * (V z θ) ^ 2) := by ring
  -- integrability of the upper bound
  have hψint : MeasureTheory.Integrable
      (fun θ => σ θ * ∫ z in Set.Ioi (0 : ℝ), (Work.Spaces.w z) ^ 2 * (V z θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    have h := MeasureTheory.Integrable.integral_prod_right hF
    have hfun : (fun θ => ∫ z, (Work.Spaces.w z) ^ 2 * σ θ * (V z θ) ^ 2
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iz))
        = fun θ => σ θ * ∫ z in Set.Ioi (0 : ℝ),
            (Work.Spaces.w z) ^ 2 * (V z θ) ^ 2 := by
      funext θ
      rw [show (fun z => (Work.Spaces.w z) ^ 2 * σ θ * (V z θ) ^ 2)
          = fun z => σ θ * ((Work.Spaces.w z) ^ 2 * (V z θ) ^ 2) from by
            funext z; ring]
      rw [MeasureTheory.integral_const_mul]
      rw [setIntegral_congr_set dzSelf2d_Iz_ae]
    rwa [hfun] at h
  have hRHSint : MeasureTheory.Integrable
      (fun θ => 5 * K * (σ θ * ∫ z in Set.Ioi (0 : ℝ),
        (Work.Spaces.w z) ^ 2 * (V z θ) ^ 2))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    hψint.const_mul (5 * K)
  have hLHSint : MeasureTheory.Integrable
      (fun θ => |∫ z in Work.Spaces.Iz,
        (Work.Spaces.w z) ^ 2 * σ θ * (A z θ * ((z * Work.Spaces.pz V z θ) * V z θ))|)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    have h := MeasureTheory.Integrable.integral_prod_right hcross
    exact h.abs
  -- Fubini and the comparison
  have hswap : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.w z) ^ 2 * σ θ * (A z θ * ((z * Work.Spaces.pz V z θ) * V z θ)))
      = ∫ θ in Work.Spaces.Iθ, ∫ z in Work.Spaces.Iz,
        (Work.Spaces.w z) ^ 2 * σ θ * (A z θ * ((z * Work.Spaces.pz V z θ) * V z θ)) :=
    MeasureTheory.integral_integral_swap hcross
  calc |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.w z) ^ 2 * σ θ * (A z θ * ((z * Work.Spaces.pz V z θ) * V z θ))|
      = |∫ θ in Work.Spaces.Iθ, ∫ z in Work.Spaces.Iz,
          (Work.Spaces.w z) ^ 2 * σ θ
            * (A z θ * ((z * Work.Spaces.pz V z θ) * V z θ))| := by rw [hswap]
    _ ≤ ∫ θ in Work.Spaces.Iθ,
          |∫ z in Work.Spaces.Iz,
            (Work.Spaces.w z) ^ 2 * σ θ
              * (A z θ * ((z * Work.Spaces.pz V z θ) * V z θ))| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ θ in Work.Spaces.Iθ, 5 * K * (σ θ * ∫ z in Set.Ioi (0 : ℝ),
          (Work.Spaces.w z) ^ 2 * (V z θ) ^ 2) :=
        integral_mono_ae hLHSint hRHSint hkey
    _ = 5 * K * ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.w z) ^ 2 * σ θ * (V z θ) ^ 2 := by
        rw [MeasureTheory.integral_const_mul]
        congr 1
        rw [show (fun θ => σ θ * ∫ z in Set.Ioi (0 : ℝ),
              (Work.Spaces.w z) ^ 2 * (V z θ) ^ 2)
            = fun θ => ∫ z in Work.Spaces.Iz,
              (Work.Spaces.w z) ^ 2 * σ θ * (V z θ) ^ 2 from by
              funext θ
              rw [← MeasureTheory.integral_const_mul]
              rw [← setIntegral_congr_set dzSelf2d_Iz_ae]
              exact MeasureTheory.integral_congr_ae
                (Filter.Eventually.of_forall fun z => by ring)]
        rw [← MeasureTheory.integral_integral_swap hF]

end

end Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux
end
