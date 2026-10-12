import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1B.perBoxCrudeLower
import Submission.Work.BoseFixR.occChiIntegrand_integrable
import Submission.Work.BoseFixR.qLHSwordIntegrand_lower
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory Metric Filter
open scoped Real Topology BigOperators ENNReal

namespace Work.BoseFixR

open _root_.BoseGases Submission.BoseGases Work.BoseBox Work.BoseBoxFix Work.UBB
open Work.SmallBoxSliding

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# `Submission.Work.BoseFixR.PerBoxWordCrudeLow`

The **low-occupancy half** of the crude per-box lower bound for the sliding word
`Work.BoseFixB1.sbWord` (FS `thm:smallbox` with the positive mean-field square dropped).

The statement (verbatim at the end of this file) is: there is a smallness threshold `ε₀` such that
for *every* `K ≥ 0` there is `C ≥ 0` with, at every admissible `μ`, every box state `Φ`, every `u`,

  `occChi_{B(u)}(Φ) ≤ K·(μ·χ-mass(u) + 1)·‖Φ‖²  ⟹  −(C(μ²(a v)χ-mass(u) + μ(a v)))‖Φ‖² ≤ sbWord`.

## The proof (all constants free)

`sbWord = sbKin + sbPot` with `sbKin ≥ 0` (`Work.UBBInputs9.A.tBwordBInd_nonneg`) and
`sbPot = qLHSwordB h M ℓ d μ u Φ = ∫_{abox n ℓ} Φ(x)²·(−μΣᵢ∫_y w_{1,B(u)}(xᵢ,y) + ½Σ_{pairs} w_{B(u)})`.

* the pair kernel is pointwise `≥ 0` (`Work.BoseFixB1S.wSmallPair_nonneg`), so the pair term may be
  dropped;
* the one-body fibre obeys `|∫_y w_{1,B(u)}(x,y)dy| ≤ Cf·(a v)·χ_{B(u)}(x)` in the regime
  (`Work.BoseFixB1B.fibre_chiB_le`), so the chemical term dominates
  `−μ·(Cf·a v)·Σᵢχ_{B(u)}(xᵢ)` pointwise.

Integrating (with the junk-safe comparison `integral_le_integral_of_le_of_nonpos`, because the
Bochner integral of the `qLHSwordB` integrand need not be finite) gives

  `qLHSwordB ≥ −μ·(Cf·a v)·occChi_{B(u)}(Φ) ≥ −(Cf·K)(μ²(a v)χ-mass + μ(a v))‖Φ‖²`,

the second step being exactly the occupancy hypothesis.  This is the whole content: the low-occupancy
hypothesis is what replaces FS's per-box analysis (the mean-field/excited-count payment), which is
needed only in the complementary `PerBoxWordCrudeHigh` regime.
-/

/-! ## 0.  The integrands, and the junk-safe comparison of integrals -/

/-- The integrand of `occChi`: `Φ(x)²·Σᵢχ_{B(u)}(xᵢ)`. -/
noncomputable def occIntegrand (M : ℕ) (ℓ d : ℝ) (u : EuclideanSpace ℝ (Fin 3)) {n : ℕ}
    (Φ : Submission.BoseGases.X n → ℝ) : Submission.BoseGases.X n → ℝ :=
  fun x => (Φ x) ^ 2 * ∑ i : Fin n, Submission.BoseGases.chiSmallB M ℓ d u (x i)

/-- The **lower-bound integrand** of the low-occupancy crude bound:
`Φ(x)²·(−c·Σᵢχ_{B(u)}(xᵢ))` with `c = μ·(Cf·(a v))`. -/
noncomputable def lowIntegrand (M : ℕ) (ℓ d : ℝ) (u : EuclideanSpace ℝ (Fin 3)) (c : ℝ) {n : ℕ}
    (Φ : Submission.BoseGases.X n → ℝ) : Submission.BoseGases.X n → ℝ :=
  fun x => (Φ x) ^ 2 * (- c * ∑ i : Fin n, Submission.BoseGases.chiSmallB M ℓ d u (x i))

/-- The integrand of `Work.SmallBoxSliding.qLHSwordB` at the localised kernels
`w_{B(u)} = wSmallPair M ℓ d u v`, `w_{1,B(u)} = wSmall1Pair h M ℓ d u`. -/
noncomputable def sbPotIntegrand {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (M : ℕ) (ℓ d : ℝ) (u : EuclideanSpace ℝ (Fin 3)) (μ : ℝ) {n : ℕ}
    (Φ : Submission.BoseGases.X n → ℝ) : Submission.BoseGases.X n → ℝ :=
  fun x => (Φ x) ^ 2 * (- μ * (∑ i : Fin n,
        Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u) (x i))
      + (1 / 2) * (∑ p ∈ Submission.BoseGases.pairSet n,
          Submission.BoseGases.wSmallPair M ℓ d u v (x p.1) (x p.2)))

/-- `occChi` **is** the integral of `occIntegrand`. -/
lemma occChi_eq_integral (M : ℕ) (ℓ d : ℝ) (u : EuclideanSpace ℝ (Fin 3)) {n : ℕ}
    (Φ : Submission.BoseGases.X n → ℝ) :
    Work.BoseFixR.occChi M ℓ d u Φ
      = ∫ x in Submission.BoseGases.abox n ℓ, occIntegrand M ℓ d u Φ x := rfl

/-- `qLHSwordB` **is** the integral of `sbPotIntegrand`. -/
lemma qLHSwordB_eq_integral {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (M : ℕ) (ℓ d : ℝ) (u : EuclideanSpace ℝ (Fin 3)) (μ : ℝ) {n : ℕ}
    (Φ : Submission.BoseGases.X n → ℝ) :
    Work.SmallBoxSliding.qLHSwordB h M ℓ d μ u Φ
      = ∫ x in Submission.BoseGases.abox n ℓ, sbPotIntegrand h M ℓ d u μ Φ x := by
  rw [Work.SmallBoxSliding.qLHSwordB, Submission.BoseGases.qLHSword]
  rfl

/-- **The junk-safe comparison of integrals.**  If `G ≤ F` pointwise, `G` is integrable and `G ≤ 0`
pointwise, then `∫G ≤ ∫F`.  (The only non-elementary point is that the Bochner integral of a
non-integrable function is `0`, so the case `¬Integrable F` is immediate.) -/
lemma integral_le_integral_of_le_of_nonpos {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F G : α → ℝ} (hFG : ∀ a, G a ≤ F a) (hGint : Integrable G μ) (hG0 : ∀ a, G a ≤ 0) :
    ∫ a, G a ∂μ ≤ ∫ a, F a ∂μ := by
  by_cases hF : Integrable F μ
  · exact integral_mono hGint hF hFG
  · rw [integral_undef hF]
    exact integral_nonpos_of_ae (ae_of_all _ hG0)

/-! ## 2.  The target -/

theorem PerBoxWordCrudeLow {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ K : ℝ, 0 ≤ K → ∃ C : ℝ, 0 ≤ C ∧
        ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
          ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
            (u : EuclideanSpace ℝ (Fin 3)),
            Work.BoseFixR.occChi (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
                (Φ : Submission.BoseGases.X n → ℝ)
              ≤ Work.BoseFixR.crudeThreshold v K μ
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                  (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
                  (Φ : Submission.BoseGases.X n → ℝ) →
            -(C * (μ ^ 2 * _root_.BoseGases.a v
                  * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
                + μ * _root_.BoseGases.a v))
              * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
            ≤ Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ) := by
  classical
  obtain ⟨ε₀, Cf, hε₀, hCf, hfib⟩ :=
    Work.BoseFixB1B.fibre_chiB_le (v := v) h hv hv1 hvrad hR hv_supp hav
  refine ⟨ε₀, hε₀, ?_⟩
  intro K hK
  refine ⟨Cf * K, mul_nonneg hCf hK, ?_⟩
  intro μ hAdm n Φ u hocc
  -- ## the admissible-point facts
  have hμ : 0 < μ := hAdm.1
  have hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := Work.BoseFixB1.adm_ell_pos hAdm
  have heT : 0 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT :=
    (Work.BoseFixB1.adm_eT_bounds hAdm).1
  have hΦc : Continuous (Φ : Submission.BoseGases.X n → ℝ) := Φ.contDiff.continuous
  have hnorm0 : 0 ≤ Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) :=
    Work.BoseFixB1.normB_nonneg _
  have hchiB : ∀ z : EuclideanSpace ℝ (Fin 3),
      0 ≤ Submission.BoseGases.chiSmallB (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u z :=
    fun z => Submission.BoseGases.chiSmallB_nonneg _ _ _ _ _
  -- ## the fibre bound at this `μ`, in `w1Fibre` form
  have hfibu : ∀ z : EuclideanSpace ℝ (Fin 3),
      |Submission.BoseGases.w1Fibre (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Submission.BoseGases.wSmall1Pair h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) z|
        ≤ (Cf * _root_.BoseGases.a v) * Submission.BoseGases.chiSmallB
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u z := by
    intro z
    rw [Submission.BoseGases.w1Fibre]
    exact hfib μ hAdm u z
  -- ## (i)  the pointwise lower bound of the `qLHSwordB` integrand
  have hpoint : ∀ x : Submission.BoseGases.X n,
      lowIntegrand (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
          (μ * (Cf * _root_.BoseGases.a v)) (Φ : Submission.BoseGases.X n → ℝ) x
        ≤ sbPotIntegrand h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u μ
            (Φ : Submission.BoseGases.X n → ℝ) x := by
    intro x
    simpa only [lowIntegrand, sbPotIntegrand] using
      qLHSwordIntegrand_lower (v := v) (h := h) hv (le_of_lt hμ)
        (Cf := Cf * _root_.BoseGases.a v) (mul_nonneg hCf (le_of_lt hav)) hfibu
        (Φ : Submission.BoseGases.X n → ℝ) x
  -- ## (ii)  integrability of the lower-bound integrand
  have hTint : IntegrableOn
      (occIntegrand (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
        (Φ : Submission.BoseGases.X n → ℝ))
      (Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))) :=
    occChiIntegrand_integrable (M := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M)
      (ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (d := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) (u := u)
      (Φ := (Φ : Submission.BoseGases.X n → ℝ)) hℓ hΦc
  have hGint : IntegrableOn
      (lowIntegrand (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
        (μ * (Cf * _root_.BoseGases.a v)) (Φ : Submission.BoseGases.X n → ℝ))
      (Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))) := by
    refine (hTint.const_mul (-(μ * (Cf * _root_.BoseGases.a v)))).congr ?_
    filter_upwards with x
    simp only [lowIntegrand, occIntegrand]
    ring
  -- ## (iii)  the lower-bound integrand is `≤ 0`
  have hG0 : ∀ x : Submission.BoseGases.X n,
      lowIntegrand (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
        (μ * (Cf * _root_.BoseGases.a v)) (Φ : Submission.BoseGases.X n → ℝ) x ≤ 0 := by
    intro x
    have hS : 0 ≤ ∑ i : Fin n, Submission.BoseGases.chiSmallB
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u (x i) :=
      Finset.sum_nonneg fun i _ => hchiB (x i)
    have hμCf : 0 ≤ μ * (Cf * _root_.BoseGases.a v) :=
      mul_nonneg (le_of_lt hμ) (mul_nonneg hCf (le_of_lt hav))
    have hc : -(μ * (Cf * _root_.BoseGases.a v)) ≤ 0 := by linarith
    have hsq : 0 ≤ (Φ x) ^ 2 := sq_nonneg _
    have h1 : 0 ≤ (Φ x) ^ 2 * ∑ i : Fin n, Submission.BoseGases.chiSmallB
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u (x i) := mul_nonneg hsq hS
    have hmain : -(μ * (Cf * _root_.BoseGases.a v))
        * ((Φ x) ^ 2 * ∑ i : Fin n, Submission.BoseGases.chiSmallB
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u (x i)) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hc h1
    calc lowIntegrand (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
          (μ * (Cf * _root_.BoseGases.a v)) (Φ : Submission.BoseGases.X n → ℝ) x
        = -(μ * (Cf * _root_.BoseGases.a v))
          * ((Φ x) ^ 2 * ∑ i : Fin n, Submission.BoseGases.chiSmallB
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u (x i)) := by
          rw [lowIntegrand]
          ring
      _ ≤ 0 := hmain
  -- ## (iv)  the integral comparison
  have hmono : ∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
        lowIntegrand (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
          (μ * (Cf * _root_.BoseGases.a v)) (Φ : Submission.BoseGases.X n → ℝ) x
      ≤ ∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
          sbPotIntegrand h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u μ
            (Φ : Submission.BoseGases.X n → ℝ) x :=
    integral_le_integral_of_le_of_nonpos hpoint hGint hG0
  -- ## (v)  the value of the lower-bound integral
  have hGeq : ∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
        lowIntegrand (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
          (μ * (Cf * _root_.BoseGases.a v)) (Φ : Submission.BoseGases.X n → ℝ) x
      = -(μ * (Cf * _root_.BoseGases.a v))
        * Work.BoseFixR.occChi (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
            (Φ : Submission.BoseGases.X n → ℝ) := by
    rw [occChi_eq_integral]
    rw [show lowIntegrand (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
            (μ * (Cf * _root_.BoseGases.a v)) (Φ : Submission.BoseGases.X n → ℝ)
          = fun x => (-(μ * (Cf * _root_.BoseGases.a v))) *
              occIntegrand (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
                (Φ : Submission.BoseGases.X n → ℝ) x from by
      funext x
      simp only [lowIntegrand, occIntegrand]
      ring]
    rw [integral_const_mul]
  -- ## (vi)  the potential word dominates the lower-bound integral
  have hqle : -(μ * (Cf * _root_.BoseGases.a v))
        * Work.BoseFixR.occChi (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
            (Φ : Submission.BoseGases.X n → ℝ)
      ≤ Work.SmallBoxSliding.qLHSwordB h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ u
          (Φ : Submission.BoseGases.X n → ℝ) := by
    rw [qLHSwordB_eq_integral]
    rw [← hGeq]
    exact hmono
  -- ## (vii)  the occupancy hypothesis
  have hocc' : Work.BoseFixR.occChi (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
        (Φ : Submission.BoseGases.X n → ℝ)
      ≤ K * (μ * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u + 1)
        * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) := by
    rw [crudeThreshold] at hocc
    exact hocc
  -- ## (viii)  the kinetic part is nonnegative
  have hkin : 0 ≤ Work.BoseFixB1.sbKin (v := v) μ
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M u
      (Φ : Submission.BoseGases.X n → ℝ) := by
    rw [Work.BoseFixB1.sbKin]
    exact Work.UBBInputs9.A.tBwordBInd_nonneg hℓ heT u _
  -- ## (ix)  the arithmetic
  have hsign : -(μ * (Cf * _root_.BoseGases.a v)) ≤ 0 := by
    have h0 : 0 ≤ μ * (Cf * _root_.BoseGases.a v) :=
      mul_nonneg (le_of_lt hμ) (mul_nonneg hCf (le_of_lt hav))
    linarith
  have hmul1 : -(μ * (Cf * _root_.BoseGases.a v))
        * (K * (μ * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u + 1)
          * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ))
      ≤ -(μ * (Cf * _root_.BoseGases.a v))
        * Work.BoseFixR.occChi (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
            (Φ : Submission.BoseGases.X n → ℝ) :=
    mul_le_mul_of_nonpos_left hocc' hsign
  have harith : -(μ * (Cf * _root_.BoseGases.a v))
        * (K * (μ * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u + 1)
          * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ))
      = -((Cf * K) * (μ ^ 2 * _root_.BoseGases.a v
              * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                  (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
            + μ * _root_.BoseGases.a v))
          * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) := by
    ring
  -- ## assembly
  calc -((Cf * K) * (μ ^ 2 * _root_.BoseGases.a v
            * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
          + μ * _root_.BoseGases.a v))
        * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
      = -(μ * (Cf * _root_.BoseGases.a v))
          * (K * (μ * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u + 1)
            * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)) :=
        harith.symm
    _ ≤ -(μ * (Cf * _root_.BoseGases.a v))
          * Work.BoseFixR.occChi (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
              (Φ : Submission.BoseGases.X n → ℝ) := hmul1
    _ ≤ Work.SmallBoxSliding.qLHSwordB h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ u
          (Φ : Submission.BoseGases.X n → ℝ) := hqle
    _ = Work.BoseFixB1.sbPot h μ u (Φ : Submission.BoseGases.X n → ℝ) := rfl
    _ ≤ Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ) := by
        rw [Work.BoseFixB1.sbWord]
        linarith [hkin]

end Work.BoseFixR
