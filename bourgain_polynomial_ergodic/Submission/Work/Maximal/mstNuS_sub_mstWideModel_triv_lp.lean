import Mathlib
import Submission.Work.Maximal.mstWide_defs
import Submission.Work.Maximal.mstWideAux
import Submission.Work.Maximal.mst_lrs_base
import Submission.Work.Maximal.arcSymbolW_lp_bound_of_coeff
import Submission.Work.BourgainPlan.Maximal.major_arc_model
import Submission.Work.BourgainPlan.Maximal.memLp_mst_classes
import Submission.Work.BourgainPlan.Maximal.mst_major_defs

namespace Work.Maximal

open MeasureTheory Finset
open scoped BigOperators ENNReal

set_option autoImplicit false
set_option maxHeartbeats 1000000

local notation "Circle" => Work.BourgainPlan.IonescuWainger.Circle
local notation "haar" => (AddCircle.haarAddCircle (T := 1))

noncomputable section

/-- For `s ≥ 1` the annulus `𝒰(s+1) ∖ 𝒰(s)` (with the `mstLevel` convention) is the difference of
the level sets `mstU` used by the arc separation and Gauss-sum hypotheses. -/
private lemma mstAnnulus_eq_mstU_sdiff' (l s : ℕ) (hs : 1 ≤ s) :
    mstAnnulus l s = Work.BourgainPlan.Maximal.mstU l (s + 1) \
      Work.BourgainPlan.Maximal.mstU l s := by
  show Work.BourgainPlan.Maximal.mstLevel l (s + 1) \
      Work.BourgainPlan.Maximal.mstLevel l s = _
  rw [Work.BourgainPlan.Maximal.mstLevel_succ]
  congr 1
  rw [Work.BourgainPlan.Maximal.mstLevel, if_neg (by omega : s ≠ 0)]

/-- **The `ℓᵖ` bound for the narrow-to-wide replacement, in the trivial regime.**  The difference
`ν^s_{2^k} - Ω^s_{2^k}` of the level-`s` model and the wide level model is, up to the identification
`mstNuS - mstWideModel = arcSymbolW (star ∘ G) (𝒰(s+1) ∖ 𝒰(s)) (star Φ_{2^k} (η_s - ϱ_s))`, a
weighted arc symbol whose Fourier-coefficient kernel has `ℓ¹`-mass at most `K` times the number of
arcs times `sup ‖G‖ ≤ D (s+1)^{-δl}`; Young's inequality in the form
`arcSymbolW_lp_bound_of_coeff` then gives the `ℓᵖ → ℓᵖ` bound `D K (s+1)^{-δl} ♯(annulus)` for every
`q ≥ 1`, uniformly in `k`. -/
theorem mstNuS_sub_mstWideModel_triv_lp (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree)
    (hc : 0 < P.leadingCoeff) (l : ℕ) (hl : 1 ≤ l) {χ : ℝ} (hχ0 : 0 < χ) (hχ1 : χ < 1 / 10)
    (η : ℝ → ℂ) (hηc : ContDiff ℝ 2 η) (hηsup : ∀ x : ℝ, 1 / 2 ≤ |x| → η x = 0)
    {δ : ℝ} (hδ : 0 < δ) (D : ℝ) (hD : 0 < D)
    (hGauss : ∀ (s : ℕ) (β : Work.BourgainPlan.IonescuWainger.Circle),
      β ∈ Work.BourgainPlan.Maximal.mstU l (s + 1) \ Work.BourgainPlan.Maximal.mstU l s →
      ‖Work.BourgainPlan.Maximal.mstG P β‖ ≤ D * ((s : ℝ) + 1) ^ (-(δ * l)))
    (hνsml : ∀ n s : ℕ, MeasureTheory.MemLp
      (Work.BourgainPlan.Maximal.mstNuS P l P.natDegree χ η n s) ⊤
      (AddCircle.haarAddCircle (T := 1)))
    (hΩml : ∀ k s : ℕ, MeasureTheory.MemLp
      (Work.Maximal.mstWideModel P l χ η k s) ⊤ (AddCircle.haarAddCircle (T := 1)))
    {K : ℝ} (hK : 0 < K)
    (hcoeff : ∀ k s : ℕ, Summable (fun m : ℤ => ‖∫ ξ : Work.BourgainPlan.IonescuWainger.Circle,
        (star (Work.BourgainPlan.Maximal.mstProf P (2 ^ k) ξ) *
          (Work.BourgainPlan.Maximal.mstEta P.natDegree χ η s ξ -
            Work.Maximal.mstWideBump P χ η s ξ)) * star (fourier m ξ)
        ∂(AddCircle.haarAddCircle (T := 1))‖)
      ∧ (∑' m : ℤ, ‖∫ ξ : Work.BourgainPlan.IonescuWainger.Circle,
        (star (Work.BourgainPlan.Maximal.mstProf P (2 ^ k) ξ) *
          (Work.BourgainPlan.Maximal.mstEta P.natDegree χ η s ξ -
            Work.Maximal.mstWideBump P χ η s ξ)) * star (fourier m ξ)
        ∂(AddCircle.haarAddCircle (T := 1))‖) ≤ K)
    {q : ℝ} (hq : 1 ≤ q) :
    ∃ A : ℝ, 0 < A ∧ ∀ s : ℕ, 1 ≤ s → ∀ k : ℕ, ∀ g : ℤ →₀ ℂ,
      MeasureTheory.eLpNorm (fun m : ℤ => ‖Work.BourgainPlan.IonescuWainger.opMul
          (Work.BourgainPlan.Maximal.mstNuSCls P l P.natDegree χ η k s (hνsml k s))
          (⇑g) (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g) m
        - Work.BourgainPlan.IonescuWainger.opMul
          ((hΩml k s).toLp (Work.Maximal.mstWideModel P l χ η k s))
          (⇑g) (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g) m‖ₑ)
        (ENNReal.ofReal q) MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (A * ((s : ℝ) + 1) ^ (-(δ * l))
          * ((Work.Maximal.mstAnnulus l s).card : ℝ))
        * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal q) MeasureTheory.Measure.count := by
  refine ⟨D * K, mul_pos hD hK, ?_⟩
  intro s hs k g
  have hAnn := mstAnnulus_eq_mstU_sdiff' l s hs
  -- ### the combined bump `φ = star Φ_{2^k} · (η_s - ϱ_s)` and the weight `w = star ∘ G`
  set φ : Circle → ℂ := fun ζ => star (Work.BourgainPlan.Maximal.mstProf P (2 ^ k) ζ) *
      (Work.BourgainPlan.Maximal.mstEta P.natDegree χ η s ζ - mstWideBump P χ η s ζ) with hφdef
  set w : Circle → ℂ := fun β => star (Work.BourgainPlan.Maximal.mstG P β) with hwdef
  have hEta_ml : MemLp (Work.BourgainPlan.Maximal.mstEta P.natDegree χ η s) ⊤ haar :=
    Work.BourgainPlan.Maximal.memLp_mstEta_of_continuous P P.natDegree χ η hηc.continuous s
  have hWide_ml : MemLp (mstWideBump P χ η s) ⊤ haar :=
    (mstWideBump_memLp_and_narrow P χ η hηc.continuous hηsup s).1
  have hProf_ml : MemLp (Work.BourgainPlan.Maximal.mstProf P (2 ^ k)) ⊤ haar :=
    Work.BourgainPlan.Maximal.memLp_mstProf_symbol P (2 ^ k)
  have hφml : MemLp φ ⊤ haar := by
    rw [hφdef]
    exact hProf_ml.star.mul (hEta_ml.sub hWide_ml)
  -- ### the two hypotheses on the symbol weight
  have hWnn : 0 ≤ D * ((s : ℝ) + 1) ^ (-(δ * l)) :=
    mul_nonneg hD.le (Real.rpow_nonneg (by positivity) _)
  have hw : ∀ β ∈ mstAnnulus l s, ‖w β‖ ≤ D * ((s : ℝ) + 1) ^ (-(δ * l)) := by
    intro β hβ
    rw [hwdef, norm_star]
    exact hGauss s β (by rw [← hAnn]; exact hβ)
  -- ### the coefficient hypotheses come from `hcoeff`
  have hcsum : Summable fun m : ℤ => ‖∫ ξ : Circle, φ ξ * star (fourier m ξ) ∂haar‖ := by
    simpa only [hφdef] using (hcoeff k s).1
  have hcK : (∑' m : ℤ, ‖∫ ξ : Circle, φ ξ * star (fourier m ξ) ∂haar‖) ≤ K := by
    simpa only [hφdef] using (hcoeff k s).2
  -- ### the difference of the two symbols is the weighted arc symbol with symbol `φ`
  have hLp : Work.BourgainPlan.Maximal.mstNuSCls P l P.natDegree χ η k s (hνsml k s)
      - (hΩml k s).toLp (mstWideModel P l χ η k s)
      = Work.BourgainPlan.Maximal.arcSymbolWLp (fun β : Circle => β) w (mstAnnulus l s) φ hφml := by
    refine Lp.ext ?_
    filter_upwards [Lp.coeFn_sub (Work.BourgainPlan.Maximal.mstNuSCls P l P.natDegree χ η k s
        (hνsml k s)) ((hΩml k s).toLp (mstWideModel P l χ η k s)),
      Work.BourgainPlan.Maximal.mstNuSCls_coeFn P l P.natDegree χ η k s (hνsml k s),
      MemLp.coeFn_toLp (hΩml k s),
      Work.BourgainPlan.Maximal.arcSymbolWLp_coeFn (fun β : Circle => β) w (mstAnnulus l s) φ
        hφml] with ξ hsub h1 h2 h3
    rw [hsub, Pi.sub_apply, h1, h2, h3]
    rw [Work.BourgainPlan.Maximal.mstNuS_apply, mstWideModel_apply,
      Work.BourgainPlan.Maximal.arcSymbolW_apply, hφdef, hwdef,
      show mstAnnulus l s = Work.BourgainPlan.Maximal.mstLevel l (s + 1) \
        Work.BourgainPlan.Maximal.mstLevel l s from rfl]
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun β _ => by ring)
  -- ### linearity of the multiplier in its symbol
  have hout : (fun m : ℤ => ‖Work.BourgainPlan.IonescuWainger.opMul
        (Work.BourgainPlan.Maximal.mstNuSCls P l P.natDegree χ η k s (hνsml k s))
        (⇑g) (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g) m
      - Work.BourgainPlan.IonescuWainger.opMul
        ((hΩml k s).toLp (mstWideModel P l χ η k s))
        (⇑g) (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g) m‖ₑ)
      = fun m : ℤ => ‖Work.BourgainPlan.IonescuWainger.opMul
        (Work.BourgainPlan.Maximal.arcSymbolWLp (fun β : Circle => β) w (mstAnnulus l s) φ hφml)
        (⇑g) (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g) m‖ₑ := by
    funext m
    rw [show Work.BourgainPlan.IonescuWainger.opMul
          (Work.BourgainPlan.Maximal.mstNuSCls P l P.natDegree χ η k s (hνsml k s))
          (⇑g) (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g) m
        - Work.BourgainPlan.IonescuWainger.opMul
          ((hΩml k s).toLp (mstWideModel P l χ η k s))
          (⇑g) (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g) m
        = Work.BourgainPlan.IonescuWainger.opMul
          (Work.BourgainPlan.Maximal.mstNuSCls P l P.natDegree χ η k s (hνsml k s)
            - (hΩml k s).toLp (mstWideModel P l χ η k s))
          (⇑g) (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g) m from by
        rw [← Pi.sub_apply, Work.BourgainPlan.IonescuWainger.opMul_sub],
      hLp]
  -- ### Young's inequality for the weighted arc symbol
  rw [hout, MeasureTheory.eLpNorm_enorm _ (measurable_of_countable _).aestronglyMeasurable]
  refine (Work.Maximal.arcSymbolW_lp_bound_of_coeff (p := q) hq (φ := φ) hφml
      (c := fun m : ℤ => ∫ ξ : Circle, φ ξ * star (fourier m ξ) ∂haar) hcsum (fun _ => rfl)
      (W := D * ((s : ℝ) + 1) ^ (-(δ * l))) (K := K) hWnn hcK w (mstAnnulus l s) hw g).trans ?_
  refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
  exact le_of_eq (by ring)

end

end Work.Maximal
