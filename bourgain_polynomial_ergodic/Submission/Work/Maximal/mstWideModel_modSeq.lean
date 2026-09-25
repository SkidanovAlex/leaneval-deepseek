import Mathlib
import Submission.Work.Maximal.mstWide_defs
import Submission.Work.BourgainPlan.Maximal.mstModelFn_modSeq

namespace Work.Maximal

open MeasureTheory Finset
open scoped BigOperators ENNReal

open Work.BourgainPlan.IonescuWainger
open Work.BourgainPlan.Maximal (mstModelFn mstModelFn_apply mstProf mstModSeq mstModSeq_apply mstArc_apply memℒp_mstModSeq)

noncomputable section

local notation "Circ" => Work.BourgainPlan.IonescuWainger.Circle
local notation "haarT" => (AddCircle.haarAddCircle (T := 1))

/-- The `toLp` representative of an `L^∞`-class has the same Fourier coefficients as the
underlying function. -/
private lemma toLp_mul_fourier_integral_wide {F : Circ → ℂ} (hF : MemLp F ⊤ haarT) (m : ℤ) :
    ∫ ξ : Circ, (hF.toLp F : Circ → ℂ) ξ * star (fourier m ξ) ∂haarT
      = ∫ ξ : Circ, F ξ * star (fourier m ξ) ∂haarT := by
  refine integral_congr_ae ?_
  filter_upwards [hF.coeFn_toLp] with ξ hξ
  rw [hξ]

/-- **The Fourier coefficient of the weighted arc symbol**: for the symbol
`Σ_{β∈E} G β · φ(· − β)` the `m`-th coefficient is the weight `Σ_{β∈E} G β · star (fourier m β)`
times the `m`-th coefficient of `φ`.  (Translation invariance of the Haar measure together with
`fourierCoeff_arcTranslate`.) -/
private lemma integral_mstModelFn_mul_fourier_wide {Φ ψ : Circ → ℂ}
    (hφ : MemLp (fun y : Circ => Φ y * ψ y) ⊤ haarT)
    (G : Circ → ℂ) (E : Finset Circ) (m : ℤ) :
    ∫ ξ : Circ, mstModelFn G Φ ψ E ξ * star (fourier m ξ) ∂haarT
      = (∑ β ∈ E, G β * star (fourier m β))
          * (∫ ξ : Circ, (Φ ξ * ψ ξ) * star (fourier m ξ) ∂haarT) := by
  have hchar : MemLp (fun ξ : Circ => star (fourier m ξ)) ⊤ haarT :=
    memLp_top_of_bound ((continuous_star.comp (map_continuous (fourier m))).aestronglyMeasurable) 1
      (Filter.Eventually.of_forall fun ξ => by rw [norm_star, norm_fourier_apply'])
  have hInt : ∀ β ∈ E, Integrable (fun ξ : Circ =>
      G β * (arcTranslate β (fun y : Circ => Φ y * ψ y) ξ * star (fourier m ξ))) haarT := by
    intro β _
    have h1 : MemLp (arcTranslate β (fun y : Circ => Φ y * ψ y)) ⊤ haarT := memLp_arcTranslate hφ β
    have haesm : AEStronglyMeasurable
        (fun ξ : Circ => arcTranslate β (fun y : Circ => Φ y * ψ y) ξ * star (fourier m ξ)) haarT :=
      h1.aestronglyMeasurable.mul hchar.aestronglyMeasurable
    have hle : ∀ᵐ ξ ∂haarT,
        ‖arcTranslate β (fun y : Circ => Φ y * ψ y) ξ * star (fourier m ξ)‖
          ≤ ‖arcTranslate β (fun y : Circ => Φ y * ψ y) ξ‖ :=
      Filter.Eventually.of_forall fun ξ => by rw [norm_mul, norm_star, norm_fourier_apply', mul_one]
    exact ((h1.of_le haesm hle).const_mul (G β)).integrable le_top
  have hpt : ∀ ξ : Circ, mstModelFn G Φ ψ E ξ * star (fourier m ξ)
      = ∑ β ∈ E, G β * (arcTranslate β (fun y : Circ => Φ y * ψ y) ξ * star (fourier m ξ)) := by
    intro ξ
    rw [mstModelFn_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun β _ => ?_
    simp only [arcTranslate_apply]
    ring
  rw [show (fun ξ : Circ => mstModelFn G Φ ψ E ξ * star (fourier m ξ))
      = (fun ξ : Circ => ∑ β ∈ E,
          G β * (arcTranslate β (fun y : Circ => Φ y * ψ y) ξ * star (fourier m ξ)))
      from funext hpt,
    integral_finsetSum E hInt, Finset.sum_mul]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [integral_const_mul, fourierCoeff_arcTranslate (fun y : Circ => Φ y * ψ y) hφ β m]
  ring

/-- **MST's reduction of the wide level model to a single multiplier** (the wide-bump analogue of
`mstModelFn_modSeq`): the weighted arc-sum operator with symbol
`Σ_{β ∈ 𝒰(s+1)∖𝒰(s)} G β · (Φ_{2^n} ϱ_s)(·−β)` (the wide level model with weights `G`) evaluated at
`y` equals the *single* (arc-free) multiplier with symbol `Φ_{2^n} ϱ_s` applied to the modulated
input `mstModSeq G E f y`, `E = mstAnnulus l s`.  The proof is a verbatim adaptation of
`mstModelFn_modSeq` (the bump and the finset are arbitrary there). -/
theorem mstWideModel_modSeq (P : Polynomial ℤ) (l : ℕ) (χ : ℝ) (η : ℝ → ℂ) (n s : ℕ)
    (G : Work.BourgainPlan.IonescuWainger.Circle → ℂ) (f : ℤ → ℂ) (hf : Memℓp f 2)
    (hA : MeasureTheory.MemLp (Work.BourgainPlan.Maximal.mstModelFn G
      (Work.BourgainPlan.Maximal.mstProf P (2 ^ n)) (Work.Maximal.mstWideBump P χ η s)
      (Work.Maximal.mstAnnulus l s)) ⊤ (AddCircle.haarAddCircle (T := 1)))
    (hB : MeasureTheory.MemLp (fun ξ : Work.BourgainPlan.IonescuWainger.Circle =>
      Work.BourgainPlan.Maximal.mstProf P (2 ^ n) ξ * Work.Maximal.mstWideBump P χ η s ξ) ⊤
      (AddCircle.haarAddCircle (T := 1)))
    (y : ℤ) :
    Work.BourgainPlan.IonescuWainger.opMul (MeasureTheory.MemLp.toLp
        (Work.BourgainPlan.Maximal.mstModelFn G (Work.BourgainPlan.Maximal.mstProf P (2 ^ n))
          (Work.Maximal.mstWideBump P χ η s) (Work.Maximal.mstAnnulus l s)) hA) f hf y
      = Work.BourgainPlan.IonescuWainger.opMul (MeasureTheory.MemLp.toLp
          (fun ξ : Work.BourgainPlan.IonescuWainger.Circle =>
            Work.BourgainPlan.Maximal.mstProf P (2 ^ n) ξ * Work.Maximal.mstWideBump P χ η s ξ) hB)
          (Work.BourgainPlan.Maximal.mstModSeq G (Work.Maximal.mstAnnulus l s) f y)
          (Work.BourgainPlan.Maximal.memℒp_mstModSeq hf y) y := by
  classical
  have hmemB : MemLp (fun ξ : Circ => mstProf P (2 ^ n) ξ * mstWideBump P χ η s ξ) ⊤ haarT := hB
  have hkerA : ∀ m : ℤ,
      ∫ ξ : Circ, (MemLp.toLp (mstModelFn G (mstProf P (2 ^ n)) (mstWideBump P χ η s)
          (mstAnnulus l s)) hA : Circ → ℂ) ξ * star (fourier m ξ) ∂haarT
        = (∑ β ∈ mstAnnulus l s, G β * star (fourier m β))
            * (∫ ξ : Circ, (mstProf P (2 ^ n) ξ * mstWideBump P χ η s ξ) * star (fourier m ξ)
                ∂haarT) := by
    intro m
    rw [toLp_mul_fourier_integral_wide hA m,
      integral_mstModelFn_mul_fourier_wide (Φ := mstProf P (2 ^ n)) (ψ := mstWideBump P χ η s)
        hmemB G (mstAnnulus l s) m]
  rw [opMul_eq_tsum_kernel
        (MemLp.toLp (mstModelFn G (mstProf P (2 ^ n)) (mstWideBump P χ η s)
          (mstAnnulus l s)) hA) f hf hkerA y,
      opMul_eq_tsum_kernel
        (MemLp.toLp (fun ξ : Circ => mstProf P (2 ^ n) ξ * mstWideBump P χ η s ξ) hB)
        (mstModSeq G (mstAnnulus l s) f y) (memℒp_mstModSeq hf y)
        (fun m => toLp_mul_fourier_integral_wide hB m) y]
  refine tsum_congr fun k => ?_
  have hβ : ∀ β : Circ, star (fourier (y - k) β) = fourier (k - y) β := by
    intro β
    rw [show star (fourier (y - k) β) = fourier (-(y - k)) β from
      (fourier_neg (n := y - k) (x := β)).symm]
    congr 1
    ring
  have hsumeq : (∑ β ∈ mstAnnulus l s, G β * star (fourier (y - k) β))
      = (∑ β ∈ mstAnnulus l s, G β * fourier (k - y) β) :=
    Finset.sum_congr rfl fun β _ => by rw [hβ β]
  rw [mstModSeq_apply, mstArc_apply, hsumeq]
  ring

end

end Work.Maximal
