import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.SliceBadAux
import Submission.Work.BoseBoxFock.SlotProjAux
import Submission.Work.BoseBoxFock.boxRealise_regular
import Submission.Work.BoseBoxFock.integral_mode_acube
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.slotProj1_aPC_absorb_self`

The box mean `aPC ℓ i Ψ` of a state is *constant in the slot `i`* (it averages that slot over
the box), and the single-slot projection `slotProj1 e i` projects the slot `i` onto the span of
the modes `e l`.  Since the condensate mode `e 0 = c·θ_Λ` is (a multiple of) the box indicator,
the slot mean already lives in that span, so projecting the slot leaves it alone *on the box*:

    `slotProj1 e i (aPC ℓ i Ψ) =ᵐ[volume.restrict (abox N ℓ)] aPC ℓ i Ψ`.

The mathematical content is the resolution of the identity at a point:

  `∫ w, PV e a w = Σ_l e l a · ∫ w, star (e l w)`
  `             = e 0 a · star (c·ℓ³)  = 1`   for `a ∈ ℓ•cell = acube ℓ`,

because `∫ w, e l w = δ_{l0}·c·ℓ³` (`integral_mode_acube`, from the orthonormality and the
pinning `e 0 = c·θ_Λ`) and `c·star c = ℓ⁻³`.

**Repair note.**  The `hc` hypothesis as originally transcribed read
`∂(MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)) |> MeasureTheory.volume)`, which is a
type error (`volume` is a measure, not a function of a measure).  It has been written in the
form used by the sibling `aPC_slotProj1_absorb_self` (the same hypothesis, the same meaning):
`∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))`.  Nothing else in
the statement changed.
-/

namespace Work.BoseBoxFock

open MeasureTheory

noncomputable section

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "Sp" => EuclideanSpace ℝ (Fin 3)

/-- An `L^∞` function whose support lies in the box `Λ(ℓ) = corpusBox.boxL ℓ` (a compact set of
finite volume) is integrable. -/
private lemma integrable_of_memLp_top_of_support_subset {ℓ : ℝ} (hℓ : 0 < ℓ) {f : Sp → ℂ}
    (hf : MemLp f ⊤) (hfsupp : Function.support f ⊆ Work.BoseK15.corpusBox.boxL ℓ) :
    Integrable f := by
  obtain ⟨M, _hM0, hM⟩ := exists_ae_bound_of_memLp_top hf
  rw [← integrableOn_iff_integrable_of_support_subset hfsupp]
  refine IntegrableOn.of_bound ?_ (hf.aestronglyMeasurable.restrict (s := _)) M ?_
  · rw [Work.BoseB4.BoxData.volume_boxL _ hℓ]
    exact ENNReal.ofReal_lt_top
  · exact ae_mono Measure.restrict_le_self hM

theorem slotProj1_aPC_absorb_self (ℓ : ℝ) (hℓ : 0 < ℓ) {m : ℕ} [NeZero m]
    {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ}
    (he : ∀ l l', (∫ x : EuclideanSpace ℝ (Fin 3),
        (starRingEnd ℂ) (e l x) * e l' x) = if l = l' then (1 : ℂ) else 0)
    (hbdd : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (hc : ∃ c : ℂ, (starRingEnd ℂ) c * c = (ℓ ^ 3)⁻¹ ∧
      (∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))),
        e 0 x = c * Work.BoseK15.corpusBox.thetaFun ℓ x))
    {N : ℕ} (i : Fin N) {Ψ : (Fin N → EuclideanSpace ℝ (Fin 3)) → ℂ}
    (hΨ : MeasureTheory.MemLp Ψ ⊤) :
    (fun x => Work.BoseBoxFock.slotProj1 e i (Work.BoseBoxFock.aPC ℓ i Ψ) x)
      =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure
          (Fin N → EuclideanSpace ℝ (Fin 3))).restrict (Submission.BoseGases.abox N ℓ)]
      (fun x => Work.BoseBoxFock.aPC ℓ i Ψ x) := by
  classical
  obtain ⟨c, hcstar, hcae⟩ := hc
  have hKne : ((((ℓ ^ 3 : ℝ)) : ℂ)) ≠ 0 := by
    simp only [Ne, Complex.ofReal_eq_zero]
    exact pow_ne_zero 3 (ne_of_gt hℓ)
  -- the scalar identity `c·conj(c·ℓ³) = 1`
  have hnum : c * star (c * ((((ℓ ^ 3 : ℝ)) : ℂ))) = 1 := by
    have hK : star ((((ℓ ^ 3 : ℝ)) : ℂ)) = ((((ℓ ^ 3 : ℝ)) : ℂ)) := Complex.conj_ofReal _
    have hcs : c * star c = ((((ℓ ^ 3 : ℝ)) : ℂ))⁻¹ := by
      have h : (starRingEnd ℂ) c * c = ((((ℓ ^ 3 : ℝ)) : ℂ))⁻¹ := by
        simpa only [Complex.ofReal_pow, Complex.ofReal_inv] using hcstar
      rw [mul_comm]; exact h
    rw [star_mul, hK,
      show c * (((((ℓ ^ 3 : ℝ)) : ℂ)) * star c)
          = ((((ℓ ^ 3 : ℝ)) : ℂ)) * (c * star c) by ring,
      hcs]
    exact mul_inv_cancel₀ hKne
  -- ## integrability of the conjugates of the modes
  have hIntStar : ∀ l : Fin m, Integrable (fun w : Sp => star (e l w)) := fun l =>
    integrable_of_memLp_top_of_support_subset hℓ ((hbdd l).star) (fun w hw =>
      hsupp l (by
        simp only [Function.mem_support] at hw ⊢
        exact fun h0 => hw (by rw [h0, star_zero])))
  -- ## the conjugate moment of a mode
  have hJ : ∀ l : Fin m, (∫ w : Sp, star (e l w))
      = if l = 0 then star (c * ((((ℓ ^ 3 : ℝ)) : ℂ))) else 0 := by
    intro l
    have h1 : (∫ w : Sp, star (e l w)) = star (∫ w : Sp, e l w) := by
      have h := integral_conj (μ := (volume : Measure Sp)) (f := fun w : Sp => e l w)
      simpa using h
    have heq : (fun w : Sp => e l w)
        = (Submission.BoseGases.acube ℓ).indicator (fun w : Sp => e l w) := by
      funext w
      by_cases hw : w ∈ Submission.BoseGases.acube ℓ
      · rw [Set.indicator_of_mem hw]
      · rw [Set.indicator_of_notMem hw]
        by_contra hne
        exact hw (by
          rw [← corpusBox_boxL_eq_acube hℓ]
          exact hsupp l (Function.mem_support.mpr hne))
    have h2 : (∫ w : Sp, e l w) = if l = 0 then c * ((((ℓ ^ 3 : ℝ)) : ℂ)) else 0 := by
      rw [heq, MeasureTheory.integral_indicator (Submission.BoseGases.acube_measurable ℓ)]
      exact integral_mode_acube hℓ he hsupp hcae hcstar l
    rw [h1, h2]
    by_cases hl : l = 0 <;> simp [hl]
  -- ## the resolution of the identity
  have hPV : ∀ a : Sp, (∫ w : Sp, PV e a w)
      = e 0 a * star (c * ((((ℓ ^ 3 : ℝ)) : ℂ))) := by
    intro a
    have hfun : (fun w : Sp => PV e a w)
        = (fun w : Sp => ∑ l : Fin m, e l a * star (e l w)) := by
      funext w; rfl
    have hsum := MeasureTheory.integral_finsetSum (μ := (volume : Measure Sp))
      (s := (Finset.univ : Finset (Fin m)))
      (f := fun l : Fin m => fun w : Sp => e l a * star (e l w))
      (fun l _ => (hIntStar l).const_mul (e l a))
    rw [hfun, hsum]
    rw [Finset.sum_congr rfl
      (fun l _ => MeasureTheory.integral_const_mul (e l a) (fun w : Sp => star (e l w)))]
    simp only [hJ, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  -- ## the a.e. pinning on the box
  have h1 : ∀ᵐ x ∂(volume : Measure (Fin N → Sp)),
      e 0 (x i) = c * Work.BoseK15.corpusBox.thetaFun ℓ (x i) := by
    have hq := (Measure.quasiMeasurePreserving_eval
      (fun _ : Fin N => (volume : Measure Sp)) i).ae_eq hcae
    filter_upwards [hq] with x hx
    simpa only [Function.comp_apply] using hx
  have hE : ∀ᵐ x ∂((volume : Measure (Fin N → Sp)).restrict (Submission.BoseGases.abox N ℓ)),
      e 0 (x i) = c := by
    have h2 : ∀ᵐ x ∂((volume : Measure (Fin N → Sp)).restrict (Submission.BoseGases.abox N ℓ)),
        e 0 (x i) = c * Work.BoseK15.corpusBox.thetaFun ℓ (x i) :=
      MeasureTheory.ae_mono Measure.restrict_le_self h1
    filter_upwards [h2,
      self_mem_ae_restrict (Submission.BoseGases.abox_measurable N ℓ)] with x hx hmem
    have hmi : x i ∈ Submission.BoseGases.acube ℓ :=
      (Submission.BoseGases.mem_abox_iff N ℓ x).mp hmem i
    rw [hx, thetaFun_eq_indicator hℓ, Set.indicator_of_mem hmi, mul_one]
  -- ## the assembly
  filter_upwards [hE, self_mem_ae_restrict (Submission.BoseGases.abox_measurable N ℓ)]
    with x hx hmem
  have hconst : ∀ w : Sp, aPC ℓ i Ψ (Function.update x i w) = aPC ℓ i Ψ x := by
    intro w
    have hupd : (fun y : Sp => Ψ (Function.update (Function.update x i w) i y))
        = (fun y : Sp => Ψ (Function.update x i y)) := by
      funext y
      rw [Function.update_idem]
    simp only [aPC, hupd]
  calc slotProj1 e i (aPC ℓ i Ψ) x
      = ∫ w : Sp, PV e (x i) w * aPC ℓ i Ψ (Function.update x i w) := rfl
    _ = ∫ w : Sp, PV e (x i) w * aPC ℓ i Ψ x := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
        show PV e (x i) w * aPC ℓ i Ψ (Function.update x i w)
          = PV e (x i) w * aPC ℓ i Ψ x
        rw [hconst w]
    _ = (∫ w : Sp, PV e (x i) w) * aPC ℓ i Ψ x :=
        MeasureTheory.integral_mul_const _ _
    _ = (e 0 (x i) * star (c * ((((ℓ ^ 3 : ℝ)) : ℂ)))) * aPC ℓ i Ψ x := by rw [hPV]
    _ = aPC ℓ i Ψ x := by
        rw [hx, hnum, one_mul]

end

end Work.BoseBoxFock
