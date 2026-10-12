import Mathlib.Tactic.Have
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.UBBInputs8.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! Round 8, strand A — the FS-faithful kinetic clause at the constant state.

`Work.UBBInputs8.tBLocalisationInd N ℓ d b ε c Φ` is FS `lem:LocKinEn` / Bratteli–Solovej
Thm 3.10 in the corpus's word form, but with FS's own box projection
`Q_{B(u)} = 1_{B(u)} − P_{B(u)}` (`Work.UBBInputs8.tBwordBInd`, which carries the box
indicator).  At the constant state `Φ ≡ 1` all three terms vanish — `cnPlus ℓ (const 1) = 0`
(the mean-free projection of a constant over the box is `0`), `∫_u tBwordBInd u (const 1) = 0`
(identically in `u`: on a box of positive mass the two terms of FS's `Q_{B(u)}` cancel
pointwise, and on a degenerate (Lebesgue-null) box `Q_{B(u)}` reduces to the box indicator,
whose tube has measure zero and whose windowed amplitudes vanish a.e.) and
`kinWord N ℓ (const 1) = 0` (the derivatives vanish) — so the
inequality holds *for the mathematical integral*, not through the `integral_undef` convention.
This is the consistency check of the repaired clause at exactly the witness state that refutes
the round-7 bookkeeping and that makes the corpus's `tBwordB`-integrand non-integrable
(`Work.UBBInputs8.A.not_integrable_tBwordB_const`). -/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.UBBInputs8.A

open Submission.BoseGases
open Work.UBBInputs8
open Work.SmallBoxSliding
open Work.SmallBoxTBWord

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option linter.unusedVariables false

/-! ## 1  The two trivial terms at the constant state -/

/-- The mean-free projection of a constant over the centred box is `0`, hence the excited
count `n₊ = Σᵢ‖QᵢΦ‖²` vanishes at `Φ ≡ 1`. -/
private lemma cnPlus_const_one {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) :
    Submission.BoseGases.cnPlus ℓ (fun _ : X N => (1 : ℝ)) = 0 := by
  unfold Submission.BoseGases.cnPlus
  refine Finset.sum_eq_zero (fun i _ => ?_)
  have hzero : ∀ x : X N, aQ ℓ i (fun _ : X N => (1 : ℝ)) x = 0 := by
    intro x
    unfold aQ aP
    rw [integral_const_acube ℓ hℓ 1]
    field_simp
    ring
  have hfun : (fun x : X N => (aQ ℓ i (fun _ : X N => (1 : ℝ)) x) ^ 2)
      = fun _ => (0 : ℝ) := by
    funext x; rw [hzero x]; norm_num
  rw [hfun, integral_zero]

/-- The kinetic word `ΣᵢΣₖ∫(∂ᵢₖΦ)²` vanishes at `Φ ≡ 1`, whose derivatives are `0`. -/
private lemma kinWord_const_one (N : ℕ) (ℓ : ℝ) :
    Submission.BoseGases.kinWord N ℓ (fun _ : X N => (1 : ℝ)) = 0 := by
  unfold Submission.BoseGases.kinWord
  refine Finset.sum_eq_zero (fun i _ => ?_)
  refine Finset.sum_eq_zero (fun k _ => ?_)
  have hfun : (fun x : X N =>
        (fderiv ℝ (fun _ : X N => (1 : ℝ)) x (kcDir N i k)) ^ 2) = fun _ => (0 : ℝ) := by
    funext x
    rw [fderiv_const_apply]
    simp
  rw [hfun, integral_zero]

/-! ## 2  The box mass of the sliding box -/

/-- `∫_{B(u)} 1 = |B(u)|`: the corpus bookkeeping `boxMass` really is the volume of the
sliding box. -/
private lemma integral_one_dlBox {ℓ d : ℝ} (u : ℝ³) :
    (∫ z in dlBox ℓ d u, (1 : ℝ)) = boxMass ℓ d u := by
  have h := MeasureTheory.integral_indicator (μ := (volume : Measure ℝ³))
    (s := dlBox ℓ d u) (f := fun _ : ℝ³ => (1 : ℝ))
    (Work.SmallBoxSliding.measurableSet_dlBox ℓ d u)
  rw [← h]
  rfl

/-- A null sliding box: `boxMass = 0` forces `B(u)` to be Lebesgue-null. -/
private lemma volume_dlBox_eq_zero_of_boxMass_eq_zero {ℓ d : ℝ} (hℓ : 0 < ℓ) {u : ℝ³}
    (hV : boxMass ℓ d u = 0) :
    (volume : Measure ℝ³) (dlBox ℓ d u) = 0 := by
  have hreal : (volume : Measure ℝ³).real (dlBox ℓ d u) = 0 := by
    rw [← Work.SmallBoxSliding.boxMass_eq_measureReal]
    exact hV
  rw [Measure.real_def] at hreal
  have htop : (volume : Measure ℝ³) (dlBox ℓ d u) ≠ ⊤ :=
    ne_of_lt (Work.SmallBoxSliding.volume_dlBox_lt_top hℓ d u)
  rcases (ENNReal.toReal_eq_zero_iff _).mp hreal with h | h
  · exact h
  · exact absurd h htop

/-! ## 3  FS's box projection `Q_B` at the constant state -/

/-- `Q_{B,i}` acting on the constant `1`, on a box of **nonzero** mass: the two terms of
`Q_{B} = 1_B − P_B` cancel pointwise. -/
private lemma boxQInd_const_eq_zero {N : ℕ} {ℓ d : ℝ} {u : ℝ³}
    (hV : boxMass ℓ d u ≠ 0) (i : Fin N) :
    boxQInd (boxMass ℓ d u) (dlBox ℓ d u) i (fun _ : X N => (1 : ℝ)) = 0 := by
  funext x
  show boxQInd (boxMass ℓ d u) (dlBox ℓ d u) i (fun _ : X N => (1 : ℝ)) x = (0 : ℝ)
  have hI : (∫ z in dlBox ℓ d u,
      (fun _ : X N => (1 : ℝ)) (Function.update x i z)) = boxMass ℓ d u :=
    integral_one_dlBox u
  simp only [boxQInd, boxPInd]
  rw [hI, one_div, inv_mul_cancel₀ hV]
  ring

/-- `Q_{B,i}` acting on the constant `1`, on a **null** box (where `1/|B| = 0`):
`Q_{B,i}` degenerates to the box indicator `1_{B(u)}`. -/
private lemma boxQInd_const_eq_indicator {N : ℕ} {ℓ d : ℝ} {u : ℝ³}
    (hV : boxMass ℓ d u = 0) (i : Fin N) :
    boxQInd (boxMass ℓ d u) (dlBox ℓ d u) i (fun _ : X N => (1 : ℝ))
      = fun y : X N => (dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (y i) := by
  funext x
  show boxQInd (boxMass ℓ d u) (dlBox ℓ d u) i (fun _ : X N => (1 : ℝ)) x
      = (dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x i)
  have hI : (∫ z in dlBox ℓ d u,
      (fun _ : X N => (1 : ℝ)) (Function.update x i z)) = boxMass ℓ d u :=
    integral_one_dlBox u
  simp only [boxQInd, boxPInd]
  rw [hI, hV]
  simp

/-! ## 4  The tube of a null box is null -/

/-- The `i`-th tube over a null box has zero measure: for `A ⊆ acube ℓ` of measure `0`,
`∫_{abox N ℓ} 1_A(xᵢ) = 0`.  Peeling the `i`-th coordinate off the box (`abox_peel_mp` in
its `kcInsN`-form) turns the tube into the product `A × univ`. -/
private lemma integral_indicator_slot_eq_zero {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {A : Set ℝ³}
    (hAmeas : MeasurableSet A) (hAac : A ⊆ acube ℓ)
    (hA0 : (volume : Measure ℝ³) A = 0) (i : Fin N) :
    (∫ x in abox N ℓ, A.indicator (fun _ => (1 : ℝ)) (x i)) = 0 := by
  cases N with
  | zero => exact i.elim0
  | succ n =>
    have hmp2 : MeasurePreserving (⇑(kcInsN n i))
        (((volume : Measure ℝ³).restrict (acube ℓ)).prod
          ((volume : Measure (X n)).restrict (abox n ℓ)))
        ((volume : Measure (X (n + 1))).restrict (abox (n + 1) ℓ)) := by
      have h := MeasurePreserving.symm
        (e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ³) i))
        (abox_peel_mp (n := n) (ℓ := ℓ) i)
      simpa [kcInsN] using h
    have hSmeas : MeasurableSet ({x : X (n + 1) | x i ∈ A}) :=
      hAmeas.preimage (measurable_pi_apply i)
    have hpre : ⇑(kcInsN n i) ⁻¹' ({x : X (n + 1) | x i ∈ A})
        = A ×ˢ (Set.univ : Set (X n)) := by
      ext p
      obtain ⟨y, r⟩ := p
      simp [kc_insN_apply_same]
    have hSA : ((volume : Measure (X (n + 1))).restrict (abox (n + 1) ℓ))
        {x : X (n + 1) | x i ∈ A} = 0 := by
      rw [← hmp2.map_eq, Measure.map_apply hmp2.measurable hSmeas, hpre]
      rw [Measure.prod_prod]
      have hA' : ((volume : Measure ℝ³).restrict (acube ℓ)) A = 0 := by
        rw [Measure.restrict_apply hAmeas, Set.inter_eq_left.mpr hAac, hA0]
      rw [hA', zero_mul]
    have hae : ∀ᵐ x ∂((volume : Measure (X (n + 1))).restrict (abox (n + 1) ℓ)),
        A.indicator (fun _ => (1 : ℝ)) (x i) = 0 := by
      rw [MeasureTheory.ae_iff]
      have hset : {x : X (n + 1) | ¬ (A.indicator (fun _ => (1 : ℝ)) (x i) = 0)}
          = {x : X (n + 1) | x i ∈ A} := by
        ext x
        by_cases hx : x i ∈ A
        · simp [Set.indicator_of_mem hx]
        · simp [Set.indicator_of_notMem hx]
      rw [hset]
      exact hSA
    rw [integral_congr_ae hae]
    simp

/-! ## 5  The spectral amplitudes at the constant state -/

/-- Every `p`-mode amplitude of `Q_{B,i}(const 1)` vanishes.  On a box of nonzero mass
`Q_{B,i}(const 1) = 0`; on a null box it is the box indicator, seen against the null box. -/
private lemma tBamp_const_eq_zero {N : ℕ} {ℓ d : ℝ} (hℓ : 0 < ℓ) {u : ℝ³} (i : Fin N)
    (p : ℝ³) (x : X N) :
    tBamp (chiB ℓ d u) p
      (boxQInd (boxMass ℓ d u) (dlBox ℓ d u) i (fun _ : X N => (1 : ℝ))) i x = 0 := by
  by_cases hV : boxMass ℓ d u = 0
  · rw [boxQInd_const_eq_indicator hV i, tBamp]
    have hA0 : (volume : Measure ℝ³) (dlBox ℓ d u) = 0 :=
      volume_dlBox_eq_zero_of_boxMass_eq_zero hℓ hV
    have hae : ∀ᵐ z ∂(volume : Measure ℝ³),
        (chiB ℓ d u z : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
          ((((fun y : X N => (dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (y i))
              (Function.update x i z)) : ℝ) : ℂ) = 0 := by
      filter_upwards [indicator_meas_zero (s := dlBox ℓ d u)
        (f := fun _ : ℝ³ => (1 : ℝ)) hA0] with z hz
      have hz' : (dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) z = 0 := by simpa using hz
      simp [Function.update_self, hz']
    rw [integral_congr_ae hae]
    simp
  · rw [boxQInd_const_eq_zero hV i, tBamp]
    simp

/-- A `p`-amplitude that vanishes pointwise contributes nothing to the `p`-diagonal form. -/
private lemma integral_normSq_tBamp_eq_zero {N : ℕ} {ℓ d : ℝ} {u p : ℝ³} (i : Fin N)
    {ψ : X N → ℝ} (hψ : ∀ x, tBamp (chiB ℓ d u) p ψ i x = 0) :
    (∫ x in abox N ℓ, ‖tBamp (chiB ℓ d u) p ψ i x‖ ^ 2) = 0 := by
  have hf : (fun x : X N => ‖tBamp (chiB ℓ d u) p ψ i x‖ ^ 2) = fun _ => (0 : ℝ) := by
    funext x; rw [hψ x]; simp
  rw [hf, integral_zero]

/-! ## 6  The box word at the constant state -/

private theorem tBwordBInd_const_zero_aux {N : ℕ} {ℓ d ε c : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u : ℝ³) :
    Work.UBBInputs8.tBwordBInd N ℓ d ε c u (fun _ : X N => (1 : ℝ)) = 0 := by
  have hkin : Work.UBBInputs8.tBwordKinInd ℓ (dlBox ℓ d u) (boxMass ℓ d u) (chiB ℓ d u) c
      (fun _ : X N => (1 : ℝ)) = 0 := by
    unfold Work.UBBInputs8.tBwordKinInd Work.UBBInputs8.tBdiagFormInd
    refine Finset.sum_eq_zero (fun i _ => ?_)
    have hz2 : (∫ p : ℝ³, fsKinCoeff c ‖p‖ * ((ℓ ^ 3)⁻¹ *
        ∫ x in abox N ℓ,
          ‖tBamp (chiB ℓ d u) p
            (boxQInd (boxMass ℓ d u) (dlBox ℓ d u) i (fun _ : X N => (1 : ℝ))) i x‖ ^ 2)) = 0 := by
      have hz : (fun p : ℝ³ => fsKinCoeff c ‖p‖ * ((ℓ ^ 3)⁻¹ *
          ∫ x in abox N ℓ,
            ‖tBamp (chiB ℓ d u) p
              (boxQInd (boxMass ℓ d u) (dlBox ℓ d u) i (fun _ : X N => (1 : ℝ))) i x‖ ^ 2))
          = fun _ => (0 : ℝ) := by
        funext p
        have h1 : (∫ x in abox N ℓ,
              ‖tBamp (chiB ℓ d u) p
                (boxQInd (boxMass ℓ d u) (dlBox ℓ d u) i (fun _ : X N => (1 : ℝ))) i x‖ ^ 2) = 0 :=
          integral_normSq_tBamp_eq_zero i (fun x => tBamp_const_eq_zero hℓ i p x)
        rw [h1, mul_zero, mul_zero]
      rw [hz, integral_zero]
    rw [hz2, mul_zero]
  have hcn : Work.UBBInputs8.cnPlusBoxInd ℓ (dlBox ℓ d u) (boxMass ℓ d u)
      (fun _ : X N => (1 : ℝ)) = 0 := by
    unfold Work.UBBInputs8.cnPlusBoxInd
    by_cases hV : boxMass ℓ d u = 0
    · refine Finset.sum_eq_zero (fun i _ => ?_)
      have h1 : ∀ x : X N,
          boxQInd (boxMass ℓ d u) (dlBox ℓ d u) i (fun _ : X N => (1 : ℝ)) x
            = (dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x i) :=
        fun x => congrFun (boxQInd_const_eq_indicator hV i) x
      have hf : (fun x : X N =>
            (boxQInd (boxMass ℓ d u) (dlBox ℓ d u) i (fun _ : X N => (1 : ℝ)) x) ^ 2)
          = fun x : X N => (dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x i) := by
        funext x
        rw [h1 x]
        by_cases hx : x i ∈ dlBox ℓ d u
        · rw [Set.indicator_of_mem hx]; norm_num
        · rw [Set.indicator_of_notMem hx]; norm_num
      rw [hf, integral_indicator_slot_eq_zero hℓ
        (Work.SmallBoxSliding.measurableSet_dlBox ℓ d u)
        (Work.SmallBoxSliding.dlBox_subset_acube ℓ d u)
        (volume_dlBox_eq_zero_of_boxMass_eq_zero hℓ hV) i]
    · refine Finset.sum_eq_zero (fun i _ => ?_)
      have h1 : ∀ x : X N,
          boxQInd (boxMass ℓ d u) (dlBox ℓ d u) i (fun _ : X N => (1 : ℝ)) x = 0 :=
        fun x => congrFun (boxQInd_const_eq_zero hV i) x
      have hf : (fun x : X N =>
            (boxQInd (boxMass ℓ d u) (dlBox ℓ d u) i (fun _ : X N => (1 : ℝ)) x) ^ 2)
          = fun _ => (0 : ℝ) := by
        funext x; rw [h1 x]; norm_num
      rw [hf, integral_zero]
  unfold Work.UBBInputs8.tBwordBInd Work.UBBInputs8.tBwordInd
  rw [hcn, hkin]
  ring

/-! ## 7  The clause at the constant state -/

theorem tBLocalisationInd_const {N : ℕ} {ℓ d b ε c : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) :
    Work.UBBInputs8.tBLocalisationInd N ℓ d b ε c
      (fun _ : Submission.BoseGases.X N => (1 : ℝ)) := by
  unfold Work.UBBInputs8.tBLocalisationInd
  rw [cnPlus_const_one (N := N) hℓ, kinWord_const_one N ℓ]
  have hf : (fun u : ℝ³ =>
      Work.UBBInputs8.tBwordBInd N ℓ d ε c u
        (fun _ : Submission.BoseGases.X N => (1 : ℝ))) = fun _ => 0 := by
    funext u
    exact tBwordBInd_const_zero_aux hℓ hd u
  rw [hf, integral_zero]
  simp

end Work.UBBInputs8.A
