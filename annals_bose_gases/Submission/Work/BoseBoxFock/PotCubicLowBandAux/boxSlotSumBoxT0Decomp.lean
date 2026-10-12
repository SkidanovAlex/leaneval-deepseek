import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.PotCubicLowBandAux.atomPairG
import Submission.Work.BoseBoxFock.re_boxSlotSum_boxT0_le_cnPlusC
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PotCubicLowBandAux.boxSlotSumBoxT0Decomp`

**The pointwise decomposition of the excited-number slot sum.**  For measurable bounded modes
`e l` supported in the box `boxL ℓ`, the `0`-th mode proportional to the sharp box indicator
`θ_Λ = 1_{acube ℓ}` (`hc`), and a measurable bounded state `Θ` supported in the configuration box
`abox n ℓ`:

    `boxSlotSum e (boxT0 m) Θ =ᵃᵉ Σ_j slotProj1 e j Θ − Σ_j aPC ℓ j Θ`   on `abox n ℓ`,

i.e. the first-quantised slot sum of `boxT0 = 1 − |e₀⟩⟨e₀|` splits into the *total* slot
projection minus the *condensate* slot mean.

## Proof

Three steps, all at the weak (measurable + bounded) bundle:

1. `boxSlotSum e (boxT0 m) Θ = boxSlotSum e 1 Θ − Σ_j boxSlotOf e e₀ e₀ j Θ` pointwise — this is
   `Work.BoseBoxFock.boxSlotSum_boxT0` (linearity of `boxSlotSum` in the one-body operator, plus
   the rank-one piece `|e₀⟩⟨e₀|`).
2. `boxSlotSum e 1 Θ = fun x => Σ_j slotProj1 e j Θ x` pointwise — the *identity row*: the mode
   resolution of the identity `Σ_l |e_l⟩⟨e_l| = PV` in the slot kernel.  (`boxSlotSum_one_eq_sum_slotProj1`
   proves this for continuous compactly supported modes; here, at the weak bundle, the only input
   is the integrability of the fibre integrand `w ↦ star (e_l w) · Θ (x[j↦w])`, which follows from
   measurability + boundedness + the support of `e_l` in the (finite volume) box.)
3. `Σ_j boxSlotOf e e₀ e₀ j Θ = Σ_j aPC ℓ j Θ` a.e. on `abox n ℓ` — this is
   `Work.BoseBoxFock.boxSlotOf_evec_zero_eq_aPC` (the sharp indicator `θ_Λ` is fixed by complex
   conjugation and the mode is normalised by `(ℓ³)⁻¹`).

All steps are pointwise (or a.e.) with no symmetry, continuity or compact-support hypothesis on
the state, matching the weak bundle that the selection layer of the low-band chapter produces.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock.PotCubicLowBandAux

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-! ## 1. The fibre integrand is integrable at the weak bundle -/

/-- The insertion map `w ↦ x[j↦w]` is continuous. -/
private lemma continuous_update_const' {n : ℕ} (x : Work.BoseDict.Xn n) (j : Fin n) :
    Continuous (fun w : Work.BoseDict.Sp => Function.update x j w) :=
  (continuous_update (A := fun _ : Fin n => Work.BoseDict.Sp) j).comp
    (continuous_const.prodMk continuous_id)

/-- For a bounded measurable mode `e l` supported in the box `boxL ℓ` and a bounded measurable
state `Θ`, the fibre integrand `w ↦ star (e l w) · Θ(x[j↦w])` is integrable on the one-particle
space: it is measurable, bounded by `‖e l‖_∞ · ‖Θ‖_∞` and supported in the box `boxL ℓ` of finite
volume. -/
private theorem integrable_mode_state_bdd {m n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {e : Fin m → Work.BoseDict.Sp → ℂ} (hmeas : ∀ l, Measurable (e l))
    (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    {Θ : Work.BoseDict.Xn n → ℂ} (hΘm : Measurable Θ)
    (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C) (l : Fin m) (x : Work.BoseDict.Xn n) (j : Fin n) :
    Integrable (fun w : Work.BoseDict.Sp => star (e l w) * Θ (Function.update x j w)) := by
  classical
  obtain ⟨Cl, hCl⟩ := hbdd l
  obtain ⟨Ct, hCt⟩ := hΘb
  have hm : Measurable
      (fun w : Work.BoseDict.Sp => star (e l w) * Θ (Function.update x j w)) :=
    (continuous_star.measurable.comp (hmeas l)).mul
      (hΘm.comp (continuous_update_const' x j).measurable)
  have hsupp' : Function.support
      (fun w : Work.BoseDict.Sp => star (e l w) * Θ (Function.update x j w))
        ⊆ Work.BoseK15.corpusBox.boxL ℓ := by
    intro w hw
    have hne : star (e l w) * Θ (Function.update x j w) ≠ 0 := Function.mem_support.mp hw
    have he : e l w ≠ 0 := fun h0 => hne (by rw [h0, star_zero, zero_mul])
    exact hsupp l (Function.mem_support.mpr he)
  rw [← MeasureTheory.integrableOn_iff_integrable_of_support_subset hsupp']
  rw [Work.BoseBoxFock.boxL_eq_acube hℓ]
  refine MeasureTheory.IntegrableOn.of_bound (Submission.BoseGases.acube_lt_top ℓ hℓ.le)
    (hm.aestronglyMeasurable.restrict) (max Cl 0 * max Ct 0) ?_
  filter_upwards with w
  calc ‖star (e l w) * Θ (Function.update x j w)‖
      = ‖e l w‖ * ‖Θ (Function.update x j w)‖ := by rw [norm_mul, norm_star]
    _ ≤ max Cl 0 * max Ct 0 :=
        mul_le_mul (le_trans (hCl w) (le_max_left _ _)) (le_trans (hCt _) (le_max_left _ _))
          (norm_nonneg _) (le_max_right _ _)

/-! ## 2. The pointwise decomposition of `boxSlotSum e 1` at the weak bundle -/

/-- `η_{evec m l} = e l`: the superposition of the modes with the coordinate vector `evec m l`
is the single mode `e l`. -/
private lemma etaOf_evec' {m : ℕ} (e : Fin m → Work.BoseDict.Sp → ℂ) (l : Fin m) :
    Work.BoseDict.etaOf e (Work.BoseB4.evec m l) = e l := by
  funext z
  rw [Work.BoseDict.etaOf, Work.BoseB4.evec]
  rw [Finset.sum_eq_single l]
  · simp
  · intro b _ hb
    rw [Pi.single_eq_of_ne hb]
    simp
  · intro h
    exact absurd (Finset.mem_univ l) h

/-- The coordinate vector `evec m l'` read in the direction `l`: the Kronecker symbol. -/
private lemma coeff_one' {m : ℕ} (l l' : Fin m) :
    ((1 : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (Work.BoseB4.evec m l')) l
      = (if l = l' then (1 : ℝ) else 0) := by
  rw [Module.End.one_apply]
  simp [Work.BoseB4.evec, Pi.single_apply]

/-- The diagonal slot of `|e_l⟩⟨e_l|` is `e l (x j) · ∫_w star (e l w) · Θ (x[j↦w])`. -/
private lemma boxSlotOf_evec_self_apply' {m n : ℕ} (e : Fin m → Work.BoseDict.Sp → ℂ)
    (l : Fin m) (j : Fin n) (Θ : Work.BoseDict.Xn n → ℂ) (x : Work.BoseDict.Xn n) :
    Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l) j Θ x
      = e l (x j) * ∫ w : Work.BoseDict.Sp, star (e l w) * Θ (Function.update x j w) := by
  rw [Work.BoseDict.boxSlotOf, etaOf_evec' e l]
  simp only [starRingEnd_apply]

/-- Evaluation of `boxSlotSum` at a configuration, as a triple sum of slot values. -/
private lemma boxSlotSum_apply' {m n : ℕ} (e : Fin m → Work.BoseDict.Sp → ℂ)
    (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (Θ : Work.BoseDict.Xn n → ℂ)
    (x : Work.BoseDict.Xn n) :
    Work.BoseDict.boxSlotSum e T Θ x = ∑ j : Fin n, ∑ l : Fin m, ∑ l' : Fin m,
      (T (Work.BoseB4.evec m l') l : ℝ) •
        Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ x := by
  simp only [Work.BoseDict.boxSlotSum, Finset.sum_apply, Pi.smul_apply]

/-- **Left computation**: `boxSlotSum e 1 Φ x` is the double sum of the diagonal slot values. -/
private lemma boxSlotSum_one_apply' {m n : ℕ} (e : Fin m → Work.BoseDict.Sp → ℂ)
    (Θ : Work.BoseDict.Xn n → ℂ) (x : Work.BoseDict.Xn n) :
    Work.BoseDict.boxSlotSum e (1 : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) Θ x
      = ∑ j : Fin n, ∑ l : Fin m,
          e l (x j) * ∫ w : Work.BoseDict.Sp, star (e l w) * Θ (Function.update x j w) := by
  rw [boxSlotSum_apply']
  simp only [coeff_one']
  refine Finset.sum_congr rfl (fun j _ => ?_)
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [Finset.sum_eq_single l]
  · rw [if_pos rfl, one_smul]
    exact boxSlotOf_evec_self_apply' e l j Θ x
  · intro b _ hb
    rw [if_neg (Ne.symm hb), zero_smul]
  · intro h
    exact absurd (Finset.mem_univ l) h

/-- **Right computation**: the single-slot projection resolves into the mode sum
`Σ_l e_l(x_j) · ∫_w star(e_l w) · Θ(x[j↦w])`. -/
private lemma slotProj1_eq_sum_int_bdd {m n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {e : Fin m → Work.BoseDict.Sp → ℂ} (hmeas : ∀ l, Measurable (e l))
    (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    {Θ : Work.BoseDict.Xn n → ℂ} (hΘm : Measurable Θ)
    (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C) (x : Work.BoseDict.Xn n) (j : Fin n) :
    slotProj1 e j Θ x
      = ∑ l : Fin m,
          e l (x j) * ∫ w : Work.BoseDict.Sp, star (e l w) * Θ (Function.update x j w) := by
  show (∫ w : Work.BoseDict.Sp, PV e (x j) w * Θ (Function.update x j w)) = _
  rw [show (fun w : Work.BoseDict.Sp => PV e (x j) w * Θ (Function.update x j w))
      = fun w : Work.BoseDict.Sp =>
          ∑ l : Fin m, (e l (x j) * star (e l w)) * Θ (Function.update x j w) from by
    funext w
    simp only [PV, Finset.sum_mul]]
  rw [MeasureTheory.integral_finsetSum]
  · refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [show (fun w : Work.BoseDict.Sp => (e l (x j) * star (e l w)) * Θ (Function.update x j w))
        = fun w : Work.BoseDict.Sp =>
            e l (x j) * (star (e l w) * Θ (Function.update x j w)) from
      funext fun w => by ring]
    rw [MeasureTheory.integral_const_mul]
  · intro l _
    simpa only [mul_assoc] using
      (integrable_mode_state_bdd hℓ hmeas hbdd hsupp hΘm hΘb l x j).const_mul (e l (x j))

/-- **The identity row at the weak bundle.**  For measurable bounded modes supported in the box
and a measurable bounded state, the first-quantised slot sum of the identity one-body operator is
the sum of the single-slot projections. -/
private theorem boxSlotSum_one_eq_sum_slotProj1_bdd {m n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {e : Fin m → Work.BoseDict.Sp → ℂ} (hmeas : ∀ l, Measurable (e l))
    (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    {Θ : Work.BoseDict.Xn n → ℂ} (hΘm : Measurable Θ) (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C) :
    Work.BoseDict.boxSlotSum e (1 : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) Θ
      = fun x => ∑ j : Fin n, slotProj1 e j Θ x := by
  funext x
  show Work.BoseDict.boxSlotSum e (1 : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) Θ x
      = ∑ j : Fin n, slotProj1 e j Θ x
  rw [boxSlotSum_one_apply' e Θ x]
  exact Finset.sum_congr rfl (fun j _ =>
    (slotProj1_eq_sum_int_bdd hℓ hmeas hbdd hsupp hΘm hΘb x j).symm)

/-! ## 3. The target -/

theorem boxSlotSumBoxT0Decomp {m n : ℕ} [NeZero m] {ℓ : ℝ} (hℓ : 0 < ℓ)
    {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (hMemLp : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (hc : ∃ c : ℂ, (starRingEnd ℂ) c * c = (ℓ ^ 3)⁻¹ ∧
      e 0 =ᵐ[MeasureTheory.volume] fun x => c * Work.BoseK15.corpusBox.thetaFun ℓ x)
    {Θ : Submission.BoseGases.X n → ℂ} (hΘm : Measurable Θ)
    (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C)
    (hΘsupp : Function.support Θ ⊆ Submission.BoseGases.abox n ℓ) :
    Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m) Θ
      =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
          (Submission.BoseGases.abox n ℓ)]
      fun x => (∑ j : Fin n, Work.BoseBoxFock.slotProj1 e j Θ x)
        - ∑ j : Fin n, Work.BoseBoxFock.aPC ℓ j Θ x := by
  classical
  -- ## 1. the identity row: `boxSlotSum e 1 Θ = Σ_j slotProj1 e j Θ` (pointwise)
  have hone : Work.BoseDict.boxSlotSum e (1 : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) Θ
      = fun x => ∑ j : Fin n, Work.BoseBoxFock.slotProj1 e j Θ x :=
    boxSlotSum_one_eq_sum_slotProj1_bdd (m := m) (n := n) hℓ hmeas hbdd hsupp hΘm hΘb
  -- ## 2. the pointwise split off the rank-one condensate slot
  have hsplit : ∀ x : Submission.BoseGases.X n,
      Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m) Θ x
        = (∑ j : Fin n, Work.BoseBoxFock.slotProj1 e j Θ x)
          - ∑ j : Fin n,
              Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m 0) (Work.BoseB4.evec m 0) j Θ x := by
    intro x
    have h1 := congrFun (Work.BoseBoxFock.boxSlotSum_boxT0 (m := m) (d := n) (e := e) Θ) x
    have h2 := congrFun hone x
    simp only [Pi.sub_apply, Finset.sum_apply] at h1 h2 ⊢
    rw [h1, h2]
  -- ## 3. the a.e. identification of the condensate slot with the complex slot mean
  have haeP : ∀ᵐ x ∂((MeasureTheory.volume : MeasureTheory.Measure
        (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ)),
      (∑ j : Fin n,
          Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m 0) (Work.BoseB4.evec m 0) j Θ x)
        = ∑ j : Fin n, Work.BoseBoxFock.aPC ℓ j Θ x := by
    have h := Filter.eventually_all.mpr (fun j : Fin n =>
      Work.BoseBoxFock.boxSlotOf_evec_zero_eq_aPC (m := m) (d := n) hℓ hMemLp hsupp hc Θ
        hΘsupp j)
    filter_upwards [h] with x hx
    exact Finset.sum_congr rfl (fun j _ => hx j)
  -- ## 4. assembly
  filter_upwards [haeP] with x hx
  rw [hsplit x, hx]

end Work.BoseBoxFock.PotCubicLowBandAux
