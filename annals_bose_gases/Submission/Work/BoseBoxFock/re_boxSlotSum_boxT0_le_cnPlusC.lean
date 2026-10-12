import Mathlib
import Submission.Work.BoseBoxFock.boxSlotOf_evec_zero_eq_aPC
import Submission.Work.BoseBoxFock.boxSlotSum_boxT0
import Submission.Work.BoseBoxFock.boxTwinDefs
import Submission.Work.BoseBoxFock.cnPlusC_eq_kinetic_sub_aPC
import Submission.Work.BoseBoxFock.slotProj1_boxSlotOf_self
import Submission.Work.BoseBoxFock.xwSlotAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.re_boxSlotSum_boxT0_le_cnPlusC` — the `nExc` row at a **weak** state bundle

The companion of `Work.BoseBoxFock.re_cIPn_boxSlotSum_boxT0_le_cnPlusC`, but for the *honest*
(weak) regularity bundle that the selection layer actually produces: the modes `e l` are only
**measurable and bounded** (with support in the box `boxL ℓ`) and the state `Θ` is only
**measurable, bounded and supported in `abox n ℓ`** — no continuity, no compact support and no
symmetry.

The inequality is the same, `∫_{abox} (star Θ · Σ_j (boxT0)_j Θ).re ≤ cnPlusC ℓ Θ`, and the
proof is the same three-piece decomposition as in the continuous case, with each analytic input
re-derived at the weak bundle:

* `boxSlotSum e boxT0 Θ = Σ_j slotProj1 e j Θ − Σ_j boxSlotOf e e₀ e₀ j Θ` pointwise
  (`boxSlotSum_boxT0` + a weak `boxSlotSum_one_eq_sum_slotProj1_bdd`, whose only new ingredient
  is the integrability of the fibre integrand from boundedness + box support,
  `integrable_mode_state_bdd`);
* `boxSlotOf e e₀ e₀ j Θ = aPC ℓ j Θ` a.e. on the box (`boxSlotOf_evec_zero_eq_aPC`, which
  already only needs `MemLp · ⊤`, derived here from measurability + boundedness);
* the box pairing `A = Σ_j ∫ ‖slotProj1 e j Θ‖²` (`re_integral_star_sum_slotProj1_bdd`, built on
  `XwSlot.inner_pair_eq_normSq_bdd`) and the contraction `A ≤ n ∫ ‖Θ‖²`
  (`XwSlot.slotProj1_contract_box'`).

The kinetic form of the excited count (`cnPlusC_eq_kinetic_sub_aPC_bdd`) is the weak twin of
`cnPlusC_eq_kinetic_sub_aPC`: its proof needs only `MemLp Θ ⊤` (from measurability + boundedness)
for `cIPn_sum_aPC_re`, plus the everywhere bound for the integrability bookkeeping.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-! ## 1. The fibre integrand is integrable -/

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

private lemma coeff_one' {m : ℕ} (l l' : Fin m) :
    ((1 : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (Work.BoseB4.evec m l')) l
      = (if l = l' then (1 : ℝ) else 0) := by
  rw [Module.End.one_apply]
  simp [Work.BoseB4.evec, Pi.single_apply]

private lemma boxSlotOf_evec_self_apply' {m n : ℕ} (e : Fin m → Work.BoseDict.Sp → ℂ)
    (l : Fin m) (j : Fin n) (Θ : Work.BoseDict.Xn n → ℂ) (x : Work.BoseDict.Xn n) :
    Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l) j Θ x
      = e l (x j) * ∫ w : Work.BoseDict.Sp, star (e l w) * Θ (Function.update x j w) := by
  rw [Work.BoseDict.boxSlotOf, etaOf_evec' e l]
  simp only [starRingEnd_apply]

private lemma boxSlotSum_apply' {m n : ℕ} (e : Fin m → Work.BoseDict.Sp → ℂ)
    (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (Θ : Work.BoseDict.Xn n → ℂ)
    (x : Work.BoseDict.Xn n) :
    Work.BoseDict.boxSlotSum e T Θ x = ∑ j : Fin n, ∑ l : Fin m, ∑ l' : Fin m,
      (T (Work.BoseB4.evec m l') l : ℝ) •
        Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ x := by
  simp only [Work.BoseDict.boxSlotSum, Finset.sum_apply, Pi.smul_apply]

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

/-- Evaluation of the single-slot projection as the mode expansion of the fibre. -/
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

/-! ## 3. Measurability of the complex slot mean at a merely measurable state -/

/-- `aPC` of a measurable state is a.e. strongly measurable.  (Twin of
`aPC_aestronglyMeasurable_of_stronglyMeasurable` with measurable in place of strongly
measurable.) -/
private theorem aPC_aestronglyMeasurable_of_measurable {N : ℕ} {ℓ : ℝ} (j : Fin N)
    {f : Work.BoseDict.Xn N → ℂ} (hf : Measurable f) :
    AEStronglyMeasurable (aPC ℓ j f) (volume : Measure (Work.BoseDict.Xn N)) := by
  have hjoint : AEStronglyMeasurable
      (fun p : Work.BoseDict.Xn N × Work.BoseDict.Sp => f (Function.update p.1 j p.2))
      ((volume : Measure (Work.BoseDict.Xn N)).prod
        ((volume : Measure (Work.BoseDict.Sp)).restrict (Submission.BoseGases.acube ℓ))) :=
    (hf.comp (measurable_update'
      (X := fun _ : Fin N => Work.BoseDict.Sp) (a := j))).aestronglyMeasurable
  have h1 := hjoint.integral_prod_right'
  have h2 : AEStronglyMeasurable
      (fun x : Work.BoseDict.Xn N => ((1 / ℓ ^ 3 : ℝ) : ℂ)
        * ∫ y : Work.BoseDict.Sp, f (Function.update x j y)
          ∂((volume : Measure (Work.BoseDict.Sp)).restrict (Submission.BoseGases.acube ℓ)))
      volume :=
    h1.const_mul _
  exact h2

/-! ## 4. The box pairing with the total slot projection, at the weak bundle -/

private theorem re_integral_star_sum_slotProj1_bdd {m n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {e : Fin m → Work.BoseDict.Sp → ℂ}
    (he : ∀ l l', (∫ x : Work.BoseDict.Sp, (starRingEnd ℂ) (e l x) * e l' x)
      = if l = l' then (1 : ℂ) else 0)
    (hbdd : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    {Θ : Work.BoseDict.Xn n → ℂ} (hΘm : Measurable Θ) (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C) :
    (∫ x in Submission.BoseGases.abox n ℓ,
        star (Θ x) * (∑ j : Fin n, slotProj1 e j Θ x)).re
      = ∑ j : Fin n, ∫ x in Submission.BoseGases.abox n ℓ, ‖slotProj1 e j Θ x‖ ^ 2 := by
  classical
  obtain ⟨C, hC⟩ := hΘb
  haveI hfin : IsFiniteMeasure
      ((volume : Measure (Work.BoseDict.Xn n)).restrict (Submission.BoseGases.abox n ℓ)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact Submission.BoseGases.abox_lt_top n ℓ hℓ.le⟩
  have hΘmem : MemLp Θ ⊤ :=
    MeasureTheory.memLp_top_of_bound hΘm.aestronglyMeasurable C (Filter.Eventually.of_forall hC)
  have hPj : ∀ j : Fin n, MemLp (slotProj1 e j Θ) ⊤ :=
    fun j => slotProj1_memLp_top hℓ hbdd hsupp j hΘmem
  have hInt : ∀ j : Fin n, Integrable (fun x => star (Θ x) * slotProj1 e j Θ x)
      ((volume : Measure (Work.BoseDict.Xn n)).restrict (Submission.BoseGases.abox n ℓ)) := by
    intro j
    exact ((hΘmem.star).mono_measure Measure.restrict_le_self).mul
      ((hPj j).mono_measure Measure.restrict_le_self) |>.integrable le_top
  have hmain : (∫ x in Submission.BoseGases.abox n ℓ,
        star (Θ x) * (∑ j : Fin n, slotProj1 e j Θ x))
      = ∑ j : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
          star (Θ x) * slotProj1 e j Θ x := by
    rw [show (fun x => star (Θ x) * (∑ j : Fin n, slotProj1 e j Θ x))
        = fun x => ∑ j : Fin n, star (Θ x) * slotProj1 e j Θ x from
      funext fun x => by rw [Finset.mul_sum]]
    exact MeasureTheory.integral_finsetSum Finset.univ (fun j _ => hInt j)
  rw [hmain, Complex.re_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have h := ContinuousLinearMap.integral_comp_comm Complex.reCLM (hInt j)
  simp only [Complex.reCLM_apply] at h
  rw [← h]
  exact Work.BoseBoxFock.XwSlot.inner_pair_eq_normSq_bdd hℓ he hbdd hsupp j hΘm ⟨C, hC⟩

/-! ## 5. The kinetic form of the excited count, at the weak bundle -/

private theorem cnPlusC_eq_kinetic_sub_aPC_bdd {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {Θ : Work.BoseDict.Xn n → ℂ} (hΘm : Measurable Θ)
    (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C)
    (hΘsupp : Function.support Θ ⊆ Submission.BoseGases.abox n ℓ) :
    cnPlusC ℓ Θ
      = (n : ℝ) * (∫ x in Submission.BoseGases.abox n ℓ, ‖Θ x‖ ^ 2)
        - (∫ x in Submission.BoseGases.abox n ℓ,
            star (Θ x) * (∑ j : Fin n, aPC ℓ j Θ x)).re := by
  obtain ⟨C₀, hCb₀⟩ := hΘb
  set C : ℝ := max C₀ 0 with hCdef
  have hC0 : 0 ≤ C := le_max_right _ _
  have hCb : ∀ x, ‖Θ x‖ ≤ C := fun x => le_trans (hCb₀ x) (le_max_left _ _)
  have hMemLp : MemLp Θ (⊤ : ENNReal) (volume : Measure (Work.BoseDict.Xn n)) :=
    MeasureTheory.memLp_top_of_bound hΘm.aestronglyMeasurable C (Filter.Eventually.of_forall hCb)
  have hcn := cIPn_sum_aPC_re (d := n) hℓ Θ hMemLp hΘsupp
  rw [← hcn]
  -- ## measurability and bounds on the box
  have hAesmΘ : AEStronglyMeasurable Θ
      (volume.restrict (Submission.BoseGases.abox n ℓ)) :=
    hΘm.aestronglyMeasurable.restrict
  have hAesm_aPC : ∀ j : Fin n, AEStronglyMeasurable (aPC ℓ j Θ)
      (volume.restrict (Submission.BoseGases.abox n ℓ)) :=
    fun j => (aPC_aestronglyMeasurable_of_measurable (ℓ := ℓ) j hΘm).restrict
  have hbnd_aPC : ∀ j : Fin n, ∀ x, ‖aPC ℓ j Θ x‖ ≤ C :=
    fun j => norm_aPC_le hℓ j hC0 hCb
  have hAesm_A : AEStronglyMeasurable
      (fun x : Work.BoseDict.Xn n => ∑ j : Fin n, aPC ℓ j Θ x)
      (volume.restrict (Submission.BoseGases.abox n ℓ)) := by
    have h := Finset.aestronglyMeasurable_sum (Finset.univ : Finset (Fin n))
      (fun j _ => hAesm_aPC j)
    exact h.congr (Filter.Eventually.of_forall (fun x => by simp only [Finset.sum_apply]))
  have hAesm_g : AEStronglyMeasurable
      (fun x : Work.BoseDict.Xn n => ∑ j : Fin n, (Θ x - aPC ℓ j Θ x))
      (volume.restrict (Submission.BoseGases.abox n ℓ)) := by
    have h := Finset.aestronglyMeasurable_sum (Finset.univ : Finset (Fin n))
      (fun j _ => hAesmΘ.sub (hAesm_aPC j))
    exact h.congr (Filter.Eventually.of_forall (fun x => by simp [Finset.sum_apply]))
  have hbnd_A : ∀ x : Work.BoseDict.Xn n, ‖∑ j : Fin n, aPC ℓ j Θ x‖ ≤ n * C := by
    intro x
    calc ‖∑ j : Fin n, aPC ℓ j Θ x‖
        ≤ ∑ j : Fin n, ‖aPC ℓ j Θ x‖ := norm_sum_le _ _
      _ ≤ ∑ _j : Fin n, C := Finset.sum_le_sum (fun j _ => hbnd_aPC j x)
      _ = n * C := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hbnd_g : ∀ x : Work.BoseDict.Xn n,
      ‖∑ j : Fin n, (Θ x - aPC ℓ j Θ x)‖ ≤ n * (C + C) := by
    intro x
    calc ‖∑ j : Fin n, (Θ x - aPC ℓ j Θ x)‖
        ≤ ∑ j : Fin n, ‖Θ x - aPC ℓ j Θ x‖ := norm_sum_le _ _
      _ ≤ ∑ _j : Fin n, (C + C) := Finset.sum_le_sum
          (fun j _ => le_trans (norm_sub_le _ _) (add_le_add (hCb x) (hbnd_aPC j x)))
      _ = n * (C + C) := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- ## integrability of the three integrands on the (finite-measure) box
  have hIntL : IntegrableOn
      (fun x => star (Θ x) * (∑ j : Fin n, (Θ x - aPC ℓ j Θ x)))
      (Submission.BoseGases.abox n ℓ) volume := by
    refine IntegrableOn.of_bound (Submission.BoseGases.abox_lt_top n ℓ hℓ.le)
      (hAesmΘ.star.mul hAesm_g) (C * (n * (C + C))) ?_
    filter_upwards with x
    rw [norm_mul, norm_star]
    exact mul_le_mul (hCb x) (hbnd_g x) (norm_nonneg _) hC0
  have hIntR : IntegrableOn
      (fun x => star (Θ x) * (∑ j : Fin n, aPC ℓ j Θ x))
      (Submission.BoseGases.abox n ℓ) volume := by
    refine IntegrableOn.of_bound (Submission.BoseGases.abox_lt_top n ℓ hℓ.le)
      (hAesmΘ.star.mul hAesm_A) (C * (n * C)) ?_
    filter_upwards with x
    rw [norm_mul, norm_star]
    exact mul_le_mul (hCb x) (hbnd_A x) (norm_nonneg _) hC0
  have hIntSq : IntegrableOn (fun x => ‖Θ x‖ ^ 2) (Submission.BoseGases.abox n ℓ) volume := by
    refine IntegrableOn.of_bound (Submission.BoseGases.abox_lt_top n ℓ hℓ.le)
      (((hΘm.norm.aestronglyMeasurable).pow 2).mono_measure Measure.restrict_le_self)
        (C * C) ?_
    filter_upwards with x
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    nlinarith [hCb x, hC0, norm_nonneg (Θ x)]
  -- ## rewrite the pairing as a box integral (`Θ` vanishes off the box)
  have h1 : Work.BoseDict.cIPn n Θ (fun x => ∑ j : Fin n, (Θ x - aPC ℓ j Θ x))
      = ∫ x in Submission.BoseGases.abox n ℓ,
          star (Θ x) * (∑ j : Fin n, (Θ x - aPC ℓ j Θ x)) := by
    rw [Work.BoseDict.cIPn]
    exact (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      have hx0 : Θ x = 0 := by
        by_contra h
        exact hx (hΘsupp ((Function.mem_support).mpr h))
      rw [hx0]; simp)).symm
  -- ## pass to real parts
  have h2 : (∫ x in Submission.BoseGases.abox n ℓ,
        star (Θ x) * (∑ j : Fin n, (Θ x - aPC ℓ j Θ x))).re
      = ∫ x in Submission.BoseGases.abox n ℓ,
          (star (Θ x) * (∑ j : Fin n, (Θ x - aPC ℓ j Θ x))).re :=
    setIntegral_re_complex_xn _ _ hIntL
  -- ## the pointwise algebraic identity
  have hpt : ∀ x : Work.BoseDict.Xn n,
      (star (Θ x) * (∑ j : Fin n, (Θ x - aPC ℓ j Θ x))).re
      = (n : ℝ) * ‖Θ x‖ ^ 2
        - (star (Θ x) * (∑ j : Fin n, aPC ℓ j Θ x)).re := by
    intro x
    have hsplit : star (Θ x) * (∑ j : Fin n, (Θ x - aPC ℓ j Θ x))
        = (n : ℂ) * (star (Θ x) * Θ x) - star (Θ x) * (∑ j : Fin n, aPC ℓ j Θ x) := by
      rw [Finset.mul_sum]
      simp only [mul_sub, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      rw [← Finset.mul_sum]
    rw [hsplit, Complex.sub_re]
    congr 1
    rw [show star (Θ x) = (starRingEnd ℂ) (Θ x) from rfl, Complex.conj_mul']
    rw [show (n : ℂ) = ((n : ℝ) : ℂ) from (Complex.ofReal_natCast n).symm]
    rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
  have h3 : (∫ x in Submission.BoseGases.abox n ℓ,
        (star (Θ x) * (∑ j : Fin n, (Θ x - aPC ℓ j Θ x))).re)
      = ∫ x in Submission.BoseGases.abox n ℓ,
          ((n : ℝ) * ‖Θ x‖ ^ 2 - (star (Θ x) * (∑ j : Fin n, aPC ℓ j Θ x)).re) :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)
  -- ## split the integral
  have h4 : (∫ x in Submission.BoseGases.abox n ℓ,
          ((n : ℝ) * ‖Θ x‖ ^ 2 - (star (Θ x) * (∑ j : Fin n, aPC ℓ j Θ x)).re))
      = (n : ℝ) * (∫ x in Submission.BoseGases.abox n ℓ, ‖Θ x‖ ^ 2)
        - ∫ x in Submission.BoseGases.abox n ℓ,
            (star (Θ x) * (∑ j : Fin n, aPC ℓ j Θ x)).re := by
    have h := MeasureTheory.integral_sub (f := fun x => (n : ℝ) * ‖Θ x‖ ^ 2)
      (g := fun x => (star (Θ x) * (∑ j : Fin n, aPC ℓ j Θ x)).re)
      (hIntSq.const_mul (n : ℝ)) hIntR.re
    rw [MeasureTheory.integral_const_mul] at h
    exact h
  have h5 : (∫ x in Submission.BoseGases.abox n ℓ,
          (star (Θ x) * (∑ j : Fin n, aPC ℓ j Θ x)).re)
      = (∫ x in Submission.BoseGases.abox n ℓ,
          star (Θ x) * (∑ j : Fin n, aPC ℓ j Θ x)).re :=
    (setIntegral_re_complex_xn _ _ hIntR).symm
  rw [h1, h2, h3, h4, h5]

/-! ## 6. The target -/

theorem re_boxSlotSum_boxT0_le_cnPlusC {m n : ℕ} [NeZero m] {ℓ : ℝ} (hℓ : 0 < ℓ)
    {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hmeas : ∀ l, Measurable (e l))
    (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (horth : ∀ l l', (∫ z : EuclideanSpace ℝ (Fin 3), star (e l z) * e l' z)
      = (if l = l' then (1 : ℂ) else 0))
    (hint : ∀ l l', MeasureTheory.Integrable
      (fun z : EuclideanSpace ℝ (Fin 3) => star (e l z) * e l' z))
    (hpin : ∃ c : ℂ, (starRingEnd ℂ) c * c = (ℓ ^ 3)⁻¹ ∧
      e 0 =ᵐ[MeasureTheory.volume] fun x => c * Work.BoseK15.corpusBox.thetaFun ℓ x)
    {Θ : Work.BoseDict.Xn n → ℂ} (hΘm : Measurable Θ)
    (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C)
    (hΘsupp : Function.support Θ ⊆ Submission.BoseGases.abox n ℓ) :
    (∫ x in Submission.BoseGases.abox n ℓ,
        (star (Θ x) * Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m) Θ x).re)
      ≤ Work.BoseBoxFock.cnPlusC ℓ Θ := by
  classical
  -- ## 0. the weak bundle converted to `MemLp`
  have heMemLp : ∀ l, MemLp (e l) (⊤ : ENNReal) := by
    intro l
    obtain ⟨Cl, hCl⟩ := hbdd l
    exact MeasureTheory.memLp_top_of_bound (hmeas l).aestronglyMeasurable (max Cl 0)
      (Filter.Eventually.of_forall (fun x => le_trans (hCl x) (le_max_left _ _)))
  have horth' : ∀ l l', (∫ x : EuclideanSpace ℝ (Fin 3), (starRingEnd ℂ) (e l x) * e l' x)
      = (if l = l' then (1 : ℂ) else 0) := fun l l' => horth l l'
  have hΘb' : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C := hΘb
  obtain ⟨CΘ, hCΘ⟩ := hΘb'
  set C : ℝ := max CΘ 0 with hCdef
  have hC0 : 0 ≤ C := le_max_right _ _
  have hCb : ∀ x, ‖Θ x‖ ≤ C := fun x => le_trans (hCΘ x) (le_max_left _ _)
  have hΘmemLp : MemLp Θ (⊤ : ENNReal) :=
    MeasureTheory.memLp_top_of_bound hΘm.aestronglyMeasurable C
      (Filter.Eventually.of_forall hCb)
  have hΘ0 : ∀ x, x ∉ Submission.BoseGases.abox n ℓ → Θ x = 0 := fun x hx => by
    by_contra h
    exact hx (hΘsupp (Function.mem_support.mpr h))
  haveI hfin : IsFiniteMeasure
      ((volume : Measure (Work.BoseDict.Xn n)).restrict (Submission.BoseGases.abox n ℓ)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact Submission.BoseGases.abox_lt_top n ℓ hℓ.le⟩
  -- ## 1. the pointwise split of the `boxT0` slot sum
  have hsplit : ∀ x : Work.BoseDict.Xn n,
      Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m) Θ x
        = (∑ j : Fin n, slotProj1 e j Θ x)
          - ∑ j : Fin n,
              Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m 0) (Work.BoseB4.evec m 0) j Θ x := by
    intro x
    have h1 := congrFun
      (boxSlotSum_one_eq_sum_slotProj1_bdd (m := m) (n := n) hℓ hmeas hbdd hsupp hΘm hΘb) x
    have h2 := congrFun (Work.BoseBoxFock.boxSlotSum_boxT0 (m := m) (d := n) (e := e) Θ) x
    rw [h2]
    simp only [Pi.sub_apply, Finset.sum_apply]
    rw [h1]
  -- ## 2. the a.e. identification of the condensate slot with `aPC`
  have haeP : ∀ᵐ x ∂((volume : Measure (Work.BoseDict.Xn n)).restrict
        (Submission.BoseGases.abox n ℓ)),
      (∑ j : Fin n, Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m 0) (Work.BoseB4.evec m 0) j Θ x)
        = ∑ j : Fin n, aPC ℓ j Θ x := by
    have h := (Filter.eventually_all).mpr (fun j : Fin n =>
      Work.BoseBoxFock.boxSlotOf_evec_zero_eq_aPC (m := m) (d := n) hℓ heMemLp hsupp hpin Θ
        hΘsupp j)
    filter_upwards [h] with x hx
    exact Finset.sum_congr rfl (fun j _ => hx j)
  -- ## 3. integrability of the two pieces on the box
  have hmemLp_starΘ : MemLp (fun x : Work.BoseDict.Xn n => star (Θ x)) (⊤ : ENNReal)
      ((volume : Measure (Work.BoseDict.Xn n)).restrict (Submission.BoseGases.abox n ℓ)) :=
    MeasureTheory.memLp_top_of_bound
      (hΘm.aestronglyMeasurable.star.mono_measure Measure.restrict_le_self) C
      (Filter.Eventually.of_forall (fun x => by rw [norm_star]; exact hCb x))
  have hmemLp_slot : MemLp (fun x : Work.BoseDict.Xn n => ∑ j : Fin n, slotProj1 e j Θ x)
      (⊤ : ENNReal)
      ((volume : Measure (Work.BoseDict.Xn n)).restrict (Submission.BoseGases.abox n ℓ)) :=
    memLp_finsetSum Finset.univ (fun j _ =>
      (slotProj1_memLp_top hℓ heMemLp hsupp j hΘmemLp).mono_measure Measure.restrict_le_self)
  have hmemLp_aPC : MemLp (fun x : Work.BoseDict.Xn n => ∑ j : Fin n, aPC ℓ j Θ x)
      (⊤ : ENNReal)
      ((volume : Measure (Work.BoseDict.Xn n)).restrict (Submission.BoseGases.abox n ℓ)) :=
    memLp_finsetSum Finset.univ (fun j _ =>
      MeasureTheory.memLp_top_of_bound
        ((aPC_aestronglyMeasurable_of_measurable (ℓ := ℓ) j hΘm).mono_measure
          Measure.restrict_le_self)
        C (Filter.Eventually.of_forall (fun x => norm_aPC_le hℓ j hC0 hCb x)))
  have hInt1 : Integrable
      (fun x : Work.BoseDict.Xn n => star (Θ x) * (∑ j : Fin n, slotProj1 e j Θ x))
      ((volume : Measure (Work.BoseDict.Xn n)).restrict (Submission.BoseGases.abox n ℓ)) :=
    (MeasureTheory.MemLp.mul hmemLp_starΘ hmemLp_slot).integrable le_top
  have hInt2 : Integrable
      (fun x : Work.BoseDict.Xn n => star (Θ x) * (∑ j : Fin n, aPC ℓ j Θ x))
      ((volume : Measure (Work.BoseDict.Xn n)).restrict (Submission.BoseGases.abox n ℓ)) :=
    (MeasureTheory.MemLp.mul hmemLp_starΘ hmemLp_aPC).integrable le_top
  have hI0 : Integrable
      (fun x : Work.BoseDict.Xn n =>
        star (Θ x) * Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m) Θ x)
      ((volume : Measure (Work.BoseDict.Xn n)).restrict (Submission.BoseGases.abox n ℓ)) :=
    (hInt1.sub hInt2).congr (by
      filter_upwards [haeP] with x hx
      simp only [Pi.sub_apply]
      rw [hsplit x, hx, mul_sub])
  -- ## 4. the box integral rewritten as the difference
  have hcongr : (∫ x in Submission.BoseGases.abox n ℓ,
        star (Θ x) * Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m) Θ x)
      = ∫ x in Submission.BoseGases.abox n ℓ,
          (star (Θ x) * (∑ j : Fin n, slotProj1 e j Θ x)
            - star (Θ x) * (∑ j : Fin n, aPC ℓ j Θ x)) := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [haeP] with x hx
    rw [hsplit x, hx, mul_sub]
  -- ## 5. the two estimates
  have hAeq := re_integral_star_sum_slotProj1_bdd (m := m) (n := n) hℓ horth' heMemLp hsupp
    hΘm hΘb
  have hS : (∑ j : Fin n, ∫ x in Submission.BoseGases.abox n ℓ, ‖slotProj1 e j Θ x‖ ^ 2)
      ≤ (n : ℝ) * ∫ x in Submission.BoseGases.abox n ℓ, ‖Θ x‖ ^ 2 := by
    calc (∑ j : Fin n, ∫ x in Submission.BoseGases.abox n ℓ, ‖slotProj1 e j Θ x‖ ^ 2)
        ≤ ∑ _j : Fin n, ∫ x in Submission.BoseGases.abox n ℓ, ‖Θ x‖ ^ 2 :=
          Finset.sum_le_sum (fun j _ =>
            Work.BoseBoxFock.XwSlot.slotProj1_contract_box' hℓ horth' heMemLp hsupp j
              hΘmemLp hΘ0)
      _ = (n : ℝ) * ∫ x in Submission.BoseGases.abox n ℓ, ‖Θ x‖ ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h2 := cnPlusC_eq_kinetic_sub_aPC_bdd (n := n) hℓ hΘm hΘb hΘsupp
  -- ## 6. assembly
  calc (∫ x in Submission.BoseGases.abox n ℓ,
        (star (Θ x) * Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m) Θ x).re)
      = (∫ x in Submission.BoseGases.abox n ℓ,
          star (Θ x) * Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 m) Θ x).re :=
        (setIntegral_re_complex_xn _ _ hI0).symm
    _ = (∫ x in Submission.BoseGases.abox n ℓ,
          (star (Θ x) * (∑ j : Fin n, slotProj1 e j Θ x)
            - star (Θ x) * (∑ j : Fin n, aPC ℓ j Θ x))).re := by rw [hcongr]
    _ = ((∫ x in Submission.BoseGases.abox n ℓ,
            star (Θ x) * (∑ j : Fin n, slotProj1 e j Θ x))
          - (∫ x in Submission.BoseGases.abox n ℓ,
            star (Θ x) * (∑ j : Fin n, aPC ℓ j Θ x))).re := by
        rw [MeasureTheory.integral_sub hInt1 hInt2]
    _ = (∫ x in Submission.BoseGases.abox n ℓ,
            star (Θ x) * (∑ j : Fin n, slotProj1 e j Θ x)).re
          - (∫ x in Submission.BoseGases.abox n ℓ,
            star (Θ x) * (∑ j : Fin n, aPC ℓ j Θ x)).re :=
        Complex.sub_re _ _
    _ ≤ Work.BoseBoxFock.cnPlusC ℓ Θ := by
        linarith [hAeq, hS, h2]

end Work.BoseBoxFock
