import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

set_option linter.unusedSimpArgs false

namespace Commons.Analysis.Inequalities

open scoped BigOperators ENNReal
open MeasureTheory

noncomputable section

/-- `LWStatement m` is the `ℝ≥0∞`-valued Loomis–Whitney inequality for `ℝ^{m+1}` with its `m+1`
coordinate projections to `ℝ^m`, exponent `m`. -/
def LWStatement (m : ℕ) : Prop :=
  ∀ g : Fin (m + 1) → (Fin m → ℝ) → ℝ≥0∞,
    (∀ i, Measurable (g i)) →
    ∫⁻ x : Fin (m + 1) → ℝ, ∏ i : Fin (m + 1), g i (fun j : Fin m => x (Fin.succAbove i j))
      ≤ ∏ i : Fin (m + 1),
          (∫⁻ y : Fin m → ℝ, g i y ^ ((m : ℕ) : ℝ)) ^ (1 / ((m : ℕ) : ℝ))

/-- The map `(t, z) ↦ Fin.cons t z` transports the product Lebesgue measure on `ℝ × ℝ^N`
to the Lebesgue measure on `ℝ^{N+1}`. -/
lemma volume_preserving_cons (N : ℕ) :
    MeasurePreserving (fun p : ℝ × (Fin N → ℝ) => Fin.cons p.1 p.2) volume
      (volume : Measure (Fin (N + 1) → ℝ)) := by
  have h := (volume_preserving_piFinSuccAbove (fun _ : Fin (N + 1) => ℝ) 0).symm
  have hf : (fun p : ℝ × (Fin N → ℝ) => Fin.cons p.1 p.2)
      = (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N + 1) => ℝ) 0).symm := by
    funext p; simp [MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv]
  rw [hf]; exact h

/-- Splitting off the first coordinate of `ℝ^{N+1}`. -/
lemma lintegral_pi_succ_split {N : ℕ} (Φ : (Fin (N + 1) → ℝ) → ℝ≥0∞)
    (hΦ : AEMeasurable Φ volume) :
    ∫⁻ x : Fin (N + 1) → ℝ, Φ x
      = ∫⁻ t : ℝ, ∫⁻ z : Fin N → ℝ, Φ (Fin.cons t z) := by
  have hMP : MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N + 1) => ℝ) 0)
      volume (volume.prod volume) := volume_preserving_piFinSuccAbove _ 0
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N + 1) => ℝ) 0 with he
  have harr : (fun a : Fin (N + 1) → ℝ => Φ (e.symm (e a))) = Φ := by
    funext a; simp
  have h1 := (MeasurePreserving.lintegral_map_equiv
      (f := fun p : ℝ × (Fin N → ℝ) => Φ (e.symm p)) e hMP).symm
  rw [harr] at h1
  have hcons : (fun p : ℝ × (Fin N → ℝ) => e.symm p)
      = (fun p : ℝ × (Fin N → ℝ) => Fin.cons p.1 p.2) := by
    funext p; simp [he, MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv]
  have h2 : ∫⁻ (a : ℝ × (Fin N → ℝ)), Φ (e.symm a)
      = ∫⁻ p : ℝ × (Fin N → ℝ), Φ (Fin.cons p.1 p.2) := by
    simp only [hcons]
  have h3 := h1.trans h2
  rw [h3]
  exact lintegral_prod (fun p : ℝ × (Fin N → ℝ) => Φ (Fin.cons p.1 p.2))
    (hΦ.comp_quasiMeasurePreserving (volume_preserving_cons N).quasiMeasurePreserving)

/-- Composing an ae-measurable function with the coordinate deletion `x ↦ x ∘ succAbove i`. -/
lemma aemeasurable_comp_succAbove {N : ℕ} (i : Fin (N + 1)) {h : (Fin N → ℝ) → ℝ≥0∞}
    (hh : AEMeasurable h volume) :
    AEMeasurable (fun x : Fin (N + 1) → ℝ => h (fun j => x (Fin.succAbove i j))) volume := by
  have he := volume_preserving_piFinSuccAbove (fun _ : Fin (N + 1) => ℝ) i
  have h1 : AEMeasurable (fun p : ℝ × (Fin N → ℝ) => h p.2) (volume.prod volume) :=
    hh.comp_snd
  exact (h1.comp_quasiMeasurePreserving he.quasiMeasurePreserving)

/-- `Fin 1 → ℝ` integrals are integrals over `ℝ` of the constant functions. -/
lemma lintegral_const_fin_one (h : (Fin 1 → ℝ) → ℝ≥0∞) :
    ∫⁻ y : Fin 1 → ℝ, h y = ∫⁻ t : ℝ, h (fun _ => t) := by
  have step1 : ∫⁻ y : Fin 1 → ℝ, h y
      = ∫⁻ y : Fin 1 → ℝ, h (fun _ : Fin 1 => y default) := by
    refine lintegral_congr fun y => ?_
    congr 1
    funext j
    rw [Subsingleton.elim j default]
  rw [step1]
  have hMP := volume_preserving_piUnique (fun _ : Fin 1 => ℝ)
  have hh := MeasurePreserving.lintegral_map_equiv (f := fun t : ℝ => h (fun _ : Fin 1 => t))
      (MeasurableEquiv.piUnique (fun _ : Fin 1 => ℝ)) hMP
  rw [hh]
  refine lintegral_congr fun y => ?_
  simp [MeasurableEquiv.piUnique_apply]

/-- The transport `t ↦ (fun _ : Fin 1 => t)` is quasi-measure-preserving. -/
lemma quasiMeasurePreserving_const_fin_one :
    Measure.QuasiMeasurePreserving (fun t : ℝ => (fun _ : Fin 1 => t)) volume
      (volume : Measure (Fin 1 → ℝ)) := by
  have h := (volume_preserving_piUnique (fun _ : Fin 1 => ℝ)).symm.quasiMeasurePreserving
  have he : (fun t : ℝ => (fun _ : Fin 1 => t))
      = (MeasurableEquiv.piUnique (fun _ : Fin 1 => ℝ)).symm := by
    funext t
    rw [MeasurableEquiv.piUnique_symm_apply]
    funext i; simp [uniqueElim]
  rwa [he]

/-- The base case `m = 1` of Loomis–Whitney: Fubini. -/
lemma lw_base : LWStatement 1 := by
  intro g hg
  have hR : ∏ i : Fin (1 + 1),
        (∫⁻ y : Fin 1 → ℝ, g i y ^ (((1 : ℕ) : ℝ))) ^ (1 / (((1 : ℕ) : ℝ)))
      = (∫⁻ y : Fin 1 → ℝ, g 0 y) * (∫⁻ y : Fin 1 → ℝ, g 1 y) := by
    simp [Fin.prod_univ_succ]
  rw [hR]
  have hA : AEMeasurable (fun x : Fin (1 + 1) → ℝ =>
      ∏ i : Fin (1 + 1), g i (fun j : Fin 1 => x (Fin.succAbove i j))) volume := by
    simpa using Finset.aemeasurable_fun_prod (Finset.univ : Finset (Fin (1 + 1)))
      (fun i _ => aemeasurable_comp_succAbove i (hg i).aemeasurable)
  rw [lintegral_pi_succ_split _ hA]
  have hc0 : ∀ (t : ℝ) (z : Fin 1 → ℝ),
      (fun j : Fin 1 => (Fin.cons t z : Fin (1 + 1) → ℝ) (Fin.succAbove 0 j)) = z := by
    intro t z; funext j; fin_cases j; simp [Fin.succAbove_zero, Fin.cons_succ]
  have hc1 : ∀ (t : ℝ) (z : Fin 1 → ℝ),
      (fun j : Fin 1 => (Fin.cons t z : Fin (1 + 1) → ℝ) (Fin.succAbove 1 j)) = fun _ => t := by
    intro t z; funext j; fin_cases j; simp [Fin.succAbove, Fin.cons_zero]
  have hprod : ∀ (t : ℝ) (z : Fin 1 → ℝ),
      (∏ i : Fin (1 + 1), g i (fun j : Fin 1 => (Fin.cons t z : Fin (1+1) → ℝ) (Fin.succAbove i j)))
      = g 0 z * g 1 (fun _ : Fin 1 => t) := by
    intro t z
    rw [Fin.prod_univ_succ]
    simp only [Fin.prod_univ_one, Fin.succ_zero_eq_one]
    rw [hc0 t z, hc1 t z]
  simp_rw [hprod]
  have h1 : ∀ t : ℝ, ∫⁻ z : Fin 1 → ℝ, g 0 z * g 1 (fun _ : Fin 1 => t)
      = (∫⁻ z : Fin 1 → ℝ, g 0 z) * g 1 (fun _ : Fin 1 => t) := by
    intro t; rw [lintegral_mul_const'' (g 1 (fun _ : Fin 1 => t)) (hg 0).aemeasurable]
  simp_rw [h1]
  have h2 : ∫⁻ t : ℝ, (∫⁻ z : Fin 1 → ℝ, g 0 z) * g 1 (fun _ : Fin 1 => t)
      = (∫⁻ z : Fin 1 → ℝ, g 0 z) * ∫⁻ t : ℝ, g 1 (fun _ : Fin 1 => t) :=
    lintegral_const_mul'' (∫⁻ z : Fin 1 → ℝ, g 0 z)
      ((hg 1).aemeasurable.comp_quasiMeasurePreserving quasiMeasurePreserving_const_fin_one)
  rw [h2, lintegral_const_fin_one (g 1)]

/-- The induction step of Loomis–Whitney: `m+1 ≥ 2` from `m ≥ 1`. -/
lemma lw_step (m : ℕ) (hm : 1 ≤ m) (ih : LWStatement m) : LWStatement (m + 1) := by
  intro g hg
  have hMpos : (0:ℝ) < ((m:ℕ):ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hNpos : (0:ℝ) < ((m+1:ℕ):ℝ) := by exact_mod_cast (by omega : 0 < m + 1)
  have hqpos : (0:ℝ) < (((m+1:ℕ):ℝ)/((m:ℕ):ℝ)) := div_pos hNpos hMpos
  have hqinvpos : (0:ℝ) <= 1/(((m+1:ℕ):ℝ)/((m:ℕ):ℝ)) := by positivity
  have hpq : (((m+1:ℕ):ℝ)).HolderConjugate (((m+1:ℕ):ℝ)/((m:ℕ):ℝ)) := by
    rw [Real.holderConjugate_iff]
    refine ⟨by exact_mod_cast (by omega : 1 < m+1), ?_⟩
    have hM0 : ((m:ℕ):ℝ) ≠ 0 := hMpos.ne'
    have hN0 : ((m+1:ℕ):ℝ) ≠ 0 := hNpos.ne'
    field_simp
    push_cast; ring
  have hqmul : (((m+1:ℕ):ℝ)/((m:ℕ):ℝ)) * ((m:ℕ):ℝ) = ((m+1:ℕ):ℝ) := by
    have hM0 : ((m:ℕ):ℝ) ≠ 0 := hMpos.ne'
    field_simp
  have hpow : (1/((m:ℕ):ℝ)) * (1/(((m+1:ℕ):ℝ)/((m:ℕ):ℝ))) = 1/((m+1:ℕ):ℝ) := by
    have hM0 : ((m:ℕ):ℝ) ≠ 0 := hMpos.ne'
    have hN0 : ((m+1:ℕ):ℝ) ≠ 0 := hNpos.ne'
    field_simp
  have hsum : ∑ _i : Fin (m+1), (1:ℝ)/((m+1:ℕ):ℝ) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hN0 : ((m+1:ℕ):ℝ) ≠ 0 := hNpos.ne'
    field_simp
  -- measurability of `(t,z) ↦ Fin.cons t (z ∘ succAbove i)`
  have hconsmeas : ∀ i : Fin (m+1),
      Measurable (fun p : ℝ × (Fin (m+1) → ℝ) =>
        (Fin.cons p.1 (p.2 ∘ Fin.succAbove i) : Fin (m+1) → ℝ)) := by
    intro i
    have h1 : Measurable (fun p : ℝ × (Fin (m+1) → ℝ) => (p.1, p.2 ∘ Fin.succAbove i)) :=
      measurable_fst.prodMk
        ((measurable_pi_iff.mpr (fun j => measurable_pi_apply (Fin.succAbove i j))).comp measurable_snd)
    exact (volume_preserving_cons m).measurable.comp h1
  -- the goal's integrand
  have hΦae : AEMeasurable (fun x : Fin (m + 2) → ℝ =>
      ∏ i : Fin (m + 2), g i (fun j : Fin (m + 1) => x (Fin.succAbove i j))) volume := by
    simpa using Finset.aemeasurable_fun_prod (Finset.univ : Finset (Fin (m + 2)))
      (fun i _ => aemeasurable_comp_succAbove i (hg i).aemeasurable)
  have hcons0 : ∀ (t : ℝ) (z : Fin (m+1) → ℝ),
      (fun j : Fin (m+1) => (Fin.cons t z : Fin (m+2) → ℝ) (Fin.succAbove 0 j)) = z := by
    intro t z; funext j; simp [Fin.succAbove_zero, Fin.cons_succ]
  have hcons_succ : ∀ (t : ℝ) (z : Fin (m+1) → ℝ) (i : Fin (m+1)),
      (fun j : Fin (m+1) => (Fin.cons t z : Fin (m+2) → ℝ) (Fin.succAbove (Fin.succ i) j))
        = (Fin.cons t (z ∘ Fin.succAbove i) : Fin (m+1) → ℝ) := by
    intro t z i
    funext j
    exact congrFun (Fin.cons_comp_succ_succAbove t z i) j
  have hΦcons : ∀ (t : ℝ) (z : Fin (m+1) → ℝ),
      (∏ i : Fin (m+2), g i (fun j : Fin (m+1) => (Fin.cons t z : Fin (m+2) → ℝ) (Fin.succAbove i j)))
        = g 0 z * ∏ i : Fin (m+1), g (Fin.succ i) (Fin.cons t (z ∘ Fin.succAbove i)) := by
    intro t z
    rw [Fin.prod_univ_succ, hcons0 t z]
    simp only [hcons_succ t z]
  -- Step B2: the LW bound for the inner `z`-integral
  have hΩmeas : ∀ t : ℝ,
      AEMeasurable (fun z : Fin (m+1) → ℝ =>
        ∏ i : Fin (m+1), g (Fin.succ i) (Fin.cons t (z ∘ Fin.succAbove i))) volume := by
    intro t
    refine Finset.aemeasurable_fun_prod (Finset.univ : Finset (Fin (m+1))) (fun i _ => ?_)
    have h1 : Measurable (fun z : Fin (m+1) → ℝ =>
        (Fin.cons t (z ∘ Fin.succAbove i) : Fin (m+1) → ℝ)) :=
      (hconsmeas i).comp (measurable_const.prodMk measurable_id)
    exact ((hg (Fin.succ i)).comp h1).aemeasurable
  have hBmeas : ∀ (i : Fin (m+1)) (t : ℝ),
      Measurable (fun w : Fin m → ℝ => g (Fin.succ i) (Fin.cons t w)) := by
    intro i t
    exact (hg (Fin.succ i)).comp
      ((volume_preserving_cons m).measurable.comp (measurable_const.prodMk measurable_id))
  have stepB2 : ∀ t : ℝ,
      (∫⁻ z : Fin (m+1) → ℝ,
          (∏ i : Fin (m+1), g (Fin.succ i) (Fin.cons t (z ∘ Fin.succAbove i)))
            ^ (((m+1:ℕ):ℝ)/((m:ℕ):ℝ))) ^ (1 / (((m+1:ℕ):ℝ)/((m:ℕ):ℝ)))
      ≤ ∏ i : Fin (m+1),
          (∫⁻ w : Fin m → ℝ, (g (Fin.succ i) (Fin.cons t w)) ^ (((m+1:ℕ):ℝ)))
            ^ (1/((m+1:ℕ):ℝ)) := by
    intro t
    have hprod : ∀ z : Fin (m+1) → ℝ,
        (∏ i : Fin (m+1), g (Fin.succ i) (Fin.cons t (z ∘ Fin.succAbove i)))
            ^ (((m+1:ℕ):ℝ)/((m:ℕ):ℝ))
          = ∏ i : Fin (m+1),
              (g (Fin.succ i) (Fin.cons t (z ∘ Fin.succAbove i))) ^ (((m+1:ℕ):ℝ)/((m:ℕ):ℝ)) := by
      intro z
      rw [ENNReal.prod_rpow_of_nonneg (le_of_lt hqpos)]
    simp_rw [hprod]
    have hih := ih (fun i (w : Fin m → ℝ) =>
        (g (Fin.succ i) (Fin.cons t w)) ^ (((m+1:ℕ):ℝ)/((m:ℕ):ℝ)))
      (fun i => (hBmeas i t).pow_const _)
    have hAi : ∀ i : Fin (m+1),
        (∫⁻ w : Fin m → ℝ,
          ((g (Fin.succ i) (Fin.cons t w)) ^ (((m+1:ℕ):ℝ)/((m:ℕ):ℝ))) ^ ((m:ℕ):ℝ))
          = (∫⁻ w : Fin m → ℝ, (g (Fin.succ i) (Fin.cons t w)) ^ (((m+1:ℕ):ℝ))) := by
      intro i
      refine lintegral_congr fun w => ?_
      rw [← ENNReal.rpow_mul, hqmul]
    calc (∫⁻ z : Fin (m+1) → ℝ,
            ∏ i : Fin (m+1),
              (g (Fin.succ i) (Fin.cons t (z ∘ Fin.succAbove i))) ^ (((m+1:ℕ):ℝ)/((m:ℕ):ℝ)))
          ^ (1 / (((m+1:ℕ):ℝ)/((m:ℕ):ℝ)))
        ≤ (∏ i : Fin (m+1),
            (∫⁻ w : Fin m → ℝ,
              ((g (Fin.succ i) (Fin.cons t w)) ^ (((m+1:ℕ):ℝ)/((m:ℕ):ℝ))) ^ ((m:ℕ):ℝ))
              ^ (1/((m:ℕ):ℝ))) ^ (1 / (((m+1:ℕ):ℝ)/((m:ℕ):ℝ))) :=
          ENNReal.rpow_le_rpow hih hqinvpos
        _ = ∏ i : Fin (m+1),
            (∫⁻ w : Fin m → ℝ, (g (Fin.succ i) (Fin.cons t w)) ^ (((m+1:ℕ):ℝ)))
              ^ (1/((m+1:ℕ):ℝ)) := by
          simp_rw [hAi]
          rw [← ENNReal.prod_rpow_of_nonneg hqinvpos]
          refine Finset.prod_congr rfl (fun i _ => ?_)
          rw [← ENNReal.rpow_mul, hpow]
  -- the pointwise bound on the `z`-integral
  have hbound : ∀ t : ℝ, ∫⁻ z : Fin (m+1) → ℝ,
        (g 0 z * ∏ i : Fin (m+1), g (Fin.succ i) (Fin.cons t (z ∘ Fin.succAbove i)))
      ≤ (∫⁻ z : Fin (m+1) → ℝ, (g 0 z) ^ (((m+1:ℕ):ℝ))) ^ (1/((m+1:ℕ):ℝ))
        * ∏ i : Fin (m+1),
            (∫⁻ w : Fin m → ℝ, (g (Fin.succ i) (Fin.cons t w)) ^ (((m+1:ℕ):ℝ)))
              ^ (1/((m+1:ℕ):ℝ)) := by
    intro t
    refine (ENNReal.lintegral_mul_le_Lp_mul_Lq volume hpq (hg 0).aemeasurable (hΩmeas t)).trans ?_
    exact mul_le_mul_of_nonneg_left (stepB2 t) bot_le
  -- Step A: multi-factor Hölder in `t`
  have stepA : (∫⁻ t : ℝ, ∏ i : Fin (m+1),
        (∫⁻ w : Fin m → ℝ, (g (Fin.succ i) (Fin.cons t w)) ^ (((m+1:ℕ):ℝ))) ^ (1/((m+1:ℕ):ℝ)))
      ≤ ∏ i : Fin (m+1),
        (∫⁻ t : ℝ, ∫⁻ w : Fin m → ℝ, (g (Fin.succ i) (Fin.cons t w)) ^ (((m+1:ℕ):ℝ)))
          ^ (1/((m+1:ℕ):ℝ)) := by
    have hf : ∀ i ∈ (Finset.univ : Finset (Fin (m+1))),
        AEMeasurable (fun t : ℝ =>
          ∫⁻ w : Fin m → ℝ, (g (Fin.succ i) (Fin.cons t w)) ^ (((m+1:ℕ):ℝ))) volume := by
      intro i _
      have hjoint : AEMeasurable (fun p : ℝ × (Fin m → ℝ) =>
          (g (Fin.succ i) (Fin.cons p.1 p.2)) ^ (((m+1:ℕ):ℝ))) (volume.prod volume) :=
        ((hg (Fin.succ i)).comp (volume_preserving_cons m).measurable).aemeasurable.pow_const _
      exact hjoint.lintegral_prod_right'
    have hp : ∑ i ∈ (Finset.univ : Finset (Fin (m+1))), (1:ℝ)/((m+1:ℕ):ℝ) = 1 := by
      simpa using hsum
    have h2p : ∀ i ∈ (Finset.univ : Finset (Fin (m+1))), 0 ≤ (1:ℝ)/((m+1:ℕ):ℝ) :=
      fun i _ => by positivity
    simpa using ENNReal.lintegral_prod_norm_pow_le (Finset.univ : Finset (Fin (m+1)))
      (f := fun i t => ∫⁻ w : Fin m → ℝ, (g (Fin.succ i) (Fin.cons t w)) ^ (((m+1:ℕ):ℝ)))
      hf hp h2p
  -- Tonelli for the individual `t`-integrals
  have hEton : ∀ i : Fin (m+1),
      (∫⁻ t : ℝ, ∫⁻ w : Fin m → ℝ, (g (Fin.succ i) (Fin.cons t w)) ^ (((m+1:ℕ):ℝ)))
        = ∫⁻ y : Fin (m+1) → ℝ, (g (Fin.succ i) y) ^ (((m+1:ℕ):ℝ)) := by
    intro i
    refine (lintegral_prod (fun p : ℝ × (Fin m → ℝ) =>
      (g (Fin.succ i) (Fin.cons p.1 p.2)) ^ (((m+1:ℕ):ℝ))) ?_).symm.trans ?_
    · exact ((hg (Fin.succ i)).comp (volume_preserving_cons m).measurable).aemeasurable.pow_const _
    · exact MeasurePreserving.lintegral_comp (volume_preserving_cons m)
        (f := fun y : Fin (m+1) → ℝ => (g (Fin.succ i) y) ^ (((m+1:ℕ):ℝ)))
        ((hg (Fin.succ i)).pow_const _)
  -- measurability of the `t`-integrand for `lintegral_const_mul''`
  have hEmeas : AEMeasurable (fun t : ℝ => ∏ i : Fin (m+1),
      (∫⁻ w : Fin m → ℝ, (g (Fin.succ i) (Fin.cons t w)) ^ (((m+1:ℕ):ℝ))) ^ (1/((m+1:ℕ):ℝ))) volume := by
    refine Finset.aemeasurable_fun_prod (Finset.univ : Finset (Fin (m+1))) (fun i _ => ?_)
    have hjoint : AEMeasurable (fun p : ℝ × (Fin m → ℝ) =>
        (g (Fin.succ i) (Fin.cons p.1 p.2)) ^ (((m+1:ℕ):ℝ))) (volume.prod volume) :=
      ((hg (Fin.succ i)).comp (volume_preserving_cons m).measurable).aemeasurable.pow_const _
    exact (hjoint.lintegral_prod_right').pow_const _
  -- assemble
  rw [lintegral_pi_succ_split (N := m+1)
      (fun x : Fin (m+2) → ℝ => ∏ i : Fin (m+2), g i (fun j : Fin (m+1) => x (Fin.succAbove i j))) hΦae]
  simp_rw [hΦcons]
  calc ∫⁻ t : ℝ, ∫⁻ z : Fin (m+1) → ℝ,
          (g 0 z * ∏ i : Fin (m+1), g (Fin.succ i) (Fin.cons t (z ∘ Fin.succAbove i)))
      ≤ ∫⁻ t : ℝ, ((∫⁻ z : Fin (m+1) → ℝ, (g 0 z) ^ (((m+1:ℕ):ℝ))) ^ (1/((m+1:ℕ):ℝ))
          * ∏ i : Fin (m+1),
              (∫⁻ w : Fin m → ℝ, (g (Fin.succ i) (Fin.cons t w)) ^ (((m+1:ℕ):ℝ)))
                ^ (1/((m+1:ℕ):ℝ))) := lintegral_mono hbound
    _ = (∫⁻ z : Fin (m+1) → ℝ, (g 0 z) ^ (((m+1:ℕ):ℝ))) ^ (1/((m+1:ℕ):ℝ))
          * ∫⁻ t : ℝ, ∏ i : Fin (m+1),
              (∫⁻ w : Fin m → ℝ, (g (Fin.succ i) (Fin.cons t w)) ^ (((m+1:ℕ):ℝ)))
                ^ (1/((m+1:ℕ):ℝ)) := by
          rw [lintegral_const_mul'' _ hEmeas]
    _ ≤ (∫⁻ z : Fin (m+1) → ℝ, (g 0 z) ^ (((m+1:ℕ):ℝ))) ^ (1/((m+1:ℕ):ℝ))
          * ∏ i : Fin (m+1),
              (∫⁻ t : ℝ, ∫⁻ w : Fin m → ℝ, (g (Fin.succ i) (Fin.cons t w)) ^ (((m+1:ℕ):ℝ)))
                ^ (1/((m+1:ℕ):ℝ)) := by
          exact mul_le_mul_of_nonneg_left stepA bot_le
    _ = (∫⁻ z : Fin (m+1) → ℝ, (g 0 z) ^ (((m+1:ℕ):ℝ))) ^ (1/((m+1:ℕ):ℝ))
          * ∏ i : Fin (m+1),
              (∫⁻ y : Fin (m+1) → ℝ, (g (Fin.succ i) y) ^ (((m+1:ℕ):ℝ)))
                ^ (1/((m+1:ℕ):ℝ)) := by
          simp_rw [hEton]
    _ = ∏ i : Fin (m + 2),
          (∫⁻ y : Fin (m+1) → ℝ, (g i y) ^ (((m+1:ℕ):ℝ))) ^ (1/((m+1:ℕ):ℝ)) := by
          conv_rhs => rw [Fin.prod_univ_succ]

/-- The `ℝ≥0∞`-valued Loomis–Whitney inequality, for all `m ≥ 1`. -/
lemma lw_lintegral (m : ℕ) (hm : 1 ≤ m) (g : Fin (m + 1) → (Fin m → ℝ) → ℝ≥0∞)
    (hg : ∀ i, Measurable (g i)) :
    ∫⁻ x : Fin (m + 1) → ℝ, ∏ i : Fin (m + 1), g i (fun j : Fin m => x (Fin.succAbove i j))
      ≤ ∏ i : Fin (m + 1),
          (∫⁻ y : Fin m → ℝ, (g i y) ^ ((m : ℕ) : ℝ)) ^ (1 / ((m : ℕ) : ℝ)) := by
  have key : ∀ m, 1 ≤ m → LWStatement m := by
    intro m
    induction m with
    | zero => intro h; omega
    | succ m ih =>
      intro hm
      rcases Nat.eq_zero_or_pos m with rfl | hm'
      · exact lw_base
      · exact lw_step m hm' (ih hm')
  exact key m hm g hg

open MeasureTheory in
/-- The Loomis–Whitney inequality (Lieb's sharp form): for `m ≥ 1` and nonnegative
`f i : ℝ^m → ℝ`,
`∫_{ℝ^{m+1}} Π_i f_i(x̂_i) ≤ Π_i ‖f_i‖_{L^m}`, where `x̂_i` deletes the `i`-th
coordinate (`fun j => x (Fin.succAbove i j)`).  The case `m = 1` is Fubini. -/
theorem loomis_whitney (m : ℕ) (hm : 1 ≤ m) {f : Fin (m + 1) → (Fin m → ℝ) → ℝ}
    (hf : ∀ i y, 0 ≤ f i y)
    (hint : ∀ i, Integrable (fun y : Fin m → ℝ => (f i y) ^ ((m : ℕ) : ℝ)) volume)
    (hprod : Integrable (fun x : Fin (m + 1) → ℝ =>
      ∏ i : Fin (m + 1), f i (fun j : Fin m => x (Fin.succAbove i j))) volume) :
    (∫ x : Fin (m + 1) → ℝ, ∏ i : Fin (m + 1), f i (fun j : Fin m => x (Fin.succAbove i j)))
      ≤ ∏ i : Fin (m + 1),
          (∫ y : Fin m → ℝ, (f i y) ^ (((m : ℕ) : ℝ))) ^ (1 / (((m : ℕ) : ℝ))) := by
  have hMpos : (0:ℝ) < ((m:ℕ):ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hMne : ((m:ℕ):ℝ) ≠ 0 := hMpos.ne'
  have hcpos : (0:ℝ) < 1/((m:ℕ):ℝ) := by positivity
  have hcnonneg : (0:ℝ) ≤ 1/((m:ℕ):ℝ) := hcpos.le
  -- `ENNReal.ofReal ∘ f i` is ae-measurable
  have hGae : ∀ i, AEMeasurable (fun y : Fin m → ℝ => ENNReal.ofReal (f i y)) volume := by
    intro i
    have hMae : AEMeasurable (fun y : Fin m → ℝ => (f i y) ^ (((m:ℕ):ℝ))) volume :=
      (hint i).aestronglyMeasurable.aemeasurable
    let F' : (Fin m → ℝ) → ℝ := hMae.mk (fun y : Fin m → ℝ => (f i y) ^ (((m:ℕ):ℝ)))
    have hF'meas : Measurable F' := hMae.measurable_mk
    have hF'eq : (fun y : Fin m → ℝ => (f i y) ^ (((m:ℕ):ℝ))) =ᵐ[volume] F' := hMae.ae_eq_mk
    have hfeq : ∀ y : Fin m → ℝ, ((f i y) ^ (((m:ℕ):ℝ))) ^ (1/(((m:ℕ):ℝ))) = f i y := by
      intro y; rw [← Real.rpow_mul (hf i y), mul_one_div, div_self hMne, Real.rpow_one]
    have h2 : (fun y : Fin m → ℝ => ENNReal.ofReal (F' y ^ (1/((m:ℕ):ℝ)))) =ᵐ[volume]
        (fun y : Fin m → ℝ => ENNReal.ofReal (f i y)) := by
      filter_upwards [hF'eq] with y hy
      rw [← hfeq y, hy]
    have hm : Measurable (fun y : Fin m → ℝ => ENNReal.ofReal (F' y ^ (1/((m:ℕ):ℝ)))) :=
      (ENNReal.continuous_ofReal.comp (Real.continuous_rpow_const hcnonneg)).measurable.comp hF'meas
    exact hm.aemeasurable.congr h2
  let G' : Fin (m+1) → (Fin m → ℝ) → ℝ≥0∞ :=
    fun i => (hGae i).mk (fun y => ENNReal.ofReal (f i y))
  have hG'meas : ∀ i, Measurable (G' i) := fun i => (hGae i).measurable_mk
  have hG'eq : ∀ i, (fun y : Fin m → ℝ => ENNReal.ofReal (f i y)) =ᵐ[volume] G' i :=
    fun i => (hGae i).ae_eq_mk
  -- the LW inequality for `G'`
  have hLW := lw_lintegral m hm G' hG'meas
  -- quasi-measure-preservation of the projections
  have hπ : ∀ i : Fin (m+1), Measure.QuasiMeasurePreserving
      (fun x : Fin (m+1) → ℝ => (fun j : Fin m => x (Fin.succAbove i j))) volume volume := by
    intro i
    have h1 : Measure.QuasiMeasurePreserving
        (⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m+1) => ℝ) i)) volume
        (volume.prod volume) :=
      (volume_preserving_piFinSuccAbove (fun _ : Fin (m+1) => ℝ) i).quasiMeasurePreserving
    have h2 : Measure.QuasiMeasurePreserving Prod.snd (volume.prod volume)
        (volume : Measure (Fin m → ℝ)) :=
      (@Measure.quasiMeasurePreserving_snd ℝ (Fin m → ℝ) _ _ (volume : Measure ℝ)
        (volume : Measure (Fin m → ℝ)) _)
    have h3 := h2.comp h1
    have hfun : (Prod.snd ∘ ⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m+1) => ℝ) i))
        = (fun x : Fin (m+1) → ℝ => (fun j : Fin m => x (Fin.succAbove i j))) := by
      funext x
      simp only [Function.comp_apply, MeasurableEquiv.piFinSuccAbove_apply]
      rfl
    rwa [hfun] at h3
  -- transfer the RHS
  have hRHS : ∀ i : Fin (m+1), (∫⁻ y : Fin m → ℝ, (G' i y) ^ (((m:ℕ):ℝ)))
      = ∫⁻ y : Fin m → ℝ, ENNReal.ofReal ((f i y) ^ (((m:ℕ):ℝ))) := by
    intro i
    refine lintegral_congr_ae ?_
    filter_upwards [hG'eq i] with y hy
    rw [← hy, ENNReal.ofReal_rpow_of_nonneg (hf i y) (le_of_lt hMpos)]
  -- transfer the LHS
  have hLHS : (∫⁻ x : Fin (m+1) → ℝ, ∏ i : Fin (m+1), G' i (fun j : Fin m => x (Fin.succAbove i j)))
      = ∫⁻ x : Fin (m+1) → ℝ,
          ∏ i : Fin (m+1), ENNReal.ofReal (f i (fun j : Fin m => x (Fin.succAbove i j))) := by
    refine lintegral_congr_ae ?_
    filter_upwards [(Filter.eventually_all).2 (fun i => (hπ i).ae_eq_comp (hG'eq i).symm)] with x hx
    simp only [Function.comp_apply] at hx
    exact Finset.prod_congr rfl (fun i _ => hx i)
  have hLHS2 : (∫⁻ x : Fin (m+1) → ℝ,
        ∏ i : Fin (m+1), ENNReal.ofReal (f i (fun j : Fin m => x (Fin.succAbove i j))))
      = ∫⁻ x : Fin (m+1) → ℝ,
          ENNReal.ofReal (∏ i : Fin (m+1), f i (fun j : Fin m => x (Fin.succAbove i j))) := by
    refine lintegral_congr fun x => ?_
    rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => hf i _)]
  -- the `ℝ≥0∞` inequality for `ofReal ∘ f`
  have hLHSall : (∫⁻ x : Fin (m+1) → ℝ, ∏ i : Fin (m+1), G' i (fun j : Fin m => x (Fin.succAbove i j)))
      = ∫⁻ x : Fin (m+1) → ℝ,
          ENNReal.ofReal (∏ i : Fin (m+1), f i (fun j : Fin m => x (Fin.succAbove i j))) :=
    hLHS.trans hLHS2
  have hLW2 : (∫⁻ x : Fin (m+1) → ℝ,
        ENNReal.ofReal (∏ i : Fin (m+1), f i (fun j : Fin m => x (Fin.succAbove i j))))
      ≤ ∏ i : Fin (m+1),
          (∫⁻ y : Fin m → ℝ, ENNReal.ofReal ((f i y) ^ (((m:ℕ):ℝ)))) ^ (1/((m:ℕ):ℝ)) := by
    rw [← hLHSall]
    refine hLW.trans (le_of_eq ?_)
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [hRHS i]
  -- identify the lintegrals with the Bochner integrals
  have hlin_i : ∀ i : Fin (m+1),
      (∫⁻ y : Fin m → ℝ, ENNReal.ofReal ((f i y) ^ (((m:ℕ):ℝ))))
        = ENNReal.ofReal (∫ y : Fin m → ℝ, (f i y) ^ (((m:ℕ):ℝ))) :=
    fun i => (MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hint i)
      (ae_of_all _ (fun y => Real.rpow_nonneg (hf i y) _))).symm
  have hlin_p : (∫⁻ x : Fin (m+1) → ℝ,
        ENNReal.ofReal (∏ i : Fin (m+1), f i (fun j : Fin m => x (Fin.succAbove i j))))
      = ENNReal.ofReal (∫ x : Fin (m+1) → ℝ,
          ∏ i : Fin (m+1), f i (fun j : Fin m => x (Fin.succAbove i j))) :=
    (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hprod
      (ae_of_all _ (fun x => Finset.prod_nonneg (fun i _ => hf i _)))).symm
  have hLW3 : ENNReal.ofReal (∫ x : Fin (m+1) → ℝ,
        ∏ i : Fin (m+1), f i (fun j : Fin m => x (Fin.succAbove i j)))
      ≤ ∏ i : Fin (m+1),
          (ENNReal.ofReal (∫ y : Fin m → ℝ, (f i y) ^ (((m:ℕ):ℝ)))) ^ (1/((m:ℕ):ℝ)) := by
    rw [← hlin_p]
    refine hLW2.trans (le_of_eq ?_)
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [hlin_i i]
  -- finiteness
  have hfin : (∏ i : Fin (m+1),
        (ENNReal.ofReal (∫ y : Fin m → ℝ, (f i y) ^ (((m:ℕ):ℝ)))) ^ (1/((m:ℕ):ℝ))) < ⊤ :=
    ENNReal.prod_lt_top (fun i _ => ENNReal.rpow_lt_top_of_nonneg hcnonneg ENNReal.ofReal_lt_top.ne)
  -- convert to reals
  have hleft : (ENNReal.ofReal (∫ x : Fin (m+1) → ℝ,
        ∏ i : Fin (m+1), f i (fun j : Fin m => x (Fin.succAbove i j)))).toReal
      = ∫ x : Fin (m+1) → ℝ, ∏ i : Fin (m+1), f i (fun j : Fin m => x (Fin.succAbove i j)) :=
    ENNReal.toReal_ofReal (integral_nonneg (f := fun x : Fin (m+1) → ℝ =>
      ∏ i : Fin (m+1), f i (fun j : Fin m => x (Fin.succAbove i j)))
      (fun x => Finset.prod_nonneg (fun i _ => hf i _)))
  have hright : (∏ i : Fin (m+1),
        (ENNReal.ofReal (∫ y : Fin m → ℝ, (f i y) ^ (((m:ℕ):ℝ)))) ^ (1/((m:ℕ):ℝ))).toReal
      = ∏ i : Fin (m+1),
          (∫ y : Fin m → ℝ, (f i y) ^ (((m:ℕ):ℝ))) ^ (1/((m:ℕ):ℝ)) := by
    rw [ENNReal.toReal_prod]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [← ENNReal.toReal_rpow, ENNReal.toReal_ofReal
      (integral_nonneg (fun y => Real.rpow_nonneg (hf i y) _))]
  have hmain := ENNReal.toReal_mono hfin.ne hLW3
  rw [hleft, hright] at hmain
  exact hmain

end

end Commons.Analysis.Inequalities