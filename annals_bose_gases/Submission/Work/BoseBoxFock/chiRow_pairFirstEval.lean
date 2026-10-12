import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.chiRowDict
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.chiRow_pairFirstEval`

The first orientation of the `χ`-row of the first-quantised box word:

    `(cIPn n Ψ (B (A Ψ))).re = pairHalfOne n ℓ (chiW ℓ N) Φ`,   `Ψ = boxRestrictC ℓ Φ`,

where `A = boxSlotSum e (rankOnePair C (evec0 m))` is the `χ`-mode slot sum and
`B = boxSlotSum e (rankOne (evec0 m))` is the condensate slot sum.

The proof is a dictionary chain of a.e. (on the box) steps:

* `A Ψ =ᵐ ∑_j chiMode(x_j)·aPC_j Ψ` (`chiRow_chiMode_dict`), and on the box
  `aPC_j Ψ = aP_j Φ` (`chiRow_aPC_dict`), so `A Ψ =ᵐ S` with
  `S x = ∑_j chiMode(x_j)·(aP_j Φ x : ℂ)`;
* `B` is the sum of the slot operators of the *pinned* vector `e 0` (`chiRow_slotSum_expand_weak`
  at the coordinate vector plus `boxSlotOf_evec0_eq_uSlot`), whose slot operators equal the slot
  means `aPC` on the box (`uSlot_ae_eq_aPC_aux`), so `B (A Ψ) =ᵐ ∑_j aPC_j S`;
* the box-relative a.e. congruence of `aPC` (`aPC_congr_ae_box`, generalised here) transfers the
  state;
* on the box `Re aPC_j S = aP_j G` with `G y = ∑_k chiW(y_k)·aP_k Φ y`, because
  `Re chiMode = chiW` on the cube (`chiMode_re_of_theta_eq_one`); taking real parts of the
  `cIPn` pairing produces exactly `pairHalfOne`.

The only measure theory needed beyond the dictionary is the a.e. equality of `S` with its
pinned representative `S' x = ∑_j √ℓ³·η_C(x_j)·(aP_j Φ x : ℂ)` (a consequence of the pin
`√ℓ³·η_C =ᵐ chiMode`), which makes the slices of `S` integrable via `qmp_update_Xn_aux`.

Everything here is `sorry`-free.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

local notation "Sp" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

/-! ## 1. Reusable helpers -/

/-- The complex box restriction of a **continuous** state is measurable. -/
lemma chiRowEval_boxRestrictC_measurable {n : ℕ} (ℓ : ℝ) {Φ : Submission.BoseGases.X n → ℝ}
    (hΦc : Continuous Φ) : Measurable (boxRestrictC ℓ Φ) := by
  have h : boxRestrictC ℓ Φ = fun x : Submission.BoseGases.X n =>
      ((Φ x : ℝ) : ℂ) *
        (((Submission.BoseGases.abox n ℓ).indicator (fun _ => (1 : ℝ)) x : ℝ) : ℂ) := rfl
  rw [h]
  exact (Complex.continuous_ofReal.measurable.comp hΦc.measurable).mul
    (Complex.continuous_ofReal.measurable.comp
      (measurable_const.indicator (Submission.BoseGases.abox_measurable n ℓ)))

/-- The complex box restriction of a continuous state is globally bounded. -/
lemma chiRowEval_boxRestrictC_bound {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Submission.BoseGases.X n, ‖boxRestrictC ℓ Φ x‖ ≤ C := by
  obtain ⟨C, hC⟩ := (Submission.BoseGases.abox_compact n hℓ).exists_bound_of_continuousOn
    hΦc.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  rw [show boxRestrictC ℓ Φ x = ((Φ x : ℝ) : ℂ) *
      (((Submission.BoseGases.abox n ℓ).indicator (fun _ => (1 : ℝ)) x : ℝ) : ℂ) from rfl]
  by_cases hx : x ∈ Submission.BoseGases.abox n ℓ
  · rw [Set.indicator_of_mem hx]
    simp only [Complex.ofReal_one, mul_one, Complex.norm_real]
    exact (hC x hx).trans (le_max_left _ _)
  · rw [Set.indicator_of_notMem hx]
    simp

/-- The complex box restriction of a state is supported in the box. -/
lemma chiRowEval_boxRestrictC_support {n : ℕ} (ℓ : ℝ) (Φ : Submission.BoseGases.X n → ℝ) :
    Function.support (boxRestrictC ℓ Φ) ⊆ Submission.BoseGases.abox n ℓ := by
  intro x hx
  by_contra h
  exact hx (by
    rw [show boxRestrictC ℓ Φ x = ((Φ x : ℝ) : ℂ) *
      (((Submission.BoseGases.abox n ℓ).indicator (fun _ => (1 : ℝ)) x : ℝ) : ℂ) from rfl]
    rw [Set.indicator_of_notMem h]
    simp)

/-- The real part of a Bochner integral over a set is the integral of the real parts. -/
lemma chiRowEval_integral_re_set {n : ℕ} (s : Set (Submission.BoseGases.X n))
    (f : Submission.BoseGases.X n → ℂ) (hf : IntegrableOn f s volume) :
    (∫ x in s, f x).re = ∫ x in s, (f x).re := by
  have h := integral_re (𝕜 := ℂ)
    (μ := (volume : Measure (Submission.BoseGases.X n)).restrict s) (f := f) hf
  simpa using h.symm

/-- **The `cIPn` pairing against the box restriction is a real integral over the box.** -/
lemma chiRowEval_cIPn_re {n : ℕ} {ℓ : ℝ} {Φ : Submission.BoseGases.X n → ℝ}
    {G : Submission.BoseGases.X n → ℂ}
    (hG : IntegrableOn (fun x => (((Φ x : ℝ)) : ℂ) * G x) (Submission.BoseGases.abox n ℓ)) :
    (Work.BoseDict.cIPn n (boxRestrictC ℓ Φ) G).re
      = ∫ x in Submission.BoseGases.abox n ℓ, Φ x * (G x).re := by
  have hpt : ∀ x : Submission.BoseGases.X n,
      (starRingEnd ℂ) (boxRestrictC ℓ Φ x) * G x
        = (Submission.BoseGases.abox n ℓ).indicator
            (fun x => (((Φ x : ℝ)) : ℂ) * G x) x := by
    intro x
    rw [show boxRestrictC ℓ Φ x = ((Φ x : ℝ) : ℂ) *
        (((Submission.BoseGases.abox n ℓ).indicator (fun _ => (1 : ℝ)) x : ℝ) : ℂ) from rfl]
    by_cases hx : x ∈ Submission.BoseGases.abox n ℓ
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
      simp
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
      simp
  rw [Work.BoseDict.cIPn,
    show (∫ x, (starRingEnd ℂ) (boxRestrictC ℓ Φ x) * G x)
        = ∫ x, (Submission.BoseGases.abox n ℓ).indicator
            (fun x => (((Φ x : ℝ)) : ℂ) * G x) x from
      integral_congr_ae (Filter.Eventually.of_forall hpt),
    MeasureTheory.integral_indicator (Submission.BoseGases.abox_measurable n ℓ),
    chiRowEval_integral_re_set (Submission.BoseGases.abox n ℓ) _ hG]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  simp [Complex.mul_re]

/-- **The box-relative a.e. congruence of `aPC`**, for an arbitrary number of slots. -/
lemma chiRowEval_aPC_congr_abox {N : ℕ} {ℓ : ℝ} (i : Fin N)
    {f g : Submission.BoseGases.X N → ℂ}
    (h : f =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)] g) :
    aPC ℓ i f =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)] aPC ℓ i g := by
  cases N with
  | zero => exact i.elim0
  | succ k => exact aPC_congr_ae_box (ℓ := ℓ) i h

/-- **The box-relative a.e. congruence of the real slot mean `aP`.** -/
lemma chiRowEval_aP_congr_abox {N : ℕ} {ℓ : ℝ} (i : Fin N)
    {F G : Submission.BoseGases.X N → ℝ}
    (h : F =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)] G) :
    Submission.BoseGases.aP ℓ i F
      =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)]
      Submission.BoseGases.aP ℓ i G := by
  have h' : (fun x => ((F x : ℝ) : ℂ))
      =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)]
      (fun x => ((G x : ℝ) : ℂ)) :=
    h.mono (fun x hx => by show ((F x : ℝ) : ℂ) = ((G x : ℝ) : ℂ); rw [hx])
  have h2 := chiRowEval_aPC_congr_abox (ℓ := ℓ) i h'
  filter_upwards [h2] with x hx
  have h1 : ((Submission.BoseGases.aP ℓ i F x : ℝ) : ℂ)
      = ((Submission.BoseGases.aP ℓ i G x : ℝ) : ℂ) := by
    rw [← aPC_ofReal ℓ i F x, ← aPC_ofReal ℓ i G x]
    exact hx
  exact Complex.ofReal_injective h1

/-- **On the box, the sum of the `uSlot`s of a fixed one-particle vector is the sum of the
slot means.** -/
lemma chiRowEval_uSlot_sum_ae {d : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {u : Sp → ℂ} {c : ℂ}
    (huc : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure Sp),
      u z = c * Work.BoseK15.corpusBox.thetaFun ℓ z)
    (hcc : (starRingEnd ℂ) c * c = (ℓ ^ 3)⁻¹) (Θ : Submission.BoseGases.X d → ℂ) :
    (fun x => ∑ j : Fin d, uSlot u j Θ x)
      =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox d ℓ)]
      (fun x => ∑ j : Fin d, aPC ℓ j Θ x) := by
  filter_upwards [Filter.eventually_all.mpr
    (fun j : Fin d => uSlot_ae_eq_aPC_aux hℓ j huc hcc (Θ := Θ))] with x hx
  exact Finset.sum_congr rfl (fun j _ => hx j)

/-- **The real slot mean of a continuous state is bounded on the box by the sup-norm of the
state on the box.** -/
lemma chiRowEval_aP_abs_le_abox {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (k : Fin n)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ) {CΦ : ℝ} (hCΦ0 : 0 ≤ CΦ)
    (hCΦ : ∀ z ∈ Submission.BoseGases.abox n ℓ, |Φ z| ≤ CΦ)
    {z : Submission.BoseGases.X n} (hz : z ∈ Submission.BoseGases.abox n ℓ) :
    |Submission.BoseGases.aP ℓ k Φ z| ≤ CΦ := by
  have hae : ∀ᵐ y ∂((MeasureTheory.volume : MeasureTheory.Measure Sp).restrict
      (Submission.BoseGases.acube ℓ)), ‖Φ (Function.update z k y)‖ ≤ CΦ := by
    filter_upwards [self_mem_ae_restrict (Submission.BoseGases.acube_measurable ℓ)] with y hy
    rw [Real.norm_eq_abs]
    exact hCΦ _ (Submission.BoseGases.update_mem_abox k hz hy)
  have hb := norm_integral_le_of_norm_le_const
    (μ := (MeasureTheory.volume : MeasureTheory.Measure Sp).restrict
      (Submission.BoseGases.acube ℓ))
    (f := fun y : Sp => Φ (Function.update z k y)) hae
  have hreal : ((MeasureTheory.volume : MeasureTheory.Measure Sp).restrict
      (Submission.BoseGases.acube ℓ)).real Set.univ = ℓ ^ 3 := by
    rw [Measure.real, Measure.restrict_apply_univ,
      Submission.BoseGases.acube_volume ℓ hℓ.le,
      ENNReal.toReal_ofReal (by positivity)]
  rw [hreal] at hb
  have hval : Submission.BoseGases.aP ℓ k Φ z
      = (1 / ℓ ^ 3) * ∫ y in Submission.BoseGases.acube ℓ, Φ (Function.update z k y) := rfl
  rw [hval, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / ℓ ^ 3)]
  calc (1 / ℓ ^ 3) * |∫ y in Submission.BoseGases.acube ℓ, Φ (Function.update z k y)|
      = (1 / ℓ ^ 3) * ‖∫ y in Submission.BoseGases.acube ℓ,
          Φ (Function.update z k y)‖ := by rw [Real.norm_eq_abs]
    _ ≤ (1 / ℓ ^ 3) * (CΦ * ℓ ^ 3) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = CΦ := by field_simp

/-! ## 2. The main theorem -/

theorem chiRow_pairFirstEval {n m : ℕ} [NeZero m] {ℓ : ℝ} (hℓ : 0 < ℓ) {N : ℕ}
    {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hpin : e 0 =ᵐ[MeasureTheory.volume] fun z =>
      ((Real.sqrt (ℓ ^ 3))⁻¹ : ℂ) * Work.BoseK15.corpusBox.thetaFun ℓ z)
    (hmeas : ∀ l, Measurable (e l)) (hemem : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    {C : Fin m → ℝ} (hC : (fun z => ((Real.sqrt (ℓ ^ 3) : ℝ) : ℂ) * Work.BoseDict.etaOf e C z)
      =ᵐ[MeasureTheory.volume] Work.BoseBoxFock.chiMode ℓ N)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ) :
    (Work.BoseDict.cIPn n (Work.BoseBoxFock.boxRestrictC ℓ Φ)
        (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.rankOne (Work.BoseBoxFock.evec0 m))
          (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.rankOnePair C (Work.BoseBoxFock.evec0 m))
            (Work.BoseBoxFock.boxRestrictC ℓ Φ)))).re
      = Work.BoseBoxFock.pairHalfOne n ℓ (Work.BoseBoxFock.chiW ℓ N) Φ := by
  classical
  -- ## 0. Notation
  set Ψ : Submission.BoseGases.X n → ℂ := boxRestrictC ℓ Φ with hΨ
  set Θ₁ : Submission.BoseGases.X n → ℂ :=
    Work.BoseDict.boxSlotSum e (rankOnePair C (evec0 m)) Ψ with hΘ₁
  set Θ₂ : Submission.BoseGases.X n → ℂ :=
    Work.BoseDict.boxSlotSum e (rankOne (evec0 m)) Θ₁ with hΘ₂
  set S : Submission.BoseGases.X n → ℂ := fun x =>
    ∑ k : Fin n, chiMode ℓ N (x k) * ((Submission.BoseGases.aP ℓ k Φ x : ℝ) : ℂ) with hS
  set S' : Submission.BoseGases.X n → ℂ := fun x =>
    ∑ k : Fin n, ((Real.sqrt (ℓ ^ 3) : ℝ) : ℂ) * Work.BoseDict.etaOf e C (x k) *
      ((Submission.BoseGases.aP ℓ k Φ x : ℝ) : ℂ) with hS'
  set G : Submission.BoseGases.X n → ℝ := fun y =>
    ∑ k : Fin n, chiW ℓ N (y k) * Submission.BoseGases.aP ℓ k Φ y with hG
  -- ## 1. Basic facts
  have hΨm : Measurable Ψ := by rw [hΨ]; exact chiRowEval_boxRestrictC_measurable ℓ hΦc
  obtain ⟨CΨ, hCΨ0, hCΨ⟩ := chiRowEval_boxRestrictC_bound hℓ hΦc
  have hΨb : ∃ D : ℝ, ∀ x, ‖Ψ x‖ ≤ D := ⟨CΨ, fun x => by rw [hΨ]; exact hCΨ x⟩
  obtain ⟨hΘ₁m, hΘ₁b⟩ := Work.MB.boxSlotSum_measurable_bounded_ae hmeas hbdd hsupp
    (rankOnePair C (evec0 m)) Ψ hΨm hΨb
  obtain ⟨hΘ₂m, hΘ₂b⟩ := Work.MB.boxSlotSum_measurable_bounded_ae hmeas hbdd hsupp
    (rankOne (evec0 m)) Θ₁ hΘ₁m hΘ₁b
  obtain ⟨CΘ₂, hCΘ₂⟩ := hΘ₂b
  obtain ⟨CΦ, hCΦ⟩ := (Submission.BoseGases.abox_compact n hℓ).exists_bound_of_continuousOn
    (f := Φ) hΦc.continuousOn
  have hCΦ0 : 0 ≤ max CΦ 0 := le_max_right _ _
  have hCΦabs : ∀ z ∈ Submission.BoseGases.abox n ℓ, |Φ z| ≤ max CΦ 0 :=
    fun z hz => (hCΦ z hz).trans (le_max_left _ _)
  obtain ⟨BE, hBE0, hBEbd⟩ := Work.MB.etaOf_weak_bound (e := e) (w := C) hbdd
  have hS'm : Measurable S' := by
    rw [hS']
    refine Finset.measurable_sum _ (fun k _ => ?_)
    refine (measurable_const.mul ?_).mul ?_
    · exact (Work.MB.etaOf_weak_measurable hmeas C).comp (measurable_pi_apply k)
    · exact Complex.continuous_ofReal.measurable.comp
        (Submission.BoseGases.aP_continuous hℓ k hΦc).measurable
  -- ## 2. `S` vs. the pinned representative `S'`
  have hcoordG : ∀ k : Fin n,
      ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)),
        ((Real.sqrt (ℓ ^ 3) : ℝ) : ℂ) * Work.BoseDict.etaOf e C (x k) = chiMode ℓ N (x k) := by
    intro k
    filter_upwards [(Measure.quasiMeasurePreserving_eval
      (μ := fun _ : Fin n => (MeasureTheory.volume : MeasureTheory.Measure Sp)) k).ae_eq_comp hC]
      with x hx
    exact hx
  have hSS' : S =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n))] S' := by
    have hsu := (Finset.eventually_all Finset.univ).mpr (fun k _ => hcoordG k)
    filter_upwards [hsu] with x hx
    rw [hS, hS']
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [← hx k (Finset.mem_univ k)]
  -- ## 3. The inner (`χ`-mode) row: `Θ₁ =ᵐ S`
  have hinner := chiRow_chiMode_dict (m := m) (d := n) (N := N) hℓ hpin hmeas hbdd hsupp hC
    Ψ hΨm hΨb
  have hrow2 := (chiRow_aPC_dict (n := n) (ℓ := ℓ) hℓ).2.1
  have hT1S : (fun x : Submission.BoseGases.X n =>
        ∑ j : Fin n, chiMode ℓ N (x j) * aPC ℓ j Ψ x)
      =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)] S := by
    filter_upwards [MeasureTheory.self_mem_ae_restrict
      (Submission.BoseGases.abox_measurable n ℓ)] with x hx
    rw [hS]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hrow2 j Φ x hx]
  have hinnerS : Θ₁ =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)] S :=
    hinner.trans hT1S
  -- ## 4. The outer (condensate) row: `Θ₂ =ᵐ ∑_j aPC_j S`
  have huc : e 0 =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure Sp)]
      (fun z : Sp => ((Real.sqrt (ℓ ^ 3))⁻¹ : ℂ) * Work.BoseK15.corpusBox.thetaFun ℓ z) := hpin
  have huSlot : Θ₂ =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)]
      (fun x => ∑ j : Fin n, uSlot (e 0) j Θ₁ x) := by
    rw [hΘ₂, rankOne_eq_rankOnePair]
    rw [chiRow_slotSum_expand_weak hmeas hbdd hsupp (evec0 m) (evec0 m) Θ₁ hΘ₁m hΘ₁b]
    exact Filter.Eventually.of_forall (fun x => by
      rw [Finset.sum_apply]
      exact Finset.sum_congr rfl (fun j _ => congrFun (boxSlotOf_evec0_eq_uSlot e j Θ₁) x))
  have huSlotPC : (fun x => ∑ j : Fin n, uSlot (e 0) j Θ₁ x)
      =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)]
      (fun x => ∑ j : Fin n, aPC ℓ j Θ₁ x) :=
    chiRowEval_uSlot_sum_ae hℓ huc (conj_inv_sqrt_mul_self hℓ) Θ₁
  have hPCcong : (fun x => ∑ j : Fin n, aPC ℓ j Θ₁ x)
      =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)]
      (fun x => ∑ j : Fin n, aPC ℓ j S x) := by
    have hsu := (Finset.eventually_all Finset.univ).mpr
      (fun j _ => chiRowEval_aPC_congr_abox (ℓ := ℓ) j hinnerS)
    filter_upwards [hsu] with x hx
    exact Finset.sum_congr rfl (fun j _ => hx j (Finset.mem_univ j))
  have hΘ₂ae : Θ₂ =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)]
      (fun x => ∑ j : Fin n, aPC ℓ j S x) := huSlot.trans (huSlotPC.trans hPCcong)
  -- ## 5. Slice integrability of `S`
  have hsliceEq : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)),
      ∀ j : Fin n, ∀ᵐ y ∂(MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ)),
        S (Function.update x j y) = S' (Function.update x j y) := by
    have hprod : ∀ᵐ p ∂(MeasureTheory.volume :
        MeasureTheory.Measure (Submission.BoseGases.X n × Sp)),
        ∀ j : Fin n, S (Function.update p.1 j p.2) = S' (Function.update p.1 j p.2) := by
      filter_upwards [(Finset.eventually_all Finset.univ).mpr
        (fun j _ => (qmp_update_Xn_aux j).ae_eq_comp hSS')] with p hp
      intro j
      exact hp j (Finset.mem_univ j)
    have hiter : ∀ᵐ x ∂(MeasureTheory.volume :
        MeasureTheory.Measure (Submission.BoseGases.X n)),
        ∀ᵐ y ∂(MeasureTheory.volume : MeasureTheory.Measure Sp),
          ∀ j : Fin n, S (Function.update x j y) = S' (Function.update x j y) :=
      Measure.ae_ae_of_ae_prod hprod
    have h1 : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)),
        ∀ᵐ y ∂(MeasureTheory.volume : MeasureTheory.Measure Sp),
          ∀ j : Fin n, S (Function.update x j y) = S' (Function.update x j y) :=
      MeasureTheory.ae_mono Measure.restrict_le_self hiter
    filter_upwards [h1] with x hx
    intro j
    filter_upwards [MeasureTheory.ae_mono Measure.restrict_le_self hx] with y hy
    exact hy j
  have hS'slice : ∀ (x : Submission.BoseGases.X n), x ∈ Submission.BoseGases.abox n ℓ →
      ∀ j : Fin n, IntegrableOn (fun y : Sp => S' (Function.update x j y))
        (Submission.BoseGases.acube ℓ) := by
    intro x hx j
    refine IntegrableOn.of_bound (Submission.BoseGases.acube_lt_top ℓ hℓ.le) ?_
      ((n : ℝ) * (Real.sqrt (ℓ ^ 3) * (BE * max CΦ 0))) ?_
    · exact ((hS'm.comp (measurable_update x (a := j))).aestronglyMeasurable).restrict
    · filter_upwards [self_mem_ae_restrict (Submission.BoseGases.acube_measurable ℓ)] with y hy
      rw [hS']
      refine (norm_sum_le _ _).trans ?_
      have hterm : ∀ k : Fin n,
          ‖((Real.sqrt (ℓ ^ 3) : ℝ) : ℂ) * Work.BoseDict.etaOf e C (Function.update x j y k) *
              ((Submission.BoseGases.aP ℓ k Φ (Function.update x j y) : ℝ) : ℂ)‖
            ≤ Real.sqrt (ℓ ^ 3) * (BE * max CΦ 0) := by
        intro k
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
          Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg (ℓ ^ 3)), mul_assoc]
        refine mul_le_mul_of_nonneg_left
          (mul_le_mul (hBEbd _) ?_ (abs_nonneg _) hBE0) (Real.sqrt_nonneg _)
        exact chiRowEval_aP_abs_le_abox (CΦ := max CΦ 0) hℓ k hΦc hCΦ0 hCΦabs
          (Submission.BoseGases.update_mem_abox j hx hy)
      calc ∑ k : Fin n, ‖((Real.sqrt (ℓ ^ 3) : ℝ) : ℂ) * Work.BoseDict.etaOf e C
              (Function.update x j y k) *
              ((Submission.BoseGases.aP ℓ k Φ (Function.update x j y) : ℝ) : ℂ)‖
          ≤ ∑ _k : Fin n, Real.sqrt (ℓ ^ 3) * (BE * max CΦ 0) :=
            Finset.sum_le_sum (fun k _ => hterm k)
        _ = (n : ℝ) * (Real.sqrt (ℓ ^ 3) * (BE * max CΦ 0)) := by
            rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  have hsliceInt : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)),
      ∀ j : Fin n, IntegrableOn (fun y : Sp => S (Function.update x j y))
        (Submission.BoseGases.acube ℓ) := by
    filter_upwards [hsliceEq, MeasureTheory.self_mem_ae_restrict
      (Submission.BoseGases.abox_measurable n ℓ)] with x hsx hx
    intro j
    exact (hS'slice x hx j).congr_fun_ae (Filter.EventuallyEq.symm (hsx j))
  -- ## 6. The pointwise real evaluation on the box
  have hSre : ∀ y ∈ Submission.BoseGases.abox n ℓ, (S y).re = G y := by
    intro y hy
    rw [hS, hG, Complex.re_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
      chiMode_re_of_theta_eq_one ℓ N ((chiRow_aP_abox_facts hℓ).2.1 hy k)]
  have hRe : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)),
      (∑ j : Fin n, aPC ℓ j S x).re = ∑ j : Fin n, Submission.BoseGases.aP ℓ j G x := by
    filter_upwards [hsliceInt, MeasureTheory.self_mem_ae_restrict
      (Submission.BoseGases.abox_measurable n ℓ)] with x hslice hx
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [aPC_re ℓ j S x (hslice j)]
    exact (chiRow_aP_abox_facts hℓ).2.2 j (fun y hy => hSre y hy) x hx
  -- ## 7. Integrability of the `cIPn` integrand
  have hInt : IntegrableOn (fun x : Submission.BoseGases.X n => (((Φ x : ℝ)) : ℂ) * Θ₂ x)
      (Submission.BoseGases.abox n ℓ) := by
    refine IntegrableOn.of_bound (Submission.BoseGases.abox_lt_top n ℓ hℓ.le) ?_
      (max CΦ 0 * max CΘ₂ 0) ?_
    · exact ((Complex.continuous_ofReal.measurable.comp hΦc.measurable).aestronglyMeasurable.mul
        hΘ₂m.aestronglyMeasurable).restrict
    · filter_upwards [self_mem_ae_restrict (Submission.BoseGases.abox_measurable n ℓ)] with x hx
      rw [norm_mul, Complex.norm_real]
      exact mul_le_mul ((hCΦ x hx).trans (le_max_left _ _))
        ((hCΘ₂ x).trans (le_max_left _ _)) (norm_nonneg _) hCΦ0
  -- ## 8. The definitional identity for `pairHalfOne`
  have hpair : pairHalfOne n ℓ (chiW ℓ N) Φ
      = ∫ x in Submission.BoseGases.abox n ℓ, Φ x *
          (∑ j : Fin n, Submission.BoseGases.aP ℓ j G x) := by
    unfold pairHalfOne
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    simp only [Finset.sum_apply]
    rw [hG]
  -- ## 9. Assembly
  calc (Work.BoseDict.cIPn n Ψ Θ₂).re
      = ∫ x in Submission.BoseGases.abox n ℓ, Φ x * (Θ₂ x).re := by
        rw [hΨ]
        exact chiRowEval_cIPn_re hInt
    _ = ∫ x in Submission.BoseGases.abox n ℓ, Φ x * ((∑ j : Fin n, aPC ℓ j S x)).re := by
        refine integral_congr_ae ?_
        filter_upwards [hΘ₂ae] with x hx
        rw [hx]
    _ = ∫ x in Submission.BoseGases.abox n ℓ, Φ x *
          (∑ j : Fin n, Submission.BoseGases.aP ℓ j G x) := by
        refine integral_congr_ae ?_
        filter_upwards [hRe] with x hx
        rw [hx]
    _ = pairHalfOne n ℓ (chiW ℓ N) Φ := hpair.symm

end Work.BoseBoxFock
