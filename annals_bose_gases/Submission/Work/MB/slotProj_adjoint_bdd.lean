import Mathlib.CategoryTheory.Countable
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.MB.SlotWeakBase
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.MB

open MeasureTheory

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 0. The `L¹` inputs: integrability of the two slot kernels for weak data

The strong module `Work.BoseBoxFock.slotProj_adjoint` reduces the adjointness identity to the
integrability of the two kernels `slotKernelG` and `slotKernelH`, the measure preserving swap
`slotSwapMeas` and the pointwise kernel symmetry `slotKernel_swap_pointwise`.  All of the latter
are hypothesis-free; only the integrability has to be redone for weak (measurable, everywhere
bounded, box supported) modes and states.

* `slotKernelG_integrable_bdd` — `slotKernelG e S Φ Ψ` is the product of the bounded measurable
  factor `star (Φ ·)`, the `S`-fold product of the bounded measurable kernels `PV e` and the
  bounded measurable factor `Ψ ∘ updateFinset`; it vanishes as soon as the configuration leaves
  the state box (where `Φ` vanishes) or a fibre coordinate leaves `boxL ℓ` (where the
  corresponding `PV`-factor vanishes).  Hence it is supported in
  `boxPow n ℓ ×ˢ Set.univ.pi (fun _ : ↥S => boxL ℓ)`, a set of finite measure.
* `slotKernelH_integrable_bdd` — `slotKernelH` is `slotKernelG` transported along the measure
  preserving swap `slotSwapMeas S`. -/

/-- The right-hand slot kernel is integrable for weak modes and weak states. -/
theorem slotKernelG_integrable_bdd {m n : ℕ} {ℓ : ℝ} {e : Fin m → E3 → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (S : Finset (Fin n)) {Φ Ψ : (Fin n → E3) → ℂ}
    (hΦm : Measurable Φ) (hΦb : ∃ C, ∀ x, ‖Φ x‖ ≤ C)
    (hΦsupp : Function.support Φ ⊆ boxPow n ℓ)
    (hΨm : Measurable Ψ) (hΨb : ∃ C, ∀ x, ‖Ψ x‖ ≤ C) :
    Integrable (Work.BoseBoxFock.slotKernelG e S Φ Ψ)
      (volume : Measure ((Fin n → E3) × ({i : Fin n // i ∈ S} → E3))) := by
  classical
  -- the support set: the state box times the box to the power of the projected slots
  set B : Set E3 := Work.BoseK15.corpusBox.boxL ℓ with hB
  have hBmeas : MeasurableSet B := hB ▸ Work.BoseK15.corpusBox.boxL_measurableSet ℓ
  have hBfin : (volume : Measure E3) B ≠ ⊤ :=
    hB ▸ (Work.BoseK15.corpusBox.boxL_compact ℓ).measure_lt_top.ne
  set Z : Set ({i : Fin n // i ∈ S} → E3) := Set.univ.pi (fun _ => B) with hZ
  have hZmeas : MeasurableSet Z := by
    rw [hZ]
    exact MeasurableSet.pi Set.countable_univ (fun _ _ => hBmeas)
  have hZfin : (volume : Measure ({i : Fin n // i ∈ S} → E3)) Z ≠ ⊤ := by
    rw [hZ]
    show (Measure.pi (fun _ : {i : Fin n // i ∈ S} => (volume : Measure E3)))
      (Set.univ.pi (fun _ : {i : Fin n // i ∈ S} => B)) ≠ ⊤
    rw [Measure.pi_pi]
    exact ENNReal.prod_ne_top (fun i _ => hBfin)
  have hSmeas : MeasurableSet (boxPow n ℓ ×ˢ Z) := (measurableSet_boxPow n ℓ).prod hZmeas
  have hSfin : (volume : Measure ((Fin n → E3) × ({i : Fin n // i ∈ S} → E3)))
      (boxPow n ℓ ×ˢ Z) ≠ ⊤ := by
    rw [Measure.volume_eq_prod (Fin n → E3) ({i : Fin n // i ∈ S} → E3), Measure.prod_prod]
    exact ENNReal.mul_ne_top (volume_boxPow_lt_top n ℓ) hZfin
  -- measurability
  have hGmeas : Measurable (Work.BoseBoxFock.slotKernelG e S Φ Ψ) := by
    have hfac : ∀ i : {i : Fin n // i ∈ S},
        Measurable (fun p : (Fin n → E3) × ({i : Fin n // i ∈ S} → E3) =>
          Work.BoseBoxFock.PV e (p.1 i.1) (p.2 i)) := by
      intro i
      simp only [Work.BoseBoxFock.PV]
      exact Finset.measurable_sum Finset.univ (fun l _ =>
        ((hmeas l).comp ((measurable_pi_apply i.1).comp measurable_fst)).mul
          (continuous_star.measurable.comp
            ((hmeas l).comp ((measurable_pi_apply i).comp measurable_snd))))
    have hP : Measurable (fun p : (Fin n → E3) × ({i : Fin n // i ∈ S} → E3) =>
        ∏ i : {i : Fin n // i ∈ S}, Work.BoseBoxFock.PV e (p.1 i.1) (p.2 i)) :=
      Finset.measurable_prod Finset.univ (fun i _ => hfac i)
    exact ((continuous_star.measurable.comp (hΦm.comp measurable_fst)).mul hP).mul
      (hΨm.comp (Work.BoseBoxFock.measurable_updateFinset_pair S))
  -- an everywhere bound
  choose Bl hBl using hbdd
  have hBl0 : ∀ l, 0 ≤ Bl l := fun l => (norm_nonneg (e l 0)).trans (hBl l 0)
  set K : ℝ := ∑ l : Fin m, Bl l * Bl l with hKdef
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun l _ => mul_nonneg (hBl0 l) (hBl0 l)
  obtain ⟨CΦ, hCΦ⟩ := hΦb
  obtain ⟨CΨ, hCΨ⟩ := hΨb
  refine integrable_of_bdd_of_support hSmeas hSfin hGmeas.aestronglyMeasurable
    (C := max CΦ 0 * K ^ (Fintype.card {i : Fin n // i ∈ S}) * max CΨ 0) ?_ ?_
  · intro p
    have hPV : ∀ i : {i : Fin n // i ∈ S},
        ‖Work.BoseBoxFock.PV e (p.1 i.1) (p.2 i)‖ ≤ K := by
      intro i
      calc ‖Work.BoseBoxFock.PV e (p.1 i.1) (p.2 i)‖
          = ‖∑ l : Fin m, e l (p.1 i.1) * star (e l (p.2 i))‖ := rfl
        _ ≤ ∑ l : Fin m, ‖e l (p.1 i.1) * star (e l (p.2 i))‖ := norm_sum_le _ _
        _ = ∑ l : Fin m, ‖e l (p.1 i.1)‖ * ‖e l (p.2 i)‖ := by
              refine Finset.sum_congr rfl fun l _ => ?_
              rw [norm_mul, norm_star]
        _ ≤ ∑ l : Fin m, Bl l * Bl l := Finset.sum_le_sum fun l _ =>
              mul_le_mul (hBl l _) (hBl l _) (norm_nonneg _) (hBl0 l)
        _ = K := hKdef.symm
    have hprod : (∏ i : {i : Fin n // i ∈ S},
        ‖Work.BoseBoxFock.PV e (p.1 i.1) (p.2 i)‖) ≤ K ^ (Fintype.card {i : Fin n // i ∈ S}) := by
      calc (∏ i : {i : Fin n // i ∈ S}, ‖Work.BoseBoxFock.PV e (p.1 i.1) (p.2 i)‖)
          ≤ ∏ _ : {i : Fin n // i ∈ S}, K :=
            Finset.prod_le_prod₀ (s := Finset.univ)
              (f := fun i : {i : Fin n // i ∈ S} =>
                ‖Work.BoseBoxFock.PV e (p.1 i.1) (p.2 i)‖)
              (g := fun _ : {i : Fin n // i ∈ S} => K)
              (fun i _ => norm_nonneg _) (fun i _ => hPV i)
        _ = K ^ (Fintype.card {i : Fin n // i ∈ S}) := by
            rw [Finset.prod_const, Finset.card_univ]
    simp only [Work.BoseBoxFock.slotKernelG, norm_mul, norm_star, norm_prod]
    exact mul_le_mul
      (mul_le_mul ((hCΦ _).trans (le_max_left CΦ 0)) hprod
        (Finset.prod_nonneg fun i _ => norm_nonneg _) (le_max_right CΦ 0))
      ((hCΨ _).trans (le_max_left CΨ 0)) (norm_nonneg _)
      (mul_nonneg (le_max_right CΦ 0) (pow_nonneg hK0 _))
  · intro p hp
    have hp2 : p.1 ∈ boxPow n ℓ → p.2 ∉ Z := fun h1 h2 =>
      hp (Set.mem_prod.mpr ⟨h1, h2⟩)
    by_cases h1 : p.1 ∈ boxPow n ℓ
    · have h2 : p.2 ∉ Z := hp2 h1
      rw [hZ, Set.mem_univ_pi] at h2
      obtain ⟨i, hi⟩ := not_forall.mp h2
      have hzero : Work.BoseBoxFock.PV e (p.1 i.1) (p.2 i) = 0 :=
        Work.BoseBoxFock.PV_eq_zero_of_notMem_boxL hsupp hi
      simp only [Work.BoseBoxFock.slotKernelG]
      rw [Finset.prod_eq_zero (Finset.mem_univ i) hzero, mul_zero, zero_mul]
    · have hex : ∃ j : Fin n, p.1 j ∉ Work.BoseK15.corpusBox.boxL ℓ := by
        have h := h1
        rw [boxPow, Set.mem_univ_pi] at h
        exact not_forall.mp h
      obtain ⟨j, hj⟩ := hex
      have hnot : p.1 ∉ Function.support Φ := fun hmem =>
        hj ((mem_boxPow_iff.mp (hΦsupp hmem)) j)
      have hΦ0 : Φ p.1 = 0 := Function.notMem_support.mp hnot
      simp only [Work.BoseBoxFock.slotKernelG]
      rw [hΦ0, star_zero, zero_mul, zero_mul]

/-- The left-hand slot kernel is integrable for weak modes and weak states: transport
`slotKernelG_integrable_bdd` along the measure preserving swap `slotSwapMeas S`. -/
theorem slotKernelH_integrable_bdd {m n : ℕ} {ℓ : ℝ} {e : Fin m → E3 → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (S : Finset (Fin n)) {Φ Ψ : (Fin n → E3) → ℂ}
    (hΦm : Measurable Φ) (hΦb : ∃ C, ∀ x, ‖Φ x‖ ≤ C)
    (hΦsupp : Function.support Φ ⊆ boxPow n ℓ)
    (hΨm : Measurable Ψ) (hΨb : ∃ C, ∀ x, ‖Ψ x‖ ≤ C) :
    Integrable (Work.BoseBoxFock.slotKernelH e S Φ Ψ)
      (volume : Measure ((Fin n → E3) × ({i : Fin n // i ∈ S} → E3))) :=
  (((Work.BoseBoxFock.measurePreserving_slotSwapMeas S).integrable_comp_emb
      (Work.BoseBoxFock.slotSwapMeas S).measurableEmbedding).mpr
    (slotKernelG_integrable_bdd hmeas hbdd hsupp S hΦm hΦb hΦsupp hΨm hΨb)).congr
    (Filter.Eventually.of_forall fun p =>
      Work.BoseBoxFock.slotKernel_swap_pointwise e S Φ Ψ p)

/-- **Self-adjointness of the slot projection `slotProj e T`, for weak (measurable, everywhere
bounded, box supported) modes and states.**

Both states `Φ, Ψ` are measurable, everywhere bounded and supported in the `n`-particle box
`Work.MB.boxPow n ℓ = (boxL ℓ)^n`; the modes `e l` are measurable, everywhere bounded and
supported in `Work.BoseK15.corpusBox.boxL ℓ`.

Mirror of `Work.BoseBoxFock.slotProj_adjoint` (`Submission/Work/BoseBoxFock/slotProj_adjoint.lean`),
which needs `Continuous`/`HasCompactSupport` for both states and both mode conditions; there the
hypotheses are used only for the integrability of the two kernels
`slotKernelG e S Φ Ψ p = star (Φ p.1) * (∏ i, PV e (p.1 i.1) (p.2 i)) * Ψ (updateFinset p.1 S p.2)`
and `slotKernelH` (the swapped one).  The *structural* part of the strong proof is
hypothesis-free and already available in that module:
`slotSwapMeas`/`slotSwapFun` and the measure-preserving swap (`measurePreserving_slotSwapMeas`),
`slotUpdateFinset_updateFinset`, `slotSwap_prod_PV`, `slotKernel_swap_pointwise` (the pointwise
identity `slotKernelG (swap p) = slotKernelH p`), and the two `integral_prod` rewrites
(`hstep1`, `hstep2`).  What the weak version has to redo is only the `Integrable` input: the
kernel `G` is measurable, everywhere bounded and supported in the set
`Work.MB.boxPow n ℓ × Set.univ.pi (fun _ : ↥T => Work.BoseK15.corpusBox.boxL ℓ)` of finite measure
(`Work.MB.volume_boxPow_lt_top`, `Work.MB.integrable_of_bdd_of_support`), and `H` is integrable by
transport along the measure-preserving swap.  No orthonormality (`horth`) and no `hint` are needed
(the identity is the kernel symmetry `Work.BoseBoxFock.star_PV_comm`). -/
theorem slotProj_adjoint_bdd {m n : ℕ} {ℓ : ℝ} {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ) :
    (∀ (T : Finset (Fin n)) (Φ Ψ : (Fin n → EuclideanSpace ℝ (Fin 3)) → ℂ), Measurable Φ →
        (∃ C, ∀ x, ‖Φ x‖ ≤ C) → Function.support Φ ⊆ Work.MB.boxPow n ℓ →
        Measurable Ψ → (∃ C, ∀ x, ‖Ψ x‖ ≤ C) → Function.support Ψ ⊆ Work.MB.boxPow n ℓ →
        (∫ x, star (Work.BoseBoxFock.slotProj e T Φ x) * Ψ x)
          = ∫ x, star (Φ x) * Work.BoseBoxFock.slotProj e T Ψ x) := by
  intro T Φ Ψ hΦm hΦb hΦsupp hΨm hΨb hΨsupp
  classical
  have hIntG := slotKernelG_integrable_bdd hmeas hbdd hsupp T hΦm hΦb hΦsupp hΨm hΨb
  have hIntH := slotKernelH_integrable_bdd hmeas hbdd hsupp T hΦm hΦb hΦsupp hΨm hΨb
  have hstep1 : (∫ x, star (Work.BoseBoxFock.slotProj e T Φ x) * Ψ x)
      = ∫ p, Work.BoseBoxFock.slotKernelH e T Φ Ψ p := by
    have h1 : (∫ x, star (Work.BoseBoxFock.slotProj e T Φ x) * Ψ x)
        = ∫ x, ∫ z : ({i : Fin n // i ∈ T} → E3),
            Work.BoseBoxFock.slotKernelH e T Φ Ψ (x, z) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [Work.BoseBoxFock.slotKernelH]
      rw [Work.BoseBoxFock.slotProj, Work.BoseBoxFock.slotStar_integral volume,
        ← integral_mul_const]
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      simp only [Function.updateFinset_def, star_mul]
      ring
    exact h1.trans (integral_prod (Work.BoseBoxFock.slotKernelH e T Φ Ψ) hIntH).symm
  have hstep2 : (∫ x, star (Φ x) * Work.BoseBoxFock.slotProj e T Ψ x)
      = ∫ p, Work.BoseBoxFock.slotKernelG e T Φ Ψ p := by
    have h1 : (∫ x, star (Φ x) * Work.BoseBoxFock.slotProj e T Ψ x)
        = ∫ x, ∫ z : ({i : Fin n // i ∈ T} → E3),
            Work.BoseBoxFock.slotKernelG e T Φ Ψ (x, z) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [Work.BoseBoxFock.slotKernelG]
      rw [Work.BoseBoxFock.slotProj, ← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      simp only [Function.updateFinset_def]
      ring
    exact h1.trans (integral_prod (Work.BoseBoxFock.slotKernelG e T Φ Ψ) hIntG).symm
  have hswap : (∫ p, Work.BoseBoxFock.slotKernelH e T Φ Ψ p)
      = ∫ p, Work.BoseBoxFock.slotKernelG e T Φ Ψ p :=
    (integral_congr_ae (Filter.Eventually.of_forall fun p =>
      (Work.BoseBoxFock.slotKernel_swap_pointwise e T Φ Ψ p).symm)).trans
      (MeasurePreserving.integral_comp (Work.BoseBoxFock.measurePreserving_slotSwapMeas T)
        (Work.BoseBoxFock.slotSwapMeas T).measurableEmbedding
        (Work.BoseBoxFock.slotKernelG e T Φ Ψ))
  exact hstep1.trans (hswap.trans hstep2.symm)

end Work.MB
