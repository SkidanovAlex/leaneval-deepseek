import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.PotCubicLowBandAux.atomPairG
import Submission.Work.BoseBoxFock.PotCubicLowBandAux.spectralNPlusSqLe
import Submission.Work.BoseBoxFock.aPCPairAlg
import Submission.Work.BoseBoxFock.bessel_honest
import Submission.Work.BoseBoxFock.cnPlusC_boxRestrictC_eq_cnPlus
import Submission.Work.BoseBoxFock.re_boxSlotSum_boxT0_le_cnPlusC
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PotCubicLowBandAux.windowCGAux`

The **second-moment `n₊`-window** of the cubic low band: for a state `Θ = boxRestrictC ℓ Φ`
whose `n₊`-spectrum lies in `[0, 𝓜]` (the all-moments hypothesis `hmom`), the quadratic form of
the *square* of the model excited-number operator `S = dΓ(boxT0)` is bounded by `𝓜` times the box
excited count `cnPlusC ℓ Θ`.

The mathematical content is the operator inequality `S² ≤ 𝓜 n₊` on the window.  Both operators are
slot sums, `S = Σ_j (A_j − P_j)` and `n₊ = Σ_j (1 − P_j)`, where

* `A_j = slotProj1 e j` is the projection of slot `j` onto the span of the modes,
* `P_j = aPC ℓ j` is the projection of slot `j` onto the constants (`e 0`),

so `n₊ = S + D` with `D = Σ_j (1 − A_j) ≥ 0`; the two operators commute (their slot-wise pieces
do), whence `S² ≤ n₊²`, and the window `⟨n₊²⟩ ≤ 𝓜⟨n₊⟩` (`spectralNPlusSqLe`) finishes.

Everything is developed at the honest (measurable, everywhere bounded, box supported) mode/state
bundle, using the weak-bundle slot algebra of `Submission/Work/MB/`.
-/


/-
PROOF RECIPE for `nCfSecondMomentLe` (delegated: the second-moment slot comparison).

With `A_j := slotProj1 e j`, `P_j := aPC ℓ j` (both acting on the state `Θ`), put
`Pi j x := A_j Θ x − P_j Θ x`, `E j x := Θ x − A_j Θ x`, `v j x := Θ x − P_j Θ x`, so that
`u = ∑ j, Pi j` and `nCf ℓ Θ = ∑ j, v j` pointwise, and `v j = Pi j + E j` pointwise.

1. `∫_S‖∑v‖² − ∫_S‖∑Pi‖² = ∫_S [2 Re (conj (∑Pi) · ∑E) + ‖∑E‖²]` by the pointwise
   identity `normSq_add_sub_normSq` (`∑j v j = ∑j Pi j + ∑j E j` via `Finset.sum_add_distrib`).
2. `∫_S ‖∑E‖² ≥ 0`.
3. `Re ∫_S conj (∑Pi) · ∑E ≥ 0`: expand `= ∑_k ∑_l ∫_S conj (Pi k) · E l` and prove each
   term's real part is `≥ 0`:
   * `k = l`: `∫_S conj (Pi k) · E k = ∫_S conj (A_k (v k)) · (E k) = ∫_S conj (v k) · (A_k (E k))`
     (`slotProj1_box_adjoint`) and `A_k (E k) = A_k Θ − A_k (A_k Θ) = 0` (idempotence,
     `Work.MB.slotProj1_idem_weak`).
   * `k ≠ l`: `∫_S conj (Pi k) · E l = ∫_S conj (Pi k) · (E l (Pi k))`, because
     `E l Θ = E l (Pi k) + E l (Θ − Pi k)` and the second summand pairs to zero:
     `E l (Θ − Pi k) = (1 − Pi_k) (E l Θ)` (commutation of `E_l` with `Π_k`, from
     `Work.MB.slotProj_comp_weak` and `aPC_slotProj1_comm_ne`) and `(1 − Π_k) Π_k = 0`.
     Finally `∫_S conj (Pi k) · (E l (Pi k)) ≥ 0` because `E l = 1 − A_l` is a positive
     operator on `L²(S)`: `∫_S conj w · (E l w) = ‖w‖²_{L²(S)} − ‖A_l w‖²_{L²(S)} ≥ 0`
     (`slotProj1_box_adjoint` + idempotence + Cauchy–Schwarz).
4. Combine.

-/

namespace Work.BoseBoxFock.PotCubicLowBandAux

open MeasureTheory
open scoped BigOperators

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 0. Elementary box facts -/

/-- The slot update of a box configuration with a cube element stays in the box. -/
lemma update_mem_abox {N : ℕ} {ℓ : ℝ} (j : Fin N) {x : Submission.BoseGases.X N} {z : E3}
    (hx : x ∈ Submission.BoseGases.abox N ℓ) (hz : z ∈ Submission.BoseGases.acube ℓ) :
    Function.update x j z ∈ Submission.BoseGases.abox N ℓ := by
  rw [Submission.BoseGases.mem_abox_iff] at hx ⊢
  intro i
  rcases eq_or_ne i j with h | h
  · rw [h, Function.update_self]; exact hz
  · rw [Function.update_of_ne h]; exact hx i

/-- The weak "box power" of `Submission/Work/MB/` is the configuration box. -/
lemma boxPow_eq_abox {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) :
    Work.MB.boxPow N ℓ = Submission.BoseGases.abox N ℓ := by
  ext x
  rw [Work.MB.boxPow, Set.mem_univ_pi, Work.BoseBoxFock.boxL_eq_acube hℓ,
    Submission.BoseGases.mem_abox_iff]

/-- The mode kernel vanishes outside the cube. -/
lemma PV_eq_zero_of_notMem_acube {m : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {e : Fin m → E3 → ℂ}
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    {a y : E3} (hy : y ∉ Submission.BoseGases.acube ℓ) : Work.BoseBoxFock.PV e a y = 0 := by
  refine Work.BoseBoxFock.PV_eq_zero_of_notMem_boxL hsupp ?_
  rwa [Work.BoseBoxFock.boxL_eq_acube hℓ]

/-- An indicator never increases an everywhere bound. -/
lemma norm_indicator_le_bound {α : Type*} {s : Set α} {f : α → ℂ} {C : ℝ}
    (h : ∀ x, ‖f x‖ ≤ C) : ∀ x, ‖s.indicator f x‖ ≤ C := by
  intro x
  by_cases hx : x ∈ s
  · rw [Set.indicator_of_mem hx]; exact h x
  · rw [Set.indicator_of_notMem hx, norm_zero]; exact le_trans (norm_nonneg _) (h x)

/-! ## 1. Locality of the slot projection -/

/-- **Locality.**  On the box, the slot projection `A_j = slotProj1 e j` does not see
modifications of its argument off the box: `A_j (1_abox · g) = A_j g` on `abox`. -/
theorem slotProj1_indicator_abox {m N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {e : Fin m → E3 → ℂ}
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (j : Fin N) (g : Submission.BoseGases.X N → ℂ) :
    ∀ x ∈ Submission.BoseGases.abox N ℓ,
      Work.BoseBoxFock.slotProj1 e j (Set.indicator (Submission.BoseGases.abox N ℓ) g) x
        = Work.BoseBoxFock.slotProj1 e j g x := by
  intro x hx
  rw [Work.BoseBoxFock.slotProj1, Work.BoseBoxFock.slotProj1]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
  show Work.BoseBoxFock.PV e (x j) z * (Submission.BoseGases.abox N ℓ).indicator g
      (Function.update x j z)
    = Work.BoseBoxFock.PV e (x j) z * g (Function.update x j z)
  by_cases hz : z ∈ Submission.BoseGases.acube ℓ
  · rw [Set.indicator_of_mem (update_mem_abox j hx hz)]
  · rw [PV_eq_zero_of_notMem_acube hℓ hsupp hz, zero_mul, zero_mul]

/-! ## 2. Box self-adjointness of the slot projection -/

/-- **Box self-adjointness of `A_j = slotProj1 e j`.**  For measurable bounded `f, g`,

    `∫_abox (star (A_j f)) g = ∫_abox (star f) (A_j g)`.

The existing weak-bundle adjointness `Work.MB.slotProj_adjoint_bdd` covers the case where *both*
states are supported in the box; the general case is reduced to it by the locality of `A_j`
(`slotProj1_indicator_abox`). -/
theorem slotProj1_box_adjoint {m N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {e : Fin m → E3 → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (j : Fin N) {f g : Submission.BoseGases.X N → ℂ}
    (hfm : Measurable f) (hfb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C)
    (hgm : Measurable g) (hgb : ∃ C : ℝ, ∀ x, ‖g x‖ ≤ C) :
    (∫ x in Submission.BoseGases.abox N ℓ,
        star (Work.BoseBoxFock.slotProj1 e j f x) * g x)
      = ∫ x in Submission.BoseGases.abox N ℓ,
        star (f x) * Work.BoseBoxFock.slotProj1 e j g x := by
  classical
  obtain ⟨Cf, hCf⟩ := hfb
  obtain ⟨Cg, hCg⟩ := hgb
  have hCf0 : 0 ≤ Cf := le_trans (norm_nonneg (f 0)) (hCf 0)
  have hCg0 : 0 ≤ Cg := le_trans (norm_nonneg (g 0)) (hCg 0)
  set S := Submission.BoseGases.abox N ℓ with hS
  have hSmeas : MeasurableSet S := Submission.BoseGases.abox_measurable N ℓ
  have hsp : Function.support (S.indicator f) ⊆ Work.MB.boxPow N ℓ := by
    rw [boxPow_eq_abox hℓ]; exact Set.support_indicator_subset
  have hsp' : Function.support (S.indicator g) ⊆ Work.MB.boxPow N ℓ := by
    rw [boxPow_eq_abox hℓ]; exact Set.support_indicator_subset
  -- the weak-bundle adjointness, at the two box-supported states
  have hadj : (∫ x, star (Work.BoseBoxFock.slotProj1 e j (S.indicator f) x)
        * S.indicator g x)
      = ∫ x, star (S.indicator f x) * Work.BoseBoxFock.slotProj1 e j (S.indicator g) x := by
    have h := (Work.MB.slotProj_adjoint_bdd hmeas hbdd hsupp) {j}
      (S.indicator f) (S.indicator g)
      (hfm.indicator hSmeas) ⟨Cf, norm_indicator_le_bound hCf⟩ hsp
      (hgm.indicator hSmeas) ⟨Cg, norm_indicator_le_bound hCg⟩ hsp'
    simpa only [Work.BoseBoxFock.slotProj_singleton_eq_slotProj1_aux] using h
  -- the two locality rewrites, as box integrals
  have hlocf : (∫ x in S, star (Work.BoseBoxFock.slotProj1 e j f x) * g x)
      = ∫ x in S, star (Work.BoseBoxFock.slotProj1 e j (S.indicator f) x) * g x :=
    MeasureTheory.setIntegral_congr_fun hSmeas (fun x hx => by
      rw [slotProj1_indicator_abox hℓ hsupp j f x hx])
  have hlocg : (∫ x in S, star (f x) * Work.BoseBoxFock.slotProj1 e j g x)
      = ∫ x in S, star (f x) * Work.BoseBoxFock.slotProj1 e j (S.indicator g) x :=
    MeasureTheory.setIntegral_congr_fun hSmeas (fun x hx => by
      rw [slotProj1_indicator_abox hℓ hsupp j g x hx])
  -- the two sides as whole-space integrals against the indicators
  have e1 : (∫ x in S, star (Work.BoseBoxFock.slotProj1 e j f x) * g x)
      = ∫ x, star (Work.BoseBoxFock.slotProj1 e j (S.indicator f) x) * S.indicator g x := by
    rw [hlocf]
    rw [← MeasureTheory.integral_indicator (μ := (MeasureTheory.volume :
      MeasureTheory.Measure (Submission.BoseGases.X N))) hSmeas
      (f := fun x => star (Work.BoseBoxFock.slotProj1 e j (S.indicator f) x) * g x)]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    show S.indicator (fun x => star (Work.BoseBoxFock.slotProj1 e j (S.indicator f) x) * g x) x
      = star (Work.BoseBoxFock.slotProj1 e j (S.indicator f) x) * S.indicator g x
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, mul_zero]
  have e2 : (∫ x in S, star (f x) * Work.BoseBoxFock.slotProj1 e j (S.indicator g) x)
      = ∫ x, star (S.indicator f x) * Work.BoseBoxFock.slotProj1 e j (S.indicator g) x := by
    rw [← MeasureTheory.integral_indicator (μ := (MeasureTheory.volume :
      MeasureTheory.Measure (Submission.BoseGases.X N))) hSmeas
      (f := fun x => star (f x) * Work.BoseBoxFock.slotProj1 e j (S.indicator g) x)]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    show S.indicator (fun x => star (f x)
        * Work.BoseBoxFock.slotProj1 e j (S.indicator g) x) x
      = star (S.indicator f x) * Work.BoseBoxFock.slotProj1 e j (S.indicator g) x
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, star_zero, zero_mul]
  rw [hlocg, e1, e2, hadj]

/-! ## 3. Integrability of bounded functions on the box -/

/-- Measurable everywhere bounded functions are integrable on the (finite measure) box. -/
lemma integrableOn_of_bounded_abox {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {F : Submission.BoseGases.X N → ℂ}
    (hFm : AEStronglyMeasurable F
      (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N)))
    {C : ℝ} (hC : ∀ x, ‖F x‖ ≤ C) :
    MeasureTheory.IntegrableOn F (Submission.BoseGases.abox N ℓ) := by
  haveI : IsFiniteMeasure
      ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N)).restrict
        (Submission.BoseGases.abox N ℓ)) :=
    ⟨by rw [MeasureTheory.Measure.restrict_apply_univ]
        exact Submission.BoseGases.abox_lt_top N ℓ hℓ.le⟩
  exact ((MeasureTheory.memLp_top_of_bound hFm C (Filter.Eventually.of_forall hC)).mono_measure
    MeasureTheory.Measure.restrict_le_self).integrable le_top

/-! ## 4. Box self-adjointness of the condensate slot mean -/

/-- **Box self-adjointness of `P_j = aPC ℓ j`.** -/
theorem aPC_box_adjoint {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (j : Fin N)
    {f g : Submission.BoseGases.X N → ℂ}
    (hfm : Measurable f) (hfb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C)
    (hgm : Measurable g) (hgb : ∃ C : ℝ, ∀ x, ‖g x‖ ≤ C) :
    (∫ x in Submission.BoseGases.abox N ℓ,
        star (Work.BoseBoxFock.aPC ℓ j f x) * g x)
      = ∫ x in Submission.BoseGases.abox N ℓ,
        star (f x) * Work.BoseBoxFock.aPC ℓ j g x := by
  obtain ⟨Cf, hCf⟩ := hfb
  obtain ⟨Cg, hCg⟩ := hgb
  have hCf0 : 0 ≤ Cf := le_trans (norm_nonneg (f 0)) (hCf 0)
  have hCg0 : 0 ≤ Cg := le_trans (norm_nonneg (g 0)) (hCg 0)
  have hfstar : Measurable (fun y => star (f y)) := continuous_star.measurable.comp hfm
  have hCfs : ∀ x, ‖(fun y => star (f y)) x‖ ≤ Cf := fun x => by
    rw [norm_star]; exact hCf x
  have hI1 : MeasureTheory.IntegrableOn
      (fun x => Work.BoseBoxFock.aPC ℓ j (fun y => star (f y)) x * g x)
      (Submission.BoseGases.abox N ℓ) :=
    integrableOn_of_bounded_abox hℓ
      ((Work.BoseBoxFock.aPC_aesm_full ℓ j hfstar.aestronglyMeasurable).mul
        hgm.aestronglyMeasurable)
      (C := Cf * Cg) (fun x => by
        rw [norm_mul]
        exact mul_le_mul (Work.BoseBoxFock.norm_aPC_le hℓ j hCf0 hCfs x) (hCg x) (norm_nonneg _)
          (le_trans (norm_nonneg _) (Work.BoseBoxFock.norm_aPC_le hℓ j hCf0 hCfs x)))
  have hI2 : MeasureTheory.IntegrableOn
      (fun x => star (f x) * Work.BoseBoxFock.aPC ℓ j g x)
      (Submission.BoseGases.abox N ℓ) :=
    integrableOn_of_bounded_abox hℓ
      (hfstar.aestronglyMeasurable.mul
        (Work.BoseBoxFock.aPC_aesm_full ℓ j hgm.aestronglyMeasurable))
      (C := Cf * Cg) (fun x => by
        rw [norm_mul, norm_star]
        exact mul_le_mul (hCf x) (Work.BoseBoxFock.norm_aPC_le hℓ j hCg0 hCg x)
          (norm_nonneg _) (le_trans (norm_nonneg _) (hCf x)))
  have hcongr : (fun x => star (Work.BoseBoxFock.aPC ℓ j f x) * g x)
      = fun x => Work.BoseBoxFock.aPC ℓ j (fun y => star (f y)) x * g x := by
    funext x
    exact congrArg (fun z => z * g x)
      (congrFun (Work.BoseBoxFock.aPC_conj ℓ j f) x).symm
  rw [hcongr]
  exact Work.BoseBoxFock.aPC_sym_box j hI1 hI2

/-! ## 5. Locality of the slot operators, in general form -/

/-- On the box, the slot projection `A_j` only sees the values of its argument on the box. -/
theorem slotProj1_equiv_on_box {m N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {e : Fin m → E3 → ℂ}
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (j : Fin N) {h h' : Submission.BoseGases.X N → ℂ}
    (heq : ∀ y ∈ Submission.BoseGases.abox N ℓ, h y = h' y) :
    ∀ x ∈ Submission.BoseGases.abox N ℓ,
      Work.BoseBoxFock.slotProj1 e j h x = Work.BoseBoxFock.slotProj1 e j h' x := by
  intro x hx
  rw [Work.BoseBoxFock.slotProj1, Work.BoseBoxFock.slotProj1]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
  show Work.BoseBoxFock.PV e (x j) z * h (Function.update x j z)
    = Work.BoseBoxFock.PV e (x j) z * h' (Function.update x j z)
  by_cases hz : z ∈ Submission.BoseGases.acube ℓ
  · rw [heq _ (update_mem_abox j hx hz)]
  · rw [PV_eq_zero_of_notMem_acube hℓ hsupp hz, zero_mul, zero_mul]

/-- On the box, the slot mean `P_j` only sees the values of its argument on the box. -/
theorem aPC_equiv_on_box {N : ℕ} {ℓ : ℝ} (j : Fin N)
    {h h' : Submission.BoseGases.X N → ℂ}
    (heq : ∀ y ∈ Submission.BoseGases.abox N ℓ, h y = h' y) :
    ∀ x ∈ Submission.BoseGases.abox N ℓ,
      Work.BoseBoxFock.aPC ℓ j h x = Work.BoseBoxFock.aPC ℓ j h' x := by
  intro x hx
  show ((1 / ℓ ^ 3 : ℝ) : ℂ) * _ = ((1 / ℓ ^ 3 : ℝ) : ℂ) * _
  congr 1
  exact MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.acube_measurable ℓ)
    (fun z hz => heq _ (update_mem_abox j hx hz))

/-! ## 6. The excited-count function and elementary algebra -/

/-- The complex excited-count function `n₊Θ = Σ_j (Θ − aPC_j Θ)`. -/
noncomputable def nCf (ℓ : ℝ) {N : ℕ} (Θ : Submission.BoseGases.X N → ℂ) :
    Submission.BoseGases.X N → ℂ :=
  fun x => ∑ j : Fin N, (Θ x - Work.BoseBoxFock.aPC ℓ j Θ x)

/-- Algebraic identity: `‖u + d‖² − ‖u‖² = 2 Re (conj u · d) + ‖d‖²` for complex numbers. -/
lemma normSq_add_sub_normSq (u d : ℂ) :
    ‖u + d‖ ^ 2 - ‖u‖ ^ 2 = 2 * (star u * d).re + ‖d‖ ^ 2 := by
  rw [Work.BoseBoxFock.sq_norm_eq_re_sq_add_im_sq (u + d),
    Work.BoseBoxFock.sq_norm_eq_re_sq_add_im_sq u,
    Work.BoseBoxFock.sq_norm_eq_re_sq_add_im_sq d]
  simp only [Complex.add_re, Complex.add_im, Complex.star_def, Complex.mul_re,
    Complex.conj_re, Complex.conj_im]
  ring

/-- A bounded measurable product is integrable on the box. -/
lemma integrableOn_star_mul_bdd {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {f g : Submission.BoseGases.X N → ℂ}
    (hfm : AEStronglyMeasurable f
      (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N)))
    (hfb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C)
    (hgm : AEStronglyMeasurable g
      (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N)))
    (hgb : ∃ C : ℝ, ∀ x, ‖g x‖ ≤ C) :
    MeasureTheory.Integrable (fun x => star (f x) * g x)
      ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N)).restrict
        (Submission.BoseGases.abox N ℓ)) := by
  obtain ⟨Cf, hCf⟩ := hfb
  obtain ⟨Cg, hCg⟩ := hgb
  refine integrableOn_of_bounded_abox hℓ ?_ (C := Cf * Cg) (fun x => ?_)
  · exact (continuous_star.comp_aestronglyMeasurable hfm).mul hgm
  · rw [norm_mul, norm_star]
    exact mul_le_mul (hCf x) (hCg x) (norm_nonneg _) (le_trans (norm_nonneg _) (hCf x))


end Work.BoseBoxFock.PotCubicLowBandAux
