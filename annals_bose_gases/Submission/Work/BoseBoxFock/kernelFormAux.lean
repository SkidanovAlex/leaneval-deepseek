import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.PotPairRowsNormalForm
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.kernelFormAux` — the toolbox of the kernel form of the `Q₂` row

This module collects the generic facts used by the *kernel form* of the `Q₂` pair row
(`Submission/Work/BoseBoxFock/potPairRows_kernelForm.lean`): the row of
`Work.BoseBoxFock.potPairRows_cIPn_pinned_gen` has its mode sum `∑ₖ` **outside** the position
integrals, while the kernel form (the shape to which the frame/Poisson identity of the chapter
applies) has it **inside**, as the kernel
`∑ₖ cₖ·Fpₖ(x_{p.2})·conj(Fpₖ y)`.

The passage is the exchange of a *finite* sum with a *triple* iterated integral, together with the
integrability of the summands.  Everything here is stated for the threefold product measure
`volume ⊗ volume ⊗ volume` on `(Xn n × Ω) × Ω`, so that a *single* `Integrable` hypothesis per
summand (bounded, box-supported, jointly measurable) drives the whole Fubini chain
(`MeasureTheory.integral_prod` twice + `MeasureTheory.Integrable.integral_prod_left`).

Contents:

* `vXn`, `v3` — the `Xn n`-volume and the threefold product measure;
* `kernelFormAux_boxL_ne_top` — the corpus box has finite volume (⚠ renamed from
  `volume_boxL_lt_top` by the holder of `Work.BoseBoxFock.box_to_model` on 2026-10-10 to break the
  duplicate declaration with `qVecFrameWeighted.volume_boxL_lt_top`, which made the kinetic and
  potential cones of the target un-importable together — see
  `BLOCKER_kernelFormAux_qVecFrameWeighted.md`; name-only change, no statement touched);
* `measurable_update_update_snd` — the double coordinate update `(x, y, u) ↦ x[i↦y][j↦u]` is
  measurable;
* `ae_eval_volume_pi`, `ae_v3_snd`, `ae_v3_fst_snd`, `ae_v3_fst_fst_eval`, `ae_v2_snd`,
  `ae_v2_fst_eval` — a.e. statements pull back along the coordinate projections;
* `integrable_on_box3` — the `L¹` criterion at the fixed box product;
* `integrable_state_triple` — the canonical integrand `conj Θ(x)·α(x)·β(y)·γ(u)·Θ(x[i↦y][j↦u])` is
  integrable on the product space as soon as the factors are measurable and bounded and `Θ` is
  supported in the `n`-particle box;
* `sum_mul_iterated_triple_eq` — the finite-sum/triple-integral exchange;
* `integral_triple_congr_ae`, `integral_double_congr_ae`, `integral_triple_congr_of_forall` — the
  a.e./pointwise congruence of iterated integrals;
* `sum_mul_factor` — the elementary rearrangement `∑ₖ cₖ·(A·fₖ·D) = A·(∑ₖ cₖ·fₖ)·D`.

Everything here is `sorry`-free.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

local notation "Ω" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Work.BoseDict.Xn
local notation "boxL" => Work.BoseK15.corpusBox.boxL

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## 1. The measures -/

/-- `volume` on the `n`-particle configuration space `Xn n`, as an abbreviation (so that type
class search unfolds it). -/
abbrev vXn (n : ℕ) : Measure (Xn n) := (volume : Measure (Xn n))

/-- The threefold product measure `volume ⊗ volume ⊗ volume` on `(Xn n × Ω) × Ω`. -/
abbrev v3 (n : ℕ) : Measure ((Xn n × Ω) × Ω) :=
  ((vXn n).prod (volume : Measure Ω)).prod (volume : Measure Ω)

/-- The `n`-particle box has finite volume. -/
theorem kernelFormAux_boxL_ne_top (ℓ : ℝ) : (volume : Measure Ω) (boxL ℓ) ≠ ⊤ :=
  (Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox ℓ).measure_lt_top.ne

/-- The double box product (the support of the triple integrands) has finite volume. -/
theorem v3_box_lt_top (n : ℕ) (ℓ : ℝ) :
    v3 n ((Work.MB.boxPow n ℓ ×ˢ boxL ℓ) ×ˢ boxL ℓ) ≠ ⊤ := by
  rw [v3, MeasureTheory.Measure.prod_prod, MeasureTheory.Measure.prod_prod]
  exact ENNReal.mul_ne_top
    (ENNReal.mul_ne_top (Work.MB.volume_boxPow_lt_top n ℓ) (kernelFormAux_boxL_ne_top ℓ))
    (kernelFormAux_boxL_ne_top ℓ)

/-! ## 2. Measurability of the coordinate updates -/

/-- `a ↦ x[i ↦ a]` is measurable. -/
theorem kf_measurable_update_snd {n : ℕ} (i : Fin n) (x : Xn n) :
    Measurable (fun a : Ω => Function.update x i a) := by
  rw [measurable_pi_iff]
  intro m
  by_cases hmi : m = i
  · subst hmi
    simp only [Function.update_self]
    exact measurable_id
  · simp only [Function.update_of_ne hmi]
    exact measurable_const

/-- `(a, b) ↦ g a [j ↦ b]` is measurable for measurable `g`. -/
theorem kf_measurable_update_update {n : ℕ} (j : Fin n) {α : Type*} [MeasurableSpace α]
    {g : α → Xn n} (hg : Measurable g) :
    Measurable (fun p : α × Ω => Function.update (g p.1) j p.2) := by
  rw [measurable_pi_iff]
  intro m
  by_cases hmj : m = j
  · subst hmj
    simp only [Function.update_self]
    exact measurable_snd
  · simp only [Function.update_of_ne hmj]
    exact (measurable_pi_apply m).comp (hg.comp measurable_fst)

/-- `z ↦ z.1.1[i ↦ z.1.2][j ↦ z.2]` is measurable on the product space. -/
theorem kf_measurable_update_update_snd {n : ℕ} (i j : Fin n) :
    Measurable (fun z : (Xn n × Ω) × Ω =>
      Function.update (Function.update z.1.1 i z.1.2) j z.2) := by
  rw [measurable_pi_iff]
  intro m
  have hpt : ∀ z : (Xn n × Ω) × Ω,
      Function.update (Function.update z.1.1 i z.1.2) j z.2 m
        = if m = j then z.2 else if m = i then z.1.2 else z.1.1 m := by
    intro z
    simp only [Function.update_apply]
  simp only [hpt]
  split_ifs
  · exact measurable_snd
  · exact measurable_fst.snd
  · exact (measurable_pi_apply m).comp measurable_fst.fst

/-! ## 3. A.e. statements pull back along the coordinate projections -/

/-- A.e. statements about `Ω` pull back along a coordinate of the product `Xn N`. -/
theorem ae_eval_volume_pi {N : ℕ} (i : Fin N) {P : Ω → Prop}
    (h : ∀ᵐ a ∂(volume : Measure Ω), P a) :
    ∀ᵐ x ∂(volume : Measure (Xn N)), P (x i) := by
  rw [MeasureTheory.volume_pi]
  exact (Measure.quasiMeasurePreserving_eval (μ := fun _ : Fin N => (volume : Measure Ω)) i).ae h

/-- A.e. statements about `Ω` pull back along the second coordinate of the pair `Xn N × Ω`. -/
theorem ae_v2_snd {N : ℕ} {P : Ω → Prop} (h : ∀ᵐ a ∂(volume : Measure Ω), P a) :
    ∀ᵐ z ∂(vXn N).prod (volume : Measure Ω), P z.2 :=
  (Measure.quasiMeasurePreserving_snd (μ := vXn N) (ν := (volume : Measure Ω))).ae h

/-- A.e. statements about `Ω` pull back along a coordinate of the first factor of
`Xn N × Ω`. -/
theorem ae_v2_fst_eval {N : ℕ} (m : Fin N) {P : Ω → Prop}
    (h : ∀ᵐ a ∂(volume : Measure Ω), P a) :
    ∀ᵐ z ∂(vXn N).prod (volume : Measure Ω), P (z.1 m) :=
  (Measure.quasiMeasurePreserving_fst (μ := vXn N) (ν := (volume : Measure Ω))).ae
    (ae_eval_volume_pi m h)

/-- A.e. statements about `Ω` pull back along the last coordinate of `(Xn N × Ω) × Ω`. -/
theorem ae_v3_snd {N : ℕ} {P : Ω → Prop} (h : ∀ᵐ a ∂(volume : Measure Ω), P a) :
    ∀ᵐ z ∂v3 N, P z.2 :=
  (Measure.quasiMeasurePreserving_snd
    (μ := (vXn N).prod (volume : Measure Ω)) (ν := (volume : Measure Ω))).ae h

/-- A.e. statements about `Ω` pull back along the middle coordinate of `(Xn N × Ω) × Ω`. -/
theorem ae_v3_fst_snd {N : ℕ} {P : Ω → Prop} (h : ∀ᵐ a ∂(volume : Measure Ω), P a) :
    ∀ᵐ z ∂v3 N, P z.1.2 :=
  ((Measure.quasiMeasurePreserving_snd (μ := vXn N) (ν := (volume : Measure Ω))).comp
    (Measure.quasiMeasurePreserving_fst
      (μ := (vXn N).prod (volume : Measure Ω)) (ν := (volume : Measure Ω)))).ae h

/-- A.e. statements about `Ω` pull back along a coordinate of the first factor of
`(Xn N × Ω) × Ω`. -/
theorem ae_v3_fst_fst_eval {N : ℕ} (m : Fin N) {P : Ω → Prop}
    (h : ∀ᵐ a ∂(volume : Measure Ω), P a) :
    ∀ᵐ z ∂v3 N, P (z.1.1 m) :=
  ((Measure.quasiMeasurePreserving_fst (μ := vXn N) (ν := (volume : Measure Ω))).comp
    (Measure.quasiMeasurePreserving_fst
      (μ := (vXn N).prod (volume : Measure Ω)) (ν := (volume : Measure Ω)))).ae
    (ae_eval_volume_pi m h)

/-! ## 4. The `L¹` criterion at the fixed box product -/

/-- A measurable integrand which is everywhere bounded and vanishes off the box product is
integrable on the threefold product space. -/
theorem integrable_on_box3 {n : ℕ} {ℓ : ℝ} {f : (Xn n × Ω) × Ω → ℂ}
    (hfm : AEStronglyMeasurable f (v3 n)) {C : ℝ} (hC : ∀ z, ‖f z‖ ≤ C)
    (hsupp : ∀ z, z ∉ (Work.MB.boxPow n ℓ ×ˢ boxL ℓ) ×ˢ boxL ℓ → f z = 0) :
    Integrable f (v3 n) :=
  Work.MB.integrable_of_bdd_of_support
    (((Work.MB.measurableSet_boxPow n ℓ).prod (Work.BoseB4.BoxData.boxL_measurableSet _ ℓ)).prod
      (Work.BoseB4.BoxData.boxL_measurableSet _ ℓ))
    (v3_box_lt_top n ℓ) hfm hC hsupp

/-! ## 5. The canonical integrand: bounded factors times the box state -/

/-- **The canonical triple integrand is integrable on the product space.**  For measurable,
everywhere bounded `α`, `β`, `γ` and a measurable state `Θ` supported in the `n`-particle box
`boxPow n ℓ`, the function
`z ↦ conj Θ(z.1.1)·α(z.1.1)·β(z.1.2)·γ(z.2)·Θ(z.1.1[i↦z.1.2][j↦z.2])` is `L¹` for the threefold
product measure.  (For `i ≠ j` the state alone carries the support; the `conj Θ(x)` factor
carries the `x`-support.) -/
theorem integrable_state_triple {n : ℕ} {ℓ : ℝ} {Θ α : Xn n → ℂ} {β γ : Ω → ℂ} {i j : Fin n}
    (hij : i ≠ j) {Cα Cβ Cγ CΘ : ℝ}
    (hCα : 0 ≤ Cα) (hCβ : 0 ≤ Cβ) (hCγ : 0 ≤ Cγ) (hCΘ : 0 ≤ CΘ)
    (hαm : Measurable α) (hαb : ∀ x, ‖α x‖ ≤ Cα)
    (hβm : Measurable β) (hβb : ∀ z, ‖β z‖ ≤ Cβ)
    (hγm : Measurable γ) (hγb : ∀ z, ‖γ z‖ ≤ Cγ)
    (hΘm : Measurable Θ) (hΘb : ∀ z, ‖Θ z‖ ≤ CΘ) (hΘs : Function.support Θ ⊆ Work.MB.boxPow n ℓ) :
    Integrable (fun z : (Xn n × Ω) × Ω =>
      (starRingEnd ℂ) (Θ z.1.1) * α z.1.1 * β z.1.2 * γ z.2 *
        Θ (Function.update (Function.update z.1.1 i z.1.2) j z.2)) (v3 n) := by
  refine integrable_on_box3 (ℓ := ℓ) ?_ (C := CΘ * Cα * Cβ * Cγ * CΘ) ?_ ?_
  · have hm : Measurable (fun z : (Xn n × Ω) × Ω =>
        (starRingEnd ℂ) (Θ z.1.1) * α z.1.1 * β z.1.2 * γ z.2 *
          Θ (Function.update (Function.update z.1.1 i z.1.2) j z.2)) :=
      ((((Complex.continuous_conj.measurable.comp (hΘm.comp measurable_fst.fst)).mul
        (hαm.comp measurable_fst.fst)).mul
        (hβm.comp measurable_fst.snd)).mul (hγm.comp measurable_snd)).mul
        (hΘm.comp (kf_measurable_update_update_snd i j))
    exact hm.aestronglyMeasurable
  · intro z
    rw [norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_conj]
    gcongr
    · exact hΘb z.1.1
    · exact hαb z.1.1
    · exact hβb z.1.2
    · exact hγb z.2
    · exact hΘb _
  · intro z hz
    by_cases h1 : z.1.1 ∈ Work.MB.boxPow n ℓ
    · by_cases h2 : z.1.2 ∈ boxL ℓ
      · by_cases h3 : z.2 ∈ boxL ℓ
        · exact absurd (show z ∈ (Work.MB.boxPow n ℓ ×ˢ boxL ℓ) ×ˢ boxL ℓ from ⟨⟨h1, h2⟩, h3⟩) hz
        · have hz0 : Θ (Function.update (Function.update z.1.1 i z.1.2) j z.2) = 0 := by
            by_contra hne
            have hmem := (Work.MB.mem_boxPow_iff.mp (hΘs (Function.mem_support.mpr hne))) j
            rw [Function.update_self] at hmem
            exact h3 hmem
          simp [hz0]
      · have hz0 : Θ (Function.update (Function.update z.1.1 i z.1.2) j z.2) = 0 := by
          by_contra hne
          have hmem := (Work.MB.mem_boxPow_iff.mp (hΘs (Function.mem_support.mpr hne))) i
          rw [Function.update_of_ne hij, Function.update_self] at hmem
          exact h2 hmem
        simp [hz0]
    · have hz0 : (starRingEnd ℂ) (Θ z.1.1) = 0 := by
        rw [show Θ z.1.1 = 0 from Function.notMem_support.mp (fun h => h1 (hΘs h))]
        simp
      simp [hz0]

/-! ## 6. The finite-sum/triple-integral exchange -/

/-- **The finite sum exchanges with the triple iterated integral.**  If each summand is integrable
on the product space, then
`∑ₖ cₖ·(∑_{p∈s} ∫ₓ∫_y∫_u Aₖp) = ∑_{p∈s} ∫ₓ∫_y∫_u ∑ₖ cₖ·Aₖp`.

The proof is `MeasureTheory.integral_prod` twice (converting the product integral into the iterated
one) together with `MeasureTheory.integral_finsetSum` at the product level; no per-level
integrability is needed. -/
theorem sum_mul_iterated_triple_eq {ι : Type*} {Mode : Type*} [Fintype Mode] {n : ℕ}
    (s : Finset ι) (c : Mode → ℂ) (A : Mode → ι → Xn n → Ω → Ω → ℂ)
    (hA : ∀ k p, p ∈ s → Integrable (fun z : (Xn n × Ω) × Ω => A k p z.1.1 z.1.2 z.2) (v3 n)) :
    (∑ k : Mode, c k * (∑ p ∈ s, ∫ x : Xn n, ∫ y : Ω, ∫ u : Ω, A k p x y u))
      = ∑ p ∈ s, ∫ x : Xn n, ∫ y : Ω, ∫ u : Ω, ∑ k : Mode, c k * A k p x y u := by
  classical
  have key : ∀ p ∈ s, (∑ k : Mode, c k * (∫ x : Xn n, ∫ y : Ω, ∫ u : Ω, A k p x y u))
      = ∫ x : Xn n, ∫ y : Ω, ∫ u : Ω, ∑ k : Mode, c k * A k p x y u := by
    intro p hp
    have h1 : ∀ k, (∫ z : (Xn n × Ω) × Ω, A k p z.1.1 z.1.2 z.2 ∂v3 n)
        = ∫ q : Xn n × Ω, ∫ u : Ω, A k p q.1 q.2 u ∂volume := fun k =>
      MeasureTheory.integral_prod (fun z : (Xn n × Ω) × Ω => A k p z.1.1 z.1.2 z.2) (hA k p hp)
    have h2 : ∀ k, (∫ q : Xn n × Ω, ∫ u : Ω, A k p q.1 q.2 u ∂volume)
        = ∫ x : Xn n, ∫ y : Ω, ∫ u : Ω, A k p x y u := fun k =>
      MeasureTheory.integral_prod (fun q : Xn n × Ω => ∫ u : Ω, A k p q.1 q.2 u)
        (MeasureTheory.Integrable.integral_prod_left (hA k p hp))
    have hs : Integrable (fun z : (Xn n × Ω) × Ω => ∑ k : Mode, c k * A k p z.1.1 z.1.2 z.2)
        (v3 n) :=
      MeasureTheory.integrable_finsetSum Finset.univ (fun k _ => (hA k p hp).const_mul (c k))
    have h1s : (∫ z : (Xn n × Ω) × Ω, (∑ k : Mode, c k * A k p z.1.1 z.1.2 z.2) ∂v3 n)
        = ∫ q : Xn n × Ω, ∫ u : Ω, (∑ k : Mode, c k * A k p q.1 q.2 u) ∂volume :=
      MeasureTheory.integral_prod
        (fun z : (Xn n × Ω) × Ω => ∑ k : Mode, c k * A k p z.1.1 z.1.2 z.2) hs
    have h2s : (∫ q : Xn n × Ω, ∫ u : Ω, (∑ k : Mode, c k * A k p q.1 q.2 u) ∂volume)
        = ∫ x : Xn n, ∫ y : Ω, ∫ u : Ω, ∑ k : Mode, c k * A k p x y u :=
      MeasureTheory.integral_prod
        (fun q : Xn n × Ω => ∫ u : Ω, ∑ k : Mode, c k * A k p q.1 q.2 u)
        (MeasureTheory.Integrable.integral_prod_left hs)
    calc (∑ k : Mode, c k * (∫ x : Xn n, ∫ y : Ω, ∫ u : Ω, A k p x y u))
        = ∑ k : Mode, c k * (∫ z : (Xn n × Ω) × Ω, A k p z.1.1 z.1.2 z.2 ∂v3 n) := by
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [h1 k, h2 k]
      _ = ∑ k : Mode, ∫ z : (Xn n × Ω) × Ω, c k * A k p z.1.1 z.1.2 z.2 ∂v3 n := by
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [MeasureTheory.integral_const_mul]
      _ = ∫ z : (Xn n × Ω) × Ω, ∑ k : Mode, c k * A k p z.1.1 z.1.2 z.2 ∂v3 n :=
          (MeasureTheory.integral_finsetSum Finset.univ
            (fun k _ => (hA k p hp).const_mul (c k))).symm
      _ = _ := by rw [h1s, h2s]
  calc (∑ k : Mode, c k * (∑ p ∈ s, ∫ x : Xn n, ∫ y : Ω, ∫ u : Ω, A k p x y u))
      = ∑ k : Mode, ∑ p ∈ s, c k * (∫ x : Xn n, ∫ y : Ω, ∫ u : Ω, A k p x y u) :=
        Finset.sum_congr rfl (fun k _ => Finset.mul_sum s _ (c k))
    _ = ∑ p ∈ s, ∑ k : Mode, c k * (∫ x : Xn n, ∫ y : Ω, ∫ u : Ω, A k p x y u) := Finset.sum_comm
    _ = ∑ p ∈ s, ∫ x : Xn n, ∫ y : Ω, ∫ u : Ω, ∑ k : Mode, c k * A k p x y u :=
        Finset.sum_congr rfl (fun p hp => key p hp)

/-! ## 7. Congruence of iterated integrals -/

/-- Pointwise (hence a.e.) equal integrands have equal triple iterated integrals. -/
theorem integral_triple_congr_ae {n : ℕ} {f g : Xn n → Ω → Ω → ℂ}
    (h : ∀ᵐ x ∂(volume : Measure (Xn n)), ∀ᵐ y ∂(volume : Measure Ω),
      ∀ᵐ u ∂(volume : Measure Ω), f x y u = g x y u) :
    (∫ x : Xn n, ∫ y : Ω, ∫ u : Ω, f x y u) = ∫ x : Xn n, ∫ y : Ω, ∫ u : Ω, g x y u := by
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [h] with x hx
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [hx] with y hy
  exact MeasureTheory.integral_congr_ae hy

/-- Pointwise equal integrands have equal triple iterated integrals. -/
theorem integral_triple_congr_of_forall {n : ℕ} {f g : Xn n → Ω → Ω → ℂ}
    (h : ∀ x y u, f x y u = g x y u) :
    (∫ x : Xn n, ∫ y : Ω, ∫ u : Ω, f x y u) = ∫ x : Xn n, ∫ y : Ω, ∫ u : Ω, g x y u :=
  integral_triple_congr_ae (Filter.Eventually.of_forall fun x =>
    Filter.Eventually.of_forall fun y => Filter.Eventually.of_forall fun u => h x y u)

/-- Pointwise equal integrands have equal double iterated integrals. -/
theorem integral_double_congr_of_forall {n : ℕ} {f g : Xn n → Ω → ℂ}
    (h : ∀ x y, f x y = g x y) :
    (∫ x : Xn n, ∫ y : Ω, f x y) = ∫ x : Xn n, ∫ y : Ω, g x y := by
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with x
  exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => h x y)

/-! ## 8. An elementary finite-sum rearrangement -/

/-- `∑ₖ cₖ·(A·fₖ·D) = A·(∑ₖ cₖ·fₖ)·D`. -/
theorem sum_mul_factor {Mode : Type*} [Fintype Mode] (c : Mode → ℂ) (A D : ℂ) (f : Mode → ℂ) :
    (∑ k : Mode, c k * (A * f k * D)) = A * (∑ k : Mode, c k * f k) * D := by
  rw [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl (fun k _ => by ring)

/-! ## 9. The `(W₁ + W₁ω)` block of the `Q₂` row in kernel form -/

/-- **The `(W₁+W₁ω)` block of the `Q₂` row in kernel form.**  The finite mode sum `∑ₖ` of the
pinned normal form
(`Work.BoseBoxFock.potPairRows_cIPn_pinned_gen`, first block) is moved inside the three position
integrals, where it becomes the kernel
`∑ₖ (W₁ k + W₁ω k)·Fpₖ(x_{p.2})·conj(Fpₖ y)`.

The hypotheses are the two a.e. pinning facts `Fpₖ =ᵐ Gₖ`, `Th =ᵐ T` against the *everywhere*
measurable, bounded representatives `G`, `T` (in the application these are `η_{f k}` and
`η_{evec0}`), which is what makes the summands integrable. -/
theorem potPairRowsKernelBlock1 {n : ℕ} {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode]
    (E : Work.BoseB7.Q3Env Mode) (Fp G : Mode → Ω → ℂ) (Th T : Ω → ℂ) (Θ : Xn n → ℂ) (ℓ : ℝ)
    (hGm : ∀ k, Measurable (G k)) (hGb : ∀ k, ∃ C : ℝ, 0 ≤ C ∧ ∀ z, ‖G k z‖ ≤ C)
    (hTm : Measurable T) (hTb : ∃ C : ℝ, 0 ≤ C ∧ ∀ z, ‖T z‖ ≤ C)
    (hFp : ∀ k, Fp k =ᵐ[volume] G k) (hTh : Th =ᵐ[volume] T)
    (hΘm : Measurable Θ) (hΘb : ∃ C : ℝ, 0 ≤ C ∧ ∀ z, ‖Θ z‖ ≤ C)
    (hΘs : Function.support Θ ⊆ Work.MB.boxPow n ℓ) :
    (∑ k : Mode, (E.W1 k + E.W1omega k) •
        (∑ p ∈ Submission.BoseGases.pairSet n,
          ∫ x : Xn n, ∫ y : Ω, ∫ u : Ω,
            (starRingEnd ℂ) (Θ x) * Th (x p.1) * (starRingEnd ℂ) (Fp k y) * Fp k (x p.2)
              * (starRingEnd ℂ) (Th u)
              * Θ (Function.update (Function.update x p.1 y) p.2 u)))
      = ∑ p ∈ Submission.BoseGases.pairSet n,
          ∫ x : Xn n, ∫ y : Ω, ∫ u : Ω,
            (starRingEnd ℂ) (Θ x) * Th (x p.1)
              * (∑ k : Mode, (E.W1 k + E.W1omega k) * (Fp k (x p.2) * (starRingEnd ℂ) (Fp k y)))
              * (starRingEnd ℂ) (Th u)
              * Θ (Function.update (Function.update x p.1 y) p.2 u) := by
  classical
  -- ### the integrability of each summand
  have hInt : ∀ k p, p ∈ Submission.BoseGases.pairSet n →
      Integrable (fun z : (Xn n × Ω) × Ω =>
        (starRingEnd ℂ) (Θ z.1.1) * Th (z.1.1 p.1) * (starRingEnd ℂ) (Fp k z.1.2)
          * Fp k (z.1.1 p.2) * (starRingEnd ℂ) (Th z.2)
          * Θ (Function.update (Function.update z.1.1 p.1 z.1.2) p.2 z.2)) (v3 n) := by
    intro k p hp
    have hij : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
    obtain ⟨CG, hCG0, hCG⟩ := hGb k
    obtain ⟨CT, hCT0, hCT⟩ := hTb
    obtain ⟨CΘ, hCΘ0, hCΘ⟩ := hΘb
    have hη : Integrable (fun z : (Xn n × Ω) × Ω =>
        (starRingEnd ℂ) (Θ z.1.1) * (T (z.1.1 p.1) * G k (z.1.1 p.2))
          * (starRingEnd ℂ) (G k z.1.2) * (starRingEnd ℂ) (T z.2)
          * Θ (Function.update (Function.update z.1.1 p.1 z.1.2) p.2 z.2)) (v3 n) := by
      refine integrable_state_triple (Θ := Θ) (α := fun x : Xn n => T (x p.1) * G k (x p.2))
        (β := fun y : Ω => (starRingEnd ℂ) (G k y)) (γ := fun u : Ω => (starRingEnd ℂ) (T u))
        (i := p.1) (j := p.2) hij (Cα := CT * CG) (Cβ := CG) (Cγ := CT) (CΘ := CΘ)
        (mul_nonneg hCT0 hCG0) hCG0 hCT0 hCΘ0 ?_ ?_ ?_ ?_ ?_ ?_ ?_ hCΘ hΘs
      · exact (hTm.comp (measurable_pi_apply p.1)).mul ((hGm k).comp (measurable_pi_apply p.2))
      · intro x
        rw [norm_mul]
        exact mul_le_mul (hCT _) (hCG _) (norm_nonneg _) hCT0
      · exact Complex.continuous_conj.measurable.comp (hGm k)
      · intro y
        rw [Complex.norm_conj]
        exact hCG y
      · exact Complex.continuous_conj.measurable.comp hTm
      · intro u
        rw [Complex.norm_conj]
        exact hCT u
      · exact hΘm
    have hη' : Integrable (fun z : (Xn n × Ω) × Ω =>
        (starRingEnd ℂ) (Θ z.1.1) * T (z.1.1 p.1) * (starRingEnd ℂ) (G k z.1.2)
          * G k (z.1.1 p.2) * (starRingEnd ℂ) (T z.2)
          * Θ (Function.update (Function.update z.1.1 p.1 z.1.2) p.2 z.2)) (v3 n) :=
      hη.congr (Filter.Eventually.of_forall fun z => by ring)
    have hs1 : ∀ᵐ z ∂v3 n,
        (starRingEnd ℂ) (G k z.1.2) = (starRingEnd ℂ) (Fp k z.1.2) :=
      (ae_v3_fst_snd (hFp k).symm).mono fun z hz => by rw [hz]
    have hs2 : ∀ᵐ z ∂v3 n, (starRingEnd ℂ) (T z.2) = (starRingEnd ℂ) (Th z.2) :=
      (ae_v3_snd hTh.symm).mono fun z hz => by rw [hz]
    refine hη'.congr ?_
    filter_upwards [ae_v3_fst_fst_eval p.1 hTh.symm, ae_v3_fst_fst_eval p.2 (hFp k).symm,
      hs1, hs2] with z h1 h2 h3 h4
    simp only [h1, h2, h3, h4]
  -- ### the exchange
  simp only [Complex.real_smul]
  rw [sum_mul_iterated_triple_eq (s := Submission.BoseGases.pairSet n)
    (c := fun k : Mode => (((E.W1 k + E.W1omega k : ℝ)) : ℂ))
    (A := fun k p x y u =>
      (starRingEnd ℂ) (Θ x) * Th (x p.1) * (starRingEnd ℂ) (Fp k y) * Fp k (x p.2)
        * (starRingEnd ℂ) (Th u) * Θ (Function.update (Function.update x p.1 y) p.2 u)) hInt]
  -- ### the pointwise algebraic identity
  refine Finset.sum_congr rfl (fun p hp => ?_)
  refine integral_triple_congr_of_forall (fun x y u => ?_)
  rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  push_cast
  ring

end Work.BoseBoxFock
