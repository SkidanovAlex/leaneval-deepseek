import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.slotExact_comp
import Submission.Work.BoseBoxFock.slotProj_adjoint_meas
import Submission.Work.BoseBoxFock.slotProj_hasCompactSupport
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.fibre_decomposition` — the box ↔ model fibre decomposition

For orthonormal modes `e l ∈ L²(ℝ³)` and a continuous compactly supported state
`Φ : (Fin n → ℝ³) → ℂ`, the `j`-fibres `fibre e j Φ` (`SlotProjDefs.lean`), `j = 0, …, n`, of the
box ↔ model bridge add up to `Φ`, are pairwise (L²-)orthogonal, and their squared norms add up to
`‖Φ‖²` (Parseval).

The proof goes through the *sector* decomposition `slotExact e S Φ` (`FibreProjDefs.lean`), one
sector per set `S` of slots: the sectors resolve the identity (`slotExact_sum_eq`), are pairwise
orthogonal projections (`slotExact_comp`), are self-adjoint on compactly supported states
(`slotProj_adjoint_meas`), and are compactly supported (`slotProj_hasCompactSupport`).
-/

noncomputable section

namespace Work.BoseBoxFock

open MeasureTheory

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false

/-! ## 1. Integrability and regularity helpers

States built out of slot projections are measurable, bounded and compactly supported, so products
of them are integrable. -/

/-- A bounded measurable function with compact support, times a bounded measurable function, is
integrable. -/
theorem integrable_mul_of_hasCompactSupport_of_bounded {X : Type*} [MeasurableSpace X]
    [TopologicalSpace X] [OpensMeasurableSpace X] {μ : Measure X} [IsFiniteMeasureOnCompacts μ]
    {f g : X → ℂ} (hfc : HasCompactSupport f) (hfm : AEStronglyMeasurable f μ)
    (hfb : ∃ C, ∀ x, ‖f x‖ ≤ C) (hgm : AEStronglyMeasurable g μ)
    (hgb : ∃ C, ∀ x, ‖g x‖ ≤ C) :
    Integrable (fun x => f x * g x) μ := by
  obtain ⟨C, hC⟩ := hfb
  obtain ⟨C', hC'⟩ := hgb
  refine Integrable.mono'
    (g := (tsupport f).indicator (fun _ => max C 0 * max C' 0)) ?_ (hfm.mul hgm) ?_
  · rw [integrable_indicator_iff (isClosed_tsupport f).measurableSet]
    exact integrableOn_const (hfc.measure_lt_top.ne)
  · filter_upwards with x
    by_cases hx : x ∈ tsupport f
    · rw [Set.indicator_of_mem hx, norm_mul]
      exact mul_le_mul ((hC x).trans (le_max_left _ _)) ((hC' x).trans (le_max_left _ _))
        (norm_nonneg _) (le_max_right _ _)
    · rw [Set.indicator_of_notMem hx, norm_mul, image_eq_zero_of_notMem_tsupport hx,
        norm_zero, zero_mul]

/-- `star ∘ f` is measurable when `f` is. -/
theorem measurable_star_comp {X : Type*} [MeasurableSpace X] {f : X → ℂ} (hf : Measurable f) :
    Measurable (fun x => star (f x)) :=
  Complex.continuous_conj.measurable.comp hf

/-- A finite sum (pointwise) of compactly supported functions is compactly supported. -/
theorem hasCompactSupport_finset_sum {ι X M : Type*} [TopologicalSpace X] [AddCommMonoid M]
    (s : Finset ι) (f : ι → X → M) (h : ∀ i ∈ s, HasCompactSupport (f i)) :
    HasCompactSupport (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact HasCompactSupport.zero
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- A finite `ℂ`-linear combination of measurable, bounded, compactly supported states is
measurable, bounded and compactly supported. -/
theorem finset_smul_measurable_bounded_compactSupport {ι : Type*} [DecidableEq ι] {n : ℕ}
    (s : Finset ι) (c : ι → ℂ) (G : ι → (Fin n → Ω) → ℂ)
    (hGm : ∀ i, Measurable (G i)) (hGb : ∀ i, ∃ C, ∀ x, ‖G i x‖ ≤ C)
    (hGc : ∀ i, HasCompactSupport (G i)) :
    Measurable (fun x => ∑ i ∈ s, c i • G i x) ∧
      (∃ C, ∀ x, ‖∑ i ∈ s, c i • G i x‖ ≤ C) ∧
      HasCompactSupport (fun x => ∑ i ∈ s, c i • G i x) := by
  classical
  choose B hB using hGb
  refine ⟨Finset.measurable_sum _ (fun i _ => (hGm i).const_smul (c i)),
    ⟨∑ i ∈ s, ‖c i‖ * max (B i) 0, fun x => ?_⟩, ?_⟩
  · calc ‖∑ i ∈ s, c i • G i x‖ ≤ ∑ i ∈ s, ‖c i • G i x‖ := norm_sum_le _ _
      _ = ∑ i ∈ s, ‖c i‖ * ‖G i x‖ := Finset.sum_congr rfl (fun i _ => norm_smul _ _)
      _ ≤ ∑ i ∈ s, ‖c i‖ * max (B i) 0 :=
          Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left
            ((hB i x).trans (le_max_left _ _)) (norm_nonneg _))
  · exact hasCompactSupport_finset_sum s (fun i x => c i • G i x)
      (fun i _ => (hGc i).smul_left (f := fun _ => c i))

/-- `slotProj e T Φ` (`Φ` continuous, compactly supported) is measurable, bounded and compactly
supported. -/
theorem slotProj_measurable_bounded_compactSupport {m n : ℕ} (e : Fin m → Ω → ℂ)
    (he : ∀ l, Continuous (e l)) (hec : ∀ l, HasCompactSupport (e l))
    (T : Finset (Fin n)) (Φ : (Fin n → Ω) → ℂ) (hΦ : Continuous Φ)
    (hΦc : HasCompactSupport Φ) :
    Measurable (slotProj e T Φ) ∧ (∃ C, ∀ x, ‖slotProj e T Φ x‖ ≤ C) ∧
      HasCompactSupport (slotProj e T Φ) :=
  ⟨(slotInt_measurable_bounded e he hec T Φ hΦ.measurable
      (hΦ.bounded_above_of_compact_support hΦc)).1,
    (slotInt_measurable_bounded e he hec T Φ hΦ.measurable
      (hΦ.bounded_above_of_compact_support hΦc)).2,
    slotProj_hasCompactSupport e he hec T Φ hΦ hΦc⟩

/-- The sectors of a continuous compactly supported state are measurable, bounded and compactly
supported. -/
theorem slotExact_measurable_bounded_compactSupport {m n : ℕ} (e : Fin m → Ω → ℂ)
    (he : ∀ l, Continuous (e l)) (hec : ∀ l, HasCompactSupport (e l))
    (S : Finset (Fin n)) (Φ : (Fin n → Ω) → ℂ) (hΦ : Continuous Φ)
    (hΦc : HasCompactSupport Φ) :
    Measurable (slotExact e S Φ) ∧ (∃ C, ∀ x, ‖slotExact e S Φ x‖ ≤ C) ∧
      HasCompactSupport (slotExact e S Φ) := by
  have hfun : slotExact e S Φ =
      fun x => ∑ T ∈ Finset.univ.filter (fun T : Finset (Fin n) => S ⊆ T),
        (-1 : ℂ) ^ (T.card - S.card) • slotProj e T Φ x := by
    funext x
    simp only [slotExact, Finset.sum_apply, Pi.smul_apply]
  rw [hfun]
  exact finset_smul_measurable_bounded_compactSupport
    (Finset.univ.filter (fun T : Finset (Fin n) => S ⊆ T))
    (fun T => (-1 : ℂ) ^ (T.card - S.card))
    (fun T => slotProj e T Φ)
    (fun T => (slotProj_measurable_bounded_compactSupport e he hec T Φ hΦ hΦc).1)
    (fun T => (slotProj_measurable_bounded_compactSupport e he hec T Φ hΦ hΦc).2.1)
    (fun T => (slotProj_measurable_bounded_compactSupport e he hec T Φ hΦ hΦc).2.2)

/-- The fibres of a continuous compactly supported state are measurable, bounded and compactly
supported. -/
theorem fibre_measurable_bounded_compactSupport {m n : ℕ} (e : Fin m → Ω → ℂ)
    (he : ∀ l, Continuous (e l)) (hec : ∀ l, HasCompactSupport (e l))
    (j : ℕ) (Φ : (Fin n → Ω) → ℂ) (hΦ : Continuous Φ)
    (hΦc : HasCompactSupport Φ) :
    Measurable (fibre e j Φ) ∧ (∃ C, ∀ x, ‖fibre e j Φ x‖ ≤ C) ∧
      HasCompactSupport (fibre e j Φ) := by
  have hfun : fibre e j Φ =
      fun x => ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => S.card = j),
        (1 : ℂ) • slotExact e S Φ x := by
    funext x
    rw [fibre_eq_sum_slotExact]
    simp only [Finset.sum_apply, one_smul]
  rw [hfun]
  exact finset_smul_measurable_bounded_compactSupport
    (Finset.univ.filter (fun S : Finset (Fin n) => S.card = j)) (fun _ => (1 : ℂ))
    (fun S => slotExact e S Φ)
    (fun S => (slotExact_measurable_bounded_compactSupport e he hec S Φ hΦ hΦc).1)
    (fun S => (slotExact_measurable_bounded_compactSupport e he hec S Φ hΦ hΦc).2.1)
    (fun S => (slotExact_measurable_bounded_compactSupport e he hec S Φ hΦ hΦc).2.2)

/-! ## 2. Linearity of the integral over a finite sum of states -/

/-- The integral of `star (∑ G i) * Ψ` is the sum of the integrals. -/
theorem integral_star_sum_mul {ι : Type*} [DecidableEq ι] {n : ℕ}
    (s : Finset ι) (G : ι → (Fin n → Ω) → ℂ) (Ψ : (Fin n → Ω) → ℂ)
    (hGc : ∀ i, HasCompactSupport (G i)) (hGm : ∀ i, Measurable (G i))
    (hGb : ∀ i, ∃ C, ∀ x, ‖G i x‖ ≤ C)
    (hΨm : Measurable Ψ) (hΨb : ∃ C, ∀ x, ‖Ψ x‖ ≤ C) :
    ∫ x, star (∑ i ∈ s, G i x) * Ψ x = ∑ i ∈ s, ∫ x, star (G i x) * Ψ x := by
  have hpt : ∀ x, star (∑ i ∈ s, G i x) * Ψ x = ∑ i ∈ s, star (G i x) * Ψ x := by
    intro x
    rw [star_sum, Finset.sum_mul]
  rw [show (∫ x, star (∑ i ∈ s, G i x) * Ψ x) = ∫ x, ∑ i ∈ s, star (G i x) * Ψ x from
    integral_congr_ae (Filter.Eventually.of_forall hpt)]
  rw [integral_finsetSum (f := fun i x => star (G i x) * Ψ x)]
  intro i _
  exact integrable_mul_of_hasCompactSupport_of_bounded
    ((hGc i).comp_left (g := star) (by simp))
    (measurable_star_comp (hGm i)).aestronglyMeasurable
    ((hGb i).imp (fun C hC x => by rw [norm_star]; exact hC x))
    hΨm.aestronglyMeasurable hΨb

/-- The integral of `Θ * (∑ G i)` is the sum of the integrals. -/
theorem integral_mul_sum {ι : Type*} [DecidableEq ι] {n : ℕ}
    (s : Finset ι) (G : ι → (Fin n → Ω) → ℂ) (Θ : (Fin n → Ω) → ℂ)
    (hΘc : HasCompactSupport Θ) (hΘm : Measurable Θ) (hΘb : ∃ C, ∀ x, ‖Θ x‖ ≤ C)
    (hGm : ∀ i, Measurable (G i)) (hGb : ∀ i, ∃ C, ∀ x, ‖G i x‖ ≤ C) :
    ∫ x, Θ x * (∑ i ∈ s, G i x) = ∑ i ∈ s, ∫ x, Θ x * G i x := by
  have hpt : ∀ x, Θ x * (∑ i ∈ s, G i x) = ∑ i ∈ s, Θ x * G i x := by
    intro x
    rw [Finset.mul_sum]
  rw [show (∫ x, Θ x * (∑ i ∈ s, G i x)) = ∫ x, ∑ i ∈ s, Θ x * G i x from
    integral_congr_ae (Filter.Eventually.of_forall hpt)]
  rw [integral_finsetSum (f := fun i x => Θ x * G i x)]
  intro i _
  exact integrable_mul_of_hasCompactSupport_of_bounded hΘc hΘm.aestronglyMeasurable hΘb
    (hGm i).aestronglyMeasurable (hGb i)

/-- The integral of `star (∑ G i) * (∑ H j)` is the double sum of the integrals. -/
theorem integral_star_sum_mul_sum {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] {n : ℕ}
    (s : Finset ι) (t : Finset κ) (G : ι → (Fin n → Ω) → ℂ) (H : κ → (Fin n → Ω) → ℂ)
    (hGc : ∀ i, HasCompactSupport (G i)) (hGm : ∀ i, Measurable (G i))
    (hGb : ∀ i, ∃ C, ∀ x, ‖G i x‖ ≤ C)
    (hHm : ∀ i, Measurable (H i)) (hHb : ∀ i, ∃ C, ∀ x, ‖H i x‖ ≤ C) :
    ∫ x, star (∑ i ∈ s, G i x) * (∑ j ∈ t, H j x)
      = ∑ i ∈ s, ∑ j ∈ t, ∫ x, star (G i x) * H j x := by
  have hpt : ∀ x, star (∑ i ∈ s, G i x) * (∑ j ∈ t, H j x)
      = ∑ i ∈ s, ∑ j ∈ t, star (G i x) * H j x := by
    intro x
    rw [star_sum, Finset.sum_mul_sum]
  rw [show (∫ x, star (∑ i ∈ s, G i x) * (∑ j ∈ t, H j x))
      = ∫ x, ∑ i ∈ s, ∑ j ∈ t, star (G i x) * H j x from
    integral_congr_ae (Filter.Eventually.of_forall hpt)]
  rw [integral_finsetSum (f := fun i x => ∑ j ∈ t, star (G i x) * H j x)]
  swap
  · intro i _
    exact integrable_finsetSum _ (fun j _ =>
      integrable_mul_of_hasCompactSupport_of_bounded
        ((hGc i).comp_left (g := star) (by simp))
        (measurable_star_comp (hGm i)).aestronglyMeasurable
        ((hGb i).imp (fun C hC x => by rw [norm_star]; exact hC x))
        (hHm j).aestronglyMeasurable (hHb j))
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [integral_finsetSum (f := fun j x => star (G i x) * H j x)]
  intro j _
  exact integrable_mul_of_hasCompactSupport_of_bounded
    ((hGc i).comp_left (g := star) (by simp))
    (measurable_star_comp (hGm i)).aestronglyMeasurable
    ((hGb i).imp (fun C hC x => by rw [norm_star]; exact hC x))
    (hHm j).aestronglyMeasurable (hHb j)

/-! ## 3. The fibres are the cardinality sums of the sectors -/

/-- Regrouping a sum over slot sets by cardinality. -/
theorem sum_range_sum_card {n : ℕ} {M : Type*} [AddCommMonoid M] (f : Finset (Fin n) → M) :
    ∑ j ∈ Finset.range (n + 1),
        ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => S.card = j), f S
      = ∑ S : Finset (Fin n), f S := by
  have hcard : (Finset.univ : Finset (Fin n)).card = n := by simp
  have hpcard : ∀ j : ℕ, Finset.powersetCard j (Finset.univ : Finset (Fin n)) =
      Finset.univ.filter (fun S : Finset (Fin n) => S.card = j) := by
    intro j
    ext S
    simp [Finset.mem_powersetCard]
  have hpow : (Finset.univ : Finset (Fin n)).powerset = Finset.univ := by
    ext S
    simp
  calc ∑ j ∈ Finset.range (n + 1),
        ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => S.card = j), f S
      = ∑ j ∈ Finset.range ((Finset.univ : Finset (Fin n)).card + 1),
          ∑ S ∈ Finset.powersetCard j (Finset.univ : Finset (Fin n)), f S := by
        rw [hcard]
        exact Finset.sum_congr rfl (fun j _ => by rw [hpcard j])
    _ = ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset, f S :=
        (Finset.sum_powerset _ _).symm
    _ = ∑ S : Finset (Fin n), f S := by rw [hpow]

/-- Summing the fibres over the cardinalities `0, …, n` is summing the sectors over all the slot
sets. -/
theorem sum_range_fibre_eq_sum_slotExact {m n : ℕ} (e : Fin m → Ω → ℂ)
    (Φ : (Fin n → Ω) → ℂ) :
    ∑ j ∈ Finset.range (n + 1), fibre e j Φ = ∑ S : Finset (Fin n), slotExact e S Φ := by
  rw [show (∑ j ∈ Finset.range (n + 1), fibre e j Φ)
      = ∑ j ∈ Finset.range (n + 1),
          ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => S.card = j),
            slotExact e S Φ from
    Finset.sum_congr rfl (fun j _ => fibre_eq_sum_slotExact e j Φ)]
  exact sum_range_sum_card (fun S => slotExact e S Φ)

/-! ## 4. The sectors are pairwise orthogonal -/

/-- The sectors of the fibre decomposition are pairwise orthogonal: the diagonal pairing of two
sectors is the pairing of `Φ` with the sector, the off-diagonal pairing vanishes. -/
theorem slotExact_orth {m n : ℕ} (e : Fin m → Ω → ℂ)
    (he : ∀ l, Continuous (e l)) (hec : ∀ l, HasCompactSupport (e l))
    (horth : ∀ l l', ∫ z, star (e l z) * e l' z = (if l = l' then (1 : ℂ) else 0))
    (S S' : Finset (Fin n)) (Φ : (Fin n → Ω) → ℂ) (hΦ : Continuous Φ)
    (hΦc : HasCompactSupport Φ) :
    ∫ x, star (slotExact e S Φ x) * slotExact e S' Φ x =
      if S = S' then ∫ x, star (Φ x) * slotExact e S Φ x else 0 := by
  classical
  set sS : Finset (Finset (Fin n)) :=
    Finset.univ.filter (fun T : Finset (Fin n) => S ⊆ T) with hsS
  set cP : Finset (Fin n) → ℂ := fun T => (-1 : ℂ) ^ (T.card - S.card) with hcP
  have hΨ := slotExact_measurable_bounded_compactSupport e he hec S' Φ hΦ hΦc
  have hconj : ∀ k : ℕ, star ((-1 : ℂ) ^ k) = (-1 : ℂ) ^ k := by
    intro k
    rw [Complex.star_def, map_pow]
    simp
  -- the sector `S` is the sum of the slot projections over the supersets of `S`
  have hE : ∀ Ψ : (Fin n → Ω) → ℂ, ∀ x : Fin n → Ω,
      slotExact e S Ψ x = ∑ T ∈ sS, cP T * slotProj e T Ψ x := by
    intro Ψ x
    simp only [slotExact, hsS, hcP, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hPm : ∀ T : Finset (Fin n), Measurable (fun x => cP T * slotProj e T Φ x) := fun T =>
    (slotProj_measurable_bounded_compactSupport e he hec T Φ hΦ hΦc).1.const_smul (cP T)
  have hPb : ∀ T : Finset (Fin n), ∃ C, ∀ x, ‖cP T * slotProj e T Φ x‖ ≤ C := fun T => by
    obtain ⟨C, hC⟩ := (slotProj_measurable_bounded_compactSupport e he hec T Φ hΦ hΦc).2.1
    exact ⟨‖cP T‖ * C, fun x => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hC x) (norm_nonneg _)⟩
  have hPc : ∀ T : Finset (Fin n), HasCompactSupport (fun x => cP T * slotProj e T Φ x) := fun T =>
    (slotProj_measurable_bounded_compactSupport e he hec T Φ hΦ hΦc).2.2.smul_left
      (f := fun _ => cP T)
  have hQm : ∀ T : Finset (Fin n),
      Measurable (fun x => cP T * slotProj e T (slotExact e S' Φ) x) := fun T =>
    (slotInt_measurable_bounded e he hec T (slotExact e S' Φ) hΨ.1 hΨ.2.1).1.const_smul (cP T)
  have hQb : ∀ T : Finset (Fin n),
      ∃ C, ∀ x, ‖cP T * slotProj e T (slotExact e S' Φ) x‖ ≤ C := fun T => by
    obtain ⟨C, hC⟩ := (slotInt_measurable_bounded e he hec T (slotExact e S' Φ) hΨ.1 hΨ.2.1).2
    exact ⟨‖cP T‖ * C, fun x => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hC x) (norm_nonneg _)⟩
  -- step 1: expand the left factor and pull out the coefficients
  have h1 : ∫ x, star (slotExact e S Φ x) * slotExact e S' Φ x
      = ∑ T ∈ sS, cP T * ∫ x, star (slotProj e T Φ x) * slotExact e S' Φ x := by
    have hpt : ∀ x : Fin n → Ω,
        star (slotExact e S Φ x) * slotExact e S' Φ x
          = star (∑ T ∈ sS, cP T * slotProj e T Φ x) * slotExact e S' Φ x := by
      intro x
      rw [hE Φ x, star_sum]
    rw [show (∫ x, star (slotExact e S Φ x) * slotExact e S' Φ x)
        = ∫ x, star (∑ T ∈ sS, cP T * slotProj e T Φ x) * slotExact e S' Φ x from
      integral_congr_ae (Filter.Eventually.of_forall hpt)]
    rw [integral_star_sum_mul sS (fun T x => cP T * slotProj e T Φ x) (slotExact e S' Φ)
      hPc hPm hPb hΨ.1 hΨ.2.1]
    refine Finset.sum_congr rfl (fun T _ => ?_)
    rw [show (fun x => star (cP T * slotProj e T Φ x) * slotExact e S' Φ x)
        = fun x => cP T * (star (slotProj e T Φ x) * slotExact e S' Φ x) from by
      funext x
      rw [star_mul, hconj]
      ring]
    rw [integral_const_mul]
  -- step 2: self-adjointness of `slotProj`
  have h2 : ∑ T ∈ sS, cP T * ∫ x, star (slotProj e T Φ x) * slotExact e S' Φ x
      = ∑ T ∈ sS, ∫ x, star (Φ x) * (cP T * slotProj e T (slotExact e S' Φ) x) := by
    refine Finset.sum_congr rfl (fun T _ => ?_)
    rw [slotProj_adjoint_meas e he hec horth T Φ (slotExact e S' Φ) hΦ hΦc hΨ.1 hΨ.2.1]
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  -- step 3: fold the sum back
  have h3 : ∑ T ∈ sS, ∫ x, star (Φ x) * (cP T * slotProj e T (slotExact e S' Φ) x)
      = ∫ x, star (Φ x) * slotExact e S (slotExact e S' Φ) x := by
    have hpt : ∀ x : Fin n → Ω, star (Φ x) * slotExact e S (slotExact e S' Φ) x
        = star (Φ x) * (∑ T ∈ sS, cP T * slotProj e T (slotExact e S' Φ) x) := by
      intro x
      rw [hE (slotExact e S' Φ) x]
    rw [show (∫ x, star (Φ x) * slotExact e S (slotExact e S' Φ) x)
        = ∫ x, star (Φ x) * (∑ T ∈ sS, cP T * slotProj e T (slotExact e S' Φ) x) from
      integral_congr_ae (Filter.Eventually.of_forall hpt)]
    rw [← integral_mul_sum sS (fun T x => cP T * slotProj e T (slotExact e S' Φ) x)
      (fun x => star (Φ x))
      (hΦc.comp_left (g := star) (by simp)) (measurable_star_comp hΦ.measurable)
      (hΦ.bounded_above_of_compact_support hΦc |>.imp (fun C hC x => by
        rw [norm_star]; exact hC x))
      hQm hQb]
  -- step 4: the composition law
  rw [h1, h2, h3, slotExact_comp e he hec horth S S' Φ hΦ.measurable
    (hΦ.bounded_above_of_compact_support hΦc)]
  by_cases h : S = S'
  · simp only [if_pos h]
  · simp only [if_neg h]
    simp

/-! ## 5. The target -/

theorem fibre_decomposition {m n : ℕ} (e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ)
    (he : ∀ l, Continuous (e l)) (hec : ∀ l, HasCompactSupport (e l))
    (horth : ∀ l l', ∫ z, star (e l z) * e l' z = (if l = l' then (1 : ℂ) else 0))
    (Φ : (Fin n → EuclideanSpace ℝ (Fin 3)) → ℂ)
    (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ) :
    (∀ x, Φ x = ∑ j ∈ Finset.range (n + 1), fibre e j Φ x) ∧
    (∀ j ∈ Finset.range (n + 1), ∀ j' ∈ Finset.range (n + 1), j ≠ j' →
      ∫ x, star (fibre e j Φ x) * fibre e j' Φ x = 0) ∧
    (∫ x, ‖Φ x‖ ^ 2 = ∑ j ∈ Finset.range (n + 1), ∫ x, ‖fibre e j Φ x‖ ^ 2) := by
  classical
  have hΦb : ∃ C, ∀ x, ‖Φ x‖ ≤ C := hΦ.bounded_above_of_compact_support hΦc
  have hpoint : ∀ x, Φ x = ∑ j ∈ Finset.range (n + 1), fibre e j Φ x := fun x => by
    have h := congrFun ((sum_range_fibre_eq_sum_slotExact e Φ).trans (slotExact_sum_eq e Φ)) x
    rw [Finset.sum_apply] at h
    exact h.symm
  have hfs : ∀ j : ℕ, Measurable (fibre e j Φ) ∧ (∃ C, ∀ x, ‖fibre e j Φ x‖ ≤ C) ∧
      HasCompactSupport (fibre e j Φ) := fun j =>
    fibre_measurable_bounded_compactSupport e he hec j Φ hΦ hΦc
  have hEs : ∀ S : Finset (Fin n), Measurable (slotExact e S Φ) ∧
      (∃ C, ∀ x, ‖slotExact e S Φ x‖ ≤ C) ∧ HasCompactSupport (slotExact e S Φ) := fun S =>
    slotExact_measurable_bounded_compactSupport e he hec S Φ hΦ hΦc
  -- (2) pairwise orthogonality of the fibres
  have horth2 : ∀ j ∈ Finset.range (n + 1), ∀ j' ∈ Finset.range (n + 1), j ≠ j' →
      ∫ x, star (fibre e j Φ x) * fibre e j' Φ x = 0 := by
    intro j _ j' _ hjj'
    rw [fibre_eq_sum_slotExact e j Φ, fibre_eq_sum_slotExact e j' Φ]
    simp only [Finset.sum_apply]
    rw [integral_star_sum_mul_sum
      (Finset.univ.filter (fun S : Finset (Fin n) => S.card = j))
      (Finset.univ.filter (fun S : Finset (Fin n) => S.card = j'))
      (fun S => slotExact e S Φ) (fun S => slotExact e S Φ)
      (fun S => (hEs S).2.2) (fun S => (hEs S).1) (fun S => (hEs S).2.1)
      (fun S => (hEs S).1) (fun S => (hEs S).2.1)]
    refine Finset.sum_eq_zero (fun S hS => Finset.sum_eq_zero (fun S' hS' => ?_))
    rw [slotExact_orth e he hec horth S S' Φ hΦ hΦc]
    by_cases hSS : S = S'
    · exfalso
      have h1 : S.card = j := (Finset.mem_filter.mp hS).2
      have h2 : S'.card = j' := (Finset.mem_filter.mp hS').2
      rw [hSS] at h1
      exact hjj' (h1.symm.trans h2)
    · rw [if_neg hSS]
  -- the complex-valued Parseval identity
  have hparseval : ∫ x, star (Φ x) * Φ x
      = ∑ j ∈ Finset.range (n + 1), ∫ x, star (fibre e j Φ x) * fibre e j Φ x := by
    have hpt : ∀ x : Fin n → Ω, star (Φ x) * Φ x
        = star (∑ j ∈ Finset.range (n + 1), fibre e j Φ x) *
            (∑ j ∈ Finset.range (n + 1), fibre e j Φ x) := by
      intro x
      rw [hpoint x]
    have h1 : ∫ x, star (Φ x) * Φ x
        = ∫ x, star (∑ j ∈ Finset.range (n + 1), fibre e j Φ x) *
            (∑ j ∈ Finset.range (n + 1), fibre e j Φ x) :=
      integral_congr_ae (Filter.Eventually.of_forall hpt)
    rw [h1, integral_star_sum_mul_sum (Finset.range (n + 1)) (Finset.range (n + 1))
      (fun j => fibre e j Φ) (fun j => fibre e j Φ)
      (fun j => (hfs j).2.2) (fun j => (hfs j).1) (fun j => (hfs j).2.1)
      (fun j => (hfs j).1) (fun j => (hfs j).2.1)]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [Finset.sum_eq_single j]
    · intro j' hj' hne
      exact horth2 j hj j' hj' (Ne.symm hne)
    · intro hnot
      exact absurd hj hnot
  refine ⟨hpoint, horth2, ?_⟩
  -- from the complex identity to the real statement
  have hnorm : ∀ z : ℂ, (star z * z).re = ‖z‖ ^ 2 := fun z => by
    rw [show star z * z = ((Complex.normSq z : ℝ) : ℂ) from
        Complex.normSq_eq_conj_mul_self.symm,
      Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  have hnt : ∀ z : ℂ, ‖star z‖ = ‖z‖ := fun z => norm_star z
  have hIntΦ : Integrable (fun x => star (Φ x) * Φ x) :=
    integrable_mul_of_hasCompactSupport_of_bounded (hΦc.comp_left (g := star) (by simp))
      (measurable_star_comp hΦ.measurable).aestronglyMeasurable
      (hΦb.imp (fun C hC x => by rw [hnt]; exact hC x))
      hΦ.measurable.aestronglyMeasurable hΦb
  have hL : (∫ x, star (Φ x) * Φ x).re = ∫ x, ‖Φ x‖ ^ 2 := by
    rw [show (∫ x, star (Φ x) * Φ x).re = ∫ x, (star (Φ x) * Φ x).re from
      (integral_re hIntΦ).symm]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => hnorm (Φ x))
  have hR : (∑ j ∈ Finset.range (n + 1), ∫ x, star (fibre e j Φ x) * fibre e j Φ x).re
      = ∑ j ∈ Finset.range (n + 1), ∫ x, ‖fibre e j Φ x‖ ^ 2 := by
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have hIj : Integrable (fun x => star (fibre e j Φ x) * fibre e j Φ x) :=
      integrable_mul_of_hasCompactSupport_of_bounded
        ((hfs j).2.2.comp_left (g := star) (by simp))
        (measurable_star_comp (hfs j).1).aestronglyMeasurable
        ((hfs j).2.1.imp (fun C hC x => by rw [hnt]; exact hC x))
        (hfs j).1.aestronglyMeasurable (hfs j).2.1
    rw [show (∫ x, star (fibre e j Φ x) * fibre e j Φ x).re
        = ∫ x, (star (fibre e j Φ x) * fibre e j Φ x).re from (integral_re hIj).symm]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => hnorm (fibre e j Φ x))
  rw [← hL, ← hR, hparseval]

end Work.BoseBoxFock
