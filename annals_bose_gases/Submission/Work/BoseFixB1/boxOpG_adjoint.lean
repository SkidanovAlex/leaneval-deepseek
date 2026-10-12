import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.setIntegral_acube_eq_of_tsupport_subset
import Submission.Work.BoseFixB1S.BoxPIndFlat
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.boxOpG_adjoint` — adjointness of the one-slot box operators

`boxOpG A f h` creates a particle in slot `i`, weighted by the box indicator `1_A(x_i) f(x_i)`,
and annihilates the slot `i` against the test function `h`:

  `boxOpG A f h Ψ x = Σ_i 1_A(x_i)·f(x_i)·∫_{z∈A} h z·Ψ(x|i↦z)`,

while `boxOpZ A h f` is the same one-slot operator *without* the indicator.  The adjointness

  `∫_{abox} Φ·(boxOpG A f h Ψ) = ∫_{abox} (boxOpZ A h f Φ)·Ψ`

is the "one-slot peel + swap of the created and annihilated slot" identity.  Peel the slot `i`
(measure-preserving split `kcInsN`, `Submission.BoseGases.abox_integral_peel`): writing
`x = kcInsN N i (y,r)` (and `x|i↦z = kcInsN N i (z,r)`), both sides become iterated integrals
over `(y ∈ acube a, r ∈ abox N a)`.  For fixed `r`:

* the left inner integral is `∫_y Φ(y,r)·(1_A(y)·f(y)·C)` with `C = ∫_z h z·Ψ(z,r)`, which pulls
  the `y`-constant `C` out and collapses `∫_{acube a} 1_A·(Φ·f) = ∫_A Φ·f` (via `A ⊆ acube a`);
* the right inner integral is `∫_y (h(y)·D)·Ψ(y,r)` with `D = ∫_z f z·Φ(z,r)`, which pulls `D`
  out and localises `∫_{acube a} h·Ψ = ∫_A h·Ψ` (via `h = 0` off `A`, i.e. `tsupport h ⊆ A`).

The two resulting products of integrals are the same by `mul_comm` and renaming of the bound
variable.  The only measure theory used is the peel (needs `IntegrableOn` of the two slot
integrands, obtained from boundedness and measurability) and `integral_mul_const`/`integral_const_mul`
(which are unconditional).

## Main results
* `Work.BoseFixB1.update_mem_abox_aux`, `abs_bound_setIntegral_update`,
  `measurable_slotG`, `measurable_slotZ` — elementary one-slot facts;
* `Work.BoseFixB1.integrableOn_slotG`, `integrableOn_slotZ` — integrability on the box;
* `Work.BoseFixB1.slot_adjoint` — the per-slot identity;
* `Work.BoseFixB1.boxOpG_adjoint` — the theorem.

The localisation `∫_{acube a} h·g = ∫_A h·g` for `tsupport h ⊆ A` is the delegated
`Work.BoseFixB1.setIntegral_acube_eq_of_tsupport_subset`; the indicator collapse
`∫_{acube a} 1_A·g = ∫_A g` is `Work.BoseFixB1S.setIntegral_indicator_one_mul`, and the
measurability of the fibre integral is `Work.BoseFixB1S.measurable_fibreMean`, both from
`Submission.Work.BoseFixB1S.BoxPIndFlat`. -/

namespace Work.BoseFixB1

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Elementary one-slot facts -/

/-- Inserting a point of `A` into one slot of a configuration of the box keeps it in the box. -/
lemma update_mem_abox_aux {N : ℕ} {a : ℝ} {A : Set (EuclideanSpace ℝ (Fin 3))}
    (hAc : A ⊆ Submission.BoseGases.acube a) {x : Submission.BoseGases.X (N + 1)}
    (hx : x ∈ Submission.BoseGases.abox (N + 1) a) (i : Fin (N + 1))
    {z : EuclideanSpace ℝ (Fin 3)} (hz : z ∈ A) :
    Function.update x i z ∈ Submission.BoseGases.abox (N + 1) a := by
  intro j
  rw [Function.update_apply]
  by_cases hj : j = i
  · rw [if_pos hj]; exact hAc hz
  · rw [if_neg hj]; exact hx j

/-- The one-slot integral `∫_{z∈A} g z · Φ(x|i↦z)` is bounded on the box. -/
lemma abs_bound_setIntegral_update {N : ℕ} {a CΦ : ℝ} (ha : 0 < a) (hCΦ : 0 ≤ CΦ)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hAc : A ⊆ Submission.BoseGases.acube a)
    {g : EuclideanSpace ℝ (Fin 3) → ℝ} (hg : Continuous g)
    {Φ : Submission.BoseGases.X (N + 1) → ℝ}
    (hΦb : ∀ x ∈ Submission.BoseGases.abox (N + 1) a, ‖Φ x‖ ≤ CΦ) (i : Fin (N + 1)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Submission.BoseGases.abox (N + 1) a,
      |∫ z in A, g z * Φ (Function.update x i z)| ≤ C := by
  obtain ⟨Cg, hCg⟩ :=
    (Submission.BoseGases.acube_compact ha).exists_bound_of_continuousOn hg.continuousOn
  have hAfin : (volume : Measure (EuclideanSpace ℝ (Fin 3))) A < ⊤ :=
    lt_of_le_of_lt (measure_mono hAc)
      (by rw [Submission.BoseGases.acube_volume a ha.le]; exact ENNReal.ofReal_lt_top)
  refine ⟨max Cg 0 * CΦ * (volume A).toReal,
    mul_nonneg (mul_nonneg (le_max_right Cg 0) hCΦ) ENNReal.toReal_nonneg, fun x hx => ?_⟩
  have hb : ∀ z ∈ A, ‖g z * Φ (Function.update x i z)‖ ≤ max Cg 0 * CΦ := by
    intro z hz
    rw [norm_mul]
    exact mul_le_mul (le_trans (hCg z (hAc hz)) (le_max_left _ _))
      (hΦb _ (update_mem_abox_aux hAc hx i hz)) (norm_nonneg _) (le_max_right _ _)
  have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := A)
    (f := fun z : EuclideanSpace ℝ (Fin 3) => g z * Φ (Function.update x i z))
    (C := max Cg 0 * CΦ) hAfin hb
  simpa [Real.norm_eq_abs, MeasureTheory.Measure.real] using h

/-- Measurability of the `boxOpG` one-slot factor. -/
lemma measurable_slotG {N : ℕ} {A : Set (EuclideanSpace ℝ (Fin 3))} (hAm : MeasurableSet A)
    {f h : EuclideanSpace ℝ (Fin 3) → ℝ} (hf : Continuous f) (hh : Continuous h)
    {Ψ : Submission.BoseGases.X (N + 1) → ℝ} (hΨ : Continuous Ψ) (i : Fin (N + 1)) :
    Measurable (fun x : Submission.BoseGases.X (N + 1) =>
      A.indicator (fun _ => (1 : ℝ)) (x i) * f (x i)
        * ∫ z in A, h z * Ψ (Function.update x i z)) := by
  have h1 : Measurable (fun x : Submission.BoseGases.X (N + 1) =>
      A.indicator (fun _ => (1 : ℝ)) (x i)) :=
    (measurable_const.indicator hAm).comp (measurable_pi_apply i)
  have h2 : Measurable (fun x : Submission.BoseGases.X (N + 1) => f (x i)) :=
    hf.measurable.comp (measurable_pi_apply i)
  have h3 : Measurable (fun x : Submission.BoseGases.X (N + 1) =>
      ∫ z in A, h z * Ψ (Function.update x i z)) := by
    have hfun : (fun x : Submission.BoseGases.X (N + 1) =>
          ∫ z in A, (fun u : Submission.BoseGases.X (N + 1) => h (u i) * Ψ u)
            (Function.update x i z))
        = (fun x : Submission.BoseGases.X (N + 1) =>
            ∫ z in A, h z * Ψ (Function.update x i z)) := by
      funext x
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
      simp only [Function.update_apply, if_true]
    rw [← hfun]
    exact Work.BoseFixB1S.measurable_fibreMean A hAm i
      ((hh.measurable.comp (measurable_pi_apply i)).mul hΨ.measurable)
  exact h1.mul h2 |>.mul h3

/-- Measurability of the `boxOpZ` one-slot factor. -/
lemma measurable_slotZ {N : ℕ} {A : Set (EuclideanSpace ℝ (Fin 3))} (hAm : MeasurableSet A)
    {f : EuclideanSpace ℝ (Fin 3) → ℝ} (hf : Continuous f)
    {h : EuclideanSpace ℝ (Fin 3) → ℝ} (hh : Continuous h)
    {Φ : Submission.BoseGases.X (N + 1) → ℝ} (hΦm : Measurable Φ) (i : Fin (N + 1)) :
    Measurable (fun x : Submission.BoseGases.X (N + 1) =>
      h (x i) * ∫ z in A, f z * Φ (Function.update x i z)) := by
  have h1 : Measurable (fun x : Submission.BoseGases.X (N + 1) => h (x i)) :=
    hh.measurable.comp (measurable_pi_apply i)
  have h2 : Measurable (fun x : Submission.BoseGases.X (N + 1) =>
      ∫ z in A, f z * Φ (Function.update x i z)) := by
    have hfun : (fun x : Submission.BoseGases.X (N + 1) =>
          ∫ z in A, (fun u : Submission.BoseGases.X (N + 1) => f (u i) * Φ u)
            (Function.update x i z))
        = (fun x : Submission.BoseGases.X (N + 1) =>
            ∫ z in A, f z * Φ (Function.update x i z)) := by
      funext x
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
      simp only [Function.update_apply, if_true]
    rw [← hfun]
    exact Work.BoseFixB1S.measurable_fibreMean A hAm i
      ((hf.measurable.comp (measurable_pi_apply i)).mul hΦm)
  exact h1.mul h2

/-! ## Integrability of the two slot integrands -/

/-- Integrability on the box of the `boxOpG` one-slot summand. -/
lemma integrableOn_slotG {N : ℕ} {a : ℝ} (ha : 0 < a)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hAm : MeasurableSet A)
    (hAc : A ⊆ Submission.BoseGases.acube a)
    {f h : EuclideanSpace ℝ (Fin 3) → ℝ} (hf : Continuous f) (hh : Continuous h)
    (i : Fin (N + 1))
    {Φ : Submission.BoseGases.X (N + 1) → ℝ} (hΦm : Measurable Φ)
    {CΦ : ℝ} (hΦb : ∀ x ∈ Submission.BoseGases.abox (N + 1) a, |Φ x| ≤ CΦ)
    {Ψ : Submission.BoseGases.X (N + 1) → ℝ} (hΨ : Continuous Ψ) :
    IntegrableOn (fun x : Submission.BoseGases.X (N + 1) =>
        Φ x * (A.indicator (fun _ => (1 : ℝ)) (x i) * f (x i)
          * ∫ z in A, h z * Ψ (Function.update x i z)))
      (Submission.BoseGases.abox (N + 1) a) volume := by
  obtain ⟨Cf, hCf⟩ :=
    (Submission.BoseGases.acube_compact ha).exists_bound_of_continuousOn hf.continuousOn
  obtain ⟨Ch, hCh⟩ :=
    (Submission.BoseGases.acube_compact ha).exists_bound_of_continuousOn hh.continuousOn
  obtain ⟨CΨ0, hCΨ0⟩ :=
    (Submission.BoseGases.abox_compact (N + 1) ha).exists_bound_of_continuousOn hΨ.continuousOn
  have hAfin : (volume : Measure (EuclideanSpace ℝ (Fin 3))) A < ⊤ :=
    lt_of_le_of_lt (measure_mono hAc)
      (by rw [Submission.BoseGases.acube_volume a ha.le]; exact ENNReal.ofReal_lt_top)
  have hI : ∀ x ∈ Submission.BoseGases.abox (N + 1) a,
      |∫ z in A, h z * Ψ (Function.update x i z)|
        ≤ max Ch 0 * max CΨ0 0 * (volume A).toReal := by
    intro x hx
    have hb : ∀ z ∈ A, ‖h z * Ψ (Function.update x i z)‖ ≤ max Ch 0 * max CΨ0 0 := by
      intro z hz
      rw [norm_mul]
      refine mul_le_mul (le_trans (hCh z (hAc hz)) (le_max_left _ _)) ?_
        (norm_nonneg _) (le_max_right _ _)
      exact le_trans (hCΨ0 _ (update_mem_abox_aux hAc hx i hz)) (le_max_left _ _)
    have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := A)
      (f := fun z : EuclideanSpace ℝ (Fin 3) => h z * Ψ (Function.update x i z))
      (C := max Ch 0 * max CΨ0 0) hAfin hb
    simpa [Real.norm_eq_abs, MeasureTheory.Measure.real] using h
  refine Work.BoseFixB1S.integrableOn_mul_of_bound ha hΦm
    (measurable_slotG hAm hf hh hΨ i) hΦb
    (Cg := (1 * max Cf 0) * (max Ch 0 * max CΨ0 0 * (volume A).toReal)) ?_
  intro x hx
  have hf' : |f (x i)| ≤ max Cf 0 := le_trans (hCf _ (hx i)) (le_max_left _ _)
  have hind' : |A.indicator (fun _ => (1 : ℝ)) (x i)| ≤ 1 := by
    by_cases hxi : x i ∈ A <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, hxi]
  calc |A.indicator (fun _ => (1 : ℝ)) (x i) * f (x i)
          * ∫ z in A, h z * Ψ (Function.update x i z)|
      = |A.indicator (fun _ => (1 : ℝ)) (x i)| * |f (x i)|
          * |∫ z in A, h z * Ψ (Function.update x i z)| := by rw [abs_mul, abs_mul]
    _ ≤ (1 * max Cf 0) * (max Ch 0 * max CΨ0 0 * (volume A).toReal) :=
        mul_le_mul (mul_le_mul hind' hf' (abs_nonneg _) zero_le_one) (hI x hx)
          (abs_nonneg _) (mul_nonneg zero_le_one (le_max_right Cf 0))

/-- Integrability on the box of the `boxOpZ` one-slot summand. -/
lemma integrableOn_slotZ {N : ℕ} {a : ℝ} (ha : 0 < a)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hAm : MeasurableSet A)
    (hAc : A ⊆ Submission.BoseGases.acube a)
    {f h : EuclideanSpace ℝ (Fin 3) → ℝ} (hf : Continuous f) (hh : Continuous h)
    (i : Fin (N + 1))
    {Φ : Submission.BoseGases.X (N + 1) → ℝ} (hΦm : Measurable Φ)
    {CΦ : ℝ} (hΦb : ∀ x ∈ Submission.BoseGases.abox (N + 1) a, |Φ x| ≤ CΦ)
    {Ψ : Submission.BoseGases.X (N + 1) → ℝ} (hΨ : Continuous Ψ) :
    IntegrableOn (fun x : Submission.BoseGases.X (N + 1) =>
        (h (x i) * ∫ z in A, f z * Φ (Function.update x i z)) * Ψ x)
      (Submission.BoseGases.abox (N + 1) a) volume := by
  obtain ⟨Ch, hCh⟩ :=
    (Submission.BoseGases.acube_compact ha).exists_bound_of_continuousOn hh.continuousOn
  obtain ⟨CΨ0, hCΨ0⟩ :=
    (Submission.BoseGases.abox_compact (N + 1) ha).exists_bound_of_continuousOn hΨ.continuousOn
  have hCΨb : ∀ x ∈ Submission.BoseGases.abox (N + 1) a, |Ψ x| ≤ max CΨ0 0 := by
    intro x hx
    rw [← Real.norm_eq_abs]
    exact le_trans (hCΨ0 x hx) (le_max_left _ _)
  have hΦb' : ∀ x ∈ Submission.BoseGases.abox (N + 1) a, ‖Φ x‖ ≤ max CΦ 0 := by
    intro x hx
    rw [Real.norm_eq_abs]
    exact le_trans (hΦb x hx) (le_max_left _ _)
  obtain ⟨C, hC0, hC⟩ :=
    abs_bound_setIntegral_update ha (le_max_right CΦ 0) hAc hf hΦb' i
  refine Work.BoseFixB1S.integrableOn_mul_of_bound ha
    (measurable_slotZ hAm hf hh hΦm i) hΨ.measurable (Cf := max Ch 0 * C) ?_ hCΨb
  intro x hx
  calc |h (x i) * ∫ z in A, f z * Φ (Function.update x i z)|
      = |h (x i)| * |∫ z in A, f z * Φ (Function.update x i z)| := abs_mul _ _
    _ ≤ max Ch 0 * C :=
        mul_le_mul (le_trans (hCh _ (hx i)) (le_max_left _ _)) (hC x hx)
          (abs_nonneg _) (le_max_right _ _)

/-! ## The per-slot identity -/

/-- **One-slot adjointness**: `∫ Φ·(boxOpG-slot) = ∫ (boxOpZ-slot)·Ψ` on the box. -/
lemma slot_adjoint {N : ℕ} {a : ℝ} (ha : 0 < a)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hAm : MeasurableSet A)
    (hAc : A ⊆ Submission.BoseGases.acube a)
    {f h : EuclideanSpace ℝ (Fin 3) → ℝ} (hf : Continuous f) (hh : Continuous h)
    (hsh : tsupport h ⊆ A)
    {Φ : Submission.BoseGases.X (N + 1) → ℝ} (hΦm : Measurable Φ)
    {CΦ : ℝ} (hΦb : ∀ x ∈ Submission.BoseGases.abox (N + 1) a, |Φ x| ≤ CΦ)
    {Ψ : Submission.BoseGases.X (N + 1) → ℝ} (hΨ : Continuous Ψ) (i : Fin (N + 1)) :
    (∫ x in Submission.BoseGases.abox (N + 1) a,
        Φ x * (A.indicator (fun _ => (1 : ℝ)) (x i) * f (x i)
          * ∫ z in A, h z * Ψ (Function.update x i z)))
      = (∫ x in Submission.BoseGases.abox (N + 1) a,
          (h (x i) * ∫ z in A, f z * Φ (Function.update x i z)) * Ψ x) := by
  have hpeelG := Submission.BoseGases.abox_integral_peel (n := N) (ℓ := a) i
    (fun x : Submission.BoseGases.X (N + 1) =>
      Φ x * (A.indicator (fun _ => (1 : ℝ)) (x i) * f (x i)
        * ∫ z in A, h z * Ψ (Function.update x i z)))
    (integrableOn_slotG ha hAm hAc hf hh i hΦm hΦb hΨ)
  have hpeelZ := Submission.BoseGases.abox_integral_peel (n := N) (ℓ := a) i
    (fun x : Submission.BoseGases.X (N + 1) =>
      (h (x i) * ∫ z in A, f z * Φ (Function.update x i z)) * Ψ x)
    (integrableOn_slotZ ha hAm hAc hf hh i hΦm hΦb hΨ)
  rw [hpeelG, hpeelZ]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun r => ?_))
  simp only [Submission.BoseGases.kc_insN_apply_same, Submission.BoseGases.update_kcInsN]
  set C : ℝ := ∫ z in A, h z * Ψ ((Submission.BoseGases.kcInsN N i) (z, r)) with hCdef
  set D : ℝ := ∫ z in A, f z * Φ ((Submission.BoseGases.kcInsN N i) (z, r)) with hDdef
  have hL1 : (∫ y in Submission.BoseGases.acube a,
        Φ ((Submission.BoseGases.kcInsN N i) (y, r))
          * (A.indicator (fun _ => (1 : ℝ)) y * f y * C))
      = ∫ y in Submission.BoseGases.acube a,
          (Φ ((Submission.BoseGases.kcInsN N i) (y, r))
            * (A.indicator (fun _ => (1 : ℝ)) y * f y)) * C := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
    ring
  have hL2 : (∫ y in Submission.BoseGases.acube a,
        (Φ ((Submission.BoseGases.kcInsN N i) (y, r))
          * (A.indicator (fun _ => (1 : ℝ)) y * f y)) * C)
      = (∫ y in Submission.BoseGases.acube a,
          Φ ((Submission.BoseGases.kcInsN N i) (y, r))
            * (A.indicator (fun _ => (1 : ℝ)) y * f y)) * C :=
    MeasureTheory.integral_mul_const C _
  have hL3 : (∫ y in Submission.BoseGases.acube a,
        Φ ((Submission.BoseGases.kcInsN N i) (y, r))
          * (A.indicator (fun _ => (1 : ℝ)) y * f y))
      = ∫ y in Submission.BoseGases.acube a,
          (A.indicator (fun _ => (1 : ℝ)) y)
            * (Φ ((Submission.BoseGases.kcInsN N i) (y, r)) * f y) := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
    ring
  have hL4 : (∫ y in Submission.BoseGases.acube a,
        (A.indicator (fun _ => (1 : ℝ)) y)
          * (Φ ((Submission.BoseGases.kcInsN N i) (y, r)) * f y))
      = ∫ y in A, Φ ((Submission.BoseGases.kcInsN N i) (y, r)) * f y :=
    Work.BoseFixB1S.setIntegral_indicator_one_mul (A := A) (ℓ := a) hAm hAc
      (fun y : EuclideanSpace ℝ (Fin 3) => Φ ((Submission.BoseGases.kcInsN N i) (y, r)) * f y)
  have hL : (∫ y in Submission.BoseGases.acube a,
        Φ ((Submission.BoseGases.kcInsN N i) (y, r))
          * (A.indicator (fun _ => (1 : ℝ)) y * f y * C))
      = (∫ y in A, Φ ((Submission.BoseGases.kcInsN N i) (y, r)) * f y) * C :=
    hL1.trans (hL2.trans ((congrArg (fun t : ℝ => t * C) hL3).trans
      (congrArg (fun t : ℝ => t * C) hL4)))
  have hR1 : (∫ y in Submission.BoseGases.acube a,
        (h y * D) * Ψ ((Submission.BoseGases.kcInsN N i) (y, r)))
      = ∫ y in Submission.BoseGases.acube a,
          D * (h y * Ψ ((Submission.BoseGases.kcInsN N i) (y, r))) := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
    ring
  have hR2 : (∫ y in Submission.BoseGases.acube a,
        D * (h y * Ψ ((Submission.BoseGases.kcInsN N i) (y, r))))
      = D * ∫ y in Submission.BoseGases.acube a,
          h y * Ψ ((Submission.BoseGases.kcInsN N i) (y, r)) :=
    MeasureTheory.integral_const_mul D _
  have hR3 : (∫ y in Submission.BoseGases.acube a,
        h y * Ψ ((Submission.BoseGases.kcInsN N i) (y, r)))
      = ∫ y in A, h y * Ψ ((Submission.BoseGases.kcInsN N i) (y, r)) :=
    setIntegral_acube_eq_of_tsupport_subset hAm hAc hsh
      (fun y : EuclideanSpace ℝ (Fin 3) => Ψ ((Submission.BoseGases.kcInsN N i) (y, r)))
  have hR := hR1.trans (hR2.trans (congrArg (fun t : ℝ => D * t) hR3))
  have hDC : D = ∫ y in A, Φ ((Submission.BoseGases.kcInsN N i) (y, r)) * f y := by
    rw [hDdef]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
    ring
  rw [hL, hR, hDC]

/-! ## The theorem -/

theorem boxOpG_adjoint {N : ℕ} {a : ℝ} (ha : 0 < a)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hAm : MeasurableSet A)
    (hAc : A ⊆ Submission.BoseGases.acube a)
    {f h : EuclideanSpace ℝ (Fin 3) → ℝ} (hf : Continuous f) (hh : Continuous h)
    (hsh : tsupport h ⊆ A)
    {Φ : Submission.BoseGases.X (N + 1) → ℝ} (hΦm : Measurable Φ)
    {CΦ : ℝ} (hΦb : ∀ x ∈ Submission.BoseGases.abox (N + 1) a, |Φ x| ≤ CΦ)
    {Ψ : Submission.BoseGases.X (N + 1) → ℝ} (hΨ : Continuous Ψ) :
    ∫ x in Submission.BoseGases.abox (N + 1) a, Φ x * Work.BoseFixB1.boxOpG A f h Ψ x
      = ∫ x in Submission.BoseGases.abox (N + 1) a, Work.BoseFixB1.boxOpZ A h f Φ x * Ψ x := by
  unfold boxOpG boxOpZ
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [MeasureTheory.integral_finsetSum Finset.univ
        (fun i _ => integrableOn_slotG ha hAm hAc hf hh i hΦm hΦb hΨ),
      MeasureTheory.integral_finsetSum Finset.univ
        (fun i _ => integrableOn_slotZ ha hAm hAc hf hh i hΦm hΦb hΨ)]
  exact Finset.sum_congr rfl (fun i _ => slot_adjoint ha hAm hAc hf hh hsh hΦm hΦb hΨ i)

end Work.BoseFixB1
