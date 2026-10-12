import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB1S.BoxQWords
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1S.BoxQIndCore` — the box-projection square identities

The FS-faithful box projection `boxPInd volA A i` (`Work.UBBInputs8.boxPInd`,
`P_{B,i}ψ = |B|⁻¹⟨1_B,ψ⟩1_B` in slot `i`) carries the box indicator, so it is *not* constant in
the `i`-th slot, but it factors as

  `(P_iψ)(x) = 1_A(x i) · (1/volA)·∫_{z∈A} ψ(x|i↦z) dz`,

and for `i ≠ j` the two-fold projection is

  `(P_iP_jψ)(x) = 1_A(x i)·1_A(x j)·M(x)`,  `M` independent of the slots `i,j`.

This module records that structure, the slot means `oneRest`/`pairRest`, and their
boundedness/measurability/integrability.
-/

noncomputable section

namespace Work.BoseFixB1S

open MeasureTheory
open scoped ENNReal
open Submission.BoseGases

namespace Q0C

/-! ## 1. Pointwise structure of `boxPInd` -/

/-- `P_i` at an inserted configuration: the box indicator times the one-slot mean. -/
theorem boxPInd_kcInsN {n : ℕ} (volA : ℝ) (A : Set kcE3) (i : Fin (n + 1))
    (Ψ : X (n + 1) → ℝ) (t : kcE3) (r : X n) :
    Work.UBBInputs8.boxPInd volA A i Ψ (kcInsN n i (t, r))
      = A.indicator (fun _ => (1 : ℝ)) t
        * ((1 / volA) * ∫ z in A, Ψ (kcInsN n i (z, r))) := by
  simp only [Work.UBBInputs8.boxPInd, kc_insN_apply_same, update_kcInsN]
  try ring

/-- `P_i` at a configuration whose `i`-th slot has been updated: the indicator sits on the new
value, the mean does not see it. -/
theorem boxPInd_update_self {N : ℕ} (volA : ℝ) (A : Set kcE3) (i : Fin N)
    (Ψ : X N → ℝ) (x : X N) (u : kcE3) :
    Work.UBBInputs8.boxPInd volA A i Ψ (Function.update x i u)
      = (1 / volA) * (∫ z in A, Ψ (Function.update x i z))
        * A.indicator (fun _ => (1 : ℝ)) u := by
  simp only [Work.UBBInputs8.boxPInd, Function.update_idem, Function.update_self]
  try ring

/-- The two-fold projection at a doubly inserted configuration: the product of the two box
indicators times the slot-independent double mean. -/
theorem boxPInd_pair_ins2 {p : ℕ} (volA : ℝ) (A : Set kcE3) (i : Fin (p + 2))
    (j' : Fin (p + 1)) (Ψ : X (p + 2) → ℝ) (y z : kcE3) (r2 : X p) :
    Work.UBBInputs8.boxPInd volA A i
        (Work.UBBInputs8.boxPInd volA A (i.succAbove j') Ψ) (ins2 i j' y z r2)
      = A.indicator (fun _ => (1 : ℝ)) y * A.indicator (fun _ => (1 : ℝ)) z
        * ((1 / volA) * ((1 / volA) * ∫ u in A, ∫ w in A, Ψ (ins2 i j' u w r2))) := by
  simp only [Work.UBBInputs8.boxPInd, ins2_apply_i, ins2_update_i, ins2_update_succ,
    ins2_apply_succ]
  rw [MeasureTheory.integral_mul_const, MeasureTheory.integral_const_mul]
  ring

/-! ## 2. The slot means -/

/-- The one-slot mean of `Ψ` over `A` (independent of the `i`-th slot). -/
noncomputable def oneRest (volA : ℝ) (A : Set kcE3) {n : ℕ} (i : Fin (n + 1))
    (Ψ : X (n + 1) → ℝ) (r : X n) : ℝ :=
  (1 / volA) * ∫ u in A, Ψ (kcInsN n i (u, r))

/-- The two-slot mean of `Ψ` over `A × A` (independent of both distinguished slots). -/
noncomputable def pairRest (volA : ℝ) (A : Set kcE3) {p : ℕ} (i : Fin (p + 2)) (j' : Fin (p + 1))
    (Ψ : X (p + 2) → ℝ) (r2 : X p) : ℝ :=
  (1 / volA) * ((1 / volA) * ∫ u in A, ∫ w in A, Ψ (ins2 i j' u w r2))

theorem oneRest_def {n : ℕ} (volA : ℝ) (A : Set kcE3) (i : Fin (n + 1))
    (Ψ : X (n + 1) → ℝ) (r : X n) :
    oneRest volA A i Ψ r = (1 / volA) * ∫ u in A, Ψ (kcInsN n i (u, r)) := rfl

theorem pairRest_def {p : ℕ} (volA : ℝ) (A : Set kcE3) (i : Fin (p + 2)) (j' : Fin (p + 1))
    (Ψ : X (p + 2) → ℝ) (r2 : X p) :
    pairRest volA A i j' Ψ r2
      = (1 / volA) * ((1 / volA) * ∫ u in A, ∫ w in A, Ψ (ins2 i j' u w r2)) := rfl

/-- The squared pair projection is the product of the two box indicators times the square of
the slot-independent double mean. -/
theorem boxPInd_pair_ins2_sq {p : ℕ} (volA : ℝ) (A : Set kcE3) (i : Fin (p + 2))
    (j' : Fin (p + 1)) (Ψ : X (p + 2) → ℝ) (y z : kcE3) (r2 : X p) :
    (Work.UBBInputs8.boxPInd volA A i
        (Work.UBBInputs8.boxPInd volA A (i.succAbove j') Ψ) (ins2 i j' y z r2)) ^ 2
      = A.indicator (fun _ => (1 : ℝ)) y * A.indicator (fun _ => (1 : ℝ)) z
        * (pairRest volA A i j' Ψ r2) ^ 2 := by
  rw [boxPInd_pair_ins2, pairRest_def]
  by_cases hy : y ∈ A <;> by_cases hz : z ∈ A <;>
    simp [Set.indicator_of_mem, Set.indicator_of_notMem, hy, hz]

/-- The one-slot projection satisfies `(P_iΨ)(x)² = 1_A(x i)·(oneRest)²`. -/
theorem boxPInd_sq_kcInsN {n : ℕ} (volA : ℝ) (A : Set kcE3) (i : Fin (n + 1))
    (Ψ : X (n + 1) → ℝ) (t : kcE3) (r : X n) :
    (Work.UBBInputs8.boxPInd volA A i Ψ (kcInsN n i (t, r))) ^ 2
      = A.indicator (fun _ => (1 : ℝ)) t * (oneRest volA A i Ψ r) ^ 2 := by
  rw [boxPInd_kcInsN, oneRest_def]
  by_cases ht : t ∈ A <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, ht]

/-! ## 3. Membership of the inserted configurations -/

theorem kcInsN_mem_abox {n : ℕ} {ℓ : ℝ} {A : Set kcE3} (hAc : A ⊆ acube ℓ) (i : Fin (n + 1))
    {u : kcE3} (hu : u ∈ A) {r : X n} (hr : r ∈ abox n ℓ) :
    kcInsN n i (u, r) ∈ abox (n + 1) ℓ := by
  intro k
  by_cases hk : k = i
  · subst hk
    simpa [kc_insN_apply_same] using hAc hu
  · rcases Fin.exists_succAbove_eq hk with ⟨j, hj⟩
    rw [← hj, kc_insN_apply_succ]
    exact hr j

theorem ins2_mem_abox {p : ℕ} {ℓ : ℝ} {A : Set kcE3} (hAc : A ⊆ acube ℓ) (i : Fin (p + 2))
    (j' : Fin (p + 1)) {y z : kcE3} (hy : y ∈ A) (hz : z ∈ A) {r2 : X p}
    (hr2 : r2 ∈ abox p ℓ) : ins2 i j' y z r2 ∈ abox (p + 2) ℓ := by
  intro k
  dsimp [ins2]
  by_cases hk : k = i
  · subst hk
    simpa [kc_insN_apply_same] using hAc hy
  · by_cases hkj : k = i.succAbove j'
    · subst hkj
      rw [kc_insN_apply_succ]
      simpa [kc_insN_apply_same] using hAc hz
    · rcases Fin.exists_succAbove_eq hk with ⟨l, hl⟩
      rw [← hl]
      have hlne : l ≠ j' := by
        intro hlj
        exact hkj (by rw [← hl, hlj])
      rw [kc_insN_apply_succ]
      rcases Fin.exists_succAbove_eq hlne with ⟨m, hm⟩
      rw [← hm, kc_insN_apply_succ]
      exact hr2 m

/-! ## 4. Boundedness, measurability and integrability of the slot means -/

theorem volume_A_lt_top {ℓ : ℝ} (hℓ : 0 < ℓ) {A : Set kcE3} (hAc : A ⊆ acube ℓ) :
    (volume : Measure kcE3) A < ∞ :=
  lt_of_le_of_lt (measure_mono hAc)
    (by rw [acube_volume ℓ hℓ.le]; exact ENNReal.ofReal_lt_top)

theorem abs_pairRest_le {p : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set kcE3} (hAc : A ⊆ acube ℓ) (hvolA : volA = (volume : Measure kcE3).real A)
    (i : Fin (p + 2)) (j' : Fin (p + 1)) {Ψ : X (p + 2) → ℝ} (hΨc : Continuous Ψ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ r2 ∈ abox p ℓ, |pairRest volA A i j' Ψ r2| ≤ B := by
  obtain ⟨B, hB⟩ := (abox_compact (p + 2) hℓ).exists_bound_of_continuousOn
    (s := abox (p + 2) ℓ) (f := Ψ) hΨc.continuousOn
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB _ (zero_mem_abox hℓ.le))
  refine ⟨B, hB0, ?_⟩
  intro r2 hr2
  have hfin := volume_A_lt_top hℓ hAc
  have hinner : ∀ u ∈ A, ‖∫ w in A, Ψ (ins2 i j' u w r2)‖
      ≤ B * (volume : Measure kcE3).real A :=
    fun u hu => norm_setIntegral_le_of_norm_le_const hfin
      (fun w hw => hB _ (ins2_mem_abox hAc i j' hu hw hr2))
  have houter : ‖∫ u in A, ∫ w in A, Ψ (ins2 i j' u w r2)‖ ≤ (B * volA) * volA := by
    have := norm_setIntegral_le_of_norm_le_const hfin hinner
    rwa [← hvolA] at this
  have h1 : |∫ u in A, ∫ w in A, Ψ (ins2 i j' u w r2)| ≤ (B * volA) * volA := by
    simpa [Real.norm_eq_abs] using houter
  have hrepr : |pairRest volA A i j' Ψ r2|
      = (1 / volA) * ((1 / volA) * |∫ u in A, ∫ w in A, Ψ (ins2 i j' u w r2)|) := by
    simp only [pairRest_def, abs_mul, abs_of_pos (one_div_pos.mpr hvol)]
  rw [hrepr]
  have h0 : 0 ≤ (1 / volA) * (1 / volA) := by positivity
  have h2 : (1 / volA) * ((1 / volA) * ((B * volA) * volA)) = B := by
    field_simp
  calc (1 / volA) * ((1 / volA) * |∫ u in A, ∫ w in A, Ψ (ins2 i j' u w r2)|)
      ≤ (1 / volA) * ((1 / volA) * ((B * volA) * volA)) := by
        nlinarith [h1, h0, mul_le_mul_of_nonneg_right h1 h0]
    _ = B := h2

theorem abs_oneRest_le {n : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set kcE3} (hAc : A ⊆ acube ℓ) (hvolA : volA = (volume : Measure kcE3).real A)
    (i : Fin (n + 1)) {Ψ : X (n + 1) → ℝ} (hΨc : Continuous Ψ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ r ∈ abox n ℓ, |oneRest volA A i Ψ r| ≤ B := by
  obtain ⟨B, hB⟩ := (abox_compact (n + 1) hℓ).exists_bound_of_continuousOn
    (s := abox (n + 1) ℓ) (f := Ψ) hΨc.continuousOn
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB _ (zero_mem_abox hℓ.le))
  refine ⟨B, hB0, ?_⟩
  intro r hr
  have hfin := volume_A_lt_top hℓ hAc
  have hb : ‖∫ u in A, Ψ (kcInsN n i (u, r))‖ ≤ B * volA := by
    have := norm_setIntegral_le_of_norm_le_const hfin
      (fun u hu => hB _ (kcInsN_mem_abox hAc i hu hr))
    rwa [← hvolA] at this
  have h1 : |∫ u in A, Ψ (kcInsN n i (u, r))| ≤ B * volA := by
    simpa [Real.norm_eq_abs] using hb
  have hrepr : |oneRest volA A i Ψ r|
      = (1 / volA) * |∫ u in A, Ψ (kcInsN n i (u, r))| := by
    simp only [oneRest_def, abs_mul, abs_of_pos (one_div_pos.mpr hvol)]
  rw [hrepr]
  have h2 : (1 / volA) * (B * volA) = B := by field_simp
  calc (1 / volA) * |∫ u in A, Ψ (kcInsN n i (u, r))|
      ≤ (1 / volA) * (B * volA) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = B := h2

theorem aem_oneRest {n : ℕ} {ℓ : ℝ} (volA : ℝ) (A : Set kcE3) (i : Fin (n + 1))
    {Ψ : X (n + 1) → ℝ} (hΨm : Measurable Ψ) :
    AEStronglyMeasurable (fun r : X n => ∫ u in A, Ψ (kcInsN n i (u, r)))
      (volume.restrict (abox n ℓ)) := by
  have hsm : StronglyMeasurable
      (Function.uncurry (fun (r : X n) (u : kcE3) => Ψ (kcInsN n i (u, r)))) := by
    have hmap : Measurable (fun q : X n × kcE3 => kcInsN n i (q.2, q.1)) :=
      (kcInsN n i).measurable.comp (MeasurableEquiv.prodComm).measurable
    exact (hΨm.comp hmap).stronglyMeasurable
  exact (StronglyMeasurable.integral_prod_right (ν := (volume : Measure kcE3).restrict A)
    (f := fun (r : X n) (u : kcE3) => Ψ (kcInsN n i (u, r))) hsm).aestronglyMeasurable

theorem integrableOn_oneRest_sq {n : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set kcE3} (hAc : A ⊆ acube ℓ) (hvolA : volA = (volume : Measure kcE3).real A)
    (i : Fin (n + 1)) {Ψ : X (n + 1) → ℝ} (hΨc : Continuous Ψ) :
    IntegrableOn (fun r : X n => (oneRest volA A i Ψ r) ^ 2) (abox n ℓ) volume := by
  obtain ⟨B, hB0, hB⟩ := abs_oneRest_le (volA := volA) hℓ hvol hAc hvolA i hΨc
  have hfin : (volume : Measure (X n)) (abox n ℓ) < ∞ := abox_lt_top n ℓ hℓ.le
  have hconst : IntegrableOn (fun _ : X n => B ^ 2) (abox n ℓ) volume :=
    integrableOn_const hfin.ne
  refine Integrable.mono' hconst ?_ ?_
  · have h1 : AEStronglyMeasurable (fun r : X n => oneRest volA A i Ψ r)
        (volume.restrict (abox n ℓ)) := by
      simpa only [oneRest_def] using
        (aem_oneRest (ℓ := ℓ) volA A i hΨc.measurable).const_mul (1 / volA)
    exact h1.pow 2
  · filter_upwards [self_mem_ae_restrict (abox_measurable n ℓ)] with r hr
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg (oneRest volA A i Ψ r)) (hB r hr) 2

theorem aem_pairRest {p : ℕ} {ℓ : ℝ} (volA : ℝ) (A : Set kcE3) (i : Fin (p + 2))
    (j' : Fin (p + 1)) {Ψ : X (p + 2) → ℝ} (hΨm : Measurable Ψ) :
    AEStronglyMeasurable (fun r2 : X p => pairRest volA A i j' Ψ r2)
      (volume.restrict (abox p ℓ)) := by
  have hmap : Measurable (fun z : (kcE3 × X p) × kcE3 => ins2 i j' z.1.1 z.2 z.1.2) := by
    have h2 : Measurable (fun z : (kcE3 × X p) × kcE3 => (kcInsN p j') (z.2, z.1.2)) :=
      (kcInsN p j').measurable.comp (Measurable.prodMk measurable_snd
        (measurable_snd.comp measurable_fst))
    have h3 : Measurable (fun z : (kcE3 × X p) × kcE3 =>
        (z.1.1, (kcInsN p j') (z.2, z.1.2))) :=
      Measurable.prodMk (measurable_fst.comp measurable_fst) h2
    exact (kcInsN (p + 1) i).measurable.comp h3
  have hsm : StronglyMeasurable
      (Function.uncurry (fun (q : kcE3 × X p) (w : kcE3) => Ψ (ins2 i j' q.1 w q.2))) :=
    (hΨm.comp hmap).stronglyMeasurable
  have h1 := StronglyMeasurable.integral_prod_right (ν := (volume : Measure kcE3).restrict A)
    (f := fun (q : kcE3 × X p) (w : kcE3) => Ψ (ins2 i j' q.1 w q.2)) hsm
  have h2 := StronglyMeasurable.integral_prod_left' (μ := (volume : Measure kcE3).restrict A) h1
  simpa only [pairRest_def] using
    (h2.aestronglyMeasurable.const_mul (1 / volA)).const_mul (1 / volA)

theorem integrableOn_pairRest_sq {p : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set kcE3} (hAc : A ⊆ acube ℓ) (hvolA : volA = (volume : Measure kcE3).real A)
    (i : Fin (p + 2)) (j' : Fin (p + 1)) {Ψ : X (p + 2) → ℝ} (hΨc : Continuous Ψ) :
    IntegrableOn (fun r2 : X p => (pairRest volA A i j' Ψ r2) ^ 2) (abox p ℓ) volume := by
  obtain ⟨B, hB0, hB⟩ := abs_pairRest_le (volA := volA) hℓ hvol hAc hvolA i j' hΨc
  have hfin : (volume : Measure (X p)) (abox p ℓ) < ∞ := abox_lt_top p ℓ hℓ.le
  have hconst : IntegrableOn (fun _ : X p => B ^ 2) (abox p ℓ) volume :=
    integrableOn_const hfin.ne
  refine Integrable.mono' hconst ?_ ?_
  · have h1 : AEStronglyMeasurable (fun r2 : X p => pairRest volA A i j' Ψ r2)
        (volume.restrict (abox p ℓ)) :=
      aem_pairRest (ℓ := ℓ) volA A i j' hΨc.measurable
    exact h1.pow 2
  · filter_upwards [self_mem_ae_restrict (abox_measurable p ℓ)] with r2 hr2
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    simpa [sq_abs] using
      pow_le_pow_left₀ (abs_nonneg (pairRest volA A i j' Ψ r2)) (hB r2 hr2) 2

/-! ## 5. Transport and the one-slot peel identities -/

/-- Transport of a configuration-box integral to the product of the `i`-th slot and the
remaining coordinates. -/
theorem abox_peel_transport {n : ℕ} {ℓ : ℝ} (i : Fin (n + 1)) (F : X (n + 1) → ℝ) :
    (∫ x in abox (n + 1) ℓ, F x)
      = ∫ q : kcE3 × X n, F (kcInsN n i q)
          ∂(((volume : Measure kcE3).restrict (acube ℓ)).prod
            ((volume : Measure (X n)).restrict (abox n ℓ))) := by
  rw [← (abox_peel_mp (n := n) ℓ i).integral_comp'
    (fun q : kcE3 × X n => F (kcInsN n i q))]
  apply integral_congr_ae
  filter_upwards with x
  have hx : kcInsN n i
      ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => kcE3) i) x) = x :=
    MeasurableEquiv.symm_apply_apply _ x
  simp only [hx]

theorem one_kernel {n : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA) {A : Set kcE3}
    (hA : MeasurableSet A) (hAc : A ⊆ acube ℓ)
    (hvolA : volA = (volume : Measure kcE3).real A) (i : Fin (n + 1))
    {Ψ : X (n + 1) → ℝ} (hΨc : Continuous Ψ)
    {g : kcE3 → ℝ} (hg : Integrable g (volume.restrict A)) :
    (∫ x in abox (n + 1) ℓ, (Work.UBBInputs8.boxPInd volA A i Ψ x) ^ 2 * g (x i))
      = (∫ z in A, g z) * (∫ r in abox n ℓ, (oneRest volA A i Ψ r) ^ 2) := by
  rw [abox_peel_transport (n := n) (ℓ := ℓ) i
    (fun x => (Work.UBBInputs8.boxPInd volA A i Ψ x) ^ 2 * g (x i))]
  have hpoint : ∀ q : kcE3 × X n,
      (Work.UBBInputs8.boxPInd volA A i Ψ (kcInsN n i q)) ^ 2 * g ((kcInsN n i q) i)
        = (A.indicator (fun _ => (1 : ℝ)) q.1 * g q.1) * (oneRest volA A i Ψ q.2) ^ 2 := by
    intro q
    rcases q with ⟨t, r⟩
    rw [boxPInd_sq_kcInsN, kc_insN_apply_same]
    by_cases ht : t ∈ A
    · simp only [Set.indicator_of_mem ht]
      ring
    · simp only [Set.indicator_of_notMem ht]
      ring
  simp only [hpoint]
  haveI : IsFiniteMeasure ((volume : Measure kcE3).restrict (acube ℓ)) :=
    ⟨by rw [Measure.restrict_apply_univ, acube_volume ℓ hℓ.le]; exact ENNReal.ofReal_lt_top⟩
  haveI : IsFiniteMeasure ((volume : Measure (X n)).restrict (abox n ℓ)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact abox_lt_top n ℓ hℓ.le⟩
  have hgA : Integrable (fun t : kcE3 => A.indicator (fun _ => (1 : ℝ)) t * g t)
      ((volume : Measure kcE3).restrict (acube ℓ)) := by
    have hEq : (fun t : kcE3 => A.indicator (fun _ => (1 : ℝ)) t * g t) = A.indicator g := by
      funext t
      by_cases ht : t ∈ A <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, ht]
    rw [hEq, MeasureTheory.integrable_indicator_iff hA]
    have hg' : Integrable g ((volume : Measure kcE3).restrict (acube ℓ) |>.restrict A) := by
      rw [Measure.restrict_restrict_of_subset (μ := (volume : Measure kcE3)) hAc]
      exact hg
    exact hg'
  have hgr := integrableOn_oneRest_sq (volA := volA) hℓ hvol hAc hvolA i hΨc
  have hprod : Integrable (fun q : kcE3 × X n =>
      (A.indicator (fun _ => (1 : ℝ)) q.1 * g q.1) * (oneRest volA A i Ψ q.2) ^ 2)
      (((volume : Measure kcE3).restrict (acube ℓ)).prod
        ((volume : Measure (X n)).restrict (abox n ℓ))) :=
    Integrable.smul_prod hgA hgr
  rw [MeasureTheory.integral_prod _ hprod]
  have hstep : (∫ t in acube ℓ, ∫ r in abox n ℓ,
        (A.indicator (fun _ => (1 : ℝ)) t * g t) * (oneRest volA A i Ψ r) ^ 2)
      = ∫ t in acube ℓ, (A.indicator (fun _ => (1 : ℝ)) t * g t)
          * (∫ r in abox n ℓ, (oneRest volA A i Ψ r) ^ 2) := by
    apply integral_congr_ae
    filter_upwards with t
    rw [MeasureTheory.integral_const_mul]
  rw [hstep, MeasureTheory.integral_mul_const]
  have hlast : (∫ t in acube ℓ, A.indicator (fun _ => (1 : ℝ)) t * g t) = ∫ z in A, g z := by
    have hEq : (fun t : kcE3 => A.indicator (fun _ => (1 : ℝ)) t * g t) = A.indicator g := by
      funext t
      by_cases ht : t ∈ A <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, ht]
    rw [hEq, MeasureTheory.setIntegral_indicator hA, Set.inter_eq_right.mpr hAc]
  rw [hlast]

/-- The product of the restricted slot measures equals the restricted product measure. -/
theorem prod_restrict_acube (n : ℕ) (ℓ : ℝ) :
    (((volume : Measure kcE3).restrict (acube ℓ)).prod
        ((volume : Measure (X n)).restrict (abox n ℓ)))
      = (volume : Measure (kcE3 × X n)).restrict (acube ℓ ×ˢ abox n ℓ) :=
  Measure.prod_restrict (acube ℓ) (abox n ℓ)

theorem one_flat {n : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA) {A : Set kcE3}
    (hA : MeasurableSet A) (hAc : A ⊆ acube ℓ)
    (hvolA : volA = (volume : Measure kcE3).real A) (i : Fin (n + 1))
    {Ψ : X (n + 1) → ℝ} (hΨc : Continuous Ψ) :
    (∫ x in abox (n + 1) ℓ, (Work.UBBInputs8.boxPInd volA A i Ψ x) ^ 2)
      = volA * (∫ r in abox n ℓ, (oneRest volA A i Ψ r) ^ 2) := by
  have hAfin := volume_A_lt_top hℓ hAc
  have hg : Integrable (fun _ : kcE3 => (1 : ℝ)) (volume.restrict A) :=
    integrableOn_const hAfin.ne
  have h := one_kernel (volA := volA) hℓ hvol hA hAc hvolA i hΨc hg
  have hc : (∫ z in A, (1 : ℝ)) = volA := by
    rw [MeasureTheory.setIntegral_const, smul_eq_mul, mul_one]
    exact hvolA.symm
  rw [hc] at h
  simpa using h

theorem one_self {n : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA) {A : Set kcE3}
    (hA : MeasurableSet A) (hAc : A ⊆ acube ℓ)
    (hvolA : volA = (volume : Measure kcE3).real A) (i : Fin (n + 1))
    {Ψ : X (n + 1) → ℝ} (hΨc : Continuous Ψ) :
    (∫ x in abox (n + 1) ℓ, Ψ x * Work.UBBInputs8.boxPInd volA A i Ψ x)
      = volA * (∫ r in abox n ℓ, (oneRest volA A i Ψ r) ^ 2) := by
  rw [abox_peel_transport (n := n) (ℓ := ℓ) i
    (fun x => Ψ x * Work.UBBInputs8.boxPInd volA A i Ψ x)]
  have hpoint : ∀ q : kcE3 × X n,
      Ψ (kcInsN n i q) * Work.UBBInputs8.boxPInd volA A i Ψ (kcInsN n i q)
        = Ψ (kcInsN n i q) * (A.indicator (fun _ => (1 : ℝ)) q.1
            * oneRest volA A i Ψ q.2) := by
    intro q
    rcases q with ⟨t, r⟩
    rw [boxPInd_kcInsN, oneRest_def]
    try ring
  simp only [hpoint]
  haveI : IsFiniteMeasure ((volume : Measure kcE3).restrict (acube ℓ)) :=
    ⟨by rw [Measure.restrict_apply_univ, acube_volume ℓ hℓ.le]; exact ENNReal.ofReal_lt_top⟩
  haveI : IsFiniteMeasure ((volume : Measure (X n)).restrict (abox n ℓ)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact abox_lt_top n ℓ hℓ.le⟩
  obtain ⟨B, hB⟩ := (abox_compact (n + 1) hℓ).exists_bound_of_continuousOn
    (s := abox (n + 1) ℓ) (f := Ψ) hΨc.continuousOn
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB _ (zero_mem_abox hℓ.le))
  obtain ⟨C, hC0, hC⟩ := abs_oneRest_le (volA := volA) hℓ hvol hAc hvolA i hΨc
  have hmems : ∀ᵐ q ∂(((volume : Measure kcE3).restrict (acube ℓ)).prod
        ((volume : Measure (X n)).restrict (abox n ℓ))),
      q.1 ∈ acube ℓ ∧ q.2 ∈ abox n ℓ := by
    have hmem : ∀ᵐ q ∂(volume : Measure (kcE3 × X n)).restrict (acube ℓ ×ˢ abox n ℓ),
        q ∈ acube ℓ ×ˢ abox n ℓ :=
      self_mem_ae_restrict ((acube_measurable ℓ).prod (abox_measurable n ℓ))
    rw [← prod_restrict_acube n ℓ] at hmem
    simpa [Set.mem_prod] using hmem
  have hbnd : ∀ᵐ q ∂(((volume : Measure kcE3).restrict (acube ℓ)).prod
        ((volume : Measure (X n)).restrict (abox n ℓ))),
      ‖Ψ (kcInsN n i q) * (A.indicator (fun _ => (1 : ℝ)) q.1
          * oneRest volA A i Ψ q.2)‖ ≤ B * C := by
    filter_upwards [hmems] with q hq
    obtain ⟨hq1, hq2⟩ := hq
    by_cases ht : q.1 ∈ A
    · have h1 : |Ψ (kcInsN n i q)| ≤ B := by
        simpa [Real.norm_eq_abs] using hB _ (kcInsN_mem_abox hAc i ht hq2)
      have h2 : |oneRest volA A i Ψ q.2| ≤ C := hC q.2 hq2
      rw [Set.indicator_of_mem ht, one_mul, Real.norm_eq_abs, abs_mul]
      exact mul_le_mul h1 h2 (abs_nonneg _) hB0
    · rw [Set.indicator_of_notMem ht, zero_mul, mul_zero, norm_zero]
      exact mul_nonneg hB0 hC0
  have hmeas_one : AEStronglyMeasurable (fun q : kcE3 × X n => oneRest volA A i Ψ q.2)
      (((volume : Measure kcE3).restrict (acube ℓ)).prod
        ((volume : Measure (X n)).restrict (abox n ℓ))) := by
    have h := ((aem_oneRest (ℓ := ℓ) volA A i hΨc.measurable).comp_snd
      (μ := (volume : Measure kcE3).restrict (acube ℓ))).const_mul (1 / volA)
    simpa only [oneRest_def] using h
  have hmeas : AEStronglyMeasurable (fun q : kcE3 × X n =>
      Ψ (kcInsN n i q) * (A.indicator (fun _ => (1 : ℝ)) q.1 * oneRest volA A i Ψ q.2))
      (((volume : Measure kcE3).restrict (acube ℓ)).prod
        ((volume : Measure (X n)).restrict (abox n ℓ))) :=
    ((hΨc.measurable.comp (kcInsN n i).measurable).aestronglyMeasurable).mul
      (((measurable_const.indicator hA).comp measurable_fst).aestronglyMeasurable.mul hmeas_one)
  have hprod : Integrable (fun q : kcE3 × X n =>
      Ψ (kcInsN n i q) * (A.indicator (fun _ => (1 : ℝ)) q.1 * oneRest volA A i Ψ q.2))
      (((volume : Measure kcE3).restrict (acube ℓ)).prod
        ((volume : Measure (X n)).restrict (abox n ℓ))) :=
    Integrable.mono' (integrable_const (B * C)) hmeas hbnd
  rw [MeasureTheory.integral_prod_symm _ hprod]
  have hstep : (∫ r in abox n ℓ, ∫ t in acube ℓ,
        Ψ (kcInsN n i (t, r)) * (A.indicator (fun _ => (1 : ℝ)) t * oneRest volA A i Ψ r))
      = ∫ r in abox n ℓ, (∫ t in acube ℓ, Ψ (kcInsN n i (t, r))
          * A.indicator (fun _ => (1 : ℝ)) t) * oneRest volA A i Ψ r := by
    apply integral_congr_ae
    filter_upwards with r
    have hcomm : (∫ t in acube ℓ,
          Ψ (kcInsN n i (t, r)) * (A.indicator (fun _ => (1 : ℝ)) t * oneRest volA A i Ψ r))
        = ∫ t in acube ℓ, (Ψ (kcInsN n i (t, r)) * A.indicator (fun _ => (1 : ℝ)) t)
            * oneRest volA A i Ψ r := by
      apply integral_congr_ae
      filter_upwards with t
      ring
    rw [hcomm, MeasureTheory.integral_mul_const]
  rw [hstep]
  have hinner : (∫ r in abox n ℓ, (∫ t in acube ℓ, Ψ (kcInsN n i (t, r))
        * A.indicator (fun _ => (1 : ℝ)) t) * oneRest volA A i Ψ r)
      = ∫ r in abox n ℓ, (volA * oneRest volA A i Ψ r) * oneRest volA A i Ψ r := by
    apply integral_congr_ae
    filter_upwards with r
    have hEq : (fun t : kcE3 => Ψ (kcInsN n i (t, r)) * A.indicator (fun _ => (1 : ℝ)) t)
        = A.indicator (fun t : kcE3 => Ψ (kcInsN n i (t, r))) := by
      funext t
      by_cases ht : t ∈ A <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, ht]
    have hone : (∫ t in acube ℓ, Ψ (kcInsN n i (t, r)) * A.indicator (fun _ => (1 : ℝ)) t)
        = volA * oneRest volA A i Ψ r := by
      rw [hEq, MeasureTheory.setIntegral_indicator hA, Set.inter_eq_right.mpr hAc, oneRest_def]
      have hX : volA * ((1 / volA) * (∫ t in A, Ψ (kcInsN n i (t, r))))
          = ∫ t in A, Ψ (kcInsN n i (t, r)) := by
        field_simp [ne_of_gt hvol]
      exact hX.symm
    rw [hone]
  rw [hinner]
  have hlast : (∫ r in abox n ℓ, (volA * oneRest volA A i Ψ r) * oneRest volA A i Ψ r)
      = ∫ r in abox n ℓ, volA * (oneRest volA A i Ψ r) ^ 2 := by
    apply integral_congr_ae
    filter_upwards with r
    ring
  rw [hlast, MeasureTheory.integral_const_mul]

/-! ## 6. The two-slot peel -/

/-- The restricted product measure on `A × A` is the product of the restricted measures. -/
theorem prod_measure_eq_A (A : Set kcE3) :
    (volume : Measure (kcE3 × kcE3)).restrict (A ×ˢ A)
      = ((volume : Measure kcE3).restrict A).prod ((volume : Measure kcE3).restrict A) :=
  (Measure.prod_restrict (μ := (volume : Measure kcE3)) (ν := (volume : Measure kcE3)) A A).symm

/-- The indicator-form integrability on `A × A` transfers to the two-cube product measure. -/
theorem integrable_indicator_pair {ℓ : ℝ} {A : Set kcE3} (hA : MeasurableSet A)
    (hAc : A ⊆ acube ℓ) {h : kcE3 → kcE3 → ℝ}
    (hh : Integrable (fun q : kcE3 × kcE3 => h q.1 q.2) (volume.restrict (A ×ˢ A))) :
    Integrable (fun q : kcE3 × kcE3 => A.indicator (fun _ => (1 : ℝ)) q.1
        * A.indicator (fun _ => (1 : ℝ)) q.2 * h q.1 q.2)
      (((volume : Measure kcE3).restrict (acube ℓ)).prod
        ((volume : Measure kcE3).restrict (acube ℓ))) := by
  have hEq : (fun q : kcE3 × kcE3 => A.indicator (fun _ => (1 : ℝ)) q.1
        * A.indicator (fun _ => (1 : ℝ)) q.2 * h q.1 q.2)
      = (A ×ˢ A).indicator (fun q : kcE3 × kcE3 => h q.1 q.2) := by
    funext q
    by_cases h1 : q.1 ∈ A <;> by_cases h2 : q.2 ∈ A <;>
      simp [Set.mem_prod, Set.indicator_of_mem, Set.indicator_of_notMem, h1, h2]
  rw [hEq, MeasureTheory.integrable_indicator_iff (hA.prod hA)]
  have hgoal : Integrable (fun q : kcE3 × kcE3 => h q.1 q.2)
      ((((volume : Measure kcE3).restrict (acube ℓ)).prod
        ((volume : Measure kcE3).restrict (acube ℓ))).restrict (A ×ˢ A)) := by
    rw [← Measure.prod_restrict,
      Measure.restrict_restrict_of_subset (μ := (volume : Measure kcE3)) hAc,
      ← prod_measure_eq_A A]
    exact hh
  exact hgoal

/-- The two-slot insertion map as a measurable equivalence. -/
noncomputable def eIns2 {p : ℕ} (i : Fin (p + 2)) (j' : Fin (p + 1)) :
    ((kcE3 × kcE3) × X p) ≃ᵐ X (p + 2) :=
  (MeasurableEquiv.prodAssoc.trans
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl kcE3) (kcInsN p j'))).trans
    (kcInsN (p + 1) i)

theorem eIns2_apply {p : ℕ} (i : Fin (p + 2)) (j' : Fin (p + 1)) (q : (kcE3 × kcE3) × X p) :
    eIns2 i j' q = ins2 i j' q.1.1 q.1.2 q.2 := rfl

theorem eIns2_apply_i {p : ℕ} (i : Fin (p + 2)) (j' : Fin (p + 1))
    (q : (kcE3 × kcE3) × X p) : eIns2 i j' q i = q.1.1 := by
  rw [eIns2_apply]
  exact ins2_apply_i i j' q.1.1 q.1.2 q.2

theorem eIns2_apply_succ {p : ℕ} (i : Fin (p + 2)) (j' : Fin (p + 1))
    (q : (kcE3 × kcE3) × X p) : eIns2 i j' q (i.succAbove j') = q.1.2 := by
  rw [eIns2_apply]
  exact ins2_apply_succ i j' q.1.1 q.1.2 q.2

/-- The two-slot insertion map is measure preserving (from the two cube measures times the
remaining box to the `(p+2)`-box). -/
theorem mp_eIns2 {p : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin (p + 2)) (j' : Fin (p + 1)) :
    MeasurePreserving (⇑(eIns2 i j'))
      ((((volume : Measure kcE3).restrict (acube ℓ)).prod
          ((volume : Measure kcE3).restrict (acube ℓ))).prod
        ((volume : Measure (X p)).restrict (abox p ℓ)))
      ((volume : Measure (X (p + 2))).restrict (abox (p + 2) ℓ)) := by
  have h := ins2_flat_mp (p := p) hℓ i j'
  have hfun : (⇑(eIns2 i j') : ((kcE3 × kcE3) × X p) → X (p + 2))
      = fun q : (kcE3 × kcE3) × X p =>
          kcInsN (p + 1) i (q.1.1, kcInsN p j' (q.1.2, q.2)) := by
    funext q
    rw [eIns2_apply]
    rfl
  rw [hfun]
  exact h

/-- Transport of a two-slot box integral to the two-cube-times-rest product. -/
theorem abox_peel2_transport {p : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin (p + 2))
    (j' : Fin (p + 1)) (F : X (p + 2) → ℝ) :
    (∫ x in abox (p + 2) ℓ, F x)
      = ∫ q : (kcE3 × kcE3) × X p, F (ins2 i j' q.1.1 q.1.2 q.2)
          ∂((((volume : Measure kcE3).restrict (acube ℓ)).prod
              ((volume : Measure kcE3).restrict (acube ℓ))).prod
            ((volume : Measure (X p)).restrict (abox p ℓ))) := by
  rw [← (mp_eIns2 (p := p) hℓ i j').integral_comp' F]
  apply integral_congr_ae
  filter_upwards with q
  simp only [eIns2_apply]

/-- The first of the two distinguished slots at a doubly inserted configuration. -/
theorem boxPInd_ins2_self {p : ℕ} (volA : ℝ) (A : Set kcE3) (i : Fin (p + 2))
    (j' : Fin (p + 1)) (Ψ : X (p + 2) → ℝ) (y z : kcE3) (r2 : X p) :
    Work.UBBInputs8.boxPInd volA A i Ψ (ins2 i j' y z r2)
      = A.indicator (fun _ => (1 : ℝ)) y
        * ((1 / volA) * ∫ u in A, Ψ (ins2 i j' u z r2)) := by
  simp only [Work.UBBInputs8.boxPInd, ins2_update_i, ins2_apply_i]
  try ring

/-- The second of the two distinguished slots at a doubly inserted configuration. -/
theorem boxPInd_succAbove_ins2 {p : ℕ} (volA : ℝ) (A : Set kcE3) (i : Fin (p + 2))
    (j' : Fin (p + 1)) (Ψ : X (p + 2) → ℝ) (y z : kcE3) (r2 : X p) :
    Work.UBBInputs8.boxPInd volA A (i.succAbove j') Ψ (ins2 i j' y z r2)
      = A.indicator (fun _ => (1 : ℝ)) z
        * ((1 / volA) * ∫ w in A, Ψ (ins2 i j' y w r2)) := by
  simp only [Work.UBBInputs8.boxPInd, ins2_update_succ, ins2_apply_succ]
  try ring

/-- The two-slot value identity for an arbitrary kernel `h` on `A × A`. -/
theorem pair_kernel {p : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA) {A : Set kcE3}
    (hA : MeasurableSet A) (hAc : A ⊆ acube ℓ)
    (hvolA : volA = (volume : Measure kcE3).real A) (i : Fin (p + 2)) (j' : Fin (p + 1))
    {Ψ : X (p + 2) → ℝ} (hΨc : Continuous Ψ) {h : kcE3 → kcE3 → ℝ}
    (hh : Integrable (fun q : kcE3 × kcE3 => h q.1 q.2) (volume.restrict (A ×ˢ A))) :
    (∫ x in abox (p + 2) ℓ,
        (Work.UBBInputs8.boxPInd volA A i
          (Work.UBBInputs8.boxPInd volA A (i.succAbove j') Ψ) x) ^ 2
          * h (x i) (x (i.succAbove j')))
      = (∫ z in A, ∫ y in A, h y z) * (∫ r2 in abox p ℓ, (pairRest volA A i j' Ψ r2) ^ 2) := by
  rw [abox_peel2_transport (p := p) (ℓ := ℓ) hℓ i j'
    (fun x => (Work.UBBInputs8.boxPInd volA A i
      (Work.UBBInputs8.boxPInd volA A (i.succAbove j') Ψ) x) ^ 2 * h (x i) (x (i.succAbove j')))]
  have hpoint : ∀ q : (kcE3 × kcE3) × X p,
      (Work.UBBInputs8.boxPInd volA A i
        (Work.UBBInputs8.boxPInd volA A (i.succAbove j') Ψ)
          (ins2 i j' q.1.1 q.1.2 q.2)) ^ 2
        * h ((ins2 i j' q.1.1 q.1.2 q.2) i) ((ins2 i j' q.1.1 q.1.2 q.2) (i.succAbove j'))
        = (A.indicator (fun _ => (1 : ℝ)) q.1.1 * A.indicator (fun _ => (1 : ℝ)) q.1.2
            * h q.1.1 q.1.2) * (pairRest volA A i j' Ψ q.2) ^ 2 := by
    intro q
    rcases q with ⟨⟨y, z⟩, r2⟩
    dsimp only
    rw [ins2_apply_i, ins2_apply_succ, boxPInd_pair_ins2_sq]
    ring
  simp only [hpoint]
  haveI : IsFiniteMeasure ((volume : Measure kcE3).restrict (acube ℓ)) :=
    ⟨by rw [Measure.restrict_apply_univ, acube_volume ℓ hℓ.le]; exact ENNReal.ofReal_lt_top⟩
  haveI : IsFiniteMeasure ((volume : Measure (X p)).restrict (abox p ℓ)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact abox_lt_top p ℓ hℓ.le⟩
  have hF := integrable_indicator_pair (ℓ := ℓ) hA hAc hh
  have hG := integrableOn_pairRest_sq (volA := volA) hℓ hvol hAc hvolA i j' hΨc
  have hprod : Integrable (fun q : (kcE3 × kcE3) × X p =>
      (A.indicator (fun _ => (1 : ℝ)) q.1.1 * A.indicator (fun _ => (1 : ℝ)) q.1.2
          * h q.1.1 q.1.2) * (pairRest volA A i j' Ψ q.2) ^ 2)
      (((volume : Measure (kcE3 × kcE3)).restrict (acube ℓ ×ˢ acube ℓ)).prod
        ((volume : Measure (X p)).restrict (abox p ℓ))) := by
    have hF' : Integrable (fun q : kcE3 × kcE3 => A.indicator (fun _ => (1 : ℝ)) q.1
        * A.indicator (fun _ => (1 : ℝ)) q.2 * h q.1 q.2)
        ((volume : Measure (kcE3 × kcE3)).restrict (acube ℓ ×ˢ acube ℓ)) := by
      rw [Submission.BoseGases.prod_measure_eq ℓ]
      exact hF
    exact Integrable.smul_prod hF' hG
  rw [show ((((volume : Measure kcE3).restrict (acube ℓ)).prod
          ((volume : Measure kcE3).restrict (acube ℓ))).prod
        ((volume : Measure (X p)).restrict (abox p ℓ)))
      = (((volume : Measure (kcE3 × kcE3)).restrict (acube ℓ ×ˢ acube ℓ)).prod
        ((volume : Measure (X p)).restrict (abox p ℓ))) from
    congrArg (fun m : Measure (kcE3 × kcE3) =>
      m.prod ((volume : Measure (X p)).restrict (abox p ℓ)))
      (Submission.BoseGases.prod_measure_eq ℓ).symm]
  rw [MeasureTheory.integral_prod _ hprod]
  have hstep : (∫ q' in acube ℓ ×ˢ acube ℓ, ∫ r2 in abox p ℓ,
        (A.indicator (fun _ => (1 : ℝ)) q'.1 * A.indicator (fun _ => (1 : ℝ)) q'.2
            * h q'.1 q'.2) * (pairRest volA A i j' Ψ r2) ^ 2)
      = (∫ q' in acube ℓ ×ˢ acube ℓ, A.indicator (fun _ => (1 : ℝ)) q'.1
            * A.indicator (fun _ => (1 : ℝ)) q'.2 * h q'.1 q'.2)
          * (∫ r2 in abox p ℓ, (pairRest volA A i j' Ψ r2) ^ 2) := by
    rw [show (∫ q' in acube ℓ ×ˢ acube ℓ, ∫ r2 in abox p ℓ,
          (A.indicator (fun _ => (1 : ℝ)) q'.1 * A.indicator (fun _ => (1 : ℝ)) q'.2
              * h q'.1 q'.2) * (pairRest volA A i j' Ψ r2) ^ 2)
        = ∫ q' in acube ℓ ×ˢ acube ℓ, (A.indicator (fun _ => (1 : ℝ)) q'.1
              * A.indicator (fun _ => (1 : ℝ)) q'.2 * h q'.1 q'.2)
            * (∫ r2 in abox p ℓ, (pairRest volA A i j' Ψ r2) ^ 2) from by
      apply integral_congr_ae
      filter_upwards with q'
      rw [MeasureTheory.integral_const_mul]]
    rw [MeasureTheory.integral_mul_const]
  have hconst : (∫ q' in acube ℓ ×ˢ acube ℓ, A.indicator (fun _ => (1 : ℝ)) q'.1
        * A.indicator (fun _ => (1 : ℝ)) q'.2 * h q'.1 q'.2)
      = ∫ z in A, ∫ y in A, h y z := by
    have hEq : (fun q : kcE3 × kcE3 => A.indicator (fun _ => (1 : ℝ)) q.1
          * A.indicator (fun _ => (1 : ℝ)) q.2 * h q.1 q.2)
        = (A ×ˢ A).indicator (fun q : kcE3 × kcE3 => h q.1 q.2) := by
      funext q
      by_cases h1 : q.1 ∈ A <;> by_cases h2 : q.2 ∈ A <;>
        simp [Set.mem_prod, Set.indicator_of_mem, Set.indicator_of_notMem, h1, h2]
    rw [hEq, MeasureTheory.setIntegral_indicator (hA.prod hA),
      Set.inter_eq_right.mpr (Set.prod_mono hAc hAc), prod_measure_eq_A A]
    exact MeasureTheory.integral_prod_symm (fun q : kcE3 × kcE3 => h q.1 q.2) (by
      rw [← prod_measure_eq_A A]
      exact hh)
  rw [hstep, hconst]

/-- The flat (`h ≡ 1`) two-slot value identity. -/
theorem pair_flat {p : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA) {A : Set kcE3}
    (hA : MeasurableSet A) (hAc : A ⊆ acube ℓ)
    (hvolA : volA = (volume : Measure kcE3).real A) (i : Fin (p + 2)) (j' : Fin (p + 1))
    {Ψ : X (p + 2) → ℝ} (hΨc : Continuous Ψ) :
    (∫ x in abox (p + 2) ℓ,
        (Work.UBBInputs8.boxPInd volA A i
          (Work.UBBInputs8.boxPInd volA A (i.succAbove j') Ψ) x) ^ 2)
      = volA ^ 2 * (∫ r2 in abox p ℓ, (pairRest volA A i j' Ψ r2) ^ 2) := by
  have hAfin := volume_A_lt_top hℓ hAc
  have hA2fin : (volume : Measure (kcE3 × kcE3)) (A ×ˢ A) < ∞ := by
    rw [MeasureTheory.Measure.volume_eq_prod, Measure.prod_prod]
    exact ENNReal.mul_lt_top hAfin hAfin
  have hh : Integrable (fun _ : kcE3 × kcE3 => (1 : ℝ)) (volume.restrict (A ×ˢ A)) :=
    integrableOn_const hA2fin.ne
  have h := pair_kernel (volA := volA) hℓ hvol hA hAc hvolA i j' hΨc
    (h := fun _ _ => (1 : ℝ)) hh
  have hc1 : (∫ y in A, (1 : ℝ)) = volA := by
    rw [MeasureTheory.setIntegral_const, smul_eq_mul, mul_one]
    exact hvolA.symm
  have hc : (∫ z in A, ∫ y in A, (1 : ℝ)) = volA ^ 2 := by
    rw [show (∫ z in A, ∫ y in A, (1 : ℝ)) = (∫ z in A, volA) from by
      apply integral_congr_ae
      filter_upwards with z
      exact hc1]
    rw [MeasureTheory.setIntegral_const, smul_eq_mul, ← hvolA]
    ring
  rw [hc] at h
  simpa using h

/-! ## 7. The per-pair and per-slot value identities -/

/-- The two-slot value identity at distinct slots. -/
theorem pair_value {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA) {A : Set kcE3}
    (hA : MeasurableSet A) (hvolA : volA = (volume : Measure kcE3).real A)
    (hAc : A ⊆ acube ℓ) {i j : Fin N} (hij : i ≠ j)
    {w2 : kcE3 → kcE3 → ℝ}
    (hw2 : Integrable (fun p : kcE3 × kcE3 => w2 p.1 p.2) (volume.restrict (A ×ˢ A)))
    {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    (∫ x in abox N ℓ,
        (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x) ^ 2
          * w2 (x i) (x j))
      = (boxM2 volA A w2 / volA ^ 2)
        * (∫ x in abox N ℓ,
          (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x) ^ 2) := by
  cases N with
  | zero => exact absurd i.isLt (Nat.not_lt_zero _)
  | succ n =>
    cases n with
    | zero =>
      have hi : i = 0 := Fin.ext (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ i.isLt))
      have hj : j = 0 := Fin.ext (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ j.isLt))
      exact absurd (hi.trans hj.symm) hij
    | succ p =>
      rcases Fin.exists_succAbove_eq (x := j) (y := i) hij.symm with ⟨j', hj'⟩
      subst hj'
      have h1 := pair_kernel (volA := volA) hℓ hvol hA hAc hvolA i j' hΦc hw2
      have h2 := pair_flat (volA := volA) hℓ hvol hA hAc hvolA i j' hΦc
      have hM2 : (∫ z in A, ∫ y in A, w2 y z) = boxM2 volA A w2 := by
        rw [boxM2]
        rw [show (∫ q in A ×ˢ A, w2 q.1 q.2)
            = ∫ q : kcE3 × kcE3, w2 q.1 q.2
              ∂(((volume : Measure kcE3).restrict A).prod
                ((volume : Measure kcE3).restrict A)) from by
          rw [prod_measure_eq_A A]]
        exact (MeasureTheory.integral_prod_symm (fun q : kcE3 × kcE3 => w2 q.1 q.2) (by
          rw [← prod_measure_eq_A A]
          exact hw2)).symm
      rw [h1, hM2, h2]
      field_simp

/-- The one-slot value identity. -/
theorem one_value {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA) {A : Set kcE3}
    (hA : MeasurableSet A) (hvolA : volA = (volume : Measure kcE3).real A)
    (hAc : A ⊆ acube ℓ) (i : Fin N)
    {w1 : kcE3 → kcE3 → ℝ}
    (hw1 : IntegrableOn (w1Fibre ℓ w1) A) {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    (∫ x in abox N ℓ,
        (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2 * w1Fibre ℓ w1 (x i))
      = (boxM1 ℓ A w1 / volA)
        * (∫ x in abox N ℓ, (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2) := by
  cases N with
  | zero => exact absurd i.isLt (Nat.not_lt_zero _)
  | succ n =>
    have h1 := one_kernel (volA := volA) hℓ hvol hA hAc hvolA i hΦc hw1
    have h2 := one_flat (volA := volA) hℓ hvol hA hAc hvolA i hΦc
    rw [h1, h2, boxM1]
    field_simp

/-! ## 8. The mixed two-slot identity -/

theorem update_mem_abox {N : ℕ} {ℓ : ℝ} {A : Set kcE3} (hAc : A ⊆ acube ℓ) {x : X N}
    (hx : x ∈ abox N ℓ) (i : Fin N) {u : kcE3} (hu : u ∈ A) :
    Function.update x i u ∈ abox N ℓ := by
  intro k
  rw [Function.update_apply]
  by_cases hk : k = i
  · rw [if_pos hk]
    exact hAc hu
  · rw [if_neg hk]
    exact hx k

theorem ae_mem_prod_restrict {A : Set kcE3} (hA : MeasurableSet A) :
    ∀ᵐ q ∂(((volume : Measure kcE3).restrict A).prod
      ((volume : Measure kcE3).restrict A)), q.1 ∈ A ∧ q.2 ∈ A := by
  have h := self_mem_ae_restrict (μ := (volume : Measure (kcE3 × kcE3))) (hA.prod hA)
  rw [prod_measure_eq_A A] at h
  filter_upwards [h] with q hq
  exact Set.mem_prod.mp hq

theorem abs_boxPInd_le {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA) {A : Set kcE3}
    (hA : MeasurableSet A) (hAc : A ⊆ acube ℓ)
    (hvolA : volA = (volume : Measure kcE3).real A) (i : Fin N) {Ψ : X N → ℝ}
    (hΨc : Continuous Ψ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ abox N ℓ, |Work.UBBInputs8.boxPInd volA A i Ψ x| ≤ B := by
  obtain ⟨B, hB⟩ := (abox_compact N hℓ).exists_bound_of_continuousOn (s := abox N ℓ)
    (f := Ψ) hΨc.continuousOn
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB _ (zero_mem_abox hℓ.le))
  refine ⟨B, hB0, ?_⟩
  intro x hx
  have hfin := volume_A_lt_top hℓ hAc
  have hmain : |(1 / volA) * ∫ u in A, Ψ (Function.update x i u)| ≤ B := by
    have hb1 : ‖∫ u in A, Ψ (Function.update x i u)‖ ≤ B * volA := by
      have := norm_setIntegral_le_of_norm_le_const hfin
        (fun u hu => hB _ (update_mem_abox hAc hx i hu))
      rwa [← hvolA] at this
    have hb2 : |∫ u in A, Ψ (Function.update x i u)| ≤ B * volA := by
      simpa [Real.norm_eq_abs] using hb1
    have h2 : (1 / volA) * (B * volA) = B := by field_simp
    rw [abs_mul, abs_of_pos (one_div_pos.mpr hvol)]
    calc (1 / volA) * |∫ u in A, Ψ (Function.update x i u)|
        ≤ (1 / volA) * (B * volA) :=
          mul_le_mul_of_nonneg_left hb2 (by positivity)
      _ = B := h2
  rw [Work.UBBInputs8.boxPInd]
  by_cases hxi : x i ∈ A
  · rw [Set.indicator_of_mem hxi, mul_one]
    exact hmain
  · rw [Set.indicator_of_notMem hxi, mul_zero, abs_zero]
    exact hB0

theorem aem_boxPInd {N : ℕ} (volA : ℝ) (A : Set kcE3) (hA : MeasurableSet A) (i : Fin N)
    {Ψ : X N → ℝ} (hΨc : Continuous Ψ) (μ : Measure (X N)) :
    AEStronglyMeasurable (Work.UBBInputs8.boxPInd volA A i Ψ) μ := by
  have h1 : Measurable (fun x : X N => A.indicator (fun _ => (1 : ℝ)) (x i)) :=
    (measurable_const.indicator hA).comp (measurable_pi_apply i)
  have h2 : StronglyMeasurable (fun x : X N => ∫ u in A, Ψ (Function.update x i u)) := by
    have hsm : StronglyMeasurable
        (Function.uncurry (fun (x : X N) (u : kcE3) => Ψ (Function.update x i u))) := by
      have hmap : Measurable (fun p : X N × kcE3 => Function.update p.1 i p.2) := by fun_prop
      exact (hΨc.measurable.comp hmap).stronglyMeasurable
    exact StronglyMeasurable.integral_prod_right (ν := (volume : Measure kcE3).restrict A) hsm
  show AEStronglyMeasurable (fun x : X N =>
      (1 / volA) * (∫ u in A, Ψ (Function.update x i u))
        * A.indicator (fun _ => (1 : ℝ)) (x i)) μ
  exact ((h2.const_mul (1 / volA)).aestronglyMeasurable).mul h1.aestronglyMeasurable

/-- The `y`-slot integral of the mixed two-slot form. -/
theorem slotInt_Y {p : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA) {A : Set kcE3}
    (hA : MeasurableSet A) (hAc : A ⊆ acube ℓ)
    (hvolA : volA = (volume : Measure kcE3).real A) (i : Fin (p + 2)) (j' : Fin (p + 1))
    {Ψ : X (p + 2) → ℝ} (hΨc : Continuous Ψ) (r2 : X p) :
    (∫ y in acube ℓ, A.indicator (fun _ => (1 : ℝ)) y
        * ((1 / volA) * ∫ w in A, Ψ (ins2 i j' y w r2)))
      = volA * pairRest volA A i j' Ψ r2 := by
  rw [show (fun y : kcE3 => A.indicator (fun _ => (1 : ℝ)) y
        * ((1 / volA) * ∫ w in A, Ψ (ins2 i j' y w r2)))
      = A.indicator (fun y : kcE3 => ((1 / volA) * ∫ w in A, Ψ (ins2 i j' y w r2))) from by
    funext y
    by_cases hy : y ∈ A <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hy]]
  rw [MeasureTheory.setIntegral_indicator hA, Set.inter_eq_right.mpr hAc]
  rw [MeasureTheory.integral_const_mul]
  have hX : (∫ y in A, ∫ w in A, Ψ (ins2 i j' y w r2))
      = volA ^ 2 * pairRest volA A i j' Ψ r2 := by
    rw [pairRest_def]
    field_simp [ne_of_gt hvol]
  rw [hX]
  field_simp [ne_of_gt hvol]

/-- The `z`-slot integral of the mixed two-slot form. -/
theorem slotInt_Z {p : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA) {A : Set kcE3}
    (hA : MeasurableSet A) (hAc : A ⊆ acube ℓ)
    (hvolA : volA = (volume : Measure kcE3).real A) (i : Fin (p + 2)) (j' : Fin (p + 1))
    {Ψ : X (p + 2) → ℝ} (hΨc : Continuous Ψ) {r2 : X p} (hr2 : r2 ∈ abox p ℓ) :
    (∫ z in acube ℓ, A.indicator (fun _ => (1 : ℝ)) z
        * ((1 / volA) * ∫ u in A, Ψ (ins2 i j' u z r2)))
      = volA * pairRest volA A i j' Ψ r2 := by
  rw [show (fun z : kcE3 => A.indicator (fun _ => (1 : ℝ)) z
        * ((1 / volA) * ∫ u in A, Ψ (ins2 i j' u z r2)))
      = A.indicator (fun z : kcE3 => ((1 / volA) * ∫ u in A, Ψ (ins2 i j' u z r2))) from by
    funext z
    by_cases hz : z ∈ A <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hz]]
  rw [MeasureTheory.setIntegral_indicator hA, Set.inter_eq_right.mpr hAc]
  rw [MeasureTheory.integral_const_mul]
  have hswap : (∫ z in A, ∫ u in A, Ψ (ins2 i j' u z r2))
      = ∫ u in A, ∫ z in A, Ψ (ins2 i j' u z r2) := by
    obtain ⟨B, hB⟩ := (abox_compact (p + 2) hℓ).exists_bound_of_continuousOn
      (s := abox (p + 2) ℓ) (f := Ψ) hΨc.continuousOn
    have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB _ (zero_mem_abox hℓ.le))
    have hAfin : (volume : Measure kcE3) A < ∞ := volume_A_lt_top hℓ hAc
    haveI : IsFiniteMeasure ((volume : Measure kcE3).restrict A) := ⟨by
      rw [Measure.restrict_apply_univ]
      exact hAfin⟩
    have hint : Integrable (fun q : kcE3 × kcE3 => Ψ (ins2 i j' q.1 q.2 r2))
        (((volume : Measure kcE3).restrict A).prod ((volume : Measure kcE3).restrict A)) := by
      have hmap : Measurable (fun q : kcE3 × kcE3 => ins2 i j' q.1 q.2 r2) := by
        have h1 : Measurable (fun q : kcE3 × kcE3 => ((q.1, q.2), r2)) := by fun_prop
        exact (eIns2 i j').measurable.comp h1
      refine Integrable.mono' (integrable_const B) ((hΨc.measurable.comp hmap).aestronglyMeasurable) ?_
      filter_upwards [ae_mem_prod_restrict hA] with q hq
      exact hB _ (ins2_mem_abox hAc i j' hq.1 hq.2 hr2)
    have h1 := MeasureTheory.integral_prod (fun q : kcE3 × kcE3 => Ψ (ins2 i j' q.1 q.2 r2)) hint
    have h2 := MeasureTheory.integral_prod_symm (fun q : kcE3 × kcE3 => Ψ (ins2 i j' q.1 q.2 r2)) hint
    rw [← h1, h2]
  rw [hswap]
  have hX : (∫ u in A, ∫ z in A, Ψ (ins2 i j' u z r2))
      = volA ^ 2 * pairRest volA A i j' Ψ r2 := by
    rw [pairRest_def]
    field_simp [ne_of_gt hvol]
  rw [hX]
  field_simp [ne_of_gt hvol]

/-- The mixed two-slot identity: `∫(P_iΨ)(P_jΨ) = volA²∫(pairRest)²`. -/
theorem pair_mixed {p : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA) {A : Set kcE3}
    (hA : MeasurableSet A) (hAc : A ⊆ acube ℓ)
    (hvolA : volA = (volume : Measure kcE3).real A) (i : Fin (p + 2)) (j' : Fin (p + 1))
    {Ψ : X (p + 2) → ℝ} (hΨc : Continuous Ψ) :
    (∫ x in abox (p + 2) ℓ,
        Work.UBBInputs8.boxPInd volA A i Ψ x
          * Work.UBBInputs8.boxPInd volA A (i.succAbove j') Ψ x)
      = volA ^ 2 * (∫ r2 in abox p ℓ, (pairRest volA A i j' Ψ r2) ^ 2) := by
  have hF_int : IntegrableOn (fun x : X (p + 2) =>
      Work.UBBInputs8.boxPInd volA A i Ψ x
        * Work.UBBInputs8.boxPInd volA A (i.succAbove j') Ψ x) (abox (p + 2) ℓ) volume := by
    obtain ⟨B1, hB1_0, hB1⟩ := abs_boxPInd_le (volA := volA) hℓ hvol hA hAc hvolA i hΨc
    obtain ⟨B2, hB2_0, hB2⟩ := abs_boxPInd_le (volA := volA) hℓ hvol hA hAc hvolA
      (i.succAbove j') hΨc
    have hfin : (volume : Measure (X (p + 2))) (abox (p + 2) ℓ) < ∞ :=
      abox_lt_top (p + 2) ℓ hℓ.le
    haveI : IsFiniteMeasure ((volume : Measure (X (p + 2))).restrict (abox (p + 2) ℓ)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩
    refine Integrable.mono' (integrable_const (B1 * B2)) ?_ ?_
    · exact ((aem_boxPInd volA A hA i hΨc
        (volume.restrict (abox (p + 2) ℓ))).mul
        (aem_boxPInd volA A hA (i.succAbove j') hΨc (volume.restrict (abox (p + 2) ℓ))))
    · filter_upwards [self_mem_ae_restrict (abox_measurable (p + 2) ℓ)] with x hx
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hB1 x hx) (hB2 x hx) (abs_nonneg _) hB1_0
  rw [abox_integral_peel2 (i := i) (j' := j')
    (F := fun x => Work.UBBInputs8.boxPInd volA A i Ψ x
      * Work.UBBInputs8.boxPInd volA A (i.succAbove j') Ψ x) hF_int]
  have hstep : ∀ r2 ∈ abox p ℓ, (∫ z in acube ℓ, ∫ y in acube ℓ,
        Work.UBBInputs8.boxPInd volA A i Ψ (ins2 i j' y z r2)
          * Work.UBBInputs8.boxPInd volA A (i.succAbove j') Ψ (ins2 i j' y z r2))
      = (volA * pairRest volA A i j' Ψ r2) * (volA * pairRest volA A i j' Ψ r2) := by
    intro r2 hr2
    have hp : ∀ y z : kcE3,
        Work.UBBInputs8.boxPInd volA A i Ψ (ins2 i j' y z r2)
          * Work.UBBInputs8.boxPInd volA A (i.succAbove j') Ψ (ins2 i j' y z r2)
        = (A.indicator (fun _ => (1 : ℝ)) y
            * ((1 / volA) * ∫ u in A, Ψ (ins2 i j' u z r2)))
          * (A.indicator (fun _ => (1 : ℝ)) z
            * ((1 / volA) * ∫ w in A, Ψ (ins2 i j' y w r2))) := by
      intro y z
      rw [boxPInd_ins2_self, boxPInd_succAbove_ins2]
    simp only [hp]
    have hswap : (∫ z in acube ℓ, ∫ y in acube ℓ,
          (A.indicator (fun _ => (1 : ℝ)) y
              * ((1 / volA) * ∫ u in A, Ψ (ins2 i j' u z r2)))
            * (A.indicator (fun _ => (1 : ℝ)) z
              * ((1 / volA) * ∫ w in A, Ψ (ins2 i j' y w r2))))
        = ∫ z in acube ℓ, ∫ y in acube ℓ,
            (A.indicator (fun _ => (1 : ℝ)) y
                * ((1 / volA) * ∫ w in A, Ψ (ins2 i j' y w r2)))
              * (A.indicator (fun _ => (1 : ℝ)) z
                * ((1 / volA) * ∫ u in A, Ψ (ins2 i j' u z r2))) := by
      apply integral_congr_ae
      filter_upwards with z
      apply integral_congr_ae
      filter_upwards with y
      ring
    rw [hswap]
    have h1 : ∀ z : kcE3, (∫ y in acube ℓ,
          (A.indicator (fun _ => (1 : ℝ)) y
              * ((1 / volA) * ∫ w in A, Ψ (ins2 i j' y w r2)))
            * (A.indicator (fun _ => (1 : ℝ)) z
              * ((1 / volA) * ∫ u in A, Ψ (ins2 i j' u z r2))))
        = (∫ y in acube ℓ, A.indicator (fun _ => (1 : ℝ)) y
              * ((1 / volA) * ∫ w in A, Ψ (ins2 i j' y w r2)))
          * (A.indicator (fun _ => (1 : ℝ)) z
              * ((1 / volA) * ∫ u in A, Ψ (ins2 i j' u z r2))) := by
      intro z
      rw [MeasureTheory.integral_mul_const]
    rw [show (∫ z in acube ℓ, ∫ y in acube ℓ,
          (A.indicator (fun _ => (1 : ℝ)) y
              * ((1 / volA) * ∫ w in A, Ψ (ins2 i j' y w r2)))
            * (A.indicator (fun _ => (1 : ℝ)) z
              * ((1 / volA) * ∫ u in A, Ψ (ins2 i j' u z r2))))
        = ∫ z in acube ℓ, (∫ y in acube ℓ, A.indicator (fun _ => (1 : ℝ)) y
              * ((1 / volA) * ∫ w in A, Ψ (ins2 i j' y w r2)))
          * (A.indicator (fun _ => (1 : ℝ)) z
              * ((1 / volA) * ∫ u in A, Ψ (ins2 i j' u z r2))) from by
      apply integral_congr_ae
      filter_upwards with z
      exact h1 z]
    rw [MeasureTheory.integral_const_mul]
    rw [slotInt_Y (volA := volA) hℓ hvol hA hAc hvolA i j' hΨc r2]
    rw [slotInt_Z (volA := volA) hℓ hvol hA hAc hvolA i j' hΨc hr2]
  rw [show (∫ r2 in abox p ℓ, ∫ z in acube ℓ, ∫ y in acube ℓ,
        Work.UBBInputs8.boxPInd volA A i Ψ (kcInsN (p + 1) i (y, kcInsN p j' (z, r2)))
          * Work.UBBInputs8.boxPInd volA A (i.succAbove j') Ψ
              (kcInsN (p + 1) i (y, kcInsN p j' (z, r2))))
      = ∫ r2 in abox p ℓ, (volA * pairRest volA A i j' Ψ r2)
          * (volA * pairRest volA A i j' Ψ r2) from by
    apply integral_congr_ae
    filter_upwards [self_mem_ae_restrict (abox_measurable p ℓ)] with r2 hr2
    exact hstep r2 hr2]
  rw [show (∫ r2 in abox p ℓ, (volA * pairRest volA A i j' Ψ r2)
        * (volA * pairRest volA A i j' Ψ r2))
      = ∫ r2 in abox p ℓ, volA ^ 2 * (pairRest volA A i j' Ψ r2) ^ 2 from by
    apply integral_congr_ae
    filter_upwards with r2
    ring]
  rw [MeasureTheory.integral_const_mul]

theorem one_self_N {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA) {A : Set kcE3}
    (hA : MeasurableSet A) (hvolA : volA = (volume : Measure kcE3).real A)
    (hAc : A ⊆ acube ℓ) (i : Fin N) {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    (∫ x in abox N ℓ, Φ x * Work.UBBInputs8.boxPInd volA A i Φ x)
      = ∫ x in abox N ℓ, (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2 := by
  cases N with
  | zero => exact absurd i.isLt (Nat.not_lt_zero _)
  | succ n =>
    rw [one_self (volA := volA) hℓ hvol hA hAc hvolA i hΦc,
      one_flat (volA := volA) hℓ hvol hA hAc hvolA i hΦc]

theorem pair_mixed_N {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA) {A : Set kcE3}
    (hA : MeasurableSet A) (hvolA : volA = (volume : Measure kcE3).real A)
    (hAc : A ⊆ acube ℓ) {i j : Fin N} (hij : i ≠ j) {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    (∫ x in abox N ℓ, Work.UBBInputs8.boxPInd volA A i Φ x
        * Work.UBBInputs8.boxPInd volA A j Φ x)
      = ∫ x in abox N ℓ,
          (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x) ^ 2 := by
  cases N with
  | zero => exact absurd i.isLt (Nat.not_lt_zero _)
  | succ n =>
    cases n with
    | zero =>
      have h1 : i.1 = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ i.isLt)
      have h2 : j.1 = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ j.isLt)
      exact absurd (Fin.ext (h1.trans h2.symm)) hij
    | succ q =>
      rcases Fin.exists_succAbove_eq (x := j) (y := i) hij.symm with ⟨j', hj'⟩
      subst hj'
      rw [pair_mixed (volA := volA) hℓ hvol hA hAc hvolA i j' hΦc,
        pair_flat (volA := volA) hℓ hvol hA hAc hvolA i j' hΦc]

/-! ## 9. Cauchy--Schwarz for integrals and the flat-count inequality -/

/-- Cauchy--Schwarz for the Bochner integral of a.e.-bounded real functions:
`(∫ f·g)² ≤ (∫f²)(∫g²)`. -/
theorem integral_mul_sq_le {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {f g : α → ℝ} (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    {Cf Cg : ℝ} (hb : ∀ᵐ x ∂μ, |f x| ≤ Cf) (hb' : ∀ᵐ x ∂μ, |g x| ≤ Cg) :
    (∫ x, f x * g x ∂μ) ^ 2 ≤ (∫ x, (f x) ^ 2 ∂μ) * (∫ x, (g x) ^ 2 ∂μ) := by
  have hfm : MemLp (fun x => |f x|) (ENNReal.ofReal 2) μ :=
    MemLp.of_bound hf.norm Cf (by
      filter_upwards [hb] with x hx
      simpa using hx)
  have hgm : MemLp (fun x => |g x|) (ENNReal.ofReal 2) μ :=
    MemLp.of_bound hg.norm Cg (by
      filter_upwards [hb'] with x hx
      simpa using hx)
  have hmain := integral_mul_le_Lp_mul_Lq_of_nonneg (p := 2) (q := 2) (μ := μ)
    Real.HolderConjugate.two_two (ae_of_all _ (fun _ => abs_nonneg _))
    (ae_of_all _ (fun _ => abs_nonneg _)) hfm hgm
  have hsq1 : (fun x => |f x| ^ (2 : ℝ)) = fun x => (f x) ^ 2 := by
    funext x
    rw [Real.rpow_two, sq_abs]
  have hsq2 : (fun x => |g x| ^ (2 : ℝ)) = fun x => (g x) ^ 2 := by
    funext x
    rw [Real.rpow_two, sq_abs]
  rw [hsq1, hsq2] at hmain
  have hnonf : 0 ≤ ∫ x, (f x) ^ 2 ∂μ := integral_nonneg (fun x => sq_nonneg _)
  have hnong : 0 ≤ ∫ x, (g x) ^ 2 ∂μ := integral_nonneg (fun x => sq_nonneg _)
  have habs : |∫ x, f x * g x ∂μ| ≤ ∫ x, |f x| * |g x| ∂μ := by
    calc |∫ x, f x * g x ∂μ| ≤ ∫ x, |f x * g x| ∂μ := abs_integral_le_integral_abs
      _ = ∫ x, |f x| * |g x| ∂μ := by
          apply integral_congr_ae
          filter_upwards with x
          rw [abs_mul]
  have hsqrtf : ((∫ x, (f x) ^ 2 ∂μ) ^ (1 / 2 : ℝ)) ^ 2 = ∫ x, (f x) ^ 2 ∂μ := by
    rw [← Real.rpow_two, ← Real.rpow_mul hnonf,
      show (1 / 2 : ℝ) * 2 = 1 by norm_num, Real.rpow_one]
  have hsqrtg : ((∫ x, (g x) ^ 2 ∂μ) ^ (1 / 2 : ℝ)) ^ 2 = ∫ x, (g x) ^ 2 ∂μ := by
    rw [← Real.rpow_two, ← Real.rpow_mul hnong,
      show (1 / 2 : ℝ) * 2 = 1 by norm_num, Real.rpow_one]
  have hX2 : (∫ x, |f x| * |g x| ∂μ) ^ 2
      ≤ (∫ x, (f x) ^ 2 ∂μ) * (∫ x, (g x) ^ 2 ∂μ) := by
    have h0 : 0 ≤ ∫ x, |f x| * |g x| ∂μ :=
      integral_nonneg (fun x => mul_nonneg (abs_nonneg _) (abs_nonneg _))
    have h1 := pow_le_pow_left₀ h0 hmain 2
    rw [mul_pow, hsqrtf, hsqrtg] at h1
    exact h1
  have hle := abs_le.mp habs
  calc (∫ x, f x * g x ∂μ) ^ 2
      ≤ (∫ x, |f x| * |g x| ∂μ) ^ 2 := sq_le_sq' hle.1 hle.2
    _ ≤ (∫ x, (f x) ^ 2 ∂μ) * (∫ x, (g x) ^ 2 ∂μ) := hX2

/-- The diagonal-plus-off-diagonal splitting of a double sum over `Fin N`. -/
theorem sum_univ_univ_eq {N : ℕ} (G : Fin N → Fin N → ℝ) :
    (∑ i : Fin N, ∑ j : Fin N, G i j)
      = (∑ i : Fin N, G i i) + ∑ p ∈ Submission.BoseGases.pairSet N, G p.1 p.2 := by
  have h1 : (∑ i : Fin N, ∑ j : Fin N, G i j)
      = ∑ p ∈ (Finset.univ : Finset (Fin N × Fin N)), G p.1 p.2 := by
    conv_rhs => rw [← Finset.univ_product_univ]
    rw [Finset.sum_product]
  have h2 : (∑ p ∈ (Finset.univ : Finset (Fin N × Fin N)), G p.1 p.2)
      = (∑ p ∈ (Finset.univ.filter (fun p : Fin N × Fin N => p.1 = p.2)), G p.1 p.2)
        + ∑ p ∈ (Finset.univ.filter (fun p : Fin N × Fin N => p.1 ≠ p.2)), G p.1 p.2 :=
    (Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset (Fin N × Fin N)))
      (p := fun p : Fin N × Fin N => p.1 = p.2) (f := fun p => G p.1 p.2)).symm
  have h3 : (∑ p ∈ (Finset.univ.filter (fun p : Fin N × Fin N => p.1 = p.2)), G p.1 p.2)
      = ∑ i : Fin N, G i i := by
    refine Finset.sum_bij (fun (p : Fin N × Fin N) (_ : p ∈ Finset.univ.filter
      (fun p : Fin N × Fin N => p.1 = p.2)) => p.1) ?_ ?_ ?_ ?_
    · intro p hp
      exact Finset.mem_univ _
    · intro p hp q hq hpq
      have hp' : p.1 = p.2 := (Finset.mem_filter.mp hp).2
      have hq' : q.1 = q.2 := (Finset.mem_filter.mp hq).2
      simp only [Prod.ext_iff]
      exact ⟨hpq, by rw [← hp', ← hq', hpq]⟩
    · intro b hb
      exact ⟨(b, b), by simp, rfl⟩
    · intro p hp
      have hp' : p.1 = p.2 := (Finset.mem_filter.mp hp).2
      rw [hp']
  have h4 : (Finset.univ.filter (fun p : Fin N × Fin N => p.1 ≠ p.2))
      = Submission.BoseGases.pairSet N := rfl
  rw [h2, h3, h4] at h1
  exact h1

/-- The flat-count inequality: `boxFlatCount² − boxFlatCount ≤ boxPairCount` for a state of
unit `L²`-norm. -/
theorem count_ge {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA) {A : Set kcE3}
    (hA : MeasurableSet A) (hvolA : volA = (volume : Measure kcE3).real A)
    (hAc : A ⊆ acube ℓ) {Φ : X N → ℝ} (hΦc : Continuous Φ)
    (hnorm : (∫ x in abox N ℓ, (Φ x) ^ 2) = 1) :
    boxFlatCount volA ℓ A Φ ^ 2 - boxFlatCount volA ℓ A Φ ≤ boxPairCount volA ℓ A Φ := by
  have hfin : (volume : Measure (X N)) (abox N ℓ) < ∞ := abox_lt_top N ℓ hℓ.le
  haveI : IsFiniteMeasure ((volume : Measure (X N)).restrict (abox N ℓ)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩
  obtain ⟨C, hC⟩ := (abox_compact N hℓ).exists_bound_of_continuousOn (s := abox N ℓ)
    (f := Φ) hΦc.continuousOn
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC _ (zero_mem_abox hℓ.le))
  choose B hB0 hB using fun i : Fin N =>
    abs_boxPInd_le (volA := volA) hℓ hvol hA hAc hvolA i hΦc
  have hsum_bound : ∀ᵐ x ∂((volume : Measure (X N)).restrict (abox N ℓ)),
      ‖∑ i : Fin N, Work.UBBInputs8.boxPInd volA A i Φ x‖ ≤ ∑ i : Fin N, B i := by
    filter_upwards [self_mem_ae_restrict (abox_measurable N ℓ)] with x hx
    calc ‖∑ i : Fin N, Work.UBBInputs8.boxPInd volA A i Φ x‖
        ≤ ∑ i : Fin N, ‖Work.UBBInputs8.boxPInd volA A i Φ x‖ := norm_sum_le _ _
      _ ≤ ∑ i : Fin N, B i := Finset.sum_le_sum (fun i _ => by
          simpa [Real.norm_eq_abs] using hB i x hx)
  have hInt_prod : ∀ i j : Fin N, IntegrableOn (fun x : X N =>
      Work.UBBInputs8.boxPInd volA A i Φ x * Work.UBBInputs8.boxPInd volA A j Φ x)
      (abox N ℓ) volume := by
    intro i j
    refine Integrable.mono' (integrable_const (B i * B j)) ?_ ?_
    · exact ((aem_boxPInd volA A hA i hΦc _).mul (aem_boxPInd volA A hA j hΦc _))
    · filter_upwards [self_mem_ae_restrict (abox_measurable N ℓ)] with x hx
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hB i x hx) (hB j x hx) (abs_nonneg _) (hB0 i)
  have hInt_Φ : ∀ i : Fin N, IntegrableOn (fun x : X N =>
      Φ x * Work.UBBInputs8.boxPInd volA A i Φ x) (abox N ℓ) volume := by
    intro i
    refine Integrable.mono' (integrable_const (C * B i)) ?_ ?_
    · exact ((hΦc.measurable.aestronglyMeasurable).mul (aem_boxPInd volA A hA i hΦc _))
    · filter_upwards [self_mem_ae_restrict (abox_measurable N ℓ)] with x hx
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (by simpa [Real.norm_eq_abs] using hC x hx) (hB i x hx)
        (abs_nonneg _) hC0
  -- `boxFlatCount = ∫ Φ·(Σᵢ PᵢΦ)`
  have hS : boxFlatCount volA ℓ A Φ
      = ∫ x in abox N ℓ, Φ x * ∑ i : Fin N, Work.UBBInputs8.boxPInd volA A i Φ x := by
    rw [boxFlatCount]
    rw [show (∑ i : Fin N, ∫ x in abox N ℓ, (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2)
        = ∑ i : Fin N, ∫ x in abox N ℓ,
            Φ x * Work.UBBInputs8.boxPInd volA A i Φ x from
      Finset.sum_congr rfl (fun i _ => by
        rw [one_self_N (volA := volA) hℓ hvol hA hvolA hAc i hΦc])]
    rw [show (∫ x in abox N ℓ, Φ x * ∑ i : Fin N, Work.UBBInputs8.boxPInd volA A i Φ x)
        = ∑ i : Fin N, ∫ x in abox N ℓ, Φ x * Work.UBBInputs8.boxPInd volA A i Φ x from by
      rw [show (fun x : X N => Φ x * ∑ i : Fin N, Work.UBBInputs8.boxPInd volA A i Φ x)
          = fun x : X N => ∑ i : Fin N,
              Φ x * Work.UBBInputs8.boxPInd volA A i Φ x from by
        funext x
        rw [Finset.mul_sum]]
      rw [MeasureTheory.integral_finset_sum]
      intro i _
      exact hInt_Φ i]
  -- the expansion of `∫(Σᵢ PᵢΦ)²`
  have hN : (∫ x in abox N ℓ, (∑ i : Fin N, Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2)
      = boxFlatCount volA ℓ A Φ + boxPairCount volA ℓ A Φ := by
    have hexpand : (∫ x in abox N ℓ, (∑ i : Fin N, Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2)
        = ∑ i : Fin N, ∑ j : Fin N,
            ∫ x in abox N ℓ, Work.UBBInputs8.boxPInd volA A i Φ x
              * Work.UBBInputs8.boxPInd volA A j Φ x := by
      rw [show (∫ x in abox N ℓ, (∑ i : Fin N, Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2)
          = ∫ x in abox N ℓ, ∑ i : Fin N, ∑ j : Fin N,
              Work.UBBInputs8.boxPInd volA A i Φ x
                * Work.UBBInputs8.boxPInd volA A j Φ x from by
        apply integral_congr_ae
        filter_upwards with x
        rw [pow_two, Finset.sum_mul_sum]]
      rw [MeasureTheory.integral_finset_sum]
      · refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [MeasureTheory.integral_finset_sum]
        intro j _
        exact hInt_prod i j
      · intro i _
        refine Integrable.mono' (integrable_const (∑ j : Fin N, B i * B j)) ?_ ?_
        · have hfun : (fun x : X N => ∑ j : Fin N, Work.UBBInputs8.boxPInd volA A i Φ x
                * Work.UBBInputs8.boxPInd volA A j Φ x)
              = ∑ j : Fin N, fun x : X N => Work.UBBInputs8.boxPInd volA A i Φ x
                  * Work.UBBInputs8.boxPInd volA A j Φ x := by
            funext x
            rw [Finset.sum_apply]
          rw [hfun]
          exact Finset.aestronglyMeasurable_sum _ (fun j _ =>
            (aem_boxPInd volA A hA i hΦc _).mul (aem_boxPInd volA A hA j hΦc _))
        · filter_upwards [self_mem_ae_restrict (abox_measurable N ℓ)] with x hx
          calc ‖∑ j : Fin N, Work.UBBInputs8.boxPInd volA A i Φ x
                * Work.UBBInputs8.boxPInd volA A j Φ x‖
              ≤ ∑ j : Fin N, ‖Work.UBBInputs8.boxPInd volA A i Φ x
                  * Work.UBBInputs8.boxPInd volA A j Φ x‖ := norm_sum_le _ _
            _ ≤ ∑ j : Fin N, B i * B j := Finset.sum_le_sum (fun j _ => by
                rw [Real.norm_eq_abs, abs_mul]
                exact mul_le_mul (hB i x hx) (hB j x hx) (abs_nonneg _) (hB0 i))
    rw [hexpand, sum_univ_univ_eq (fun i j =>
      ∫ x in abox N ℓ, Work.UBBInputs8.boxPInd volA A i Φ x
        * Work.UBBInputs8.boxPInd volA A j Φ x)]
    congr 1
    · rw [boxFlatCount]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      apply integral_congr_ae
      filter_upwards with x
      ring
    · rw [boxPairCount]
      refine Finset.sum_congr rfl (fun p hp => ?_)
      have hp12 : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
      cases N with
      | zero => exact absurd p.1.isLt (Nat.not_lt_zero _)
      | succ n =>
        cases n with
        | zero =>
          have h1 : p.1.1 = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ p.1.isLt)
          have h2 : p.2.1 = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ p.2.isLt)
          exact absurd (Fin.ext (h1.trans h2.symm)) hp12
        | succ q =>
          rcases Fin.exists_succAbove_eq (x := p.2) (y := p.1) hp12.symm with ⟨j', hj'⟩
          rw [← hj']
          rw [pair_mixed (volA := volA) hℓ hvol hA hAc hvolA p.1 j' hΦc,
            pair_flat (volA := volA) hℓ hvol hA hAc hvolA p.1 j' hΦc]
  -- Cauchy--Schwarz
  have hCS := integral_mul_sq_le (μ := (volume : Measure (X N)).restrict (abox N ℓ))
    (f := Φ) (g := fun x : X N => ∑ i : Fin N, Work.UBBInputs8.boxPInd volA A i Φ x)
    (Cf := C) (Cg := ∑ i : Fin N, B i)
    hΦc.measurable.aestronglyMeasurable
    (by
      have hfun : (fun x : X N => ∑ i : Fin N, Work.UBBInputs8.boxPInd volA A i Φ x)
          = ∑ i : Fin N, Work.UBBInputs8.boxPInd volA A i Φ := by
        funext x
        rw [Finset.sum_apply]
      rw [hfun]
      exact Finset.aestronglyMeasurable_sum _
        (fun i _ => aem_boxPInd volA A hA i hΦc _))
    (by filter_upwards [self_mem_ae_restrict (abox_measurable N ℓ)] with x hx
        simpa [Real.norm_eq_abs] using hC x hx)
    hsum_bound
  rw [hnorm, one_mul, hN, ← hS] at hCS
  linarith [hCS]
