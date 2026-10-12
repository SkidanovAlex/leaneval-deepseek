import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB1S.BoxQWords
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory
open scoped Real BigOperators ENNReal

namespace Work.BoseFixB1S

open Submission.BoseGases

set_option maxHeartbeats 800000

/-! ## 1. The pointwise structure of `boxPInd` -/

/-- `Pᵢ` at a configuration with the `i`-th slot set to `t`: the box indicator in slot `i`
times the (slot-independent) mean over `A`. -/
theorem boxPInd_kcInsN {n : ℕ} (volA : ℝ) (A : Set ℝ³) (i : Fin (n + 1))
    (Ψ : X (n + 1) → ℝ) (t : ℝ³) (r : X n) :
    UBBInputs8.boxPInd volA A i Ψ (kcInsN n i (t, r))
      = A.indicator (fun _ => (1 : ℝ)) t
        * ((1 / volA) * ∫ z in A, Ψ (kcInsN n i (z, r))) := by
  simp only [UBBInputs8.boxPInd, kc_insN_apply_same, update_kcInsN]
  ring

/-- The square of `Pᵢ` at an inserted configuration. -/
theorem boxPInd_sq_ins2 {p : ℕ} (volA : ℝ) (A : Set ℝ³) (i : Fin (p + 2))
    (j' : Fin (p + 1)) (Ψ : X (p + 2) → ℝ) (y z : ℝ³) (r2 : X p) :
    (UBBInputs8.boxPInd volA A i Ψ (ins2 i j' y z r2)) ^ 2
      = A.indicator (fun _ => (1 : ℝ)) y
        * ((1 / volA) * ∫ u in A, Ψ (ins2 i j' u z r2)) ^ 2 := by
  simp only [UBBInputs8.boxPInd, ins2_apply_i, ins2_update_i]
  by_cases hy : y ∈ A <;>
    simp [Set.indicator_of_mem, Set.indicator_of_notMem, hy]

/-- `P_{i.succAbove j'}` at a doubly inserted configuration. -/
theorem boxPInd_succAbove_ins2 {p : ℕ} (volA : ℝ) (A : Set ℝ³) (i : Fin (p + 2))
    (j' : Fin (p + 1)) (Ψ : X (p + 2) → ℝ) (y z : ℝ³) (r2 : X p) :
    UBBInputs8.boxPInd volA A (i.succAbove j') Ψ (ins2 i j' y z r2)
      = A.indicator (fun _ => (1 : ℝ)) z
        * ((1 / volA) * ∫ w in A, Ψ (ins2 i j' y w r2)) := by
  simp only [UBBInputs8.boxPInd, ins2_apply_succ, ins2_update_succ]
  ring

/-- The two-fold projection at a doubly inserted configuration: the product of the two box
indicators times the slot-independent double mean. -/
theorem boxPInd_pair_ins2 {p : ℕ} (volA : ℝ) (A : Set ℝ³) (i : Fin (p + 2))
    (j' : Fin (p + 1)) (Ψ : X (p + 2) → ℝ) (y z : ℝ³) (r2 : X p) :
    UBBInputs8.boxPInd volA A i
        (UBBInputs8.boxPInd volA A (i.succAbove j') Ψ) (ins2 i j' y z r2)
      = A.indicator (fun _ => (1 : ℝ)) y * A.indicator (fun _ => (1 : ℝ)) z
        * ((1 / volA) * ((1 / volA) * ∫ u in A, ∫ w in A, Ψ (ins2 i j' u w r2))) := by
  simp only [UBBInputs8.boxPInd, ins2_apply_i, ins2_update_i, ins2_update_succ,
    ins2_apply_succ]
  rw [MeasureTheory.integral_mul_const, MeasureTheory.integral_const_mul]
  ring

/-- The square of the two-fold projection at a doubly inserted configuration. -/
theorem boxPInd_pair_ins2_sq {p : ℕ} (volA : ℝ) (A : Set ℝ³) (i : Fin (p + 2))
    (j' : Fin (p + 1)) (Ψ : X (p + 2) → ℝ) (y z : ℝ³) (r2 : X p) :
    (UBBInputs8.boxPInd volA A i
        (UBBInputs8.boxPInd volA A (i.succAbove j') Ψ) (ins2 i j' y z r2)) ^ 2
      = A.indicator (fun _ => (1 : ℝ)) y * A.indicator (fun _ => (1 : ℝ)) z
        * ((1 / volA) * ((1 / volA) * ∫ u in A, ∫ w in A, Ψ (ins2 i j' u w r2))) ^ 2 := by
  rw [boxPInd_pair_ins2]
  by_cases hy : y ∈ A <;> by_cases hz : z ∈ A <;>
    simp [Set.indicator_of_mem, Set.indicator_of_notMem, hy, hz]

/-! ## 2. Membership of the inserted configurations -/

theorem kcInsN_mem_abox {n : ℕ} {ℓ : ℝ} {A : Set ℝ³} (hAc : A ⊆ acube ℓ) (i : Fin (n + 1))
    {u : ℝ³} (hu : u ∈ A) {r : X n} (hr : r ∈ abox n ℓ) :
    kcInsN n i (u, r) ∈ abox (n + 1) ℓ := by
  intro k
  by_cases hk : k = i
  · subst hk
    simpa [kc_insN_apply_same] using hAc hu
  · rcases Fin.exists_succAbove_eq hk with ⟨j, hj⟩
    rw [← hj, kc_insN_apply_succ]
    exact hr j

theorem ins2_mem_abox {p : ℕ} {ℓ : ℝ} {A : Set ℝ³} (hAc : A ⊆ acube ℓ) (i : Fin (p + 2))
    (j' : Fin (p + 1)) {y z : ℝ³} (hy : y ∈ A) (hz : z ∈ A) {r2 : X p}
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

/-! ## 3. Finiteness, measurability and boundedness -/

theorem volume_A_lt_top {ℓ : ℝ} (hℓ : 0 < ℓ) {A : Set ℝ³} (hAc : A ⊆ acube ℓ) :
    (volume : Measure ℝ³) A < ∞ :=
  lt_of_le_of_lt (measure_mono hAc)
    (by rw [acube_volume ℓ hℓ.le]; exact ENNReal.ofReal_lt_top)

/-- The fibre mean `x ↦ ∫_{z∈A} Ψ(x|i↦z) dz` is measurable for measurable `Ψ`. -/
theorem measurable_fibreMean {N : ℕ} (A : Set ℝ³) (hA : MeasurableSet A) (i : Fin N)
    {Ψ : X N → ℝ} (hΨ : Measurable Ψ) :
    Measurable (fun x : X N => ∫ z in A, Ψ (Function.update x i z)) := by
  have huncurry : Measurable (Function.uncurry (fun (x : X N) (z : ℝ³) =>
      A.indicator (fun _ => (1 : ℝ)) z * Ψ (Function.update x i z))) := by
    apply Measurable.mul
    · exact (measurable_const.indicator hA).comp measurable_snd
    · exact hΨ.comp (by fun_prop)
  have hsm := StronglyMeasurable.integral_prod_right (ν := (volume : Measure ℝ³))
    (f := fun (x : X N) (z : ℝ³) =>
      A.indicator (fun _ => (1 : ℝ)) z * Ψ (Function.update x i z))
    huncurry.stronglyMeasurable
  have hEq : (fun x : X N => ∫ z, A.indicator (fun _ => (1 : ℝ)) z * Ψ (Function.update x i z))
      = fun x : X N => ∫ z in A, Ψ (Function.update x i z) := by
    funext x
    rw [← MeasureTheory.integral_indicator (μ := (volume : Measure ℝ³)) hA
      (f := fun z : ℝ³ => Ψ (Function.update x i z))]
    apply integral_congr_ae
    filter_upwards with z
    by_cases hz : z ∈ A <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, hz]
  rw [hEq] at hsm
  exact hsm.measurable

/-- `PᵢΨ` is globally measurable when `Ψ` is. -/
theorem measurable_boxPInd {N : ℕ} (volA : ℝ) (A : Set ℝ³) (hA : MeasurableSet A)
    (i : Fin N) {Ψ : X N → ℝ} (hΨ : Measurable Ψ) :
    Measurable (UBBInputs8.boxPInd volA A i Ψ) := by
  have h1 : Measurable (fun x : X N => ∫ z in A, Ψ (Function.update x i z)) :=
    measurable_fibreMean A hA i hΨ
  exact ((h1.const_mul (1 / volA)).mul
    (((measurable_const.indicator hA).comp (measurable_pi_apply i))))

/-- `PᵢΨ` is bounded on the box by any bound of `Ψ`. -/
theorem abs_boxPInd_le {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set ℝ³} (hA : MeasurableSet A) (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ acube ℓ) (i : Fin N) {Ψ : X N → ℝ} {C : ℝ}
    (hC : ∀ x ∈ abox N ℓ, |Ψ x| ≤ C) :
    ∀ x ∈ abox N ℓ, |UBBInputs8.boxPInd volA A i Ψ x| ≤ C := by
  intro x hx
  have hfin : (volume : Measure ℝ³) A < ∞ := volume_A_lt_top hℓ hAc
  have hone : (volume : Measure ℝ³).real A = volA := hvolA.symm
  have hInt : ‖∫ z in A, Ψ (Function.update x i z)‖ ≤ C * volA := by
    have h := norm_setIntegral_le_of_norm_le_const hfin (s := A)
      (f := fun z : ℝ³ => Ψ (Function.update x i z)) (C := C) (fun z hz => by
        rw [Real.norm_eq_abs]
        exact hC _ (update_mem_abox i hx (hAc hz)))
    rwa [hone] at h
  have hstep : |(1 / volA) * (∫ z in A, Ψ (Function.update x i z))| ≤ C := by
    rw [abs_mul, abs_of_pos (one_div_pos.mpr hvol)]
    calc (1 / volA) * ‖∫ z in A, Ψ (Function.update x i z)‖
        ≤ (1 / volA) * (C * volA) :=
          mul_le_mul_of_nonneg_left hInt (by positivity)
      _ = C := by field_simp
  have hind : |A.indicator (fun _ => (1 : ℝ)) (x i)| ≤ 1 := by
    by_cases hxi : x i ∈ A <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, hxi]
  have hfac : UBBInputs8.boxPInd volA A i Ψ x
      = ((1 / volA) * (∫ z in A, Ψ (Function.update x i z)))
        * A.indicator (fun _ => (1 : ℝ)) (x i) := rfl
  rw [hfac, abs_mul]
  exact le_trans (mul_le_mul hstep hind (abs_nonneg _) (le_trans (abs_nonneg _) hstep))
    (le_of_eq (mul_one C))

/-! ## 4. Integrability of bounded measurable products on the box -/

theorem integrableOn_mul_of_bound {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {f g : X N → ℝ}
    (hfm : Measurable f) (hgm : Measurable g) {Cf Cg : ℝ}
    (hfb : ∀ x ∈ abox N ℓ, |f x| ≤ Cf) (hgb : ∀ x ∈ abox N ℓ, |g x| ≤ Cg) :
    IntegrableOn (fun x : X N => f x * g x) (abox N ℓ) volume := by
  refine IntegrableOn.of_bound (abox_lt_top N ℓ hℓ.le)
    (hfm.aestronglyMeasurable.mul hgm.aestronglyMeasurable) (|Cf| * |Cg|) ?_
  rw [ae_restrict_iff' (abox_measurable N ℓ)]
  refine ae_of_all _ (fun x hx => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (le_trans (hfb x hx) (le_abs_self Cf)) (le_trans (hgb x hx) (le_abs_self Cg))
    (abs_nonneg _) (abs_nonneg _)

theorem integrableOn_sq_of_bound {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {f : X N → ℝ}
    (hfm : Measurable f) {Cf : ℝ} (hfb : ∀ x ∈ abox N ℓ, |f x| ≤ Cf) :
    IntegrableOn (fun x : X N => (f x) ^ 2) (abox N ℓ) volume := by
  have h := integrableOn_mul_of_bound (N := N) hℓ hfm hfm hfb hfb (Cf := Cf) (Cg := Cf)
  refine h.congr ?_
  filter_upwards with x
  ring

/-! ## 5. The indicator collapse -/

/-- `∫_{acube ℓ} 1_A h = ∫_A h` for `A ⊆ acube ℓ`. -/
theorem setIntegral_indicator_one_mul {ℓ : ℝ} {A : Set ℝ³} (hA : MeasurableSet A)
    (hAc : A ⊆ acube ℓ) (h : ℝ³ → ℝ) :
    (∫ t in acube ℓ, A.indicator (fun _ => (1 : ℝ)) t * h t) = ∫ t in A, h t := by
  have hEq : (fun t : ℝ³ => A.indicator (fun _ => (1 : ℝ)) t * h t) = A.indicator h := by
    funext t
    by_cases ht : t ∈ A <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, ht]
  have hgoal : (∫ t : ℝ³, A.indicator h t ∂(volume.restrict (acube ℓ))) = ∫ t in A, h t := by
    rw [MeasureTheory.integral_indicator (μ := (volume.restrict (acube ℓ))) hA]
    rw [Measure.restrict_restrict_of_subset (μ := (volume : Measure ℝ³)) hAc]
  rw [hEq]
  exact hgoal

end Work.BoseFixB1S
