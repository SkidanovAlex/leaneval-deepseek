import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.boxPInd_boxQInd_pointwise
import Submission.Work.BoseFixB1S.peelPInd_pairMixed
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

set_option maxHeartbeats 2000000

/-! ## Local helpers -/

/-- Pulling a slot-`j` box indicator out of the slot-`i` projection (`i ≠ j`). -/
theorem boxPInd_indicator_mul {N : ℕ} {volA : ℝ} {A : Set (EuclideanSpace ℝ (Fin 3))}
    {i j : Fin N} (hij : i ≠ j) (h : X N → ℝ) :
    Work.UBBInputs8.boxPInd volA A i (fun x => A.indicator (fun _ => (1 : ℝ)) (x j) * h x)
      = fun x => A.indicator (fun _ => (1 : ℝ)) (x j)
          * Work.UBBInputs8.boxPInd volA A i h x := by
  funext x
  simp only [Work.UBBInputs8.boxPInd]
  rw [show (∫ z in A, A.indicator (fun _ => (1 : ℝ)) ((Function.update x i z) j)
        * h (Function.update x i z))
      = ∫ z in A, A.indicator (fun _ => (1 : ℝ)) (x j) * h (Function.update x i z) from by
    apply integral_congr_ae
    filter_upwards with z
    rw [Function.update_apply, if_neg (Ne.symm hij)]]
  rw [MeasureTheory.integral_const_mul]
  ring

/-- `P_i(P_jΦ)` is supported where slot `j` meets `A`. -/
theorem boxPInd_boxPInd_indicator {N : ℕ} {volA : ℝ} {A : Set (EuclideanSpace ℝ (Fin 3))}
    {i j : Fin N} (hij : i ≠ j) (h : X N → ℝ) :
    Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j h)
      = fun x => A.indicator (fun _ => (1 : ℝ)) (x j)
          * Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j h) x := by
  have hσ : (fun x : X N => A.indicator (fun _ => (1 : ℝ)) (x j)
        * Work.UBBInputs8.boxPInd volA A j h x) = Work.UBBInputs8.boxPInd volA A j h := by
    funext x
    simp only [Work.UBBInputs8.boxPInd]
    by_cases hx : x j ∈ A
    · rw [Set.indicator_of_mem hx]; ring
    · rw [Set.indicator_of_notMem hx]; ring
  have h := boxPInd_indicator_mul (volA := volA) (A := A) (i := i) (j := j) hij
    (Work.UBBInputs8.boxPInd volA A j h)
  rw [hσ] at h
  exact h

/-! ## The per-pair bound -/

theorem pair_bound {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {i j : Fin N} (hij : i ≠ j) {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) :
    (∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x) ^ 2)
      ≤ (∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2)
        - ∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x) ^ 2 := by
  let u : X N → ℝ := fun x => Work.UBBInputs8.boxPInd volA A i Φ x
  let v : X N → ℝ := fun x => Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x
  let σ : X N → ℝ := fun x => A.indicator (fun _ => (1 : ℝ)) (x j)
  let f : X N → ℝ := fun x => Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x
  let F1 : X N → ℝ := fun x => σ x * (u x) ^ 2
  let F2 : X N → ℝ := fun x => 2 * (σ x * u x * v x)
  let F3 : X N → ℝ := fun x => σ x * (v x) ^ 2
  let G : X N → ℝ := fun x => (u x) ^ 2
  let H : X N → ℝ := fun x => (v x) ^ 2
  obtain ⟨C, hC⟩ := (abox_compact N hℓ).exists_bound_of_continuousOn
    (s := abox N ℓ) (f := Φ) hΦc.continuousOn
  have hΦb : ∀ x ∈ abox N ℓ, |Φ x| ≤ C := fun x hx => by
    simpa [Real.norm_eq_abs] using hC x hx
  have hum : Measurable u := measurable_boxPInd volA A hA i hΦc.measurable
  have hub : ∀ x ∈ abox N ℓ, |u x| ≤ C := abs_boxPInd_le hℓ hvol hA hvolA hAc i hΦb
  have hvm : Measurable v :=
    measurable_boxPInd volA A hA i (measurable_boxPInd volA A hA j hΦc.measurable)
  have hvb : ∀ x ∈ abox N ℓ, |v x| ≤ C :=
    abs_boxPInd_le hℓ hvol hA hvolA hAc i (abs_boxPInd_le hℓ hvol hA hvolA hAc j hΦb)
  have hσm : Measurable σ := (measurable_const.indicator hA).comp (measurable_pi_apply j)
  have hσ_one : ∀ x : X N, x j ∈ A → σ x = 1 := fun x hx => by
    simp only [σ]
    rw [Set.indicator_of_mem hx]
  have hσ_zero : ∀ x : X N, x j ∉ A → σ x = 0 := fun x hx => by
    simp only [σ]
    rw [Set.indicator_of_notMem hx]
  have hσabs : ∀ x : X N, |σ x| ≤ 1 := fun x => by
    by_cases hx : x j ∈ A
    · rw [hσ_one x hx]; norm_num
    · rw [hσ_zero x hx]; norm_num
  have hσu_m : Measurable (fun x : X N => σ x * u x) := hσm.mul hum
  have hσu_b : ∀ x ∈ abox N ℓ, |σ x * u x| ≤ 1 * C := fun x hx => by
    rw [abs_mul]
    exact mul_le_mul (hσabs x) (hub x hx) (abs_nonneg _) zero_le_one
  have hσv_m : Measurable (fun x : X N => σ x * v x) := hσm.mul hvm
  have hσv_b : ∀ x ∈ abox N ℓ, |σ x * v x| ≤ 1 * C := fun x hx => by
    rw [abs_mul]
    exact mul_le_mul (hσabs x) (hvb x hx) (abs_nonneg _) zero_le_one
  have hG : IntegrableOn G (abox N ℓ) volume := integrableOn_sq_of_bound hℓ hum hub
  have hH : IntegrableOn H (abox N ℓ) volume := integrableOn_sq_of_bound hℓ hvm hvb
  have hF1 : IntegrableOn F1 (abox N ℓ) volume := by
    refine (integrableOn_mul_of_bound hℓ hσu_m hum hσu_b hub).congr ?_
    filter_upwards with x
    ring
  have hF2 : IntegrableOn F2 (abox N ℓ) volume :=
    (integrableOn_mul_of_bound hℓ hσu_m hvm hσu_b hvb).const_mul 2
  have hF3 : IntegrableOn F3 (abox N ℓ) volume := by
    refine (integrableOn_mul_of_bound hℓ hσv_m hvm hσv_b hvb).congr ?_
    filter_upwards with x
    ring
  have hσv : ∀ x : X N, σ x * v x = v x := fun x =>
    (congrFun (boxPInd_boxPInd_indicator (volA := volA) (A := A) (i := i) (j := j) hij Φ)
      x).symm
  have e1 : (∫ x in abox N ℓ, (f x) ^ 2)
      = ∫ x in abox N ℓ, (σ x * (u x - v x)) ^ 2 := by
    apply setIntegral_congr_fun (abox_measurable N ℓ)
    intro x hx
    beta_reduce
    show Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x ^ 2
      = (A.indicator (fun _ => (1 : ℝ)) (x j) *
          (Work.UBBInputs8.boxPInd volA A i Φ x
            - Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x)) ^ 2
    rw [boxPInd_boxQInd_pointwise hℓ hvol hA hvolA hAc hij hΦc x hx]
  have e2 : (∫ x in abox N ℓ, (σ x * (u x - v x)) ^ 2)
      = ∫ x in abox N ℓ, ((F1 - F2) x + F3 x) := by
    apply setIntegral_congr_fun (abox_measurable N ℓ)
    intro x hx
    beta_reduce
    show (σ x * (u x - v x)) ^ 2 = (σ x * (u x) ^ 2 - 2 * (σ x * u x * v x) + σ x * (v x) ^ 2)
    by_cases hxj : x j ∈ A
    · rw [hσ_one x hxj]; ring
    · rw [hσ_zero x hxj]; ring
  have e3 : (∫ x in abox N ℓ, ((F1 - F2) x + F3 x))
      = (∫ x in abox N ℓ, (F1 - F2) x) + ∫ x in abox N ℓ, F3 x :=
    integral_add (hF1.sub hF2) hF3
  have e4 : (∫ x in abox N ℓ, (F1 - F2) x)
      = (∫ x in abox N ℓ, F1 x) - ∫ x in abox N ℓ, F2 x :=
    integral_sub hF1 hF2
  have e5 : (∫ x in abox N ℓ, F2 x) = 2 * (∫ x in abox N ℓ, σ x * u x * v x) :=
    MeasureTheory.integral_const_mul 2 (fun x : X N => σ x * u x * v x)
  have e6a : (∫ x in abox N ℓ, σ x * u x * v x) = ∫ x in abox N ℓ, u x * v x := by
    apply setIntegral_congr_fun (abox_measurable N ℓ)
    intro x hx
    beta_reduce
    rw [show σ x * u x * v x = u x * (σ x * v x) by ring, hσv x]
  have e6b : (∫ x in abox N ℓ, u x * v x) = ∫ x in abox N ℓ, (v x) ^ 2 :=
    peelPInd_pairMixed hℓ hvol hA hvolA hAc hij hΦc
  have e7 : (∫ x in abox N ℓ, F3 x) = ∫ x in abox N ℓ, H x := by
    apply setIntegral_congr_fun (abox_measurable N ℓ)
    intro x hx
    show σ x * (v x) ^ 2 = (v x) ^ 2
    rw [show σ x * (v x) ^ 2 = (σ x * v x) * v x by ring, hσv x]
    ring
  have e8 : (∫ x in abox N ℓ, F1 x) ≤ ∫ x in abox N ℓ, G x := by
    refine integral_mono hF1 hG ?_
    intro x
    beta_reduce
    show σ x * (u x) ^ 2 ≤ (u x) ^ 2
    by_cases hxj : x j ∈ A
    · rw [hσ_one x hxj, one_mul]
    · rw [hσ_zero x hxj]
      simp only [zero_mul]
      exact sq_nonneg _
  calc (∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x) ^ 2)
      = ∫ x in abox N ℓ, (f x) ^ 2 := rfl
    _ = ∫ x in abox N ℓ, (σ x * (u x - v x)) ^ 2 := e1
    _ = ∫ x in abox N ℓ, ((F1 - F2) x + F3 x) := e2
    _ = (∫ x in abox N ℓ, (F1 - F2) x) + ∫ x in abox N ℓ, F3 x := e3
    _ = ((∫ x in abox N ℓ, F1 x) - ∫ x in abox N ℓ, F2 x) + ∫ x in abox N ℓ, F3 x := by rw [e4]
    _ = ((∫ x in abox N ℓ, F1 x) - 2 * (∫ x in abox N ℓ, σ x * u x * v x))
          + ∫ x in abox N ℓ, F3 x := by rw [e5]
    _ = ((∫ x in abox N ℓ, F1 x) - 2 * (∫ x in abox N ℓ, u x * v x))
          + ∫ x in abox N ℓ, F3 x := by rw [e6a]
    _ = ((∫ x in abox N ℓ, F1 x) - 2 * (∫ x in abox N ℓ, H x))
          + ∫ x in abox N ℓ, F3 x := by rw [e6b]
    _ = ((∫ x in abox N ℓ, F1 x) - 2 * (∫ x in abox N ℓ, H x))
          + ∫ x in abox N ℓ, H x := by rw [e7]
    _ = (∫ x in abox N ℓ, F1 x) - ∫ x in abox N ℓ, H x := by ring
    _ ≤ (∫ x in abox N ℓ, G x) - ∫ x in abox N ℓ, H x := sub_le_sub_right e8 _
    _ = (∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2)
        - ∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x) ^ 2 := rfl

/-! ## The counting identity on `pairSet` -/

/-- Summing the first slot over the ordered distinct pairs multiplies by `N - 1`. -/
theorem pairSet_sum_fst {N : ℕ} (g : Fin N → ℝ) :
    (∑ p ∈ Submission.BoseGases.pairSet N, g p.1) = ((N : ℝ) - 1) * ∑ i : Fin N, g i := by
  have h1 : (∑ p ∈ Submission.BoseGases.pairSet N, g p.1)
      = ∑ p : Fin N × Fin N, (if p.1 ≠ p.2 then g p.1 else 0) := by
    rw [show Submission.BoseGases.pairSet N
        = (Finset.univ : Finset (Fin N × Fin N)).filter (fun p => p.1 ≠ p.2) from rfl]
    rw [Finset.sum_filter]
  have h2 : (∑ p : Fin N × Fin N, (if p.1 ≠ p.2 then g p.1 else 0))
      = ∑ i : Fin N, ∑ j : Fin N, (if i ≠ j then g i else 0) := by
    conv_lhs => rw [← Finset.univ_product_univ]
    rw [Finset.sum_product]
  have h3 : ∀ i : Fin N, (∑ j : Fin N, (if i ≠ j then g i else 0)) = ((N : ℝ) - 1) * g i := by
    intro i
    have hfilter : (∑ j : Fin N, (if i ≠ j then g i else 0))
        = ∑ j ∈ (Finset.univ : Finset (Fin N)).filter (fun j => i ≠ j), g i := by
      rw [Finset.sum_filter]
    rw [hfilter, Finset.sum_const, nsmul_eq_mul]
    have hcard : ((Finset.univ : Finset (Fin N)).filter (fun j => i ≠ j)).card = N - 1 := by
      have hset : (Finset.univ : Finset (Fin N)).filter (fun j => i ≠ j) = Finset.univ.erase i := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase,
          and_true]
        exact ne_comm
      rw [hset, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
        Fintype.card_fin]
    rw [hcard]
    have hN : (1 : ℕ) ≤ N := i.pos
    rw [Nat.cast_sub hN, Nat.cast_one]
  rw [h1, h2]
  simp only [h3]
  rw [Finset.mul_sum]

/-! ## The main theorem -/

theorem boxPairQCount_eq {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) :
    (∑ p ∈ Submission.BoseGases.pairSet N,
        ∫ x in Submission.BoseGases.abox N ℓ,
          (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x) ^ 2)
      ≤ ((N : ℝ) - 1) * Work.BoseFixB1S.boxFlatCount volA ℓ A Φ
        - Work.BoseFixB1S.boxPairCount volA ℓ A Φ := by
  have hstep : (∑ p ∈ Submission.BoseGases.pairSet N,
        ∫ x in Submission.BoseGases.abox N ℓ,
          (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x) ^ 2)
      ≤ ∑ p ∈ Submission.BoseGases.pairSet N,
          ((∫ x in Submission.BoseGases.abox N ℓ,
              (Work.UBBInputs8.boxPInd volA A p.1 Φ x) ^ 2)
            - ∫ x in Submission.BoseGases.abox N ℓ,
                (Work.UBBInputs8.boxPInd volA A p.1
                  (Work.UBBInputs8.boxPInd volA A p.2 Φ) x) ^ 2) := by
    refine Finset.sum_le_sum (fun p hp => ?_)
    have hpne : p.1 ≠ p.2 := by
      have hp' : p ∈ (Finset.univ : Finset (Fin N × Fin N)).filter (fun q => q.1 ≠ q.2) := hp
      exact (Finset.mem_filter.mp hp').2
    exact pair_bound hℓ hvol hA hvolA hAc hpne hΦc
  refine le_trans hstep ?_
  rw [Finset.sum_sub_distrib,
    pairSet_sum_fst (fun i : Fin N => ∫ x in Submission.BoseGases.abox N ℓ,
      (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2)]
  simp only [boxFlatCount, boxPairCount]
  exact le_refl _

end Work.BoseFixB1S
