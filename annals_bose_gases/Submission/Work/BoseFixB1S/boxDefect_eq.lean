import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.PQIdentAux
import Submission.Work.BoseFixB1S.boxC1_add_cnPlus
import Submission.Work.BoseFixB1S.sum_pairSet_fst_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1S.boxDefect_eq` — the exact two-slot defect identity

With `σ_i(x) = 1_A(x_i)`, `P_i = boxPInd volA A i`, `Q_i = boxQInd volA A i = σ_i − P_i`,
`S = boxFlatCount = Σ_i∫(P_iΦ)²`, `n₊ = boxQCount = Σ_i∫(Q_iΦ)²` and
`Pc = boxPairCount = Σ_{p∈pairSet N}∫(P_{p.1}P_{p.2}Φ)²` (all integrals over `abox N ℓ`), the
statement is the **exact** (not just upper-bounded) two-slot defect identity

  `Σ_{p∈pairSet N} ∫ (σ_{p.1}(σ_{p.2}Φ) − P_{p.1}P_{p.2}Φ)²  =  (N−1)(S + n₊) − Pc`.

## Route

All four quantities are integrals over the *big* box `abox N ℓ`, but the state `Φ` is a.e.
supported on `A^N` (`hsupp`), where every `σ_i` equals `1`.  Hence, a.e. on the box,

* `σ_i(σ_jΦ) = Φ`, so the defect integrand is `(Φ − B)²` with `B := P_iP_jΦ`;
* `∫(σ_i(σ_jΦ))² = ∫Φ²` and `∫σ_i(σ_jΦ)·B = ∫Φ·B`;
* `P_iP_j` is an orthogonal projection (`P_i`, `P_j` commute, both self-adjoint and
  idempotent), so `∫Φ·B = ∫B²` — the chain
  `∫B² = ∫(P_iΦ)·B` (`peelPInd_pairMixed`) `= ∫Φ·P_iB = ∫Φ·B` (`boxPIndSelfAdjoint`,
  `boxPInd_idempotent`).

Expanding the square therefore gives the **per-pair** identity

  `∫(σ_i(σ_jΦ) − P_iP_jΦ)² = ∫Φ² − ∫(P_iP_jΦ)²`   (`pairDefect_eq_aux`),

and summing over the `N(N−1)` ordered pairs (`sum_pairSet_fst_eq`) gives
`N(N−1)∫Φ² − Pc`.  The count split `S + n₊ = N∫Φ²` (`countSplit`) — the `i`-summed Parseval
identity `boxPInd_sq_add_boxQInd_sq` together with `σ_iΦ² = Φ²` a.e. — converts this into
`(N−1)(S + n₊) − Pc`, which is the claim.
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators ENNReal

namespace Work.BoseFixB1S

open Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1000000

/-- The support hypothesis in slot form: a.e. on the box, `1_A(x i)·Φ x = Φ x` for every slot. -/
theorem ae_indicator_mul_eq {N : ℕ} {ℓ : ℝ} {A : Set E3} {Φ : Submission.BoseGases.X N → ℝ}
    (hsupp : ∀ᵐ x ∂(MeasureTheory.volume.restrict (abox N ℓ)),
      Φ x ≠ 0 → ∀ i : Fin N, x i ∈ A) :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (abox N ℓ)),
      ∀ i : Fin N, A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x = Φ x := by
  filter_upwards [hsupp] with x hx i
  by_cases h : Φ x = 0
  · simp [h]
  · rw [Set.indicator_of_mem (hx h i), one_mul]

/-- Two slots at once: a.e. on the box, `1_A(x i)·(1_A(x j)·Φ x) = Φ x`. -/
theorem ae_indicator_mul_mul_eq {N : ℕ} {ℓ : ℝ} {A : Set E3}
    {Φ : Submission.BoseGases.X N → ℝ}
    (hsupp : ∀ᵐ x ∂(MeasureTheory.volume.restrict (abox N ℓ)),
      Φ x ≠ 0 → ∀ i : Fin N, x i ∈ A) :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (abox N ℓ)), ∀ i j : Fin N,
      A.indicator (fun _ => (1 : ℝ)) (x i)
        * (A.indicator (fun _ => (1 : ℝ)) (x j) * Φ x) = Φ x := by
  filter_upwards [ae_indicator_mul_eq hsupp] with x hx i j
  rw [hx j, hx i]

/-- **The count split**: `S + n₊ = N·∫Φ²` for a state a.e. supported on `A^N`.  This is the
slot-summed Parseval identity `boxPInd_sq_add_boxQInd_sq` together with `σ_i(x_i)·Φ² = Φ²` a.e.
(`hsupp`). -/
theorem countSplit_aux {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
    (hsupp : ∀ᵐ x ∂(MeasureTheory.volume.restrict (abox N ℓ)),
      Φ x ≠ 0 → ∀ i : Fin N, x i ∈ A) :
    Work.BoseFixB1S.boxFlatCount volA ℓ A Φ + Work.BoseFixB1S.boxQCount volA ℓ A Φ
      = (N : ℝ) * (∫ x in abox N ℓ, (Φ x) ^ 2) := by
  classical
  have hper : ∀ i : Fin N,
      (∫ x in abox N ℓ, (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2)
        + (∫ x in abox N ℓ, (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2)
      = ∫ x in abox N ℓ, (Φ x) ^ 2 := by
    intro i
    rw [boxPInd_sq_add_boxQInd_sq (N := N) (ℓ := ℓ) (volA := volA) hℓ hA hvolA hAc i hΦc]
    apply integral_congr_ae
    filter_upwards [hsupp] with x hx
    by_cases h : Φ x = 0
    · simp [h]
    · rw [Set.indicator_of_mem (hx h i), one_mul]
  simp only [Work.BoseFixB1S.boxFlatCount, Work.BoseFixB1S.boxQCount]
  rw [← Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl (fun i _ => hper i)]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **The per-pair defect identity**: for distinct slots `i ≠ j` and a state a.e. supported on
`A^N`, the exact square of the two-slot defect `σ_i(σ_jΦ) − P_iP_jΦ` is `∫Φ² − ∫(P_iP_jΦ)²`. -/
theorem pairDefect_eq_aux {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
    (hsupp : ∀ᵐ x ∂(MeasureTheory.volume.restrict (abox N ℓ)),
      Φ x ≠ 0 → ∀ i : Fin N, x i ∈ A)
    {i j : Fin N} (hij : i ≠ j) :
    (∫ x in abox N ℓ,
        (A.indicator (fun _ => (1 : ℝ)) (x i)
            * (A.indicator (fun _ => (1 : ℝ)) (x j) * Φ x)
          - Work.UBBInputs8.boxPInd volA A i
              (Work.UBBInputs8.boxPInd volA A j Φ) x) ^ 2)
      = (∫ x in abox N ℓ, (Φ x) ^ 2)
        - ∫ x in abox N ℓ,
            (Work.UBBInputs8.boxPInd volA A i
              (Work.UBBInputs8.boxPInd volA A j Φ) x) ^ 2 := by
  classical
  obtain ⟨C, hC0, hΦb, hPb, hQb⟩ :=
    boxBounds (N := N) (ℓ := ℓ) (volA := volA) hℓ hvol hA hvolA hAc hΦc
  let B : X N → ℝ := fun x =>
    Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x
  let F : X N → ℝ := fun x => A.indicator (fun _ => (1 : ℝ)) (x i)
      * (A.indicator (fun _ => (1 : ℝ)) (x j) * Φ x)
  have hPjm : Measurable (Work.UBBInputs8.boxPInd volA A j Φ) :=
    measurable_boxPInd volA A hA j hΦc.measurable
  have hPjb : ∀ x ∈ abox N ℓ, |Work.UBBInputs8.boxPInd volA A j Φ x| ≤ C := fun x hx => hPb j x hx
  have hBm : Measurable B := measurable_boxPInd volA A hA i hPjm
  have hBb : ∀ x ∈ abox N ℓ, |B x| ≤ C :=
    fun x hx => abs_boxPInd_le hℓ hvol hA hvolA hAc i hPjb x hx
  have hFm : Measurable F :=
    (measurable_sigAt A hA i).mul ((measurable_sigAt A hA j).mul hΦc.measurable)
  have hFb : ∀ x ∈ abox N ℓ, |F x| ≤ C := by
    intro x hx
    show |A.indicator (fun _ => (1 : ℝ)) (x i)
      * (A.indicator (fun _ => (1 : ℝ)) (x j) * Φ x)| ≤ C
    rw [abs_mul]
    calc |A.indicator (fun _ => (1 : ℝ)) (x i)| * |A.indicator (fun _ => (1 : ℝ)) (x j) * Φ x|
        ≤ 1 * (1 * C) := by
          refine mul_le_mul (Aind_abs_le_one A (x i)) ?_ (abs_nonneg _) (by norm_num)
          rw [abs_mul]
          exact mul_le_mul (Aind_abs_le_one A (x j)) (hΦb x hx) (abs_nonneg _) (by norm_num)
      _ = C := by ring
  have hσ : ∀ᵐ x ∂(MeasureTheory.volume.restrict (abox N ℓ)), F x = Φ x := by
    filter_upwards [hsupp] with x hx
    show A.indicator (fun _ => (1 : ℝ)) (x i)
      * (A.indicator (fun _ => (1 : ℝ)) (x j) * Φ x) = Φ x
    by_cases h : Φ x = 0
    · simp [h]
    · rw [Set.indicator_of_mem (hx h i), Set.indicator_of_mem (hx h j)]
      ring
  have hA2 : (∫ x in abox N ℓ, (F x) ^ 2) = ∫ x in abox N ℓ, (Φ x) ^ 2 := by
    apply integral_congr_ae
    filter_upwards [hσ] with x hx
    rw [hx]
  have hAB : (∫ x in abox N ℓ, F x * B x) = ∫ x in abox N ℓ, Φ x * B x := by
    apply integral_congr_ae
    filter_upwards [hσ] with x hx
    rw [hx]
  have hidem : ∀ x : X N, Work.UBBInputs8.boxPInd volA A i B x = B x :=
    fun x => boxPInd_idempotent hℓ hvol hA hvolA hAc i
      (Work.UBBInputs8.boxPInd volA A j Φ) x
  have hself : (∫ x in abox N ℓ, Work.UBBInputs8.boxPInd volA A i Φ x * B x)
      = ∫ x in abox N ℓ, Φ x * Work.UBBInputs8.boxPInd volA A i B x :=
    boxPIndSelfAdjoint hℓ hvol hA hvolA hAc i hΦc.measurable hΦb hBm hBb
  have hpeel : (∫ x in abox N ℓ, Work.UBBInputs8.boxPInd volA A i Φ x * B x)
      = ∫ x in abox N ℓ, (B x) ^ 2 :=
    peelPInd_pairMixed hℓ hvol hA hvolA hAc hij hΦc
  have hφB : (∫ x in abox N ℓ, Φ x * B x) = ∫ x in abox N ℓ, (B x) ^ 2 := by
    rw [← hpeel, hself]
    apply integral_congr_ae
    filter_upwards with x
    rw [hidem x]
  have hI1 : IntegrableOn (fun x : X N => (F x) ^ 2) (abox N ℓ) MeasureTheory.volume :=
    integrableOn_sq_of_bound hℓ hFm hFb
  have hI2 : IntegrableOn (fun x : X N => F x * B x) (abox N ℓ) MeasureTheory.volume :=
    integrableOn_mul_of_bound hℓ hFm hBm hFb hBb
  have hI2' : IntegrableOn (fun x : X N => 2 * (F x * B x)) (abox N ℓ) MeasureTheory.volume :=
    hI2.const_mul 2
  have hI3 : IntegrableOn (fun x : X N => (B x) ^ 2) (abox N ℓ) MeasureTheory.volume :=
    integrableOn_sq_of_bound hℓ hBm hBb
  have hI12 : IntegrableOn (fun x : X N => (F x) ^ 2 - 2 * (F x * B x)) (abox N ℓ)
      MeasureTheory.volume := hI1.sub hI2'
  have hexp : (∫ x in abox N ℓ, (F x - B x) ^ 2)
      = (∫ x in abox N ℓ, (F x) ^ 2) - 2 * (∫ x in abox N ℓ, F x * B x)
        + ∫ x in abox N ℓ, (B x) ^ 2 := by
    rw [show (∫ x in abox N ℓ, (F x - B x) ^ 2)
        = ∫ x in abox N ℓ, ((F x) ^ 2 - 2 * (F x * B x) + (B x) ^ 2) from by
      apply integral_congr_ae
      filter_upwards with x
      ring]
    rw [MeasureTheory.integral_add hI12 hI3,
      MeasureTheory.integral_sub hI1 hI2', MeasureTheory.integral_const_mul]
  change (∫ x in abox N ℓ, (F x - B x) ^ 2)
      = (∫ x in abox N ℓ, Φ x ^ 2) - ∫ x in abox N ℓ, B x ^ 2
  rw [hexp, hA2, hAB, hφB]
  ring

theorem boxDefect_eq {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
    (hsupp : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)),
      Φ x ≠ 0 → ∀ i : Fin N, x i ∈ A) :
    (∑ p ∈ Submission.BoseGases.pairSet N,
        ∫ x in Submission.BoseGases.abox N ℓ,
          ((A.indicator (fun _ => (1 : ℝ)) (x p.1)
              * (A.indicator (fun _ => (1 : ℝ)) (x p.2) * Φ x))
            - Work.UBBInputs8.boxPInd volA A p.1
                (Work.UBBInputs8.boxPInd volA A p.2 Φ) x) ^ 2)
      = ((N : ℝ) - 1)
          * (Work.BoseFixB1S.boxFlatCount volA ℓ A Φ + Work.BoseFixB1S.boxQCount volA ℓ A Φ)
        - Work.BoseFixB1S.boxPairCount volA ℓ A Φ := by
  classical
  trans ∑ p ∈ Submission.BoseGases.pairSet N,
      ((∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2)
        - ∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxPInd volA A p.1
              (Work.UBBInputs8.boxPInd volA A p.2 Φ) x) ^ 2)
  · apply Finset.sum_congr rfl
    intro p hp
    exact pairDefect_eq_aux (N := N) (ℓ := ℓ) (volA := volA) (A := A) (Φ := Φ)
      hℓ hvol hA hvolA hAc hΦc hsupp (Finset.mem_filter.mp hp).2
  rw [Finset.sum_sub_distrib]
  have hcard : (∑ p ∈ Submission.BoseGases.pairSet N,
        ∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2)
      = ((N : ℝ) - 1) * ((N : ℝ) * (∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2)) := by
    have h := sum_pairSet_fst_eq (N := N)
      (g := fun _ : Fin N => (∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2))
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using h
  rw [hcard]
  have hcs := countSplit_aux (N := N) (ℓ := ℓ) (volA := volA) (A := A) hℓ hvol hA hvolA hAc hΦc hsupp
  rw [← hcs]
  simp only [Work.BoseFixB1S.boxPairCount]

end Work.BoseFixB1S
