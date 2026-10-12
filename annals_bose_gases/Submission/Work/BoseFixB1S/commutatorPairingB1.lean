import Mathlib.Tactic.Have
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.boxProj_sq_contraction
import Submission.Work.BoseFixB1S.n0FunOp_eq_excl_shift
import Submission.Work.BoseFixB1S.n0FunOp_selfAdjointB1
import Submission.Work.BoseFixB1S.sqIntegralProjSumLe
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1S.commutatorPairingB1`

The commutator pairing `⟨[g(n₀), M_fib(xᵢ)]Q_{B,i}Φ, h(n₀)P_{B,i}Φ⟩` of the sharp FS completion of
squares, bounded by `4·Cfib·‖Q_{B,i}Φ‖₂·‖h(n₀)P_{B,i}Φ‖₂` (summed over the slots `i`).

## The mathematics

With `M = M_fib(xᵢ)` the multiplication operator by the fibre weight and `P_i = P_{B,i}` the box
projection (`Work.UBBInputs8.boxPInd`), the algebra is the *interpolation* identity of the spectral
calculus `g(n₀) = g(Aᵢ+1)P_i + g(Aᵢ)(1−P_i)`, `Aᵢ = n₀ − P_i`:

* `n0FunOp_eq_excl_shift` (delegated): `g(n₀)Ψ = exclFunOp (g(·+1)) (P_iΨ) + exclFunOp g (Ψ − P_iΨ)`;
* `exclFunOpPropsB1`(1) (corpus): the fibre weight passes through `exclFunOp`
  (`exclFunOp g (fib(xᵢ)·Ψ) = fib(xᵢ)·exclFunOp g Ψ`), while the corpus's `n0OpSlotComm` shows it
  does *not* pass through `n₀` — that mismatch is the whole commutator;
* `P_i(Q_{B,i}Φ) = 0` (`boxPInd_boxQInd_self_zero`) kills the `g(Aᵢ+1)P_i` half at `Ψ = Q_{B,i}Φ`.

Hence, with `Δg(r) = g(r+1) − g(r)` and `w = P_i(M Q_{B,i}Φ)`,
`[g(n₀),M](Q_{B,i}Φ) = exclFunOp (Δg) w` a.e. on the box.  Since `w` lies in the range of `P_i`,
the `S ∌ i` terms of `exclFunOp (Δg)` vanish, so the operator is the weighted sum
`Σ_{S ∋ i} Δg(|S|−1)·n0ProjOp S w` of *orthogonal* projections with coefficients in `[0,1]`
(the telescoping `√(r+2) − √(r+1) ∈ (0,1)`), and Bessel gives `‖[g(n₀),M]Q_{B,i}Φ‖₂ ≤ ‖w‖₂ ≤
Cfib·‖Q_{B,i}Φ‖₂`.  Cauchy–Schwarz in `L²`, then in `i`, and `√A·√B = √(AB)` finish it.
-/

namespace Work.BoseFixB1S

open MeasureTheory
open scoped BigOperators ENNReal

open Submission.BoseGases
open Work.UBBInputs8

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1600000

/-! ## 1. The box projection `P_i` against the subset idempotents

`n0IterEigen` computes `P_j(n0ProjOp S Ψ)` for `Ψ` in `GoodState`; combining it with the
commutation `n0Iter_comm_boxPInd` of the box projection with the whole slot iteration gives the
mirror statements `n0ProjOp S (P_iΨ) = 1_{i∈S}·n0ProjOp S Ψ` and
`n0ProjOp S (Ψ − P_iΨ) = 1_{i∉S}·n0ProjOp S Ψ`. -/

theorem n0ProjOp_boxPInd_apply {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) (S : Finset (Fin N)) (i : Fin N)
    {Ψ : X N → ℝ} (hΨ : GoodState ℓ Ψ) :
    ∀ x ∈ abox N ℓ,
      n0ProjOp volA A S (UBBInputs8.boxPInd volA A i Ψ) x
        = (if i ∈ S then n0ProjOp volA A S Ψ x else 0) := by
  intro x hx
  have h1 : n0ProjOp volA A S (UBBInputs8.boxPInd volA A i Ψ) x
      = UBBInputs8.boxPInd volA A i (n0ProjOp volA A S Ψ) x :=
    n0Iter_comm_boxPInd hℓ hvol hA hvolA hAc (fun j : Fin N => decide (j ∈ S)) i
      (List.ofFn (fun j : Fin N => j)) hΨ x hx
  rw [h1]
  exact n0IterEigen hℓ hvol hA hvolA hAc S hΨ i x hx

theorem n0ProjOp_sub_boxPInd_apply {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) (S : Finset (Fin N)) (i : Fin N)
    {Ψ : X N → ℝ} (hΨ : GoodState ℓ Ψ) :
    ∀ x ∈ abox N ℓ,
      n0ProjOp volA A S (fun y => Ψ y - UBBInputs8.boxPInd volA A i Ψ y) x
        = (if i ∈ S then 0 else n0ProjOp volA A S Ψ x) := by
  intro x hx
  have hPi : GoodState ℓ (UBBInputs8.boxPInd volA A i Ψ) :=
    goodState_boxPInd hℓ hvol hA hvolA hAc i hΨ
  have hsub : n0ProjOp volA A S (fun y => Ψ y - UBBInputs8.boxPInd volA A i Ψ y) x
      = n0ProjOp volA A S Ψ x - n0ProjOp volA A S (UBBInputs8.boxPInd volA A i Ψ) x :=
    Work.n0ProjOpOrthAux.n0Iter_sub hℓ hvol hA hvolA hAc (fun j : Fin N => decide (j ∈ S))
      (List.ofFn (fun j : Fin N => j)) hΨ hPi x hx
  rw [hsub, n0ProjOp_boxPInd_apply hℓ hvol hA hvolA hAc S i hΨ x hx]
  by_cases hi : i ∈ S <;> simp [hi]

/-! ## 2. The excluded functional calculus: linearity and the `g(·+1) − g` difference -/

theorem exclFunOp_congr_box {N : ℕ} {ℓ volA : ℝ} {A : Set E3} (hA : MeasurableSet A)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) (i : Fin N) (g : ℝ → ℝ) {f f' : X N → ℝ}
    (h : ∀ y ∈ abox N ℓ, f y = f' y) :
    ∀ x ∈ abox N ℓ, exclFunOp volA A i g f x = exclFunOp volA A i g f' x := by
  intro x hx
  simp only [exclFunOp]
  apply Finset.sum_congr rfl
  intro S _
  congr 1
  exact n0Iter_eq_of_eqOn_box hA hAc (fun j : Fin N => decide (j ∈ S)) h
    (List.ofFn (fun j : Fin N => j)) x hx

theorem exclFunOp_sub {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) (i : Fin N) (g : ℝ → ℝ)
    {Φ Ψ : X N → ℝ} (hΦ : GoodState ℓ Φ) (hΨ : GoodState ℓ Ψ) :
    ∀ x ∈ abox N ℓ,
      exclFunOp volA A i g (fun y => Φ y - Ψ y) x
        = exclFunOp volA A i g Φ x - exclFunOp volA A i g Ψ x := by
  intro x hx
  have hterm : ∀ S : Finset (Fin N),
      n0ProjOp volA A S (fun y => Φ y - Ψ y) x
        = n0ProjOp volA A S Φ x - n0ProjOp volA A S Ψ x := fun S =>
    Work.n0ProjOpOrthAux.n0Iter_sub hℓ hvol hA hvolA hAc (fun j : Fin N => decide (j ∈ S))
      (List.ofFn (fun j : Fin N => j)) hΦ hΨ x hx
  simp only [exclFunOp]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro S _
  rw [hterm S]
  ring

theorem exclFunOp_shift_sub {N : ℕ} (volA : ℝ) (A : Set E3) (i : Fin N) (g : ℝ → ℝ)
    (Ψ : X N → ℝ) (x : X N) :
    exclFunOp volA A i (fun r => g (r + 1)) Ψ x - exclFunOp volA A i g Ψ x
      = exclFunOp volA A i (fun r => g (r + 1) - g r) Ψ x := by
  simp only [exclFunOp]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro S _
  ring

/-! ## 3. `GoodState` is closed under multiplication by the fibre weight -/

theorem goodState_fib_mul {N : ℕ} {ℓ : ℝ} {fib : E3 → ℝ} (hfm : Measurable fib) (i : Fin N)
    {Cfib : ℝ} (hCfib : 0 ≤ Cfib) (hfibb : ∀ z ∈ Submission.BoseGases.acube ℓ, |fib z| ≤ Cfib)
    {Ψ : X N → ℝ} (hΨ : GoodState ℓ Ψ) :
    GoodState ℓ (fun y => fib (y i) * Ψ y) := by
  obtain ⟨hm, C, hC⟩ := hΨ
  refine ⟨(hfm.comp (measurable_pi_apply i)).mul hm, Cfib * max C 0, fun x hx => ?_⟩
  calc |fib (x i) * Ψ x| = |fib (x i)| * |Ψ x| := abs_mul _ _
    _ ≤ Cfib * max C 0 :=
        mul_le_mul (hfibb (x i) (hx i)) (le_trans (hC x hx) (le_max_left _ _))
          (abs_nonneg _) hCfib

theorem zero_mem_acube {ℓ : ℝ} (hℓ : 0 < ℓ) : (0 : E3) ∈ acube ℓ := by
  rw [mem_acube_iff]
  intro m
  have h0 : (0 : E3).ofLp m = 0 := by simp
  rw [h0, Set.mem_Icc]
  constructor <;> linarith

theorem Cfib_nonneg {ℓ Cfib : ℝ} {fib : E3 → ℝ} (hℓ : 0 < ℓ)
    (hfibb : ∀ z ∈ acube ℓ, |fib z| ≤ Cfib) : 0 ≤ Cfib := by
  have h := hfibb 0 (zero_mem_acube hℓ)
  linarith [abs_nonneg (fib 0)]

theorem sqrt_add_one_sub_sqrt_abs_le_one (x : ℝ) (hx : 0 ≤ x) :
    |Real.sqrt (x + 1) - Real.sqrt x| ≤ 1 := by
  have hnn : 0 ≤ Real.sqrt (x + 1) - Real.sqrt x :=
    sub_nonneg.mpr (Real.sqrt_le_sqrt (by linarith))
  rw [abs_of_nonneg hnn]
  have hle : Real.sqrt (x + 1) ≤ Real.sqrt x + 1 := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    have hsq : (Real.sqrt x + 1) ^ 2 = x + 2 * Real.sqrt x + 1 := by
      rw [add_sq, Real.sq_sqrt hx]
      ring
    nlinarith [Real.sqrt_nonneg x]
  linarith

/-! ## 4. `GoodState` for the functional calculi with bounded coefficients -/

theorem goodState_n0FunOp {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (volume A).toReal)
    (hAc : A ⊆ acube ℓ) (g : ℝ → ℝ) {C : ℝ}
    (hg : ∀ S : Finset (Fin N), |g (S.card : ℝ)| ≤ C) {Ψ : X N → ℝ}
    (hΨ : GoodState ℓ Ψ) : GoodState ℓ (n0FunOp volA A g Ψ) := by
  rw [n0FunOp_eq_sum_card volA A g Ψ]
  refine goodState_finset_sum (Finset.univ) (fun S _ => ?_)
  exact goodState_const_mul (goodState_n0Iter hℓ hvol hA hvolA hAc
    (fun j : Fin N => decide (j ∈ S)) (List.ofFn (fun j : Fin N => j)) hΨ) _

theorem goodState_exclFunOp {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (volume A).toReal)
    (hAc : A ⊆ acube ℓ) (i : Fin N) (g : ℝ → ℝ) {C : ℝ}
    (hg : ∀ S : Finset (Fin N), |g ((S.card : ℝ) - (if i ∈ S then 1 else 0))| ≤ C)
    {Ψ : X N → ℝ} (hΨ : GoodState ℓ Ψ) : GoodState ℓ (exclFunOp volA A i g Ψ) := by
  refine goodState_finset_sum (Finset.univ) (fun S _ => ?_)
  exact goodState_const_mul (goodState_n0Iter hℓ hvol hA hvolA hAc
    (fun j : Fin N => decide (j ∈ S)) (List.ofFn (fun j : Fin N => j)) hΨ) _

/-! ## 5. The commutator identity

`[g(n₀), M](Q_{B,i}Φ) = exclFunOp (Δg) (P_{B,i}(M Q_{B,i}Φ))`, `Δg r = g (r+1) − g r`. -/

theorem commutator_eq_exclFunOp_gen {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (volume A).toReal)
    (hAc : A ⊆ acube ℓ) (g : ℝ → ℝ) (i : Fin N) {Φ : X N → ℝ} (hΦ : GoodState ℓ Φ)
    {fib : E3 → ℝ} (hfm : Measurable fib) {Cfib : ℝ}
    (hfibb : ∀ z ∈ acube ℓ, |fib z| ≤ Cfib) :
    (fun x : X N => n0FunOp volA A g (fun y : X N => fib (y i) * boxQInd volA A i Φ y) x
        - fib (x i) * n0FunOp volA A g (boxQInd volA A i Φ) x)
      =ᵐ[volume.restrict (abox N ℓ)]
      (fun x : X N => exclFunOp volA A i (fun r : ℝ => g (r + 1) - g r)
        (fun y : X N => boxPInd volA A i (fun y : X N => fib (y i) * boxQInd volA A i Φ y) y) x) := by
  have hu : GoodState ℓ (boxQInd volA A i Φ) := goodState_boxQInd hℓ hvol hA hvolA hAc i hΦ
  have hCfib : 0 ≤ Cfib := Cfib_nonneg hℓ hfibb
  have hMu : GoodState ℓ (fun y : X N => fib (y i) * boxQInd volA A i Φ y) :=
    goodState_fib_mul hfm i hCfib hfibb hu
  have hw : GoodState ℓ
      (fun y : X N => boxPInd volA A i (fun y : X N => fib (y i) * boxQInd volA A i Φ y) y) :=
    goodState_boxPInd hℓ hvol hA hvolA hAc i hMu
  obtain ⟨hfc, _, _, _⟩ := exclFunOpPropsB1 hℓ hvol hA hvolA hAc i
  have hfibcomm := hfc g hfm hfibb hu
  have hPiu : ∀ x ∈ abox N ℓ, boxPInd volA A i (boxQInd volA A i Φ) x = 0 :=
    fun x hx => boxPInd_boxQInd_self_zero hℓ hvol hA hvolA hAc i hΦ x hx
  have hshift : ∀ {Ψ : X N → ℝ}, GoodState ℓ Ψ → ∀ x ∈ abox N ℓ,
      n0FunOp volA A g Ψ x
        = exclFunOp volA A i (fun r : ℝ => g (r + 1)) (boxPInd volA A i Ψ) x
          + exclFunOp volA A i g (fun y => Ψ y - boxPInd volA A i Ψ y) x :=
    fun hΨ x hx => n0FunOp_eq_excl_shift hℓ hvol hA hvolA hAc g i hΨ x hx
  filter_upwards [self_mem_ae_restrict (abox_measurable N ℓ), hfibcomm] with x hx hxc
  have h1 := hshift hMu x hx
  have h2 := hshift hu x hx
  have h3 : exclFunOp volA A i (fun r : ℝ => g (r + 1))
      (boxPInd volA A i (boxQInd volA A i Φ)) x = 0 := by
    rw [exclFunOp_congr_box hA hAc i (fun r : ℝ => g (r + 1))
      (f := boxPInd volA A i (boxQInd volA A i Φ)) (f' := (0 : X N → ℝ)) hPiu x hx]
    simp only [exclFunOp]
    apply Finset.sum_eq_zero
    intro S _
    have hz : n0ProjOp volA A S (0 : X N → ℝ) = 0 :=
      n0Iter_zero volA A (fun j : Fin N => decide (j ∈ S)) (List.ofFn (fun j : Fin N => j))
    rw [hz]
    simp
  have h4 : exclFunOp volA A i g
      (fun y : X N => boxQInd volA A i Φ y - boxPInd volA A i (boxQInd volA A i Φ) y) x
      = exclFunOp volA A i g (boxQInd volA A i Φ) x :=
    exclFunOp_congr_box hA hAc i g
      (f := fun y : X N => boxQInd volA A i Φ y - boxPInd volA A i (boxQInd volA A i Φ) y)
      (f' := boxQInd volA A i Φ) (fun y hy => by rw [hPiu y hy, sub_zero]) x hx
  have h5 := exclFunOp_sub hℓ hvol hA hvolA hAc i g hMu hw x hx
  rw [h1, h2, h3, h4, h5]
  simp only [zero_add]
  rw [← hxc]
  linarith [exclFunOp_shift_sub volA A i g
    (fun y : X N => boxPInd volA A i (fun y : X N => fib (y i) * boxQInd volA A i Φ y) y) x]

/-! ## 6. Cauchy–Schwarz on the box -/

theorem pairing_le_sqrt {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {f g : X N → ℝ}
    (hf : GoodState ℓ f) (hg : GoodState ℓ g) :
    |∫ x in abox N ℓ, f x * g x|
      ≤ Real.sqrt (∫ x in abox N ℓ, (f x) ^ 2)
        * Real.sqrt (∫ x in abox N ℓ, (g x) ^ 2) := by
  obtain ⟨hfm, Cf, hfb⟩ := hf
  obtain ⟨hgm, Cg, hgb⟩ := hg
  have hfin : (volume : Measure (X N)) (abox N ℓ) < ∞ := abox_lt_top N ℓ hℓ.le
  haveI : IsFiniteMeasure ((volume : Measure (X N)).restrict (abox N ℓ)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩
  have hbf : ∀ᵐ x ∂(volume.restrict (abox N ℓ)), |f x| ≤ Cf := by
    filter_upwards [self_mem_ae_restrict (abox_measurable N ℓ)] with x hx
    exact hfb x hx
  have hbg : ∀ᵐ x ∂(volume.restrict (abox N ℓ)), |g x| ≤ Cg := by
    filter_upwards [self_mem_ae_restrict (abox_measurable N ℓ)] with x hx
    exact hgb x hx
  have hcs := Q0C.integral_mul_sq_le (μ := volume.restrict (abox N ℓ))
    hfm.aestronglyMeasurable hgm.aestronglyMeasurable hbf hbg
  have hA : 0 ≤ ∫ x in abox N ℓ, (f x) ^ 2 := integral_nonneg (fun x => sq_nonneg _)
  calc |∫ x in abox N ℓ, f x * g x|
      = Real.sqrt ((∫ x in abox N ℓ, f x * g x) ^ 2) := by rw [Real.sqrt_sq_eq_abs]
    _ ≤ Real.sqrt ((∫ x in abox N ℓ, (f x) ^ 2) * (∫ x in abox N ℓ, (g x) ^ 2)) :=
        Real.sqrt_le_sqrt hcs
    _ = Real.sqrt (∫ x in abox N ℓ, (f x) ^ 2)
          * Real.sqrt (∫ x in abox N ℓ, (g x) ^ 2) := Real.sqrt_mul hA _

/-! ## 7. The single-slot bound -/

theorem pairingBound_single {N : ℕ} {ℓ volA μ : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (volume A).toReal)
    (hAc : A ⊆ acube ℓ) {Φ : X N → ℝ} (hΦc : Continuous Φ)
    {fib : E3 → ℝ} (hfm : Measurable fib) {Cfib : ℝ}
    (hfibb : ∀ z ∈ acube ℓ, |fib z| ≤ Cfib) (i : Fin N) :
    |∫ x in abox N ℓ,
        ((n0FunOp volA A (fun r : ℝ => Real.sqrt (r + 1) + Real.sqrt (μ * volA))
            (fun y : X N => fib (y i) * boxQInd volA A i Φ y)) x
          - fib (x i) * (n0FunOp volA A (fun r : ℝ => Real.sqrt (r + 1) + Real.sqrt (μ * volA))
              (boxQInd volA A i Φ)) x)
        * (n0FunOp volA A (fun r : ℝ => Real.sqrt (r + 1) - Real.sqrt (μ * volA))
            (boxPInd volA A i Φ)) x|
      ≤ Cfib * Real.sqrt (∫ x in abox N ℓ, (boxQInd volA A i Φ x) ^ 2)
          * Real.sqrt (∫ x in abox N ℓ,
              (n0FunOp volA A (fun r : ℝ => Real.sqrt (r + 1) - Real.sqrt (μ * volA))
                (boxPInd volA A i Φ)) x ^ 2) := by
  classical
  obtain ⟨CΦ, hCΦ0, hCΦ⟩ := exists_abox_bound hℓ hΦc
  have hΦ : GoodState ℓ Φ := ⟨hΦc.measurable, CΦ, hCΦ⟩
  have hCfib : 0 ≤ Cfib := Cfib_nonneg hℓ hfibb
  have hu : GoodState ℓ (boxQInd volA A i Φ) := goodState_boxQInd hℓ hvol hA hvolA hAc i hΦ
  have hPΦ : GoodState ℓ (boxPInd volA A i Φ) := goodState_boxPInd hℓ hvol hA hvolA hAc i hΦ
  have hMu : GoodState ℓ (fun y : X N => fib (y i) * boxQInd volA A i Φ y) :=
    goodState_fib_mul hfm i hCfib hfibb hu
  have hW : GoodState ℓ (fun y : X N => boxPInd volA A i
      (fun y : X N => fib (y i) * boxQInd volA A i Φ y) y) :=
    goodState_boxPInd hℓ hvol hA hvolA hAc i hMu
  have hgcv : ∀ S : Finset (Fin N),
      |(fun r : ℝ => Real.sqrt (r + 1) - Real.sqrt (μ * volA)) (S.card : ℝ)|
        ≤ Real.sqrt ((N : ℝ) + 1) + |Real.sqrt (μ * volA)| := by
    intro S
    have h1 : (S.card : ℝ) ≤ (N : ℝ) := by
      have h2 : S.card ≤ (Finset.univ : Finset (Fin N)).card := Finset.card_le_univ S
      rw [Finset.card_univ, Fintype.card_fin] at h2
      exact_mod_cast h2
    calc |Real.sqrt ((S.card : ℝ) + 1) - Real.sqrt (μ * volA)|
        ≤ |Real.sqrt ((S.card : ℝ) + 1)| + |Real.sqrt (μ * volA)| := abs_sub _ _
      _ = Real.sqrt ((S.card : ℝ) + 1) + |Real.sqrt (μ * volA)| := by
          rw [abs_of_nonneg (Real.sqrt_nonneg _)]
      _ ≤ Real.sqrt ((N : ℝ) + 1) + |Real.sqrt (μ * volA)| := by
          have h3 : (S.card : ℝ) + 1 ≤ (N : ℝ) + 1 := by linarith
          have h4 := Real.sqrt_le_sqrt h3
          linarith
  have hv : GoodState ℓ
      (n0FunOp volA A (fun r : ℝ => Real.sqrt (r + 1) - Real.sqrt (μ * volA))
        (boxPInd volA A i Φ)) :=
    goodState_n0FunOp hℓ hvol hA hvolA hAc _ hgcv hPΦ
  -- the identity `D = exclFunOp δ W`
  have hD := commutator_eq_exclFunOp_gen hℓ hvol hA hvolA hAc
    (fun r : ℝ => Real.sqrt (r + 1) + Real.sqrt (μ * volA)) i hΦ hfm hfibb
  have hδfun : (fun r : ℝ => (Real.sqrt (r + 1 + 1) + Real.sqrt (μ * volA))
        - (Real.sqrt (r + 1) + Real.sqrt (μ * volA)))
      = fun r : ℝ => Real.sqrt (r + 2) - Real.sqrt (r + 1) := by
    funext r
    have h : r + 1 + 1 = r + 2 := by ring
    rw [h]
    ring
  have hDE : (fun x : X N =>
        n0FunOp volA A (fun r : ℝ => Real.sqrt (r + 1) + Real.sqrt (μ * volA))
          (fun y : X N => fib (y i) * boxQInd volA A i Φ y) x
        - fib (x i) * n0FunOp volA A (fun r : ℝ => Real.sqrt (r + 1) + Real.sqrt (μ * volA))
          (boxQInd volA A i Φ) x)
      =ᵐ[volume.restrict (abox N ℓ)]
      (fun x : X N => exclFunOp volA A i (fun r : ℝ => Real.sqrt (r + 2) - Real.sqrt (r + 1))
        (fun y : X N => boxPInd volA A i (fun y : X N => fib (y i) * boxQInd volA A i Φ y) y) x) := by
    filter_upwards [hD] with x hx
    simpa only [hδfun] using hx
  -- the filtered-sum form
  set c : Finset (Fin N) → ℝ := fun S : Finset (Fin N) =>
    Real.sqrt ((S.card : ℝ) - (if i ∈ S then 1 else 0) + 2)
      - Real.sqrt ((S.card : ℝ) - (if i ∈ S then 1 else 0) + 1) with hcdef
  have hEsum : ∀ x ∈ abox N ℓ,
      exclFunOp volA A i (fun r : ℝ => Real.sqrt (r + 2) - Real.sqrt (r + 1))
        (fun y : X N => boxPInd volA A i (fun y : X N => fib (y i) * boxQInd volA A i Φ y) y) x
      = ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin N) => i ∈ S),
          c S * n0ProjOp volA A S
            (fun y : X N => boxPInd volA A i (fun y : X N => fib (y i) * boxQInd volA A i Φ y) y) x := by
    intro x hx
    have hzero : ∀ S ∈ Finset.univ.filter (fun S : Finset (Fin N) => ¬ (i ∈ S)),
        c S * n0ProjOp volA A S
          (fun y : X N => boxPInd volA A i (fun y : X N => fib (y i) * boxQInd volA A i Φ y) y) x = 0 := by
      intro S hS
      have hiS : i ∉ S := by simpa using (Finset.mem_filter.mp hS).2
      have hvan : n0ProjOp volA A S
          (fun y : X N => boxPInd volA A i (fun y : X N => fib (y i) * boxQInd volA A i Φ y) y) x = 0 := by
        have h := n0ProjOp_boxPInd_apply hℓ hvol hA hvolA hAc S i hMu x hx
        rw [h, if_neg hiS]
      rw [hvan, mul_zero]
    have hsplit := Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset (Finset (Fin N))))
      (p := fun S : Finset (Fin N) => i ∈ S)
      (f := fun S : Finset (Fin N) => c S * n0ProjOp volA A S
        (fun y : X N => boxPInd volA A i (fun y : X N => fib (y i) * boxQInd volA A i Φ y) y) x)
    simp only [exclFunOp]
    rw [← hsplit, Finset.sum_eq_zero hzero, add_zero]
  -- the coefficient bound
  have hcb : ∀ S ∈ Finset.univ.filter (fun S : Finset (Fin N) => i ∈ S), |c S| ≤ 1 := by
    intro S hS
    have hiS : i ∈ S := (Finset.mem_filter.mp hS).2
    have hval : c S = Real.sqrt ((S.card : ℝ) + 1) - Real.sqrt ((S.card : ℝ)) := by
      rw [hcdef]
      simp only
      rw [if_pos hiS]
      have h2 : (S.card : ℝ) - 1 + 2 = (S.card : ℝ) + 1 := by ring
      have h3 : (S.card : ℝ) - 1 + 1 = (S.card : ℝ) := by ring
      rw [h2, h3]
    rw [hval]
    exact sqrt_add_one_sub_sqrt_abs_le_one (S.card : ℝ) (Nat.cast_nonneg _)
  have hwfix : ∀ x ∈ abox N ℓ,
      boxPInd volA A i (fun y : X N => boxPInd volA A i
        (fun y : X N => fib (y i) * boxQInd volA A i Φ y) y) x
      = boxPInd volA A i (fun y : X N => fib (y i) * boxQInd volA A i Φ y) x :=
    fun x hx => congrFun (boxPInd_idem volA A hA hvolA (ne_of_gt hvol) i
      (fun y : X N => fib (y i) * boxQInd volA A i Φ y)) x
  have hkey := sqIntegralProjSumLe hℓ hvol hA hvolA hAc i hW hwfix c hcb
  have hae : (fun x : X N => exclFunOp volA A i (fun r : ℝ => Real.sqrt (r + 2) - Real.sqrt (r + 1))
        (fun y : X N => boxPInd volA A i (fun y : X N => fib (y i) * boxQInd volA A i Φ y) y) x)
      =ᵐ[volume.restrict (abox N ℓ)]
      (fun x : X N => ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin N) => i ∈ S),
          c S * n0ProjOp volA A S
            (fun y : X N => boxPInd volA A i (fun y : X N => fib (y i) * boxQInd volA A i Φ y) y) x) := by
    filter_upwards [self_mem_ae_restrict (abox_measurable N ℓ)] with x hx
    exact hEsum x hx
  have hE2 : ∫ x in abox N ℓ,
        (exclFunOp volA A i (fun r : ℝ => Real.sqrt (r + 2) - Real.sqrt (r + 1))
          (fun y : X N => boxPInd volA A i (fun y : X N => fib (y i) * boxQInd volA A i Φ y) y) x) ^ 2
      ≤ ∫ x in abox N ℓ,
          (boxPInd volA A i (fun y : X N => fib (y i) * boxQInd volA A i Φ y) x) ^ 2 := by
    rw [show (∫ x in abox N ℓ,
          (exclFunOp volA A i (fun r : ℝ => Real.sqrt (r + 2) - Real.sqrt (r + 1))
            (fun y : X N => boxPInd volA A i (fun y : X N => fib (y i) * boxQInd volA A i Φ y) y) x) ^ 2)
        = ∫ x in abox N ℓ, (∑ S ∈ Finset.univ.filter (fun S : Finset (Fin N) => i ∈ S),
            c S * n0ProjOp volA A S
              (fun y : X N => boxPInd volA A i (fun y : X N => fib (y i) * boxQInd volA A i Φ y) y) x) ^ 2
        from by
      apply integral_congr_ae
      filter_upwards [hae] with x hx
      rw [hx]]
    exact hkey
  -- the contraction `∫ W² ≤ Cfib² ∫ u²`
  have hW2 : ∫ x in abox N ℓ,
        (boxPInd volA A i (fun y : X N => fib (y i) * boxQInd volA A i Φ y) x) ^ 2
      ≤ Cfib ^ 2 * ∫ x in abox N ℓ, (boxQInd volA A i Φ x) ^ 2 := by
    obtain ⟨hMuM, hMuC, hMuB⟩ := hMu
    have hcontr : ∫ x in abox N ℓ,
          (boxPInd volA A i (fun y : X N => fib (y i) * boxQInd volA A i Φ y) x) ^ 2
        ≤ ∫ x in abox N ℓ,
          (Aind A (x i) * (fun y : X N => fib (y i) * boxQInd volA A i Φ y) x) ^ 2 :=
      (boxProj_sq_contraction hℓ hvol hA hvolA hAc i hMuM (le_max_right _ _)
        (fun x hx => le_trans (hMuB x hx) (le_max_left _ _))).1
    have hAind : ∫ x in abox N ℓ,
          (Aind A (x i) * (fun y : X N => fib (y i) * boxQInd volA A i Φ y) x) ^ 2
        ≤ ∫ x in abox N ℓ,
          ((fun y : X N => fib (y i) * boxQInd volA A i Φ y) x) ^ 2 := by
      apply setIntegral_mono_ae_restrict
      · apply integrableOn_sq_of_bound hℓ
        · exact ((measurable_const.indicator hA).comp (measurable_pi_apply i)).mul hMuM
        · intro x hx
          have h1 := Aind_abs_le_one A (x i)
          have h2 := hMuB x hx
          calc |Aind A (x i) * (fun y : X N => fib (y i) * boxQInd volA A i Φ y) x|
              = |Aind A (x i)| * |(fun y : X N => fib (y i) * boxQInd volA A i Φ y) x| := abs_mul _ _
            _ ≤ 1 * max hMuC 0 :=
                mul_le_mul h1 (le_trans h2 (le_max_left _ _)) (abs_nonneg _) zero_le_one
            _ = max hMuC 0 := one_mul _
      · exact integrableOn_sq_of_bound hℓ hMuM hMuB
      · filter_upwards with x
        have h1 := Aind_abs_le_one A (x i)
        have h2 : (Aind A (x i)) ^ 2 ≤ 1 := by
          nlinarith [sq_abs (Aind A (x i)), abs_nonneg (Aind A (x i))]
        nlinarith [sq_nonneg ((fun y : X N => fib (y i) * boxQInd volA A i Φ y) x)]
    have hMu2 : ∫ x in abox N ℓ,
          ((fun y : X N => fib (y i) * boxQInd volA A i Φ y) x) ^ 2
        ≤ Cfib ^ 2 * ∫ x in abox N ℓ, (boxQInd volA A i Φ x) ^ 2 := by
      rw [← integral_const_mul]
      apply setIntegral_mono_ae_restrict
      · exact integrableOn_sq_of_bound hℓ hMuM hMuB
      · exact (integrableOn_sq_of_bound hℓ hu.1 hu.2.choose_spec).const_mul _
      · filter_upwards [self_mem_ae_restrict (abox_measurable N ℓ)] with x hx
        have h1 : |fib (x i)| ≤ Cfib := hfibb (x i) (hx i)
        have h2 : ((fun y : X N => fib (y i) * boxQInd volA A i Φ y) x) ^ 2
            = (fib (x i)) ^ 2 * (boxQInd volA A i Φ x) ^ 2 := by ring
        have h3 : (fib (x i)) ^ 2 ≤ Cfib ^ 2 := by
          nlinarith [sq_abs (fib (x i)), abs_nonneg (fib (x i)), hCfib, h1]
        rw [h2]
        exact mul_le_mul_of_nonneg_right h3 (sq_nonneg _)
    linarith [hcontr, hAind, hMu2]
  -- Cauchy–Schwarz and the conclusion
  have hδb : ∀ S : Finset (Fin N),
      |(fun r : ℝ => Real.sqrt (r + 2) - Real.sqrt (r + 1))
        ((S.card : ℝ) - (if i ∈ S then 1 else 0))| ≤ 1 := by
    intro S
    have hval : (fun r : ℝ => Real.sqrt (r + 2) - Real.sqrt (r + 1))
        ((S.card : ℝ) - (if i ∈ S then 1 else 0)) = c S := by
      simp only [hcdef]
    rw [hval]
    by_cases hiS : i ∈ S
    · exact hcb S (Finset.mem_filter.mpr ⟨Finset.mem_univ S, hiS⟩)
    · have h2 : c S = Real.sqrt ((S.card : ℝ) + 2) - Real.sqrt ((S.card : ℝ) + 1) := by
        rw [hcdef]
        simp only
        rw [if_neg hiS]
        have h3 : (S.card : ℝ) - 0 + 2 = (S.card : ℝ) + 2 := by ring
        have h4 : (S.card : ℝ) - 0 + 1 = (S.card : ℝ) + 1 := by ring
        rw [h3, h4]
      rw [h2]
      have h5 := sqrt_add_one_sub_sqrt_abs_le_one ((S.card : ℝ) + 1) (by positivity)
      have h6 : (S.card : ℝ) + 1 + 1 = (S.card : ℝ) + 2 := by ring
      rwa [h6] at h5
  have hEgood : GoodState ℓ (exclFunOp volA A i (fun r : ℝ => Real.sqrt (r + 2) - Real.sqrt (r + 1))
      (fun y : X N => boxPInd volA A i (fun y : X N => fib (y i) * boxQInd volA A i Φ y) y)) :=
    goodState_exclFunOp hℓ hvol hA hvolA hAc i _ hδb hW
  have hCS := pairing_le_sqrt hℓ hEgood hv
  have hDEint : ∫ x in abox N ℓ,
        (fun x : X N =>
          n0FunOp volA A (fun r : ℝ => Real.sqrt (r + 1) + Real.sqrt (μ * volA))
            (fun y : X N => fib (y i) * boxQInd volA A i Φ y) x
          - fib (x i) * n0FunOp volA A (fun r : ℝ => Real.sqrt (r + 1) + Real.sqrt (μ * volA))
            (boxQInd volA A i Φ) x) x
        * (n0FunOp volA A (fun r : ℝ => Real.sqrt (r + 1) - Real.sqrt (μ * volA))
            (boxPInd volA A i Φ)) x
      = ∫ x in abox N ℓ,
        (exclFunOp volA A i (fun r : ℝ => Real.sqrt (r + 2) - Real.sqrt (r + 1))
          (fun y : X N => boxPInd volA A i (fun y : X N => fib (y i) * boxQInd volA A i Φ y) y)) x
        * (n0FunOp volA A (fun r : ℝ => Real.sqrt (r + 1) - Real.sqrt (μ * volA))
            (boxPInd volA A i Φ)) x := by
    apply integral_congr_ae
    filter_upwards [hDE] with x hx
    rw [hx]
  rw [hDEint]
  refine le_trans hCS ?_
  have hE2' : Real.sqrt (∫ x in abox N ℓ,
      ((exclFunOp volA A i (fun r : ℝ => Real.sqrt (r + 2) - Real.sqrt (r + 1))
        (fun y : X N => boxPInd volA A i (fun y : X N => fib (y i) * boxQInd volA A i Φ y) y)) x) ^ 2)
      ≤ Real.sqrt (∫ x in abox N ℓ, (boxQInd volA A i Φ x) ^ 2) * Cfib := by
    have hAi : 0 ≤ ∫ x in abox N ℓ, (boxQInd volA A i Φ x) ^ 2 :=
      integral_nonneg (fun x => sq_nonneg _)
    have h1 : (∫ x in abox N ℓ,
        ((exclFunOp volA A i (fun r : ℝ => Real.sqrt (r + 2) - Real.sqrt (r + 1))
          (fun y : X N => boxPInd volA A i (fun y : X N => fib (y i) * boxQInd volA A i Φ y) y)) x) ^ 2)
        ≤ Cfib ^ 2 * (∫ x in abox N ℓ, (boxQInd volA A i Φ x) ^ 2) := le_trans hE2 hW2
    calc Real.sqrt (∫ x in abox N ℓ,
          ((exclFunOp volA A i (fun r : ℝ => Real.sqrt (r + 2) - Real.sqrt (r + 1))
            (fun y : X N => boxPInd volA A i (fun y : X N => fib (y i) * boxQInd volA A i Φ y) y)) x) ^ 2)
        ≤ Real.sqrt (Cfib ^ 2 * (∫ x in abox N ℓ, (boxQInd volA A i Φ x) ^ 2)) :=
          Real.sqrt_le_sqrt h1
      _ = Real.sqrt (∫ x in abox N ℓ, (boxQInd volA A i Φ x) ^ 2) * Cfib := by
          rw [show Cfib ^ 2 * (∫ x in abox N ℓ, (boxQInd volA A i Φ x) ^ 2)
              = (∫ x in abox N ℓ, (boxQInd volA A i Φ x) ^ 2) * Cfib ^ 2 from by ring]
          rw [Real.sqrt_mul hAi, Real.sqrt_sq_eq_abs, abs_of_nonneg hCfib]
  calc Real.sqrt (∫ x in abox N ℓ,
        ((exclFunOp volA A i (fun r : ℝ => Real.sqrt (r + 2) - Real.sqrt (r + 1))
          (fun y : X N => boxPInd volA A i (fun y : X N => fib (y i) * boxQInd volA A i Φ y) y)) x) ^ 2)
      * Real.sqrt (∫ x in abox N ℓ,
          (n0FunOp volA A (fun r : ℝ => Real.sqrt (r + 1) - Real.sqrt (μ * volA))
            (boxPInd volA A i Φ)) x ^ 2)
      ≤ (Real.sqrt (∫ x in abox N ℓ, (boxQInd volA A i Φ x) ^ 2) * Cfib)
        * Real.sqrt (∫ x in abox N ℓ,
          (n0FunOp volA A (fun r : ℝ => Real.sqrt (r + 1) - Real.sqrt (μ * volA))
            (boxPInd volA A i Φ)) x ^ 2) :=
        mul_le_mul hE2' le_rfl (Real.sqrt_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hCfib)
    _ = Cfib * Real.sqrt (∫ x in abox N ℓ, (boxQInd volA A i Φ x) ^ 2)
        * Real.sqrt (∫ x in abox N ℓ,
          (n0FunOp volA A (fun r : ℝ => Real.sqrt (r + 1) - Real.sqrt (μ * volA))
            (boxPInd volA A i Φ)) x ^ 2) := by ring

theorem commutatorPairingB1 {N : ℕ} {ℓ volA μ : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
    {fib : EuclideanSpace ℝ (Fin 3) → ℝ} (hfm : Measurable fib)
    {Cfib : ℝ} (hfibb : ∀ z ∈ Submission.BoseGases.acube ℓ, |fib z| ≤ Cfib) :
    |∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
        ((Work.BoseFixB1S.n0FunOp volA A (fun r : ℝ => Real.sqrt (r + 1) + Real.sqrt (μ * volA))
            (fun y : Submission.BoseGases.X N =>
              fib (y i) * Work.UBBInputs8.boxQInd volA A i Φ y)) x
          - fib (x i) * (Work.BoseFixB1S.n0FunOp volA A
              (fun r : ℝ => Real.sqrt (r + 1) + Real.sqrt (μ * volA))
              (Work.UBBInputs8.boxQInd volA A i Φ)) x)
        * (Work.BoseFixB1S.n0FunOp volA A
            (fun r : ℝ => Real.sqrt (r + 1) - Real.sqrt (μ * volA))
            (Work.UBBInputs8.boxPInd volA A i Φ)) x|
      ≤ 4 * Cfib * Real.sqrt
          ((∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
              (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2)
            * (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
                (Work.BoseFixB1S.n0FunOp volA A
                  (fun r : ℝ => Real.sqrt (r + 1) - Real.sqrt (μ * volA))
                  (Work.UBBInputs8.boxPInd volA A i Φ)) x ^ 2)) := by
  classical
  have hCfib : 0 ≤ Cfib := Cfib_nonneg hℓ hfibb
  let Ai : Fin N → ℝ := fun i : Fin N =>
    ∫ x in abox N ℓ, (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2
  let Bi : Fin N → ℝ := fun i : Fin N =>
    ∫ x in abox N ℓ, (Work.BoseFixB1S.n0FunOp volA A
      (fun r : ℝ => Real.sqrt (r + 1) - Real.sqrt (μ * volA))
      (Work.UBBInputs8.boxPInd volA A i Φ)) x ^ 2
  have hsingle : ∀ i : Fin N,
      |∫ x in Submission.BoseGases.abox N ℓ,
        ((Work.BoseFixB1S.n0FunOp volA A (fun r : ℝ => Real.sqrt (r + 1) + Real.sqrt (μ * volA))
            (fun y : Submission.BoseGases.X N =>
              fib (y i) * Work.UBBInputs8.boxQInd volA A i Φ y)) x
          - fib (x i) * (Work.BoseFixB1S.n0FunOp volA A
              (fun r : ℝ => Real.sqrt (r + 1) + Real.sqrt (μ * volA))
              (Work.UBBInputs8.boxQInd volA A i Φ)) x)
        * (Work.BoseFixB1S.n0FunOp volA A
            (fun r : ℝ => Real.sqrt (r + 1) - Real.sqrt (μ * volA))
            (Work.UBBInputs8.boxPInd volA A i Φ)) x|
      ≤ Cfib * Real.sqrt (Ai i) * Real.sqrt (Bi i) :=
    fun i => pairingBound_single hℓ hvol hA hvolA hAc hΦc hfm hfibb i
  have hA0 : ∀ i : Fin N, 0 ≤ Ai i := fun i => integral_nonneg (fun x => sq_nonneg _)
  have hB0 : ∀ i : Fin N, 0 ≤ Bi i := fun i => integral_nonneg (fun x => sq_nonneg _)
  calc |∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
        ((Work.BoseFixB1S.n0FunOp volA A (fun r : ℝ => Real.sqrt (r + 1) + Real.sqrt (μ * volA))
            (fun y : Submission.BoseGases.X N =>
              fib (y i) * Work.UBBInputs8.boxQInd volA A i Φ y)) x
          - fib (x i) * (Work.BoseFixB1S.n0FunOp volA A
              (fun r : ℝ => Real.sqrt (r + 1) + Real.sqrt (μ * volA))
              (Work.UBBInputs8.boxQInd volA A i Φ)) x)
        * (Work.BoseFixB1S.n0FunOp volA A
            (fun r : ℝ => Real.sqrt (r + 1) - Real.sqrt (μ * volA))
            (Work.UBBInputs8.boxPInd volA A i Φ)) x|
      ≤ ∑ i : Fin N, |∫ x in Submission.BoseGases.abox N ℓ,
        ((Work.BoseFixB1S.n0FunOp volA A (fun r : ℝ => Real.sqrt (r + 1) + Real.sqrt (μ * volA))
            (fun y : Submission.BoseGases.X N =>
              fib (y i) * Work.UBBInputs8.boxQInd volA A i Φ y)) x
          - fib (x i) * (Work.BoseFixB1S.n0FunOp volA A
              (fun r : ℝ => Real.sqrt (r + 1) + Real.sqrt (μ * volA))
              (Work.UBBInputs8.boxQInd volA A i Φ)) x)
        * (Work.BoseFixB1S.n0FunOp volA A
            (fun r : ℝ => Real.sqrt (r + 1) - Real.sqrt (μ * volA))
            (Work.UBBInputs8.boxPInd volA A i Φ)) x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin N, Cfib * Real.sqrt (Ai i) * Real.sqrt (Bi i) :=
        Finset.sum_le_sum (fun i _ => hsingle i)
    _ = Cfib * ∑ i : Fin N, (Real.sqrt (Ai i) * Real.sqrt (Bi i)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
    _ ≤ Cfib * Real.sqrt ((∑ i : Fin N, Ai i) * (∑ i : Fin N, Bi i)) := by
        apply mul_le_mul_of_nonneg_left _ hCfib
        have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin N))
          (fun i : Fin N => Real.sqrt (Ai i)) (fun i : Fin N => Real.sqrt (Bi i))
        have h1 : (∑ i : Fin N, (Real.sqrt (Ai i)) ^ 2) = ∑ i : Fin N, Ai i :=
          Finset.sum_congr rfl (fun i _ => Real.sq_sqrt (hA0 i))
        have h2 : (∑ i : Fin N, (Real.sqrt (Bi i)) ^ 2) = ∑ i : Fin N, Bi i :=
          Finset.sum_congr rfl (fun i _ => Real.sq_sqrt (hB0 i))
        rw [h1, h2] at hcs
        exact Real.le_sqrt_of_sq_le hcs
    _ ≤ 4 * Cfib * Real.sqrt ((∑ i : Fin N, Ai i) * (∑ i : Fin N, Bi i)) := by
        have h0 : 0 ≤ Cfib * Real.sqrt ((∑ i : Fin N, Ai i) * (∑ i : Fin N, Bi i)) :=
          mul_nonneg hCfib (Real.sqrt_nonneg _)
        linarith

end Work.BoseFixB1S
