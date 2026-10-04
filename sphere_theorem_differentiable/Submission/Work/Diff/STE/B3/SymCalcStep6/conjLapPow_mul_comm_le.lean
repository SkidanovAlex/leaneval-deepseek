import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.B3.SymCalcStep5.conjCut_lapPow
import Submission.Work.Diff.STE.B3.SymCalcStep1.laplacian_pow_mul_comm_le
import Submission.Work.Diff.STE.B3.SymCalcStep1.fourierCoeff_comp_le
import Submission.Work.Diff.STE.B3.SymCalcStep6.lapPow_toolbox
import Submission.Work.Diff.STE.B3.flat_diag_pairing_le
import Submission.Work.Diff.STE.B3.SymCalcStep6.conj_cut_comm_lapPow_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# B3 symbol calculus: `[P_k, M_a]` is of order `2k − 1` (`P_k = conjLapPow k T T'`)

This file proves `Work.Diff.STE.B3.SymCalcStep6.conjLapPow_mul_comm_le`, the *multiplication*
companion of the conjugation identity `SymCalcStep5.conjCut_lapPow_comm`: for the conjugate
Laplacian power

  `P_k = conjLapPow k T T' = comp_T ∘ Λ^k ∘ comp_{T'}`

(where `Λ^k = lapPow k` is the flat Laplacian power, `T` the chart transition, `T'` its inverse)
and a fixed smooth `1`-periodic multiplier `a`, the commutator with the pointwise multiplication
`M_a` loses exactly `2k − 1` derivatives:

  `CSq s (fourierCoeff (P_k (a · g) − a · P_k g)) ≤ C · CSq (s + 2k − 1) (fourierCoeff g)`,

with `C` depending only on `a`, `T`, `T'`, `k`, `s` (uniformly in `g`).

## Route

1. **Algebraic identity** (pure rewriting, `conjLapPow`/`compMap` being definitions): with
   `β := compMap T' a` the multiplier in the *other* chart and `γ := compMap T' g`,

     `P_k (a · g) − a · P_k g = compMap T (Λ^k (β · γ) − β · Λ^k γ)`,

   because `compMap T β = a` (`compMap_T_compMap_T'`) and `compMap T` is multiplicative.
   So the problem is pushed into the flat chart, where the operator is the plain multiplier
   `Λ^k` and the multiplication is by `β`.

2. **The flat Leibniz estimate** (`dB3_flat_comm_le`, from the proved
   `SymCalcStep1.laplacian_pow_mul_comm_le`): on the Fourier side the commutator is the family

     `m ↦ λ(m)^k (β·γ)^(m) − (β · Λ^k γ)^(m) = λ(m)^k conv β̂ γ̂ (m) − conv β̂ (λ^k γ̂) (m)`,

   and `laplacian_pow_mul_comm_le` bounds its `CSq s` by `CSq (s + 2k − 1) γ̂`; the identification
   of the families is `dB3_fourierCoeff_lapPow_comm` (using `fourierCoeff_lapPow`,
   `fourierCoeff_mul` and `fourierCoeff_sub_of_continuous`).

3. **The two conjugations are harmless**: `fourierCoeff_comp_le` bounds `CSq s` of the Fourier
   coefficients of `u ∘ T` by `CSq s` of those of `u`, for both `T` and `T'`.  The invertibility
   of the differentials of `T` and `T'` (a hypothesis of that estimate) is *derived* from the two
   inverse identities `T' ∘ T = id`, `T ∘ T' = id` (the differential of a left inverse provides a
   one-sided inverse of the differential, hence a nonzero determinant), and the `1`-periodicity of
   `T'` is `SymCalcStep1.shift_T'`.
-/

set_option maxHeartbeats 2000000

namespace Work.Diff.STE.B3.SymCalcStep6

open MeasureTheory BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The Fourier coefficients of the flat commutator `[Λ^k, M_β] γ`.**  For smooth `1`-periodic
`β`, `γ` the coefficient family of `Λ^k (β γ) − β · Λ^k γ` is
`m ↦ λ(m)^k · (β̂ * γ̂)(m) − (β̂ * (λ^k · γ̂))(m)`. -/
lemma dB3_fourierCoeff_lapPow_comm (k : ℕ) (β γ : (ι → ℝ) → ℂ)
    (hβ : ContDiff ℝ (⊤ : ℕ∞) β) (hβp : Work.Diff.STE.Periodic1 β)
    (hγ : ContDiff ℝ (⊤ : ℕ∞) γ) (hγp : Work.Diff.STE.Periodic1 γ) :
    Work.Diff.STE.fourierCoeff (fun x => Work.Diff.STE.B3.SymCalcStep5.lapPow k (fun y => β y * γ y) x
        - β x * Work.Diff.STE.B3.SymCalcStep5.lapPow k γ x)
      = fun m : ι → ℤ => (((Work.Diff.STE.B3.SymCalc.flatLam m) ^ k : ℝ) : ℂ)
            * Work.Diff.STE.conv (Work.Diff.STE.fourierCoeff β) (Work.Diff.STE.fourierCoeff γ) m
          - Work.Diff.STE.conv (Work.Diff.STE.fourierCoeff β)
              (fun m : ι → ℤ => (((Work.Diff.STE.B3.SymCalc.flatLam m) ^ k : ℝ) : ℂ)
                 * Work.Diff.STE.fourierCoeff γ m) m := by
  funext m
  have hβγ : ContDiff ℝ (⊤ : ℕ∞) (fun y : ι → ℝ => β y * γ y) := hβ.mul hγ
  have hβγp : Work.Diff.STE.Periodic1 (fun y : ι → ℝ => β y * γ y) :=
    fun i x => by
      show β (x + Pi.single i 1) * γ (x + Pi.single i 1) = β x * γ x
      rw [hβp i x, hγp i x]
  have hγsm : ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.B3.SymCalcStep5.lapPow k γ) :=
    Work.Diff.STE.B3.contDiff_lapPow k γ hγ hγp
  have hβγc : Continuous (Work.Diff.STE.B3.SymCalcStep5.lapPow k (fun y : ι → ℝ => β y * γ y)) :=
    (Work.Diff.STE.B3.contDiff_lapPow k _ hβγ hβγp).continuous
  have hb2c : Continuous (fun x : ι → ℝ => β x * Work.Diff.STE.B3.SymCalcStep5.lapPow k γ x) :=
    hβ.continuous.mul hγsm.continuous
  have hsub := Work.Diff.STE.flat.fourierCoeff_sub_of_continuous _ _ hβγc hb2c m
  have hconv : Work.Diff.STE.fourierCoeff (fun y : ι → ℝ => β y * γ y) m
      = Work.Diff.STE.conv (Work.Diff.STE.fourierCoeff β) (Work.Diff.STE.fourierCoeff γ) m := by
    have h := Work.Diff.STE.B3.fourierCoeff_mul γ β hγ hβ hβp m
    rw [show (fun x : ι → ℝ => γ x * β x) = fun x : ι → ℝ => β x * γ x from
      funext fun x => mul_comm _ _] at h
    exact h
  have hA : Work.Diff.STE.fourierCoeff
        (Work.Diff.STE.B3.SymCalcStep5.lapPow k (fun y : ι → ℝ => β y * γ y)) m
      = (((Work.Diff.STE.B3.SymCalc.flatLam m) ^ k : ℝ) : ℂ)
          * Work.Diff.STE.conv (Work.Diff.STE.fourierCoeff β) (Work.Diff.STE.fourierCoeff γ) m := by
    rw [Work.Diff.STE.B3.fourierCoeff_lapPow k _ hβγ hβγp m, hconv]
  have hB : Work.Diff.STE.fourierCoeff
        (fun x : ι → ℝ => β x * Work.Diff.STE.B3.SymCalcStep5.lapPow k γ x) m
      = Work.Diff.STE.conv (Work.Diff.STE.fourierCoeff β)
          (fun m : ι → ℤ => (((Work.Diff.STE.B3.SymCalc.flatLam m) ^ k : ℝ) : ℂ)
             * Work.Diff.STE.fourierCoeff γ m) m := by
    have h := Work.Diff.STE.B3.fourierCoeff_mul (Work.Diff.STE.B3.SymCalcStep5.lapPow k γ) β
      hγsm hβ hβp m
    rw [show (fun x : ι → ℝ => Work.Diff.STE.B3.SymCalcStep5.lapPow k γ x * β x)
        = fun x : ι → ℝ => β x * Work.Diff.STE.B3.SymCalcStep5.lapPow k γ x from
      funext fun x => mul_comm _ _] at h
    rw [h]
    congr 1
    funext m'
    exact Work.Diff.STE.B3.fourierCoeff_lapPow k γ hγ hγp m'
  rw [hsub, hA, hB]

/-- **The flat Leibniz estimate in function form.**  For a fixed smooth `1`-periodic multiplier
`a` there is `C` with `CSq s (fourierCoeff ([Λ^k, M_a] γ)) ≤ C · CSq (s + 2k − 1) (fourierCoeff γ)`
for all smooth `1`-periodic `γ`. -/
lemma dB3_flat_comm_le (a : (ι → ℝ) → ℂ) (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (hap : Work.Diff.STE.Periodic1 a) (k : ℕ) (hk : 1 ≤ k) (s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ γ : (ι → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) γ → Work.Diff.STE.Periodic1 γ →
      Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (fun x =>
          Work.Diff.STE.B3.SymCalcStep5.lapPow k (fun y => a y * γ y) x
            - a x * Work.Diff.STE.B3.SymCalcStep5.lapPow k γ x))
        ≤ C * Work.Diff.STE.CSq (s + 2 * k - 1) (Work.Diff.STE.fourierCoeff γ) := by
  obtain ⟨C, hC, hCb⟩ := Work.Diff.STE.B3.SymCalcStep1.laplacian_pow_mul_comm_le
    (Work.Diff.STE.fourierCoeff a)
    (fun N => Work.Diff.STE.B3.summable_wt_pow_mul_norm_fourierCoeff N a ha hap) k hk s
  refine ⟨C, hC, fun γ hγ hγp => ?_⟩
  rw [dB3_fourierCoeff_lapPow_comm k a γ ha hap hγ hγp]
  exact hCb (Work.Diff.STE.fourierCoeff γ)
    (Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff γ hγ hγp (s + 2 * k - 1))

theorem conjLapPow_mul_comm_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : (ι → ℝ) → ℂ) (ha : ContDiff ℝ (⊤ : ℕ∞) a) (hap : Work.Diff.STE.Periodic1 a)
    (T T' : (ι → ℝ) → (ι → ℝ))
    (hT : ContDiff ℝ (⊤ : ℕ∞) T) (hT' : ContDiff ℝ (⊤ : ℕ∞) T')
    (hTinv1 : ∀ x : ι → ℝ, T' (T x) = x) (hTinv2 : ∀ y : ι → ℝ, T (T' y) = y)
    (hTper : ∀ (i : ι) (x : ι → ℝ), T (x + Pi.single i 1) = T x + Pi.single i 1)
    (k : ℕ) (hk : 1 ≤ k) (s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ g : (ι → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) g → Work.Diff.STE.Periodic1 g →
        Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (fun x : ι → ℝ =>
            Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' (fun y : ι → ℝ => a y * g y) x
              - a x * Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' g x))
          ≤ C * Work.Diff.STE.CSq (s + 2 * k - 1) (Work.Diff.STE.fourierCoeff g) := by
  classical
  have hinjT : Function.Injective T := fun x y hxy => by rw [← hTinv1 x, hxy, hTinv1 y]
  have hinjT' : Function.Injective T' := fun x y hxy => by rw [← hTinv2 x, hxy, hTinv2 y]
  -- `T' ∘ T = id` (and `T ∘ T' = id`) makes the differential of `T` (resp. `T'`) invertible
  have hdet_of : ∀ (A B : (ι → ℝ) →L[ℝ] (ι → ℝ)), A.comp B = 1 → B.det ≠ 0 := by
    intro A B hcomp hz
    have hinj : Function.Injective B := fun u v huv => by
      have h1 := congrArg (fun (L : (ι → ℝ) →L[ℝ] (ι → ℝ)) => L u) hcomp
      have h2 := congrArg (fun (L : (ι → ℝ) →L[ℝ] (ι → ℝ)) => L v) hcomp
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply] at h1 h2
      rw [huv] at h1
      exact h1.symm.trans h2
    have hz' : LinearMap.det ((B : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))) = 0 := hz
    exact (LinearMap.det_eq_zero_iff_ker_ne_bot.mp hz') (by rw [LinearMap.ker_eq_bot]; exact hinj)
  have hdetT : ∀ z : ι → ℝ, (fderiv ℝ T z).det ≠ 0 := by
    intro z
    have hcomp : fderiv ℝ (fun x => T' (T x)) z
        = (fderiv ℝ T' (T z)).comp (fderiv ℝ T z) :=
      fderiv_comp z ((hT'.differentiable (by simp)).differentiableAt)
        ((hT.differentiable (by simp)).differentiableAt)
    have h1 : fderiv ℝ (fun x => T' (T x)) z = 1 := by
      rw [show (fun x : ι → ℝ => T' (T x)) = id from funext hTinv1]
      exact fderiv_id
    have h2 : (fderiv ℝ T' (T z)).comp (fderiv ℝ T z) = 1 := by rw [← hcomp]; exact h1
    exact hdet_of _ _ h2
  have hdetT' : ∀ z : ι → ℝ, (fderiv ℝ T' z).det ≠ 0 := by
    intro z
    have hcomp : fderiv ℝ (fun y => T (T' y)) z
        = (fderiv ℝ T (T' z)).comp (fderiv ℝ T' z) :=
      fderiv_comp z ((hT.differentiable (by simp)).differentiableAt)
        ((hT'.differentiable (by simp)).differentiableAt)
    have h1 : fderiv ℝ (fun y => T (T' y)) z = 1 := by
      rw [show (fun y : ι → ℝ => T (T' y)) = id from funext hTinv2]
      exact fderiv_id
    have h2 : (fderiv ℝ T (T' z)).comp (fderiv ℝ T' z) = 1 := by rw [← hcomp]; exact h1
    exact hdet_of _ _ h2
  have hshift : ∀ (i : ι) (z : ι → ℝ), T' (z + Pi.single i 1) = T' z + Pi.single i 1 :=
    fun i => Work.Diff.STE.B3.SymCalcStep1.shift_T' T T' hTper hTinv1 hTinv2 i
  -- the three `g`-independent estimates
  obtain ⟨C1, hC1, hC1b⟩ :=
    Work.Diff.STE.B3.SymCalcStep1.fourierCoeff_comp_le s T hT hTper hinjT hdetT
  obtain ⟨C2, hC2, hC2b⟩ :=
    Work.Diff.STE.B3.SymCalcStep1.fourierCoeff_comp_le (s + 2 * k - 1) T' hT' hshift hinjT' hdetT'
  have hβsm : ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.B3.SymCalc.compMap T' a) := ha.comp hT'
  have hβp : Work.Diff.STE.Periodic1 (Work.Diff.STE.B3.SymCalc.compMap T' a) := fun i x => by
    show a (T' (x + Pi.single i 1)) = a (T' x)
    rw [hshift i x]; exact hap i (T' x)
  obtain ⟨C3, hC3, hC3b⟩ :=
    dB3_flat_comm_le (Work.Diff.STE.B3.SymCalc.compMap T' a) hβsm hβp k hk s
  refine ⟨C1 * C3 * C2, by positivity, fun g hg hgp => ?_⟩
  have hγsm : ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.B3.SymCalc.compMap T' g) := hg.comp hT'
  have hγp : Work.Diff.STE.Periodic1 (Work.Diff.STE.B3.SymCalc.compMap T' g) := fun i x => by
    show g (T' (x + Pi.single i 1)) = g (T' x)
    rw [hshift i x]; exact hgp i (T' x)
  have hD'sm : ContDiff ℝ (⊤ : ℕ∞) (fun z : ι → ℝ =>
      Work.Diff.STE.B3.SymCalcStep5.lapPow k (fun y : ι → ℝ =>
          Work.Diff.STE.B3.SymCalc.compMap T' a y * Work.Diff.STE.B3.SymCalc.compMap T' g y) z
        - Work.Diff.STE.B3.SymCalc.compMap T' a z
            * Work.Diff.STE.B3.SymCalcStep5.lapPow k (Work.Diff.STE.B3.SymCalc.compMap T' g) z) :=
    (Work.Diff.STE.B3.contDiff_lapPow k _ (hβsm.mul hγsm)
        (Work.Diff.STE.B3.SymCalcStep1.Periodic1_mul' hβp hγp)).sub
      (hβsm.mul (Work.Diff.STE.B3.contDiff_lapPow k _ hγsm hγp))
  have hD'p : Work.Diff.STE.Periodic1 (fun z : ι → ℝ =>
      Work.Diff.STE.B3.SymCalcStep5.lapPow k (fun y : ι → ℝ =>
          Work.Diff.STE.B3.SymCalc.compMap T' a y * Work.Diff.STE.B3.SymCalc.compMap T' g y) z
        - Work.Diff.STE.B3.SymCalc.compMap T' a z
            * Work.Diff.STE.B3.SymCalcStep5.lapPow k (Work.Diff.STE.B3.SymCalc.compMap T' g) z) :=
    Work.Diff.STE.B3.SymCalcStep1.Periodic1_sub'
      (Work.Diff.STE.B3.periodic1_lapPow k _)
      (Work.Diff.STE.B3.SymCalcStep1.Periodic1_mul' hβp (Work.Diff.STE.B3.periodic1_lapPow k _))
  -- the algebraic identity: `P_k (a·g) − a · P_k g = comp_T (Λ^k (β·γ) − β · Λ^k γ)`
  have hDfun : (fun x : ι → ℝ =>
        Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' (fun y : ι → ℝ => a y * g y) x
          - a x * Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' g x)
      = Work.Diff.STE.B3.SymCalc.compMap T (fun z : ι → ℝ =>
          Work.Diff.STE.B3.SymCalcStep5.lapPow k (fun y : ι → ℝ =>
              Work.Diff.STE.B3.SymCalc.compMap T' a y * Work.Diff.STE.B3.SymCalc.compMap T' g y) z
            - Work.Diff.STE.B3.SymCalc.compMap T' a z
                * Work.Diff.STE.B3.SymCalcStep5.lapPow k (Work.Diff.STE.B3.SymCalc.compMap T' g) z) := by
    funext x
    simp only [Work.Diff.STE.B3.SymCalc.compMap, Work.Diff.STE.B3.SymCalcStep5.conjLapPow]
    rw [(congrArg a (hTinv1 x)).symm]
    rfl
  calc Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (fun x : ι → ℝ =>
          Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' (fun y : ι → ℝ => a y * g y) x
            - a x * Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' g x))
      = Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (Work.Diff.STE.B3.SymCalc.compMap T
          (fun z : ι → ℝ => Work.Diff.STE.B3.SymCalcStep5.lapPow k (fun y : ι → ℝ =>
              Work.Diff.STE.B3.SymCalc.compMap T' a y * Work.Diff.STE.B3.SymCalc.compMap T' g y) z
            - Work.Diff.STE.B3.SymCalc.compMap T' a z
                * Work.Diff.STE.B3.SymCalcStep5.lapPow k (Work.Diff.STE.B3.SymCalc.compMap T' g) z))) := by
          rw [hDfun]
    _ ≤ C1 * Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (fun z : ι → ℝ =>
            Work.Diff.STE.B3.SymCalcStep5.lapPow k (fun y : ι → ℝ =>
                Work.Diff.STE.B3.SymCalc.compMap T' a y * Work.Diff.STE.B3.SymCalc.compMap T' g y) z
              - Work.Diff.STE.B3.SymCalc.compMap T' a z
                  * Work.Diff.STE.B3.SymCalcStep5.lapPow k (Work.Diff.STE.B3.SymCalc.compMap T' g) z)) :=
          hC1b _ hD'sm hD'p
    _ ≤ C1 * (C3 * Work.Diff.STE.CSq (s + 2 * k - 1)
            (Work.Diff.STE.fourierCoeff (Work.Diff.STE.B3.SymCalc.compMap T' g))) :=
          mul_le_mul_of_nonneg_left (hC3b _ hγsm hγp) hC1
    _ ≤ C1 * (C3 * (C2 * Work.Diff.STE.CSq (s + 2 * k - 1) (Work.Diff.STE.fourierCoeff g))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hC2b g hg hgp) hC3) hC1
    _ = (C1 * C3 * C2) * Work.Diff.STE.CSq (s + 2 * k - 1) (Work.Diff.STE.fourierCoeff g) := by
          ring

end Work.Diff.STE.B3.SymCalcStep6
