import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.B3.SymCalc
import Submission.Work.Diff.STE.B3.SymCalcStep1.flat_multiplier_commutator
import Submission.Work.Diff.STE.B3.SymCalcStep1.fourierCoeff_comp_le
import Submission.Work.Diff.STE.B3.SymCalcStep1.conj_cut_aux
import Submission.Work.Diff.STE.B3.SymCalcStep1.firstOrder_comm_trunc_le
import Submission.Work.Diff.STE.fourierCoeff_mul_seriesFun
import Submission.Work.Diff.STE.flat.seriesFun_fourierCoeff
import Submission.Work.Diff.STE.B3.SymCalcStep5.conjCut_lapPow

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open MeasureTheory BigOperators

namespace Work.Diff.STE.B3.SymCalcStep6

theorem conjCut_multiplier_gain
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : (ι → ℝ) → ℝ)
    (hρb : ∀ y : ι → ℝ, ‖ρ y‖ ≤ 1)
    (hdiam : ∀ y : ι → ℝ, 2 < ∑ i, (y i) ^ 2 → ρ y = 0)
    (hρ0 : ρ 0 = 1)
    (L : ℝ) (hL : 0 ≤ L) (hρlip : ∀ y z : ι → ℝ, ‖ρ y - ρ z‖ ≤ L * ‖y - z‖)
    (T T' : (ι → ℝ) → (ι → ℝ))
    (hT : ContDiff ℝ (⊤ : ℕ∞) T) (hT' : ContDiff ℝ (⊤ : ℕ∞) T')
    (hTinv1 : ∀ x : ι → ℝ, T' (T x) = x) (hTinv2 : ∀ y : ι → ℝ, T (T' y) = y)
    (hTper : ∀ (i : ι) (x : ι → ℝ), T (x + Pi.single i 1) = T x + Pi.single i 1)
    (a : (ι → ℝ) → ℂ) (ha : ContDiff ℝ (⊤ : ℕ∞) a) (hap : Work.Diff.STE.Periodic1 a)
    (s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (ε : ℝ), 0 < ε → ε ≤ 1 → ∀ g : (ι → ℝ) → ℂ,
        ContDiff ℝ (⊤ : ℕ∞) g → Work.Diff.STE.Periodic1 g →
        Work.Diff.STE.CSq (s + 1) (Work.Diff.STE.fourierCoeff (fun x : ι → ℝ =>
            a x * Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T' g x
              - Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T' (fun y : ι → ℝ => a y * g y) x))
          ≤ C * Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff g) := by
  classical
  -- ## Injectivity and invertibility of the differentials of `T` and `T'`
  have hinjT : Function.Injective T := fun x y hxy => by rw [← hTinv1 x, hxy, hTinv1 y]
  have hinjT' : Function.Injective T' := fun x y hxy => by rw [← hTinv2 x, hxy, hTinv2 y]
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
    have hcomp : fderiv ℝ (fun x => T' (T x)) z = (fderiv ℝ T' (T z)).comp (fderiv ℝ T z) :=
      fderiv_comp z ((hT'.differentiable (by simp)).differentiableAt)
        ((hT.differentiable (by simp)).differentiableAt)
    have h1 : fderiv ℝ (fun x => T' (T x)) z = 1 := by
      rw [show (fun x : ι → ℝ => T' (T x)) = id from funext hTinv1]
      exact fderiv_id
    have h2 : (fderiv ℝ T' (T z)).comp (fderiv ℝ T z) = 1 := by rw [← hcomp]; exact h1
    exact hdet_of _ _ h2
  have hdetT' : ∀ z : ι → ℝ, (fderiv ℝ T' z).det ≠ 0 := by
    intro z
    have hcomp : fderiv ℝ (fun y => T (T' y)) z = (fderiv ℝ T (T' z)).comp (fderiv ℝ T' z) :=
      fderiv_comp z ((hT.differentiable (by simp)).differentiableAt)
        ((hT'.differentiable (by simp)).differentiableAt)
    have h1 : fderiv ℝ (fun y => T (T' y)) z = 1 := by
      rw [show (fun y : ι → ℝ => T (T' y)) = id from funext hTinv2]
      exact fderiv_id
    have h2 : (fderiv ℝ T (T' z)).comp (fderiv ℝ T' z) = 1 := by rw [← hcomp]; exact h1
    exact hdet_of _ _ h2
  -- ## Periodicity and smoothness of `a ∘ T`
  have hbper : Work.Diff.STE.Periodic1 (fun y : ι → ℝ => a (T y)) := by
    intro i x
    show a (T (x + Pi.single i 1)) = a (T x)
    rw [hTper i x]
    exact hap i (T x)
  have hbsm : ContDiff ℝ (⊤ : ℕ∞) (fun y : ι → ℝ => a (T y)) := ha.comp hT
  -- ## The three constants
  obtain ⟨K1, hK1nn, hK1⟩ :=
    Work.Diff.STE.B3.SymCalcStep1.flat_multiplier_commutator ρ hρb hdiam hρ0 L hL hρlip
      (Work.Diff.STE.fourierCoeff (fun y : ι → ℝ => a (T y)))
      (fun N => Work.Diff.STE.summable_wt_pow_norm_fourierCoeff_of_contDiff _ hbsm hbper N) s
  obtain ⟨K2, hK2nn, hK2⟩ :=
    Work.Diff.STE.B3.SymCalcStep1.fourierCoeff_comp_le s T hT hTper hinjT hdetT
  obtain ⟨K3, hK3nn, hK3⟩ :=
    Work.Diff.STE.B3.SymCalcStep1.fourierCoeff_comp_le (s + 1) T' hT'
      (Work.Diff.STE.B3.SymCalcStep1.shift_T' T T' hTper hTinv1 hTinv2) hinjT' hdetT'
  refine ⟨K3 * (K1 * K2), mul_nonneg hK3nn (mul_nonneg hK1nn hK2nn), ?_⟩
  intro ε hε hε1 g hg hgper
  -- ## Smoothness and periodicity of the pieces
  have husm : ContDiff ℝ (⊤ : ℕ∞) (fun y : ι → ℝ => g (T y)) := hg.comp hT
  have huper : Work.Diff.STE.Periodic1 (fun y : ι → ℝ => g (T y)) := by
    intro i x
    show g (T (x + Pi.single i 1)) = g (T x)
    rw [hTper i x]
    exact hgper i (T x)
  have hbusm : ContDiff ℝ (⊤ : ℕ∞) (fun z : ι → ℝ => a (T z) * g (T z)) := hbsm.mul husm
  have hbuper : Work.Diff.STE.Periodic1 (fun z : ι → ℝ => a (T z) * g (T z)) :=
    Work.Diff.STE.B3.SymCalcStep1.Periodic1_mul' hbper huper
  have hFusm : ContDiff ℝ (⊤ : ℕ∞)
      (Work.Diff.STE.B3.SymCalc.flatCut ρ ε (fun z : ι → ℝ => g (T z))) :=
    Work.Diff.STE.B3.SymCalcStep1.flatCut_contDiff ρ hρb ε husm huper
  have hFuper : Work.Diff.STE.Periodic1
      (Work.Diff.STE.B3.SymCalc.flatCut ρ ε (fun z : ι → ℝ => g (T z))) :=
    Work.Diff.STE.B3.SymCalcStep1.flatCut_periodic ρ ε _
  have hFbusm : ContDiff ℝ (⊤ : ℕ∞)
      (Work.Diff.STE.B3.SymCalc.flatCut ρ ε (fun z : ι → ℝ => a (T z) * g (T z))) :=
    Work.Diff.STE.B3.SymCalcStep1.flatCut_contDiff ρ hρb ε hbusm hbuper
  have hFbuper : Work.Diff.STE.Periodic1
      (Work.Diff.STE.B3.SymCalc.flatCut ρ ε (fun z : ι → ℝ => a (T z) * g (T z))) :=
    Work.Diff.STE.B3.SymCalcStep1.flatCut_periodic ρ ε _
  -- ## The commutator family `W = [M_{a∘T}, S_ε] (g ∘ T)`
  set W : (ι → ℝ) → ℂ := fun y : ι → ℝ =>
      a (T y) * Work.Diff.STE.B3.SymCalc.flatCut ρ ε (fun z : ι → ℝ => g (T z)) y
        - Work.Diff.STE.B3.SymCalc.flatCut ρ ε (fun z : ι → ℝ => a (T z) * g (T z)) y with hW
  have hWsm : ContDiff ℝ (⊤ : ℕ∞) W := by
    rw [hW]
    exact (hbsm.mul hFusm).sub hFbusm
  have hWper : Work.Diff.STE.Periodic1 W := by
    rw [hW]
    exact Work.Diff.STE.B3.SymCalcStep1.Periodic1_sub'
      (Work.Diff.STE.B3.SymCalcStep1.Periodic1_mul' hbper hFuper) hFbuper
  -- ## The pointwise conjugation identity
  have hId : (fun x : ι → ℝ => a x * Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T' g x
        - Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T' (fun y : ι → ℝ => a y * g y) x)
      = Work.Diff.STE.B3.SymCalc.compMap T' W := by
    rw [hW]
    funext x
    dsimp only [Work.Diff.STE.B3.SymCalc.conjCut, Work.Diff.STE.B3.SymCalc.compMap]
    rw [show Work.Diff.STE.B3.SymCalc.compMap T g = (fun z : ι → ℝ => g (T z)) from rfl,
      show Work.Diff.STE.B3.SymCalc.compMap T (fun y : ι → ℝ => a y * g y)
        = (fun z : ι → ℝ => a (T z) * g (T z)) from rfl,
      hTinv2 x]
  -- ## Summability of the relevant coefficient families
  have hFu_one : Summable (fun k : ι → ℤ =>
      ‖Work.Diff.STE.fourierCoeff (fun y : ι → ℝ => g (T y)) k‖) := by
    have h0 := Work.Diff.STE.summable_wt_pow_norm_fourierCoeff_of_contDiff
      (fun y : ι → ℝ => g (T y)) husm huper 0
    simpa using h0
  have hFutrunc_one : Summable (fun k : ι → ℤ =>
      ‖Work.Diff.STE.trunc ρ ε (Work.Diff.STE.fourierCoeff (fun y : ι → ℝ => g (T y))) k‖) :=
    Work.Diff.STE.B3.SymCalcStep1.summable_trunc_one ρ hρb ε hFu_one
  have hbIntegrable : MeasureTheory.Integrable (fun y : ι → ℝ => a (T y))
      (MeasureTheory.volume.restrict (Work.Diff.STE.unitCube (ι := ι))) :=
    Work.Diff.STE.integrableOn_unitCube_of_continuous_cplx hbsm.continuous
  -- ## The Fourier coefficients of `W`
  have hT1 : ∀ k : ι → ℤ,
      Work.Diff.STE.fourierCoeff (fun y : ι → ℝ =>
          a (T y) * Work.Diff.STE.B3.SymCalc.flatCut ρ ε (fun z : ι → ℝ => g (T z)) y) k
        = Work.Diff.STE.conv (Work.Diff.STE.fourierCoeff (fun y : ι → ℝ => a (T y)))
            (Work.Diff.STE.trunc ρ ε (Work.Diff.STE.fourierCoeff (fun y : ι → ℝ => g (T y)))) k := by
    intro k
    have h := Work.Diff.STE.fourierCoeff_mul_seriesFun (fun y : ι → ℝ => a (T y))
      (Work.Diff.STE.trunc ρ ε (Work.Diff.STE.fourierCoeff (fun y : ι → ℝ => g (T y)))) k
      hbIntegrable hFutrunc_one
    simp only [Work.Diff.STE.B3.SymCalc.flatCut] at h ⊢
    rw [h, Work.Diff.STE.B3.SymCalcStep1.conv_comm]
  have hT2 : ∀ k : ι → ℤ,
      Work.Diff.STE.fourierCoeff (Work.Diff.STE.B3.SymCalc.flatCut ρ ε
          (fun z : ι → ℝ => a (T z) * g (T z))) k
        = Work.Diff.STE.trunc ρ ε
            (Work.Diff.STE.fourierCoeff (fun z : ι → ℝ => a (T z) * g (T z))) k :=
    fun k => Work.Diff.STE.B3.SymCalcStep1.fourierCoeff_flatCut ρ hρb ε hbusm hbuper k
  have hT3 : ∀ k : ι → ℤ,
      Work.Diff.STE.fourierCoeff (fun z : ι → ℝ => a (T z) * g (T z)) k
        = Work.Diff.STE.conv (Work.Diff.STE.fourierCoeff (fun y : ι → ℝ => a (T y)))
            (Work.Diff.STE.fourierCoeff (fun y : ι → ℝ => g (T y))) k := by
    intro k
    have h := Work.Diff.STE.fourierCoeff_mul_seriesFun (fun y : ι → ℝ => a (T y))
      (Work.Diff.STE.fourierCoeff (fun y : ι → ℝ => g (T y))) k hbIntegrable hFu_one
    have hseries : (fun x : ι → ℝ => a (T x)
        * Work.Diff.STE.seriesFun
            (Work.Diff.STE.fourierCoeff (fun y : ι → ℝ => g (T y))) x)
        = (fun z : ι → ℝ => a (T z) * g (T z)) := by
      funext x
      rw [Work.Diff.STE.flat.seriesFun_fourierCoeff (fun y : ι → ℝ => g (T y)) husm huper x]
    rw [hseries] at h
    rw [h, Work.Diff.STE.B3.SymCalcStep1.conv_comm]
  have htrunc_conv : Work.Diff.STE.trunc ρ ε
        (Work.Diff.STE.fourierCoeff (fun z : ι → ℝ => a (T z) * g (T z)))
      = Work.Diff.STE.trunc ρ ε (Work.Diff.STE.conv
          (Work.Diff.STE.fourierCoeff (fun y : ι → ℝ => a (T y)))
          (Work.Diff.STE.fourierCoeff (fun y : ι → ℝ => g (T y)))) :=
    congrArg (Work.Diff.STE.trunc ρ ε) (funext hT3)
  have hT2' : ∀ k : ι → ℤ,
      Work.Diff.STE.fourierCoeff (Work.Diff.STE.B3.SymCalc.flatCut ρ ε
          (fun z : ι → ℝ => a (T z) * g (T z))) k
        = Work.Diff.STE.trunc ρ ε (Work.Diff.STE.conv
            (Work.Diff.STE.fourierCoeff (fun y : ι → ℝ => a (T y)))
            (Work.Diff.STE.fourierCoeff (fun y : ι → ℝ => g (T y)))) k := by
    intro k
    rw [hT2 k, htrunc_conv]
  have hcoefW : Work.Diff.STE.fourierCoeff W
      = fun k : ι → ℤ => Work.Diff.STE.conv (Work.Diff.STE.fourierCoeff (fun y : ι → ℝ => a (T y)))
            (Work.Diff.STE.trunc ρ ε (Work.Diff.STE.fourierCoeff (fun y : ι → ℝ => g (T y)))) k
          - Work.Diff.STE.trunc ρ ε (Work.Diff.STE.conv
              (Work.Diff.STE.fourierCoeff (fun y : ι → ℝ => a (T y)))
              (Work.Diff.STE.fourierCoeff (fun y : ι → ℝ => g (T y)))) k := by
    funext k
    rw [hW]
    rw [Work.Diff.STE.flat.fourierCoeff_sub_of_continuous
      (fun y : ι → ℝ => a (T y) * Work.Diff.STE.B3.SymCalc.flatCut ρ ε (fun z : ι → ℝ => g (T z)) y)
      (Work.Diff.STE.B3.SymCalc.flatCut ρ ε (fun z : ι → ℝ => a (T z) * g (T z)))
      (hbsm.continuous.mul hFusm.continuous) hFbusm.continuous k]
    rw [hT1 k, hT2' k]
  -- ## The three estimates
  have hmid : Work.Diff.STE.CSq (s + 1) (Work.Diff.STE.fourierCoeff W)
      ≤ K1 * Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (fun y : ι → ℝ => g (T y))) := by
    rw [hcoefW]
    exact hK1 ε hε hε1 _
      (Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff
        (fun y : ι → ℝ => g (T y)) husm huper s)
  have htop : Work.Diff.STE.CSq (s + 1)
        (Work.Diff.STE.fourierCoeff (Work.Diff.STE.B3.SymCalc.compMap T' W))
      ≤ K3 * Work.Diff.STE.CSq (s + 1) (Work.Diff.STE.fourierCoeff W) := hK3 W hWsm hWper
  rw [hId]
  calc Work.Diff.STE.CSq (s + 1)
        (Work.Diff.STE.fourierCoeff (Work.Diff.STE.B3.SymCalc.compMap T' W))
      ≤ K3 * Work.Diff.STE.CSq (s + 1) (Work.Diff.STE.fourierCoeff W) := htop
    _ ≤ K3 * (K1 * Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (fun y : ι → ℝ => g (T y)))) :=
        mul_le_mul_of_nonneg_left hmid hK3nn
    _ ≤ K3 * (K1 * (K2 * Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff g))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hK1nn) hK3nn
        exact hK2 g hg hgper
    _ = (K3 * (K1 * K2)) * Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff g) := by ring

end Work.Diff.STE.B3.SymCalcStep6
