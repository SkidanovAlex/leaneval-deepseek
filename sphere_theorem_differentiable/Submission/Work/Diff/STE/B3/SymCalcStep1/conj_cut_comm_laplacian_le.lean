import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.B3.SymCalc
import Submission.Work.Diff.STE.B3.SymCalcStep1.conj_cut_aux
import Submission.Work.Diff.STE.B3.SymCalcStep1.fourierCoeff_comp_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

namespace Work.Diff.STE.B3.SymCalcStep1

open MeasureTheory BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


/-- Linearity of `fourierCoeff` over a sum of two continuous functions. -/
lemma fourierCoeff_add_of_continuous (f g : (ι → ℝ) → ℂ) (hf : Continuous f) (hg : Continuous g)
    (k : ι → ℤ) :
    Work.Diff.STE.fourierCoeff (f + g) k
      = Work.Diff.STE.fourierCoeff f k + Work.Diff.STE.fourierCoeff g k := by
  have h1 : Integrable (fun x : ι → ℝ => Work.Diff.STE.fourierExp (-k) x * f x)
      (volume.restrict (Work.Diff.STE.unitCube (ι := ι))) :=
    Work.Diff.STE.integrableOn_unitCube_of_continuous_cplx
      ((Work.Diff.STE.continuous_fourierExp (-k)).mul hf)
  have h2 : Integrable (fun x : ι → ℝ => Work.Diff.STE.fourierExp (-k) x * g x)
      (volume.restrict (Work.Diff.STE.unitCube (ι := ι))) :=
    Work.Diff.STE.integrableOn_unitCube_of_continuous_cplx
      ((Work.Diff.STE.continuous_fourierExp (-k)).mul hg)
  simp only [Work.Diff.STE.fourierCoeff, Pi.add_apply]
  rw [← MeasureTheory.integral_add h1 h2]
  exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)

/-- **`[pullLap, S_ε]` is of order `1`.**  `pullLap T T' = comp_T ∘ lapC ∘ comp_{T'}` is a second
order operator whose top order part is a scalar symbol transported along `T`, so its commutator
with the Friedrichs cutoff loses exactly one derivative, uniformly in `ε ∈ (0,1]`. -/
lemma pullLap_comm_bound_self (ρ : (ι → ℝ) → ℝ)
    (hρb : ∀ y : ι → ℝ, ‖ρ y‖ ≤ 1)
    (hdiam : ∀ y : ι → ℝ, 2 < ∑ i, (y i) ^ 2 → ρ y = 0)
    (L : ℝ) (hL : 0 ≤ L) (hρlip : ∀ y z : ι → ℝ, ‖ρ y - ρ z‖ ≤ L * ‖y - z‖)
    (T T' : (ι → ℝ) → (ι → ℝ))
    (hTper : ∀ (i : ι) (x : ι → ℝ), T (x + Pi.single i 1) = T x + Pi.single i 1)
    (hTinv1 : ∀ x : ι → ℝ, T' (T x) = x)
    (hTinv2 : ∀ y : ι → ℝ, T (T' y) = y)
    (hT : ContDiff ℝ (⊤ : ℕ∞) T) (hT' : ContDiff ℝ (⊤ : ℕ∞) T')
    (s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ε : ℝ), 0 < ε → ε ≤ 1 → ∀ h : (ι → ℝ) → ℂ,
      ContDiff ℝ (⊤ : ℕ∞) h → Work.Diff.STE.Periodic1 h →
      Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff
          (pullLap T T' (Work.Diff.STE.B3.SymCalc.flatCut ρ ε h)
            - Work.Diff.STE.B3.SymCalc.flatCut ρ ε (pullLap T T' h)))
        ≤ C * Work.Diff.STE.CSq (s + 1) (Work.Diff.STE.fourierCoeff h) := by
  classical
  choose CQ hCQ using fun i : ι => Qop_CSq_le T T' hTper hTinv1 hTinv2 hT hT' i s
  choose CC hCC using fun i : ι => Qop_comm_le ρ hρb hdiam L hL hρlip T T' hTper hTinv1 hTinv2 hT hT' i s
  choose CC1 hCC1 using fun i : ι =>
    Qop_comm_le ρ hρb hdiam L hL hρlip T T' hTper hTinv1 hTinv2 hT hT' i (s + 1)
  refine ⟨(Fintype.card ι : ℝ) * ∑ i, (2 * (CQ i * CC1 i + CC i * CQ i)), ?_, ?_⟩
  · refine mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun i _ => ?_)
    have h1 := (hCQ i).1
    have h2 := (hCC i).1
    have h3 := (hCC1 i).1
    exact mul_nonneg (by norm_num) (add_nonneg (mul_nonneg h1 h3) (mul_nonneg h2 h1))
  intro ε hε hε1 h hhsm hhper
  set Sh : (ι → ℝ) → ℂ := Work.Diff.STE.B3.SymCalc.flatCut ρ ε h with hShdef
  have hSh : Sh = Work.Diff.STE.B3.SymCalc.flatCut ρ ε h := hShdef
  have hShsm : ContDiff ℝ (⊤ : ℕ∞) Sh := by
    rw [hSh]; exact flatCut_contDiff ρ hρb ε hhsm hhper
  have hShper : Work.Diff.STE.Periodic1 Sh := by rw [hSh]; exact flatCut_periodic ρ ε h
  set G : ι → (ι → ℝ) → ℂ := fun i => Qop T T' i (Qop T T' i Sh)
      - Work.Diff.STE.B3.SymCalc.flatCut ρ ε (Qop T T' i (Qop T T' i h)) with hGdef
  have hG_eq : ∀ i : ι, G i = Qop T T' i (Qop T T' i Sh)
      - Work.Diff.STE.B3.SymCalc.flatCut ρ ε (Qop T T' i (Qop T T' i h)) :=
    fun i => congrFun hGdef i
  have hhi : ∀ i : ι, ContDiff ℝ (⊤ : ℕ∞) (Qop T T' i h) := fun i =>
    Qop_contDiff T T' hT hT' i hhsm
  have hhip : ∀ i : ι, Work.Diff.STE.Periodic1 (Qop T T' i h) := fun i =>
    Qop_periodic T T' hTper hTinv1 hTinv2 hT' i hhsm hhper
  have hwi_eq : pullLap T T' Sh - Work.Diff.STE.B3.SymCalc.flatCut ρ ε (pullLap T T' h)
      = fun y => ∑ i, G i y := by
    have h1 : pullLap T T' Sh = fun y => ∑ i, Qop T T' i (Qop T T' i Sh) y :=
      pullLap_eq_sum_Qop T T' hTinv2 Sh
    have h2 : pullLap T T' h = fun y => ∑ i, Qop T T' i (Qop T T' i h) y :=
      pullLap_eq_sum_Qop T T' hTinv2 h
    have h3 : Work.Diff.STE.B3.SymCalc.flatCut ρ ε (pullLap T T' h)
        = fun y => ∑ i, Work.Diff.STE.B3.SymCalc.flatCut ρ ε (Qop T T' i (Qop T T' i h)) y := by
      rw [h2]
      exact flatCut_fintype_sum ρ hρb ε _
        (fun i => Qop_contDiff T T' hT hT' i (Qop_contDiff T T' hT hT' i hhsm))
        (fun i => Qop_periodic T T' hTper hTinv1 hTinv2 hT' i (Qop_contDiff T T' hT hT' i hhsm)
          (Qop_periodic T T' hTper hTinv1 hTinv2 hT' i hhsm hhper))
    rw [h1, h3]
    funext y
    simp only [Pi.sub_apply, Finset.sum_apply]
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [hG_eq i]; rfl
  have hGsm : ∀ i : ι, ContDiff ℝ (⊤ : ℕ∞) (G i) := fun i => by
    rw [hG_eq i]
    exact (Qop_contDiff T T' hT hT' i (Qop_contDiff T T' hT hT' i hShsm)).sub
      (flatCut_contDiff ρ hρb ε (Qop_contDiff T T' hT hT' i (hhi i))
        (Qop_periodic T T' hTper hTinv1 hTinv2 hT' i (hhi i) (hhip i)))
  have hGper : ∀ i : ι, Work.Diff.STE.Periodic1 (G i) := fun i => by
    rw [hG_eq i]
    exact Periodic1_sub'
      (Qop_periodic T T' hTper hTinv1 hTinv2 hT' i (Qop_contDiff T T' hT hT' i hShsm)
        (Qop_periodic T T' hTper hTinv1 hTinv2 hT' i hShsm hShper))
      (flatCut_periodic ρ ε _)
  -- the bound for each term `G i`
  have hGi : ∀ i : ι, Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (G i))
      ≤ 2 * (CQ i * CC1 i + CC i * CQ i)
          * Work.Diff.STE.CSq (s + 1) (Work.Diff.STE.fourierCoeff h) := by
    intro i
    set R : (ι → ℝ) → ℂ := Qop T T' i Sh
      - Work.Diff.STE.B3.SymCalc.flatCut ρ ε (Qop T T' i h) with hRdef
    have hR : R = Qop T T' i Sh
        - Work.Diff.STE.B3.SymCalc.flatCut ρ ε (Qop T T' i h) := hRdef
    have hRsm : ContDiff ℝ (⊤ : ℕ∞) R := by
      rw [hR]
      exact (Qop_contDiff T T' hT hT' i hShsm).sub
        (flatCut_contDiff ρ hρb ε (hhi i) (hhip i))
    have hRper : Work.Diff.STE.Periodic1 R := by
      rw [hR]
      exact Periodic1_sub'
        (Qop_periodic T T' hTper hTinv1 hTinv2 hT' i hShsm hShper)
        (flatCut_periodic ρ ε _)
    have hGdec : G i = Qop T T' i R
        + (Qop T T' i (Work.Diff.STE.B3.SymCalc.flatCut ρ ε (Qop T T' i h))
            - Work.Diff.STE.B3.SymCalc.flatCut ρ ε (Qop T T' i (Qop T T' i h))) := by
      rw [hG_eq i, hR]
      rw [Qop_sub T T' (hT'.differentiable (by simp)) i
        ((Qop_contDiff T T' hT hT' i hShsm).differentiable (by simp))
        ((flatCut_contDiff ρ hρb ε (hhi i) (hhip i)).differentiable (by simp))]
      abel
    have hCper : Work.Diff.STE.Periodic1 (Qop T T' i (Work.Diff.STE.B3.SymCalc.flatCut ρ ε (Qop T T' i h))
        - Work.Diff.STE.B3.SymCalc.flatCut ρ ε (Qop T T' i (Qop T T' i h))) :=
      Periodic1_sub'
        (Qop_periodic T T' hTper hTinv1 hTinv2 hT' i
          (flatCut_contDiff ρ hρb ε (hhi i) (hhip i)) (flatCut_periodic ρ ε _))
        (flatCut_periodic ρ ε _)
    have hCsm : ContDiff ℝ (⊤ : ℕ∞) (Qop T T' i (Work.Diff.STE.B3.SymCalc.flatCut ρ ε (Qop T T' i h))
        - Work.Diff.STE.B3.SymCalc.flatCut ρ ε (Qop T T' i (Qop T T' i h))) :=
      (Qop_contDiff T T' hT hT' i (flatCut_contDiff ρ hρb ε (hhi i) (hhip i))).sub
        (flatCut_contDiff ρ hρb ε (Qop_contDiff T T' hT hT' i (hhi i))
          (Qop_periodic T T' hTper hTinv1 hTinv2 hT' i (hhi i) (hhip i)))
    have hfc : Work.Diff.STE.fourierCoeff (Qop T T' i R
        + (Qop T T' i (Work.Diff.STE.B3.SymCalc.flatCut ρ ε (Qop T T' i h))
            - Work.Diff.STE.B3.SymCalc.flatCut ρ ε (Qop T T' i (Qop T T' i h))))
        = fun k => Work.Diff.STE.fourierCoeff (Qop T T' i R) k
            + Work.Diff.STE.fourierCoeff (Qop T T' i
                (Work.Diff.STE.B3.SymCalc.flatCut ρ ε (Qop T T' i h))
              - Work.Diff.STE.B3.SymCalc.flatCut ρ ε (Qop T T' i (Qop T T' i h))) k :=
      funext fun k => fourierCoeff_add_of_continuous _ _
        (Qop_contDiff T T' hT hT' i hRsm).continuous hCsm.continuous k
    rw [hGdec, hfc]
    calc Work.Diff.STE.CSq s (fun k => Work.Diff.STE.fourierCoeff (Qop T T' i R) k
            + Work.Diff.STE.fourierCoeff (Qop T T' i (Work.Diff.STE.B3.SymCalc.flatCut ρ ε (Qop T T' i h))
                - Work.Diff.STE.B3.SymCalc.flatCut ρ ε (Qop T T' i (Qop T T' i h))) k)
          ≤ 2 * (Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (Qop T T' i R))
              + Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (Qop T T' i
                  (Work.Diff.STE.B3.SymCalc.flatCut ρ ε (Qop T T' i h))
                - Work.Diff.STE.B3.SymCalc.flatCut ρ ε (Qop T T' i (Qop T T' i h))))) :=
            CSq_add_le s _ _
              (summable_CSq_fourierCoeff s (Qop_contDiff T T' hT hT' i hRsm)
                (Qop_periodic T T' hTper hTinv1 hTinv2 hT' i hRsm hRper))
              (summable_CSq_fourierCoeff s hCsm hCper)
        _ ≤ 2 * (CQ i * Work.Diff.STE.CSq (s + 1) (Work.Diff.STE.fourierCoeff R)
              + CC i * Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (Qop T T' i h))) := by
            refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (by norm_num)
            · exact (hCQ i).2 R hRsm hRper
            · exact (hCC i).2 ε hε hε1 (Qop T T' i h) (hhi i) (hhip i)
        _ ≤ 2 * (CQ i * (CC1 i * Work.Diff.STE.CSq (s + 1) (Work.Diff.STE.fourierCoeff h))
              + CC i * (CQ i * Work.Diff.STE.CSq (s + 1) (Work.Diff.STE.fourierCoeff h))) := by
            refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (by norm_num)
            · exact mul_le_mul_of_nonneg_left ((hCC1 i).2 ε hε hε1 h hhsm hhper) (hCQ i).1
            · exact mul_le_mul_of_nonneg_left ((hCQ i).2 h hhsm hhper) (hCC i).1
        _ = 2 * (CQ i * CC1 i + CC i * CQ i)
              * Work.Diff.STE.CSq (s + 1) (Work.Diff.STE.fourierCoeff h) := by ring
  -- assemble
  have hcoefG : Work.Diff.STE.fourierCoeff (fun y => ∑ i, G i y)
      = fun k => ∑ i, Work.Diff.STE.fourierCoeff (G i) k :=
    funext fun k => fourierCoeff_ftype_sum_of_continuous G (fun i => (hGsm i).continuous) k
  rw [hwi_eq, hcoefG]
  calc Work.Diff.STE.CSq s (fun k => ∑ i, Work.Diff.STE.fourierCoeff (G i) k)
      ≤ (Fintype.card ι : ℝ) * ∑ i, Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (G i)) :=
        CSq_fintype_sum_le s _ fun i => summable_CSq_fourierCoeff s (hGsm i) (hGper i)
    _ ≤ (Fintype.card ι : ℝ) * ∑ i, 2 * (CQ i * CC1 i + CC i * CQ i)
          * Work.Diff.STE.CSq (s + 1) (Work.Diff.STE.fourierCoeff h) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hGi i) (Nat.cast_nonneg _)
    _ = ((Fintype.card ι : ℝ) * ∑ i, (2 * (CQ i * CC1 i + CC i * CQ i)))
          * Work.Diff.STE.CSq (s + 1) (Work.Diff.STE.fourierCoeff h) := by
        simp only [Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by ring


theorem conj_cut_comm_laplacian_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : (ι → ℝ) → ℝ)
    (hρb : ∀ y : ι → ℝ, ‖ρ y‖ ≤ 1)
    (hdiam : ∀ y : ι → ℝ, 2 < ∑ i, (y i) ^ 2 → ρ y = 0)
    (hρ0 : ρ 0 = 1)
    (L : ℝ) (hL : 0 ≤ L) (hρlip : ∀ y z : ι → ℝ, ‖ρ y - ρ z‖ ≤ L * ‖y - z‖)
    (T T' : (ι → ℝ) → (ι → ℝ))
    (hTsm : ContDiff ℝ (⊤ : ℕ∞) T) (hTsm' : ContDiff ℝ (⊤ : ℕ∞) T')
    (hTinv1 : ∀ x : ι → ℝ, T' (T x) = x)
    (hTinv2 : ∀ y : ι → ℝ, T (T' y) = y)
    (hTper : ∀ (i : ι) (x : ι → ℝ), T (x + Pi.single i 1) = T x + Pi.single i 1)
    (s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (ε : ℝ), 0 < ε → ε ≤ 1 → ∀ g : (ι → ℝ) → ℂ,
        ContDiff ℝ (⊤ : ℕ∞) g → Work.Diff.STE.Periodic1 g →
        Summable (fun k : ι → ℤ =>
            (Work.Diff.STE.wt k) ^ (s + 1) * ‖Work.Diff.STE.fourierCoeff g k‖ ^ 2) →
        Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (fun x =>
            Work.Diff.STE.B3.SymCalc.lapC (Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T' g) x
              - Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T' (Work.Diff.STE.B3.SymCalc.lapC g) x))
          ≤ C * Work.Diff.STE.CSq (s + 1) (Work.Diff.STE.fourierCoeff g) := by
  classical
  -- ## Injectivity and invertibility of the differential of `T` and `T'`
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
      fderiv_comp z ((hTsm'.differentiable (by simp)).differentiableAt)
        ((hTsm.differentiable (by simp)).differentiableAt)
    have h1 : fderiv ℝ (fun x => T' (T x)) z = 1 := by
      rw [show (fun x : ι → ℝ => T' (T x)) = id from funext hTinv1]
      exact fderiv_id
    have h2 : (fderiv ℝ T' (T z)).comp (fderiv ℝ T z) = 1 := by rw [← hcomp]; exact h1
    exact hdet_of _ _ h2
  have hdetT' : ∀ z : ι → ℝ, (fderiv ℝ T' z).det ≠ 0 := by
    intro z
    have hcomp : fderiv ℝ (fun y => T (T' y)) z = (fderiv ℝ T (T' z)).comp (fderiv ℝ T' z) :=
      fderiv_comp z ((hTsm.differentiable (by simp)).differentiableAt)
        ((hTsm'.differentiable (by simp)).differentiableAt)
    have h1 : fderiv ℝ (fun y => T (T' y)) z = 1 := by
      rw [show (fun y : ι → ℝ => T (T' y)) = id from funext hTinv2]
      exact fderiv_id
    have h2 : (fderiv ℝ T (T' z)).comp (fderiv ℝ T' z) = 1 := by rw [← hcomp]; exact h1
    exact hdet_of _ _ h2
  -- ## The three constants
  obtain ⟨K1, hK1nn, hK1⟩ := pullLap_comm_bound_self (ι := ι) ρ hρb hdiam L hL hρlip T T'
    hTper hTinv1 hTinv2 hTsm hTsm' s
  obtain ⟨K2, hK2nn, hK2⟩ := fourierCoeff_comp_le (ι := ι) (s + 1) T hTsm hTper hinjT hdetT
  obtain ⟨K3, hK3nn, hK3⟩ := fourierCoeff_comp_le (ι := ι) s T' hTsm' (shift_T' T T' hTper hTinv1 hTinv2)
    hinjT' hdetT'
  refine ⟨K3 * (K1 * K2), mul_nonneg hK3nn (mul_nonneg hK1nn hK2nn),
    fun ε hε hε1 g hg hgper _ => ?_⟩
  -- ## Setup
  set h : (ι → ℝ) → ℂ := fun x => g (T x) with hh
  set w : (ι → ℝ) → ℂ := pullLap T T' (Work.Diff.STE.B3.SymCalc.flatCut ρ ε h)
    - Work.Diff.STE.B3.SymCalc.flatCut ρ ε (pullLap T T' h) with hw
  have hhsm : ContDiff ℝ (⊤ : ℕ∞) h := hg.comp hTsm
  have hhper : Work.Diff.STE.Periodic1 h := by
    intro i x
    show g (T (x + Pi.single i 1)) = g (T x)
    rw [hTper]
    exact hgper i (T x)
  have hpull_sm : ∀ {v : (ι → ℝ) → ℂ}, ContDiff ℝ (⊤ : ℕ∞) v →
      ContDiff ℝ (⊤ : ℕ∞) (pullLap T T' v) := by
    intro v hv
    rw [pullLap_eq_sum_Qop T T' hTinv2 v]
    exact ContDiff.sum fun i _ => Qop_contDiff T T' hTsm hTsm' i
      (Qop_contDiff T T' hTsm hTsm' i hv)
  have hpull_per : ∀ {v : (ι → ℝ) → ℂ}, ContDiff ℝ (⊤ : ℕ∞) v → Work.Diff.STE.Periodic1 v →
      Work.Diff.STE.Periodic1 (pullLap T T' v) := by
    intro v hv hp m y
    rw [pullLap_eq_sum_Qop T T' hTinv2 v]
    simp only [Finset.sum_apply]
    exact Finset.sum_congr rfl fun i _ => Qop_periodic T T' hTper hTinv1 hTinv2 hTsm' i
      (Qop_contDiff T T' hTsm hTsm' i hv)
      (Qop_periodic T T' hTper hTinv1 hTinv2 hTsm' i hv hp) m y
  have hwsm : ContDiff ℝ (⊤ : ℕ∞) w := by
    rw [hw]
    exact (hpull_sm (flatCut_contDiff ρ hρb ε hhsm hhper)).sub
      (flatCut_contDiff ρ hρb ε (hpull_sm hhsm) (hpull_per hhsm hhper))
  have hwper : Work.Diff.STE.Periodic1 w := by
    rw [hw]
    exact Periodic1_sub'
      (hpull_per (flatCut_contDiff ρ hρb ε hhsm hhper) (flatCut_periodic ρ ε h))
      (flatCut_periodic ρ ε _)
  -- ## The conjugation identity
  have hF : (fun x => Work.Diff.STE.B3.SymCalc.lapC (Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T' g) x
        - Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T' (Work.Diff.STE.B3.SymCalc.lapC g) x)
      = Work.Diff.STE.B3.SymCalc.compMap T' w := by
    have hA : Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T' g
        = Work.Diff.STE.B3.SymCalc.compMap T' (Work.Diff.STE.B3.SymCalc.flatCut ρ ε h) := by
      show Work.Diff.STE.B3.SymCalc.compMap T'
          (Work.Diff.STE.B3.SymCalc.flatCut ρ ε (Work.Diff.STE.B3.SymCalc.compMap T g)) = _
      rw [show Work.Diff.STE.B3.SymCalc.compMap T g = h from hh]
    have hB : Work.Diff.STE.B3.SymCalc.lapC (Work.Diff.STE.B3.SymCalc.compMap T'
          (Work.Diff.STE.B3.SymCalc.flatCut ρ ε h))
        = Work.Diff.STE.B3.SymCalc.compMap T'
            (pullLap T T' (Work.Diff.STE.B3.SymCalc.flatCut ρ ε h)) := by
      funext x
      show Work.Diff.STE.B3.SymCalc.lapC (fun z => (Work.Diff.STE.B3.SymCalc.flatCut ρ ε h) (T' z)) x
        = Work.Diff.STE.B3.SymCalc.lapC
            (fun z => (Work.Diff.STE.B3.SymCalc.flatCut ρ ε h) (T' z)) (T (T' x))
      rw [hTinv2]
    have hC2 : Work.Diff.STE.B3.SymCalc.compMap T (Work.Diff.STE.B3.SymCalc.lapC g)
        = pullLap T T' h := by
      funext y
      show Work.Diff.STE.B3.SymCalc.lapC g (T y)
        = Work.Diff.STE.B3.SymCalc.lapC (fun z => h (T' z)) (T y)
      have hgg : g = fun z => h (T' z) := by
        funext z
        show g z = h (T' z)
        simp only [hh, hTinv2]
      rw [hgg]
    have hD : Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T' (Work.Diff.STE.B3.SymCalc.lapC g)
        = Work.Diff.STE.B3.SymCalc.compMap T'
            (Work.Diff.STE.B3.SymCalc.flatCut ρ ε (pullLap T T' h)) := by
      show Work.Diff.STE.B3.SymCalc.compMap T' (Work.Diff.STE.B3.SymCalc.flatCut ρ ε
          (Work.Diff.STE.B3.SymCalc.compMap T (Work.Diff.STE.B3.SymCalc.lapC g))) = _
      rw [hC2]
    funext x
    rw [hA, hD, hB]
    rfl
  -- ## Assembly
  rw [hF]
  calc Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (Work.Diff.STE.B3.SymCalc.compMap T' w))
      ≤ K3 * Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff w) := hK3 w hwsm hwper
    _ ≤ K3 * (K1 * Work.Diff.STE.CSq (s + 1) (Work.Diff.STE.fourierCoeff h)) :=
        mul_le_mul_of_nonneg_left (hK1 ε hε hε1 h hhsm hhper) hK3nn
    _ ≤ K3 * (K1 * (K2 * Work.Diff.STE.CSq (s + 1) (Work.Diff.STE.fourierCoeff g))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hK1nn) hK3nn
        have h2 := hK2 g hg hgper
        rwa [← hh] at h2
    _ = (K3 * (K1 * K2)) * Work.Diff.STE.CSq (s + 1) (Work.Diff.STE.fourierCoeff g) := by
        ring


end Work.Diff.STE.B3.SymCalcStep1
