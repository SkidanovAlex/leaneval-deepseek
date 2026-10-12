import Mathlib.Order.CompletePartialOrder
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB1.SectorAux.sectorPiece_word_integrable
import Submission.Work.BoseFixB1B.pairRung.winModeContentLeWord
import Submission.Work.BoseFixB1B.pairRung.winModePGenLeSlotSumN
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S.win

noncomputable section

open MeasureTheory Filter
open scoped Topology Real BigOperators ENNReal

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! # `Work.BoseFixB1S.win.slotContentIntegrableC2`

The `p`-integrability of the `x`-integrated windowed amplitude of a single slot of FS's box
projection, at `C²` regularity of the window: the piece of
`Work.BoseFixB1S.win.chiSmallB_fsKinPGenIntegrable` that lives in
`Submission/Work/BoseFixB1S/winModeContentLeWordC2.lean` only in *private* form,
exported here so that the rest of the corpus can use it.

Everything below is the (verbatim, `sorry`-free) private material of that file, relocated into
this module so that it can be made public: §1 the windowed mean-free fibre, §2 its smoothness and
support, §3 the weighted Plancherel identity at `C¹`, §4 the per-`x` content bound, §5 the uniform
Dirichlet bound on the box, §6 Fubini and the slot integrability itself.

The route: `tBamp χ p (Q_{Ac,i}Ψ) i x` is the `p`-convention Fourier transform of the fibre
`z ↦ χ z (Ψ(x_{i←z}) − ⟨Ψ⟩_{Ac,i})`, which is `C¹` with compact support when `χ ∈ C²` and
`Ψ ∈ C^∞`; weighted Plancherel at `C¹` turns `∫_p fsKinCoeff c₀ ‖p‖ ‖kinFT g p‖²` into
`(2π)³ ∫_z Σ_k ‖∂_k g‖² ≤ (2π)³ Cdir`, with `Cdir` uniform on the box (the derivative bounds of
`χ`, `Ψ` on the compact box are bounded).  Fubini with the uniform section bound then gives the
`p`-integrability of the `x`-integral. -/

/-! ## 1. The windowed mean-free fibre of FS's box projection -/
/-- The windowed mean-free fibre `z ↦ χ z · (Ψ(x with xᵢ = z) − ⟨Ψ⟩_{Ac,i})`, whose
`p`-convention Fourier transform is the windowed amplitude `tBamp χ p (Q_{Ac,i}Ψ) i x`.

Kept `irreducible` so that its (large) body never enters unification: use `fibre_unfold` /
`fibre_apply` to unfold it. -/
@[irreducible] private def fibre (χ : E3 → ℝ) (volA : ℝ) (Ac : Set E3) {n : ℕ}
    (Ψ : Submission.BoseGases.X n → ℝ) (i : Fin n) (x : Submission.BoseGases.X n) : E3 → ℂ :=
  fun z => ((χ z * (Ψ (Function.update x i z) - Work.SmallBoxTBWord.boxP volA Ac i Ψ x) : ℝ) : ℂ)

private lemma fibre_unfold {n : ℕ} {volA : ℝ} {Ac : Set E3} {χ : E3 → ℝ}
    {Ψ : Submission.BoseGases.X n → ℝ} (i : Fin n) (x : Submission.BoseGases.X n) :
    fibre χ volA Ac Ψ i x
      = fun z => ((χ z * (Ψ (Function.update x i z) - Work.SmallBoxTBWord.boxP volA Ac i Ψ x)
          : ℝ) : ℂ) := by
  unfold fibre
  rfl

private lemma fibre_apply {n : ℕ} {volA : ℝ} {Ac : Set E3} {χ : E3 → ℝ}
    {Ψ : Submission.BoseGases.X n → ℝ} (i : Fin n) (x : Submission.BoseGases.X n) (z : E3) :
    fibre χ volA Ac Ψ i x z
      = ((χ z * (Ψ (Function.update x i z) - Work.SmallBoxTBWord.boxP volA Ac i Ψ x) : ℝ) : ℂ) := by
  unfold fibre
  rfl

/-- `boxP` does not depend on the slot-`i` coordinate of the state. -/
private lemma boxP_update_eq (volA : ℝ) (Ac : Set E3) {n : ℕ}
    {Ψ : Submission.BoseGases.X n → ℝ} (i : Fin n) (x : Submission.BoseGases.X n) (z : E3) :
    Work.SmallBoxTBWord.boxP volA Ac i Ψ (Function.update x i z)
      = Work.SmallBoxTBWord.boxP volA Ac i Ψ x := by
  rw [Work.SmallBoxTBWord.boxP, Work.SmallBoxTBWord.boxP]
  congr 1
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with w
  rw [Function.update_idem]

/-- `tBamp` of FS's box projection over `Ac` is the Fourier transform of the windowed
mean-free fibre. -/
private lemma tBamp_boxQInd_eq_kinFT_fibre {n : ℕ} {volA : ℝ} {Ac : Set E3} {χ : E3 → ℝ}
    (hχsupp : ∀ z, z ∉ Ac → χ z = 0) (i : Fin n) (Ψ : Submission.BoseGases.X n → ℝ)
    (p : E3) (x : Submission.BoseGases.X n) :
    Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA Ac i Ψ) i x
      = Submission.BoseGases.kinFT (fibre χ volA Ac Ψ i x) p := by
  rw [Work.BoseFixB1.SectorAux.tBamp_boxQInd_eq_kinFT_boxQ hχsupp i Ψ p x]
  refine congrArg (fun H : E3 → ℂ => Submission.BoseGases.kinFT H p) ?_
  rw [fibre_unfold]
  refine funext (fun z => ?_)
  rw [Work.SmallBoxTBWord.boxQ, boxP_update_eq volA Ac i x z]

/-! ## 2. Smoothness, support and vanishing of the fibre -/

private lemma fibre_contDiff_one {n : ℕ} {volA : ℝ} {Ac : Set E3} {χ : E3 → ℝ}
    (hχ2 : ContDiff ℝ 2 χ) {Ψ : Submission.BoseGases.X n → ℝ}
    (hΨc : ContDiff ℝ (⊤ : ℕ∞) Ψ) (i : Fin n) (x : Submission.BoseGases.X n) :
    ContDiff ℝ 1 (fibre χ volA Ac Ψ i x) := by
  rw [fibre_unfold]
  have hχ1 : ContDiff ℝ 1 χ := hχ2.of_le (by norm_num)
  have hslice : ContDiff ℝ 1 (fun z : E3 => Ψ (Function.update x i z)) :=
    (hΨc.comp (contDiff_update (⊤ : ℕ∞) x i)).of_le
      (WithTop.coe_le_coe.mpr (le_top : (1 : ℕ∞) ≤ ⊤))
  have hsub : ContDiff ℝ 1 (fun z : E3 => Ψ (Function.update x i z)
      - Work.SmallBoxTBWord.boxP volA Ac i Ψ x) := hslice.sub contDiff_const
  exact Complex.ofRealCLM.contDiff.comp (hχ1.mul hsub)

private lemma fibre_hasCompactSupport {n : ℕ} {volA : ℝ} {Ac : Set E3} {χ : E3 → ℝ}
    (hχs : HasCompactSupport χ) {Ψ : Submission.BoseGases.X n → ℝ} (i : Fin n)
    (x : Submission.BoseGases.X n) :
    HasCompactSupport (fibre χ volA Ac Ψ i x) := by
  rw [fibre_unfold]
  exact (hχs.mul_right (f' := fun z : E3 => Ψ (Function.update x i z)
    - Work.SmallBoxTBWord.boxP volA Ac i Ψ x)).comp_left
    (g := fun r : ℝ => (r : ℂ)) (by simp)

/-- The support of the fibre is contained in the support of the window. -/
private lemma tsupport_fibre_subset {n : ℕ} {volA : ℝ} {Ac : Set E3} {χ : E3 → ℝ}
    {Ψ : Submission.BoseGases.X n → ℝ} (i : Fin n) (x : Submission.BoseGases.X n) :
    tsupport (fibre χ volA Ac Ψ i x) ⊆ tsupport χ := by
  refine closure_mono ?_
  intro z hz
  simp only [Function.mem_support, ne_eq] at hz ⊢
  intro h0
  refine hz ?_
  rw [fibre_apply i x z, h0]
  simp

/-- A window vanishing off `Ac ⊆ acube a` has its (topological) support inside `acube a`. -/
private lemma tsupport_subset_acube {a : ℝ} {Ac : Set E3} {χ : E3 → ℝ} (ha : 0 < a)
    (hχsupp : ∀ z, z ∉ Ac → χ z = 0) (hAcsub : Ac ⊆ Submission.BoseGases.acube a) :
    tsupport χ ⊆ Submission.BoseGases.acube a :=
  closure_minimal (fun z hz => by
    by_contra h
    exact hz (hχsupp z (fun h' => h (hAcsub h'))))
    (Submission.BoseGases.acube_compact ha).isClosed

/-! ## 3. The weighted Plancherel identity at `C¹` -/

/-- **Weighted Plancherel at `C¹`.**  For a `C¹` compactly supported state `g : ℝ³ → ℂ` the
kinetic symbol `‖p‖²` may be traded for the position-space Dirichlet sum. -/
private theorem kinFT_energy_c1 {g : E3 → ℂ} (hg : ContDiff ℝ 1 g)
    (hcs : HasCompactSupport g) :
    MeasureTheory.Integrable (fun p : E3 => ‖p‖ ^ 2 * ‖Submission.BoseGases.kinFT g p‖ ^ 2)
      ∧ ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3, ‖p‖ ^ 2 * ‖Submission.BoseGases.kinFT g p‖ ^ 2
          = ∑ i : Fin 3, ∫ z : E3,
              ‖fderiv ℝ g z (Submission.BoseGases.kcStdBasis i)‖ ^ 2 := by
  have hInt : MeasureTheory.Integrable g := hg.continuous.integrable_of_hasCompactSupport hcs
  have hDiff : Differentiable ℝ g := hg.differentiable_one
  have hInt' : MeasureTheory.Integrable (fderiv ℝ g) :=
    (hg.continuous_fderiv (by simp)).integrable_of_hasCompactSupport (hcs.fderiv ℝ)
  have hcont_i : ∀ i : Fin 3, Continuous
      (fun z : E3 => fderiv ℝ g z (Submission.BoseGases.kcStdBasis i)) :=
    fun i => (hg.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcs_i : ∀ i : Fin 3, HasCompactSupport
      (fun z : E3 => fderiv ℝ g z (Submission.BoseGases.kcStdBasis i)) :=
    fun i => hcs.fderiv_apply ℝ _
  have hplan : ∀ i : Fin 3,
      MeasureTheory.Integrable (fun p : E3 => ‖Submission.BoseGases.kinFT
          (fun z => fderiv ℝ g z (Submission.BoseGases.kcStdBasis i)) p‖ ^ 2)
      ∧ ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3, ‖Submission.BoseGases.kinFT
          (fun z => fderiv ℝ g z (Submission.BoseGases.kcStdBasis i)) p‖ ^ 2
          = ∫ z : E3, ‖fderiv ℝ g z (Submission.BoseGases.kcStdBasis i)‖ ^ 2 := by
    intro i
    exact Work.BoseKinLoc.Kinetic.kinFT_sq_of_memLp
      ((hcont_i i).memLp_of_hasCompactSupport (hcs_i i) (p := 1))
      ((hcont_i i).memLp_of_hasCompactSupport (hcs_i i) (p := 2))
  have hpt : ∀ p : E3,
      ‖p‖ ^ 2 * ‖Submission.BoseGases.kinFT g p‖ ^ 2
        = ∑ i : Fin 3, ‖Submission.BoseGases.kinFT
            (fun z => fderiv ℝ g z (Submission.BoseGases.kcStdBasis i)) p‖ ^ 2 :=
    fun p => Work.BoseFixB1.SectorAux.normSq_kinFT_eq_sum_normSq_fderiv_one hg hcs p
  have hsumInt : MeasureTheory.Integrable (fun p : E3 => ∑ i : Fin 3,
      ‖Submission.BoseGases.kinFT
        (fun z => fderiv ℝ g z (Submission.BoseGases.kcStdBasis i)) p‖ ^ 2) :=
    integrable_finsetSum _ (fun i _ => (hplan i).1)
  have hint : MeasureTheory.Integrable
      (fun p : E3 => ‖p‖ ^ 2 * ‖Submission.BoseGases.kinFT g p‖ ^ 2) :=
    hsumInt.congr (Filter.Eventually.of_forall (fun p => (hpt p).symm))
  refine ⟨hint, ?_⟩
  rw [show (∫ p : E3, ‖p‖ ^ 2 * ‖Submission.BoseGases.kinFT g p‖ ^ 2)
      = ∫ p : E3, ∑ i : Fin 3, ‖Submission.BoseGases.kinFT
          (fun z => fderiv ℝ g z (Submission.BoseGases.kcStdBasis i)) p‖ ^ 2 from
      integral_congr_ae (Filter.Eventually.of_forall hpt)]
  rw [integral_finsetSum _ (fun i _ => (hplan i).1)]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => (hplan i).2)

/-! ## 4. The per-`x` content bound for the fibre -/

/-- `fsKinCoeff c r ≤ r²` for `c ≥ 0`. -/
private lemma fsKinCoeff_le_sq (c r : ℝ) (hc : 0 ≤ c) :
    Submission.BoseGases.fsKinCoeff c r ≤ r ^ 2 := by
  rw [Submission.BoseGases.fsKinCoeff]
  have h1 : max (r - c) 0 ≤ |r| :=
    max_le (le_trans (sub_le_self r hc) (le_abs_self r)) (abs_nonneg r)
  calc (max (r - c) 0) ^ 2 ≤ |r| ^ 2 := pow_le_pow_left₀ (le_max_right _ _) h1 2
    _ = r ^ 2 := sq_abs r

private lemma continuous_fsKinCoeff (c : ℝ) :
    Continuous (fun p : E3 => Submission.BoseGases.fsKinCoeff c ‖p‖) := by
  rw [show (fun p : E3 => Submission.BoseGases.fsKinCoeff c ‖p‖)
      = (fun r : ℝ => (max (r - c) 0) ^ 2) ∘ fun p : E3 => ‖p‖ from rfl]
  exact (((continuous_id.sub continuous_const).max continuous_const).pow 2).comp continuous_norm

/-- **The `fsKinCoeff`-weighted squared Fourier amplitude of a compactly supported `C¹` state is
integrable, and bounded by `(2π)³` times the Dirichlet energy of the state.** -/
private lemma kinFT_content_bound {g : E3 → ℂ} (hcd : ContDiff ℝ 1 g)
    (hcs : HasCompactSupport g) {c₀ : ℝ} (hc₀ : 0 < c₀) {Cdir : ℝ}
    (hdir : (∫ z : E3, ∑ k : Fin 3,
        ‖fderiv ℝ g z (Submission.BoseGases.kcStdBasis k)‖ ^ 2) ≤ Cdir) :
    MeasureTheory.Integrable (fun p : E3 => Submission.BoseGases.fsKinCoeff c₀ ‖p‖ *
        ‖Submission.BoseGases.kinFT g p‖ ^ 2)
      ∧ (∫ p : E3, Submission.BoseGases.fsKinCoeff c₀ ‖p‖ *
            ‖Submission.BoseGases.kinFT g p‖ ^ 2) ≤ (2 * Real.pi) ^ 3 * Cdir := by
  obtain ⟨hint_w, heq_w⟩ := kinFT_energy_c1 hcd hcs
  have hcs_i : ∀ k : Fin 3, HasCompactSupport (fun z : E3 => fderiv ℝ g z
      (Submission.BoseGases.kcStdBasis k)) := fun k => hcs.fderiv_apply ℝ _
  have hcont_i : ∀ k : Fin 3, Continuous (fun z : E3 => fderiv ℝ g z
      (Submission.BoseGases.kcStdBasis k)) :=
    fun k => (hcd.continuous_fderiv (by simp)).clm_apply continuous_const
  have hint_on : ∀ k : Fin 3, MeasureTheory.Integrable (fun z : E3 =>
      ‖fderiv ℝ g z (Submission.BoseGases.kcStdBasis k)‖ ^ 2) := by
    intro k
    have h1 : Continuous (fun z : E3 =>
        ‖fderiv ℝ g z (Submission.BoseGases.kcStdBasis k)‖ ^ 2) := (hcont_i k).norm.pow 2
    have h2 : HasCompactSupport (fun z : E3 =>
        ‖fderiv ℝ g z (Submission.BoseGases.kcStdBasis k)‖ ^ 2) :=
      (hcs_i k).comp_left (g := fun r : ℂ => ‖r‖ ^ 2) (by simp)
    exact h1.integrable_of_hasCompactSupport h2
  have hsum_eq : (∑ k : Fin 3, ∫ z : E3,
        ‖fderiv ℝ g z (Submission.BoseGases.kcStdBasis k)‖ ^ 2)
      = ∫ z : E3, ∑ k : Fin 3,
        ‖fderiv ℝ g z (Submission.BoseGases.kcStdBasis k)‖ ^ 2 :=
    (integral_finsetSum _ (fun k _ => hint_on k)).symm
  have hbound : (∫ p : E3, ‖p‖ ^ 2 * ‖Submission.BoseGases.kinFT g p‖ ^ 2)
      ≤ (2 * Real.pi) ^ 3 * Cdir := by
    have hne : ((2 * Real.pi) ^ 3 : ℝ) ≠ 0 := by positivity
    have h2 : (∫ p : E3, ‖p‖ ^ 2 * ‖Submission.BoseGases.kinFT g p‖ ^ 2)
        = (2 * Real.pi) ^ 3 * (∫ z : E3, ∑ k : Fin 3,
            ‖fderiv ℝ g z (Submission.BoseGases.kcStdBasis k)‖ ^ 2) := by
      calc (∫ p : E3, ‖p‖ ^ 2 * ‖Submission.BoseGases.kinFT g p‖ ^ 2)
          = (2 * Real.pi) ^ 3 * (((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3, ‖p‖ ^ 2 *
              ‖Submission.BoseGases.kinFT g p‖ ^ 2) := by
            rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]
        _ = (2 * Real.pi) ^ 3 * (∑ k : Fin 3, ∫ z : E3,
              ‖fderiv ℝ g z (Submission.BoseGases.kcStdBasis k)‖ ^ 2) := by rw [heq_w]
        _ = (2 * Real.pi) ^ 3 * (∫ z : E3, ∑ k : Fin 3,
              ‖fderiv ℝ g z (Submission.BoseGases.kcStdBasis k)‖ ^ 2) := by rw [hsum_eq]
    rw [h2]
    exact mul_le_mul_of_nonneg_left hdir (by positivity)
  have hpt : ∀ p : E3, Submission.BoseGases.fsKinCoeff c₀ ‖p‖ *
        ‖Submission.BoseGases.kinFT g p‖ ^ 2 ≤ ‖p‖ ^ 2 * ‖Submission.BoseGases.kinFT g p‖ ^ 2 :=
    fun p => mul_le_mul_of_nonneg_right (fsKinCoeff_le_sq c₀ ‖p‖ hc₀.le) (sq_nonneg _)
  have hcont_kin : Continuous (fun p : E3 => ‖Submission.BoseGases.kinFT g p‖ ^ 2) :=
    (Work.BoseKinLoc.Momentum.continuous_kinFT_of_integrable
      (hcd.continuous.integrable_of_hasCompactSupport hcs)).norm.pow 2
  have hInt : MeasureTheory.Integrable (fun p : E3 => Submission.BoseGases.fsKinCoeff c₀ ‖p‖ *
      ‖Submission.BoseGases.kinFT g p‖ ^ 2) :=
    hint_w.mono' ((continuous_fsKinCoeff c₀).aestronglyMeasurable.mul hcont_kin.aestronglyMeasurable)
      (Filter.Eventually.of_forall (fun p => by
        rw [Real.norm_of_nonneg (mul_nonneg (Submission.BoseGases.fsKinCoeff_nonneg c₀ ‖p‖)
          (sq_nonneg _))]
        exact hpt p))
  refine ⟨hInt, ?_⟩
  calc (∫ p : E3, Submission.BoseGases.fsKinCoeff c₀ ‖p‖ * ‖Submission.BoseGases.kinFT g p‖ ^ 2)
      ≤ ∫ p : E3, ‖p‖ ^ 2 * ‖Submission.BoseGases.kinFT g p‖ ^ 2 :=
        integral_mono hInt hint_w hpt
    _ ≤ (2 * Real.pi) ^ 3 * Cdir := hbound

/-! ## 5. The Dirichlet bound for the fibre -/

/-- `‖kcStdBasis k‖ = 1`. -/
private lemma norm_kcStdBasis (k : Fin 3) :
    ‖Submission.BoseGases.kcStdBasis k‖ = 1 := by
  rw [show Submission.BoseGases.kcStdBasis k = EuclideanSpace.single k (1 : ℝ) from rfl,
    PiLp.norm_single]
  norm_num

/-- **The Dirichlet energy of the fibre is uniformly bounded on the box.** -/
private lemma fibre_dirichlet_bound {n : ℕ} {a volA : ℝ} (ha : 0 < a)
    {Ac : Set E3} (hAcsub : Ac ⊆ Submission.BoseGases.acube a)
    (hvol : volA = (volume Ac).toReal) (hvolpos : 0 < volA)
    {χ : E3 → ℝ} (hχ2 : ContDiff ℝ 2 χ) (hχsupp : ∀ z, z ∉ Ac → χ z = 0)
    (hχnn : ∀ z, 0 ≤ χ z)
    {Ψ : Submission.BoseGases.X n → ℝ} (hΨc : ContDiff ℝ (⊤ : ℕ∞) Ψ) (i : Fin n) :
    ∃ Cdir : ℝ, ∀ x ∈ Submission.BoseGases.abox n a,
      (∫ z : E3, ∑ k : Fin 3,
        ‖fderiv ℝ (fibre χ volA Ac Ψ i x) z (Submission.BoseGases.kcStdBasis k)‖ ^ 2) ≤ Cdir := by
  classical
  -- the window and its derivative are bounded
  obtain ⟨Cχ, hCχ⟩ := (Submission.BoseGases.acube_compact ha).exists_bound_of_continuousOn
    hχ2.continuous.continuousOn
  set M : ℝ := max Cχ 0 with hMdef
  have hM0 : 0 ≤ M := le_max_right _ _
  have hχle : ∀ z : E3, |χ z| ≤ M := by
    intro z
    by_cases hz : z ∈ Submission.BoseGases.acube a
    · have h1 : ‖χ z‖ ≤ Cχ := hCχ z hz
      rw [Real.norm_eq_abs] at h1
      exact le_trans h1 (le_max_left _ _)
    · rw [hχsupp z (fun h => hz (hAcsub h)), abs_zero]
      exact hM0
  obtain ⟨Cχ1, hCχ1⟩ := (Submission.BoseGases.acube_compact ha).exists_bound_of_continuousOn
    ((hχ2.continuous_fderiv (by norm_num)).continuousOn)
  set M' : ℝ := max Cχ1 0 with hM'def
  have hM'0 : 0 ≤ M' := le_max_right _ _
  have hdχle : ∀ z ∈ Submission.BoseGases.acube a, ‖fderiv ℝ χ z‖ ≤ M' :=
    fun z hz => le_trans (hCχ1 z hz) (le_max_left _ _)
  -- the state and its derivative are bounded on the box
  obtain ⟨B0, hB00, hB0⟩ :=
    Work.BoseFixB1.exists_bound_abox_pos (N := n) (ℓ := a) ha hΨc.continuous
  set B : ℝ := max B0 0 with hBdef
  have hBnn : 0 ≤ B := le_max_right _ _
  have hBs : ∀ x ∈ Submission.BoseGases.abox n a, |Ψ x| ≤ B :=
    fun x hx => le_trans (hB0 x hx) (le_max_left _ _)
  obtain ⟨N0, hN0⟩ := (Submission.BoseGases.abox_compact n ha).exists_bound_of_continuousOn
    ((hΨc.continuous_fderiv (by simp)).continuousOn)
  set N : ℝ := max N0 0 with hNdef
  have hNnn : 0 ≤ N := le_max_right _ _
  have hNs : ∀ x ∈ Submission.BoseGases.abox n a, ‖fderiv ℝ Ψ x‖ ≤ N :=
    fun x hx => le_trans (hN0 x hx) (le_max_left _ _)
  -- inserting a point of the box keeps the configuration in the box
  have hmem_upd : ∀ x ∈ Submission.BoseGases.abox n a, ∀ z ∈ Submission.BoseGases.acube a,
      Function.update x i z ∈ Submission.BoseGases.abox n a := by
    intro x hx z hz j
    by_cases hj : j = i
    · subst hj; rw [Function.update_self]; exact hz
    · rw [Function.update_of_ne hj]; exact hx j
  -- the box mean is bounded by `B`
  have hmeanB : ∀ x ∈ Submission.BoseGases.abox n a,
      |Work.SmallBoxTBWord.boxP volA Ac i Ψ x| ≤ B := by
    intro x hx
    have hInt : |∫ z in Ac, Ψ (Function.update x i z)| ≤ B * volA := by
      have h3 : ‖∫ z in Ac, Ψ (Function.update x i z)‖ ≤ B * (volume Ac).toReal :=
        MeasureTheory.norm_setIntegral_le_of_norm_le_const
          (f := fun z : E3 => Ψ (Function.update x i z)) (C := B)
          (lt_of_le_of_lt (MeasureTheory.measure_mono hAcsub)
            (Submission.BoseGases.acube_lt_top a ha.le))
          (fun z hz => by
            simpa only [Real.norm_eq_abs] using hBs _ (hmem_upd x hx z (hAcsub hz)))
      rw [← hvol] at h3
      simpa only [Real.norm_eq_abs] using h3
    calc |Work.SmallBoxTBWord.boxP volA Ac i Ψ x|
        = (1 / volA) * |∫ z in Ac, Ψ (Function.update x i z)| := by
          rw [Work.SmallBoxTBWord.boxP, abs_mul,
            abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / volA)]
      _ ≤ (1 / volA) * (B * volA) := mul_le_mul_of_nonneg_left hInt (by positivity)
      _ = B := by field_simp
  -- the pointwise bound on the fibre derivative
  have hpoint : ∀ x ∈ Submission.BoseGases.abox n a, ∀ z ∈ Submission.BoseGases.acube a,
      ∑ k : Fin 3,
        ‖fderiv ℝ (fibre χ volA Ac Ψ i x) z (Submission.BoseGases.kcStdBasis k)‖ ^ 2
        ≤ 3 * (2 * B * M' + M * N) ^ 2 := by
    intro x hx z hz
    have hχd : Differentiable ℝ χ := (hχ2.of_le (by norm_num)).differentiable_one
    have hGcd : ContDiff ℝ (⊤ : ℕ∞) (fun y : Submission.BoseGases.X n =>
        Ψ y - Work.SmallBoxTBWord.boxP volA Ac i Ψ x) := hΨc.sub contDiff_const
    have hk : ∀ k : Fin 3,
        ‖fderiv ℝ (fibre χ volA Ac Ψ i x) z (Submission.BoseGases.kcStdBasis k)‖
          ≤ 2 * B * M' + M * N := by
      intro k
      have hder := Work.BoseFixB1.SectorAux.fderiv_fib_apply (χ := χ)
        (G := fun y : Submission.BoseGases.X n => Ψ y - Work.SmallBoxTBWord.boxP volA Ac i Ψ x)
        hχd hGcd i x z k
      rw [fibre_unfold]
      rw [hder, Complex.norm_real, Real.norm_eq_abs]
      have h1 : |fderiv ℝ χ z (Submission.BoseGases.kcStdBasis k)| ≤ M' := by
        have h := ContinuousLinearMap.le_opNorm (fderiv ℝ χ z)
          (Submission.BoseGases.kcStdBasis k)
        rw [norm_kcStdBasis k, mul_one] at h
        exact le_trans (by simpa using h) (hdχle z hz)
      have h2 : |(fun y : Submission.BoseGases.X n => Ψ y
          - Work.SmallBoxTBWord.boxP volA Ac i Ψ x) (Function.update x i z)| ≤ 2 * B := by
        have hx1 : |Ψ (Function.update x i z)| ≤ B := hBs _ (hmem_upd x hx z hz)
        have hx2 : |Work.SmallBoxTBWord.boxP volA Ac i Ψ x| ≤ B := hmeanB x hx
        have h1' := abs_le.mp hx1
        have h2' := abs_le.mp hx2
        rw [abs_sub_le_iff]
        exact ⟨by linarith [h1'.2, h2'.1], by linarith [h1'.1, h2'.2]⟩
      have h3 : |fderiv ℝ (fun y : Submission.BoseGases.X n => Ψ y
          - Work.SmallBoxTBWord.boxP volA Ac i Ψ x) (Function.update x i z)
            (Function.update 0 i (Submission.BoseGases.kcStdBasis k))| ≤ N := by
        rw [fderiv_sub_const]
        have h := ContinuousLinearMap.le_opNorm (fderiv ℝ Ψ (Function.update x i z))
          (Function.update 0 i (Submission.BoseGases.kcStdBasis k))
        rw [Work.BoseFixB2.Polar.norm_update_zero, norm_kcStdBasis k, mul_one] at h
        exact le_trans (by simpa using h) (hNs _ (hmem_upd x hx z hz))
      have hAG : |fderiv ℝ χ z (Submission.BoseGases.kcStdBasis k)
          * (fun y : Submission.BoseGases.X n => Ψ y
              - Work.SmallBoxTBWord.boxP volA Ac i Ψ x) (Function.update x i z)|
          ≤ M' * (2 * B) := by
        rw [abs_mul]
        exact mul_le_mul h1 h2 (abs_nonneg _) hM'0
      have hXY : |χ z * fderiv ℝ (fun y : Submission.BoseGases.X n => Ψ y
          - Work.SmallBoxTBWord.boxP volA Ac i Ψ x) (Function.update x i z)
            (Function.update 0 i (Submission.BoseGases.kcStdBasis k))| ≤ M * N := by
        rw [abs_mul, abs_of_nonneg (hχnn z)]
        exact mul_le_mul (le_trans (le_abs_self (χ z)) (hχle z)) h3 (abs_nonneg _) hM0
      have hmain2 : |fderiv ℝ χ z (Submission.BoseGases.kcStdBasis k)
              * (fun y : Submission.BoseGases.X n => Ψ y
                  - Work.SmallBoxTBWord.boxP volA Ac i Ψ x) (Function.update x i z)
            + χ z * fderiv ℝ (fun y : Submission.BoseGases.X n => Ψ y
                  - Work.SmallBoxTBWord.boxP volA Ac i Ψ x) (Function.update x i z)
                (Function.update 0 i (Submission.BoseGases.kcStdBasis k))|
          ≤ M' * (2 * B) + M * N := by
        refine abs_le.mpr ⟨?_, ?_⟩
        · have a1 := abs_le.mp hAG
          have a2 := abs_le.mp hXY
          linarith [a1.1, a2.1]
        · have a1 := abs_le.mp hAG
          have a2 := abs_le.mp hXY
          linarith [a1.2, a2.2]
      linarith [hmain2, show M' * (2 * B) + M * N = 2 * B * M' + M * N from by ring]
    calc ∑ k : Fin 3,
          ‖fderiv ℝ (fibre χ volA Ac Ψ i x) z (Submission.BoseGases.kcStdBasis k)‖ ^ 2
        ≤ ∑ _k : Fin 3, (2 * B * M' + M * N) ^ 2 :=
          Finset.sum_le_sum (fun k _ => pow_le_pow_left₀ (norm_nonneg _) (hk k) 2)
      _ = 3 * (2 * B * M' + M * N) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
          simp
  refine ⟨3 * (2 * B * M' + M * N) ^ 2 * a ^ 3, fun x hx => ?_⟩
  have hzero : ∀ z ∉ Submission.BoseGases.acube a,
      (∑ k : Fin 3, ‖fderiv ℝ (fibre χ volA Ac Ψ i x) z
        (Submission.BoseGases.kcStdBasis k)‖ ^ 2) = 0 := by
    intro z hz
    have hz' : z ∉ tsupport (fibre χ volA Ac Ψ i x) := fun h =>
      hz (tsupport_subset_acube ha hχsupp hAcsub (tsupport_fibre_subset i x h))
    have h0 : fderiv ℝ (fibre χ volA Ac Ψ i x) z = 0 :=
      (HasFDerivAt.of_notMem_tsupport ℝ hz').fderiv
    simp [h0]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := Submission.BoseGases.acube a) hzero]
  haveI : IsFiniteMeasure ((volume : Measure E3).restrict (Submission.BoseGases.acube a)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact Submission.BoseGases.acube_lt_top a ha.le⟩
  calc (∫ z in Submission.BoseGases.acube a, ∑ k : Fin 3,
        ‖fderiv ℝ (fibre χ volA Ac Ψ i x) z (Submission.BoseGases.kcStdBasis k)‖ ^ 2)
      ≤ ∫ _z in Submission.BoseGases.acube a, (3 * (2 * B * M' + M * N) ^ 2) := by
        refine integral_mono_of_nonneg
          (Filter.Eventually.of_forall (fun z => Finset.sum_nonneg (fun k _ => sq_nonneg _)))
          (integrable_const _)
          ((ae_restrict_iff' (Submission.BoseGases.acube_compact ha).isClosed.measurableSet).mpr
            (Filter.Eventually.of_forall (fun z hz => hpoint x hx z hz)))
    _ = 3 * (2 * B * M' + M * N) ^ 2 * a ^ 3 := by
        rw [MeasureTheory.integral_const]
        have hreal : ((volume : Measure E3).restrict (Submission.BoseGases.acube a)).real Set.univ
            = a ^ 3 := by
          rw [MeasureTheory.Measure.real_def, Measure.restrict_apply_univ,
            Submission.BoseGases.acube_volume a ha.le]
          simp [ENNReal.toReal_ofReal (pow_nonneg ha.le 3)]
        rw [hreal, smul_eq_mul]
        ring

/-! ## 6. Integrability of the slot `p`-integrand -/

/-- **Fubini for a slice-family with a uniform section bound.**  If the `(p, x)`-integrand is
jointly a.e. strongly measurable, the `p`-sections are a.e. integrable and their `L¹`-norms are
a.e. bounded on a finite measure space, then the `p`-integral of the `x`-sections is integrable. -/
private theorem integrable_of_section_bound {β : Type*} [MeasurableSpace β] {ν : Measure β}
    [IsFiniteMeasure ν] {H : E3 → β → ℝ}
    (hmeas : AEStronglyMeasurable (fun q : E3 × β => H q.1 q.2)
      ((volume : Measure E3).prod ν))
    (hint : ∀ᵐ x ∂ν, MeasureTheory.Integrable (fun p : E3 => H p x) (volume : Measure E3))
    {C : ℝ} (hC : ∀ᵐ x ∂ν, (∫ p : E3, ‖H p x‖ ∂(volume : Measure E3)) ≤ C) :
    MeasureTheory.Integrable (fun p : E3 => ∫ x : β, H p x ∂ν) (volume : Measure E3) := by
  have hmeas' : AEStronglyMeasurable (fun q : β × E3 => ‖H q.2 q.1‖)
      (ν.prod (volume : Measure E3)) := hmeas.prod_swap.norm
  have hInt : MeasureTheory.Integrable
      (fun x : β => ∫ p : E3, ‖H p x‖ ∂(volume : Measure E3)) ν :=
    MeasureTheory.Integrable.of_bound (hmeas'.integral_prod_right') C (by
      filter_upwards [hC] with x hx
      rwa [Real.norm_of_nonneg (integral_nonneg (fun p => norm_nonneg _))])
  have hf : MeasureTheory.Integrable (fun q : E3 × β => H q.1 q.2)
      ((volume : Measure E3).prod ν) :=
    (integrable_prod_iff' (μ := (volume : Measure E3)) (ν := ν) hmeas).mpr ⟨hint, hInt⟩
  exact hf.integral_prod_left

/-- **The `p`-integrand of a single slot is integrable at `C²` regularity of the window.** -/
theorem slotContentIntegrableC2 {n : ℕ} {a volA : ℝ} (ha : 0 < a)
    {Ac : Set (EuclideanSpace ℝ (Fin 3))} (hAcm : MeasurableSet Ac)
    (hAcsub : Ac ⊆ Submission.BoseGases.acube a)
    (hvol : volA = (MeasureTheory.volume Ac).toReal) (hvolpos : 0 < volA)
    {χ : EuclideanSpace ℝ (Fin 3) → ℝ} (hχ2 : ContDiff ℝ 2 χ) (hχs : HasCompactSupport χ)
    (hχsupp : ∀ z, z ∉ Ac → χ z = 0) (hχnn : ∀ z, 0 ≤ χ z)
    {c₀ : ℝ} (hc₀ : 0 < c₀)
    {Ψ : Submission.BoseGases.X n → ℝ} (hΨc : ContDiff ℝ (⊤ : ℕ∞) Ψ) (i : Fin n) :
    MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) => Submission.BoseGases.fsKinCoeff c₀ ‖p‖ *
      ((a ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox n a,
        ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA Ac i Ψ) i x‖ ^ 2)) := by
  classical
  obtain ⟨Cdir, hdir⟩ :=
    fibre_dirichlet_bound ha hAcsub hvol hvolpos hχ2 hχsupp hχnn hΨc i
  have hper : ∀ x ∈ Submission.BoseGases.abox n a,
      MeasureTheory.Integrable (fun p : E3 => Submission.BoseGases.fsKinCoeff c₀ ‖p‖ *
        ‖Submission.BoseGases.kinFT (fibre χ volA Ac Ψ i x) p‖ ^ 2)
      ∧ (∫ p : E3, Submission.BoseGases.fsKinCoeff c₀ ‖p‖ *
            ‖Submission.BoseGases.kinFT (fibre χ volA Ac Ψ i x) p‖ ^ 2)
          ≤ (2 * Real.pi) ^ 3 * Cdir :=
    fun x hx => kinFT_content_bound (fibre_contDiff_one hχ2 hΨc i x)
      (fibre_hasCompactSupport hχs i x) hc₀ (hdir x hx)
  have htb : ∀ (p : E3) (x : Submission.BoseGases.X n),
      ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA Ac i Ψ) i x‖ ^ 2
        = ‖Submission.BoseGases.kinFT (fibre χ volA Ac Ψ i x) p‖ ^ 2 :=
    fun p x => by rw [tBamp_boxQInd_eq_kinFT_fibre hχsupp i Ψ p x]
  have hper' : ∀ x ∈ Submission.BoseGases.abox n a,
      MeasureTheory.Integrable (fun p : E3 => Submission.BoseGases.fsKinCoeff c₀ ‖p‖ *
        ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA Ac i Ψ) i x‖ ^ 2)
      ∧ (∫ p : E3, Submission.BoseGases.fsKinCoeff c₀ ‖p‖ *
            ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA Ac i Ψ) i x‖ ^ 2)
          ≤ (2 * Real.pi) ^ 3 * Cdir := by
    intro x hx
    obtain ⟨h1, h2⟩ := hper x hx
    have heq : (fun p : E3 => Submission.BoseGases.fsKinCoeff c₀ ‖p‖ *
          ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA Ac i Ψ) i x‖ ^ 2)
        = fun p : E3 => Submission.BoseGases.fsKinCoeff c₀ ‖p‖ *
          ‖Submission.BoseGases.kinFT (fibre χ volA Ac Ψ i x) p‖ ^ 2 := by
      funext p
      simp only [htb p x]
    exact ⟨heq ▸ h1, by rw [heq]; exact h2⟩
  -- the restricted box measure
  set ν : Measure (Submission.BoseGases.X n) :=
    (volume : Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n a) with hν
  haveI hνfin : IsFiniteMeasure ν :=
    ⟨by rw [hν, Measure.restrict_apply_univ]; exact Submission.BoseGases.abox_lt_top n a ha.le⟩
  -- joint measurability
  have hΦm : Measurable (Work.UBBInputs8.boxQInd volA Ac i Ψ) :=
    Work.SlotWord.measurable_boxQInd volA Ac hAcm i hΨc.continuous.measurable
  have hpairm : Measurable (fun q : E3 × Submission.BoseGases.X n =>
      ‖Work.SmallBoxTBWord.tBamp χ q.1 (Work.UBBInputs8.boxQInd volA Ac i Ψ) i q.2‖ ^ 2) :=
    Work.BoseFixB1.SectorAux.measurable_tBamp_pair_gen hχ2.continuous hΦm i
  have hHmeas : AEStronglyMeasurable (fun q : E3 × Submission.BoseGases.X n =>
      Submission.BoseGases.fsKinCoeff c₀ ‖q.1‖ *
        ‖Work.SmallBoxTBWord.tBamp χ q.1 (Work.UBBInputs8.boxQInd volA Ac i Ψ) i q.2‖ ^ 2)
      ((volume : Measure E3).prod ν) :=
    (((continuous_fsKinCoeff c₀).measurable.comp measurable_fst).mul hpairm).aestronglyMeasurable
  have hHint : ∀ᵐ x ∂ν, MeasureTheory.Integrable (fun p : E3 =>
      Submission.BoseGases.fsKinCoeff c₀ ‖p‖ *
        ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA Ac i Ψ) i x‖ ^ 2)
      (volume : Measure E3) := by
    rw [hν, ae_restrict_iff' (Submission.BoseGases.abox_measurable n a)]
    exact Filter.Eventually.of_forall (fun x hx => (hper' x hx).1)
  have hHC : ∀ᵐ x ∂ν, (∫ p : E3, ‖Submission.BoseGases.fsKinCoeff c₀ ‖p‖ *
        ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA Ac i Ψ) i x‖ ^ 2‖
        ∂(volume : Measure E3)) ≤ (2 * Real.pi) ^ 3 * Cdir := by
    rw [hν, ae_restrict_iff' (Submission.BoseGases.abox_measurable n a)]
    refine Filter.Eventually.of_forall (fun x hx => ?_)
    rw [integral_congr_ae (Filter.Eventually.of_forall (fun p => by
      rw [Real.norm_of_nonneg (mul_nonneg (Submission.BoseGases.fsKinCoeff_nonneg c₀ ‖p‖)
        (sq_nonneg _))]))]
    exact (hper' x hx).2
  have hmain : MeasureTheory.Integrable (fun p : E3 => ∫ x : Submission.BoseGases.X n,
      Submission.BoseGases.fsKinCoeff c₀ ‖p‖ *
        ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA Ac i Ψ) i x‖ ^ 2 ∂ν)
      (volume : Measure E3) :=
    integrable_of_section_bound (ν := ν) hHmeas hHint hHC
  refine (hmain.const_mul ((a ^ 3)⁻¹)).congr (Filter.Eventually.of_forall (fun p => ?_))
  show (a ^ 3)⁻¹ * (∫ x : Submission.BoseGases.X n,
      Submission.BoseGases.fsKinCoeff c₀ ‖p‖ *
        ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA Ac i Ψ) i x‖ ^ 2 ∂ν)
    = Submission.BoseGases.fsKinCoeff c₀ ‖p‖ *
        ((a ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox n a,
          ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA Ac i Ψ) i x‖ ^ 2)
  rw [MeasureTheory.integral_const_mul]
  ring

end

end Work.BoseFixB1S.win
