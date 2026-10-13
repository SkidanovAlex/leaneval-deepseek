import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo
import Submission.Work.FTS.EllipticEst.remov.SourceBound.sliceShiftedDecomposition
import Submission.Work.FTS.EllipticEst.remov.SourceBound.sliceTendstoZeroOfMoment
import Submission.Work.FTS.EllipticEst.remov.SourceBound.weakSliceBounds
import Submission.Work.FTS.EllipticEst.remov.SourceBound.SliceAlgebra
import Submission.Work.FTS.EllipticEst.remov.coerc.slice_limit_at_right_eq_zero
import Submission.Work.FTS.EllipticEst.remov.coerc.tendsTo_atEnds_of_integrableOn_sq_deriv
import Submission.Work.FTS.EllipticEst.remov.SourceBound.sliceAesmSq
import Submission.Work.FTS.EllipticEst.remov.wsAux
import Submission.Work.FTS.EllipticEst.H2W.Fstar_DzIter_le_Psi
import Submission.Work.FTS.EllipticEst.remov.Fstar_DzIter_one_F
import Submission.Work.FTS.EllipticEst.remov.SliceTopAux.contDiffOnLzero1
import Submission.Work.FTS.EllipticEst.TT.WeakDescent

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov.SourceBound

open MeasureTheory Set Filter
open scoped Real Topology

set_option autoImplicit false
set_option maxHeartbeats 800000

local notation "Iθ" => Work.Spaces.Iθ
local notation "sEta" => Work.FTS.EllipticEst.sEta
local notation "ψ" => Work.Elliptic.sinCos2

/-! ## The weak class descends in the level -/

theorem EllWeakPos_of_le_level {α : ℝ} {k l : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hkl : l ≤ k)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) :
    Work.FTS.EllipticEst.TT.EllWeakPos α l F Ψ := by
  obtain ⟨hsw1, hsw2, hsw3, hsw4⟩ := Work.FTS.EllipticEst.remov.smoothOpen_slices_weak h 0
  have hFso : Work.FTS.EllipticEst.SmoothOpen F := hsw1
  have hAso : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
    hsw3
  have hBso : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 Ψ) := hsw4
  exact ⟨h.eq, h.zero, h.pi_half, h.orthF, h.orthPsi, h.smooth,
    Work.FTS.EllipticEst.TT.HkMem_descend_open hkl
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall F).mp hFso) h.memF,
    Work.FTS.EllipticEst.TT.HkMem_descend_open hkl
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hAso) h.memA,
    Work.FTS.EllipticEst.TT.HkMem_descend_open hkl
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hBso) h.memB,
    Work.FTS.EllipticEst.TT.HkMem_descend_open hkl
      (Work.FTS.EllipticEst.TT.smoothOpen_diagHon
        ((Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hBso)) h.memZPth2⟩

/-! ## Elementary integrability helpers -/

/-- `sEta` is a.e. strongly measurable on `Iθ`. -/
theorem aesm_sEta_Iθ : AEStronglyMeasurable (fun θ => sEta θ) (volume.restrict Iθ) := by
  have h : AEStronglyMeasurable (fun θ => sEta θ)
      (volume.restrict (Set.Ioo 0 (Real.pi / 2))) :=
    continuousOn_sEta_Ioo.aestronglyMeasurable measurableSet_Ioo
  rwa [MeasureTheory.restrict_Ioo_eq_restrict_Icc] at h

/-- A bounded slice has an integrable `ψ`-moment. -/
theorem integrableOn_mul_sinCos2_of_abs_le {g : ℝ → ℝ} {M : ℝ}
    (hg : AEStronglyMeasurable g (volume.restrict Iθ))
    (hbd : ∀ θ ∈ Iθ, |g θ| ≤ M) :
    MeasureTheory.IntegrableOn (fun θ => g θ * ψ θ) Iθ := by
  have hcont : Continuous ψ := by
    unfold Work.Elliptic.sinCos2
    exact Real.continuous_sin.mul (Real.continuous_cos.pow 2)
  have hψ : MeasureTheory.IntegrableOn (fun θ => |ψ θ|) Iθ :=
    (hcont.abs.continuousOn).integrableOn_compact isCompact_Icc
  refine Integrable.mono' (hψ.const_mul M) (hg.mul hcont.aestronglyMeasurable) ?_
  filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with θ hθ
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right (hbd θ hθ) (abs_nonneg _)

/-- A bounded slice has an integrable constant multiple of `(c·g)² · sEta`. -/
theorem integrableOn_const_mul_sq_mul_sEta_of_abs_le {g : ℝ → ℝ} {c M : ℝ}
    (hg : AEStronglyMeasurable g (volume.restrict Iθ))
    (hbd : ∀ θ ∈ Iθ, |g θ| ≤ M) :
    MeasureTheory.IntegrableOn (fun θ => (c * g θ) ^ 2 * sEta θ) Iθ := by
  have hdom : MeasureTheory.IntegrableOn (fun θ => c ^ 2 * (M ^ 2 * sEta θ)) Iθ :=
    (ws_sEta_integrableOn.const_mul (M ^ 2)).const_mul (c ^ 2)
  refine Integrable.mono' hdom (((hg.const_mul c).pow 2).mul aesm_sEta_Iθ) ?_
  filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with θ hθ
  have h1 : |g θ| ≤ M := hbd θ hθ
  have h2 : (g θ) ^ 2 ≤ M ^ 2 := sq_le_sq' (abs_le.mp h1).1 (abs_le.mp h1).2
  have h3 : 0 ≤ sEta θ := ws_sEta_nonneg hθ
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) h3), mul_pow]
  have h4 : c ^ 2 * (g θ) ^ 2 ≤ c ^ 2 * M ^ 2 := mul_le_mul_of_nonneg_left h2 (sq_nonneg c)
  calc c ^ 2 * (g θ) ^ 2 * sEta θ ≤ c ^ 2 * M ^ 2 * sEta θ :=
        mul_le_mul_of_nonneg_right h4 h3
    _ = c ^ 2 * (M ^ 2 * sEta θ) := by ring

/-! ## The `∂_z`-slice of a weak datum -/

/-- **Smoothness of the `∂_z`-slice** on the open angular interval. -/
theorem dzSlice_contDiffOn {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) {z : ℝ} (hz : 0 < z) :
    ∀ n : ℕ, ContDiffOn ℝ n (fun θ => Work.Spaces.pz Ψ z θ) (Set.Ioo 0 (Real.pi / 2)) := by
  intro n
  have hΨso : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  exact contDiffOn_iff_forall_nat_le.mp
    (Work.FTS.EllipticEst.SmoothOpen.curry_θ
      (Work.FTS.EllipticEst.SmoothOpen.pz hΨso) hz) n le_top

/-- **`(∂_θθ ∂_zΨ)² · sEta` is integrable.**  The second `θ`-derivative of the slice
`θ ↦ ∂_zΨ(z,θ)` is `∂_z(∂_θθΨ)`, the `i = 1` `D_z`-slot of `Work.Spaces.pthIter 2 Ψ`. -/
theorem dzSlice_secondDeriv_integrableOn {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ}
    (hk : 2 ≤ k) (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun t => deriv (fun θ' => Work.Spaces.pz Ψ z θ') t) θ) ^ 2
        * sEta θ) Iθ := by
  have hΨso : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hBso : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 Ψ) :=
    smoothOpen_pthIter hΨso 2
  have h1 := Work.FTS.EllipticEst.remov.ws_slot_slice hBso h.memB 1 (by omega) hz
  have h2 : MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ) ^ 2 * sEta θ) Iθ := by
    refine (h1.const_mul ((z ^ 2)⁻¹)).congr ?_
    refine Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ hθ => ?_)
    show (z ^ 2)⁻¹ * ((Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ) z θ) ^ 2 * sEta θ)
      = (Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ) ^ 2 * sEta θ
    simp only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, Work.Spaces.Dz]
    field_simp
  refine h2.congr ?_
  refine Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ hθ => ?_)
  have hQ : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩
  have hcl : Work.Spaces.pthIter 2 (Work.Spaces.pz Ψ) z θ
      = Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ := pthIter2_pz_eqOn hΨso hQ
  show (Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ) ^ 2 * sEta θ
    = (deriv (fun t => deriv (fun θ' => Work.Spaces.pz Ψ z θ') t) θ) ^ 2 * sEta θ
  rw [← hcl]
  rfl

/-- **Boundedness of the `∂_z`-slice** (and of its `θ`-derivative) on the open interval. -/
theorem dzSlice_bdd {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ}
    (hk : 2 ≤ k) (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) {z : ℝ} (hz : 0 < z) :
    ∃ C : ℝ, 0 < C ∧ ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |deriv (fun θ' => Work.Spaces.pz Ψ z θ') θ| ≤ C ∧ |Work.Spaces.pz Ψ z θ| ≤ C :=
  exists_bdd_of_sq_mul_sEta (dzSlice_contDiffOn h hz 2) (fun _ _ => rfl)
    (dzSlice_secondDeriv_integrableOn hk h hz)

/-- **`(∂_θ∂_zΨ(z,·))²` is integrable**, from the boundedness of the `θ`-derivative of the
slice and the finiteness of the angular interval. -/
theorem dzSlice_deriv_sq_integrableOn {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ}
    (hk : 2 ≤ k) (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun θ' => Work.Spaces.pz Ψ z θ') θ) ^ 2) Iθ := by
  obtain ⟨C, hCpos, hCbd⟩ := dzSlice_bdd hk h hz
  refine Integrable.mono' (g := fun _ : ℝ => C ^ 2)
    (MeasureTheory.integrableOn_const ws_vol_Iθ_ne_top)
    ((measurable_deriv (fun θ' => Work.Spaces.pz Ψ z θ')).aestronglyMeasurable.pow 2) ?_
  filter_upwards [ws_ae_mem_Ioo] with θ hθ
  have h1 : |deriv (fun θ' => Work.Spaces.pz Ψ z θ') θ| ≤ C := (hCbd θ hθ).1
  have h2 : (deriv (fun θ' => Work.Spaces.pz Ψ z θ') θ) ^ 2 ≤ C ^ 2 :=
    sq_le_sq' (abs_le.mp h1).1 (abs_le.mp h1).2
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact h2

/-- **`(∂_zΨ(z,·))²` is integrable**: the slice is bounded on the closed angular interval
(`weakSliceBounds`) and the interval has finite measure. -/
theorem dzSlice_sq_integrableOn {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ}
    (hk : 2 ≤ k) (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.pz Ψ z θ) ^ 2) Iθ := by
  obtain ⟨M, hMnn, hMbd⟩ := weakSliceBounds hk h z hz
  have hΨso : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have haesm : AEStronglyMeasurable (fun θ => Work.Spaces.pz Ψ z θ) (volume.restrict Iθ) :=
    Work.FTS.EllipticEst.remov.ws_aesm_slice (Work.FTS.EllipticEst.SmoothOpen.pz hΨso) hz
  refine Integrable.mono' (g := fun _ : ℝ => M ^ 2)
    (MeasureTheory.integrableOn_const ws_vol_Iθ_ne_top) (haesm.pow 2) ?_
  filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with θ hθ
  have h1 : |Work.Spaces.pz Ψ z θ| ≤ M := (hMbd θ hθ).2.2.1
  have h2 : (Work.Spaces.pz Ψ z θ) ^ 2 ≤ M ^ 2 :=
    sq_le_sq' (abs_le.mp h1).1 (abs_le.mp h1).2
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact h2

/-- **`(∂_z F(z,·))² · sEta` is integrable** — the `i = 1` `D_z`-slot of `HkMem α k F`. -/
theorem dzSource_sq_integrableOn {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ}
    (hk : 2 ≤ k) (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.pz F z θ) ^ 2 * sEta θ) Iθ := by
  obtain ⟨hsw1, -, -, -⟩ := Work.FTS.EllipticEst.remov.smoothOpen_slices_weak h 0
  have hFso : Work.FTS.EllipticEst.SmoothOpen F := hsw1
  have h1 := Work.FTS.EllipticEst.remov.ws_slot_slice hFso h.memF 1 (by omega) hz
  refine (h1.const_mul ((z ^ 2)⁻¹)).congr ?_
  refine Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ hθ => ?_)
  show (z ^ 2)⁻¹ * ((Work.Spaces.DzIter 1 F z θ) ^ 2 * sEta θ)
    = (Work.Spaces.pz F z θ) ^ 2 * sEta θ
  simp only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, Work.Spaces.Dz]
  field_simp

/-- **`(z ∂_z²Ψ(z,·))² · sEta` is integrable** — the `i = 0` `D_z`-slot of
`HkMem α k (z²∂_z²Ψ)`. -/
theorem zSlice2_sq_integrableOn {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ}
    (hk : 2 ≤ k) (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn
      (fun θ => (z * Work.Spaces.pzIter 2 Ψ z θ) ^ 2 * sEta θ) Iθ := by
  have hΨso : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hAso : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
    Work.FTS.EllipticEst.H2W.smoothOpen_zsq hΨso
  have h1 := Work.FTS.EllipticEst.remov.ws_slot_slice hAso h.memA 0 (by omega) hz
  refine (h1.const_mul ((z ^ 2)⁻¹)).congr ?_
  refine Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ hθ => ?_)
  show (z ^ 2)⁻¹ * ((Work.Spaces.DzIter 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
      z θ) ^ 2 * sEta θ) = (z * Work.Spaces.pzIter 2 Ψ z θ) ^ 2 * sEta θ
  simp only [Work.Spaces.DzIter_zero]
  field_simp

/-- **`(∂_z(z²∂_z²Ψ)(z,·))² · sEta` is integrable** — the `i = 1` `D_z`-slot of
`HkMem α k (z²∂_z²Ψ)`. -/
theorem pzZsqSlice2_sq_integrableOn {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ}
    (hk : 2 ≤ k) (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.pz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) ^ 2
        * sEta θ) Iθ := by
  have hΨso : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hAso : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
    Work.FTS.EllipticEst.H2W.smoothOpen_zsq hΨso
  have h1 := Work.FTS.EllipticEst.remov.ws_slot_slice hAso h.memA 1 (by omega) hz
  refine (h1.const_mul ((z ^ 2)⁻¹)).congr ?_
  refine Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ hθ => ?_)
  show (z ^ 2)⁻¹
      * ((Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) ^ 2
        * sEta θ)
    = (Work.Spaces.pz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) ^ 2 * sEta θ
  simp only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, Work.Spaces.Dz]
  field_simp

/-! ## The weighted `L²`-bound on `Lzero1 V` -/

/-- **`(Lzero1 V)² · sEta` is integrable**, where `V = θ ↦ ∂_zΨ(z,θ)`.  By
`sliceShiftedDecomposition`,

  `Lzero1 V = α(5+α)·V + α²·∂_z(z²∂_z²Ψ) + ∂_zF + (α²+5α)·z∂_z²Ψ`

on the open interval, and each of the four summands is a constant multiple of one of the four
integrable quantities `V`, `∂_z(z²∂_z²Ψ)`, `∂_zF`, `z∂_z²Ψ`. -/
theorem dzSlice_Lzero1_sq_integrableOn {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ}
    (hk : 2 ≤ k) (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn
      (fun θ => (Work.FTS.EllipticEst.Lzero1 (fun t => Work.Spaces.pz Ψ z t) θ) ^ 2
        * sEta θ) Iθ := by
  have hps : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hAso : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
    Work.FTS.EllipticEst.H2W.smoothOpen_zsq hps
  obtain ⟨M, hMnn, hMbd⟩ := weakSliceBounds hk h z hz
  have hVbd : ∀ θ ∈ Iθ, |Work.Spaces.pz Ψ z θ| ≤ M := fun θ hθ => (hMbd θ hθ).2.2.1
  have hVaesm : AEStronglyMeasurable (fun θ => Work.Spaces.pz Ψ z θ) (volume.restrict Iθ) :=
    Work.FTS.EllipticEst.remov.ws_aesm_slice (Work.FTS.EllipticEst.SmoothOpen.pz hps) hz
  -- the four summands
  have ha : MeasureTheory.IntegrableOn
      (fun θ => (α * (5 + α) * Work.Spaces.pz Ψ z θ) ^ 2 * sEta θ) Iθ :=
    integrableOn_const_mul_sq_mul_sEta_of_abs_le (c := α * (5 + α)) hVaesm hVbd
  have hc : MeasureTheory.IntegrableOn
      (fun θ => (α ^ 2 * Work.Spaces.pz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
        z θ) ^ 2 * sEta θ) Iθ := by
    refine ((pzZsqSlice2_sq_integrableOn hk h hz).const_mul ((α ^ 2) ^ 2)).congr ?_
    refine Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ _ => ?_)
    ring
  have hb : MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.pz F z θ) ^ 2 * sEta θ) Iθ := dzSource_sq_integrableOn hk h hz
  have hd : MeasureTheory.IntegrableOn
      (fun θ => ((α ^ 2 + 5 * α) * (z * Work.Spaces.pzIter 2 Ψ z θ)) ^ 2 * sEta θ) Iθ := by
    refine ((zSlice2_sq_integrableOn hk h hz).const_mul ((α ^ 2 + 5 * α) ^ 2)).congr ?_
    refine Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ _ => ?_)
    ring
  -- the pointwise identity of `sliceShiftedDecomposition`
  have hpt : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.FTS.EllipticEst.Lzero1 (fun t => Work.Spaces.pz Ψ z t) θ
        = α * (5 + α) * Work.Spaces.pz Ψ z θ
          + α ^ 2 * Work.Spaces.pz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
          + (Work.Spaces.pz F z θ
            + (α ^ 2 + 5 * α) * (z * Work.Spaces.pzIter 2 Ψ z θ)) := by
    intro θ hθ
    have h1 := sliceShiftedDecomposition hk h z hz θ hθ
    linarith
  -- the dominating function: four times the sum of the four squares
  have hsum : MeasureTheory.IntegrableOn
      (fun θ => (α * (5 + α) * Work.Spaces.pz Ψ z θ
          + α ^ 2 * Work.Spaces.pz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
          + (Work.Spaces.pz F z θ
            + (α ^ 2 + 5 * α) * (z * Work.Spaces.pzIter 2 Ψ z θ))) ^ 2 * sEta θ) Iθ := by
    have hdom : MeasureTheory.IntegrableOn
        (fun θ => (4 * ((α * (5 + α) * Work.Spaces.pz Ψ z θ) ^ 2 * sEta θ)
          + 4 * ((α ^ 2 * Work.Spaces.pz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
              z θ) ^ 2 * sEta θ))
          + (4 * ((Work.Spaces.pz F z θ) ^ 2 * sEta θ)
            + 4 * (((α ^ 2 + 5 * α) * (z * Work.Spaces.pzIter 2 Ψ z θ)) ^ 2 * sEta θ))) Iθ :=
      ((ha.const_mul 4).add (hc.const_mul 4)).add ((hb.const_mul 4).add (hd.const_mul 4))
    have haesm2 : AEStronglyMeasurable
        (fun θ => (α * (5 + α) * Work.Spaces.pz Ψ z θ
          + α ^ 2 * Work.Spaces.pz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
          + (Work.Spaces.pz F z θ
            + (α ^ 2 + 5 * α) * (z * Work.Spaces.pzIter 2 Ψ z θ))) ^ 2 * sEta θ)
        (volume.restrict Iθ) := by
      have hFso : Work.FTS.EllipticEst.SmoothOpen F :=
        (Work.FTS.EllipticEst.remov.smoothOpen_slices_weak h 0).1
      have h1 : AEStronglyMeasurable (fun θ => α * (5 + α) * Work.Spaces.pz Ψ z θ)
          (volume.restrict Iθ) := hVaesm.const_mul _
      have h2 : AEStronglyMeasurable (fun θ => Work.Spaces.pz F z θ)
          (volume.restrict Iθ) :=
        Work.FTS.EllipticEst.remov.ws_aesm_slice (Work.FTS.EllipticEst.SmoothOpen.pz hFso) hz
      have h3 : AEStronglyMeasurable
          (fun θ => Work.Spaces.pz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ)
          (volume.restrict Iθ) :=
        Work.FTS.EllipticEst.remov.ws_aesm_slice (Work.FTS.EllipticEst.SmoothOpen.pz hAso) hz
      have h4 : AEStronglyMeasurable (fun θ => z * Work.Spaces.pzIter 2 Ψ z θ)
          (volume.restrict Iθ) :=
        (Work.FTS.EllipticEst.remov.ws_aesm_slice
          (Work.FTS.EllipticEst.SmoothOpen.pzIter hps 2) hz).const_mul z
      exact (((h1.add (h3.const_mul _)).add (h2.add (h4.const_mul _))).pow 2).mul aesm_sEta_Iθ
    refine Integrable.mono' hdom haesm2 ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with θ hθ
    have h3 : 0 ≤ sEta θ := ws_sEta_nonneg hθ
    have h4 : 0 ≤ (α * (5 + α) * Work.Spaces.pz Ψ z θ
        + α ^ 2 * Work.Spaces.pz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
        + (Work.Spaces.pz F z θ
          + (α ^ 2 + 5 * α) * (z * Work.Spaces.pzIter 2 Ψ z θ))) ^ 2 := sq_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h4 h3)]
    nlinarith [sq_nonneg (α * (5 + α) * Work.Spaces.pz Ψ z θ
        - (α ^ 2 * Work.Spaces.pz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ)),
      sq_nonneg (α * (5 + α) * Work.Spaces.pz Ψ z θ - Work.Spaces.pz F z θ),
      sq_nonneg (α * (5 + α) * Work.Spaces.pz Ψ z θ
        - (α ^ 2 + 5 * α) * (z * Work.Spaces.pzIter 2 Ψ z θ)),
      sq_nonneg (α ^ 2 * Work.Spaces.pz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
        - Work.Spaces.pz F z θ),
      sq_nonneg (α ^ 2 * Work.Spaces.pz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
        - (α ^ 2 + 5 * α) * (z * Work.Spaces.pzIter 2 Ψ z θ)),
      sq_nonneg (Work.Spaces.pz F z θ
        - (α ^ 2 + 5 * α) * (z * Work.Spaces.pzIter 2 Ψ z θ)),
      sq_nonneg (α * (5 + α) * Work.Spaces.pz Ψ z θ),
      sq_nonneg (α ^ 2 * Work.Spaces.pz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ),
      sq_nonneg (Work.Spaces.pz F z θ),
      sq_nonneg ((α ^ 2 + 5 * α) * (z * Work.Spaces.pzIter 2 Ψ z θ))]
  refine hsum.congr ?_
  refine Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ hθ => ?_)
  dsimp only
  rw [hpt θ hθ]

/-- **The unweighted square of the source is integrable** (the `sEta ≥ 1` version of
`dzSlice_Lzero1_sq_integrableOn`), which is the hypothesis of the right-endpoint lemma
`coerc.slice_limit_at_right_eq_zero`. -/
theorem dzSlice_Lzero1_sq_integrableOn_plain {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ}
    (hk : 2 ≤ k) (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn
      (fun θ => (Work.FTS.EllipticEst.Lzero1 (fun t => Work.Spaces.pz Ψ z t) θ) ^ 2) Iθ := by
  refine Integrable.mono' (g := fun θ => (Work.FTS.EllipticEst.Lzero1
      (fun t => Work.Spaces.pz Ψ z t) θ) ^ 2 * sEta θ)
    (dzSlice_Lzero1_sq_integrableOn hk h hz) ?_ ?_
  · have hcont : ContinuousOn (Work.FTS.EllipticEst.Lzero1 (fun t => Work.Spaces.pz Ψ z t))
        (Set.Ioo 0 (Real.pi / 2)) :=
      (Work.FTS.EllipticEst.remov.SliceTopAux.contDiffOnLzero1 0
        (by simpa using dzSlice_contDiffOn h hz 2)).continuousOn
    have h1 : AEStronglyMeasurable
        (fun θ => (Work.FTS.EllipticEst.Lzero1 (fun t => Work.Spaces.pz Ψ z t) θ) ^ 2)
        (volume.restrict (Set.Ioo 0 (Real.pi / 2))) :=
      (hcont.aestronglyMeasurable measurableSet_Ioo).pow 2
    rwa [MeasureTheory.restrict_Ioo_eq_restrict_Icc] at h1
  · filter_upwards [ws_ae_mem_Ioo] with θ hθ
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact le_mul_of_one_le_right (sq_nonneg _) (ws_one_le_sEta hθ)

/-! ## Integrability of the `ψ`-moments of the summands -/

/-- `(D_zΨ(z,·)) · ψ` is integrable (the slice is bounded). -/
theorem integrableOn_DzMulSinCos2 {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hk : 2 ≤ k)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ => Work.Spaces.Dz Ψ z θ * ψ θ) Iθ := by
  obtain ⟨M, hMnn, hMbd⟩ := weakSliceBounds hk h z hz
  have hΨso : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  refine integrableOn_mul_sinCos2_of_abs_le (g := fun θ => Work.Spaces.Dz Ψ z θ) (M := z * M)
    ((Work.FTS.EllipticEst.remov.ws_aesm_slice
      (Work.FTS.EllipticEst.SmoothOpen.pz hΨso) hz).const_mul z) ?_
  intro θ hθ
  rw [show Work.Spaces.Dz Ψ z θ = z * Work.Spaces.pz Ψ z θ from rfl, abs_mul, abs_of_pos hz]
  exact mul_le_mul_of_nonneg_left ((hMbd θ hθ).2.2.1) hz.le

/-- `(z² ∂_z²Ψ(z,·)) · ψ` is integrable. -/
theorem integrableOn_zsqPzIter2MulSinCos2 {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hk : 2 ≤ k)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn
      (fun θ => (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) * ψ θ) Iθ := by
  have hΨso : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hAso : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
    Work.FTS.EllipticEst.H2W.smoothOpen_zsq hΨso
  exact (Work.FTS.EllipticEst.remov.ws_absMoment
    (Work.FTS.EllipticEst.remov.ws_aesm_slice hAso hz)
    (Work.FTS.EllipticEst.remov.ws_slot_slice hAso h.memA 0 (by omega) hz)).1

/-- `(∂_z(z² ∂_z²Ψ)(z,·)) · ψ` is integrable. -/
theorem integrableOn_pzZsqSlice2MulSinCos2 {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hk : 2 ≤ k)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.pz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ * ψ θ)
      Iθ := by
  have hΨso : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hAso : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
    Work.FTS.EllipticEst.H2W.smoothOpen_zsq hΨso
  exact (Work.FTS.EllipticEst.remov.ws_absMoment
    (Work.FTS.EllipticEst.remov.ws_aesm_slice (Work.FTS.EllipticEst.SmoothOpen.pz hAso) hz)
    (pzZsqSlice2_sq_integrableOn hk h hz)).1

/-- `(∂_z F(z,·)) · ψ` is integrable. -/
theorem integrableOn_pzFMulSinCos2 {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hk : 2 ≤ k)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ => Work.Spaces.pz F z θ * ψ θ) Iθ := by
  have hFso : Work.FTS.EllipticEst.SmoothOpen F :=
    (Work.FTS.EllipticEst.remov.smoothOpen_slices_weak h 0).1
  exact (Work.FTS.EllipticEst.remov.ws_absMoment
    (Work.FTS.EllipticEst.remov.ws_aesm_slice (Work.FTS.EllipticEst.SmoothOpen.pz hFso) hz)
    (dzSource_sq_integrableOn hk h hz)).1

/-- `(z ∂_z²Ψ(z,·)) · ψ` is integrable. -/
theorem integrableOn_zPzIter2MulSinCos2 {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hk : 2 ≤ k)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ => (z * Work.Spaces.pzIter 2 Ψ z θ) * ψ θ) Iθ := by
  have hΨso : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  exact (Work.FTS.EllipticEst.remov.ws_absMoment
    ((Work.FTS.EllipticEst.remov.ws_aesm_slice
      (Work.FTS.EllipticEst.SmoothOpen.pzIter hΨso 2) hz).const_mul z)
    (zSlice2_sq_integrableOn hk h hz)).1

/-- `(D_z²Ψ(z,·)) · ψ` is integrable (`D_z²Ψ = D_zΨ + z²∂_z²Ψ`). -/
theorem integrableOn_DzIter2MulSinCos2 {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hk : 2 ≤ k)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ => Work.Spaces.DzIter 2 Ψ z θ * ψ θ) Iθ := by
  have hΨso : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  refine ((integrableOn_DzMulSinCos2 hk h hz).add
    (integrableOn_zsqPzIter2MulSinCos2 hk h hz)).congr ?_
  refine Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ hθ => ?_)
  show Work.Spaces.Dz Ψ z θ * ψ θ + (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) * ψ θ
      = Work.Spaces.DzIter 2 Ψ z θ * ψ θ
  have h2 := Work.FTS.EllipticEst.H2W.zsq_pzIter2_eq hΨso hz hθ
  rw [show Work.Spaces.DzIter 2 Ψ z θ
      = Work.Spaces.Dz Ψ z θ + z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ from by linarith]
  ring

/-- `(D_z³Ψ(z,·)) · ψ` is integrable (`D_z³Ψ = D_z²Ψ + D_z(z²∂_z²Ψ)`). -/
theorem integrableOn_DzIter3MulSinCos2 {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hk : 2 ≤ k)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ => Work.Spaces.DzIter 3 Ψ z θ * ψ θ) Iθ := by
  have hΨso : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hAso : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
    Work.FTS.EllipticEst.H2W.smoothOpen_zsq hΨso
  have hA : MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
        * ψ θ) Iθ :=
    (Work.FTS.EllipticEst.remov.ws_absMoment
      (Work.FTS.EllipticEst.remov.ws_aesm_slice
        (Work.FTS.EllipticEst.SmoothOpen.DzIter hAso 1) hz)
      (Work.FTS.EllipticEst.remov.ws_slot_slice hAso h.memA 1 (by omega) hz)).1
  refine ((integrableOn_DzIter2MulSinCos2 hk h hz).add hA).congr ?_
  refine Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ hθ => ?_)
  show Work.Spaces.DzIter 2 Ψ z θ * ψ θ
      + Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ * ψ θ
      = Work.Spaces.DzIter 3 Ψ z θ * ψ θ
  have h3 := Work.FTS.EllipticEst.H2W.DzIter_three_eq hΨso hz hθ
  rw [show Work.Spaces.DzIter 3 Ψ z θ
      = Work.Spaces.DzIter 2 Ψ z θ
        + Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
      from h3]
  ring

/-! ## The four angular moments -/

/-- **`∫_θ ∂_zΨ(z,θ) sinθcos²θ = 0`**, because the left-hand side is `F_*(D_zΨ)(z)/z`. -/
theorem moment_pzPsi {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hk : 2 ≤ k)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) {z : ℝ} (hz : 0 < z) :
    (∫ θ in Iθ, Work.Spaces.pz Ψ z θ * ψ θ) = 0 := by
  have hk2 : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ := EllWeakPos_of_le_level (by omega) h
  have hFst := Work.FTS.EllipticEst.H2W.Fstar_DzIter_le_Psi α F Ψ hk2 1 (by omega) z hz
  rw [show Work.Spaces.DzIter 1 Ψ = Work.Spaces.Dz Ψ from rfl,
    Work.FTS.EllipticEst.H2W.Fstar_Dz_eq Ψ z, Work.Elliptic.Fstar] at hFst
  exact (mul_eq_zero.mp hFst).resolve_left hz.ne'

/-- **`∫_θ ∂_zF(z,θ) sinθcos²θ = 0`**, because the left-hand side is `F_*(D_zF)(z)/z`. -/
theorem moment_pzF {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hk : 2 ≤ k)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) {z : ℝ} (hz : 0 < z) :
    (∫ θ in Iθ, Work.Spaces.pz F z θ * ψ θ) = 0 := by
  have hFst := Work.FTS.EllipticEst.remov.Fstar_DzIter_one_of_two_le hk h z hz
  rw [show Work.Spaces.DzIter 1 F = Work.Spaces.Dz F from rfl,
    Work.FTS.EllipticEst.H2W.Fstar_Dz_eq F z, Work.Elliptic.Fstar] at hFst
  exact (mul_eq_zero.mp hFst).resolve_left hz.ne'

/-- **`∫_θ z ∂_z²Ψ(z,θ) sinθcos²θ = 0`**, from `D_z²Ψ = D_zΨ + z²∂_z²Ψ` and
`F_*(D_z²Ψ) = F_*(D_zΨ) = 0`. -/
theorem moment_zPzIter2 {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hk : 2 ≤ k)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) {z : ℝ} (hz : 0 < z) :
    (∫ θ in Iθ, (z * Work.Spaces.pzIter 2 Ψ z θ) * ψ θ) = 0 := by
  have hk2 : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ := EllWeakPos_of_le_level (by omega) h
  have hΨso : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hIntDz := integrableOn_DzMulSinCos2 hk h hz
  have hIntz2 := integrableOn_zsqPzIter2MulSinCos2 hk h hz
  have hFst := Work.FTS.EllipticEst.H2W.Fstar_DzIter_le_Psi α F Ψ hk2 2 (by omega) z hz
  rw [Work.Elliptic.Fstar] at hFst
  have hcongr : (fun θ => Work.Spaces.DzIter 2 Ψ z θ * ψ θ)
      =ᵐ[volume.restrict Iθ]
        (fun θ => Work.Spaces.Dz Ψ z θ * ψ θ + (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) * ψ θ) := by
    refine Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ hθ => ?_)
    dsimp only
    have h2 := Work.FTS.EllipticEst.H2W.zsq_pzIter2_eq hΨso hz hθ
    rw [show Work.Spaces.DzIter 2 Ψ z θ
        = Work.Spaces.Dz Ψ z θ + z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ from by linarith]
    ring
  have hsum : (∫ θ in Iθ, Work.Spaces.Dz Ψ z θ * ψ θ)
      + (∫ θ in Iθ, (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) * ψ θ) = 0 := by
    rw [← MeasureTheory.integral_add (f := fun θ => Work.Spaces.Dz Ψ z θ * ψ θ)
      (g := fun θ => (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) * ψ θ) hIntDz hIntz2]
    rw [← MeasureTheory.integral_congr_ae hcongr]
    exact hFst
  have hDz0 : (∫ θ in Iθ, Work.Spaces.Dz Ψ z θ * ψ θ) = 0 := by
    rw [show (fun θ => Work.Spaces.Dz Ψ z θ * ψ θ)
        = fun θ => z * (Work.Spaces.pz Ψ z θ * ψ θ) from by
      funext θ; simp only [Work.Spaces.Dz]; ring,
      MeasureTheory.integral_const_mul, moment_pzPsi hk h hz, mul_zero]
  have hz2P : (∫ θ in Iθ, (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) * ψ θ) = 0 := by
    rw [hDz0, zero_add] at hsum
    exact hsum
  have hmid : (∫ θ in Iθ, Work.Spaces.pzIter 2 Ψ z θ * ψ θ) = 0 := by
    have h1 : (∫ θ in Iθ, (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) * ψ θ)
        = z ^ 2 * (∫ θ in Iθ, Work.Spaces.pzIter 2 Ψ z θ * ψ θ) := by
      rw [show (fun θ => (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) * ψ θ)
          = fun θ => z ^ 2 * (Work.Spaces.pzIter 2 Ψ z θ * ψ θ) from by
        funext θ; ring,
        MeasureTheory.integral_const_mul]
    rw [h1] at hz2P
    exact (mul_eq_zero.mp hz2P).resolve_left (pow_ne_zero 2 hz.ne')
  rw [show (fun θ => (z * Work.Spaces.pzIter 2 Ψ z θ) * ψ θ)
      = fun θ => z * (Work.Spaces.pzIter 2 Ψ z θ * ψ θ) from by funext θ; ring,
    MeasureTheory.integral_const_mul, hmid, mul_zero]

/-- **`∫_θ ∂_z(z²∂_z²Ψ)(z,θ) sinθcos²θ = 0`**, from `D_z(z²∂_z²Ψ) = D_z³Ψ - D_z²Ψ` and the
vanishing of `F_*(D_z²Ψ)`, `F_*(D_z³Ψ)`. -/
theorem moment_pzZsqSlice2 {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hk : 2 ≤ k)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) {z : ℝ} (hz : 0 < z) :
    (∫ θ in Iθ,
        Work.Spaces.pz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ * ψ θ) = 0 := by
  have hk2 : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ := EllWeakPos_of_le_level (by omega) h
  have hΨso : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hAso : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
    Work.FTS.EllipticEst.H2W.smoothOpen_zsq hΨso
  have hIntA : MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
        * ψ θ) Iθ :=
    (Work.FTS.EllipticEst.remov.ws_absMoment
      (Work.FTS.EllipticEst.remov.ws_aesm_slice
        (Work.FTS.EllipticEst.SmoothOpen.DzIter hAso 1) hz)
      (Work.FTS.EllipticEst.remov.ws_slot_slice hAso h.memA 1 (by omega) hz)).1
  have hInt2 := integrableOn_DzIter2MulSinCos2 hk h hz
  have hInt3 := integrableOn_DzIter3MulSinCos2 hk h hz
  have hmain : (∫ θ in Iθ,
      Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ * ψ θ) = 0 := by
    have hFst3 := Work.FTS.EllipticEst.H2W.Fstar_DzIter_le_Psi α F Ψ hk2 3 (by omega) z hz
    have hFst2 := Work.FTS.EllipticEst.H2W.Fstar_DzIter_le_Psi α F Ψ hk2 2 (by omega) z hz
    rw [Work.Elliptic.Fstar] at hFst3 hFst2
    have hcongr : (fun θ => Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ
          z θ) z θ * ψ θ)
        =ᵐ[volume.restrict Iθ]
          (fun θ => Work.Spaces.DzIter 3 Ψ z θ * ψ θ
            - Work.Spaces.DzIter 2 Ψ z θ * ψ θ) := by
      refine Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ hθ => ?_)
      show Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ * ψ θ
          = Work.Spaces.DzIter 3 Ψ z θ * ψ θ - Work.Spaces.DzIter 2 Ψ z θ * ψ θ
      have h3 := Work.FTS.EllipticEst.H2W.DzIter_zsq_pzIter2_eq hΨso 1 hz hθ
      rw [show (1 + 2 : ℕ) = 3 from rfl, show (1 + 1 : ℕ) = 2 from rfl] at h3
      rw [h3]
      ring
    have hsplit : (∫ θ in Iθ,
          Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ * ψ θ)
        = (∫ θ in Iθ, Work.Spaces.DzIter 3 Ψ z θ * ψ θ)
          - (∫ θ in Iθ, Work.Spaces.DzIter 2 Ψ z θ * ψ θ) :=
      (MeasureTheory.integral_congr_ae hcongr).trans
        (MeasureTheory.integral_sub (f := fun θ => Work.Spaces.DzIter 3 Ψ z θ * ψ θ)
          (g := fun θ => Work.Spaces.DzIter 2 Ψ z θ * ψ θ) hInt3 hInt2)
    rw [hsplit, hFst3, hFst2, sub_zero]
  have hkey : (∫ θ in Iθ, Work.Spaces.pz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
        * ψ θ)
      = z⁻¹ * (∫ θ in Iθ,
          Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
            * ψ θ) := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_congr_ae ?_
    refine Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ hθ => ?_)
    dsimp only
    simp only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, Work.Spaces.Dz]
    field_simp
  rw [hkey, hmain, mul_zero]

/-! ## The angular moment of `Lzero1 V` -/

/-- **The angular moment of the source of the `∂_z`-slice vanishes.** -/
theorem dzSlice_Lzero1_moment {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hk : 2 ≤ k)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) {z : ℝ} (hz : 0 < z) :
    (∫ θ in Iθ,
      Work.FTS.EllipticEst.Lzero1 (fun t => Work.Spaces.pz Ψ z t) θ * ψ θ) = 0 := by
  have hps : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  obtain ⟨M, hMnn, hMbd⟩ := weakSliceBounds hk h z hz
  -- integrability of the four moments
  have hI1 : MeasureTheory.IntegrableOn (fun θ => Work.Spaces.pz Ψ z θ * ψ θ) Iθ :=
    integrableOn_mul_sinCos2_of_abs_le
      (Work.FTS.EllipticEst.remov.ws_aesm_slice (Work.FTS.EllipticEst.SmoothOpen.pz hps) hz)
      (fun θ hθ => (hMbd θ hθ).2.2.1)
  have hI2 := integrableOn_pzFMulSinCos2 hk h hz
  have hI3 := integrableOn_pzZsqSlice2MulSinCos2 hk h hz
  have hI4 := integrableOn_zPzIter2MulSinCos2 hk h hz
  -- the pointwise identity
  have hpt : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.FTS.EllipticEst.Lzero1 (fun t => Work.Spaces.pz Ψ z t) θ
        = α * (5 + α) * Work.Spaces.pz Ψ z θ
          + (Work.Spaces.pz F z θ
            + (α ^ 2 * Work.Spaces.pz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
              + (α ^ 2 + 5 * α) * (z * Work.Spaces.pzIter 2 Ψ z θ))) := by
    intro θ hθ
    have h1 := sliceShiftedDecomposition hk h z hz θ hθ
    linarith
  have hae : (fun θ => Work.FTS.EllipticEst.Lzero1 (fun t => Work.Spaces.pz Ψ z t) θ * ψ θ)
      =ᵐ[volume.restrict Iθ]
        (fun θ => (α * (5 + α) * Work.Spaces.pz Ψ z θ
          + (Work.Spaces.pz F z θ
            + (α ^ 2 * Work.Spaces.pz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
              + (α ^ 2 + 5 * α) * (z * Work.Spaces.pzIter 2 Ψ z θ)))) * ψ θ) := by
    refine Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ hθ => ?_)
    show Work.FTS.EllipticEst.Lzero1 (fun t => Work.Spaces.pz Ψ z t) θ * ψ θ
      = (α * (5 + α) * Work.Spaces.pz Ψ z θ
          + (Work.Spaces.pz F z θ
            + (α ^ 2 * Work.Spaces.pz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
              + (α ^ 2 + 5 * α) * (z * Work.Spaces.pzIter 2 Ψ z θ)))) * ψ θ
    rw [hpt θ hθ]
  have hFun : (fun θ => (α * (5 + α) * Work.Spaces.pz Ψ z θ
        + (Work.Spaces.pz F z θ
          + (α ^ 2 * Work.Spaces.pz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
            + (α ^ 2 + 5 * α) * (z * Work.Spaces.pzIter 2 Ψ z θ)))) * ψ θ)
      = fun θ => α * (5 + α) * (Work.Spaces.pz Ψ z θ * ψ θ)
        + (Work.Spaces.pz F z θ * ψ θ
          + (α ^ 2 * (Work.Spaces.pz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ * ψ θ)
            + (α ^ 2 + 5 * α) * ((z * Work.Spaces.pzIter 2 Ψ z θ) * ψ θ))) := by
    funext θ; ring
  rw [MeasureTheory.integral_congr_ae hae, hFun]
  -- the four moments, and the additivity of the integral
  have hA : (∫ θ in Iθ, α * (5 + α) * (Work.Spaces.pz Ψ z θ * ψ θ)) = 0 := by
    rw [MeasureTheory.integral_const_mul, moment_pzPsi hk h hz, mul_zero]
  have hB : (∫ θ in Iθ, Work.Spaces.pz F z θ * ψ θ) = 0 := moment_pzF hk h hz
  have hC : (∫ θ in Iθ,
      α ^ 2 * (Work.Spaces.pz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ * ψ θ)) = 0 := by
    rw [MeasureTheory.integral_const_mul, moment_pzZsqSlice2 hk h hz, mul_zero]
  have hD : (∫ θ in Iθ, (α ^ 2 + 5 * α) * ((z * Work.Spaces.pzIter 2 Ψ z θ) * ψ θ)) = 0 := by
    rw [MeasureTheory.integral_const_mul, moment_zPzIter2 hk h hz, mul_zero]
  -- integrability of the summands, in the exact lambda shapes
  have hI1L : Integrable (fun θ => α * (5 + α) * (Work.Spaces.pz Ψ z θ * ψ θ))
      (volume.restrict Iθ) := hI1.const_mul (α * (5 + α))
  have hI3L : Integrable (fun θ => α ^ 2
      * (Work.Spaces.pz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ * ψ θ))
      (volume.restrict Iθ) := hI3.const_mul (α ^ 2)
  have hI4L : Integrable (fun θ => (α ^ 2 + 5 * α) * ((z * Work.Spaces.pzIter 2 Ψ z θ) * ψ θ))
      (volume.restrict Iθ) := hI4.const_mul (α ^ 2 + 5 * α)
  have hI34 : Integrable (fun θ => α ^ 2
        * (Work.Spaces.pz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ * ψ θ)
        + (α ^ 2 + 5 * α) * ((z * Work.Spaces.pzIter 2 Ψ z θ) * ψ θ)) (volume.restrict Iθ) :=
    (hI3L.add hI4L).congr (by
      filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with θ _
      simp only [Pi.add_apply])
  have hI234 : Integrable (fun θ => Work.Spaces.pz F z θ * ψ θ
        + (α ^ 2 * (Work.Spaces.pz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ * ψ θ)
          + (α ^ 2 + 5 * α) * ((z * Work.Spaces.pzIter 2 Ψ z θ) * ψ θ))) (volume.restrict Iθ) :=
    (hI2.add hI34).congr (by
      filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with θ _
      simp only [Pi.add_apply])
  have hI1234 : Integrable (fun θ => α * (5 + α) * (Work.Spaces.pz Ψ z θ * ψ θ)
        + (Work.Spaces.pz F z θ * ψ θ
          + (α ^ 2 * (Work.Spaces.pz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ * ψ θ)
            + (α ^ 2 + 5 * α) * ((z * Work.Spaces.pzIter 2 Ψ z θ) * ψ θ))))
      (volume.restrict Iθ) :=
    (hI1L.add hI234).congr (by
      filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with θ _
      simp only [Pi.add_apply])
  have hBC : (∫ θ in Iθ, Work.Spaces.pz F z θ * ψ θ
        + (α ^ 2 * (Work.Spaces.pz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ * ψ θ)
          + (α ^ 2 + 5 * α) * ((z * Work.Spaces.pzIter 2 Ψ z θ) * ψ θ)))
      = (∫ θ in Iθ, Work.Spaces.pz F z θ * ψ θ)
        + (∫ θ in Iθ,
            α ^ 2 * (Work.Spaces.pz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ * ψ θ)
            + (α ^ 2 + 5 * α) * ((z * Work.Spaces.pzIter 2 Ψ z θ) * ψ θ)) :=
    MeasureTheory.integral_add (f := fun θ => Work.Spaces.pz F z θ * ψ θ)
      (g := fun θ => α ^ 2 * (Work.Spaces.pz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
          z θ * ψ θ) + (α ^ 2 + 5 * α) * ((z * Work.Spaces.pzIter 2 Ψ z θ) * ψ θ))
      hI2 hI34
  have hCD : (∫ θ in Iθ,
        α ^ 2 * (Work.Spaces.pz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ * ψ θ)
          + (α ^ 2 + 5 * α) * ((z * Work.Spaces.pzIter 2 Ψ z θ) * ψ θ))
      = (∫ θ in Iθ,
          α ^ 2 * (Work.Spaces.pz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ * ψ θ))
        + (∫ θ in Iθ, (α ^ 2 + 5 * α) * ((z * Work.Spaces.pzIter 2 Ψ z θ) * ψ θ)) :=
    MeasureTheory.integral_add
      (f := fun θ => α ^ 2 * (Work.Spaces.pz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
        z θ * ψ θ))
      (g := fun θ => (α ^ 2 + 5 * α) * ((z * Work.Spaces.pzIter 2 Ψ z θ) * ψ θ))
      hI3L hI4L
  calc (∫ θ in Iθ, α * (5 + α) * (Work.Spaces.pz Ψ z θ * ψ θ)
        + (Work.Spaces.pz F z θ * ψ θ
          + (α ^ 2 * (Work.Spaces.pz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ * ψ θ)
            + (α ^ 2 + 5 * α) * ((z * Work.Spaces.pzIter 2 Ψ z θ) * ψ θ))))
      = (∫ θ in Iθ, α * (5 + α) * (Work.Spaces.pz Ψ z θ * ψ θ))
        + (∫ θ in Iθ, Work.Spaces.pz F z θ * ψ θ
          + (α ^ 2 * (Work.Spaces.pz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ * ψ θ)
            + (α ^ 2 + 5 * α) * ((z * Work.Spaces.pzIter 2 Ψ z θ) * ψ θ))) :=
        MeasureTheory.integral_add
          (f := fun θ => α * (5 + α) * (Work.Spaces.pz Ψ z θ * ψ θ))
          (g := fun θ => Work.Spaces.pz F z θ * ψ θ
            + (α ^ 2 * (Work.Spaces.pz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ * ψ θ)
              + (α ^ 2 + 5 * α) * ((z * Work.Spaces.pzIter 2 Ψ z θ) * ψ θ)))
          hI1L hI234
    _ = (∫ θ in Iθ, α * (5 + α) * (Work.Spaces.pz Ψ z θ * ψ θ))
        + ((∫ θ in Iθ, Work.Spaces.pz F z θ * ψ θ)
          + (∫ θ in Iθ,
              α ^ 2 * (Work.Spaces.pz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ * ψ θ)
              + (α ^ 2 + 5 * α) * ((z * Work.Spaces.pzIter 2 Ψ z θ) * ψ θ))) := by rw [hBC]
    _ = (∫ θ in Iθ, α * (5 + α) * (Work.Spaces.pz Ψ z θ * ψ θ))
        + ((∫ θ in Iθ, Work.Spaces.pz F z θ * ψ θ)
          + ((∫ θ in Iθ,
              α ^ 2 * (Work.Spaces.pz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ * ψ θ))
            + (∫ θ in Iθ, (α ^ 2 + 5 * α) * ((z * Work.Spaces.pzIter 2 Ψ z θ) * ψ θ)))) := by
        rw [hCD]
    _ = 0 := by rw [hA, hB, hC, hD]; ring

theorem dzPsiLimits {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hk : 2 ≤ k)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) :
    ∀ z, 0 < z →
      Filter.Tendsto (fun θ => Work.Spaces.pz Ψ z θ) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
      Filter.Tendsto (fun θ => Work.Spaces.pz Ψ z θ)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
  intro z hz
  constructor
  · -- the left endpoint: the angular moment of the source vanishes
    exact sliceTendstoZeroOfMoment (fun θ => Work.Spaces.pz Ψ z θ) (dzSlice_contDiffOn h hz 2)
      (dzSlice_secondDeriv_integrableOn hk h hz) (dzSlice_Lzero1_sq_integrableOn hk h hz)
      (dzSlice_sq_integrableOn hk h hz) (dzSlice_Lzero1_moment hk h hz)
  · -- the right endpoint: the limit exists, and is zero because `Lzero1 V ∈ L²`
    obtain ⟨-, ν, hν⟩ :=
      Work.FTS.EllipticEst.remov.coerc.tendsTo_atEnds_of_integrableOn_sq_deriv
        (u := fun θ => Work.Spaces.pz Ψ z θ) (L := Real.pi / 2) (by linarith [Real.pi_pos])
        (dzSlice_contDiffOn h hz 2) (dzSlice_deriv_sq_integrableOn hk h hz)
    have hν0 : ν = 0 :=
      Work.FTS.EllipticEst.remov.coerc.slice_limit_at_right_eq_zero
        (u := fun θ => Work.Spaces.pz Ψ z θ) (ν := ν) (dzSlice_contDiffOn h hz 2)
        (dzSlice_sq_integrableOn hk h hz) (dzSlice_deriv_sq_integrableOn hk h hz)
        (dzSlice_Lzero1_sq_integrableOn_plain hk h hz) hν
    simpa [hν0] using hν

end Work.FTS.EllipticEst.remov.SourceBound
