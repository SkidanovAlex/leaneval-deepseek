/-
Copyright: work module for the Elgindi finite-time singularity project.

# `pPureShiftAux/Basic` — the radial difference-quotient datum of a weak datum

The level-`0` estimate `TT.EllWeak0` applies to data of the weak class `TT.EllWeakPos`.  To get
the *twice radially differentiated* datum `(D_z²F, D_z²Ψ)` into that class one cannot simply
shift (the pointwise moment condition `F_*(D_z²F) ≡ 0` is only available *a.e.*,
`H2W.Fstar_DzIter_two_F_ae`).  The way out is the radial **difference quotient**

  `dq c h = (h (c·) - h)/(c-1)`,   `c > 1`,

which commutes with `bslOp` (`Dil.bslOp_dq`), with the slot operators `z²∂_z²` and `∂_θ²`
(`Dil.zsq_pzIter_two_dq`, `Dil.pthIter_two_dq`) and with the angular moments (linearity of the
`θ`-integral), so that

  `(dq c X, dq c Y)` is in the class whenever `(X, Y)` is,

and which tends to the radial derivative `D_z` as `c → 1⁺`.

This module contains

* `HkSq_zero_DzIter_two_le'`, `lhs_eq_HkSq'` — the level-`0` bookkeeping;
* `HkMem_dq_and_HkSq_dq_le_self` — the mean-value engine (`|dq c g| ≲ D_z g` in the
  `ℋ⁰`-norm), the single analytic input;
* `ae_mem_Q0` — `Q0` is conull for the quadrant measure;
* `EllWeakPos_dq` — the class membership of the difference-quotient datum.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.Cores.Dil.DilBasic
import Submission.Work.FTS.EllipticEst.Cores.Dil.Tools
import Submission.Work.FTS.EllipticEst.Cores.Dil.DilMoments
import Submission.Work.FTS.EllipticEst.Cores.Dil.DqqTendsto
import Submission.Work.FTS.EllipticEst.Cores.Dil.HkSqLimit
import Submission.Work.FTS.EllipticEst.HkSq_congr_open
import Submission.Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0
import Submission.Work.FTS.EllipticEst.TT.HkMem_descend_open
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.EllipticEst.Cores.pPureShiftAux.MajEst

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cores.pPureShiftAux

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- The second radial difference quotient `dq c (dq c g)`. -/
abbrev dqq (c : ℝ) (g : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  Work.FTS.EllipticEst.Cores.Dil.dq c (Work.FTS.EllipticEst.Cores.Dil.dq c g)

theorem dqq_apply (c : ℝ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    dqq c g z θ = Work.FTS.EllipticEst.Cores.Dil.dq c
      (Work.FTS.EllipticEst.Cores.Dil.dq c g) z θ := rfl

/-! ## The mean-value engine -/

/-- **The difference quotient is dominated by the radial derivative.**  For `g` of class `C^∞`
on the open quadrant whose radial derivative `D_z g` is honestly in `ℋ⁰`, and `c > 1`, the
difference quotient `dq c g` is again in `ℋ⁰`, with squared `ℋ⁰`-norm bounded by `c³` times that
of `D_z g`.  This is the only analytic input of the difference-quotient route. -/
theorem HkMem_dq_and_HkSq_dq_le_self {α c : ℝ} {g : ℝ → ℝ → ℝ}
    (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (hgmem : Work.Spaces.HkMem α 0 (Work.Spaces.Dz g))
    (hc : 1 < c) :
    Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.Cores.Dil.dq c g) ∧
      Work.Spaces.HkSq α 0 (Work.FTS.EllipticEst.Cores.Dil.dq c g)
        ≤ c ^ 3 * Work.Spaces.HkSq α 0 (Work.Spaces.Dz g) := by
  have hcpos : 0 < c := lt_trans zero_lt_one hc
  set Φ : ℝ → ℝ → ℝ := fun z θ => Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz g) z θ with hΦ
  have hnn : ∀ z θ, 0 ≤ Φ z θ := fun z θ =>
    Work.Spaces.HkIntegrand_nonneg α 0 (Work.Spaces.Dz g) z θ
  have hΦc : ContinuousOn (fun p : ℝ × ℝ => Φ p.1 p.2) Work.FTS.EllipticEst.Q0 :=
    hg.Dz.continuousOn_HkIntegrand α 0
  have hcontu : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      ContinuousOn (fun u : ℝ => u ^ 2 * Φ (z * u) θ) (Set.Icc (1 : ℝ) c) :=
    Work.FTS.EllipticEst.Cores.PPureShiftRad.continuousOn_u_majorant (α := α) hg hc
  have hΦint : ∀ s ∈ Work.Spaces.Iz,
      IntegrableOn (fun θ => Φ s θ) Work.Spaces.Iθ := hgmem.1
  have hΦ0 : ∀ θ, Φ 0 θ = 0 := fun θ =>
    Work.FTS.LocData.HkIntegrand_zero_fst α 0 (Work.Spaces.Dz g) θ
  have hKfin : (∫⁻ p, ENNReal.ofReal (Φ p.1 p.2) ∂qM) ≠ ⊤ := by
    rw [lintegral_ofReal_HkIntegrand_eq' hg.Dz hgmem]
    exact ENNReal.ofReal_ne_top
  have hmem : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.Cores.Dil.dq c g) := by
    refine Work.FTS.LocData.HkMem_of_majorant α 0
      (f := Work.FTS.EllipticEst.Cores.Dil.dq c g) (M := Maj c Φ) ?_ ?_ ?_ ?_
    · exact (Work.FTS.EllipticEst.Cores.Dil.smoothOpen_dq hg hcpos).continuousOn_HkIntegrand α 0
    · exact integrableOn_Maj_slice hc hnn hΦc hcontu hΦint hΦ0 hKfin
    · exact integrableOn_Maj_z hc hnn hΦc hcontu hΦint hΦ0 hKfin
    · intro z hz θ hθ
      exact Work.FTS.EllipticEst.Cores.PPureShiftRad.HkIntegrand_dq_le hg hc z hz θ hθ
  refine ⟨hmem, ?_⟩
  have h1 := lintegral_HkIntegrand_dq_le hg hgmem hc
  rw [lintegral_ofReal_HkIntegrand_eq'
    (Work.FTS.EllipticEst.Cores.Dil.smoothOpen_dq hg hcpos) hmem] at h1
  exact (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg (by positivity) (Work.Spaces.HkSq_nonneg α 0 (Work.Spaces.Dz g)))).mp h1

/-! ## Level-`0` bookkeeping -/

/-- The level-`0` `HkIntegrand` is the single squared weighted slot. -/
theorem HkIntegrand_zero_eq' (α : ℝ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 g z θ
      = (g z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  rw [Work.Spaces.HkIntegrand]
  simp

/-- `HkSq α 0 g` is the `L²`-square of the single weighted slot. -/
theorem HkSq_zero_eq_L2Sq (α : ℝ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.HkSq α 0 g
      = Work.Spaces.L2Sq (fun z θ =>
          g z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) := by
  rw [Work.Spaces.HkSq, Work.Spaces.L2Sq]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
  exact HkIntegrand_zero_eq' α g z θ

/-- **`HkSq α 0 (D_z²f) ≤ HkSq α 2 f`**: the level-`0` norm of the twice radially differentiated
function is the `i = 2` pure slot of the level-`2` norm. -/
theorem HkSq_zero_DzIter_two_le' (α : ℝ) (g : ℝ → ℝ → ℝ) (hmem : Work.Spaces.HkMem α 2 g) :
    Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 2 g) ≤ Work.Spaces.HkSq α 2 g := by
  rw [HkSq_zero_eq_L2Sq]
  exact Work.Spaces.L2Sq_DzIter_le_HkSq α 2 g hmem 2 le_rfl

/-- On `Iθ` (where `sin(2θ) ≥ 0`) the level-`0` slot squares to `g² · sin(2θ)^{-η} · w²`. -/
theorem weight_sq_eq' (g : ℝ → ℝ → ℝ) (z θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) :
    (g z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = (g z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ * (Work.Spaces.w z) ^ 2 := by
  have hs : 0 ≤ Real.sin (2 * θ) := by
    refine Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], ?_⟩
    linarith [hθ.2, Real.pi_pos]
  have hsq : (Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) ^ (2 : ℕ)
      = Real.sin (2 * θ) ^ Work.Spaces.eta := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hs]
    norm_num
  rw [Work.FTS.EllipticEst.sEta, mul_pow, div_pow, hsq, Real.rpow_neg hs]
  ring

/-- **The left-hand side of the target is `HkSq α 0 (∂_θ²(D_z²Ψ))`.** -/
theorem lhs_eq_HkSq' (α : ℝ) (Ψ : ℝ → ℝ → ℝ) :
    (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 2 Ψ) z θ) ^ 2 *
            Work.FTS.EllipticEst.sEta θ))
      = Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 2 Ψ)) := by
  rw [HkSq_zero_eq_L2Sq, Work.Spaces.L2Sq]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
  rw [show Work.Spaces.Iθ = Set.Icc 0 (Real.pi / 2) from rfl]
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Icc
    (fun θ hθ => weight_sq_eq' _ z θ hθ)]
  rw [MeasureTheory.integral_mul_const]
  ring

/-! ## `Q0` is conull -/

/-- Almost every point of the quadrant measure lies in the open quadrant `Q0`. -/
theorem ae_mem_Q0 :
    ∀ᵐ p ∂Work.FTS.EllipticEst.Cores.Dil.quadMeasure,
      p ∈ Work.FTS.EllipticEst.Q0 := by
  have hz_ae : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), 0 < z := by
    rw [Work.Spaces.Iz, MeasureTheory.ae_restrict_iff' measurableSet_Ici, MeasureTheory.ae_iff]
    refine MeasureTheory.measure_mono_null ?_ (MeasureTheory.measure_singleton 0)
    intro z hz
    rw [Set.mem_setOf_eq, not_imp, Set.mem_Ici, not_lt] at hz
    simp only [Set.mem_singleton_iff]
    exact le_antisymm hz.2 hz.1
  have hθ_ae : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      0 < θ ∧ θ < Real.pi / 2 := by
    rw [Work.Spaces.Iθ, MeasureTheory.ae_restrict_iff' measurableSet_Icc, MeasureTheory.ae_iff]
    refine MeasureTheory.measure_mono_null ?_ (MeasureTheory.measure_union_null
      (MeasureTheory.measure_singleton 0) (MeasureTheory.measure_singleton (Real.pi / 2)))
    intro θ hθ
    rw [Set.mem_setOf_eq, not_imp, not_and, Set.mem_Icc] at hθ
    have h0 : 0 ≤ θ := hθ.1.1
    have hπ : θ ≤ Real.pi / 2 := hθ.1.2
    have hcase : 0 < θ → Real.pi / 2 ≤ θ := fun h => not_lt.mp (hθ.2 h)
    simp only [Set.mem_union, Set.mem_singleton_iff]
    by_cases hpos : 0 < θ
    · exact Or.inr (le_antisymm hπ (hcase hpos))
    · exact Or.inl (le_antisymm (not_lt.mp hpos) h0)
  rw [Work.FTS.EllipticEst.Cores.Dil.quadMeasure]
  refine (MeasureTheory.Measure.ae_prod_mem_iff_ae_ae_mem
    (Work.FTS.EllipticEst.isOpen_Q0.measurableSet)).mpr ?_
  filter_upwards [hz_ae] with z hz
  filter_upwards [hθ_ae] with θ hθ
  exact Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩

/-! ## The engine, iterated once -/

/-- `D_z (dq c g) = dq c (D_z g)` on the open quadrant. -/
theorem Dz_dq_eqOn {c : ℝ} {g : ℝ → ℝ → ℝ} (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (hc : 1 < c) :
    ∀ (z θ : ℝ), 0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) →
      Work.Spaces.Dz (Work.FTS.EllipticEst.Cores.Dil.dq c g) z θ
        = Work.FTS.EllipticEst.Cores.Dil.dq c (Work.Spaces.Dz g) z θ := by
  intro z θ hz hθ
  have hpz := Work.FTS.EllipticEst.Cores.Dil.pz_dq hg hc z θ hz hθ
  show z * Work.Spaces.pz (Work.FTS.EllipticEst.Cores.Dil.dq c g) z θ
    = (Work.Spaces.Dz g (c * z) θ - Work.Spaces.Dz g z θ) / (c - 1)
  rw [hpz]
  simp only [Work.Spaces.Dz]
  ring

/-- **`ℋ⁰`-honesty of the second difference quotient**: it follows from the honesty of the
second radial derivative of the argument, by two applications of the engine. -/
theorem HkMem_dqq {α c : ℝ} {Z : ℝ → ℝ → ℝ}
    (hZ : Work.FTS.EllipticEst.SmoothOpen Z)
    (hZ1 : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dz Z))
    (hmem : Work.Spaces.HkMem α 0 (Work.Spaces.Dz (Work.Spaces.Dz Z)))
    (hc : 1 < c) : Work.Spaces.HkMem α 0 (dqq c Z) := by
  have h1 : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.Cores.Dil.dq c (Work.Spaces.Dz Z)) :=
    (HkMem_dq_and_HkSq_dq_le_self hZ1 hmem hc).1
  have h2 : Work.Spaces.HkMem α 0 (Work.Spaces.Dz (Work.FTS.EllipticEst.Cores.Dil.dq c Z)) :=
    Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 0 h1
      (fun z hz θ hθ => (Dz_dq_eqOn hZ hc z θ hz hθ).symm)
  have h3 : Work.Spaces.HkMem α 0
      (Work.FTS.EllipticEst.Cores.Dil.dq c (Work.FTS.EllipticEst.Cores.Dil.dq c Z)) :=
    (HkMem_dq_and_HkSq_dq_le_self
      (Work.FTS.EllipticEst.Cores.Dil.smoothOpen_dq hZ (lt_trans zero_lt_one hc)) h2 hc).1
  exact h3

/-- **The `ℋ⁰`-bound for the second difference quotient**: `HkSq α 0 (dqq c Z) ≤ c⁶ HkSq α 0
(D_z²Z)`, by two applications of the engine. -/
theorem HkSq_dqq_le {α c : ℝ} {Z : ℝ → ℝ → ℝ}
    (hZ : Work.FTS.EllipticEst.SmoothOpen Z)
    (hZ1 : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dz Z))
    (hmem : Work.Spaces.HkMem α 0 (Work.Spaces.Dz (Work.Spaces.Dz Z)))
    (hc : 1 < c) :
    Work.Spaces.HkSq α 0 (dqq c Z)
      ≤ c ^ 6 * Work.Spaces.HkSq α 0 (Work.Spaces.Dz (Work.Spaces.Dz Z)) := by
  have hmem1 : Work.Spaces.HkMem α 0
      (Work.FTS.EllipticEst.Cores.Dil.dq c (Work.Spaces.Dz Z)) :=
    (HkMem_dq_and_HkSq_dq_le_self hZ1 hmem hc).1
  have h4 : Work.Spaces.HkMem α 0 (Work.Spaces.Dz (Work.FTS.EllipticEst.Cores.Dil.dq c Z)) :=
    Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 0 hmem1
      (fun z hz θ hθ => (Dz_dq_eqOn hZ hc z θ hz hθ).symm)
  have h3 : Work.Spaces.HkSq α 0
        (Work.FTS.EllipticEst.Cores.Dil.dq c (Work.FTS.EllipticEst.Cores.Dil.dq c Z))
      ≤ c ^ 3 * Work.Spaces.HkSq α 0
          (Work.Spaces.Dz (Work.FTS.EllipticEst.Cores.Dil.dq c Z)) :=
    (HkMem_dq_and_HkSq_dq_le_self
      (Work.FTS.EllipticEst.Cores.Dil.smoothOpen_dq hZ (lt_trans zero_lt_one hc)) h4 hc).2
  have h1 : Work.Spaces.HkSq α 0 (Work.FTS.EllipticEst.Cores.Dil.dq c (Work.Spaces.Dz Z))
      ≤ c ^ 3 * Work.Spaces.HkSq α 0 (Work.Spaces.Dz (Work.Spaces.Dz Z)) :=
    (HkMem_dq_and_HkSq_dq_le_self hZ1 hmem hc).2
  have h2 : Work.Spaces.HkSq α 0 (Work.Spaces.Dz (Work.FTS.EllipticEst.Cores.Dil.dq c Z))
      = Work.Spaces.HkSq α 0 (Work.FTS.EllipticEst.Cores.Dil.dq c (Work.Spaces.Dz Z)) :=
    Work.FTS.EllipticEst.HkSq_congr_open α 0
      (fun z θ hz hθ hlt => Dz_dq_eqOn hZ hc z θ hz ⟨hθ, hlt⟩)
  calc Work.Spaces.HkSq α 0
        (Work.FTS.EllipticEst.Cores.Dil.dq c (Work.FTS.EllipticEst.Cores.Dil.dq c Z))
      ≤ c ^ 3 * Work.Spaces.HkSq α 0
          (Work.Spaces.Dz (Work.FTS.EllipticEst.Cores.Dil.dq c Z)) := h3
    _ = c ^ 3 * Work.Spaces.HkSq α 0
          (Work.FTS.EllipticEst.Cores.Dil.dq c (Work.Spaces.Dz Z)) := by rw [h2]
    _ ≤ c ^ 3 * (c ^ 3 * Work.Spaces.HkSq α 0 (Work.Spaces.Dz (Work.Spaces.Dz Z))) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = c ^ 6 * Work.Spaces.HkSq α 0 (Work.Spaces.Dz (Work.Spaces.Dz Z)) := by ring

/-! ## The slot identities for the second difference quotient -/

/-- `z²∂_z²(dqq c f) = dqq c (z²∂_z²f)` on the open quadrant. -/
theorem zsq_pzIter_two_dqq_eqOn {c : ℝ} {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hc : 1 < c) :
    ∀ (z θ : ℝ), 0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) →
      z ^ 2 * Work.Spaces.pzIter 2 (dqq c f) z θ
        = dqq c (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ) z θ := by
  intro z θ hz hθ
  have h1 : z ^ 2 * Work.Spaces.pzIter 2 (Work.FTS.EllipticEst.Cores.Dil.dq c
        (Work.FTS.EllipticEst.Cores.Dil.dq c f)) z θ
      = Work.FTS.EllipticEst.Cores.Dil.dq c
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2
            (Work.FTS.EllipticEst.Cores.Dil.dq c f) z θ) z θ :=
    Work.FTS.EllipticEst.Cores.Dil.zsq_pzIter_two_dq
      (Work.FTS.EllipticEst.Cores.Dil.smoothOpen_dq hf (lt_trans zero_lt_one hc)) hc z θ hz hθ
  have hcongr : ∀ y : ℝ, 0 < y →
      Work.FTS.EllipticEst.Cores.Dil.dq c (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ) y θ
        = (fun z θ => z ^ 2 * Work.Spaces.pzIter 2
            (Work.FTS.EllipticEst.Cores.Dil.dq c f) z θ) y θ := by
    intro y hy
    exact (Work.FTS.EllipticEst.Cores.Dil.zsq_pzIter_two_dq hf hc y θ hy hθ).symm
  have h2 : Work.FTS.EllipticEst.Cores.Dil.dq c
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2
          (Work.FTS.EllipticEst.Cores.Dil.dq c f) z θ) z θ
      = Work.FTS.EllipticEst.Cores.Dil.dq c (Work.FTS.EllipticEst.Cores.Dil.dq c
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ)) z θ :=
    (Work.FTS.EllipticEst.Cores.Dil.dq_congr_of_pos (lt_trans zero_lt_one hc) hcongr hz).symm
  rw [h1, h2]

/-- `∂_θ²(dqq c f) = dqq c (∂_θ²f)` on the open quadrant. -/
theorem pthIter_two_dqq_eqOn {c : ℝ} {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hc : 1 < c) :
    ∀ (z θ : ℝ), 0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) →
      Work.Spaces.pthIter 2 (dqq c f) z θ
        = dqq c (Work.Spaces.pthIter 2 f) z θ := by
  intro z θ hz hθ
  have h1 : Work.Spaces.pthIter 2 (Work.FTS.EllipticEst.Cores.Dil.dq c
        (Work.FTS.EllipticEst.Cores.Dil.dq c f)) z θ
      = Work.FTS.EllipticEst.Cores.Dil.dq c
          (Work.Spaces.pthIter 2 (Work.FTS.EllipticEst.Cores.Dil.dq c f)) z θ :=
    Work.FTS.EllipticEst.Cores.Dil.pthIter_two_dq
      (Work.FTS.EllipticEst.Cores.Dil.smoothOpen_dq hf (lt_trans zero_lt_one hc)) hc z θ hz hθ
  have hcongr : ∀ y : ℝ, 0 < y →
      Work.FTS.EllipticEst.Cores.Dil.dq c (Work.Spaces.pthIter 2 f) y θ
        = Work.Spaces.pthIter 2 (Work.FTS.EllipticEst.Cores.Dil.dq c f) y θ := by
    intro y hy
    exact (Work.FTS.EllipticEst.Cores.Dil.pthIter_two_dq hf hc y θ hy hθ).symm
  have h2 : Work.FTS.EllipticEst.Cores.Dil.dq c
        (Work.Spaces.pthIter 2 (Work.FTS.EllipticEst.Cores.Dil.dq c f)) z θ
      = Work.FTS.EllipticEst.Cores.Dil.dq c
          (Work.FTS.EllipticEst.Cores.Dil.dq c (Work.Spaces.pthIter 2 f)) z θ :=
    (Work.FTS.EllipticEst.Cores.Dil.dq_congr_of_pos (lt_trans zero_lt_one hc) hcongr hz).symm
  rw [h1, h2]

/-- **The second radial derivative of `∂_θ²Ψ` is `∂_θ²(D_z²Ψ)`** on the open quadrant: the two
`D_z`'s commute with the two `θ`-derivatives. -/
theorem DzDz_pthIter_two_AgreeOnQ {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    ∀ (z θ : ℝ), 0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) →
      Work.Spaces.Dz (Work.Spaces.Dz (Work.Spaces.pthIter 2 Ψ)) z θ
        = Work.Spaces.pthIter 2 (Work.Spaces.DzIter 2 Ψ) z θ := by
  intro z θ hz hθ
  have hB : Work.Spaces.pthIter 2 Ψ = Work.Spaces.pthIter 2 Ψ := rfl
  have hev : (fun z' : ℝ => Work.Spaces.pthIter 2 (Work.Spaces.Dz Ψ) z' θ)
      =ᶠ[𝓝 z] (fun z' : ℝ => Work.Spaces.Dz (Work.Spaces.pthIter 2 Ψ) z' θ) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
    exact Work.FTS.EllipticEst.Cores.Dil.pthIter_two_Dz_AgreeOnQ hΨ z' θ hz' hθ.1 hθ.2
  have hderiv : deriv (fun z' : ℝ => Work.Spaces.Dz (Work.Spaces.pthIter 2 Ψ) z' θ) z
      = deriv (fun z' : ℝ => Work.Spaces.pthIter 2 (Work.Spaces.Dz Ψ) z' θ) z :=
    hev.deriv_eq.symm
  calc Work.Spaces.Dz (Work.Spaces.Dz (Work.Spaces.pthIter 2 Ψ)) z θ
      = z * deriv (fun z' : ℝ => Work.Spaces.Dz (Work.Spaces.pthIter 2 Ψ) z' θ) z := rfl
    _ = z * deriv (fun z' : ℝ => Work.Spaces.pthIter 2 (Work.Spaces.Dz Ψ) z' θ) z := by
        rw [hderiv]
    _ = Work.Spaces.Dz (Work.Spaces.pthIter 2 (Work.Spaces.Dz Ψ)) z θ := rfl
    _ = Work.Spaces.pthIter 2 (Work.Spaces.Dz (Work.Spaces.Dz Ψ)) z θ :=
        (Work.FTS.EllipticEst.Cores.Dil.pthIter_two_Dz_AgreeOnQ hΨ.Dz z θ hz hθ.1 hθ.2).symm
    _ = Work.Spaces.pthIter 2 (Work.Spaces.DzIter 2 Ψ) z θ := by
        rw [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero]

/-! ## The class membership of the second difference-quotient datum -/

/-- **The class membership of the second difference-quotient datum.**

For a datum `(F, Ψ)` of the weak class `EllWeakPos α 2` and `c > 1`, the pair
`(dqq c F, dqq c Ψ)` is again a datum of the weak class (at level `0`):

* the equation: `bslOp` commutes with `dq` (`Dil.bslOp_dq`), applied twice;
* the Dirichlet data: difference quotients of vanishing functions;
* the two angular moments: `Dil.Fstar_dqq_F_eq_zero`, `Dil.Fstar_dqq_Ψ_eq_zero` (validity of
  the moment conditions is inherited because `F_*` is linear in the function);
* the smoothness: `Dil.smoothOpen_dq`, applied twice;
* the three `ℋ⁰`-honesty clauses: from the honesty of `D_z²F`, `D_z²(z²∂_z²Ψ)`, `D_z²(∂_θ²Ψ)`
  by the iterated engine `HkMem_dqq`.

The slot identifications `z²∂_z²(dqq c Ψ) = dqq c (z²∂_z²Ψ)` and
`∂_θ²(dqq c Ψ) = dqq c (∂_θ²Ψ)` are `Dil.zsq_pzIter_two_dq` and `Dil.pthIter_two_dq`. -/
theorem EllWeakPos_dqq {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ)
    (hFmem : Work.Spaces.HkMem α 0 (Work.Spaces.Dz (Work.Spaces.Dz F)))
    (hAmem : Work.Spaces.HkMem α 0
      (Work.Spaces.Dz (Work.Spaces.Dz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))))
    (hBmem : Work.Spaces.HkMem α 0
      (Work.Spaces.Dz (Work.Spaces.Dz (Work.Spaces.pthIter 2 Ψ))))
    {c : ℝ} (hc : 1 < c)
    -- the diagonal second-order honesty for the *dilated* datum, in the exact form of the new
    -- conjunct of `EllWeakPos` (derivable from data smooth up to the closed quadrant, but not
    -- from the level-`0` clause of `h` by a `Dz`-shift, which needs level `1`)
    (hZmem : Work.Spaces.HkMem α 0
      (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 (dqq c Ψ)) z θ)) :
    Work.FTS.EllipticEst.TT.EllWeakPos α 0 (dqq c F) (dqq c Ψ) := by
  have hcpos : 0 < c := lt_trans zero_lt_one hc
  have hSΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hSF : Work.FTS.EllipticEst.SmoothOpen F :=
    Work.FTS.EllipticEst.Cores.Dil.smoothOpen_of_bslOp_eq hSΨ
      (fun z θ hz hθ hlt => h.eq z hz θ hθ hlt)
  have hSΨ1 : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.EllipticEst.Cores.Dil.dq c Ψ) :=
    Work.FTS.EllipticEst.Cores.Dil.smoothOpen_dq hSΨ hcpos
  have hAsm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
    Work.FTS.EllipticEst.Cores.Dil.smoothOpen_zsq_mul (hSΨ.pzIter 2)
  have hBsm : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 Ψ) := hSΨ.pth.pth
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the equation
    intro z hz θ hθ0 hθ1
    have hθ : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ0, hθ1⟩
    have e1 : Work.Elliptic.bslOp α (Work.FTS.EllipticEst.Cores.Dil.dq c Ψ) (c * z) θ
        = (Work.Elliptic.bslOp α Ψ (c * (c * z)) θ
            - Work.Elliptic.bslOp α Ψ (c * z) θ) / (c - 1) :=
      Work.FTS.EllipticEst.Cores.Dil.bslOp_dq α hSΨ hc (c * z) θ (by positivity) hθ
    have e2 : Work.Elliptic.bslOp α (Work.FTS.EllipticEst.Cores.Dil.dq c Ψ) z θ
        = (Work.Elliptic.bslOp α Ψ (c * z) θ - Work.Elliptic.bslOp α Ψ z θ) / (c - 1) :=
      Work.FTS.EllipticEst.Cores.Dil.bslOp_dq α hSΨ hc z θ hz hθ
    rw [Work.FTS.EllipticEst.Cores.Dil.bslOp_dq α hSΨ1 hc z θ hz hθ, e1, e2,
      h.eq (c * (c * z)) (by positivity) θ hθ0 hθ1,
      h.eq (c * z) (by positivity) θ hθ0 hθ1, h.eq z hz θ hθ0 hθ1]
    simp only [dqq, Work.FTS.EllipticEst.Cores.Dil.dq_apply]
  · -- Dirichlet data at `θ = 0`
    intro z
    simp only [dqq, Work.FTS.EllipticEst.Cores.Dil.dq_apply, h.zero, sub_self, zero_div]
  · -- Dirichlet data at `θ = π/2`
    intro z
    simp only [dqq, Work.FTS.EllipticEst.Cores.Dil.dq_apply, h.pi_half, sub_self, zero_div]
  · -- the source moment
    exact Work.FTS.EllipticEst.Cores.Dil.Fstar_dqq_F_eq_zero h hc
  · -- the solution moment
    exact Work.FTS.EllipticEst.Cores.Dil.Fstar_dqq_Ψ_eq_zero h hc
  · -- smoothness on the open quadrant
    intro n
    exact (Work.FTS.EllipticEst.smoothOpen_iff_forall (dqq c Ψ)).mp
      (Work.FTS.EllipticEst.Cores.Dil.smoothOpen_dq hSΨ1 hcpos) n
  · -- `ℋ⁰`-honesty of the source
    exact HkMem_dqq hSF hSF.Dz hFmem hc
  · -- `ℋ⁰`-honesty of `z²∂_z²(dqq c Ψ)`
    have hbase : Work.Spaces.HkMem α 0
        (dqq c (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) :=
      HkMem_dqq hAsm hAsm.Dz hAmem hc
    refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 0 hbase ?_
    intro z hz θ hθ
    exact (zsq_pzIter_two_dqq_eqOn hSΨ hc z θ hz hθ).symm
  · -- `ℋ⁰`-honesty of `∂_θ²(dqq c Ψ)`
    have hbase : Work.Spaces.HkMem α 0 (dqq c (Work.Spaces.pthIter 2 Ψ)) :=
      HkMem_dqq hBsm hBsm.Dz hBmem hc
    refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 0 hbase ?_
    intro z hz θ hθ
    exact (pthIter_two_dqq_eqOn hSΨ hc z θ hz hθ).symm
  · -- the diagonal second-order honesty of the dilated datum (assumed)
    exact hZmem

end Work.FTS.EllipticEst.Cores.pPureShiftAux
