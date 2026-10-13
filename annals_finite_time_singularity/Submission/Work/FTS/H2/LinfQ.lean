import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.H2.Defs
import Submission.Work.FTS.H2.Qd
import Submission.Work.FTS.H2.RegQDefs
import Submission.Work.FTS.H2.SupMixedLeH4
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.DzDthIterCommOn
import Submission.Work.Spaces.integrable_prod_of_iterated
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd
import Submission.Work.Spaces.HardyZ
import Submission.Work.Spaces.sin_two_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2

set_option autoImplicit false
set_option maxHeartbeats 4000000

open Work.Spaces
open Work.FTS.LocData (SmoothQuad)

/-! ## The open quadrant `(0,∞) × (0,π/2)`

Everything in this file happens on the open quadrant: `supAbsO` is the supremum over it, the
regularity class `RegQ` only constrains the function there, and the weights are continuous
there.  The complement of the open quadrant inside `Iz ×ˢ Iθ` is null for the product of the
restricted Lebesgue measures, which is what makes `aesm_of_continuousOn_Qd` applicable. -/

lemma sin_two_pos_of_mem_Ioo {θ : ℝ} (h : θ ∈ Set.Ioo 0 (π / 2)) : 0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [h.1]) (by linarith [h.2, Real.pi_pos])

lemma one_le_w_sq {z : ℝ} (hz : 0 < z) : 1 ≤ (w z) ^ 2 := by
  have h1 : (1 : ℝ) ≤ w z := by
    rw [w, le_div_iff₀ (by positivity : (0 : ℝ) < z ^ 2)]
    nlinarith
  calc (1 : ℝ) = 1 ^ 2 := by ring
    _ ≤ (w z) ^ 2 := pow_le_pow_left₀ (by norm_num) h1 2

/-- `Wt α z θ² = w(z)² sin(2θ)^{-γ}` on the open quadrant (no hypothesis on `α`: the base
`sin(2θ)` is positive there). -/
lemma Wt_sq_Ioo (α z θ : ℝ) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    (w z * (Real.sin (2 * θ)) ^ (-(gam α / 2))) ^ 2
      = (w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α)) := by
  have hs : 0 < Real.sin (2 * θ) := sin_two_pos_of_mem_Ioo hθ
  have hstep : ((Real.sin (2 * θ)) ^ (-(gam α / 2))) ^ 2
      = (Real.sin (2 * θ)) ^ (-(gam α)) := by
    rw [pow_two, ← Real.rpow_add hs]
    congr 1
    ring
  rw [mul_pow, hstep]


/-! ## Almost everywhere strong measurability and integrability of a mixed slot -/

/-- The weighted square of a mixed `D`-derivative of a `SmoothQuad` function is almost
everywhere strongly measurable for the product of the restricted Lebesgue measures: it is
*continuous* on the open quadrant, whose complement in `Iz ×ˢ Iθ` is null. -/
theorem aesm_mixed_Wt_sq_prod_quad (α : ℝ) (f : ℝ → ℝ → ℝ) (hf : SmoothQuad f) (j i : ℕ) :
    AEStronglyMeasurable
      (fun p : ℝ × ℝ => (mixed j i f p.1 p.2 * Wt α p.1 p.2) ^ 2)
      ((volume.restrict Iz).prod (volume.restrict Iθ)) :=
  aesm_of_continuousOn_Qd _
    ((((Work.FTS.LocData.contDiffOn_mixed Work.Spaces.isOpen_quadU hf j i).continuousOn.mono
        Qd_subset_quadU).mul (continuousOn_Wt_Qd α)).pow 2)

/-- The `θ`-slice measurability of a mixed slot at a fixed `z > 0`. -/
theorem aesm_slice_mixed_Wt_sq (α : ℝ) (f : ℝ → ℝ → ℝ) (hf : SmoothQuad f) (j i : ℕ)
    {z : ℝ} (hz : 0 < z) :
    AEStronglyMeasurable (fun θ => (mixed j i f z θ * Wt α z θ) ^ 2)
      (volume.restrict Iθ) :=
  aesm_slice_of_continuousOn_Qd _
    ((((Work.FTS.LocData.contDiffOn_mixed Work.Spaces.isOpen_quadU hf j i).continuousOn.mono
        Qd_subset_quadU).mul (continuousOn_Wt_Qd α)).pow 2) hz

/-- The a.e. domination of a mixed slot by the `ℋ⁴`-integrand, in the norm form required by
`Integrable.mono'`. -/
lemma slot_norm_le_HkIntegrand (α : ℝ) (f : ℝ → ℝ → ℝ) (j i : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 4)
    (z θ : ℝ) :
    ‖(mixed j i f z θ * Wt α z θ) ^ 2‖ ≤ HkIntegrand α 4 f z θ := by
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact sq_le_HkIntegrand_mixed α 4 f z θ i j hi hij

/-- The `θ`-slice of the weighted mixed slot is integrable on `Iθ`, for every `z ∈ Iz`, by
domination by the corresponding summand of `HkIntegrand α 4 f`. -/
theorem integrableOn_slice_mixed_Wt_sq (α : ℝ) (f : ℝ → ℝ → ℝ) (hf : SmoothQuad f)
    (hmem : HkMem α 4 f) (j i : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 4) {z : ℝ} (hz : z ∈ Iz) :
    IntegrableOn (fun θ => (mixed j i f z θ * Wt α z θ) ^ 2) Iθ := by
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · subst hz0
    have hzero : (fun θ => (mixed j i f 0 θ * Wt α 0 θ) ^ 2) = fun _ => (0 : ℝ) := by
      funext θ
      simp [Wt, w]
    rw [hzero]
    exact integrableOn_zero
  · refine MeasureTheory.Integrable.mono' (hmem.1 z hz)
      (aesm_slice_mixed_Wt_sq α f hf j i hzpos) ?_
    filter_upwards [ae_restrict_mem (show MeasurableSet Iθ from measurableSet_Icc)] with θ hθ
    exact slot_norm_le_HkIntegrand α f j i hi hij z θ

/-- **The mixed slot of the `ℋ⁴` norm, in the `θ`-first order.**  For a `SmoothQuad` function
`f` of class `ℋ⁴` and a mixed slot `1 ≤ i`, `i + j ≤ 4`:

* the `θ`-first iterated integral of `(D_z^jD_θ^i f · W)²` is bounded by the squared `ℋ⁴` norm;
* it is integrable in `θ`;
* for almost every `θ` the unweighted `z`-slice `(D_z^jD_θ^i f)² w²` is integrable on `Iz` (this
  is the integrability input of the radial Hardy inequality). -/
theorem slotM_quad (α : ℝ) (f : ℝ → ℝ → ℝ) (hf : SmoothQuad f) (hmem : HkMem α 4 f)
    (j i : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 4) :
    (∫ θ in Iθ, ∫ z in Iz, (mixed j i f z θ * Wt α z θ) ^ 2) ≤ HkSq α 4 f
    ∧ IntegrableOn (fun θ => ∫ z in Iz, (mixed j i f z θ * Wt α z θ) ^ 2) Iθ
    ∧ (∀ᵐ θ ∂(volume.restrict Iθ),
        IntegrableOn (fun z => (mixed j i f z θ) ^ 2 * (w z) ^ 2) Iz) := by
  have hnn : ∀ z θ : ℝ, 0 ≤ (mixed j i f z θ * Wt α z θ) ^ 2 := fun z θ => sq_nonneg _
  have hAE := aesm_mixed_Wt_sq_prod_quad α f hf j i
  have hslice : ∀ᵐ z ∂(volume.restrict Iz),
      Integrable (fun θ => (mixed j i f z θ * Wt α z θ) ^ 2) (volume.restrict Iθ) := by
    filter_upwards [hAE.prodMk_left,
      ae_restrict_mem (show MeasurableSet Iz from measurableSet_Ici)] with z hz_meas hz
    refine MeasureTheory.Integrable.mono' (hmem.1 z hz) hz_meas ?_
    filter_upwards [ae_restrict_mem (show MeasurableSet Iθ from measurableSet_Icc)] with θ hθ
    exact slot_norm_le_HkIntegrand α f j i hi hij z θ
  have houter : Integrable
      (fun z => ∫ θ, (mixed j i f z θ * Wt α z θ) ^ 2 ∂(volume.restrict Iθ))
      (volume.restrict Iz) := by
    refine MeasureTheory.Integrable.mono' hmem.2 hAE.integral_prod_right' ?_
    filter_upwards [ae_restrict_mem (show MeasurableSet Iz from measurableSet_Ici)] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun θ => sq_nonneg _)]
    exact integral_mono_of_nonneg
      (ae_restrict_of_forall_mem (show MeasurableSet Iθ from measurableSet_Icc)
        (fun θ _ => sq_nonneg _))
      (hmem.1 z hz)
      (ae_restrict_of_forall_mem (show MeasurableSet Iθ from measurableSet_Icc)
        (fun θ _ => sq_le_HkIntegrand_mixed α 4 f z θ i j hi hij))
  obtain ⟨hint, hval⟩ := integrable_prod_of_iterated hnn hAE hslice houter
  have hswap := MeasureTheory.integral_integral_swap hint
  have hL2 : (∫ z in Iz, ∫ θ in Iθ, (mixed j i f z θ * Wt α z θ) ^ 2) ≤ HkSq α 4 f := by
    simpa only [L2Sq] using L2Sq_mixed_le_HkSq α 4 f hmem i j hi hij
  refine ⟨?_, ?_, ?_⟩
  · rw [← hswap]
    exact hL2
  · exact hint.integral_prod_right
  · have haeeq : Set.Ioo (0 : ℝ) (π / 2) =ᵐ[volume] Iθ := MeasureTheory.Ioo_ae_eq_Icc
    have hIoo : volume.restrict Iθ = volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) :=
      Measure.restrict_congr_set haeeq.symm
    rw [hIoo] at hint ⊢
    filter_upwards [hint.prod_left_ae, ae_restrict_mem measurableSet_Ioo] with θ hsliceθ hθmem
    have hθI : θ ∈ Iθ := ⟨le_of_lt hθmem.1, le_of_lt hθmem.2⟩
    have hsin : 0 < Real.sin (2 * θ) := sin_two_pos_of_mem_Ioo hθmem
    have hmul : (Real.sin (2 * θ)) ^ gam α * (Real.sin (2 * θ)) ^ (-(gam α)) = 1 := by
      rw [← Real.rpow_add hsin, show gam α + -(gam α) = 0 by ring, Real.rpow_zero]
    have hEq : (fun z => (mixed j i f z θ) ^ 2 * (w z) ^ 2)
        = fun z => (Real.sin (2 * θ)) ^ gam α
            * (mixed j i f z θ * Wt α z θ) ^ 2 := by
      funext z
      have h1 : (mixed j i f z θ * Wt α z θ) ^ 2
          = (mixed j i f z θ) ^ 2 * ((w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α))) := by
        rw [show Wt α z θ = w z * (Real.sin (2 * θ)) ^ (-(gam α / 2)) from rfl, mul_pow,
          Wt_sq_Ioo α z θ hθmem]
      rw [h1]
      rw [show (Real.sin (2 * θ)) ^ gam α
            * ((mixed j i f z θ) ^ 2 * ((w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α))))
          = ((mixed j i f z θ) ^ 2 * (w z) ^ 2)
              * ((Real.sin (2 * θ)) ^ gam α * (Real.sin (2 * θ)) ^ (-(gam α))) by ring]
      rw [hmul, mul_one]
    rw [hEq]
    exact hsliceθ.const_mul _

/-! ## The iterated `D`-operators commute on the open quadrant -/

/-- On an open set on which `g` is `C^∞` (in the *genuine* smooth order `smoothOrder`, not the
analytic order), `D_z` commutes with every iterate of `D_θ`. -/
theorem DzDthIterCommOn_quad {g : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hg : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry g) V) (i : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.Dz (Work.Spaces.DthIter i g)))
      (Function.uncurry (Work.Spaces.DthIter i (Work.Spaces.Dz g))) V := by
  induction i with
  | zero => intro y hy; rfl
  | succ i ih =>
      intro y hy
      have hGi : ContDiffOn ℝ Work.Stability.smoothOrder
          (Function.uncurry (Work.Spaces.DthIter i g)) V :=
        Work.FTS.LocData.contDiffOn_DthIter hV hg i
      have hF : ContDiffAt ℝ 2 (Function.uncurry (Work.Spaces.DthIter i g)) y :=
        (hGi.contDiffAt (hV.mem_nhds hy)).of_le (by simp [Work.Stability.smoothOrder])
      have hcomm : Work.Spaces.Dz (Work.Spaces.Dth (Work.Spaces.DthIter i g)) y.1 y.2
          = Work.Spaces.Dth (Work.Spaces.Dz (Work.Spaces.DthIter i g)) y.1 y.2 :=
        Work.Spaces.Dz_Dth_comm (f := Work.Spaces.DthIter i g) hF
      show Work.Spaces.Dz (Work.Spaces.Dth (Work.Spaces.DthIter i g)) y.1 y.2
          = Work.Spaces.Dth (Work.Spaces.DthIter i (Work.Spaces.Dz g)) y.1 y.2
      rw [hcomm]
      show Real.sin (2 * y.2)
            * Work.Spaces.pth (Work.Spaces.Dz (Work.Spaces.DthIter i g)) y.1 y.2
          = Real.sin (2 * y.2)
              * Work.Spaces.pth (Work.Spaces.DthIter i (Work.Spaces.Dz g)) y.1 y.2
      rw [Work.Spaces.pth_congr_of_isOpen hV ih hy]

/-- On an open set on which `g` is `C^∞`, `D_z^b` commutes with `D_θ^a`. -/
theorem DzIter_DthIter_comm_quad {g : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hg : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry g) V) (b a : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DzIter b (Work.Spaces.DthIter a g)))
      (Function.uncurry (Work.Spaces.DthIter a (Work.Spaces.DzIter b g))) V := by
  induction b with
  | zero => intro p hp; rfl
  | succ b ih =>
      intro p hp
      have hstep : Work.Spaces.Dz (Work.Spaces.DthIter a (Work.Spaces.DzIter b g)) p.1 p.2
          = Work.Spaces.DthIter a (Work.Spaces.Dz (Work.Spaces.DzIter b g)) p.1 p.2 :=
        DzDthIterCommOn_quad hV (Work.FTS.LocData.contDiffOn_DzIter hV hg b) a hp
      have hpz : Work.Spaces.pz (Work.Spaces.DzIter b (Work.Spaces.DthIter a g)) p.1 p.2
          = Work.Spaces.pz (Work.Spaces.DthIter a (Work.Spaces.DzIter b g)) p.1 p.2 :=
        Work.Spaces.pz_congr_of_isOpen hV ih hp
      show p.1 * Work.Spaces.pz (Work.Spaces.DzIter b (Work.Spaces.DthIter a g)) p.1 p.2
          = Work.Spaces.DthIter a (Work.Spaces.Dz (Work.Spaces.DzIter b g)) p.1 p.2
      rw [hpz]
      show Work.Spaces.Dz (Work.Spaces.DthIter a (Work.Spaces.DzIter b g)) p.1 p.2
          = Work.Spaces.DthIter a (Work.Spaces.Dz (Work.Spaces.DzIter b g)) p.1 p.2
      exact hstep

/-- The key consequence: `D_θ` of `D_z^b D_θ^a f` is `D_z^b D_θ^{a+1} f` on the open
quadrant, for a `SmoothQuad` function. -/
theorem Dth_mixed_quad {f : ℝ → ℝ → ℝ} (hf : SmoothQuad f) (b a : ℕ) {z θ : ℝ}
    (hz : z ∈ Set.Ioi (0 : ℝ)) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.Spaces.Dth (mixed b a f) z θ = mixed b (a + 1) f z θ := by
  have hquad : (z, θ) ∈ Work.Spaces.quadU := by
    refine ⟨?_, hθ⟩
    exact Set.mem_Ioi.mpr (by linarith [Set.mem_Ioi.mp hz])
  have h1 : Function.uncurry
      (Work.Spaces.DzIter b (Work.Spaces.DthIter 1 (Work.Spaces.DthIter a f))) (z, θ)
      = Function.uncurry
        (Work.Spaces.DthIter 1 (Work.Spaces.DzIter b (Work.Spaces.DthIter a f))) (z, θ) :=
    (DzIter_DthIter_comm_quad Work.Spaces.isOpen_quadU
      (Work.FTS.LocData.contDiffOn_DthIter Work.Spaces.isOpen_quadU hf a) b 1) hquad
  simpa only [Function.uncurry, mixed, DthIter_succ, DthIter_zero] using h1.symm

/-- `D_z` of a mixed derivative is the next mixed derivative (definitional). -/
theorem Dz_mixed_quad (b a : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.Dz (mixed b a f) z θ = mixed (b + 1) a f z θ := rfl

/-! ## The two Hardy inequalities in the interior form

`RegQ` only gives smoothness inside the open quadrant and one-sided limits at the boundary, so
the Hardy inequalities of `Work.Spaces.HardyTheta`/`HardyZ` (which are phrased for `SmoothNbhd`,
i.e. for smoothness on a neighbourhood of the *closed* quadrant) cannot be applied directly.
Both are re-proved here in the interior form: the angular one from the fundamental theorem on
`[ε,θ]` followed by `ε → 0⁺` (the boundary value is the limit from the right), the radial one
from the fundamental theorem on `[z,B]` followed by `B → ∞` (the boundary value is the limit at
infinity). -/

/-- Monotonicity of the interval integral against the set integral over `Iθ`. -/
lemma interval_integral_le_setIntegral_Iθ {F : ℝ → ℝ} {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hb : b < π / 2) (hint : IntegrableOn F Iθ) (hnn : ∀ x ∈ Iθ, 0 ≤ F x) :
    (∫ x in a..b, F x) ≤ ∫ x in Iθ, F x := by
  rw [intervalIntegral.integral_of_le hab]
  refine setIntegral_mono_set hint (ae_restrict_of_forall_mem measurableSet_Icc hnn) ?_
  exact Eventually.of_forall fun x hx =>
    ⟨le_of_lt (lt_trans ha hx.1), le_of_lt (lt_of_le_of_lt hx.2 hb)⟩

/-- **The angular Hardy inequality in the interior form.**  For a `SmoothQuad` function `g`
whose `θ`-slice at fixed `z > -1` is smooth on `(0,π/2)`, tends to `0` at `θ = 0⁺` and has
`(∂_θ g)² sin(2θ)^{2-γ}` integrable,

  `g(z,θ)² ≤ (100/(γ-1)) ∫_Iθ (∂_θ g(z,σ))² sin(2σ)^{2-γ}`   for `0 < θ < π/2`.

The boundary value at `0` is used only through the limit hypothesis `h0`. -/
theorem HardyThetaO (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (g : ℝ → ℝ → ℝ) (z : ℝ)
    (hg : SmoothQuad g) (hz : z ∈ Set.Ioi (-1))
    (h0 : Tendsto (fun θ => g z θ) (𝓝[>] 0) (𝓝 0))
    (hint : IntegrableOn (fun σ => (pth g z σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - gam α)) Iθ) :
    ∀ θ ∈ Set.Ioo 0 (π / 2), (g z θ) ^ 2 ≤
      (100 / (gam α - 1)) * ∫ σ in Iθ, (pth g z σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - gam α) := by
  have hγ1 : 0 < gam α - 1 := by rw [gam_sub_one]; linarith
  have hp1 : -1 < gam α - 2 := by rw [gam]; linarith
  have hp0 : gam α - 2 ≤ 0 := by rw [gam]; linarith
  have hne0 : Work.Stability.smoothOrder ≠ 0 := by simp [Work.Stability.smoothOrder]
  have hslice : ContDiffOn ℝ Work.Stability.smoothOrder (fun θ' => g z θ') (Set.Ioo 0 (π / 2)) :=
    hg.curry_θ hz
  have hdth : ContDiffOn ℝ Work.Stability.smoothOrder (fun θ' => pth g z θ')
      (Set.Ioo 0 (π / 2)) :=
    Work.FTS.LocData.contDiffOn_slice_θ
      (Work.FTS.LocData.contDiffOn_pth Work.Spaces.isOpen_quadU hg) hz
  intro θ hθ
  have hθ0 : 0 < θ := hθ.1
  have hθ1 : θ < π / 2 := hθ.2
  set A : ℝ := ∫ σ in Iθ, (pth g z σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - gam α) with hAdef
  have hAnn : 0 ≤ A := by
    rw [hAdef]
    exact setIntegral_nonneg measurableSet_Icc fun σ hσ =>
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg hσ) _)
  have hKnn : 0 ≤ 100 / (gam α - 1) := div_nonneg (by norm_num) hγ1.le
  -- the bound at every `ε ∈ (0,θ)`
  have hkey : ∀ ε ∈ Set.Ioo 0 θ, (g z θ - g z ε) ^ 2 ≤ (100 / (gam α - 1)) * A := by
    intro ε hε
    have hεθ : ε ≤ θ := le_of_lt hε.2
    have hsub : Set.uIcc ε θ ⊆ Set.Ioo (0 : ℝ) (π / 2) := by
      intro x hx
      rw [Set.uIcc_of_le hεθ] at hx
      exact ⟨lt_of_lt_of_le hε.1 hx.1, lt_of_le_of_lt hx.2 hθ1⟩
    have hsubI : Set.Icc ε θ ⊆ Set.Ioo (0 : ℝ) (π / 2) := by
      rw [← Set.uIcc_of_le hεθ]; exact hsub
    have hcontθ : ContinuousOn (fun θ' => g z θ') (Set.Icc ε θ) :=
      hslice.continuousOn.mono hsubI
    have hpthcont : ContinuousOn (fun s => pth g z s) (Set.uIcc ε θ) :=
      hdth.continuousOn.mono hsub
    have hderiv : ∀ x ∈ Set.Ioo ε θ, HasDerivAt (fun θ' => g z θ') (pth g z x) x := by
      intro x hx
      have hx' : x ∈ Set.Ioo (0 : ℝ) (π / 2) :=
        ⟨lt_trans hε.1 hx.1, lt_of_lt_of_le hx.2 hθ1.le⟩
      exact ((hslice.differentiableOn hne0).differentiableAt
        (isOpen_Ioo.mem_nhds hx')).hasDerivAt
    have hintε : IntervalIntegrable (fun s => pth g z s) volume ε θ := hpthcont.intervalIntegrable
    have hFTC : ∫ s in ε..θ, pth g z s = g z θ - g z ε :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hεθ hcontθ hderiv hintε
    have hsincont : ∀ c : ℝ,
        ContinuousOn (fun s : ℝ => (Real.sin (2 * s)) ^ c) (Set.uIcc ε θ) := fun c =>
      ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn).rpow_const
        (fun s hs => Or.inl (ne_of_gt (sin_two_pos_of_mem_Ioo (hsub hs))))
    have hcs := hardyZ_interval_integral_mul_le_sqrt ε θ hεθ
      (hpthcont.mul (hsincont ((2 - gam α) / 2))) (hsincont ((gam α - 2) / 2))
    have hcongr : ∫ s in ε..θ,
          (pth g z s * (Real.sin (2 * s)) ^ ((2 - gam α) / 2))
            * (Real.sin (2 * s)) ^ ((gam α - 2) / 2)
        = ∫ s in ε..θ, pth g z s := by
      refine intervalIntegral.integral_congr fun s hs => ?_
      have hs' := hsub hs
      have hsin : 0 < Real.sin (2 * s) := sin_two_pos_of_mem_Ioo hs'
      have h1 : (Real.sin (2 * s)) ^ ((2 - gam α) / 2)
          * (Real.sin (2 * s)) ^ ((gam α - 2) / 2) = 1 := by
        rw [← Real.rpow_add hsin, show (2 - gam α) / 2 + (gam α - 2) / 2 = 0 by ring,
          Real.rpow_zero]
      rw [mul_assoc, h1, mul_one]
    have hAint : ∫ s in ε..θ, (pth g z s * (Real.sin (2 * s)) ^ ((2 - gam α) / 2)) ^ 2 ≤ A := by
      have hEq : ∫ s in ε..θ, (pth g z s * (Real.sin (2 * s)) ^ ((2 - gam α) / 2)) ^ 2
          = ∫ s in ε..θ, (pth g z s) ^ 2 * (Real.sin (2 * s)) ^ (2 - gam α) := by
        refine intervalIntegral.integral_congr fun s hs => ?_
        have hs' := hsub hs
        have h1 : ((Real.sin (2 * s)) ^ ((2 - gam α) / 2)) ^ 2
            = (Real.sin (2 * s)) ^ (2 - gam α) := by
          rw [pow_two, ← Real.rpow_add (sin_two_pos_of_mem_Ioo hs')]
          congr 1
          ring
        rw [mul_pow, h1]
      rw [hEq, hAdef]
      exact interval_integral_le_setIntegral_Iθ hε.1 hεθ hθ1 hint fun x hx =>
        mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg hx) _)
    have hBint : ∫ s in ε..θ, ((Real.sin (2 * s)) ^ ((gam α - 2) / 2)) ^ 2
        ≤ 100 / (gam α - 1) := by
      have hEq : ∫ s in ε..θ, ((Real.sin (2 * s)) ^ ((gam α - 2) / 2)) ^ 2
          = ∫ s in ε..θ, (Real.sin (2 * s)) ^ (gam α - 2) := by
        refine intervalIntegral.integral_congr fun s hs => ?_
        rw [pow_two, ← Real.rpow_add (sin_two_pos_of_mem_Ioo (hsub hs))]
        congr 1
        ring
      rw [hEq]
      refine le_trans (interval_integral_le_setIntegral_Iθ hε.1 hεθ hθ1
        (sin_two_rpow (gam α - 2) hp1 hp0).1
        (fun x hx => Real.rpow_nonneg (sin_two_nonneg hx) _)) ?_
      have h2 := (sin_two_rpow (gam α - 2) hp1 hp0).2
      rwa [show (gam α - 2) + 1 = gam α - 1 by ring] at h2
    have hstep : |g z θ - g z ε| ≤ Real.sqrt A * Real.sqrt (100 / (gam α - 1)) := by
      rw [← hFTC, ← hcongr]
      exact le_trans hcs (mul_le_mul (Real.sqrt_le_sqrt hAint) (Real.sqrt_le_sqrt hBint)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    have hsq : (g z θ - g z ε) ^ 2
        ≤ (Real.sqrt A * Real.sqrt (100 / (gam α - 1))) ^ 2 :=
      sq_le_sq' (by linarith [neg_abs_le (g z θ - g z ε), hstep])
        (le_trans (le_abs_self _) hstep)
    calc (g z θ - g z ε) ^ 2
        ≤ (Real.sqrt A * Real.sqrt (100 / (gam α - 1))) ^ 2 := hsq
      _ = A * (100 / (gam α - 1)) := by rw [mul_pow, Real.sq_sqrt hAnn, Real.sq_sqrt hKnn]
      _ = (100 / (gam α - 1)) * A := by ring
  -- pass to the limit `ε → 0⁺`
  have hlim : Tendsto (fun ε => (g z θ - g z ε) ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 ((g z θ) ^ 2)) := by
    have h1 : Tendsto (fun ε => g z θ - g z ε) (𝓝[>] (0 : ℝ)) (𝓝 (g z θ - 0)) :=
      tendsto_const_nhds.sub h0
    simpa using h1.pow 2
  refine le_of_tendsto hlim ?_
  rw [eventually_nhdsWithin_iff]
  filter_upwards [isOpen_Iio.mem_nhds hθ0] with ε hε hε0
  exact hkey ε ⟨hε0, hε⟩

/-- The algebraic identity behind the weighted Cauchy–Schwarz step of the *radial* Hardy
inequality: `(z v' w(z)) · (z/(1+z)²) = v'` for `z > 0`. -/
lemma mul_w_mul_psi_eq (v : ℝ → ℝ) {s : ℝ} (hs : 0 < s) :
    (s * deriv v s * w s) * (s / (1 + s) ^ 2) = deriv v s := by
  have h1 : (1 + s) ≠ 0 := ne_of_gt (by linarith)
  simp only [w]
  field_simp

/-- **The radial Hardy inequality in the interior form.**  For a function `v` of class `C¹` on
`(0,∞)` with `v → 0` at `+∞` and `(z v')² w(z)²` integrable on `[0,∞)`,

  `v(z)² ≤ ∫_0^∞ (s v'(s))² w(s)² ds`   for `z > 0`. -/
theorem hardyZ_open {v : ℝ → ℝ} (hcd : ContDiffOn ℝ 1 v (Set.Ioi (0 : ℝ)))
    (hdec : Tendsto v atTop (𝓝 0))
    (hint : IntegrableOn (fun s => (s * deriv v s) ^ 2 * (w s) ^ 2) Iz) :
    ∀ z ∈ Set.Ioi (0 : ℝ), (v z) ^ 2 ≤ ∫ s in Iz, (s * deriv v s) ^ 2 * (w s) ^ 2 := by
  set P : ℝ := ∫ s in Iz, (s * deriv v s) ^ 2 * (w s) ^ 2 with hPdef
  have hPnn : 0 ≤ P := integral_nonneg fun s => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hderivcont : ContinuousOn (deriv v) (Set.Ioi (0 : ℝ)) := by
    have h := hcd.continuousOn_derivWithin isOpen_Ioi.uniqueDiffOn le_rfl
    exact h.congr fun x hx => (derivWithin_of_isOpen isOpen_Ioi hx).symm
  intro z hz
  have hz0 : 0 < z := hz
  have hkey : ∀ B, z ≤ B → |v z| ≤ |v B| + Real.sqrt P := by
    intro B hzB
    have hcont : ContinuousOn v (Set.Icc z B) :=
      hcd.continuousOn.mono fun x hx => lt_of_lt_of_le hz0 hx.1
    have hderiv : ∀ x ∈ Set.Ioo z B, HasDerivAt v (deriv v x) x := by
      intro x hx
      exact ((hcd.differentiableOn (by norm_num)).differentiableAt
        (isOpen_Ioi.mem_nhds (lt_of_lt_of_le hz0 hx.1.le))).hasDerivAt
    have hderivIcc : ContinuousOn (deriv v) (Set.Icc z B) :=
      hderivcont.mono fun x hx => lt_of_lt_of_le hz0 hx.1
    have hcontU : ContinuousOn (deriv v) (Set.uIcc z B) := by
      rw [Set.uIcc_of_le hzB]
      exact hderivIcc
    have hintB : IntervalIntegrable (deriv v) volume z B := hcontU.intervalIntegrable
    have hFTC : ∫ s in z..B, deriv v s = v B - v z :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hzB hcont hderiv hintB
    have hcontA : ContinuousOn (fun s => s * deriv v s * w s) (Set.uIcc z B) := by
      rw [Set.uIcc_of_le hzB]
      have h1 : ContinuousOn (fun s : ℝ => s * deriv v s) (Set.Icc z B) :=
        continuousOn_id.mul (hderivIcc)
      have h2 : ContinuousOn w (Set.Icc z B) := by
        unfold w
        refine ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
          (continuousOn_id.pow 2) fun x hx => pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le hz0 hx.1))
      exact h1.mul h2
    have hcontψ : ContinuousOn (fun s : ℝ => s / (1 + s) ^ 2) (Set.uIcc z B) := by
      rw [Set.uIcc_of_le hzB]
      refine ContinuousOn.div continuousOn_id ((continuousOn_const.add continuousOn_id).pow 2)
        fun x hx => pow_ne_zero 2 (ne_of_gt (by linarith [lt_of_lt_of_le hz0 hx.1]))
    have hcs := hardyZ_interval_integral_mul_le_sqrt z B hzB hcontA hcontψ
    have hcongr : ∫ x in z..B, (x * deriv v x * w x) * (x / (1 + x) ^ 2)
        = ∫ x in z..B, deriv v x := by
      refine intervalIntegral.integral_congr fun x hx => ?_
      rw [Set.uIcc_of_le hzB] at hx
      exact mul_w_mul_psi_eq v (lt_of_lt_of_le hz0 hx.1)
    have hA2le : ∫ x in z..B, (x * deriv v x * w x) ^ 2 ≤ P := by
      have h1 : ∫ x in z..B, (x * deriv v x * w x) ^ 2
          = ∫ x in z..B, (x * deriv v x) ^ 2 * (w x) ^ 2 := by
        refine intervalIntegral.integral_congr fun x _ => by ring
      rw [h1, hPdef]
      exact hardyZ_integral_Ioc_le_integral_Iz hz0.le hzB hint
        fun s _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)
    have hψle : ∫ x in z..B, (x / (1 + x) ^ 2) ^ 2 ≤ 1 :=
      hardyZ_integral_psi_sq_le_one hz0.le hzB
    have hchain : |∫ x in z..B, deriv v x| ≤ Real.sqrt P := by
      rw [← hcongr]
      calc |∫ x in z..B, (x * deriv v x * w x) * (x / (1 + x) ^ 2)|
          ≤ Real.sqrt (∫ x in z..B, (x * deriv v x * w x) ^ 2)
              * Real.sqrt (∫ x in z..B, (x / (1 + x) ^ 2) ^ 2) := hcs
        _ ≤ Real.sqrt P * Real.sqrt 1 :=
            mul_le_mul (Real.sqrt_le_sqrt hA2le) (Real.sqrt_le_sqrt hψle)
              (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
        _ = Real.sqrt P := by rw [Real.sqrt_one, mul_one]
    have hchain' : |v B - v z| ≤ Real.sqrt P := by
      rw [← hFTC]
      exact hchain
    have hsplit : v z = v B - (v B - v z) := by ring
    calc |v z| = |v B - (v B - v z)| := congrArg abs hsplit
      _ ≤ |v B| + |v B - v z| := abs_sub _ _
      _ ≤ |v B| + Real.sqrt P := by linarith [hchain']
  have hlim : Tendsto (fun B => |v B| + Real.sqrt P) atTop (𝓝 (Real.sqrt P)) := by
    simpa using hdec.abs.add_const (Real.sqrt P)
  have hev : ∀ᶠ B in atTop, |v z| ≤ |v B| + Real.sqrt P :=
    (eventually_ge_atTop z).mono fun B hB => hkey B hB
  have hle : |v z| ≤ Real.sqrt P := ge_of_tendsto hlim hev
  calc (v z) ^ 2 = |v z| ^ 2 := (sq_abs _).symm
    _ ≤ (Real.sqrt P) ^ 2 := by nlinarith [hle, abs_nonneg (v z), Real.sqrt_nonneg P]
    _ = P := Real.sq_sqrt hPnn

/-! ## The boundary limits supplied by `BdryTraces`

`BdryTraces` records, for each mixed derivative, the two limits
`z·(D_z^jD_θ^i f·w)² → 0` (as `z → 0⁺` and as `z → ∞`) and
`sin(2θ)^{1-γ}·(D_z^jD_θ^i f)² → 0` (as `θ → 0⁺` and as `θ → (π/2)⁻`).  The two lemmas below
turn the second clauses into the *vanishing of the derivative itself* at the boundary, which is
what the Hardy inequalities need: `w → 1` at `∞` kills the radial weight, and `sin(2θ)^{γ-1} → 0`
(recall `γ > 1`) kills the angular one. -/

/-- `w(z) = (1+z)²/z² → 1` at `+∞`. -/
lemma tendsto_w_atTop : Tendsto w atTop (𝓝 1) := by
  have hev : (fun z : ℝ => w z) =ᶠ[atTop] fun z => (1 + 1 / z) ^ 2 := by
    filter_upwards [Filter.eventually_ge_atTop 1] with z hz
    have hz0 : z ≠ 0 := by linarith
    have h1 : w z = ((1 + z) / z) ^ 2 := by rw [w, div_pow]
    have h2 : (1 + z) / z = 1 + 1 / z := by
      rw [add_div, div_self hz0]
      ring
    rw [h1, h2]
  have hlim : Tendsto (fun z : ℝ => (1 + 1 / z) ^ 2) atTop (𝓝 1) := by
    have h : Tendsto (fun z : ℝ => (1 + z⁻¹)) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add tendsto_inv_atTop_zero
    simpa using h.pow 2
  exact hlim.congr' hev.symm

/-- The radial clause of `BdryTraces` forces the mixed derivative itself to vanish at `z → ∞`. -/
lemma tendsto_atTop_zero_of_traces {u : ℝ → ℝ}
    (h : Tendsto (fun z => z * (u z * w z) ^ 2) atTop (𝓝 0)) : Tendsto u atTop (𝓝 0) := by
  have hF : Tendsto (fun z : ℝ => (u z * w z) ^ 2) atTop (𝓝 0) := by
    have hev : (fun z : ℝ => (u z * w z) ^ 2) =ᶠ[atTop]
        fun z => (z * (u z * w z) ^ 2) * (1 / z) := by
      filter_upwards [Filter.eventually_ge_atTop 1] with z hz
      have hz0 : z ≠ 0 := by linarith
      field_simp
    have hz : Tendsto (fun z : ℝ => (z * (u z * w z) ^ 2) * (1 / z)) atTop (𝓝 0) := by
      simpa using h.mul tendsto_inv_atTop_zero
    exact hz.congr' hev.symm
  have hw2 : Tendsto (fun z : ℝ => (w z) ^ 2) atTop (𝓝 1) := by
    simpa using tendsto_w_atTop.pow 2
  have hsq : Tendsto (fun z : ℝ => (u z) ^ 2) atTop (𝓝 0) := by
    have hwinv : Tendsto (fun z : ℝ => ((w z) ^ 2)⁻¹) atTop (𝓝 1) := by
      simpa using hw2.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
    have hdiv : Tendsto (fun z : ℝ => (u z * w z) ^ 2 * ((w z) ^ 2)⁻¹) atTop (𝓝 0) := by
      simpa using hF.mul hwinv
    have hev : (fun z : ℝ => (u z) ^ 2) =ᶠ[atTop]
        fun z => (u z * w z) ^ 2 * ((w z) ^ 2)⁻¹ := by
      filter_upwards [Filter.eventually_ge_atTop 1] with z hz
      have hwne : w z ≠ 0 := by
        rw [w]
        exact div_ne_zero (pow_ne_zero 2 (by linarith)) (pow_ne_zero 2 (by linarith))
      field_simp
    exact hdiv.congr' hev.symm
  have habs : Tendsto (fun z : ℝ => |u z|) atTop (𝓝 0) := by
    have hcomp := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
    rw [Function.comp_def] at hcomp
    have h2 : (fun z : ℝ => Real.sqrt ((u z) ^ 2)) = fun z => |u z| :=
      funext fun z => Real.sqrt_sq_eq_abs (u z)
    rw [h2] at hcomp
    simpa using hcomp
  refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
  simpa only [Real.norm_eq_abs] using habs

/-- The angular clause of `BdryTraces` forces the mixed derivative itself to vanish at `θ → 0⁺`
(here `1 - γ < 0`, so `sin(2θ)^{γ-1}` tends to `0`). -/
lemma tendsto_nhdsGT_zero_of_traces (α : ℝ) (hα : 0 < α) {u : ℝ → ℝ}
    (h : Tendsto (fun θ => (Real.sin (2 * θ)) ^ (1 - gam α) * (u θ) ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    Tendsto u (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hγ1 : 0 < gam α - 1 := by rw [gam_sub_one]; linarith
  have hγne : gam α ≠ 0 := by rintro h0; rw [h0] at hγ1; norm_num at hγ1
  have hsinlim : Tendsto (fun θ : ℝ => (Real.sin (2 * θ)) ^ (gam α - 1))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hsin : Tendsto (fun θ : ℝ => Real.sin (2 * θ)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have hcont : ContinuousAt (fun θ : ℝ => Real.sin (2 * θ)) 0 :=
        (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousAt
      simpa using hcont.tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ))
    have hc : Tendsto (fun θ : ℝ => (Real.sin (2 * θ)) ^ (gam α - 1))
        (𝓝[>] (0 : ℝ)) (𝓝 ((0 : ℝ) ^ (gam α - 1))) :=
      (Real.continuousAt_rpow_const 0 (gam α - 1) (Or.inr hγ1.le)).tendsto.comp hsin
    rw [Real.zero_rpow (ne_of_gt hγ1)] at hc
    exact hc
  have hprod : Tendsto
      (fun θ => (Real.sin (2 * θ)) ^ (gam α - 1)
        * ((Real.sin (2 * θ)) ^ (1 - gam α) * (u θ) ^ 2))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using hsinlim.mul h
  have heq : (fun θ => (u θ) ^ 2) =ᶠ[𝓝[>] (0 : ℝ)]
      fun θ => (Real.sin (2 * θ)) ^ (gam α - 1)
        * ((Real.sin (2 * θ)) ^ (1 - gam α) * (u θ) ^ 2) := by
    have hlt : ∀ᶠ θ in 𝓝[>] (0 : ℝ), θ < π / 2 :=
      Filter.Eventually.filter_mono (nhdsWithin_le_nhds)
        (isOpen_Iio.mem_nhds (by linarith [Real.pi_pos] : (0 : ℝ) < π / 2))
    filter_upwards [eventually_mem_nhdsWithin (s := Set.Ioi (0 : ℝ)) (a := 0), hlt] with θ hθ0 hθlt
    have hsin : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [Set.mem_Ioi.mp hθ0])
        (by linarith [hθlt, Real.pi_pos])
    rw [← mul_assoc, ← Real.rpow_add hsin, show (gam α - 1) + (1 - gam α) = 0 by ring,
      Real.rpow_zero, one_mul]
  have hsq : Tendsto (fun θ => (u θ) ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := hprod.congr' heq.symm
  have habs : Tendsto (fun θ => |u θ|) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hcomp := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
    rw [Function.comp_def] at hcomp
    have h2 : (fun θ : ℝ => Real.sqrt ((u θ) ^ 2)) = fun θ => |u θ| :=
      funext fun θ => Real.sqrt_sq_eq_abs (u θ)
    rw [h2] at hcomp
    simpa using hcomp
  refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
  simpa only [Real.norm_eq_abs] using habs

/-- The radial Hardy inequality applied to the `θ`-slice of a mixed derivative. -/
lemma mixed_slice_hardyZ (α : ℝ) (f : ℝ → ℝ → ℝ) (hsq : SmoothQuad f)
    (hbd : Work.FTS.Nonlin.BdryTraces α 4 f) (j i : ℕ) (hij : i + j ≤ 4) {σ : ℝ}
    (hσ : σ ∈ Set.Ioo 0 (π / 2))
    (hint : IntegrableOn (fun z => (mixed (j + 1) i f z σ) ^ 2 * (w z) ^ 2) Iz) :
    ∀ z ∈ Set.Ioi (0 : ℝ), (mixed j i f z σ) ^ 2
      ≤ ∫ s in Iz, (mixed (j + 1) i f s σ) ^ 2 * (w s) ^ 2 := by
  have hcd : ContDiffOn ℝ 1 (fun z => mixed j i f z σ) (Set.Ioi (0 : ℝ)) :=
    ((hsq.mixed j i).curry_z hσ).of_le (by simp [Work.Stability.smoothOrder])
      |>.mono (Set.Ioi_subset_Ioi (by norm_num))
  have hdec : Tendsto (fun z => mixed j i f z σ) atTop (𝓝 0) :=
    tendsto_atTop_zero_of_traces ((hbd i j hij).1 σ hσ |>.2)
  intro z hz
  exact hardyZ_open hcd hdec hint z hz

/-- Almost every `θ ∈ Iθ` lies in the *open* interval `(0,π/2)`. -/
lemma ae_mem_Ioo_Iθ : ∀ᵐ θ ∂(volume.restrict Iθ), θ ∈ Set.Ioo (0 : ℝ) (π / 2) := by
  have hIoo : volume.restrict Iθ = volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) :=
    Measure.restrict_congr_set (MeasureTheory.Ioo_ae_eq_Icc (μ := volume)).symm
  rw [hIoo]
  exact ae_restrict_mem measurableSet_Ioo


/-- The `θ`-slice of `(D_θ u)² sin(2θ)^{-γ}` is a.e. strongly measurable, for `u` a mixed
derivative of a `SmoothQuad` function. -/
lemma aesm_slice_Dth_mixed_sq (α : ℝ) (f : ℝ → ℝ → ℝ) (hsq : SmoothQuad f) (b a : ℕ) {z : ℝ}
    (hz : 0 < z) :
    AEStronglyMeasurable
      (fun σ => (Work.Spaces.Dth (mixed b a f) z σ) ^ 2 * (Real.sin (2 * σ)) ^ (-(gam α)))
      (volume.restrict Iθ) := by
  have hDthc : ContinuousOn
      (fun p : ℝ × ℝ => Work.Spaces.Dth (mixed b a f) p.1 p.2) Qd :=
    ((Work.FTS.LocData.contDiffOn_Dth Work.Spaces.isOpen_quadU
        (hsq.mixed b a)).continuousOn.mono Qd_subset_quadU)
  have hcont : ContinuousOn
      (fun p : ℝ × ℝ => (Work.Spaces.Dth (mixed b a f) p.1 p.2) ^ 2
        * (Real.sin (2 * p.2)) ^ (-(gam α))) Qd :=
    (hDthc.pow 2).mul (continuousOn_sin_rpow_Qd (-(gam α)))
  exact aesm_slice_of_continuousOn_Qd _ hcont hz

/-- The `θ`-slice of `(D_θ u)² sin(2θ)^{-γ}` is integrable on `Iθ` for `z > 0`, by domination by
the corresponding mixed slot of `HkIntegrand α 4 f`. -/
lemma integrableOn_Dth_mixed_slice (α : ℝ) (f : ℝ → ℝ → ℝ) (hsq : SmoothQuad f)
    (hmem : HkMem α 4 f) (b a : ℕ) (hij : (a + 1) + b ≤ 4) {z : ℝ} (hz : 0 < z) :
    IntegrableOn
      (fun σ => (Work.Spaces.Dth (mixed b a f) z σ) ^ 2 * (Real.sin (2 * σ)) ^ (-(gam α))) Iθ := by
  have hW : IntegrableOn (fun σ => (mixed b (a + 1) f z σ * Wt α z σ) ^ 2) Iθ :=
    integrableOn_slice_mixed_Wt_sq α f hsq hmem b (a + 1) (by omega) hij (le_of_lt hz)
  refine MeasureTheory.Integrable.mono' hW (aesm_slice_Dth_mixed_sq α f hsq b a hz) ?_
  filter_upwards [ae_mem_Ioo_Iθ] with σ hσ
  have hsin : 0 < Real.sin (2 * σ) := sin_two_pos_of_mem_Ioo hσ
  rw [Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hsin.le _)),
    Dth_mixed_quad hsq b a hz hσ]
  rw [show (mixed b (a + 1) f z σ * Wt α z σ) ^ 2
      = (mixed b (a + 1) f z σ) ^ 2
        * ((w z) ^ 2 * (Real.sin (2 * σ)) ^ (-(gam α))) from by
    rw [show Wt α z σ = w z * (Real.sin (2 * σ)) ^ (-(gam α / 2)) from rfl, mul_pow,
      Wt_sq_Ioo α z σ hσ]]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
  exact le_mul_of_one_le_left (Real.rpow_nonneg hsin.le _) (one_le_w_sq hz)

/-- **The `L^∞`-`ℋ⁴` trade-off in the interior class.**  For `f` of class `RegQ α 4` and
`a + b ≤ 2`, the mixed derivative `D_z^b D_θ^a f` is bounded on the open quadrant by
`10/√(γ-1)·|f|_{ℋ⁴}`.

Proof: at each `z > 0` the angular Hardy inequality (`HardyThetaO`, with the vanishing at
`θ = 0⁺` supplied by the angular clause of `BdryTraces`, through
`tendsto_nhdsGT_zero_of_traces`) bounds `(D_z^bD_θ^a f)(z,θ)²` by
`(100/(γ-1))∫_θ (D_θD_z^bD_θ^a f)² sin(2θ)^{-γ}`, and at each `θ` the radial Hardy inequality
(`mixed_slice_hardyZ`) bounds `(D_θD_z^bD_θ^a f)(z,θ)²` by the `z`-integral of
`(D_z^{b+1}D_θ^{a+1}f)² w²`.  The iterated integral produced this way is exactly the `θ`-first
form of the mixed slot `(i,j) = (a+1,b+1)` of the `ℋ⁴` integrand, which is `≤ HkSq α 4 f` by
`slotM_quad`. -/
theorem mixed_supAbsO_le (α : ℝ) (f : ℝ → ℝ → ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hsq : SmoothQuad f) (hmem : HkMem α 4 f) (hbd : Work.FTS.Nonlin.BdryTraces α 4 f)
    (b a : ℕ) (hab : a + b ≤ 2) :
    supAbsO (mixed b a f) ≤ 10 / Real.sqrt (gam α - 1) * HkNorm α 4 f := by
  have hγ1 : 0 < gam α - 1 := by rw [gam_sub_one]; linarith
  have hγne : gam α ≠ 0 := ne_of_gt (by linarith : 0 < gam α)
  obtain ⟨hTle, hTint, hTae⟩ :=
    slotM_quad α f hsq hmem (b + 1) (a + 1) (by omega) (by omega)
  have hptslot : ∀ σ ∈ Iθ, ∀ z : ℝ, (mixed (b + 1) (a + 1) f z σ * Wt α z σ) ^ 2
      = (Real.sin (2 * σ)) ^ (-(gam α))
        * ((mixed (b + 1) (a + 1) f z σ) ^ 2 * (w z) ^ 2) := by
    intro σ hσ z
    rw [show Wt α z σ = w z * (Real.sin (2 * σ)) ^ (-(gam α / 2)) from rfl, mul_pow,
      Wt_sq α hα z σ hσ]
    ring
  set B : ℝ → ℝ := fun σ => ∫ z in Iz, (mixed (b + 1) (a + 1) f z σ) ^ 2 * (w z) ^ 2 with hBdef
  have hBae : (fun σ => (Real.sin (2 * σ)) ^ (-(gam α)) * B σ)
      =ᵐ[volume.restrict Iθ]
      fun σ => ∫ z in Iz, (mixed (b + 1) (a + 1) f z σ * Wt α z σ) ^ 2 := by
    filter_upwards [hTae, ae_restrict_mem (show MeasurableSet Iθ from measurableSet_Icc)]
      with σ hσint hσI
    rw [hBdef]
    have hstep : (Real.sin (2 * σ)) ^ (-(gam α))
          * (∫ z in Iz, (mixed (b + 1) (a + 1) f z σ) ^ 2 * (w z) ^ 2)
        = ∫ z in Iz, (mixed (b + 1) (a + 1) f z σ * Wt α z σ) ^ 2 := by
      rw [← integral_const_mul]
      exact setIntegral_congr_fun measurableSet_Ici fun z _ => (hptslot σ hσI z).symm
    exact hstep
  have hTint' : Integrable (fun σ => (Real.sin (2 * σ)) ^ (-(gam α)) * B σ)
      (volume.restrict Iθ) := hTint.congr hBae.symm
  set T : ℝ := ∫ σ in Iθ, (Real.sin (2 * σ)) ^ (-(gam α)) * B σ with hTdef
  have hTle' : T ≤ HkSq α 4 f := by
    rw [hTdef]
    rw [show (∫ σ in Iθ, (Real.sin (2 * σ)) ^ (-(gam α)) * B σ)
        = ∫ σ in Iθ, ∫ z in Iz, (mixed (b + 1) (a + 1) f z σ * Wt α z σ) ^ 2
        from integral_congr_ae hBae]
    exact hTle
  have hTnn : 0 ≤ T := by
    rw [hTdef]
    exact setIntegral_nonneg measurableSet_Icc fun σ hσ =>
      mul_nonneg (Real.rpow_nonneg (sin_two_nonneg hσ) _)
        (integral_nonneg fun z => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hKnn : 0 ≤ 100 / (gam α - 1) := div_nonneg (by norm_num) hγ1.le
  -- the pointwise bound on the open quadrant
  have hpoint : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      |mixed b a f z θ| ≤ Real.sqrt ((100 / (gam α - 1)) * T) := by
    intro z θ hz0 hθ0 hθ1
    have hθI : θ ∈ Iθ := ⟨hθ0.le, hθ1.le⟩
    have hlim0 : Tendsto (fun θ' => mixed b a f z θ') (𝓝[>] 0) (𝓝 0) :=
      tendsto_nhdsGT_zero_of_traces α hα ((hbd a b (by omega)).2 z (Set.mem_Ioi.mpr hz0) |>.1)
    have hDth_int := integrableOn_Dth_mixed_slice α f hsq hmem b a (by omega) hz0
    have hDth_int2 : IntegrableOn
        (fun σ => (Real.sin (2 * σ)) ^ (-(gam α))
          * (Work.Spaces.Dth (mixed b a f) z σ) ^ 2) Iθ :=
      hDth_int.congr_fun (fun σ _ => by ring) measurableSet_Icc
    have hint_ang : IntegrableOn
        (fun σ => (pth (mixed b a f) z σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - gam α)) Iθ :=
      hDth_int2.congr_fun (fun σ hσ => by
        calc (Real.sin (2 * σ)) ^ (-(gam α))
              * (Work.Spaces.Dth (mixed b a f) z σ) ^ 2
            = (Work.Spaces.Dth (mixed b a f) z σ) ^ 2
                * (Real.sin (2 * σ)) ^ (-(gam α)) := by ring
          _ = (pth (mixed b a f) z σ) ^ 2
                * (Real.sin (2 * σ)) ^ (2 - gam α) :=
              (pth_sq_mul_sin_eq α hα hα1 (mixed b a f) z σ hσ).symm) measurableSet_Icc
    have hHT := HardyThetaO α hα hα1 (mixed b a f) z (hsq.mixed b a)
      (Set.mem_Ioi.mpr (by linarith)) hlim0 hint_ang θ ⟨hθ0, hθ1⟩
    have hI1 : (∫ σ in Iθ, (pth (mixed b a f) z σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - gam α))
        = ∫ σ in Iθ, (Real.sin (2 * σ)) ^ (-(gam α))
            * (Work.Spaces.Dth (mixed b a f) z σ) ^ 2 := by
      refine setIntegral_congr_fun measurableSet_Icc fun σ hσ => ?_
      rw [pth_sq_mul_sin_eq α hα hα1 (mixed b a f) z σ hσ]
      ring
    have hrad : ∀ᵐ σ ∂(volume.restrict Iθ),
        (Real.sin (2 * σ)) ^ (-(gam α)) * (Work.Spaces.Dth (mixed b a f) z σ) ^ 2
          ≤ (Real.sin (2 * σ)) ^ (-(gam α)) * B σ := by
      filter_upwards [hTae, ae_restrict_mem (show MeasurableSet Iθ from measurableSet_Icc)]
        with σ hσint hσI
      rcases eq_or_lt_of_le hσI.1 with hσeq | hσpos
      · have hsin0 : Real.sin (2 * σ) = 0 := by rw [← hσeq]; simp
        have hz : (Real.sin (2 * σ)) ^ (-(gam α)) = 0 := by
          rw [hsin0]
          exact Real.zero_rpow (neg_ne_zero.mpr hγne)
        simp [hz]
      rcases eq_or_lt_of_le hσI.2 with hσeq | hσlt
      · have hsin0 : Real.sin (2 * σ) = 0 := by
          rw [hσeq, show 2 * (π / 2) = π by ring, Real.sin_pi]
        have hz : (Real.sin (2 * σ)) ^ (-(gam α)) = 0 := by
          rw [hsin0]
          exact Real.zero_rpow (neg_ne_zero.mpr hγne)
        simp [hz]
      · have hσ' : σ ∈ Set.Ioo 0 (π / 2) := ⟨hσpos, hσlt⟩
        rw [Dth_mixed_quad hsq b a hz0 hσ']
        exact mul_le_mul_of_nonneg_left
          (mixed_slice_hardyZ α f hsq hbd b (a + 1) (by omega) hσ' hσint z
            (Set.mem_Ioi.mpr hz0))
          (Real.rpow_nonneg (sin_two_nonneg hσI) _)
    have hIntLe : (∫ σ in Iθ, (pth (mixed b a f) z σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - gam α))
        ≤ T := by
      rw [hI1, hTdef]
      exact integral_mono_ae hDth_int2 hTint' hrad
    have hfin : (mixed b a f z θ) ^ 2 ≤ (100 / (gam α - 1)) * T :=
      le_trans hHT (mul_le_mul_of_nonneg_left hIntLe hKnn)
    calc |mixed b a f z θ| = Real.sqrt ((mixed b a f z θ) ^ 2) :=
          (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt ((100 / (gam α - 1)) * T) := Real.sqrt_le_sqrt hfin
  refine le_trans (supAbsO_le (g := mixed b a f)
    (C := Real.sqrt ((100 / (gam α - 1)) * T)) hpoint) ?_
  have h1 : Real.sqrt ((100 / (gam α - 1)) * T)
      ≤ Real.sqrt ((100 / (gam α - 1)) * HkSq α 4 f) :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hTle' hKnn)
  refine le_trans h1 ?_
  have hsqrt : Real.sqrt (100 / (gam α - 1)) = 10 / Real.sqrt (gam α - 1) := by
    have h2 : (0 : ℝ) ≤ 10 / Real.sqrt (gam α - 1) :=
      div_nonneg (by norm_num) (Real.sqrt_nonneg _)
    rw [← Real.sqrt_sq h2]
    congr 1
    rw [div_pow, Real.sq_sqrt hγ1.le]
    norm_num
  have hfinal : Real.sqrt ((100 / (gam α - 1)) * HkSq α 4 f)
      = 10 / Real.sqrt (gam α - 1) * HkNorm α 4 f := by
    rw [Real.sqrt_mul hKnn, hsqrt]
    simp only [HkNorm]
  exact le_of_eq hfinal


/-- Elgindi's Corollary `SecondDerivativesBounded` (tex 1094) in the *interior* class
`Work.FTS.Nonlin.RegQ` of the frozen `Submission/Work/FTS/Vocab.lean`: for `RegQ α 4 f`
(`= SmoothQuad f ∧ HkMem α 4 f ∧ BdryTraces α 4 f`) and `i + j ≤ 2`,
`supAbsO (D_z^j D_θ^i f) ≤ C/√(γ-1) |f|_{ℋ⁴}`, `C` universal.

This is the `RegQ` restatement of `Work.FTS.H2.SupMixedLeH4` (which uses `Spaces.SmoothNbhd`
= `ContDiffOn ℝ ⊤` = *analyticity* on a neighbourhood of the closed quadrant, unsatisfiable for
`F_*`, the stream functions and N9's cut-off datum; design §5 T1) and it is the design
document's `LinfQ` (§3.3 L-N4.5).  As there, `VanishTheta` is *not* assumed: the transport
estimates apply this to the radial coefficient `L₁₂(g)`.

The supremum is taken over the *open* quadrant (`Work.FTS.H2.supAbsO`), not over the closed
quadrant: `RegQ` constrains `f` only inside the quadrant and its values on `θ = 0, π/2` are
unconstrained (e.g. `f z θ = if θ = 0 then 10 else 0` has `RegQ α 4 f` and `HkNorm α 4 f = 0`),
so the closed-quadrant supremum is not controlled by the `ℋ⁴` norm, while every use of this
estimate is a pointwise bound of an integrand inside the quadrant.
`supAbsO` is dominated by `Spaces.supAbs` and agrees with it for functions continuous on the
closed quadrant (`supAbsO_le_supAbs`, `supAbsO_eq_supAbs_of_continuousOn`).

Proof route (as in `SupMixedLeH4`): for `a ≥ 1` use the angular Hardy inequality
`sup_θ |u|² ≤ C/(γ-1)∫(∂_θu)² sin(2θ)^{2-γ}` followed by the radial Hardy inequality `HardyZ`
on `∂_θu` at fixed `θ`, so that
`supAbsO (mixed b a f)² ≤ C/(γ-1)∫∫ (mixed (b+1) (a+1) f)² W²` (an `ℋ⁴`-term, using
`sin²(2θ) sin(2θ)^{-γ} = sin(2θ)^{2-γ}`); for `a = 0` compare `u` with the `θ`-average of `u²`
and conclude with `HardyZ` on `u` and on `∂_θu`.  Slice differentiability comes from
`SmoothQuad`; the boundary limits needed by the two Hardy inequalities come from `BdryTraces`
(its `z`-clauses give `mixed b a f z θ → 0` at `z → ∞` because `w → 1`). -/
theorem LinfQ : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : Work.FTS.Galerkin.Fn) (b a : ℕ),
    0 < α → α ≤ 1 → a + b ≤ 2 → Work.FTS.Nonlin.RegQ α 4 f →
    Work.FTS.H2.supAbsO (Work.Spaces.mixed b a f)
      ≤ C / Real.sqrt (Work.Spaces.gam α - 1) * Work.FTS.Nonlin.Xn α f := by
  refine ⟨10, by norm_num, ?_⟩
  intro α f b a hα hα1 hab hreg
  obtain ⟨hsq, hmem, hbd⟩ := hreg
  have h := mixed_supAbsO_le α f hα hα1 hsq hmem hbd b a hab
  simpa only [Work.FTS.Nonlin.Xn] using h

end Work.FTS.H2
