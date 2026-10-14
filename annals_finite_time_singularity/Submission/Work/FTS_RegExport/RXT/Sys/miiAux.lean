import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.Nonlinear.n4norm_exists
import Submission.Work.FTS.RegExportIface.RXT.Leaves
import Submission.Work.FTS_RegExport.RXT.jc3_aux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology NNReal
open Set Filter MeasureTheory

namespace Work.FTS_RegExport.RXT.Sys

open Work.FTS.Galerkin (Fn Fam slice gdot)
open Work.FTS.RegExportIface.RXT (idx GdotLoc)
open Work.FTS.Regularity (pExp)

set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {α C₀ S : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam}

/-! ## §0  Elementary tools -/

/-- **Difference quotients along `ε/(n+1)`.** -/
theorem mii_tendsto_slope_seq {f : ℝ → ℝ} {x L ε : ℝ} (hε : 0 < ε) (h : HasDerivAt f L x) :
    Tendsto (fun n : ℕ => (f (x + ε / ((n : ℝ) + 1)) - f x) / (ε / ((n : ℝ) + 1)))
      atTop (𝓝 L) := by
  have hδ0 : Tendsto (fun n : ℕ => ε / ((n : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) := by
    have h1 : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa [div_eq_mul_inv, mul_comm] using h1.const_mul ε
  have hne : ∀ᶠ n : ℕ in atTop, ε / ((n : ℝ) + 1) ≠ 0 :=
    Filter.Eventually.of_forall fun n => by positivity
  have hx : Tendsto (fun n : ℕ => x + ε / ((n : ℝ) + 1)) atTop (𝓝[≠] x) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨by simpa using hδ0.const_add x, ?_⟩
    filter_upwards [hne] with n hn
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro hh
    exact hn (by linarith)
  refine (h.tendsto_slope.comp hx).congr' ?_
  filter_upwards with n
  simp only [Function.comp_apply, slope, smul_eq_mul, div_eq_mul_inv, vsub_eq_sub]
  ring

/-- **The mean value bound.** -/
lemma mii_abs_sub_le_of_abs_deriv_le {f : ℝ → ℝ} {a b C : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn f (Set.Icc a b))
    (hdiff : ∀ x ∈ Set.Ioo a b, HasDerivAt f (deriv f x) x)
    (hb : ∀ x ∈ Set.Icc a b, |deriv f x| ≤ C) :
    |f b - f a| ≤ C * (b - a) := by
  rcases eq_or_lt_of_le hab with h | h
  · subst h; simp
  · obtain ⟨c, hc, hcd⟩ := exists_deriv_eq_slope f h hcont
      (fun x hx => (hdiff x hx).differentiableAt.differentiableWithinAt)
    have hpos : (0 : ℝ) < b - a := by linarith
    have h1 : |f b - f a| = |deriv f c| * (b - a) := by
      rw [hcd, abs_div, abs_of_pos hpos, div_mul_cancel₀ _ (ne_of_gt hpos)]
    rw [h1]
    exact mul_le_mul_of_nonneg_right (hb c ⟨le_of_lt hc.1, le_of_lt hc.2⟩) (le_of_lt hpos)

/-- **Measurability of a parametrized derivative.** -/
theorem mii_aesm_param_deriv {μ : Measure ℝ} {G : ℝ → ℝ → ℝ} {G' : ℝ → ℝ} {x r : ℝ}
    (hr : 0 < r)
    (hmeas : ∀ y ∈ Set.Ioo (x - r) (x + r), AEStronglyMeasurable (fun σ => G σ y) μ)
    (hder : ∀ᵐ σ ∂μ, HasDerivAt (fun y => G σ y) (G' σ) x) :
    AEStronglyMeasurable G' μ := by
  have hmem : ∀ n : ℕ, x + r / ((n : ℝ) + 2) ∈ Set.Ioo (x - r) (x + r) := by
    intro n
    have h2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    have hp : 0 < r / ((n : ℝ) + 2) := div_pos hr h2
    have hl : r / ((n : ℝ) + 2) < r := by rw [div_lt_iff₀ h2]; nlinarith
    exact ⟨by linarith, by linarith⟩
  have hxn : x ∈ Set.Ioo (x - r) (x + r) := ⟨by linarith, by linarith⟩
  have hu : ∀ n : ℕ, AEStronglyMeasurable
      (fun σ => (r / ((n : ℝ) + 2))⁻¹ * (G σ (x + r / ((n : ℝ) + 2)) - G σ x)) μ :=
    fun n => ((hmeas _ (hmem n)).sub (hmeas _ hxn)).const_mul _
  have htend : Tendsto (fun n : ℕ => r / ((n : ℝ) + 2)) atTop (𝓝[≠] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, Filter.Eventually.of_forall fun n => ne_of_gt (div_pos hr (by positivity))⟩
    have hg : Tendsto (fun n : ℕ => ((n : ℝ) + 2)) atTop atTop :=
      tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop
    exact tendsto_const_nhds.div_atTop hg
  have hlim : ∀ᵐ σ ∂μ, Tendsto (fun n : ℕ =>
      (r / ((n : ℝ) + 2))⁻¹ * (G σ (x + r / ((n : ℝ) + 2)) - G σ x)) atTop (𝓝 (G' σ)) :=
    hder.mono fun σ hσ => by
      have h := hσ.tendsto_slope_zero.comp htend
      simpa only [Function.comp_def, smul_eq_mul] using h
  exact aestronglyMeasurable_of_tendsto_ae atTop hu hlim

/-- The `z`-slice of a mixed jet is differentiable, at finite order `n ≥ j + i + 1`. -/
lemma mii_hasDerivAt_mixed_slice_z {W : ℝ → ℝ → ℝ} {n j i : ℕ}
    (hW : ContDiffOn ℝ n (Function.uncurry W) Work.FTS.EllipticEst.Q0) (hji : j + i + 1 ≤ n)
    {x θ : ℝ} (hx : 0 < x) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    HasDerivAt (fun x' : ℝ => Work.Spaces.mixed j i W x' θ)
      (Work.Spaces.pz (Work.Spaces.mixed j i W) x θ) x :=
  hasDerivAt_slice_fst_of_contDiffOn Work.FTS.EllipticEst.isOpen_Q0
    (Work.FTS.CoercivityFix.Transfer.E2pkg.contDiffOn_uncurry_mixed_le
      Work.FTS.EllipticEst.isOpen_Q0 i j 1 (by omega) hW) ⟨hx, hθ⟩

/-- The `θ`-slice of a mixed jet is differentiable, at finite order `n ≥ j + i + 1`. -/
lemma mii_hasDerivAt_mixed_slice_theta {W : ℝ → ℝ → ℝ} {n j i : ℕ}
    (hW : ContDiffOn ℝ n (Function.uncurry W) Work.FTS.EllipticEst.Q0) (hji : j + i + 1 ≤ n)
    {x θ : ℝ} (hx : 0 < x) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    HasDerivAt (fun θ' : ℝ => Work.Spaces.mixed j i W x θ')
      (Work.Spaces.pth (Work.Spaces.mixed j i W) x θ) θ :=
  hasDerivAt_slice_snd_of_contDiffOn Work.FTS.EllipticEst.isOpen_Q0
    (Work.FTS.CoercivityFix.Transfer.E2pkg.contDiffOn_uncurry_mixed_le
      Work.FTS.EllipticEst.isOpen_Q0 i j 1 (by omega) hW) ⟨hx, hθ⟩

/-- `mixed 1 0 X z θ = z ∂_z X (z,θ)`. -/
lemma mii_mixed_one_zero_apply (X : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.mixed 1 0 X z θ = z * Work.Spaces.pz X z θ := by
  have h := congrFun (congrFun (mixed_succ_fst_eq X 0 0) z) θ
  simpa only [Work.Spaces.mixed, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_zero,
    Nat.zero_add] using h

/-- `mixed 0 1 X z θ = sin (2θ) ∂_θ X (z,θ)`. -/
lemma mii_mixed_zero_one_apply (X : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.mixed 0 1 X z θ = Real.sin (2 * θ) * Work.Spaces.pth X z θ := by
  simp only [Work.Spaces.mixed, Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero,
    Work.Spaces.DzIter_zero, Work.Spaces.Dth]

/-- `mixed (j+1) i X z θ = z ∂_z (mixed j i X) (z,θ)`. -/
lemma mii_mixed_succ_apply (X : ℝ → ℝ → ℝ) (j i : ℕ) (z θ : ℝ) :
    Work.Spaces.mixed (j + 1) i X z θ
      = z * Work.Spaces.pz (Work.Spaces.mixed j i X) z θ :=
  congrFun (congrFun (mixed_succ_fst_eq X j i) z) θ

/-- `mixed 0 (i+1) X z θ = sin (2θ) ∂_θ (mixed 0 i X) (z,θ)`. -/
lemma mii_mixed_zero_succ_apply (X : ℝ → ℝ → ℝ) (i : ℕ) (z θ : ℝ) :
    Work.Spaces.mixed 0 (i + 1) X z θ
      = Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.mixed 0 i X) z θ :=
  rfl

/-! ## §1  The two predicates -/

/-- The integrated identity for the slot `D_z^jD_θ^i`. -/
def mii_P (S : ℝ) (g : Fam) (j i : ℕ) : Prop :=
  ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 → ∀ τ₁ τ₂, 0 ≤ τ₁ → τ₁ ≤ τ₂ → τ₂ ≤ S →
    Work.Spaces.mixed j i (slice g τ₂) z θ - Work.Spaces.mixed j i (slice g τ₁) z θ
      = ∫ σ in τ₁..τ₂, Work.Spaces.mixed j i (gdot g σ) z θ

/-- The `τ`-integrability of the slot `D_z^jD_θ^i` of `∂_τg`. -/
def mii_R (S : ℝ) (g : Fam) (j i : ℕ) : Prop :=
  ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 → ∀ τ₁ τ₂, 0 ≤ τ₁ → τ₁ ≤ τ₂ → τ₂ ≤ S →
    IntervalIntegrable (fun σ => Work.Spaces.mixed j i (gdot g σ) z θ) volume τ₁ τ₂

/-! ## §2  Measurability of the slots of total order `≤ 1` of `∂_τg` -/

/-- `GdotLoc` gives the `C²`-hypothesis at every `σ ∈ (0,S]`, hence a.e. on `(0,S]`. -/
theorem mii_ae_contDiffOn_gdot {S τ₁ τ₂ : ℝ} {g : Fam} (hG : GdotLoc S g)
    (h0 : 0 ≤ τ₁) (h2S : τ₂ ≤ S) :
    ∀ᵐ σ ∂(volume.restrict (Set.Ioc τ₁ τ₂)),
      ContDiffOn ℝ 2 (Function.uncurry (gdot g σ)) Work.FTS.EllipticEst.Q0 := by
  rw [ae_restrict_iff' measurableSet_Ioc]
  exact Filter.Eventually.of_forall fun σ hσ =>
    hG.1 σ ⟨lt_of_le_of_lt h0 hσ.1, le_trans hσ.2 h2S⟩

/-- The slot `mixed 0 0 (gdot g σ) = ∂_τg(σ)` is measurable in `σ` (`measurable_deriv`). -/
theorem mii_aesm_mixed_gdot_00 {τ₁ τ₂ : ℝ} {g : Fam} :
    ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      AEStronglyMeasurable
        (fun σ => Work.Spaces.mixed 0 0 (gdot g σ) z θ) (volume.restrict (Set.Ioc τ₁ τ₂)) :=
  fun z θ _ _ _ => by
    simpa only [Work.Spaces.mixed, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_zero,
      Work.FTS.Galerkin.gdot] using
      (measurable_deriv (fun s : ℝ => g z θ s)).aestronglyMeasurable

/-- The slot `mixed 1 0 (gdot g σ) = z ∂_z(∂_τg)(σ)` is measurable in `σ`. -/
theorem mii_aesm_mixed_gdot_10 {S τ₁ τ₂ : ℝ} {g : Fam} (hG : GdotLoc S g)
    (h0 : 0 ≤ τ₁) (h2S : τ₂ ≤ S) :
    ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      AEStronglyMeasurable
        (fun σ => Work.Spaces.mixed 1 0 (gdot g σ) z θ) (volume.restrict (Set.Ioc τ₁ τ₂)) := by
  intro z θ hz hθ hθ'
  have hbase : ∀ y ∈ Set.Ioo (z - z / 2) (z + z / 2),
      AEStronglyMeasurable (fun σ => Work.Spaces.mixed 0 0 (gdot g σ) y θ)
        (volume.restrict (Set.Ioc τ₁ τ₂)) :=
    fun y hy => mii_aesm_mixed_gdot_00 y θ (by linarith [hy.1]) hθ hθ'
  have hder : ∀ᵐ σ ∂(volume.restrict (Set.Ioc τ₁ τ₂)),
      HasDerivAt (fun y => Work.Spaces.mixed 0 0 (gdot g σ) y θ)
        (deriv (fun y => Work.Spaces.mixed 0 0 (gdot g σ) y θ) z) z := by
    filter_upwards [mii_ae_contDiffOn_gdot hG h0 h2S] with σ hσ
    exact (mii_hasDerivAt_mixed_slice_z (n := 2) (j := 0) (i := 0) hσ (by norm_num) hz
      ⟨hθ, hθ'⟩).differentiableAt.hasDerivAt
  have h := mii_aesm_param_deriv (x := z) (r := z / 2) (by linarith) hbase hder
  refine (h.const_mul z).congr (Filter.Eventually.of_forall fun σ => ?_)
  show z * deriv (fun y => Work.Spaces.mixed 0 0 (gdot g σ) y θ) z
    = Work.Spaces.mixed 1 0 (gdot g σ) z θ
  rw [mii_mixed_one_zero_apply]
  simp [Work.Spaces.pz]

/-- The slot `mixed 0 1 (gdot g σ) = sin(2θ) ∂_θ(∂_τg)(σ)` is measurable in `σ`. -/
theorem mii_aesm_mixed_gdot_01 {S τ₁ τ₂ : ℝ} {g : Fam} (hG : GdotLoc S g)
    (h0 : 0 ≤ τ₁) (h2S : τ₂ ≤ S) :
    ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      AEStronglyMeasurable
        (fun σ => Work.Spaces.mixed 0 1 (gdot g σ) z θ) (volume.restrict (Set.Ioc τ₁ τ₂)) := by
  intro z θ hz hθ hθ'
  have hbase : ∀ y ∈ Set.Ioo (θ - min θ (Real.pi / 2 - θ) / 2) (θ + min θ (Real.pi / 2 - θ) / 2),
      AEStronglyMeasurable (fun σ => Work.Spaces.mixed 0 0 (gdot g σ) z y)
        (volume.restrict (Set.Ioc τ₁ τ₂)) := by
    intro y hy
    obtain ⟨hy1, hy2⟩ := hy
    have hmin1 : min θ (Real.pi / 2 - θ) ≤ θ := min_le_left _ _
    have hmin2 : min θ (Real.pi / 2 - θ) ≤ Real.pi / 2 - θ := min_le_right _ _
    have hy0 : 0 < y := by linarith
    have hy1' : y < Real.pi / 2 := by linarith
    exact mii_aesm_mixed_gdot_00 z y hz hy0 hy1'
  have hder : ∀ᵐ σ ∂(volume.restrict (Set.Ioc τ₁ τ₂)),
      HasDerivAt (fun y => Work.Spaces.mixed 0 0 (gdot g σ) z y)
        (deriv (fun y => Work.Spaces.mixed 0 0 (gdot g σ) z y) θ) θ := by
    filter_upwards [mii_ae_contDiffOn_gdot hG h0 h2S] with σ hσ
    exact (mii_hasDerivAt_mixed_slice_theta (n := 2) (j := 0) (i := 0) hσ (by norm_num) hz
      ⟨hθ, hθ'⟩).differentiableAt.hasDerivAt
  have hminpos : 0 < min θ (Real.pi / 2 - θ) := lt_min hθ (by linarith)
  have h := mii_aesm_param_deriv (x := θ) (r := min θ (Real.pi / 2 - θ) / 2)
    (by linarith) hbase hder
  refine (h.const_mul (Real.sin (2 * θ))).congr (Filter.Eventually.of_forall fun σ => ?_)
  show Real.sin (2 * θ) * deriv (fun y => Work.Spaces.mixed 0 0 (gdot g σ) z y) θ
    = Work.Spaces.mixed 0 1 (gdot g σ) z θ
  rw [mii_mixed_zero_one_apply]
  simp [Work.Spaces.pth]

/-! ## §3  Sup bounds for the first derivatives of the slots of order `≤ 1` -/

/-- `GdotLoc`'s sup bound for the first `z`-derivatives of the slots of order `≤ 1`, on the box
`[z/2, 2z] × {θ}`. -/
theorem mii_abs_pz_mixed_gdot_le {S : ℝ} {g : Fam} (hG : GdotLoc S g) {j i : ℕ}
    (hji : j + i ≤ 1) {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ ∈ Set.Ioc (0 : ℝ) S, ∀ y ∈ Set.Icc (z / 2) (2 * z),
      |Work.Spaces.pz (Work.Spaces.mixed j i (gdot g σ)) y θ| ≤ C := by
  obtain ⟨C, hC⟩ := hG.2 (z / 2) (2 * z) (θ / 2) ((θ + Real.pi / 2) / 2)
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith [Real.pi_pos])
  refine ⟨max C 0, le_max_right _ _, fun σ hσ y hy => ?_⟩
  exact ((hC σ hσ y hy θ ⟨by linarith, by linarith⟩).2 j i hji).1.trans (le_max_left _ _)

/-- `GdotLoc`'s sup bound for the first `θ`-derivatives of the slots of order `≤ 1`, on the box
`{z} × [θ, (θ+π/2)/2]`. -/
theorem mii_abs_pth_mixed_gdot_le {S : ℝ} {g : Fam} (hG : GdotLoc S g) {j i : ℕ}
    (hji : j + i ≤ 1) {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ ∈ Set.Ioc (0 : ℝ) S, ∀ y ∈ Set.Icc θ ((θ + Real.pi / 2) / 2),
      |Work.Spaces.pth (Work.Spaces.mixed j i (gdot g σ)) z y| ≤ C := by
  obtain ⟨C, hC⟩ := hG.2 (z / 2) (2 * z) (θ / 2) ((θ + Real.pi / 2) / 2)
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith [Real.pi_pos])
  refine ⟨max C 0, le_max_right _ _, fun σ hσ y hy => ?_⟩
  obtain ⟨hy1, hy2⟩ := hy
  exact ((hC σ hσ z ⟨by linarith, by linarith⟩ y ⟨by linarith, by linarith⟩).2 j i hji).2.trans
    (le_max_left _ _)

/-- `GdotLoc`'s sup bound for the slots of total order `≤ 2` (used for the dominated convergence
in the difference-quotient argument). -/
theorem mii_abs_mixed_gdot_le {S : ℝ} {g : Fam} (hG : GdotLoc S g) {j i : ℕ}
    (hji : j + i ≤ 1) {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ ∈ Set.Ioc (0 : ℝ) S, ∀ y ∈ Set.Icc (z / 2) (2 * z),
      |Work.Spaces.mixed j i (gdot g σ) y θ| ≤ C := by
  obtain ⟨C, hC⟩ := hG.2 (z / 2) (2 * z) (θ / 2) ((θ + Real.pi / 2) / 2)
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith [Real.pi_pos])
  refine ⟨max C 0, le_max_right _ _, fun σ hσ y hy => ?_⟩
  exact ((hC σ hσ y hy θ ⟨by linarith, by linarith⟩).1 j i (by omega)).trans (le_max_left _ _)

/-! ## §4  Integrability of the slots of order `≤ 1` -/

/-- `σ ↦ gdot g σ z θ` is interval integrable. -/
theorem mii_R_00 {S : ℝ} {g : Fam} (hG : GdotLoc S g) : mii_R S g 0 0 := by
  intro z θ hz hθ hθ' τ₁ τ₂ h0 h12 h2S
  obtain ⟨C, hC0, hC⟩ := mii_abs_mixed_gdot_le hG (j := 0) (i := 0) (by omega) hz hθ hθ'
  rw [intervalIntegrable_iff, uIoc_of_le h12]
  refine IntegrableOn.of_bound (s := Set.Ioc τ₁ τ₂) measure_Ioc_lt_top ?_ C ?_
  · exact mii_aesm_mixed_gdot_00 z θ hz hθ hθ'
  · rw [ae_restrict_iff' measurableSet_Ioc]
    refine Filter.Eventually.of_forall fun σ hσ => ?_
    have hb := hC σ ⟨lt_of_le_of_lt h0 hσ.1, le_trans hσ.2 h2S⟩ z ⟨by linarith, by linarith⟩
    simpa only [Real.norm_eq_abs, Work.Spaces.mixed, Work.Spaces.DzIter_zero,
      Work.Spaces.DthIter_zero] using hb

/-- `σ ↦ mixed 1 0 (gdot g σ) z θ` is interval integrable. -/
theorem mii_R_10 {S : ℝ} {g : Fam} (hG : GdotLoc S g) : mii_R S g 1 0 := by
  intro z θ hz hθ hθ' τ₁ τ₂ h0 h12 h2S
  obtain ⟨C, hC0, hC⟩ := mii_abs_pz_mixed_gdot_le hG (j := 0) (i := 0) (by omega) hz hθ hθ'
  rw [intervalIntegrable_iff, uIoc_of_le h12]
  refine IntegrableOn.of_bound (s := Set.Ioc τ₁ τ₂) measure_Ioc_lt_top ?_ (C * z) ?_
  · exact mii_aesm_mixed_gdot_10 hG h0 h2S z θ hz hθ hθ'
  · rw [ae_restrict_iff' measurableSet_Ioc]
    refine Filter.Eventually.of_forall fun σ hσ => ?_
    have hb := hC σ ⟨lt_of_le_of_lt h0 hσ.1, le_trans hσ.2 h2S⟩ z ⟨by linarith, by linarith⟩
    rw [Real.norm_eq_abs, mii_mixed_one_zero_apply, abs_mul, abs_of_pos hz]
    calc z * |Work.Spaces.pz (gdot g σ) z θ| ≤ z * C :=
          mul_le_mul_of_nonneg_left (by simpa only [Work.Spaces.mixed, Work.Spaces.DzIter_zero,
            Work.Spaces.DthIter_zero] using hb) (le_of_lt hz)
      _ = C * z := by ring

/-- `σ ↦ mixed 0 1 (gdot g σ) z θ` is interval integrable. -/
theorem mii_R_01 {S : ℝ} {g : Fam} (hG : GdotLoc S g) : mii_R S g 0 1 := by
  intro z θ hz hθ hθ' τ₁ τ₂ h0 h12 h2S
  obtain ⟨C, hC0, hC⟩ := mii_abs_pth_mixed_gdot_le hG (j := 0) (i := 0) (by omega) hz hθ hθ'
  rw [intervalIntegrable_iff, uIoc_of_le h12]
  refine IntegrableOn.of_bound (s := Set.Ioc τ₁ τ₂) measure_Ioc_lt_top ?_ (C * Real.sin (2 * θ)) ?_
  · exact mii_aesm_mixed_gdot_01 hG h0 h2S z θ hz hθ hθ'
  · rw [ae_restrict_iff' measurableSet_Ioc]
    refine Filter.Eventually.of_forall fun σ hσ => ?_
    have hmemσ : σ ∈ Set.Ioc (0 : ℝ) S := ⟨lt_of_le_of_lt h0 hσ.1, le_trans hσ.2 h2S⟩
    have hmemθ : θ ∈ Set.Icc θ ((θ + Real.pi / 2) / 2) := ⟨le_refl θ, by linarith⟩
    have hb := hC σ hmemσ θ hmemθ
    have hb' : |Work.Spaces.pth (gdot g σ) z θ| ≤ C := by
      simpa only [Work.Spaces.mixed, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_zero] using hb
    have hsin : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
    rw [Real.norm_eq_abs, mii_mixed_zero_one_apply, abs_mul, abs_of_pos hsin]
    calc Real.sin (2 * θ) * |Work.Spaces.pth (gdot g σ) z θ| ≤ Real.sin (2 * θ) * C :=
          mul_le_mul_of_nonneg_left hb' (le_of_lt hsin)
      _ = C * Real.sin (2 * θ) := by ring



/-! ## §5  The combined measurability statement for the slots of order `≤ 1` -/

theorem mii_aesm_mixed_gdot_low {S τ₁ τ₂ : ℝ} {g : Fam} (hG : GdotLoc S g)
    (h0 : 0 ≤ τ₁) (h2S : τ₂ ≤ S) :
    ∀ j i : ℕ, j + i ≤ 1 → ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      AEStronglyMeasurable (fun σ => Work.Spaces.mixed j i (gdot g σ) z θ)
        (volume.restrict (Set.Ioc τ₁ τ₂)) := by
  intro j i hji z θ hz hθ hθ'
  obtain rfl | rfl : j = 0 ∨ j = 1 := by omega
  · obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
    · exact mii_aesm_mixed_gdot_00 z θ hz hθ hθ'
    · exact mii_aesm_mixed_gdot_01 hG h0 h2S z θ hz hθ hθ'
  · obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
    · exact mii_aesm_mixed_gdot_10 hG h0 h2S z θ hz hθ hθ'
    · omega

/-! ## §6  Continuity of the mixed slices -/

/-- The `z`-slices of the mixed slots are continuous on compact sub-intervals of `(0,∞)`. -/
lemma mii_continuousOn_mixed_slice_z {W : ℝ → ℝ → ℝ} {n j i : ℕ}
    (hW : ContDiffOn ℝ n (Function.uncurry W) Work.FTS.EllipticEst.Q0) (hji : j + i + 1 ≤ n)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun y : ℝ => Work.Spaces.mixed j i W y θ) (Set.Icc a b) := by
  have hC1 : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.mixed j i W))
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS.CoercivityFix.Transfer.E2pkg.contDiffOn_uncurry_mixed_le
      Work.FTS.EllipticEst.isOpen_Q0 i j 1 (by omega) hW
  have hmaps : MapsTo (fun y : ℝ => (y, θ)) (Set.Icc a b) Work.FTS.EllipticEst.Q0 :=
    fun y hy => ⟨ha.trans_le hy.1, hθ.1, hθ.2⟩
  have h := hC1.continuousOn.comp (continuousOn_id.prodMk continuousOn_const) hmaps
  simpa only [Function.comp_def, Function.uncurry_apply_pair, id_eq] using h

/-- The `θ`-slices of the mixed slots are continuous on compact sub-intervals of `(0,π/2)`. -/
lemma mii_continuousOn_mixed_slice_theta {W : ℝ → ℝ → ℝ} {n j i : ℕ}
    (hW : ContDiffOn ℝ n (Function.uncurry W) Work.FTS.EllipticEst.Q0) (hji : j + i + 1 ≤ n)
    {z : ℝ} (hz : 0 < z) {c d : ℝ} (hc : 0 < c) (hd : d < Real.pi / 2) :
    ContinuousOn (fun y : ℝ => Work.Spaces.mixed j i W z y) (Set.Icc c d) := by
  have hC1 : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.mixed j i W))
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS.CoercivityFix.Transfer.E2pkg.contDiffOn_uncurry_mixed_le
      Work.FTS.EllipticEst.isOpen_Q0 i j 1 (by omega) hW
  have hmaps : MapsTo (fun y : ℝ => (z, y)) (Set.Icc c d) Work.FTS.EllipticEst.Q0 :=
    fun y hy => ⟨hz, hc.trans_le hy.1, hy.2.trans_lt hd⟩
  have h := hC1.continuousOn.comp (continuousOn_const.prodMk continuousOn_id) hmaps
  simpa only [Function.comp_def, Function.uncurry_apply_pair, id_eq] using h

end Work.FTS_RegExport.RXT.Sys
