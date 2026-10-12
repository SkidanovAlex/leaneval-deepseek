import Mathlib
import Submission.Work.BoseFixB1S.CubeWindowKernel
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END
set_option synthInstance.maxSize 1024
set_option synthInstance.maxHeartbeats 400000

/-!
# `Work.BoseFixB1S.familyFormUnprojCube_eq_kernelForm`

The **cube-window** instance of the unprojected one-body family form / kernel-form identity
(`Work.BSKinetic.familyFormUnproj_eq_kernelForm`, which is stated for the corpus's *ball* window
family `bsWin ℓ u`): with the cube small factor `cubeWin M a u` (FS's own cosine bump `χ_M`, at
scale `a`, shift `u`) in place of `bsWin` and the cube overlap kernel
`convScaleCube M a z = (χ_M ⋆ χ_M)(z/a)` in place of `convScale ℓ`,

    `∫_u (2π)⁻³∫_p F‖p‖·‖kinFT(cubeWin M a u · ψ) p‖²`
      `= ∫_x ∫_y convScaleCube M a (x−y) · K_F(x−y) · ψ x · ψ y`.

The proof is a verbatim re-run of the ball argument (the Fubini/Plancherel computation of the
windowed mode form, then Fubini in `u`, then the `u`-integral of the window product) with three
cube-specific ingredients, all supplied here:

* the per-`u` kernel identity is *window-generic*
  (`Work.SmallBoxBridge.winModeForm_eq_kernelForm_general`), and
  `bsOneBodyUnprojCube M a F u ψ = winModeForm (cubeWin M a u) F ψ` is definitional;
* the `u`-integral of the window product is `integral_cubeWin_mul_cubeWin`
  (`Submission.Work.BoseFixB1S.CubeWindowKernel`, PROVED);
* the integrability bookkeeping: `cubeWin` is continuous with compact support
  (`support ⊆ closedBall (a•u) a`, since `χ_M` is supported in the unit ball), `convScaleCube` is
  continuous (as the convolution `χ_M ⋆ χ_M`, `HasCompactSupport.continuous_convolution_right`) and
  bounded by `1` (`conv3Small_abs_le_one`).
-/

noncomputable section

open MeasureTheory
open scoped ContDiff Topology Real BigOperators ENNReal Convolution

namespace Work.BoseFixB1S

open _root_.BoseGases Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-! ## 1. The cube window: continuity, compact support, support bound -/

/-- Support of the normalised cosine bump in the unit ball. -/
private lemma chiSmall_norm_le_one {M : ℕ} (hM : 1 ≤ M) {z : E3}
    (hz : Submission.BoseGases.chiSmall M z ≠ 0) : ‖z‖ ≤ 1 := by
  have hcoord : ∀ j : Fin 3, |z.ofLp j| ≤ 1 / 2 := fun j =>
    Submission.BoseGases.chiSmall_support_mem_abs_le hM hz j
  have hsq : ‖z‖ ^ 2 = ∑ j : Fin 3, |z.ofLp j| ^ 2 := by
    simpa using (PiLp.norm_sq_eq_of_L2 (β := fun _ : Fin 3 => ℝ) z)
  have hsum : (∑ j : Fin 3, |z.ofLp j| ^ 2) ≤ 3 * (1 / 2 : ℝ) ^ 2 := by
    calc (∑ j : Fin 3, |z.ofLp j| ^ 2) ≤ ∑ _j : Fin 3, (1 / 2 : ℝ) ^ 2 :=
          Finset.sum_le_sum (fun j _ => pow_le_pow_left₀ (abs_nonneg _) (hcoord j) 2)
      _ = 3 * (1 / 2 : ℝ) ^ 2 := by norm_num
  have hsq1 : ‖z‖ ^ 2 ≤ 1 := by rw [hsq]; nlinarith
  have hx0 : 0 ≤ ‖z‖ := norm_nonneg z
  have habs : |‖z‖| ≤ |(1 : ℝ)| := sq_le_sq.mp (by simpa using hsq1)
  simpa [abs_of_nonneg hx0] using habs

/-- `cubeWin M a u` is continuous. -/
private lemma continuous_cubeWin {M : ℕ} (hM : 1 ≤ M) (a : ℝ) (u : E3) :
    Continuous (cubeWin M a u) :=
  (Submission.BoseGases.chiSmall_continuous hM).comp (by fun_prop)

/-- A nonzero value of `cubeWin M a u x` forces `‖x − a•u‖ ≤ a`. -/
private lemma cubeWin_ne_zero_le_norm {M : ℕ} (hM : 1 ≤ M) {a : ℝ} (ha : 0 < a) {u x : E3}
    (h : cubeWin M a u x ≠ 0) : ‖x - a • u‖ ≤ a := by
  have h' : Submission.BoseGases.chiSmall M (a⁻¹ • x - u) ≠ 0 := h
  have h1 : ‖a⁻¹ • x - u‖ ≤ 1 := chiSmall_norm_le_one hM h'
  have hsm : x - a • u = a • (a⁻¹ • x - u) := by
    rw [smul_sub, smul_smul, mul_inv_cancel₀ (ne_of_gt ha), one_smul]
  rw [hsm, norm_smul, Real.norm_eq_abs, abs_of_pos ha]
  calc a * ‖a⁻¹ • x - u‖ ≤ a * 1 := mul_le_mul_of_nonneg_left h1 (le_of_lt ha)
    _ = a := by ring

/-- `cubeWin M a u` has compact support (`a > 0`), since `χ_M` is supported in the unit ball. -/
private lemma cubeWin_hasCompactSupport {M : ℕ} (hM : 1 ≤ M) {a : ℝ} (ha : 0 < a) (u : E3) :
    HasCompactSupport (cubeWin M a u) := by
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (a • u) a) ?_
  rw [Function.support_subset_iff]
  intro x hx
  rw [Metric.mem_closedBall, dist_eq_norm]
  exact cubeWin_ne_zero_le_norm hM ha hx

/-- `x ↦ cubeWin M a u x * ψ x` is integrable for smooth compactly supported `ψ`. -/
private lemma integrable_cubeWin_mul {M : ℕ} (hM : 1 ≤ M) {a : ℝ} (ha : 0 < a) (u : E3)
    {ψ : E3 → ℝ} (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) :
    MeasureTheory.Integrable (fun x : E3 => cubeWin M a u x * ψ x) :=
  ((continuous_cubeWin hM a u).mul hψ.continuous).integrable_of_hasCompactSupport
    ((cubeWin_hasCompactSupport hM ha u).mul_right)

/-! ## 2. The cube overlap kernel: bounded by `1`, and continuous -/

/-- `convScaleCube M a z = conv3Small M (a⁻¹ • z)`, definitionally. -/
private lemma convScaleCube_eq_conv3Small (M : ℕ) (a : ℝ) (z : E3) :
    convScaleCube M a z = Submission.BoseGases.conv3Small M (a⁻¹ • z) := rfl

/-- `|convScaleCube M a z| ≤ 1`. -/
private lemma abs_convScaleCube_le_one (M : ℕ) (hM : 1 ≤ M) (a : ℝ) (z : E3) :
    |convScaleCube M a z| ≤ 1 := by
  rw [convScaleCube_eq_conv3Small]
  exact Submission.BoseGases.conv3Small_abs_le_one hM _

/-- `conv3Small M = χ_M ⋆ χ_M` (mathlib's convolution). -/
private lemma conv3Small_eq_convolution (M : ℕ) :
    Submission.BoseGases.conv3Small M
      = (Submission.BoseGases.chiSmall M ⋆ Submission.BoseGases.chiSmall M) := by
  funext x
  rw [Submission.BoseGases.conv3Small, MeasureTheory.convolution_def]
  simp [ContinuousLinearMap.lsmul_apply]

/-- `conv3Small M` is continuous. -/
private lemma continuous_conv3Small (M : ℕ) (hM : 1 ≤ M) :
    Continuous (Submission.BoseGases.conv3Small M) := by
  rw [conv3Small_eq_convolution M]
  exact (Submission.BoseGases.chiSmall_hasCompactSupport hM).continuous_convolution_right
    (L := ContinuousLinearMap.lsmul ℝ ℝ)
    ((Submission.BoseGases.chiSmall_continuous hM).locallyIntegrable)
    (Submission.BoseGases.chiSmall_continuous hM)

/-- `convScaleCube M a` is continuous. -/
private lemma continuous_convScaleCube (M : ℕ) (hM : 1 ≤ M) (a : ℝ) :
    Continuous (convScaleCube M a) := by
  change Continuous (fun z : E3 => Submission.BoseGases.conv3Small M (a⁻¹ • z))
  exact (continuous_conv3Small M hM).comp (by fun_prop)

/-! ## 3. The integrands of the Fubini computation -/

/-- The family/kernel integrand at a triple `(u,x,y)`. -/
private noncomputable def ckiFam (M : ℕ) (a : ℝ) (F : ℝ → ℝ) (ψ : E3 → ℝ) (u x y : E3) : ℝ :=
  cubeWin M a u x * ψ x * (kinKernel F (x - y) * (cubeWin M a u y * ψ y))

/-- The `(x,y)`-integrand of the right hand side. -/
private noncomputable def ckiFinal (M : ℕ) (a : ℝ) (F : ℝ → ℝ) (ψ : E3 → ℝ) (z : E3 × E3) : ℝ :=
  kinKernel F (z.1 - z.2) * (ψ z.1 * (ψ z.2 * convScaleCube M a (z.1 - z.2)))

/-- The two-slot kernel pairing `g(z₁)·(K_F(z₁−z₂)·g(z₂))` is integrable for bounded kernel
`K_F` (`kinKernel_bdd`) and integrable `g`: dominate by `C·‖g z₁‖·‖g z₂‖` and use Tonelli. -/
private lemma integrable_mul_kernel_pair {F : ℝ → ℝ} {g : E3 → ℝ}
    (hF : MeasureTheory.Integrable (fun p : E3 => F ‖p‖)) (hg : MeasureTheory.Integrable g) :
    MeasureTheory.Integrable
      (fun z : E3 × E3 => g z.1 * (kinKernel F (z.1 - z.2) * g z.2))
      (volume.prod volume) := by
  have hKbd : ∀ w : E3,
      ‖kinKernel F w‖ ≤ ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3, ‖F ‖p‖‖ :=
    fun w => Work.SmallBoxBridge.Resolve.kinKernel_bdd F hF w
  have hmaj : MeasureTheory.Integrable
      (fun z : E3 × E3 =>
        (((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3, ‖F ‖p‖‖) * (‖g z.1‖ * ‖g z.2‖))
      (volume.prod volume) :=
    (hg.norm.mul_prod hg.norm).const_mul _
  refine MeasureTheory.Integrable.mono' hmaj ?_ ?_
  · exact (hg.aestronglyMeasurable.comp_fst).mul
      (((Work.SmallBoxBridge.Resolve.kinKernel_stronglyMeasurable hF).comp_measurable
        (measurable_fst.sub measurable_snd)).aestronglyMeasurable.mul
        (hg.aestronglyMeasurable.comp_snd))
  · filter_upwards with z
    calc ‖g z.1 * (kinKernel F (z.1 - z.2) * g z.2)‖
        = ‖g z.1‖ * ‖kinKernel F (z.1 - z.2) * g z.2‖ := norm_mul _ _
      _ ≤ ‖g z.1‖ * (‖kinKernel F (z.1 - z.2)‖ * ‖g z.2‖) :=
          mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg _)
      _ ≤ ‖g z.1‖ * ((((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3, ‖F ‖p‖‖) * ‖g z.2‖) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (hKbd _) (norm_nonneg _)) (norm_nonneg _)
      _ = (((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3, ‖F ‖p‖‖) * (‖g z.1‖ * ‖g z.2‖) := by ring

/-- The slice (`u` fixed) integrability of the cube family integrand. -/
private lemma integrable_ckiFamSlice {M : ℕ} (hM : 1 ≤ M) {a : ℝ} (ha : 0 < a) {F : ℝ → ℝ}
    (hFi : MeasureTheory.Integrable (fun p : E3 => F ‖p‖)) {ψ : E3 → ℝ}
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) (u : E3) :
    MeasureTheory.Integrable (fun z : E3 × E3 => ckiFam M a F ψ u z.1 z.2)
      ((volume : Measure E3).prod (volume : Measure E3)) := by
  refine integrable_mul_kernel_pair (F := F) (g := fun x : E3 => cubeWin M a u x * ψ x)
    hFi (integrable_cubeWin_mul hM ha u hψ hcs)

/-- The right-hand-side double integrand is integrable: it is bounded (the kernel through
`kinKernel_bdd`, `|convScaleCube| ≤ 1`) and supported in the compact square determined by the
support of `ψ`. -/
private lemma integrable_ckiFinal {M : ℕ} (hM : 1 ≤ M) {a : ℝ} (ha : 0 < a) {F : ℝ → ℝ}
    (hFi : MeasureTheory.Integrable (fun p : E3 => F ‖p‖)) {ψ : E3 → ℝ}
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) :
    MeasureTheory.Integrable (ckiFinal M a F ψ)
      ((volume : Measure E3).prod (volume : Measure E3)) := by
  obtain ⟨R, hψsupp⟩ := Work.BSKinetic.HasCompactSupport.exists_norm_le hcs
  obtain ⟨Cψ, hCψ⟩ := hcs.exists_bound_of_continuous hψ.continuous
  set B : ℝ := ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3, ‖F ‖p‖‖ with hB
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have hCψ0 : 0 ≤ Cψ := le_trans (norm_nonneg (ψ 0)) (hCψ 0)
  have hkey : ∀ z : E3 × E3, ‖ckiFinal M a F ψ z‖ ≤ B * Cψ * (Cψ * 1) := by
    intro z
    have h1 : ‖kinKernel F (z.1 - z.2)‖ ≤ B := by
      rw [hB]; exact Work.SmallBoxBridge.Resolve.kinKernel_bdd F hFi _
    have h2 : ‖ψ z.1‖ ≤ Cψ := hCψ z.1
    have h3 : ‖ψ z.2‖ ≤ Cψ := hCψ z.2
    have h4 : ‖convScaleCube M a (z.1 - z.2)‖ ≤ 1 := by
      rw [Real.norm_eq_abs]; exact abs_convScaleCube_le_one M hM a _
    calc ‖ckiFinal M a F ψ z‖
        = ‖kinKernel F (z.1 - z.2)‖ *
            (‖ψ z.1‖ * (‖ψ z.2‖ * ‖convScaleCube M a (z.1 - z.2)‖)) := by
          simp only [ckiFinal, norm_mul]
      _ ≤ B * (Cψ * (Cψ * 1)) := by
          refine mul_le_mul h1 (mul_le_mul h2 (mul_le_mul h3 h4 (norm_nonneg _) hCψ0)
            (by positivity) hCψ0) (by positivity) hB0
      _ = B * Cψ * (Cψ * 1) := by ring
  have hmeas : AEStronglyMeasurable (ckiFinal M a F ψ)
      ((volume : Measure E3).prod (volume : Measure E3)) := by
    have h1 : AEStronglyMeasurable (fun z : E3 × E3 => kinKernel F (z.1 - z.2))
        ((volume : Measure E3).prod (volume : Measure E3)) :=
      Work.BSKinetic.aestronglyMeasurable_kinKernel_sub hFi
    have h2 : AEStronglyMeasurable
        (fun z : E3 × E3 => ψ z.1 * (ψ z.2 * convScaleCube M a (z.1 - z.2)))
        ((volume : Measure E3).prod (volume : Measure E3)) :=
      ((hψ.continuous.comp continuous_fst).mul
        ((hψ.continuous.comp continuous_snd).mul
          ((continuous_convScaleCube M hM a).comp
            (continuous_fst.sub continuous_snd)))).aestronglyMeasurable
    have hmul : AEStronglyMeasurable ((fun z : E3 × E3 => kinKernel F (z.1 - z.2)) *
          fun z : E3 × E3 => ψ z.1 * (ψ z.2 * convScaleCube M a (z.1 - z.2)))
        ((volume : Measure E3).prod (volume : Measure E3)) := h1.mul h2
    unfold ckiFinal
    exact hmul
  refine Work.BSKinetic.integrable_of_compact_support
    ⟨Metric.closedBall 0 R ×ˢ Metric.closedBall 0 R,
      (isCompact_closedBall 0 R).prod (isCompact_closedBall 0 R), ?_⟩ hmeas
    ⟨B * Cψ * (Cψ * 1), hkey⟩
  intro z hz
  have hz1 : ψ z.1 ≠ 0 := by
    intro h0; refine hz ?_
    simp only [ckiFinal, h0, mul_zero, zero_mul]
  have hz2 : ψ z.2 ≠ 0 := by
    intro h0; refine hz ?_
    simp only [ckiFinal, h0, zero_mul, mul_zero]
  simp only [Set.mem_prod, Metric.mem_closedBall, dist_zero_right]
  exact ⟨hψsupp z.1 hz1, hψsupp z.2 hz2⟩

/-- The joint (`u`-integrated) cube family integrand is `L¹`: bounded, a.e. strongly measurable,
and supported in the compact product of balls
`closedBall 0 (1 + a⁻¹R) × (closedBall 0 R × closedBall 0 R)`, where `R` bounds the support of
`ψ`: `ψ x ≠ 0` forces `‖x‖ ≤ R`, and `cubeWin M a u x ≠ 0` forces `‖x − a•u‖ ≤ a`, whence
`‖u‖ ≤ 1 + a⁻¹‖x‖`. -/
private lemma integrable_ckiFamJoint {M : ℕ} (hM : 1 ≤ M) {a : ℝ} (ha : 0 < a) {F : ℝ → ℝ}
    (hFi : MeasureTheory.Integrable (fun p : E3 => F ‖p‖))
    (ψ : E3 → ℝ) (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) :
    MeasureTheory.Integrable
      (fun w : E3 × (E3 × E3) => ckiFam M a F ψ w.1 w.2.1 w.2.2)
      ((volume : Measure E3).prod ((volume : Measure E3).prod (volume : Measure E3))) := by
  classical
  obtain ⟨R, hψsupp⟩ := Work.BSKinetic.HasCompactSupport.exists_norm_le hcs
  obtain ⟨Cψ, hCψ⟩ := hcs.exists_bound_of_continuous hψ.continuous
  set Mψ : ℝ := max Cψ 0 with hMψdef
  have hMψnn : 0 ≤ Mψ := by rw [hMψdef]; exact le_max_right _ _
  have hψM : ∀ x : E3, ‖ψ x‖ ≤ Mψ := by
    intro x; rw [hMψdef]; exact le_trans (hCψ x) (le_max_left _ _)
  obtain ⟨Cc, hCc⟩ := (Submission.BoseGases.chiSmall_hasCompactSupport hM).exists_bound_of_continuous
    (Submission.BoseGases.chiSmall_continuous hM)
  have hCcnn : 0 ≤ Cc := le_trans (norm_nonneg (Submission.BoseGases.chiSmall M 0)) (hCc 0)
  have hcw : ∀ (u x : E3), |cubeWin M a u x| ≤ Cc := fun u x => by
    simpa only [cubeWin, Real.norm_eq_abs] using hCc (a⁻¹ • x - u)
  set Kval : ℝ := ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3, ‖F ‖p‖‖ with hKvaldef
  have hKbd : ∀ z : E3, ‖kinKernel F z‖ ≤ Kval := by
    intro z; rw [hKvaldef]; exact Work.SmallBoxBridge.Resolve.kinKernel_bdd F hFi z
  have hKnn : 0 ≤ Kval := le_trans (norm_nonneg (kinKernel F 0)) (hKbd 0)
  set Kc : Set (E3 × (E3 × E3)) :=
      Metric.closedBall (0:E3) (1 + a⁻¹ * R) ×ˢ
        (Metric.closedBall (0:E3) R ×ˢ Metric.closedBall (0:E3) R) with hKcdef
  have hKcompact : IsCompact Kc := by
    rw [hKcdef]
    exact (isCompact_closedBall _ _).prod
      ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))
  have hsupp : ∀ w : E3 × (E3 × E3),
      ckiFam M a F ψ w.1 w.2.1 w.2.2 ≠ 0 → w ∈ Kc := by
    intro w hw
    rw [hKcdef]
    obtain ⟨hA, hB⟩ := mul_ne_zero_iff.mp hw
    obtain ⟨hcx, hψx⟩ := mul_ne_zero_iff.mp hA
    obtain ⟨_hK, hBy⟩ := mul_ne_zero_iff.mp hB
    obtain ⟨hcy, hψy⟩ := mul_ne_zero_iff.mp hBy
    have hxR : ‖w.2.1‖ ≤ R := hψsupp w.2.1 hψx
    have hyR : ‖w.2.2‖ ≤ R := hψsupp w.2.2 hψy
    have hnsub : ‖w.2.1 - a • w.1‖ ≤ a := cubeWin_ne_zero_le_norm hM ha hcx
    have huU : ‖w.1‖ ≤ 1 + a⁻¹ * R := by
      have h1 : a * ‖w.1‖ ≤ a + R := by
        have h2 : ‖a • w.1‖ ≤ ‖w.2.1‖ + ‖w.2.1 - a • w.1‖ := by
          simpa using (norm_sub_le w.2.1 (w.2.1 - a • w.1))
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha] at h2
        linarith
      have h4 : a * (1 + a⁻¹ * R) = a + R := by
        rw [mul_add, mul_one, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt ha), one_mul]
      rw [← h4] at h1
      exact le_of_mul_le_mul_left h1 ha
    refine ⟨?_, ?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_zero_right]; exact huU
    · rw [Metric.mem_closedBall, dist_zero_right]; exact hxR
    · rw [Metric.mem_closedBall, dist_zero_right]; exact hyR
  have hbound : ∀ w : E3 × (E3 × E3),
      ‖ckiFam M a F ψ w.1 w.2.1 w.2.2‖ ≤ Cc * Mψ * (Kval * (Cc * Mψ)) := by
    intro w
    have hcx : |cubeWin M a w.1 w.2.1| ≤ Cc := hcw w.1 w.2.1
    have hcy : |cubeWin M a w.1 w.2.2| ≤ Cc := hcw w.1 w.2.2
    have hψx : |ψ w.2.1| ≤ Mψ := by simpa [Real.norm_eq_abs] using hψM w.2.1
    have hψy : |ψ w.2.2| ≤ Mψ := by simpa [Real.norm_eq_abs] using hψM w.2.2
    have hKz : |kinKernel F (w.2.1 - w.2.2)| ≤ Kval := by
      simpa [Real.norm_eq_abs] using hKbd (w.2.1 - w.2.2)
    simp only [ckiFam, Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (mul_le_mul hcx hψx (abs_nonneg _) hCcnn)
      (mul_le_mul hKz (mul_le_mul hcy hψy (abs_nonneg _) hCcnn)
        (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hKnn)
      (mul_nonneg (abs_nonneg _) (mul_nonneg (abs_nonneg _) (abs_nonneg _)))
      (mul_nonneg hCcnn hMψnn)
  have hχc : Continuous (Submission.BoseGases.chiSmall M) :=
    Submission.BoseGases.chiSmall_continuous hM
  have hc1 : Continuous (fun w : E3 × (E3 × E3) => cubeWin M a w.1 w.2.1) :=
    hχc.comp ((continuous_snd.fst).const_smul (a⁻¹) |>.sub continuous_fst)
  have hc2 : Continuous (fun w : E3 × (E3 × E3) => ψ w.2.1) :=
    hψ.continuous.comp continuous_snd.fst
  have hc3 : Continuous (fun w : E3 × (E3 × E3) => cubeWin M a w.1 w.2.2) :=
    hχc.comp ((continuous_snd.snd).const_smul (a⁻¹) |>.sub continuous_fst)
  have hc4 : Continuous (fun w : E3 × (E3 × E3) => ψ w.2.2) :=
    hψ.continuous.comp continuous_snd.snd
  have hKmeas : AEStronglyMeasurable (fun w : E3 × (E3 × E3) => kinKernel F (w.2.1 - w.2.2))
      ((volume : Measure E3).prod ((volume : Measure E3).prod (volume : Measure E3))) := by
    have hsub : Measure.QuasiMeasurePreserving (fun q : E3 × E3 => q.1 - q.2)
        ((volume : Measure E3).prod (volume : Measure E3)) (volume : Measure E3) :=
      quasiMeasurePreserving_sub_of_right_invariant volume volume
    have h1 : AEStronglyMeasurable (fun q : E3 × E3 => kinKernel F (q.1 - q.2))
        ((volume : Measure E3).prod (volume : Measure E3)) :=
      (Work.SmallBoxBridge.Resolve.kinKernel_aestronglyMeasurable F hFi)
        |>.comp_quasiMeasurePreserving hsub
    have h2 := h1.comp_quasiMeasurePreserving
      (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure E3))
        (ν := (volume : Measure E3).prod (volume : Measure E3)))
    simpa only [Function.comp_def] using h2
  have haes : AEStronglyMeasurable (fun w : E3 × (E3 × E3) =>
      ckiFam M a F ψ w.1 w.2.1 w.2.2)
      ((volume : Measure E3).prod ((volume : Measure E3).prod (volume : Measure E3))) :=
    ((hc1.aestronglyMeasurable.mul hc2.aestronglyMeasurable).mul
      (hKmeas.mul (hc3.aestronglyMeasurable.mul hc4.aestronglyMeasurable)))
  exact Work.BSKinetic.integrable_of_compact_support ⟨Kc, hKcompact, hsupp⟩ haes
    ⟨Cc * Mψ * (Kval * (Cc * Mψ)), hbound⟩

/-! ## 4. The main identity -/

/-- The unprojected cube family form at fixed `u` *is* the windowed mode form of the window
`cubeWin M a u` (both are `(2π)⁻³∫_p F‖p‖·‖kinFT(χ_u·ψ) p‖²`, definitionally). -/
private lemma bsOneBodyUnprojCube_eq_winModeForm (M : ℕ) (a : ℝ) (F : ℝ → ℝ) (u : E3)
    (ψ : E3 → ℝ) :
    bsOneBodyUnprojCube M a F u ψ = Submission.BoseGases.winModeForm (cubeWin M a u) F ψ := rfl

theorem familyFormUnprojCube_eq_kernelForm (M : ℕ) (hM : 1 ≤ M) {a : ℝ} (ha : 0 < a) {F : ℝ → ℝ}
    (ψ : EuclideanSpace ℝ (Fin 3) → ℝ) (hψ : ContDiff ℝ (⊤ : ENat) ψ)
    (hcs : HasCompactSupport ψ)
    (hFi : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) => F ‖p‖))
    (hFm : ∀ r : ℝ, 0 ≤ F r) :
    Work.BoseFixB1S.bsFamilyFormUnprojCube M a F ψ
      = ∫ x : EuclideanSpace ℝ (Fin 3), ∫ y : EuclideanSpace ℝ (Fin 3),
          Work.BoseFixB1S.convScaleCube M a (x - y) * Submission.BoseGases.kinKernel F (x - y)
            * ψ x * ψ y := by
  have hJoint : MeasureTheory.Integrable
      (fun w : E3 × (E3 × E3) => ckiFam M a F ψ w.1 w.2.1 w.2.2)
      ((volume : Measure E3).prod ((volume : Measure E3).prod (volume : Measure E3))) :=
    integrable_ckiFamJoint hM ha hFi ψ hψ hcs
  have hSlice : ∀ u : E3, MeasureTheory.Integrable
      (fun z : E3 × E3 => ckiFam M a F ψ u z.1 z.2)
      ((volume : Measure E3).prod (volume : Measure E3)) :=
    fun u => integrable_ckiFamSlice hM ha hFi hψ hcs u
  have hfin : MeasureTheory.Integrable (ckiFinal M a F ψ)
      ((volume : Measure E3).prod (volume : Measure E3)) :=
    integrable_ckiFinal hM ha hFi hψ hcs
  calc bsFamilyFormUnprojCube M a F ψ
      = ∫ u : E3, ∫ x : E3, (cubeWin M a u x * ψ x) *
          (∫ y : E3, kinKernel F (x - y) * (cubeWin M a u y * ψ y)) := by
        rw [bsFamilyFormUnprojCube]
        apply integral_congr_ae
        filter_upwards with u
        rw [bsOneBodyUnprojCube_eq_winModeForm]
        exact Work.SmallBoxBridge.winModeForm_eq_kernelForm_general (cubeWin M a u) ψ F hFi
          (integrable_cubeWin_mul hM ha u hψ hcs)
    _ = ∫ u : E3, ∫ z : E3 × E3, ckiFam M a F ψ u z.1 z.2 := by
        apply integral_congr_ae
        filter_upwards with u
        have h1 : (∫ x : E3, (cubeWin M a u x * ψ x) *
              (∫ y : E3, kinKernel F (x - y) * (cubeWin M a u y * ψ y)))
            = ∫ x : E3, ∫ y : E3, ckiFam M a F ψ u x y := by
          apply integral_congr_ae
          filter_upwards with x
          simp only [ckiFam]
          rw [MeasureTheory.integral_const_mul]
        have h2 : (∫ x : E3, ∫ y : E3, ckiFam M a F ψ u x y)
            = ∫ z : E3 × E3, ckiFam M a F ψ u z.1 z.2 :=
          (MeasureTheory.integral_prod (fun z : E3 × E3 => ckiFam M a F ψ u z.1 z.2)
            (hSlice u)).symm
        exact h1.trans h2
    _ = ∫ z : E3 × E3, ∫ u : E3, ckiFam M a F ψ u z.1 z.2 :=
        MeasureTheory.integral_integral_swap (f := fun (u : E3) (z : E3 × E3) =>
          ckiFam M a F ψ u z.1 z.2) hJoint
    _ = ∫ z : E3 × E3, ckiFinal M a F ψ z := by
        apply integral_congr_ae
        filter_upwards with z
        have hfun : (fun u : E3 => ckiFam M a F ψ u z.1 z.2)
            = fun u : E3 => (kinKernel F (z.1 - z.2) * ψ z.1 * ψ z.2) *
                (cubeWin M a u z.1 * cubeWin M a u z.2) := by
          funext u; simp only [ckiFam]; ring
        rw [hfun, MeasureTheory.integral_const_mul,
          integral_cubeWin_mul_cubeWin M hM (ne_of_gt ha) z.1 z.2]
        simp only [ckiFinal]
        ring
    _ = ∫ x : E3, ∫ y : E3, ckiFinal M a F ψ (x, y) :=
        MeasureTheory.integral_prod (fun z : E3 × E3 => ckiFinal M a F ψ z) hfin
    _ = ∫ x : E3, ∫ y : E3,
          kinKernel F (x - y) * (ψ x * (ψ y * convScaleCube M a (x - y))) := by
        apply integral_congr_ae
        filter_upwards with x
        apply integral_congr_ae
        filter_upwards with y
        simp only [ckiFinal]
    _ = ∫ x : E3, ∫ y : E3,
          convScaleCube M a (x - y) * kinKernel F (x - y) * ψ x * ψ y := by
        apply integral_congr_ae
        filter_upwards with x
        apply integral_congr_ae
        filter_upwards with y
        ring

end Work.BoseFixB1S
