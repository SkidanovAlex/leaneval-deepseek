import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Submission.Work.BoseFixB1.SectorAux.chiSmallB_lipschitz
import Submission.Work.BoseFixB1S.chiSmallB_eq_zero_of_volume_dlBox_eq_zero
import Submission.Work.BoseFixB1S.corrMarg.measurable_and_bound_boxMean
import Submission.Work.BoseFixB1S.corrPlanchMarg
import Submission.Work.BoseFixB1S.kineticCruxParsed
import Submission.Work.BoseFixB1S.weightedPlancherelKinFT
import Submission.Work.BoseFixB1S.win.chiSmallB_kinFT_decay
import Submission.Work.BoseFixR.SmoothApproxGradient
import Submission.Work.BoseKinLoc.Momentum.kinFT_l1l2_plancherel
import Submission.Work.LocRepoint.chiSmallB_sq_integral_u
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal ContDiff Pointwise NNReal

namespace Work.BoseFixB1S.CubeWindow

local notation "E3" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## 1. Continuity and support of the cube window -/

/-- Joint continuity of `(u,z) ↦ χ_{B(u)}(z) = chiSmallB M ℓ d u z`. -/
private lemma continuous_uncurry_chiSmallB (M : ℕ) (hM : 1 ≤ M) (ℓ d : ℝ) :
    Continuous (Function.uncurry (Submission.BoseGases.chiSmallB M ℓ d)) := by
  have h1 : Continuous (fun p : E3 × E3 => Submission.BoseGases.chiScale ℓ p.2) :=
    (Submission.BoseGases.chiScale_continuous ℓ).comp continuous_snd
  have h2 : Continuous (fun p : E3 × E3 =>
      Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • p.2 - p.1)) :=
    (Submission.BoseGases.chiSmall_continuous hM).comp
      ((continuous_snd.const_smul ((ℓ * d)⁻¹)).sub continuous_fst)
  show Continuous (fun p : E3 × E3 => Submission.BoseGases.chiScale ℓ p.2 *
    Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • p.2 - p.1))
  exact h1.mul h2

/-- **Geometric core of the `u`-support.**  If `χ_{B(u)}` does not vanish at `z`, then the sliding
centre `u` lies in the *fixed* cube `acube ((1+d)/d)`.  Coordinate computation: `χ_{B(u)}(z) ≠ 0`
forces `z ∈ acube ℓ` and `z - (ℓd)•u ∈ acube (ℓd)`, hence `ℓd|u_j| ≤ ℓ(1+d)/2`. -/
private lemma mem_acube_u_of_chiSmallB_ne_zero {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ)
    (hd : 0 < d) {u z : E3} (h : Submission.BoseGases.chiSmallB M ℓ d u z ≠ 0) :
    u ∈ Submission.BoseGases.acube ((1 + d) / d) := by
  have hmem : z ∈ Submission.BoseGases.dlBox ℓ d u :=
    Work.BoseFixB1S.chiSmallB_support_subset_dlBox hM hℓ hd u (Function.mem_support.mpr h)
  rw [Submission.BoseGases.mem_dlBox_iff] at hmem
  obtain ⟨hz, hzu⟩ := hmem
  rw [Submission.BoseGases.mem_acube_iff] at hz hzu ⊢
  have hld : 0 < ℓ * d := mul_pos hℓ hd
  intro m
  have hzm := hz m
  have hzum := hzu m
  simp only [Set.mem_Icc] at hzm hzum
  have h2 : |z.ofLp m - ℓ * d * u.ofLp m| ≤ ℓ * d / 2 := by
    have he : (z - (ℓ * d) • u).ofLp m = z.ofLp m - ℓ * d * u.ofLp m := by
      simp [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    rw [he] at hzum
    exact abs_le.mpr ⟨by linarith [hzum.1], by linarith [hzum.2]⟩
  have h1 : |z.ofLp m| ≤ ℓ / 2 := abs_le.mpr ⟨by linarith [hzm.1], by linarith [hzm.2]⟩
  have h4 : ℓ * d * |u.ofLp m| ≤ ℓ * (1 + d) / 2 := by
    have hrew : ℓ * d * |u.ofLp m| = |ℓ * d * u.ofLp m| := by
      rw [abs_mul, abs_of_pos hld, mul_comm]
    rw [hrew]
    have htri : |ℓ * d * u.ofLp m| - |z.ofLp m| ≤ |ℓ * d * u.ofLp m - z.ofLp m| :=
      le_trans (le_abs_self _) (abs_abs_sub_abs_le_abs_sub (ℓ * d * u.ofLp m) (z.ofLp m))
    have h2' : |ℓ * d * u.ofLp m - z.ofLp m| ≤ ℓ * d / 2 := by
      rw [abs_sub_comm]; exact h2
    linarith
  have hkey : |u.ofLp m| ≤ (1 + d) / (2 * d) := by
    have hstep : |u.ofLp m| ≤ (ℓ * (1 + d) / 2) / (ℓ * d) := by
      rw [le_div_iff₀ hld]; linarith
    have hrew : (ℓ * (1 + d) / 2) / (ℓ * d) = (1 + d) / (2 * d) := by field_simp
    rwa [hrew] at hstep
  have hb : ((1 + d) / d) / 2 = (1 + d) / (2 * d) := by ring
  rw [Set.mem_Icc]
  constructor
  · have hneg : -((1 + d) / d) / 2 = -((1 + d) / (2 * d)) := by rw [neg_div, hb]
    rw [hneg]; linarith [neg_abs_le (u.ofLp m)]
  · rw [hb]; linarith [le_abs_self (u.ofLp m)]

/-- **The `u`-support of the cube window**: off the fixed cube `acube ((1+d)/d)` the whole family
`u ↦ χ_{B(u)}` vanishes. -/
lemma chiSmallB_eq_zero_of_not_mem_acube_u {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ)
    (hd : 0 < d) {u : E3} (hu : u ∉ Submission.BoseGases.acube ((1 + d) / d)) (z : E3) :
    Submission.BoseGases.chiSmallB M ℓ d u z = 0 := by
  by_contra h
  exact hu (mem_acube_u_of_chiSmallB_ne_zero hM hℓ hd h)

/-! ## 2. A.e. strong measurability of the windowed cut word (abstract window) -/

/-- **A.e. strong measurability of `u ↦ bsW (fsKinCoeff c) (χ_u · W u)`** for a jointly continuous
window `χ` and a jointly measurable kernel `W` (the proof only uses joint continuity of the window
and joint measurability of the kernel; it is the parametric-integral device
`MeasureTheory.StronglyMeasurable.integral_prod_right'` applied twice, first to `kinFT` in `z` and
then to `bsW` in `p`). -/
private theorem aemeasurable_bsW_windowCube {χ : E3 → E3 → ℝ} {c : ℝ}
    (hχc : Continuous (Function.uncurry χ)) {W : E3 → E3 → ℝ}
    (hW : Measurable (Function.uncurry W)) :
    AEMeasurable
      (fun u : E3 =>
        Work.BSKinetic.Decomp.bsW (Submission.BoseGases.fsKinCoeff c)
          (fun z : E3 => χ u z * W u z))
      (volume : Measure E3) := by
  classical
  let J : (E3 × E3) × E3 → ℂ := fun q =>
    Complex.exp (-(Complex.I * (inner ℝ q.1.2 q.2 : ℂ))) *
      ((χ q.1.1 q.2 * W q.1.1 q.2 : ℝ) : ℂ)
  have hprojC : Continuous (fun q : (E3 × E3) × E3 => (q.1.1, q.2)) :=
    (continuous_fst.comp continuous_fst).prodMk continuous_snd
  have hχsm : StronglyMeasurable (fun q : (E3 × E3) × E3 => χ q.1.1 q.2) :=
    (hχc.comp hprojC).stronglyMeasurable
  have hWsm : StronglyMeasurable (fun q : (E3 × E3) × E3 => W q.1.1 q.2) :=
    (hW.comp hprojC.measurable).stronglyMeasurable
  have hprod : StronglyMeasurable (fun q : (E3 × E3) × E3 => χ q.1.1 q.2 * W q.1.1 q.2) :=
    hχsm.mul hWsm
  have hJ : StronglyMeasurable J := by
    refine (by fun_prop : Continuous (fun q : (E3 × E3) × E3 =>
      Complex.exp (-(Complex.I * (inner ℝ q.1.2 q.2 : ℂ))))).stronglyMeasurable.mul ?_
    exact Complex.continuous_ofReal.comp_stronglyMeasurable hprod
  have hK : StronglyMeasurable (fun q : E3 × E3 => ∫ z : E3, J (q, z)) :=
    hJ.integral_prod_right' (ν := volume)
  have hfs : Continuous (fun r : ℝ => Submission.BoseGases.fsKinCoeff c r) := by
    unfold Submission.BoseGases.fsKinCoeff
    fun_prop
  have hG : StronglyMeasurable (fun q : E3 × E3 =>
      Submission.BoseGases.fsKinCoeff c ‖q.2‖ * ‖(∫ z : E3, J (q, z))‖ ^ 2) :=
    ((hfs.comp continuous_norm).measurable.comp measurable_snd).stronglyMeasurable.mul
      (hK.norm.pow 2)
  have hfinal : StronglyMeasurable (fun u : E3 =>
      ∫ p : E3, Submission.BoseGases.fsKinCoeff c ‖p‖ * ‖(∫ z : E3, J ((u, p), z))‖ ^ 2) :=
    hG.integral_prod_right' (ν := volume)
  simpa only [Work.BSKinetic.Decomp.bsW, Work.BSKinetic.Decomp.bsPsi,
    Submission.BoseGases.kinFT, J] using hfinal.aemeasurable

/-! ## 3. Elementary facts about the weighted kinetic symbol -/

/-- `bsW` at the nonnegative symbol `fsKinCoeff c` is nonnegative. -/
private lemma bsW_fsKinCoeff_nonneg_cw (c : ℝ) (h : E3 → ℝ) :
    0 ≤ Work.BSKinetic.Decomp.bsW (Submission.BoseGases.fsKinCoeff c) h := by
  rw [Work.BSKinetic.Decomp.bsW]
  exact integral_nonneg fun p =>
    mul_nonneg (Submission.BoseGases.fsKinCoeff_nonneg c ‖p‖) (sq_nonneg _)

/-- The cut kinetic word of the zero state vanishes. -/
private lemma bsW_zero_cw (F : ℝ → ℝ) :
    Work.BSKinetic.Decomp.bsW F (fun _ : E3 => (0 : ℝ)) = 0 := by
  rw [Work.BSKinetic.Decomp.bsW]
  simp [Work.BSKinetic.Decomp.bsPsi, Submission.BoseGases.kinFT]

/-- **Uniform-in-`u` sup and Lipschitz bounds for the cube window.** -/
theorem chiSmallB_supLipschitz_uniform {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) :
    ∃ Mχ Lχ : ℝ, 0 ≤ Mχ ∧ 0 ≤ Lχ ∧
      (∀ u : E3, ∀ z : E3, |chiSmallB M ℓ d u z| ≤ Mχ) ∧
      (∀ u y t : E3, |chiSmallB M ℓ d u y - chiSmallB M ℓ d u t| ≤ Lχ * ‖y - t‖) := by
  obtain ⟨C, hC0, hC⟩ := Work.BoseFixB1B.exists_lipschitz_chi
  obtain ⟨L₁, hL₁0, hL₁⟩ := Work.BoseFixB1S.chiSmall_lipschitz (M := M) hM
  have hℓd : 0 < ℓ * d := mul_pos hℓ hd
  have hℓinv : 0 ≤ ℓ⁻¹ := inv_nonneg.mpr hℓ.le
  have hℓdinv : 0 ≤ (ℓ * d)⁻¹ := inv_nonneg.mpr hℓd.le
  refine ⟨chiSupAbs * chiSmallDecay M,
    C * ℓ⁻¹ * chiSmallDecay M + chiSupAbs * (L₁ * (ℓ * d)⁻¹), ?_, ?_, ?_, ?_⟩
  · exact mul_nonneg chiSupAbs_nonneg (chiSmallDecay_nonneg M)
  · exact add_nonneg (mul_nonneg (mul_nonneg hC0 hℓinv) (chiSmallDecay_nonneg M))
      (mul_nonneg chiSupAbs_nonneg (mul_nonneg hL₁0 hℓdinv))
  · intro u z
    have h1 : |chiScale ℓ z| ≤ chiSupAbs := chiScale_abs_le_sup ℓ z
    have h2 : |chiSmall M ((ℓ * d)⁻¹ • z - u)| ≤ chiSmallDecay M :=
      chiSmall_decay_coord_le_decay hM _
    calc |chiSmallB M ℓ d u z| = |chiScale ℓ z| * |chiSmall M ((ℓ * d)⁻¹ • z - u)| := by
          rw [chiSmallB, abs_mul]
      _ ≤ chiSupAbs * chiSmallDecay M :=
          mul_le_mul h1 h2 (abs_nonneg _) chiSupAbs_nonneg
  · intro u y t
    have hA := Work.BoseFixB1.SectorAux.chiScale_lipschitz hC hℓ y t
    have hB := Work.BoseFixB1.SectorAux.chiSmall_smul_sub_lipschitz (M := M) hL₁ hℓd u y t
    have hBx : |chiSmall M ((ℓ * d)⁻¹ • y - u)| ≤ chiSmallDecay M :=
      chiSmall_decay_coord_le_decay hM _
    have hAy : |chiScale ℓ t| ≤ chiSupAbs := chiScale_abs_le_sup ℓ t
    have hkey : chiSmallB M ℓ d u y - chiSmallB M ℓ d u t
        = (chiScale ℓ y - chiScale ℓ t) * chiSmall M ((ℓ * d)⁻¹ • y - u)
          + chiScale ℓ t * (chiSmall M ((ℓ * d)⁻¹ • y - u)
              - chiSmall M ((ℓ * d)⁻¹ • t - u)) := by
      simp only [chiSmallB]
      ring
    rw [hkey]
    have h1 : |(chiScale ℓ y - chiScale ℓ t) * chiSmall M ((ℓ * d)⁻¹ • y - u)|
        ≤ (C * ℓ⁻¹ * ‖y - t‖) * chiSmallDecay M := by
      rw [abs_mul]
      exact mul_le_mul hA hBx (abs_nonneg _) (by positivity)
    have h2 : |chiScale ℓ t * (chiSmall M ((ℓ * d)⁻¹ • y - u)
          - chiSmall M ((ℓ * d)⁻¹ • t - u))|
        ≤ chiSupAbs * (L₁ * (ℓ * d)⁻¹ * ‖y - t‖) := by
      rw [abs_mul]
      exact mul_le_mul hAy hB (abs_nonneg _) chiSupAbs_nonneg
    calc |(chiScale ℓ y - chiScale ℓ t) * chiSmall M ((ℓ * d)⁻¹ • y - u)
          + chiScale ℓ t * (chiSmall M ((ℓ * d)⁻¹ • y - u)
              - chiSmall M ((ℓ * d)⁻¹ • t - u))|
        ≤ |(chiScale ℓ y - chiScale ℓ t) * chiSmall M ((ℓ * d)⁻¹ • y - u)|
          + |chiScale ℓ t * (chiSmall M ((ℓ * d)⁻¹ • y - u)
              - chiSmall M ((ℓ * d)⁻¹ • t - u))| := abs_add_le _ _
      _ ≤ (C * ℓ⁻¹ * ‖y - t‖) * chiSmallDecay M
          + chiSupAbs * (L₁ * (ℓ * d)⁻¹ * ‖y - t‖) := by linarith
      _ = (C * ℓ⁻¹ * chiSmallDecay M + chiSupAbs * (L₁ * (ℓ * d)⁻¹)) * ‖y - t‖ := by ring

/-- The `chiScale` factor vanishes outside the open ball of radius `ℓ/2`. -/
lemma chiScale_eq_zero_of_half_lt_norm' {ℓ : ℝ} (hℓ : 0 < ℓ) {z : E3} (hz : ℓ / 2 < ‖z‖) :
    chiScale ℓ z = 0 := by
  have h : (1 / 2 : ℝ) ≤ ‖(ℓ⁻¹ : ℝ) • z‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hℓ)]
    have he : ℓ⁻¹ * (ℓ / 2) = 1 / 2 := by field_simp
    rw [← he]
    exact mul_le_mul_of_nonneg_left hz.le (inv_pos.mpr hℓ).le
  have h2 : chi ((ℓ⁻¹ : ℝ) • z) = 0 := chi_eq_zero_of_half_le_norm _ h
  simpa only [chiScale] using h2

/-- **Uniform-in-`u` geometric bounds for the cube-windowed shifted states.** -/
theorem chiSmallB_mul_uniformBounds_self {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ)
    (hd : 0 < d) :
    ∀ w : E3 → ℝ, ContDiff ℝ (⊤ : ENat) w → ∀ C : ℝ,
      ∃ A L : ℝ, 0 ≤ A ∧ 0 ≤ L ∧
        ∀ cu : E3 → ℝ,
          (∀ u : E3, |cu u| ≤ C) → ∀ u : E3,
            (∀ z : E3, |chiSmallB M ℓ d u z * (w z - cu u)| ≤ A)
            ∧ (∀ y t : E3, |chiSmallB M ℓ d u y * (w y - cu u)
                  - chiSmallB M ℓ d u t * (w t - cu u)| ≤ L * ‖y - t‖)
            ∧ (∀ z : E3, ℓ / 2 < ‖z‖ → chiSmallB M ℓ d u z * (w z - cu u) = 0) := by
  intro w hw C
  obtain ⟨Mχ, Lχ, hMχ0, hLχ0, hMχsup, hMχlip⟩ := chiSmallB_supLipschitz_uniform hM hℓ hd
  obtain ⟨S, hS⟩ := (acube_compact hℓ).exists_bound_of_continuousOn hw.continuous.norm.continuousOn
  have hS' : ∀ z ∈ acube ℓ, |w z| ≤ max S 0 := fun z hz => by
    refine le_trans ?_ (le_max_left _ _)
    simpa [Real.norm_eq_abs] using hS z hz
  have hS0 : 0 ≤ max S 0 := le_max_right _ _
  obtain ⟨D, hD⟩ := (acube_compact hℓ).exists_bound_of_continuousOn
    (hw.continuous_fderiv (by simp)).norm.continuousOn
  have hD0 : 0 ≤ max D 0 := le_max_right _ _
  have hDbd : ∀ z ∈ acube ℓ, ‖fderiv ℝ w z‖ ≤ max D 0 := fun z hz => by
    refine le_trans ?_ (le_max_left _ _)
    simpa using hD z hz
  have hconv : Convex ℝ (acube ℓ) := by
    intro x hx y hy a b ha hb hab
    rw [mem_acube_iff] at hx hy ⊢
    intro m
    have h1 := (hx m).1
    have h2 := (hx m).2
    have h3 := (hy m).1
    have h4 := (hy m).2
    simp only [Set.mem_Icc] at h1 h2 h3 h4 ⊢
    have he : (a • x + b • y).ofLp m = a * x.ofLp m + b * y.ofLp m := by
      simp [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    rw [he]
    have h1' : a * (-ℓ / 2) ≤ a * x.ofLp m := mul_le_mul_of_nonneg_left h1 ha
    have h3' : b * (-ℓ / 2) ≤ b * y.ofLp m := mul_le_mul_of_nonneg_left h3 hb
    have h1'' : a * x.ofLp m ≤ a * (ℓ / 2) := mul_le_mul_of_nonneg_left h2 ha
    have h3'' : b * y.ofLp m ≤ b * (ℓ / 2) := mul_le_mul_of_nonneg_left h4 hb
    constructor <;> nlinarith
  have hwlip : ∀ y t : E3, y ∈ acube ℓ → t ∈ acube ℓ → |w y - w t| ≤ max D 0 * ‖y - t‖ := by
    intro y t hy ht
    have h := Convex.norm_image_sub_le_of_norm_fderiv_le
      (f := w) (s := acube ℓ) (C := max D 0)
      (fun x _ => (hw.differentiable (by simp)) x) (fun x hx => hDbd x hx) hconv ht hy
    rw [Real.norm_eq_abs] at h
    exact h
  refine ⟨Mχ * (max S 0 + max C 0), Lχ * (max S 0 + max C 0) + Mχ * max D 0, ?_, ?_, ?_⟩
  · exact mul_nonneg hMχ0 (add_nonneg hS0 (le_max_right _ _))
  · exact add_nonneg (mul_nonneg hLχ0 (add_nonneg hS0 (le_max_right _ _)))
      (mul_nonneg hMχ0 hD0)
  · intro cu hcu u
    have hmem : ∀ z : E3, chiSmallB M ℓ d u z ≠ 0 → z ∈ acube ℓ := by
      intro z hz
      rw [mem_acube_iff]
      intro m
      have hb := abs_le.mp (chiSmallB_support_big_box hM hℓ hz m)
      exact Set.mem_Icc.mpr ⟨by linarith [hb.1], by linarith [hb.2]⟩
    have hwz : ∀ z : E3, chiSmallB M ℓ d u z ≠ 0 → |w z| ≤ max S 0 :=
      fun z hz => hS' z (hmem z hz)
    have hcuC : |cu u| ≤ max C 0 := le_trans (hcu u) (le_max_left _ _)
    have hSC : (0 : ℝ) ≤ max S 0 + max C 0 := add_nonneg hS0 (le_max_right _ _)
    have hLnn : (0 : ℝ) ≤ Lχ * (max S 0 + max C 0) + Mχ * max D 0 :=
      add_nonneg (mul_nonneg hLχ0 hSC) (mul_nonneg hMχ0 hD0)
    -- the pointwise bound on the shift at points where the window does not vanish
    have hshift : ∀ z : E3, chiSmallB M ℓ d u z ≠ 0 → |w z - cu u| ≤ max S 0 + max C 0 := by
      intro z hz
      have h := abs_add_le (w z) (-(cu u))
      rw [← sub_eq_add_neg, abs_neg] at h
      exact le_trans h (add_le_add (hwz z hz) hcuC)
    refine ⟨?_, ?_, ?_⟩
    · intro z
      by_cases hz : chiSmallB M ℓ d u z = 0
      · rw [hz, zero_mul, abs_zero]
        exact mul_nonneg hMχ0 hSC
      · rw [abs_mul]
        exact mul_le_mul (hMχsup u z) (hshift z hz) (abs_nonneg _) hMχ0
    · intro y t
      by_cases hy : chiSmallB M ℓ d u y = 0
      · by_cases ht : chiSmallB M ℓ d u t = 0
        · rw [hy, ht]
          simp only [zero_mul, sub_zero, abs_zero]
          exact mul_nonneg hLnn (norm_nonneg _)
        · simp only [hy, zero_mul, zero_sub, abs_neg, abs_mul]
          have hA : |chiSmallB M ℓ d u t| ≤ Lχ * ‖y - t‖ := by
            have h := hMχlip u t y
            rw [norm_sub_rev] at h
            rw [hy, sub_zero] at h
            exact h
          calc |chiSmallB M ℓ d u t| * |w t - cu u|
              ≤ (Lχ * ‖y - t‖) * (max S 0 + max C 0) :=
                mul_le_mul hA (hshift t ht) (abs_nonneg _)
                  (mul_nonneg hLχ0 (norm_nonneg _))
            _ = (Lχ * (max S 0 + max C 0)) * ‖y - t‖ := by ring
            _ ≤ (Lχ * (max S 0 + max C 0) + Mχ * max D 0) * ‖y - t‖ :=
                mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (mul_nonneg hMχ0 hD0))
                  (norm_nonneg _)
      · by_cases ht : chiSmallB M ℓ d u t = 0
        · simp only [ht, zero_mul, sub_zero, abs_mul]
          have hAy : |chiSmallB M ℓ d u y| ≤ Lχ * ‖y - t‖ := by
            have h := hMχlip u y t
            rw [ht, sub_zero] at h
            exact h
          calc |chiSmallB M ℓ d u y| * |w y - cu u|
              ≤ (Lχ * ‖y - t‖) * (max S 0 + max C 0) :=
                mul_le_mul hAy (hshift y hy) (abs_nonneg _)
                  (mul_nonneg hLχ0 (norm_nonneg _))
            _ = (Lχ * (max S 0 + max C 0)) * ‖y - t‖ := by ring
            _ ≤ (Lχ * (max S 0 + max C 0) + Mχ * max D 0) * ‖y - t‖ :=
                mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (mul_nonneg hMχ0 hD0))
                  (norm_nonneg _)
        · have hwlt : |w y - w t| ≤ max D 0 * ‖y - t‖ :=
            hwlip y t (hmem y hy) (hmem t ht)
          have hkey : chiSmallB M ℓ d u y * (w y - cu u) - chiSmallB M ℓ d u t * (w t - cu u)
              = (chiSmallB M ℓ d u y - chiSmallB M ℓ d u t) * (w y - cu u)
                + chiSmallB M ℓ d u t * (w y - w t) := by ring
          rw [hkey]
          refine le_trans (abs_add_le _ _) ?_
          have h1 : |(chiSmallB M ℓ d u y - chiSmallB M ℓ d u t) * (w y - cu u)|
              ≤ (Lχ * ‖y - t‖) * (max S 0 + max C 0) := by
            rw [abs_mul]
            exact mul_le_mul (hMχlip u y t) (hshift y hy) (abs_nonneg _)
              (mul_nonneg hLχ0 (norm_nonneg _))
          have h2 : |chiSmallB M ℓ d u t * (w y - w t)| ≤ Mχ * (max D 0 * ‖y - t‖) := by
            rw [abs_mul]
            exact mul_le_mul (hMχsup u t) hwlt (abs_nonneg _) hMχ0
          calc |(chiSmallB M ℓ d u y - chiSmallB M ℓ d u t) * (w y - cu u)|
                + |chiSmallB M ℓ d u t * (w y - w t)|
              ≤ (Lχ * ‖y - t‖) * (max S 0 + max C 0) + Mχ * (max D 0 * ‖y - t‖) :=
                add_le_add h1 h2
            _ = (Lχ * (max S 0 + max C 0) + Mχ * max D 0) * ‖y - t‖ := by ring
    · intro z hz
      simp only [chiSmallB, chiScale_eq_zero_of_half_lt_norm' hℓ hz, zero_mul, mul_zero]

/-- **Weighted Plancherel at `C¹`**: the box-free `H¹` bound for the cut kinetic word. -/
theorem bsW_le_of_c1_self {c : ℝ} {h : E3 → ℝ} (h1 : ContDiff ℝ 1 h) (hcs : HasCompactSupport h) :
    Work.BSKinetic.Decomp.bsW (fsKinCoeff c) h
      ≤ 2 * (1 + c ^ 2) * ((2 * Real.pi) ^ 3 *
          (Work.BSKinetic.Decomp.bsL2 h + Work.BSKinetic.Decomp.bsDir h)) := by
  have h1c : ContDiff ℝ 1 (fun z : E3 => ((h z : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp h1
  have hcsc : HasCompactSupport (fun z : E3 => ((h z : ℝ) : ℂ)) :=
    hcs.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  obtain ⟨hpl_int, hpl_val⟩ := Work.BoseFixB1S.weightedPlancherelKinFT h1c hcsc
  have hpl_int' : Integrable (fun p : E3 =>
      (1 + ‖p‖ ^ 2) * ‖Work.BSKinetic.Decomp.bsPsi h p‖ ^ 2) := by
    simpa only [Work.BSKinetic.Decomp.bsPsi] using hpl_int
  have hpl_real : (∫ p : E3, (1 + ‖p‖ ^ 2) * ‖Work.BSKinetic.Decomp.bsPsi h p‖ ^ 2)
      = (2 * Real.pi) ^ 3 * (Work.BSKinetic.Decomp.bsL2 h + Work.BSKinetic.Decomp.bsDir h) := by
    simp only [Work.BSKinetic.Decomp.bsPsi] at hpl_val ⊢
    rw [hpl_val]
    congr 1
    rw [Work.BSKinetic.Decomp.bsL2, Work.BSKinetic.Decomp.bsDir]
    congr 1
    · refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      show ‖((h z : ℝ) : ℂ)‖ ^ 2 = (h z) ^ 2
      rw [Complex.sq_norm, Complex.normSq_ofReal]
      ring
    · refine Finset.sum_congr rfl fun k _ => ?_
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      have h2 : fderiv ℝ (fun z : E3 => ((h z : ℝ) : ℂ)) z
          = Complex.ofRealCLM.comp (fderiv ℝ h z) := by
        have hh := (Complex.ofRealCLM.hasFDerivAt (x := h z)).comp z
          (h1.differentiable one_ne_zero z).hasFDerivAt
        simpa [Function.comp_def] using hh.fderiv
      show ‖(fderiv ℝ (fun z : E3 => ((h z : ℝ) : ℂ)) z) (kcStdBasis k)‖ ^ 2
        = (fderiv ℝ h z (kcStdBasis k)) ^ 2
      rw [h2, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, Complex.sq_norm,
        Complex.normSq_ofReal]
      ring
  have hmaj_int : Integrable (fun p : E3 =>
      2 * (1 + c ^ 2) * ((1 + ‖p‖ ^ 2) * ‖Work.BSKinetic.Decomp.bsPsi h p‖ ^ 2)) :=
    hpl_int'.const_mul _
  have hpt : ∀ p : E3, fsKinCoeff c ‖p‖ * ‖Work.BSKinetic.Decomp.bsPsi h p‖ ^ 2
      ≤ 2 * (1 + c ^ 2) * ((1 + ‖p‖ ^ 2) * ‖Work.BSKinetic.Decomp.bsPsi h p‖ ^ 2) := by
    intro p
    have hsym : fsKinCoeff c ‖p‖ ≤ 2 * (1 + c ^ 2) * (1 + ‖p‖ ^ 2) := by
      have h2 : fsKinCoeff c ‖p‖ ≤ 2 * ‖p‖ ^ 2 + 2 * c ^ 2 :=
        Work.BSKinetic.Decomp.fsKinCoeff_le_two_mul c ‖p‖
      nlinarith [sq_nonneg ‖p‖, sq_nonneg c, norm_nonneg p]
    calc fsKinCoeff c ‖p‖ * ‖Work.BSKinetic.Decomp.bsPsi h p‖ ^ 2
        ≤ (2 * (1 + c ^ 2) * (1 + ‖p‖ ^ 2)) * ‖Work.BSKinetic.Decomp.bsPsi h p‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hsym (sq_nonneg _)
      _ = 2 * (1 + c ^ 2) * ((1 + ‖p‖ ^ 2) * ‖Work.BSKinetic.Decomp.bsPsi h p‖ ^ 2) := by ring
  have hmono : (∫ p : E3, fsKinCoeff c ‖p‖ * ‖Work.BSKinetic.Decomp.bsPsi h p‖ ^ 2)
      ≤ ∫ p : E3, 2 * (1 + c ^ 2) *
          ((1 + ‖p‖ ^ 2) * ‖Work.BSKinetic.Decomp.bsPsi h p‖ ^ 2) :=
    integral_mono_of_nonneg (Eventually.of_forall fun p =>
      mul_nonneg (fsKinCoeff_nonneg c ‖p‖) (sq_nonneg _)) hmaj_int
      (Eventually.of_forall hpt)
  rw [Work.BSKinetic.Decomp.bsW]
  refine hmono.trans ?_
  rw [MeasureTheory.integral_const_mul, hpl_real]

/-- **The box form** of `bsW_le_of_c1`: for a `C¹` state of compact support, bounded by `A` with
coordinate derivatives bounded by `D` and vanishing outside `acube ℓ`. -/
theorem bsW_le_of_c1_box_self {c ℓ A D : ℝ} (hℓ : 0 < ℓ) {h : E3 → ℝ}
    (h1 : ContDiff ℝ 1 h) (hcs : HasCompactSupport h) (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hbd : ∀ z : E3, |h z| ≤ A)
    (hDbd : ∀ (k : Fin 3) (z : E3), |fderiv ℝ h z (kcStdBasis k)| ≤ D)
    (hzero : ∀ z : E3, z ∉ acube ℓ → h z = 0) :
    Work.BSKinetic.Decomp.bsW (fsKinCoeff c) h
      ≤ 2 * (1 + c ^ 2) * ((2 * Real.pi) ^ 3 * (A ^ 2 * ℓ ^ 3 + 3 * (D ^ 2 * ℓ ^ 3))) := by
  have hL2 := Work.BSKinetic.Decomp.bsL2_le_of_bounded_support hℓ hA hbd hzero
  have hDir := Work.BSKinetic.Decomp.bsDir_le_of_bounded_support hℓ hD hDbd hzero
  have hbase := bsW_le_of_c1_self (c := c) h1 hcs
  calc Work.BSKinetic.Decomp.bsW (fsKinCoeff c) h
      ≤ 2 * (1 + c ^ 2) * ((2 * Real.pi) ^ 3 *
          (Work.BSKinetic.Decomp.bsL2 h + Work.BSKinetic.Decomp.bsDir h)) := hbase
    _ ≤ 2 * (1 + c ^ 2) * ((2 * Real.pi) ^ 3 * (A ^ 2 * ℓ ^ 3 + 3 * (D ^ 2 * ℓ ^ 3))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul_of_nonneg_left (add_le_add hL2 hDir) (by positivity)

/-- **`bsW` bound for a globally Lipschitz, compactly supported state.** -/

theorem bsW_fsKinCoeff_le_lipschitz_self :
    ∃ Cm : ℝ, 0 ≤ Cm ∧ ∀ {c A L R : ℝ}, 0 ≤ A → 0 ≤ L → 0 ≤ R →
      ∀ {h : E3 → ℝ}, Continuous h →
        (∀ z, |h z| ≤ A) →
        (∀ y t, |h y - h t| ≤ L * ‖y - t‖) →
        (∀ z, R < ‖z‖ → h z = 0) →
        Work.BSKinetic.Decomp.bsW (Submission.BoseGases.fsKinCoeff c) h
          ≤ Cm * (1 + c ^ 2) * (A ^ 2 + L ^ 2) * (1 + R) ^ 4 := by
  refine ⟨48 * (2 * Real.pi) ^ 3, by positivity, ?_⟩
  intro c A L R hA0 hL0 hR0 h hcont hbd hlip hsupp
  -- `h` has compact support
  have hcs : HasCompactSupport h := by
    refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : E3) R) ?_
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    by_contra hc
    exact hz (hsupp z (lt_of_not_ge hc))
  -- the mollifying bumps
  let r : ℕ → ℝ := fun n => ((n : ℝ) + 1)⁻¹
  have hrpos : ∀ n, 0 < r n := fun n => by positivity
  have hrle1 : ∀ n, r n ≤ 1 := by
    intro n
    have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    exact inv_le_one_of_one_le₀ h1
  have hr0 : Tendsto r atTop (nhds 0) := by
    simpa only [r, one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  let b : ℕ → ContDiffBump (0 : E3) := fun n =>
    ⟨r n / 2, r n, by have := hrpos n; linarith, by have := hrpos n; linarith⟩
  let ρ : ℕ → E3 → ℝ := fun n => (b n).normed volume
  have hρint : ∀ n, (∫ x : E3, ρ n x) = 1 := fun n => ContDiffBump.integral_normed (b n)
  have hρnn : ∀ n x, 0 ≤ ρ n x := fun n x => ContDiffBump.nonneg_normed (b n) x
  have hρcont : ∀ n, Continuous (ρ n) := fun n =>
    (ContDiffBump.contDiff_normed (f := b n) (μ := volume) (n := (⊤ : ℕ∞))).continuous
  have hρcs : ∀ n, HasCompactSupport (ρ n) := fun n =>
    ContDiffBump.hasCompactSupport_normed (b n)
  have hρsupp : ∀ n, Function.support (ρ n) = Metric.ball (0 : E3) (r n) := by
    intro n
    change Function.support ((b n).normed volume) = Metric.ball (0 : E3) (r n)
    rw [ContDiffBump.support_normed_eq (b n)]
  let u : ℕ → E3 → ℝ := fun n =>
    MeasureTheory.convolution (ρ n) h (ContinuousLinearMap.lsmul ℝ ℝ) volume
  have hu_eq : ∀ n x, u n x = ∫ t : E3, ρ n t * h (x - t) := by
    intro n x
    simp only [u, MeasureTheory.convolution_lsmul, smul_eq_mul]
  have hu_int : ∀ n x, Integrable (fun t : E3 => ρ n t * h (x - t)) := by
    intro n x
    exact ((hρcont n).mul (hcont.comp ((continuous_const : Continuous fun _ : E3 => x).sub
      continuous_id))).integrable_of_hasCompactSupport (hρcs n).mul_right
  have hρc_int : ∀ n (C : ℝ), Integrable (fun t : E3 => ρ n t * C) := by
    intro n C
    exact ((hρcont n).mul_const C).integrable_of_hasCompactSupport (hρcs n).mul_right
  -- uniform bounds along the mollified sequence
  have hu_smooth : ∀ n, ContDiff ℝ (⊤ : ENat) (u n) := fun n =>
    HasCompactSupport.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
      (hρcs n)
      (ContDiffBump.contDiff_normed (f := b n) (μ := volume) (n := (⊤ : ℕ∞)))
      hcont.locallyIntegrable
  have hu_cs : ∀ n, HasCompactSupport (u n) := fun n =>
    HasCompactSupport.convolution (ContinuousLinearMap.lsmul ℝ ℝ) (hρcs n) hcs
  have hu_bd : ∀ n x, |u n x| ≤ A := by
    intro n x
    rw [hu_eq]
    have h1 : ∀ t : E3, ‖ρ n t * h (x - t)‖ ≤ ρ n t * A := by
      intro t
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hρnn n t)]
      exact mul_le_mul_of_nonneg_left (hbd _) (hρnn n t)
    calc |∫ t : E3, ρ n t * h (x - t)|
        ≤ ∫ t : E3, ‖ρ n t * h (x - t)‖ := abs_integral_le_integral_abs
      _ ≤ ∫ t : E3, ρ n t * A := integral_mono (hu_int n x).norm (hρc_int n A) h1
      _ = (∫ t : E3, ρ n t) * A := by rw [MeasureTheory.integral_mul_const]
      _ = A := by rw [hρint n, one_mul]
  have hu_lip : ∀ n y t, |u n y - u n t| ≤ L * ‖y - t‖ := by
    intro n y t
    have hsub : u n y - u n t = ∫ s : E3, ρ n s * (h (y - s) - h (t - s)) := by
      rw [hu_eq n y, hu_eq n t, ← MeasureTheory.integral_sub (hu_int n y) (hu_int n t)]
      refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun s => ?_)
      ring
    have h1 : ∀ s : E3, ‖ρ n s * (h (y - s) - h (t - s))‖ ≤ ρ n s * (L * ‖y - t‖) := by
      intro s
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hρnn n s)]
      refine mul_le_mul_of_nonneg_left ?_ (hρnn n s)
      have harg : (y - s) - (t - s) = y - t := by abel
      calc |h (y - s) - h (t - s)| ≤ L * ‖(y - s) - (t - s)‖ := hlip _ _
        _ = L * ‖y - t‖ := by rw [harg]
    have hD_int : Integrable (fun s : E3 => ρ n s * (h (y - s) - h (t - s))) :=
      ((hu_int n y).sub (hu_int n t)).congr
        (Eventually.of_forall fun s => by simp only [Pi.sub_apply]; ring)
    rw [hsub]
    calc |∫ s : E3, ρ n s * (h (y - s) - h (t - s))|
        ≤ ∫ s : E3, ‖ρ n s * (h (y - s) - h (t - s))‖ := abs_integral_le_integral_abs
      _ ≤ ∫ s : E3, ρ n s * (L * ‖y - t‖) :=
          integral_mono hD_int.norm (hρc_int n (L * ‖y - t‖)) h1
      _ = (∫ s : E3, ρ n s) * (L * ‖y - t‖) := by rw [MeasureTheory.integral_mul_const]
      _ = L * ‖y - t‖ := by rw [hρint n, one_mul]
  have hu_grad : ∀ n x, ‖fderiv ℝ (u n) x‖ ≤ L := by
    intro n x
    have hlipn : LipschitzWith (⟨L, hL0⟩ : ℝ≥0) (u n) :=
      LipschitzWith.of_dist_le_mul (K := (⟨L, hL0⟩ : ℝ≥0)) fun y t => by
        rw [Real.dist_eq, dist_eq_norm]
        exact hu_lip n y t
    exact HasFDerivAt.le_of_lipschitz (((hu_smooth n).differentiable (by simp)) x).hasFDerivAt
      hlipn
  -- the support of the mollified states
  have hts : tsupport h ⊆ Metric.closedBall (0 : E3) R := by
    refine closure_minimal ?_ Metric.isClosed_closedBall
    intro z hz
    rw [Function.mem_support] at hz
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    by_contra hc
    exact hz (hsupp z (lt_of_not_ge hc))
  have hu_supp : ∀ n z, z ∉ acube (2 * (R + 1)) → u n z = 0 := by
    intro n z hz
    have h1 : tsupport (u n) ⊆ tsupport h + Metric.closedBall (0 : E3) 1 := by
      have hb1 : (b n).rOut ≤ 1 := by
        rw [show (b n).rOut = r n from rfl]
        exact hrle1 n
      have := Work.BoseFixR.tsupport_moll_subset hcs (b n) hb1
      simpa only [u, ρ] using this
    refine image_eq_zero_of_notMem_tsupport ?_
    intro hmem
    obtain ⟨a, ha, c', hc', haz⟩ := h1 hmem
    rw [← haz] at hz
    refine hz ?_
    rw [mem_acube_iff]
    intro m
    have ha' : ‖a‖ ≤ R := by
      have := hts ha
      rwa [Metric.mem_closedBall, dist_eq_norm, sub_zero] at this
    have hc'' : ‖c'‖ ≤ 1 := by
      have := hc'
      rwa [Metric.mem_closedBall, dist_eq_norm, sub_zero] at this
    have hnorm : ‖a + c'‖ ≤ R + 1 := by
      calc ‖a + c'‖ ≤ ‖a‖ + ‖c'‖ := norm_add_le _ _
        _ ≤ R + 1 := add_le_add ha' hc''
    have hcoord : |(a + c').ofLp m| ≤ ‖a + c'‖ := by
      have := PiLp.norm_apply_le (a + c') m
      rwa [Real.norm_eq_abs] at this
    have h2 : (2 * (R + 1)) / 2 = R + 1 := by ring
    rw [Set.mem_Icc, h2]
    constructor <;> linarith [hcoord, hnorm, neg_abs_le ((a + c').ofLp m),
      le_abs_self ((a + c').ofLp m)]
  -- the uniform bound for the mollified states
  have hB : ∀ n, Work.BSKinetic.Decomp.bsW (Submission.BoseGases.fsKinCoeff c) (u n)
      ≤ 2 * (1 + c ^ 2) * ((2 * Real.pi) ^ 3 *
          (A ^ 2 * (2 * (R + 1)) ^ 3 + 3 * (L ^ 2 * (2 * (R + 1)) ^ 3))) := by
    intro n
    refine bsW_le_of_c1_box_self (c := c) (ℓ := 2 * (R + 1)) (A := A) (D := L)
      (by linarith) ?_ (hu_cs n) hA0 hL0 (hu_bd n) ?_ (fun z hz => hu_supp n z hz)
    · exact (hu_smooth n).of_le (by simp)
    · intro k z
      have h1 : ‖fderiv ℝ (u n) z‖ ≤ L := hu_grad n z
      calc |fderiv ℝ (u n) z (kcStdBasis k)|
          = ‖fderiv ℝ (u n) z (kcStdBasis k)‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖fderiv ℝ (u n) z‖ * ‖kcStdBasis k‖ := ContinuousLinearMap.le_opNorm _ _
        _ = ‖fderiv ℝ (u n) z‖ := by
            rw [show ‖kcStdBasis k‖ = 1 from by simp [kcStdBasis], mul_one]
        _ ≤ L := h1
  -- pointwise convergence of the mollified states
  have hu_tend : ∀ x : E3, Tendsto (fun n => u n x) atTop (nhds (h x)) := by
    intro x
    by_cases hx : ‖x‖ ≤ R
    · have hbd' : ∀ n, |u n x - h x| ≤ L * r n := by
        intro n
        have hdiff : u n x - h x = ∫ t : E3, ρ n t * (h (x - t) - h x) := by
          have h2 : (∫ t : E3, ρ n t * h x) = h x := by
            rw [MeasureTheory.integral_mul_const, hρint n, one_mul]
          calc u n x - h x = (∫ t : E3, ρ n t * h (x - t)) - ∫ t : E3, ρ n t * h x := by
                rw [hu_eq, h2]
            _ = ∫ t : E3, (ρ n t * h (x - t) - ρ n t * h x) :=
                (MeasureTheory.integral_sub (hu_int n x) (hρc_int n (h x))).symm
            _ = ∫ t : E3, ρ n t * (h (x - t) - h x) := by
                refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun t => ?_)
                ring
        have h1 : ∀ t : E3, ‖ρ n t * (h (x - t) - h x)‖ ≤ ρ n t * (L * r n) := by
          intro t
          by_cases ht : ρ n t = 0
          · rw [ht, zero_mul, norm_zero, zero_mul]
          · have ht' : ‖t‖ < r n := by
              have hmem : t ∈ Function.support (ρ n) := Function.mem_support.mpr ht
              rw [hρsupp n, Metric.mem_ball, dist_eq_norm, sub_zero] at hmem
              exact hmem
            rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hρnn n t)]
            refine mul_le_mul_of_nonneg_left ?_ (hρnn n t)
            calc |h (x - t) - h x| ≤ L * ‖(x - t) - x‖ := hlip _ _
              _ = L * ‖t‖ := by rw [show (x - t) - x = -t from by abel, norm_neg]
              _ ≤ L * r n := mul_le_mul_of_nonneg_left ht'.le hL0
        have hD_int : Integrable (fun t : E3 => ρ n t * (h (x - t) - h x)) :=
          ((hu_int n x).sub (hρc_int n (h x))).congr
            (Eventually.of_forall fun t => by simp only [Pi.sub_apply]; ring)
        rw [hdiff]
        calc |∫ t : E3, ρ n t * (h (x - t) - h x)|
            ≤ ∫ t : E3, ‖ρ n t * (h (x - t) - h x)‖ := abs_integral_le_integral_abs
          _ ≤ ∫ t : E3, ρ n t * (L * r n) :=
              integral_mono hD_int.norm (hρc_int n (L * r n)) h1
          _ = (∫ t : E3, ρ n t) * (L * r n) := by rw [MeasureTheory.integral_mul_const]
          _ = L * r n := by rw [hρint n, one_mul]
      have hlim : Tendsto (fun n => L * r n) atTop (nhds 0) := by
        simpa using hr0.const_mul L
      refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
      refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hlim
      rw [Real.norm_eq_abs]
      exact hbd' n
    · have hx0 : h x = 0 := hsupp x (lt_of_not_ge hx)
      have hev : ∀ᶠ n in atTop, u n x = 0 := by
        have hpos : 0 < ‖x‖ - R := by linarith
        have hev1 : ∀ᶠ n in atTop, r n < ‖x‖ - R := (tendsto_order.1 hr0).2 _ hpos
        filter_upwards [hev1] with n hn
        rw [hu_eq]
        rw [MeasureTheory.integral_congr_ae (Eventually.of_forall fun t => ?_),
          MeasureTheory.integral_zero]
        by_cases ht : ρ n t = 0
        · rw [ht, zero_mul]
        · have ht' : ‖t‖ < r n := by
            have hmem : t ∈ Function.support (ρ n) := Function.mem_support.mpr ht
            rw [hρsupp n, Metric.mem_ball, dist_eq_norm, sub_zero] at hmem
            exact hmem
          have hz : R < ‖x - t‖ := by
            have h1 : ‖x‖ ≤ ‖x - t‖ + ‖t‖ := by
              calc ‖x‖ = ‖(x - t) + t‖ := by rw [sub_add_cancel]
                _ ≤ ‖x - t‖ + ‖t‖ := norm_add_le _ _
            linarith
          rw [hsupp _ hz, mul_zero]
      have heq : (fun _ : ℕ => h x) =ᶠ[atTop] (fun k => u k x) :=
        hev.mono fun k hk => by
          show h x = u k x
          rw [hk, hx0]
      exact Filter.Tendsto.congr' heq tendsto_const_nhds
  -- the Fourier transforms converge pointwise
  have hft : ∀ p : E3, Tendsto (fun n => Work.BSKinetic.Decomp.bsPsi (u n) p) atTop
      (nhds (Work.BSKinetic.Decomp.bsPsi h p)) := by
    intro p
    have hmain := MeasureTheory.tendsto_integral_of_dominated_convergence
      (μ := volume)
      (F := fun n z => Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * ((u n z : ℝ) : ℂ))
      (f := fun z => Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * ((h z : ℝ) : ℂ))
      (bound := (acube (2 * (R + 1))).indicator (fun _ => max A 0))
      (fun n => (((by fun_prop : Continuous fun z : E3 =>
          Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))).mul
            (Complex.continuous_ofReal.comp ((hu_smooth n).continuous)))).aestronglyMeasurable)
      ?_ ?_ ?_
    · simpa only [Work.BSKinetic.Decomp.bsPsi, Submission.BoseGases.kinFT] using hmain
    · rw [MeasureTheory.integrable_indicator_iff (acube_measurable _)]
      exact MeasureTheory.integrableOn_const
        (ne_of_lt (acube_lt_top _ (by linarith))) (by simp)
    · intro n
      filter_upwards with z
      by_cases hz : z ∈ acube (2 * (R + 1))
      · rw [Set.indicator_of_mem hz, norm_mul,
          Work.BSKinetic.Decomp.norm_exp_neg_I_inner p z, one_mul]
        have hnorm : ‖((u n z : ℝ) : ℂ)‖ = |u n z| := by
          have hsq : ‖((u n z : ℝ) : ℂ)‖ ^ 2 = |u n z| ^ 2 := by
            rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal, sq_abs]
            ring
          nlinarith [norm_nonneg (((u n z : ℝ) : ℂ)), abs_nonneg (u n z)]
        rw [hnorm]
        exact le_trans (hu_bd n z) (le_max_left _ _)
      · rw [Set.indicator_of_notMem hz, norm_mul,
          Work.BSKinetic.Decomp.norm_exp_neg_I_inner p z, one_mul,
          hu_supp n z hz, Complex.ofReal_zero, norm_zero]
    · filter_upwards with z
      have hhz := hu_tend z
      have h2 : Tendsto (fun n => ((u n z : ℝ) : ℂ)) atTop (nhds ((h z : ℝ) : ℂ)) :=
        (Complex.continuous_ofReal.tendsto (h z)).comp hhz
      have h3 : Tendsto (fun _ : ℕ => Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))) atTop
          (nhds (Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))))) := tendsto_const_nhds
      exact h3.mul h2
  -- measurability of the limiting integrand
  have hbsPsi_sm : ∀ n, StronglyMeasurable (fun p : E3 => Work.BSKinetic.Decomp.bsPsi (u n) p) := by
    intro n
    have hJ : StronglyMeasurable (fun q : E3 × E3 =>
        Complex.exp (-(Complex.I * (inner ℝ q.1 q.2 : ℂ))) * ((u n q.2 : ℝ) : ℂ)) := by
      refine (by fun_prop : Continuous fun q : E3 × E3 =>
        Complex.exp (-(Complex.I * (inner ℝ q.1 q.2 : ℂ)))).stronglyMeasurable.mul ?_
      exact Complex.continuous_ofReal.comp_stronglyMeasurable
        (((hu_smooth n).continuous.stronglyMeasurable).comp_measurable measurable_snd)
    have := hJ.integral_prod_right' (ν := volume)
    simpa only [Work.BSKinetic.Decomp.bsPsi, Submission.BoseGases.kinFT] using this
  have hkin_cont : Continuous (fun p : E3 => Submission.BoseGases.fsKinCoeff c ‖p‖) := by
    have h1 : Continuous (fun r : ℝ => Submission.BoseGases.fsKinCoeff c r) := by
      unfold Submission.BoseGases.fsKinCoeff
      fun_prop
    exact h1.comp continuous_norm
  have hFS_sm : AEStronglyMeasurable
      (fun p : E3 => Submission.BoseGases.fsKinCoeff c ‖p‖ *
        ‖Work.BSKinetic.Decomp.bsPsi h p‖ ^ 2) volume := by
    have hJ : StronglyMeasurable (fun q : E3 × E3 =>
        Complex.exp (-(Complex.I * (inner ℝ q.1 q.2 : ℂ))) * ((h q.2 : ℝ) : ℂ)) := by
      refine (by fun_prop : Continuous fun q : E3 × E3 =>
        Complex.exp (-(Complex.I * (inner ℝ q.1 q.2 : ℂ)))).stronglyMeasurable.mul ?_
      exact Complex.continuous_ofReal.comp_stronglyMeasurable
        (hcont.stronglyMeasurable.comp_measurable measurable_snd)
    have hbsPsi : StronglyMeasurable (fun p : E3 => Work.BSKinetic.Decomp.bsPsi h p) := by
      have := hJ.integral_prod_right' (ν := volume)
      simpa only [Work.BSKinetic.Decomp.bsPsi, Submission.BoseGases.kinFT] using this
    exact ((hkin_cont.stronglyMeasurable).mul (hbsPsi.norm.pow 2)).aestronglyMeasurable
  -- integrability of the approximating integrands
  have hInt : ∀ n, Integrable
      (fun p : E3 => Submission.BoseGases.fsKinCoeff c ‖p‖ *
        ‖Work.BSKinetic.Decomp.bsPsi (u n) p‖ ^ 2) volume := by
    intro n
    have h1c : ContDiff ℝ 1 (fun z : E3 => ((u n z : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp ((hu_smooth n).of_le (by simp))
    have hcsc : HasCompactSupport (fun z : E3 => ((u n z : ℝ) : ℂ)) :=
      (hu_cs n).comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
    obtain ⟨hint, -⟩ := Work.BoseFixB1S.weightedPlancherelKinFT h1c hcsc
    refine (hint.const_mul (2 * (1 + c ^ 2))).mono'
      (((hkin_cont.stronglyMeasurable).mul
        (((hbsPsi_sm n).norm).pow 2))).aestronglyMeasurable ?_
    filter_upwards with p
    have hsym : Submission.BoseGases.fsKinCoeff c ‖p‖
        ≤ 2 * (1 + c ^ 2) * (1 + ‖p‖ ^ 2) := by
      have h2 : Submission.BoseGases.fsKinCoeff c ‖p‖ ≤ 2 * ‖p‖ ^ 2 + 2 * c ^ 2 :=
        Work.BSKinetic.Decomp.fsKinCoeff_le_two_mul c ‖p‖
      nlinarith [sq_nonneg ‖p‖, sq_nonneg c, norm_nonneg p]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (fsKinCoeff_nonneg c ‖p‖) (sq_nonneg _))]
    calc Submission.BoseGases.fsKinCoeff c ‖p‖ *
          ‖Work.BSKinetic.Decomp.bsPsi (u n) p‖ ^ 2
        ≤ (2 * (1 + c ^ 2) * (1 + ‖p‖ ^ 2)) *
            ‖Work.BSKinetic.Decomp.bsPsi (u n) p‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hsym (sq_nonneg _)
      _ = 2 * (1 + c ^ 2) * ((1 + ‖p‖ ^ 2) *
            ‖Work.BSKinetic.Decomp.bsPsi (u n) p‖ ^ 2) := by ring
  -- Fatou
  have hFS_tend : ∀ p : E3, Tendsto
      (fun n => Submission.BoseGases.fsKinCoeff c ‖p‖ *
        ‖Work.BSKinetic.Decomp.bsPsi (u n) p‖ ^ 2) atTop
      (nhds (Submission.BoseGases.fsKinCoeff c ‖p‖ *
        ‖Work.BSKinetic.Decomp.bsPsi h p‖ ^ 2)) := by
    intro p
    exact tendsto_const_nhds.mul ((hft p).norm.pow 2)
  have hFatou : (∫⁻ p : E3, ENNReal.ofReal (Submission.BoseGases.fsKinCoeff c ‖p‖ *
        ‖Work.BSKinetic.Decomp.bsPsi h p‖ ^ 2))
      ≤ ENNReal.ofReal (2 * (1 + c ^ 2) * ((2 * Real.pi) ^ 3 *
          (A ^ 2 * (2 * (R + 1)) ^ 3 + 3 * (L ^ 2 * (2 * (R + 1)) ^ 3)))) := by
    have h1 : (∫⁻ p : E3, ENNReal.ofReal (Submission.BoseGases.fsKinCoeff c ‖p‖ *
          ‖Work.BSKinetic.Decomp.bsPsi h p‖ ^ 2))
        ≤ Filter.liminf (fun n => ∫⁻ p : E3, ENNReal.ofReal (Submission.BoseGases.fsKinCoeff c ‖p‖ *
            ‖Work.BSKinetic.Decomp.bsPsi (u n) p‖ ^ 2)) atTop := by
      calc (∫⁻ p : E3, ENNReal.ofReal (Submission.BoseGases.fsKinCoeff c ‖p‖ *
            ‖Work.BSKinetic.Decomp.bsPsi h p‖ ^ 2))
          = ∫⁻ p : E3, Filter.liminf (fun n => ENNReal.ofReal (Submission.BoseGases.fsKinCoeff c ‖p‖ *
              ‖Work.BSKinetic.Decomp.bsPsi (u n) p‖ ^ 2)) atTop := by
            refine MeasureTheory.lintegral_congr_ae ?_
            filter_upwards with p
            exact (ENNReal.continuous_ofReal.tendsto _ |>.comp (hFS_tend p)).liminf_eq.symm
        _ ≤ Filter.liminf (fun n => ∫⁻ p : E3, ENNReal.ofReal (Submission.BoseGases.fsKinCoeff c ‖p‖ *
              ‖Work.BSKinetic.Decomp.bsPsi (u n) p‖ ^ 2)) atTop :=
            MeasureTheory.lintegral_liminf_le' fun n =>
              (ENNReal.continuous_ofReal.comp_aestronglyMeasurable
                (hInt n).aestronglyMeasurable).aemeasurable
    refine h1.trans ?_
    refine Filter.liminf_le_of_le ⟨0, Eventually.of_forall fun n => bot_le⟩ ?_
    intro b hb
    rcases (Filter.eventually_atTop.1 hb) with ⟨N, hN⟩
    have h2 : (∫⁻ p : E3, ENNReal.ofReal (Submission.BoseGases.fsKinCoeff c ‖p‖ *
          ‖Work.BSKinetic.Decomp.bsPsi (u N) p‖ ^ 2))
        = ENNReal.ofReal (∫ p : E3, Submission.BoseGases.fsKinCoeff c ‖p‖ *
            ‖Work.BSKinetic.Decomp.bsPsi (u N) p‖ ^ 2) :=
      (MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hInt N)
        (Eventually.of_forall fun p => mul_nonneg (fsKinCoeff_nonneg c ‖p‖) (sq_nonneg _))).symm
    calc b ≤ (∫⁻ p : E3, ENNReal.ofReal (Submission.BoseGases.fsKinCoeff c ‖p‖ *
            ‖Work.BSKinetic.Decomp.bsPsi (u N) p‖ ^ 2)) := hN N le_rfl
      _ = ENNReal.ofReal (∫ p : E3, Submission.BoseGases.fsKinCoeff c ‖p‖ *
            ‖Work.BSKinetic.Decomp.bsPsi (u N) p‖ ^ 2) := h2
      _ ≤ ENNReal.ofReal (2 * (1 + c ^ 2) * ((2 * Real.pi) ^ 3 *
            (A ^ 2 * (2 * (R + 1)) ^ 3 + 3 * (L ^ 2 * (2 * (R + 1)) ^ 3)))) :=
          ENNReal.ofReal_le_ofReal (hB N)
  -- conclude
  have hfin : Work.BSKinetic.Decomp.bsW (Submission.BoseGases.fsKinCoeff c) h
      ≤ 2 * (1 + c ^ 2) * ((2 * Real.pi) ^ 3 *
          (A ^ 2 * (2 * (R + 1)) ^ 3 + 3 * (L ^ 2 * (2 * (R + 1)) ^ 3))) := by
    have hval : Work.BSKinetic.Decomp.bsW (Submission.BoseGases.fsKinCoeff c) h
        = (∫⁻ p : E3, ENNReal.ofReal (Submission.BoseGases.fsKinCoeff c ‖p‖ *
            ‖Work.BSKinetic.Decomp.bsPsi h p‖ ^ 2)).toReal := by
      rw [Work.BSKinetic.Decomp.bsW,
        MeasureTheory.integral_eq_lintegral_of_nonneg_ae
          (Eventually.of_forall fun p => mul_nonneg (fsKinCoeff_nonneg c ‖p‖) (sq_nonneg _))
          hFS_sm]
    rw [hval]
    calc (∫⁻ p : E3, ENNReal.ofReal (Submission.BoseGases.fsKinCoeff c ‖p‖ *
          ‖Work.BSKinetic.Decomp.bsPsi h p‖ ^ 2)).toReal
        ≤ (ENNReal.ofReal (2 * (1 + c ^ 2) * ((2 * Real.pi) ^ 3 *
            (A ^ 2 * (2 * (R + 1)) ^ 3 + 3 * (L ^ 2 * (2 * (R + 1)) ^ 3))))).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hFatou
      _ = 2 * (1 + c ^ 2) * ((2 * Real.pi) ^ 3 *
            (A ^ 2 * (2 * (R + 1)) ^ 3 + 3 * (L ^ 2 * (2 * (R + 1)) ^ 3))) :=
          ENNReal.toReal_ofReal (by positivity)
  refine hfin.trans ?_
  have h3 : A ^ 2 * (2 * (R + 1)) ^ 3 + 3 * (L ^ 2 * (2 * (R + 1)) ^ 3)
      ≤ 24 * (A ^ 2 + L ^ 2) * (1 + R) ^ 4 := by
    have h4 : (2 * (R + 1)) ^ 3 = 8 * (R + 1) ^ 3 := by ring
    have h5 : (1 : ℝ) ≤ (1 + R) := by linarith
    have h6 : (R + 1) ^ 3 ≤ (1 + R) ^ 4 := by
      calc (R + 1) ^ 3 = (1 + R) ^ 3 := by ring
        _ ≤ (1 + R) ^ 3 * (1 + R) := le_mul_of_one_le_right (by positivity) h5
        _ = (1 + R) ^ 4 := by ring
    rw [h4]
    have h7 : A ^ 2 * (8 * (R + 1) ^ 3) ≤ A ^ 2 * (8 * (1 + R) ^ 4) :=
      mul_le_mul_of_nonneg_left (by linarith [h6]) (sq_nonneg A)
    have h8 : L ^ 2 * (8 * (R + 1) ^ 3) ≤ L ^ 2 * (8 * (1 + R) ^ 4) :=
      mul_le_mul_of_nonneg_left (by linarith [h6]) (sq_nonneg L)
    have hP : (0 : ℝ) ≤ (1 + R) ^ 4 := by positivity
    have h9 : A ^ 2 * (8 * (1 + R) ^ 4) + 3 * (L ^ 2 * (8 * (1 + R) ^ 4))
        ≤ 24 * (A ^ 2 + L ^ 2) * (1 + R) ^ 4 := by
      nlinarith [sq_nonneg A, sq_nonneg L, hP]
    linarith [h7, h8, h9]
  calc 2 * (1 + c ^ 2) * ((2 * Real.pi) ^ 3 *
        (A ^ 2 * (2 * (R + 1)) ^ 3 + 3 * (L ^ 2 * (2 * (R + 1)) ^ 3)))
      ≤ 2 * (1 + c ^ 2) * ((2 * Real.pi) ^ 3 * (24 * (A ^ 2 + L ^ 2) * (1 + R) ^ 4)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = 48 * (2 * Real.pi) ^ 3 * (1 + c ^ 2) * (A ^ 2 + L ^ 2) * (1 + R) ^ 4 := by ring

/-! ## 4. The `u`-integrability of the two cut kinetic words -/

/-- **`u`-integrability of the cut kinetic word with a mean shift.**

For `0 < ℓ`, `0 < d`, a smooth `g` and a measurable, uniformly bounded shift `ρ`, the function

  `u ↦ bsW (fsKinCoeff c) (χ_{B(u)}·(g − ρ u))`

is Lebesgue-integrable on `ℝ³`: it is a.e. strongly measurable
(`aemeasurable_bsW_windowCube`), uniformly bounded (`chiSmallB_mul_uniformBounds_self` +
`bsW_fsKinCoeff_le_lipschitz`), and it vanishes identically off the fixed cube
`acube ((1+d)/d)` (`chiSmallB_eq_zero_of_not_mem_acube_u`), so the indicator of that cube is an
integrable majorant. -/
theorem integrable_bsW_chiSmallB_sub {M : ℕ} (hM : 1 ≤ M) {ℓ d c : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    {g : E3 → ℝ} (hg : ContDiff ℝ (⊤ : ENat) g) {ρ : E3 → ℝ} (hρ : Measurable ρ)
    (hρbd : ∃ C : ℝ, ∀ u : E3, |ρ u| ≤ C) :
    MeasureTheory.Integrable (fun u : E3 =>
      Work.BSKinetic.Decomp.bsW (Submission.BoseGases.fsKinCoeff c)
        (fun z : E3 => Submission.BoseGases.chiSmallB M ℓ d u z * (g z - ρ u))) := by
  obtain ⟨C, hC⟩ := hρbd
  obtain ⟨A, L, hA0, hL0, hunif⟩ :=
    chiSmallB_mul_uniformBounds_self (M := M) hM (ℓ := ℓ) (d := d) hℓ hd g hg C
  obtain ⟨Cm, hCm0, hCm⟩ := bsW_fsKinCoeff_le_lipschitz_self
  have hR0 : (0 : ℝ) ≤ ℓ / 2 := by linarith
  set B : ℝ := Cm * (1 + c ^ 2) * (A ^ 2 + L ^ 2) * (1 + ℓ / 2) ^ 4 with hB
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have hrd : 0 ≤ (1 + d) / d := by positivity
  have hmaj : MeasureTheory.Integrable
      ((Submission.BoseGases.acube ((1 + d) / d)).indicator (fun _ : E3 => B)) := by
    rw [MeasureTheory.integrable_indicator_iff (Submission.BoseGases.acube_measurable _)]
    exact MeasureTheory.integrableOn_const
      (ne_of_lt (Submission.BoseGases.acube_lt_top _ hrd)) (by simp)
  refine MeasureTheory.Integrable.mono' hmaj ?_ ?_
  · have hWmeas : Measurable (Function.uncurry (fun u z : E3 => g z - ρ u)) := by
      show Measurable (fun q : E3 × E3 => g q.2 - ρ q.1)
      exact (hg.continuous.measurable.comp measurable_snd).sub (hρ.comp measurable_fst)
    exact (aemeasurable_bsW_windowCube (χ := Submission.BoseGases.chiSmallB M ℓ d)
      (c := c) (continuous_uncurry_chiSmallB M hM ℓ d) hWmeas).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun u => ?_
    by_cases hu : u ∈ Submission.BoseGases.acube ((1 + d) / d)
    · rw [Set.indicator_of_mem hu]
      obtain ⟨hsup, hlip, hsupp⟩ := hunif ρ hC u
      have hcont : Continuous
          (fun z : E3 => Submission.BoseGases.chiSmallB M ℓ d u z * (g z - ρ u)) :=
        (Work.BoseFixB1S.chiSmallB_continuous hM ℓ d u).mul (hg.continuous.sub continuous_const)
      have hbound := hCm (c := c) (A := A) (L := L) (R := ℓ / 2) hA0 hL0 hR0
        hcont hsup hlip hsupp
      rw [Real.norm_of_nonneg (bsW_fsKinCoeff_nonneg_cw c _)]
      simpa [hB] using hbound
    · rw [Set.indicator_of_notMem hu]
      have hzero : (fun z : E3 => Submission.BoseGases.chiSmallB M ℓ d u z * (g z - ρ u))
          = (fun _ : E3 => (0 : ℝ)) := by
        funext z
        rw [chiSmallB_eq_zero_of_not_mem_acube_u hM hℓ hd hu z, zero_mul]
      rw [hzero, bsW_zero_cw, norm_zero]

/-! ## 5. The `u`-marginal of `χ_{B(u)}²w²` -/

/-- **Conjuncts 3 and 4 of `marginalCube`**: the `u`-marginal of `χ_{B(u)}² w²` is integrable and
its `u`-integral collapses to `∫_z χ(z/ℓ)² w(z)²`.

The joint integrand `(u,z) ↦ χ_{B(u)}(z)² w(z)²` is continuous with compact support inside the
product of the fixed cubes `acube ((1+d)/d) × acube ℓ` (the `u`- and `z`-supports of the window), so
it is jointly integrable; `Integrable.integral_prod_left` gives conjunct 3, and the exchange of the
two integrals plus the pointwise partition identity
`Work.LocRepoint.chiSmallB_sq_integral_u` (`∫_u χ_{B(u)}(z)² = χ(z/ℓ)²`) gives conjunct 4. -/
theorem integrable_and_marginal_chiSmallB {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    {w : E3 → ℝ} (hw : ContDiff ℝ (⊤ : ENat) w) :
    MeasureTheory.Integrable (fun u : E3 => ∫ z : E3,
        (Submission.BoseGases.chiSmallB M ℓ d u z) ^ 2 * (w z) ^ 2)
      ∧ (∫ u : E3, ∫ z : E3,
            (Submission.BoseGases.chiSmallB M ℓ d u z) ^ 2 * (w z) ^ 2)
        = ∫ z : E3, (Submission.BoseGases.chiScale ℓ z) ^ 2 * (w z) ^ 2 := by
  have hχc : Continuous (Function.uncurry (Submission.BoseGases.chiSmallB M ℓ d)) :=
    continuous_uncurry_chiSmallB M hM ℓ d
  have hrd : 0 < (1 + d) / d := div_pos (by linarith) hd
  have hjoint : MeasureTheory.Integrable
      (Function.uncurry (fun u z : E3 =>
        (Submission.BoseGases.chiSmallB M ℓ d u z) ^ 2 * (w z) ^ 2))
      ((volume : Measure E3).prod (volume : Measure E3)) := by
    have hcont : Continuous (fun p : E3 × E3 =>
        (Submission.BoseGases.chiSmallB M ℓ d p.1 p.2) ^ 2 * (w p.2) ^ 2) :=
      (hχc.pow 2).mul ((hw.continuous.comp continuous_snd).pow 2)
    refine hcont.integrable_of_hasCompactSupport
      (HasCompactSupport.of_support_subset_isCompact
        ((Submission.BoseGases.acube_compact hrd).prod (Submission.BoseGases.acube_compact hℓ)) ?_)
    rintro ⟨u, z⟩ hp
    have hp' : (Submission.BoseGases.chiSmallB M ℓ d u z) ^ 2 * (w z) ^ 2 ≠ 0 := hp
    have hne : Submission.BoseGases.chiSmallB M ℓ d u z ≠ 0 := by
      intro h0
      exact hp' (by rw [h0]; ring)
    refine ⟨mem_acube_u_of_chiSmallB_ne_zero hM hℓ hd hne, ?_⟩
    rw [Submission.BoseGases.mem_acube_iff]
    intro m
    have hb := abs_le.mp (Submission.BoseGases.chiSmallB_support_big_box hM hℓ hne m)
    exact Set.mem_Icc.mpr ⟨by linarith [hb.1], by linarith [hb.2]⟩
  refine ⟨hjoint.integral_prod_left, ?_⟩
  rw [MeasureTheory.integral_integral_swap hjoint]
  have hperz : ∀ z : E3, (∫ u : E3,
      (Submission.BoseGases.chiSmallB M ℓ d u z) ^ 2 * (w z) ^ 2)
      = (Submission.BoseGases.chiScale ℓ z) ^ 2 * (w z) ^ 2 := by
    intro z
    have hpt : (fun u : E3 => (Submission.BoseGases.chiSmallB M ℓ d u z) ^ 2 * (w z) ^ 2)
        = fun u : E3 => (w z) ^ 2 * (Submission.BoseGases.chiSmallB M ℓ d u z) ^ 2 := by
      funext u; ring
    rw [hpt, MeasureTheory.integral_const_mul]
    have h1 : (∫ u : E3, (Submission.BoseGases.chiSmallB M ℓ d u z) ^ 2)
        = (Submission.BoseGases.chiScale ℓ z) ^ 2 :=
      Work.LocRepoint.chiSmallB_sq_integral_u (M := M) hM hℓ hd z
    rw [h1]
    ring
  exact integral_congr_ae (Filter.Eventually.of_forall hperz)

/-! ## 6. The main lemma -/

/-- **Marginal integrability at the cube cutoff**: the four conjuncts that the mean-mismatch
assembly consumes -- `u`-integrability of the two windowed kinetic words (with the *sliding* box
mean in the second), `u`-integrability of the `x`-space marginal of `χ_{B(u)}²w²`, and the pointwise
partition identity `∫_u χ_{B(u)}(z)² du = χ(z/ℓ)²` integrated against `w²`.  Cube twin of the four
conjuncts of `Work.BoseFixB1.KH.corr.Marginal` (`integrable_and_marginal_chiB`). -/
theorem marginalCube (M : ℕ) (hM : 1 ≤ M) {ℓ d c : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) :
    ∀ w : EuclideanSpace ℝ (Fin 3) → ℝ, ContDiff ℝ (⊤ : ENat) w →
      MeasureTheory.Integrable (fun u : EuclideanSpace ℝ (Fin 3) => Work.BSKinetic.Decomp.bsW
          (Submission.BoseGases.fsKinCoeff c)
          (fun z : EuclideanSpace ℝ (Fin 3) => Submission.BoseGases.chiSmallB M ℓ d u z * w z))
    ∧ MeasureTheory.Integrable (fun u : EuclideanSpace ℝ (Fin 3) => Work.BSKinetic.Decomp.bsW
          (Submission.BoseGases.fsKinCoeff c)
          (fun z : EuclideanSpace ℝ (Fin 3) => Submission.BoseGases.chiSmallB M ℓ d u z *
            (w z - (1 / Work.SmallBoxSliding.boxMass ℓ d u) *
              (∫ z' in Submission.BoseGases.dlBox ℓ d u, w z'))))
    ∧ MeasureTheory.Integrable (fun u : EuclideanSpace ℝ (Fin 3) => ∫ z : EuclideanSpace ℝ (Fin 3),
          (Submission.BoseGases.chiSmallB M ℓ d u z) ^ 2 * (w z) ^ 2)
    ∧ (∫ u : EuclideanSpace ℝ (Fin 3), ∫ z : EuclideanSpace ℝ (Fin 3),
          (Submission.BoseGases.chiSmallB M ℓ d u z) ^ 2 * (w z) ^ 2)
      = (∫ z : EuclideanSpace ℝ (Fin 3), (Submission.BoseGases.chiScale ℓ z) ^ 2 * (w z) ^ 2) := by
  intro w hw
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := integrable_bsW_chiSmallB_sub (M := M) hM (ℓ := ℓ) (d := d) (c := c) hℓ hd
      (g := w) hw (ρ := fun _ : E3 => (0 : ℝ)) measurable_const ⟨0, fun u => by simp⟩
    simpa using h
  · obtain ⟨hρm, hρb⟩ :=
      Work.BoseFixB1S.corrMarg.measurable_and_bound_boxMean (ℓ := ℓ) (d := d) hℓ hd hw.continuous
    obtain ⟨C, hC0, hC⟩ := hρb
    have h := integrable_bsW_chiSmallB_sub (M := M) hM (ℓ := ℓ) (d := d) (c := c) hℓ hd
      (g := w) hw
      (ρ := fun u : E3 => (1 / Work.SmallBoxSliding.boxMass ℓ d u) *
        ∫ z' in Submission.BoseGases.dlBox ℓ d u, w z')
      (by simpa only [one_div] using hρm)
      (⟨C, fun u => by simpa only [one_div] using hC u⟩)
    simpa using h
  · exact (integrable_and_marginal_chiSmallB (M := M) hM hℓ hd hw).1
  · exact (integrable_and_marginal_chiSmallB (M := M) hM hℓ hd hw).2

end Work.BoseFixB1S.CubeWindow
