import Mathlib
import Submission.Work.Drive.N2.FieldData
import Submission.Work.Drive.N2.contDiff_levelField
import Submission.Work.ODE.SmoothFlow
import Submission.Work.ODE.CompactSupportBounds
import Submission.Work.ODE.GlobalFlow
import Submission.Work.Whitney.CutPush.flow_of_compactSupport
import Submission.Work.Drive.N2.jointFlowAssembly
import Submission.Work.Drive.N2.smoothCutoff

/-!

This file proves `Work.Drive.N2.exists_flow_jointSmooth_levelField`: the flow of the compactly
supported level field `levelField E G χ` exists, is a one-parameter group of self-maps of `ℝ^N`,
has the level field as its velocity, and is jointly `C^∞` in `(time, initial condition)`.

It must NOT import `Submission.Work.Drive.N2.contDiff_flow_joint`, because that module declares a
constant `Work.Drive.N2.auxField` clashing with the `Work.Drive.N2.auxField` of
`Submission.Work.Drive.N2.FieldData` (needed here).  Instead the internal argument of that module
(which reduces joint smoothness of the flow of a field `X` to that of the auxiliary field
`(a, z) ↦ (1, χ a • X z)` on `ℝ × ℝ^N`, whose flow is `(a,z) ↦ (a + σ, FL (∫_0^σ χ (a+s) ds) z)`)
is reproduced below with every auxiliary name prefixed `cut`, and applied to `X = levelField E G χ`
with the bounds provided by compact support (`Work.ODE.exists_norm_le_of_hasCompactSupport`).

-/

set_option autoImplicit false

open scoped Topology NNReal ContDiff
open Set Function

namespace Work.Drive.N2

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

/-- The auxiliary field `p ↦ (1, χ p.1 • X p.2)` on `ℝ × E`. -/
noncomputable def cutAuxField (χ : ℝ → ℝ) (X : E → E) (p : ℝ × E) : ℝ × E :=
  (1, χ p.1 • X p.2)

/-- The effective time `σ ↦ ∫_0^σ χ (a + s) ds`. -/
noncomputable def cutTau (χ : ℝ → ℝ) (σ a : ℝ) : ℝ := ∫ s in (0 : ℝ)..σ, χ (a + s)

/-- The candidate flow of the auxiliary field. -/
noncomputable def cutAuxFlow (χ : ℝ → ℝ) (FL : ℝ → E → E) (σ : ℝ) (p : ℝ × E) : ℝ × E :=
  (p.1 + σ, FL (cutTau χ σ p.1) p.2)

lemma cutAuxFlow_apply (χ : ℝ → ℝ) (FL : ℝ → E → E) (σ : ℝ) (p : ℝ × E) :
    cutAuxFlow χ FL σ p = (p.1 + σ, FL (cutTau χ σ p.1) p.2) := rfl

lemma contDiff_cutAuxField {χ : ℝ → ℝ} {X : E → E}
    (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    (hX : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) X) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (cutAuxField χ X) := by
  unfold cutAuxField
  refine ContDiff.prodMk contDiff_const ?_
  exact (hχ.comp contDiff_fst).smul (hX.comp contDiff_snd)

lemma norm_cutAuxField_le {χ : ℝ → ℝ} {X : E → E} {M : ℝ} (hχbd : ∀ a, |χ a| ≤ 3)
    (hM : ∀ z, ‖X z‖ ≤ M) (p : ℝ × E) : ‖cutAuxField χ X p‖ ≤ max 1 (3 * M) := by
  rw [cutAuxField, Prod.norm_def, norm_one]
  refine max_le (le_max_left _ _) ?_
  rw [norm_smul, Real.norm_eq_abs]
  exact (mul_le_mul (hχbd p.1) (hM p.2) (norm_nonneg _) (by norm_num)).trans (le_max_right _ _)

lemma cutAuxField_sub {χ : ℝ → ℝ} {X : E → E} (a a' : ℝ) (z z' : E) :
    cutAuxField χ X (a, z) - cutAuxField χ X (a', z') = (0, χ a • X z - χ a' • X z') := by
  rw [cutAuxField, cutAuxField, Prod.mk_sub_mk, sub_self]

lemma norm_cutAuxField_sub_le {χ : ℝ → ℝ} {X : E → E} {M K L : ℝ}
    (hχlip : ∀ a b, |χ a - χ b| ≤ L * |a - b|)
    (hXsub : ∀ a b, ‖X a - X b‖ ≤ K * ‖a - b‖) (hχbd : ∀ a, |χ a| ≤ 3)
    (hM : ∀ z, ‖X z‖ ≤ M) (hL0 : 0 ≤ L) (hM0 : 0 ≤ M) (hK0 : 0 ≤ K)
    (p q : ℝ × E) : ‖cutAuxField χ X p - cutAuxField χ X q‖ ≤ (L * M + 3 * K) * ‖p - q‖ := by
  obtain ⟨a, z⟩ := p
  obtain ⟨a', z'⟩ := q
  rw [cutAuxField_sub, Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _)]
  have hsplit : χ a • X z - χ a' • X z' = (χ a - χ a') • X z + χ a' • (X z - X z') := by
    rw [sub_smul, smul_sub]; abel
  rw [hsplit]
  have hA : |a - a'| ≤ ‖(a, z) - (a', z')‖ := by
    rw [show (a, z) - (a', z') = (a - a', z - z') from rfl, Prod.norm_def, Real.norm_eq_abs]
    exact le_max_left _ _
  have hZ : ‖z - z'‖ ≤ ‖(a, z) - (a', z')‖ := by
    rw [show (a, z) - (a', z') = (a - a', z - z') from rfl, Prod.norm_def]
    exact le_max_right _ _
  calc ‖(χ a - χ a') • X z + χ a' • (X z - X z')‖
      ≤ ‖(χ a - χ a') • X z‖ + ‖χ a' • (X z - X z')‖ := norm_add_le _ _
    _ = |χ a - χ a'| * ‖X z‖ + |χ a'| * ‖X z - X z'‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ (L * |a - a'|) * M + 3 * (K * ‖z - z'‖) := by
        refine add_le_add ?_ ?_
        · exact mul_le_mul (hχlip a a') (hM z) (norm_nonneg _) (mul_nonneg hL0 (abs_nonneg _))
        · exact mul_le_mul (hχbd a') (hXsub z z') (norm_nonneg _) (by norm_num)
    _ ≤ (L * M + 3 * K) * ‖(a, z) - (a', z')‖ := by
        have h1 : (L * |a - a'|) * M = L * M * |a - a'| := by ring
        have h2 : 3 * (K * ‖z - z'‖) = 3 * K * ‖z - z'‖ := by ring
        rw [h1, h2]
        have h3 : L * M * |a - a'| ≤ L * M * ‖(a, z) - (a', z')‖ :=
          mul_le_mul_of_nonneg_left hA (mul_nonneg hL0 hM0)
        have h4 : 3 * K * ‖z - z'‖ ≤ 3 * K * ‖(a, z) - (a', z')‖ :=
          mul_le_mul_of_nonneg_left hZ (by positivity)
        calc L * M * |a - a'| + 3 * K * ‖z - z'‖
            ≤ L * M * ‖(a, z) - (a', z')‖ + 3 * K * ‖(a, z) - (a', z')‖ := add_le_add h3 h4
          _ = (L * M + 3 * K) * ‖(a, z) - (a', z')‖ := by ring

lemma lipschitz_cutAuxField {χ : ℝ → ℝ} {X : E → E} {M K L : ℝ}
    (hχlip : ∀ a b, |χ a - χ b| ≤ L * |a - b|)
    (hXsub : ∀ a b, ‖X a - X b‖ ≤ K * ‖a - b‖) (hχbd : ∀ a, |χ a| ≤ 3)
    (hM : ∀ z, ‖X z‖ ≤ M) (hL0 : 0 ≤ L) (hM0 : 0 ≤ M) (hK0 : 0 ≤ K) :
    LipschitzWith (L * M + 3 * K).toNNReal (cutAuxField χ X) :=
  LipschitzWith.of_dist_le_mul fun p q => by
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (by positivity)]
    exact norm_cutAuxField_sub_le hχlip hXsub hχbd hM hL0 hM0 hK0 p q

lemma norm_fderiv_cutAuxField_le {χ : ℝ → ℝ} {X : E → E} {M K L : ℝ}
    (hχsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    (hXsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) X)
    (hχlip : ∀ a b, |χ a - χ b| ≤ L * |a - b|)
    (hXsub : ∀ a b, ‖X a - X b‖ ≤ K * ‖a - b‖) (hχbd : ∀ a, |χ a| ≤ 3)
    (hM : ∀ z, ‖X z‖ ≤ M) (hL0 : 0 ≤ L) (hM0 : 0 ≤ M) (hK0 : 0 ≤ K) :
    ∀ p : ℝ × E, ‖fderiv ℝ (cutAuxField χ X) p‖ ≤ L * M + 3 * K := by
  intro p
  have hd : HasFDerivAt (cutAuxField χ X) (fderiv ℝ (cutAuxField χ X) p) p :=
    ((contDiff_cutAuxField hχsm hXsm).differentiable (by simp)).differentiableAt.hasFDerivAt
  have h := hd.le_of_lipschitz (lipschitz_cutAuxField hχlip hXsub hχbd hM hL0 hM0 hK0)
  rwa [Real.coe_toNNReal _ (by positivity)] at h

lemma cutAuxFlow_zero {χ : ℝ → ℝ} {FL : ℝ → E → E} (h0 : ∀ p, FL 0 p = p) (p : ℝ × E) :
    cutAuxFlow χ FL 0 p = p := by
  simp [cutAuxFlow, cutTau, h0]

lemma isIntegralCurve_cutAuxFlow {χ : ℝ → ℝ} {X : E → E} {FL : ℝ → E → E}
    (hχcont : Continuous χ)
    (hcurve : ∀ p, IsIntegralCurve (fun s => FL s p) (fun _ z => X z)) (p : ℝ × E) :
    IsIntegralCurve (fun σ => cutAuxFlow χ FL σ p) (fun _ q => cutAuxField χ X q) := by
  intro σ
  have hτ : HasDerivAt (fun σ : ℝ => cutTau χ σ p.1) (χ (p.1 + σ)) σ := by
    have hc : Continuous fun s : ℝ => χ (p.1 + s) := hχcont.comp (continuous_const.add continuous_id)
    have h := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable (0 : ℝ) σ)
      (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt
    simpa [cutTau] using h
  have h2 : HasDerivAt (fun σ : ℝ => FL (cutTau χ σ p.1) p.2)
      (χ (p.1 + σ) • X (FL (cutTau χ σ p.1) p.2)) σ := by
    have h := (hcurve p.2 (cutTau χ σ p.1)).scomp (x := σ) hτ
    simpa [Function.comp_def] using h
  have h1 : HasDerivAt (fun σ : ℝ => p.1 + σ) 1 σ := (hasDerivAt_id σ).const_add p.1
  have h3 := h1.prodMk h2
  simpa [cutAuxFlow, cutAuxField] using h3

lemma cutAuxFlow_semigroup {χ : ℝ → ℝ} {X : E → E} {FL : ℝ → E → E}
    (h0 : ∀ p, FL 0 p = p)
    (hcurve : ∀ p, IsIntegralCurve (fun s => FL s p) (fun _ z => X z))
    (hχcont : Continuous χ) {L : NNReal} (hZlip : LipschitzWith L (cutAuxField χ X)) :
    ∀ σ σ' p, cutAuxFlow χ FL (σ + σ') p = cutAuxFlow χ FL σ (cutAuxFlow χ FL σ' p) := by
  intro σ σ' p
  have h1 : IsIntegralCurve (fun σ : ℝ => cutAuxFlow χ FL (σ + σ') p) (fun _ q => cutAuxField χ X q) := by
    have h := (isIntegralCurve_cutAuxFlow (X := X) hχcont hcurve p).comp_add σ'
    simpa [Function.comp_def] using h
  have h2 : IsIntegralCurve (fun σ : ℝ => cutAuxFlow χ FL σ (cutAuxFlow χ FL σ' p))
      (fun _ q => cutAuxField χ X q) :=
    isIntegralCurve_cutAuxFlow (X := X) hχcont hcurve (cutAuxFlow χ FL σ' p)
  have h0' : (fun σ : ℝ => cutAuxFlow χ FL (σ + σ') p) 0
      = (fun σ : ℝ => cutAuxFlow χ FL σ (cutAuxFlow χ FL σ' p)) 0 := by
    simp [cutAuxFlow_zero h0]
  have := Work.ODE.eq_of_isIntegralCurve hZlip h1 h2 h0'
  exact congrFun this σ

lemma cutAuxFlow_nsmul {χ : ℝ → ℝ} {X : E → E} {FL : ℝ → E → E}
    (h0 : ∀ p, FL 0 p = p)
    (hcurve : ∀ p, IsIntegralCurve (fun s => FL s p) (fun _ z => X z))
    (hχcont : Continuous χ) {L : NNReal} (hZlip : LipschitzWith L (cutAuxField χ X)) (s : ℝ) :
    ∀ (k : ℕ) (p : ℝ × E), cutAuxFlow χ FL ((k : ℝ) * s) p = (cutAuxFlow χ FL s)^[k] p := by
  intro k
  induction k with
  | zero => intro p; simp [Function.iterate_zero, cutAuxFlow_zero h0]
  | succ k ih =>
      intro p
      rw [show ((k.succ : ℕ) : ℝ) * s = (k : ℝ) * s + s by push_cast; ring]
      rw [cutAuxFlow_semigroup h0 hcurve hχcont hZlip ((k : ℝ) * s) s p,
        ih (cutAuxFlow χ FL s p), Function.iterate_succ_apply]


/-- **Local joint smoothness of the flow**, via the auxiliary field `(a,z) ↦ (1, χ a • X z)`. -/
theorem contDiffOn_joint_small_of_cutoffLevel {χ : ℝ → ℝ} {L : NNReal} {X : E → E}
    (hX : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) X) (M K : ℝ)
    (hM : ∀ z, ‖X z‖ ≤ M) (hK : ∀ z, ‖fderiv ℝ X z‖ ≤ K) (FL : ℝ → E → E)
    (h0 : ∀ p, FL 0 p = p)
    (hsem : ∀ s t p, FL (s + t) p = FL s (FL t p))
    (hcurve : ∀ p, IsIntegralCurve (fun s => FL s p) (fun _ z => X z))
    (hχsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) (hχid : ∀ a : ℝ, |a| ≤ 2 → χ a = a)
    (hχbd : ∀ a : ℝ, |χ a| ≤ 3) (hχlip : LipschitzWith L χ) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × E => FL p.1 p.2)
      (Set.Ioo (-3/2) (3/2) ×ˢ (Set.univ : Set E)) := by
  have hM0 : 0 ≤ M := (norm_nonneg (X 0)).trans (hM 0)
  have hK0 : 0 ≤ K := (norm_nonneg (fderiv ℝ X 0)).trans (hK 0)
  have hL0 : (0 : ℝ) ≤ L := L.coe_nonneg
  have hX1 : ContDiff ℝ 1 X := hX.of_le (by exact_mod_cast le_top)
  have hXsub : ∀ a b : E, ‖X a - X b‖ ≤ K * ‖a - b‖ :=
    Work.ODE.norm_sub_le_of_norm_fderiv_le hX1 hK
  have hχlip' : ∀ a b : ℝ, |χ a - χ b| ≤ (L : ℝ) * |a - b| := by
    intro a b
    have h := hχlip.dist_le_mul a b
    simpa [Real.dist_eq] using h
  have hχcont : Continuous χ := hχsm.continuous
  have hZsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (cutAuxField χ X) := contDiff_cutAuxField hχsm hX
  have hZbd : ∀ p : ℝ × E, ‖cutAuxField χ X p‖ ≤ max 1 (3 * M) :=
    fun p => norm_cutAuxField_le hχbd hM p
  have hZlip : LipschitzWith (L * M + 3 * K).toNNReal (cutAuxField χ X) :=
    lipschitz_cutAuxField hχlip' hXsub hχbd hM hL0 hM0 hK0
  have hZderiv : ∀ p : ℝ × E, ‖fderiv ℝ (cutAuxField χ X) p‖ ≤ L * M + 3 * K :=
    norm_fderiv_cutAuxField_le hχsm hX hχlip' hXsub hχbd hM hL0 hM0 hK0
  obtain ⟨δ, hδpos, hδsm⟩ := Work.ODE.contDiff_flow_timeSlice (cutAuxField χ X) hZsm
    (max 1 (3 * M)) (L * M + 3 * K) hZbd hZderiv (cutAuxFlow χ FL)
    (fun t y => ⟨fun σ => cutAuxFlow χ FL σ y, cutAuxFlow_zero h0 y,
      isIntegralCurve_cutAuxFlow hχcont hcurve y, rfl⟩)
  obtain ⟨n, hnpos, hnle⟩ : ∃ n : ℕ, 0 < n ∧ (1 : ℝ) / (n : ℝ) ≤ δ := by
    obtain ⟨n, hn⟩ := exists_nat_gt ((1 : ℝ) / δ)
    have hnpos : 0 < n := by
      by_contra h
      have h0 : (n : ℝ) ≤ 0 := by exact_mod_cast Nat.le_of_not_lt h
      have : (1 : ℝ) / δ ≤ 0 := (lt_of_lt_of_le hn h0).le
      linarith [one_div_pos.mpr hδpos]
    refine ⟨n, hnpos, ?_⟩
    rw [div_le_iff₀ (by exact_mod_cast hnpos : (0 : ℝ) < (n : ℝ))]
    have h1 : δ * (1 / δ) = 1 := by field_simp
    have h2 : δ * (1 / δ) ≤ δ * n := mul_le_mul_of_nonneg_left hn.le hδpos.le
    rw [h1] at h2
    linarith
  have hiter : ∀ k : ℕ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ((cutAuxFlow χ FL (1 / (n : ℝ)))^[k]) := by
    intro k
    induction k with
    | zero => simpa using contDiff_id
    | succ k ih =>
        have hcomp : ((cutAuxFlow χ FL (1 / (n : ℝ)))^[k.succ])
            = (cutAuxFlow χ FL (1 / (n : ℝ))) ∘ ((cutAuxFlow χ FL (1 / (n : ℝ)))^[k]) := by
          funext x
          rw [Function.iterate_succ_apply', Function.comp_apply]
        rw [hcomp]
        exact (hδsm (1 / (n : ℝ)) (by rw [abs_of_nonneg (by positivity)]; exact hnle)).comp ih
  have hΨ1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × E => cutAuxFlow χ FL 1 p) := by
    have hmul : (n : ℝ) * (1 / (n : ℝ)) = 1 := by field_simp
    have hfun : (fun p : ℝ × E => cutAuxFlow χ FL 1 p)
        = ((cutAuxFlow χ FL (1 / (n : ℝ)))^[n]) := by
      funext p
      have := cutAuxFlow_nsmul h0 hcurve hχcont hZlip (1 / (n : ℝ)) n p
      rwa [hmul] at this
    rw [hfun]
    exact hiter n
  have hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × E => (cutAuxFlow χ FL 1 p).2) := hΨ1.snd
  have hτ1 : ∀ a : ℝ, a ∈ Set.Ioo (-2) 1 → cutTau χ 1 a = a + 1 / 2 := by
    intro a ha
    have hτ : cutTau χ 1 a = ∫ u in a..(a+1), χ u := by
      rw [cutTau]
      rw [show (∫ s in (0 : ℝ)..1, χ (a + s)) = ∫ s in (0 : ℝ)..1, χ (s + a) from
        intervalIntegral.integral_congr (fun s _ => by rw [add_comm])]
      rw [intervalIntegral.integral_comp_add_right]
      rw [show (0 : ℝ) + a = a from by ring, show (1 : ℝ) + a = a + 1 from by ring]
    rw [hτ]
    have hcongr : EqOn (fun u : ℝ => χ u) (fun u : ℝ => u) (Set.uIcc a (a + 1)) := by
      intro u hu
      rw [Set.uIcc_of_le (by linarith [ha.2] : a ≤ a + 1)] at hu
      exact hχid u (by rw [abs_le]; constructor <;> linarith [hu.1, hu.2, ha.1, ha.2])
    rw [intervalIntegral.integral_congr hcongr]
    have hderiv : ∀ x ∈ Set.uIcc a (a + 1), HasDerivAt (fun u : ℝ => u ^ 2 / 2) x x := by
      intro x hx
      have h : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
        simpa using (hasDerivAt_pow 2 x)
      have h2 : HasDerivAt (fun u : ℝ => u ^ 2 / 2) ((2 * x) / 2) x := h.div_const 2
      convert h2 using 1
      ring
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun u : ℝ => u ^ 2 / 2)
      (f' := fun x : ℝ => x) hderiv (continuous_id.intervalIntegrable _ _)
    rw [hftc]
    ring
  have hU : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × E => FL (p.1 + 1 / 2) p.2)
      (Set.Ioo (-2) 1 ×ˢ (Set.univ : Set E)) := by
    refine hg.contDiffOn.congr (fun p hp => ?_)
    show FL (p.1 + 1 / 2) p.2 = (cutAuxFlow χ FL 1 p).2
    rw [cutAuxFlow_apply, hτ1 p.1 hp.1]
  have hsub : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × E => (p.1 - 1 / 2, p.2)) :=
    (contDiff_fst.sub contDiff_const).prodMk contDiff_snd
  have hmaps : MapsTo (fun p : ℝ × E => (p.1 - 1 / 2, p.2))
      (Set.Ioo (-3/2) (3/2) ×ˢ (Set.univ : Set E)) (Set.Ioo (-2) 1 ×ˢ (Set.univ : Set E)) := by
    rintro ⟨a, z⟩ ⟨ha, hz⟩
    exact ⟨⟨by linarith [ha.1], by linarith [ha.2]⟩, trivial⟩
  refine (hU.comp hsub.contDiffOn hmaps).congr (fun p hp => ?_)
  show FL p.1 p.2 = FL ((p.1 - 1 / 2) + 1 / 2) p.2
  rw [show (p.1 - 1 / 2) + 1 / 2 = p.1 from by ring]



end

/-- **Joint smoothness of the flow.**  Whitney (1944), §"self-intersections": the flow of a smooth
vector field with bounded value and bounded derivative is `C^∞` in `(time, initial condition)`
jointly. -/
theorem contDiff_flow_joint_of_bounds {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E] (X : E → E)
    (hX : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) X) (M K : ℝ)
    (hM : ∀ z, ‖X z‖ ≤ M) (hK : ∀ z, ‖fderiv ℝ X z‖ ≤ K) (FL : ℝ → E → E)
    (h0 : ∀ p, FL 0 p = p)
    (hsem : ∀ s t p, FL (s + t) p = FL s (FL t p))
    (hcurve : ∀ p, IsIntegralCurve (fun s => FL s p) (fun _ z => X z)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × E => FL p.1 p.2) := by
  obtain ⟨χ, L, hχsm, hχid, hχbd, hχlip⟩ := smoothCutoff
  have hslice : ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, |s| ≤ δ → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (FL s) :=
    Work.ODE.contDiff_flow_timeSlice X hX M K hM hK FL
      (fun t y => ⟨fun s => FL s y, h0 y, hcurve y, rfl⟩)
  have hloc := contDiffOn_joint_small_of_cutoffLevel (χ := χ) (L := L) hX M K hM hK FL h0 hsem hcurve
    hχsm hχid hχbd hχlip
  refine jointFlowAssembly FL h0 hsem hslice (hloc.mono ?_)
  rintro ⟨a, z⟩ ⟨ha, hz⟩
  exact ⟨⟨by linarith [ha.1], by linarith [ha.2]⟩, trivial⟩

/-- **Existence and joint smoothness of the level flow.**  Whitney (1944): the flow of the
smooth compactly supported level field `levelField E G χ` is a one-parameter group of self-maps
of `ℝ^N`, every orbit is an integral curve of the field, and the map `(t, p) ↦ FL t p` is `C^∞`. -/
theorem exists_flow_jointSmooth_levelField {N : ℕ}
    (E : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (G : EuclideanSpace ℝ (Fin N) → ℝ) (χ : EuclideanSpace ℝ (Fin N) → ℝ)
    (hE : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) E) (hG : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G)
    (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) (hcχ : HasCompactSupport χ)
    (hsupp : tsupport χ ⊆ {z | auxField E G z ≠ 0}) :
    ∃ FL : ℝ → EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N),
      (∀ p, FL 0 p = p) ∧ (∀ s t p, FL (s + t) p = FL s (FL t p)) ∧
      (∀ p, IsIntegralCurve (fun s => FL s p) (fun _ z => levelField E G χ z)) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × EuclideanSpace ℝ (Fin N) => FL p.1 p.2) := by
  -- The level field is `C^∞` with compact support ...
  obtain ⟨hlf, hcs⟩ := contDiff_levelField E G χ hE hG hχ hcχ hsupp
  -- ... so it has a global flow with the group law and its integral curves ...
  obtain ⟨FL, δ, _hδpos, h0, hsem, hcurve, _hslice⟩ :=
    Work.Whitney.CutPush.flow_of_compactSupport (levelField E G χ) hlf hcs
  refine ⟨FL, h0, hsem, hcurve, ?_⟩
  -- ... and, being smooth with compact support, it and its derivative are bounded, so the joint
  -- smoothness theorem above applies.
  obtain ⟨M, _hM0, hM⟩ := Work.ODE.exists_norm_le_of_hasCompactSupport hlf.continuous hcs
  have hfdc : Continuous (fderiv ℝ (levelField E G χ)) := hlf.continuous_fderiv (by norm_num)
  have hfcs : HasCompactSupport (fderiv ℝ (levelField E G χ)) := hcs.fderiv (𝕜 := ℝ)
  obtain ⟨K, _hK0, hK⟩ := Work.ODE.exists_norm_le_of_hasCompactSupport hfdc hfcs
  exact contDiff_flow_joint_of_bounds (levelField E G χ) hlf M K hM hK FL h0 hsem hcurve

end Work.Drive.N2
