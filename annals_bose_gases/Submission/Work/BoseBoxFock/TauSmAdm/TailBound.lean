import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Submission.Work.BoseBoxFock.Defs
import Submission.Work.BoseBoxFock.TauSmAdm.Homogeneous
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseBoxFock/TauSmAdm/TailBound.lean`

The **tail bound** for `tauProf`: if `f₀ p = tauProf ‖p‖`, then the sixth iterated derivative of
`f₀` decays like `(1 + ‖p‖)^{-5}` on the tail `3 ≤ ‖p‖`.

Ingredients:

* `iteratedFDeriv_sq_eq_zero` — `D⁶ (fun p => ‖p‖^2) = 0` (the function is homogeneous of
  degree `2`, hence its sixth derivative is homogeneous of degree `-4`, and it is continuous, so
  it vanishes);
* `norm_sphere_bound` — `D⁶ ‖·‖` is bounded on the unit sphere (compactness);
* `norm_decay` — `D⁶ ‖·‖` decays like `‖p‖^{-5}` along rays (homogeneity, from
  `Work.BoseBoxFock.TauSmAdm.iteratedFDeriv_smul_of_homogeneous`);
* `iteratedFDeriv_tauProf_tail` — on the tail, `D⁶ (tauProf ‖·‖) = D⁶ (‖·‖²) - 3 • D⁶ ‖·‖`
  (the pointwise identity `tauProf r = r^2 - 3r + c₀` for `r ≥ 2`, transported through
  `Filter.EventuallyEq.iteratedFDeriv`);
* `exists_tail_bound` — the combination.
-/

open Filter MeasureTheory

set_option maxHeartbeats 1000000

namespace Work.BoseBoxFock.TauSmAdm

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- `iteratedFDeriv ℝ 6 (fun p : ℝ³ => ‖p‖^2)` vanishes identically: the function is homogeneous
of degree `2`, so its sixth derivative is homogeneous of degree `-4`, and it is continuous. -/
theorem iteratedFDeriv_sq_eq_zero (x : E3) :
    iteratedFDeriv ℝ 6 (fun p : E3 => ‖p‖ ^ 2) x = 0 := by
  have hcont : Continuous (fun y : E3 => iteratedFDeriv ℝ 6 (fun p : E3 => ‖p‖ ^ 2) y) :=
    (contDiff_norm_sq (𝕜 := ℝ) (n := (↑(6:ℕ) : WithTop ℕ∞))).continuous_iteratedFDeriv (le_refl _)
  have hhom : ∀ t : ℝ, 0 < t → t ^ 6 •
        iteratedFDeriv ℝ 6 (fun p : E3 => ‖p‖ ^ 2) (t • x)
      = t ^ 2 • iteratedFDeriv ℝ 6 (fun p : E3 => ‖p‖ ^ 2) x := by
    intro t ht
    refine Work.BoseBoxFock.TauSmAdm.iteratedFDeriv_smul_of_homogeneous
      (H := fun p : E3 => ‖p‖ ^ 2) (k := 2) (n := 6) ht isOpen_univ
      (Set.mem_univ _) (Set.mem_univ _) ?_ ?_
    · intro c hc y
      rw [norm_smul, Real.norm_of_nonneg hc.le, mul_pow]
    · exact (contDiff_norm_sq (𝕜 := ℝ) (n := (↑(6:ℕ) : WithTop ℕ∞))).contDiffOn
  have hnorm : ∀ t : ℝ, 0 < t → t ^ 4 *
        ‖iteratedFDeriv ℝ 6 (fun p : E3 => ‖p‖ ^ 2) (t • x)‖
      = ‖iteratedFDeriv ℝ 6 (fun p : E3 => ‖p‖ ^ 2) x‖ := by
    intro t ht
    have h := congrArg (fun A => ‖A‖) (hhom t ht)
    simp only [norm_smul, Real.norm_eq_abs, abs_of_pos ht, abs_pow] at h
    have h' : t ^ 2 * (t ^ 4 * ‖iteratedFDeriv ℝ 6 (fun p : E3 => ‖p‖ ^ 2) (t • x)‖)
        = t ^ 2 * ‖iteratedFDeriv ℝ 6 (fun p : E3 => ‖p‖ ^ 2) x‖ := by
      rw [show t ^ 2 * (t ^ 4 * ‖iteratedFDeriv ℝ 6 (fun p : E3 => ‖p‖ ^ 2) (t • x)‖)
          = t ^ 6 * ‖iteratedFDeriv ℝ 6 (fun p : E3 => ‖p‖ ^ 2) (t • x)‖ from by ring, h]
    exact mul_left_cancel₀ (pow_ne_zero 2 ht.ne') h'
  have hconst' : (fun t : ℝ => t ^ 4 *
        ‖iteratedFDeriv ℝ 6 (fun p : E3 => ‖p‖ ^ 2) (t • x)‖)
      =ᶠ[nhdsWithin (0:ℝ) (Set.Ioi 0)]
      (fun _ => ‖iteratedFDeriv ℝ 6 (fun p : E3 => ‖p‖ ^ 2) x‖) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact hnorm t ht
  have hlim : Tendsto
      (fun t : ℝ => t ^ 4 * ‖iteratedFDeriv ℝ 6 (fun p : E3 => ‖p‖ ^ 2) (t • x)‖)
      (nhdsWithin (0:ℝ) (Set.Ioi 0))
      (nhds (‖iteratedFDeriv ℝ 6 (fun p : E3 => ‖p‖ ^ 2) x‖)) :=
    tendsto_const_nhds.congr' hconst'.symm
  have hlim2 : Tendsto
      (fun t : ℝ => t ^ 4 * ‖iteratedFDeriv ℝ 6 (fun p : E3 => ‖p‖ ^ 2) (t • x)‖)
      (nhdsWithin (0:ℝ) (Set.Ioi 0))
      (nhds (0 ^ 4 * ‖iteratedFDeriv ℝ 6 (fun p : E3 => ‖p‖ ^ 2) (0 : E3)‖)) := by
    have ht : Tendsto (fun t : ℝ => t) (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds (0:ℝ)) :=
      tendsto_nhdsWithin_of_tendsto_nhds (continuous_id.tendsto 0)
    have h1 : Tendsto (fun t : ℝ => t ^ 4) (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds ((0:ℝ) ^ 4)) :=
      ht.pow 4
    have h2 : Tendsto (fun t : ℝ => iteratedFDeriv ℝ 6 (fun p : E3 => ‖p‖ ^ 2) (t • x))
        (nhdsWithin (0:ℝ) (Set.Ioi 0))
        (nhds (iteratedFDeriv ℝ 6 (fun p : E3 => ‖p‖ ^ 2) ((0:ℝ) • x))) :=
      hcont.continuousAt.tendsto.comp (ht.smul tendsto_const_nhds)
    simpa using h1.mul h2.norm
  have huniq := tendsto_nhds_unique hlim hlim2
  have h0 : ‖iteratedFDeriv ℝ 6 (fun p : E3 => ‖p‖ ^ 2) x‖ = 0 := by
    simpa using huniq
  exact norm_eq_zero.mp h0

/-- Bound on the unit sphere for the sixth derivative of the norm. -/
theorem norm_sphere_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : E3, ‖p‖ = 1 →
      ‖iteratedFDeriv ℝ 6 (fun q : E3 => ‖q‖) p‖ ≤ C := by
  have hco : ContDiffOn ℝ (↑(6:ℕ) : WithTop ℕ∞) (fun q : E3 => ‖q‖) {p : E3 | p ≠ 0} :=
    fun y hy => (contDiffAt_norm ℝ hy).contDiffWithinAt
  have hUW : UniqueDiffOn ℝ {p : E3 | p ≠ 0} := isOpen_ne.uniqueDiffOn
  have hcontW : ContinuousOn (fun p => iteratedFDerivWithin ℝ 6 (fun q : E3 => ‖q‖) {p : E3 | p ≠ 0} p)
      {p : E3 | p ≠ 0} := hco.continuousOn_iteratedFDerivWithin (le_refl _) hUW
  have hcont0 : ContinuousOn (fun p => iteratedFDeriv ℝ 6 (fun q : E3 => ‖q‖) p) {p : E3 | p ≠ 0} := by
    refine ContinuousOn.congr
      (f := fun p => iteratedFDerivWithin ℝ 6 (fun q : E3 => ‖q‖) {p : E3 | p ≠ 0} p) hcontW ?_
    intro p hp
    exact ((iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := fun q : E3 => ‖q‖) 6 isOpen_ne) hp).symm
  have hcont : ContinuousOn (fun p => iteratedFDeriv ℝ 6 (fun q : E3 => ‖q‖) p)
      (Metric.sphere (0 : E3) 1) :=
    hcont0.mono (fun p hp => by
      have hp' : ‖p‖ = 1 := by simpa [dist_eq_norm] using Metric.mem_sphere.mp hp
      exact norm_ne_zero_iff.mp (by rw [hp']; norm_num))
  obtain ⟨C, hC⟩ := IsCompact.exists_bound_of_continuousOn (isCompact_sphere (0:E3) 1) hcont
  exact ⟨max C 0, le_max_right _ _, fun p hp =>
    le_trans (hC p (Metric.mem_sphere.mpr (by rw [dist_eq_norm, sub_zero]; simpa using hp)))
      (le_max_left _ _)⟩

/-- The sixth derivative of the norm decays like `‖p‖^{-5}` along rays. -/
theorem norm_decay (CN : ℝ)
    (hCN : ∀ p : E3, ‖p‖ = 1 → ‖iteratedFDeriv ℝ 6 (fun q : E3 => ‖q‖) p‖ ≤ CN)
    (p : E3) (hp0 : p ≠ 0) :
    ‖iteratedFDeriv ℝ 6 (fun q : E3 => ‖q‖) p‖ ≤ CN / ‖p‖ ^ 5 := by
  have htpos : 0 < ‖p‖ := norm_pos_iff.mpr hp0
  have hx1 : ‖(‖p‖)⁻¹ • p‖ = 1 := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg p)), inv_mul_cancel₀ htpos.ne']
  have htx : ‖p‖ • ((‖p‖)⁻¹ • p) = p := by
    rw [smul_smul, mul_inv_cancel₀ htpos.ne', one_smul]
  have hhom : ‖p‖ ^ 6 • iteratedFDeriv ℝ 6 (fun q : E3 => ‖q‖) p
      = ‖p‖ ^ 1 • iteratedFDeriv ℝ 6 (fun q : E3 => ‖q‖) ((‖p‖)⁻¹ • p) := by
    have hmain := Work.BoseBoxFock.TauSmAdm.iteratedFDeriv_smul_of_homogeneous
      (H := fun q : E3 => ‖q‖) (k := 1) (n := 6) htpos (s := {q : E3 | q ≠ 0}) isOpen_ne
      (x := (‖p‖)⁻¹ • p) (by simpa [hx1]) (by simpa [htx] using hp0)
      (fun c hc y => by rw [norm_smul, Real.norm_of_nonneg hc.le, pow_one])
      (fun y hy => (contDiffAt_norm ℝ hy).contDiffWithinAt)
    simpa [htx] using hmain
  have hnorm := congrArg (fun A => ‖A‖) hhom
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos htpos, abs_pow, pow_one] at hnorm
  have hxle : ‖iteratedFDeriv ℝ 6 (fun q : E3 => ‖q‖) ((‖p‖)⁻¹ • p)‖ ≤ CN := hCN _ hx1
  have h1 : ‖p‖ * (‖iteratedFDeriv ℝ 6 (fun q : E3 => ‖q‖) p‖ * ‖p‖ ^ 5) ≤ ‖p‖ * CN := by
    rw [show ‖p‖ * (‖iteratedFDeriv ℝ 6 (fun q : E3 => ‖q‖) p‖ * ‖p‖ ^ 5)
        = ‖p‖ ^ 6 * ‖iteratedFDeriv ℝ 6 (fun q : E3 => ‖q‖) p‖ from by ring, hnorm]
    exact mul_le_mul_of_nonneg_left hxle htpos.le
  exact (le_div_iff₀ (pow_pos htpos 5)).mpr (le_of_mul_le_mul_left h1 htpos)

/-- On the tail, `tauProf ‖p‖ = ‖p‖² - 3‖p‖ + c₀`, so the sixth derivative of `tauProf ‖·‖`
is `D⁶(‖·‖²) - 3 • D⁶(‖·‖)` there. -/
theorem iteratedFDeriv_tauProf_tail {p : E3} (hp : 2 < ‖p‖) :
    iteratedFDeriv ℝ 6 (fun q : E3 => Work.BoseBoxFock.tauProf ‖q‖) p
      = iteratedFDeriv ℝ 6 (fun q : E3 => ‖q‖ ^ 2) p
        - (3:ℝ) • iteratedFDeriv ℝ 6 (fun q : E3 => ‖q‖) p := by
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ℝ, ∀ r : ℝ, 2 ≤ r →
      Work.BoseBoxFock.tauProf r = r ^ 2 - 3 * r + c₀ :=
    ⟨9/4 + ∫ t, t ^ 2 * Work.BoseBoxFock.tauKer t, fun r hr => by
      have h := Work.BoseBoxFock.tauPhi_quad r hr
      have h2 : Work.BoseBoxFock.tauProf r = Work.BoseBoxFock.tauPhi r := rfl
      rw [h2, h]; ring⟩
  have hp0 : p ≠ 0 := by intro h; rw [h] at hp; norm_num at hp
  have hN : ContDiffAt ℝ (↑(6:ℕ) : WithTop ℕ∞) (fun q : E3 => ‖q‖) p := contDiffAt_norm ℝ hp0
  have hS : ContDiffAt ℝ (↑(6:ℕ) : WithTop ℕ∞) (fun q : E3 => ‖q‖ ^ 2) p :=
    (contDiff_norm_sq (𝕜 := ℝ)).contDiffAt
  have hc : ContDiffAt ℝ (↑(6:ℕ) : WithTop ℕ∞) (fun _ : E3 => c₀) p := contDiffAt_const
  have hSq : ContDiffAt ℝ (↑(6:ℕ) : WithTop ℕ∞)
      ((fun q : E3 => ‖q‖ ^ 2) + fun _ : E3 => c₀) p := hS.add hc
  have h3N : ContDiffAt ℝ (↑(6:ℕ) : WithTop ℕ∞) ((3:ℝ) • fun q : E3 => ‖q‖) p :=
    hN.const_smul (3:ℝ)
  have hagree : (fun q : E3 => Work.BoseBoxFock.tauProf ‖q‖) =ᶠ[nhds p]
      (((fun q : E3 => ‖q‖ ^ 2) + fun _ : E3 => c₀) - (3:ℝ) • fun q : E3 => ‖q‖) := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hp] with q hq
    have h := hc₀ ‖q‖ (le_of_lt hq)
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [h]; ring
  have e1 : iteratedFDeriv ℝ 6 (fun q : E3 => Work.BoseBoxFock.tauProf ‖q‖) p
      = iteratedFDeriv ℝ 6 (((fun q : E3 => ‖q‖ ^ 2) + fun _ : E3 => c₀)
          - (3:ℝ) • fun q : E3 => ‖q‖) p :=
    (hagree.iteratedFDeriv ℝ 6).eq_of_nhds
  have e3 : iteratedFDeriv ℝ 6 (((fun q : E3 => ‖q‖ ^ 2) + fun _ : E3 => c₀)
        - (3:ℝ) • fun q : E3 => ‖q‖) p
      = iteratedFDeriv ℝ 6 ((fun q : E3 => ‖q‖ ^ 2) + fun _ : E3 => c₀) p
        - iteratedFDeriv ℝ 6 ((3:ℝ) • fun q : E3 => ‖q‖) p :=
    iteratedFDeriv_sub_apply hSq h3N
  have e4 : iteratedFDeriv ℝ 6 ((fun q : E3 => ‖q‖ ^ 2) + fun _ : E3 => c₀) p
      = iteratedFDeriv ℝ 6 (fun q : E3 => ‖q‖ ^ 2) p
        + iteratedFDeriv ℝ 6 (fun _ : E3 => c₀) p :=
    iteratedFDeriv_add_apply hS hc
  have e5 : iteratedFDeriv ℝ 6 ((3:ℝ) • fun q : E3 => ‖q‖) p
      = (3:ℝ) • iteratedFDeriv ℝ 6 (fun q : E3 => ‖q‖) p :=
    iteratedFDeriv_const_smul_apply (a := (3:ℝ)) hN
  have e6 : iteratedFDeriv ℝ 6 (fun _ : E3 => c₀) p = 0 := by
    have h6 : iteratedFDeriv ℝ 6 (fun _ : E3 => c₀) = 0 := by
      simpa using (iteratedFDeriv_succ_const (𝕜 := ℝ) (E := E3) (F := ℝ) 5 c₀ :
        iteratedFDeriv ℝ (5+1) (fun _ : E3 => c₀) = 0)
    exact congrFun h6 p
  have hfin : iteratedFDeriv ℝ 6 ((fun q : E3 => ‖q‖ ^ 2) + fun _ : E3 => c₀) p
        - iteratedFDeriv ℝ 6 ((3:ℝ) • fun q : E3 => ‖q‖) p
      = iteratedFDeriv ℝ 6 (fun q : E3 => ‖q‖ ^ 2) p
        - (3:ℝ) • iteratedFDeriv ℝ 6 (fun q : E3 => ‖q‖) p := by
    rw [e4, e5, e6, add_zero]
  exact e1.trans (e3.trans hfin)

/-- **The tail bound**: the sixth derivative of `tauProf ‖·‖` decays like `(1 + ‖p‖)^{-5}`. -/
theorem exists_tail_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : E3, 3 ≤ ‖p‖ →
      ‖iteratedFDeriv ℝ 6 (fun q : E3 => Work.BoseBoxFock.tauProf ‖q‖) p‖
        ≤ C * (1 + ‖p‖) ^ (-(5:ℤ)) := by
  obtain ⟨CN, hCN0, hCN⟩ := norm_sphere_bound
  refine ⟨96 * CN, by positivity, ?_⟩
  intro p hp
  have hp1 : 1 ≤ ‖p‖ := by linarith
  have hp0 : p ≠ 0 := by intro h; rw [h] at hp; norm_num at hp
  have htail := iteratedFDeriv_tauProf_tail (p := p) (by linarith)
  rw [htail, iteratedFDeriv_sq_eq_zero p, zero_sub, norm_neg, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by norm_num : (0:ℝ) < 3)]
  have hdec := norm_decay CN hCN p hp0
  simp only [zpow_neg, zpow_natCast]
  have hpos : (0:ℝ) < ‖p‖ ^ 5 := by positivity
  have hpos2 : (0:ℝ) < (1 + ‖p‖) ^ 5 := by positivity
  have hkey : (1 + ‖p‖) ^ 5 ≤ 32 * ‖p‖ ^ 5 := by
    have h2 : 1 + ‖p‖ ≤ 2 * ‖p‖ := by linarith
    calc (1 + ‖p‖) ^ 5 ≤ (2 * ‖p‖) ^ 5 := by gcongr
      _ = 32 * ‖p‖ ^ 5 := by ring
  have h2 : (32 * ‖p‖ ^ 5)⁻¹ ≤ ((1 + ‖p‖) ^ 5)⁻¹ :=
    (inv_le_inv₀ (by positivity : (0:ℝ) < 32 * ‖p‖ ^ 5) hpos2).mpr hkey
  have h3 : 96 * CN * (32 * ‖p‖ ^ 5)⁻¹ ≤ 96 * CN * ((1 + ‖p‖) ^ 5)⁻¹ :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  have h4 : 96 * CN * (32 * ‖p‖ ^ 5)⁻¹ = 3 * (CN * (‖p‖ ^ 5)⁻¹) := by
    rw [mul_inv]; ring
  rw [h4] at h3
  calc 3 * ‖iteratedFDeriv ℝ 6 (fun q : E3 => ‖q‖) p‖
      ≤ 3 * (CN / ‖p‖ ^ 5) := by linarith
    _ = 3 * (CN * (‖p‖ ^ 5)⁻¹) := by rw [div_eq_mul_inv]
    _ ≤ 96 * CN * ((1 + ‖p‖) ^ 5)⁻¹ := h3

end Work.BoseBoxFock.TauSmAdm
