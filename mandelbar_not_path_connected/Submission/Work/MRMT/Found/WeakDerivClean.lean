import Mathlib
import Submission.Work.MRMT.Basic
import Submission.Work.MRMT.Found.Defs
import Submission.Work.MRMT.Found.dzSq_integral_le_area
import Submission.Work.MRMT.Found.courantLebesgue_uniform
import Submission.Work.MRMT.Found.uniform_dz_bound
import Submission.Work.MRMT.Beltrami.integral_mul_dz_eq_neg
import Submission.Work.MRMT.QC.integral_mul_dzbar_eq_neg
import Submission.Work.MRMT.Found.PLWD.Defs
import Submission.Work.MRMT.Found.PLWD.denseRange_testLp
import Submission.Work.MRMT.Found.PLWD.exists_weak_dz_deriv_of_bound_memLp
import Submission.Work.MRMT.Found.PLWD.inner_testLp_eq_integral_star_mul
import Submission.Work.MRMT.Found.principalData_local_weak_derivative

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open MeasureTheory Filter Topology Complex Function
open scoped Distributions Topology ENNReal InnerProductSpace

namespace Work.MRMT.Found

variable {μ : ℂ → ℂ}

/-!
# The global weak Wirtinger derivatives of the principal solution

`principalData_weakDeriv_clean2`: for an admissible coefficient `μ` and a `PrincipalData μ`, the
homeomorphism `φ` has *global* weak `∂`- and `∂̄`-derivatives: there is `D ∈ L²_loc(ℂ)` with
`IsDzDeriv φ D` and `IsDbarDeriv φ (μ · D)`.

The proof glues the local weak derivatives of `principalData_local_weak_derivative` (one on each
ball `B(0, N+1)`, `N ∈ ℕ`) into a single function.  Two local derivatives agree almost everywhere
on the smaller of the two balls because there they have the same pairings against every test
function supported in that ball, and the test functions are dense in `L²`.
-/

/-! ## The local weak derivative, with a.e. strong measurability of the solution -/

/-- On every ball `B(0,R)` with `R > 0` the principal solution `φ` has a weak `∂`-derivative `D`
which is *square integrable* (hence a.e. strongly measurable), and `∂̄φ = μ D` weakly. -/
private theorem local_weak_deriv_memLp (hμ : Admissible μ) (d : PrincipalData μ)
    {R : ℝ} (hR : 0 < R) :
    ∃ D : ℂ → ℂ, MemLp D 2 ((volume : Measure ℂ).restrict (Metric.ball 0 R)) ∧
      (∀ ψ : ℂ → ℂ, ContDiff ℝ 1 ψ → HasCompactSupport ψ → tsupport ψ ⊆ Metric.ball 0 R →
        ∫ z, D z * ψ z = -∫ z, (d.φ : ℂ → ℂ) z * dz ψ z) ∧
      (∀ ψ : ℂ → ℂ, ContDiff ℝ 1 ψ → HasCompactSupport ψ → tsupport ψ ⊆ Metric.ball 0 R →
        ∫ z, μ z * D z * ψ z = -∫ z, (d.φ : ℂ → ℂ) z * dzbar ψ z) := by
  obtain ⟨C₀, hC₀⟩ := uniform_dz_bound hμ d R hR
  have hφloc : LocallyIntegrable (d.φ : ℂ → ℂ) (volume : Measure ℂ) :=
    d.φ.continuous.locallyIntegrable
  have hbd : ∀ ψ : testSpace R, ‖∫ z, (d.φ : ℂ → ℂ) z * dz (ψ : ℂ → ℂ) z‖ ≤
      Real.sqrt (max C₀ 0) * ‖testLp R ψ‖ := by
    intro ψ
    have hconv := plwd_tendsto_integral_Fn_mul d (plwd_continuous_dz ψ.2.1)
      (plwd_hasCompactSupport_dz ψ) (plwd_support_dz_subset_closedBall ψ)
    refine le_of_tendsto hconv.norm (Filter.Eventually.of_forall fun n => ?_)
    rw [Beltrami.integral_mul_dz_eq_neg (d.contDiff_Fn n) ψ.2.1 ψ.2.2.1, norm_neg]
    rw [plwd_integral_ball_eq (plwd_support_mul_subset ψ.2.2.2
      (fun z => dz ((d.Fn n : ℂ ≃ₜ ℂ) : ℂ → ℂ) z))]
    refine (plwd_norm_integral_mul_le (plwd_memLp_dz d R hR n)
      (memLp_of_mem_testSpace ψ.2)).trans ?_
    have hnormψ : Real.sqrt (∫ z, ‖(ψ : ℂ → ℂ) z‖ ^ 2
        ∂((volume : Measure ℂ).restrict (Metric.ball 0 R))) = ‖testLp R ψ‖ := by
      rw [← plwd_norm_testLp R ψ, Real.sqrt_sq (norm_nonneg _)]
    rw [hnormψ]
    exact mul_le_mul_of_nonneg_right
      (Real.sqrt_le_sqrt (le_trans (hC₀ n) (le_max_left _ _))) (norm_nonneg _)
  obtain ⟨D, hDm, hD⟩ := PLWD.exists_weak_dz_deriv_of_bound_memLp (φ := (d.φ : ℂ → ℂ))
    hφloc (Real.sqrt_nonneg _) (PLWD.denseRange_testLp R) hbd
  exact ⟨D, hDm, (fun ψ h1 h2 h3 => hD ⟨ψ, h1, h2, h3⟩),
    fun ψ h1 h2 h3 => plwd_second_identity hμ d hR hDm hD ψ h1 h2 h3⟩

/-- The weak `∂`-derivative on the ball of radius `N+1`, chosen once and for all. -/
private noncomputable def ballD (hμ : Admissible μ) (d : PrincipalData μ) (N : ℕ) : ℂ → ℂ :=
  Classical.choose (local_weak_deriv_memLp (μ := μ) hμ d (by positivity : (0 : ℝ) < (N : ℝ) + 1))

private theorem ballD_memLp (hμ : Admissible μ) (d : PrincipalData μ) (N : ℕ) :
    MemLp (ballD hμ d N) 2 ((volume : Measure ℂ).restrict (Metric.ball 0 ((N : ℝ) + 1))) :=
  (Classical.choose_spec (local_weak_deriv_memLp (μ := μ) hμ d
    (by positivity : (0 : ℝ) < (N : ℝ) + 1))).1

private theorem ballD_dz (hμ : Admissible μ) (d : PrincipalData μ) (N : ℕ) :
    ∀ ψ : ℂ → ℂ, ContDiff ℝ 1 ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Metric.ball 0 ((N : ℝ) + 1) →
      ∫ z, ballD hμ d N z * ψ z = -∫ z, (d.φ : ℂ → ℂ) z * dz ψ z :=
  (Classical.choose_spec (local_weak_deriv_memLp (μ := μ) hμ d
    (by positivity : (0 : ℝ) < (N : ℝ) + 1))).2.1

private theorem ballD_dzbar (hμ : Admissible μ) (d : PrincipalData μ) (N : ℕ) :
    ∀ ψ : ℂ → ℂ, ContDiff ℝ 1 ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Metric.ball 0 ((N : ℝ) + 1) →
      ∫ z, μ z * ballD hμ d N z * ψ z = -∫ z, (d.φ : ℂ → ℂ) z * dzbar ψ z :=
  (Classical.choose_spec (local_weak_deriv_memLp (μ := μ) hμ d
    (by positivity : (0 : ℝ) < (N : ℝ) + 1))).2.2

/-! ## Compatibility of the local weak derivatives -/

/-- The conjugate of a `C¹` compactly supported function is again `C¹` with compact support. -/
private theorem contDiff_conj_comp {ψ : ℂ → ℂ} (hψ : ContDiff ℝ 1 ψ) :
    ContDiff ℝ 1 (fun z => star (ψ z)) := by
  have hconj : ContDiff ℝ 1 (fun z : ℂ => star z) :=
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).contDiff
  exact hconj.comp hψ

private theorem hasCompactSupport_conj_comp {ψ : ℂ → ℂ} (hψ : HasCompactSupport ψ) :
    HasCompactSupport (fun z => star (ψ z)) :=
  hψ.comp_left (g := fun w : ℂ => star w) (by simp)

private theorem tsupport_conj_comp_subset (ψ : ℂ → ℂ) :
    tsupport (fun z => star (ψ z)) ⊆ tsupport ψ := by
  refine closure_mono ?_
  intro z hz
  rw [Function.mem_support] at hz ⊢
  intro h0
  exact hz (by simp [h0])

/-- `∂ψ` is supported in the *open* ball whenever `ψ` is. -/
private theorem support_dz_subset_ball {R : ℝ} {ψ : ℂ → ℂ}
    (hψ : tsupport ψ ⊆ Metric.ball 0 R) : Function.support (dz ψ) ⊆ Metric.ball 0 R := by
  intro x hx
  by_contra hxK
  exact hx (plwd_dz_eq_zero_of_notMem_tsupport (fun h => hxK (hψ h)))

/-- **The two local weak derivatives agree a.e. on the smaller ball.** -/
private theorem ballD_ae_eq (hμ : Admissible μ) (d : PrincipalData μ) {i N : ℕ} (hiN : i ≤ N) :
    ballD hμ d i =ᵐ[volume.restrict (Metric.ball 0 ((i : ℝ) + 1))] ballD hμ d N := by
  have hsub : Metric.ball (0 : ℂ) ((i : ℝ) + 1) ⊆ Metric.ball (0 : ℂ) ((N : ℝ) + 1) :=
    Metric.ball_subset_ball (by exact_mod_cast Nat.succ_le_succ hiN)
  have hνle : (volume : Measure ℂ).restrict (Metric.ball 0 ((i : ℝ) + 1)) ≤
      (volume : Measure ℂ).restrict (Metric.ball 0 ((N : ℝ) + 1)) :=
    Measure.restrict_mono (μ := (volume : Measure ℂ)) (ν := (volume : Measure ℂ)) hsub le_rfl
  set dd : ℂ → ℂ := fun z => ballD hμ d i z - ballD hμ d N z with hdd
  have hdmem : MemLp dd 2 ((volume : Measure ℂ).restrict (Metric.ball 0 ((i : ℝ) + 1))) :=
    (ballD_memLp hμ d i).sub ((ballD_memLp hμ d N).mono_measure hνle)
  -- the pairings of `dd` against the test functions vanish
  have hzero : ∀ ψ : testSpace ((i : ℝ) + 1),
      ∫ z, dd z * (ψ : ℂ → ℂ) z ∂((volume : Measure ℂ).restrict (Metric.ball 0 ((i : ℝ) + 1)))
        = 0 := by
    intro ψ
    have h1 : ∫ z, ballD hμ d i z * (ψ : ℂ → ℂ) z
          ∂((volume : Measure ℂ).restrict (Metric.ball 0 ((i : ℝ) + 1)))
        = -∫ z, (d.φ : ℂ → ℂ) z * dz (ψ : ℂ → ℂ) z
          ∂((volume : Measure ℂ).restrict (Metric.ball 0 ((i : ℝ) + 1))) := by
      rw [← plwd_integral_ball_eq (plwd_support_mul_subset ψ.2.2.2
            (fun z => ballD hμ d i z)),
          ← plwd_integral_ball_eq (fun z hz => by
            have hz0 : dz (ψ : ℂ → ℂ) z = 0 := by
              by_contra h0
              exact hz (support_dz_subset_ball ψ.2.2.2 (Function.mem_support.mpr h0))
            rw [hz0, mul_zero])]
      exact ballD_dz hμ d i _ ψ.2.1 ψ.2.2.1 ψ.2.2.2
    have h2 : ∫ z, ballD hμ d N z * (ψ : ℂ → ℂ) z
          ∂((volume : Measure ℂ).restrict (Metric.ball 0 ((i : ℝ) + 1)))
        = -∫ z, (d.φ : ℂ → ℂ) z * dz (ψ : ℂ → ℂ) z
          ∂((volume : Measure ℂ).restrict (Metric.ball 0 ((i : ℝ) + 1))) := by
      rw [← plwd_integral_ball_eq (plwd_support_mul_subset ψ.2.2.2
            (fun z => ballD hμ d N z)),
          ← plwd_integral_ball_eq (fun z hz => by
            have hz0 : dz (ψ : ℂ → ℂ) z = 0 := by
              by_contra h0
              exact hz (support_dz_subset_ball ψ.2.2.2 (Function.mem_support.mpr h0))
            rw [hz0, mul_zero])]
      exact ballD_dz hμ d N _ ψ.2.1 ψ.2.2.1 (ψ.2.2.2.trans hsub)
    have hsub' : (fun z => dd z * (ψ : ℂ → ℂ) z)
        = fun z => ballD hμ d i z * (ψ : ℂ → ℂ) z - ballD hμ d N z * (ψ : ℂ → ℂ) z := by
      funext z
      simp only [hdd]
      ring
    rw [hsub', integral_sub]
    · rw [h1, h2, sub_self]
    · exact plwd_integrable_mul_of_memLp (ballD_memLp hμ d i) (memLp_of_mem_testSpace ψ.2)
    · exact plwd_integrable_mul_of_memLp ((ballD_memLp hμ d N).mono_measure hνle)
        (memLp_of_mem_testSpace ψ.2)
  -- the conjugate of a test function is a test function, and `ψ ↦ ∫ dd ψ` vanishes on it
  have hconjtest : ∀ ψ : testSpace ((i : ℝ) + 1),
      (fun z => star ((ψ : ℂ → ℂ) z)) ∈ testSpace ((i : ℝ) + 1) := by
    intro ψ
    exact ⟨contDiff_conj_comp ψ.2.1, hasCompactSupport_conj_comp ψ.2.2.1,
      (tsupport_conj_comp_subset _).trans ψ.2.2.2⟩
  have hzero' : ∀ ψ : testSpace ((i : ℝ) + 1),
      ∫ z, dd z * star ((ψ : ℂ → ℂ) z)
        ∂((volume : Measure ℂ).restrict (Metric.ball 0 ((i : ℝ) + 1))) = 0 :=
    fun ψ => hzero ⟨_, hconjtest ψ⟩
  -- pairings against the dense set of test functions
  let w : Lp ℂ 2 ((volume : Measure ℂ).restrict (Metric.ball 0 ((i : ℝ) + 1))) :=
    hdmem.toLp dd
  have hpair : ∀ ψ : testSpace ((i : ℝ) + 1), inner ℂ w (testLp ((i : ℝ) + 1) ψ) = 0 := by
    intro ψ
    rw [PLWD.inner_testLp_eq_integral_star_mul w ψ]
    have hcoe : (w : ℂ → ℂ) =ᵐ[volume.restrict (Metric.ball 0 ((i : ℝ) + 1))] dd :=
      MemLp.coeFn_toLp hdmem
    have hstep : (∫ z, star (w z) * (ψ : ℂ → ℂ) z) =
        ∫ z in Metric.ball 0 ((i : ℝ) + 1), star (dd z) * (ψ : ℂ → ℂ) z := by
      rw [plwd_integral_ball_eq (plwd_support_mul_subset ψ.2.2.2 (fun z => star (w z)))]
      refine integral_congr_ae ?_
      filter_upwards [hcoe] with z hz
      simp only [hz]
    rw [hstep]
    have hconj : (∫ z in Metric.ball 0 ((i : ℝ) + 1), star (dd z) * (ψ : ℂ → ℂ) z)
        = star (∫ z in Metric.ball 0 ((i : ℝ) + 1), dd z * star ((ψ : ℂ → ℂ) z)) := by
      have hpt : (fun z => star (dd z) * (ψ : ℂ → ℂ) z)
          = fun z => star (dd z * star ((ψ : ℂ → ℂ) z)) := by
        funext z
        rw [star_mul, star_star]
        ring
      rw [hpt]
      exact integral_conj
    rw [hconj, hzero' ψ]
    simp
  have hw0 : w = 0 := by
    have hclosed : IsClosed {v : Lp ℂ 2 ((volume : Measure ℂ).restrict (Metric.ball 0 ((i : ℝ) + 1))) |
        inner ℂ w v = 0} := isClosed_eq (continuous_const.inner continuous_id) continuous_const
    have hrange : Set.range (testLp ((i : ℝ) + 1)) ⊆
        {v : Lp ℂ 2 ((volume : Measure ℂ).restrict (Metric.ball 0 ((i : ℝ) + 1))) |
          inner ℂ w v = 0} := by
      rintro v ⟨ψ, rfl⟩
      exact hpair ψ
    have hwmem : w ∈ closure (Set.range (testLp ((i : ℝ) + 1))) := by
      rw [DenseRange.closure_range (PLWD.denseRange_testLp ((i : ℝ) + 1))]
      exact Set.mem_univ w
    exact inner_self_eq_zero.mp (closure_minimal hrange hclosed hwmem)
  have hddzero : dd =ᵐ[((volume : Measure ℂ).restrict (Metric.ball 0 ((i : ℝ) + 1)))] 0 := by
    have h0 : (w : ℂ → ℂ) =ᵐ[((volume : Measure ℂ).restrict (Metric.ball 0 ((i : ℝ) + 1)))] 0 :=
      Lp.eq_zero_iff_ae_eq_zero.mp hw0
    exact (MemLp.coeFn_toLp hdmem).symm.trans h0
  filter_upwards [hddzero] with z hz
  have := sub_eq_zero.mp hz
  simpa [hdd] using this


/-! ## The global weak derivative -/

/-- Monotonicity of the restricted volume measure along inclusions of subsets of `ℂ`. -/
private theorem restrict_mono_ball {s t : Set ℂ} (h : s ⊆ t) :
    (volume : Measure ℂ).restrict s ≤ (volume : Measure ℂ).restrict t :=
  Measure.restrict_mono (μ := (volume : Measure ℂ)) (ν := (volume : Measure ℂ)) h le_rfl

/-- `∂ψ` has compact support when `ψ` has. -/
private theorem hasCompactSupport_dz_of_hasCompactSupport {ψ : ℂ → ℂ}
    (hψ : HasCompactSupport ψ) : HasCompactSupport (dz ψ) := by
  have h4 : HasCompactSupport
      (fun z : ℂ => fderiv ℝ ψ z (1 : ℂ) - Complex.I * fderiv ℝ ψ z Complex.I) := by
    have h1 : HasCompactSupport (fun z : ℂ => fderiv ℝ ψ z (1 : ℂ)) :=
      hψ.fderiv_apply ℝ (1 : ℂ)
    have h2 : HasCompactSupport (fun z : ℂ => fderiv ℝ ψ z Complex.I) :=
      hψ.fderiv_apply ℝ Complex.I
    have h3 : HasCompactSupport (fun z : ℂ => Complex.I * fderiv ℝ ψ z Complex.I) :=
      h2.comp_left (g := fun w : ℂ => Complex.I * w) (by simp)
    exact h1.sub h3
  have key : dz ψ = fun z : ℂ =>
      (fderiv ℝ ψ z (1 : ℂ) - Complex.I * fderiv ℝ ψ z Complex.I) / 2 := rfl
  rw [key]
  exact (h4.comp_left (g := fun w : ℂ => w / 2) (by simp)).comp_left (g := id) (by simp)

/-- `∂̄ψ` has compact support when `ψ` has. -/
private theorem hasCompactSupport_dzbar_of_hasCompactSupport {ψ : ℂ → ℂ}
    (hψ : HasCompactSupport ψ) : HasCompactSupport (dzbar ψ) := by
  have h4 : HasCompactSupport
      (fun z : ℂ => fderiv ℝ ψ z (1 : ℂ) + Complex.I * fderiv ℝ ψ z Complex.I) := by
    have h1 : HasCompactSupport (fun z : ℂ => fderiv ℝ ψ z (1 : ℂ)) :=
      hψ.fderiv_apply ℝ (1 : ℂ)
    have h2 : HasCompactSupport (fun z : ℂ => fderiv ℝ ψ z Complex.I) :=
      hψ.fderiv_apply ℝ Complex.I
    have h3 : HasCompactSupport (fun z : ℂ => Complex.I * fderiv ℝ ψ z Complex.I) :=
      h2.comp_left (g := fun w : ℂ => Complex.I * w) (by simp)
    exact h1.add h3
  have key : dzbar ψ = fun z : ℂ =>
      (fderiv ℝ ψ z (1 : ℂ) + Complex.I * fderiv ℝ ψ z Complex.I) / 2 := rfl
  rw [key]
  exact (h4.comp_left (g := fun w : ℂ => w / 2) (by simp)).comp_left (g := id) (by simp)

/-- The global weak `∂`-derivative: on the annulus `N ≤ ‖z‖ < N+1` it is the local weak
derivative of the ball of radius `N+1`. -/
private noncomputable def Dglob (hμ : Admissible μ) (d : PrincipalData μ) : ℂ → ℂ :=
  fun z => ballD hμ d ⌊‖z‖⌋₊ z

/-- On the ball `B(0,N+1)` the global derivative agrees a.e. with the local one. -/
private theorem Dglob_ae_eq_ballD (hμ : Admissible μ) (d : PrincipalData μ) (N : ℕ) :
    Dglob hμ d =ᵐ[volume.restrict (Metric.ball 0 ((N : ℝ) + 1))] ballD hμ d N := by
  have hpiece : ∀ i : ℕ, ∀ᵐ z ∂(volume.restrict (Metric.ball 0 ((N : ℝ) + 1))),
      z ∈ {z : ℂ | ⌊‖z‖⌋₊ = i} → Dglob hμ d z = ballD hμ d N z := by
    intro i
    by_cases hiN : i ≤ N
    · have hcompat : ∀ᵐ z ∂(volume : Measure ℂ),
          z ∈ Metric.ball 0 ((i : ℝ) + 1) → ballD hμ d i z = ballD hμ d N z :=
        (ae_restrict_iff' Metric.isOpen_ball.measurableSet).mp (ballD_ae_eq hμ d hiN)
      filter_upwards [ae_restrict_of_ae hcompat] with z hz hzi
      have hzi' : ⌊‖z‖⌋₊ = i := hzi
      have hzball : z ∈ Metric.ball 0 ((i : ℝ) + 1) := by
        rw [Metric.mem_ball, dist_zero_right]
        have hlt : ⌊‖z‖⌋₊ < i + 1 := by omega
        have := (Nat.floor_lt (norm_nonneg z)).mp hlt
        simpa using this
      have hD : Dglob hμ d z = ballD hμ d i z := by
        simp only [Dglob, hzi']
      rw [hD]
      exact hz hzball
    · filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with z hzmem hzi
      exfalso
      have hlt : ‖z‖ < ((N : ℝ) + 1) := by
        simpa [Metric.mem_ball, dist_zero_right] using hzmem
      have hfloor : ⌊‖z‖⌋₊ ≤ N := by
        have := (Nat.floor_lt (norm_nonneg z)).mpr (by exact_mod_cast hlt)
        omega
      rw [hzi] at hfloor
      exact hiN hfloor
  have hall : ∀ᵐ z ∂(volume.restrict (Metric.ball 0 ((N : ℝ) + 1))), ∀ i : ℕ,
      z ∈ {z : ℂ | ⌊‖z‖⌋₊ = i} → Dglob hμ d z = ballD hμ d N z := ae_all_iff.mpr hpiece
  filter_upwards [hall] with z hz
  exact hz ⌊‖z‖⌋₊ rfl

/-- The global derivative is a.e. equal to the local one on any compact subset of the ball. -/
private theorem Dglob_ae_eq_ballD_of_subset (hμ : Admissible μ) (d : PrincipalData μ)
    {K : Set ℂ} (hK : IsCompact K) (N : ℕ)
    (hKsub : K ⊆ Metric.ball 0 ((N : ℝ) + 1)) :
    Dglob hμ d =ᵐ[volume.restrict K] ballD hμ d N := by
  have h1 : ∀ᵐ z ∂(volume : Measure ℂ),
      z ∈ Metric.ball 0 ((N : ℝ) + 1) → Dglob hμ d z = ballD hμ d N z :=
    (ae_restrict_iff' Metric.isOpen_ball.measurableSet).mp (Dglob_ae_eq_ballD hμ d N)
  filter_upwards [ae_restrict_of_ae h1, ae_restrict_mem hK.measurableSet] with z hz hzK
  exact hz (hKsub hzK)

/-- The global derivative is locally square integrable. -/
private theorem memL2Loc_Dglob (hμ : Admissible μ) (d : PrincipalData μ) :
    MemL2Loc (Dglob hμ d) := by
  intro K hK
  obtain ⟨M, hM⟩ := hK.isBounded.exists_norm_le
  obtain ⟨N, hN⟩ := exists_nat_gt M
  have hKsub : K ⊆ Metric.ball 0 ((N : ℝ) + 1) := by
    intro z hz
    rw [Metric.mem_ball, dist_zero_right]
    have h1 : ‖z‖ ≤ M := hM z hz
    have h2 : M < (N : ℝ) := hN
    linarith
  have hloc : IntegrableOn (fun z => ‖ballD hμ d N z‖ ^ 2)
      (Metric.ball 0 ((N : ℝ) + 1)) (volume : Measure ℂ) :=
    (memLp_two_iff_integrable_sq_norm (ballD_memLp hμ d N).aestronglyMeasurable).mp
      (ballD_memLp hμ d N)
  have hlocK : IntegrableOn (fun z => ‖ballD hμ d N z‖ ^ 2) K (volume : Measure ℂ) :=
    hloc.mono_set hKsub
  rw [Set.inter_univ]
  refine hlocK.congr ?_
  filter_upwards [Dglob_ae_eq_ballD_of_subset hμ d hK N hKsub] with z hz
  rw [hz]

/-- The global derivative is locally integrable. -/
private theorem locallyIntegrable_Dglob (hμ : Admissible μ) (d : PrincipalData μ) :
    LocallyIntegrable (Dglob hμ d) (volume : Measure ℂ) := by
  refine MeasureTheory.locallyIntegrable_iff.mpr fun K hK => ?_
  obtain ⟨M, hM⟩ := hK.isBounded.exists_norm_le
  obtain ⟨N, hN⟩ := exists_nat_gt M
  have hKsub : K ⊆ Metric.ball 0 ((N : ℝ) + 1) := by
    intro z hz
    rw [Metric.mem_ball, dist_zero_right]
    have h1 : ‖z‖ ≤ M := hM z hz
    have h2 : M < (N : ℝ) := hN
    linarith
  haveI : IsFiniteMeasure (volume.restrict K) := by
    rw [isFiniteMeasure_restrict]
    exact hK.measure_lt_top.ne
  have haes : AEStronglyMeasurable (Dglob hμ d) (volume.restrict K) :=
    ((ballD_memLp hμ d N).aestronglyMeasurable.mono_measure (restrict_mono_ball hKsub)).congr
      (Dglob_ae_eq_ballD_of_subset hμ d hK N hKsub).symm
  have hD2 : Integrable (fun z => ‖Dglob hμ d z‖ ^ 2) (volume.restrict K) := by
    simpa [Set.inter_univ] using (memL2Loc_Dglob hμ d K hK).integrable
  have hg : Integrable (fun z => (1 / 2 : ℝ) * (1 + ‖Dglob hμ d z‖ ^ 2)) (volume.restrict K) :=
    ((integrable_const (1 : ℝ)).add hD2).const_mul _
  have hInt : Integrable (Dglob hμ d) (volume.restrict K) := by
    refine Integrable.mono' hg haes ?_
    filter_upwards with z
    nlinarith [sq_nonneg (‖Dglob hμ d z‖ - 1)]
  exact hInt

/-- The local derivative against a test function is integrable over the whole plane. -/
private theorem integrable_ballD_mul {μ : ℂ → ℂ} (hμ : Admissible μ) (d : PrincipalData μ)
    (N : ℕ) {ψ : ℂ → ℂ} (hcd : ContDiff ℝ 1 ψ) (hcs : HasCompactSupport ψ)
    (hsub : tsupport ψ ⊆ Metric.ball 0 ((N : ℝ) + 1)) :
    Integrable (fun z => ballD hμ d N z * ψ z) (volume : Measure ℂ) := by
  have hrestrict : Integrable (fun z => ballD hμ d N z * ψ z)
      ((volume : Measure ℂ).restrict (Metric.ball 0 ((N : ℝ) + 1))) :=
    plwd_integrable_mul_of_memLp (ballD_memLp hμ d N)
      (memLp_of_mem_testSpace ⟨hcd, hcs, hsub⟩)
  have hzero : ∀ z ∉ Metric.ball 0 ((N : ℝ) + 1), ballD hμ d N z * ψ z = 0 :=
    plwd_support_mul_subset hsub (fun z => ballD hμ d N z)
  refine (MeasureTheory.IntegrableOn.integrable_indicator hrestrict
    Metric.isOpen_ball.measurableSet).congr (Filter.Eventually.of_forall fun z => ?_)
  by_cases hz : z ∈ Metric.ball 0 ((N : ℝ) + 1)
  · simp only [Set.indicator_of_mem hz]
  · simp only [Set.indicator_of_notMem hz, hzero z hz]

/-- Multiplication by the (a.e. bounded) admissible coefficient preserves integrability. -/
private theorem integrable_mu_mul {μ : ℂ → ℂ} (hμ : Admissible μ) {f : ℂ → ℂ}
    (hf : Integrable f (volume : Measure ℂ)) :
    Integrable (fun z => μ z * f z) (volume : Measure ℂ) := by
  obtain ⟨k, hk, hkb⟩ := hμ.bound
  refine Integrable.mono' hf.norm (hμ.meas.mul hf.aestronglyMeasurable) ?_
  filter_upwards [hkb] with z hz
  rw [norm_mul]
  calc ‖μ z‖ * ‖f z‖ ≤ 1 * ‖f z‖ :=
        mul_le_mul_of_nonneg_right (le_trans hz hk.le) (norm_nonneg _)
    _ = ‖f z‖ := one_mul _

/-- The global derivative against a test function is integrable over the whole plane. -/
private theorem integrable_Dglob_mul (hμ : Admissible μ) (d : PrincipalData μ)
    (ψ : 𝓓(⊤, ℂ)) :
    Integrable (fun z => Dglob hμ d z * (ψ : ℂ → ℂ) z) (volume : Measure ℂ) := by
  obtain ⟨M, hM⟩ := (TestFunction.hasCompactSupport ψ).isCompact.isBounded.exists_norm_le
  obtain ⟨N, hN⟩ := exists_nat_gt M
  have hsub : tsupport (ψ : ℂ → ℂ) ⊆ Metric.ball 0 ((N : ℝ) + 1) := by
    intro z hz
    rw [Metric.mem_ball, dist_zero_right]
    have h1 : ‖z‖ ≤ M := hM z hz
    have h2 : M < (N : ℝ) := hN
    linarith
  have hcd : ContDiff ℝ 1 (ψ : ℂ → ℂ) := (TestFunction.contDiff ψ).of_le (by norm_num)
  refine (integrable_ballD_mul hμ d N hcd (TestFunction.hasCompactSupport ψ) hsub).congr ?_
  filter_upwards [(ae_restrict_iff' Metric.isOpen_ball.measurableSet).mp
    (Dglob_ae_eq_ballD hμ d N)] with z hz
  by_cases hzb : z ∈ Metric.ball 0 ((N : ℝ) + 1)
  · rw [hz hzb]
  · have hz0 : (ψ : ℂ → ℂ) z = 0 := by
      by_contra h
      exact hzb (hsub (subset_tsupport _ (Function.mem_support.mpr h)))
    rw [hz0, mul_zero, mul_zero]

/-- The `∂`-identity for the global weak derivative. -/
private theorem Dglob_dz_eq (hμ : Admissible μ) (d : PrincipalData μ) (ψ : 𝓓(⊤, ℂ)) :
    ∫ z, (d.φ : ℂ → ℂ) z * dz (ψ : ℂ → ℂ) z = -∫ z, Dglob hμ d z * (ψ : ℂ → ℂ) z := by
  obtain ⟨M, hM⟩ := (TestFunction.hasCompactSupport ψ).isCompact.isBounded.exists_norm_le
  obtain ⟨N, hN⟩ := exists_nat_gt M
  have hsub : tsupport (ψ : ℂ → ℂ) ⊆ Metric.ball 0 ((N : ℝ) + 1) := by
    intro z hz
    rw [Metric.mem_ball, dist_zero_right]
    have h1 : ‖z‖ ≤ M := hM z hz
    have h2 : M < (N : ℝ) := hN
    linarith
  have hcd : ContDiff ℝ 1 (ψ : ℂ → ℂ) := (TestFunction.contDiff ψ).of_le (by norm_num)
  have hlocal : ∫ z, ballD hμ d N z * (ψ : ℂ → ℂ) z
      = -∫ z, (d.φ : ℂ → ℂ) z * dz (ψ : ℂ → ℂ) z :=
    ballD_dz hμ d N _ hcd (TestFunction.hasCompactSupport ψ) hsub
  have hglob : ∫ z, Dglob hμ d z * (ψ : ℂ → ℂ) z
      = ∫ z, ballD hμ d N z * (ψ : ℂ → ℂ) z := by
    refine integral_congr_ae ?_
    filter_upwards [(ae_restrict_iff' Metric.isOpen_ball.measurableSet).mp
      (Dglob_ae_eq_ballD hμ d N)] with z hz
    by_cases hzb : z ∈ Metric.ball 0 ((N : ℝ) + 1)
    · rw [hz hzb]
    · have hz0 : (ψ : ℂ → ℂ) z = 0 := by
        by_contra h
        exact hzb (hsub (subset_tsupport _ (Function.mem_support.mpr h)))
      rw [hz0, mul_zero, mul_zero]
  rw [hglob, hlocal]
  ring

/-- The `∂̄`-identity for the global weak derivative. -/
private theorem Dglob_dzbar_eq (hμ : Admissible μ) (d : PrincipalData μ) (ψ : 𝓓(⊤, ℂ)) :
    ∫ z, (d.φ : ℂ → ℂ) z * dzbar (ψ : ℂ → ℂ) z
      = -∫ z, μ z * Dglob hμ d z * (ψ : ℂ → ℂ) z := by
  obtain ⟨M, hM⟩ := (TestFunction.hasCompactSupport ψ).isCompact.isBounded.exists_norm_le
  obtain ⟨N, hN⟩ := exists_nat_gt M
  have hsub : tsupport (ψ : ℂ → ℂ) ⊆ Metric.ball 0 ((N : ℝ) + 1) := by
    intro z hz
    rw [Metric.mem_ball, dist_zero_right]
    have h1 : ‖z‖ ≤ M := hM z hz
    have h2 : M < (N : ℝ) := hN
    linarith
  have hcd : ContDiff ℝ 1 (ψ : ℂ → ℂ) := (TestFunction.contDiff ψ).of_le (by norm_num)
  have hlocal : ∫ z, μ z * ballD hμ d N z * (ψ : ℂ → ℂ) z
      = -∫ z, (d.φ : ℂ → ℂ) z * dzbar (ψ : ℂ → ℂ) z :=
    ballD_dzbar hμ d N _ hcd (TestFunction.hasCompactSupport ψ) hsub
  have hglob : ∫ z, μ z * Dglob hμ d z * (ψ : ℂ → ℂ) z
      = ∫ z, μ z * ballD hμ d N z * (ψ : ℂ → ℂ) z := by
    refine integral_congr_ae ?_
    filter_upwards [(ae_restrict_iff' Metric.isOpen_ball.measurableSet).mp
      (Dglob_ae_eq_ballD hμ d N)] with z hz
    by_cases hzb : z ∈ Metric.ball 0 ((N : ℝ) + 1)
    · rw [hz hzb]
    · have hz0 : (ψ : ℂ → ℂ) z = 0 := by
        by_contra h
        exact hzb (hsub (subset_tsupport _ (Function.mem_support.mpr h)))
      simp only [hz0, mul_zero]
  rw [hglob, hlocal]
  ring

/-- The product `μ · Dglob` is locally integrable. -/
private theorem locallyIntegrable_mu_Dglob (hμ : Admissible μ) (d : PrincipalData μ) :
    LocallyIntegrable (fun z => μ z * Dglob hμ d z) (volume : Measure ℂ) := by
  refine MeasureTheory.locallyIntegrable_iff.mpr fun K hK => ?_
  obtain ⟨M, hM⟩ := hK.isBounded.exists_norm_le
  obtain ⟨N, hN⟩ := exists_nat_gt M
  have hKsub : K ⊆ Metric.ball 0 ((N : ℝ) + 1) := by
    intro z hz
    rw [Metric.mem_ball, dist_zero_right]
    have h1 : ‖z‖ ≤ M := hM z hz
    have h2 : M < (N : ℝ) := hN
    linarith
  haveI : IsFiniteMeasure (volume.restrict K) := by
    rw [isFiniteMeasure_restrict]
    exact hK.measure_lt_top.ne
  have hDaes : AEStronglyMeasurable (Dglob hμ d) (volume.restrict K) :=
    ((ballD_memLp hμ d N).aestronglyMeasurable.mono_measure (restrict_mono_ball hKsub)).congr
      (Dglob_ae_eq_ballD_of_subset hμ d hK N hKsub).symm
  have haes : AEStronglyMeasurable (fun z => μ z * Dglob hμ d z) (volume.restrict K) :=
    (hμ.meas.mono_measure Measure.restrict_le_self).mul hDaes
  have hD2 : Integrable (fun z => ‖Dglob hμ d z‖ ^ 2) (volume.restrict K) := by
    simpa [Set.inter_univ] using (memL2Loc_Dglob hμ d K hK).integrable
  have hg : Integrable (fun z => (1 / 2 : ℝ) * (1 + ‖Dglob hμ d z‖ ^ 2)) (volume.restrict K) :=
    ((integrable_const (1 : ℝ)).add hD2).const_mul _
  have hnormInt : Integrable (fun z => ‖Dglob hμ d z‖) (volume.restrict K) := by
    refine Integrable.mono' hg hDaes.norm ?_
    filter_upwards with z
    have ht : 0 ≤ ‖Dglob hμ d z‖ := norm_nonneg _
    calc ‖‖Dglob hμ d z‖‖ = ‖Dglob hμ d z‖ := Real.norm_of_nonneg ht
      _ ≤ 1 / 2 * (1 + ‖Dglob hμ d z‖ ^ 2) := by
          nlinarith [sq_nonneg (‖Dglob hμ d z‖ - 1)]
  obtain ⟨k, hk, hkb⟩ := hμ.bound
  refine Integrable.mono' hnormInt haes ?_
  filter_upwards [ae_restrict_of_ae hkb] with z hz
  rw [norm_mul]
  calc ‖μ z‖ * ‖Dglob hμ d z‖ ≤ 1 * ‖Dglob hμ d z‖ :=
        mul_le_mul_of_nonneg_right (le_trans hz hk.le) (norm_nonneg _)
    _ = ‖Dglob hμ d z‖ := one_mul _

/-! ## The main theorem -/

theorem principalData_weakDeriv_clean2 {μ : ℂ → ℂ} (hμ : Admissible μ) (d : PrincipalData μ) :
    ∃ D : ℂ → ℂ, Work.MRMT.MemL2Loc D ∧
      Work.MRMT.IsDzDeriv (d.φ : ℂ → ℂ) D ∧
      Work.MRMT.IsDbarDeriv (d.φ : ℂ → ℂ) (fun z => μ z * D z) := by
  have hφloc : LocallyIntegrable (d.φ : ℂ → ℂ) (volume : Measure ℂ) :=
    d.φ.continuous.locallyIntegrable
  have hDloc : LocallyIntegrable (Dglob hμ d) (volume : Measure ℂ) := locallyIntegrable_Dglob hμ d
  have hμDloc : LocallyIntegrable (fun z => μ z * Dglob hμ d z) (volume : Measure ℂ) :=
    locallyIntegrable_mu_Dglob hμ d
  refine ⟨Dglob hμ d, memL2Loc_Dglob hμ d, ?_, ?_⟩
  · unfold Work.MRMT.IsDzDeriv
    refine ⟨hφloc, hDloc, ?_⟩
    intro ψ
    have hcd : ContDiff ℝ 1 (ψ : ℂ → ℂ) := (TestFunction.contDiff ψ).of_le (by norm_num)
    have hcs : HasCompactSupport (ψ : ℂ → ℂ) := TestFunction.hasCompactSupport ψ
    refine ⟨?_, integrable_Dglob_mul hμ d ψ, Dglob_dz_eq hμ d ψ⟩
    exact ((d.φ.continuous.mul (plwd_continuous_dz hcd)).integrable_of_hasCompactSupport
      ((hasCompactSupport_dz_of_hasCompactSupport hcs).mul_left))
  · unfold Work.MRMT.IsDbarDeriv
    refine ⟨hφloc, hμDloc, ?_⟩
    · intro ψ
      have hcd : ContDiff ℝ 1 (ψ : ℂ → ℂ) := (TestFunction.contDiff ψ).of_le (by norm_num)
      have hcs : HasCompactSupport (ψ : ℂ → ℂ) := TestFunction.hasCompactSupport ψ
      have hint1 : Integrable (fun z => Dglob hμ d z * (ψ : ℂ → ℂ) z) (volume : Measure ℂ) :=
        integrable_Dglob_mul hμ d ψ
      refine ⟨?_, ?_, Dglob_dzbar_eq hμ d ψ⟩
      · exact ((d.φ.continuous.mul (plwd_continuous_dzbar hcd)).integrable_of_hasCompactSupport
          ((hasCompactSupport_dzbar_of_hasCompactSupport hcs).mul_left))
      · have := integrable_mu_mul hμ hint1
        refine this.congr ?_
        filter_upwards with z
        ring

end Work.MRMT.Found
