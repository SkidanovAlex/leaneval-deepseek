import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Have
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.RCLike.Inner
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Submission.Commons.Analysis.Fourier.integral_mul_eq_integral_fourier_mul
import Submission.Work.BoseFixB1.BoxPairIntGenC2.fourier_memLp_one_of_contDiff_two
import Submission.Work.BoseKinLoc.Momentum.kinFT_l1l2_plancherel
import Submission.Work.BoseKinLoc.Momentum.memLp_kinFT
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1B

open MeasureTheory
open scoped FourierTransform RealInnerProductSpace Real

/-
The analytic core of `Work.BoseFixB1B.wMR_memLp_one_contDiff`: the "diagonal Fourier
transform" of a SMOOTH kernel times a merely CONTINUOUS compactly supported window `χ` is
integrable in the momentum variable `q`.  (`hAc` is exactly `A ⊆ Submission.BoseGases.acube ℓ`,
written out to keep the statement self-contained.)

Proof strategy that is known to work (so that this is worth proving as written):
write the z-integral first and expand `F(y, ·)` on the cube `C := {s | ∀ j, -ℓ/2 ≤ s j ∧ s j ≤ ℓ/2}`
by the multivariate product-form fundamental formula of calculus: for smooth `g` and `z ∈ C`,
with `z₀ := fun _ => -ℓ/2`,
  `g z = ∑_{S ⊆ Fin 3} (1/ℓ^{3-|S|}) ∫_{s ∈ C} (∂_S g)(π_S(s)) · ∏_{j ∈ S} 1_{s_j ≤ z_j} ds`,
where `π_S(s)` has coordinate `j = s_j` for `j ∈ S` and `= z₀_j` otherwise.  (`|S|` is the
cardinality of the finite set `S`; the factor `ℓ^{-(3-|S|)}` compensates for integrating over
all three coordinates of the cube; the identity is obtained by iterating the one-dimensional
fundamental formula in the three coordinates.)  Inserting this into the `(y,z)`-integral gives,
after Fubini,
  `∑_S (1/ℓ^{3-|S|}) ∫_{s ∈ C} A_S(s,q) · B_S(s,q) ds`
with `A_S(s,q) = ∫_{y ∈ A} χ y · e^{i⟪q,y⟫} · (∂_S F)(y, π_S(s)) dy` and
`B_S(s,q) = ∫_{z ∈ A} χ z · e^{-i⟪q,z⟫} · ∏_{j ∈ S} 1_{s_j ≤ z_j} dz`.
Both are (up to harmless scalings of `q`) Fourier transforms of `L²` functions, whose `L²`
norms are bounded by `(2π)^{3/2}·‖χ‖₂·sup|∂_S F|` and `(2π)^{3/2}·‖χ‖₂` respectively, uniformly
in `s`; Cauchy–Schwarz in `q` and then Tonelli (the `(s,q)`-integral of `|A_S B_S|` is finite)
give the result.

**Implementation note.**  The proof below follows the same plan in a slightly different
(Lean-friendlier) organisation: the `z`-integrand is split as a product of two `L¹ ∩ L²`
functions and paired by Plancherel (`Commons.Analysis.Fourier.integral_mul_eq_integral_fourier_mul`),
which produces the expansion directly, without ever writing down the fundamental theorem of
calculus on the cube.  The decay of the expansion kernel `ξ ↦ 𝓕(F(y,·)·η)(ξ)` needed for the
final Cauchy–Schwarz is obtained from Plancherel applied to the Hessian trace, uniformly in `y`.
-/

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ### Geometry: the centred cube -/

/-- The centred cube of side `ℓ` (the statement's `hAc`). -/
def DCube (ℓ : ℝ) : Set E3 := {s : E3 | ∀ j : Fin 3, -(ℓ / 2) ≤ s j ∧ s j ≤ ℓ / 2}

/-- The circumradius of the centred cube of side `ℓ`. -/
noncomputable def cubeR (ℓ : ℝ) : ℝ := ℓ * Real.sqrt 3 / 2

lemma mem_DCube_iff {ℓ : ℝ} {s : E3} :
    s ∈ DCube ℓ ↔ ∀ j : Fin 3, -(ℓ / 2) ≤ s j ∧ s j ≤ ℓ / 2 := Iff.rfl

lemma norm_sq_eq_sum (s : E3) : ‖s‖ ^ 2 = ∑ j : Fin 3, (s j) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Real.norm_eq_abs, sq_abs]

/-- Any element of the centred cube has norm at most its circumradius. -/
lemma norm_le_cubeR {ℓ : ℝ} (hℓ : 0 ≤ ℓ) {s : E3} (hs : s ∈ DCube ℓ) :
    ‖s‖ ≤ cubeR ℓ := by
  have h2 : ∀ j : Fin 3, (s j) ^ 2 ≤ (ℓ / 2) ^ 2 := by
    intro j
    have hj := hs j
    exact sq_le_sq' (by linarith [hj.1]) (by linarith [hj.2])
  have h3 : ‖s‖ ^ 2 ≤ 3 * (ℓ / 2) ^ 2 := by
    rw [norm_sq_eq_sum]
    calc ∑ j : Fin 3, (s j) ^ 2 ≤ ∑ _j : Fin 3, (ℓ / 2) ^ 2 :=
          Finset.sum_le_sum fun j _ => h2 j
      _ = 3 * (ℓ / 2) ^ 2 := by simp [Finset.sum_const, Finset.card_univ]
  have hs2 : ‖s‖ ^ 2 ≤ (cubeR ℓ) ^ 2 := by
    have hsq : (cubeR ℓ) ^ 2 = 3 * (ℓ / 2) ^ 2 := by
      rw [cubeR, div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]; ring
    rw [hsq]; exact h3
  have hcR : 0 ≤ cubeR ℓ := by unfold cubeR; positivity
  nlinarith [norm_nonneg s, hcR, hs2]

/-- The outer radius of the cutoff: twice the circumradius (plus one) of the cube. -/
noncomputable def cutoffR (ℓ : ℝ) : ℝ := |ℓ| * Real.sqrt 3 / 2 + 1

/-- The cutoff bump: a fixed smooth compactly supported function, equal to `1` on the
centred cube of side `ℓ`. -/
noncomputable def etaBump (ℓ : ℝ) : ContDiffBump (0 : E3) :=
  ⟨cutoffR ℓ, cutoffR ℓ + 1, by unfold cutoffR; positivity, by unfold cutoffR; linarith⟩

/-- A fixed smooth compactly supported cutoff `η` on `ℝ³`, equal to `1` on a neighbourhood
of the centred cube of side `ℓ` (and with values in `[0,1]`). -/
noncomputable def etaCut (ℓ : ℝ) : E3 → ℝ := etaBump ℓ

lemma contDiff_etaCut (ℓ : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (etaCut ℓ) :=
  ContDiffBump.contDiff (etaBump ℓ) (n := (⊤ : ℕ∞))

lemma hasCompactSupport_etaCut (ℓ : ℝ) : HasCompactSupport (etaCut ℓ) :=
  ContDiffBump.hasCompactSupport (etaBump ℓ)

lemma etaCut_eq_one {ℓ : ℝ} (hℓ : 0 ≤ ℓ) {s : E3} (hs : s ∈ DCube ℓ) : etaCut ℓ s = 1 := by
  have hmem : s ∈ Metric.closedBall (0 : E3) (cutoffR ℓ) := by
    rw [Metric.mem_closedBall, dist_zero_right]
    refine (norm_le_cubeR hℓ hs).trans ?_
    unfold cubeR cutoffR
    have h2 : (0 : ℝ) ≤ Real.sqrt 3 / 2 := by positivity
    have h3 : ℓ * Real.sqrt 3 / 2 ≤ |ℓ| * Real.sqrt 3 / 2 := by
      calc ℓ * Real.sqrt 3 / 2 = ℓ * (Real.sqrt 3 / 2) := by ring
        _ ≤ |ℓ| * (Real.sqrt 3 / 2) := mul_le_mul_of_nonneg_right (le_abs_self ℓ) h2
        _ = |ℓ| * Real.sqrt 3 / 2 := by ring
    linarith
  exact ContDiffBump.one_of_mem_closedBall (etaBump ℓ) hmem

lemma etaCut_nonneg (ℓ : ℝ) (s : E3) : 0 ≤ etaCut ℓ s :=
  ContDiffBump.nonneg (etaBump ℓ)

lemma etaCut_le_one (ℓ : ℝ) (s : E3) : etaCut ℓ s ≤ 1 :=
  ContDiffBump.le_one (etaBump ℓ)

lemma tsupport_etaCut_subset (ℓ : ℝ) :
    tsupport (etaCut ℓ) ⊆ Metric.closedBall (0 : E3) (cutoffR ℓ + 1) := by
  have hs : Function.support (etaCut ℓ) = Metric.ball (0 : E3) (cutoffR ℓ + 1) :=
    ContDiffBump.support_eq (etaBump ℓ)
  rw [tsupport, hs]
  exact closure_minimal Metric.ball_subset_closedBall Metric.isClosed_closedBall

lemma etaCut_eq_zero_of_not_mem {ℓ : ℝ} {z : E3}
    (hz : z ∉ Metric.closedBall (0 : E3) (cutoffR ℓ + 1)) : etaCut ℓ z = 0 := by
  by_contra h
  exact hz (tsupport_etaCut_subset ℓ (subset_tsupport _ h))

/-! ### The smooth kernel `F(y,z)·η(z)` and its slices -/

/-- The smooth kernel `(y,z) ↦ F y z · η z` on `ℝ³ × ℝ³`. -/
noncomputable def JFun (F : E3 × E3 → ℝ) (η : E3 → ℝ) : E3 × E3 → ℂ :=
  fun p => ((F p : ℝ) : ℂ) * (η p.2 : ℂ)

/-- The `y`-slice `z ↦ F y z · η z`. -/
noncomputable def slice (F : E3 × E3 → ℝ) (η : E3 → ℝ) (y : E3) : E3 → ℂ :=
  (JFun F η) ∘ fun z : E3 => (y, z)

lemma slice_apply {F : E3 × E3 → ℝ} {η : E3 → ℝ} {y z : E3} :
    slice F η y z = ((F (y, z) : ℝ) : ℂ) * (η z : ℂ) := rfl

lemma contDiff_JFun {F : E3 × E3 → ℝ} {η : E3 → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) : ContDiff ℝ (⊤ : ℕ∞) (JFun F η) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) fun p : E3 × E3 => ((F p : ℝ) : ℂ) :=
    Complex.ofRealCLM.contDiff.comp hF
  have h2 : ContDiff ℝ (⊤ : ℕ∞) fun p : E3 × E3 => ((η p.2 : ℝ) : ℂ) :=
    Complex.ofRealCLM.contDiff.comp (hη.comp contDiff_snd)
  exact h1.mul h2

lemma hasCompactSupport_slice {F : E3 × E3 → ℝ} {η : E3 → ℝ} (hηs : HasCompactSupport η)
    (y : E3) : HasCompactSupport (slice F η y) :=
  hηs.mono (by
    intro z hz
    rw [Function.mem_support] at hz ⊢
    exact fun h => hz (by simp [slice_apply, h]))

lemma tsupport_slice_subset {F : E3 × E3 → ℝ} {η : E3 → ℝ} (y : E3) :
    tsupport (slice F η y) ⊆ tsupport η :=
  closure_mono (by
    intro z hz
    rw [Function.mem_support] at hz ⊢
    exact fun h => hz (by simp [slice_apply, h]))

lemma fderiv_prodMk_right (y x : E3) :
    fderiv ℝ (fun z : E3 => (y, z)) x = ContinuousLinearMap.inr ℝ E3 E3 :=
  (hasFDerivAt_prodMk_right (𝕜 := ℝ) y x).fderiv

lemma iteratedFDeriv_prodMk_right_two (y x : E3) :
    iteratedFDeriv ℝ 2 (fun z : E3 => (y, z)) x = 0 := by
  refine ContinuousMultilinearMap.ext (fun m => ?_)
  rw [iteratedFDeriv_two_apply, zero_apply]
  have h' : fderiv ℝ (fun z : E3 => (y, z))
      = Function.const E3 (ContinuousLinearMap.inr ℝ E3 E3) := by
    funext z
    exact fderiv_prodMk_right y z
  rw [h', fderiv_const]
  rfl

/-- **Derivative bounds for a slice.**  If the joint kernel `JFun F η` has its `i`-th iterated
derivatives (for `i ≤ 2`) bounded by `M` at `(y,z)`, then the slice `slice F η y` has its `n`-th
iterated derivative at `z` bounded by `n! · M` (for `n ≤ 2`). -/
lemma norm_iteratedFDeriv_slice_le {F : E3 × E3 → ℝ} {η : E3 → ℝ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hη : ContDiff ℝ (⊤ : ℕ∞) η) {y z : E3} {M : ℝ}
    (hM : ∀ i : ℕ, i ≤ 2 → ‖iteratedFDeriv ℝ i (JFun F η) (y, z)‖ ≤ M)
    {n : ℕ} (hn : n ≤ 2) :
    ‖iteratedFDeriv ℝ n (slice F η y) z‖ ≤ n.factorial * M := by
  have hcd : ContDiff ℝ (⊤ : ℕ∞) (JFun F η) := contDiff_JFun hF hη
  have hinner : ContDiff ℝ (⊤ : ℕ∞) (fun z : E3 => (y, z)) :=
    contDiff_const.prodMk contDiff_id
  have htop : ((n : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
    WithTop.coe_le_coe.mpr le_top
  have h := norm_iteratedFDeriv_comp_le (𝕜 := ℝ) (N := ((⊤ : ℕ∞) : WithTop ℕ∞)) hcd hinner
    htop z (C := M) (D := 1)
    (fun i hi => hM i (le_trans hi hn)) (fun i hi1 hi2 => ?_)
  · simpa [slice] using h
  · have hi : i = 1 ∨ i = 2 := by omega
    rcases hi with rfl | rfl
    · rw [norm_iteratedFDeriv_one, fderiv_prodMk_right, ContinuousLinearMap.norm_inr]
      norm_num
    · rw [iteratedFDeriv_prodMk_right_two]; simp

/-- The joint kernel's first three iterated derivatives are bounded on the compact product of
the cube's circumscribed ball with the cutoff's support ball. -/
lemma exists_joint_bound {F : E3 × E3 → ℝ} {η : E3 → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (ℓ : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ i : ℕ, i ≤ 2 → ∀ p ∈ Metric.closedBall (0 : E3) (cubeR ℓ) ×ˢ
      Metric.closedBall (0 : E3) (cutoffR ℓ + 1),
      ‖iteratedFDeriv ℝ i (JFun F η) p‖ ≤ M := by
  have hcd : ContDiff ℝ (⊤ : ℕ∞) (JFun F η) := contDiff_JFun hF hη
  have hc : IsCompact (Metric.closedBall (0 : E3) (cubeR ℓ) ×ˢ
      Metric.closedBall (0 : E3) (cutoffR ℓ + 1)) :=
    (isCompact_closedBall (0 : E3) (cubeR ℓ)).prod
      (isCompact_closedBall (0 : E3) (cutoffR ℓ + 1))
  have ht : ∀ m : ℕ, ((m : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
    fun m => WithTop.coe_le_coe.mpr le_top
  obtain ⟨C0, hC0⟩ := hc.exists_bound_of_continuousOn
    ((hcd.continuous_iteratedFDeriv (m := 0) (ht 0)).continuousOn)
  obtain ⟨C1, hC1⟩ := hc.exists_bound_of_continuousOn
    ((hcd.continuous_iteratedFDeriv (m := 1) (ht 1)).continuousOn)
  obtain ⟨C2, hC2⟩ := hc.exists_bound_of_continuousOn
    ((hcd.continuous_iteratedFDeriv (m := 2) (ht 2)).continuousOn)
  refine ⟨max 0 (max C0 (max C1 C2)), le_max_left _ _, fun i hi p hp => ?_⟩
  interval_cases i
  · exact (hC0 p hp).trans (le_max_of_le_right (le_max_left _ _))
  · exact (hC1 p hp).trans (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))
  · exact (hC2 p hp).trans (le_max_of_le_right (le_max_of_le_right (le_max_right _ _)))

/-- **Uniform derivative bounds for the slices.** -/
lemma slice_deriv_bound {ℓ : ℝ} (hℓ : 0 ≤ ℓ) {A : Set E3}
    (hAc : ∀ z ∈ A, ∀ j : Fin 3, -(ℓ / 2) ≤ z j ∧ z j ≤ ℓ / 2)
    {F : E3 × E3 → ℝ} {η : E3 → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηsupp : tsupport η ⊆ Metric.closedBall (0 : E3) (cutoffR ℓ + 1)) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ i : ℕ, i ≤ 2 → ∀ p ∈ Metric.closedBall (0 : E3) (cubeR ℓ) ×ˢ
      Metric.closedBall (0 : E3) (cutoffR ℓ + 1), ‖iteratedFDeriv ℝ i (JFun F η) p‖ ≤ M)
    {y : E3} (hy : y ∈ A) {n : ℕ} (hn : n ≤ 2) :
    ∀ z : E3, ‖iteratedFDeriv ℝ n (slice F η y) z‖ ≤ n.factorial * M := by
  intro z
  have hyc : y ∈ Metric.closedBall (0 : E3) (cubeR ℓ) := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact norm_le_cubeR hℓ (mem_DCube_iff.mp (fun j => hAc y hy j))
  rcases Classical.em (z ∈ Metric.closedBall (0 : E3) (cutoffR ℓ + 1)) with hz | hz
  · exact norm_iteratedFDeriv_slice_le hF hη (fun i hi => hM i hi (y, z) ⟨hyc, hz⟩) hn
  · have hzero : iteratedFDeriv ℝ n (slice F η y) z = 0 := by
      have h1 : z ∉ tsupport (slice F η y) := fun hcontra =>
        hz (hηsupp (tsupport_slice_subset (F := F) (η := η) y hcontra))
      have h2 : z ∉ Function.support (iteratedFDeriv ℝ n (slice F η y)) :=
        fun hc => h1 (support_iteratedFDeriv_subset n hc)
      simpa [Function.mem_support] using h2
    rw [hzero, norm_zero]
    exact mul_nonneg (Nat.cast_nonneg _) hM0

/-! ### The weighted Plancherel bound for a single `C²` compactly supported function -/

/-- Continuity of the evaluation of a second-order multilinear map. -/
lemma continuous_hess_eval (m : Fin 2 → E3) :
    Continuous (fun φ : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E3) ℂ => φ m) :=
  AddMonoidHomClass.continuous_of_bound (ContinuousMultilinearMap.applyAddHom m) (∏ i, ‖m i‖)
    (fun φ => by
      have h := ContinuousMultilinearMap.le_opNorm φ m
      rw [show ‖φ‖ * ∏ i, ‖m i‖ = (∏ i, ‖m i‖) * ‖φ‖ from mul_comm _ _] at h
      exact h)

/-- **Weighted `L²` bound for the Fourier transform.**  For `f : ℝ³ → ℂ` of class `C²` with
compact support, whose values and second derivatives are bounded by `M`, the
`(1+‖ξ‖²)²`-weighted `L²` norm of `𝓕 f` is integrable and controlled by the volume of any
measurable set `S` containing the support.

The proof writes `(1+s²)² ≤ 2 + 2s⁴`, uses the identity `𝓕L = -(4π²‖ξ‖²)𝓕f` for the Hessian
trace `L` of `f`, and then Plancherel for `f` and for `L`. -/
lemma weighted_fourier_le {f : E3 → ℂ} (hf : ContDiff ℝ 2 f) (hs : HasCompactSupport f)
    {M : ℝ} (hM0 : ∀ z, ‖f z‖ ≤ M) (hM2 : ∀ z, ‖iteratedFDeriv ℝ 2 f z‖ ≤ M)
    {S : Set E3} (hS : tsupport f ⊆ S) (hSmeas : MeasurableSet S) (hSfin : volume S < ⊤) :
    Integrable (fun ξ : E3 => (1 + ‖ξ‖ ^ 2) ^ 2 * ‖𝓕 f ξ‖ ^ 2) (volume : Measure E3) ∧
    ∫ ξ : E3, (1 + ‖ξ‖ ^ 2) ^ 2 * ‖𝓕 f ξ‖ ^ 2
      ≤ (2 * M ^ 2 + 2 * ((4 * Real.pi ^ 2) ^ 2)⁻¹ * (3 * M) ^ 2) * volume.real S := by
  classical
  set b : OrthonormalBasis (Fin 3) ℝ E3 := EuclideanSpace.basisFun (Fin 3) ℝ with hb
  have hf2 : MemLp f 2 (volume : Measure E3) := hf.continuous.memLp_of_hasCompactSupport hs
  have hfl1 : Integrable f (volume : Measure E3) :=
    hf.continuous.integrable_of_hasCompactSupport hs
  have hint : ∀ n : ℕ, n ≤ 2 → Integrable (iteratedFDeriv ℝ n f) (volume : Measure E3) := by
    intro n hn
    exact (hf.continuous_iteratedFDeriv (m := n) (by exact_mod_cast hn)).integrable_of_hasCompactSupport
      (hs.iteratedFDeriv n)
  set L : E3 → ℂ := fun x => ∑ j : Fin 3, iteratedFDeriv ℝ 2 f x (fun _ : Fin 2 => b j) with hLdef
  have hLcont : Continuous L := by
    rw [hLdef]
    exact continuous_finsetSum _ (fun j _ =>
      (continuous_hess_eval (m := fun _ : Fin 2 => b j)).comp
        (hf.continuous_iteratedFDeriv (m := 2) le_rfl))
  have hLsupp : HasCompactSupport L := by
    rw [hLdef]
    exact (hs.iteratedFDeriv 2).comp_left
      (g := fun φ : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E3) ℂ =>
        ∑ j : Fin 3, φ (fun _ : Fin 2 => b j)) (by simp)
  have hL1 : MemLp L 1 (volume : Measure E3) := hLcont.memLp_of_hasCompactSupport hLsupp
  have hL2 : MemLp L 2 (volume : Measure E3) := hLcont.memLp_of_hasCompactSupport hLsupp
  have hPlanchL : Integrable (fun ξ : E3 => ‖𝓕 L ξ‖ ^ 2) (volume : Measure E3) :=
    Work.BoseFixB1.BoxPairIntGenC2.integrable_norm_fourier_sq' hL1 hL2
  have hPlanchf : Integrable (fun ξ : E3 => ‖𝓕 f ξ‖ ^ 2) (volume : Measure E3) :=
    Work.BoseFixB1.BoxPairIntGenC2.integrable_norm_fourier_sq'
      (memLp_one_iff_integrable.mpr hfl1) hf2
  have hdf : ∀ j : Fin 3,
      Integrable (fun x : E3 => iteratedFDeriv ℝ 2 f x (fun _ : Fin 2 => b j))
        (volume : Measure E3) := by
    intro j
    have hc : Continuous (fun x : E3 => iteratedFDeriv ℝ 2 f x (fun _ : Fin 2 => b j)) :=
      (continuous_hess_eval (m := fun _ : Fin 2 => b j)).comp
        (hf.continuous_iteratedFDeriv (m := 2) le_rfl)
    have hsupp : HasCompactSupport
        (fun x : E3 => iteratedFDeriv ℝ 2 f x (fun _ : Fin 2 => b j)) :=
      (hs.iteratedFDeriv 2).comp_left
        (g := fun φ : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E3) ℂ =>
          φ (fun _ : Fin 2 => b j)) (by simp)
    exact hc.integrable_of_hasCompactSupport hsupp
  have hscal : (-(2 * (Real.pi : ℂ) * Complex.I)) ^ 2 = ((-(4 * Real.pi ^ 2) : ℝ) : ℂ) := by
    rw [show (-(2 * (Real.pi : ℂ) * Complex.I)) = -(((2 * Real.pi : ℝ)) : ℂ) * Complex.I by
      push_cast; ring]
    rw [mul_pow, Complex.I_sq]
    push_cast
    ring
  have hterm : ∀ (ξ : E3) (j : Fin 3),
      𝓕 (fun x => iteratedFDeriv ℝ 2 f x (fun _ : Fin 2 => b j)) ξ
        = ((-(4 * Real.pi ^ 2 * ⟪ξ, b j⟫ ^ 2)) : ℝ) • 𝓕 f ξ := by
    intro ξ j
    rw [← Real.fourier_continuousMultilinearMap_apply (f := iteratedFDeriv ℝ 2 f)
      (m := fun _ : Fin 2 => b j) (v := ξ) (hint 2 le_rfl)]
    rw [Real.fourier_iteratedFDeriv (N := (2 : ℕ∞)) hf (fun n hn => hint n (by exact_mod_cast hn)) (n := 2) le_rfl]
    rw [VectorFourier.fourierPowSMulRight_apply]
    have hprod : (∏ i : Fin 2, (-innerSL ℝ) ξ (b j)) = ⟪ξ, b j⟫ ^ 2 := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      simp only [neg_apply, innerSL_apply_apply, neg_sq]
    rw [hprod, hscal, smul_eq_mul, Complex.real_smul, Complex.real_smul]
    push_cast
    ring
  have hId : ∀ ξ : E3, 𝓕 L ξ = ((-(4 * Real.pi ^ 2 * ‖ξ‖ ^ 2)) : ℝ) • 𝓕 f ξ := by
    intro ξ
    have h1 : 𝓕 L ξ
        = ∑ j : Fin 3, 𝓕 (fun x => iteratedFDeriv ℝ 2 f x (fun _ : Fin 2 => b j)) ξ := by
      rw [hLdef]
      exact Commons.Analysis.Fourier.fourier_finsetSum Finset.univ
        (fun j => fun x : E3 => iteratedFDeriv ℝ 2 f x (fun _ : Fin 2 => b j))
        (fun j _ => hdf j) ξ
    rw [h1, Finset.sum_congr rfl (fun j _ => hterm ξ j), ← Finset.sum_smul]
    congr 1
    calc ∑ j : Fin 3, (-(4 * Real.pi ^ 2 * ⟪ξ, b j⟫ ^ 2))
        = (-(4 * Real.pi ^ 2)) * ∑ j : Fin 3, ⟪ξ, b j⟫ ^ 2 := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun j _ => by ring)
      _ = (-(4 * Real.pi ^ 2)) * ‖ξ‖ ^ 2 := by rw [OrthonormalBasis.sum_sq_inner_left b ξ]
      _ = -(4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) := by ring
  have hpt : ∀ ξ : E3, (1 + ‖ξ‖ ^ 2) ^ 2 * ‖𝓕 f ξ‖ ^ 2
      ≤ 2 * ‖𝓕 f ξ‖ ^ 2 + 2 * ((4 * Real.pi ^ 2) ^ 2)⁻¹ * ‖𝓕 L ξ‖ ^ 2 := by
    intro ξ
    have h1 : ‖𝓕 L ξ‖ = 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 * ‖𝓕 f ξ‖ := by
      rw [hId ξ, norm_smul, Real.norm_eq_abs, abs_neg,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2)]
    rw [h1]
    have h2 : ((4 * Real.pi ^ 2) ^ 2)⁻¹ * (4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 * ‖𝓕 f ξ‖) ^ 2
        = ‖ξ‖ ^ 4 * ‖𝓕 f ξ‖ ^ 2 := by
      field_simp
    rw [show (2 : ℝ) * ((4 * Real.pi ^ 2) ^ 2)⁻¹ * (4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 * ‖𝓕 f ξ‖) ^ 2
        = 2 * (‖ξ‖ ^ 4 * ‖𝓕 f ξ‖ ^ 2) by rw [mul_assoc, h2]]
    nlinarith [sq_nonneg (‖ξ‖ ^ 2 - 1), sq_nonneg (‖𝓕 f ξ‖), norm_nonneg ξ,
      sq_nonneg (‖ξ‖ ^ 2), sq_nonneg (‖ξ‖)]
  have hInt2 : Integrable
      (fun ξ : E3 => 2 * ‖𝓕 f ξ‖ ^ 2 + 2 * ((4 * Real.pi ^ 2) ^ 2)⁻¹ * ‖𝓕 L ξ‖ ^ 2)
      (volume : Measure E3) :=
    (hPlanchf.const_mul 2).add (hPlanchL.const_mul _)
  have hFcont : Continuous (fun ξ : E3 => 𝓕 f ξ) :=
    VectorFourier.fourierIntegral_continuous (𝕜 := ℝ) Real.continuous_fourierChar
      continuous_inner hfl1
  have hmeas1 : AEStronglyMeasurable (fun ξ : E3 => (1 + ‖ξ‖ ^ 2) ^ 2 * ‖𝓕 f ξ‖ ^ 2)
      (volume : Measure E3) :=
    (((continuous_const.add (continuous_norm.pow 2)).pow 2).mul (hFcont.norm.pow 2)).aestronglyMeasurable
  have hInt1 : Integrable (fun ξ : E3 => (1 + ‖ξ‖ ^ 2) ^ 2 * ‖𝓕 f ξ‖ ^ 2)
      (volume : Measure E3) :=
    hInt2.mono' hmeas1
      (Filter.Eventually.of_forall fun ξ => by
        rw [Real.norm_of_nonneg (by positivity)]; exact hpt ξ)
  have hmain : ∫ ξ : E3, (1 + ‖ξ‖ ^ 2) ^ 2 * ‖𝓕 f ξ‖ ^ 2
      ≤ ∫ ξ : E3, (2 * ‖𝓕 f ξ‖ ^ 2 + 2 * ((4 * Real.pi ^ 2) ^ 2)⁻¹ * ‖𝓕 L ξ‖ ^ 2) :=
    integral_mono hInt1 hInt2 hpt
  have hmid : 2 * (∫ z : E3, ‖f z‖ ^ 2)
      + 2 * ((4 * Real.pi ^ 2) ^ 2)⁻¹ * (∫ z : E3, ‖L z‖ ^ 2)
      = ∫ ξ : E3, (2 * ‖𝓕 f ξ‖ ^ 2 + 2 * ((4 * Real.pi ^ 2) ^ 2)⁻¹ * ‖𝓕 L ξ‖ ^ 2) := by
    rw [integral_add (hPlanchf.const_mul 2) (hPlanchL.const_mul _), integral_const_mul,
      integral_const_mul, Commons.Analysis.Fourier.integral_norm_sq_fourier_l1l2 hfl1 hf2,
      Commons.Analysis.Fourier.integral_norm_sq_fourier_l1l2
        (memLp_one_iff_integrable.mp hL1) hL2]
  have hIf : ∫ z : E3, ‖f z‖ ^ 2 ≤ M ^ 2 * volume.real S := by
    have hzero : ∀ z ∉ S, (fun z : E3 => ‖f z‖ ^ 2) z = 0 := by
      intro z hz
      have hz' : f z = 0 := by
        by_contra h
        exact hz (hS (subset_tsupport _ h))
      simp [hz']
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
    have h1 := norm_setIntegral_le_of_norm_le_const hSfin
      (f := fun z : E3 => ‖f z‖ ^ 2) (C := M ^ 2)
      (fun z _ => by
        rw [Real.norm_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hM0 z) 2)
    have hnn : (0 : ℝ) ≤ ∫ z in S, ‖f z‖ ^ 2 :=
      setIntegral_nonneg hSmeas (fun z _ => by positivity)
    rwa [Real.norm_of_nonneg hnn] at h1
  have hLzero : ∀ z ∉ S, L z = 0 := by
    intro z hz
    have hz1 : z ∉ tsupport f := fun hc => hz (hS hc)
    have h1 : z ∉ Function.support (iteratedFDeriv ℝ 2 f) :=
      fun hc => hz1 (support_iteratedFDeriv_subset 2 hc)
    have h2 : iteratedFDeriv ℝ 2 f z = 0 := by
      simpa [Function.mem_support] using h1
    simp [hLdef, h2]
  have hIL : ∫ z : E3, ‖L z‖ ^ 2 ≤ (3 * M) ^ 2 * volume.real S := by
    have hzero : ∀ z ∉ S, (fun z : E3 => ‖L z‖ ^ 2) z = 0 := by
      intro z hz; simp [hLzero z hz]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
    have hbound : ∀ z ∈ S, ‖L z‖ ≤ 3 * M := by
      intro z _
      have h3 : ∀ j : Fin 3, ‖iteratedFDeriv ℝ 2 f z (fun _ : Fin 2 => b j)‖ ≤ M := by
        intro j
        calc ‖iteratedFDeriv ℝ 2 f z (fun _ : Fin 2 => b j)‖
            ≤ ‖iteratedFDeriv ℝ 2 f z‖ * ∏ i : Fin 2, ‖(fun _ : Fin 2 => b j) i‖ :=
              ContinuousMultilinearMap.le_opNorm _ _
          _ = ‖iteratedFDeriv ℝ 2 f z‖ * 1 := by
              congr 1
              simp [OrthonormalBasis.orthonormal b]
          _ ≤ M * 1 := mul_le_mul_of_nonneg_right (hM2 z) zero_le_one
          _ = M := by ring
      calc ‖L z‖ = ‖∑ j : Fin 3, iteratedFDeriv ℝ 2 f z (fun _ : Fin 2 => b j)‖ := by rw [hLdef]
        _ ≤ ∑ j : Fin 3, ‖iteratedFDeriv ℝ 2 f z (fun _ : Fin 2 => b j)‖ := norm_sum_le _ _
        _ ≤ ∑ _j : Fin 3, M := Finset.sum_le_sum (fun j _ => h3 j)
        _ = 3 * M := by rw [Finset.sum_const, Finset.card_univ]; norm_num
    have h1 := norm_setIntegral_le_of_norm_le_const hSfin
      (f := fun z : E3 => ‖L z‖ ^ 2) (C := (3 * M) ^ 2)
      (fun z hz => by
        rw [Real.norm_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hbound z hz) 2)
    have hnn : (0 : ℝ) ≤ ∫ z in S, ‖L z‖ ^ 2 :=
      setIntegral_nonneg hSmeas (fun z _ => by positivity)
    rwa [Real.norm_of_nonneg hnn] at h1
  refine ⟨hInt1, ?_⟩
  calc ∫ ξ : E3, (1 + ‖ξ‖ ^ 2) ^ 2 * ‖𝓕 f ξ‖ ^ 2
      ≤ 2 * (∫ z : E3, ‖f z‖ ^ 2)
        + 2 * ((4 * Real.pi ^ 2) ^ 2)⁻¹ * (∫ z : E3, ‖L z‖ ^ 2) := by
        rw [hmid]; exact hmain
    _ ≤ 2 * (M ^ 2 * volume.real S)
          + 2 * ((4 * Real.pi ^ 2) ^ 2)⁻¹ * ((3 * M) ^ 2 * volume.real S) := by
        have ha : 2 * (∫ z : E3, ‖f z‖ ^ 2) ≤ 2 * (M ^ 2 * volume.real S) :=
          mul_le_mul_of_nonneg_left hIf (by norm_num : (0 : ℝ) ≤ 2)
        have hb : 2 * ((4 * Real.pi ^ 2) ^ 2)⁻¹ * (∫ z : E3, ‖L z‖ ^ 2)
            ≤ 2 * ((4 * Real.pi ^ 2) ^ 2)⁻¹ * ((3 * M) ^ 2 * volume.real S) :=
          mul_le_mul_of_nonneg_left hIL (by positivity)
        linarith [ha, hb]
    _ = (2 * M ^ 2 + 2 * ((4 * Real.pi ^ 2) ^ 2)⁻¹ * (3 * M) ^ 2) * volume.real S := by ring

/-- **`L¹` bound from the weighted `L²` bound.**  For `f : ℝ³ → ℂ` of class `C²` and compact
support, an explicit `(1+‖ξ‖²)²`-weighted `L²` bound on `𝓕 f` gives an `L¹` bound, by
`2‖𝓕 f ξ‖ ≤ (1+‖ξ‖²)²‖𝓕 f ξ‖² + (1+‖ξ‖²)⁻²`. -/
lemma fourier_l1_le_of_weighted {f : E3 → ℂ} (hf : ContDiff ℝ 2 f) (hs : HasCompactSupport f)
    {Cw : ℝ} (hint : Integrable (fun ξ : E3 => (1 + ‖ξ‖ ^ 2) ^ 2 * ‖𝓕 f ξ‖ ^ 2) (volume : Measure E3))
    (hbnd : ∫ ξ : E3, (1 + ‖ξ‖ ^ 2) ^ 2 * ‖𝓕 f ξ‖ ^ 2 ≤ Cw) :
    ∫ ξ : E3, ‖𝓕 f ξ‖
      ≤ Cw / 2 + (1 / 2) * ∫ ξ : E3, (1 + ‖ξ‖ ^ 2) ^ (-2 : ℝ) := by
  have hfl1 : Integrable f (volume : Measure E3) :=
    hf.continuous.integrable_of_hasCompactSupport hs
  have hFcont : Continuous (fun ξ : E3 => 𝓕 f ξ) :=
    VectorFourier.fourierIntegral_continuous (𝕜 := ℝ) Real.continuous_fourierChar
      continuous_inner hfl1
  have hWint : Integrable (fun ξ : E3 => (1 + ‖ξ‖ ^ 2) ^ (-2 : ℝ)) (volume : Measure E3) := by
    have h := integrable_rpow_neg_one_add_norm_sq (E := E3) (μ := (volume : Measure E3)) (r := 4)
      (by rw [finrank_euclideanSpace_fin]; norm_num)
    convert h using 2 with ξ
    norm_num
  have hpt : ∀ ξ : E3, ‖𝓕 f ξ‖
      ≤ (1 / 2) * ((1 + ‖ξ‖ ^ 2) ^ 2 * ‖𝓕 f ξ‖ ^ 2) + (1 / 2) * (1 + ‖ξ‖ ^ 2) ^ (-2 : ℝ) := by
    intro ξ
    have hpos : (0 : ℝ) < 1 + ‖ξ‖ ^ 2 := by positivity
    have hinv : (1 + ‖ξ‖ ^ 2) ^ (-2 : ℝ) = ((1 + ‖ξ‖ ^ 2)⁻¹) ^ 2 := by
      rw [Real.rpow_neg hpos.le, Real.rpow_two, inv_pow]
    have hc1 : (1 + ‖ξ‖ ^ 2) * (1 + ‖ξ‖ ^ 2)⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hpos)
    rw [hinv]
    nlinarith [sq_nonneg ((1 + ‖ξ‖ ^ 2) * ‖𝓕 f ξ‖ - (1 + ‖ξ‖ ^ 2)⁻¹), hc1,
      norm_nonneg (𝓕 f ξ)]
  have hIntL : Integrable (fun ξ : E3 => ‖𝓕 f ξ‖) (volume : Measure E3) :=
    (((hint.const_mul (1 / 2 : ℝ)).add (hWint.const_mul (1 / 2 : ℝ))).mono' hFcont.norm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ξ => by
        rw [Real.norm_of_nonneg (by positivity)]
        exact hpt ξ))
  have hIntR : Integrable (fun ξ : E3 => (1 / 2) * ((1 + ‖ξ‖ ^ 2) ^ 2 * ‖𝓕 f ξ‖ ^ 2)
      + (1 / 2) * (1 + ‖ξ‖ ^ 2) ^ (-2 : ℝ)) (volume : Measure E3) :=
    (hint.const_mul (1 / 2 : ℝ)).add (hWint.const_mul (1 / 2 : ℝ))
  have hmain : ∫ ξ : E3, ‖𝓕 f ξ‖
      ≤ ∫ ξ : E3, ((1 / 2) * ((1 + ‖ξ‖ ^ 2) ^ 2 * ‖𝓕 f ξ‖ ^ 2)
          + (1 / 2) * (1 + ‖ξ‖ ^ 2) ^ (-2 : ℝ)) :=
    integral_mono hIntL hIntR hpt
  have hsplit : ∫ ξ : E3, ((1 / 2) * ((1 + ‖ξ‖ ^ 2) ^ 2 * ‖𝓕 f ξ‖ ^ 2)
      + (1 / 2) * (1 + ‖ξ‖ ^ 2) ^ (-2 : ℝ))
      = (1 / 2) * (∫ ξ : E3, (1 + ‖ξ‖ ^ 2) ^ 2 * ‖𝓕 f ξ‖ ^ 2)
        + (1 / 2) * (∫ ξ : E3, (1 + ‖ξ‖ ^ 2) ^ (-2 : ℝ)) := by
    rw [integral_add (hint.const_mul _) (hWint.const_mul _), integral_const_mul, integral_const_mul]
  rw [hsplit] at hmain
  have h1 : (1 / 2) * (∫ ξ : E3, (1 + ‖ξ‖ ^ 2) ^ 2 * ‖𝓕 f ξ‖ ^ 2) ≤ (1 / 2) * Cw :=
    mul_le_mul_of_nonneg_left hbnd (by norm_num)
  linarith [hmain, h1]

/-- **The uniform kernel bound.**  The weighted `L²` norm of the Fourier transform of the
slices `z ↦ F y z · η z` is bounded uniformly in `y ∈ A`, as is its `L¹` norm. -/
theorem kernel_bounds {ℓ : ℝ} (hℓ : 0 < ℓ) {A : Set E3}
    (hAc : ∀ z ∈ A, ∀ j : Fin 3, -(ℓ / 2) ≤ z j ∧ z j ≤ ℓ / 2)
    {F : E3 × E3 → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    {η : E3 → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηs : HasCompactSupport η)
    (hηsupp : tsupport η ⊆ Metric.closedBall (0 : E3) (cutoffR ℓ + 1)) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧
      (∀ y ∈ A, ∫ ξ : E3, (1 + ‖ξ‖ ^ 2) ^ 2 * ‖𝓕 (slice F η y) ξ‖ ^ 2 ≤ C) ∧
      (∀ y ∈ A, ∫ ξ : E3, ‖𝓕 (slice F η y) ξ‖ ≤ D) := by
  obtain ⟨M, hM0, hM⟩ := exists_joint_bound hF hη ℓ
  have hslice : ∀ y ∈ A, ∀ z : E3, ∀ i : ℕ, i ≤ 2 →
      ‖iteratedFDeriv ℝ i (slice F η y) z‖ ≤ i.factorial * M :=
    fun y hy z i hi => slice_deriv_bound hℓ.le hAc hF hη hηsupp hM0 hM hy hi z
  set S : Set E3 := Metric.closedBall (0 : E3) (cutoffR ℓ + 1) with hSdef
  have hSmeas : MeasurableSet S := measurableSet_closedBall
  have hSfin : volume S < ⊤ := (isCompact_closedBall (0 : E3) (cutoffR ℓ + 1)).measure_lt_top
  have hVnn : 0 ≤ volume.real S := measureReal_nonneg
  set Cw : ℝ := (2 * (2 * M) ^ 2 + 2 * ((4 * Real.pi ^ 2) ^ 2)⁻¹ * (3 * (2 * M)) ^ 2) *
    volume.real S with hCw
  have hCwnn : 0 ≤ Cw := by
    rw [hCw]
    exact mul_nonneg (by positivity) hVnn
  have hcd : ∀ y : E3, ContDiff ℝ 2 (slice F η y) := by
    intro y
    have h1 : ContDiff ℝ (⊤ : ℕ∞) (JFun F η) := contDiff_JFun hF hη
    have h2 : ContDiff ℝ (2 : WithTop ℕ∞) (JFun F η) :=
      h1.of_le (WithTop.coe_le_coe.mpr le_top)
    exact h2.comp (contDiff_const.prodMk contDiff_id)
  have hkey : ∀ y ∈ A, (∫ ξ : E3, (1 + ‖ξ‖ ^ 2) ^ 2 * ‖𝓕 (slice F η y) ξ‖ ^ 2 ≤ Cw) ∧
      Integrable (fun ξ : E3 => (1 + ‖ξ‖ ^ 2) ^ 2 * ‖𝓕 (slice F η y) ξ‖ ^ 2) (volume : Measure E3) := by
    intro y hy
    have hs : HasCompactSupport (slice F η y) := hasCompactSupport_slice hηs y
    have hM0' : ∀ z, ‖slice F η y z‖ ≤ 2 * M := by
      intro z
      have h0 : ‖slice F η y z‖ ≤ M := by
        have h := hslice y hy z 0 (by norm_num)
        simpa using h
      linarith [h0, hM0]
    have hM2' : ∀ z, ‖iteratedFDeriv ℝ 2 (slice F η y) z‖ ≤ 2 * M := by
      intro z
      have h2 := hslice y hy z 2 le_rfl
      have hfac : (2 : ℕ).factorial * M = 2 * M := by norm_num
      rw [hfac] at h2
      exact h2
    have hSsub : tsupport (slice F η y) ⊆ S :=
      (tsupport_slice_subset (F := F) (η := η) y).trans hηsupp
    obtain ⟨hint, hbnd⟩ := weighted_fourier_le (hcd y) hs hM0' hM2' hSsub hSmeas hSfin
    rw [hCw]
    exact ⟨hbnd, hint⟩
  refine ⟨Cw, Cw / 2 + (1 / 2) * (∫ ξ : E3, (1 + ‖ξ‖ ^ 2) ^ (-2 : ℝ)), hCwnn, ?_,
    fun y hy => (hkey y hy).1, ?_⟩
  · have hWnn : 0 ≤ ∫ ξ : E3, (1 + ‖ξ‖ ^ 2) ^ (-2 : ℝ) :=
      integral_nonneg (fun ξ => Real.rpow_nonneg (by positivity) _)
    linarith [hCwnn, hWnn]
  · intro y hy
    exact fourier_l1_le_of_weighted (hcd y) (hasCompactSupport_slice hηs y)
      (hkey y hy).2 (hkey y hy).1

/-! ### The assembly -/

section Assembly

variable {ℓ : ℝ} {A : Set E3} {χ : E3 → ℝ} {F : E3 × E3 → ℝ}

/-- The indicator-windowed `+`-exponential `1_A χ e^{i⟪q,·⟫}`. -/
noncomputable def Aw (A : Set E3) (χ : E3 → ℝ) (q : E3) : E3 → ℂ :=
  A.indicator fun y => (χ y : ℂ) * Complex.exp (Complex.I * ((inner ℝ q y : ℝ) : ℂ))

/-- The indicator-windowed `-`-exponential `1_A χ e^{-i⟪q,·⟫}`. -/
noncomputable def Bw (A : Set E3) (χ : E3 → ℝ) (q : E3) : E3 → ℂ :=
  A.indicator fun z => (χ z : ℂ) * Complex.exp (-(Complex.I * ((inner ℝ q z : ℝ) : ℂ)))

lemma Aw_apply_of_mem {q y : E3} (hy : y ∈ A) :
    Aw A χ q y = (χ y : ℂ) * Complex.exp (Complex.I * ((inner ℝ q y : ℝ) : ℂ)) :=
  Set.indicator_of_mem hy _

lemma Bw_apply_of_mem {q z : E3} (hz : z ∈ A) :
    Bw A χ q z = (χ z : ℂ) * Complex.exp (-(Complex.I * ((inner ℝ q z : ℝ) : ℂ))) :=
  Set.indicator_of_mem hz _

lemma norm_Aw_le (q y : E3) : ‖Aw A χ q y‖ ≤ ‖χ y‖ := by
  by_cases hy : y ∈ A
  · rw [Aw_apply_of_mem hy, norm_mul, Complex.norm_exp]
    simp
  · rw [Aw, Set.indicator_of_notMem hy, norm_zero]; positivity

lemma norm_Bw_le (q z : E3) : ‖Bw A χ q z‖ ≤ ‖χ z‖ := by
  by_cases hz : z ∈ A
  · rw [Bw_apply_of_mem hz, norm_mul, Complex.norm_exp]
    simp
  · rw [Bw, Set.indicator_of_notMem hz, norm_zero]; positivity

lemma aestronglyMeasurable_Aw {q : E3} (hχc : Continuous χ) (hA : MeasurableSet A) :
    AEStronglyMeasurable (Aw A χ q) (volume : Measure E3) := by
  rw [Aw]
  have hg : Continuous fun y : E3 => (χ y : ℂ) *
      Complex.exp (Complex.I * ((inner ℝ q y : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.comp hχc).mul (by fun_prop)
  exact (hg.measurable.indicator hA).aestronglyMeasurable

lemma aestronglyMeasurable_Bw {q : E3} (hχc : Continuous χ) (hA : MeasurableSet A) :
    AEStronglyMeasurable (Bw A χ q) (volume : Measure E3) := by
  rw [Bw]
  have hg : Continuous fun z : E3 => (χ z : ℂ) *
      Complex.exp (-(Complex.I * ((inner ℝ q z : ℝ) : ℂ))) :=
    (Complex.continuous_ofReal.comp hχc).mul (by fun_prop)
  exact (hg.measurable.indicator hA).aestronglyMeasurable

lemma integrable_Aw {q : E3} (hA : MeasurableSet A) (hχc : Continuous χ)
    (hχs : HasCompactSupport χ) : Integrable (Aw A χ q) (volume : Measure E3) := by
  refine Integrable.mono' (hχc.integrable_of_hasCompactSupport hχs).norm
    (aestronglyMeasurable_Aw (A := A) (χ := χ) hχc hA) ?_
  filter_upwards with y
  exact norm_Aw_le q y

lemma integrable_Bw {q : E3} (hA : MeasurableSet A) (hχc : Continuous χ)
    (hχs : HasCompactSupport χ) : Integrable (Bw A χ q) (volume : Measure E3) := by
  refine Integrable.mono' (hχc.integrable_of_hasCompactSupport hχs).norm
    (aestronglyMeasurable_Bw (A := A) (χ := χ) hχc hA) ?_
  filter_upwards with z
  exact norm_Bw_le q z

lemma memLp_two_Aw {q : E3} (hA : MeasurableSet A) (hχc : Continuous χ)
    (hχs : HasCompactSupport χ) : MemLp (Aw A χ q) 2 (volume : Measure E3) := by
  refine MemLp.of_le ((hχc.memLp_of_hasCompactSupport hχs).norm)
    (aestronglyMeasurable_Aw (A := A) (χ := χ) hχc hA) ?_
  filter_upwards with y
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  exact norm_Aw_le q y

lemma memLp_two_Bw {q : E3} (hA : MeasurableSet A) (hχc : Continuous χ)
    (hχs : HasCompactSupport χ) : MemLp (Bw A χ q) 2 (volume : Measure E3) := by
  refine MemLp.of_le ((hχc.memLp_of_hasCompactSupport hχs).norm)
    (aestronglyMeasurable_Bw (A := A) (χ := χ) hχc hA) ?_
  filter_upwards with z
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  exact norm_Bw_le q z

/-- **Plancherel for the `p`-convention transform, Lebesgue-integral form.** -/
lemma lintegral_kinFT_sq {u : E3 → ℂ} (h1 : Integrable u) (h2 : MemLp u 2) :
    ∫⁻ q : E3, (‖Submission.BoseGases.kinFT u q‖ₑ) ^ 2
      = ENNReal.ofReal ((2 * Real.pi) ^ 3 * ∫ y, ‖u y‖ ^ 2) := by
  have hml : MemLp (Submission.BoseGases.kinFT u) 2 (volume : Measure E3) :=
    Work.BoseKinLoc.Momentum.memLp_kinFT h1 h2
  have hint : Integrable (fun q : E3 => ‖Submission.BoseGases.kinFT u q‖ ^ 2)
      (volume : Measure E3) :=
    (memLp_two_iff_integrable_sq_norm hml.aestronglyMeasurable).mp hml
  have hb := ofReal_integral_norm_eq_lintegral_enorm (μ := (volume : Measure E3))
    (f := fun q : E3 => ‖Submission.BoseGases.kinFT u q‖ ^ 2) hint
  rw [show (∫ q : E3, ‖(fun q : E3 => ‖Submission.BoseGases.kinFT u q‖ ^ 2) q‖)
      = ∫ q : E3, ‖Submission.BoseGases.kinFT u q‖ ^ 2 from
    integral_congr_ae (Filter.Eventually.of_forall fun q => Real.norm_of_nonneg (by positivity))]
    at hb
  rw [Work.BoseKinLoc.Momentum.kinFT_l1l2_plancherel h1 h2] at hb
  rw [hb]
  refine lintegral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
  change (‖Submission.BoseGases.kinFT u q‖ₑ) ^ 2
    = ‖(‖Submission.BoseGases.kinFT u q‖ ^ 2 : ℝ)‖ₑ
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤
    ‖Submission.BoseGases.kinFT u q‖)]
  rw [Real.enorm_eq_ofReal (by positivity)]

end Assembly

/-! ### Joint measurability and the pointwise representation -/

section Final

variable {ℓ : ℝ} {A : Set E3} {χ : E3 → ℝ} {F : E3 × E3 → ℝ} {η : E3 → ℝ}

end Final

/-! ### The windowed indicator, the two transforms, and the uniform slice bounds -/

section DiagSetup

variable {ℓ : ℝ} {A : Set E3} {χ : E3 → ℝ} {F : E3 × E3 → ℝ} {η : E3 → ℝ}

/-- The windowed indicator `𝟙_A χ`, as a complex-valued function. -/
noncomputable def chiA (A : Set E3) (χ : E3 → ℝ) : E3 → ℂ :=
  fun z => ((A.indicator χ z : ℝ) : ℂ)

lemma chiA_of_mem {z : E3} (hz : z ∈ A) : chiA A χ z = (χ z : ℂ) := by
  simp [chiA, Set.indicator_of_mem hz]

lemma chiA_of_notMem {z : E3} (hz : z ∉ A) : chiA A χ z = 0 := by
  simp [chiA, Set.indicator_of_notMem hz]

lemma norm_chiA_le (z : E3) : ‖chiA A χ z‖ ≤ ‖χ z‖ := by
  by_cases hz : z ∈ A
  · rw [chiA_of_mem hz]; simp
  · rw [chiA_of_notMem hz]; simp

lemma chiA_eq_indicator_mul (z : E3) :
    chiA A χ z = (A.indicator (fun _ : E3 => (1 : ℂ)) z) * (χ z : ℂ) := by
  by_cases hz : z ∈ A
  · rw [chiA_of_mem hz, Set.indicator_of_mem hz, one_mul]
  · rw [chiA_of_notMem hz, Set.indicator_of_notMem hz, zero_mul]

lemma measurable_chiA (hχc : Continuous χ) (hA : MeasurableSet A) : Measurable (chiA A χ) :=
  Complex.continuous_ofReal.measurable.comp (hχc.measurable.indicator hA)

lemma aestronglyMeasurable_chiA (hχc : Continuous χ) (hA : MeasurableSet A) :
    AEStronglyMeasurable (chiA A χ) (volume : Measure E3) :=
  (measurable_chiA hχc hA).aestronglyMeasurable

lemma Aw_eq_chiA (q y : E3) :
    Aw A χ q y = chiA A χ y * Complex.exp (Complex.I * ((inner ℝ q y : ℝ) : ℂ)) := by
  by_cases hy : y ∈ A
  · rw [Aw_apply_of_mem hy, chiA_of_mem hy]
  · rw [Aw, Set.indicator_of_notMem hy, chiA_of_notMem hy, zero_mul]

lemma Bw_eq_chiA (q z : E3) :
    Bw A χ q z = chiA A χ z * Complex.exp (-(Complex.I * ((inner ℝ q z : ℝ) : ℂ))) := by
  by_cases hz : z ∈ A
  · rw [Bw_apply_of_mem hz, chiA_of_mem hz]
  · rw [Bw, Set.indicator_of_notMem hz, chiA_of_notMem hz, zero_mul]

lemma exp_inner_sub (q y z : E3) :
    Complex.exp (Complex.I * ((inner ℝ q (y - z) : ℝ) : ℂ))
      = Complex.exp (Complex.I * ((inner ℝ q y : ℝ) : ℂ))
        * Complex.exp (-(Complex.I * ((inner ℝ q z : ℝ) : ℂ))) := by
  rw [inner_sub_right, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- `𝓕` is the `p`-convention transform at the frequency `2πw`. -/
lemma fourier_eq_kinFT (g : E3 → ℂ) (w : E3) :
    𝓕 g w = Submission.BoseGases.kinFT g ((2 * Real.pi) • w) := by
  rw [Work.SmallBoxBridge.Resolve.kinFT_eq_fourier g ((2 * Real.pi) • w)]
  congr 1
  simp only [smul_smul, inv_mul_cancel₀ (by positivity : (2 * Real.pi : ℝ) ≠ 0), one_smul]

/-- The Fourier transform of the `+`-window `𝟙_A χ e^{-i⟪q,·⟫}`, in `p`. -/
noncomputable def AFun (A : Set E3) (χ : E3 → ℝ) (q p : E3) : ℂ := 𝓕 (Bw A χ q) p

/-- The `(y,p)`-transform `∫_y 𝟙_A χ e^{i⟪q,y⟫} 𝓕(F(y,·)·η)(-p)`. -/
noncomputable def UFun (A : Set E3) (χ : E3 → ℝ) (F : E3 × E3 → ℝ) (η : E3 → ℝ)
    (q p : E3) : ℂ := ∫ y : E3, Aw A χ q y * 𝓕 (slice F η y) (-p)

lemma AFun_eq_kinFT (q p : E3) :
    AFun A χ q p = Submission.BoseGases.kinFT (fun z => Bw A χ ((2 * Real.pi) • p) z) q := by
  have hfun : Submission.BoseGases.kinFT (Bw A χ q) ((2 * Real.pi) • p)
      = Submission.BoseGases.kinFT (fun z => Bw A χ ((2 * Real.pi) • p) z) q := by
    simp only [Submission.BoseGases.kinFT]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    dsimp only
    have hexp : Complex.exp (-(Complex.I * ((inner ℝ ((2 * Real.pi) • p) z : ℝ) : ℂ)))
        = Complex.exp (-(Complex.I * ((((2 * Real.pi : ℝ) * (inner ℝ p z)) : ℝ) : ℂ))) := by
      rw [real_inner_smul_left]
    rw [Bw_eq_chiA ((2 * Real.pi) • p) z, Bw_eq_chiA q z, hexp]
    ring
  rw [AFun, fourier_eq_kinFT]
  exact hfun

lemma UFun_eq_kinFT (q p : E3) :
    UFun A χ F η q p
      = Submission.BoseGases.kinFT (fun y => chiA A χ y * 𝓕 (slice F η y) (-p)) (-q) := by
  simp only [UFun, Submission.BoseGases.kinFT]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  dsimp only
  have hexp : Complex.exp (-(Complex.I * ((inner ℝ (-q) y : ℝ) : ℂ)))
      = Complex.exp (Complex.I * ((inner ℝ q y : ℝ) : ℂ)) := by
    congr 1
    rw [inner_neg_left]
    push_cast
    ring
  rw [Aw_eq_chiA q y, hexp]
  ring

/-! ### Elementary facts about slices and the `L¹` bounds -/

lemma contDiff_slice {F : E3 × E3 → ℝ} {η : E3 → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (y : E3) : ContDiff ℝ (⊤ : ℕ∞) (slice F η y) :=
  (contDiff_JFun hF hη).comp (contDiff_const.prodMk contDiff_id)

lemma integrable_slice {F : E3 × E3 → ℝ} {η : E3 → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηs : HasCompactSupport η) (y : E3) :
    Integrable (slice F η y) (volume : Measure E3) :=
  (contDiff_slice hF hη y).continuous.integrable_of_hasCompactSupport (hasCompactSupport_slice hηs y)

lemma memLp_two_slice {F : E3 × E3 → ℝ} {η : E3 → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηs : HasCompactSupport η) (y : E3) :
    MemLp (slice F η y) 2 (volume : Measure E3) :=
  (contDiff_slice hF hη y).continuous.memLp_of_hasCompactSupport (hasCompactSupport_slice hηs y)

lemma fourier_norm_le_integral (g : E3 → ℂ) (p : E3) :
    ‖𝓕 g p‖ ≤ ∫ z : E3, ‖g z‖ := by
  rw [Real.fourier_eq]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  simp_rw [Circle.norm_smul]

lemma norm_AFun_le (hA : MeasurableSet A) (hχc : Continuous χ) (hχs : HasCompactSupport χ)
    (q p : E3) : ‖AFun A χ q p‖ ≤ ∫ z : E3, ‖χ z‖ := by
  have h1 : Integrable (Bw A χ q) (volume : Measure E3) := integrable_Bw (A := A) (χ := χ) hA hχc hχs
  have h2 : Integrable (fun z : E3 => ‖χ z‖) (volume : Measure E3) :=
    (hχc.integrable_of_hasCompactSupport hχs).norm
  calc ‖AFun A χ q p‖ = ‖∫ z : E3, 𝐞 (-⟪z, p⟫) • Bw A χ q z‖ := by
        rw [AFun, Real.fourier_eq]
    _ ≤ ∫ z : E3, ‖Bw A χ q z‖ := by
        refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
        simp_rw [Circle.norm_smul]
    _ ≤ ∫ z : E3, ‖χ z‖ := integral_mono h1.norm h2 (fun z => norm_Bw_le q z)

/-! ### Measurability of the joint integrands -/

lemma measurable_Aw_joint (hχc : Continuous χ) (hA : MeasurableSet A) :
    Measurable (fun w : (E3 × E3) × E3 => Aw A χ w.1.1 w.2) := by
  rw [show (fun w : (E3 × E3) × E3 => Aw A χ w.1.1 w.2)
      = fun w => (A.indicator (fun _ : E3 => (1 : ℂ)) w.2)
        * ((χ w.2 : ℂ) * Complex.exp (Complex.I * ((inner ℝ w.1.1 w.2 : ℝ) : ℂ))) from
    funext fun w => by rw [Aw_eq_chiA, chiA_eq_indicator_mul]; ring]
  refine Measurable.mul ((measurable_const.indicator hA).comp measurable_snd) (Measurable.mul ?_ ?_)
  · exact Complex.continuous_ofReal.measurable.comp (hχc.measurable.comp measurable_snd)
  · refine Complex.measurable_exp.comp ?_
    have hinner : Continuous fun w : (E3 × E3) × E3 => (inner ℝ w.1.1 w.2 : ℝ) :=
      continuous_inner.comp (continuous_fst.fst.prodMk continuous_snd)
    exact (continuous_const.mul (Complex.continuous_ofReal.comp hinner)).measurable

lemma measurable_Bw_joint (hχc : Continuous χ) (hA : MeasurableSet A) :
    Measurable (fun w : (E3 × E3) × E3 => Bw A χ w.1.1 w.2) := by
  rw [show (fun w : (E3 × E3) × E3 => Bw A χ w.1.1 w.2)
      = fun w => (A.indicator (fun _ : E3 => (1 : ℂ)) w.2)
        * ((χ w.2 : ℂ) * Complex.exp (-(Complex.I * ((inner ℝ w.1.1 w.2 : ℝ) : ℂ)))) from
    funext fun w => by rw [Bw_eq_chiA, chiA_eq_indicator_mul]; ring]
  refine Measurable.mul ((measurable_const.indicator hA).comp measurable_snd) (Measurable.mul ?_ ?_)
  · exact Complex.continuous_ofReal.measurable.comp (hχc.measurable.comp measurable_snd)
  · refine Complex.measurable_exp.comp ?_
    have hinner : Continuous fun w : (E3 × E3) × E3 => (inner ℝ w.1.1 w.2 : ℝ) :=
      continuous_inner.comp (continuous_fst.fst.prodMk continuous_snd)
    exact ((continuous_const.mul (Complex.continuous_ofReal.comp hinner)).neg).measurable

lemma measurable_Aw_fst (hχc : Continuous χ) (hA : MeasurableSet A) (q : E3) :
    Measurable (fun w : E3 × E3 => Aw A χ q w.1) := by
  rw [show (fun w : E3 × E3 => Aw A χ q w.1)
      = fun w => (A.indicator (fun _ : E3 => (1 : ℂ)) w.1)
        * ((χ w.1 : ℂ) * Complex.exp (Complex.I * ((inner ℝ q w.1 : ℝ) : ℂ))) from
    funext fun w => by rw [Aw_eq_chiA, chiA_eq_indicator_mul]; ring]
  refine Measurable.mul ((measurable_const.indicator hA).comp measurable_fst) (Measurable.mul ?_ ?_)
  · exact Complex.continuous_ofReal.measurable.comp (hχc.measurable.comp measurable_fst)
  · refine Complex.measurable_exp.comp ?_
    have hinner : Continuous fun w : E3 × E3 => (inner ℝ q w.1 : ℝ) :=
      continuous_inner.comp (continuous_const.prodMk continuous_fst)
    exact (continuous_const.mul (Complex.continuous_ofReal.comp hinner)).measurable

/-- `(q,p) ↦ AFun A χ q p` is a.e. strongly measurable. -/
lemma aesm_AFun_joint (hχc : Continuous χ) (hA : MeasurableSet A) :
    AEStronglyMeasurable (fun w : E3 × E3 => AFun A χ w.1 w.2) (volume.prod volume) := by
  have hbase : AEStronglyMeasurable (fun v : (E3 × E3) × E3 =>
      Complex.exp ((↑(-2 * Real.pi * (inner ℝ v.2 v.1.2)) : ℂ) * Complex.I) * Bw A χ v.1.1 v.2)
      (((volume : Measure E3).prod (volume : Measure E3)).prod (volume : Measure E3)) := by
    refine Measurable.aestronglyMeasurable (Measurable.mul ?_ (measurable_Bw_joint hχc hA))
    refine Complex.measurable_exp.comp ?_
    have hinner : Continuous fun v : (E3 × E3) × E3 =>
        (-2 * Real.pi * (inner ℝ v.2 v.1.2) : ℝ) :=
      continuous_const.mul (continuous_inner.comp (continuous_snd.prodMk continuous_fst.snd))
    exact ((Complex.continuous_ofReal.comp hinner).mul continuous_const).measurable
  have h := hbase.integral_prod_right'
  refine h.congr (Filter.Eventually.of_forall fun w => ?_)
  dsimp only
  rw [AFun, Real.fourier_eq']
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only [smul_eq_mul]

/-- For fixed `q`, `(y,p) ↦ AFun A χ q p` is a.e. strongly measurable. -/
lemma aesm_AFun_snd (hχc : Continuous χ) (hA : MeasurableSet A) (q : E3) :
    AEStronglyMeasurable (fun w : E3 × E3 => AFun A χ q w.2) (volume.prod volume) := by
  have hbw : Measurable (fun v : (E3 × E3) × E3 => Bw A χ q v.2) := by
    rw [show (fun v : (E3 × E3) × E3 => Bw A χ q v.2)
        = fun v => (A.indicator (fun _ : E3 => (1 : ℂ)) v.2)
          * ((χ v.2 : ℂ) * Complex.exp (-(Complex.I * ((inner ℝ q v.2 : ℝ) : ℂ)))) from
      funext fun v => by rw [Bw_eq_chiA, chiA_eq_indicator_mul]; ring]
    refine Measurable.mul ((measurable_const.indicator hA).comp measurable_snd) (Measurable.mul ?_ ?_)
    · exact Complex.continuous_ofReal.measurable.comp (hχc.measurable.comp measurable_snd)
    · refine Complex.measurable_exp.comp ?_
      have hinner : Continuous fun v : (E3 × E3) × E3 => (inner ℝ q v.2 : ℝ) :=
        continuous_inner.comp (continuous_const.prodMk continuous_snd)
      exact ((continuous_const.mul (Complex.continuous_ofReal.comp hinner)).neg).measurable
  have hbase : AEStronglyMeasurable (fun v : (E3 × E3) × E3 =>
      Complex.exp ((↑(-2 * Real.pi * (inner ℝ v.2 v.1.2)) : ℂ) * Complex.I) * Bw A χ q v.2)
      (((volume : Measure E3).prod (volume : Measure E3)).prod (volume : Measure E3)) := by
    refine Measurable.aestronglyMeasurable (Measurable.mul ?_ hbw)
    refine Complex.measurable_exp.comp ?_
    have hinner : Continuous fun v : (E3 × E3) × E3 =>
        (-2 * Real.pi * (inner ℝ v.2 v.1.2) : ℝ) :=
      continuous_const.mul (continuous_inner.comp (continuous_snd.prodMk continuous_fst.snd))
    exact ((Complex.continuous_ofReal.comp hinner).mul continuous_const).measurable
  have h := hbase.integral_prod_right'
  refine h.congr (Filter.Eventually.of_forall fun w => ?_)
  dsimp only
  rw [AFun, Real.fourier_eq']
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only [smul_eq_mul]

/-- `(w,y) ↦ 𝓕 (slice F η y) (-p)` is a.e. strongly measurable on the triple product. -/
lemma aesm_sliceFourier_joint3 (hFc : Continuous F) (hηc : Continuous η) :
    AEStronglyMeasurable (fun v : (E3 × E3) × E3 => 𝓕 (slice F η v.2) (-v.1.2))
      (((volume : Measure E3).prod (volume : Measure E3)).prod (volume : Measure E3)) := by
  have hpair : Measurable fun u : ((E3 × E3) × E3) × E3 => (u.1.2, u.2) :=
    measurable_fst.snd.prodMk measurable_snd
  have hbase : AEStronglyMeasurable (fun u : ((E3 × E3) × E3) × E3 =>
      Complex.exp ((↑(-2 * Real.pi * (inner ℝ u.2 (-u.1.1.2))) : ℂ) * Complex.I) * slice F η u.1.2 u.2)
      ((((volume : Measure E3).prod (volume : Measure E3)).prod (volume : Measure E3)).prod
        (volume : Measure E3)) := by
    refine Measurable.aestronglyMeasurable (Measurable.mul ?_ ?_)
    · refine Complex.measurable_exp.comp ?_
      have hinner : Continuous fun u : ((E3 × E3) × E3) × E3 =>
          (-2 * Real.pi * (inner ℝ u.2 (-u.1.1.2)) : ℝ) :=
        continuous_const.mul (continuous_inner.comp (continuous_snd.prodMk (continuous_fst.fst.snd).neg))
      exact ((Complex.continuous_ofReal.comp hinner).mul continuous_const).measurable
    · simp only [slice_apply]
      exact Measurable.mul
        (Complex.continuous_ofReal.measurable.comp (hFc.measurable.comp hpair))
        (Complex.continuous_ofReal.measurable.comp (hηc.measurable.comp measurable_snd))
  have h := hbase.integral_prod_right'
  refine h.congr (Filter.Eventually.of_forall fun v => ?_)
  dsimp only
  rw [Real.fourier_eq']
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only [smul_eq_mul]

/-- `(q,p) ↦ UFun A χ F η q p` is a.e. strongly measurable. -/
lemma aesm_UFun_joint (hχc : Continuous χ) (hA : MeasurableSet A) (hFc : Continuous F)
    (hηc : Continuous η) :
    AEStronglyMeasurable (fun w : E3 × E3 => UFun A χ F η w.1 w.2) (volume.prod volume) := by
  have hbase : AEStronglyMeasurable (fun v : (E3 × E3) × E3 =>
      Aw A χ v.1.1 v.2 * 𝓕 (slice F η v.2) (-v.1.2))
      (((volume : Measure E3).prod (volume : Measure E3)).prod (volume : Measure E3)) :=
    (measurable_Aw_joint hχc hA).aestronglyMeasurable.mul (aesm_sliceFourier_joint3 hFc hηc)
  have h := hbase.integral_prod_right'
  refine h.congr (Filter.Eventually.of_forall fun w => ?_)
  dsimp only
  rw [UFun]

/-- `(y,p) ↦ 𝓕 (slice F η y) (-p)` is a.e. strongly measurable. -/
lemma aesm_sliceFourier_neg (hFc : Continuous F) (hηc : Continuous η) :
    AEStronglyMeasurable (fun w : E3 × E3 => 𝓕 (slice F η w.1) (-w.2)) (volume.prod volume) := by
  have hpair : Measurable fun u : (E3 × E3) × E3 => (u.1.1, u.2) :=
    measurable_fst.fst.prodMk measurable_snd
  have hbase : AEStronglyMeasurable (fun u : (E3 × E3) × E3 =>
      Complex.exp ((↑(-2 * Real.pi * (inner ℝ u.2 (-u.1.2))) : ℂ) * Complex.I) * slice F η u.1.1 u.2)
      (((volume : Measure E3).prod (volume : Measure E3)).prod (volume : Measure E3)) := by
    refine Measurable.aestronglyMeasurable (Measurable.mul ?_ ?_)
    · refine Complex.measurable_exp.comp ?_
      have hinner : Continuous fun u : (E3 × E3) × E3 =>
          (-2 * Real.pi * (inner ℝ u.2 (-u.1.2)) : ℝ) :=
        continuous_const.mul (continuous_inner.comp (continuous_snd.prodMk (continuous_fst.snd).neg))
      exact ((Complex.continuous_ofReal.comp hinner).mul continuous_const).measurable
    · simp only [slice_apply]
      exact Measurable.mul
        (Complex.continuous_ofReal.measurable.comp (hFc.measurable.comp hpair))
        (Complex.continuous_ofReal.measurable.comp (hηc.measurable.comp measurable_snd))
  have h := hbase.integral_prod_right'
  refine h.congr (Filter.Eventually.of_forall fun w => ?_)
  dsimp only
  rw [Real.fourier_eq']
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only [smul_eq_mul]

/-- For fixed `p`, `y ↦ 𝓕 (slice F η y) (-p)` is a.e. strongly measurable. -/
lemma aesm_sliceFourier_fst (hFc : Continuous F) (hηc : Continuous η) (p : E3) :
    AEStronglyMeasurable (fun y : E3 => 𝓕 (slice F η y) (-p)) (volume : Measure E3) := by
  have hbase : AEStronglyMeasurable (fun u : E3 × E3 =>
      Complex.exp ((↑(-2 * Real.pi * (inner ℝ u.2 (-p))) : ℂ) * Complex.I) * slice F η u.1 u.2)
      (volume.prod volume) := by
    refine Measurable.aestronglyMeasurable (Measurable.mul ?_ ?_)
    · refine Complex.measurable_exp.comp ?_
      have hinner : Continuous fun u : E3 × E3 => (-2 * Real.pi * (inner ℝ u.2 (-p)) : ℝ) :=
        continuous_const.mul (continuous_inner.comp (continuous_snd.prodMk continuous_const))
      exact ((Complex.continuous_ofReal.comp hinner).mul continuous_const).measurable
    · simp only [slice_apply]
      exact Measurable.mul
        (Complex.continuous_ofReal.measurable.comp (hFc.measurable.comp (measurable_fst.prodMk measurable_snd)))
        (Complex.continuous_ofReal.measurable.comp (hηc.measurable.comp measurable_snd))
  have h := hbase.integral_prod_right'
  refine h.congr (Filter.Eventually.of_forall fun y => ?_)
  dsimp only
  rw [Real.fourier_eq']
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only [smul_eq_mul]

end DiagSetup

/-! ### The two Plancherel identities and the Fubini domination -/

section DiagPlancherel

variable {ℓ : ℝ} {A : Set E3} {χ : E3 → ℝ} {F : E3 × E3 → ℝ} {η : E3 → ℝ}

/-- For fixed `y`, the slice transform is continuous in the frequency. -/
lemma continuous_fourier_slice (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηs : HasCompactSupport η) (y : E3) :
    Continuous (fun p : E3 => 𝓕 (slice F η y) p) :=
  VectorFourier.fourierIntegral_continuous (𝕜 := ℝ) Real.continuous_fourierChar continuous_inner
    (integrable_slice hF hη hηs y)

/-- Negation does not change the lintegral of the slice transform. -/
lemma lintegral_sliceFourier_neg (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηs : HasCompactSupport η) (y : E3) :
    ∫⁻ p : E3, ‖𝓕 (slice F η y) (-p)‖ₑ = ∫⁻ p : E3, ‖𝓕 (slice F η y) p‖ₑ :=
  (Measure.measurePreserving_neg (volume : Measure E3)).lintegral_comp
    (f := fun p : E3 => ‖𝓕 (slice F η y) p‖ₑ)
    ((continuous_fourier_slice hF hη hηs y).measurable.enorm)

/-- The Fourier transform of a weighted `C²` compactly supported function is integrable. -/
lemma integrable_fourier_of_weighted {f : E3 → ℂ} (hf : ContDiff ℝ 2 f) (hs : HasCompactSupport f)
    (hint : Integrable (fun ξ : E3 => (1 + ‖ξ‖ ^ 2) ^ 2 * ‖𝓕 f ξ‖ ^ 2) (volume : Measure E3)) :
    Integrable (𝓕 f) (volume : Measure E3) := by
  have hfl1 : Integrable f (volume : Measure E3) := hf.continuous.integrable_of_hasCompactSupport hs
  have hFcont : Continuous (fun ξ : E3 => 𝓕 f ξ) :=
    VectorFourier.fourierIntegral_continuous (𝕜 := ℝ) Real.continuous_fourierChar continuous_inner
      hfl1
  have hWint : Integrable (fun ξ : E3 => (1 + ‖ξ‖ ^ 2) ^ (-2 : ℝ)) (volume : Measure E3) := by
    have h := integrable_rpow_neg_one_add_norm_sq (E := E3) (μ := (volume : Measure E3)) (r := 4)
      (by rw [finrank_euclideanSpace_fin]; norm_num)
    convert h using 2 with ξ
    norm_num
  have hpt : ∀ ξ : E3, ‖𝓕 f ξ‖
      ≤ (1 / 2) * ((1 + ‖ξ‖ ^ 2) ^ 2 * ‖𝓕 f ξ‖ ^ 2) + (1 / 2) * (1 + ‖ξ‖ ^ 2) ^ (-2 : ℝ) := by
    intro ξ
    have hpos : (0 : ℝ) < 1 + ‖ξ‖ ^ 2 := by positivity
    have hinv : (1 + ‖ξ‖ ^ 2) ^ (-2 : ℝ) = ((1 + ‖ξ‖ ^ 2)⁻¹) ^ 2 := by
      rw [Real.rpow_neg hpos.le, Real.rpow_two, inv_pow]
    have hc1 : (1 + ‖ξ‖ ^ 2) * (1 + ‖ξ‖ ^ 2)⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hpos)
    rw [hinv]
    nlinarith [sq_nonneg ((1 + ‖ξ‖ ^ 2) * ‖𝓕 f ξ‖ - (1 + ‖ξ‖ ^ 2)⁻¹), hc1,
      norm_nonneg (𝓕 f ξ)]
  exact ((hint.const_mul (1 / 2 : ℝ)).add (hWint.const_mul (1 / 2 : ℝ))).mono'
    hFcont.aestronglyMeasurable (Filter.Eventually.of_forall hpt)

/-- **The extended uniform kernel bounds.**  The weighted `L²` bound, the `L¹` bound, the
integrability of the slice transform, and a uniform pointwise bound on the slice transform. -/
theorem kernel_bounds_ext {ℓ : ℝ} (hℓ : 0 < ℓ) {A : Set E3}
    (hAc : ∀ z ∈ A, ∀ j : Fin 3, -(ℓ / 2) ≤ z j ∧ z j ≤ ℓ / 2)
    {F : E3 × E3 → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    ∃ C D Ms : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ 0 ≤ Ms ∧
      (∀ y ∈ A, ∫ ξ : E3, (1 + ‖ξ‖ ^ 2) ^ 2 * ‖𝓕 (slice F (etaCut ℓ) y) ξ‖ ^ 2 ≤ C) ∧
      (∀ y ∈ A, ∫ ξ : E3, ‖𝓕 (slice F (etaCut ℓ) y) ξ‖ ≤ D) ∧
      (∀ y ∈ A, Integrable (𝓕 (slice F (etaCut ℓ) y)) (volume : Measure E3)) ∧
      (∀ y ∈ A, Integrable (fun ξ : E3 => (1 + ‖ξ‖ ^ 2) ^ 2
        * ‖𝓕 (slice F (etaCut ℓ) y) ξ‖ ^ 2) (volume : Measure E3)) ∧
      (∀ y ∈ A, ∀ p : E3, ‖𝓕 (slice F (etaCut ℓ) y) p‖ ≤ Ms) := by
  have hηc : ContDiff ℝ (⊤ : ℕ∞) (etaCut ℓ) := contDiff_etaCut ℓ
  have hηs : HasCompactSupport (etaCut ℓ) := hasCompactSupport_etaCut ℓ
  have hηsupp : tsupport (etaCut ℓ) ⊆ Metric.closedBall (0 : E3) (cutoffR ℓ + 1) :=
    tsupport_etaCut_subset ℓ
  obtain ⟨C, D, hC0, hD0, hCb, hDb⟩ := kernel_bounds hℓ hAc hF hηc hηs hηsupp
  obtain ⟨M, hM0, hM⟩ := exists_joint_bound hF hηc ℓ
  have hslice : ∀ y ∈ A, ∀ z : E3, ‖slice F (etaCut ℓ) y z‖ ≤ 2 * M := by
    intro y hy z
    have h0 : ‖slice F (etaCut ℓ) y z‖ ≤ M := by
      have h := slice_deriv_bound hℓ.le hAc hF hηc hηsupp hM0 hM hy (n := 0) (by norm_num) z
      simpa using h
    linarith
  set S : Set E3 := Metric.closedBall (0 : E3) (cutoffR ℓ + 1) with hSdef
  have hSmeas : MeasurableSet S := measurableSet_closedBall
  have hSfin : (volume : Measure E3) S < ⊤ :=
    (isCompact_closedBall (0 : E3) (cutoffR ℓ + 1)).measure_lt_top
  have hpair : ∀ y ∈ A,
      (Integrable (fun ξ : E3 => (1 + ‖ξ‖ ^ 2) ^ 2 * ‖𝓕 (slice F (etaCut ℓ) y) ξ‖ ^ 2)
          (volume : Measure E3)) ∧
      Integrable (𝓕 (slice F (etaCut ℓ) y)) (volume : Measure E3) := by
    intro y hy
    have hcd2 : ContDiff ℝ 2 (slice F (etaCut ℓ) y) :=
      (contDiff_slice hF hηc y).of_le (WithTop.coe_le_coe.mpr le_top)
    have hM0' : ∀ z, ‖slice F (etaCut ℓ) y z‖ ≤ 2 * M := hslice y hy
    have hM2' : ∀ z, ‖iteratedFDeriv ℝ 2 (slice F (etaCut ℓ) y) z‖ ≤ 2 * M := by
      intro z
      have h2 := slice_deriv_bound hℓ.le hAc hF hηc hηsupp hM0 hM hy (n := 2) le_rfl z
      have hfac : (2 : ℕ).factorial * M = 2 * M := by norm_num
      rw [hfac] at h2
      exact h2
    have hSsub : tsupport (slice F (etaCut ℓ) y) ⊆ S :=
      (tsupport_slice_subset (F := F) (η := etaCut ℓ) y).trans hηsupp
    have hw := weighted_fourier_le hcd2 (hasCompactSupport_slice hηs y) hM0' hM2' hSsub
      hSmeas hSfin
    exact ⟨hw.1, integrable_fourier_of_weighted hcd2 (hasCompactSupport_slice hηs y) hw.1⟩
  refine ⟨C, D, 2 * M * (volume : Measure E3).real S, hC0, hD0, ?_, hCb, hDb,
    (fun y hy => (hpair y hy).2), (fun y hy => (hpair y hy).1), ?_⟩
  · have hnn : 0 ≤ (volume : Measure E3).real S := measureReal_nonneg
    nlinarith [hM0, hnn]
  · intro y hy p
    have h0 : ∀ z : E3, ‖slice F (etaCut ℓ) y z‖ ≤ 2 * M := hslice y hy
    have hzero : ∀ z ∉ S, slice F (etaCut ℓ) y z = 0 := by
      intro z hz
      have h1 : z ∉ tsupport (slice F (etaCut ℓ) y) :=
        fun h => hz (hηsupp (tsupport_slice_subset (F := F) (η := etaCut ℓ) y h))
      have h2 : z ∉ Function.support (slice F (etaCut ℓ) y) :=
        fun hc => h1 (subset_tsupport _ hc)
      simpa [Function.mem_support] using h2
    have hpt : ∀ z : E3, ‖slice F (etaCut ℓ) y z‖ ≤ S.indicator (fun _ : E3 => 2 * M) z := by
      intro z
      by_cases hz : z ∈ S
      · rw [Set.indicator_of_mem hz]; exact h0 z
      · rw [Set.indicator_of_notMem hz, hzero z hz, norm_zero]
    have hInt1 : Integrable (fun z : E3 => ‖slice F (etaCut ℓ) y z‖) (volume : Measure E3) :=
      (integrable_slice hF hηc hηs y).norm
    have hInt2 : Integrable (S.indicator fun _ : E3 => 2 * M) (volume : Measure E3) :=
      (integrable_indicator_iff hSmeas).mpr
        (integrableOn_const (C := 2 * M) (ne_of_lt hSfin)
          (by rw [Real.enorm_eq_ofReal (by linarith : (0 : ℝ) ≤ 2 * M)]
              exact ENNReal.ofReal_ne_top))
    calc ‖𝓕 (slice F (etaCut ℓ) y) p‖ ≤ ∫ z : E3, ‖slice F (etaCut ℓ) y z‖ :=
          fourier_norm_le_integral _ _
      _ ≤ ∫ z : E3, S.indicator (fun _ : E3 => 2 * M) z := integral_mono hInt1 hInt2 hpt
      _ = 2 * M * (volume : Measure E3).real S := by
          rw [integral_indicator_const (2 * M) hSmeas, smul_eq_mul, mul_comm]

/-- The windowed slice transform (against the fixed frequency `-p`) is integrable. -/
lemma integrable_wp (hχc : Continuous χ) (hA : MeasurableSet A) (hχs : HasCompactSupport χ)
    (hFc : Continuous F) (hηc : Continuous η) {Ms : ℝ} (hMs0 : 0 ≤ Ms)
    (hsup : ∀ y ∈ A, ∀ p : E3, ‖𝓕 (slice F η y) p‖ ≤ Ms) (p : E3) :
    Integrable (fun y : E3 => chiA A χ y * 𝓕 (slice F η y) (-p)) (volume : Measure E3) := by
  have hχint : Integrable (fun y : E3 => ‖χ y‖) (volume : Measure E3) :=
    (hχc.integrable_of_hasCompactSupport hχs).norm
  have hdom : Integrable (fun y : E3 => ‖χ y‖ * Ms) (volume : Measure E3) := hχint.mul_const Ms
  refine hdom.mono' ((measurable_chiA hχc hA).aestronglyMeasurable.mul
    (aesm_sliceFourier_fst (F := F) (η := η) hFc hηc p)) ?_
  filter_upwards with y
  rw [norm_mul]
  by_cases hy : y ∈ A
  · exact mul_le_mul (norm_chiA_le y) (hsup y hy (-p)) (norm_nonneg _) (norm_nonneg _)
  · rw [chiA_of_notMem hy, norm_zero, zero_mul]
    exact mul_nonneg (norm_nonneg _) hMs0

/-- The same function is in `L²`. -/
lemma memLp_two_wp (hχc : Continuous χ) (hA : MeasurableSet A) (hχs : HasCompactSupport χ)
    (hFc : Continuous F) (hηc : Continuous η) {Ms : ℝ} (hMs0 : 0 ≤ Ms)
    (hsup : ∀ y ∈ A, ∀ p : E3, ‖𝓕 (slice F η y) p‖ ≤ Ms) (p : E3) :
    MemLp (fun y : E3 => chiA A χ y * 𝓕 (slice F η y) (-p)) 2 (volume : Measure E3) := by
  have hg : MemLp (fun y : E3 => ‖χ y‖ * Ms) 2 (volume : Measure E3) :=
    (hχc.memLp_of_hasCompactSupport hχs).norm.mul_const Ms
  refine hg.of_le ((measurable_chiA hχc hA).aestronglyMeasurable.mul
    (aesm_sliceFourier_fst (F := F) (η := η) hFc hηc p)) ?_
  filter_upwards with y
  rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) hMs0), norm_mul]
  by_cases hy : y ∈ A
  · exact mul_le_mul (norm_chiA_le y) (hsup y hy (-p)) (norm_nonneg _) (norm_nonneg _)
  · rw [chiA_of_notMem hy, norm_zero, zero_mul]
    exact mul_nonneg (norm_nonneg _) hMs0

/-- **Plancherel in `q` for `AFun`.** -/
lemma AFun_lintegral_sq (hA : MeasurableSet A) (hχc : Continuous χ) (hχs : HasCompactSupport χ)
    (p : E3) :
    ∫⁻ q : E3, (‖AFun A χ q p‖ₑ) ^ 2
      = ENNReal.ofReal ((2 * Real.pi) ^ 3 * ∫ z : E3, ‖chiA A χ z‖ ^ 2) := by
  have hfun : (fun q : E3 => (‖AFun A χ q p‖ₑ) ^ 2)
      = fun q : E3 =>
          (‖Submission.BoseGases.kinFT (fun z => Bw A χ ((2 * Real.pi) • p) z) q‖ₑ) ^ 2 := by
    funext q
    rw [AFun_eq_kinFT]
  rw [hfun, lintegral_kinFT_sq (integrable_Bw (A := A) (χ := χ) (q := (2 * Real.pi) • p)
      hA hχc hχs) (memLp_two_Bw (A := A) (χ := χ) (q := (2 * Real.pi) • p) hA hχc hχs)]
  congr 1
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  dsimp only
  rw [Bw_eq_chiA, norm_mul, Complex.norm_exp]
  simp

/-- **Plancherel in `q` for `UFun`.** -/
lemma UFun_lintegral_sq (hA : MeasurableSet A) (hχc : Continuous χ) (hχs : HasCompactSupport χ)
    (hFc : Continuous F) (hηc : Continuous η) {Ms : ℝ} (hMs0 : 0 ≤ Ms)
    (hsup : ∀ y ∈ A, ∀ p : E3, ‖𝓕 (slice F η y) p‖ ≤ Ms) (p : E3) :
    ∫⁻ q : E3, (‖UFun A χ F η q p‖ₑ) ^ 2
      = ENNReal.ofReal ((2 * Real.pi) ^ 3
          * ∫ y : E3, ‖chiA A χ y‖ ^ 2 * ‖𝓕 (slice F η y) (-p)‖ ^ 2) := by
  set w : E3 → ℂ := fun y => chiA A χ y * 𝓕 (slice F η y) (-p) with hw
  have hw1 : Integrable w (volume : Measure E3) :=
    integrable_wp hχc hA hχs hFc hηc hMs0 hsup p
  have hw2 : MemLp w 2 (volume : Measure E3) :=
    memLp_two_wp hχc hA hχs hFc hηc hMs0 hsup p
  have hfun : (fun q : E3 => (‖UFun A χ F η q p‖ₑ) ^ 2)
      = fun q : E3 => (‖Submission.BoseGases.kinFT w (-q)‖ₑ) ^ 2 := by
    funext q
    rw [UFun_eq_kinFT, hw]
  rw [hfun, (Measure.measurePreserving_neg (volume : Measure E3)).lintegral_comp
    (f := fun q : E3 => (‖Submission.BoseGases.kinFT w q‖ₑ) ^ 2)
    (((Work.BoseKinLoc.Momentum.continuous_kinFT_of_integrable hw1).measurable.enorm).pow_const 2),
    lintegral_kinFT_sq hw1 hw2]
  congr 1
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  dsimp only
  rw [hw, norm_mul, mul_pow]

/-- **The Fubini domination.**  The `(y,p)`-integrand of the representation is integrable. -/
lemma integrable_fubini_integrand (hχc : Continuous χ) (hA : MeasurableSet A)
    (hχs : HasCompactSupport χ) (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηs : HasCompactSupport η) {D : ℝ} (hD0 : 0 ≤ D)
    (hD : ∀ y ∈ A, ∫ ξ : E3, ‖𝓕 (slice F η y) ξ‖ ≤ D)
    (hIntF : ∀ y ∈ A, Integrable (𝓕 (slice F η y)) (volume : Measure E3)) (q : E3) :
    Integrable (fun w : E3 × E3 =>
      Aw A χ q w.1 * (AFun A χ q w.2 * 𝓕 (slice F η w.1) (-w.2))) (volume.prod volume) := by
  set Kχ : ℝ := ∫ z : E3, ‖χ z‖ with hKχdef
  have hKχ0 : 0 ≤ Kχ := integral_nonneg fun z => norm_nonneg (χ z)
  have hAK : ∀ p : E3, ‖AFun A χ q p‖ ≤ Kχ := fun p => by
    rw [hKχdef]; exact norm_AFun_le hA hχc hχs q p
  set g : E3 × E3 → ℝ := fun w =>
    A.indicator (fun y => ‖χ y‖) w.1 * (Kχ * ‖𝓕 (slice F η w.1) (-w.2)‖) with hgdef
  have hgAESM : AEStronglyMeasurable g (volume.prod volume) := by
    rw [hgdef]
    exact AEStronglyMeasurable.mul
      (((hχc.measurable.norm.indicator hA).comp measurable_fst).aestronglyMeasurable)
      (AEStronglyMeasurable.mul aestronglyMeasurable_const
        (aesm_sliceFourier_neg (F := F) (η := η) hF.continuous hη.continuous).norm)
  have hgval : ∀ y p : E3, ‖g (y, p)‖ₑ
      = ENNReal.ofReal (A.indicator (fun z => ‖χ z‖) y)
        * (ENNReal.ofReal Kχ * ‖𝓕 (slice F η y) (-p)‖ₑ) := by
    intro y p
    rw [hgdef]
    dsimp only
    by_cases hy : y ∈ A
    · rw [Set.indicator_of_mem hy]
      rw [Real.enorm_eq_ofReal (mul_nonneg (norm_nonneg _) (mul_nonneg hKχ0 (norm_nonneg _))),
        ENNReal.ofReal_mul (norm_nonneg _), ENNReal.ofReal_mul hKχ0]
      simp
    · rw [Set.indicator_of_notMem hy, zero_mul,
        Real.enorm_eq_ofReal le_rfl, ENNReal.ofReal_zero, zero_mul]
  have hgFI : HasFiniteIntegral g (volume.prod volume) := by
    rw [hasFiniteIntegral_iff_enorm,
      lintegral_prod (f := fun w : E3 × E3 => ‖g w‖ₑ) hgAESM.enorm]
    have hstep : ∀ y : E3, ∫⁻ p : E3, ‖g (y, p)‖ₑ
        ≤ ENNReal.ofReal (A.indicator (fun z => ‖χ z‖) y)
          * (ENNReal.ofReal Kχ * ENNReal.ofReal D) := by
      intro y
      rw [lintegral_congr_ae (Filter.Eventually.of_forall (hgval y))]
      by_cases hy : y ∈ A
      · have hbd : ∫⁻ p : E3, ‖𝓕 (slice F η y) (-p)‖ₑ ≤ ENNReal.ofReal D := by
          rw [lintegral_sliceFourier_neg (F := F) (η := η) hF hη hηs y,
            ← ofReal_integral_norm_eq_lintegral_enorm (hIntF y hy)]
          exact ENNReal.ofReal_le_ofReal (hD y hy)
        rw [Set.indicator_of_mem hy, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        gcongr
      · rw [Set.indicator_of_notMem hy]
        simp
    have hmain : ∫⁻ y : E3, ENNReal.ofReal (A.indicator (fun z => ‖χ z‖) y)
        ≤ ENNReal.ofReal (∫ z : E3, ‖χ z‖) := by
      have h1 : ∫⁻ y : E3, ENNReal.ofReal (A.indicator (fun z => ‖χ z‖) y)
          ≤ ∫⁻ y : E3, ‖χ y‖ₑ :=
        lintegral_mono fun y => by
          by_cases hy : y ∈ A
          · rw [Set.indicator_of_mem hy, Real.enorm_eq_ofReal_abs, Real.norm_eq_abs]
          · rw [Set.indicator_of_notMem hy]
            simp
      exact h1.trans (le_of_eq (ofReal_integral_norm_eq_lintegral_enorm
        (hχc.integrable_of_hasCompactSupport hχs)).symm)
    calc ∫⁻ y : E3, ∫⁻ p : E3, ‖g (y, p)‖ₑ
        ≤ ∫⁻ y : E3, ENNReal.ofReal (A.indicator (fun z => ‖χ z‖) y)
            * (ENNReal.ofReal Kχ * ENNReal.ofReal D) := lintegral_mono hstep
      _ = (∫⁻ y : E3, ENNReal.ofReal (A.indicator (fun z => ‖χ z‖) y))
            * (ENNReal.ofReal Kχ * ENNReal.ofReal D) := by
          rw [lintegral_mul_const' _ _
            (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)]
      _ ≤ ENNReal.ofReal (∫ z : E3, ‖χ z‖) * (ENNReal.ofReal Kχ * ENNReal.ofReal D) := by
          gcongr
      _ = ENNReal.ofReal (Kχ * D * ∫ z : E3, ‖χ z‖) := by
          rw [ENNReal.ofReal_mul (mul_nonneg hKχ0 hD0), ENNReal.ofReal_mul hKχ0]
          exact mul_comm _ _
      _ < ⊤ := ENNReal.ofReal_lt_top
  have hAESM : AEStronglyMeasurable (fun w : E3 × E3 =>
      Aw A χ q w.1 * (AFun A χ q w.2 * 𝓕 (slice F η w.1) (-w.2))) (volume.prod volume) :=
    ((measurable_Aw_fst hχc hA q).aestronglyMeasurable).mul
      ((aesm_AFun_snd hχc hA q).mul
        (aesm_sliceFourier_neg (F := F) (η := η) hF.continuous hη.continuous))
  refine ⟨hAESM, HasFiniteIntegral.mono' hgFI (Filter.Eventually.of_forall fun w => ?_)⟩
  rw [norm_mul, norm_mul]
  by_cases hy : w.1 ∈ A
  · have h1 : ‖Aw A χ q w.1‖ ≤ ‖χ w.1‖ := norm_Aw_le q w.1
    have h2 : ‖AFun A χ q w.2‖ ≤ Kχ := hAK w.2
    have h3 : 0 ≤ ‖𝓕 (slice F η w.1) (-w.2)‖ := norm_nonneg _
    have h4 : 0 ≤ ‖AFun A χ q w.2‖ := norm_nonneg _
    have key : ‖Aw A χ q w.1‖ * (‖AFun A χ q w.2‖ * ‖𝓕 (slice F η w.1) (-w.2)‖)
        ≤ ‖χ w.1‖ * (Kχ * ‖𝓕 (slice F η w.1) (-w.2)‖) :=
      mul_le_mul h1 (mul_le_mul_of_nonneg_right h2 h3) (mul_nonneg h4 h3) (norm_nonneg _)
    rw [hgdef]
    dsimp only
    rw [Set.indicator_of_mem hy]
    exact key
  · rw [Aw, Set.indicator_of_notMem hy, norm_zero, zero_mul]
    rw [hgdef]
    dsimp only
    rw [Set.indicator_of_notMem hy]
    simp

end DiagPlancherel

/-! ### The final assembly: weights, the representation, and the `L¹` bound -/

section DiagFinal

variable {ℓ : ℝ} {A : Set E3} {χ : E3 → ℝ} {F : E3 × E3 → ℝ} {η : E3 → ℝ}

/-- The low-frequency weight `(1+‖p‖²)⁻²/2`. -/
noncomputable def cfw (p : E3) : ℝ := (1 / 2) * ((1 + ‖p‖ ^ 2) ^ 2)⁻¹

/-- The high-frequency weight `(1+‖p‖²)²/2`. -/
noncomputable def dfw (p : E3) : ℝ := (1 / 2) * (1 + ‖p‖ ^ 2) ^ 2

lemma cfw_nonneg (p : E3) : 0 ≤ cfw p := by rw [cfw]; positivity

lemma dfw_nonneg (p : E3) : 0 ≤ dfw p := by rw [dfw]; positivity

lemma cfw_pos (p : E3) : 0 < cfw p := by rw [cfw]; positivity

lemma dfw_pos (p : E3) : 0 < dfw p := by rw [dfw]; positivity

lemma cfw_mul_dfw (p : E3) : cfw p * dfw p = 1 / 4 := by
  rw [cfw, dfw,
    show (1 / 2) * ((1 + ‖p‖ ^ 2) ^ 2)⁻¹ * ((1 / 2) * (1 + ‖p‖ ^ 2) ^ 2)
      = (1 / 4) * (((1 + ‖p‖ ^ 2) ^ 2)⁻¹ * (1 + ‖p‖ ^ 2) ^ 2) by ring,
    inv_mul_cancel₀ (by positivity : ((1 + ‖p‖ ^ 2) ^ 2) ≠ 0), mul_one]

lemma continuous_cfw : Continuous cfw := by
  change Continuous fun p : E3 => (1 / 2) * ((1 + ‖p‖ ^ 2) ^ 2)⁻¹
  exact continuous_const.mul
    ((by fun_prop : Continuous fun p : E3 => (1 + ‖p‖ ^ 2) ^ 2).inv₀ (fun p => by positivity))

lemma continuous_dfw : Continuous dfw := by
  change Continuous fun p : E3 => (1 / 2) * (1 + ‖p‖ ^ 2) ^ 2
  fun_prop

lemma integrable_cfw : Integrable cfw (volume : Measure E3) := by
  have h0 : Integrable (fun p : E3 => (1 + ‖p‖ ^ 2) ^ (-2 : ℝ)) (volume : Measure E3) := by
    convert integrable_rpow_neg_one_add_norm_sq (E := E3) (μ := (volume : Measure E3)) (r := 4)
      (by rw [finrank_euclideanSpace_fin]; norm_num) using 2 with p
    rw [show (-4 / 2 : ℝ) = -2 by norm_num]
  have h2 : ∀ p : E3, (1 + ‖p‖ ^ 2) ^ (-2 : ℝ) = ((1 + ‖p‖ ^ 2) ^ 2)⁻¹ := by
    intro p
    rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ 1 + ‖p‖ ^ 2), Real.rpow_two]
  refine Integrable.congr (h0.const_mul (1 / 2)) ?_
  filter_upwards with p
  rw [cfw, h2 p]

/-- The two-point AM–GM with the weights `cfw`, `dfw`. -/
lemma amgm_weight {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (p : E3) :
    a * b ≤ cfw p * a ^ 2 + dfw p * b ^ 2 := by
  have hd : 0 < dfw p := dfw_pos p
  have hcd : cfw p * dfw p = 1 / 4 := cfw_mul_dfw p
  have key : 0 ≤ dfw p * (a / (2 * dfw p) - b) ^ 2 := mul_nonneg hd.le (sq_nonneg _)
  have hid : cfw p * a ^ 2 + dfw p * b ^ 2 - a * b = dfw p * (a / (2 * dfw p) - b) ^ 2 := by
    field_simp
    nlinarith [hcd]
  linarith [key, hid]

/-- Negation does not change a Lebesgue integral on `ℝ³`. -/
lemma integral_neg_comp_eq (g : E3 → ℝ) :
    ∫ p : E3, g (-p) = ∫ p : E3, g p :=
  (Measure.measurePreserving_neg (volume : Measure E3)).integral_comp measurableEmbedding_neg g

/-- The slice transform with the frequency in the first slot is a.e. strongly measurable. -/
lemma aesm_sliceFourier_swap (hFc : Continuous F) (hηc : Continuous η) :
    AEStronglyMeasurable (fun w : E3 × E3 => 𝓕 (slice F η w.2) (-w.1)) (volume.prod volume) := by
  have hpair : Measurable fun u : (E3 × E3) × E3 => (u.1.2, u.2) :=
    measurable_fst.snd.prodMk measurable_snd
  have hbase : AEStronglyMeasurable (fun u : (E3 × E3) × E3 =>
      Complex.exp ((↑(-2 * Real.pi * (inner ℝ u.2 (-u.1.1))) : ℂ) * Complex.I)
        * slice F η u.1.2 u.2)
      (((volume : Measure E3).prod (volume : Measure E3)).prod (volume : Measure E3)) := by
    refine Measurable.aestronglyMeasurable (Measurable.mul ?_ ?_)
    · refine Complex.measurable_exp.comp ?_
      have hinner : Continuous fun u : (E3 × E3) × E3 =>
          (-2 * Real.pi * (inner ℝ u.2 (-u.1.1)) : ℝ) :=
        continuous_const.mul (continuous_inner.comp (continuous_snd.prodMk (continuous_fst.fst).neg))
      exact ((Complex.continuous_ofReal.comp hinner).mul continuous_const).measurable
    · simp only [slice_apply]
      exact Measurable.mul
        (Complex.continuous_ofReal.measurable.comp (hFc.measurable.comp hpair))
        (Complex.continuous_ofReal.measurable.comp (hηc.measurable.comp measurable_snd))
  have h := hbase.integral_prod_right'
  refine h.congr (Filter.Eventually.of_forall fun w => ?_)
  dsimp only
  rw [Real.fourier_eq']
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only [smul_eq_mul]

/-- **The pointwise representation of the diagonal Fourier transform.** -/
lemma diag_repr (q : E3) (hA : MeasurableSet A) (hχc : Continuous χ) (hχs : HasCompactSupport χ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) {η : E3 → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη1 : ∀ z ∈ A, η z = 1) (hηs : HasCompactSupport η)
    {D : ℝ} (hD0 : 0 ≤ D) (hD : ∀ y ∈ A, ∫ ξ : E3, ‖𝓕 (slice F η y) ξ‖ ≤ D)
    (hIntF : ∀ y ∈ A, Integrable (𝓕 (slice F η y)) (volume : Measure E3)) :
    (∫ y in A, ∫ z in A, (χ y : ℂ) * (χ z : ℂ)
        * Complex.exp (Complex.I * ((inner ℝ q (y - z) : ℝ) : ℂ)) * ((F (y, z) : ℝ) : ℂ))
      = ∫ p : E3, AFun A χ q p * UFun A χ F η q p := by
  set G : E3 → E3 → ℂ := fun y z => (χ y : ℂ) * (χ z : ℂ)
      * Complex.exp (Complex.I * ((inner ℝ q (y - z) : ℝ) : ℂ)) * ((F (y, z) : ℝ) : ℂ) with hG
  set H : E3 → E3 → ℂ := fun y z => chiA A χ y * chiA A χ z
      * Complex.exp (Complex.I * ((inner ℝ q (y - z) : ℝ) : ℂ)) * ((F (y, z) : ℝ) : ℂ) with hH
  have hα : (∫ y in A, ∫ z in A, G y z) = ∫ y : E3, ∫ z : E3, H y z := by
    rw [← integral_indicator hA]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    by_cases hy : y ∈ A
    · rw [Set.indicator_of_mem hy, ← integral_indicator hA]
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      by_cases hz : z ∈ A
      · rw [Set.indicator_of_mem hz, hG, hH]
        dsimp only
        rw [chiA_of_mem hy, chiA_of_mem hz]
      · rw [Set.indicator_of_notMem hz, hH]
        dsimp only
        rw [chiA_of_notMem hz]
        simp
    · rw [Set.indicator_of_notMem hy]
      simp [hH, chiA_of_notMem hy]
  have hβpt : ∀ y z : E3, H y z = Aw A χ q y * (Bw A χ q z * slice F η y z) := by
    intro y z
    by_cases hy : y ∈ A
    · by_cases hz : z ∈ A
      · rw [hH]
        dsimp only
        rw [Aw_eq_chiA q y, Bw_eq_chiA q z, chiA_of_mem hy, chiA_of_mem hz, slice_apply,
          hη1 z hz, exp_inner_sub q y z]
        push_cast
        ring
      · rw [hH]
        dsimp only
        rw [Aw_eq_chiA q y, Bw_eq_chiA q z, chiA_of_mem hy, chiA_of_notMem hz]
        push_cast
        ring
    · rw [hH]
      dsimp only
      rw [Aw_eq_chiA q y, chiA_of_notMem hy]
      push_cast
      ring
  have hβ : ∀ y : E3, (∫ z : E3, H y z)
      = Aw A χ q y * ∫ z : E3, Bw A χ q z * slice F η y z := by
    intro y
    rw [show (∫ z : E3, H y z)
        = ∫ z : E3, Aw A χ q y * (Bw A χ q z * slice F η y z) from
      integral_congr_ae (Filter.Eventually.of_forall (hβpt y))]
    exact integral_const_mul _ _
  have hγ : ∀ y : E3, (∫ z : E3, Bw A χ q z * slice F η y z)
      = ∫ p : E3, AFun A χ q p * 𝓕 (slice F η y) (-p) := fun y =>
    Commons.Analysis.Fourier.integral_mul_eq_integral_fourier_mul
      (integrable_Bw (A := A) (χ := χ) (q := q) hA hχc hχs)
      (integrable_slice hF hη hηs y)
      (memLp_two_Bw (A := A) (χ := χ) (q := q) hA hχc hχs)
      (memLp_two_slice hF hη hηs y)
  have h1 : (∫ y : E3, ∫ z : E3, H y z)
      = ∫ y : E3, Aw A χ q y * (∫ p : E3, AFun A χ q p * 𝓕 (slice F η y) (-p)) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    dsimp only
    rw [hβ y, hγ y]
  have h2 : (∫ y : E3, Aw A χ q y * (∫ p : E3, AFun A χ q p * 𝓕 (slice F η y) (-p)))
      = ∫ y : E3, ∫ p : E3, Aw A χ q y * (AFun A χ q p * 𝓕 (slice F η y) (-p)) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    exact (integral_const_mul (Aw A χ q y) _).symm
  have h3 : (∫ y : E3, ∫ p : E3, Aw A χ q y * (AFun A χ q p * 𝓕 (slice F η y) (-p)))
      = ∫ p : E3, ∫ y : E3, Aw A χ q y * (AFun A χ q p * 𝓕 (slice F η y) (-p)) :=
    integral_integral_swap (f := fun y p : E3 =>
      Aw A χ q y * (AFun A χ q p * 𝓕 (slice F η y) (-p)))
      (integrable_fubini_integrand hχc hA hχs hF hη hηs hD0 hD hIntF q)
  have h4 : (∫ p : E3, ∫ y : E3, Aw A χ q y * (AFun A χ q p * 𝓕 (slice F η y) (-p)))
      = ∫ p : E3, AFun A χ q p * UFun A χ F η q p := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    dsimp only
    unfold UFun
    rw [show (∫ y : E3, Aw A χ q y * (AFun A χ q p * 𝓕 (slice F η y) (-p)))
        = ∫ y : E3, AFun A χ q p * (Aw A χ q y * 𝓕 (slice F η y) (-p)) from
      integral_congr_ae (Filter.Eventually.of_forall fun y => by ring)]
    exact integral_const_mul _ _
  exact hα.trans (h1.trans (h2.trans (h3.trans h4)))

end DiagFinal

theorem wMR_diagFourier {ℓ : ℝ} {A : Set (EuclideanSpace ℝ (Fin 3))}
    (hA : MeasurableSet A) (hℓ : 0 < ℓ)
    (hAc : ∀ z ∈ A, ∀ j : Fin 3, -(ℓ/2) ≤ z j ∧ z j ≤ ℓ/2)
    {χ : EuclideanSpace ℝ (Fin 3) → ℝ} (hχc : Continuous χ) (hχs : HasCompactSupport χ)
    {F : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) → ℝ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    MeasureTheory.MemLp
      (fun q : EuclideanSpace ℝ (Fin 3) =>
        ∫ y in A, ∫ z in A, (χ y : ℂ) * (χ z : ℂ)
          * Complex.exp (Complex.I * ((inner ℝ q (y - z) : ℝ) : ℂ))
          * ((F (y, z) : ℝ) : ℂ))
      1 (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) := by
  obtain ⟨C, D, Ms, hC0, hD0, hMs0, hCb, hDb, hIntF, hCInt, hSup⟩ :=
    kernel_bounds_ext hℓ hAc hF
  have hηc : ContDiff ℝ (⊤ : ℕ∞) (etaCut ℓ) := contDiff_etaCut ℓ
  have hηs : HasCompactSupport (etaCut ℓ) := hasCompactSupport_etaCut ℓ
  have hη1 : ∀ z ∈ A, etaCut ℓ z = 1 := fun z hz =>
    etaCut_eq_one hℓ.le (mem_DCube_iff.mpr (hAc z hz))
  have hχ2int : Integrable (fun z : E3 => ‖χ z‖ ^ 2) (volume : Measure E3) :=
    (memLp_two_iff_integrable_sq_norm hχc.aestronglyMeasurable).mp
      (hχc.memLp_of_hasCompactSupport hχs)
  set Gχ : ℝ := ∫ z : E3, ‖χ z‖ ^ 2 with hGχ
  have hGχ0 : 0 ≤ Gχ := by
    rw [hGχ]
    exact integral_nonneg fun z => by positivity
  set W : ℝ := ∫ p : E3, cfw p with hW
  have hW0 : 0 ≤ W := by
    rw [hW]
    exact integral_nonneg fun p => cfw_nonneg p
  have hAESM : AEStronglyMeasurable (fun q : E3 => ∫ y in A, ∫ z in A, (χ y : ℂ) * (χ z : ℂ)
      * Complex.exp (Complex.I * ((inner ℝ q (y - z) : ℝ) : ℂ)) * ((F (y, z) : ℝ) : ℂ))
      (volume : Measure E3) := by
    have h1 : AEStronglyMeasurable
        (fun q : E3 => ∫ p : E3, AFun A χ q p * UFun A χ F (etaCut ℓ) q p)
        (volume : Measure E3) :=
      ((aesm_AFun_joint hχc hA).mul
        (aesm_UFun_joint hχc hA hF.continuous hηc.continuous)).integral_prod_right'
    refine h1.congr (Filter.Eventually.of_forall fun q => ?_)
    dsimp only
    exact (diag_repr q hA hχc hχs hF hηc hη1 hηs hD0 hDb hIntF).symm
  rw [memLp_one_iff_integrable]
  refine ⟨hAESM, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  -- the AM–GM, in `ENNReal`
  have hamgm : ∀ a b : ℂ, ∀ p : E3, ‖a‖ₑ * ‖b‖ₑ
      ≤ ENNReal.ofReal (cfw p) * ‖a‖ₑ ^ 2 + ENNReal.ofReal (dfw p) * ‖b‖ₑ ^ 2 := by
    intro a b p
    have ha : (0 : ℝ) ≤ ‖a‖ := norm_nonneg _
    have hb : (0 : ℝ) ≤ ‖b‖ := norm_nonneg _
    have h1 : ‖a‖ₑ * ‖b‖ₑ = ENNReal.ofReal (‖a‖ * ‖b‖) := by
      rw [ENNReal.ofReal_mul ha]
      simp
    have h2 : ENNReal.ofReal (cfw p * ‖a‖ ^ 2 + dfw p * ‖b‖ ^ 2)
        = ENNReal.ofReal (cfw p) * ‖a‖ₑ ^ 2 + ENNReal.ofReal (dfw p) * ‖b‖ₑ ^ 2 := by
      rw [ENNReal.ofReal_add (mul_nonneg (cfw_nonneg p) (sq_nonneg _))
          (mul_nonneg (dfw_nonneg p) (sq_nonneg _)),
        ENNReal.ofReal_mul (cfw_nonneg p), ENNReal.ofReal_mul (dfw_nonneg p),
        ENNReal.ofReal_pow ha, ENNReal.ofReal_pow hb]
      simp
    rw [h1, ← h2]
    exact ENNReal.ofReal_le_ofReal (amgm_weight ha hb p)
  -- the pointwise representation bound
  have hrepr : ∀ q : E3,
      ‖(∫ y in A, ∫ z in A, (χ y : ℂ) * (χ z : ℂ)
        * Complex.exp (Complex.I * ((inner ℝ q (y - z) : ℝ) : ℂ)) * ((F (y, z) : ℝ) : ℂ))‖ₑ
      ≤ ∫⁻ p : E3, ‖AFun A χ q p‖ₑ * ‖UFun A χ F (etaCut ℓ) q p‖ₑ := by
    intro q
    rw [diag_repr q hA hχc hχs hF hηc hη1 hηs hD0 hDb hIntF]
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
    refine lintegral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    dsimp only
    rw [enorm_mul]
  have hAmgmInt : ∫⁻ q : E3,
      ‖(∫ y in A, ∫ z in A, (χ y : ℂ) * (χ z : ℂ)
        * Complex.exp (Complex.I * ((inner ℝ q (y - z) : ℝ) : ℂ)) * ((F (y, z) : ℝ) : ℂ))‖ₑ
      ≤ ∫⁻ q : E3, ∫⁻ p : E3, (ENNReal.ofReal (cfw p) * ‖AFun A χ q p‖ₑ ^ 2
          + ENNReal.ofReal (dfw p) * ‖UFun A χ F (etaCut ℓ) q p‖ₑ ^ 2) := by
    refine lintegral_mono fun q => (hrepr q).trans ?_
    exact lintegral_mono fun p =>
      hamgm (AFun A χ q p) (UFun A χ F (etaCut ℓ) q p) p
  have hswap : (∫⁻ q : E3, ∫⁻ p : E3, (ENNReal.ofReal (cfw p) * ‖AFun A χ q p‖ₑ ^ 2
          + ENNReal.ofReal (dfw p) * ‖UFun A χ F (etaCut ℓ) q p‖ₑ ^ 2))
      = ∫⁻ p : E3, ∫⁻ q : E3, (ENNReal.ofReal (cfw p) * ‖AFun A χ q p‖ₑ ^ 2
          + ENNReal.ofReal (dfw p) * ‖UFun A χ F (etaCut ℓ) q p‖ₑ ^ 2) := by
    refine lintegral_lintegral_swap ?_
    exact (((continuous_cfw.measurable.ennreal_ofReal).comp measurable_snd).aemeasurable.mul
        ((aesm_AFun_joint hχc hA).enorm.pow_const 2)).add
      (((continuous_dfw.measurable.ennreal_ofReal).comp measurable_snd).aemeasurable.mul
        ((aesm_UFun_joint hχc hA hF.continuous hηc.continuous).enorm.pow_const 2))
  have hAEmul : ∀ p : E3, AEMeasurable
      (fun q : E3 => ENNReal.ofReal (cfw p) * ‖AFun A χ q p‖ₑ ^ 2) (volume : Measure E3) := by
    intro p
    have hcont : Continuous fun q : E3 => AFun A χ q p := by
      rw [show (fun q : E3 => AFun A χ q p)
          = fun q => Submission.BoseGases.kinFT (fun z => Bw A χ ((2 * Real.pi) • p) z) q from
        funext fun q => AFun_eq_kinFT q p]
      exact Work.BoseKinLoc.Momentum.continuous_kinFT_of_integrable
        (integrable_Bw (A := A) (χ := χ) (q := (2 * Real.pi) • p) hA hχc hχs)
    exact aemeasurable_const.mul ((hcont.measurable.enorm.pow_const 2).aemeasurable)
  have hsplit : (∫⁻ p : E3, ∫⁻ q : E3, (ENNReal.ofReal (cfw p) * ‖AFun A χ q p‖ₑ ^ 2
          + ENNReal.ofReal (dfw p) * ‖UFun A χ F (etaCut ℓ) q p‖ₑ ^ 2))
      = ∫⁻ p : E3, (ENNReal.ofReal (cfw p) * (∫⁻ q : E3, ‖AFun A χ q p‖ₑ ^ 2)
          + ENNReal.ofReal (dfw p) * (∫⁻ q : E3, ‖UFun A χ F (etaCut ℓ) q p‖ₑ ^ 2)) := by
    refine lintegral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    dsimp only
    rw [lintegral_add_left' (hAEmul p), lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hmeas1 : AEMeasurable (fun p : E3 => ENNReal.ofReal (cfw p)
      * (∫⁻ q : E3, ‖AFun A χ q p‖ₑ ^ 2)) (volume : Measure E3) := by
    have h0 : Measurable fun p : E3 => ENNReal.ofReal (cfw p)
        * ENNReal.ofReal ((2 * Real.pi) ^ 3 * ∫ z : E3, ‖chiA A χ z‖ ^ 2) :=
      (continuous_cfw.measurable.ennreal_ofReal).mul measurable_const
    refine h0.aemeasurable.congr (Filter.Eventually.of_forall fun p => ?_)
    dsimp only
    exact congrArg (fun t => ENNReal.ofReal (cfw p) * t)
      (AFun_lintegral_sq hA hχc hχs p).symm
  -- term 1
  have hK1le : ENNReal.ofReal ((2 * Real.pi) ^ 3 * ∫ z : E3, ‖chiA A χ z‖ ^ 2)
      ≤ ENNReal.ofReal ((2 * Real.pi) ^ 3 * Gχ) := by
    refine ENNReal.ofReal_le_ofReal ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [hGχ]
    refine integral_mono ?_ hχ2int fun z => ?_
    · refine Integrable.mono' hχ2int ((measurable_chiA hχc hA).norm.pow_const 2).aestronglyMeasurable ?_
      filter_upwards with z
      rw [Real.norm_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_chiA_le z) 2
    · exact pow_le_pow_left₀ (norm_nonneg _) (norm_chiA_le z) 2
  have hT1 : ∫⁻ p : E3, ENNReal.ofReal (cfw p) * (∫⁻ q : E3, ‖AFun A χ q p‖ₑ ^ 2)
      ≤ ENNReal.ofReal W * ENNReal.ofReal ((2 * Real.pi) ^ 3 * Gχ) := by
    rw [show (∫⁻ p : E3, ENNReal.ofReal (cfw p) * (∫⁻ q : E3, ‖AFun A χ q p‖ₑ ^ 2))
        = ∫⁻ p : E3, ENNReal.ofReal (cfw p)
          * ENNReal.ofReal ((2 * Real.pi) ^ 3 * ∫ z : E3, ‖chiA A χ z‖ ^ 2) from
      lintegral_congr_ae (Filter.Eventually.of_forall fun p => by
        dsimp only
        rw [AFun_lintegral_sq hA hχc hχs p])]
    rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,
      ← ofReal_integral_eq_lintegral_ofReal integrable_cfw
        (Filter.Eventually.of_forall cfw_nonneg), ← hW]
    exact mul_le_mul_of_nonneg_left hK1le (by positivity)
  -- term 2
  have hint : ∀ p : E3, Integrable (fun y : E3 => ‖chiA A χ y‖ ^ 2
      * ‖𝓕 (slice F (etaCut ℓ) y) (-p)‖ ^ 2) (volume : Measure E3) := by
    intro p
    refine Integrable.mono' (hχ2int.mul_const (Ms ^ 2))
      (((measurable_chiA hχc hA).norm.pow_const 2).aestronglyMeasurable.mul
        ((((aesm_sliceFourier_fst (F := F) (η := etaCut ℓ) hF.continuous hηc.continuous
          p).norm).aemeasurable.pow_const 2).aestronglyMeasurable)) ?_
    filter_upwards with y
    rw [Real.norm_of_nonneg (by positivity)]
    by_cases hy : y ∈ A
    · exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (norm_chiA_le y) 2)
        (pow_le_pow_left₀ (norm_nonneg _) (hSup y hy (-p)) 2) (by positivity) (by positivity)
    · rw [chiA_of_notMem hy]
      simp only [norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), ENNReal.ofReal_zero,
        zero_mul]
      positivity
  have henorm_sq : ∀ z : ℂ, ‖z‖ₑ ^ 2 = ENNReal.ofReal (‖z‖ ^ 2) := by
    intro z
    have h1 : ‖z‖ₑ = ENNReal.ofReal ‖z‖ :=
      (enorm_eq_nnnorm z).trans (ENNReal.coe_nnreal_eq ‖z‖₊)
    rw [h1, ← ENNReal.ofReal_pow (norm_nonneg z)]
  have hfac : ∀ p y : E3, ENNReal.ofReal (‖chiA A χ y‖ ^ 2)
        * ‖𝓕 (slice F (etaCut ℓ) y) (-p)‖ₑ ^ 2
      = ENNReal.ofReal (‖chiA A χ y‖ ^ 2 * ‖𝓕 (slice F (etaCut ℓ) y) (-p)‖ ^ 2) := by
    intro p y
    rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ ‖chiA A χ y‖ ^ 2),
      henorm_sq (𝓕 (slice F (etaCut ℓ) y) (-p))]
  have hK2val : ∀ p : E3, ENNReal.ofReal ((2 * Real.pi) ^ 3
        * ∫ y : E3, ‖chiA A χ y‖ ^ 2 * ‖𝓕 (slice F (etaCut ℓ) y) (-p)‖ ^ 2)
      = ENNReal.ofReal ((2 * Real.pi) ^ 3)
        * ∫⁻ y : E3, ENNReal.ofReal (‖chiA A χ y‖ ^ 2)
          * ‖𝓕 (slice F (etaCut ℓ) y) (-p)‖ₑ ^ 2 := by
    intro p
    rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (2 * Real.pi) ^ 3)]
    congr 1
    rw [lintegral_congr_ae (Filter.Eventually.of_forall (hfac p)),
      ← ofReal_integral_eq_lintegral_ofReal (hint p)
        (Filter.Eventually.of_forall fun y => by positivity)]
  have hT2a : ∀ y ∈ A, ∫⁻ p : E3, ENNReal.ofReal (dfw p)
        * ‖𝓕 (slice F (etaCut ℓ) y) (-p)‖ₑ ^ 2 ≤ ENNReal.ofReal (C / 2) := by
    intro y hy
    have hpt : ∀ p : E3, ENNReal.ofReal (dfw p) * ‖𝓕 (slice F (etaCut ℓ) y) (-p)‖ₑ ^ 2
        = ENNReal.ofReal (dfw p * ‖𝓕 (slice F (etaCut ℓ) y) (-p)‖ ^ 2) := by
      intro p
      rw [ENNReal.ofReal_mul (dfw_nonneg p), ENNReal.ofReal_pow (norm_nonneg _)]
      simp
    have hint2 : Integrable (fun p : E3 => dfw p * ‖𝓕 (slice F (etaCut ℓ) y) (-p)‖ ^ 2)
        (volume : Measure E3) := by
      unfold dfw
      refine (((hCInt y hy).const_mul (1 / 2)).comp_smul (R := (-1 : ℝ))
        (by norm_num)).congr ?_
      filter_upwards with p
      have h1 : (-1 : ℝ) • p = -p := by simp
      rw [h1, norm_neg]
      ring
    calc ∫⁻ p : E3, ENNReal.ofReal (dfw p) * ‖𝓕 (slice F (etaCut ℓ) y) (-p)‖ₑ ^ 2
        = ENNReal.ofReal (∫ p : E3, dfw p * ‖𝓕 (slice F (etaCut ℓ) y) (-p)‖ ^ 2) := by
          rw [lintegral_congr_ae (Filter.Eventually.of_forall hpt),
            ← ofReal_integral_eq_lintegral_ofReal hint2
              (Filter.Eventually.of_forall fun p => by unfold dfw; positivity)]
      _ ≤ ENNReal.ofReal (C / 2) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have hsub : (∫ p : E3, (1 + ‖p‖ ^ 2) ^ 2 * ‖𝓕 (slice F (etaCut ℓ) y) (-p)‖ ^ 2)
              = ∫ p : E3, (1 + ‖p‖ ^ 2) ^ 2 * ‖𝓕 (slice F (etaCut ℓ) y) p‖ ^ 2 := by
            have hg := integral_neg_comp_eq (fun ξ : E3 =>
              (1 + ‖ξ‖ ^ 2) ^ 2 * ‖𝓕 (slice F (etaCut ℓ) y) ξ‖ ^ 2)
            simpa [norm_neg] using hg
          have hsplit2 : (∫ p : E3, dfw p * ‖𝓕 (slice F (etaCut ℓ) y) (-p)‖ ^ 2)
              = (1 / 2) * ∫ p : E3, (1 + ‖p‖ ^ 2) ^ 2
                  * ‖𝓕 (slice F (etaCut ℓ) y) (-p)‖ ^ 2 := by
            unfold dfw
            rw [show (∫ p : E3, (1 / 2) * (1 + ‖p‖ ^ 2) ^ 2
                  * ‖𝓕 (slice F (etaCut ℓ) y) (-p)‖ ^ 2)
                = ∫ p : E3, (1 / 2) * ((1 + ‖p‖ ^ 2) ^ 2
                  * ‖𝓕 (slice F (etaCut ℓ) y) (-p)‖ ^ 2) from
              integral_congr_ae (Filter.Eventually.of_forall fun p => by ring),
              integral_const_mul]
          rw [hsplit2, hsub]
          have hC := hCb y hy
          linarith
  have hT2 : ∫⁻ p : E3, ENNReal.ofReal (dfw p)
        * ENNReal.ofReal ((2 * Real.pi) ^ 3
          * ∫ y : E3, ‖chiA A χ y‖ ^ 2 * ‖𝓕 (slice F (etaCut ℓ) y) (-p)‖ ^ 2)
      ≤ ENNReal.ofReal ((2 * Real.pi) ^ 3 * (C / 2) * Gχ) := by
    have hswap2 : (∫⁻ p : E3, ENNReal.ofReal (dfw p)
          * ENNReal.ofReal ((2 * Real.pi) ^ 3
            * ∫ y : E3, ‖chiA A χ y‖ ^ 2 * ‖𝓕 (slice F (etaCut ℓ) y) (-p)‖ ^ 2))
        = ENNReal.ofReal ((2 * Real.pi) ^ 3) * (∫⁻ p : E3, ENNReal.ofReal (dfw p)
            * ∫⁻ y : E3, ENNReal.ofReal (‖chiA A χ y‖ ^ 2)
              * ‖𝓕 (slice F (etaCut ℓ) y) (-p)‖ₑ ^ 2) := by
      rw [show (∫⁻ p : E3, ENNReal.ofReal (dfw p)
            * ENNReal.ofReal ((2 * Real.pi) ^ 3
              * ∫ y : E3, ‖chiA A χ y‖ ^ 2 * ‖𝓕 (slice F (etaCut ℓ) y) (-p)‖ ^ 2))
          = ∫⁻ p : E3, ENNReal.ofReal ((2 * Real.pi) ^ 3) * (ENNReal.ofReal (dfw p)
              * ∫⁻ y : E3, ENNReal.ofReal (‖chiA A χ y‖ ^ 2)
                * ‖𝓕 (slice F (etaCut ℓ) y) (-p)‖ₑ ^ 2) from by
        refine lintegral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
        dsimp only
        rw [hK2val p]
        ring]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    have hswap3 : (∫⁻ p : E3, ENNReal.ofReal (dfw p)
          * ∫⁻ y : E3, ENNReal.ofReal (‖chiA A χ y‖ ^ 2)
            * ‖𝓕 (slice F (etaCut ℓ) y) (-p)‖ₑ ^ 2)
        = ∫⁻ y : E3, ∫⁻ p : E3, ENNReal.ofReal (dfw p)
            * (ENNReal.ofReal (‖chiA A χ y‖ ^ 2)
              * ‖𝓕 (slice F (etaCut ℓ) y) (-p)‖ₑ ^ 2) := by
      rw [show (∫⁻ p : E3, ENNReal.ofReal (dfw p)
            * ∫⁻ y : E3, ENNReal.ofReal (‖chiA A χ y‖ ^ 2)
              * ‖𝓕 (slice F (etaCut ℓ) y) (-p)‖ₑ ^ 2)
          = ∫⁻ p : E3, ∫⁻ y : E3, ENNReal.ofReal (dfw p)
              * (ENNReal.ofReal (‖chiA A χ y‖ ^ 2)
                * ‖𝓕 (slice F (etaCut ℓ) y) (-p)‖ₑ ^ 2) from by
        refine lintegral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
        dsimp only
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]]
      refine lintegral_lintegral_swap ?_
      have h1 : AEMeasurable (fun w : E3 × E3 => ENNReal.ofReal (dfw w.1))
          (volume.prod volume) :=
        ((continuous_dfw.measurable.ennreal_ofReal).comp measurable_fst).aemeasurable
      have h2 : AEMeasurable (fun w : E3 × E3 => ENNReal.ofReal (‖chiA A χ w.2‖ ^ 2))
          (volume.prod volume) :=
        (((measurable_chiA hχc hA).comp measurable_snd).norm.pow_const 2).aemeasurable.ennreal_ofReal
      have h3 : AEMeasurable (fun w : E3 × E3 => ‖𝓕 (slice F (etaCut ℓ) w.2) (-w.1)‖ₑ ^ 2)
          (volume.prod volume) :=
        (aesm_sliceFourier_swap (F := F) (η := etaCut ℓ) hF.continuous
          hηc.continuous).enorm.pow_const 2
      exact h1.mul (h2.mul h3)
    have hswap4 : (∫⁻ y : E3, ∫⁻ p : E3, ENNReal.ofReal (dfw p)
          * (ENNReal.ofReal (‖chiA A χ y‖ ^ 2)
            * ‖𝓕 (slice F (etaCut ℓ) y) (-p)‖ₑ ^ 2))
        = ∫⁻ y : E3, ENNReal.ofReal (‖chiA A χ y‖ ^ 2)
            * ∫⁻ p : E3, ENNReal.ofReal (dfw p) * ‖𝓕 (slice F (etaCut ℓ) y) (-p)‖ₑ ^ 2 := by
      refine lintegral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      dsimp only
      rw [show (∫⁻ p : E3, ENNReal.ofReal (dfw p) * (ENNReal.ofReal (‖chiA A χ y‖ ^ 2)
              * ‖𝓕 (slice F (etaCut ℓ) y) (-p)‖ₑ ^ 2))
          = ∫⁻ p : E3, ENNReal.ofReal (‖chiA A χ y‖ ^ 2) * (ENNReal.ofReal (dfw p)
              * ‖𝓕 (slice F (etaCut ℓ) y) (-p)‖ₑ ^ 2) from
        lintegral_congr_ae (Filter.Eventually.of_forall fun p => by ring)]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    have hbound : (∫⁻ y : E3, ENNReal.ofReal (‖chiA A χ y‖ ^ 2)
          * ∫⁻ p : E3, ENNReal.ofReal (dfw p) * ‖𝓕 (slice F (etaCut ℓ) y) (-p)‖ₑ ^ 2)
        ≤ ∫⁻ y : E3, ENNReal.ofReal (‖chiA A χ y‖ ^ 2) * ENNReal.ofReal (C / 2) := by
      refine lintegral_mono fun y => ?_
      by_cases hy : y ∈ A
      · exact mul_le_mul_of_nonneg_left (hT2a y hy) (by positivity)
      · have h0 : ENNReal.ofReal (‖chiA A χ y‖ ^ 2) = 0 := by
          rw [chiA_of_notMem hy]
          simp
        rw [h0, zero_mul]
        exact zero_le
    have hbound2 : (∫⁻ y : E3, ENNReal.ofReal (‖chiA A χ y‖ ^ 2) * ENNReal.ofReal (C / 2))
        ≤ ENNReal.ofReal (C / 2) * ENNReal.ofReal Gχ := by
      rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,
        mul_comm (ENNReal.ofReal (C / 2)) (ENNReal.ofReal Gχ)]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      have h1 : (∫⁻ a : E3, ENNReal.ofReal (‖chiA A χ a‖ ^ 2))
          ≤ ∫⁻ a : E3, ENNReal.ofReal (‖χ a‖ ^ 2) :=
        lintegral_mono fun y => ENNReal.ofReal_le_ofReal
          (pow_le_pow_left₀ (norm_nonneg _) (norm_chiA_le y) 2)
      rw [← ofReal_integral_eq_lintegral_ofReal hχ2int
        (Filter.Eventually.of_forall fun y => by positivity), ← hGχ] at h1
      exact h1
    calc ∫⁻ p : E3, ENNReal.ofReal (dfw p)
          * ENNReal.ofReal ((2 * Real.pi) ^ 3
            * ∫ y : E3, ‖chiA A χ y‖ ^ 2 * ‖𝓕 (slice F (etaCut ℓ) y) (-p)‖ ^ 2)
        = ENNReal.ofReal ((2 * Real.pi) ^ 3) * (∫⁻ p : E3, ENNReal.ofReal (dfw p)
            * ∫⁻ y : E3, ENNReal.ofReal (‖chiA A χ y‖ ^ 2)
              * ‖𝓕 (slice F (etaCut ℓ) y) (-p)‖ₑ ^ 2) := hswap2
      _ = ENNReal.ofReal ((2 * Real.pi) ^ 3) * ∫⁻ y : E3, ∫⁻ p : E3, ENNReal.ofReal (dfw p)
            * (ENNReal.ofReal (‖chiA A χ y‖ ^ 2)
              * ‖𝓕 (slice F (etaCut ℓ) y) (-p)‖ₑ ^ 2) := by rw [hswap3]
      _ = ENNReal.ofReal ((2 * Real.pi) ^ 3) * (∫⁻ y : E3, ENNReal.ofReal (‖chiA A χ y‖ ^ 2)
            * ∫⁻ p : E3, ENNReal.ofReal (dfw p) * ‖𝓕 (slice F (etaCut ℓ) y) (-p)‖ₑ ^ 2) := by
          rw [hswap4]
      _ ≤ ENNReal.ofReal ((2 * Real.pi) ^ 3) * (∫⁻ y : E3, ENNReal.ofReal (‖chiA A χ y‖ ^ 2)
            * ENNReal.ofReal (C / 2)) :=
          mul_le_mul_of_nonneg_left hbound (by positivity)
      _ ≤ ENNReal.ofReal ((2 * Real.pi) ^ 3) * (ENNReal.ofReal (C / 2) * ENNReal.ofReal Gχ) :=
          mul_le_mul_of_nonneg_left hbound2 (by positivity)
      _ = ENNReal.ofReal ((2 * Real.pi) ^ 3 * (C / 2) * Gχ) := by
          rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ C / 2),
            ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (2 * Real.pi) ^ 3)]
          congr 1
          ring
  -- the final chain
  have hmain : ∫⁻ q : E3,
      ‖(∫ y in A, ∫ z in A, (χ y : ℂ) * (χ z : ℂ)
        * Complex.exp (Complex.I * ((inner ℝ q (y - z) : ℝ) : ℂ)) * ((F (y, z) : ℝ) : ℂ))‖ₑ
      ≤ ENNReal.ofReal (W * ((2 * Real.pi) ^ 3 * Gχ) + (2 * Real.pi) ^ 3 * (C / 2) * Gχ) := by
    calc ∫⁻ q : E3,
          ‖(∫ y in A, ∫ z in A, (χ y : ℂ) * (χ z : ℂ)
            * Complex.exp (Complex.I * ((inner ℝ q (y - z) : ℝ) : ℂ))
            * ((F (y, z) : ℝ) : ℂ))‖ₑ
        ≤ ∫⁻ q : E3, ∫⁻ p : E3, (ENNReal.ofReal (cfw p) * ‖AFun A χ q p‖ₑ ^ 2
            + ENNReal.ofReal (dfw p) * ‖UFun A χ F (etaCut ℓ) q p‖ₑ ^ 2) := hAmgmInt
      _ = ∫⁻ p : E3, ∫⁻ q : E3, (ENNReal.ofReal (cfw p) * ‖AFun A χ q p‖ₑ ^ 2
            + ENNReal.ofReal (dfw p) * ‖UFun A χ F (etaCut ℓ) q p‖ₑ ^ 2) := hswap
      _ = ∫⁻ p : E3, (ENNReal.ofReal (cfw p) * (∫⁻ q : E3, ‖AFun A χ q p‖ₑ ^ 2)
          + ENNReal.ofReal (dfw p) * (∫⁻ q : E3, ‖UFun A χ F (etaCut ℓ) q p‖ₑ ^ 2)) := hsplit
      _ = ∫⁻ p : E3, (ENNReal.ofReal (cfw p) * (∫⁻ q : E3, ‖AFun A χ q p‖ₑ ^ 2)
          + ENNReal.ofReal (dfw p)
            * ENNReal.ofReal ((2 * Real.pi) ^ 3
              * ∫ y : E3, ‖chiA A χ y‖ ^ 2 * ‖𝓕 (slice F (etaCut ℓ) y) (-p)‖ ^ 2)) := by
          refine lintegral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
          dsimp only
          rw [UFun_lintegral_sq (A := A) (χ := χ) (F := F) (η := etaCut ℓ) hA hχc hχs
            hF.continuous hηc.continuous hMs0 hSup p]
      _ = (∫⁻ p : E3, ENNReal.ofReal (cfw p) * (∫⁻ q : E3, ‖AFun A χ q p‖ₑ ^ 2))
          + ∫⁻ p : E3, ENNReal.ofReal (dfw p)
            * ENNReal.ofReal ((2 * Real.pi) ^ 3
              * ∫ y : E3, ‖chiA A χ y‖ ^ 2 * ‖𝓕 (slice F (etaCut ℓ) y) (-p)‖ ^ 2) := by
          rw [lintegral_add_left' hmeas1]
      _ ≤ ENNReal.ofReal W * ENNReal.ofReal ((2 * Real.pi) ^ 3 * Gχ)
          + ENNReal.ofReal ((2 * Real.pi) ^ 3 * (C / 2) * Gχ) := add_le_add hT1 hT2
      _ = ENNReal.ofReal (W * ((2 * Real.pi) ^ 3 * Gχ) + (2 * Real.pi) ^ 3 * (C / 2) * Gχ) := by
          rw [← ENNReal.ofReal_mul hW0,
            ← ENNReal.ofReal_add (mul_nonneg hW0 (by positivity)) (by positivity)]
  exact lt_of_le_of_lt hmain ENNReal.ofReal_lt_top

end Work.BoseFixB1B
