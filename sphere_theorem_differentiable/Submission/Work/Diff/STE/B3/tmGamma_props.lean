/-
# The coefficient family `tmGamma` of the tame transport: smoothness, symmetry, positivity, bounds

`Work.Diff.STE.B3.tmGamma D j a b ha hab h z p q` is the coefficient matrix of the *tame* transport
identity of Layer B3 (`Work.Diff.STE.B3.transport_deTurck_tame`): the inverse of the coordinate-frame
chart matrix of the section `h`, computed through the clamped inverse `tmInv` of the *nominal*
coordinate chart matrix built from the `g₀`-orthonormal-frame chart matrix `D.mat j h`.

This file proves `Work.Diff.STE.B3.tmGamma_props`: for a section `h` which is `λ`-bounded below and
`K`-bounded above by the background metric `g₀` and whose chart matrices have bounded first jets, the
family `tmGamma` is, on a ball strictly larger than the `2σ j`-ball of the B3 data, smooth,
symmetric, positive definite with a uniform constant, and it agrees on the `2σ j`-ball with the
honest inverse of the chart matrix of `h`.

The mathematical content is:

* on the `2σ j` ball the frame `D.e j ·` is `g₀`-orthonormal (`B3Data.heON`), so the ON-frame chart
  matrix `D.mat j h` is positive definite with eigenvalues in `[λ, K]` and invertible, and the
  *congruence* identity `Mf = Ff · Gf · Ffᵀ` (`Work.Diff.STE.B3.Mf_matrix_eq_of_target`) converts
  the nominal matrix `tmGK z (Mf z)` into the honest chart matrix `Gf` of `h`;
* every entrance in that identity is *open* (the chart target is open, and the invertibility of `Ff`
  persists on a neighbourhood, because the Gram determinant of the frame is `1` on the `2σ j` ball
  and continuous) — this is what produces the uniform ball of radius `2σ j + δ`;
* on that larger ball the inverse of the chart matrix is smooth (`Matrix.inv_def` = Cramer's rule,
  `ContDiffOn` away from `det = 0`), positive definite (`Matrix.PosDef.inv`) and its entries and
  quadratic form are uniformly bounded — the latter by compactness;
* the clamping window `[a,b]` is chosen (again by compactness of `det Gf`) so that the clamp is
  inactive on the ball, whence `tmInv` *is* the honest inverse there.
-/
import Mathlib
import Submission.Work.Diff.STE.B3.transport_tame_defs
import Submission.Work.Diff.STE.B3.TransportDefs
import Submission.Work.Diff.STE.B3.tmGK_eq_Gf
import Submission.Work.Diff.STE.B3.Mf_matrix_eq_of_target
import Submission.Work.Diff.STE.B3.chartMatOf_posDef
import Submission.Work.Diff.STE.B3.contDiffAt_inv_entry
import Submission.Work.Diff.STE.B3.quadForm_bounds
import Submission.Work.Diff.STE.B3.det_Mf_metric_ne_zero

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators Matrix
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.STE.B3

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

/-! ## 1. Elementary matrix facts -/

/-- The quadratic form of a real matrix, as a `dotProduct`. -/
private lemma star_dotProduct_mulVec_eq_sum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (ξ : Fin n → ℝ) :
    star ξ ⬝ᵥ (A.mulVec ξ) = ∑ p, ∑ q, A p q * ξ p * ξ q := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, star_trivial]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  ring

/-- The determinant, as a function of the entries of the matrix. -/
private lemma det_contDiff_fn {n : ℕ} :
    ContDiff ℝ (⊤ : ℕ∞) (fun A : Fin n → Fin n → ℝ => (Matrix.of A).det) := by
  have h : (fun A : Fin n → Fin n → ℝ => (Matrix.of A).det)
      = fun A => ∑ σ : Equiv.Perm (Fin n), (↑↑(Equiv.Perm.sign σ) : ℝ) * ∏ i, A (σ i) i := by
    funext A
    rw [Matrix.det_apply']
    simp only [Matrix.of_apply]
  rw [h]
  fun_prop

/-- `tmInv` is the honest inverse as soon as the determinant lies in the clamping window. -/
private lemma tmInv_eq_inv_of_det_mem {n : ℕ} (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.det ∈ Set.Icc a b) :
    tmInv a b ha hab A = A⁻¹ := by
  have h1 : ((⟨(b - a) / 2, b / 2, by linarith, by linarith⟩ :
      ContDiffBump ((a + b) / 2)) A.det) = 1 := by
    apply ContDiffBump.one_of_mem_closedBall
    rw [Metric.mem_closedBall, Real.dist_eq]
    rw [abs_sub_le_iff]
    exact ⟨by linarith [hA.2], by linarith [hA.1]⟩
  simp only [tmInv, tmClampBump]
  rw [h1]
  simp

/-- **The closed ball of radius `R + δ/2` is contained in the `δ`-thickening of the closed ball of
radius `R`**: radial projection. -/
private lemma closedBall_add_subset_thickening {k : ℕ} {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ) :
    Metric.closedBall (0 : Fin k → ℝ) (R + δ / 2) ⊆
      Metric.thickening δ (Metric.closedBall (0 : Fin k → ℝ) R) := by
  intro z hz
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hz
  rw [Metric.mem_thickening_iff]
  by_cases h : ‖z‖ ≤ R
  · exact ⟨z, by rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]; exact h, by simpa using hδ⟩
  · push Not at h
    have hzpos : 0 < ‖z‖ := lt_of_le_of_lt hR h
    refine ⟨(R / ‖z‖) • z, ?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg hR (norm_nonneg z)), div_mul_cancel₀ _ hzpos.ne']
    · rw [dist_eq_norm]
      have hsub : z - (R / ‖z‖) • z = (1 - R / ‖z‖) • z := by
        rw [sub_smul, one_smul]
      rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by
        rw [sub_nonneg, div_le_one hzpos]
        exact le_of_lt h), sub_mul, one_mul, div_mul_cancel₀ _ hzpos.ne']
      linarith

/-! ## 2. Smoothness of the chart matrix entries and of its determinant -/

/-- The preimage of the chart target under `flatToE` is open. -/
private lemma isOpen_flatToE_preimage_target (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (j : ι₀) :
    IsOpen (Work.Diff.STE.flatToE (I := I) (D.x₀ j) ⁻¹' (extChartAt I (D.x₀ j)).target) :=
  (isOpen_extChartAt_target (I := I) (D.x₀ j)).preimage
    ((Work.Diff.STE.contDiff_flatToE (I := I) (x₀ := D.x₀ j)).continuous)

/-- **The entries of the chart matrix of `h` in the chart of `x₀ j` are smooth in the flat
coordinate**, on the preimage of the chart target: `ChartData` composed with `flatToE`. -/
private lemma contDiffOn_Gf_entry (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M) h) (j : ι₀)
    (p q : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z => Gf (I := I) (M := M) D h j z p q)
      (Work.Diff.STE.flatToE (I := I) (D.x₀ j) ⁻¹' (extChartAt I (D.x₀ j)).target) := by
  have hmain : ContDiffOn ℝ (⊤ : ℕ∞) (fun y : E => Work.Diff.STE.D.chartMatOf
      (I := I) (M := M) h (D.x₀ j) y) (extChartAt I (D.x₀ j)).target := hsmooth (D.x₀ j)
  have hfl : ContDiffOn ℝ (⊤ : ℕ∞) (Work.Diff.STE.flatToE (I := I) (D.x₀ j))
      (Work.Diff.STE.flatToE (I := I) (D.x₀ j) ⁻¹' (extChartAt I (D.x₀ j)).target) :=
    (Work.Diff.STE.contDiff_flatToE (I := I) (x₀ := D.x₀ j)).contDiffOn.mono (Set.subset_univ _)
  have hcomp := hmain.comp hfl (fun z hz => hz)
  have h1 : ContDiffOn ℝ (⊤ : ℕ∞) (fun z => (Work.Diff.STE.D.chartMatOf
      (I := I) (M := M) h (D.x₀ j) (Work.Diff.STE.flatToE (I := I) (D.x₀ j) z)) p)
      (Work.Diff.STE.flatToE (I := I) (D.x₀ j) ⁻¹' (extChartAt I (D.x₀ j)).target) :=
    (contDiffOn_pi.mp hcomp) p
  have h2 := (contDiffOn_pi.mp h1) q
  simpa only [Gf, yf] using h2

/-- The determinant of the chart matrix of `h` is smooth in the flat coordinate near every point
whose flat coordinate lies in the chart target. -/
private lemma contDiffAt_det_Gf (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M) h) (j : ι₀)
    {z : Fin (Module.finrank ℝ E) → ℝ}
    (hz : Work.Diff.STE.flatToE (I := I) (D.x₀ j) z ∈ (extChartAt I (D.x₀ j)).target) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun w => (Matrix.of (Gf (I := I) (M := M) D h j w)).det) z := by
  have hmem : Work.Diff.STE.flatToE (I := I) (D.x₀ j) ⁻¹' (extChartAt I (D.x₀ j)).target
      ∈ 𝓝 z := (isOpen_flatToE_preimage_target (I := I) (M := M) D j).mem_nhds hz
  have hentry : ∀ p q, ContDiffAt ℝ (⊤ : ℕ∞) (fun w => Gf (I := I) (M := M) D h j w p q) z :=
    fun p q => (contDiffOn_Gf_entry (I := I) (M := M) D h hsmooth j p q).contDiffAt hmem
  have hA : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun w : Fin (Module.finrank ℝ E) → ℝ => Gf (I := I) (M := M) D h j w) z := by
    rw [contDiffAt_pi]
    intro p
    rw [contDiffAt_pi]
    intro q
    exact hentry p q
  exact (det_contDiff_fn (n := Module.finrank ℝ E)).contDiffAt.comp z hA

/-- **The chart matrix of `h` is symmetric** whenever `h` is. -/
private lemma transpose_Gf (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hsym : ∀ (x : M) (u v : TangentSpace I x), h x u v = h x v u) (j : ι₀)
    (z : Fin (Module.finrank ℝ E) → ℝ) :
    (Matrix.of (Gf (I := I) (M := M) D h j z)).transpose
      = Matrix.of (Gf (I := I) (M := M) D h j z) := by
  ext p q
  rw [Matrix.transpose_apply, Matrix.of_apply, Matrix.of_apply]
  show Gf (I := I) (M := M) D h j z q p = Gf (I := I) (M := M) D h j z p q
  rw [Gf, Work.Diff.STE.D.chartMatOf_apply, Work.Diff.STE.D.chartMatOf_apply, yf]
  exact hsym _ _ _

/-! ## 3. The region: the chart target and the invertibility of the frame matrix -/

/-- **The determinant of the frame matrix is nonzero** on the chart target whenever the ON-frame
chart matrix of the background metric is invertible there: the congruence identity
`Mf = Ff · Gf · Ffᵀ` (`Mf_matrix_eq_of_target`) turns the invertibility of the Gram matrix
into the invertibility of `Ff` because the background chart matrix has positive determinant. -/
private lemma det_Ff_ne_zero_of_region (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (j : ι₀) {z : Fin (Module.finrank ℝ E) → ℝ}
    (htgt : Work.Diff.STE.flatToE (I := I) (D.x₀ j) z ∈ (extChartAt I (D.x₀ j)).target)
    (hEM : (Matrix.of (Mf (I := I) (M := M) D g₀.inner j z)).det ≠ 0) :
    (Matrix.of (Ff (I := I) (M := M) D j z)).det ≠ 0 := by
  have hdetGf : 0 < (Matrix.of (Gf (I := I) (M := M) D g₀.inner j z)).det :=
    Matrix.PosDef.det_pos (chartMatOf_posDef (I := I) (M := M) g₀.inner (D.x₀ j)
      (fun x u v => g₀.symm x u v) (fun x v hv => g₀.pos x v hv) htgt)
  have hcong := Mf_matrix_eq_of_target (I := I) (M := M) D g₀.inner j z htgt
  have hdet := congrArg Matrix.det hcong
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at hdet
  intro h0
  exact hEM (by rw [hdet, h0]; ring)

/-- **The region of the B3 data**: a uniform ball strictly larger than the `2σ j`-ball on which the
flat coordinate stays in the chart target *and* the frame matrix is invertible. -/
private theorem exists_region (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ z : Fin (Module.finrank ℝ E) → ℝ,
      ‖z‖ ≤ 2 * D.σ j + δ₀ →
      (Work.Diff.STE.flatToE (I := I) (D.x₀ j) z ∈ (extChartAt I (D.x₀ j)).target ∧
        (Matrix.of (Ff (I := I) (M := M) D j z)).det ≠ 0) := by
  classical
  have hK : IsCompact (Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ j)) :=
    isCompact_closedBall _ _
  have hKU : Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ j) ⊆
      Work.Diff.STE.flatToE (I := I) (D.x₀ j) ⁻¹' (extChartAt I (D.x₀ j)).target := by
    intro z hz
    exact D.htarget j z (by rwa [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hz)
  obtain ⟨δ₁, hδ₁pos, hδ₁sub⟩ :=
    hK.exists_thickening_subset_open (isOpen_flatToE_preimage_target (I := I) (M := M) D j) hKU
  obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := det_Mf_metric_ne_zero (I := I) (M := M) (g₀ := g₀) D j
  refine ⟨min (δ₁ / 2) δ₂, lt_min (by linarith) hδ₂pos, fun z hz => ?_⟩
  have hz₁ : ‖z‖ ≤ 2 * D.σ j + δ₁ / 2 :=
    le_trans hz (by linarith [min_le_left (δ₁ / 2) δ₂])
  have hz₂ : ‖z‖ ≤ 2 * D.σ j + δ₂ :=
    le_trans hz (by linarith [min_le_right (δ₁ / 2) δ₂])
  have hσ : 0 ≤ 2 * D.σ j := by linarith [D.hσ j]
  have htgt : Work.Diff.STE.flatToE (I := I) (D.x₀ j) z ∈ (extChartAt I (D.x₀ j)).target :=
    hδ₁sub (closedBall_add_subset_thickening (k := Module.finrank ℝ E) hσ hδ₁pos
      (by rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]; exact hz₁))
  exact ⟨htgt, det_Ff_ne_zero_of_region (I := I) (M := M) D j htgt (hδ₂ z hz₂)⟩

/-! ## 4. The clamping window -/

/-- **The values of a positive continuous function on a compact ball are confined to an interval
`[a,b]` with `0 < a < b`.** -/
private lemma exists_det_range {k : ℕ} {R : ℝ} (hR : 0 ≤ R)
    (f : (Fin k → ℝ) → ℝ) (hcont : ContinuousOn f (Metric.closedBall 0 R))
    (hpos : ∀ z ∈ Metric.closedBall (0 : Fin k → ℝ) R, 0 < f z) :
    ∃ a b : ℝ, 0 < a ∧ a < b ∧
      ∀ z ∈ Metric.closedBall (0 : Fin k → ℝ) R, a ≤ f z ∧ f z ≤ b := by
  have hne : (Metric.closedBall (0 : Fin k → ℝ) R).Nonempty :=
    ⟨0, Metric.mem_closedBall_self hR⟩
  obtain ⟨z₁, hz₁, hmin⟩ := (isCompact_closedBall (0 : Fin k → ℝ) R).exists_isMinOn hne hcont
  obtain ⟨z₂, hz₂, hmax⟩ := (isCompact_closedBall (0 : Fin k → ℝ) R).exists_isMaxOn hne hcont
  refine ⟨f z₁ / 2, f z₂ + 1, by have h := hpos z₁ hz₁; linarith,
    by have h1 : 0 < f z₁ := hpos z₁ hz₁
       have h2 : f z₁ ≤ f z₂ := hmax hz₁
       linarith, fun z hz => ⟨?_, ?_⟩⟩
  · have h1 : 0 < f z₁ := hpos z₁ hz₁
    have h2 : f z₁ ≤ f z := hmin hz
    linarith
  · have h2 : f z ≤ f z₂ := hmax hz
    linarith

/-- A one-term bound for a finite sum of nonnegative terms. -/
private lemma le_sum_of_nonneg {n : ℕ} (f : Fin n → ℝ) (hf : ∀ i, 0 ≤ f i) (i : Fin n) :
    f i ≤ ∑ j, f j :=
  Finset.single_le_sum (fun j _ => hf j) (Finset.mem_univ i)

/-- One term of a triple finite sum of nonnegative terms is bounded by the whole sum. -/
private lemma le_nested_sum {n : ℕ} {f : Fin n → Fin n → Fin n → ℝ}
    (hf : ∀ i j k, 0 ≤ f i j k) (r p q : Fin n) :
    f r p q ≤ ∑ r', ∑ p', ∑ q', f r' p' q' := by
  refine le_trans (le_sum_of_nonneg (fun q' => f r p q') (fun q' => hf r p q') q) ?_
  refine le_trans (le_sum_of_nonneg (fun p' => ∑ q', f r p' q')
    (fun p' => Finset.sum_nonneg fun q' _ => hf r p' q') p) ?_
  exact le_sum_of_nonneg (fun r' => ∑ p', ∑ q', f r' p' q')
    (fun r' => Finset.sum_nonneg fun p' _ => Finset.sum_nonneg fun q' _ => hf r' p' q') r

/-- A finite sum of functions continuous at a point is continuous at that point. -/
private lemma continuousAt_finsetSum {ι X : Type*} [TopologicalSpace X] (s : Finset ι)
    {f : ι → X → ℝ} {x : X} (hf : ∀ i ∈ s, ContinuousAt (f i) x) :
    ContinuousAt (fun y => s.sum (fun i => f i y)) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using continuousAt_const
  | insert a s ha ih =>
      have hfun : (fun y : X => (insert a s).sum (fun i => f i y))
          = fun y => f a y + s.sum (fun i => f i y) := by
        funext y
        rw [Finset.sum_insert ha]
      rw [hfun]
      exact (hf a (Finset.mem_insert_self a s)).add
        (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- A finite sum of functions continuous at a point is continuous at that point (`univ` form). -/
private lemma continuousAt_sum_univ {ι X : Type*} [Fintype ι] [TopologicalSpace X]
    {f : ι → X → ℝ} {x : X} (hf : ∀ i, ContinuousAt (f i) x) :
    ContinuousAt (fun y => ∑ i, f i y) x := by
  have h := continuousAt_finsetSum (s := Finset.univ) (f := f) (fun i _ => hf i)
  simpa using h

/-! ## 5. The main theorem -/

theorem tmGamma_props
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (lam K : ℝ) (hlam : 0 < lam) (j : ι₀) :
    ∃ (δ : ℝ), 0 < δ ∧
      ∀ (h : Work.Diff.STE.Bil (I := I) (M := M))
        (hsym : ∀ (x : M) (u v : TangentSpace I x), h x u v = h x v u)
        (hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
        (hell : ∀ (x : M) (v : TangentSpace I x), lam * g₀.inner x v v ≤ h x v v)
        (hub : ∀ (x : M) (v : TangentSpace I x), h x v v ≤ K * g₀.inner x v v)
        (hjet : ∀ (i : ι₀) (c d r : Fin (Module.finrank ℝ E))
          (z : Fin (Module.finrank ℝ E) → ℝ), ‖z‖ ≤ 2 * D.σ i →
          |Work.Diff.STE.pdR r (D.mat i h c d) z| ≤ K),
      ∃ (a b : ℝ) (ha : 0 < a) (hab : a < b) (c₁ C₁ C₂ : ℝ),
        0 < c₁ ∧ 0 ≤ C₁ ∧ 0 ≤ C₂ ∧
        (∀ p q, ContDiffOn ℝ (⊤ : ℕ∞) (fun w => tmGamma (I := I) (M := M) D j a b ha hab h w p q)
          (Metric.ball 0 (2 * D.σ j + δ))) ∧
        (∀ z, ‖z‖ ≤ 2 * D.σ j + δ →
          (∀ p q, tmGamma (I := I) (M := M) D j a b ha hab h z p q
              = tmGamma (I := I) (M := M) D j a b ha hab h z q p) ∧
          (∀ ξ : Fin (Module.finrank ℝ E) → ℝ,
            c₁ * ∑ p, (ξ p) ^ 2 ≤ ∑ p, ∑ q,
              tmGamma (I := I) (M := M) D j a b ha hab h z p q * ξ p * ξ q) ∧
          (∀ p q, |tmGamma (I := I) (M := M) D j a b ha hab h z p q| ≤ C₁) ∧
          (∀ r p q, |Work.Diff.STE.pdR r
              (fun w => tmGamma (I := I) (M := M) D j a b ha hab h w p q) z| ≤ C₂)) ∧
        (∀ z, ‖z‖ ≤ 2 * D.σ j → ∀ p q,
          tmGamma (I := I) (M := M) D j a b ha hab h z p q
            = ((Matrix.of (fun i k => Work.Diff.STE.D.chartMatOf (I := I) (M := M) h (D.x₀ j)
                (yf (I := I) (M := M) D j z) i k))⁻¹) p q) := by
  classical
  obtain ⟨δ₀, hδ₀pos, hregion⟩ := exists_region (I := I) (M := M) (g₀ := g₀) D j
  refine ⟨δ₀ / 2, half_pos hδ₀pos, ?_⟩
  intro h hsym hsmooth hell hub hjet
  -- the section is positive definite
  have hpos : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < h x v v := by
    intro x v hv
    have h1 : lam * g₀.inner x v v ≤ h x v v := hell x v
    have h2 : 0 < lam * g₀.inner x v v := mul_pos hlam (g₀.pos x v hv)
    linarith
  -- the ball on which the constants are taken
  set Rb : ℝ := 2 * D.σ j + δ₀ with hRbdef
  have hRbnn : 0 ≤ Rb := by rw [hRbdef]; linarith [D.hσ j, hδ₀pos]
  have hmemR : ∀ z ∈ Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) Rb,
      Work.Diff.STE.flatToE (I := I) (D.x₀ j) z ∈ (extChartAt I (D.x₀ j)).target ∧
      (Matrix.of (Ff (I := I) (M := M) D j z)).det ≠ 0 := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hz
    exact hregion z (by rw [hRbdef] at hz; exact hz)
  -- positive definiteness of the chart matrix
  have hpd : ∀ z ∈ Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) Rb,
      (Matrix.of (Gf (I := I) (M := M) D h j z)).PosDef :=
    fun z hz => chartMatOf_posDef (I := I) (M := M) h (D.x₀ j) hsym hpos (hmemR z hz).1
  -- the clamping window
  have hdetcont : ContinuousOn (fun z => (Matrix.of (Gf (I := I) (M := M) D h j z)).det)
      (Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) Rb) := by
    intro z hz
    exact ((contDiffAt_det_Gf (I := I) (M := M) D h hsmooth j (hmemR z hz).1).continuousAt).continuousWithinAt
  have hdetpos : ∀ z ∈ Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) Rb,
      0 < (Matrix.of (Gf (I := I) (M := M) D h j z)).det :=
    fun z hz => Matrix.PosDef.det_pos (hpd z hz)
  obtain ⟨a, b, ha, hab, hdetrange⟩ := exists_det_range (k := Module.finrank ℝ E) hRbnn
    (fun z => (Matrix.of (Gf (I := I) (M := M) D h j z)).det) hdetcont hdetpos
  -- the identity on the region `‖z‖ ≤ 2σ + δ₀`
  have hident : ∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ ≤ 2 * D.σ j + δ₀ → ∀ p q,
      tmGamma (I := I) (M := M) D j a b ha hab h z p q
        = ((Matrix.of (Gf (I := I) (M := M) D h j z))⁻¹) p q := by
    intro z hz p q
    obtain ⟨htgt, hdetFf⟩ := hregion z hz
    have h1 := tmGK_eq_Gf (I := I) (M := M) D h j z htgt hdetFf
    have h2 := tmInv_eq_inv_of_det_mem a b ha hab (Matrix.of (Gf (I := I) (M := M) D h j z))
      (hdetrange z (by rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]; rw [hRbdef]; exact hz))
    unfold tmGamma tmGKi
    rw [show (fun p q : Fin (Module.finrank ℝ E) => D.mat j h p q z)
        = Mf (I := I) (M := M) D h j z from rfl, h1, h2]
  -- smoothness of the inverse entries
  have hinvsm : ∀ z ∈ Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) Rb, ∀ p q,
      ContDiffAt ℝ (⊤ : ℕ∞)
        (fun w => ((Matrix.of (Gf (I := I) (M := M) D h j w))⁻¹) p q) z := by
    intro z hz p q
    have hentry : ∀ p q, ContDiffAt ℝ (⊤ : ℕ∞)
        (fun w => (Matrix.of (Gf (I := I) (M := M) D h j w)) p q) z := by
      intro p q
      have h1 : ContDiffAt ℝ (⊤ : ℕ∞)
          (fun w => Gf (I := I) (M := M) D h j w p q) z :=
        (contDiffOn_Gf_entry (I := I) (M := M) D h hsmooth j p q).contDiffAt
          ((isOpen_flatToE_preimage_target (I := I) (M := M) D j).mem_nhds (hmemR z hz).1)
      simpa only [Matrix.of_apply] using h1
    exact contDiffAt_inv_entry (fun w => Matrix.of (Gf (I := I) (M := M) D h j w)) z
      hentry (Matrix.PosDef.det_pos (hpd z hz)).ne' p q
  -- quadratic form bounds for the inverse family
  have hqfpos : ∀ z ∈ Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) Rb,
      ∀ ξ : Fin (Module.finrank ℝ E) → ℝ, ξ ≠ 0 → 0 < ∑ p, ∑ q,
        ((Matrix.of (Gf (I := I) (M := M) D h j z))⁻¹) p q * ξ p * ξ q := by
    intro z hz ξ hξ
    have h1 : ((Matrix.of (Gf (I := I) (M := M) D h j z))⁻¹).PosDef := (hpd z hz).inv
    have h2 := (Matrix.posDef_iff_dotProduct_mulVec.mp h1).2 hξ
    rw [star_dotProduct_mulVec_eq_sum] at h2
    exact h2
  have hqfcont : ∀ p q, ContinuousOn (fun z =>
      ((Matrix.of (Gf (I := I) (M := M) D h j z))⁻¹) p q)
      (Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) Rb) :=
    fun p q z hz => (hinvsm z hz p q).continuousAt.continuousWithinAt
  obtain ⟨c₁, C₁, hc₁, hC₁, hqfb, hC1b⟩ := quadForm_bounds
    (Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) Rb)
    (isCompact_closedBall _ _) (fun z => (Matrix.of (Gf (I := I) (M := M) D h j z))⁻¹)
    hqfcont hqfpos
  -- the bound on the first derivatives
  have hderivcont : ∀ (r p q : Fin (Module.finrank ℝ E))
      (z : Fin (Module.finrank ℝ E) → ℝ),
      z ∈ Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) Rb →
      ContinuousAt (fun w => Work.Diff.STE.pdR r
        (fun w => ((Matrix.of (Gf (I := I) (M := M) D h j w))⁻¹) p q) w) z := by
    intro r p q z hz
    have h1 : ContinuousAt (fun w => fderiv ℝ
        (fun w => ((Matrix.of (Gf (I := I) (M := M) D h j w))⁻¹) p q) w) z :=
      (hinvsm z hz p q).continuousAt_fderiv (by norm_num)
    have h2 : ContinuousAt (fun w => (fderiv ℝ
        (fun w => ((Matrix.of (Gf (I := I) (M := M) D h j w))⁻¹) p q) w)
        (Pi.single r 1)) z := h1.clm_apply continuousAt_const
    simpa only [Work.Diff.STE.pdR] using h2
  have hC2 : ∃ C₂ : ℝ, 0 ≤ C₂ ∧ ∀ z, ‖z‖ ≤ 2 * D.σ j + δ₀ / 2 →
      ∀ r p q, |Work.Diff.STE.pdR r
        (fun w => ((Matrix.of (Gf (I := I) (M := M) D h j w))⁻¹) p q) z| ≤ C₂ := by
    let Gf' : (Fin (Module.finrank ℝ E) → ℝ) → ℝ := fun z =>
      ∑ r, ∑ p, ∑ q, |Work.Diff.STE.pdR r
        (fun w => ((Matrix.of (Gf (I := I) (M := M) D h j w))⁻¹) p q) z|
    have hcont : ContinuousOn Gf' (Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) Rb) := by
      intro z hz
      exact (continuousAt_sum_univ fun r => continuousAt_sum_univ fun p =>
        continuousAt_sum_univ fun q =>
          (hderivcont r p q z hz).abs).continuousWithinAt
    obtain ⟨z₀, hz₀, hmax⟩ := (isCompact_closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) Rb).exists_isMaxOn
      ⟨0, Metric.mem_closedBall_self hRbnn⟩ hcont
    refine ⟨Gf' z₀, ?_, fun z hz r p q => ?_⟩
    · exact Finset.sum_nonneg fun r _ => Finset.sum_nonneg fun p _ =>
        Finset.sum_nonneg fun q _ => abs_nonneg _
    · have hzK : z ∈ Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) Rb := by
        rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, hRbdef]
        linarith
      have h1 : |Work.Diff.STE.pdR r
          (fun w => ((Matrix.of (Gf (I := I) (M := M) D h j w))⁻¹) p q) z| ≤ Gf' z :=
        le_nested_sum (n := Module.finrank ℝ E)
          (f := fun (r' p' q' : Fin (Module.finrank ℝ E)) =>
            |Work.Diff.STE.pdR r'
              (fun w => ((Matrix.of (Gf (I := I) (M := M) D h j w))⁻¹) p' q') z|)
          (fun r' p' q' => abs_nonneg _) r p q
      have h2 : Gf' z ≤ Gf' z₀ := hmax hzK
      linarith
  obtain ⟨C₂, hC₂, hC2b⟩ := hC2
  refine ⟨a, b, ha, hab, c₁, C₁, C₂, hc₁, hC₁, hC₂, ?_, ?_, ?_⟩
  · -- (A) smoothness on the ball of radius `2σ + δ₀/2`
    intro p q z hz
    rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hz
    have hzbig : ‖z‖ < 2 * D.σ j + δ₀ := by linarith
    have heq : (fun w => tmGamma (I := I) (M := M) D j a b ha hab h w p q)
        =ᶠ[𝓝 z] (fun w => ((Matrix.of (Gf (I := I) (M := M) D h j w))⁻¹) p q) := by
      filter_upwards [Metric.closedBall_mem_nhds z (show 0 < 2 * D.σ j + δ₀ - ‖z‖ by linarith)]
        with w hw
      rw [Metric.mem_closedBall, dist_eq_norm] at hw
      refine hident w ?_ p q
      have h2 : ‖w‖ ≤ ‖w - z‖ + ‖z‖ := by
        have hh := norm_add_le (w - z) z
        rwa [sub_add_cancel] at hh
      linarith
    have hzK : z ∈ Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) Rb := by
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, hRbdef]
      linarith
    exact ((hinvsm z hzK p q).congr_of_eventuallyEq heq).contDiffWithinAt
  · -- (B) symmetry, positivity and bounds on the ball of radius `2σ + δ₀/2`
    intro z hz
    have hzK : z ∈ Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) Rb := by
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, hRbdef]
      linarith
    have hzbig : ‖z‖ ≤ 2 * D.σ j + δ₀ := by linarith
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro p q
      rw [hident z hzbig p q, hident z hzbig q p]
      have h4 : ((Matrix.of (Gf (I := I) (M := M) D h j z))⁻¹).transpose
          = (Matrix.of (Gf (I := I) (M := M) D h j z))⁻¹ := by
        rw [Matrix.transpose_nonsing_inv, transpose_Gf (I := I) (M := M) D h hsym j z]
      have h5 : ((Matrix.of (Gf (I := I) (M := M) D h j z))⁻¹) p q
          = ((Matrix.of (Gf (I := I) (M := M) D h j z))⁻¹) q p := by
        have h6 := congrFun (congrFun h4 q) p
        simpa only [Matrix.transpose_apply] using h6
      exact h5
    · intro ξ
      have hsum : ∑ p, ∑ q, tmGamma (I := I) (M := M) D j a b ha hab h z p q * ξ p * ξ q
          = ∑ p, ∑ q, ((Matrix.of (Gf (I := I) (M := M) D h j z))⁻¹) p q * ξ p * ξ q := by
        refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
        rw [hident z hzbig p q]
      rw [hsum]
      exact hqfb z hzK ξ
    · intro p q
      rw [hident z hzbig p q]
      exact hC1b z hzK p q
    · intro r p q
      have heq : (fun w => tmGamma (I := I) (M := M) D j a b ha hab h w p q)
          =ᶠ[𝓝 z] (fun w => ((Matrix.of (Gf (I := I) (M := M) D h j w))⁻¹) p q) := by
        filter_upwards [Metric.closedBall_mem_nhds z (show 0 < 2 * D.σ j + δ₀ - ‖z‖ by linarith)]
          with w hw
        rw [Metric.mem_closedBall, dist_eq_norm] at hw
        refine hident w ?_ p q
        have h2 : ‖w‖ ≤ ‖w - z‖ + ‖z‖ := by
          have hh := norm_add_le (w - z) z
          rwa [sub_add_cancel] at hh
        linarith
      have hfde : fderiv ℝ (fun w => tmGamma (I := I) (M := M) D j a b ha hab h w p q) z
          = fderiv ℝ (fun w => ((Matrix.of (Gf (I := I) (M := M) D h j w))⁻¹) p q) z :=
        heq.fderiv_eq
      have hval : Work.Diff.STE.pdR r (fun w => tmGamma (I := I) (M := M) D j a b ha hab h w p q) z
          = Work.Diff.STE.pdR r (fun w => ((Matrix.of (Gf (I := I) (M := M) D h j w))⁻¹) p q) z := by
        simp only [Work.Diff.STE.pdR, hfde]
      rw [hval]
      exact hC2b z hz r p q
  · -- (C) the honest chart matrix on the `2σ j` ball
    intro z hz p q
    have hfun : (fun i k => Work.Diff.STE.D.chartMatOf (I := I) (M := M) h (D.x₀ j)
        (yf (I := I) (M := M) D j z) i k)
        = Work.Diff.STE.D.chartMatOf (I := I) (M := M) h (D.x₀ j)
          (yf (I := I) (M := M) D j z) := by
      funext i k
      rfl
    rw [hfun]
    exact hident z (by linarith [hδ₀pos]) p q

end Work.Diff.STE.B3
