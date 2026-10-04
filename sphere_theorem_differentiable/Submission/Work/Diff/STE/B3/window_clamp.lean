import Mathlib
import Submission.Work.Diff.STE.B3.TransportDefs
import Submission.Work.Diff.STE.B3.transport_tame_defs
import Submission.Work.Diff.STE.B3.tmGK_eq_Gf
import Submission.Work.Diff.STE.B3.transport_Mf_second
import Submission.Work.Diff.STE.B3.det_bounds_of_quadForm

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators Matrix
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.STE.B3

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

/-! ## 0. Local helpers

Private copies of two facts that are already proved inside a sibling module
(`Submission/Work/Diff/STE/B3/tmGamma_props.lean`). -/

/-- The determinant, as a function of the entries of the matrix, is smooth. -/
private lemma window_clamp_det_contDiff_fn {n : ℕ} :
    ContDiff ℝ (⊤ : ℕ∞) (fun A : Fin n → Fin n → ℝ => (Matrix.of A).det) := by
  have h : (fun A : Fin n → Fin n → ℝ => (Matrix.of A).det)
      = fun A => ∑ σ : Equiv.Perm (Fin n), (↑↑(Equiv.Perm.sign σ) : ℝ) * ∏ i, A (σ i) i := by
    funext A
    rw [Matrix.det_apply']
    simp only [Matrix.of_apply]
  rw [h]
  fun_prop

/-- `tmInv` is the honest inverse as soon as the determinant lies in the clamping window. -/
private lemma window_clamp_tmInv_eq_inv_of_det_mem {n : ℕ} (a b : ℝ) (ha : 0 < a) (hab : a < b)
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

/-- The determinant of `tmGK z V = Finvf · V · Finvfᵀ`, in terms of the determinant of `V` and the
determinant of the frame matrix: `det (tmGK z V) = det V · ((det Ff) ^ 2)⁻¹`. -/
private lemma window_clamp_det_tmGK {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    (z : Fin (Module.finrank ℝ E) → ℝ)
    (V : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) :
    (tmGK (I := I) (M := M) D j z V).det
      = (Matrix.of V).det * (((Matrix.of (Ff (I := I) (M := M) D j z)).det) ^ 2)⁻¹ := by
  have h1 : (Matrix.of (Finvf (I := I) (M := M) D j z)).det
      = ((Matrix.of (Ff (I := I) (M := M) D j z)).det)⁻¹ := by
    rw [Finvf_eq_inv (I := I) (M := M) D j z, Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
  rw [tmGK, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h1, ← inv_pow]
  ring

/-- **The quadratic-form sandwich of the orthonormal-frame chart matrix.**  On the closed `2σ j`-ball
the frame `e j ·` is `g₀`-orthonormal, so `Mf z` is the matrix of the symmetric form `h` in a
`g₀`-orthonormal basis and inherits the pointwise pinching `lam · g₀ ≤ h ≤ K · g₀`. -/
private lemma window_clamp_Mf_quadForm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (j : ι₀) {lam K : ℝ}
    (hell : ∀ (x : M) (v : TangentSpace I x), lam * g₀.inner x v v ≤ h x v v)
    (hub : ∀ (x : M) (v : TangentSpace I x), h x v v ≤ K * g₀.inner x v v) :
    ∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ ≤ 2 * D.σ j →
      ∀ ξ : Fin (Module.finrank ℝ E) → ℝ,
        (lam * ∑ i, (ξ i) ^ 2 ≤ ∑ a, ∑ b, Mf (I := I) (M := M) D h j z a b * ξ a * ξ b) ∧
        (∑ a, ∑ b, Mf (I := I) (M := M) D h j z a b * ξ a * ξ b ≤ K * ∑ i, (ξ i) ^ 2) := by
  intro z hz ξ
  have hON : ∀ a b : Fin (Module.finrank ℝ E),
      g₀.inner (D.pt j z) (D.e j a (D.pt j z)) (D.e j b (D.pt j z)) =
        if a = b then 1 else 0 := D.heON j z hz
  have hbil : ∀ a b : Fin (Module.finrank ℝ E), Mf (I := I) (M := M) D h j z a b
      = h (D.pt j z) (D.e j a (D.pt j z)) (D.e j b (D.pt j z)) := fun a b => rfl
  have hform : (∑ a, ∑ b, Mf (I := I) (M := M) D h j z a b * ξ a * ξ b)
      = h (D.pt j z) (∑ a, ξ a • D.e j a (D.pt j z))
          (∑ b, ξ b • D.e j b (D.pt j z)) := by
    simp only [hbil, map_sum, ContinuousLinearMap.sum_apply, map_smul,
      ContinuousLinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  have hg : g₀.inner (D.pt j z) (∑ a, ξ a • D.e j a (D.pt j z))
      (∑ b, ξ b • D.e j b (D.pt j z)) = ∑ a, (ξ a) ^ 2 := by
    simp only [map_sum, ContinuousLinearMap.sum_apply, map_smul,
      ContinuousLinearMap.smul_apply, smul_eq_mul, Finset.mul_sum, hON]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single a]
    · rw [if_pos rfl]
      ring
    · intro b _ hba
      rw [if_neg (Ne.symm hba)]
      ring
    · intro ha
      exact absurd (Finset.mem_univ a) ha
  rw [hform]
  constructor
  · rw [← hg]
    exact hell _ _
  · calc h (D.pt j z) (∑ a, ξ a • D.e j a (D.pt j z))
          (∑ b, ξ b • D.e j b (D.pt j z))
        ≤ K * g₀.inner (D.pt j z) (∑ a, ξ a • D.e j a (D.pt j z))
            (∑ b, ξ b • D.e j b (D.pt j z)) := hub _ _
      _ = K * ∑ i, (ξ i) ^ 2 := by rw [hg]

/-- **Symmetry of the orthonormal-frame chart matrix** (the section is symmetric). -/
private lemma window_clamp_Mf_symm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hsym : ∀ (x : M) (u v : TangentSpace I x), h x u v = h x v u) (j : ι₀)
    (z : Fin (Module.finrank ℝ E) → ℝ) (a b : Fin (Module.finrank ℝ E)) :
    Mf (I := I) (M := M) D h j z a b = Mf (I := I) (M := M) D h j z b a := by
  change h (D.pt j z) (D.e j a (D.pt j z)) (D.e j b (D.pt j z))
      = h (D.pt j z) (D.e j b (D.pt j z)) (D.e j a (D.pt j z))
  exact hsym _ _ _

/-- **Uniform two-sided bounds for the square of the determinant of the frame matrix** on a closed
`2σ j`-ball: the determinant is continuous there (`Ff` is smooth on the chart target) and never
vanishes (`det_Ff_ne_zero`), so it stays in a window `[mj, Mj]` with `mj > 0`. -/
private lemma window_clamp_det_Ff_sq_bounds {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀) :
    ∃ mj Mj : ℝ, 0 < mj ∧ 0 < Mj ∧
      ∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ ≤ 2 * D.σ j →
        mj ≤ (Matrix.of (Ff (I := I) (M := M) D j z)).det ^ 2 ∧
        (Matrix.of (Ff (I := I) (M := M) D j z)).det ^ 2 ≤ Mj := by
  classical
  have hσ : 0 ≤ 2 * D.σ j := by linarith [D.hσ j]
  have hne : (Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ j)).Nonempty :=
    ⟨0, Metric.mem_closedBall_self hσ⟩
  have hcont : ContinuousOn
      (fun z : Fin (Module.finrank ℝ E) → ℝ =>
        (Matrix.of (Ff (I := I) (M := M) D j z)).det ^ 2)
      (Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ j)) := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hz
    have htgt : Work.Diff.STE.flatToE (I := I) (M := M) (D.x₀ j) z
        ∈ (extChartAt I (D.x₀ j)).target := D.htarget j z hz
    have hentry : ContDiffAt ℝ ∞
        (fun w : Fin (Module.finrank ℝ E) → ℝ => (Ff (I := I) (M := M) D j w :
          Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ)) z := by
      rw [contDiffAt_pi]
      intro a
      rw [contDiffAt_pi]
      intro i
      exact Ff_contDiffAt (I := I) (M := M) D j a i htgt
    have hdet : ContDiffAt ℝ ∞
        (fun w : Fin (Module.finrank ℝ E) → ℝ =>
          (Matrix.of (Ff (I := I) (M := M) D j w)).det) z :=
      (window_clamp_det_contDiff_fn (n := Module.finrank ℝ E)).contDiffAt.comp z hentry
    exact ((hdet.pow 2).continuousAt).continuousWithinAt
  obtain ⟨z₁, hz₁, hmin⟩ :=
    (isCompact_closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ j)).exists_isMinOn
      hne hcont
  obtain ⟨z₂, hz₂, hmax⟩ :=
    (isCompact_closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ j)).exists_isMaxOn
      hne hcont
  have hz₁' : ‖z₁‖ ≤ 2 * D.σ j := by
    rwa [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hz₁
  refine ⟨(Matrix.of (Ff (I := I) (M := M) D j z₁)).det ^ 2,
    max ((Matrix.of (Ff (I := I) (M := M) D j z₂)).det ^ 2) 1, ?_, ?_, ?_⟩
  · exact sq_pos_of_ne_zero (det_Ff_ne_zero (I := I) (M := M) D j hz₁')
  · exact lt_of_lt_of_le one_pos (le_max_right _ _)
  · intro z hz
    have hz' : z ∈ Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ j) := by
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
      exact hz
    exact ⟨hmin hz', le_trans (hmax hz') (le_max_left _ _)⟩

/-! ## 1. The determinant sandwich lemma for symmetric matrices -/

private lemma window_clamp_det_bounds_placeholder {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hsym : ∀ a b, A a b = A b a) {c K : ℝ} (hc : 0 ≤ c)
    (hl : ∀ ξ : Fin n → ℝ, c * ∑ i, (ξ i) ^ 2 ≤ ∑ a, ∑ b, A a b * ξ a * ξ b)
    (hu : ∀ ξ : Fin n → ℝ, ∑ a, ∑ b, A a b * ξ a * ξ b ≤ K * ∑ i, (ξ i) ^ 2) :
    c ^ n ≤ A.det ∧ A.det ≤ K ^ n :=
  det_bounds_of_quadForm A hsym hc hl hu

/-! ## 2. The main theorem -/

/-- **The uniform window for the clamped inverse, and the identification of the clamped inverse of
the frame-changed chart matrix with the honest inverse of the coordinate-frame chart matrix.**

`tmGKi a b ha hab z V = tmInv a b ha hab (tmGK z V)` where `tmInv` is the smoothly clamped matrix
inverse (a bump of the determinant times `A⁻¹` plus `(1 - bump) • 1`, equal to `A⁻¹` on the window
`det A ∈ [a,b]`), and `tmGK z (Mf z) = Finvf z * Mf z * Finvf zᵀ` is the frame change.

ROUTE.  The constant `lam`, `K` and the pointwise pinching `hell`, `hub` are *fixed* here, so the
window only needs the two-sided bound for the *background* chart matrix and the frame: on the closed
`2σ j`-ball the frame `e j ·` is `g₀`-orthonormal, so `Mf D h j z` is the matrix of the symmetric
form `h` in a `g₀`-orthonormal basis and satisfies `lam • 1 ≤ Mf ≤ K • 1`; then
`det (tmGK z (Mf z)) = det (Mf z) * (det (Finvf z))² = det (Mf z) / (det (Ff z))²`, where
`det (Ff z) ≠ 0` on the ball (`Work.Diff.STE.B3.det_Ff_ne_zero`).  Both factors are continuous on
the compact set `⋃ j, closedBall 0 (2 σ j)` (`Ff` is smooth there — see
`Work.Diff.STE.B3.Ff_contDiffAt`), and the determinant is positive, so

* `∃ a > 0` with `a ≤ det (tmGK z (Mf z))` for all `h`, `j`, `‖z‖ ≤ 2 σ j`, and
* `∃ b ≥` the corresponding sup,

by the "positive continuous function on a compact set has a positive min" argument
(`IsCompact.exists_isMinOn` / `exists_isMaxOn`, cf. `Work.Diff.STE.B3.quadForm_bounds` and
`exists_abs_entry_bound` for the shape).  With such a window, `tmInv a b ... A = A⁻¹` on
`{det A ∈ [a,b]}` (`ContDiffBump.one_of_mem_closedBall`; the private
`tmInv_eq_inv_of_det_mem` of `Submission/Work/Diff/STE/B3/tmGamma_props.lean` proves exactly this,
copy it), and `tmGK z (Mf z) = Matrix.of (Gf z)` is
`Work.Diff.STE.B3.tmGK_eq_Gf` (proved), which needs `flatToE (D.x₀ j) z ∈ target`
(`B3Data.htarget`) and `det (Ff z) ≠ 0` (both available on the ball).

Useful proved input in the importing module: `Work.Diff.STE.B3.Mf_loewner_ball` gives
`lam • ∑ ξᵢ² ≤ ξᵀ(Mf z)ξ ≤ K • ∑ ξᵢ²` for `‖z‖ ≤ 2 σ j`. -/
theorem window_clamp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (lam K : ℝ) (hlam : 0 < lam) (hK : 0 < K) :
    ∃ (a b : ℝ) (ha : 0 < a) (hab : a < b),
      ∀ (h : Work.Diff.STE.Bil (I := I) (M := M))
        (hsym : ∀ (x : M) (u v : TangentSpace I x), h x u v = h x v u)
        (hell : ∀ (x : M) (v : TangentSpace I x), lam * g₀.inner x v v ≤ h x v v)
        (hub : ∀ (x : M) (v : TangentSpace I x), h x v v ≤ K * g₀.inner x v v),
        ∀ (j : ι₀) (z : Fin (Module.finrank ℝ E) → ℝ), ‖z‖ ≤ 2 * D.σ j →
          (a ≤ (Work.Diff.STE.B3.tmGK (I := I) (M := M) D j z
                (Mf (I := I) (M := M) D h j z)).det ∧
            (Work.Diff.STE.B3.tmGK (I := I) (M := M) D j z
                (Mf (I := I) (M := M) D h j z)).det ≤ b) ∧
          Work.Diff.STE.B3.tmGKi (I := I) (M := M) D j a b ha hab z
              (Mf (I := I) (M := M) D h j z)
            = (Matrix.of (Gf (I := I) (M := M) D h j z))⁻¹ := by
  classical
  -- (1) uniform window for `(det Ff) ^ 2` over all charts
  have hper : ∀ j : ι₀, ∃ mj Mj : ℝ, 0 < mj ∧ 0 < Mj ∧
      ∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ ≤ 2 * D.σ j →
        mj ≤ (Matrix.of (Ff (I := I) (M := M) D j z)).det ^ 2 ∧
        (Matrix.of (Ff (I := I) (M := M) D j z)).det ^ 2 ≤ Mj :=
    fun j => window_clamp_det_Ff_sq_bounds (I := I) (M := M) D j
  obtain ⟨mF, MF, hmFpos, hMFpos, hbound⟩ : ∃ mF MF : ℝ, 0 < mF ∧ 0 < MF ∧
      ∀ (j : ι₀) (z : Fin (Module.finrank ℝ E) → ℝ), ‖z‖ ≤ 2 * D.σ j →
        mF ≤ (Matrix.of (Ff (I := I) (M := M) D j z)).det ^ 2 ∧
        (Matrix.of (Ff (I := I) (M := M) D j z)).det ^ 2 ≤ MF := by
    rcases isEmpty_or_nonempty ι₀ with hι | hι
    · exact ⟨1, 1, one_pos, one_pos, fun j => (hι.false j).elim⟩
    · haveI : Nonempty ι₀ := hι
      choose mj Mj hmj using hper
      have hj₀ : (Finset.univ : Finset ι₀).Nonempty := Finset.univ_nonempty
      refine ⟨Finset.univ.inf' hj₀ mj, Finset.univ.sup' hj₀ Mj, ?_, ?_, ?_⟩
      · exact (Finset.lt_inf'_iff hj₀).mpr (fun i _ => (hmj i).1)
      · obtain ⟨j₀, hj₀mem⟩ := Finset.univ_nonempty (α := ι₀)
        exact (Finset.lt_sup'_iff Finset.univ_nonempty).mpr ⟨j₀, hj₀mem, (hmj j₀).2.1⟩
      · intro j z hz
        obtain ⟨hlo, hhi⟩ := (hmj j).2.2 z hz
        exact ⟨le_trans (Finset.inf'_le mj (Finset.mem_univ j)) hlo,
          le_trans hhi (Finset.le_sup' Mj (Finset.mem_univ j))⟩
  -- (2) the constants of the window
  set a : ℝ := min (lam ^ Module.finrank ℝ E * MF⁻¹) (K ^ Module.finrank ℝ E * mF⁻¹) / 2
    with ha_def
  set b : ℝ := max (lam ^ Module.finrank ℝ E * MF⁻¹) (K ^ Module.finrank ℝ E * mF⁻¹) + 1
    with hb_def
  have hlamn : 0 < lam ^ Module.finrank ℝ E := pow_pos hlam _
  have hKn : 0 < K ^ Module.finrank ℝ E := pow_pos hK _
  have hMFiv : 0 < MF⁻¹ := inv_pos.mpr hMFpos
  have hmFiv : 0 < mF⁻¹ := inv_pos.mpr hmFpos
  have hminpos : 0 < min (lam ^ Module.finrank ℝ E * MF⁻¹) (K ^ Module.finrank ℝ E * mF⁻¹) :=
    lt_min (mul_pos hlamn hMFiv) (mul_pos hKn hmFiv)
  have ha : 0 < a := by
    rw [ha_def]
    linarith
  have hab : a < b := by
    rw [ha_def, hb_def]
    have h0 : 0 < min (lam ^ Module.finrank ℝ E * MF⁻¹) (K ^ Module.finrank ℝ E * mF⁻¹) :=
      hminpos
    have h1 : min (lam ^ Module.finrank ℝ E * MF⁻¹) (K ^ Module.finrank ℝ E * mF⁻¹) / 2
        ≤ max (lam ^ Module.finrank ℝ E * MF⁻¹) (K ^ Module.finrank ℝ E * mF⁻¹) :=
      le_trans (div_le_self h0.le (by norm_num)) (min_le_max)
    linarith
  refine ⟨a, b, ha, hab, ?_⟩
  intro h hsym hell hub j z hz
  -- (3) the two-sided quadratic-form bound for `Mf`
  have hMfquad := window_clamp_Mf_quadForm (I := I) (M := M) D h j hell hub z hz
  have hsymMf : ∀ p q, Matrix.of (Mf (I := I) (M := M) D h j z) p q
      = Matrix.of (Mf (I := I) (M := M) D h j z) q p := by
    intro p q
    simp only [Matrix.of_apply]
    exact window_clamp_Mf_symm (I := I) (M := M) D h hsym j z p q
  obtain ⟨hdetMflo, hdetMfhi⟩ := window_clamp_det_bounds_placeholder
    (A := Matrix.of (Mf (I := I) (M := M) D h j z)) hsymMf hlam.le
    (fun ξ => (hMfquad ξ).1) (fun ξ => (hMfquad ξ).2)
  -- (4) the two-sided bound for `(det Ff) ^ 2`
  obtain ⟨hFflo, hFfhi⟩ := hbound j z hz
  have hFf2pos : 0 < (Matrix.of (Ff (I := I) (M := M) D j z)).det ^ 2 :=
    lt_of_lt_of_le hmFpos hFflo
  -- (5) the determinant of `tmGK z (Mf z)`
  have hkey := window_clamp_det_tmGK (I := I) (M := M) D j z (Mf (I := I) (M := M) D h j z)
  have hinvlo : MF⁻¹ ≤ (((Matrix.of (Ff (I := I) (M := M) D j z)).det) ^ 2)⁻¹ :=
    (inv_le_inv₀ hMFpos hFf2pos).mpr hFfhi
  have hinvhi : (((Matrix.of (Ff (I := I) (M := M) D j z)).det) ^ 2)⁻¹ ≤ mF⁻¹ :=
    (inv_le_inv₀ hFf2pos hmFpos).mpr hFflo
  have hdetMfnn : 0 ≤ (Matrix.of (Mf (I := I) (M := M) D h j z)).det :=
    le_trans hlamn.le hdetMflo
  have hdetlo : a ≤ (tmGK (I := I) (M := M) D j z
      (Mf (I := I) (M := M) D h j z)).det := by
    rw [hkey]
    have h2 : a ≤ lam ^ Module.finrank ℝ E * MF⁻¹ := by
      rw [ha_def]
      exact le_trans (div_le_self hminpos.le (by norm_num)) (min_le_left _ _)
    have h3 := mul_le_mul hdetMflo hinvlo hMFiv.le hdetMfnn
    linarith
  have hdethi : (tmGK (I := I) (M := M) D j z
      (Mf (I := I) (M := M) D h j z)).det ≤ b := by
    rw [hkey]
    have h2 : K ^ Module.finrank ℝ E * mF⁻¹ ≤ b := by
      rw [hb_def]
      exact le_trans (le_max_right _ _) (le_add_of_nonneg_right zero_le_one)
    have h3 := mul_le_mul hdetMfhi hinvhi (le_of_lt (inv_pos.mpr hFf2pos)) hKn.le
    linarith
  have hwin : (Matrix.of (Gf (I := I) (M := M) D h j z)).det ∈ Set.Icc a b := by
    have hGK := tmGK_eq_Gf (I := I) (M := M) D h j z (D.htarget j z hz)
      (det_Ff_ne_zero (I := I) (M := M) D j hz)
    rw [← hGK]
    exact ⟨hdetlo, hdethi⟩
  constructor
  · exact ⟨hdetlo, hdethi⟩
  · have hGK := tmGK_eq_Gf (I := I) (M := M) D h j z (D.htarget j z hz)
      (det_Ff_ne_zero (I := I) (M := M) D j hz)
    rw [tmGKi, hGK]
    exact window_clamp_tmInv_eq_inv_of_det_mem a b ha hab (Matrix.of (Gf (I := I) (M := M) D h j z))
      hwin

end Work.Diff.STE.B3
