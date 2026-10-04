import Mathlib
import Submission.Work.Diff.MP.TruncDefs
import Submission.Work.Diff.MP.Basic
import Submission.Work.Diff.MP.Defs
import Submission.Work.Diff.MP.TruncKit
import Submission.Work.Diff.MP.frobInfDist_rmFrame_eq
import Submission.Work.Diff.MP.frob_nearest_supporting
import Submission.Work.Diff.GE.rmP_jointSmoothNoCompact
import Submission.Work.Diff.GE.continuous_flow_quantities
import Submission.Work.Diff.GE.NablaRm
import Submission.Work.Diff.GE.matrix_sqrt_family_kit
import Submission.Work.Diff.EXT.contMDiffAt_metric_pairing

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 8000000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology Matrix
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Filter

namespace Work.Diff.MP

/-!
# Regularity in time of the truncated supremum of the Frobenius distance

This file proves `Work.Diff.MP.sup_dist_regular`, the Chow--Lu Lemma 3.2 input of the
time-dependent maximum principle: the function `t ↦ truncSup G F Υ t` (the supremum over the
compact manifold of the Frobenius distance from the curvature array of `G t` to the truncated
invariant family `F t ∩ frobBall (Υ t)`) is lower semicontinuous and right upper semicontinuous.

The structural ingredients are

* `exists_local_rep`: near every space--time point `(t, y)` there is an open time interval `J'`,
  a neighbourhood `U` of `y` and a *continuously varying* family of curvature arrays `R s z`,
  each of which is the curvature array of `G s` at `z` in an orthonormal frame, so that
  `frobInfDist (rmC (G s) z) (F s ∩ frobBall (Υ s)) = frobInfDist (R s z) (F s ∩ frobBall (Υ s))`.
  (**Notation-free note**: the local frame is obtained from an orthonormal frame field of the
  *reference* metric `G t` (supplied by `LapRmFrameParallel`) by the inverse square root of its
  Gram matrix for `G s`.)
* `K_shrinks`: the fibres `K s = F s ∩ frobBall (Υ s)` shrink into `K t` as `s → t` (closedness of
  the space--time track plus compactness of the Frobenius ball).
-/

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## Multilinearity of `rmP` -/

/-- `rmP` is multilinear over four sums. -/
theorem rmP_sum4 [T2Space M] (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    {ι : Type*} (sa sb sc sd : Finset ι) (ca cb cc cd : ι → ℝ)
    (a b c d : ι → TangentSpace I x) :
    rmP g x (∑ i ∈ sa, ca i • a i) (∑ j ∈ sb, cb j • b j) (∑ k ∈ sc, cc k • c k)
        (∑ l ∈ sd, cd l • d l)
      = ∑ i ∈ sa, ∑ j ∈ sb, ∑ k ∈ sc, ∑ l ∈ sd,
          ca i * cb j * cc k * cd l * rmP g x (a i) (b j) (c k) (d l) := by
  rw [Work.Diff.GE.cfq_rmP_sum_fst hLC g x sa ca a (∑ j ∈ sb, cb j • b j)
    (∑ k ∈ sc, cc k • c k) (∑ l ∈ sd, cd l • d l)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Work.Diff.GE.cfq_rmP_sum_snd hLC g x sb cb b (a i)
    (∑ k ∈ sc, cc k • c k) (∑ l ∈ sd, cd l • d l)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Work.Diff.GE.cfq_rmP_sum_thd hLC g x sc cc c (a i) (b j) (∑ l ∈ sd, cd l • d l)]
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Work.Diff.GE.cfq_rmP_sum_fth hLC g x sd cd d (a i) (b j) (c k)]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

/-! ## The inverse square root of the Gram matrix -/

/-- For a symmetric matrix close to `1`, the inverse-function-theorem square root `P` of its
inverse satisfies `Pᵀ Γ P = 1`, and it depends continuously on `Γ` at `Γ = 1`. -/
theorem sqrtNear_orthogonal (n : ℕ) :
    (∃ V ∈ nhds (1 : Matrix (Fin n) (Fin n) ℝ), ∀ Γ ∈ V,
        Matrix.transpose Γ = Γ →
        Matrix.transpose (Work.Diff.GE.sqrtNear (Ring.inverse Γ)) * Γ *
            Work.Diff.GE.sqrtNear (Ring.inverse Γ) = 1) ∧
    Filter.Tendsto (fun Γ : Matrix (Fin n) (Fin n) ℝ ↦
        Work.Diff.GE.sqrtNear (Ring.inverse Γ)) (nhds (1 : Matrix (Fin n) (Fin n) ℝ)) (nhds 1) := by
  classical
  have hinv : Tendsto (fun Γ : Matrix (Fin n) (Fin n) ℝ => Ring.inverse Γ) (nhds 1) (nhds 1) := by
    have h : ContinuousAt (Ring.inverse : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ) 1 :=
      (hasFDerivAt_ringInverse (𝕜 := ℝ) (1 : (Matrix (Fin n) (Fin n) ℝ)ˣ)).continuousAt
    simpa only [Ring.inverse_one] using h.tendsto
  have hP : Tendsto (fun Γ : Matrix (Fin n) (Fin n) ℝ =>
      Work.Diff.GE.sqrtNear (Ring.inverse Γ)) (nhds 1) (nhds 1) := by
    have hsqrt : Tendsto (fun y : Matrix (Fin n) (Fin n) ℝ => Work.Diff.GE.sqrtNear y)
        (nhds 1) (nhds 1) := by
      have h : ContinuousAt (Work.Diff.GE.sqrtNear) (1 : Matrix (Fin n) (Fin n) ℝ) :=
        (Work.Diff.GE.sqrtNear_deriv (𝔸 := Matrix (Fin n) (Fin n) ℝ)).hasFDerivAt.continuousAt
      simpa only [Work.Diff.GE.sqrtNear_one] using h.tendsto
    exact hsqrt.comp hinv
  have hPT : Tendsto (fun Γ : Matrix (Fin n) (Fin n) ℝ =>
      Matrix.transpose (Work.Diff.GE.sqrtNear (Ring.inverse Γ))) (nhds 1) (nhds 1) := by
    have hT : Tendsto (Matrix.transpose : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ)
        (nhds 1) (nhds 1) := by
      have hc : Continuous (Matrix.transpose : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ) :=
        continuous_id.matrix_transpose
      simpa only [Matrix.transpose_one] using hc.tendsto 1
    exact hT.comp hP
  have hmm : ∀ᶠ y in nhds (1 : Matrix (Fin n) (Fin n) ℝ),
      Work.Diff.GE.sqrtNear y * Work.Diff.GE.sqrtNear y = y := Work.Diff.GE.sqrtNear_mul_self
  have hsq : ∀ᶠ x in nhds (1 : Matrix (Fin n) (Fin n) ℝ),
      Work.Diff.GE.sqrtNear (x * x) = x := Work.Diff.GE.sqrtNear_sq_eq
  have hGinv_ev : ∀ᶠ Γ in nhds (1 : Matrix (Fin n) (Fin n) ℝ), IsUnit Γ := by
    filter_upwards [Metric.ball_mem_nhds (1 : Matrix (Fin n) (Fin n) ℝ) (by norm_num : (0:ℝ) < 1/2)]
      with Γ hΓ
    rw [Metric.mem_ball, dist_eq_norm] at hΓ
    have h' : ‖(1 : Matrix (Fin n) (Fin n) ℝ) - Γ‖ < 1/2 := by
      simpa [norm_sub_rev] using hΓ
    have h'' : ‖(1 : Matrix (Fin n) (Fin n) ℝ) - Γ‖ < 1 := by linarith
    have h2 : IsUnit ((1 : Matrix (Fin n) (Fin n) ℝ) - ((1:Matrix (Fin n) (Fin n) ℝ) - Γ)) :=
      isUnit_one_sub_of_norm_lt_one h''
    simpa using h2
  have hV : ∃ V ∈ nhds (1 : Matrix (Fin n) (Fin n) ℝ), ∀ Γ ∈ V,
      Matrix.transpose Γ = Γ →
      Matrix.transpose (Work.Diff.GE.sqrtNear (Ring.inverse Γ)) * Γ *
          Work.Diff.GE.sqrtNear (Ring.inverse Γ) = 1 := by
    refine ⟨{Γ | Ring.inverse Γ ∈ {y | Work.Diff.GE.sqrtNear y * Work.Diff.GE.sqrtNear y = y}}
      ∩ {Γ | IsUnit Γ}
      ∩ {Γ | Matrix.transpose (Work.Diff.GE.sqrtNear (Ring.inverse Γ))
              ∈ {x | Work.Diff.GE.sqrtNear (x * x) = x}}, ?_, ?_⟩
    · exact Filter.inter_mem (Filter.inter_mem (hinv.eventually hmm) hGinv_ev) (hPT.eventually hsq)
    · intro Γ hΓ hsym
      obtain ⟨⟨hA, hunit⟩, hD⟩ := hΓ
      set P : Matrix (Fin n) (Fin n) ℝ := Work.Diff.GE.sqrtNear (Ring.inverse Γ) with hP'
      have hPP : P * P = Ring.inverse Γ := hA
      have hGinv : Ring.inverse Γ * Γ = 1 := by
        obtain ⟨u, hu⟩ : ∃ u : (Matrix (Fin n) (Fin n) ℝ)ˣ, (u : Matrix (Fin n) (Fin n) ℝ) = Γ :=
          ⟨hunit.unit, hunit.unit_spec⟩
        rw [← hu, Ring.inverse_unit]
        simpa using congrArg (Units.val) (Units.inv_mul u)
      have hGinv' : Γ * Ring.inverse Γ = 1 := by
        obtain ⟨u, hu⟩ : ∃ u : (Matrix (Fin n) (Fin n) ℝ)ˣ, (u : Matrix (Fin n) (Fin n) ℝ) = Γ :=
          ⟨hunit.unit, hunit.unit_spec⟩
        rw [← hu, Ring.inverse_unit]
        simpa using congrArg (Units.val) (Units.mul_inv u)
      have hsyinv : Matrix.transpose (Ring.inverse Γ) = Ring.inverse Γ := by
        obtain ⟨u, hu⟩ : ∃ u : (Matrix (Fin n) (Fin n) ℝ)ˣ, (u : Matrix (Fin n) (Fin n) ℝ) = Γ :=
          ⟨hunit.unit, hunit.unit_spec⟩
        rw [← hu, Ring.inverse_unit]
        let v : (Matrix (Fin n) (Fin n) ℝ)ˣ :=
          Units.mk (Matrix.transpose (u : Matrix (Fin n) (Fin n) ℝ))
            (Matrix.transpose ((u⁻¹ : (Matrix (Fin n) (Fin n) ℝ)ˣ) : Matrix (Fin n) (Fin n) ℝ))
            (by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one])
            (by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one])
        have hv : (v : Matrix (Fin n) (Fin n) ℝ) = (u : Matrix (Fin n) (Fin n) ℝ) := by
          show Matrix.transpose (u : Matrix (Fin n) (Fin n) ℝ) = (u : Matrix (Fin n) (Fin n) ℝ)
          rw [hu, hsym]
        have hvv : v = u := Units.ext hv
        have hv' : ((v⁻¹ : (Matrix (Fin n) (Fin n) ℝ)ˣ) : Matrix (Fin n) (Fin n) ℝ)
            = Matrix.transpose (((u⁻¹ : (Matrix (Fin n) (Fin n) ℝ)ˣ) : Matrix (Fin n) (Fin n) ℝ)) := by
          simp only [v, Units.inv_mk]
        calc Matrix.transpose (((u⁻¹ : (Matrix (Fin n) (Fin n) ℝ)ˣ) : Matrix (Fin n) (Fin n) ℝ))
            = ((v⁻¹ : (Matrix (Fin n) (Fin n) ℝ)ˣ) : Matrix (Fin n) (Fin n) ℝ) := hv'.symm
          _ = (((u⁻¹ : (Matrix (Fin n) (Fin n) ℝ)ˣ) : Matrix (Fin n) (Fin n) ℝ)) := by rw [hvv]
      have h1 : Matrix.transpose P * Matrix.transpose P = P * P := by
        rw [← Matrix.transpose_mul, hPP, hsyinv]
      have h2 : Work.Diff.GE.sqrtNear (Matrix.transpose P * Matrix.transpose P)
          = Matrix.transpose P := by
        have hh : Work.Diff.GE.sqrtNear
            (Matrix.transpose (Work.Diff.GE.sqrtNear (Ring.inverse Γ)) *
             Matrix.transpose (Work.Diff.GE.sqrtNear (Ring.inverse Γ)))
            = Matrix.transpose (Work.Diff.GE.sqrtNear (Ring.inverse Γ)) := hD
        rw [show Work.Diff.GE.sqrtNear (Ring.inverse Γ) = P from hP'.symm] at hh
        exact hh
      have hPsym : Matrix.transpose P = P := by
        rw [h1] at h2
        rw [hPP] at h2
        rw [show Work.Diff.GE.sqrtNear (Ring.inverse Γ) = P from hP'.symm] at h2
        exact h2.symm
      have hL' : (Γ * P) * P = 1 := by rw [mul_assoc, hPP, hGinv']
      have hR' : P * (P * Γ) = 1 := by rw [← mul_assoc, hPP, hGinv]
      have hcomm : Γ * P = P * Γ := by
        calc Γ * P = (Γ * P) * (P * (P * Γ)) := by rw [hR', mul_one]
          _ = ((Γ * P) * P) * (P * Γ) := by rw [← mul_assoc]
          _ = P * Γ := by rw [hL', one_mul]
      calc Matrix.transpose P * Γ * P = P * Γ * P := by rw [hPsym]
        _ = (P * Γ) * P := rfl
        _ = (Γ * P) * P := by rw [hcomm]
        _ = 1 := hL'
  exact ⟨hV, hP⟩

/-! ## Continuity of a finite sum of pointwise continuous functions -/

theorem continuousAt_finset_sum {ι X : Type*} [TopologicalSpace X] {s : Finset ι}
    {f : ι → X → ℝ} {x : X} (h : ∀ i ∈ s, ContinuousAt (f i) x) :
    ContinuousAt (fun y => ∑ i ∈ s, f i y) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using continuousAt_const
  | insert i s hi ih =>
      have h1 : ContinuousAt (f i) x := h i (Finset.mem_insert_self i s)
      have h2 : ContinuousAt (fun y => ∑ j ∈ s, f j y) x :=
        ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
      have hgoal : (fun y => ∑ j ∈ insert i s, f j y) = (f i + fun y => ∑ j ∈ s, f j y) := by
        funext y
        simp [Finset.sum_insert hi, Pi.add_apply]
      rw [hgoal]
      exact h1.add h2

/-! ## The local continuously varying frame and curvature array

The heart of the proof: near every space--time point `(t, y)` there is a neighbourhood on which the
curvature array of `G s` at `z`, computed in an orthonormal frame, is a *continuous* function of
`(s, z)`.  The orthonormal frame is obtained from an orthonormal frame field `Ef` of the reference
metric `G t` (supplied by `LapRmFrameParallel`) by the inverse square root `P` of the Gram matrix of
`Ef` for the moving metric `G s`; as `s → t` the Gram matrix tends to the identity, hence so does
`P`, and `Pᵀ Γ P = 1` makes the resulting frame orthonormal.
-/

theorem exists_local_rep [I.Boundaryless] [T2Space M]
    (hLC : LCSmooth I M) (hLP : LapRmFrameParallel I M)
    {G : ℝ → SMet I M} {J : Set ℝ} (hJ : IsOpen J) (hG : JointSmooth G J)
    {F : ℝ → Set (Curv4 (Module.finrank ℝ E))}
    (hFrot : ∀ t (A : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ),
      A ∈ Matrix.orthogonalGroup (Fin (Module.finrank ℝ E)) ℝ → ∀ R ∈ F t, rot A R ∈ F t)
    (Υ : ℝ → ℝ) {t : ℝ} (ht : t ∈ J) (y : M) :
    ∃ (J' : Set ℝ) (U : Set M) (R : ℝ → M → Curv4 (Module.finrank ℝ E)),
      IsOpen J' ∧ t ∈ J' ∧ J' ⊆ J ∧ U ∈ 𝓝 y ∧
      (∀ s ∈ J', ∀ z ∈ U, truncDist G F Υ s z
        = frobInfDist (R s z) (F s ∩ frobBall (Υ s))) ∧
      ContinuousAt (fun p : ℝ × M => R p.1 p.2) (t, y) := by
  classical
  obtain ⟨Ef, hEfy, hEfsm, _hEfON, _hLP⟩ :=
    hLP (G t) y (onFrame (G t) y) (Work.Diff.GE.isONFrame_onFrame (G t) y)
  let Γ : ℝ → M → Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    fun s z i j => (G s).inner z (Ef i z) (Ef j z)
  let P : ℝ → M → Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    fun s z => Work.Diff.GE.sqrtNear (Ring.inverse (Γ s z))
  have hΓc : ContinuousAt (fun p : ℝ × M => Γ p.1 p.2) (t, y) := by
    change ContinuousAt (fun p : ℝ × M =>
      (fun (i : Fin (Module.finrank ℝ E)) => fun (j : Fin (Module.finrank ℝ E)) =>
        Γ p.1 p.2 i j)) (t, y)
    rw [continuousAt_pi]
    intro i
    rw [continuousAt_pi]
    intro j
    have h := Work.Diff.EXT.contMDiffAt_metric_pairing (I := I) (M := M) hJ hG ht
      (x := y) (Y := Ef i) (Z := Ef j) (hEfsm i y) (hEfsm j y)
    simpa only [Γ] using h.continuousAt
  have hΓty : Γ t y = 1 := by
    ext i j
    simp only [Γ, Matrix.one_apply]
    rw [hEfy i, hEfy j]
    exact Work.Diff.GE.isONFrame_onFrame (G t) y i j
  obtain ⟨V, hVmem, hVorth⟩ := (sqrtNear_orthogonal (Module.finrank ℝ E)).1
  have hPc : ContinuousAt (fun p : ℝ × M => P p.1 p.2) (t, y) := by
    have hinv : ContinuousAt (fun p : ℝ × M => Ring.inverse (Γ p.1 p.2)) (t, y) := by
      have h1 : ContinuousAt (Ring.inverse : Matrix (Fin (Module.finrank ℝ E))
          (Fin (Module.finrank ℝ E)) ℝ → Matrix (Fin (Module.finrank ℝ E))
          (Fin (Module.finrank ℝ E)) ℝ) 1 :=
        (hasFDerivAt_ringInverse (𝕜 := ℝ)
          (1 : (Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ)ˣ)).continuousAt
      have h2 : ContinuousAt (Ring.inverse : Matrix (Fin (Module.finrank ℝ E))
          (Fin (Module.finrank ℝ E)) ℝ → Matrix (Fin (Module.finrank ℝ E))
          (Fin (Module.finrank ℝ E)) ℝ) (Γ t y) := by rw [hΓty]; exact h1
      have h3 := ContinuousAt.comp (g := Ring.inverse)
        (f := fun p : ℝ × M => Γ p.1 p.2) (x := (t, y)) h2 hΓc
      simpa only [Function.comp_def] using h3
    have h4 : ContinuousAt (Work.Diff.GE.sqrtNear : Matrix (Fin (Module.finrank ℝ E))
        (Fin (Module.finrank ℝ E)) ℝ → Matrix (Fin (Module.finrank ℝ E))
        (Fin (Module.finrank ℝ E)) ℝ) (Ring.inverse (Γ t y)) := by
      rw [hΓty, Ring.inverse_one]
      exact (Work.Diff.GE.sqrtNear_deriv (𝔸 := Matrix (Fin (Module.finrank ℝ E))
        (Fin (Module.finrank ℝ E)) ℝ)).hasFDerivAt.continuousAt
    have h5 := ContinuousAt.comp (g := Work.Diff.GE.sqrtNear)
      (f := fun p : ℝ × M => Ring.inverse (Γ p.1 p.2)) (x := (t, y)) h4 hinv
    simpa only [Function.comp_def, P] using h5
  have hVpre : (fun p : ℝ × M => Γ p.1 p.2) ⁻¹' V ∈ 𝓝 (t, y) :=
    hΓc.preimage_mem_nhds (by rw [hΓty]; exact hVmem)
  have hJpre : J ×ˢ (Set.univ : Set M) ∈ 𝓝 (t, y) := by
    rw [nhds_prod_eq]
    exact Filter.prod_mem_prod (hJ.mem_nhds ht) Filter.univ_mem
  obtain ⟨s₁, hs₁, s₂, hs₂, hs₁₂⟩ := mem_nhds_prod_iff.mp (Filter.inter_mem hVpre hJpre)
  obtain ⟨J', hJ's₁, hJ'open, htJ'⟩ := _root_.mem_nhds_iff.mp hs₁
  obtain ⟨U, hUs₂, hUopen, hyU⟩ := _root_.mem_nhds_iff.mp hs₂
  have hVsz : ∀ s ∈ J', ∀ z ∈ U, Γ s z ∈ V := by
    intro s hs z hz
    have hmem : (s, z) ∈ s₁ ×ˢ s₂ := ⟨hJ's₁ hs, hUs₂ hz⟩
    have h1 := (hs₁₂ hmem).1
    simpa only [Set.mem_preimage] using h1
  have hJ'J : ∀ s ∈ J', s ∈ J := by
    intro s hs
    have hmem : (s, y) ∈ s₁ ×ˢ s₂ := ⟨hJ's₁ hs, hUs₂ hyU⟩
    exact (hs₁₂ hmem).2.1
  have hON : ∀ s ∈ J', ∀ z ∈ U, IsONFrame (G s) z (fun i => ∑ a, P s z a i • Ef a z) := by
    intro s hs z hz
    have hsym : Matrix.transpose (Γ s z) = Γ s z := by
      ext a b
      simp only [Γ, Matrix.transpose_apply]
      exact (G s).symm z (Ef b z) (Ef a z)
    have hkey : Matrix.transpose (P s z) * Γ s z * P s z = 1 := hVorth (Γ s z) (hVsz s hs z hz) hsym
    intro a b
    show (G s).inner z (∑ i, P s z i a • Ef i z) (∑ j, P s z j b • Ef j z) = if a = b then 1 else 0
    have hL : (G s).inner z (∑ i, P s z i a • Ef i z) (∑ j, P s z j b • Ef j z)
        = ∑ i, ∑ j, P s z i a * P s z j b * Γ s z i j := by
      have hA : (G s).inner z (∑ i, P s z i a • Ef i z)
          = ∑ i, P s z i a • (G s).inner z (Ef i z) := by
        rw [map_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [map_smul]
      have heval : ∀ (w : TangentSpace I z),
          (∑ i, P s z i a • (G s).inner z (Ef i z)) w
            = ∑ i, P s z i a * (G s).inner z (Ef i z) w := by
        intro w
        rw [ContinuousLinearMap.sum_apply]
        exact Finset.sum_congr rfl fun i _ =>
          by rw [ContinuousLinearMap.smul_apply, smul_eq_mul]
      have h2 : ∀ (w : TangentSpace I z),
          (G s).inner z (∑ i, P s z i a • Ef i z) w
            = ∑ i, P s z i a * (G s).inner z (Ef i z) w := by
        intro w
        rw [hA]
        exact heval w
      have h3 : ∀ (i : Fin (Module.finrank ℝ E)),
          (G s).inner z (Ef i z) (∑ j, P s z j b • Ef j z)
            = ∑ j, P s z j b * (G s).inner z (Ef i z) (Ef j z) := by
        intro i
        rw [map_sum]
        exact Finset.sum_congr rfl fun j _ => by rw [map_smul, smul_eq_mul]
      simp only [h2, h3, Γ]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    have hR : (Matrix.transpose (P s z) * Γ s z * P s z) a b
        = ∑ i, ∑ j, P s z i a * P s z j b * Γ s z i j := by
      rw [Matrix.mul_apply]
      have hstep : ∀ c, (Matrix.transpose (P s z) * Γ s z) a c
          = ∑ b, P s z b a * Γ s z b c := by
        intro c
        rw [Matrix.mul_apply]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Matrix.transpose_apply]
      simp only [hstep, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [hL, ← hR, hkey, Matrix.one_apply]
  refine ⟨J', U, fun s z => rmFrame (G s) z (fun i => ∑ a, P s z a i • Ef a z), hJ'open, htJ',
    hJ'J, hUopen.mem_nhds hyU, ?_, ?_⟩
  · intro s hs z hz
    rw [truncDist]
    exact (frobInfDist_rmFrame_eq (I := I) (M := M) hLC (G s) z (F s ∩ frobBall (Υ s))
      (fun A hA R hR => ⟨hFrot s A hA R hR.1, (mem_frobBall_rot A hA).mpr hR.2⟩)
      (fun i => ∑ a, P s z a i • Ef a z) (hON s hs z hz)).symm
  · -- continuity of the curvature array at `(t, y)`
    have hPa : ∀ (i a : Fin (Module.finrank ℝ E)), ContinuousAt (fun p : ℝ × M =>
        P p.1 p.2 i a) (t, y) := by
      intro i a
      have h : ContinuousAt ((fun M : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ
          => M i a) ∘ fun p : ℝ × M => P p.1 p.2) (t, y) :=
        ContinuousAt.comp (((continuous_apply a).comp (continuous_apply i)).continuousAt) hPc
      simpa only [Function.comp_def] using h
    have hRm : ∀ a b c d : Fin (Module.finrank ℝ E), ContinuousAt (fun p : ℝ × M =>
        rmP (G p.1) p.2 (Ef a p.2) (Ef b p.2) (Ef c p.2) (Ef d p.2)) (t, y) := by
      intro a b c d
      exact (Work.Diff.GE.rmP_jointSmoothNoCompact (I := I) (M := M) hLC hJ hG ht y
        (hEfsm a) (hEfsm b) (hEfsm c) (hEfsm d)).continuousAt
    have hsum : ∀ i j k l : Fin (Module.finrank ℝ E), ContinuousAt (fun p : ℝ × M =>
        ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
            P p.1 p.2 a i * P p.1 p.2 b j * P p.1 p.2 c k * P p.1 p.2 d l *
              rmP (G p.1) p.2 (Ef a p.2) (Ef b p.2) (Ef c p.2) (Ef d p.2)) (t, y) := by
      intro i j k l
      refine continuousAt_finset_sum (fun a _ => ?_)
      refine continuousAt_finset_sum (fun b _ => ?_)
      refine continuousAt_finset_sum (fun c _ => ?_)
      refine continuousAt_finset_sum (fun d _ => ?_)
      have ha := hPa a i
      have hb := hPa b j
      have hc := hPa c k
      have hd := hPa d l
      have h1 : ContinuousAt (fun p : ℝ × M => P p.1 p.2 a i * P p.1 p.2 b j *
          P p.1 p.2 c k * P p.1 p.2 d l) (t, y) := by fun_prop
      exact h1.mul (hRm a b c d)
    have hReq : ∀ p : ℝ × M, rmFrame (G p.1) p.2 (fun i => ∑ a, P p.1 p.2 a i • Ef a p.2)
        = fun i j k l => ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
              P p.1 p.2 a i * P p.1 p.2 b j * P p.1 p.2 c k * P p.1 p.2 d l *
                rmP (G p.1) p.2 (Ef a p.2) (Ef b p.2) (Ef c p.2) (Ef d p.2) := by
      intro p
      funext i j k l
      show rmP (G p.1) p.2 (∑ a, P p.1 p.2 a i • Ef a p.2)
          (∑ b, P p.1 p.2 b j • Ef b p.2) (∑ c, P p.1 p.2 c k • Ef c p.2)
          (∑ d, P p.1 p.2 d l • Ef d p.2) = _
      rw [rmP_sum4 (I := I) (M := M) hLC (G p.1) p.2 Finset.univ Finset.univ Finset.univ Finset.univ
        (fun a => P p.1 p.2 a i) (fun b => P p.1 p.2 b j) (fun c => P p.1 p.2 c k)
        (fun d => P p.1 p.2 d l) (fun a => Ef a p.2) (fun b => Ef b p.2) (fun c => Ef c p.2)
        (fun d => Ef d p.2)]
    rw [funext hReq]
    rw [continuousAt_pi]
    intro i
    rw [continuousAt_pi]
    intro j
    rw [continuousAt_pi]
    intro k
    rw [continuousAt_pi]
    intro l
    exact hsum i j k l

/-! ## Elementary facts about `truncSup` -/

section SupFacts

variable {G : ℝ → SMet I M} {F : ℝ → Set (Curv4 (Module.finrank ℝ E))} {Υ : ℝ → ℝ}

theorem truncDist_nonneg (t : ℝ) (x : M) : 0 ≤ truncDist G F Υ t x := frobInfDist_nonneg _ _

theorem continuous_truncDist [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : LCSmooth I M) (hLP : LapRmFrameParallel I M)
    (hF : IsInvariantFamily F) (t : ℝ) : Continuous fun x : M => truncDist G F Υ t x :=
  continuous_frobInfDist_truncFam (I := I) (M := M) hLC hLP (G t) hF Υ t

theorem exists_truncSup_eq [I.Boundaryless] [T2Space M] [CompactSpace M] [Nonempty M]
    (hLC : LCSmooth I M)
    (hLP : LapRmFrameParallel I M) (hF : IsInvariantFamily F) (t : ℝ) :
    ∃ x : M, (∀ y : M, truncDist G F Υ t y ≤ truncDist G F Υ t x) ∧
      truncSup G F Υ t = truncDist G F Υ t x := by
  obtain ⟨x, -, hsup, hge⟩ := (isCompact_univ : IsCompact (Set.univ : Set M)).exists_sSup_image_eq_and_ge
    Set.univ_nonempty (continuous_truncDist hLC hLP hF t).continuousOn
  exact ⟨x, fun y => hge y trivial, hsup⟩

theorem truncDist_le_truncSup [I.Boundaryless] [T2Space M] [CompactSpace M] [Nonempty M]
    (hLC : LCSmooth I M)
    (hLP : LapRmFrameParallel I M) (hF : IsInvariantFamily F) (t : ℝ) (x : M) :
    truncDist G F Υ t x ≤ truncSup G F Υ t := by
  obtain ⟨z, hz, hzeq⟩ := exists_truncSup_eq hLC hLP hF t
  rw [hzeq]
  exact hz x

theorem truncSup_le_of [I.Boundaryless] [T2Space M] [CompactSpace M] [Nonempty M]
    (hLC : LCSmooth I M)
    (hLP : LapRmFrameParallel I M) (hF : IsInvariantFamily F) (t : ℝ) {c : ℝ}
    (h : ∀ x : M, truncDist G F Υ t x ≤ c) : truncSup G F Υ t ≤ c := by
  obtain ⟨z, _, hzeq⟩ := exists_truncSup_eq hLC hLP hF t
  rw [hzeq]
  exact h z

end SupFacts

/-! ## The fibres shrink into the fibre at the limit time

Closedness of the space--time track of `F` forces the truncated fibres `F s ∩ frobBall (Υ s)` to
accumulate inside `F t ∩ frobBall (Υ t)` as `s → t` (compactness of the Frobenius balls). -/

theorem K_shrinks {n : ℕ} {F : ℝ → Set (Curv4 n)}
    (hFcl : IsClosed {p : ℝ × Curv4 n | p.2 ∈ F p.1})
    {Υ : ℝ → ℝ} (hΥ : Continuous Υ)
    {I : Set ℝ} (hIc : IsCompact I) {t : ℝ} (_ht : t ∈ I) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ s ∈ I, |s - t| ≤ δ → ∀ S ∈ F s ∩ frobBall (Υ s),
      ∃ S' ∈ F t ∩ frobBall (Υ t), frobDist S S' ≤ ε := by
  classical
  by_contra hcon
  have hbad : ∀ δ : ℝ, 0 < δ → ∃ s ∈ I, |s - t| ≤ δ ∧ ∃ S ∈ F s ∩ frobBall (Υ s),
      ∀ S' ∈ F t ∩ frobBall (Υ t), ε < frobDist S S' := by
    intro δ hδ
    by_contra hbad_neg
    apply hcon
    refine ⟨δ, hδ, ?_⟩
    intro s hs hst S hS
    by_contra hc
    apply hbad_neg
    exact ⟨s, hs, hst, S, hS, fun S' hS' => not_le.mp (fun hle => hc ⟨S', hS', hle⟩)⟩
  choose s hsI hst S hS hSfar using fun m : ℕ => hbad (1 / (m + 1)) (by positivity)
  obtain ⟨R, hR⟩ := hIc.exists_bound_of_continuousOn hΥ.continuousOn
  have hSball : ∀ m : ℕ, S m ∈ frobBall (n := n) R := by
    intro m
    rw [frobBall_mem]
    have h1 : frobNorm (S m) ≤ Υ (s m) := (hS m).2
    have h2 : |Υ (s m)| ≤ R := by simpa [Real.norm_eq_abs] using hR (s m) (hsI m)
    have h3 : 0 ≤ frobNorm (S m) := frobNorm_nonneg _
    have h4 : Υ (s m) ≤ R := (abs_le.mp h2).2
    linarith
  have hcomp : IsCompact (frobBall (n := n) R) := by
    refine Metric.isCompact_iff_isClosed_bounded.mpr ⟨isClosed_frobBall R, ?_⟩
    refine isBounded_iff_forall_norm_le.mpr ⟨max R 0, fun x hx => ?_⟩
    rw [frobBall_mem] at hx
    exact le_trans (norm_le_frobNorm x) (le_trans hx (le_max_left _ _))
  obtain ⟨a, ha_ball, φ, hφ, hφtend⟩ := hcomp.tendsto_subseq (fun m => hSball m)
  have hφtop : Tendsto φ atTop atTop := hφ.tendsto_atTop
  have hslim : Tendsto (fun m : ℕ => s m - t) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun m => norm_nonneg _) (fun m => ?_)
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    rw [Real.norm_eq_abs]
    exact hst m
  have hstend : Tendsto (fun m : ℕ => s m) atTop (𝓝 t) := by
    have h2 : Tendsto (fun m : ℕ => t + (s m - t)) atTop (𝓝 (t + 0)) :=
      tendsto_const_nhds.add hslim
    simpa using h2
  have hstendφ : Tendsto (fun m : ℕ => s (φ m)) atTop (𝓝 t) := hstend.comp hφtop
  have hpair : Tendsto (fun m : ℕ => (s (φ m), S (φ m))) atTop (𝓝 (t, a)) := by
    have h1 := Tendsto.prodMk hstendφ hφtend
    rwa [← nhds_prod_eq] at h1
  have haF : a ∈ F t := hFcl.mem_of_tendsto hpair (Eventually.of_forall fun m => (hS (φ m)).1)
  have haΥ : a ∈ frobBall (Υ t) := by
    rw [frobBall_mem]
    have h1 : Tendsto (fun m : ℕ => frobNorm (S (φ m))) atTop (𝓝 (frobNorm a)) :=
      (continuous_frobNorm.tendsto a).comp hφtend
    have h2 : Tendsto (fun m : ℕ => Υ (s (φ m))) atTop (𝓝 (Υ t)) :=
      (hΥ.continuousAt.tendsto).comp hstendφ
    exact le_of_tendsto_of_tendsto h1 h2 (Eventually.of_forall fun m => (hS (φ m)).2)
  have hcont : Continuous fun S : Curv4 n => frobDist S a :=
    continuous_frobNorm.comp (continuous_id.sub continuous_const)
  have h3 : Tendsto (fun m : ℕ => frobDist (S (φ m)) a) atTop (𝓝 0) := by
    have h1 : Tendsto (fun m : ℕ => frobDist (S (φ m)) a) atTop (𝓝 (frobDist a a)) :=
      hcont.tendsto a |>.comp hφtend
    have h2 : frobDist a a = 0 := by rw [frobDist, sub_self, frobNorm_zero]
    rwa [h2] at h1
  have hle : ε ≤ 0 := le_of_tendsto_of_tendsto tendsto_const_nhds h3
    (Eventually.of_forall fun m => le_of_lt (hSfar (φ m) a ⟨haF, haΥ⟩))
  linarith

/-! ## The lower semicontinuity and right upper semicontinuity of `truncSup` -/

/-- The local representation hypothesis: near every point the truncated Frobenius distance is the
distance to the (continuously varying) curvature array of `G` in an orthonormal frame. -/
abbrev HasLocalRep (G : ℝ → SMet I M) (F : ℝ → Set (Curv4 (Module.finrank ℝ E)))
    (Υ : ℝ → ℝ) (J : Set ℝ) (t : ℝ) : Prop :=
  ∀ y : M, ∃ (J' : Set ℝ) (U : Set M) (R : ℝ → M → Curv4 (Module.finrank ℝ E)),
    IsOpen J' ∧ t ∈ J' ∧ J' ⊆ J ∧ U ∈ 𝓝 y ∧
    (∀ s ∈ J', ∀ z ∈ U, truncDist G F Υ s z
      = frobInfDist (R s z) (F s ∩ frobBall (Υ s))) ∧
    ContinuousAt (fun p : ℝ × M => R p.1 p.2) (t, y)

theorem hasLocalRep_of_jointSmooth [I.Boundaryless] [T2Space M]
    (hLC : LCSmooth I M) (hLP : LapRmFrameParallel I M)
    {G : ℝ → SMet I M} {J : Set ℝ} (hJ : IsOpen J) (hG : JointSmooth G J)
    {F : ℝ → Set (Curv4 (Module.finrank ℝ E))}
    (hFrot : ∀ t (A : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ),
      A ∈ Matrix.orthogonalGroup (Fin (Module.finrank ℝ E)) ℝ → ∀ R ∈ F t, rot A R ∈ F t)
    (Υ : ℝ → ℝ) {t : ℝ} (ht : t ∈ J) :
    HasLocalRep (I := I) (M := M) G F Υ J t :=
  fun y => exists_local_rep (I := I) (M := M) hLC hLP hJ hG hFrot Υ ht y

/-- `frobDist` is dominated by the instance norm. -/
theorem frobDist_lt_of_norm_sub_lt {n : ℕ} {x y : Curv4 n} {η : ℝ} (hη : 0 < η)
    (h : ‖x - y‖ < η / ((n : ℝ) ^ 2 + 1)) : frobDist x y < η := by
  have h1 : frobDist x y ≤ (n : ℝ) ^ 2 * ‖x - y‖ := frobNorm_le_mul_norm _
  have h2 : (n : ℝ) ^ 2 * ‖x - y‖ ≤ (n : ℝ) ^ 2 * (η / ((n : ℝ) ^ 2 + 1)) :=
    mul_le_mul_of_nonneg_left (le_of_lt h) (by positivity)
  have h3 : (n : ℝ) ^ 2 * (η / ((n : ℝ) ^ 2 + 1))
      = η * ((n : ℝ) ^ 2 / ((n : ℝ) ^ 2 + 1)) := by ring
  have h4 : (n : ℝ) ^ 2 / ((n : ℝ) ^ 2 + 1) < 1 := by
    rw [div_lt_one (by positivity)]
    linarith [sq_nonneg (n : ℝ)]
  have h5 : η * ((n : ℝ) ^ 2 / ((n : ℝ) ^ 2 + 1)) < η * 1 :=
    mul_lt_mul_of_pos_left h4 hη
  linarith

/-- A sequence of curvature arrays converging to `a` has Frobenius distance to `a` tending to `0`.
(The topology on `Curv4 n` is the product topology, and `frobDist` is continuous for it.) -/
theorem tendsto_frobDist_zero {ι : Type*} {l : Filter ι} {n : ℕ} {F : ι → Curv4 n} {a : Curv4 n}
    (h : Tendsto F l (𝓝 a)) : Tendsto (fun m => frobDist (F m) a) l (𝓝 0) := by
  have h1 : Tendsto (fun m => F m - a) l (𝓝 (a - a)) := h.sub tendsto_const_nhds
  have h2 : Tendsto (fun m => frobNorm (F m - a)) l (𝓝 (frobNorm (a - a))) :=
    continuous_frobNorm.tendsto _ |>.comp h1
  have h3 : frobNorm (a - a) = 0 := by rw [sub_self, frobNorm_zero]
  simpa only [frobDist, h3] using h2

/-- **Left lower semicontinuity** of `t ↦ truncSup G F Υ t`. -/
theorem truncSup_lsc_left [I.Boundaryless] [T2Space M] [CompactSpace M] [Nonempty M]
    (hLC : LCSmooth I M) (hLP : LapRmFrameParallel I M)
    {G : ℝ → SMet I M} {F : ℝ → Set (Curv4 (Module.finrank ℝ E))} {Υ : ℝ → ℝ}
    (hF : IsInvariantFamily F) (hΥ : Continuous Υ)
    {J : Set ℝ} (hJ : IsOpen J) {t δk : ℝ} (ht : t ∈ J) (hδk : 0 < δk)
    (hloc : HasLocalRep (I := I) (M := M) G F Υ J t)
    (hKne : ∀ s ∈ J, s ≤ t → |s - t| ≤ δk → (F s ∩ frobBall (Υ s)).Nonempty) :
    ∀ ε > 0, ∃ δ > 0, ∀ s ∈ J, s ≤ t → |s - t| ≤ δ →
      truncSup G F Υ t ≤ truncSup G F Υ s + ε := by
  intro ε hε
  have hη3 : 0 < ε / 3 := by linarith
  by_contra hcon
  have hbad : ∀ δ : ℝ, 0 < δ → ∃ s ∈ J, s ≤ t ∧ |s - t| ≤ δ ∧
      truncSup G F Υ t > truncSup G F Υ s + ε := by
    intro δ hδ
    by_contra hb
    apply hcon
    refine ⟨δ, hδ, fun s hs hst hst' => ?_⟩
    by_contra hlt
    exact hb ⟨s, hs, hst, hst', not_le.mp hlt⟩
  choose s hsJ hst hδs hgt using fun m : ℕ => hbad (min (1 / (m + 1)) δk) (by positivity)
  have hsmk : ∀ m : ℕ, |s m - t| ≤ δk := by
    intro m
    exact le_trans (hδs m) (min_le_right _ _)
  obtain ⟨x₀, hx₀max, hx₀eq⟩ := exists_truncSup_eq (I := I) (M := M) hLC hLP hF t
  obtain ⟨J', U, R, hJ'open, htJ', hJ'J, hU, hlocid, hRcont⟩ := hloc x₀
  have hx₀U : x₀ ∈ U := mem_of_mem_nhds hU
  obtain ⟨δ_J, hδ_J, hδ_JJ⟩ : ∃ δ > 0, Set.Icc (t - δ) (t + δ) ⊆ J := by
    rcases Metric.mem_nhds_iff.mp (hJ.mem_nhds ht) with ⟨r, hr, hsub⟩
    refine ⟨r / 2, by linarith, fun x hx => hsub ?_⟩
    rw [Set.mem_Icc] at hx
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hx.1, hx.2, hr]
  have htI : t ∈ Set.Icc (t - δ_J) (t + δ_J) := ⟨by linarith, by linarith⟩
  obtain ⟨δ_S, hδ_S, hδ_Sprop⟩ := K_shrinks hF.1 hΥ isCompact_Icc htI hη3
  have hslim : Tendsto (fun m : ℕ => s m) atTop (𝓝 t) := by
    have h1 : Tendsto (fun m : ℕ => s m - t) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine squeeze_zero (fun m => norm_nonneg _) (fun m => ?_)
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      rw [Real.norm_eq_abs]
      exact le_trans (hδs m) (min_le_left _ _)
    have h2 : Tendsto (fun m : ℕ => t + (s m - t)) atTop (𝓝 (t + 0)) :=
      tendsto_const_nhds.add h1
    simpa using h2
  have hevJ' : ∀ᶠ m in atTop, s m ∈ J' := hslim.eventually (hJ'open.mem_nhds htJ')
  have hevI : ∀ᶠ m in atTop, s m ∈ Set.Icc (t - δ_J) (t + δ_J) := by
    filter_upwards [hslim.eventually (Metric.ball_mem_nhds t hδ_J)] with m hm
    rw [Set.mem_Icc]
    have hm' : |s m - t| < δ_J := by simpa [Real.dist_eq] using hm
    rw [abs_lt] at hm'
    constructor <;> linarith [hm'.1, hm'.2]
  have hevS : ∀ᶠ m in atTop, |s m - t| ≤ δ_S := by
    filter_upwards [hslim.eventually (Metric.ball_mem_nhds t hδ_S)] with m hm
    exact le_of_lt (by simpa [Real.dist_eq] using hm)
  have hevR : ∀ᶠ m in atTop, frobDist (R (s m) x₀) (R t x₀) ≤ ε / 3 := by
    have h1 : Tendsto (fun m : ℕ => (s m, x₀)) atTop (𝓝 (t, x₀)) := by
      have h : Tendsto (fun m : ℕ => (s m, x₀)) atTop (𝓝 t ×ˢ 𝓝 x₀) :=
        Tendsto.prodMk hslim tendsto_const_nhds
      rwa [← nhds_prod_eq] at h
    have h2 : Tendsto (fun m : ℕ => R (s m) x₀) atTop (𝓝 (R t x₀)) := by
      have h3 := (hRcont.tendsto).comp h1
      simpa only [Function.comp_def] using h3
    have h4 := tendsto_frobDist_zero h2
    exact h4.eventually (Iic_mem_nhds (by linarith))
  have hfinal : ∀ᶠ m in atTop, truncSup G F Υ t ≤ truncSup G F Υ (s m) + ε := by
    filter_upwards [hevJ', hevI, hevS, hevR] with m hJ'm hIm hSm hRm
    have hKne_m : (F (s m) ∩ frobBall (Υ (s m))).Nonempty :=
      hKne (s m) (hsJ m) (hst m) (hsmk m)
    have hstep : frobInfDist (R t x₀) (F t ∩ frobBall (Υ t))
        ≤ frobInfDist (R t x₀) (F (s m) ∩ frobBall (Υ (s m))) + ε / 3 := by
      have h1 : frobInfDist (R t x₀) (F t ∩ frobBall (Υ t)) - ε / 3
          ≤ frobInfDist (R t x₀) (F (s m) ∩ frobBall (Υ (s m))) := by
        refine le_frobInfDist hKne_m (fun S hS => ?_)
        obtain ⟨S', hS', hSS'⟩ := hδ_Sprop (s m) hIm hSm S hS
        have h2 : frobInfDist (R t x₀) (F t ∩ frobBall (Υ t)) ≤ frobDist (R t x₀) S' :=
          frobInfDist_le hS'
        have h3 : frobDist (R t x₀) S' ≤ frobDist (R t x₀) S + frobDist S S' :=
          frobDist_triangle _ _ _
        linarith
      linarith
    have hstep2 : frobInfDist (R t x₀) (F (s m) ∩ frobBall (Υ (s m)))
        ≤ frobDist (R t x₀) (R (s m) x₀)
          + frobInfDist (R (s m) x₀) (F (s m) ∩ frobBall (Υ (s m))) := by
      have h1 := abs_frobInfDist_sub_le hKne_m (R t x₀) (R (s m) x₀)
      have h2 := (abs_le.mp h1).2
      linarith
    have ht_eq : frobInfDist (R t x₀) (F t ∩ frobBall (Υ t)) = truncDist G F Υ t x₀ :=
      (hlocid t htJ' x₀ hx₀U).symm
    have hs_eq : frobInfDist (R (s m) x₀) (F (s m) ∩ frobBall (Υ (s m)))
        = truncDist G F Υ (s m) x₀ := (hlocid (s m) hJ'm x₀ hx₀U).symm
    have hsu : truncDist G F Υ (s m) x₀ ≤ truncSup G F Υ (s m) :=
      truncDist_le_truncSup hLC hLP hF (s m) x₀
    have hRm' : frobDist (R t x₀) (R (s m) x₀) ≤ ε / 3 := by
      rw [frobDist_comm]
      exact hRm
    rw [ht_eq] at hstep
    rw [hs_eq] at hstep2
    rw [hx₀eq]
    linarith [hstep, hstep2, hRm', hsu]
  rcases (hfinal.and (Eventually.of_forall hgt)).exists with ⟨m, hle, hgtm⟩
  linarith

/-- **Right lower semicontinuity** of `t ↦ truncSup G F Υ t`. -/
theorem truncSup_lsc_right [I.Boundaryless] [T2Space M] [CompactSpace M] [Nonempty M]
    (hLC : LCSmooth I M) (hLP : LapRmFrameParallel I M)
    {G : ℝ → SMet I M} {F : ℝ → Set (Curv4 (Module.finrank ℝ E))} {Υ : ℝ → ℝ}
    (hF : IsInvariantFamily F) (hΥ : Continuous Υ)
    {J : Set ℝ} (hJ : IsOpen J) {t : ℝ} (ht : t ∈ J)
    (hloc : HasLocalRep (I := I) (M := M) G F Υ J t)
    (hKne : ∀ s ∈ J, t ≤ s → (F s ∩ frobBall (Υ s)).Nonempty) :
    ∀ ε > 0, ∃ δ > 0, ∀ s ∈ J, t ≤ s → s ≤ t + δ →
      truncSup G F Υ t ≤ truncSup G F Υ s + ε := by
  intro ε hε
  have hη3 : 0 < ε / 3 := by linarith
  by_contra hcon
  have hbad : ∀ δ : ℝ, 0 < δ → ∃ s ∈ J, t ≤ s ∧ s ≤ t + δ ∧
      truncSup G F Υ t > truncSup G F Υ s + ε := by
    intro δ hδ
    by_contra hb
    apply hcon
    refine ⟨δ, hδ, fun s hs hts hst => ?_⟩
    by_contra hlt
    exact hb ⟨s, hs, hts, hst, not_le.mp hlt⟩
  choose s hsJ hst hδs hgt using fun m : ℕ => hbad (1 / (m + 1)) (by positivity)
  obtain ⟨x₀, hx₀max, hx₀eq⟩ := exists_truncSup_eq (I := I) (M := M) hLC hLP hF t
  obtain ⟨J', U, R, hJ'open, htJ', hJ'J, hU, hlocid, hRcont⟩ := hloc x₀
  have hx₀U : x₀ ∈ U := mem_of_mem_nhds hU
  obtain ⟨δ_J, hδ_J, hδ_JJ⟩ : ∃ δ > 0, Set.Icc (t - δ) (t + δ) ⊆ J := by
    rcases Metric.mem_nhds_iff.mp (hJ.mem_nhds ht) with ⟨r, hr, hsub⟩
    refine ⟨r / 2, by linarith, fun x hx => hsub ?_⟩
    rw [Set.mem_Icc] at hx
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hx.1, hx.2, hr]
  have htI : t ∈ Set.Icc (t - δ_J) (t + δ_J) := ⟨by linarith, by linarith⟩
  obtain ⟨δ_S, hδ_S, hδ_Sprop⟩ := K_shrinks hF.1 hΥ isCompact_Icc htI hη3
  have hslim : Tendsto (fun m : ℕ => s m) atTop (𝓝 t) := by
    have h1 : Tendsto (fun m : ℕ => s m - t) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine squeeze_zero (fun m => norm_nonneg _) (fun m => ?_)
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      rw [Real.norm_eq_abs]
      have h := hδs m
      have h' := hst m
      rw [abs_le]
      constructor <;> linarith
    have h2 : Tendsto (fun m : ℕ => t + (s m - t)) atTop (𝓝 (t + 0)) :=
      tendsto_const_nhds.add h1
    simpa using h2
  have hevJ' : ∀ᶠ m in atTop, s m ∈ J' := hslim.eventually (hJ'open.mem_nhds htJ')
  have hevI : ∀ᶠ m in atTop, s m ∈ Set.Icc (t - δ_J) (t + δ_J) := by
    filter_upwards [hslim.eventually (Metric.ball_mem_nhds t hδ_J)] with m hm
    rw [Set.mem_Icc]
    have hm' : |s m - t| < δ_J := by simpa [Real.dist_eq] using hm
    rw [abs_lt] at hm'
    constructor <;> linarith [hm'.1, hm'.2]
  have hevS : ∀ᶠ m in atTop, |s m - t| ≤ δ_S := by
    filter_upwards [hslim.eventually (Metric.ball_mem_nhds t hδ_S)] with m hm
    exact le_of_lt (by simpa [Real.dist_eq] using hm)
  have hevR : ∀ᶠ m in atTop, frobDist (R (s m) x₀) (R t x₀) ≤ ε / 3 := by
    have h1 : Tendsto (fun m : ℕ => (s m, x₀)) atTop (𝓝 (t, x₀)) := by
      have h : Tendsto (fun m : ℕ => (s m, x₀)) atTop (𝓝 t ×ˢ 𝓝 x₀) :=
        Tendsto.prodMk hslim tendsto_const_nhds
      rwa [← nhds_prod_eq] at h
    have h2 : Tendsto (fun m : ℕ => R (s m) x₀) atTop (𝓝 (R t x₀)) := by
      have h3 := (hRcont.tendsto).comp h1
      simpa only [Function.comp_def] using h3
    have h4 := tendsto_frobDist_zero h2
    exact h4.eventually (Iic_mem_nhds (by linarith))
  have hfinal : ∀ᶠ m in atTop, truncSup G F Υ t ≤ truncSup G F Υ (s m) + ε := by
    filter_upwards [hevJ', hevI, hevS, hevR] with m hJ'm hIm hSm hRm
    have hKne_m : (F (s m) ∩ frobBall (Υ (s m))).Nonempty := hKne (s m) (hsJ m) (hst m)
    have hstep : frobInfDist (R t x₀) (F t ∩ frobBall (Υ t))
        ≤ frobInfDist (R t x₀) (F (s m) ∩ frobBall (Υ (s m))) + ε / 3 := by
      have h1 : frobInfDist (R t x₀) (F t ∩ frobBall (Υ t)) - ε / 3
          ≤ frobInfDist (R t x₀) (F (s m) ∩ frobBall (Υ (s m))) := by
        refine le_frobInfDist hKne_m (fun S hS => ?_)
        obtain ⟨S', hS', hSS'⟩ := hδ_Sprop (s m) hIm hSm S hS
        have h2 : frobInfDist (R t x₀) (F t ∩ frobBall (Υ t)) ≤ frobDist (R t x₀) S' :=
          frobInfDist_le hS'
        have h3 : frobDist (R t x₀) S' ≤ frobDist (R t x₀) S + frobDist S S' :=
          frobDist_triangle _ _ _
        linarith
      linarith
    have hstep2 : frobInfDist (R t x₀) (F (s m) ∩ frobBall (Υ (s m)))
        ≤ frobDist (R t x₀) (R (s m) x₀)
          + frobInfDist (R (s m) x₀) (F (s m) ∩ frobBall (Υ (s m))) := by
      have h1 := abs_frobInfDist_sub_le hKne_m (R t x₀) (R (s m) x₀)
      have h2 := (abs_le.mp h1).2
      linarith
    have ht_eq : frobInfDist (R t x₀) (F t ∩ frobBall (Υ t)) = truncDist G F Υ t x₀ :=
      (hlocid t htJ' x₀ hx₀U).symm
    have hs_eq : frobInfDist (R (s m) x₀) (F (s m) ∩ frobBall (Υ (s m)))
        = truncDist G F Υ (s m) x₀ := (hlocid (s m) hJ'm x₀ hx₀U).symm
    have hsu : truncDist G F Υ (s m) x₀ ≤ truncSup G F Υ (s m) :=
      truncDist_le_truncSup hLC hLP hF (s m) x₀
    have hRm' : frobDist (R t x₀) (R (s m) x₀) ≤ ε / 3 := by
      rw [frobDist_comm]
      exact hRm
    rw [ht_eq] at hstep
    rw [hs_eq] at hstep2
    rw [hx₀eq]
    linarith [hstep, hstep2, hRm', hsu]
  rcases (hfinal.and (Eventually.of_forall hgt)).exists with ⟨m, hle, hgtm⟩
  linarith

/-- A cluster point of a sequence is frequently in every neighbourhood. -/
theorem MapClusterPt.frequently_mem {ι X : Type*} [TopologicalSpace X] {x : X} {l : Filter ι}
    {u : ι → X} (h : MapClusterPt x l u) {U : Set X} (hU : U ∈ 𝓝 x) :
    ∃ᶠ i in l, u i ∈ U := by
  by_contra hc
  have h2 : {i | u i ∉ U} ∈ l := Filter.not_frequently.mp hc
  have h3 : u '' {i | u i ∉ U} ∈ map u l :=
    Filter.mem_map.mpr (Filter.mem_of_superset h2 (fun i hi => ⟨i, hi, rfl⟩))
  have h4 : (U ∩ u '' {i | u i ∉ U}).Nonempty := by
    apply h.nonempty_of_mem
    rw [Filter.mem_inf_iff]
    exact ⟨U, hU, u '' {i | u i ∉ U}, h3, rfl⟩
  obtain ⟨y, hy1, i, hi, hyi⟩ := h4
  exact hi (hyi.symm ▸ hy1)

/-- `frobDist` is continuous on pairs. -/
theorem continuous_frobDist_pair {n : ℕ} :
    Continuous fun q : Curv4 n × Curv4 n => frobDist q.1 q.2 :=
  continuous_frobNorm.comp (continuous_fst.sub continuous_snd)

theorem nhds_prod_forall {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y}
    {P : X → Y → Prop} (h : ∀ᶠ p in 𝓝 ((x, y)), P p.1 p.2) :
    ∃ A ∈ 𝓝 x, ∃ B ∈ 𝓝 y, ∀ a ∈ A, ∀ b ∈ B, P a b := by
  obtain ⟨A, hA, B, hB, hAB⟩ :=
    mem_nhds_prod_iff.mp (show {p : X × Y | P p.1 p.2} ∈ 𝓝 (x, y) from h)
  exact ⟨A, hA, B, hB, fun a ha b hb =>
    hAB (show (a, b) ∈ A ×ˢ B from ⟨ha, hb⟩)⟩

/-- **Right upper semicontinuity** of `t ↦ truncSup G F Υ t`. -/
theorem truncSup_rusc [I.Boundaryless] [T2Space M] [CompactSpace M] [Nonempty M]
    (hLC : LCSmooth I M) (hLP : LapRmFrameParallel I M)
    {G : ℝ → SMet I M} {F : ℝ → Set (Curv4 (Module.finrank ℝ E))} {Υ : ℝ → ℝ}
    (hF : IsInvariantFamily F) {J : Set ℝ} (hJ : IsOpen J) {t : ℝ} (ht : t ∈ J)
    (hloc : HasLocalRep (I := I) (M := M) G F Υ J t)
    (hKne_t : (F t ∩ frobBall (Υ t)).Nonempty)
    (hpushW : ∃ δ > 0, ∃ C', ∀ h : ℝ, 0 < h → h ≤ δ → t + h ∈ J →
      ∀ S ∈ F t ∩ frobBall (Υ t),
        ∃ S' ∈ F (t + h) ∩ frobBall (Υ (t + h)), frobDist S' S ≤ C' * h) :
    ∀ ε > 0, ∃ δ > 0, ∀ h : ℝ, 0 < h → h ≤ δ → t + h ∈ J →
      truncSup G F Υ (t + h) ≤ truncSup G F Υ t + ε := by
  intro ε hε
  have hη2 : 0 < ε / 2 := by linarith
  by_contra hcon
  have hbad : ∀ δ : ℝ, 0 < δ → ∃ h : ℝ, 0 < h ∧ h ≤ δ ∧ t + h ∈ J ∧
      truncSup G F Υ (t + h) > truncSup G F Υ t + ε := by
    intro δ hδ
    by_contra hb
    apply hcon
    refine ⟨δ, hδ, fun h hh0 hhδ hth => ?_⟩
    by_contra hlt
    exact hb ⟨h, hh0, hhδ, hth, not_le.mp hlt⟩
  choose h hh0 hhδ hthJ hgt using fun m : ℕ => hbad (1 / (m + 1)) (by positivity)
  choose x _hxmax hxeq using fun m : ℕ =>
    exists_truncSup_eq (I := I) (M := M) hLC hLP hF (t + h m)
  obtain ⟨x_star, -, hclust⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set M)).exists_mapClusterPt (f := atTop) (u := x)
      (Filter.le_principal_iff.mpr Filter.univ_mem)
  obtain ⟨J', U, R, hJ'open, htJ', hJ'J, hU, hlocid, hRcont⟩ := hloc x_star
  obtain ⟨δ_P, hδ_P, C', hC'⟩ := hpushW
  have hhlim : Tendsto (fun m : ℕ => h m) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun m => norm_nonneg _) (fun m => ?_)
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    rw [Real.norm_eq_abs, abs_of_pos (hh0 m)]
    exact hhδ m
  have hthlim : Tendsto (fun m : ℕ => t + h m) atTop (𝓝 t) := by
    have h2 : Tendsto (fun m : ℕ => t + h m) atTop (𝓝 (t + 0)) :=
      tendsto_const_nhds.add hhlim
    simpa using h2
  -- the composite error along the local representation
  have hfst : Tendsto (fun p : ℝ × M => t + p.1) (𝓝 ((0 : ℝ), x_star)) (𝓝 t) := by
    have hct : Tendsto (fun _ : ℝ × M => t) (𝓝 ((0 : ℝ), x_star)) (𝓝 t) := tendsto_const_nhds
    have hid : Tendsto (fun p : ℝ × M => p.1) (𝓝 ((0 : ℝ), x_star)) (𝓝 (0 : ℝ)) := by
      have h := (tendsto_fst : Tendsto (fun p : ℝ × M => p.1)
        (𝓝 (0 : ℝ) ×ˢ 𝓝 x_star) (𝓝 (0 : ℝ)))
      rwa [← nhds_prod_eq] at h
    have h := hct.add hid
    simpa using h
  have hsnd : Tendsto (fun p : ℝ × M => p.2) (𝓝 ((0 : ℝ), x_star)) (𝓝 x_star) := by
    have h := (tendsto_snd : Tendsto (fun p : ℝ × M => p.2)
      (𝓝 (0 : ℝ) ×ˢ 𝓝 x_star) (𝓝 x_star))
    rwa [← nhds_prod_eq] at h
  have hmap : Tendsto (fun p : ℝ × M => (t + p.1, p.2)) (𝓝 ((0 : ℝ), x_star))
      (𝓝 (t, x_star)) := by
    have h := Tendsto.prodMk hfst hsnd
    rwa [← nhds_prod_eq] at h
  have h1t : Tendsto (fun p : ℝ × M => R (t + p.1) p.2) (𝓝 ((0 : ℝ), x_star))
      (𝓝 (R t x_star)) := by
    have h := (hRcont.tendsto).comp hmap
    simpa only [Function.comp_def] using h
  have h2t : Tendsto (fun p : ℝ × M => R t p.2) (𝓝 ((0 : ℝ), x_star)) (𝓝 (R t x_star)) := by
    have hmap2 : Tendsto (fun p : ℝ × M => (t, p.2)) (𝓝 ((0 : ℝ), x_star)) (𝓝 (t, x_star)) := by
      have hct : Tendsto (fun _ : ℝ × M => t) (𝓝 ((0 : ℝ), x_star)) (𝓝 t) := tendsto_const_nhds
      have h := Tendsto.prodMk hct hsnd
      rwa [← nhds_prod_eq] at h
    have h := (hRcont.tendsto).comp hmap2
    simpa only [Function.comp_def] using h
  have hpair : Tendsto (fun p : ℝ × M => (R (t + p.1) p.2, R t p.2)) (𝓝 ((0 : ℝ), x_star))
      (𝓝 (R t x_star, R t x_star)) := by
    have h := Tendsto.prodMk h1t h2t
    rwa [← nhds_prod_eq] at h
  have hΦev : ∀ᶠ p in 𝓝 ((0 : ℝ), x_star),
      frobDist (R (t + p.1) p.2) (R t p.2) ≤ ε / 2 := by
    have h0 : frobDist (R t x_star) (R t x_star) < ε / 2 := by
      rw [frobDist, sub_self, frobNorm_zero]
      linarith
    exact (continuous_frobDist_pair.tendsto (R t x_star, R t x_star) |>.comp hpair).eventually
      (Iic_mem_nhds h0)
  obtain ⟨A, hA, B, hB, hAB⟩ :=
    nhds_prod_forall (X := ℝ) (Y := M) (x := (0 : ℝ)) (y := x_star)
      (P := fun s z => frobDist (R (t + s) z) (R t z) ≤ ε / 2) hΦev
  obtain ⟨r, hr, hrA⟩ := Metric.mem_nhds_iff.mp hA
  have hfreq : ∃ᶠ m in atTop, x m ∈ B ∩ U :=
    MapClusterPt.frequently_mem hclust (Filter.inter_mem hB hU)
  have hevC : ∀ᶠ m in atTop, C' * h m ≤ ε / 2 := by
    rcases le_or_gt C' 0 with hC0 | hC0
    · filter_upwards with m
      have h1 : C' * h m ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hC0 (le_of_lt (hh0 m))
      linarith
    · have h1 : Tendsto (fun m : ℕ => C' * h m) atTop (𝓝 (C' * 0)) :=
        tendsto_const_nhds.mul hhlim
      have h2 : C' * 0 = 0 := mul_zero C'
      rw [h2] at h1
      exact h1.eventually (Iic_mem_nhds hη2)
  have hev : ∀ᶠ m in atTop, h m ∈ Metric.ball (0 : ℝ) r ∧ h m ≤ δ_P ∧
      C' * h m ≤ ε / 2 ∧ t + h m ∈ J' := by
    filter_upwards [hhlim.eventually (Metric.ball_mem_nhds (0 : ℝ) hr),
      hhlim.eventually (Iic_mem_nhds hδ_P), hevC,
      hthlim.eventually (hJ'open.mem_nhds htJ')] with m hm1 hm2 hm3 hm4
    exact ⟨hm1, hm2, hm3, hm4⟩
  obtain ⟨m, hxm, hm1, hm2, hm3, hm4⟩ := (hfreq.and_eventually hev).exists
  have hxmU : x m ∈ U := hxm.2
  have hΦm : frobDist (R (t + h m) (x m)) (R t (x m)) ≤ ε / 2 :=
    hAB (h m) (hrA hm1) (x m) hxm.1
  obtain ⟨S, hS, hSmin⟩ := exists_frobDist_min (Module.finrank ℝ E) (F t ∩ frobBall (Υ t))
    ((isClosed_fibre_of_isClosed_track hF.1 t).inter (isClosed_frobBall (Υ t))) hKne_t
    ⟨max (Υ t) 0, fun S hS => le_trans (frobBall_mem.mp hS.2) (le_max_left _ _)⟩ (R t (x m))
  obtain ⟨S', hS', hSS'⟩ := hC' (h m) (hh0 m) hm2 (hthJ m) S hS
  have hSS'' : frobDist S S' ≤ C' * h m := by rw [frobDist_comm]; exact hSS'
  have hlocs : frobInfDist (R (t + h m) (x m)) (F (t + h m) ∩ frobBall (Υ (t + h m)))
      = truncDist G F Υ (t + h m) (x m) := (hlocid (t + h m) hm4 (x m) hxmU).symm
  have hloct : frobInfDist (R t (x m)) (F t ∩ frobBall (Υ t)) = truncDist G F Υ t (x m) :=
    (hlocid t htJ' (x m) hxmU).symm
  have h1 : frobInfDist (R (t + h m) (x m)) (F (t + h m) ∩ frobBall (Υ (t + h m)))
      ≤ ε / 2 + truncDist G F Υ t (x m) + C' * h m := by
    have h2 : frobInfDist (R (t + h m) (x m)) (F (t + h m) ∩ frobBall (Υ (t + h m)))
        ≤ frobDist (R (t + h m) (x m)) S' := frobInfDist_le hS'
    have h3 : frobDist (R (t + h m) (x m)) S'
        ≤ frobDist (R (t + h m) (x m)) (R t (x m)) + frobDist (R t (x m)) S
          + frobDist S S' := by
      have htr := frobDist_triangle (R (t + h m) (x m)) (R t (x m)) S'
      have htr2 := frobDist_triangle (R t (x m)) S S'
      linarith
    have h4 : frobDist (R t (x m)) S = truncDist G F Υ t (x m) := by
      rw [← hloct]
      exact le_antisymm (le_frobInfDist hKne_t (fun S' hS' => hSmin S' hS'))
        (frobInfDist_le (S := S) hS)
    linarith [h2, h3, h4, hSS'', hΦm]
  have h5 : truncDist G F Υ t (x m) ≤ truncSup G F Υ t := truncDist_le_truncSup hLC hLP hF t (x m)
  have hchain : truncSup G F Υ (t + h m) ≤ truncSup G F Υ t + ε := by
    rw [hxeq m, ← hlocs]
    linarith [h1, h5, hm3]
  linarith [hchain, hgt m]

/-! ## The one-sided local representation and the endpoint `t = 0` -/

/-- **Right-handed local representation.**  For `s ≥ t` near `t` the truncated distance is the
Frobenius distance from the truncated fibre to a curvature array `R s z` which varies continuously
with `(s, z)`.  Unlike `HasLocalRep` this only asks for the representation on the *right* of `t`,
which is what one has at `t = 0` for a flow that is jointly smooth only on `[0, T)`. -/
abbrev HasRightRep (G : ℝ → SMet I M) (F : ℝ → Set (Curv4 (Module.finrank ℝ E)))
    (Υ : ℝ → ℝ) (t : ℝ) : Prop :=
  ∀ y : M, ∃ (J' : Set ℝ) (U : Set M) (R : ℝ → M → Curv4 (Module.finrank ℝ E)),
    IsOpen J' ∧ t ∈ J' ∧ U ∈ 𝓝 y ∧
    (∀ s ∈ J', t ≤ s → ∀ z ∈ U, truncDist G F Υ s z
      = frobInfDist (R s z) (F s ∩ frobBall (Υ s))) ∧
    ContinuousAt (fun p : ℝ × M => R p.1 p.2) (t, y)

/-- On an empty manifold the truncated supremum vanishes. -/
theorem truncSup_eq_zero [IsEmpty M] (G : ℝ → SMet I M)
    (F : ℝ → Set (Curv4 (Module.finrank ℝ E))) (Υ : ℝ → ℝ) (t : ℝ) :
    truncSup G F Υ t = 0 := by
  have huniv : (Set.univ : Set M) = ∅ := Set.univ_eq_empty_iff.mpr inferInstance
  rw [truncSup, huniv, Set.image_empty, Real.sSup_empty]

/-- **The right-handed local representation at `t = 0`.**  A flow that is jointly smooth only on the
half-open interval `[0, T)` still has a right-handed local representation at `0`: reparametrise
time by `τ ↦ τ²` (which turns `[0,T)` into an open interval around `0`), take the local
representation of the reparametrised data from `exists_local_rep` and pull it back along the
continuous map `s ↦ √s`. -/
theorem hasRightRep_zero [I.Boundaryless] [T2Space M]
    (hLC : LCSmooth I M) (hLP : LapRmFrameParallel I M)
    {G : ℝ → SMet I M} {F : ℝ → Set (Curv4 (Module.finrank ℝ E))}
    (hFrot : ∀ t (A : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ),
      A ∈ Matrix.orthogonalGroup (Fin (Module.finrank ℝ E)) ℝ → ∀ R ∈ F t, rot A R ∈ F t)
    {Υ : ℝ → ℝ} {T ρ : ℝ} (hT : 0 < T) (hρ : 0 < ρ) (hρT : ρ ^ 2 < T)
    (hG : JointSmooth G (Set.Ico 0 T)) :
    HasRightRep (I := I) (M := M) G F Υ 0 := by
  intro y
  have hG' : JointSmooth (Work.Diff.GE.cfq_sqFlow G) (Set.Ioo (-ρ) ρ) :=
    Work.Diff.GE.cfq_jointSmooth_sqFlow (I := I) (M := M) G hT hρ hρT hG
  obtain ⟨J', U, R, hJ'open, h0J', _hJ'J, hU, hlocid, hRcont⟩ :=
    exists_local_rep (I := I) (M := M) hLC hLP (G := Work.Diff.GE.cfq_sqFlow G)
      (J := Set.Ioo (-ρ) ρ) isOpen_Ioo hG'
      (F := fun τ => F (τ ^ 2)) (fun τ A hA R hR => hFrot (τ ^ 2) A hA R hR)
      (fun τ => Υ (τ ^ 2)) (t := 0) ⟨by linarith, hρ⟩ y
  refine ⟨Real.sqrt ⁻¹' J', U, fun s z => R (Real.sqrt s) z, ?_, ?_, hU, ?_, ?_⟩
  · exact hJ'open.preimage Real.continuous_sqrt
  · simpa only [Set.mem_preimage, Real.sqrt_zero] using h0J'
  · intro s hs h0s z hz
    have hsq : Real.sqrt s ^ 2 = s := Real.sq_sqrt h0s
    simpa only [truncDist, Work.Diff.GE.cfq_sqFlow, hsq] using hlocid (Real.sqrt s) hs z hz
  · have hcont : ContinuousAt (fun p : ℝ × M => (Real.sqrt p.1, p.2)) ((0 : ℝ), y) :=
      (Real.continuous_sqrt.continuousAt.comp continuousAt_fst).prodMk continuousAt_snd
    have hRcont' : ContinuousAt (fun p : ℝ × M => R p.1 p.2) ((Real.sqrt 0 : ℝ), y) := by
      simpa only [Real.sqrt_zero] using hRcont
    have h2 := ContinuousAt.comp (x := ((0 : ℝ), y))
      (f := fun p : ℝ × M => (Real.sqrt p.1, p.2)) hRcont' hcont
    simpa only [Function.comp_def] using h2

/-- A two-sided local representation restricts to a right-handed one. -/
theorem hasRightRep_of_localRep [I.Boundaryless] [T2Space M]
    {G : ℝ → SMet I M} {F : ℝ → Set (Curv4 (Module.finrank ℝ E))} {Υ : ℝ → ℝ} {J : Set ℝ}
    {t : ℝ} (hJ : IsOpen J) (ht : t ∈ J)
    (hloc : HasLocalRep (I := I) (M := M) G F Υ J t) :
    HasRightRep (I := I) (M := M) G F Υ t := by
  intro y
  obtain ⟨J', U, R, hJ'open, htJ', _hJ'J, hU, hlocid, hRcont⟩ := hloc y
  exact ⟨J', U, R, hJ'open, htJ', hU, fun s hs _ z hz => hlocid s hs z hz, hRcont⟩

/-- **Right lower semicontinuity** of `t ↦ truncSup G F Υ t`, in the one-sided form. -/
theorem truncSup_lsc_right_r [I.Boundaryless] [T2Space M] [CompactSpace M] [Nonempty M]
    (hLC : LCSmooth I M) (hLP : LapRmFrameParallel I M)
    {G : ℝ → SMet I M} {F : ℝ → Set (Curv4 (Module.finrank ℝ E))} {Υ : ℝ → ℝ}
    (hF : IsInvariantFamily F) (hΥ : Continuous Υ)
    {t δk : ℝ} (hδk : 0 < δk)
    (hloc : HasRightRep (I := I) (M := M) G F Υ t)
    (hKne : ∀ s : ℝ, t ≤ s → s ≤ t + δk → (F s ∩ frobBall (Υ s)).Nonempty) :
    ∀ ε > 0, ∃ δ > 0, ∀ s : ℝ, t ≤ s → s ≤ t + δ →
      truncSup G F Υ t ≤ truncSup G F Υ s + ε := by
  intro ε hε
  have hη3 : 0 < ε / 3 := by linarith
  by_contra hcon
  have hbad : ∀ δ : ℝ, 0 < δ → ∃ s : ℝ, t ≤ s ∧ s ≤ t + δ ∧
      truncSup G F Υ t > truncSup G F Υ s + ε := by
    intro δ hδ
    by_contra hb
    apply hcon
    refine ⟨δ, hδ, fun s hts hst => ?_⟩
    by_contra hlt
    exact hb ⟨s, hts, hst, not_le.mp hlt⟩
  choose s hst hδs hgt using fun m : ℕ => hbad (min (1 / (m + 1)) δk) (by positivity)
  have hsmk : ∀ m : ℕ, s m ≤ t + δk := by
    intro m
    have h1 : min (1 / ((m : ℝ) + 1)) δk ≤ δk := min_le_right _ _
    linarith [hδs m]
  obtain ⟨x₀, hx₀max, hx₀eq⟩ := exists_truncSup_eq (I := I) (M := M) hLC hLP hF t
  obtain ⟨J', U, R, hJ'open, htJ', hU, hlocid, hRcont⟩ := hloc x₀
  have hx₀U : x₀ ∈ U := mem_of_mem_nhds hU
  have htI : t ∈ Set.Icc t (t + δk) := ⟨le_rfl, by linarith [hδk]⟩
  obtain ⟨δ_S, hδ_S, hδ_Sprop⟩ := K_shrinks hF.1 hΥ isCompact_Icc htI hη3
  have hslim : Tendsto (fun m : ℕ => s m) atTop (𝓝 t) := by
    have h1 : Tendsto (fun m : ℕ => s m - t) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine squeeze_zero (fun m => norm_nonneg _) (fun m => ?_)
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      rw [Real.norm_eq_abs]
      have h := hδs m
      have h' := hst m
      have h2 : min (1 / ((m : ℝ) + 1)) δk ≤ 1 / ((m : ℝ) + 1) := min_le_left _ _
      rw [abs_le]
      constructor <;> linarith
    have h2 : Tendsto (fun m : ℕ => t + (s m - t)) atTop (𝓝 (t + 0)) :=
      tendsto_const_nhds.add h1
    simpa using h2
  have hevJ' : ∀ᶠ m in atTop, s m ∈ J' := hslim.eventually (hJ'open.mem_nhds htJ')
  have hevS : ∀ᶠ m in atTop, |s m - t| ≤ δ_S := by
    filter_upwards [hslim.eventually (Metric.ball_mem_nhds t hδ_S)] with m hm
    exact le_of_lt (by simpa [Real.dist_eq] using hm)
  have hevKne : ∀ᶠ m in atTop, (F (s m) ∩ frobBall (Υ (s m))).Nonempty :=
    Eventually.of_forall fun m => hKne (s m) (hst m) (hsmk m)
  have hevR : ∀ᶠ m in atTop, frobDist (R (s m) x₀) (R t x₀) ≤ ε / 3 := by
    have h1 : Tendsto (fun m : ℕ => (s m, x₀)) atTop (𝓝 (t, x₀)) := by
      have h : Tendsto (fun m : ℕ => (s m, x₀)) atTop (𝓝 t ×ˢ 𝓝 x₀) :=
        Tendsto.prodMk hslim tendsto_const_nhds
      rwa [← nhds_prod_eq] at h
    have h2 : Tendsto (fun m : ℕ => R (s m) x₀) atTop (𝓝 (R t x₀)) := by
      have h3 := (hRcont.tendsto).comp h1
      simpa only [Function.comp_def] using h3
    have h4 := tendsto_frobDist_zero h2
    exact h4.eventually (Iic_mem_nhds (by linarith))
  have hfinal : ∀ᶠ m in atTop, truncSup G F Υ t ≤ truncSup G F Υ (s m) + ε := by
    filter_upwards [hevJ', hevS, hevKne, hevR] with m hJ'm hSm hKne_m hRm
    have hstep : frobInfDist (R t x₀) (F t ∩ frobBall (Υ t))
        ≤ frobInfDist (R t x₀) (F (s m) ∩ frobBall (Υ (s m))) + ε / 3 := by
      have h1 : frobInfDist (R t x₀) (F t ∩ frobBall (Υ t)) - ε / 3
          ≤ frobInfDist (R t x₀) (F (s m) ∩ frobBall (Υ (s m))) := by
        refine le_frobInfDist hKne_m (fun S hS => ?_)
        obtain ⟨S', hS', hSS'⟩ := hδ_Sprop (s m) ⟨hst m, hsmk m⟩ hSm S hS
        have h2 : frobInfDist (R t x₀) (F t ∩ frobBall (Υ t)) ≤ frobDist (R t x₀) S' :=
          frobInfDist_le hS'
        have h3 : frobDist (R t x₀) S' ≤ frobDist (R t x₀) S + frobDist S S' :=
          frobDist_triangle _ _ _
        linarith
      linarith
    have hstep2 : frobInfDist (R t x₀) (F (s m) ∩ frobBall (Υ (s m)))
        ≤ frobDist (R t x₀) (R (s m) x₀)
          + frobInfDist (R (s m) x₀) (F (s m) ∩ frobBall (Υ (s m))) := by
      have h1 := abs_frobInfDist_sub_le hKne_m (R t x₀) (R (s m) x₀)
      have h2 := (abs_le.mp h1).2
      linarith
    have ht_eq : frobInfDist (R t x₀) (F t ∩ frobBall (Υ t)) = truncDist G F Υ t x₀ :=
      (hlocid t htJ' le_rfl x₀ hx₀U).symm
    have hs_eq : frobInfDist (R (s m) x₀) (F (s m) ∩ frobBall (Υ (s m)))
        = truncDist G F Υ (s m) x₀ := (hlocid (s m) hJ'm (hst m) x₀ hx₀U).symm
    have hsu : truncDist G F Υ (s m) x₀ ≤ truncSup G F Υ (s m) :=
      truncDist_le_truncSup hLC hLP hF (s m) x₀
    have hRm' : frobDist (R t x₀) (R (s m) x₀) ≤ ε / 3 := by
      rw [frobDist_comm]
      exact hRm
    rw [ht_eq] at hstep
    rw [hs_eq] at hstep2
    rw [hx₀eq]
    linarith [hstep, hstep2, hRm', hsu]
  rcases (hfinal.and (Eventually.of_forall hgt)).exists with ⟨m, hle, hgtm⟩
  linarith

/-- **Right upper semicontinuity** of `t ↦ truncSup G F Υ t`, in the one-sided form. -/
theorem truncSup_rusc_r [I.Boundaryless] [T2Space M] [CompactSpace M] [Nonempty M]
    (hLC : LCSmooth I M) (hLP : LapRmFrameParallel I M)
    {G : ℝ → SMet I M} {F : ℝ → Set (Curv4 (Module.finrank ℝ E))} {Υ : ℝ → ℝ}
    (hF : IsInvariantFamily F) {t δP C' : ℝ} (hδP : 0 < δP)
    (hloc : HasRightRep (I := I) (M := M) G F Υ t)
    (hKne_t : (F t ∩ frobBall (Υ t)).Nonempty)
    (hpushW : ∀ h : ℝ, 0 < h → h ≤ δP → ∀ S ∈ F t ∩ frobBall (Υ t),
        ∃ S' ∈ F (t + h) ∩ frobBall (Υ (t + h)), frobDist S' S ≤ C' * h) :
    ∀ ε > 0, ∃ δ > 0, δ ≤ δP ∧ ∀ h : ℝ, 0 < h → h ≤ δ →
      truncSup G F Υ (t + h) ≤ truncSup G F Υ t + ε := by
  intro ε hε
  have hη2 : 0 < ε / 2 := by linarith
  by_contra hcon
  have hbad : ∀ δ : ℝ, 0 < δ → δ ≤ δP → ∃ h : ℝ, 0 < h ∧ h ≤ δ ∧
      truncSup G F Υ (t + h) > truncSup G F Υ t + ε := by
    intro δ hδ hδle
    by_contra hb
    apply hcon
    refine ⟨δ, hδ, hδle, fun h hh0 hhδ => ?_⟩
    by_contra hlt
    exact hb ⟨h, hh0, hhδ, not_le.mp hlt⟩
  choose h hh0 hhδ hgt using fun m : ℕ =>
    hbad (min (1 / (m + 1)) δP) (by positivity) (min_le_right _ _)
  choose x _hxmax hxeq using fun m : ℕ =>
    exists_truncSup_eq (I := I) (M := M) hLC hLP hF (t + h m)
  obtain ⟨x_star, -, hclust⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set M)).exists_mapClusterPt (f := atTop) (u := x)
      (Filter.le_principal_iff.mpr Filter.univ_mem)
  obtain ⟨J', U, R, hJ'open, htJ', hU, hlocid, hRcont⟩ := hloc x_star
  have hhlim : Tendsto (fun m : ℕ => h m) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun m => norm_nonneg _) (fun m => ?_)
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    rw [Real.norm_eq_abs, abs_of_pos (hh0 m)]
    exact le_trans (hhδ m) (min_le_left _ _)
  have hthlim : Tendsto (fun m : ℕ => t + h m) atTop (𝓝 t) := by
    have h2 : Tendsto (fun m : ℕ => t + h m) atTop (𝓝 (t + 0)) :=
      tendsto_const_nhds.add hhlim
    simpa using h2
  -- the composite error along the local representation
  have hfst : Tendsto (fun p : ℝ × M => t + p.1) (𝓝 ((0 : ℝ), x_star)) (𝓝 t) := by
    have hct : Tendsto (fun _ : ℝ × M => t) (𝓝 ((0 : ℝ), x_star)) (𝓝 t) := tendsto_const_nhds
    have hid : Tendsto (fun p : ℝ × M => p.1) (𝓝 ((0 : ℝ), x_star)) (𝓝 (0 : ℝ)) := by
      have h := (tendsto_fst : Tendsto (fun p : ℝ × M => p.1)
        (𝓝 (0 : ℝ) ×ˢ 𝓝 x_star) (𝓝 (0 : ℝ)))
      rwa [← nhds_prod_eq] at h
    have h := hct.add hid
    simpa using h
  have hsnd : Tendsto (fun p : ℝ × M => p.2) (𝓝 ((0 : ℝ), x_star)) (𝓝 x_star) := by
    have h := (tendsto_snd : Tendsto (fun p : ℝ × M => p.2)
      (𝓝 (0 : ℝ) ×ˢ 𝓝 x_star) (𝓝 x_star))
    rwa [← nhds_prod_eq] at h
  have hmap : Tendsto (fun p : ℝ × M => (t + p.1, p.2)) (𝓝 ((0 : ℝ), x_star))
      (𝓝 (t, x_star)) := by
    have h := Tendsto.prodMk hfst hsnd
    rwa [← nhds_prod_eq] at h
  have h1t : Tendsto (fun p : ℝ × M => R (t + p.1) p.2) (𝓝 ((0 : ℝ), x_star))
      (𝓝 (R t x_star)) := by
    have h := (hRcont.tendsto).comp hmap
    simpa only [Function.comp_def] using h
  have h2t : Tendsto (fun p : ℝ × M => R t p.2) (𝓝 ((0 : ℝ), x_star)) (𝓝 (R t x_star)) := by
    have hmap2 : Tendsto (fun p : ℝ × M => (t, p.2)) (𝓝 ((0 : ℝ), x_star)) (𝓝 (t, x_star)) := by
      have hct : Tendsto (fun _ : ℝ × M => t) (𝓝 ((0 : ℝ), x_star)) (𝓝 t) := tendsto_const_nhds
      have h := Tendsto.prodMk hct hsnd
      rwa [← nhds_prod_eq] at h
    have h := (hRcont.tendsto).comp hmap2
    simpa only [Function.comp_def] using h
  have hpair : Tendsto (fun p : ℝ × M => (R (t + p.1) p.2, R t p.2)) (𝓝 ((0 : ℝ), x_star))
      (𝓝 (R t x_star, R t x_star)) := by
    have h := Tendsto.prodMk h1t h2t
    rwa [← nhds_prod_eq] at h
  have hΦev : ∀ᶠ p in 𝓝 ((0 : ℝ), x_star),
      frobDist (R (t + p.1) p.2) (R t p.2) ≤ ε / 2 := by
    have h0 : frobDist (R t x_star) (R t x_star) < ε / 2 := by
      rw [frobDist, sub_self, frobNorm_zero]
      linarith
    exact (continuous_frobDist_pair.tendsto (R t x_star, R t x_star) |>.comp hpair).eventually
      (Iic_mem_nhds h0)
  obtain ⟨A, hA, B, hB, hAB⟩ :=
    nhds_prod_forall (X := ℝ) (Y := M) (x := (0 : ℝ)) (y := x_star)
      (P := fun s z => frobDist (R (t + s) z) (R t z) ≤ ε / 2) hΦev
  obtain ⟨r, hr, hrA⟩ := Metric.mem_nhds_iff.mp hA
  have hfreq : ∃ᶠ m in atTop, x m ∈ B ∩ U :=
    MapClusterPt.frequently_mem hclust (Filter.inter_mem hB hU)
  have hevC : ∀ᶠ m in atTop, C' * h m ≤ ε / 2 := by
    rcases le_or_gt C' 0 with hC0 | hC0
    · filter_upwards with m
      have h1 : C' * h m ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hC0 (le_of_lt (hh0 m))
      linarith
    · have h1 : Tendsto (fun m : ℕ => C' * h m) atTop (𝓝 (C' * 0)) :=
        tendsto_const_nhds.mul hhlim
      have h2 : C' * 0 = 0 := mul_zero C'
      rw [h2] at h1
      exact h1.eventually (Iic_mem_nhds hη2)
  have hev : ∀ᶠ m in atTop, h m ∈ Metric.ball (0 : ℝ) r ∧ C' * h m ≤ ε / 2 ∧
      t + h m ∈ J' := by
    filter_upwards [hhlim.eventually (Metric.ball_mem_nhds (0 : ℝ) hr), hevC,
      hthlim.eventually (hJ'open.mem_nhds htJ')] with m hm1 hm3 hm4
    exact ⟨hm1, hm3, hm4⟩
  obtain ⟨m, hxm, hm1, hm3, hm4⟩ := (hfreq.and_eventually hev).exists
  have hxmU : x m ∈ U := hxm.2
  have hΦm : frobDist (R (t + h m) (x m)) (R t (x m)) ≤ ε / 2 :=
    hAB (h m) (hrA hm1) (x m) hxm.1
  obtain ⟨S, hS, hSmin⟩ := exists_frobDist_min (Module.finrank ℝ E) (F t ∩ frobBall (Υ t))
    ((isClosed_fibre_of_isClosed_track hF.1 t).inter (isClosed_frobBall (Υ t))) hKne_t
    ⟨max (Υ t) 0, fun S hS => le_trans (frobBall_mem.mp hS.2) (le_max_left _ _)⟩ (R t (x m))
  obtain ⟨S', hS', hSS'⟩ := hpushW (h m) (hh0 m) (le_trans (hhδ m) (min_le_right _ _)) S hS
  have hSS'' : frobDist S S' ≤ C' * h m := by rw [frobDist_comm]; exact hSS'
  have hlocs : frobInfDist (R (t + h m) (x m)) (F (t + h m) ∩ frobBall (Υ (t + h m)))
      = truncDist G F Υ (t + h m) (x m) :=
    (hlocid (t + h m) hm4 (by linarith [hh0 m]) (x m) hxmU).symm
  have hloct : frobInfDist (R t (x m)) (F t ∩ frobBall (Υ t)) = truncDist G F Υ t (x m) :=
    (hlocid t htJ' le_rfl (x m) hxmU).symm
  have h1 : frobInfDist (R (t + h m) (x m)) (F (t + h m) ∩ frobBall (Υ (t + h m)))
      ≤ ε / 2 + truncDist G F Υ t (x m) + C' * h m := by
    have h2 : frobInfDist (R (t + h m) (x m)) (F (t + h m) ∩ frobBall (Υ (t + h m)))
        ≤ frobDist (R (t + h m) (x m)) S' := frobInfDist_le hS'
    have h3 : frobDist (R (t + h m) (x m)) S'
        ≤ frobDist (R (t + h m) (x m)) (R t (x m)) + frobDist (R t (x m)) S
          + frobDist S S' := by
      have htr := frobDist_triangle (R (t + h m) (x m)) (R t (x m)) S'
      have htr2 := frobDist_triangle (R t (x m)) S S'
      linarith
    have h4 : frobDist (R t (x m)) S = truncDist G F Υ t (x m) := by
      rw [← hloct]
      exact le_antisymm (le_frobInfDist hKne_t (fun S' hS' => hSmin S' hS'))
        (frobInfDist_le (S := S) hS)
    linarith [h2, h3, h4, hSS'', hΦm]
  have h5 : truncDist G F Υ t (x m) ≤ truncSup G F Υ t := truncDist_le_truncSup hLC hLP hF t (x m)
  have hchain : truncSup G F Υ (t + h m) ≤ truncSup G F Υ t + ε := by
    rw [hxeq m, ← hlocs]
    linarith [h1, h5, hm3]
  linarith [hchain, hgt m]


open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology Matrix
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Filter

theorem sup_dist_regular
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M] [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : Submission.Diff.LCSmooth I M) (hLP : Submission.Diff.LapRmFrameParallel I M)
    {G : ℝ → Submission.Diff.SMet I M} {T : ℝ} (hflow : Submission.Diff.IsRicciFlow G T)
    {F : ℝ → Set (Submission.Diff.Alg.Curv4 (Module.finrank ℝ E))}
    (hF : Submission.Diff.Alg.IsInvariantFamily F)
    {Υ : ℝ → ℝ} (hΥ : Continuous Υ)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hbT : b < T)
    (hKne : ∀ t ∈ Set.Icc a b, (F t ∩ Work.Diff.MP.frobBall (Υ t)).Nonempty)
    (hpush : ∀ t ∈ Set.Ico a b, ∃ δ > 0, ∃ C', ∀ h : ℝ, 0 < h → h ≤ δ →
      ∀ S ∈ F t ∩ Work.Diff.MP.frobBall (Υ t),
        ∃ S' ∈ F (t + h) ∩ Work.Diff.MP.frobBall (Υ (t + h)),
          Work.Diff.MP.frobDist S' (S + h • Submission.Diff.Alg.Q S) ≤ C' * h ^ 2 ∧
          Work.Diff.MP.frobDist S' S ≤ C' * h) :
    (∀ t ∈ Set.Icc a b, ∀ ε > 0, ∃ δ > 0, ∀ s ∈ Set.Icc a b, |s - t| ≤ δ →
      Work.Diff.MP.truncSup G F Υ t ≤ Work.Diff.MP.truncSup G F Υ s + ε) ∧
    (∀ t ∈ Set.Ico a b, ∀ ε > 0, ∃ δ > 0, ∀ h : ℝ, 0 < h → h ≤ δ → t + h ≤ b →
      Work.Diff.MP.truncSup G F Υ (t + h) ≤ Work.Diff.MP.truncSup G F Υ t + ε)    := by
  by_cases hne : Nonempty M
  · haveI : Nonempty M := hne
    by_cases hb0 : b = 0
    · -- the interval `[a,b]` collapses to `{0}`
      have haz : a = 0 := le_antisymm (by rw [hb0] at hab; exact hab) ha
      refine ⟨?_, ?_⟩
      · intro t ht ε hε
        have h1 : t ≤ 0 := by rw [hb0] at ht; exact ht.2
        have h2 : 0 ≤ t := by rw [haz] at ht; exact ht.1
        have ht0 : t = 0 := le_antisymm h1 h2
        subst ht0
        refine ⟨1, one_pos, fun s hs _ => ?_⟩
        have hs1 : s ≤ 0 := by rw [hb0] at hs; exact hs.2
        have hs2 : 0 ≤ s := by rw [haz] at hs; exact hs.1
        have hs0 : s = 0 := le_antisymm hs1 hs2
        subst hs0
        linarith
      · intro t ht ε hε
        exfalso
        have h1 : t < 0 := by rw [hb0] at ht; exact ht.2
        have h2 : 0 ≤ t := by rw [haz] at ht; exact ht.1
        linarith
    · have hbpos : 0 < b := lt_of_le_of_ne (le_trans ha hab) (Ne.symm hb0)
      have hTpos : 0 < T := lt_of_lt_of_le hbpos (le_of_lt hbT)
      -- the right-handed local representation at time `0`, via the time reparametrisation `τ ↦ τ²`
      have hrep0 : HasRightRep (I := I) (M := M) G F Υ 0 := by
        refine hasRightRep_zero (I := I) (M := M) hLC hLP
          (hFrot := fun τ A hA R hR => hF.2.2.2.1 τ A hA R hR) (ρ := (Real.sqrt b + Real.sqrt T) / 2)
          hTpos ?_ ?_ hflow.1
        · have h1 : 0 < Real.sqrt b := Real.sqrt_pos.mpr hbpos
          have h2 : 0 < Real.sqrt T := Real.sqrt_pos.mpr hTpos
          positivity
        have hx : Real.sqrt b < Real.sqrt T := Real.sqrt_lt_sqrt (le_of_lt hbpos) hbT
        have hxsq : Real.sqrt b ^ 2 = b := Real.sq_sqrt (le_of_lt hbpos)
        have hysq : Real.sqrt T ^ 2 = T := Real.sq_sqrt (le_of_lt hTpos)
        have hypos : 0 < Real.sqrt T := Real.sqrt_pos.mpr hTpos
        have hxy : Real.sqrt b * Real.sqrt T < Real.sqrt T * Real.sqrt T :=
          mul_lt_mul_of_pos_right hx hypos
        have h4 : ((Real.sqrt b + Real.sqrt T) / 2) ^ 2 * 4 = (Real.sqrt b + Real.sqrt T) ^ 2 := by
          ring
        have h5 : (Real.sqrt b + Real.sqrt T) ^ 2 < 4 * T := by
          nlinarith [hxsq, hysq, hx, hxy, Real.sqrt_nonneg b, Real.sqrt_nonneg T]
        nlinarith [h4, h5]
      -- the right-handed local representation at a positive time, from an open interval inside `[0,T)`
      have hrep_pos : ∀ t : ℝ, 0 < t → t < T →
          HasRightRep (I := I) (M := M) G F Υ t := by
        intro t ht0 htT
        let η : ℝ := min (t / 2) ((T - t) / 2)
        have hηpos : 0 < η := lt_min (by linarith) (by linarith)
        have hηt : η ≤ t / 2 := min_le_left _ _
        have hηT : η ≤ (T - t) / 2 := min_le_right _ _
        have hsub : Set.Ioo (t - η) (t + η) ⊆ Set.Ico 0 T := by
          intro s hs
          exact ⟨by linarith [hs.1, hηt, ht0], by linarith [hs.2, hηT, htT]⟩
        have hJopen : IsOpen (Set.Ioo (t - η) (t + η)) := isOpen_Ioo
        have htJ : t ∈ Set.Ioo (t - η) (t + η) := ⟨by linarith, by linarith⟩
        have hGJ : JointSmooth G (Set.Ioo (t - η) (t + η)) :=
          hflow.1.mono (Set.prod_mono hsub (Set.subset_univ _))
        exact hasRightRep_of_localRep (I := I) (M := M) hJopen htJ
          (hasLocalRep_of_jointSmooth (I := I) (M := M) hLC hLP hJopen hGJ
            (fun τ A hA R hR => hF.2.2.2.1 τ A hA R hR) Υ htJ)
      refine ⟨?_, ?_⟩
      · -- (1) lower semicontinuity of `t ↦ truncSup G F Υ t`
        intro t ht ε hε
        have htT : t < T := lt_of_le_of_lt ht.2 hbT
        by_cases ht0 : 0 < t
        · have hrepT : HasRightRep (I := I) (M := M) G F Υ t := hrep_pos t ht0 htT
          have hright : t < b → ∃ δ > 0, ∀ s : ℝ, t ≤ s → |s - t| ≤ δ →
              truncSup G F Υ t ≤ truncSup G F Υ s + ε := by
            intro htb
            have hδk : 0 < b - t := by linarith
            have hKn : ∀ s : ℝ, t ≤ s → s ≤ t + (b - t) →
                (F s ∩ frobBall (Υ s)).Nonempty := by
              intro s hts hs
              exact hKne s ⟨le_trans ht.1 hts, by linarith⟩
            obtain ⟨δ, hδ, hprop⟩ :=
              truncSup_lsc_right_r (I := I) (M := M) hLC hLP hF hΥ hδk hrepT hKn ε hε
            refine ⟨δ, hδ, fun s hts hst => hprop s hts ?_⟩
            have h' : s - t ≤ δ := (abs_le.mp hst).2
            linarith
          have hleft : a < t → ∃ δ > 0, ∀ s : ℝ, s ∈ Set.Icc a b → s ≤ t →
              |s - t| ≤ δ → truncSup G F Υ t ≤ truncSup G F Υ s + ε := by
            intro hat
            let η : ℝ := min (t / 2) ((T - t) / 2)
            have hηpos : 0 < η := lt_min (by linarith) (by linarith [htT])
            have hηt : η ≤ t / 2 := min_le_left _ _
            have hηT : η ≤ (T - t) / 2 := min_le_right _ _
            have hsub : Set.Ioo (t - η) (t + η) ⊆ Set.Ico 0 T := by
              intro s hs
              exact ⟨by linarith [hs.1, hηt, ht0], by linarith [hs.2, hηT, htT]⟩
            have hJopen : IsOpen (Set.Ioo (t - η) (t + η)) := isOpen_Ioo
            have htJ : t ∈ Set.Ioo (t - η) (t + η) := ⟨by linarith, by linarith⟩
            have hGJ : JointSmooth G (Set.Ioo (t - η) (t + η)) :=
              hflow.1.mono (Set.prod_mono hsub (Set.subset_univ _))
            have hloc := hasLocalRep_of_jointSmooth (I := I) (M := M) hLC hLP hJopen hGJ
              (fun τ A hA R hR => hF.2.2.2.1 τ A hA R hR) Υ htJ
            let δk : ℝ := min η ((t - a) / 2)
            have hδkpos : 0 < δk := lt_min hηpos (by linarith)
            have hδka : δk ≤ (t - a) / 2 := min_le_right _ _
            have hKn : ∀ s ∈ Set.Ioo (t - η) (t + η), s ≤ t → |s - t| ≤ δk →
                (F s ∩ frobBall (Υ s)).Nonempty := by
              intro s hs hst hst'
              refine hKne s ⟨?_, le_trans hst ht.2⟩
              have h1 : t - δk ≤ s := by linarith [(abs_le.mp hst').1]
              have h2 : a < t - δk := by linarith [hδka, hat]
              linarith
            obtain ⟨δ₀, hδ₀, hprop⟩ :=
              truncSup_lsc_left (I := I) (M := M) hLC hLP hF hΥ hJopen htJ hδkpos hloc hKn ε hε
            refine ⟨min δ₀ (η / 2), lt_min hδ₀ (by linarith), fun s hs hst hst' => ?_⟩
            have h1 : t - η < s := by
              have h2 : -(min δ₀ (η / 2)) ≤ s - t := (abs_le.mp hst').1
              have h3 : min δ₀ (η / 2) ≤ η / 2 := min_le_right _ _
              linarith
            have h2 : s < t + η := by linarith
            exact hprop s ⟨h1, h2⟩ hst (le_trans hst' (min_le_left _ _))
          rcases lt_or_ge a t with hat | hta
          · rcases lt_or_ge t b with htb | hbt
            · obtain ⟨δ₁, hδ₁, hp₁⟩ := hleft hat
              obtain ⟨δ₂, hδ₂, hp₂⟩ := hright htb
              refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun s hs hst => ?_⟩
              rcases le_or_gt s t with hst' | hst'
              · exact hp₁ s hs hst' (le_trans hst (min_le_left _ _))
              · exact hp₂ s (le_of_lt hst') (le_trans hst (min_le_right _ _))
            · have htb' : t = b := le_antisymm ht.2 hbt
              obtain ⟨δ₁, hδ₁, hp₁⟩ := hleft hat
              exact ⟨δ₁, hδ₁, fun s hs hst => hp₁ s hs (by rw [htb']; exact hs.2) hst⟩
          · have hta' : t = a := le_antisymm hta ht.1
            rcases lt_or_ge t b with htb | hbt
            · obtain ⟨δ₂, hδ₂, hp₂⟩ := hright htb
              exact ⟨δ₂, hδ₂, fun s hs hst => hp₂ s (by rw [hta']; exact hs.1) hst⟩
            · refine ⟨1, one_pos, fun s hs hst => ?_⟩
              have hste : s = t := le_antisymm (le_trans hs.2 hbt) (by rw [hta']; exact hs.1)
              rw [hste]
              linarith
        · -- `t = 0`
          have ht_eq : t = 0 := le_antisymm (le_of_not_gt ht0) (le_trans ha ht.1)
          have haz : a = 0 := le_antisymm (by rw [ht_eq] at ht; exact ht.1) ha
          have hKn : ∀ s : ℝ, 0 ≤ s → s ≤ 0 + b → (F s ∩ frobBall (Υ s)).Nonempty := by
            intro s hs0 hsb
            refine hKne s ⟨?_, by linarith⟩
            rw [haz]; exact hs0
          obtain ⟨δ, hδ, hprop⟩ :=
            truncSup_lsc_right_r (I := I) (M := M) hLC hLP hF hΥ hbpos hrep0 hKn ε hε
          refine ⟨δ, hδ, fun s hs hst => ?_⟩
          have h' : |s - t| ≤ δ := hst
          rw [ht_eq] at h' ⊢
          refine hprop s (le_trans ha hs.1) ?_
          have h2 : s - 0 ≤ δ := (abs_le.mp h').2
          linarith
      · -- (2) right upper semicontinuity of `t ↦ truncSup G F Υ t`
        intro t ht ε hε
        have htT : t < T := lt_trans ht.2 hbT
        have hKne_t : (F t ∩ frobBall (Υ t)).Nonempty := hKne t ⟨ht.1, le_of_lt ht.2⟩
        obtain ⟨δP, hδP, C', hC'⟩ := hpush t ht
        have hpushW : ∀ h : ℝ, 0 < h → h ≤ δP → ∀ S ∈ F t ∩ frobBall (Υ t),
            ∃ S' ∈ F (t + h) ∩ frobBall (Υ (t + h)), frobDist S' S ≤ C' * h := by
          intro h hh0 hhδ S hS
          obtain ⟨S', hS', _hSq, hSlin⟩ := hC' h hh0 hhδ S hS
          exact ⟨S', hS', hSlin⟩
        by_cases ht0 : 0 < t
        · have hrepT : HasRightRep (I := I) (M := M) G F Υ t := hrep_pos t ht0 htT
          obtain ⟨δ, hδ, _hδle, hprop⟩ :=
            truncSup_rusc_r (I := I) (M := M) hLC hLP hF hδP hrepT hKne_t hpushW ε hε
          exact ⟨δ, hδ, fun h hh0 hhδ _hb => hprop h hh0 hhδ⟩
        · have ht_eq : t = 0 := le_antisymm (le_of_not_gt ht0) (le_trans ha ht.1)
          rw [ht_eq] at hKne_t hpushW ⊢
          obtain ⟨δ, hδ, _hδle, hprop⟩ :=
            truncSup_rusc_r (I := I) (M := M) hLC hLP hF hδP hrep0 hKne_t hpushW ε hε
          exact ⟨δ, hδ, fun h hh0 hhδ _hb => hprop h hh0 hhδ⟩
  · -- empty manifold
    haveI : IsEmpty M := ⟨fun x => hne ⟨x⟩⟩
    refine ⟨?_, ?_⟩
    · intro t ht ε hε
      refine ⟨1, one_pos, fun s hs hst => ?_⟩
      simp only [truncSup_eq_zero]
      linarith
    · intro t ht ε hε
      refine ⟨1, one_pos, fun h hh0 hhδ hb => ?_⟩
      simp only [truncSup_eq_zero]
      linarith

end Work.Diff.MP
