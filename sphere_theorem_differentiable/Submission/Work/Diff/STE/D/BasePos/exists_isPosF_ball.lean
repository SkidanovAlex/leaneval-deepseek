/-
# Layer D, base-generalised positivity: the ball of coefficients with positive definite foreground

The corrected Galerkin scheme of Layer D runs on the *base-generalised* foreground

  `fore a₀ D ε c = a₀ + genMap D ε c`,

where `a₀` is an arbitrary smooth positive definite section of the bundle of bilinear forms (in the
intended application a smoothed background metric) and `genMap D ε c = ∑_z c z • jSym D ε z` is the
finite linear combination of the symmetrised spanning family.  For the ODE `c' = psiConcB c` to be
run in the Galerkin space one needs the *positivity set*

  `IsPosF a₀ D ε c := ∀ x v, v ≠ 0 → 0 < fore a₀ D ε c x v v`

to be a neighbourhood of `c = 0`; this module produces that neighbourhood in ball form.

## Proof

`genMap D ε c` is a linear combination of the `jSym z`, for which the workspace already proves the
*upper bound*

  `|genMap D ε c x v v| ≤ (∑_z |c z|) · K · g₀(x)(v,v)`,  `K = 2 (√d₀)⁻¹`

(`Work.Diff.STE.D.abs_genMap_apply_le`, with `d₀` the uniform lower bound for the volume densities
`Work.Diff.STE.B3.dens_lower_bound`).  So it is enough to know that `a₀` dominates a multiple of
`g₀` *globally*:

  `∃ λ > 0, ∀ x v, λ · g₀(x)(v,v) ≤ a₀(x)(v,v)`.

That is a *global* statement (the perturbation `genMap` is not compactly supported inside a single
chart: the closed `σ i`-coordinate balls `pt i '' closedBall (0, σ i)` of the `B3Data` cover `M`,
`B3Data.hcover`), but it reduces to *per-chart* statements, because the `cover` is by the chart
balls: for `x ∈ M` with chart index `i` and coordinates `z = coord i x` (`‖z‖ ≤ σ i`), the point `x`
is `pt i z`, and the per-chart statement is the comparison of `a₀` and `g₀` on the *compact*
coordinate ball `coordBall (x₀ i) (σ i)`:

* `Work.Diff.STE.D.BasePos.bil_uniform_lower`: some `δ i > 0` with
  `δ i ‖a‖² ≤ a₀(p)(v_a, v_a)` on that ball (`v_a = frameVector I (x₀ i) p a`),
* `Work.Diff.STE.D.BasePos.smet_uniform_upper`: some `C i > 0` with
  `g₀(p)(v_a,v_a) ≤ C i ‖a‖²` on that ball,

and `λ i = δ i / C i` then works on the chart ball (`‖a‖` is the coordinate norm, and every tangent
vector is the frame vector of its trivialisation coordinates).  Since `ι₀` is finite,
`λ = min_i λ i > 0` is uniform, and `δ = min 1 (lam / (2 K (N+1)))` (`N` the number of coefficients)
gives, for `‖c‖ < δ`,

  `fore a₀ D ε c x v v ≥ λ g₀(v,v) - (∑_z |c z|) K g₀(v,v) > (λ/2) g₀(v,v) > 0`.

If `ι₀` is empty then `M` is empty (`B3Data.hcover`) and any `δ` works.
-/
import Mathlib
import Submission.Work.Diff.STE.D.Base.Defs
import Submission.Work.Diff.STE.D.psi.Positivity
import Submission.Work.Diff.STE.D.BasePos.bil_uniform_lower
import Submission.Work.Diff.STE.D.BasePos.smet_uniform_upper

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open Classical
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.STE.D.BasePos

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

noncomputable section

/-! ## The coordinate ball is compact -/

/-- The closed coordinate ball of radius `r` about the centre of the chart at `x₀`. -/
lemma coordBall_eq_image (x₀ : M) (r : ℝ) :
    Work.Diff.STE.coordBall (I := I) (M := M) x₀ r
      = Work.Diff.STE.flatToE (I := I) x₀ ''
        Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) r := by
  ext y
  constructor
  · intro hy
    refine ⟨(Module.finBasis ℝ E).equivFun y
      - (Module.finBasis ℝ E).equivFun ((extChartAt I x₀) x₀), ?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
      simpa only [Work.Diff.STE.coordBall, Set.mem_ofPred_eq] using hy
    · simp only [Work.Diff.STE.flatToE]
      rw [show (Module.finBasis ℝ E).equivFun ((extChartAt I x₀) x₀)
          + ((Module.finBasis ℝ E).equivFun y
            - (Module.finBasis ℝ E).equivFun ((extChartAt I x₀) x₀))
          = (Module.finBasis ℝ E).equivFun y from by abel]
      exact LinearEquiv.symm_apply_apply _ _
  · rintro ⟨z, hz, rfl⟩
    rw [Work.Diff.STE.flatToE_mem_coordBall]
    simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hz

/-- **The closed coordinate ball of a chart is compact.**  It is the image of the compact closed ball
of the flat coordinates under the affine map `flatToE`. -/
lemma isCompact_coordBall (x₀ : M) (r : ℝ) :
    IsCompact (Work.Diff.STE.coordBall (I := I) (M := M) x₀ r) := by
  rw [coordBall_eq_image (I := I) (M := M) x₀ r]
  refine IsCompact.image ?_ ?_
  · exact isCompact_closedBall _ _
  · have h1 : Continuous fun z : Fin (Module.finrank ℝ E) → ℝ =>
        (Module.finBasis ℝ E).equivFun ((extChartAt I x₀) x₀) + z :=
      continuous_const.add continuous_id
    have h2 : Continuous fun w : Fin (Module.finrank ℝ E) → ℝ => (Module.finBasis ℝ E).equivFun.symm w :=
      (((Module.finBasis ℝ E).equivFun.symm :
        (Fin (Module.finrank ℝ E) → ℝ) ≃ₗ[ℝ] E).toContinuousLinearMap).continuous
    exact h2.comp h1

/-- **Every tangent vector is the frame vector of its coordinates in the chart at `x₀`.**  The
coordinates are read off from the trivialisation of the tangent bundle at `x₀`; on the chart source
the frame vector of those coordinates is the vector itself. -/
lemma exists_frameVector_eq (x₀ : M) {x : M} (hx : x ∈ (chartAt H x₀).source)
    (v : TangentSpace I x) :
    ∃ a : E, Submission.Geodesic.frameVector (I := I) x₀ x a = v := by
  refine ⟨(FiberBundle.trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ x v, ?_⟩
  show (FiberBundle.trivializationAt E (TangentSpace I) x₀).symmL ℝ x
      ((FiberBundle.trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ x v) = v
  exact Bundle.Trivialization.symmL_continuousLinearMapAt _ (R := ℝ)
    (by rwa [TangentBundle.trivializationAt_baseSet]) v

/-- Membership in the closed coordinate ball, in flat coordinates. -/
lemma mem_coordBall_iff (x₀ : M) (r : ℝ) {y : E} :
    y ∈ Work.Diff.STE.coordBall (I := I) (M := M) x₀ r ↔
      ∃ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ ≤ r ∧ Work.Diff.STE.flatToE (I := I) x₀ z = y := by
  rw [coordBall_eq_image (I := I) (M := M) x₀ r]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, by simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, by simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hz, rfl⟩

/-! ## The per-chart comparison of `a₀` and `g₀` -/

/-- **On one chart ball, `a₀` dominates a positive multiple of `g₀`.**  For the chart of `D` with
index `i`, there is `λ > 0` with `λ g₀(v_a,v_a) ≤ a₀(v_a,v_a)` for every flat coordinate
`z` with `‖z‖ ≤ σ i` and every `a : E`, `v_a = frameVector I (x₀ i) (pt i z) a`. -/
lemma perChart_bound
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (a₀ : Work.Diff.STE.Bil (I := I) (M := M))
    (ha₀ : Work.Diff.STE.D.ChartData (I := I) (M := M) a₀)
    (hpos : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < a₀ x v v) (i : ι₀) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ (z : Fin (Module.finrank ℝ E) → ℝ), ‖z‖ ≤ D.σ i → ∀ a : E,
      lam * g₀.inner (D.pt i z)
            (Submission.Geodesic.frameVector (I := I) (D.x₀ i) (D.pt i z) a)
            (Submission.Geodesic.frameVector (I := I) (D.x₀ i) (D.pt i z) a)
        ≤ a₀ (D.pt i z)
            (Submission.Geodesic.frameVector (I := I) (D.x₀ i) (D.pt i z) a)
            (Submission.Geodesic.frameVector (I := I) (D.x₀ i) (D.pt i z) a) := by
  set K' : Set E := Work.Diff.STE.coordBall (I := I) (M := M) (D.x₀ i) (D.σ i) with hK'
  have hK'c : IsCompact K' := isCompact_coordBall (I := I) (M := M) (D.x₀ i) (D.σ i)
  have hK't : K' ⊆ (extChartAt I (D.x₀ i)).target := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := (mem_coordBall_iff (I := I) (M := M) (x₀ := D.x₀ i)
      (r := D.σ i)).mp hy
    exact D.htarget i z (by linarith [hz, D.hσ i])
  obtain ⟨δ, hδpos, hδb⟩ :=
    bil_uniform_lower (I := I) (M := M) a₀ ha₀ hpos (D.x₀ i) K' hK'c hK't
  obtain ⟨C, hCpos, hCb⟩ :=
    smet_uniform_upper (I := I) (M := M) g₀ (D.x₀ i) K' hK'c hK't
  refine ⟨δ / C, div_pos hδpos hCpos, fun z hz a => ?_⟩
  have hmem : Work.Diff.STE.flatToE (I := I) (D.x₀ i) z ∈ K' :=
    (Work.Diff.STE.flatToE_mem_coordBall (I := I) (D.x₀ i) (D.σ i) z).mpr hz
  have h1 : δ * ‖a‖ ^ 2 ≤ a₀ (D.pt i z)
      (Submission.Geodesic.frameVector (I := I) (D.x₀ i) (D.pt i z) a)
      (Submission.Geodesic.frameVector (I := I) (D.x₀ i) (D.pt i z) a) :=
    hδb (Work.Diff.STE.flatToE (I := I) (D.x₀ i) z) hmem a
  have h2 : g₀.inner (D.pt i z)
      (Submission.Geodesic.frameVector (I := I) (D.x₀ i) (D.pt i z) a)
      (Submission.Geodesic.frameVector (I := I) (D.x₀ i) (D.pt i z) a) ≤ C * ‖a‖ ^ 2 :=
    hCb (Work.Diff.STE.flatToE (I := I) (D.x₀ i) z) hmem a
  calc δ / C * g₀.inner (D.pt i z)
        (Submission.Geodesic.frameVector (I := I) (D.x₀ i) (D.pt i z) a)
        (Submission.Geodesic.frameVector (I := I) (D.x₀ i) (D.pt i z) a)
      ≤ δ / C * (C * ‖a‖ ^ 2) := mul_le_mul_of_nonneg_left h2 (div_nonneg hδpos.le hCpos.le)
    _ = δ * ‖a‖ ^ 2 := by
        rw [← mul_assoc, div_mul_cancel₀ δ (ne_of_gt hCpos)]
    _ ≤ a₀ (D.pt i z) (Submission.Geodesic.frameVector (I := I) (D.x₀ i) (D.pt i z) a)
        (Submission.Geodesic.frameVector (I := I) (D.x₀ i) (D.pt i z) a) := h1

/-! ## The global comparison -/

/-- **The base section dominates a positive multiple of `g₀` globally.**  Since the closed
`σ i`-coordinate balls of the charts cover `M` (`B3Data.hcover`), the per-chart comparisons combine
into a single uniform multiple. -/
lemma exists_global_lambda
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (a₀ : Work.Diff.STE.Bil (I := I) (M := M))
    (ha₀ : Work.Diff.STE.D.ChartData (I := I) (M := M) a₀)
    (hpos : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < a₀ x v v) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ (x : M) (v : TangentSpace I x), lam * g₀.inner x v v ≤ a₀ x v v := by
  by_cases hι : Nonempty ι₀
  · haveI := hι
    choose lam hlampos hlamb using fun i : ι₀ =>
      perChart_bound (I := I) (M := M) D a₀ ha₀ hpos i
    refine ⟨Finset.univ.inf' Finset.univ_nonempty lam, ?_, ?_⟩
    · rw [Finset.lt_inf'_iff Finset.univ_nonempty]
      intro i _
      exact hlampos i
    · intro x v
      obtain ⟨i, hsrc, hcoord⟩ := D.hcover x
      have hle : Finset.univ.inf' Finset.univ_nonempty lam ≤ lam i :=
        Finset.inf'_le lam (Finset.mem_univ i)
      have hb := hlamb i (Work.Diff.STE.coord (I := I) (D.x₀ i) x) hcoord
      rw [D.pt_coord i hsrc] at hb
      have hsrc' : x ∈ (chartAt H (D.x₀ i)).source := by
        simpa only [extChartAt_source] using hsrc
      obtain ⟨a, ha⟩ := exists_frameVector_eq (I := I) (M := M) (D.x₀ i) hsrc' v
      have hthis : lam i * g₀.inner x v v ≤ a₀ x v v := by
        have h := hb a
        rwa [ha] at h
      calc Finset.univ.inf' Finset.univ_nonempty lam * g₀.inner x v v
          ≤ lam i * g₀.inner x v v :=
            mul_le_mul_of_nonneg_right hle (Work.Diff.STE.D.smet_inner_self_nonneg (I := I) g₀ x v)
        _ ≤ a₀ x v v := hthis
  · refine ⟨1, one_pos, fun x v => ?_⟩
    obtain ⟨i, _⟩ := D.hcover x
    exact absurd ⟨i⟩ hι

theorem exists_isPosF_ball
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ)
    (a₀ : Work.Diff.STE.Bil (I := I) (M := M))
    (ha₀ : Work.Diff.STE.D.ChartData (I := I) (M := M) a₀)
    (hpos : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < a₀ x v v) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ,
      ‖c‖ < δ → Work.Diff.STE.D.Base.IsPosF (I := I) (M := M) a₀ D ε c := by
  by_cases hι : Nonempty ι₀
  · haveI := hι
    -- the uniform bound of the perturbation
    obtain ⟨d₀, hd₀pos, hdens⟩ :=
      Work.Diff.STE.B3.dens_lower_bound (I := I) (M := M) D
        (fun i => Work.Diff.STE.B3.densGood (I := I) (M := M) D i)
    set K : ℝ := 2 * (Real.sqrt d₀)⁻¹ with hKdef
    have hKpos : 0 < K := by
      rw [hKdef]
      exact mul_pos two_pos (inv_pos.mpr (Real.sqrt_pos.mpr hd₀pos))
    -- the global comparison
    obtain ⟨lam, hlampos, hlamb⟩ := exists_global_lambda (I := I) (M := M) D a₀ ha₀ hpos
    -- the number of coefficients
    set N : ℝ := (Fintype.card (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε) : ℝ) with hNdef
    have hNnonneg : 0 ≤ N := by
      rw [hNdef]
      exact Nat.cast_nonneg _
    refine ⟨min 1 (lam / (2 * K * (N + 1))), lt_min one_pos ?_, ?_⟩
    · exact div_pos hlampos (mul_pos (mul_pos two_pos hKpos) (by linarith))
    · intro c hc x v hv
      have hc1 : ‖c‖ < lam / (2 * K * (N + 1)) := lt_of_lt_of_le hc (min_le_right _ _)
      have hle : (∑ z, |c z|) ≤ N * ‖c‖ := by
        calc (∑ z, |c z|) = ∑ z, ‖c z‖ := by simp only [Real.norm_eq_abs]
          _ ≤ ∑ _z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε, ‖c‖ :=
              Finset.sum_le_sum (fun z _ => norm_le_pi_norm c z)
          _ = N * ‖c‖ := by
              rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hNdef]
      have hsumK : (∑ z, |c z|) * K < lam / 2 := by
        have h1 : (∑ z, |c z|) * K ≤ N * ‖c‖ * K :=
          mul_le_mul_of_nonneg_right hle hKpos.le
        have h2 : N * ‖c‖ * K < lam / 2 := by
          rcases eq_or_lt_of_le hNnonneg with hN0 | hNpos
          · rw [← hN0]
            simp only [zero_mul]
            positivity
          · calc N * ‖c‖ * K < N * (lam / (2 * K * (N + 1))) * K :=
                mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hc1 hNpos) hKpos
              _ = lam * N / (2 * (N + 1)) := by field_simp
              _ ≤ lam / 2 := by
                  rw [div_le_div_iff₀ (by positivity) (by norm_num : (0:ℝ) < 2)]
                  nlinarith [hlampos, hNnonneg]
        linarith [h1, h2]
      -- the perturbation bound
      have hpert : |(Work.Diff.STE.D.genMap (I := I) (M := M) D ε c x) v v|
          ≤ (∑ z, |c z|) * K * g₀.inner x v v := by
        have h := Work.Diff.STE.D.abs_genMap_apply_le (I := I) (M := M) D ε d₀ hd₀pos hdens c x v
        rwa [← hKdef] at h
      have hneg : -((∑ z, |c z|) * K * g₀.inner x v v)
          ≤ Work.Diff.STE.D.genMap (I := I) (M := M) D ε c x v v := (abs_le.mp hpert).1
      have hgpos : 0 < g₀.inner x v v := g₀.pos x v hv
      have hstep : (lam / 2) * g₀.inner x v v
          ≤ a₀ x v v - (∑ z, |c z|) * K * g₀.inner x v v := by
        have hlt : (lam / 2) * g₀.inner x v v < (lam - (∑ z, |c z|) * K) * g₀.inner x v v :=
          mul_lt_mul_of_pos_right (by linarith [hsumK]) hgpos
        have hsplit : (lam - (∑ z, |c z|) * K) * g₀.inner x v v
            = lam * g₀.inner x v v - (∑ z, |c z|) * K * g₀.inner x v v := by ring
        rw [hsplit] at hlt
        linarith [hlamb x v]
      rw [Work.Diff.STE.D.Base.fore_apply]
      have h0 : (0 : ℝ) < (lam / 2) * g₀.inner x v v := mul_pos (by linarith) hgpos
      linarith [h0, hstep, hneg]
  · refine ⟨1, one_pos, fun c _ => ?_⟩
    intro x v _
    obtain ⟨i, _⟩ := D.hcover x
    exact absurd ⟨i⟩ hι

end

end Work.Diff.STE.D.BasePos
