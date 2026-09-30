import Mathlib
import Submission.Work.CartanHadamard.Translate
import Submission.Work.CartanHadamard.Basic
import Submission.Work.CartanHadamard.lift_family_continuity_core
import Submission.Work.RiemLib.API

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option maxHeartbeats 1600000

namespace Work.CartanHadamard

open scoped Manifold ContDiff Bundle Topology ENNReal in
theorem continuousOn_translate
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    (hK : ∀ K : ℝ, 0 < K → Submission.RauchK.CurvLe cov K)
    {p y : M} {vt : TangentSpace I p}
    (hvt : Submission.GlobalExp.GExp (cov := cov) hmet p vt = y) {ρ : ℝ} (hρpos : 0 < ρ) :
    ContinuousOn (fun w : TangentSpace I y =>
        translate (cov := cov) hmet htor hK vt w) (Metric.ball (0 : TangentSpace I y) ρ) := by
  classical
  -- A conjugate-radius bound `R = π/√K₀` exceeding `‖vt‖ + ρ`.
  obtain ⟨K₀, hK₀pos, hK₀lt⟩ := Work.RiemLib.exists_lt_pi_div_sqrt (‖vt‖ + ρ)
  set R : ℝ := Real.pi / Real.sqrt K₀ with hRdef
  -- The exponential map of the fibre is a local homeomorphism, hence locally injective.
  have hloc : ∀ v : TangentSpace I p, ‖v‖ < R → ∃ u ∈ 𝓝 v,
      ∀ a ∈ u, ∀ b ∈ u,
        Submission.GlobalExp.GExp (cov := cov) hmet p a
          = Submission.GlobalExp.GExp (cov := cov) hmet p b → a = b := by
    intro v _
    obtain ⟨U, hUopen, hvU, hUinj⟩ :=
      (Work.CartanHadamard.isLocalHomeomorph_GExp (cov := cov) hmet htor hK p).isLocallyInjective v
    exact ⟨U, hUopen.mem_nhds hvU, fun a ha b hb heq => hUinj ha hb heq⟩
  -- The radius of the parameter ball, as a fibre-norm bound.
  have hmem_ball : ∀ w : Metric.ball (0 : TangentSpace I y) ρ,
      ‖(w : TangentSpace I y)‖ < ρ := by
    intro w
    have h := w.2
    simp only [Metric.mem_ball] at h
    simpa [dist_eq_norm] using h
  -- For every `w` in the ball, a lift of the radial curve `τ ↦ GExp y (τ • w)` starting at `vt`.
  have hchoose : ∀ w : Metric.ball (0 : TangentSpace I y) ρ,
      ∃ W : ℝ → TangentSpace I p,
        ContinuousOn W (Set.Icc (0 : ℝ) 1) ∧ W 0 = vt ∧
        (∀ s ∈ Set.Icc (0 : ℝ) 1,
          Submission.GlobalExp.GExp (cov := cov) hmet p (W s)
            = Submission.GlobalExp.GExp (cov := cov) hmet y (s • (w : TangentSpace I y))) ∧
        (∀ s ∈ Set.Icc (0 : ℝ) 1, ‖W s‖ ≤ ‖vt‖ +
          Submission.Length.curveLength (I := I)
            (fun τ : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet y
              (τ • (w : TangentSpace I y))) 0 s) := by
    intro w
    have hlen : Submission.Length.curveLength (I := I)
        (fun τ : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet y (τ • (w : TangentSpace I y)))
        0 1 = ‖(w : TangentSpace I y)‖ := by
      rw [Submission.Shorten.curveLength_GExp_ray_all (cov := cov) hmet y (w : TangentSpace I y)
        (by norm_num : (0 : ℝ) ≤ 1)]
      ring
    refine exists_lift_from_vector (cov := cov) hmet htor hK₀pos (hK K₀ hK₀pos)
      (p := p)
      (h := fun τ : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet y
        (τ • (w : TangentSpace I y)))
      (S := 1) one_pos
      (contMDiffOn_GExp_ray (cov := cov) hmet y (w : TangentSpace I y)) ?_ ?_
    · show Submission.GlobalExp.GExp (cov := cov) hmet p vt
        = Submission.GlobalExp.GExp (cov := cov) hmet y ((0 : ℝ) • (w : TangentSpace I y))
      rw [zero_smul, Submission.GlobalExp.GExp_zero]
      exact hvt
    · rw [hlen]
      linarith [hmem_ball w]
  -- The chosen family, slice-wise continuous.
  let W : ℝ → Metric.ball (0 : TangentSpace I y) ρ → TangentSpace I p :=
    fun s w => (Classical.choose (hchoose w)) s
  have hWspec : ∀ w : Metric.ball (0 : TangentSpace I y) ρ,
      ContinuousOn (fun s : ℝ => W s w) (Set.Icc (0 : ℝ) 1) ∧ W 0 w = vt ∧
      (∀ s ∈ Set.Icc (0 : ℝ) 1,
        Submission.GlobalExp.GExp (cov := cov) hmet p (W s w)
          = Submission.GlobalExp.GExp (cov := cov) hmet y (s • (w : TangentSpace I y))) ∧
      (∀ s ∈ Set.Icc (0 : ℝ) 1, ‖W s w‖ ≤ ‖vt‖ +
        Submission.Length.curveLength (I := I)
          (fun τ : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet y
            (τ • (w : TangentSpace I y))) 0 s) :=
    fun w => Classical.choose_spec (hchoose w)
  -- Joint continuity of the parameter map `Φ`.
  have hΦcont : Continuous (fun u : ℝ × Metric.ball (0 : TangentSpace I y) ρ =>
      Submission.GlobalExp.GExp (cov := cov) hmet y (u.1 • (u.2 : TangentSpace I y))) :=
    (Work.CartanHadamard.isLocalHomeomorph_GExp (cov := cov) hmet htor hK y).continuous.comp
      (continuous_smul.comp (continuous_fst.prodMk
        (continuous_subtype_val.comp continuous_snd)))
  -- The uniform radial-norm bound `‖W s w‖ < R`.
  have hb : ∀ w : Metric.ball (0 : TangentSpace I y) ρ,
      ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖W s w‖ < R := by
    intro w s hs
    have h1 := (hWspec w).2.2.2 s hs
    have h2 : Submission.Length.curveLength (I := I)
        (fun τ : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet y (τ • (w : TangentSpace I y))) 0 s
        = ‖(w : TangentSpace I y)‖ * s := by
      rw [Submission.Shorten.curveLength_GExp_ray_all (cov := cov) hmet y (w : TangentSpace I y) hs.1]
      ring
    rw [h2] at h1
    have hle : ‖(w : TangentSpace I y)‖ * s ≤ ‖(w : TangentSpace I y)‖ := by
      have h0 : 0 ≤ ‖(w : TangentSpace I y)‖ := norm_nonneg _
      nlinarith [hs.1, hs.2]
    rw [hRdef]
    linarith [hmem_ball w]
  -- The parametric lifting theorem: joint continuity of `(s,w) ↦ W s w`.
  have hjoint : ContinuousOn (fun u : ℝ × Metric.ball (0 : TangentSpace I y) ρ => W u.1 u.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) :=
    lift_family_continuity_core
      (X := TangentSpace I p) (Y := M)
      (f := fun v : TangentSpace I p => Submission.GlobalExp.GExp (cov := cov) hmet p v)
      (Work.CartanHadamard.isLocalHomeomorph_GExp (cov := cov) hmet htor hK p).continuous
      hloc
      (A := Metric.ball (0 : TangentSpace I y) ρ)
      (Φ := fun u : ℝ × Metric.ball (0 : TangentSpace I y) ρ =>
        Submission.GlobalExp.GExp (cov := cov) hmet y (u.1 • (u.2 : TangentSpace I y)))
      hΦcont (W := W) (S := 1) (v₀ := vt)
      (fun w => (hWspec w).1)
      (fun w => (hWspec w).2.1)
      (fun w s hs => (hWspec w).2.2.1 s hs)
      hb
  -- Continuity in `w` at the endpoint `s = 1`.
  have hcont1 : Continuous (fun w : Metric.ball (0 : TangentSpace I y) ρ => W 1 w) := by
    have hk : Continuous (fun w : Metric.ball (0 : TangentSpace I y) ρ => ((1 : ℝ), w)) :=
      continuous_const.prodMk continuous_id
    have h := hjoint.comp_continuous hk
      (fun w => ⟨⟨zero_le_one, le_rfl⟩, Set.mem_univ w⟩)
    change Continuous (fun w : Metric.ball (0 : TangentSpace I y) ρ => W 1 w) at h
    exact h
  -- The lift's endpoint is the translate, by the universal property.
  have heq : ∀ w : Metric.ball (0 : TangentSpace I y) ρ,
      translate (cov := cov) hmet htor hK vt (w : TangentSpace I y) = W 1 w := by
    intro w
    exact (translate_eq_of_lift (cov := cov) hmet htor hK hvt (w : TangentSpace I y)
      (W := fun s => W s w) (hWspec w).1 (hWspec w).2.1 (hWspec w).2.2.1).symm
  rw [continuousOn_iff_continuous_domRestrict]
  rw [show (Metric.ball (0 : TangentSpace I y) ρ).domRestrict
        (fun w : TangentSpace I y => translate (cov := cov) hmet htor hK vt w)
      = fun w : Metric.ball (0 : TangentSpace I y) ρ => W 1 w from funext heq]
  exact hcont1

end Work.CartanHadamard
