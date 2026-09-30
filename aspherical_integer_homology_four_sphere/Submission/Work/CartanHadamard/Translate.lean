/-
# Cartan–Hadamard: the geodesic translate along the exponential map

Fix a base point `p` and a second point `y`, a vector `vt ∈ T_pM` with `GExp p vt = y` and a vector
`w ∈ T_yM`.  The **translate** `translate vt w ∈ T_pM` is the endpoint of the lift, under
`GExp p`, of the radial geodesic `τ ↦ GExp y (τ • w)` starting at `vt` — the "geodesic transport"
of the tangent vector `vt` along the exponential chart at `y`.

Its two defining properties (proved here) are

* `translate_apply : GExp p (translate vt w) = GExp y w`, and
* the **universal property** `translate_eq_of_lift`: *any* continuous lift `W` of `τ ↦ GExp y (τ • w)`
  on `[0,1]` with `W 0 = vt` satisfies `W 1 = translate vt w`.

The existence of the lift is `Work.CartanHadamard.exists_lift_from_vector` (the lifting theorem of
the vendored library, with an arbitrary starting vector); the universal property is uniqueness of
lifts along a preconnected interval (`Work.CartanHadamard.lift_unique_GExp`).

`exists_translate_eq` is the converse statement used in the cover half of the evenly-covered
neighbourhood argument: every point `u` of `T_pM` with `GExp p u = GExp y w` is the translate of a
unique fibre point `vt ∈ GExp p ⁻¹' {y}`.
-/
import Submission.Work.CartanHadamard.Basic
import Submission.Work.CartanHadamard.exists_lift_from_vector

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open LeanEval.Geometry.SphereTheorem

namespace Work.CartanHadamard

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]
  [I.Boundaryless] [Nontrivial E] [CompactSpace M]
  {cov : CovariantDerivative I E (TangentSpace I (M := M))}
  [ContMDiffCovariantDerivative cov ∞]

/-- The radial curve `τ ↦ GExp y (τ • w)` of the exponential chart at `y` is `C^∞`. -/
theorem contMDiffOn_GExp_ray (hmet : IsMetricCompatible cov) (y : M)
    (w : TangentSpace I y) :
    ContMDiffOn 𝓘(ℝ) I 1 (fun τ : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet y (τ • w))
      (Set.Icc (0 : ℝ) 1) := by
  have hlin : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun τ : ℝ => (show E from τ • w))
      (Set.Icc (0 : ℝ) 1) := by
    rw [contMDiffOn_iff_contDiffOn]
    fun_prop
  refine ((Submission.XuLift.contMDiffOn_GExp_model (cov := cov) hmet y).comp hlin
    (fun τ _ => Set.mem_univ _)).of_le
    (show (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω) from WithTop.coe_le_coe.mpr le_top)

/-- **Existence of the geodesic translate.**  For `vt ∈ T_pM` with `GExp p vt = y` and `w ∈ T_yM`
there is a point `u ∈ T_pM` which lies over `GExp y w` and is the endpoint of *every* continuous
lift of the radial curve `τ ↦ GExp y (τ • w)` starting at `vt`. -/
theorem exists_translate (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    (hK : ∀ K : ℝ, 0 < K → Submission.RauchK.CurvLe cov K)
    {p y : M} {vt : TangentSpace I p} (hvt : Submission.GlobalExp.GExp (cov := cov) hmet p vt = y)
    (w : TangentSpace I y) :
    ∃ u : TangentSpace I p,
      Submission.GlobalExp.GExp (cov := cov) hmet p u
        = Submission.GlobalExp.GExp (cov := cov) hmet y w ∧
      ∀ W : ℝ → TangentSpace I p, ContinuousOn W (Set.Icc (0 : ℝ) 1) → W 0 = vt →
        (∀ τ ∈ Set.Icc (0 : ℝ) 1,
          Submission.GlobalExp.GExp (cov := cov) hmet p (W τ)
            = Submission.GlobalExp.GExp (cov := cov) hmet y (τ • w)) →
        W 1 = u := by
  obtain ⟨K, hKpos, hKlt⟩ := Work.RiemLib.exists_lt_pi_div_sqrt
    (‖vt‖ + Submission.Length.curveLength (I := I)
      (fun τ : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet y (τ • w)) 0 1)
  obtain ⟨W₀, hW₀c, hW₀0, hW₀G, -⟩ :=
    exists_lift_from_vector (cov := cov) hmet htor hKpos (hK K hKpos)
      (p := p) (h := fun τ : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet y (τ • w))
      (S := 1) one_pos (contMDiffOn_GExp_ray (cov := cov) hmet y w)
      (by rw [zero_smul, Submission.GlobalExp.GExp_zero]; exact hvt) hKlt
  refine ⟨W₀ 1, ?_, ?_⟩
  · rw [hW₀G 1 ⟨zero_le_one, le_rfl⟩, one_smul]
  · intro W hWc hW0 hWG
    haveI : PreconnectedSpace ↥(Set.Icc (0 : ℝ) 1) :=
      Subtype.preconnectedSpace (isPreconnected_Icc (a := (0 : ℝ)) (b := 1))
    have h_eq : (fun τ : ↥(Set.Icc (0 : ℝ) 1) => W τ.1)
        = fun τ : ↥(Set.Icc (0 : ℝ) 1) => W₀ τ.1 :=
      lift_unique_GExp (cov := cov) hmet htor hK p hWc.domRestrict hW₀c.domRestrict
        (fun τ => by rw [hWG τ.1 τ.2, hW₀G τ.1 τ.2])
        (a₀ := ⟨0, ⟨le_refl 0, zero_le_one⟩⟩) (by simp [hW0, hW₀0])
    exact congrFun h_eq ⟨1, ⟨zero_le_one, le_rfl⟩⟩

/-- The **geodesic translate** of a tangent vector `vt` over `p` (with `GExp p vt = y`) by a vector
`w` at `y`: the endpoint of the lift of the radial geodesic `τ ↦ GExp y (τ • w)` starting at `vt`.
When `GExp p vt ≠ y` the definition is arbitrary (the value is `0`); all its properties are proved
under the hypothesis `GExp p vt = y`. -/
noncomputable def translate (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    (hK : ∀ K : ℝ, 0 < K → Submission.RauchK.CurvLe cov K) {p y : M}
    (vt : TangentSpace I p) (w : TangentSpace I y) : TangentSpace I p := by
  classical
  exact if h : Submission.GlobalExp.GExp (cov := cov) hmet p vt = y then
    Classical.choose (exists_translate (cov := cov) hmet htor hK h w)
  else 0

/-- The defining property of the translate: it lies over the same point as `w`. -/
theorem translate_apply (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    (hK : ∀ K : ℝ, 0 < K → Submission.RauchK.CurvLe cov K)
    {p y : M} {vt : TangentSpace I p} (hvt : Submission.GlobalExp.GExp (cov := cov) hmet p vt = y)
    (w : TangentSpace I y) :
    Submission.GlobalExp.GExp (cov := cov) hmet p (translate (cov := cov) hmet htor hK vt w)
      = Submission.GlobalExp.GExp (cov := cov) hmet y w := by
  rw [translate, dite_eq_left hvt]
  exact (Classical.choose_spec (exists_translate (cov := cov) hmet htor hK hvt w)).1

/-- **The universal property of the translate**: any continuous lift of `τ ↦ GExp y (τ • w)` on
`[0,1]` starting at `vt` ends at `translate vt w`. -/
theorem translate_eq_of_lift (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    (hK : ∀ K : ℝ, 0 < K → Submission.RauchK.CurvLe cov K)
    {p y : M} {vt : TangentSpace I p} (hvt : Submission.GlobalExp.GExp (cov := cov) hmet p vt = y)
    (w : TangentSpace I y) {W : ℝ → TangentSpace I p}
    (hWc : ContinuousOn W (Set.Icc (0 : ℝ) 1)) (hW0 : W 0 = vt)
    (hWG : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      Submission.GlobalExp.GExp (cov := cov) hmet p (W τ)
        = Submission.GlobalExp.GExp (cov := cov) hmet y (τ • w)) :
    W 1 = translate (cov := cov) hmet htor hK vt w := by
  rw [translate, dite_eq_left hvt]
  exact (Classical.choose_spec (exists_translate (cov := cov) hmet htor hK hvt w)).2 W hWc hW0 hWG

/-- The translate by `0` is the starting point. -/
theorem translate_zero (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    (hK : ∀ K : ℝ, 0 < K → Submission.RauchK.CurvLe cov K)
    {p y : M} {vt : TangentSpace I p} (hvt : Submission.GlobalExp.GExp (cov := cov) hmet p vt = y) :
    translate (cov := cov) hmet htor hK vt (0 : TangentSpace I y) = vt := by
  refine (translate_eq_of_lift (cov := cov) hmet htor hK hvt (0 : TangentSpace I y)
    (W := fun _ => vt) continuousOn_const rfl ?_).symm
  intro τ _
  rw [smul_zero, Submission.GlobalExp.GExp_zero]
  exact hvt

/-- **Cover property of the translates**: every point `u` of `T_pM` lying over `GExp y w` is the
translate of a fibre point `vt` over `y`. -/
theorem exists_translate_eq (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    (hK : ∀ K : ℝ, 0 < K → Submission.RauchK.CurvLe cov K)
    {p y : M} {w : TangentSpace I y} {u : TangentSpace I p}
    (hu : Submission.GlobalExp.GExp (cov := cov) hmet p u
      = Submission.GlobalExp.GExp (cov := cov) hmet y w) :
    ∃ vt : TangentSpace I p, Submission.GlobalExp.GExp (cov := cov) hmet p vt = y ∧
      translate (cov := cov) hmet htor hK vt w = u := by
  obtain ⟨K, hKpos, hKlt⟩ := Work.RiemLib.exists_lt_pi_div_sqrt
    (‖u‖ + Submission.Length.curveLength (I := I)
      (fun τ : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet y ((1 - τ) • w)) 0 1)
  have hcrev : ContMDiffOn 𝓘(ℝ) I 1
      (fun τ : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet y ((1 - τ) • w))
      (Set.Icc (0 : ℝ) 1) := by
    have hlin : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun τ : ℝ => (show E from (1 - τ) • w))
        (Set.Icc (0 : ℝ) 1) := by
      rw [contMDiffOn_iff_contDiffOn]
      fun_prop
    refine ((Submission.XuLift.contMDiffOn_GExp_model (cov := cov) hmet y).comp hlin
      (fun τ _ => Set.mem_univ _)).of_le
      (show (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω) from WithTop.coe_le_coe.mpr le_top)
  obtain ⟨W, hWc, hW0, hWG, -⟩ :=
    exists_lift_from_vector (cov := cov) hmet htor hKpos (hK K hKpos) (p := p)
      (h := fun τ : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet y ((1 - τ) • w))
      (S := 1) one_pos hcrev (by rw [sub_zero, one_smul]; exact hu) hKlt
  set vt : TangentSpace I p := W 1 with hvtdef
  have hvt : Submission.GlobalExp.GExp (cov := cov) hmet p vt = y := by
    rw [hvtdef, hWG 1 ⟨zero_le_one, le_rfl⟩]
    norm_num
  refine ⟨vt, hvt, ?_⟩
  have hW'c : ContinuousOn (fun τ : ℝ => W (1 - τ)) (Set.Icc (0 : ℝ) 1) :=
    hWc.comp (continuous_const.sub continuous_id).continuousOn
      (fun τ hτ => ⟨by linarith [hτ.2], by linarith [hτ.1]⟩)
  refine (translate_eq_of_lift (cov := cov) hmet htor hK hvt w (W := fun τ => W (1 - τ))
    hW'c (by simp [hvtdef]) ?_).symm.trans ?_
  · intro τ hτ
    have h1 : (1 : ℝ) - τ ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hτ.2], by linarith [hτ.1]⟩
    rw [hWG _ h1]
    congr 1
    ring_nf
  · simpa [hvtdef] using hW0

end

end Work.CartanHadamard
