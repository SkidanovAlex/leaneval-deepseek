import Mathlib
import Submission.Work.Diff.L.Defs
import Submission.Work.Diff.L.Stmt
import Submission.Work.Diff.L.myers_sec_ge
import Submission.Work.Diff.L.myers_sec_ge_aux
import Submission.Work.Diff.L.gradSq_cauchy
import Submission.Work.Diff.L.deriv_comp
import Submission.Work.Diff.L.comparison
import Submission.Work.EXT.lcSmooth_noBoundary
import Submission.Work.EXT.contMDiffCovariantDerivative_lcOf
import Submission.HopfRinow2
import Submission.LensLoop
import Submission.GExpRayZero
import Submission.CutTime
import Submission.GExpVelocity
import Submission.BrokenLength
import Submission.Work.Diff.GE.bianchi_kato_defs
import Submission.Work.Diff.L.spread_numeric
import Submission.Work.Diff.L.spread_drop_bound
import Submission.Work.Diff.L.spread_first_exit

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.L

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Submission.Geodesic Submission.GlobalExp

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I (((⊤ : ℕ∞) : WithTop ℕ∞)) M]

/-! The three supporting lemmas `spread_numeric`, `spread_drop_bound` and `spread_first_exit` are
proved in the sibling modules `Submission.Work.Diff.L.spread_numeric`,
`Submission.Work.Diff.L.spread_drop_bound` and `Submission.Work.Diff.L.spread_first_exit`
(delegated and proved in parallel). -/

/-! ### Elementary arithmetic for the gradient bound -/

/-- **The pointwise gradient bound.**  If `s ≤ S₀`, `0 ≤ S₀`, `β > 0` and `Cn ≤ β²S₀²` then
`β² s³ + Cn ≤ (β (S₀√S₀ + S₀))²`.  This is the constant that the gradient inequality
`|∇S|² ≤ β²S³ + Cn` produces on the region where `S ≤ S₀` (note that `s³ ≤ S₀³` holds for *all*
`s ≤ S₀` when `S₀ ≥ 0`, so no case distinction on the sign of `S` is needed). -/
theorem spread_grad_arith {s S₀ β Cn : ℝ} (hβ : 0 < β) (hS₀ : 0 ≤ S₀) (hs : s ≤ S₀)
    (hCn : Cn ≤ β ^ 2 * S₀ ^ 2) :
    β ^ 2 * s ^ 3 + Cn ≤ (β * (S₀ * Real.sqrt S₀ + S₀)) ^ 2 := by
  have hs3 : s ^ 3 ≤ S₀ ^ 3 := (show Odd 3 by norm_num).pow_le_pow.mpr hs
  have h1 : β ^ 2 * s ^ 3 ≤ β ^ 2 * S₀ ^ 3 := mul_le_mul_of_nonneg_left hs3 (sq_nonneg β)
  have hsq : Real.sqrt S₀ ^ 2 = S₀ := Real.sq_sqrt hS₀
  have h2 : β ^ 2 * S₀ ^ 3 + β ^ 2 * S₀ ^ 2 ≤ (β * (S₀ * Real.sqrt S₀ + S₀)) ^ 2 := by
    rw [← mul_add, mul_pow]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg β)
    nlinarith [hsq, Real.sqrt_nonneg S₀]
  linarith

/-! ### The ray of the exponential map

These are the two properties of the ray `s ↦ GExp x (s • v)` (`‖v‖ = 1`) that the Myers argument
consumes: unit speed and minimality up to the distance realised at the endpoint. -/

section Ray

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I (((⊤ : ℕ∞) : WithTop ℕ∞)) E (fun x : M ↦ TangentSpace I x)]
  [I.Boundaryless] [Nontrivial E] [CompactSpace M] [T2Space M]
  {cov : CovariantDerivative I E (TangentSpace I (M := M))}
  [ContMDiffCovariantDerivative cov ∞]

/-- **The ray of `GExp` in a unit direction has unit speed.** -/
theorem unit_speed_GExp_ray (hmet : IsMetricCompatible cov) (x : M) {w : TangentSpace I x}
    (hw : ‖w‖ = 1) (hwne : w ≠ 0) :
    ∀ t : ℝ, ‖curveVelocity (I := I) (fun s : ℝ => GExp (cov := cov) hmet x (s • w)) t‖ = 1 := by
  intro t
  rw [← Submission.GeodesicSpeed.curveSpeed_eq_norm]
  rw [Submission.BrokenLength.curveSpeed_GExp_ray (cov := cov) hmet x hwne t, hw]

/-- **Up to the distance realised at the endpoint, the ray is minimising.** -/
theorem edist_GExp_ray_eq (hmet : IsMetricCompatible cov) (x : M) {w : TangentSpace I x}
    (hw : ‖w‖ = 1) {T : ℝ} (hT : 0 ≤ T)
    (hmin : Manifold.riemannianEDist I x (GExp (cov := cov) hmet x (T • w)) =
      ENNReal.ofReal T) :
    ∀ t ∈ Set.Icc 0 T,
      Manifold.riemannianEDist I x (GExp (cov := cov) hmet x (t • w)) = ENNReal.ofReal t := by
  intro t ht
  rcases eq_or_lt_of_le ht.1 with h | h
  · rw [← h, zero_smul, GExp_zero, Manifold.riemannianEDist_self]
    simp
  · exact Submission.CutTime.edist_GExp_smul_eq_of_le_of_eq (cov := cov) hmet hw ht.1 ht.2 hmin

end Ray

/-! ### The main theorem -/

/-- **Spreading of the scalar curvature.**  Let `g` be a smooth metric with a smooth scalar curvature `S = scalAt g` whose maximum `S₀` is large (`Θ ≤ S₀`), whose gradient is controlled by `|∇S|² ≤ β²S³ + Cn` with `Cn ≤ β²S₀²` and `β ≤ β₀` small, and which is `c₀ S₀`-positively curved wherever `S ≥ (1-ε)S₀`.  Then `S ≥ (1-ε)S₀` everywhere.  This is a re-request of `Submission.Work.Diff.L.spread_scalar`, whose prover never wrote a proof down.  (Route: integrate `|∇S| ≤ β S^{3/2} + βS₀` along minimising geodesics from the maximum point `x₀`; on the ball where `S ≥ (1-ε)S₀` the curvature lower bound and Bonnet–Myers (`Work.Diff.L.myers_sec_ge`, `Submission.GlobalBM`, `Submission.HopfRinow`) give `diam ≤ π/√(c₀ S₀)`, which is smaller than the radius for `β₀` small enough — so the ball is all of `M`.  Connectedness of `M` is `[PreconnectedSpace M]`.) -/
theorem spread_scalar_v2
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I (((⊤ : ℕ∞) : WithTop ℕ∞)) M] [I.Boundaryless] [T2Space M] [CompactSpace M]
    [PreconnectedSpace M]
    (hdim : 2 ≤ Module.finrank ℝ E) {ε : ℝ} (hε : 0 < ε) :
    ∃ Θ : ℝ, 0 < Θ ∧ ∀ c₀ : ℝ, 0 < c₀ → ∃ β₀ : ℝ, 0 < β₀ ∧
      ∀ (g : Submission.Diff.SMet I M) (S : M → ℝ) (x₀ : M) (S₀ β Cn : ℝ),
        ContMDiff I (modelWithCornersSelf ℝ ℝ) (((⊤ : ℕ∞) : WithTop ℕ∞)) S →
        (∀ x, S x = Submission.Diff.scalAt g x) →
        Submission.Diff.scalAt g x₀ = S₀ → Θ ≤ S₀ → 0 < β → β ≤ β₀ →
        (∀ x, Submission.Diff.gradSq g (Submission.Diff.scalAt g) x ≤ β ^ 2 * (S x) ^ 3 + Cn) →
        Cn ≤ β ^ 2 * S₀ ^ 2 →
        (∀ x, (1 - ε) * S₀ ≤ S x → ∀ u v : TangentSpace I x,
          g.inner x u u = 1 → g.inner x v v = 1 → g.inner x u v = 0 →
          c₀ * S₀ ≤ Work.Diff.L.secCurvAt g x u v) →
        ∀ y, (1 - ε) * S₀ ≤ S y := by
  classical
  refine ⟨1, one_pos, fun c₀ hc₀ =>
    ⟨ε * Real.sqrt c₀ / (4 * Real.sqrt 2 * Real.pi), by positivity, ?_⟩⟩
  intro g S x₀ S₀ β Cn hSsm hSeq hS₀eq hΘpos hβpos hββ₀ hgrad hCn hcurv
  -- ## Step 0: set up the metric `g` as the ambient Riemannian structure
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I (((⊤ : ℕ∞) : WithTop ℕ∞)) E
      (fun x : M ↦ TangentSpace I x) := inferInstance
  haveI : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  haveI : Nonempty M := ⟨x₀⟩
  haveI : ConnectedSpace M := ConnectedSpace.mk inferInstance
  haveI hLPC : LocallyPathConnectedSpace M := by
    haveI : LocallyPathConnectedSpace H := I.toHomeomorph.symm.locallyPathConnectedSpace
    exact ChartedSpace.locallyPathConnectedSpace H M
  haveI : PathConnectedSpace M := (pathConnectedSpace_iff_connectedSpace (X := M)).mpr inferInstance
  haveI : RegularSpace M := inferInstance
  obtain ⟨hcovn, htor, hmet⟩ := Work.EXT.lcSmooth_noBoundary (I := I) (M := M) g
  obtain ⟨hcov⟩ := hcovn
  have hS₀pos : 0 < S₀ := lt_of_lt_of_le zero_lt_one hΘpos
  have hSeq' : S = Submission.Diff.scalAt g := funext hSeq
  -- the gradient bound, phrased with `S`
  have hgrad' : ∀ x : M, Submission.Diff.gradSq g S x ≤ β ^ 2 * (S x) ^ 3 + Cn := by
    intro x
    have h := hgrad x
    rw [hSeq'] at h ⊢
    exact h
  -- ## Step 1: suppose the conclusion fails
  by_contra hcon
  push Not at hcon
  obtain ⟨y, hy⟩ := hcon
  have hyne : y ≠ x₀ := by
    intro h
    have h1 : S y = S₀ := by rw [h, hSeq x₀, hS₀eq]
    have h2 : (1 - ε) * S₀ ≤ S₀ := by nlinarith
    linarith [hy, h1]
  -- ## Step 2: a minimising geodesic from `x₀` to `y`
  obtain ⟨v, hv_exp, hv_ed⟩ :=
    Submission.HopfRinow.exists_geodesic_riemannianEDist_eq (I := I) (M := M)
      (cov := Submission.Diff.lcOf g) hmet htor x₀ y
  have hvne : v ≠ 0 := by
    intro h0
    rw [h0, Submission.GlobalExp.GExp_zero] at hv_exp
    exact hyne hv_exp.symm
  have hspan : 0 < ‖v‖ := norm_pos_iff.mpr hvne
  -- the unit direction of `v`, and the ray in that direction
  let η : TangentSpace I x₀ := Submission.GlobalExp.unitOf v hvne
  have hη : ‖η‖ = 1 := Submission.GlobalExp.unitOf_norm v hvne
  have hηne : η ≠ 0 := by rw [← norm_pos_iff, hη]; norm_num
  have hLη : ‖v‖ • η = v := by
    show ‖v‖ • (‖v‖⁻¹ • v) = v
    rw [smul_smul, mul_inv_cancel₀ hspan.ne', one_smul]
  let L : ℝ := ‖v‖
  let γ : ℝ → M := fun s : ℝ => Submission.GlobalExp.GExp hmet x₀ (s • η)
  have hγ0 : γ 0 = x₀ := by simp only [γ, zero_smul, Submission.GlobalExp.GExp_zero]
  have hγL : γ L = y := by
    show Submission.GlobalExp.GExp hmet x₀ (‖v‖ • η) = y
    rw [hLη]; exact hv_exp
  have hγsm : ContMDiffOn (modelWithCornersSelf ℝ ℝ) I (((⊤ : ℕ∞) : WithTop ℕ∞)) γ univ :=
    Submission.LensLoop.contMDiffOn_GExp_smul (cov := Submission.Diff.lcOf g) hmet x₀ hηne
  have hγgeo : ∀ t : ℝ, IsGeodesicAt (Submission.Diff.lcOf g) γ t :=
    Submission.GExpRayZero.isGeodesicAt_GExp_smul_all (cov := Submission.Diff.lcOf g) hmet x₀ hηne
  have hγunit : ∀ t : ℝ, ‖curveVelocity (I := I) γ t‖ = 1 :=
    unit_speed_GExp_ray (cov := Submission.Diff.lcOf g) hmet x₀ hη hηne
  have hLpos : 0 < L := hspan
  have hγmin : ∀ t ∈ Icc 0 L,
      Manifold.riemannianEDist I x₀ (γ t) = ENNReal.ofReal t := by
    have hmin : Manifold.riemannianEDist I x₀ (γ L) = ENNReal.ofReal L := by
      rw [hγL]
      simpa only [L] using hv_ed
    intro t ht
    exact edist_GExp_ray_eq (cov := Submission.Diff.lcOf g) hmet x₀ hη hLpos.le hmin t ht
  -- ## Step 3: the first exit time `r` from the superlevel set `{S > (1-ε)S₀}` and the last
  --          return `ρ` to the level `S₀`
  let c : ℝ := (1 - ε) * S₀
  let f : ℝ → ℝ := fun t : ℝ => S (γ t)
  have hγcont : ContinuousOn γ (Icc 0 L) := hγsm.continuousOn.mono (subset_univ _)
  have hfcont : ContinuousOn f (Icc 0 L) := by
    have h := hSsm.continuous.comp_continuousOn hγcont
    simpa only [f, Function.comp_def] using h
  have hf0 : f 0 = S₀ := by
    simp only [f, hγ0, hSeq x₀, hS₀eq]
  have hfL : f L < c := by
    simp only [f, hγL, c]
    exact hy
  have hcs : c < S₀ := by
    simp only [c]
    nlinarith
  obtain ⟨r, ρ, hrpos, hrle, hfr, hfgt, hρmem, hfρ, hfle⟩ :=
    spread_first_exit hLpos hfcont hf0 hfL hcs
  have hfge : ∀ t ∈ Icc 0 r, c ≤ f t := by
    intro t ht
    rcases eq_or_lt_of_le ht.2 with h | h
    · rw [h]; exact hfr.ge
    · exact le_of_lt (hfgt t ⟨ht.1, h⟩)
  -- ## Step 4: Bonnet–Myers on the arc `[0,r]`
  have hmyers : r ≤ Real.pi / Real.sqrt (c₀ * S₀ / 2) := by
    refine myers_sec_ge (I := I) (M := M) (cov := Submission.Diff.lcOf g) (k := c₀ * S₀ / 2)
      (by positivity) hmet htor hdim isOpen_univ hrpos (subset_univ _) hγsm
      (fun t _ => hγgeo t) (fun t _ => hγunit t) ?_ ?_
    · -- the lower curvature bound along the arc
      intro t ht u v hu hv huv
      have hle : c ≤ f t := hfge t ht
      have hinner : ∀ (x : M) (a b : TangentSpace I x), inner ℝ a b = g.inner x a b :=
        fun _ _ _ => rfl
      have h1 : c₀ * S₀ ≤ Work.Diff.L.secCurvAt g (γ t) u v := by
        refine hcurv (γ t) ?_ u v ?_ ?_ ?_
        · simpa only [c, f] using hle
        · rw [← hinner (γ t) u u]; exact hu
        · rw [← hinner (γ t) v v]; exact hv
        · rw [← hinner (γ t) u v]; exact huv
      have h2 : Work.Diff.L.secCurvAt g (γ t) u v
          = inner ℝ (Submission.CurvatureVec.curvVec (Submission.Diff.lcOf g) (γ t) u v v) u := by
        rw [Work.Diff.L.secCurvAt, Work.Diff.GE.rmVec_eq_curvVec_lcOf g hcov (γ t) u v v]
        exact (hinner (γ t)
          (Submission.CurvatureVec.curvVec (Submission.Diff.lcOf g) (γ t) u v v) u).symm
      rw [h2] at h1
      have hpos : 0 < c₀ * S₀ := mul_pos hc₀ hS₀pos
      linarith
    · -- the arc `[0,r]` is minimising
      have h := hγmin r ⟨hrpos.le, hrle⟩
      rw [hγ0]
      exact h
  -- ## Step 5: the drop bound along `[ρ,r]`
  let C : ℝ := β * (S₀ * Real.sqrt S₀ + S₀)
  have hCnn : 0 ≤ C := by
    simp only [C]
    positivity
  have hderiv : ∀ t ∈ Icc ρ r, HasDerivAt f (mvfderiv I S (γ t) (curveVelocity (I := I) γ t)) t := by
    intro t _
    have h := deriv_comp (I := I) (M := M) hSsm isOpen_univ hγsm (mem_univ t)
    simpa only [f] using h
  have hbound : ∀ t ∈ Icc ρ r,
      -C ≤ mvfderiv I S (γ t) (curveVelocity (I := I) γ t) := by
    intro t ht
    have ht_le : f t ≤ S₀ := hfle t ht
    have hg : Submission.Diff.gradSq g S (γ t) ≤ C ^ 2 := by
      have h1 := hgrad' (γ t)
      have h2 : β ^ 2 * (S (γ t)) ^ 3 + Cn ≤ C ^ 2 := by
        have := spread_grad_arith hβpos hS₀pos.le (show S (γ t) ≤ S₀ from ht_le) hCn
        simpa only [C] using this
      linarith
    have hcv := gradSq_cauchy (I := I) (M := M) g hSsm (γ t) (curveVelocity (I := I) γ t)
    have hunit : g.inner (γ t) (curveVelocity (I := I) γ t) (curveVelocity (I := I) γ t) = 1 := by
      have h1 : g.inner (γ t) (curveVelocity (I := I) γ t) (curveVelocity (I := I) γ t)
          = inner ℝ (curveVelocity (I := I) γ t) (curveVelocity (I := I) γ t) := rfl
      rw [h1, real_inner_self_eq_norm_sq, hγunit t]
      norm_num
    have hsq : (mvfderiv I S (γ t) (curveVelocity (I := I) γ t)) ^ 2 ≤ C ^ 2 := by
      have := hcv
      rw [hunit, mul_one] at this
      exact this.trans hg
    have habs : |mvfderiv I S (γ t) (curveVelocity (I := I) γ t)| ≤ C := by
      have h := sq_le_sq.mp hsq
      rwa [abs_of_nonneg hCnn] at h
    exact (abs_le.mp habs).1
  have hdrop := spread_drop_bound (f := f)
    (f' := fun t : ℝ => mvfderiv I S (γ t) (curveVelocity (I := I) γ t)) (C := C)
    hρmem.2 hderiv hbound
  -- ## Step 6: the two bounds on `r` contradict each other
  have hfr' : f r = c := hfr
  have hstep : ε * S₀ ≤ C * r := by
    rw [hfρ, hfr'] at hdrop
    have h2 : C * (r - ρ) ≤ C * r :=
      mul_le_mul_of_nonneg_left (by linarith [hρmem.1]) hCnn
    have h3 : S₀ - C * (r - ρ) ≤ (1 - ε) * S₀ := by
      simpa only [c] using hdrop
    nlinarith
  refine spread_numeric hc₀ hε hΘpos hβpos hββ₀ le_rfl ?_ hmyers
  exact hstep

end Work.Diff.L
