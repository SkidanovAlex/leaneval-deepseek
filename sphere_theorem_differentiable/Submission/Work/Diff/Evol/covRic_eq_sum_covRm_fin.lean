import Mathlib
import Submission.Work.Diff.GE.curvbasic
import Submission.Work.Diff.GE.covRic_eq_sum_covRm
import Submission.Work.Diff.Evol.Deps
import Submission.Work.Diff.GE.Kato3.CovRmKit
import Submission.Work.Diff.GE.frame_deps

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Filter

namespace Work.Diff.Evol

/-! ## The pointwise trace identity for `Ric` at the *smooth* level

`Work.Diff.GE.ricAt_eq_sum_frame` proves
`ricAt (lcOf g) x u v = ∑ m, rmP g x (e m) u (e m) v` for a `g`-orthonormal frame `e`, but only
under the *analytic* manifold hypothesis `IsManifold I (⊤ : WithTop ℕ∞) M`.  Analyticity of the
manifold does not follow from smoothness (`SMet I M` only asks for `IsManifold I ∞ M`), so we
re-prove the (basis-independence of the trace) identity with the same proof at the smooth level.
No further hypothesis is needed: the proof only uses the trace formula in the canonical basis
`Module.finBasis ℝ E`, the fact that `rmVec` is linear in its first slot (`rmVec_add_left`,
`rmVec_smul_left`, both at the smooth level), and `LinearMap.trace_eq_sum_inner` for the
orthonormal basis `basisOfOrthonormalOfCardEqFinrank hon`. -/
theorem ricAt_eq_sum_frame_ovf
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (((⊤ : ℕ∞) : WithTop ℕ∞)) M]
    [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M)
    (g : Submission.Diff.SMet I M) (x : M)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x) (he : Submission.Diff.IsONFrame g x e)
    (u v : TangentSpace I x) :
    Submission.Diff.ricAt (Submission.Diff.lcOf g) x u v
      = (Finset.univ : Finset (Fin (Module.finrank ℝ E))).sum
          (fun m => Submission.Diff.rmP g x (e m) u (e m) v) := by
  by_cases hn : Module.finrank ℝ E = 0
  · haveI : IsEmpty (Fin (Module.finrank ℝ E)) := by rw [hn]; infer_instance
    simp only [Submission.Diff.ricAt, Finset.univ_eq_empty, Finset.sum_empty]
  · letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    haveI : IsContMDiffRiemannianBundle I (((⊤ : ℕ∞) : WithTop ℕ∞)) E
        (fun x : M ↦ TangentSpace I x) := inferInstance
    obtain ⟨hcovne, -, -⟩ := hLC g
    obtain ⟨hcov⟩ := hcovne
    have hconv : ∀ a b : TangentSpace I x, Inner.inner ℝ a b = g.inner x a b := fun a b => rfl
    let T : E →ₗ[ℝ] E :=
      { toFun := fun w => Submission.Diff.rmVec (Submission.Diff.lcOf g) x w u v
        map_add' := fun a b =>
          Work.Diff.GE.rmVec_add_left (Submission.Diff.lcOf g) hcov x a b u v
        map_smul' := fun c a =>
          Work.Diff.GE.rmVec_smul_left (Submission.Diff.lcOf g) hcov x c a u v }
    have hleft : Submission.Diff.ricAt (Submission.Diff.lcOf g) x u v
        = ∑ i, (Module.finBasis ℝ E).coord i (T ((Module.finBasis ℝ E) i)) := rfl
    have hmatrix : (∑ i, (Module.finBasis ℝ E).coord i (T ((Module.finBasis ℝ E) i)))
        = Matrix.trace (LinearMap.toMatrix (Module.finBasis ℝ E) (Module.finBasis ℝ E) T) := by
      simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply,
        Module.Basis.coord_apply]
    have htrace : Matrix.trace (LinearMap.toMatrix (Module.finBasis ℝ E) (Module.finBasis ℝ E) T)
        = LinearMap.trace ℝ E T :=
      (LinearMap.trace_eq_matrix_trace ℝ (Module.finBasis ℝ E) T).symm
    have hbridge : LinearMap.trace ℝ E T = LinearMap.trace ℝ (TangentSpace I x) T := rfl
    have hnpos : 0 < Module.finrank ℝ E := Nat.pos_of_ne_zero hn
    haveI : Nonempty (Fin (Module.finrank ℝ E)) := Fin.pos_iff_nonempty.mp hnpos
    have hon : Orthonormal ℝ e := by
      rw [orthonormal_iff_ite]
      intro i j
      rw [hconv (e i) (e j)]
      exact he i j
    let c : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) :=
      basisOfOrthonormalOfCardEqFinrank hon (by rw [Fintype.card_fin]; rfl)
    have hc : (c : Fin (Module.finrank ℝ E) → TangentSpace I x) = e :=
      coe_basisOfOrthonormalOfCardEqFinrank hon _
    have honc : Orthonormal ℝ (c : Fin (Module.finrank ℝ E) → TangentSpace I x) := by
      rw [hc]; exact hon
    have hsuminner : LinearMap.trace ℝ (TangentSpace I x) T
        = ∑ i, Inner.inner ℝ (e i) (T (e i)) := by
      have h := LinearMap.trace_eq_sum_inner T (c.toOrthonormalBasis honc)
      rw [Module.Basis.coe_toOrthonormalBasis c honc, hc] at h
      exact h
    have hfinal : (∑ i, Inner.inner ℝ (e i) (T (e i)))
        = ∑ i, Submission.Diff.rmP g x (e i) u (e i) v := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hconv (e i) (T (e i)), g.symm x (e i) (T (e i))]
      rfl
    exact hleft.trans (hmatrix.trans (htrace.trans (hbridge.trans (hsuminner.trans hfinal))))

/-- **Trace identity for `∇Ric` in an orthonormal frame.**  For a `g`-orthonormal frame `e` of `TₓM`,
`(∇_v Ric)(a,b) = ∑_m (∇_v Rm)(e_m, a, e_m, b)`, for an *arbitrary* orthonormal frame `e` (not only `onFrame`).

This is `Work.Diff.GE.covRic_eq_sum_covRm` with (a) the frame `onFrame g x` replaced by an arbitrary
orthonormal frame `e`, (b) the hypothesis `htr` dropped, (c) `[CompactSpace M]` dropped, and (d) the
manifold hypothesis at the SMOOTH level (`IsManifold I (((⊤ : ℕ∞) : WithTop ℕ∞)) M`): note that
`Work.Diff.GE.ricAt_eq_sum_frame` and `Work.Diff.GE.covRic_eq_sum_covRm` are both stated with the
*analytic* hypothesis `IsManifold I (⊤ : WithTop ℕ∞) M`, which does NOT follow from smoothness, so
you must re-state/re-prove the pointwise trace identity
`ricAt (lcOf g) y u v = ∑ m, rmP g y (e m) u (e m) v` for orthonormal `e` at the smooth level
(copy the short proof of `ricAt_eq_sum_frame`, its ingredients — `rmVec_add_left`, `rmVec_smul_left`,
`basisOfOrthonormalOfCardEqFinrank`, `LinearMap.trace_eq_sum_inner` — are all at the smooth level).

ROUTE for the main statement: copy the proof of `Work.Diff.GE.covRic_eq_sum_covRm` (read it!):
take `V i := smoothExt x (e i)`, get a smooth frame `W := katoFrame g x V`, orthonormal near `x` with
`W i x = e i` via `Work.Diff.GE.covRic_onFrame_family` (no `CompactSpace`); the identity of functions
`ricAt (lcOf g) y (A y) (B y) = ∑ m, rmP g y (W m y) (A y) (W m y) (B y)` near `x` (with
`A = smoothExt x a`, `B = smoothExt x b`) holds pointwise for `y` near `x` by the trace identity
(re-proved as above); differentiate both sides at `x` in direction `v`
(`Kato3.mvfderiv_sum`, `Work.Diff.Evol.mvfderiv_ricF_eq`, `covRic_eq_dRicPhi`,
`Work.Diff.GE.covRic_frame_correction_zero`, `Kato3.covRm_field_form`), and finish with
`Work.Diff.GE.Kato3.covRm_field_form` to turn `dRmPhi` into `covRm` — the chain-A version of the source
proof, with `W m x = e m` in place of `onFrame`. -/
theorem covRic_eq_sum_covRm_fin
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (((⊤ : ℕ∞) : WithTop ℕ∞)) M]
    [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (x : M)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x) (he : Submission.Diff.IsONFrame g x e)
    (v a b : TangentSpace I x) :
    Work.Diff.Evol.covRic g x v a b
      = (Finset.univ : Finset (Fin (Module.finrank ℝ E))).sum
          (fun m => Submission.Diff.covRm g x v (e m) a (e m) b) := by
  classical
  -- a smooth `g`-orthonormal frame near `x` agreeing with `e` at `x`
  have hVs : ∀ i : Work.Diff.GE.katoIdx E, CMDiff ∞ (T% (smoothExt x (e i))) :=
    fun i => Work.Diff.GE.smoothExt_cmdiff x (e i)
  have hVON : IsONFrame g x (fun i => smoothExt x (e i) x) := by
    have h : (fun i => smoothExt x (e i) x) = e := by
      funext i; exact Work.Diff.GE.smoothExt_apply x (e i)
    rw [h]; exact he
  obtain ⟨hWs0, hWON0, hWx0⟩ :=
    Work.Diff.GE.covRic_onFrame_family g x (fun i => smoothExt x (e i)) hVs hVON
  set W : Work.Diff.GE.katoIdx E → Π y : M, TangentSpace I y :=
    Work.Diff.GE.katoFrame g x (fun i => smoothExt x (e i)) with hWdef
  have hWs : ∀ i : Work.Diff.GE.katoIdx E, CMDiff ∞ (T% (W i)) := fun i => by
    rw [hWdef]; exact hWs0 i
  have hWON : ∀ᶠ y in 𝓝 x, IsONFrame g y (fun i => W i y) := by rw [hWdef]; exact hWON0
  have hWx : ∀ i : Work.Diff.GE.katoIdx E, W i x = e i := by
    intro i; rw [hWx0 i, Work.Diff.GE.smoothExt_apply]
  have hONx : IsONFrame g x (fun m => W m x) := hWON.self_of_nhds
  -- the smooth extensions of `a` and `b`
  set A : Π y : M, TangentSpace I y := smoothExt x a with hA
  set B : Π y : M, TangentSpace I y := smoothExt x b with hB
  have hAs : CMDiff ∞ (T% A) := by rw [hA]; exact Work.Diff.GE.smoothExt_cmdiff x a
  have hBs : CMDiff ∞ (T% B) := by rw [hB]; exact Work.Diff.GE.smoothExt_cmdiff x b
  have hAx : A x = a := by rw [hA]; exact Work.Diff.GE.smoothExt_apply x a
  have hBx : B x = b := by rw [hB]; exact Work.Diff.GE.smoothExt_apply x b
  -- `Ric` and the frame trace agree near `x` (the smooth-level trace identity)
  have hsm : ∀ m : Work.Diff.GE.katoIdx E,
      CMDiff ∞ (fun y : M => rmP g y (W m y) (A y) (W m y) (B y)) :=
    fun m => Work.Diff.GE.rmP_fields_smooth hLC g (hWs m) hAs (hWs m) hBs
  have hagree : (ricF g A B)
      =ᶠ[𝓝 x] (fun y : M => ∑ m, rmP g y (W m y) (A y) (W m y) (B y)) := by
    filter_upwards [hWON] with y hy
    simpa only [ricF] using
      ricAt_eq_sum_frame_ovf (I := I) (M := M) hLC g y (fun m => W m y) hy (A y) (B y)
  have hkey : mvfderiv I (ricF g A B) x v
      = ∑ m, mvfderiv I (fun y : M => rmP g y (W m y) (A y) (W m y) (B y)) x v := by
    have h := Work.Diff.GE.mvfderiv_congr_eventuallyEq (I := I) hagree
    exact (congrArg (fun L : TangentSpace I x →L[ℝ] ℝ => L v) h).trans
      (Work.Diff.GE.Kato3.mvfderiv_sum Finset.univ _ hsm x v)
  have hric : mvfderiv I (ricF g A B) x v
      = dRicPhi g x v A B + ricAt (lcOf g) x (lcOf g A x v) (B x)
        + ricAt (lcOf g) x (A x) (lcOf g B x v) :=
    mvfderiv_ricF_eq g x v A B
  -- the definition of `dRmPhi` on the frame
  have hdRm : ∀ m : Work.Diff.GE.katoIdx E,
      Work.Diff.GE.dRmPhi g x v (W m) A (W m) B
        = mvfderiv I (fun y : M => rmP g y (W m y) (A y) (W m y) (B y)) x v
          - rmP g x (lcOf g (W m) x v) (A x) (W m x) (B x)
          - rmP g x (W m x) (lcOf g A x v) (W m x) (B x)
          - rmP g x (W m x) (A x) (lcOf g (W m) x v) (B x)
          - rmP g x (W m x) (A x) (W m x) (lcOf g B x v) := by
    intro m
    simp only [Work.Diff.GE.dRmPhi]
  -- summing the definition of `dRmPhi` gives an identity relating the five sums
  have h1 : (∑ m : Work.Diff.GE.katoIdx E, Work.Diff.GE.dRmPhi g x v (W m) A (W m) B)
      + (∑ m, rmP g x (lcOf g (W m) x v) (A x) (W m x) (B x))
      + (∑ m, rmP g x (W m x) (lcOf g A x v) (W m x) (B x))
      + (∑ m, rmP g x (W m x) (A x) (lcOf g (W m) x v) (B x))
      + (∑ m, rmP g x (W m x) (A x) (W m x) (lcOf g B x v))
      = ∑ m, mvfderiv I (fun y : M => rmP g y (W m y) (A y) (W m y) (B y)) x v := by
    simp only [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hdRm m]
    ring
  -- the two frame-derivative corrections cancel
  have hPR : (∑ m : Work.Diff.GE.katoIdx E,
        rmP g x (lcOf g (W m) x v) (A x) (W m x) (B x))
      + (∑ m, rmP g x (W m x) (A x) (lcOf g (W m) x v) (B x)) = 0 :=
    Work.Diff.GE.covRic_frame_correction_zero hLC g x v W hWs hWON (A x) (B x)
  -- the two `∇A`, `∇B` corrections are the `ricAt` corrections
  have hQr : (∑ m : Work.Diff.GE.katoIdx E,
        rmP g x (W m x) (lcOf g A x v) (W m x) (B x))
      = ricAt (lcOf g) x (lcOf g A x v) (B x) :=
    (ricAt_eq_sum_frame_ovf (I := I) (M := M) hLC g x (fun m => W m x) hONx
      (lcOf g A x v) (B x)).symm
  have hYr : (∑ m : Work.Diff.GE.katoIdx E,
        rmP g x (W m x) (A x) (W m x) (lcOf g B x v))
      = ricAt (lcOf g) x (A x) (lcOf g B x v) :=
    (ricAt_eq_sum_frame_ovf (I := I) (M := M) hLC g x (fun m => W m x) hONx
      (A x) (lcOf g B x v)).symm
  have h2 : (∑ m : Work.Diff.GE.katoIdx E,
        mvfderiv I (fun y : M => rmP g y (W m y) (A y) (W m y) (B y)) x v)
      = dRicPhi g x v A B
        + ricAt (lcOf g) x (lcOf g A x v) (B x)
        + ricAt (lcOf g) x (A x) (lcOf g B x v) := by
    rw [← hkey, hric]
  -- the trace of `∇Rm` is `dRicPhi`
  have hmain : dRicPhi g x v A B
      = ∑ m : Work.Diff.GE.katoIdx E, Work.Diff.GE.dRmPhi g x v (W m) A (W m) B := by
    linarith [h1, h2, hPR, hQr, hYr]
  -- rewrite `dRmPhi` back into `covRm`
  have hper : ∀ m : Work.Diff.GE.katoIdx E,
      Work.Diff.GE.dRmPhi g x v (W m) A (W m) B = covRm g x v (e m) a (e m) b := by
    intro m
    have h := Work.Diff.GE.Kato3.covRm_field_form (X₁ := W m) (X₂ := A) (X₃ := W m) (X₄ := B)
      hLC g x v (hWs m) hAs (hWs m) hBs
    rw [hWx m, hAx, hBx] at h
    exact h.symm
  have hDRsm : dRicPhi g x v A B
      = dRicPhi g x v (smoothExt x a) (smoothExt x b) := by
    rw [hA, hB]
  rw [covRic_eq_dRicPhi (I := I) (M := M) g x v a b]
  rw [← hDRsm, hmain]
  exact Finset.sum_congr rfl (fun m _ => hper m)

end Work.Diff.Evol
