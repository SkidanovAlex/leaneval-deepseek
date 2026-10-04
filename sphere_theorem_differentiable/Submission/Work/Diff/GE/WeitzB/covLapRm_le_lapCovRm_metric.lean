import Mathlib
import Submission.Work.Diff.GE.ReactionDefs
import Submission.Work.Diff.GE.cov3Rm_ricci
import Submission.Work.Diff.GE.cov3Rm_swap
import Submission.Work.Diff.GE.frameMotion_cancel_cov2Rm
import Submission.Work.Diff.GE.lapCovRmAt_trace
import Submission.Work.Diff.GE.onFrameONfield
import Submission.Work.Diff.GE.kato_cov3RmExt_field
import Submission.Work.Diff.GE.covLapRmAt_eq_sum_cov3Rm
import Submission.Work.Diff.GE.kato_second_deriv_defs
import Submission.Work.Diff.GE.dRmPhi
import Submission.Work.Diff.GE.curvDerivInner
import Submission.Work.Diff.GE.curvDerivNormSq_le
import Submission.Work.Diff.GE.connectionVariation_le
import Submission.Work.Diff.Evol.ricci_identity_rm

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Weitzenböck (Bochner) inequality for the rough Laplacian of the curvature

`Work.Diff.GE.covLapRmAt g x v a b c d` is the covariant derivative `∇_v(ΔRm)` of the rough
Laplacian of the curvature, and `Work.Diff.GE.lapCovRmAt g x v a b c d` is `Δ(∇Rm)` evaluated on the
same five vectors.  Their difference is the commutator `[Δ, ∇_v]Rm`, which by the Weitzenböck
identity is a purely algebraic contraction of `Rm` with `∇Rm`; this file proves that it is bounded
by `C |Rm| |∇Rm| ‖v‖ ‖a‖ ‖b‖ ‖c‖ ‖d‖` with a constant `C` depending only on `dim E` — that is the
statement `Work.Diff.GE.WeitzB.covLapRm_le_lapCovRm_metric`.

The route is:

* `covLapRmAt_eq_sum_cov3Rm_frame` (this file): in a frame `F` which is `g`-orthonormal near `x`,
  `covLapRmAt g x v a b c d = ∑_m ∇³Rm(v, F m, F m, a, b, c, d)`; the frame-motion terms of the
  `y`-dependent frame cancel (`Work.Diff.GE.frameMotion_cancel_cov2Rm`) and the four tensorialising
  corrections cancel against those in the definition of `covLapRmAt` (via
  `Work.Diff.GE.lapRmAt_trace`).  Together with `Work.Diff.GE.lapCovRmAt_trace` (the same trace for
  `Δ(∇Rm)`) this writes the difference as `∑_m (cov3Rm(v,e_m,e_m,…) − cov3Rm(e_m,e_m,v,…))`.
* the two Ricci identities `Work.Diff.GE.cov3Rm_ricci` and `Work.Diff.GE.cov3Rm_swap` express each
  summand as a sum of thirteen terms, each of them a product of one curvature component with one
  component of `∇Rm` (times frame coefficients of the five vectors);
* each such term is then bounded by Cauchy–Schwarz in the orthonormal frame.

Everything is pointwise and at the smooth manifold level `IsManifold I (⊤ : ℕ∞) M`, which is the
level of the frozen interfaces `SMet I M` and `LCSmooth I M`; the constant only depends on
`Module.finrank ℝ E`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

namespace Work.Diff.GE.WeitzB

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]

/-! ## Elementary facts about the metric -/

/-- The `g`-norm of a tangent vector. -/
private noncomputable def nrm (g : SMet I M) (x : M) (u : TangentSpace I x) : ℝ :=
  Real.sqrt (g.inner x u u)

private theorem nrm_nonneg (g : SMet I M) (x : M) (u : TangentSpace I x) : 0 ≤ nrm g x u :=
  Real.sqrt_nonneg _

/-- The envelope `|Rm| |∇Rm| ‖v‖‖a‖‖b‖‖c‖‖d‖` of the Weitzenböck bound, written exactly in the
shape of the target statement. -/
private noncomputable def Env (g : SMet I M) (x : M) (v a b c d : TangentSpace I x) : ℝ :=
  Real.sqrt (rmNormSq g x) * Real.sqrt (dRmNormSq g x)
    * (Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x a a) * Real.sqrt (g.inner x b b)
       * Real.sqrt (g.inner x c c) * Real.sqrt (g.inner x d d))

private theorem inner_self_nonneg (g : SMet I M) (x : M) (v : TangentSpace I x) :
    0 ≤ g.inner x v v := by
  rcases eq_or_ne v 0 with h | h
  · subst h; simp
  · exact le_of_lt (g.pos x v h)

/-- Cauchy–Schwarz for a single Riemannian metric. -/
private theorem inner_cauchy (g : SMet I M) (x : M) (v w : TangentSpace I x) :
    |g.inner x v w| ≤ Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x w w) := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  have h1 : g.inner x v w = Inner.inner ℝ v w := rfl
  have h2 : g.inner x v v = Inner.inner ℝ v v := rfl
  have h3 : g.inner x w w = Inner.inner ℝ w w := rfl
  rw [h1, h2, h3]
  have hcs : |Inner.inner ℝ v w| ≤ ‖v‖ * ‖w‖ := abs_real_inner_le_norm v w
  have hv : Real.sqrt (Inner.inner ℝ v v) = ‖v‖ := by
    rw [real_inner_self_eq_norm_sq, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg v)]
  have hw : Real.sqrt (Inner.inner ℝ w w) = ‖w‖ := by
    rw [real_inner_self_eq_norm_sq, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg w)]
  rw [hv, hw]
  exact hcs

private theorem sqrt_mul4 {p q r s : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    Real.sqrt (p * q * r * s) = Real.sqrt p * Real.sqrt q * Real.sqrt r * Real.sqrt s := by
  rw [Real.sqrt_mul (mul_nonneg (mul_nonneg hp hq) hr),
    Real.sqrt_mul (mul_nonneg hp hq), Real.sqrt_mul hp]

private theorem sqrt_mul5 {p q r s t : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (ht : 0 ≤ t) :
    Real.sqrt (p * q * r * s * t)
      = Real.sqrt p * Real.sqrt q * Real.sqrt r * Real.sqrt s * Real.sqrt t := by
  rw [Real.sqrt_mul (mul_nonneg (mul_nonneg (mul_nonneg hp hq) hr) hs),
    Real.sqrt_mul (mul_nonneg (mul_nonneg hp hq) hr), Real.sqrt_mul (mul_nonneg hp hq),
    Real.sqrt_mul hp]

/-! ## The pointwise bounds for `∇Rm` and for the curvature vector `R(u,w)z` -/

/-- **The `(0,5)`-tensor bound for `∇Rm`.**  `covRm g x v a b c d = (∇_v Rm)(a,b,c,d)` is bounded by
`√|∇Rm|²` times the `g`-norms of the five vectors.  Proof: `covRm v a b c d` is the pairing of the
curvature-derivative vector `curvDeriv g x v a b d` (`Work.Diff.GE.curvDerivInner`) with `c`, so
Cauchy–Schwarz (`inner_cauchy`) and the pointwise estimate
`Work.Diff.GE.curvDerivNormSq_le` give the claim. -/
theorem covRm_abs_le (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (v a b c d : TangentSpace I x) :
    |covRm g x v a b c d|
      ≤ Real.sqrt (dRmNormSq g x) * (nrm g x v * nrm g x a * nrm g x b * nrm g x c * nrm g x d) := by
  have hval : covRm g x v a b c d = g.inner x (curvDeriv g x v a b d) c :=
    (curvDerivInner hLC g x v a b d c).symm
  have hD : 0 ≤ dRmNormSq g x := Work.Diff.GE.Gest.dRmNormSq_nonneg g x
  have hcs := inner_cauchy g x (curvDeriv g x v a b d) c
  have hW : g.inner x (curvDeriv g x v a b d) (curvDeriv g x v a b d)
      ≤ dRmNormSq g x * (g.inner x v v) * (g.inner x a a) * (g.inner x b b) * (g.inner x d d) :=
    curvDerivNormSq_le hLC g x v a b d
  have hsqrt : Real.sqrt (g.inner x (curvDeriv g x v a b d) (curvDeriv g x v a b d))
      ≤ Real.sqrt (dRmNormSq g x) * (nrm g x v * nrm g x a * nrm g x b * nrm g x d) := by
    refine le_trans (Real.sqrt_le_sqrt hW) (le_of_eq ?_)
    rw [sqrt_mul5 hD (inner_self_nonneg g x v) (inner_self_nonneg g x a)
        (inner_self_nonneg g x b) (inner_self_nonneg g x d)]
    simp only [nrm]
    ring
  calc |covRm g x v a b c d| = |g.inner x (curvDeriv g x v a b d) c| := by rw [hval]
    _ ≤ Real.sqrt (g.inner x (curvDeriv g x v a b d) (curvDeriv g x v a b d))
          * Real.sqrt (g.inner x c c) := hcs
    _ ≤ (Real.sqrt (dRmNormSq g x) * (nrm g x v * nrm g x a * nrm g x b * nrm g x d))
          * Real.sqrt (g.inner x c c) :=
        mul_le_mul_of_nonneg_right hsqrt (Real.sqrt_nonneg _)
    _ = Real.sqrt (dRmNormSq g x)
          * (nrm g x v * nrm g x a * nrm g x b * nrm g x c * nrm g x d) := by
        simp only [nrm]; ring

/-- **The curvature-vector bound.**  The squared `g`-norm of `R(u,w)z = rmVec (lcOf g) x u w z` is
bounded by `(dim+1)² |Rm|² |u|²|w|²|z|²`.  Proof: Parseval in the orthonormal frame
(`Work.Diff.GE.onFrame_parseval_sq`) writes the squared norm as `∑_k (rmP g x u w e_k z)²`
(`rmP` is the curvature form), and each summand is bounded by
`Work.Diff.GE.rmP_norm_bound_smooth`. -/
theorem rmVec_sq_le [I.Boundaryless] [CompactSpace M] (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (u w z : TangentSpace I x) :
    g.inner x (rmVec (lcOf g) x u w z) (rmVec (lcOf g) x u w z)
      ≤ ((Module.finrank ℝ E : ℝ) + 1) ^ 2 * rmNormSq g x * (g.inner x u u)
          * (g.inner x w w) * (g.inner x z z) := by
  classical
  have hR : 0 ≤ rmNormSq g x := Work.Diff.GE.Gest.rmNormSq_nonneg g x
  have hu : 0 ≤ g.inner x u u := inner_self_nonneg g x u
  have hw : 0 ≤ g.inner x w w := inner_self_nonneg g x w
  have hz : 0 ≤ g.inner x z z := inner_self_nonneg g x z
  have hnle : (Module.finrank ℝ E : ℝ) ≤ ((Module.finrank ℝ E : ℝ) + 1) ^ 2 := by nlinarith
  by_cases hfr : 0 < Module.finrank ℝ E
  · -- Parseval in the orthonormal frame
    have hp : g.inner x (rmVec (lcOf g) x u w z) (rmVec (lcOf g) x u w z)
        = ∑ k, (rmP g x u w (onFrame g x k) z) ^ 2 := by
      rw [← onFrame_parseval_sq g x hfr (rmVec (lcOf g) x u w z)]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [g.symm x (onFrame g x k) (rmVec (lcOf g) x u w z)]
      rfl
    -- each summand is bounded by the same multiple of `|Rm|²|u|²|w|²|z|²`
    have hk : ∀ k, (rmP g x u w (onFrame g x k) z) ^ 2
        ≤ rmNormSq g x * (g.inner x u u) * (g.inner x w w) * (g.inner x z z) := by
      intro k
      have hone : g.inner x (onFrame g x k) (onFrame g x k) = 1 := by
        have h := isONFrame_onFrame g x k k
        simpa using h
      have hb := rmP_norm_bound_smooth hLC g x u w (onFrame g x k) z
      refine le_trans (sq_le_sq' (abs_le.mp hb).1 (abs_le.mp hb).2) (le_of_eq ?_)
      repeat rw [mul_pow]
      rw [Real.sq_sqrt hR, Real.sq_sqrt hu, Real.sq_sqrt hw,
        Real.sq_sqrt hz, Real.sq_sqrt (by rw [hone]; norm_num), hone]
      ring
    calc g.inner x (rmVec (lcOf g) x u w z) (rmVec (lcOf g) x u w z)
        = ∑ k, (rmP g x u w (onFrame g x k) z) ^ 2 := hp
      _ ≤ ∑ _k : Fin (Module.finrank ℝ E),
            rmNormSq g x * (g.inner x u u) * (g.inner x w w) * (g.inner x z z) :=
          Finset.sum_le_sum (fun k _ => hk k)
      _ = (Module.finrank ℝ E : ℝ) * (rmNormSq g x * (g.inner x u u) * (g.inner x w w)
            * (g.inner x z z)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ ((Module.finrank ℝ E : ℝ) + 1) ^ 2 * rmNormSq g x * (g.inner x u u)
            * (g.inner x w w) * (g.inner x z z) := by
          have h0 : 0 ≤ rmNormSq g x * (g.inner x u u) * (g.inner x w w) * (g.inner x z z) :=
            mul_nonneg (mul_nonneg (mul_nonneg hR hu) hw) hz
          calc (Module.finrank ℝ E : ℝ) * (rmNormSq g x * (g.inner x u u) * (g.inner x w w)
                * (g.inner x z z))
              ≤ ((Module.finrank ℝ E : ℝ) + 1) ^ 2 * (rmNormSq g x * (g.inner x u u)
                * (g.inner x w w) * (g.inner x z z)) :=
                mul_le_mul_of_nonneg_right hnle h0
            _ = ((Module.finrank ℝ E : ℝ) + 1) ^ 2 * rmNormSq g x * (g.inner x u u)
                * (g.inner x w w) * (g.inner x z z) := by ring
  · -- degenerate case: `finrank ℝ E = 0`, all tangent vectors vanish
    have h0 : Module.finrank ℝ E = 0 := Nat.eq_zero_of_not_pos hfr
    have hsub : Subsingleton E := Module.finrank_zero_iff.mp h0
    haveI : Subsingleton (TangentSpace I x) := hsub
    have hu0 : u = 0 := Subsingleton.elim u 0
    have hw0 : w = 0 := Subsingleton.elim w 0
    have hz0 : z = 0 := Subsingleton.elim z 0
    rw [hu0, hw0, hz0]
    have hv0 : rmVec (lcOf g) x 0 0 0 = 0 := Subsingleton.elim _ _
    rw [hv0]
    simp

/-- The `√`-form of `rmVec_sq_le`: the norm of `R(u,w)z` is bounded by `(dim+1) |Rm| |u||w||z|`. -/
theorem rmVec_nrm_le [I.Boundaryless] [CompactSpace M] (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (u w z : TangentSpace I x) :
    nrm g x (rmVec (lcOf g) x u w z)
      ≤ ((Module.finrank ℝ E : ℝ) + 1) * Real.sqrt (rmNormSq g x)
          * (nrm g x u * nrm g x w * nrm g x z) := by
  have hR : 0 ≤ rmNormSq g x := Work.Diff.GE.Gest.rmNormSq_nonneg g x
  have hu : 0 ≤ g.inner x u u := inner_self_nonneg g x u
  have hw : 0 ≤ g.inner x w w := inner_self_nonneg g x w
  have hz : 0 ≤ g.inner x z z := inner_self_nonneg g x z
  have hsq := rmVec_sq_le (I := I) (M := M) hLC g x u w z
  have h1 : nrm g x (rmVec (lcOf g) x u w z) ^ 2
      ≤ (((Module.finrank ℝ E : ℝ) + 1) * Real.sqrt (rmNormSq g x)
          * (nrm g x u * nrm g x w * nrm g x z)) ^ 2 := by
    rw [show nrm g x (rmVec (lcOf g) x u w z) ^ 2
        = g.inner x (rmVec (lcOf g) x u w z) (rmVec (lcOf g) x u w z) from by
      simp only [nrm, Real.sq_sqrt (inner_self_nonneg g x _)]]
    refine le_trans hsq (le_of_eq ?_)
    simp only [nrm]
    repeat rw [mul_pow]
    rw [Real.sq_sqrt hR, Real.sq_sqrt hu, Real.sq_sqrt hw, Real.sq_sqrt hz]
    ring
  have hb : 0 ≤ ((Module.finrank ℝ E : ℝ) + 1) * Real.sqrt (rmNormSq g x)
      * (nrm g x u * nrm g x w * nrm g x z) :=
    mul_nonneg (mul_nonneg (by positivity) (Real.sqrt_nonneg _))
      (mul_nonneg (mul_nonneg (nrm_nonneg g x u) (nrm_nonneg g x w)) (nrm_nonneg g x z))
  calc nrm g x (rmVec (lcOf g) x u w z)
      = Real.sqrt (nrm g x (rmVec (lcOf g) x u w z) ^ 2) :=
        (Real.sqrt_sq (nrm_nonneg g x _)).symm
    _ ≤ Real.sqrt ((((Module.finrank ℝ E : ℝ) + 1) * Real.sqrt (rmNormSq g x)
          * (nrm g x u * nrm g x w * nrm g x z)) ^ 2) := Real.sqrt_le_sqrt h1
    _ = ((Module.finrank ℝ E : ℝ) + 1) * Real.sqrt (rmNormSq g x)
          * (nrm g x u * nrm g x w * nrm g x z) := Real.sqrt_sq hb

/-- The `√`-form of `curvDerivNormSq_le`: the norm of `(∇_X R)(Y,P)Z` is bounded by
`√|∇Rm|² |X||Y||P||Z|`. -/
theorem curvDeriv_nrm_le (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (X Y P Z : TangentSpace I x) :
    nrm g x (curvDeriv g x X Y P Z)
      ≤ Real.sqrt (dRmNormSq g x) * (nrm g x X * nrm g x Y * nrm g x P * nrm g x Z) := by
  have hlhs : nrm g x (curvDeriv g x X Y P Z) ^ 2
      = g.inner x (curvDeriv g x X Y P Z) (curvDeriv g x X Y P Z) := by
    simp only [nrm, Real.sq_sqrt (inner_self_nonneg g x _)]
  have hb : 0 ≤ Real.sqrt (dRmNormSq g x) * (nrm g x X * nrm g x Y * nrm g x P * nrm g x Z) :=
    mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg (mul_nonneg (mul_nonneg (nrm_nonneg g x X)
      (nrm_nonneg g x Y)) (nrm_nonneg g x P)) (nrm_nonneg g x Z))
  calc nrm g x (curvDeriv g x X Y P Z)
      = Real.sqrt (nrm g x (curvDeriv g x X Y P Z) ^ 2) :=
        (Real.sqrt_sq (nrm_nonneg g x _)).symm
    _ ≤ Real.sqrt ((Real.sqrt (dRmNormSq g x)
          * (nrm g x X * nrm g x Y * nrm g x P * nrm g x Z)) ^ 2) := by
        refine Real.sqrt_le_sqrt ?_
        rw [hlhs]
        refine le_trans (curvDerivNormSq_le hLC g x X Y P Z) (le_of_eq ?_)
        simp only [nrm]
        repeat rw [mul_pow]
        rw [Real.sq_sqrt (Work.Diff.GE.Gest.dRmNormSq_nonneg g x),
          Real.sq_sqrt (inner_self_nonneg g x X), Real.sq_sqrt (inner_self_nonneg g x Y),
          Real.sq_sqrt (inner_self_nonneg g x P), Real.sq_sqrt (inner_self_nonneg g x Z)]
        ring
    _ = Real.sqrt (dRmNormSq g x) * (nrm g x X * nrm g x Y * nrm g x P * nrm g x Z) :=
        Real.sqrt_sq hb

/-! ## The trace of `∇³Rm` and the covariant derivative of the Laplacian -/

/-- **The covariant derivative of the Laplacian is a trace of `∇³Rm`.**  If `F` is a family of
globally `C^∞` fields which is `g`-orthonormal near `x`, then
`covLapRmAt g x v a b c d = ∑_m ∇³Rm(v, F m, F m, a, b, c, d)`.

The frame-motion terms produced by differentiating the `y`-dependent chosen frame inside the trace
`lapRmAt` cancel over `m` (`Work.Diff.GE.frameMotion_cancel_cov2Rm`), and the four tensorialising
corrections cancel against the four corrections in the definition of `covLapRmAt` (two applications
of `Work.Diff.GE.lapRmAt_trace`).  A family `F` with these properties exists at every `x` by
`Work.Diff.GE.onFrameONfield`. -/
theorem covLapRmAt_eq_sum_cov3Rm_frame
    (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (F : Fin (Module.finrank ℝ E) → (Π y : M, TangentSpace I y))
    (hFs : ∀ i, SmoothField M (F i)) (hFON : OnFrameNear g x F)
    (v a b c d : TangentSpace I x) :
    covLapRmAt g x v a b c d = ∑ m, cov3Rm g x v (F m x) (F m x) a b c d := by
  classical
  have hA : CMDiff ∞ (T% (smoothExt x a)) := smoothExt_cmdiff x a
  have hB : CMDiff ∞ (T% (smoothExt x b)) := smoothExt_cmdiff x b
  have hC : CMDiff ∞ (T% (smoothExt x c)) := smoothExt_cmdiff x c
  have hD : CMDiff ∞ (T% (smoothExt x d)) := smoothExt_cmdiff x d
  have hONx : IsONFrame g x (fun i => F i x) := hFON.self_of_nhds
  -- the trace of `ΔRm` computed in the frame `F`, near `x`
  have htr : (fun y : M => lapRmAt g y (smoothExt x a y) (smoothExt x b y) (smoothExt x c y)
        (smoothExt x d y))
      =ᶠ[𝓝 x] (fun y : M => ∑ m, cov2Rm g y (F m y) (F m y) (smoothExt x a y)
        (smoothExt x b y) (smoothExt x c y) (smoothExt x d y)) := by
    filter_upwards [hFON] with y hy
    exact lapRmAt_trace hLC g y (fun i => F i y) hy _ _ _ _
  -- its derivative, term by term
  have hsum1 : mvfderiv I (fun y : M => lapRmAt g y (smoothExt x a y) (smoothExt x b y)
        (smoothExt x c y) (smoothExt x d y)) x v
      = ∑ m, (cov3RmExt g x v (F m) (F m) (smoothExt x a) (smoothExt x b) (smoothExt x c)
            (smoothExt x d)
          + cov2Rm g x (lcOf g (F m) x v) (F m x) a b c d
          + cov2Rm g x (F m x) (lcOf g (F m) x v) a b c d
          + cov2Rm g x (F m x) (F m x) (lcOf g (smoothExt x a) x v) b c d
          + cov2Rm g x (F m x) (F m x) a (lcOf g (smoothExt x b) x v) c d
          + cov2Rm g x (F m x) (F m x) a b (lcOf g (smoothExt x c) x v) d
          + cov2Rm g x (F m x) (F m x) a b c (lcOf g (smoothExt x d) x v)) := by
    rw [mvfderiv_congr_eventuallyEq htr]
    rw [Work.Diff.GE.Kato3.mvfderiv_sum Finset.univ _
      (fun m => Work.Diff.GE.Kato3.cov2Rm_field_smooth hLC g (hFs m) (hFs m) hA hB hC hD) x v]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [mvfderiv_cov2Rm_eq hLC g x v (F m) (F m) (smoothExt x a) (smoothExt x b)
      (smoothExt x c) (smoothExt x d)]
    simp only [smoothExt_apply]
  have hsplit : (∑ m, (cov3RmExt g x v (F m) (F m) (smoothExt x a) (smoothExt x b)
          (smoothExt x c) (smoothExt x d)
        + cov2Rm g x (lcOf g (F m) x v) (F m x) a b c d
        + cov2Rm g x (F m x) (lcOf g (F m) x v) a b c d
        + cov2Rm g x (F m x) (F m x) (lcOf g (smoothExt x a) x v) b c d
        + cov2Rm g x (F m x) (F m x) a (lcOf g (smoothExt x b) x v) c d
        + cov2Rm g x (F m x) (F m x) a b (lcOf g (smoothExt x c) x v) d
        + cov2Rm g x (F m x) (F m x) a b c (lcOf g (smoothExt x d) x v)))
      = (∑ m, cov3RmExt g x v (F m) (F m) (smoothExt x a) (smoothExt x b) (smoothExt x c)
            (smoothExt x d))
        + (∑ m, (cov2Rm g x (lcOf g (F m) x v) (F m x) a b c d
            + cov2Rm g x (F m x) (lcOf g (F m) x v) a b c d))
        + (∑ m, cov2Rm g x (F m x) (F m x) (lcOf g (smoothExt x a) x v) b c d)
        + (∑ m, cov2Rm g x (F m x) (F m x) a (lcOf g (smoothExt x b) x v) c d)
        + (∑ m, cov2Rm g x (F m x) (F m x) a b (lcOf g (smoothExt x c) x v) d)
        + (∑ m, cov2Rm g x (F m x) (F m x) a b c (lcOf g (smoothExt x d) x v)) := by
    simp only [Finset.sum_add_distrib]
    ring
  have hc12 : (∑ m, (cov2Rm g x (lcOf g (F m) x v) (F m x) a b c d
        + cov2Rm g x (F m x) (lcOf g (F m) x v) a b c d)) = 0 :=
    frameMotion_cancel_cov2Rm hLC g x F hFs hFON v a b c d
  have hc3 : (∑ m, cov2Rm g x (F m x) (F m x) (lcOf g (smoothExt x a) x v) b c d)
      = lapRmAt g x (lcOf g (smoothExt x a) x v) b c d :=
    (lapRmAt_trace hLC g x (fun i => F i x) hONx (lcOf g (smoothExt x a) x v) b c d).symm
  have hc4 : (∑ m, cov2Rm g x (F m x) (F m x) a (lcOf g (smoothExt x b) x v) c d)
      = lapRmAt g x a (lcOf g (smoothExt x b) x v) c d :=
    (lapRmAt_trace hLC g x (fun i => F i x) hONx a (lcOf g (smoothExt x b) x v) c d).symm
  have hc5 : (∑ m, cov2Rm g x (F m x) (F m x) a b (lcOf g (smoothExt x c) x v) d)
      = lapRmAt g x a b (lcOf g (smoothExt x c) x v) d :=
    (lapRmAt_trace hLC g x (fun i => F i x) hONx a b (lcOf g (smoothExt x c) x v) d).symm
  have hc6 : (∑ m, cov2Rm g x (F m x) (F m x) a b c (lcOf g (smoothExt x d) x v))
      = lapRmAt g x a b c (lcOf g (smoothExt x d) x v) :=
    (lapRmAt_trace hLC g x (fun i => F i x) hONx a b c (lcOf g (smoothExt x d) x v)).symm
  -- the `cov3RmExt` trace only sees the values of the frame fields
  have hP : (∑ m, cov3RmExt g x v (F m) (F m) (smoothExt x a) (smoothExt x b) (smoothExt x c)
        (smoothExt x d))
      = ∑ m, cov3Rm g x v (F m x) (F m x) a b c d := by
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [show cov3Rm g x v (F m x) (F m x) a b c d
        = cov3RmExt g x v (smoothExt x (F m x)) (smoothExt x (F m x)) (smoothExt x a)
            (smoothExt x b) (smoothExt x c) (smoothExt x d) from rfl]
    rw [Work.Diff.GE.Kato3.cov3RmExt_bind_fst (I := I) (M := M) hLC g x v
      (U₁ := F m) (U₂ := smoothExt x (F m x)) (V := F m) (A := smoothExt x a)
      (B := smoothExt x b) (C := smoothExt x c) (D := smoothExt x d)
      (hFs m) (smoothExt_cmdiff x (F m x)) (hFs m) (smoothExt_cmdiff x a)
      (smoothExt_cmdiff x b) (smoothExt_cmdiff x c) (smoothExt_cmdiff x d)
      (smoothExt_apply x (F m x)).symm]
    rw [Work.Diff.GE.Kato3.cov3RmExt_bind_snd (I := I) (M := M) hLC g x v
      (U := smoothExt x (F m x)) (V₁ := F m) (V₂ := smoothExt x (F m x)) (A := smoothExt x a)
      (B := smoothExt x b) (C := smoothExt x c) (D := smoothExt x d)
      (smoothExt_cmdiff x (F m x)) (hFs m) (smoothExt_cmdiff x (F m x)) (smoothExt_cmdiff x a)
      (smoothExt_cmdiff x b) (smoothExt_cmdiff x c) (smoothExt_cmdiff x d)
      (smoothExt_apply x (F m x)).symm]
  unfold covLapRmAt
  rw [hsum1, hsplit, ← hc3, ← hc4, ← hc5, ← hc6, hc12, hP]
  ring
/-! ## The Ricci identities for `∇³Rm`, via a proved source

The general Ricci identity for `Ext`-tensors exists in the workspace in two copies: the GE-area
`Work.Diff.GE.extDD_antisymm` / `extDD_antisymm_swap`, which are still unproved, and the proved
API-area copy `Work.Diff.Evol.ricci_id_aux_extDD_antisymm` (in
`Submission/Work/Diff/Evol/ricci_identity_rm.lean`).  The GE-area lemmas `cov3Rm_ricci` and
`cov3Rm_swap` are derived from the former and therefore inherit that gap; the two private
statements below are the same lemmas derived from the *proved* copy, so that the Weitzenböck
estimate is complete. -/

/-! ## The thirteen-term bound for one Ricci commutator -/

/-- The Ricci identity for `∇³Rm`: exchanging the first two differentiation slots
(`Work.Diff.GE.cov3Rm_ricci`, with a complete proof). -/
private theorem cov3Rm_ricci_clean (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (w u p a b c d : TangentSpace I x) :
    cov3Rm g x w u p a b c d - cov3Rm g x u w p a b c d
      = - (covRm g x (rmVec (lcOf g) x w u p) a b c d
          + covRm g x p (rmVec (lcOf g) x w u a) b c d
          + covRm g x p a (rmVec (lcOf g) x w u b) c d
          + covRm g x p a b (rmVec (lcOf g) x w u c) d
          + covRm g x p a b c (rmVec (lcOf g) x w u d)) := by
  obtain ⟨hcov⟩ := (hLC g).1
  have htor : (lcOf g).torsion = 0 := (hLC g).2.1
  let F : Fin 5 → (Π y : M, TangentSpace I y) :=
    ![smoothExt x p, smoothExt x a, smoothExt x b, smoothExt x c, smoothExt x d]
  have hF : ∀ i, CMDiff ∞ (T% (F i)) := by
    intro i
    fin_cases i <;>
      · simp only [F]
        simp
        exact smoothExt_cmdiff x _
  have hX : CMDiff ∞ (T% (smoothExt x w)) := smoothExt_cmdiff x w
  have hY : CMDiff ∞ (T% (smoothExt x u)) := smoothExt_cmdiff x u
  have hgen := Work.Diff.Evol.ricci_id_aux_extDD_antisymm (cov := lcOf g) hcov htor (covRmT g)
    (covRmT_smooth hLC g) (covRmT_add hLC g) (covRmT_smul hLC g)
    x (smoothExt x w) (smoothExt x u) hX hY F hF
  have h1 : extDD (lcOf g) (covRmT g) x (smoothExt x w) (smoothExt x u) F
      = cov3Rm g x w u p a b c d := by
    rw [extDD_covRmT hLC g x (smoothExt x w) (smoothExt x u) hX hY F hF]
    rw [smoothExt_apply x w]
    simp only [F]
    simp
    rfl
  have h2 : extDD (lcOf g) (covRmT g) x (smoothExt x u) (smoothExt x w) F
      = cov3Rm g x u w p a b c d := by
    rw [extDD_covRmT hLC g x (smoothExt x u) (smoothExt x w) hY hX F hF]
    rw [smoothExt_apply x u]
    simp only [F]
    simp
    rfl
  have hsumR : (∑ i : Fin 5, covRmT g (Function.update F i
        (fun y => curv (lcOf g) (smoothExt x w) (smoothExt x u) (F i) y)) x)
      = covRm g x (rmVec (lcOf g) x w u p) a b c d
        + covRm g x p (rmVec (lcOf g) x w u a) b c d
        + covRm g x p a (rmVec (lcOf g) x w u b) c d
        + covRm g x p a b (rmVec (lcOf g) x w u c) d
        + covRm g x p a b c (rmVec (lcOf g) x w u d) := by
    rw [Fin.sum_univ_five]
    simp only [covRmT_apply, Function.update_apply, ite_apply, F]
    simp
    simp only [smoothExt_apply, rmVec]
  rw [h1, h2] at hgen
  rw [hsumR] at hgen
  exact hgen

/-- The Ricci identity for `∇³Rm` exchanging the second and third slots
(`Work.Diff.GE.cov3Rm_swap`, with a complete proof). -/
private theorem cov3Rm_swap_clean (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (X Y P a b c d : TangentSpace I x) :
    cov3Rm g x X Y P a b c d - cov3Rm g x X P Y a b c d
      = - (rmP g x (curvDeriv g x X Y P a) b c d
          + rmP g x a (curvDeriv g x X Y P b) c d
          + rmP g x a b (curvDeriv g x X Y P c) d
          + rmP g x a b c (curvDeriv g x X Y P d))
        - (covRm g x X (rmVec (lcOf g) x Y P a) b c d
          + covRm g x X a (rmVec (lcOf g) x Y P b) c d
          + covRm g x X a b (rmVec (lcOf g) x Y P c) d
          + covRm g x X a b c (rmVec (lcOf g) x Y P d)) := by
  have hRicci : RicciPt (I := I) (M := M) g :=
    ricciPt_of_antisymm (I := I) (M := M) hLC g
      (fun x X Y hX hY F hF =>
        Work.Diff.Evol.ricci_id_aux_extDD_antisymm (I := I) (M := M) (lcOf g)
          ((hLC g).1.some) ((hLC g).2.1) (rmPTensor g)
          (fun F hF => rmPTensor_smooth (I := I) (M := M) hLC g hF)
          (rmPTensor_add (I := I) (M := M) hLC g)
          (rmPTensor_smul (I := I) (M := M) hLC g) x X Y hX hY F hF)
  have h1 := cov3Rm_swap_step1 (I := I) (M := M) hLC g x X Y P a b c d hRicci
  have h2 := extD_phiT_fields (I := I) (M := M) hLC g x
    (Xs := smoothExt x X) (Ys := smoothExt x Y) (Ps := smoothExt x P) (As := smoothExt x a)
    (Bs := smoothExt x b) (Cs := smoothExt x c) (Ds := smoothExt x d)
    (smoothExt_cmdiff x X) (smoothExt_cmdiff x Y) (smoothExt_cmdiff x P)
    (smoothExt_cmdiff x a) (smoothExt_cmdiff x b) (smoothExt_cmdiff x c)
    (smoothExt_cmdiff x d)
  simp only [smoothExt_apply, rmVec] at h2 ⊢
  rw [h1, h2]
  ring

private theorem mul4_p1 {A B c1 c2 c3 : ℝ} (h : A ≤ B) (h1 : 0 ≤ c1) (h2 : 0 ≤ c2)
    (h3 : 0 ≤ c3) : A * c1 * c2 * c3 ≤ B * c1 * c2 * c3 :=
  mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h h1) h2) h3

private theorem mul4_p2 {A B c1 c2 c3 : ℝ} (h : A ≤ B) (h1 : 0 ≤ c1) (h2 : 0 ≤ c2)
    (h3 : 0 ≤ c3) : c1 * A * c2 * c3 ≤ c1 * B * c2 * c3 :=
  mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h h1) h2) h3

private theorem mul4_p3 {A B c1 c2 c3 : ℝ} (h : A ≤ B) (h1 : 0 ≤ c1) (h2 : 0 ≤ c2)
    (h3 : 0 ≤ c3) : c1 * c2 * A * c3 ≤ c1 * c2 * B * c3 :=
  mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h (mul_nonneg h1 h2)) h3

private theorem mul4_p4 {A B c1 c2 c3 : ℝ} (h : A ≤ B) (h1 : 0 ≤ c1) (h2 : 0 ≤ c2)
    (h3 : 0 ≤ c3) : c1 * c2 * c3 * A ≤ c1 * c2 * c3 * B :=
  mul_le_mul_of_nonneg_left h (mul_nonneg (mul_nonneg h1 h2) h3)

private theorem mul5_p1 {A B c1 c2 c3 c4 : ℝ} (h : A ≤ B) (h1 : 0 ≤ c1) (h2 : 0 ≤ c2)
    (h3 : 0 ≤ c3) (h4 : 0 ≤ c4) : A * c1 * c2 * c3 * c4 ≤ B * c1 * c2 * c3 * c4 :=
  mul_le_mul_of_nonneg_right (mul4_p1 h h1 h2 h3) h4

/-- One summand of the Weitzenböck commutator: `Work.Diff.GE.cov3Rm_ricci` (with `w,u,p = v,e,e`)
and `Work.Diff.GE.cov3Rm_swap` (with `X,Y,P = e,v,e`) write

`∇³Rm(v,e,e,…) − ∇³Rm(e,e,v,…) = −∑_{i≤5} (Rm · ∇Rm)_i − ∑_{j≤4}((R(v,e) · ∇Rm))_j
   − ∑_{j≤4}(Rm · (∇R))_j`

with `e` a unit vector; each of the thirteen terms is a product of one curvature component with one
component of `∇Rm`, hence subject to `covRm_abs_le` and `rmP_norm_bound_smooth`, while the curvature
vectors that occur satisfy `rmVec_nrm_le` and the curvature-derivative vectors `curvDeriv_nrm_le`.
All thirteen terms are therefore bounded by `(dim+1)·|Rm||∇Rm|∏‖·‖`. -/
private theorem weitzTerm_le [I.Boundaryless] [CompactSpace M]
    (hLC : LCSmooth I M) (g : SMet I M) (x : M) (e : TangentSpace I x)
    (he : g.inner x e e = 1) (v a b c d : TangentSpace I x) :
    cov3Rm g x v e e a b c d - cov3Rm g x e e v a b c d
      ≤ 13 * ((Module.finrank ℝ E : ℝ) + 1) * Env g x v a b c d := by
  have hK : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) + 1 := by positivity
  have hK1 : (1 : ℝ) ≤ (Module.finrank ℝ E : ℝ) + 1 := by
    have h0 : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
    linarith
  have he1 : Real.sqrt (g.inner x e e) = 1 := by rw [he, Real.sqrt_one]
  have hEnv : 0 ≤ Env g x v a b c d := by
    simp only [Env]
    exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
        (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
  -- norms of the curvature vectors
  have hW1 : Real.sqrt (g.inner x (rmVec (lcOf g) x v e e) (rmVec (lcOf g) x v e e))
      ≤ ((Module.finrank ℝ E : ℝ) + 1) * Real.sqrt (rmNormSq g x) * Real.sqrt (g.inner x v v) := by
    have h := rmVec_nrm_le (I := I) (M := M) hLC g x v e e
    simp only [nrm, he1, mul_one, one_mul] at h
    exact h
  have hWa : Real.sqrt (g.inner x (rmVec (lcOf g) x v e a) (rmVec (lcOf g) x v e a))
      ≤ ((Module.finrank ℝ E : ℝ) + 1) * Real.sqrt (rmNormSq g x)
          * (Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x a a)) := by
    have h := rmVec_nrm_le (I := I) (M := M) hLC g x v e a
    simp only [nrm, he1, mul_one, one_mul] at h
    exact h
  have hWb : Real.sqrt (g.inner x (rmVec (lcOf g) x v e b) (rmVec (lcOf g) x v e b))
      ≤ ((Module.finrank ℝ E : ℝ) + 1) * Real.sqrt (rmNormSq g x)
          * (Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x b b)) := by
    have h := rmVec_nrm_le (I := I) (M := M) hLC g x v e b
    simp only [nrm, he1, mul_one, one_mul] at h
    exact h
  have hWc : Real.sqrt (g.inner x (rmVec (lcOf g) x v e c) (rmVec (lcOf g) x v e c))
      ≤ ((Module.finrank ℝ E : ℝ) + 1) * Real.sqrt (rmNormSq g x)
          * (Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x c c)) := by
    have h := rmVec_nrm_le (I := I) (M := M) hLC g x v e c
    simp only [nrm, he1, mul_one, one_mul] at h
    exact h
  have hWd : Real.sqrt (g.inner x (rmVec (lcOf g) x v e d) (rmVec (lcOf g) x v e d))
      ≤ ((Module.finrank ℝ E : ℝ) + 1) * Real.sqrt (rmNormSq g x)
          * (Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x d d)) := by
    have h := rmVec_nrm_le (I := I) (M := M) hLC g x v e d
    simp only [nrm, he1, mul_one, one_mul] at h
    exact h
  -- norms of the curvature-derivative vectors
  have hVa : Real.sqrt (g.inner x (curvDeriv g x e v e a) (curvDeriv g x e v e a))
      ≤ Real.sqrt (dRmNormSq g x) * (Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x a a)) := by
    have h := curvDeriv_nrm_le hLC g x e v e a
    simp only [nrm, he1, mul_one, one_mul] at h
    exact h
  have hVb : Real.sqrt (g.inner x (curvDeriv g x e v e b) (curvDeriv g x e v e b))
      ≤ Real.sqrt (dRmNormSq g x) * (Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x b b)) := by
    have h := curvDeriv_nrm_le hLC g x e v e b
    simp only [nrm, he1, mul_one, one_mul] at h
    exact h
  have hVc : Real.sqrt (g.inner x (curvDeriv g x e v e c) (curvDeriv g x e v e c))
      ≤ Real.sqrt (dRmNormSq g x) * (Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x c c)) := by
    have h := curvDeriv_nrm_le hLC g x e v e c
    simp only [nrm, he1, mul_one, one_mul] at h
    exact h
  have hVd : Real.sqrt (g.inner x (curvDeriv g x e v e d) (curvDeriv g x e v e d))
      ≤ Real.sqrt (dRmNormSq g x) * (Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x d d)) := by
    have h := curvDeriv_nrm_le hLC g x e v e d
    simp only [nrm, he1, mul_one, one_mul] at h
    exact h
  have hsv : ∀ u : TangentSpace I x, 0 ≤ Real.sqrt (g.inner x u u) := fun u => Real.sqrt_nonneg _
  have hSD : 0 ≤ Real.sqrt (dRmNormSq g x) := Real.sqrt_nonneg _
  have hSR : 0 ≤ Real.sqrt (rmNormSq g x) := Real.sqrt_nonneg _
  -- the thirteen terms of the commutator
  have h1 := cov3Rm_ricci_clean hLC g x v e e a b c d
  have h2 := cov3Rm_swap_clean hLC g x e v e a b c d
  have hmid : cov3Rm g x v e e a b c d - cov3Rm g x e e v a b c d
      = (cov3Rm g x v e e a b c d - cov3Rm g x e v e a b c d)
        + (cov3Rm g x e v e a b c d - cov3Rm g x e e v a b c d) := by ring
  rw [hmid, h1, h2]
  set A1 := covRm g x (rmVec (lcOf g) x v e e) a b c d with hA1def
  set A2 := covRm g x e (rmVec (lcOf g) x v e a) b c d with hA2def
  set A3 := covRm g x e a (rmVec (lcOf g) x v e b) c d with hA3def
  set A4 := covRm g x e a b (rmVec (lcOf g) x v e c) d with hA4def
  set A5 := covRm g x e a b c (rmVec (lcOf g) x v e d) with hA5def
  set B1 := rmP g x (curvDeriv g x e v e a) b c d with hB1def
  set B2 := rmP g x a (curvDeriv g x e v e b) c d with hB2def
  set B3 := rmP g x a b (curvDeriv g x e v e c) d with hB3def
  set B4 := rmP g x a b c (curvDeriv g x e v e d) with hB4def
  have hE1 : |A1| ≤ ((Module.finrank ℝ E : ℝ) + 1) * Env g x v a b c d := by
    rw [hA1def]
    refine le_trans (covRm_abs_le hLC g x (rmVec (lcOf g) x v e e) a b c d) ?_
    simp only [nrm]
    refine le_trans (mul_le_mul_of_nonneg_left
      (mul5_p1 hW1 (hsv a) (hsv b) (hsv c) (hsv d)) hSD) (le_of_eq ?_)
    simp only [Env]; ring
  have hE2 : |A2| ≤ ((Module.finrank ℝ E : ℝ) + 1) * Env g x v a b c d := by
    rw [hA2def]
    refine le_trans (covRm_abs_le hLC g x e (rmVec (lcOf g) x v e a) b c d) ?_
    simp only [nrm, he1, one_mul]
    refine le_trans (mul_le_mul_of_nonneg_left
      (mul4_p1 hWa (hsv b) (hsv c) (hsv d)) hSD) (le_of_eq ?_)
    simp only [Env]; ring
  have hE3 : |A3| ≤ ((Module.finrank ℝ E : ℝ) + 1) * Env g x v a b c d := by
    rw [hA3def]
    refine le_trans (covRm_abs_le hLC g x e a (rmVec (lcOf g) x v e b) c d) ?_
    simp only [nrm, he1, one_mul]
    refine le_trans (mul_le_mul_of_nonneg_left
      (mul4_p2 hWb (hsv a) (hsv c) (hsv d)) hSD) (le_of_eq ?_)
    simp only [Env]; ring
  have hE4 : |A4| ≤ ((Module.finrank ℝ E : ℝ) + 1) * Env g x v a b c d := by
    rw [hA4def]
    refine le_trans (covRm_abs_le hLC g x e a b (rmVec (lcOf g) x v e c) d) ?_
    simp only [nrm, he1, one_mul]
    refine le_trans (mul_le_mul_of_nonneg_left
      (mul4_p3 hWc (hsv a) (hsv b) (hsv d)) hSD) (le_of_eq ?_)
    simp only [Env]; ring
  have hE5 : |A5| ≤ ((Module.finrank ℝ E : ℝ) + 1) * Env g x v a b c d := by
    rw [hA5def]
    refine le_trans (covRm_abs_le hLC g x e a b c (rmVec (lcOf g) x v e d)) ?_
    simp only [nrm, he1, one_mul]
    refine le_trans (mul_le_mul_of_nonneg_left
      (mul4_p4 hWd (hsv a) (hsv b) (hsv c)) hSD) (le_of_eq ?_)
    simp only [Env]; ring
  have hF1 : |B1| ≤ ((Module.finrank ℝ E : ℝ) + 1) * Env g x v a b c d := by
    rw [hB1def]
    refine le_trans (rmP_norm_bound_smooth hLC g x (curvDeriv g x e v e a) b c d) ?_
    refine le_trans (mul_le_mul_of_nonneg_left
      (mul4_p1 hVa (hsv b) (hsv c) (hsv d)) hSR) ?_
    refine le_trans (le_of_eq ?_) (by simpa using mul_le_mul_of_nonneg_right hK1 hEnv)
    simp only [Env]; ring
  have hF2 : |B2| ≤ ((Module.finrank ℝ E : ℝ) + 1) * Env g x v a b c d := by
    rw [hB2def]
    refine le_trans (rmP_norm_bound_smooth hLC g x a (curvDeriv g x e v e b) c d) ?_
    refine le_trans (mul_le_mul_of_nonneg_left
      (mul4_p2 hVb (hsv a) (hsv c) (hsv d)) hSR) ?_
    refine le_trans (le_of_eq ?_) (by simpa using mul_le_mul_of_nonneg_right hK1 hEnv)
    simp only [Env]; ring
  have hF3 : |B3| ≤ ((Module.finrank ℝ E : ℝ) + 1) * Env g x v a b c d := by
    rw [hB3def]
    refine le_trans (rmP_norm_bound_smooth hLC g x a b (curvDeriv g x e v e c) d) ?_
    refine le_trans (mul_le_mul_of_nonneg_left
      (mul4_p3 hVc (hsv a) (hsv b) (hsv d)) hSR) ?_
    refine le_trans (le_of_eq ?_) (by simpa using mul_le_mul_of_nonneg_right hK1 hEnv)
    simp only [Env]; ring
  have hF4 : |B4| ≤ ((Module.finrank ℝ E : ℝ) + 1) * Env g x v a b c d := by
    rw [hB4def]
    refine le_trans (rmP_norm_bound_smooth hLC g x a b c (curvDeriv g x e v e d)) ?_
    refine le_trans (mul_le_mul_of_nonneg_left
      (mul4_p4 hVd (hsv a) (hsv b) (hsv c)) hSR) ?_
    refine le_trans (le_of_eq ?_) (by simpa using mul_le_mul_of_nonneg_right hK1 hEnv)
    simp only [Env]; ring
  -- combine the thirteen terms
  have ht1 : |A1 + A2 + A3 + A4 + A5| ≤ |A1| + |A2| + |A3| + |A4| + |A5| := by
    have s0 := abs_add_le A1 A2
    have s1 := abs_add_le (A1 + A2) A3
    have s2 := abs_add_le (A1 + A2 + A3) A4
    have s3 := abs_add_le (A1 + A2 + A3 + A4) A5
    linarith
  have ht2 : |B1 + B2 + B3 + B4| ≤ |B1| + |B2| + |B3| + |B4| := by
    have s0 := abs_add_le B1 B2
    have s1 := abs_add_le (B1 + B2) B3
    have s2 := abs_add_le (B1 + B2 + B3) B4
    linarith
  have e1 : -(A1 + A2 + A3 + A4 + A5) ≤ |A1| + |A2| + |A3| + |A4| + |A5| := by
    linarith [ht1, neg_le_abs (A1 + A2 + A3 + A4 + A5)]
  have e2 : -(B1 + B2 + B3 + B4) ≤ |B1| + |B2| + |B3| + |B4| := by
    linarith [ht2, neg_le_abs (B1 + B2 + B3 + B4)]
  have e3 : -(A2 + A3 + A4 + A5) ≤ |A2| + |A3| + |A4| + |A5| := by
    have s0 := abs_add_le A2 A3
    have s1 := abs_add_le (A2 + A3) A4
    have s2 := abs_add_le (A2 + A3 + A4) A5
    have h0 : |A2 + A3 + A4 + A5| ≤ |A2| + |A3| + |A4| + |A5| := by linarith
    linarith [h0, neg_le_abs (A2 + A3 + A4 + A5)]
  linarith [e1, e2, e3, hE1, hE2, hE3, hE4, hE5, hF1, hF2, hF3, hF4, hK, hEnv]
/-! ## The Weitzenböck inequality -/

/-- The commutator `[Δ, ∇_v]Rm` written as the trace of the differences
`∇³Rm(v,e_m,e_m,…) − ∇³Rm(e_m,e_m,v,…)`, using the trace identity for `covLapRmAt` and
`Work.Diff.GE.lapCovRmAt_trace` for `Δ(∇Rm)`. -/
theorem covLapRm_sub_lapCovRm_eq_sum
    (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (F : Fin (Module.finrank ℝ E) → (Π y : M, TangentSpace I y))
    (hFs : ∀ i, SmoothField M (F i)) (hFON : OnFrameNear g x F)
    (v a b c d : TangentSpace I x) :
    covLapRmAt g x v a b c d - lapCovRmAt g x v a b c d
      = ∑ m, (cov3Rm g x v (F m x) (F m x) a b c d
              - cov3Rm g x (F m x) (F m x) v a b c d) := by
  rw [covLapRmAt_eq_sum_cov3Rm_frame hLC g x F hFs hFON v a b c d,
    lapCovRmAt_trace hLC g x (fun i => F i x) hFON.self_of_nhds v a b c d,
    Finset.sum_sub_distrib]

/-- The Weitzenböck estimate at a point, in a frame `F` which is orthonormal near `x`:
`∇_v(ΔRm) − Δ(∇Rm) ≤ dim · 13(dim+1) |Rm| |∇Rm| ‖v‖‖a‖‖b‖‖c‖‖d‖`. -/
theorem covLapRm_sub_lapCovRm_le [I.Boundaryless] [CompactSpace M]
    (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (F : Fin (Module.finrank ℝ E) → (Π y : M, TangentSpace I y))
    (hFs : ∀ i, SmoothField M (F i)) (hFON : OnFrameNear g x F)
    (v a b c d : TangentSpace I x) :
    covLapRmAt g x v a b c d - lapCovRmAt g x v a b c d
      ≤ (Module.finrank ℝ E : ℝ) * (13 * ((Module.finrank ℝ E : ℝ) + 1)
          * Env g x v a b c d) := by
  rw [covLapRm_sub_lapCovRm_eq_sum hLC g x F hFs hFON v a b c d]
  have hONx : IsONFrame g x (fun i => F i x) := hFON.self_of_nhds
  have hone : ∀ m : Fin (Module.finrank ℝ E), g.inner x (F m x) (F m x) = 1 := by
    intro m
    have h := hONx m m
    simpa using h
  calc ∑ m, (cov3Rm g x v (F m x) (F m x) a b c d
          - cov3Rm g x (F m x) (F m x) v a b c d)
      ≤ ∑ _m : Fin (Module.finrank ℝ E),
          13 * ((Module.finrank ℝ E : ℝ) + 1) * Env g x v a b c d :=
        Finset.sum_le_sum (fun m _ => weitzTerm_le hLC g x (F m x) (hone m) v a b c d)
    _ = (Module.finrank ℝ E : ℝ) * (13 * ((Module.finrank ℝ E : ℝ) + 1)
          * Env g x v a b c d) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
theorem covLapRm_le_lapCovRm_metric
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : Submission.Diff.LCSmooth I M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : Submission.Diff.SMet I M) (x : M)
        (v a b c d : TangentSpace I x),
      Work.Diff.GE.covLapRmAt g x v a b c d ≤ Work.Diff.GE.lapCovRmAt g x v a b c d
        + C * Real.sqrt (Submission.Diff.rmNormSq g x)
            * Real.sqrt (Submission.Diff.dRmNormSq g x)
            * (Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x a a)
              * Real.sqrt (g.inner x b b) * Real.sqrt (g.inner x c c)
              * Real.sqrt (g.inner x d d)) := by
  refine ⟨(Module.finrank ℝ E : ℝ) * (13 * ((Module.finrank ℝ E : ℝ) + 1)), by positivity, ?_⟩
  intro g x v a b c d
  obtain ⟨F, hFs, hFON, _⟩ := onFrameONfield (I := I) (M := M) hLC g x
  have h := covLapRm_sub_lapCovRm_le (I := I) (M := M) hLC g x F hFs hFON v a b c d
  have hEnv : Env g x v a b c d = Real.sqrt (rmNormSq g x) * Real.sqrt (dRmNormSq g x)
      * (Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x a a) * Real.sqrt (g.inner x b b)
         * Real.sqrt (g.inner x c c) * Real.sqrt (g.inner x d d)) := rfl
  rw [hEnv] at h
  have hkey : covLapRmAt g x v a b c d - lapCovRmAt g x v a b c d
      ≤ ((Module.finrank ℝ E : ℝ) * (13 * ((Module.finrank ℝ E : ℝ) + 1)))
        * (Real.sqrt (rmNormSq g x) * Real.sqrt (dRmNormSq g x)
          * (Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x a a) * Real.sqrt (g.inner x b b)
             * Real.sqrt (g.inner x c c) * Real.sqrt (g.inner x d d))) := by
    refine le_trans h (le_of_eq ?_)
    ring
  linarith [hkey]

end Work.Diff.GE.WeitzB
