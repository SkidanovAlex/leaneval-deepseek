import ChallengeDeps
import Mathlib
import Submission.Work.Diff.GE.rmP_norm_bound
import Submission.Work.Diff.GE.curvDerivNormSq_le
import Submission.Work.Diff.GE.CurvDerivDefs
import Submission.Work.Diff.GE.WeitzB.covLapRm_le_lapCovRm_metric

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The summand bound for the Weitzenböck commutator `∇_v(ΔRm) − Δ(∇_v Rm)`

`Work.Diff.GE.covLapRmAt g x v a b c d` is the covariant derivative `∇_v(ΔRm)` of the rough
Laplacian of the curvature and `Work.Diff.GE.lapCovRmAt g x v a b c d` is `Δ(∇Rm)` on the same five
vectors.  The Ricci identities write their difference, at a point and in a unit frame vector `e`, as
a sum of thirteen terms: five of the shape `(∇Rm)(R(v,e)e, a, b, c, d)`, … , four of the shape
`Rm((∇_e R)(v,e)a, b, c, d)`, … , and four further terms of the shape `(∇Rm)(e, R(v,e)a, b, c, d)`.

This file proves the pointwise bound for that explicit sum: every one of the thirteen summands is
bounded by the envelope `|Rm| · |∇Rm| · ‖v‖‖a‖‖b‖‖c‖‖d‖`, so the sum is bounded by thirteen times
it.  The individual estimates used are

* `covRm_abs_le_sqrt` : `|(∇_X Rm)(a,b,c,d)| ≤ √|∇Rm|² ‖X‖‖a‖‖b‖‖c‖‖d‖`,
* `rmP_norm_bound_smooth` : `|Rm(u,b,c,d)| ≤ √|Rm|² ‖u‖‖b‖‖c‖‖d‖` (the lower-level
  `Work.Diff.GE.rmP_norm_bound` is stated under the *analytic* manifold hypothesis and is not
  applicable at the smooth level `IsManifold I ∞ M` of the frozen interfaces),
* `sqrt_rmVec_le` : `‖R(u,w)z‖ ≤ √|Rm|² ‖u‖‖w‖‖z‖` — the sharp curvature-vector bound, proved here
  from `rmVec_sq_le_sharp'`, which is Cauchy–Schwarz for the four-fold contraction applied with the
  test vector `X = R(u,w)z` itself, so that no dimension factor is lost,
* `sqrt_curvDeriv_le` : `‖(∇_X R)(Y,P)Z‖ ≤ √|∇Rm|² ‖X‖‖Y‖‖P‖‖Z‖`.

The dimension-free constant `13` is what makes this bound usable in the Kato-type arguments, where a
factor `dim M` would spoil an estimate with a non-absolute constant.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.GE

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]

/-! ## Elementary arithmetic -/

/-- `√(p q r s) = √p √q √r √s` for nonnegative factors. -/
private theorem sqrt_mul4' {p q r s : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    Real.sqrt (p * q * r * s) = Real.sqrt p * Real.sqrt q * Real.sqrt r * Real.sqrt s := by
  rw [Real.sqrt_mul (mul_nonneg (mul_nonneg hp hq) hr), Real.sqrt_mul (mul_nonneg hp hq),
    Real.sqrt_mul hp]

/-- `√(p q r s t) = √p √q √r √s √t` for nonnegative factors. -/
private theorem sqrt_mul5' {p q r s t : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (ht : 0 ≤ t) :
    Real.sqrt (p * q * r * s * t)
      = Real.sqrt p * Real.sqrt q * Real.sqrt r * Real.sqrt s * Real.sqrt t := by
  rw [Real.sqrt_mul (mul_nonneg (mul_nonneg (mul_nonneg hp hq) hr) hs),
    Real.sqrt_mul (mul_nonneg (mul_nonneg hp hq) hr), Real.sqrt_mul (mul_nonneg hp hq),
    Real.sqrt_mul hp]

/-- The metric pairing of a vector with itself is nonnegative. -/
private theorem inner_self_nonneg' (g : SMet I M) (x : M) (v : TangentSpace I x) :
    0 ≤ g.inner x v v := by
  rcases eq_or_ne v 0 with h | h
  · rw [h]; simp
  · exact le_of_lt (g.pos x v h)

/-- Multiply an inequality on the first factor of a product of four reals. -/
private theorem mul4_le_of_le {A B c1 c2 c3 : ℝ} (h : A ≤ B) (h1 : 0 ≤ c1) (h2 : 0 ≤ c2)
    (h3 : 0 ≤ c3) : A * c1 * c2 * c3 ≤ B * c1 * c2 * c3 :=
  mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h h1) h2) h3

/-- Multiply an inequality on the first factor of a product of five reals. -/
private theorem mul5_le_of_le {A B c1 c2 c3 c4 : ℝ} (h : A ≤ B) (h1 : 0 ≤ c1) (h2 : 0 ≤ c2)
    (h3 : 0 ≤ c3) (h4 : 0 ≤ c4) : A * c1 * c2 * c3 * c4 ≤ B * c1 * c2 * c3 * c4 :=
  mul_le_mul_of_nonneg_right (mul4_le_of_le h h1 h2 h3) h4

/-! ## The sharp curvature-vector bound -/

/-- **The sharp curvature-vector bound** `‖R(u,w)z‖² ≤ |Rm|² ‖u‖²‖w‖²‖z‖²`.

In the orthonormal frame `e = onFrame`, the `l`-th coordinate of `R(u,w)z` is the four-fold
contraction `∑_{ijk} αᵢβⱼγₖ (Rm)_{ijl k}` of the rank-one coefficient tensor with the curvature
array.  Instead of Cauchy–Schwarz in the three summed indices we apply the four-fold
Cauchy–Schwarz `Work.Diff.GE.sum4_coeff_sq_le` to an arbitrary test vector `X` and then put
`X := R(u,w)z` and divide by `‖R(u,w)z‖²`; this keeps the constant dimension-free. -/
theorem rmVec_sq_le_sharp' (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (u w z : TangentSpace I x) :
    g.inner x (rmVec (lcOf g) x u w z) (rmVec (lcOf g) x u w z)
      ≤ rmNormSq g x * (g.inner x u u) * (g.inner x w w) * (g.inner x z z) := by
  classical
  by_cases hn : 0 < Module.finrank ℝ E
  · have hR : 0 ≤ rmNormSq g x := Gest.rmNormSq_nonneg g x
    -- the key estimate for an arbitrary test vector
    have hkey : ∀ X : TangentSpace I x,
        (rmP g x u w X z) ^ 2
          ≤ (rmNormSq g x * (g.inner x u u) * (g.inner x w w) * (g.inner x z z))
            * (g.inner x X X) := by
      intro X
      have hexp := rmP_expansion hLC g x hn u w X z
      have hcs := sum4_coeff_sq_le (A := rmC g x)
        (a := fun i => g.inner x (onFrame g x i) u)
        (b := fun j => g.inner x (onFrame g x j) w)
        (c := fun k => g.inner x (onFrame g x k) X)
        (d := fun l => g.inner x (onFrame g x l) z)
      have hSU := onFrame_parseval_sq g x hn u
      have hSW := onFrame_parseval_sq g x hn w
      have hSX := onFrame_parseval_sq g x hn X
      have hSZ := onFrame_parseval_sq g x hn z
      have hstep : (rmP g x u w X z) ^ 2
          ≤ rmNormSq g x * ((g.inner x u u) * ((g.inner x w w)
              * ((g.inner x X X) * (g.inner x z z)))) := by
        rw [hexp]
        refine le_trans hcs ?_
        rw [hSU, hSW, hSX, hSZ]
        exact le_rfl
      calc (rmP g x u w X z) ^ 2
          ≤ rmNormSq g x * ((g.inner x u u) * ((g.inner x w w)
              * ((g.inner x X X) * (g.inner x z z)))) := hstep
        _ = (rmNormSq g x * (g.inner x u u) * (g.inner x w w) * (g.inner x z z))
              * (g.inner x X X) := by ring
    set W := rmVec (lcOf g) x u w z with hWdef
    have h1 : (g.inner x W W) ^ 2
        ≤ (rmNormSq g x * (g.inner x u u) * (g.inner x w w) * (g.inner x z z))
          * (g.inner x W W) := by
      have h := hkey W
      have hWv : rmP g x u w W z = g.inner x W W := by
        rw [hWdef]
        rfl
      rwa [hWv] at h
    have hWnn : 0 ≤ g.inner x W W := by
      rw [← onFrame_parseval_sq g x hn W]
      exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have hCnn : 0 ≤ rmNormSq g x * (g.inner x u u) * (g.inner x w w) * (g.inner x z z) :=
      mul_nonneg (mul_nonneg (mul_nonneg hR (inner_self_nonneg' g x u)) (inner_self_nonneg' g x w))
        (inner_self_nonneg' g x z)
    rcases eq_or_lt_of_le hWnn with h0 | hpos
    · rw [← h0]
      exact hCnn
    · have h2 : g.inner x W W * g.inner x W W
          ≤ (rmNormSq g x * (g.inner x u u) * (g.inner x w w) * (g.inner x z z))
            * (g.inner x W W) := by
        calc g.inner x W W * g.inner x W W = (g.inner x W W) ^ 2 := by ring
          _ ≤ _ := h1
      exact (mul_le_mul_iff_of_pos_right hpos).mp h2
  · -- degenerate case: `finrank ℝ E = 0`, all tangent vectors vanish
    have h0 : Module.finrank ℝ E = 0 := Nat.eq_zero_of_not_pos hn
    have hsub : Subsingleton E := Module.finrank_zero_iff.mp h0
    haveI : Subsingleton (TangentSpace I x) := hsub
    have hu : u = 0 := Subsingleton.elim u 0
    have hw : w = 0 := Subsingleton.elim w 0
    have hz : z = 0 := Subsingleton.elim z 0
    rw [hu, hw, hz]
    have hv0 : rmVec (lcOf g) x 0 0 0 = 0 := Subsingleton.elim _ _
    rw [hv0]
    simp

/-- The `√`-form of the sharp curvature-vector bound: `‖R(u,w)z‖ ≤ √|Rm|² ‖u‖‖w‖‖z‖`. -/
private theorem sqrt_rmVec_le (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (u w z : TangentSpace I x) :
    Real.sqrt (g.inner x (rmVec (lcOf g) x u w z) (rmVec (lcOf g) x u w z))
      ≤ Real.sqrt (rmNormSq g x) * (Real.sqrt (g.inner x u u) * Real.sqrt (g.inner x w w)
          * Real.sqrt (g.inner x z z)) := by
  refine le_trans (Real.sqrt_le_sqrt (rmVec_sq_le_sharp' hLC g x u w z)) (le_of_eq ?_)
  rw [sqrt_mul4' (Gest.rmNormSq_nonneg g x) (inner_self_nonneg' g x u) (inner_self_nonneg' g x w)
    (inner_self_nonneg' g x z)]
  ring

/-! ## The pointwise bounds in `√`-form -/

/-- **The `(0,5)`-tensor bound for `∇Rm`**: `|(∇_v Rm)(a,b,c,d)| ≤ √|∇Rm|² ‖v‖‖a‖‖b‖‖c‖‖d‖`.
This is `Work.Diff.GE.WeitzB.covRm_abs_le` with the private `nrm`-notation unfolded. -/
private theorem covRm_abs_le_sqrt (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (v a b c d : TangentSpace I x) :
    |covRm g x v a b c d|
      ≤ Real.sqrt (dRmNormSq g x) * (Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x a a)
          * Real.sqrt (g.inner x b b) * Real.sqrt (g.inner x c c) * Real.sqrt (g.inner x d d)) :=
  WeitzB.covRm_abs_le hLC g x v a b c d

/-- **The curvature-derivative-vector bound**: `‖(∇_X R)(Y,P)Z‖ ≤ √|∇Rm|² ‖X‖‖Y‖‖P‖‖Z‖`.
This is `Work.Diff.GE.WeitzB.curvDeriv_nrm_le` with the private `nrm`-notation unfolded. -/
private theorem sqrt_curvDeriv_le (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (X Y P Z : TangentSpace I x) :
    Real.sqrt (g.inner x (curvDeriv g x X Y P Z) (curvDeriv g x X Y P Z))
      ≤ Real.sqrt (dRmNormSq g x) * (Real.sqrt (g.inner x X X) * Real.sqrt (g.inner x Y Y)
          * Real.sqrt (g.inner x P P) * Real.sqrt (g.inner x Z Z)) :=
  WeitzB.curvDeriv_nrm_le hLC g x X Y P Z

theorem covLapRm_sub_lapCovRm_summand_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ENat) M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : Submission.Diff.LCSmooth I M)
    (g : Submission.Diff.SMet I M) (x : M) (v a b c d : TangentSpace I x)
    (m : Fin (Module.finrank ℝ E)) :
    |(Submission.Diff.covRm g x
              (Submission.Diff.rmVec (Submission.Diff.lcOf g) x v (Submission.Diff.onFrame g x m)
                (Submission.Diff.onFrame g x m)) a b c d
            + Submission.Diff.covRm g x (Submission.Diff.onFrame g x m)
              (Submission.Diff.rmVec (Submission.Diff.lcOf g) x v (Submission.Diff.onFrame g x m) a)
              b c d
            + Submission.Diff.covRm g x (Submission.Diff.onFrame g x m) a
              (Submission.Diff.rmVec (Submission.Diff.lcOf g) x v (Submission.Diff.onFrame g x m) b)
              c d
            + Submission.Diff.covRm g x (Submission.Diff.onFrame g x m) a b
              (Submission.Diff.rmVec (Submission.Diff.lcOf g) x v (Submission.Diff.onFrame g x m) c)
              d
            + Submission.Diff.covRm g x (Submission.Diff.onFrame g x m) a b c
              (Submission.Diff.rmVec (Submission.Diff.lcOf g) x v (Submission.Diff.onFrame g x m) d))
        + (Submission.Diff.rmP g x
              (Work.Diff.GE.curvDeriv g x (Submission.Diff.onFrame g x m) v
                (Submission.Diff.onFrame g x m) a) b c d
            + Submission.Diff.rmP g x a
              (Work.Diff.GE.curvDeriv g x (Submission.Diff.onFrame g x m) v
                (Submission.Diff.onFrame g x m) b) c d
            + Submission.Diff.rmP g x a b
              (Work.Diff.GE.curvDeriv g x (Submission.Diff.onFrame g x m) v
                (Submission.Diff.onFrame g x m) c) d
            + Submission.Diff.rmP g x a b c
              (Work.Diff.GE.curvDeriv g x (Submission.Diff.onFrame g x m) v
                (Submission.Diff.onFrame g x m) d))
        + (Submission.Diff.covRm g x (Submission.Diff.onFrame g x m)
              (Submission.Diff.rmVec (Submission.Diff.lcOf g) x v (Submission.Diff.onFrame g x m) a)
              b c d
            + Submission.Diff.covRm g x (Submission.Diff.onFrame g x m) a
              (Submission.Diff.rmVec (Submission.Diff.lcOf g) x v (Submission.Diff.onFrame g x m) b)
              c d
            + Submission.Diff.covRm g x (Submission.Diff.onFrame g x m) a b
              (Submission.Diff.rmVec (Submission.Diff.lcOf g) x v (Submission.Diff.onFrame g x m) c)
              d
            + Submission.Diff.covRm g x (Submission.Diff.onFrame g x m) a b c
              (Submission.Diff.rmVec (Submission.Diff.lcOf g) x v (Submission.Diff.onFrame g x m) d))|
      ≤ 13 * (Real.sqrt (Submission.Diff.rmNormSq g x) * Real.sqrt (Submission.Diff.dRmNormSq g x)
        * (Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x a a)
          * Real.sqrt (g.inner x b b) * Real.sqrt (g.inner x c c)
          * Real.sqrt (g.inner x d d))) := by
  -- the frame vector `e = onFrame g x m` is a unit vector
  set e := Submission.Diff.onFrame g x m with hedef
  have he1 : g.inner x e e = 1 := by
    rw [hedef]
    simpa using isONFrame_onFrame g x m m
  have hse : Real.sqrt (g.inner x e e) = 1 := by rw [he1, Real.sqrt_one]
  -- the envelope
  set Env := Real.sqrt (rmNormSq g x) * Real.sqrt (dRmNormSq g x)
      * (Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x a a) * Real.sqrt (g.inner x b b)
         * Real.sqrt (g.inner x c c) * Real.sqrt (g.inner x d d)) with hEnvdef
  -- the thirteen summands
  set A1 := covRm g x (rmVec (lcOf g) x v e e) a b c d with hA1def
  set A2 := covRm g x e (rmVec (lcOf g) x v e a) b c d with hA2def
  set A3 := covRm g x e a (rmVec (lcOf g) x v e b) c d with hA3def
  set A4 := covRm g x e a b (rmVec (lcOf g) x v e c) d with hA4def
  set A5 := covRm g x e a b c (rmVec (lcOf g) x v e d) with hA5def
  set B1 := rmP g x (curvDeriv g x e v e a) b c d with hB1def
  set B2 := rmP g x a (curvDeriv g x e v e b) c d with hB2def
  set B3 := rmP g x a b (curvDeriv g x e v e c) d with hB3def
  set B4 := rmP g x a b c (curvDeriv g x e v e d) with hB4def
  -- norms of the curvature vectors `R(v,e)z`
  have hW1 : Real.sqrt (g.inner x (rmVec (lcOf g) x v e e) (rmVec (lcOf g) x v e e))
      ≤ Real.sqrt (rmNormSq g x) * Real.sqrt (g.inner x v v) := by
    have h := sqrt_rmVec_le hLC g x v e e
    simpa only [hse, mul_one, one_mul] using h
  have hWa : Real.sqrt (g.inner x (rmVec (lcOf g) x v e a) (rmVec (lcOf g) x v e a))
      ≤ Real.sqrt (rmNormSq g x) * (Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x a a)) := by
    have h := sqrt_rmVec_le hLC g x v e a
    simpa only [hse, mul_one, one_mul] using h
  have hWb : Real.sqrt (g.inner x (rmVec (lcOf g) x v e b) (rmVec (lcOf g) x v e b))
      ≤ Real.sqrt (rmNormSq g x) * (Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x b b)) := by
    have h := sqrt_rmVec_le hLC g x v e b
    simpa only [hse, mul_one, one_mul] using h
  have hWc : Real.sqrt (g.inner x (rmVec (lcOf g) x v e c) (rmVec (lcOf g) x v e c))
      ≤ Real.sqrt (rmNormSq g x) * (Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x c c)) := by
    have h := sqrt_rmVec_le hLC g x v e c
    simpa only [hse, mul_one, one_mul] using h
  have hWd : Real.sqrt (g.inner x (rmVec (lcOf g) x v e d) (rmVec (lcOf g) x v e d))
      ≤ Real.sqrt (rmNormSq g x) * (Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x d d)) := by
    have h := sqrt_rmVec_le hLC g x v e d
    simpa only [hse, mul_one, one_mul] using h
  -- norms of the curvature-derivative vectors `(∇_e R)(v,e)z`
  have hVa : Real.sqrt (g.inner x (curvDeriv g x e v e a) (curvDeriv g x e v e a))
      ≤ Real.sqrt (dRmNormSq g x) * (Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x a a)) := by
    have h := sqrt_curvDeriv_le hLC g x e v e a
    simpa only [hse, mul_one, one_mul] using h
  have hVb : Real.sqrt (g.inner x (curvDeriv g x e v e b) (curvDeriv g x e v e b))
      ≤ Real.sqrt (dRmNormSq g x) * (Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x b b)) := by
    have h := sqrt_curvDeriv_le hLC g x e v e b
    simpa only [hse, mul_one, one_mul] using h
  have hVc : Real.sqrt (g.inner x (curvDeriv g x e v e c) (curvDeriv g x e v e c))
      ≤ Real.sqrt (dRmNormSq g x) * (Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x c c)) := by
    have h := sqrt_curvDeriv_le hLC g x e v e c
    simpa only [hse, mul_one, one_mul] using h
  have hVd : Real.sqrt (g.inner x (curvDeriv g x e v e d) (curvDeriv g x e v e d))
      ≤ Real.sqrt (dRmNormSq g x) * (Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x d d)) := by
    have h := sqrt_curvDeriv_le hLC g x e v e d
    simpa only [hse, mul_one, one_mul] using h
  -- the thirteen summands, each bounded by the envelope
  have hA1 : |A1| ≤ Env := by
    rw [hA1def, hEnvdef]
    have hmain : |covRm g x (rmVec (lcOf g) x v e e) a b c d|
        ≤ Real.sqrt (dRmNormSq g x)
          * (Real.sqrt (g.inner x (rmVec (lcOf g) x v e e) (rmVec (lcOf g) x v e e))
             * Real.sqrt (g.inner x a a) * Real.sqrt (g.inner x b b) * Real.sqrt (g.inner x c c)
             * Real.sqrt (g.inner x d d)) :=
      covRm_abs_le_sqrt hLC g x (rmVec (lcOf g) x v e e) a b c d
    have hstep : Real.sqrt (g.inner x (rmVec (lcOf g) x v e e) (rmVec (lcOf g) x v e e))
          * Real.sqrt (g.inner x a a) * Real.sqrt (g.inner x b b) * Real.sqrt (g.inner x c c)
          * Real.sqrt (g.inner x d d)
        ≤ (Real.sqrt (rmNormSq g x) * Real.sqrt (g.inner x v v))
          * Real.sqrt (g.inner x a a) * Real.sqrt (g.inner x b b) * Real.sqrt (g.inner x c c)
          * Real.sqrt (g.inner x d d) :=
      mul5_le_of_le hW1 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
        (Real.sqrt_nonneg _)
    exact le_trans hmain (le_trans (mul_le_mul_of_nonneg_left hstep (Real.sqrt_nonneg _))
      (le_of_eq (by ring)))
  have hA2 : |A2| ≤ Env := by
    rw [hA2def, hEnvdef]
    have hmain : |covRm g x e (rmVec (lcOf g) x v e a) b c d|
        ≤ Real.sqrt (dRmNormSq g x)
          * (Real.sqrt (g.inner x (rmVec (lcOf g) x v e a) (rmVec (lcOf g) x v e a))
             * Real.sqrt (g.inner x b b) * Real.sqrt (g.inner x c c)
             * Real.sqrt (g.inner x d d)) := by
      have h := covRm_abs_le_sqrt hLC g x e (rmVec (lcOf g) x v e a) b c d
      refine le_trans h (le_of_eq ?_)
      rw [hse]
      ring
    have hstep : Real.sqrt (g.inner x (rmVec (lcOf g) x v e a) (rmVec (lcOf g) x v e a))
          * Real.sqrt (g.inner x b b) * Real.sqrt (g.inner x c c) * Real.sqrt (g.inner x d d)
        ≤ (Real.sqrt (rmNormSq g x) * (Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x a a)))
          * Real.sqrt (g.inner x b b) * Real.sqrt (g.inner x c c) * Real.sqrt (g.inner x d d) :=
      mul4_le_of_le hWa (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    exact le_trans hmain (le_trans (mul_le_mul_of_nonneg_left hstep (Real.sqrt_nonneg _))
      (le_of_eq (by ring)))
  have hA3 : |A3| ≤ Env := by
    rw [hA3def, hEnvdef]
    have hmain : |covRm g x e a (rmVec (lcOf g) x v e b) c d|
        ≤ Real.sqrt (dRmNormSq g x)
          * (Real.sqrt (g.inner x (rmVec (lcOf g) x v e b) (rmVec (lcOf g) x v e b))
             * Real.sqrt (g.inner x a a) * Real.sqrt (g.inner x c c)
             * Real.sqrt (g.inner x d d)) := by
      have h := covRm_abs_le_sqrt hLC g x e a (rmVec (lcOf g) x v e b) c d
      refine le_trans h (le_of_eq ?_)
      rw [hse]
      ring
    have hstep : Real.sqrt (g.inner x (rmVec (lcOf g) x v e b) (rmVec (lcOf g) x v e b))
          * Real.sqrt (g.inner x a a) * Real.sqrt (g.inner x c c) * Real.sqrt (g.inner x d d)
        ≤ (Real.sqrt (rmNormSq g x) * (Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x b b)))
          * Real.sqrt (g.inner x a a) * Real.sqrt (g.inner x c c) * Real.sqrt (g.inner x d d) :=
      mul4_le_of_le hWb (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    exact le_trans hmain (le_trans (mul_le_mul_of_nonneg_left hstep (Real.sqrt_nonneg _))
      (le_of_eq (by ring)))
  have hA4 : |A4| ≤ Env := by
    rw [hA4def, hEnvdef]
    have hmain : |covRm g x e a b (rmVec (lcOf g) x v e c) d|
        ≤ Real.sqrt (dRmNormSq g x)
          * (Real.sqrt (g.inner x (rmVec (lcOf g) x v e c) (rmVec (lcOf g) x v e c))
             * Real.sqrt (g.inner x a a) * Real.sqrt (g.inner x b b)
             * Real.sqrt (g.inner x d d)) := by
      have h := covRm_abs_le_sqrt hLC g x e a b (rmVec (lcOf g) x v e c) d
      refine le_trans h (le_of_eq ?_)
      rw [hse]
      ring
    have hstep : Real.sqrt (g.inner x (rmVec (lcOf g) x v e c) (rmVec (lcOf g) x v e c))
          * Real.sqrt (g.inner x a a) * Real.sqrt (g.inner x b b) * Real.sqrt (g.inner x d d)
        ≤ (Real.sqrt (rmNormSq g x) * (Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x c c)))
          * Real.sqrt (g.inner x a a) * Real.sqrt (g.inner x b b) * Real.sqrt (g.inner x d d) :=
      mul4_le_of_le hWc (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    exact le_trans hmain (le_trans (mul_le_mul_of_nonneg_left hstep (Real.sqrt_nonneg _))
      (le_of_eq (by ring)))
  have hA5 : |A5| ≤ Env := by
    rw [hA5def, hEnvdef]
    have hmain : |covRm g x e a b c (rmVec (lcOf g) x v e d)|
        ≤ Real.sqrt (dRmNormSq g x)
          * (Real.sqrt (g.inner x (rmVec (lcOf g) x v e d) (rmVec (lcOf g) x v e d))
             * Real.sqrt (g.inner x a a) * Real.sqrt (g.inner x b b)
             * Real.sqrt (g.inner x c c)) := by
      have h := covRm_abs_le_sqrt hLC g x e a b c (rmVec (lcOf g) x v e d)
      refine le_trans h (le_of_eq ?_)
      rw [hse]
      ring
    have hstep : Real.sqrt (g.inner x (rmVec (lcOf g) x v e d) (rmVec (lcOf g) x v e d))
          * Real.sqrt (g.inner x a a) * Real.sqrt (g.inner x b b) * Real.sqrt (g.inner x c c)
        ≤ (Real.sqrt (rmNormSq g x) * (Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x d d)))
          * Real.sqrt (g.inner x a a) * Real.sqrt (g.inner x b b) * Real.sqrt (g.inner x c c) :=
      mul4_le_of_le hWd (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    exact le_trans hmain (le_trans (mul_le_mul_of_nonneg_left hstep (Real.sqrt_nonneg _))
      (le_of_eq (by ring)))
  have hB1 : |B1| ≤ Env := by
    rw [hB1def, hEnvdef]
    have hmain : |rmP g x (curvDeriv g x e v e a) b c d|
        ≤ Real.sqrt (rmNormSq g x)
          * (Real.sqrt (g.inner x (curvDeriv g x e v e a) (curvDeriv g x e v e a))
             * Real.sqrt (g.inner x b b) * Real.sqrt (g.inner x c c)
             * Real.sqrt (g.inner x d d)) :=
      rmP_norm_bound_smooth hLC g x (curvDeriv g x e v e a) b c d
    have hstep : Real.sqrt (g.inner x (curvDeriv g x e v e a) (curvDeriv g x e v e a))
          * Real.sqrt (g.inner x b b) * Real.sqrt (g.inner x c c) * Real.sqrt (g.inner x d d)
        ≤ (Real.sqrt (dRmNormSq g x) * (Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x a a)))
          * Real.sqrt (g.inner x b b) * Real.sqrt (g.inner x c c) * Real.sqrt (g.inner x d d) :=
      mul4_le_of_le hVa (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    exact le_trans hmain (le_trans (mul_le_mul_of_nonneg_left hstep (Real.sqrt_nonneg _))
      (le_of_eq (by ring)))
  have hB2 : |B2| ≤ Env := by
    rw [hB2def, hEnvdef]
    have hmain : |rmP g x a (curvDeriv g x e v e b) c d|
        ≤ Real.sqrt (rmNormSq g x)
          * (Real.sqrt (g.inner x (curvDeriv g x e v e b) (curvDeriv g x e v e b))
             * Real.sqrt (g.inner x a a) * Real.sqrt (g.inner x c c)
             * Real.sqrt (g.inner x d d)) := by
      have h := rmP_norm_bound_smooth hLC g x a (curvDeriv g x e v e b) c d
      refine le_trans h (le_of_eq ?_)
      ring
    have hstep : Real.sqrt (g.inner x (curvDeriv g x e v e b) (curvDeriv g x e v e b))
          * Real.sqrt (g.inner x a a) * Real.sqrt (g.inner x c c) * Real.sqrt (g.inner x d d)
        ≤ (Real.sqrt (dRmNormSq g x) * (Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x b b)))
          * Real.sqrt (g.inner x a a) * Real.sqrt (g.inner x c c) * Real.sqrt (g.inner x d d) :=
      mul4_le_of_le hVb (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    exact le_trans hmain (le_trans (mul_le_mul_of_nonneg_left hstep (Real.sqrt_nonneg _))
      (le_of_eq (by ring)))
  have hB3 : |B3| ≤ Env := by
    rw [hB3def, hEnvdef]
    have hmain : |rmP g x a b (curvDeriv g x e v e c) d|
        ≤ Real.sqrt (rmNormSq g x)
          * (Real.sqrt (g.inner x (curvDeriv g x e v e c) (curvDeriv g x e v e c))
             * Real.sqrt (g.inner x a a) * Real.sqrt (g.inner x b b)
             * Real.sqrt (g.inner x d d)) := by
      have h := rmP_norm_bound_smooth hLC g x a b (curvDeriv g x e v e c) d
      refine le_trans h (le_of_eq ?_)
      ring
    have hstep : Real.sqrt (g.inner x (curvDeriv g x e v e c) (curvDeriv g x e v e c))
          * Real.sqrt (g.inner x a a) * Real.sqrt (g.inner x b b) * Real.sqrt (g.inner x d d)
        ≤ (Real.sqrt (dRmNormSq g x) * (Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x c c)))
          * Real.sqrt (g.inner x a a) * Real.sqrt (g.inner x b b) * Real.sqrt (g.inner x d d) :=
      mul4_le_of_le hVc (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    exact le_trans hmain (le_trans (mul_le_mul_of_nonneg_left hstep (Real.sqrt_nonneg _))
      (le_of_eq (by ring)))
  have hB4 : |B4| ≤ Env := by
    rw [hB4def, hEnvdef]
    have hmain : |rmP g x a b c (curvDeriv g x e v e d)|
        ≤ Real.sqrt (rmNormSq g x)
          * (Real.sqrt (g.inner x (curvDeriv g x e v e d) (curvDeriv g x e v e d))
             * Real.sqrt (g.inner x a a) * Real.sqrt (g.inner x b b)
             * Real.sqrt (g.inner x c c)) := by
      have h := rmP_norm_bound_smooth hLC g x a b c (curvDeriv g x e v e d)
      refine le_trans h (le_of_eq ?_)
      ring
    have hstep : Real.sqrt (g.inner x (curvDeriv g x e v e d) (curvDeriv g x e v e d))
          * Real.sqrt (g.inner x a a) * Real.sqrt (g.inner x b b) * Real.sqrt (g.inner x c c)
        ≤ (Real.sqrt (dRmNormSq g x) * (Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x d d)))
          * Real.sqrt (g.inner x a a) * Real.sqrt (g.inner x b b) * Real.sqrt (g.inner x c c) :=
      mul4_le_of_le hVd (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    exact le_trans hmain (le_trans (mul_le_mul_of_nonneg_left hstep (Real.sqrt_nonneg _))
      (le_of_eq (by ring)))
  -- the triangle inequality for the three groups
  have hS1 : |A1 + A2 + A3 + A4 + A5| ≤ 5 * Env := by
    have t1 := abs_add_le A1 A2
    have t2 := abs_add_le (A1 + A2) A3
    have t3 := abs_add_le (A1 + A2 + A3) A4
    have t4 := abs_add_le (A1 + A2 + A3 + A4) A5
    linarith [hA1, hA2, hA3, hA4, hA5]
  have hS2 : |B1 + B2 + B3 + B4| ≤ 4 * Env := by
    have t1 := abs_add_le B1 B2
    have t2 := abs_add_le (B1 + B2) B3
    have t3 := abs_add_le (B1 + B2 + B3) B4
    linarith [hB1, hB2, hB3, hB4]
  have hS3 : |A2 + A3 + A4 + A5| ≤ 4 * Env := by
    have t1 := abs_add_le A2 A3
    have t2 := abs_add_le (A2 + A3) A4
    have t3 := abs_add_le (A2 + A3 + A4) A5
    linarith [hA2, hA3, hA4, hA5]
  have htot : |(A1 + A2 + A3 + A4 + A5) + (B1 + B2 + B3 + B4) + (A2 + A3 + A4 + A5)|
      ≤ 13 * Env := by
    have u1 := abs_add_le (A1 + A2 + A3 + A4 + A5) (B1 + B2 + B3 + B4)
    have u2 := abs_add_le ((A1 + A2 + A3 + A4 + A5) + (B1 + B2 + B3 + B4))
      (A2 + A3 + A4 + A5)
    linarith [hS1, hS2, hS3]
  exact htot

end Work.Diff.GE
