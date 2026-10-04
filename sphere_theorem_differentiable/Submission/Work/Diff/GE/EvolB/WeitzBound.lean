import Mathlib
import Submission.Work.Diff.GE.EvolB.WeitzDiff
import Submission.Work.Diff.GE.EvolB.NrmBounds
import Submission.Work.Diff.GE.EvolB.rmPbound_B
import Submission.Work.Diff.GE.EvolB.rmVec_normSq_le_B

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Weitzenböck estimate (`EvolB`)

`Work.Diff.GE.EvolB.covLapRm_le_lapCovRm_B`: for a smooth metric `g` on `M`,

`covLapRmAt g x v a b c d ≤ lapCovRmAt g x v a b c d + C |Rm| |∇Rm| |v||a||b||c||d|`

with a constant `C` depending only on `finrank ℝ E`.  It is obtained from the exact identity
`Work.Diff.GE.EvolB.covLapRm_sub_lapCovRm_eq_B` by bounding each of the `13` curvature-contraction
terms of its summand: the `∇Rm`-terms with `EvolB.covRm_norm_le_B`, the `Rm`-terms with
`EvolB.rmP_norm_le_B`, and the two varying vectors with `EvolB.rmVec_nrm_le_B'` and
`EvolB.curvDeriv_nrm_le_B`.  Every frame vector has metric norm `1`, and the sum over the frame has
`finrank ℝ E` terms, both of which are absorbed in the constant.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 3200000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.GE.EvolB

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M]

/-- The frame vectors have metric norm `1`. -/
theorem onFrame_nrm_eq_one (g : SMet I M) (x : M) (m : Fin (Module.finrank ℝ E)) :
    nrm g x (Submission.Diff.onFrame g x m) = 1 := by
  rw [nrm_eq_sqrt, isONFrame_onFrame g x m m]
  simp

/-- The curvature-vector bound in square-root form. -/
theorem rmVec_nrm_le_B' [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : LCSmooth I M) (g : SMet I M) (x : M) (X Y Z : TangentSpace I x) :
    nrm g x (rmVec (lcOf g) x X Y Z)
      ≤ Real.sqrt (Module.finrank ℝ E : ℝ) * Real.sqrt (rmNormSq g x) * nrm g x X * nrm g x Y
          * nrm g x Z := by
  have h := rmVec_normSq_le_B (I := I) (M := M) hLC g x X Y Z
  have hrm : (0 : ℝ) ≤ rmNormSq g x := by
    rw [rmNormSq, Submission.Diff.Alg.frobSq]
    positivity
  have hsq : nrm g x (rmVec (lcOf g) x X Y Z) ^ 2
      ≤ (Real.sqrt (Module.finrank ℝ E : ℝ) * Real.sqrt (rmNormSq g x) * nrm g x X * nrm g x Y
          * nrm g x Z) ^ 2 := by
    rw [nrm_sq,
      show (Real.sqrt (Module.finrank ℝ E : ℝ) * Real.sqrt (rmNormSq g x) * nrm g x X
            * nrm g x Y * nrm g x Z) ^ 2
          = (Real.sqrt (Module.finrank ℝ E : ℝ)) ^ 2 * (Real.sqrt (rmNormSq g x)) ^ 2
            * (nrm g x X) ^ 2 * (nrm g x Y) ^ 2 * (nrm g x Z) ^ 2 from by ring,
      Real.sq_sqrt (Nat.cast_nonneg _), Real.sq_sqrt hrm, nrm_sq, nrm_sq, nrm_sq]
    linarith [h]
  exact le_of_sq_le_sq hsq (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (nrm_nonneg g x X)) (nrm_nonneg g x Y))
    (nrm_nonneg g x Z))



/-- Multiply an inequality by a product of three nonnegative factors on the right. -/
theorem mul_le_mul_right3 {A B C1 C2 C3 : ℝ} (h : A ≤ B)
    (h1 : 0 ≤ C1) (h2 : 0 ≤ C2) (h3 : 0 ≤ C3) :
    A * C1 * C2 * C3 ≤ B * C1 * C2 * C3 := by
  rw [show A * C1 * C2 * C3 = A * (C1 * C2 * C3) from by ring,
    show B * C1 * C2 * C3 = B * (C1 * C2 * C3) from by ring]
  exact mul_le_mul_of_nonneg_right h (mul_nonneg (mul_nonneg h1 h2) h3)

/-- Multiply an inequality by a product of four nonnegative factors on the right (left-associated
shape, which is how the products of metric norms below are written). -/
theorem mul_le_mul_right4 {A B C1 C2 C3 C4 : ℝ} (h : A ≤ B)
    (h1 : 0 ≤ C1) (h2 : 0 ≤ C2) (h3 : 0 ≤ C3) (h4 : 0 ≤ C4) :
    A * C1 * C2 * C3 * C4 ≤ B * C1 * C2 * C3 * C4 := by
  rw [show A * C1 * C2 * C3 * C4 = A * (C1 * C2 * C3 * C4) from by ring,
    show B * C1 * C2 * C3 * C4 = B * (C1 * C2 * C3 * C4) from by ring]
  exact mul_le_mul_of_nonneg_right h (mul_nonneg (mul_nonneg (mul_nonneg h1 h2) h3) h4)

/-- **The Weitzenböck estimate.**  There is a constant `C ≥ 0` (depending only on the dimension)
with `covLapRmAt g x v a b c d ≤ lapCovRmAt g x v a b c d + C |Rm| |∇Rm| |v||a||b||c||d|` for
every smooth metric `g`, every `x` and all tangent vectors `v, a, b, c, d`. -/
theorem covLapRm_le_lapCovRm_B [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : Submission.Diff.LCSmooth I M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : Submission.Diff.SMet I M) (x : M)
        (v a b c d : TangentSpace I x),
      Work.Diff.GE.covLapRmAt g x v a b c d ≤ Work.Diff.GE.lapCovRmAt g x v a b c d
        + C * Real.sqrt (Submission.Diff.rmNormSq g x)
            * Real.sqrt (Submission.Diff.dRmNormSq g x)
            * (Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x a a)
              * Real.sqrt (g.inner x b b) * Real.sqrt (g.inner x c c)
              * Real.sqrt (g.inner x d d)) := by
  refine ⟨(Module.finrank ℝ E : ℝ) * (9 * Real.sqrt (Module.finrank ℝ E : ℝ) + 4),
    by positivity, ?_⟩
  intro g x v a b c d
  set R : ℝ := Real.sqrt (rmNormSq g x) with hRdef
  set D : ℝ := Real.sqrt (dRmNormSq g x) with hDdef
  have hR : 0 ≤ R := by rw [hRdef]; exact Real.sqrt_nonneg _
  have hD : 0 ≤ D := by rw [hDdef]; exact Real.sqrt_nonneg _
  set K : ℝ := 9 * Real.sqrt (Module.finrank ℝ E : ℝ) + 4 with hKdef
  have hprod : Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x a a)
      * Real.sqrt (g.inner x b b) * Real.sqrt (g.inner x c c) * Real.sqrt (g.inner x d d)
      = nrm g x v * nrm g x a * nrm g x b * nrm g x c * nrm g x d := by
    simp only [nrm_eq_sqrt]
  rw [hprod, hRdef, hDdef]
  have hid := covLapRm_sub_lapCovRm_eq_B (I := I) (M := M) hLC g x v a b c d
  -- ### the bound for a single summand
  have hterm : ∀ m : Fin (Module.finrank ℝ E),
      (- (covRm g x (rmVec (lcOf g) x v (onFrame g x m) (onFrame g x m)) a b c d
            + covRm g x (onFrame g x m)
                (rmVec (lcOf g) x v (onFrame g x m) a) b c d
            + covRm g x (onFrame g x m) a
                (rmVec (lcOf g) x v (onFrame g x m) b) c d
            + covRm g x (onFrame g x m) a b
                (rmVec (lcOf g) x v (onFrame g x m) c) d
            + covRm g x (onFrame g x m) a b c
                (rmVec (lcOf g) x v (onFrame g x m) d))
          - (rmP g x (curvDeriv g x (onFrame g x m) v (onFrame g x m) a) b c d
            + rmP g x a (curvDeriv g x (onFrame g x m) v (onFrame g x m) b) c d
            + rmP g x a b (curvDeriv g x (onFrame g x m) v (onFrame g x m) c) d
            + rmP g x a b c (curvDeriv g x (onFrame g x m) v (onFrame g x m) d))
          - (covRm g x (onFrame g x m)
                (rmVec (lcOf g) x v (onFrame g x m) a) b c d
            + covRm g x (onFrame g x m) a
                (rmVec (lcOf g) x v (onFrame g x m) b) c d
            + covRm g x (onFrame g x m) a b
                (rmVec (lcOf g) x v (onFrame g x m) c) d
            + covRm g x (onFrame g x m) a b c
                (rmVec (lcOf g) x v (onFrame g x m) d)))
        ≤ K * R * D * nrm g x v * nrm g x a * nrm g x b * nrm g x c * nrm g x d := by
    intro m
    have hnu : nrm g x (onFrame g x m) = 1 := onFrame_nrm_eq_one g x m
    -- the generic curvature bounds
    have hCov : ∀ p1 p2 p3 p4 p5 : TangentSpace I x,
        |covRm g x p1 p2 p3 p4 p5| ≤ D * nrm g x p1 * nrm g x p2 * nrm g x p3 * nrm g x p4
          * nrm g x p5 := by
      intro p1 p2 p3 p4 p5
      have h := covRm_norm_le_B (I := I) (M := M) hLC g x p1 p2 p3 p4 p5
      rw [← hDdef] at h
      exact h
    have hRmP : ∀ p1 p2 p3 p4 : TangentSpace I x,
        |rmP g x p1 p2 p3 p4| ≤ R * nrm g x p1 * nrm g x p2 * nrm g x p3 * nrm g x p4 := by
      intro p1 p2 p3 p4
      have h := rmP_norm_le_B (I := I) (M := M) hLC g x p1 p2 p3 p4
      rw [← hRdef] at h
      exact h
    -- the norms of the varying vectors
    have hW : ∀ z : TangentSpace I x,
        nrm g x (rmVec (lcOf g) x v (onFrame g x m) z)
          ≤ Real.sqrt (Module.finrank ℝ E : ℝ) * R * nrm g x v * nrm g x z := by
      intro z
      have h := rmVec_nrm_le_B' (I := I) (M := M) hLC g x v (onFrame g x m) z
      rw [hnu, mul_one, ← hRdef] at h
      exact h
    have hC : ∀ z : TangentSpace I x,
        nrm g x (curvDeriv g x (onFrame g x m) v (onFrame g x m) z)
          ≤ D * nrm g x v * nrm g x z := by
      intro z
      have h := curvDeriv_nrm_le_B (I := I) (M := M) hLC g x (onFrame g x m) v
        (onFrame g x m) z
      rw [hnu, mul_one, ← hDdef] at h
      simpa only [mul_one] using h
    set P : ℝ := R * D * nrm g x v * nrm g x a * nrm g x b * nrm g x c * nrm g x d with hPdef
    have hP0 : 0 ≤ P := by
      rw [hPdef]
      exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hR hD)
        (nrm_nonneg g x v)) (nrm_nonneg g x a)) (nrm_nonneg g x b)) (nrm_nonneg g x c))
        (nrm_nonneg g x d)
    have hSP : (0 : ℝ) ≤ Real.sqrt (Module.finrank ℝ E : ℝ) * P :=
      mul_nonneg (Real.sqrt_nonneg _) hP0
    -- ### the five `covRm` terms and the four `rmP` terms, each bounded by `c * P`
    have eT : |covRm g x (rmVec (lcOf g) x v (onFrame g x m) (onFrame g x m)) a b c d|
        ≤ Real.sqrt (Module.finrank ℝ E : ℝ) * P := by
      refine le_trans (hCov _ a b c d) ?_
      have h2 := hW (onFrame g x m)
      rw [hnu, mul_one] at h2
      calc D * nrm g x (rmVec (lcOf g) x v (onFrame g x m) (onFrame g x m))
            * nrm g x a * nrm g x b * nrm g x c * nrm g x d
          ≤ D * (Real.sqrt (Module.finrank ℝ E : ℝ) * R * nrm g x v) * nrm g x a * nrm g x b
              * nrm g x c * nrm g x d :=
            mul_le_mul_right4 (mul_le_mul_of_nonneg_left h2 hD) (nrm_nonneg g x a)
              (nrm_nonneg g x b) (nrm_nonneg g x c) (nrm_nonneg g x d)
        _ = Real.sqrt (Module.finrank ℝ E : ℝ) * P := by rw [hPdef]; ring
    have e1 : |covRm g x (onFrame g x m) (rmVec (lcOf g) x v (onFrame g x m) a) b c d|
        ≤ Real.sqrt (Module.finrank ℝ E : ℝ) * P := by
      refine le_trans (hCov _ _ b c d) ?_
      rw [hnu, mul_one]
      have h2 := hW a
      calc D * nrm g x (rmVec (lcOf g) x v (onFrame g x m) a) * nrm g x b * nrm g x c
            * nrm g x d
          ≤ D * (Real.sqrt (Module.finrank ℝ E : ℝ) * R * nrm g x v * nrm g x a) * nrm g x b
              * nrm g x c * nrm g x d :=
            mul_le_mul_right3 (mul_le_mul_of_nonneg_left h2 hD) (nrm_nonneg g x b)
              (nrm_nonneg g x c) (nrm_nonneg g x d)
        _ = Real.sqrt (Module.finrank ℝ E : ℝ) * P := by rw [hPdef]; ring
    have e2 : |covRm g x (onFrame g x m) a (rmVec (lcOf g) x v (onFrame g x m) b) c d|
        ≤ Real.sqrt (Module.finrank ℝ E : ℝ) * P := by
      refine le_trans (hCov _ a _ c d) ?_
      rw [hnu, mul_one]
      have h2 := hW b
      calc D * nrm g x a * nrm g x (rmVec (lcOf g) x v (onFrame g x m) b) * nrm g x c
            * nrm g x d
          ≤ D * nrm g x a * (Real.sqrt (Module.finrank ℝ E : ℝ) * R * nrm g x v * nrm g x b)
              * nrm g x c * nrm g x d :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left h2 (mul_nonneg hD (nrm_nonneg g x a)))
              (nrm_nonneg g x c)) (nrm_nonneg g x d)
        _ = Real.sqrt (Module.finrank ℝ E : ℝ) * P := by rw [hPdef]; ring
    have e3 : |covRm g x (onFrame g x m) a b (rmVec (lcOf g) x v (onFrame g x m) c) d|
        ≤ Real.sqrt (Module.finrank ℝ E : ℝ) * P := by
      refine le_trans (hCov _ a b _ d) ?_
      rw [hnu, mul_one]
      have h2 := hW c
      calc D * nrm g x a * nrm g x b * nrm g x (rmVec (lcOf g) x v (onFrame g x m) c)
            * nrm g x d
          ≤ D * nrm g x a * nrm g x b
              * (Real.sqrt (Module.finrank ℝ E : ℝ) * R * nrm g x v * nrm g x c) * nrm g x d :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2
              (mul_nonneg (mul_nonneg hD (nrm_nonneg g x a)) (nrm_nonneg g x b)))
              (nrm_nonneg g x d)
        _ = Real.sqrt (Module.finrank ℝ E : ℝ) * P := by rw [hPdef]; ring
    have e4 : |covRm g x (onFrame g x m) a b c (rmVec (lcOf g) x v (onFrame g x m) d)|
        ≤ Real.sqrt (Module.finrank ℝ E : ℝ) * P := by
      refine le_trans (hCov _ a b c _) ?_
      rw [hnu, mul_one]
      have h2 := hW d
      calc D * nrm g x a * nrm g x b * nrm g x c
            * nrm g x (rmVec (lcOf g) x v (onFrame g x m) d)
          ≤ D * nrm g x a * nrm g x b * nrm g x c
              * (Real.sqrt (Module.finrank ℝ E : ℝ) * R * nrm g x v * nrm g x d) :=
            mul_le_mul_of_nonneg_left h2
              (mul_nonneg (mul_nonneg (mul_nonneg hD (nrm_nonneg g x a)) (nrm_nonneg g x b))
                (nrm_nonneg g x c))
        _ = Real.sqrt (Module.finrank ℝ E : ℝ) * P := by rw [hPdef]; ring
    have f0 : |rmP g x (curvDeriv g x (onFrame g x m) v (onFrame g x m) a) b c d| ≤ P := by
      refine le_trans (hRmP _ b c d) ?_
      have h2 := hC a
      calc R * nrm g x (curvDeriv g x (onFrame g x m) v (onFrame g x m) a) * nrm g x b
            * nrm g x c * nrm g x d
          ≤ R * (D * nrm g x v * nrm g x a) * nrm g x b * nrm g x c * nrm g x d :=
            mul_le_mul_right3 (mul_le_mul_of_nonneg_left h2 hR) (nrm_nonneg g x b)
              (nrm_nonneg g x c) (nrm_nonneg g x d)
        _ = P := by rw [hPdef]; ring
    have f1 : |rmP g x a (curvDeriv g x (onFrame g x m) v (onFrame g x m) b) c d| ≤ P := by
      refine le_trans (hRmP a _ c d) ?_
      have h2 := hC b
      calc R * nrm g x a * nrm g x (curvDeriv g x (onFrame g x m) v (onFrame g x m) b)
            * nrm g x c * nrm g x d
          ≤ R * nrm g x a * (D * nrm g x v * nrm g x b) * nrm g x c * nrm g x d :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left h2 (mul_nonneg hR (nrm_nonneg g x a)))
              (nrm_nonneg g x c)) (nrm_nonneg g x d)
        _ = P := by rw [hPdef]; ring
    have f2 : |rmP g x a b (curvDeriv g x (onFrame g x m) v (onFrame g x m) c) d| ≤ P := by
      refine le_trans (hRmP a b _ d) ?_
      have h2 := hC c
      calc R * nrm g x a * nrm g x b
            * nrm g x (curvDeriv g x (onFrame g x m) v (onFrame g x m) c) * nrm g x d
          ≤ R * nrm g x a * nrm g x b * (D * nrm g x v * nrm g x c) * nrm g x d :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2
              (mul_nonneg (mul_nonneg hR (nrm_nonneg g x a)) (nrm_nonneg g x b)))
              (nrm_nonneg g x d)
        _ = P := by rw [hPdef]; ring
    have f3 : |rmP g x a b c (curvDeriv g x (onFrame g x m) v (onFrame g x m) d)| ≤ P := by
      refine le_trans (hRmP a b c _) ?_
      have h2 := hC d
      calc R * nrm g x a * nrm g x b * nrm g x c
            * nrm g x (curvDeriv g x (onFrame g x m) v (onFrame g x m) d)
          ≤ R * nrm g x a * nrm g x b * nrm g x c * (D * nrm g x v * nrm g x d) :=
            mul_le_mul_of_nonneg_left h2
              (mul_nonneg (mul_nonneg (mul_nonneg hR (nrm_nonneg g x a)) (nrm_nonneg g x b))
                (nrm_nonneg g x c))
        _ = P := by rw [hPdef]; ring
    -- ### assembly: bound the three groups
    have hg1 : |covRm g x (rmVec (lcOf g) x v (onFrame g x m) (onFrame g x m)) a b c d
          + covRm g x (onFrame g x m) (rmVec (lcOf g) x v (onFrame g x m) a) b c d
          + covRm g x (onFrame g x m) a (rmVec (lcOf g) x v (onFrame g x m) b) c d
          + covRm g x (onFrame g x m) a b (rmVec (lcOf g) x v (onFrame g x m) c) d
          + covRm g x (onFrame g x m) a b c (rmVec (lcOf g) x v (onFrame g x m) d)|
        ≤ Real.sqrt (Module.finrank ℝ E : ℝ) * P + 4 * (Real.sqrt (Module.finrank ℝ E : ℝ) * P) := by
      have hsplit : covRm g x (rmVec (lcOf g) x v (onFrame g x m) (onFrame g x m)) a b c d
            + covRm g x (onFrame g x m) (rmVec (lcOf g) x v (onFrame g x m) a) b c d
            + covRm g x (onFrame g x m) a (rmVec (lcOf g) x v (onFrame g x m) b) c d
            + covRm g x (onFrame g x m) a b (rmVec (lcOf g) x v (onFrame g x m) c) d
            + covRm g x (onFrame g x m) a b c (rmVec (lcOf g) x v (onFrame g x m) d)
          = covRm g x (rmVec (lcOf g) x v (onFrame g x m) (onFrame g x m)) a b c d
            + (covRm g x (onFrame g x m) (rmVec (lcOf g) x v (onFrame g x m) a) b c d
              + (covRm g x (onFrame g x m) a (rmVec (lcOf g) x v (onFrame g x m) b) c d
                + (covRm g x (onFrame g x m) a b (rmVec (lcOf g) x v (onFrame g x m) c) d
                  + covRm g x (onFrame g x m) a b c (rmVec (lcOf g) x v (onFrame g x m) d)))) := by
        ring
      rw [hsplit]
      have habs := abs_add_le (covRm g x (rmVec (lcOf g) x v (onFrame g x m) (onFrame g x m))
          a b c d)
        (covRm g x (onFrame g x m) (rmVec (lcOf g) x v (onFrame g x m) a) b c d
          + (covRm g x (onFrame g x m) a (rmVec (lcOf g) x v (onFrame g x m) b) c d
            + (covRm g x (onFrame g x m) a b (rmVec (lcOf g) x v (onFrame g x m) c) d
              + covRm g x (onFrame g x m) a b c (rmVec (lcOf g) x v (onFrame g x m) d))))
      have habs2 := abs_add_le (covRm g x (onFrame g x m)
          (rmVec (lcOf g) x v (onFrame g x m) a) b c d)
        (covRm g x (onFrame g x m) a (rmVec (lcOf g) x v (onFrame g x m) b) c d
          + (covRm g x (onFrame g x m) a b (rmVec (lcOf g) x v (onFrame g x m) c) d
            + covRm g x (onFrame g x m) a b c (rmVec (lcOf g) x v (onFrame g x m) d)))
      have habs3 := abs_add_le (covRm g x (onFrame g x m) a
          (rmVec (lcOf g) x v (onFrame g x m) b) c d)
        (covRm g x (onFrame g x m) a b (rmVec (lcOf g) x v (onFrame g x m) c) d
          + covRm g x (onFrame g x m) a b c (rmVec (lcOf g) x v (onFrame g x m) d))
      have habs4 := abs_add_le (covRm g x (onFrame g x m) a b
          (rmVec (lcOf g) x v (onFrame g x m) c) d)
        (covRm g x (onFrame g x m) a b c (rmVec (lcOf g) x v (onFrame g x m) d))
      linarith [habs, habs2, habs3, habs4, eT, e1, e2, e3, e4, hSP]
    have hg2 : |rmP g x (curvDeriv g x (onFrame g x m) v (onFrame g x m) a) b c d
          + rmP g x a (curvDeriv g x (onFrame g x m) v (onFrame g x m) b) c d
          + rmP g x a b (curvDeriv g x (onFrame g x m) v (onFrame g x m) c) d
          + rmP g x a b c (curvDeriv g x (onFrame g x m) v (onFrame g x m) d)|
        ≤ P + P + P + P := by
      have habs1 := abs_add_le (rmP g x (curvDeriv g x (onFrame g x m) v (onFrame g x m) a)
          b c d + rmP g x a (curvDeriv g x (onFrame g x m) v (onFrame g x m) b) c d
          + rmP g x a b (curvDeriv g x (onFrame g x m) v (onFrame g x m) c) d)
        (rmP g x a b c (curvDeriv g x (onFrame g x m) v (onFrame g x m) d))
      have habs2 := abs_add_le (rmP g x (curvDeriv g x (onFrame g x m) v (onFrame g x m) a)
          b c d + rmP g x a (curvDeriv g x (onFrame g x m) v (onFrame g x m) b) c d)
        (rmP g x a b (curvDeriv g x (onFrame g x m) v (onFrame g x m) c) d)
      have habs3 := abs_add_le (rmP g x (curvDeriv g x (onFrame g x m) v (onFrame g x m) a)
          b c d) (rmP g x a (curvDeriv g x (onFrame g x m) v (onFrame g x m) b) c d)
      linarith [habs1, habs2, habs3, f0, f1, f2, f3]
    have hg3 : |covRm g x (onFrame g x m) (rmVec (lcOf g) x v (onFrame g x m) a) b c d
          + covRm g x (onFrame g x m) a (rmVec (lcOf g) x v (onFrame g x m) b) c d
          + covRm g x (onFrame g x m) a b (rmVec (lcOf g) x v (onFrame g x m) c) d
          + covRm g x (onFrame g x m) a b c (rmVec (lcOf g) x v (onFrame g x m) d)|
        ≤ 4 * (Real.sqrt (Module.finrank ℝ E : ℝ) * P) := by
      have hsplit : covRm g x (onFrame g x m) (rmVec (lcOf g) x v (onFrame g x m) a) b c d
            + covRm g x (onFrame g x m) a (rmVec (lcOf g) x v (onFrame g x m) b) c d
            + covRm g x (onFrame g x m) a b (rmVec (lcOf g) x v (onFrame g x m) c) d
            + covRm g x (onFrame g x m) a b c (rmVec (lcOf g) x v (onFrame g x m) d)
          = covRm g x (onFrame g x m) (rmVec (lcOf g) x v (onFrame g x m) a) b c d
            + (covRm g x (onFrame g x m) a (rmVec (lcOf g) x v (onFrame g x m) b) c d
              + (covRm g x (onFrame g x m) a b (rmVec (lcOf g) x v (onFrame g x m) c) d
                + covRm g x (onFrame g x m) a b c (rmVec (lcOf g) x v (onFrame g x m) d))) := by
        ring
      rw [hsplit]
      have habs := abs_add_le (covRm g x (onFrame g x m)
          (rmVec (lcOf g) x v (onFrame g x m) a) b c d)
        (covRm g x (onFrame g x m) a (rmVec (lcOf g) x v (onFrame g x m) b) c d
          + (covRm g x (onFrame g x m) a b (rmVec (lcOf g) x v (onFrame g x m) c) d
            + covRm g x (onFrame g x m) a b c (rmVec (lcOf g) x v (onFrame g x m) d)))
      have habs2 := abs_add_le (covRm g x (onFrame g x m) a
          (rmVec (lcOf g) x v (onFrame g x m) b) c d)
        (covRm g x (onFrame g x m) a b (rmVec (lcOf g) x v (onFrame g x m) c) d
          + covRm g x (onFrame g x m) a b c (rmVec (lcOf g) x v (onFrame g x m) d))
      have habs3 := abs_add_le (covRm g x (onFrame g x m) a b
          (rmVec (lcOf g) x v (onFrame g x m) c) d)
        (covRm g x (onFrame g x m) a b c (rmVec (lcOf g) x v (onFrame g x m) d))
      linarith [habs, habs2, habs3, e1, e2, e3, e4, hSP]
    -- ### the summand bound
    have hsp1 : - (covRm g x (rmVec (lcOf g) x v (onFrame g x m) (onFrame g x m)) a b c d
            + covRm g x (onFrame g x m) (rmVec (lcOf g) x v (onFrame g x m) a) b c d
            + covRm g x (onFrame g x m) a (rmVec (lcOf g) x v (onFrame g x m) b) c d
            + covRm g x (onFrame g x m) a b (rmVec (lcOf g) x v (onFrame g x m) c) d
            + covRm g x (onFrame g x m) a b c (rmVec (lcOf g) x v (onFrame g x m) d))
          ≤ Real.sqrt (Module.finrank ℝ E : ℝ) * P + 4 * (Real.sqrt (Module.finrank ℝ E : ℝ) * P) :=
      le_trans (neg_le_abs _) hg1
    have hsp2 : - (rmP g x (curvDeriv g x (onFrame g x m) v (onFrame g x m) a) b c d
            + rmP g x a (curvDeriv g x (onFrame g x m) v (onFrame g x m) b) c d
            + rmP g x a b (curvDeriv g x (onFrame g x m) v (onFrame g x m) c) d
            + rmP g x a b c (curvDeriv g x (onFrame g x m) v (onFrame g x m) d))
          ≤ P + P + P + P := le_trans (neg_le_abs _) hg2
    have hsp3 : - (covRm g x (onFrame g x m) (rmVec (lcOf g) x v (onFrame g x m) a) b c d
            + covRm g x (onFrame g x m) a (rmVec (lcOf g) x v (onFrame g x m) b) c d
            + covRm g x (onFrame g x m) a b (rmVec (lcOf g) x v (onFrame g x m) c) d
            + covRm g x (onFrame g x m) a b c (rmVec (lcOf g) x v (onFrame g x m) d))
          ≤ 4 * (Real.sqrt (Module.finrank ℝ E : ℝ) * P) := le_trans (neg_le_abs _) hg3
    have hK : Real.sqrt (Module.finrank ℝ E : ℝ) * P + 4 * (Real.sqrt (Module.finrank ℝ E : ℝ) * P)
        + (P + P + P + P) + 4 * (Real.sqrt (Module.finrank ℝ E : ℝ) * P) ≤ K * P := by
      rw [hKdef]
      nlinarith [hSP, hP0]
    calc
      - (covRm g x (rmVec (lcOf g) x v (onFrame g x m) (onFrame g x m)) a b c d
            + covRm g x (onFrame g x m) (rmVec (lcOf g) x v (onFrame g x m) a) b c d
            + covRm g x (onFrame g x m) a (rmVec (lcOf g) x v (onFrame g x m) b) c d
            + covRm g x (onFrame g x m) a b (rmVec (lcOf g) x v (onFrame g x m) c) d
            + covRm g x (onFrame g x m) a b c (rmVec (lcOf g) x v (onFrame g x m) d))
          - (rmP g x (curvDeriv g x (onFrame g x m) v (onFrame g x m) a) b c d
            + rmP g x a (curvDeriv g x (onFrame g x m) v (onFrame g x m) b) c d
            + rmP g x a b (curvDeriv g x (onFrame g x m) v (onFrame g x m) c) d
            + rmP g x a b c (curvDeriv g x (onFrame g x m) v (onFrame g x m) d))
          - (covRm g x (onFrame g x m) (rmVec (lcOf g) x v (onFrame g x m) a) b c d
            + covRm g x (onFrame g x m) a (rmVec (lcOf g) x v (onFrame g x m) b) c d
            + covRm g x (onFrame g x m) a b (rmVec (lcOf g) x v (onFrame g x m) c) d
            + covRm g x (onFrame g x m) a b c (rmVec (lcOf g) x v (onFrame g x m) d))
        ≤ (Real.sqrt (Module.finrank ℝ E : ℝ) * P + 4 * (Real.sqrt (Module.finrank ℝ E : ℝ) * P))
          + (P + P + P + P) + 4 * (Real.sqrt (Module.finrank ℝ E : ℝ) * P) := by
          linarith [hsp1, hsp2, hsp3]
      _ ≤ K * P := hK
      _ = K * R * D * nrm g x v * nrm g x a * nrm g x b * nrm g x c * nrm g x d := by
          rw [hPdef]; ring
  -- ### summing over the frame
  have hsum : Work.Diff.GE.covLapRmAt g x v a b c d - Work.Diff.GE.lapCovRmAt g x v a b c d
      ≤ ∑ _m : Fin (Module.finrank ℝ E),
          K * R * D * nrm g x v * nrm g x a * nrm g x b * nrm g x c * nrm g x d := by
    rw [hid]
    exact Finset.sum_le_sum fun m _ => hterm m
  have hsumval : (∑ _m : Fin (Module.finrank ℝ E),
        K * R * D * nrm g x v * nrm g x a * nrm g x b * nrm g x c * nrm g x d)
      = (Module.finrank ℝ E : ℝ)
        * (K * R * D * nrm g x v * nrm g x a * nrm g x b * nrm g x c * nrm g x d) := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hsumval] at hsum
  calc Work.Diff.GE.covLapRmAt g x v a b c d
      ≤ Work.Diff.GE.lapCovRmAt g x v a b c d
        + (Module.finrank ℝ E : ℝ)
          * (K * R * D * nrm g x v * nrm g x a * nrm g x b * nrm g x c * nrm g x d) := by
        linarith [hsum]
    _ = Work.Diff.GE.lapCovRmAt g x v a b c d
        + ((Module.finrank ℝ E : ℝ) * (9 * Real.sqrt (Module.finrank ℝ E : ℝ) + 4))
          * R * D * (nrm g x v * nrm g x a * nrm g x b * nrm g x c * nrm g x d) := by
        rw [hKdef]; ring

end Work.Diff.GE.EvolB
