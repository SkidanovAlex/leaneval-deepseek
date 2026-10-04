import Mathlib
import Submission.Work.Diff.GE.EvolB.Lib
import Submission.Work.Diff.GE.rmP_norm_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.GE.EvolB

/-- **The squared bound for a component of the curvature form.**

For the frozen pointwise curvature form `rmP g x u b c d = ⟪R(u,b)d, c⟫` one has
`(rmP g x u b c d)² ≤ |Rm|² ⟨u,u⟩⟨b,b⟩⟨c,c⟩⟨d,d⟩`, where `|Rm| = √(rmNormSq g x)` and `⟨·,·⟩` is
`g.inner x · ·`.

This is the *squared* form of `Work.Diff.GE.rmP_norm_bound_smooth` (whose statement carries square
roots); it is proved directly by the same route (frame expansion of `rmP` in the `g`-orthonormal
frame `onFrame g x` + the four-fold Cauchy–Schwarz inequality `Work.Diff.GE.sum4_coeff_sq_le`
+ Parseval `Work.Diff.GE.onFrame_parseval_sq`), so that no square-root side conditions are needed
downstream. -/
theorem rmP_sq_le_B
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (x : M)
    (u b c d : TangentSpace I x) :
    (Submission.Diff.rmP g x u b c d) ^ 2
      ≤ Submission.Diff.rmNormSq g x
        * (g.inner x u u * (g.inner x b b * (g.inner x c c * g.inner x d d))) := by
  by_cases hn : 0 < Module.finrank ℝ E
  · have hkey := Work.Diff.GE.rmP_expansion hLC g x hn u b c d
    have hSU := Work.Diff.GE.onFrame_parseval_sq g x hn u
    have hSB := Work.Diff.GE.onFrame_parseval_sq g x hn b
    have hSC := Work.Diff.GE.onFrame_parseval_sq g x hn c
    have hSD := Work.Diff.GE.onFrame_parseval_sq g x hn d
    have hcs := Work.Diff.GE.sum4_coeff_sq_le (A := Submission.Diff.rmC g x)
      (a := fun i => g.inner x (Submission.Diff.onFrame g x i) u)
      (b := fun j => g.inner x (Submission.Diff.onFrame g x j) b)
      (c := fun k => g.inner x (Submission.Diff.onFrame g x k) c)
      (d := fun l => g.inner x (Submission.Diff.onFrame g x l) d)
    rw [hkey]
    refine le_trans hcs ?_
    rw [hSU, hSB, hSC, hSD]
    exact le_rfl
  · have h0 : Module.finrank ℝ E = 0 := Nat.eq_zero_of_not_pos hn
    have hzero : ∀ v : E, v = 0 := finrank_zero_iff_forall_zero.mp h0
    have hu : u = 0 := hzero u
    have hb : b = 0 := hzero b
    have hc : c = 0 := hzero c
    have hd : d = 0 := hzero d
    rw [hu, hb, hc, hd]
    simp [Submission.Diff.rmP]

/-- **The (crude) norm bound for the curvature vector.**  `|R(X,Y)Z|² ≤ n |Rm|² |X|²|Y|²|Z|²`,
where `n = finrank ℝ E` and `|·|` are the metric norms `√(g.inner x · ·)`.

`Work.Diff.GE.rmVec (lcOf g) x X Y Z` is the vector `R(X,Y)Z`, and
`Submission.Diff.rmP g x X Y W Z = g(R(X,Y)Z, W)`.

Route (one Parseval identity and one component bound).  Let `e := Submission.Diff.onFrame g x`,
which is `g`-orthonormal at `x` (`Submission.Work.Diff.GE.isONFrame_onFrame`).  By
`Submission.Work.Diff.GE.onFrame_parseval_sq` (PROVED, in
`Submission/Work/Diff/GE/rmP_norm_bound.lean`) applied to `u := rmVec (lcOf g) x X Y Z`,
`g.inner x (rmVec …) (rmVec …) = ∑ k, (rmP g x X Y (e k) Z)^2` (this is exactly the definition
`rmP g x a b c d = g(R(a,b)d, c)`), and by the squared component bound `rmP_sq_le_B` above (the
squared form of `Submission.Work.Diff.GE.rmP_norm_bound_smooth`, PROVED in
`Submission/Work/Diff/GE/connectionVariation_le.lean`)
each summand is `≤ rmNormSq g x * (g X X) * (g Y Y) * (g Z Z)` because `g.inner x (e k) (e k) = 1`.
Summing the `n` summands gives the claim.  The statement is in squared form precisely to avoid
square-root side conditions.  A *sharper* statement (without the factor `n`) is the
`sorry`ed `Work.Diff.GE.rmVec_normSq_le`; the crude form with `n` is all that is needed here.

NOTE: only the (sorry-free) module `Submission.Work.Diff.GE.rmP_norm_bound` is imported, and
`Submission/Work/Diff/GE/rmVec_normSq_le.lean` (which carries a `sorry`) is *not*. -/
theorem rmVec_normSq_le_B
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (x : M)
    (X Y Z : TangentSpace I x) :
    g.inner x (Submission.Diff.rmVec (Submission.Diff.lcOf g) x X Y Z)
        (Submission.Diff.rmVec (Submission.Diff.lcOf g) x X Y Z)
      ≤ (Module.finrank ℝ E : ℝ) * Submission.Diff.rmNormSq g x
          * (g.inner x X X * (g.inner x Y Y * (g.inner x Z Z))) := by
  by_cases hn : 0 < Module.finrank ℝ E
  · -- Step 1: Parseval in the orthonormal frame `e = onFrame g x`.
    have hdiag : ∀ i : Fin (Module.finrank ℝ E),
        g.inner x (Submission.Diff.onFrame g x i) (Submission.Diff.onFrame g x i) = 1 := by
      intro i
      have h := Work.Diff.GE.isONFrame_onFrame g x i i
      simpa using h
    rw [← Work.Diff.GE.onFrame_parseval_sq g x hn
      (Submission.Diff.rmVec (Submission.Diff.lcOf g) x X Y Z)]
    calc (∑ i, (g.inner x (Submission.Diff.onFrame g x i)
              (Submission.Diff.rmVec (Submission.Diff.lcOf g) x X Y Z)) ^ 2)
        = ∑ i, (Submission.Diff.rmP g x X Y (Submission.Diff.onFrame g x i) Z) ^ 2 := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [Submission.Diff.rmP, g.symm x (Submission.Diff.onFrame g x i)
            (Submission.Diff.rmVec (Submission.Diff.lcOf g) x X Y Z)]
      _ ≤ ∑ _i : Fin (Module.finrank ℝ E), Submission.Diff.rmNormSq g x *
              (g.inner x X X * (g.inner x Y Y * (g.inner x Z Z))) := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          have hb := rmP_sq_le_B (I := I) (M := M) hLC g x X Y
            (Submission.Diff.onFrame g x i) Z
          rw [hdiag i, one_mul] at hb
          exact hb
      _ = (Module.finrank ℝ E : ℝ) * Submission.Diff.rmNormSq g x *
            (g.inner x X X * (g.inner x Y Y * (g.inner x Z Z))) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
          simp only [nsmul_eq_mul]
          ring
  · -- degenerate case: `finrank ℝ E = 0`, so all tangent spaces are subsingletons
    have h0 : Module.finrank ℝ E = 0 := Nat.eq_zero_of_not_pos hn
    haveI hE : Subsingleton E := Module.finrank_zero_iff.mp h0
    haveI hT : Subsingleton (TangentSpace I x) := hE
    have hv : Submission.Diff.rmVec (Submission.Diff.lcOf g) x X Y Z = 0 := Subsingleton.elim _ _
    have hX0 : X = 0 := Subsingleton.elim X 0
    have hY0 : Y = 0 := Subsingleton.elim Y 0
    have hZ0 : Z = 0 := Subsingleton.elim Z 0
    rw [hv, hX0, hY0, hZ0, h0]
    simp

end Work.Diff.GE.EvolB
