import Mathlib
import Submission.Work.KeyLemma.Pencil
import Submission.Work.AbVar.P1Action.Points

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


/-!
# `ℙ¹` has two distinct `k`-points

The projective line `ℙ¹ = Work.AbVar.P1 k` has at least two rational points: this is the
`k`-point input needed by the rigidity-type arguments that take two *distinct* points of `ℙ¹`
(see `Work.KeyLemma.SymPow`, `Work.KeyLemma.Pencil`, `Work.KeyLemma.Sum.sumOfPoints_eq_of_factors`).

Concretely, the chart `D₊(X₀) = Spec (Away k[X₀,X₁] (X₀))` of `ℙ¹` is the affine line with
coordinate `X₁/X₀`; evaluating this coordinate at `c ∈ k` gives a `k`-point `p1Point c = [1 : c]`
of `ℙ¹`.  Since a field has (at least) two elements, `p1Point 0` and `p1Point 1` are distinct:
the chart inclusion is an open immersion, hence a monomorphism, so a hypothetical equality of the
two points would force `chartEval 0 = chartEval 1`, hence `0 = 1`.
-/

universe u

namespace Work.KeyLemma.Curve

noncomputable section

variable {k : Type u} [Field k]

open CategoryTheory AlgebraicGeometry

/-- Evaluation of the chart coordinate `X₁/X₀` of `D₊(X₀) ⊆ ℙ¹` at the element `c ∈ k`:
the `k`-algebra homomorphism `Away k[X₀,X₁] (X₀) ⟶ k` sending `X₁/X₀ ↦ c`. -/
noncomputable def p1ChartEval (c : k) :
    Work.AbVar.P1Action.chartRing k 0 →+* k :=
  (Polynomial.eval₂RingHom (RingHom.id k) c).comp
    (Work.AbVar.ProjectiveLine.awayToPoly (R := k) 0)

/-- The coordinate evaluation `p1ChartEval c` fixes the base field `k`. -/
lemma p1ChartEval_algebraMap (c : k) (r : k) :
    p1ChartEval (k := k) c (algebraMap k (Work.AbVar.P1Action.chartRing k 0) r) = r := by
  rw [p1ChartEval, RingHom.comp_apply, Work.AbVar.ProjectiveLine.awayToPoly_algMap]
  change Polynomial.eval₂ (RingHom.id k) c (Polynomial.C r) = r
  rw [Polynomial.eval₂_C, RingHom.id_apply]

/-- `p1ChartEval c` sends the chart coordinate `X₁/X₀` to `c`. -/
lemma p1ChartEval_awayU (c : k) :
    p1ChartEval (k := k) c (Work.AbVar.ProjectiveLine.awayU (R := k) 0 1) = c := by
  rw [p1ChartEval, RingHom.comp_apply,
    ← Work.AbVar.ProjectiveLine.polyToAway_X (R := k) (i := 0) (j := 1),
    Work.AbVar.ProjectiveLine.awayToPoly_awayU (R := k) (by decide)]
  exact Polynomial.eval₂_X _ _

/-- The `k`-point `[1 : c]` of `ℙ¹`, i.e. the point of the chart `D₊(X₀)` at which the
coordinate `X₁/X₀` takes the value `c`. -/
noncomputable def p1Point (c : k) : Pt k (Work.AbVar.P1 k) :=
  Over.homMk (Spec.map (CommRingCat.ofHom (p1ChartEval (k := k) c)) ≫
      Work.AbVar.P1Action.chartObjHom k 0) (by
    have hgen : (Spec.map (CommRingCat.ofHom (p1ChartEval (k := k) c)) ≫
        Work.AbVar.P1Action.chartObjHom k 0) ≫ (Work.AbVar.P1 k).hom = 𝟙 (Spec (.of k)) := by
      rw [Category.assoc, Work.AbVar.P1Action.chartObjHom_hom, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp]
      rw [show ((p1ChartEval (k := k) c).comp
          (algebraMap k (Work.AbVar.P1Action.chartRing k 0))) = RingHom.id k from
        RingHom.ext fun r => p1ChartEval_algebraMap c r]
      exact Spec.map_id _
    exact hgen)

/-- The underlying morphism of the `k`-point `p1Point c`, on the chart `D₊(X₀)`. -/
lemma p1Point_left (c : k) :
    (p1Point (k := k) c).left = Spec.map (CommRingCat.ofHom (p1ChartEval (k := k) c)) ≫
      Work.AbVar.P1Action.chartObjHom k 0 :=
  Over.homMk_left _ _

/-- The two points `[1 : 0]` and `[1 : 1]` of `ℙ¹` are distinct. -/
theorem p1Point_zero_ne_one : p1Point (k := k) 0 ≠ p1Point (k := k) 1 := by
  intro h
  have hleft : (p1Point (k := k) 0).left = (p1Point (k := k) 1).left :=
    congrArg (fun m => Over.Hom.left m) h
  rw [p1Point_left, p1Point_left] at hleft
  -- the chart inclusion is an open immersion, hence a monomorphism
  have hspec : Spec.map (CommRingCat.ofHom (p1ChartEval (k := k) 0)) =
      Spec.map (CommRingCat.ofHom (p1ChartEval (k := k) 1)) :=
    (cancel_mono (Work.AbVar.P1Action.chartObjHom k 0)).mp hleft
  have hcat : CommRingCat.ofHom (p1ChartEval (k := k) 0) =
      CommRingCat.ofHom (p1ChartEval (k := k) 1) := Spec.map_injective hspec
  have hhom : p1ChartEval (k := k) 0 = p1ChartEval (k := k) 1 := by
    have hh : (CommRingCat.ofHom (p1ChartEval (k := k) 0)).hom =
        (CommRingCat.ofHom (p1ChartEval (k := k) 1)).hom :=
      congrArg CommRingCat.Hom.hom hcat
    simpa using hh
  have hval := congrArg (fun f => f (Work.AbVar.ProjectiveLine.awayU (R := k) 0 1)) hhom
  rw [p1ChartEval_awayU, p1ChartEval_awayU] at hval
  exact zero_ne_one hval

end

theorem exists_ne_point_p1 {k : Type u} [Field k] :
    ∃ z i : Work.KeyLemma.Curve.Pt k (Work.AbVar.P1 k), z ≠ i :=
  ⟨p1Point (k := k) 0, p1Point (k := k) 1, p1Point_zero_ne_one⟩

end Work.KeyLemma.Curve
