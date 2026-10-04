import Mathlib
import Submission.Work.Diff.EXT.ConnCov.Kit
import Submission.Work.Diff.EXT.ConnCov.dtMet
import Submission.Work.Diff.EXT.ric_bound_of_curvBound

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The time derivative of the lowered connection difference

`Work.Diff.EXT.aOf G s X Y Z x = (G s).inner x (∇^{G s}_Y X − ∇^{G 0}_Y X) (Z x)` is the lowered
connection difference, and the target of this file computes its derivative in `s` at an interior
time `t ∈ (0,T)` of a Ricci flow.

The computation is the product rule applied to the two `s`-dependent factors, followed by the
first-variation formula for the Levi-Civita connection:

* the derivative of `s ↦ (G s).inner x (∇^{G s}_Y X) (Z x)` is `½ · dtKoszulForm G t X Y Z x`
  (`Work.Diff.T.hasDerivAt_koszulForm`, i.e. Clairaut + the Koszul formula);
* the derivative of `s ↦ (G s).inner x (∇^{G 0}_Y X) (Z x)` is
  `dtMet G t x (∇^{G 0}_Y X) (Z x)` (`Work.Diff.T.metric_family_deriv`).

Using `dtMet = −2 Ric` (`Work.Diff.EXT.ConnCov.dtMet_eq_of_flow`) and the algebraic identity
`Work.Diff.T.variation_algebra`, this equals the claimed expression.
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT.ConnCov

/-- `ricAt` is additive in its middle slot, obtained from the two `L`-forms. -/
theorem ricAt_sub_middle_kit
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]
    (hLC : LCSmooth I M) (g : SMet I M) (x : M) (u₁ u₂ v : TangentSpace I x) :
    ricAt (lcOf g) x (u₁ - u₂) v
      = ricAt (lcOf g) x u₁ v - ricAt (lcOf g) x u₂ v := by
  haveI : CovariantDerivative.ContMDiffCovariantDerivative (lcOf g) (⊤ : ℕ∞) := (hLC g).1.some
  rw [sub_eq_add_neg,
    Work.Diff.EXT.ricAt_add_middle_L g (inferInstance) x u₁ (-u₂) v,
    ← neg_one_smul ℝ u₂,
    Work.Diff.EXT.ricAt_smul_middle_L g (inferInstance) x (-1) u₂ v]
  ring

theorem aOf_hasDerivAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M)
    {G : ℝ → Submission.Diff.SMet I M} {T : ℝ} (hflow : Submission.Diff.IsRicciFlow G T)
    {t : ℝ} (ht : t ∈ Set.Ioo 0 T)
    {X Y Z : Π y : M, TangentSpace I y}
    (hX : Work.Diff.EXT.ATower.SmE I M X)
    (hY : Work.Diff.EXT.ATower.SmE I M Y)
    (hZ : Work.Diff.EXT.ATower.SmE I M Z) (x : M) :
    HasDerivAt (fun s : ℝ => Work.Diff.EXT.aOf G s X Y Z x)
      (-2 * Submission.Diff.ricAt (Submission.Diff.lcOf (G t)) x
          (Submission.Diff.lcOf (G t) Y x (X x) - Submission.Diff.lcOf (G 0) Y x (X x)) (Z x)
        + (1 / 2 : ℝ) * (Submission.Diff.covDerivSym2 (Submission.Diff.lcOf (G t)) (Submission.Diff.dtMet G t) X Y Z x
            + Submission.Diff.covDerivSym2 (Submission.Diff.lcOf (G t)) (Submission.Diff.dtMet G t) Y X Z x
            - Submission.Diff.covDerivSym2 (Submission.Diff.lcOf (G t)) (Submission.Diff.dtMet G t) Z X Y x)) t := by
  have hX' : CMDiff ∞ (T% X) := hX
  have hY' : CMDiff ∞ (T% Y) := hY
  have hZ' : CMDiff ∞ (T% Z) := hZ
  -- joint smoothness on the open interval, from the half-open slab
  have hJopen : IsOpen (Set.Ioo (0 : ℝ) T) := isOpen_Ioo
  have hJs : JointSmooth G (Set.Ioo (0 : ℝ) T) :=
    (hflow.1).mono (Set.prod_mono Set.Ioo_subset_Ico_self (Set.Subset.refl _))
  -- the derivative of the moving part: Koszul form, by Clairaut
  have hKos : ∀ s : ℝ, (G s).inner x (lcOf (G s) Y x (X x)) (Z x)
      = (1 / 2 : ℝ) * Work.Diff.T.koszulForm G X Y Z x s := by
    intro s
    simpa only [Work.Diff.T.koszulForm] using
      Work.Diff.T.lcOf_apply_inner_koszul G s X Y Z hX' hY' hZ' x
  have hpair : HasDerivAt (fun s : ℝ => (G s).inner x (lcOf (G s) Y x (X x)) (Z x))
      ((1 / 2 : ℝ) * Work.Diff.T.dtKoszulForm G t X Y Z x) t :=
    ((Work.Diff.T.hasDerivAt_koszulForm hJopen hJs ht X Y Z hX' hY' hZ' x).const_mul (1 / 2)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall hKos)
  -- the derivative of the frozen part
  have hfixed : HasDerivAt (fun s : ℝ => (G s).inner x (lcOf (G 0) Y x (X x)) (Z x))
      (dtMet G t x (lcOf (G 0) Y x (X x)) (Z x)) t :=
    Work.Diff.T.metric_family_deriv hJopen hJs ht x _ (Z x)
  have hprod := hpair.sub hfixed
  -- split `aOf` into the difference of the two inner products
  have hsplit : (fun s : ℝ => Work.Diff.EXT.aOf G s X Y Z x)
      = fun s : ℝ => (G s).inner x (lcOf (G s) Y x (X x)) (Z x)
        - (G s).inner x (lcOf (G 0) Y x (X x)) (Z x) := by
    funext s
    simp only [Work.Diff.EXT.aOf, map_sub, sub_apply]
  have hmain : HasDerivAt (fun s : ℝ => Work.Diff.EXT.aOf G s X Y Z x)
      ((1 / 2 : ℝ) * Work.Diff.T.dtKoszulForm G t X Y Z x
        - dtMet G t x (lcOf (G 0) Y x (X x)) (Z x)) t :=
    hprod.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq hsplit)
  -- the algebraic comparison
  have hvar := Work.Diff.T.variation_algebra (G := G) (J := Set.Ioo (0 : ℝ) T) hJopen hJs ht
    X Y Z hX' hY' hZ' (x := x)
  have hd1 := dtMet_eq_of_flow (G := G) (T := T) hflow ht x (lcOf (G t) Y x (X x)) (Z x)
  have hd0 := dtMet_eq_of_flow (G := G) (T := T) hflow ht x (lcOf (G 0) Y x (X x)) (Z x)
  have hsub := ricAt_sub_middle_kit (I := I) (M := M) hLC (G t) x
    (lcOf (G t) Y x (X x)) (lcOf (G 0) Y x (X x)) (Z x)
  refine hmain.congr_deriv ?_
  linarith [hvar, hd1, hd0, hsub]

end Work.Diff.EXT.ConnCov

