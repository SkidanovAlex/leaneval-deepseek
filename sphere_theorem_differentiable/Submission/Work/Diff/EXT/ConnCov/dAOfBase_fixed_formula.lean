import Mathlib
import Submission.Work.Diff.EXT.ConnCov.Vocab
import Submission.Work.Diff.EXT.ConnCov.dAOfTowerBoundShi
import Submission.Work.Diff.EXT.ConnCov.dtMet
import Submission.Work.Diff.EXT.ric_bound_of_curvBound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The fixed-connection formula for the reaction `∂ₜ aOf`

Target: `Work.Diff.EXT.ConnCov.dAOfBase_fixed_formula`.

`dAOfBase G t` is the base of the `∇^{G 0}`-tower of `∂ₜ aOf(·)` (the *reaction* of the Gronwall
induction of `Submission/Work/Diff/EXT/ConnCov/covKAExt_bound.lean`).  Its *explicit value* on
smooth fields is the moving-connection Koszul formula `dAOfBase_apply`:

`dAOfBase G t X Y Z x = −2 Ric(δ(Y,X), Z) + ½((∇^{Gt}h)(X,Y,Z) + (∇^{Gt}h)(Y,X,Z) − (∇^{Gt}h)(Z,X,Y))`,

with `h = ∂ₜg = −2 Ric` and `δ := ∇^{Gt} − ∇^{G0}`.  The present lemma rewrites this into a
formula that only involves the **fixed** connection `∇^{G0}`: the `Ric(δ(·,·),·)`-terms cancel
pairwise (using that `δ` is symmetric, `covDiff_symm`, and that `Ric` is symmetric,
`ricAt_symm_L`) and the moving derivatives of `Ric` become fixed ones.  Concretely, with
`RIC := ricAt (lcOf (G t))` and `S₀` the shifted level-`1` fixed tower of `RIC` (so that
`S₀ U V W x + RIC(V,W) = (∇^{G0}_U RIC)(V,W)`, `S₀_apply`), the formula reads

`dAOfBase G t X Y Z x = −(S₀ X Y Z x + RIC(Y,Z)) − (S₀ Y X Z x + RIC(X,Z)) + (S₀ Z X Y x + RIC(X,Y))`.

This is the algebraic base of the Leibniz expansion of the tower of `dAOfBase` into towers of
`RIC` and `S₀` (steps 2–4 of the plan in `dAOfTowerBoundShiPar.lean`).

## Proof

* `dAOfBase_apply` gives the moving formula; `dtMet_eq_of_flow` gives `h = −2 RIC` as functions of
  the base point, and `covDerivSym2` is linear in `h` (`covDerivSym2_const_mul_factor`), so the
  three Koszul terms become `−2 (∇^{Gt}_U RIC)(V,W)`.
* `covDerivSym2_transfer` moves each `(∇^{Gt}_U RIC)(V,W)` to the fixed connection at the cost of
  the two `δ`-insertions.
* `S₀_apply` rewrites the right-hand side into the same three fixed derivatives `(∇^{G0}_U RIC)(V,W)`.
* What is left is the pointwise algebraic cancellation of the six `RIC(δ(·,·),·)`-terms: `δ` is
  symmetric (`covDiff_symm`) and `RIC` is symmetric (`ricAt_symm_L`), and `ring` closes.
-/

namespace Work.Diff.EXT.ConnCov

/-- `covDerivSym2` is linear in the bilinear form `h`: scaling `h` by a constant scales the
covariant derivative by the same constant.  (A local copy of `Work.Diff.GE.Sm.covDerivSym2_const_mul`
so that this module needs no additional import.) -/
theorem covDerivSym2_const_mul_factor
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I (⊤ : ℕ∞) M]
    (cov : CovariantDerivative I E (TangentSpace I (M := M))) (c : ℝ)
    (h : Π y : M, TangentSpace I y → TangentSpace I y → ℝ)
    (X Y Z : Π y : M, TangentSpace I y) (x : M) :
    Submission.Diff.covDerivSym2 cov (fun y a b => c * h y a b) X Y Z x
      = c * Submission.Diff.covDerivSym2 cov h X Y Z x := by
  have hfun : (fun y : M => c * h y (Y y) (Z y))
      = (fun y : M => c • (fun y' : M => h y' (Y y') (Z y')) y) := by
    funext y
    rw [smul_eq_mul]
  rw [Submission.Diff.covDerivSym2, Submission.Diff.covDerivSym2, hfun,
    Commons.Geometry.Manifold.Riemannian.mvfderiv_const_smul]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem dAOfBase_fixed_formula
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M)
    {G : ℝ → Submission.Diff.SMet I M} {T : ℝ} (hflow : Submission.Diff.IsRicciFlow G T)
    {t : ℝ} (ht : t ∈ Set.Ioo 0 T)
    (X Y Z : Π y : M, TangentSpace I y)
    (hX : Work.Diff.EXT.ATower.SmE I M X) (hY : Work.Diff.EXT.ATower.SmE I M Y)
    (hZ : Work.Diff.EXT.ATower.SmE I M Z) (x : M) :
    Work.Diff.EXT.ConnCov.dAOfBase G t
        (Fin.elim0 : Fin 0 → (Π y : M, TangentSpace I y)) X Y Z x
      = - (Work.Diff.EXT.ConnCov.S₀ G t X Y Z x
            + Submission.Diff.ricAt (Submission.Diff.lcOf (G t)) x (Y x) (Z x))
        - (Work.Diff.EXT.ConnCov.S₀ G t Y X Z x
            + Submission.Diff.ricAt (Submission.Diff.lcOf (G t)) x (X x) (Z x))
        + (Work.Diff.EXT.ConnCov.S₀ G t Z X Y x
            + Submission.Diff.ricAt (Submission.Diff.lcOf (G t)) x (X x) (Y x)) := by
  -- The moving Levi-Civita connection is a smooth covariant derivative, so `Ric` is additive in
  -- each of its two vector slots (needed to transfer `∇^{Gt}` derivatives to `∇^{G0}`).
  have hcovt : (Submission.Diff.lcOf (G t)).ContMDiffCovariantDerivative (⊤ : ℕ∞) :=
    (hLC (G t)).1.some
  have hadd1 : ∀ (y : M) (a b c : TangentSpace I y),
      Submission.Diff.ricAt (Submission.Diff.lcOf (G t)) y (a + b) c
        = Submission.Diff.ricAt (Submission.Diff.lcOf (G t)) y a c
          + Submission.Diff.ricAt (Submission.Diff.lcOf (G t)) y b c :=
    fun y a b c => Work.Diff.EXT.ricAt_add_middle_L (G t) hcovt y a b c
  have hadd2 : ∀ (y : M) (a b c : TangentSpace I y),
      Submission.Diff.ricAt (Submission.Diff.lcOf (G t)) y a (b + c)
        = Submission.Diff.ricAt (Submission.Diff.lcOf (G t)) y a b
          + Submission.Diff.ricAt (Submission.Diff.lcOf (G t)) y a c :=
    fun y a b c => Work.Diff.EXT.ricAt_add_last_L (G t) hcovt y a b c
  -- Along a Ricci flow the first variation of the metric is `−2 Ric` at an interior time.
  have hdtfun : Submission.Diff.dtMet G t
      = fun z p q => (-2 : ℝ) * Submission.Diff.ricAt (Submission.Diff.lcOf (G t)) z p q := by
    funext z p q
    exact Work.Diff.EXT.ConnCov.dtMet_eq_of_flow hflow ht z p q
  -- The explicit (moving-connection) value of the reaction.
  rw [Work.Diff.EXT.ConnCov.dAOfBase_apply hLC hflow ht hX hY hZ x]
  -- Write the Ric slot as the connection difference, so that the symmetry of `δ` applies to it.
  rw [show (Submission.Diff.lcOf (G t)) Y x (X x) - (Submission.Diff.lcOf (G 0)) Y x (X x)
        = Work.Diff.EXT.ConnCov.covDiff G t Y X x from rfl]
  -- The right-hand side, in terms of the fixed covariant derivative of `Ric`.
  rw [Work.Diff.EXT.ConnCov.S₀_apply G t X Y Z x,
    Work.Diff.EXT.ConnCov.S₀_apply G t Y X Z x,
    Work.Diff.EXT.ConnCov.S₀_apply G t Z X Y x]
  -- `∂ₜg = −2 Ric`, and the Koszul combination is linear in the lowered form.
  rw [hdtfun]
  rw [covDerivSym2_const_mul_factor (Submission.Diff.lcOf (G t)) (-2)
        (fun z p q => Submission.Diff.ricAt (Submission.Diff.lcOf (G t)) z p q) X Y Z x,
      covDerivSym2_const_mul_factor (Submission.Diff.lcOf (G t)) (-2)
        (fun z p q => Submission.Diff.ricAt (Submission.Diff.lcOf (G t)) z p q) Y X Z x,
      covDerivSym2_const_mul_factor (Submission.Diff.lcOf (G t)) (-2)
        (fun z p q => Submission.Diff.ricAt (Submission.Diff.lcOf (G t)) z p q) Z X Y x]
  -- Transfer the three moving derivatives of `Ric` to the fixed connection.
  rw [Work.Diff.EXT.ConnCov.covDerivSym2_transfer G t
        (fun z p q => Submission.Diff.ricAt (Submission.Diff.lcOf (G t)) z p q) hadd1 hadd2 X Y Z x,
      Work.Diff.EXT.ConnCov.covDerivSym2_transfer G t
        (fun z p q => Submission.Diff.ricAt (Submission.Diff.lcOf (G t)) z p q) hadd1 hadd2 Y X Z x,
      Work.Diff.EXT.ConnCov.covDerivSym2_transfer G t
        (fun z p q => Submission.Diff.ricAt (Submission.Diff.lcOf (G t)) z p q) hadd1 hadd2 Z X Y x]
  -- Symmetry of the connection difference `δ = ∇^{Gt} − ∇^{G0}` (both connections are torsion free).
  rw [Work.Diff.EXT.ConnCov.covDiff_symm hLC G t Y X hY hX x,
    Work.Diff.EXT.ConnCov.covDiff_symm hLC G t Z X hZ hX x,
    Work.Diff.EXT.ConnCov.covDiff_symm hLC G t Z Y hZ hY x]
  -- Symmetry of `Ric`, to cancel the last pair of corrections.
  rw [Work.Diff.EXT.ricAt_symm_L hLC (G t) hcovt x
        (Work.Diff.EXT.ConnCov.covDiff G t X Z x) (Y x)]
  simp only [Work.Diff.EXT.ConnCov.covDiff]
  ring

end Work.Diff.EXT.ConnCov
