import Mathlib
import Submission.Work.Diff.EXT.ConnCov.Kit
import Submission.Work.Diff.EXT.covKRmExt_eval_bound
import Submission.Work.Diff.EXT.ConnCov.dAOfTowerBoundShi
import Submission.Commons.Geometry.Manifold.Riemannian.metricCompatible_scaleMetric

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Submission.Diff

namespace Work.Diff.EXT.ConnCov

/-- **The connection difference of two torsion-free connections is symmetric.**
`δ(X,Y) = ∇^{G t}_X Y − ∇^{G 0}_X Y` satisfies `δ(X,Y) = δ(Y,X)`, because both `lcOf (G 0)` and
`lcOf (G t)` are torsion free (`hLC`), so the Lie-bracket terms cancel. -/
theorem covDiff_symm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (hLC : Submission.Diff.LCSmooth I M) (G : ℝ → Submission.Diff.SMet I M) (t : ℝ)
    (X Y : Π y : M, TangentSpace I y)
    (hX : Work.Diff.EXT.ATower.SmE I M X) (hY : Work.Diff.EXT.ATower.SmE I M Y) (x : M) :
    Work.Diff.EXT.ConnCov.covDiff G t X Y x = Work.Diff.EXT.ConnCov.covDiff G t Y X x := by
  have hXd : MDiffAt (T% X) x := hX.mdifferentiableAt (by simp)
  have hYd : MDiffAt (T% Y) x := hY.mdifferentiableAt (by simp)
  have h1 := (lcOf (G t)).torsion_apply (X := X) (Y := Y) hXd hYd
  have h2 := (lcOf (G 0)).torsion_apply (X := X) (Y := Y) hXd hYd
  have ht1 : (lcOf (G t)).torsion x (X x) (Y x) = 0 := by
    have h : (lcOf (G t)).torsion = 0 := (hLC (G t)).2.1
    rw [h]; simp
  have ht0 : (lcOf (G 0)).torsion x (X x) (Y x) = 0 := by
    have h : (lcOf (G 0)).torsion = 0 := (hLC (G 0)).2.1
    rw [h]; simp
  rw [ht1] at h1
  rw [ht0] at h2
  have h1' : lcOf (G t) Y x (X x) - lcOf (G t) X x (Y x) = mlieBracket I X Y x :=
    sub_eq_zero.mp h1.symm
  have h2' : lcOf (G 0) Y x (X x) - lcOf (G 0) X x (Y x) = mlieBracket I X Y x :=
    sub_eq_zero.mp h2.symm
  have e1 : lcOf (G t) X x (Y x) = lcOf (G t) Y x (X x) - mlieBracket I X Y x := by
    rw [← h1']; abel
  have e0 : lcOf (G 0) X x (Y x) = lcOf (G 0) Y x (X x) - mlieBracket I X Y x := by
    rw [← h2']; abel
  simp only [Work.Diff.EXT.ConnCov.covDiff, Pi.sub_apply]
  rw [e1, e0]
  abel

/-- **The shifted level-`1` tower of `Ric(G t)`** with respect to the fixed connection: it is
`step (∇^{G 0}) (baseRic (G t))` evaluated with the first *value* slot used as the derivation
direction, so that (by `S₀_apply`)
`S₀ G t X Y Z x = (∇^{G 0}_X Ric(G t))(Y,Z) − Ric(G t)(Y,Z)`.  (Its `Op3 0` version for the
recursion of step 2 of the plan below is `fun _ X Y Z y => S₀ G t X Y Z y`.) -/
noncomputable def S₀
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (G : ℝ → Submission.Diff.SMet I M) (t : ℝ)
    (X Y Z : Π y : M, TangentSpace I y) (y : M) : ℝ :=
  Work.Diff.EXT.ATower.step (Submission.Diff.lcOf (G 0))
    (Work.Diff.EXT.ConnCov.baseRic (G t)) (fun _ : Fin 1 => X) Y Z Z y

/-- **Unfolding of `S₀`**: the shifted level-`1` tower plus the shift `Ric(Y,Z)` is the fixed
covariant derivative of `Ric(G t)` at `(Y,Z)` in the direction `X` (i.e. `covDerivSym2` with the
lowered form `h = Ric(G t)` and the *fixed* connection). -/
theorem S₀_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (G : ℝ → Submission.Diff.SMet I M) (t : ℝ)
    (X Y Z : Π y : M, TangentSpace I y) (x : M) :
    S₀ G t X Y Z x + Submission.Diff.ricAt (Submission.Diff.lcOf (G t)) x (Y x) (Z x)
      = Submission.Diff.covDerivSym2 (Submission.Diff.lcOf (G 0))
          (fun (y : M) (a b : TangentSpace I y) =>
            Submission.Diff.ricAt (Submission.Diff.lcOf (G t)) y a b) X Y Z x := by
  have hfun : Work.Diff.EXT.ConnCov.baseRic (G t) (fun _ : Fin 0 => X) Y Z Z
      = fun y : M => Submission.Diff.ricAt (Submission.Diff.lcOf (G t)) y (Y y) (Z y) := rfl
  simp only [S₀, Work.Diff.EXT.ConnCov.baseRic, hfun, Work.Diff.EXT.ATower.step,
    Work.Diff.EXT.ATower.tower, Finset.univ_eq_empty, Finset.sum_empty,
    Submission.Diff.covDerivSym2, Function.comp_apply]
  ring

/-- **Level-`1` transfer for `covDerivSym2`.**  Replacing the moving connection `∇^{G t}` by the
fixed one `∇^{G 0}` in the covariant derivative of a lowered bilinear form `h` (additive in each
slot) costs exactly the two `δ := covDiff G t`-insertions. -/
theorem covDerivSym2_transfer
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (G : ℝ → Submission.Diff.SMet I M) (t : ℝ)
    (h : Π y : M, TangentSpace I y → TangentSpace I y → ℝ)
    (hadd : ∀ (y : M) (a b c : TangentSpace I y),
      h y (a + b) c = h y a c + h y b c)
    (hadd₂ : ∀ (y : M) (a b c : TangentSpace I y),
      h y a (b + c) = h y a b + h y a c)
    (X Y Z : Π y : M, TangentSpace I y) (x : M) :
    Submission.Diff.covDerivSym2 (Submission.Diff.lcOf (G t)) h X Y Z x
      = Submission.Diff.covDerivSym2 (Submission.Diff.lcOf (G 0)) h X Y Z x
        - h x (Work.Diff.EXT.ConnCov.covDiff G t Y X x) (Z x)
        - h x (Y x) (Work.Diff.EXT.ConnCov.covDiff G t Z X x) := by
  have e1 : Submission.Diff.lcOf (G t) Y x (X x)
      = Work.Diff.EXT.ConnCov.covDiff G t Y X x + Submission.Diff.lcOf (G 0) Y x (X x) :=
    sub_eq_iff_eq_add.mp rfl
  have e2 : Submission.Diff.lcOf (G t) Z x (X x)
      = Work.Diff.EXT.ConnCov.covDiff G t Z X x + Submission.Diff.lcOf (G 0) Z x (X x) :=
    sub_eq_iff_eq_add.mp rfl
  simp only [Submission.Diff.covDerivSym2, e1, e2]
  rw [hadd x (Work.Diff.EXT.ConnCov.covDiff G t Y X x) (Submission.Diff.lcOf (G 0) Y x (X x)) (Z x),
    hadd₂ x (Y x) (Work.Diff.EXT.ConnCov.covDiff G t Z X x) (Submission.Diff.lcOf (G 0) Z x (X x))]
  ring

/-! ## Step 2 of the plan: linearity of the recursion in the `Op3` argument

`step cov` is linear in its operator argument, pointwise in the values.  This is the first half of
step 2 (the second half — commutation with permutations of the three *value* slots — is delegated);
together they let the recursion be applied to the fixed linear combination of `S₀`/`RIC₀`
permutations delivered by `dAOfBase_fixed_formula`. -/

/-- **Constant-factor rule for `mvfderiv` on scalar functions**, in the applied form used by
`step_linear`: `mvfderiv I (fun y => c * g y) x w = c * mvfderiv I g x w`.  This is
`mvfderiv_const_smul` (`Submission/Commons/.../metricCompatible_scaleMetric.lean`, which needs no
differentiability hypothesis) with the scalar-multiplication and the `*`-form reconciled, and with
the continuous-linear-map application carried out. -/
theorem mvfderiv_const_mul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (c : ℝ) (g : M → ℝ) (x : M) (w : TangentSpace I x) :
    mvfderiv I (fun y : M => c * g y) x w = c * mvfderiv I g x w := by
  have h : mvfderiv I (fun y : M => c • g y) x = c • mvfderiv I g x :=
    Commons.Geometry.Manifold.Riemannian.mvfderiv_const_smul c g x
  have h' := congrArg (fun (L : TangentSpace I x →L[ℝ] ℝ) => L w) h
  simpa only [ContinuousLinearMap.smul_apply, Pi.smul_apply', smul_eq_mul] using h'

/-- **Splitting a `Fin k`-sum of two scaled families.**  This is the bookkeeping identity of
`step_linear`'s correction terms: the left summands are `c₁ * aᵢ + c₂ * bᵢ`, the right side is
`c₁ * (∑ aᵢ) + c₂ * (∑ bᵢ)`.  Proved by induction on the finset with `simp`/`ring`, so it does not
depend on the exact statement shape of `Finset.sum_add_distrib`/`Finset.mul_sum`. -/
theorem sum_add_scaled {k : ℕ} (a b : Fin k → ℝ) (c₁ c₂ : ℝ) :
    (∑ i, (c₁ * a i + c₂ * b i)) = c₁ * (∑ i, a i) + c₂ * (∑ i, b i) := by
  induction (Finset.univ : Finset (Fin k)) using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, Finset.sum_insert hi, ih]
      ring

/-- **`step` is linear in its operator argument** (pointwise in the values).  Additivity of
`mvfderiv` (`mvfderiv_add`) and the Leibniz rule for scalar multiples (`mvfderiv_smul`, with a
constant factor) handle the derivative term; the slot corrections are pointwise linear. -/
theorem step_linear
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (cov : CovariantDerivative I E (TangentSpace I (M := M))) {k : ℕ}
    (c₁ c₂ : ℝ) (τ₁ τ₂ : Work.Diff.EXT.ATower.Op3 (I := I) (M := M) k)
    (h₁ : ∀ (w : Fin k → (Π y : M, TangentSpace I y)) (X Y Z : Π y : M, TangentSpace I y),
      (∀ i, Work.Diff.EXT.ATower.SmE I M (w i)) → Work.Diff.EXT.ATower.SmE I M X →
      Work.Diff.EXT.ATower.SmE I M Y → Work.Diff.EXT.ATower.SmE I M Z →
      Work.Diff.EXT.ATower.SmF I M (τ₁ w X Y Z))
    (h₂ : ∀ (w : Fin k → (Π y : M, TangentSpace I y)) (X Y Z : Π y : M, TangentSpace I y),
      (∀ i, Work.Diff.EXT.ATower.SmE I M (w i)) → Work.Diff.EXT.ATower.SmE I M X →
      Work.Diff.EXT.ATower.SmE I M Y → Work.Diff.EXT.ATower.SmE I M Z →
      Work.Diff.EXT.ATower.SmF I M (τ₂ w X Y Z))
    (v : Fin (k + 1) → (Π y : M, TangentSpace I y)) (A B C : Π y : M, TangentSpace I y)
    (hv : ∀ i, Work.Diff.EXT.ATower.SmE I M (v i)) (hA : Work.Diff.EXT.ATower.SmE I M A)
    (hB : Work.Diff.EXT.ATower.SmE I M B) (hC : Work.Diff.EXT.ATower.SmE I M C) (x : M) :
    Work.Diff.EXT.ATower.step cov
        (fun w X Y Z y => c₁ * τ₁ w X Y Z y + c₂ * τ₂ w X Y Z y) v A B C x
      = c₁ * Work.Diff.EXT.ATower.step cov τ₁ v A B C x
        + c₂ * Work.Diff.EXT.ATower.step cov τ₂ v A B C x := by
  have hd₁ : MDiffAt (τ₁ (fun i : Fin k => v i.succ) A B C) x :=
    (h₁ (fun i : Fin k => v i.succ) A B C (fun i => hv i.succ) hA hB hC).mdifferentiableAt
      (by simp)
  have hd₂ : MDiffAt (τ₂ (fun i : Fin k => v i.succ) A B C) x :=
    (h₂ (fun i : Fin k => v i.succ) A B C (fun i => hv i.succ) hA hB hC).mdifferentiableAt
      (by simp)
  have hmv : mvfderiv I
        ((fun (w : Fin k → (Π y : M, TangentSpace I y))
          (X Y Z : Π y : M, TangentSpace I y) (y : M) =>
          c₁ * τ₁ w X Y Z y + c₂ * τ₂ w X Y Z y)
          (fun i : Fin k => v i.succ) A B C) x (v 0 x)
      = c₁ * mvfderiv I (τ₁ (fun i : Fin k => v i.succ) A B C) x (v 0 x)
        + c₂ * mvfderiv I (τ₂ (fun i : Fin k => v i.succ) A B C) x (v 0 x) := by
    change mvfderiv I (fun y : M => c₁ * τ₁ (fun i : Fin k => v i.succ) A B C y
          + c₂ * τ₂ (fun i : Fin k => v i.succ) A B C y) x (v 0 x)
        = c₁ * mvfderiv I (τ₁ (fun i : Fin k => v i.succ) A B C) x (v 0 x)
          + c₂ * mvfderiv I (τ₂ (fun i : Fin k => v i.succ) A B C) x (v 0 x)
    rw [show (fun y : M => c₁ * τ₁ (fun i : Fin k => v i.succ) A B C y
            + c₂ * τ₂ (fun i : Fin k => v i.succ) A B C y)
        = (fun y : M => c₁ * τ₁ (fun i : Fin k => v i.succ) A B C y)
          + (fun y : M => c₂ * τ₂ (fun i : Fin k => v i.succ) A B C y) from by
      funext y; rfl]
    rw [mvfderiv_add (g := fun y : M => c₁ * τ₁ (fun i : Fin k => v i.succ) A B C y)
      (g' := fun y : M => c₂ * τ₂ (fun i : Fin k => v i.succ) A B C y)
      ((mdifferentiableAt_const (c := c₁)).mul hd₁)
      ((mdifferentiableAt_const (c := c₂)).mul hd₂)]
    rw [add_apply]
    rw [mvfderiv_const_mul (I := I) (M := M) c₁
        (τ₁ (fun i : Fin k => v i.succ) A B C) x (v 0 x),
      mvfderiv_const_mul (I := I) (M := M) c₂
        (τ₂ (fun i : Fin k => v i.succ) A B C) x (v 0 x)]
  -- NOTE (step 2a, remaining gap): everything above is proved — `hmv` (the derivative identity with
  -- the additive split by `mvfderiv_add` and the constant-factor rule `mvfderiv_const_mul`) is the
  -- whole mathematical content of this lemma, and the four slot corrections are pointwise linear
  -- (`ring`).  What remains is one normalization step in the *outer* goal: after
  -- `simp only [Work.Diff.EXT.ATower.step, Function.comp_apply]` the two sides are the unfolded
  -- recursion expressions, and the `mvfderiv` term there must be lined up with `hmv`'s statement
  -- before rewriting.  Recipe that works: first the β-bridge
  --   `have hnorm : mvfderiv I ((fun w X Y Z y => c₁ * τ₁ w X Y Z y + c₂ * τ₂ w X Y Z y)
  --        (fun i : Fin k => v i.succ) A B C) x (v 0 x)
  --      = mvfderiv I (fun y : M => c₁ * τ₁ (fun i : Fin k => v i.succ) A B C y
  --          + c₂ * τ₂ (fun i : Fin k => v i.succ) A B C y) x (v 0 x) := rfl`
  -- (definitional, β-reduction only), then `simp only [hnorm, hmv, add_apply]` and `ring`.
  -- Lesson recorded for the neighbouring terms: after `mvfderiv_add` the two `d%`-applications sit
  -- under a `+` of continuous linear maps, so `rw [add_apply]` must come *before* any rewrite that
  -- needs the applied form (this was the single blocker of `mvfderiv_const_mul` above).
  -- STATUS: `hmv` above is proved and is stated in the *applied-lambda* form (the `change` inside
  -- its proof confirms the applied/reduced bridge is `change`-able, even though it is not
  -- `rfl`-provable as a term).  So the only remaining step of this lemma is the outer equality:
  -- after `simp only [Work.Diff.EXT.ATower.step, Function.comp_apply]` both sides are the unfolded
  -- recursion expressions; `hmv` rewrites the derivative term, and what is left is to reconcile the
  -- four correction terms, whose `Fin k`-sum has summands `c₁ * aᵢ + c₂ * bᵢ` on the left against
  -- `c₁ * (∑ aᵢ) + c₂ * (∑ bᵢ)` on the right.  Plan: `rw [hmv]`, then split/factor the sum
  -- (now done by the banked identity `sum_add_scaled` above), with `ring` finishing on the atoms.
  simp only [Work.Diff.EXT.ATower.step, Function.comp_apply, hmv, sum_add_scaled]
  ring

/-- **The field-level form of `dAOfBase` on smooth fields** (immediate from the proved
/-- **(Inlined) the fixed-connection formula for the reaction.**  This is the statement of the
/-- **`dAOfBase` as a pointwise `Op3`-level combination** of `S₀`-permutations and `baseRic`: the
`Op3 0` form of the proved `dAOfBase_fixed_formula`.  This is the shape that
`Work.Diff.EXT.ConnCov.tower_linear_ext` consumes, and it is the entry point of the Leibniz
expansion of the reaction tower (step 4 of the module's plan). -/
theorem dAOfBase_eq_opCombination
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
      = - (S₀ G t X Y Z x
            + Work.Diff.EXT.ConnCov.baseRic (G t)
                (Fin.elim0 : Fin 0 → (Π y : M, TangentSpace I y)) Y Z Z x)
        - (S₀ G t Y X Z x
            + Work.Diff.EXT.ConnCov.baseRic (G t)
                (Fin.elim0 : Fin 0 → (Π y : M, TangentSpace I y)) X Z Z x)
        + (S₀ G t Z X Y x
            + Work.Diff.EXT.ConnCov.baseRic (G t)
                (Fin.elim0 : Fin 0 → (Π y : M, TangentSpace I y)) X Y Y x) := by
  -- NOTE (import cycle): this is the `Op3`-level form of the proved
  -- `Work.Diff.EXT.ConnCov.dAOfBase_fixed_formula`, but that lemma lives in
  -- `Submission/Work/Diff/EXT/ConnCov/dAOfBase_fixed_formula.lean`, whose `depends_on` includes
  -- *this* file (it uses `S₀`, `S₀_apply`, `covDerivSym2_transfer`, `covDiff_symm`), so importing it
  -- here is a build cycle.  Two clean repairs: (a) inline that lemma's statement+proof here under a
  -- fresh name (its proof is `dAOfBase_apply` + `covDerivSym2_const_mul_factor` + the three
  -- `S₀_apply` rewrites + `covDerivSym2_transfer` + `covDiff_symm` + `ricAt_symm_L` + `ring`), or
  -- (b) move `S₀`, `S₀_apply`, `covDerivSym2_transfer`, `covDiff_symm` (and the linearity lemmas
  -- `step_linear`, `tower_linear_ext` clients) into a helper module imported by both files.  The
  -- pointwise statement itself is the `baseRic`-rewriting of `dAOfBase_fixed_formula`.
  rw [dAOfBase_fixed_formula_inline (I := I) (M := M) hLC hflow ht X Y Z hX hY hZ x]
  simp only [Work.Diff.EXT.ConnCov.baseRic]

delegated `Submission.Work.Diff.EXT.ConnCov.dAOfBase_fixed_formula`, inlined here (with its proof)
because that module imports *this* one — it was spawned with `S₀`, `S₀_apply`,
`covDerivSym2_transfer`, `covDiff_symm` in scope — so importing it back is a build cycle.  Proof
plan (see the chunks below): `dAOfBase_apply` (moving formula) → the Ric slot as `covDiff G t Y X`
→ the three `S₀_apply` rewrites → `dtMet = −2·ricAt` → `covDerivSym2_const_mul_factor` →
`covDerivSym2_transfer` (three times) → `covDiff_symm` + `ricAt_symm_L` for the cancellation →
`ring`. -/
theorem dAOfBase_fixed_formula_inline
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
  -- CHUNK 2: `dtMet = −2 Ric`, factor the constant out of each `covDerivSym2`
  -- (inlined `covDerivSym2_const_mul_factor`, using the proved `mvfderiv_const_mul`), transfer the
  -- three moving derivatives to the fixed connection, cancel with `covDiff_symm` + `ricAt_symm_L`.
  have hcm : ∀ (c : ℝ) (h' : Π y : M, TangentSpace I y → TangentSpace I y → ℝ)
      (U V W : Π y : M, TangentSpace I y),
      Submission.Diff.covDerivSym2 (Submission.Diff.lcOf (G t))
          (fun y a b => c * h' y a b) U V W x
        = c * Submission.Diff.covDerivSym2 (Submission.Diff.lcOf (G t)) h' U V W x := by
    intro c h' U V W
    simp only [Submission.Diff.covDerivSym2]
    rw [mvfderiv_const_mul (I := I) (M := M) c (fun y : M => h' y (V y) (W y)) x (U x)]
    ring
  rw [hdtfun]
  rw [hcm (-2) (fun z p q => Submission.Diff.ricAt (Submission.Diff.lcOf (G t)) z p q) X Y Z,
    hcm (-2) (fun z p q => Submission.Diff.ricAt (Submission.Diff.lcOf (G t)) z p q) Y X Z,
    hcm (-2) (fun z p q => Submission.Diff.ricAt (Submission.Diff.lcOf (G t)) z p q) Z X Y]
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

`Work.Diff.EXT.ConnCov.dAOfBase_apply`): at an interior time the reaction is

`−2 Ric(∇^{g_t} − ∇^{g_0}, ·) + ½((∇^{g_t}_X h)(Y,Z) + (∇^{g_t}_Y h)(X,Z) − (∇^{g_t}_Z h)(X,Y))`

with `h = ∂ₜ g = dtMet G t`.  No metric-inverse factor occurs: everything is already lowered. -/
theorem dAOfBase_formula_par
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M)
    {G : ℝ → Submission.Diff.SMet I M} {T : ℝ} (hflow : Submission.Diff.IsRicciFlow G T)
    {t : ℝ} (ht : t ∈ Set.Ioo 0 T)
    (X Y Z : Π y : M, TangentSpace I y)
    (hX : Work.Diff.EXT.ATower.SmE I M X) (hY : Work.Diff.EXT.ATower.SmE I M Y)
    (hZ : Work.Diff.EXT.ATower.SmE I M Z) :
    Work.Diff.EXT.ConnCov.dAOfBase G t
        (Fin.elim0 : Fin 0 → (Π y : M, TangentSpace I y)) X Y Z
      = fun x : M =>
          -2 * Submission.Diff.ricAt (Submission.Diff.lcOf (G t)) x
              (Submission.Diff.lcOf (G t) Y x (X x) - Submission.Diff.lcOf (G 0) Y x (X x)) (Z x)
            + (1 / 2 : ℝ) * (Submission.Diff.covDerivSym2 (Submission.Diff.lcOf (G t))
                  (Submission.Diff.dtMet G t) X Y Z x
              + Submission.Diff.covDerivSym2 (Submission.Diff.lcOf (G t))
                  (Submission.Diff.dtMet G t) Y X Z x
              - Submission.Diff.covDerivSym2 (Submission.Diff.lcOf (G t))
                  (Submission.Diff.dtMet G t) Z X Y x) := by
  funext x
  exact Work.Diff.EXT.ConnCov.dAOfBase_apply (I := I) (M := M) hLC hflow ht hX hY hZ x


end Work.Diff.EXT.ConnCov
