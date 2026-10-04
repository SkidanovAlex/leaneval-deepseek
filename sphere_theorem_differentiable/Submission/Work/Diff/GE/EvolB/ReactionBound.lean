import Mathlib
import Submission.Work.Diff.GE.ReactionDefs
import Submission.Work.Diff.GE.Frame
import Submission.Work.Diff.GE.dRmPhi
import Submission.Work.Diff.GE.rot_pair
import Submission.Work.Diff.GE.Gest.hess_mul_field
import Submission.Work.Diff.EXT.laplAt_curvNormK_eq
import Submission.Work.Diff.GE.covRxn.Defs
import Submission.Work.Diff.GE.covRxnA.mvfderiv_rmFrameField
import Submission.Work.Diff.GE.covRxnA.mvfderiv_comp_curv4
import Submission.Work.Diff.GE.covRxnA.mvfderiv_pi_apply
import Submission.Work.Diff.GE.covRxnA.mvfderiv_F_rmFrameField
import Submission.Work.Diff.GE.covRxnA.pairing_le
import Submission.Work.Diff.GE.covRxnA.quad_cauchy
import Submission.Work.Diff.GE.Rfa.reactionFormAtE_frame_indep
import Submission.Work.Diff.GE.RL.covRm_linear_fst

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The derivative bound for the quadratic reaction `F(Rm)`

This file proves `Work.Diff.GE.covReactionFormAt_le`: for a `C^∞`, `rot`-equivariant
`F : Curv4 n → Curv4 n` which is quadratic at infinity with `‖fderiv ℝ F R‖ ≤ CF' ‖R‖`, the
`Ext`-pattern covariant derivative `covReactionFormAt F` of the `(0,4)`-tensor `y ↦ F (Rm y)`
satisfies

`covReactionFormAt F g x v a b c d ≤ C |Rm| |∇Rm| ‖v‖‖a‖‖b‖‖c‖‖d‖`.

## Structure of the proof

1. `reactionFormAtE` is the reaction form evaluated in an *explicit* frame `e`.  By definition
   `reactionFormAt F g x = reactionFormAtE F g x (onFrame g x)`.

2. **Frame independence** (`reactionFormAtE_frame_indep`): if `F` commutes with `rot A` for
   orthogonal `A`, then `reactionFormAtE F g x e` does not depend on the orthonormal frame `e`.
   This is what makes `y ↦ reactionFormAt F g y (...)` a *smooth* function of `y` although
   `onFrame g y` is chosen by `Classical.epsilon`: it equals the same expression in any smooth
   orthonormal frame field.

3. **The value of `covReactionFormAt`**: evaluating in a *geodesic* orthonormal frame
   `W` at `x` (`kato_geodesic_frame`: `∇_{W m x} W j = 0`), all frame-derivative terms and all
   slot corrections vanish in the `Ext` pattern, and the chain rule gives
   `covReactionFormAt F g x v a b c d = ∑ aᵢbⱼcₖdₗ (fderiv ℝ F (Rm) (∇Rm))ᵢⱼₖₗ`,
   where `∇Rm` is the curvature derivative array `dRmArrayAt g x v`.

4. **The bound** (`reactionPairing_le`): the four-fold contraction of an array with the frame
   components of four vectors is bounded by the `ℓ²` norm of the array times the product of the
   norms, and `|fderiv ℝ F R| ≤ CF' |R|`, `|∇Rm| ≤ √|∇Rm|²` give the estimate.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.GE.EvolB

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The reaction form `y ↦ F(Rm(y))` evaluated on four vectors, computed in an *explicit* frame
`e` at `x`: `∑ᵢⱼₖₗ (⟨eᵢ,a⟩⟨eⱼ,b⟩⟨eₖ,c⟩⟨eₗ,d⟩) · F(rmFrame g x e)ᵢⱼₖₗ`.  For an orthonormal `e`
this is the value of `reactionFormAt F g x a b c d`. -/
noncomputable def reactionFormAtE
    (F : Curv4 (Module.finrank ℝ E) → Curv4 (Module.finrank ℝ E)) (g : SMet I M) (x : M)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x) (a b c d : TangentSpace I x) : ℝ :=
  ∑ i, ∑ j, ∑ k, ∑ l,
    (g.inner x (e i) a * g.inner x (e j) b * g.inner x (e k) c * g.inner x (e l) d)
      * (F (rmFrame g x e)) i j k l

/-- `reactionFormAt` is `reactionFormAtE` computed in the chosen frame `onFrame g x`. -/
lemma reactionFormAt_eq_reactionFormAtE
    (F : Curv4 (Module.finrank ℝ E) → Curv4 (Module.finrank ℝ E)) (g : SMet I M) (x : M)
    (a b c d : TangentSpace I x) :
    reactionFormAt F g x a b c d = reactionFormAtE F g x (onFrame g x) a b c d := rfl

/-- The reaction form evaluated in a frame *field* `W`, as a function of the base point. -/
noncomputable def reactionPhi
    (F : Curv4 (Module.finrank ℝ E) → Curv4 (Module.finrank ℝ E)) (g : SMet I M)
    (W : Π y : M, Fin (Module.finrank ℝ E) → TangentSpace I y)
    (A B C D : Π y : M, TangentSpace I y) (y : M) : ℝ :=
  reactionFormAtE F g y (W y) (A y) (B y) (C y) (D y)

/-- The array of components of `∇Rm` at `x` in the direction `v`, in the chosen frame. -/
noncomputable def dRmArrayAt (g : SMet I M) (x : M) (v : TangentSpace I x) :
    Curv4 (Module.finrank ℝ E) :=
  fun i j k l => covRm g x v (onFrame g x i) (onFrame g x j) (onFrame g x k) (onFrame g x l)

/-- The four-fold contraction of a curvature array `X` with the frame components of four vectors. -/
noncomputable def reactionPairing (g : SMet I M) (x : M)
    (a b c d : TangentSpace I x) (X : Curv4 (Module.finrank ℝ E)) : ℝ :=
  ∑ i, ∑ j, ∑ k, ∑ l,
    (g.inner x (onFrame g x i) a * g.inner x (onFrame g x j) b * g.inner x (onFrame g x k) c
      * g.inner x (onFrame g x l) d) * X i j k l

/-- Nonnegativity of the metric pairing of a vector with itself. -/
theorem smet_inner_self_nonneg (g : SMet I M) (x : M) (v : TangentSpace I x) :
    0 ≤ g.inner x v v := by
  rcases eq_or_ne v 0 with h | h
  · subst h; simp
  · exact le_of_lt (g.pos x v h)


/-! ## Bridges to the parallel developments

`reactionFormAtE`, `reactionPairing`, `dRmArrayAt` are definitionally the same as
`Work.Diff.GE.Rfa.reactionFormAtE`, `Work.Diff.GE.Rxn.pairing` and `Work.Diff.GE.Rxn.dRmArr`; the
bridging step is `rfl`. -/

lemma reactionFormAtE_eq_Rfa (F : Curv4 (Module.finrank ℝ E) → Curv4 (Module.finrank ℝ E))
    (g : SMet I M) (x : M) (e : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (a b c d : TangentSpace I x) :
    reactionFormAtE F g x e a b c d = Rfa.reactionFormAtE F g x e a b c d := rfl

/-! ## Frame independence of the reaction form (in the `∞`-smoothness setting of this file) -/

variable {n : ℕ}

private noncomputable def outer4 (B C D E : Fin n → ℝ) : Curv4 n :=
  fun a b c d => B a * C b * D c * E d

/-- `rot A` is multiplicative on the outer product `B ⊗ C ⊗ D ⊗ E`: the transformed array is the
outer product of the four `A`-transformed coefficient vectors. -/
private theorem rot_outer4 (A : Matrix (Fin n) (Fin n) ℝ) (B C D E : Fin n → ℝ)
    (i j k l : Fin n) :
    rot A (outer4 B C D E) i j k l
      = (∑ a, A i a * B a) * (∑ b, A j b * C b) * (∑ c, A k c * D c)
        * (∑ d, A l d * E d) := by
  have key : (∑ a, A i a * B a) * (∑ b, A j b * C b) * (∑ c, A k c * D c)
        * (∑ d, A l d * E d)
      = ∑ a, ∑ b, ∑ c, ∑ d, A i a * A j b * A k c * A l d * (B a * C b * D c * E d) := by
    have h1 : (∑ a, A i a * B a) * (∑ b, A j b * C b)
        = ∑ a, ∑ b, (A i a * B a) * (A j b * C b) := Finset.sum_mul_sum _ _ _ _
    have h2 : (∑ a, ∑ b, (A i a * B a) * (A j b * C b)) * (∑ c, A k c * D c)
        = ∑ a, ∑ b, ∑ c, (A i a * B a) * (A j b * C b) * (A k c * D c) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl; intro a _
      rw [Finset.sum_mul_sum]
    have h3 : (∑ a, ∑ b, ∑ c, (A i a * B a) * (A j b * C b) * (A k c * D c))
          * (∑ d, A l d * E d)
        = ∑ a, ∑ b, ∑ c, ∑ d,
            (A i a * B a) * (A j b * C b) * (A k c * D c) * (A l d * E d) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl; intro a _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl; intro b _
      rw [Finset.sum_mul_sum]
    rw [h1, h2, h3]
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    apply Finset.sum_congr rfl; intro c _
    apply Finset.sum_congr rfl; intro d _
    ring
  rw [key]
  simp only [rot, outer4]

/-- **Algebraic contraction identity for `rot`.**  For an orthogonal `A`, contracting `rot A X` with
the four `A`-transformed coefficient vectors is the same as contracting `X` with the original
coefficient vectors. -/
private theorem rot_vec_contract (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ Matrix.orthogonalGroup (Fin n) ℝ) (B C D E : Fin n → ℝ) (X : Curv4 n) :
    (∑ i, ∑ j, ∑ k, ∑ l,
        (∑ a, A i a * B a) * (∑ b, A j b * C b) * (∑ c, A k c * D c)
          * (∑ d, A l d * E d) * rot A X i j k l)
      = ∑ a, ∑ b, ∑ c, ∑ d, B a * C b * D c * E d * X a b c d := by
  have h1 : (∑ i, ∑ j, ∑ k, ∑ l,
        (∑ a, A i a * B a) * (∑ b, A j b * C b) * (∑ c, A k c * D c)
          * (∑ d, A l d * E d) * rot A X i j k l)
      = ∑ i, ∑ j, ∑ k, ∑ l, rot A (outer4 B C D E) i j k l * rot A X i j k l := by
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro k _
    apply Finset.sum_congr rfl; intro l _
    rw [rot_outer4 A B C D E i j k l]
  rw [h1, Work.Diff.GE.rot_pair A hA (outer4 B C D E) X]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  apply Finset.sum_congr rfl; intro c _
  apply Finset.sum_congr rfl; intro d _
  simp only [outer4]

/-! ## Frame independence -/

/-- **Frame independence of the reaction form**: for `F` commuting with the orthogonal action
`rot A`, the value `reactionFormAtE F g x e a b c d` is the same for all orthonormal frames `e` of
`g` at `x`. -/
theorem reactionFormAtE_frame_indep
    [T2Space M]
    (hLC : LCSmooth I M)
    (F : Curv4 (Module.finrank ℝ E) → Curv4 (Module.finrank ℝ E))
    (hFeq : ∀ A ∈ Matrix.orthogonalGroup (Fin (Module.finrank ℝ E)) ℝ,
      ∀ R : Curv4 (Module.finrank ℝ E), F (rot A R) = rot A (F R))
    (g : SMet I M) (x : M) (e e' : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (he : IsONFrame g x e) (he' : IsONFrame g x e') (a b c d : TangentSpace I x) :
    reactionFormAtE F g x e' a b c d = reactionFormAtE F g x e a b c d := by
  obtain ⟨A, hA, hAe⟩ := onFrame_orthogonal_change g x e e' he he'
  have hrm : rmFrame g x e' = rot A (rmFrame g x e) := rmFrame_eq_rot hLC g x e e' A hAe
  have hF : F (rmFrame g x e') = rot A (F (rmFrame g x e)) := by
    rw [hrm, hFeq A hA]
  have hinner : ∀ (c : TangentSpace I x) (i : Fin (Module.finrank ℝ E)),
      g.inner x (e' i) c = ∑ j, A i j * g.inner x (e j) c := by
    intro c i
    rw [hAe i]
    simp only [map_sum, sum_apply, map_smul, smul_apply, smul_eq_mul]
  simp only [reactionFormAtE]
  rw [hF]
  simp only [hinner]
  exact rot_vec_contract A hA (fun j => g.inner x (e j) a) (fun j => g.inner x (e j) b)
    (fun j => g.inner x (e j) c) (fun j => g.inner x (e j) d) (F (rmFrame g x e))

/-! ## Bookkeeping lemmas for the assembly (moved here from the parallel assembly file
`Submission/Work/Diff/GE/covReactionFormAt_le_A.lean`, renamed to avoid any clash) -/

theorem covRn_mvfderiv_inner_lc (g : SMet I M) (x : M) (v : TangentSpace I x)
    {Y Z : Π y : M, TangentSpace I y} (hY : Work.Diff.GE.Rxn.SmoothField Y)
      (hZ : Work.Diff.GE.Rxn.SmoothField Z) :
    mvfderiv I (fun y : M => g.inner y (Y y) (Z y)) x v
      = g.inner x (lcOf g Y x v) (Z x) + g.inner x (Y x) (lcOf g Z x v) := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  have key : mvfderiv I (fun y : M => Inner.inner ℝ (Y y) (Z y)) x v
      = Inner.inner ℝ (lcOf g Y x v) (Z x) + Inner.inner ℝ (Y x) (lcOf g Z x v) := by
    have hY' : MDiffAt (T% Y) x := hY.contMDiffAt.mdifferentiableAt (by simp)
    have hZ' : MDiffAt (T% Z) x := hZ.contMDiffAt.mdifferentiableAt (by simp)
    have h' := (CovariantDerivative.isMetricCompatible_leviCivitaConnection (I := I) (M := M))
      |>.mvfderiv_inner_eq (σ := Y) (τ := Z) (fun _ : M => v) hY' hZ'
    simpa only [lcOf] using h'
  change mvfderiv I (fun y : M => Inner.inner ℝ (Y y) (Z y)) x v
      = Inner.inner ℝ (lcOf g Y x v) (Z x) + Inner.inner ℝ (Y x) (lcOf g Z x v)
  exact key

/-- **The `Ext` pattern on arbitrary smooth fields.**  The derivative of
`y ↦ rmP g y (A y) (B y) (C y) (D y)` is the value of `∇Rm` at `x` plus the four connection
corrections: the `Ext` pattern computes `∇Rm` and depends only on the values at `x`. -/

theorem covRn_curv4_norm_bounds {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (X : Curv4 (Module.finrank ℝ E)) :
    ‖X‖ ≤ Real.sqrt (∑ i, ∑ j, ∑ k, ∑ l, (X i j k l) ^ 2) ∧
      Real.sqrt (∑ i, ∑ j, ∑ k, ∑ l, (X i j k l) ^ 2)
        ≤ (Module.finrank ℝ E : ℝ) ^ 2 * ‖X‖ := by
  set S := ∑ i, ∑ j, ∑ k, ∑ l, (X i j k l) ^ 2 with hS
  have hSnn : 0 ≤ S := by
    rw [hS]
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun l _ => sq_nonneg _
  have hterm : ∀ i j k l, (X i j k l) ^ 2 ≤ S := by
    intro i j k l
    rw [hS]
    have h1 : (X i j k l) ^ 2 ≤ ∑ l', (X i j k l') ^ 2 :=
      Finset.single_le_sum (fun a _ => sq_nonneg _) (Finset.mem_univ l)
    have h2 : (∑ l', (X i j k l') ^ 2) ≤ ∑ k', ∑ l', (X i j k' l') ^ 2 :=
      Finset.single_le_sum (fun a _ => Finset.sum_nonneg fun b _ => sq_nonneg _)
        (Finset.mem_univ k)
    have h3 : (∑ k', ∑ l', (X i j k' l') ^ 2) ≤ ∑ j', ∑ k', ∑ l', (X i j' k' l') ^ 2 :=
      Finset.single_le_sum (fun a _ => Finset.sum_nonneg fun b _ =>
        Finset.sum_nonneg fun c _ => sq_nonneg _) (Finset.mem_univ j)
    have h4 : (∑ j', ∑ k', ∑ l', (X i j' k' l') ^ 2)
        ≤ ∑ i', ∑ j', ∑ k', ∑ l', (X i' j' k' l') ^ 2 :=
      Finset.single_le_sum (fun a _ => Finset.sum_nonneg fun b _ =>
        Finset.sum_nonneg fun c _ => Finset.sum_nonneg fun d _ => sq_nonneg _)
        (Finset.mem_univ i)
    exact h1.trans (h2.trans (h3.trans h4))
  constructor
  · refine pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _) |>.mpr fun i => ?_
    refine pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _) |>.mpr fun j => ?_
    refine pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _) |>.mpr fun k => ?_
    refine pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _) |>.mpr fun l => ?_
    rw [Real.norm_eq_abs, Real.le_sqrt (abs_nonneg _) hSnn, sq_abs]
    exact hterm i j k l
  · have hle : S ≤ (Module.finrank ℝ E : ℝ) ^ 4 * ‖X‖ ^ 2 := by
      rw [hS]
      calc ∑ i, ∑ j, ∑ k, ∑ l, (X i j k l) ^ 2
          ≤ ∑ i, ∑ j, ∑ k, ∑ l, ‖X‖ ^ 2 := by
            refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
              Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ => ?_
            have h1 : ‖X i j k l‖ ≤ ‖X‖ :=
              (norm_le_pi_norm (X i j k) l).trans ((norm_le_pi_norm (X i j) k).trans
                ((norm_le_pi_norm (X i) j).trans (norm_le_pi_norm X i)))
            have h2 : (X i j k l) ^ 2 = ‖X i j k l‖ ^ 2 := by
              rw [Real.norm_eq_abs, sq_abs]
            rw [h2]
            simpa only [sq] using mul_le_mul h1 h1 (norm_nonneg _) (norm_nonneg _)
        _ = (Module.finrank ℝ E : ℝ) ^ 4 * ‖X‖ ^ 2 := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            ring
    calc Real.sqrt S ≤ Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 4 * ‖X‖ ^ 2) :=
          Real.sqrt_le_sqrt hle
      _ = (Module.finrank ℝ E : ℝ) ^ 2 * ‖X‖ := by
          rw [show (Module.finrank ℝ E : ℝ) ^ 4 * ‖X‖ ^ 2
                = ((Module.finrank ℝ E : ℝ) ^ 2 * ‖X‖) ^ 2 by ring]
          rw [Real.sqrt_sq (by positivity)]

/-! ## Bookkeeping lemmas for the assembly -/

/-- The product rule for a product of four smooth real functions. -/

theorem covRn_mvfderiv_prod4 [T2Space M] (f₁ f₂ f₃ f₄ : M → ℝ) (h₁ : CMDiff ∞ f₁) (h₂ : CMDiff ∞ f₂)
    (h₃ : CMDiff ∞ f₃) (h₄ : CMDiff ∞ f₄) (x : M) (v : TangentSpace I x) :
    mvfderiv I (fun y : M => f₁ y * f₂ y * f₃ y * f₄ y) x v
      = f₂ x * f₃ x * f₄ x * mvfderiv I f₁ x v + f₁ x * f₃ x * f₄ x * mvfderiv I f₂ x v
        + f₁ x * f₂ x * f₄ x * mvfderiv I f₃ x v
        + f₁ x * f₂ x * f₃ x * mvfderiv I f₄ x v := by
  have h12 : CMDiff ∞ (fun y : M => f₁ y * f₂ y) := h₁.mul h₂
  have h123 : CMDiff ∞ (fun y : M => f₁ y * f₂ y * f₃ y) := h12.mul h₃
  have e1 := Work.Diff.GE.Gest.mvfderiv_mul_apply (I := I) (M := M)
    (u := fun y : M => f₁ y * f₂ y * f₃ y) (v := f₄) h123 h₄ x v
  have e2 := Work.Diff.GE.Gest.mvfderiv_mul_apply (I := I) (M := M)
    (u := fun y : M => f₁ y * f₂ y) (v := f₃) h12 h₃ x v
  have e3 := Work.Diff.GE.Gest.mvfderiv_mul_apply (I := I) (M := M)
    (u := f₁) (v := f₂) h₁ h₂ x v
  rw [e1, e2, e3]
  ring

/-- Chain rule over a quadruple finite sum of products. -/

theorem covRn_mvfderiv_sum4_prod [T2Space M] {ι : Type*} [Fintype ι]
    (C E : ι → ι → ι → ι → M → ℝ) (hC : ∀ i j k l, CMDiff ∞ (C i j k l))
    (hE : ∀ i j k l, CMDiff ∞ (E i j k l)) (x : M) (v : TangentSpace I x) :
    mvfderiv I (fun y : M => ∑ i, ∑ j, ∑ k, ∑ l, C i j k l y * E i j k l y) x v
      = ∑ i, ∑ j, ∑ k, ∑ l, (C i j k l x * mvfderiv I (E i j k l) x v
          + E i j k l x * mvfderiv I (C i j k l) x v) := by
  have h4 : ∀ i j k, CMDiff ∞ (fun y : M => ∑ l, C i j k l y * E i j k l y) :=
    fun i j k => ContMDiff.sum fun l _ => (hC i j k l).mul (hE i j k l)
  have h3 : ∀ i j, CMDiff ∞ (fun y : M => ∑ k, ∑ l, C i j k l y * E i j k l y) :=
    fun i j => ContMDiff.sum fun k _ => h4 i j k
  have h2 : ∀ i, CMDiff ∞ (fun y : M => ∑ j, ∑ k, ∑ l, C i j k l y * E i j k l y) :=
    fun i => ContMDiff.sum fun j _ => h3 i j
  rw [Work.Diff.GE.Kato3.mvfderiv_sum (Finset.univ : Finset ι)
    (fun i y => ∑ j, ∑ k, ∑ l, C i j k l y * E i j k l y) (fun i => h2 i) x v]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Work.Diff.GE.Kato3.mvfderiv_sum (Finset.univ : Finset ι)
    (fun j y => ∑ k, ∑ l, C i j k l y * E i j k l y) (fun j => h3 i j) x v]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Work.Diff.GE.Kato3.mvfderiv_sum (Finset.univ : Finset ι)
    (fun k y => ∑ l, C i j k l y * E i j k l y) (fun k => h4 i j k) x v]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Work.Diff.GE.Kato3.mvfderiv_sum (Finset.univ : Finset ι)
    (fun l y => C i j k l y * E i j k l y) (fun l => (hC i j k l).mul (hE i j k l)) x v]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Work.Diff.GE.Gest.mvfderiv_mul_apply (I := I) (M := M) (u := C i j k l)
    (v := E i j k l) (hC i j k l) (hE i j k l) x v]

/-- Distributing the four-term derivative of a product inside a quadruple sum. -/

theorem covRn_sum_prod4_deriv {ι : Type*} [Fintype ι]
    (X : ι → ι → ι → ι → ℝ) (P1 P2 P3 P4 dP1 dP2 dP3 dP4 : ι → ℝ) :
    (∑ i, ∑ j, ∑ k, ∑ l, X i j k l * (P2 j * P3 k * P4 l * dP1 i + P1 i * P3 k * P4 l * dP2 j
        + P1 i * P2 j * P4 l * dP3 k + P1 i * P2 j * P3 k * dP4 l))
      = (∑ i, ∑ j, ∑ k, ∑ l, (dP1 i * P2 j * P3 k * P4 l) * X i j k l)
        + (∑ i, ∑ j, ∑ k, ∑ l, (P1 i * dP2 j * P3 k * P4 l) * X i j k l)
        + (∑ i, ∑ j, ∑ k, ∑ l, (P1 i * P2 j * dP3 k * P4 l) * X i j k l)
        + (∑ i, ∑ j, ∑ k, ∑ l, (P1 i * P2 j * P3 k * dP4 l) * X i j k l) := by
  have h : ∀ i j k l, X i j k l * (P2 j * P3 k * P4 l * dP1 i + P1 i * P3 k * P4 l * dP2 j
        + P1 i * P2 j * P4 l * dP3 k + P1 i * P2 j * P3 k * dP4 l)
      = (dP1 i * P2 j * P3 k * P4 l) * X i j k l + (P1 i * dP2 j * P3 k * P4 l) * X i j k l
        + (P1 i * P2 j * dP3 k * P4 l) * X i j k l
        + (P1 i * P2 j * P3 k * dP4 l) * X i j k l := by
    intro i j k l; ring
  rw [show (∑ i, ∑ j, ∑ k, ∑ l, X i j k l * (P2 j * P3 k * P4 l * dP1 i
        + P1 i * P3 k * P4 l * dP2 j + P1 i * P2 j * P4 l * dP3 k + P1 i * P2 j * P3 k * dP4 l))
      = ∑ i, ∑ j, ∑ k, ∑ l, ((dP1 i * P2 j * P3 k * P4 l) * X i j k l
        + (P1 i * dP2 j * P3 k * P4 l) * X i j k l + (P1 i * P2 j * dP3 k * P4 l) * X i j k l
        + (P1 i * P2 j * P3 k * dP4 l) * X i j k l) from
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => h i j k l]
  simp only [Finset.sum_add_distrib]

/-- `covRm` is `ℝ`-linear in its *direction* argument, finite-sum form. -/
theorem covRm_sum_dir [T2Space M] (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    {ι : Type*} (t : Finset ι) (c : ι → ℝ) (e : ι → TangentSpace I x)
    (a b cc d : TangentSpace I x) :
    covRm g x (∑ m ∈ t, c m • e m) a b cc d
      = ∑ m ∈ t, c m * covRm g x (e m) a b cc d := by
  classical
  have hlin : RL.CovRmLinFst g := RL.covRm_linear_fst (I := I) (M := M) hLC g
  induction t using Finset.induction_on with
  | empty => simpa using hlin x 0 0 (0 : TangentSpace I x) (0 : TangentSpace I x) a b cc d
  | insert i t hi ih =>
      have hstep := hlin x (c i) 1 (e i) (∑ m ∈ t, c m • e m) a b cc d
      rw [one_smul] at hstep
      rw [Finset.sum_insert hi, Finset.sum_insert hi, hstep, ih]
      simp

/-- Parseval's identity for the frame coefficients of a `g`-orthonormal frame. -/
theorem sum_sq_inner_of_isONFrame [T2Space M] (g : SMet I M) (x : M)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x) (he : IsONFrame g x e)
    (u : TangentSpace I x) :
    ∑ i, (g.inner x (e i) u) ^ 2 = g.inner x u u := by
  classical
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  rcases Nat.eq_zero_or_pos (Module.finrank ℝ E) with h0 | hpos
  · haveI : Subsingleton (TangentSpace I x) := by
      rw [← Module.finrank_zero_iff (R := ℝ) (M := TangentSpace I x)]; exact h0
    have hu : u = 0 := Subsingleton.elim u 0
    have hzero : ∀ i : Fin (Module.finrank ℝ E), (g.inner x (e i) u) ^ 2 = 0 := by
      intro i; rw [hu]; simp
    rw [Finset.sum_eq_zero (fun i _ => hzero i), hu]
    simp
  · have hexp : (∑ i, g.inner x (e i) u • e i) = u :=
      Work.Diff.GE.sum_inner_smul_eq_self g x hpos e he u
    have h1 : ∀ a : TangentSpace I x, g.inner x a (∑ j, g.inner x (e j) u • e j)
          = ∑ j, g.inner x (e j) u * g.inner x a (e j) := by
      intro a
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, smul_eq_mul]
    have h2 : g.inner x u (∑ j, g.inner x (e j) u • e j)
        = ∑ j, g.inner x (e j) u * g.inner x (e j) u := by
      rw [h1 u]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [g.symm x u (e j)]
    calc ∑ i, (g.inner x (e i) u) ^ 2
        = ∑ i, g.inner x (e i) u * g.inner x (e i) u := by
          refine Finset.sum_congr rfl fun i _ => by ring
      _ = g.inner x u u := by rw [← h2, hexp]

/-- The `ℓ²` norm of the array of components of `∇Rm` in the direction `v` is bounded by
`|v| √|∇Rm|²`. -/
theorem sqrt_sum_dRmArrayAt_sq_le [T2Space M] (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (v : TangentSpace I x) :
    Real.sqrt (∑ i, ∑ j, ∑ k, ∑ l, (dRmArrayAt g x v i j k l) ^ 2)
      ≤ Real.sqrt (g.inner x v v) * Real.sqrt (dRmNormSq g x) := by
  classical
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  set e : Fin (Module.finrank ℝ E) → TangentSpace I x := onFrame g x with he
  have heON : IsONFrame g x e := isONFrame_onFrame g x
  rcases Nat.eq_zero_or_pos (Module.finrank ℝ E) with h0 | hpos
  · haveI : IsEmpty (Fin (Module.finrank ℝ E)) := by
      rw [← Fintype.card_eq_zero_iff, Fintype.card_fin]; exact h0
    have hsum0 : (∑ i : Fin (Module.finrank ℝ E), ∑ j, ∑ k, ∑ l,
        (dRmArrayAt g x v i j k l) ^ 2) = 0 := by
      rw [Finset.univ_eq_empty, Finset.sum_empty]
    rw [hsum0, Real.sqrt_zero]
    exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  · have hexp : (∑ m, g.inner x (e m) v • e m) = v :=
      Work.Diff.GE.sum_inner_smul_eq_self g x hpos e heON v
    have hkey : ∀ i j k l, dRmArrayAt g x v i j k l
        = ∑ m, (g.inner x (e m) v) * covRm g x (e m) (e i) (e j) (e k) (e l) := by
      intro i j k l
      simp only [dRmArrayAt]
      rw [← he]
      rw [show covRm g x v (e i) (e j) (e k) (e l)
          = covRm g x (∑ m, (g.inner x (e m) v) • e m) (e i) (e j) (e k) (e l) from by
        rw [hexp]]
      simpa using covRm_sum_dir (I := I) (M := M) hLC g x Finset.univ
        (fun m => g.inner x (e m) v) e (e i) (e j) (e k) (e l)
    have hcs := covRxnA.quad_cauchy (κ := Fin (Module.finrank ℝ E))
      (fun m => g.inner x (e m) v)
      (fun m i j k l => covRm g x (e m) (e i) (e j) (e k) (e l))
    have hpar := sum_sq_inner_of_isONFrame (I := I) (M := M) g x e heON v
    have hdRm : (∑ m, ∑ i, ∑ j, ∑ k, ∑ l,
        (covRm g x (e m) (e i) (e j) (e k) (e l)) ^ 2) = dRmNormSq g x := rfl
    have hle : (∑ i, ∑ j, ∑ k, ∑ l, (dRmArrayAt g x v i j k l) ^ 2)
        ≤ (g.inner x v v) * (dRmNormSq g x) := by
      calc (∑ i, ∑ j, ∑ k, ∑ l, (dRmArrayAt g x v i j k l) ^ 2)
          = ∑ i, ∑ j, ∑ k, ∑ l,
              (∑ m, (g.inner x (e m) v) * covRm g x (e m) (e i) (e j) (e k) (e l)) ^ 2 := by
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
              Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
            rw [hkey i j k l]
        _ ≤ (∑ m, (g.inner x (e m) v) ^ 2)
              * (∑ m, ∑ i, ∑ j, ∑ k, ∑ l,
                  (covRm g x (e m) (e i) (e j) (e k) (e l)) ^ 2) := hcs
        _ = (g.inner x v v) * (dRmNormSq g x) := by rw [hpar, hdRm]
    calc Real.sqrt (∑ i, ∑ j, ∑ k, ∑ l, (dRmArrayAt g x v i j k l) ^ 2)
        ≤ Real.sqrt ((g.inner x v v) * (dRmNormSq g x)) := Real.sqrt_le_sqrt hle
      _ = Real.sqrt (g.inner x v v) * Real.sqrt (dRmNormSq g x) :=
          Real.sqrt_mul (smet_inner_self_nonneg g x v) (dRmNormSq g x)


/-! ## The value of the `Ext`-pattern covariant derivative of `F(Rm)` -/

/-- **The value of `covReactionFormAt`**: for `C^∞`, `rot`-equivariant `F`, the `Ext`-pattern
covariant derivative of `y ↦ F(Rm(y))` is the four-fold contraction of the array
`fderiv ℝ F (Rm) (∇Rm)` with the frame components of `a b c d`.  This is the chain rule for the
composition of `F` with the curvature tensor, together with the observation that the four
tensorialising slot corrections of the `Ext` pattern cancel the derivative of the four coefficient
pairings in a *geodesic* frame. -/
theorem covReactionFormAt_eq_pairing
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : LCSmooth I M)
    (F : Curv4 (Module.finrank ℝ E) → Curv4 (Module.finrank ℝ E))
    (hF : ContDiff ℝ ∞ F)
    (hE : ∀ A ∈ Matrix.orthogonalGroup (Fin (Module.finrank ℝ E)) ℝ,
      ∀ R : Curv4 (Module.finrank ℝ E), F (rot A R) = rot A (F R))
    (g : SMet I M) (x : M) (v a b c d : TangentSpace I x) :
    covReactionFormAt F g x v a b c d
      = reactionPairing g x a b c d (fderiv ℝ F (rmC g x) (dRmArrayAt g x v)) := by
  classical
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  -- a smooth orthonormal frame, geodesic at `x` and agreeing with `onFrame g x` there
  obtain ⟨W, hWs, hWON, hWx, hWgeo⟩ := Work.Diff.EXT.geodesic_frame_aux (I := I) (M := M) g x
  let V : Π y : M, Fin (Module.finrank ℝ E) → TangentSpace I y := fun y i => W i y
  have hVs : ∀ i, Rxn.SmoothField (fun y : M => V y i) := fun i => by
    have h := hWs i
    have h' : Work.Diff.EXT.SmoothF (fun y : M => V y i) := by simpa only [V] using h
    simpa only [Work.Diff.EXT.SmoothF, Rxn.SmoothField] using h'
  have hVON : ∀ᶠ y in 𝓝 x, IsONFrame g y (V y) := by simpa only [V] using hWON
  have hVx : ∀ i, V x i = onFrame g x i := fun i => by simpa only [V] using hWx i
  have hVONx : IsONFrame g x (V x) := mem_of_mem_nhds hVON
  have hVgeo : ∀ m j, lcOf g (fun y : M => V y j) x (V x m) = 0 := by
    intro m j; simpa only [V] using hWgeo m j
  -- smooth extensions of the four vectors
  let A : Π y : M, TangentSpace I y := smoothExt x a
  let B : Π y : M, TangentSpace I y := smoothExt x b
  let C : Π y : M, TangentSpace I y := smoothExt x c
  let D : Π y : M, TangentSpace I y := smoothExt x d
  have hAs : Rxn.SmoothField A := smoothExt_cmdiff x a
  have hBs : Rxn.SmoothField B := smoothExt_cmdiff x b
  have hCs : Rxn.SmoothField C := smoothExt_cmdiff x c
  have hDs : Rxn.SmoothField D := smoothExt_cmdiff x d
  have hAx : A x = a := smoothExt_apply x a
  have hBx : B x = b := smoothExt_apply x b
  have hCx : C x = c := smoothExt_apply x c
  have hDx : D x = d := smoothExt_apply x d
  -- the frame is geodesic in *every* direction
  have hVv : ∀ j, lcOf g (fun y : M => V y j) x v = 0 := by
    intro j
    rcases Nat.eq_zero_or_pos (Module.finrank ℝ E) with h0 | hpos
    · have hsub : Subsingleton (TangentSpace I x) := by
        rw [← Module.finrank_zero_iff (R := ℝ) (M := TangentSpace I x)]; exact h0
      rw [Subsingleton.elim v 0, map_zero]
    · conv_lhs => rw [← Work.Diff.GE.sum_inner_smul_eq_self g x hpos (V x) hVONx v]
      rw [map_sum]
      refine Finset.sum_eq_zero fun m _ => ?_
      rw [map_smul, hVgeo m j, smul_zero]
  -- `rmP g x` vanishes whenever one of its slots is zero
  have hrmP0 : ∀ b c d : TangentSpace I x, rmP g x (0 : TangentSpace I x) b c d = 0 := by
    intro b c d
    simpa using rmP_smul_fst (I := I) (M := M) g hLC x 0 (0 : TangentSpace I x) b c d
  have hrmP0' : ∀ a c d : TangentSpace I x, rmP g x a (0 : TangentSpace I x) c d = 0 := by
    intro a c d
    simpa using rmP_smul_snd (I := I) (M := M) g hLC x 0 a (0 : TangentSpace I x) c d
  have hrmP0'' : ∀ a b d : TangentSpace I x, rmP g x a b (0 : TangentSpace I x) d = 0 := by
    intro a b d
    simpa using rmP_smul_thd (I := I) (M := M) g hLC x 0 a b (0 : TangentSpace I x) d
  have hrmP0''' : ∀ a b c : TangentSpace I x, rmP g x a b c (0 : TangentSpace I x) = 0 := by
    intro a b c
    simpa using rmP_smul_fth (I := I) (M := M) g hLC x 0 a b c (0 : TangentSpace I x)
  -- smoothness of the curvature array and of `F` composed with it
  have hRsm : ContMDiff I (modelWithCornersSelf ℝ (Curv4 (Module.finrank ℝ E))) ∞
      (fun y : M => Rxn.rmFrameField g V y) := by
    rw [contMDiff_pi_space]; intro i
    rw [contMDiff_pi_space]; intro j
    rw [contMDiff_pi_space]; intro k
    rw [contMDiff_pi_space]; intro l
    exact rmP_fields_smooth (I := I) hLC g (hVs i) (hVs j) (hVs k) (hVs l)
  have hFc : ContMDiff (modelWithCornersSelf ℝ (Curv4 (Module.finrank ℝ E)))
      (modelWithCornersSelf ℝ (Curv4 (Module.finrank ℝ E))) ∞ F := hF.contMDiff
  have hFsm : ContMDiff I (modelWithCornersSelf ℝ (Curv4 (Module.finrank ℝ E))) ∞
      (fun y : M => F (Rxn.rmFrameField g V y)) := hFc.comp hRsm
  have hEfsm : ∀ i j k l, ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞
      (fun y : M => (F (Rxn.rmFrameField g V y)) i j k l) := by
    intro i j k l
    have h1 : ContMDiff I (modelWithCornersSelf ℝ
        (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ)) ∞
        (fun y : M => (F (Rxn.rmFrameField g V y)) i) :=
      (contMDiff_pi_space (φ := fun y : M => F (Rxn.rmFrameField g V y))).mp hFsm i
    have h2 : ContMDiff I (modelWithCornersSelf ℝ
        (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ)) ∞
        (fun y : M => (F (Rxn.rmFrameField g V y)) i j) :=
      (contMDiff_pi_space (φ := fun y : M => (F (Rxn.rmFrameField g V y)) i)).mp h1 j
    have h3 : ContMDiff I (modelWithCornersSelf ℝ (Fin (Module.finrank ℝ E) → ℝ)) ∞
        (fun y : M => (F (Rxn.rmFrameField g V y)) i j k) :=
      (contMDiff_pi_space (φ := fun y : M => (F (Rxn.rmFrameField g V y)) i j)).mp h2 k
    exact (contMDiff_pi_space (φ := fun y : M => (F (Rxn.rmFrameField g V y)) i j k)).mp h3 l
  -- the coefficient pairings
  let P₁ : Fin (Module.finrank ℝ E) → M → ℝ := fun i y => g.inner y (V y i) (A y)
  let P₂ : Fin (Module.finrank ℝ E) → M → ℝ := fun j y => g.inner y (V y j) (B y)
  let P₃ : Fin (Module.finrank ℝ E) → M → ℝ := fun k y => g.inner y (V y k) (C y)
  let P₄ : Fin (Module.finrank ℝ E) → M → ℝ := fun l y => g.inner y (V y l) (D y)
  have hP₁ : ∀ i, CMDiff ∞ (P₁ i) := fun i => by
    show CMDiff ∞ (fun y : M => Inner.inner ℝ (V y i) (A y))
    exact ContMDiff.inner_bundle (IB := I) (b := id) (v := fun y : M => V y i) (w := A)
      (hVs i) hAs
  have hP₂ : ∀ j, CMDiff ∞ (P₂ j) := fun j => by
    show CMDiff ∞ (fun y : M => Inner.inner ℝ (V y j) (B y))
    exact ContMDiff.inner_bundle (IB := I) (b := id) (v := fun y : M => V y j) (w := B)
      (hVs j) hBs
  have hP₃ : ∀ k, CMDiff ∞ (P₃ k) := fun k => by
    show CMDiff ∞ (fun y : M => Inner.inner ℝ (V y k) (C y))
    exact ContMDiff.inner_bundle (IB := I) (b := id) (v := fun y : M => V y k) (w := C)
      (hVs k) hCs
  have hP₄ : ∀ l, CMDiff ∞ (P₄ l) := fun l => by
    show CMDiff ∞ (fun y : M => Inner.inner ℝ (V y l) (D y))
    exact ContMDiff.inner_bundle (IB := I) (b := id) (v := fun y : M => V y l) (w := D)
      (hVs l) hDs
  let Cf : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Fin (Module.finrank ℝ E) → M → ℝ := fun i j k l y => P₁ i y * P₂ j y * P₃ k y * P₄ l y
  let Ef : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Fin (Module.finrank ℝ E) → M → ℝ := fun i j k l y => (F (Rxn.rmFrameField g V y)) i j k l
  have hCf : ∀ i j k l, CMDiff ∞ (Cf i j k l) := fun i j k l =>
    ((hP₁ i).mul (hP₂ j)).mul (hP₃ k) |>.mul (hP₄ l)
  have hEf : ∀ i j k l, CMDiff ∞ (Ef i j k l) := fun i j k l => by
    show ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞
      (fun y : M => (F (Rxn.rmFrameField g V y)) i j k l)
    exact hEfsm i j k l
  let Ψ : M → ℝ := fun y =>
    ∑ i, ∑ j, ∑ k, ∑ l, Cf i j k l y * Ef i j k l y
  let Φ : M → ℝ := fun y => reactionFormAt F g y (A y) (B y) (C y) (D y)
  -- germ equality: the (non-smooth) reaction is the frame-independent value
  have hgerm : Φ =ᶠ[𝓝 x] Ψ := by
    filter_upwards [hVON] with y hy
    have h2 := reactionFormAtE_frame_indep (I := I) (M := M) hLC F hE g y
      (onFrame g y) (V y) (isONFrame_onFrame g y) hy (A y) (B y) (C y) (D y)
    show reactionFormAt F g y (A y) (B y) (C y) (D y) = Ψ y
    rw [reactionFormAt_eq_reactionFormAtE, ← h2]
    rfl
  have hderiv : mvfderiv I Φ x v = mvfderiv I Ψ x v :=
    congrArg (fun L : TangentSpace I x →L[ℝ] ℝ => L v)
      (mvfderiv_congr_eventuallyEq (I := I) hgerm)
  -- the definition of `covReactionFormAt`
  have hcov : covReactionFormAt F g x v a b c d
      = mvfderiv I Φ x v - reactionFormAt F g x (lcOf g A x v) b c d
        - reactionFormAt F g x a (lcOf g B x v) c d
        - reactionFormAt F g x a b (lcOf g C x v) d
        - reactionFormAt F g x a b c (lcOf g D x v) := by
    simp only [covReactionFormAt, Φ, A, B, C, D]
  -- the array derivative is `∇Rm`
  have hY : mvfderiv I (fun y : M => Rxn.rmFrameField g V y) x v = Rxn.dRmArr g x v := by
    rw [Work.Diff.GE.covRxnA.mvfderiv_rmFrameField (I := I) (M := M) hLC g V hVs x v]
    funext i j k l
    simp only [Rxn.dRmArr]
    rw [hVv i, hVv j, hVv k, hVv l, hVx i, hVx j, hVx k, hVx l]
    simp only [hrmP0, hrmP0', hrmP0'', hrmP0''', add_zero]
  -- derivative of `F(Rm)`
  have hEfderiv : ∀ i j k l, mvfderiv I (Ef i j k l) x v
      = (fderiv ℝ F (Rxn.rmFrameField g V x) (Rxn.dRmArr g x v)) i j k l := by
    intro i j k l
    have h := covRxnA.mvfderiv_F_rmFrameField (I := I) (M := M) hLC F hF g V
      hVs x v i j k l
    rw [hY] at h
    exact h
  -- derivative of the coefficients
  have hP₁x : ∀ i, P₁ i x = g.inner x (onFrame g x i) a := by
    intro i; simp only [P₁, hVx i, hAx]
  have hP₂x : ∀ j, P₂ j x = g.inner x (onFrame g x j) b := by
    intro j; simp only [P₂, hVx j, hBx]
  have hP₃x : ∀ k, P₃ k x = g.inner x (onFrame g x k) c := by
    intro k; simp only [P₃, hVx k, hCx]
  have hP₄x : ∀ l, P₄ l x = g.inner x (onFrame g x l) d := by
    intro l; simp only [P₄, hVx l, hDx]
  have hdP₁ : ∀ i, mvfderiv I (P₁ i) x v = g.inner x (onFrame g x i) (lcOf g A x v) := by
    intro i
    have h := covRn_mvfderiv_inner_lc (I := I) (M := M) g x v (hVs i) hAs
    rw [hVv i, hVx i] at h
    simp only [map_zero, zero_apply, zero_add] at h
    simpa only [P₁] using h
  have hdP₂ : ∀ j, mvfderiv I (P₂ j) x v = g.inner x (onFrame g x j) (lcOf g B x v) := by
    intro j
    have h := covRn_mvfderiv_inner_lc (I := I) (M := M) g x v (hVs j) hBs
    rw [hVv j, hVx j] at h
    simp only [map_zero, zero_apply, zero_add] at h
    simpa only [P₂] using h
  have hdP₃ : ∀ k, mvfderiv I (P₃ k) x v = g.inner x (onFrame g x k) (lcOf g C x v) := by
    intro k
    have h := covRn_mvfderiv_inner_lc (I := I) (M := M) g x v (hVs k) hCs
    rw [hVv k, hVx k] at h
    simp only [map_zero, zero_apply, zero_add] at h
    simpa only [P₃] using h
  have hdP₄ : ∀ l, mvfderiv I (P₄ l) x v = g.inner x (onFrame g x l) (lcOf g D x v) := by
    intro l
    have h := covRn_mvfderiv_inner_lc (I := I) (M := M) g x v (hVs l) hDs
    rw [hVv l, hVx l] at h
    simp only [map_zero, zero_apply, zero_add] at h
    simpa only [P₄] using h
  have hCfderiv : ∀ i j k l, mvfderiv I (Cf i j k l) x v
      = P₂ j x * P₃ k x * P₄ l x * mvfderiv I (P₁ i) x v
        + P₁ i x * P₃ k x * P₄ l x * mvfderiv I (P₂ j) x v
        + P₁ i x * P₂ j x * P₄ l x * mvfderiv I (P₃ k) x v
        + P₁ i x * P₂ j x * P₃ k x * mvfderiv I (P₄ l) x v := by
    intro i j k l
    simpa only [Cf] using covRn_mvfderiv_prod4 (I := I) (M := M) (P₁ i) (P₂ j) (P₃ k) (P₄ l)
      (hP₁ i) (hP₂ j) (hP₃ k) (hP₄ l) x v
  -- derivative of `Ψ`
  have hΨ : mvfderiv I Ψ x v = ∑ i, ∑ j, ∑ k, ∑ l,
      (Cf i j k l x * mvfderiv I (Ef i j k l) x v
        + Ef i j k l x * mvfderiv I (Cf i j k l) x v) := by
    show mvfderiv I (fun y : M => ∑ i, ∑ j, ∑ k, ∑ l, Cf i j k l y * Ef i j k l y) x v = _
    exact covRn_mvfderiv_sum4_prod Cf Ef hCf hEf x v
  -- the first half: the contraction of `fderiv F (rmC)` with `∇Rm`
  have hrc : Rxn.rmFrameField g V x = rmC g x := by
    funext i j k l
    simp only [Rxn.rmFrameField, rmC, rmFrame, rmP, hVx]
  have hfirst : (∑ i, ∑ j, ∑ k, ∑ l, Cf i j k l x * mvfderiv I (Ef i j k l) x v)
      = Rxn.pairing g x a b c d (fderiv ℝ F (rmC g x) (Rxn.dRmArr g x v)) := by
    simp only [hEfderiv, hrc]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    simp only [Rxn.pairing, Cf, hP₁x i, hP₂x j, hP₃x k, hP₄x l]
  -- the second half: the four tensorialising corrections
  have hsecond : (∑ i, ∑ j, ∑ k, ∑ l, Ef i j k l x * mvfderiv I (Cf i j k l) x v)
      = reactionFormAt F g x (lcOf g A x v) b c d + reactionFormAt F g x a (lcOf g B x v) c d
        + reactionFormAt F g x a b (lcOf g C x v) d
        + reactionFormAt F g x a b c (lcOf g D x v) := by
    have hsplit : (∑ i, ∑ j, ∑ k, ∑ l, Ef i j k l x * mvfderiv I (Cf i j k l) x v)
        = ∑ i, ∑ j, ∑ k, ∑ l, Ef i j k l x * (P₂ j x * P₃ k x * P₄ l x * mvfderiv I (P₁ i) x v
            + P₁ i x * P₃ k x * P₄ l x * mvfderiv I (P₂ j) x v
            + P₁ i x * P₂ j x * P₄ l x * mvfderiv I (P₃ k) x v
            + P₁ i x * P₂ j x * P₃ k x * mvfderiv I (P₄ l) x v) := by
      simp only [hCfderiv]
    rw [hsplit, covRn_sum_prod4_deriv]
    have hrc : Rxn.rmFrameField g V x = rmC g x := by
      funext i j k l
      simp only [Rxn.rmFrameField, rmC, rmFrame, rmP, hVx]
    have e1 : (∑ i, ∑ j, ∑ k, ∑ l,
          (mvfderiv I (P₁ i) x v * P₂ j x * P₃ k x * P₄ l x) * Ef i j k l x)
        = reactionFormAt F g x (lcOf g A x v) b c d := by
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
        Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
      simp only [reactionFormAt, Ef, hrc, hdP₁ i, hP₂x j, hP₃x k, hP₄x l]
      try ring
    have e2 : (∑ i, ∑ j, ∑ k, ∑ l,
          (P₁ i x * mvfderiv I (P₂ j) x v * P₃ k x * P₄ l x) * Ef i j k l x)
        = reactionFormAt F g x a (lcOf g B x v) c d := by
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
        Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
      simp only [reactionFormAt, Ef, hrc, hP₁x i, hdP₂ j, hP₃x k, hP₄x l]
      try ring
    have e3 : (∑ i, ∑ j, ∑ k, ∑ l,
          (P₁ i x * P₂ j x * mvfderiv I (P₃ k) x v * P₄ l x) * Ef i j k l x)
        = reactionFormAt F g x a b (lcOf g C x v) d := by
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
        Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
      simp only [reactionFormAt, Ef, hrc, hP₁x i, hP₂x j, hdP₃ k, hP₄x l]
      try ring
    have e4 : (∑ i, ∑ j, ∑ k, ∑ l,
          (P₁ i x * P₂ j x * P₃ k x * mvfderiv I (P₄ l) x v) * Ef i j k l x)
        = reactionFormAt F g x a b c (lcOf g D x v) := by
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
        Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
      simp only [reactionFormAt, Ef, hrc, hP₁x i, hP₂x j, hP₃x k, hdP₄ l]
      try ring
    rw [e1, e2, e3, e4]
  -- putting the two halves together
  have hmain : covReactionFormAt F g x v a b c d
      = Rxn.pairing g x a b c d (fderiv ℝ F (rmC g x) (Rxn.dRmArr g x v)) := by
    rw [hcov, hderiv, hΨ]
    rw [show (∑ i, ∑ j, ∑ k, ∑ l, (Cf i j k l x * mvfderiv I (Ef i j k l) x v
        + Ef i j k l x * mvfderiv I (Cf i j k l) x v))
        = (∑ i, ∑ j, ∑ k, ∑ l, Cf i j k l x * mvfderiv I (Ef i j k l) x v)
          + (∑ i, ∑ j, ∑ k, ∑ l, Ef i j k l x * mvfderiv I (Cf i j k l) x v) from by
          simp only [Finset.sum_add_distrib]]
    rw [hfirst, hsecond]
    ring
  rw [hmain]
  rfl

/-- The one-sided contraction bound for `reactionPairing`. -/
theorem reactionPairing_le (g : SMet I M) (x : M) (a b c d : TangentSpace I x)
    (X : Curv4 (Module.finrank ℝ E)) :
    reactionPairing g x a b c d X
      ≤ Real.sqrt (∑ i, ∑ j, ∑ k, ∑ l, (X i j k l) ^ 2)
        * (Real.sqrt (g.inner x a a) * Real.sqrt (g.inner x b b)
          * Real.sqrt (g.inner x c c) * Real.sqrt (g.inner x d d)) := by
  have h := covRxnA.pairing_le (I := I) (M := M) g x a b c d X
  simpa only [reactionPairing, Rxn.pairing] using h

/-- Bound on the covariant derivative of the quadratic reaction tensor: for `C^∞`, `rot`-equivariant
`F : Curv4 n → Curv4 n` with `‖F R‖ ≤ CF ‖R‖²` and `‖fderiv ℝ F R‖ ≤ CF' ‖R‖`, the `Ext`-pattern
covariant derivative `covReactionFormAt F` of the `(0,4)`-tensor `y ↦ F (rmC g y)` along a Ricci flow
is bounded by a constant times `|Rm| |∇Rm|` and the metric norms of the five vectors.  This is the
estimate `|∇(F(Rm))| ≤ CF' |Rm| |∇Rm|` on the derivative of the quadratic reaction plus the bound on
the four tensorialising slot corrections.  Proof route: the equivariance makes `reactionFormAt F g`
a genuine tensor component expression (independent of the frame `onFrame g x`), so its `Ext` pattern
is the honest covariant derivative; replace the frame locally by a smooth orthonormal frame, apply
the chain rule to the smooth composition `y ↦ F (rmC g y)`, and use the two hypotheses on `F`
(the `so(n)`-valued connection term cancels precisely by equivariance); finally bound the four slot
corrections, which are of the same order. -/
theorem covReactionFormAt_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : LCSmooth I M) :
    ∀ (F : Submission.Diff.Alg.Curv4 (Module.finrank ℝ E) →
        Submission.Diff.Alg.Curv4 (Module.finrank ℝ E)),
      ContDiff ℝ ∞ F →
      (∃ CF : ℝ, 0 ≤ CF ∧ ∀ R : Submission.Diff.Alg.Curv4 (Module.finrank ℝ E),
        ‖F R‖ ≤ CF * ‖R‖ * ‖R‖) →
      (∃ CF' : ℝ, 0 ≤ CF' ∧ ∀ R : Submission.Diff.Alg.Curv4 (Module.finrank ℝ E),
        ‖fderiv ℝ F R‖ ≤ CF' * ‖R‖) →
      (∀ A ∈ Matrix.orthogonalGroup (Fin (Module.finrank ℝ E)) ℝ,
        ∀ R : Submission.Diff.Alg.Curv4 (Module.finrank ℝ E),
        F (Submission.Diff.Alg.rot A R) = Submission.Diff.Alg.rot A (F R)) →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (G : ℝ → SMet I M) (T : ℝ), IsRicciFlow G T →
        ∀ t ∈ Set.Ico 0 T, ∀ x : M, ∀ v a b c d : TangentSpace I x,
          Work.Diff.GE.covReactionFormAt F (G t) x v a b c d ≤
            C * Real.sqrt (rmNormSq (G t) x) * Real.sqrt (dRmNormSq (G t) x)
              * (Real.sqrt ((G t).inner x v v) * Real.sqrt ((G t).inner x a a)
                * Real.sqrt ((G t).inner x b b) * Real.sqrt ((G t).inner x c c)
                * Real.sqrt ((G t).inner x d d)) := by
  intro F hFdiff hF2 hF' hFeq
  obtain ⟨CF, hCF0, hCF⟩ := hF2
  obtain ⟨CF', hCF'0, hCF'⟩ := hF'
  refine ⟨(Module.finrank ℝ E : ℝ) ^ 2 * CF', mul_nonneg (sq_nonneg _) hCF'0, ?_⟩
  intro G T hG t ht x v a b c d
  set g : SMet I M := G t with hg
  rw [covReactionFormAt_eq_pairing (I := I) (M := M) hLC F hFdiff hFeq g x v a b c d]
  have hrm : ‖rmC g x‖ ≤ Real.sqrt (rmNormSq g x) := (covRn_curv4_norm_bounds (rmC g x)).1
  have hdv : ‖dRmArrayAt g x v‖ ≤ Real.sqrt (g.inner x v v) * Real.sqrt (dRmNormSq g x) := by
    refine ((covRn_curv4_norm_bounds (dRmArrayAt g x v)).1).trans ?_
    exact sqrt_sum_dRmArrayAt_sq_le (I := I) (M := M) hLC g x v
  have hop : ‖fderiv ℝ F (rmC g x) (dRmArrayAt g x v)‖
      ≤ (CF' * Real.sqrt (rmNormSq g x))
        * (Real.sqrt (g.inner x v v) * Real.sqrt (dRmNormSq g x)) := by
    refine (ContinuousLinearMap.le_opNorm (fderiv ℝ F (rmC g x)) (dRmArrayAt g x v)).trans ?_
    refine mul_le_mul ?_ hdv (norm_nonneg _) ?_
    · exact (hCF' (rmC g x)).trans (mul_le_mul_of_nonneg_left hrm hCF'0)
    · exact mul_nonneg hCF'0 (Real.sqrt_nonneg _)
  have hsq : Real.sqrt (∑ i, ∑ j, ∑ k, ∑ l,
        ((fderiv ℝ F (rmC g x) (dRmArrayAt g x v)) i j k l) ^ 2)
      ≤ (Module.finrank ℝ E : ℝ) ^ 2 * (CF' * Real.sqrt (rmNormSq g x)
          * (Real.sqrt (g.inner x v v) * Real.sqrt (dRmNormSq g x))) := by
    refine ((covRn_curv4_norm_bounds (fderiv ℝ F (rmC g x) (dRmArrayAt g x v))).2).trans ?_
    exact mul_le_mul_of_nonneg_left hop (sq_nonneg _)
  have hpair := reactionPairing_le g x a b c d (fderiv ℝ F (rmC g x) (dRmArrayAt g x v))
  have hPa : 0 ≤ Real.sqrt (g.inner x a a) * Real.sqrt (g.inner x b b)
      * Real.sqrt (g.inner x c c) * Real.sqrt (g.inner x d d) := by positivity
  calc reactionPairing g x a b c d (fderiv ℝ F (rmC g x) (dRmArrayAt g x v))
      ≤ Real.sqrt (∑ i, ∑ j, ∑ k, ∑ l,
            ((fderiv ℝ F (rmC g x) (dRmArrayAt g x v)) i j k l) ^ 2)
          * (Real.sqrt (g.inner x a a) * Real.sqrt (g.inner x b b)
            * Real.sqrt (g.inner x c c) * Real.sqrt (g.inner x d d)) := hpair
    _ ≤ ((Module.finrank ℝ E : ℝ) ^ 2 * (CF' * Real.sqrt (rmNormSq g x)
            * (Real.sqrt (g.inner x v v) * Real.sqrt (dRmNormSq g x))))
          * (Real.sqrt (g.inner x a a) * Real.sqrt (g.inner x b b)
            * Real.sqrt (g.inner x c c) * Real.sqrt (g.inner x d d)) :=
        mul_le_mul_of_nonneg_right hsq hPa
    _ = ((Module.finrank ℝ E : ℝ) ^ 2 * CF') * Real.sqrt (rmNormSq g x)
          * Real.sqrt (dRmNormSq g x)
          * (Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x a a)
            * Real.sqrt (g.inner x b b) * Real.sqrt (g.inner x c c)
            * Real.sqrt (g.inner x d d)) := by ring


end Work.Diff.GE.EvolB

namespace Work.Diff.GE.EvolB.covRxnRN

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! Notation-free wrappers for the statements of the delegated lemmas of this development.
Delegated statements are elaborated in a file that only gets plain imports and no `open scoped`
lines, so they may not use the scoped notations `T%`, `∞`, `𝓝`, `CMDiff` or `𝓘(·,·)`. -/

/-- The tangent field `X` is `C^∞`. -/
abbrev SmoothField (X : Π y : M, TangentSpace I y) : Prop := CMDiff ∞ (T% X)

/-- `θ : M → Π i, F i` is differentiable at `x`. -/
abbrev MDiffPi {ι : Type*} [Fintype ι] {F : ι → Type*} [∀ i, NormedAddCommGroup (F i)]
    [∀ i, NormedSpace ℝ (F i)] (θ : M → Π i, F i) (x : M) : Prop :=
  MDifferentiableAt I (𝓘(ℝ, Π i, F i)) θ x

/-- The tangent field `X` is `C^∞` at `x`. -/
abbrev SmoothFieldAt (X : Π y : M, TangentSpace I y) (x : M) : Prop :=
  ContMDiffAt I I.tangent ∞ (T% X) x

end Work.Diff.GE.EvolB.covRxnRN

