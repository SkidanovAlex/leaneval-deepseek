import Mathlib
import Submission.Work.Diff.GE.dRmPhi
import Submission.Work.Diff.GE.NablaRm
import Submission.Work.Diff.GE.Frame
import Submission.Work.Diff.GE.dRmPhi_slotA
import Submission.Work.Diff.GE.covRm_linear_thd
import Submission.Work.Diff.GE.covRm_linear_fth

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.GE

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## Linearity of `covRm` in each of its five arguments, in finite-sum form

`covRm g x v a b c d = (∇_v Rm)(a,b,c,d)` is the `(0,5)`-tensor `∇Rm` evaluated on five tangent
vectors, so it is linear in each argument.  The binary (two-term) linearity is available in the
workspace (`Work.Diff.GE.covRm_linear_snd`, `covRm_linear_thd`, `covRm_linear_fth` for the three
`rmP` slots `a b c`; the first slot `v` is proved here, since it is simply the additivity and
homogeneity of the defining `mvfderiv`/`lcOf` in their direction argument).

The finite-sum forms below are what the frame expansion of `covRm` uses.  The passage from the
binary form to the finite-sum form is the elementary `Finset` induction packaged once in
`linear_of_binary`. -/

/-- If `F : V → ℝ` is additive and homogeneous (i.e. two-term linear, as produced by the
`covRm_linear_*` lemmas), then it is linear on finite sums. -/
private lemma linear_of_binary {V : Type*} [AddCommMonoid V] [Module ℝ V] (F : V → ℝ)
    (hadd : ∀ x y : V, F (x + y) = F x + F y)
    (hsmul : ∀ (r : ℝ) (x : V), F (r • x) = r * F x)
    {ι : Type*} (s : Finset ι) (r : ι → ℝ) (z : ι → V) :
    F (∑ i ∈ s, r i • z i) = ∑ i ∈ s, r i * F (z i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have h0 := hsmul 0 (0 : V)
      simpa using h0
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, hadd, hsmul, ih]

/-! ### The first (direction) argument `v` -/

/-- Binary additivity of `covRm` in its first (direction) argument `v`. -/
private lemma covRm_add_fst (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (v₁ v₂ a b c d : TangentSpace I x) :
    covRm g x (v₁ + v₂) a b c d = covRm g x v₁ a b c d + covRm g x v₂ a b c d := by
  rw [covRm_eq_dRmPhi, covRm_eq_dRmPhi, covRm_eq_dRmPhi]
  simp only [dRmPhi]
  rw [map_add (mvfderiv I (fun y : M => rmP g y (smoothExt x a y) (smoothExt x b y)
        (smoothExt x c y) (smoothExt x d y)) x)]
  simp only [map_add, rmP_add_fst g hLC, rmP_add_snd g hLC, rmP_add_thd g hLC, rmP_add_fth g hLC]
  ring

/-- Binary homogeneity of `covRm` in its first (direction) argument `v`. -/
private lemma covRm_smul_fst (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (ρ : ℝ) (v a b c d : TangentSpace I x) :
    covRm g x (ρ • v) a b c d = ρ * covRm g x v a b c d := by
  rw [covRm_eq_dRmPhi, covRm_eq_dRmPhi]
  simp only [dRmPhi]
  rw [map_smul (mvfderiv I (fun y : M => rmP g y (smoothExt x a y) (smoothExt x b y)
        (smoothExt x c y) (smoothExt x d y)) x)]
  simp only [map_smul, smul_eq_mul, rmP_smul_fst g hLC, rmP_smul_snd g hLC, rmP_smul_thd g hLC,
    rmP_smul_fth g hLC]
  ring

/-! ### Finite-sum forms in the five arguments -/

/-- Finite-sum form of the linearity of `covRm` in its first (direction) argument `v`. -/
private lemma covRm_sum_fst (hLC : LCSmooth I M) (g : SMet I M) (x : M) {ι : Type*}
    (s : Finset ι) (r : ι → ℝ) (v : ι → TangentSpace I x) (a b c d : TangentSpace I x) :
    covRm g x (∑ i ∈ s, r i • v i) a b c d
      = ∑ i ∈ s, r i * covRm g x (v i) a b c d :=
  linear_of_binary (fun w : TangentSpace I x => covRm g x w a b c d)
    (fun u w => covRm_add_fst hLC g x u w a b c d)
    (fun ρ w => covRm_smul_fst hLC g x ρ w a b c d) s r v

/-- Finite-sum form of the linearity of `covRm` in its second argument `a`. -/
private lemma covRm_sum_snd (hLC : LCSmooth I M) (g : SMet I M) (x : M) {ι : Type*}
    (s : Finset ι) (r : ι → ℝ) (a : ι → TangentSpace I x) (v b c d : TangentSpace I x) :
    covRm g x v (∑ i ∈ s, r i • a i) b c d
      = ∑ i ∈ s, r i * covRm g x v (a i) b c d :=
  linear_of_binary (fun w : TangentSpace I x => covRm g x v w b c d)
    (fun u w => by
      have h := covRm_linear_snd hLC g x v 1 1 u w b c d
      simpa using h)
    (fun ρ w => by
      have h := covRm_linear_snd hLC g x v ρ 0 w 0 b c d
      simpa using h)
    s r a

/-- Finite-sum form of the linearity of `covRm` in its third argument `b`. -/
private lemma covRm_sum_thd (hLC : LCSmooth I M) (g : SMet I M) (x : M) {ι : Type*}
    (s : Finset ι) (r : ι → ℝ) (b : ι → TangentSpace I x) (v a c d : TangentSpace I x) :
    covRm g x v a (∑ i ∈ s, r i • b i) c d
      = ∑ i ∈ s, r i * covRm g x v a (b i) c d :=
  linear_of_binary (fun w : TangentSpace I x => covRm g x v a w c d)
    (fun u w => by
      have h := covRm_linear_thd hLC g x v a 1 1 u w c d
      simpa using h)
    (fun ρ w => by
      have h := covRm_linear_thd hLC g x v a ρ 0 w 0 c d
      simpa using h)
    s r b

/-- Finite-sum form of the linearity of `covRm` in its fourth argument `c`. -/
private lemma covRm_sum_fth (hLC : LCSmooth I M) (g : SMet I M) (x : M) {ι : Type*}
    (s : Finset ι) (r : ι → ℝ) (c : ι → TangentSpace I x) (v a b d : TangentSpace I x) :
    covRm g x v a b (∑ i ∈ s, r i • c i) d
      = ∑ i ∈ s, r i * covRm g x v a b (c i) d :=
  linear_of_binary (fun w : TangentSpace I x => covRm g x v a b w d)
    (fun u w => by
      have h := covRm_linear_fth hLC g x v a b 1 1 u w d
      simpa using h)
    (fun ρ w => by
      have h := covRm_linear_fth hLC g x v a b ρ 0 w 0 d
      simpa using h)
    s r c

/-! ### The fifth argument: skew-symmetry with the fourth

`Rm(a,b,c,d) = ⟪R(a,b)d, c⟫` is skew in its last two `rmP` slots (`Work.Diff.GE.rmP_skew`), so
`covRm` is too: differentiating the pointwise identity swaps the sign.  Hence the linearity of
`covRm` in its fifth argument follows from its linearity in its fourth. -/

/-- `dRmPhi` is skew in its last two field slots. -/
private lemma dRmPhi_skew_last (hLC : LCSmooth I M) (g : SMet I M) (x : M) (v : TangentSpace I x)
    (A B C D : Π y : M, TangentSpace I y) :
    dRmPhi g x v A B C D = -dRmPhi g x v A B D C := by
  have h1 : (fun y : M => rmP g y (A y) (B y) (C y) (D y))
      = -(fun y : M => rmP g y (A y) (B y) (D y) (C y)) := by
    funext y
    rw [rmP_skew hLC g y]
    rfl
  simp only [dRmPhi]
  rw [h1, mvfderiv_neg]
  simp only [ContinuousLinearMap.neg_apply]
  rw [rmP_skew hLC g x (lcOf g A x v) (B x) (C x) (D x),
      rmP_skew hLC g x (A x) (lcOf g B x v) (C x) (D x),
      rmP_skew hLC g x (A x) (B x) (lcOf g C x v) (D x),
      rmP_skew hLC g x (A x) (B x) (C x) (lcOf g D x v)]
  ring

/-- `covRm` is skew in its last two arguments. -/
private lemma covRm_skew_last (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (v a b c d : TangentSpace I x) :
    covRm g x v a b c d = -covRm g x v a b d c := by
  rw [covRm_eq_dRmPhi (a := a) (b := b) (c := c) (d := d),
      covRm_eq_dRmPhi (a := a) (b := b) (c := d) (d := c)]
  exact dRmPhi_skew_last hLC g x v (smoothExt x a) (smoothExt x b) (smoothExt x c)
    (smoothExt x d)

/-- Finite-sum form of the linearity of `covRm` in its fifth (last) argument `d`. -/
private lemma covRm_sum_fith (hLC : LCSmooth I M) (g : SMet I M) (x : M) {ι : Type*}
    (s : Finset ι) (r : ι → ℝ) (d : ι → TangentSpace I x) (v a b c : TangentSpace I x) :
    covRm g x v a b c (∑ i ∈ s, r i • d i)
      = ∑ i ∈ s, r i * covRm g x v a b c (d i) := by
  have h1 : covRm g x v a b c (∑ i ∈ s, r i • d i)
      = -covRm g x v a b (∑ i ∈ s, r i • d i) c :=
    covRm_skew_last hLC g x v a b c _
  rw [h1, covRm_sum_fth hLC g x s r d v a b c]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [covRm_skew_last hLC g x v a b c (d i)]
  ring

/-- **`covRm` is multilinear in its five arguments.**  `∇Rm` is a `(0,5)`-tensor, so its components in
an arbitrary frame are multilinear: expanding all five arguments in a family `e` gives the five-fold sum
(cf. `rot` for 4-tensors).  Only linearity, not orthonormality of `e`, is involved.  This follows from
the field form `kato_covRm_field` (additivity and homogeneity in each vector argument reduce to the
corresponding statements for the fields `smoothExt x ·`); add the import of that module if needed. -/
theorem kato_covRm_multilinear
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x) (c : Fin 5 → Fin (Module.finrank ℝ E) → ℝ) :
    covRm g x (∑ i, c 0 i • e i) (∑ i, c 1 i • e i) (∑ i, c 2 i • e i)
        (∑ i, c 3 i • e i) (∑ i, c 4 i • e i)
      = ∑ i0, ∑ i1, ∑ i2, ∑ i3, ∑ i4,
          (c 0 i0 * c 1 i1 * c 2 i2 * c 3 i3 * c 4 i4)
            * covRm g x (e i0) (e i1) (e i2) (e i3) (e i4) := by
  rw [covRm_sum_fst hLC g x Finset.univ (c 0) e _ _ _ _]
  refine Finset.sum_congr rfl (fun i0 _ => ?_)
  rw [covRm_sum_snd hLC g x Finset.univ (c 1) e (e i0) _ _ _]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i1 _ => ?_)
  rw [covRm_sum_thd hLC g x Finset.univ (c 2) e (e i0) (e i1) _ _]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i2 _ => ?_)
  rw [covRm_sum_fth hLC g x Finset.univ (c 3) e (e i0) (e i1) (e i2) _]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i3 _ => ?_)
  rw [covRm_sum_fith hLC g x Finset.univ (c 4) e (e i0) (e i1) (e i2) (e i3)]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i4 _ => ?_)
  ring

end Work.Diff.GE
