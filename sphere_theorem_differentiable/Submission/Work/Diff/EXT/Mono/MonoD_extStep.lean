import Mathlib
import Submission.Work.Diff.EXT.reactBase
import Submission.Work.Diff.EXT.Mono.towerArr_mvfderiv
import Submission.Work.Diff.EXT.Mono.pairing_mvfderiv
import Submission.Work.Diff.EXT.evX.mvfderiv_rmSymV

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Leibniz recursion of the monomial `MonoD` of the level-`0` reaction ladder

`Work.Diff.EXT.MonoD g N a b d₁ d₂ s e F y` is the contraction of the polarized reaction
`rmSym (∇^a Rm) (∇^b Rm)` — the tower levels `a` and `b` of the curvature evaluated on the
partition of the tuple `F` prescribed by the three index maps `d₁`, `d₂`, `s` — with the four
slot pairings of the tuple against the frame `e`.

This file proves that one step of the Ext-pattern covariant derivative
`Work.Diff.EXT.extStep` (which is `∇_{F 0}` together with the Leibniz corrections of *all* the
slots of the running tuple) splits the monomial into its two children: the new derivative
direction goes into the first tower factor (giving `MonoD` at level `(a+1,b)`) or into the second
(giving `MonoD` at level `(a,b+1)`).

## Route of the proof

* `mvfderiv_sum4_prod_pt` is the four-fold sum-of-products rule for `mvfderiv`, and
  `mvfderiv_rmSym_contract` applies it to the contraction of `rmSym (A z) (B z)` with a
  four-index family `P`: the derivative is the sum of the three groups `C · dP`,
  `rmSym dA (B y) · P` and `rmSym (A y) dB · P`.
* The three ingredients are the pointwise Leibniz rules of the shared library:
  `Work.Diff.EXT.Mono.towerArr_mvfderiv` (derivative of the tower array, in a frame that is
  parallel at `y` — this is where `hgeo` is used: the four slot corrections of the frame fields
  vanish), `pairProd_mvfderiv` below (derivative of the product of the four metric pairings, from
  `Work.Diff.EXT.Mono.pairing_mvfderiv`) and `Work.Diff.EXT.evX.mvfderiv_rmSymV` (Leibniz rule for
  `rmSym`, the `RmPair` copy being still in flight).
* The correction sum `∑ u, MonoD (F with slot u replaced by ∇_{F 0})` of `extStep` is split along
  the three index maps by `sum_over_partition` (here `hcov`, the injectivities and the pairwise
  disjointnesses enter) and matched term by term with the three groups of the derivative
  (`update_comp_same` / `update_comp_ne` identify the corresponding tuples).
-/

namespace Work.Diff.EXT.Mono

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]

/-! ## The Leibniz rules for finite sums and products of scalar functions -/

/-- A finite sum of functions differentiable at `y` is differentiable at `y`. -/
theorem mdifferentiableAt_sum_pt {ι : Type*} (t : Finset ι) (F : ι → M → ℝ) {y : M}
    (hF : ∀ i ∈ t, MDifferentiableAt I (modelWithCornersSelf ℝ ℝ) (F i) y) :
    MDifferentiableAt I (modelWithCornersSelf ℝ ℝ) (fun z => ∑ i ∈ t, F i z) y := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      have h : (fun z : M => ∑ i ∈ (∅ : Finset ι), F i z) = fun _ : M => (0 : ℝ) := by
        funext z; simp
      rw [h]; exact mdifferentiableAt_const (c := (0 : ℝ))
  | insert i t hi ih =>
      have h : (fun z : M => ∑ j ∈ insert i t, F j z) = fun z : M => F i z + ∑ j ∈ t, F j z := by
        funext z; rw [Finset.sum_insert hi]
      rw [h]
      exact (hF i (Finset.mem_insert_self i t)).add
        (ih (fun j hj => hF j (Finset.mem_insert_of_mem hj)))

/-- The derivative of a finite sum, in the evaluated form. -/
theorem mvfderiv_sum_pt {ι : Type*} (t : Finset ι) (F : ι → M → ℝ) {y : M} (v : TangentSpace I y)
    (hF : ∀ i ∈ t, MDifferentiableAt I (modelWithCornersSelf ℝ ℝ) (F i) y) :
    (mvfderiv I (fun z => ∑ i ∈ t, F i z) y) v = ∑ i ∈ t, (mvfderiv I (F i) y) v := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact congrArg (fun L : TangentSpace I y →L[ℝ] ℝ => L v)
        (mvfderiv_const (I := I) (c := (0 : ℝ)) (x := y))
  | insert i t hi ih =>
      have h : (fun z : M => ∑ j ∈ insert i t, F j z) = fun z : M => F i z + ∑ j ∈ t, F j z := by
        funext z; rw [Finset.sum_insert hi]
      have hplus : (fun z : M => F i z + ∑ j ∈ t, F j z)
          = F i + (fun z : M => ∑ j ∈ t, F j z) := rfl
      have hsum : MDifferentiableAt I (modelWithCornersSelf ℝ ℝ)
          (fun z : M => ∑ j ∈ t, F j z) y :=
        mdifferentiableAt_sum_pt t F (fun j hj => hF j (Finset.mem_insert_of_mem hj))
      have hd := congrArg (fun L : TangentSpace I y →L[ℝ] ℝ => L v)
        (mvfderiv_add (I := I) (x := y) (g := F i)
          (g' := fun z : M => ∑ j ∈ t, F j z) (hF i (Finset.mem_insert_self i t)) hsum)
      simp only [add_apply] at hd
      rw [h, hplus, hd, ih (fun j hj => hF j (Finset.mem_insert_of_mem hj)), Finset.sum_insert hi]

/-- The product rule, in the evaluated form. -/
theorem mvfderiv_mul_pt {f g : M → ℝ} {y : M} (v : TangentSpace I y)
    (hf : MDifferentiableAt I (modelWithCornersSelf ℝ ℝ) f y)
    (hg : MDifferentiableAt I (modelWithCornersSelf ℝ ℝ) g y) :
    (mvfderiv I (fun z => f z * g z) y) v
      = f y * (mvfderiv I g y) v + g y * (mvfderiv I f y) v := by
  rw [show (fun z : M => f z * g z) = f * g from rfl]
  have h := congrArg (fun L : TangentSpace I y →L[ℝ] ℝ => L v)
    (mvfderiv_mul (I := I) (x := y) (f := f) (g := g) hf hg)
  simpa only [add_apply, smul_apply, smul_eq_mul] using h

/-- The four-fold sum-of-products rule for `mvfderiv`. -/
theorem mvfderiv_sum4_prod_pt {ι : Type*} [Fintype ι] {y : M} (v : TangentSpace I y)
    (C P : ι → ι → ι → ι → M → ℝ)
    (hC : ∀ i j k l, MDifferentiableAt I (modelWithCornersSelf ℝ ℝ) (C i j k l) y)
    (hP : ∀ i j k l, MDifferentiableAt I (modelWithCornersSelf ℝ ℝ) (P i j k l) y) :
    (mvfderiv I (fun z => ∑ i, ∑ j, ∑ k, ∑ l, C i j k l z * P i j k l z) y) v
      = ∑ i, ∑ j, ∑ k, ∑ l, (C i j k l y * (mvfderiv I (P i j k l) y) v
          + P i j k l y * (mvfderiv I (C i j k l) y) v) := by
  have h4 : ∀ i j k, MDifferentiableAt I (modelWithCornersSelf ℝ ℝ)
      (fun z => ∑ l, C i j k l z * P i j k l z) y :=
    fun i j k => mdifferentiableAt_sum_pt _ _ (fun l _ => (hC i j k l).mul (hP i j k l))
  have h3 : ∀ i j, MDifferentiableAt I (modelWithCornersSelf ℝ ℝ)
      (fun z => ∑ k, ∑ l, C i j k l z * P i j k l z) y :=
    fun i j => mdifferentiableAt_sum_pt _ _ (fun k _ => h4 i j k)
  have h2 : ∀ i, MDifferentiableAt I (modelWithCornersSelf ℝ ℝ)
      (fun z => ∑ j, ∑ k, ∑ l, C i j k l z * P i j k l z) y :=
    fun i => mdifferentiableAt_sum_pt _ _ (fun j _ => h3 i j)
  rw [mvfderiv_sum_pt Finset.univ (fun i z => ∑ j, ∑ k, ∑ l, C i j k l z * P i j k l z) v
    (fun i _ => h2 i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mvfderiv_sum_pt Finset.univ (fun j z => ∑ k, ∑ l, C i j k l z * P i j k l z) v
    (fun j _ => h3 i j)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mvfderiv_sum_pt Finset.univ (fun k z => ∑ l, C i j k l z * P i j k l z) v
    (fun k _ => h4 i j k)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mvfderiv_sum_pt Finset.univ (fun l z => C i j k l z * P i j k l z) v
    (fun l _ => (hC i j k l).mul (hP i j k l))]
  exact Finset.sum_congr rfl fun l _ => mvfderiv_mul_pt v (hC i j k l) (hP i j k l)

/-! ## The product of the four slot pairings and its derivative -/

/-- The product of the four pairings of the frame `e` with the four slot fields `sl`. -/
noncomputable def pairProd (g : Submission.Diff.SMet I M)
    (e : Fin (Module.finrank ℝ E) → Work.Diff.EXT.TField (I := I) (M := M))
    (sl : Fin 4 → Work.Diff.EXT.TField (I := I) (M := M))
    (i j k l : Fin (Module.finrank ℝ E)) : M → ℝ :=
  fun y => g.inner y (e i y) (sl 0 y) * g.inner y (e j y) (sl 1 y)
    * g.inner y (e k y) (sl 2 y) * g.inner y (e l y) (sl 3 y)

/-- The metric pairing of two smooth fields is smooth. -/
theorem metricPairing_smooth (g : Submission.Diff.SMet I M)
    {Y Z : Work.Diff.EXT.TField (I := I) (M := M)}
    (hY : Work.Diff.GE.SmoothFieldT (I := I) (M := M) Y)
    (hZ : Work.Diff.GE.SmoothFieldT (I := I) (M := M) Z) :
    CMDiff ∞ (fun y : M => g.inner y (Y y) (Z y)) := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  change CMDiff ∞ (fun y : M => inner ℝ (Y y) (Z y))
  exact ContMDiff.inner_bundle (IB := I) (b := id) (v := Y) (w := Z) hY hZ

/-- The metric pairing of two smooth fields is differentiable. -/
theorem metricPairing_mdiffAt (g : Submission.Diff.SMet I M)
    {Y Z : Work.Diff.EXT.TField (I := I) (M := M)}
    (hY : Work.Diff.GE.SmoothFieldT (I := I) (M := M) Y)
    (hZ : Work.Diff.GE.SmoothFieldT (I := I) (M := M) Z) (y : M) :
    MDifferentiableAt I (modelWithCornersSelf ℝ ℝ) (fun z => g.inner z (Y z) (Z z)) y :=
  (metricPairing_smooth g hY hZ).contMDiffAt.mdifferentiableAt (by simp)

/-- **The derivative of the product of the four slot pairings**: the sum of the four terms in which
one pairing is replaced by its covariant derivative. -/
theorem pairProd_mvfderiv (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M)
    (y : M) (e : Fin (Module.finrank ℝ E) → Work.Diff.EXT.TField (I := I) (M := M))
    (he : ∀ i, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (e i))
    (hgeo : ∀ i, Submission.Diff.lcOf g (e i) y = 0)
    (sl : Fin 4 → Work.Diff.EXT.TField (I := I) (M := M))
    (hsl : ∀ t, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (sl t))
    (X : Work.Diff.EXT.TField (I := I) (M := M))
    (hX : Work.Diff.GE.SmoothFieldT (I := I) (M := M) X)
    (i j k l : Fin (Module.finrank ℝ E)) :
    (mvfderiv I (pairProd (I := I) (M := M) g e sl i j k l) y) (X y)
      = g.inner y (e j y) (sl 1 y) * g.inner y (e k y) (sl 2 y) * g.inner y (e l y) (sl 3 y)
          * g.inner y (e i y) (Work.Diff.EXT.dirF g (sl 0) X y)
        + g.inner y (e i y) (sl 0 y) * g.inner y (e k y) (sl 2 y) * g.inner y (e l y) (sl 3 y)
          * g.inner y (e j y) (Work.Diff.EXT.dirF g (sl 1) X y)
        + g.inner y (e i y) (sl 0 y) * g.inner y (e j y) (sl 1 y) * g.inner y (e l y) (sl 3 y)
          * g.inner y (e k y) (Work.Diff.EXT.dirF g (sl 2) X y)
        + g.inner y (e i y) (sl 0 y) * g.inner y (e j y) (sl 1 y) * g.inner y (e k y) (sl 2 y)
          * g.inner y (e l y) (Work.Diff.EXT.dirF g (sl 3) X y) := by
  have hm1 := metricPairing_mdiffAt g (he i) (hsl 0) y
  have hm2 := metricPairing_mdiffAt g (he j) (hsl 1) y
  have hm3 := metricPairing_mdiffAt g (he k) (hsl 2) y
  have hm4 := metricPairing_mdiffAt g (he l) (hsl 3) y
  have e1 := mvfderiv_mul_pt (I := I) (M := M)
    (f := fun z : M => g.inner z (e i z) (sl 0 z) * g.inner z (e j z) (sl 1 z)
      * g.inner z (e k z) (sl 2 z))
    (g := fun z : M => g.inner z (e l z) (sl 3 z)) (X y) ((hm1.mul hm2).mul hm3) hm4
  have e2 := mvfderiv_mul_pt (I := I) (M := M)
    (f := fun z : M => g.inner z (e i z) (sl 0 z) * g.inner z (e j z) (sl 1 z))
    (g := fun z : M => g.inner z (e k z) (sl 2 z)) (X y) (hm1.mul hm2) hm3
  have e3 := mvfderiv_mul_pt (I := I) (M := M)
    (f := fun z : M => g.inner z (e i z) (sl 0 z))
    (g := fun z : M => g.inner z (e j z) (sl 1 z)) (X y) hm1 hm2
  change (mvfderiv I (fun z : M => g.inner z (e i z) (sl 0 z) * g.inner z (e j z) (sl 1 z)
      * g.inner z (e k z) (sl 2 z) * g.inner z (e l z) (sl 3 z)) y) (X y) = _
  rw [e1, e2, e3]
  rw [pairing_mvfderiv (I := I) (M := M) hLC g y e he hgeo (sl 0) (hsl 0) X hX i,
    pairing_mvfderiv (I := I) (M := M) hLC g y e he hgeo (sl 1) (hsl 1) X hX j,
    pairing_mvfderiv (I := I) (M := M) hLC g y e he hgeo (sl 2) (hsl 2) X hX k,
    pairing_mvfderiv (I := I) (M := M) hLC g y e he hgeo (sl 3) (hsl 3) X hX l]
  ring

/-! ## Componentwise differentiability of `Curv4`-valued maps -/

/-- The `(i,j,k,l)`-component of a differentiable `Curv4`-valued map is differentiable. -/
theorem curv4_comp_mdiffAt {n : ℕ} {A : M → Curv4 n} {x : M}
    (h : MDifferentiableAt I (modelWithCornersSelf ℝ (Curv4 n)) A x) (i j k l : Fin n) :
    MDifferentiableAt I (modelWithCornersSelf ℝ ℝ) (fun y => A y i j k l) x := by
  have hd1 : MDifferentiableAt I (modelWithCornersSelf ℝ (Fin n → Fin n → Fin n → ℝ))
      (fun y => A y i) x :=
    ((differentiableAt_apply (𝕜 := ℝ) i (A x)).mdifferentiableAt).comp x h
  have hd2 : MDifferentiableAt I (modelWithCornersSelf ℝ (Fin n → Fin n → ℝ))
      (fun y => A y i j) x :=
    ((differentiableAt_apply (𝕜 := ℝ) j (A x i)).mdifferentiableAt).comp x hd1
  have hd3 : MDifferentiableAt I (modelWithCornersSelf ℝ (Fin n → ℝ))
      (fun y => A y i j k) x :=
    ((differentiableAt_apply (𝕜 := ℝ) k (A x i j)).mdifferentiableAt).comp x hd2
  exact ((differentiableAt_apply (𝕜 := ℝ) l (A x i j k)).mdifferentiableAt).comp x hd3

/-- `rmSym` is additive in its first argument, for finite sums. -/
theorem rmSym_sum_left {n : ℕ} {ι : Type*} (t : Finset ι) (X : ι → Curv4 n) (Y : Curv4 n) :
    rmSym (∑ i ∈ t, X i) Y = ∑ i ∈ t, rmSym (X i) Y := by
  have h := map_sum (Work.Diff.EXT.evX.rmSymCLM n) X t
  have h2 := congrArg (fun L : Curv4 n →L[ℝ] Curv4 n => L Y) h
  simpa only [ContinuousLinearMap.sum_apply, Work.Diff.EXT.evX.rmSymCLM_apply] using h2

/-- `rmSym` is additive in its second argument, for finite sums. -/
theorem rmSym_sum_right {n : ℕ} {ι : Type*} (t : Finset ι) (X : Curv4 n) (Y : ι → Curv4 n) :
    rmSym X (∑ i ∈ t, Y i) = ∑ i ∈ t, rmSym X (Y i) := by
  have h := map_sum (Work.Diff.EXT.evX.rmSymCLM n X) Y t
  simpa only [Work.Diff.EXT.evX.rmSymCLM_apply] using h

/-! ## The Leibniz rule for a contraction of `rmSym` with a four-index family -/

/-- **The Leibniz rule for the contraction `∑ i j k l, rmSym (A z) (B z) i j k l * P i j k l z`**,
evaluated at the point `y` in the direction `v`: the derivative is the sum of the three groups in
which the derivative acts on the pairing family (`C · dP`) or on one of the two `rmSym`-arguments. -/
theorem mvfderiv_rmSym_contract {n : ℕ}
    (A B : M → Curv4 n) (P : Fin n → Fin n → Fin n → Fin n → M → ℝ)
    (y : M) (v : TangentSpace I y)
    (dA dB : Curv4 n) (dP : Fin n → Fin n → Fin n → Fin n → ℝ)
    (hA : ∀ p q r s, mvfderiv I (fun z => A z p q r s) y v = dA p q r s)
    (hB : ∀ p q r s, mvfderiv I (fun z => B z p q r s) y v = dB p q r s)
    (hP : ∀ p q r s, mvfderiv I (fun z => P p q r s z) y v = dP p q r s)
    (hAd : ∀ p q r s, MDifferentiableAt I (modelWithCornersSelf ℝ ℝ) (fun z => A z p q r s) y)
    (hBd : ∀ p q r s, MDifferentiableAt I (modelWithCornersSelf ℝ ℝ) (fun z => B z p q r s) y)
    (hPd : ∀ p q r s, MDifferentiableAt I (modelWithCornersSelf ℝ ℝ) (fun z => P p q r s z) y) :
    (mvfderiv I (fun z => ∑ i, ∑ j, ∑ k, ∑ l,
        rmSym (A z) (B z) i j k l * P i j k l z) y) v
      = (∑ i, ∑ j, ∑ k, ∑ l, rmSym (A y) (B y) i j k l * dP i j k l)
        + (∑ i, ∑ j, ∑ k, ∑ l, rmSym dA (B y) i j k l * P i j k l y)
        + (∑ i, ∑ j, ∑ k, ∑ l, rmSym (A y) dB i j k l * P i j k l y) := by
  have hA' : MDifferentiableAt I (modelWithCornersSelf ℝ (Curv4 n)) A y :=
    Work.Diff.EXT.evX.mdifferentiableAt_curv4_of_components hAd
  have hB' : MDifferentiableAt I (modelWithCornersSelf ℝ (Curv4 n)) B y :=
    Work.Diff.EXT.evX.mdifferentiableAt_curv4_of_components hBd
  have hbilin : MDifferentiableAt I (modelWithCornersSelf ℝ (Curv4 n))
      (fun z => rmSym (A z) (B z)) y :=
    Work.Diff.EXT.evX.mdifferentiableAt_bilin_pair
      (fun w : Curv4 n × Curv4 n => rmSym w.1 w.2)
      (Work.Diff.EXT.evX.rmSym_isBoundedBilinearMap n) hA' hB'
  have hCd : ∀ p q r s, MDifferentiableAt I (modelWithCornersSelf ℝ ℝ)
      (fun z => rmSym (A z) (B z) p q r s) y :=
    fun p q r s => curv4_comp_mdiffAt hbilin p q r s
  rw [mvfderiv_sum4_prod_pt (I := I) (M := M) (ι := Fin n) v
    (fun i j k l z => rmSym (A z) (B z) i j k l) P hCd hPd]
  have hdA : (fun p q r s => mvfderiv I (fun z => A z p q r s) y v) = dA :=
    funext fun p => funext fun q => funext fun r => funext fun s => hA p q r s
  have hdB : (fun p q r s => mvfderiv I (fun z => B z p q r s) y v) = dB :=
    funext fun p => funext fun q => funext fun r => funext fun s => hB p q r s
  have hpt : ∀ i j k l,
      (rmSym (A y) (B y) i j k l * (mvfderiv I (P i j k l) y) v
        + P i j k l y * (mvfderiv I (fun z => rmSym (A z) (B z) i j k l) y) v)
        = (rmSym (A y) (B y) i j k l * dP i j k l
            + (rmSym dA (B y) i j k l * P i j k l y + rmSym (A y) dB i j k l * P i j k l y)) := by
    intro i j k l
    rw [Work.Diff.EXT.evX.mvfderiv_rmSymV (I := I) (M := M) n A B y v hAd hBd i j k l,
      hP i j k l, hdA, hdB]
    ring
  rw [show (∑ i, ∑ j, ∑ k, ∑ l, (rmSym (A y) (B y) i j k l * (mvfderiv I (P i j k l) y) v
        + P i j k l y * (mvfderiv I (fun z => rmSym (A z) (B z) i j k l) y) v))
      = (∑ i, ∑ j, ∑ k, ∑ l, (rmSym (A y) (B y) i j k l * dP i j k l
          + (rmSym dA (B y) i j k l * P i j k l y
            + rmSym (A y) dB i j k l * P i j k l y))) from by
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ =>
      Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => hpt i j k l))))]
  simp only [Finset.sum_add_distrib]
  ring

/-! ## Differentiability of the tower array -/

/-- The `(i,j,k,l)`-component of the tower array `∇^a Rm` in the frame `e` is differentiable. -/
theorem TowerArr_mdiffAt (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M)
    (a : ℕ) (D : Fin a → Work.Diff.EXT.TField (I := I) (M := M))
    (hD : ∀ r, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (D r))
    (e : Fin (Module.finrank ℝ E) → Work.Diff.EXT.TField (I := I) (M := M))
    (he : ∀ i, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (e i))
    (z : M) (i j k l : Fin (Module.finrank ℝ E)) :
    MDifferentiableAt I (modelWithCornersSelf ℝ ℝ)
      (fun y => Work.Diff.EXT.TowerArr g a D e y i j k l) z := by
  have hFS : ∀ s : Fin (a + 4),
      Work.Diff.EXT.SmoothF ((Fin.append D ![e i, e j, e k, e l]) s) := by
    intro s
    refine Fin.addCases (m := a) (n := 4) (fun r => ?_) (fun t => ?_) s
    · rw [Fin.append_left]; exact hD r
    · rw [Fin.append_right]
      fin_cases t
      · exact he i
      · exact he j
      · exact he k
      · exact he l
  have h := (Work.Diff.EXT.tensProp_all hLC g a
    (Fin.append D ![e i, e j, e k, e l]) hFS).1
  change MDifferentiableAt I (modelWithCornersSelf ℝ ℝ)
    (fun y => Work.Diff.EXT.ckt g a (Fin.append D ![e i, e j, e k, e l]) y) z
  exact h.contMDiffAt.mdifferentiableAt (by simp)

/-! ## The derivative of the tower array, at the level of `Curv4`-valued functions -/

/-- The value of a sum of `Curv4`-valued functions at a multi-index. -/
theorem sum_app4 {n : ℕ} {ι : Type*} [Fintype ι] (f : ι → Curv4 n) (i j k l : Fin n) :
    (∑ r, f r) i j k l = ∑ r, f r i j k l := by
  simp only [Finset.sum_apply]

/-- **The Leibniz recursion of the tower array**, as an equality of `Curv4`-valued functions: the
derivative of `TowerArr g a D e ·` along `X` is the next tower level (with `X` prepended) plus the
`a` correction terms of the differentiation slots.  The four frame-slot corrections vanish because
the frame is parallel at `y` (`hgeo`); this is the content of
`Work.Diff.EXT.Mono.towerArr_mvfderiv`. -/
theorem TowerArr_deriv_fun (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M)
    (y : M) (e : Fin (Module.finrank ℝ E) → Work.Diff.EXT.TField (I := I) (M := M))
    (he : ∀ i, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (e i))
    (hgeo : ∀ i, Submission.Diff.lcOf g (e i) y = 0)
    (a : ℕ) (D : Fin a → Work.Diff.EXT.TField (I := I) (M := M))
    (hD : ∀ r, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (D r))
    (X : Work.Diff.EXT.TField (I := I) (M := M))
    (hX : Work.Diff.GE.SmoothFieldT (I := I) (M := M) X) :
    (fun p q r s => mvfderiv I (fun z => Work.Diff.EXT.TowerArr g a D e z p q r s) y (X y))
      = Work.Diff.EXT.TowerArr g (a + 1) (Fin.cons X D) e y
        + ∑ r : Fin a, Work.Diff.EXT.TowerArr g a
            (Function.update D r (Work.Diff.EXT.dirF g (D r) X)) e y := by
  funext p q r s
  rw [towerArr_mvfderiv (I := I) (M := M) hLC g y e he hgeo a D hD X hX p q r s]
  simp only [Pi.add_apply]
  rw [sum_app4]

/-! ## The unfolding of `MonoD` and the sums over partitions -/

/-- The four-fold unfolding of `MonoD` into the product of the `rmSym`-contraction with the product
of the four slot pairings. -/
theorem MonoD_sum {g : Submission.Diff.SMet I M} {y : M}
    {e : Fin (Module.finrank ℝ E) → Work.Diff.EXT.TField (I := I) (M := M)}
    {N a b : ℕ} (d₁ : Fin a → Fin N) (d₂ : Fin b → Fin N) (s : Fin 4 → Fin N)
    (G : Fin N → Work.Diff.EXT.TField (I := I) (M := M)) :
    Work.Diff.EXT.MonoD g N a b d₁ d₂ s e G y
      = ∑ i, ∑ j, ∑ k, ∑ l,
          rmSym (Work.Diff.EXT.TowerArr g a (fun r => G (d₁ r)) e y)
            (Work.Diff.EXT.TowerArr g b (fun r => G (d₂ r)) e y) i j k l
          * pairProd (I := I) (M := M) g e (fun t => G (s t)) i j k l y := by
  simp only [Work.Diff.EXT.MonoD, pairProd]

/-- **The sum over the tuple slots splits along the three index maps.**  If `d₁`, `d₂`, `s` are
injective with pairwise disjoint images covering `Fin N`, then a sum over `Fin N` is the sum over
the three index sets. -/
theorem sum_over_partition {N a b : ℕ} (d₁ : Fin a → Fin N) (d₂ : Fin b → Fin N) (s : Fin 4 → Fin N)
    (hinj₁ : Function.Injective d₁) (hinj₂ : Function.Injective d₂) (hinjs : Function.Injective s)
    (hd₁₂ : ∀ r r', d₁ r ≠ d₂ r') (hd₁s : ∀ r t, d₁ r ≠ s t) (hd₂s : ∀ r t, d₂ r ≠ s t)
    (hcov : ∀ u : Fin N, (∃ r, d₁ r = u) ∨ (∃ r, d₂ r = u) ∨ (∃ t, s t = u))
    {A : Type*} [AddCommMonoid A] (Φ : Fin N → A) :
    ∑ u : Fin N, Φ u = (∑ r : Fin a, Φ (d₁ r)) + (∑ r : Fin b, Φ (d₂ r)) + (∑ t : Fin 4, Φ (s t)) := by
  classical
  have hcover : ((Finset.univ.image d₁ ∪ Finset.univ.image d₂) ∪ Finset.univ.image s :
      Finset (Fin N)) = Finset.univ := by
    ext u
    constructor
    · intro _; exact Finset.mem_univ u
    · intro _
      rcases hcov u with ⟨r, hr⟩ | ⟨r, hr⟩ | ⟨t, ht⟩
      · exact Finset.mem_union_left _
          (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨r, Finset.mem_univ r, hr⟩))
      · exact Finset.mem_union_left _
          (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨r, Finset.mem_univ r, hr⟩))
      · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨t, Finset.mem_univ t, ht⟩)
  have hd12 : Disjoint (Finset.univ.image d₁ : Finset (Fin N)) (Finset.univ.image d₂) := by
    rw [Finset.disjoint_left]
    intro u hu hu'
    obtain ⟨r, -, hr⟩ := Finset.mem_image.mp hu
    obtain ⟨r', -, hr'⟩ := Finset.mem_image.mp hu'
    exact hd₁₂ r r' (hr.trans hr'.symm)
  have hd1s : Disjoint (Finset.univ.image d₁ : Finset (Fin N)) (Finset.univ.image s) := by
    rw [Finset.disjoint_left]
    intro u hu hu'
    obtain ⟨r, -, hr⟩ := Finset.mem_image.mp hu
    obtain ⟨t, -, ht⟩ := Finset.mem_image.mp hu'
    exact hd₁s r t (hr.trans ht.symm)
  have hd2s : Disjoint (Finset.univ.image d₂ : Finset (Fin N)) (Finset.univ.image s) := by
    rw [Finset.disjoint_left]
    intro u hu hu'
    obtain ⟨r, -, hr⟩ := Finset.mem_image.mp hu
    obtain ⟨t, -, ht⟩ := Finset.mem_image.mp hu'
    exact hd₂s r t (hr.trans ht.symm)
  have h1 : ∑ u ∈ (Finset.univ.image d₁ : Finset (Fin N)), Φ u = ∑ r : Fin a, Φ (d₁ r) :=
    Finset.sum_image (fun x _ y _ hxy => hinj₁ hxy)
  have h2 : ∑ u ∈ (Finset.univ.image d₂ : Finset (Fin N)), Φ u = ∑ r : Fin b, Φ (d₂ r) :=
    Finset.sum_image (fun x _ y _ hxy => hinj₂ hxy)
  have h3 : ∑ u ∈ (Finset.univ.image s : Finset (Fin N)), Φ u = ∑ t : Fin 4, Φ (s t) :=
    Finset.sum_image (fun x _ y _ hxy => hinjs hxy)
  have hdU : Disjoint ((Finset.univ.image d₁ ∪ Finset.univ.image d₂ : Finset (Fin N)))
      (Finset.univ.image s) :=
    Finset.disjoint_union_left.mpr ⟨hd1s, hd2s⟩
  rw [← hcover, Finset.sum_union hdU, Finset.sum_union hd12, h1, h2, h3]

/-- Moving a sum over an auxiliary index out of a four-fold sum over the frame indices. -/
theorem sum4_comm_sum {ι : Type*} [Fintype ι] {A : Type*} [AddCommMonoid A] {n : ℕ}
    (G : Fin n → Fin n → Fin n → Fin n → ι → A) :
    (∑ i, ∑ j, ∑ k, ∑ l, ∑ r, G i j k l r) = (∑ r, ∑ i, ∑ j, ∑ k, ∑ l, G i j k l r) := by
  have h3 : ∀ i j k : Fin n, (∑ l, ∑ r, G i j k l r) = ∑ r, ∑ l, G i j k l r := fun i j k =>
    Finset.sum_comm
  have h2 : ∀ i j : Fin n, (∑ k, ∑ r, ∑ l, G i j k l r) = ∑ r, ∑ k, ∑ l, G i j k l r :=
    fun i j => Finset.sum_comm
  have h1 : ∀ i : Fin n, (∑ j, ∑ r, ∑ k, ∑ l, G i j k l r) = ∑ r, ∑ j, ∑ k, ∑ l, G i j k l r :=
    fun i => Finset.sum_comm
  have h0 : (∑ i, ∑ r, ∑ j, ∑ k, ∑ l, G i j k l r) = ∑ r, ∑ i, ∑ j, ∑ k, ∑ l, G i j k l r :=
    Finset.sum_comm
  calc (∑ i, ∑ j, ∑ k, ∑ l, ∑ r, G i j k l r)
      = ∑ i, ∑ j, ∑ k, ∑ r, ∑ l, G i j k l r := by simp only [h3]
    _ = ∑ i, ∑ j, ∑ r, ∑ k, ∑ l, G i j k l r := by simp only [h2]
    _ = ∑ i, ∑ r, ∑ j, ∑ k, ∑ l, G i j k l r := by simp only [h1]
    _ = ∑ r, ∑ i, ∑ j, ∑ k, ∑ l, G i j k l r := h0

/-- Updating a tuple at the image of `d` and restricting to the image of `d`. -/
theorem update_comp_same {N a : ℕ} (tup : Fin N → Work.Diff.EXT.TField (I := I) (M := M))
    (d : Fin a → Fin N) (hinj : Function.Injective d) (r : Fin a)
    (W : Work.Diff.EXT.TField (I := I) (M := M)) :
    (fun r' : Fin a => (Function.update tup (d r) W) (d r'))
      = Function.update (fun r' : Fin a => tup (d r')) r W := by
  funext r'
  rcases eq_or_ne r' r with h | h
  · subst h; rw [Function.update_self, Function.update_self]
  · rw [Function.update_of_ne (fun hh => h (hinj hh)) W tup, Function.update_of_ne h]

/-- Updating a tuple at the image of `d` and restricting to the image of `d'` (disjoint from `d`). -/
theorem update_comp_ne {N a a' : ℕ} (tup : Fin N → Work.Diff.EXT.TField (I := I) (M := M))
    (d : Fin a → Fin N) (d' : Fin a' → Fin N) (h : ∀ r r', d r ≠ d' r') (r : Fin a)
    (W : Work.Diff.EXT.TField (I := I) (M := M)) :
    (fun r' : Fin a' => (Function.update tup (d r) W) (d' r')) = fun r' => tup (d' r') := by
  funext r'
  rw [Function.update_of_ne (Ne.symm (h r r')) W tup]

/-! ## The Leibniz recursion of the monomial -/

theorem MonoD_extStep
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (y : M)
    (e : Fin (Module.finrank ℝ E) → Work.Diff.EXT.TField (I := I) (M := M))
    (he : ∀ i, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (e i))
    (hgeo : ∀ i, Submission.Diff.lcOf g (e i) y = 0)
    (N a b : ℕ) (hN : a + b + 4 = N)
    (d₁ : Fin a → Fin N) (d₂ : Fin b → Fin N) (s : Fin 4 → Fin N)
    (hinj₁ : Function.Injective d₁) (hinj₂ : Function.Injective d₂) (hinjs : Function.Injective s)
    (hd₁₂ : ∀ r r', d₁ r ≠ d₂ r') (hd₁s : ∀ r t, d₁ r ≠ s t) (hd₂s : ∀ r t, d₂ r ≠ s t)
    (hcov : ∀ u : Fin N, (∃ r, d₁ r = u) ∨ (∃ r, d₂ r = u) ∨ (∃ t, s t = u))
    (F : Fin (N + 1) → Work.Diff.EXT.TField (I := I) (M := M))
    (hF : ∀ u, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (F u)) :
    Work.Diff.EXT.extStep (I := I) (M := M) g
        (Work.Diff.EXT.MonoD (I := I) (M := M) g N a b d₁ d₂ s e) F y
      = Work.Diff.EXT.MonoD (I := I) (M := M) g (N + 1) (a + 1) b
          (Fin.cons 0 (fun r => (d₁ r).succ)) (fun r => (d₂ r).succ)
          (fun t => (s t).succ) e F y
        + Work.Diff.EXT.MonoD (I := I) (M := M) g (N + 1) a (b + 1)
          (fun r => (d₁ r).succ) (Fin.cons 0 (fun r => (d₂ r).succ))
          (fun t => (s t).succ) e F y := by
  classical
  let tup : Fin N → Work.Diff.EXT.TField (I := I) (M := M) := fun i => F i.succ
  let X : Work.Diff.EXT.TField (I := I) (M := M) := F 0
  let D₁ : Fin a → Work.Diff.EXT.TField (I := I) (M := M) := fun r => tup (d₁ r)
  let D₂ : Fin b → Work.Diff.EXT.TField (I := I) (M := M) := fun r => tup (d₂ r)
  let sl : Fin 4 → Work.Diff.EXT.TField (I := I) (M := M) := fun t => tup (s t)
  have htupsm : ∀ u, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (tup u) := fun u => hF u.succ
  have hXsm : Work.Diff.GE.SmoothFieldT (I := I) (M := M) X := hF 0
  have hD₁sm : ∀ r, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (D₁ r) :=
    fun r => htupsm (d₁ r)
  have hD₂sm : ∀ r, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (D₂ r) :=
    fun r => htupsm (d₂ r)
  have hslsm : ∀ t, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (sl t) :=
    fun t => htupsm (s t)
  -- differentiability of the two tower arrays and of the pairing product
  have hAd : ∀ p q r s, MDifferentiableAt I (modelWithCornersSelf ℝ ℝ)
      (fun z => Work.Diff.EXT.TowerArr g a D₁ e z p q r s) y := fun p q r s =>
    TowerArr_mdiffAt (I := I) (M := M) hLC g a D₁ hD₁sm e he y p q r s
  have hBd : ∀ p q r s, MDifferentiableAt I (modelWithCornersSelf ℝ ℝ)
      (fun z => Work.Diff.EXT.TowerArr g b D₂ e z p q r s) y := fun p q r s =>
    TowerArr_mdiffAt (I := I) (M := M) hLC g b D₂ hD₂sm e he y p q r s
  have hPd : ∀ p q r s, MDifferentiableAt I (modelWithCornersSelf ℝ ℝ)
      (pairProd (I := I) (M := M) g e sl p q r s) y := fun p q r s =>
    (((metricPairing_mdiffAt g (he p) (hslsm 0) y).mul
        (metricPairing_mdiffAt g (he q) (hslsm 1) y)).mul
        (metricPairing_mdiffAt g (he r) (hslsm 2) y)).mul
      (metricPairing_mdiffAt g (he s) (hslsm 3) y)
  -- the derivatives of the two tower arrays and of the pairing product
  have hAder :
      (fun p q r s => mvfderiv I (fun z => Work.Diff.EXT.TowerArr g a D₁ e z p q r s) y (X y))
        = Work.Diff.EXT.TowerArr g (a + 1) (Fin.cons X D₁) e y
          + ∑ r : Fin a, Work.Diff.EXT.TowerArr g a
              (Function.update D₁ r (Work.Diff.EXT.dirF g (D₁ r) X)) e y :=
    TowerArr_deriv_fun (I := I) (M := M) hLC g y e he hgeo a D₁ hD₁sm X hXsm
  have hBder :
      (fun p q r s => mvfderiv I (fun z => Work.Diff.EXT.TowerArr g b D₂ e z p q r s) y (X y))
        = Work.Diff.EXT.TowerArr g (b + 1) (Fin.cons X D₂) e y
          + ∑ r : Fin b, Work.Diff.EXT.TowerArr g b
              (Function.update D₂ r (Work.Diff.EXT.dirF g (D₂ r) X)) e y :=
    TowerArr_deriv_fun (I := I) (M := M) hLC g y e he hgeo b D₂ hD₂sm X hXsm
  have hPder : ∀ i j k l,
      (mvfderiv I (fun z => pairProd (I := I) (M := M) g e sl i j k l z) y) (X y)
        = ∑ t : Fin 4, pairProd (I := I) (M := M) g e
            (Function.update sl t (Work.Diff.EXT.dirF g (sl t) X)) i j k l y := by
    intro i j k l
    rw [pairProd_mvfderiv (I := I) (M := M) hLC g y e he hgeo sl hslsm X hXsm i j k l]
    rw [Fin.sum_univ_four]
    simp only [pairProd]
    rw [Function.update_self, Function.update_self, Function.update_self, Function.update_self,
      Function.update_of_ne (by decide : (0 : Fin 4) ≠ 1) _ sl,
      Function.update_of_ne (by decide : (0 : Fin 4) ≠ 2) _ sl,
      Function.update_of_ne (by decide : (0 : Fin 4) ≠ 3) _ sl,
      Function.update_of_ne (by decide : (1 : Fin 4) ≠ 0) _ sl,
      Function.update_of_ne (by decide : (1 : Fin 4) ≠ 2) _ sl,
      Function.update_of_ne (by decide : (1 : Fin 4) ≠ 3) _ sl,
      Function.update_of_ne (by decide : (2 : Fin 4) ≠ 0) _ sl,
      Function.update_of_ne (by decide : (2 : Fin 4) ≠ 1) _ sl,
      Function.update_of_ne (by decide : (2 : Fin 4) ≠ 3) _ sl,
      Function.update_of_ne (by decide : (3 : Fin 4) ≠ 0) _ sl,
      Function.update_of_ne (by decide : (3 : Fin 4) ≠ 1) _ sl,
      Function.update_of_ne (by decide : (3 : Fin 4) ≠ 2) _ sl]
    ring
  -- the derivative of the monomial
  have hM0 :
      (mvfderiv I (fun z => Work.Diff.EXT.MonoD (I := I) (M := M) g N a b d₁ d₂ s e tup z) y)
        (X y)
        = (∑ i, ∑ j, ∑ k, ∑ l, rmSym (Work.Diff.EXT.TowerArr g a D₁ e y)
              (Work.Diff.EXT.TowerArr g b D₂ e y) i j k l
            * (∑ t : Fin 4, pairProd (I := I) (M := M) g e
                (Function.update sl t (Work.Diff.EXT.dirF g (sl t) X)) i j k l y))
          + (∑ i, ∑ j, ∑ k, ∑ l,
              rmSym (Work.Diff.EXT.TowerArr g (a + 1) (Fin.cons X D₁) e y
                  + ∑ r : Fin a, Work.Diff.EXT.TowerArr g a
                      (Function.update D₁ r (Work.Diff.EXT.dirF g (D₁ r) X)) e y)
                (Work.Diff.EXT.TowerArr g b D₂ e y) i j k l
              * pairProd (I := I) (M := M) g e sl i j k l y)
          + (∑ i, ∑ j, ∑ k, ∑ l,
              rmSym (Work.Diff.EXT.TowerArr g a D₁ e y)
                (Work.Diff.EXT.TowerArr g (b + 1) (Fin.cons X D₂) e y
                  + ∑ r : Fin b, Work.Diff.EXT.TowerArr g b
                      (Function.update D₂ r (Work.Diff.EXT.dirF g (D₂ r) X)) e y) i j k l
              * pairProd (I := I) (M := M) g e sl i j k l y) := by
    rw [show (fun z => Work.Diff.EXT.MonoD (I := I) (M := M) g N a b d₁ d₂ s e tup z)
        = fun z => ∑ i, ∑ j, ∑ k, ∑ l,
            rmSym (Work.Diff.EXT.TowerArr g a D₁ e z) (Work.Diff.EXT.TowerArr g b D₂ e z)
              i j k l
            * pairProd (I := I) (M := M) g e sl i j k l z from by
      funext z
      exact MonoD_sum (I := I) (M := M) (g := g) (y := z) (e := e) d₁ d₂ s tup]
    exact mvfderiv_rmSym_contract (I := I) (M := M) (n := Module.finrank ℝ E)
      (A := fun z => Work.Diff.EXT.TowerArr g a D₁ e z)
      (B := fun z => Work.Diff.EXT.TowerArr g b D₂ e z)
      (P := fun i j k l z => pairProd (I := I) (M := M) g e sl i j k l z)
      y (X y)
      (dA := Work.Diff.EXT.TowerArr g (a + 1) (Fin.cons X D₁) e y
        + ∑ r : Fin a, Work.Diff.EXT.TowerArr g a
            (Function.update D₁ r (Work.Diff.EXT.dirF g (D₁ r) X)) e y)
      (dB := Work.Diff.EXT.TowerArr g (b + 1) (Fin.cons X D₂) e y
        + ∑ r : Fin b, Work.Diff.EXT.TowerArr g b
            (Function.update D₂ r (Work.Diff.EXT.dirF g (D₂ r) X)) e y)
      (dP := fun i j k l => ∑ t : Fin 4, pairProd (I := I) (M := M) g e
          (Function.update sl t (Work.Diff.EXT.dirF g (sl t) X)) i j k l y)
      (fun p q r s => congrFun (congrFun (congrFun (congrFun hAder p) q) r) s)
      (fun p q r s => congrFun (congrFun (congrFun (congrFun hBder p) q) r) s)
      hPder hAd hBd hPd
  -- the pairing-derivative group
  have hEterm :
      (∑ i, ∑ j, ∑ k, ∑ l, rmSym (Work.Diff.EXT.TowerArr g a D₁ e y)
            (Work.Diff.EXT.TowerArr g b D₂ e y) i j k l
          * (∑ t : Fin 4, pairProd (I := I) (M := M) g e
              (Function.update sl t (Work.Diff.EXT.dirF g (sl t) X)) i j k l y))
        = ∑ t : Fin 4, ∑ i, ∑ j, ∑ k, ∑ l,
            rmSym (Work.Diff.EXT.TowerArr g a D₁ e y) (Work.Diff.EXT.TowerArr g b D₂ e y)
              i j k l
            * pairProd (I := I) (M := M) g e
                (Function.update sl t (Work.Diff.EXT.dirF g (sl t) X)) i j k l y := by
    rw [show (∑ i, ∑ j, ∑ k, ∑ l, rmSym (Work.Diff.EXT.TowerArr g a D₁ e y)
            (Work.Diff.EXT.TowerArr g b D₂ e y) i j k l
          * (∑ t : Fin 4, pairProd (I := I) (M := M) g e
              (Function.update sl t (Work.Diff.EXT.dirF g (sl t) X)) i j k l y))
        = ∑ i, ∑ j, ∑ k, ∑ l, ∑ t : Fin 4,
            rmSym (Work.Diff.EXT.TowerArr g a D₁ e y) (Work.Diff.EXT.TowerArr g b D₂ e y)
              i j k l
            * pairProd (I := I) (M := M) g e
                (Function.update sl t (Work.Diff.EXT.dirF g (sl t) X)) i j k l y from by
      simp only [Finset.mul_sum]]
    exact sum4_comm_sum (fun i j k l (t : Fin 4) =>
      rmSym (Work.Diff.EXT.TowerArr g a D₁ e y) (Work.Diff.EXT.TowerArr g b D₂ e y) i j k l
        * pairProd (I := I) (M := M) g e
            (Function.update sl t (Work.Diff.EXT.dirF g (sl t) X)) i j k l y)
  -- the first-factor group
  have hAterm :
      (∑ i, ∑ j, ∑ k, ∑ l,
          rmSym (Work.Diff.EXT.TowerArr g (a + 1) (Fin.cons X D₁) e y
              + ∑ r : Fin a, Work.Diff.EXT.TowerArr g a
                  (Function.update D₁ r (Work.Diff.EXT.dirF g (D₁ r) X)) e y)
            (Work.Diff.EXT.TowerArr g b D₂ e y) i j k l
          * pairProd (I := I) (M := M) g e sl i j k l y)
        = (∑ i, ∑ j, ∑ k, ∑ l, rmSym (Work.Diff.EXT.TowerArr g (a + 1) (Fin.cons X D₁) e y)
              (Work.Diff.EXT.TowerArr g b D₂ e y) i j k l
            * pairProd (I := I) (M := M) g e sl i j k l y)
          + (∑ r : Fin a, ∑ i, ∑ j, ∑ k, ∑ l,
              rmSym (Work.Diff.EXT.TowerArr g a
                    (Function.update D₁ r (Work.Diff.EXT.dirF g (D₁ r) X)) e y)
                (Work.Diff.EXT.TowerArr g b D₂ e y) i j k l
              * pairProd (I := I) (M := M) g e sl i j k l y) := by
    rw [show (∑ i, ∑ j, ∑ k, ∑ l,
          rmSym (Work.Diff.EXT.TowerArr g (a + 1) (Fin.cons X D₁) e y
              + ∑ r : Fin a, Work.Diff.EXT.TowerArr g a
                  (Function.update D₁ r (Work.Diff.EXT.dirF g (D₁ r) X)) e y)
            (Work.Diff.EXT.TowerArr g b D₂ e y) i j k l
          * pairProd (I := I) (M := M) g e sl i j k l y)
        = (∑ i, ∑ j, ∑ k, ∑ l, rmSym (Work.Diff.EXT.TowerArr g (a + 1) (Fin.cons X D₁) e y)
              (Work.Diff.EXT.TowerArr g b D₂ e y) i j k l
            * pairProd (I := I) (M := M) g e sl i j k l y)
          + (∑ i, ∑ j, ∑ k, ∑ l,
              rmSym (∑ r : Fin a, Work.Diff.EXT.TowerArr g a
                    (Function.update D₁ r (Work.Diff.EXT.dirF g (D₁ r) X)) e y)
                  (Work.Diff.EXT.TowerArr g b D₂ e y) i j k l
              * pairProd (I := I) (M := M) g e sl i j k l y) from by
      simp only [Work.Diff.EXT.evX.rmSym_add_left, Pi.add_apply, add_mul,
        Finset.sum_add_distrib]]
    rw [show (∑ i, ∑ j, ∑ k, ∑ l,
          rmSym (∑ r : Fin a, Work.Diff.EXT.TowerArr g a
                (Function.update D₁ r (Work.Diff.EXT.dirF g (D₁ r) X)) e y)
              (Work.Diff.EXT.TowerArr g b D₂ e y) i j k l
          * pairProd (I := I) (M := M) g e sl i j k l y)
        = ∑ r : Fin a, ∑ i, ∑ j, ∑ k, ∑ l,
            rmSym (Work.Diff.EXT.TowerArr g a
                  (Function.update D₁ r (Work.Diff.EXT.dirF g (D₁ r) X)) e y)
                (Work.Diff.EXT.TowerArr g b D₂ e y) i j k l
            * pairProd (I := I) (M := M) g e sl i j k l y from by
      rw [show (∑ i, ∑ j, ∑ k, ∑ l,
            rmSym (∑ r : Fin a, Work.Diff.EXT.TowerArr g a
                  (Function.update D₁ r (Work.Diff.EXT.dirF g (D₁ r) X)) e y)
                (Work.Diff.EXT.TowerArr g b D₂ e y) i j k l
            * pairProd (I := I) (M := M) g e sl i j k l y)
          = ∑ i, ∑ j, ∑ k, ∑ l, ∑ r : Fin a,
              rmSym (Work.Diff.EXT.TowerArr g a
                    (Function.update D₁ r (Work.Diff.EXT.dirF g (D₁ r) X)) e y)
                  (Work.Diff.EXT.TowerArr g b D₂ e y) i j k l
              * pairProd (I := I) (M := M) g e sl i j k l y from by
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ =>
          Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))))
        rw [rmSym_sum_left (Finset.univ)
          (fun r : Fin a => Work.Diff.EXT.TowerArr g a
            (Function.update D₁ r (Work.Diff.EXT.dirF g (D₁ r) X)) e y)
          (Work.Diff.EXT.TowerArr g b D₂ e y)]
        rw [sum_app4]
        rw [Finset.sum_mul]]
      exact sum4_comm_sum (fun i j k l (r : Fin a) =>
        rmSym (Work.Diff.EXT.TowerArr g a
              (Function.update D₁ r (Work.Diff.EXT.dirF g (D₁ r) X)) e y)
            (Work.Diff.EXT.TowerArr g b D₂ e y) i j k l
          * pairProd (I := I) (M := M) g e sl i j k l y)]
  -- the second-factor group
  have hBterm :
      (∑ i, ∑ j, ∑ k, ∑ l,
          rmSym (Work.Diff.EXT.TowerArr g a D₁ e y)
            (Work.Diff.EXT.TowerArr g (b + 1) (Fin.cons X D₂) e y
              + ∑ r : Fin b, Work.Diff.EXT.TowerArr g b
                  (Function.update D₂ r (Work.Diff.EXT.dirF g (D₂ r) X)) e y) i j k l
          * pairProd (I := I) (M := M) g e sl i j k l y)
        = (∑ i, ∑ j, ∑ k, ∑ l, rmSym (Work.Diff.EXT.TowerArr g a D₁ e y)
              (Work.Diff.EXT.TowerArr g (b + 1) (Fin.cons X D₂) e y) i j k l
            * pairProd (I := I) (M := M) g e sl i j k l y)
          + (∑ r : Fin b, ∑ i, ∑ j, ∑ k, ∑ l,
              rmSym (Work.Diff.EXT.TowerArr g a D₁ e y)
                (Work.Diff.EXT.TowerArr g b
                  (Function.update D₂ r (Work.Diff.EXT.dirF g (D₂ r) X)) e y) i j k l
              * pairProd (I := I) (M := M) g e sl i j k l y) := by
    rw [show (∑ i, ∑ j, ∑ k, ∑ l,
          rmSym (Work.Diff.EXT.TowerArr g a D₁ e y)
            (Work.Diff.EXT.TowerArr g (b + 1) (Fin.cons X D₂) e y
              + ∑ r : Fin b, Work.Diff.EXT.TowerArr g b
                  (Function.update D₂ r (Work.Diff.EXT.dirF g (D₂ r) X)) e y) i j k l
          * pairProd (I := I) (M := M) g e sl i j k l y)
        = (∑ i, ∑ j, ∑ k, ∑ l, rmSym (Work.Diff.EXT.TowerArr g a D₁ e y)
              (Work.Diff.EXT.TowerArr g (b + 1) (Fin.cons X D₂) e y) i j k l
            * pairProd (I := I) (M := M) g e sl i j k l y)
          + (∑ i, ∑ j, ∑ k, ∑ l,
              rmSym (Work.Diff.EXT.TowerArr g a D₁ e y)
                (∑ r : Fin b, Work.Diff.EXT.TowerArr g b
                  (Function.update D₂ r (Work.Diff.EXT.dirF g (D₂ r) X)) e y) i j k l
              * pairProd (I := I) (M := M) g e sl i j k l y) from by
      simp only [Work.Diff.EXT.evX.rmSym_add_right, Pi.add_apply, add_mul,
        Finset.sum_add_distrib]]
    rw [show (∑ i, ∑ j, ∑ k, ∑ l,
          rmSym (Work.Diff.EXT.TowerArr g a D₁ e y)
              (∑ r : Fin b, Work.Diff.EXT.TowerArr g b
                (Function.update D₂ r (Work.Diff.EXT.dirF g (D₂ r) X)) e y) i j k l
          * pairProd (I := I) (M := M) g e sl i j k l y)
        = ∑ r : Fin b, ∑ i, ∑ j, ∑ k, ∑ l,
            rmSym (Work.Diff.EXT.TowerArr g a D₁ e y)
              (Work.Diff.EXT.TowerArr g b
                (Function.update D₂ r (Work.Diff.EXT.dirF g (D₂ r) X)) e y) i j k l
            * pairProd (I := I) (M := M) g e sl i j k l y from by
      rw [show (∑ i, ∑ j, ∑ k, ∑ l,
            rmSym (Work.Diff.EXT.TowerArr g a D₁ e y)
                (∑ r : Fin b, Work.Diff.EXT.TowerArr g b
                  (Function.update D₂ r (Work.Diff.EXT.dirF g (D₂ r) X)) e y) i j k l
            * pairProd (I := I) (M := M) g e sl i j k l y)
          = ∑ i, ∑ j, ∑ k, ∑ l, ∑ r : Fin b,
              rmSym (Work.Diff.EXT.TowerArr g a D₁ e y)
                (Work.Diff.EXT.TowerArr g b
                  (Function.update D₂ r (Work.Diff.EXT.dirF g (D₂ r) X)) e y) i j k l
              * pairProd (I := I) (M := M) g e sl i j k l y from by
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ =>
          Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))))
        rw [rmSym_sum_right (Finset.univ)
          (Work.Diff.EXT.TowerArr g a D₁ e y)
          (fun r : Fin b => Work.Diff.EXT.TowerArr g b
            (Function.update D₂ r (Work.Diff.EXT.dirF g (D₂ r) X)) e y)]
        rw [sum_app4]
        rw [Finset.sum_mul]]
      exact sum4_comm_sum (fun i j k l (r : Fin b) =>
        rmSym (Work.Diff.EXT.TowerArr g a D₁ e y)
              (Work.Diff.EXT.TowerArr g b
                (Function.update D₂ r (Work.Diff.EXT.dirF g (D₂ r) X)) e y) i j k l
          * pairProd (I := I) (M := M) g e sl i j k l y)]
  -- the two children of the monomial
  have hchild1 : Work.Diff.EXT.MonoD (I := I) (M := M) g (N + 1) (a + 1) b
        (Fin.cons 0 (fun r => (d₁ r).succ)) (fun r => (d₂ r).succ) (fun t => (s t).succ) e F y
      = ∑ i, ∑ j, ∑ k, ∑ l, rmSym (Work.Diff.EXT.TowerArr g (a + 1) (Fin.cons X D₁) e y)
            (Work.Diff.EXT.TowerArr g b D₂ e y) i j k l
          * pairProd (I := I) (M := M) g e sl i j k l y := by
    rw [MonoD_sum (I := I) (M := M) (g := g) (y := y) (e := e) (N := N + 1) (a := a + 1) (b := b)
      (d₁ := (Fin.cons 0 (fun r : Fin a => (d₁ r).succ) : Fin (a + 1) → Fin (N + 1)))
      (d₂ := fun r => (d₂ r).succ) (s := fun t => (s t).succ) (G := F)]
    have h1 : (fun r : Fin (a + 1) =>
          F ((Fin.cons 0 (fun r' : Fin a => (d₁ r').succ) : Fin (a + 1) → Fin (N + 1)) r))
        = (Fin.cons X D₁ : Fin (a + 1) → Work.Diff.EXT.TField (I := I) (M := M)) := by
      funext r
      refine Fin.cases ?_ ?_ r
      · rfl
      · intro r'; rfl
    have h2 : (fun r : Fin b => F ((d₂ r).succ)) = D₂ := rfl
    have h3 : (fun t : Fin 4 => F ((s t).succ)) = sl := rfl
    rw [h1, h2, h3]
  have hchild2 : Work.Diff.EXT.MonoD (I := I) (M := M) g (N + 1) a (b + 1)
        (fun r => (d₁ r).succ) (Fin.cons 0 (fun r => (d₂ r).succ)) (fun t => (s t).succ) e F y
      = ∑ i, ∑ j, ∑ k, ∑ l, rmSym (Work.Diff.EXT.TowerArr g a D₁ e y)
            (Work.Diff.EXT.TowerArr g (b + 1) (Fin.cons X D₂) e y) i j k l
          * pairProd (I := I) (M := M) g e sl i j k l y := by
    rw [MonoD_sum (I := I) (M := M) (g := g) (y := y) (e := e) (N := N + 1) (a := a) (b := b + 1)
      (d₁ := fun r => (d₁ r).succ)
      (d₂ := (Fin.cons 0 (fun r : Fin b => (d₂ r).succ) : Fin (b + 1) → Fin (N + 1)))
      (s := fun t => (s t).succ) (G := F)]
    have h1 : (fun r : Fin a => F ((d₁ r).succ)) = D₁ := rfl
    have h2 : (fun r : Fin (b + 1) =>
          F ((Fin.cons 0 (fun r' : Fin b => (d₂ r').succ) : Fin (b + 1) → Fin (N + 1)) r))
        = (Fin.cons X D₂ : Fin (b + 1) → Work.Diff.EXT.TField (I := I) (M := M)) := by
      funext r
      refine Fin.cases ?_ ?_ r
      · rfl
      · intro r'; rfl
    have h3 : (fun t : Fin 4 => F ((s t).succ)) = sl := rfl
    rw [h1, h2, h3]
  -- the correction sum of `extStep`, slot by slot
  have hΦ₁ : ∀ r₀ : Fin a, Work.Diff.EXT.MonoD (I := I) (M := M) g N a b d₁ d₂ s e
        (Function.update tup (d₁ r₀) (Work.Diff.EXT.dirF g (tup (d₁ r₀)) X)) y
      = ∑ i, ∑ j, ∑ k, ∑ l,
          rmSym (Work.Diff.EXT.TowerArr g a
                (Function.update D₁ r₀ (Work.Diff.EXT.dirF g (D₁ r₀) X)) e y)
            (Work.Diff.EXT.TowerArr g b D₂ e y) i j k l
          * pairProd (I := I) (M := M) g e sl i j k l y := by
    intro r₀
    rw [MonoD_sum (I := I) (M := M) (g := g) (y := y) (e := e) (N := N) (a := a) (b := b)
      (d₁ := d₁) (d₂ := d₂) (s := s)
      (G := Function.update tup (d₁ r₀) (Work.Diff.EXT.dirF g (tup (d₁ r₀)) X))]
    rw [update_comp_same (I := I) (M := M) tup d₁ hinj₁ r₀
        (Work.Diff.EXT.dirF g (tup (d₁ r₀)) X),
      update_comp_ne (I := I) (M := M) tup d₁ d₂ hd₁₂ r₀
        (Work.Diff.EXT.dirF g (tup (d₁ r₀)) X),
      update_comp_ne (I := I) (M := M) tup d₁ s hd₁s r₀
        (Work.Diff.EXT.dirF g (tup (d₁ r₀)) X)]
  have hΦ₂ : ∀ r₀ : Fin b, Work.Diff.EXT.MonoD (I := I) (M := M) g N a b d₁ d₂ s e
        (Function.update tup (d₂ r₀) (Work.Diff.EXT.dirF g (tup (d₂ r₀)) X)) y
      = ∑ i, ∑ j, ∑ k, ∑ l,
          rmSym (Work.Diff.EXT.TowerArr g a D₁ e y)
            (Work.Diff.EXT.TowerArr g b
              (Function.update D₂ r₀ (Work.Diff.EXT.dirF g (D₂ r₀) X)) e y) i j k l
          * pairProd (I := I) (M := M) g e sl i j k l y := by
    intro r₀
    rw [MonoD_sum (I := I) (M := M) (g := g) (y := y) (e := e) (N := N) (a := a) (b := b)
      (d₁ := d₁) (d₂ := d₂) (s := s)
      (G := Function.update tup (d₂ r₀) (Work.Diff.EXT.dirF g (tup (d₂ r₀)) X))]
    rw [update_comp_ne (I := I) (M := M) tup d₂ d₁ (fun r r' => (hd₁₂ r' r).symm) r₀
        (Work.Diff.EXT.dirF g (tup (d₂ r₀)) X),
      update_comp_same (I := I) (M := M) tup d₂ hinj₂ r₀
        (Work.Diff.EXT.dirF g (tup (d₂ r₀)) X),
      update_comp_ne (I := I) (M := M) tup d₂ s hd₂s r₀
        (Work.Diff.EXT.dirF g (tup (d₂ r₀)) X)]
  have hΦ₃ : ∀ t₀ : Fin 4, Work.Diff.EXT.MonoD (I := I) (M := M) g N a b d₁ d₂ s e
        (Function.update tup (s t₀) (Work.Diff.EXT.dirF g (tup (s t₀)) X)) y
      = ∑ i, ∑ j, ∑ k, ∑ l,
          rmSym (Work.Diff.EXT.TowerArr g a D₁ e y) (Work.Diff.EXT.TowerArr g b D₂ e y)
            i j k l
          * pairProd (I := I) (M := M) g e
              (Function.update sl t₀ (Work.Diff.EXT.dirF g (sl t₀) X)) i j k l y := by
    intro t₀
    rw [MonoD_sum (I := I) (M := M) (g := g) (y := y) (e := e) (N := N) (a := a) (b := b)
      (d₁ := d₁) (d₂ := d₂) (s := s)
      (G := Function.update tup (s t₀) (Work.Diff.EXT.dirF g (tup (s t₀)) X))]
    rw [update_comp_ne (I := I) (M := M) tup s d₁ (fun t r => (hd₁s r t).symm) t₀
        (Work.Diff.EXT.dirF g (tup (s t₀)) X),
      update_comp_ne (I := I) (M := M) tup s d₂ (fun t r => (hd₂s r t).symm) t₀
        (Work.Diff.EXT.dirF g (tup (s t₀)) X),
      update_comp_same (I := I) (M := M) tup s hinjs t₀
        (Work.Diff.EXT.dirF g (tup (s t₀)) X)]
  have hCS : (∑ u : Fin N, Work.Diff.EXT.MonoD (I := I) (M := M) g N a b d₁ d₂ s e
        (Function.update tup u (Work.Diff.EXT.dirF g (tup u) X)) y)
      = (∑ r : Fin a, ∑ i, ∑ j, ∑ k, ∑ l,
            rmSym (Work.Diff.EXT.TowerArr g a
                  (Function.update D₁ r (Work.Diff.EXT.dirF g (D₁ r) X)) e y)
                (Work.Diff.EXT.TowerArr g b D₂ e y) i j k l
            * pairProd (I := I) (M := M) g e sl i j k l y)
        + (∑ r : Fin b, ∑ i, ∑ j, ∑ k, ∑ l,
            rmSym (Work.Diff.EXT.TowerArr g a D₁ e y)
              (Work.Diff.EXT.TowerArr g b
                (Function.update D₂ r (Work.Diff.EXT.dirF g (D₂ r) X)) e y) i j k l
            * pairProd (I := I) (M := M) g e sl i j k l y)
        + (∑ t : Fin 4, ∑ i, ∑ j, ∑ k, ∑ l,
            rmSym (Work.Diff.EXT.TowerArr g a D₁ e y) (Work.Diff.EXT.TowerArr g b D₂ e y)
              i j k l
            * pairProd (I := I) (M := M) g e
                (Function.update sl t (Work.Diff.EXT.dirF g (sl t) X)) i j k l y) := by
    rw [sum_over_partition d₁ d₂ s hinj₁ hinj₂ hinjs hd₁₂ hd₁s hd₂s hcov
      (fun u => Work.Diff.EXT.MonoD (I := I) (M := M) g N a b d₁ d₂ s e
        (Function.update tup u (Work.Diff.EXT.dirF g (tup u) X)) y)]
    simp only [hΦ₁, hΦ₂, hΦ₃]
  -- assembly
  have hmain :
      (mvfderiv I (fun z => Work.Diff.EXT.MonoD (I := I) (M := M) g N a b d₁ d₂ s e tup z) y)
          (X y)
        = Work.Diff.EXT.MonoD (I := I) (M := M) g (N + 1) (a + 1) b
            (Fin.cons 0 (fun r => (d₁ r).succ)) (fun r => (d₂ r).succ)
            (fun t => (s t).succ) e F y
          + Work.Diff.EXT.MonoD (I := I) (M := M) g (N + 1) a (b + 1)
            (fun r => (d₁ r).succ) (Fin.cons 0 (fun r => (d₂ r).succ))
            (fun t => (s t).succ) e F y
          + ∑ u : Fin N, Work.Diff.EXT.MonoD (I := I) (M := M) g N a b d₁ d₂ s e
              (Function.update tup u (Work.Diff.EXT.dirF g (tup u) X)) y := by
    rw [hM0, hEterm, hAterm, hBterm, hchild1.symm, hchild2.symm, hCS]
    ring
  rw [show Work.Diff.EXT.extStep (I := I) (M := M) g
        (Work.Diff.EXT.MonoD (I := I) (M := M) g N a b d₁ d₂ s e) F y
      = (mvfderiv I (fun z => Work.Diff.EXT.MonoD (I := I) (M := M) g N a b d₁ d₂ s e
            tup z) y) (X y)
        - ∑ u : Fin N, Work.Diff.EXT.MonoD (I := I) (M := M) g N a b d₁ d₂ s e
            (Function.update tup u (Work.Diff.EXT.dirF g (tup u) X)) y from rfl]
  rw [hmain]
  ring

end Work.Diff.EXT.Mono
