import Mathlib
import Submission.Work.Diff.EXT.ChartCoreDefs
import Submission.Work.Diff.GE.chartcalc
import Submission.Work.Diff.GE.norms_defs
import Submission.Work.Diff.GE.koszul
import Submission.Work.Diff.GE.cGram_chrB_eq_koszulPair
import Submission.Work.Diff.T.mvfderiv_frameVector_real
import Submission.Work.Diff.GE.curvbasic
import Submission.Work.Diff.T.lc_smooth
import Submission.Work.Diff.EXT.contMDiffAt_mvfderiv_gen

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Submission.Geodesic Submission.ChartCurv Work.Diff.GE

namespace Work.Diff.EXT

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  [I.Boundaryless] [T2Space M]

/-! ## The framework: tangent fields and smoothness on an open set -/

/-- Tangent fields on `M`. -/
abbrev KaTF := Π y : M, TangentSpace I y

/-- `C^∞`-smoothness of a tangent field on a set, in the tangent bundle model. -/
def KaSm (U : Set M) (X : KaTF (I := I) (M := M)) : Prop := CMDiff[U] ∞ (T% X)

/-- The Levi-Civita connection of a smooth metric is smooth. -/
theorem ka_lcSmooth (g : Submission.Diff.SMet I M) :
    Nonempty (ContMDiffCovariantDerivative (Submission.Diff.lcOf g) ∞) :=
  (Work.Diff.T.lc_smooth (I := I) (M := M) g).1

/-- The Levi-Civita connection of a smooth metric is torsion-free. -/
theorem ka_lcTor (g : Submission.Diff.SMet I M) :
    (Submission.Diff.lcOf g).torsion = 0 :=
  (Work.Diff.T.lc_smooth (I := I) (M := M) g).2.1

/-- Unfolding of the recursion `covKAExt` at `k+1`. -/
theorem ka_covKAExt_succ (G : ℝ → Submission.Diff.SMet I M) (t : ℝ) (k : ℕ)
    (v : Fin (k+1) → KaTF (I := I) (M := M))
    (A B C : KaTF (I := I) (M := M)) :
    covKAExt G t (k+1) v A B C = fun x =>
      mvfderiv I (covKAExt G t k (fun i : Fin k => v i.succ) A B C) x (v 0 x)
        - ∑ i : Fin k, covKAExt G t k
            (Function.update (fun j : Fin k => v j.succ) i
              (fun y => Submission.Diff.lcOf (G 0) (v i.succ) y (v 0 y))) A B C x
        - covKAExt G t k (fun i : Fin k => v i.succ)
            (fun y => Submission.Diff.lcOf (G 0) A y (v 0 y)) B C x
        - covKAExt G t k (fun i : Fin k => v i.succ) A
            (fun y => Submission.Diff.lcOf (G 0) B y (v 0 y)) C x
        - covKAExt G t k (fun i : Fin k => v i.succ) A B
            (fun y => Submission.Diff.lcOf (G 0) C y (v 0 y)) x := by
  funext x
  simp only [covKAExt]

/-! ## The chart formula for `∇` on the coordinate frame -/

/-- The chart Christoffel symbols are symmetric in their two lower indices (torsion-freeness
of the Levi-Civita connection). -/
lemma ka_cGam_comm (g : Submission.Diff.SMet I M) (x₀ p : M)
    (hp : p ∈ (chartAt H x₀).source) (k i j : Fin (Module.finrank ℝ E)) :
    Work.Diff.GE.cGam g x₀ p k i j = Work.Diff.GE.cGam g x₀ p k j i := by
  letI : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M => TangentSpace I x) := inferInstance
  have htor : (Submission.Diff.lcOf g).torsion = 0 := ka_lcTor g
  have h := christoffelEval_comm (cov := Submission.Diff.lcOf g) htor x₀ p hp
    (Work.Diff.GE.cBasis (E := E) i) (Work.Diff.GE.cBasis (E := E) j)
  simp only [Work.Diff.GE.cGam, chrB_apply]
  rw [h]

/-- **The chart formula for `∇` of the coordinate frame.** `∇_{σ_b}σ_a = ∑_k Γ^k_{ba}σ_k`. -/
lemma ka_lcOf_cFrame (g : Submission.Diff.SMet I M) (x₀ p : M)
    (hp : p ∈ (chartAt H x₀).source) (a b : Fin (Module.finrank ℝ E)) :
    Submission.Diff.lcOf g (Work.Diff.GE.cFrame (I := I) x₀ a) p
        (Work.Diff.GE.cFrame (I := I) x₀ b p)
      = ∑ k, Work.Diff.GE.cGam g x₀ p k b a • Work.Diff.GE.cFrame (I := I) x₀ k p := by
  letI : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M => TangentSpace I x) := inferInstance
  have h1 := cov_frameSection_eq (Submission.Diff.lcOf g) x₀ p
      (Work.Diff.GE.cBasis (E := E) a)
      (frameVector (I := I) x₀ p (Work.Diff.GE.cBasis (E := E) b)) hp
  have h2 : Submission.Diff.lcOf g (Work.Diff.GE.cFrame (I := I) x₀ a) p
        (Work.Diff.GE.cFrame (I := I) x₀ b p)
      = frameVector (I := I) x₀ p
          (christoffelEval (Submission.Diff.lcOf g) x₀ p (Work.Diff.GE.cBasis (E := E) a)
            (frameVector (I := I) x₀ p (Work.Diff.GE.cBasis (E := E) b))) := h1
  rw [h2]
  conv_lhs => rw [← sum_coord_smul_eq
    (christoffelEval (Submission.Diff.lcOf g) x₀ p (Work.Diff.GE.cBasis (E := E) a)
      (frameVector (I := I) x₀ p (Work.Diff.GE.cBasis (E := E) b)))]
  rw [frameVector_sum]
  apply Finset.sum_congr rfl
  intro k _
  congr 1

/-- The `∇_{σ_b}σ_a` expansion with the two lower indices in the order used by the chart
recursion. -/
lemma ka_lcOf_cFrame' (g : Submission.Diff.SMet I M) (x₀ p : M)
    (hp : p ∈ (chartAt H x₀).source) (a b : Fin (Module.finrank ℝ E)) :
    Submission.Diff.lcOf g (Work.Diff.GE.cFrame (I := I) x₀ a) p
        (Work.Diff.GE.cFrame (I := I) x₀ b p)
      = ∑ k, Work.Diff.GE.cGam g x₀ p k a b • Work.Diff.GE.cFrame (I := I) x₀ k p := by
  rw [ka_lcOf_cFrame (I := I) g x₀ p hp a b]
  apply Finset.sum_congr rfl
  intro k _
  rw [ka_cGam_comm (I := I) g x₀ p hp k b a]

/-- The coordinate frame is smooth at the points of the chart source. -/
lemma ka_cFrame_contMDiffAt (x₀ : M) (i : Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ (chartAt H x₀).source) :
    ContMDiffAt I I.tangent ∞ (T% (Work.Diff.GE.cFrame (I := I) x₀ i)) x := by
  rw [Trivialization.contMDiffAt_section_iff
    (trivializationAt E (TangentSpace I) x₀) (by simpa using hx)]
  refine (contMDiffAt_const (c := Work.Diff.GE.cBasis (E := E) i)).congr_of_eventuallyEq ?_
  filter_upwards [(trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds
    (by simpa using hx)] with y hy
  rw [show Work.Diff.GE.cFrame (I := I) x₀ i y
      = (trivializationAt E (TangentSpace I) x₀).symmL ℝ y (Work.Diff.GE.cBasis (E := E) i)
      from rfl]
  rw [Trivialization.symmL_apply (e := trivializationAt E (TangentSpace I) x₀) (R := ℝ) hy
    (Work.Diff.GE.cBasis (E := E) i)]
  exact congrArg Prod.snd ((trivializationAt E (TangentSpace I) x₀).apply_mk_symm hy
    (Work.Diff.GE.cBasis (E := E) i))

/-- The coordinate frame is smooth on the chart source. -/
lemma ka_smooth_cFrame (x₀ : M) (i : Fin (Module.finrank ℝ E)) :
    KaSm (I := I) (M := M) (chartAt H x₀).source (Work.Diff.GE.cFrame (I := I) x₀ i) := by
  intro x hx
  exact (ka_cFrame_contMDiffAt (I := I) x₀ i hx).contMDiffWithinAt

/-- The coordinate entries of the chart Christoffel symbols are smooth on the chart source. -/
lemma ka_cGam_smooth (g : Submission.Diff.SMet I M) (x₀ : M)
    (k a b : Fin (Module.finrank ℝ E)) :
    CMDiff[(chartAt H x₀).source] ∞ (fun y => Work.Diff.GE.cGam g x₀ y k a b) := by
  letI : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M => TangentSpace I x) := inferInstance
  haveI : ContMDiffCovariantDerivative (Submission.Diff.lcOf g) ∞ := (ka_lcSmooth g).some
  have h1 : CMDiff[(chartAt H x₀).source] ∞
      (gammaEntry (Submission.Diff.lcOf g) x₀ b a) :=
    contMDiffOn_gammaEntry x₀ b a
  have h2 : CMDiff[(chartAt H x₀).source] ∞
      (fun y => ((Work.Diff.GE.cBasis (E := E)).coord k)
        (gammaEntry (Submission.Diff.lcOf g) x₀ b a y)) :=
    (ContinuousLinearMap.contMDiff
      (((Work.Diff.GE.cBasis (E := E)).coord k : E →ₗ[ℝ] ℝ).toContinuousLinearMap)).comp_contMDiffOn h1
  refine h2.congr (fun y hy => ?_)
  simp only [Work.Diff.GE.cGam, gammaEntry_apply, chrB_apply]

/-- The covariant derivative of a smooth field along a smooth direction is smooth. -/
lemma ka_lcField_smooth (g : Submission.Diff.SMet I M) {U : Set M} (hU : IsOpen U)
    {Y Z : KaTF (I := I) (M := M)} (hY : KaSm (I := I) (M := M) U Y)
    (hZ : KaSm (I := I) (M := M) U Z) :
    KaSm (I := I) (M := M) U (fun y => Submission.Diff.lcOf g Y y (Z y)) := by
  letI : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M => TangentSpace I x) := inferInstance
  haveI : ContMDiffCovariantDerivative (Submission.Diff.lcOf g) ∞ := (ka_lcSmooth g).some
  have h := Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiffOn_cov_apply
    (Submission.Diff.lcOf g) inferInstance hU hY hZ
  simpa only [KaSm] using h

/-- `mvfderiv` applied to a smooth function and a smooth field is smooth. -/
lemma ka_mvfderiv_apply {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : Set M} (hU : IsOpen U) {f : M → F} {X : KaTF (I := I) (M := M)}
    (hf : CMDiff[U] ∞ f) (hX : KaSm (I := I) (M := M) U X) :
    CMDiff[U] ∞ (fun y => mvfderiv I f y (X y)) := by
  intro y hy
  exact (contMDiffAt_mvfderiv_gen (I := I) (f := f) (X := X)
    ((hf y hy).contMDiffAt (hU.mem_nhds hy))
    ((hX y hy).contMDiffAt (hU.mem_nhds hy))).contMDiffWithinAt

/-- The metric pairing of two smooth fields is smooth. -/
lemma ka_metric_pairing_smooth (g : Submission.Diff.SMet I M) {U : Set M}
    {Y Z : KaTF (I := I) (M := M)} (hY : KaSm (I := I) (M := M) U Y)
    (hZ : KaSm (I := I) (M := M) U Z) :
    CMDiff[U] ∞ (fun y => g.inner y (Y y) (Z y)) := by
  intro y hy
  have hψ : ContMDiffWithinAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun m : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) m (g.inner m))
      U y := (g.contMDiff (x := y)).contMDiffWithinAt
  have hmain : ContMDiffWithinAt I (I.prod 𝓘(ℝ, ℝ)) ∞
      (fun m : M => TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) m (g.inner m (Y m) (Z m)))
      U y :=
    ContMDiffWithinAt.clm_bundle_apply₂ (𝕜 := ℝ) (B := M) (F₁ := E) (F₂ := E) (F₃ := ℝ)
      (E₁ := fun x : M => TangentSpace I x) (E₂ := fun x : M => TangentSpace I x)
      (E₃ := Bundle.Trivial M ℝ) (b := fun m : M => m)
      (v := Y) (w := Z) (ψ := fun m : M => g.inner m) (s := U) (x := y)
      hψ (hY y hy) (hZ y hy)
  simp only [contMDiffWithinAt_totalSpace] at hmain
  exact hmain.2

/-! ## `KKT`: `covKAExt` with the tensor slots packaged as a `Fin 3`-tuple -/

/-- `covKAExt` with the three tensor slots packaged as a `Fin 3`-tuple. -/
noncomputable def KKT (G : ℝ → Submission.Diff.SMet I M) (t : ℝ) (k : ℕ)
    (w : Fin k → KaTF (I := I) (M := M)) (t3 : Fin 3 → KaTF (I := I) (M := M)) : M → ℝ :=
  covKAExt G t k w (t3 0) (t3 1) (t3 2)

/-- The tail of a family of `k+1` direction fields. -/
noncomputable def KaTail {k : ℕ} (w : Fin (k+1) → KaTF (I := I) (M := M)) :
    Fin k → KaTF (I := I) (M := M) := fun i => w i.succ

lemma KaTail_apply {k : ℕ} (w : Fin (k+1) → KaTF (I := I) (M := M)) (i : Fin k) :
    KaTail w i = w i.succ := rfl

@[simp] lemma ka_upd0_1 (t3 : Fin 3 → KaTF (I := I) (M := M)) (F : KaTF (I := I) (M := M)) :
    (Function.update t3 (0 : Fin 3) F) 1 = t3 1 := by
  rw [Function.update_apply]
  exact if_neg (by decide)

@[simp] lemma ka_upd0_2 (t3 : Fin 3 → KaTF (I := I) (M := M)) (F : KaTF (I := I) (M := M)) :
    (Function.update t3 (0 : Fin 3) F) 2 = t3 2 := by
  rw [Function.update_apply]
  exact if_neg (by decide)

@[simp] lemma ka_upd1_0 (t3 : Fin 3 → KaTF (I := I) (M := M)) (F : KaTF (I := I) (M := M)) :
    (Function.update t3 (1 : Fin 3) F) 0 = t3 0 := by
  rw [Function.update_apply]
  exact if_neg (by decide)

@[simp] lemma ka_upd1_2 (t3 : Fin 3 → KaTF (I := I) (M := M)) (F : KaTF (I := I) (M := M)) :
    (Function.update t3 (1 : Fin 3) F) 2 = t3 2 := by
  rw [Function.update_apply]
  exact if_neg (by decide)

@[simp] lemma ka_upd2_0 (t3 : Fin 3 → KaTF (I := I) (M := M)) (F : KaTF (I := I) (M := M)) :
    (Function.update t3 (2 : Fin 3) F) 0 = t3 0 := by
  rw [Function.update_apply]
  exact if_neg (by decide)

@[simp] lemma ka_upd2_1 (t3 : Fin 3 → KaTF (I := I) (M := M)) (F : KaTF (I := I) (M := M)) :
    (Function.update t3 (2 : Fin 3) F) 1 = t3 1 := by
  rw [Function.update_apply]
  exact if_neg (by decide)


/-- The `Fin 3`-tuple of three tangent fields. -/
noncomputable def tup3 (A B C : KaTF (I := I) (M := M)) : Fin 3 → KaTF (I := I) (M := M) :=
  fun j => Fin.cases A (fun j2 => Fin.cases B (fun _ => C) j2) j

@[simp] lemma tup3_0 (A B C : KaTF (I := I) (M := M)) : tup3 A B C 0 = A := rfl
@[simp] lemma tup3_1 (A B C : KaTF (I := I) (M := M)) : tup3 A B C 1 = B := rfl
@[simp] lemma tup3_2 (A B C : KaTF (I := I) (M := M)) : tup3 A B C 2 = C := rfl

lemma tup3_update_0 (A B C W' : KaTF (I := I) (M := M)) :
    Function.update (tup3 A B C) 0 W' = tup3 W' B C := by
  funext j
  fin_cases j <;> rfl

lemma tup3_update_1 (A B C W' : KaTF (I := I) (M := M)) :
    Function.update (tup3 A B C) 1 W' = tup3 A W' C := by
  funext j
  fin_cases j <;> rfl

lemma tup3_update_2 (A B C W' : KaTF (I := I) (M := M)) :
    Function.update (tup3 A B C) 2 W' = tup3 A B W' := by
  funext j
  fin_cases j <;> rfl

/-- Unfolding of `KKT` at `k+1`. -/
theorem ka_KKT_succ (G : ℝ → Submission.Diff.SMet I M) (t : ℝ) (k : ℕ)
    (w : Fin (k+1) → KaTF (I := I) (M := M)) (t3 : Fin 3 → KaTF (I := I) (M := M)) :
    KKT (I := I) (M := M) G t (k+1) w t3 = fun x =>
      mvfderiv I (KKT (I := I) (M := M) G t k (KaTail w) t3) x (w 0 x)
        - ∑ i : Fin k, KKT (I := I) (M := M) G t k
            (Function.update (KaTail w) i
              (fun y => Submission.Diff.lcOf (G 0) (w i.succ) y (w 0 y))) t3 x
        - ∑ j : Fin 3, KKT (I := I) (M := M) G t k (KaTail w)
            (Function.update t3 j (fun y => Submission.Diff.lcOf (G 0) (t3 j) y (w 0 y))) x := by
  funext x
  simp only [KKT, KaTail, covKAExt, Fin.sum_univ_three, Function.update_self,
    ka_upd0_1, ka_upd0_2, ka_upd1_0, ka_upd1_2, ka_upd2_0, ka_upd2_1]
  rw [show KaTail w = (fun i : Fin k => w i.succ) from rfl]
  ring

/-- Joint smoothness of the field-level expression `KKT`. -/
theorem ka_KKT_smooth (G : ℝ → Submission.Diff.SMet I M) (t : ℝ) {U : Set M} (hU : IsOpen U) :
    ∀ k (w : Fin k → KaTF (I := I) (M := M)) (t3 : Fin 3 → KaTF (I := I) (M := M)),
      (∀ s, KaSm (I := I) (M := M) U (w s)) →
      (∀ j, KaSm (I := I) (M := M) U (t3 j)) →
      CMDiff[U] ∞ (KKT (I := I) (M := M) G t k w t3) := by
  intro k
  induction k with
  | zero =>
      intro w t3 hw h3
      have h1 : KaSm (I := I) (M := M) U
          (fun z => Submission.Diff.lcOf (G t) (t3 1) z (t3 0 z)) :=
        ka_lcField_smooth (I := I) (G t) hU (h3 1) (h3 0)
      have h0 : KaSm (I := I) (M := M) U
          (fun z => Submission.Diff.lcOf (G 0) (t3 1) z (t3 0 z)) :=
        ka_lcField_smooth (I := I) (G 0) hU (h3 1) (h3 0)
      have hd : KaSm (I := I) (M := M) U
          (fun z => Submission.Diff.lcOf (G t) (t3 1) z (t3 0 z)
            - Submission.Diff.lcOf (G 0) (t3 1) z (t3 0 z)) :=
        ContMDiffOn.sub_section h1 h0
      have hp := ka_metric_pairing_smooth (I := I) (G t) hd (h3 2)
      refine hp.congr (fun z hz => ?_)
      simp only [KKT, covKAExt, aOf]
  | succ k ih =>
      intro w t3 hw h3
      have htail : ∀ s : Fin k, KaSm (I := I) (M := M) U (KaTail w s) := fun s => hw s.succ
      have h1 : CMDiff[U] ∞ (fun x => mvfderiv I
          (KKT (I := I) (M := M) G t k (KaTail w) t3) x (w 0 x)) :=
        ka_mvfderiv_apply (I := I) hU (ih (KaTail w) t3 htail h3) (hw 0)
      have h2i : ∀ i : Fin k, CMDiff[U] ∞ (KKT (I := I) (M := M) G t k
          (Function.update (KaTail w) i
            (fun y => Submission.Diff.lcOf (G 0) (w i.succ) y (w 0 y))) t3) := by
        intro i
        refine ih _ _ ?_ h3
        intro s
        by_cases hs : s = i
        · rw [hs, Function.update_self]
          exact ka_lcField_smooth (I := I) (G 0) hU (hw i.succ) (hw 0)
        · rw [Function.update_of_ne hs]
          exact htail s
      have h2 : CMDiff[U] ∞ (fun x => ∑ i : Fin k, KKT (I := I) (M := M) G t k
          (Function.update (KaTail w) i
            (fun y => Submission.Diff.lcOf (G 0) (w i.succ) y (w 0 y))) t3 x) := by
        intro x hx
        exact ContMDiffWithinAt.sum (t := Finset.univ) (fun i _ => (h2i i) x hx)
      have h3j : ∀ j : Fin 3, CMDiff[U] ∞ (KKT (I := I) (M := M) G t k (KaTail w)
          (Function.update t3 j
            (fun y => Submission.Diff.lcOf (G 0) (t3 j) y (w 0 y)))) := by
        intro j
        refine ih _ _ htail ?_
        intro j'
        by_cases hj : j' = j
        · rw [hj, Function.update_self]
          exact ka_lcField_smooth (I := I) (G 0) hU (h3 j) (hw 0)
        · rw [Function.update_of_ne hj]
          exact h3 j'
      have h3' : CMDiff[U] ∞ (fun x => ∑ j : Fin 3, KKT (I := I) (M := M) G t k (KaTail w)
          (Function.update t3 j
            (fun y => Submission.Diff.lcOf (G 0) (t3 j) y (w 0 y))) x) := by
        intro x hx
        exact ContMDiffWithinAt.sum (t := Finset.univ) (fun j _ => (h3j j) x hx)
      rw [ka_KKT_succ]
      exact (h1.sub h2).sub h3'

/-! ## The base case: the chart array of the connection difference at order `0` -/

/-- At order `0` the chart array `aComp` is the field-level lowered connection difference
evaluated on the coordinate frame. -/
lemma ka_base (G : ℝ → Submission.Diff.SMet I M) (x₀ : M) (t : ℝ)
    (i j l : Fin (Module.finrank ℝ E)) {y : E} (hy : y ∈ (extChartAt I x₀).target) :
    Work.Diff.EXT.aComp G x₀ t y i j l
      = Work.Diff.EXT.aOf G t (Work.Diff.GE.cFrame (I := I) x₀ i)
          (Work.Diff.GE.cFrame (I := I) x₀ j) (Work.Diff.GE.cFrame (I := I) x₀ l)
          (pt (I := I) x₀ y) := by
  have hsrc : pt (I := I) x₀ y ∈ (chartAt H x₀).source := by
    rw [pt, ← extChartAt_source I x₀]
    exact (extChartAt I x₀).map_target hy
  letI : RiemannianBundle (fun z : M => TangentSpace I z) := ⟨(G t).toRiemannianMetric⟩
  have hb : ∀ (z : M) (u v : TangentSpace I z), (G t).inner z u v = inner ℝ u v :=
    fun z u v => rfl
  simp only [Work.Diff.EXT.aComp, Work.Diff.EXT.aOf, Work.Diff.GE.GramM, Work.Diff.GE.mComp, hb]
  rw [ka_lcOf_cFrame' (I := I) (G t) x₀ (pt (I := I) x₀ y) hsrc j i,
    ka_lcOf_cFrame' (I := I) (G 0) x₀ (pt (I := I) x₀ y) hsrc j i]
  rw [inner_sub_left, sum_inner, sum_inner, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro m _
  simp only [real_inner_smul_left]
  rw [real_inner_comm (Work.Diff.GE.cFrame (I := I) x₀ l (pt (I := I) x₀ y))
    (Work.Diff.GE.cFrame (I := I) x₀ m (pt (I := I) x₀ y))]
  rw [ka_cGam_comm (I := I) (G t) x₀ (pt (I := I) x₀ y) hsrc m j i,
    ka_cGam_comm (I := I) (G 0) x₀ (pt (I := I) x₀ y) hsrc m j i]
  ring

/-! ## The two linearity statements -/

/-- Linearity of `covKAExt` in a *direction* slot over a finite sum of fields with coefficient
functions. -/
def KaLinD (G : ℝ → Submission.Diff.SMet I M) (t : ℝ) (U : Set M) (k : ℕ) : Prop :=
  ∀ (w : Fin k → KaTF (I := I) (M := M)) (i : Fin k) (t3 : Fin 3 → KaTF (I := I) (M := M))
    (W' : KaTF (I := I) (M := M)) {ι : Type} [Fintype ι] (d : ι → M → ℝ)
    (V : ι → KaTF (I := I) (M := M)),
    (∀ s, KaSm (I := I) (M := M) U (w s)) →
    (∀ j, KaSm (I := I) (M := M) U (t3 j)) →
    KaSm (I := I) (M := M) U W' →
    (∀ q, CMDiff[U] ∞ (d q)) →
    (∀ q, KaSm (I := I) (M := M) U (V q)) →
    (∀ x ∈ U, W' x = ∑ q, d q x • V q x) →
    ∀ x ∈ U, KKT (I := I) (M := M) G t k (Function.update w i W') t3 x
      = ∑ q, d q x * KKT (I := I) (M := M) G t k (Function.update w i (V q)) t3 x

/-- Linearity of `covKAExt` in a *tensor* slot over a finite sum of fields with coefficient
functions. -/
def KaLinT (G : ℝ → Submission.Diff.SMet I M) (t : ℝ) (U : Set M) (k : ℕ) : Prop :=
  ∀ (w : Fin k → KaTF (I := I) (M := M)) (t3 : Fin 3 → KaTF (I := I) (M := M)) (j : Fin 3)
    (W' : KaTF (I := I) (M := M)) {ι : Type} [Fintype ι] (d : ι → M → ℝ)
    (V : ι → KaTF (I := I) (M := M)),
    (∀ s, KaSm (I := I) (M := M) U (w s)) →
    (∀ j', KaSm (I := I) (M := M) U (t3 j')) →
    KaSm (I := I) (M := M) U W' →
    (∀ q, CMDiff[U] ∞ (d q)) →
    (∀ q, KaSm (I := I) (M := M) U (V q)) →
    (∀ x ∈ U, W' x = ∑ q, d q x • V q x) →
    ∀ x ∈ U, KKT (I := I) (M := M) G t k w (Function.update t3 j W') x
      = ∑ q, d q x * KKT (I := I) (M := M) G t k w (Function.update t3 j (V q)) x


/-! ## The main induction -/

/-- **The chart recursion computes `covKAExt` in the coordinate frame** (assuming the linearity of
`covKAExt` in its slots, which is the content of `Work.Diff.EXT.KaLinD` / `KaLinT`). -/
theorem ka_main (G : ℝ → Submission.Diff.SMet I M) (x₀ : M) (t : ℝ)
    (hlinD : ∀ k, KaLinD G t (chartAt H x₀).source k)
    (hlinT : ∀ k, KaLinT G t (chartAt H x₀).source k) :
    ∀ k (v : Fin k → Fin (Module.finrank ℝ E)) (i j l : Fin (Module.finrank ℝ E)) {y : E},
      y ∈ (extChartAt I x₀).target →
      Work.Diff.EXT.aCovArr G x₀ t k v i j l y
        = covKAExt G t k (fun s => cFrame (I := I) x₀ (v s)) (cFrame (I := I) x₀ i)
            (cFrame (I := I) x₀ j) (cFrame (I := I) x₀ l) (pt (I := I) x₀ y) := by
  intro k
  induction k with
  | zero =>
      intro v i j l y hy
      simp only [Work.Diff.EXT.aCovArr, covKAExt]
      exact ka_base G x₀ t i j l hy
  | succ k ih =>
      intro v i j l y hy
      have hsrc : pt (I := I) x₀ y ∈ (chartAt H x₀).source := by
        rw [pt, ← extChartAt_source I x₀]
        exact (extChartAt I x₀).map_target hy
      have htarget : (extChartAt I x₀).target ∈ 𝓝 y :=
        (OpenPartialHomeomorph.isOpen_extend_target (chartAt H x₀) (I := I)).mem_nhds hy
      have hfr : ∀ p : Fin (Module.finrank ℝ E),
          KaSm (I := I) (M := M) (chartAt H x₀).source (cFrame (I := I) x₀ p) :=
        fun p => ka_smooth_cFrame (I := I) x₀ p
      -- smoothness of the level-`k` field-level expression
      have hksm : CMDiff[(chartAt H x₀).source] ∞
          (covKAExt G t k (fun s : Fin k => cFrame (I := I) x₀ (v s.succ))
            (cFrame (I := I) x₀ i) (cFrame (I := I) x₀ j) (cFrame (I := I) x₀ l)) := by
        have h := ka_KKT_smooth (I := I) (M := M) G t (U := (chartAt H x₀).source)
          (chartAt H x₀).open_source k (fun s : Fin k => cFrame (I := I) x₀ (v s.succ))
          (tup3 (cFrame (I := I) x₀ i) (cFrame (I := I) x₀ j) (cFrame (I := I) x₀ l))
          (fun s => hfr _)
          (fun j3 => by
            fin_cases j3 <;> simp only [tup3_0, tup3_1, tup3_2] <;> exact hfr _)
        simpa only [KKT, tup3_0, tup3_1, tup3_2] using h
      have hkdiff : MDifferentiableAt I 𝓘(ℝ, ℝ)
          (covKAExt G t k (fun s : Fin k => cFrame (I := I) x₀ (v s.succ))
            (cFrame (I := I) x₀ i) (cFrame (I := I) x₀ j) (cFrame (I := I) x₀ l))
          (pt (I := I) x₀ y) :=
        ((hksm _ hsrc).contMDiffAt ((chartAt H x₀).open_source.mem_nhds hsrc)).mdifferentiableAt
          (by simp)
      -- the derivative term
      have hD : fderiv ℝ (Work.Diff.EXT.aCovArr G x₀ t k (fun s : Fin k => v s.succ) i j l) y
            (cBasis (E := E) (v 0))
          = mvfderiv I (covKAExt G t k (fun s : Fin k => cFrame (I := I) x₀ (v s.succ))
              (cFrame (I := I) x₀ i) (cFrame (I := I) x₀ j) (cFrame (I := I) x₀ l))
            (pt (I := I) x₀ y) (cFrame (I := I) x₀ (v 0) (pt (I := I) x₀ y)) := by
        have hev : Work.Diff.EXT.aCovArr G x₀ t k (fun s : Fin k => v s.succ) i j l
            =ᶠ[𝓝 y] fun y' => covKAExt G t k (fun s : Fin k => cFrame (I := I) x₀ (v s.succ))
              (cFrame (I := I) x₀ i) (cFrame (I := I) x₀ j) (cFrame (I := I) x₀ l)
              (pt (I := I) x₀ y') := by
          filter_upwards [htarget] with y' hy'
          exact ih (fun s : Fin k => v s.succ) i j l hy'
        rw [Filter.EventuallyEq.fderiv_eq hev]
        have h := (Work.Diff.T.mvfderiv_frameVector_real (I := I) x₀ hsrc hkdiff
          (cBasis (E := E) (v 0))).symm
        have hpt : (extChartAt I x₀) (pt (I := I) x₀ y) = y := by
          rw [pt]
          exact (extChartAt I x₀).right_inv hy
        rw [hpt] at h
        exact h
      -- the direction-slot corrections
      have hR : ∀ r : Fin k,
          (∑ p : Fin (Module.finrank ℝ E),
              cGam (G 0) x₀ (pt (I := I) x₀ y) p (v r.succ) (v 0)
                * Work.Diff.EXT.aCovArr G x₀ t k
                    (Function.update (fun s : Fin k => v s.succ) r p) i j l y)
            = covKAExt G t k
                (Function.update (fun s : Fin k => cFrame (I := I) x₀ (v s.succ)) r
                  (fun z => Submission.Diff.lcOf (G 0) (cFrame (I := I) x₀ (v r.succ)) z
                    (cFrame (I := I) x₀ (v 0) z)))
                (cFrame (I := I) x₀ i) (cFrame (I := I) x₀ j) (cFrame (I := I) x₀ l)
                (pt (I := I) x₀ y) := by
        intro r
        have hsmW : KaSm (I := I) (M := M) (chartAt H x₀).source
            (fun z => Submission.Diff.lcOf (G 0) (cFrame (I := I) x₀ (v r.succ)) z
              (cFrame (I := I) x₀ (v 0) z)) :=
          ka_lcField_smooth (I := I) (G 0) (chartAt H x₀).open_source (hfr _) (hfr _)
        have hlin := hlinD k (w := fun s : Fin k => cFrame (I := I) x₀ (v s.succ)) (i := r)
          (t3 := tup3 (cFrame (I := I) x₀ i) (cFrame (I := I) x₀ j) (cFrame (I := I) x₀ l))
          (W' := fun z => Submission.Diff.lcOf (G 0) (cFrame (I := I) x₀ (v r.succ)) z
            (cFrame (I := I) x₀ (v 0) z))
          (d := fun q z => cGam (G 0) x₀ z q (v r.succ) (v 0))
          (V := fun q => cFrame (I := I) x₀ q)
          (fun s => hfr _)
          (fun j3 => by
            fin_cases j3 <;> simp only [tup3_0, tup3_1, tup3_2] <;> exact hfr _)
          hsmW
          (fun q => ka_cGam_smooth (I := I) (G 0) x₀ q (v r.succ) (v 0))
          (fun q => hfr q)
          (fun z hz => ka_lcOf_cFrame' (I := I) (G 0) x₀ z hz (v r.succ) (v 0))
        rw [show covKAExt G t k
              (Function.update (fun s : Fin k => cFrame (I := I) x₀ (v s.succ)) r
                (fun z => Submission.Diff.lcOf (G 0) (cFrame (I := I) x₀ (v r.succ)) z
                  (cFrame (I := I) x₀ (v 0) z)))
              (cFrame (I := I) x₀ i) (cFrame (I := I) x₀ j) (cFrame (I := I) x₀ l)
              (pt (I := I) x₀ y)
            = KKT (I := I) (M := M) G t k
              (Function.update (fun s : Fin k => cFrame (I := I) x₀ (v s.succ)) r
                (fun z => Submission.Diff.lcOf (G 0) (cFrame (I := I) x₀ (v r.succ)) z
                  (cFrame (I := I) x₀ (v 0) z)))
              (tup3 (cFrame (I := I) x₀ i) (cFrame (I := I) x₀ j) (cFrame (I := I) x₀ l))
              (pt (I := I) x₀ y) from rfl]
        rw [hlin (pt (I := I) x₀ y) hsrc]
        refine Finset.sum_congr rfl (fun q _ => ?_)
        rw [show KKT (I := I) (M := M) G t k
              (Function.update (fun s : Fin k => cFrame (I := I) x₀ (v s.succ)) r
                (cFrame (I := I) x₀ q))
              (tup3 (cFrame (I := I) x₀ i) (cFrame (I := I) x₀ j) (cFrame (I := I) x₀ l))
              (pt (I := I) x₀ y)
            = covKAExt G t k
              (Function.update (fun s : Fin k => cFrame (I := I) x₀ (v s.succ)) r
                (cFrame (I := I) x₀ q))
              (cFrame (I := I) x₀ i) (cFrame (I := I) x₀ j) (cFrame (I := I) x₀ l)
              (pt (I := I) x₀ y) from rfl]
        rw [show Function.update (fun s : Fin k => cFrame (I := I) x₀ (v s.succ)) r
              (cFrame (I := I) x₀ q)
            = fun s : Fin k => cFrame (I := I) x₀
                ((Function.update (fun s : Fin k => v s.succ) r q) s) from by
          funext s
          by_cases h : s = r <;> simp [Function.update_apply, h]]
        rw [← ih (Function.update (fun s : Fin k => v s.succ) r q) i j l hy]
      -- the three tensor-slot corrections
      have hA : (∑ p : Fin (Module.finrank ℝ E),
            cGam (G 0) x₀ (pt (I := I) x₀ y) p i (v 0)
              * Work.Diff.EXT.aCovArr G x₀ t k (fun s : Fin k => v s.succ) p j l y)
          = covKAExt G t k (fun s : Fin k => cFrame (I := I) x₀ (v s.succ))
              (fun z => Submission.Diff.lcOf (G 0) (cFrame (I := I) x₀ i) z
                (cFrame (I := I) x₀ (v 0) z))
              (cFrame (I := I) x₀ j) (cFrame (I := I) x₀ l) (pt (I := I) x₀ y) := by
        have hsmW : KaSm (I := I) (M := M) (chartAt H x₀).source
            (fun z => Submission.Diff.lcOf (G 0) (cFrame (I := I) x₀ i) z
              (cFrame (I := I) x₀ (v 0) z)) :=
          ka_lcField_smooth (I := I) (G 0) (chartAt H x₀).open_source (hfr i) (hfr (v 0))
        have hlin := hlinT k (w := fun s : Fin k => cFrame (I := I) x₀ (v s.succ))
          (t3 := tup3 (cFrame (I := I) x₀ i) (cFrame (I := I) x₀ j) (cFrame (I := I) x₀ l))
          (j := 0)
          (W' := fun z => Submission.Diff.lcOf (G 0) (cFrame (I := I) x₀ i) z
            (cFrame (I := I) x₀ (v 0) z))
          (d := fun q z => cGam (G 0) x₀ z q i (v 0))
          (V := fun q => cFrame (I := I) x₀ q)
          (fun s => hfr _)
          (fun j3 => by
            fin_cases j3 <;> simp only [tup3_0, tup3_1, tup3_2] <;> exact hfr _)
          hsmW
          (fun q => ka_cGam_smooth (I := I) (G 0) x₀ q i (v 0))
          (fun q => hfr q)
          (fun z hz => ka_lcOf_cFrame' (I := I) (G 0) x₀ z hz i (v 0))
        rw [show covKAExt G t k (fun s : Fin k => cFrame (I := I) x₀ (v s.succ))
              (fun z => Submission.Diff.lcOf (G 0) (cFrame (I := I) x₀ i) z
                (cFrame (I := I) x₀ (v 0) z))
              (cFrame (I := I) x₀ j) (cFrame (I := I) x₀ l) (pt (I := I) x₀ y)
            = KKT (I := I) (M := M) G t k (fun s : Fin k => cFrame (I := I) x₀ (v s.succ))
              (Function.update (tup3 (cFrame (I := I) x₀ i) (cFrame (I := I) x₀ j)
                (cFrame (I := I) x₀ l)) 0
                (fun z => Submission.Diff.lcOf (G 0) (cFrame (I := I) x₀ i) z
                  (cFrame (I := I) x₀ (v 0) z)))
              (pt (I := I) x₀ y) from by
          simp only [KKT, tup3_update_0, tup3_0, tup3_1, tup3_2]]
        rw [hlin (pt (I := I) x₀ y) hsrc]
        refine Finset.sum_congr rfl (fun q _ => ?_)
        rw [show KKT (I := I) (M := M) G t k (fun s : Fin k => cFrame (I := I) x₀ (v s.succ))
              (Function.update (tup3 (cFrame (I := I) x₀ i) (cFrame (I := I) x₀ j)
                (cFrame (I := I) x₀ l)) 0 (cFrame (I := I) x₀ q)) (pt (I := I) x₀ y)
            = covKAExt G t k (fun s : Fin k => cFrame (I := I) x₀ (v s.succ))
              (cFrame (I := I) x₀ q) (cFrame (I := I) x₀ j) (cFrame (I := I) x₀ l)
              (pt (I := I) x₀ y) from by
          simp only [KKT, tup3_update_0, tup3_0, tup3_1, tup3_2]]
        rw [← ih (fun s : Fin k => v s.succ) q j l hy]
      have hB : (∑ p : Fin (Module.finrank ℝ E),
            cGam (G 0) x₀ (pt (I := I) x₀ y) p j (v 0)
              * Work.Diff.EXT.aCovArr G x₀ t k (fun s : Fin k => v s.succ) i p l y)
          = covKAExt G t k (fun s : Fin k => cFrame (I := I) x₀ (v s.succ))
              (cFrame (I := I) x₀ i)
              (fun z => Submission.Diff.lcOf (G 0) (cFrame (I := I) x₀ j) z
                (cFrame (I := I) x₀ (v 0) z))
              (cFrame (I := I) x₀ l) (pt (I := I) x₀ y) := by
        have hsmW : KaSm (I := I) (M := M) (chartAt H x₀).source
            (fun z => Submission.Diff.lcOf (G 0) (cFrame (I := I) x₀ j) z
              (cFrame (I := I) x₀ (v 0) z)) :=
          ka_lcField_smooth (I := I) (G 0) (chartAt H x₀).open_source (hfr j) (hfr (v 0))
        have hlin := hlinT k (w := fun s : Fin k => cFrame (I := I) x₀ (v s.succ))
          (t3 := tup3 (cFrame (I := I) x₀ i) (cFrame (I := I) x₀ j) (cFrame (I := I) x₀ l))
          (j := 1)
          (W' := fun z => Submission.Diff.lcOf (G 0) (cFrame (I := I) x₀ j) z
            (cFrame (I := I) x₀ (v 0) z))
          (d := fun q z => cGam (G 0) x₀ z q j (v 0))
          (V := fun q => cFrame (I := I) x₀ q)
          (fun s => hfr _)
          (fun j3 => by
            fin_cases j3 <;> simp only [tup3_0, tup3_1, tup3_2] <;> exact hfr _)
          hsmW
          (fun q => ka_cGam_smooth (I := I) (G 0) x₀ q j (v 0))
          (fun q => hfr q)
          (fun z hz => ka_lcOf_cFrame' (I := I) (G 0) x₀ z hz j (v 0))
        rw [show covKAExt G t k (fun s : Fin k => cFrame (I := I) x₀ (v s.succ))
              (cFrame (I := I) x₀ i)
              (fun z => Submission.Diff.lcOf (G 0) (cFrame (I := I) x₀ j) z
                (cFrame (I := I) x₀ (v 0) z))
              (cFrame (I := I) x₀ l) (pt (I := I) x₀ y)
            = KKT (I := I) (M := M) G t k (fun s : Fin k => cFrame (I := I) x₀ (v s.succ))
              (Function.update (tup3 (cFrame (I := I) x₀ i) (cFrame (I := I) x₀ j)
                (cFrame (I := I) x₀ l)) 1
                (fun z => Submission.Diff.lcOf (G 0) (cFrame (I := I) x₀ j) z
                  (cFrame (I := I) x₀ (v 0) z)))
              (pt (I := I) x₀ y) from by
          simp only [KKT, tup3_update_1, tup3_0, tup3_1, tup3_2]]
        rw [hlin (pt (I := I) x₀ y) hsrc]
        refine Finset.sum_congr rfl (fun q _ => ?_)
        rw [show KKT (I := I) (M := M) G t k (fun s : Fin k => cFrame (I := I) x₀ (v s.succ))
              (Function.update (tup3 (cFrame (I := I) x₀ i) (cFrame (I := I) x₀ j)
                (cFrame (I := I) x₀ l)) 1 (cFrame (I := I) x₀ q)) (pt (I := I) x₀ y)
            = covKAExt G t k (fun s : Fin k => cFrame (I := I) x₀ (v s.succ))
              (cFrame (I := I) x₀ i) (cFrame (I := I) x₀ q) (cFrame (I := I) x₀ l)
              (pt (I := I) x₀ y) from by
          simp only [KKT, tup3_update_1, tup3_0, tup3_1, tup3_2]]
        rw [← ih (fun s : Fin k => v s.succ) i q l hy]
      have hC : (∑ p : Fin (Module.finrank ℝ E),
            cGam (G 0) x₀ (pt (I := I) x₀ y) p l (v 0)
              * Work.Diff.EXT.aCovArr G x₀ t k (fun s : Fin k => v s.succ) i j p y)
          = covKAExt G t k (fun s : Fin k => cFrame (I := I) x₀ (v s.succ))
              (cFrame (I := I) x₀ i) (cFrame (I := I) x₀ j)
              (fun z => Submission.Diff.lcOf (G 0) (cFrame (I := I) x₀ l) z
                (cFrame (I := I) x₀ (v 0) z))
              (pt (I := I) x₀ y) := by
        have hsmW : KaSm (I := I) (M := M) (chartAt H x₀).source
            (fun z => Submission.Diff.lcOf (G 0) (cFrame (I := I) x₀ l) z
              (cFrame (I := I) x₀ (v 0) z)) :=
          ka_lcField_smooth (I := I) (G 0) (chartAt H x₀).open_source (hfr l) (hfr (v 0))
        have hlin := hlinT k (w := fun s : Fin k => cFrame (I := I) x₀ (v s.succ))
          (t3 := tup3 (cFrame (I := I) x₀ i) (cFrame (I := I) x₀ j) (cFrame (I := I) x₀ l))
          (j := 2)
          (W' := fun z => Submission.Diff.lcOf (G 0) (cFrame (I := I) x₀ l) z
            (cFrame (I := I) x₀ (v 0) z))
          (d := fun q z => cGam (G 0) x₀ z q l (v 0))
          (V := fun q => cFrame (I := I) x₀ q)
          (fun s => hfr _)
          (fun j3 => by
            fin_cases j3 <;> simp only [tup3_0, tup3_1, tup3_2] <;> exact hfr _)
          hsmW
          (fun q => ka_cGam_smooth (I := I) (G 0) x₀ q l (v 0))
          (fun q => hfr q)
          (fun z hz => ka_lcOf_cFrame' (I := I) (G 0) x₀ z hz l (v 0))
        rw [show covKAExt G t k (fun s : Fin k => cFrame (I := I) x₀ (v s.succ))
              (cFrame (I := I) x₀ i) (cFrame (I := I) x₀ j)
              (fun z => Submission.Diff.lcOf (G 0) (cFrame (I := I) x₀ l) z
                (cFrame (I := I) x₀ (v 0) z))
              (pt (I := I) x₀ y)
            = KKT (I := I) (M := M) G t k (fun s : Fin k => cFrame (I := I) x₀ (v s.succ))
              (Function.update (tup3 (cFrame (I := I) x₀ i) (cFrame (I := I) x₀ j)
                (cFrame (I := I) x₀ l)) 2
                (fun z => Submission.Diff.lcOf (G 0) (cFrame (I := I) x₀ l) z
                  (cFrame (I := I) x₀ (v 0) z)))
              (pt (I := I) x₀ y) from by
          simp only [KKT, tup3_update_2, tup3_0, tup3_1, tup3_2]]
        rw [hlin (pt (I := I) x₀ y) hsrc]
        refine Finset.sum_congr rfl (fun q _ => ?_)
        rw [show KKT (I := I) (M := M) G t k (fun s : Fin k => cFrame (I := I) x₀ (v s.succ))
              (Function.update (tup3 (cFrame (I := I) x₀ i) (cFrame (I := I) x₀ j)
                (cFrame (I := I) x₀ l)) 2 (cFrame (I := I) x₀ q)) (pt (I := I) x₀ y)
            = covKAExt G t k (fun s : Fin k => cFrame (I := I) x₀ (v s.succ))
              (cFrame (I := I) x₀ i) (cFrame (I := I) x₀ j) (cFrame (I := I) x₀ q)
              (pt (I := I) x₀ y) from by
          simp only [KKT, tup3_update_2, tup3_0, tup3_1, tup3_2]]
        rw [← ih (fun s : Fin k => v s.succ) i j q hy]
      -- assembly
      simp only [Work.Diff.EXT.aCovArr, covKAExt]
      rw [hD, Finset.sum_congr rfl (fun r _ => hR r), hA, hB, hC]

/-! ## Auxiliary lemmas for the linearity of `covKAExt` -/

/-- A continuous linear endomorphism is additive and homogeneous over finite sums of scaled
vectors. -/
lemma ka_clm_sum_smul {ι : Type*} [Fintype ι] {x : M}
    (L : TangentSpace I x →L[ℝ] TangentSpace I x) (c : ι → ℝ) (u : ι → TangentSpace I x) :
    L (∑ q, c q • u q) = ∑ q, c q • L (u q) := by
  rw [map_sum]
  simp_rw [map_smul]

lemma ka_clm_sum_smul_real {ι : Type*} [Fintype ι] {x : M}
    (L : TangentSpace I x →L[ℝ] ℝ) (c : ι → ℝ) (u : ι → TangentSpace I x) :
    L (∑ q, c q • u q) = ∑ q, c q • L (u q) := by
  rw [map_sum]
  simp_rw [map_smul]

/-- The product rule for a finite sum of products of functions on `M`. -/
lemma ka_mvfderiv_sum_mul {ι : Type*} [Fintype ι] {g f : ι → M → ℝ} {x : M}
    {v : TangentSpace I x} (hg : ∀ q, MDifferentiableAt I 𝓘(ℝ, ℝ) (g q) x)
    (hf : ∀ q, MDifferentiableAt I 𝓘(ℝ, ℝ) (f q) x) :
    mvfderiv I (∑ q, g q * f q) x v
      = ∑ q, (mvfderiv I (g q) x v * f q x + g q x * mvfderiv I (f q) x v) := by
  classical
  have key : ∀ s : Finset ι, (∀ q ∈ s, MDifferentiableAt I 𝓘(ℝ, ℝ) (g q) x) →
      (∀ q ∈ s, MDifferentiableAt I 𝓘(ℝ, ℝ) (f q) x) →
      mvfderiv I (∑ q ∈ s, g q * f q) x v
        = ∑ q ∈ s, (mvfderiv I (g q) x v * f q x + g q x * mvfderiv I (f q) x v) := by
    intro s
    induction s using Finset.induction with
    | empty =>
        intro _ _
        rw [show (∑ q ∈ (∅ : Finset ι), g q * f q) = (0 : M → ℝ) from by funext y; simp]
        simp
    | insert a t ha ih =>
        intro hg' hf'
        have hfun : (∑ q ∈ insert a t, g q * f q) = g a * f a + ∑ q ∈ t, g q * f q :=
          Finset.sum_insert ha
        have hga := hg' a (Finset.mem_insert_self a t)
        have hfa := hf' a (Finset.mem_insert_self a t)
        have hgt : ∀ q ∈ t, MDifferentiableAt I 𝓘(ℝ, ℝ) (g q) x :=
          fun q hq => hg' q (Finset.mem_insert_of_mem hq)
        have hft : ∀ q ∈ t, MDifferentiableAt I 𝓘(ℝ, ℝ) (f q) x :=
          fun q hq => hf' q (Finset.mem_insert_of_mem hq)
        have hsum : MDifferentiableAt I 𝓘(ℝ, ℝ) (∑ q ∈ t, g q * f q) x :=
          MDifferentiableAt.sum (t := t) (fun q hq => (hgt q hq).mul (hft q hq))
        rw [hfun, mvfderiv_add (hga.mul hfa) hsum, add_apply, mvfderiv_mul hga hfa]
        simp only [add_apply, smul_apply]
        rw [ih hgt hft, Finset.sum_insert ha]
        ring
  exact key Finset.univ (fun q _ => hg q) (fun q _ => hf q)

/-! ### The linearity of `aOf` in its three slots (the `k = 0` case) -/

lemma ka_aOf_lin_0 (G : ℝ → Submission.Diff.SMet I M) (t : ℝ) {U : Set M} (hU : IsOpen U)
    {ι : Type} [Fintype ι] (d : ι → M → ℝ) (V : ι → KaTF (I := I) (M := M))
    (B C W' : KaTF (I := I) (M := M))
    (hd : ∀ q, CMDiff[U] ∞ (d q)) (hV : ∀ q, KaSm (I := I) (M := M) U (V q))
    (hB : KaSm (I := I) (M := M) U B) (hC : KaSm (I := I) (M := M) U C)
    (hW' : KaSm (I := I) (M := M) U W')
    (hpt : ∀ x ∈ U, W' x = ∑ q, d q x • V q x) :
    ∀ x ∈ U, Work.Diff.EXT.aOf G t W' B C x = ∑ q, d q x * Work.Diff.EXT.aOf G t (V q) B C x := by
  intro x hx
  have hWx : W' x = ∑ q, d q x • V q x := hpt x hx
  simp only [Work.Diff.EXT.aOf, hWx]
  rw [show (Submission.Diff.lcOf (G t) B x) (∑ q, d q x • V q x)
        = ∑ q, d q x • (Submission.Diff.lcOf (G t) B x) (V q x) from
      ka_clm_sum_smul (Submission.Diff.lcOf (G t) B x) (fun q => d q x) (fun q => V q x),
    show (Submission.Diff.lcOf (G 0) B x) (∑ q, d q x • V q x)
        = ∑ q, d q x • (Submission.Diff.lcOf (G 0) B x) (V q x) from
      ka_clm_sum_smul (Submission.Diff.lcOf (G 0) B x) (fun q => d q x) (fun q => V q x)]
  rw [← Finset.sum_sub_distrib]
  rw [show (∑ q, (d q x • (Submission.Diff.lcOf (G t) B x) (V q x)
          - d q x • (Submission.Diff.lcOf (G 0) B x) (V q x)))
        = ∑ q, d q x • ((Submission.Diff.lcOf (G t) B x) (V q x)
            - (Submission.Diff.lcOf (G 0) B x) (V q x)) from
      Finset.sum_congr rfl (fun q _ => (smul_sub _ _ _).symm)]
  rw [map_sum]
  simp only [map_smul]
  rw [ContinuousLinearMap.sum_apply]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]

lemma ka_aOf_lin_2 (G : ℝ → Submission.Diff.SMet I M) (t : ℝ) {U : Set M} (hU : IsOpen U)
    {ι : Type} [Fintype ι] (d : ι → M → ℝ) (V : ι → KaTF (I := I) (M := M))
    (A B W' : KaTF (I := I) (M := M))
    (hd : ∀ q, CMDiff[U] ∞ (d q)) (hV : ∀ q, KaSm (I := I) (M := M) U (V q))
    (hA : KaSm (I := I) (M := M) U A) (hB : KaSm (I := I) (M := M) U B)
    (hW' : KaSm (I := I) (M := M) U W')
    (hpt : ∀ x ∈ U, W' x = ∑ q, d q x • V q x) :
    ∀ x ∈ U, Work.Diff.EXT.aOf G t A B W' x = ∑ q, d q x * Work.Diff.EXT.aOf G t A B (V q) x := by
  intro x hx
  have hWx : W' x = ∑ q, d q x • V q x := hpt x hx
  simp only [Work.Diff.EXT.aOf, hWx]
  rw [show (G t).inner x (Submission.Diff.lcOf (G t) B x (A x) - Submission.Diff.lcOf (G 0) B x (A x))
        (∑ q, d q x • V q x)
      = ∑ q, d q x • ((G t).inner x
          (Submission.Diff.lcOf (G t) B x (A x) - Submission.Diff.lcOf (G 0) B x (A x)) (V q x)) from by
    rw [map_sum]
    simp only [map_smul]]
  simp only [smul_eq_mul]

lemma ka_aOf_lin_1 (G : ℝ → Submission.Diff.SMet I M) (t : ℝ) {U : Set M} (hU : IsOpen U)
    {ι : Type} [Fintype ι] (d : ι → M → ℝ) (V : ι → KaTF (I := I) (M := M))
    (A C W' : KaTF (I := I) (M := M))
    (hd : ∀ q, CMDiff[U] ∞ (d q)) (hV : ∀ q, KaSm (I := I) (M := M) U (V q))
    (hA : KaSm (I := I) (M := M) U A) (hC : KaSm (I := I) (M := M) U C)
    (hW' : KaSm (I := I) (M := M) U W')
    (hpt : ∀ x ∈ U, W' x = ∑ q, d q x • V q x) :
    ∀ x ∈ U, Work.Diff.EXT.aOf G t A W' C x = ∑ q, d q x * Work.Diff.EXT.aOf G t A (V q) C x := by
  intro x hx
  have hgerm : W' =ᶠ[𝓝 x] fun y => ∑ q, d q y • V q y := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hpt y hy
  have hZsm : ContMDiffAt I I.tangent ∞ (T% W') x := hW'.contMDiffAt (hU.mem_nhds hx)
  have hVsm : ∀ q, ContMDiffAt I I.tangent ∞ (T% (V q)) x :=
    fun q => (hV q).contMDiffAt (hU.mem_nhds hx)
  have hdsm : ∀ q, ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (d q) x :=
    fun q => (hd q).contMDiffAt (hU.mem_nhds hx)
  have key : ∀ (g : Submission.Diff.SMet I M),
      (Submission.Diff.lcOf g W' x) (A x)
        = ∑ q ∈ Finset.univ, d q x • (Submission.Diff.lcOf g (V q) x) (A x)
          + ∑ q ∈ Finset.univ, mvfderiv I (d q) x (A x) • V q x := by
    intro g
    exact Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.cov_eq_sum_of_eventuallyEq_pointwise
      (cov := Submission.Diff.lcOf g) Finset.univ d V hZsm (fun q => hVsm q)
      (fun q => hdsm q) hgerm
  simp only [Work.Diff.EXT.aOf]
  rw [key (G t), key (G 0)]
  rw [show (∑ q ∈ Finset.univ, d q x • (Submission.Diff.lcOf (G t) (V q) x) (A x)
        + ∑ q ∈ Finset.univ, mvfderiv I (d q) x (A x) • V q x
        - (∑ q ∈ Finset.univ, d q x • (Submission.Diff.lcOf (G 0) (V q) x) (A x)
            + ∑ q ∈ Finset.univ, mvfderiv I (d q) x (A x) • V q x))
      = ∑ q, d q x • ((Submission.Diff.lcOf (G t) (V q) x) (A x)
          - (Submission.Diff.lcOf (G 0) (V q) x) (A x)) from by
    rw [add_sub_add_right_eq_sub, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun q _ => (smul_sub _ _ _).symm)]
  rw [map_sum]
  simp only [map_smul]
  rw [ContinuousLinearMap.sum_apply]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]

/-! ### Tail and update lemmas, and the `KaTail`-form of the recursion -/

lemma KaTail_update_zero {k : ℕ} (w : Fin (k+1) → KaTF (I := I) (M := M))
    (V : KaTF (I := I) (M := M)) :
    KaTail (Function.update w 0 V) = KaTail w := by
  funext s
  show (Function.update w 0 V) s.succ = w s.succ
  rw [Function.update_apply, if_neg (Fin.succ_ne_zero s)]

lemma KaTail_update_succ {k : ℕ} (w : Fin (k+1) → KaTF (I := I) (M := M)) (i : Fin k)
    (V : KaTF (I := I) (M := M)) :
    KaTail (Function.update w (Fin.succ i) V) = Function.update (KaTail w) i V := by
  have h1 : KaTail (Function.update w (Fin.succ i) V)
      = fun s => Function.update (fun s' : Fin k => w s'.succ) i V s := by
    funext s
    show (Function.update w (Fin.succ i) V) s.succ
      = Function.update (fun s' : Fin k => w s'.succ) i V s
    rw [Function.update_apply, Function.update_apply]
    by_cases h : s = i
    · subst h; simp
    · have h' : Fin.succ s ≠ Fin.succ i := fun hh => h (Fin.succ_inj.mp hh)
      rw [if_neg h', if_neg h]
  have h2 : (fun s => Function.update (fun s' : Fin k => w s'.succ) i V s)
      = Function.update (KaTail w) i V := rfl
  rw [h1, h2]

lemma ka_upd_zero_succ {k : ℕ} (w : Fin (k+1) → KaTF (I := I) (M := M)) (i : Fin k)
    (V : KaTF (I := I) (M := M)) :
    (Function.update w (Fin.succ i) V) 0 = w 0 := by
  rw [Function.update_apply, if_neg]
  exact fun h => Fin.succ_ne_zero i h.symm

lemma ka_upd_self_update {ι : Type*} [DecidableEq ι] {β : Type*} (f : ι → β) (a : ι)
    (x y : β) :
    Function.update (Function.update f a x) a y = Function.update f a y := by
  funext z
  by_cases h : z = a
  · rw [h, Function.update_self, Function.update_self]
  · rw [Function.update_of_ne h y (Function.update f a x), Function.update_of_ne h x f,
      Function.update_of_ne h y f]

lemma ka_upd_comm {ι : Type*} [DecidableEq ι] {β : Type*} (f : ι → β) {a b : ι} (h : b ≠ a)
    (x y : β) :
    Function.update (Function.update f a x) b y = Function.update (Function.update f b y) a x := by
  funext z
  by_cases hza : z = a
  · rw [hza, Function.update_of_ne h.symm y (Function.update f a x), Function.update_self,
      Function.update_self]
  · by_cases hzb : z = b
    · rw [hzb, Function.update_self, Function.update_of_ne h x (Function.update f b y),
        Function.update_self]
    · rw [Function.update_of_ne hzb y (Function.update f a x), Function.update_of_ne hza x f,
        Function.update_of_ne hza x (Function.update f b y), Function.update_of_ne hzb y f]

/-- Unfolding of `KKT` at `k+1`, in the `KaTail` form. -/
theorem ka_KKT_succT (G : ℝ → Submission.Diff.SMet I M) (t : ℝ) (k : ℕ)
    (w : Fin (k+1) → KaTF (I := I) (M := M)) (t3 : Fin 3 → KaTF (I := I) (M := M)) :
    KKT (I := I) (M := M) G t (k+1) w t3 = fun x =>
      mvfderiv I (KKT (I := I) (M := M) G t k (KaTail w) t3) x (w 0 x)
        - ∑ i : Fin k, KKT (I := I) (M := M) G t k
            (Function.update (KaTail w) i
              (fun y => Submission.Diff.lcOf (G 0) ((KaTail w) i) y (w 0 y))) t3 x
        - ∑ j : Fin 3, KKT (I := I) (M := M) G t k (KaTail w)
            (Function.update t3 j
              (fun y => Submission.Diff.lcOf (G 0) (t3 j) y (w 0 y))) x :=
  ka_KKT_succ G t k w t3

/-! ## The linearity of `covKAExt` in its slots -/



/-- The combined-family expansion of `∇_{W}X` for a field `X` that is a finite combination of
fields `V q` with coefficient functions `d q`: the Leibniz rule produces a sum of two families,
packaged as a single family over `ι ⊕ ι`. -/
lemma ka_lcOf_expand_two (G : ℝ → Submission.Diff.SMet I M) {U : Set M} (hU : IsOpen U)
    {ι : Type} [Fintype ι] {d : ι → M → ℝ} {V : ι → KaTF (I := I) (M := M)}
    {X W : KaTF (I := I) (M := M)} (hd : ∀ q, CMDiff[U] ∞ (d q))
    (hV : ∀ q, KaSm (I := I) (M := M) U (V q)) (hX : KaSm (I := I) (M := M) U X)
    (hW : KaSm (I := I) (M := M) U W)
    (hpt : ∀ y ∈ U, X y = ∑ q, d q y • V q y) :
    ∀ y ∈ U, Submission.Diff.lcOf (G 0) X y (W y)
      = ∑ s : ι ⊕ ι,
          (Sum.elim (fun q => d q) (fun q => fun y' => mvfderiv I (d q) y' (W y'))) s y
            • (Sum.elim (fun q => fun y' => Submission.Diff.lcOf (G 0) (V q) y' (W y'))
                (fun q => V q)) s y := by
  intro y hy
  have hgerm : X =ᶠ[𝓝 y] fun y' => ∑ q, d q y' • V q y' := by
    filter_upwards [hU.mem_nhds hy] with y' hy'
    exact hpt y' hy'
  rw [Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.cov_eq_sum_of_eventuallyEq_pointwise
    (cov := Submission.Diff.lcOf (G 0)) Finset.univ d V (hX.contMDiffAt (hU.mem_nhds hy))
    (fun q => (hV q).contMDiffAt (hU.mem_nhds hy))
    (fun q => (hd q).contMDiffAt (hU.mem_nhds hy)) hgerm]
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]

/-- `mvfderiv` of a real-valued function respects eventual equality.  (The library version
`Submission.ChartCurv.mvfderiv_congr_of_eventuallyEq` is stated for functions into the *model*
space `E`.) -/
lemma ka_mvfderiv_congr_real {f g : M → ℝ} {x : M} (h : f =ᶠ[𝓝 x] g) :
    mvfderiv I f x = mvfderiv I g x := by
  rw [mvfderiv, mvfderiv, h.eq_of_nhds, Filter.EventuallyEq.mfderiv_eq h]
  all_goals first | rfl | (ext v; rfl)


theorem ka_linAll (G : ℝ → Submission.Diff.SMet I M) (t : ℝ) {U : Set M} (hU : IsOpen U) :
    ∀ k, KaLinD G t U k ∧ KaLinT G t U k := by
  intro k
  induction k with
  | zero =>
      refine ⟨?_, ?_⟩
      · intro w i
        exact i.elim0
      · intro w t3 j W' ι _ d V hw h3 hW' hd hV hpt x hx
        fin_cases j
        · simp only [KKT, covKAExt, Function.update_self, ka_upd0_1, ka_upd0_2]
          exact ka_aOf_lin_0 G t hU d V (t3 1) (t3 2) W' hd hV (h3 1) (h3 2) hW' hpt x hx
        · simp only [KKT, covKAExt, ka_upd1_0, Function.update_self, ka_upd1_2]
          exact ka_aOf_lin_1 G t hU d V (t3 0) (t3 2) W' hd hV (h3 0) (h3 2) hW' hpt x hx
        · simp only [KKT, covKAExt, ka_upd2_0, ka_upd2_1, Function.update_self]
          exact ka_aOf_lin_2 G t hU d V (t3 0) (t3 1) W' hd hV (h3 0) (h3 1) hW' hpt x hx
  | succ k ih =>
      obtain ⟨ihD, ihT⟩ := ih
      refine ⟨?_, ?_⟩
      · -- linearity in a direction slot, at level `k+1`
        intro w i t3 W' ι _ d V hw h3 hW' hd hV hpt
        revert hW' hpt
        refine Fin.cases ?_ (fun i₀ => ?_) i
        · -- `i = 0`
          intro hW' hpt x hx
          have htail : ∀ s : Fin k, KaSm (I := I) (M := M) U (KaTail w s) := fun s => hw s.succ
          simp only [ka_KKT_succT, KaTail_update_zero, Function.update_self]
          have hL1 : mvfderiv I (KKT G t k (KaTail w) t3) x (W' x)
              = ∑ q, d q x * mvfderiv I (KKT G t k (KaTail w) t3) x (V q x) := by
            rw [hpt x hx, ka_clm_sum_smul_real]
            simp only [smul_eq_mul]
          have hL2 : (∑ i' : Fin k, KKT G t k
                (Function.update (KaTail w) i'
                  (fun y => Submission.Diff.lcOf (G 0) ((KaTail w) i') y (W' y))) t3 x)
              = ∑ q, d q x * ∑ i' : Fin k, KKT G t k
                  (Function.update (KaTail w) i'
                    (fun y => Submission.Diff.lcOf (G 0) ((KaTail w) i') y (V q y))) t3 x := by
            have h2 : ∀ i' : Fin k, KKT G t k
                (Function.update (KaTail w) i'
                  (fun y => Submission.Diff.lcOf (G 0) ((KaTail w) i') y (W' y))) t3 x
                = ∑ q, d q x * KKT G t k
                    (Function.update (KaTail w) i'
                      (fun y => Submission.Diff.lcOf (G 0) ((KaTail w) i') y (V q y))) t3 x :=
              fun i' => ihD (KaTail w) i' t3
                (fun y => Submission.Diff.lcOf (G 0) ((KaTail w) i') y (W' y)) d
                (fun q y => Submission.Diff.lcOf (G 0) ((KaTail w) i') y (V q y))
                htail h3
                (ka_lcField_smooth (I := I) (G 0) hU (hw i'.succ) hW')
                hd (fun q => ka_lcField_smooth (I := I) (G 0) hU (hw i'.succ) (hV q))
                (fun y hy => by
                  rw [hpt y hy]
                  exact ka_clm_sum_smul (Submission.Diff.lcOf (G 0) ((KaTail w) i') y)
                    (fun q => d q y) (fun q => V q y))
                x hx
            rw [Finset.sum_congr rfl (fun i' _ => h2 i'), Finset.sum_comm]
            exact Finset.sum_congr rfl (fun q _ => (Finset.mul_sum ..).symm)
          have hL3 : (∑ j : Fin 3, KKT G t k (KaTail w)
                (Function.update t3 j
                  (fun y => Submission.Diff.lcOf (G 0) (t3 j) y (W' y))) x)
              = ∑ q, d q x * ∑ j : Fin 3, KKT G t k (KaTail w)
                  (Function.update t3 j
                    (fun y => Submission.Diff.lcOf (G 0) (t3 j) y (V q y))) x := by
            have h2 : ∀ j : Fin 3, KKT G t k (KaTail w)
                (Function.update t3 j
                  (fun y => Submission.Diff.lcOf (G 0) (t3 j) y (W' y))) x
                = ∑ q, d q x * KKT G t k (KaTail w)
                    (Function.update t3 j
                      (fun y => Submission.Diff.lcOf (G 0) (t3 j) y (V q y))) x :=
              fun j => ihT (KaTail w) t3 j
                (fun y => Submission.Diff.lcOf (G 0) (t3 j) y (W' y)) d
                (fun q y => Submission.Diff.lcOf (G 0) (t3 j) y (V q y))
                htail h3
                (ka_lcField_smooth (I := I) (G 0) hU (h3 j) hW')
                hd (fun q => ka_lcField_smooth (I := I) (G 0) hU (h3 j) (hV q))
                (fun y hy => by
                  rw [hpt y hy]
                  exact ka_clm_sum_smul (Submission.Diff.lcOf (G 0) (t3 j) y)
                    (fun q => d q y) (fun q => V q y))
                x hx
            rw [Finset.sum_congr rfl (fun j _ => h2 j), Finset.sum_comm]
            exact Finset.sum_congr rfl (fun q _ => (Finset.mul_sum ..).symm)
          rw [show (∑ q, d q x * (mvfderiv I (KKT G t k (KaTail w) t3) x (V q x)
                - (∑ i' : Fin k, KKT G t k (Function.update (KaTail w) i'
                    (fun y => Submission.Diff.lcOf (G 0) ((KaTail w) i') y (V q y))) t3 x)
                - (∑ j : Fin 3, KKT G t k (KaTail w) (Function.update t3 j
                    (fun y => Submission.Diff.lcOf (G 0) (t3 j) y (V q y))) x)))
              = (∑ q, d q x * mvfderiv I (KKT G t k (KaTail w) t3) x (V q x))
                - (∑ q, d q x * ∑ i' : Fin k, KKT G t k (Function.update (KaTail w) i'
                    (fun y => Submission.Diff.lcOf (G 0) ((KaTail w) i') y (V q y))) t3 x)
                - (∑ q, d q x * ∑ j : Fin 3, KKT G t k (KaTail w) (Function.update t3 j
                    (fun y => Submission.Diff.lcOf (G 0) (t3 j) y (V q y))) x) from by
            rw [show (∑ q, d q x * mvfderiv I (KKT G t k (KaTail w) t3) x (V q x))
                  - (∑ q, d q x * ∑ i' : Fin k, KKT G t k (Function.update (KaTail w) i'
                      (fun y => Submission.Diff.lcOf (G 0) ((KaTail w) i') y (V q y))) t3 x)
                  - (∑ q, d q x * ∑ j : Fin 3, KKT G t k (KaTail w) (Function.update t3 j
                      (fun y => Submission.Diff.lcOf (G 0) (t3 j) y (V q y))) x)
                = ∑ q, (d q x * mvfderiv I (KKT G t k (KaTail w) t3) x (V q x)
                    - d q x * (∑ i' : Fin k, KKT G t k (Function.update (KaTail w) i'
                        (fun y => Submission.Diff.lcOf (G 0) ((KaTail w) i') y (V q y))) t3 x)
                    - d q x * (∑ j : Fin 3, KKT G t k (KaTail w) (Function.update t3 j
                        (fun y => Submission.Diff.lcOf (G 0) (t3 j) y (V q y))) x)) from by
              rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]]
            exact Finset.sum_congr rfl (fun q _ => by ring)]
          rw [hL1, hL2, hL3]
        · -- `i = Fin.succ i₀`
          intro hW' hpt x hx
          have htail : ∀ s : Fin k, KaSm (I := I) (M := M) U (KaTail w s) := fun s => hw s.succ
          have hdir : KaSm (I := I) (M := M) U (fun y : M => w 0 y) := hw 0
          have hKsm : ∀ (F : KaTF (I := I) (M := M)), KaSm (I := I) (M := M) U F →
              MDifferentiableAt I 𝓘(ℝ, ℝ) (KKT G t k (Function.update (KaTail w) i₀ F) t3) x := by
            intro F hF
            have hwa : ∀ s : Fin k, KaSm (I := I) (M := M) U
                ((Function.update (KaTail w) i₀ F) s) := by
              intro s
              by_cases hs : s = i₀
              · rw [hs, Function.update_self]; exact hF
              · rw [Function.update_of_ne hs]; exact htail s
            exact (((ka_KKT_smooth (I := I) (M := M) G t (U := U) hU k
              (Function.update (KaTail w) i₀ F) t3 hwa h3) x hx).contMDiffAt
                (hU.mem_nhds hx)).mdifferentiableAt (by simp)
          simp only [ka_KKT_succT, KaTail_update_succ, ka_upd_zero_succ]
          -- (1) the derivative term
          have hL1 : mvfderiv I (KKT G t k (Function.update (KaTail w) i₀ W') t3) x (w 0 x)
              = (∑ q, d q x * mvfderiv I (KKT G t k (Function.update (KaTail w) i₀ (V q)) t3) x (w 0 x))
                + ∑ q, mvfderiv I (d q) x (w 0 x)
                    * KKT G t k (Function.update (KaTail w) i₀ (V q)) t3 x := by
            have heq : KKT G t k (Function.update (KaTail w) i₀ W') t3
                =ᶠ[𝓝 x] ∑ q, d q * KKT G t k (Function.update (KaTail w) i₀ (V q)) t3 := by
              filter_upwards [hU.mem_nhds hx] with y hy
              rw [Finset.sum_apply]
              simp only [Pi.mul_apply]
              exact ihD (KaTail w) i₀ t3 W' d V htail h3 hW' hd hV hpt y hy
            rw [ka_mvfderiv_congr_real heq]
            rw [ka_mvfderiv_sum_mul (g := d)
              (f := fun q => KKT G t k (Function.update (KaTail w) i₀ (V q)) t3)
              (fun q => ((hd q).contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp))
              (fun q => hKsm (V q) (hV q))]
            rw [Finset.sum_add_distrib]
            ring
          -- (3) the tensor corrections
          have hL3 : (∑ j : Fin 3, KKT G t k (Function.update (KaTail w) i₀ W')
                (Function.update t3 j
                  (fun y => Submission.Diff.lcOf (G 0) (t3 j) y (w 0 y))) x)
              = ∑ q, d q x * ∑ j : Fin 3, KKT G t k (Function.update (KaTail w) i₀ (V q))
                  (Function.update t3 j
                    (fun y => Submission.Diff.lcOf (G 0) (t3 j) y (w 0 y))) x := by
            have hsm : ∀ j : Fin 3, KaSm (I := I) (M := M) U
                (fun y => Submission.Diff.lcOf (G 0) (t3 j) y (w 0 y)) :=
              fun j => ka_lcField_smooth (I := I) (G 0) hU (h3 j) hdir
            have h2 : ∀ j : Fin 3, KKT G t k (Function.update (KaTail w) i₀ W')
                (Function.update t3 j
                  (fun y => Submission.Diff.lcOf (G 0) (t3 j) y (w 0 y))) x
                = ∑ q, d q x * KKT G t k (Function.update (KaTail w) i₀ (V q))
                    (Function.update t3 j
                      (fun y => Submission.Diff.lcOf (G 0) (t3 j) y (w 0 y))) x := by
              intro j
              have h3j : ∀ j' : Fin 3, KaSm (I := I) (M := M) U
                  ((Function.update t3 j
                    (fun y => Submission.Diff.lcOf (G 0) (t3 j) y (w 0 y))) j') := by
                intro j'
                by_cases hj : j' = j
                · rw [hj, Function.update_self]; exact hsm j
                · rw [Function.update_of_ne hj]; exact h3 j'
              exact ihD (KaTail w) i₀
                (Function.update t3 j
                  (fun y => Submission.Diff.lcOf (G 0) (t3 j) y (w 0 y)))
                W' d V htail h3j hW' hd hV hpt x hx
            rw [Finset.sum_congr rfl (fun j _ => h2 j), Finset.sum_comm]
            exact Finset.sum_congr rfl (fun q _ => (Finset.mul_sum ..).symm)
          -- (2) the direction corrections
          have hmid : KKT G t k (Function.update (KaTail w) i₀
                (fun y => Submission.Diff.lcOf (G 0) W' y (w 0 y))) t3 x
              = (∑ q, d q x * KKT G t k (Function.update (KaTail w) i₀
                    (fun y => Submission.Diff.lcOf (G 0) (V q) y (w 0 y))) t3 x)
                + ∑ q, mvfderiv I (d q) x (w 0 x)
                    * KKT G t k (Function.update (KaTail w) i₀ (V q)) t3 x := by
            have hIH := ihD (KaTail w) i₀ t3
              (fun y => Submission.Diff.lcOf (G 0) W' y (w 0 y))
              (fun s => Sum.elim (fun q => d q)
                (fun q => fun y => mvfderiv I (d q) y (w 0 y)) s)
              (fun s => Sum.elim (fun q => fun y => Submission.Diff.lcOf (G 0) (V q) y (w 0 y))
                (fun q => V q) s)
              htail h3 (ka_lcField_smooth (I := I) (G 0) hU hW' hdir)
              (fun s => by
                rcases s with q | q
                · exact hd q
                · exact ka_mvfderiv_apply (I := I) hU (hd q) hdir)
              (fun s => by
                rcases s with q | q
                · exact ka_lcField_smooth (I := I) (G 0) hU (hV q) hdir
                · exact hV q)
              (fun y hy => ka_lcOf_expand_two (I := I) (G := G) hU hd hV hW' hdir hpt y hy) x hx
            rw [hIH, Fintype.sum_sum_type]
            simp only [Sum.elim_inl, Sum.elim_inr, smul_eq_mul]
          have hrest : ∀ i' ∈ (Finset.univ : Finset (Fin k)) \ {i₀},
              KKT G t k (Function.update (Function.update (KaTail w) i₀ W') i'
                (fun y => Submission.Diff.lcOf (G 0)
                  ((Function.update (KaTail w) i₀ W') i') y (w 0 y))) t3 x
              = ∑ q, d q x * KKT G t k (Function.update (Function.update (KaTail w) i₀ (V q)) i'
                  (fun y => Submission.Diff.lcOf (G 0)
                    ((Function.update (KaTail w) i₀ (V q)) i') y (w 0 y))) t3 x := by
            intro i' hi'
            have hne : i' ≠ i₀ := fun h => (Finset.mem_sdiff.mp hi').2 (Finset.mem_singleton.mpr h)
            have hsmT : ∀ s : Fin k, KaSm (I := I) (M := M) U
                ((Function.update (KaTail w) i'
                  (fun y => Submission.Diff.lcOf (G 0) ((KaTail w) i') y (w 0 y))) s) := by
              intro s
              by_cases hs : s = i'
              · rw [hs, Function.update_self]
                exact ka_lcField_smooth (I := I) (G 0) hU (hw i'.succ) hdir
              · rw [Function.update_of_ne hs]; exact htail s
            rw [show (Function.update (Function.update (KaTail w) i₀ W') i'
                  (fun y => Submission.Diff.lcOf (G 0)
                    ((Function.update (KaTail w) i₀ W') i') y (w 0 y)))
                = Function.update (Function.update (KaTail w) i'
                    (fun y => Submission.Diff.lcOf (G 0) ((KaTail w) i') y (w 0 y))) i₀ W'
                from by
              rw [Function.update_comm (Ne.symm hne) W'
                (fun y => Submission.Diff.lcOf (G 0)
                  ((Function.update (KaTail w) i₀ W') i') y (w 0 y)) (KaTail w)]
              congr 1
              congr 1
              funext y
              rw [Function.update_of_ne hne]]
            rw [ihD (Function.update (KaTail w) i'
                (fun y => Submission.Diff.lcOf (G 0) ((KaTail w) i') y (w 0 y))) i₀ t3 W' d V
              hsmT h3 hW' hd hV hpt x hx]
            refine Finset.sum_congr rfl (fun q _ => ?_)
            rw [show (Function.update (Function.update (KaTail w) i'
                    (fun y => Submission.Diff.lcOf (G 0) ((KaTail w) i') y (w 0 y))) i₀ (V q))
                = Function.update (Function.update (KaTail w) i₀ (V q)) i'
                    (fun y => Submission.Diff.lcOf (G 0)
                      ((Function.update (KaTail w) i₀ (V q)) i') y (w 0 y)) from by
              rw [Function.update_comm hne
                (fun y => Submission.Diff.lcOf (G 0) ((KaTail w) i') y (w 0 y)) (V q) (KaTail w)]
              congr 1
              congr 1
              funext y
              rw [Function.update_of_ne hne]]
          have hL2 : (∑ i' : Fin k, KKT G t k
                (Function.update (Function.update (KaTail w) i₀ W') i'
                  (fun y => Submission.Diff.lcOf (G 0)
                    ((Function.update (KaTail w) i₀ W') i') y (w 0 y))) t3 x)
              = (∑ q, d q x * ∑ i' : Fin k, KKT G t k
                    (Function.update (Function.update (KaTail w) i₀ (V q)) i'
                      (fun y => Submission.Diff.lcOf (G 0)
                        ((Function.update (KaTail w) i₀ (V q)) i') y (w 0 y))) t3 x)
                + ∑ q, mvfderiv I (d q) x (w 0 x)
                    * KKT G t k (Function.update (KaTail w) i₀ (V q)) t3 x := by
            rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ i₀)]
            rw [show (KKT G t k (Function.update (Function.update (KaTail w) i₀ W') i₀
                  (fun y => Submission.Diff.lcOf (G 0)
                    ((Function.update (KaTail w) i₀ W') i₀) y (w 0 y))) t3 x)
                = KKT G t k (Function.update (KaTail w) i₀
                    (fun y => Submission.Diff.lcOf (G 0) W' y (w 0 y))) t3 x from by
              congr 1
              rw [ka_upd_self_update]
              congr 1
              funext y
              rw [Function.update_self]]
            rw [hmid]
            rw [Finset.sum_congr rfl (fun i' hi' => hrest i' hi')]
            rw [show ((∑ q, d q x * KKT G t k (Function.update (KaTail w) i₀
                    (fun y => Submission.Diff.lcOf (G 0) (V q) y (w 0 y))) t3 x)
                  + ∑ q, mvfderiv I (d q) x (w 0 x)
                      * KKT G t k (Function.update (KaTail w) i₀ (V q)) t3 x)
                  + ∑ i' ∈ (Finset.univ : Finset (Fin k)) \ {i₀},
                      ∑ q, d q x * KKT G t k (Function.update (Function.update (KaTail w) i₀ (V q)) i'
                        (fun y => Submission.Diff.lcOf (G 0)
                          ((Function.update (KaTail w) i₀ (V q)) i') y (w 0 y))) t3 x
                = ((∑ q, d q x * KKT G t k (Function.update (KaTail w) i₀
                      (fun y => Submission.Diff.lcOf (G 0) (V q) y (w 0 y))) t3 x)
                    + ∑ i' ∈ (Finset.univ : Finset (Fin k)) \ {i₀},
                        ∑ q, d q x * KKT G t k (Function.update (Function.update (KaTail w) i₀ (V q)) i'
                          (fun y => Submission.Diff.lcOf (G 0)
                            ((Function.update (KaTail w) i₀ (V q)) i') y (w 0 y))) t3 x)
                  + ∑ q, mvfderiv I (d q) x (w 0 x)
                      * KKT G t k (Function.update (KaTail w) i₀ (V q)) t3 x from by
              ring]
            rw [Finset.sum_comm]
            rw [← Finset.sum_add_distrib]
            congr 1
            refine Finset.sum_congr rfl (fun q _ => ?_)
            rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ i₀), mul_add,
              Finset.mul_sum]
            rw [show (KKT G t k (Function.update (Function.update (KaTail w) i₀ (V q)) i₀
                    (fun y => Submission.Diff.lcOf (G 0)
                      ((Function.update (KaTail w) i₀ (V q)) i₀) y (w 0 y))) t3 x)
                  = KKT G t k (Function.update (KaTail w) i₀
                      (fun y => Submission.Diff.lcOf (G 0) (V q) y (w 0 y))) t3 x from by
              congr 1
              rw [ka_upd_self_update]
              congr 1
              funext y
              rw [Function.update_self]]
          rw [show (∑ q, d q x * (mvfderiv I (KKT G t k (Function.update (KaTail w) i₀ (V q)) t3) x (w 0 x)
                - (∑ i' : Fin k, KKT G t k (Function.update (Function.update (KaTail w) i₀ (V q)) i'
                    (fun y => Submission.Diff.lcOf (G 0)
                      ((Function.update (KaTail w) i₀ (V q)) i') y (w 0 y))) t3 x)
                - (∑ j : Fin 3, KKT G t k (Function.update (KaTail w) i₀ (V q))
                    (Function.update t3 j
                      (fun y => Submission.Diff.lcOf (G 0) (t3 j) y (w 0 y))) x)))
              = (∑ q, d q x * mvfderiv I (KKT G t k (Function.update (KaTail w) i₀ (V q)) t3) x (w 0 x))
                - (∑ q, d q x * ∑ i' : Fin k, KKT G t k (Function.update (Function.update (KaTail w) i₀ (V q)) i'
                    (fun y => Submission.Diff.lcOf (G 0)
                      ((Function.update (KaTail w) i₀ (V q)) i') y (w 0 y))) t3 x)
                - (∑ q, d q x * ∑ j : Fin 3, KKT G t k (Function.update (KaTail w) i₀ (V q))
                    (Function.update t3 j
                      (fun y => Submission.Diff.lcOf (G 0) (t3 j) y (w 0 y))) x) from by
            rw [show (∑ q, d q x * mvfderiv I (KKT G t k (Function.update (KaTail w) i₀ (V q)) t3) x (w 0 x))
                  - (∑ q, d q x * ∑ i' : Fin k, KKT G t k (Function.update (Function.update (KaTail w) i₀ (V q)) i'
                      (fun y => Submission.Diff.lcOf (G 0)
                        ((Function.update (KaTail w) i₀ (V q)) i') y (w 0 y))) t3 x)
                  - (∑ q, d q x * ∑ j : Fin 3, KKT G t k (Function.update (KaTail w) i₀ (V q))
                      (Function.update t3 j
                        (fun y => Submission.Diff.lcOf (G 0) (t3 j) y (w 0 y))) x)
                = ∑ q, (d q x * mvfderiv I (KKT G t k (Function.update (KaTail w) i₀ (V q)) t3) x (w 0 x)
                    - d q x * (∑ i' : Fin k, KKT G t k (Function.update (Function.update (KaTail w) i₀ (V q)) i'
                        (fun y => Submission.Diff.lcOf (G 0)
                          ((Function.update (KaTail w) i₀ (V q)) i') y (w 0 y))) t3 x)
                    - d q x * (∑ j : Fin 3, KKT G t k (Function.update (KaTail w) i₀ (V q))
                        (Function.update t3 j
                          (fun y => Submission.Diff.lcOf (G 0) (t3 j) y (w 0 y))) x)) from by
              rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]]
            exact Finset.sum_congr rfl (fun q _ => by ring)]
          rw [hL1, hL2, hL3]
          ring
      · -- linearity in a tensor slot, at level `k+1`
        intro w t3 j W' ι _ d V hw h3 hW' hd hV hpt x hx
        have htail : ∀ s : Fin k, KaSm (I := I) (M := M) U (KaTail w s) := fun s => hw s.succ
        have hdir : KaSm (I := I) (M := M) U (fun y : M => w 0 y) := hw 0
        have hKsm : ∀ (F : KaTF (I := I) (M := M)), KaSm (I := I) (M := M) U F →
            MDifferentiableAt I 𝓘(ℝ, ℝ) (KKT G t k (KaTail w) (Function.update t3 j F)) x := by
          intro F hF
          have h3a : ∀ j' : Fin 3, KaSm (I := I) (M := M) U ((Function.update t3 j F) j') := by
            intro j'
            by_cases hj : j' = j
            · rw [hj, Function.update_self]; exact hF
            · rw [Function.update_of_ne hj]; exact h3 j'
          exact (((ka_KKT_smooth (I := I) (M := M) G t (U := U) hU k (KaTail w)
            (Function.update t3 j F) htail h3a) x hx).contMDiffAt
              (hU.mem_nhds hx)).mdifferentiableAt (by simp)
        simp only [ka_KKT_succT]
        have hL1 : mvfderiv I (KKT G t k (KaTail w) (Function.update t3 j W')) x (w 0 x)
            = (∑ q, d q x * mvfderiv I (KKT G t k (KaTail w) (Function.update t3 j (V q))) x (w 0 x))
              + ∑ q, mvfderiv I (d q) x (w 0 x)
                  * KKT G t k (KaTail w) (Function.update t3 j (V q)) x := by
          have heq : KKT G t k (KaTail w) (Function.update t3 j W')
              =ᶠ[𝓝 x] ∑ q, d q * KKT G t k (KaTail w) (Function.update t3 j (V q)) := by
            filter_upwards [hU.mem_nhds hx] with y hy
            rw [Finset.sum_apply]
            simp only [Pi.mul_apply]
            exact ihT (KaTail w) t3 j W' d V htail h3 hW' hd hV hpt y hy
          rw [ka_mvfderiv_congr_real heq]
          rw [ka_mvfderiv_sum_mul (g := d)
            (f := fun q => KKT G t k (KaTail w) (Function.update t3 j (V q)))
            (fun q => ((hd q).contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp))
            (fun q => hKsm (V q) (hV q))]
          rw [Finset.sum_add_distrib]
          ring
        have hL2 : (∑ i' : Fin k, KKT G t k
              (Function.update (KaTail w) i'
                (fun y => Submission.Diff.lcOf (G 0) ((KaTail w) i') y (w 0 y)))
              (Function.update t3 j W') x)
            = ∑ q, d q x * ∑ i' : Fin k, KKT G t k
                (Function.update (KaTail w) i'
                  (fun y => Submission.Diff.lcOf (G 0) ((KaTail w) i') y (w 0 y)))
                (Function.update t3 j (V q)) x := by
          have h2 : ∀ i' : Fin k, KKT G t k
              (Function.update (KaTail w) i'
                (fun y => Submission.Diff.lcOf (G 0) ((KaTail w) i') y (w 0 y)))
              (Function.update t3 j W') x
              = ∑ q, d q x * KKT G t k
                  (Function.update (KaTail w) i'
                    (fun y => Submission.Diff.lcOf (G 0) ((KaTail w) i') y (w 0 y)))
                  (Function.update t3 j (V q)) x := by
            intro i'
            have hw' : ∀ s : Fin k, KaSm (I := I) (M := M) U
                ((Function.update (KaTail w) i'
                  (fun y => Submission.Diff.lcOf (G 0) ((KaTail w) i') y (w 0 y))) s) := by
              intro s
              by_cases hs : s = i'
              · rw [hs, Function.update_self]
                exact ka_lcField_smooth (I := I) (G 0) hU (hw i'.succ) hdir
              · rw [Function.update_of_ne hs]; exact htail s
            exact ihT (Function.update (KaTail w) i'
                (fun y => Submission.Diff.lcOf (G 0) ((KaTail w) i') y (w 0 y)))
              t3 j W' d V hw' h3 hW' hd hV hpt x hx
          rw [Finset.sum_congr rfl (fun i' _ => h2 i'), Finset.sum_comm]
          exact Finset.sum_congr rfl (fun q _ => (Finset.mul_sum ..).symm)
        have hmid : KKT G t k (KaTail w) (Function.update t3 j
              (fun y => Submission.Diff.lcOf (G 0) W' y (w 0 y))) x
            = (∑ q, d q x * KKT G t k (KaTail w) (Function.update t3 j
                  (fun y => Submission.Diff.lcOf (G 0) (V q) y (w 0 y))) x)
              + ∑ q, mvfderiv I (d q) x (w 0 x)
                  * KKT G t k (KaTail w) (Function.update t3 j (V q)) x := by
          have hIH := ihT (KaTail w) t3 j
            (fun y => Submission.Diff.lcOf (G 0) W' y (w 0 y))
            (fun s => Sum.elim (fun q => d q)
              (fun q => fun y => mvfderiv I (d q) y (w 0 y)) s)
            (fun s => Sum.elim (fun q => fun y => Submission.Diff.lcOf (G 0) (V q) y (w 0 y))
              (fun q => V q) s)
            htail h3 (ka_lcField_smooth (I := I) (G 0) hU hW' hdir)
            (fun s => by
              rcases s with q | q
              · exact hd q
              · exact ka_mvfderiv_apply (I := I) hU (hd q) hdir)
            (fun s => by
              rcases s with q | q
              · exact ka_lcField_smooth (I := I) (G 0) hU (hV q) hdir
              · exact hV q)
            (fun y hy => ka_lcOf_expand_two (I := I) (G := G) hU hd hV hW' hdir hpt y hy) x hx
          rw [hIH, Fintype.sum_sum_type]
          simp only [Sum.elim_inl, Sum.elim_inr, smul_eq_mul]
        have hrest : ∀ j' ∈ (Finset.univ : Finset (Fin 3)) \ {j},
            KKT G t k (KaTail w) (Function.update (Function.update t3 j W') j'
              (fun y => Submission.Diff.lcOf (G 0)
                ((Function.update t3 j W') j') y (w 0 y))) x
            = ∑ q, d q x * KKT G t k (KaTail w)
                (Function.update (Function.update t3 j (V q)) j'
                  (fun y => Submission.Diff.lcOf (G 0)
                    ((Function.update t3 j (V q)) j') y (w 0 y))) x := by
          intro j' hj'
          have hne : j' ≠ j := fun h => (Finset.mem_sdiff.mp hj').2 (Finset.mem_singleton.mpr h)
          have h3T : ∀ j'' : Fin 3, KaSm (I := I) (M := M) U
              ((Function.update t3 j'
                (fun y => Submission.Diff.lcOf (G 0) (t3 j') y (w 0 y))) j'') := by
            intro j''
            by_cases hj : j'' = j'
            · rw [hj, Function.update_self]
              exact ka_lcField_smooth (I := I) (G 0) hU (h3 j') hdir
            · rw [Function.update_of_ne hj]; exact h3 j''
          rw [show (Function.update (Function.update t3 j W') j'
                (fun y => Submission.Diff.lcOf (G 0)
                  ((Function.update t3 j W') j') y (w 0 y)))
              = Function.update (Function.update t3 j'
                  (fun y => Submission.Diff.lcOf (G 0) (t3 j') y (w 0 y))) j W'
              from by
            rw [Function.update_comm (Ne.symm hne) W'
              (fun y => Submission.Diff.lcOf (G 0) ((Function.update t3 j W') j') y (w 0 y)) t3]
            congr 1
            congr 1
            funext y
            rw [Function.update_of_ne hne]]
          rw [ihT (KaTail w) (Function.update t3 j'
                (fun y => Submission.Diff.lcOf (G 0) (t3 j') y (w 0 y))) j W' d V
              htail h3T hW' hd hV hpt x hx]
          refine Finset.sum_congr rfl (fun q _ => ?_)
          rw [show (Function.update (Function.update t3 j'
                  (fun y => Submission.Diff.lcOf (G 0) (t3 j') y (w 0 y))) j (V q))
                = Function.update (Function.update t3 j (V q)) j'
                    (fun y => Submission.Diff.lcOf (G 0)
                      ((Function.update t3 j (V q)) j') y (w 0 y)) from by
            rw [Function.update_comm hne
              (fun y => Submission.Diff.lcOf (G 0) (t3 j') y (w 0 y)) (V q) t3]
            congr 1
            congr 1
            funext y
            rw [Function.update_of_ne hne]]
        have hL3 : (∑ j' : Fin 3, KKT G t k (KaTail w)
              (Function.update (Function.update t3 j W') j'
                (fun y => Submission.Diff.lcOf (G 0)
                  ((Function.update t3 j W') j') y (w 0 y))) x)
            = (∑ q, d q x * ∑ j' : Fin 3, KKT G t k (KaTail w)
                  (Function.update (Function.update t3 j (V q)) j'
                    (fun y => Submission.Diff.lcOf (G 0)
                      ((Function.update t3 j (V q)) j') y (w 0 y))) x)
              + ∑ q, mvfderiv I (d q) x (w 0 x)
                  * KKT G t k (KaTail w) (Function.update t3 j (V q)) x := by
          rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ j)]
          rw [show (KKT G t k (KaTail w) (Function.update (Function.update t3 j W') j
                (fun y => Submission.Diff.lcOf (G 0)
                  ((Function.update t3 j W') j) y (w 0 y))) x)
              = KKT G t k (KaTail w) (Function.update t3 j
                  (fun y => Submission.Diff.lcOf (G 0) W' y (w 0 y))) x from by
            congr 1
            rw [ka_upd_self_update]
            congr 1
            funext y
            rw [Function.update_self]]
          rw [hmid]
          rw [Finset.sum_congr rfl (fun j' hj' => hrest j' hj')]
          rw [show ((∑ q, d q x * KKT G t k (KaTail w) (Function.update t3 j
                    (fun y => Submission.Diff.lcOf (G 0) (V q) y (w 0 y))) x)
                  + ∑ q, mvfderiv I (d q) x (w 0 x)
                      * KKT G t k (KaTail w) (Function.update t3 j (V q)) x)
                  + ∑ j' ∈ (Finset.univ : Finset (Fin 3)) \ {j},
                      ∑ q, d q x * KKT G t k (KaTail w)
                        (Function.update (Function.update t3 j (V q)) j'
                          (fun y => Submission.Diff.lcOf (G 0)
                            ((Function.update t3 j (V q)) j') y (w 0 y))) x
                = ((∑ q, d q x * KKT G t k (KaTail w) (Function.update t3 j
                      (fun y => Submission.Diff.lcOf (G 0) (V q) y (w 0 y))) x)
                    + ∑ j' ∈ (Finset.univ : Finset (Fin 3)) \ {j},
                        ∑ q, d q x * KKT G t k (KaTail w)
                          (Function.update (Function.update t3 j (V q)) j'
                            (fun y => Submission.Diff.lcOf (G 0)
                              ((Function.update t3 j (V q)) j') y (w 0 y))) x)
                  + ∑ q, mvfderiv I (d q) x (w 0 x)
                      * KKT G t k (KaTail w) (Function.update t3 j (V q)) x from by
            ring]
          rw [Finset.sum_comm]
          rw [← Finset.sum_add_distrib]
          congr 1
          refine Finset.sum_congr rfl (fun q _ => ?_)
          rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ j), mul_add,
            Finset.mul_sum]
          rw [show (KKT G t k (KaTail w) (Function.update (Function.update t3 j (V q)) j
                  (fun y => Submission.Diff.lcOf (G 0)
                    ((Function.update t3 j (V q)) j) y (w 0 y))) x)
                = KKT G t k (KaTail w) (Function.update t3 j
                    (fun y => Submission.Diff.lcOf (G 0) (V q) y (w 0 y))) x from by
            congr 1
            rw [ka_upd_self_update]
            congr 1
            funext y
            rw [Function.update_self]]
        rw [show (∑ q, d q x * (mvfderiv I (KKT G t k (KaTail w) (Function.update t3 j (V q))) x (w 0 x)
              - (∑ i' : Fin k, KKT G t k (Function.update (KaTail w) i'
                  (fun y => Submission.Diff.lcOf (G 0) ((KaTail w) i') y (w 0 y)))
                  (Function.update t3 j (V q)) x)
              - (∑ j' : Fin 3, KKT G t k (KaTail w)
                  (Function.update (Function.update t3 j (V q)) j'
                    (fun y => Submission.Diff.lcOf (G 0)
                      ((Function.update t3 j (V q)) j') y (w 0 y))) x)))
            = (∑ q, d q x * mvfderiv I (KKT G t k (KaTail w) (Function.update t3 j (V q))) x (w 0 x))
              - (∑ q, d q x * ∑ i' : Fin k, KKT G t k (Function.update (KaTail w) i'
                  (fun y => Submission.Diff.lcOf (G 0) ((KaTail w) i') y (w 0 y)))
                  (Function.update t3 j (V q)) x)
              - (∑ q, d q x * ∑ j' : Fin 3, KKT G t k (KaTail w)
                  (Function.update (Function.update t3 j (V q)) j'
                    (fun y => Submission.Diff.lcOf (G 0)
                      ((Function.update t3 j (V q)) j') y (w 0 y))) x) from by
          rw [show (∑ q, d q x * mvfderiv I (KKT G t k (KaTail w) (Function.update t3 j (V q))) x (w 0 x))
                - (∑ q, d q x * ∑ i' : Fin k, KKT G t k (Function.update (KaTail w) i'
                    (fun y => Submission.Diff.lcOf (G 0) ((KaTail w) i') y (w 0 y)))
                    (Function.update t3 j (V q)) x)
                - (∑ q, d q x * ∑ j' : Fin 3, KKT G t k (KaTail w)
                    (Function.update (Function.update t3 j (V q)) j'
                      (fun y => Submission.Diff.lcOf (G 0)
                        ((Function.update t3 j (V q)) j') y (w 0 y))) x)
              = ∑ q, (d q x * mvfderiv I (KKT G t k (KaTail w) (Function.update t3 j (V q))) x (w 0 x)
                  - d q x * (∑ i' : Fin k, KKT G t k (Function.update (KaTail w) i'
                      (fun y => Submission.Diff.lcOf (G 0) ((KaTail w) i') y (w 0 y)))
                      (Function.update t3 j (V q)) x)
                  - d q x * (∑ j' : Fin 3, KKT G t k (KaTail w)
                      (Function.update (Function.update t3 j (V q)) j'
                        (fun y => Submission.Diff.lcOf (G 0)
                          ((Function.update t3 j (V q)) j') y (w 0 y))) x)) from by
            rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]]
          exact Finset.sum_congr rfl (fun q _ => by ring)]
        rw [hL1, hL2, hL3]
        ring

theorem aCovArr_eq_covKAExt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (G : ℝ → Submission.Diff.SMet I M) (x₀ : M) (t : ℝ) (k : ℕ)
    (v : Fin k → Fin (Module.finrank ℝ E)) (i j l : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) :
    Work.Diff.EXT.aCovArr (I := I) (M := M) G x₀ t k v i j l y
      = Work.Diff.EXT.covKAExt G t k (fun s : Fin k => Work.Diff.GE.cFrame (I := I) x₀ (v s))
          (Work.Diff.GE.cFrame (I := I) x₀ i) (Work.Diff.GE.cFrame (I := I) x₀ j)
          (Work.Diff.GE.cFrame (I := I) x₀ l) (Work.Diff.EXT.pt (I := I) x₀ y) := by
  have hlin := ka_linAll (I := I) (M := M) G t (U := (chartAt H x₀).source)
    (chartAt H x₀).open_source
  exact ka_main (I := I) (M := M) G x₀ t (fun k => (hlin k).1) (fun k => (hlin k).2)
    k v i j l hy

end Work.Diff.EXT
