import Mathlib
import Submission.Work.Diff.EXT.reactBase
import Submission.Work.Diff.EXT.evX.pairing_mvfderivV
import Submission.Work.Diff.EXT.evX.mvfderiv_rmSymV
import Submission.Work.Diff.GE.Gest.hess_mul_field

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT.evX

set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

set_option backward.isDefEq.respectTransparency false

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]

/-! ## Componentwise differentiability and smoothness -/

/-- The `(i,j,k,l)`-component of a `Curv4`-valued map differentiable at `x` is differentiable. -/
theorem mdiffAt_curv4_comp {n : ℕ} {A : M → Curv4 n} {x : M}
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

section Smoothness

/-- The tuple `Fin.append D ![e i, e j, e k, e l]` of a tower is smooth. -/
theorem append_smoothT {a : ℕ} {D : Fin a → TField (I := I) (M := M)}
    (hD : ∀ r, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (D r))
    {e : Fin (Module.finrank ℝ E) → TField (I := I) (M := M)}
    (he : ∀ i, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (e i))
    (i j k l : Fin (Module.finrank ℝ E)) :
    ∀ s : Fin (a + 4),
      Work.Diff.GE.SmoothFieldT (I := I) (M := M)
        ((Fin.append D ![e i, e j, e k, e l]) s) := by
  intro s
  refine Fin.addCases ?_ ?_ s
  · intro r; rw [Fin.append_left]; exact hD r
  · intro t; rw [Fin.append_right]
    fin_cases t
    · simpa using he i
    · simpa using he j
    · simpa using he k
    · simpa using he l

/-- The `(i,j,k,l)`-component of the tower array `∇^a Rm` in the frame `e` is differentiable. -/
theorem TowerArr_mdiffAt (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M)
    (a : ℕ) (D : Fin a → TField (I := I) (M := M))
    (hD : ∀ r, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (D r))
    (e : Fin (Module.finrank ℝ E) → TField (I := I) (M := M))
    (he : ∀ i, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (e i))
    (z : M) (i j k l : Fin (Module.finrank ℝ E)) :
    MDifferentiableAt I (modelWithCornersSelf ℝ ℝ)
      (fun y => Work.Diff.EXT.TowerArr g a D e y i j k l) z := by
  have htup := append_smoothT (I := I) (M := M) hD he i j k l
  have h := (Work.Diff.EXT.tensProp_all hLC g a
    (Fin.append D ![e i, e j, e k, e l]) htup).1
  change MDifferentiableAt I (modelWithCornersSelf ℝ ℝ)
    (fun y => Work.Diff.EXT.ckt g a (Fin.append D ![e i, e j, e k, e l]) y) z
  exact h.contMDiffAt.mdifferentiableAt (by simp)

/-- The metric pairing of two smooth fields is smooth. -/
theorem metricPairing_smooth (g : Submission.Diff.SMet I M)
    {Y Z : TField (I := I) (M := M)}
    (hY : Work.Diff.GE.SmoothFieldT (I := I) (M := M) Y)
    (hZ : Work.Diff.GE.SmoothFieldT (I := I) (M := M) Z) :
    CMDiff ∞ (fun y : M => g.inner y (Y y) (Z y)) := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  change CMDiff ∞ (fun y : M => inner ℝ (Y y) (Z y))
  exact ContMDiff.inner_bundle (IB := I) (b := id) (v := Y) (w := Z) hY hZ

/-- The metric pairing of two smooth fields is differentiable. -/
theorem metricPairing_mdiffAt (g : Submission.Diff.SMet I M)
    {Y Z : TField (I := I) (M := M)}
    (hY : Work.Diff.GE.SmoothFieldT (I := I) (M := M) Y)
    (hZ : Work.Diff.GE.SmoothFieldT (I := I) (M := M) Z) (y : M) :
    MDifferentiableAt I (modelWithCornersSelf ℝ ℝ)
      (fun z => g.inner z (Y z) (Z z)) y :=
  (metricPairing_smooth g hY hZ).contMDiffAt.mdifferentiableAt (by simp)

end Smoothness

/-! ## The pairing product of the four reaction slots -/

/-- The product of the four pairings of the frame with the four `reactionMap`-slots. -/
noncomputable def pairProd (g : Submission.Diff.SMet I M)
    (e : Fin (Module.finrank ℝ E) → TField (I := I) (M := M))
    (sl : Fin 4 → TField (I := I) (M := M))
    (i j k l : Fin (Module.finrank ℝ E)) : M → ℝ :=
  fun y => g.inner y (e i y) (sl 0 y) * g.inner y (e j y) (sl 1 y)
    * g.inner y (e k y) (sl 2 y) * g.inner y (e l y) (sl 3 y)

/-- The derivative of the pairing product along `X`: the sum of the four terms in which one pairing
is replaced by its covariant derivative. -/
theorem pairProd_mvfderiv (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M)
    (y : M) (e : Fin (Module.finrank ℝ E) → TField (I := I) (M := M))
    (he : ∀ i, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (e i))
    (hgeo : ∀ i, Submission.Diff.lcOf g (e i) y = 0)
    (sl : Fin 4 → TField (I := I) (M := M))
    (hsl : ∀ t, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (sl t))
    (X : TField (I := I) (M := M)) (hX : Work.Diff.GE.SmoothFieldT (I := I) (M := M) X)
    (i j k l : Fin (Module.finrank ℝ E)) :
    (mvfderiv I (pairProd g e sl i j k l) y) (X y)
      = g.inner y (e j y) (sl 1 y) * g.inner y (e k y) (sl 2 y) * g.inner y (e l y) (sl 3 y)
          * g.inner y (e i y) (Work.Diff.EXT.dirF g (sl 0) X y)
        + g.inner y (e i y) (sl 0 y) * g.inner y (e k y) (sl 2 y) * g.inner y (e l y) (sl 3 y)
          * g.inner y (e j y) (Work.Diff.EXT.dirF g (sl 1) X y)
        + g.inner y (e i y) (sl 0 y) * g.inner y (e j y) (sl 1 y) * g.inner y (e l y) (sl 3 y)
          * g.inner y (e k y) (Work.Diff.EXT.dirF g (sl 2) X y)
        + g.inner y (e i y) (sl 0 y) * g.inner y (e j y) (sl 1 y) * g.inner y (e k y) (sl 2 y)
          * g.inner y (e l y) (Work.Diff.EXT.dirF g (sl 3) X y) := by
  have h1 : CMDiff ∞ (fun z => g.inner z (e i z) (sl 0 z)) :=
    metricPairing_smooth g (he i) (hsl 0)
  have h2 : CMDiff ∞ (fun z => g.inner z (e j z) (sl 1 z)) :=
    metricPairing_smooth g (he j) (hsl 1)
  have h3 : CMDiff ∞ (fun z => g.inner z (e k z) (sl 2 z)) :=
    metricPairing_smooth g (he k) (hsl 2)
  have h4 : CMDiff ∞ (fun z => g.inner z (e l z) (sl 3 z)) :=
    metricPairing_smooth g (he l) (hsl 3)
  have h12 : CMDiff ∞ (fun z => g.inner z (e i z) (sl 0 z) * g.inner z (e j z) (sl 1 z)) :=
    h1.mul h2
  have h123 : CMDiff ∞ (fun z => g.inner z (e i z) (sl 0 z) * g.inner z (e j z) (sl 1 z)
      * g.inner z (e k z) (sl 2 z)) := h12.mul h3
  have e1 := Work.Diff.GE.Gest.mvfderiv_mul_apply (I := I) (M := M)
    (u := fun z : M => g.inner z (e i z) (sl 0 z) * g.inner z (e j z) (sl 1 z)
      * g.inner z (e k z) (sl 2 z))
    (v := fun z : M => g.inner z (e l z) (sl 3 z)) h123 h4 y (X y)
  have e2 := Work.Diff.GE.Gest.mvfderiv_mul_apply (I := I) (M := M)
    (u := fun z : M => g.inner z (e i z) (sl 0 z) * g.inner z (e j z) (sl 1 z))
    (v := fun z : M => g.inner z (e k z) (sl 2 z)) h12 h3 y (X y)
  have e3 := Work.Diff.GE.Gest.mvfderiv_mul_apply (I := I) (M := M)
    (u := fun z : M => g.inner z (e i z) (sl 0 z))
    (v := fun z : M => g.inner z (e j z) (sl 1 z)) h1 h2 y (X y)
  change (mvfderiv I (fun z : M => g.inner z (e i z) (sl 0 z) * g.inner z (e j z) (sl 1 z)
      * g.inner z (e k z) (sl 2 z) * g.inner z (e l z) (sl 3 z)) y) (X y) = _
  rw [e1, e2, e3]
  rw [pairing_mvfderivV (I := I) (M := M) hLC g y e he hgeo (sl 0) (hsl 0) X hX i,
      pairing_mvfderivV (I := I) (M := M) hLC g y e he hgeo (sl 1) (hsl 1) X hX j,
      pairing_mvfderivV (I := I) (M := M) hLC g y e he hgeo (sl 2) (hsl 2) X hX k,
      pairing_mvfderivV (I := I) (M := M) hLC g y e he hgeo (sl 3) (hsl 3) X hX l]
  ring

/-! ## The Leibniz recursion of the tower -/

/-- `Fin.cons` of a concatenation splits the concatenation. -/
theorem cons_append_eq {a : ℕ} (X : TField (I := I) (M := M))
    (D : Fin a → TField (I := I) (M := M)) (B : Fin 4 → TField (I := I) (M := M)) :
    (Fin.cons X (Fin.append D B) : Fin (a + 1 + 4) → TField (I := I) (M := M))
      = Fin.append (Fin.cons X D) B := by
  funext s
  refine Fin.addCases (m := a + 1) (n := 4) ?_ ?_ s
  · intro r
    refine Fin.cases ?_ ?_ r
    · rw [Fin.append_left, Fin.cons_zero]
      have h0 : (Fin.castAdd 4 (0 : Fin (a + 1)) : Fin (a + 4 + 1)) = 0 := by ext; simp
      rw [h0, Fin.cons_zero]
    · intro r'
      have h1 : (Fin.castAdd 4 r'.succ : Fin (a + 1 + 4))
          = (Fin.castAdd 4 (r' : Fin a) : Fin (a + 4)).succ := by
        ext; simp only [Fin.val_castAdd, Fin.val_succ]
      rw [Fin.append_left, Fin.cons_succ, h1, Fin.cons_succ, Fin.append_left]
  · intro t
    rw [Fin.append_right]
    have h : (Fin.natAdd (a + 1) t : Fin (a + 1 + 4)) = (Fin.natAdd a t).succ := by
      ext; simp only [Fin.val_natAdd, Fin.val_succ]; omega
    rw [h, Fin.cons_succ, Fin.append_right]

/-- Updating a direction slot of a concatenation. -/
theorem update_append_eq {a : ℕ} (D : Fin a → TField (I := I) (M := M))
    (B : Fin 4 → TField (I := I) (M := M)) (r : Fin a) (W : TField (I := I) (M := M)) :
    (Function.update (Fin.append D B) (Fin.castAdd 4 r) W : Fin (a + 4) → TField (I := I) (M := M))
      = Fin.append (Function.update D r W) B := by
  funext s
  refine Fin.addCases (m := a) (n := 4) ?_ ?_ s
  · intro r'
    rw [Fin.append_left]
    rcases eq_or_ne r' r with h | h
    · subst h; rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne (fun hh => h (Fin.castAdd_inj.mp hh)) W (Fin.append D B),
        Fin.append_left, Function.update_of_ne h]
  · intro t
    rw [Fin.append_right]
    have hne : (Fin.natAdd a t : Fin (a + 4)) ≠ Fin.castAdd 4 r := by
      intro hh
      have hv := congrArg Fin.val hh
      simp only [Fin.val_natAdd, Fin.val_castAdd] at hv
      have := r.isLt
      omega
    rw [Function.update_of_ne hne, Fin.append_right]

/-- **The Leibniz recursion of the tower**: the directional derivative of the `(i,j,k,l)`-component
of `∇^a Rm` in the frame `e` along `X` is the component of `∇^{a+1} Rm` plus the `a` correction terms
in which one differentiation slot is replaced by its covariant derivative.  The corrections of the
four *curvature* slots vanish because the frame is parallel at `y`. -/
theorem TowerArr_mvfderiv (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M)
    (y : M) (e : Fin (Module.finrank ℝ E) → TField (I := I) (M := M))
    (he : ∀ i, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (e i))
    (hgeo : ∀ i, Submission.Diff.lcOf g (e i) y = 0)
    (a : ℕ) (D : Fin a → TField (I := I) (M := M))
    (hD : ∀ r, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (D r))
    (X : TField (I := I) (M := M)) (hX : Work.Diff.GE.SmoothFieldT (I := I) (M := M) X) :
    ∀ i j k l, mvfderiv I (fun z => Work.Diff.EXT.TowerArr g a D e z i j k l) y (X y)
      = Work.Diff.EXT.TowerArr g (a + 1) (Fin.cons X D) e y i j k l
        + ∑ r : Fin a, Work.Diff.EXT.TowerArr g a
            (Function.update D r (Work.Diff.EXT.dirF g (D r) X)) e y i j k l := by
  intro i j k l
  have htup := append_smoothT (I := I) (M := M) hD he i j k l
  have hmain := Work.Diff.EXT.mvfderiv_ckt_T2 (I := I) (M := M) g a
    (Fin.append D ![e i, e j, e k, e l]) X y
  change mvfderiv I (fun z => Work.Diff.EXT.ckt g a
      (Fin.append D ![e i, e j, e k, e l]) z) y (X y)
    = Work.Diff.EXT.ckt g (a + 1) (Fin.append (Fin.cons X D) ![e i, e j, e k, e l]) y
      + ∑ r : Fin a, Work.Diff.EXT.ckt g a
          (Fin.append (Function.update D r (Work.Diff.EXT.dirF g (D r) X))
            ![e i, e j, e k, e l]) y
  rw [hmain, ← cons_append_eq X D ![e i, e j, e k, e l]]
  congr 1
  rw [Fin.sum_univ_add]
  have hzero : (∑ t : Fin 4, Work.Diff.EXT.ckt g a
      (Function.update (Fin.append D ![e i, e j, e k, e l]) (Fin.natAdd a t)
        (Work.Diff.EXT.dirF g ((Fin.append D ![e i, e j, e k, e l]) (Fin.natAdd a t)) X)) y) = 0 := by
    refine Finset.sum_eq_zero (fun t _ => ?_)
    rw [Fin.append_right]
    have hBsm : ∀ t : Fin 4, Work.Diff.GE.SmoothFieldT (I := I) (M := M)
        ((![e i, e j, e k, e l] : Fin 4 → TField (I := I) (M := M)) t) := by
      intro t
      fin_cases t
      · simpa using he i
      · simpa using he j
      · simpa using he k
      · simpa using he l
    have hY : Work.Diff.EXT.SmoothF (Work.Diff.EXT.dirF g
        ((![e i, e j, e k, e l] : Fin 4 → TField (I := I) (M := M)) t) X) :=
      Work.Diff.EXT.dirF_smooth (I := I) (M := M) hLC g (hBsm t) hX
    have hYx : (Work.Diff.EXT.dirF g
        ((![e i, e j, e k, e l] : Fin 4 → TField (I := I) (M := M)) t) X) y = 0 := by
      simp only [Work.Diff.EXT.dirF]
      fin_cases t <;> simp [hgeo]
    exact Work.Diff.EXT.ckt_zero_slot_T2 (I := I) (M := M) hLC g a htup
      (Fin.natAdd a t) y hY hYx
  rw [hzero, add_zero]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [Fin.append_left, update_append_eq]

/-! ## Sum and product rules for `mvfderiv` in the pointwise (evaluated) form -/

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

/-- The product rule for a product of four functions. -/
theorem mvfderiv_prod4_pt (f₁ f₂ f₃ f₄ : M → ℝ) {y : M} (v : TangentSpace I y)
    (h₁ : MDifferentiableAt I (modelWithCornersSelf ℝ ℝ) f₁ y)
    (h₂ : MDifferentiableAt I (modelWithCornersSelf ℝ ℝ) f₂ y)
    (h₃ : MDifferentiableAt I (modelWithCornersSelf ℝ ℝ) f₃ y)
    (h₄ : MDifferentiableAt I (modelWithCornersSelf ℝ ℝ) f₄ y) :
    (mvfderiv I (fun z => f₁ z * f₂ z * f₃ z * f₄ z) y) v
      = f₂ y * f₃ y * f₄ y * (mvfderiv I f₁ y) v
        + f₁ y * f₃ y * f₄ y * (mvfderiv I f₂ y) v
        + f₁ y * f₂ y * f₄ y * (mvfderiv I f₃ y) v
        + f₁ y * f₂ y * f₃ y * (mvfderiv I f₄ y) v := by
  have h12 : MDifferentiableAt I (modelWithCornersSelf ℝ ℝ) (fun z => f₁ z * f₂ z) y := h₁.mul h₂
  have h123 : MDifferentiableAt I (modelWithCornersSelf ℝ ℝ)
      (fun z => f₁ z * f₂ z * f₃ z) y := h12.mul h₃
  have e1 := mvfderiv_mul_pt (f := fun z => f₁ z * f₂ z * f₃ z) (g := f₄) v h123 h₄
  have e2 := mvfderiv_mul_pt (f := fun z => f₁ z * f₂ z) (g := f₃) v h12 h₃
  have e3 := mvfderiv_mul_pt (f := f₁) (g := f₂) v h₁ h₂
  change (mvfderiv I (fun z => f₁ z * f₂ z * f₃ z * f₄ z) y) v = _
  rw [e1, e2, e3]
  ring

/-- The chain rule over a quadruple sum of products, in the evaluated form. -/
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

/-- `rmSym` is additive in its first argument, for finite sums. -/
theorem rmSym_sum_left {n : ℕ} {ι : Type*} (t : Finset ι) (X : ι → Curv4 n) (Y : Curv4 n) :
    rmSym (∑ i ∈ t, X i) Y = ∑ i ∈ t, rmSym (X i) Y := by
  have h := map_sum (rmSymCLM n) X t
  have h2 := congrArg (fun L : Curv4 n →L[ℝ] Curv4 n => L Y) h
  simpa only [ContinuousLinearMap.sum_apply, rmSymCLM_apply] using h2

/-! ## The decomposition of the sum over the tuple slots -/

/-- **The sum over the tuple slots splits along the three index maps.**  If `d₁`, `d₂`, `s` are
injective with pairwise disjoint images covering `Fin N`, then the sum over `Fin N` of any family is
the sum over the three index sets. -/
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

/-- Moving the sum over `Fin a` out of a quadruple sum over the frame indices. -/
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

/-! ## Updating the tuple at a slot -/

/-- Updating a tuple at the image of `d` and restricting to the image of `d`. -/
theorem update_comp_same {N a : ℕ} (tup : Fin N → TField (I := I) (M := M))
    (d : Fin a → Fin N) (hinj : Function.Injective d) (r : Fin a)
    (W : TField (I := I) (M := M)) :
    (fun r' : Fin a => (Function.update tup (d r) W) (d r'))
      = Function.update (fun r' : Fin a => tup (d r')) r W := by
  funext r'
  rcases eq_or_ne r' r with h | h
  · subst h; rw [Function.update_self, Function.update_self]
  · rw [Function.update_of_ne (fun hh => h (hinj hh)) W tup, Function.update_of_ne h]

/-- Updating a tuple at the image of `d` and restricting to the image of `d'` (disjoint from `d`). -/
theorem update_comp_ne {N a a' : ℕ} (tup : Fin N → TField (I := I) (M := M))
    (d : Fin a → Fin N) (d' : Fin a' → Fin N) (h : ∀ r r', d r ≠ d' r') (r : Fin a)
    (W : TField (I := I) (M := M)) :
    (fun r' : Fin a' => (Function.update tup (d r) W) (d' r')) = fun r' => tup (d' r') := by
  funext r'
  rw [Function.update_of_ne (Ne.symm (h r r')) W tup]


/-- Applying a sum of `Curv4`-valued functions at a multi-index. -/
theorem sum_app4 {n : ℕ} {ι : Type*} [Fintype ι] (f : ι → Curv4 n) (i j k l : Fin n) :
    (∑ r, f r) i j k l = ∑ r, f r i j k l := by
  simp only [Finset.sum_apply]

/-- `rmSym` is additive in its second argument, for finite sums. -/
theorem rmSym_sum_right {n : ℕ} {ι : Type*} (t : Finset ι) (X : Curv4 n) (Y : ι → Curv4 n) :
    rmSym X (∑ i ∈ t, Y i) = ∑ i ∈ t, rmSym X (Y i) := by
  have h := map_sum (rmSymCLM n X) Y t
  simpa only [rmSymCLM_apply] using h

/-- The derivative of the tower array, in function form. -/
theorem TowerArr_deriv_fun (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M)
    (y : M) (e : Fin (Module.finrank ℝ E) → TField (I := I) (M := M))
    (he : ∀ i, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (e i))
    (hgeo : ∀ i, Submission.Diff.lcOf g (e i) y = 0)
    (a : ℕ) (D : Fin a → TField (I := I) (M := M))
    (hD : ∀ r, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (D r))
    (X : TField (I := I) (M := M)) (hX : Work.Diff.GE.SmoothFieldT (I := I) (M := M) X) :
    (fun p q r s => mvfderiv I (fun z => Work.Diff.EXT.TowerArr g a D e z p q r s) y (X y))
      = Work.Diff.EXT.TowerArr g (a + 1) (Fin.cons X D) e y
        + ∑ r : Fin a, Work.Diff.EXT.TowerArr g a
            (Function.update D r (Work.Diff.EXT.dirF g (D r) X)) e y := by
  funext p q r s
  rw [TowerArr_mvfderiv (I := I) (M := M) hLC g y e he hgeo a D hD X hX p q r s]
  simp only [Pi.add_apply]
  rw [sum_app4]

/-! ## The unpacking of `MonoD` -/

/-- The four-fold unfolding of `MonoD`. -/
theorem MonoD_sum {g : Submission.Diff.SMet I M} {y : M}
    {e : Fin (Module.finrank ℝ E) → TField (I := I) (M := M)}
    {N a b : ℕ} (d₁ : Fin a → Fin N) (d₂ : Fin b → Fin N) (s : Fin 4 → Fin N)
    (G : Fin N → TField (I := I) (M := M)) :
    Work.Diff.EXT.MonoD g N a b d₁ d₂ s e G y
      = ∑ i, ∑ j, ∑ k, ∑ l,
          rmSym (Work.Diff.EXT.TowerArr g a (fun r => G (d₁ r)) e y)
              (Work.Diff.EXT.TowerArr g b (fun r => G (d₂ r)) e y) i j k l
            * pairProd (I := I) (M := M) g e (fun t => G (s t)) i j k l y := by
  simp only [Work.Diff.EXT.MonoD, pairProd]

/-- **The derivative of the packed monomial of level `(a,b)`.** -/
theorem monoD_mvfderiv_step
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (y : M)
    (e : Fin (Module.finrank ℝ E) → TField (I := I) (M := M))
    (he : ∀ i, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (e i))
    (hgeo : ∀ i, Submission.Diff.lcOf g (e i) y = 0)
    (N a b : ℕ) (d₁ : Fin a → Fin N) (d₂ : Fin b → Fin N) (s : Fin 4 → Fin N)
    (hinj₁ : Function.Injective d₁) (hinj₂ : Function.Injective d₂) (hinjs : Function.Injective s)
    (hd₁₂ : ∀ r r', d₁ r ≠ d₂ r') (hd₁s : ∀ r t, d₁ r ≠ s t) (hd₂s : ∀ r t, d₂ r ≠ s t)
    (hcov : ∀ u : Fin N, (∃ r, d₁ r = u) ∨ (∃ r, d₂ r = u) ∨ (∃ t, s t = u))
    (F : Fin (N + 1) → TField (I := I) (M := M))
    (hF : ∀ u, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (F u)) :
    (mvfderiv I (fun z => Work.Diff.EXT.MonoD g N a b d₁ d₂ s e (fun i : Fin N => F i.succ) z) y)
        (F 0 y)
      = Work.Diff.EXT.MonoD g (N + 1) (a + 1) b
          (Fin.cons 0 (fun r => (d₁ r).succ)) (fun r => (d₂ r).succ) (fun t => (s t).succ) e F y
        + Work.Diff.EXT.MonoD g (N + 1) a (b + 1)
          (fun r => (d₁ r).succ) (Fin.cons 0 (fun r => (d₂ r).succ)) (fun t => (s t).succ) e F y
        + ∑ u : Fin N, Work.Diff.EXT.MonoD g N a b d₁ d₂ s e
            (Function.update (fun i : Fin N => F i.succ) u
              (Work.Diff.EXT.dirF g ((fun i : Fin N => F i.succ) u) (F 0))) y := by
  classical
  set tup : Fin N → TField (I := I) (M := M) := fun i => F i.succ with htup
  set X : TField (I := I) (M := M) := F 0 with hX
  have htupsm : ∀ u, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (tup u) := fun u => hF u.succ
  have hXsm : Work.Diff.GE.SmoothFieldT (I := I) (M := M) X := hF 0
  have hT₁md : MDifferentiableAt I (modelWithCornersSelf ℝ (Curv4 (Module.finrank ℝ E)))
      (fun z => Work.Diff.EXT.TowerArr g a (fun r => tup (d₁ r)) e z) y :=
    mdifferentiableAt_curv4_of_components (fun i j k l =>
      TowerArr_mdiffAt (I := I) (M := M) hLC g a (fun r => tup (d₁ r))
        (fun r => htupsm (d₁ r)) e he y i j k l)
  have hT₂md : MDifferentiableAt I (modelWithCornersSelf ℝ (Curv4 (Module.finrank ℝ E)))
      (fun z => Work.Diff.EXT.TowerArr g b (fun r => tup (d₂ r)) e z) y :=
    mdifferentiableAt_curv4_of_components (fun i j k l =>
      TowerArr_mdiffAt (I := I) (M := M) hLC g b (fun r => tup (d₂ r))
        (fun r => htupsm (d₂ r)) e he y i j k l)
  have hCmd : MDifferentiableAt I (modelWithCornersSelf ℝ (Curv4 (Module.finrank ℝ E)))
      (fun z => rmSym (Work.Diff.EXT.TowerArr g a (fun r => tup (d₁ r)) e z)
        (Work.Diff.EXT.TowerArr g b (fun r => tup (d₂ r)) e z)) y :=
    mdifferentiableAt_bilin_pair
      (fun p : Curv4 (Module.finrank ℝ E) × Curv4 (Module.finrank ℝ E) => rmSym p.1 p.2)
      (rmSym_isBoundedBilinearMap (Module.finrank ℝ E)) hT₁md hT₂md
  have hC : ∀ i j k l, MDifferentiableAt I (modelWithCornersSelf ℝ ℝ)
      (fun z => rmSym (Work.Diff.EXT.TowerArr g a (fun r => tup (d₁ r)) e z)
        (Work.Diff.EXT.TowerArr g b (fun r => tup (d₂ r)) e z) i j k l) y :=
    fun i j k l => mdiffAt_curv4_comp hCmd i j k l
  have hP : ∀ i j k l, MDifferentiableAt I (modelWithCornersSelf ℝ ℝ)
      (pairProd (I := I) (M := M) g e (fun t => tup (s t)) i j k l) y :=
    fun i j k l =>
      ((((metricPairing_mdiffAt g (he i) (htupsm (s 0)) y).mul
        (metricPairing_mdiffAt g (he j) (htupsm (s 1)) y)).mul
        (metricPairing_mdiffAt g (he k) (htupsm (s 2)) y)).mul
        (metricPairing_mdiffAt g (he l) (htupsm (s 3)) y))
  have hrmSym : ∀ i j k l,
      (mvfderiv I (fun z => rmSym (Work.Diff.EXT.TowerArr g a (fun r => tup (d₁ r)) e z)
          (Work.Diff.EXT.TowerArr g b (fun r => tup (d₂ r)) e z) i j k l) y) (X y)
        = rmSym (Work.Diff.EXT.TowerArr g (a + 1) (Fin.cons X (fun r => tup (d₁ r))) e y)
              (Work.Diff.EXT.TowerArr g b (fun r => tup (d₂ r)) e y) i j k l
          + rmSym (∑ r : Fin a, Work.Diff.EXT.TowerArr g a
                (Function.update (fun r' => tup (d₁ r')) r
                  (Work.Diff.EXT.dirF g (tup (d₁ r)) X)) e y)
              (Work.Diff.EXT.TowerArr g b (fun r => tup (d₂ r)) e y) i j k l
          + rmSym (Work.Diff.EXT.TowerArr g a (fun r => tup (d₁ r)) e y)
              (Work.Diff.EXT.TowerArr g (b + 1) (Fin.cons X (fun r => tup (d₂ r))) e y) i j k l
          + rmSym (Work.Diff.EXT.TowerArr g a (fun r => tup (d₁ r)) e y)
              (∑ r : Fin b, Work.Diff.EXT.TowerArr g b
                (Function.update (fun r' => tup (d₂ r')) r
                  (Work.Diff.EXT.dirF g (tup (d₂ r)) X)) e y) i j k l := by
    intro i j k l
    have e1 := TowerArr_deriv_fun (I := I) (M := M) hLC g y e he hgeo a (fun r => tup (d₁ r))
      (fun r => htupsm (d₁ r)) X hXsm
    have e2 := TowerArr_deriv_fun (I := I) (M := M) hLC g y e he hgeo b (fun r => tup (d₂ r))
      (fun r => htupsm (d₂ r)) X hXsm
    rw [mvfderiv_rmSymV (Module.finrank ℝ E)
      (fun z => Work.Diff.EXT.TowerArr g a (fun r => tup (d₁ r)) e z)
      (fun z => Work.Diff.EXT.TowerArr g b (fun r => tup (d₂ r)) e z) y (X y)
      (fun p q r s => TowerArr_mdiffAt (I := I) (M := M) hLC g a (fun r => tup (d₁ r))
        (fun r => htupsm (d₁ r)) e he y p q r s)
      (fun p q r s => TowerArr_mdiffAt (I := I) (M := M) hLC g b (fun r => tup (d₂ r))
        (fun r => htupsm (d₂ r)) e he y p q r s) i j k l,
      e1, e2, rmSym_add_left, rmSym_add_right]
    simp only [Pi.add_apply]
    ring
  have hpair : ∀ i j k l, (mvfderiv I (pairProd (I := I) (M := M) g e
        (fun t => tup (s t)) i j k l) y) (X y)
      = ∑ t : Fin 4, pairProd (I := I) (M := M) g e
          (Function.update (fun t' => tup (s t')) t (Work.Diff.EXT.dirF g (tup (s t)) X))
          i j k l y := by
    intro i j k l
    rw [pairProd_mvfderiv (I := I) (M := M) hLC g y e he hgeo (fun t => tup (s t))
      (fun t => htupsm (s t)) X hXsm i j k l]
    rw [Fin.sum_univ_four]
    simp only [pairProd]
    rw [Function.update_self, Function.update_self, Function.update_self, Function.update_self,
      Function.update_of_ne (by decide : (0 : Fin 4) ≠ 1) _ (fun t => tup (s t)),
      Function.update_of_ne (by decide : (0 : Fin 4) ≠ 2) _ (fun t => tup (s t)),
      Function.update_of_ne (by decide : (0 : Fin 4) ≠ 3) _ (fun t => tup (s t)),
      Function.update_of_ne (by decide : (1 : Fin 4) ≠ 0) _ (fun t => tup (s t)),
      Function.update_of_ne (by decide : (1 : Fin 4) ≠ 2) _ (fun t => tup (s t)),
      Function.update_of_ne (by decide : (1 : Fin 4) ≠ 3) _ (fun t => tup (s t)),
      Function.update_of_ne (by decide : (2 : Fin 4) ≠ 0) _ (fun t => tup (s t)),
      Function.update_of_ne (by decide : (2 : Fin 4) ≠ 1) _ (fun t => tup (s t)),
      Function.update_of_ne (by decide : (2 : Fin 4) ≠ 3) _ (fun t => tup (s t)),
      Function.update_of_ne (by decide : (3 : Fin 4) ≠ 0) _ (fun t => tup (s t)),
      Function.update_of_ne (by decide : (3 : Fin 4) ≠ 1) _ (fun t => tup (s t)),
      Function.update_of_ne (by decide : (3 : Fin 4) ≠ 2) _ (fun t => tup (s t))]
    ring
  have hBsum : (∑ i, ∑ j, ∑ k, ∑ l,
        pairProd (I := I) (M := M) g e (fun t => tup (s t)) i j k l y
          * rmSym (∑ r : Fin a, Work.Diff.EXT.TowerArr g a
                (Function.update (fun r' => tup (d₁ r')) r
                  (Work.Diff.EXT.dirF g (tup (d₁ r)) X)) e y)
              (Work.Diff.EXT.TowerArr g b (fun r => tup (d₂ r)) e y) i j k l)
      = ∑ r : Fin a, ∑ i, ∑ j, ∑ k, ∑ l,
          rmSym (Work.Diff.EXT.TowerArr g a
                (Function.update (fun r' => tup (d₁ r')) r
                  (Work.Diff.EXT.dirF g (tup (d₁ r)) X)) e y)
              (Work.Diff.EXT.TowerArr g b (fun r => tup (d₂ r)) e y) i j k l
            * pairProd (I := I) (M := M) g e (fun t => tup (s t)) i j k l y := by
    rw [show (∑ i, ∑ j, ∑ k, ∑ l,
          pairProd (I := I) (M := M) g e (fun t => tup (s t)) i j k l y
            * rmSym (∑ r : Fin a, Work.Diff.EXT.TowerArr g a
                  (Function.update (fun r' => tup (d₁ r')) r
                    (Work.Diff.EXT.dirF g (tup (d₁ r)) X)) e y)
                (Work.Diff.EXT.TowerArr g b (fun r => tup (d₂ r)) e y) i j k l)
        = ∑ i, ∑ j, ∑ k, ∑ l, ∑ r : Fin a,
            pairProd (I := I) (M := M) g e (fun t => tup (s t)) i j k l y
              * rmSym (Work.Diff.EXT.TowerArr g a
                    (Function.update (fun r' => tup (d₁ r')) r
                      (Work.Diff.EXT.dirF g (tup (d₁ r)) X)) e y)
                  (Work.Diff.EXT.TowerArr g b (fun r => tup (d₂ r)) e y) i j k l from by
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ =>
        Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))))
      rw [rmSym_sum_left (Finset.univ)
        (fun r => Work.Diff.EXT.TowerArr g a
          (Function.update (fun r' => tup (d₁ r')) r
            (Work.Diff.EXT.dirF g (tup (d₁ r)) X)) e y)
        (Work.Diff.EXT.TowerArr g b (fun r => tup (d₂ r)) e y)]
      rw [sum_app4]
      rw [Finset.mul_sum]]
    rw [sum4_comm_sum (fun i j k l (r : Fin a) =>
      pairProd (I := I) (M := M) g e (fun t => tup (s t)) i j k l y
        * rmSym (Work.Diff.EXT.TowerArr g a
              (Function.update (fun r' => tup (d₁ r')) r
                (Work.Diff.EXT.dirF g (tup (d₁ r)) X)) e y)
            (Work.Diff.EXT.TowerArr g b (fun r => tup (d₂ r)) e y) i j k l)]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ =>
      Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))))
    ring
  have hCsum : (∑ i, ∑ j, ∑ k, ∑ l,
        pairProd (I := I) (M := M) g e (fun t => tup (s t)) i j k l y
          * rmSym (Work.Diff.EXT.TowerArr g a (fun r => tup (d₁ r)) e y)
              (∑ r : Fin b, Work.Diff.EXT.TowerArr g b
                (Function.update (fun r' => tup (d₂ r')) r
                  (Work.Diff.EXT.dirF g (tup (d₂ r)) X)) e y) i j k l)
      = ∑ r : Fin b, ∑ i, ∑ j, ∑ k, ∑ l,
          rmSym (Work.Diff.EXT.TowerArr g a (fun r => tup (d₁ r)) e y)
              (Work.Diff.EXT.TowerArr g b
                (Function.update (fun r' => tup (d₂ r')) r
                  (Work.Diff.EXT.dirF g (tup (d₂ r)) X)) e y) i j k l
            * pairProd (I := I) (M := M) g e (fun t => tup (s t)) i j k l y := by
    rw [show (∑ i, ∑ j, ∑ k, ∑ l,
          pairProd (I := I) (M := M) g e (fun t => tup (s t)) i j k l y
            * rmSym (Work.Diff.EXT.TowerArr g a (fun r => tup (d₁ r)) e y)
                (∑ r : Fin b, Work.Diff.EXT.TowerArr g b
                  (Function.update (fun r' => tup (d₂ r')) r
                    (Work.Diff.EXT.dirF g (tup (d₂ r)) X)) e y) i j k l)
        = ∑ i, ∑ j, ∑ k, ∑ l, ∑ r : Fin b,
            pairProd (I := I) (M := M) g e (fun t => tup (s t)) i j k l y
              * rmSym (Work.Diff.EXT.TowerArr g a (fun r => tup (d₁ r)) e y)
                  (Work.Diff.EXT.TowerArr g b
                    (Function.update (fun r' => tup (d₂ r')) r
                      (Work.Diff.EXT.dirF g (tup (d₂ r)) X)) e y) i j k l from by
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ =>
        Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))))
      rw [rmSym_sum_right (Finset.univ)
        (Work.Diff.EXT.TowerArr g a (fun r => tup (d₁ r)) e y)
        (fun r => Work.Diff.EXT.TowerArr g b
          (Function.update (fun r' => tup (d₂ r')) r
            (Work.Diff.EXT.dirF g (tup (d₂ r)) X)) e y)]
      rw [sum_app4]
      rw [Finset.mul_sum]]
    rw [sum4_comm_sum (fun i j k l (r : Fin b) =>
      pairProd (I := I) (M := M) g e (fun t => tup (s t)) i j k l y
        * rmSym (Work.Diff.EXT.TowerArr g a (fun r => tup (d₁ r)) e y)
            (Work.Diff.EXT.TowerArr g b
              (Function.update (fun r' => tup (d₂ r')) r
                (Work.Diff.EXT.dirF g (tup (d₂ r)) X)) e y) i j k l)]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ =>
      Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))))
    ring
  have hchild1 : Work.Diff.EXT.MonoD g (N + 1) (a + 1) b
        (Fin.cons 0 (fun r => (d₁ r).succ)) (fun r => (d₂ r).succ) (fun t => (s t).succ) e F y
      = ∑ i, ∑ j, ∑ k, ∑ l,
          rmSym (Work.Diff.EXT.TowerArr g (a + 1) (Fin.cons X (fun r => tup (d₁ r))) e y)
              (Work.Diff.EXT.TowerArr g b (fun r => tup (d₂ r)) e y) i j k l
            * pairProd (I := I) (M := M) g e (fun t => tup (s t)) i j k l y := by
    rw [MonoD_sum (g := g) (y := y) (e := e) (N := N + 1) (a := a + 1) (b := b)
      (d₁ := (Fin.cons 0 (fun r' : Fin a => (d₁ r').succ) : Fin (a + 1) → Fin (N + 1)))
      (d₂ := fun r => (d₂ r).succ) (s := fun t => (s t).succ) (G := F)]
    have h1 : (fun r : Fin (a + 1) =>
          F ((Fin.cons 0 (fun r' : Fin a => (d₁ r').succ) : Fin (a + 1) → Fin (N + 1)) r))
        = (Fin.cons X (fun r' => tup (d₁ r')) : Fin (a + 1) → TField (I := I) (M := M)) := by
      funext r
      refine Fin.cases ?_ ?_ r
      · rfl
      · intro r'
        rfl
    have h2 : (fun r : Fin b => F ((d₂ r).succ)) = (fun r => tup (d₂ r)) := rfl
    have h3 : (fun t : Fin 4 => F ((s t).succ)) = (fun t => tup (s t)) := rfl
    rw [h1, h2, h3]
  have hchild2 : Work.Diff.EXT.MonoD g (N + 1) a (b + 1)
        (fun r => (d₁ r).succ) (Fin.cons 0 (fun r => (d₂ r).succ)) (fun t => (s t).succ) e F y
      = ∑ i, ∑ j, ∑ k, ∑ l,
          rmSym (Work.Diff.EXT.TowerArr g a (fun r => tup (d₁ r)) e y)
              (Work.Diff.EXT.TowerArr g (b + 1) (Fin.cons X (fun r => tup (d₂ r))) e y) i j k l
            * pairProd (I := I) (M := M) g e (fun t => tup (s t)) i j k l y := by
    rw [MonoD_sum (g := g) (y := y) (e := e) (N := N + 1) (a := a) (b := b + 1) (d₁ := fun r => (d₁ r).succ)
      (d₂ := (Fin.cons 0 (fun r' : Fin b => (d₂ r').succ) : Fin (b + 1) → Fin (N + 1)))
      (s := fun t => (s t).succ) (G := F)]
    have h1 : (fun r : Fin a => F ((d₁ r).succ)) = (fun r => tup (d₁ r)) := rfl
    have h2 : (fun r : Fin (b + 1) =>
          F ((Fin.cons 0 (fun r' : Fin b => (d₂ r').succ) : Fin (b + 1) → Fin (N + 1)) r))
        = (Fin.cons X (fun r' => tup (d₂ r')) : Fin (b + 1) → TField (I := I) (M := M)) := by
      funext r
      refine Fin.cases ?_ ?_ r
      · rfl
      · intro r'
        rfl
    have h3 : (fun t : Fin 4 => F ((s t).succ)) = (fun t => tup (s t)) := rfl
    rw [h1, h2, h3]
  have hΦ1 : ∀ r₀ : Fin a, Work.Diff.EXT.MonoD g N a b d₁ d₂ s e
        (Function.update tup (d₁ r₀) (Work.Diff.EXT.dirF g (tup (d₁ r₀)) X)) y
      = ∑ i, ∑ j, ∑ k, ∑ l,
          rmSym (Work.Diff.EXT.TowerArr g a
              (Function.update (fun r' => tup (d₁ r')) r₀
                (Work.Diff.EXT.dirF g (tup (d₁ r₀)) X)) e y)
              (Work.Diff.EXT.TowerArr g b (fun r => tup (d₂ r)) e y) i j k l
            * pairProd (I := I) (M := M) g e (fun t => tup (s t)) i j k l y := by
    intro r₀
    rw [MonoD_sum (g := g) (y := y) (e := e) (N := N) (a := a) (b := b) (d₁ := d₁)
      (d₂ := d₂) (s := s) (G := Function.update tup (d₁ r₀) (Work.Diff.EXT.dirF g (tup (d₁ r₀)) X))]
    rw [update_comp_same tup d₁ hinj₁ r₀ (Work.Diff.EXT.dirF g (tup (d₁ r₀)) X),
      update_comp_ne tup d₁ d₂ hd₁₂ r₀ (Work.Diff.EXT.dirF g (tup (d₁ r₀)) X),
      update_comp_ne tup d₁ s hd₁s r₀ (Work.Diff.EXT.dirF g (tup (d₁ r₀)) X)]
  have hΦ2 : ∀ r₀ : Fin b, Work.Diff.EXT.MonoD g N a b d₁ d₂ s e
        (Function.update tup (d₂ r₀) (Work.Diff.EXT.dirF g (tup (d₂ r₀)) X)) y
      = ∑ i, ∑ j, ∑ k, ∑ l,
          rmSym (Work.Diff.EXT.TowerArr g a (fun r => tup (d₁ r)) e y)
              (Work.Diff.EXT.TowerArr g b
                (Function.update (fun r' => tup (d₂ r')) r₀
                  (Work.Diff.EXT.dirF g (tup (d₂ r₀)) X)) e y) i j k l
            * pairProd (I := I) (M := M) g e (fun t => tup (s t)) i j k l y := by
    intro r₀
    rw [MonoD_sum (g := g) (y := y) (e := e) (N := N) (a := a) (b := b) (d₁ := d₁)
      (d₂ := d₂) (s := s) (G := Function.update tup (d₂ r₀) (Work.Diff.EXT.dirF g (tup (d₂ r₀)) X))]
    rw [update_comp_ne tup d₂ d₁ (fun r r' => (hd₁₂ r' r).symm) r₀
        (Work.Diff.EXT.dirF g (tup (d₂ r₀)) X),
      update_comp_same tup d₂ hinj₂ r₀ (Work.Diff.EXT.dirF g (tup (d₂ r₀)) X),
      update_comp_ne tup d₂ s hd₂s r₀ (Work.Diff.EXT.dirF g (tup (d₂ r₀)) X)]
  have hΦ3 : ∀ t₀ : Fin 4, Work.Diff.EXT.MonoD g N a b d₁ d₂ s e
        (Function.update tup (s t₀) (Work.Diff.EXT.dirF g (tup (s t₀)) X)) y
      = ∑ i, ∑ j, ∑ k, ∑ l,
          rmSym (Work.Diff.EXT.TowerArr g a (fun r => tup (d₁ r)) e y)
              (Work.Diff.EXT.TowerArr g b (fun r => tup (d₂ r)) e y) i j k l
            * pairProd (I := I) (M := M) g e
                (Function.update (fun t' => tup (s t')) t₀
                  (Work.Diff.EXT.dirF g (tup (s t₀)) X)) i j k l y := by
    intro t₀
    rw [MonoD_sum (g := g) (y := y) (e := e) (N := N) (a := a) (b := b) (d₁ := d₁)
      (d₂ := d₂) (s := s) (G := Function.update tup (s t₀) (Work.Diff.EXT.dirF g (tup (s t₀)) X))]
    rw [update_comp_ne tup s d₁ (fun t r => (hd₁s r t).symm) t₀
        (Work.Diff.EXT.dirF g (tup (s t₀)) X),
      update_comp_ne tup s d₂ (fun t r => (hd₂s r t).symm) t₀
        (Work.Diff.EXT.dirF g (tup (s t₀)) X),
      update_comp_same tup s hinjs t₀ (Work.Diff.EXT.dirF g (tup (s t₀)) X)]
  have hCS : (∑ u : Fin N, Work.Diff.EXT.MonoD g N a b d₁ d₂ s e
        (Function.update tup u (Work.Diff.EXT.dirF g (tup u) X)) y)
      = (∑ r : Fin a, ∑ i, ∑ j, ∑ k, ∑ l,
            rmSym (Work.Diff.EXT.TowerArr g a
                (Function.update (fun r' => tup (d₁ r')) r
                  (Work.Diff.EXT.dirF g (tup (d₁ r)) X)) e y)
                (Work.Diff.EXT.TowerArr g b (fun r => tup (d₂ r)) e y) i j k l
              * pairProd (I := I) (M := M) g e (fun t => tup (s t)) i j k l y)
        + (∑ r : Fin b, ∑ i, ∑ j, ∑ k, ∑ l,
            rmSym (Work.Diff.EXT.TowerArr g a (fun r => tup (d₁ r)) e y)
                (Work.Diff.EXT.TowerArr g b
                  (Function.update (fun r' => tup (d₂ r')) r
                    (Work.Diff.EXT.dirF g (tup (d₂ r)) X)) e y) i j k l
              * pairProd (I := I) (M := M) g e (fun t => tup (s t)) i j k l y)
        + (∑ t : Fin 4, ∑ i, ∑ j, ∑ k, ∑ l,
            rmSym (Work.Diff.EXT.TowerArr g a (fun r => tup (d₁ r)) e y)
                (Work.Diff.EXT.TowerArr g b (fun r => tup (d₂ r)) e y) i j k l
              * pairProd (I := I) (M := M) g e
                  (Function.update (fun t' => tup (s t')) t
                    (Work.Diff.EXT.dirF g (tup (s t)) X)) i j k l y) := by
    rw [sum_over_partition d₁ d₂ s hinj₁ hinj₂ hinjs hd₁₂ hd₁s hd₂s hcov
      (fun u => Work.Diff.EXT.MonoD g N a b d₁ d₂ s e
        (Function.update tup u (Work.Diff.EXT.dirF g (tup u) X)) y)]
    simp only [hΦ1, hΦ2, hΦ3]
  have hL : (mvfderiv I (fun z => Work.Diff.EXT.MonoD g N a b d₁ d₂ s e tup z) y) (X y)
      = (∑ i, ∑ j, ∑ k, ∑ l,
            rmSym (Work.Diff.EXT.TowerArr g (a + 1) (Fin.cons X (fun r => tup (d₁ r))) e y)
                (Work.Diff.EXT.TowerArr g b (fun r => tup (d₂ r)) e y) i j k l
              * pairProd (I := I) (M := M) g e (fun t => tup (s t)) i j k l y)
        + (∑ i, ∑ j, ∑ k, ∑ l,
            rmSym (Work.Diff.EXT.TowerArr g a (fun r => tup (d₁ r)) e y)
                (Work.Diff.EXT.TowerArr g (b + 1) (Fin.cons X (fun r => tup (d₂ r))) e y) i j k l
              * pairProd (I := I) (M := M) g e (fun t => tup (s t)) i j k l y)
        + (∑ r : Fin a, ∑ i, ∑ j, ∑ k, ∑ l,
            rmSym (Work.Diff.EXT.TowerArr g a
                (Function.update (fun r' => tup (d₁ r')) r
                  (Work.Diff.EXT.dirF g (tup (d₁ r)) X)) e y)
                (Work.Diff.EXT.TowerArr g b (fun r => tup (d₂ r)) e y) i j k l
              * pairProd (I := I) (M := M) g e (fun t => tup (s t)) i j k l y)
        + (∑ r : Fin b, ∑ i, ∑ j, ∑ k, ∑ l,
            rmSym (Work.Diff.EXT.TowerArr g a (fun r => tup (d₁ r)) e y)
                (Work.Diff.EXT.TowerArr g b
                  (Function.update (fun r' => tup (d₂ r')) r
                    (Work.Diff.EXT.dirF g (tup (d₂ r)) X)) e y) i j k l
              * pairProd (I := I) (M := M) g e (fun t => tup (s t)) i j k l y)
        + (∑ t : Fin 4, ∑ i, ∑ j, ∑ k, ∑ l,
            rmSym (Work.Diff.EXT.TowerArr g a (fun r => tup (d₁ r)) e y)
                (Work.Diff.EXT.TowerArr g b (fun r => tup (d₂ r)) e y) i j k l
              * pairProd (I := I) (M := M) g e
                  (Function.update (fun t' => tup (s t')) t
                    (Work.Diff.EXT.dirF g (tup (s t)) X)) i j k l y) := by
    have hstep : (mvfderiv I (fun z => Work.Diff.EXT.MonoD g N a b d₁ d₂ s e tup z) y) (X y)
        = ∑ i, ∑ j, ∑ k, ∑ l,
            ( rmSym (Work.Diff.EXT.TowerArr g a (fun r => tup (d₁ r)) e y)
                  (Work.Diff.EXT.TowerArr g b (fun r => tup (d₂ r)) e y) i j k l
                * (mvfderiv I (pairProd (I := I) (M := M) g e
                    (fun t => tup (s t)) i j k l) y) (X y)
              + pairProd (I := I) (M := M) g e (fun t => tup (s t)) i j k l y
                * (mvfderiv I (fun z => rmSym
                    (Work.Diff.EXT.TowerArr g a (fun r => tup (d₁ r)) e z)
                    (Work.Diff.EXT.TowerArr g b (fun r => tup (d₂ r)) e z) i j k l) y) (X y) ) := by
      rw [show (fun z => Work.Diff.EXT.MonoD g N a b d₁ d₂ s e tup z)
          = fun z => ∑ i, ∑ j, ∑ k, ∑ l,
              rmSym (Work.Diff.EXT.TowerArr g a (fun r => tup (d₁ r)) e z)
                  (Work.Diff.EXT.TowerArr g b (fun r => tup (d₂ r)) e z) i j k l
                * pairProd (I := I) (M := M) g e (fun t => tup (s t)) i j k l z from by
            funext z; exact MonoD_sum (g := g) (y := z) (e := e) d₁ d₂ s tup]
      exact mvfderiv_sum4_prod_pt (X y) _ _ hC hP
    rw [hstep]
    simp only [hrmSym, hpair]
    simp only [Finset.sum_add_distrib, mul_add, Finset.mul_sum]
    rw [show (∑ i, ∑ j, ∑ k, ∑ l,
          pairProd (I := I) (M := M) g e (fun t => tup (s t)) i j k l y
            * rmSym (Work.Diff.EXT.TowerArr g (a + 1)
                  (Fin.cons X (fun r => tup (d₁ r))) e y)
                (Work.Diff.EXT.TowerArr g b (fun r => tup (d₂ r)) e y) i j k l)
        = ∑ i, ∑ j, ∑ k, ∑ l,
            rmSym (Work.Diff.EXT.TowerArr g (a + 1)
                  (Fin.cons X (fun r => tup (d₁ r))) e y)
                (Work.Diff.EXT.TowerArr g b (fun r => tup (d₂ r)) e y) i j k l
              * pairProd (I := I) (M := M) g e (fun t => tup (s t)) i j k l y from by
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ =>
        Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))))
      ring]
    rw [show (∑ i, ∑ j, ∑ k, ∑ l,
          pairProd (I := I) (M := M) g e (fun t => tup (s t)) i j k l y
            * rmSym (Work.Diff.EXT.TowerArr g a (fun r => tup (d₁ r)) e y)
                (Work.Diff.EXT.TowerArr g (b + 1) (Fin.cons X (fun r => tup (d₂ r))) e y)
                i j k l)
        = ∑ i, ∑ j, ∑ k, ∑ l,
            rmSym (Work.Diff.EXT.TowerArr g a (fun r => tup (d₁ r)) e y)
                (Work.Diff.EXT.TowerArr g (b + 1) (Fin.cons X (fun r => tup (d₂ r))) e y)
                i j k l
              * pairProd (I := I) (M := M) g e (fun t => tup (s t)) i j k l y from by
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ =>
        Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))))
      ring]
    rw [hBsum, hCsum]
    rw [sum4_comm_sum (fun i j k l (t : Fin 4) =>
      rmSym (Work.Diff.EXT.TowerArr g a (fun r => tup (d₁ r)) e y)
          (Work.Diff.EXT.TowerArr g b (fun r => tup (d₂ r)) e y) i j k l
        * pairProd (I := I) (M := M) g e
            (Function.update (fun t' => tup (s t')) t
              (Work.Diff.EXT.dirF g (tup (s t)) X)) i j k l y)]
    ring
  have hR : Work.Diff.EXT.MonoD g (N + 1) (a + 1) b
        (Fin.cons 0 (fun r => (d₁ r).succ)) (fun r => (d₂ r).succ) (fun t => (s t).succ) e F y
      + Work.Diff.EXT.MonoD g (N + 1) a (b + 1)
        (fun r => (d₁ r).succ) (Fin.cons 0 (fun r => (d₂ r).succ)) (fun t => (s t).succ) e F y
      + (∑ u : Fin N, Work.Diff.EXT.MonoD g N a b d₁ d₂ s e
          (Function.update (fun i : Fin N => F i.succ) u
            (Work.Diff.EXT.dirF g ((fun i : Fin N => F i.succ) u) (F 0))) y)
      = (∑ i, ∑ j, ∑ k, ∑ l,
            rmSym (Work.Diff.EXT.TowerArr g (a + 1) (Fin.cons X (fun r => tup (d₁ r))) e y)
                (Work.Diff.EXT.TowerArr g b (fun r => tup (d₂ r)) e y) i j k l
              * pairProd (I := I) (M := M) g e (fun t => tup (s t)) i j k l y)
        + (∑ i, ∑ j, ∑ k, ∑ l,
            rmSym (Work.Diff.EXT.TowerArr g a (fun r => tup (d₁ r)) e y)
                (Work.Diff.EXT.TowerArr g (b + 1) (Fin.cons X (fun r => tup (d₂ r))) e y) i j k l
              * pairProd (I := I) (M := M) g e (fun t => tup (s t)) i j k l y)
        + (∑ r : Fin a, ∑ i, ∑ j, ∑ k, ∑ l,
            rmSym (Work.Diff.EXT.TowerArr g a
                (Function.update (fun r' => tup (d₁ r')) r
                  (Work.Diff.EXT.dirF g (tup (d₁ r)) X)) e y)
                (Work.Diff.EXT.TowerArr g b (fun r => tup (d₂ r)) e y) i j k l
              * pairProd (I := I) (M := M) g e (fun t => tup (s t)) i j k l y)
        + (∑ r : Fin b, ∑ i, ∑ j, ∑ k, ∑ l,
            rmSym (Work.Diff.EXT.TowerArr g a (fun r => tup (d₁ r)) e y)
                (Work.Diff.EXT.TowerArr g b
                  (Function.update (fun r' => tup (d₂ r')) r
                    (Work.Diff.EXT.dirF g (tup (d₂ r)) X)) e y) i j k l
              * pairProd (I := I) (M := M) g e (fun t => tup (s t)) i j k l y)
        + (∑ t : Fin 4, ∑ i, ∑ j, ∑ k, ∑ l,
            rmSym (Work.Diff.EXT.TowerArr g a (fun r => tup (d₁ r)) e y)
                (Work.Diff.EXT.TowerArr g b (fun r => tup (d₂ r)) e y) i j k l
              * pairProd (I := I) (M := M) g e
                  (Function.update (fun t' => tup (s t')) t
                    (Work.Diff.EXT.dirF g (tup (s t)) X)) i j k l y) := by
    rw [hchild1, hchild2, hCS]
    ring
  calc (mvfderiv I (fun z => Work.Diff.EXT.MonoD g N a b d₁ d₂ s e
          (fun i : Fin N => F i.succ) z) y) (F 0 y)
      = (mvfderiv I (fun z => Work.Diff.EXT.MonoD g N a b d₁ d₂ s e tup z) y) (X y) := rfl
    _ = _ := hL
    _ = _ := hR.symm

/-! ## The target -/

/-- **The Leibniz recursion of the monomial of the level-`0` reaction ladder.**

With `d₁, d₂ : Fin a/b → Fin N` (resp. `s : Fin 4 → Fin N`) the tuple positions of the `a` derivative
slots of the first factor (resp. the `b` of the second, and the four `reactionMap` slots), the packed
monomial `MonoD g N a b d₁ d₂ s e` is the contraction of `rmSym (∇^a Rm) (∇^b Rm)` in the frame `e`
with the tuple.  One `extStep` (the Ext-pattern covariant derivative) inserts the new derivative
direction `F 0` into the *first* factor (giving `MonoD` at level `(a+1,b)` with `d₁' = Fin.cons 0
(d₁ ∘ succ)`) or into the *second* (level `(a,b+1)`); the two Leibniz correction sums are matched by
the `−∑_{u : Fin N}` of `extStep` (using `hcov`), and the frame-slot corrections of the towers vanish
because the frame is parallel at `y` (`hgeo`: `lcOf g (e i) y = 0`, so `∇_X e i (y) = 0`, and a
`ckt`-slot with zero value is zero by `Work.Diff.EXT.ckt_zero_slot_T2`).

Ingredients available in the workspace: `Work.Diff.EXT.mvfderiv_ckt_T2`, `Work.Diff.EXT.ckt_succ`,
`Work.Diff.EXT.ckt_zero_slot_T2`, `Work.Diff.EXT.TowerArr` (`Work.Diff.EXT.reactBase`), together with
the (in-flight, sibling) pointwise Leibniz rules `Work.Diff.EXT.evX.towerArr_mvfderivV`,
`Work.Diff.EXT.evX.pairing_mvfderivV`, `Work.Diff.EXT.evX.mvfderiv_rmSymV`; they are tiny and can also
be re-derived inline.  `SmoothF`/`SmoothFieldT` smoothness of the `ckt`-expressions is available
(`Work.Diff.GE.tensProp_all`, `Work.Diff.EXT.mvfderiv_ckt_gen'`). -/
theorem MonoD_extStepV
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
  have h := monoD_mvfderiv_step (I := I) (M := M) hLC g y e he hgeo N a b d₁ d₂ s
    hinj₁ hinj₂ hinjs hd₁₂ hd₁s hd₂s hcov F hF
  rw [show Work.Diff.EXT.extStep (I := I) (M := M) g
        (Work.Diff.EXT.MonoD (I := I) (M := M) g N a b d₁ d₂ s e) F y
      = (mvfderiv I (fun z => Work.Diff.EXT.MonoD (I := I) (M := M) g N a b d₁ d₂ s e
            (fun i : Fin N => F i.succ) z) y) (F 0 y)
        - ∑ u : Fin N, Work.Diff.EXT.MonoD (I := I) (M := M) g N a b d₁ d₂ s e
            (Function.update (fun i : Fin N => F i.succ) u
              (Work.Diff.EXT.dirF g ((fun i : Fin N => F i.succ) u) (F 0))) y from rfl]
  rw [h]
  ring

end Work.Diff.EXT.evX
