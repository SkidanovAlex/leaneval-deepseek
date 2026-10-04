import Mathlib
import Submission.Work.Diff.EXT.ConnCov.ChartTowerDefs
import Submission.Work.Diff.EXT.chartData_step_aux
import Submission.Work.Diff.EXT.ConnCov.norm_iteratedFDeriv_fderiv_apply_le
import Submission.Work.Diff.EXT.christoffel_bounds_of_core

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Uniform jet bounds for the chart tower `tower3Arr`

`Work.Diff.EXT.ConnCov.tower3Arr G x₀ t A m v i j l` is the chart recursion of a `(0,3)`-array
`A` with respect to the **fixed** background connection `∇^{G 0}`: level `0` is the base `A`, and
each level is the chart derivative of the previous one in the direction `v 0`, corrected by the
four Christoffel contractions of the coordinate frame with respect to `cGam (G 0)`.

The recursion is *the same* as the one defining `Work.Diff.EXT.aCovArr` (the `∇^{G 0}`-tower of the
connection difference), the only difference being that the base array is arbitrary and the level
functions depend on the parameter `t` only through `A t`.  This file proves the uniform jet bound

`‖D^j (level m)‖ ≤ C` for `j + m ≤ Mm`, on a set `K'` of chart coordinates, uniformly in
`t ∈ [σ, T)`, from

* the uniform jet bounds of the base array `A t` up to order `Mm` (`hA`),
* the pointwise smoothness of `A t` on `K'` (`hAsm`),
* the uniform jet bounds of the background Christoffel symbols `cGam (G 0)` up to order `Mm`
  (`hΓ`).

## Route

Exactly as in `Work.Diff.EXT.ConnCov.aCovArr_bound_of_jets`, but with the *full* diagonal range
`j + m ≤ Mm`:

* the recursion is solved for the derivative: `∂_a (level m) = level (m+1) + (correction)`, where
  the correction is a sum of products of `cGam (G 0)` with level-`m` components
  (`tower3Arr_succ_expand`, `fderiv_tower3Arr_eq`);
* an *ascending* induction on the level `m` therefore bounds the jets of level `m + 1` of order
  `≤ k` by the jets of level `m` of order `≤ k + 1` (`norm_iteratedFDeriv_fderiv_apply_le`) plus
  the Leibniz estimate for the correction (`norm_iteratedFDeriv_mul_le_at_le`), with the counts of
  the four sums;
* the smoothness of every level (needed for the two estimates above) is a separate induction on
  the level (`tower3Arr_contDiffAt`);
* the constants obtained for the individual levels are unified into a single constant by
  `Work.Diff.EXT.exists_uniform_bound_of_le`, which is exactly the passage from
  "jets of order `≤ Mm - m` at level `m`" to the diagonal statement `j + m ≤ Mm`.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT.ConnCov

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  [I.Boundaryless] [T2Space M]

/-- **The Christoffel correction function of the recursion `tower3Arr`.**  The four sums are the
contractions of the Christoffel symbols `cGam (G 0)` with the level-`m` array in the derivative
slots (`w r`) and in the three tensor slots. -/
private noncomputable def towerCorrFun (G : ℝ → Submission.Diff.SMet I M) (x₀ : M) (t : ℝ)
    (A : E → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ)
    (m : ℕ) (w : Fin m → Fin (Module.finrank ℝ E)) (a i j l : Fin (Module.finrank ℝ E))
    (y : E) : ℝ :=
  (∑ r : Fin m, ∑ p : Fin (Module.finrank ℝ E),
      Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y) p (w r) a
        * tower3Arr (I := I) (M := M) G x₀ t A m (Function.update w r p) i j l y)
    + (∑ p : Fin (Module.finrank ℝ E),
        Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y) p i a
          * tower3Arr (I := I) (M := M) G x₀ t A m w p j l y
      + (∑ p : Fin (Module.finrank ℝ E),
          Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y) p j a
            * tower3Arr (I := I) (M := M) G x₀ t A m w i p l y
        + ∑ p : Fin (Module.finrank ℝ E),
            Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y) p l a
              * tower3Arr (I := I) (M := M) G x₀ t A m w i j p y))

/-- **The recursion solved for the derivative.**  The level-`(m+1)` array is the chart derivative
of the level-`m` array in the direction `v 0` minus the four Christoffel corrections; this is the
defining recursion rearranged. -/
private lemma tower3Arr_succ_expand (G : ℝ → Submission.Diff.SMet I M) (x₀ : M) (t : ℝ)
    (A : E → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ)
    (m : ℕ) (v : Fin (m + 1) → Fin (Module.finrank ℝ E))
    (i j l : Fin (Module.finrank ℝ E)) (y : E) :
    tower3Arr G x₀ t A (m + 1) v i j l y
      = fderiv ℝ (tower3Arr G x₀ t A m (fun s : Fin m => v s.succ) i j l) y
          (Work.Diff.GE.cBasis (E := E) (v 0))
        - ∑ r : Fin m, ∑ p : Fin (Module.finrank ℝ E),
              Work.Diff.GE.cGam (G 0) x₀ (pt (I := I) x₀ y) p (v r.succ) (v 0)
                * tower3Arr G x₀ t A m (Function.update (fun s : Fin m => v s.succ) r p) i j l y
        - ∑ p : Fin (Module.finrank ℝ E),
              Work.Diff.GE.cGam (G 0) x₀ (pt (I := I) x₀ y) p i (v 0)
                * tower3Arr G x₀ t A m (fun s : Fin m => v s.succ) p j l y
        - ∑ p : Fin (Module.finrank ℝ E),
              Work.Diff.GE.cGam (G 0) x₀ (pt (I := I) x₀ y) p j (v 0)
                * tower3Arr G x₀ t A m (fun s : Fin m => v s.succ) i p l y
        - ∑ p : Fin (Module.finrank ℝ E),
              Work.Diff.GE.cGam (G 0) x₀ (pt (I := I) x₀ y) p l (v 0)
                * tower3Arr G x₀ t A m (fun s : Fin m => v s.succ) i j p y := rfl

/-- The derivative of the level-`m` array in a direction of the model basis is the level-`(m+1)`
array plus the Christoffel correction. -/
private lemma fderiv_tower3Arr_eq (G : ℝ → Submission.Diff.SMet I M) (x₀ : M) (t : ℝ)
    (A : E → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ)
    (m : ℕ) (w : Fin m → Fin (Module.finrank ℝ E)) (a i j l : Fin (Module.finrank ℝ E)) (y : E) :
    fderiv ℝ (fun y' : E => tower3Arr G x₀ t A m w i j l y') y (Work.Diff.GE.cBasis (E := E) a)
      = tower3Arr G x₀ t A (m + 1) (Fin.cons a w) i j l y
        + towerCorrFun G x₀ t A m w a i j l y := by
  have h := tower3Arr_succ_expand (I := I) (M := M) G x₀ t A m (Fin.cons a w) i j l y
  simp only [Fin.cons_zero, Fin.cons_succ] at h
  rw [h]
  simp only [towerCorrFun]
  ring

/-- **Smoothness of the Christoffel correction.** -/
private lemma towerCorrFun_contDiffAt (G : ℝ → Submission.Diff.SMet I M) (x₀ : M) (K' : Set E)
    (hK't : K' ⊆ (extChartAt I x₀).target)
    {A : E → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ}
    {m : ℕ} {w : Fin m → Fin (Module.finrank ℝ E)} {a i j l : Fin (Module.finrank ℝ E)}
    (hA : ∀ (w' : Fin m → Fin (Module.finrank ℝ E))
      (i' j' l' : Fin (Module.finrank ℝ E)) (t : ℝ) {y : E}, y ∈ K' →
      ContDiffAt ℝ (⊤ : ℕ∞)
        (fun y' : E => tower3Arr (I := I) (M := M) G x₀ t A m w' i' j' l' y') y)
    (t : ℝ) {y : E} (hy : y ∈ K') :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun y' : E => towerCorrFun (I := I) (M := M) G x₀ t A m w a i j l y') y := by
  have hGam : ∀ (p q r : Fin (Module.finrank ℝ E)), ContDiffAt ℝ (⊤ : ℕ∞)
      (fun y' : E => Work.Diff.GE.cGam (G 0) x₀ (pt (I := I) x₀ y') p q r) y :=
    fun p q r => Work.Diff.EXT.CBound.cGam_contDiffAt_of_target (I := I) (M := M) (G 0) x₀
      (hK't hy) p q r
  have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun y' : E => ∑ r : Fin m,
      ∑ p : Fin (Module.finrank ℝ E),
        Work.Diff.GE.cGam (G 0) x₀ (pt (I := I) x₀ y') p (w r) a
          * tower3Arr (I := I) (M := M) G x₀ t A m (Function.update w r p) i j l y') y :=
    ContDiffAt.sum (s := Finset.univ) (fun r _ => ContDiffAt.sum (s := Finset.univ) (fun p _ =>
      (hGam p (w r) a).mul (hA (Function.update w r p) i j l t hy)))
  have h2 : ContDiffAt ℝ (⊤ : ℕ∞) (fun y' : E => ∑ p : Fin (Module.finrank ℝ E),
        Work.Diff.GE.cGam (G 0) x₀ (pt (I := I) x₀ y') p i a
          * tower3Arr (I := I) (M := M) G x₀ t A m w p j l y') y :=
    ContDiffAt.sum (s := Finset.univ) (fun p _ => (hGam p i a).mul (hA w p j l t hy))
  have h3 : ContDiffAt ℝ (⊤ : ℕ∞) (fun y' : E => ∑ p : Fin (Module.finrank ℝ E),
        Work.Diff.GE.cGam (G 0) x₀ (pt (I := I) x₀ y') p j a
          * tower3Arr (I := I) (M := M) G x₀ t A m w i p l y') y :=
    ContDiffAt.sum (s := Finset.univ) (fun p _ => (hGam p j a).mul (hA w i p l t hy))
  have h4 : ContDiffAt ℝ (⊤ : ℕ∞) (fun y' : E => ∑ p : Fin (Module.finrank ℝ E),
        Work.Diff.GE.cGam (G 0) x₀ (pt (I := I) x₀ y') p l a
          * tower3Arr (I := I) (M := M) G x₀ t A m w i j p y') y :=
    ContDiffAt.sum (s := Finset.univ) (fun p _ => (hGam p l a).mul (hA w i j p t hy))
  exact (h1.add (h2.add (h3.add h4))).congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun y' => rfl))

/-- **Jet bound for the Christoffel correction.**  If every product of a background Christoffel
entry with a component of the level-`m` array has `jj`-th jet bounded by `P`, then the `jj`-th jet
of the correction is bounded by the number of summands times `P`. -/
private lemma towerCorrFun_jet_le (G : ℝ → Submission.Diff.SMet I M) (x₀ : M) (K' : Set E)
    (hK't : K' ⊆ (extChartAt I x₀).target)
    (A : E → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ)
    (m : ℕ) (w : Fin m → Fin (Module.finrank ℝ E)) (a i j l : Fin (Module.finrank ℝ E))
    {jj : ℕ} {t : ℝ} {y : E} (hy : y ∈ K') {P : ℝ}
    (hsm : ∀ (w' : Fin m → Fin (Module.finrank ℝ E)) (i' j' l' : Fin (Module.finrank ℝ E)),
      ContDiffAt ℝ (⊤ : ℕ∞)
        (fun y' : E => tower3Arr (I := I) (M := M) G x₀ t A m w' i' j' l' y') y)
    (hprod : ∀ (p q r : Fin (Module.finrank ℝ E)) (w' : Fin m → Fin (Module.finrank ℝ E))
        (i' j' l' : Fin (Module.finrank ℝ E)),
      ‖iteratedFDeriv ℝ jj (fun y' : E => Work.Diff.GE.cGam (G 0) x₀
          (Work.Diff.EXT.pt (I := I) x₀ y') p q r
        * tower3Arr (I := I) (M := M) G x₀ t A m w' i' j' l' y') y‖ ≤ P) :
    ‖iteratedFDeriv ℝ jj
        (fun y' : E => towerCorrFun (I := I) (M := M) G x₀ t A m w a i j l y') y‖
      ≤ ((m : ℝ) * (Module.finrank ℝ E : ℝ) + 3 * (Module.finrank ℝ E : ℝ)) * P := by
  classical
  have hcG : ∀ (p q r : Fin (Module.finrank ℝ E)), ContDiffAt ℝ (⊤ : ℕ∞)
      (fun y' : E => Work.Diff.GE.cGam (G 0) x₀ (pt (I := I) x₀ y') p q r) y :=
    fun p q r => Work.Diff.EXT.CBound.cGam_contDiffAt_of_target (I := I) (M := M) (G 0) x₀
      (hK't hy) p q r
  -- a bound for a single sum over the model basis
  have hsingle : ∀ (ψ : Fin (Module.finrank ℝ E) → E → ℝ),
      (∀ p, ContDiffAt ℝ (⊤ : ℕ∞) (ψ p) y) →
      (∀ p, ‖iteratedFDeriv ℝ jj (ψ p) y‖ ≤ P) →
      ‖iteratedFDeriv ℝ jj (fun y' : E => ∑ p : Fin (Module.finrank ℝ E), ψ p y') y‖
        ≤ (Module.finrank ℝ E : ℝ) * P := by
    intro ψ hψ hψb
    refine le_trans (Work.Diff.EXT.norm_iteratedFDeriv_sum_le_at
      (s := (Finset.univ : Finset (Fin (Module.finrank ℝ E)))) (φ := ψ) (x := y) (n := jj)
      (C := P) (fun p _ => hψ p) (fun p _ => hψb p)) ?_
    simp
  set F1 : E → ℝ := fun y' => ∑ r : Fin m, ∑ p : Fin (Module.finrank ℝ E),
      Work.Diff.GE.cGam (G 0) x₀ (pt (I := I) x₀ y') p (w r) a
        * tower3Arr (I := I) (M := M) G x₀ t A m (Function.update w r p) i j l y' with hF1def
  set F2 : E → ℝ := fun y' => ∑ p : Fin (Module.finrank ℝ E),
      Work.Diff.GE.cGam (G 0) x₀ (pt (I := I) x₀ y') p i a
        * tower3Arr (I := I) (M := M) G x₀ t A m w p j l y' with hF2def
  set F3 : E → ℝ := fun y' => ∑ p : Fin (Module.finrank ℝ E),
      Work.Diff.GE.cGam (G 0) x₀ (pt (I := I) x₀ y') p j a
        * tower3Arr (I := I) (M := M) G x₀ t A m w i p l y' with hF3def
  set F4 : E → ℝ := fun y' => ∑ p : Fin (Module.finrank ℝ E),
      Work.Diff.GE.cGam (G 0) x₀ (pt (I := I) x₀ y') p l a
        * tower3Arr (I := I) (M := M) G x₀ t A m w i j p y' with hF4def
  have hF1b : ‖iteratedFDeriv ℝ jj F1 y‖
      ≤ (m : ℝ) * ((Module.finrank ℝ E : ℝ) * P) := by
    rw [hF1def]
    refine le_trans (Work.Diff.EXT.norm_iteratedFDeriv_sum_le_at
      (s := (Finset.univ : Finset (Fin m)))
      (φ := fun r y' => ∑ p : Fin (Module.finrank ℝ E),
        Work.Diff.GE.cGam (G 0) x₀ (pt (I := I) x₀ y') p (w r) a
          * tower3Arr (I := I) (M := M) G x₀ t A m (Function.update w r p) i j l y')
      (x := y) (n := jj) (C := (Module.finrank ℝ E : ℝ) * P) ?_ ?_) ?_
    · intro r _
      exact ContDiffAt.sum (s := (Finset.univ : Finset (Fin (Module.finrank ℝ E))))
        fun p _ => ContDiffAt.mul (hcG p (w r) a) (hsm (Function.update w r p) i j l)
    · intro r _
      exact hsingle (fun p y' => Work.Diff.GE.cGam (G 0) x₀ (pt (I := I) x₀ y') p (w r) a
          * tower3Arr (I := I) (M := M) G x₀ t A m (Function.update w r p) i j l y')
        (fun p => ContDiffAt.mul (hcG p (w r) a) (hsm (Function.update w r p) i j l))
        (fun p => hprod p (w r) a (Function.update w r p) i j l)
    · simp
  have hF2b : ‖iteratedFDeriv ℝ jj F2 y‖ ≤ (Module.finrank ℝ E : ℝ) * P := by
    rw [hF2def]
    exact hsingle (fun p y' => Work.Diff.GE.cGam (G 0) x₀ (pt (I := I) x₀ y') p i a
        * tower3Arr (I := I) (M := M) G x₀ t A m w p j l y')
      (fun p => ContDiffAt.mul (hcG p i a) (hsm w p j l)) (fun p => hprod p i a w p j l)
  have hF3b : ‖iteratedFDeriv ℝ jj F3 y‖ ≤ (Module.finrank ℝ E : ℝ) * P := by
    rw [hF3def]
    exact hsingle (fun p y' => Work.Diff.GE.cGam (G 0) x₀ (pt (I := I) x₀ y') p j a
        * tower3Arr (I := I) (M := M) G x₀ t A m w i p l y')
      (fun p => ContDiffAt.mul (hcG p j a) (hsm w i p l)) (fun p => hprod p j a w i p l)
  have hF4b : ‖iteratedFDeriv ℝ jj F4 y‖ ≤ (Module.finrank ℝ E : ℝ) * P := by
    rw [hF4def]
    exact hsingle (fun p y' => Work.Diff.GE.cGam (G 0) x₀ (pt (I := I) x₀ y') p l a
        * tower3Arr (I := I) (M := M) G x₀ t A m w i j p y')
      (fun p => ContDiffAt.mul (hcG p l a) (hsm w i j p)) (fun p => hprod p l a w i j p)
  have hF1sm : ContDiffAt ℝ (⊤ : ℕ∞) F1 y := by
    rw [hF1def]
    exact ContDiffAt.sum (s := (Finset.univ : Finset (Fin m))) fun r _ =>
      ContDiffAt.sum (s := (Finset.univ : Finset (Fin (Module.finrank ℝ E))))
        fun p _ => ContDiffAt.mul (hcG p (w r) a) (hsm (Function.update w r p) i j l)
  have hF2sm : ContDiffAt ℝ (⊤ : ℕ∞) F2 y := by
    rw [hF2def]
    exact ContDiffAt.sum (s := (Finset.univ : Finset (Fin (Module.finrank ℝ E))))
      fun p _ => ContDiffAt.mul (hcG p i a) (hsm w p j l)
  have hF3sm : ContDiffAt ℝ (⊤ : ℕ∞) F3 y := by
    rw [hF3def]
    exact ContDiffAt.sum (s := (Finset.univ : Finset (Fin (Module.finrank ℝ E))))
      fun p _ => ContDiffAt.mul (hcG p j a) (hsm w i p l)
  have hF4sm : ContDiffAt ℝ (⊤ : ℕ∞) F4 y := by
    rw [hF4def]
    exact ContDiffAt.sum (s := (Finset.univ : Finset (Fin (Module.finrank ℝ E))))
      fun p _ => ContDiffAt.mul (hcG p l a) (hsm w i j p)
  have hCf : (fun y' : E => towerCorrFun (I := I) (M := M) G x₀ t A m w a i j l y')
      = fun y' : E => F1 y' + (F2 y' + (F3 y' + F4 y')) := by
    funext y'
    simp only [towerCorrFun, hF1def, hF2def, hF3def, hF4def]
  rw [hCf]
  have h34 : ‖iteratedFDeriv ℝ jj (fun y' : E => F3 y' + F4 y') y‖
      ≤ (Module.finrank ℝ E : ℝ) * P + (Module.finrank ℝ E : ℝ) * P :=
    Work.Diff.EXT.norm_iteratedFDeriv_add_le_at₂ (f := F3) (g := F4)
      (C := (Module.finrank ℝ E : ℝ) * P) (D := (Module.finrank ℝ E : ℝ) * P)
      hF3sm hF4sm hF3b hF4b
  have h234 : ‖iteratedFDeriv ℝ jj (fun y' : E => F2 y' + (F3 y' + F4 y')) y‖
      ≤ (Module.finrank ℝ E : ℝ) * P
        + ((Module.finrank ℝ E : ℝ) * P + (Module.finrank ℝ E : ℝ) * P) :=
    Work.Diff.EXT.norm_iteratedFDeriv_add_le_at₂ (f := F2)
      (g := fun y' : E => F3 y' + F4 y')
      (C := (Module.finrank ℝ E : ℝ) * P)
      (D := (Module.finrank ℝ E : ℝ) * P + (Module.finrank ℝ E : ℝ) * P)
      hF2sm (hF3sm.add hF4sm) hF2b h34
  have hall : ‖iteratedFDeriv ℝ jj (fun y' : E => F1 y' + (F2 y' + (F3 y' + F4 y'))) y‖
      ≤ (m : ℝ) * ((Module.finrank ℝ E : ℝ) * P)
        + ((Module.finrank ℝ E : ℝ) * P
          + ((Module.finrank ℝ E : ℝ) * P + (Module.finrank ℝ E : ℝ) * P)) :=
    Work.Diff.EXT.norm_iteratedFDeriv_add_le_at₂ (f := F1)
      (g := fun y' : E => F2 y' + (F3 y' + F4 y'))
      (C := (m : ℝ) * ((Module.finrank ℝ E : ℝ) * P))
      (D := (Module.finrank ℝ E : ℝ) * P
        + ((Module.finrank ℝ E : ℝ) * P + (Module.finrank ℝ E : ℝ) * P))
      hF1sm (hF2sm.add (hF3sm.add hF4sm)) hF1b h234
  refine le_trans hall (le_of_eq ?_)
  ring

/-- **Smoothness of every level of the tower**, from the pointwise smoothness of the base array on
`K'` (and the smoothness of the background Christoffel symbols on the chart target). -/
private theorem tower3Arr_contDiffAt
    (G : ℝ → Submission.Diff.SMet I M) (x₀ : M) (K' : Set E)
    (hK't : K' ⊆ (extChartAt I x₀).target)
    (A : E → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ)
    (hA : ∀ (i j l : Fin (Module.finrank ℝ E)) {y : E}, y ∈ K' →
      ContDiffAt ℝ (⊤ : ℕ∞) (fun y' : E => A y' i j l) y) :
    ∀ (m : ℕ) (w : Fin m → Fin (Module.finrank ℝ E))
      (i j l : Fin (Module.finrank ℝ E)) (t : ℝ) {y : E}, y ∈ K' →
      ContDiffAt ℝ (⊤ : ℕ∞) (fun y' : E =>
        tower3Arr (I := I) (M := M) G x₀ t A m w i j l y') y := by
  intro m
  induction m with
  | zero =>
    intro w i j l t y hy
    simpa only [tower3Arr_zero] using hA i j l hy
  | succ m ih =>
    intro w i j l t y hy
    have hfun : (fun y' : E => tower3Arr (I := I) (M := M) G x₀ t A (m + 1) w i j l y')
        = fun y' : E =>
            fderiv ℝ (fun y'' : E => tower3Arr (I := I) (M := M) G x₀ t A m
                (fun s : Fin m => w s.succ) i j l y'') y'
              (Work.Diff.GE.cBasis (E := E) (w 0))
            - towerCorrFun (I := I) (M := M) G x₀ t A m (fun s : Fin m => w s.succ)
                (w 0) i j l y' := by
      funext y'
      rw [tower3Arr_succ_expand (I := I) (M := M) G x₀ t A m w i j l y']
      simp only [towerCorrFun]
      ring
    rw [hfun]
    exact (Work.Diff.EXT.CBound.contDiffAt_fderiv_apply'
        (ih (fun s : Fin m => w s.succ) i j l t hy)).sub
      (towerCorrFun_contDiffAt (I := I) (M := M) G x₀ K' hK't
        (fun w' i' j' l' t' => ih w' i' j' l' t') t hy)

theorem tower3Arr_jets_family
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (G : ℝ → Submission.Diff.SMet I M) (x₀ : M) (σ T : ℝ)
    (A : ℝ → E → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Fin (Module.finrank ℝ E) → ℝ)
    (K' : Set E) (Mm : ℕ) (hK't : K' ⊆ (extChartAt I x₀).target)
    (hA : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ico σ T, ∀ j : ℕ, j ≤ Mm →
      ∀ (i j' l : Fin (Module.finrank ℝ E)), ∀ y ∈ K',
        ‖iteratedFDeriv ℝ j (fun y' : E => A t y' i j' l) y‖ ≤ C)
    (hAsm : ∀ t ∈ Set.Ico σ T, ∀ y ∈ K', ∀ (i j' l : Fin (Module.finrank ℝ E)),
      ContDiffAt ℝ (⊤ : ℕ∞) (fun y' : E => A t y' i j' l) y)
    (hΓ : ∃ C : ℝ, 0 ≤ C ∧ ∀ j : ℕ, j ≤ Mm →
      ∀ (p a b : Fin (Module.finrank ℝ E)), ∀ y ∈ K',
        ‖iteratedFDeriv ℝ j (fun y' : E => Work.Diff.GE.cGam (G 0) x₀
            (Work.Diff.EXT.pt (I := I) x₀ y') p a b) y‖ ≤ C) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ico σ T, ∀ j : ℕ, j ≤ Mm → ∀ m : ℕ, m ≤ Mm - j →
      ∀ (v : Fin m → Fin (Module.finrank ℝ E)) (i j' l : Fin (Module.finrank ℝ E)), ∀ y ∈ K',
        ‖iteratedFDeriv ℝ j (fun y' : E =>
            Work.Diff.EXT.ConnCov.tower3Arr (I := I) (M := M) G x₀ t (A t) m v i j' l y') y‖ ≤ C := by
  classical
  obtain ⟨CA, hCA0, hCA⟩ := hA
  obtain ⟨CΓ, hCΓ0, hCΓ⟩ := hΓ
  -- the uniform norm of the model basis
  set Kb : ℝ := max 1 (∑ a : Fin (Module.finrank ℝ E), ‖Module.finBasis ℝ E a‖) with hKbdef
  have hKb0 : 0 ≤ Kb := le_trans zero_le_one (le_max_left _ _)
  have hKbnorm : ∀ a : Fin (Module.finrank ℝ E),
      ‖Work.Diff.GE.cBasis (E := E) a‖ ≤ Kb := by
    intro a
    refine le_trans (Finset.single_le_sum (s := Finset.univ)
      (f := fun b : Fin (Module.finrank ℝ E) => ‖Module.finBasis ℝ E b‖)
      (fun b _ => norm_nonneg _) (Finset.mem_univ a)) (le_max_right _ _)
  -- the statement, with the level as the index of the uniform constant
  set P : ℕ → ℝ → Prop := (fun m C => ∀ t ∈ Set.Ico σ T, ∀ y ∈ K', ∀ j : ℕ, j ≤ Mm - m →
      ∀ (v : Fin m → Fin (Module.finrank ℝ E)) (i j' l : Fin (Module.finrank ℝ E)),
        ‖iteratedFDeriv ℝ j (fun y' : E =>
          tower3Arr (I := I) (M := M) G x₀ t (A t) m v i j' l y') y‖ ≤ C) with hPdef
  have hmono : ∀ m (C C' : ℝ), P m C → C ≤ C' → P m C' := by
    intro m C C' h hle
    rw [hPdef] at h ⊢
    exact fun t ht y hy j hj v i j' l => le_trans (h t ht y hy j hj v i j' l) hle
  have key : ∀ m ≤ Mm, ∃ C : ℝ, 0 ≤ C ∧ P m C := by
    intro m
    induction m with
    | zero =>
      intro _
      rw [hPdef]
      refine ⟨CA, hCA0, ?_⟩
      intro t ht y hy j hj v i j' l
      simpa only [tower3Arr_zero] using hCA t ht j (by omega) i j' l y hy
    | succ m ih =>
      intro hmk
      obtain ⟨Cm, hCm0, hCm⟩ := ih (by omega)
      rw [hPdef] at hCm
      -- the common bound for the two smooth factors of the Leibniz estimate
      set B : ℝ := max Cm CΓ with hBdef
      have hB0 : 0 ≤ B := by rw [hBdef]; exact le_trans hCm0 (le_max_left _ _)
      have hCmB : Cm ≤ B := by rw [hBdef]; exact le_max_left _ _
      have hCΓB : CΓ ≤ B := by rw [hBdef]; exact le_max_right _ _
      -- the Leibniz bound for one Christoffel-times-level product
      set Pj : ℝ := (2 : ℝ) ^ Mm * B * B with hPjdef
      -- the number of summands of the correction
      set Ns : ℝ := (m : ℝ) * (Module.finrank ℝ E : ℝ)
        + 3 * (Module.finrank ℝ E : ℝ) with hNsdef
      set Cb : ℝ := max (Kb * Cm) (Ns * Pj) with hCbdef
      have hKbCm : Kb * Cm ≤ Cb := le_max_left _ _
      have hNsPj : Ns * Pj ≤ Cb := le_max_right _ _
      refine ⟨Cb + Cb, by positivity, ?_⟩
      rw [hPdef]
      intro t ht y hy j hj v i j' l
      have hjSm : j ≤ Mm - m := by omega
      have hj1 : j + 1 ≤ Mm - m := by omega
      have hAsm' : ∀ (i0 j0 l0 : Fin (Module.finrank ℝ E)) {y0 : E}, y0 ∈ K' →
          ContDiffAt ℝ (⊤ : ℕ∞) (fun y' : E => A t y' i0 j0 l0) y0 :=
        fun i0 j0 l0 y0 hy0 => hAsm t ht y0 hy0 i0 j0 l0
      have hlevsm : ∀ (w' : Fin m → Fin (Module.finrank ℝ E))
          (i0 j0 l0 : Fin (Module.finrank ℝ E)),
          ContDiffAt ℝ (⊤ : ℕ∞) (fun y' : E =>
            tower3Arr (I := I) (M := M) G x₀ t (A t) m w' i0 j0 l0 y') y :=
        fun w' i0 j0 l0 => tower3Arr_contDiffAt (I := I) (M := M) G x₀ K' hK't (A t) hAsm'
          m w' i0 j0 l0 t hy
      -- the two pieces of the recursion
      set G1 : E → ℝ := fun y' => fderiv ℝ (fun y'' : E =>
          tower3Arr (I := I) (M := M) G x₀ t (A t) m (fun s : Fin m => v s.succ) i j' l y'') y'
          (Work.Diff.GE.cBasis (E := E) (v 0)) with hG1def
      set G2 : E → ℝ := fun y' => towerCorrFun (I := I) (M := M) G x₀ t (A t) m
          (fun s : Fin m => v s.succ) (v 0) i j' l y' with hG2def
      have hsplit : (fun y' : E => tower3Arr (I := I) (M := M) G x₀ t (A t) (m + 1) v i j' l y')
          = fun y' : E => G1 y' + (fun z : E => -G2 z) y' := by
        funext y'
        rw [tower3Arr_succ_expand (I := I) (M := M) G x₀ t (A t) m v i j' l y']
        simp only [hG1def, hG2def, towerCorrFun]
        ring
      have hG1sm : ContDiffAt ℝ (⊤ : ℕ∞) G1 y := by
        rw [hG1def]
        exact Work.Diff.EXT.CBound.contDiffAt_fderiv_apply'
          (hlevsm (fun s : Fin m => v s.succ) i j' l)
      have hG2sm : ContDiffAt ℝ (⊤ : ℕ∞) G2 y := by
        rw [hG2def]
        exact towerCorrFun_contDiffAt (I := I) (M := M) G x₀ K' hK't
          (fun w' i' j' l' t' => tower3Arr_contDiffAt (I := I) (M := M) G x₀ K' hK't (A t)
            hAsm' m w' i' j' l' t') t hy
      have hG1b : ‖iteratedFDeriv ℝ j G1 y‖ ≤ Kb * Cm := by
        rw [hG1def]
        refine le_trans (norm_iteratedFDeriv_fderiv_apply_le (ψ := fun y'' : E =>
          tower3Arr (I := I) (M := M) G x₀ t (A t) m (fun s : Fin m => v s.succ) i j' l y'')
          (y := y) (ζ := Work.Diff.GE.cBasis (E := E) (v 0)) (j := j) ?_) ?_
        · exact hlevsm (fun s : Fin m => v s.succ) i j' l
        · exact mul_le_mul (hKbnorm (v 0))
            (hCm t ht y hy (j + 1) hj1 (fun s : Fin m => v s.succ) i j' l)
            (norm_nonneg _) hKb0
      have hG2b : ‖iteratedFDeriv ℝ j G2 y‖ ≤ Ns * Pj := by
        rw [hG2def]
        have hprod : ∀ (p q r : Fin (Module.finrank ℝ E))
            (w' : Fin m → Fin (Module.finrank ℝ E))
            (i' j' l' : Fin (Module.finrank ℝ E)),
            ‖iteratedFDeriv ℝ j (fun y' : E => Work.Diff.GE.cGam (G 0) x₀
              (Work.Diff.EXT.pt (I := I) x₀ y') p q r
              * tower3Arr (I := I) (M := M) G x₀ t (A t) m w' i' j' l' y') y‖ ≤ Pj := by
          intro p q r w' i' j' l'
          refine le_trans (Work.Diff.EXT.norm_iteratedFDeriv_mul_le_at_le (k := j) (m := j)
            (B := B) le_rfl ?_ ?_ hB0 ?_ ?_) ?_
          · exact Work.Diff.EXT.CBound.cGam_contDiffAt_of_target (I := I) (M := M) (G 0) x₀
              (hK't hy) p q r
          · exact hlevsm w' i' j' l'
          · intro i hi
            exact le_trans (hCΓ i (by omega) p q r y hy) hCΓB
          · intro i hi
            exact le_trans (hCm t ht y hy i (le_trans hi hjSm) w' i' j' l') hCmB
          · rw [hPjdef]
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right
                (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : j ≤ Mm)) hB0)
              (by positivity)
        refine le_trans (towerCorrFun_jet_le (I := I) (M := M) G x₀ K' hK't (A t) m
          (fun s : Fin m => v s.succ) (v 0) i j' l (t := t) (y := y) hy hlevsm hprod) ?_
        rw [hNsdef]
      have hGneg : ‖iteratedFDeriv ℝ j (fun z : E => -G2 z) y‖ ≤ Ns * Pj := by
        have h1 : (fun z : E => -G2 z) = -G2 := rfl
        rw [h1, iteratedFDeriv_neg]
        simpa using hG2b
      rw [hsplit]
      refine le_trans (Work.Diff.EXT.norm_iteratedFDeriv_add_le_at₂ (f := G1)
        (g := fun z : E => -G2 z) (C := Kb * Cm) (D := Ns * Pj) hG1sm hG2sm.neg hG1b hGneg) ?_
      linarith [hKbCm, hNsPj]
  obtain ⟨C, hC0, hC⟩ := Work.Diff.EXT.exists_uniform_bound_of_le (P := P) hmono Mm key
  rw [hPdef] at hC
  exact ⟨C, hC0, fun t ht j hj m hm v i j' l y hy => hC m (by omega) t ht y hy j (by omega) v i j' l⟩

end Work.Diff.EXT.ConnCov
