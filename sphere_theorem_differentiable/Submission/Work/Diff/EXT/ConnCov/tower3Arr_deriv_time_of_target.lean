import Mathlib
import Submission.Work.Diff.EXT.ConnCov.ChartTowerDefs
import Submission.Work.Diff.T.clairaut_fderiv_apply
import Submission.Work.Diff.EXT.ConnCov.tower3Arr_jointSmooth

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The time derivative of the chart tower `tower3Arr`

`Work.Diff.EXT.ConnCov.tower3Arr G x₀ t A m v i j l` is the chart recursion of a `(0,3)`-array
`A` with respect to the *fixed* background connection `cGam (G 0)`.  Its parameter `t` is phantom:
`tower3Arr G x₀ s A m v i j l` depends on `s` only through the base `A`.  Hence, for a family
`s ↦ A s`, the time derivative of the tower of the family is the tower of the pointwise time
derivative `∂_s A`:

`∂_s (tower3Arr G x₀ s (A s) m v i j l y) = tower3Arr G x₀ t (∂_s A) m v i j l y`   at `s = t`.

**This is the statement of `Work.Diff.EXT.ConnCov.tower3Arr_deriv_time`, which however is FALSE as
written**: it omits the hypothesis that the point `y` lies in the chart target
`(extChartAt I x₀).target`.  The recursion multiplies by the coefficient functions
`y' ↦ cGam (G 0) x₀ (pt x₀ y') k i j`, which are smooth only on the target (they involve the
inverse chart `pt x₀ = (extChartAt I x₀).symm`, whose values outside the target are *arbitrary
junk data* of the `ChartedSpace` structure, not controlled by anything).  For `y` outside the
target these coefficients need not even be continuous at `y`, the tower levels need not be
differentiable at `y`, and `fderiv` defaults to `0` there; the resulting "junk cancellation" does
not preserve the claimed identity.  (Concretely: take `E = ℝ`, a chart whose `invFun` is a step
function jumping at `y`, `A s y' = c + (s - t) * (y' - y)^2` with `c ≠ 0` — jointly smooth, indeed
polynomial — and level `m = 2`: then `T_1(A_s) = ∂_{y'} A_s - 3γ·A_s` is *not* differentiable at
`y` for any `s`, so its `fderiv` at `y` vanishes identically in `s` and the left-hand side has
derivative `0`, while the right-hand side is `fderiv (∂_{y'}A_t - 3γ·A_t)(y)`, which is nonzero
because `(y'-y)^2` tames the jump of `γ`.)

The present file proves the *correct* statement, i.e. with `hy : y ∈ (extChartAt I x₀).target`.
The proof is split into two halves:

* `tower3Arr_hasDerivAt_of_jointSmooth` — the derivative statement, assuming that every level of
  the tower is *jointly* smooth at `(t,y)` (this hypothesis is what makes Clairaut's theorem
  applicable, since level `m+1` is the `fderiv` in `y` of level `m`);
* `tower3Arr_deriv_time_of_target` — the same with the joint smoothness *proved* from `hy` and
  the joint smoothness of `A` (via `Work.Diff.EXT.ConnCov.tower3Arr_jointSmooth`).
-/

set_option maxHeartbeats 2000000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.EXT.ConnCov

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-- `(k : ℕ∞ω) ≤ ∞`, i.e. `C^k` follows from `C^∞`. -/
private lemma natCast_le_smooth (k : ℕ) : ((k : ℕ∞ω) ≤ ∞) := by
  rw [show (∞ : ℕ∞ω) = ((⊤ : ℕ∞) : ℕ∞ω) from rfl]
  exact WithTop.coe_le_coe.mpr le_top

/-- `(k : ℕ∞ω) ≠ ∞` for `k : ℕ`. -/
private lemma natCast_ne_smooth (k : ℕ) : ((k : ℕ∞ω) ≠ ∞) := by
  rw [show (∞ : ℕ∞ω) = ((⊤ : ℕ∞) : ℕ∞ω) from rfl]
  intro h
  exact absurd (WithTop.coe_injective h) (ne_of_lt (WithTop.coe_lt_top (k : ℕ)))

/-- **The time derivative of the chart tower `tower3Arr`**, assuming that all its levels are
jointly smooth at `(t, y)` (which is what Clairaut's theorem needs at level `m + 1`).  The
statement has no manifold-level hypothesis: it is a purely analytic statement about the chart
recursion `tower3Arr` and the pointwise time derivative of its base. -/
theorem tower3Arr_hasDerivAt_of_jointSmooth
    (G : ℝ → Submission.Diff.SMet I M) (x₀ : M) {t : ℝ} {y : E}
    (A : ℝ → E → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Fin (Module.finrank ℝ E) → ℝ)
    (J : ∀ (m : ℕ) (v : Fin m → Fin (Module.finrank ℝ E))
        (i j l : Fin (Module.finrank ℝ E)),
      ContDiffAt ℝ (⊤ : ℕ∞) (fun p : ℝ × E =>
        tower3Arr (I := I) (M := M) G x₀ p.1 (A p.1) m v i j l p.2) (t, y)) :
    ∀ (m : ℕ) (v : Fin m → Fin (Module.finrank ℝ E)) (i j l : Fin (Module.finrank ℝ E)),
      HasDerivAt (fun s : ℝ => tower3Arr (I := I) (M := M) G x₀ s (A s) m v i j l y)
        (tower3Arr (I := I) (M := M) G x₀ t
          (fun y' i j' l => deriv (fun s : ℝ => A s y' i j' l) t) m v i j l y) t := by
  classical
  set dA : E → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Fin (Module.finrank ℝ E) → ℝ :=
    fun y' i j l => deriv (fun s : ℝ => A s y' i j l) t with hdA
  suffices key : ∀ m : ℕ, ∃ V : Set E, IsOpen V ∧ y ∈ V ∧
      ∀ (v : Fin m → Fin (Module.finrank ℝ E)) (i j l : Fin (Module.finrank ℝ E)), ∀ y' ∈ V,
        HasDerivAt (fun s : ℝ => tower3Arr (I := I) (M := M) G x₀ s (A s) m v i j l y')
          (tower3Arr (I := I) (M := M) G x₀ t dA m v i j l y') t by
    intro m v i j l
    obtain ⟨V, _, hyV, hV⟩ := key m
    simpa only [hdA] using hV v i j l y hyV
  intro m
  induction m with
  | zero =>
      have hpt : ∀ (i j l : Fin (Module.finrank ℝ E)), ∀ᶠ y' in 𝓝 y,
          HasDerivAt (fun s : ℝ => A s y' i j l)
            (deriv (fun s : ℝ => A s y' i j l) t) t := by
        intro i j l
        have hcd : ContDiffAt ℝ 1 (fun p : ℝ × E => A p.1 p.2 i j l) (t, y) :=
          (J 0 (fun i : Fin 0 => i.elim0) i j l).of_le (natCast_le_smooth 1)
        have h1 : ∀ᶠ p in 𝓝 (t, y),
            DifferentiableAt ℝ (fun p : ℝ × E => A p.1 p.2 i j l) p :=
          (hcd.eventually (natCast_ne_smooth 1)).mono
            (fun p hp => hp.differentiableAt (by norm_num))
        have h2 : ∀ᶠ y' in 𝓝 y,
            DifferentiableAt ℝ (fun p : ℝ × E => A p.1 p.2 i j l) (t, y') :=
          (continuousAt_const.prodMk continuousAt_id).eventually h1
        filter_upwards [h2] with y' hy'
        exact (hy'.comp t ((differentiableAt_id.prodMk (differentiableAt_const y')))).hasDerivAt
      have hall : ∀ᶠ y' in 𝓝 y, ∀ (i j l : Fin (Module.finrank ℝ E)),
          HasDerivAt (fun s : ℝ => A s y' i j l)
            (deriv (fun s : ℝ => A s y' i j l) t) t :=
        Filter.eventually_all.2 (fun i =>
          Filter.eventually_all.2 (fun j => Filter.eventually_all.2 (fun l => hpt i j l)))
      obtain ⟨V, hVsub, hVopen, hyV⟩ := _root_.mem_nhds_iff.1 hall
      refine ⟨V, hVopen, hyV, ?_⟩
      intro v i j l y' hy'
      simpa only [tower3Arr_zero, hdA] using hVsub hy' i j l
  | succ m ih =>
      obtain ⟨V, hVopen, hyV, hV⟩ := ih
      -- the level-`m` towers are `C²`, hence jointly smooth, near `(t, y')` for `y'` near `y`
      have hsmev : ∀ᶠ y' in 𝓝 y, ∀ (w : Fin m → Fin (Module.finrank ℝ E))
            (a b c : Fin (Module.finrank ℝ E)),
          ContDiffAt ℝ 2 (fun p : ℝ × E =>
            tower3Arr (I := I) (M := M) G x₀ p.1 (A p.1) m w a b c p.2) (t, y') := by
        refine Filter.eventually_all.2 (fun w => Filter.eventually_all.2 (fun a =>
          Filter.eventually_all.2 (fun b => Filter.eventually_all.2 (fun c => ?_))))
        have h1 : ∀ᶠ p in 𝓝 (t, y), ContDiffAt ℝ 2 (fun p : ℝ × E =>
            tower3Arr (I := I) (M := M) G x₀ p.1 (A p.1) m w a b c p.2) p :=
          ((J m w a b c).of_le (natCast_le_smooth 2)).eventually (natCast_ne_smooth 2)
        exact (continuousAt_const.prodMk continuousAt_id).eventually h1
      obtain ⟨W, hWsub, hWopen, hyW⟩ := _root_.mem_nhds_iff.1 hsmev
      refine ⟨V ∩ W, hVopen.inter hWopen, ⟨hyV, hyW⟩, ?_⟩
      intro v i j l y' hy'
      obtain ⟨hy'V, hy'W⟩ := hy'
      -- the level-`m` derivative statement, available on the whole open set `V ∋ y'`
      have hT : ∀ (w : Fin m → Fin (Module.finrank ℝ E)) (a b c : Fin (Module.finrank ℝ E)),
          HasDerivAt (fun s : ℝ => tower3Arr (I := I) (M := M) G x₀ s (A s) m w a b c y')
            (tower3Arr (I := I) (M := M) G x₀ t dA m w a b c y') t :=
        fun w a b c => hV w a b c y' hy'V
      -- ## the `fderiv` term, by Clairaut
      set Φ : ℝ × E → ℝ := fun p => tower3Arr (I := I) (M := M) G x₀ p.1 (A p.1) m
        (fun i : Fin m => v i.succ) i j l p.2 with hΦ
      have hF : HasDerivAt
          (fun s : ℝ => fderiv ℝ (fun y'' : E => tower3Arr (I := I) (M := M) G x₀ s (A s) m
              (fun i : Fin m => v i.succ) i j l y'') y' (Work.Diff.GE.cBasis (E := E) (v 0)))
          (fderiv ℝ (fun y'' : E => tower3Arr (I := I) (M := M) G x₀ t dA m
              (fun i : Fin m => v i.succ) i j l y'') y' (Work.Diff.GE.cBasis (E := E) (v 0))) t := by
        have hsm2 : ContDiffAt ℝ 2 Φ (t, y') := by
          simpa only [hΦ] using hWsub hy'W (fun i : Fin m => v i.succ) i j l
        have hcl := Work.Diff.T.clairaut_fderiv_apply (Φ := Φ) hsm2
          (Work.Diff.GE.cBasis (E := E) (v 0))
        have heq : (fun y'' : E => deriv (fun s : ℝ => Φ (s, y'')) t)
            =ᶠ[𝓝 y'] (fun y'' : E => tower3Arr (I := I) (M := M) G x₀ t dA m
              (fun i : Fin m => v i.succ) i j l y'') := by
          filter_upwards [hVopen.mem_nhds hy'V] with y'' hy''V
          simpa only [hΦ] using
            (hV (fun i : Fin m => v i.succ) i j l y'' hy''V).deriv
        refine hcl.congr_deriv ?_
        rw [heq.fderiv_eq]
      -- ## the correction sums
      have hS1 : HasDerivAt
          (fun s : ℝ => ∑ r : Fin m, ∑ p : Fin (Module.finrank ℝ E),
              Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y')
                  p (v r.succ) (v 0)
                * tower3Arr (I := I) (M := M) G x₀ s (A s) m
                    (Function.update (fun i : Fin m => v i.succ) r p) i j l y')
          (∑ r : Fin m, ∑ p : Fin (Module.finrank ℝ E),
              Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y')
                  p (v r.succ) (v 0)
                * tower3Arr (I := I) (M := M) G x₀ t dA m
                    (Function.update (fun i : Fin m => v i.succ) r p) i j l y') t := by
        have hinner : ∀ r : Fin m, HasDerivAt
            (fun s : ℝ => ∑ p : Fin (Module.finrank ℝ E),
                Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y')
                    p (v r.succ) (v 0)
                  * tower3Arr (I := I) (M := M) G x₀ s (A s) m
                      (Function.update (fun i : Fin m => v i.succ) r p) i j l y')
            (∑ p : Fin (Module.finrank ℝ E),
                Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y')
                    p (v r.succ) (v 0)
                  * tower3Arr (I := I) (M := M) G x₀ t dA m
                      (Function.update (fun i : Fin m => v i.succ) r p) i j l y') t := by
          intro r
          have hsum := HasDerivAt.sum
            (u := (Finset.univ : Finset (Fin (Module.finrank ℝ E))))
            (A := fun p : Fin (Module.finrank ℝ E) => fun s : ℝ =>
                Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y')
                    p (v r.succ) (v 0)
                  * tower3Arr (I := I) (M := M) G x₀ s (A s) m
                      (Function.update (fun i : Fin m => v i.succ) r p) i j l y')
            (A' := fun p : Fin (Module.finrank ℝ E) =>
                Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y')
                    p (v r.succ) (v 0)
                  * tower3Arr (I := I) (M := M) G x₀ t dA m
                      (Function.update (fun i : Fin m => v i.succ) r p) i j l y')
            (fun p _ => (hT (Function.update (fun i : Fin m => v i.succ) r p) i j l).const_mul _)
          refine hsum.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
          simp only [Finset.sum_apply]
        have houter := HasDerivAt.sum (u := (Finset.univ : Finset (Fin m)))
          (A := fun r : Fin m => fun s : ℝ => ∑ p : Fin (Module.finrank ℝ E),
              Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y')
                  p (v r.succ) (v 0)
                * tower3Arr (I := I) (M := M) G x₀ s (A s) m
                    (Function.update (fun i : Fin m => v i.succ) r p) i j l y')
          (A' := fun r : Fin m => ∑ p : Fin (Module.finrank ℝ E),
              Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y')
                  p (v r.succ) (v 0)
                * tower3Arr (I := I) (M := M) G x₀ t dA m
                    (Function.update (fun i : Fin m => v i.succ) r p) i j l y')
          (fun r _ => hinner r)
        refine houter.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
        simp only [Finset.sum_apply]
      have hS2 : HasDerivAt
          (fun s : ℝ => ∑ p : Fin (Module.finrank ℝ E),
              Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y') p i (v 0)
                * tower3Arr (I := I) (M := M) G x₀ s (A s) m
                    (fun i : Fin m => v i.succ) p j l y')
          (∑ p : Fin (Module.finrank ℝ E),
              Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y') p i (v 0)
                * tower3Arr (I := I) (M := M) G x₀ t dA m
                    (fun i : Fin m => v i.succ) p j l y') t := by
        have hsum := HasDerivAt.sum
          (u := (Finset.univ : Finset (Fin (Module.finrank ℝ E))))
          (A := fun p : Fin (Module.finrank ℝ E) => fun s : ℝ =>
              Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y') p i (v 0)
                * tower3Arr (I := I) (M := M) G x₀ s (A s) m
                    (fun i : Fin m => v i.succ) p j l y')
          (A' := fun p : Fin (Module.finrank ℝ E) =>
              Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y') p i (v 0)
                * tower3Arr (I := I) (M := M) G x₀ t dA m
                    (fun i : Fin m => v i.succ) p j l y')
          (fun p _ => (hT (fun i : Fin m => v i.succ) p j l).const_mul _)
        refine hsum.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
        simp only [Finset.sum_apply]
      have hS3 : HasDerivAt
          (fun s : ℝ => ∑ p : Fin (Module.finrank ℝ E),
              Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y') p j (v 0)
                * tower3Arr (I := I) (M := M) G x₀ s (A s) m
                    (fun i : Fin m => v i.succ) i p l y')
          (∑ p : Fin (Module.finrank ℝ E),
              Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y') p j (v 0)
                * tower3Arr (I := I) (M := M) G x₀ t dA m
                    (fun i : Fin m => v i.succ) i p l y') t := by
        have hsum := HasDerivAt.sum
          (u := (Finset.univ : Finset (Fin (Module.finrank ℝ E))))
          (A := fun p : Fin (Module.finrank ℝ E) => fun s : ℝ =>
              Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y') p j (v 0)
                * tower3Arr (I := I) (M := M) G x₀ s (A s) m
                    (fun i : Fin m => v i.succ) i p l y')
          (A' := fun p : Fin (Module.finrank ℝ E) =>
              Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y') p j (v 0)
                * tower3Arr (I := I) (M := M) G x₀ t dA m
                    (fun i : Fin m => v i.succ) i p l y')
          (fun p _ => (hT (fun i : Fin m => v i.succ) i p l).const_mul _)
        refine hsum.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
        simp only [Finset.sum_apply]
      have hS4 : HasDerivAt
          (fun s : ℝ => ∑ p : Fin (Module.finrank ℝ E),
              Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y') p l (v 0)
                * tower3Arr (I := I) (M := M) G x₀ s (A s) m
                    (fun i : Fin m => v i.succ) i j p y')
          (∑ p : Fin (Module.finrank ℝ E),
              Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y') p l (v 0)
                * tower3Arr (I := I) (M := M) G x₀ t dA m
                    (fun i : Fin m => v i.succ) i j p y') t := by
        have hsum := HasDerivAt.sum
          (u := (Finset.univ : Finset (Fin (Module.finrank ℝ E))))
          (A := fun p : Fin (Module.finrank ℝ E) => fun s : ℝ =>
              Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y') p l (v 0)
                * tower3Arr (I := I) (M := M) G x₀ s (A s) m
                    (fun i : Fin m => v i.succ) i j p y')
          (A' := fun p : Fin (Module.finrank ℝ E) =>
              Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y') p l (v 0)
                * tower3Arr (I := I) (M := M) G x₀ t dA m
                    (fun i : Fin m => v i.succ) i j p y')
          (fun p _ => (hT (fun i : Fin m => v i.succ) i j p).const_mul _)
        refine hsum.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
        simp only [Finset.sum_apply]
      -- ## unfold both sides one level and assemble
      rw [show (fun s : ℝ => tower3Arr (I := I) (M := M) G x₀ s (A s) (m + 1) v i j l y')
          = fun s : ℝ =>
              fderiv ℝ (fun y'' : E => tower3Arr (I := I) (M := M) G x₀ s (A s) m
                  (fun i : Fin m => v i.succ) i j l y'') y'
                  (Work.Diff.GE.cBasis (E := E) (v 0))
              - (∑ r : Fin m, ∑ p : Fin (Module.finrank ℝ E),
                    Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y')
                        p (v r.succ) (v 0)
                      * tower3Arr (I := I) (M := M) G x₀ s (A s) m
                          (Function.update (fun i : Fin m => v i.succ) r p) i j l y')
              - (∑ p : Fin (Module.finrank ℝ E),
                    Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y') p i (v 0)
                      * tower3Arr (I := I) (M := M) G x₀ s (A s) m
                          (fun i : Fin m => v i.succ) p j l y')
              - (∑ p : Fin (Module.finrank ℝ E),
                    Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y') p j (v 0)
                      * tower3Arr (I := I) (M := M) G x₀ s (A s) m
                          (fun i : Fin m => v i.succ) i p l y')
              - (∑ p : Fin (Module.finrank ℝ E),
                    Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y') p l (v 0)
                      * tower3Arr (I := I) (M := M) G x₀ s (A s) m
                          (fun i : Fin m => v i.succ) i j p y') from by
        funext s
        exact congrFun (tower3Arr_succ (I := I) (M := M) G x₀ s (A s) m v i j l) y']
      rw [show tower3Arr (I := I) (M := M) G x₀ t dA (m + 1) v i j l y'
          = fderiv ℝ (fun y'' : E => tower3Arr (I := I) (M := M) G x₀ t dA m
                (fun i : Fin m => v i.succ) i j l y'') y'
                (Work.Diff.GE.cBasis (E := E) (v 0))
            - (∑ r : Fin m, ∑ p : Fin (Module.finrank ℝ E),
                  Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y')
                      p (v r.succ) (v 0)
                    * tower3Arr (I := I) (M := M) G x₀ t dA m
                        (Function.update (fun i : Fin m => v i.succ) r p) i j l y')
            - (∑ p : Fin (Module.finrank ℝ E),
                  Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y') p i (v 0)
                    * tower3Arr (I := I) (M := M) G x₀ t dA m
                        (fun i : Fin m => v i.succ) p j l y')
            - (∑ p : Fin (Module.finrank ℝ E),
                  Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y') p j (v 0)
                    * tower3Arr (I := I) (M := M) G x₀ t dA m
                        (fun i : Fin m => v i.succ) i p l y')
            - (∑ p : Fin (Module.finrank ℝ E),
                  Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y') p l (v 0)
                    * tower3Arr (I := I) (M := M) G x₀ t dA m
                        (fun i : Fin m => v i.succ) i j p y') from
        congrFun (tower3Arr_succ (I := I) (M := M) G x₀ t dA m v i j l) y']
      exact ((((hF.sub hS1).sub hS2).sub hS3).sub hS4)

/-- **The time derivative of the chart tower `tower3Arr`** — the *correct* version of
`Work.Diff.EXT.ConnCov.tower3Arr_deriv_time`, with the chart-target hypothesis
`hy : y ∈ (extChartAt I x₀).target` which is needed to make the coefficient functions
`y' ↦ cGam (G 0) x₀ (pt x₀ y') k i j` smooth (see the docstring of
`Submission/Work/Diff/EXT/ConnCov/tower3Arr_deriv_time.lean` for the counterexample showing that
the statement without `hy` is false). -/
theorem tower3Arr_deriv_time_of_target
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (G : ℝ → Submission.Diff.SMet I M) (x₀ : M) {t : ℝ} {y : E}
    (hy : y ∈ (extChartAt I x₀).target)
    (A : ℝ → E → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ)
    (hsm : ∀ (i j l : Fin (Module.finrank ℝ E)),
      ContDiffAt ℝ (⊤ : ℕ∞) (fun p : ℝ × E => A p.1 p.2 i j l) (t, y)) :
    ∀ (m : ℕ) (v : Fin m → Fin (Module.finrank ℝ E))
      (i j l : Fin (Module.finrank ℝ E)),
      HasDerivAt (fun s : ℝ => tower3Arr (I := I) (M := M) G x₀ s (A s) m v i j l y)
        (tower3Arr (I := I) (M := M) G x₀ t
          (fun y' i j' l => deriv (fun s : ℝ => A s y' i j' l) t) m v i j l y) t :=
  tower3Arr_hasDerivAt_of_jointSmooth (I := I) (M := M) G x₀ A
    (fun m v i j l =>
      tower3Arr_jointSmooth (I := I) (M := M) G x₀ hy A hsm m v i j l)

end Work.Diff.EXT.ConnCov
