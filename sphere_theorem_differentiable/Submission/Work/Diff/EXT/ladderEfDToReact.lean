import Mathlib
import Submission.Work.Diff.EXT.ladderEfDefs
import Submission.Work.Diff.EXT.towerReactDefs
import Submission.Work.Diff.EXT.evolCompKFix_all
import Submission.Work.Diff.EXT.evolX.ladderPlumb
import Submission.Work.Diff.EXT.covKRm_derivWithin
import Submission.Work.Diff.EXT.reactOpDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# From the frame-field reaction ladder to the classical reaction estimate

`Work.Diff.EXT.ladderEfDToReact` converts the *ladder* hypothesis

`∀ j, ∃ C ≥ 0, ∀ G T (IsRicciFlow G T) t ∈ [0,T) x Ef (IsFrameNear (G t) x Ef),
   LadderEfD G t x Ef k j C`

— a bound on *all jets* `∇^j R_k` of the reaction `R_k = ∂ₜ⁺(∇^k Rm) − Δ(∇^k Rm)` traced in a
smooth frame *field* `Ef` which is orthonormal near `x` — into the classical reaction estimate
`Work.Diff.EXT.EvolCompKFixReact k`:

`D ≤ Δ(∇^k Rm) + C (∑_{i+j=k} √f_i √f_j) ∏‖·‖`,  `f_i = |∇^i Rm|²`,

where `D` is the right derivative of `s ↦ ∇^k Rm(G s)(x)` on `[0,T)`.

## Contents

* `Work.Diff.EXT.ckt_append_smoothExt_eq_covKRm` — the value of the level-`k` tower `ckt` on the
  tuple `smoothExt x (Fin.append u v ·)` is the `(0,k+4)`-tensor `covKRm` on the corresponding
  tangent vectors (definitional unpacking of `ckt_eq_covKRmExt`).
* `Work.Diff.EXT.sum_cons_ckt_eq_lapCovKRm` — the *trace identity*: for a frame field `Ef` with
  `Ef m x = onFrame g x m`, the `Ef`-trace of the second derivative of the tower is the rough
  Laplacian `lapCovKRm`, traced in `onFrame g x`.  This is what makes the frame-field operator
  `reactOpEfD` (whose trace is taken in `Ef`) agree at `x` with the honest reaction
  `∂ₜ(∇^k Rm) − Δ(∇^k Rm)`.  Proof: `ckt_eq_covKRmExt` + the value-dependence `ckt_val_dep_all`
  (`∇^k Rm` is tensorial), reducing both traces to the values of the frame at `x`.
* the target, which uses the existence half `Work.Diff.EXT.covKRm_derivWithin`
  (`s ↦ ∇^k Rm(G s)(x)` has right derivative `derivWithin … (Ioi 0) t`) and the `j = 0` ladder
  bound with the frame field `Ef` chosen by `Work.Diff.EXT.evolX.isFrameNear_exists` (so that its
  value at `x` is `onFrame (G t) x`).
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-! ## The two dictionary lemmas -/

/-- **The tower on the `smoothExt`-extensions of `Fin.append u v` is `covKRm`.** -/
theorem ckt_append_smoothExt_eq_covKRm [T2Space M] (g : SMet I M) (x : M) (k : ℕ)
    (u : Fin k → TangentSpace I x) (v : Fin 4 → TangentSpace I x) :
    ckt g k (fun r => smoothExt x (Fin.append u v r)) x
      = covKRm g x k u (v 0) (v 1) (v 2) (v 3) := by
  rw [ckt_eq_covKRmExt]
  have h1 : (fun i : Fin k => smoothExt x (Fin.append u v (Fin.castAdd 4 i)))
      = fun i : Fin k => smoothExt x (u i) := by
    funext i
    rw [Fin.append_left]
  have h2 : smoothExt x (Fin.append u v (Fin.natAdd k 0)) = smoothExt x (v 0) := by
    rw [Fin.append_right]
  have h3 : smoothExt x (Fin.append u v (Fin.natAdd k 1)) = smoothExt x (v 1) := by
    rw [Fin.append_right]
  have h4 : smoothExt x (Fin.append u v (Fin.natAdd k 2)) = smoothExt x (v 2) := by
    rw [Fin.append_right]
  have h5 : smoothExt x (Fin.append u v (Fin.natAdd k 3)) = smoothExt x (v 3) := by
    rw [Fin.append_right]
  rw [h1, h2, h3, h4, h5]
  rfl

/-- **The trace identity: the `Ef`-trace of the second derivative of the tower is `lapCovKRm`.**
For a smooth frame family `Ef` whose value at `x` is the metric frame `onFrame g x`, the trace
`∑ m ∇_{Ef m}∇_{Ef m}(∇^k Rm)(x)` (written through the tower `ckt`) is the rough Laplacian
`Δ∇^k Rm` at `x` traced in `onFrame g x` (the definition of `lapCovKRm`).

Both sides are `ckt`/`covKRmExt` on tuples of smooth fields with the same values at `x`
(`Ef m x = onFrame g x m`, `smoothExt x · x = ·`), so the value-dependence of the tower
(`Work.Diff.EXT.ckt_val_dep_all`) identifies them. -/
theorem sum_cons_ckt_eq_lapCovKRm [T2Space M] (hLC : LCSmooth I M)
    (g : SMet I M) (x : M) (k : ℕ)
    (F : Fin (k + 4) → TField (I := I) (M := M))
    (Ef : Fin (Module.finrank ℝ E) → TField (I := I) (M := M))
    (hF : ∀ r, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (F r))
    (hEf : ∀ m, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (Ef m))
    (hEfx : ∀ m, Ef m x = onFrame g x m) :
    (∑ m, ckt g (k + 2) (Fin.cons (Ef m) (Fin.cons (Ef m) F)) x)
      = lapCovKRm g x k (fun r => F (Fin.castAdd 4 r) x)
          (F (Fin.natAdd k 0) x) (F (Fin.natAdd k 1) x) (F (Fin.natAdd k 2) x)
          (F (Fin.natAdd k 3) x) := by
  refine Finset.sum_congr rfl (fun m _ => ?_)
  set Cm : Fin (k + 2 + 4) → TField (I := I) (M := M) :=
    Fin.cons (Ef m) (Fin.cons (Ef m) F) with hCm
  set V : Fin (k + 2) → TangentSpace I x :=
    Fin.cons (onFrame g x m) (Fin.cons (onFrame g x m)
      (fun r : Fin k => F (Fin.castAdd 4 r) x)) with hV
  set Mk : Fin (k + 2 + 4) → TField (I := I) (M := M) :=
    fun s => smoothExt x (Cm s x) with hMk
  have hCmsm : ∀ s, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (Cm s) := by
    intro s
    rw [hCm]
    refine Fin.cases ?_ ?_ s
    · exact hEf m
    · intro s1
      refine Fin.cases ?_ ?_ s1
      · exact hEf m
      · intro r
        exact hF r
  have hMksm : ∀ s, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (Mk s) := fun s =>
    Work.Diff.GE.smoothExt_cmdiff x (Cm s x)
  have hval : ∀ s, Cm s x = Mk s x := fun s =>
    (Work.Diff.GE.smoothExt_apply x (Cm s x)).symm
  rw [ckt_val_dep_all hLC g (k + 2) x hCmsm hMksm hval]
  rw [ckt_eq_covKRmExt]
  have hP1 : ∀ i : Fin (k + 2), Cm (Fin.castAdd 4 i) x = V i := by
    intro i
    rw [hCm, hV]
    refine Fin.cases ?_ ?_ i
    · exact hEfx m
    · intro i1
      refine Fin.cases ?_ ?_ i1
      · exact hEfx m
      · intro r
        rfl
  have hP2 : ∀ p : Fin 4, Cm (Fin.natAdd (k + 2) p) x = F (Fin.natAdd k p) x := by
    intro p
    rw [hCm]
    fin_cases p <;> rfl
  have hMk1 : (fun i : Fin (k + 2) => Mk (Fin.castAdd 4 i))
      = fun i : Fin (k + 2) => smoothExt x (V i) := by
    funext i
    show smoothExt x (Cm (Fin.castAdd 4 i) x) = smoothExt x (V i)
    rw [hP1 i]
  have hMk2 : ∀ p : Fin 4, Mk (Fin.natAdd (k + 2) p)
      = smoothExt x (F (Fin.natAdd k p) x) := by
    intro p
    show smoothExt x (Cm (Fin.natAdd (k + 2) p) x) = smoothExt x (F (Fin.natAdd k p) x)
    rw [hP2 p]
  rw [hMk1, hMk2 0, hMk2 1, hMk2 2, hMk2 3]
  rfl

/-! ## The target -/

theorem ladderEfDToReact
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (k : ℕ) (hk : 1 ≤ k)
    (h : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (G : ℝ → Submission.Diff.SMet I M) (T : ℝ), Submission.Diff.IsRicciFlow G T →
        ∀ t ∈ Set.Ico 0 T, ∀ x : M,
        ∀ Ef : Fin (Module.finrank ℝ E) → Work.Diff.EXT.TField (I := I) (M := M),
          Work.Diff.EXT.IsFrameNear (I := I) (M := M) (G t) x Ef →
          Work.Diff.EXT.LadderEfD (I := I) (M := M) G t x Ef k j C) :
    Work.Diff.EXT.EvolCompKFixReact (I := I) (M := M) k := by
  obtain ⟨C, hC0, hLad⟩ := h 0
  refine ⟨C, hC0, ?_⟩
  intro G T hflow t ht x u a b c d
  have hLC : LCSmooth I M := Work.EXT.lcSmooth_noBoundary (I := I) (M := M)
  -- the frame field near `x` with the prescribed value at `x`
  obtain ⟨Ef, hEfNear, hEfx⟩ :=
    Work.Diff.EXT.evolX.isFrameNear_exists (I := I) (M := M) (G t) x
  have hEfsm : ∀ m, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (Ef m) := hEfNear.1
  obtain ⟨-, hLbd⟩ := hLad G T hflow t ht x Ef hEfNear
  -- the tuple of tangent vectors and the corresponding smooth `smoothExt`-extensions
  set v : Fin 4 → TangentSpace I x := ![a, b, c, d] with hv
  set w : Fin (k + 4) → TangentSpace I x := Fin.append u v with hw
  set F : Fin (k + 4) → TField (I := I) (M := M) := fun r => smoothExt x (w r) with hFdef
  have hFsm : ∀ r, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (F r) :=
    fun r => Work.Diff.GE.smoothExt_cmdiff x (w r)
  -- the level-`k`, jet-order-`0` ladder bound
  have hb := hLbd (k + 4) rfl w
  have hb' : |reactOpEfD (I := I) (M := M) Ef G t k F x|
      ≤ C * Shape (G t) x k * ∏ r : Fin (k + 4), Real.sqrt ((G t).inner x (w r) (w r)) := hb
  -- the product of the `w`-norms is the product of the `u`- and the `(a,b,c,d)`-norms
  have hprod1 : (∏ r : Fin k,
        Real.sqrt ((G t).inner x (w (Fin.castAdd 4 r)) (w (Fin.castAdd 4 r))))
      = (∏ r : Fin k, Real.sqrt ((G t).inner x (u r) (u r))) := by
    refine Finset.prod_congr rfl (fun r _ => ?_)
    rw [hw, Fin.append_left]
  have hprod2 : (∏ r : Fin 4,
        Real.sqrt ((G t).inner x (w (Fin.natAdd k r)) (w (Fin.natAdd k r))))
      = Real.sqrt ((G t).inner x a a) * Real.sqrt ((G t).inner x b b)
        * Real.sqrt ((G t).inner x c c) * Real.sqrt ((G t).inner x d d) := by
    rw [Fin.prod_univ_four]
    simp only [hw, Fin.append_right, hv, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three]
  have hprod : (∏ r : Fin (k + 4), Real.sqrt ((G t).inner x (w r) (w r)))
      = (∏ r : Fin k, Real.sqrt ((G t).inner x (u r) (u r)))
          * Real.sqrt ((G t).inner x a a) * Real.sqrt ((G t).inner x b b)
          * Real.sqrt ((G t).inner x c c) * Real.sqrt ((G t).inner x d d) := by
    rw [Fin.prod_univ_add, hprod1, hprod2]
    ring
  -- the trace in `Ef` is the rough Laplacian traced in `onFrame (G t) x`
  have htrace : (∑ m, ckt (G t) (k + 2) (Fin.cons (Ef m) (Fin.cons (Ef m) F)) x)
      = lapCovKRm (G t) x k u a b c d := by
    rw [sum_cons_ckt_eq_lapCovKRm (I := I) (M := M) hLC (G t) x k F Ef hFsm hEfsm hEfx]
    have e1 : (fun r : Fin k => F (Fin.castAdd 4 r) x) = u := by
      funext r
      simp only [hFdef, hw, Work.Diff.GE.smoothExt_apply, Fin.append_left]
    have e2 : F (Fin.natAdd k 0) x = a := by
      simp only [hFdef, hw, Work.Diff.GE.smoothExt_apply, Fin.append_right, hv,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
        Matrix.tail_cons, Matrix.cons_val_three]
    have e3 : F (Fin.natAdd k 1) x = b := by
      simp only [hFdef, hw, Work.Diff.GE.smoothExt_apply, Fin.append_right, hv,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
        Matrix.tail_cons, Matrix.cons_val_three]
    have e4 : F (Fin.natAdd k 2) x = c := by
      simp only [hFdef, hw, Work.Diff.GE.smoothExt_apply, Fin.append_right, hv,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
        Matrix.tail_cons, Matrix.cons_val_three]
    have e5 : F (Fin.natAdd k 3) x = d := by
      simp only [hFdef, hw, Work.Diff.GE.smoothExt_apply, Fin.append_right, hv,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
        Matrix.tail_cons, Matrix.cons_val_three]
    rw [e1, e2, e3, e4, e5]
  -- the `s`-slice of the tower is the component of `∇^k Rm`
  have hckts : (fun s => ckt (G s) k F x) = fun s => covKRm (G s) x k u a b c d := by
    funext s
    simp only [hFdef, hw, ckt_append_smoothExt_eq_covKRm (I := I) (M := M), hv,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.cons_val_three]
  have hdw : derivWithin (fun s => ckt (G s) k F x) (Set.Ioi 0) t
      = derivWithin (fun s => covKRm (G s) x k u a b c d) (Set.Ioi 0) t :=
    congrArg (fun f : ℝ → ℝ => derivWithin f (Set.Ioi 0) t) hckts
  -- the reaction traced in `Ef`, at `x`
  have hreact : reactOpEfD (I := I) (M := M) Ef G t k F x
      = derivWithin (fun s => covKRm (G s) x k u a b c d) (Set.Ioi 0) t
        - lapCovKRm (G t) x k u a b c d := by
    simp only [reactOpEfD]
    rw [hdw, htrace]
  -- the derivative exists (Shi's estimate, existence half)
  refine ⟨derivWithin (fun s => covKRm (G s) x k u a b c d) (Set.Ioi 0) t,
    Work.Diff.EXT.covKRm_derivWithin (I := I) (M := M) hflow ht x k u a b c d, ?_⟩
  -- the bound
  have hb2 : |derivWithin (fun s => covKRm (G s) x k u a b c d) (Set.Ioi 0) t
      - lapCovKRm (G t) x k u a b c d|
      ≤ C * (∑ i ∈ Finset.range (k + 1), Real.sqrt (curvNormK (G t) x i)
              * Real.sqrt (curvNormK (G t) x (k - i)))
          * ((∏ r : Fin k, Real.sqrt ((G t).inner x (u r) (u r)))
              * Real.sqrt ((G t).inner x a a) * Real.sqrt ((G t).inner x b b)
              * Real.sqrt ((G t).inner x c c) * Real.sqrt ((G t).inner x d d)) := by
    have h1 := hb'
    rw [hprod] at h1
    rw [← hreact]
    exact h1
  have hfin := (abs_le.mp hb2).2
  linarith

end Work.Diff.EXT
