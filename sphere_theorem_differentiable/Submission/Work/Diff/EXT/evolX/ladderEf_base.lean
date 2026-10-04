import Mathlib
import Submission.Work.Diff.EXT.ladderEfDefs
import Submission.Work.Diff.EXT.towerReactDefs
import Submission.Work.Diff.EXT.reactOpDefs
import Submission.Work.Diff.EXT.reactDefs
import Submission.Work.Diff.EXT.evolX.ladderPlumb
import Submission.Work.Diff.EXT.evolKDefs
import Submission.Work.Diff.GE.EvolA.rmP_evol_fixed
import Submission.Work.Diff.GE.lapRmAt_trace
import Submission.Work.Diff.GE.derivWithin_Ico_zero
import Submission.Work.Diff.EXT.rmP_derivWithin_Ioi

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The base case (`k = 0`) of the reaction ladder, in the `Ef`-frame formulation

The target `Work.Diff.EXT.evolX.ladderEf_base` produces the constant family `C : ℕ → ℝ` of the
level-`0` ladder invariant `Work.Diff.EXT.LadderEfD G t x Ef 0 j (C j)` from the *pointwise*
level-`0` reaction bound `hreact`: for every jet order `j` a constant `C j ≥ 0` bounds the `j`-th
jet of the quadratic reaction `F ↦ reactionFormAt reactionMap (·) (F 0) (F 1) (F 2) (F 3)` by
`C j · Shape (·) j` times the metric norms of the tuple.

The ladder invariant at level `0` is about the *honest* reaction
`reactOpEfD Ef G t 0`: the one-sided time derivative `∂ₜ⁺Rm(G ·)` of the curvature minus the rough
Laplacian traced in the frame **field** `Ef`.  The proof is therefore a reduction to `hreact`, in
three steps.

* **The one-sided curvature evolution on `[0,T)`**: at every `t ∈ [0,T)` the right derivative of
  the fixed-vector curvature component is `ΔRm + reactionMap(Rm)`
  (`Work.Diff.EXT.rmP_derivWithin_Ioi`, proved in the workspaces' `EXT` area; at interior times
  this is `Work.Diff.GE.EvolA.rmP_evol_fixed`, at `t = 0` the mean-value-theorem lemma
  `Work.Diff.GE.derivWithin_Ico_zero` together with the continuity of `rmP` and of
  `ΔRm + reactionMap(Rm)` at `0⁺`).
* **The trace identity**: for a frame field `Ef` which is `G t`-orthonormal *near* `x`, the sum
  `∑ m ∇_{Ef m}∇_{Ef m} Rm` of the second covariant derivatives of the curvature computed through
  the tower `ckt` coincides with the `onFrame`-traced Laplacian `lapRmAt`
  (`sum_ckt_two_eq_lapRmAt'` below, from `Work.Diff.EXT.ckt_eq_covKRmExt`,
  `Work.Diff.GE.cov2Rm_eq_covKRmExt_two` and the frame independence
  `Work.Diff.GE.lapRmAt_trace`).
* **Locality of the jets on smooth tuples** (`jetAll_congr_of_eventuallyEq_smooth'`): the tower
  `ckt` is tensorial only in *smooth* fields, so the identification of the operator
  `reactOpEfD Ef G t 0` with the quadratic reaction holds only on smooth tuples — which is exactly
  what is needed, since the ladder is evaluated on the smooth extensions `smoothExt x ·`.

Combining the first two gives the germ identity `reactOpEfD_zero_eventuallyEq_reaction'`; the third
then transfers the `hreact` bound on the jets of the quadratic reaction to the jets of the honest
reaction.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option maxHeartbeats 800000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.EXT.evolX

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-! ## The two tower levels appearing in the level-`0` reaction -/

/-- **Level two of the tower is `∇²Rm`.**  For globally `C^∞` fields `X`, `Y`, `F 0, …, F 3`, the
tower value `ckt g 2 (X, Y, F 0, …, F 3)` at `x` is the `(0,6)`-tensor `∇²Rm` contracted with the
values of the fields: `Work.Diff.EXT.ckt_eq_covKRmExt` identifies `ckt g 2` with the recursive
`covKRmExt g 2`, and `Work.Diff.GE.cov2Rm_eq_covKRmExt_two` identifies the latter with the explicit
`∇²Rm`. -/
theorem ckt_two_eq_cov2Rm' [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (x : M)
    {X Y : TField (I := I) (M := M)}
    (hX : Work.Diff.GE.SmoothFieldT (I := I) (M := M) X)
    (hY : Work.Diff.GE.SmoothFieldT (I := I) (M := M) Y)
    {F : Fin 4 → TField (I := I) (M := M)}
    (hF : ∀ i, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (F i)) :
    ckt g 2 (Fin.cons X (Fin.cons Y F)) x
      = Work.Diff.GE.cov2Rm g x (X x) (Y x) (F 0 x) (F 1 x) (F 2 x) (F 3 x) := by
  rw [ckt_eq_covKRmExt]
  have htuple : ∀ i : Fin 2,
      ((Fin.cons X (Fin.cons Y F) : Fin 6 → TField (I := I) (M := M)) (Fin.castAdd 4 i))
        = (if i = 0 then X else Y) := by
    intro i
    fin_cases i <;> rfl
  have hslot : ∀ j : Fin 4,
      ((Fin.cons X (Fin.cons Y F) : Fin 6 → TField (I := I) (M := M)) (Fin.natAdd 2 j)) = F j := by
    intro j
    fin_cases j <;> rfl
  simp only [htuple, hslot]
  exact (Work.Diff.GE.cov2Rm_eq_covKRmExt_two (I := I) (M := M) hLC g x hX hY
    (hF 0) (hF 1) (hF 2) (hF 3)).symm

/-- **The rough Laplacian of the curvature traced in an orthonormal frame field.**  If the fields
`Ef m` are smooth and `g`-orthonormal *near* `x`, then the trace
`∑ m ∇_{Ef m}∇_{Ef m}Rm` of the second covariant derivative of the curvature, computed through the
tower, agrees with the `onFrame`-traced Laplacian `Work.Diff.GE.lapRmAt g` near `x`. -/
theorem sum_ckt_two_eq_lapRmAt' [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (x : M)
    {Ef : Fin (Module.finrank ℝ E) → TField (I := I) (M := M)}
    (hEf : ∀ i, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (Ef i))
    (hON : ∀ᶠ y in 𝓝 x, Submission.Diff.IsONFrame g y (fun i => Ef i y))
    {F : Fin 4 → TField (I := I) (M := M)}
    (hF : ∀ i, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (F i)) :
    (fun y : M => ∑ m : Fin (Module.finrank ℝ E),
        ckt g 2 (Fin.cons (Ef m) (Fin.cons (Ef m) F)) y)
      =ᶠ[𝓝 x] (fun y : M =>
        Work.Diff.GE.lapRmAt g y (F 0 y) (F 1 y) (F 2 y) (F 3 y)) := by
  filter_upwards [hON] with y hy
  refine Eq.trans (Finset.sum_congr rfl (fun m _ =>
    ckt_two_eq_cov2Rm' (I := I) (M := M) hLC g y (hEf m) (hEf m) hF)) ?_
  exact (Work.Diff.GE.lapRmAt_trace (I := I) (M := M) hLC g y (fun i => Ef i y) hy
    (F 0 y) (F 1 y) (F 2 y) (F 3 y)).symm

/-! ## Locality of the jets on smooth tuples -/

/-- **Locality of the iterated covariant derivative `jetAll`, restricted to *smooth* tuples.**
The statement of `Work.Diff.EXT.evolX.jetAll_congr_of_eventuallyEq` quantifies over *all* tuples of
fields; for operators built from the tower `ckt` the value is tensorial only on smooth fields, so
the honest statement is the restricted one: if two packed operators agree near `x` on every *smooth*
tuple, then their `j`-th jets at `x` agree on every smooth tuple.  The proof is the induction of
`Work.Diff.EXT.evolX.jetAll_eventuallyEq_of_eventuallyEq`, with the smoothness of the Leibniz
corrections `Function.update G s (dirF g (G s) (G 0))` supplied by `Work.Diff.EXT.smoothF_update`
and `Work.Diff.EXT.dirF_smooth`. -/
theorem jetAll_eventuallyEq_of_eventuallyEq_smooth' [T2Space M] {g : Submission.Diff.SMet I M}
    (hLC : Submission.Diff.LCSmooth I M) :
    ∀ (j : ℕ) (K : ℕ)
      (S S' : (Fin K → TField (I := I) (M := M)) → M → ℝ) (x : M),
      (∀ F, (∀ i, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (F i)) → S F =ᶠ[𝓝 x] S' F) →
      ∀ G : Fin (K + j) → TField (I := I) (M := M),
        (∀ i, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (G i)) →
        jetAll g j K S G =ᶠ[𝓝 x] jetAll g j K S' G := by
  intro j
  induction j with
  | zero =>
      intro K S S' x h G hG
      exact h G hG
  | succ l ih =>
      intro K S S' x h G hG
      simp only [jetAll]
      simp only [extStep, Pi.sub_apply, Finset.sum_apply]
      have hmv : ∀ᶠ y in 𝓝 x,
          mvfderiv I (fun y' : M => jetAll g l K S (fun i : Fin (K + l) => G i.succ) y') y
            (G 0 y)
          = mvfderiv I (fun y' : M => jetAll g l K S' (fun i : Fin (K + l) => G i.succ) y') y
            (G 0 y) := by
        filter_upwards [mvfderiv_eventuallyEq_of_eventuallyEq (I := I)
          (ih K S S' x h (fun i : Fin (K + l) => G i.succ) (fun i => hG i.succ))] with y hy
        exact congrArg (fun L : TangentSpace I y →L[ℝ] ℝ => L (G 0 y)) hy
      have hcorr : ∀ᶠ y in 𝓝 x, ∀ s : Fin (K + l),
          jetAll g l K S
              (Function.update (fun i : Fin (K + l) => G i.succ) s
                (dirF g ((fun i : Fin (K + l) => G i.succ) s) (G 0))) y
            = jetAll g l K S'
              (Function.update (fun i : Fin (K + l) => G i.succ) s
                (dirF g ((fun i : Fin (K + l) => G i.succ) s) (G 0))) y :=
        Filter.eventually_all.mpr fun s =>
          ih K S S' x h _
            (smoothF_update (G := fun i : Fin (K + l) => G i.succ)
              (fun i => hG i.succ)
              (dirF_smooth (I := I) (M := M) hLC g (hG s.succ) (hG 0)))
      filter_upwards [hmv, hcorr] with y hy1 hy2
      rw [hy1, Finset.sum_congr rfl (fun s _ => hy2 s)]

/-- Locality of the jets at a point, smooth-tuple form. -/
theorem jetAll_congr_of_eventuallyEq_smooth' [T2Space M] {g : Submission.Diff.SMet I M} {K j : ℕ}
    (hLC : Submission.Diff.LCSmooth I M)
    {S S' : (Fin K → TField (I := I) (M := M)) → M → ℝ} {x : M}
    (h : ∀ F, (∀ i, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (F i)) →
      S F =ᶠ[𝓝 x] S' F)
    (G : Fin (K + j) → TField (I := I) (M := M))
    (hG : ∀ i, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (G i)) :
    jetAll g j K S G x = jetAll g j K S' G x :=
  (jetAll_eventuallyEq_of_eventuallyEq_smooth' (I := I) (M := M) hLC j K S S' x h G hG).eq_of_nhds

/-! ## The germ of the level-`0` reaction is the quadratic reaction -/

/-- **The germ identity for the level-`0` reaction.**  For a Ricci flow `G` on `[0,T)`, `t ∈ [0,T)`,
a point `x` and a family `Ef` of smooth fields which is `G t`-orthonormal near `x`, the level-`0`
reaction operator `Work.Diff.EXT.reactOpEfD Ef G t 0` (the one-sided time derivative of the
curvature minus the rough Laplacian traced in the frame field `Ef`) agrees, near `x`, with the
quadratic reaction `reactionFormAt reactionMap`: this is the fixed-vector curvature evolution
(`Work.Diff.EXT.rmP_derivWithin_Ioi`) together with the trace identity `sum_ckt_two_eq_lapRmAt'`. -/
theorem reactOpEfD_zero_eventuallyEq_reaction' [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : Submission.Diff.LCSmooth I M) (hLV : Submission.Diff.LCVariation I M)
    {G : ℝ → Submission.Diff.SMet I M} {T : ℝ} (hflow : Submission.Diff.IsRicciFlow G T)
    {t : ℝ} (ht : t ∈ Set.Ico 0 T) {x : M}
    {Ef : Fin (Module.finrank ℝ E) → TField (I := I) (M := M)}
    (hEf : ∀ i, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (Ef i))
    (hON : ∀ᶠ y in 𝓝 x, Submission.Diff.IsONFrame (G t) y (fun i => Ef i y))
    {F : Fin 4 → TField (I := I) (M := M)}
    (hF : ∀ i, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (F i)) :
    (fun y : M => reactOpEfD (I := I) (M := M) Ef G t 0 F y)
      =ᶠ[𝓝 x] (fun y : M => Work.Diff.GE.reactionFormAt Work.Diff.GE.reactionMap (G t) y
        (F 0 y) (F 1 y) (F 2 y) (F 3 y)) := by
  filter_upwards [sum_ckt_two_eq_lapRmAt' (I := I) (M := M) hLC (G t) x hEf hON hF] with y htrace
  show derivWithin (fun s : ℝ => ckt (G s) 0 F y) (Set.Ioi 0) t
      - (∑ m : Fin (Module.finrank ℝ E),
          ckt (G t) 2 (Fin.cons (Ef m) (Fin.cons (Ef m) F)) y)
      = Work.Diff.GE.reactionFormAt Work.Diff.GE.reactionMap (G t) y
          (F 0 y) (F 1 y) (F 2 y) (F 3 y)
  have hderiv : derivWithin (fun s : ℝ => ckt (G s) 0 F y) (Set.Ioi 0) t
      = Work.Diff.GE.lapRmAt (G t) y (F 0 y) (F 1 y) (F 2 y) (F 3 y)
        + Work.Diff.GE.reactionFormAt Work.Diff.GE.reactionMap (G t) y
            (F 0 y) (F 1 y) (F 2 y) (F 3 y) := by
    show derivWithin (fun s : ℝ => Submission.Diff.rmP (G s) y
        (F 0 y) (F 1 y) (F 2 y) (F 3 y)) (Set.Ioi 0) t = _
    have huniq : UniqueDiffWithinAt ℝ (Set.Ioi 0) t := by
      rcases eq_or_lt_of_le ht.1 with h0 | hpos
      · subst h0
        exact uniqueDiffWithinAt_Ioi 0
      · exact uniqueDiffWithinAt_of_mem_nhds (Ioi_mem_nhds hpos)
    exact (Work.Diff.EXT.rmP_derivWithin_Ioi (I := I) (M := M) hLC hLV G T hflow t ht y
      (F 0 y) (F 1 y) (F 2 y) (F 3 y)).derivWithin huniq
  rw [hderiv, htrace]
  ring

/-! ## The base case of the ladder -/

theorem ladderEf_base
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : Submission.Diff.LCSmooth I M) (hLV : Submission.Diff.LCVariation I M)
    (hreact : ∀ j, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (g : Submission.Diff.SMet I M) (x : M)
        (G : Fin (4 + j) → Work.Diff.EXT.TField (I := I) (M := M)),
        (∀ i, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (G i)) →
        |Work.Diff.EXT.jetAll g j 4
            (fun (F : Fin 4 → Work.Diff.EXT.TField (I := I) (M := M)) => fun (y : M) =>
              Work.Diff.GE.reactionFormAt Work.Diff.GE.reactionMap g y (F 0 y) (F 1 y) (F 2 y) (F 3 y))
            G x|
          ≤ C * Work.Diff.EXT.Shape g x j
              * ∏ r : Fin (4 + j), Real.sqrt (g.inner x (G r x) (G r x))) :
    ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧
      ∀ (G : ℝ → Submission.Diff.SMet I M) (T : ℝ), Submission.Diff.IsRicciFlow G T →
        ∀ t ∈ Set.Ico 0 T, ∀ x : M,
        ∀ Ef : Fin (Module.finrank ℝ E) → Work.Diff.EXT.TField (I := I) (M := M),
          Work.Diff.EXT.IsFrameNear (G t) x Ef →
          ∀ j, Work.Diff.EXT.LadderEfD G t x Ef 0 j (C j) := by
  choose C hC using hreact
  refine ⟨C, fun j => (hC j).1, ?_⟩
  intro G T hflow t ht x Ef hEf j
  refine ⟨(hC j).1, ?_⟩
  intro N hN w
  subst hN
  -- the tuple of the smooth extensions of the evaluated vectors
  have hGs : ∀ i, Work.Diff.GE.SmoothFieldT (I := I) (M := M)
      ((fun r : Fin (4 + j) => Submission.Diff.smoothExt x (w (Fin.cast rfl.symm r))) i) :=
    fun i => Work.Diff.GE.smoothExt_cmdiff x _
  -- the jets of the honest reaction at `x` are those of the quadratic reaction
  have hjet : jetAll (G t) j 4 (reactOpEfD (I := I) (M := M) Ef G t 0)
      (fun r : Fin (4 + j) => Submission.Diff.smoothExt x (w (Fin.cast rfl.symm r))) x
      = jetAll (G t) j 4
        (fun (F : Fin 4 → TField (I := I) (M := M)) => fun (y : M) =>
          Work.Diff.GE.reactionFormAt Work.Diff.GE.reactionMap (G t) y
            (F 0 y) (F 1 y) (F 2 y) (F 3 y))
        (fun r : Fin (4 + j) => Submission.Diff.smoothExt x (w (Fin.cast rfl.symm r))) x := by
    refine jetAll_congr_of_eventuallyEq_smooth' (I := I) (M := M) hLC ?_ _ hGs
    intro F hF
    exact reactOpEfD_zero_eventuallyEq_reaction' (I := I) (M := M) hLC hLV hflow ht
      hEf.1 hEf.2 hF
  rw [hjet]
  -- the `hreact` bound on the jets of the quadratic reaction, reindexed along `w`
  refine le_trans ((hC j).2 (G t) x
    (fun r : Fin (4 + j) => Submission.Diff.smoothExt x (w (Fin.cast rfl.symm r))) hGs)
    (le_of_eq ?_)
  have hprod : (∏ r : Fin (4 + j), Real.sqrt ((G t).inner x
        (Submission.Diff.smoothExt x (w (Fin.cast rfl.symm r)) x)
        (Submission.Diff.smoothExt x (w (Fin.cast rfl.symm r)) x)))
      = ∏ r : Fin (4 + j), Real.sqrt ((G t).inner x (w r) (w r)) := by
    refine Finset.prod_congr rfl (fun r _ => ?_)
    simp only [Work.Diff.GE.smoothExt_apply, Fin.cast_eq_self]
  rw [hprod, show (0 : ℕ) + j = j from Nat.zero_add j]

end Work.Diff.EXT.evolX
