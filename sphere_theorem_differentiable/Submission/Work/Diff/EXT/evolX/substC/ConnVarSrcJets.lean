import Mathlib
import Submission.Work.Diff.EXT.evolX.connVarDefs
import Submission.Work.Diff.EXT.ladderSrcDefs
import Submission.Work.Diff.EXT.ladderEfDefs
import Submission.Work.Diff.EXT.jetSmoothDefs
import Submission.Work.Diff.EXT.ckt_step_tderiv
import Submission.Work.Diff.GE.curv_var_prelim
import Submission.Work.Diff.T.lc_variation
import Submission.Work.Diff.Evol.cv_dLC
import Submission.Work.Diff.EXT.evolX.opJetSmooth_dtOpD
import Submission.Work.Diff.EXT.evolX.substC.ConnVarOpJets
import Submission.Work.Diff.EXT.evolX.srcConnVar_continuousAt_zero
import Submission.Work.Diff.EXT.evolX.shape_prod_continuousWithinAt_zero

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

/-!
# `connVarSrcJets` (copy of the W-chain version)

Part of the independent chain `substC.Assembly` → `substC.ConnVarOpJets` → `substC.ConnVarSrcJets`
→ `substC.LadderStep` → `substC.ReactAll` feeding `Work.Diff.EXT.evolK_of_flow`.
-/

namespace Work.Diff.EXT.evolX

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  [I.Boundaryless] [T2Space M]

/-! ## The connection-variation source as an operator

The connection-variation source of the ladder step,
`srcConnvar = dtOpD G t (k+1) − extStep (G t) (dtOpD G t k)`, is *equal*, near the base point and
for every smooth tuple, to the operator `connVarOp G t k` which inserts the first variation of the
Levi-Civita connection `dLC G t` into the level-`k` curvature tower. -/

/-- **The operator identity of the connection-variation source.**  For an interior time
`t ∈ Ioo 0 T`, every base point and every tuple `F` of globally smooth fields, the difference
`dtOpD G t (k+1) F − extStep (G t) (dtOpD G t k) F` is (the negative of) the connection-variation
operator: it is obtained from the one-step time derivative of the tower
(`Work.Diff.EXT.ckt_step_tderiv`, whose connection-variation vector is identified with `dLC` through
`dLC_pairing` + `variation_algebra`) and the single-slot value dependence of the tower
(`ckt_val_dep`, which replaces the pointwise extension by the globally smooth field `dLC`). -/
theorem dtOpD_succ_eqC [T2Space M]
    (hLC : LCSmooth I M) (hLV : LCVariation I M)
    {G : ℝ → Submission.Diff.SMet I M} {T : ℝ} (hflow : IsRicciFlow G T)
    {t : ℝ} (ht : t ∈ Set.Ioo 0 T) (k : ℕ) (x : M)
    (F : Fin (k + 5) → TField (I := I) (M := M)) (hF : ∀ i, SmoothF (F i)) :
    (fun y => dtOpD (I := I) (M := M) G t (k + 1) F y)
      =ᶠ[𝓝 x]
    (fun y => extStep (I := I) (M := M) (G t) (dtOpD (I := I) (M := M) G t k) F y
      + connVarOp (I := I) (M := M) G t k F y) := by
  classical
  have ht0 : 0 < t := ht.1
  have hIoi : Set.Ioi (0 : ℝ) ∈ 𝓝 t := isOpen_Ioi.mem_nhds ht0
  have hJopen : IsOpen (Set.Ioo (0 : ℝ) T) := isOpen_Ioo
  have hJs : Submission.Diff.JointSmooth G (Set.Ioo (0 : ℝ) T) :=
    hflow.1.mono (Set.prod_mono Set.Ioo_subset_Ico_self (subset_refl _))
  have hF' : ∀ i : Fin (k + 4), SmoothF ((fun i : Fin (k + 4) => F i.succ) i) :=
    fun i => hF i.succ
  -- the inserted field `dLC G t (F 0) (F' s)` is globally smooth
  have hWs : ∀ s : Fin (k + 4),
      SmoothF (Submission.Diff.dLC G t (F 0) ((fun i : Fin (k + 4) => F i.succ) s)) :=
    fun s => fun y => Work.Diff.Evol.cv_dLC_smooth (I := I) (M := M) hLC hLV hJopen hJs ht
      (F 0) ((fun i : Fin (k + 4) => F i.succ) s) (hF 0) (hF' s) y
  filter_upwards with y
  -- the pairing identity characterising the connection-variation vector
  have hAv : ∀ (s : Fin (k + 4)) (Z : TField (I := I) (M := M)), SmoothF Z →
      (G t).inner y (Submission.Diff.dLC G t (F 0)
          ((fun i : Fin (k + 4) => F i.succ) s) y) (Z y)
        = (1 / 2 : ℝ) *
            (Submission.Diff.covDerivSym2 (Submission.Diff.lcOf (G t)) (Submission.Diff.dtMet G t)
                (F 0) ((fun i : Fin (k + 4) => F i.succ) s) Z y
              + Submission.Diff.covDerivSym2 (Submission.Diff.lcOf (G t))
                (Submission.Diff.dtMet G t) ((fun i : Fin (k + 4) => F i.succ) s) (F 0) Z y
              - Submission.Diff.covDerivSym2 (Submission.Diff.lcOf (G t))
                (Submission.Diff.dtMet G t) Z (F 0) ((fun i : Fin (k + 4) => F i.succ) s) y) := by
    intro s Z hZ
    have hp := Work.Diff.GE.dLC_pairing (I := I) (M := M) hLV hJopen hJs ht
      (Y := F 0) (Z := (fun i : Fin (k + 4) => F i.succ) s) (W := Z) (hF 0) (hF' s) hZ y
    have hv := Work.Diff.T.variation_algebra (I := I) (M := M) (G := G) hJopen hJs ht
      (x := y) (F 0) ((fun i : Fin (k + 4) => F i.succ) s) Z (hF 0) (hF' s) hZ
    linarith [hp, hv]
  -- the one-step time derivative of the tower at `y`
  have hder := ckt_step_tderiv (I := I) (M := M) hLC hLV hflow ht F hF y
    (Av := fun s => Submission.Diff.dLC G t (F 0) ((fun i : Fin (k + 4) => F i.succ) s) y) hAv
  -- rewrite `dtOpD` as a two-sided derivative (interior time) and use `hder`
  have hdw : derivWithin (fun s : ℝ => ckt (G s) (k + 1) F y) (Set.Ioi 0) t
      = deriv (fun s : ℝ => ckt (G s) (k + 1) F y) t := derivWithin_of_mem_nhds hIoi
  rw [dtOpD, hdw, hder.deriv]
  simp only [extStep, dirF, connVarOp, Pi.sub_apply]
  -- identify the two-sided derivatives with `dtOpD`
  have hid1 : mvfderiv I (fun y' : M => deriv
        (fun s : ℝ => ckt (G s) k (fun i : Fin (k + 4) => F i.succ) y') t) y (F 0 y)
      = mvfderiv I (fun y' : M => dtOpD (I := I) (M := M) G t k
          (fun i : Fin (k + 4) => F i.succ) y') y (F 0 y) := by
    have hfun : (fun y' : M => deriv
          (fun s : ℝ => ckt (G s) k (fun i : Fin (k + 4) => F i.succ) y') t)
        = fun y' : M => dtOpD (I := I) (M := M) G t k
            (fun i : Fin (k + 4) => F i.succ) y' := by
      funext y'
      rw [dtOpD, derivWithin_of_mem_nhds hIoi]
    rw [hfun]
  have hid2 : ∀ s : Fin (k + 4),
      deriv (fun s' : ℝ => ckt (G s') k
          (Function.update (fun i : Fin (k + 4) => F i.succ) s
            (fun z : M => Submission.Diff.lcOf (G t)
              ((fun i : Fin (k + 4) => F i.succ) s) z (F 0 z))) y) t
        = dtOpD (I := I) (M := M) G t k
            (Function.update (fun i : Fin (k + 4) => F i.succ) s
              (fun z : M => Submission.Diff.lcOf (G t)
                ((fun i : Fin (k + 4) => F i.succ) s) z (F 0 z))) y := by
    intro s
    rw [dtOpD, derivWithin_of_mem_nhds hIoi]
  have hid3 : ∀ s : Fin (k + 4),
      ckt (G t) k (Function.update (fun i : Fin (k + 4) => F i.succ) s
          (fun z : M => Submission.Diff.smoothExt y
            (Submission.Diff.dLC G t (F 0) ((fun i : Fin (k + 4) => F i.succ) s) y) z)) y
        = ckt (G t) k (Function.update (fun i : Fin (k + 4) => F i.succ) s
            (Submission.Diff.dLC G t (F 0) ((fun i : Fin (k + 4) => F i.succ) s))) y := by
    intro s
    refine ckt_val_dep (I := I) (M := M) hLC (G t) k y hF' s
      (Work.Diff.GE.smoothExt_cmdiff y _) (hWs s) ?_
    simp only [Work.Diff.GE.smoothExt_apply]
  rw [hid1, Finset.sum_congr rfl (fun s _ => hid2 s), Finset.sum_congr rfl (fun s _ => hid3 s)]
  have hdir : ∀ s : Fin (k + 4), dirF (G t) ((fun i : Fin (k + 4) => F i.succ) s) (F 0)
      = (fun z : M => Submission.Diff.lcOf (G t)
          ((fun i : Fin (k + 4) => F i.succ) s) z (F 0 z)) := fun s => rfl
  simp only [hdir]
  ring

/-! ## Locality of the jets for smooth tuples

The statement of `Work.Diff.EXT.evolX.jetAll_congr_of_eventuallyEq` quantifies over *all* tuples of
fields; for operators built from the tower `ckt` the value is tensorial only on smooth fields, so
the honest statement is the restricted one: if two packed operators agree near `x` on every *smooth*
tuple, then their `j`-th jets at `x` agree on every smooth tuple.  (This is the smooth-tuple
locality, reproduced here so that the reduction below does not depend on the module
`Work.Diff.EXT.ladderEfD_base`, whose import closure is under construction.) -/

/-- **Locality of the iterated covariant derivative `jetAll`, restricted to smooth tuples.** -/
theorem jetAll_eventuallyEq_of_eventuallyEq_smoothC [T2Space M] {g : Submission.Diff.SMet I M}
    (hLC : Submission.Diff.LCSmooth I M) :
    ∀ (j : ℕ) (K : ℕ)
      (S S' : (Fin K → TField (I := I) (M := M)) → M → ℝ) (x : M),
      (∀ F, (∀ i, SmoothF (F i)) → S F =ᶠ[𝓝 x] S' F) →
      ∀ G : Fin (K + j) → TField (I := I) (M := M),
        (∀ i, SmoothF (G i)) →
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
            (smoothF_update' (fun i => hG i.succ) s
              (dirF_smooth (I := I) (M := M) hLC g (hG s.succ) (hG 0)))
      filter_upwards [hmv, hcorr] with y hy1 hy2
      rw [hy1, Finset.sum_congr rfl (fun s _ => hy2 s)]

/-- **Locality of the jets at a point, smooth-tuple form.** -/
theorem jetAll_congr_of_eventuallyEq_smoothC' [T2Space M] {g : Submission.Diff.SMet I M} {K j : ℕ}
    (hLC : Submission.Diff.LCSmooth I M)
    {S S' : (Fin K → TField (I := I) (M := M)) → M → ℝ} {x : M}
    (h : ∀ F, (∀ i, SmoothF (F i)) → S F =ᶠ[𝓝 x] S' F)
    (G : Fin (K + j) → TField (I := I) (M := M))
    (hG : ∀ i, SmoothF (G i)) :
    jetAll g j K S G x = jetAll g j K S' G x :=
  (jetAll_eventuallyEq_of_eventuallyEq_smoothC (I := I) (M := M) hLC j K S S' x h G hG).eq_of_nhds

/-! ## Reduction of the target to the connection-variation operator -/

/-- **`JetSmoothOp` is preserved by the `extStep` recursion**: if all the jets of a packed operator
`S` are mdifferentiable near `x`, then so are those of `extStep g S` (its `l`-th jet is the
`(l+1)`-st jet of `S` up to the canonical reindexing of the tuple). -/
theorem jetSmoothOp_extStepC [T2Space M] {g : Submission.Diff.SMet I M} {K : ℕ}
    {S : (Fin K → TField (I := I) (M := M)) → M → ℝ} {x : M}
    (h : JetSmoothOp (I := I) (M := M) g K S x) :
    JetSmoothOp (I := I) (M := M) g (K + 1)
      (extStep (I := I) (M := M) g S) x := by
  filter_upwards [h] with y hy
  intro l F hF
  have hfun : (fun z : M => jetAll g l (K + 1) (extStep (I := I) (M := M) g S) F z)
      = fun z : M => jetAll g (l + 1) K S
          (fun r : Fin (K + (l + 1)) => F (Fin.cast (by omega : K + (l + 1) = (K + 1) + l) r)) z := by
    funext z
    exact (jetAll_extStep (I := I) (M := M) g l K S F z).symm
  rw [hfun]
  exact hy (l + 1) _ (fun i => hF _)

/-- **The target's left-hand side is the jet of the connection-variation operator** (interior time,
canonical tuples).  The two ingredients are the operator identity `dtOpD_succ_eq` and the linearity
of `jetAll` on differences (`jetAll_sub_of_JetSmoothOp`, whose hypothesis `JetSmoothOp` holds for
`dtOpD` by `Work.Diff.EXT.evolX.opJetSmooth_dtOpD` and hence for its `extStep`). -/
theorem srcJet_eqC [T2Space M] [CompactSpace M]
    (hLC : LCSmooth I M) (hLV : LCVariation I M)
    {G : ℝ → Submission.Diff.SMet I M} {T : ℝ} (hflow : IsRicciFlow G T)
    {t : ℝ} (ht : t ∈ Set.Ioo 0 T) (k j : ℕ) (x : M)
    (F : Fin ((k + 5) + j) → TField (I := I) (M := M)) (hF : ∀ i, SmoothF (F i)) :
    jetAll (G t) j (k + 5) (dtOpD (I := I) (M := M) G t (k + 1)) F x
      - jetAll (G t) j (k + 5)
          (extStep (I := I) (M := M) (G t) (dtOpD (I := I) (M := M) G t k)) F x
      = jetAll (G t) j (k + 5) (connVarOp (I := I) (M := M) G t k) F x := by
  have ht' : t ∈ Set.Ico 0 T := ⟨le_of_lt ht.1, ht.2⟩
  have hsm : JetSmoothOp (I := I) (M := M) (G t) (k + 5)
      (dtOpD (I := I) (M := M) G t (k + 1)) x :=
    opJetSmooth_dtOpD (I := I) (M := M) (k + 1) G T hflow t ht' x
  have hsm' : JetSmoothOp (I := I) (M := M) (G t) (k + 5)
      (extStep (I := I) (M := M) (G t) (dtOpD (I := I) (M := M) G t k)) x :=
    jetSmoothOp_extStepC (I := I) (M := M)
      (opJetSmooth_dtOpD (I := I) (M := M) k G T hflow t ht' x)
  have hsub := (jetAll_sub_of_JetSmoothOp (I := I) (M := M) (g := G t) (K := k + 5)
      (S := dtOpD (I := I) (M := M) G t (k + 1))
      (S' := extStep (I := I) (M := M) (G t) (dtOpD (I := I) (M := M) G t k))
      x hsm hsm') j F hF
  have hcongr : jetAll (G t) j (k + 5)
        (dtOpD (I := I) (M := M) G t (k + 1)
          - extStep (I := I) (M := M) (G t) (dtOpD (I := I) (M := M) G t k)) F x
      = jetAll (G t) j (k + 5) (connVarOp (I := I) (M := M) G t k) F x :=
    jetAll_congr_of_eventuallyEq_smoothC' (I := I) (M := M) hLC (K := k + 5) (j := j)
      (S := dtOpD (I := I) (M := M) G t (k + 1)
        - extStep (I := I) (M := M) (G t) (dtOpD (I := I) (M := M) G t k))
      (S' := connVarOp (I := I) (M := M) G t k) (x := x)
      (fun F' hF' => by
        filter_upwards [dtOpD_succ_eqC (I := I) (M := M) hLC hLV hflow ht k x F' hF'] with y hy
        simp only [Pi.sub_apply]
        rw [hy]; ring)
      F hF
  rw [← hsub.eq_of_nhds, hcongr]

/-- **The positive-time case of the target**: for `0 < t` the bound follows from the reduction
`srcJet_eq` and the jet bound for the connection-variation operator (`connVarOp_jets`). -/
theorem srcJet_bound_posC [T2Space M] [CompactSpace M] (k j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (G : ℝ → Submission.Diff.SMet I M) (T : ℝ), Submission.Diff.IsRicciFlow G T →
        ∀ t ∈ Set.Ico 0 T, 0 < t → ∀ x : M,
        ∀ (N : ℕ) (h1 : (k + 1 + 4) + j = N) (h2 : (k + 4) + (j + 1) = N)
          (w : Fin N → TangentSpace I x),
          |jetAll (G t) j (k + 1 + 4) (dtOpD (I := I) (M := M) G t (k + 1))
              (fun r : Fin ((k + 1 + 4) + j) => Submission.Diff.smoothExt x (w (Fin.cast h1 r))) x
            - jetAll (G t) (j + 1) (k + 4) (dtOpD (I := I) (M := M) G t k)
              (fun r : Fin ((k + 4) + (j + 1)) => Submission.Diff.smoothExt x (w (Fin.cast h2 r))) x|
          ≤ C * Shape (G t) x ((k + 1) + j)
              * Finset.univ.prod (fun r : Fin N => Real.sqrt ((G t).inner x (w r) (w r))) := by
  obtain ⟨C, hC, hbound⟩ := connVarOp_jetsC (I := I) (M := M) k j
  refine ⟨C, hC, ?_⟩
  intro G T hflow t ht ht0 x N h1 h2 w
  have hLC : LCSmooth I M := Work.EXT.lcSmooth_noBoundary (I := I) (M := M)
  have hLV : LCVariation I M := Work.Diff.T.lc_variation hLC
  have ht' : t ∈ Set.Ioo 0 T := ⟨ht0, ht.2⟩
  -- the canonical smooth tuple
  have hF : ∀ i : Fin ((k + 5) + j), SmoothF
      ((fun r : Fin ((k + 5) + j) => Submission.Diff.smoothExt x
        (w (Fin.cast (by omega : (k + 5) + j = N) r))) i) :=
    fun i => Work.Diff.GE.smoothExt_cmdiff x _
  -- the two tuples of the target, in canonical form
  have e1 : (fun r : Fin ((k + 1 + 4) + j) => Submission.Diff.smoothExt x (w (Fin.cast h1 r)))
      = (fun r : Fin ((k + 5) + j) => Submission.Diff.smoothExt x
          (w (Fin.cast (by omega : (k + 5) + j = N) r))) := by
    funext r
    congr 1
  have e2 : (fun r : Fin ((k + 4) + (j + 1)) => Submission.Diff.smoothExt x (w (Fin.cast h2 r)))
      = (fun r : Fin ((k + 4) + (j + 1)) => (fun r' : Fin ((k + 5) + j) =>
            Submission.Diff.smoothExt x (w (Fin.cast (by omega : (k + 5) + j = N) r')))
          (Fin.cast (by omega : (k + 4) + (j + 1) = ((k + 4) + 1) + j) r)) := by
    funext r
    congr 1
  rw [e1, e2]
  -- the second jet is the jet of the `extStep`
  rw [jetAll_extStep (I := I) (M := M) (G t) j (k + 4) (dtOpD (I := I) (M := M) G t k)
    (fun r : Fin ((k + 5) + j) => Submission.Diff.smoothExt x
      (w (Fin.cast (by omega : (k + 5) + j = N) r))) x]
  -- the operator identity
  rw [srcJet_eqC (I := I) (M := M) hLC hLV hflow ht' k j x
    (fun r : Fin ((k + 5) + j) => Submission.Diff.smoothExt x
      (w (Fin.cast (by omega : (k + 5) + j = N) r))) hF]
  -- the jet bound for `connVarOp`
  refine le_trans (hbound G T hflow t ht' x
    (fun r : Fin ((k + 5) + j) => Submission.Diff.smoothExt x
      (w (Fin.cast (by omega : (k + 5) + j = N) r))) hF) ?_
  -- reindexing of the product
  have hprod : (∏ r : Fin ((k + 5) + j), Real.sqrt ((G t).inner x
        ((fun r' : Fin ((k + 5) + j) => Submission.Diff.smoothExt x
          (w (Fin.cast (by omega : (k + 5) + j = N) r'))) r x)
        ((fun r' : Fin ((k + 5) + j) => Submission.Diff.smoothExt x
          (w (Fin.cast (by omega : (k + 5) + j = N) r'))) r x)))
      = ∏ r : Fin N, Real.sqrt ((G t).inner x (w r) (w r)) := by
    refine Fintype.prod_bijective (finCongr (by omega : (k + 5) + j = N))
      (finCongr (by omega : (k + 5) + j = N)).bijective _ _ (fun r => ?_)
    simp only [finCongr_apply, Work.Diff.GE.smoothExt_apply]
  rw [hprod]

theorem connVarSrcJetsC
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (k j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (G : ℝ → Submission.Diff.SMet I M) (T : ℝ), Submission.Diff.IsRicciFlow G T →
        ∀ t ∈ Set.Ico 0 T, ∀ x : M,
        ∀ Ef : Fin (Module.finrank ℝ E) → Work.Diff.EXT.TField (I := I) (M := M),
          Work.Diff.EXT.IsFrameNear (I := I) (M := M) (G t) x Ef →
        ∀ (N : ℕ) (h1 : (k + 1 + 4) + j = N) (h2 : (k + 4) + (j + 1) = N)
          (w : Fin N → TangentSpace I x),
          |Work.Diff.EXT.jetAll (G t) j (k + 1 + 4)
              (Work.Diff.EXT.dtOpD (I := I) (M := M) G t (k + 1))
              (fun r : Fin ((k + 1 + 4) + j) => Submission.Diff.smoothExt x (w (Fin.cast h1 r))) x
            - Work.Diff.EXT.jetAll (G t) (j + 1) (k + 4)
              (Work.Diff.EXT.dtOpD (I := I) (M := M) G t k)
              (fun r : Fin ((k + 4) + (j + 1)) => Submission.Diff.smoothExt x (w (Fin.cast h2 r))) x|
          ≤ C * Work.Diff.EXT.Shape (G t) x ((k + 1) + j)
              * Finset.univ.prod (fun r : Fin N => Real.sqrt ((G t).inner x (w r) (w r))) := by
  obtain ⟨C, hC, hpos⟩ := srcJet_bound_posC (I := I) (M := M) k j
  refine ⟨C, hC, ?_⟩
  intro G T hflow t ht x Ef hEf N h1 h2 w
  rcases lt_or_eq_of_le ht.1 with ht0 | ht_eq
  · -- positive time: the reduction + the jet bound for `connVarOp`
    exact hpos G T hflow t ht ht0 x N h1 h2 w
  · -- `t = 0`: pass to the limit from the right
    subst ht_eq
    -- the smoothness of the two tuples
    have hF₁ : ∀ i, Work.Diff.EXT.SmoothF (I := I) (M := M)
        ((fun r : Fin ((k + 1 + 4) + j) =>
          Submission.Diff.smoothExt x (w (Fin.cast h1 r))) i) :=
      fun i => Work.Diff.GE.smoothExt_cmdiff x _
    have hF₂ : ∀ i, Work.Diff.EXT.SmoothF (I := I) (M := M)
        ((fun r : Fin ((k + 4) + (j + 1)) =>
          Submission.Diff.smoothExt x (w (Fin.cast h2 r))) i) :=
      fun i => Work.Diff.GE.smoothExt_cmdiff x _
    by_cases hT : 0 < T
    · -- the bound for positive times
      have hev : ∀ᶠ s in 𝓝[Set.Ioo (0 : ℝ) T] 0,
          |Work.Diff.EXT.jetAll (G s) j (k + 1 + 4)
                (Work.Diff.EXT.dtOpD (I := I) (M := M) G s (k + 1))
                (fun r : Fin ((k + 1 + 4) + j) =>
                  Submission.Diff.smoothExt x (w (Fin.cast h1 r))) x
              - Work.Diff.EXT.jetAll (G s) (j + 1) (k + 4)
                (Work.Diff.EXT.dtOpD (I := I) (M := M) G s k)
                (fun r : Fin ((k + 4) + (j + 1)) =>
                  Submission.Diff.smoothExt x (w (Fin.cast h2 r))) x|
            ≤ C * (Work.Diff.EXT.Shape (G s) x ((k + 1) + j)
                * Finset.univ.prod
                    (fun r : Fin N => Real.sqrt ((G s).inner x (w r) (w r)))) := by
        filter_upwards [self_mem_nhdsWithin] with s hs
        have hsIco : s ∈ Set.Ico 0 T := ⟨le_of_lt hs.1, hs.2⟩
        simpa only [mul_assoc] using hpos G T hflow s hsIco hs.1 x N h1 h2 w
      -- continuity of the two sides at `0`
      have hle : 𝓝[Set.Ioo (0 : ℝ) T] 0 ≤ 𝓝[Set.Ico 0 T] 0 :=
        nhdsWithin_mono _ fun s hs => ⟨le_of_lt hs.1, hs.2⟩
      have hf : ContinuousWithinAt
          (fun s : ℝ =>
            |Work.Diff.EXT.jetAll (G s) j (k + 1 + 4)
                  (Work.Diff.EXT.dtOpD (I := I) (M := M) G s (k + 1))
                  (fun r : Fin ((k + 1 + 4) + j) =>
                    Submission.Diff.smoothExt x (w (Fin.cast h1 r))) x
                - Work.Diff.EXT.jetAll (G s) (j + 1) (k + 4)
                  (Work.Diff.EXT.dtOpD (I := I) (M := M) G s k)
                  (fun r : Fin ((k + 4) + (j + 1)) =>
                    Submission.Diff.smoothExt x (w (Fin.cast h2 r))) x|)
          (Set.Ico 0 T) 0 :=
        (srcConnVar_continuousAt_zero (I := I) (M := M) k j G T hflow x _ hF₁ _ hF₂).abs
      have hg : ContinuousWithinAt
          (fun s : ℝ => C * (Work.Diff.EXT.Shape (G s) x ((k + 1) + j)
                * Finset.univ.prod
                    (fun r : Fin N => Real.sqrt ((G s).inner x (w r) (w r)))))
          (Set.Ico 0 T) 0 :=
        (shape_prod_continuousWithinAt_zero (I := I) (M := M) hflow ((k + 1) + j) N x w).const_mul C
      haveI hne : (𝓝[Set.Ioo (0 : ℝ) T] 0).NeBot := by
        have hle0 : 𝓝[Set.Ioi (0 : ℝ)] 0 ≤ 𝓝 (0 : ℝ) := by
          simpa only [nhdsWithin_univ] using
            nhdsWithin_mono (0 : ℝ) (Set.subset_univ (Set.Ioi (0 : ℝ)))
        have hmem : Set.Iio T ∈ 𝓝[Set.Ioi (0 : ℝ)] 0 :=
          (Filter.le_def.mp hle0) (Set.Iio T) (isOpen_Iio.mem_nhds hT)
        have hset : Set.Ioo (0 : ℝ) T = Set.Iio T ∩ Set.Ioi 0 := by
          ext s; simp only [Set.mem_Ioo, Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ioi, and_comm]
        have heq : 𝓝[Set.Ioo (0 : ℝ) T] 0 = 𝓝[Set.Ioi (0 : ℝ)] 0 := by
          rw [hset]
          exact nhdsWithin_inter_of_mem hmem
        rw [heq]
        infer_instance
      have hkey := le_of_tendsto_of_tendsto (hf.tendsto.mono_left hle)
        (hg.tendsto.mono_left hle) hev
      simpa only [mul_assoc] using hkey
    · -- `T ≤ 0`: the slab is empty, so there is nothing to prove
      exact absurd ht.2 hT

end Work.Diff.EXT.evolX
