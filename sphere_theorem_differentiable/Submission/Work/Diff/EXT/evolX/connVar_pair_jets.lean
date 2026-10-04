import Mathlib
import Submission.Work.Diff.EXT.evolX.connVarDefs
import Submission.Work.Diff.EXT.evolX.connVarPairDefs
import Submission.Work.Diff.EXT.evolX.connVarPairIns
import Submission.Work.Diff.EXT.evolX.connVar_pair_base
import Submission.Work.Diff.EXT.evolX.connVar_pair_trace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The jets of the connection-variation pairing

The target `Work.Diff.EXT.evolX.connVar_pair_jets`: the `a`-th jet of the pairing
`(V,W,Z) ↦ ⟪dLC G t V W, Z⟫` of the first variation of the Levi-Civita connection along a Ricci
flow is bounded by `C √|∇^{a+1}Rm|²` times the product of the metric norms of the arguments.

The route is

* `connVar_pair_base` (`Submission.Work.Diff.EXT.evolX.connVar_pair_base`): the pairing is the
  combination `-(T₁ + T₂ - T₃)` of the frame traces `T_i = cvTr0ρ (G t) ef ρ_i` of the level-`1`
  tower;
* `connVar_pair_trace` (`Submission.Work.Diff.EXT.evolX.connVar_pair_trace`): the `a`-th jet of a
  frame trace is the level-`a+1` tower on the tuple with the frame vectors inserted in the two
  traced slots;
* the sharp Hilbert–Schmidt bound for the tower (`Work.Diff.EXT.Kpt_norm_bound`) together with its
  value dependence (`Work.Diff.EXT.ckt_val_dep_all`);
* the product over the slots of the insertion (`cv_prod_univ_Hins`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option maxHeartbeats 1600000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT.evolX

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-- **The entries of an insertion are smooth fields.** -/
theorem cvHins_smooth [T2Space M] {a : ℕ} (ρ : Fin 3 ≃ Fin 3)
    {F : Fin (a + 3) → Work.Diff.EXT.TField (I := I) (M := M)}
    (hF : ∀ i, Work.Diff.EXT.SmoothF (I := I) (M := M) (F i))
    {ef : Fin (Module.finrank ℝ E) → Work.Diff.EXT.TField (I := I) (M := M)}
    (hef : ∀ i, Work.Diff.EXT.SmoothF (I := I) (M := M) (ef i))
    (m : Fin (Module.finrank ℝ E)) :
    ∀ j, Work.Diff.EXT.SmoothF (I := I) (M := M) ((cvHins ρ F (ef m)) j) := by
  intro j
  revert j
  refine Fin.addCases (motive := fun j : Fin (a + 5) =>
    Work.Diff.EXT.SmoothF (I := I) (M := M) ((cvHins ρ F (ef m)) j)) ?_ ?_
  · intro r
    rw [cvHins_left]
    exact hF _
  · intro j5
    rw [cvHins_right]
    fin_cases j5 <;> simp only [cvIns5_0, cvIns5_1, cvIns5_2, cvIns5_3, cvIns5_4]
    · exact hF _
    · exact hef m
    · exact hF _
    · exact hef m
    · exact hF _

/-- **The sharp bound for one value of the level-`a+1` tower on an inserted tuple.** -/
theorem cv_ckt_hins_bound [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (x : M)
    {ef : Fin (Module.finrank ℝ E) → Work.Diff.EXT.TField (I := I) (M := M)}
    (hef : Work.Diff.EXT.IsFrameNear (I := I) (M := M) g x ef)
    (ρ : Fin 3 ≃ Fin 3) (a : ℕ)
    (F : Fin (a + 3) → Work.Diff.EXT.TField (I := I) (M := M))
    (hF : ∀ i, Work.Diff.EXT.SmoothF (I := I) (M := M) (F i))
    (m : Fin (Module.finrank ℝ E)) :
    |Work.Diff.EXT.ckt g (a + 1) (cvHins ρ F (ef m)) x|
      ≤ Real.sqrt (Work.Diff.EXT.curvNormK g x (a + 1))
        * ∏ s : Fin (a + 3), Real.sqrt (g.inner x (F s x) (F s x)) := by
  have hsm1 : ∀ j, Work.Diff.EXT.SmoothF (I := I) (M := M) ((cvHins ρ F (ef m)) j) :=
    cvHins_smooth (I := I) (M := M) ρ hF hef.1 m
  have hsm2 : ∀ j, Work.Diff.EXT.SmoothF (I := I) (M := M)
      ((fun j => Submission.Diff.smoothExt x ((cvHins ρ F (ef m)) j x)) j) :=
    fun j => Work.Diff.GE.smoothExt_cmdiff (I := I) (M := M) x _
  have hv : Work.Diff.EXT.ckt g (a + 1) (cvHins ρ F (ef m)) x
      = Work.Diff.EXT.ckt g (a + 1)
          (fun j => Submission.Diff.smoothExt x ((cvHins ρ F (ef m)) j x)) x :=
    Work.Diff.EXT.ckt_val_dep_all (I := I) (M := M) hLC g (a + 1) x hsm1 hsm2
      (fun j => (Work.Diff.GE.smoothExt_apply x (((cvHins ρ F (ef m)) j x))).symm)
  have hK : Work.Diff.EXT.ckt g (a + 1)
      (fun j => Submission.Diff.smoothExt x ((cvHins ρ F (ef m)) j x)) x
      = Work.Diff.EXT.Kpt g x (a + 1) (fun j => (cvHins ρ F (ef m)) j x) := rfl
  rw [hv, hK]
  have hKpt := Work.Diff.EXT.Kpt_norm_bound (I := I) (M := M) hLC g x (a + 1)
    (fun j => (cvHins ρ F (ef m)) j x)
  refine le_trans hKpt (le_of_eq ?_)
  rw [cv_prod_univ_Hins ρ
    (fun j => Real.sqrt (g.inner x ((cvHins ρ F (ef m)) j x) ((cvHins ρ F (ef m)) j x)))]
  have hon : Submission.Diff.IsONFrame g x (fun i => ef i x) := hef.2.self_of_nhds
  have hmm : g.inner x (ef m x) (ef m x) = 1 := by simpa using hon m m
  have hu0 : Real.sqrt (g.inner x ((cvHins ρ F (ef m)) (cvUslot0 a) x)
      ((cvHins ρ F (ef m)) (cvUslot0 a) x)) = 1 := by
    rw [cvHins_uslot0]
    rw [hmm]
    exact Real.sqrt_one
  have hu1 : Real.sqrt (g.inner x ((cvHins ρ F (ef m)) (cvUslot1 a) x)
      ((cvHins ρ F (ef m)) (cvUslot1 a) x)) = 1 := by
    rw [cvHins_uslot1]
    rw [hmm]
    exact Real.sqrt_one
  rw [hu0, hu1]
  have hprod : (∏ s : Fin (a + 3),
      Real.sqrt (g.inner x ((cvHins ρ F (ef m)) (cvHpos a ρ s) x)
        ((cvHins ρ F (ef m)) (cvHpos a ρ s) x)))
      = ∏ s : Fin (a + 3), Real.sqrt (g.inner x (F s x) (F s x)) := by
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [cvHins_hpos]
  rw [hprod]
  ring

/-- **The frame trace is `C^∞` on smooth tuples.** -/
theorem cvTr0ρ_cmdiff [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (x : M)
    {ef : Fin (Module.finrank ℝ E) → Work.Diff.EXT.TField (I := I) (M := M)}
    (hef : Work.Diff.EXT.IsFrameNear (I := I) (M := M) g x ef) (ρ : Fin 3 ≃ Fin 3)
    (F : Fin 3 → Work.Diff.EXT.TField (I := I) (M := M))
    (hF : ∀ i, Work.Diff.EXT.SmoothF (I := I) (M := M) (F i)) :
    CMDiff ∞ (cvTr0ρ g ef ρ F) := by
  have hsum : CMDiff ∞ (fun y : M => ∑ m : Fin (Module.finrank ℝ E),
      Work.Diff.EXT.ckt g 1 (cvHins ρ F (ef m)) y) :=
    ContMDiff.sum (t := Finset.univ)
      (f := fun m : Fin (Module.finrank ℝ E) => fun y : M =>
        Work.Diff.EXT.ckt g 1 (cvHins ρ F (ef m)) y)
      (fun m _ => (Work.Diff.EXT.tensProp_all (I := I) (M := M) hLC g 1
        (cvHins ρ F (ef m)) (cvHins_smooth (I := I) (M := M) ρ hF hef.1 m)).1)
  have hfun : cvTr0ρ g ef ρ F = fun y : M => ∑ m : Fin (Module.finrank ℝ E),
      Work.Diff.EXT.ckt g 1 (cvHins ρ F (ef m)) y := rfl
  rw [hfun]
  exact hsum

/-- **All the jets of a frame trace are `C^∞`.** -/
theorem cvTr0ρ_jetSmoothOp [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (x : M)
    {ef : Fin (Module.finrank ℝ E) → Work.Diff.EXT.TField (I := I) (M := M)}
    (hef : Work.Diff.EXT.IsFrameNear (I := I) (M := M) g x ef) (ρ : Fin 3 ≃ Fin 3) :
    Work.Diff.EXT.JetSmoothOp (I := I) (M := M) g 3 (cvTr0ρ g ef ρ) x := by
  refine Filter.Eventually.of_forall fun y => ?_
  intro l F hF
  exact (Work.Diff.EXT.evolX.jetAll_contMDiff_of_base (I := I) (M := M) hLC g
    (K := 3) (S := cvTr0ρ g ef ρ) (fun F hF => cvTr0ρ_cmdiff (I := I) (M := M)
      hLC g x hef ρ F hF) l F hF).contMDiffAt.mdifferentiableAt (by simp)

/-- **All the jets of the difference of two frame traces are `C^∞`.** -/
theorem cvTr0ρ_sub_jetSmoothOp [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (x : M)
    {ef : Fin (Module.finrank ℝ E) → Work.Diff.EXT.TField (I := I) (M := M)}
    (hef : Work.Diff.EXT.IsFrameNear (I := I) (M := M) g x ef) (ρ ρ' : Fin 3 ≃ Fin 3) :
    Work.Diff.EXT.JetSmoothOp (I := I) (M := M) g 3 (cvTr0ρ g ef ρ - cvTr0ρ g ef ρ') x := by
  refine Filter.Eventually.of_forall fun y => ?_
  intro l F hF
  exact (Work.Diff.EXT.evolX.jetAll_contMDiff_of_base (I := I) (M := M) hLC g
    (K := 3) (S := cvTr0ρ g ef ρ - cvTr0ρ g ef ρ') (fun F hF =>
      (cvTr0ρ_cmdiff (I := I) (M := M) hLC g x hef ρ F hF).sub
        (cvTr0ρ_cmdiff (I := I) (M := M) hLC g x hef ρ' F hF)) l F hF).contMDiffAt.mdifferentiableAt
    (by simp)

/-- **The pairing, jet by jet, is the trace combination** (the gluing of the level-`0` identity
`connVar_pair_base` to all jet orders). -/
theorem cvPairOp_jetAll_eq_traceComb [T2Space M]
    {G : ℝ → Submission.Diff.SMet I M} {t : ℝ} (x : M)
    {ef : Fin (Module.finrank ℝ E) → Work.Diff.EXT.TField (I := I) (M := M)}
    (hbase : ∀ Z : Fin 3 → Work.Diff.EXT.TField (I := I) (M := M),
      (∀ i, Work.Diff.EXT.SmoothF (I := I) (M := M) (Z i)) →
      cvPairOp (I := I) (M := M) G t Z =ᶠ[nhds x] cvTraceComb (I := I) (M := M) (G t) ef Z)
    (a : ℕ) (F : Fin (3 + a) → Work.Diff.EXT.TField (I := I) (M := M))
    (hF : ∀ i, Work.Diff.EXT.SmoothF (I := I) (M := M) (F i)) :
    Work.Diff.EXT.jetAll (G t) a 3 (cvPairOp (I := I) (M := M) G t) F
      =ᶠ[nhds x] Work.Diff.EXT.jetAll (G t) a 3 (cvTraceComb (I := I) (M := M) (G t) ef) F := by
  have hLC : Submission.Diff.LCSmooth I M := Work.EXT.lcSmooth_noBoundary (I := I) (M := M)
  have key : ∀ (b : ℕ) (U : Fin (3 + b) → Work.Diff.EXT.TField (I := I) (M := M)),
      (∀ i, Work.Diff.EXT.SmoothF (I := I) (M := M) (U i)) →
      Work.Diff.EXT.jetAll (G t) b 3 (cvPairOp (I := I) (M := M) G t) U
        =ᶠ[nhds x]
        Work.Diff.EXT.jetAll (G t) b 3 (cvTraceComb (I := I) (M := M) (G t) ef) U := by
    intro b
    induction b with
    | zero => intro U hU; simpa only [Work.Diff.EXT.jetAll] using hbase U hU
    | succ b ih =>
      intro U hU
      have htail : ∀ i : Fin (3 + b), Work.Diff.EXT.SmoothF (I := I) (M := M)
          ((fun i : Fin (3 + b) => U i.succ) i) := fun i => hU i.succ
      have hW : ∀ s : Fin (3 + b), Work.Diff.EXT.SmoothF (I := I) (M := M)
          (Work.Diff.EXT.dirF (G t) ((fun i : Fin (3 + b) => U i.succ) s) (U 0)) :=
        fun s => Work.Diff.EXT.dirF_smooth (I := I) (M := M) hLC (G t) (htail s) (hU 0)
      have h0 : (Work.Diff.EXT.jetAll (G t) b 3 (cvPairOp (I := I) (M := M) G t))
            (fun i : Fin (3 + b) => U i.succ)
          =ᶠ[nhds x]
          (Work.Diff.EXT.jetAll (G t) b 3 (cvTraceComb (I := I) (M := M) (G t) ef))
            (fun i : Fin (3 + b) => U i.succ) := ih _ htail
      have h1 : ∀ s : Fin (3 + b),
          (Work.Diff.EXT.jetAll (G t) b 3 (cvPairOp (I := I) (M := M) G t))
            (Function.update (fun i : Fin (3 + b) => U i.succ) s
              (Work.Diff.EXT.dirF (G t) ((fun i : Fin (3 + b) => U i.succ) s) (U 0)))
          =ᶠ[nhds x]
          (Work.Diff.EXT.jetAll (G t) b 3 (cvTraceComb (I := I) (M := M) (G t) ef))
            (Function.update (fun i : Fin (3 + b) => U i.succ) s
              (Work.Diff.EXT.dirF (G t) ((fun i : Fin (3 + b) => U i.succ) s) (U 0))) :=
        fun s => ih _ (Work.Diff.EXT.smoothF_update' htail s (hW s))
      have hcongr := Work.Diff.EXT.extStep_congr_at (I := I) (M := M) (G t)
        (Work.Diff.EXT.jetAll (G t) b 3 (cvPairOp (I := I) (M := M) G t))
        (Work.Diff.EXT.jetAll (G t) b 3 (cvTraceComb (I := I) (M := M) (G t) ef)) U x h0 h1
      simpa only [Work.Diff.EXT.jetAll] using hcongr
  exact key a F hF

/-- **The main bound, from the two inputs**: the level-`0` identity `connVar_pair_base` and the
trace/jet identity `connVar_pair_trace` (which are proved in their own modules). -/
theorem connVar_pair_jets_of_inputs
    [I.Boundaryless] [T2Space M]
    (hbase : ∀ (G : ℝ → Submission.Diff.SMet I M) (T : ℝ), Submission.Diff.IsRicciFlow G T →
      ∀ t ∈ Set.Ioo 0 T, ∀ x : M,
      ∀ (ef : Fin (Module.finrank ℝ E) → Work.Diff.EXT.TField (I := I) (M := M)),
        Work.Diff.EXT.IsFrameNear (I := I) (M := M) (G t) x ef →
      ∀ Z : Fin 3 → Work.Diff.EXT.TField (I := I) (M := M),
        (∀ i, Work.Diff.EXT.SmoothF (I := I) (M := M) (Z i)) →
        cvPairOp (I := I) (M := M) G t Z =ᶠ[nhds x] cvTraceComb (I := I) (M := M) (G t) ef Z)
    (htrace : ∀ (g : Submission.Diff.SMet I M) (x : M)
        (ef : Fin (Module.finrank ℝ E) → Work.Diff.EXT.TField (I := I) (M := M)),
      Work.Diff.EXT.IsFrameNear (I := I) (M := M) g x ef →
      ∀ (ρ : Fin 3 ≃ Fin 3) (a : ℕ)
        (F : Fin (a + 3) → Work.Diff.EXT.TField (I := I) (M := M)),
        (∀ i, Work.Diff.EXT.SmoothF (I := I) (M := M) (F i)) →
        Work.Diff.EXT.jetAll g a 3 (cvTr0ρ g ef ρ)
            (fun r : Fin (3 + a) => F (cvCast3' a r))
          =ᶠ[nhds x] fun y => ∑ m : Fin (Module.finrank ℝ E),
            Work.Diff.EXT.ckt g (a + 1) (cvHins ρ F (ef m)) y)
    (a : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (G : ℝ → Submission.Diff.SMet I M) (T : ℝ), Submission.Diff.IsRicciFlow G T →
        ∀ t ∈ Set.Ioo 0 T, ∀ x : M,
        ∀ (F : Fin (3 + a) → Work.Diff.EXT.TField (I := I) (M := M)),
          (∀ i, Work.Diff.EXT.SmoothF (I := I) (M := M) (F i)) →
          |Work.Diff.EXT.jetAll (G t) a 3
              (fun (F' : Fin 3 → Work.Diff.EXT.TField (I := I) (M := M)) (y : M) =>
                (G t).inner y (Submission.Diff.dLC G t (F' 0) (F' 1) y) (F' 2 y))
              F x|
            ≤ C * Real.sqrt (Work.Diff.EXT.curvNormK (G t) x (1 + a))
                * ∏ r : Fin (3 + a), Real.sqrt ((G t).inner x (F r x) (F r x)) := by
  have hLC : Submission.Diff.LCSmooth I M := Work.EXT.lcSmooth_noBoundary (I := I) (M := M)
  refine ⟨3 * (Module.finrank ℝ E : ℝ), by positivity, ?_⟩
  intro G T hflow t ht x F hF
  obtain ⟨ef, hef, _hefx⟩ := Work.Diff.EXT.evolX.isFrameNear_exists (I := I) (M := M) (G t) x
  have hop : (fun (F' : Fin 3 → Work.Diff.EXT.TField (I := I) (M := M)) (y : M) =>
      (G t).inner y (Submission.Diff.dLC G t (F' 0) (F' 1) y) (F' 2 y))
      = cvPairOp (I := I) (M := M) G t := rfl
  rw [hop]
  -- glue to the trace combination
  have hglue := cvPairOp_jetAll_eq_traceComb (I := I) (M := M) (G := G) (t := t) x
    (fun Z hZ => hbase G T hflow t ht x ef hef Z hZ) a F hF
  rw [hglue.eq_of_nhds]
  -- linearity in the (nested difference) combination
  have hA1 := cvTr0ρ_jetSmoothOp (I := I) (M := M) hLC (G t) x hef cvRho1
  have hA2 := cvTr0ρ_jetSmoothOp (I := I) (M := M) hLC (G t) x hef cvRho2
  have hA3 := cvTr0ρ_jetSmoothOp (I := I) (M := M) hLC (G t) x hef cvRho3
  have hA31 := cvTr0ρ_sub_jetSmoothOp (I := I) (M := M) hLC (G t) x hef cvRho3 cvRho1
  have e1 := (Work.Diff.EXT.jetAll_sub_of_JetSmoothOp (I := I) (M := M) (g := G t) (K := 3)
    (S := cvTr0ρ (G t) ef cvRho3 - cvTr0ρ (G t) ef cvRho1)
    (S' := cvTr0ρ (G t) ef cvRho2) x hA31 hA2 a F hF).eq_of_nhds
  have e2 := (Work.Diff.EXT.jetAll_sub_of_JetSmoothOp (I := I) (M := M) (g := G t) (K := 3)
    (S := cvTr0ρ (G t) ef cvRho3) (S' := cvTr0ρ (G t) ef cvRho1) x hA3 hA1 a F hF).eq_of_nhds
  rw [show cvTraceComb (I := I) (M := M) (G t) ef
      = (cvTr0ρ (G t) ef cvRho3 - cvTr0ρ (G t) ef cvRho1) - cvTr0ρ (G t) ef cvRho2 from rfl]
  rw [e1, e2]
  -- the bound for each of the three traces
  set T1 := Work.Diff.EXT.jetAll (G t) a 3 (cvTr0ρ (G t) ef cvRho1) F x with hT1
  set T2 := Work.Diff.EXT.jetAll (G t) a 3 (cvTr0ρ (G t) ef cvRho2) F x with hT2
  set T3 := Work.Diff.EXT.jetAll (G t) a 3 (cvTr0ρ (G t) ef cvRho3) F x with hT3
  -- the reindexed tuple of arity `a+3`
  set F' : Fin (a + 3) → Work.Diff.EXT.TField (I := I) (M := M) :=
    fun i => F (cvCast3 a i) with hF'def
  have hF'sm : ∀ i, Work.Diff.EXT.SmoothF (I := I) (M := M) (F' i) := fun i => hF _
  have htup : (fun r : Fin (3 + a) => F' (cvCast3' a r)) = F := by
    funext r
    rw [hF'def]
    exact congrArg F (cvCast3_cast3' r)
  have hprod : (∏ s : Fin (a + 3), Real.sqrt ((G t).inner x (F' s x) (F' s x)))
      = ∏ r : Fin (3 + a), Real.sqrt ((G t).inner x (F r x) (F r x)) := by
    refine Finset.prod_bij (fun s _ => cvCast3 a s) (fun s _ => Finset.mem_univ _) ?_ ?_ ?_
    · intro s _ s' _ h
      rw [← cvCast3'_cvCast3 (a := a) s, h, cvCast3'_cvCast3 (a := a) s']
    · intro r _
      exact ⟨cvCast3' a r, Finset.mem_univ _, cvCast3_cast3' r⟩
    · intro s _
      rw [hF'def]
  have hbound : ∀ (ρ : Fin 3 ≃ Fin 3), |Work.Diff.EXT.jetAll (G t) a 3
        (cvTr0ρ (G t) ef ρ) F x|
      ≤ (Module.finrank ℝ E : ℝ) * Real.sqrt (Work.Diff.EXT.curvNormK (G t) x (a + 1))
        * ∏ r : Fin (3 + a), Real.sqrt ((G t).inner x (F r x) (F r x)) := by
    intro ρ
    have htr := htrace (G t) x ef hef ρ a F' hF'sm
    rw [htup] at htr
    rw [htr.eq_of_nhds]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hterm : ∀ m : Fin (Module.finrank ℝ E),
        |Work.Diff.EXT.ckt (G t) (a + 1) (cvHins ρ F' (ef m)) x|
          ≤ Real.sqrt (Work.Diff.EXT.curvNormK (G t) x (a + 1))
            * ∏ r : Fin (3 + a), Real.sqrt ((G t).inner x (F r x) (F r x)) := by
      intro m
      have hb := cv_ckt_hins_bound (I := I) (M := M) hLC (G t) x hef ρ a F' hF'sm m
      rw [hprod] at hb
      exact hb
    refine le_trans (Finset.sum_le_sum fun m _ => hterm m) (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have h1 := hbound cvRho1
  have h2 := hbound cvRho2
  have h3 := hbound cvRho3
  set B := (Module.finrank ℝ E : ℝ) * Real.sqrt (Work.Diff.EXT.curvNormK (G t) x (a + 1))
    * ∏ r : Fin (3 + a), Real.sqrt ((G t).inner x (F r x) (F r x)) with hB
  have htri : |(T3 - T1) - T2| ≤ 3 * B := by
    calc |(T3 - T1) - T2| ≤ |(T3 - T1) - 0| + |0 - T2| := abs_sub_le (T3 - T1) 0 T2
      _ ≤ (|T3| + |T1|) + |T2| := by
          have h := abs_sub_le T3 0 T1
          simp only [sub_zero, zero_sub, abs_neg] at h ⊢
          linarith [h]
      _ ≤ B + B + B := by linarith [h1, h2, h3]
      _ = 3 * B := by ring
  refine le_trans htri (le_of_eq ?_)
  rw [hB, show (1 : ℕ) + a = a + 1 from Nat.add_comm 1 a]
  ring

/-- **The jets of the connection-variation pairing** (Brendle–Schoen, the connection-variation
source of the `k`-th order Shi estimate): the `a`-th covariant derivative of the pairing
`(V,W,Z) ↦ ⟪dLC G t V W, Z⟫` along a Ricci flow is bounded by a universal constant times
`√|∇^{a+1}Rm|²` times the product of the metric norms of the arguments. -/
theorem connVar_pair_jets
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (a : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (G : ℝ → Submission.Diff.SMet I M) (T : ℝ), Submission.Diff.IsRicciFlow G T →
        ∀ t ∈ Set.Ioo 0 T, ∀ x : M,
        ∀ (F : Fin (3 + a) → Work.Diff.EXT.TField (I := I) (M := M)),
          (∀ i, Work.Diff.EXT.SmoothF (I := I) (M := M) (F i)) →
          |Work.Diff.EXT.jetAll (G t) a 3
              (fun (F' : Fin 3 → Work.Diff.EXT.TField (I := I) (M := M)) (y : M) =>
                (G t).inner y (Submission.Diff.dLC G t (F' 0) (F' 1) y) (F' 2 y))
              F x|
            ≤ C * Real.sqrt (Work.Diff.EXT.curvNormK (G t) x (1 + a))
                * ∏ r : Fin (3 + a), Real.sqrt ((G t).inner x (F r x) (F r x)) := by
  have hLC : Submission.Diff.LCSmooth I M := Work.EXT.lcSmooth_noBoundary (I := I) (M := M)
  have hLV : Submission.Diff.LCVariation I M := Work.Diff.T.lc_variation (I := I) (M := M) hLC
  exact connVar_pair_jets_of_inputs (I := I) (M := M)
    (fun G T hflow t ht x ef hef Z hZ =>
      (connVar_pair_base (I := I) (M := M) (G := G) (T := T) (t := t) (ef := ef)
        hLC hLV hflow ht x hef Z hZ).trans
        (Filter.Eventually.of_forall (fun y => (cvTraceComb_apply (G t) ef Z y).symm)))
    (fun g x ef hef ρ b F hF =>
      connVar_pair_trace (I := I) (M := M) hLC g x hef ρ b F hF)
    a

end Work.Diff.EXT.evolX
