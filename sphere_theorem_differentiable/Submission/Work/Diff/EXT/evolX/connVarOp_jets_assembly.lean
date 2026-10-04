import Mathlib
import Submission.Work.Diff.EXT.evolX.jetCalcDefs
import Submission.Work.Diff.EXT.evolX.connVarDefs
import Submission.Work.Diff.EXT.jetSmoothDefs
import Submission.Work.Diff.EXT.covKRmExt_tensorial
import Submission.Work.Diff.EXT.evolX.jetAll_locality
import Submission.Work.Diff.EXT.evolX.jetAll_sum_of_JetSmoothOp
import Submission.Work.Diff.EXT.evolX.opJetSmooth_lapOpE
import Submission.Work.Diff.EXT.curvNormK_frame_indep
import Submission.Work.Diff.Evol.cv_dLC
import Submission.Work.Diff.T.lc_smooth
import Submission.Work.Diff.T.lc_variation
import Submission.Work.EXT.lcSmooth_noBoundary

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.EXT.evolX

/-! ## Assembly of the jet bound for the connection-variation operator

The target `Work.Diff.EXT.evolX.connVarOp_jets` is assembled here from

* the pointwise identity `connVarOp_eq_sum_substOp_loc` (the sum of contracted towers),
* the locality of the jets (`jetAll_congr_of_pointwise`),
* the additivity of the jets over the finite sum (`jetAll_sum_of_JetSmoothOp`) with the
  `JetSmoothOp` of the summands (`jetSmoothOp_substOp_loc`) and of their sum
  (`jetSmoothOp_sum_substOp`), the negation rule for the jets (`JetNegRule`, proved as
  `Work.Diff.EXT.evolX.jetAll_neg_of_JetSmoothOp`),
* the per-summand bound (`substOp_jets_le_v2`, with the vector-valued operator `vdlcOp G t`, level
  `1` for the pairing and level `k` for the tower — `strongAt_ckt`), and
* the triangle inequality.

Everything in this module is independent of `connVar_src_jets`/`connVarOp_subst`, so that the
target module (which those modules import) may import it. -/

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-- **The vector-valued operator of the first variation of the connection** (the local name of the
operator `Work.Diff.EXT.evolX.VdLC`, so that this module avoids the cycle through
`connVarOp_subst`).  It is definitionally equal to `VdLC`. -/
noncomputable def vdlcOp (G : ℝ → Submission.Diff.SMet I M) (t : ℝ) :
    (Fin 2 → Work.Diff.EXT.TField (I := I) (M := M)) → (y : M) → TangentSpace I y :=
  fun H y => Submission.Diff.dLC G t (H 0) (H 1) y

/-- **The connection-variation operator is the sum of the contracted towers** (local copy of
`Work.Diff.EXT.evolX.connVarOp_eq_sum_substOp`, with the vector-valued operator `vdlcOp`). -/
theorem connVarOp_eq_sum_substOp_loc [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (hLV : Submission.Diff.LCVariation I M)
    {G : ℝ → Submission.Diff.SMet I M} {T : ℝ} (hflow : Submission.Diff.IsRicciFlow G T)
    {t : ℝ} (ht : t ∈ Set.Ioo 0 T) (k : ℕ)
    (F : Fin (k + 5) → Work.Diff.EXT.TField (I := I) (M := M))
    (hF : ∀ i, Work.Diff.EXT.SmoothF (I := I) (M := M) (F i)) :
    (fun y : M => connVarOp (I := I) (M := M) G t k F y)
      = fun y : M => - Finset.univ.sum (fun s : Fin (k + 4) =>
          substOp (I := I) (M := M) (G t) k s (vdlcOp (I := I) (M := M) G t) F y) := by
  have hJopen : IsOpen (Set.Ioo (0 : ℝ) T) := isOpen_Ioo
  have hJs : Submission.Diff.JointSmooth G (Set.Ioo (0 : ℝ) T) :=
    hflow.1.mono (Set.prod_mono Set.Ioo_subset_Ico_self (subset_refl _))
  have hF' : ∀ i : Fin (k + 4), Work.Diff.EXT.SmoothF (I := I) (M := M)
      ((fun i : Fin (k + 4) => F i.succ) i) := fun i => hF i.succ
  have hW : ∀ s : Fin (k + 4), Work.Diff.EXT.SmoothF (I := I) (M := M)
      (Submission.Diff.dLC G t (F 0) (F s.succ)) :=
    fun s => Work.Diff.Evol.cv_dLC_smooth (I := I) (M := M) hLC hLV hJopen hJs ht
      (F 0) (F s.succ) (hF 0) (hF s.succ)
  funext y
  simp only [connVarOp, substOp, vdlcOp, Finset.sum_apply, Pi.neg_apply]
  congr 1
  refine Finset.sum_congr rfl (fun s _ => ?_)
  refine Work.Diff.EXT.ckt_val_dep_all (I := I) (M := M) hLC (G t) k y ?_ ?_ ?_
  · intro r
    by_cases hr : r = s
    · subst hr
      rw [Function.update_self]
      exact hW r
    · rw [Function.update_of_ne hr]
      exact hF' r
  · intro r
    by_cases hr : r = s
    · subst hr
      rw [Function.update_self]
      exact Work.Diff.GE.smoothExt_cmdiff y _
    · rw [Function.update_of_ne hr]
      exact hF' r
  · intro r
    by_cases hr : r = s
    · subst hr
      rw [Function.update_self, Function.update_self, Work.Diff.GE.smoothExt_apply]
      congr 1
    · rw [Function.update_of_ne hr, Function.update_of_ne hr]

/-- **The value of the contracted tower with the connection variation inserted is `C^∞`** on tuples
of smooth fields (the `C^∞`-level input of `Work.Diff.EXT.evolX.jetSmoothOp_substOp_VdLC`). -/
theorem substOp_value_cmdiff [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (hLV : Submission.Diff.LCVariation I M)
    {G : ℝ → Submission.Diff.SMet I M} {T : ℝ} (hflow : Submission.Diff.IsRicciFlow G T)
    {t : ℝ} (ht : t ∈ Set.Ioo 0 T) (k : ℕ) (s : Fin (k + 4))
    (F : Fin (k + 5) → Work.Diff.EXT.TField (I := I) (M := M))
    (hF : ∀ i, Work.Diff.EXT.SmoothF (I := I) (M := M) (F i)) :
    CMDiff ∞ (substOp (I := I) (M := M) (G t) k s (vdlcOp (I := I) (M := M) G t) F) := by
  have hJopen : IsOpen (Set.Ioo (0 : ℝ) T) := isOpen_Ioo
  have hJs : Submission.Diff.JointSmooth G (Set.Ioo (0 : ℝ) T) :=
    hflow.1.mono (Set.prod_mono Set.Ioo_subset_Ico_self (subset_refl _))
  have hF' : ∀ i : Fin (k + 4),
      Work.Diff.EXT.SmoothF (I := I) (M := M) ((fun i : Fin (k + 4) => F i.succ) i) :=
    fun i => hF i.succ
  have hW : Work.Diff.EXT.SmoothF (I := I) (M := M)
      (fun z : M => Submission.Diff.dLC G t (F 0) (F s.succ) z) :=
    fun y => Work.Diff.Evol.cv_dLC_smooth (I := I) (M := M) hLC hLV hJopen hJs ht
      (F 0) (F s.succ) (hF 0) (hF s.succ) y
  have hfun : substOp (I := I) (M := M) (G t) k s (vdlcOp (I := I) (M := M) G t) F
      = Work.Diff.EXT.ckt (I := I) (M := M) (G t) k
          (Function.update (fun i : Fin (k + 4) => F i.succ) s
            (fun z : M => Submission.Diff.dLC G t (F 0) (F s.succ) z)) := by
    funext y
    refine Work.Diff.EXT.ckt_val_dep (I := I) (M := M) hLC (G t) k y hF' s
      (Work.Diff.GE.smoothExt_cmdiff (I := I) (M := M) y
        ((vdlcOp (I := I) (M := M) G t)
          (Fin.cons (F 0) (Fin.cons (F s.succ)
            (Fin.elim0 : Fin 0 → Work.Diff.EXT.TField (I := I) (M := M)))) y))
      hW ?_
    simp only [Work.Diff.GE.smoothExt_apply, vdlcOp]
    rfl
  rw [hfun]
  exact (Work.Diff.EXT.tensProp_all (I := I) (M := M) hLC (G t) k _
    (Work.Diff.EXT.smoothF_update' (I := I) (M := M) hF' s hW)).1

/-- **`JetSmoothOp` for the contracted tower with the connection variation inserted** (local copy
of `Work.Diff.EXT.evolX.jetSmoothOp_substOp_VdLC`). -/
theorem jetSmoothOp_substOp_loc [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (hLV : Submission.Diff.LCVariation I M)
    {G : ℝ → Submission.Diff.SMet I M} {T : ℝ} (hflow : Submission.Diff.IsRicciFlow G T)
    {t : ℝ} (ht : t ∈ Set.Ioo 0 T) (k : ℕ) (s : Fin (k + 4)) (x : M) :
    Work.Diff.EXT.JetSmoothOp (I := I) (M := M) (G t) (k + 5)
      (substOp (I := I) (M := M) (G t) k s (vdlcOp (I := I) (M := M) G t)) x := by
  refine Filter.Eventually.of_forall fun y => ?_
  intro l F hF
  exact ((Work.Diff.EXT.evolX.jetAll_contMDiff_of_base (I := I) (M := M) hLC (G t)
      (K := k + 5)
      (S := substOp (I := I) (M := M) (G t) k s (vdlcOp (I := I) (M := M) G t))
      (fun F hF => substOp_value_cmdiff (I := I) (M := M) hLC hLV hflow ht k s F hF)
      l F hF)).contMDiffAt.mdifferentiableAt (by simp)

/-- **`JetSmoothOp` for the *sum* of the contracted towers**: the value of the sum is `C^∞` on
tuples of smooth fields (a finite sum of `C^∞` values), so all its jets are. -/
theorem jetSmoothOp_sum_substOp [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (hLV : Submission.Diff.LCVariation I M)
    {G : ℝ → Submission.Diff.SMet I M} {T : ℝ} (hflow : Submission.Diff.IsRicciFlow G T)
    {t : ℝ} (ht : t ∈ Set.Ioo 0 T) (k : ℕ) (x : M) :
    Work.Diff.EXT.JetSmoothOp (I := I) (M := M) (G t) (k + 5)
      (fun (F' : Fin (k + 5) → Work.Diff.EXT.TField (I := I) (M := M)) (y : M) =>
        ∑ s : Fin (k + 4),
          substOp (I := I) (M := M) (G t) k s (vdlcOp (I := I) (M := M) G t) F' y) x := by
  refine Filter.Eventually.of_forall fun y => ?_
  intro l F hF
  have h0 : ∀ F' : Fin (k + 5) → Work.Diff.EXT.TField (I := I) (M := M),
      (∀ i, Work.Diff.EXT.SmoothF (I := I) (M := M) (F' i)) →
      CMDiff ∞ (fun z : M => ∑ s : Fin (k + 4),
        substOp (I := I) (M := M) (G t) k s (vdlcOp (I := I) (M := M) G t) F' z) := by
    intro F' hF'
    exact ContMDiff.sum (t := Finset.univ)
      (f := fun s : Fin (k + 4) => substOp (I := I) (M := M) (G t) k s
        (vdlcOp (I := I) (M := M) G t) F')
      (fun s _ => substOp_value_cmdiff (I := I) (M := M) hLC hLV hflow ht k s F' hF')
  exact ((Work.Diff.EXT.evolX.jetAll_contMDiff_of_base (I := I) (M := M) hLC (G t)
      (K := k + 5)
      (S := fun (F' : Fin (k + 5) → Work.Diff.EXT.TField (I := I) (M := M)) (y : M) =>
        ∑ s : Fin (k + 4),
          substOp (I := I) (M := M) (G t) k s (vdlcOp (I := I) (M := M) G t) F' y)
      h0 l F hF)).contMDiffAt.mdifferentiableAt (by simp)

/-- **The per-summand bound** used by the assembly: the jet bound for one contracted tower
`substOp (G t) k s (vdlcOp G t)` at jet order `j`, with the constant coming from a pairing strength
`CV` (the levels: tower `k`, pairing `1`, hence `Shape (k+1+j)`). -/
def ConnVarSubstBound (k j : ℕ) (CV : ℕ → ℝ) : Prop :=
  ∀ (G : ℝ → Submission.Diff.SMet I M) (T : ℝ), Submission.Diff.IsRicciFlow G T →
    ∀ t ∈ Set.Ioo 0 T, ∀ x : M, ∀ s : Fin (k + 4),
      ∀ F : Fin ((k + 5) + j) → Work.Diff.EXT.TField (I := I) (M := M),
        (∀ i, Work.Diff.EXT.SmoothF (I := I) (M := M) (F i)) →
        |Work.Diff.EXT.jetAll (G t) j (k + 5)
            (substOp (I := I) (M := M) (G t) k s (vdlcOp (I := I) (M := M) G t)) F x|
          ≤ (Finset.sum (Finset.range (j + 1))
                (fun b => ((Nat.choose j b : ℕ) : ℝ) * CV (j - b)))
            * Work.Diff.EXT.Shape (G t) x (k + 1 + j)
            * Finset.univ.prod (fun r : Fin ((k + 5) + j) =>
                Real.sqrt ((G t).inner x (F r x) (F r x)))

/-- **The negation rule for the jets** (germ form): the jets of `-S` are the negatives of the jets
of `S`, for an operator whose jets are mdifferentiable.  This is the statement of the proved
`Work.Diff.EXT.evolX.jetAll_neg_of_JetSmoothOp`. -/
def JetNegRule [T2Space M] : Prop :=
  ∀ {K : ℕ} (g : Submission.Diff.SMet I M)
    (S : (Fin K → Work.Diff.EXT.TField (I := I) (M := M)) → M → ℝ) (x : M),
    Work.Diff.EXT.JetSmoothOp (I := I) (M := M) g K S x →
    ∀ (j : ℕ) (F : Fin (K + j) → Work.Diff.EXT.TField (I := I) (M := M)),
      (∀ r, Work.Diff.EXT.SmoothF (I := I) (M := M) (F r)) →
      Work.Diff.EXT.jetAll g j K (fun F y => - S F y) F =ᶠ[nhds x]
        fun y => - Work.Diff.EXT.jetAll g j K S F y

/-- **The assembly**: given the display negation rule and the per-summand bound, the jet bound for
`connVarOp` follows. -/
theorem connVarOp_jets_of_subst [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hneg : JetNegRule (I := I) (M := M))
    (k j : ℕ) (CV : ℕ → ℝ) (hCV : ∀ a, 0 ≤ CV a)
    (hsubst : ConnVarSubstBound (I := I) (M := M) k j CV) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (G : ℝ → Submission.Diff.SMet I M) (T : ℝ), Submission.Diff.IsRicciFlow G T →
        ∀ t ∈ Set.Ioo 0 T, ∀ x : M,
        ∀ (F : Fin ((k + 5) + j) → Work.Diff.EXT.TField (I := I) (M := M)),
          (∀ i, Work.Diff.EXT.SmoothF (I := I) (M := M) (F i)) →
          |Work.Diff.EXT.jetAll (G t) j (k + 5)
              (Work.Diff.EXT.evolX.connVarOp (I := I) (M := M) G t k) F x|
            ≤ C * Work.Diff.EXT.Shape (G t) x (k + 1 + j)
                * ∏ r : Fin ((k + 5) + j),
                    Real.sqrt ((G t).inner x (F r x) (F r x)) := by
  have hLC : Submission.Diff.LCSmooth I M := Work.EXT.lcSmooth_noBoundary (I := I) (M := M)
  have hLV : Submission.Diff.LCVariation I M := Work.Diff.T.lc_variation (I := I) (M := M) hLC
  refine ⟨((k + 4 : ℕ) : ℝ) * Finset.sum (Finset.range (j + 1))
      (fun b => ((Nat.choose j b : ℕ) : ℝ) * CV (j - b)), ?_, ?_⟩
  · have h0 : ∀ b ∈ Finset.range (j + 1), 0 ≤ ((Nat.choose j b : ℕ) : ℝ) * CV (j - b) :=
      fun b _ => mul_nonneg (by positivity) (hCV (j - b))
    exact mul_nonneg (by positivity) (Finset.sum_nonneg h0)
  · intro G T hflow t ht x F hF
    set B : ℝ := (Finset.sum (Finset.range (j + 1))
        (fun b => ((Nat.choose j b : ℕ) : ℝ) * CV (j - b)))
        * Work.Diff.EXT.Shape (G t) x (k + 1 + j)
        * Finset.univ.prod (fun r : Fin ((k + 5) + j) =>
            Real.sqrt ((G t).inner x (F r x) (F r x))) with hB
    -- the per-summand bound
    have hb : ∀ s : Fin (k + 4),
        |Work.Diff.EXT.jetAll (G t) j (k + 5)
            (substOp (I := I) (M := M) (G t) k s (vdlcOp (I := I) (M := M) G t)) F x| ≤ B := by
      intro s
      rw [hB]
      exact hsubst G T hflow t ht x s F hF
    have hsm : ∀ s : Fin (k + 4), Work.Diff.EXT.JetSmoothOp (I := I) (M := M) (G t) (k + 5)
        (substOp (I := I) (M := M) (G t) k s (vdlcOp (I := I) (M := M) G t)) x :=
      fun s => jetSmoothOp_substOp_loc (I := I) (M := M) hLC hLV hflow ht k s x
    have hsm_sum : Work.Diff.EXT.JetSmoothOp (I := I) (M := M) (G t) (k + 5)
        (fun (F' : Fin (k + 5) → Work.Diff.EXT.TField (I := I) (M := M)) (y : M) =>
          ∑ s : Fin (k + 4),
            substOp (I := I) (M := M) (G t) k s (vdlcOp (I := I) (M := M) G t) F' y) x :=
      jetSmoothOp_sum_substOp (I := I) (M := M) hLC hLV hflow ht k x
    -- locality: `connVarOp` is the negative of that sum
    have hloc : Work.Diff.EXT.jetAll (G t) j (k + 5)
        (Work.Diff.EXT.evolX.connVarOp (I := I) (M := M) G t k) F x
        = Work.Diff.EXT.jetAll (G t) j (k + 5)
            (fun (F' : Fin (k + 5) → Work.Diff.EXT.TField (I := I) (M := M)) (y : M) =>
              - ∑ s : Fin (k + 4),
                  substOp (I := I) (M := M) (G t) k s (vdlcOp (I := I) (M := M) G t) F' y)
            F x := by
      exact jetAll_congr_of_pointwise (I := I) (M := M) hLC (g := G t) (K := k + 5)
        (S := Work.Diff.EXT.evolX.connVarOp (I := I) (M := M) G t k)
        (S' := fun (F' : Fin (k + 5) → Work.Diff.EXT.TField (I := I) (M := M)) (y : M) =>
          - ∑ s : Fin (k + 4),
              substOp (I := I) (M := M) (G t) k s (vdlcOp (I := I) (M := M) G t) F' y)
        (fun F' hF' y => by
          have h := congrFun (connVarOp_eq_sum_substOp_loc (I := I) (M := M) hLC hLV hflow
            ht k F' hF') y
          simpa only [Pi.neg_apply] using h)
        j F hF x
    -- the negation rule
    have hnegstep := (hneg (G t) _ x hsm_sum j F hF).eq_of_nhds
    -- the additivity of the jets over the sum
    have hadd := (jetAll_sum_of_JetSmoothOp (I := I) (M := M) hLC (g := G t) (K := k + 5)
      (S := fun s : Fin (k + 4) =>
        substOp (I := I) (M := M) (G t) k s (vdlcOp (I := I) (M := M) G t))
      (x := x) hsm j F hF).eq_of_nhds
    have hop : (∑ s : Fin (k + 4),
          substOp (I := I) (M := M) (G t) k s (vdlcOp (I := I) (M := M) G t))
        = (fun (F' : Fin (k + 5) → Work.Diff.EXT.TField (I := I) (M := M)) (y : M) =>
          ∑ s : Fin (k + 4),
            substOp (I := I) (M := M) (G t) k s (vdlcOp (I := I) (M := M) G t) F' y) := by
      funext F' y
      simp only [Finset.sum_apply]
    rw [hop] at hadd
    rw [hloc, hnegstep, abs_neg, hadd]
    calc |Finset.univ.sum (fun s : Fin (k + 4) =>
            Work.Diff.EXT.jetAll (G t) j (k + 5)
              (substOp (I := I) (M := M) (G t) k s (vdlcOp (I := I) (M := M) G t)) F x)|
        ≤ Finset.univ.sum (fun s : Fin (k + 4) =>
            |Work.Diff.EXT.jetAll (G t) j (k + 5)
              (substOp (I := I) (M := M) (G t) k s (vdlcOp (I := I) (M := M) G t)) F x|) :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ Finset.univ.sum (fun _ : Fin (k + 4) => B) := Finset.sum_le_sum (fun s _ => hb s)
      _ = ((k + 4 : ℕ) : ℝ) * B := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ = ((k + 4 : ℕ) : ℝ) * (Finset.sum (Finset.range (j + 1))
            (fun b => ((Nat.choose j b : ℕ) : ℝ) * CV (j - b))
            * Work.Diff.EXT.Shape (G t) x (k + 1 + j)
            * Finset.univ.prod (fun r : Fin ((k + 5) + j) =>
                Real.sqrt ((G t).inner x (F r x) (F r x)))) := by rw [hB]
      _ = ((k + 4 : ℕ) : ℝ) * Finset.sum (Finset.range (j + 1))
              (fun b => ((Nat.choose j b : ℕ) : ℝ) * CV (j - b))
            * Work.Diff.EXT.Shape (G t) x (k + 1 + j)
            * Finset.univ.prod (fun r : Fin ((k + 5) + j) =>
                Real.sqrt ((G t).inner x (F r x) (F r x))) := by ring

end Work.Diff.EXT.evolX
