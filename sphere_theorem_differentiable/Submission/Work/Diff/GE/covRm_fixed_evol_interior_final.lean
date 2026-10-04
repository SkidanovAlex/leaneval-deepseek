import Mathlib
import Submission.Work.Diff.GE.covRmFixedEvolDefs
import Submission.Work.Diff.GE.reaction_map_defs
import Submission.Work.Diff.GE.frame_deps
import Submission.Work.Diff.GE.FixAsm.mvfderiv_rmP_timeDeriv

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The interior evolution estimate for the fixed-vector component of `∇Rm`

This file proves `Work.Diff.GE.covRm_fixed_evol_interior_final`: at an interior time `t ∈ (0,T)` of a
Ricci flow, the fixed-vector component `s ↦ covRm (G s) x v a b c d` of `∇Rm` is differentiable from
the right with derivative `covRmTimeDeriv reactionMap G t x v a b c d`, and that derivative differs
from the rough Laplacian `lapCovRmAt` by at most `C |Rm| |∇Rm|` times the metric norms of the five
vectors.

The proof is an assembly of the hypotheses:

* the derivative of the main term `s ↦ mvfderiv I (fun y ↦ rmP (G s) y (A y) …) x v` is Clairaut's
  step `Work.Diff.GE.FixAsm.mvfderiv_rmP_timeDeriv`, whose value is split over the sum
  `ΔRm + reactionMap(Rm)` using the differentiability hypotheses `hLapD`, `hReactD`;
* the derivative of each of the four correction terms `s ↦ rmP (G s) x (∇_v A_slot) b c d` is the
  moving-slot product rule `hP13`;
* unfolding `covLapRmAt`, `covReactionFormAt` and `covRmTimeDeriv` gives the stated value;
* the bound is the sum of the Weitzenböck bound `hWeit`, the two reaction bounds `hReactB`,
  `hReactB2` and the connection-variation bound `hConn` — the last after identifying the
  `LCVariation` vectors of `hLV` with those of `hConn` by uniqueness of the `IsConnVar`
  characterisation.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.GE

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
  [I.Boundaryless] [T2Space M] [CompactSpace M]

/-- Projection of `![a,b,c,d]` at `0`. -/
private theorem fm_vec4_zero {x : M} (a b c d : TangentSpace I x) :
    (![a, b, c, d] : Fin 4 → TangentSpace I x) 0 = a := by simp

/-- Projection of `![a,b,c,d]` at `1`. -/
private theorem fm_vec4_one {x : M} (a b c d : TangentSpace I x) :
    (![a, b, c, d] : Fin 4 → TangentSpace I x) 1 = b := by simp

/-- Projection of `![a,b,c,d]` at `2`. -/
private theorem fm_vec4_two {x : M} (a b c d : TangentSpace I x) :
    (![a, b, c, d] : Fin 4 → TangentSpace I x) 2 = c := by simp

/-- Projection of `![a,b,c,d]` at `3`. -/
private theorem fm_vec4_three {x : M} (a b c d : TangentSpace I x) :
    (![a, b, c, d] : Fin 4 → TangentSpace I x) 3 = d := by simp

/-- Bilinearity of the metric pairing in the first slot. -/
private theorem fm_inner_sub_left (g : SMet I M) (x : M) (u v w : TangentSpace I x) :
    g.inner x (u - v) w = g.inner x u w - g.inner x v w := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  show inner ℝ (u - v) w = inner ℝ u w - inner ℝ v w
  rw [inner_sub_left]

/-- `reactionFormAt` is linear in the reaction map. -/
private theorem fm_reactionFormAt_neg (F : Curv4 (Module.finrank ℝ E) → Curv4 (Module.finrank ℝ E))
    (g : SMet I M) (x : M) (a b c d : TangentSpace I x) :
    reactionFormAt (fun R ↦ -F R) g x a b c d = - reactionFormAt F g x a b c d := by
  simp [reactionFormAt]

/-- `covReactionFormAt` is linear in the reaction map. -/
private theorem fm_covReactionFormAt_neg (F : Curv4 (Module.finrank ℝ E) → Curv4 (Module.finrank ℝ E))
    (g : SMet I M) (x : M) (v a b c d : TangentSpace I x) :
    covReactionFormAt (fun R ↦ -F R) g x v a b c d
      = - covReactionFormAt F g x v a b c d := by
  rw [covReactionFormAt, covReactionFormAt]
  simp only [fm_reactionFormAt_neg]
  rw [show (fun y : M ↦ -reactionFormAt F g y (smoothExt x a y) (smoothExt x b y)
        (smoothExt x c y) (smoothExt x d y))
      = - (fun y : M ↦ reactionFormAt F g y (smoothExt x a y) (smoothExt x b y)
        (smoothExt x c y) (smoothExt x d y)) from rfl]
  rw [mvfderiv_neg]
  simp only [neg_apply]
  ring

/-- Uniqueness of the connection-variation vector: `IsConnVar` determines `w`. -/
private theorem fm_IsConnVar_unique {G : ℝ → SMet I M} {t : ℝ} {x : M}
    {X Y : Π y : M, TangentSpace I y} {w w' : TangentSpace I x}
    (hw : IsConnVar G t x X Y w) (hw' : IsConnVar G t x X Y w') : w = w' := by
  have h1 := hw (smoothExt x (w - w')) (smoothExt_cmdiff x (w - w'))
  have h2 := hw' (smoothExt x (w - w')) (smoothExt_cmdiff x (w - w'))
  rw [smoothExt_apply] at h1 h2
  have hz : (G t).inner x (w - w') (w - w') = 0 := by
    rw [fm_inner_sub_left (G t) x w w' (w - w'), h1, h2, sub_self]
  have hzero : w - w' = 0 := by
    by_contra hne
    have hpos := (G t).pos x (w - w') hne
    rw [hz] at hpos
    exact absurd hpos (lt_irrefl 0)
  exact sub_eq_zero.mp hzero

theorem covRm_fixed_evol_interior_final
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : Submission.Diff.LCSmooth I M) (hLV : Submission.Diff.LCVariation I M)
    (hEvol : ∀ (G : ℝ → Submission.Diff.SMet I M) (T : ℝ), Submission.Diff.IsRicciFlow G T →
      ∀ t ∈ Set.Ioo 0 T, ∀ x : M, ∀ a b c d : TangentSpace I x,
      HasDerivWithinAt (fun s ↦ Submission.Diff.rmP (G s) x a b c d)
        (Work.Diff.GE.lapRmAt (G t) x a b c d
          + Work.Diff.GE.reactionFormAt Work.Diff.GE.reactionMap (G t)
              x a b c d) (Set.Ico 0 T) t)
    (hLapD : ∀ (g : Submission.Diff.SMet I M) (x : M)
      (A B C D : Π y : M, TangentSpace I y),
        Work.Diff.GE.SmoothField (I := I) (M := M) A →
        Work.Diff.GE.SmoothField (I := I) (M := M) B →
        Work.Diff.GE.SmoothField (I := I) (M := M) C →
        Work.Diff.GE.SmoothField (I := I) (M := M) D →
      MDifferentiableAt I (modelWithCornersSelf ℝ ℝ)
        (fun y : M ↦ Work.Diff.GE.lapRmAt g y (A y) (B y) (C y) (D y)) x)
    (hReactD : ∀ (g : Submission.Diff.SMet I M) (x : M)
      (A B C D : Π y : M, TangentSpace I y),
        Work.Diff.GE.SmoothField (I := I) (M := M) A →
        Work.Diff.GE.SmoothField (I := I) (M := M) B →
        Work.Diff.GE.SmoothField (I := I) (M := M) C →
        Work.Diff.GE.SmoothField (I := I) (M := M) D →
      MDifferentiableAt I (modelWithCornersSelf ℝ ℝ)
        (fun y : M ↦ Work.Diff.GE.reactionFormAt Work.Diff.GE.reactionMap
          g y (A y) (B y) (C y) (D y)) x)
    (hP13 : ∀ (G : ℝ → Submission.Diff.SMet I M) (T : ℝ), Submission.Diff.IsRicciFlow G T →
      ∀ t ∈ Set.Ioo 0 T, ∀ x : M, ∀ (p : Fin 4 → TangentSpace I x) (j : Fin 4)
        (w : ℝ → TangentSpace I x) (w' : TangentSpace I x),
      HasDerivAt w w' t →
      HasDerivAt
        (fun s ↦ Submission.Diff.rmP (G s) x ((Function.update p j (w s)) 0)
          ((Function.update p j (w s)) 1) ((Function.update p j (w s)) 2)
          ((Function.update p j (w s)) 3))
        (Work.Diff.GE.lapRmAt (G t) x ((Function.update p j (w t)) 0)
            ((Function.update p j (w t)) 1) ((Function.update p j (w t)) 2)
            ((Function.update p j (w t)) 3)
          + Work.Diff.GE.reactionFormAt Work.Diff.GE.reactionMap (G t) x
              ((Function.update p j (w t)) 0) ((Function.update p j (w t)) 1)
              ((Function.update p j (w t)) 2) ((Function.update p j (w t)) 3)
          + Submission.Diff.rmP (G t) x ((Function.update p j w') 0)
              ((Function.update p j w') 1) ((Function.update p j w') 2)
              ((Function.update p j w') 3)) t)
    (hWeit : ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : Submission.Diff.SMet I M) (x : M)
        (v a b c d : TangentSpace I x),
      |Work.Diff.GE.covLapRmAt g x v a b c d - Work.Diff.GE.lapCovRmAt g x v a b c d|
        ≤ C * Real.sqrt (Submission.Diff.rmNormSq g x)
            * Real.sqrt (Submission.Diff.dRmNormSq g x)
            * (Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x a a)
              * Real.sqrt (g.inner x b b) * Real.sqrt (g.inner x c c)
              * Real.sqrt (g.inner x d d)))
    (hReactB : ∃ C : ℝ, 0 ≤ C ∧ ∀ (G : ℝ → Submission.Diff.SMet I M) (T : ℝ),
        Submission.Diff.IsRicciFlow G T → ∀ t ∈ Set.Ico 0 T, ∀ x : M,
        ∀ v a b c d : TangentSpace I x,
        Work.Diff.GE.covReactionFormAt Work.Diff.GE.reactionMap (G t)
            x v a b c d
          ≤ C * Real.sqrt (Submission.Diff.rmNormSq (G t) x)
            * Real.sqrt (Submission.Diff.dRmNormSq (G t) x)
            * (Real.sqrt ((G t).inner x v v) * Real.sqrt ((G t).inner x a a)
              * Real.sqrt ((G t).inner x b b) * Real.sqrt ((G t).inner x c c)
              * Real.sqrt ((G t).inner x d d)))
    (hReactB2 : ∃ C : ℝ, 0 ≤ C ∧ ∀ (G : ℝ → Submission.Diff.SMet I M) (T : ℝ),
        Submission.Diff.IsRicciFlow G T → ∀ t ∈ Set.Ico 0 T, ∀ x : M,
        ∀ v a b c d : TangentSpace I x,
        Work.Diff.GE.covReactionFormAt (fun R ↦ -Work.Diff.GE.reactionMap R) (G t)
            x v a b c d
          ≤ C * Real.sqrt (Submission.Diff.rmNormSq (G t) x)
            * Real.sqrt (Submission.Diff.dRmNormSq (G t) x)
            * (Real.sqrt ((G t).inner x v v) * Real.sqrt ((G t).inner x a a)
              * Real.sqrt ((G t).inner x b b) * Real.sqrt ((G t).inner x c c)
              * Real.sqrt ((G t).inner x d d)))
    (hConn : ∃ C : ℝ, 0 ≤ C ∧ ∀ (G : ℝ → Submission.Diff.SMet I M) (T : ℝ),
      Submission.Diff.IsRicciFlow G T → ∀ t ∈ Set.Ioo 0 T, ∀ x : M,
      ∀ v a b c d : TangentSpace I x,
        ∃ wa wb wc wd : TangentSpace I x,
          Work.Diff.GE.IsConnVar G t x (Submission.Diff.smoothExt x v)
              (Submission.Diff.smoothExt x a) wa ∧
          Work.Diff.GE.IsConnVar G t x (Submission.Diff.smoothExt x v)
              (Submission.Diff.smoothExt x b) wb ∧
          Work.Diff.GE.IsConnVar G t x (Submission.Diff.smoothExt x v)
              (Submission.Diff.smoothExt x c) wc ∧
          Work.Diff.GE.IsConnVar G t x (Submission.Diff.smoothExt x v)
              (Submission.Diff.smoothExt x d) wd ∧
          |Submission.Diff.rmP (G t) x wa b c d + Submission.Diff.rmP (G t) x a wb c d
             + Submission.Diff.rmP (G t) x a b wc d + Submission.Diff.rmP (G t) x a b c wd|
            ≤ C * Real.sqrt (Submission.Diff.rmNormSq (G t) x)
              * Real.sqrt (Submission.Diff.dRmNormSq (G t) x)
              * (Real.sqrt ((G t).inner x v v) * Real.sqrt ((G t).inner x a a)
                * Real.sqrt ((G t).inner x b b) * Real.sqrt ((G t).inner x c c)
                * Real.sqrt ((G t).inner x d d))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (G : ℝ → Submission.Diff.SMet I M) (T : ℝ),
      Submission.Diff.IsRicciFlow G T → ∀ t ∈ Set.Ioo 0 T, ∀ x : M,
      ∀ v a b c d : TangentSpace I x,
      HasDerivWithinAt (fun s ↦ Submission.Diff.covRm (G s) x v a b c d)
        (Work.Diff.GE.covRmTimeDeriv Work.Diff.GE.reactionMap
          G t x v a b c d) (Set.Ico 0 T) t ∧
      |Work.Diff.GE.covRmTimeDeriv Work.Diff.GE.reactionMap
            G t x v a b c d - Work.Diff.GE.lapCovRmAt (G t) x v a b c d|
        ≤ C * Real.sqrt (Submission.Diff.rmNormSq (G t) x)
          * Real.sqrt (Submission.Diff.dRmNormSq (G t) x)
          * (Real.sqrt ((G t).inner x v v) * Real.sqrt ((G t).inner x a a)
             * Real.sqrt ((G t).inner x b b) * Real.sqrt ((G t).inner x c c)
             * Real.sqrt ((G t).inner x d d)) := by
  obtain ⟨Cw, hCw0, hWeit'⟩ := hWeit
  obtain ⟨Cb, hCb0, hReactB'⟩ := hReactB
  obtain ⟨Cb2, hCb20, hReactB2'⟩ := hReactB2
  obtain ⟨Cc, hCc0, hConn'⟩ := hConn
  refine ⟨Cw + max Cb Cb2 + Cc, by positivity, ?_⟩
  intro G T hflow t ht x v a b c d
  -- the model-space structure on the tangent space (`TangentSpace I x` is a type synonym for `E`,
  -- which type class inference does not unfold)
  letI hAT : AddTorsor (TangentSpace I x) (TangentSpace I x) := inferInstance
  letI hNAG : NormedAddCommGroup (TangentSpace I x) :=
    (inferInstanceAs (NormedAddCommGroup E) : NormedAddCommGroup E)
  letI hNS : NormedSpace ℝ (TangentSpace I x) :=
    (inferInstanceAs (NormedSpace ℝ E) : NormedSpace ℝ E)
  letI hFD : FiniteDimensional ℝ (TangentSpace I x) :=
    (inferInstanceAs (FiniteDimensional ℝ E) : FiniteDimensional ℝ E)
  have hAa : SmoothField (I := I) (M := M) (smoothExt x a) := smoothExt_cmdiff x a
  have hAb : SmoothField (I := I) (M := M) (smoothExt x b) := smoothExt_cmdiff x b
  have hAc : SmoothField (I := I) (M := M) (smoothExt x c) := smoothExt_cmdiff x c
  have hAd : SmoothField (I := I) (M := M) (smoothExt x d) := smoothExt_cmdiff x d
  have hJs : JointSmooth G (Set.Ioo 0 T) :=
    hflow.1.mono (Set.prod_mono Set.Ioo_subset_Ico_self (Set.subset_univ _))
  -- ### the main term, via Clairaut
  have hM := Work.Diff.GE.FixAsm.mvfderiv_rmP_timeDeriv (I := I) (M := M) hLC hLV G T hflow ht x v
    (smoothExt x a) (smoothExt x b) (smoothExt x c) (smoothExt x d) hAa hAb hAc hAd
  -- ### the split of the `mvfderiv` of the sum
  have hsplit : mvfderiv I (fun y : M ↦ Work.Diff.GE.lapRmAt (G t) y (smoothExt x a y)
        (smoothExt x b y) (smoothExt x c y) (smoothExt x d y)
      + Work.Diff.GE.reactionFormAt Work.Diff.GE.reactionMap (G t) y (smoothExt x a y)
        (smoothExt x b y) (smoothExt x c y) (smoothExt x d y)) x v
      = mvfderiv I (fun y : M ↦ Work.Diff.GE.lapRmAt (G t) y (smoothExt x a y)
          (smoothExt x b y) (smoothExt x c y) (smoothExt x d y)) x v
        + mvfderiv I (fun y : M ↦ Work.Diff.GE.reactionFormAt Work.Diff.GE.reactionMap (G t) y
          (smoothExt x a y) (smoothExt x b y) (smoothExt x c y) (smoothExt x d y)) x v := by
    change mvfderiv I
        ((fun y : M ↦ Work.Diff.GE.lapRmAt (G t) y (smoothExt x a y) (smoothExt x b y)
          (smoothExt x c y) (smoothExt x d y))
          + (fun y : M ↦ Work.Diff.GE.reactionFormAt Work.Diff.GE.reactionMap (G t) y
            (smoothExt x a y) (smoothExt x b y) (smoothExt x c y) (smoothExt x d y))) x v
      = mvfderiv I (fun y : M ↦ Work.Diff.GE.lapRmAt (G t) y (smoothExt x a y)
          (smoothExt x b y) (smoothExt x c y) (smoothExt x d y)) x v
        + mvfderiv I (fun y : M ↦ Work.Diff.GE.reactionFormAt Work.Diff.GE.reactionMap (G t) y
          (smoothExt x a y) (smoothExt x b y) (smoothExt x c y) (smoothExt x d y)) x v
    have h := congrArg (fun (L : TangentSpace I x →L[ℝ] ℝ) ↦ L v)
      (mvfderiv_add
        (hLapD (G t) x (smoothExt x a) (smoothExt x b) (smoothExt x c) (smoothExt x d)
          hAa hAb hAc hAd)
        (hReactD (G t) x (smoothExt x a) (smoothExt x b) (smoothExt x c) (smoothExt x d)
          hAa hAb hAc hAd))
    simpa only [ContinuousLinearMap.add_apply] using h
  rw [hsplit] at hM
  -- ### the four connection-variation curves
  obtain ⟨ua, hua, huaI⟩ := hLV G (Set.Ioo 0 T) isOpen_Ioo hJs t ht (smoothExt x v)
    (smoothExt x a) (smoothExt_cmdiff x v) (smoothExt_cmdiff x a) x
  obtain ⟨ub, hub, hubI⟩ := hLV G (Set.Ioo 0 T) isOpen_Ioo hJs t ht (smoothExt x v)
    (smoothExt x b) (smoothExt_cmdiff x v) (smoothExt_cmdiff x b) x
  obtain ⟨uc, huc, hucI⟩ := hLV G (Set.Ioo 0 T) isOpen_Ioo hJs t ht (smoothExt x v)
    (smoothExt x c) (smoothExt_cmdiff x v) (smoothExt_cmdiff x c) x
  obtain ⟨ud, hud, hudI⟩ := hLV G (Set.Ioo 0 T) isOpen_Ioo hJs t ht (smoothExt x v)
    (smoothExt x d) (smoothExt_cmdiff x v) (smoothExt_cmdiff x d) x
  -- the same curves, in the tangent-space world
  have hwa : HasDerivAt (fun s : ℝ ↦
      (Submission.Diff.lcOf (G s) (smoothExt x a) x v : TangentSpace I x))
      (ua : TangentSpace I x) t := by
    have h := hua
    rw [smoothExt_apply x v] at h
    exact h
  have hwb : HasDerivAt (fun s : ℝ ↦
      (Submission.Diff.lcOf (G s) (smoothExt x b) x v : TangentSpace I x))
      (ub : TangentSpace I x) t := by
    have h := hub
    rw [smoothExt_apply x v] at h
    exact h
  have hwc : HasDerivAt (fun s : ℝ ↦
      (Submission.Diff.lcOf (G s) (smoothExt x c) x v : TangentSpace I x))
      (uc : TangentSpace I x) t := by
    have h := huc
    rw [smoothExt_apply x v] at h
    exact h
  have hwd : HasDerivAt (fun s : ℝ ↦
      (Submission.Diff.lcOf (G s) (smoothExt x d) x v : TangentSpace I x))
      (ud : TangentSpace I x) t := by
    have h := hud
    rw [smoothExt_apply x v] at h
    exact h
  -- the `E`-valued versions, for the `deriv`-identities
  have hcua : HasDerivAt (connVar G x a v) (ua : TangentSpace I x) t := by
    have h := hua
    rw [smoothExt_apply x v] at h
    exact h
  have hcub : HasDerivAt (connVar G x b v) (ub : TangentSpace I x) t := by
    have h := hub
    rw [smoothExt_apply x v] at h
    exact h
  have hcuc : HasDerivAt (connVar G x c v) (uc : TangentSpace I x) t := by
    have h := huc
    rw [smoothExt_apply x v] at h
    exact h
  have hcud : HasDerivAt (connVar G x d v) (ud : TangentSpace I x) t := by
    have h := hud
    rw [smoothExt_apply x v] at h
    exact h
  -- ### the four correction terms
  have hP0 : HasDerivAt (fun s ↦ Submission.Diff.rmP (G s) x
        (Submission.Diff.lcOf (G s) (smoothExt x a) x v : TangentSpace I x) b c d)
      (Work.Diff.GE.lapRmAt (G t) x
          (Submission.Diff.lcOf (G t) (smoothExt x a) x v : TangentSpace I x) b c d
        + Work.Diff.GE.reactionFormAt Work.Diff.GE.reactionMap (G t) x
            (Submission.Diff.lcOf (G t) (smoothExt x a) x v : TangentSpace I x) b c d
        + Submission.Diff.rmP (G t) x ua b c d) t := by
    have h := hP13 G T hflow t ht x ![a, b, c, d] (0 : Fin 4)
      (fun s : ℝ ↦ (Submission.Diff.lcOf (G s) (smoothExt x a) x v : TangentSpace I x))
      (ua : TangentSpace I x) hwa
    simpa only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, Fin.mk_one,
      Fin.reduceFinMk, fm_vec4_zero, fm_vec4_one, fm_vec4_two, fm_vec4_three] using h
  have hP1 : HasDerivAt (fun s ↦ Submission.Diff.rmP (G s) x a
        (Submission.Diff.lcOf (G s) (smoothExt x b) x v : TangentSpace I x) c d)
      (Work.Diff.GE.lapRmAt (G t) x a
          (Submission.Diff.lcOf (G t) (smoothExt x b) x v : TangentSpace I x) c d
        + Work.Diff.GE.reactionFormAt Work.Diff.GE.reactionMap (G t) x a
            (Submission.Diff.lcOf (G t) (smoothExt x b) x v : TangentSpace I x) c d
        + Submission.Diff.rmP (G t) x a ub c d) t := by
    have h := hP13 G T hflow t ht x ![a, b, c, d] (1 : Fin 4)
      (fun s : ℝ ↦ (Submission.Diff.lcOf (G s) (smoothExt x b) x v : TangentSpace I x))
      (ub : TangentSpace I x) hwb
    simpa only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, Fin.mk_one,
      Fin.reduceFinMk, fm_vec4_zero, fm_vec4_one, fm_vec4_two, fm_vec4_three] using h
  have hP2 : HasDerivAt (fun s ↦ Submission.Diff.rmP (G s) x a b
        (Submission.Diff.lcOf (G s) (smoothExt x c) x v : TangentSpace I x) d)
      (Work.Diff.GE.lapRmAt (G t) x a b
          (Submission.Diff.lcOf (G t) (smoothExt x c) x v : TangentSpace I x) d
        + Work.Diff.GE.reactionFormAt Work.Diff.GE.reactionMap (G t) x a b
            (Submission.Diff.lcOf (G t) (smoothExt x c) x v : TangentSpace I x) d
        + Submission.Diff.rmP (G t) x a b uc d) t := by
    have h := hP13 G T hflow t ht x ![a, b, c, d] (2 : Fin 4)
      (fun s : ℝ ↦ (Submission.Diff.lcOf (G s) (smoothExt x c) x v : TangentSpace I x))
      (uc : TangentSpace I x) hwc
    simpa only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, Fin.mk_one,
      Fin.reduceFinMk, fm_vec4_zero, fm_vec4_one, fm_vec4_two, fm_vec4_three] using h
  have hP3 : HasDerivAt (fun s ↦ Submission.Diff.rmP (G s) x a b c
        (Submission.Diff.lcOf (G s) (smoothExt x d) x v : TangentSpace I x))
      (Work.Diff.GE.lapRmAt (G t) x a b c
          (Submission.Diff.lcOf (G t) (smoothExt x d) x v : TangentSpace I x)
        + Work.Diff.GE.reactionFormAt Work.Diff.GE.reactionMap (G t) x a b c
            (Submission.Diff.lcOf (G t) (smoothExt x d) x v : TangentSpace I x)
        + Submission.Diff.rmP (G t) x a b c ud) t := by
    have h := hP13 G T hflow t ht x ![a, b, c, d] (3 : Fin 4)
      (fun s : ℝ ↦ (Submission.Diff.lcOf (G s) (smoothExt x d) x v : TangentSpace I x))
      (ud : TangentSpace I x) hwd
    simpa only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, Fin.mk_one,
      Fin.reduceFinMk, fm_vec4_zero, fm_vec4_one, fm_vec4_two, fm_vec4_three] using h
  -- ### the value of the derivative
  have hda : deriv (connVar G x a v) t = ua := hcua.deriv
  have hdb : deriv (connVar G x b v) t = ub := hcub.deriv
  have hdc : deriv (connVar G x c v) t = uc := hcuc.deriv
  have hdd : deriv (connVar G x d v) t = ud := hcud.deriv
  have hval : (mvfderiv I (fun y : M ↦ Work.Diff.GE.lapRmAt (G t) y (smoothExt x a y)
        (smoothExt x b y) (smoothExt x c y) (smoothExt x d y)) x v
      + mvfderiv I (fun y : M ↦ Work.Diff.GE.reactionFormAt Work.Diff.GE.reactionMap (G t) y
        (smoothExt x a y) (smoothExt x b y) (smoothExt x c y) (smoothExt x d y)) x v)
      - (Work.Diff.GE.lapRmAt (G t) x
          (Submission.Diff.lcOf (G t) (smoothExt x a) x v : TangentSpace I x) b c d
        + Work.Diff.GE.reactionFormAt Work.Diff.GE.reactionMap (G t) x
            (Submission.Diff.lcOf (G t) (smoothExt x a) x v : TangentSpace I x) b c d
        + Submission.Diff.rmP (G t) x ua b c d)
      - (Work.Diff.GE.lapRmAt (G t) x a
          (Submission.Diff.lcOf (G t) (smoothExt x b) x v : TangentSpace I x) c d
        + Work.Diff.GE.reactionFormAt Work.Diff.GE.reactionMap (G t) x a
            (Submission.Diff.lcOf (G t) (smoothExt x b) x v : TangentSpace I x) c d
        + Submission.Diff.rmP (G t) x a ub c d)
      - (Work.Diff.GE.lapRmAt (G t) x a b
          (Submission.Diff.lcOf (G t) (smoothExt x c) x v : TangentSpace I x) d
        + Work.Diff.GE.reactionFormAt Work.Diff.GE.reactionMap (G t) x a b
            (Submission.Diff.lcOf (G t) (smoothExt x c) x v : TangentSpace I x) d
        + Submission.Diff.rmP (G t) x a b uc d)
      - (Work.Diff.GE.lapRmAt (G t) x a b c
          (Submission.Diff.lcOf (G t) (smoothExt x d) x v : TangentSpace I x)
        + Work.Diff.GE.reactionFormAt Work.Diff.GE.reactionMap (G t) x a b c
            (Submission.Diff.lcOf (G t) (smoothExt x d) x v : TangentSpace I x)
        + Submission.Diff.rmP (G t) x a b c ud)
      = Work.Diff.GE.covRmTimeDeriv Work.Diff.GE.reactionMap G t x v a b c d := by
    simp only [Work.Diff.GE.covRmTimeDeriv, Work.Diff.GE.covLapRmAt,
      Work.Diff.GE.covReactionFormAt, hda, hdb, hdc, hdd]
    ring
  -- ### the function identity
  have hfun : ((fun s : ℝ ↦ mvfderiv I (fun y : M ↦ Submission.Diff.rmP (G s) y
          (smoothExt x a y) (smoothExt x b y) (smoothExt x c y) (smoothExt x d y)) x v)
        - (fun s : ℝ ↦ Submission.Diff.rmP (G s) x
            (Submission.Diff.lcOf (G s) (smoothExt x a) x v : TangentSpace I x) b c d)
        - (fun s : ℝ ↦ Submission.Diff.rmP (G s) x a
            (Submission.Diff.lcOf (G s) (smoothExt x b) x v : TangentSpace I x) c d)
        - (fun s : ℝ ↦ Submission.Diff.rmP (G s) x a b
            (Submission.Diff.lcOf (G s) (smoothExt x c) x v : TangentSpace I x) d)
        - (fun s : ℝ ↦ Submission.Diff.rmP (G s) x a b c
            (Submission.Diff.lcOf (G s) (smoothExt x d) x v : TangentSpace I x)))
      = (fun s : ℝ ↦ Submission.Diff.covRm (G s) x v a b c d) := by
    funext s
    simp only [Pi.sub_apply, Submission.Diff.covRm]
  have hcomb := (((hM.sub hP0.hasDerivWithinAt).sub hP1.hasDerivWithinAt).sub
    hP2.hasDerivWithinAt).sub hP3.hasDerivWithinAt
  rw [hfun] at hcomb
  rw [hval] at hcomb
  refine ⟨hcomb, ?_⟩
  -- ### the bound
  obtain ⟨wa, wb, wc, wd, hwaI, hwbI, hwcI, hwdI, hconnbound⟩ :=
    hConn' G T hflow t ht x v a b c d
  have hua_eq : ua = wa := fm_IsConnVar_unique huaI hwaI
  have hub_eq : ub = wb := fm_IsConnVar_unique hubI hwbI
  have huc_eq : uc = wc := fm_IsConnVar_unique hucI hwcI
  have hud_eq : ud = wd := fm_IsConnVar_unique hudI hwdI
  have hda' : deriv (connVar G x a v) t = wa := by rw [hda, hua_eq]
  have hdb' : deriv (connVar G x b v) t = wb := by rw [hdb, hub_eq]
  have hdc' : deriv (connVar G x c v) t = wc := by rw [hdc, huc_eq]
  have hdd' : deriv (connVar G x d v) t = wd := by rw [hdd, hud_eq]
  rw [Work.Diff.GE.covRmTimeDeriv, hda', hdb', hdc', hdd']
  -- the product constant
  set P : ℝ := Real.sqrt (Submission.Diff.rmNormSq (G t) x)
      * Real.sqrt (Submission.Diff.dRmNormSq (G t) x)
      * (Real.sqrt ((G t).inner x v v) * Real.sqrt ((G t).inner x a a)
        * Real.sqrt ((G t).inner x b b) * Real.sqrt ((G t).inner x c c)
        * Real.sqrt ((G t).inner x d d)) with hPdef
  have hPnn : 0 ≤ P := by rw [hPdef]; positivity
  have hPmul : ∀ s : ℝ, s * Real.sqrt (Submission.Diff.rmNormSq (G t) x)
      * Real.sqrt (Submission.Diff.dRmNormSq (G t) x)
      * (Real.sqrt ((G t).inner x v v) * Real.sqrt ((G t).inner x a a)
        * Real.sqrt ((G t).inner x b b) * Real.sqrt ((G t).inner x c c)
        * Real.sqrt ((G t).inner x d d)) = s * P := by
    intro s
    rw [hPdef]
    ring
  rw [hPmul (Cw + max Cb Cb2 + Cc)]
  have hW := hWeit' (G t) x v a b c d
  have hR := hReactB' G T hflow t ⟨ht.1.le, ht.2⟩ x v a b c d
  have hR2 := hReactB2' G T hflow t ⟨ht.1.le, ht.2⟩ x v a b c d
  rw [fm_covReactionFormAt_neg] at hR2
  rw [hPmul Cw] at hW
  rw [hPmul Cb] at hR
  rw [hPmul Cb2] at hR2
  have hA1 : Work.Diff.GE.covLapRmAt (G t) x v a b c d - Work.Diff.GE.lapCovRmAt (G t) x v a b c d
      ≤ Cw * P := (abs_le.mp hW).2
  have hA2 : -(Work.Diff.GE.covLapRmAt (G t) x v a b c d
      - Work.Diff.GE.lapCovRmAt (G t) x v a b c d) ≤ Cw * P := by
    have h := (abs_le.mp hW).1
    linarith
  have hB1 : Work.Diff.GE.covReactionFormAt Work.Diff.GE.reactionMap (G t) x v a b c d
      ≤ max Cb Cb2 * P :=
    le_trans hR (mul_le_mul_of_nonneg_right (le_max_left Cb Cb2) hPnn)
  have hB2 : -(Work.Diff.GE.covReactionFormAt Work.Diff.GE.reactionMap (G t) x v a b c d)
      ≤ max Cb Cb2 * P :=
    le_trans hR2 (mul_le_mul_of_nonneg_right (le_max_right Cb Cb2) hPnn)
  have hS1 : Submission.Diff.rmP (G t) x wa b c d + Submission.Diff.rmP (G t) x a wb c d
      + Submission.Diff.rmP (G t) x a b wc d + Submission.Diff.rmP (G t) x a b c wd
      ≤ Cc * P := by
    rw [hPmul Cc] at hconnbound
    exact (abs_le.mp hconnbound).2
  have hS2 : -(Submission.Diff.rmP (G t) x wa b c d + Submission.Diff.rmP (G t) x a wb c d
      + Submission.Diff.rmP (G t) x a b wc d + Submission.Diff.rmP (G t) x a b c wd)
      ≤ Cc * P := by
    rw [hPmul Cc] at hconnbound
    have h := (abs_le.mp hconnbound).1
    linarith
  rw [show Work.Diff.GE.covLapRmAt (G t) x v a b c d
      + Work.Diff.GE.covReactionFormAt Work.Diff.GE.reactionMap (G t) x v a b c d
      - Submission.Diff.rmP (G t) x wa b c d - Submission.Diff.rmP (G t) x a wb c d
      - Submission.Diff.rmP (G t) x a b wc d - Submission.Diff.rmP (G t) x a b c wd
      - Work.Diff.GE.lapCovRmAt (G t) x v a b c d
      = (Work.Diff.GE.covLapRmAt (G t) x v a b c d
          - Work.Diff.GE.lapCovRmAt (G t) x v a b c d)
        + Work.Diff.GE.covReactionFormAt Work.Diff.GE.reactionMap (G t) x v a b c d
        - (Submission.Diff.rmP (G t) x wa b c d + Submission.Diff.rmP (G t) x a wb c d
          + Submission.Diff.rmP (G t) x a b wc d + Submission.Diff.rmP (G t) x a b c wd)
      from by ring]
  rw [abs_le]
  constructor
  · nlinarith [hA1, hB1, hS2]
  · nlinarith [hA2, hB2, hS1]

end Work.Diff.GE
