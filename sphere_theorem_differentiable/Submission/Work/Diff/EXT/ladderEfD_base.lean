import Mathlib
import Submission.Work.Diff.EXT.ladderEfDefs
import Submission.Work.Diff.EXT.reaction0_jets
import Submission.Work.Diff.EXT.towerReactDefs
import Submission.Work.Diff.EXT.reactDefs
import Submission.Work.Diff.EXT.lapCovKRm_one_eq_lapCovRmAt
import Submission.Work.Diff.EXT.evolX.ladderPlumb
import Submission.Work.Diff.GE.EvolA.rmP_evol_fixed
import Submission.Work.Diff.GE.lapRmAt_zero_continuous
import Submission.Work.Diff.GE.lapRmAt_trace
import Submission.Work.Diff.GE.derivWithin_Ico_zero
import Submission.Work.Diff.GE.continuousWithinAt_rmP_zero
import Submission.Work.Diff.GE.uhlenbeck_frame_kit
import Submission.Work.Diff.GE.react.rmReact_contDiff
import Submission.Work.Diff.EXT.reactionMap_rot
import Submission.Work.Diff.GE.Rfa.reactionFormAtE_frame_indep
import Submission.Work.Diff.T.lc_variation
import Submission.Work.EXT.lcSmooth_noBoundary

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The base case of the reaction ladder (`Work.Diff.EXT.ladderEfD_base`)

`Work.Diff.EXT.LadderEfD G t x Ef 0 j C` is the ladder invariant at level `0` and jet order `j`
for the reaction of the Ricci flow `G` at time `t`, traced in the frame field `Ef`:

`R_0 = ∂ₜ⁺Rm − ΔRm`, and the invariant bounds its `j`-th covariant derivative at `x` by
`C · Shape (G t) x j` times the metric norms of the tuple.

The level-`0` reaction is, near every point, the *quadratic* expression `Q(Rm)` of the curvature
(the fixed-vector curvature evolution), so its jets are the jets of the quadratic reaction
`reactionFormAt reactionMap`: that is `Work.Diff.EXT.reaction0_jets`, and the whole content of this
file is the reduction of the ladder invariant at level `0` to that lemma, namely

* the **germ identity** `Work.Diff.EXT.reactOpEfD_zero_eventuallyEq_reaction`: for a Ricci flow `G`,
  `t ∈ [0,T)`, a frame field `Ef` which is orthonormal near `x` and every *smooth* tuple `F`, the
  operator `reactOpEfD Ef G t 0` agrees, near `x`, with `reactionFormAt reactionMap (G t)`;
* its two ingredients: the **one-sided fixed-vector curvature evolution** on the whole half-open
  interval `[0,T)` (`Work.Diff.EXT.rmP_derivWithin_Ioi_ladder`), and the **trace identity**
  (`Work.Diff.EXT.sum_ckt_two_eq_lapRmAt`: the rough Laplacian of the curvature traced in the
  fields `Ef m` is the `onFrame`-traced Laplacian `lapRmAt` when `Ef` is orthonormal);
* the **transfer of the jet bound** through the germ identity, in the *smooth-tuple* form
  `Work.Diff.EXT.jetAll_congr_of_eventuallyEq_smooth` of the locality of the jets (the tower `ckt`
  is tensorial only for smooth fields, so the operator `reactOpEfD` is only identifiable with
  `Q(Rm)` on smooth tuples — which is all that is needed, the ladder being evaluated on the smooth
  extensions `smoothExt x ·`).
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.EXT

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-! ## Level two of the tower is `∇²Rm` -/

/-- **Level two of the tower is `∇²Rm`.**  For globally `C^∞` fields `X`, `Y`, `F 0, …, F 3`, the
tower value `ckt g 2 (X, Y, F 0, …, F 3)` at `x` is the `(0,6)`-tensor `∇²Rm` contracted with the
values of the fields.  This is `Work.Diff.EXT.ckt_eq_covKRmExt` (the tower is `covKRmExt`) followed
by the proved level-`2` bridge `Work.Diff.GE.cov2Rm_eq_covKRmExt_two`. -/
theorem ckt_two_eq_cov2Rm_ladder
    [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : SMet I M) (x : M)
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
    fin_cases i <;> first
      | rfl
      | (simp only [Fin.cons_zero, Fin.cons_succ, Fin.reduceEq, ↓reduceIte])
  have hslot : ∀ j : Fin 4,
      ((Fin.cons X (Fin.cons Y F) : Fin 6 → TField (I := I) (M := M)) (Fin.natAdd 2 j)) = F j := by
    intro j
    fin_cases j <;> rfl
  simp only [htuple, hslot]
  exact (Work.Diff.GE.cov2Rm_eq_covKRmExt_two (I := I) (M := M) hLC g x hX hY
    (hF 0) (hF 1) (hF 2) (hF 3)).symm

/-! ## The rough Laplacian traced in a frame field -/

/-- **The rough Laplacian of the curvature, traced in an orthonormal frame field.**  If the fields
`Ef m` are `g`-orthonormal at `x`, then the trace `∑ m, ∇_{Ef m}∇_{Ef m}Rm` of the second covariant
derivative of the curvature, computed through the tower, is the `onFrame`-traced Laplacian
`Work.Diff.GE.lapRmAt g x`. -/
theorem sum_ckt_two_eq_lapRmAt
    [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : SMet I M) (x : M)
    {Ef : Fin (Module.finrank ℝ E) → TField (I := I) (M := M)}
    (hEf : ∀ i, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (Ef i))
    (hON : Submission.Diff.IsONFrame g x (fun i => Ef i x))
    {F : Fin 4 → TField (I := I) (M := M)}
    (hF : ∀ i, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (F i)) :
    (∑ m : Fin (Module.finrank ℝ E),
        ckt g 2 (Fin.cons (Ef m) (Fin.cons (Ef m) F)) x)
      = Work.Diff.GE.lapRmAt g x (F 0 x) (F 1 x) (F 2 x) (F 3 x) := by
  refine Eq.trans (Finset.sum_congr rfl (fun m _ => ckt_two_eq_cov2Rm_ladder (I := I) (M := M) hLC g x
    (hEf m) (hEf m) hF)) ?_
  exact (Work.Diff.GE.lapRmAt_trace (I := I) (M := M) hLC g x (fun i => Ef i x) hON
    (F 0 x) (F 1 x) (F 2 x) (F 3 x)).symm

/-! ## Continuity of the reaction at the initial time

The reaction `reactionFormAt reactionMap` is computed in the `Classical.epsilon`-chosen frame
`onFrame (G s) y`, which is *not* continuous in `s`; but its value is frame independent, so along a
Ricci flow (where the Uhlenbeck frame `Work.Diff.GE.uhlenbeck_frame_exists_kit` provides a family of
`G s`-orthonormal frames which is differentiable, hence continuous, at `0`) it is continuous from
the right at `0`. -/

/-- **A finite sum of functions continuous within a set is continuous within the set.** -/
private theorem continuousWithinAt_sum_fintype {ι : Type*} [Fintype ι] {f : ι → ℝ → ℝ}
    {s : Set ℝ} {x : ℝ} (h : ∀ i, ContinuousWithinAt (f i) s x) :
    ContinuousWithinAt (fun t => ∑ i, f i t) s x := by
  show Tendsto (fun t => ∑ i, f i t) (𝓝[s] x) (𝓝 (∑ i, f i x))
  simpa using tendsto_finsetSum (Finset.univ : Finset ι) (fun i _ => h i)

/-- **Composition of a curve continuous within a set with a globally continuous map.** -/
private theorem continuousWithinAt_comp_continuous {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] {f : ℝ → α} {g : α → β} {s : Set ℝ} {x : ℝ}
    (hg : Continuous g) (hf : ContinuousWithinAt f s x) :
    ContinuousWithinAt (fun t => g (f t)) s x := by
  show ContinuousWithinAt (g ∘ f) s x
  exact hg.continuousWithinAt.comp (t := Set.univ) hf (fun _ _ => trivial)

/-- The coordinates of a curve in a basis are continuous. -/
private theorem coord_continuousWithinAt {n : ℕ} {y : M}
    (b : Module.Basis (Fin n) ℝ (TangentSpace I y))
    {c : ℝ → TangentSpace I y} {s : Set ℝ} {x : ℝ} (hc : ContinuousWithinAt c s x) (i : Fin n) :
    ContinuousWithinAt (fun t => (b.repr (c t)) i) s x := by
  have hfun : (fun t => (b.repr (c t)) i) = (⇑(b.coord i) ∘ c) := by
    funext t
    rw [Function.comp_apply, Module.Basis.coord_apply]
  rw [hfun]
  exact (LinearMap.continuous_of_finiteDimensional (b.coord i)).continuousWithinAt.comp
    (t := Set.univ) hc (fun _ _ => trivial)

/-- The metric pairing of a fixed vector with a curve of vectors is continuous from the right at `0`
along a Ricci flow (the metric is only jointly smooth on `[0,T)`, whence the flow equation). -/
private theorem inner_curve_continuousWithinAt_zero [I.Boundaryless] [T2Space M] [CompactSpace M]
    {G : ℝ → SMet I M} {T : ℝ} (hflow : IsRicciFlow G T) (hT : 0 < T) (y : M)
    (a : TangentSpace I y) {c : ℝ → TangentSpace I y}
    (hc : ContinuousWithinAt c (Set.Ico 0 T) 0) :
    ContinuousWithinAt (fun s => (G s).inner y (c s) a) (Set.Ico 0 T) 0 := by
  classical
  set b := Module.finBasis ℝ (TangentSpace I y) with hb
  have hexp : ∀ s, (G s).inner y (c s) a
      = ∑ i, (b.repr (c s)) i * ((G s).inner y (b i)) a := by
    intro s
    conv_lhs => rw [← Module.Basis.sum_repr b (c s)]
    simp only [map_sum, ContinuousLinearMap.sum_apply, map_smul, ContinuousLinearMap.smul_apply,
      smul_eq_mul]
  refine ContinuousWithinAt.congr_of_eventuallyEq ?_ (Filter.Eventually.of_forall hexp) (hexp 0)
  refine continuousWithinAt_sum_fintype (fun i => ?_)
  exact (coord_continuousWithinAt b hc i).mul
    ((hflow.2 0 ⟨le_refl 0, hT⟩ y (b i) a).continuousWithinAt)

/-- The curvature component `rmP (G s) y (c s) (d s) (e s) (f s)` along four continuous curves of
vectors is continuous from the right at `0` along a Ricci flow (multilinearity in the four arguments
reduces this to the fixed-vector statement `continuousWithinAt_rmP_zero`). -/
private theorem rmP_curve_continuousWithinAt_zero [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : LCSmooth I M) {G : ℝ → SMet I M} {T : ℝ} (hflow : IsRicciFlow G T)
    (y : M) {c d e' f' : ℝ → TangentSpace I y}
    (hc : ContinuousWithinAt c (Set.Ico 0 T) 0) (hd : ContinuousWithinAt d (Set.Ico 0 T) 0)
    (he : ContinuousWithinAt e' (Set.Ico 0 T) 0) (hf : ContinuousWithinAt f' (Set.Ico 0 T) 0) :
    ContinuousWithinAt (fun s => rmP (G s) y (c s) (d s) (e' s) (f' s)) (Set.Ico 0 T) 0 := by
  classical
  set b := Module.finBasis ℝ (TangentSpace I y) with hb
  have hexp : ∀ s, rmP (G s) y (c s) (d s) (e' s) (f' s)
      = ∑ i, ∑ j, ∑ k, ∑ l, (b.repr (c s)) i * (b.repr (d s)) j * (b.repr (e' s)) k
          * (b.repr (f' s)) l * rmP (G s) y (b i) (b j) (b k) (b l) := by
    intro s
    exact Work.Diff.GE.EvolA.expand_apply_of_basis (I := I) (M := M) y
      (fun i u => (b.repr u) i) b (fun u => (Module.Basis.sum_repr b u).symm)
      (fun a b c d => rmP (G s) y a b c d)
      (fun r s' u v b' c' d' =>
        Work.Diff.GE.EvolA.rmP_lin_fst (I := I) (M := M) hLC (G s) y r s' u v b' c' d')
      (fun r s' a u v c' d' =>
        Work.Diff.GE.EvolA.rmP_lin_snd (I := I) (M := M) hLC (G s) y r s' a u v c' d')
      (fun r s' a b' u v d' =>
        Work.Diff.GE.EvolA.rmP_lin_thd (I := I) (M := M) hLC (G s) y r s' a b' u v d')
      (fun r s' a b' c' u v =>
        Work.Diff.GE.EvolA.rmP_lin_fth (I := I) (M := M) hLC (G s) y r s' a b' c' u v)
      (c s) (d s) (e' s) (f' s)
  refine ContinuousWithinAt.congr_of_eventuallyEq ?_ (Filter.Eventually.of_forall hexp) (hexp 0)
  refine continuousWithinAt_sum_fintype (fun i => ?_)
  refine continuousWithinAt_sum_fintype (fun j => ?_)
  refine continuousWithinAt_sum_fintype (fun k => ?_)
  refine continuousWithinAt_sum_fintype (fun l => ?_)
  refine ContinuousWithinAt.mul (ContinuousWithinAt.mul (ContinuousWithinAt.mul
    (ContinuousWithinAt.mul (coord_continuousWithinAt b hc i) (coord_continuousWithinAt b hd j))
    (coord_continuousWithinAt b he k)) (coord_continuousWithinAt b hf l)) ?_
  exact Work.Diff.GE.continuousWithinAt_rmP_zero (I := I) (M := M) hLC hflow y
    (b i) (b j) (b k) (b l)

/-- The curvature array in a continuous family of frames is continuous from the right at `0`. -/
private theorem rmFrame_curve_continuousWithinAt_zero [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : LCSmooth I M) {G : ℝ → SMet I M} {T : ℝ} (hflow : IsRicciFlow G T)
    (y : M) {e : ℝ → Fin (Module.finrank ℝ E) → TangentSpace I y}
    (hec : ∀ i, ContinuousWithinAt (fun s => e s i) (Set.Ico 0 T) 0) :
    ContinuousWithinAt (fun s => Submission.Diff.rmFrame (G s) y (fun i => e s i))
      (Set.Ico 0 T) 0 := by
  rw [continuousWithinAt_pi]
  intro i
  rw [continuousWithinAt_pi]
  intro j
  rw [continuousWithinAt_pi]
  intro k
  rw [continuousWithinAt_pi]
  intro l
  show ContinuousWithinAt (fun s => rmP (G s) y (e s i) (e s j) (e s k) (e s l))
    (Set.Ico 0 T) 0
  exact rmP_curve_continuousWithinAt_zero (I := I) (M := M) hLC hflow y
    (hec i) (hec j) (hec k) (hec l)

/-- **The reaction is continuous from the right at the initial time.**  For a Ricci flow `G` on
`[0,T)`, fixed vectors `a b c d` at `y`, the value `reactionFormAt reactionMap (G s) y a b c d`
tends to its value at `0` as `s ↓ 0` within `[0,T)`. -/
theorem reactionFormAt_continuousWithinAt_zero [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : LCSmooth I M) {G : ℝ → SMet I M} {T : ℝ} (hflow : IsRicciFlow G T)
    (y : M) (a b c d : TangentSpace I y) :
    ContinuousWithinAt
      (fun s : ℝ => Work.Diff.GE.reactionFormAt Work.Diff.GE.reactionMap (G s) y a b c d)
      (Set.Ico 0 T) 0 := by
  by_cases hT : T ≤ 0
  · rw [Set.Ico_eq_empty_iff.mpr (not_lt.mpr hT)]
    simp [ContinuousWithinAt, nhdsWithin_empty]
  · have hTpos : 0 < T := not_le.mp hT
    obtain ⟨e, hON, hder⟩ :=
      Work.Diff.GE.uhlenbeck_frame_kit (I := I) (M := M) hLC G T hflow 0
        ⟨le_refl 0, hTpos⟩ y
    have hec : ∀ i, ContinuousWithinAt (fun s => e s i) (Set.Ico 0 T) 0 :=
      fun i => (hder i).continuousWithinAt
    -- frame independence: on `[0,T)` the reaction may be computed in the Uhlenbeck frame
    have hframe : (fun s : ℝ => Work.Diff.GE.reactionFormAt Work.Diff.GE.reactionMap (G s) y
          a b c d)
        =ᶠ[𝓝[Set.Ico 0 T] 0]
        (fun s : ℝ => Work.Diff.GE.Rfa.reactionFormAtE Work.Diff.GE.reactionMap (G s) y
          (fun i => e s i) a b c d) := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      rw [Work.Diff.GE.Rfa.reactionFormAt_eq_reactionFormAtE]
      exact (Work.Diff.GE.Rfa.reactionFormAtE_frame_indep (I := I) (M := M) hLC
        Work.Diff.GE.reactionMap Work.Diff.EXT.reactionMap_rot (G s) y
        (Submission.Diff.onFrame (G s) y) (fun i => e s i)
        (Work.Diff.GE.isONFrame_onFrame (G s) y) (hON s hs) a b c d).symm
    refine ContinuousWithinAt.congr_of_eventuallyEq ?_ hframe
      (hframe.self_of_nhdsWithin ⟨le_refl 0, hTpos⟩)
    -- continuity of the explicit-frame expression
    have hexp : ∀ s, Work.Diff.GE.Rfa.reactionFormAtE Work.Diff.GE.reactionMap (G s) y
        (fun i => e s i) a b c d
        = ∑ i, ∑ j, ∑ k, ∑ l,
            ((G s).inner y (e s i) a * (G s).inner y (e s j) b * (G s).inner y (e s k) c
              * (G s).inner y (e s l) d)
            * (Work.Diff.GE.reactionMap
                (Submission.Diff.rmFrame (G s) y (fun i => e s i))) i j k l := by
      intro s
      rfl
    refine ContinuousWithinAt.congr_of_eventuallyEq ?_
      (Filter.Eventually.of_forall hexp) (hexp 0)
    have hcont : Continuous (Work.Diff.GE.reactionMap :
        Curv4 (Module.finrank ℝ E) → Curv4 (Module.finrank ℝ E)) := by
      rw [show (Work.Diff.GE.reactionMap : Curv4 (Module.finrank ℝ E) →
            Curv4 (Module.finrank ℝ E))
          = Work.Diff.GE.rmReact (Module.finrank ℝ E) from
        funext (fun R => Work.Diff.GE.EvolA.reactionMap_eq_rmReact R)]
      exact (Work.Diff.GE.react.rmReact_contDiff (Module.finrank ℝ E)).continuous
    have hrm := rmFrame_curve_continuousWithinAt_zero (I := I) (M := M) hLC hflow y hec
    have hrmc := continuousWithinAt_comp_continuous (g := Work.Diff.GE.reactionMap) hcont hrm
    refine continuousWithinAt_sum_fintype (fun i => ?_)
    refine continuousWithinAt_sum_fintype (fun j => ?_)
    refine continuousWithinAt_sum_fintype (fun k => ?_)
    refine continuousWithinAt_sum_fintype (fun l => ?_)
    refine ContinuousWithinAt.mul (ContinuousWithinAt.mul (ContinuousWithinAt.mul
      (ContinuousWithinAt.mul
        (inner_curve_continuousWithinAt_zero (I := I) (M := M) hflow hTpos y a (hec i))
        (inner_curve_continuousWithinAt_zero (I := I) (M := M) hflow hTpos y b (hec j)))
      (inner_curve_continuousWithinAt_zero (I := I) (M := M) hflow hTpos y c (hec k)))
      (inner_curve_continuousWithinAt_zero (I := I) (M := M) hflow hTpos y d (hec l))) ?_
    exact (continuousWithinAt_pi.mp (continuousWithinAt_pi.mp
      (continuousWithinAt_pi.mp (continuousWithinAt_pi.mp hrmc i) j) k) l)

/-! ## Continuity of `ΔRm` at the initial time -/

/-- **Continuity of `ΔRm` at the initial time** (the smooth-manifold version of
`Work.Diff.GE.lapRmAt_zero_continuous`, whose statement carries an *analytic* model structure).  The
proof uses only smooth intermediate lemmas: the trace of `∇²Rm` is written in the coordinate frame
`cFrame` with the inverse Gram matrix (`Work.Diff.GE.lapRmAt_eq_sum_invGram_aux`), each summand is
continuous at `0` (`Work.Diff.GE.cov2Rm_continuousAt_aux`, `Work.Diff.GE.gramInv_jointSmooth`), and
time is reparametrised by `τ ↦ τ²` so that the flow becomes jointly smooth on an *open* interval. -/
theorem lapRmAt_continuousWithinAt_zero [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : Submission.Diff.LCSmooth I M)
    {G : ℝ → SMet I M} {T : ℝ} (hflow : IsRicciFlow G T) (y : M) (a b c d : TangentSpace I y) :
    ContinuousWithinAt (fun s : ℝ => Work.Diff.GE.lapRmAt (G s) y a b c d)
      (Set.Ico 0 T) 0 := by
  by_cases hT : T ≤ 0
  · rw [Set.Ico_eq_empty_iff.mpr (not_lt.mpr hT)]
    simp [ContinuousWithinAt, nhdsWithin_empty]
  · have hTpos : 0 < T := not_le.mp hT
    set ρ : ℝ := Real.sqrt T / 2 with hρdef
    have hρ : 0 < ρ := by positivity
    have hρT : ρ ^ 2 < T := by
      rw [hρdef, div_pow, Real.sq_sqrt (le_of_lt hTpos)]
      nlinarith
    have hsq : JointSmooth (Work.Diff.GE.cfq_sqFlow G) (Set.Ioo (-ρ) ρ) :=
      Work.Diff.GE.cfq_jointSmooth_sqFlow (I := I) (M := M) G hTpos hρ hρT hflow.1
    have h0 : (0 : ℝ) ∈ Set.Ioo (-ρ) ρ := ⟨by linarith, hρ⟩
    have hcont : ContinuousAt
        (fun τ : ℝ => Work.Diff.GE.lapRmAt (Work.Diff.GE.cfq_sqFlow G τ) y a b c d) 0 := by
      classical
      letI : RiemannianBundle (fun z : M ↦ TangentSpace I z) :=
        ⟨(Work.Diff.GE.cfq_sqFlow G 0).toRiemannianMetric⟩
      haveI : IsContMDiffRiemannianBundle I ∞ E (fun z : M ↦ TangentSpace I z) := inferInstance
      have hid : ∀ τ : ℝ, Work.Diff.GE.lapRmAt (Work.Diff.GE.cfq_sqFlow G τ) y a b c d
          = ∑ i, ∑ j, (Work.Diff.GE.GramInv (I := I) (Work.Diff.GE.cfq_sqFlow G) y τ y) i j *
              Work.Diff.GE.cov2Rm (Work.Diff.GE.cfq_sqFlow G τ) y
                (Work.Diff.GE.cFrame (I := I) y i y) (Work.Diff.GE.cFrame (I := I) y j y)
                a b c d := by
        intro τ
        have h := Work.Diff.GE.lapRmAt_eq_sum_invGram_aux (I := I) (M := M) hLC
          (Work.Diff.GE.cfq_sqFlow G τ) y a b c d
          (fun i => Work.Diff.GE.cFrame (I := I) y i y)
          (Work.Diff.GE.GramM (I := I) (Work.Diff.GE.cfq_sqFlow G) y τ y)
          (fun i j => rfl)
          (Work.Diff.GE.cfq_cFrame_span (I := I) y (mem_chart_source H y))
        simpa only [Work.Diff.GE.GramInv] using h
      have hterm : ∀ i j : Fin (Module.finrank ℝ E),
          ContinuousAt (fun τ : ℝ =>
              (Work.Diff.GE.GramInv (I := I) (Work.Diff.GE.cfq_sqFlow G) y τ y) i j *
              Work.Diff.GE.cov2Rm (Work.Diff.GE.cfq_sqFlow G τ) y
                (Work.Diff.GE.cFrame (I := I) y i y) (Work.Diff.GE.cFrame (I := I) y j y)
                a b c d) 0 := by
        intro i j
        have hg : ContinuousAt
            (fun τ : ℝ =>
              (Work.Diff.GE.GramInv (I := I) (Work.Diff.GE.cfq_sqFlow G) y τ y) i j) 0 :=
          Work.Diff.GE.cfq_continuousAt_of_jointSmoothAt (I := I) (M := M)
            (Work.Diff.GE.gramInv_jointSmooth (I := I) (M := M)
              (G := Work.Diff.GE.cfq_sqFlow G) isOpen_Ioo hsq h0 y i j)
        have hc : ContinuousAt (fun τ : ℝ =>
            Work.Diff.GE.cov2Rm (Work.Diff.GE.cfq_sqFlow G τ) y
              (Work.Diff.GE.cFrame (I := I) y i y) (Work.Diff.GE.cFrame (I := I) y j y)
              a b c d) 0 :=
          Work.Diff.GE.cov2Rm_continuousAt_aux (I := I) (M := M) hLC isOpen_Ioo hsq h0 y
            (Work.Diff.GE.cFrame (I := I) y i y) (Work.Diff.GE.cFrame (I := I) y j y) a b c d
        exact hg.mul hc
      have hsum : ContinuousAt (fun τ : ℝ => ∑ i, ∑ j,
          (Work.Diff.GE.GramInv (I := I) (Work.Diff.GE.cfq_sqFlow G) y τ y) i j *
              Work.Diff.GE.cov2Rm (Work.Diff.GE.cfq_sqFlow G τ) y
                (Work.Diff.GE.cFrame (I := I) y i y) (Work.Diff.GE.cFrame (I := I) y j y)
                a b c d) 0 := by
        refine Work.Diff.GE.cfq_continuousAt_finsetSum Finset.univ (fun i _ => ?_)
        refine Work.Diff.GE.cfq_continuousAt_finsetSum Finset.univ (fun j _ => ?_)
        exact hterm i j
      exact hsum.congr_of_eventuallyEq (Filter.Eventually.of_forall fun τ => hid τ)
    refine Work.Diff.GE.cfq_continuousWithinAt_of_continuousAt_comp_sq hTpos hcont ?_
    intro s hs
    show Work.Diff.GE.lapRmAt (G s) y a b c d
      = Work.Diff.GE.lapRmAt (Work.Diff.GE.cfq_sqFlow G (Real.sqrt s)) y a b c d
    rw [show Work.Diff.GE.cfq_sqFlow G (Real.sqrt s) = G s from by
      rw [Work.Diff.GE.cfq_sqFlow, Real.sq_sqrt hs.1]]

/-! ## The one-sided fixed-vector curvature evolution on `[0,T)` -/

/-- **The fixed-vector curvature evolution on the whole half-open interval `[0,T)`** (as a one-sided
derivative): at every `t ∈ [0,T)` the component `s ↦ Rm(G s)(y)(a,b,c,d)` has right derivative
`ΔRm(G t)(y)(a,b,c,d) + Q(Rm(G t))(y)(a,b,c,d)`.  The interior case is
`Work.Diff.GE.EvolA.rmP_evol_fixed`; at `t = 0` the mean value theorem
(`Work.Diff.GE.derivWithin_Ico_zero`) is applied, which needs the continuity at `0` of both the
component (`Work.Diff.GE.continuousWithinAt_rmP_zero`) and of `ΔRm + Q(Rm)`
(`Work.Diff.GE.lapRmAt_zero_continuous`, `reactionFormAt_continuousWithinAt_zero`). -/
theorem rmP_hasDerivWithinAt_Ico [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : Submission.Diff.LCSmooth I M) (hLV : Submission.Diff.LCVariation I M)
    {G : ℝ → SMet I M} {T : ℝ} (hflow : IsRicciFlow G T)
    {t : ℝ} (ht : t ∈ Set.Ico 0 T) (y : M) (a b c d : TangentSpace I y) :
    HasDerivWithinAt (fun s => rmP (G s) y a b c d)
      (Work.Diff.GE.lapRmAt (G t) y a b c d
        + Work.Diff.GE.reactionFormAt Work.Diff.GE.reactionMap (G t) y a b c d)
      (Set.Ico 0 T) t := by
  by_cases h0 : t = 0
  · subst h0
    have hTpos : 0 < T := ht.2
    refine Work.Diff.GE.derivWithin_Ico_zero (fun s => rmP (G s) y a b c d)
      (fun s => Work.Diff.GE.lapRmAt (G s) y a b c d
        + Work.Diff.GE.reactionFormAt Work.Diff.GE.reactionMap (G s) y a b c d) T hTpos
      ?_ ?_ ?_
    · intro s hs
      exact Work.Diff.GE.EvolA.rmP_evol_fixed (I := I) (M := M) hLC hLV G T hflow s hs y a b c d
    · exact Work.Diff.GE.continuousWithinAt_rmP_zero (I := I) (M := M) hLC hflow y a b c d
    · exact ContinuousWithinAt.add
        (Work.Diff.EXT.lapRmAt_continuousWithinAt_zero (I := I) (M := M) hLC hflow y a b c d)
        (reactionFormAt_continuousWithinAt_zero (I := I) (M := M) hLC hflow y a b c d)
  · have ht' : t ∈ Set.Ioo 0 T :=
      ⟨lt_of_le_of_ne ht.1 (Ne.symm h0), ht.2⟩
    exact (Work.Diff.GE.EvolA.rmP_evol_fixed (I := I) (M := M) hLC hLV G T hflow t ht'
      y a b c d).hasDerivWithinAt

/-- **The fixed-vector curvature evolution on `[0,T)`, in the `derivWithin (Ioi 0)` form used by the
reaction operator**: at every `t ∈ [0,T)` the right derivative of `s ↦ Rm(G s)(y)(a,b,c,d)` is
`ΔRm + Q(Rm)` at `t`. -/
theorem rmP_derivWithin_Ioi_ladder [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : Submission.Diff.LCSmooth I M) (hLV : Submission.Diff.LCVariation I M)
    {G : ℝ → SMet I M} {T : ℝ} (hflow : IsRicciFlow G T)
    {t : ℝ} (ht : t ∈ Set.Ico 0 T) (y : M) (a b c d : TangentSpace I y) :
    derivWithin (fun s => rmP (G s) y a b c d) (Set.Ioi 0) t
      = Work.Diff.GE.lapRmAt (G t) y a b c d
        + Work.Diff.GE.reactionFormAt Work.Diff.GE.reactionMap (G t) y a b c d := by
  by_cases h0 : t = 0
  · subst h0
    have hTpos : 0 < T := ht.2
    have hmain := rmP_hasDerivWithinAt_Ico (I := I) (M := M) hLC hLV hflow ht y a b c d
    have h1 : HasDerivWithinAt (fun s => rmP (G s) y a b c d)
        (Work.Diff.GE.lapRmAt (G 0) y a b c d
          + Work.Diff.GE.reactionFormAt Work.Diff.GE.reactionMap (G 0) y a b c d)
        (Set.Ioi 0) 0 := by
      rw [hasDerivWithinAt_iff_tendsto_slope] at hmain ⊢
      rw [Set.Ico_sdiff_left] at hmain
      have hmem : Set.Iio T ∈ 𝓝[Set.Ioi (0 : ℝ)] 0 :=
        nhdsWithin_le_nhds (Iio_mem_nhds hTpos)
      have hfilt : 𝓝[Set.Ioo (0 : ℝ) T] 0 = 𝓝[Set.Ioi (0 : ℝ)] 0 := by
        have h := nhdsWithin_inter_of_mem hmem
        rw [show Set.Iio T ∩ Set.Ioi (0 : ℝ) = Set.Ioo 0 T from by
          ext u
          simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ioi, Set.mem_Ioo]
          exact and_comm] at h
        exact h
      have hset : Set.Ioi (0 : ℝ) \ {0} = Set.Ioi 0 :=
        Set.sdiff_singleton_eq_self (by simp)
      rw [hset, ← hfilt]
      exact hmain
    rw [h1.derivWithin (uniqueDiffWithinAt_Ioi 0)]
  · have ht' : t ∈ Set.Ioo 0 T := ⟨lt_of_le_of_ne ht.1 (Ne.symm h0), ht.2⟩
    rw [derivWithin_of_mem_nhds (Ioi_mem_nhds (lt_of_le_of_ne ht.1 (Ne.symm h0)))]
    exact (Work.Diff.GE.EvolA.rmP_evol_fixed (I := I) (M := M) hLC hLV G T hflow t ht'
      y a b c d).deriv

/-! ## Locality of the jets for smooth tuples -/

/-- **Locality of the iterated covariant derivative `jetAll`, restricted to *smooth* tuples.**  The
statement of `Work.Diff.EXT.evolX.jetAll_congr_of_eventuallyEq` quantifies over *all* tuples of
fields; for operators built from the tower `ckt` the value is tensorial only on smooth fields, so
the honest statement is the restricted one: if two packed operators agree near `x` on every *smooth*
tuple, then their `j`-th jets at `x` agree on every smooth tuple.  The proof is the induction of
`Work.Diff.EXT.evolX.jetAll_eventuallyEq_of_eventuallyEq`, with the smoothness of the Leibniz
corrections `Function.update G s (dirF g (G s) (G 0))` supplied by `Work.Diff.EXT.smoothF_update`
and `Work.Diff.EXT.dirF_smooth`. -/
theorem jetAll_eventuallyEq_of_eventuallyEq_smooth [T2Space M] {g : SMet I M}
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
        filter_upwards [Work.Diff.EXT.evolX.mvfderiv_eventuallyEq_of_eventuallyEq (I := I)
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
            (Work.Diff.EXT.smoothF_update (G := fun i : Fin (K + l) => G i.succ)
              (fun i => hG i.succ)
              (Work.Diff.EXT.dirF_smooth (I := I) (M := M) hLC g (hG s.succ) (hG 0)))
      filter_upwards [hmv, hcorr] with y hy1 hy2
      rw [hy1, Finset.sum_congr rfl (fun s _ => hy2 s)]

/-- Locality of the jets at a point, smooth-tuple form. -/
theorem jetAll_congr_of_eventuallyEq_smooth [T2Space M] {g : SMet I M} {K j : ℕ}
    (hLC : Submission.Diff.LCSmooth I M)
    {S S' : (Fin K → TField (I := I) (M := M)) → M → ℝ} {x : M}
    (h : ∀ F, (∀ i, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (F i)) →
      S F =ᶠ[𝓝 x] S' F)
    (G : Fin (K + j) → TField (I := I) (M := M))
    (hG : ∀ i, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (G i)) :
    jetAll g j K S G x = jetAll g j K S' G x :=
  (jetAll_eventuallyEq_of_eventuallyEq_smooth (I := I) (M := M) hLC j K S S' x h G hG).eq_of_nhds

/-! ## The germ of the level-`0` reaction is `Q(Rm)` -/

/-- **The germ identity for the level-`0` reaction.**  For a Ricci flow `G` on `[0,T)`, `t ∈ [0,T)`,
a point `x` and a family `Ef` of smooth fields which is `G t`-orthonormal near `x`, the level-`0`
reaction operator `Work.Diff.EXT.reactOpEfD Ef G t 0` (the one-sided time derivative of the curvature
minus the rough Laplacian traced in the frame field `Ef`) agrees, near `x`, with the quadratic
reaction `Q(Rm) = reactionFormAt reactionMap`: this is the fixed-vector curvature evolution
(`rmP_derivWithin_Ioi_ladder`) together with the trace identity `sum_ckt_two_eq_lapRmAt`. -/
theorem reactOpEfD_zero_eventuallyEq_reaction [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : Submission.Diff.LCSmooth I M) (hLV : Submission.Diff.LCVariation I M)
    {G : ℝ → SMet I M} {T : ℝ} (hflow : IsRicciFlow G T)
    {t : ℝ} (ht : t ∈ Set.Ico 0 T) {x : M}
    {Ef : Fin (Module.finrank ℝ E) → TField (I := I) (M := M)}
    (hEf : ∀ i, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (Ef i))
    (hON : ∀ᶠ y in 𝓝 x, Submission.Diff.IsONFrame (G t) y (fun i => Ef i y))
    {F : Fin 4 → TField (I := I) (M := M)}
    (hF : ∀ i, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (F i)) :
    (fun y : M => reactOpEfD (I := I) (M := M) Ef G t 0 F y)
      =ᶠ[𝓝 x] (fun y : M => Work.Diff.GE.reactionFormAt Work.Diff.GE.reactionMap (G t) y
        (F 0 y) (F 1 y) (F 2 y) (F 3 y)) := by
  filter_upwards [hON] with y hy
  have hderiv : derivWithin (fun s : ℝ => ckt (G s) 0 F y) (Set.Ioi 0) t
      = Work.Diff.GE.lapRmAt (G t) y (F 0 y) (F 1 y) (F 2 y) (F 3 y)
        + Work.Diff.GE.reactionFormAt Work.Diff.GE.reactionMap (G t) y
            (F 0 y) (F 1 y) (F 2 y) (F 3 y) := by
    have h := rmP_derivWithin_Ioi_ladder (I := I) (M := M) hLC hLV hflow ht y
      (F 0 y) (F 1 y) (F 2 y) (F 3 y)
    simpa only [ckt_zero_eq_rmPT, rmPT] using h
  have htrace : (∑ m : Fin (Module.finrank ℝ E),
        ckt (G t) 2 (Fin.cons (Ef m) (Fin.cons (Ef m) F)) y)
      = Work.Diff.GE.lapRmAt (G t) y (F 0 y) (F 1 y) (F 2 y) (F 3 y) :=
    sum_ckt_two_eq_lapRmAt (I := I) (M := M) hLC (G t) y hEf hy hF
  show derivWithin (fun s : ℝ => ckt (G s) 0 F y) (Set.Ioi 0) t
      - (∑ m : Fin (Module.finrank ℝ E),
          ckt (G t) 2 (Fin.cons (Ef m) (Fin.cons (Ef m) F)) y)
      = Work.Diff.GE.reactionFormAt Work.Diff.GE.reactionMap (G t) y
          (F 0 y) (F 1 y) (F 2 y) (F 3 y)
  rw [hderiv, htrace]
  ring

theorem ladderEfD_base
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M] [CompactSpace M] :
    ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (G : ℝ → Submission.Diff.SMet I M) (T : ℝ), Submission.Diff.IsRicciFlow G T →
        ∀ t ∈ Set.Ico 0 T, ∀ x : M,
        ∀ Ef : Fin (Module.finrank ℝ E) → Work.Diff.EXT.TField (I := I) (M := M),
          Work.Diff.EXT.IsFrameNear (I := I) (M := M) (G t) x Ef →
          Work.Diff.EXT.LadderEfD (I := I) (M := M) G t x Ef 0 j C := by
  intro j
  obtain ⟨C, hC, hb⟩ := Work.Diff.EXT.reaction0_jets (I := I) (M := M) j
  refine ⟨C, hC, ?_⟩
  intro G T hflow t ht x Ef hEf
  have hLC : Submission.Diff.LCSmooth I M := Work.EXT.lcSmooth_noBoundary
  have hLV : Submission.Diff.LCVariation I M := Work.Diff.T.lc_variation hLC
  refine ⟨hC, fun N hN w => ?_⟩
  subst hN
  -- the operator, with the tuple of smooth extensions of the vectors
  have hjet : Work.Diff.EXT.jetAll (G t) j 4 (Work.Diff.EXT.reactOpEfD (I := I) (M := M) Ef G t 0)
      (fun r : Fin (4 + j) => Submission.Diff.smoothExt x (w (Fin.cast rfl.symm r))) x
      = Work.Diff.EXT.jetAll (G t) j 4
        (fun (F : Fin 4 → Work.Diff.EXT.TField (I := I) (M := M)) => fun (y : M) =>
          Work.Diff.GE.reactionFormAt Work.Diff.GE.reactionMap (G t) y
            (F 0 y) (F 1 y) (F 2 y) (F 3 y))
        (fun r : Fin (4 + j) => Submission.Diff.smoothExt x (w (Fin.cast rfl.symm r))) x := by
    refine Work.Diff.EXT.jetAll_congr_of_eventuallyEq_smooth (I := I) (M := M) hLC ?_ _ ?_
    · intro F hF
      exact Work.Diff.EXT.reactOpEfD_zero_eventuallyEq_reaction (I := I) (M := M) hLC hLV hflow
        ht hEf.1 hEf.2 hF
    · intro i
      exact Work.Diff.GE.smoothExt_cmdiff x _
  rw [hjet]
  refine le_trans (hb (G t) x (fun r : Fin (4 + j) => Submission.Diff.smoothExt x (w (Fin.cast rfl.symm r)))
    (fun i => Work.Diff.GE.smoothExt_cmdiff x _)) (le_of_eq ?_)
  have hprod : (∏ r : Fin (4 + j),
        Real.sqrt ((G t).inner x (Submission.Diff.smoothExt x (w (Fin.cast rfl.symm r)) x)
          (Submission.Diff.smoothExt x (w (Fin.cast rfl.symm r)) x)))
      = ∏ r : Fin (4 + j), Real.sqrt ((G t).inner x (w r) (w r)) := by
    refine Finset.prod_congr rfl (fun r _ => ?_)
    simp only [Work.Diff.GE.smoothExt_apply]
    rfl
  rw [hprod, show (0 : ℕ) + j = j from Nat.zero_add j]

end Work.Diff.EXT
