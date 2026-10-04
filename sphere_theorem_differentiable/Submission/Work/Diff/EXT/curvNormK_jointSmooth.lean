import Mathlib
import Submission.Work.Diff.EXT.curvDefs
import Submission.Work.Diff.EXT.covK_spatialDeriv
import Submission.Work.Diff.EXT.covK_familySmooth
import Submission.Work.Diff.EXT.curvNormK_frame_indepL
import Submission.Work.Diff.EXT.covK_linearL
import Submission.Work.Diff.EXT.covK_germ
import Submission.Work.Diff.EXT.curvDefs2
import Submission.Work.Diff.EXT.covK_valueDepN
import Submission.Work.Diff.EXT.covK_onFrameFamily
import Submission.Work.Diff.EXT.twoSided_of_within

/-!
# Joint smoothness of `|∇^k Rm|²` along a Ricci flow

`Work.Diff.EXT.NormSmoothK` says: for every smooth Ricci flow `G` on `[0,T)` and every `k : ℕ`,
the function `(t,x) ↦ curvNormK (G t) x k` is `C^∞` on `Ico 0 T ×ˢ univ`.

`curvNormK` is `|∇^k Rm|²` computed as the sum of squares of the components of the `(0,k+4)`-tensor
`∇^k Rm` in the `Classical.epsilon`-chosen orthonormal frame `onFrame g x`.  That choice of frame is
not smooth in `x`, but the sum of squares does not depend on the orthonormal frame
(`covK_frameInv`), so the function is smooth: near any point we replace `onFrame` by a *smooth*
family of orthonormal frames (`covK_onFrameFamily`) and rewrite the components through the
field-level tower `covKRmExt` (`covK_valueDep`), which is jointly smooth along a jointly smooth
family of metrics and fields (`covK_familySmooth`).

At the initial time `t = 0` the family `G` is only known to be smooth for `t ≥ 0`; the two-sided
extension `Work.Diff.EXT.twoSided_of_within` reduces that boundary case to the interior one.

The vocabulary is in `Submission.Work.Diff.EXT.curvDefs`; the individual lemmas are in the modules
imported above:

* `covK_valueDepN` — value dependence (`KrValueDepN`) of the tower for fields smooth on a
  neighbourhood of the point, from `KrLinear` and `KrGerm` (see `curvDefs2.lean`; note that
  `ContMDiffAt ∞` does not give smoothness on a neighbourhood, which is why `KrValueDep` is not
  usable directly);
* `covK_familySmooth` — joint smoothness of
  `(t,y) ↦ covKRmExt (G t) k (Vf t) (A t) (B t) (C t) (D t) y` on an open set (it contains its own
  proof of the `lcOf`-along-families step);
* `covK_onFrameFamily` — a jointly smooth family of orthonormal frames;
* `covK_spatialDeriv`, `covK_germ`, `covK_linearL` and `curvNormK_frame_indepL` — the frame
  independence of the sum of squares of the components.

IMPORT CLASH WARNING: `Submission.Work.Diff.GE.norms_defs` and the `Submission.Work.Diff.GE.frobSq5_*`
files both declare the name `Work.Diff.GE.rot5` (a `def` and a private `lemma`), so no single file may
import both sides.  The `...L` files above are clash-free copies of the `frobSq5` side in which that

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
private lemma is renamed `rot5L` (`frobSq5_frameIndepL`, `frobSqN_frame_indepL`,
`curvNormK_frame_indepL`, `covK_linearL`).
-/

set_option maxHeartbeats 1000000

namespace Work.Diff.EXT

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology Matrix
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-- The slice at a fixed time of a jointly smooth family of fields is smooth. -/
theorem jointField_sliceAt {X : ℝ → TField (I := I) (M := M)} {V : Set (ℝ × M)}
    (hV : IsOpen V) (hX : JointField X V) {p : ℝ × M} (hp : p ∈ V) :
    SmoothTFieldAt (I := I) (M := M) (fun y : M => X p.1 y) p.2 := by
  have hslice : ContMDiffAt I ((𝓘(ℝ, ℝ)).prod I) ∞ (fun y : M => (p.1, y)) p.2 :=
    (contMDiffAt_const (c := p.1)).prodMk contMDiffAt_id
  exact (hX.contMDiffAt (hV.mem_nhds hp)).comp p.2 hslice

/-- A finite sum of smooth functions is smooth. -/
theorem contMDiffOn_finset_sum {ι : Type*} (s : Finset ι) {f : ι → ℝ × M → ℝ}
    {W : Set (ℝ × M)}
    (h : ∀ i ∈ s, ContMDiffOn ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) ∞ (f i) W) :
    ContMDiffOn ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) ∞ (fun p : ℝ × M ↦ ∑ i ∈ s, f i p) W := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using contMDiffOn_const (c := (0 : ℝ)) (s := W)
  | insert a s ha ih =>
      have h1 : ContMDiffOn ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) ∞ (f a) W :=
        h a (Finset.mem_insert_self a s)
      have h2 : ContMDiffOn ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) ∞
          (fun p : ℝ × M ↦ ∑ i ∈ s, f i p) W :=
        ih fun i hi => h i (Finset.mem_insert_of_mem hi)
      have hfun : (fun p : ℝ × M ↦ ∑ i ∈ insert a s, f i p)
          = (f a + fun p : ℝ × M ↦ ∑ i ∈ s, f i p) := by
        funext p
        simp only [Finset.sum_insert ha, Pi.add_apply]
      rw [hfun]
      exact h1.add h2

/-- **The interior case**: on an open time interval, `(t,x) ↦ curvNormK (G t) x k` is smooth. -/
theorem curvNormK_jointSmooth_open
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : Submission.Diff.LCSmooth I M)
    (K : ℝ → Submission.Diff.SMet I M) {J : Set ℝ} (hJ : IsOpen J)
    (hK : JointSmooth K J) (k : ℕ) :
    ContMDiffOn ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M ↦ curvNormK (K p.1) p.2 k) (J ×ˢ (univ : Set M)) := by
  intro p₀ hp₀
  have hV : IsOpen (J ×ˢ (univ : Set M)) := hJ.prod isOpen_univ
  have hG : JointMet (I := I) (M := M) K (J ×ˢ (univ : Set M)) := hK
  obtain ⟨W, hWopen, hp₀W, hWV, F, hFjoint, hFON⟩ :=
    covK_onFrameFamily (I := I) (M := M) hV hG hp₀
  -- the smooth expression in terms of the field-level tower
  have hΨ : ContMDiffOn ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M ↦ ∑ ι : Fin k → Fin (Module.finrank ℝ E), ∑ i, ∑ j, ∑ l, ∑ m,
        (covKRmExt (K p.1) k (fun s ↦ fun y ↦ F p.1 y (ι s))
          (fun y ↦ F p.1 y i) (fun y ↦ F p.1 y j) (fun y ↦ F p.1 y l)
          (fun y ↦ F p.1 y m) p.2) ^ 2) W := by
    refine contMDiffOn_finset_sum Finset.univ fun ι _ ↦ ?_
    refine contMDiffOn_finset_sum Finset.univ fun i _ ↦ ?_
    refine contMDiffOn_finset_sum Finset.univ fun j _ ↦ ?_
    refine contMDiffOn_finset_sum Finset.univ fun l _ ↦ ?_
    refine contMDiffOn_finset_sum Finset.univ fun m _ ↦ ?_
    have h0 := covK_familySmooth (I := I) (M := M) (hLC := hLC) (G := K) (V := W) hWopen
      (hG.mono hWV) k (Vf := fun t s y ↦ F t y (ι s)) (fun s ↦ hFjoint (ι s))
      (A := fun t y ↦ F t y i) (hFjoint i) (B := fun t y ↦ F t y j) (hFjoint j)
      (C := fun t y ↦ F t y l) (hFjoint l) (D := fun t y ↦ F t y m) (hFjoint m)
    exact h0.pow 2
  -- rewriting the components through the value-dependence of the tower
  have hval : EqOn
      (fun p : ℝ × M ↦ ∑ ι : Fin k → Fin (Module.finrank ℝ E), ∑ i, ∑ j, ∑ l, ∑ m,
        (covKRmC (K p.1) p.2 (F p.1 p.2) k ι i j l m) ^ 2)
      (fun p : ℝ × M ↦ ∑ ι : Fin k → Fin (Module.finrank ℝ E), ∑ i, ∑ j, ∑ l, ∑ m,
        (covKRmExt (K p.1) k (fun s ↦ fun y ↦ F p.1 y (ι s))
          (fun y ↦ F p.1 y i) (fun y ↦ F p.1 y j) (fun y ↦ F p.1 y l)
          (fun y ↦ F p.1 y m) p.2) ^ 2) W := by
    intro p hp
    have hVD := covK_valueDepN (I := I) (M := M) hLC (K p.1) k
      (covK_linearL (I := I) (M := M) hLC (K p.1) k)
      (covK_germ (I := I) (M := M) hLC (K p.1) k)
    refine Finset.sum_congr rfl fun ι _ ↦ ?_
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    refine Finset.sum_congr rfl fun m _ ↦ ?_
    congr 1
    simpa only [covKRmC_eq_covKRm, covKRm] using (hVD (V := fun s ↦ fun y ↦ F p.1 y (ι s))
      (V' := fun s ↦ smoothExt p.2 (F p.1 p.2 (ι s)))
      (A := fun y ↦ F p.1 y i) (A' := smoothExt p.2 (F p.1 p.2 i))
      (B := fun y ↦ F p.1 y j) (B' := smoothExt p.2 (F p.1 p.2 j))
      (C := fun y ↦ F p.1 y l) (C' := smoothExt p.2 (F p.1 p.2 l))
      (D := fun y ↦ F p.1 y m) (D' := smoothExt p.2 (F p.1 p.2 m)) (x := p.2)
      (fun s ↦ jointField_sliceNear hWopen (hFjoint (ι s)) hp)
      (fun s ↦ (SmoothTField.smoothNear (Work.Diff.GE.smoothExt_cmdiff p.2 (F p.1 p.2 (ι s))) p.2))
      (jointField_sliceNear hWopen (hFjoint i) hp) ((SmoothTField.smoothNear (Work.Diff.GE.smoothExt_cmdiff p.2 (F p.1 p.2 i)) p.2))
      (jointField_sliceNear hWopen (hFjoint j) hp) ((SmoothTField.smoothNear (Work.Diff.GE.smoothExt_cmdiff p.2 (F p.1 p.2 j)) p.2))
      (jointField_sliceNear hWopen (hFjoint l) hp) ((SmoothTField.smoothNear (Work.Diff.GE.smoothExt_cmdiff p.2 (F p.1 p.2 l)) p.2))
      (jointField_sliceNear hWopen (hFjoint m) hp) ((SmoothTField.smoothNear (Work.Diff.GE.smoothExt_cmdiff p.2 (F p.1 p.2 m)) p.2))
      (fun s ↦ (Work.Diff.GE.smoothExt_apply p.2 (F p.1 p.2 (ι s))).symm)
      (Work.Diff.GE.smoothExt_apply p.2 (F p.1 p.2 i)).symm (Work.Diff.GE.smoothExt_apply p.2 (F p.1 p.2 j)).symm
      (Work.Diff.GE.smoothExt_apply p.2 (F p.1 p.2 l)).symm (Work.Diff.GE.smoothExt_apply p.2 (F p.1 p.2 m)).symm).symm
  -- the frame independence of the sum of squares
  have hsum : ContMDiffOn ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M ↦ ∑ ι : Fin k → Fin (Module.finrank ℝ E), ∑ i, ∑ j, ∑ l, ∑ m,
        (covKRmC (K p.1) p.2 (F p.1 p.2) k ι i j l m) ^ 2) W :=
    hΨ.congr hval
  -- the frame identity on `W`: `|∇^k Rm|²` is the sum of squares in the smooth frame `F`
  have hframe : EqOn (fun p : ℝ × M ↦ curvNormK (K p.1) p.2 k)
      (fun p : ℝ × M ↦ ∑ ι : Fin k → Fin (Module.finrank ℝ E), ∑ i, ∑ j, ∑ l, ∑ m,
        (covKRmC (K p.1) p.2 (F p.1 p.2) k ι i j l m) ^ 2) W := by
    intro p hp
    exact curvNormK_frame_indepL (I := I) (M := M) (hLC := hLC) (g := K p.1) (x := p.2)
      (k := k) (e := F p.1 p.2) (he := hFON p hp)
  have hfin : ContMDiffOn ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M ↦ curvNormK (K p.1) p.2 k) W :=
    hsum.congr fun p hp => hframe hp
  exact (hfin.contMDiffAt (hWopen.mem_nhds hp₀W)).contMDiffWithinAt

/-- **Smoothness of `|∇^k Rm|²` along a Ricci flow, up to and including the initial time.** -/
theorem curvNormK_jointSmooth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : Submission.Diff.LCSmooth I M) :
    Work.Diff.EXT.NormSmoothK (I := I) (M := M) := by
  intro G T hflow k p₀ hp₀
  by_cases hT : 0 < T
  · by_cases ht₀ : 0 < p₀.1
    · -- interior point
      obtain ⟨J, hJopen, hp₀J, hJsub⟩ : ∃ J : Set ℝ, IsOpen J ∧ p₀.1 ∈ J ∧ J ⊆ Set.Ico 0 T :=
        ⟨Set.Ioo (p₀.1 / 2) T, isOpen_Ioo, ⟨by linarith, hp₀.1.2⟩, fun t ht => ⟨by linarith [ht.1], ht.2⟩⟩
      have hKJ : JointSmooth G J := hflow.1.mono fun p hp => ⟨hJsub hp.1, hp.2⟩
      exact (((curvNormK_jointSmooth_open (I := I) (M := M) hLC G hJopen hKJ k) p₀
        ⟨hp₀J, mem_univ _⟩).contMDiffAt
        ((hJopen.prod isOpen_univ).mem_nhds ⟨hp₀J, mem_univ _⟩)).contMDiffWithinAt
    · -- boundary point `p₀.1 = 0`
      have ht₀0 : p₀.1 = 0 := le_antisymm (not_lt.mp ht₀) hp₀.1.1
      obtain ⟨ε, hε, K, hKsm, hagree⟩ := twoSided_of_within (I := I) (M := M) G T hT hflow.1
      have hεT : 0 < min ε T := lt_min hε hT
      have h1 : ContMDiffOn ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) ∞
          (fun p : ℝ × M ↦ curvNormK (K p.1) p.2 k) (Set.Ico 0 (min ε T) ×ˢ (univ : Set M)) :=
        (curvNormK_jointSmooth_open (I := I) (M := M) hLC K isOpen_Ioo hKsm k).mono
          (Set.prod_mono (fun t ht => ⟨by linarith [ht.1, ht.2, min_le_left ε T],
            by linarith [ht.2, min_le_left ε T]⟩) Subset.rfl)
      have h2 : ContMDiffOn ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) ∞
          (fun p : ℝ × M ↦ curvNormK (G p.1) p.2 k) (Set.Ico 0 (min ε T) ×ˢ (univ : Set M)) :=
        h1.congr fun p hp => by
          rw [hagree p.1 ⟨hp.1.1, lt_of_lt_of_le hp.1.2 (min_le_left ε T)⟩]
      have hp₀' : p₀ ∈ Set.Ico 0 (min ε T) ×ˢ (univ : Set M) := by
        refine Set.mem_prod.mpr ⟨?_, mem_univ _⟩
        rw [ht₀0]
        exact ⟨le_refl 0, hεT⟩
      have h3 : ContMDiffWithinAt ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) ∞
          (fun p : ℝ × M ↦ curvNormK (G p.1) p.2 k) (Set.Ico 0 (min ε T) ×ˢ (univ : Set M)) p₀ :=
        h2 p₀ hp₀'
      refine (contMDiffWithinAt_congr_set ?_).mp h3
      have hδ : 0 < min ε T := hεT
      filter_upwards [(isOpen_Ioo.prod isOpen_univ).mem_nhds
        (show p₀ ∈ Set.Ioo (-(min ε T)) (min ε T) ×ˢ (univ : Set M) from
          ⟨by rw [ht₀0]; exact ⟨by linarith, hδ⟩, mem_univ _⟩)] with q hq
      apply propext
      refine ⟨?_, ?_⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨h1.1, by linarith [h1.2, min_le_right ε T]⟩, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨h1.1, hq.1.2⟩, h2⟩
  · exfalso
    have := hp₀.1.2
    have := hp₀.1.1
    linarith [not_lt.mp hT]

end Work.Diff.EXT
