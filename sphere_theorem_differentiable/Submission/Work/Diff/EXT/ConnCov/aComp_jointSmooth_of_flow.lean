import Mathlib
import Submission.Work.Diff.EXT.ConnCov.ChartTowerDefs
import Submission.Work.Diff.EXT.ConnCov.aComp_jets_of_chartMat_jets
import Submission.Work.Diff.EXT.ConnCov.tower3Arr_jointSmooth
import Submission.Work.Diff.EXT.contDiffWithinAt_chartMat_of_jointSmooth
import Submission.Work.Diff.EXT.chartData_contDiffOn
import Submission.Work.Diff.EXT.christoffel_bounds_of_core

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Joint smoothness of the chart array `aComp` of the connection difference

`Work.Diff.EXT.aComp G x₀ t y i j l` is the chart array of the *lowered* connection difference
`g_t(∇^{g_t} − ∇^{g_0})` of a family of metrics `G`, read in the coordinate frame of the chart at
`x₀` at the chart coordinate `y`.  This module proves that this array is *jointly* `C^∞` in
`(t, y)` at every pair `(t, y)` with `t ∈ (0, T)` and `y` in the chart target, as soon as the
family of metrics is jointly smooth on `[0, T)` — in particular along a Ricci flow.

The point is the *chart* identity (`Work.Diff.EXT.ConnCov.aComp_eq_sKz_sub`)

`aComp G x₀ t y i j l = sKz (dJet1 (G t) x₀ y) i j l − ∑_p chartMat G x₀ t y l p · Γ(G 0)^p_{ij}(y)`

of `Work.Diff.EXT.ConnCov.aComp_jets_of_chartMat_jets`: the term that would need the *inverse*
chart Gram matrix cancels, and both remaining terms are built from the chart matrix itself (its
first spatial jet in the first term, its value in the second) and from the *fixed* initial
Christoffel symbols.  Joint smoothness therefore follows from the joint smoothness of the chart
matrix — which is `Work.Diff.EXT.contDiffWithinAt_chartMat_of_jointSmooth_gen` read within the
time set `[0, T)` — together with the elementary fact that the *slice* derivative of a jointly
smooth function is jointly smooth (`Work.Diff.EXT.ConnCov.contDiffAt_fderiv_slice_apply`).

## Main result

`Work.Diff.EXT.ConnCov.aComp_jointSmooth_of_flow`:
for a Ricci flow `G` on `[0, T)`, `t ∈ [T/2, T)` and `y` in the chart target, the array
`(s, y') ↦ aComp G x₀ s y' i j l` is `C^∞` at `(t, y)`.
-/

set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT.ConnCov

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  [I.Boundaryless] [T2Space M]

/-! ## Joint smoothness of the chart matrix of a jointly smooth family -/

/-- **An entry of the chart matrix of a jointly smooth family of metrics is jointly `C^∞`** at
every `(t, y)` with `t` in the *interior* of the time set and `y` in the target of the extended
chart at `x₀`.  This is `Work.Diff.EXT.contDiffWithinAt_chartMat_of_jointSmooth_gen` read within
the set `[0, T) ×ˢ target` (a neighbourhood of `(t, y)` when `t ∈ (0, T)` and `y` is in the
target). -/
lemma chartMat_entry_jointSmooth
    {G : ℝ → Submission.Diff.SMet I M} {T : ℝ}
    (hG : Submission.Diff.JointSmooth G (Set.Ico 0 T))
    {t : ℝ} (ht : t ∈ Set.Ioo 0 T) (x₀ : M) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) (l p : Fin (Module.finrank ℝ E)) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q : ℝ × E => Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ q.1 q.2 l p) (t, y) := by
  have hmem : Set.Ico 0 T ×ˢ (extChartAt I x₀).target ∈ 𝓝 (t, y) := by
    rw [nhds_prod_eq]
    exact Filter.prod_mem_prod
      (Filter.mem_of_superset (isOpen_Ioo.mem_nhds ht) Set.Ioo_subset_Ico_self)
      ((isOpen_extChartAt_target (I := I) x₀).mem_nhds hy)
  have hw := (Work.Diff.EXT.contDiffWithinAt_chartMat_of_jointSmooth_gen (I := I) (M := M)
    hG ⟨le_of_lt ht.1, ht.2⟩ x₀ hy).contDiffAt hmem
  exact (ContinuousLinearMap.contDiff
    ((ContinuousLinearMap.proj p : (Fin (Module.finrank ℝ E) → ℝ) →L[ℝ] ℝ).comp
      (ContinuousLinearMap.proj l : Work.Diff.EXT.MatE (E := E) →L[ℝ]
        (Fin (Module.finrank ℝ E) → ℝ)))).contDiffAt.comp (t, y) hw

/-! ## Joint smoothness of the Koszul pairing of the first chart jet -/

/-- **A matrix entry of the first chart jet of a jointly smooth family is jointly `C^∞`.**  This is
the slice derivative `Work.Diff.EXT.ConnCov.contDiffAt_fderiv_slice_apply` of an entry of the
chart matrix, written through `Work.Diff.EXT.kz_fderiv_chartMatFun_apply`, which exchanges the
entry of the Fréchet derivative with the Fréchet derivative of the entry. -/
lemma fderiv_chartMat_entry_jointSmooth
    {G : ℝ → Submission.Diff.SMet I M} {T : ℝ}
    (hG : Submission.Diff.JointSmooth G (Set.Ico 0 T))
    {t : ℝ} (ht : t ∈ Set.Ioo 0 T) (x₀ : M) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) (a b m : Fin (Module.finrank ℝ E)) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q : ℝ × E =>
        (fderiv ℝ (Work.Diff.EXT.chartMatFun (I := I) (G q.1) x₀) q.2
          (Work.Diff.EXT.bB (E := E) m)) a b) (t, y) := by
  have hslice : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q : ℝ × E => fderiv ℝ
        (fun y' : E => Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ q.1 y' a b) q.2
          (Work.Diff.EXT.bB (E := E) m)) (t, y) :=
    Work.Diff.EXT.ConnCov.contDiffAt_fderiv_slice_apply
      (Φ := fun q : ℝ × E => Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ q.1 q.2 a b)
      (chartMat_entry_jointSmooth (I := I) (M := M) hG ht x₀ hy a b) _
  refine hslice.congr_of_eventuallyEq ?_
  rw [nhds_prod_eq]
  filter_upwards [Filter.prod_mem_prod Filter.univ_mem
    ((isOpen_extChartAt_target (I := I) x₀).mem_nhds hy)] with q hq
  exact Work.Diff.EXT.kz_fderiv_chartMatFun_apply (I := I) (M := M) (G q.1) x₀ hq.2 m a b

/-- **Joint smoothness of the Koszul pairing of the first chart jet.**  The Koszul pairing
`sKz (dJet1 g x₀ y) i j l = ½ (∂_i g_{jl} + ∂_j g_{il} − ∂_l g_{ij})` is a fixed linear combination
of three entries of the first chart jet, hence jointly `C^∞`. -/
lemma sKz_dJet1_jointSmooth
    {G : ℝ → Submission.Diff.SMet I M} {T : ℝ}
    (hG : Submission.Diff.JointSmooth G (Set.Ico 0 T))
    {t : ℝ} (ht : t ∈ Set.Ioo 0 T) (x₀ : M) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) (i j l : Fin (Module.finrank ℝ E)) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q : ℝ × E => Work.Diff.EXT.sKz (Work.Diff.EXT.dJet1 (G q.1) x₀ q.2) i j l) (t, y) := by
  have hmain : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q : ℝ × E => (1 / 2 : ℝ) *
        ((fderiv ℝ (Work.Diff.EXT.chartMatFun (I := I) (G q.1) x₀) q.2
              (Work.Diff.EXT.bB (E := E) i)) j l
          + (fderiv ℝ (Work.Diff.EXT.chartMatFun (I := I) (G q.1) x₀) q.2
              (Work.Diff.EXT.bB (E := E) j)) i l
          - (fderiv ℝ (Work.Diff.EXT.chartMatFun (I := I) (G q.1) x₀) q.2
              (Work.Diff.EXT.bB (E := E) l)) i j)) (t, y) :=
    (contDiffAt_const (c := (1 / 2 : ℝ))).mul
      (((fderiv_chartMat_entry_jointSmooth (I := I) (M := M) hG ht x₀ hy j l i).add
        (fderiv_chartMat_entry_jointSmooth (I := I) (M := M) hG ht x₀ hy i l j)).sub
        (fderiv_chartMat_entry_jointSmooth (I := I) (M := M) hG ht x₀ hy i j l))
  simpa only [Work.Diff.EXT.sKz, Work.Diff.EXT.dJet1] using hmain

/-! ## The main result -/

/-- **Joint smoothness of the chart array `aComp` of the connection difference.**  If the family of
metrics is jointly smooth on `[0, T)` — the smoothness half of the Ricci-flow hypothesis — then the
chart array of the lowered connection difference is `C^∞` at every `(s, y)` with `s ∈ (0, T)` and
`y` in the target of the chart at `x₀`.

No ellipticity and no compactness is needed: the identity `aComp = sKz ∘ dJet1 − chartMat · Γ(G 0)`
expresses everything through the chart matrix and the *fixed* initial Christoffel symbols. -/
theorem aComp_jointSmooth_of_jointSmooth
    (G : ℝ → Submission.Diff.SMet I M) {T : ℝ}
    (hG : Submission.Diff.JointSmooth G (Set.Ico 0 T))
    {t : ℝ} (ht : t ∈ Set.Ioo 0 T) (x₀ : M) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) (i j l : Fin (Module.finrank ℝ E)) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun p : ℝ × E => Work.Diff.EXT.aComp (I := I) (M := M) G x₀ p.1 p.2 i j l) (t, y) := by
  -- the Koszul-pairing half
  have hsKz := sKz_dJet1_jointSmooth (I := I) (M := M) hG ht x₀ hy i j l
  -- the Christoffel-symbol half of the *initial* metric: constant in time, smooth in the chart
  have hcGam : ∀ p : Fin (Module.finrank ℝ E), ContDiffAt ℝ (⊤ : ℕ∞)
      (fun s : ℝ × E =>
        Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ s.2) p i j) (t, y) :=
    fun p => ContDiffAt.comp (f := fun s : ℝ × E => s.2)
      (g := fun y' : E => Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y') p i j)
      (t, y) (Work.Diff.EXT.CBound.cGam_contDiffAt_of_target (I := I) (M := M) (G 0) x₀ hy p i j)
      contDiffAt_snd
  have hterm2 : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun s : ℝ × E => ∑ p : Fin (Module.finrank ℝ E),
        Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ s.1 s.2 l p
          * Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ s.2) p i j) (t, y) := by
    refine ContDiffAt.sum (s := Finset.univ) (fun p _ => ?_)
    exact (chartMat_entry_jointSmooth (I := I) (M := M) hG ht x₀ hy l p).mul (hcGam p)
  have hrhs : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun s : ℝ × E => Work.Diff.EXT.sKz (Work.Diff.EXT.dJet1 (G s.1) x₀ s.2) i j l
        - ∑ p : Fin (Module.finrank ℝ E),
            Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ s.1 s.2 l p
              * Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ s.2) p i j) (t, y) :=
    hsKz.sub hterm2
  refine hrhs.congr_of_eventuallyEq ?_
  rw [nhds_prod_eq]
  filter_upwards [Filter.prod_mem_prod Filter.univ_mem
    ((isOpen_extChartAt_target (I := I) x₀).mem_nhds hy)] with s hs
  exact aComp_eq_sKz_sub (I := I) (M := M) G x₀ s.1 hs.2 i j l

theorem aComp_jointSmooth_of_flow
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (G : ℝ → Submission.Diff.SMet I M) (T : ℝ) (hT : 0 < T)
    (hflow : Submission.Diff.IsRicciFlow G T)
    (x₀ : M) (K' : Set E) (hK't : K' ⊆ (extChartAt I x₀).target) :
    ∀ t ∈ Set.Ico (T / 2) T, ∀ y ∈ K', ∀ (i j l : Fin (Module.finrank ℝ E)),
      ContDiffAt ℝ (⊤ : ℕ∞)
        (fun p : ℝ × E => Work.Diff.EXT.aComp (I := I) (M := M) G x₀ p.1 p.2 i j l) (t, y) := by
  intro t ht y hy i j l
  have ht0 : 0 < t := lt_of_lt_of_le (half_pos hT) ht.1
  exact aComp_jointSmooth_of_jointSmooth (I := I) (M := M) G hflow.1 (x₀ := x₀)
    ⟨ht0, ht.2⟩ (hK't hy) i j l

end Work.Diff.EXT.ConnCov
