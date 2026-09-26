import Submission.Work.PinchCounted.Step2
import Submission.Work.InnermostDisk.not_isEssential_of_range_subset_covered
import Submission.Work.BoxShrink.Pinch.TraceClass
import Submission.Work.PinchCounted.isEssential_range_eq_of_range_subset_isSimple

/-!
# The slice inessentiality from the count, given a circle cover of the plane trace

`Counting.lean` derives the inessentiality of the slice from the plane count only through Pardon's
*planar* innermost input (`CleansInSphere (cutDisc s c σ u)`), which the workspace has for almost
every plane level but not at a prescribed one (§6.3 of `README.md`).  This module records the
*other* route to the same conclusion, the one available when the trace of the cutting plane is a
finite disjoint union of simple closed curves of "meridian or longitude" type: there an essential
loop of the slice covers one of the circles
(`Work.PinchCounted.isEssential_range_eq_of_range_subset_isSimple`), that circle lies in the slice,
and Pardon's intersection bound `Work.CoreTopology.min_le_encard_inter_standardCurve` then forces the
plane count to be at least `min p q = I(F,β)` — contradicting the count hypothesis.

The trace of the cutting plane in the *smooth* torus `ψ(F_std)` is `ψ` of the level set of the
arbitrary smooth function `y (σ 2) ∘ ψ`, so its circles can carry any homology class and this route
is not available in general; but it is available whenever the level circles do have a vanishing
winding coordinate, which is what the hypothesis `hdich` below records.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

namespace Work.PinchCounted

noncomputable section

/-- **A loop of the surface inside `sliceRegion` lies in `planeTrace`.** -/
theorem sliceRegion_subset_planeTrace {P : Work.CoreTopology.ParamTorus} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ} :
    Work.BoxShrink.Core.sliceRegion P s c σ u ⊆ Work.BoxShrink.Pinch.planeTrace P c σ u := by
  intro y hy
  obtain ⟨hmem, -, hplane⟩ := Work.BoxShrink.Core.mem_sliceRegion.mp hy
  exact Work.BoxShrink.Pinch.mem_planeTrace.mpr ⟨hmem, hplane⟩

/-- **The plane count bounds the number of intersection points of the knot with the slicing disc**,
in the `ℕ∞`-valued form used below.  (The parameter count of the crux dominates the number of
intersection points, `Work.BoxBubble.encard_range_inter_le_param`.) -/
theorem encard_inter_sliceRegion_le_planeCount {P : Work.CoreTopology.ParamTorus} (β : Work.CoreTopology.ClosedCurve P)
    (K : Knot) (himg : Set.range K.curve = Set.range β.γ)
    {c : R3} {σ : Equiv.Perm (Fin 3)} {s u : ℝ} :
    Set.encard (Set.range β.γ ∩ Work.BoxShrink.Core.sliceRegion P s c σ u) ≤
      Work.BoxShrink.planeCount K c σ s u := by
  classical
  let γK : Work.CoreTopology.ClosedCurve P :=
    { γ := K.curve
      cont := K.smooth.continuous
      periodic := K.periodic
      mem := fun t => by
        have ht : K.curve t ∈ Set.range β.γ := by
          rw [← himg]
          exact Set.mem_range_self t
        obtain ⟨u', hu'⟩ := ht
        rw [← hu']
        exact β.mem u' }
  have h1 : Set.encard (Set.range β.γ ∩ Work.BoxShrink.Core.sliceRegion P s c σ u) ≤
      Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        K.curve t ∈ Work.BoxShrink.Core.sliceRegion P s c σ u} := by
    rw [← himg]
    exact Work.BoxBubble.encard_range_inter_le_param γK _
  refine le_trans h1 (Set.encard_mono ?_)
  rintro t ⟨ht, hmem⟩
  obtain ⟨-, hbox, hplane⟩ := Work.BoxShrink.Core.mem_sliceRegion.mp hmem
  exact ⟨ht, hbox, hplane⟩

/-- **The slice is inessential, from the plane count and a circle cover of the trace.**  If the
trace of the cutting plane is covered by finitely many pairwise disjoint simple closed curves, each
of which is either inessential or meets the curve `β` in at least `min p q ≤ I(P,β)` points, then the
slicing disc carries no essential loop — with no planar innermost input. -/
theorem not_containsEssentialLoop_sliceRegion_of_traceCircles {P : Work.CoreTopology.ParamTorus}
    (β : Work.CoreTopology.ClosedCurve P)
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hβI : (Nat.min p q : ℕ∞) ≤ Work.CoreTopology.pardonsI P β)
    (K : Knot) {d : ℝ} (hd : 0 ≤ d)
    (himg : Set.range K.curve = Set.range β.γ)
    (hsmall : Submission.countConst * d < (Nat.min p q : ℝ))
    {c : R3} {σ : Equiv.Perm (Fin 3)} {s u : ℝ}
    (hcount : (↑(Work.BoxShrink.planeCount K c σ s u) : ENNReal)
      ≤ ENNReal.ofReal (5 * (1 + Submission.eps) / Submission.eps * d))
    {ι : Type} [Fintype ι] (C : ι → Work.CoreTopology.ClosedCurve P)
    (hdisj : Pairwise fun i j => Disjoint (Set.range (C i).γ) (Set.range (C j).γ))
    (hsimple : ∀ i, Work.CoreTopology.IsSimple P (C i))
    (hcover : Work.BoxShrink.Pinch.planeTrace P c σ u ⊆ ⋃ i, Set.range (C i).γ)
    (hdich : ∀ i, ¬ Work.CoreTopology.IsEssential P (C i) ∨
      (Nat.min p q : ℕ∞) ≤ Set.encard (Set.range β.γ ∩ Set.range (C i).γ)) :
    ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sliceRegion P s c σ u) := by
  classical
  rintro ⟨γ, hess, hγ⟩
  have hsub : Set.range γ.γ ⊆ ⋃ i, Set.range (C i).γ := by
    rintro y ⟨t, rfl⟩
    exact hcover (sliceRegion_subset_planeTrace (hγ t))
  obtain ⟨i, hi⟩ := Work.InnermostDisk.exists_subset_of_preconnected_iUnion
    (isPreconnected_range γ.cont) ⟨γ.γ 0, ⟨0, rfl⟩⟩ (fun i => Set.range (C i).γ)
    (fun i => Work.InnermostDisk.isClosed_range_closedCurve (C i)) hdisj hsub
  rcases hdich i with hine | hbound
  · exact Work.InnermostDisk.not_isEssential_of_range_subset_isSimple (hsimple i) hi hine hess
  · have heq := isEssential_range_eq_of_range_subset_isSimple (hsimple i) hi hess
    have hsub' : Set.range (C i).γ ⊆ Work.BoxShrink.Core.sliceRegion P s c σ u := by
      rw [← heq]
      rintro y ⟨t, rfl⟩
      exact hγ t
    have hle : (Nat.min p q : ℕ∞) ≤ Set.encard (Set.range β.γ ∩
        Work.BoxShrink.Core.sliceRegion P s c σ u) :=
      le_trans (le_trans hbound (Set.encard_mono (Set.inter_subset_inter_right _ hsub')))
        le_rfl
    have hlt : Work.BoxShrink.planeCount K c σ s u < (Nat.min p q : ℕ∞) :=
      Work.BoxShrink.planeCount_lt (lt_min hp hq) hd hsmall hcount
    have hle' : (Nat.min p q : ℕ∞) ≤ Work.BoxShrink.planeCount K c σ s u :=
      le_trans hle (encard_inter_sliceRegion_le_planeCount β K himg)
    exact absurd (lt_of_lt_of_le hlt hle') (lt_irrefl _)

/-- **The slice is inessential for the tori of the challenge**, from the plane count and a circle
cover of the trace: the special case of `not_containsEssentialLoop_sliceRegion_of_traceCircles` in
which `β` is the image of the standard `(p,q)`-curve under `ψ`, so that
`I(torus ψ, β) = min p q` (`Work.CoreTopology.pardonsI_standard_mapHomeomorph`). -/
theorem not_containsEssentialLoop_sliceRegion_of_traceCircles_mapHomeomorph
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q)
    (ψ : Submission.Diffeo) (K : Knot) {d : ℝ} (hd : 0 ≤ d)
    (himg : Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ)
    (hsmall : Submission.countConst * d < (Nat.min p q : ℝ))
    {c : R3} {σ : Equiv.Perm (Fin 3)} {s u : ℝ}
    (hcount : (↑(Work.BoxShrink.planeCount K c σ s u) : ENNReal)
      ≤ ENNReal.ofReal (5 * (1 + Submission.eps) / Submission.eps * d))
    {ι : Type} [Fintype ι] (C : ι → Work.CoreTopology.ClosedCurve (Work.Smooth.Morse.torus ψ))
    (hdisj : Pairwise fun i j => Disjoint (Set.range (C i).γ) (Set.range (C j).γ))
    (hsimple : ∀ i, Work.CoreTopology.IsSimple (Work.Smooth.Morse.torus ψ) (C i))
    (hcover : Work.BoxShrink.Pinch.planeTrace (Work.Smooth.Morse.torus ψ) c σ u ⊆
      ⋃ i, Set.range (C i).γ)
    (hdich : ∀ i, ¬ Work.CoreTopology.IsEssential (Work.Smooth.Morse.torus ψ) (C i) ∨
      (Nat.min p q : ℕ∞) ≤ Set.encard (Set.range
        (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
          (Work.CoreTopology.standardCurve p q)).γ ∩ Set.range (C i).γ)) :
    ¬ (Work.Smooth.Morse.torus ψ).ContainsEssentialLoop
      (Work.BoxShrink.Core.sliceRegion (Work.Smooth.Morse.torus ψ) s c σ u) :=
  not_containsEssentialLoop_sliceRegion_of_traceCircles
    (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
      (Work.CoreTopology.standardCurve p q)) p q hp hq
    (le_of_eq (Work.CoreTopology.pardonsI_standard_mapHomeomorph p q hp hq hc ψ.toHomeomorph).symm)
    K hd himg hsmall hcount C hdisj hsimple hcover hdich

end

end Work.PinchCounted
