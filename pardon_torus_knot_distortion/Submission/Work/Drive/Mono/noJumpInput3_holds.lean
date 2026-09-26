import Mathlib
import Submission.Work.Drive.Mono.SweepGeom3
import Submission.Work.Drive.Mono.Split
import Submission.Work.Drive.Mono.DichotomyB
import Submission.Work.Drive.Final.noJumpBelow_of_region
import Submission.Work.Drive.Final.AnyEventDefs
import Submission.Work.Drive.Mono.levelCount_lt_min_all
import Submission.Work.Drive.Mono.traceLocallyEuclidean_of_junctionGenC
import Submission.Work.Drive.Mono.frontier_tiltedLevelRemoved_sphereFace
import Submission.Work.Drive.Final.openTiltedSweepRegion_subset_dentOutRegion
import Submission.Work.Drive.Mono.aboveGenericAt_of_junctionGen
import Submission.Work.Drive.Mono.noJumpBelowAt_of_anyEventAt

/-!
# Field (L) of the tilted sweep on the bundle `GoodDataPackage3`: the no-jump

`Work.Drive.Mono.noJumpInput3_holds` is the per-datum no-jump on the *honest* bundle
`Work.Drive.Mono.GoodDataPackage3` (`DataPackage ∧ GoodSweepData3 ∧` the level count at every level of
the window).  The proof splits on whether the level carries an event:

* **no event at the level** — the level's trace is a finite family of pairwise disjoint simple
  *inessential* closed curves (the spheres of `SphereCoverAt` sliced by the surface, with the
  inessentiality from the level count through Pardon's Lemma 2), so the trace argument
  `Work.Drive.Mono.noJumpBelow_of_traceCurves` gives the conclusion.  This half is proved *here*, by
  the observation that dropping the level from the exceptional set preserves `TiltData` and
  `JunctionGenC` (`tiltData_erase`, `junctionGenC_erase`), so that the resident local-model and
  clause-2 lemmas (`traceLocallyEuclidean_of_junctionGenC`, `aboveGenericAt_of_junctionGenC`) apply.
* **an event at the level** — the trace is not a curve family (a saddle gives a crossing), and the
  level must be *resolved* by a dent; this is `Work.Drive.Mono.noJumpBelowAt_of_anyEventAt`
  (the dent layer `Work.Drive.Final.DentOutResolved` at the event, consuming the gates, the
  resolution clause, `W Ω₁ = ⊥` and the union-form genericity).

The docstring of the target theorem records the meaning of `himg`, `hcl` and of the three arithmetic
binders.
-/

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion Set

noncomputable section
/-- The two pull-backs of the sweep height used by `IsFaceEvent` and by `TiltedGenericity` have the
same derivative (they differ by the constant `⟪v,c⟫ + u`). -/
theorem fderiv_sweepHeight_slabFnPar {ψ : Submission.Diffeo} {u : ℝ} {c : R3}
    {v : R3} (p : ℝ × ℝ) :
    fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p =
      fderiv ℝ (Work.Drive.Final.slabFnPar ψ c u v) p := by
  have h1 : (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q))
      = fun q => Work.Drive.Final.slabFnPar ψ c u v q + (inner ℝ v c + u) := by
    funext q
    rw [Work.Drive.Final.slabFnPar_apply, Work.Drive.Final.slabFn_apply]
    ring
  rw [h1, fderiv_add_const]

/-- `TiltedGenericity` survives dropping one level from `exc`, provided no event sits at that level. -/
theorem tiltedGenericity_erase {ψ : Submission.Diffeo} {s u : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {v : R3} {h : ℝ} {ℓ : R3 →L[ℝ] ℝ} {exc : Finset ℝ} {lam : ℝ}
    (hG : Work.Drive.Final.TiltedGenericity ψ s c σ u v h ℓ exc)
    (hnoev : ¬ ∃ pp : ℝ × ℝ, Work.Drive.Final.IsAnyEvent ψ s c σ u v h ℓ pp ∧
      ℓ (Work.BoxShrink.Pinch.par ψ pp) = lam) :
    Work.Drive.Final.TiltedGenericity ψ s c σ u v h ℓ (exc.erase lam) := by
  obtain ⟨h1, h2, h3, h4⟩ := hG
  refine ⟨?_, ?_, ?_, h4⟩
  · intro lam' hne p hpBox hpSlab hℓl
    by_cases h : lam' = lam
    · subst h
      intro hf0
      exact hnoev ⟨p, Or.inl ⟨hpBox, hpSlab, hf0⟩, hℓl⟩
    · exact h1 lam' (fun hmem => hne (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨h, hmem⟩)))
        p hpBox hpSlab hℓl
  · intro lam' hne p hpBox hface hℓl
    by_cases h : lam' = lam
    · subst h
      intro t hft
      have hB : |Work.Drive.Final.slabFn c u v (Work.BoxShrink.Pinch.par ψ p)| = h := by
        rw [Work.Drive.Final.slabFn_apply]; exact hface
      have hT : ∃ t' : ℝ, fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p =
          t' • fderiv ℝ (Work.Drive.Final.slabFnPar ψ c u v) p := by
        refine ⟨t, ?_⟩
        have hcong := fderiv_sweepHeight_slabFnPar (ψ := ψ) (c := c) (u := u) (v := v) p
        rw [hcong] at hft
        exact hft
      have hisF : Work.Drive.Final.IsFaceEvent ψ s c σ u v h ℓ p := ⟨hpBox, hB, hT⟩
      exact hnoev ⟨p, Or.inr (Or.inl hisF), hℓl⟩
    · exact h2 lam' (fun hmem => hne (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨h, hmem⟩)))
        p hpBox hface hℓl
  · intro p hpBox hpSlab hf0
    obtain ⟨hinj, hexc⟩ := h3 p hpBox hpSlab hf0
    refine ⟨hinj, ?_⟩
    by_cases hl : ℓ (Work.BoxShrink.Pinch.par ψ p) = lam
    · exact (hnoev ⟨p, Or.inl ⟨hpBox, hpSlab, hf0⟩, hl⟩).elim
    · exact Finset.mem_erase.mpr ⟨hl, hexc⟩

/-- `TiltData` survives dropping one level from `exc`, provided no event sits at that level. -/
theorem tiltData_erase {ψ : Submission.Diffeo} {s u : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)}
    {v : R3} {h R : ℝ} {ℓ : R3 →L[ℝ] ℝ} {exc : Finset ℝ} {lam0 lam1 lam : ℝ}
    (hT : TiltData ψ s c σ u v h R ℓ exc lam0 lam1)
    (hnoev : ¬ ∃ pp : ℝ × ℝ, Work.Drive.Final.IsAnyEvent ψ s c σ u v h ℓ pp ∧
      ℓ (Work.BoxShrink.Pinch.par ψ pp) = lam) :
    TiltData ψ s c σ u v h R ℓ (exc.erase lam) lam0 lam1 := by
  obtain ⟨hgen, hv1, hℓne, hℓv, hsize, hh, hRbox, hlow, hhigh, hl, hexc⟩ := hT
  exact ⟨tiltedGenericity_erase hgen hnoev, hv1, hℓne, hℓv, hsize, hh, hRbox, hlow, hhigh, hl,
    fun t ht => hexc t (Finset.mem_erase.mp ht).2⟩

/-- `JunctionGenC` survives dropping one level from `exc`, provided no event sits at that level. -/
theorem junctionGenC_erase {ψ : Submission.Diffeo} {s u : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)}
    {v : R3} {h : ℝ} {ℓ : R3 →L[ℝ] ℝ} {exc : Finset ℝ} {lam0 lam1 lam : ℝ}
    (hJ : JunctionGenC ψ s c σ u v h ℓ exc lam0 lam1)
    (hEF : EdgeFree ψ s c σ u v h)
    (hGT : ∀ p : ℝ × ℝ, Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ p) = s →
      |Work.Drive.Final.slabFn c u v (Work.BoxShrink.Pinch.par ψ p)| ≤ h →
      fderiv ℝ (fun q : ℝ × ℝ => Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q)) p ≠ 0 ∧
      ∀ t : ℝ, fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p ≠
        t • fderiv ℝ (fun q : ℝ × ℝ =>
          Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q)) p)
    (hs : 0 < s) (hlam0 : lam0 < lam1)
    (hnoev : ¬ ∃ pp : ℝ × ℝ, Work.Drive.Final.IsAnyEvent ψ s c σ u v h ℓ pp ∧
      ℓ (Work.BoxShrink.Pinch.par ψ pp) = lam) :
    JunctionGenC ψ s c σ u v h ℓ (exc.erase lam) lam0 lam1 := by
  obtain ⟨h1, h2, h3, h4⟩ := hJ
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro lam' hIcc hne z hz hzS hslab hℓl
    by_cases h : lam' = lam
    · subst h
      obtain ⟨p, hp⟩ : ∃ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p = z := hz
      obtain ⟨hb1, hb2⟩ := hGT p (by rw [hp]; exact hzS)
        (by rw [Work.Drive.Final.slabFn_apply, hp]; exact hslab)
      exact ⟨p, hp, (fun h0 => hb2 0 (by rw [h0, zero_smul])), hb1, hb2⟩
    · exact h1 lam' hIcc (fun hmem => hne (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨h, hmem⟩)))
        z hz hzS hslab hℓl
  · intro lam' hIcc hne z hz hzS hface hlt
    by_cases h : lam' = lam
    · subst h
      have hlz_lt_lam1 : ℓ z < lam1 := lt_of_lt_of_le hlt hIcc.2
      have hmax_lt : max lam0 (ℓ z) < lam1 := max_lt hlam0 hlz_lt_lam1
      obtain ⟨β, hβ, hβne⟩ := (Set.Ioo_infinite hmax_lt).exists_notMem_finite exc.finite_toSet
      have hβIcc : β ∈ Set.Icc lam0 lam1 :=
        ⟨le_trans (le_max_left _ _) (le_of_lt hβ.1), le_of_lt hβ.2⟩
      have hβlt : ℓ z < β := lt_of_le_of_lt (le_max_right _ _) hβ.1
      exact h2 β hβIcc hβne z hz hzS hface hβlt
    · exact h2 lam' hIcc (fun hmem => hne (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨h, hmem⟩)))
        z hz hzS hface hlt
  · intro z hz hzS hslab hext
    exact absurd (hEF z hz hzS hext) (not_lt.mpr hslab)
  · intro z hz hzS hface
    refine Finset.mem_erase.mpr ⟨?_, h4 z hz hzS hface⟩
    intro hl
    obtain ⟨p, hp⟩ : ∃ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p = z := hz
    refine hnoev ⟨p, Or.inr (Or.inr ⟨?_, ?_, ?_⟩), ?_⟩
    · rw [hp]
      exact mem_closure_PBox_of_boxNorm_le hs c σ (le_of_eq hzS)
    · rw [hp]; exact hzS
    · rw [hp, Work.Drive.Final.slabFn_apply]; exact hface
    · rw [hp]; exact hl

/-- **The local models of the trace at a level with no event**, from the third bundle: the junction
bundle and the tilt data at the exceptional set with the level removed. -/
theorem traceLocallyEuclidean_of_not_event_direct
    {ψ : Submission.Diffeo} {K : Knot} {s u : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {v : R3}
    {h R : ℝ} {ℓ : R3 →L[ℝ] ℝ} {exc : Finset ℝ} {lam0 lam1 : ℝ} {p q : ℕ}
    (hDP : GoodDataPackage3 ψ K s u c σ v h R ℓ exc lam0 lam1 p q)
    {lam : ℝ} (hlam : lam ∈ Set.Icc lam0 lam1)
    (hnoev : ¬ ∃ pp : ℝ × ℝ, Work.Drive.Final.IsAnyEvent ψ s c σ u v h ℓ pp ∧
      ℓ (Work.BoxShrink.Pinch.par ψ pp) = lam) :
    ∀ z : R3, z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier ∩
        frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam) →
      ∃ O : Set R3, IsOpen O ∧ z ∈ O ∧
        Work.Smooth.OneManifold.IsLocallyEuclidean
          (O ∩ ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
            frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam))) := by
  obtain ⟨hdata, hG3, -⟩ := hDP
  obtain ⟨hGS2, hEF, hBelt, hSBCR, hGT, hFRC, hCorner, hOffK, hOne, hSph⟩ := hG3
  obtain ⟨-, -, -, -, -, -, -, -, -, hl, -⟩ := hdata.tilt
  have hs : 0 < s := by
    obtain ⟨y, hy, -⟩ := hdata.slabCuts.1
    have h1 : Submission.boxNorm c σ y < s := (Submission.mem_PBox_iff s c σ y).mp hy
    have h2 : 0 ≤ Submission.boxNorm c σ y := Submission.boxNorm_nonneg c σ y
    linarith
  refine traceLocallyEuclidean_of_junctionGenC (ψ := ψ) (s := s) (u := u) (c := c) (σ := σ)
    (v := v) (h := h) (R := R) (ℓ := ℓ) (exc := exc.erase lam) (lam0 := lam0) (lam1 := lam1)
    (lam := lam) hs hdata.slicing hdata.faceReg (tiltData_erase hdata.tilt hnoev)
    (junctionGenC_erase hdata.junc hEF hGT hs hl hnoev) hlam ?_
  intro hmem
  exact (Finset.mem_erase.mp (Finset.mem_coe.mp hmem)).1 rfl

/-- **A member of a finite cover of a set by closed pieces pairwise disjoint on the surface is
relatively open in the surface's part of the union.** -/
theorem isOpenInSet_of_sphereCover
    {P : Work.CoreTopology.ParamTorus} {m : ℕ} {Ss : Fin m → Set R3}
    (hcl : ∀ i, IsClosed (Ss i))
    (hdisj : ∀ i j : Fin m, i ≠ j →
      Disjoint (Ss i ∩ P.carrier) (Ss j ∩ P.carrier)) (i : Fin m) :
    Work.Smooth.OneManifold.IsOpenInSet (P.carrier ∩ ⋃ j, Ss j) (Ss i ∩ P.carrier) := by
  classical
  have hopen : IsOpen ((⋃ j ∈ (Finset.univ.filter (fun j : Fin m => j ≠ i)), Ss j)ᶜ) :=
    (isClosed_biUnion_finset (fun j _ => hcl j)).isOpen_compl
  have h1 : (Subtype.val ⁻¹' (Ss i ∩ P.carrier) : Set ↥(P.carrier ∩ ⋃ j, Ss j)) =
      Subtype.val ⁻¹' (⋃ j ∈ (Finset.univ.filter (fun j : Fin m => j ≠ i)), Ss j)ᶜ := by
    ext x
    constructor
    · intro hx
      rw [Set.mem_preimage, Set.mem_compl_iff, Set.mem_iUnion₂]
      rintro ⟨j, hj, hxj⟩
      exact (Set.disjoint_left.mp (hdisj i j (Ne.symm (Finset.mem_filter.mp hj).2)))
        hx ⟨hxj, x.2.1⟩
    · intro hx
      rw [Set.mem_preimage] at hx
      rw [Set.mem_preimage]
      have hxU : (x : R3) ∈ ⋃ j, Ss j := x.2.2
      obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hxU
      have hji : j = i := by
        by_contra hne
        exact hx (Set.mem_iUnion₂.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hne⟩, hxj⟩)
      rw [hji] at hxj
      exact ⟨hxj, x.2.1⟩
  rw [Work.Smooth.OneManifold.IsOpenInSet, h1]
  exact hopen.preimage continuous_subtype_val

/-- **The inessentiality of the level's trace from a sphere cover of the level frontier and the
level count.**  This is the extraction of the argument of
`Work.Drive.Mono.traceCurvesAt_of_sphereDecomposition` that only needs the cover of the frontier by
embedded spheres pairwise disjoint *on the surface*, together with the local Euclidean structure of
each sphere's trace and the count. -/
theorem not_containsEssentialLoop_of_sphereCover
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q)
    (ψ : Submission.Diffeo) (K : LeanEval.KnotTheory.PardonDistortion.Knot)
    (himg : Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ)
    (hcl : Work.Drive.CleansDiscsWd (Work.Drive.EpsSphere.torusOf ψ))
    {s u h lam : ℝ} {c v : R3} {σ : Equiv.Perm (Fin 3)} {ℓ : R3 →L[ℝ] ℝ}
    {m : ℕ} {Ss : Fin m → Set R3}
    (hdecomp : frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam) = ⋃ i, Ss i)
    (hdisj : ∀ i j : Fin m, i ≠ j →
      Disjoint (Ss i ∩ (Work.Drive.EpsSphere.torusOf ψ).carrier)
        (Ss j ∩ (Work.Drive.EpsSphere.torusOf ψ).carrier))
    (hsph : ∀ i, Work.InnermostDisk.IsEmbeddedSphere (Ss i))
    (hlocI : ∀ i, Work.Smooth.OneManifold.IsLocallyEuclidean
      (Ss i ∩ (Work.Drive.EpsSphere.torusOf ψ).carrier))
    (hcount : Set.encard (Set.range K.curve ∩
      frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam)) < (Nat.min p q : ℕ∞)) :
    ¬ (Work.Drive.EpsSphere.torusOf ψ).ContainsEssentialLoop
      (frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam)) := by
  classical
  set P := Work.Drive.EpsSphere.torusOf ψ with hP
  have hsub_i : ∀ i, Ss i ⊆
      frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam) := by
    intro i
    rw [hdecomp]
    exact Set.subset_iUnion _ i
  have hcomp_i : ∀ i, IsCompact (Ss i ∩ P.carrier) := by
    intro i
    obtain ⟨e, -, he⟩ := hsph i
    have hcomp' : IsCompact (Ss i) := by
      rw [← he]
      exact isCompact_range e.continuous
    exact hcomp'.inter_right (Work.Smooth.Morse.Surface.isCompact_torus ψ).isClosed
  have hclosed_i : ∀ i, IsClosed (Ss i ∩ P.carrier) := fun i => (hcomp_i i).isClosed
  have hnoess_i : ∀ i, ¬ P.ContainsEssentialLoop (Ss i) := by
    intro i
    obtain ⟨Sl⟩ := sphereSlicing_of_isEmbeddedSphere_of_localModels (P := P) (S := Ss i)
      (hsph i) (hcomp_i i) (hlocI i)
    refine Work.EpsW.trace_inessential_of_slicing_of_countsWd p q hp hq hc ψ K himg Sl hcl ?_
    refine lt_of_le_of_lt (Set.encard_le_encard ?_) hcount
    rintro x ⟨hxK, hxS⟩
    exact ⟨hxK, hsub_i i hxS⟩
  rintro ⟨γ, hγess, hγ⟩
  have hsub : Set.range γ.γ ⊆ ⋃ i, (Ss i ∩ P.carrier) := by
    rintro x ⟨t, rfl⟩
    have hx : γ.γ t ∈ frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam) := hγ t
    rw [hdecomp] at hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨i, hi, γ.mem t⟩
  have hpre : IsPreconnected (Set.range γ.γ) := by
    rw [Work.CoreTopology.ClosedCurve.range_eq_image P γ]
    exact isPreconnected_Ico.image γ.γ γ.cont.continuousOn
  obtain ⟨i, hi⟩ := Work.InnermostDisk.exists_subset_of_preconnected_iUnion hpre
    ⟨γ.γ 0, ⟨0, rfl⟩⟩ (fun i => Ss i ∩ P.carrier) hclosed_i
    (fun i j hij => hdisj i j hij) hsub
  exact hnoess_i i ⟨γ, hγess, fun t => (hi ⟨t, rfl⟩).1⟩

/-- Clause 2 of the trace data at a level with no event, from the third bundle. -/
theorem aboveGenericAt_of_not_event_direct
    {ψ : Submission.Diffeo} {K : LeanEval.KnotTheory.PardonDistortion.Knot} {s u : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {v : R3} {h R : ℝ} {ℓ : R3 →L[ℝ] ℝ} {exc : Finset ℝ}
    {lam0 lam1 : ℝ} {p q : ℕ}
    (hDP : GoodDataPackage3 ψ K s u c σ v h R ℓ exc lam0 lam1 p q)
    {lam : ℝ} (hlam : lam ∈ Set.Icc lam0 lam1)
    (hnoev : ¬ ∃ pp : ℝ × ℝ, Work.Drive.Final.IsAnyEvent ψ s c σ u v h ℓ pp ∧
      ℓ (Work.BoxShrink.Pinch.par ψ pp) = lam) :
    Work.Drive.Mono.AboveGenericAt (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ lam := by
  obtain ⟨hdata, hG3, -⟩ := hDP
  obtain ⟨hGS2, hEF, hBelt, hSBCR, hGT, hFRC, hCorner, hOffK, hOne, hSph⟩ := hG3
  obtain ⟨-, -, -, -, -, -, -, -, -, hl, -⟩ := hdata.tilt
  have hs : 0 < s := by
    obtain ⟨y, hy, -⟩ := hdata.slabCuts.1
    have h1 : Submission.boxNorm c σ y < s := (Submission.mem_PBox_iff s c σ y).mp hy
    have h2 : 0 ≤ Submission.boxNorm c σ y := Submission.boxNorm_nonneg c σ y
    linarith
  exact aboveGenericAt_of_junctionGenC (ψ := ψ) (s := s) (u := u) (c := c) (σ := σ) (v := v)
    (h := h) (R := R) (ℓ := ℓ) (exc := exc.erase lam) (lam0 := lam0) (lam1 := lam1)
    (lam := lam) hs (tiltData_erase hdata.tilt hnoev)
    (junctionGenC_erase hdata.junc hEF hGT hs hl hnoev) hlam
    (fun hmem => (Finset.mem_erase.mp (Finset.mem_coe.mp hmem)).1 rfl)

/-- Clause 1 of the trace data at a level with no event, from the third bundle. -/
theorem traceCurvesAt_of_not_event_direct
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q)
    (ψ : Submission.Diffeo) (K : LeanEval.KnotTheory.PardonDistortion.Knot)
    (himg : Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ)
    (hcl : Work.Drive.CleansDiscsWd (Work.Drive.EpsSphere.torusOf ψ))
    {s u : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {v : R3} {h R : ℝ} {ℓ : R3 →L[ℝ] ℝ}
    {exc : Finset ℝ} {lam0 lam1 : ℝ}
    (hDP : GoodDataPackage3 ψ K s u c σ v h R ℓ exc lam0 lam1 p q)
    {lam : ℝ} (hlam : lam ∈ Set.Icc lam0 lam1)
    (hnoev : ¬ ∃ pp : ℝ × ℝ, Work.Drive.Final.IsAnyEvent ψ s c σ u v h ℓ pp ∧
      ℓ (Work.BoxShrink.Pinch.par ψ pp) = lam) :
    Work.Drive.Mono.TraceCurvesAt (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ lam := by
  have hlocZ : Work.Smooth.OneManifold.IsLocallyEuclidean
      ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
        frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam)) :=
    isLocallyEuclidean_trace_of_local_models
      (traceLocallyEuclidean_of_not_event_direct hDP hlam hnoev)
  obtain ⟨hdata, hG3, hcount3⟩ := hDP
  obtain ⟨hGS2, hEF, hBelt, hSBCR, hGT, hFRC, hCorner, hOffK, hOne, hSph⟩ := hG3
  obtain ⟨m, Ss, hsph, hdisj, hdecomp⟩ := hSph lam hlam
  have hsub_i : ∀ i, Ss i ⊆
      frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam) := by
    intro i
    rw [hdecomp]
    exact Set.subset_iUnion _ i
  have hclosed_i : ∀ i, IsClosed (Ss i) := by
    intro i
    obtain ⟨e, -, he⟩ := hsph i
    rw [← he]
    exact (isCompact_range e.continuous).isClosed
  have hlocU : Work.Smooth.OneManifold.IsLocallyEuclidean
      ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩ ⋃ i, Ss i) := by
    rw [← hdecomp]
    exact hlocZ
  have hlocI : ∀ i, Work.Smooth.OneManifold.IsLocallyEuclidean
      (Ss i ∩ (Work.Drive.EpsSphere.torusOf ψ).carrier) := fun i =>
    Work.Smooth.OneManifold.IsLocallyEuclidean.of_isOpenIn
      (Z := (Work.Drive.EpsSphere.torusOf ψ).carrier ∩ ⋃ j, Ss j)
      (V := Ss i ∩ (Work.Drive.EpsSphere.torusOf ψ).carrier)
      (fun x hx => ⟨hx.2, by rw [← hdecomp]; exact hsub_i i hx.1⟩)
      (isOpenInSet_of_sphereCover hclosed_i hdisj i) hlocU
  exact traceCurvesAt_of_isLocallyEuclidean
    (isCompact_trace_torusOf ψ s u c σ v h ℓ lam) hlocZ
    (not_containsEssentialLoop_of_sphereCover p q hp hq hc ψ K himg hcl hdecomp hdisj hsph hlocI
      (hcount3 lam hlam))

/-- **The no-jump at a level with no event**, by the trace argument. -/
theorem noJumpBelowAt_of_noEventAt_direct
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q)
    (ψ : Submission.Diffeo) (K : LeanEval.KnotTheory.PardonDistortion.Knot)
    (himg : Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ)
    (hcl : Work.Drive.CleansDiscsWd (Work.Drive.EpsSphere.torusOf ψ))
    {s u : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {v : R3} {h R : ℝ} {ℓ : R3 →L[ℝ] ℝ}
    {exc : Finset ℝ} {lam0 lam1 : ℝ}
    (hDP : GoodDataPackage3 ψ K s u c σ v h R ℓ exc lam0 lam1 p q)
    {lam : ℝ} (hlam : lam ∈ Set.Icc lam0 lam1)
    (hnoev : ¬ ∃ pp : ℝ × ℝ, Work.Drive.Final.IsAnyEvent ψ s c σ u v h ℓ pp ∧
      ℓ (Work.BoxShrink.Pinch.par ψ pp) = lam)
    (hbot : Work.SurgeryInvariance.WindingSpan (Work.Drive.EpsSphere.torusOf ψ)
      (Work.Drive.Final.sweep (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ lam) = ⊥) :
    ∃ mu0 : ℝ, mu0 < lam ∧ ∀ mu ∈ Set.Ico mu0 lam,
      Work.SurgeryInvariance.WindingSpan (Work.Drive.EpsSphere.torusOf ψ)
        (Work.Drive.Final.sweep (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ mu) ≠ ⊤ := by
  obtain ⟨-, hv1, hℓne, hℓv, -⟩ := hDP.1.tilt
  have hv : v ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hv1
    exact one_ne_zero hv1.symm
  exact noJumpBelow_of_traceCurves (P := Work.Drive.EpsSphere.torusOf ψ) (s := s) (c := c)
    (σ := σ) (u := u) (v := v) (h := h) (ℓ := ℓ) (lam := lam) hv hℓv hℓne
    (traceCurvesAt_of_not_event_direct p q hp hq hc ψ K himg hcl hDP hlam hnoev)
    (aboveGenericAt_of_not_event_direct hDP hlam hnoev) hbot

/-- **The regular box-sphere points of the level lie in `closure Ω₁`.**  A point `z` of the surface
on the box sphere, in the closed slab, at the level of the dent's centre, is a limit of points of the
dent's preimage region `Ω₁`: the non-parallelness of the sweep height and the box norm at `z`
(`GammaTransverse`, which the third bundle carries *universally*) produces points of the surface
inside the box and strictly above the level, arbitrarily close to `z`, all of which lie in the open
sweep region, hence in `Ω₁`. -/
theorem mem_closure_dentOutRegion_of_boxNorm_eq
    {ψ : Submission.Diffeo} {K : LeanEval.KnotTheory.PardonDistortion.Knot} {s u : ℝ}
    {c : LeanEval.KnotTheory.PardonDistortion.R3} {σ : Equiv.Perm (Fin 3)}
    {v : LeanEval.KnotTheory.PardonDistortion.R3} {h R : ℝ}
    {ℓ : LeanEval.KnotTheory.PardonDistortion.R3 →L[ℝ] ℝ}
    {U : Set LeanEval.KnotTheory.PardonDistortion.R3}
    (D : Work.Drive.Final.AnyDentDatum ψ K s c σ u v h R ℓ U)
    (hGT : ∀ p : ℝ × ℝ, Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ p) = s →
      |Work.Drive.Final.slabFn c u v (Work.BoxShrink.Pinch.par ψ p)| ≤ h →
      fderiv ℝ (fun q : ℝ × ℝ => Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q)) p ≠ 0 ∧
      ∀ t : ℝ, fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p ≠
        t • fderiv ℝ (fun q : ℝ × ℝ =>
          Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q)) p)
    {z : LeanEval.KnotTheory.PardonDistortion.R3}
    (hzc : z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier)
    (hzS : Submission.boxNorm c σ z = s)
    (hzslab : |Work.Drive.Final.slabFn c u v z| ≤ h)
    (hzl : ℓ z = ℓ D.centre) :
    z ∈ closure (Work.Drive.Final.dentOutRegion ψ s c σ u v h R ℓ D) := by
  obtain ⟨p, hp⟩ : ∃ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p = z := hzc
  obtain ⟨hgne, hind⟩ := hGT p (by rw [hp]; exact hzS)
    (by rw [Work.Drive.Final.slabFn_apply]; rwa [hp])
  have hfne : fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p ≠ 0 :=
    fun h0 => hind 0 (by rw [h0, zero_smul])
  have hfderiv : HasFDerivAt (Work.Drive.EpsForm.sweepHeight ψ ℓ)
      (fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p) p :=
    (((Work.Smooth.Morse.pullback_contDiff_one ψ
        (ℓ.contDiff : ContDiff ℝ 1 (fun y : LeanEval.KnotTheory.PardonDistortion.R3 => ℓ y))
      ).contDiffAt.differentiableAt one_ne_zero)).hasFDerivAt
  have hgderiv : HasFDerivAt
      (fun q : ℝ × ℝ => Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q))
      (fderiv ℝ (fun q : ℝ × ℝ =>
        Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q)) p) p := by
    have hd : DifferentiableAt ℝ (fun q : ℝ × ℝ =>
        Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q)) p := by
      by_contra h
      rw [fderiv_zero_of_not_differentiableAt h] at hgne
      exact hgne rfl
    exact hd.hasFDerivAt
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hcont : ContinuousAt (Work.BoxShrink.Pinch.par ψ) p := by
    rw [Work.BoxShrink.Pinch.par_def]
    exact (Work.Smooth.Morse.param_continuous ψ).continuousAt
  obtain ⟨δ, hδpos, hδ⟩ := Metric.continuousAt_iff.mp hcont ε hε
  obtain ⟨q, hq, hqf, hqg⟩ :=
    Work.Drive.Mono.exists_near_lt_of_fderiv_indep hfderiv hgderiv hfne hgne hind δ hδpos
  refine ⟨Work.BoxShrink.Pinch.par ψ q, ?_, ?_⟩
  · refine Work.Drive.Final.openTiltedSweepRegion_subset_dentOutRegion D ?_
    rw [Work.Drive.Mono.mem_openTiltedSweepRegion_iff]
    refine ⟨Work.BoxShrink.Pinch.par_mem_carrier ψ q, ?_, ?_⟩
    · exact (Submission.mem_PBox_iff s c σ _).mpr (by rw [← hzS, ← hp]; exact hqg)
    · intro hcon
      have hle : ℓ (Work.BoxShrink.Pinch.par ψ q) ≤ ℓ D.centre := hcon.2
      have hlt : ℓ (Work.BoxShrink.Pinch.par ψ q) > ℓ D.centre := by
        rw [← hzl, ← hp]; exact hqf
      linarith
  · have h1 : dist (Work.BoxShrink.Pinch.par ψ q) z < ε := by
      have h2 := hδ (by simpa [dist_eq_norm] using hq)
      rwa [hp] at h2
    rwa [dist_comm]

/-- **Field (L): the no-jump, per datum, on the honest bundle `GoodDataPackage3`.**  At every datum
satisfying `Work.Drive.Mono.GoodDataPackage3` — `Work.Drive.Mono.DataPackage` (the tilt data, the
junction genericity `JunctionGenC`, the face regularity, `SlabCutsBox`, the slicing of the box sphere,
the disjoint-sphere decomposition `LevelSphereDecomposition` of the level frontier and the level
count off `exc`), together with `Work.Drive.Final.GoodSweepData3` (the three event types with *one
event per level*, `EdgeFree`, the universal `SlabBoxCrossReg`, `GammaTransverse`, `FaceRegClosed`,
`offK` for all three types and the sphere cover `SphereCoverAt` at every level of the window), together
with the **level count at every level of the window** (`Work.Drive.Mono.levelCount_lt_min_all`'s
conclusion, whose hypotheses are the non-grazing package that the producer establishes) — at every
level of the window at which the level region's winding span vanishes, no level just below carries the
full span.

The hypotheses `0 < p`, `0 < q` and `Nat.Coprime p q` are binders of
`Work.Drive.Mono.GoodNoJumpInput3` itself (as in `Work.Drive.Mono.GoodSweepGeomAEG3`), because the
counting route needs the essentiality threshold `min p q`, which only bounds the transversal count for
coprime `p q`.  (The definition on disk additionally binds the distortion data `d`, `0 ≤ d`,
`countConst * d < min p q` and the box-sphere count `hS` of the crux; those binders are carried along
for the consumer's threading and are *not* consumed by the proof below — see
`Submission/Work/Drive/Mono/NOTES_noEventAt_PROVED.md` §5.)

The hypotheses `himg` (the knot is the standard `(p,q)` curve composed with `ψ`) and `hcl`
(`Work.Drive.CleansDiscsWd`) are needed because in this workspace the *inessentiality* of the level's
trace comes from Pardon's counting through
`Work.EpsW.trace_inessential_of_slicing_of_countsWd`, whose consumers require both; without them the
statement has no content tying the knot to the surface, as the prover of the earlier spelling
diagnosed in `Submission/Work/Drive/Mono/NOTES_noJumpInput3_holds_FALSE.md` §1–§5. -/
theorem noJumpInput3_holds : ∀ p q : ℕ, Work.Drive.Mono.GoodNoJumpInput3 p q := by
  intro p q hp hq hc ψ K himg hcl s u c σ v h R ℓ exc lam0 lam1 d hd hsmall hS hDP lam hlam hbot
  by_cases hev : ∃ pp : ℝ × ℝ, Work.Drive.Final.IsAnyEvent ψ s c σ u v h ℓ pp ∧
      ℓ (Work.BoxShrink.Pinch.par ψ pp) = lam
  · exact noJumpBelowAt_of_anyEventAt p q hp hq hc ψ K himg hcl hDP hlam hev hbot
  · exact noJumpBelowAt_of_noEventAt_direct p q hp hq hc ψ K himg hcl hDP hlam hev hbot

end

end Work.Drive.Mono
