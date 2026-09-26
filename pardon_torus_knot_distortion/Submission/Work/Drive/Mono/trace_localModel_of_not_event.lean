import Mathlib
import Submission.Work.Drive.Mono.SweepGeom3
import Submission.Work.Drive.Mono.Split
import Submission.Work.Drive.Mono.traceLocallyEuclidean_of_junctionGenC
import Submission.Work.Topology.SphereSlicing.frontier_PBox

/-!
# The local model of the trace at a level carrying no event

`Work.Drive.Mono.GoodDataPackage3` carries the tilt data (`TiltData`), the corrected junction
genericity (`JunctionGenC`), the face regularity, the slicing of the box sphere and the
disjoint-sphere decomposition — but the genericity clauses of the first two are stated *off the
exceptional set* `exc`.  The point of this module is that at a level `lam` which carries **no event
of any of the three types** (`Work.Drive.Final.IsAnyEvent`), the whole local-model analysis of
`Work.Drive.Mono.traceLocallyEuclidean_of_junctionGenC` still runs, at the *enlarged* exceptional set

  `exc' = exc.erase lam`   (so that `lam` becomes non-exceptional),

because each clause of `TiltedGenericity` and of `JunctionGenC` that is only available off `exc`
becomes true at `lam` from the absence of an event:

* clause (1) of `TiltedGenericity` (regularity of the sweep height in the box ∩ slab): its failure
  at `lam` is exactly an `IsEvent` of value `lam`;
* clause (2) (transversality of the wall with the slab faces): its failure is an `IsFaceEvent` of
  value `lam`;
* clause (iii) puts the values of the interior critical points in `exc`; the value cannot be `lam`,
  so it survives the erasure;
* clause (a) of `JunctionGenC` is a consequence of the *universal* clause `GammaTransverse` of
  `GoodSweepData3`;
* clause (b) is *level-independent in its conclusion*: at `lam` one evaluates it at an auxiliary
  level `lam'' ∈ (max (ℓ z) lam0, lam1) \ exc`, which exists because `exc` is finite;
* clause (c) is vacuous by `EdgeFree`;
* clause (d) puts the value of a corner point in `exc`; a corner of value `lam` *is* an `IsCornerEvent`
  of value `lam`, hence excluded, so the value survives the erasure.

The assembly is then a verbatim application of
`Work.Drive.Mono.traceLocallyEuclidean_of_junctionGenC`.
-/

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion Set

noncomputable section

/-! ## 1. Auxiliaries -/

/-- The derivative of the pulled-back slab functional is the derivative of the pulled-back normal
functional (the shift `⟪v,c⟫ + u` is constant). -/
theorem fderiv_slabFnPar_eq_aux (ψ : Submission.Diffeo) (c v : R3) (u : ℝ) (p : ℝ × ℝ) :
    fderiv ℝ (Work.Drive.Final.slabFnPar ψ c u v) p =
      fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p := by
  have h1 : Work.Drive.Final.slabFnPar ψ c u v =
      fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q) - (inner ℝ v c + u) := rfl
  rw [h1]
  exact fderiv_sub_const _

/-- A point of the box sphere lies in the closure of the box. -/
theorem mem_closure_PBox_of_boxNorm_eq {s : ℝ} (hs : 0 < s) {c : R3} {σ : Equiv.Perm (Fin 3)}
    {y : R3} (h : Submission.boxNorm c σ y = s) : y ∈ closure (Submission.PBox s c σ) := by
  refine frontier_subset_closure ?_
  rw [Work.Topology.SphereSlicing.frontier_PBox hs c σ]
  exact h

/-- There is a real number strictly between `a` and `b` which avoids a finite set. -/
theorem exists_level_gt_finset (exc : Finset ℝ) {a b : ℝ} (hab : a < b) :
    ∃ t : ℝ, a < t ∧ t < b ∧ t ∉ (exc : Set ℝ) := by
  obtain ⟨t, ht, htf⟩ := (Set.Ioo_infinite hab).exists_notMem_finset exc
  exact ⟨t, ht.1, ht.2, fun h => htf (Finset.mem_coe.mp h)⟩

/-! ## 2. The genericity of `TiltedGenericity` at a level carrying no event -/

/-- **`TiltedGenericity` survives the erasure of an event-free level from `exc`.** -/
theorem tiltedGenericity_erase_of_no_event {ψ : Submission.Diffeo} {s u : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {v : R3} {h : ℝ} {ℓ : R3 →L[ℝ] ℝ} {exc : Finset ℝ} {lam : ℝ}
    (hG : Work.Drive.Final.TiltedGenericity ψ s c σ u v h ℓ exc)
    (hnoev : ∀ p : ℝ × ℝ, Work.Drive.Final.IsAnyEvent ψ s c σ u v h ℓ p →
      ℓ (Work.BoxShrink.Pinch.par ψ p) ≠ lam) :
    Work.Drive.Final.TiltedGenericity ψ s c σ u v h ℓ (exc.erase lam) := by
  refine ⟨?_, ?_, ?_, hG.2.2.2⟩
  · intro lam' hne' p hpP hpS hpl hf
    by_cases h : lam' = lam
    · subst h
      exact hnoev p (Or.inl ⟨hpP, hpS, hf⟩) hpl
    · exact hG.1 lam' (fun hmem => hne' (by
        rw [Finset.mem_coe, Finset.mem_erase]
        exact ⟨h, Finset.mem_coe.mp hmem⟩)) p hpP hpS hpl hf
  · intro lam' hne' p hpP hpabs hpl t ht
    by_cases h : lam' = lam
    · subst h
      exact hnoev p (Or.inr (Or.inl ⟨hpP, by rw [Work.Drive.Final.slabFn_apply]; exact hpabs,
        ⟨t, by rw [ht, fderiv_slabFnPar_eq_aux]⟩⟩)) hpl
    · exact hG.2.1 lam' (fun hmem => hne' (by
        rw [Finset.mem_coe, Finset.mem_erase]
        exact ⟨h, Finset.mem_coe.mp hmem⟩)) p hpP hpabs hpl t ht
  · intro p hpP hpS hf
    obtain ⟨hinj, hexc⟩ := hG.2.2.1 p hpP hpS hf
    refine ⟨hinj, ?_⟩
    have hne : ℓ (Work.BoxShrink.Pinch.par ψ p) ≠ lam := hnoev p (Or.inl ⟨hpP, hpS, hf⟩)
    rw [Finset.mem_erase]
    exact ⟨hne, hexc⟩

/-- **`TiltData` survives the erasure of an event-free level from `exc`.** -/
theorem tiltData_erase_of_no_event {ψ : Submission.Diffeo} {s u : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {v : R3} {h R : ℝ} {ℓ : R3 →L[ℝ] ℝ} {exc : Finset ℝ}
    {lam0 lam1 lam : ℝ}
    (hT : TiltData ψ s c σ u v h R ℓ exc lam0 lam1)
    (hnoev : ∀ p : ℝ × ℝ, Work.Drive.Final.IsAnyEvent ψ s c σ u v h ℓ p →
      ℓ (Work.BoxShrink.Pinch.par ψ p) ≠ lam) :
    TiltData ψ s c σ u v h R ℓ (exc.erase lam) lam0 lam1 := by
  obtain ⟨hgen, hv1, hℓne, hℓv, hsize, hh, hRbox, hlow, hhigh, hl, hexc⟩ := hT
  exact ⟨tiltedGenericity_erase_of_no_event hgen hnoev, hv1, hℓne, hℓv, hsize, hh, hRbox,
    hlow, hhigh, hl, fun t ht => hexc t (Finset.mem_of_mem_erase ht)⟩

/-! ## 3. The junction bundle at a level carrying no event -/

/-- **`JunctionGenC` survives the erasure of an event-free level from `exc`**, provided the universal
transversality of `GoodSweepData3` and `EdgeFree` are available. -/
theorem junctionGenC_erase_of_no_event {ψ : Submission.Diffeo} {s u : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {v : R3} {h : ℝ} {ℓ : R3 →L[ℝ] ℝ} {exc : Finset ℝ}
    {lam0 lam1 lam : ℝ}
    (hs : 0 < s)
    (hJ : JunctionGenC ψ s c σ u v h ℓ exc lam0 lam1)
    (h01 : lam0 < lam1)
    (hΓ : ∀ p : ℝ × ℝ, Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ p) = s →
      |Work.Drive.Final.slabFn c u v (Work.BoxShrink.Pinch.par ψ p)| ≤ h →
      fderiv ℝ (fun q : ℝ × ℝ => Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q)) p ≠ 0 ∧
      ∀ t : ℝ, fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p ≠
        t • fderiv ℝ (fun q : ℝ × ℝ => Submission.boxNorm c σ
          (Work.BoxShrink.Pinch.par ψ q)) p)
    (hEF : EdgeFree ψ s c σ u v h)
    (hnoev : ∀ p : ℝ × ℝ, Work.Drive.Final.IsAnyEvent ψ s c σ u v h ℓ p →
      ℓ (Work.BoxShrink.Pinch.par ψ p) ≠ lam) :
    JunctionGenC ψ s c σ u v h ℓ (exc.erase lam) lam0 lam1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro lam' hlam' hne' z hz hzs hslab hzl
    by_cases h : lam' = lam
    · subst h
      obtain ⟨p, hp⟩ := (show z ∈ Set.range (Work.BoxShrink.Pinch.par ψ) from hz)
      obtain ⟨hB, hind⟩ := hΓ p (by rw [hp]; exact hzs)
        (by rw [hp, Work.Drive.Final.slabFn_apply]; exact hslab)
      refine ⟨p, hp, ?_, hB, hind⟩
      intro hF
      exact hind 0 (by rw [hF, zero_smul])
    · exact hJ.1 lam' hlam' (fun hmem => hne' (by
        rw [Finset.mem_coe, Finset.mem_erase]
        exact ⟨h, Finset.mem_coe.mp hmem⟩)) z hz hzs hslab hzl
  · intro lam' hlam' hne' z hz hzs hslab hzlt
    by_cases h : lam' = lam
    · subst h
      have hx : ℓ z < lam1 := lt_of_lt_of_le hzlt hlam'.2
      obtain ⟨t, ht1, ht2, ht3⟩ := exists_level_gt_finset exc (a := max (ℓ z) lam0)
        (b := lam1) (max_lt hx h01)
      exact hJ.2.1 t ⟨le_of_lt (lt_of_le_of_lt (le_max_right _ _) ht1), le_of_lt ht2⟩ ht3
        z hz hzs hslab (lt_of_le_of_lt (le_max_left _ _) ht1)
    · exact hJ.2.1 lam' hlam' (fun hmem => hne' (by
        rw [Finset.mem_coe, Finset.mem_erase]
        exact ⟨h, Finset.mem_coe.mp hmem⟩)) z hz hzs hslab hzlt
  · intro z hz hzs hslab hext
    exact absurd (hEF z hz hzs hext) (not_lt.mpr hslab)
  · intro z hz hzs hslab
    have hmem : ℓ z ∈ (exc : Set ℝ) := hJ.2.2.2 z hz hzs hslab
    have hne : ℓ z ≠ lam := by
      intro heq
      obtain ⟨p, hp⟩ := (show z ∈ Set.range (Work.BoxShrink.Pinch.par ψ) from hz)
      have hclos : Work.BoxShrink.Pinch.par ψ p ∈ closure (Submission.PBox s c σ) := by
        rw [hp]
        exact mem_closure_PBox_of_boxNorm_eq hs hzs
      have hbox : Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ p) = s := by
        rw [hp]; exact hzs
      have hsl : |Work.Drive.Final.slabFn c u v (Work.BoxShrink.Pinch.par ψ p)| = h := by
        rw [Work.Drive.Final.slabFn_apply, hp]; exact hslab
      have hev : ℓ (Work.BoxShrink.Pinch.par ψ p) = lam := by rw [hp]; exact heq
      exact hnoev p (Or.inr (Or.inr ⟨hclos, hbox, hsl⟩)) hev
    rw [Finset.mem_coe, Finset.mem_erase]
    exact ⟨hne, Finset.mem_coe.mp hmem⟩

/-! ## 4. The main theorem -/

theorem trace_localModel_of_not_event
    {ψ : Submission.Diffeo} {K : LeanEval.KnotTheory.PardonDistortion.Knot} {s u : ℝ}
    {c : LeanEval.KnotTheory.PardonDistortion.R3} {σ : Equiv.Perm (Fin 3)}
    {v : LeanEval.KnotTheory.PardonDistortion.R3} {h R : ℝ}
    {ℓ : LeanEval.KnotTheory.PardonDistortion.R3 →L[ℝ] ℝ} {exc : Finset ℝ} {lam0 lam1 : ℝ}
    {p q : ℕ}
    (hDP : Work.Drive.Mono.GoodDataPackage3 ψ K s u c σ v h R ℓ exc lam0 lam1 p q)
    {lam : ℝ} (hlam : lam ∈ Set.Icc lam0 lam1)
    (hnoev : ¬ ∃ pp : ℝ × ℝ, Work.Drive.Final.IsAnyEvent ψ s c σ u v h ℓ pp ∧
      ℓ (Work.BoxShrink.Pinch.par ψ pp) = lam) :
    ∀ z : LeanEval.KnotTheory.PardonDistortion.R3,
      z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier ∩
        frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam) →
      ∃ O : Set LeanEval.KnotTheory.PardonDistortion.R3, IsOpen O ∧ z ∈ O ∧
        Work.Smooth.OneManifold.IsLocallyEuclidean
          (O ∩ ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
            frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam))) := by
  obtain ⟨hData, hG3, -⟩ := hDP
  obtain ⟨-, hEF, -, -, hΓ, -, -, -, -, -⟩ := hG3
  obtain ⟨hT, hJ, hfaceReg, hslabCuts, hslice, -, -⟩ := hData
  have hnoev' : ∀ pp : ℝ × ℝ, Work.Drive.Final.IsAnyEvent ψ s c σ u v h ℓ pp →
      ℓ (Work.BoxShrink.Pinch.par ψ pp) ≠ lam := fun pp hp hc => hnoev ⟨pp, hp, hc⟩
  have hs : 0 < s := by
    obtain ⟨⟨y, hyP, -⟩, -⟩ := hslabCuts
    have h1 : Submission.boxNorm c σ y < s := (Submission.mem_PBox_iff s c σ y).mp hyP
    have h2 : 0 ≤ Submission.boxNorm c σ y := Submission.boxNorm_nonneg c σ y
    linarith
  have hl : lam0 < lam1 := hT.2.2.2.2.2.2.2.2.2.1
  refine Work.Drive.Mono.traceLocallyEuclidean_of_junctionGenC hs hslice hfaceReg
    (tiltData_erase_of_no_event hT hnoev') (junctionGenC_erase_of_no_event hs hJ hl hΓ hEF hnoev')
    hlam ?_
  intro hc
  exact (Finset.mem_erase.mp (Finset.mem_coe.mp hc)).1 rfl

end

end Work.Drive.Mono
