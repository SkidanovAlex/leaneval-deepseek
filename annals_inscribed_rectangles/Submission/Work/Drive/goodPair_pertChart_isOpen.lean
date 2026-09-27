import Mathlib
import Submission.Work.Drive.sideGermDefs
import Submission.Work.Drive.sgSweepDefs
import Submission.Work.Drive.sgAssembly
import Submission.Work.Drive.CntAt_locallyConstant
import Submission.Work.Drive.sideGerm_parity_local
import Submission.Work.Drive.parityFamDefs
import Submission.Work.Drive.meetBoxEngine
import Submission.Work.Drive.geometricLocality
import Submission.Work.Drive.continuousAt_partial_fderiv
import Submission.Work.Drive.range_sup_eq_top_of_chartedDiff_surjective_real

/-!
# The good configurations of the germ route form an open set

The germ value `Work.Drive.sideGerm Ξ Q c w` is defined from the configurations `t` at which the
perturbed pair `(Ξ t.1 ∘ Q, rotCapping w ∘ Ξ t.2 ∘ Q)` is a `GoodPair` (finite meet set, every meet
interior in the box, transverse there).  This module proves that this set of configurations is
**open** in the two chart-perturbation parameters:

> `Work.Drive.goodPair_pertChart_isOpen` — `{p | GoodAt Ξ Q c w p}` is open.

The mathematics is the stability of the meet set of a loop against a `3`-chain under a small
perturbation of the two curves: the meets near a good configuration are exactly the images of the base
meets under the implicit-function branches, so their number is the same (the counting engine
`Work.Drive.eventually_ncard_meetBox_eq_manifold`), they stay strictly inside the box (the compactness
cover `Work.Drive.eventually_meetBox_cover_par_diag` with balls inside the open box), and they stay
transverse (the charted derivative of the difference system is surjective at the base meet and remains
surjective nearby, because the partial derivative in the box variable is *continuous* in the family
parameter — `Work.Drive.continuousAt_partial_fderiv` — and surjectivity of linear maps is open, while
the intrinsic transversality is equivalent to the surjectivity of the charted derivative —
`Work.Drive.range_sup_eq_top_of_chartedDiff_surjective_real`).

The transport to the design's `GoodAt` is through the family `Work.Drive.parityLoopFam` /
`Work.Drive.parityChainFam` of the germ route, whose meet set **is** `coreMeet` of the perturbed pair
(`Work.Drive.meetBox_parityFam`, definitional).
-/

namespace Work.Drive

open Manifold Filter Set
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

noncomputable section

variable {m : ℕ}

/-! ## The smoothness of the perturbed charts -/

/-- The perturbed chart of a smooth chart by a chart perturbation is smooth. -/
lemma contMDiff_pertChart (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (hΞ : ChartPert Q m Ξ) (hQ : IsSmoothChart Q)
    (t : EuclideanSpace ℝ (Fin m)) :
    ContMDiff (𝓘(ℝ, ℂ)) (𝓡 4) Ctop (pertChart Ξ Q t) := by
  have h : ContMDiff (𝓘(ℝ, ℂ)) ((𝓡 m).prod (𝓡 4)) Ctop
      (fun z : ℂ => (t, Q z)) :=
    (contMDiff_const (c := t) (I := 𝓘(ℝ, ℂ)) (I' := 𝓡 m)).prodMk hQ
  exact hΞ.2.1.comp h

/-- The rotation of the perturbed chart is smooth. -/
lemma contMDiff_rot_pertChart (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (w : UnitAddCircle) (hΞ : ChartPert Q m Ξ) (hQ : IsSmoothChart Q)
    (t : EuclideanSpace ℝ (Fin m)) :
    ContMDiff (𝓘(ℝ, ℂ)) (𝓡 4) Ctop
      (fun p : ℂ => rotCapping w (pertChart Ξ Q t p)) :=
  (contMDiff_rotCappingAngle w).comp (contMDiff_pertChart Ξ Q hΞ hQ t)

/-! ## Joint smoothness of the loop and chain families along the perturbation parameter -/

/-- **The loop family is jointly `C^∞`** (the `IsSmoothChart` form of
`Work.Drive.parityLoopFam_contMDiff`). -/
theorem gpLoop_contMDiff (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (hΞ : ChartPert Q m Ξ) (hQ : IsSmoothChart Q)
    (A : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) :
    ContMDiff (𝓘(ℝ, (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) × ℝ)) (𝓡 4) Ctop
      (fun q : (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) × ℝ =>
        parityLoopFam Ξ Q A q.1 q.2) := by
  have hpt : ContMDiff (𝓘(ℝ, (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) × ℝ))
      (𝓘(ℝ, ℂ)) Ctop
      (fun q : (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) × ℝ =>
        Complex.exp ((Real.pi : ℂ) * ((q.2 : ℝ) : ℂ) * Complex.I)) := by
    have h2 : ContDiff ℝ Ctop
        (fun q : (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) × ℝ => ((q.2 : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (by fun_prop)
    have hlin : ContDiff ℝ Ctop
        (fun q : (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) × ℝ =>
          (Real.pi : ℂ) * ((q.2 : ℝ) : ℂ) * Complex.I) :=
      (contDiff_const.mul h2).mul contDiff_const
    exact contMDiff_iff_contDiff.mpr (Complex.contDiff_exp.comp hlin)
  have hQ5 : ContMDiff (𝓘(ℝ, (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) × ℝ))
      (𝓡 4) Ctop
      (fun q : (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) × ℝ =>
        Q (Complex.exp ((Real.pi : ℂ) * ((q.2 : ℝ) : ℂ) * Complex.I))) :=
    hQ.comp hpt
  have hfst : ContMDiff (𝓘(ℝ, (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) × ℝ))
      (𝓡 m) Ctop
      (fun q : (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) × ℝ => A.1 + q.1.1) :=
    contMDiff_iff_contDiff.mpr (by fun_prop)
  have hmain := hΞ.2.1.comp (hfst.prodMk hQ5)
  refine hmain.congr fun q => ?_
  simp only [Function.comp_def, coreLoop, pertChart, parityLoopFam]

/-- **The plane-presentation family is jointly `C^∞`** (the `IsSmoothChart` form of
`Work.Drive.contMDiff_rotPresentation_pertChart`). -/
lemma gpRotPresentation_contMDiff
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (w : UnitAddCircle)
    (hΞ : ChartPert Q m Ξ) (hQ : IsSmoothChart Q)
    (A : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) :
    ContMDiff (𝓘(ℝ, (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) ×
        EuclideanSpace ℝ (Fin 2))) (𝓡 4) Ctop
      (fun q : (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) × EuclideanSpace ℝ (Fin 2) =>
        rotPresentation (pertChart Ξ Q (A.2 + q.1.2)) w q.2) := by
  have hinner : ContMDiff
      (𝓘(ℝ, (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) × EuclideanSpace ℝ (Fin 2)))
      (𝓡 4) Ctop
      (fun q : (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) × EuclideanSpace ℝ (Fin 2) =>
        Ξ (A.2 + q.1.2) (diskPlane Q q.2)) := by
    have h1 : ContMDiff
        (𝓘(ℝ, (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) × EuclideanSpace ℝ (Fin 2)))
        (𝓡 m) Ctop
        (fun q : (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) × EuclideanSpace ℝ (Fin 2) =>
          A.2 + q.1.2) :=
      contMDiff_iff_contDiff.mpr (by fun_prop)
    have hdp : ContMDiff (𝓡 2) (𝓡 4) Ctop (diskPlane Q) := contMDiff_diskPlane hQ
    have h2 : ContMDiff
        (𝓘(ℝ, (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) × EuclideanSpace ℝ (Fin 2)))
        (𝓡 4) Ctop
        (fun q : (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) × EuclideanSpace ℝ (Fin 2) =>
          diskPlane Q q.2) :=
      hdp.comp (contMDiff_iff_contDiff.mpr (by fun_prop))
    exact hΞ.2.1.comp (h1.prodMk h2)
  have hrot := contMDiff_rotCappingAngle w
  refine (hrot.comp hinner).congr fun q => ?_
  simp only [Function.comp_def, rotPresentation, diskPlane, pertChart, Function.comp_apply]

/-- **The chain family is jointly `C^∞`** (the `IsSmoothChart` form of
`Work.Drive.parityChainFam_contMDiff`). -/
theorem gpChain_contMDiff
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (c : ℝ) (w : UnitAddCircle)
    (hΞ : ChartPert Q m Ξ) (hQ : IsSmoothChart Q)
    (A : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) :
    ContMDiff
      (𝓘(ℝ, (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) × EuclideanSpace ℝ (Fin 3)))
      (𝓡 4) Ctop
      (fun q : (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) × EuclideanSpace ℝ (Fin 3) =>
        parityChainFam Ξ Q c w A q.1 q.2) := by
  have hPp := gpRotPresentation_contMDiff Ξ Q w hΞ hQ A
  have hmain := contMDiff_clampedSweep_family_gen
    (P := EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
    c (fun s : ℝ => 1 - s) (by fun_prop)
    (fun u (y : EuclideanSpace ℝ (Fin 2)) => rotPresentation (pertChart Ξ Q (A.2 + u.2)) w y) hPp
  simpa only [parityChainFam] using hmain

/-! ## A radius inside the open box -/

/-- A radius in which both coordinates of the box stay *strictly* inside, from the strict interiority
of a point (the open-box form of `Work.Drive.exists_box_radius`). -/
theorem exists_openBox_radius (ξ : ℝ × EuclideanSpace ℝ (Fin 3))
    (h1 : ξ.1 ∈ Set.Ioo (0 : ℝ) 1) (h2 : ∀ i : Fin 3, ξ.2 i ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ r : ℝ, 0 < r ∧ ∀ x : ℝ × EuclideanSpace ℝ (Fin 3), ‖x - ξ‖ < r →
      x.1 ∈ Set.Ioo (0 : ℝ) 1 ∧ ∀ i : Fin 3, x.2 i ∈ Set.Ioo (0 : ℝ) 1 := by
  set S : Finset ℝ := {ξ.1, 1 - ξ.1, ξ.2 0, 1 - ξ.2 0, ξ.2 1, 1 - ξ.2 1, ξ.2 2, 1 - ξ.2 2}
    with hSdef
  have hmem : ∀ y ∈ S, 0 < y := by
    intro y hy
    rw [hSdef] at hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact h1.1
    · linarith [h1.2]
    · exact (h2 0).1
    · linarith [(h2 0).2]
    · exact (h2 1).1
    · linarith [(h2 1).2]
    · exact (h2 2).1
    · linarith [(h2 2).2]
  have hne : S.Nonempty := ⟨ξ.1, by rw [hSdef]; simp⟩
  set mm : ℝ := S.min' hne with hmdef
  have hmpos : 0 < mm := by
    rw [hmdef]
    exact hmem _ (Finset.min'_mem S hne)
  have hle : ∀ y ∈ S, mm ≤ y := fun y hy => by
    rw [hmdef]; exact Finset.min'_le S y hy
  have hhalf : mm / 2 ≤ mm := by linarith
  refine ⟨mm / 2, by linarith, ?_⟩
  intro x hx
  have hfst : |x.1 - ξ.1| ≤ ‖x - ξ‖ := by simpa using norm_fst_le (x - ξ)
  have hsnd : ‖x.2 - ξ.2‖ ≤ ‖x - ξ‖ := by simpa using norm_snd_le (x - ξ)
  have hb1 : |x.1 - ξ.1| < mm / 2 := lt_of_le_of_lt hfst hx
  have hb1' := abs_lt.mp hb1
  have h1m : mm ≤ ξ.1 := hle ξ.1 (by rw [hSdef]; simp)
  have h2m : mm ≤ 1 - ξ.1 := hle (1 - ξ.1) (by rw [hSdef]; simp)
  refine ⟨⟨by linarith [hb1'.1, h1m, hhalf], by linarith [hb1'.2, h2m, hhalf]⟩, ?_⟩
  intro i
  have hcoord : |x.2 i - ξ.2 i| ≤ ‖x.2 - ξ.2‖ := by
    simpa using PiLp.norm_apply_le (p := 2) (x.2 - ξ.2) i
  have hbi : |x.2 i - ξ.2 i| < mm / 2 := lt_of_le_of_lt (le_trans hcoord hsnd) hx
  have hbi' := abs_lt.mp hbi
  have h3m : mm ≤ ξ.2 i := by
    fin_cases i
    · exact hle (ξ.2 0) (by rw [hSdef]; simp)
    · exact hle (ξ.2 1) (by rw [hSdef]; simp)
    · exact hle (ξ.2 2) (by rw [hSdef]; simp)
  have h4m : mm ≤ 1 - ξ.2 i := by
    fin_cases i
    · exact hle (1 - ξ.2 0) (by rw [hSdef]; simp)
    · exact hle (1 - ξ.2 1) (by rw [hSdef]; simp)
    · exact hle (1 - ξ.2 2) (by rw [hSdef]; simp)
  exact ⟨by linarith [hbi'.1, h3m, hhalf], by linarith [hbi'.2, h4m, hhalf]⟩

/-! ## The chart region of the family, and the smoothness of the charted system -/

/-- The chart region of the loop/chain family: the pairs of parameters at which both values lie in the
source of the chart `chr c`. -/
def famChartRegion {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (c : CappingSpace) (L : P → ℝ → CappingSpace) (D : P → EuclideanSpace ℝ (Fin 3) → CappingSpace) :
    Set (P × (ℝ × EuclideanSpace ℝ (Fin 3))) :=
  {q | L q.1 q.2.1 ∈ (chr c).source ∧ D q.1 q.2.2 ∈ (chr c).source}

@[simp] lemma mem_famChartRegion {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {c : CappingSpace} {L : P → ℝ → CappingSpace}
    {D : P → EuclideanSpace ℝ (Fin 3) → CappingSpace}
    {q : P × (ℝ × EuclideanSpace ℝ (Fin 3))} :
    q ∈ famChartRegion c L D ↔
      L q.1 q.2.1 ∈ (chr c).source ∧ D q.1 q.2.2 ∈ (chr c).source := Iff.rfl

theorem isOpen_famChartRegion {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (c : CappingSpace) (L : P → ℝ → CappingSpace) (D : P → EuclideanSpace ℝ (Fin 3) → CappingSpace)
    (hL : Continuous fun q : P × ℝ => L q.1 q.2)
    (hD : Continuous fun q : P × EuclideanSpace ℝ (Fin 3) => D q.1 q.2) :
    IsOpen (famChartRegion c L D) := by
  have hpairL : Continuous (fun q : P × (ℝ × EuclideanSpace ℝ (Fin 3)) => (q.1, q.2.1)) := by
    fun_prop
  have hpairD : Continuous (fun q : P × (ℝ × EuclideanSpace ℝ (Fin 3)) => (q.1, q.2.2)) := by
    fun_prop
  have h1 : IsOpen {q : P × (ℝ × EuclideanSpace ℝ (Fin 3)) | L q.1 q.2.1 ∈ (chr c).source} :=
    (chr c).open_source.preimage (hL.comp hpairL)
  have h2 : IsOpen {q : P × (ℝ × EuclideanSpace ℝ (Fin 3)) | D q.1 q.2.2 ∈ (chr c).source} :=
    (chr c).open_source.preimage (hD.comp hpairD)
  exact h1.inter h2

/-- **The charted difference system of the loop/chain family is smooth on the chart region.** -/
theorem contDiffOn_famChartDiff {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (c : CappingSpace) (L : P → ℝ → CappingSpace)
    (D : P → EuclideanSpace ℝ (Fin 3) → CappingSpace)
    (hL : ContMDiff (𝓘(ℝ, P × ℝ)) (𝓡 4) Ctop (fun q : P × ℝ => L q.1 q.2))
    (hD : ContMDiff (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 3))) (𝓡 4) Ctop
      (fun q : P × EuclideanSpace ℝ (Fin 3) => D q.1 q.2)) :
    ContDiffOn ℝ Ctop
      (fun q : P × (ℝ × EuclideanSpace ℝ (Fin 3)) => chr c (L q.1 q.2.1) - chr c (D q.1 q.2.2))
      (famChartRegion c L D) := by
  have hpairL : ContMDiff (𝓘(ℝ, P × (ℝ × EuclideanSpace ℝ (Fin 3)))) (𝓘(ℝ, P × ℝ)) Ctop
      (fun q : P × (ℝ × EuclideanSpace ℝ (Fin 3)) => (q.1, q.2.1)) :=
    contMDiff_iff_contDiff.mpr (by fun_prop)
  have hpairD : ContMDiff (𝓘(ℝ, P × (ℝ × EuclideanSpace ℝ (Fin 3))))
      (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 3))) Ctop
      (fun q : P × (ℝ × EuclideanSpace ℝ (Fin 3)) => (q.1, q.2.2)) :=
    contMDiff_iff_contDiff.mpr (by fun_prop)
  have hLglob : ContMDiff (𝓘(ℝ, P × (ℝ × EuclideanSpace ℝ (Fin 3)))) (𝓡 4) Ctop
      (fun q : P × (ℝ × EuclideanSpace ℝ (Fin 3)) => L q.1 q.2.1) := hL.comp hpairL
  have hDglob : ContMDiff (𝓘(ℝ, P × (ℝ × EuclideanSpace ℝ (Fin 3)))) (𝓡 4) Ctop
      (fun q : P × (ℝ × EuclideanSpace ℝ (Fin 3)) => D q.1 q.2.2) := hD.comp hpairD
  have hA : ContMDiffOn (𝓘(ℝ, P × (ℝ × EuclideanSpace ℝ (Fin 3)))) (𝓡 4) Ctop
      (fun q : P × (ℝ × EuclideanSpace ℝ (Fin 3)) => chr c (L q.1 q.2.1))
      (famChartRegion c L D) :=
    (contMDiffOn_chr c).comp hLglob.contMDiffOn (fun q hq => hq.1)
  have hB : ContMDiffOn (𝓘(ℝ, P × (ℝ × EuclideanSpace ℝ (Fin 3)))) (𝓡 4) Ctop
      (fun q : P × (ℝ × EuclideanSpace ℝ (Fin 3)) => chr c (D q.1 q.2.2))
      (famChartRegion c L D) :=
    (contMDiffOn_chr c).comp hDglob.contMDiffOn (fun q hq => hq.2)
  have hsub : ContMDiffOn (𝓘(ℝ, P × (ℝ × EuclideanSpace ℝ (Fin 3)))) (𝓡 4) Ctop
      (fun q : P × (ℝ × EuclideanSpace ℝ (Fin 3)) => chr c (L q.1 q.2.1) - chr c (D q.1 q.2.2))
      (famChartRegion c L D) := hA.sub hB
  exact contMDiffOn_iff_contDiffOn.mp (by simpa only [Pi.sub_apply] using hsub)

/-! ## Insert a constant into a family parameter -/

lemma contMDiff_const_param {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] (u : P) :
    ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, P × ℝ)) Ctop (fun q : ℝ => (u, q)) :=
  contMDiff_iff_contDiff.mpr (by fun_prop)

lemma contMDiff_const_param3 {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] (u : P) :
    ContMDiff (𝓡 3) (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 3))) Ctop
      (fun q : EuclideanSpace ℝ (Fin 3) => (u, q)) :=
  contMDiff_iff_contDiff.mpr (by fun_prop)

lemma contMDiff_const_param23 {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] (u : P) :
    ContMDiff (𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 3))) (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 3))) Ctop
      (fun q : ℝ × EuclideanSpace ℝ (Fin 3) => (u, q.2)) :=
  contMDiff_iff_contDiff.mpr (by fun_prop)

/-! ## Transversality is stable under a small perturbation of the parameter -/

/-- **The charted surjectivity at a base meet persists in a neighbourhood of the base parameter.**
For a base meet `ξ` at which the pair `(L 0, D 0)` is transverse, there is a radius `θ` such that for
`‖u‖ < θ` and `z` within `θ` of `ξ.1` the charted difference system of the pair `(L u, D u)` (in the
chart centred at the base meet's value `L 0 ξ.1.1`) is smooth and surjective at `z`. -/
lemma exists_transverse_radius {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (L : P → ℝ → CappingSpace) (D : P → EuclideanSpace ℝ (Fin 3) → CappingSpace)
    (hL : ContMDiff (𝓘(ℝ, P × ℝ)) (𝓡 4) Ctop (fun q : P × ℝ => L q.1 q.2))
    (hD : ContMDiff (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 3))) (𝓡 4) Ctop
      (fun q : P × EuclideanSpace ℝ (Fin 3) => D q.1 q.2))
    (ξ : ↥(meetBox (L 0) (D 0)))
    (htrans : LinearMap.range (mfderiv (𝓘(ℝ, ℝ)) (𝓡 4) (L 0) ξ.1.1).toLinearMap ⊔
      LinearMap.range (mfderiv (𝓡 3) (𝓡 4) (D 0) ξ.1.2).toLinearMap = ⊤) :
    ∃ θ : ℝ, 0 < θ ∧
      ∀ (u : P) (z : ℝ × EuclideanSpace ℝ (Fin 3)),
        ‖u‖ < θ → ‖z - ξ.1‖ < θ →
          ((L u z.1 ∈ (chr (L 0 ξ.1.1)).source ∧ D u z.2 ∈ (chr (L 0 ξ.1.1)).source) ∧
            Function.Surjective (fderiv ℝ (fun z' : ℝ × EuclideanSpace ℝ (Fin 3) =>
              chr (L 0 ξ.1.1) (L u z'.1) - chr (L 0 ξ.1.1) (D u z'.2)) z)) := by
  classical
  have heq : L 0 ξ.1.1 = D 0 ξ.1.2 := ξ.2.2.2
  have hq0 : (((0 : P), ξ.1) : P × (ℝ × EuclideanSpace ℝ (Fin 3)))
      ∈ famChartRegion (L 0 ξ.1.1) L D :=
    ⟨mem_chart_source _ _, by rw [← heq]; exact mem_chart_source _ _⟩
  have hU : IsOpen (famChartRegion (L 0 ξ.1.1) L D) :=
    isOpen_famChartRegion _ L D hL.continuous hD.continuous
  have hGon := contDiffOn_famChartDiff (L 0 ξ.1.1) L D hL hD
  -- the partial derivative of the charted system is continuous at the base point
  have hcont : ContinuousAt (fun q : P × (ℝ × EuclideanSpace ℝ (Fin 3)) =>
      fderiv ℝ (fun z' : ℝ × EuclideanSpace ℝ (Fin 3) =>
        chr (L 0 ξ.1.1) (L q.1 z'.1) - chr (L 0 ξ.1.1) (D q.1 z'.2)) q.2) ((0 : P), ξ.1) :=
    continuousAt_partial_fderiv hU
      (fun q : P × (ℝ × EuclideanSpace ℝ (Fin 3)) =>
        chr (L 0 ξ.1.1) (L q.1 q.2.1) - chr (L 0 ξ.1.1) (D q.1 q.2.2)) hGon hq0
  -- surjectivity at the base meet
  have hL0 : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 4) Ctop (L 0) := hL.comp (contMDiff_const_param 0)
  have hD0 : ContMDiff (𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 3))) (𝓡 4) Ctop
      (fun q : ℝ × EuclideanSpace ℝ (Fin 3) => D 0 q.2) :=
    hD.comp (contMDiff_const_param23 0)
  have hbase : Function.Surjective
      (fderiv ℝ (fun z' : ℝ × EuclideanSpace ℝ (Fin 3) =>
        chr (L 0 ξ.1.1) (L 0 z'.1) - chr (L 0 ξ.1.1) (D 0 z'.2)) ξ.1) :=
    chartedDiff_surjective_of_transverse (L 0) (fun _ : ℝ => D 0) hL0 hD0 heq htrans
  have hopen := isOpen_setOf_surjective_clm (E := ℝ × EuclideanSpace ℝ (Fin 3))
    (F := EuclideanSpace ℝ (Fin 4))
  have hnb : {q : P × (ℝ × EuclideanSpace ℝ (Fin 3)) |
      Function.Surjective (fderiv ℝ (fun z' : ℝ × EuclideanSpace ℝ (Fin 3) =>
        chr (L 0 ξ.1.1) (L q.1 z'.1) - chr (L 0 ξ.1.1) (D q.1 z'.2)) q.2)} ∈ 𝓝 ((0 : P), ξ.1) :=
    hcont.preimage_mem_nhds (hopen.mem_nhds hbase)
  have hboth : famChartRegion (L 0 ξ.1.1) L D ∩
      {q : P × (ℝ × EuclideanSpace ℝ (Fin 3)) |
        Function.Surjective (fderiv ℝ (fun z' : ℝ × EuclideanSpace ℝ (Fin 3) =>
          chr (L 0 ξ.1.1) (L q.1 z'.1) - chr (L 0 ξ.1.1) (D q.1 z'.2)) q.2)} ∈
      𝓝 ((0 : P), ξ.1) :=
    Filter.inter_mem (hU.mem_nhds hq0) hnb
  obtain ⟨θ, hθ, hθsub⟩ := Metric.mem_nhds_iff.mp hboth
  refine ⟨θ, hθ, ?_⟩
  intro u z hu hz
  have hmem : (((u, z)) : P × (ℝ × EuclideanSpace ℝ (Fin 3))) ∈
      famChartRegion (L 0 ξ.1.1) L D ∩
      {q : P × (ℝ × EuclideanSpace ℝ (Fin 3)) |
        Function.Surjective (fderiv ℝ (fun z' : ℝ × EuclideanSpace ℝ (Fin 3) =>
          chr (L 0 ξ.1.1) (L q.1 z'.1) - chr (L 0 ξ.1.1) (D q.1 z'.2)) q.2)} := by
    refine hθsub ?_
    rw [Metric.mem_ball, Prod.dist_eq, dist_zero_right, dist_eq_norm]
    exact max_lt hu hz
  exact ⟨hmem.1, hmem.2⟩

/-! ## The eventual goodness of the meet set under a good base configuration -/

/-- **Goodness of the loop/chain meet set is a neighbourhood property**: if at the base parameter the
meet set is finite, strictly interior in the box, and transverse, then for nearby parameters the meet
set is finite, strictly interior, and transverse. -/
theorem eventually_good_meetBox {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P]
    (L : P → ℝ → CappingSpace) (D : P → EuclideanSpace ℝ (Fin 3) → CappingSpace)
    (hL : ContMDiff (𝓘(ℝ, P × ℝ)) (𝓡 4) Ctop (fun q : P × ℝ => L q.1 q.2))
    (hD : ContMDiff (𝓘(ℝ, P × EuclideanSpace ℝ (Fin 3))) (𝓡 4) Ctop
      (fun q : P × EuclideanSpace ℝ (Fin 3) => D q.1 q.2))
    (hfin : (meetBox (L 0) (D 0)).Finite)
    (hint : ∀ p ∈ meetBox (L 0) (D 0), p.1 ∈ Set.Ioo (0 : ℝ) 1 ∧
      ∀ i : Fin 3, p.2 i ∈ Set.Ioo (0 : ℝ) 1)
    (htrans : ∀ p ∈ meetBox (L 0) (D 0),
      LinearMap.range (mfderiv (𝓘(ℝ, ℝ)) (𝓡 4) (L 0) p.1).toLinearMap ⊔
        LinearMap.range (mfderiv (𝓡 3) (𝓡 4) (D 0) p.2).toLinearMap = ⊤) :
    ∀ᶠ u in 𝓝 (0 : P),
      (meetBox (L u) (D u)).Finite ∧
      (∀ p ∈ meetBox (L u) (D u), p.1 ∈ Set.Ioo (0 : ℝ) 1 ∧
        ∀ i : Fin 3, p.2 i ∈ Set.Ioo (0 : ℝ) 1) ∧
      (∀ p ∈ meetBox (L u) (D u),
        LinearMap.range (mfderiv (𝓘(ℝ, ℝ)) (𝓡 4) (L u) p.1).toLinearMap ⊔
          LinearMap.range (mfderiv (𝓡 3) (𝓡 4) (D u) p.2).toLinearMap = ⊤) := by
  classical
  have hpairL : Continuous (fun q : P × (ℝ × EuclideanSpace ℝ (Fin 3)) => (q.1, q.2.1)) := by
    fun_prop
  have hpairD : Continuous (fun q : P × (ℝ × EuclideanSpace ℝ (Fin 3)) => (q.1, q.2.2)) := by
    fun_prop
  have hcont : Continuous (fun q : P × (ℝ × EuclideanSpace ℝ (Fin 3)) =>
      (L q.1 q.2.1, D q.1 q.2.2)) :=
    (hL.continuous.comp hpairL).prodMk (hD.continuous.comp hpairD)
  -- ## strict interiority
  have hInt : ∀ᶠ u in 𝓝 (0 : P), ∀ p ∈ meetBox (L u) (D u),
      p.1 ∈ Set.Ioo (0 : ℝ) 1 ∧ ∀ i : Fin 3, p.2 i ∈ Set.Ioo (0 : ℝ) 1 := by
    by_cases hne : (meetBox (L 0) (D 0)).Nonempty
    · choose rf hrfpos hrf using fun ξ : ↥(meetBox (L 0) (D 0)) =>
        exists_openBox_radius ξ.1 (hint ξ.1 ξ.2).1 (hint ξ.1 ξ.2).2
      have hcov := eventually_meetBox_cover_par_diag hcont (δ := rf) hrfpos
      filter_upwards [hcov] with u hu p hp
      obtain ⟨ξ, hξ⟩ := hu p hp
      exact hrf ξ p hξ
    · have hcov := eventually_meetBox_cover_par_diag hcont (δ := fun _ => (1 : ℝ))
          (fun _ => one_pos)
      filter_upwards [hcov] with u hu p hp
      obtain ⟨ξ, -⟩ := hu p hp
      exact absurd ⟨ξ.1, ξ.2⟩ hne
  -- ## finiteness
  have hFin : ∀ᶠ u in 𝓝 (0 : P), (meetBox (L u) (D u)).Finite := by
    by_cases hne : (meetBox (L 0) (D 0)).Nonempty
    · have hNpos : 0 < (meetBox (L 0) (D 0)).ncard := Set.Nonempty.ncard_pos hfin hne
      have hNne : (meetBox (L 0) (D 0)).ncard ≠ 0 := hNpos.ne'
      have hEv := eventually_ncard_meetBox_eq_manifold L D hL hD hfin hint htrans
      filter_upwards [hEv] with u hu
      by_contra hcon
      have h0 : (meetBox (L u) (D u)).ncard = 0 := Set.Infinite.ncard hcon
      rw [hu] at h0
      exact hNne h0
    · have hcov := eventually_meetBox_cover_par_diag hcont (δ := fun _ => (1 : ℝ))
          (fun _ => one_pos)
      filter_upwards [hcov] with u hu
      refine Set.finite_empty.subset ?_
      intro p hp
      obtain ⟨ξ, -⟩ := hu p hp
      exact absurd ⟨ξ.1, ξ.2⟩ hne
  -- ## transversality
  have hTR : ∀ᶠ u in 𝓝 (0 : P), ∀ p ∈ meetBox (L u) (D u),
      LinearMap.range (mfderiv (𝓘(ℝ, ℝ)) (𝓡 4) (L u) p.1).toLinearMap ⊔
        LinearMap.range (mfderiv (𝓡 3) (𝓡 4) (D u) p.2).toLinearMap = ⊤ := by
    haveI : Fintype ↥(meetBox (L 0) (D 0)) := hfin.fintype
    choose θ hθpos hθ using fun ξ : ↥(meetBox (L 0) (D 0)) =>
      exists_transverse_radius L D hL hD ξ (htrans ξ.1 ξ.2)
    choose rf hrfpos hrf using fun ξ : ↥(meetBox (L 0) (D 0)) =>
      exists_openBox_radius ξ.1 (hint ξ.1 ξ.2).1 (hint ξ.1 ξ.2).2
    have hsmall : ∀ᶠ u in 𝓝 (0 : P), ∀ ξ : ↥(meetBox (L 0) (D 0)), ‖u‖ < θ ξ := by
      rw [Filter.eventually_all]
      intro ξ
      filter_upwards [Metric.ball_mem_nhds (0 : P) (hθpos ξ)] with u hu
      rwa [Metric.mem_ball, dist_zero_right] at hu
    have hcov := eventually_meetBox_cover_par_diag hcont
      (δ := fun ξ => min (θ ξ) (rf ξ)) (fun ξ => lt_min (hθpos ξ) (hrfpos ξ))
    filter_upwards [hsmall, hcov] with u hu1 hu2 p hp
    obtain ⟨ξ, hξ⟩ := hu2 p hp
    have hξθ : ‖p - ξ.1‖ < θ ξ := lt_of_lt_of_le hξ (min_le_left _ _)
    obtain ⟨⟨hsrcL, hsrcD⟩, hsurj⟩ := hθ ξ u p (hu1 ξ) hξθ
    have hmeet : L u p.1 = D u p.2 := (mem_meetBox.mp hp).2.2
    have hLu : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 4) Ctop (L u) := hL.comp (contMDiff_const_param u)
    have hDu : ContMDiff (𝓡 3) (𝓡 4) Ctop (D u) := hD.comp (contMDiff_const_param3 u)
    exact range_sup_eq_top_of_chartedDiff_surjective_real (L 0 ξ.1.1) (L u) (D u)
      hLu hDu hsrcL hsrcD hmeet hsurj
  exact hFin.and (hInt.and hTR)

/-! ## The target: the good configurations form an open set -/

theorem goodPair_pertChart_isOpen {Ξ : EuclideanSpace ℝ (Fin 4) → Work.Drive.CappingSpace → Work.Drive.CappingSpace}
    {Q : ℂ → Work.Drive.CappingSpace}
    (hΞ : Work.Drive.ChartPert Q 4 Ξ) (hQ : Work.Drive.IsSmoothChart Q) (c : ℝ) (w : UnitAddCircle) :
    IsOpen {p : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4) |
      Work.Drive.GoodAt Ξ Q c w p} := by
  rw [isOpen_iff_mem_nhds]
  intro A hA
  -- the base data, at the parameter `A = A + 0` of the family
  have hA0 : GoodAt Ξ Q c w (A + 0) := by simpa using hA
  obtain ⟨-, -, hfin, hint, htrans⟩ := hA0
  -- the family and the engine
  have hL := gpLoop_contMDiff Ξ Q hΞ hQ A
  have hD := gpChain_contMDiff Ξ Q c w hΞ hQ A
  have hEv := eventually_good_meetBox (parityLoopFam Ξ Q A) (parityChainFam Ξ Q c w A)
    hL hD hfin hint htrans
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.mem_nhds_iff.mp hEv
  refine Filter.mem_of_superset (Metric.ball_mem_nhds A hρ) ?_
  intro A' hA'ball
  have hu : ‖A' - A‖ < ρ := by
    rw [Metric.mem_ball, dist_eq_norm] at hA'ball
    exact hA'ball
  set u : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4) := A' - A with hudef
  have hAsum : A + u = A' := by rw [hudef]; abel
  have hsum1 : A.1 + u.1 = A'.1 := congrArg Prod.fst hAsum
  have hsum2 : A.2 + u.2 = A'.2 := congrArg Prod.snd hAsum
  -- the transported identification of the two families
  have hloopfun : parityLoopFam Ξ Q A u = coreLoop (pertChart Ξ Q A'.1) := by
    funext t
    simp only [parityLoopFam_apply]
    rw [hsum1]
  have hchainfun : parityChainFam Ξ Q c w A u
      = clampedSweep c (fun t => 1 - t)
          (diskPlane (fun p => rotCapping w (pertChart Ξ Q A'.2 p))) := by
    funext x
    simp only [parityChainFam_apply, rotPresentation]
    rw [hsum2]
  have hmeetEq : meetBox (parityLoopFam Ξ Q A u) (parityChainFam Ξ Q c w A u)
      = coreMeet (pertChart Ξ Q A'.1) c
          (diskPlane (fun p => rotCapping w (pertChart Ξ Q A'.2 p))) := by
    rw [meetBox_parityFam Ξ Q c w A u, hAsum]
    rfl
  have hgood := hρsub (by rw [Metric.mem_ball, dist_eq_norm, sub_zero]; exact hu)
  simp only [Set.mem_ofPred_eq] at hgood
  rw [hmeetEq] at hgood
  rw [hloopfun] at hgood
  rw [hchainfun] at hgood
  exact ⟨contMDiff_pertChart Ξ Q hΞ hQ A'.1, contMDiff_rot_pertChart Ξ Q w hΞ hQ A'.2,
    hgood.1, hgood.2.1, hgood.2.2⟩

end

end Work.Drive
