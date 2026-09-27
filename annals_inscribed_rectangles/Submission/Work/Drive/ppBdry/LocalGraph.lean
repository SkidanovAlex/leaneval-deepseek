import Mathlib
import Submission.Work.Drive.ppBdry.Basic
import Submission.Work.Drive.exists_local_normalForm
import Submission.Work.Drive.ManifoldParity.exists_chartDiff_extension
import Submission.Work.ManifoldParity.Defs
import Submission.Work.Drive.ManifoldParity.InterSetFlowDefs
import Submission.Work.Drive.interior_unitBox

/-!
# The local graph structure of the pair-meet set

`Work.Drive.PPRegAt E E' V W x` gives, at a meet `x`, the surjectivity of the derivative of the
charted pair map taken at the *meet-value charts* `(q, q') = (E x, E' x)`.  Since that map is smooth
on a neighbourhood of `x` (the chart sources are open) and its zero set there is exactly the meet
set, the implicit function theorem (`Work.Drive.exists_local_normalForm`) exhibits the meet set
near `x` as the graph of a smooth map over a coordinate axis.  This is
`Work.ManifoldParity.HasLocalGraphCharts (ppMeet E E' V W)`.
-/

namespace Work.Drive
namespace PPB

open scoped Manifold ContDiff Topology
open Manifold Set

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [IsManifold (𝓡 4) Ctop M]

/-! ## The chart region of the meet-value chart pair -/

/-- At a meet, all four values lie in the sources of the two meet-value charts. -/
lemma mem_ppRegion_self {E E' : ℝ → EuclideanSpace ℝ (Fin 2) → M}
    {V W : EuclideanSpace ℝ (Fin 3) → M} {x : EuclideanSpace ℝ (Fin 9)}
    (hx : x ∈ ppMeet E E' V W) :
    x ∈ ppRegion (E (ftS x) (ftU x)) (E' (ftS x) (ftU x)) E E' V W := by
  obtain ⟨-, h1, h2⟩ := hx
  refine ⟨mem_chart_source _ _, ?_, mem_chart_source _ _, ?_⟩
  · rw [h1]; exact mem_chart_source _ _
  · rw [h2]; exact mem_chart_source _ _

/-- The chart region of the meet-value chart pair is open. -/
lemma isOpen_ppRegion (p p' : M) (E E' : ℝ → EuclideanSpace ℝ (Fin 2) → M)
    (V W : EuclideanSpace ℝ (Fin 3) → M)
    (hEc : Continuous (pE E)) (hE'c : Continuous (pE E')) (hVc : Continuous (pV V))
    (hWc : Continuous (pW W)) :
    IsOpen (ppRegion p p' E E' V W) := by
  have h1 : IsOpen (pE E ⁻¹' (chr p).source) := (chr p).open_source.preimage hEc
  have h2 : IsOpen (pV V ⁻¹' (chr p).source) := (chr p).open_source.preimage hVc
  have h3 : IsOpen (pE E' ⁻¹' (chr p').source) := (chr p').open_source.preimage hE'c
  have h4 : IsOpen (pW W ⁻¹' (chr p').source) := (chr p').open_source.preimage hWc
  have h : ppRegion p p' E E' V W =
      (pE E ⁻¹' (chr p).source ∩ pV V ⁻¹' (chr p).source) ∩
        (pE E' ⁻¹' (chr p').source ∩ pW W ⁻¹' (chr p').source) := by
    ext y
    simp only [ppRegion, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, pE_apply, pV_apply,
      pW_apply]
    tauto
  rw [h]
  exact (h1.inter h2).inter (h3.inter h4)

/-! ## Zeros of the charted pair map on the region -/

/-- `pair44` vanishes exactly when both components do. -/
lemma pair44_eq_zero_iff (a b : EuclideanSpace ℝ (Fin 4)) :
    pair44 a b = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    constructor
    · ext j
      have := congrArg (fun v : EuclideanSpace ℝ (Fin 8) => v (Fin.castAdd 4 j)) h
      simpa using this
    · ext j
      have := congrArg (fun v : EuclideanSpace ℝ (Fin 8) => v (Fin.natAdd 4 j)) h
      simpa using this
  · rintro ⟨rfl, rfl⟩
    ext i
    fin_cases i <;> simp [pair44]

/-- On the chart region, the charted pair map vanishes exactly where the two pair equations hold. -/
lemma ppDiff_eq_zero_iff {p p' : M} {E E' : ℝ → EuclideanSpace ℝ (Fin 2) → M}
    {V W : EuclideanSpace ℝ (Fin 3) → M} {y : EuclideanSpace ℝ (Fin 9)}
    (hy : y ∈ ppRegion p p' E E' V W) :
    ppDiff p p' E E' V W y = 0 ↔ pE E y = pV V y ∧ pE E' y = pW W y := by
  obtain ⟨h1, h2, h3, h4⟩ := hy
  rw [ppDiff_apply]
  constructor
  · intro h
    obtain ⟨hfst, hsnd⟩ := pair44_eq_zero_iff _ _ |>.mp h
    exact ⟨(chr p).injOn h1 h2 (sub_eq_zero.mp hfst), (chr p').injOn h3 h4 (sub_eq_zero.mp hsnd)⟩
  · rintro ⟨h1', h2'⟩
    rw [h1', h2', sub_self, sub_self]
    exact PMB.pair44_zero

/-! ## Support tools -/

/-- The topological support of a bump function is contained in the closed ball of its outer radius. -/
lemma tsupport_bump_subset_closedBall {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [HasContDiffBump E] {c : E} (f : ContDiffBump c) :
    tsupport f ⊆ Metric.closedBall c f.rOut := by
  refine closure_minimal (fun x hx => ?_) Metric.isClosed_closedBall
  by_contra hmem
  exact hx (f.zero_of_le_dist (le_of_lt (not_le.mp (fun h => hmem (Metric.mem_closedBall.mpr h)))))

/-- A smooth function on an open set, multiplied by a function whose topological support is
contained in that open set, is smooth everywhere. -/
lemma contDiff_smul_of_tsupport_subset {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {g : E → F} {ψ : E → ℝ} {U : Set E}
    (hψ : ContDiff ℝ Ctop ψ) (hU : IsOpen U) (hg : ContDiffOn ℝ Ctop g U)
    (hsupp : tsupport ψ ⊆ U) : ContDiff ℝ Ctop (fun x => ψ x • g x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ U
  · exact (hψ.contDiffAt.smul (hg.contDiffAt (hU.mem_nhds hx)))
  · have hx' : x ∉ tsupport ψ := fun h => hx (hsupp h)
    have hev : ψ =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hx'
    refine (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq ?_
    filter_upwards [hev] with y hy
    simp [hy]

/-! ## Globalization -/

/-- **Globalization of the charted pair map**: on a neighbourhood of a point of its chart region it
agrees with a globally `C^∞` map. -/
theorem exists_ppDiff_extension (p p' : M) (E E' : ℝ → EuclideanSpace ℝ (Fin 2) → M)
    (V W : EuclideanSpace ℝ (Fin 3) → M)
    (hE : ContMDiff (modelWithCornersSelf ℝ (ℝ × EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry E))
    (hE' : ContMDiff (modelWithCornersSelf ℝ (ℝ × EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry E'))
    (hV : ContMDiff (𝓡 3) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hW : ContMDiff (𝓡 3) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) W)
    {x : EuclideanSpace ℝ (Fin 9)} (hx : x ∈ ppRegion p p' E E' V W) :
    ∃ (F : EuclideanSpace ℝ (Fin 9) → EuclideanSpace ℝ (Fin 8))
      (U : Set (EuclideanSpace ℝ (Fin 9))),
      IsOpen U ∧ x ∈ U ∧ U ⊆ ppRegion p p' E E' V W ∧ ContDiff ℝ Ctop F ∧
        Set.EqOn F (ppDiff p p' E E' V W) U := by
  have hEc : Continuous (pE E) := (contMDiff_pE E hE).continuous
  have hE'c : Continuous (pE E') := (contMDiff_pE E' hE').continuous
  have hVc : Continuous (pV V) := (contMDiff_pV V hV).continuous
  have hWc : Continuous (pW W) := (contMDiff_pW W hW).continuous
  have hregion : IsOpen (ppRegion p p' E E' V W) :=
    isOpen_ppRegion p p' E E' V W hEc hE'c hVc hWc
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hregion x hx
  set χ : ContDiffBump x := ⟨r / 4, r / 2, by linarith, by linarith⟩ with hχ
  have hχrIn : χ.rIn = r / 4 := by rw [hχ]
  have hχrOut : χ.rOut = r / 2 := by rw [hχ]
  have hχ1 : ∀ y ∈ Metric.ball x (r / 4), χ y = 1 := fun y hy =>
    χ.one_of_mem_closedBall (Metric.ball_subset_closedBall hy)
  have hχ0 : ∀ y, r / 2 ≤ dist y x → χ y = 0 := by
    intro y hy
    refine χ.zero_of_le_dist ?_
    simpa [Metric.mem_closedBall, dist_comm] using hy
  have htsupp : tsupport (χ : EuclideanSpace ℝ (Fin 9) → ℝ) ⊆ ppRegion p p' E E' V W := by
    refine (tsupport_bump_subset_closedBall χ).trans ?_
    intro y hy
    refine hsub (Metric.mem_ball.mpr ?_)
    have hy' : dist y x ≤ χ.rOut := Metric.mem_closedBall.mp hy
    have : dist y x < r := by rw [hχrOut] at hy'; linarith
    simpa [dist_comm] using this
  refine ⟨fun y => χ y • ppDiff p p' E E' V W y, Metric.ball x (r / 4),
    Metric.isOpen_ball, Metric.mem_ball_self (by linarith), ?_, ?_, ?_⟩
  · intro y hy
    refine hsub (Metric.mem_ball.mpr (lt_of_lt_of_le (Metric.mem_ball.mp hy) ?_))
    linarith
  · exact contDiff_smul_of_tsupport_subset χ.contDiff hregion
      (contDiffOn_ppDiff p p' E E' V W hE hE' hV hW) htsupp
  · intro y hy
    show χ y • ppDiff p p' E E' V W y = ppDiff p p' E E' V W y
    rw [hχ1 y hy, one_smul]


end

end PPB
end Work.Drive
