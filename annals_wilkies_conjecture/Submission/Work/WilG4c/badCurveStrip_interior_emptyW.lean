import Mathlib
import Submission.Work.WilG4a.F1AffineW
import Submission.Work.WilG4c.badCurveStrip_interior_empty
import Submission.Work.WilG4c.StepLipDefs

set_option autoImplicit false
noncomputable section
open Classical
open scoped Topology

namespace Work.WilG4c

open Work.WilkG4c

open WilkiesDesign WilkiesDesign.CG

/-- **`badCurveStrip_interior_empty` with the corrected `h1` binder.**  The frozen
`WilkiesDesign.CG.F1Affine` is FALSE at `p = 1`, so the already-proved
`Work.WilG4c.badCurveStrip_interior_empty` (which carries `h1 : ∀ q, F1Affine S q`) can no
longer be applied.  Its hypothesis `h1` occurs ONLY in its statement — the proof never uses it
(the work goes through `Work.WilkG4c.bddDxHyp_of_choice`).  So this is the same statement with
the `h1` binder restated as the corrected `Work.WilG4a.F1AffineW`, and the proof is a verbatim
copy of the original with only the binder type changed. -/
theorem badCurveStrip_interior_emptyW (S : WilkiesDesign.SOMin) (hcd : S.SharpCD)
    (hder : S.SharpDeriv)
    (hchoice : Work.WilkG4c.ChoiceHyp S) (h1 : ∀ q, Work.WilG4a.F1AffineW S q)
    {p n F0 D r : ℕ} (hr : 1 ≤ r) {f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ}
    (hf : WilkiesDesign.CG.famGraph f ∈ S.Ω F0 D (p + (n + 1) + 1))
    (hval : ∀ l : Fin p → ℝ, ∀ z ∈ WilkiesDesign.openCube (n + 1), f l z ∈ Set.Ioo (0 : ℝ) 1)
    (hY : ∀ l : Fin p → ℝ, ∀ x ∈ Work.WilkG4c.I, ∀ m, m ≤ r → ∀ y ∈ WilkiesDesign.openCube n,
      ‖iteratedFDeriv ℝ m (Work.WilkG4c.slice (f l) x) y‖ ≤ 1) :
    interior {w : Fin (p + 1) → ℝ | w (Fin.last p) ∈ Work.WilkG4c.I ∧ w ∈ Work.WilkG4c.badCurve f}
      = ∅ := by
  classical
  obtain ⟨K, hK⟩ := Work.WilG4c.graphOf_member_mem S p n
  -- (1) the `x`-partial is bounded off a finite set of `x`, for each parameter `l`
  have hperl : ∀ l : Fin p → ℝ, ∃ s : Finset ℝ, ∀ x ∈ I, x ∉ s →
      BddAbove ((fun y => |xDeriv f l x y|) ''
        {y : Fin n → ℝ | y ∈ openCube n ∧
          xPt l x y ∈ interior {z : Fin (p + (n + 1)) → ℝ |
            ContDiffAt ℝ 1 (famFunHat f) z}}) := by
    intro l
    obtain ⟨s, hs⟩ := (bddDxHyp_of_choice S hcd hder hchoice) (f l)
      (hK F0 D f l hf) (fun z hz => hval l z hz) (by
        refine ⟨∅, fun x hx _ => ⟨1, fun y hy _ i => ?_⟩⟩
        calc |fderiv ℝ (f l) (Fin.cons x y) (Pi.single i.succ 1)|
            ≤ ‖iteratedFDeriv ℝ 1 (slice (f l) x) y‖ := abs_fderiv_cons_le (f l) x y i
          _ ≤ 1 := hY l x hx 1 hr y hy)
    refine ⟨s, fun x hx hxs => ?_⟩
    obtain ⟨B, hB⟩ := hs x hx hxs
    refine ⟨B, ?_⟩
    rintro b ⟨y, ⟨hyc, hyl⟩, rfl⟩
    change |xDeriv f l x y| ≤ B
    have hlocus : ContDiffAt ℝ 1 (famFunHat f) (xPt l x y) :=
      (mem_interior_contDiffAt_locus 1 (famFunHat f) (xPt l x y)).mp hyl
    rw [Work.WilG4c.pullX_xDeriv_eq_fderiv f l x y (hlocus.differentiableAt (by norm_num))]
    refine hB y hyc ?_
    exact (mem_interior_contDiffAt_locus 1 (f l) (Fin.cons x y)).mpr
      (by simpa [pt] using contDiffAt_famFunHat_xPt f l x y hlocus)
  -- (2) the second exceptional set has empty interior
  let sOf : (Fin p → ℝ) → Finset ℝ := fun l => Classical.choose (hperl l)
  have hsOf : ∀ l, ∀ x ∈ I, x ∉ sOf l → BddAbove ((fun y => |xDeriv f l x y|) ''
      {y : Fin n → ℝ | y ∈ openCube n ∧
        xPt l x y ∈ interior {z : Fin (p + (n + 1)) → ℝ |
          ContDiffAt ℝ 1 (famFunHat f) z}}) := fun l => Classical.choose_spec (hperl l)
  set Sset : Set (Fin (p + 1) → ℝ) :=
    {w | w (Fin.last p) ∈ sOf (fun i => w (Fin.castSucc i))} with hSsetdef
  have hinteriorS : interior Sset = ∅ := by
    rw [← Set.not_nonempty_iff_eq_empty]
    rintro ⟨w, hw⟩
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior w hw
    set x₀ : ℝ := w (Fin.last p) with hx₀def
    set l₀ : Fin p → ℝ := fun i => w (Fin.castSucc i) with hl₀def
    have hw_eq : (Fin.snoc l₀ x₀ : Fin (p + 1) → ℝ) = w := by
      funext i
      refine Fin.lastCases ?_ ?_ i
      · rw [Fin.snoc_last, hx₀def]
      · intro i'; rw [Fin.snoc_castSucc, hl₀def]
    have hsub : Set.Ioo (x₀ - ε) (x₀ + ε) ⊆ (sOf l₀ : Set ℝ) := by
      intro x hx
      have hmem : (Fin.snoc l₀ x : Fin (p + 1) → ℝ) ∈ Metric.ball w ε := by
        rw [Metric.mem_ball]
        rw [show dist (Fin.snoc l₀ x : Fin (p + 1) → ℝ) w
            = |x - x₀| from by rw [← hw_eq]; exact Work.WilG1.Cell.dist_snoc_last l₀ x x₀]
        rw [abs_lt]
        exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
      have hS := interior_subset (hball hmem)
      simp only [hSsetdef, Set.mem_ofPred_eq] at hS
      have hl : (fun i : Fin p => (Fin.snoc l₀ x : Fin (p + 1) → ℝ) (Fin.castSucc i)) = l₀ := by
        funext i; rw [Fin.snoc_castSucc]
      have hlast : (Fin.snoc l₀ x : Fin (p + 1) → ℝ) (Fin.last p) = x := by simp
      rw [hl, hlast] at hS
      exact hS
    have hinf : (Set.Ioo (x₀ - ε) (x₀ + ε)).Infinite := Set.Ioo_infinite (by linarith)
    exact (Set.Infinite.mono hsub hinf) ((sOf l₀).finite_toSet)
  -- (3) the `CaseA` set is nowhere dense
  have hD := interior_closure_nonC1_empty S hcd (famFunHat f) hf
  have hCA : IsNowhereDense (CaseA f) := CaseA_nowhereDense f hD
  -- (4) every bad `(l,x)` with `x ∈ I` lies in `CaseA f ∪ Sset`
  have hTsub : {w : Fin (p + 1) → ℝ | w (Fin.last p) ∈ I ∧ w ∈ badCurve f}
      ⊆ CaseA f ∪ Sset := by
    intro w hw
    obtain ⟨hxI, hbad⟩ := hw
    simp only [badCurve, Set.mem_ofPred_eq] at hbad
    by_cases hx : w (Fin.last p) ∈ sOf (fun i => w (Fin.castSucc i))
    · exact Or.inr hx
    · refine Or.inl fun y hy hyl => ?_
      exfalso
      have hbdd := hsOf (fun i => w (Fin.castSucc i)) (w (Fin.last p)) hxI hx
      have hne : ({y : Fin n → ℝ | y ∈ openCube n ∧
          xPt (fun i => w (Fin.castSucc i)) (w (Fin.last p)) y ∈
            interior {z : Fin (p + (n + 1)) → ℝ |
              ContDiffAt ℝ 1 (famFunHat f) z}}).Nonempty := ⟨y, hy, hyl⟩
      obtain ⟨y₀, hy₀, hmax⟩ := Work.WilG4c.exists_nearmax_of_bdd hne
        (fun y => xDeriv f (fun i => w (Fin.castSucc i)) (w (Fin.last p)) y) hbdd
      exact hbad ⟨y₀, hy₀.1, hy₀.2, fun y' hy' hyl' => hmax y' ⟨hy', hyl'⟩⟩
  -- (5) assemble
  rw [← Set.not_nonempty_iff_eq_empty]
  rintro ⟨w, hw⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior w hw
  have hB_sub : Metric.ball w ε ⊆ CaseA f ∪ Sset :=
    fun z hz => hTsub (interior_subset (hball hz))
  have hne : (Metric.ball w ε \ closure (CaseA f)).Nonempty := by
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty, Set.sdiff_eq_empty] at hcon
    have hsub' : Metric.ball w ε ⊆ interior (closure (CaseA f)) :=
      interior_maximal hcon Metric.isOpen_ball
    rw [show interior (closure (CaseA f)) = ∅ from hCA] at hsub'
    exact hsub' (Metric.mem_ball_self hε)
  obtain ⟨z, hz⟩ := hne
  have hopen : IsOpen (Metric.ball w ε \ closure (CaseA f)) :=
    IsOpen.sdiff Metric.isOpen_ball isClosed_closure
  have hzS : Metric.ball w ε \ closure (CaseA f) ⊆ Sset := by
    intro z' hz'
    rcases hB_sub hz'.1 with h | h
    · exact absurd (subset_closure h) hz'.2
    · exact h
  have hzint : z ∈ interior Sset :=
    mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset (hopen.mem_nhds hz) hzS)
  rw [hinteriorS] at hzint
  exact hzint

end Work.WilG4c
