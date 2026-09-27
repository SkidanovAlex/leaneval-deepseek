import Mathlib
import Submission.Work.Drive.projCharted
import Submission.Work.Drive.ProjectiveTopology
import Submission.Work.Drive.isCoveringMap_projOfUnitSphere

namespace Work.Drive

open scoped Manifold ContDiff

set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

noncomputable section

/-! ## The box and its midpoint

The box `[a,b] × [c,d] ⊆ ℝ²` is convex, hence contractible and locally path connected, so the
lifting criterion for the covering map `S³ → ℝP³` applies to it directly.  The two elementary
lemmas below (`convex_liftBox`, `midLiftBox_mem`) supply exactly the convexity and the non-emptiness
that `Convex.contractibleSpace` and `Convex.locallyPathConnectedSpace` consume. -/

/-- The closed box `[a,b] × [c,d]` inside `ℝ²`. -/
private def liftBox (a b c d : ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  {q | q 0 ∈ Set.Icc a b ∧ q 1 ∈ Set.Icc c d}

/-- The box is convex. -/
private lemma convex_liftBox (a b c d : ℝ) : Convex ℝ (liftBox a b c d) := by
  intro x hx y hy p q hp hq hpq
  refine ⟨?_, ?_⟩
  · have h := (convex_Icc a b) hx.1 hy.1 hp hq hpq
    have hxy : (p • x + q • y) 0 = p * (x 0) + q * (y 0) := by
      simp [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    rwa [hxy]
  · have h := (convex_Icc c d) hx.2 hy.2 hp hq hpq
    have hxy : (p • x + q • y) 1 = p * (x 1) + q * (y 1) := by
      simp [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    rwa [hxy]

/-- The midpoint of the box. -/
private def midLiftBox (a b c d : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then (a + b) / 2 else (c + d) / 2)

private lemma midLiftBox_zero (a b c d : ℝ) : midLiftBox a b c d 0 = (a + b) / 2 := by
  rw [midLiftBox, WithLp.ofLp_toLp]
  simp

private lemma midLiftBox_one (a b c d : ℝ) : midLiftBox a b c d 1 = (c + d) / 2 := by
  rw [midLiftBox, WithLp.ofLp_toLp]
  simp

/-- The midpoint lies in the box when the box is non-degenerate. -/
private lemma midLiftBox_mem (a b c d : ℝ) (hab : a < b) (hcd : c < d) :
    midLiftBox a b c d ∈ liftBox a b c d := by
  simp only [liftBox, Set.mem_ofPred_eq]
  rw [midLiftBox_zero, midLiftBox_one]
  exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

/-- **A continuous unit lift of a `C^∞`-on-a-box map `h : ℝ² → ℝP³`.**  If `h` is `C^∞` (Whitney)
on the closed box `[a,b] × [c,d]` then there is `v : ℝ² → S³`, continuous on the box, with
`projOfUnitSphere (v q) = h q` for `q` in the box.  The box is convex, hence simply connected and
locally path connected, so the lifting criterion for the covering map `S³ → ℝP³` applies. -/
theorem exists_lift_box_projOfUnitSphere (a b c d : ℝ) (hab : a < b) (hcd : c < d)
    {h : EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (EuclideanSpace ℝ (Fin 4))}
    (hh : letI := Work.Drive.projCharted 3
      ContMDiffOn (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) ((⊤ : ℕ∞) : WithTop ℕ∞) h
        {q : EuclideanSpace ℝ (Fin 2) | q 0 ∈ Set.Icc a b ∧ q 1 ∈ Set.Icc c d})
    (hcov : IsCoveringMap (Work.Drive.projOfUnitSphere (n := 3))) :
    ∃ v : EuclideanSpace ℝ (Fin 2) → Work.Drive.unitSphere 3,
      ContinuousOn v {q : EuclideanSpace ℝ (Fin 2) | q 0 ∈ Set.Icc a b ∧ q 1 ∈ Set.Icc c d} ∧
      ∀ q : EuclideanSpace ℝ (Fin 2), q 0 ∈ Set.Icc a b → q 1 ∈ Set.Icc c d →
        Work.Drive.projOfUnitSphere (v q) = h q := by
  letI := Work.Drive.projCharted 3
  classical
  -- `h` is continuous on the box, since it is smooth there.
  have hc : ContinuousOn h (liftBox a b c d) := hh.continuousOn
  -- The box, as a subtype, is contractible (hence simply connected) and locally path connected.
  have hne : (liftBox a b c d).Nonempty :=
    ⟨midLiftBox a b c d, midLiftBox_mem a b c d hab hcd⟩
  haveI : ContractibleSpace {q : EuclideanSpace ℝ (Fin 2) // q ∈ liftBox a b c d} :=
    (convex_liftBox a b c d).contractibleSpace hne
  haveI : LocallyPathConnectedSpace {q : EuclideanSpace ℝ (Fin 2) // q ∈ liftBox a b c d} :=
    (convex_liftBox a b c d).locallyPathConnectedSpace
  -- The restriction of `h` to the box, and a point above `h` of the box.
  let f : C({q : EuclideanSpace ℝ (Fin 2) // q ∈ liftBox a b c d},
      Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) := ⟨fun x => h x.1, hc.domRestrict⟩
  let x₀ : {q : EuclideanSpace ℝ (Fin 2) // q ∈ liftBox a b c d} :=
    ⟨midLiftBox a b c d, midLiftBox_mem a b c d hab hcd⟩
  obtain ⟨e₀, he₀⟩ := Work.Drive.surjective_projOfUnitSphere (h x₀.1)
  -- The lifting criterion gives a continuous lift `F : box → S³` of `h|box`.
  obtain ⟨F, ⟨-, hFlift⟩, -⟩ := hcov.existsUnique_continuousMap_lifts f x₀ e₀ he₀
  refine ⟨fun q => if hq : q ∈ liftBox a b c d then F ⟨q, hq⟩ else F x₀, ?_, ?_⟩
  · -- On the box, `v` is `F` read through the inclusion of the box as a subtype.
    rw [continuousOn_iff_continuous_domRestrict]
    refine F.continuous.congr (fun x => ?_)
    simp only [Set.domRestrict, dif_pos x.2]
  · intro q hq0 hq1
    have hq : q ∈ liftBox a b c d := ⟨hq0, hq1⟩
    show Work.Drive.projOfUnitSphere
      (if hq' : q ∈ liftBox a b c d then F ⟨q, hq'⟩ else F x₀) = h q
    rw [dif_pos hq]
    exact congr_fun hFlift ⟨q, hq⟩

end

end Work.Drive
