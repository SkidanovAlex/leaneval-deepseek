import Mathlib
import Submission.Work.Drive.ppIntrinsic.Defs
import Submission.Work.Drive.ppParity.Defs
import Submission.Work.Drive.ppBdry.LocalGraph2

namespace Work.Drive.ppIntrinsic

open scoped Manifold ContDiff Topology
open Manifold Set

set_option backward.isDefEq.respectTransparency false

noncomputable section

/-- **The chart-free local graph presentation of `Zpp` at a meet.**

At a meet `x` of `ppMeet E E' V W`, given a coordinate `i` over which the derivative of the
(self-centred, charted) pair map is surjective when restricted to the hyperplane `{v | v i = 0}`,
there is an open neighbourhood `U` of `x` on which `Zpp E E' V W` agrees with the graph
`y ↦ (y i) • eᵢ + η (y i)` of a smooth map `η` with `η t i = 0`.

This is the *absolute* (box-free) local graph presentation of the chart-free equation set `Zpp`,
as opposed to the *relative* one of `ppMeet` in `Work.Drive.PPB.exists_pp_localGraph`: the box
condition is dropped from the membership, so the presentation is valid also at the boundary points of
the box, where the graph leaves the box. -/
theorem ppMeet_localGraph_Zpp
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (E E' : ℝ → EuclideanSpace ℝ (Fin 2) → M) (V W : EuclideanSpace ℝ (Fin 3) → M)
    (hE : ContMDiff
      (modelWithCornersSelf ℝ (ℝ × EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry E))
    (hE' : ContMDiff
      (modelWithCornersSelf ℝ (ℝ × EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry E'))
    (hV : ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hW : ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) W)
    {x : EuclideanSpace ℝ (Fin 9)} (hx : x ∈ Work.Drive.ppMeet E E' V W)
    (hreg : Work.Drive.PPRegAt E E' V W x) (i : Fin 9)
    (hsurj : Function.Surjective (fun v : {v : EuclideanSpace ℝ (Fin 9) // v i = 0} =>
        fderiv ℝ (Work.Drive.ppDiff (E (Work.Drive.ftS x) (Work.Drive.ftU x))
          (E' (Work.Drive.ftS x) (Work.Drive.ftU x)) E E' V W) x v.1)) :
    ∃ (U : Set (EuclideanSpace ℝ (Fin 9))) (η : ℝ → EuclideanSpace ℝ (Fin 9)),
      IsOpen U ∧ x ∈ U ∧ ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η ∧ (∀ t : ℝ, η t i = 0) ∧
      (∀ y ∈ U, (y ∈ Work.Drive.Zpp E E' V W ↔
        y = (y i) • EuclideanSpace.single i (1 : ℝ) + η (y i))) := by
  -- the self-centred chart pair of the meet
  have hregion : x ∈ Work.Drive.ppRegion (E (Work.Drive.ftS x) (Work.Drive.ftU x))
      (E' (Work.Drive.ftS x) (Work.Drive.ftU x)) E E' V W :=
    Work.Drive.PPB.mem_ppRegion_self hx
  obtain ⟨F, U₀, hU₀open, hxU₀, hU₀sub, hFsmooth, hFeq⟩ :=
    Work.Drive.PPB.exists_ppDiff_extension (E (Work.Drive.ftS x) (Work.Drive.ftU x))
      (E' (Work.Drive.ftS x) (Work.Drive.ftU x)) E E' V W hE hE' hV hW hregion
  have hFx : F x = 0 := by
    rw [hFeq hxU₀]
    exact (Work.Drive.PPB.ppDiff_eq_zero_iff hregion).mpr ⟨hx.2.1, hx.2.2⟩
  have hderiv : fderiv ℝ F x =
      fderiv ℝ (Work.Drive.ppDiff (E (Work.Drive.ftS x) (Work.Drive.ftU x))
        (E' (Work.Drive.ftS x) (Work.Drive.ftU x)) E E' V W) x :=
    Filter.EventuallyEq.fderiv_eq (hFeq.eventuallyEq_of_mem (hU₀open.mem_nhds hxU₀))
  have hsurjF : Function.Surjective (fun v : {v : EuclideanSpace ℝ (Fin 9) // v i = 0} =>
      fderiv ℝ F x v.1) := by
    rw [hderiv]; exact hsurj
  obtain ⟨δ, ρ, η, hδ, hρ, hηcd, hηi, hηx, hgraph1, hgraph2⟩ :=
    Work.Drive.exists_local_normalForm hFsmooth hFx i hsurjF
  refine ⟨U₀ ∩ {y : EuclideanSpace ℝ (Fin 9) | |y i - x i| < δ} ∩
      {y : EuclideanSpace ℝ (Fin 9) |
        ‖y - (y i) • EuclideanSpace.single i (1 : ℝ) - η (y i)‖ < ρ}, η, ?_, ?_, hηcd, hηi, ?_⟩
  · refine (hU₀open.inter ?_).inter ?_
    · exact isOpen_lt (by fun_prop) continuous_const
    · exact isOpen_lt (by fun_prop) continuous_const
  · refine ⟨⟨hxU₀, ?_⟩, ?_⟩
    · show |x i - x i| < δ
      rw [sub_self, abs_zero]
      exact hδ
    · show ‖x - (x i) • EuclideanSpace.single i (1 : ℝ) - η (x i)‖ < ρ
      rw [hηx]
      have hzero : x - (x i) • EuclideanSpace.single i (1 : ℝ) -
          (x - (x i) • EuclideanSpace.single i (1 : ℝ)) = 0 := sub_self _
      rw [hzero, norm_zero]
      exact hρ
  · intro y hy
    obtain ⟨⟨hyU₀, hyδ⟩, hyρ⟩ := hy
    have hyF : F y = Work.Drive.ppDiff (E (Work.Drive.ftS x) (Work.Drive.ftU x))
        (E' (Work.Drive.ftS x) (Work.Drive.ftU x)) E E' V W y := hFeq hyU₀
    have hyreg : y ∈ Work.Drive.ppRegion (E (Work.Drive.ftS x) (Work.Drive.ftU x))
        (E' (Work.Drive.ftS x) (Work.Drive.ftU x)) E E' V W := hU₀sub hyU₀
    rw [Work.Drive.mem_Zpp]
    constructor
    · rintro ⟨h1, h2⟩
      rw [← hgraph2 y hyδ hyρ, hyF, (Work.Drive.PPB.ppDiff_eq_zero_iff hyreg).mpr ⟨h1, h2⟩]
    · rintro hygraph
      have hygraph' : y = (y i) • EuclideanSpace.single i (1 : ℝ) + η (y i) := hygraph
      rw [← hgraph2 y hyδ hyρ, hyF] at hygraph'
      exact (Work.Drive.PPB.ppDiff_eq_zero_iff hyreg).mp hygraph'

end

end Work.Drive.ppIntrinsic
