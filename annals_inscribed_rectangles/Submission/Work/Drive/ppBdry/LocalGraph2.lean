import Mathlib
import Submission.Work.Drive.ppBdry.LocalGraph

/-!
# The local graph structure of the pair-meet set

From `Work.Drive.PPRegAt E E' V W x` at a meet `x`, the charted pair map taken at the meet-value
charts is a smooth submersion near `x` whose zero set there is the meet set; the implicit function
theorem (`Work.Drive.exists_local_normalForm`) then exhibits the meet set near `x` as the graph of a
smooth map over a coordinate axis.  This file records that structure, in the *relative* form (in
which membership in the box is part of the condition), valid at every point of `ppMeet`.
-/

namespace Work.Drive
namespace PPB

open scoped Manifold ContDiff Topology
open Manifold Set

noncomputable section

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [IsManifold (𝓡 4) Ctop M]

/-- The graph map `u ↦ u • eᵢ + η u`. -/
def pgGmap (i : Fin 9) (η : ℝ → EuclideanSpace ℝ (Fin 9)) :
    ℝ → EuclideanSpace ℝ (Fin 9) := fun u => u • EuclideanSpace.single i (1 : ℝ) + η u

/-- A local graph presentation of the pair-meet set at a point. -/
structure PPLocalGraph (E E' : ℝ → EuclideanSpace ℝ (Fin 2) → M)
    (V W : EuclideanSpace ℝ (Fin 3) → M) (x : EuclideanSpace ℝ (Fin 9)) where
  /-- the coordinate over which the meet set is a graph -/
  i : Fin 9
  /-- the open set on which the presentation is valid -/
  U : Set (EuclideanSpace ℝ (Fin 9))
  /-- the graph map -/
  η : ℝ → EuclideanSpace ℝ (Fin 9)
  hU : IsOpen U
  hxU : x ∈ U
  hη : ContDiff ℝ Ctop η
  hηi : ∀ t, η t i = 0
  hηx : η (x i) = x - (x i) • EuclideanSpace.single i (1 : ℝ)
  /-- membership in the meet set is membership in the box together with lying on the graph -/
  hmem : ∀ y ∈ U, (y ∈ ppMeet E E' V W ↔
    y ∈ Submission.Drive.unitBox 8 ∧ y = pgGmap i η (y i))


/-- **Every point of the pair-meet set has a local graph presentation.** -/
theorem exists_pp_localGraph (E E' : ℝ → EuclideanSpace ℝ (Fin 2) → M)
    (V W : EuclideanSpace ℝ (Fin 3) → M)
    (hE : ContMDiff (modelWithCornersSelf ℝ (ℝ × EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry E))
    (hE' : ContMDiff (modelWithCornersSelf ℝ (ℝ × EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry E'))
    (hV : ContMDiff (𝓡 3) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hW : ContMDiff (𝓡 3) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) W)
    (hreg : ∀ x ∈ ppMeet E E' V W, PPRegAt E E' V W x)
    {x : EuclideanSpace ℝ (Fin 9)} (hx : x ∈ ppMeet E E' V W) :
    Nonempty (PPLocalGraph E E' V W x) := by
  have hxm : x ∈ ppMeet E E' V W := hx
  obtain ⟨hsurjΛ, hfaceΛ⟩ := hreg x hx
  have hregion : x ∈ ppRegion (E (ftS x) (ftU x)) (E' (ftS x) (ftU x)) E E' V W :=
    mem_ppRegion_self hx
  obtain ⟨F, U₀, hU₀open, hxU₀, hU₀sub, hFsmooth, hFeq⟩ :=
    exists_ppDiff_extension (E (ftS x) (ftU x)) (E' (ftS x) (ftU x)) E E' V W
      hE hE' hV hW hregion
  have hFx : F x = 0 := by
    rw [hFeq hxU₀]
    exact (ppDiff_eq_zero_iff hregion).mpr ⟨(mem_ppMeet.mp hxm).2.1, (mem_ppMeet.mp hxm).2.2⟩
  have hderiv : fderiv ℝ F x =
      fderiv ℝ (ppDiff (E (ftS x) (ftU x)) (E' (ftS x) (ftU x)) E E' V W) x :=
    Filter.EventuallyEq.fderiv_eq (hFeq.eventuallyEq_of_mem (hU₀open.mem_nhds hxU₀))
  have hsurjF : Function.Surjective (fderiv ℝ F x) := by
    rw [hderiv]; exact hsurjΛ
  have hkey : ∃ i : Fin 9, Function.Surjective (fun v : {v : EuclideanSpace ℝ (Fin 9) // v i = 0} =>
      fderiv ℝ F x v.1) := by
    by_cases hint : x ∈ interior (Submission.Drive.unitBox 8)
    · exact Work.Drive.exists_domRestrict_surjective hsurjF
    · have hxbox : x ∈ Submission.Drive.unitBox 8 := (mem_ppMeet.mp hxm).1
      have hbdry : x ∈ Submission.Drive.unitBoxBdry 8 :=
        ⟨hxbox, Work.Drive.exists_coord_eq_zero_or_one_of_not_mem_interior hxbox hint⟩
      obtain ⟨i, -, -, hi⟩ := hfaceΛ hbdry
      exact ⟨i, by rw [hderiv]; exact hi⟩
  obtain ⟨i, hsurj_i⟩ := hkey
  obtain ⟨δ, ρ, η, hδ, hρ, hηcd, hηi, hηx, hgraph1, hgraph2⟩ :=
    exists_local_normalForm hFsmooth hFx i hsurj_i
  set U : Set (EuclideanSpace ℝ (Fin 9)) :=
    U₀ ∩ {y : EuclideanSpace ℝ (Fin 9) | |y i - x i| < δ} ∩
      {y : EuclideanSpace ℝ (Fin 9) |
        ‖y - (y i) • EuclideanSpace.single i (1 : ℝ) - η (y i)‖ < ρ} with hUdef
  refine ⟨i, U, η, ?_, ?_, hηcd, hηi, hηx, ?_⟩
  · refine (hU₀open.inter ?_).inter ?_
    · exact isOpen_lt (by fun_prop : Continuous fun y : EuclideanSpace ℝ (Fin 9) => |y i - x i|)
        continuous_const
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
    have hyF : F y = ppDiff (E (ftS x) (ftU x)) (E' (ftS x) (ftU x)) E E' V W y := hFeq hyU₀
    have hyreg : y ∈ ppRegion (E (ftS x) (ftU x)) (E' (ftS x) (ftU x)) E E' V W := hU₀sub hyU₀
    constructor
    · rintro ⟨hybox, hy1, hy2⟩
      refine ⟨hybox, ?_⟩
      show y = (y i) • EuclideanSpace.single i (1 : ℝ) + η (y i)
      rw [← hgraph2 y hyδ hyρ, hyF, (ppDiff_eq_zero_iff hyreg).mpr ⟨hy1, hy2⟩]
    · rintro ⟨hybox, hygraph⟩
      have hygraph' : y = (y i) • EuclideanSpace.single i (1 : ℝ) + η (y i) := hygraph
      rw [← hgraph2 y hyδ hyρ, hyF] at hygraph'
      obtain ⟨h1', h2'⟩ := (ppDiff_eq_zero_iff hyreg).mp hygraph'
      exact ⟨hybox, h1', h2'⟩

end
end PPB
end Work.Drive
