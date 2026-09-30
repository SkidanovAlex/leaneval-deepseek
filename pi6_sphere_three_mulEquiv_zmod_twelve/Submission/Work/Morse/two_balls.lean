import Mathlib
import Submission.Work.Morse.TwoBallsBasic
import Submission.Work.Morse.boundary_homeo
import Submission.Work.Morse.coning_extension

set_option synthInstance.maxHeartbeats 400000

/-!
# Glueing two closed balls along their boundary: `Dⁿ ∪_{Sⁿ⁻¹} Dⁿ ≅ Sⁿ`

`Work.Morse.two_balls` is the topological fact underlying Reeb's theorem: a compact Hausdorff
space covered by two closed subsets each homeomorphic to the closed unit ball `Dⁿ`, glued along
the unit sphere, is homeomorphic to `Sⁿ`.

The proof builds an explicit continuous bijection onto the unit sphere of `ℝⁿ⁺¹`: on `A` we use
the upper graph parametrisation `upMap ∘ α`, on `B` the lower one `downMap ∘ C ∘ β`, where
`C` is a self-homeomorphism of `Dⁿ` (built by coning the boundary identification `Sⁿ⁻¹ ≃ₜ Sⁿ⁻¹`
coming from `α` and `β`) that arranges for the two halves to agree on `A ∩ B`.  A continuous
bijection from the compact space `X` to the Hausdorff sphere is then a homeomorphism.
-/

open scoped Manifold ContDiff Topology
open Metric

namespace Work.Morse

lemma mem_of_not_mem_of_union_eq_univ {X : Type*} {A B : Set X} (hAB : A ∪ B = Set.univ)
    {x : X} (hx : x ∉ A) : x ∈ B := by
  have : x ∈ A ∪ B := by rw [hAB]; exact Set.mem_univ x
  rw [Set.mem_union] at this
  rcases this with h | h
  · exact absurd h hx
  · exact h

/-- The map that glues `A` (via the upper hemisphere parametrisation of `α`) to `B` (via the
lower hemisphere parametrisation of `C ∘ β`). -/
noncomputable def glueMap {n : ℕ} {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : A ∪ B = Set.univ)
    (α : A ≃ₜ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)
    (β : B ≃ₜ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)
    (C : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 ≃ₜ
         Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) (x : X) :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 := by
  classical
  exact if h : x ∈ A then upMap (α ⟨x, h⟩)
    else downMap (C (β ⟨x, mem_of_not_mem_of_union_eq_univ hAB h⟩))

lemma glueMap_of_mem_A {n : ℕ} {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : A ∪ B = Set.univ)
    (α : A ≃ₜ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)
    (β : B ≃ₜ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)
    (C : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 ≃ₜ
         Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) (x : A) :
    glueMap hAB α β C (x : X) = upMap (α x) := by
  unfold glueMap
  rw [dif_pos x.2]

theorem two_balls {n : ℕ} (hn : 1 ≤ n) {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X]
    {A B : Set X} (hA : IsClosed A) (hB : IsClosed B) (hAB : A ∪ B = Set.univ)
    {α : A ≃ₜ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1}
    {β : B ≃ₜ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1}
    (hα : ∀ x : A, (x : X) ∈ B ↔ α x ∈ Metric.sphere 0 1)
    (hβ : ∀ x : B, (x : X) ∈ A ↔ β x ∈ Metric.sphere 0 1) :
    Nonempty (X ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) := by
  classical
  have _hn := hn
  -- the boundary identification coming from `α` and `β`
  obtain ⟨γ, hγ⟩ := boundary_homeo (n := n) hα hβ
  -- its coning extension to the ball
  obtain ⟨C, hCboundary, hCnorm⟩ := coning_extension γ.symm
  let f : X → Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 := glueMap hAB α β C
  -- values of `f` on `A` and `B`
  have hfA : ∀ x : A, f x = upMap (α x) := fun x => by
    show glueMap hAB α β C (x : X) = upMap (α x)
    exact glueMap_of_mem_A hAB α β C x
  have hfB : ∀ x : B, f x = downMap (C (β x)) := by
    intro x
    by_cases hx : (x : X) ∈ A
    · have hsphere : (β x : EuclideanSpace ℝ (Fin n)) ∈
          Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := (hβ x).mp hx
      set u : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 :=
        ⟨(β x : EuclideanSpace ℝ (Fin n)), hsphere⟩ with hu
      have hgu : (γ.symm u : EuclideanSpace ℝ (Fin n))
          = (α ⟨(x : X), hx⟩ : EuclideanSpace ℝ (Fin n)) := by
        have hu_eq : u = γ ⟨α ⟨(x : X), hx⟩, (hα ⟨(x : X), hx⟩).mp x.2⟩ := by
          apply Subtype.ext
          rw [hu]
          simpa using (hγ ⟨(x : X), hx⟩ x.2).symm
        have h2 := congrArg
          (fun z : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
            (γ.symm z : EuclideanSpace ℝ (Fin n))) hu_eq
        simpa using h2
      have hCeq : C (β x) = α ⟨(x : X), hx⟩ := by
        apply Subtype.ext
        have hbound := hCboundary u
        rw [show (⟨(u : EuclideanSpace ℝ (Fin n)), Metric.sphere_subset_closedBall u.2⟩ :
              Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) = β x from Subtype.ext rfl] at hbound
        rw [hbound, hgu]
      rw [hfA ⟨(x : X), hx⟩, hCeq]
      exact upMap_eq_downMap_of_norm_eq_one
        (norm_eq_one_of_mem_sphere_closedBall (α ⟨(x : X), hx⟩) ((hα ⟨(x : X), hx⟩).mp x.2))
    · show glueMap hAB α β C (x : X) = downMap (C (β x))
      unfold glueMap
      rw [dif_neg hx]
  -- sign of the last coordinate on the two halves
  have hA_nonneg : ∀ x : A, 0 ≤ lastCoord n (f (x : X)) := by
    intro x
    rw [hfA x, lastCoord_upMap]
    exact Real.sqrt_nonneg _
  have hB_nonpos : ∀ x : B, lastCoord n (f (x : X)) ≤ 0 := by
    intro x
    rw [hfB x, lastCoord_downMap]
    exact neg_nonpos.mpr (Real.sqrt_nonneg _)
  have hA_zero : ∀ x : A, lastCoord n (f (x : X)) = 0 ↔ (x : X) ∈ B := by
    intro x
    rw [hfA x, lastCoord_upMap]
    have hnn : 0 ≤ 1 - ‖(α x : EuclideanSpace ℝ (Fin n))‖ ^ 2 :=
      by nlinarith [norm_nonneg (α x : EuclideanSpace ℝ (Fin n)),
        norm_le_one_of_mem_closedBall (α x).2]
    rw [Real.sqrt_eq_zero hnn]
    constructor
    · intro h
      refine (hα x).mpr ?_
      have hnorm : ‖(α x : EuclideanSpace ℝ (Fin n))‖ = 1 := by
        rcases sq_eq_one_iff.mp (by linarith :
          ‖(α x : EuclideanSpace ℝ (Fin n))‖ ^ 2 = 1) with h' | h'
        · exact h'
        · exfalso; linarith [norm_nonneg (α x : EuclideanSpace ℝ (Fin n))]
      exact mem_sphere_closedBall_of_norm_eq_one (α x) hnorm
    · intro h
      have hnorm : ‖(α x : EuclideanSpace ℝ (Fin n))‖ = 1 :=
        norm_eq_one_of_mem_sphere_closedBall (α x) ((hα x).mp h)
      rw [hnorm]; ring
  have hB_zero : ∀ x : B, lastCoord n (f (x : X)) = 0 ↔ (x : X) ∈ A := by
    intro x
    rw [hfB x, lastCoord_downMap, neg_eq_zero]
    have hnn : 0 ≤ 1 - ‖(C (β x) : EuclideanSpace ℝ (Fin n))‖ ^ 2 :=
      by nlinarith [norm_nonneg (C (β x) : EuclideanSpace ℝ (Fin n)),
        norm_le_one_of_mem_closedBall (C (β x)).2]
    rw [Real.sqrt_eq_zero hnn]
    constructor
    · intro h
      refine (hβ x).mpr ?_
      have hC1 : ‖(C (β x) : EuclideanSpace ℝ (Fin n))‖ = 1 := by
        rcases sq_eq_one_iff.mp (by linarith :
          ‖(C (β x) : EuclideanSpace ℝ (Fin n))‖ ^ 2 = 1) with h' | h'
        · exact h'
        · exfalso; linarith [norm_nonneg (C (β x) : EuclideanSpace ℝ (Fin n))]
      exact mem_sphere_closedBall_of_norm_eq_one (β x) (by rw [← hCnorm (β x), hC1])
    · intro h
      have hnorm : ‖(β x : EuclideanSpace ℝ (Fin n))‖ = 1 :=
        norm_eq_one_of_mem_sphere_closedBall (β x) ((hβ x).mp h)
      rw [hCnorm (β x), hnorm]; ring
  -- injectivity on each half
  have hinjA : ∀ x y : A, f (x : X) = f (y : X) → x = y := by
    intro x y hxy
    have h1 : upMap (α x) = upMap (α y) := by rw [← hfA x, ← hfA y, hxy]
    exact α.injective (upMap_injective h1)
  have hinjB : ∀ x y : B, f (x : X) = f (y : X) → x = y := by
    intro x y hxy
    have h1 : downMap (C (β x)) = downMap (C (β y)) := by rw [← hfB x, ← hfB y, hxy]
    exact β.injective (C.injective (downMap_injective h1))
  -- global injectivity
  have hinj : Function.Injective f := by
    intro x y hxy
    by_cases hxA : x ∈ A
    · by_cases hyA : y ∈ A
      · exact congrArg Subtype.val (hinjA ⟨x, hxA⟩ ⟨y, hyA⟩ hxy)
      · have hyB : y ∈ B := mem_of_not_mem_of_union_eq_univ hAB hyA
        have hxB : x ∈ B := by
          have h1 : lastCoord n (f x) = lastCoord n (f y) := by rw [hxy]
          have h2 : 0 ≤ lastCoord n (f x) := hA_nonneg ⟨x, hxA⟩
          have h3 : lastCoord n (f y) ≤ 0 := hB_nonpos ⟨y, hyB⟩
          exact (hA_zero ⟨x, hxA⟩).mp (le_antisymm (h1 ▸ h3) h2)
        exact congrArg Subtype.val (hinjB ⟨x, hxB⟩ ⟨y, hyB⟩ hxy)
    · have hxB : x ∈ B := mem_of_not_mem_of_union_eq_univ hAB hxA
      by_cases hyA : y ∈ A
      · have hyB : y ∈ B := by
          have h1 : lastCoord n (f y) = lastCoord n (f x) := by rw [hxy]
          have h2 : 0 ≤ lastCoord n (f y) := hA_nonneg ⟨y, hyA⟩
          have h3 : lastCoord n (f x) ≤ 0 := hB_nonpos ⟨x, hxB⟩
          exact (hA_zero ⟨y, hyA⟩).mp (le_antisymm (h1 ▸ h3) h2)
        exact congrArg Subtype.val (hinjB ⟨x, hxB⟩ ⟨y, hyB⟩ hxy)
      · exact congrArg Subtype.val
          (hinjB ⟨x, hxB⟩ ⟨y, mem_of_not_mem_of_union_eq_univ hAB hyA⟩ hxy)
  -- surjectivity
  have hsurj : Function.Surjective f := by
    intro z
    rcases le_total (lastCoord n z) 0 with hz | hz
    · obtain ⟨w, hw⟩ := mem_range_downMap (z := z) hz
      obtain ⟨v, hv⟩ := C.surjective w
      refine ⟨((β.symm v : B) : X), ?_⟩
      rw [hfB (β.symm v), Homeomorph.apply_symm_apply, hv]
      exact hw
    · obtain ⟨y, hy⟩ := mem_range_upMap (z := z) hz
      refine ⟨((α.symm y : A) : X), ?_⟩
      rw [hfA (α.symm y), Homeomorph.apply_symm_apply]
      exact hy
  -- continuity
  have hcontA : ContinuousOn f A := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hfun : A.domRestrict f = fun x : A => upMap (α x) := by funext x; exact hfA x
    rw [hfun]
    exact continuous_upMap.comp α.continuous
  have hcontB : ContinuousOn f B := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hfun : B.domRestrict f = fun x : B => downMap (C (β x)) := by funext x; exact hfB x
    rw [hfun]
    exact continuous_downMap.comp (C.continuous.comp β.continuous)
  have hcont : Continuous f := by
    have h1 : ContinuousOn f (A ∪ B) := ContinuousOn.union_of_isClosed hcontA hcontB hA hB
    rw [hAB] at h1
    exact continuousOn_univ.mp h1
  exact ⟨Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective f ⟨hinj, hsurj⟩) hcont⟩

end Work.Morse
