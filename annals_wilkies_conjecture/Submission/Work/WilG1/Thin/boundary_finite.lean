import Mathlib
import Submission.Work.WilG1.Basic
import Submission.Work.WilG1.OneDim.interval_cover_of_omega
import Submission.Work.WilG1.Thin.frontier_isPreconnected_finite

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG1.Thin

/-- The canonical homeomorphism `ℝ ≃ₜ (Fin 1 → ℝ)`, `x ↦ (fun _ => x)`. -/
def liftHomeo : ℝ ≃ₜ (Fin 1 → ℝ) where
  toFun x := fun _ => x
  invFun y := y 0
  left_inv x := rfl
  right_inv y := by
    funext i
    exact (congrArg y (Fin.eq_zero i)).symm
  continuous_toFun := continuous_pi fun _ => continuous_id
  continuous_invFun := continuous_apply 0

/-- The topological boundary of a one-dimensional `Ω`-set is finite.  Indeed `S.comps` writes
`A` as a finite union of preconnected sets, and a preconnected subset of `ℝ` is an interval,
whose frontier has at most two points; the frontier of a finite union is contained in the
union of the frontiers. -/
theorem boundary_finite {S : WilkiesDesign.SOMin} {a b : ℕ} {A : Set (Fin 1 → ℝ)}
    (hA : A ∈ S.Ω a b 1) :
    ({x : ℝ | (fun _ : Fin 1 => x) ∈ closure A ∧ (fun _ : Fin 1 => x) ∈ closure Aᶜ}).Finite := by
  classical
  obtain ⟨p, hp⟩ := Work.WilG1.OneDim.interval_cover_of_omega (S := S) (a := a)
  have hA' : A ∈ S.Ω a ((Polynomial.C b : Polynomial ℕ).eval 0) 1 := by simpa using hA
  obtain ⟨s, hs⟩ := hp (D := 0) (b := (Polynomial.C b : Polynomial ℕ)) hA'
  obtain ⟨hpre, hset⟩ := hs.2
  have hfront : ({x : ℝ | (fun _ : Fin 1 => x) ∈ closure A ∧ (fun _ : Fin 1 => x) ∈ closure Aᶜ})
      = frontier {x : ℝ | (fun _ : Fin 1 => x) ∈ A} := by
    have hL : {x : ℝ | (fun _ : Fin 1 => x) ∈ closure A ∧ (fun _ : Fin 1 => x) ∈ closure Aᶜ}
        = liftHomeo ⁻¹' frontier A := by
      rw [frontier_eq_closure_inter_closure, Set.preimage_inter]
      rfl
    have hR : frontier {x : ℝ | (fun _ : Fin 1 => x) ∈ A} = frontier (liftHomeo ⁻¹' A) := rfl
    rw [hL, hR, ← Homeomorph.preimage_frontier]
  rw [hfront, hset, Set.sUnion_eq_biUnion]
  have hbig : (⋃ i ∈ (s : Set (Set ℝ)), frontier i).Finite :=
    Set.Finite.biUnion (Finset.finite_toSet s)
      (fun I hI => frontier_isPreconnected_finite (hpre I hI))
  exact Set.Finite.subset hbig (Finset.frontier_biUnion_subset s (fun I : Set ℝ => I))

end Work.WilG1.Thin
