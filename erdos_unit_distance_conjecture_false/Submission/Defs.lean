import ChallengeDeps
import Submission.Work.Interface.All

/-!
# The final bridge to the challenge statement

`Work.Interface.construction` builds planar point sets inside `ℂ`; the challenge statement is
about `EuclideanSpace ℝ (Fin 2)`. This file provides the isometric transfer.
-/

open MeasureTheory
open NumberField
open LeanEval.Combinatorics
open scoped Classical nonZeroDivisors

namespace Submission

/-- The isometric model of the plane as `ℂ`. -/
noncomputable abbrev planeIso : ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) :=
  Complex.orthonormalBasisOneI.repr

/-- The unit-distance count in `ℂ` agrees with `unitDist` under the isometry `ℂ ≃ ℝ²`. -/
theorem unitDist_image (P : Finset ℂ) :
    unitDist (P.image (planeIso : ℂ → EuclideanSpace ℝ (Fin 2))) = Work.Defs.cDist P := by
  classical
  set e : ℂ → EuclideanSpace ℝ (Fin 2) := fun z => planeIso z with he
  have hinj : Function.Injective e := fun z w h => planeIso.injective h
  have hdist : ∀ z w : ℂ, dist (e z) (e w) = ‖z - w‖ := by
    intro z w
    rw [he, planeIso.dist_map, dist_eq_norm]
  rw [Work.Defs.cDist, unitDist]
  congr 1
  symm
  refine Finset.card_bij (fun (pq : ℂ × ℂ) _ => (e pq.1, e pq.2)) ?_ ?_ ?_
  · rintro ⟨a, b⟩ h
    rw [Finset.mem_filter] at h ⊢
    obtain ⟨hoff, hd⟩ := h
    rw [Finset.mem_offDiag] at hoff ⊢
    obtain ⟨ha, hb, hab⟩ := hoff
    exact ⟨⟨Finset.mem_image.mpr ⟨a, ha, rfl⟩, Finset.mem_image.mpr ⟨b, hb, rfl⟩,
      fun hc => hab (hinj hc)⟩, by rw [hdist]; exact hd⟩
  · rintro ⟨a, b⟩ _ ⟨a', b'⟩ _ h
    exact Prod.ext (hinj (congrArg Prod.fst h)) (hinj (congrArg Prod.snd h))
  · rintro ⟨u, v⟩ h
    rw [Finset.mem_filter, Finset.mem_offDiag] at h
    obtain ⟨⟨hu, hv, huv⟩, hd⟩ := h
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hv
    refine ⟨(a, b), ?_, rfl⟩
    rw [Finset.mem_filter, Finset.mem_offDiag]
    refine ⟨⟨ha, hb, ?_⟩, ?_⟩
    · simp only [Prod.fst, Prod.snd] at huv ⊢
      intro hab
      exact huv (by rw [hab])
    · rw [← hdist a b]
      simp only [Prod.fst, Prod.snd] at hd ⊢
      exact hd

end Submission
