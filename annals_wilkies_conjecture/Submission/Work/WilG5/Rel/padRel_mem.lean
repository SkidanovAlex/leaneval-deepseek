import Mathlib
import Submission.Work.WilG5.Defs

namespace Work.WilG5.Rel

open WilkiesDesign WilkiesConjecture

/-- Reading a point of `ℝ^{μ+n}` off the coordinate map that `padRel` uses: the `d` source
coordinates are the first `d` coordinates of the ambient point and the `n` value coordinates
are the last `n`.  The middle `μ - d` coordinates are ignored, which is exactly the
"padding" of the source cube. -/
def padRelIdx {d n μ : ℕ} (h : d ≤ μ) : Fin (d + n) → Fin (μ + n) :=
  Fin.append (fun i : Fin d => Fin.castAdd n (Fin.castLE h i))
    (fun j : Fin n => Fin.natAdd μ j)

theorem padRelIdx_castAdd {d n μ : ℕ} (h : d ≤ μ) (i : Fin d) :
    padRelIdx h (Fin.castAdd n i) = Fin.castAdd n (Fin.castLE h i) := by
  unfold padRelIdx
  rw [Fin.append_left]

theorem padRelIdx_natAdd {d n μ : ℕ} (h : d ≤ μ) (j : Fin n) :
    padRelIdx h (Fin.natAdd d j) = Fin.natAdd μ j := by
  unfold padRelIdx
  rw [Fin.append_right]

/-- `padRel` is the preimage of `R` under the coordinate map `z ↦ z ∘ padRelIdx`. -/
theorem padRelIdx_comp {d n μ : ℕ} (h : d ≤ μ) (z : Fin (μ + n) → ℝ) :
    (fun k : Fin (d + n) => z (padRelIdx h k)) =
      Fin.append (fun i : Fin d => z (Fin.castAdd n (Fin.castLE h i)))
        (fun j : Fin n => z (Fin.natAdd μ j)) := by
  rw [← append_self (fun k : Fin (d + n) => z (padRelIdx h k))]
  congr 1
  · funext i
    rw [padRelIdx_castAdd]
  · funext j
    rw [padRelIdx_natAdd]

theorem padRel_eq_coordPre {d n μ : ℕ} (h : d ≤ μ) (R : Set (Fin (d + n) → ℝ)) :
    padRel h R = coordPre (padRelIdx h) R := by
  ext z
  show (Fin.append (fun i : Fin d => z (Fin.castAdd n (Fin.castLE h i)))
      (fun j : Fin n => z (Fin.natAdd μ j)) ∈ R) ↔ (z ∘ padRelIdx h) ∈ R
  rw [show z ∘ padRelIdx h = Fin.append (fun i : Fin d => z (Fin.castAdd n (Fin.castLE h i)))
      (fun j : Fin n => z (Fin.natAdd μ j)) from padRelIdx_comp h z]

theorem padRel_mem (S : WilkiesDesign.SOMin) {d n μ : ℕ} (h : d ≤ μ) :
    ∃ (A L : ℕ), ∀ (A₀ B : ℕ) (R : Set (Fin (d + n) → ℝ)), R ∈ S.Ω A₀ B (d + n) →
      Work.WilG5.padRel h R ∈ S.Ω (A + A₀) (B + L) (μ + n) := by
  refine ⟨64 * ((μ + n) + (d + n)) + 64, 32 * ((μ + n) + (d + n)) + 32, ?_⟩
  intro A₀ B R hR
  have hcoord := coordPre_mem (S := S) (ι := padRelIdx h) (A := R) hR
  rw [padRel_eq_coordPre h R]
  exact mem_mono hcoord _ _ (by omega) (by omega)

end Work.WilG5.Rel
