import Mathlib
import Submission.Work.WilG4c.ChartRescaleDefs
import Submission.Work.WilG5.Basic

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign

/-- The trailing block of the glued point `Fin.append z y` is `y`. -/
theorem append_natAdd_eq (m : ℕ) (z y : Fin (m + 1) → ℝ) :
    (fun i : Fin (m + 1) => Fin.append z y (Fin.natAdd (m + 1) i)) = y :=
  funext fun i => Fin.append_right z y i

/-- Membership in a graph, unfolded. -/
theorem mem_graphOf_iff {n : ℕ} (f : (Fin n → ℝ) → ℝ) (z : Fin (n + 1) → ℝ) :
    z ∈ WilkiesDesign.graphOf f ↔ z (Fin.last n) = f (Fin.init z) := Iff.rfl

/-- **The projection of the rescaled chart is the graph of the rescaled function.**
Projecting the `crSet` of the graph of `f` (the sum-of-squares relation `crQ` identifying the
argument coordinates and imposing `z (last m) = c + u (last m)/K` between the new point `z` and
the old point `u`) away from the old block gives exactly the graph of `u ↦ c + f u / K`. -/
theorem CrProjEq (m K : ℕ) (c : ℝ) (f : (Fin m → ℝ) → ℝ) :
    Work.WilG5.projN (m + 1) (Work.WilG4c.crSet m K c (WilkiesDesign.graphOf f)) =
      WilkiesDesign.graphOf (fun u => c + f u / (K : ℝ)) := by
  ext z
  constructor
  · intro hz
    simp only [Work.WilG5.projN, crSet, Set.mem_ofPred_eq] at hz
    obtain ⟨y, hy, hq⟩ := hz
    have hyl : y ∈ WilkiesDesign.graphOf f := by
      simpa only [append_natAdd_eq m z y] using hy
    have hyv : y (Fin.last m) = f (Fin.init y) := hyl
    have hq2 := (CrQ_eval_eq_zero_iff m K c z y).mp hq
    have hiny : Fin.init y = Fin.init z := funext fun i => hq2.1 i
    show z (Fin.last m) = c + f (Fin.init z) / (K : ℝ)
    rw [hq2.2, hyv, hiny]
  · intro hz
    have hz' : z (Fin.last m) = c + f (Fin.init z) / (K : ℝ) := hz
    set y : Fin (m + 1) → ℝ := Fin.snoc (Fin.init z) (f (Fin.init z)) with hydef
    refine ⟨y, ?_, ?_⟩
    · rw [append_natAdd_eq m z y]
      show y (Fin.last m) = f (Fin.init y)
      rw [hydef, Fin.snoc_last, Fin.init_snoc]
    · refine (CrQ_eval_eq_zero_iff m K c z y).mpr ⟨?_, ?_⟩
      · intro i
        show y (Fin.castSucc i) = z (Fin.castSucc i)
        rw [hydef, Fin.snoc_castSucc]
        rfl
      · show z (Fin.last m) = c + y (Fin.last m) / (K : ℝ)
        rw [hydef, Fin.snoc_last]
        exact hz'

end Work.WilG4c
