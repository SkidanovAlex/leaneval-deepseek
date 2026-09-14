import Mathlib
import Submission.Subspace.RealRank.Containment
open Matrix
open scoped BigOperators

namespace Submission.Subspace.RealRank

variable {N : ℕ}

/-- The box of the compound system (a set of integer vectors indexed by `Idx N r`). -/
def compBox (r : ℕ) (M : Matrix (Fin N) (Fin N) ℝ) (xbar : Idx N r → ℝ) (Q : ℝ) :
    Set (Idx N r → ℤ) :=
  {y | ∀ i, |∑ j : Idx N r, (Commons.LinearAlgebra.Matrix.compound r M) i j * (y j : ℝ)|
    ≤ Q ^ (xbar i)}

/-- **The wedge vectors of a compound box are independent, so its rank is `≥ N' - 1`.** -/
theorem rankBox_compound_ge {N r : ℕ} (M : Matrix (Fin N) (Fin N) ℝ)
    (V : Matrix (Fin N) (Fin N) ℤ) (xbar : Idx N r → ℝ) {Q : ℝ} (Tstar : Idx N r)
    (hmem : ∀ S : Idx N r, S ≠ Tstar → (fun S' => (Commons.LinearAlgebra.Matrix.compound r V) S' S)
      ∈ compBox r M xbar Q)
    (hli : LinearIndependent ℚ (fun S : Idx N r =>
      fun S' : Idx N r => ((Commons.LinearAlgebra.Matrix.compound r V) S' S : ℚ))) :
    Fintype.card {S : Idx N r // S ≠ Tstar} ≤ Module.finrank ℚ (Submodule.span ℚ
      (Set.image (fun y : Idx N r → ℤ => fun k => (y k : ℚ)) (compBox r M xbar Q))) := by
  classical
  set b : Idx N r → Idx N r → ℚ :=
    fun S S' => ((Commons.LinearAlgebra.Matrix.compound r V) S' S : ℚ) with hb
  have hli' : LinearIndependent ℚ b := hli
  have hsub : LinearIndependent ℚ (fun S : {S : Idx N r // S ≠ Tstar} => b (S : Idx N r)) := by
    have h := hli'.comp (Subtype.val : {S : Idx N r // S ≠ Tstar} → Idx N r)
      Subtype.coe_injective
    simpa only [Function.comp_def, hb] using h
  have hspan : Submodule.span ℚ (Set.range (fun S : {S : Idx N r // S ≠ Tstar} =>
        b (S : Idx N r))) ≤
      Submodule.span ℚ (Set.image (fun y : Idx N r → ℤ => fun k => (y k : ℚ))
        (compBox r M xbar Q)) := by
    rw [Submodule.span_le]
    rintro v ⟨S, rfl⟩
    refine Submodule.subset_span ⟨(fun S' => (Commons.LinearAlgebra.Matrix.compound r V) S' (S : Idx N r)),
      hmem (S : Idx N r) S.2, ?_⟩
    funext k
    simp [hb]
  have h1 : Module.finrank ℚ (Submodule.span ℚ
      (Set.range (fun S : {S : Idx N r // S ≠ Tstar} => b (S : Idx N r))))
      = Fintype.card {S : Idx N r // S ≠ Tstar} := finrank_span_eq_card hsub
  calc Fintype.card {S : Idx N r // S ≠ Tstar}
      = Module.finrank ℚ (Submodule.span ℚ (Set.range (fun S : {S : Idx N r // S ≠ Tstar} =>
          b (S : Idx N r)))) := h1.symm
    _ ≤ Module.finrank ℚ (Submodule.span ℚ (Set.image (fun y : Idx N r → ℤ => fun k => (y k : ℚ))
          (compBox r M xbar Q))) := Submodule.finrank_mono hspan

end Submission.Subspace.RealRank
