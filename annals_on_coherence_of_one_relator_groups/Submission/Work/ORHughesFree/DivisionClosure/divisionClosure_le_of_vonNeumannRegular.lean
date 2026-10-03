import Mathlib
import Submission.Work.ORHughesFree.DivisionClosure
import Submission.Work.ORHughesFree.StarRegular

namespace Work.ORHughesFree.DivisionClosure

open Work.ORHughesFree

/-- In a von Neumann regular ring, the two-sided inverse (in an ambient ring) of an element is
already an element of the ring: if `x ∈ U`, `x * y = 1` and `y * x = 1` in `S`, and `U` is von
Neumann regular, then `y ∈ U`. -/
theorem mem_of_mul_eq_one_of_vonNeumannRegular {S : Type*} [Ring S] {U : Subring S}
    [VonNeumannRegularRing U] {x y : S} (hx : x ∈ U) (hxy : x * y = 1) (hyx : y * x = 1) :
    y ∈ U := by
  obtain ⟨z, hz⟩ := VonNeumannRegularRing.exists_mul_inverse (⟨x, hx⟩ : U)
  have hzS : x * (z : S) * x = x := by
    have h := congrArg (fun w : U => (w : S)) hz
    simpa using h
  have h1 : (z : S) * x = 1 := by
    have h : y * (x * (z : S) * x) = 1 := by rw [hzS, hyx]
    calc (z : S) * x = (y * x) * ((z : S) * x) := by rw [hyx, one_mul]
      _ = y * (x * (z : S) * x) := by noncomm_ring
      _ = 1 := h
  have h2 : (z : S) = y := by
    calc (z : S) = (z : S) * (x * y) := by rw [hxy, mul_one]
      _ = ((z : S) * x) * y := by rw [mul_assoc]
      _ = y := by rw [h1, one_mul]
  rw [← h2]
  exact z.2

/-- Every approximating subring `Qₙ` of the division closure of `R` is contained in any von Neumann
regular subring containing `R`. -/
theorem divisionClosureChain_le {S : Type*} [Ring S] {R : Set S} {U : Subring S}
    [VonNeumannRegularRing U] (hR : R ⊆ (U : Set S)) (n : ℕ) :
    divisionClosureChain R n ≤ U := by
  induction n with
  | zero => exact Subring.closure_le.mpr hR
  | succ n ih =>
    apply Subring.closure_le.mpr
    intro y hy
    rcases hy with hy | ⟨x, hx, hxy, hyx⟩
    · exact ih hy
    · exact mem_of_mul_eq_one_of_vonNeumannRegular (ih hx) hxy hyx

/-- The division closure of a subset `R` of a ring `S` is contained in any von Neumann regular
subring of `S` that contains `R`. -/
theorem divisionClosure_le_of_vonNeumannRegular {S : Type*} [Ring S] {R : Set S}
    {U : Subring S} [VonNeumannRegularRing U] (hR : R ⊆ (U : Set S)) :
    (divisionClosure R : Set S) ⊆ (U : Set S) := by
  rw [divisionClosure]
  exact iSup_le (fun n => divisionClosureChain_le hR n)

end Work.ORHughesFree.DivisionClosure
