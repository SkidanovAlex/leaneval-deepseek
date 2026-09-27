import Mathlib
import Submission.Work.EKLC6Core.ae_forall_smul_mem
import Submission.Work.EKLC6Core.radius_independence

namespace Work.EKLC6Core

open MeasureTheory

/-- **Countable intersections of conull sets along the orbit of a single diagonal flow.**

If the single map `x ↦ aDiag t • x` preserves `μ` and `X'`, `X''` are conull, then for a.e. `x`
and every `j : ℕ` the point `aDiag (j • t) • x` lies in `X' ∩ X''`.

The point is that `aDiag (j • t) = (aDiag t)^j`: `aDiag` is a homomorphism
(`Work.EKLContract.aDiag_add`, `aDiag_zero`), so the `j`-fold iterate of the measure-preserving
map `x ↦ aDiag t • x` is `x ↦ aDiag (j • t) • x`, hence also measure preserving
(`MeasurePreserving.iterate`).  Each of the countably many bad preimages is therefore null. -/
theorem ae_forall_smul_mem_mp {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ]
    {t : Fin 3 → ℝ}
    (hmp : MeasureTheory.MeasurePreserving
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) μ μ)
    {X' X'' : Set Work.EKLContract.X3} (hX' : μ X'ᶜ = 0) (hX'' : μ X''ᶜ = 0) :
    ∀ᵐ x ∂μ, ∀ j : ℕ, Work.EKLContract.aDiag ((j : ℝ) • t) • x ∈ X' ∩ X'' := by
  -- `X' ∩ X''` is conull.
  have hS : μ (X' ∩ X'')ᶜ = 0 := by
    rw [Set.compl_inter]
    exact MeasureTheory.measure_union_null hX' hX''
  -- The `j`-th iterate of `x ↦ aDiag t • x` is `x ↦ aDiag (j • t) • x`.
  have hiter : ∀ j : ℕ, ∀ x : Work.EKLContract.X3,
      Work.EKLContract.aDiag ((j : ℝ) • t) • x
        = (fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y)^[j] x := by
    intro j
    induction j with
    | zero =>
      intro x
      rw [Nat.cast_zero, zero_smul, Function.iterate_zero_apply]
      rw [Work.EKLContract.aDiag_zero, one_smul]
    | succ k ih =>
      intro x
      rw [Function.iterate_succ_apply']
      rw [← ih x]
      rw [Work.EKLContract.aDiag_smul_mul]
      have hv : t + (k : ℝ) • t = ((k + 1 : ℕ) : ℝ) • t := by
        funext i
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        push_cast
        ring
      rw [hv]
  have hiterfun : ∀ j : ℕ,
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag ((j : ℝ) • t) • x)
        = (fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y)^[j] :=
    fun j => funext (hiter j)
  -- The bad event is a countable union of preimages of the null set `(X' ∩ X'')ᶜ`.
  rw [MeasureTheory.ae_iff]
  have hset : {x : Work.EKLContract.X3 |
        ¬ (∀ j : ℕ, Work.EKLContract.aDiag ((j : ℝ) • t) • x ∈ X' ∩ X'')}
      = ⋃ j : ℕ,
          (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag ((j : ℝ) • t) • x) ⁻¹'
            (X' ∩ X'')ᶜ := by
    ext x
    simp [Set.mem_iUnion]
  rw [hset]
  refine MeasureTheory.measure_iUnion_null (fun j => ?_)
  rw [hiterfun j]
  exact (hmp.iterate j).preimage_null hS

end Work.EKLC6Core
