import Mathlib
import Submission.Work.BW.basisRed_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open scoped Matrix

/-- For each `i`, the `i`-th component of the image `A v` of a lattice point `v` of `wNorm`-norm
at most `t` is bounded by `t / c i`. -/
theorem wNorm_apply_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (c : Fin n → ℝ)
    (hc : ∀ i, 0 < c i) (t : ℝ) (v : Fin n → ℤ)
    (hv : wNorm A c (fun i => (v i : ℝ)) ≤ t) (i : Fin n) :
    |(((A.mulVec v) i : ℤ) : ℝ)| ≤ t / c i := by
  have hcast : (A.map (Int.castRingHom ℝ)).mulVec (fun j => (v j : ℝ))
      = fun j => (((A.mulVec v) j : ℤ) : ℝ) := by
    ext j
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
    push_cast
    rfl
  have hsingle := Finset.single_le_sum
    (f := fun j => c j * |(A.map (Int.castRingHom ℝ)).mulVec (fun k => (v k : ℝ)) j|)
    (s := Finset.univ)
    (fun j _ => mul_nonneg (le_of_lt (hc j)) (abs_nonneg _)) (Finset.mem_univ i)
  have hterm : c i * |(A.map (Int.castRingHom ℝ)).mulVec (fun k => (v k : ℝ)) i| ≤
      wNorm A c (fun j => (v j : ℝ)) := by
    simpa [wNorm] using hsingle
  rw [hcast] at hterm
  rw [le_div_iff₀ (hc i)]
  calc |(((A.mulVec v) i : ℤ) : ℝ)| * c i
      = c i * |(((A.mulVec v) i : ℤ) : ℝ)| := mul_comm _ _
    _ ≤ t := le_trans hterm hv

/-- The integer vectors all of whose components are bounded by the prescribed bounds form a
finite set. -/
theorem finite_int_vectors_bound {n : ℕ} (b : Fin n → ℝ) :
    {w : Fin n → ℤ | ∀ i, |(((w i : ℤ) : ℝ))| ≤ b i}.Finite := by
  have hfin : ∀ i, {z : ℤ | |((z : ℝ))| ≤ b i}.Finite := by
    intro i
    refine Set.Finite.subset (Set.finite_Icc (-⌈b i⌉) ⌈b i⌉) ?_
    intro z hz
    refine ⟨?_, ?_⟩
    · have h1 : ((-z : ℤ) : ℝ) ≤ (⌈b i⌉ : ℝ) := by
        push_cast
        exact le_trans (neg_le_abs (z : ℝ)) (le_trans hz (Int.le_ceil _))
      have h2 : -z ≤ ⌈b i⌉ := Int.cast_le.mp h1
      linarith
    · have h1 : (z : ℝ) ≤ (⌈b i⌉ : ℝ) :=
        le_trans (le_abs_self (z : ℝ)) (le_trans hz (Int.le_ceil _))
      exact Int.cast_le.mp h1
  have hpi := Set.Finite.pi (fun i => hfin i)
  refine hpi.subset ?_
  intro w hw i _
  exact hw i

theorem wNorm_finite {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (hA : A.det ≠ 0) (c : Fin n → ℝ) (hc : ∀ i, 0 < c i) (t : ℝ) : {v : Fin n → ℤ | Work.BW.wNorm A c (fun i => (v i : ℝ)) ≤ t}.Finite := by
  have hinj : Function.Injective (fun v : Fin n → ℤ => A.mulVec v) :=
    Matrix.mulVec_injective_of_det_ne_zero hA
  have hTfin : {w : Fin n → ℤ | ∀ i, |(((w i : ℤ) : ℝ))| ≤ t / c i}.Finite :=
    finite_int_vectors_bound (fun i => t / c i)
  have hpre : ((fun v : Fin n → ℤ => A.mulVec v) ⁻¹'
      {w : Fin n → ℤ | ∀ i, |(((w i : ℤ) : ℝ))| ≤ t / c i}).Finite :=
    hTfin.preimage (fun _ _ _ _ hxy => hinj hxy)
  refine hpre.subset ?_
  intro v hv
  exact wNorm_apply_le A c hc t v hv

end Work.BW
