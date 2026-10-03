import Mathlib
import Submission.Work.ORLyndon.Fox

namespace Work.ORLyndon

/-- Let `φ : G →* Multiplicative ℤ` be a "degree" homomorphism.  If
`s` is a finite family of group elements whose `φ`-degrees are all `≤` the degree of a
distinguished element `g i₀`, with uniqueness of the maximal degree, then the group-algebra
element `∑ i ∈ s, ε i • of (g i)` (with `ε i₀ ≠ 0`) is right regular: it is not a left
zero-divisor.  The proof extracts the coefficient at the top degree via
`MonoidAlgebra.coeff_mul_mul_of_uniqueMul`. -/
theorem signedSum_regular {G : Type*} [Group G] {K : Type*} [Field K]
    (φ : G →* Multiplicative ℤ) {ι : Type*} (s : Finset ι) (g : ι → G) (ε : ι → K) (i₀ : ι)
    (hi₀ : i₀ ∈ s) (hε : ε i₀ ≠ 0)
    (hle : ∀ i ∈ s, Multiplicative.toAdd (φ (g i)) ≤ Multiplicative.toAdd (φ (g i₀)))
    (huniq : ∀ i ∈ s, Multiplicative.toAdd (φ (g i)) = Multiplicative.toAdd (φ (g i₀)) → i = i₀) :
    ∀ b : MonoidAlgebra K G, b * (∑ i ∈ s, ε i • MonoidAlgebra.of K G (g i)) = 0 → b = 0 := by
  intro b hb
  by_contra hbne
  classical
  set a : MonoidAlgebra K G := ∑ i ∈ s, ε i • MonoidAlgebra.of K G (g i) with ha
  have hterm : ∀ i, MonoidAlgebra.coeff (ε i • MonoidAlgebra.of K G (g i)) =
      Finsupp.single (g i) (ε i) := by
    intro i
    rw [MonoidAlgebra.coeff_smul, MonoidAlgebra.of_apply, MonoidAlgebra.coeff_single,
      Finsupp.smul_single', mul_one]
  have hacoeff : a.coeff = ∑ i ∈ s, Finsupp.single (g i) (ε i) := by
    rw [ha, MonoidAlgebra.coeff_sum]
    exact Finset.sum_congr rfl (fun i _ => hterm i)
  have hbne' : b.coeff ≠ 0 := fun h => hbne (MonoidAlgebra.coeff_eq_zero.mp h)
  have hsupp : b.coeff.support.Nonempty := Finsupp.support_nonempty_iff.mpr hbne'
  obtain ⟨y₀, hy₀, hy₀max⟩ :=
    Finset.exists_max_image b.coeff.support (fun y => Multiplicative.toAdd (φ y)) hsupp
  have hzex : ∀ z ∈ a.coeff.support, ∃ i ∈ s, g i = z := by
    intro z hz
    by_contra h
    have h' : ∀ i, i ∈ s → g i ≠ z := fun i hi hgi => h ⟨i, hi, hgi⟩
    have hmem : z ∈ (∑ i ∈ s, Finsupp.single (g i) (ε i)).support := by rwa [← hacoeff]
    rw [Finsupp.mem_support_iff, Finsupp.finsetSum_apply] at hmem
    refine hmem (Finset.sum_eq_zero (fun i hi => ?_))
    exact Finsupp.single_eq_of_ne (h' i hi).symm
  have hacoef0 : a.coeff (g i₀) = ε i₀ := by
    rw [hacoeff, Finsupp.finsetSum_apply]
    rw [Finset.sum_eq_single_of_mem
      (f := fun i => (Finsupp.single (g i) (ε i)) (g i₀)) i₀ hi₀ ?_]
    · exact Finsupp.single_eq_same
    · intro i hi hne
      exact Finsupp.single_eq_of_ne (fun hgi => hne (huniq i hi (by rw [hgi])))
  have huni : UniqueMul b.coeff.support a.coeff.support y₀ (g i₀) := by
    intro x z hx hz hxz
    have hxle : Multiplicative.toAdd (φ x) ≤ Multiplicative.toAdd (φ y₀) := hy₀max x hx
    obtain ⟨i, hi, hgi⟩ := hzex z hz
    have hzle : Multiplicative.toAdd (φ z) ≤ Multiplicative.toAdd (φ (g i₀)) := by
      rw [← hgi]; exact hle i hi
    have h1 : Multiplicative.toAdd (φ x) + Multiplicative.toAdd (φ z)
        = Multiplicative.toAdd (φ y₀) + Multiplicative.toAdd (φ (g i₀)) := by
      have := congrArg (fun w => Multiplicative.toAdd (φ w)) hxz
      simpa only [map_mul, toAdd_mul] using this
    have hzEq : Multiplicative.toAdd (φ z) = Multiplicative.toAdd (φ (g i₀)) := by linarith
    have hxEq : Multiplicative.toAdd (φ x) = Multiplicative.toAdd (φ y₀) := by linarith
    have hz0 : z = g i₀ := by
      have hii : i = i₀ := huniq i hi (by rw [hgi]; exact hzEq)
      rw [← hgi, hii]
    have hx0 : x = y₀ := by
      have hzz : x * z = y₀ * z := by rw [hxz, hz0]
      exact mul_right_cancel hzz
    exact ⟨hx0, hz0⟩
  have hcoeff : (b * a).coeff (y₀ * g i₀) = b.coeff y₀ * ε i₀ := by
    rw [MonoidAlgebra.coeff_mul_mul_of_uniqueMul huni, hacoef0]
  have hne : (b * a).coeff (y₀ * g i₀) ≠ 0 := by
    rw [hcoeff]
    exact mul_ne_zero (Finsupp.mem_support_iff.mp hy₀) hε
  exact hne (by rw [hb]; rfl)

end Work.ORLyndon
