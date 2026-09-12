import Mathlib
import Submission.Commons.Algebra.MvPolynomial.exists_harmonic_orthonormal_basis
import Submission.Commons.Algebra.MvPolynomial.homogeneous_decompose
import Submission.Commons.Algebra.MvPolynomial.harmonic_X2_intersection
import Submission.Commons.Algebra.MvPolynomial.X2_mul_left_cancel
import Submission.Commons.Algebra.MvPolynomial.homogeneousSubmodule_finiteDimensional

namespace Commons.Algebra.MvPolynomial

set_option linter.style.haveILetI false

open scoped BigOperators

/-- The squared norm `∑ⱼ Xⱼ²` in `n` variables. -/
private noncomputable abbrev normSq (n : ℕ) : MvPolynomial (Fin n) ℝ := ∑ j : Fin n, (MvPolynomial.X j)^2

private lemma normSq_isHomogeneous (n : ℕ) : (normSq n).IsHomogeneous 2 := by
  unfold normSq
  refine MvPolynomial.IsHomogeneous.sum Finset.univ
    (fun j : Fin n => (MvPolynomial.X j)^2) 2 (fun j _ => ?_)
  simpa using (MvPolynomial.isHomogeneous_X (R := ℝ) (σ := Fin n) j).pow 2

theorem finrank_harmHom_add (n k : ℕ) [Nonempty (Fin n)] (hk : 2 ≤ k) :
    Module.finrank ℝ (Commons.Algebra.MvPolynomial.harmHom n k)
      + Module.finrank ℝ (MvPolynomial.homogeneousSubmodule (Fin n) ℝ (k - 2))
      = Module.finrank ℝ (MvPolynomial.homogeneousSubmodule (Fin n) ℝ k) := by
  classical
  have hk2 : 2 + (k - 2) = k := by omega
  -- The domain and the map "multiplication by `∑ Xⱼ²`".
  let Vk := MvPolynomial.homogeneousSubmodule (Fin n) ℝ k
  let Vm := MvPolynomial.homogeneousSubmodule (Fin n) ℝ (k - 2)
  let mulR2 : ↥Vm →ₗ[ℝ] MvPolynomial (Fin n) ℝ :=
    (LinearMap.mulLeft ℝ (normSq n)).comp Vm.subtype
  have hmulR2_apply : ∀ Q : ↥Vm, mulR2 Q = normSq n * (Q : MvPolynomial (Fin n) ℝ) :=
    fun Q => rfl
  -- Multiplication by `∑ Xⱼ²` is injective.
  have hinj : Function.Injective mulR2 := by
    intro Q₁ Q₂ h
    have h' : normSq n * (Q₁ : MvPolynomial (Fin n) ℝ)
        = normSq n * (Q₂ : MvPolynomial (Fin n) ℝ) := by
      simpa only [hmulR2_apply] using h
    exact Subtype.ext (X2_mul_left_cancel h')
  have hker : LinearMap.ker mulR2 = ⊥ := LinearMap.ker_eq_bot.mpr hinj
  -- Finiteness instances.
  haveI hVmfin : FiniteDimensional ℝ ↥Vm := homogeneousSubmodule_finiteDimensional
  haveI hVkfin : FiniteDimensional ℝ ↥Vk := homogeneousSubmodule_finiteDimensional
  haveI hHfin : FiniteDimensional ℝ (harmHom n k) :=
    Submodule.finiteDimensional_of_le (fun x hx => (mem_harmHom.mp hx).1)
  -- Rank-nullity: `finrank (range mulR2) = finrank Vm`.
  have hfinrange : Module.finrank ℝ (LinearMap.range mulR2)
      = Module.finrank ℝ (MvPolynomial.homogeneousSubmodule (Fin n) ℝ (k - 2)) := by
    have h := LinearMap.finrank_range_add_finrank_ker mulR2
    rw [hker, finrank_bot, add_zero] at h
    exact h
  -- The range consists of homogeneous polynomials of degree `k`.
  have hMemRange : LinearMap.range mulR2 ≤ Vk := by
    rintro x ⟨Q, rfl⟩
    have hQ : (Q : MvPolynomial (Fin n) ℝ).IsHomogeneous (k - 2) :=
      (MvPolynomial.mem_homogeneousSubmodule (k - 2) (Q : MvPolynomial (Fin n) ℝ)).mp Q.2
    have h := (normSq_isHomogeneous n).mul hQ
    rw [hk2] at h
    exact (MvPolynomial.mem_homogeneousSubmodule k (normSq n * (Q : MvPolynomial (Fin n) ℝ))).mpr h
  -- The harmonic homogeneous part and the range fill up `Vk`.
  have hsup : harmHom n k ⊔ LinearMap.range mulR2 = Vk := by
    apply le_antisymm
    · refine sup_le (fun x hx => (mem_harmHom.mp hx).1) hMemRange
    · intro P hP
      obtain ⟨H, Q, hH, hQ, hlap, hdec⟩ := homogeneous_decompose (n := n) (k := k) P hP
      have hH' : H ∈ harmHom n k := mem_harmHom.mpr ⟨hH, hlap⟩
      have hQrange : (∑ j : Fin n, (MvPolynomial.X j)^2) * Q ∈ LinearMap.range mulR2 :=
        ⟨⟨Q, hQ⟩, by rw [hmulR2_apply]⟩
      rw [hdec]
      exact Submodule.add_mem_sup hH' hQrange
  -- ... and they intersect trivially.
  have hinf : harmHom n k ⊓ LinearMap.range mulR2 = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    rw [Submodule.mem_inf] at hx
    obtain ⟨hxH, hxR⟩ := hx
    obtain ⟨Q, hQ⟩ := hxR
    have hxVk : x ∈ Vk := (mem_harmHom.mp hxH).1
    have hxlap : lapLM n x = 0 := (mem_harmHom.mp hxH).2
    have hxeq : x = (∑ j : Fin n, (MvPolynomial.X j)^2) * (Q : MvPolynomial (Fin n) ℝ) := by
      rw [← hQ, hmulR2_apply]
    exact harmonic_X2_intersection x (Q : MvPolynomial (Fin n) ℝ) hxVk Q.2 hxlap hxeq
  -- Dimension identity for a direct sum.
  have hfin := Submodule.finrank_sup_add_finrank_inf_eq (harmHom n k) (LinearMap.range mulR2)
  rw [hsup, hinf, finrank_bot, add_zero, hfinrange] at hfin
  exact hfin.symm

end Commons.Algebra.MvPolynomial
