import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# A surjection between two copies of `ℤ` is an isomorphism

The elementary algebra input of the projection lemma of the Serre exact sequence
(`Submission/Work/StemsB/SERRE_PLAN.md` §6): a surjective `ℤ`-linear map between two `ℤ`-modules that
are each linearly isomorphic to `ℤ` is bijective.  The proof conjugates the map to an endomorphism
of `ℤ`, which is multiplication by its value at `1`; surjectivity forces that value to be `±1`.
-/

namespace Work.StemsB

theorem bijective_of_surjective_of_int_iso {M N : Type*} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N] (hM : Nonempty (M ≃ₗ[ℤ] ℤ)) (hN : Nonempty (N ≃ₗ[ℤ] ℤ))
    (f : M →ₗ[ℤ] N) (hf : Function.Surjective f) : Function.Bijective f := by
  obtain ⟨e⟩ := hM
  obtain ⟨e'⟩ := hN
  -- the conjugate endomorphism of `ℤ`
  set T : ℤ →ₗ[ℤ] ℤ := e'.comp (f.comp e.symm.toLinearMap) with hTdef
  have hTz : ∀ z : ℤ, T z = z * T 1 := by
    intro z
    have h : z • (1 : ℤ) = z := by simp
    rw [← h, map_zsmul]
    simp
  have hTsurj : Function.Surjective T := by
    intro z
    obtain ⟨m, hm⟩ := hf (e'.symm z)
    refine ⟨e m, ?_⟩
    simp only [hTdef, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [LinearEquiv.symm_apply_apply, hm]
    simp
  obtain ⟨y, hy⟩ := hTsurj 1
  have h1 : T 1 * y = 1 := by
    have h := hTz y
    rw [hy] at h
    rw [mul_comm, ← h]
  have hunit : T 1 = 1 ∨ T 1 = -1 := Int.eq_one_or_neg_one_of_mul_eq_one h1
  have hTinj : Function.Injective T := by
    intro a b hab
    have h2 : T (a - b) = 0 := by rw [map_sub, hab, sub_self]
    rw [hTz] at h2
    have hzero : (a - b) = 0 := by
      rcases hunit with h | h
      · simpa [h] using h2
      · have h3 : b - a = 0 := by simpa [h] using h2
        exact sub_eq_zero.mpr ((sub_eq_zero.mp h3).symm)
    exact sub_eq_zero.mp hzero
  constructor
  · intro a b hab
    have h : T (e a) = T (e b) := by
      simp only [hTdef, LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply, hab]
    exact e.injective (hTinj h)
  · intro b
    obtain ⟨m, hm⟩ := hf b
    exact ⟨m, hm⟩

end Work.StemsB
