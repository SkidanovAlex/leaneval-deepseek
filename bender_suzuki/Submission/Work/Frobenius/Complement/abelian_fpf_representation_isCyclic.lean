import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped IsMulCommutative

namespace Work.Frobenius.Complement

set_option linter.style.haveILetI false

/-- Auxiliary linear-algebra fact: let `B` be a commutative `F`-algebra of finite `F`-dimension and
`Φ : B →+* Module.End F W` an injective ring homomorphism into the endomorphisms of a
finite-dimensional `F`-vector space `W`. If the image of `b : B` is injective as a map on `W`,
then `b` is a unit of `B`. -/
private lemma isUnit_of_injective_ringHom_end {F W B : Type*} [Field F] [CommRing B] [Algebra F B]
    [AddCommGroup W] [Module F W] [FiniteDimensional F B]
    (Φ : B →+* Module.End F W) (hΦ : Function.Injective Φ)
    (b : B) (hb : Function.Injective (Φ b)) : IsUnit b := by
  have hz : ∀ z : B, b * z = 0 → z = 0 := by
    intro z hb0
    apply hΦ
    rw [map_zero]
    have h1 : Φ (b * z) = 0 := by rw [hb0, map_zero]
    rw [map_mul] at h1
    have h2 : Φ z = 0 := by
      apply LinearMap.ext
      intro w
      rw [LinearMap.zero_apply]
      have h3 : (Φ b) ((Φ z) w) = 0 := by
        have := DFunLike.congr_fun h1 w
        simpa [Module.End.mul_apply] using this
      exact hb (by rw [h3]; exact (map_zero (Φ b)).symm)
    exact h2
  have hlm_apply : ∀ x : B, Algebra.lmul F B b x = b * x := by
    intro x
    rw [Algebra.coe_lmul_eq_mul, LinearMap.mul_apply']
  have hinjLM : Function.Injective ⇑(Algebra.lmul F B b) := by
    intro x y hxy
    rw [hlm_apply x, hlm_apply y] at hxy
    have : b * (x - y) = 0 := by rw [mul_sub, hxy, sub_self]
    exact sub_eq_zero.mp (hz (x - y) this)
  have hsurj : Function.Surjective (Algebra.lmul F B b) :=
    LinearMap.surjective_of_injective (f := Algebra.lmul F B b) hinjLM
  obtain ⟨y, hy⟩ := hsurj 1
  have hy' : b * y = 1 := by rw [← hlm_apply y]; exact hy
  exact isUnit_iff_exists.mpr ⟨y, hy', by rw [mul_comm, hy']⟩

theorem abelian_fpf_representation_isCyclic {F : Type*} [Field F] {A : Type*} [Group A]
    [Finite A] [IsMulCommutative A] {W : Type*} [AddCommGroup W] [Module F W]
    [FiniteDimensional F W] (ρ : Representation F A W) (hW : Nontrivial W)
    (hfp : ∀ a : A, a ≠ 1 → ∀ w : W, ρ a w = w → w = 0) : IsCyclic A := by
  classical
  let φ : MonoidAlgebra F A →ₐ[F] Module.End F W := ρ.asAlgebraHom
  let K : Ideal (MonoidAlgebra F A) := RingHom.ker φ.toRingHom
  let Φ : MonoidAlgebra F A ⧸ K →+* Module.End F W := RingHom.kerLift φ.toRingHom
  have hΦ_inj : Function.Injective Φ := RingHom.kerLift_injective φ.toRingHom
  have hΦ_mk : ∀ r : MonoidAlgebra F A, Φ (Ideal.Quotient.mk K r) = φ r :=
    fun r => RingHom.kerLift_mk φ.toRingHom r
  have hne : (1 : Module.End F W) ≠ 0 := by
    intro h
    obtain ⟨w, hw⟩ := exists_ne (0 : W)
    exact hw (by
      have := DFunLike.congr_fun h w
      simpa using this)
  have hB_nt : Nontrivial (MonoidAlgebra F A ⧸ K) := by
    rw [Ideal.Quotient.nontrivial_iff]
    intro htop
    have h1 : (1 : MonoidAlgebra F A) ∈ K := by rw [htop]; trivial
    rw [show K = RingHom.ker φ.toRingHom from rfl, RingHom.mem_ker] at h1
    exact hne (by rw [← map_one φ]; exact h1)
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (MonoidAlgebra F A ⧸ K)
  haveI : M.IsMaximal := hM
  letI : Field ((MonoidAlgebra F A ⧸ K) ⧸ M) := Ideal.Quotient.field M
  let g : A →* (MonoidAlgebra F A ⧸ K) :=
    (Ideal.Quotient.mk K).toMonoidHom.comp (MonoidAlgebra.of F A)
  let f : A →* ((MonoidAlgebra F A ⧸ K) ⧸ M) := (Ideal.Quotient.mk M).toMonoidHom.comp g
  have he_unit : ∀ a : A, a ≠ 1 → IsUnit (g a - 1) := by
    intro a ha
    have hΦa : Φ (g a - 1) = ρ a - 1 := by
      have hga : g a = Ideal.Quotient.mk K (MonoidAlgebra.of F A a) := rfl
      rw [hga, map_sub, hΦ_mk, Representation.asAlgebraHom_of, map_one]
    refine isUnit_of_injective_ringHom_end Φ hΦ_inj (g a - 1) ?_
    rw [hΦa]
    intro w1 w2 h
    have h1 : (ρ a - 1) (w1 - w2) = 0 := by rw [map_sub, h, sub_self]
    rw [LinearMap.sub_apply, Module.End.one_eq_id, LinearMap.id_apply, sub_eq_zero] at h1
    exact sub_eq_zero.mp (hfp a ha (w1 - w2) h1)
  have hf_ne_one : ∀ c : A, c ≠ 1 → f c ≠ 1 := by
    intro c hc hfc
    have h' : Ideal.Quotient.mk M (g c) = Ideal.Quotient.mk M (1 : MonoidAlgebra F A ⧸ K) := by
      rw [map_one]
      exact hfc
    have hmem : g c - 1 ∈ M := Ideal.Quotient.eq.mp h'
    exact hM.ne_top (Ideal.eq_top_of_isUnit_mem M hmem (he_unit c hc))
  have hf_inj : Function.Injective f := by
    intro a b hab
    by_contra hneab
    have hne' : a * b⁻¹ ≠ 1 := fun h => hneab (mul_inv_eq_one.mp h)
    have h1 : f (a * b⁻¹) = 1 := by
      rw [map_mul, hab, ← map_mul, mul_inv_cancel, map_one]
    exact hf_ne_one (a * b⁻¹) hne' h1
  exact isCyclic_of_injective_ringHom f hf_inj

end Work.Frobenius.Complement
