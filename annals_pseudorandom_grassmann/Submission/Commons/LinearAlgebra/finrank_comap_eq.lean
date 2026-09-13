import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace Commons.LinearAlgebra

theorem finrank_comap_eq {K : Type*} [Field K] {V W : Type*}
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [FiniteDimensional K V] (f : V →ₗ[K] W) (S : Submodule K W) :
    Module.finrank K ↥(Submodule.comap f S) =
      Module.finrank K ↥(LinearMap.ker f) +
        Module.finrank K ↥(S ⊓ LinearMap.range f) := by
  set T : Submodule K V := Submodule.comap f S with hT
  let e : T →ₗ[K] W := f.comp T.subtype
  have hrange : LinearMap.range e = S ⊓ LinearMap.range f := by
    ext w
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.2, ⟨x.1, rfl⟩⟩
    · rintro ⟨hw, v, hv⟩
      refine ⟨⟨v, ?_⟩, hv⟩
      rw [hT, Submodule.mem_comap]
      rw [hv]; exact hw
  have hle : LinearMap.ker f ≤ T := by
    intro x hx
    rw [LinearMap.mem_ker] at hx
    rw [hT, Submodule.mem_comap, hx]
    exact S.zero_mem
  have hker : LinearMap.ker e = Submodule.comap T.subtype (LinearMap.ker f) := by
    ext x
    rw [LinearMap.mem_ker, Submodule.mem_comap, LinearMap.mem_ker]
    rfl
  have hkerfin : Module.finrank K ↥(LinearMap.ker e) =
      Module.finrank K ↥(LinearMap.ker f) := by
    rw [hker]
    exact (Submodule.comapSubtypeEquivOfLe hle).finrank_eq
  have h := e.finrank_range_add_finrank_ker
  rw [hrange, hkerfin] at h
  rw [hT] at h
  rw [← h]
  exact add_comm _ _

end Commons.LinearAlgebra