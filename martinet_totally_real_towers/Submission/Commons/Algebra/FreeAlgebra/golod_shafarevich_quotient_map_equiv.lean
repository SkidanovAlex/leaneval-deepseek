import Mathlib.Algebra.FreeAlgebra
import Mathlib.LinearAlgebra.Isomorphisms

namespace Commons.Algebra.FreeAlgebra

theorem golod_shafarevich_quotient_map_equiv
    {K ι : Type*} [Field K]
    (I V : Submodule K (FreeAlgebra K ι)) :
    Nonempty ((Submodule.map I.mkQ V) ≃ₗ[K]
      (V ⧸ (Submodule.comap V.subtype I))) := by
  classical
  let g : V →ₗ[K] (FreeAlgebra K ι) ⧸ I := I.mkQ.comp V.subtype
  have hrange : LinearMap.range g = Submodule.map I.mkQ V := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨v, rfl⟩
      exact ⟨v, v.2, rfl⟩
    · intro hx
      rcases hx with ⟨v, hv, rfl⟩
      exact ⟨⟨v, hv⟩, rfl⟩
  have hker : LinearMap.ker g = Submodule.comap V.subtype I := by
    ext x
    constructor
    · intro hx
      rw [LinearMap.mem_ker] at hx
      simp [g, Submodule.Quotient.mk_eq_zero] at hx
      exact hx
    · intro hx
      rw [LinearMap.mem_ker]
      simp [g, Submodule.Quotient.mk_eq_zero]
      simpa using hx
  let e1 : (Submodule.map I.mkQ V) ≃ₗ[K] (LinearMap.range g) :=
    (LinearEquiv.ofEq (p := LinearMap.range g) (q := Submodule.map I.mkQ V) hrange).symm
  let e2 : (LinearMap.range g) ≃ₗ[K] (V ⧸ LinearMap.ker g) :=
    g.quotKerEquivRange.symm
  let e3 : (V ⧸ LinearMap.ker g) ≃ₗ[K] (V ⧸ Submodule.comap V.subtype I) :=
    Submodule.quotEquivOfEq (p := LinearMap.ker g) (p' := Submodule.comap V.subtype I) hker
  exact ⟨e1.trans (e2.trans e3)⟩

end Commons.Algebra.FreeAlgebra