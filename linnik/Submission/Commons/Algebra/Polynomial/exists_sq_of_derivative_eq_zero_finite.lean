import Mathlib.Algebra.CharP.Reduced
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.Algebra.Polynomial

open _root_.Polynomial

/-- Over a finite field of characteristic `2`, a polynomial with vanishing derivative is a
square. -/
theorem exists_sq_of_derivative_eq_zero_finite {F : Type*} [Field F] [Fintype F] [CharP F 2]
    (g : Polynomial F) (h : Polynomial.derivative g = 0) :
    ∃ h' : Polynomial F, g = h' ^ 2 := by
  have hinj : Function.Injective (frobenius F 2) := frobenius_inj F 2
  have hbij : Function.Bijective (frobenius F 2) := hinj.bijective_of_finite
  let σ : F ≃+* F := RingEquiv.ofBijective (frobenius F 2) hbij
  refine ⟨Polynomial.map (σ.symm : F →+* F) (contract 2 g), ?_⟩
  have hexp : expand F 2 (contract 2 g) = g := expand_contract' (p := 2) h
  have hmap : Polynomial.map (frobenius F 2) g = (contract 2 g) ^ 2 := by
    conv_lhs => rw [← hexp]
    exact map_frobenius_expand 2 (contract 2 g)
  have hcomp : ((σ.symm : F →+* F).comp (frobenius F 2)) = RingHom.id F := by
    ext x
    exact σ.symm_apply_apply x
  have key : Polynomial.map (σ.symm : F →+* F) ((contract 2 g) ^ 2) = g := by
    rw [← hmap, Polynomial.map_map, hcomp, Polynomial.map_id]
  have key2 : (Polynomial.map (σ.symm : F →+* F) (contract 2 g)) ^ 2
      = Polynomial.map (σ.symm : F →+* F) ((contract 2 g) ^ 2) :=
    (Polynomial.map_pow (p := contract 2 g) (f := (σ.symm : F →+* F)) 2).symm
  rw [key2, key]

end Commons.Algebra.Polynomial