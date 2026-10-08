import Mathlib
import Submission.Work.Hering.HardCore.aut_involutions_conj
import Submission.Work.Hering.Step5.mulAut_eight_order21

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Hering.HardCore

/-- **Conjugacy of non-identity involutions of `Aut(V)`** for `V` a finite group of order `8`
and exponent `2`.  Such a `V` is elementary abelian of rank `3` (`Work.Hering.Step5.iso_fin3`),
and transporting along that isomorphism reduces to
`Work.Hering.HardCore.aut_involutions_conj` in the concrete model `(ℤ/2)³`. -/
theorem aut_inv_conj_V {V : Type*} [Group V] [Finite V] (hcard : Nat.card V = 8)
    (hexp : ∀ x : V, x * x = 1) (u w : MulAut V) (hu : u ≠ 1) (hu2 : u * u = 1)
    (hw : w ≠ 1) (hw2 : w * w = 1) : ∃ φ : MulAut V, w = φ * u * φ⁻¹ := by
  obtain ⟨e⟩ := Work.Hering.Step5.iso_fin3 hcard hexp
  let F : MulAut V ≃* MulAut (Multiplicative (Fin 3 → ZMod 2)) := MulAut.congr e
  have hu' : F u ≠ 1 := fun h1 => hu (F.injective (by rw [h1, map_one]))
  have hu2' : F u * F u = 1 := by rw [← map_mul, hu2, map_one]
  have hw' : F w ≠ 1 := fun h1 => hw (F.injective (by rw [h1, map_one]))
  have hw2' : F w * F w = 1 := by rw [← map_mul, hw2, map_one]
  obtain ⟨U, hU⟩ := aut_involutions_conj (F u) (F w) hu' hu2' hw' hw2'
  refine ⟨F.symm U, ?_⟩
  apply F.injective
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  exact hU

end Work.Hering.HardCore
