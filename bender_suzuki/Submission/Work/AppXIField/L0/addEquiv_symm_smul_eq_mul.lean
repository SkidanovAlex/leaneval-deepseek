import Mathlib
import Submission.Work.AppXIField.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.AppXIField.L0

theorem addEquiv_symm_smul_eq_mul {V A : Type} [AddCommGroup V] [CommGroup A] [DistribMulAction A V]
    (v₀ : V) (ι : A →* (Module.End ↥(Work.AppXIField.actSubring A V) V)ˣ)
    (hιact : ∀ (a : A) (v : V),
        ((ι a : Module.End ↥(Work.AppXIField.actSubring A V) V) : V → V) v = a • v)
    (Φ : Module.End ↥(Work.AppXIField.actSubring A V) V →+ V)
    (hΦ : ∀ k : Module.End ↥(Work.AppXIField.actSubring A V) V, Φ k = (k : V → V) v₀)
    (hbij : Function.Bijective Φ) :
    ∀ (a : A) (v : V),
      (AddEquiv.ofBijective Φ hbij).symm (a • v) =
        (ι a : Module.End ↥(Work.AppXIField.actSubring A V) V) *
          (AddEquiv.ofBijective Φ hbij).symm v := by
  intro a v
  apply (AddEquiv.ofBijective Φ hbij).injective
  rw [AddEquiv.apply_symm_apply]
  change a • v = Φ (↑(ι a) * (AddEquiv.ofBijective Φ hbij).symm v)
  rw [hΦ, Module.End.mul_apply]
  have h1 : (((AddEquiv.ofBijective Φ hbij).symm v :
      Module.End ↥(Work.AppXIField.actSubring A V) V) : V → V) v₀ = v := by
    have h := (AddEquiv.ofBijective Φ hbij).apply_symm_apply v
    change Φ ((AddEquiv.ofBijective Φ hbij).symm v) = v at h
    rw [hΦ] at h
    exact h
  rw [h1, hιact]

end Work.AppXIField.L0
