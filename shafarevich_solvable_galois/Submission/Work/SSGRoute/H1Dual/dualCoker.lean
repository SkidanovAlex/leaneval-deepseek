import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.H1Dual

/-- For a linear map `g : B →ₗ[k] C` over a field, the cokernel of the transpose `g.dualMap`
is the dual of the kernel of `g`.

Proof: over a field the range of `g.dualMap` is exactly the annihilator of `ker g`
(`LinearMap.range_dualMap_eq_dualAnnihilator_ker`), and for any subspace `W` the quotient of the
dual by the annihilator of `W` is the dual of `W` (`Subspace.quotAnnihilatorEquiv`). -/
theorem dualCoker {k : Type*} [Field k] {B C : Type*} [AddCommGroup B] [Module k B]
    [AddCommGroup C] [Module k C] (g : B →ₗ[k] C) :
    Nonempty ((Module.Dual k B ⧸ (g.dualMap).range) ≃ₗ[k] Module.Dual k g.ker) :=
  ⟨(Submodule.quotEquivOfEq _ _ (LinearMap.range_dualMap_eq_dualAnnihilator_ker g)).trans
    (Subspace.quotAnnihilatorEquiv g.ker)⟩

end Work.SSGRoute.H1Dual
