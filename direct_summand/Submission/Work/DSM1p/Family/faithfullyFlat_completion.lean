import Mathlib
import Submission.Work.DSM1p.Family
import Submission.Work.DSM1p.Family.flat_completion
import Submission.Work.DSM1p.Family.maximalIdeal_smul_ne_top
import Submission.Work.DSM1p.Assembly.faithfullyFlat_of_flat_of_maximalIdeal_smul_ne_top

/-!
# Faithful flatness of the `p`-adic completion of the multi-parameter root closure

Assembly of the two ingredients proved elsewhere in this subproject:

* `Work.DSM1p.Family.flat_completion` : the `p`-adic completion `A′ = (R[x₁^{1/p^∞},…,x_d^{1/p^∞}])^`
  is a flat `R`-module;
* `Work.DSM1p.Family.maximalIdeal_smul_ne_top` : `𝔪 • ⊤ ≠ ⊤` for the (local) base `R`.

Over a local ring a flat module not killed by the maximal ideal (the only maximal ideal) is
faithfully flat.
-/

namespace Work.DSM1p.Family

theorem faithfullyFlat_completion (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (p : ℕ) (hp0 : p ≠ 0) (hp : IsSMulRegular R p)
    (hpm : (p : R) ∈ IsLocalRing.maximalIdeal R) {d : ℕ} (x : Fin d → R)
    (hx : ∀ i, x i ∈ IsLocalRing.maximalIdeal R) :
    Module.FaithfullyFlat R (Work.DSM1p.FamCompletion R p x) := by
  have hp' : 0 < p := Nat.pos_of_ne_zero hp0
  have hflat : Module.Flat R (Work.DSM1p.FamCompletion R p x) :=
    flat_completion R p hp0 hp x
  exact { toFlat := hflat
          submodule_ne_top := fun m hm => by
            rw [IsLocalRing.eq_maximalIdeal hm]
            exact maximalIdeal_smul_ne_top R p hp' hpm x hx }

end Work.DSM1p.Family
