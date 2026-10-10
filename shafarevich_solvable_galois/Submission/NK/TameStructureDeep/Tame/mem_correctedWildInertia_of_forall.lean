import Mathlib.FieldTheory.Galois.Basic
import Submission.NK.TameStructureDeep.Tame.TameClosure
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Classical
open IntermediateField

set_option linter.unusedVariables false

namespace NK.TameStructureDeep.Tame

/-- **Membership criterion for the corrected wild inertia.**  An element `x` of `Gal(K'/κ)`
which fixes the maximal unramified extension `κ^{ur} = unramifiedClosure p` pointwise and fixes
every `n`-th root of the uniformiser `π` with `p ∤ n` lies in `V_κ = Gal(K'/κ^{tr})`: it fixes
each generator of `κ^{tr}` over `κ^{ur}`, hence the whole compositum.

This is the converse direction of `tameClosure_le_iff`, transported across the Galois
correspondence `σ ∈ L.fixingSubgroup`; note that `hp : p ≠ 1` is not needed, but is carried
along so that the statement matches the shape of the local structure theorem. -/
theorem mem_correctedWildInertia_of_forall {κ K' : Type*} [Field κ] [Field K'] [Algebra κ K']
    {p : ℕ} (hp : p ≠ 1) {π : κ} (x : Gal(K'/κ))
    (hunr : ∀ y ∈ NK.LocalAnabelian.unramifiedClosure (κ := κ) (K' := K') p, x y = y)
    (hroot : ∀ (n : ℕ), ¬ p ∣ n → ∀ β : K', β ^ n = algebraMap κ K' π → x β = β) :
    x ∈ NK.TameStructureDeep.Tame.correctedWildInertia (K' := K') p π := by
  rw [correctedWildInertia, tameClosure, IntermediateField.fixingSubgroup_sup]
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · exact (IntermediateField.mem_fixingSubgroup_iff _ x).mpr hunr
  · refine (IntermediateField.mem_fixingSubgroup_iff _ x).mpr ?_
    have key : ∀ y ∈ IntermediateField.adjoin κ (tameRootSet (K' := K') p π), x y = y := by
      intro y hy
      induction hy using IntermediateField.adjoin_induction with
      | mem z hz => obtain ⟨n, hn, hzn⟩ := hz; exact hroot n hn z hzn
      | algebraMap a => exact x.commutes a
      | add a b ha hb iha ihb => rw [map_add, iha, ihb]
      | inv a ha iha => rw [map_inv₀, iha]
      | mul a b ha hb iha ihb => rw [map_mul, iha, ihb]
    exact key

end NK.TameStructureDeep.Tame
