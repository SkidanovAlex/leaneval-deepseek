import Mathlib
import Submission.Work.SSGRoute.PT.g1plus_levelTransport
import Submission.Work.SSGRoute.PT.g1plus_levelTransportIota
import Submission.Work.SSGRoute.CokerPT.IotaAlgebra
import Submission.Work.SSGRoute.PT.g1plus_levelInfl
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The level change of `chi o iota_w o levelPair` (the *spine* of `finAtLevel`'s level independence)

`PT.finAtLevel` evaluates `chi L hKL (iota_w z)` where `z = levelPair f iota (beta_l a) hval` is a
class in `H^2(D_w, L_w^x)`.  Its level independence (given the inflation coherence `hchi` of the
coherent `p`-torsion invariant `chi`) reduces to: *if `z'` is the local inflation of `z` from the
place `w` of `L` to the place `w'` of `L' >= L`, then `chi L' hKL' (iota_{w'} z') = chi L hKL
(iota_w z)`.*

This file proves that spine from the two level-transport lemmas
(`PT.iotaLift_idleRepMap`, `PT.extToClasses_idleRepMap`) and `chi`'s coherence, so that the
remaining work of `PT.finAtLevel_eq_of_le` is only the *comparison of the local data* (`z'` is the
local inflation of `z`).

**Vocabulary.**  The coherence hypothesis is taken in the `inflC` form (the definitional spelling
of `PT.inflLevel`); the bridge `inflLevel = inflC` is `inflLevel_eq_inflC` below, whose statement
seeds the instances that `inflLevel`'s body uses so that the comparison is syntactic -- the naive
statement (abstract instances) makes `isDefEq` diverge (measured;
`CokerPT/PING_h_levelClass_and_finAtLevelFix.md` section 4).
-/

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option autoImplicit false

open CategoryTheory SSGRoute.PTExt
open scoped TensorProduct

namespace Work.SSGRoute.PT

/-- **`inflLevel` is `inflC`** (they are the same term).  The conclusion seeds the very instances
that `inflLevel`'s body uses, so the comparison of the two instance arguments is a syntactic match
(the naive statement, with abstract instances, makes `isDefEq` diverge -- see the module
docstring). -/
theorem inflLevel_eq_inflC (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    (L L' : IntermediateField k Ω) [NumberField L] [NumberField L']
    [FiniteDimensional k L] [IsGalois k L] (h : L ≤ L') {n : ℕ}
    (y : extH (classesK k L) n) :
    letI : Algebra (↥L) (↥L') := (IntermediateField.inclusion h).toAlgebra
    haveI : IsScalarTower k (↥L) (↥L') := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    inflLevel L L' h y = inflC (k := k) (K := ↥L) (L := ↥L') y := by
  rw [inflLevel_def]

/-- **The spine of `finAtLevel`'s level independence.**  Let `K ≤ L ≤ L'` be levels of `Ω/k`,
`w` a place of `L` and `w'` a place of `L'` lying over it, and let `z' ∈ H²(D_{w'}, L'_{w'}ˣ)` be
the *local inflation* of `z ∈ H²(D_w, L_wˣ)`: inflation along the restriction
`ρ = decompKRestrict` of decomposition groups, composed with the local-units map `μ`.  Then for a
`χ` with the inflation coherence `hχ` (clause (3) of the coherent `p`-torsion invariant, in its
`inflC` spelling), `χ L' hKL' (ι_{w'} z') = χ L hKL (ι_w z)`.

Route: `ι_w = extToClasses ∘ iotaLift`; `PT.iotaLift_idleRepMap` moves the orbit-supported lift
along the idèle level map `E9c.idleRepMap`; `PT.extToClasses_idleRepMap` (via the proved
coefficient square `E9c.resMap_classGroupMap_comp_classIncl`) moves it to `C_L'` as `inflC`; and
`hχ` finishes.  The `p`-torsion of `ι_w z` is `PT.iota_add`/`PT.iota_zero` applied to `hptor`. -/
theorem chi_iota_eq_of_localInflation
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (χ : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L],
        K ≤ L → extH (classesK k L) 2 → ZMod p)
    (hχ : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
        (hKL : K ≤ L) (L' : IntermediateField k Ω) [NumberField L']
        [FiniteDimensional k L'] [IsGalois k L'] (hKL' : K ≤ L') [Algebra (↥L) (↥L')]
        [IsScalarTower k (↥L) (↥L')] (hLL : L ≤ L') (u : extH (classesK k L) 2),
        p • u = 0 → χ L' hKL' (inflC (k := k) (K := ↥L) (L := ↥L') u) = χ L hKL u)
    (L L' : IntermediateField k Ω) [NumberField L] [NumberField L']
    [FiniteDimensional k L] [IsGalois k L] [FiniteDimensional k L'] [IsGalois k L']
    [Algebra (↥L) (↥L')] [IsScalarTower k (↥L) (↥L')]
    (hKL : K ≤ L) (hKL' : K ≤ L') (hLL : L ≤ L')
    (w : NK.GlobalCFT.Place ↥L) (w' : NK.GlobalCFT.Place ↥L')
    (hw' : NK.GlobalCFT.Place.LiesOver w' w)
    (μ : Rep.res (decompKRestrict k (↥L) (↥L') w w' hw') (localUnitsK (k := k) (K := ↥L) w) ⟶
      localUnitsK (k := k) (K := ↥L') w')
    (hμ : ∀ y : (NK.GlobalCFT.Place.localField ↥L w)ˣ,
      μ.hom (Additive.ofMul y)
        = Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits w' w hw' y))
    (z : extH (localUnitsK (k := k) (K := ↥L) w) 2)
    (z' : extH (localUnitsK (k := k) (K := ↥L') w') 2)
    (hz' : z' = extHMap (decompKRestrict k (↥L) (↥L') w w' hw') μ z)
    (hptor : p • z = 0) :
    χ L hKL (iota (k := k) (L := ↥L) w z)
      = χ L' hKL' (iota (k := k) (L := ↥L') w' z') := by
  classical
  have hiota_nsmul : ∀ n : ℕ,
      n • iota (k := k) (L := ↥L) w z = iota (k := k) (L := ↥L) w (n • z) := by
    intro n
    induction n with
    | zero => rw [zero_smul, zero_smul, iota_zero]
    | succ n ih => simp only [add_nsmul, one_nsmul, iota_add, ih]
  have hptor' : p • iota (k := k) (L := ↥L) w z = 0 := by
    rw [hiota_nsmul, hptor, iota_zero]
  rw [← hχ L hKL L' hKL' hLL (iota (k := k) (L := ↥L) w z) hptor']
  refine congrArg (fun v : extH (classesK k ↥L') 2 => χ L' hKL' v) ?_
  rw [hz']
  rw [show iota (k := k) (L := ↥L') w'
        (extHMap (decompKRestrict k (↥L) (↥L') w w' hw') μ z)
      = extToClasses (k := k) (K := ↥L')
          (iotaLift (k := k) (L := ↥L') w'
            (extHMap (decompKRestrict k (↥L) (↥L') w w' hw') μ z)) from rfl]
  rw [iotaLift_idleRepMap k (↥L) (↥L') w w' hw' μ hμ z]
  rw [extToClasses_idleRepMap k (↥L) (↥L') (iotaLift (k := k) (L := ↥L) w z)]
  rfl

end Work.SSGRoute.PT
