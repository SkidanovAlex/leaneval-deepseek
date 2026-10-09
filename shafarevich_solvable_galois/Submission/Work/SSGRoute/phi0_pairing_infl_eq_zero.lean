import Mathlib
import Submission.Work.SSGRoute.PTDefsOmega
import Submission.Work.SSGRoute.phi_pair_natural
import Submission.Work.SSGRoute.phiTriv_mk0_eq
import Submission.Work.SSGRoute.E4R3.inflC_injective
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `φ⁰` pairing kills classes that die under inflation

Level `K ≤ L ≤ L'` of a fixed algebraic closure `Ω` of `K`, `c : 𝔽_p ⟶ C_K` a level-`K`
coefficient class and `h ∈ H²(Gal(L/k), 𝔽_p)`.  If `h` becomes zero after inflation to the
higher level `L'`, then its level-`L` Yoneda pairing with `c` vanishes:

`h ∪ c = 0` in `H²(Gal(L/k), C_L)`.

This is the injectivity half of the reduction of node `E4` (`phi0_trivial_epi`): the pairing
factors through the level-`L` value of the class, and the level inflation
`H²(Gal(L/k), C_L) → H²(Gal(L'/k), C_{L'})` is injective — so it suffices to check the value
after inflating to `L'`, where the class `h` is already `0`.

The proof is three rewrites:

* `phiTriv_mk₀_pushClass` — the level-`L` pairing with the level-`K` class `c` is the level-`L`
  Yoneda pairing with the pushed-forward coefficient map `pushClass k K L 𝔽_p c`;
* `phi_pair_natural` — naturality of the Yoneda pairing under inflation: inflating the value of
  the level-`L` pairing gives the level-`L'` pairing of the pushed-forward coefficient map with
  the inflated class `inflTriv h`, which is `0` by hypothesis;
* `inflC_injective` — inflation on `H²(·, C_·)` is injective, so the level-`L` value itself is
  `0`.
-/

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory

set_option linter.style.haveILetI false

theorem phi0_pairing_infl_eq_zero (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
    [FiniteDimensional k K] [IsGalois k K] (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω]
    [Algebra k Ω] [IsScalarTower k K Ω]
    (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
    (L' : IntermediateField K Ω) [NumberField L'] [FiniteDimensional k L'] [IsGalois k L']
    (hLL : L ≤ L')
    (c : Rep.trivial Coeff (K ≃ₐ[k] K) (ZMod p) ⟶ classesK k K)
    (h : extH (Rep.trivial Coeff (L ≃ₐ[k] L) (ZMod p)) 2)
    (hz : inflTrivIn (k := k) hLL (ZMod p) h = 0) :
    phiTriv (k := k) (K := K) (L := L) (ZMod p) (Abelian.Ext.mk₀ c) h = 0 := by
  -- The level-`L` pairing with the pushed-forward coefficient class `pushClass k K L 𝔽_p c`.
  have key : pairK (k := k) (K := L)
      (Abelian.Ext.mk₀ (pushClass k K L (ZMod p) c)) h = 0 := by
    -- the inclusion `L ≤ L'` gives the level `L'` used for the inflation
    letI : Algebra L L' := (IntermediateField.inclusion hLL).toAlgebra
    haveI : IsScalarTower k L L' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    -- the hypothesis, read as vanishing of `inflTriv`
    have hz' : inflTriv (k := k) (K := L) (L := L') (ZMod p) h = 0 := hz
    -- inflation kills zero
    have h0 : inflC (k := k) (K := L) (L := L') (0 : extH (classesK k L) 2) = 0 := by
      simp only [inflC, extHMap, extRes, Abelian.Ext.mapExactFunctor_zero,
        Abelian.Ext.zero_comp, Abelian.Ext.comp_zero]
    -- the value after inflation is the level-`L'` pairing with the inflated class
    have hval : inflC (k := k) (K := L) (L := L')
        (pairK (k := k) (K := L)
          (Abelian.Ext.mk₀ (pushClass k K L (ZMod p) c)) h) = 0 := by
      rw [phi_pair_natural p k L L' (pushClass k K L (ZMod p) c) h, hz']
      simp only [pairK, yonedaPair, Abelian.Ext.zero_comp]
    -- inflation on `H²(·, C_·)` is injective, so the level-`L` value vanishes
    exact Work.SSGRoute.E4R3.inflC_injective k L L'
      (by beta_reduce; rw [hval, h0])
  rw [phiTriv_mk₀_pushClass p k K L c h]
  exact key

end Work.SSGRoute
