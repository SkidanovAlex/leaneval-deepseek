import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.Sha2Lib.yonedaPair_extToClasses_eq_zero_of_locTrivial
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# E9 `pt_core_assembly` — the Ext-core assembly of the Tate-Poitou duality

New file (`namespace SSGRoute.PTExt`).  The design (`DESIGN_PT.md` E9, `DESIGN_FIX.md` §(4),
`DESIGN_FIX2.md` §2-3) writes the assembly of the family `Work.SSGRoute.tatePoitouEmbedding` out of

* the formal exactness of the class formation `0 → Kˣ → 𝕀_K → C_K → 0` (`extToClasses`,
  `extDelta`), giving `(∃ z, extToClasses z = x) ↔ extDelta x = 0`;
* the `φ¹`-mono input `E6Ω` (`Work.SSGRoute.phi1_mono_sylow_in`);
* the local realisation `E7` (`Work.SSGRoute.local_duality_ext`) and the local–global
  compatibility `E8`.

This file isolates the *formal* half.
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory

noncomputable section

namespace SSGRoute.PTExt

variable (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]

/-- The connecting map `extDelta` of the class formation kills the image of `extToClasses`: the
Yoneda product of the extension class of `0 → Kˣ → 𝕀_K → C_K → 0` with the map `𝕀_K → C_K` is the
class of the pullback of the extension along its own surjection, which is split. -/
theorem extDelta_extToClasses {M : Rep.{0} Coeff (K ≃ₐ[k] K)} {r : ℕ}
    (z : Abelian.Ext.{0} M (idelesK k K) r) :
    extDelta (k := k) (K := K) (extToClasses (k := k) (K := K) z) = 0 := by
  have hS := NK.HassePrinciple.ideleShortComplex_shortExact k K
  have hstep :
      (z.comp (Abelian.Ext.mk₀ (NK.HassePrinciple.ideleShortComplex k K).g) (add_zero r)).comp
        hS.extClass (rfl : r + 1 = r + 1)
      = z.comp ((Abelian.Ext.mk₀ (NK.HassePrinciple.ideleShortComplex k K).g).comp hS.extClass
          (zero_add 1)) (by omega) :=
    Abelian.Ext.comp_assoc z _ hS.extClass (add_zero r) (zero_add 1) (by omega)
  rw [show extDelta (k := k) (K := K) (extToClasses (k := k) (K := K) z)
      = (z.comp (Abelian.Ext.mk₀ (NK.HassePrinciple.ideleShortComplex k K).g) (add_zero r)).comp
        hS.extClass (rfl : r + 1 = r + 1) from rfl,
    hstep, hS.comp_extClass, Abelian.Ext.comp_zero]

/-- **Exactness of the class formation at `Ext¹(M, C_K)`**: a class of `Ext¹(M, C_K)` is the
pushforward of a class of `Ext¹(M, 𝕀_K)` along `𝕀_K → C_K` if and only if it dies under the
connecting map `extDelta` (i.e. if and only if its image in `Ext²(M, Kˣ)` vanishes).  This is the
formal half of `E9` (`DESIGN_FIX.md` §(4)). -/
theorem exists_extToClasses_iff_extDelta_eq_zero {M : Rep.{0} Coeff (K ≃ₐ[k] K)}
    (x : Abelian.Ext.{0} M (classesK k K) 1) :
    (∃ z : Abelian.Ext.{0} M (idelesK k K) 1, extToClasses (k := k) (K := K) z = x)
      ↔ extDelta (k := k) (K := K) x = 0 := by
  have hS := NK.HassePrinciple.ideleShortComplex_shortExact k K
  constructor
  · rintro ⟨z, rfl⟩
    exact extDelta_extToClasses k K z
  · intro hx
    have hx' : x.comp hS.extClass (rfl : 1 + 1 = 2) = 0 := hx
    obtain ⟨z, hz⟩ := Abelian.Ext.covariant_sequence_exact₃ (X := M) hS x (n₁ := 2)
      (rfl : 1 + 1 = 2) hx'
    exact ⟨z, hz⟩


/-! ## The well-definedness of the Poitou–Tate pairing on `Ш²(k,E)` (the `G5`/`E9` interface)

The pairing `(a, b) ↦ χ (pairK x_b (β a))` of the `G5` assembly is defined by choosing, for a class
`b ∈ Ш²(k,E)`, an `x_b ∈ Ext¹_G(M, C_K)` with `extDelta x_b = β₂(b)` (`M = E^∨(1)`; such a class
exists because `im β₂ = ker extToIdeles = im extDelta`, the clause of node `E1a`).  The lemmas below
show that the pairing value depends only on `b`, i.e. is independent of the choice of `x_b`: two
choices differ by `extToClasses z`, and `yonedaPair (extToClasses z) h = 0` for every locally
trivial `h` (the orthogonality lemma `Sha2Lib/yonedaPair_extToClasses_eq_zero_of_locTrivial`, the
"easy direction" of `E9` / `DESIGN_FIX2.md` §5). -/

/-- `extDelta` is additive (hence kills differences of equal values). -/
theorem extDelta_sub {M : Rep.{0} Coeff (K ≃ₐ[k] K)}
    (x x' : Abelian.Ext.{0} M (classesK k K) 1) :
    extDelta (k := k) (K := K) (x - x')
      = extDelta (k := k) (K := K) x - extDelta (k := k) (K := K) x' := by
  simp only [extDelta]
  rw [sub_eq_add_neg]
  rw [Abelian.Ext.add_comp, Abelian.Ext.neg_comp]
  rw [sub_eq_add_neg]

/-- `yonedaPair` is additive in the `Ext` variable. -/
theorem yonedaPair_sub {M A : Rep.{0} Coeff (K ≃ₐ[k] K)} {r s : ℕ}
    (x x' : Abelian.Ext.{0} M A r) (h : extH M s) :
    yonedaPair (x - x') h = yonedaPair x h - yonedaPair x' h := by
  simp only [yonedaPair]
  rw [sub_eq_add_neg]
  rw [Abelian.Ext.comp_add, Abelian.Ext.comp_neg]
  rw [sub_eq_add_neg]

/-- **Well-definedness of the Poitou–Tate pairing on `Ш²`.**  If `extDelta x = extDelta x'` (i.e.
`x` and `x'` are two choices of a preimage of the same `Ш²`-class under `extDelta`) then they pair
in the same way against every locally trivial class. -/
theorem yonedaPair_eq_of_extDelta_eq [FiniteDimensional k K] [IsGalois k K]
    {M : Rep.{0} Coeff (K ≃ₐ[k] K)}
    {x x' : Abelian.Ext.{0} M (classesK k K) 1}
    (hxx' : extDelta (k := k) (K := K) x = extDelta (k := k) (K := K) x')
    (h : extH M 1) (hh : IsLocTrivial (k := k) (K := K) h) :
    yonedaPair x h = yonedaPair x' h := by
  -- `x - x'` dies under `extDelta`, so it is pushed forward from `𝕀_K`
  have hzero : extDelta (k := k) (K := K) (x - x') = 0 := by
    rw [extDelta_sub, hxx', sub_self]
  obtain ⟨z, hz⟩ :=
    (exists_extToClasses_iff_extDelta_eq_zero k K (x - x')).mpr hzero
  -- the orthogonality of the image of `extToClasses` with locally trivial classes
  have horth : yonedaPair (extToClasses (k := k) (K := K) z) h = 0 :=
    Work.SSGRoute.Sha2Lib.yonedaPair_extToClasses_eq_zero_of_locTrivial k K z h hh
  have hsub := yonedaPair_sub (k := k) (K := K) x x' h
  rw [← hz] at hsub
  rw [horth] at hsub
  exact sub_eq_zero.mp hsub.symm

end SSGRoute.PTExt

end
