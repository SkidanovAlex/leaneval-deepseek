import Mathlib.NumberTheory.NumberField.Completion.Ramification
import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Submission.NK.NUV2.ArtinBridge.KummerSUnitField
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The archimedean places of the Kummer `S`-field

At an infinite place `v` of `K`, every `p`-th power in `K_vˣ` is a local norm from `L_wˣ`, where
`L = K(U(S)^{1/p})` is the Kummer `S`-field: at a complex place the local norm is onto, and at a
real place `p = 2` (a field containing a primitive `p`-th root of unity with `p` odd has no real
place) while the local norm group has index `1` or `2`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000

open scoped NumberField RestrictedProduct NumberField.LiesOver
open NumberField IsDedekindDomain

noncomputable section

namespace NK.NUV2.ArtinBridge

open NK.GlobalCFT

/-! ### The archimedean places -/

variable {K : Type} [Field K] [NumberField K] {Ω : Type} [Field Ω] [Algebra K Ω]

section Infinite

open scoped NumberField.LiesOver

variable [IsSepClosure K Ω]

/-- At an infinite place `v` of `K`, every `p`-th power in `K_vˣ` is a local norm from `L_wˣ`,
`L = K(U(S)^{1/p})`: at a complex place the local norm is onto, and at a real place `p = 2` (a
field containing a primitive `p`-th root of unity with `p` odd has no real place) and the local
norm group has index `≤ 2`. -/
theorem localPow_mem_localNormInfinite_kummerSUnitField {p : ℕ} (hp : p.Prime) {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) (S : Finset (Place K))
    [FiniteDimensional K ↥(kummerSUnitField K Ω p S)]
    (v : NumberField.InfinitePlace K)
    (w : NumberField.InfinitePlace ↥(kummerSUnitField K Ω p S)) [w.LiesOver v] :
    ∀ x ∈ NK.GlobalCFTdeep.SecondInequality.KummerCase.localPow (K := K) p
      (NK.GlobalCFT.Place.ofInfinite v),
      ∃ u : w.Completionˣ, NK.GlobalCFT.Place.localNormInfinite w v u = x := by
  classical
  haveI : IsGalois K ↥(kummerSUnitField K Ω p S) :=
    isGalois_kummerSUnitField (K := K) (Ω := Ω) (S := S) (p := p) hp hζ
  intro x hx
  obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp hx
  rw [powMonoidHom_apply] at hy
  have hindex := NK.GlobalCFTdeep.Herbrand.index_normGroup_completion_eq_finrank v w
  have key : x ∈ NK.LocalReciprocity.normGroup v.Completion w.Completion := by
    rcases NumberField.InfinitePlace.isUnramified_or_isRamified K w with h | h
    · have hfin : Module.finrank v.Completion w.Completion = 1 := h.finrank_eq_one v
      have htop : NK.LocalReciprocity.normGroup v.Completion w.Completion = ⊤ :=
        Subgroup.index_eq_one.mp (by rw [hindex, hfin])
      rw [htop]
      exact Subgroup.mem_top x
    · have hvreal : v.IsReal := (NumberField.InfinitePlace.LiesOver.comap_eq w v) ▸ h.isReal
      have hp2 : p = 2 := by
        rcases hp.eq_two_or_odd with h2 | hodd
        · exact h2
        · exact absurd hvreal
            (NK.GlobalCFTdeep.SecondInequality.KummerCase.no_isReal_of_isPrimitiveRoot_ne_two
              hp (by omega) hζ v)
      have hfin : Module.finrank v.Completion w.Completion = 2 := h.finrank_eq_two v
      have hidx : (NK.LocalReciprocity.normGroup v.Completion w.Completion).index = 2 := by
        rw [hindex, hfin]
      have hpow := Subgroup.pow_index_mem
        (NK.LocalReciprocity.normGroup v.Completion w.Completion) y
      rw [hidx, ← hp2] at hpow
      rwa [hy] at hpow
  rw [NK.LocalReciprocity.mem_normGroup_iff] at key
  obtain ⟨u, hu⟩ := key
  refine ⟨u, ?_⟩
  apply Units.ext
  simpa [NK.GlobalCFT.Place.localNormInfinite] using hu


end Infinite

end NK.NUV2.ArtinBridge
