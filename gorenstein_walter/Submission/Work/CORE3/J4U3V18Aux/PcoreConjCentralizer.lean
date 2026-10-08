import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE3.SevenNoInvolCentralizer

/-!
# CORE3 / J4U3V18: `V^g` centralizes the inverted odd `X`, and `V^g ∩ Ĥ = 1`

This is the pair of facts (F1) and (F2) recorded in
`Submission/Work/CORE3/NOTES_J4U3V18.md` §1, in the setting of Bender (1981) §3, p. 224, item (7):

`G` is a minimal counterexample, `B` a Bender setup, `Case1 B` holds, `D : Case1bData B` is the
subcase `V = O₂(Ĥ)` of type `(2,2)`, `y ∉ Ĥ` is an involution inverting a nontrivial odd-order
`X ≤ Ĥ` whose centralizer in `G` has even order, and `g : G` is a conjugating element with
`X ≤ K^g` and `N_G(X) ≤ Ĥ^g = N_G(V^g)` (`Work.CORE3.SevenConjK_conj`).

* (F1) `V^g ≤ C_G(X)`: `V = O₂(Ĥ)` centralizes `U = O(Ĥ)` (Theorem 2.6,
  `Work.CORE2A.thm26Concl_centralizer_eq`), hence centralizes `K ≤ F(U) ≤ U`; transporting along
  conjugation by `g` and using `X ≤ K^g` gives `V^g ≤ C_G(X)`.
* (F2) `V^g ⊓ Ĥ = ⊥`: any nontrivial `s ∈ V^g ⊓ Ĥ` is an involution of `Ĥ` centralizing `X`
  (by (F1)), which is impossible by `Work.CORE3.SevenNoInvolCentralizer`.

Neither part uses `hCeven`, `hN`, or `|U| = 3`; the hypotheses are simply those the caller has.
-/

namespace Work.CORE3.J4U3V18Aux

open Subgroup

set_option linter.unusedVariables false

/-- **(F1).** `V^g = O₂(Ĥ)^g` centralizes `X`, for `X ≤ K^g` with `K ≤ F(U) ≤ U = O(Ĥ)`.

`V = O₂(Ĥ)` commutes with `U` because `(S ⊓ C_G(U)) = O₂(Ĥ)` (Theorem 2.6), and `V`, `U ≤ Ĥ`
are normal of coprime order; conjugating by `g` and restricting along `X ≤ K^g ≤ U^g` gives the
claim. -/
theorem conjSub_pCoreIn_le_centralizer {G : Type} [Group G] [Finite G]
    (I : Work.CORE3.Case1Inputs) (h : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G)
    (D : Work.GW2.Case1bData B) (g : G) (X : Subgroup G)
    (hK : X ≤ Work.GW2.conjSub g D.K) :
    Work.GW2.conjSub g (Work.GW2.pCoreIn 2 B.Hhat) ≤ Subgroup.centralizer (X : Set G) := by
  have h26 : Work.GW2.Thm26Concl B := I.h26 G I.T.ft h B
  -- `V = O₂(Ĥ)` commutes with `U = O(Ĥ)`
  have hVleCU : Work.GW2.pCoreIn 2 B.Hhat ≤ Subgroup.centralizer (B.U : Set G) := by
    rw [← Work.CORE2A.thm26Concl_centralizer_eq h26]
    exact inf_le_right
  -- `K ≤ F(U) ≤ U`
  have hKleU : D.K ≤ B.U :=
    le_trans D.hall.1 (by
      simpa [Work.GW2.fittingIn] using
        Subgroup.map_subtype_le (Work.GW2.fitting ↥B.U))
  have hXleU : X ≤ Work.GW2.conjSub g B.U := hK.trans (Work.CORE2A.conjSub_mono hKleU g)
  intro w hw
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hw' : g⁻¹ * w * g ∈ Work.GW2.pCoreIn 2 B.Hhat := Work.CORE2A.mem_conjSub_iff.mp hw
  have hx' : g⁻¹ * x * g ∈ B.U := Work.CORE2A.mem_conjSub_iff.mp (hXleU hx)
  have hcomm : (g⁻¹ * x * g) * (g⁻¹ * w * g) = (g⁻¹ * w * g) * (g⁻¹ * x * g) :=
    Subgroup.mem_centralizer_iff.mp (hVleCU hw') (g⁻¹ * x * g) hx'
  calc x * w = g * ((g⁻¹ * x * g) * (g⁻¹ * w * g)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * w * g) * (g⁻¹ * x * g)) * g⁻¹ := by rw [hcomm]
    _ = w * x := by group

theorem PcoreConjCentralizer {G : Type} [Group G] [Finite G]
    (I : Work.CORE3.Case1Inputs) (h : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G)
    (h1 : Work.GW2.Case1 B) (D : Work.GW2.Case1bData B) {y : G} (hy2 : orderOf y = 2)
    (hyH : y ∉ B.Hhat) (X : Subgroup G) (hXle : X ≤ B.Hhat) (hXne : X ≠ ⊥)
    (hXodd : Odd (Nat.card X)) (hinv : Work.GW2.Inverts y X)
    (hCeven : Even (Nat.card (Subgroup.centralizer (X : Set G))))
    (g : G) (hK : X ≤ Work.GW2.conjSub g D.K)
    (hN : Subgroup.normalizer (X : Set G) ≤ Work.GW2.conjSub g B.Hhat) :
    (Work.GW2.conjSub g (Work.GW2.pCoreIn 2 B.Hhat) ≤
        Subgroup.centralizer (X : Set G)) ∧
      Work.GW2.conjSub g (Work.GW2.pCoreIn 2 B.Hhat) ⊓ B.Hhat = ⊥ := by
  refine ⟨conjSub_pCoreIn_le_centralizer I h B D g X hK, ?_⟩
  -- (F2): a nontrivial element of `V^g ⊓ Ĥ` would be an involution of `Ĥ` centralizing `X`.
  have hcent : Work.GW2.conjSub g (Work.GW2.pCoreIn 2 B.Hhat) ≤
      Subgroup.centralizer (X : Set G) := conjSub_pCoreIn_le_centralizer I h B D g X hK
  have hnoinv :=
    Work.CORE3.SevenNoInvolCentralizer G I h B h1 D hy2 hyH hXle hXne hXodd hinv
  rw [Subgroup.eq_bot_iff_forall]
  intro s hs
  rw [Subgroup.mem_inf] at hs
  obtain ⟨hsV, hsH⟩ := hs
  by_contra hs1
  -- `s² = 1`, because `s` is a conjugate of an element of the four-group `V`
  have hsq : s * s = 1 := by
    have hv : g⁻¹ * s * g ∈ Work.GW2.pCoreIn 2 B.Hhat := Work.CORE2A.mem_conjSub_iff.mp hsV
    have hv2 : (g⁻¹ * s * g) * (g⁻¹ * s * g) = 1 := by
      simpa [pow_two] using D.four.2 (g⁻¹ * s * g) hv
    calc s * s = g * ((g⁻¹ * s * g) * (g⁻¹ * s * g)) * g⁻¹ := by group
      _ = 1 := by rw [hv2]; group
  have hs2 : orderOf s = 2 := by
    have hdvd : orderOf s ∣ 2 :=
      orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact hsq)
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with hh | hh
    · exact absurd (orderOf_eq_one_iff.mp hh) hs1
    · exact hh
  exact hnoinv ⟨s, hsH, hs2,
    fun x hx => (Subgroup.mem_centralizer_iff.mp (hcent hsV) x hx).symm⟩

end Work.CORE3.J4U3V18Aux
