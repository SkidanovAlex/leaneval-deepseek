import Mathlib
import Submission.Work.WingbergH3.Constructive

/-!
# `Work.WingbergH3.contH2DimLe_iff_kummerCarrierInput`

**The Kummer-carrier form of the Salle--Koch input is *equivalent* to the cohomological relation
bound** `dim_{𝔽₂} H²(G,𝔽₂) ≤ m`.

One direction is `Work.WingbergH3.contH2DimLe_of_kummerCarrier` (`Constructive.lean`): a finite
`𝔽₂`-vector space `V` of cardinal at most `2 ^ m` whose `𝔽₂`-dual receives `H²(G,𝔽₂)` injectively
bounds `#H²(G,𝔽₂) ≤ #V ≤ 2 ^ m`.

The converse is the content of this module: if `#H²(G,𝔽₂) = 2 ^ k` with `k ≤ m` then the
*explicit* carrier `V = 𝔽₂^k` -- the `𝔽₂`-vector space `Fin k → ZMod 2` -- has `2 ^ k` elements, its
dual `V^* = Hom_{𝔽₂}(V, 𝔽₂)` is again an `𝔽₂`-vector space of dimension `k`
(`Subspace.dual_finrank_eq`), hence also has `2 ^ k` elements, and two finite types of equal
cardinality are in bijection (`Fintype.equivOfCardEq`); the bijection
`H²(G,𝔽₂) ≃ V^*` is the required injection.  No linear structure on `H²(G,𝔽₂)` is needed -- the
`φ` field of `KummerCarrier` is an arbitrary function.

Consequently the two normalisations of the constructive arithmetic input
(`Work.WingbergH3.KummerCarrierInput` and `Work.RelatorRank.ContH2DimLe`) are *the same
proposition*, so the classical Salle--Koch detection theorem may be quoted in whichever form is
convenient.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open scoped Classical

noncomputable section

namespace Work.WingbergH3

open Work.ConCohomology Work.RelatorRank

/-- **The cohomological relation bound produces the Kummer carrier.**  If
`#H²(G,𝔽₂) = 2 ^ k` with `k ≤ m`, then `V = 𝔽₂^k = Fin k → ZMod 2` is a finite `𝔽₂`-vector space
of cardinal `2 ^ k ≤ 2 ^ m` whose `𝔽₂`-dual has the same cardinal `2 ^ k` as `H²(G,𝔽₂)`; a
bijection between the two finite types is the required injection `H²(G,𝔽₂) ↪ V^*`. -/
theorem kummerCarrierInput_of_contH2DimLe {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {m : ℕ} (h : Work.RelatorRank.ContH2DimLe G m) :
    Work.WingbergH3.KummerCarrierInput G m := by
  obtain ⟨k, hk, hcard⟩ := h
  -- `H²(G,𝔽₂)` is finite, of cardinal `2 ^ k ≠ 0`.
  haveI : Finite (Work.RelatorRank.contH2 G) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ (by norm_num))
  -- the carrier `𝔽₂^k = Fin k → ZMod 2` has `2 ^ k` elements.
  have hVcard : Nat.card (Fin k → ZMod 2) = 2 ^ k := by
    rw [Nat.card_fun, Nat.card_fin, Nat.card_zmod]
  -- its `𝔽₂`-dual is a `k`-dimensional `𝔽₂`-vector space, hence also has `2 ^ k` elements.
  have hDcard : Nat.card (Module.Dual (ZMod 2) (Fin k → ZMod 2)) = 2 ^ k := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2)
          (V := Module.Dual (ZMod 2) (Fin k → ZMod 2)),
      Subspace.dual_finrank_eq (K := ZMod 2) (V := Fin k → ZMod 2),
      Module.finrank_fintype_fun_eq_card (ZMod 2), Fintype.card_fin, Nat.card_zmod]
  haveI : Finite (Module.Dual (ZMod 2) (Fin k → ZMod 2)) :=
    Nat.finite_of_card_ne_zero (by rw [hDcard]; exact pow_ne_zero _ (by norm_num))
  -- equal cardinalities of two finite types give a bijection, hence an injection.
  haveI : Fintype (Work.RelatorRank.contH2 G) := Fintype.ofFinite _
  haveI : Fintype (Module.Dual (ZMod 2) (Fin k → ZMod 2)) := Fintype.ofFinite _
  have hcardeq : Fintype.card (Work.RelatorRank.contH2 G) =
      Fintype.card (Module.Dual (ZMod 2) (Fin k → ZMod 2)) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcard, hDcard]
  let e := Fintype.equivOfCardEq hcardeq
  refine ⟨{ V := Fin k → ZMod 2, hcard := ?_, φ := e, inj := e.injective }⟩
  rw [hVcard]
  exact Nat.pow_le_pow_right (by norm_num) hk

/-- **The Kummer-carrier form of the Salle--Koch input is the cohomological relation bound.**
`Work.WingbergH3.KummerCarrierInput G m` says that `H²(G,𝔽₂)` embeds into the `𝔽₂`-dual of a
finite `𝔽₂`-vector space of at most `2 ^ m` elements -- the shape of the classical Salle--Koch
detection `Sha_∅ ↪ (V_∅/(F^×)²)^∨` -- and
`Work.RelatorRank.ContH2DimLe G m` says `dim_{𝔽₂} H²(G,𝔽₂) ≤ m`.  The two are equivalent: `⟸` is
`contH2DimLe_of_kummerCarrier` (`Constructive.lean`) and `⟹` is
`kummerCarrierInput_of_contH2DimLe` above, which takes the carrier `V = 𝔽₂^k`. -/
theorem contH2DimLe_iff_kummerCarrierInput {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {m : ℕ} :
    Work.RelatorRank.ContH2DimLe G m ↔ Work.WingbergH3.KummerCarrierInput G m :=
  ⟨kummerCarrierInput_of_contH2DimLe, contH2DimLe_of_kummerCarrier⟩

end Work.WingbergH3
