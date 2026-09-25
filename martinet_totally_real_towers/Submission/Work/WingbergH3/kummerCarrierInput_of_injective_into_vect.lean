import Mathlib
import Submission.Work.WingbergH3.Constructive

/-!
# `Work.WingbergH3.kummerCarrierInput_of_injective_into_vect`

**Any finite `𝔽₂`-vector space carrying `H²(G,𝔽₂)` injectively and of cardinal `≤ 2 ^ m` yields a
Kummer carrier** `Work.WingbergH3.KummerCarrierInput G m` -- a finite `𝔽₂`-vector space of cardinal
`≤ 2 ^ m` whose `𝔽₂`-dual receives `H²(G,𝔽₂)` injectively (the shape of the Salle--Koch detection).

The point is that only the *cardinality* of the carrier matters, not its linear structure: an
injection `H²(G,𝔽₂) ↪ V` with `#V ≤ 2 ^ m` makes `H²(G,𝔽₂)` finite of cardinal `≤ 2 ^ m`, and the
standard carrier `W = 𝔽₂^m = Fin m → ZMod 2` has `#W = 2 ^ m = #W^*` (a finite-dimensional space
over a finite field has the same cardinal as its dual), so a *function* injection
`H²(G,𝔽₂) ↪ W^*` exists by the elementary cardinality criterion for finite types.  Note that the
carrier of `KummerCarrier` is a type in `Type` (universe `0`), while the given `V` may live in any
universe -- which is why the explicit small carrier `Fin m → ZMod 2` is used rather than
`Module.Dual (ZMod 2) V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped Classical

noncomputable section

namespace Work.WingbergH3

/-- **An injective carrier of `H²(G,𝔽₂)` of cardinal `≤ 2 ^ m` is a Kummer carrier.**

Given `f : H²(G,𝔽₂) ↪ V` with `V` a finite `𝔽₂`-vector space of cardinal at most `2 ^ m`, the
Kummer carrier `W = 𝔽₂^m` has cardinal `2 ^ m`, hence (`Subspace.dual_finrank_eq`) its `𝔽₂`-dual
`W^*` also has `2 ^ m` elements, and `#H²(G,𝔽₂) ≤ #V ≤ 2 ^ m = #W^*` produces an injection
`H²(G,𝔽₂) ↪ W^*`. -/
theorem kummerCarrierInput_of_injective_into_vect {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {m : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (hcard : Nat.card V ≤ 2 ^ m)
    (f : Work.RelatorRank.contH2 G → V) (hf : Function.Injective f) :
    Work.WingbergH3.KummerCarrierInput G m := by
  -- the hypothesis makes `H²(G,𝔽₂)` finite, of cardinal at most `2 ^ m`.
  haveI : Finite (Work.RelatorRank.contH2 G) := Finite.of_injective f hf
  have hcardle : Nat.card (Work.RelatorRank.contH2 G) ≤ 2 ^ m :=
    le_trans (Nat.card_le_card_of_injective f hf) hcard
  -- the carrier `𝔽₂^m = Fin m → ZMod 2` has `2 ^ m` elements ...
  have hW : Nat.card (Fin m → ZMod 2) = 2 ^ m := by
    rw [Nat.card_fun, Nat.card_fin, Nat.card_zmod]
  -- ... and so does its `𝔽₂`-dual.
  have hD : Nat.card (Module.Dual (ZMod 2) (Fin m → ZMod 2)) = 2 ^ m := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Module.Dual (ZMod 2) (Fin m → ZMod 2)),
      Subspace.dual_finrank_eq (K := ZMod 2) (V := Fin m → ZMod 2),
      Module.finrank_fintype_fun_eq_card (ZMod 2), Fintype.card_fin, Nat.card_zmod]
  haveI : Finite (Module.Dual (ZMod 2) (Fin m → ZMod 2)) :=
    Finite.of_injective
      (fun g : Module.Dual (ZMod 2) (Fin m → ZMod 2) => (g : (Fin m → ZMod 2) → ZMod 2))
      (fun g h gh => LinearMap.ext fun v => congrFun gh v)
  -- two finite types of cardinal `≤` are related by an embedding.
  haveI : Fintype (Work.RelatorRank.contH2 G) := Fintype.ofFinite _
  haveI : Fintype (Module.Dual (ZMod 2) (Fin m → ZMod 2)) := Fintype.ofFinite _
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le (α := Work.RelatorRank.contH2 G)
    (β := Module.Dual (ZMod 2) (Fin m → ZMod 2)) (by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hD]
      exact hcardle)
  exact ⟨{ V := Fin m → ZMod 2, hcard := le_of_eq hW, φ := e, inj := e.injective }⟩

end Work.WingbergH3
